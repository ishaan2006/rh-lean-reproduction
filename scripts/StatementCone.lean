/-
StatementCone.lean: what a reader has to read to check what a statement SAYS.

Given a module and a declaration in it, list every project definition the declaration's
statement depends on: the constants in its type, then, recursively, the constants in the
types of those constants and in the bodies of the definitions among them. Theorem proofs are
never followed, and a theorem constant met inside a definition's body is skipped (it is a
proof, and proofs cannot change what a statement means). Constants from outside the project
(Mathlib, Batteries, Lean core, ...) are counted but not followed.

The result over-approximates what must be read: a definition used only inside a proof
term that sits in another definition's body is still listed. That is the safe direction.

Usage (from the project root, after `lake build <Module>`):
  lake env lean --run StatementCone.lean <Module> <Declaration> [options]
Options:
  --md FILE        also write a Markdown reading list to FILE
  --url PREFIX     link each entry to PREFIX/<path>#L<line> (e.g. a GitHub blob URL at a commit)
  --src DIR        the project's source directory (default: src)
  --root NAME      a module root that counts as the project (repeatable; default: this project's)
Output on stdout: one line per project constant, <kind>\t<name>\t<file>:<line>.
A summary goes to stderr.

The Markdown list puts files in dependency order (a file comes before the files whose cone
entries use it, so each definition is read before the definitions built on it) and entries in
source order within a file. Constructors, matchers and other auxiliary constants are folded
into the declaration they belong to.
-/
import Lean
open Lean

def defaultRoots : List Name :=
  [`CompanionTheory, `Development, `Formalism, `GroundTheory, `Lemmata, `PositivityTheory,
   `ReciprocityTheory, `Supplements, `Main, `Statements]

structure Config where
  module : Name
  decl : Name
  md? : Option String := none
  url? : Option String := none
  src : String := "src"
  roots : List Name := []

partial def parseArgs : List String → Config → Except String Config
  | [], c => if c.module.isAnonymous || c.decl.isAnonymous then .error "missing <Module> <Declaration>" else .ok c
  | "--md" :: f :: r, c => parseArgs r { c with md? := some f }
  | "--url" :: u :: r, c => parseArgs r { c with url? := some u }
  | "--src" :: d :: r, c => parseArgs r { c with src := d }
  | "--root" :: n :: r, c => parseArgs r { c with roots := c.roots ++ [n.toName] }
  | a :: r, c =>
    if a.startsWith "--" then .error s!"unknown option {a}"
    else if c.module.isAnonymous then parseArgs r { c with module := a.toName }
    else if c.decl.isAnonymous then parseArgs r { c with decl := a.toName }
    else .error s!"unexpected argument {a}"

def moduleOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some idx => env.header.moduleNames[idx.toNat]!
  | none => `_unknown

def kindOf : ConstantInfo → String
  | .defnInfo _ => "def"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .axiomInfo _ => "axiom"
  | .inductInfo d => if d.isRec then "inductive" else "inductive"
  | .ctorInfo _ => "ctor"
  | .recInfo _ => "rec"
  | .quotInfo _ => "quot"

/-- Constants that matter for meaning: everything in `e` except theorem constants. -/
def meaningConsts (env : Environment) (e : Expr) : Array Name :=
  e.getUsedConstants.filter fun c =>
    match env.find? c with
    | some (.thmInfo _) => false
    | _ => true

def successors (env : Environment) (ci : ConstantInfo) : Array Name :=
  let fromType := meaningConsts env ci.type
  match ci with
  | .defnInfo d => fromType ++ meaningConsts env d.value
  | .opaqueInfo d => fromType ++ meaningConsts env d.value
  | .inductInfo d => fromType ++ d.ctors.toArray
  | .ctorInfo d => fromType.push d.induct
  | .recInfo d => fromType ++ d.all.toArray
  | _ => fromType

/-- The declaration a reader would look for: constructors and recursors belong to their
inductive, matchers and other generated helpers to the declaration whose name prefixes theirs. -/
def ownerOf (env : Environment) (n : Name) : Name := Id.run do
  match env.find? n with
  | some (.ctorInfo d) => return d.induct
  | some (.recInfo d) => return d.all.headD n
  | _ => pure ()
  -- a structure's field projections belong to the structure
  if let some info := env.getProjectionFnInfo? n then
    if let some (.ctorInfo c) := env.find? info.ctorName then return c.induct
  let isAux (m : Name) : Bool :=
    m.isInternal || Meta.isMatcherCore env m ||
      (match m with
       | .str _ s => s.startsWith "match_" || s.startsWith "proof_" || s.startsWith "eq_" ||
           s == "casesOn" || s == "recOn" || s == "noConfusion" || s == "noConfusionType" ||
           s == "brecOn" || s == "below" || s == "binductionOn" || s == "ibelow"
       | _ => false)
  let mut m := n
  while isAux m && !m.getPrefix.isAnonymous do
    m := m.getPrefix
  return m

structure Entry where
  name : Name
  kind : String
  module : Name
  line : Nat
  members : Array Name := #[]

def modulePath (src : String) (m : Name) : String :=
  src ++ "/" ++ (m.toString (escape := false)).replace "." "/" ++ ".lean"

def cone (cfg : Config) : CoreM UInt32 := do
  let env ← getEnv
  let roots := if cfg.roots.isEmpty then defaultRoots else cfg.roots
  let some tci := env.find? cfg.decl
    | IO.eprintln s!"unknown declaration {cfg.decl}"; return 1
  let inProject (n : Name) : Bool := roots.any (·.isPrefixOf (moduleOf env n))
  let mut seen : NameSet := {}
  let mut work : Array Name := meaningConsts env tci.type
  if let .defnInfo d := tci then
    work := work ++ meaningConsts env d.value
  let mut project : Array Name := #[]
  let mut edges : Array (Name × Name) := #[]   -- (user, used), both project constants
  let mut outside : NameSet := {}
  let mut noBody : Array Name := #[]
  while h : work.size > 0 do
    let n := work.back
    work := work.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | continue
    if !inProject n then
      outside := outside.insert n
      continue
    project := project.push n
    if let .axiomInfo _ := ci then noBody := noBody.push n
    for s in successors env ci do
      if inProject s then edges := edges.push (n, s)
      work := work.push s
  -- Fold auxiliary constants into their owners.
  let mut entries : Std.HashMap Name Entry := {}
  for n in project do
    let o := ownerOf env n
    let o := if (env.find? o).isSome && inProject o then o else n
    let line := match (← findDeclarationRangesCore? o) with
      | some r => r.range.pos.line
      | none => 0
    let e := entries.getD o { name := o, kind := (env.find? o).map kindOf |>.getD "?",
                              module := moduleOf env o, line }
    entries := entries.insert o (if n == o then e else { e with members := e.members.push n })
  -- Module dependency order: depth-first from the target's module, dependencies first.
  let mut modDeps : Std.HashMap Name NameSet := {}
  for (a, b) in edges do
    let ma := moduleOf env a
    let mb := moduleOf env b
    if ma != mb then
      modDeps := modDeps.insert ma ((modDeps.getD ma {}).insert mb)
  let mods := entries.fold (fun (s : NameSet) _ e => s.insert e.module) {}
  let mut order : Array Name := #[]
  let mut done : NameSet := {}
  let mut stack : Array (Name × Bool) := #[]
  let starts := #[moduleOf env cfg.decl] ++ mods.toArray.qsort (fun a b => a.toString < b.toString)
  for st in starts do
    stack := stack.push (st, false)
    while h : stack.size > 0 do
      let (m, post) := stack.back
      stack := stack.pop
      if post then
        if !done.contains m then
          done := done.insert m
          if mods.contains m then order := order.push m
        continue
      if done.contains m then continue
      stack := stack.push (m, true)
      for d in (modDeps.getD m {}).toArray.qsort (fun a b => a.toString > b.toString) do
        if !done.contains d then stack := stack.push (d, false)
  -- stdout: one line per entry
  let byModule (m : Name) : Array Entry :=
    (entries.fold (fun (acc : Array Entry) _ e => if e.module == m then acc.push e else acc) #[]).qsort
      (fun a b => a.line < b.line || (a.line == b.line && a.name.toString < b.name.toString))
  for m in order do
    for e in byModule m do
      IO.println s!"{e.kind}\t{e.name}\t{modulePath cfg.src e.module}:{e.line}"
  let named := entries.fold (fun n _ e => if e.kind == "theorem" then n else n + 1) 0
  IO.eprintln s!"target: {cfg.decl} ({kindOf tci}) in {moduleOf env cfg.decl}"
  IO.eprintln s!"project constants in the statement's cone: {project.size}; \
    declarations to read: {named} in {order.size} files"
  IO.eprintln s!"constants from outside the project (not followed): {outside.size}"
  if !noBody.isEmpty then
    IO.eprintln s!"WARNING: {noBody.size} project constants are axioms or have no body: {noBody.toList.take 10}"
  -- Markdown reading list
  if let some path := cfg.md? then
    let link (e : Entry) : String :=
      let loc := s!"{modulePath cfg.src e.module}:{e.line}"
      match cfg.url? with
      | some u => s!"[`{loc}`]({u}/{modulePath cfg.src e.module}#L{e.line})"
      | none => s!"`{loc}`"
    let mut md := s!"# What `{cfg.decl}` says: the definitions to read\n\n"
    md := md ++ s!"Statement: `{cfg.decl}` in `{modulePath cfg.src (moduleOf env cfg.decl)}`.\n\n"
    md := md ++ s!"{named} declarations in {order.size} files ({project.size} project constants \
      before folding constructors and generated helpers into their declarations). \
      {outside.size} constants from outside the project (Mathlib, Lean) are used but not listed.\n\n"
    md := md ++ "Files are in dependency order: each file's entries use only entries in earlier files \
      and in the file itself, except where two files use each other. Within a file, entries are in \
      source order. Theorems appear only when a statement or definition mentions one by name; \
      their proofs never need reading.\n\n"
    if !noBody.isEmpty then
      md := md ++ s!"**Warning:** {noBody.size} project constants have no body here: {noBody.toList.take 10}.\n\n"
    let mut i := 0
    for m in order do
      i := i + 1
      let es := byModule m
      md := md ++ s!"## {i}. `{modulePath cfg.src m}` ({es.size})\n\n"
      for e in es do
        let extra := if e.members.isEmpty then "" else
          s!" (with {e.members.size} generated helper{if e.members.size == 1 then "" else "s"})"
        md := md ++ s!"- [ ] {e.kind} `{e.name}`, {link e}{extra}\n"
      md := md ++ "\n"
    IO.FS.writeFile path md
    IO.eprintln s!"wrote {path}"
  return 0

unsafe def main (args : List String) : IO UInt32 := do
  let cfg ← match parseArgs args {module := .anonymous, decl := .anonymous} with
    | .ok c => pure c
    | .error e =>
      IO.eprintln s!"{e}\nusage: lean --run StatementCone.lean <Module> <Declaration> [--md FILE] [--url PREFIX] [--src DIR] [--root NAME]..."
      return 2
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := cfg.module }] {}
  let ctx : Core.Context := { fileName := "<StatementCone>", fileMap := default }
  let (r, _) ← (cone cfg).toIO ctx { env }
  return r
