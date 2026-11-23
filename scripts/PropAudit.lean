/-
PropAudit.lean: which propositions and types does a proof actually establish?

Dependency tools report that a declaration X is "reachable" from a theorem when X's name occurs
anywhere in the theorem's closure, in a statement, a definition or a proof. That does not say
whether the proof ever *proves* X. A hypothesis that is mentioned along the way but never
discharged, or a predicate defined as `True`, is reachable without carrying any weight.

This tool classifies every project-defined type or proposition in the closure of the given
theorems:

* established: some chain of the closure's declarations produces an inhabitant from nothing;
* inert: reachable, but nothing in the closure produces an inhabitant. Every occurrence is an
  assumption (a binder, a structure field, a premise) that the proof never discharges;
* trivial: a definition whose body is `True` (after binders), or a `Prop` structure or
  inductive with a constructor that takes no arguments.

Method. Every declaration in the closure is read as an inference rule from its type: binders
whose types have project-defined heads are premises, and the conclusion's head is what it
produces (constructors, projections, theorems, instances and definitions alike). Conjunctions,
products, existentials (including `∃!`), `Nonempty`, `Iff` and equalities of propositions are taken apart, and
each project definition of a type or proposition can be unfolded in both directions. The least
fixpoint of these rules is what the closure establishes.

The approximation is chosen so that it errs towards "established", never towards "inert":
binders whose types are implications or universally quantified are treated as dischargeable
(a proof can be a lambda), and heads from outside the project (Mathlib, core) are treated as
available. A verification pass then searches every definition body and proof in the closure
for an application that supplies a *closed* argument (one built without any local hypothesis)
to a premise of an inert type, and for a closed application of an inert type's constructor.
Any such application is reported, and the type is moved to "established". An inert entry that
survives both is one that the proof never discharges by any route the tool can see.

Usage (from the project root, with the project built):
  lake env lean --run PropAudit.lean [options]
Options:
  --module M      module to load (default: Main)
  --decl NAME     a theorem to audit (repeatable; default: the five headline theorems)
  --root NAME     a module root that counts as the project (repeatable; default: this project's)
  --tsv FILE      write one line per classified constant
  --md FILE       write a Markdown report
  --src DIR       the project's source directory, for file:line (default: src)
  --url PREFIX    link file:line in the Markdown report to PREFIX/<path>#L<line>
  --no-verify     skip the verification pass
  --why NAME      print how NAME is established, in the closure and anywhere (repeatable)
  --prefix TEXT   classify every project type or proposition whose name contains TEXT, reachable
                  or not (repeatable; e.g. `.Published.`); with --prefix-tsv FILE, one line each
-/
import Lean
open Lean Meta

def defaultRoots : List Name :=
  [`CompanionTheory, `Development, `Formalism, `GroundTheory, `Lemmata, `PositivityTheory,
   `ReciprocityTheory, `Supplements, `Main, `Statements]

def defaultDecls : List Name :=
  [`riemannHypothesis, `riemannZeta_eq_zero_re, `LFunction_ne_zero_of_half_lt_re,
   `LFunction_eq_zero_re, `LFunction_eq_zero_re_of_isPrimitive]

structure AuditConfig where
  module : Name := `Main
  decls : List Name := []
  roots : List Name := []
  tsv? : Option String := none
  md? : Option String := none
  src : String := "src"
  url? : Option String := none
  verify : Bool := true
  why : List Name := []
  prefixes : List String := []
  prefixTsv? : Option String := none

partial def parseArgs : List String → AuditConfig → Except String AuditConfig
  | [], c => .ok c
  | "--module" :: m :: r, c => parseArgs r { c with module := m.toName }
  | "--decl" :: d :: r, c => parseArgs r { c with decls := c.decls ++ [d.toName] }
  | "--root" :: n :: r, c => parseArgs r { c with roots := c.roots ++ [n.toName] }
  | "--tsv" :: f :: r, c => parseArgs r { c with tsv? := some f }
  | "--md" :: f :: r, c => parseArgs r { c with md? := some f }
  | "--src" :: d :: r, c => parseArgs r { c with src := d }
  | "--url" :: u :: r, c => parseArgs r { c with url? := some u }
  | "--no-verify" :: r, c => parseArgs r { c with verify := false }
  | "--why" :: n :: r, c => parseArgs r { c with why := c.why ++ [n.toName] }
  | "--prefix" :: x :: r, c => parseArgs r { c with prefixes := c.prefixes ++ [x] }
  | "--prefix-tsv" :: f :: r, c => parseArgs r { c with prefixTsv? := some f }
  | a :: _, _ => .error s!"unknown argument {a}"

def moduleOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some idx => env.header.moduleNames[idx.toNat]!
  | none => `_unknown

def modulePath (src : String) (m : Name) : String :=
  src ++ "/" ++ (m.toString (escape := false)).replace "." "/" ++ ".lean"

/-- Constants a declaration refers to: its type, its body or proof, an inductive's
constructors, a constructor's inductive, a recursor's inductives. -/
def successors (ci : ConstantInfo) : Array Name :=
  let t := ci.type.getUsedConstants
  match ci with
  | .defnInfo d => t ++ d.value.getUsedConstants
  | .thmInfo d => t ++ d.value.getUsedConstants
  | .opaqueInfo d => t ++ d.value.getUsedConstants
  | .inductInfo d => t ++ d.ctors.toArray
  | .ctorInfo d => t.push d.induct
  | .recInfo d => t ++ d.all.toArray
  | _ => t

/-- The sentinel for `False`/`Empty`: never available unless the rules derive it. -/
def falseName : Name := `False

mutual
/-- What a hypothesis of type `e` requires, as tracked heads. For `∀ Γ, B` (a lambda can prove
it) this is what `B` requires, less what the hypotheses in `Γ` supply themselves. -/
partial def premHeads (tracked : Name → Bool) (e : Expr) : Array Name :=
  let e := e.consumeMData
  if e.isForall then
    let (local_, body) := forallParts tracked #[] e
    -- `A → False` (a negation) can be proved from a contradiction in `A`: require nothing
    if body.consumeMData.isConstOf ``False then #[] else
    (premHeads tracked body).filter (!local_.contains ·)
  else
  let f := e.getAppFn
  let args := e.getAppArgs
  match f with
  | .const n _ =>
    if n == ``False || n == ``Empty || n == ``PEmpty then #[falseName]
    else if (n == ``And || n == ``Prod || n == ``PProd || n == ``MProd) && args.size == 2 then
      premHeads tracked args[0]! ++ premHeads tracked args[1]!
    else if (n == ``Exists || n == ``Subtype || n == `ExistsUnique) && args.size == 2 then
      match args[1]!.consumeMData with
      | .lam _ _ b _ => premHeads tracked b
      | p => premHeads tracked p
    else if (n == ``Sigma || n == ``PSigma) && args.size == 2 then
      premHeads tracked args[0]! ++
        (match args[1]!.consumeMData with
         | .lam _ _ b _ => premHeads tracked b
         | p => premHeads tracked p)
    else if (n == ``Nonempty || n == ``Inhabited || n == `Fact || n == ``PLift || n == ``ULift || n == ``Squash || n == `Trunc) && args.size == 1 then
      premHeads tracked args[0]!
    else if tracked n then #[n] else #[]
  | _ => #[]

/-- The heads supplied by the binders of a `∀` telescope, and its body. -/
partial def forallParts (tracked : Name → Bool) (acc : Array Name) : Expr → Array Name × Expr
  | .forallE _ d b _ => forallParts tracked (acc ++ (conclusions tracked #[] d).map (·.2)) b
  | .mdata _ b => forallParts tracked acc b
  | e => (acc, e)

/-- The (premises, head) pairs that an inhabitant of `e` yields, given premises `prem` already
needed to reach it. -/
partial def conclusions (tracked : Name → Bool) (prem : Array Name) (e : Expr) :
    Array (Array Name × Name) :=
  let e := e.consumeMData
  match e with
  | .forallE _ d b _ => conclusions tracked (prem ++ premHeads tracked d) b
  | _ =>
  let f := e.getAppFn
  let args := e.getAppArgs
  match f with
  | .const n _ =>
    if n == ``False || n == ``Empty || n == ``PEmpty then #[(prem, falseName)]
    else if (n == ``And || n == ``Prod || n == ``PProd || n == ``MProd) && args.size == 2 then
      conclusions tracked prem args[0]! ++ conclusions tracked prem args[1]!
    else if (n == ``Exists || n == ``Subtype || n == `ExistsUnique) && args.size == 2 then
      match args[1]!.consumeMData with
      | .lam _ _ b _ => conclusions tracked prem b
      | p => conclusions tracked prem p
    else if (n == ``Sigma || n == ``PSigma) && args.size == 2 then
      conclusions tracked prem args[0]! ++
        (match args[1]!.consumeMData with
         | .lam _ _ b _ => conclusions tracked prem b
         | p => conclusions tracked prem p)
    else if (n == ``Nonempty || n == ``Inhabited || n == `Fact || n == ``PLift || n == ``ULift || n == ``Squash || n == `Trunc) && args.size == 1 then
      conclusions tracked prem args[0]!
    else if n == ``Iff && args.size == 2 then
      (conclusions tracked (prem ++ premHeads tracked args[1]!) args[0]!) ++
        (conclusions tracked (prem ++ premHeads tracked args[0]!) args[1]!)
    else if n == ``Eq && args.size == 3 && args[0]!.consumeMData.isSort then
      (conclusions tracked (prem ++ premHeads tracked args[2]!) args[1]!) ++
        (conclusions tracked (prem ++ premHeads tracked args[1]!) args[2]!)
    else if tracked n then #[(prem, n)] else #[]
  | _ => #[]
end

/-- Positions (in the top-level binder telescope) of binders whose type requires `x`. -/
def premisePositions (tracked : Name → Bool) (t : Expr) : Array (Nat × Array Name) := Id.run do
  let mut out := #[]
  let mut e := t.consumeMData
  let mut i := 0
  while true do
    match e with
    | .forallE _ d b _ =>
      let hs := premHeads tracked d
      if !hs.isEmpty then out := out.push (i, hs)
      e := b.consumeMData
      i := i + 1
    | _ => break
  return out

/-- Declarations Lean generates for every inductive or structure (injectivity, `sizeOf`,
`noConfusion`, eliminators, extensionality, and internal names such as `_flat_ctor`). Their bodies mention constructors, but they never
build an inhabitant from nothing, so their bodies do not count as uses. -/
def isBoilerplate (n : Name) : Bool :=
  n.components.any fun c => match c with
    | .str _ s => s ∈ ["injEq", "inj", "sizeOf_spec", "noConfusion", "noConfusionType", "casesOn",
        "recOn", "below", "brecOn", "ibelow", "binductionOn", "ctorIdx", "ext", "ext_iff", "ctorElim",
        "ctorElimType"] || (s.startsWith "_" && s != "_private")
    | _ => false

def stripBinders : Expr → Expr
  | .lam _ _ b _ => stripBinders b
  | .forallE _ _ b _ => stripBinders b
  | .mdata _ b => stripBinders b
  | e => e

def stripLams : Expr → Expr
  | .lam _ _ b _ => stripLams b
  | .mdata _ b => stripLams b
  | e => e

/-- Does a declaration of type `t` produce types or propositions (`∀ Γ, Sort u`)? Read from the
shape of `t`, unfolding the head of its conclusion through definitions (`GeoP := fun X => X → Prop`)
at most `fuel` times. `some true`: propositions; `some false`: types; `none`: neither. -/
partial def sortShape (env : Environment) (fuel : Nat) (t : Expr) : Option Bool :=
  let rec body : Expr → Expr
    | .forallE _ _ b _ => body b
    | .mdata _ b => body b
    | e => e
  match body t with
  | .sort l => some (l == .zero)
  | e => match e.getAppFn with
    | .const c _ =>
      if fuel == 0 then none else
      match env.find? c with
      | some (.defnInfo d) => sortShape env (fuel - 1) (stripLams d.value)
      | _ => none
    | _ => none

/-- Append `x` to the array stored at `k`. The array is taken out of the map before the push, so
it is updated in place instead of copied (pushing onto `m.getD k #[]` while `m` still holds the
array copies it every time, which is quadratic for keys with many entries). -/
@[inline] def pushAt {α : Type} (m : Std.HashMap Name (Array α)) (k : Name) (x : α) :
    Std.HashMap Name (Array α) :=
  match m.get? k with
  | some a => (m.erase k).insert k (a.push x)
  | none => m.insert k #[x]

/-- An inference rule: from `prem`, conclude `concl`; read from the type of `src`, or from
unfolding the definition `src` when `unfold` is set. -/
structure Rule where
  prem : Array Name
  concl : Name
  src : Name
  unfold : Bool := false
  deriving Inhabited

/-- Least fixpoint: heads reachable from rules with all premises available, and for each head
the index of the rule that first produced it (absent for seeds). -/
def fixpoint (clauses : Array Rule) (seed : Std.HashSet Name := {}) :
    Std.HashSet Name × Std.HashMap Name Nat := Id.run do
  let mut why : Std.HashMap Name Nat := {}
  let mut avail : Std.HashSet Name := {}
  let mut queue : Array Name := #[]
  for s in seed do
    avail := avail.insert s
    queue := queue.push s
  let mut need : Array Nat := Array.mkEmpty clauses.size
  let mut watch : Std.HashMap Name (Array Nat) := {}
  for h : i in [:clauses.size] do
    let ps := clauses[i].prem
    let c := clauses[i].concl
    let ps := (ps.foldl (fun (s : Std.HashSet Name) p => s.insert p) {}).toArray
    let ps := ps.filter (!avail.contains ·)
    need := need.push ps.size
    if ps.isEmpty then
      if !avail.contains c then
        avail := avail.insert c
        why := why.insert c i
        queue := queue.push c
    else
      for p in ps do
        watch := pushAt watch p i
  while h : queue.size > 0 do
    let p := queue.back
    queue := queue.pop
    for i in watch.getD p #[] do
      let k := need[i]! - 1
      need := need.set! i k
      if k == 0 then
        let c := clauses[i]!.concl
        if !avail.contains c then
          avail := avail.insert c
          why := why.insert c i
          queue := queue.push c
  return (avail, why)

/-- How `n` was established: the rule that first produced it, then its premises in turn, each
explained once, at most `maxLines` lines. -/
def derivation (rules : Array Rule) (why : Std.HashMap Name Nat) (extra : Name → Option String)
    (n : Name) (maxLines : Nat := 40) : Array String := Id.run do
  let mut out : Array String := #[]
  let mut seen : Std.HashSet Name := {}
  let mut stack : Array (Name × Nat) := #[(n, 0)]
  while h : stack.size > 0 do
    let (m, d) := stack.back
    stack := stack.pop
    if out.size ≥ maxLines then
      out := out.push "  …"
      break
    let pad := "".pushn ' ' (2 * d)
    if seen.contains m then
      out := out.push s!"{pad}{m}: see above"
      continue
    seen := seen.insert m
    match why.get? m with
    | some i =>
      let r := rules[i]!
      let via := if r.unfold then s!"unfolding `{r.src}`" else s!"`{r.src}`"
      let ps := (r.prem.foldl (fun (s : Std.HashSet Name) p => s.insert p) {}).toArray
      let from_ := if ps.isEmpty then "" else s!", from {", ".intercalate (ps.toList.map toString)}"
      out := out.push s!"{pad}{m} ← {via}{from_}"
      for p in ps.reverse do stack := stack.push (p, d + 1)
    | none =>
      match extra m with
      | some e => out := out.push s!"{pad}{m} ← {e}"
      | none => out := out.push s!"{pad}{m}: not established"
  return out

/-- Positions of the top-level binders of `t` whose declared type is a proposition or a predicate
(ends in `Prop` exactly, not in a universe variable `Sort u`). -/
def propParamPositions (t : Expr) : Array Nat := Id.run do
  let mut out := #[]
  let mut e := t.consumeMData
  let mut i := 0
  while true do
    match e with
    | .forallE _ d b _ =>
      if stripBinders d == .sort .zero then out := out.push i
      e := b.consumeMData
      i := i + 1
    | _ => break
  return out

structure Row where
  name : Name
  status : String       -- inert / inert-in-proof / trivial / established-by-witness
  sort : String         -- Prop / Type
  module : Name
  line : Nat
  refs : Nat := 0
  consumers : Array Name := #[]
  note : String := ""

def kindOf : ConstantInfo → String
  | .defnInfo _ => "def" | .thmInfo _ => "theorem" | .opaqueInfo _ => "opaque"
  | .axiomInfo _ => "axiom" | .inductInfo _ => "inductive" | .ctorInfo _ => "ctor"
  | .recInfo _ => "rec" | .quotInfo _ => "quot"

/-- Uses of proofs of the statements in a set, found in one body or proof. -/
structure UseScan where
  applied : Std.HashMap Name Nat := {}
  carried : Std.HashMap Name Nat := {}
  nodes : Nat := 0
  /-- subterms already scanned, by address and binder depth: shared subterms are read once -/
  seen : Std.HashSet (USize × Nat) := {}

/-- Classify how proofs of the statements `lit` occur in `e`.

A *proof term* of `P` is a bound variable whose binder type is `P …`, or a constant whose type
concludes `P …` applied to exactly its own arguments. An occurrence is *applied* when the proof is
applied to further arguments (eliminating the `∀`/`→` of `P`), projected, or passed to anything
other than a project declaration or a constructor (an eliminator such as `And.left`,
`Exists.casesOn`, `Iff.mp`, a cast: the conservative choice). It is *carried* when it is stored
by a constructor or passed to a project declaration, whose own body is scanned separately. -/
unsafe def scanUses (env : Environment) (lit : Std.HashSet Name)
    (proofOf : Std.HashMap Name (Name × Nat)) (inProject : Name → Bool) (budget : Nat)
    (e : Expr) : UseScan :=
  let headLit (t : Expr) : Option Name :=
    match t.consumeMData.getAppFn with
    | .const c _ => if lit.contains c then some c else none
    | _ => none
  let bump (m : Std.HashMap Name Nat) (p : Name) := m.insert p (m.getD p 0 + 1)
  let rec go (ctx : Array Expr) (e : Expr) (st : UseScan) : UseScan := Id.run do
    if st.nodes ≥ budget then return st
    let key := (ptrAddrUnsafe e, ctx.size)
    if st.seen.contains key then return st
    let mut st := { st with nodes := st.nodes + 1, seen := st.seen.insert key }
    let proofTerm (a : Expr) : Option Name :=
      let a := a.consumeMData
      match a.getAppFn with
      | .bvar i => if a.getAppNumArgs == 0 && i < ctx.size then headLit ctx[ctx.size - 1 - i]! else none
      | .const c _ => match proofOf.get? c with
        | some (p, k) => if a.getAppNumArgs == k then some p else none
        | none => none
      | _ => none
    match e with
    | .app .. =>
      let f := e.getAppFn
      let args := e.getAppArgs
      match f with
      | .bvar i =>
        if i < ctx.size then
          if let some p := headLit ctx[ctx.size - 1 - i]! then st := { st with applied := bump st.applied p }
      | .const c _ =>
        if let some (p, k) := proofOf.get? c then
          if args.size > k then st := { st with applied := bump st.applied p }
      | _ => pure ()
      let stores : Bool := match f with
        | .const c _ =>
          match env.find? c with
          | some (.ctorInfo _) => true
          | _ => inProject c
        | _ => false
      for a in args do
        if let some p := proofTerm a then
          if stores then st := { st with carried := bump st.carried p }
          else st := { st with applied := bump st.applied p }
      if !f.isConst && !f.isBVar then st := go ctx f st
      for a in args do st := go ctx a st
      return st
    | .lam _ t b _ => return go (ctx.push t) b (go ctx t st)
    | .forallE _ t b _ => return go (ctx.push t) b (go ctx t st)
    | .letE _ t v b _ => return go (ctx.push t) b (go ctx v (go ctx t st))
    | .mdata _ b => return go ctx b st
    | .proj _ _ b =>
      if let some p := proofTerm b then st := { st with applied := bump st.applied p }
      return go ctx b st
    | _ => return st
  go #[] e {}

unsafe def audit (cfg : AuditConfig) : MetaM UInt32 := do
  let env ← getEnv
  let roots := if cfg.roots.isEmpty then defaultRoots else cfg.roots
  -- membership in the project, decided once per module rather than once per constant
  let projMod : Array Bool := env.header.moduleNames.map fun m => roots.any (·.isPrefixOf m)
  let inProject (n : Name) : Bool := match env.getModuleIdxFor? n with
    | some i => projMod.getD i.toNat false
    | none => false
  let decls := if cfg.decls.isEmpty then defaultDecls else cfg.decls
  let found := decls.filter (env.contains ·)
  for d in decls do
    if !env.contains d then IO.eprintln s!"warning: unknown declaration {d}"
  if found.isEmpty then
    IO.eprintln "no declarations to audit"; return 1
  let t0 ← IO.monoMsNow
  let lap (what : String) : MetaM Unit := do
    IO.eprintln s!"  [{((← IO.monoMsNow) - t0) / 1000} s] {what}"
  -- 1. Closure (project constants only; outside constants cannot mention project ones).
  -- `used`: constants that occur in some body or proof in the closure. Only these are ever
  -- applied, so only these can produce anything; a constructor that is reachable only because
  -- its type is mentioned builds nothing.
  let mut inC : Std.HashSet Name := {}
  let mut used : Std.HashSet Name := found.foldl (·.insert ·) {}
  let mut closure : Array Name := #[]
  let mut work : Array Name := found.toArray
  -- Each body or proof is read once: its constants are cached here and reused by every pass
  -- below (bodies in this project can be very large, and every read walks the whole term).
  let mut valConsts : Std.HashMap Name (Array Name) := {}
  while h : work.size > 0 do
    let n := work.back
    work := work.pop
    if inC.contains n then continue
    let some ci := env.find? n | continue
    if !inProject n && !found.contains n then continue
    inC := inC.insert n
    closure := closure.push n
    let vc := match ci.value? (allowOpaque := true) with
      | some v => v.getUsedConstants
      | none => #[]
    valConsts := valConsts.insert n vc
    if !isBoilerplate n then
      for c in vc do used := used.insert c
    let succ := ci.type.getUsedConstants ++ vc ++ (match ci with
      | .inductInfo d => d.ctors.toArray
      | .ctorInfo d => #[d.induct]
      | .recInfo d => d.all.toArray
      | _ => #[])
    for s in succ do
      if !inC.contains s then work := work.push s
  IO.eprintln s!"closure: {closure.size} project constants from {found.length} theorems"
  lap "closure"
  -- 2. Tracked heads: project inductive types, and project definitions of types/propositions.
  let mut trackedSet : Std.HashSet Name := {}
  let mut isPropOf : Std.HashMap Name Bool := {}
  let projectConsts := env.constants.fold (init := #[]) fun (acc : Array Name) n _ =>
    if inProject n then acc.push n else acc
  IO.eprintln s!"project constants in the environment: {projectConsts.size}"
  lap "listing project constants"
  for n in projectConsts do
    let some ci := env.find? n | continue
    match ci with
    | .inductInfo d =>
      trackedSet := trackedSet.insert n
      isPropOf := isPropOf.insert n (stripBinders d.type == .sort .zero)
    | .defnInfo _ | .opaqueInfo _ =>
      if let some p := sortShape env 4 ci.type then
        trackedSet := trackedSet.insert n
        isPropOf := isPropOf.insert n p
    | _ => pure ()
  let tracked (n : Name) : Bool := trackedSet.contains n
  IO.eprintln s!"tracked types and propositions in the project: {trackedSet.size}"
  lap "tracked heads"
  -- 3. Rules from a set of constants.
  -- Rules: every theorem, definition, instance and projection yields rules from its type (it is
  -- a closed term of that type). A constructor yields rules only where it is applied: every
  -- inductive has constructors, and one that is never applied builds nothing. Every tracked
  -- definition can be unfolded (definitional unfolding applies nothing).
  let rulesOf (cs : Array Name) (applied : Name → Bool) : Array Rule := Id.run do
    let mut out := #[]
    for n in cs do
      let some ci := env.find? n | continue
      let isCtor := match ci with | .ctorInfo _ => true | _ => false
      if (!isCtor && !isBoilerplate n) || applied n then
        for (ps, c) in conclusions tracked #[] ci.type do
          out := out.push { prem := ps, concl := c, src := n }
      if tracked n then
        if let .defnInfo d := ci then
          let body := stripLams d.value
          out := out.push { prem := premHeads tracked body, concl := n, src := n, unfold := true }
          for (ps, c) in conclusions tracked #[n] body do
            out := out.push { prem := ps, concl := c, src := n, unfold := true }
    return out
  let rulesC := rulesOf closure used.contains
  let (availC0, whyC0) := fixpoint rulesC
  let mut availC := availC0
  let mut whyC := whyC0
  lap s!"rules and fixpoint for the closure ({rulesC.size} rules)"
  -- Environment-wide: constants applied in any project body or proof.
  let mut usedAll : Std.HashSet Name := {}
  for n in projectConsts do
    if isBoilerplate n then continue
    match valConsts.get? n with
    | some vc => for c in vc do usedAll := usedAll.insert c
    | none =>
      if let some v := (env.find? n).bind (·.value? (allowOpaque := true)) then
        for c in v.getUsedConstants do usedAll := usedAll.insert c
  lap "constants used anywhere in the project"
  let rulesAll := rulesOf projectConsts usedAll.contains
  lap s!"rules for the whole project ({rulesAll.size})"
  let (availAll, whyAll) := fixpoint rulesAll
  lap "rules and fixpoint for the whole project"
  -- 4. Candidates: tracked constants in the closure that the closure never establishes.
  let candidates (avail : Std.HashSet Name) : Array Name :=
    closure.filter fun n => tracked n && !avail.contains n
  let mut inert := candidates availC
  IO.eprintln s!"inert candidates after the rules: {inert.size}"
  -- 5. Verification: closed arguments supplied to an inert premise, closed constructor uses.
  let mut witnesses : Std.HashMap Name String := {}
  if cfg.verify && !inert.isEmpty then
    let mut round := 0
    while true do
      round := round + 1
      let inertSet : Std.HashSet Name := inert.foldl (·.insert ·) {}
      -- consumers: closure constants with a top-level binder requiring an inert head
      let mut consumers : Std.HashMap Name (Array (Nat × Array Name)) := {}
      for n in closure do
        let some ci := env.find? n | continue
        let ps := (premisePositions tracked ci.type).filter fun (_, hs) => hs.any inertSet.contains
        if !ps.isEmpty then consumers := consumers.insert n ps
      let mut ctorOf : Std.HashMap Name (Name × Nat) := {}   -- ctor ↦ (type, full arity)
      for p in inert do
        if let some (.inductInfo d) := env.find? p then
          for c in d.ctors do
            if let some (.ctorInfo ci) := env.find? c then
              ctorOf := ctorOf.insert c (p, ci.numParams + ci.numFields)
      let mut newly : Array (Name × String) := #[]
      for n in closure do
        let some ci := env.find? n | continue
        let some v := ci.value? (allowOpaque := true) | continue
        let vUsed := valConsts.getD n #[]
        if !vUsed.any (fun c => consumers.contains c || ctorOf.contains c) then continue
        let hits ← IO.mkRef (#[] : Array (Name × String))
        v.forEach fun s => do
          let f := s.getAppFn
          if let .const c _ := f then
            let args := s.getAppArgs
            if let some ps := consumers.get? c then
              for (i, hs) in ps do
                if h : i < args.size then
                  if !args[i].hasLooseBVars then
                    for p in hs do
                      if inertSet.contains p then
                        hits.modify (·.push (p, s!"{n} applies {c} to a closed argument #{i}"))
            if let some (p, arity) := ctorOf.get? c then
              if args.size ≥ arity && !s.hasLooseBVars then
                hits.modify (·.push (p, s!"{n} contains a closed `{c}` term"))
        for (p, why) in (← hits.get) do
          newly := newly.push (p, why)
      if newly.isEmpty then break
      let mut seed : Std.HashSet Name := {}
      for (p, why) in newly do
        if !witnesses.contains p then witnesses := witnesses.insert p why
        seed := seed.insert p
      let (a, w) := fixpoint rulesC (seed.fold (·.insert ·) availC)
      availC := a
      -- keep the first reason found for each head
      whyC := w.fold (fun (m : Std.HashMap Name Nat) k v => if m.contains k then m else m.insert k v) whyC
      inert := candidates availC
      IO.eprintln s!"verification round {round}: {seed.size} types established by closed \
        applications; {inert.size} inert remain"
      if round ≥ 10 then break
  lap "verification"
  -- 6. Trivial predicates: definitions whose body is True, Prop types with a nullary constructor.
  let mut trivial : Array (Name × String) := #[]
  for n in closure do
    if !tracked n then continue
    match env.find? n with
    | some (.defnInfo d) =>
      if stripBinders d.value == .const ``True [] then
        trivial := trivial.push (n, "body is `True` (after binders and hypotheses)")
    | some (.inductInfo d) =>
      if isPropOf.getD n false then
        for c in d.ctors do
          if let some (.ctorInfo ci) := env.find? c then
            if ci.numFields == 0 then trivial := trivial.push (n, s!"constructor `{c}` has no arguments")
    | _ => pure ()
  -- 6b. Where the proof leans on something true by definition, read from proof terms:
  --  * a trivial discharge: an argument supplied for a hypothesis whose type is a trivial predicate;
  --  * a degenerate instantiation: `True`, or `fun … => True`, passed as an argument.
  -- Then every closure declaration whose body or proof uses such a step, directly or through
  -- the declarations it uses.
  let trivialSet : Std.HashSet Name := trivial.foldl (fun s (n, _) => s.insert n) {}
  let mut trivConsumers : Std.HashMap Name (Array (Nat × Array Name)) := {}
  for n in closure do
    let some ci := env.find? n | continue
    let ps := (premisePositions tracked ci.type).filter fun (_, hs) => hs.any trivialSet.contains
    if !ps.isEmpty then trivConsumers := trivConsumers.insert n ps
  let isTrueFn (e : Expr) : Bool := stripLams e.consumeMData == .const ``True []
  let mut sites : Array (Name × String) := #[]       -- (declaration, what it does)
  let mut direct : Std.HashSet Name := {}
  for n in closure do
    if isBoilerplate n then continue
    let some ci := env.find? n | continue
    let hits ← IO.mkRef (#[] : Array String)
    for (v, isVal) in #[(ci.type, false)] ++ ((ci.value? (allowOpaque := true)).map (·, true)).toArray do
      let vUsed := if isVal then valConsts.getD n #[] else v.getUsedConstants
      if vUsed.any (fun c => c == ``True || trivConsumers.contains c) then
        v.forEach fun s => do
          if let .const c _ := s.getAppFn then
            let args := s.getAppArgs
            if let some ps := trivConsumers.get? c then
              for (i, hs) in ps do
                if i < args.size then
                  for t in hs do
                    if trivialSet.contains t then
                      hits.modify (·.push s!"discharges `{t}` (argument {i} of `{c}`)")
            if inProject c then
              let some cci := env.find? c | return
              for i in propParamPositions cci.type do
                if h : i < args.size then
                 if isTrueFn args[i] then
                  hits.modify (·.push s!"passes `{if args[i].consumeMData.isLambda then "fun … => True" else "True"}` (argument {i} of `{c}`)")
    let hs := (← hits.get).toList.eraseDups
    if !hs.isEmpty then
      direct := direct.insert n
      for h in hs.take 4 do sites := sites.push (n, h)
      if hs.length > 4 then sites := sites.push (n, s!"and {hs.length - 4} more")
  -- dependents within the closure, through bodies and proofs
  let mut usersOf : Std.HashMap Name (Array Name) := {}
  if !direct.isEmpty then
    for n in closure do
      if isBoilerplate n then continue
      for c in valConsts.getD n #[] do
        if inC.contains c && c != n then usersOf := pushAt usersOf c n
  let mut leans : Std.HashSet Name := direct
  let mut todo : Array Name := direct.toArray
  while h : todo.size > 0 do
    let m := todo.back
    todo := todo.pop
    for u in usersOf.getD m #[] do
      if !leans.contains u then
        leans := leans.insert u
        todo := todo.push u
  let rootsLean := found.filter leans.contains
  IO.eprintln s!"declarations that discharge a trivial predicate or pass `True` as an argument: {direct.size}; \
    closure declarations that use one, directly or not: {leans.size}; of the theorems: {rootsLean.length}"
  lap "trivial discharges"
  -- 7. Where each inert constant occurs in the closure.
  let inertSet : Std.HashSet Name := inert.foldl (·.insert ·) {}
  let mut refs : Std.HashMap Name (Array Name) := {}
  if !inertSet.isEmpty then
   for n in closure do
    let some ci := env.find? n | continue
    for c in ci.type.getUsedConstants ++ valConsts.getD n #[] do
      if inertSet.contains c && !c.isPrefixOf n then
        refs := pushAt refs c n
  let lineOf (n : Name) : MetaM Nat := do
    match (← findDeclarationRangesCore? n) with
    | some r => pure r.range.pos.line
    | none => pure 0
  let mut rows : Array Row := #[]
  for n in inert do
    let rs := ((refs.getD n #[]).foldl (fun (s : Std.HashSet Name) x => s.insert x) {}).toArray
    let elsewhere := match whyAll.get? n with
      | some i => let r := rulesAll[i]!
                  s!"established elsewhere by {if r.unfold then "unfolding " else ""}`{r.src}`" ++
                    (if r.prem.isEmpty then "" else s!" from {", ".intercalate (r.prem.toList.map toString)}")
      | none => ""
    rows := rows.push { name := n, status := if availAll.contains n then "inert-in-proof" else "inert",
                        sort := if isPropOf.getD n false then "Prop" else "Type",
                        module := moduleOf env n, line := ← lineOf n, refs := rs.size,
                        consumers := rs.qsort (·.toString < ·.toString), note := elsewhere }
  for (n, why) in trivial do
    rows := rows.push { name := n, status := "trivial", sort := "Prop", module := moduleOf env n,
                        line := ← lineOf n, note := why }
  for (n, what) in sites do
    rows := rows.push { name := n, status := "trivial-use", sort := "", module := moduleOf env n,
                        line := ← lineOf n, note := what }
  for (n, why) in witnesses.toArray do
    rows := rows.push { name := n, status := "established-by-witness",
                        sort := if isPropOf.getD n false then "Prop" else "Type",
                        module := moduleOf env n, line := ← lineOf n, note := why }
  rows := rows.qsort fun a b => a.status < b.status || (a.status == b.status && a.name.toString < b.name.toString)
  let count (s : String) : Nat := (rows.filter fun (r : Row) => r.status == s).size
  let trackedInC := (closure.filter tracked).size
  IO.eprintln s!"theorems: {found}"
  IO.eprintln s!"project types and propositions in the closure: {trackedInC}"
  IO.eprintln s!"  inert (never established anywhere in the project): {count "inert"}"
  IO.eprintln s!"  inert in the proof (established elsewhere, not in the closure): {count "inert-in-proof"}"
  IO.eprintln s!"  trivial: {count "trivial"}"
  IO.eprintln s!"  declarations that discharge a trivial predicate or pass `True`: {direct.size} \
    ({leans.size} closure declarations use one, directly or not; theorems among them: {rootsLean})"
  IO.eprintln s!"  moved to established by the verification pass: {count "established-by-witness"}"
  if !cfg.prefixes.isEmpty then
    let hits := projectConsts.filter fun n =>
      tracked n && !isBoilerplate n && cfg.prefixes.any fun x => (n.toString.splitOn x).length > 1
    -- for a head never established: the rules concluding it, each with its unmet premises
    let mut byConcl : Std.HashMap Name (Array Nat) := {}
    for h : i in [:rulesAll.size] do
      let c := rulesAll[i].concl
      byConcl := pushAt byConcl c i
    let blockers (n : Name) : String :=
      let rs := (byConcl.getD n #[]).toList.take 3
      if rs.isEmpty then "nothing in the project concludes it" else
      "; ".intercalate (rs.map fun i =>
        let r := rulesAll[i]!
        let miss := (r.prem.toList.eraseDups.filter (!availAll.contains ·)).take 3
        s!"{if r.unfold then "unfolding " else ""}{r.src} needs {", ".intercalate (miss.map toString)}")
    -- applied vs carried, for the propositions among them
    let lit : Std.HashSet Name := hits.foldl (fun s n => if isPropOf.getD n false then s.insert n else s) {}
    let mut proofOf : Std.HashMap Name (Name × Nat) := {}
    for c in closure do
      let some ci := env.find? c | continue
      let mut t := ci.type.consumeMData
      let mut k := 0
      while t.isForall do
        t := t.bindingBody!.consumeMData
        k := k + 1
      if let .const p _ := t.getAppFn then
        if lit.contains p then proofOf := proofOf.insert c (p, k)
    let mut applied : Std.HashMap Name Nat := {}
    let mut carried : Std.HashMap Name Nat := {}
    let mut appliedIn : Std.HashMap Name Name := {}
    let mut carriedIn : Std.HashMap Name Name := {}
    let mut skipped : Array Name := #[]
    let budget := 5000000
    for c in closure do
      if isBoilerplate c then continue
      let some v := (env.find? c).bind (·.value? (allowOpaque := true)) | continue
      let vu := valConsts.getD c #[]
      if !vu.any (fun d => proofOf.contains d || lit.contains d) then continue
      let r := scanUses env lit proofOf inProject budget v
      if r.nodes ≥ budget then skipped := skipped.push c
      for (p, n) in r.applied do
        applied := applied.insert p (applied.getD p 0 + n)
        if !appliedIn.contains p then appliedIn := appliedIn.insert p c
      for (p, n) in r.carried do
        carried := carried.insert p (carried.getD p 0 + n)
        if !carriedIn.contains p then carriedIn := carriedIn.insert p c
    lap s!"applied vs carried ({proofOf.size} proof constants, {skipped.size} bodies over budget)"
    let mut lb : Std.HashMap String Nat := {}
    for p in lit do
      if !inC.contains p then continue
      let k := if applied.getD p 0 > 0 then "applied (load-bearing)"
        else if carried.getD p 0 > 0 then "carried but never applied" else "no proof of it occurs in the proof"
      lb := lb.insert k (lb.getD k 0 + 1)
    IO.eprintln s!"reachable propositions among them, by use:"
    for (k, v) in lb.toArray do IO.eprintln s!"  {v}  {k}"
    if !skipped.isEmpty then IO.eprintln s!"  (bodies too large to scan fully: {skipped.toList.take 5})"
    let mut lines := #["name\tsort\treachable\testablished_in_proof\testablished_anywhere\thow_or_what_blocks\tlocation\tapplied\tcarried\tapplied_in\tcarried_in"]
    let mut tally : Std.HashMap String Nat := {}
    for n in hits do
      let reach := inC.contains n
      let inProof := availC.contains n
      let anywhere := availAll.contains n
      let how := if anywhere then
          match whyAll.get? n with
          | some i => let r := rulesAll[i]!
                      s!"by {if r.unfold then "unfolding " else ""}{r.src}"
          | none => "seed"
        else blockers n
      let key := s!"reachable={reach} in_proof={inProof} anywhere={anywhere}"
      tally := tally.insert key (tally.getD key 0 + 1)
      let line ← lineOf n
      lines := lines.push s!"{n}\t{if isPropOf.getD n false then "Prop" else "Type"}\t{reach}\t{inProof}\t{anywhere}\t{how}\t{modulePath cfg.src (moduleOf env n)}:{line}\t{applied.getD n 0}\t{carried.getD n 0}\t{(appliedIn.get? n).map toString |>.getD ""}\t{(carriedIn.get? n).map toString |>.getD ""}"
    IO.eprintln s!"prefix report ({", ".intercalate cfg.prefixes}): {hits.size} types and propositions"
    for (k, v) in tally.toArray.qsort (fun a b => a.2 > b.2) do
      IO.eprintln s!"  {v}  {k}"
    if let some f := cfg.prefixTsv? then
      IO.FS.writeFile f ("\n".intercalate lines.toList ++ "\n")
      IO.eprintln s!"wrote {f}"
  let mut whyText := ""
  for n in cfg.why do
    let w (m : Name) : Option String := (witnesses.get? m).map (s!"closed application: " ++ ·)
    let inProof := derivation rulesC whyC w n
    let inAll := derivation rulesAll whyAll (fun _ => none) n
    let reach := if inC.contains n then "reachable from the theorems" else
      if env.contains n then "NOT reachable from the theorems" else "not in the environment"
    whyText := whyText ++ s!"### `{n}` ({reach})\n\nIn the theorems' closure:\n```\n{"\n".intercalate inProof.toList}\n```\n\
      Anywhere in the project:\n```\n{"\n".intercalate inAll.toList}\n```\n\n"
    IO.eprintln s!"why {n} ({reach}):\n  in the closure:\n    {"\n    ".intercalate inProof.toList}\n  \
      anywhere in the project:\n    {"\n    ".intercalate inAll.toList}"
  if let some f := cfg.tsv? then
    let mut s := "status\tsort\tname\tlocation\trefs_in_closure\texample_users\tnote\n"
    for r in rows do
      s := s ++ s!"{r.status}\t{r.sort}\t{r.name}\t{modulePath cfg.src r.module}:{r.line}\t{r.refs}\t\
        {",".intercalate (r.consumers.toList.take 5 |>.map toString)}\t{r.note}\n"
    IO.FS.writeFile f s
    IO.eprintln s!"wrote {f}"
  if let some f := cfg.md? then
    let link (r : Row) : String :=
      let loc := s!"{modulePath cfg.src r.module}:{r.line}"
      match cfg.url? with
      | some u => s!"[`{loc}`]({u}/{modulePath cfg.src r.module}#L{r.line})"
      | none => s!"`{loc}`"
    let mut md := "# Which types and propositions the proof establishes\n\n"
    md := md ++ s!"Theorems: {", ".intercalate (found.map fun d => s!"`{d}`")}. Closure: \
      {closure.size} project constants, of which {trackedInC} are types or propositions.\n\n"
    md := md ++ s!"| Status | Count |\n|---|---|\n| inert: never established anywhere in the project | \
      {count "inert"} |\n| inert in the proof: established elsewhere, never in the closure | \
      {count "inert-in-proof"} |\n| trivial | {count "trivial"} |\n| declarations that discharge a trivial predicate or pass `True` | {direct.size} |\n| closure declarations using one, directly or not | {leans.size} |\n| moved to established by a closed \
      application | {count "established-by-witness"} |\n\n"
    for (st, title, blurb) in [
        ("inert", "Inert: never established anywhere",
         "Reachable from the theorems, but nothing in the project produces one. Every occurrence is an assumption that is never discharged."),
        ("inert-in-proof", "Inert in the proof, established elsewhere",
         "Something in the project produces one, but nothing in the theorems' closure does."),
        ("trivial", "Trivial", "True by definition."),
        ("trivial-use", "Where the proof leans on something true by definition",
         "Each entry is a body or proof in the closure that supplies an argument for a hypothesis whose type is one of the trivial predicates above, or passes `True` or `fun … => True` as an argument (for example as a predicate parameter). One line per kind of step, at most four per declaration."),
        ("established-by-witness", "Established by a closed application",
         "The rules missed these; the verification pass found a closed term supplying one. Listed so the rules' gaps are visible.")] do
      let rs := rows.filter fun (r : Row) => r.status == st
      if rs.isEmpty then continue
      md := md ++ s!"## {title} ({rs.size})\n\n{blurb}\n\n"
      for r in rs do
        let users := if r.consumers.isEmpty then "" else
          s!"; mentioned by {r.refs} closure declarations, e.g. " ++
            ", ".intercalate (r.consumers.toList.take 3 |>.map fun c => s!"`{c}`")
        let note := if r.note.isEmpty then "" else s!"; {r.note}"
        md := md ++ s!"- {r.sort} `{r.name}`, {link r}{users}{note}\n"
      md := md ++ "\n"
    if !whyText.isEmpty then md := md ++ "## Derivations\n\n" ++ whyText
    IO.FS.writeFile f md
    IO.eprintln s!"wrote {f}"
  return 0

unsafe def main (args : List String) : IO UInt32 := do
  let cfg ← match parseArgs args {} with
    | .ok c => pure c
    | .error e =>
      IO.eprintln s!"{e}\nusage: lean --run PropAudit.lean [--module M] [--decl NAME]... [--root NAME]... [--tsv FILE] [--md FILE] [--src DIR] [--url PREFIX] [--no-verify]"
      return 2
  initSearchPath (← findSysroot)
  let t0 ← IO.monoMsNow
  let env ← importModules #[{ module := cfg.module }] {}
  IO.eprintln s!"  [{((← IO.monoMsNow) - t0) / 1000} s] importing {cfg.module}"
  -- each type check gets a fresh budget of 200000 heartbeats (Lean's default per command)
  let ctx : Core.Context := { fileName := "<PropAudit>", fileMap := default,
                              maxHeartbeats := 200000 * 1000 }
  let (r, _) ← ((audit cfg).run' {} {}).toIO ctx { env }
  return r
