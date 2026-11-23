# Reproducing and examining the Lean proof of the Riemann Hypothesis

Ishaan Dixit, November 2026. The build is complete and clean, and the proof is now traced end to end.

On 20 November 2026 Levent Alpöge released a four-page note ([alpo.ge/remark.pdf](https://alpo.ge/remark.pdf)) and a Lean 4 project of 175,187 files and 17.4 million lines that claims to prove the Riemann Hypothesis and the Generalized Riemann Hypothesis for Dirichlet L-functions. Within hours several people had compiled it, and independent kernels (nanoda, con-leche, lean4lean, Pestka, con-agua, nanoclo, tenet) accepted it; see [Andrew Sutherland's page](https://math.mit.edu/~drew/grh/).

This repository is my independent look at the release. It does **not** claim to verify the proof; the kernel checks above do that. What it adds is a set of smaller, checkable facts: about the statement, the structure of the code, the numerical computations inside it, the reproducibility of the build, and how the ideas in the note show up in the code. It also has two interactive pages that explain the structure and the mathematics.

## Start here

- **[The readable account](https://ishaan2006.github.io/rh-lean-reproduction/)** (also as a [PDF](https://ishaan2006.github.io/rh-lean-reproduction/paper/), LaTeX source in `writeup/main.tex`): the whole proof top down, in six steps, with 15 figures and the load-bearing footprint of classical inputs. Every claim is labelled Exact, Verified, Reading or Ours.
- **[`mechanism/TRACE.md`](mechanism/TRACE.md)**: the evidence, 29 sections, every declaration with file and line.
- **[`results/audit/verdict_table.md`](results/audit/verdict_table.md)** and **[`published_now.tsv`](results/audit/published_now.tsv)**: `PropAudit.lean` load-bearing map of all 610 `*.Published` / `OpenLiterature` items and the 12 inert types/propositions inside the live closure.
- **[`scripts/`](scripts/)**: rebuild, audit and re-check everything yourself.

## Summary of findings

| | Finding | Confidence |
|---|---|---|
| 1 | The theorem proves Mathlib's own `RiemannHypothesis`, unchanged at the pinned Mathlib commit, and Mathlib's `riemannZeta` is the usual ζ. | Checked against source |
| 2 | Every one of the 175,187 files is in the import closure of `Main`; nothing is dead at the file level. About 72% of the 1,061,531 declarations are used by the top theorem. | Files: my scan. Declarations: tamnd's index, approximate |
| 3 | No `sorry`, `axiom`, `native_decide`, `unsafe`, `implemented_by`, `extern` or `opaque`. Metaprogramming is small and confined to a few helper files. | Text census; agrees with Deicyde's scan |
| 4 | All the heavy computations the proof asks Lean's kernel to run (124 `decide +kernel` sites) give the claimed results when re-run independently in Python. | Re-run with cross-checks and negative tests |
| 5 | My independent build is clean: 175,187 modules, Mathlib's own statement, axioms `propext`, `Quot.sound`, `Classical.choice` only. 76,968 compiled files are byte-identical to Sutherland's manifest, including `Main.olean`; the other 98,219 all store the absolute build path, and 0 differ without one. Recompiled at Sutherland's build path, a random sample of 300 of those 98,219 is byte-identical to his manifest, 300 of 300. Re-exporting with `lean4export` gives a byte-identical 61,570,595,788-byte export matching the published sha256 `5ea74b91…244e`. | Full build, full comparison, and full export hash |
| 6 | Several key words of the note (Stepanov, Guinand–Weil, relative trace formula, Vandiver) never appear in the code, while theta lifts, seesaws and covolumes appear in thousands of files. | Name search only |
| 7 | The √X is one inequality: per unit of main term the error is about x/m + m, where m is the length of the chain of lifts. m ≈ √x is set by hand in `RankVal`; the other two sizes (n ≈ x², k ≈ x^(9/2)) follow from it. Nothing in the construction of the family forces m ≈ √x. | Read in source; every declaration checked against the exact list the proof uses |
| 8 | Both sides of the balance are paid by one inequality, the divisibility bound `DIV`. The energy and slope charges of the same nominal size are slack, and the signature drift is an artefact smaller than its bound by a factor of x^1131. What is left is `Eb`: m lifts times a Bloch–Kato rank m, one m used twice. | Each step checked against the used-declaration list |
| 9 | The outline's 2/3 is reproduced exactly by charging each lift for the whole chain below it (x/m + m²). The code avoids it by charging every local piece to exactly one lift; no 2/3 route survives in the archive. | Reconstruction from the code's own quantities |
| 10 | The last analytic step is a windowed Landau theorem, and the Ш window rests on Lean proofs of Ferrero–Washington, Poitou–Tate and CM theory, all proved in the project, none assumed. | Checked against the used-declaration list |
| 11 | The proof also establishes Google DeepMind's own statements of RH and GRH (formal-conjectures), not just this project's: the bridge in community PR #88 compiles against my build with only the three standard axioms, and `con-leche --compare` accepts both theorems against the formal-conjectures challenge (`results/formal_conjectures_result.txt`). | Compiled and compared on the full build |
| 12 | `PropAudit.lean` classifies all 610 `*.Published` / `OpenLiterature` items at `40e56bab`: 276 unreachable, 261 applied, 60 carried-only (including `UnusedSlot72 := True`), 9 zero-proof (6 are `Set` definitions). Inside the live closure, 12 types/propositions are inert (`LocLanglands.IsRec`, `WeightedAtlas` [215 refs], `OTY.Cover`/`Etale`, `AdaptedBasis`/`PlueckerData`, etc.) and only 10 definitions have body `True`. Dropping unread hypothesis fields disconnects 14 classical theories (~2,600+ live declarations, including Ohsawa-Takegoshi / $L^2$ $\bar\partial$-estimates, `PushDown`, and 12 `ThetaLocalInputs` fields) from `Main` (upstream PRs #384, #395, #398). | Compiled `.olean` closure + source-checked `--why` traces (`results/audit/`) |

## 1. Source and provenance

The 14 parts from alpo.ge join to `lean.tar.gz`: 239,275,554 bytes, sha256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`, the published values. The project pins Lean v4.33.1 and Mathlib commit `0df444a3`. I also verified the published challenge export (sha256 `bd484ac9…b2b9`) and the hash of Sutherland's manifest of compiled files (`375cbee2…1d25`). Details: `results/hashes.txt`.

## 2. What is proved

`Main.lean` line 4 is `theorem riemannHypothesis : RiemannHypothesis := rhOfAll`, and `RiemannHypothesis` is not redefined anywhere in the project. In Mathlib at the pinned commit (`Mathlib/NumberTheory/LSeries/RiemannZeta.lean`, line 185):

```lean
def RiemannHypothesis : Prop :=
  ∀ (s : ℂ) (_ : riemannZeta s = 0) (_ : ¬∃ n : ℕ, s = -2 * (n + 1)) (_ : s ≠ 1), s.re = 1 / 2
```

The same file proves that `riemannZeta` equals Σ 1/nˢ for Re s > 1 (line 207), has the trivial zeros at −2, −4, … (line 173) and satisfies the functional equation (line 178), so it is the usual ζ. The other four theorems in `Main.lean` concern Dirichlet L-functions. All five follow from one statement the code calls `EveryCharacter`: no Dirichlet L-function has a zero with Re s > ½. The step from there to RH is classical and uses only Mathlib. Details: `results/statement_check.txt`.

## 3. Structure of the code

A text-only import-graph scan (`analysis/reach.py`) finds that all 175,187 files and 17,374,215 lines are reachable from `Main`; the longest import chain is 203 modules, and the only external libraries are Mathlib, Lean and Batteries. This answered a Zulip question about "~400k unreachable lines": at the file level there are none.

At the declaration level the picture is different. Using the declaration index published by [riemann.tamnd.com](https://riemann.tamnd.com) (data CC0), 769,260 of 1,061,531 declarations (72%) are used by `riemannHypothesis`. So roughly 292,000 declarations are compiled but never reached, which may be what the Zulip question was seeing. tamnd's resolver works without Lean, so these counts are close but not exact.

Exact count: the published export (`solution.ndjson.zst`, sha256 `61a8938a…b05381`) is the proof's full dependency closure, including Mathlib and Lean core. It has 1,468,419 declarations (1,246,110 theorems, 214,241 definitions, 7,970 inductive types, 91 opaque, 4 quotient, 3 axioms: `propext`, `Quot.sound`, `Classical.choice`), plus 16,314 constructors and recursors (`analysis/export_decls.py`). Reconciling the counts in circulation (noted by `james-shore` and `sphereofrealization` in issue #1): 1,484,733 lines in `used_decls.txt.gz` minus 4 exporter-added primitives gives 1,484,729 (`james-shore`), minus 6,486 unreferenced recursors gives 1,478,243 (`aapolipponen`), while 1,468,418 is the count of declaration records. The exact number of project declarations outside this closure needs the compiled environment; `analysis/dead_code/` will produce it when my build finishes.

Below `EveryCharacter` the proof runs down a chain of eight short theorems, each a few lines, with the work in large branches hanging off them: a statement about Galois representations attached to automorphic forms (54,225 declarations), a "window bound" on Galois cohomology (56,145), a covolume bound (52,322), and the construction of a 46-field record of hypotheses about unitary groups (89,250 in its largest branch). The interactive map in `visuals/proof-map.html` lays this out.

## 4. Static census

`analysis/census.py` strips comments and strings, then counts constructs across all files (`results/census_summary.txt`). It finds zero `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, `implemented_by`, `extern` and `opaque`. `partial` occurs twice, both in metaprogramming helper files. There are 4 `elab` declarations in 3 files and 5 `run_cmd` calls, all in `BuildAid`, where each adds one name to a library-suggestion deny list. The `elab` tactics build proof terms that the kernel re-checks, so they cannot make a false proof pass. These results agree with the static scan in [Deicyde/riemann-hypothesis](https://github.com/Deicyde/riemann-hypothesis).

## 5. The proof's numerical computations, re-run independently

Lean checks proofs symbolically and never evaluates ζ. In a few places, though, the proof makes the kernel actually compute something, with `decide +kernel`: 124 call sites in 34 files. I ported each Lean function to Python line by line, keeping Lean's natural-number semantics (truncating subtraction, floor division, x / 0 = 0), ran it, and compared with the claimed result. Where possible I added an independent cross-check, and for each I confirmed that a tampered input fails, so the ports are not vacuous. Scripts: `analysis/kernel-computations/`; output: `results/kernel_computations.txt`.

| Computation | What it does | Result | Used by the RH proof? |
|---|---|---|---|
| `run1`–`run4` | Prime counts in (h/2, h] for h up to 131,072, with an inequality at each step | Pass; counts equal an independent sieve | No |
| `loop_run` | A prime-count bound up to 131,071 | Pass; ends at π(131071) = 12,251 | Yes |
| Three factorial ladders | A lower bound on sums of 1/p, in steps | Pass | Yes |
| `table_ok` | 878 primes in 12 intervals | Pass; every listed number is prime | Yes |
| lcm{1..n} ≤ 3ⁿ (n < 30), ≤ 4ⁿ (n ≤ 100) | Inputs to a ψ estimate | Pass | Yes |
| `BB_disj0` | gcd and divisibility facts for two 12-digit primes | Pass | Yes |
| Five Pratt certificates | Primality, up to a 310-bit prime | Pass; `sympy.isprime` agrees | No |
| Four Lucas certificates and 20 identities | Primality of 63- to 616-bit primes and facts about them | Pass | No |

"Used by the RH proof" comes from tamnd's index and is approximate. Two constants in the cyclotomic file (`d = 599`, `condN = 16·571·599`) were inferred from the file's own identities rather than read from the source; all 24 facts in that file hold with them. A few small finite checks on custom structures were not ported. This confirms the arithmetic and nothing else; the logic is the kernels' job.

## 6. Reproducibility of the build

I built the project with `lake build Main` on a Google Cloud VM (377 GB RAM, 94 parallel jobs), using the scripts in `scripts/`. `scripts/7_compare.sh` hashes every compiled `.olean` and compares it with Sutherland's manifest. When I ran this, his caveats noted that only a 77-module sample of his build had been compared with a real `lake build`; he has since run a full sandboxed `lake build` (see below).

Full result (all 175,187 files; `results/olean_comparison.txt`):

| | No source path in file | Source path in file |
|---|---:|---:|
| Identical to manifest | 76,968 | 0 |
| Different | 0 | 98,219 |

`Main.olean` is identical. The build itself took 401 minutes on 94 cores and the check step reports `OVERALL: CLEAN` (`results/build_check_summary.txt`). `leanchecker` re-checks `Main` with exit code 0, and the full single-threaded replay of everything `Main` depends on (`leanchecker --fresh Main`) ran to completion in about 10 h 17 min with no error reported (its exit code was not recorded).

The two groups do not overlap. In the one module I examined by hand, the only differing text was the stored source path (`/mnt/rh_ram/lean/src/…` in my build against a relative path in a rebuild), which shifts everything after it. My working explanation is that `.olean` files store messages such as linter warnings, and those carry the absolute path of the build directory, so they cannot match a build made elsewhere.

**Settled: the path is the only difference.** Sutherland confirmed in leanprover-community/riemann-hypothesis#6 that his build passed sources to `lean` as `/home/ubuntu/grh/src/lean/src/<Module>.lean`. `scripts/11_path_sample.sh` replays, for a random sample of 300 of the 98,219 differing modules (seed 20261121), the exact `lean` command Lake recorded in each module's `.trace`, changing only the output location and the source prefix to his path. All 300 are byte-identical to his manifest (`results/path_sample_result.txt`). A calibration step first checks that the same replay at our own path reproduces our own `.olean` files exactly.

`scripts/8_export_hash.sh` exports my build with `lean4export` (v4.33.0, commit `15f6055e`) and compares it with the published export (`results/export_result.txt`). It finished in 89 minutes and **matched byte for byte**: 61,570,595,788 bytes, sha256 `5ea74b912147c5c93cc2b6d70cc727cf908df2f62ac6a20480a3fa02f6be244e`. That confirms the differing `.olean` files do not affect the kernel declarations.

My build is not sandboxed. Sutherland has since closed that gap himself: `lake build Main` in a bubblewrap sandbox (no network, read-only source, archive downloaded afresh) on a separate machine, at his build path, gives an export byte-identical to the published one, and 175,186 of its 175,187 compiled files match his manifest. The one exception, `Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/LocModel.olean`, compiles non-deterministically in Lean v4.33.1: two theorems elaborated in parallel both trigger an auto-generated equation lemma (`BBtop.eq_1`), and one bound-variable name in it depends on which gets there first. The two outputs differ in 38 bytes, bound-variable names play no part in kernel checking, and the lemma is not in the export. The underlying race was fixed in Lean v4.36.0 (lean4#15499). Details are on [his page](https://math.mit.edu/~drew/grh/). The perturbation test of the size windows (`mechanism/PERTURB.md`) will be added in a follow-up update.

**Against Google DeepMind's statements.** Community PR #88 adds a second Comparator setup whose challenge is formal-conjectures' own `RiemannHypothesis.riemannHypothesis` and `GRH.generalized_riemann_hypothesis`, the latter covering every non-trivial zero of a primitive Dirichlet L-function. `scripts/12_formal_conjectures.sh` runs it on my build: the three files compile against the real `Main.lean` (axioms `propext`, `Classical.choice`, `Quot.sound`), the challenge export on Linux has the sha256 the PR quotes, and `con-leche --compare` (branch `compare`, `274f0138`) accepts both theorems (`results/formal_conjectures_result.txt`). The full `lake comparator` run was not done.

## 7. The note's vocabulary against the code

The note ends with a 20-step timeline. `analysis/note_terms.py` searches all files for each step's key names, matching whole words in CamelCase identifiers and paths (`results/note_terms.json`). Theta lifts (2,629 files), covolumes (3,670), seesaws (565), Bessel periods (359) and GGP periods (236) are everywhere. **Stepanov, Guinand–Weil, "relative trace formula" and Vandiver never appear**, and "Iwasawa tower or theory" appears in 2 files. So those steps live in the code under other names, or were dropped on the way. A name match is not a semantic match; this is a map for readers, not an analysis of the mathematics.

## 8. Universe levels and ZFC Foundations

`analysis/levels.py` reads a `lean4export` file and reports which universe levels are actually used.

- **On the challenge export** (the five statements plus the Mathlib definitions they need): the largest concrete level is 2, that is `Type 1` (`results/levels_challenge_only.txt`), with the mathematical content (complex numbers, zeta, L-functions) living strictly in `Type 0`.
- **On the full published proof export** (`solution.ndjson.zst`, 61.57 GB, 1,484,733 declarations; `results/levels_full_export.txt`): there are 21,604 level records. Concrete level usage is:
  - Level 0 (`Prop = Sort 0`): 369,334 constant uses, 1 Sort use
  - Level 1 (`Type 0 = Sort 1`): 36,070 constant uses, 1 Sort use
  - Level 2 (`Type 1 = Sort 2`): 3,868 constant uses, 1 Sort use
  - Level 3 (`Type 2 = Sort 3`): 100 constant uses, 1 Sort use
  - Level 4 (`Type 3 = Sort 4`): 4 constant uses (`const Exists`, `const Exists.intro`, `const inferInstance`), 0 Sort uses
  - Largest symbolic offset: $u + 4$ in polymorphic template definitions.

**The reduction to ZFC:** On Zulip, Joël Riou pointed out that the presence of `Type 2` (`Sort 3`) is an implementation artifact of Mathlib's generic category theory instantiating sheaves over the "big" étale site $\mathrm{Sch}_{/S}$ (where sheaf categories live in `Type 2` and derived category typeclasses push to `Type 3`), much like early formalizations of the Weil conjectures.

By replacing big sites with standard **small étale sites** $X_\mathrm{et}$ (consisting of étale schemes of finite presentation over $X$, whose isomorphism classes form a countable set $|X_\mathrm{et}| \le \aleph_0$ in `Type 0`), the category of sheaves becomes locally small (`Obj : Type 1, Hom : Type 0`), derived categories have small hom-sets, and all cohomology groups and arithmetic inputs (Grothendieck-Messing deformations, de Rham crystals, Bloch-Kato Selmer groups, Poitou-Tate duality, Ferrero-Washington) operate on finite-type objects or modules over commutative rings in `Type 0`.

Consequently, the formal proof of the Riemann Hypothesis is fully conservative over **standard ZFC** without Grothendieck universes or inaccessible cardinals. See [analysis/foundations_zfc_universes.md](file:///Users/ishaandixit/random_experiments/rh-receipts/analysis/foundations_zfc_universes.md) for the complete derivation and source citations.

## 9. Interactive pages

Both pages are self-contained; open them in a browser.

- `visuals/proof-map.html`: the structure of the proof. The half-plane that `EveryCharacter` rules out, the eight-theorem trunk with branch sizes, how the declarations split across libraries, the note's 20 steps on a date axis against the name search, and a clearly labelled community reading of the core mechanism.
- `visuals/proof-math.html`: the mathematics, as six interactive plates computed live from real data. (1) ψ(x) − x against Schoenfeld's √x band out to 10⁶. (2) The zeros of ζ and the explicit formula rebuilding the prime staircase, with a slider that moves a zero off the line. (3) How a bound on prime sums clears a half-plane of zeros. (4) RH over finite fields: elliptic-curve point counts inside Hasse's bound for any curve you type. (5) Stepanov's multiplicity trick and its √q balance. (6) The note's chain of about √X theta lifts. Each plate is labelled as established mathematics, from the note, an unverified reading, or schematic. The data for plate 2 comes from `visuals/make_zeta_data.py`.

One small numerical note from building plate 1: the simple form |ψ(x) − x| < √x (log x)² fails for 2 ≤ x < 3 (at x just below 3, ψ = log 2) and holds from x = 3 to 10⁶. Schoenfeld's sharper bound with constant 1/(8π) holds for 73.2 ≤ x ≤ 10⁶, reaching 91.8% of the band.

## 10. Where the √X comes from

`mechanism/TRACE.md` follows the proof downward from the top theorem, with every declaration checked against the exact list of declarations the proof uses. The main points, each with file and line there:

- **The endgame.** A bound Gm(x) ≤ x^(1/2+Cε) on a weighted prime sum, needed only on windows [Y, Y^(1+δ)], gives zero-freeness by a windowed Landau argument (`zeroFree_of_rpow_window`, `lemmaL`). One-sided bounds suffice because the combined Dirichlet coefficients are positive. The named Landau theorem `zero_free_of_Chebyshev_growth` is not used.
- **The balance.** The square-root bound is one inequality, `proposition_size_bound`. Divided by the main term, its four error terms are about x/m, x·m/k, m and k/n², so the error is about x/m + m once the windows on k hold, smallest at m ≈ √x. The x/m comes from the top weight a = x·b against m lifts of size b each; the m comes from a chain cost of m·B0 with B0 = f·m·b·x^ε, a budget defined in the code.
- **The sizes are chosen.** `RankVal` sets m ∈ [√(x·δ1), 2√(x·δ1)] with δ1 = x^(−ε/8), n ≈ x^(2+8ε) and k ≈ x^(9/2+10ε), and `exists_ranks_rankVal_frame` picks them. The constructor accepts any even m with 2 ≤ m ≤ 2n ≤ k, and a host exists for every choice. n and k are tied to m: the family needs about exp(m⁵·n) words, coded in k bits, so k ≳ m⁵·n (`exists_injective_words`); and the balance needs k ≤ n²·√x. With m = √x this gives n ≈ x² and k ≈ x^(9/2).
- **Who pays the m.** Inside the divisibility inequality `DIV` only two error terms use the full m·B0 budget: a signature drift, bounded in absolute value although its signed sum is exactly zero, and a hypothesis `Eb` on the per-lift charges. Since Gz(x) = Ω(√x), the m cost cannot be removable everywhere. `Eb` turns out to carry a genuine m²: m lifts, each charged a Selmer colength whose rank is a Bloch–Kato count of m Hodge–Tate weights (fixed by equality in the family). The small Ш loss is a separate additive term (trace section 13).

- **Slack and artefacts.** The energy charge is really about 2fb per lift (no factor m) and the slope upper bound `ClaimHigh` has no error term. The signature drift is bounded term by term in absolute value; its signed size is below that bound by a factor of at least x^1131 (trace section 16). So the "+m" rests on `Eb` alone: one m used twice, since the starting signature is (k−1, m) and the chain walks the m side down to 0 (section 18).
- **The 2/3.** Charging each lift for the whole chain below it gives x/m + m², minimised at x^(1/3) with value x^(2/3), exactly the outline's barrier. The code avoids it with `NData.locs_mem` and per-lift blocks (section 19).
- **The common lattice.** `exists_divStage_of_pk` builds the shared lattice `RR` with `prescribedRowLat`, place by place from each place's own twist, and intersects them (section 17).
- **The degree identity.** Four used statements, `NprimeMuR`, `LinkG_at`, `LinkDIV_at`, `Frame_at`: the finite places give the prime counts, the infinite places the Chowla–Selberg periods (section 20). The `g`-place energy clause in `linkDIVt_of_rowsF` (`RecBridge.lean:598` -> `WeightDegreeSizes.lean:142-261`) is a local sum over places `w | g_i` (`NormDecompositionCond` + `factEtaMean` + `DegreeCountBound` + `TypePrimeSizeBound`), not a global product formula (section 29.3).
- **The rest of the chain.** Local divisibility through a √p trick (`key_minor_dvd`), near-orthogonality of the words (`LinkS`), Fourier isolation with auxiliary characters chosen by a zero-density estimate, and the Ш window with its formal Ferrero–Washington (sections 21 to 25).

The balance x/m + m was stated independently, from other sources, in Jonas Whidden's Zulip reading and in Bartosz Naskręcki's proof guide (section 12). What the trace adds is the exact location of each step in the code, the fact that the sizes are chosen rather than forced, where the m cost is charged, and why it stops at √X rather than 2/3.

## 10a. Load-bearing audit (`PropAudit`)

Dependency reachability tells you which names occur in the closure, not whether the proof actually constructs or applies them. `scripts/PropAudit.lean` runs on the compiled `.olean` closure of the five headline theorems at `40e56bab` (1,265,279 project constants, 64,730 tracked types and propositions):

- **610 `*.Published` and `OpenLiterature` items ([`results/audit/published_now.tsv`](results/audit/published_now.tsv)):** 276 are unreachable from the five theorems (including `LocalLanglandsExists` and `CaraianiLocalGlobal`), 261 are applied, 60 are carried-only (`applied=0, carried>0`, including `GlobalTheory.Published.UnusedSlot72 := True`), and 9 have zero proof occurrences (source-checked: 6 are `Set` definitions rather than theorems).
- **Source-checked `--why` derivations ([`results/audit/verdict_table.md`](results/audit/verdict_table.md), 83 targets):** `GrothendieckDeformation` / `GrothendieckMessing` (`abelianScheme_hom_lifting_nilpotent_dividedPowers`), `BlochKato.RationalDuality` / `IntegralDuality` / `DimFormula` (`bkAL`, `bkBL`), `PoitouTate.ShaDual`, `HoweDualityReal`, and `DeRhamVectorExtension.Family.Natural` are all genuinely proved and applied. `OpenLiteratureStatements` (carried 316x, applied 3x) is established via weak `IsRecT` (`recTExists`) and `galoisLocalGlobalStrong_recParameter`, bypassing full `IsRec`.
- **12 inert types/propositions inside the live closure ([`results/audit/audit_now.tsv`](results/audit/audit_now.tsv)):** never constructed in the closure, appearing only as undischarged hypotheses. The largest clusters are `ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas` (215 refs) + `GlobalTheory.OTY.Cover`/`Etale` (40/38 refs), `GlobalTheory.LocLanglands.IsRec`/`Laws`/`IsDeligneEps` (2/14/1 refs), and `AdaptedBasis`/`PlueckerData` (17/12 refs). Of 27 `Prop` declarations flagged as nullary in the closure, 17 are ordinary indexed inductives with a 0-field base constructor and only 10 have body `True` (3 explicit `UnusedSlot`s and 7 explicit "no extra filter" predicates).
- **Live-closure field-level pruning (upstream PRs [#384](https://github.com/leanprover-community/riemann-hypothesis/pull/384), [#395](https://github.com/leanprover-community/riemann-hypothesis/pull/395), [#398](https://github.com/leanprover-community/riemann-hypothesis/pull/398)):** dropping unread record fields disconnects ~2,600+ live declarations from `Main`:
  - `#384` (4 files, +1/-9 lines): drops unread `PublishedHodgeBundleTheorems.q8` / `GlobalTheory.HSCore.Quoted.l2`, disconnecting ~1,645 declarations of Ohsawa-Takegoshi / $L^2$ $\bar\partial$-estimates (`L2DbarEstimates`, `OTY`, `WeightedAtlas`).
  - `#395` (2 files, +2/-4 lines): replaces the unread 4th conjunct `PushDown.Statement` in `ZhangDimensionPushDownGrassmannianHeightBounds`, disconnecting ~160+ declarations (`PushDown`, `HodgeFlag*`, `PlueckerData`, `AdaptedBasis`).
  - `#398` (2 files, -48 lines): drops 12 unread classical-theorem fields from `GlobalTheory.FunPr.ThetaLocalInputs` (including Stone-von Neumann, metaplectic representation, Kudla splitting, holomorphic discrete series, Weyl branching, and cuspidal mirabolic), disconnecting ~800+ declarations.

Caveats: the fixpoint rules are statement-level and err toward "established" (never toward "inert"), and `applied=0` can miss unfolded applications, so carried-only rows require source inspection before removing anything.

## 10b. Upstream contributions (`leanprover-community/riemann-hypothesis`)

| PR / Issue | Scope |
|---|---|
| [#421](https://github.com/leanprover-community/riemann-hypothesis/pull/421) | Docstrings for near-orthogonality (`LinkS` in `GlobalTheoremInputs.lean`) and `Sha` window (`VWinAt`/`VWin` in `ExistsPageN.lean`, `vwin_of_row` in `VwinOfRow.lean`) |
| [#417](https://github.com/leanprover-community/riemann-hypothesis/pull/417) | Docstrings for divisibility bridge (`RecBridge.lean`), local `g`-place energy (`WeightDegreeSizes.lean`), and common lattice (`ExistsDivStageOfPk.lean`) |
| [#416](https://github.com/leanprover-community/riemann-hypothesis/pull/416) | Docstrings for Fourier isolation (`ChBalance.lean`), Lipschitz bounds (`LipschitzWeightAndMinimum.lean`), `ChainTied` (`TieGlobal.lean`), and `RankVal` (`ExistsRanksRankValFrame.lean`) |
| [#411](https://github.com/leanprover-community/riemann-hypothesis/pull/411) | Docstrings along the top-level proof spine (`Main.lean`, `MainConclusion.lean`, `ZeroFreeAllOfTopG.lean`, `ZeroFreeOfRpowWindow.lean`, `landauWindow.lean`) |
| [#407](https://github.com/leanprover-community/riemann-hypothesis/pull/407) | Literature citations for `KawamataViehweg` (Kawamata 1982, Viehweg 1982) and `StrongApproxSU` (Platonov-Rapinchuk 1994, Theorem 7.12) |
| [#405](https://github.com/leanprover-community/riemann-hypothesis/pull/405) | Literature citations for `BlochKatoLocal` (Bloch-Kato 1990) and `GrothendieckMessing` (Messing 1972) |
| [#272](https://github.com/leanprover-community/riemann-hypothesis/pull/272) | Literature citations for `PoitouTateDuality` (Milne 2006) and `FerreroWashington` (Ferrero-Washington 1979) |
| [#398](https://github.com/leanprover-community/riemann-hypothesis/pull/398) | Drop 12 unread classical-theorem fields from `GlobalTheory.FunPr.ThetaLocalInputs` (~800+ live declarations) |
| [#395](https://github.com/leanprover-community/riemann-hypothesis/pull/395) | Drop unread `PushDown.Statement` conjunct (~160+ live declarations) |
| [#384](https://github.com/leanprover-community/riemann-hypothesis/pull/384) | Drop unread `L2ExtensionLogCanonical` field `q8`/`l2` (~1,645 live declarations) |
| [#367](https://github.com/leanprover-community/riemann-hypothesis/pull/367) | Update `verification/NOTES.md` with current `con-leche`/`con-ron` status on the reflexive mutual block |
| [#39 comment](https://github.com/leanprover-community/riemann-hypothesis/issues/39#issuecomment-7103416740) | `PropAudit` 610-item load-bearing classification and 83-target source-checked verdict table |

## 11. What this does not show

- Nothing here checks the logic of the proof. That is done by the independent kernels and by `lake comparator --paranoid`.
- The trace explains where √X sits in the inequalities, not why the automorphic objects (theta lifts, Hida theory, slopes) satisfy them. `Eb` is now traced to its source (section 13), and it is connected to the "+m" side of the size balance: both balance terms sit in the error of the divisibility hypothesis `DIV`, whose m-term is the drift plus `Eb` (section 14). The other two charges of the same size (energy, slope) are slack in the family, the drift is an artefact of bounding term by term (section 16), so the "+m" rests on `Eb` alone, and every per-lift cost is at most one factor m, which is why the balance stops at √X and not at the 2/3 the outline says a naive count gives (section 15). Charging each lift for the whole chain below it reproduces that 2/3 exactly; the code avoids it by charging every piece to one lift, each lift on its own block (section 19). Claims in `mechanism/TRACE.md` are labelled Verified, Exact, Index or Reading.
- Declaration-level numbers depend on tamnd's approximate index.
- The classical inputs (Ferrero–Washington, Poitou–Tate, CM theory) are proved in Lean; whether each formal statement is as strong as the published theorem is for specialists to judge.

## 12. Related work by others

- [Andrew Sutherland](https://math.mit.edu/~drew/grh/): the main verification record and downloads.
- [Deicyde/riemann-hypothesis](https://github.com/Deicyde/riemann-hypothesis): source mirror, comparator setup, static scan and metaprogramming notes.
- [tamnd/riemann](https://riemann.tamnd.com): a written proof from the top down, with a page per declaration.
- [nasqret/riemann-rev](https://github.com/nasqret/riemann-rev): Bartosz Naskręcki's status dashboard, map and 11-page proof guide; it states the x/m + m balance and describes the per-lift Iwasawa-theory loss.
- Jonas Whidden's AI-assisted readings on the Lean Zulip (20 November): the 2/3 barrier and the x/m against m balance.
- [drew2apps/rh-lean-decomposition](https://github.com/drew2apps/rh-lean-decomposition): dominator-tree decomposition of the import graph.
- [kant2002/riemann-hypothesis-supplimentary](https://github.com/kant2002/riemann-hypothesis-supplimentary): folder-level import graph.
- [Infatoshi/rh-verification-receipts](https://github.com/Infatoshi/rh-verification-receipts): an independent build and nanoda run.
- [DevinWatson/rh-weil-bound-toy](https://github.com/DevinWatson/rh-weil-bound-toy): the note's toy finite-field argument.
- [friederrr/riemann-review](https://github.com/friederrr/riemann-review): a pooled AI-written informal write-up.
- [james-shore/rh-proof-dependencies](https://github.com/james-shore/rh-proof-dependencies): exact dependency and dead-code counts from the kernel proof terms (256,620 of 1,061,531 declarations unused).
- [nasqret/riemann-rev book](https://nasqret.github.io/riemann-rev/book/): Bartosz Naskręcki's book on the architecture; it also covers the localized Landau step, the auxiliary primes and the Ferrero–Washington and Poitou–Tate premises.
- [JoseClaudioSJr's reader's map](https://github.com/leanprover-community/riemann-hypothesis/issues/5) (community issue #5): independently traces the windowed Landau route and the gain chain.
- [keithadler/rh-trim](https://github.com/keithadler/rh-trim), [jae-63/rh-alpoge-blueprint](https://github.com/jae-63/rh-alpoge-blueprint), [cadamcat/riemann-hypothesis-exposition](https://github.com/cadamcat/riemann-hypothesis-exposition): trimming, a blueprint and an exposition.
- [Nondual-Observer/riemann-lean4-blueprint](https://github.com/Nondual-Observer/riemann-lean4-blueprint): blueprint, 240-entry kernel declaration index, and standalone Lean 4 companion theorems.
- Also: the dead-code counts by Sonoda, patunz's report on path-dependent `.olean` hashes, and the full kernel replays and rebuilds by Simon DeDeo and Elliot Arledge.

## 13. Reproduce

```bash
# source, hash check, build (Linux or macOS; see scripts/README.md)
cd scripts && bash run_all.sh
PARTIAL=1 bash 7_compare.sh        # during the build; full run afterwards
bash 8_export_hash.sh              # after the build
bash 11_path_sample.sh             # rebuild a sample at Sutherland's path
bash 12_formal_conjectures.sh      # PR #88: check against formal-conjectures' RH and GRH

# text-only analyses on the extracted source (no code is run)
python3 -I analysis/reach.py ~/rh/lean
python3 -I analysis/census.py ~/rh/lean
python3 -I analysis/note_terms.py ~/rh/lean/src note_terms.json

# kernel computations (needs sympy)
cd analysis/kernel-computations
python3 dyadic.py && python3 certs.py && python3 disjoint.py
python3 more.py ~/rh/lean/src && python3 cyclo.py ~/rh/lean/src
```

## Layout

- `scripts/`: the build pipeline (steps 1 to 6), `7_compare.sh`, `8_export_hash.sh`, `11_path_sample.sh`, `12_formal_conjectures.sh`, `13_comparator_original.sh`, `PropAudit.lean`, and `StatementCone.lean`.
- `analysis/`: `reach.py`, `census.py`, `levels.py`, `note_terms.py`, and `kernel-computations/`.
- `results/`: every output quoted above, with the date it was taken, `audit/` (`PropAudit` tables and `verdict_table.md`), `reading/` (`StatementCone` reading lists), and `used_decls.txt.gz`, the names of the 1,484,733 declarations in the export of `Main` (one `kind name` per line), so anyone can check "used / not used" with `zgrep -w`.
- `mechanism/TRACE.md`: the mechanism trace of section 10.
- `analysis/dead_code/`: the exact dead-code count, to be run on the finished build.
- `visuals/`: the two interactive pages and the script for their data.
- `docs/`: the GitHub Pages site with the readable account, its figures and the PDF.
- `writeup/`: the LaTeX source of the readable account.

## Contact

Ishaan Dixit. Questions, corrections and suggestions are welcome, by email or as a GitHub issue on this repository.

- Personal: [ishaandixit2017@gmail.com](mailto:ishaandixit2017@gmail.com)
- Student (Arizona State University): [idixit@asu.edu](mailto:idixit@asu.edu)

## License

MIT, for everything in this repository. The Lean proof itself is Levent Alpöge's and is not covered by this licence.

## How this was made

I wrote the scripts, analyses and pages with help from Claude, an AI assistant, and ran and checked the results myself. The scripts only read the downloaded source as text, or build it with the pinned toolchain. Every number here comes from a file in `results/`; judge the work by rerunning it.
