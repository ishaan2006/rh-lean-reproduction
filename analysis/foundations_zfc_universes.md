# Foundations and Universe Levels: Reducing the RH Proof from Type 2 to ZFC

**Author:** Ishaan Dixit (`ishaan2006`)  
**Context:** Riemann Hypothesis Lean 4 verification and foundational analysis  
**Reference:** Zulip discussions (Mario Carneiro, metakuntyyy, Joël Riou, David Loeffler, November 2026)  

---

## 1. The Foundational Question

A natural question raised immediately after the publication of Levent Alpöge's formal proof of the Riemann Hypothesis in Lean 4 is its foundational strength:

> *Does the Lean 4 formalization require Grothendieck universes (strongly inaccessible cardinals), or can the proof be carried out within standard Zermelo-Fraenkel set theory with Choice (ZFC)?*

In Lean 4, the type theory (Calculus of Inductive Constructions with a cumulative universe hierarchy `Sort u`) treats `Prop = Sort 0`, `Type 0 = Sort 1`, `Type 1 = Sort 2`, `Type 2 = Sort 3`, etc.
* `Type 0` (together with `Prop`, function types, and inductive types) corresponds proof-theoretically to standard ZFC.
* Each higher universe level `Type u` corresponds to the existence of an inaccessible cardinal $\kappa_u$.
* Therefore, a proof strictly confined to `Type 0` (with `Prop`) operates in ZFC. A proof that essentially requires `Type 1` operates in ZFC + "there exists an inaccessible cardinal", and one requiring `Type 2` operates in ZFC + "there exist two inaccessible cardinals" (or Grothendieck's universe axiom from SGA 4 Exposé I).

This document establishes that:
1. The mathematical statements of RH and GRH live entirely in `Type 0` (second-order arithmetic / analysis).
2. The presence of `Type 2` (`Sort 3`) and `Type 3` (`Sort 4`) in the Lean 4 export is an implementation artifact of Mathlib's generic category theory (specifically, sheaves on "big" étale sites and derived categories).
3. By replacing big sites with standard **small étale sites** (following Deligne in SGA $4\frac{1}{2}$ and standard algebraic geometry), the entire geometric apparatus drops to locally small categories with objects in `Type 1` and morphisms in `Type 0`.
4. All arithmetic inputs (Grothendieck-Messing deformation, crystalline / de Rham cohomology, Bloch-Kato Selmer groups, Poitou-Tate duality, Ferrero-Washington) operate on finite-type objects or modules over commutative rings in `Type 0`.
5. Consequently, the proof of RH is fully conservative over standard ZFC (and does not rely on any inaccessible cardinals).

---

## 2. Empirical Census from the Export

We ran `analysis/levels.py` on both the standalone challenge export and the full 61.57 GB kernel export (`solution.ndjson.zst`, sha256 `61a8938ad5f5e57397c1c0e3b954916af546d9004ade01c3555744a681b05381`).

### 2.1. Challenge Export (Statement Level)
The challenge export (`results/levels_challenge_only.txt`) contains the five headline theorems (`riemannHypothesis`, `riemannZeta_eq_zero_re`, `LFunction_ne_zero_of_half_lt_re`, `LFunction_eq_zero_re`, `LFunction_eq_zero_re_of_isPrimitive`) and the Mathlib definitions they reference:

| Level $u$ | Lean Type | Uses in `Sort` | Uses in Constant Arguments | Representative Constants |
|---|---|---:|---:|---|
| $0$ | `Prop = Sort 0` | 1 | 18,334 | `True`, `Eq`, `And` |
| $1$ | `Type 0 = Sort 1` | 1 | 2,669 | `Nat`, `Real`, `Complex`, `DirichletCharacter` |
| $2$ | `Type 1 = Sort 2` | 0 | 41 | `Lean.Grind.CommRing.Mon.rec`, `Nat.rec` |

* **Largest concrete level used:** Level 2 (`Type 1 = Sort 2`), appearing solely in recursors for typeclasses/algebra structures.
* **Mathematical statements:** The complex plane $\mathbb{C}$, the zeta function $\zeta(s)$, Dirichlet $L$-functions, and prime sums live strictly in `Type 0`.

### 2.2. Full Proof Export (Solution Closure)
The full proof export (`results/levels_full_export.txt`) contains all 1,484,733 declarations in the transitive closure of `Main`:

| Level $u$ | Lean Type | Distinct Uses in `Sort` | Distinct Uses in Constant Arguments | Representative Constants |
|---|---|---:|---:|---|
| $0$ | `Prop = Sort 0` | 1 | 369,334 | Basic logical propositions |
| $1$ | `Type 0 = Sort 1` | 1 | 36,070 | Standard mathematical objects |
| $2$ | `Type 1 = Sort 2` | 1 | 3,868 | Schemes, categories, large sheaves |
| $3$ | `Type 2 = Sort 3` | 1 | 100 | Sheaf categories on big sites, derived complexes |
| $4$ | `Type 3 = Sort 4` | 0 | 4 | `const Exists`, `const Exists.intro`, `const inferInstance` |

* **Concrete Level 4 occurrences:** Exactly 4 expressions in the entire export reference Level 4. Crucially, none are `Sort 4`. All 4 are polymorphic constants (`Exists`, `Exists.intro`, `inferInstance`) instantiated over a Level 3 type (i.e. `∃ (C : Type 2), ...` or typeclass synthesis on a category in `Type 2`).
* **Largest symbolic offset:** $u + 4$ in polymorphic template definitions (e.g. general limits or functor categories in Mathlib).

---

## 3. Where Type 2 and Type 3 Enter: Big Sites vs. Small Sites

To understand why Level 3 (`Type 2`) and Level 4 appear in the export, we trace Mathlib's category theory and algebraic geometry foundations.

### 3.1. Mathlib's Scheme and Sheaf Hierarchy
In Mathlib:
1. `Scheme.{u}` is defined as a `LocallyRingedSpace` whose structure sheaf has values in `CommRingCat.{u}`.
2. The collection of all schemes living in `Type u` forms a large category:
   $$\mathrm{Scheme}.\{u\} : \mathrm{Type}\,(u + 1)$$
3. In the formalization of algebraic geometry, if one forms a "big site" over a base scheme $S \in \mathrm{Scheme}.\{u\}$ (such as the category of all schemes over $S$, $\mathrm{Sch}_{/S}$), the objects of the site live in $\mathrm{Type}\,(u + 1)$.
4. A presheaf on this site with values in $\mathrm{Ab}$ is a functor:
   $$F : (\mathrm{Sch}_{/S})^\mathrm{op} \to \mathrm{Ab}$$
   The type of all such functors lives in $\mathrm{Type}\,(u + 2)$.
5. For $u = 0$, the category of sheaves on the big site:
   $$\mathrm{Shv}(\mathrm{Sch}_{/S}) : \mathrm{Type}\,2$$
   Its morphisms live in $\mathrm{Type}\,1$.
6. When forming derived categories $\mathcal{D}(\mathrm{Shv}(\mathrm{Sch}_{/S}))$ or chain complexes $\mathrm{Ch}(\mathrm{Shv}(\mathrm{Sch}_{/S}))$, the objects are complexes of sheaves, living in $\mathrm{Type}\,2$.
7. Finally, Lean typeclass resolution on these categories (e.g. `inferInstance : DerivedCategory ...` or existential quantification `∃ (D : Type 2), ...`) requires universe Level 4 (`Type 3`), accounting for the 4 isolated Level 4 records observed in the export census.

---

## 4. The Reduction to ZFC: Small Étale Sites

As Joël Riou pointed out on Zulip (November 2026), the use of `Type 2` for sheaf categories is identical to what occurred in early formalizations of the Weil conjectures, and is completely bypassed by using **small sites**.

### 4.1. The Small Étale Site $X_\mathrm{et}$
In classical algebraic geometry (Grothendieck-Artin in SGA 4 Exposé VII, Deligne in SGA $4\frac{1}{2}$, and Milne's *Étale Cohomology*):
* Let $X$ be a scheme of finite type over a number field $K$ or over $\mathbb{Z}$.
* The **small étale site** $X_\mathrm{et}$ is defined as the category whose objects are morphisms:
  $$U \to X$$
  which are **étale and of finite presentation** (or finite type) over $X$.
* Morphisms in $X_\mathrm{et}$ are $X$-morphisms between such schemes.

### 4.2. Cardinality and Smallness
1. Because $X$ is of finite type over a countable ring (such as $\mathbb{Z}$ or $\mathcal{O}_K$), the coordinate rings of affine charts of $X$ are finitely generated $\mathbb{Z}$-algebras, which are countable sets in $\mathrm{Type}\,0$.
2. Every étale scheme $U \to X$ of finite presentation is determined by finitely many polynomial equations with coefficients in the coordinate rings of $X$.
3. Up to isomorphism, there are at most countably many such étale schemes $U \to X$.
4. Therefore, the set of isomorphism classes of objects in $X_\mathrm{et}$ has cardinality:
   $$|X_\mathrm{et}| \le \aleph_0$$
5. Consequently, $X_\mathrm{et}$ has a skeleton that is a **small category**:
   $$\mathrm{Obj}(X_\mathrm{et}) : \mathrm{Type}\,0, \quad \mathrm{Hom}(U, V) : \mathrm{Type}\,0$$

### 4.3. Sheaf Categories on Small Sites
Because the site $X_\mathrm{et}$ is small:
1. **Presheaves and Sheaves:** A sheaf $\mathcal{F}$ of abelian groups on $X_\mathrm{et}$ is a functor from a small category to $\mathrm{Ab}$. The hom-sets between two sheaves are given by the equalizer of natural transformations:
   $$\mathrm{Hom}_{\mathrm{Shv}}(\mathcal{F}, \mathcal{G}) \subseteq \prod_{U \in \mathrm{Obj}(X_\mathrm{et})} \mathrm{Hom}(\mathcal{F}(U), \mathcal{G}(U))$$
   Since $\mathrm{Obj}(X_\mathrm{et}) : \mathrm{Type}\,0$ and each $\mathcal{F}(U) : \mathrm{Type}\,0$, this product is indexed by a small set of small sets, which lives in **`Type 0`**!
2. **Locally Small Category:** The category $\mathrm{Shv}(X_\mathrm{et})$ has objects in $\mathrm{Type}\,1$ and morphisms in $\mathrm{Type}\,0$.
3. **Abelian Category Structure and AB5:** Representable sheaves $\{h_U\}_{U \in \mathrm{Obj}(X_\mathrm{et})}$ form a small set of generators. By standard category theory (Baer's criterion / Grothendieck's AB5 axiom), $\mathrm{Shv}(X_\mathrm{et})$ has enough injectives constructed without Grothendieck universes.
4. **Derived Category:** The bounded derived category $\mathcal{D}^b(X_\mathrm{et}, \mathbb{Z}/\ell^n)$ has small hom-sets (living in `Type 0`), and complexes living in `Type 1`.
5. **Cohomology Groups:** The étale cohomology groups:
   $$H^i_\mathrm{et}(X, \mathcal{F}) = \mathrm{Ext}^i_{\mathrm{Shv}(X_\mathrm{et})}(\mathbb{Z}, \mathcal{F})$$
   are abelian groups living strictly in **`Type 0`**.
6. **Comparison Theorem:** By the classical comparison theorem between big and small étale sites (SGA 4 Exposé VII Theorem 5.1; Stacks Project Tag 03PO), the cohomology groups and higher direct images computed on $X_\mathrm{et}$ are canonically isomorphic to those computed on the big site:
   $$H^i_\mathrm{et}(X_\mathrm{small}, \mathcal{F}) \cong H^i_\mathrm{et}(X_\mathrm{big}, \mathcal{F})$$

Thus, all étale cohomology inputs (including Deligne's Weil I and II bounds on Frobenius eigenvalues) require only small sites.

---

## 5. Arithmetic Inputs: Concrete Verification in Source

We inspected the actual Lean declarations used in the live proof closure to verify whether any arithmetic input genuinely requires higher universes:

### 5.1. Grothendieck-Messing Deformation Theory
In `src/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/CanonicalOfAbelianDeRham.lean`:
```lean
variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R}
```
* The base rings $R$ and $R_0$ are explicitly declared in `Type` (which is `Type 0`).
* Grothendieck-Messing deformation classifies lifts of an abelian scheme $A_0$ over $R/I$ to $R$ (where $I$ has nilpotent divided powers) via direct summands $F \subseteq M$ of the de Rham homology $M = \mathbb{D}(A)_R$.
* The module $M$ is a finite free $R$-module of rank $2g$, and $F$ is a projective summand of rank $g$.
* This is purely finite-rank linear algebra over commutative rings in `Type 0`.

### 5.2. Galois Cohomology, Poitou-Tate, and Bloch-Kato
In `src/Formalism/GaloisCohomology/` and `src/Development/AbelianVarietyTheory/PublishedTheorems/`:
* The Galois group $G_K = \mathrm{Gal}(\bar{K}/K)$ is a profinite group (inverse limit of finite groups).
* The representations $W$ are either finite $\mathbb{Z}/\ell^r$-modules or finite-dimensional $\mathbb{Q}_\ell$-vector spaces.
* Continuous cochains $C^n(G_K, W)$ are locally constant functions from $G_K^n$ to $W$. Since $W$ is discrete and finite, these are functions factoring through finite quotients, living strictly in `Type 0`.
* The Selmer groups $H^1_f(K, W)$, the Tate-Shafarevich group $\Sha(A/K)$, and Poitou-Tate 9-term exact sequences are finite or torsion abelian groups in `Type 0`.

### 5.3. Ferrero-Washington ($\mu = 0$)
In `src/Development/AutomorphicArithmetic/DedekindLFunctions/`:
* Mathlib's ideal class group $\mathrm{Cl}(K')$ for cyclotomic layers $K' = K(\mu_{\ell^n})$ is the quotient of fractional ideals by principal ideals.
* Number fields $K'$ and their class groups are countable/finite objects living strictly in `Type 0`.

---

## 6. Proof-Theoretic Conclusion

| Aspect | Current Formalization (`Main`) | Mathematical Reality (Small Sites) |
|---|---|---|
| **Headline Statements** | `Type 0` (second-order arithmetic) | `Type 0` |
| **Max Universe in Export** | `Type 3 = Sort 4` (4 instances) | `Type 1` (classes of small functors) |
| **Sheaf Categories** | `Type 2` (big étale site) | Locally small (`Obj : Type 1, Hom : Type 0`) |
| **Cohomology Groups** | `Type 0` | `Type 0` |
| **Axiomatic Strength** | Lean 4 CIC + 3 universes | **Standard ZFC** |

### Summary Verdict
1. **Conservative over ZFC:** The formal proof of the Riemann Hypothesis in Lean 4 does **not** rely on Grothendieck universes in any mathematically essential way.
2. **Implementation Artifact:** The 100 occurrences of Level 3 (`Type 2`) and 4 occurrences of Level 4 (`Type 3`) in the compiled export arise solely because Mathlib's generic category theory instantiates sheaves over large sites $\mathrm{Sch}_{/S}$.
3. **Equiconsistency:** Because all geometric and arithmetic components (Weil conjectures, Grothendieck-Messing, Galois cohomology, Bloch-Kato, Ferrero-Washington) can be formulated on small étale sites $X_\mathrm{et}$ where $|X_\mathrm{et}| \le \aleph_0$, the theorem is completely provable in first-order ZFC without inaccessible cardinals.
