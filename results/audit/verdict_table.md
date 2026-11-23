# Source-Checked PropAudit Verdict Table (83 Targets)

Generated from `published_now.tsv`, `why_published.txt` (83 `--why` derivations in closure and project-wide), `witness_sources.txt`, and archive source at commit `40e56bab026552e089d7afcfeff08d2defb9c005`.

## 1. Main Audit Table (19 Explicit Targets)

| Statement | App / Car | Closure Witness (`why_published.txt`) | Source-Checked Verdict |
|---|---:|---|---|
| `GrothendieckDeformation` | 9 / 93 | `grothendieckDeformation_of_lifting` (from `AbelianDeRham`, `AbelianLifting` ← `print_abelianLifting`) | **Proved & applied.** Terminal `abelianScheme_hom_lifting_nilpotent_dividedPowers` verified in source (`AbelianSchemeHomLiftingNilpotentDividedPowers.lean:19`): genuine proof via `abelianLifting_of_four`. |
| `GrothendieckMessing` | 1 / 12 | `GrothendieckDeformation.grothendieckMessing` | **Proved & applied.** Follows from `GrothendieckDeformation`. |
| `GrothendieckMessing.At` | 7 / 0 | Unfolding `GrothendieckDeformation` + `IsNilDP` | **Proved & applied.** |
| `GrothendieckMessing.Canonical` | 10 / 9 | Unfolding `Canonical` from `IsAdmissible` | **Proved & applied.** |
| `GrothendieckMessing.LiftObj` | 3 / 3 | `GlobalTheory.T.grothendieckMessingLiftAbelianScheme_of_squareZero` | **Proved & applied.** (`published_now.tsv` showed unfolding from project-wide pass; closure has explicit theorem.) |
| `GrothendieckMessing.LiftHom` | 7 / 10 | `GlobalTheory.T.grothendieckMessingLiftHomomorphism_of_squareZero` | **Proved & applied.** |
| `GrothendieckMessing.IsAdmissible` | 17 / 4 | `GlobalTheory.T.admissible_deRhamHomology_summands_crystal` | **Proved & applied.** (`published_now.tsv` showed unfolding; closure has explicit theorem.) |
| `HoweDualityReal` | 4 / 149 | `GlobalTheory.howeDualityReal_holds` | **Proved & applied.** (Note: distinct from the 167 dead Howe declarations removed in PR #354.) |
| `BlochKato.RationalDuality` | 1 / 2 | `BlochKato.rationalDuality_of_allCoefficients` | **Proved & applied.** `bkAL` verified in source (`BlochKatoLocal.lean:229`): genuine proof via orthogonality + Tate duality + finrank. |
| `BlochKato.IntegralDuality` | 1 / 2 | Conjunct of `BlochKatoLocal` ← `UpperTheory.Lit.blochKatoLocal` | **Proved & applied.** `bkBL` verified in source (`BlochKatoLocal.lean:258`): genuine lattice-cocycle descent proof. |
| `BlochKato.DimFormula` | 2 / 1 | Conjunct of `BlochKatoLocal` (`RationalDualityOfAllCoefficients.lean:21,60`) | **Proved & applied** (`UpperTheory.V.Loc.bkDim`). |
| `PoitouTate.ShaDual` | 8 / 4 | `PositivityTheory.Lit1.PTN.shaDual_of_perfectPair` | **Proved & applied.** (`published_now.tsv` showed unfolding; closure has explicit theorem chain.) |
| `DeRhamVectorExtension.Family.Natural` | 2 / 3 | Conjunct of `DeRhamVectorExtension` (`DeRhamVectorExtension.lean:26,48`) | **Proved & applied** (`Natural.primPull`). |
| `DeRhamVectorExtension.Family.Tangent` | 0 / 1 | `GlobalTheory.T.exists_canonical_deRham_rigidExtension_family` | **Proved, carried only** (conjunct of `DeRhamVectorExtension`; 0 direct applications detected). |
| `DeRhamVectorExtension.Family.Filtered` | 0 / 1 | `GlobalTheory.T.exists_canonical_deRham_rigidExtension_family` | **Proved, carried only** (conjunct of `DeRhamVectorExtension`; 0 direct applications detected). |
| `CohDimTwo` | 0 / 16 | `GlobalTheory.twist_front_inputs` (`CohDimTwoGlobal ∧ CohDimTwoLocal`) | **Proved, carried only** as bundle (`CohDimTwoLocal` is applied 1x; `CohDimTwoGlobal` is carried 1x, applied 0x). |
| `ChebotarevOpenNormal` | 0 / 0 | `GlobalTheory.twist_front_inputs` (`ChebotarevOpenNormal ↔ ChebotarevDegreeOne`) | **Proved in closure, unused by name** (0 applied, 0 carried; equivalent `ChebotarevDegreeOne` / `TwSys.Cheb` is the active form). |
| `GoodChernNumbers` | 0 / 0 | Conjunct of `GoodChernWeil := GoodChernNumbers ∧ FlagPushForward` | **Dead in direct use** (0 applied, 0 carried; `GoodChernWeil` is bundled in `PublishedHodgeBundleTheorems`). |
| `OpenLiteratureStatements` | 3 / 316 | `OpenLiteratureStatements.mk` (from `recTExists` and `galoisLocalGlobalStrong_recParameter`) | **Proved & applied.** Uses weak `IsRecT` (`recTExists`), not full `IsRec`. |

## 2. The 9 Reachable `applied=0, carried=0` `Prop` Rows

Source inspection shows **6 of the 9 are `Set` definitions (`α → Prop`), not theorems**:
- `LogLine.offDivisor` (`Set (Fin n → ℂ)`)
- `SUSupp` (`Set (HA (AF F) σ J)`)
- `AutFin.forms` (`Set (GA D V → ℂ)`)
- `idealInvariants` (`Set ℂ`)
- `primesInProgression` (`Set ℕ`)
- `AutFinGL.forms` (`Set (Sm E a)`)

The remaining 3:
- `ChebotarevOpenNormal` and `GoodChernNumbers` (in Section 1 above).
- `HarishChandraModulesOn`: projection/unfolding of `HarishChandraModules` ← `CompanionTheory.D.gk.HC.print_harishChandraModules`.

## 3. All 60 Carried-Only Rows (`reachable=true, applied=0, carried>0`)

Caveat: `applied=0` means `PropAudit` found no direct application of a proof of the named head; unfolded applications can still occur and require per-item source checks before proposing deletion.

### A. Trivial Placeholder (1)
- `GlobalTheory.Published.UnusedSlot72` (carried 5x): literally `abbrev GlobalTheory.Published.UnusedSlot72 : Prop := True` (`DiscreteSpectrumResidualClassification.lean:7`). Safe deletion/cleanup candidate.

### B. Proved via Parent Bundle Conjunct / Alias (8)
- `ArMetric` (car=1): conjunct of `ArCalc` (`arCalc_direct`).
- `CohDimTwo` (car=16) and `CohDimTwoGlobal` (car=1): proved via `GlobalTheory.twist_front_inputs` (`CohDimTwoLocal` is applied 1x).
- `DeRhamVectorExtension.Family.Tangent` (car=1) and `.Filtered` (car=1): conjuncts of `DeRhamVectorExtension` (`exists_canonical_deRham_rigidExtension_family`).
- `BaseChangeDefiniteUnitaryGroup` (car=12), `BaseChangeIsobaricTransfer` (car=3), `DoublingMethodLocalZetaIntegrals` (car=38): `abbrev`s in `DiscreteSpectrumResidualClassification.lean` for `DefiniteN` (`definiteN_of` ← `baseChangeNB`), `BaseChangeIsobaricN` (`baseChangeNB`), and `ResidueKilled.DM` (`dm_of_two`).

### C. Proved Directly in Closure by Explicit Theorem Witness (51)
All 51 have concrete theorem witnesses in `why_published.txt` (not unfolding-only):
- **Direct `_holds` / outright theorems (36):**
  `HeckeEntire` (`HeckeEntire_holds`), `HasseNorm` (`CNorm.hasseNorm`), `L2ExtensionLogCanonical` (`l2ExtensionLogCanonical'`), `FlagPushForward` (`fullFlagBundle_pushForward_formula`), `ChowFormHyperplaneSection` (`chow_form_hyperplane_section`), `PointSeparationPair` (`NSI.pointSeparationPair`), `LocalConverseGL` (`LConv.localConverseGL`), `AdmissibleCoefficientsAnalytic` (`Hypotheses₂.admissibleCoefficientsAnalytic`), `WeylBranching` (`Stage1.PM.weylBranching`), `HolomorphicDiscreteSeries` (`HolDS.holomorphicDiscreteSeries_holds`), `BernsteinUnitaryProductIrreducible` (`RgUd.All.bernsteinUnitaryProductIrreducible`), `CMPotentialGoodReductionSt` (`Lit.cmPotentialGoodReduction`), `CuspidalMirabolic` (`cuspidalMirabolic_holds`), `principalPolarisationOneSection` (`AbLaw.principalPolarisation_unique_section`), `ThetaRationalInvariance` (`Stage1.PM.thetaRationalInvariance`), `InfinitesimalEquivalence` (`GKPort.Closure.infinitesimalEquivalence_unitaryGroupPQ`), `CuspidalExists` (`Hypotheses₂.cuspidalExists_holds`), `AdmissibleClosure` (`GKPort.Closure.admissibleClosure_gKSubmodule`), `HarishChandraAnalyticity` (`Hypotheses₂.harishChandra_analyticity_density`), `StoneVonNeumann` (`Stage1.PM.stoneVonNeumann`), `StandardFunctorsFiniteLength` (`BZGL.standardFunctorsFiniteLength_top`), `MetaplecticRepresentation` (`metaplecticRepresentation_holds`), `SerreTateGoodReductionSt` (`Lit.serreTateGoodReduction`), `DefQuatExists` (`V.Af.defQuatExists`), `KudlaSplittingSplitUnitary` (`kudlaSplittingSplitUnitary`), `GKGlobalisation` (`gkGlobalisation_holds`), `QuadraticClassFieldTheory` (`Stage1.PM.quadraticClassFieldTheory`), `CuspDiscreteDecompositionGL` (`CuspRep.cuspDiscreteDecompositionGL`), `BrauerDegreeZero` (`BrauerZero.brauerDegreeZero`), `CuspidalRestrictsToInduced` (`Mirab.Restr.cuspidalRestrictsToInduced`), `HermitianLocalGlobal` (`Stage1.PM.hermitianLocalGlobal`), `LeviSubmoduleDense` (`Hypotheses₂.leviSubmoduleDense`), `WeilRepresentationExists` (`Lit.weilRepresentationExists_pair`), `IdealInvariantsOneOrbitSt` (`Prw.idealInvariantsOneOrbitSt_holds`), `FormalAlgebraisation.Schemes` (`T.formal_algebraisation_schemes` ← `grothendieck_existence_closed_proj`), `PoitouTate.ConjCompatible` (`PoitouTateConj.conjCompatible`).
- **Conditional theorems whose premises are all proved in closure (15):**
  `GreenSeriesSt` (`greenSeriesSt_of`), `VolGe` (`volGe_of_hilbertSamuel`), `VolNef` (`ArithHilbertSamuel.volNef`), `ArBirational` (`arBirational_of_arProj`), `ProperIntersectionLength` (`PublishedHodgeBundleTheorems.q12`), `FinitenessOfHermitianClasses` (`PublishedHodgeBundleTheorems.p18`), `SquareIntegrableSegment` (`squareIntegrableSegment_of`), `RallisInnerProductConvergent` (`rallis_of_dm`), `ToroidalCharts` (`toroidalCharts_of_siegel_of_forFan`), `NefBigIff` (`NefRiemannRoch.nefBigIff`), `FubiniStudyChowHeight` (`fubiniStudy_chowHeight_formula`), `ArDegree` (`arDegree_of`), `TemperedProductOfSquareIntegrable` (`Cas.temperedProduct`), `CanonicalExtensionRankOne` (`PublishedHodgeBundleTheorems.q2`), `FlathFactorisation` (`flathFactorisation_of`).

## 4. Breakdown of the 27 `trivial` Predicates and 3,976 `trivial-use` Rows (`audit_now.tsv`)

To avoid misreading the summary counts in `audit_now.log`:
- **17 of the 27 `trivial` predicates are normal indexed inductives with a 0-field base-case constructor** (`IsSmoothBlowupSeq.id`, `IsBlowupSeq.id`, `IsSncBlowupSeq.id`, `Reach.zero`, `Reach.base`, `Interleave.nil`, `Shuffle.nil`, `ListInf.nil`, `Tile.empty`, `LoweringWord.base`, `IsLoweringWord.base`, `LoweringWordAlt.zero`, `ExpSum.zero`, `Low.one`, `U1.one`). `PropAudit` flags any `Prop` inductive with a 0-field constructor regardless of indices.
- **Only 10 of the 27 are actual `:= True` definitions**, all explicitly named as unused slots or unrestricted predicates:
  - 3 unused slots: `GlobalTheory.Published.UnusedSlot72`, `UpperTheory.GalS.UnusedSlot55`, `GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.trivialClassCondition`.
  - 7 explicit unrestricted/trivial predicates: `GlobalTheory.Mem.Top.Bl.anyGeometry`, `GlobalTheory.BigTop.Fun.trivialTieCondition`, `Formalism.L2.Pj.trivialClassCondition`, `Formalism.L2.PjFree.trivialClassCondition`, `UpperTheory.GalS.NoCondition`, `UpperTheory.One.M.TrivialCondition`, `UpperTheory.V.U3.GCond.noCondition`.
- **The 3,976 `trivial-use` rows are overwhelmingly unrestricted filter parameters**, led by `fun ... => True` passed as argument 5 of `Formalism.IndefR.Datum.latO` (1,760 rows), `GlobalTheory.LatticeStable.smul_mem_latO` (111), `GlobalTheory.FinPl.MxAt` (102), `GlobalTheory.FinPl.Vac` (79), `GlobalTheory.Dieu.Base.M` (76), and `Formalism.L2.Pj.vAtV`/`PtV` (75 each). These represent "no extra filter condition" rather than hidden vacuous proofs.

