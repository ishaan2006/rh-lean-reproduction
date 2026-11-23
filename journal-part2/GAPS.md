# Part II gap ledger (what stands between Part II v1.2 and a complete conventional proof)

Status codes: **P** = proved conventionally in Part I/II; **A** = Part II proves only the real-number
assembly, the substantive input is a cited Lean statement; **L** = cited Lean statement, no
conventional argument; **X** = Part II's paraphrase does not match the formal statement.

Import cone = files/lines transitively imported by the Lean file that proves the statement (archive
40e56bab). This over-counts (imports, not uses) but gives the order of magnitude.

| # | Obligation | Part II | Lean | Status | Import cone |
|---|---|---|---|---|---|
| 1 | (C1) replaced by standard inputs (N1)-(N5) (zero-free region + Landau-Page + effective real zeros; IK Thm 5.27; explicit formula; Montgomery density; Linnik in quantitative form). Square-root bounds for all twists rho*chi_q, rho*chi_d, rho*chi_q*chi_d (rho of conductor dividing lcm(8,f_psi)) proved in full: identities, tail under box, mean square via reciprocity, Sobolev/Markov uniformity, equidistribution with one exceptional s, box-failure count, two-stage choice of (q,d). | Sec 3 (Thm 3.8) | stage1, stage2, box_of_S, meanSqK, bad_share, twistK, count_a, count_bad, tailK | **P** (mod N1-N5) | 39 files, <5k lines |
| 2 | (C2) relation-free thick set: Behrend construction proved in full (Lemma 4.3), transferred to the cyclic group A0 | Sec 4.3 | hostThickExists | **P** | 8 files |
| 3 | Host field G = (Z/N)^x / W = E0 x H, structure of H and A0, datum (H1)-(H4), psi_D = primitive character, T with exact 4:3 shares, X' = exp(x^(eps/3)), theta = exp(-x^(eps/8)). Proved: B0, B3, first half of B4, B5 except a_E, B6, B7, G_K = G_{F_psi}, Sigma_rest <= 3o x^(1/2+eps). Left to the family (moved to item 5): B1 weights w_{u,j}, b', eta and b'X' <= xb; B2 numbers a_t; second half of B4; a_E in B5. | Sec 4, Prop 4.5 | KerChi, HostRaw, arith, Shares, lam, thin, g_integral, core_gm | **P** for host-level clauses; family clauses -> 5 | |
| 4 | Count of d in the residue class mod M: done via Linnik in quantitative form (N5) inside Lemma 3.6, giving |P| >= X/(4 m0^2 log X) | Lemma 3.6, Thm 3.8 step 2 | PNTAPRelW, count_a | **P** (mod N5) | |
| 5 | Theta-lift chain, word lattices N_nu, common lattice RR, metrics | Sec 4 | (C8) | L | Dev/AbelianVarietyTheory: 99k files |
| 6 | Hodge-Tate shape (ShapeJumps / admG2) | Thm 5.3(ii) | AdmG2TwistSetup.main | L | 3.5k files, 0.61M lines |
| 7 | (S1): divisibility into dual(RR), operator-norm chain hypothesis, (D1)-(D4), (T1)-(T6) of Part I Thm 10.7 for the family | Thm 5.3(iii), Lem 5.1 | divClausesR_of, linkDIV_at_words | A | 0.16M / 0.29M lines |
| 8 | (S1) Selmer colength E_b (Bloch-Kato rank, lifting exponents e_L, sum over small primes) | Thm 5.3(ii) | rank_le_row, errB_of_units | sketch (undefined s_N, locDeg, vvTerm) | |
| 9 | (S2) row-parameter bounds (a)-(d) and LevelPrimeBudget, StabiliserLogBound, DiscriminantOffsetBound, InertPrimeLossBound | Lem 5.4-5.5, Prop 5.6 | C2atG_of, secondComplement_of_inputs | A | |
| 10 | (S3) height comparability | Prop 5.6 | LinkDIV_at (final clause) | L | |
| 11 | (S4) choice of T(nu) | Prop 5.6 | | sketch | |
| 12 | (S5) reference slopes | Prop 5.6 | linkGLOBAL7_min | L | 1.4k files, 0.35M lines |
| 13 | (S6) Places_at: slope identity and index bounds | Prop 6.1 | NprimeMuR, slopesN_at_of | L | 0.13M lines |
| 14 | (S7) StarAt orbitwise bound (kS_ord, key3Ord), lo_G/fl_G sums, loss_bound_at | Thm 6.5 | starAll_of, LinkG | A | 0.05M (starAll), LinkG concrete 0.46M |
| 15 | (S8) ChosenProviso (class number formula) | Prop 7.2(i) | chosenProviso_4f | L | 1.9k files, 0.43M lines |
| 16 | (S8) LinkS Gram decorrelation (four kernel clauses, ResidEv, CountAllPointsClass) | Prop 7.2(ii) | theoremS_link_concrete | L | 3.3k files, 0.76M lines |
| 17 | (S8) LinkIRR irreducibility decay | Prop 7.2(iii) | linkIRR_of_tied | L | 1.4k files, 0.28M lines |
| 18 | Sha window VWin | Sec 7.2 | vwin_of_counts | partly A | 0.18M lines |
| 19 | (C3)-(C7): exact theorem numbers, and a check that each formal statement follows from the published one | Sec 10 | | citations to pin; also pin (N4) Montgomery Topics Thm 12.2 form and (N5) exact statement (IK ch. 18 / Gallagher Thm 7) |

Done in Part I: Theorems A, B, C1; Theorem F; Prop 9.4; the sqrt(p) lemma; Prop 10.1 and Lemma
10.2; Theorem 10.7 (divisor inequality).
