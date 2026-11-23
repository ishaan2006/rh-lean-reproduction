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
| 3 | Host field G = (Z/N)^x / W = E0 x H, structure of H and A0, datum (H1)-(H4), psi_D = primitive character, T with exact 4:3 shares, X' = exp(x^(eps/3)), theta = exp(-x^(eps/8)), plus family-coupled clauses B1 (w_{u,j}, b', eta, b'X'=xb), B2 (a_t), second half of B4, and 0 <= a_E <= 2xb in B5. | Sec 4, Prop 4.5 | KerChi, HostRaw, arith, Shares, lam, thin, g_integral, core_gm | **P** | |
| 4 | Count of d in the residue class mod M: done via Linnik in quantitative form (N5) inside Lemma 3.6, giving |P| >= X/(4 m0^2 log X) | Lemma 3.6, Thm 3.8 step 2 | PNTAPRelW, count_a | **P** (mod N5) | |
| 5 | Theta-lift chain, unitary spaces V_j of sig (k+j-1, m-j), word lattices N_nu, common lattice RR, nonvanishing (StepUp, ChainLW) | Sec 5, Thm 5.1, Lem 5.2-5.3, Prop 5.4 | prescribedRowLat, ip_unique, chainUp_of, rulePar_step | **P** (mod Landherr/Scharlau Ch.10 Thm 6.9; Rallis inner product Li Thm 3.2, Gan-Qiu-Takeda Thm 1.1/7.2; Paul Thm 6.1) | Dev/AbelianVarietyTheory: 99k files |
| 6 | Hodge-Tate shape (ShapeJumps / admG2) | Prop 5.4(ii), Lem 5.3(ii) | multW_of_shape, AdmG2TwistSetup.main | **P** (mod Labesse Thm 5.4; Shin Thm 1.2; BLGGT Thm 2.1.1) | 3.5k files, 0.61M lines |
| 7 | (S1): divisibility into dual(RR), operator-norm chain hypothesis, (D1)-(D4), (T1)-(T6) of Part I Thm 10.7 for the family | Lem 6.1, Lem 6.5, Thm 6.6 | oneMap_of_coord, opNormAt_pos_of, htMap_le_of_bound, wordFacts_of | **P** | 0.16M / 0.29M lines |
| 8 | (S1) Selmer colength E_b (Bloch-Kato rank, lifting exponents e_L, sum over small primes) | Thm 6.6(ii) | rank_le_row, errB_of_units | **P** (s_N, vvTerm defined; sum s_N log l << L^2 proved; BK Prop 3.8/Cor 3.8.4 & FL Thm 4.3/\S8 cited) | |
| 9 | (S2) row-parameter bounds (a)-(d) and LevelPrimeBudget, StabiliserLogBound, DiscriminantOffsetBound, InertPrimeLossBound | Lem 6.7-6.9, Prop 6.12 | C2atG_of, secondComplement_of_inputs | **P** | |
| 10 | (S3) height comparability | Lem 6.11(i), Prop 6.12 | Compl3 | **P** | |
| 11 | (S4) choice of T(nu) | Lem 6.10, Prop 6.12 | | **P** (mod N1, N5; M0 = 2^(e+2) has real chars only of cond | 8) | |
| 12 | (S5) reference slopes | Lem 6.11(ii), Prop 6.12 | linkGLOBAL7_min | **P** (mod Bost \S4.1 Prop 4.1.2) | 1.4k files, 0.35M lines |
| 13 | (S6) Places_at: slope identity and index bounds | Lem 7.1, Prop 7.2 | mu_index_sum, mu_eq, muMax_le, places_at_of, slopesN_at_of | **P** | 0.13M lines |
| 14 | (S7) StarAt orbitwise bound (key_pow_dvd, kS_ord, kW_ord, key3Ord), lo_G/fl_G sums, loss_bound_at | Lem 7.3-7.6, Thm 7.7 | key_pow_dvd, kS_ord, kW_ord, starAll_of, losses_of_small_share_weight | **P** | 0.05M (starAll), LinkG concrete 0.46M |
| 15 | (S8) ChosenProviso (class number formula) | Lem 8.2, Prop 8.5(i) | mass_corollary, proviso_e | **P** (mod Shimura Thm 5.8, Kottwitz tau=2) | 1.9k files, 0.43M lines |
| 16 | (S8) LinkS Gram decorrelation (four kernel clauses, ResidEv, CountAllPointsClass) | Lem 8.4, Prop 8.5(ii) | hsNormSq_add_le, diag_unproj, linkS_concl, eF_nonneg_and_le_exp_neg | **P** (mod geometric trace formula + Shin Thms 4.11-4.12) | 3.3k files, 0.76M lines |
| 17 | (S8) LinkIRR irreducibility decay | Lem 8.3, Prop 8.5(iii) | weight_numbers_bound, delp_of_allRows, linkIRR_of_allRows | **P** (mod Shin Cor 4.12, Shin-Templier Thm 9.16, Green Thm 14, Deligne-Lusztig Cor 7.6) | 1.4k files, 0.28M lines |
| 18 | Sha window VWin | Sec 8.2, Lem 8.6-8.8, Thm 8.9 | prime_of, stick_of, vwin_of_counts | **P** (mod Mazur-Wiles Ch.1 \S10, Milne Ch.I Thm 4.10, Coates-Sinnott Thm 1.3, Washington Ch.4/6, Ferrero-Washington, Kato Thm 12.5) | 0.18M lines |
| 19 | (C3)-(C7), (N4), (N5): exact theorem numbers and hypothesis checks; (C8) removed | Sec 1.2, Sec 3.1, Sec 10 | | **P** | |

Done in Part I: Theorems A, B, C1; Theorem F; Prop 9.4; the sqrt(p) lemma; Prop 10.1 and Lemma
10.2; Theorem 10.7 (divisor inequality).
