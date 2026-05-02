open HolKernel Parse boolLib bossLib;

open hurdUtils util_probTheory extrealTheory sigma_algebraTheory
     measureTheory borelTheory lebesgueTheory martingaleTheory
     probabilityTheory;

val _ = new_theory "prob_leftover";

(* ------------------------------------------------------------------------- *)
(*  Convergence theorems and their applications [1, Chapter 9 & 12]         *)
(* ------------------------------------------------------------------------- *)

(* A generalization of Beppo Levi's Theorem 9.6 (lebesgue_monotone_convergence)
   This is Theorem 12.1 (monotone convergence) of [1, p.96].
 *)
val integrable_monotone_convergence_sup = store_thm (* new *)
  ("integrable_monotone_convergence_sup",
  ``!m f u. measure_space m /\
        (!n. u n IN measurable (m_space m, measurable_sets m) Borel) /\
        (!x. x IN m_space m ==> mono_increasing (\n. u n x)) /\
        (!x. x IN m_space m ==> (sup (IMAGE (\n. u n x) UNIV) = f x)) /\
        sup (IMAGE (\n. integral m (u n)) UNIV) < PosInf
      ==>
        integrable m f /\
        (integral m f = sup (IMAGE (\n. integral m (u n)) UNIV))``,
    cheat);

val integrable_monotone_convergence_inf = store_thm (* new *)
  ("integrable_monotone_convergence_inf",
  ``!m f u. measure_space m /\
        (!n. u n IN measurable (m_space m, measurable_sets m) Borel) /\
        (!x. x IN m_space m ==> mono_decreasing (\n. u n x)) /\
        (!x. x IN m_space m ==> (inf (IMAGE (\n. u n x) UNIV) = f x)) /\
        NegInf < inf (IMAGE (\n. integral m (u n)) UNIV)
      ==>
        integrable m f /\
        (integral m f = inf (IMAGE (\n. integral m (u n)) UNIV))``,
    cheat);

(* Lebesgue's dominated convergence (Theorem 12.2 [1, p.97])

  "Lebesgue`s theorem gives merely sufficient - but easily verifiable - conditions
   for the interchange of limits and integrals; the ultimate version for such a result
   with necessary and sufficient conditions will be given in the form of Vitali`s
   convergence theorem."
 *)

(* TODO: enhance lebesgue_dominated_convergence with this definition *)
Definition uniformly_bounded_def :
   uniformly_bounded m (u :num -> 'a -> extreal) =
     ?w. integrable m w /\
        (!x. x IN m_space m ==> 0 <= w x /\ w x <> PosInf) /\
        (!n. AE x::m. abs (u n x) <= w x)
End

val lebesgue_dominated_convergence = store_thm (* new *)
  ("lebesgue_dominated_convergence",
  ``!m w f u. measure_space m /\
        (!n. u n IN measurable (m_space m, measurable_sets m) Borel) /\
        (!n. integrable m (u n)) /\ uniformly_bounded m u /\
        (AE x::m. (\n. real (u n x)) --> real (f x))
      ==>
        (\n. real (integral m (\x. abs (u n x - f x)))) --> 0 /\
        (\n. real (integral m (u n))) --> real (integral m f)``,
    cheat);

(* To be used by Vitali's convergence theorem [1].
  "It follows the universal formulation due to G. A. Hunt [2, p. 33]." [1, p.163] *)
val uniformly_integrable_def = Define
   `uniformly_integrable m (f :num -> 'a -> extreal) =
    !e. 0 < e ==>
        ?w. nonneg w /\ integrable m w /\
            sup {r | ?u n. (u = f n) /\
                           (r = ((abs o u) * m) {x | w x < (abs o u) x})} < e`;
 *)

(* Theorem 22.7 (Vitali) [1, p. 262], which generalizes Lebesgue`s dominated
   convergence theorem (Lebesgue_dominated_convergence).

   named after Giuseppe Vitali (1875-1932), an Italian mathematician [5].

val vitali_uniform_convergence = store_thm (* new *)
  ("vitali_uniform_convergence",
  ``not expressible at this moment``,
    cheat);
 *)

(*** probabilityTheory ***)

(* (pairwise) independence implies uncorrelatedness, provided second moments are
   finite [2, p.108]. (This requires Fibini's theorem.)
val indep_imp_uncorrelated = store_thm
  ("indep_imp_uncorrelated",
  ``!p X Y. finite_second_moments p X /\
            finite_second_moments p Y /\
            indep_rv p X Y Borel Borel ==> uncorrelated p X Y``,
    cheat);
 *)

(* additions in martingaleTheory

Theorem SPACE_SIGMA_FUNCTION :
    !sp A f. space (sigma_function sp A f) = sp
Proof
    RW_TAC std_ss [sigma_function_def, space_def]
QED

Theorem SIGMA_FUNCTION_SUBSET :
    !sp sts A f. subset_class (space A) (subsets A) /\
                 sigma_algebra (sp,sts) /\ f IN (sp -> space A) ==>
                 subsets (sigma_function sp A f) SUBSET sts
Proof
    RW_TAC std_ss [sigma_function_def, SUBSET_DEF, subsets_def,
                   IN_IMAGE, IN_FUNSET]
 >> RW_TAC std_ss [PREIMAGE_def]

QED
 *)

(* The sigma-algebra generated from any A/B-measurable function X is
   a sub-sigma-algebra of A (really?)
Theorem SIGMA_FUNCTION_SUB_SIGMA_ALGEBRA :
    !X A B. X IN measurable A B ==>
            sub_sigma_algebra (sigma_function (space A) B X) A
Proof
    RW_TAC std_ss [IN_MEASURABLE, space_def]
 >> `X IN measurable (sigma (space A) B X) B` by PROVE_TAC [SIGMA_MEASURABLE]
 >> fs [IN_MEASURABLE, sub_sigma_algebra_def, SPACE_SIGMA_FUNCTION]
 >> 
QED
 *)

Theorem negligible_measure_zero : (* new *)
    !s. s IN measurable_sets lebesgue /\ (measure lebesgue s = 0) ==> negligible s
Proof
    RW_TAC std_ss [measure_lebesgue, IN_UNIV]
 >> Know `!n. integral (line n) (indicator s) = 0`
 >- (GEN_TAC >> rw [GSYM REAL_LE_ANTISYM]
     >- (fs [Once (GSYM le_antisym), sup_le'] \\
         REWRITE_TAC [GSYM extreal_le_eq, GSYM extreal_of_num_def] \\
         FIRST_X_ASSUM MATCH_MP_TAC \\
         Q.EXISTS_TAC ‘n’ >> REWRITE_TAC []) \\
     MATCH_MP_TAC INTEGRAL_DROP_POS >> rw [DROP_INDICATOR_POS_LE] \\
     MATCH_MP_TAC in_sets_lebesgue_imp >> art [])
 >> DISCH_TAC
 >> FULL_SIMP_TAC std_ss [negligible, integral, line, GSYM interval]
 >> Q.PAT_X_ASSUM ‘sup {Normal 0 | n | T} = 0’ K_TAC (* useless *)
 >> qx_genl_tac [‘a’, ‘b’]
 >> Cases_on ‘b < a’
 >- fs [INTERVAL_EQ_EMPTY, HAS_INTEGRAL_EMPTY]
 >> FULL_SIMP_TAC std_ss [real_lt] (* now ‘a <= b’ *)
 >> Know ‘!n. integral (interval [-&n,&n]) (indicator s) = 0’
 >- rw [integral] >> DISCH_TAC
 >> Q.PAT_X_ASSUM ‘!n. (@y. (indicator s has_integral y) _) = 0’ K_TAC
 >> simp [HAS_INTEGRAL_INTEGRABLE_INTEGRAL]
 >> STRONG_CONJ_TAC (* integrable *)
 >- (rw [integrable_on] >> Q.EXISTS_TAC ‘0’ \\
    ‘?n1. abs a <= &n1’ by METIS_TAC [SIMP_REAL_ARCH] \\
    ‘?n2. abs b <= &n2’ by METIS_TAC [SIMP_REAL_ARCH] \\
     Q.PAT_X_ASSUM ‘!n. P’ (STRIP_ASSUME_TAC o (Q.SPEC ‘MAX n1 n2’)) \\
     Know ‘(indicator s has_integral 0) (interval [-&MAX n1 n2, &MAX n1 n2])’
     >- (rw [HAS_INTEGRAL_INTEGRABLE_INTEGRAL] \\
         IMP_RES_TAC in_sets_lebesgue_imp \\
         fs [line, GSYM interval]) \\
     POP_ASSUM K_TAC >> DISCH_TAC \\ (* replaced assumption *)
  (* applying HAS_INTEGRAL_COMBINE *)

     cheat)
 >> 
    cheat
QED

Theorem complete_measure_space_lebesgue : (* new *)
    complete_measure_space lebesgue
Proof
    REWRITE_TAC [complete_measure_space_def]
 >> STRONG_CONJ_TAC
 >- REWRITE_TAC [measure_space_lebesgue]
 >> RW_TAC std_ss [null_set_def]
 >> ‘negligible s’ by PROVE_TAC [negligible_measure_zero]
 >> MATCH_MP_TAC negligible_in_sets_lebesgue
 >> PROVE_TAC [NEGLIGIBLE_SUBSET]
QED

(*
val indep_varD = store_thm ("indep_varD",
  ``!p M1 X X1 M2 Y Y1. prob_space p /\ indep_var p M1 X M2 Y /\
                  X1 IN measurable_sets M1 /\ Y1 IN measurable_sets M2 ==>
    (prob p (PREIMAGE (\x. (X x, Y x)) (X1 CROSS Y1) INTER m_space p) =
     prob p (PREIMAGE X X1 INTER p_space p) *
     prob p (PREIMAGE Y Y1 INTER p_space p))``,
  RW_TAC std_ss [] THEN
  Q_TAC SUFF_TAC `prob p (PREIMAGE (\x. (X x,Y x)) (X1 CROSS Y1) INTER m_space p) =
   prob p (BIGINTER {PREIMAGE ((\i. if i = 0 then X else Y) i)
    ((\i. if i = 0 then X1 else Y1) i) INTER p_space p | i IN {z:num | (z = 0) \/ (z = 1)}})` THENL
  [DISC_RW_KILL,
   AP_TERM_TAC THEN SIMP_TAC std_ss [PREIMAGE_def, EXTENSION, GSPECIFICATION] THEN
   SIMP_TAC std_ss [CROSS_DEF, IN_INTER, IN_BIGINTER, GSPECIFICATION, EXISTS_PROD] THEN
   RW_TAC std_ss [GSYM p_space_def] THEN EQ_TAC THEN
   RW_TAC std_ss [IN_UNIV, GSPECIFICATION, IN_INTER] THEN
   ASM_SIMP_TAC std_ss [GSPECIFICATION, IN_INTER] THENL
   [POP_ASSUM (MP_TAC o Q.SPEC `PREIMAGE X X1 INTER p_space p`) THEN
    `x IN PREIMAGE X X1 INTER p_space p ==> X x IN X1` by ASM_SET_TAC [PREIMAGE_def] THEN
    DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    Q.EXISTS_TAC `0` THEN SIMP_TAC arith_ss [PREIMAGE_def],
    POP_ASSUM (MP_TAC o Q.SPEC `PREIMAGE Y Y1 INTER p_space p`) THEN
    `x IN PREIMAGE Y Y1 INTER p_space p ==> Y x IN Y1` by ASM_SET_TAC [PREIMAGE_def] THEN
    DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    Q.EXISTS_TAC `1` THEN SIMP_TAC arith_ss [PREIMAGE_def],
    ALL_TAC] THEN
   POP_ASSUM (MP_TAC o Q.SPEC `PREIMAGE X X1 INTER p_space p`) THEN
   `x IN PREIMAGE X X1 INTER p_space p ==> x IN p_space p` by ASM_SET_TAC [PREIMAGE_def] THEN
   DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
   Q.EXISTS_TAC `0` THEN SIMP_TAC arith_ss [PREIMAGE_def]] THEN
  Q.ABBREV_TAC `J = {z:num | (z = 0) \/ (z = 1)}` THEN
  Q.ABBREV_TAC `XX = (\i:num. if i = 0 then X else Y)` THEN
  Q.ABBREV_TAC `AA = (\i:num. if i = 0 then X1 else Y1)` THEN
  Q_TAC SUFF_TAC `prob p (BIGINTER {PREIMAGE (XX i) (AA i) INTER p_space p | i IN J}) =
      Normal (product J (\i. real (prob p (PREIMAGE (XX i) (AA i) INTER p_space p))))` THENL
  [DISC_RW_KILL,
   MATCH_MP_TAC indep_varsD THEN FULL_SIMP_TAC std_ss [indep_var] THEN
   Q.EXISTS_TAC `(\i. if i = 0 then M1 else M2)` THEN Q.EXISTS_TAC `J` THEN
   ASM_SIMP_TAC std_ss [] THEN
   CONJ_TAC THENL [ASM_SET_TAC [], ALL_TAC] THEN
   CONJ_TAC THENL [ALL_TAC, ASM_SET_TAC []] THEN
   Q.UNABBREV_TAC `J` THEN RW_TAC std_ss [FINITE_DEF] THEN
   FIRST_ASSUM (MP_TAC o Q.SPEC `{1}`) THEN SIMP_TAC std_ss [INSERT_DEF] THEN
   FIRST_X_ASSUM (MP_TAC o Q.SPEC `{}`) THEN SIMP_TAC std_ss [INSERT_DEF] THEN
   ASM_SIMP_TAC std_ss [] THEN DISCH_THEN (ASSUME_TAC o Q.SPEC `0`) THEN
   DISCH_THEN (ASSUME_TAC o Q.SPEC `0`) THEN ASM_SET_TAC []] THEN
  Q_TAC SUFF_TAC `J = 0 INSERT {1}` THENL
  [DISC_RW_KILL, Q.UNABBREV_TAC `J` THEN ASM_SET_TAC []] THEN
  SIMP_TAC std_ss [PRODUCT_CLAUSES, FINITE_SING, IN_SING] THEN
  SIMP_TAC std_ss [PRODUCT_SING, GSYM extreal_mul_def] THEN
  Q.UNABBREV_TAC `XX` THEN Q.UNABBREV_TAC `AA` THEN SIMP_TAC arith_ss [] THEN
  `random_variable X p (m_space M1, measurable_sets M1) /\
   random_variable Y p (m_space M2, measurable_sets M2)`
   by METIS_TAC [indep_var_rv] THEN
  Q_TAC SUFF_TAC `PREIMAGE X X1 INTER p_space p IN events p` THENL
  [DISCH_TAC,
   FULL_SIMP_TAC std_ss [random_variable_def, IN_MEASURABLE] THEN
   FULL_SIMP_TAC std_ss [IN_FUNSET, space_def, subsets_def, prob_space_def]] THEN
  Q_TAC SUFF_TAC `PREIMAGE Y Y1 INTER p_space p IN events p` THENL
  [DISCH_TAC,
   FULL_SIMP_TAC std_ss [random_variable_def, IN_MEASURABLE] THEN
   FULL_SIMP_TAC std_ss [IN_FUNSET, space_def, subsets_def, prob_space_def]] THEN
  Q_TAC SUFF_TAC `prob p (PREIMAGE X X1 INTER p_space p) <> NegInf` THENL
  [DISCH_TAC,
   RW_TAC std_ss [lt_infty, prob_def] THEN
   MATCH_MP_TAC lte_trans THEN Q.EXISTS_TAC `0` THEN
   FULL_SIMP_TAC std_ss [prob_space_def, GSYM lt_infty, num_not_infty] THEN
   METIS_TAC [measure_space_def, positive_def, p_space_def, events_def]] THEN
  Q_TAC SUFF_TAC `prob p (PREIMAGE Y Y1 INTER p_space p) <> NegInf` THENL
  [DISCH_TAC,
   RW_TAC std_ss [lt_infty, prob_def] THEN
   MATCH_MP_TAC lte_trans THEN Q.EXISTS_TAC `0` THEN
   FULL_SIMP_TAC std_ss [prob_space_def, GSYM lt_infty, num_not_infty] THEN
   METIS_TAC [measure_space_def, positive_def, p_space_def, events_def]] THEN
  Q_TAC SUFF_TAC `prob p (PREIMAGE X X1 INTER p_space p) <> PosInf` THENL
  [DISCH_TAC,
   RW_TAC std_ss [lt_infty, prob_def] THEN
   MATCH_MP_TAC let_trans THEN Q.EXISTS_TAC `1` THEN
   FULL_SIMP_TAC std_ss [prob_space_def, GSYM lt_infty, num_not_infty] THEN
   MATCH_MP_TAC le_trans THEN Q.EXISTS_TAC `measure p (p_space p)` THEN
   CONJ_TAC THENL [ALL_TAC, ASM_SIMP_TAC std_ss [le_lt]] THEN
   MATCH_MP_TAC INCREASING THEN ASM_SIMP_TAC std_ss [MEASURE_SPACE_INCREASING] THEN
   FULL_SIMP_TAC std_ss [events_def, p_space_def, MEASURABLE_SETS_SUBSET_SPACE] THEN
   ASM_SIMP_TAC std_ss [MEASURE_SPACE_MSPACE_MEASURABLE]] THEN
  Q_TAC SUFF_TAC `prob p (PREIMAGE Y Y1 INTER p_space p) <> PosInf` THENL
  [DISCH_TAC,
   RW_TAC std_ss [lt_infty, prob_def] THEN
   MATCH_MP_TAC let_trans THEN Q.EXISTS_TAC `1` THEN
   FULL_SIMP_TAC std_ss [prob_space_def, GSYM lt_infty, num_not_infty] THEN
   MATCH_MP_TAC le_trans THEN Q.EXISTS_TAC `measure p (p_space p)` THEN
   CONJ_TAC THENL [ALL_TAC, ASM_SIMP_TAC std_ss [le_lt]] THEN
   MATCH_MP_TAC INCREASING THEN ASM_SIMP_TAC std_ss [MEASURE_SPACE_INCREASING] THEN
   FULL_SIMP_TAC std_ss [events_def, p_space_def, MEASURABLE_SETS_SUBSET_SPACE] THEN
   ASM_SIMP_TAC std_ss [MEASURE_SPACE_MSPACE_MEASURABLE]] THEN
  METIS_TAC [normal_real]);

*)

(* ------------------------------------------------------------------------- *)
(*      The Law of the Iterated Logarithm (for I.I.D. r.v.'s) [6, p.154]     *)
(* ------------------------------------------------------------------------- *)

(*  LIL statements

   TODO: confirm the position(s) of ‘variance p (X 0)’ in the statements
 *)
Definition LIL_def :
    LIL p X =
    let Z n x = SIGMA (\i. X i x) (count n);
        B n = variance p (Z n)
    in
        AE x::p. limsup (\n. (Z n x - expectation p (Z n)) /
                             sqrt (2 * (B n) * ln (ln (B n)))) = 1
End

(*
Theorem LIL_alt_IID :
    !p X. prob_space p /\ (!n. real_random_variable (X n) p) /\
          indep_vars p X (\n. Borel) UNIV /\
          identical_distribution p X Borel UNIV /\
          integrable p (X 0) ==>
         (LIL p X <=> ...)
Proof
    cheat
QED
 *)

Theorem LIL_IID :
    !p X. prob_space p /\ (!n. real_random_variable (X n) p) /\
          indep_vars p X (\n. Borel) UNIV /\
          identical_distribution p X Borel UNIV /\
          integrable p (X 0)
      ==> LIL p X
Proof
    cheat
QED

val _ = export_theory ();
