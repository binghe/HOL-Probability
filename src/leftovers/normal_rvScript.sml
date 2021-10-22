(* ========================================================================= *)
(*                                                                           *)
(*                    Probability Density Function Theory                    *)
(*                                                                           *)
(*        (c) Copyright,                                                     *)
(*                       Muhammad Qasim,                                     *)
(*                       Osman Hasan,                                        *)
(*                       Hardware Verification Group,                        *)
(*                       Concordia University                                *)
(*                                                                           *)
(*            Contact:  <m_qasi@ece.concordia.ca>                            *)
(*                                                                           *)
(*                                                                           *)
(* Note: This theory has been ported from hol light                          *)
(* Last update: Jan, 2015                                                    *)
(*                                                                           *)
(* ========================================================================= *)

open HolKernel Parse boolLib bossLib numLib unwindLib tautLib Arith prim_recTheory
combinTheory quotientTheory arithmeticTheory hrealTheory realaxTheory realTheory
realLib jrhUtils pairTheory seqTheory limTheory transcTheory listTheory mesonLib
boolTheory topologyTheory pred_setTheory util_probTheory optionTheory numTheory
sumTheory InductiveDefinition ind_typeTheory pred_setLib iterate_hvgTheory
card_hvgTheory product_hvgTheory topology_hvgTheory derivative_hvgTheory
integration_hvgTheory real_sigmaTheory extreal_hvgTheory measure_hvgTheory
lebesgue_hvgTheory probability_hvgTheory lebesgue_measure_hvgTheory;

val _ = new_theory "normal_rv_hvg";

(* ------------------------------------------------------------------------- *)
(* MESON, METIS, SET_TAC, SET_RULE, ASSERT_TAC, ASM_ARITH_TAC                *)
(* ------------------------------------------------------------------------- *)

fun K_TAC _ = ALL_TAC;
fun MESON ths tm = prove(tm,MESON_TAC ths);
fun METIS ths tm = prove(tm,METIS_TAC ths);

val DISC_RW_KILL = DISCH_TAC THEN ONCE_ASM_REWRITE_TAC [] THEN
                   POP_ASSUM K_TAC;

val IN_REST = store_thm ("IN_REST",
 ``!x:'a. !s. x IN (REST s) <=> x IN s /\ ~(x = CHOICE s)``,
  REWRITE_TAC[REST_DEF, IN_DELETE]);

fun ASSERT_TAC tm = SUBGOAL_THEN tm STRIP_ASSUME_TAC;

val ASM_ARITH_TAC = REPEAT (POP_ASSUM MP_TAC) THEN ARITH_TAC;
val ASM_REAL_ARITH_TAC = REPEAT (POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC;

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* ------------------------------------------------------------------------- *)

(* DONE *)
val lemma1 = store_thm ("lemma1", (* new: distribution_space_eq_1 *)
 ``!p X. prob_space p ==> (distribution p X (IMAGE X (m_space p)) = 1)``,
  REWRITE_TAC [prob_space_def] THEN REPEAT STRIP_TAC THEN
  SIMP_TAC std_ss [distribution_def] THEN
  SIMP_TAC std_ss [IMAGE_DEF, PREIMAGE_def, INTER_DEF, GSPECIFICATION] THEN
  REWRITE_TAC [GSYM p_space_def, prob_def] THEN
  REWRITE_TAC [SET_RULE ``{x | (?x''. (X x = X x'') /\ x'' IN s) /\ x IN s} = s``] THEN
  ASM_REWRITE_TAC []);

(* ------------------------------------------------------------------------- *)
(* RN_deriv                                                                  *)
(* ------------------------------------------------------------------------- *)

(* (!x. 0 <= f x) *)
val RN_deriv = new_definition ("RN_deriv",
  ``RN_deriv m v = @f. f IN measurable (m_space m,measurable_sets m) Borel /\
                    (!x. 0 <= f x) /\ !A. A IN measurable_sets m ==>
                     (pos_fn_integral m (\x. f x * indicator_fn A x) =
                      measure v A)``);

val RN_derivI = store_thm ("RN_derivI",
  ``!f M N. f IN measurable (m_space M, measurable_sets M) Borel /\
            (!x. 0 <= f x) /\ (density M f = measure_of N) /\
             measure_space M /\ measure_space N /\
            (measurable_sets M = measurable_sets N) ==>
            (density M (RN_deriv M N) = measure_of N)``,
  RW_TAC std_ss [RN_deriv] THEN SELECT_ELIM_TAC THEN
  `m_space M = m_space N` by METIS_TAC [sets_eq_imp_space_eq] THEN
  Q_TAC SUFF_TAC `measurable_sets N SUBSET POW (m_space N)` THENL
  [DISCH_TAC,
   FULL_SIMP_TAC std_ss [measure_space_def, sigma_algebra_iff2]] THEN
  `sigma_sets (m_space N) (measurable_sets N) = measurable_sets N`
   by METIS_TAC [sigma_sets_eq, measure_space_def] THEN
  RW_TAC std_ss [] THENL
  [Q.EXISTS_TAC `f` THEN FULL_SIMP_TAC std_ss [] THEN RW_TAC std_ss [] THEN
   UNDISCH_TAC ``density M f = measure_of N`` THEN
   GEN_REWR_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [GSYM MEASURE_SPACE_REDUCE] THEN
   FULL_SIMP_TAC std_ss [density, measure_of, FUN_EQ_THM] THEN
   DISCH_THEN (MP_TAC o Q.SPEC `A`) THEN
   FULL_SIMP_TAC std_ss [extreal_max_def, le_mul, indicator_fn_pos_le] THEN
   METIS_TAC [MEASURE_SPACE_REDUCE],
   ALL_TAC] THEN
  GEN_REWR_TAC (RAND_CONV o RAND_CONV) [GSYM MEASURE_SPACE_REDUCE] THEN
  FULL_SIMP_TAC std_ss [density, measure_def, measure_of] THEN RW_TAC std_ss [] THEN
  SIMP_TAC std_ss [GSYM density] THEN ASM_SIMP_TAC std_ss [measure_space_density] THEN
  FULL_SIMP_TAC std_ss [MEASURE_SPACE_REDUCE] THEN
  FULL_SIMP_TAC std_ss [extreal_max_def, le_mul, indicator_fn_pos_le]);

val density_RN_deriv = store_thm ("density_RN_deriv",
  ``!M N. sigma_finite_measure M /\ measure_space M /\ measure_space N /\
          measure_absolutely_continuous N M /\
         (measurable_sets M = measurable_sets N) ==>
         (density M (RN_deriv M N) = measure_of N)``,
  RW_TAC std_ss [] THEN MATCH_MP_TAC RN_derivI THEN
  Q_TAC SUFF_TAC `sigma_finite_measure M /\ measure_space M /\
    measure_space N /\ measure_absolutely_continuous N M /\
   (measurable_sets M = measurable_sets N)` THENL
  [DISCH_THEN (MP_TAC o MATCH_MP RADON_NIKODYM),
   ASM_SIMP_TAC std_ss []] THEN
  RW_TAC std_ss [] THEN Q.EXISTS_TAC `f` THEN
  ASM_SIMP_TAC std_ss [density] THEN
  `m_space M = m_space N` by METIS_TAC [sets_eq_imp_space_eq] THEN
  Q_TAC SUFF_TAC `measurable_sets N SUBSET POW (m_space N)` THENL
  [DISCH_TAC,
   FULL_SIMP_TAC std_ss [measure_space_def, sigma_algebra_iff2]] THEN
  `sigma_sets (m_space N) (measurable_sets N) = measurable_sets N`
   by METIS_TAC [sigma_sets_eq, measure_space_def] THEN
  GEN_REWR_TAC (RAND_CONV o RAND_CONV) [GSYM MEASURE_SPACE_REDUCE] THEN
  ASM_SIMP_TAC std_ss [FUN_EQ_THM, measure_of, MEASURE_SPACE_REDUCE] THEN
  ASM_SIMP_TAC std_ss [extreal_max_def, le_mul, indicator_fn_pos_le]);

val RN_deriv_positive_integral = store_thm ("RN_deriv_positive_integral",
  ``!M N f. sigma_finite_measure M /\ measure_space M /\ measure_space N /\
          measure_absolutely_continuous N M /\
          (measurable_sets M = measurable_sets N) /\
          f IN measurable (m_space M, measurable_sets M) Borel ==>
          (pos_fn_integral N f =
           pos_fn_integral (density M (RN_deriv M N)) f)``,
  RW_TAC std_ss [] THEN
  Q_TAC SUFF_TAC `pos_fn_integral N f = pos_fn_integral (measure_of N) f` THENL
  [METIS_TAC [density_RN_deriv], ALL_TAC] THEN
  ONCE_REWRITE_TAC [METIS [MEASURE_SPACE_REDUCE]
   ``measure_of N = measure_of (m_space N, measurable_sets N, measure N)``] THEN
  Q_TAC SUFF_TAC `measurable_sets N SUBSET POW (m_space N)` THENL
  [DISCH_TAC,
   FULL_SIMP_TAC std_ss [measure_space_def, sigma_algebra_iff2]] THEN
  `sigma_sets (m_space N) (measurable_sets N) = measurable_sets N`
   by METIS_TAC [sigma_sets_eq, measure_space_def] THEN
  ASM_SIMP_TAC std_ss [measure_of] THEN
  SIMP_TAC std_ss [pos_fn_integral_def] THEN AP_TERM_TAC THEN
  AP_TERM_TAC THEN ABS_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  ABS_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC std_ss [IN_psfis_eq, MEASURE_SPACE_REDUCE] THEN
  AP_TERM_TAC THEN ABS_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN
  AP_TERM_TAC THEN ABS_TAC THEN
  Q_TAC SUFF_TAC `pos_simple_fn N g s a x =
   pos_simple_fn (m_space N,measurable_sets N,
    (\a. if a IN measurable_sets N then measure N a else 0)) g s a x` THENL
  [DISCH_TAC THEN ASM_SIMP_TAC std_ss [],
   SIMP_TAC std_ss [pos_simple_fn_def] THEN EQ_TAC THEN
   RW_TAC std_ss [measure_of, m_space_def, measurable_sets_def, measure_def]] THEN
  MATCH_MP_TAC (METIS [] ``(a ==> (b = c)) ==> (a /\ b = a /\ c)``) THEN
  POP_ASSUM (ASSUME_TAC o ONCE_REWRITE_RULE [EQ_SYM_EQ]) THEN
  POP_ASSUM (fn th => REWRITE_TAC [th]) THEN DISCH_TAC THEN
  AP_TERM_TAC THEN SIMP_TAC std_ss [pos_simple_fn_integral_def] THEN
  FULL_SIMP_TAC std_ss [pos_simple_fn_def] THEN
  FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP EXTREAL_SUM_IMAGE_EQ) THEN
  CONJ_TAC THENL [ALL_TAC, RW_TAC std_ss [measure_def]] THEN
  DISJ1_TAC THEN RW_TAC std_ss [] THENL
  [SIMP_TAC std_ss [lt_infty] THEN MATCH_MP_TAC lte_trans THEN
   Q.EXISTS_TAC `0` THEN CONJ_TAC THENL
   [METIS_TAC [lt_infty, num_not_infty, extreal_of_num_def], ALL_TAC] THEN
   MATCH_MP_TAC le_mul THEN ASM_SIMP_TAC std_ss [extreal_of_num_def, extreal_le_def] THEN
   ASM_SIMP_TAC std_ss [GSYM extreal_of_num_def] THEN
   METIS_TAC [measure_space_def, positive_def], ALL_TAC] THEN
  SIMP_TAC std_ss [lt_infty] THEN MATCH_MP_TAC lte_trans THEN
  Q.EXISTS_TAC `0` THEN CONJ_TAC THENL
  [METIS_TAC [lt_infty, num_not_infty, extreal_of_num_def], ALL_TAC] THEN
  MATCH_MP_TAC le_mul THEN ASM_SIMP_TAC std_ss [extreal_of_num_def, extreal_le_def] THEN
  ASM_SIMP_TAC std_ss [GSYM extreal_of_num_def, measure_def] THEN
  METIS_TAC [measure_space_def, positive_def]);

(* ------------------------------------------------------------------------- *)
(* PDF_def                                                                   *)
(* ------------------------------------------------------------------------- *)

Definition PDF :
    PDF p X = RN_deriv (distribution p X) lborel
End

(* simplifed as (\s. distribution p X) *)
val measurable_distr = new_definition ("measurable_distr",
  ``measurable_distr p X = (\s. if s IN subsets borel then distribution p X s else 0)``);

(* ------------------------------------------------------------------------- *)
(* normal_density                                                            *)
(* ------------------------------------------------------------------------- *)

Definition normal_density_def :
    normal_density m s x =
      (1 / sqrt (2 * pi * s pow 2)) * exp (-((x - m) pow 2) / (2 * s pow 2))
End

val std_normal_density = new_definition("std_normal_density",
  ``std_normal_density = normal_density 0 1``);

val std_normal_density_def = store_thm ("stand_normal_density_def",
  ``!x. std_normal_density x = (1 / sqrt (2 * pi)) * exp (-(x pow 2) / 2)``,
  RW_TAC std_ss [std_normal_density, normal_density] THEN
  SIMP_TAC real_ss [REAL_SUB_RZERO, POW_ONE]);

val normal_density_nonneg = store_thm ("normal_density_nonneg",
  ``!mu sig x. 0 <= normal_density mu sig x``,
  RW_TAC std_ss [normal_density] THEN MATCH_MP_TAC REAL_LE_MUL THEN
  SIMP_TAC std_ss [EXP_POS_LE, GSYM REAL_INV_1OVER, REAL_LE_INV_EQ] THEN
  MATCH_MP_TAC SQRT_POS_LE THEN MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
  [MATCH_MP_TAC REAL_LE_MUL THEN SIMP_TAC real_ss [REAL_LE_LT, PI_POS],
   ALL_TAC] THEN
  SIMP_TAC real_ss [REAL_LE_POW2]);

val normal_density_pos = store_thm ("normal_density_pos",
  ``!mu sig. 0 < sig ==> 0 < normal_density mu sig x``,
  RW_TAC std_ss [normal_density] THEN MATCH_MP_TAC REAL_LT_MUL THEN
  SIMP_TAC std_ss [EXP_POS_LT, GSYM REAL_INV_1OVER, REAL_LT_INV_EQ] THEN
  MATCH_MP_TAC SQRT_POS_LT THEN MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
  [MATCH_MP_TAC REAL_LT_MUL THEN SIMP_TAC real_ss [PI_POS], ALL_TAC] THEN
  SIMP_TAC std_ss [POW_2, REAL_POASQ] THEN ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
  MATCH_MP_TAC REAL_LT_IMP_NE THEN ASM_SIMP_TAC std_ss []);

(* normal_density IN measurable borel Borel *)

val restrict_space = new_definition ("restrict_space",
  ``restrict_space M sp =
    (sp INTER m_space M,
     IMAGE (\a. a INTER sp) (measurable_sets M),
     measure M)``);

val space_restrict_space = store_thm ("space_restrict_space",
  ``!M sp. m_space (restrict_space M sp) = (sp INTER m_space M)``,
  SIMP_TAC std_ss [restrict_space, m_space_def]);

val space_restrict_space2 = store_thm ("space_restrict_space2",
  ``!M sp. measure_space M /\ sp IN measurable_sets M ==>
         (m_space (restrict_space M sp) = sp)``,
  RW_TAC std_ss [restrict_space, m_space_def] THEN
  `sp SUBSET m_space M` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
  ASM_SET_TAC []);

val sets_restrict_space = store_thm ("sets_restrict_space",
  ``!M sp. measurable_sets (restrict_space M sp) = IMAGE (\a. a INTER sp) (measurable_sets M)``,
  RW_TAC std_ss [restrict_space, measurable_sets_def]);

val IN_MEASURABLE_BOREL_normal_density = store_thm ("IN_MEASURABLE_BOREL_normal_density",
  ``!mu sig. (\x. Normal (normal_density mu sig x)) IN
            measurable (m_space lborel, measurable_sets lborel) Borel``,
  RW_TAC std_ss [normal_density, GSYM extreal_mul_def] THEN
  MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL THEN
  Q.EXISTS_TAC `(\x. Normal (exp (-((x - mu) pow 2) / (2 * sig pow 2))))` THEN
  Q.EXISTS_TAC `(1 / sqrt (2 * pi * sig pow 2))` THEN CONJ_TAC THENL
  [RW_TAC std_ss [lborel, m_space_def, measurable_sets_def] THEN
   SIMP_TAC std_ss [GSYM space_borel, SPACE, sigma_algebra_borel], ALL_TAC] THEN
  SIMP_TAC std_ss [] THEN
  Q_TAC SUFF_TAC `(\x. Normal ((\x. exp (-((x - mu) pow 2) / (2 * sig pow 2))) x)) IN
                    measurable (m_space lborel,measurable_sets lborel) Borel` THENL
  [SIMP_TAC std_ss [], ALL_TAC] THEN MATCH_MP_TAC borel_IMP_Borel THEN
  SIMP_TAC std_ss [lborel, m_space_def, measurable_sets_def] THEN
  SIMP_TAC std_ss [GSYM space_borel, SPACE, GSYM borel_measurable] THEN
  MATCH_MP_TAC borel_measurable_continuous_on1 THEN
  Q_TAC SUFF_TAC `(\x. exp ((\x. -((x - mu) pow 2) / (2 * sig pow 2)) x))
                       continuous_on univ(:real)` THENL
  [SIMP_TAC std_ss [], ALL_TAC] THEN
  MATCH_MP_TAC (SIMP_RULE std_ss [o_DEF] CONTINUOUS_ON_COMPOSE) THEN
  SIMP_TAC std_ss [CONTINUOUS_ON_EXP, real_div] THEN
  Q_TAC SUFF_TAC `(\x. -inv (2 * sig pow 2) * (\x. ((x - mu) pow 2)) x)
                       continuous_on univ(:real)` THENL
  [SIMP_TAC real_ss [REAL_MUL_COMM], ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN
  ONCE_REWRITE_TAC [METIS [] ``(x - mu) = (\x:real. x - mu) x``] THEN
  MATCH_MP_TAC CONTINUOUS_ON_POW THEN SIMP_TAC std_ss [] THEN
  Q_TAC SUFF_TAC `(\x. (\x. x) x - (\x. mu) x) continuous_on univ(:real)` THENL
  [SIMP_TAC std_ss [], ALL_TAC] THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
  SIMP_TAC std_ss [CONTINUOUS_ON_ID, CONTINUOUS_ON_CONST]);

val _ = hide "normal_pmeasure";

val normal_pmeasure = new_definition("normal_pmeasure",
  ``normal_pmeasure mu sig =
     (\A. if A IN measurable_sets lborel then
          pos_fn_integral lborel
            (\x. (\x. Normal (normal_density mu sig x)) x *
               indicator_fn A x) else 0)``);

val _ = hide "normal_rv";

val normal_rv = new_definition("normal_rv",``normal_rv X p mu sig =
   (random_variable X p borel /\
   (measurable_distr p X = normal_pmeasure mu sig))``);

val normal_measure_abs_continuous = store_thm ("normal_measure_abs_continuous",
  ``!mu sig. measure_absolutely_continuous
     (space borel,subsets borel,normal_pmeasure mu sig) lborel``,
  RW_TAC std_ss [] THEN
  SIMP_TAC std_ss [measure_absolutely_continuous_def] THEN
  RW_TAC std_ss [measurable_sets_def, measure_def] THEN
  ONCE_REWRITE_TAC [normal_pmeasure] THEN
  Q.ABBREV_TAC `f = (\x. Normal (normal_density mu sig x))` THEN
  Q_TAC SUFF_TAC `A IN measurable_sets lborel /\
   (measure (m_space lborel, measurable_sets lborel,
    (\A. if A IN measurable_sets lborel then
          pos_fn_integral lborel (\x. f x * indicator_fn A x)
         else 0)) A = 0)` THENL
  [SIMP_TAC std_ss [measure_def], ALL_TAC] THEN
  Q_TAC SUFF_TAC `measure_space lborel /\ (!x. 0 <= f x) /\
    f IN measurable (m_space lborel,measurable_sets lborel) Borel` THENL
  [DISCH_THEN (MP_TAC o MATCH_MP null_sets_density_iff) THEN
   DISCH_THEN (MP_TAC o Q.SPEC `A`) THEN DISC_RW_KILL THEN
   ASM_SIMP_TAC std_ss [lborel, measurable_sets_def] THEN
   SIMP_TAC std_ss [AE, ae_filter, GSPECIFICATION] THEN
   SIMP_TAC std_ss [m_space_def, IN_UNIV] THEN Q.EXISTS_TAC `A` THEN
   SIMP_TAC std_ss [SUBSET_DEF, GSPECIFICATION, null_sets] THEN
   ASM_SIMP_TAC std_ss [GSYM lborel] THEN
   ASM_SIMP_TAC std_ss [lborel, measurable_sets_def],
   ALL_TAC] THEN
  `(!x. 0 <= f x)` by METIS_TAC [normal_density_nonneg, extreal_of_num_def, extreal_le_def] THEN
  ASM_SIMP_TAC std_ss [measure_space_lborel] THEN Q.UNABBREV_TAC `f` THEN
  SIMP_TAC std_ss [IN_MEASURABLE_BOREL_normal_density]);

val normal_measure_space = store_thm ("normal_measure_space",
  ``!mu sig. measure_space (space borel,subsets borel,normal_pmeasure mu sig)``,
  RW_TAC std_ss [] THEN
  SIMP_TAC std_ss [measure_space_def, m_space_def, measurable_sets_def] THEN
  SIMP_TAC std_ss [SPACE, sigma_algebra_borel] THEN
  CONJ_TAC THENL
  [SIMP_TAC std_ss [positive_def, measure_def, measurable_sets_def] THEN
   CONJ_TAC THENL
   [SIMP_TAC std_ss [normal_pmeasure] THEN ASSUME_TAC measure_space_lborel THEN
    POP_ASSUM MP_TAC THEN SIMP_TAC std_ss [measure_space_def, sigma_algebra_iff2] THEN
    REPEAT STRIP_TAC THEN SIMP_TAC std_ss [indicator_fn_def, NOT_IN_EMPTY, mul_rzero] THEN
    SIMP_TAC std_ss [measure_space_lborel, pos_fn_integral_zero], ALL_TAC] THEN
   RW_TAC std_ss [normal_pmeasure, le_refl] THEN
   MATCH_MP_TAC pos_fn_integral_pos THEN SIMP_TAC std_ss [measure_space_lborel] THEN
   GEN_TAC THEN SIMP_TAC std_ss [indicator_fn_def] THEN COND_CASES_TAC THEN
   SIMP_TAC std_ss [mul_rzero, mul_rone, le_refl] THEN
   SIMP_TAC std_ss [extreal_of_num_def, extreal_le_def, normal_density_nonneg],
   ALL_TAC] THEN

  RW_TAC std_ss [countably_additive_def, measurable_sets_def, measure_def, o_DEF] THEN
  SIMP_TAC std_ss [normal_pmeasure] THEN
  `BIGUNION (IMAGE f univ(:num)) IN measurable_sets lborel` by
   METIS_TAC [lborel, measurable_sets_def] THEN ASM_SIMP_TAC std_ss [] THEN
  Q_TAC SUFF_TAC `!x. f x IN measurable_sets lborel` THENL
  [ALL_TAC,
   GEN_TAC THEN FULL_SIMP_TAC std_ss [IN_FUNSET, IN_UNIV] THEN
   ASM_SIMP_TAC std_ss [measurable_sets_def, lborel]] THEN
  DISCH_TAC THEN ASM_SIMP_TAC std_ss [] THEN
  Q.ABBREV_TAC `g = (\x. (\x'. Normal (normal_density mu sig x') * indicator_fn (f x) x'))` THEN
  Q_TAC SUFF_TAC `suminf (\x. pos_fn_integral lborel
       (\x'. Normal (normal_density mu sig x') * indicator_fn (f x) x')) =
                  suminf (\x. pos_fn_integral lborel (g x))` THENL
  [DISC_RW_KILL, Q.UNABBREV_TAC `g` THEN SIMP_TAC std_ss []] THEN
  Q_TAC SUFF_TAC `suminf (\x. pos_fn_integral lborel (g x)) =
                  pos_fn_integral lborel (\z. suminf (\x. g x z))` THENL
  [ALL_TAC,
   MATCH_MP_TAC (GSYM pos_fn_integral_suminf) THEN
   SIMP_TAC std_ss [measure_space_lborel] THEN Q.UNABBREV_TAC `g` THEN
   SIMP_TAC std_ss [] THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC le_mul THEN
    SIMP_TAC std_ss [extreal_of_num_def, extreal_le_def, normal_density_nonneg] THEN
    SIMP_TAC std_ss [GSYM extreal_of_num_def, indicator_fn_def] THEN
    COND_CASES_TAC THEN SIMP_TAC real_ss [extreal_of_num_def, extreal_le_def],
    ALL_TAC] THEN
   GEN_TAC THEN ONCE_REWRITE_TAC [METIS [] ``Normal (normal_density mu sig x') =
                 (\x'. Normal (normal_density mu sig x')) x'``] THEN
   MATCH_MP_TAC IN_MEASURABLE_BOREL_MUL_INDICATOR THEN
   ASM_SIMP_TAC std_ss [subsets_def, IN_MEASURABLE_BOREL_normal_density] THEN
   SIMP_TAC std_ss [lborel, m_space_def, measurable_sets_def, GSYM space_borel] THEN
   SIMP_TAC std_ss [SPACE, sigma_algebra_borel]] THEN
  DISC_RW_KILL THEN Q.UNABBREV_TAC `g` THEN SIMP_TAC std_ss [] THEN
  AP_TERM_TAC THEN ABS_TAC THEN Q.ABBREV_TAC `c = Normal (normal_density mu sig x)` THEN
  ONCE_REWRITE_TAC [METIS [] ``indicator_fn (f x') x = (\x'. indicator_fn (f x') x) x'``] THEN
  Q.ABBREV_TAC `g = (\x'. indicator_fn (f x') x)` THEN
  Q_TAC SUFF_TAC `suminf (\x'. c * g x') = c * suminf g` THENL
  [ALL_TAC,
   MATCH_MP_TAC ext_suminf_cmul THEN Q.UNABBREV_TAC `c` THEN Q.UNABBREV_TAC `g` THEN
   SIMP_TAC std_ss [extreal_of_num_def, extreal_le_def, normal_density_nonneg] THEN
   GEN_TAC THEN SIMP_TAC std_ss [GSYM extreal_of_num_def, indicator_fn_def] THEN
   COND_CASES_TAC THEN SIMP_TAC real_ss [extreal_of_num_def, extreal_le_def]] THEN
  DISC_RW_KILL THEN AP_TERM_TAC THEN Q.UNABBREV_TAC `g` THEN SIMP_TAC std_ss [] THEN
  GEN_REWR_TAC (LAND_CONV o ONCE_DEPTH_CONV) [indicator_fn_def] THEN
  SIMP_TAC std_ss [] THEN COND_CASES_TAC THENL
  [ALL_TAC,
   SIMP_TAC std_ss [indicator_fn_def] THEN
   Q_TAC SUFF_TAC `!x'. x NOTIN f x'` THENL
   [DISCH_TAC THEN ASM_SIMP_TAC std_ss [suminf_0], ALL_TAC] THEN
   ASM_SET_TAC []] THEN
  FULL_SIMP_TAC std_ss [IN_BIGUNION, IN_IMAGE, ext_suminf_def] THEN
  ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN SIMP_TAC std_ss [sup_eq] THEN
  CONJ_TAC THENL
  [GEN_TAC THEN GEN_REWR_TAC LAND_CONV [GSYM SPECIFICATION] THEN
   SIMP_TAC std_ss [GSPECIFICATION, IN_IMAGE] THEN STRIP_TAC THEN
   ASM_REWRITE_TAC [] THEN ASM_CASES_TAC ``x' < n:num`` THENL
   [ALL_TAC,
    MATCH_MP_TAC le_trans THEN Q.EXISTS_TAC `0` THEN
    SIMP_TAC real_ss [extreal_of_num_def, extreal_le_def] THEN
    SIMP_TAC std_ss [GSYM extreal_of_num_def, le_lt] THEN
    DISJ2_TAC THEN MATCH_MP_TAC EXTREAL_SUM_IMAGE_0 THEN
    SIMP_TAC std_ss [FINITE_COUNT] THEN RW_TAC std_ss [count_def, GSPECIFICATION] THEN
    `x'' <> x'` by ASM_SIMP_TAC arith_ss [] THEN SIMP_TAC std_ss [indicator_fn_def] THEN
    `x NOTIN f x''` by ASM_SET_TAC [] THEN ASM_SIMP_TAC std_ss []] THEN
   SIMP_TAC std_ss [count_def] THEN
   Q_TAC SUFF_TAC `{m | m < n} = ({m | m < n} DIFF {x'}) UNION {x'}` THENL
   [DISC_RW_KILL,
    SIMP_TAC std_ss [EXTENSION, GSPECIFICATION, IN_DIFF, IN_UNION, IN_SING] THEN
    ASM_SIMP_TAC real_ss []] THEN
   Q_TAC SUFF_TAC `FINITE ({m | m < n} DIFF {x'}) /\ FINITE {x'} /\
           DISJOINT ({m | m < n} DIFF {x'}) {x'}` THENL
   [ALL_TAC, SIMP_TAC std_ss [GSYM count_def] THEN
    SIMP_TAC std_ss [FINITE_SING, FINITE_COUNT, DISJOINT_DEF, FINITE_DIFF] THEN
    SET_TAC []] THEN
   DISCH_THEN (ASSUME_TAC o MATCH_MP EXTREAL_SUM_IMAGE_DISJOINT_UNION) THEN
   Q_TAC SUFF_TAC `SIGMA (\x'. indicator_fn (f x') x) (({m | m < n} DIFF {x'}) UNION {x'}) =
                   SIGMA (\x'. indicator_fn (f x') x) ({m | m < n} DIFF {x'}) +
                   SIGMA (\x'. indicator_fn (f x') x) {x'}` THENL
   [DISC_RW_KILL,
    POP_ASSUM MATCH_MP_TAC THEN DISJ1_TAC THEN
    RW_TAC std_ss [indicator_fn_def, num_not_infty]] THEN
   ASM_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_SING, indicator_fn_def] THEN
   `x IN f x'` by METIS_TAC [] THEN ASM_SIMP_TAC std_ss [extreal_of_num_def] THEN
   ONCE_REWRITE_TAC [GSYM add_comm_normal] THEN
   SIMP_TAC std_ss [le_lt] THEN DISJ2_TAC THEN
   GEN_REWR_TAC RAND_CONV [GSYM add_rzero] THEN AP_TERM_TAC THEN
   MATCH_MP_TAC EXTREAL_SUM_IMAGE_0 THEN
   SIMP_TAC std_ss [FINITE_DIFF, FINITE_SING, FINITE_COUNT, GSYM count_def] THEN
   RW_TAC std_ss [count_def, GSYM extreal_of_num_def] THEN
   SIMP_TAC real_ss [extreal_11, extreal_of_num_def] THEN
   UNDISCH_TAC ``x IN (f:num->real->bool) x''`` THEN POP_ASSUM MP_TAC THEN
   SIMP_TAC arith_ss [IN_DIFF, IN_SING, GSPECIFICATION] THEN ASM_SET_TAC [],
   ALL_TAC] THEN
  GEN_TAC THEN DISCH_THEN MATCH_MP_TAC THEN ONCE_REWRITE_TAC [GSYM SPECIFICATION] THEN
  SIMP_TAC std_ss [GSPECIFICATION, IN_IMAGE] THEN Q.EXISTS_TAC `SUC x'` THEN
  SIMP_TAC std_ss [IN_UNIV, COUNT_SUC] THEN REWRITE_TAC [count_def] THEN
  ONCE_REWRITE_TAC [SET_RULE ``a INSERT b = {a} UNION b``] THEN
  Q_TAC SUFF_TAC `FINITE {x'} /\ FINITE {m | m < x'} /\ DISJOINT {x'} {m | m < x'}` THENL
  [ALL_TAC, SIMP_TAC std_ss [GSYM count_def] THEN
   SIMP_TAC std_ss [FINITE_SING, FINITE_COUNT, DISJOINT_DEF, FINITE_DIFF] THEN
   ASM_SIMP_TAC arith_ss [count_def, EXTENSION, NOT_IN_EMPTY, IN_INTER,
    GSPECIFICATION, IN_SING]] THEN
  DISCH_THEN (ASSUME_TAC o MATCH_MP EXTREAL_SUM_IMAGE_DISJOINT_UNION) THEN
  Q_TAC SUFF_TAC `SIGMA (\x'. indicator_fn (f x') x) ({x'} UNION {m | m < x'}) =
                  SIGMA (\x'. indicator_fn (f x') x) {x'} +
                  SIGMA (\x'. indicator_fn (f x') x) {m | m < x'}` THENL
  [DISC_RW_KILL,
   POP_ASSUM MATCH_MP_TAC THEN DISJ1_TAC THEN
   RW_TAC std_ss [indicator_fn_def, num_not_infty]] THEN
  `x IN f x'` by METIS_TAC [] THEN
  ASM_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_SING, indicator_fn_def] THEN
  GEN_REWR_TAC LAND_CONV [GSYM add_rzero] THEN AP_TERM_TAC THEN
  ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN MATCH_MP_TAC EXTREAL_SUM_IMAGE_0 THEN
  SIMP_TAC std_ss [FINITE_COUNT, GSYM count_def] THEN
  RW_TAC std_ss [count_def, GSPECIFICATION] THEN
  `x'' <> x'` by ASM_SIMP_TAC arith_ss [] THEN ASM_SET_TAC []);

val normal_pdf_nonneg = store_thm ("normal_pdf_nonneg",
 ``!X p mu sig. normal_rv X p mu sig ==>
            !x. 0 <= PDF p (X:'a->real) x``,
  RW_TAC std_ss [normal_rv] THEN MATCH_MP_TAC PDF_LE_POS THEN
  FULL_SIMP_TAC std_ss [random_variable_def, prob_space_def] THEN
  METIS_TAC [normal_measure_abs_continuous, normal_measure_space]);

val normal_pdf_integral_eq_1 = store_thm ("normal_pdf_integral_eq_1",
 ``!X p mu sig. normal_rv X p mu sig ==> (integral lborel (PDF p X) = 1)``,
  RW_TAC std_ss [normal_rv] THEN MATCH_MP_TAC INTEGRAL_PDF_1 THEN
  RW_TAC std_ss [prob_space_def, normal_measure_space, m_space_def,
                 normal_measure_abs_continuous, measure_def, p_space_def] THEN
  POP_ASSUM (ASSUME_TAC o ONCE_REWRITE_RULE [EQ_SYM_EQ]) THEN
  FULL_SIMP_TAC std_ss [random_variable_def, distribution_def,
                        measurable_distr, prob_space_def] THEN
  `space borel IN subsets borel` by
   METIS_TAC [ALGEBRA_SPACE, sigma_algebra_borel, sigma_algebra_def] THEN
  ASM_SIMP_TAC std_ss [] THEN
  Q_TAC SUFF_TAC `PREIMAGE X (space borel) INTER p_space p = p_space p` THENL
  [METIS_TAC [prob_def], ALL_TAC] THEN
  FULL_SIMP_TAC std_ss [PREIMAGE_def] THEN
  FULL_SIMP_TAC std_ss [IN_MEASURABLE, space_def, IN_FUNSET] THEN
  ASM_SET_TAC []);

val integral_normal_pdf_eq_density = store_thm ("integral_normal_pdf_eq_density",
  ``!X p mu sig A. normal_rv X p mu sig /\ A IN measurable_sets lborel ==>
       (pos_fn_integral lborel (\x. PDF p X x * indicator_fn A x) =
        pos_fn_integral lborel
         (\x. Normal (normal_density mu sig x) * indicator_fn A x))``,
  RW_TAC std_ss [normal_rv, PDF_def, RN_deriv] THEN
  SELECT_ELIM_TAC THEN RW_TAC std_ss [measure_def, normal_pmeasure] THEN
  Q.EXISTS_TAC `(\x. Normal (normal_density mu sig x))` THEN
  SIMP_TAC real_ss [extreal_of_num_def, extreal_le_def, normal_density_nonneg] THEN
  SIMP_TAC std_ss [IN_MEASURABLE_BOREL_normal_density]);

val integral_normal_pdf_eq_density' = store_thm ("integral_normal_pdf_eq_density'",
  ``!X p mu sig f. normal_rv X p mu sig /\ (!x. 0 <= f x) /\
       f IN measurable (m_space lborel, measurable_sets lborel) Borel ==>
       (pos_fn_integral lborel (\x. f x * PDF p X x) =
        pos_fn_integral lborel
         (\x. f x * Normal (normal_density mu sig x)))``,
  RW_TAC std_ss [normal_rv, PDF_def] THEN ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
  Q_TAC SUFF_TAC `pos_fn_integral lborel (\x. f x *
     RN_deriv lborel (space borel,subsets borel,normal_pmeasure mu sig) x) =
   pos_fn_integral (density lborel
    (RN_deriv lborel (space borel,subsets borel,normal_pmeasure mu sig))) f` THENL
  [DISC_RW_KILL,
   `f = (\x. max 0 (f x))` by METIS_TAC [FUN_EQ_THM, extreal_max_def] THEN
   POP_ASSUM (fn th => GEN_REWR_TAC (RAND_CONV o ONCE_DEPTH_CONV) [th]) THEN
   ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
   Q.ABBREV_TAC `g = RN_deriv lborel (space borel,subsets borel,normal_pmeasure mu sig)` THEN
   Q_TAC SUFF_TAC `!x. f x * g x = max 0 (f x * g x)` THENL
   [DISC_RW_KILL,
    Q_TAC SUFF_TAC `!x. 0 <= f x * g x` THENL [METIS_TAC [extreal_max_def], ALL_TAC] THEN
    GEN_TAC THEN MATCH_MP_TAC le_mul THEN ASM_SIMP_TAC std_ss [] THEN
    METIS_TAC [PDF_def, normal_pdf_nonneg, normal_rv]] THEN
   ONCE_REWRITE_TAC [mul_comm] THEN
   MATCH_MP_TAC (REWRITE_RULE [GSYM density] pos_fn_integral_density') THEN
   Q.UNABBREV_TAC `g` THEN ASM_SIMP_TAC std_ss [measure_space_lborel] THEN
   CONJ_TAC THENL
   [Q.ABBREV_TAC `M = lborel` THEN
    Q.ABBREV_TAC `N = (space borel,subsets borel,normal_pmeasure mu sig)` THEN
    Q_TAC SUFF_TAC `sigma_finite_measure M /\ measure_space M /\ measure_space N /\
     measure_absolutely_continuous N M /\ (measurable_sets M = measurable_sets N)` THENL
    [DISCH_THEN (MP_TAC o MATCH_MP RADON_NIKODYM) THEN SIMP_TAC std_ss [RN_deriv] THEN
     METIS_TAC [], ALL_TAC] THEN
    CONJ_TAC THENL [METIS_TAC [sigma_finite_measure_lborel], ALL_TAC] THEN
    CONJ_TAC THENL [METIS_TAC [measure_space_lborel], ALL_TAC] THEN
    CONJ_TAC THENL [METIS_TAC [normal_measure_space], ALL_TAC] THEN
    CONJ_TAC THENL [METIS_TAC [normal_measure_abs_continuous], ALL_TAC] THEN
    METIS_TAC [lborel, measurable_sets_def], ALL_TAC] THEN
   SIMP_TAC std_ss [AE, ae_filter, GSPECIFICATION] THEN Q.EXISTS_TAC `{}` THEN
   SIMP_TAC std_ss [null_sets, GSPECIFICATION] THEN RW_TAC std_ss [] THENL
   [SIMP_TAC std_ss [lborel, measurable_sets_def] THEN
    METIS_TAC [borel_closed, CLOSED_EMPTY],
    METIS_TAC [measure_space_lborel, measure_space_def, positive_def],
    ALL_TAC] THEN
   Q_TAC SUFF_TAC `RN_deriv lborel (space borel,subsets borel,normal_pmeasure mu sig) =
    PDF p X` THENL [DISC_RW_KILL, ASM_SIMP_TAC std_ss [PDF_def]] THEN
   `normal_rv X p mu sig` by ASM_SIMP_TAC std_ss [normal_rv] THEN
   `!x. 0 <= PDF p X x` by METIS_TAC [normal_pdf_nonneg] THEN
   ASM_SIMP_TAC std_ss [GSPEC_F, SUBSET_EMPTY]] THEN
  Q.ABBREV_TAC `N = (space borel,subsets borel,normal_pmeasure mu sig)` THEN
  Q_TAC SUFF_TAC `pos_fn_integral lborel (\x. f x * Normal (normal_density mu sig x)) =
    pos_fn_integral N f` THENL
  [DISC_RW_KILL THEN MATCH_MP_TAC RN_deriv_positive_integral THEN
   ASM_SIMP_TAC std_ss [measure_space_lborel, sigma_finite_measure_lborel] THEN
   CONJ_TAC THENL [METIS_TAC [normal_measure_space], ALL_TAC] THEN
   CONJ_TAC THENL [METIS_TAC [normal_measure_abs_continuous], ALL_TAC] THEN
   METIS_TAC [lborel, measurable_sets_def], ALL_TAC] THEN
  ONCE_REWRITE_TAC [METIS [] ``Normal (normal_density mu sig x) =
                          (\x. Normal (normal_density mu sig x)) x``] THEN
  Q.ABBREV_TAC `g = (\x. Normal (normal_density mu sig x))` THEN
  ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN ONCE_REWRITE_TAC [mul_comm] THEN
  Q_TAC SUFF_TAC `N = density lborel g` THENL
  [DISC_RW_KILL,
   Q.UNABBREV_TAC `N` THEN ASM_SIMP_TAC std_ss [density] THEN
   CONJ_TAC THENL [METIS_TAC [m_space_def, lborel, space_borel], ALL_TAC] THEN
   CONJ_TAC THENL [METIS_TAC [measurable_sets_def, lborel], ALL_TAC] THEN
   SIMP_TAC std_ss [normal_pmeasure] THEN ABS_TAC THEN RW_TAC std_ss [] THEN
   `!x. 0 <= g x` by (Q.UNABBREV_TAC `g` THEN
     SIMP_TAC std_ss [extreal_of_num_def, extreal_le_def] THEN
     METIS_TAC [normal_density_nonneg]) THEN
   ASM_SIMP_TAC std_ss [extreal_max_def, le_mul, indicator_fn_pos_le]] THEN
  `!x. 0 <= g x` by (Q.UNABBREV_TAC `g` THEN
     SIMP_TAC std_ss [extreal_of_num_def, extreal_le_def] THEN
     METIS_TAC [normal_density_nonneg]) THEN
  Q_TAC SUFF_TAC `pos_fn_integral (density lborel g) (\x. max 0 (f x)) =
                  pos_fn_integral lborel (\x. max 0 (g x * f x))` THENL
  [ASM_SIMP_TAC std_ss [extreal_max_def, le_mul, ETA_AX], ALL_TAC] THEN
  MATCH_MP_TAC (REWRITE_RULE [GSYM density] pos_fn_integral_density') THEN
  ASM_SIMP_TAC std_ss [measure_space_lborel, GSPEC_T] THEN
  CONJ_TAC THENL [Q.UNABBREV_TAC `g` THEN
   SIMP_TAC std_ss [IN_MEASURABLE_BOREL_normal_density], ALL_TAC] THEN
  SIMP_TAC std_ss [AE, ae_filter, GSPECIFICATION] THEN Q.EXISTS_TAC `{}` THEN
  SIMP_TAC std_ss [null_sets, GSPECIFICATION] THEN RW_TAC std_ss [] THENL
  [SIMP_TAC std_ss [lborel, measurable_sets_def] THEN
   METIS_TAC [borel_closed, CLOSED_EMPTY],
   METIS_TAC [measure_space_lborel, measure_space_def, positive_def],
   ALL_TAC] THEN
  SIMP_TAC std_ss [IN_UNIV, GSPEC_F, SUBSET_EMPTY]);

val integral_normal_pdf_symmetry = store_thm ("integral_normal_pdf_symmetry",
  ``!X p mu sig A. normal_rv X p mu sig ==>
      (pos_fn_integral lborel (\x. PDF p X x * indicator_fn {x | x <= mu} x) =
       pos_fn_integral lborel (\x. PDF p X x * indicator_fn {x | mu <= x} x))``,
  RW_TAC std_ss [] THEN
  Q_TAC SUFF_TAC `{x | x <= mu} IN measurable_sets lborel /\
                  {x | mu <= x} IN measurable_sets lborel` THENL
  [ALL_TAC,
   Q_TAC SUFF_TAC `topology_hvg$Closed {x | x <= mu} /\
                   topology_hvg$Closed {x | mu <= x}` THENL
   [STRIP_TAC THEN SIMP_TAC std_ss [lborel, measurable_sets_def] THEN
    CONJ_TAC THEN MATCH_MP_TAC borel_closed THEN ASM_SIMP_TAC std_ss [],
    ALL_TAC] THEN
   SIMP_TAC std_ss [CLOSED_HALFSPACE_COMPONENT_LE] THEN
   ONCE_REWRITE_TAC [GSYM real_ge] THEN SIMP_TAC std_ss [CLOSED_HALFSPACE_COMPONENT_GE]] THEN
  STRIP_TAC THEN ASM_SIMP_TAC std_ss [integral_normal_pdf_eq_density] THEN
  `pos_fn_integral lborel (\x. PDF p X x * indicator_fn {x | x <= mu} x) =
   pos_fn_integral lborel
    (\x. Normal (normal_density mu sig x) * indicator_fn {x | x <= mu} x)`
    by METIS_TAC [integral_normal_pdf_eq_density] THEN
  `pos_fn_integral lborel (\x. PDF p X x * indicator_fn {x | mu <= x} x) =
   pos_fn_integral lborel
    (\x. Normal (normal_density mu sig x) * indicator_fn {x | mu <= x} x)`
    by METIS_TAC [integral_normal_pdf_eq_density] THEN
  ASM_REWRITE_TAC [] THEN POP_ASSUM K_TAC THEN POP_ASSUM K_TAC THEN
  Q.ABBREV_TAC `f = (\x.
     Normal (normal_density mu sig x) * indicator_fn {x | x <= mu} x)` THEN
  Q_TAC SUFF_TAC `pos_fn_integral lborel (\x. f x) =
   Normal (abs (-1)) * pos_fn_integral lborel (\x. f ((2 * mu) + (-1) * x))` THENL
  [ALL_TAC,
   Q_TAC SUFF_TAC `pos_fn_integral lborel (\x. max 0 (f x)) =
   Normal (abs (-1)) * pos_fn_integral lborel (\x. max 0 (f ((2 * mu) + (-1) * x)))` THENL
   [Q_TAC SUFF_TAC `!x. 0 <= f x` THENL
    [DISCH_TAC THEN ASM_SIMP_TAC std_ss [extreal_max_def], ALL_TAC] THEN
    Q.UNABBREV_TAC `f` THEN GEN_TAC THEN SIMP_TAC std_ss [] THEN
    MATCH_MP_TAC le_mul THEN SIMP_TAC std_ss [indicator_fn_pos_le] THEN
    SIMP_TAC std_ss [normal_density_nonneg, extreal_of_num_def, extreal_le_def],
    ALL_TAC] THEN
   MATCH_MP_TAC lebesgue_pos_integral_real_affine THEN
   SIMP_TAC real_ss [] THEN Q.UNABBREV_TAC `f` THEN
   ONCE_REWRITE_TAC [METIS [] ``Normal (normal_density mu sig x) =
                           (\x. Normal (normal_density mu sig x)) x``] THEN
   MATCH_MP_TAC IN_MEASURABLE_BOREL_MUL_INDICATOR THEN
   FULL_SIMP_TAC std_ss [sigma_algebra_borel, lborel, measurable_sets_def] THEN
   `borel = (m_space lborel, measurable_sets lborel)` by
     METIS_TAC [lborel, m_space_def, measurable_sets_def, SPACE, space_borel] THEN
   ASM_SIMP_TAC std_ss [IN_MEASURABLE_BOREL_normal_density]] THEN
  SIMP_TAC std_ss [ETA_AX] THEN DISC_RW_KILL THEN
  SIMP_TAC real_ss [abs, GSYM extreal_of_num_def, mul_lone] THEN
  Q.UNABBREV_TAC `f` THEN SIMP_TAC std_ss [indicator_fn_def, GSYM real_sub] THEN
  SIMP_TAC real_ss [GSPECIFICATION, REAL_ARITH `` 2 * mu - x <= mu = mu <= x:real``] THEN
  AP_TERM_TAC THEN ABS_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  SIMP_TAC std_ss [extreal_11, normal_density] THEN
  ONCE_REWRITE_TAC [REAL_ARITH ``2 * mu = mu + mu:real``] THEN
  Q_TAC SUFF_TAC `(mu + mu - x - mu) pow 2 = (x - mu) pow 2` THENL
  [METIS_TAC [], ALL_TAC] THEN SIMP_TAC std_ss [POW_2] THEN REAL_ARITH_TAC);

val integral_normal_pdf_symmetry' = store_thm ("integral_normal_pdf_symmetry'",
  ``!X p mu sig A a. normal_rv X p mu sig ==>
      (pos_fn_integral lborel (\x. PDF p X x * indicator_fn {x | (mu - a) <= x /\ x <= mu} x) =
       pos_fn_integral lborel (\x. PDF p X x * indicator_fn {x | mu <= x /\ x <= (mu + a)} x))``,
  RW_TAC std_ss [] THEN
  Q_TAC SUFF_TAC `{x | (mu - a) <= x /\ x <= mu} IN measurable_sets lborel /\
                  {x | mu <= x /\ x <= (mu + a)} IN measurable_sets lborel` THENL
  [STRIP_TAC,
   SIMP_TAC std_ss [GSYM interval, lborel, measurable_sets_def] THEN CONJ_TAC THEN
   (MATCH_MP_TAC borel_closed THEN SIMP_TAC std_ss [CLOSED_INTERVAL])] THEN
  `pos_fn_integral lborel (\x. PDF p X x * indicator_fn {x | (mu - a) <= x /\ x <= mu} x) =
   pos_fn_integral lborel
    (\x. Normal (normal_density mu sig x) * indicator_fn {x | (mu - a) <= x /\ x <= mu} x)`
    by METIS_TAC [integral_normal_pdf_eq_density] THEN
  `pos_fn_integral lborel (\x. PDF p X x * indicator_fn {x | mu <= x /\ x <= (mu + a)} x) =
   pos_fn_integral lborel
    (\x. Normal (normal_density mu sig x) * indicator_fn {x | mu <= x /\ x <= (mu + a)} x)`
    by METIS_TAC [integral_normal_pdf_eq_density] THEN
  ASM_REWRITE_TAC [] THEN POP_ASSUM K_TAC THEN POP_ASSUM K_TAC THEN
  Q.ABBREV_TAC `f = (\x.
     Normal (normal_density mu sig x) * indicator_fn {x | (mu - a) <= x /\ x <= mu} x)` THEN
  Q_TAC SUFF_TAC `pos_fn_integral lborel (\x. f x) =
   Normal (abs (-1)) * pos_fn_integral lborel (\x. f ((2 * mu) + (-1) * x))` THENL
  [ALL_TAC,
   Q_TAC SUFF_TAC `pos_fn_integral lborel (\x. max 0 (f x)) =
   Normal (abs (-1)) * pos_fn_integral lborel (\x. max 0 (f ((2 * mu) + (-1) * x)))` THENL
   [Q_TAC SUFF_TAC `!x. 0 <= f x` THENL
    [DISCH_TAC THEN ASM_SIMP_TAC std_ss [extreal_max_def], ALL_TAC] THEN
    Q.UNABBREV_TAC `f` THEN GEN_TAC THEN SIMP_TAC std_ss [] THEN
    MATCH_MP_TAC le_mul THEN SIMP_TAC std_ss [indicator_fn_pos_le] THEN
    SIMP_TAC std_ss [normal_density_nonneg, extreal_of_num_def, extreal_le_def],
    ALL_TAC] THEN
   MATCH_MP_TAC lebesgue_pos_integral_real_affine THEN
   SIMP_TAC real_ss [] THEN Q.UNABBREV_TAC `f` THEN
   ONCE_REWRITE_TAC [METIS [] ``Normal (normal_density mu sig x) =
                           (\x. Normal (normal_density mu sig x)) x``] THEN
   MATCH_MP_TAC IN_MEASURABLE_BOREL_MUL_INDICATOR THEN
   FULL_SIMP_TAC std_ss [sigma_algebra_borel, lborel, measurable_sets_def] THEN
   `borel = (m_space lborel, measurable_sets lborel)` by
     METIS_TAC [lborel, m_space_def, measurable_sets_def, SPACE, space_borel] THEN
   ASM_SIMP_TAC std_ss [IN_MEASURABLE_BOREL_normal_density]] THEN
  SIMP_TAC std_ss [ETA_AX] THEN DISC_RW_KILL THEN
  SIMP_TAC real_ss [abs, GSYM extreal_of_num_def, mul_lone] THEN
  Q.UNABBREV_TAC `f` THEN SIMP_TAC std_ss [indicator_fn_def, GSYM real_sub] THEN
  SIMP_TAC real_ss [GSPECIFICATION, REAL_ARITH `` 2 * mu - x <= mu = mu <= x:real``,
                    REAL_ARITH ``mu - a <= 2 * mu - x = x <= mu + a:real``] THEN
  GEN_REWR_TAC (LAND_CONV o ONCE_DEPTH_CONV) [CONJ_COMM] THEN
  AP_TERM_TAC THEN ABS_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  SIMP_TAC std_ss [extreal_11, normal_density] THEN
  ONCE_REWRITE_TAC [REAL_ARITH ``2 * mu = mu + mu:real``] THEN
  Q_TAC SUFF_TAC `(mu + mu - x - mu) pow 2 = (x - mu) pow 2` THENL
  [METIS_TAC [], ALL_TAC] THEN SIMP_TAC std_ss [POW_2] THEN REAL_ARITH_TAC);

val extreal_double = store_thm ("extreal_double",
  ``!a:extreal. a + a = 2 * a``,
  GEN_TAC THEN Cases_on `a` THEN
  SIMP_TAC real_ss [extreal_add_def, extreal_mul_def, extreal_of_num_def] THEN
  SIMP_TAC std_ss [extreal_11, REAL_DOUBLE]);

val eq_rdiv = store_thm ("eq_rdiv",
  ``!x y z. 0 < z ==> ((x = y / Normal z) <=> (x * Normal z = y))``,
  RW_TAC std_ss [GSYM le_antisym] THEN
  MATCH_MP_TAC (TAUT `(a = c) /\ (b = d) ==> (a /\ b = c /\ d)`) THEN
  METIS_TAC [le_rdiv, le_ldiv]);

val integral_normal_pdf_half1 = store_thm ("integral_normal_pdf_half1",
  ``!X p mu sig A. normal_rv X p mu sig /\ (A = {x | x <= mu}) ==>
      (pos_fn_integral lborel (\x. PDF p X x * indicator_fn A x) = 1 / 2)``,
  RW_TAC std_ss [] THEN
  Q_TAC SUFF_TAC `{x | x <= mu} IN measurable_sets lborel /\
                  {x | mu <= x} IN measurable_sets lborel` THENL
  [ALL_TAC,
   Q_TAC SUFF_TAC `topology_hvg$Closed {x | x <= mu} /\
                   topology_hvg$Closed {x | mu <= x}` THENL
   [STRIP_TAC THEN SIMP_TAC std_ss [lborel, measurable_sets_def] THEN
    CONJ_TAC THEN MATCH_MP_TAC borel_closed THEN ASM_SIMP_TAC std_ss [],
    ALL_TAC] THEN
   SIMP_TAC std_ss [CLOSED_HALFSPACE_COMPONENT_LE] THEN
   ONCE_REWRITE_TAC [GSYM real_ge] THEN SIMP_TAC std_ss [CLOSED_HALFSPACE_COMPONENT_GE]] THEN
  STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o MATCH_MP normal_pdf_integral_eq_1) THEN
  `UNIV IN measurable_sets lborel` by (SIMP_TAC std_ss [lborel, measurable_sets_def] THEN
    METIS_TAC [space_in_borel]) THEN
  `pos_fn_integral lborel (\x. PDF p X x * indicator_fn UNIV x) =
   pos_fn_integral lborel
    (\x. Normal (normal_density mu sig x) * indicator_fn UNIV x)`
    by METIS_TAC [integral_normal_pdf_eq_density] THEN
  Q_TAC SUFF_TAC `UNIV = {x | x <= mu} UNION {x | mu < x}` THENL
  [DISCH_TAC,
   SIMP_TAC real_ss [EXTENSION, IN_UNIV, IN_UNION, GSPECIFICATION] THEN
   REAL_ARITH_TAC] THEN
  `pos_fn_integral lborel (PDF p X) = 1`
    by METIS_TAC [integral_pos_fn, normal_pdf_nonneg, measure_space_lborel] THEN
  Q_TAC SUFF_TAC `pos_fn_integral lborel
   (\x. PDF p X x * indicator_fn univ(:real) x) = 1` THENL
  [DISCH_TAC,
   SIMP_TAC std_ss [indicator_fn_def, IN_UNIV, mul_rone] THEN
   METIS_TAC [ETA_AX]] THEN
  Q.ABBREV_TAC `f = (\x. Normal (normal_density mu sig x))` THEN
  `1 = pos_fn_integral lborel (\x. f x *
           indicator_fn ({x | x <= mu} UNION {x | mu < x}) x)` by
    (Q.UNABBREV_TAC `f` THEN METIS_TAC []) THEN
  Q_TAC SUFF_TAC
  `pos_fn_integral lborel (\x. f x *
           indicator_fn ({x | x <= mu} UNION {x | mu < x}) x) =
   pos_fn_integral lborel (\x. f x *
           indicator_fn ({x | x <= mu}) x) +
   pos_fn_integral lborel (\x. f x *
           indicator_fn ({x | mu < x}) x)` THENL
  [ALL_TAC,
   MATCH_MP_TAC pos_fn_integral_disjoint_sets THEN Q.UNABBREV_TAC `f` THEN
   ASM_SIMP_TAC std_ss [measure_space_lborel, IN_MEASURABLE_BOREL_normal_density] THEN
   SIMP_TAC std_ss [normal_density_nonneg, extreal_le_def, extreal_of_num_def] THEN
   CONJ_TAC THENL
   [SIMP_TAC std_ss [EXTENSION, DISJOINT_DEF, IN_INTER, NOT_IN_EMPTY] THEN
    SIMP_TAC real_ss [GSPECIFICATION] THEN REAL_ARITH_TAC,
    ALL_TAC] THEN
   SIMP_TAC std_ss [lborel, measurable_sets_def] THEN
   MATCH_MP_TAC borel_open THEN SIMP_TAC std_ss [OPEN_INTERVAL_RIGHT]] THEN
  Q_TAC SUFF_TAC `pos_fn_integral lborel (\x. f x * indicator_fn {x | mu < x} x) =
                 pos_fn_integral lborel (\x. f x * indicator_fn {x | mu <= x} x)` THENL
  [DISCH_THEN (fn th => GEN_REWR_TAC (LAND_CONV o ONCE_DEPTH_CONV) [th]) THEN
   Q.UNABBREV_TAC `f` THEN SIMP_TAC std_ss [] THEN
   FIRST_ASSUM (MP_TAC o MATCH_MP integral_normal_pdf_symmetry) THEN
   `pos_fn_integral lborel (\x. PDF p X x * indicator_fn {x | x <= mu} x) =
   pos_fn_integral lborel
    (\x. Normal (normal_density mu sig x) * indicator_fn {x | x <= mu} x)`
    by METIS_TAC [integral_normal_pdf_eq_density] THEN
   `pos_fn_integral lborel (\x. PDF p X x * indicator_fn {x | mu <= x} x) =
    pos_fn_integral lborel
     (\x. Normal (normal_density mu sig x) * indicator_fn {x | mu <= x} x)`
     by METIS_TAC [integral_normal_pdf_eq_density] THEN
   POP_ASSUM (fn th => REWRITE_TAC [th]) THEN
   POP_ASSUM (fn th => REWRITE_TAC [th]) THEN
   DISCH_THEN (fn th => REWRITE_TAC [th]) THEN
   SIMP_TAC std_ss [extreal_double] THEN DISCH_TAC THEN
   SIMP_TAC real_ss [eq_rdiv, extreal_of_num_def] THEN
   SIMP_TAC std_ss [GSYM extreal_of_num_def] THEN ONCE_REWRITE_TAC [mul_comm] THEN
   METIS_TAC [],
   ALL_TAC] THEN
  Q_TAC SUFF_TAC `{x | mu <= x} = {x | mu < x} UNION {mu}` THENL
  [DISC_RW_KILL,
   SIMP_TAC std_ss [EXTENSION, IN_UNION, GSPECIFICATION, IN_SING] THEN
   REAL_ARITH_TAC] THEN
  Q_TAC SUFF_TAC  `pos_fn_integral lborel
    (\x. f x * indicator_fn ({x | mu < x} UNION {mu}) x) =
   pos_fn_integral lborel (\x. f x * indicator_fn ({x | mu < x}) x) +
   pos_fn_integral lborel (\x. f x * indicator_fn ({mu}) x)` THENL
  [ALL_TAC,
   MATCH_MP_TAC pos_fn_integral_disjoint_sets THEN Q.UNABBREV_TAC `f` THEN
   ASM_SIMP_TAC std_ss [measure_space_lborel, IN_MEASURABLE_BOREL_normal_density] THEN
   SIMP_TAC std_ss [normal_density_nonneg, extreal_le_def, extreal_of_num_def] THEN
   CONJ_TAC THENL
   [SIMP_TAC std_ss [EXTENSION, DISJOINT_DEF, IN_INTER, NOT_IN_EMPTY, IN_SING] THEN
    SIMP_TAC real_ss [GSPECIFICATION] THEN REAL_ARITH_TAC,
    ALL_TAC] THEN
   SIMP_TAC std_ss [lborel, measurable_sets_def] THEN CONJ_TAC THENL
   [MATCH_MP_TAC borel_open THEN SIMP_TAC std_ss [OPEN_INTERVAL_RIGHT],
    ALL_TAC] THEN
   MATCH_MP_TAC borel_closed THEN SIMP_TAC std_ss [CLOSED_SING]] THEN
  DISC_RW_KILL THEN
  Q_TAC SUFF_TAC `pos_fn_integral lborel (\x. f x * indicator_fn {mu} x) = 0` THENL
  [METIS_TAC [add_rzero], ALL_TAC] THEN
  Q_TAC SUFF_TAC `(\x. f x * indicator_fn {mu} x) = (\x. f mu * indicator_fn {mu} x)` THENL
  [DISC_RW_KILL,
   ABS_TAC THEN SIMP_TAC std_ss [indicator_fn_def, IN_SING] THEN
   COND_CASES_TAC THEN ASM_SIMP_TAC std_ss [mul_rone, mul_rzero]] THEN
  Q.UNABBREV_TAC `f` THEN SIMP_TAC std_ss [] THEN
  Q_TAC SUFF_TAC `pos_fn_integral lborel
   (\x. Normal (normal_density mu sig mu) * indicator_fn {mu} x) =
    Normal (normal_density mu sig mu) * measure lborel {mu}` THENL
  [DISC_RW_KILL,
   MATCH_MP_TAC pos_fn_integral_cmul_indicator THEN
   SIMP_TAC std_ss [normal_density_nonneg, measure_space_lborel] THEN
   SIMP_TAC std_ss [lborel, measurable_sets_def] THEN MATCH_MP_TAC borel_closed THEN
   SIMP_TAC std_ss [CLOSED_SING]] THEN
  Q_TAC SUFF_TAC `measure lborel {mu} = 0` THENL
  [SIMP_TAC std_ss [mul_rzero], ALL_TAC] THEN
  SIMP_TAC std_ss [measure_def, lborel, measure_lebesgue, sup_eq] THEN
  CONJ_TAC THENL
  [GEN_TAC THEN GEN_REWR_TAC LAND_CONV [GSYM SPECIFICATION] THEN
   SIMP_TAC std_ss [GSPECIFICATION] THEN STRIP_TAC THEN
   ASM_REWRITE_TAC [extreal_le_def, extreal_of_num_def] THEN
   ASM_CASES_TAC ``mu NOTIN line n`` THENL
   [ONCE_REWRITE_TAC [GSYM integral_indicator_UNIV] THEN
    `{mu} INTER line n = {}` by ASM_SET_TAC [] THEN
    ASM_SIMP_TAC std_ss [indicator, NOT_IN_EMPTY] THEN
    SIMP_TAC real_ss [INTEGRAL_0],
    ALL_TAC] THEN
   ONCE_REWRITE_TAC [GSYM integral_indicator_UNIV] THEN
   `{mu} INTER line n = {mu}` by ASM_SET_TAC [] THEN
   POP_ASSUM (fn th => REWRITE_TAC [th]) THEN
   ONCE_REWRITE_TAC [SET_RULE ``{x} = {x} INTER {x}``] THEN
   SIMP_TAC std_ss [GSYM INTERVAL_SING] THEN
   ONCE_REWRITE_TAC [integral_indicator_UNIV] THEN
   SIMP_TAC real_ss [INTEGRAL_REFL],
   ALL_TAC] THEN
  GEN_TAC THEN DISCH_THEN MATCH_MP_TAC THEN
  ONCE_REWRITE_TAC [GSYM SPECIFICATION] THEN SIMP_TAC std_ss [GSPECIFICATION] THEN
  Q.EXISTS_TAC `n` THEN SIMP_TAC std_ss [IN_UNIV, extreal_of_num_def, extreal_11] THEN
  ASM_CASES_TAC ``mu NOTIN line n`` THENL
   [ONCE_REWRITE_TAC [GSYM integral_indicator_UNIV] THEN
    `{mu} INTER line n = {}` by ASM_SET_TAC [] THEN
    ASM_SIMP_TAC std_ss [indicator, NOT_IN_EMPTY] THEN
    SIMP_TAC real_ss [INTEGRAL_0],
    ALL_TAC] THEN
  ONCE_REWRITE_TAC [GSYM integral_indicator_UNIV] THEN
   `{mu} INTER line n = {mu}` by ASM_SET_TAC [] THEN
   POP_ASSUM (fn th => REWRITE_TAC [th]) THEN
   ONCE_REWRITE_TAC [SET_RULE ``{x} = {x} INTER {x}``] THEN
   SIMP_TAC std_ss [GSYM INTERVAL_SING] THEN
   ONCE_REWRITE_TAC [integral_indicator_UNIV] THEN
   SIMP_TAC real_ss [INTEGRAL_REFL]);

val integral_normal_pdf_split = store_thm ("integral_normal_pdf_split",
  ``!X p mu sig A. normal_rv X p mu sig ==>
      (pos_fn_integral lborel (\x. PDF p X x) =
       pos_fn_integral lborel (\x. PDF p X x * indicator_fn {x | x <= mu} x) +
       pos_fn_integral lborel (\x. PDF p X x * indicator_fn {x | mu <= x} x))``,
  RW_TAC std_ss [] THEN
  Q_TAC SUFF_TAC `{x | x <= mu} IN measurable_sets lborel /\
                  {x | mu <= x} IN measurable_sets lborel` THENL
  [ALL_TAC,
   Q_TAC SUFF_TAC `topology_hvg$Closed {x | x <= mu} /\
                   topology_hvg$Closed {x | mu <= x}` THENL
   [STRIP_TAC THEN SIMP_TAC std_ss [lborel, measurable_sets_def] THEN
    CONJ_TAC THEN MATCH_MP_TAC borel_closed THEN ASM_SIMP_TAC std_ss [],
    ALL_TAC] THEN
   SIMP_TAC std_ss [CLOSED_HALFSPACE_COMPONENT_LE] THEN
   ONCE_REWRITE_TAC [GSYM real_ge] THEN SIMP_TAC std_ss [CLOSED_HALFSPACE_COMPONENT_GE]] THEN
  STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o MATCH_MP normal_pdf_integral_eq_1) THEN
  `UNIV IN measurable_sets lborel` by (SIMP_TAC std_ss [lborel, measurable_sets_def] THEN
    METIS_TAC [space_in_borel]) THEN
  `pos_fn_integral lborel (\x. PDF p X x * indicator_fn UNIV x) =
   pos_fn_integral lborel
    (\x. Normal (normal_density mu sig x) * indicator_fn UNIV x)`
    by METIS_TAC [integral_normal_pdf_eq_density] THEN
  `pos_fn_integral lborel (\x. PDF p X x) =
   pos_fn_integral lborel (\x. PDF p X x * indicator_fn univ(:real) x)`
    by SIMP_TAC std_ss [indicator_fn_def, IN_UNIV, mul_rone] THEN
  `pos_fn_integral lborel (\x. PDF p X x * indicator_fn {x | x <= mu} x) =
   pos_fn_integral lborel
    (\x. Normal (normal_density mu sig x) * indicator_fn {x | x <= mu} x)`
    by METIS_TAC [integral_normal_pdf_eq_density] THEN
  `pos_fn_integral lborel (\x. PDF p X x * indicator_fn {x | mu <= x} x) =
   pos_fn_integral lborel
    (\x. Normal (normal_density mu sig x) * indicator_fn {x | mu <= x} x)`
    by METIS_TAC [integral_normal_pdf_eq_density] THEN
  FULL_SIMP_TAC std_ss [] THEN
  Q_TAC SUFF_TAC `UNIV = {x | x <= mu} UNION {x | mu < x}` THENL
  [DISCH_TAC,
   SIMP_TAC real_ss [EXTENSION, IN_UNIV, IN_UNION, GSPECIFICATION] THEN
   REAL_ARITH_TAC] THEN
  POP_ASSUM (fn th => REWRITE_TAC [th]) THEN
  Q_TAC SUFF_TAC `pos_fn_integral lborel
  (\x. Normal (normal_density mu sig x) * indicator_fn {x | mu <= x} x) =
                  pos_fn_integral lborel
  (\x. Normal (normal_density mu sig x) * indicator_fn {x | mu < x} x)` THENL
  [DISC_RW_KILL THEN
   ONCE_REWRITE_TAC [METIS [] ``Normal (normal_density mu sig x) =
                          (\x. Normal (normal_density mu sig x)) x``] THEN
   MATCH_MP_TAC pos_fn_integral_disjoint_sets THEN
   ASM_SIMP_TAC std_ss [measure_space_lborel, IN_MEASURABLE_BOREL_normal_density] THEN
   SIMP_TAC std_ss [normal_density_nonneg, extreal_le_def, extreal_of_num_def] THEN
   CONJ_TAC THENL
   [SIMP_TAC std_ss [EXTENSION, DISJOINT_DEF, IN_INTER, NOT_IN_EMPTY] THEN
    SIMP_TAC real_ss [GSPECIFICATION] THEN REAL_ARITH_TAC,
    ALL_TAC] THEN
   SIMP_TAC std_ss [lborel, measurable_sets_def] THEN
   MATCH_MP_TAC borel_open THEN SIMP_TAC std_ss [OPEN_INTERVAL_RIGHT],
   ALL_TAC] THEN
  Q_TAC SUFF_TAC `{x | mu <= x} = {x | mu < x} UNION {mu}` THENL
  [DISC_RW_KILL,
   SIMP_TAC std_ss [EXTENSION, IN_UNION, GSPECIFICATION, IN_SING] THEN
   REAL_ARITH_TAC] THEN
  Q_TAC SUFF_TAC  `pos_fn_integral lborel
    (\x. (\x. Normal (normal_density mu sig x)) x *
   indicator_fn ({x | mu < x} UNION {mu}) x) =
   pos_fn_integral lborel (\x. (\x. Normal (normal_density mu sig x)) x *
                                      indicator_fn ({x | mu < x}) x) +
   pos_fn_integral lborel (\x. (\x. Normal (normal_density mu sig x)) x *
                                              indicator_fn ({mu}) x)` THENL
  [ALL_TAC,
   MATCH_MP_TAC pos_fn_integral_disjoint_sets THEN
   ASM_SIMP_TAC std_ss [measure_space_lborel, IN_MEASURABLE_BOREL_normal_density] THEN
   SIMP_TAC std_ss [normal_density_nonneg, extreal_le_def, extreal_of_num_def] THEN
   CONJ_TAC THENL
   [SIMP_TAC std_ss [EXTENSION, DISJOINT_DEF, IN_INTER, NOT_IN_EMPTY, IN_SING] THEN
    SIMP_TAC real_ss [GSPECIFICATION] THEN REAL_ARITH_TAC,
    ALL_TAC] THEN
   SIMP_TAC std_ss [lborel, measurable_sets_def] THEN CONJ_TAC THENL
   [MATCH_MP_TAC borel_open THEN SIMP_TAC std_ss [OPEN_INTERVAL_RIGHT],
    ALL_TAC] THEN
   MATCH_MP_TAC borel_closed THEN SIMP_TAC std_ss [CLOSED_SING]] THEN
  SIMP_TAC std_ss [] THEN DISC_RW_KILL THEN
  Q_TAC SUFF_TAC `pos_fn_integral lborel
   (\x. Normal (normal_density mu sig x) * indicator_fn {mu} x) = 0` THENL
  [METIS_TAC [add_rzero], ALL_TAC] THEN
  Q_TAC SUFF_TAC `(\x. Normal (normal_density mu sig x) * indicator_fn {mu} x) =
                  (\x. Normal (normal_density mu sig mu) * indicator_fn {mu} x)` THENL
  [DISC_RW_KILL,
   ABS_TAC THEN SIMP_TAC std_ss [indicator_fn_def, IN_SING] THEN
   COND_CASES_TAC THEN ASM_SIMP_TAC std_ss [mul_rone, mul_rzero]] THEN
  Q_TAC SUFF_TAC `pos_fn_integral lborel
   (\x. Normal (normal_density mu sig mu) * indicator_fn {mu} x) =
    Normal (normal_density mu sig mu) * measure lborel {mu}` THENL
  [DISC_RW_KILL,
   MATCH_MP_TAC pos_fn_integral_cmul_indicator THEN
   SIMP_TAC std_ss [normal_density_nonneg, measure_space_lborel] THEN
   SIMP_TAC std_ss [lborel, measurable_sets_def] THEN MATCH_MP_TAC borel_closed THEN
   SIMP_TAC std_ss [CLOSED_SING]] THEN
  Q_TAC SUFF_TAC `measure lborel {mu} = 0` THENL
  [SIMP_TAC std_ss [mul_rzero], ALL_TAC] THEN
  SIMP_TAC std_ss [measure_def, lborel, measure_lebesgue, sup_eq] THEN
  CONJ_TAC THENL
  [GEN_TAC THEN GEN_REWR_TAC LAND_CONV [GSYM SPECIFICATION] THEN
   SIMP_TAC std_ss [GSPECIFICATION] THEN STRIP_TAC THEN
   ASM_REWRITE_TAC [extreal_le_def, extreal_of_num_def] THEN
   ASM_CASES_TAC ``mu NOTIN line n`` THENL
   [ONCE_REWRITE_TAC [GSYM integral_indicator_UNIV] THEN
    `{mu} INTER line n = {}` by ASM_SET_TAC [] THEN
    ASM_SIMP_TAC std_ss [indicator, NOT_IN_EMPTY] THEN
    SIMP_TAC real_ss [INTEGRAL_0],
    ALL_TAC] THEN
   ONCE_REWRITE_TAC [GSYM integral_indicator_UNIV] THEN
   `{mu} INTER line n = {mu}` by ASM_SET_TAC [] THEN
   POP_ASSUM (fn th => REWRITE_TAC [th]) THEN
   ONCE_REWRITE_TAC [SET_RULE ``{x} = {x} INTER {x}``] THEN
   SIMP_TAC std_ss [GSYM INTERVAL_SING] THEN
   ONCE_REWRITE_TAC [integral_indicator_UNIV] THEN
   SIMP_TAC real_ss [INTEGRAL_REFL],
   ALL_TAC] THEN
  GEN_TAC THEN DISCH_THEN MATCH_MP_TAC THEN
  ONCE_REWRITE_TAC [GSYM SPECIFICATION] THEN SIMP_TAC std_ss [GSPECIFICATION] THEN
  Q.EXISTS_TAC `n` THEN SIMP_TAC std_ss [IN_UNIV, extreal_of_num_def, extreal_11] THEN
  ASM_CASES_TAC ``mu NOTIN line n`` THENL
   [ONCE_REWRITE_TAC [GSYM integral_indicator_UNIV] THEN
    `{mu} INTER line n = {}` by ASM_SET_TAC [] THEN
    ASM_SIMP_TAC std_ss [indicator, NOT_IN_EMPTY] THEN
    SIMP_TAC real_ss [INTEGRAL_0],
    ALL_TAC] THEN
  ONCE_REWRITE_TAC [GSYM integral_indicator_UNIV] THEN
   `{mu} INTER line n = {mu}` by ASM_SET_TAC [] THEN
   POP_ASSUM (fn th => REWRITE_TAC [th]) THEN
   ONCE_REWRITE_TAC [SET_RULE ``{x} = {x} INTER {x}``] THEN
   SIMP_TAC std_ss [GSYM INTERVAL_SING] THEN
   ONCE_REWRITE_TAC [integral_indicator_UNIV] THEN
   SIMP_TAC real_ss [INTEGRAL_REFL]);

val integral_normal_pdf_half2 = store_thm ("integral_normal_pdf_half2",
  ``!X p mu sig A. normal_rv X p mu sig /\ (A = {x | mu <= x}) ==>
      (pos_fn_integral lborel (\x. PDF p X x * indicator_fn A x) = 1 / 2)``,
  RW_TAC std_ss [] THEN
  FIRST_ASSUM (ASSUME_TAC o MATCH_MP normal_pdf_integral_eq_1) THEN
  FIRST_ASSUM (MP_TAC o MATCH_MP integral_normal_pdf_split) THEN
  SIMP_TAC std_ss [METIS [ETA_AX] ``(\x. PDF p X x) = PDF p X``] THEN
  `pos_fn_integral lborel (\x. PDF p X x * indicator_fn {x | x <= mu} x) = 1 / 2`
   by METIS_TAC [integral_normal_pdf_half1] THEN
  `pos_fn_integral lborel (PDF p X) = 1`
    by METIS_TAC [integral_pos_fn, normal_pdf_nonneg, measure_space_lborel] THEN
  ASM_REWRITE_TAC [] THEN
  Q_TAC SUFF_TAC `1 = 1 / 2 + 1 / 2` THENL
  [DISCH_THEN (fn th => GEN_REWR_TAC (LAND_CONV o LAND_CONV) [th]) THEN
   `1 / 2 <> PosInf` by SIMP_TAC real_ss [lt_infty, extreal_of_num_def, extreal_div_eq] THEN
   `1 / 2 <> NegInf` by SIMP_TAC real_ss [lt_infty, extreal_of_num_def, extreal_div_eq] THEN
   METIS_TAC [EXTREAL_EQ_LADD],
   ALL_TAC] THEN
  SIMP_TAC real_ss [extreal_11, extreal_add_def, extreal_div_eq, extreal_of_num_def]);

val normal_rv_affine = store_thm ("normal_rv_affine",
  ``!X p mu sig Y b.
     normal_rv X p mu sig /\ (!x. Y x = X x + b) ==>
     normal_rv Y p (mu  + b) (sig)``,
  RW_TAC std_ss [normal_rv] THENL
  [FULL_SIMP_TAC std_ss [random_variable_def, IN_MEASURABLE] THEN
   SIMP_TAC std_ss [IN_FUNSET, space_borel, IN_UNIV] THEN
   FULL_SIMP_TAC std_ss [space_def, subsets_def] THEN
   RW_TAC std_ss [] THEN FULL_SIMP_TAC std_ss [PREIMAGE_def] THEN
   `{x | X x + b IN s} = {x | X x IN {x | x + b IN s}}`
    by SET_TAC [] THEN POP_ASSUM (fn th => REWRITE_TAC [th]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
   `{x | x + b IN s} = PREIMAGE (\x. x + b) s` by
    (SIMP_TAC std_ss [PREIMAGE_def] THEN SET_TAC []) THEN
   POP_ASSUM (fn th => REWRITE_TAC [th]) THEN
   Q_TAC SUFF_TAC `(\x. x + b) IN borel_measurable borel` THENL
   [RW_TAC std_ss [borel_measurable, IN_MEASURABLE] THEN
    FULL_SIMP_TAC std_ss [space_borel, INTER_UNIV],
    ALL_TAC] THEN
   MATCH_MP_TAC borel_measurable_continuous_on1 THEN
   ONCE_REWRITE_TAC [METIS [] ``(\x. x + b) =
              (\x:real. (\x. x) x + (\x. b) x)``] THEN MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
   SIMP_TAC std_ss [CONTINUOUS_ON_CONST, CONTINUOUS_ON_ID],
   ALL_TAC] THEN
  FULL_SIMP_TAC std_ss [measurable_distr, distribution_def, normal_pmeasure] THEN
  FULL_SIMP_TAC std_ss [FUN_EQ_THM] THEN GEN_TAC THEN
  `A IN subsets borel = A IN measurable_sets lborel`
   by METIS_TAC [lborel, measurable_sets_def] THEN
  POP_ASSUM MP_TAC THEN RW_TAC std_ss [] THEN
  Q_TAC SUFF_TAC `PREIMAGE Y A =
                  PREIMAGE X {x | x + b IN A}` THENL
  [DISC_RW_KILL,
   SIMP_TAC std_ss [PREIMAGE_def] THEN ASM_SET_TAC []] THEN
  ASM_REWRITE_TAC [] THEN
  Q_TAC SUFF_TAC `{x | x + b IN A} IN measurable_sets lborel` THENL
  [DISCH_TAC,
   FULL_SIMP_TAC std_ss [lborel, measurable_sets_def] THEN
   `{x | x + b IN A} = PREIMAGE (\x. x + b) A` by
    (SIMP_TAC std_ss [PREIMAGE_def] THEN SET_TAC []) THEN
   POP_ASSUM (fn th => REWRITE_TAC [th]) THEN
   Q_TAC SUFF_TAC `(\x. x + b) IN borel_measurable borel` THENL
   [RW_TAC std_ss [borel_measurable, IN_MEASURABLE] THEN
    FULL_SIMP_TAC std_ss [space_borel, INTER_UNIV],
    ALL_TAC] THEN
   MATCH_MP_TAC borel_measurable_continuous_on1 THEN
   ONCE_REWRITE_TAC [METIS [] ``(\x. x + b) =
              (\x:real. (\x. x) x + (\x. b) x)``] THEN MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
   SIMP_TAC std_ss [CONTINUOUS_ON_CONST, CONTINUOUS_ON_ID]] THEN
  ASM_SIMP_TAC std_ss [] THEN
  Q.ABBREV_TAC `f = (\x. Normal (normal_density mu sig x) *
                         indicator_fn {x | x + b IN A} x)` THEN
  ONCE_REWRITE_TAC [METIS [ETA_AX]
   ``pos_fn_integral lborel f = pos_fn_integral lborel (\x. f x)``] THEN
  Q_TAC SUFF_TAC `pos_fn_integral lborel
   (\x. (\x. Normal (normal_density (mu + b) sig x) * indicator_fn A x) x) =
   Normal (abs 1) * pos_fn_integral lborel (\x. f (-b + 1 * x))` THENL
  [SIMP_TAC std_ss [] THEN DISC_RW_KILL THEN
   Q_TAC SUFF_TAC `pos_fn_integral lborel (\x. max 0 (f x)) =
    Normal (abs 1) * pos_fn_integral lborel (\x. max 0 (f (-b + 1 * x)))` THENL
   [Q_TAC SUFF_TAC `!x. 0 <= f x` THENL
    [DISCH_TAC THEN ASM_SIMP_TAC std_ss [extreal_max_def] THEN
     Q.UNABBREV_TAC `f` THEN SIMP_TAC std_ss [] THEN
     DISCH_THEN (ASSUME_TAC o ONCE_REWRITE_RULE [EQ_SYM_EQ]) THEN
     `{x | x + b IN A} IN subsets borel` by METIS_TAC [lborel, measurable_sets_def] THEN
     FULL_SIMP_TAC std_ss [] THEN METIS_TAC [], ALL_TAC] THEN
    Q.UNABBREV_TAC `f` THEN SIMP_TAC std_ss [] THEN GEN_TAC THEN
    MATCH_MP_TAC le_mul THEN SIMP_TAC std_ss [indicator_fn_pos_le] THEN
    SIMP_TAC std_ss [normal_density_nonneg, extreal_of_num_def, extreal_le_def],
    ALL_TAC] THEN
   MATCH_MP_TAC lebesgue_pos_integral_real_affine THEN
   Q.UNABBREV_TAC `f` THEN SIMP_TAC real_ss [] THEN
   MATCH_MP_TAC IN_MEASURABLE_BOREL_MUL THEN
   Q.EXISTS_TAC `(\x. Normal (normal_density mu sig x))` THEN
   Q.EXISTS_TAC `indicator_fn {x | x + b IN A}` THEN
   SIMP_TAC std_ss [sigma_algebra_borel, extreal_not_infty] THEN CONJ_TAC THENL
   [Q_TAC SUFF_TAC `borel = (m_space lborel,measurable_sets lborel)` THENL
    [SIMP_TAC std_ss [IN_MEASURABLE_BOREL_normal_density], ALL_TAC] THEN
    SIMP_TAC std_ss [GSYM space_borel, lborel, m_space_def, measurable_sets_def, SPACE],
    ALL_TAC] THEN CONJ_TAC THENL
   [ALL_TAC,
    MATCH_MP_TAC IN_MEASURABLE_BOREL_INDICATOR THEN Q.EXISTS_TAC `{x | x + b IN A}` THEN
    METIS_TAC [lborel, measurable_sets_def, sigma_algebra_borel]] THEN
   RW_TAC std_ss [indicator_fn_def, extreal_of_num_def],
   ALL_TAC] THEN
  SIMP_TAC real_ss [ABS_1, GSYM extreal_of_num_def, mul_lone] THEN
  Q.UNABBREV_TAC `f` THEN SIMP_TAC real_ss [indicator_fn_def, GSPECIFICATION] THEN
  ONCE_REWRITE_TAC [REAL_ARITH ``-b + x + b = x:real``] THEN
  AP_TERM_TAC THEN ABS_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  SIMP_TAC std_ss [extreal_11, normal_density] THEN
  ONCE_REWRITE_TAC [REAL_ARITH ``-b + x - mu = x - (mu + b:real)``] THEN
  SIMP_TAC std_ss []);

val normal_rv_affine' = store_thm ("normal_rv_affine'",
  ``!X p mu sig Y a b. a <> 0 /\ 0 < sig /\
     normal_rv X p mu sig /\ (!x. Y x = b + a * X x) ==>
     normal_rv Y p (b + a * mu) (abs a * sig)``,
  RW_TAC std_ss [normal_rv] THENL
  [FULL_SIMP_TAC std_ss [random_variable_def, IN_MEASURABLE] THEN
   SIMP_TAC std_ss [IN_FUNSET, space_borel, IN_UNIV] THEN
   FULL_SIMP_TAC std_ss [space_def, subsets_def] THEN
   RW_TAC std_ss [] THEN FULL_SIMP_TAC std_ss [PREIMAGE_def] THEN
   `{x | b + a * X x IN s} = {x | X x IN {x | b + a * x IN s}}`
    by SET_TAC [] THEN POP_ASSUM (fn th => REWRITE_TAC [th]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
   `{x | b + a * x IN s} = PREIMAGE (\x. b + a * x) s` by
    (SIMP_TAC std_ss [PREIMAGE_def] THEN SET_TAC []) THEN
   POP_ASSUM (fn th => REWRITE_TAC [th]) THEN
   Q_TAC SUFF_TAC `(\x. b + a * x) IN borel_measurable borel` THENL
   [RW_TAC std_ss [borel_measurable, IN_MEASURABLE] THEN
    FULL_SIMP_TAC std_ss [space_borel, INTER_UNIV],
    ALL_TAC] THEN
   MATCH_MP_TAC borel_measurable_continuous_on1 THEN
   Q_TAC SUFF_TAC
   `(\x:real. (\x. b) x + (\x:real. a * x) x) continuous_on UNIV` THENL
   [SIMP_TAC std_ss [], ALL_TAC] THEN
   MATCH_MP_TAC CONTINUOUS_ON_ADD THEN SIMP_TAC std_ss [CONTINUOUS_ON_CONST] THEN
   Q_TAC SUFF_TAC
   `(\x:real. (\x. a) x * (\x. x) x) continuous_on UNIV` THENL
   [SIMP_TAC std_ss [], ALL_TAC] THEN MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
   SIMP_TAC std_ss [CONTINUOUS_ON_CONST, CONTINUOUS_ON_ID],
   ALL_TAC] THEN
  FULL_SIMP_TAC std_ss [measurable_distr, distribution_def, PREIMAGE_def] THEN
  FULL_SIMP_TAC std_ss [FUN_EQ_THM] THEN GEN_TAC THEN
  `{x | b + a * X x IN s} = {x | X x IN {x | b + a * x IN s}}`
    by SET_TAC [] THEN POP_ASSUM (fn th => REWRITE_TAC [th]) THEN
  FIRST_X_ASSUM (ASSUME_TAC o Q.SPEC `{x | b + a * x IN s:real->bool}`) THEN
  SIMP_TAC std_ss [normal_pmeasure] THEN
  `s IN subsets borel = s IN measurable_sets lborel`
   by METIS_TAC [lborel, measurable_sets_def] THEN
  POP_ASSUM MP_TAC THEN RW_TAC std_ss [] THEN
  Q_TAC SUFF_TAC `{x | b + a * x IN s} IN measurable_sets lborel` THENL
  [DISCH_TAC THEN ASM_SIMP_TAC std_ss [],
   FULL_SIMP_TAC std_ss [measurable_sets_def, lborel] THEN
   Q_TAC SUFF_TAC `(\x. b + a * x) IN borel_measurable borel` THENL
   [RW_TAC std_ss [borel_measurable, IN_MEASURABLE] THEN
    ONCE_REWRITE_TAC [SET_RULE ``{x | b + a * x IN s} =
      {x | (\x. b + a * x) x IN s:real->bool} INTER UNIV``] THEN
    REWRITE_TAC [GSYM PREIMAGE_def, GSYM space_borel] THEN
    METIS_TAC [], ALL_TAC] THEN
   MATCH_MP_TAC borel_measurable_continuous_on1 THEN
   Q_TAC SUFF_TAC
   `(\x:real. (\x. b) x + (\x:real. a * x) x) continuous_on UNIV` THENL
   [SIMP_TAC std_ss [], ALL_TAC] THEN
   MATCH_MP_TAC CONTINUOUS_ON_ADD THEN SIMP_TAC std_ss [CONTINUOUS_ON_CONST] THEN
   Q_TAC SUFF_TAC
   `(\x:real. (\x. a) x * (\x. x) x) continuous_on UNIV` THENL
   [SIMP_TAC std_ss [], ALL_TAC] THEN MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
   SIMP_TAC std_ss [CONTINUOUS_ON_CONST, CONTINUOUS_ON_ID]] THEN
  `{x | b + a * x IN s} IN subsets borel` by METIS_TAC [lborel, measurable_sets_def] THEN
  FULL_SIMP_TAC std_ss [normal_pmeasure] THEN
  Q_TAC SUFF_TAC `!x. Normal (normal_density mu sig x) *
                      indicator_fn {x | b + a * x IN s} x =
     Normal (abs a) * Normal (normal_density (b + a * mu) (abs a * sig) (b + a * x)) *
                      indicator_fn s (b + a * x)` THENL
  [DISC_RW_KILL THEN
   Q_TAC SUFF_TAC `pos_fn_integral lborel
    (\x. Normal (abs a) *
     (\x. Normal (normal_density (b + a * mu) (abs a * sig) (b + a * x)) *
          indicator_fn s (b + a * x)) x) =
   Normal (abs a) * pos_fn_integral lborel
    (\x. Normal (normal_density (b + a * mu) (abs a * sig) (b + a * x)) *
          indicator_fn s (b + a * x))` THENL
   [SIMP_TAC std_ss [mul_assoc] THEN DISC_RW_KILL,
    MATCH_MP_TAC pos_fn_integral_cmul THEN SIMP_TAC std_ss [measure_space_lborel] THEN
    RW_TAC std_ss [ABS_POS] THEN MATCH_MP_TAC le_mul THEN
    SIMP_TAC std_ss [indicator_fn_pos_le, extreal_of_num_def, extreal_le_def] THEN
    SIMP_TAC std_ss [normal_density_nonneg]] THEN
   ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
   Q_TAC SUFF_TAC `pos_fn_integral lborel
    (\x. max 0 ((\x. Normal (normal_density (b + a * mu) (abs a * sig) x) *
                     indicator_fn s x) x)) =
    Normal (abs a) *
                   pos_fn_integral lborel
   (\x. max 0 ((\x. Normal (normal_density (b + a * mu) (abs a * sig) x) *
                    indicator_fn s x) (b + a * x)))` THENL
   [SIMP_TAC std_ss [extreal_max_def] THEN
    ASM_SIMP_TAC std_ss [normal_density_nonneg, le_mul, indicator_fn_pos_le,
                         extreal_of_num_def, extreal_le_def],
    ALL_TAC] THEN
   MATCH_MP_TAC lebesgue_pos_integral_real_affine THEN ASM_SIMP_TAC std_ss [] THEN
   ONCE_REWRITE_TAC [METIS [lborel, m_space_def, measurable_sets_def,
    space_borel, SPACE] ``borel = (m_space lborel, measurable_sets lborel)``] THEN
   MATCH_MP_TAC IN_MEASURABLE_BOREL_TIMES THEN
   Q.EXISTS_TAC `(\x. Normal (normal_density (b + a * mu) (abs a * sig) x))` THEN
   Q.EXISTS_TAC `(\x. indicator_fn s x)` THEN SIMP_TAC std_ss [measure_space_lborel] THEN
   SIMP_TAC std_ss [IN_MEASURABLE_BOREL_normal_density] THEN
   MATCH_MP_TAC IN_MEASURABLE_BOREL_INDICATOR THEN Q.EXISTS_TAC `s` THEN
   ASSUME_TAC measure_space_lborel THEN
   FULL_SIMP_TAC std_ss [measure_space_def, subsets_def],
   ALL_TAC] THEN
  SIMP_TAC std_ss [indicator_fn_def, GSPECIFICATION] THEN GEN_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  SIMP_TAC std_ss [extreal_mul_def, extreal_11] THEN
  SIMP_TAC std_ss [normal_density] THEN
  ONCE_REWRITE_TAC [REAL_ARITH ``a * (b * c) = (a:real * b:real) * c:real``] THEN
  Q_TAC SUFF_TAC `1 / sqrt (2 * pi * sig pow 2) =
   abs a * (1 / sqrt (2 * pi * (abs a * sig) pow 2))` THENL
  [DISC_RW_KILL,
   SIMP_TAC real_ss [real_div, REAL_MUL_ASSOC, POW_2] THEN
   ONCE_REWRITE_TAC [REAL_ARITH ``2 * pi * abs a * sig * abs a * sig =
     (2:real * pi:real * sig * sig:real) * (abs a * abs a:real)``] THEN
   Q_TAC SUFF_TAC `0 < 2 * pi * sig * sig` THENL
   [DISCH_TAC, ASSUME_TAC PI_POS THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC real_ss [] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC real_ss [] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC real_ss []] THEN
   Q_TAC SUFF_TAC `0 < abs a * abs a` THENL
   [DISCH_TAC, MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC std_ss [GSYM ABS_NZ]] THEN
   `0 <= 2 * pi * sig * sig` by ASM_SIMP_TAC std_ss [REAL_LT_IMP_LE] THEN
   `0 <= abs a * abs a` by ASM_SIMP_TAC std_ss [REAL_LT_IMP_LE] THEN
   ASM_SIMP_TAC std_ss [SQRT_MUL] THEN
   `0 < sqrt (2:real * pi * sig * sig)` by METIS_TAC [SQRT_POS_LT] THEN
   `0 < sqrt (abs a * abs a)` by METIS_TAC [SQRT_POS_LT] THEN
   `sqrt (2:real * pi * sig * sig) <> 0` by METIS_TAC [REAL_LT_IMP_NE] THEN
   `sqrt (abs a * abs a) <> 0` by METIS_TAC [REAL_LT_IMP_NE] THEN
   ASM_SIMP_TAC std_ss [REAL_INV_MUL, GSYM POW_2] THEN
   SIMP_TAC std_ss [POW_2_SQRT, ABS_POS] THEN
   ONCE_REWRITE_TAC [REAL_ARITH ``a * (b * c) = b:real * (a:real * c:real)``] THEN
   `0 < abs a` by FULL_SIMP_TAC std_ss [ABS_NZ] THEN
   `abs a <> 0` by METIS_TAC [REAL_LT_IMP_NE] THEN
   FULL_SIMP_TAC std_ss [REAL_MUL_RINV, REAL_MUL_RID]] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  ONCE_REWRITE_TAC [REAL_ARITH ``b + a * x - (b + a * mu) =
                    a:real * (x:real - mu:real)``] THEN
  SIMP_TAC real_ss [POW_MUL, real_div, REAL_MUL_ASSOC] THEN
  ONCE_REWRITE_TAC [REAL_MUL_COMM] THEN SIMP_TAC std_ss [REAL_MUL_ASSOC] THEN
  AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  ONCE_REWRITE_TAC [REAL_ARITH ``a * b * c = (a:real * c:real) * b:real``] THEN
  Q_TAC SUFF_TAC `0 < 2 * (sig * sig)` THENL
  [DISCH_TAC,
   MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC real_ss [] THEN
   MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC real_ss [] THEN
   MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC real_ss []] THEN
  Q_TAC SUFF_TAC `0 < abs a * abs a` THENL
  [DISCH_TAC, MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC std_ss [GSYM ABS_NZ]] THEN
  `0 <= 2 * (sig * sig)` by ASM_SIMP_TAC std_ss [REAL_LT_IMP_LE] THEN
  `0 <= abs a * abs a` by ASM_SIMP_TAC std_ss [REAL_LT_IMP_LE] THEN
  `2:real * (sig * sig) <> 0` by METIS_TAC [REAL_LT_IMP_NE] THEN
  `(abs a * abs a) <> 0` by METIS_TAC [REAL_LT_IMP_NE] THEN
  FULL_SIMP_TAC std_ss [GSYM POW_2, REAL_INV_MUL] THEN
  ONCE_REWRITE_TAC [GSYM REAL_MUL_ASSOC] THEN
  ONCE_REWRITE_TAC [GSYM REAL_POW2_ABS] THEN
  ASM_SIMP_TAC real_ss [REAL_MUL_LINV, ABS_ABS]);

val normal_distribution_affine = store_thm ("normal_distribution_affine",
  ``!X p mu sig Y a b. a <> 0 /\ 0 < sig /\
     random_variable X p borel /\
     (!s. s IN subsets borel ==> (distribution p X s = normal_pmeasure mu sig s)) /\
     (!x. Y x = b + a * X x)  ==>
     random_variable Y p borel /\ (!s. s IN subsets borel ==>
      (distribution p Y s = normal_pmeasure (b + a * mu) (abs a * sig) s))``,
  RW_TAC std_ss [] THENL
  [FULL_SIMP_TAC std_ss [random_variable_def, IN_MEASURABLE] THEN
   SIMP_TAC std_ss [IN_FUNSET, space_borel, IN_UNIV] THEN
   FULL_SIMP_TAC std_ss [space_def, subsets_def] THEN
   RW_TAC std_ss [] THEN FULL_SIMP_TAC std_ss [PREIMAGE_def] THEN
   `{x | b + a * X x IN s} = {x | X x IN {x | b + a * x IN s}}`
    by SET_TAC [] THEN POP_ASSUM (fn th => REWRITE_TAC [th]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
   `{x | b + a * x IN s} = PREIMAGE (\x. b + a * x) s` by
    (SIMP_TAC std_ss [PREIMAGE_def] THEN SET_TAC []) THEN
   POP_ASSUM (fn th => REWRITE_TAC [th]) THEN
   Q_TAC SUFF_TAC `(\x. b + a * x) IN borel_measurable borel` THENL
   [RW_TAC std_ss [borel_measurable, IN_MEASURABLE] THEN
    FULL_SIMP_TAC std_ss [space_borel, INTER_UNIV],
    ALL_TAC] THEN
   MATCH_MP_TAC borel_measurable_continuous_on1 THEN
   Q_TAC SUFF_TAC
   `(\x:real. (\x. b) x + (\x:real. a * x) x) continuous_on UNIV` THENL
   [SIMP_TAC std_ss [], ALL_TAC] THEN
   MATCH_MP_TAC CONTINUOUS_ON_ADD THEN SIMP_TAC std_ss [CONTINUOUS_ON_CONST] THEN
   Q_TAC SUFF_TAC
   `(\x:real. (\x. a) x * (\x. x) x) continuous_on UNIV` THENL
   [SIMP_TAC std_ss [], ALL_TAC] THEN MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
   SIMP_TAC std_ss [CONTINUOUS_ON_CONST, CONTINUOUS_ON_ID],
   ALL_TAC] THEN
  FULL_SIMP_TAC std_ss [distribution_def, PREIMAGE_def] THEN
  `{x | b + a * X x IN s} = {x | X x IN {x | b + a * x IN s}}`
    by SET_TAC [] THEN POP_ASSUM (fn th => REWRITE_TAC [th]) THEN
  FIRST_X_ASSUM (MP_TAC o Q.SPEC `{x | b + a * x IN s:real->bool}`) THEN
  Q_TAC SUFF_TAC `{x | b + a * x IN s} IN measurable_sets lborel` THENL
  [DISCH_TAC THEN ASM_SIMP_TAC std_ss [],
   FULL_SIMP_TAC std_ss [measurable_sets_def, lborel] THEN
   Q_TAC SUFF_TAC `(\x. b + a * x) IN borel_measurable borel` THENL
   [RW_TAC std_ss [borel_measurable, IN_MEASURABLE] THEN
    ONCE_REWRITE_TAC [SET_RULE ``{x | b + a * x IN s} =
      {x | (\x. b + a * x) x IN s:real->bool} INTER UNIV``] THEN
    REWRITE_TAC [GSYM PREIMAGE_def, GSYM space_borel] THEN
    METIS_TAC [], ALL_TAC] THEN
   MATCH_MP_TAC borel_measurable_continuous_on1 THEN
   Q_TAC SUFF_TAC
   `(\x:real. (\x. b) x + (\x:real. a * x) x) continuous_on UNIV` THENL
   [SIMP_TAC std_ss [], ALL_TAC] THEN
   MATCH_MP_TAC CONTINUOUS_ON_ADD THEN SIMP_TAC std_ss [CONTINUOUS_ON_CONST] THEN
   Q_TAC SUFF_TAC
   `(\x:real. (\x. a) x * (\x. x) x) continuous_on UNIV` THENL
   [SIMP_TAC std_ss [], ALL_TAC] THEN MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
   SIMP_TAC std_ss [CONTINUOUS_ON_CONST, CONTINUOUS_ON_ID]] THEN
  `s IN measurable_sets lborel` by METIS_TAC [lborel, measurable_sets_def] THEN
  `{x | b + a * x IN s} IN subsets borel` by METIS_TAC [lborel, measurable_sets_def] THEN
  ASM_SIMP_TAC std_ss [normal_pmeasure] THEN RW_TAC std_ss [] THEN
  Q_TAC SUFF_TAC `!x. Normal (normal_density mu sig x) *
                      indicator_fn {x | b + a * x IN s} x =
     Normal (abs a) * Normal (normal_density (b + a * mu) (abs a * sig) (b + a * x)) *
                      indicator_fn s (b + a * x)` THENL
  [DISC_RW_KILL THEN
   Q_TAC SUFF_TAC `pos_fn_integral lborel
    (\x. Normal (abs a) *
     (\x. Normal (normal_density (b + a * mu) (abs a * sig) (b + a * x)) *
          indicator_fn s (b + a * x)) x) =
   Normal (abs a) * pos_fn_integral lborel
    (\x. Normal (normal_density (b + a * mu) (abs a * sig) (b + a * x)) *
          indicator_fn s (b + a * x))` THENL
   [SIMP_TAC std_ss [mul_assoc] THEN DISC_RW_KILL,
    MATCH_MP_TAC pos_fn_integral_cmul THEN SIMP_TAC std_ss [measure_space_lborel] THEN
    RW_TAC std_ss [ABS_POS] THEN MATCH_MP_TAC le_mul THEN
    SIMP_TAC std_ss [indicator_fn_pos_le, extreal_of_num_def, extreal_le_def] THEN
    SIMP_TAC std_ss [normal_density_nonneg]] THEN
   ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
   Q_TAC SUFF_TAC `pos_fn_integral lborel
    (\x. max 0 ((\x. Normal (normal_density (b + a * mu) (abs a * sig) x) *
                     indicator_fn s x) x)) =
    Normal (abs a) *
                   pos_fn_integral lborel
   (\x. max 0 ((\x. Normal (normal_density (b + a * mu) (abs a * sig) x) *
                    indicator_fn s x) (b + a * x)))` THENL
   [SIMP_TAC std_ss [extreal_max_def] THEN
    ASM_SIMP_TAC std_ss [normal_density_nonneg, le_mul, indicator_fn_pos_le,
                         extreal_of_num_def, extreal_le_def],
    ALL_TAC] THEN
   MATCH_MP_TAC lebesgue_pos_integral_real_affine THEN ASM_SIMP_TAC std_ss [] THEN
   ONCE_REWRITE_TAC [METIS [lborel, m_space_def, measurable_sets_def,
    space_borel, SPACE] ``borel = (m_space lborel, measurable_sets lborel)``] THEN
   MATCH_MP_TAC IN_MEASURABLE_BOREL_TIMES THEN
   Q.EXISTS_TAC `(\x. Normal (normal_density (b + a * mu) (abs a * sig) x))` THEN
   Q.EXISTS_TAC `(\x. indicator_fn s x)` THEN SIMP_TAC std_ss [measure_space_lborel] THEN
   SIMP_TAC std_ss [IN_MEASURABLE_BOREL_normal_density] THEN
   MATCH_MP_TAC IN_MEASURABLE_BOREL_INDICATOR THEN Q.EXISTS_TAC `s` THEN
   ASSUME_TAC measure_space_lborel THEN
   FULL_SIMP_TAC std_ss [measure_space_def, subsets_def],
   ALL_TAC] THEN
  SIMP_TAC std_ss [indicator_fn_def, GSPECIFICATION] THEN GEN_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  SIMP_TAC std_ss [extreal_mul_def, extreal_11] THEN
  SIMP_TAC std_ss [normal_density] THEN
  ONCE_REWRITE_TAC [REAL_ARITH ``a * (b * c) = (a:real * b:real) * c:real``] THEN
  Q_TAC SUFF_TAC `1 / sqrt (2 * pi * sig pow 2) =
   abs a * (1 / sqrt (2 * pi * (abs a * sig) pow 2))` THENL
  [DISC_RW_KILL,
   SIMP_TAC real_ss [real_div, REAL_MUL_ASSOC, POW_2] THEN
   ONCE_REWRITE_TAC [REAL_ARITH ``2 * pi * abs a * sig * abs a * sig =
     (2:real * pi:real * sig * sig:real) * (abs a * abs a:real)``] THEN
   Q_TAC SUFF_TAC `0 < 2 * pi * sig * sig` THENL
   [DISCH_TAC, ASSUME_TAC PI_POS THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC real_ss [] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC real_ss [] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC real_ss []] THEN
   Q_TAC SUFF_TAC `0 < abs a * abs a` THENL
   [DISCH_TAC, MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC std_ss [GSYM ABS_NZ]] THEN
   `0 <= 2 * pi * sig * sig` by ASM_SIMP_TAC std_ss [REAL_LT_IMP_LE] THEN
   `0 <= abs a * abs a` by ASM_SIMP_TAC std_ss [REAL_LT_IMP_LE] THEN
   ASM_SIMP_TAC std_ss [SQRT_MUL] THEN
   `0 < sqrt (2:real * pi * sig * sig)` by METIS_TAC [SQRT_POS_LT] THEN
   `0 < sqrt (abs a * abs a)` by METIS_TAC [SQRT_POS_LT] THEN
   `sqrt (2:real * pi * sig * sig) <> 0` by METIS_TAC [REAL_LT_IMP_NE] THEN
   `sqrt (abs a * abs a) <> 0` by METIS_TAC [REAL_LT_IMP_NE] THEN
   ASM_SIMP_TAC std_ss [REAL_INV_MUL, GSYM POW_2] THEN
   SIMP_TAC std_ss [POW_2_SQRT, ABS_POS] THEN
   ONCE_REWRITE_TAC [REAL_ARITH ``a * (b * c) = b:real * (a:real * c:real)``] THEN
   `0 < abs a` by FULL_SIMP_TAC std_ss [ABS_NZ] THEN
   `abs a <> 0` by METIS_TAC [REAL_LT_IMP_NE] THEN
   FULL_SIMP_TAC std_ss [REAL_MUL_RINV, REAL_MUL_RID]] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  ONCE_REWRITE_TAC [REAL_ARITH ``b + a * x - (b + a * mu) =
                    a:real * (x:real - mu:real)``] THEN
  SIMP_TAC real_ss [POW_MUL, real_div, REAL_MUL_ASSOC] THEN
  ONCE_REWRITE_TAC [REAL_MUL_COMM] THEN SIMP_TAC std_ss [REAL_MUL_ASSOC] THEN
  AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  ONCE_REWRITE_TAC [REAL_ARITH ``a * b * c = (a:real * c:real) * b:real``] THEN
  Q_TAC SUFF_TAC `0 < 2 * (sig * sig)` THENL
  [DISCH_TAC,
   MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC real_ss [] THEN
   MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC real_ss [] THEN
   MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC real_ss []] THEN
  Q_TAC SUFF_TAC `0 < abs a * abs a` THENL
  [DISCH_TAC, MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC std_ss [GSYM ABS_NZ]] THEN
  `0 <= 2 * (sig * sig)` by ASM_SIMP_TAC std_ss [REAL_LT_IMP_LE] THEN
  `0 <= abs a * abs a` by ASM_SIMP_TAC std_ss [REAL_LT_IMP_LE] THEN
  `2:real * (sig * sig) <> 0` by METIS_TAC [REAL_LT_IMP_NE] THEN
  `(abs a * abs a) <> 0` by METIS_TAC [REAL_LT_IMP_NE] THEN
  FULL_SIMP_TAC std_ss [GSYM POW_2, REAL_INV_MUL] THEN
  ONCE_REWRITE_TAC [GSYM REAL_MUL_ASSOC] THEN
  ONCE_REWRITE_TAC [GSYM REAL_POW2_ABS] THEN
  ASM_SIMP_TAC real_ss [REAL_MUL_LINV, ABS_ABS]);

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* ------------------------------------------------------------------------- *)

(* DFUNSET *)
val Pi = new_definition("Pi",``Pi A B = {f | !x. x IN A ==> f x IN B x}``);

val Pi_iff = store_thm ("Pi_iff",
  ``!f I X. f IN Pi I X = (!i. i IN I ==> f i IN X i)``,
  SET_TAC [Pi]);

val indep_sets = new_definition("indep_sets",``indep_sets p ff ii = prob_space p /\
     (!i. i IN (ii:num->bool) ==> (ff i) SUBSET events p) /\
     (!J. J SUBSET ii /\ J <> {} /\ FINITE J ==>
       !A. A IN (Pi J ff) ==> (prob p (BIGINTER {A j | j IN J}) =
                       Normal (product J (\j. real (prob p (A j))))))``);

val indep_set = new_definition("indep_set",``indep_set p A B = prob_space p /\
   indep_sets p (\i. if i = 0 then A else B) UNIV``);

val indep_vars = new_definition("indep_vars",``indep_vars p M X ii =
  (!i. i IN ii ==> random_variable (X i) p (m_space (M i), measurable_sets (M i))) /\
  indep_sets p (\i. {(PREIMAGE f A) INTER p_space p | (f = X i) /\ A IN measurable_sets (M i)}) ii``);

val indep_var = new_definition("indep_var",``indep_var p Ma A Mb B =
                        indep_vars p (\i. if i = 0 then Ma else Mb)
                                     (\i. if i = 0 then A else B) {x | (x = 0) \/ (x = 1)}``);

val indep_sets_cong = store_thm ("indep_sets_cong",
  ``!p ii J ff G. prob_space p /\ (ii = J) /\ (!i. i IN ii ==> (ff i = G i)) ==>
      (indep_sets p ff ii = indep_sets p G J)``,
  RW_TAC std_ss [indep_sets] THEN ASM_SET_TAC [Pi_iff]);

val indep_sets_mono_index = store_thm ("indep_sets_mono_index",
  ``!ff ii J p. prob_space p /\ J SUBSET ii /\ indep_sets p ff ii ==>
                indep_sets p ff J``,
  RW_TAC std_ss [indep_sets] THENL [ASM_SET_TAC [], ALL_TAC] THEN
  ASM_SET_TAC []);

val indep_sets_finite_index_sets = store_thm ("indep_sets_finite_index_sets",
  ``!p ff ii. prob_space p ==> (indep_sets p ff ii =
    (!J. J SUBSET ii /\ J <> {} /\ FINITE J ==> indep_sets p ff J))``,
  RW_TAC std_ss [indep_sets] THEN EQ_TAC THEN RW_TAC std_ss [] THENL
  [ASM_SET_TAC [], ASM_SET_TAC [], ALL_TAC, ASM_SET_TAC []] THEN
  FIRST_X_ASSUM (MP_TAC o Q.SPEC `{i}`) THEN
  ASM_SET_TAC [FINITE_SING]);

val indep_sets_mono_sets = store_thm ("indep_sets_mono_sets",
  ``!p ff G ii. indep_sets p ff ii /\
      (!i. i IN ii ==> G i SUBSET ff i) ==> indep_sets p G ii``,
  RW_TAC std_ss [indep_sets] THENL [ASM_SET_TAC [], ALL_TAC] THEN
  FIRST_X_ASSUM (MP_TAC o Q.SPEC `J:num->bool`) THEN
  ASM_SIMP_TAC std_ss [] THEN DISCH_THEN MATCH_MP_TAC THEN
  FULL_SIMP_TAC std_ss [Pi_iff] THEN ASM_SET_TAC []);

val indep_setsI = store_thm ("indep_setsI",
 ``!p ff ii. prob_space p /\ (!i. i IN ii ==> ff i SUBSET events p) /\
     (!A J. J <> {} /\ J SUBSET ii /\ FINITE J /\
       (!j. j IN J ==> A j IN ff j) ==>
     (prob p (BIGINTER {A j | j IN J}) =
      Normal (product J (\j. real (prob p (A j)))))) ==>
    indep_sets p ff ii``,
  RW_TAC std_ss [indep_sets] THEN ASM_SET_TAC [Pi_iff]);

val indep_setsD = store_thm ("indep_setsD",
  ``!p ff ii A J. prob_space p /\ indep_sets p ff ii /\ J SUBSET ii /\ J <> {} /\
     FINITE J /\ (!j. j IN J ==> A j IN ff j) ==>
     (prob p (BIGINTER {A j | j IN J}) =
      Normal (product J (\j. real (prob p (A j)))))``,
  RW_TAC std_ss [indep_sets] THEN ASM_SET_TAC [Pi_iff]);

val indep_sets_dynkin = store_thm ("indep_sets_dynkin",
  ``!p ff ii. prob_space p /\ indep_sets p ff ii ==>
      indep_sets p (\i. dynkin (p_space p) (ff i)) ii``,
  REPEAT STRIP_TAC THEN
  Q_TAC SUFF_TAC `!J. J SUBSET ii /\ J <> {} /\ FINITE J ==>
   indep_sets p (\i. dynkin (p_space p) (ff i)) J` THENL
  [METIS_TAC [indep_sets_finite_index_sets], ALL_TAC] THEN
  RW_TAC std_ss [] THEN
  `indep_sets p ff J` by METIS_TAC [indep_sets_finite_index_sets] THEN
  Q.ABBREV_TAC `gg =
   (\s i. if i IN s then (\i. dynkin (p_space p) (ff i)) i else ff i)` THEN
  Q_TAC SUFF_TAC `indep_sets p (gg J) ii` THENL
  [DISCH_TAC,
   UNDISCH_TAC ``J <> {}:num->bool`` THEN
   UNDISCH_TAC ``indep_sets p ff J`` THEN
   UNDISCH_TAC ``J SUBSET ii:num->bool`` THEN
   UNDISCH_TAC ``FINITE (J:num->bool)`` THEN
   Q.SPEC_TAC (`J`,`J`) THEN SET_INDUCT_TAC THENL
   [METIS_TAC [NOT_IN_EMPTY, ETA_AX], ALL_TAC] THEN
   Q.ABBREV_TAC `G = gg s` THEN RW_TAC std_ss [] THEN
   Q_TAC SUFF_TAC `indep_sets p G ii /\
    (!i. i IN ii ==> G i SUBSET events p) /\ e IN ii` THENL
   [STRIP_TAC,
    `e IN ii` by ASM_SET_TAC [] THEN ASM_SIMP_TAC std_ss [] THEN
    `s SUBSET ii` by ASM_SET_TAC [] THEN
    Q_TAC SUFF_TAC `indep_sets p G ii` THENL
    [DISCH_TAC THEN ASM_SIMP_TAC std_ss [],
     ASM_CASES_TAC ``s = {}:num->bool`` THENL
     [Q.UNABBREV_TAC `G` THEN Q.UNABBREV_TAC `gg` THEN
      ASM_SIMP_TAC std_ss [NOT_IN_EMPTY] THEN METIS_TAC [ETA_AX],
      ALL_TAC] THEN
     `indep_sets p ff s` by METIS_TAC [indep_sets_finite_index_sets] THEN
     METIS_TAC []] THEN
    POP_ASSUM MP_TAC THEN RW_TAC std_ss [indep_sets]] THEN
   Q.ABBREV_TAC `dd = {E | E IN events p /\
    indep_sets p (\i. if i = e then {E} else G i) ii}` THEN
   Q_TAC SUFF_TAC `!X. X IN events p /\
    (!J A. J <> {} /\ J SUBSET ii /\ FINITE J /\ e NOTIN J /\
     (!i. i IN J ==> A i IN G i) ==>
     (prob p (BIGINTER {A j | j IN J} INTER X) = prob p X *
      Normal (product J (\j. real (prob p (A j)))))) ==>
    indep_sets p (\i. if i = e then {X} else G i) ii` THENL
   [DISCH_TAC,
    RW_TAC std_ss [] THEN MATCH_MP_TAC indep_setsI THEN
    ASM_SIMP_TAC std_ss [] THEN CONJ_TAC THENL
    [RW_TAC std_ss [] THEN ASM_SET_TAC [], ALL_TAC] THEN
    RW_TAC std_ss [] THEN ASM_CASES_TAC ``e IN J:num->bool`` THENL
    [`A e = X` by
     (FIRST_X_ASSUM (MP_TAC o Q.SPEC `e`) THEN ASM_SIMP_TAC std_ss [IN_SING]) THEN
     ASM_CASES_TAC ``J = {e:num}`` THENL
     [ASM_SIMP_TAC std_ss [IN_SING] THEN
      `{A j | j = e} = {X}` by ASM_SET_TAC [] THEN
      ASM_SIMP_TAC std_ss [PRODUCT_SING, BIGINTER_SING] THEN
      METIS_TAC [normal_real, PROB_FINITE], ALL_TAC] THEN
     Q_TAC SUFF_TAC `prob p (BIGINTER {A j | j IN J}) =
                     prob p (BIGINTER {A j | j IN J DIFF {e}} INTER X)` THENL
     [DISCH_TAC, AP_TERM_TAC THEN ASM_SET_TAC []] THEN
     Q_TAC SUFF_TAC `prob p (BIGINTER {A j | j IN J DIFF {e}} INTER X) =
          prob p X * Normal (product (J DIFF {e}) (\j. real (prob p (A j))))` THENL
     [DISCH_TAC,
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_SIMP_TAC std_ss [FINITE_DIFF, FINITE_SING] THEN ASM_SET_TAC []] THEN
     ASM_SIMP_TAC std_ss [] THEN UNDISCH_TAC ``A (e:num) = X:'a->bool`` THEN
     DISCH_THEN (fn th => ASSUME_TAC (GSYM th) THEN ASM_REWRITE_TAC [GSYM th]) THEN
     Q_TAC SUFF_TAC `prob p (A e) = Normal (product {e} (\j. real (prob p (A j))))` THENL
     [DISC_RW_KILL THEN SIMP_TAC std_ss [extreal_mul_def],
      SIMP_TAC std_ss [PRODUCT_SING] THEN METIS_TAC [PROB_FINITE, normal_real]] THEN
     `FINITE {e} /\ FINITE (J DIFF {e}) /\ DISJOINT {e} (J DIFF {e})`
      by (ASM_SIMP_TAC std_ss [FINITE_SING, FINITE_DIFF] THEN ASM_SET_TAC []) THEN
     ASM_SIMP_TAC std_ss [GSYM PRODUCT_UNION] THEN
     `{e} UNION (J DIFF {e}) = J` by ASM_SET_TAC [] THEN ASM_SIMP_TAC std_ss [],
     ALL_TAC] THEN
    FIRST_X_ASSUM (MP_TAC o Q.SPECL [`J`, `A`]) THEN ASM_SIMP_TAC std_ss [] THEN
    `(!i. i IN J ==> A i IN G i)` by ASM_SET_TAC [] THEN ASM_SIMP_TAC std_ss [] THEN
    DISCH_TAC THEN MATCH_MP_TAC indep_setsD THEN METIS_TAC []] THEN
   Q_TAC SUFF_TAC `dynkin_system (p_space p) dd` THENL
   [DISCH_TAC,
    MATCH_MP_TAC dynkin_systemI THEN Q.UNABBREV_TAC `dd` THEN
    SIMP_TAC std_ss [GSPECIFICATION] THEN CONJ_TAC THENL
    [RW_TAC std_ss [events_def, p_space_def] THEN
     MATCH_MP_TAC MEASURE_SPACE_SUBSET_MSPACE THEN METIS_TAC [prob_space_def],
     ALL_TAC] THEN
    CONJ_TAC THENL
    [ASM_SIMP_TAC std_ss [EVENTS_SPACE] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
     ASM_SIMP_TAC std_ss [EVENTS_SPACE] THEN RW_TAC std_ss [] THEN
     Q_TAC SUFF_TAC `BIGINTER {A j | j IN J} SUBSET p_space p` THENL
     [DISCH_TAC,
      MATCH_MP_TAC BIGINTER_SUBSET THEN CONJ_TAC THENL [ALL_TAC, ASM_SET_TAC []] THEN
      FULL_SIMP_TAC std_ss [prob_space_def, p_space_def, events_def] THEN
      RW_TAC std_ss [GSPECIFICATION] THEN MATCH_MP_TAC MEASURE_SPACE_SUBSET_MSPACE THEN
      ASM_SET_TAC []] THEN
     `!a b. a SUBSET b ==> (a INTER b = a)` by ASM_SET_TAC [] THEN
     FULL_SIMP_TAC std_ss [prob_space_def, GSYM prob_def, mul_lone] THEN
     `prob_space p` by METIS_TAC [prob_space_def, prob_def] THEN
     `indep_sets p G J` by METIS_TAC [indep_sets_finite_index_sets] THEN
     POP_ASSUM MP_TAC THEN RW_TAC std_ss [indep_sets] THEN
     POP_ASSUM (MP_TAC o Q.SPEC `J`) THEN ASM_SIMP_TAC std_ss [SUBSET_REFL] THEN
     DISCH_THEN MATCH_MP_TAC THEN METIS_TAC [Pi_iff],
     ALL_TAC] THEN
    CONJ_TAC THENL
    [GEN_TAC THEN STRIP_TAC THEN
     `p_space p DIFF A IN events p` by METIS_TAC [EVENTS_COMPL] THEN
     ASM_SIMP_TAC std_ss [] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
     ASM_SIMP_TAC std_ss [] THEN RW_TAC std_ss [] THEN
     Q.ABBREV_TAC `eJ = e INSERT J` THEN
     Q_TAC SUFF_TAC `prob p (BIGINTER {A' j | j IN J} INTER (p_space p DIFF A)) =
       prob p (BIGINTER {A' j | j IN J} DIFF
               BIGINTER {(\j. if j = e then A else A' j) j | j IN eJ})` THENL
     [DISC_RW_KILL,
      Q_TAC SUFF_TAC `BIGINTER {A' j | j IN J} SUBSET p_space p` THENL
      [DISCH_TAC,
       MATCH_MP_TAC BIGINTER_SUBSET THEN CONJ_TAC THENL [ALL_TAC, ASM_SET_TAC []] THEN
       FULL_SIMP_TAC std_ss [prob_space_def, p_space_def, events_def] THEN
       RW_TAC std_ss [GSPECIFICATION] THEN MATCH_MP_TAC MEASURE_SPACE_SUBSET_MSPACE THEN
       ASM_SET_TAC []] THEN
      AP_TERM_TAC THEN ASM_SET_TAC []] THEN
     Q_TAC SUFF_TAC `prob p (BIGINTER {A' j | j IN J} DIFF
          BIGINTER {(\j. if j = e then A else A' j) j | j IN eJ}) =
       prob p (BIGINTER {A' j | j IN J}) -
       prob p (BIGINTER {(\j. if j = e then A else A' j) j | j IN eJ})` THENL
     [DISC_RW_KILL,
      SIMP_TAC std_ss [prob_def] THEN MATCH_MP_TAC measure_Diff THEN
      CONJ_TAC THENL [METIS_TAC [prob_space_def], ALL_TAC] THEN
      Q_TAC SUFF_TAC `BIGINTER {A' j | j IN J} IN measurable_sets p` THENL
      [DISCH_TAC THEN ASM_SIMP_TAC std_ss [],
       SIMP_TAC std_ss [GSYM events_def] THEN MATCH_MP_TAC EVENTS_COUNTABLE_INTER THEN
       ASM_SIMP_TAC std_ss [GSYM IMAGE_DEF] THEN
       CONJ_TAC THENL [ASM_SET_TAC [IMAGE_DEF], ALL_TAC] THEN
       CONJ_TAC THENL [ALL_TAC, ASM_SET_TAC [IMAGE_DEF]] THEN
       MATCH_MP_TAC pred_setTheory.image_countable THEN METIS_TAC [finite_countable]] THEN
      Q_TAC SUFF_TAC `BIGINTER {if j = e then A else A' j | j IN eJ} IN
                      measurable_sets p` THENL
      [DISCH_TAC THEN ASM_SIMP_TAC std_ss [],
       FULL_SIMP_TAC std_ss [GSYM events_def] THEN
       `BIGINTER {if j = e then A else A' j | j IN eJ} =
        BIGINTER {A' j | j IN J} INTER A` by ASM_SET_TAC [] THEN
       POP_ASSUM (fn th => REWRITE_TAC [th]) THEN
       ONCE_REWRITE_TAC [METIS [subsets_def]
        ``events p = subsets (p_space p, events p)``] THEN
       MATCH_MP_TAC ALGEBRA_INTER THEN ASM_SIMP_TAC std_ss [subsets_def] THEN
       FULL_SIMP_TAC std_ss [prob_space_def, p_space_def, events_def] THEN
       FULL_SIMP_TAC std_ss [measure_space_def, sigma_algebra_def]] THEN
      CONJ_TAC THENL
      [`BIGINTER {if j = e then A else A' j | j IN eJ} =
        BIGINTER {A' j | j IN J} INTER A` by ASM_SET_TAC [] THEN
       POP_ASSUM (fn th => REWRITE_TAC [th]) THEN
       SIMP_TAC std_ss [SET_RULE ``!A B. A INTER B SUBSET A``],
       ALL_TAC] THEN
      FULL_SIMP_TAC std_ss [GSYM events_def, GSYM prob_def] THEN
      METIS_TAC [PROB_FINITE]] THEN
     Q_TAC SUFF_TAC `prob p (BIGINTER {A' j | j IN J}) =
      prob p (p_space p) * Normal (product J (\j. real (prob p (A' j))))` THENL
     [DISC_RW_KILL,
      `prob p (p_space p) = 1` by METIS_TAC [prob_space_def, prob_def] THEN
      ASM_SIMP_TAC std_ss [mul_lone] THEN MATCH_MP_TAC indep_setsD THEN
      METIS_TAC []] THEN
     Q_TAC SUFF_TAC `prob p (BIGINTER {(\j. if j = e then A else A' j) j | j IN eJ}) =
      Normal (product (e INSERT J) (\j. real (prob p ((\j. if j = e then A else A' j) j))))` THENL
     [DISCH_TAC,
      Q.UNABBREV_TAC `eJ` THEN MATCH_MP_TAC indep_setsD THEN
      Q.EXISTS_TAC `(\i. if i = e then {A} else G i)` THEN
      Q.EXISTS_TAC `ii` THEN ASM_SIMP_TAC std_ss [] THEN
      CONJ_TAC THENL [ASM_SET_TAC [], ALL_TAC] THEN
      CONJ_TAC THENL [ASM_SET_TAC [], ALL_TAC] THEN
      CONJ_TAC THENL [ASM_SET_TAC [FINITE_INSERT], ALL_TAC] THEN
      RW_TAC std_ss [IN_SING] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_SET_TAC []] THEN ASM_SIMP_TAC std_ss [] THEN
     Q_TAC SUFF_TAC `Normal (product eJ (\j. real (prob p (if j = e then A else A' j)))) =
          prob p A * Normal (product J (\j. real (prob p (if j = e then A else A' j))))` THENL
     [DISC_RW_KILL,
      `prob p A <> NegInf /\ prob p A <> PosInf` by METIS_TAC [PROB_FINITE] THEN
      `prob p A = Normal (product {e} (\j. real (prob p (if j = e then A else A' j))))`
       by ASM_SIMP_TAC std_ss [normal_real, PRODUCT_SING] THEN
      POP_ASSUM (fn th => REWRITE_TAC [th]) THEN SIMP_TAC std_ss [extreal_mul_def] THEN
      `FINITE {e} /\ FINITE J /\ DISJOINT {e} J` by ASM_SET_TAC [FINITE_SING] THEN
      SIMP_TAC std_ss [extreal_11] THEN `eJ = {e} UNION J` by ASM_SET_TAC [] THEN
      METIS_TAC [PRODUCT_UNION]] THEN
     Q_TAC SUFF_TAC `product J (\j. real (prob p (if j = e then A else A' j))) =
                     product J (\j. real (prob p (A' j)))` THENL
     [DISC_RW_KILL,
      MATCH_MP_TAC PRODUCT_EQ THEN ASM_SET_TAC []] THEN
     `p_space p IN events p` by METIS_TAC [EVENTS_SPACE] THEN
     `prob p (p_space p) = Normal (real (prob p (p_space p)))`
      by METIS_TAC [normal_real, PROB_FINITE] THEN
     `prob p A = Normal (real (prob p A))` by METIS_TAC [normal_real, PROB_FINITE] THEN
     ONCE_ASM_REWRITE_TAC [] THEN SIMP_TAC std_ss [extreal_mul_def] THEN
     SIMP_TAC std_ss [extreal_not_infty, extreal_sub_add] THEN
     SIMP_TAC std_ss [GSYM extreal_mul_def] THEN
     SIMP_TAC std_ss [GSYM mul_lneg, extreal_ainv_def] THEN
     SIMP_TAC std_ss [GSYM add_rdistrib_normal, extreal_not_infty] THEN
     AP_THM_TAC THEN AP_TERM_TAC THEN SIMP_TAC std_ss [GSYM extreal_ainv_def] THEN
     ASM_SIMP_TAC std_ss [extreal_not_infty, GSYM extreal_sub_add] THEN
     ASM_SIMP_TAC std_ss [PROB_FINITE, normal_real] THEN
     REWRITE_TAC [prob_def] THEN MATCH_MP_TAC (GSYM measure_Diff) THEN
     CONJ_TAC THENL [METIS_TAC [prob_space_def], ALL_TAC] THEN
     ASM_SIMP_TAC std_ss [GSYM events_def] THEN
     ASM_SIMP_TAC std_ss [GSYM PROB_FINITE, GSYM prob_def, p_space_def] THEN
     MATCH_MP_TAC MEASURABLE_SETS_SUBSET_SPACE THEN
     METIS_TAC [prob_space_def, events_def],
     ALL_TAC] THEN
    GEN_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
    `BIGUNION (IMAGE A univ(:num)) IN events p` by
     (MATCH_MP_TAC EVENTS_COUNTABLE_UNION THEN
      SIMP_TAC std_ss [COUNTABLE_NUM, pred_setTheory.image_countable] THEN
      ASM_SET_TAC []) THEN ASM_SIMP_TAC std_ss [] THEN
    `!i. A i IN events p` by ASM_SET_TAC [] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC std_ss [] THEN RW_TAC std_ss [] THEN
    `!i. i IN J ==> A' i IN events p` by ASM_SET_TAC [] THEN
    Q.ABBREV_TAC `eJ = e INSERT J` THEN
    Q_TAC SUFF_TAC `prob p (BIGINTER {A' j | j IN J} INTER BIGUNION (IMAGE A univ(:num))) =
      prob p (BIGUNION {BIGINTER {if i = e then A k else A' i | i IN eJ} | k IN UNIV})` THENL
    [DISC_RW_KILL,
     AP_TERM_TAC THEN
     SIMP_TAC std_ss [INTER_DEF, GSPECIFICATION,
      IN_BIGINTER, IN_BIGUNION, IMAGE_DEF, EXTENSION] THEN
     GEN_TAC THEN EQ_TAC THENL [ALL_TAC, ASM_SET_TAC []] THEN
     RW_TAC std_ss [IN_UNIV] THEN
     Q.EXISTS_TAC `BIGINTER {if i = e then A x' else A' i | i IN eJ}` THEN
     RW_TAC std_ss [] THENL
     [ASM_SIMP_TAC std_ss [IN_BIGINTER, GSPECIFICATION] THEN RW_TAC std_ss [] THEN
      COND_CASES_TAC THEN FULL_SIMP_TAC std_ss [] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_SET_TAC [], ALL_TAC] THEN
     Q.EXISTS_TAC `x'` THEN ASM_SIMP_TAC std_ss [IN_BIGINTER, GSPECIFICATION] THEN
     METIS_TAC []] THEN
    Q_TAC SUFF_TAC `suminf (prob p o (\k. BIGINTER {if i = e then A k else A' i | i IN eJ})) =
            prob p (BIGUNION {BIGINTER {if i = e then A k else A' i | i IN eJ} | k IN UNIV})` THENL
    [DISCH_TAC,
     SIMP_TAC std_ss [prob_def] THEN MATCH_MP_TAC MEASURE_COUNTABLY_ADDITIVE THEN
     CONJ_TAC THENL [METIS_TAC [prob_space_def], ALL_TAC] THEN
     CONJ_TAC THENL
     [SIMP_TAC std_ss [IN_FUNSET] THEN RW_TAC std_ss [GSYM events_def] THEN
      MATCH_MP_TAC EVENTS_COUNTABLE_INTER THEN ASM_SIMP_TAC std_ss [] THEN
      CONJ_TAC THENL [ASM_SET_TAC [], ALL_TAC] THEN
      `countable {(\i. if i = e then A k else A' i) i | i IN eJ}` by
       (SIMP_TAC std_ss [GSYM IMAGE_DEF] THEN MATCH_MP_TAC pred_setTheory.image_countable THEN
        MATCH_MP_TAC finite_countable THEN METIS_TAC [FINITE_INSERT]) THEN
      FULL_SIMP_TAC std_ss [] THEN ASM_SET_TAC [],
      ALL_TAC] THEN
     CONJ_TAC THENL
     [FULL_SIMP_TAC std_ss [DISJOINT_DEF, disjoint_family, disjoint_family_on] THEN
      ASM_SET_TAC [], ALL_TAC] THEN
     ASM_SET_TAC []] THEN
    Q_TAC SUFF_TAC `!k. prob p (BIGINTER {(\j. if j = e then A k else A' j) j | j IN eJ}) =
                        prob p (A k) * Normal (product J (\j. real (prob p (A' j))))` THENL
    [DISCH_TAC,
     GEN_TAC THEN
     Q_TAC SUFF_TAC `prob p (BIGINTER {(\j. if j = e then A k else A' j) j | j IN eJ}) =
      Normal (product (e INSERT J) (\j. real (prob p ((\j. if j = e then A k else A' j) j))))` THENL
     [DISCH_TAC,
      Q.UNABBREV_TAC `eJ` THEN MATCH_MP_TAC indep_setsD THEN
      Q.EXISTS_TAC `(\i. if i = e then {A k} else G i)` THEN
      Q.EXISTS_TAC `ii` THEN ASM_SIMP_TAC std_ss [] THEN
      CONJ_TAC THENL [ASM_SET_TAC [], ALL_TAC] THEN
      CONJ_TAC THENL [ASM_SET_TAC [], ALL_TAC] THEN
      CONJ_TAC THENL [ASM_SET_TAC [], ALL_TAC] THEN
      CONJ_TAC THENL [ASM_SET_TAC [FINITE_INSERT], ALL_TAC] THEN
      RW_TAC std_ss [IN_SING] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_SET_TAC []] THEN ASM_SIMP_TAC std_ss [] THEN
     Q_TAC SUFF_TAC `Normal (product eJ (\j. real (prob p (if j = e then A k else A' j)))) =
          prob p (A k) * Normal (product J (\j. real (prob p (if j = e then A k else A' j))))` THENL
     [DISC_RW_KILL,
      `prob p (A k) <> NegInf /\ prob p (A k) <> PosInf` by METIS_TAC [PROB_FINITE] THEN
      `prob p (A k) = Normal (product {e} (\j. real (prob p (if j = e then A k else A' j))))`
       by ASM_SIMP_TAC std_ss [normal_real, PRODUCT_SING] THEN
      POP_ASSUM (fn th => REWRITE_TAC [th]) THEN SIMP_TAC std_ss [extreal_mul_def] THEN
      `FINITE {e} /\ FINITE J /\ DISJOINT {e} J` by ASM_SET_TAC [FINITE_SING] THEN
      SIMP_TAC std_ss [extreal_11] THEN `eJ = {e} UNION J` by ASM_SET_TAC [] THEN
      METIS_TAC [PRODUCT_UNION]] THEN
     Q_TAC SUFF_TAC `product J (\j. real (prob p (if j = e then A k else A' j))) =
                     product J (\j. real (prob p (A' j)))` THENL
     [DISC_RW_KILL,
      MATCH_MP_TAC PRODUCT_EQ THEN ASM_SET_TAC []] THEN
     SIMP_TAC std_ss []] THEN
    Q_TAC SUFF_TAC `!k. prob p (A k) * Normal (product J (\j. real (prob p (A' j)))) =
                        prob p (A k) * prob p (BIGINTER {A' j | j IN J})` THENL
    [DISCH_TAC, GEN_TAC THEN AP_TERM_TAC THEN
     MATCH_MP_TAC (GSYM indep_setsD) THEN METIS_TAC []] THEN
    Q_TAC SUFF_TAC `suminf (\k. prob p (A k) * prob p (BIGINTER {A' j | j IN J})) =
           prob p (BIGUNION {A k | k IN UNIV}) * prob p (BIGINTER {A' j | j IN J})` THENL
    [DISCH_TAC,
     ONCE_REWRITE_TAC [mul_comm] THEN
     Q_TAC SUFF_TAC `suminf (\k. prob p (BIGINTER {A' j | j IN J}) * (\k. prob p (A k)) k) =
                     prob p (BIGINTER {A' j | j IN J}) * suminf (\k. prob p (A k))` THENL
     [SIMP_TAC std_ss [] THEN DISC_RW_KILL,
      MATCH_MP_TAC ext_suminf_cmul THEN RW_TAC std_ss [] THENL
      [ALL_TAC, MATCH_MP_TAC PROB_POSITIVE THEN ASM_SIMP_TAC std_ss []] THEN
      MATCH_MP_TAC PROB_POSITIVE THEN ASM_SIMP_TAC std_ss [] THEN
      MATCH_MP_TAC EVENTS_COUNTABLE_INTER THEN ASM_SIMP_TAC std_ss [GSYM IMAGE_DEF] THEN
      CONJ_TAC THENL [ASM_SET_TAC [IMAGE_DEF], ALL_TAC] THEN
      CONJ_TAC THENL [ALL_TAC, ASM_SET_TAC []] THEN
      MATCH_MP_TAC pred_setTheory.image_countable THEN METIS_TAC [finite_countable]] THEN
     AP_TERM_TAC THEN SIMP_TAC std_ss [GSYM o_DEF, prob_def] THEN
     MATCH_MP_TAC MEASURE_COUNTABLY_ADDITIVE THEN
     CONJ_TAC THENL [METIS_TAC [prob_space_def], ALL_TAC] THEN
     ASM_SIMP_TAC std_ss [IN_FUNSET, GSYM events_def, IMAGE_DEF] THEN
     ASM_SET_TAC [DISJOINT_DEF, disjoint_family, disjoint_family_on]] THEN
    Q_TAC SUFF_TAC `prob p (BIGINTER {A' j | j IN J}) =
            Normal (product J (\j. real (prob p (A' j))))` THENL
    [DISCH_TAC, MATCH_MP_TAC indep_setsD THEN METIS_TAC []] THEN
    POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
    POP_ASSUM MP_TAC THEN POP_ASSUM (ASSUME_TAC o ONCE_REWRITE_RULE [EQ_SYM_EQ]) THEN
    ASM_SIMP_TAC std_ss [] THEN REWRITE_TAC [o_DEF] THEN REPEAT STRIP_TAC THEN
    SIMP_TAC std_ss [] THEN ONCE_ASM_REWRITE_TAC [] THEN ONCE_ASM_REWRITE_TAC [] THEN
    ONCE_ASM_REWRITE_TAC [] THEN ONCE_ASM_REWRITE_TAC [] THEN
    SIMP_TAC std_ss [IMAGE_DEF]] THEN
   Q_TAC SUFF_TAC `dynkin (p_space p) (G e) SUBSET
    {E | E IN events p /\ indep_sets p (\i. if i = e then {E} else G i) ii}` THENL
   [DISCH_TAC,
    MATCH_MP_TAC dynkin_subset THEN ASM_SIMP_TAC std_ss [] THEN
    Q.UNABBREV_TAC `dd` THEN RW_TAC std_ss [SUBSET_DEF, GSPECIFICATION] THENL
    [ASM_SET_TAC [], ALL_TAC] THEN MATCH_MP_TAC indep_sets_mono_sets THEN
    Q.EXISTS_TAC `G` THEN ASM_SIMP_TAC std_ss [] THEN
    Q.UNABBREV_TAC `G` THEN RW_TAC std_ss [SUBSET_DEF, IN_SING]] THEN
   Q_TAC SUFF_TAC `indep_sets p (\i. if i = e then dd else G i) ii` THENL
   [DISCH_TAC,
    MATCH_MP_TAC indep_setsI THEN ASM_SIMP_TAC std_ss [] THEN
    CONJ_TAC THENL [ASM_SET_TAC [], ALL_TAC] THEN
    RW_TAC std_ss [] THEN ASM_CASES_TAC ``e IN J:num->bool`` THENL
    [Q_TAC SUFF_TAC `indep_sets p (\i. if i = e then {A i} else G i) ii` THENL
     [DISCH_TAC, ASM_SET_TAC []] THEN
     MATCH_MP_TAC indep_setsD THEN Q.EXISTS_TAC `(\i. if i = e then {A i} else G i)` THEN
     Q.EXISTS_TAC `ii` THEN ASM_SIMP_TAC std_ss [] THEN METIS_TAC [IN_SING],
     ALL_TAC] THEN
    `!i. i IN J ==> A i IN G i` by ASM_SET_TAC [] THEN
    MATCH_MP_TAC indep_setsD THEN METIS_TAC []] THEN
   Q_TAC SUFF_TAC `indep_sets p (\i. if i = e then dynkin (p_space p) (G e) else G i) ii` THENL
   [DISCH_TAC,
    MATCH_MP_TAC indep_sets_mono_sets THEN Q.EXISTS_TAC `(\i. if i = e then dd else G i)` THEN
    ASM_SIMP_TAC std_ss [SUBSET_DEF] THEN RW_TAC std_ss [] THEN
    ASM_SET_TAC []] THEN
   Q.UNABBREV_TAC `gg` THEN SIMP_TAC std_ss [] THEN
   MATCH_MP_TAC indep_sets_mono_sets THEN
   Q.EXISTS_TAC `(\i. if i = e then dynkin (p_space p) (G e) else G i)` THEN
   ASM_SIMP_TAC std_ss [] THEN ASM_SET_TAC []] THEN
  Q.UNABBREV_TAC `gg` THEN FULL_SIMP_TAC std_ss [] THEN
  MATCH_MP_TAC indep_sets_mono_sets THEN
  Q.EXISTS_TAC `(\i. if i IN J then dynkin (p_space p) (ff i) else ff i)` THEN
  ASM_SIMP_TAC std_ss [SUBSET_REFL] THEN ASM_SET_TAC [indep_sets]);

val indep_sets_sigma = store_thm ("indep_sets_sigma",
  ``!p ff ii. prob_space p /\ indep_sets p ff ii /\
              (!i. i IN ii ==> Int_stable (ff i)) ==>
              indep_sets p (\i. subsets (sigma (p_space p) (ff i))) ii``,
  RW_TAC std_ss [] THEN
  Q_TAC SUFF_TAC `indep_sets p (\i. dynkin (p_space p) (ff i)) ii` THENL
  [ALL_TAC, ASM_SIMP_TAC std_ss [indep_sets_dynkin]] THEN
  Q_TAC SUFF_TAC `!i. i IN ii ==>
   (subsets (sigma (p_space p) (ff i)) = dynkin (p_space p) (ff i))` THENL
  [RW_TAC std_ss [Pi_iff, indep_sets] THEN ASM_SET_TAC [], ALL_TAC] THEN
  RW_TAC std_ss [] THEN MATCH_MP_TAC sigma_eq_dynkin THEN
  ASM_SIMP_TAC std_ss [] THEN
  `!s. s IN events p ==> s SUBSET p_space p` by
   METIS_TAC [prob_space_def, p_space_def, events_def, MEASURABLE_SETS_SUBSET_SPACE] THEN
  ASM_SET_TAC [POW_DEF, indep_sets]);

val sigma_eq_dynkin' = store_thm ("sigma_eq_dynkin'",
  ``!sp M. M SUBSET POW sp /\ Int_stable M ==>
             (sigma_sets sp M = dynkin sp M)``,
  RW_TAC std_ss [] THEN
  Q_TAC SUFF_TAC `dynkin sp M SUBSET (sigma_sets sp M)` THENL
  [DISCH_TAC,
   SIMP_TAC std_ss [dynkin, SUBSET_DEF, IN_BIGINTER, GSPECIFICATION] THEN
   RW_TAC std_ss [] THEN POP_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC sigma_algebra_imp_dynkin_system THEN
    MATCH_MP_TAC sigma_algebra_sigma_sets THEN ASM_SIMP_TAC std_ss [],
    ALL_TAC] THEN
   SIMP_TAC std_ss [sigma_sets_basic]] THEN
  `dynkin_system sp (dynkin sp M)` by METIS_TAC [dynkin_system_dynkin] THEN
  Q_TAC SUFF_TAC `sigma_algebra (sp, dynkin sp M)` THENL
  [DISCH_TAC,
   ASM_SIMP_TAC std_ss [sigma_algebra_eq_Int_stable, Int_stable] THEN
   RW_TAC std_ss [] THEN
   Q.ABBREV_TAC `D = (\E. {Q | Q SUBSET sp /\ Q INTER E IN dynkin sp M})` THEN
   Q_TAC SUFF_TAC `M SUBSET D b` THENL
   [DISCH_TAC,
    RW_TAC std_ss [SUBSET_DEF] THEN
    Q_TAC SUFF_TAC `x IN dynkin sp M` THENL
    [DISCH_TAC,
     SIMP_TAC std_ss [dynkin, IN_BIGINTER, GSPECIFICATION] THEN
     RW_TAC std_ss [SUBSET_DEF]] THEN
    Q_TAC SUFF_TAC `dynkin sp M SUBSET D x` THENL
    [DISCH_TAC,
     MATCH_MP_TAC dynkin_subset THEN Q.UNABBREV_TAC `D` THEN
     RW_TAC std_ss [] THENL
     [ALL_TAC,
      MATCH_MP_TAC restricted_dynkin_system THEN
      ASM_SIMP_TAC std_ss []] THEN
     RW_TAC std_ss [SUBSET_DEF, GSPECIFICATION] THENL
     [ASM_SET_TAC [POW_DEF], ALL_TAC] THEN
     SIMP_TAC std_ss [dynkin, IN_BIGINTER, GSPECIFICATION] THEN
     RW_TAC std_ss [SUBSET_DEF] THEN FIRST_ASSUM MATCH_MP_TAC THEN
     FULL_SIMP_TAC std_ss [Int_stable]] THEN
    `b IN D x` by ASM_SET_TAC [] THEN
    Q.UNABBREV_TAC `D` THEN SIMP_TAC std_ss [GSPECIFICATION] THEN
    CONJ_TAC THENL [ASM_SET_TAC [POW_DEF], ALL_TAC] THEN
    FULL_SIMP_TAC std_ss [GSPECIFICATION] THEN METIS_TAC [INTER_COMM]] THEN
   Q_TAC SUFF_TAC `dynkin sp M SUBSET D b` THENL
   [DISCH_TAC,
    MATCH_MP_TAC dynkin_subset THEN Q.UNABBREV_TAC `D` THEN
    RW_TAC std_ss [] THEN MATCH_MP_TAC restricted_dynkin_system THEN
    ASM_SIMP_TAC std_ss []] THEN
   POP_ASSUM MP_TAC THEN Q.UNABBREV_TAC `D` THEN
   ASM_SIMP_TAC std_ss [GSPECIFICATION, SUBSET_DEF]] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_SIMP_TAC std_ss [] THEN
  MATCH_MP_TAC sigma_sets_subset THEN ASM_SIMP_TAC std_ss [] THEN
  SET_TAC [dynkin]);

val dynkin_lemma' = store_thm ("dynkin_lemma'",
  ``!sp E M. Int_stable E /\ E SUBSET M /\
             M SUBSET sigma_sets sp E /\ dynkin_system sp M ==>
             (sigma_sets sp E = M)``,
  RW_TAC std_ss [] THEN
  `E SUBSET POW sp` by ASM_SET_TAC [POW_DEF, dynkin_system, subset_class_def] THEN
  `sigma_sets sp E = dynkin sp E` by METIS_TAC [sigma_eq_dynkin'] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_SIMP_TAC std_ss [] THEN
  MATCH_MP_TAC dynkin_subset THEN ASM_SIMP_TAC std_ss []);

val sigma_sets_induct_disjoint' = store_thm ("sigma_sets_induct_disjoint'",
  ``!G A P sp.
    Int_stable G /\ G SUBSET POW sp /\ A IN sigma_sets sp G /\
    (!A. A IN G ==> P A) /\ P {} /\
    (!A. A IN sigma_sets sp G ==> P A ==> P (sp DIFF A)) /\
    (!A. disjoint_family A ==> IMAGE A UNIV SUBSET sigma_sets sp G
         ==> (!i. P (A i)) ==> P (BIGUNION (IMAGE A univ(:num)))) ==>
    P A``,
  RW_TAC std_ss [] THEN
  Q.ABBREV_TAC `dd = {A | A IN sigma_sets sp G /\ P A}` THEN
  Q_TAC SUFF_TAC `sigma_algebra (sp, sigma_sets sp G)` THENL
  [DISCH_TAC,
   MATCH_MP_TAC sigma_algebra_sigma_sets THEN
   ASM_SIMP_TAC std_ss []] THEN
  Q_TAC SUFF_TAC `P (sp DIFF {})` THENL
  [RW_TAC std_ss [DIFF_EMPTY],
   FULL_SIMP_TAC std_ss [AND_IMP_INTRO] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC std_ss [] THEN
   SIMP_TAC std_ss [sigma_sets_empty]] THEN
  Q_TAC SUFF_TAC `dynkin_system sp dd` THENL
  [DISCH_TAC,
   MATCH_MP_TAC dynkin_systemI THEN Q.UNABBREV_TAC `dd` THEN
   ASM_SIMP_TAC std_ss [GSPECIFICATION] THEN RW_TAC std_ss [] THENL
   [POP_ASSUM (fn th => POP_ASSUM MP_TAC THEN ASSUME_TAC th) THEN
    Q.SPEC_TAC (`A'`, `A'`) THEN MATCH_MP_TAC sigma_sets_into_sp THEN
    ASM_SIMP_TAC std_ss [],
    ASM_SIMP_TAC std_ss [sigma_sets_top],
    ONCE_REWRITE_TAC [METIS [subsets_def]
     ``sigma_sets sp G = subsets (sp, sigma_sets sp G)``] THEN
    MATCH_MP_TAC ALGEBRA_DIFF THEN
    FULL_SIMP_TAC std_ss [sigma_sets_top, subsets_def, sigma_algebra_def],
    MATCH_MP_TAC (SIMP_RULE std_ss [GSYM IMAGE_DEF] sigma_sets_union) THEN
    ASM_SET_TAC [], ALL_TAC] THEN
   ASM_SET_TAC []] THEN
  Q_TAC SUFF_TAC `sigma_sets sp G = dd` THENL
  [DISCH_TAC,
   MATCH_MP_TAC dynkin_lemma' THEN ASM_SIMP_TAC std_ss [] THEN
   CONJ_TAC THENL [ALL_TAC, ASM_SET_TAC []] THEN
   Q.UNABBREV_TAC `dd` THEN RW_TAC std_ss [GSPECIFICATION, SUBSET_DEF] THEN
   MATCH_MP_TAC sigma_sets_basic THEN ASM_SIMP_TAC std_ss []] THEN
  ASM_SET_TAC []);

val indep_sets_sigma' = store_thm ("indep_sets_sigma'",
  ``!p ff ii. prob_space p /\ indep_sets p ff ii /\
              (!i. i IN ii ==> Int_stable (ff i)) ==>
              indep_sets p (\i. sigma_sets (p_space p) (ff i)) ii``,
  RW_TAC std_ss [] THEN
  Q_TAC SUFF_TAC `indep_sets p (\i. dynkin (p_space p) (ff i)) ii` THENL
  [ALL_TAC, ASM_SIMP_TAC std_ss [indep_sets_dynkin]] THEN
  Q_TAC SUFF_TAC `!i. i IN ii ==>
   (sigma_sets (p_space p) (ff i) = dynkin (p_space p) (ff i))` THENL
  [RW_TAC std_ss [Pi_iff, indep_sets] THEN ASM_SET_TAC [], ALL_TAC] THEN
  RW_TAC std_ss [] THEN MATCH_MP_TAC sigma_eq_dynkin' THEN
  ASM_SIMP_TAC std_ss [] THEN
  `!s. s IN events p ==> s SUBSET p_space p` by
   METIS_TAC [prob_space_def, p_space_def, events_def, MEASURABLE_SETS_SUBSET_SPACE] THEN
  ASM_SET_TAC [POW_DEF, indep_sets]);

val indep_sets_sigma_sets_iff = store_thm ("indep_sets_sigma_sets_iff",
  ``!p ff ii.
     prob_space p /\ (!i. i IN ii ==> Int_stable (ff i)) ==>
     (indep_sets p (\i. subsets (sigma (p_space p) (ff i))) ii =
      indep_sets p ff ii)``,
  RW_TAC std_ss [] THEN EQ_TAC THENL
  [DISCH_TAC, METIS_TAC [indep_sets_sigma]] THEN
  MATCH_MP_TAC indep_sets_mono_sets THEN
  Q.EXISTS_TAC `(\i. subsets (sigma (p_space p) (ff i)))` THEN
  ASM_SIMP_TAC std_ss [] THEN METIS_TAC [SIGMA_SUBSET_SUBSETS]);

val indep_sets_sigma_sets_iff' = store_thm ("indep_sets_sigma_sets_iff'",
  ``!p ff ii.
     prob_space p /\ (!i. i IN ii ==> Int_stable (ff i)) ==>
     (indep_sets p (\i. sigma_sets (p_space p) (ff i)) ii =
      indep_sets p ff ii)``,
  RW_TAC std_ss [] THEN EQ_TAC THENL
  [DISCH_TAC, METIS_TAC [indep_sets_sigma']] THEN
  MATCH_MP_TAC indep_sets_mono_sets THEN
  Q.EXISTS_TAC `(\i. sigma_sets (p_space p) (ff i))` THEN
  ASM_SIMP_TAC std_ss [] THEN METIS_TAC [sigma_sets_superset_generator]);

val indep_vars_def = store_thm ("indep_vars_def",
  ``!p M X ii. prob_space p /\ (!i. i IN ii ==> measure_space (M i)) ==>
     (indep_vars p M X ii =
     ((!i. i IN ii ==> random_variable (X i) p (m_space (M i), measurable_sets (M i))) /\
      indep_sets p (\i. subsets (sigma (p_space p)
       ((\i. {PREIMAGE f A INTER p_space p | (f = X i) /\ A IN measurable_sets (M i)}) i))) ii))``,
  RW_TAC std_ss [indep_vars] THEN
  MATCH_MP_TAC (METIS [] ``(a ==> (b = c)) ==> (a /\ b = a /\ c)``) THEN
  DISCH_TAC THEN
  Q_TAC SUFF_TAC `indep_sets p
    (\i. {PREIMAGE f A INTER p_space p | (f = X i) /\ A IN measurable_sets (M i)}) ii <=>
   indep_sets p (\i. subsets (sigma (p_space p)
   ((\i. {PREIMAGE (f) A INTER p_space p | (f = X i) /\
           A IN measurable_sets (M i)}) i))) ii` THENL
  [SIMP_TAC std_ss [], ALL_TAC] THEN
  MATCH_MP_TAC (GSYM indep_sets_sigma_sets_iff) THEN ASM_SIMP_TAC std_ss [] THEN
  RW_TAC std_ss [Int_stable, GSPECIFICATION, EXISTS_PROD] THEN
  Q.EXISTS_TAC `p_2 INTER p_2'` THEN SIMP_TAC std_ss [PREIMAGE_def, GSPECIFICATION] THEN
  CONJ_TAC THENL [ASM_SET_TAC [], ALL_TAC] THEN
  MATCH_MP_TAC MEASURE_SPACE_INTER THEN METIS_TAC []);

val SIGMA_SETS_SUBSET_EQ = store_thm ("SIGMA_SETS_SUBSET_EQ",
  ``!a b sp. a SUBSET b ==> subsets (sigma sp a) SUBSET subsets (sigma sp b)``,
  RW_TAC std_ss [SUBSET_DEF, subsets_def, sigma_def, IN_BIGINTER, GSPECIFICATION]);

val indep_vars_compose = store_thm ("indep_vars_compose",
  ``!p M N X Y ii. prob_space p /\ indep_vars p M X ii /\
      (!i. i IN ii ==> measure_space (M i)) /\
      (!i. i IN ii ==> measure_space (N i)) /\
      (!i. i IN ii ==> (Y i) IN
         measurable (m_space (M i), measurable_sets (M i))
                    (m_space (N i), measurable_sets (N i))) ==>
      indep_vars p N (\i. Y i o X i) ii``,
  RW_TAC std_ss [indep_vars_def] THENL
  [FULL_SIMP_TAC std_ss [indep_vars] THEN
   FIRST_X_ASSUM (MP_TAC o Q.SPEC `i:num`) THEN
   FIRST_X_ASSUM (MP_TAC o Q.SPEC `i:num`) THEN
   FIRST_X_ASSUM (MP_TAC o Q.SPEC `i:num`) THEN
   FIRST_X_ASSUM (MP_TAC o Q.SPEC `i:num`) THEN
   ASM_SIMP_TAC std_ss [] THEN RW_TAC std_ss [random_variable_def] THEN
   FULL_SIMP_TAC std_ss [IN_MEASURABLE, space_def, subsets_def] THEN
   FULL_SIMP_TAC std_ss [IN_FUNSET, PREIMAGE_def] THEN RW_TAC std_ss [] THEN
   Q_TAC SUFF_TAC `{x | Y i (X i x) IN s} INTER p_space p =
    {x | (X i x) IN ({x | Y i (x) IN s} INTER m_space (M i))} INTER p_space p` THENL
   [DISC_RW_KILL, ASM_SET_TAC []] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
   ASM_SIMP_TAC std_ss [],
   ALL_TAC] THEN
  Q_TAC SUFF_TAC `indep_sets p
   (\i. subsets (sigma (p_space p) ((\i. {(PREIMAGE f A) INTER p_space p |
        (f = X i) /\ A IN measurable_sets (M i)}) i))) ii` THENL
  [RW_TAC std_ss [], METIS_TAC [indep_vars_def]] THEN
  MATCH_MP_TAC indep_sets_mono_sets THEN
  Q.EXISTS_TAC `(\i. subsets (sigma (p_space p)
   {PREIMAGE f A INTER p_space p | (f = X i) /\ A IN measurable_sets (M i)}))` THEN
  ASM_SIMP_TAC std_ss [] THEN RW_TAC std_ss [] THEN MATCH_MP_TAC SIGMA_SETS_SUBSET_EQ THEN
  RW_TAC std_ss [PREIMAGE_def, GSPECIFICATION, EXISTS_PROD, SUBSET_DEF] THEN
  FULL_SIMP_TAC std_ss [IN_MEASURABLE, space_def, subsets_def] THEN
  FULL_SIMP_TAC std_ss [IN_FUNSET, PREIMAGE_def] THEN
  UNDISCH_TAC ``indep_vars p M X ii`` THEN RW_TAC std_ss [indep_vars] THEN
  FIRST_X_ASSUM (MP_TAC o Q.SPEC `i:num`) THEN
  ASM_SIMP_TAC std_ss [] THEN RW_TAC std_ss [random_variable_def] THEN
  FULL_SIMP_TAC std_ss [IN_MEASURABLE, space_def, subsets_def] THEN
  FULL_SIMP_TAC std_ss [IN_FUNSET, PREIMAGE_def] THEN RW_TAC std_ss [] THEN
  Q_TAC SUFF_TAC `{x | Y i (X i x) IN s} INTER p_space p =
   {x | (X i x) IN ({x | Y i (x) IN s} INTER m_space (M i))} INTER p_space p` THENL
  [DISC_RW_KILL, ASM_SET_TAC []] THEN
  Q.EXISTS_TAC `{x | Y i x IN p_2} INTER m_space (M i)` THEN ASM_SET_TAC []);

val indep_var_compose = store_thm ("indep_var_compose",
 ``!p M1 N1 X1 Y1 M2 N2 X2 Y2. prob_space p /\
    measure_space M1 /\ measure_space M2 /\ measure_space N1 /\ measure_space N2 /\
    indep_var p M1 X1 M2 X2 /\
    Y1 IN measurable (m_space M1, measurable_sets M1) (m_space N1, measurable_sets N1) /\
    Y2 IN measurable (m_space M2, measurable_sets M2) (m_space N2, measurable_sets N2) ==>
    indep_var p N1 (Y1 o X1) N2 (Y2 o X2)``,
  RW_TAC std_ss [indep_var] THEN
  Q.ABBREV_TAC `Y = (\i:num. if i = 0 then Y1 else Y2)` THEN
  Q.ABBREV_TAC `X = (\i:num. if i = 0 then X1 else X2)` THEN
  Q_TAC SUFF_TAC `indep_vars p (\i. if i = 0 then N1 else N2) (\i. Y i o X i)
                   {x | (x = 0) \/ (x = 1)}` THENL
  [MATCH_MP_TAC EQ_IMPLIES THEN AP_THM_TAC THEN AP_TERM_TAC THEN
   METIS_TAC [o_DEF], ALL_TAC] THEN
  MATCH_MP_TAC indep_vars_compose THEN Q.EXISTS_TAC `(\i. if i = 0 then M1 else M2)` THEN
  METIS_TAC []);

val measurable_sigma_sets = store_thm ("measurable_sigma_sets",
  ``!M N f sp A. measure_space M /\ measure_space N /\
     (measurable_sets N = sigma_sets sp A) /\ A SUBSET POW sp /\
     f IN (m_space M -> sp) /\
     (!y. y IN A ==> PREIMAGE f y INTER m_space M IN measurable_sets M) ==>
     f IN measurable (m_space M, measurable_sets M)
                     (m_space N, measurable_sets N)``,
  RW_TAC std_ss [] THEN
  `sigma_algebra (sp, sigma_sets sp A)` by METIS_TAC [sigma_algebra_sigma_sets] THEN
  Q_TAC SUFF_TAC `sp = m_space N` THENL
  [DISCH_TAC,
   Q.ABBREV_TAC `m = (sp, sigma_sets sp A, (\x:'b->bool. 0))` THEN
   `sp = m_space m` by METIS_TAC [m_space_def] THEN
   ASM_SIMP_TAC std_ss [] THEN MATCH_MP_TAC sets_eq_imp_space_eq THEN
   Q.UNABBREV_TAC `m` THEN ASM_SIMP_TAC std_ss [measurable_sets_def] THEN
   ASM_SIMP_TAC std_ss [measure_space_def, m_space_def, measurable_sets_def] THEN
   SIMP_TAC std_ss [positive_def, measure_def, measurable_sets_def, le_refl] THEN
   SIMP_TAC std_ss [countably_additive_alt_eq, o_DEF, suminf_0]] THEN
  RW_TAC std_ss [IN_MEASURABLE] THENL
  [METIS_TAC [measure_space_def],
   ASM_SIMP_TAC std_ss [space_def],
   ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN SIMP_TAC std_ss [space_def, subsets_def, SPECIFICATION] THEN
  Q_TAC SUFF_TAC `sigma_sets (m_space N) A s ==>
   (\s. measurable_sets M (PREIMAGE f s INTER m_space M)) s` THENL
  [SIMP_TAC std_ss [], ALL_TAC] THEN
  MATCH_MP_TAC sigma_sets_ind THEN RW_TAC std_ss [] THENL
  [ONCE_REWRITE_TAC [GSYM SPECIFICATION] THEN
   SIMP_TAC std_ss [PREIMAGE_EMPTY, INTER_EMPTY] THEN
   ASM_SIMP_TAC std_ss [MEASURE_SPACE_EMPTY_MEASURABLE],
   ONCE_REWRITE_TAC [GSYM SPECIFICATION] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   ASM_SIMP_TAC std_ss [SPECIFICATION],
   POP_ASSUM (ASSUME_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION]) THEN
   ONCE_REWRITE_TAC [GSYM SPECIFICATION] THEN
   Q_TAC SUFF_TAC `PREIMAGE f (m_space N) INTER m_space M = m_space M` THENL
   [DISCH_TAC,
    FULL_SIMP_TAC std_ss [IN_FUNSET, PREIMAGE_def] THEN ASM_SET_TAC []] THEN
   SIMP_TAC std_ss [PREIMAGE_DIFF] THEN
   ONCE_REWRITE_TAC [SET_RULE ``(a DIFF b) INTER m = (a INTER m) DIFF (b INTER m)``] THEN
   MATCH_MP_TAC MEASURE_SPACE_DIFF THEN ASM_SIMP_TAC std_ss [] THEN
   METIS_TAC [MEASURE_SPACE_MSPACE_MEASURABLE],
   ALL_TAC] THEN
  ONCE_REWRITE_TAC [GSYM SPECIFICATION] THEN POP_ASSUM MP_TAC THEN
  GEN_REWR_TAC (LAND_CONV o QUANT_CONV) [GSYM SPECIFICATION] THEN
  DISCH_TAC THEN SIMP_TAC std_ss [PREIMAGE_BIGUNION] THEN
  Q_TAC SUFF_TAC `(IMAGE (PREIMAGE f) {A' i | i IN univ(:num)}) =
                  (IMAGE (\i. PREIMAGE f (A' i)) UNIV)` THENL
  [DISC_RW_KILL,
   SIMP_TAC std_ss [IMAGE_DEF, PREIMAGE_def] THEN ASM_SET_TAC []] THEN
  SIMP_TAC std_ss [INTER_BIGUNION, GSYM IMAGE_DEF] THEN
  Q_TAC SUFF_TAC `(IMAGE (\x. x INTER m_space M)
     (IMAGE (\i. PREIMAGE f (A' i)) univ(:num))) =
     (IMAGE (\x. PREIMAGE f (A' x) INTER m_space M) univ(:num))` THENL
  [DISC_RW_KILL,
   SIMP_TAC std_ss [IMAGE_DEF, PREIMAGE_def] THEN ASM_SET_TAC []] THEN
  MATCH_MP_TAC MEASURE_SPACE_BIGUNION THEN ASM_SIMP_TAC std_ss []);

val measurable_measure_of = store_thm ("measurable_measure_of",
  ``!sp N mu f M. measure_space M /\
     N SUBSET POW sp /\ f IN (m_space M -> sp) /\
     (!y. y IN N ==> PREIMAGE f y INTER m_space M IN measurable_sets M) ==>
     f IN measurable (m_space M, measurable_sets M)
                     (m_space (measure_of (sp,N,mu)), measurable_sets (measure_of (sp,N,mu)))``,
  RW_TAC std_ss [] THEN MATCH_MP_TAC measurable_sigma_sets THEN
  Q.EXISTS_TAC `sp` THEN Q.EXISTS_TAC `N` THEN
  ASM_SIMP_TAC std_ss [] THEN CONJ_TAC THENL
  [ALL_TAC, ASM_SIMP_TAC std_ss [measure_of, measurable_sets_def]] THEN
  RW_TAC std_ss [measure_space_def] THENL
  [ASM_SIMP_TAC std_ss [measurable_sets_def, measure_of, m_space_def] THEN
   METIS_TAC [sigma_algebra_sigma_sets],
   RW_TAC std_ss [positive_def, measure_of, measure_def, measurable_sets_def] THENL
   [METIS_TAC [measure_space_def, positive_def, measure_def],
    METIS_TAC [measure_space_def, positive_def, measure_def, measurable_sets_def],
    ALL_TAC] THEN
   COND_CASES_TAC THEN SIMP_TAC std_ss [le_refl] THEN
   METIS_TAC [measure_space_def, positive_def, measure_def, measurable_sets_def],
   ALL_TAC] THEN
  FULL_SIMP_TAC std_ss [countably_additive_def, measurable_sets_def, measure_def, measure_of] THEN
  RW_TAC std_ss [o_DEF, suminf_0] THEN FULL_SIMP_TAC std_ss [o_DEF, IN_FUNSET, IN_UNIV] THEN
  FULL_SIMP_TAC std_ss [measure_space_def, countably_additive_def, m_space_def,
                        measurable_sets_def, measure_def, o_DEF] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN FULL_SIMP_TAC std_ss [o_DEF, IN_FUNSET, IN_UNIV]);

val measurable_pair_measureI = store_thm ("measurable_pair_measureI",
  ``!f M M1 M2. measure_space M /\ measure_space M1 /\ measure_space M2 /\
     f IN (m_space M -> m_space M1 CROSS m_space M2) /\
     (!A B. A IN measurable_sets M1 /\ B IN measurable_sets M2 ==>
      PREIMAGE f (A CROSS B) INTER m_space M IN measurable_sets M) ==>
     f IN measurable (m_space M, measurable_sets M)
         (m_space (pair_measure M1 M2), measurable_sets (pair_measure M1 M2))``,
  RW_TAC std_ss [pair_measure] THEN MATCH_MP_TAC measurable_measure_of THEN
  ASM_SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD, POW_DEF] THEN
  RW_TAC std_ss [] THENL [ALL_TAC, METIS_TAC []] THEN
  FULL_SIMP_TAC std_ss [IN_FUNSET, SUBSET_DEF, GSPECIFICATION, EXISTS_PROD, CROSS_DEF] THEN
  RW_TAC std_ss [] THEN FULL_SIMP_TAC std_ss [IN_FUNSET, GSPECIFICATION, EXISTS_PROD] THEN
  `p_1 SUBSET m_space M1` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
  `p_2 SUBSET m_space M2` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
  ASM_SET_TAC []);

val measurable_Pair = store_thm ("measurable_Pair",
  ``!f g M M1 M2.
     measure_space M /\ measure_space M1 /\ measure_space M2 /\
     f IN measurable (m_space M, measurable_sets M) (m_space M1, measurable_sets M1) /\
     g IN measurable (m_space M, measurable_sets M) (m_space M2, measurable_sets M2) ==>
     (\x. (f x, g x)) IN measurable (m_space M, measurable_sets M)
         (m_space (pair_measure M1 M2), measurable_sets (pair_measure M1 M2))``,
  RW_TAC std_ss [] THEN MATCH_MP_TAC measurable_pair_measureI THEN
  FULL_SIMP_TAC std_ss [IN_MEASURABLE, IN_FUNSET, space_def, subsets_def] THEN
  CONJ_TAC THENL [RW_TAC std_ss [CROSS_DEF, GSPECIFICATION, EXISTS_PROD], ALL_TAC] THEN
  RW_TAC std_ss [] THEN
  Q_TAC SUFF_TAC `PREIMAGE (\x. (f x,g x)) (A CROSS B) INTER m_space M =
    (PREIMAGE f A INTER m_space M) INTER (PREIMAGE g B INTER m_space M)` THENL
  [DISC_RW_KILL,
   SIMP_TAC std_ss [PREIMAGE_def, CROSS_DEF, GSPECIFICATION, EXISTS_PROD] THEN
   SET_TAC []] THEN
  MATCH_MP_TAC MEASURE_SPACE_INTER THEN ASM_SIMP_TAC std_ss []);

val indep_var_rv = store_thm ("indep_var_rv",
  ``!p M1 X M2 Y. indep_var p M1 X M2 Y ==>
      random_variable X p (m_space M1, measurable_sets M1) /\
      random_variable Y p (m_space M2, measurable_sets M2)``,
  RW_TAC std_ss [indep_var, indep_vars, GSPECIFICATION] THENL
  [ASM_SET_TAC [], ALL_TAC] THEN FIRST_X_ASSUM (MP_TAC o Q.SPEC `1`) THEN
  ASM_SIMP_TAC arith_ss []);

val indep_varsD = store_thm ("indep_varsD",
  ``!p M X ii A J. prob_space p /\ indep_vars p M X ii /\
             J <> {} /\ FINITE J /\ J SUBSET ii /\
             (!i. i IN J ==> A i IN measurable_sets (M i)) ==>
             (prob p (BIGINTER {PREIMAGE (X i) (A i) INTER p_space p | i IN J}) =
             Normal (product J (\i. real (prob p (PREIMAGE (X i) (A i) INTER p_space p)))))``,
  RW_TAC std_ss [] THEN
  ONCE_REWRITE_TAC [METIS [] ``PREIMAGE (X i) (A i) INTER p_space p =
                          (\i. PREIMAGE (X i) (A i) INTER p_space p) i``] THEN
  MATCH_MP_TAC indep_setsD THEN FULL_SIMP_TAC std_ss [indep_vars] THEN
  Q.EXISTS_TAC `(\i. {PREIMAGE f A INTER p_space p |
            (f = X i) /\ A IN measurable_sets (M i)})` THEN
  Q.EXISTS_TAC `ii` THEN ASM_SIMP_TAC std_ss [] THEN ASM_SET_TAC []);

val sigma_finite_incseq = store_thm ("sigma_finite_incseq",
  ``!M. measure_space M /\ sigma_finite_measure M ==>
     ?A. IMAGE A univ(:num) SUBSET measurable_sets M /\
         (BIGUNION {A i | i IN univ(:num)} = m_space M) /\
         !i. measure M (A i) <> PosInf /\
         !n. A n SUBSET A (SUC n)``,
  RW_TAC std_ss [] THEN
  `?f. IMAGE f univ(:num) SUBSET measurable_sets M /\
      (BIGUNION {f i | i IN univ(:num)} = m_space M) /\
      !i. measure M (f i) <> PosInf` by METIS_TAC [sigma_finite] THEN
  `BIGUNION {BIGUNION {f i | i IN {x | 0 <= x /\ x < n}} | n IN univ(:num)} =
   m_space M` by METIS_TAC [UN_UN_finite_eq] THEN
  Q.EXISTS_TAC `(\n. BIGUNION {f i | i IN {x | 0 <= x /\ x < n}})` THEN
  ASM_SIMP_TAC std_ss [] THEN RW_TAC std_ss [] THENL
  [ALL_TAC, ASM_SET_TAC [],
   `measure M (BIGUNION {f n | n IN {x | 0 <= x /\ x < i}}) <=
   SIGMA (\n. measure M (f n)) {x | 0 <= x /\ x < i}` by
   (MATCH_MP_TAC measure_subadditive_finite THEN
    ASM_SIMP_TAC std_ss [FINITE_COUNT, GSYM count_def] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN Q.EXISTS_TAC `IMAGE f UNIV` THEN
    ASM_SIMP_TAC std_ss [IMAGE_SUBSET, SUBSET_UNIV]) THEN
   `SIGMA (\n. measure M (f n)) {x | 0 <= x /\ x < i} <> PosInf` by
   (MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_POS_INF THEN
    ASM_SIMP_TAC std_ss [FINITE_COUNT, GSYM count_def]) THEN
   FULL_SIMP_TAC arith_ss [lt_infty, GSPECIFICATION] THEN
   METIS_TAC [let_trans],
   MATCH_MP_TAC SUBSET_BIGUNION THEN
   SIMP_TAC arith_ss [GSYM IMAGE_DEF] THEN
   MATCH_MP_TAC IMAGE_SUBSET THEN
   SIMP_TAC arith_ss [SUBSET_DEF, GSPECIFICATION]] THEN
  `m_space M IN measurable_sets M` by METIS_TAC [MEASURE_SPACE_MSPACE_MEASURABLE] THEN
  RW_TAC arith_ss [GSPECIFICATION, SUBSET_DEF, IN_IMAGE] THEN
  FULL_SIMP_TAC arith_ss [measure_space_def, sigma_algebra_def, space_def, subsets_def] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL [ALL_TAC, ASM_SET_TAC []] THEN
  Q_TAC SUFF_TAC `countable {f i | i IN {x | x < n}}` THENL
  [SIMP_TAC std_ss [GSPECIFICATION], ALL_TAC] THEN
  SIMP_TAC std_ss [GSYM IMAGE_DEF] THEN
  MATCH_MP_TAC pred_setTheory.image_countable THEN
  SIMP_TAC std_ss [COUNTABLE_COUNT, GSYM count_def]);

val incseq_imp = store_thm ("incseq_imp",
  ``!f. (!i. f i SUBSET f (SUC i)) ==>
        (!m n. m <= n ==> f m SUBSET f n)``,
  RW_TAC std_ss [] THEN Induct_on `n` THEN
  ASM_SIMP_TAC arith_ss [SUBSET_REFL] THEN
  RW_TAC std_ss [] THEN ASM_CASES_TAC ``m = n:num`` THEN
  ASM_SIMP_TAC std_ss [] THEN
  ASM_CASES_TAC ``m = SUC n`` THEN
  ASM_SIMP_TAC std_ss [SUBSET_REFL] THEN
  `m <= n` by ASM_SIMP_TAC arith_ss [] THEN
  METIS_TAC [SUBSET_TRANS]);

val sigma_finite_up_in_pair_measure_generator = store_thm ("sigma_finite_up_in_pair_measure_generator",
  ``!M1 M2. measure_space M1 /\ measure_space M2 /\
      sigma_finite_measure M1 /\ sigma_finite_measure M2 ==>
    (E = {A CROSS B | A IN measurable_sets M1 /\ B IN measurable_sets M2}) ==>
    ?f. IMAGE f univ(:num) SUBSET E /\
        (BIGUNION {f i | i IN UNIV} = m_space M1 CROSS m_space M2) /\
        (!i. measure (pair_measure M1 M2) (f i) <> PosInf)``,
  RW_TAC std_ss [] THEN
  `?f1. IMAGE f1 univ(:num) SUBSET measurable_sets M1 /\
       (BIGUNION {f1 i | i IN univ(:num)} = m_space M1) /\
       (!i. measure M1 (f1 i) <> PosInf) /\
       !n. f1 n SUBSET f1 (SUC n)` by METIS_TAC [sigma_finite_incseq] THEN
  `?f2. IMAGE f2 univ(:num) SUBSET measurable_sets M2 /\
       (BIGUNION {f2 i | i IN univ(:num)} = m_space M2) /\
       (!i. measure M2 (f2 i) <> PosInf) /\
       !n. f2 n SUBSET f2 (SUC n)` by METIS_TAC [sigma_finite_incseq] THEN
  RULE_ASSUM_TAC (ONCE_REWRITE_RULE [EQ_SYM_EQ]) THEN
  Q.EXISTS_TAC `(\i. f1 i CROSS f2 i)` THEN RW_TAC std_ss [] THENL
  [FULL_SIMP_TAC std_ss [SUBSET_DEF, IMAGE_DEF, CROSS_DEF, GSPECIFICATION, EXISTS_PROD] THEN
   FULL_SIMP_TAC std_ss [IN_UNIV] THEN METIS_TAC [],
   MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [SIMP_TAC std_ss [BIGUNION, GSPECIFICATION, CROSS_DEF, EXISTS_PROD] THEN
    ASM_SET_TAC [], ALL_TAC] THEN
   RW_TAC std_ss [SUBSET_DEF, CROSS_DEF, IN_BIGUNION, EXISTS_PROD] THEN
   FULL_SIMP_TAC std_ss [GSPECIFICATION] THEN
   Q_TAC SUFF_TAC `FST x IN f1 (MAX i i')` THENL
   [DISCH_TAC,
    `!m n. m <= n ==> f1 m SUBSET f1 n` by METIS_TAC [incseq_imp] THEN
    POP_ASSUM (MP_TAC o Q.SPECL [`i`,`MAX i i'`]) THEN
    SIMP_TAC arith_ss [] THEN ASM_SET_TAC []] THEN
   Q_TAC SUFF_TAC `SND x IN f2 (MAX i i')` THENL
   [DISCH_TAC,
    `!m n. m <= n ==> f2 m SUBSET f2 n` by METIS_TAC [incseq_imp] THEN
    POP_ASSUM (MP_TAC o Q.SPECL [`i'`,`MAX i i'`]) THEN
    SIMP_TAC arith_ss [] THEN ASM_SET_TAC []] THEN
   Q.EXISTS_TAC `f1 (MAX i i') CROSS f2 (MAX i i')` THEN CONJ_TAC THENL
   [ASM_SIMP_TAC std_ss [CROSS_DEF, GSPECIFICATION, EXISTS_PROD] THEN
    `?a b. x = (a,b)` by METIS_TAC [pair_CASES] THEN
    FULL_SIMP_TAC std_ss [FST, SND], ALL_TAC] THEN
   Q.EXISTS_TAC `MAX i i'` THEN `?a b. x = (a,b)` by METIS_TAC [pair_CASES] THEN
   FULL_SIMP_TAC std_ss [FST, SND, CROSS_DEF, GSPECIFICATION, EXISTS_PROD] THEN
   SIMP_TAC std_ss [IN_UNIV],
   ALL_TAC] THEN
  RW_TAC std_ss [pair_measure, measure_of, measure_def, num_not_infty] THEN
  Q_TAC SUFF_TAC `!x y. indicator_fn (f1 i CROSS f2 i) (x,y) =
                        indicator_fn (PREIMAGE (\y. (x,y)) (f1 i CROSS f2 i)) y` THENL
  [DISCH_TAC, SIMP_TAC std_ss [indicator_fn_def, IN_PREIMAGE]] THEN
  ASM_SIMP_TAC std_ss [] THEN
  Q_TAC SUFF_TAC `!x. pos_fn_integral M2
       (\y. indicator_fn (PREIMAGE (\y. (x,y)) (f1 i CROSS f2 i)) y) =
   measure M2 (PREIMAGE (\y. (x,y)) (f1 i CROSS f2 i))` THENL
  [DISCH_TAC,
   ONCE_REWRITE_TAC [METIS [] ``!s. (\y. indicator_fn s y) = indicator_fn s``] THEN
   GEN_TAC THEN MATCH_MP_TAC pos_fn_integral_indicator THEN
   ASM_SIMP_TAC std_ss [PREIMAGE_def, CROSS_DEF, GSPECIFICATION, EXISTS_PROD] THEN
   ASM_CASES_TAC ``x IN f1 (i:num)`` THENL
   [ASM_SIMP_TAC std_ss [] THEN ONCE_REWRITE_TAC [SET_RULE ``{x | x IN s} = s``] THEN
    ASM_SET_TAC [], ALL_TAC] THEN
   ASM_SIMP_TAC std_ss [GSPEC_F] THEN METIS_TAC [measure_space_def, sigma_algebra_iff2]] THEN
  ASM_SIMP_TAC std_ss [PREIMAGE_def, CROSS_DEF, GSPECIFICATION, EXISTS_PROD] THEN
  Q_TAC SUFF_TAC `!x. measure M2 {y | x IN f1 i /\ y IN f2 i} =
                      measure M2 (f2 i) * indicator_fn (f1 i) x` THENL
  [DISCH_TAC THEN ASM_SIMP_TAC std_ss [],
   GEN_TAC THEN ASM_CASES_TAC ``x IN (f1 (i:num))`` THENL
   [ASM_SIMP_TAC std_ss [indicator_fn_def, mul_rone] THEN
    AP_TERM_TAC THEN SET_TAC [], ALL_TAC] THEN
   ASM_SIMP_TAC std_ss [indicator_fn_def, mul_rzero, GSPEC_F] THEN
   METIS_TAC [measure_space_def, positive_def]] THEN
  Q_TAC SUFF_TAC
  `pos_fn_integral M1 (\x. max 0 (measure M2 (f2 i) * indicator_fn (f1 i) x)) =
   measure M2 (f2 i) * pos_fn_integral M1 (\x. max 0 (indicator_fn (f1 i) x))` THENL
  [ALL_TAC,
   MATCH_MP_TAC pos_fn_integral_cmult THEN ASM_SIMP_TAC std_ss [] THEN
   CONJ_TAC THENL
   [FULL_SIMP_TAC std_ss [measure_space_def, positive_def] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SET_TAC [], ALL_TAC] THEN
   RULE_ASSUM_TAC (ONCE_REWRITE_RULE [EQ_SYM_EQ]) THEN ASM_SIMP_TAC std_ss [] THEN
   MATCH_MP_TAC IN_MEASURABLE_BOREL_INDICATOR THEN
   Q.EXISTS_TAC `f1 i` THEN FULL_SIMP_TAC std_ss [measure_space_def] THEN
   ASM_SET_TAC [subsets_def]] THEN
  `0 <= measure M2 (f2 i)` by (FULL_SIMP_TAC std_ss [measure_space_def, positive_def] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SET_TAC []) THEN
  ASM_SIMP_TAC std_ss [extreal_max_def, le_mul, indicator_fn_pos_le] THEN
  `(f1 i) IN measurable_sets M1` by ASM_SET_TAC [] THEN
  ONCE_REWRITE_TAC [METIS [] ``!s. (\y. indicator_fn s y) = indicator_fn s``] THEN
  DISCH_TAC THEN ASM_SIMP_TAC std_ss [pos_fn_integral_indicator] THEN
  SIMP_TAC std_ss [lt_infty] THEN
  ONCE_REWRITE_TAC [METIS [extreal_mul_def] ``PosInf = PosInf * PosInf``] THEN
  MATCH_MP_TAC lt_mul2 THEN
  `(f2 i) IN measurable_sets M2` by ASM_SET_TAC [] THEN
  `0 <= measure M2 (f2 i) /\ 0 <= measure M1 (f1 i)` by
   METIS_TAC [measure_space_def, positive_def] THEN
  ASM_SIMP_TAC std_ss [GSYM lt_infty]);

val Int_stable_pair_measure_generator = store_thm ("Int_stable_pair_measure_generator",
  ``!M N. measure_space M /\ measure_space N ==> Int_stable
    {a CROSS b | a IN measurable_sets N /\ b IN measurable_sets M}``,
  RW_TAC std_ss [Int_stable, GSPECIFICATION, EXISTS_PROD] THEN
  Q.EXISTS_TAC `p_1 INTER p_1'` THEN Q.EXISTS_TAC `p_2 INTER p_2'` THEN
  SIMP_TAC std_ss [CROSS_DEF, INTER_DEF] THEN CONJ_TAC THENL
  [ASM_SET_TAC [], ALL_TAC] THEN SIMP_TAC std_ss [GSYM INTER_DEF] THEN
  CONJ_TAC THEN (MATCH_MP_TAC MEASURE_SPACE_INTER) THEN METIS_TAC []);

val finite_measure_cut_measurable = store_thm ("finite_measure_cut_measurable",
  ``!M N Q. measure_space M /\ measure_space N /\ finite_measure M /\
        Q IN measurable_sets (pair_measure N M) ==>
        (\x. measure M (\y. (x,y) IN Q)) IN measurable (m_space N, measurable_sets N) Borel``,
  RW_TAC std_ss [] THEN POP_ASSUM MP_TAC THEN
  SIMP_TAC std_ss [pair_measure, measure_of, measurable_sets_def] THEN
  Q_TAC SUFF_TAC `{a CROSS b | a IN measurable_sets N /\ b IN measurable_sets M}
                  SUBSET POW (m_space N CROSS m_space M)` THENL
  [DISCH_TAC THEN ASM_SIMP_TAC std_ss [],
   SIMP_TAC std_ss [CROSS_DEF, SUBSET_DEF, POW_DEF, GSPECIFICATION, EXISTS_PROD] THEN
   RW_TAC std_ss [] THEN FULL_SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD] THEN
   `p_1 SUBSET m_space N` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
   `p_2 SUBSET m_space M` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
   ASM_SET_TAC []] THEN DISCH_TAC THEN
  Q_TAC SUFF_TAC `(\Q. (\x. measure M (\y. (x,y) IN Q)) IN
        measurable (m_space N,measurable_sets N) Borel) Q` THENL
  [SIMP_TAC std_ss [SPECIFICATION], ALL_TAC] THEN
  MATCH_MP_TAC sigma_sets_induct_disjoint' THEN
  Q.EXISTS_TAC `{a CROSS b | a IN measurable_sets N /\ b IN measurable_sets M}` THEN
  Q.EXISTS_TAC `(m_space N CROSS m_space M)` THEN ASM_SIMP_TAC std_ss [] THEN
  ASM_SIMP_TAC std_ss [Int_stable_pair_measure_generator] THEN
  CONJ_TAC THENL
  [RW_TAC std_ss [CROSS_DEF, GSPECIFICATION, EXISTS_PROD] THEN
   SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD] THEN
   ONCE_REWRITE_TAC [SET_RULE
    ``!x. (\y. x IN p_1 /\ y IN p_2) = {y | x IN p_1 /\ y IN p_2}``] THEN
   Q_TAC SUFF_TAC `!x. measure M {y | x IN p_1 /\ y IN p_2} =
                       measure M p_2 * indicator_fn p_1 x` THENL
   [DISCH_TAC THEN ASM_SIMP_TAC std_ss [],
    GEN_TAC THEN ASM_CASES_TAC ``x:'b IN p_1`` THENL
    [ASM_SIMP_TAC std_ss [indicator_fn_def, mul_rone] THEN
      AP_TERM_TAC THEN SET_TAC [], ALL_TAC] THEN
    ASM_SIMP_TAC std_ss [indicator_fn_def, mul_rzero, GSPEC_F] THEN
    METIS_TAC [measure_space_def, positive_def]] THEN
   MATCH_MP_TAC IN_MEASURABLE_BOREL_TIMES THEN
   Q.EXISTS_TAC `(\x. measure M p_2)` THEN Q.EXISTS_TAC `indicator_fn p_1` THEN
   ASM_SIMP_TAC std_ss [] THEN CONJ_TAC THENL
   [MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST THEN
    METIS_TAC [measure_space_def], ALL_TAC] THEN
   MATCH_MP_TAC IN_MEASURABLE_BOREL_INDICATOR THEN
   Q.EXISTS_TAC `p_1` THEN ASM_SIMP_TAC std_ss [space_def, subsets_def] THEN
   METIS_TAC [measure_space_def],
   ALL_TAC] THEN
  CONJ_TAC THENL
  [SIMP_TAC std_ss [NOT_IN_EMPTY, SET_RULE ``(\x. F) = {}``] THEN
   `measure M {} = 0` by METIS_TAC [measure_space_def, positive_def] THEN
   ASM_SIMP_TAC std_ss [] THEN MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST THEN
   METIS_TAC [measure_space_def], ALL_TAC] THEN
  Q_TAC SUFF_TAC `!x A. A IN sigma_sets (m_space N CROSS m_space M)
     {a CROSS b | a IN measurable_sets N /\ b IN measurable_sets M} ==>
     (\y. (x,y) IN A) IN measurable_sets M` THENL
  [DISCH_TAC,
   GEN_TAC THEN GEN_TAC THEN
   Q_TAC SUFF_TAC `sigma_sets (m_space N CROSS m_space M)
    {a CROSS b | a IN measurable_sets N /\ b IN measurable_sets M} A ==>
    (\z. (\y. (x,y) IN z) IN measurable_sets M) A` THENL
   [SIMP_TAC std_ss [SPECIFICATION], ALL_TAC] THEN
   MATCH_MP_TAC sigma_sets_ind THEN RW_TAC std_ss [] THENL
   [SIMP_TAC std_ss [NOT_IN_EMPTY, SET_RULE ``(\x. F) = {}``] THEN
    METIS_TAC [MEASURE_SPACE_EMPTY_MEASURABLE],
    POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION]) THEN
    RW_TAC std_ss [CROSS_DEF, GSPECIFICATION, EXISTS_PROD] THEN
    SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD] THEN
    ASM_CASES_TAC ``x:'b IN p_1`` THENL
    [ASM_SIMP_TAC std_ss [] THEN
     ASM_SIMP_TAC std_ss [MEASURE_SPACE_MSPACE_MEASURABLE,
      SET_RULE ``(\x. x IN s) = s``], ALL_TAC] THEN
    ASM_SIMP_TAC std_ss [SET_RULE ``(\x. F) = {}``] THEN
    ASM_SIMP_TAC std_ss [MEASURE_SPACE_EMPTY_MEASURABLE],
    Q_TAC SUFF_TAC `(\y. (x,y) IN m_space N CROSS m_space M DIFF a) =
         if x IN m_space N then m_space M DIFF (\y. (x,y) IN a) else {}` THENL
    [DISCH_TAC THEN ASM_SIMP_TAC std_ss [],
     ASM_SIMP_TAC std_ss [CROSS_DEF, INTER_DEF, DIFF_DEF] THEN
     ASM_SIMP_TAC std_ss [EXTENSION, GSPECIFICATION, EXISTS_PROD] THEN
     ASM_SET_TAC []] THEN
    `{} IN measurable_sets M` by METIS_TAC [MEASURE_SPACE_EMPTY_MEASURABLE] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC std_ss [] THEN
    MATCH_MP_TAC MEASURE_SPACE_DIFF THEN
    ASM_SIMP_TAC std_ss [MEASURE_SPACE_MSPACE_MEASURABLE],
    ALL_TAC] THEN
   Q_TAC SUFF_TAC `(\y. (x,y) IN BIGUNION {A i | i IN univ(:num)}) =
      BIGUNION {(\y. (x,y) IN A i) | i IN UNIV}` THENL
   [DISC_RW_KILL,
    SIMP_TAC std_ss [EXTENSION, IN_BIGUNION, IN_INTER, GSPECIFICATION, EXISTS_PROD] THEN
    GEN_TAC THEN EQ_TAC THEN RW_TAC std_ss [] THEN TRY (ASM_SET_TAC []) THEN
    POP_ASSUM (MP_TAC o SIMP_RULE std_ss [IN_DEF]) THEN
    RW_TAC std_ss [] THEN Q.EXISTS_TAC `(\x'. A i (x, x'))` THEN
    CONJ_TAC THENL [ASM_SET_TAC [], ALL_TAC] THEN SET_TAC []] THEN
   SIMP_TAC std_ss [GSYM IMAGE_DEF] THEN MATCH_MP_TAC MEASURE_SPACE_BIGUNION THEN
   ASM_SIMP_TAC std_ss []] THEN
  CONJ_TAC THENL
  [RW_TAC std_ss [] THEN
   `(\y. (x,y) IN A) IN measurable_sets M` by METIS_TAC [] THEN
   Q_TAC SUFF_TAC `!x. measure M (\y. (x,y) IN m_space N CROSS m_space M DIFF A) =
     if x IN m_space N then measure M (m_space M) -
             measure M ((\y. (x,y) IN A)) else 0` THENL
   [DISC_RW_KILL,
    RW_TAC std_ss [CROSS_DEF, GSPECIFICATION, EXISTS_PROD, IN_DIFF] THENL
    [ALL_TAC, SIMP_TAC std_ss [SET_RULE ``(\x. F) = {}``] THEN
     METIS_TAC [measure_space_def, positive_def]] THEN
    Q_TAC SUFF_TAC `(\y. y IN m_space M /\ (x',y) NOTIN A) =
        m_space M DIFF ((\y. (x',y) IN A))` THENL
    [DISC_RW_KILL, SET_TAC []] THEN
    MATCH_MP_TAC MEASURE_SPACE_FINITE_DIFF THEN ASM_SIMP_TAC std_ss [] THEN
    FULL_SIMP_TAC std_ss [lt_infty, finite_measure] THEN
    MATCH_MP_TAC let_trans THEN Q.EXISTS_TAC `measure M (m_space M)` THEN
    ASM_SIMP_TAC std_ss [] THEN MATCH_MP_TAC INCREASING THEN
    ASM_SIMP_TAC std_ss [MEASURE_SPACE_INCREASING] THEN
    ASM_SIMP_TAC std_ss [MEASURE_SPACE_MSPACE_MEASURABLE] THEN
    METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE]] THEN
   Q_TAC SUFF_TAC `(\x. if (\x. x IN m_space N) x then
     (\x. measure M (m_space M) - measure M (\y. (x,y) IN A)) x
    else (\x. 0) x) IN measurable (m_space N,measurable_sets N)
     (m_space (space Borel, subsets Borel, (\x. 0)),
      measurable_sets (space Borel, subsets Borel, (\x. 0)))` THENL
   [SIMP_TAC std_ss [SPECIFICATION, m_space_def, measurable_sets_def, SPACE],
    ALL_TAC] THEN
   MATCH_MP_TAC measurable_If THEN
   SIMP_TAC std_ss [m_space_def, measurable_sets_def, SPACE] THEN
   ASM_SIMP_TAC std_ss [SET_RULE ``{x | x IN s} = s``] THEN
   ASM_SIMP_TAC std_ss [MEASURE_SPACE_MSPACE_MEASURABLE] THEN
   CONJ_TAC THENL
   [ALL_TAC,
    MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST THEN
    METIS_TAC [measure_space_def]] THEN
   MATCH_MP_TAC IN_MEASURABLE_BOREL_SUB THEN
   Q.EXISTS_TAC `(\x. measure M (m_space M))` THEN
   Q.EXISTS_TAC `(\x. measure M (\y. (x,y) IN A))` THEN
   ASM_SIMP_TAC std_ss [space_def] THEN
   CONJ_TAC THENL [METIS_TAC [measure_space_def], ALL_TAC] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST THEN
    METIS_TAC [measure_space_def], ALL_TAC] THEN
   FULL_SIMP_TAC std_ss [finite_measure] THEN RW_TAC std_ss [] THENL
   [SIMP_TAC std_ss [lt_infty] THEN
    `m_space M IN measurable_sets M` by METIS_TAC [MEASURE_SPACE_MSPACE_MEASURABLE] THEN
    MATCH_MP_TAC lte_trans THEN Q.EXISTS_TAC `0` THEN
    SIMP_TAC std_ss [GSYM lt_infty, num_not_infty] THEN
    METIS_TAC [measure_space_def, positive_def],
    ALL_TAC] THEN
   `(\y. (x',y) IN A) SUBSET m_space M` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
   SIMP_TAC std_ss [lt_infty] THEN MATCH_MP_TAC let_trans THEN
   Q.EXISTS_TAC `measure M (m_space M)` THEN ASM_SIMP_TAC std_ss [] THEN
   ASM_SIMP_TAC std_ss [GSYM lt_infty] THEN MATCH_MP_TAC INCREASING THEN
   ASM_SIMP_TAC std_ss [MEASURE_SPACE_INCREASING] THEN
   ASM_SIMP_TAC std_ss [MEASURE_SPACE_MSPACE_MEASURABLE],
   ALL_TAC] THEN
  RW_TAC std_ss [] THEN
  Q_TAC SUFF_TAC `!x. measure M (\y. (x,y) IN BIGUNION (IMAGE A univ(:num))) =
    suminf (\i. measure M (\y. (x,y) IN A i))` THENL
  [DISC_RW_KILL,
   GEN_TAC THEN
   Q_TAC SUFF_TAC `(\y. (x,y) IN BIGUNION (IMAGE A univ(:num))) =
                   BIGUNION (IMAGE (\i y. (x,y) IN A i) univ(:num))` THENL
   [DISC_RW_KILL,
    SIMP_TAC std_ss [EXTENSION, BIGUNION, GSPECIFICATION, EXISTS_PROD, IN_IMAGE] THEN
    GEN_TAC THEN EQ_TAC THEN RW_TAC std_ss [IN_DEF] THEN TRY (ASM_SET_TAC []) THEN
    Q.EXISTS_TAC `(\y. (x,y) IN A x'')` THEN ASM_SET_TAC []] THEN
   Q_TAC SUFF_TAC `measure M (BIGUNION (IMAGE (\i. (\y. (x,y) IN A i)) univ(:num))) =
     suminf (\i. measure M ((\i. (\y. (x,y) IN A i)) i))` THENL
   [SIMP_TAC std_ss [], ALL_TAC] THEN
   MATCH_MP_TAC (GSYM (SIMP_RULE std_ss [GSYM IMAGE_DEF] suminf_measure)) THEN
   ASM_SIMP_TAC std_ss [] THEN RW_TAC std_ss [SUBSET_DEF, IN_IMAGE] THENL
   [ALL_TAC,
    FULL_SIMP_TAC std_ss [disjoint_family, disjoint_family_on, IN_UNIV] THEN
    RW_TAC std_ss [] THEN ASM_SET_TAC []] THEN
   POP_ASSUM K_TAC THEN POP_ASSUM MP_TAC THEN
   POP_ASSUM (fn th => DISCH_TAC THEN MP_TAC th) THEN
   SIMP_TAC std_ss [SUBSET_DEF] THEN DISCH_THEN (MP_TAC o Q.SPEC `A (i:num)`) THEN
   `A i IN IMAGE A UNIV` by ASM_SET_TAC [] THEN ASM_SIMP_TAC std_ss []] THEN
  SIMP_TAC std_ss [ext_suminf_def] THEN MATCH_MP_TAC IN_MEASURABLE_BOREL_MONO_SUP THEN
  Q.EXISTS_TAC `(\n x. SIGMA (\i. measure M (\y. (x,y) IN A i)) (count n))` THEN
  SIMP_TAC std_ss [] THEN CONJ_TAC THENL [METIS_TAC [measure_space_def], ALL_TAC] THEN
  CONJ_TAC THENL
  [GEN_TAC THEN Q.ABBREV_TAC `s = count n` THEN
   Q.ABBREV_TAC `f = (\i x. measure M (\y. (x,y) IN A i))` THEN
   Q_TAC SUFF_TAC ` FINITE s /\ sigma_algebra (m_space N,measurable_sets N) /\
    (!i. i IN s ==>
     f i IN measurable (m_space N,measurable_sets N) Borel) /\
    (!i x. i IN s /\ x IN space (m_space N,measurable_sets N) ==>
     f i x <> NegInf) /\
    !x. x IN space (m_space N,measurable_sets N) ==>
    ((\x. SIGMA (\i. measure M (\y. (x,y) IN A i)) (count n)) x =
     SIGMA (\i. f i x) s)` THENL
   [DISCH_THEN (MP_TAC o MATCH_MP IN_MEASURABLE_BOREL_SUM) THEN
    METIS_TAC [], ALL_TAC] THEN
   Q.UNABBREV_TAC `s` THEN Q.UNABBREV_TAC `f` THEN
   ASM_SIMP_TAC std_ss [FINITE_COUNT] THEN
   CONJ_TAC THENL [METIS_TAC [measure_space_def], ALL_TAC] THEN
   RW_TAC std_ss [space_def, lt_infty] THEN
   MATCH_MP_TAC lte_trans THEN Q.EXISTS_TAC `0` THEN
   SIMP_TAC std_ss [GSYM lt_infty, num_not_infty] THEN
   `A i IN sigma_sets (m_space N CROSS m_space M)
        {a CROSS b | a IN measurable_sets N /\ b IN measurable_sets M}` by
    ASM_SET_TAC [] THEN METIS_TAC [measure_space_def, positive_def],
   ALL_TAC] THEN
  RW_TAC std_ss [] THEN MATCH_MP_TAC EXTREAL_SUM_IMAGE_MONO_SET THEN
  SIMP_TAC std_ss [FINITE_COUNT] THEN CONJ_TAC THENL
  [SIMP_TAC arith_ss [count_def, SUBSET_DEF, GSPECIFICATION], ALL_TAC] THEN
  RW_TAC std_ss [] THEN
  `A x' IN sigma_sets (m_space N CROSS m_space M)
        {a CROSS b | a IN measurable_sets N /\ b IN measurable_sets M}` by
   ASM_SET_TAC [] THEN METIS_TAC [measure_space_def, positive_def]);

val measurable_measure_Pair = store_thm ("measurable_measure_Pair",
  ``!M N Q. measure_space M /\ measure_space N /\ sigma_finite_measure M /\
        Q IN measurable_sets (pair_measure N M) ==>
        (\x. measure M (\y. (x,y) IN Q)) IN measurable (m_space N, measurable_sets N) Borel``,
  RW_TAC std_ss [] THEN
  `?ff. IMAGE ff univ(:num) SUBSET measurable_sets M /\
       (BIGUNION {ff i | i IN univ(:num)} = m_space M) /\
       (!i. measure M (ff i) <> PosInf) /\ disjoint_family ff` by
    METIS_TAC [sigma_finite_disjoint] THEN
  `!i. ff i IN measurable_sets M` by ASM_SET_TAC [] THEN
  Q.ABBREV_TAC `C = (\x i. ff i INTER (\y. (x,y) IN Q))` THEN
  Q_TAC SUFF_TAC `!i. (m_space N CROSS ff i) INTER (m_space N CROSS m_space M) =
                      m_space N CROSS ff i` THENL
  [DISCH_TAC,
   GEN_TAC THEN `ff i SUBSET m_space M` by ASM_SET_TAC [] THEN
   SIMP_TAC std_ss [CROSS_DEF, INTER_DEF] THEN ASM_SET_TAC []] THEN
  Q_TAC SUFF_TAC `!i. finite_measure (density M (indicator_fn (ff i)))` THENL
  [DISCH_TAC,
   RW_TAC std_ss [finite_measure] THENL
   [ALL_TAC, SIMP_TAC std_ss [density, m_space_def] THEN
    SIMP_TAC std_ss [extreal_max_def, indicator_fn_pos_le, le_mul] THEN
    `m_space M IN measurable_sets M` by METIS_TAC [MEASURE_SPACE_MSPACE_MEASURABLE] THEN
    ASM_SIMP_TAC std_ss [measure_restricted] THEN
    `ff i SUBSET m_space M` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
    `ff i INTER m_space M = ff i` by ASM_SET_TAC [] THEN
    METIS_TAC [sigma_finite_measure]] THEN
   FULL_SIMP_TAC std_ss [sigma_finite_measure, density, m_space_def, measurable_sets_def] THEN
   SIMP_TAC std_ss [extreal_max_def, indicator_fn_pos_le, le_mul] THEN
   `m_space M IN measurable_sets M` by METIS_TAC [MEASURE_SPACE_MSPACE_MEASURABLE] THEN
   Q.EXISTS_TAC `A` THEN ASM_SIMP_TAC std_ss [] THEN RW_TAC std_ss [] THEN
   `a IN measurable_sets M` by ASM_SET_TAC [] THEN
   ASM_SIMP_TAC std_ss [measure_restricted, lt_infty] THEN
   MATCH_MP_TAC let_trans THEN Q.EXISTS_TAC `measure M a` THEN
   ASM_SIMP_TAC std_ss [GSYM lt_infty] THEN MATCH_MP_TAC INCREASING THEN
   ASM_SIMP_TAC std_ss [MEASURE_SPACE_INCREASING] THEN
   `ff i INTER a IN measurable_sets M` by METIS_TAC [MEASURE_SPACE_INTER] THEN
   ASM_SET_TAC []] THEN
  `!i. (indicator_fn (ff i)) IN measurable (m_space M, measurable_sets M) Borel` by
   (GEN_TAC THEN MATCH_MP_TAC IN_MEASURABLE_BOREL_INDICATOR THEN
    Q.EXISTS_TAC `ff i` THEN METIS_TAC [subsets_def, measure_space_def]) THEN
  `!i. measure_space (density M (indicator_fn (ff i)))` by
    METIS_TAC [measure_space_density] THEN

  Q_TAC SUFF_TAC `!i. (\x. measure (density M (indicator_fn (ff i)))
        (\y. (x,y) IN (m_space N CROSS m_space (density M (indicator_fn (ff i))) INTER Q)))
        IN measurable (m_space N, measurable_sets N) Borel` THENL
  [DISCH_TAC,
   GEN_TAC THEN MATCH_MP_TAC finite_measure_cut_measurable THEN
   ASM_SIMP_TAC std_ss [pair_measure, measure_of, measurable_sets_def] THEN
   `{a CROSS b | a IN measurable_sets N /\
     b IN measurable_sets (density M (indicator_fn (ff i)))} SUBSET
     POW (m_space N CROSS m_space (density M (indicator_fn (ff i))))` by
    (SIMP_TAC std_ss [CROSS_DEF, POW_DEF, GSPECIFICATION, EXISTS_PROD, SUBSET_DEF] THEN
     RW_TAC std_ss [] THEN FULL_SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD] THEN
     `p_1 SUBSET m_space N` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
     `p_2 SUBSET m_space (density M (indicator_fn (ff i)))` by
      METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
     ASM_SET_TAC []) THEN
   ASM_SIMP_TAC std_ss [density, m_space_def, measurable_sets_def] THEN
   UNDISCH_TAC ``Q:'b#'a->bool IN measurable_sets (pair_measure N M)`` THEN
   SIMP_TAC std_ss [measurable_sets_def, pair_measure, measure_of] THEN
   POP_ASSUM (ASSUME_TAC o SIMP_RULE std_ss [density, m_space_def, measurable_sets_def]) THEN
   ASM_SIMP_TAC std_ss [] THEN POP_ASSUM (ASSUME_TAC o MATCH_MP sigma_sets_into_sp) THEN
   DISCH_TAC THEN `Q SUBSET m_space N CROSS m_space M` by METIS_TAC [] THEN
   `m_space N CROSS m_space M INTER Q = Q` by ASM_SET_TAC [] THEN
   ASM_SIMP_TAC std_ss []] THEN
  Q_TAC SUFF_TAC `!i x.  measure (density M (indicator_fn (ff i)))
      (\y. (x,y) IN m_space N CROSS
                    m_space (density M (indicator_fn (ff i))) INTER Q) =
    measure M (ff i INTER (\y. (x,y) IN m_space N CROSS
                    m_space (density M (indicator_fn (ff i))) INTER Q))` THENL
  [DISCH_TAC,
   SIMP_TAC std_ss [density, measure_def, m_space_def] THEN
   `{a CROSS b | a IN measurable_sets N /\
     b IN measurable_sets (density M (indicator_fn (ff i)))} SUBSET
     POW (m_space N CROSS m_space (density M (indicator_fn (ff i))))` by
    (SIMP_TAC std_ss [CROSS_DEF, POW_DEF, GSPECIFICATION, EXISTS_PROD, SUBSET_DEF] THEN
     RW_TAC std_ss [] THEN FULL_SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD] THEN
     `p_1 SUBSET m_space N` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
     `p_2 SUBSET m_space (density M (indicator_fn (ff i)))` by
      METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
     ASM_SET_TAC []) THEN
   ASM_SIMP_TAC std_ss [density, m_space_def, measurable_sets_def] THEN
   UNDISCH_TAC ``Q:'b#'a->bool IN measurable_sets (pair_measure N M)`` THEN
   SIMP_TAC std_ss [measurable_sets_def, pair_measure, measure_of] THEN
   POP_ASSUM (ASSUME_TAC o SIMP_RULE std_ss [density, m_space_def, measurable_sets_def]) THEN
   ASM_SIMP_TAC std_ss [] THEN POP_ASSUM (ASSUME_TAC o MATCH_MP sigma_sets_into_sp) THEN
   DISCH_TAC THEN `Q SUBSET m_space N CROSS m_space M` by METIS_TAC [] THEN
   `m_space N CROSS m_space M INTER Q = Q` by ASM_SET_TAC [] THEN
   ASM_SIMP_TAC std_ss [] THEN
   Q_TAC SUFF_TAC `!x A. A IN sigma_sets (m_space N CROSS m_space M)
     {a CROSS b | a IN measurable_sets N /\ b IN measurable_sets M} ==>
     (\y. (x,y) IN A) IN measurable_sets M` THENL
   [DISCH_TAC,
    GEN_TAC THEN GEN_TAC THEN
    Q_TAC SUFF_TAC `sigma_sets (m_space N CROSS m_space M)
     {a CROSS b | a IN measurable_sets N /\ b IN measurable_sets M} A ==>
     (\z. (\y. (x,y) IN z) IN measurable_sets M) A` THENL
    [SIMP_TAC std_ss [SPECIFICATION], ALL_TAC] THEN
    MATCH_MP_TAC sigma_sets_ind THEN RW_TAC std_ss [] THENL
    [SIMP_TAC std_ss [NOT_IN_EMPTY, SET_RULE ``(\x. F) = {}``] THEN
     METIS_TAC [MEASURE_SPACE_EMPTY_MEASURABLE],
     POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION]) THEN
     RW_TAC std_ss [CROSS_DEF, GSPECIFICATION, EXISTS_PROD] THEN
     SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD] THEN
     ASM_CASES_TAC ``x:'b IN p_1`` THENL
     [ASM_SIMP_TAC std_ss [] THEN
      ASM_SIMP_TAC std_ss [MEASURE_SPACE_MSPACE_MEASURABLE,
       SET_RULE ``(\x. x IN s) = s``], ALL_TAC] THEN
     ASM_SIMP_TAC std_ss [SET_RULE ``(\x. F) = {}``] THEN
     ASM_SIMP_TAC std_ss [MEASURE_SPACE_EMPTY_MEASURABLE],
     Q_TAC SUFF_TAC `(\y. (x,y) IN m_space N CROSS m_space M DIFF a) =
          if x IN m_space N then m_space M DIFF (\y. (x,y) IN a) else {}` THENL
     [DISCH_TAC THEN ASM_SIMP_TAC std_ss [],
      ASM_SIMP_TAC std_ss [CROSS_DEF, INTER_DEF, DIFF_DEF] THEN
      ASM_SIMP_TAC std_ss [EXTENSION, GSPECIFICATION, EXISTS_PROD] THEN
      ASM_SET_TAC []] THEN
     `{} IN measurable_sets M` by METIS_TAC [MEASURE_SPACE_EMPTY_MEASURABLE] THEN
     COND_CASES_TAC THEN ASM_SIMP_TAC std_ss [] THEN
     MATCH_MP_TAC MEASURE_SPACE_DIFF THEN
     ASM_SIMP_TAC std_ss [MEASURE_SPACE_MSPACE_MEASURABLE],
     ALL_TAC] THEN
    Q_TAC SUFF_TAC `(\y. (x,y) IN BIGUNION {A i | i IN univ(:num)}) =
       BIGUNION {(\y. (x,y) IN A i) | i IN UNIV}` THENL
    [DISC_RW_KILL,
     SIMP_TAC std_ss [EXTENSION, IN_BIGUNION, IN_INTER, GSPECIFICATION, EXISTS_PROD] THEN
     GEN_TAC THEN EQ_TAC THEN RW_TAC std_ss [] THEN TRY (ASM_SET_TAC []) THEN
     POP_ASSUM (MP_TAC o SIMP_RULE std_ss [IN_DEF]) THEN
     RW_TAC std_ss [] THEN Q.EXISTS_TAC `(\x'. A i (x, x'))` THEN
     CONJ_TAC THENL [ASM_SET_TAC [], ALL_TAC] THEN SET_TAC []] THEN
    SIMP_TAC std_ss [GSYM IMAGE_DEF] THEN MATCH_MP_TAC MEASURE_SPACE_BIGUNION THEN
    ASM_SIMP_TAC std_ss []] THEN
   `!x. (\y. (x,y) IN Q) IN measurable_sets M` by METIS_TAC [] THEN
    ASM_SIMP_TAC std_ss [extreal_max_def, le_mul, indicator_fn_pos_le] THEN
    SIMP_TAC std_ss [INDICATOR_FN_MUL_INTER] THEN GEN_TAC THEN GEN_TAC THEN
   `ff i INTER (\y. (x,y) IN Q) IN measurable_sets M` by
    METIS_TAC [MEASURE_SPACE_INTER] THEN
   Q.UNABBREV_TAC `C` THEN ASM_SIMP_TAC std_ss [GSYM pos_fn_integral_indicator] THEN
   METIS_TAC [ETA_AX]] THEN
  Q_TAC SUFF_TAC `!i x. ff i INTER
    (\y. (x,y) IN m_space N CROSS
                  m_space (density M (indicator_fn (ff i))) INTER Q) =
    C x i` THENL
  [DISCH_TAC,
   SIMP_TAC std_ss [density, measure_def, m_space_def] THEN
   `{a CROSS b | a IN measurable_sets N /\
     b IN measurable_sets (density M (indicator_fn (ff i)))} SUBSET
     POW (m_space N CROSS m_space (density M (indicator_fn (ff i))))` by
    (SIMP_TAC std_ss [CROSS_DEF, POW_DEF, GSPECIFICATION, EXISTS_PROD, SUBSET_DEF] THEN
     RW_TAC std_ss [] THEN FULL_SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD] THEN
     `p_1 SUBSET m_space N` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
     `p_2 SUBSET m_space (density M (indicator_fn (ff i)))` by
      METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
     ASM_SET_TAC []) THEN
   ASM_SIMP_TAC std_ss [density, m_space_def, measurable_sets_def] THEN
   UNDISCH_TAC ``Q:'b#'a->bool IN measurable_sets (pair_measure N M)`` THEN
   SIMP_TAC std_ss [measurable_sets_def, pair_measure, measure_of] THEN
   POP_ASSUM (ASSUME_TAC o SIMP_RULE std_ss [density, m_space_def, measurable_sets_def]) THEN
   ASM_SIMP_TAC std_ss [] THEN POP_ASSUM (ASSUME_TAC o MATCH_MP sigma_sets_into_sp) THEN
   DISCH_TAC THEN `Q SUBSET m_space N CROSS m_space M` by METIS_TAC [] THEN
   `m_space N CROSS m_space M INTER Q = Q` by ASM_SET_TAC [] THEN
   ASM_SIMP_TAC std_ss []] THEN
  POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
  POP_ASSUM (fn th => DISCH_TAC THEN DISCH_TAC THEN MP_TAC th) THEN
  ASM_SIMP_TAC std_ss [] THEN POP_ASSUM K_TAC THEN POP_ASSUM K_TAC THEN
  DISCH_TAC THEN

  Q_TAC SUFF_TAC `!x. suminf (\i. measure M (C x i)) =
        measure M (BIGUNION {C x i | i IN UNIV})` THENL
  [DISCH_TAC,
   GEN_TAC THEN MATCH_MP_TAC suminf_measure THEN
   ASM_SIMP_TAC std_ss [] THEN Q.UNABBREV_TAC `C` THEN CONJ_TAC THENL
   [ALL_TAC,
    UNDISCH_TAC ``disjoint_family (ff:num->'a->bool)`` THEN
    SIMP_TAC std_ss [disjoint_family, disjoint_family_on, IN_UNIV] THEN
    RW_TAC std_ss [INTER_DEF] THEN ASM_SET_TAC []] THEN
   `{a CROSS b | a IN measurable_sets N /\
     b IN measurable_sets (density M (indicator_fn (ff i)))} SUBSET
     POW (m_space N CROSS m_space (density M (indicator_fn (ff i))))` by
    (SIMP_TAC std_ss [CROSS_DEF, POW_DEF, GSPECIFICATION, EXISTS_PROD, SUBSET_DEF] THEN
     RW_TAC std_ss [] THEN FULL_SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD] THEN
     `p_1 SUBSET m_space N` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
     `p_2 SUBSET m_space (density M (indicator_fn (ff i)))` by
      METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
     ASM_SET_TAC []) THEN
   ASM_SIMP_TAC std_ss [density, m_space_def, measurable_sets_def] THEN
   UNDISCH_TAC ``Q:'b#'a->bool IN measurable_sets (pair_measure N M)`` THEN
   SIMP_TAC std_ss [measurable_sets_def, pair_measure, measure_of] THEN
   POP_ASSUM (ASSUME_TAC o SIMP_RULE std_ss [density, m_space_def, measurable_sets_def]) THEN
   ASM_SIMP_TAC std_ss [] THEN DISCH_TAC THEN
   Q_TAC SUFF_TAC `!x A. A IN sigma_sets (m_space N CROSS m_space M)
     {a CROSS b | a IN measurable_sets N /\ b IN measurable_sets M} ==>
     (\y. (x,y) IN A) IN measurable_sets M` THENL
   [DISCH_TAC,
    GEN_TAC THEN GEN_TAC THEN
    Q_TAC SUFF_TAC `sigma_sets (m_space N CROSS m_space M)
     {a CROSS b | a IN measurable_sets N /\ b IN measurable_sets M} A ==>
     (\z. (\y. (x,y) IN z) IN measurable_sets M) A` THENL
    [SIMP_TAC std_ss [SPECIFICATION], ALL_TAC] THEN
    MATCH_MP_TAC sigma_sets_ind THEN RW_TAC std_ss [] THENL
    [SIMP_TAC std_ss [NOT_IN_EMPTY, SET_RULE ``(\x. F) = {}``] THEN
     METIS_TAC [MEASURE_SPACE_EMPTY_MEASURABLE],
     POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION]) THEN
     RW_TAC std_ss [CROSS_DEF, GSPECIFICATION, EXISTS_PROD] THEN
     SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD] THEN
     ASM_CASES_TAC ``x:'b IN p_1`` THENL
     [ASM_SIMP_TAC std_ss [] THEN
      ASM_SIMP_TAC std_ss [MEASURE_SPACE_MSPACE_MEASURABLE,
       SET_RULE ``(\x. x IN s) = s``], ALL_TAC] THEN
     ASM_SIMP_TAC std_ss [SET_RULE ``(\x. F) = {}``] THEN
     ASM_SIMP_TAC std_ss [MEASURE_SPACE_EMPTY_MEASURABLE],
     Q_TAC SUFF_TAC `(\y. (x,y) IN m_space N CROSS m_space M DIFF a) =
          if x IN m_space N then m_space M DIFF (\y. (x,y) IN a) else {}` THENL
     [DISCH_TAC THEN ASM_SIMP_TAC std_ss [],
      ASM_SIMP_TAC std_ss [CROSS_DEF, INTER_DEF, DIFF_DEF] THEN
      ASM_SIMP_TAC std_ss [EXTENSION, GSPECIFICATION, EXISTS_PROD] THEN
      ASM_SET_TAC []] THEN
     `{} IN measurable_sets M` by METIS_TAC [MEASURE_SPACE_EMPTY_MEASURABLE] THEN
     COND_CASES_TAC THEN ASM_SIMP_TAC std_ss [] THEN
     MATCH_MP_TAC MEASURE_SPACE_DIFF THEN
     ASM_SIMP_TAC std_ss [MEASURE_SPACE_MSPACE_MEASURABLE],
     ALL_TAC] THEN
    Q_TAC SUFF_TAC `(\y. (x,y) IN BIGUNION {A i | i IN univ(:num)}) =
       BIGUNION {(\y. (x,y) IN A i) | i IN UNIV}` THENL
    [DISC_RW_KILL,
     SIMP_TAC std_ss [EXTENSION, IN_BIGUNION, IN_INTER, GSPECIFICATION, EXISTS_PROD] THEN
     GEN_TAC THEN EQ_TAC THEN RW_TAC std_ss [] THEN TRY (ASM_SET_TAC []) THEN
     POP_ASSUM (MP_TAC o SIMP_RULE std_ss [IN_DEF]) THEN
     RW_TAC std_ss [] THEN Q.EXISTS_TAC `(\x'. A i (x, x'))` THEN
     CONJ_TAC THENL [ASM_SET_TAC [], ALL_TAC] THEN SET_TAC []] THEN
    SIMP_TAC std_ss [GSYM IMAGE_DEF] THEN MATCH_MP_TAC MEASURE_SPACE_BIGUNION THEN
    ASM_SIMP_TAC std_ss []] THEN
   `!x. (\y. (x,y) IN Q) IN measurable_sets M` by METIS_TAC [] THEN
   RW_TAC std_ss [SUBSET_DEF, IN_IMAGE] THEN METIS_TAC [MEASURE_SPACE_INTER]] THEN
  Q_TAC SUFF_TAC `!i x. BIGUNION {C x i | i IN univ(:num)} = (\y. (x,y) IN Q)` THENL
  [DISCH_TAC,
   Q.UNABBREV_TAC `C` THEN SIMP_TAC std_ss [] THEN
   `{a CROSS b | a IN measurable_sets N /\
     b IN measurable_sets (density M (indicator_fn (ff i)))} SUBSET
     POW (m_space N CROSS m_space (density M (indicator_fn (ff i))))` by
    (SIMP_TAC std_ss [CROSS_DEF, POW_DEF, GSPECIFICATION, EXISTS_PROD, SUBSET_DEF] THEN
     RW_TAC std_ss [] THEN FULL_SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD] THEN
     `p_1 SUBSET m_space N` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
     `p_2 SUBSET m_space (density M (indicator_fn (ff i)))` by
      METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
     ASM_SET_TAC []) THEN
   ASM_SIMP_TAC std_ss [density, m_space_def, measurable_sets_def] THEN
   UNDISCH_TAC ``Q:'b#'a->bool IN measurable_sets (pair_measure N M)`` THEN
   SIMP_TAC std_ss [measurable_sets_def, pair_measure, measure_of] THEN
   POP_ASSUM (ASSUME_TAC o SIMP_RULE std_ss [density, m_space_def, measurable_sets_def]) THEN
   ASM_SIMP_TAC std_ss [] THEN POP_ASSUM (ASSUME_TAC o MATCH_MP sigma_sets_into_sp) THEN
   DISCH_TAC THEN `Q SUBSET m_space N CROSS m_space M` by METIS_TAC [] THEN
   `m_space N CROSS m_space M INTER Q = Q` by ASM_SET_TAC [] THEN
   ASM_SIMP_TAC std_ss [] THEN
   Q_TAC SUFF_TAC `!x A. A IN sigma_sets (m_space N CROSS m_space M)
     {a CROSS b | a IN measurable_sets N /\ b IN measurable_sets M} ==>
     (\y. (x,y) IN A) IN measurable_sets M` THENL
   [DISCH_TAC,
    GEN_TAC THEN GEN_TAC THEN
    Q_TAC SUFF_TAC `sigma_sets (m_space N CROSS m_space M)
     {a CROSS b | a IN measurable_sets N /\ b IN measurable_sets M} A ==>
     (\z. (\y. (x,y) IN z) IN measurable_sets M) A` THENL
    [SIMP_TAC std_ss [SPECIFICATION], ALL_TAC] THEN
    MATCH_MP_TAC sigma_sets_ind THEN RW_TAC std_ss [] THENL
    [SIMP_TAC std_ss [NOT_IN_EMPTY, SET_RULE ``(\x. F) = {}``] THEN
     METIS_TAC [MEASURE_SPACE_EMPTY_MEASURABLE],
     POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION]) THEN
     RW_TAC std_ss [CROSS_DEF, GSPECIFICATION, EXISTS_PROD] THEN
     SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD] THEN
     ASM_CASES_TAC ``x:'b IN p_1`` THENL
     [ASM_SIMP_TAC std_ss [] THEN
      ASM_SIMP_TAC std_ss [MEASURE_SPACE_MSPACE_MEASURABLE,
       SET_RULE ``(\x. x IN s) = s``], ALL_TAC] THEN
     ASM_SIMP_TAC std_ss [SET_RULE ``(\x. F) = {}``] THEN
     ASM_SIMP_TAC std_ss [MEASURE_SPACE_EMPTY_MEASURABLE],
     Q_TAC SUFF_TAC `(\y. (x,y) IN m_space N CROSS m_space M DIFF a) =
          if x IN m_space N then m_space M DIFF (\y. (x,y) IN a) else {}` THENL
     [DISCH_TAC THEN ASM_SIMP_TAC std_ss [],
      ASM_SIMP_TAC std_ss [CROSS_DEF, INTER_DEF, DIFF_DEF] THEN
      ASM_SIMP_TAC std_ss [EXTENSION, GSPECIFICATION, EXISTS_PROD] THEN
      ASM_SET_TAC []] THEN
     `{} IN measurable_sets M` by METIS_TAC [MEASURE_SPACE_EMPTY_MEASURABLE] THEN
     COND_CASES_TAC THEN ASM_SIMP_TAC std_ss [] THEN
     MATCH_MP_TAC MEASURE_SPACE_DIFF THEN
     ASM_SIMP_TAC std_ss [MEASURE_SPACE_MSPACE_MEASURABLE],
     ALL_TAC] THEN
    Q_TAC SUFF_TAC `(\y. (x,y) IN BIGUNION {A i | i IN univ(:num)}) =
       BIGUNION {(\y. (x,y) IN A i) | i IN UNIV}` THENL
    [DISC_RW_KILL,
     SIMP_TAC std_ss [EXTENSION, IN_BIGUNION, IN_INTER, GSPECIFICATION, EXISTS_PROD] THEN
     GEN_TAC THEN EQ_TAC THEN RW_TAC std_ss [] THEN TRY (ASM_SET_TAC []) THEN
     POP_ASSUM (MP_TAC o SIMP_RULE std_ss [IN_DEF]) THEN
     RW_TAC std_ss [] THEN Q.EXISTS_TAC `(\x'. A i (x, x'))` THEN
     CONJ_TAC THENL [ASM_SET_TAC [], ALL_TAC] THEN SET_TAC []] THEN
    SIMP_TAC std_ss [GSYM IMAGE_DEF] THEN MATCH_MP_TAC MEASURE_SPACE_BIGUNION THEN
    ASM_SIMP_TAC std_ss []] THEN
   `!x. (\y. (x,y) IN Q) IN measurable_sets M` by METIS_TAC [] THEN GEN_TAC THEN
   `(\y. (x,y) IN Q) SUBSET m_space M` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
   Q_TAC SUFF_TAC `BIGUNION {ff i INTER (\y. (x,y) IN Q) | i IN univ(:num)} =
                   BIGUNION {ff i | i IN univ(:num)} INTER (\y. (x,y) IN Q)` THENL
   [DISCH_TAC THEN ASM_SIMP_TAC std_ss [],
    SIMP_TAC std_ss [EXTENSION, IN_BIGUNION, IN_INTER] THEN
    RW_TAC std_ss [IN_UNIV] THEN EQ_TAC THEN RW_TAC std_ss [] THEN
    FULL_SIMP_TAC std_ss [GSPECIFICATION] THENL
    [Q.EXISTS_TAC `ff i` THEN ASM_SET_TAC [],
     ASM_SET_TAC [], ALL_TAC] THEN
    Q.EXISTS_TAC `ff i INTER (\y. (x,y) IN Q)` THEN ASM_SET_TAC []] THEN
   ASM_SET_TAC []] THEN
  POP_ASSUM (fn th => REWRITE_TAC [GSYM th]) THEN
  POP_ASSUM (fn th => REWRITE_TAC [GSYM th]) THEN
  SIMP_TAC std_ss [ext_suminf_def] THEN MATCH_MP_TAC IN_MEASURABLE_BOREL_MONO_SUP THEN
  Q.EXISTS_TAC `(\n x. SIGMA (\i. measure M (C x i)) (count n))` THEN
  CONJ_TAC THENL [METIS_TAC [measure_space_def], ALL_TAC] THEN
  `{a CROSS b | a IN measurable_sets N /\
     b IN measurable_sets (density M (indicator_fn (ff i)))} SUBSET
     POW (m_space N CROSS m_space (density M (indicator_fn (ff i))))` by
    (SIMP_TAC std_ss [CROSS_DEF, POW_DEF, GSPECIFICATION, EXISTS_PROD, SUBSET_DEF] THEN
     RW_TAC std_ss [] THEN FULL_SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD] THEN
     `p_1 SUBSET m_space N` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
     `p_2 SUBSET m_space (density M (indicator_fn (ff i)))` by
      METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
     ASM_SET_TAC []) THEN
  ASM_SIMP_TAC std_ss [density, m_space_def, measurable_sets_def] THEN
  UNDISCH_TAC ``Q:'b#'a->bool IN measurable_sets (pair_measure N M)`` THEN
  SIMP_TAC std_ss [measurable_sets_def, pair_measure, measure_of] THEN
  POP_ASSUM (ASSUME_TAC o SIMP_RULE std_ss [density, m_space_def, measurable_sets_def]) THEN
  ASM_SIMP_TAC std_ss [] THEN POP_ASSUM (ASSUME_TAC o MATCH_MP sigma_sets_into_sp) THEN
  DISCH_TAC THEN `Q SUBSET m_space N CROSS m_space M` by METIS_TAC [] THEN
  `m_space N CROSS m_space M INTER Q = Q` by ASM_SET_TAC [] THEN
  ASM_SIMP_TAC std_ss [] THEN
  Q_TAC SUFF_TAC `!x A. A IN sigma_sets (m_space N CROSS m_space M)
    {a CROSS b | a IN measurable_sets N /\ b IN measurable_sets M} ==>
    (\y. (x,y) IN A) IN measurable_sets M` THENL
  [DISCH_TAC,
   GEN_TAC THEN GEN_TAC THEN
   Q_TAC SUFF_TAC `sigma_sets (m_space N CROSS m_space M)
    {a CROSS b | a IN measurable_sets N /\ b IN measurable_sets M} A ==>
    (\z. (\y. (x,y) IN z) IN measurable_sets M) A` THENL
   [SIMP_TAC std_ss [SPECIFICATION], ALL_TAC] THEN
   MATCH_MP_TAC sigma_sets_ind THEN RW_TAC std_ss [] THENL
   [SIMP_TAC std_ss [NOT_IN_EMPTY, SET_RULE ``(\x. F) = {}``] THEN
    METIS_TAC [MEASURE_SPACE_EMPTY_MEASURABLE],
    POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION]) THEN
    RW_TAC std_ss [CROSS_DEF, GSPECIFICATION, EXISTS_PROD] THEN
    SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD] THEN
    ASM_CASES_TAC ``x:'b IN p_1`` THENL
    [ASM_SIMP_TAC std_ss [] THEN
     ASM_SIMP_TAC std_ss [MEASURE_SPACE_MSPACE_MEASURABLE,
      SET_RULE ``(\x. x IN s) = s``], ALL_TAC] THEN
    ASM_SIMP_TAC std_ss [SET_RULE ``(\x. F) = {}``] THEN
    ASM_SIMP_TAC std_ss [MEASURE_SPACE_EMPTY_MEASURABLE],
    Q_TAC SUFF_TAC `(\y. (x,y) IN m_space N CROSS m_space M DIFF a) =
         if x IN m_space N then m_space M DIFF (\y. (x,y) IN a) else {}` THENL
    [DISCH_TAC THEN ASM_SIMP_TAC std_ss [],
     ASM_SIMP_TAC std_ss [CROSS_DEF, INTER_DEF, DIFF_DEF] THEN
     ASM_SIMP_TAC std_ss [EXTENSION, GSPECIFICATION, EXISTS_PROD] THEN
     ASM_SET_TAC []] THEN
    `{} IN measurable_sets M` by METIS_TAC [MEASURE_SPACE_EMPTY_MEASURABLE] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC std_ss [] THEN
    MATCH_MP_TAC MEASURE_SPACE_DIFF THEN
    ASM_SIMP_TAC std_ss [MEASURE_SPACE_MSPACE_MEASURABLE],
    ALL_TAC] THEN
   Q_TAC SUFF_TAC `(\y. (x,y) IN BIGUNION {A i | i IN univ(:num)}) =
      BIGUNION {(\y. (x,y) IN A i) | i IN UNIV}` THENL
   [DISC_RW_KILL,
    SIMP_TAC std_ss [EXTENSION, IN_BIGUNION, IN_INTER, GSPECIFICATION, EXISTS_PROD] THEN
    GEN_TAC THEN EQ_TAC THEN RW_TAC std_ss [] THEN TRY (ASM_SET_TAC []) THEN
    POP_ASSUM (MP_TAC o SIMP_RULE std_ss [IN_DEF]) THEN
    RW_TAC std_ss [] THEN Q.EXISTS_TAC `(\x'. A i (x, x'))` THEN
    CONJ_TAC THENL [ASM_SET_TAC [], ALL_TAC] THEN SET_TAC []] THEN
   SIMP_TAC std_ss [GSYM IMAGE_DEF] THEN MATCH_MP_TAC MEASURE_SPACE_BIGUNION THEN
   ASM_SIMP_TAC std_ss []] THEN
  `!x. (\y. (x,y) IN Q) IN measurable_sets M` by METIS_TAC [] THEN
  `!i x. C x i IN measurable_sets M` by METIS_TAC [MEASURE_SPACE_INTER] THEN
  CONJ_TAC THENL
  [GEN_TAC THEN Q.ABBREV_TAC `s = count n` THEN
   Q.ABBREV_TAC `f = (\i x. measure M (C x i))` THEN
   Q_TAC SUFF_TAC ` FINITE s /\ sigma_algebra (m_space N,measurable_sets N) /\
    (!i. i IN s ==>
     f i IN measurable (m_space N,measurable_sets N) Borel) /\
    (!i x. i IN s /\ x IN space (m_space N,measurable_sets N) ==>
     f i x <> NegInf) /\
    !x. x IN space (m_space N,measurable_sets N) ==>
    ((\x. SIGMA (\i. measure M (C x i)) (count n)) x =
     SIGMA (\i. f i x) s)` THENL
   [DISCH_THEN (MP_TAC o MATCH_MP IN_MEASURABLE_BOREL_SUM) THEN
    METIS_TAC [], ALL_TAC] THEN
   Q.UNABBREV_TAC `s` THEN Q.UNABBREV_TAC `f` THEN
   ASM_SIMP_TAC std_ss [FINITE_COUNT] THEN
   CONJ_TAC THENL [METIS_TAC [measure_space_def], ALL_TAC] THEN
   RW_TAC std_ss [space_def, lt_infty] THEN
   MATCH_MP_TAC lte_trans THEN Q.EXISTS_TAC `0` THEN
   SIMP_TAC std_ss [GSYM lt_infty, num_not_infty] THEN
   METIS_TAC [measure_space_def, positive_def],
   ALL_TAC] THEN
  RW_TAC std_ss [] THEN MATCH_MP_TAC EXTREAL_SUM_IMAGE_MONO_SET THEN
  SIMP_TAC std_ss [FINITE_COUNT] THEN CONJ_TAC THENL
  [SIMP_TAC arith_ss [count_def, SUBSET_DEF, GSPECIFICATION], ALL_TAC] THEN
  METIS_TAC [measure_space_def, positive_def]);

val indep_set_sigma_sets = store_thm ("indep_sets_sigma_sets",
  ``!p A B. prob_space p /\ indep_set p A B /\ Int_stable A /\ Int_stable B ==>
            indep_set p (subsets (sigma (m_space p) A)) (subsets (sigma (m_space p) B))``,
  RW_TAC std_ss [indep_set] THEN
  Q_TAC SUFF_TAC `(\i:num. if i = 0 then subsets (sigma (m_space p) A)
                         else subsets (sigma (m_space p) B)) =
                  (\i:num. subsets (sigma (p_space p) ((\i. if i = 0 then A else B) i)))` THENL
  [DISC_RW_KILL, ABS_TAC THEN METIS_TAC [p_space_def]] THEN
  MATCH_MP_TAC indep_sets_sigma THEN ASM_SIMP_TAC std_ss [IN_UNIV] THEN
  RW_TAC std_ss [Int_stable] THEN FULL_SIMP_TAC std_ss [Int_stable] THEN
  METIS_TAC []);

val indep_var_distribution_imp = store_thm ("indep_var_distribution_imp",
  ``!p M1 X M2 Y. prob_space p /\ measure_space M1 /\ measure_space M2 /\
                  sigma_finite_measure M2 /\ indep_var p M1 X M2 Y ==>
      random_variable X p (m_space M1, measurable_sets M1) /\
      random_variable Y p (m_space M2, measurable_sets M2) /\
      (measure_of (pair_measure (distr p M1 X) (distr p M2 Y)) =
       measure_of (distr p (pair_measure M1 M2) (\x. (X x, Y x))))``,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  `indep_var p M1 X M2 Y ==>
      random_variable X p (m_space M1, measurable_sets M1) /\
      random_variable Y p (m_space M2, measurable_sets M2)`
   by METIS_TAC [indep_var_rv] THEN
  `indep_var p M1 X M2 Y ==>
      random_variable (\x. (X x, Y x)) p
      (m_space (pair_measure M1 M2), measurable_sets (pair_measure M1 M2))` by
   (DISCH_THEN (fn th => POP_ASSUM MP_TAC THEN ASSUME_TAC th) THEN
    ASM_SIMP_TAC std_ss [random_variable_def] THEN STRIP_TAC THEN
    SIMP_TAC std_ss [p_space_def, events_def] THEN MATCH_MP_TAC measurable_Pair THEN
    FULL_SIMP_TAC std_ss [prob_space_def, p_space_def, events_def]) THEN
  `indep_var p M1 X M2 Y ==> prob_space (distr p M1 X)` by
   METIS_TAC [prob_space_distr, random_variable_def, p_space_def, events_def] THEN
  `indep_var p M1 X M2 Y ==> prob_space (distr p M2 Y)` by
   METIS_TAC [prob_space_distr, random_variable_def, p_space_def, events_def] THEN
  Q_TAC SUFF_TAC `indep_var p M1 X M2 Y ==>
                  (measure_of (pair_measure (distr p M1 X) (distr p M2 Y)) =
                   measure_of (distr p (pair_measure M1 M2) (\x. X x,Y x)))` THENL
  [DISCH_TAC,
   DISCH_TAC THEN MATCH_MP_TAC pair_measure_eqI THEN
   Q_TAC SUFF_TAC `sigma_finite_measure (distr p M1 X)` THENL
   [DISCH_TAC THEN ASM_SIMP_TAC std_ss [],
    RW_TAC std_ss [sigma_finite_measure] THEN Q.EXISTS_TAC `{m_space M1}` THEN
    SIMP_TAC std_ss [countable_sing] THEN
    CONJ_TAC THENL
    [RW_TAC std_ss [SUBSET_DEF, distr, measurable_sets_def, IN_SING] THEN
     ASM_SIMP_TAC std_ss [MEASURE_SPACE_MSPACE_MEASURABLE], ALL_TAC] THEN
    CONJ_TAC THENL [SIMP_TAC std_ss [BIGUNION_SING, distr, m_space_def], ALL_TAC] THEN
    RW_TAC std_ss [IN_SING] THEN FULL_SIMP_TAC std_ss [prob_space_def] THEN
    `m_space M1 = p_space (distr p M1 X)` by METIS_TAC [p_space_def, m_space_def, distr] THEN
    ASM_SIMP_TAC std_ss [num_not_infty]] THEN
   Q_TAC SUFF_TAC `sigma_finite_measure (distr p M2 Y)` THENL
   [DISCH_TAC THEN ASM_SIMP_TAC std_ss [],
    RW_TAC std_ss [sigma_finite_measure] THEN Q.EXISTS_TAC `{m_space M2}` THEN
    SIMP_TAC std_ss [countable_sing] THEN
    CONJ_TAC THENL
    [RW_TAC std_ss [SUBSET_DEF, distr, measurable_sets_def, IN_SING] THEN
     ASM_SIMP_TAC std_ss [MEASURE_SPACE_MSPACE_MEASURABLE], ALL_TAC] THEN
    CONJ_TAC THENL [SIMP_TAC std_ss [BIGUNION_SING, distr, m_space_def], ALL_TAC] THEN
    RW_TAC std_ss [IN_SING] THEN FULL_SIMP_TAC std_ss [prob_space_def] THEN
    `m_space M2 = p_space (distr p M2 Y)` by METIS_TAC [p_space_def, m_space_def, distr] THEN
    ASM_SIMP_TAC std_ss [num_not_infty]] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC measure_space_distr THEN
    FULL_SIMP_TAC std_ss [prob_space_def, measure_space_pair_measure'] THEN
    FULL_SIMP_TAC std_ss [random_variable_def, p_space_def, events_def],
    ALL_TAC] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC measure_space_distr THEN FULL_SIMP_TAC std_ss [prob_space_def] THEN
    FULL_SIMP_TAC std_ss [random_variable_def, p_space_def, events_def],
    ALL_TAC] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC measure_space_distr THEN FULL_SIMP_TAC std_ss [prob_space_def] THEN
    FULL_SIMP_TAC std_ss [random_variable_def, p_space_def, events_def],
    ALL_TAC] THEN
   CONJ_TAC THENL
   [Q_TAC SUFF_TAC `{a CROSS b | a IN measurable_sets M1 /\ b IN measurable_sets M2}
                     SUBSET POW (m_space M1 CROSS m_space M2)` THENL
    [DISCH_TAC THEN ASM_SIMP_TAC std_ss [],
     SIMP_TAC std_ss [CROSS_DEF, SUBSET_DEF, POW_DEF, GSPECIFICATION, EXISTS_PROD] THEN
     RW_TAC std_ss [] THEN FULL_SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD] THEN
     `p_1 SUBSET m_space M1` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
     `p_2 SUBSET m_space M2` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
     ASM_SET_TAC []] THEN
    FULL_SIMP_TAC std_ss [pair_measure, measure_of, measurable_sets_def, distr, m_space_def],
    ALL_TAC] THEN
   RW_TAC std_ss [distr, measurable_sets_def] THEN SIMP_TAC std_ss [GSYM distr] THEN
   ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN SIMP_TAC std_ss [distr, measure_def] THEN
   SIMP_TAC std_ss [GSYM prob_def, GSYM p_space_def] THEN
   MATCH_MP_TAC (REWRITE_RULE [GSYM p_space_def] indep_varD) THEN
   METIS_TAC []] THEN
  METIS_TAC []);

val convolution = Define
   `(convolution M N):(real -> bool) # ((real -> bool) -> bool) # ((real->bool) -> extreal)
    = distr (pair_measure M N)
      (space borel, subsets borel, (\x. 0)) (\(x,y). x + y)`;

val sum_indep_random_variable = store_thm ("sum_indep_random_variable",
  ``!p X Y. prob_space p /\
        indep_var p (space borel, subsets borel, (\x. 0)) X
                    (space borel, subsets borel, (\x. 0)) Y ==>
        (!a. a  IN measurable_sets (space borel, subsets borel, (\x. 0)) ==>
        (distribution p (\x. X x + (Y:'a->real) x) a =
         measure (convolution
                  (distr' p (space borel, subsets borel, (\x. 0)) X)
                  (distr' p (space borel, subsets borel, (\x. 0)) Y)) a))``,
  RW_TAC std_ss [convolution] THEN ASSUME_TAC measure_space_borel THEN
  Q_TAC SUFF_TAC `sigma_finite_measure (space borel, subsets borel, (\x. 0))` THENL
  [DISCH_TAC,
   RW_TAC std_ss [sigma_finite_measure] THEN
   SIMP_TAC std_ss [m_space_def, measurable_sets_def, measure_def] THEN
   Q.EXISTS_TAC `{space borel}` THEN SIMP_TAC std_ss [num_not_infty] THEN
   `algebra borel` by METIS_TAC [measure_space_def, sigma_algebra_def,
     m_space_def, measurable_sets_def, SPACE] THEN
   ASM_SIMP_TAC std_ss [countable_sing, BIGUNION_SING] THEN
   ASM_SIMP_TAC std_ss [SUBSET_DEF, IN_SING, ALGEBRA_SPACE]] THEN
  Q.ABBREV_TAC `M = (space borel, subsets borel, (\x:real->bool. 0:extreal))` THEN
  `random_variable X p (m_space M,measurable_sets M) /\
   random_variable Y p (m_space M,measurable_sets M) /\
   (measure_of (pair_measure (distr p M X) (distr p M Y)) =
    measure_of (distr p (pair_measure M M) (\x. (X x,Y x))))`
   by METIS_TAC [indep_var_distribution_imp] THEN

  Q_TAC SUFF_TAC `measure_space (distr p M X)` THENL
  [DISCH_TAC, MATCH_MP_TAC measure_space_distr THEN
   FULL_SIMP_TAC std_ss [random_variable_def, prob_space_def] THEN
   FULL_SIMP_TAC std_ss [prob_def, events_def, p_space_def]] THEN
  Q_TAC SUFF_TAC `measure_space (distr p M Y)` THENL
  [DISCH_TAC, MATCH_MP_TAC measure_space_distr THEN
   FULL_SIMP_TAC std_ss [random_variable_def, prob_space_def] THEN
   FULL_SIMP_TAC std_ss [prob_def, events_def, p_space_def]] THEN

  Q_TAC SUFF_TAC `measure
   (distr (pair_measure (distr' p M X) (distr' p M Y)) M (\(x,y). x + y)) a =
                  measure
   (distr (pair_measure (distr p M X) (distr p M Y)) M (\(x,y). x + y)) a` THENL
  [DISC_RW_KILL,
   SIMP_TAC std_ss [distr, measure_def] THEN SIMP_TAC std_ss [GSYM distr] THEN
   Q_TAC SUFF_TAC `m_space (pair_measure (distr' p M X) (distr' p M Y)) =
                   m_space (distr' p M X) CROSS m_space (distr' p M Y)` THENL
   [DISC_RW_KILL, METIS_TAC [m_space_def, pair_measure, measure_of]] THEN
   Q_TAC SUFF_TAC `m_space (pair_measure (distr p M X) (distr p M Y)) =
                   m_space (distr p M X) CROSS m_space (distr p M Y)` THENL
   [DISC_RW_KILL, METIS_TAC [m_space_def, pair_measure, measure_of]] THEN
   SIMP_TAC std_ss [distr, distr', m_space_def] THEN
   SIMP_TAC std_ss [GSYM distr, GSYM distr'] THEN
   `!X. m_space (distr' p M X) = m_space (distr p M X)` by
    METIS_TAC [distr, m_space_def, distr'] THEN
   `!X. measurable_sets (distr' p M X) = measurable_sets (distr p M X)` by
    METIS_TAC [distr, measurable_sets_def, distr'] THEN
    ASM_SIMP_TAC std_ss [pair_measure, measure_of, measure_def] THEN
    ASM_SIMP_TAC std_ss [space_def, subsets_def] THEN
   Q_TAC SUFF_TAC `(\X'. pos_fn_integral (distr' p M X)
       (\x. pos_fn_integral (distr' p M Y) (\y. indicator_fn X' (x,y)))) =
                   (\X'. pos_fn_integral (distr p M X)
       (\x. pos_fn_integral (distr p M Y) (\y. indicator_fn X' (x,y))))` THENL
   [DISC_RW_KILL,
    ABS_TAC THEN ASM_SIMP_TAC std_ss [measure_of_eq] THEN
    SIMP_TAC std_ss [distr', distr, m_space_def, measurable_sets_def] THEN
    SIMP_TAC std_ss [measure_def]] THEN
   COND_CASES_TAC THEN ASM_SIMP_TAC std_ss [] THEN
   ASM_SIMP_TAC std_ss [measure_of_eq] THEN
   SIMP_TAC std_ss [distr', distr, m_space_def, measurable_sets_def] THEN
   SIMP_TAC std_ss [measure_def]] THEN

  Q_TAC SUFF_TAC `distribution p (\x. X x + Y x) a =
   measure
    (distr (measure_of (pair_measure (distr p M X) (distr p M Y))) M (\(x,y). x + y)) a` THENL
  [ONCE_REWRITE_TAC [pair_measure] THEN
   Q.ABBREV_TAC `N1 = (distr p M X)` THEN Q.ABBREV_TAC `N2 = (distr p M Y)` THEN
   Q_TAC SUFF_TAC `{a CROSS b | a IN measurable_sets N1 /\ b IN measurable_sets N2}
                   SUBSET POW (m_space N1 CROSS m_space N2)` THENL
   [DISCH_TAC,
    SIMP_TAC std_ss [CROSS_DEF, SUBSET_DEF, POW_DEF, GSPECIFICATION, EXISTS_PROD] THEN
    RW_TAC std_ss [] THEN FULL_SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD] THEN
    `p_1 SUBSET m_space N1` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
    `p_2 SUBSET m_space N2` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
    ASM_SET_TAC []] THEN
   Q.ABBREV_TAC `sp = (m_space N1 CROSS m_space N2)` THEN
   Q.ABBREV_TAC `st = {a CROSS b | a IN measurable_sets N1 /\ b IN measurable_sets N2}` THEN
   Q.ABBREV_TAC `MM = (sp,st, (\X'. pos_fn_integral N1
                  (\x. pos_fn_integral N2 (\y. indicator_fn X' (x,y)))))` THEN
   `m_space MM = sp` by METIS_TAC [m_space_def] THEN
   `measurable_sets MM = st` by METIS_TAC [measurable_sets_def] THEN
   METIS_TAC [measure_of_measure_of],
   ALL_TAC] THEN

  ASM_SIMP_TAC std_ss [] THEN
  `sigma_sets (m_space M) (measurable_sets M) = measurable_sets M` by
   METIS_TAC [sigma_sets_eq, measure_space_def] THEN
  `measurable_sets M SUBSET POW (m_space M)` by
   (FULL_SIMP_TAC std_ss [measure_space_def, sigma_algebra_iff2, POW_DEF] THEN
    ASM_SET_TAC []) THEN
  `measure_space (pair_measure M M)` by METIS_TAC [measure_space_pair_measure'] THEN
  `measurable_sets (pair_measure M M) SUBSET POW (m_space (pair_measure M M))` by
   (FULL_SIMP_TAC std_ss [measure_space_def, sigma_algebra_iff2, POW_DEF] THEN
    ASM_SET_TAC []) THEN
  `random_variable X p borel /\ random_variable Y p borel` by
    METIS_TAC [m_space_def, measurable_sets_def, space_def, subsets_def, SPACE] THEN
  `sigma_sets (m_space (pair_measure M M)) (measurable_sets (pair_measure M M)) =
              (measurable_sets (pair_measure M M))` by
   METIS_TAC [sigma_sets_eq, measure_space_def] THEN
  Q_TAC SUFF_TAC `measure_space (distr p M (\x. X x + Y x))` THENL
  [DISCH_TAC,
   MATCH_MP_TAC measure_space_distr THEN
   `measure_space p` by METIS_TAC [prob_space_def] THEN
   ASM_SIMP_TAC std_ss [] THEN Q.UNABBREV_TAC `M` THEN
   SIMP_TAC std_ss [m_space_def, measurable_sets_def, SPACE, GSYM borel_measurable] THEN
   MATCH_MP_TAC borel_measurable_add THEN Q.EXISTS_TAC `X` THEN Q.EXISTS_TAC `Y` THEN
   FULL_SIMP_TAC std_ss [borel_measurable, measure_space_def, random_variable_def] THEN
   FULL_SIMP_TAC std_ss [p_space_def, events_def]] THEN
  `{a CROSS b | a IN measurable_sets M /\ b IN measurable_sets M} SUBSET
     POW (m_space M CROSS m_space M)` by
   (SIMP_TAC std_ss [CROSS_DEF, SUBSET_DEF, POW_DEF, GSPECIFICATION, EXISTS_PROD] THEN
    RW_TAC std_ss [] THEN FULL_SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD] THEN
    `p_1 SUBSET m_space M` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
    `p_2 SUBSET m_space M` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
    ASM_SET_TAC []) THEN
  Q_TAC SUFF_TAC `measure_space (distr p (pair_measure M M) (\x. (X x,Y x)))` THENL
  [DISCH_TAC,
   MATCH_MP_TAC measure_space_distr THEN
   `measure_space p` by METIS_TAC [prob_space_def] THEN
   ASM_SIMP_TAC std_ss [] THEN MATCH_MP_TAC measurable_Pair THEN Q.UNABBREV_TAC `M` THEN
   ASM_SIMP_TAC std_ss [m_space_def, measurable_sets_def, SPACE, GSYM borel_measurable] THEN
   FULL_SIMP_TAC std_ss [borel_measurable, measure_space_def, random_variable_def] THEN
   FULL_SIMP_TAC std_ss [p_space_def, events_def]] THEN
  RW_TAC std_ss [measure_of, distr] THEN
  ASM_SIMP_TAC std_ss [m_space_def, measurable_sets_def, measure_def] THEN
  ASM_SIMP_TAC std_ss [GSYM distr] THEN
  Q_TAC SUFF_TAC `a IN measurable_sets M ==>
    PREIMAGE (\(x,y). x + y) a INTER m_space (pair_measure M M) IN
     measurable_sets (pair_measure M M)` THENL
  [ASM_SIMP_TAC std_ss [] THEN DISCH_TAC THEN RW_TAC std_ss [] THEN
   ASM_SIMP_TAC std_ss [distribution_def, prob_def] THEN AP_TERM_TAC THEN
   SIMP_TAC std_ss [EXTENSION, PREIMAGE_def, GSPECIFICATION, EXISTS_PROD] THEN
   SIMP_TAC std_ss [pair_measure, m_space_def, measure_of, p_space_def] THEN
   Q.UNABBREV_TAC `M` THEN SIMP_TAC std_ss [m_space_def, CROSS_DEF, space_borel] THEN
   SIMP_TAC std_ss [IN_UNIV, GSPEC_T, INTER_UNIV] THEN SET_TAC [],
   ALL_TAC] THEN
  DISCH_TAC THEN
  Q_TAC SUFF_TAC `(\x:real#real. FST x + SND x) IN
   measurable (m_space (pair_measure M M),measurable_sets (pair_measure M M))
                                  (m_space M,measurable_sets M)` THENL
  [Q_TAC SUFF_TAC `(\x:real#real. FST x + SND x) = (\(x,y). x + y)` THENL
   [DISC_RW_KILL,
    RW_TAC std_ss [FUN_EQ_THM] THEN
    `?a b. x = (a,b)` by METIS_TAC [pair_CASES] THEN
    ASM_SIMP_TAC std_ss []] THEN
   ASM_SIMP_TAC std_ss [IN_MEASURABLE, space_def, subsets_def],
   ALL_TAC] THEN

  Q.UNABBREV_TAC `M` THEN SIMP_TAC std_ss [m_space_def, measurable_sets_def, SPACE] THEN
  Q.ABBREV_TAC `M = (space borel, subsets borel, (\x:real->bool. 0:extreal))` THEN
  SIMP_TAC std_ss [GSYM borel_measurable] THEN MATCH_MP_TAC borel_measurable_add THEN
  Q.EXISTS_TAC `(\x. FST x)` THEN Q.EXISTS_TAC `(\x. SND x)` THEN
  SIMP_TAC std_ss [] THEN CONJ_TAC THENL [METIS_TAC [measure_space_def], ALL_TAC] THEN
  CONJ_TAC THENL
  [SIMP_TAC std_ss [borel_measurable, IN_MEASURABLE, space_def, subsets_def] THEN
   CONJ_TAC THENL [METIS_TAC [measure_space_def], ALL_TAC] THEN
   SIMP_TAC std_ss [sigma_algebra_borel, IN_FUNSET, space_borel, IN_UNIV] THEN
   ASM_SIMP_TAC std_ss [pair_measure, measure_of, m_space_def, measurable_sets_def] THEN
   Q_TAC SUFF_TAC `m_space M CROSS m_space M = UNIV` THENL
   [DISC_RW_KILL,
    Q.UNABBREV_TAC `M` THEN SIMP_TAC std_ss [m_space_def] THEN
    SIMP_TAC std_ss [space_borel, CROSS_DEF, IN_UNIV, GSPEC_T]] THEN
   RW_TAC std_ss [INTER_UNIV] THEN MATCH_MP_TAC sigma_sets_basic THEN
   SIMP_TAC std_ss [PREIMAGE_def, CROSS_DEF, GSPECIFICATION, EXISTS_PROD] THEN
   Q.EXISTS_TAC `s` THEN Q.EXISTS_TAC `UNIV` THEN SIMP_TAC std_ss [IN_UNIV] THEN
   Q.UNABBREV_TAC `M` THEN ASM_SIMP_TAC std_ss [measurable_sets_def] THEN
   SIMP_TAC std_ss [GSYM space_borel] THEN MATCH_MP_TAC ALGEBRA_SPACE THEN
   METIS_TAC [sigma_algebra_def, sigma_algebra_borel], ALL_TAC] THEN
  SIMP_TAC std_ss [borel_measurable, IN_MEASURABLE, space_def, subsets_def] THEN
  CONJ_TAC THENL [METIS_TAC [measure_space_def], ALL_TAC] THEN
  SIMP_TAC std_ss [sigma_algebra_borel, IN_FUNSET, space_borel, IN_UNIV] THEN
  ASM_SIMP_TAC std_ss [pair_measure, measure_of, m_space_def, measurable_sets_def] THEN
  Q_TAC SUFF_TAC `m_space M CROSS m_space M = UNIV` THENL
  [DISC_RW_KILL,
   Q.UNABBREV_TAC `M` THEN SIMP_TAC std_ss [m_space_def] THEN
   SIMP_TAC std_ss [space_borel, CROSS_DEF, IN_UNIV, GSPEC_T]] THEN
  RW_TAC std_ss [INTER_UNIV] THEN MATCH_MP_TAC sigma_sets_basic THEN
  SIMP_TAC std_ss [PREIMAGE_def, CROSS_DEF, GSPECIFICATION, EXISTS_PROD] THEN
  Q.EXISTS_TAC `UNIV` THEN Q.EXISTS_TAC `s` THEN SIMP_TAC std_ss [IN_UNIV] THEN
  Q.UNABBREV_TAC `M` THEN ASM_SIMP_TAC std_ss [measurable_sets_def] THEN
  SIMP_TAC std_ss [GSYM space_borel] THEN MATCH_MP_TAC ALGEBRA_SPACE THEN
  METIS_TAC [sigma_algebra_def, sigma_algebra_borel]);

val distr_pair_swap = store_thm ("distr_pair_swap",
  ``!M1 M2. measure_space M1 /\ measure_space M2 /\
            sigma_finite_measure M1 /\ sigma_finite_measure M2 ==>
            (pair_measure M1 M2 =
      measure_of (distr (pair_measure M2 M1) (pair_measure M1 M2) (\(x,y). (y,x))))``,
  RW_TAC std_ss [] THEN
  Q.ABBREV_TAC `E = {A CROSS B |
       A IN measurable_sets M1 /\ B IN measurable_sets M2}` THEN
  `?f. IMAGE f univ(:num) SUBSET E /\
       (BIGUNION {f i | i IN univ(:num)} =
        m_space M1 CROSS m_space M2) /\
       !i. measure (pair_measure M1 M2) (f i) <> PosInf` by
   METIS_TAC [sigma_finite_up_in_pair_measure_generator] THEN
  Q_TAC SUFF_TAC `E SUBSET POW (m_space M1 CROSS m_space M2)` THENL
  [DISCH_TAC,
   Q.UNABBREV_TAC `E` THEN
   SIMP_TAC std_ss [CROSS_DEF, SUBSET_DEF, POW_DEF, GSPECIFICATION, EXISTS_PROD] THEN
   RW_TAC std_ss [] THEN FULL_SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD] THEN
   `p_1 SUBSET m_space M1` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
   `p_2 SUBSET m_space M2` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
   ASM_SET_TAC []] THEN
  Q_TAC SUFF_TAC `pair_measure M1 M2 = measure_of (pair_measure M1 M2)` THENL
  [DISCH_TAC,
   ASM_SIMP_TAC std_ss [pair_measure] THEN
   Q.ABBREV_TAC `M = (m_space M1 CROSS m_space M2,E,
      (\X. pos_fn_integral M1
           (\x. pos_fn_integral M2 (\y. indicator_fn X (x,y)))))` THEN
   METIS_TAC [measure_of_measure_of, m_space_def, measurable_sets_def]] THEN
  Q_TAC SUFF_TAC `measure_of (pair_measure M1 M2) =
   measure_of (distr (pair_measure M2 M1) (pair_measure M1 M2) (\(x,y). (y,x)))` THENL
  [METIS_TAC [], POP_ASSUM K_TAC] THEN
  MATCH_MP_TAC measure_eqI_generator_eq' THEN Q.EXISTS_TAC `E` THEN
  Q.EXISTS_TAC `m_space M1 CROSS m_space M2` THEN Q.EXISTS_TAC `f` THEN
  `Int_stable E` by METIS_TAC [Int_stable_pair_measure_generator] THEN
  `measure_space (pair_measure M1 M2)` by METIS_TAC [measure_space_pair_measure'] THEN
  `measure_space (pair_measure M2 M1)` by METIS_TAC [measure_space_pair_measure'] THEN
  Q_TAC SUFF_TAC `(\(x,y). (y,x)) IN measurable
   (m_space (pair_measure M2 M1),measurable_sets (pair_measure M2 M1))
   (m_space (pair_measure M1 M2),measurable_sets (pair_measure M1 M2))` THENL
  [DISCH_TAC,
   Q_TAC SUFF_TAC `(\(x,y). (y:'a,x:'b)) = (\z. (SND z, FST z))` THENL
   [DISC_RW_KILL,
    SIMP_TAC std_ss [FUN_EQ_THM] THEN RW_TAC std_ss [] THEN
    `?a b. z = (a,b)` by METIS_TAC [pair_CASES] THEN
    ASM_SIMP_TAC std_ss []] THEN
   MATCH_MP_TAC measurable_Pair THEN ASM_SIMP_TAC std_ss [] THEN
   CONJ_TAC THENL
   [ASM_SIMP_TAC std_ss [IN_MEASURABLE] THEN
    CONJ_TAC THENL [METIS_TAC [measure_space_def], ALL_TAC] THEN
    CONJ_TAC THENL [METIS_TAC [measure_space_def], ALL_TAC] THEN
    SIMP_TAC std_ss [space_def, subsets_def, IN_FUNSET] THEN CONJ_TAC THENL
    [RW_TAC std_ss [pair_measure, measure_of, m_space_def] THEN
     `?a b. x = (a,b)` by METIS_TAC [pair_CASES] THEN
     POP_ASSUM (fn th => POP_ASSUM MP_TAC THEN ASSUME_TAC th) THEN
     ASM_SIMP_TAC std_ss [CROSS_DEF, GSPECIFICATION, EXISTS_PROD],
     ALL_TAC] THEN
    Q_TAC SUFF_TAC `!s. PREIMAGE SND s = UNIV CROSS s` THENL
    [DISCH_TAC,
     RW_TAC std_ss [PREIMAGE_def, EXTENSION, CROSS_DEF] THEN
     SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD, IN_UNIV]] THEN
    SIMP_TAC std_ss [pair_measure, measure_of, m_space_def, measurable_sets_def] THEN
    Q_TAC SUFF_TAC `{a CROSS b | a IN measurable_sets M2 /\ b IN measurable_sets M1}
                   SUBSET POW (m_space M2 CROSS m_space M1)` THENL
    [DISCH_TAC,
     SIMP_TAC std_ss [CROSS_DEF, SUBSET_DEF, POW_DEF, GSPECIFICATION, EXISTS_PROD] THEN
     RW_TAC std_ss [] THEN FULL_SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD] THEN
     `p_1 SUBSET m_space M2` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
     `p_2 SUBSET m_space M1` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
     ASM_SET_TAC []] THEN
    ASM_SIMP_TAC std_ss [CROSS_INTER_CROSS] THEN RW_TAC std_ss [INTER_UNIV] THEN
    `s SUBSET m_space M1` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
    `s INTER m_space M1 = s` by ASM_SET_TAC [] THEN
    ASM_SIMP_TAC std_ss [] THEN MATCH_MP_TAC sigma_sets_basic THEN
    SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD] THEN
    Q.EXISTS_TAC `m_space M2` THEN Q.EXISTS_TAC `s` THEN
    ASM_SIMP_TAC std_ss [MEASURE_SPACE_MSPACE_MEASURABLE],
    ALL_TAC] THEN
   ASM_SIMP_TAC std_ss [IN_MEASURABLE] THEN
   CONJ_TAC THENL [METIS_TAC [measure_space_def], ALL_TAC] THEN
   CONJ_TAC THENL [METIS_TAC [measure_space_def], ALL_TAC] THEN
   SIMP_TAC std_ss [space_def, subsets_def, IN_FUNSET] THEN CONJ_TAC THENL
   [RW_TAC std_ss [pair_measure, measure_of, m_space_def] THEN
    `?a b. x = (a,b)` by METIS_TAC [pair_CASES] THEN
    POP_ASSUM (fn th => POP_ASSUM MP_TAC THEN ASSUME_TAC th) THEN
    ASM_SIMP_TAC std_ss [CROSS_DEF, GSPECIFICATION, EXISTS_PROD],
    ALL_TAC] THEN
   Q_TAC SUFF_TAC `!s:'b->bool. PREIMAGE FST s = s CROSS UNIV` THENL
   [DISCH_TAC,
    RW_TAC std_ss [PREIMAGE_def, EXTENSION, CROSS_DEF] THEN
    SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD, IN_UNIV]] THEN
   SIMP_TAC std_ss [pair_measure, measure_of, m_space_def, measurable_sets_def] THEN
   Q_TAC SUFF_TAC `{a CROSS b | a IN measurable_sets M2 /\ b IN measurable_sets M1}
                  SUBSET POW (m_space M2 CROSS m_space M1)` THENL
   [DISCH_TAC,
    SIMP_TAC std_ss [CROSS_DEF, SUBSET_DEF, POW_DEF, GSPECIFICATION, EXISTS_PROD] THEN
    RW_TAC std_ss [] THEN FULL_SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD] THEN
    `p_1 SUBSET m_space M2` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
    `p_2 SUBSET m_space M1` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
    ASM_SET_TAC []] THEN
   ASM_SIMP_TAC std_ss [CROSS_INTER_CROSS] THEN RW_TAC std_ss [INTER_UNIV] THEN
   `s SUBSET m_space M2` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
   `s INTER m_space M2 = s` by ASM_SET_TAC [] THEN
   ASM_SIMP_TAC std_ss [] THEN MATCH_MP_TAC sigma_sets_basic THEN
   SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD] THEN
   Q.EXISTS_TAC `s` THEN Q.EXISTS_TAC `m_space M1` THEN
   ASM_SIMP_TAC std_ss [MEASURE_SPACE_MSPACE_MEASURABLE]] THEN
  `measure_space
   (distr (pair_measure M2 M1) (pair_measure M1 M2) (\(x,y). (y,x)))` by
   METIS_TAC [measure_space_distr] THEN
  Q_TAC SUFF_TAC `measurable_sets (pair_measure M1 M2) =
                  sigma_sets (m_space M1 CROSS m_space M2) E` THENL
  [DISCH_TAC,
   SIMP_TAC std_ss [pair_measure, measure_of, m_space_def, measurable_sets_def] THEN
   METIS_TAC []] THEN
  Q_TAC SUFF_TAC `measurable_sets
   (distr (pair_measure M2 M1) (pair_measure M1 M2) (\(x,y). (y,x))) =
   sigma_sets (m_space M1 CROSS m_space M2) E` THENL
  [DISCH_TAC THEN ASM_SIMP_TAC std_ss [],
   ASM_SIMP_TAC std_ss [distr, measurable_sets_def]] THEN
  Q.UNABBREV_TAC `E` THEN RW_TAC std_ss [GSPECIFICATION, EXISTS_PROD] THEN
  SIMP_TAC std_ss [distr, measure_def] THEN
  `p_1 SUBSET m_space M1` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
  `p_2 SUBSET m_space M2` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
  Q_TAC SUFF_TAC `PREIMAGE (\(x,y). (y,x)) (p_1 CROSS p_2) INTER
   m_space (pair_measure M2 M1) = p_2 CROSS p_1` THENL
  [DISC_RW_KILL,
   SIMP_TAC std_ss [pair_measure, measure_of, m_space_def] THEN
   SIMP_TAC std_ss [PREIMAGE_def, EXTENSION, INTER_DEF, CROSS_DEF] THEN
   SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD] THEN
   ASM_SET_TAC []] THEN
  ASM_SIMP_TAC std_ss [measure_pair_measure_Times] THEN
  METIS_TAC [mul_comm]);

val convolution_density = store_thm ("convolution_density",
  ``!f g. f IN measurable (m_space lborel, measurable_sets lborel) Borel /\
          g IN measurable (m_space lborel, measurable_sets lborel) Borel /\
          finite_measure (density lborel f) /\ finite_measure (density lborel g) /\
          (!x. 0 <= f x) /\ (!x. 0 <= g x) ==>
          (measure_of (convolution (density lborel f) (density lborel g)) =
           measure_of (density lborel (\x. pos_fn_integral lborel (\y. f (x - y) * g y))))``,
  RW_TAC std_ss [] THEN MATCH_MP_TAC measure_eqI THEN
  ASSUME_TAC measure_space_lborel THEN
  `measure_space (density lborel f)` by METIS_TAC [measure_space_density] THEN
  `measure_space (density lborel g)` by METIS_TAC [measure_space_density] THEN
  Q_TAC SUFF_TAC `sigma_finite_measure (density lborel g)` THENL
  [DISCH_TAC,
   FULL_SIMP_TAC std_ss [sigma_finite_measure, finite_measure] THEN
   Q.EXISTS_TAC `{m_space (density lborel g)}` THEN
   SIMP_TAC std_ss [countable_sing, BIGUNION_SING] THEN
   ASM_SIMP_TAC std_ss [MEASURE_SPACE_MSPACE_MEASURABLE, SUBSET_DEF, IN_SING]] THEN
  CONJ_TAC THENL
  [SIMP_TAC std_ss [convolution] THEN MATCH_MP_TAC measure_space_distr THEN
   ASM_SIMP_TAC std_ss [measure_space_pair_measure', measure_space_borel] THEN
   SIMP_TAC std_ss [m_space_def, measurable_sets_def, SPACE, GSYM borel_measurable] THEN
   Q_TAC SUFF_TAC `(\(x,y). x + y:real) = (\z. FST z + SND z)` THENL
   [DISC_RW_KILL,
    SIMP_TAC std_ss [FUN_EQ_THM] THEN GEN_TAC THEN
    `?a b. z = (a,b)` by METIS_TAC [pair_CASES] THEN ASM_SIMP_TAC std_ss []] THEN
   MATCH_MP_TAC borel_measurable_add THEN Q.EXISTS_TAC `FST` THEN Q.EXISTS_TAC `SND` THEN
   ASM_SIMP_TAC std_ss [] THEN
   `measure_space (pair_measure (density lborel f) (density lborel g))` by
    ASM_SIMP_TAC std_ss [measure_space_pair_measure'] THEN
   CONJ_TAC THENL [METIS_TAC [measure_space_def], ALL_TAC] THEN
   SIMP_TAC std_ss [borel_measurable] THEN CONJ_TAC THENL
   [SIMP_TAC std_ss [IN_MEASURABLE, sigma_algebra_borel] THEN
    CONJ_TAC THENL [METIS_TAC [measure_space_def], ALL_TAC] THEN
    SIMP_TAC std_ss [IN_FUNSET, space_def, subsets_def] THEN CONJ_TAC THENL
    [SIMP_TAC std_ss [space_borel, IN_UNIV], ALL_TAC] THEN
    SIMP_TAC std_ss [pair_measure, measure_of, m_space_def, measurable_sets_def] THEN
    Q.ABBREV_TAC `M1 = density lborel f` THEN
    Q.ABBREV_TAC `M2 = density lborel g` THEN
    Q_TAC SUFF_TAC `!s:real->bool. PREIMAGE FST s = s CROSS univ(:real)` THENL
    [DISCH_TAC,
     RW_TAC std_ss [PREIMAGE_def, EXTENSION, CROSS_DEF] THEN
     SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD, IN_UNIV]] THEN
    Q_TAC SUFF_TAC `{a CROSS b | a IN measurable_sets M1 /\ b IN measurable_sets M2}
                  SUBSET POW (m_space M1 CROSS m_space M2)` THENL
    [DISCH_TAC,
     SIMP_TAC std_ss [CROSS_DEF, SUBSET_DEF, POW_DEF, GSPECIFICATION, EXISTS_PROD] THEN
     RW_TAC std_ss [] THEN FULL_SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD] THEN
     `p_1 SUBSET m_space M1` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
     `p_2 SUBSET m_space M2` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
     ASM_SET_TAC []] THEN
    ASM_SIMP_TAC std_ss [CROSS_INTER_CROSS] THEN RW_TAC std_ss [INTER_UNIV] THEN
    `s IN measurable_sets M1` by METIS_TAC [density, measurable_sets_def, lborel] THEN
    `s SUBSET m_space M1` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
    `s INTER m_space M1 = s` by ASM_SET_TAC [] THEN
    ASM_SIMP_TAC std_ss [] THEN MATCH_MP_TAC sigma_sets_basic THEN
    SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD] THEN
    Q.EXISTS_TAC `s` THEN Q.EXISTS_TAC `m_space M2` THEN
    ASM_SIMP_TAC std_ss [MEASURE_SPACE_MSPACE_MEASURABLE],
    ALL_TAC] THEN
   SIMP_TAC std_ss [IN_MEASURABLE, sigma_algebra_borel] THEN
   CONJ_TAC THENL [METIS_TAC [measure_space_def], ALL_TAC] THEN
   SIMP_TAC std_ss [IN_FUNSET, space_def, subsets_def] THEN CONJ_TAC THENL
   [SIMP_TAC std_ss [space_borel, IN_UNIV], ALL_TAC] THEN
   SIMP_TAC std_ss [pair_measure, measure_of, m_space_def, measurable_sets_def] THEN
   Q.ABBREV_TAC `M1 = density lborel f` THEN
   Q.ABBREV_TAC `M2 = density lborel g` THEN
   Q_TAC SUFF_TAC `!s:real->bool. PREIMAGE SND s = univ(:real) CROSS s` THENL
   [DISCH_TAC,
    RW_TAC std_ss [PREIMAGE_def, EXTENSION, CROSS_DEF] THEN
    SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD, IN_UNIV]] THEN
   Q_TAC SUFF_TAC `{a CROSS b | a IN measurable_sets M1 /\ b IN measurable_sets M2}
                 SUBSET POW (m_space M1 CROSS m_space M2)` THENL
   [DISCH_TAC,
    SIMP_TAC std_ss [CROSS_DEF, SUBSET_DEF, POW_DEF, GSPECIFICATION, EXISTS_PROD] THEN
    RW_TAC std_ss [] THEN FULL_SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD] THEN
    `p_1 SUBSET m_space M1` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
    `p_2 SUBSET m_space M2` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
    ASM_SET_TAC []] THEN
   ASM_SIMP_TAC std_ss [CROSS_INTER_CROSS] THEN RW_TAC std_ss [INTER_UNIV] THEN
   `s IN measurable_sets M2` by METIS_TAC [density, measurable_sets_def, lborel] THEN
   `s SUBSET m_space M2` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
   `s INTER m_space M2 = s` by ASM_SET_TAC [] THEN
   ASM_SIMP_TAC std_ss [] THEN MATCH_MP_TAC sigma_sets_basic THEN
   SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD] THEN
   Q.EXISTS_TAC `m_space M1` THEN Q.EXISTS_TAC `s` THEN
   ASM_SIMP_TAC std_ss [MEASURE_SPACE_MSPACE_MEASURABLE],
   ALL_TAC] THEN

  CONJ_TAC THENL
  [MATCH_MP_TAC measure_space_density THEN SIMP_TAC std_ss [measure_space_lborel] THEN
   Q_TAC SUFF_TAC `(\x. pos_fn_integral lborel (\y. f (x - y) * g y)) =
      (\x. pos_fn_integral lborel (\y. max 0 (if x IN m_space lborel
           then (\(x,y). (\y. f (x - y) * g y) y) (x,y) else 0)))` THENL
   [DISC_RW_KILL,
    ABS_TAC THEN MATCH_MP_TAC positive_integral_cong THEN
    ASM_SIMP_TAC std_ss [le_mul, le_max1] THEN
    SIMP_TAC std_ss [m_space_def, lborel, space_borel, IN_UNIV] THEN
    ASM_SIMP_TAC std_ss [extreal_max_def, le_mul]] THEN
   MATCH_MP_TAC borel_measurable_pos_integral_fst THEN
   ASM_SIMP_TAC std_ss [measure_space_lborel, sigma_finite_measure_lborel] THEN
   CONJ_TAC THENL
   [GEN_TAC THEN `?a b. x = (a,b)` by METIS_TAC [pair_CASES] THEN
    ASM_SIMP_TAC std_ss [le_mul], ALL_TAC] THEN
   Q_TAC SUFF_TAC `(\(x,y). f (x - y) * g y) = (\z. f (FST z - SND z) * g (SND z))` THENL
   [DISC_RW_KILL,
    SIMP_TAC std_ss [FUN_EQ_THM] THEN GEN_TAC THEN
    `?a b. z = (a,b)` by METIS_TAC [pair_CASES] THEN
    ASM_SIMP_TAC std_ss []] THEN
   MATCH_MP_TAC IN_MEASURABLE_BOREL_TIMES THEN
   Q.EXISTS_TAC `(\z. f (FST z - SND z))` THEN Q.EXISTS_TAC `(\z. g (SND z))` THEN
   ASSUME_TAC sigma_finite_measure_lborel THEN
   ASM_SIMP_TAC std_ss [measure_space_pair_measure', GSYM o_DEF] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC MEASURABLE_COMP THEN
    Q.EXISTS_TAC `(m_space lborel,measurable_sets lborel)` THEN
    ASM_SIMP_TAC std_ss [lborel, m_space_def, measurable_sets_def] THEN
    SIMP_TAC std_ss [GSYM lborel, SPACE, GSYM borel_measurable, GSYM space_borel] THEN
    MATCH_MP_TAC borel_measurable_sub THEN Q.EXISTS_TAC `FST` THEN
    Q.EXISTS_TAC `SND` THEN SIMP_TAC std_ss [] THEN
    `measure_space (pair_measure lborel lborel)` by
     ASM_SIMP_TAC std_ss [measure_space_pair_measure'] THEN
    CONJ_TAC THENL [METIS_TAC [measure_space_def], ALL_TAC] THEN
    SIMP_TAC std_ss [borel_measurable] THEN CONJ_TAC THENL
    [SIMP_TAC std_ss [IN_MEASURABLE, sigma_algebra_borel] THEN
     CONJ_TAC THENL [METIS_TAC [measure_space_def], ALL_TAC] THEN
     SIMP_TAC std_ss [IN_FUNSET, space_def, subsets_def] THEN CONJ_TAC THENL
     [SIMP_TAC std_ss [space_borel, IN_UNIV], ALL_TAC] THEN
     SIMP_TAC std_ss [pair_measure, measure_of, m_space_def, measurable_sets_def] THEN
     Q_TAC SUFF_TAC `!s:real->bool. PREIMAGE FST s = s CROSS univ(:real)` THENL
     [DISCH_TAC,
      RW_TAC std_ss [PREIMAGE_def, EXTENSION, CROSS_DEF] THEN
      SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD, IN_UNIV]] THEN
     Q_TAC SUFF_TAC `{a CROSS b | a IN measurable_sets lborel /\ b IN measurable_sets lborel}
                     SUBSET POW (m_space lborel CROSS m_space lborel)` THENL
     [DISCH_TAC,
      SIMP_TAC std_ss [CROSS_DEF, SUBSET_DEF, POW_DEF, GSPECIFICATION, EXISTS_PROD] THEN
      RW_TAC std_ss [] THEN FULL_SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD] THEN
      `p_1 SUBSET m_space lborel` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
      `p_2 SUBSET m_space lborel` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
      ASM_SET_TAC []] THEN
     ASM_SIMP_TAC std_ss [CROSS_INTER_CROSS] THEN RW_TAC std_ss [INTER_UNIV] THEN
     `s IN measurable_sets lborel` by METIS_TAC [density, measurable_sets_def, lborel] THEN
     `s SUBSET m_space lborel` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
     `s INTER m_space lborel = s` by ASM_SET_TAC [] THEN
     ASM_SIMP_TAC std_ss [] THEN MATCH_MP_TAC sigma_sets_basic THEN
     SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD] THEN
     Q.EXISTS_TAC `s` THEN Q.EXISTS_TAC `m_space lborel` THEN
     ASM_SIMP_TAC std_ss [MEASURE_SPACE_MSPACE_MEASURABLE],
     ALL_TAC] THEN
    SIMP_TAC std_ss [IN_MEASURABLE, sigma_algebra_borel] THEN
    CONJ_TAC THENL [METIS_TAC [measure_space_def], ALL_TAC] THEN
    SIMP_TAC std_ss [IN_FUNSET, space_def, subsets_def] THEN CONJ_TAC THENL
    [SIMP_TAC std_ss [space_borel, IN_UNIV], ALL_TAC] THEN
    SIMP_TAC std_ss [pair_measure, measure_of, m_space_def, measurable_sets_def] THEN
    Q_TAC SUFF_TAC `!s:real->bool. PREIMAGE SND s = univ(:real) CROSS s` THENL
    [DISCH_TAC,
     RW_TAC std_ss [PREIMAGE_def, EXTENSION, CROSS_DEF] THEN
     SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD, IN_UNIV]] THEN
    Q_TAC SUFF_TAC `{a CROSS b | a IN measurable_sets lborel /\ b IN measurable_sets lborel}
                    SUBSET POW (m_space lborel CROSS m_space lborel)` THENL
    [DISCH_TAC,
     SIMP_TAC std_ss [CROSS_DEF, SUBSET_DEF, POW_DEF, GSPECIFICATION, EXISTS_PROD] THEN
     RW_TAC std_ss [] THEN FULL_SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD] THEN
     `p_1 SUBSET m_space lborel` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
     `p_2 SUBSET m_space lborel` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
     ASM_SET_TAC []] THEN
    ASM_SIMP_TAC std_ss [CROSS_INTER_CROSS] THEN RW_TAC std_ss [INTER_UNIV] THEN
    `s IN measurable_sets lborel` by METIS_TAC [density, measurable_sets_def, lborel] THEN
    `s SUBSET m_space lborel` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
    `s INTER m_space lborel = s` by ASM_SET_TAC [] THEN
    ASM_SIMP_TAC std_ss [] THEN MATCH_MP_TAC sigma_sets_basic THEN
    SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD] THEN
    Q.EXISTS_TAC `m_space lborel` THEN Q.EXISTS_TAC `s` THEN
    ASM_SIMP_TAC std_ss [MEASURE_SPACE_MSPACE_MEASURABLE],
    ALL_TAC] THEN
   MATCH_MP_TAC MEASURABLE_COMP THEN
   Q.EXISTS_TAC `(m_space lborel,measurable_sets lborel)` THEN
   ASM_SIMP_TAC std_ss [] THEN
   SIMP_TAC std_ss [lborel, m_space_def, measurable_sets_def] THEN
   SIMP_TAC std_ss [GSYM lborel, GSYM space_borel, SPACE] THEN
   SIMP_TAC std_ss [IN_MEASURABLE, sigma_algebra_borel] THEN
   `measure_space (pair_measure lborel lborel)` by
     ASM_SIMP_TAC std_ss [measure_space_pair_measure'] THEN
   CONJ_TAC THENL [METIS_TAC [measure_space_def], ALL_TAC] THEN
   SIMP_TAC std_ss [IN_FUNSET, space_def, subsets_def] THEN CONJ_TAC THENL
   [SIMP_TAC std_ss [space_borel, IN_UNIV], ALL_TAC] THEN
   SIMP_TAC std_ss [pair_measure, measure_of, m_space_def, measurable_sets_def] THEN
   Q_TAC SUFF_TAC `!s:real->bool. PREIMAGE SND s = univ(:real) CROSS s` THENL
   [DISCH_TAC,
    RW_TAC std_ss [PREIMAGE_def, EXTENSION, CROSS_DEF] THEN
    SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD, IN_UNIV]] THEN
   Q_TAC SUFF_TAC `{a CROSS b | a IN measurable_sets lborel /\ b IN measurable_sets lborel}
                   SUBSET POW (m_space lborel CROSS m_space lborel)` THENL
   [DISCH_TAC,
    SIMP_TAC std_ss [CROSS_DEF, SUBSET_DEF, POW_DEF, GSPECIFICATION, EXISTS_PROD] THEN
    RW_TAC std_ss [] THEN FULL_SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD] THEN
    `p_1 SUBSET m_space lborel` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
    `p_2 SUBSET m_space lborel` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
    ASM_SET_TAC []] THEN
   ASM_SIMP_TAC std_ss [CROSS_INTER_CROSS] THEN RW_TAC std_ss [INTER_UNIV] THEN
   `s IN measurable_sets lborel` by METIS_TAC [density, measurable_sets_def, lborel] THEN
   `s SUBSET m_space lborel` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
   `s INTER m_space lborel = s` by ASM_SET_TAC [] THEN
   ASM_SIMP_TAC std_ss [] THEN MATCH_MP_TAC sigma_sets_basic THEN
   SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD] THEN
   Q.EXISTS_TAC `m_space lborel` THEN Q.EXISTS_TAC `s` THEN
   ASM_SIMP_TAC std_ss [MEASURE_SPACE_MSPACE_MEASURABLE],
   ALL_TAC] THEN
  Q_TAC SUFF_TAC
  `(measurable_sets (convolution (density lborel f) (density lborel g)) =
    measurable_sets (density lborel
      (\x. pos_fn_integral lborel (\y. f (x - y) * g y))))` THENL
  [DISCH_TAC THEN ASM_SIMP_TAC std_ss [],
   SIMP_TAC std_ss [convolution, distr, density, measurable_sets_def] THEN
   SIMP_TAC std_ss [lborel, measurable_sets_def]] THEN

  RW_TAC std_ss [] THEN SIMP_TAC std_ss [convolution, density, distr, measure_def] THEN
  `A IN measurable_sets lborel` by METIS_TAC [density, measurable_sets_def] THEN
  ASM_SIMP_TAC std_ss [GSYM density, measure_of, pair_measure] THEN
  SIMP_TAC std_ss [measure_def, measurable_sets_def, m_space_def] THEN
  ASM_SIMP_TAC std_ss [measure_space_pair_measure] THEN
  Q_TAC SUFF_TAC ` PREIMAGE (\(x,y). x + y) A INTER
   (m_space (density lborel f) CROSS m_space (density lborel g)) IN
   sigma_sets
     (m_space (density lborel f) CROSS m_space (density lborel g))
     {a CROSS b |
      a IN measurable_sets (density lborel f) /\
      b IN measurable_sets (density lborel g)}` THENL
  [DISCH_TAC THEN ASM_SIMP_TAC std_ss [],
   Q_TAC SUFF_TAC `(\(x,y). x + y) IN measurable
    (m_space (pair_measure (density lborel f) (density lborel g)),
     measurable_sets (pair_measure (density lborel f) (density lborel g))) borel` THENL
   [RW_TAC std_ss [IN_MEASURABLE, space_def, subsets_def] THEN
    POP_ASSUM MP_TAC THEN
    ASM_SIMP_TAC std_ss [pair_measure, measure_of, m_space_def, measurable_sets_def] THEN
    Q.ABBREV_TAC `M1 = density lborel f` THEN
    Q.ABBREV_TAC `M2 = density lborel g` THEN
    Q_TAC SUFF_TAC `{a CROSS b | a IN measurable_sets M1 /\ b IN measurable_sets M2}
                  SUBSET POW (m_space M1 CROSS m_space M2)` THENL
    [DISCH_TAC,
     SIMP_TAC std_ss [CROSS_DEF, SUBSET_DEF, POW_DEF, GSPECIFICATION, EXISTS_PROD] THEN
     RW_TAC std_ss [] THEN FULL_SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD] THEN
     `p_1 SUBSET m_space M1` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
     `p_2 SUBSET m_space M2` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
     ASM_SET_TAC []] THEN
    ASM_SIMP_TAC std_ss [] THEN DISCH_THEN MATCH_MP_TAC THEN
    METIS_TAC [lborel, measurable_sets_def],
    ALL_TAC] THEN

   SIMP_TAC std_ss [GSYM borel_measurable] THEN
   Q_TAC SUFF_TAC `(\(x,y). x + y:real) = (\z. FST z + SND z)` THENL
   [DISC_RW_KILL,
    SIMP_TAC std_ss [FUN_EQ_THM] THEN GEN_TAC THEN
    `?a b. z = (a,b)` by METIS_TAC [pair_CASES] THEN ASM_SIMP_TAC std_ss []] THEN
   MATCH_MP_TAC borel_measurable_add THEN Q.EXISTS_TAC `FST` THEN Q.EXISTS_TAC `SND` THEN
   ASM_SIMP_TAC std_ss [] THEN
   `measure_space (pair_measure (density lborel f) (density lborel g))` by
    ASM_SIMP_TAC std_ss [measure_space_pair_measure'] THEN
   CONJ_TAC THENL [METIS_TAC [measure_space_def], ALL_TAC] THEN
   SIMP_TAC std_ss [borel_measurable] THEN CONJ_TAC THENL
   [SIMP_TAC std_ss [IN_MEASURABLE, sigma_algebra_borel] THEN
    CONJ_TAC THENL [METIS_TAC [measure_space_def], ALL_TAC] THEN
    SIMP_TAC std_ss [IN_FUNSET, space_def, subsets_def] THEN CONJ_TAC THENL
    [SIMP_TAC std_ss [space_borel, IN_UNIV], ALL_TAC] THEN
    SIMP_TAC std_ss [pair_measure, measure_of, m_space_def, measurable_sets_def] THEN
    Q.ABBREV_TAC `M1 = density lborel f` THEN
    Q.ABBREV_TAC `M2 = density lborel g` THEN
    Q_TAC SUFF_TAC `!s:real->bool. PREIMAGE FST s = s CROSS univ(:real)` THENL
    [DISCH_TAC,
     RW_TAC std_ss [PREIMAGE_def, EXTENSION, CROSS_DEF] THEN
     SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD, IN_UNIV]] THEN
    Q_TAC SUFF_TAC `{a CROSS b | a IN measurable_sets M1 /\ b IN measurable_sets M2}
                  SUBSET POW (m_space M1 CROSS m_space M2)` THENL
    [DISCH_TAC,
     SIMP_TAC std_ss [CROSS_DEF, SUBSET_DEF, POW_DEF, GSPECIFICATION, EXISTS_PROD] THEN
     RW_TAC std_ss [] THEN FULL_SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD] THEN
     `p_1 SUBSET m_space M1` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
     `p_2 SUBSET m_space M2` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
     ASM_SET_TAC []] THEN
    ASM_SIMP_TAC std_ss [CROSS_INTER_CROSS] THEN RW_TAC std_ss [INTER_UNIV] THEN
    `s IN measurable_sets M1` by METIS_TAC [density, measurable_sets_def, lborel] THEN
    `s SUBSET m_space M1` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
    `s INTER m_space M1 = s` by ASM_SET_TAC [] THEN
    ASM_SIMP_TAC std_ss [] THEN MATCH_MP_TAC sigma_sets_basic THEN
    SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD] THEN
    Q.EXISTS_TAC `s` THEN Q.EXISTS_TAC `m_space M2` THEN
    ASM_SIMP_TAC std_ss [MEASURE_SPACE_MSPACE_MEASURABLE],
    ALL_TAC] THEN
   SIMP_TAC std_ss [IN_MEASURABLE, sigma_algebra_borel] THEN
   CONJ_TAC THENL [METIS_TAC [measure_space_def], ALL_TAC] THEN
   SIMP_TAC std_ss [IN_FUNSET, space_def, subsets_def] THEN CONJ_TAC THENL
   [SIMP_TAC std_ss [space_borel, IN_UNIV], ALL_TAC] THEN
   SIMP_TAC std_ss [pair_measure, measure_of, m_space_def, measurable_sets_def] THEN
   Q.ABBREV_TAC `M1 = density lborel f` THEN
   Q.ABBREV_TAC `M2 = density lborel g` THEN
   Q_TAC SUFF_TAC `!s:real->bool. PREIMAGE SND s = univ(:real) CROSS s` THENL
   [DISCH_TAC,
    RW_TAC std_ss [PREIMAGE_def, EXTENSION, CROSS_DEF] THEN
    SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD, IN_UNIV]] THEN
   Q_TAC SUFF_TAC `{a CROSS b | a IN measurable_sets M1 /\ b IN measurable_sets M2}
                 SUBSET POW (m_space M1 CROSS m_space M2)` THENL
   [DISCH_TAC,
    SIMP_TAC std_ss [CROSS_DEF, SUBSET_DEF, POW_DEF, GSPECIFICATION, EXISTS_PROD] THEN
    RW_TAC std_ss [] THEN FULL_SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD] THEN
    `p_1 SUBSET m_space M1` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
    `p_2 SUBSET m_space M2` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
    ASM_SET_TAC []] THEN
   ASM_SIMP_TAC std_ss [CROSS_INTER_CROSS] THEN RW_TAC std_ss [INTER_UNIV] THEN
   `s IN measurable_sets M2` by METIS_TAC [density, measurable_sets_def, lborel] THEN
   `s SUBSET m_space M2` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
   `s INTER m_space M2 = s` by ASM_SET_TAC [] THEN
   ASM_SIMP_TAC std_ss [] THEN MATCH_MP_TAC sigma_sets_basic THEN
   SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD] THEN
   Q.EXISTS_TAC `m_space M1` THEN Q.EXISTS_TAC `s` THEN
   ASM_SIMP_TAC std_ss [MEASURE_SPACE_MSPACE_MEASURABLE]] THEN
  Q_TAC SUFF_TAC `PREIMAGE (\(x,y). x + y) A SUBSET
        m_space (density lborel f) CROSS m_space (density lborel g)` THENL
  [DISCH_TAC,
   SIMP_TAC std_ss [density, m_space_def, lborel, measurable_sets_def] THEN
   SIMP_TAC std_ss [CROSS_DEF, SUBSET_DEF, GSPECIFICATION, EXISTS_PROD] THEN
   METIS_TAC [IN_UNIV, pair_CASES]] THEN
  `PREIMAGE (\(x,y). x + y) A INTER (m_space (density lborel f) CROSS
    m_space (density lborel g)) = PREIMAGE (\(x,y). x + y) A` by ASM_SET_TAC [] THEN
  Q_TAC SUFF_TAC `!x y. indicator_fn (PREIMAGE (\(x,y). x + y) A) (x,y) =
                        indicator_fn A (x + y)` THENL
  [DISCH_TAC THEN ASM_SIMP_TAC std_ss [],
   SIMP_TAC std_ss [indicator_fn_def, IN_PREIMAGE]] THEN
  Q_TAC SUFF_TAC `!x. 0 <= pos_fn_integral (density lborel g) (\y. indicator_fn A (x + y))` THENL
  [DISCH_TAC,
   GEN_TAC THEN MATCH_MP_TAC pos_fn_integral_pos THEN
   ASM_SIMP_TAC std_ss [indicator_fn_pos_le]] THEN
  Q_TAC SUFF_TAC `pos_fn_integral (density lborel f)
   (\x. max 0 ((\x. pos_fn_integral (density lborel g) (\y. indicator_fn A (x + y))) x)) =
   pos_fn_integral lborel
   (\x. max 0 (f x * (\x. pos_fn_integral (density lborel g) (\y. indicator_fn A (x + y))) x))`
  THENL
  [ALL_TAC,
   MATCH_MP_TAC (REWRITE_RULE [GSYM density] pos_fn_integral_density') THEN
   ASM_SIMP_TAC std_ss [GSPEC_T, AE, ae_filter, GSPECIFICATION] THEN
   ASM_SIMP_TAC std_ss [IN_UNIV, GSPEC_F, EMPTY_SUBSET] THEN
   CONJ_TAC THENL
   [Q.EXISTS_TAC `{}` THEN SIMP_TAC std_ss [null_sets, GSPECIFICATION] THEN
    ASM_SIMP_TAC std_ss [MEASURE_SPACE_EMPTY_MEASURABLE] THEN
    METIS_TAC [measure_space_def, positive_def], ALL_TAC] THEN
   Q_TAC SUFF_TAC `!x.
    pos_fn_integral (density lborel g) (\y. indicator_fn A (x + y)) =
    pos_fn_integral (density lborel g) (\y. max 0 (if x IN m_space lborel
     then (\(x,y). indicator_fn A (x + y)) (x,y) else 0))` THENL
   [DISC_RW_KILL,
    GEN_TAC THEN MATCH_MP_TAC positive_integral_cong THEN
    ASM_SIMP_TAC std_ss [indicator_fn_pos_le, le_max1] THEN
    RW_TAC std_ss [lborel, m_space_def, IN_UNIV] THEN
    SIMP_TAC std_ss [extreal_max_def, indicator_fn_pos_le]] THEN
   MATCH_MP_TAC borel_measurable_pos_integral_fst THEN
   ASM_SIMP_TAC std_ss [] THEN CONJ_TAC THENL
   [GEN_TAC THEN `?a b. x = (a,b)` by METIS_TAC [pair_CASES] THEN
    ASM_SIMP_TAC std_ss [indicator_fn_pos_le], ALL_TAC] THEN
   MATCH_MP_TAC IN_MEASURABLE_BOREL_INDICATOR THEN
   Q.EXISTS_TAC `PREIMAGE (\(x,y). x + y) A` THEN
   ASM_SIMP_TAC std_ss [subsets_def] THEN
   `measure_space (pair_measure lborel (density lborel g))` by
    METIS_TAC [measure_space_pair_measure'] THEN
   CONJ_TAC THENL [METIS_TAC [measure_space_def], ALL_TAC] THEN
   CONJ_TAC THENL
   [ALL_TAC,
    RW_TAC std_ss [] THEN `?a b. x = (a,b)` by METIS_TAC [pair_CASES] THEN
    ASM_SIMP_TAC std_ss []] THEN
   Q_TAC SUFF_TAC `(\(x,y). x + y) IN measurable
    (m_space (pair_measure (lborel) (density lborel g)),
     measurable_sets (pair_measure (lborel) (density lborel g))) borel` THENL
   [RW_TAC std_ss [IN_MEASURABLE, space_def, subsets_def] THEN
    POP_ASSUM MP_TAC THEN
    ASM_SIMP_TAC std_ss [pair_measure, measure_of, m_space_def, measurable_sets_def] THEN
    Q.ABBREV_TAC `M2 = density lborel g` THEN
    Q.ABBREV_TAC `M1 = lborel` THEN
    Q_TAC SUFF_TAC `{a CROSS b | a IN measurable_sets M1 /\ b IN measurable_sets M2}
                  SUBSET POW (m_space M1 CROSS m_space M2)` THENL
    [DISCH_TAC,
     SIMP_TAC std_ss [CROSS_DEF, SUBSET_DEF, POW_DEF, GSPECIFICATION, EXISTS_PROD] THEN
     RW_TAC std_ss [] THEN FULL_SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD] THEN
     `p_1 SUBSET m_space M1` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
     `p_2 SUBSET m_space M2` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
     ASM_SET_TAC []] THEN
    ASM_SIMP_TAC std_ss [] THEN DISCH_THEN (MP_TAC o Q.SPEC `A`) THEN
    `A IN subsets borel` by METIS_TAC [measurable_sets_def, lborel] THEN
    FULL_SIMP_TAC std_ss [m_space_def, density],
    ALL_TAC] THEN

   SIMP_TAC std_ss [GSYM borel_measurable] THEN
   Q_TAC SUFF_TAC `(\(x,y). x + y:real) = (\z. FST z + SND z)` THENL
   [DISC_RW_KILL,
    SIMP_TAC std_ss [FUN_EQ_THM] THEN GEN_TAC THEN
    `?a b. z = (a,b)` by METIS_TAC [pair_CASES] THEN ASM_SIMP_TAC std_ss []] THEN
   MATCH_MP_TAC borel_measurable_add THEN Q.EXISTS_TAC `FST` THEN Q.EXISTS_TAC `SND` THEN
   ASM_SIMP_TAC std_ss [] THEN
   CONJ_TAC THENL [METIS_TAC [measure_space_def], ALL_TAC] THEN
   SIMP_TAC std_ss [borel_measurable] THEN CONJ_TAC THENL
   [SIMP_TAC std_ss [IN_MEASURABLE, sigma_algebra_borel] THEN
    CONJ_TAC THENL [METIS_TAC [measure_space_def], ALL_TAC] THEN
    SIMP_TAC std_ss [IN_FUNSET, space_def, subsets_def] THEN CONJ_TAC THENL
    [SIMP_TAC std_ss [space_borel, IN_UNIV], ALL_TAC] THEN
    SIMP_TAC std_ss [pair_measure, measure_of, m_space_def, measurable_sets_def] THEN
    Q.ABBREV_TAC `M1 = lborel` THEN
    Q.ABBREV_TAC `M2 = density M1 g` THEN
    Q_TAC SUFF_TAC `!s:real->bool. PREIMAGE FST s = s CROSS univ(:real)` THENL
    [DISCH_TAC,
     RW_TAC std_ss [PREIMAGE_def, EXTENSION, CROSS_DEF] THEN
     SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD, IN_UNIV]] THEN
    Q_TAC SUFF_TAC `{a CROSS b | a IN measurable_sets M1 /\ b IN measurable_sets M2}
                  SUBSET POW (m_space M1 CROSS m_space M2)` THENL
    [DISCH_TAC,
     SIMP_TAC std_ss [CROSS_DEF, SUBSET_DEF, POW_DEF, GSPECIFICATION, EXISTS_PROD] THEN
     RW_TAC std_ss [] THEN FULL_SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD] THEN
     `p_1 SUBSET m_space M1` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
     `p_2 SUBSET m_space M2` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
     ASM_SET_TAC []] THEN
    ASM_SIMP_TAC std_ss [CROSS_INTER_CROSS] THEN RW_TAC std_ss [INTER_UNIV] THEN
    `s IN measurable_sets M1` by METIS_TAC [density, measurable_sets_def, lborel] THEN
    `s SUBSET m_space M1` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
    `s INTER m_space M1 = s` by ASM_SET_TAC [] THEN
    ASM_SIMP_TAC std_ss [] THEN MATCH_MP_TAC sigma_sets_basic THEN
    SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD] THEN
    Q.EXISTS_TAC `s` THEN Q.EXISTS_TAC `m_space M2` THEN
    ASM_SIMP_TAC std_ss [MEASURE_SPACE_MSPACE_MEASURABLE],
    ALL_TAC] THEN
   SIMP_TAC std_ss [IN_MEASURABLE, sigma_algebra_borel] THEN
   CONJ_TAC THENL [METIS_TAC [measure_space_def], ALL_TAC] THEN
   SIMP_TAC std_ss [IN_FUNSET, space_def, subsets_def] THEN CONJ_TAC THENL
   [SIMP_TAC std_ss [space_borel, IN_UNIV], ALL_TAC] THEN
   SIMP_TAC std_ss [pair_measure, measure_of, m_space_def, measurable_sets_def] THEN
   Q.ABBREV_TAC `M1 = lborel` THEN
   Q.ABBREV_TAC `M2 = density M1 g` THEN
   Q_TAC SUFF_TAC `!s:real->bool. PREIMAGE SND s = univ(:real) CROSS s` THENL
   [DISCH_TAC,
    RW_TAC std_ss [PREIMAGE_def, EXTENSION, CROSS_DEF] THEN
    SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD, IN_UNIV]] THEN
   Q_TAC SUFF_TAC `{a CROSS b | a IN measurable_sets M1 /\ b IN measurable_sets M2}
                 SUBSET POW (m_space M1 CROSS m_space M2)` THENL
   [DISCH_TAC,
    SIMP_TAC std_ss [CROSS_DEF, SUBSET_DEF, POW_DEF, GSPECIFICATION, EXISTS_PROD] THEN
    RW_TAC std_ss [] THEN FULL_SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD] THEN
    `p_1 SUBSET m_space M1` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
    `p_2 SUBSET m_space M2` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
    ASM_SET_TAC []] THEN
   ASM_SIMP_TAC std_ss [CROSS_INTER_CROSS] THEN RW_TAC std_ss [INTER_UNIV] THEN
   `s IN measurable_sets M2` by METIS_TAC [density, measurable_sets_def, lborel] THEN
   `s SUBSET m_space M2` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
   `s INTER m_space M2 = s` by ASM_SET_TAC [] THEN
   ASM_SIMP_TAC std_ss [] THEN MATCH_MP_TAC sigma_sets_basic THEN
   SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD] THEN
   Q.EXISTS_TAC `m_space M1` THEN Q.EXISTS_TAC `s` THEN
   ASM_SIMP_TAC std_ss [MEASURE_SPACE_MSPACE_MEASURABLE]] THEN
  ASM_SIMP_TAC std_ss [extreal_max_def, le_mul] THEN DISC_RW_KILL THEN
  SIMP_TAC std_ss [GSYM extreal_max_def] THEN

  Q_TAC SUFF_TAC
  `!x. f x * pos_fn_integral (density lborel g) (\y. max 0 ((\y. indicator_fn A (x + y)) y)) =
   pos_fn_integral (density lborel g) (\y. max 0 (f x * (\y. indicator_fn A (x + y)) y))` THENL
  [ALL_TAC,
   GEN_TAC THEN
   MATCH_MP_TAC (GSYM pos_fn_integral_cmult) THEN ASM_SIMP_TAC std_ss [] THEN
   MATCH_MP_TAC IN_MEASURABLE_BOREL_INDICATOR THEN Q.EXISTS_TAC `PREIMAGE (\y. x + y) A` THEN
   ASM_SIMP_TAC std_ss [subsets_def] THEN
   CONJ_TAC THENL [METIS_TAC [measure_space_def], ALL_TAC] THEN
   CONJ_TAC THENL [ALL_TAC, SIMP_TAC std_ss [indicator_fn_def, IN_PREIMAGE]] THEN
   SIMP_TAC std_ss [density, measurable_sets_def, lborel] THEN
   Q_TAC SUFF_TAC `(\y. x + y) IN measurable borel borel` THENL
   [RW_TAC std_ss [IN_MEASURABLE, space_borel, INTER_UNIV] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN METIS_TAC [lborel, measurable_sets_def],
    ALL_TAC] THEN
   SIMP_TAC std_ss [GSYM borel_measurable] THEN MATCH_MP_TAC borel_measurable_add THEN
   Q.EXISTS_TAC `(\y. x)` THEN Q.EXISTS_TAC `(\y. y)` THEN ASM_SIMP_TAC std_ss [] THEN
   SIMP_TAC std_ss [sigma_algebra_borel, borel_measurable_const] THEN
   SIMP_TAC std_ss [borel_measurable, METIS [I_THM] ``(\y. y) = I``] THEN
   MATCH_MP_TAC MEASURABLE_I THEN SIMP_TAC std_ss [sigma_algebra_borel]] THEN
  SIMP_TAC std_ss [extreal_max_def, indicator_fn_pos_le] THEN
  DISC_RW_KILL THEN SIMP_TAC std_ss [GSYM extreal_max_def] THEN

  Q_TAC SUFF_TAC `!x. pos_fn_integral (density lborel g)
    (\y. max 0 ((\y. f x * indicator_fn A (x + y)) y)) =
   pos_fn_integral lborel (\y. max 0 ( g y * (\y. f x * indicator_fn A (x + y)) y))` THENL
  [SIMP_TAC std_ss [] THEN DISC_RW_KILL,
   GEN_TAC THEN MATCH_MP_TAC (REWRITE_RULE [GSYM density] pos_fn_integral_density') THEN
   ASM_SIMP_TAC std_ss [le_mul, indicator_fn_pos_le] THEN
   ASM_SIMP_TAC std_ss [GSPEC_T, AE, ae_filter, GSPECIFICATION] THEN
   ASM_SIMP_TAC std_ss [IN_UNIV, GSPEC_F, EMPTY_SUBSET] THEN
   CONJ_TAC THENL
   [Q.EXISTS_TAC `{}` THEN SIMP_TAC std_ss [null_sets, GSPECIFICATION] THEN
    ASM_SIMP_TAC std_ss [MEASURE_SPACE_EMPTY_MEASURABLE] THEN
    METIS_TAC [measure_space_def, positive_def], ALL_TAC] THEN
   MATCH_MP_TAC IN_MEASURABLE_BOREL_TIMES THEN
   Q.EXISTS_TAC `(\y. f x)` THEN Q.EXISTS_TAC `(\y. indicator_fn A (x + y))` THEN
   ASM_SIMP_TAC std_ss [] THEN CONJ_TAC THENL
   [MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST THEN METIS_TAC [measure_space_def],
    ALL_TAC] THEN
   MATCH_MP_TAC IN_MEASURABLE_BOREL_INDICATOR THEN
   Q.EXISTS_TAC `PREIMAGE (\y. x + y) A` THEN
   ASM_SIMP_TAC std_ss [subsets_def] THEN
   CONJ_TAC THENL [METIS_TAC [measure_space_def], ALL_TAC] THEN
   CONJ_TAC THENL [ALL_TAC, SIMP_TAC std_ss [indicator_fn_def, IN_PREIMAGE]] THEN
   SIMP_TAC std_ss [density, measurable_sets_def, lborel] THEN
   Q_TAC SUFF_TAC `(\y. x + y) IN measurable borel borel` THENL
   [RW_TAC std_ss [IN_MEASURABLE, space_borel, INTER_UNIV] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN METIS_TAC [lborel, measurable_sets_def],
    ALL_TAC] THEN
   SIMP_TAC std_ss [GSYM borel_measurable] THEN MATCH_MP_TAC borel_measurable_add THEN
   Q.EXISTS_TAC `(\y. x)` THEN Q.EXISTS_TAC `(\y. y)` THEN ASM_SIMP_TAC std_ss [] THEN
   SIMP_TAC std_ss [sigma_algebra_borel, borel_measurable_const] THEN
   SIMP_TAC std_ss [borel_measurable, METIS [I_THM] ``(\y. y) = I``] THEN
   MATCH_MP_TAC MEASURABLE_I THEN SIMP_TAC std_ss [sigma_algebra_borel]] THEN

  Q_TAC SUFF_TAC `pos_fn_integral lborel
   (\x. pos_fn_integral lborel (\y. (\(x,y). max 0 (g y * (f x * indicator_fn A (x + y)))) (x,y))) =
                  pos_fn_integral lborel
   (\y. pos_fn_integral lborel (\x. (\(x,y). max 0 (g y * (f x * indicator_fn A (x + y)))) (x,y)))`
  THENL
  [SIMP_TAC std_ss [] THEN DISC_RW_KILL,
   MATCH_MP_TAC fubini THEN ASM_SIMP_TAC std_ss [sigma_finite_measure_lborel] THEN
   CONJ_TAC THENL
   [GEN_TAC THEN `?a b. x = (a,b)` by METIS_TAC [pair_CASES] THEN
    ASM_SIMP_TAC std_ss [le_max1], ALL_TAC] THEN
   Q_TAC SUFF_TAC `(\(x,y). max 0 (g y * (f x * indicator_fn A (x + y)))) =
          (\z. max 0 (g (SND z) * (f (FST z) * indicator_fn A (FST z + SND z))))` THENL
   [DISC_RW_KILL,
    SIMP_TAC std_ss [FUN_EQ_THM] THEN GEN_TAC THEN
    `?a b. z = (a,b)` by METIS_TAC [pair_CASES] THEN ASM_SIMP_TAC std_ss []] THEN
   Q_TAC SUFF_TAC `(\z. max ((\z. 0) z)
                   ((\z. (g (SND z) * (f (FST z) * indicator_fn A (FST z + SND z)))) z)) IN
    measurable (m_space (pair_measure lborel lborel),
                measurable_sets (pair_measure lborel lborel)) Borel` THENL
   [SIMP_TAC std_ss [], ALL_TAC] THEN
   MATCH_MP_TAC IN_MEASURABLE_BOREL_MAX THEN
   `measure_space (pair_measure lborel lborel)` by
    METIS_TAC [measure_space_pair_measure', sigma_finite_measure_lborel] THEN
   CONJ_TAC THENL [METIS_TAC [measure_space_def], ALL_TAC] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST THEN
    METIS_TAC [measure_space_def], ALL_TAC] THEN
   MATCH_MP_TAC IN_MEASURABLE_BOREL_TIMES THEN Q.EXISTS_TAC `(\z. g (SND z))` THEN
   Q.EXISTS_TAC `(\z. f (FST z) * indicator_fn A (FST z + SND z))` THEN
   ASM_SIMP_TAC std_ss [] THEN CONJ_TAC THENL
   [SIMP_TAC std_ss [GSYM o_DEF] THEN MATCH_MP_TAC MEASURABLE_COMP THEN
    Q.EXISTS_TAC `(m_space lborel,measurable_sets lborel)` THEN ASM_SIMP_TAC std_ss [] THEN
    SIMP_TAC std_ss [IN_MEASURABLE, sigma_algebra_borel] THEN
    CONJ_TAC THENL [METIS_TAC [measure_space_def], ALL_TAC] THEN
    CONJ_TAC THENL [METIS_TAC [measure_space_def], ALL_TAC] THEN
    SIMP_TAC std_ss [IN_FUNSET, space_def, subsets_def] THEN CONJ_TAC THENL
    [SIMP_TAC std_ss [IN_UNIV, space_def, lborel, m_space_def], ALL_TAC] THEN
    SIMP_TAC std_ss [pair_measure, measure_of, m_space_def, measurable_sets_def] THEN
    Q.ABBREV_TAC `M = lborel` THEN
    Q_TAC SUFF_TAC `!s:real->bool. PREIMAGE SND s = univ(:real) CROSS s` THENL
    [DISCH_TAC,
     RW_TAC std_ss [PREIMAGE_def, EXTENSION, CROSS_DEF] THEN
     SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD, IN_UNIV]] THEN
    Q_TAC SUFF_TAC `{a CROSS b | a IN measurable_sets M /\ b IN measurable_sets M}
                  SUBSET POW (m_space M CROSS m_space M)` THENL
    [DISCH_TAC,
     SIMP_TAC std_ss [CROSS_DEF, SUBSET_DEF, POW_DEF, GSPECIFICATION, EXISTS_PROD] THEN
     RW_TAC std_ss [] THEN FULL_SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD] THEN
     `p_1 SUBSET m_space M` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
     `p_2 SUBSET m_space M` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
     ASM_SET_TAC []] THEN
    ASM_SIMP_TAC std_ss [CROSS_INTER_CROSS] THEN RW_TAC std_ss [INTER_UNIV] THEN
    `s IN measurable_sets M` by METIS_TAC [density, measurable_sets_def, lborel] THEN
    `s SUBSET m_space M` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
    `s INTER m_space M = s` by ASM_SET_TAC [] THEN
    ASM_SIMP_TAC std_ss [] THEN MATCH_MP_TAC sigma_sets_basic THEN
    SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD] THEN
    Q.EXISTS_TAC `m_space M` THEN Q.EXISTS_TAC `s` THEN
    ASM_SIMP_TAC std_ss [MEASURE_SPACE_MSPACE_MEASURABLE],
    ALL_TAC] THEN
   MATCH_MP_TAC IN_MEASURABLE_BOREL_TIMES THEN Q.EXISTS_TAC `(\z. f (FST z))` THEN
   Q.EXISTS_TAC `(\z. indicator_fn A (FST z + SND z))` THEN
   ASM_SIMP_TAC std_ss [] THEN CONJ_TAC THENL
   [SIMP_TAC std_ss [GSYM o_DEF] THEN MATCH_MP_TAC MEASURABLE_COMP THEN
    Q.EXISTS_TAC `(m_space lborel,measurable_sets lborel)` THEN ASM_SIMP_TAC std_ss [] THEN
    SIMP_TAC std_ss [IN_MEASURABLE, sigma_algebra_borel] THEN
    CONJ_TAC THENL [METIS_TAC [measure_space_def], ALL_TAC] THEN
    CONJ_TAC THENL [METIS_TAC [measure_space_def], ALL_TAC] THEN
    SIMP_TAC std_ss [IN_FUNSET, space_def, subsets_def] THEN CONJ_TAC THENL
    [SIMP_TAC std_ss [IN_UNIV, space_def, lborel, m_space_def], ALL_TAC] THEN
    SIMP_TAC std_ss [pair_measure, measure_of, m_space_def, measurable_sets_def] THEN
    Q.ABBREV_TAC `M = lborel` THEN
    Q_TAC SUFF_TAC `!s:real->bool. PREIMAGE FST s = s CROSS univ(:real)` THENL
    [DISCH_TAC,
     RW_TAC std_ss [PREIMAGE_def, EXTENSION, CROSS_DEF] THEN
     SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD, IN_UNIV]] THEN
    Q_TAC SUFF_TAC `{a CROSS b | a IN measurable_sets M /\ b IN measurable_sets M}
                  SUBSET POW (m_space M CROSS m_space M)` THENL
    [DISCH_TAC,
     SIMP_TAC std_ss [CROSS_DEF, SUBSET_DEF, POW_DEF, GSPECIFICATION, EXISTS_PROD] THEN
     RW_TAC std_ss [] THEN FULL_SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD] THEN
     `p_1 SUBSET m_space M` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
     `p_2 SUBSET m_space M` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
     ASM_SET_TAC []] THEN
    ASM_SIMP_TAC std_ss [CROSS_INTER_CROSS] THEN RW_TAC std_ss [INTER_UNIV] THEN
    `s IN measurable_sets M` by METIS_TAC [density, measurable_sets_def, lborel] THEN
    `s SUBSET m_space M` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
    `s INTER m_space M = s` by ASM_SET_TAC [] THEN
    ASM_SIMP_TAC std_ss [] THEN MATCH_MP_TAC sigma_sets_basic THEN
    SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD] THEN
    Q.EXISTS_TAC `s` THEN Q.EXISTS_TAC `m_space M` THEN
    ASM_SIMP_TAC std_ss [MEASURE_SPACE_MSPACE_MEASURABLE],
    ALL_TAC] THEN
   MATCH_MP_TAC IN_MEASURABLE_BOREL_INDICATOR THEN
   Q.EXISTS_TAC `PREIMAGE (\z. FST z + SND z) A` THEN SIMP_TAC std_ss [subsets_def] THEN
   CONJ_TAC THENL [METIS_TAC [measure_space_def], ALL_TAC] THEN
   CONJ_TAC THENL [ALL_TAC, RW_TAC std_ss [indicator_fn_def, IN_PREIMAGE]] THEN
   Q_TAC SUFF_TAC `(\z. FST z + SND z) = (\(x,y). x + y:real)` THENL
   [DISC_RW_KILL,
    SIMP_TAC std_ss [FUN_EQ_THM] THEN GEN_TAC THEN
    `?a b. z = (a,b)` by METIS_TAC [pair_CASES] THEN ASM_SIMP_TAC std_ss []] THEN
   Q.ABBREV_TAC `M = lborel` THEN
   Q_TAC SUFF_TAC `(\(x,y). x + y) IN measurable
    (m_space (pair_measure M M), measurable_sets (pair_measure M M))
    (m_space M, measurable_sets M)` THENL
   [RW_TAC std_ss [IN_MEASURABLE, space_def, subsets_def] THEN
    POP_ASSUM MP_TAC THEN
    ASM_SIMP_TAC std_ss [pair_measure, measure_of, m_space_def, measurable_sets_def] THEN
    Q_TAC SUFF_TAC `{a CROSS b | a IN measurable_sets M /\ b IN measurable_sets M}
                  SUBSET POW (m_space M CROSS m_space M)` THENL
    [DISCH_TAC,
     SIMP_TAC std_ss [CROSS_DEF, SUBSET_DEF, POW_DEF, GSPECIFICATION, EXISTS_PROD] THEN
     RW_TAC std_ss [] THEN FULL_SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD] THEN
     `p_1 SUBSET m_space M` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
     `p_2 SUBSET m_space M` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
     ASM_SET_TAC []] THEN
    ASM_SIMP_TAC std_ss [] THEN DISCH_THEN (MP_TAC o Q.SPEC `A`) THEN
    `A IN subsets borel` by METIS_TAC [measurable_sets_def, lborel] THEN
    FULL_SIMP_TAC std_ss [m_space_def, density],
    ALL_TAC] THEN
   Q.UNABBREV_TAC `M` THEN SIMP_TAC std_ss [lborel, m_space_def, measurable_sets_def] THEN
   SIMP_TAC std_ss [GSYM lborel, GSYM space_borel, SPACE, GSYM borel_measurable] THEN
   Q_TAC SUFF_TAC `(\(x,y). x + y:real) = (\z. FST z + SND z)` THENL
   [DISC_RW_KILL,
    SIMP_TAC std_ss [FUN_EQ_THM] THEN GEN_TAC THEN
    `?a b. z = (a,b)` by METIS_TAC [pair_CASES] THEN ASM_SIMP_TAC std_ss []] THEN

    MATCH_MP_TAC borel_measurable_add THEN Q.EXISTS_TAC `FST` THEN Q.EXISTS_TAC `SND` THEN
    ASM_SIMP_TAC std_ss [] THEN
    CONJ_TAC THENL [METIS_TAC [measure_space_def], ALL_TAC] THEN
    SIMP_TAC std_ss [borel_measurable] THEN CONJ_TAC THENL
    [SIMP_TAC std_ss [IN_MEASURABLE, sigma_algebra_borel] THEN
     CONJ_TAC THENL [METIS_TAC [measure_space_def], ALL_TAC] THEN
     SIMP_TAC std_ss [IN_FUNSET, space_def, subsets_def] THEN CONJ_TAC THENL
     [SIMP_TAC std_ss [space_borel, IN_UNIV], ALL_TAC] THEN
     SIMP_TAC std_ss [pair_measure, measure_of, m_space_def, measurable_sets_def] THEN
     Q.ABBREV_TAC `M = lborel` THEN
     Q_TAC SUFF_TAC `!s:real->bool. PREIMAGE FST s = s CROSS univ(:real)` THENL
     [DISCH_TAC,
      RW_TAC std_ss [PREIMAGE_def, EXTENSION, CROSS_DEF] THEN
      SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD, IN_UNIV]] THEN
     Q_TAC SUFF_TAC `{a CROSS b | a IN measurable_sets M /\ b IN measurable_sets M}
                   SUBSET POW (m_space M CROSS m_space M)` THENL
     [DISCH_TAC,
      SIMP_TAC std_ss [CROSS_DEF, SUBSET_DEF, POW_DEF, GSPECIFICATION, EXISTS_PROD] THEN
      RW_TAC std_ss [] THEN FULL_SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD] THEN
      `p_1 SUBSET m_space M` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
      `p_2 SUBSET m_space M` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
      ASM_SET_TAC []] THEN
     ASM_SIMP_TAC std_ss [CROSS_INTER_CROSS] THEN RW_TAC std_ss [INTER_UNIV] THEN
     `s IN measurable_sets M` by METIS_TAC [density, measurable_sets_def, lborel] THEN
     `s SUBSET m_space M` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
     `s INTER m_space M = s` by ASM_SET_TAC [] THEN
     ASM_SIMP_TAC std_ss [] THEN MATCH_MP_TAC sigma_sets_basic THEN
     SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD] THEN
     Q.EXISTS_TAC `s` THEN Q.EXISTS_TAC `m_space M` THEN
     ASM_SIMP_TAC std_ss [MEASURE_SPACE_MSPACE_MEASURABLE],
     ALL_TAC] THEN
   SIMP_TAC std_ss [IN_MEASURABLE, sigma_algebra_borel] THEN
   CONJ_TAC THENL [METIS_TAC [measure_space_def], ALL_TAC] THEN
   SIMP_TAC std_ss [IN_FUNSET, space_def, subsets_def] THEN CONJ_TAC THENL
   [SIMP_TAC std_ss [space_borel, IN_UNIV], ALL_TAC] THEN
   SIMP_TAC std_ss [pair_measure, measure_of, m_space_def, measurable_sets_def] THEN
   Q.ABBREV_TAC `M = lborel` THEN
   Q_TAC SUFF_TAC `!s:real->bool. PREIMAGE SND s = univ(:real) CROSS s` THENL
   [DISCH_TAC,
    RW_TAC std_ss [PREIMAGE_def, EXTENSION, CROSS_DEF] THEN
    SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD, IN_UNIV]] THEN
   Q_TAC SUFF_TAC `{a CROSS b | a IN measurable_sets M /\ b IN measurable_sets M}
                 SUBSET POW (m_space M CROSS m_space M)` THENL
   [DISCH_TAC,
    SIMP_TAC std_ss [CROSS_DEF, SUBSET_DEF, POW_DEF, GSPECIFICATION, EXISTS_PROD] THEN
    RW_TAC std_ss [] THEN FULL_SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD] THEN
    `p_1 SUBSET m_space M` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
    `p_2 SUBSET m_space M` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
    ASM_SET_TAC []] THEN
   ASM_SIMP_TAC std_ss [CROSS_INTER_CROSS] THEN RW_TAC std_ss [INTER_UNIV] THEN
   `s IN measurable_sets M` by METIS_TAC [density, measurable_sets_def, lborel] THEN
   `s SUBSET m_space M` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
   `s INTER m_space M = s` by ASM_SET_TAC [] THEN
   ASM_SIMP_TAC std_ss [] THEN MATCH_MP_TAC sigma_sets_basic THEN
   SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD] THEN
   Q.EXISTS_TAC `m_space M` THEN Q.EXISTS_TAC `s` THEN
   ASM_SIMP_TAC std_ss [MEASURE_SPACE_MSPACE_MEASURABLE]] THEN

  Q_TAC SUFF_TAC `!y. pos_fn_integral lborel
   (\x. max 0 (g y * ((\x. f x * indicator_fn A (x + y)) x))) =
                g y * pos_fn_integral lborel
   (\x. max 0 ((\x. f x * indicator_fn A (x + y)) x))` THENL
  [SIMP_TAC std_ss [] THEN DISC_RW_KILL,
   GEN_TAC THEN MATCH_MP_TAC pos_fn_integral_cmult THEN
   ASM_SIMP_TAC std_ss [] THEN MATCH_MP_TAC IN_MEASURABLE_BOREL_TIMES THEN
   Q.EXISTS_TAC `f` THEN Q.EXISTS_TAC `(\x. indicator_fn A (x + y))` THEN
   ASM_SIMP_TAC std_ss [] THEN
   MATCH_MP_TAC IN_MEASURABLE_BOREL_INDICATOR THEN
   Q.EXISTS_TAC `PREIMAGE (\x. x + y) A` THEN
   ASM_SIMP_TAC std_ss [subsets_def] THEN
   CONJ_TAC THENL [METIS_TAC [measure_space_def], ALL_TAC] THEN
   CONJ_TAC THENL [ALL_TAC, SIMP_TAC std_ss [indicator_fn_def, IN_PREIMAGE]] THEN
   SIMP_TAC std_ss [density, measurable_sets_def, lborel] THEN
   Q_TAC SUFF_TAC `(\x. x + y) IN measurable borel borel` THENL
   [RW_TAC std_ss [IN_MEASURABLE, space_borel, INTER_UNIV] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN METIS_TAC [lborel, measurable_sets_def],
    ALL_TAC] THEN
   SIMP_TAC std_ss [GSYM borel_measurable] THEN MATCH_MP_TAC borel_measurable_add THEN
   Q.EXISTS_TAC `(\x. x)` THEN Q.EXISTS_TAC `(\x. y)` THEN ASM_SIMP_TAC std_ss [] THEN
   SIMP_TAC std_ss [sigma_algebra_borel, borel_measurable_const] THEN
   SIMP_TAC std_ss [borel_measurable, METIS [I_THM] ``(\y. y) = I``] THEN
   MATCH_MP_TAC MEASURABLE_I THEN SIMP_TAC std_ss [sigma_algebra_borel]] THEN

  Q_TAC SUFF_TAC `!y. pos_fn_integral lborel (\x. max 0 ((\x. f x * indicator_fn A (x + y)) x)) =
     Normal (abs 1) * pos_fn_integral lborel
     (\x. max 0 ((\x. f x * indicator_fn A (x + y)) (-y + 1 * x)))` THENL
  [SIMP_TAC std_ss [] THEN DISC_RW_KILL,
   GEN_TAC THEN MATCH_MP_TAC lebesgue_pos_integral_real_affine THEN
   SIMP_TAC real_ss [] THEN
   ONCE_REWRITE_TAC [METIS [m_space_def, measurable_sets_def, SPACE] ``borel =
    (m_space (space borel, subsets borel, (\x. 0)),
     measurable_sets (space borel, subsets borel, (\x. 0)))``] THEN
   MATCH_MP_TAC IN_MEASURABLE_BOREL_TIMES THEN
   Q.EXISTS_TAC `f` THEN Q.EXISTS_TAC `(\x. indicator_fn A (x + y))` THEN
   ASM_SIMP_TAC std_ss [measure_space_borel] THEN
   CONJ_TAC THENL
   [METIS_TAC [m_space_def, measurable_sets_def, lborel, space_borel], ALL_TAC] THEN
   MATCH_MP_TAC IN_MEASURABLE_BOREL_INDICATOR THEN
   Q.EXISTS_TAC `PREIMAGE (\x. x + y) A` THEN
   ASM_SIMP_TAC std_ss [subsets_def, m_space_def, measurable_sets_def] THEN
   SIMP_TAC std_ss [space_def, sigma_algebra_borel, SPACE] THEN
   CONJ_TAC THENL [ALL_TAC, SIMP_TAC std_ss [indicator_fn_def, IN_PREIMAGE]] THEN
   SIMP_TAC std_ss [density, measurable_sets_def, lborel] THEN
   Q_TAC SUFF_TAC `(\x. x + y) IN measurable borel borel` THENL
   [RW_TAC std_ss [IN_MEASURABLE, space_borel, INTER_UNIV] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN METIS_TAC [lborel, measurable_sets_def],
    ALL_TAC] THEN
   SIMP_TAC std_ss [GSYM borel_measurable] THEN MATCH_MP_TAC borel_measurable_add THEN
   Q.EXISTS_TAC `(\x. x)` THEN Q.EXISTS_TAC `(\x. y)` THEN ASM_SIMP_TAC std_ss [] THEN
   SIMP_TAC std_ss [sigma_algebra_borel, borel_measurable_const] THEN
   SIMP_TAC std_ss [borel_measurable, METIS [I_THM] ``(\y. y) = I``] THEN
   MATCH_MP_TAC MEASURABLE_I THEN SIMP_TAC std_ss [sigma_algebra_borel]] THEN
  SIMP_TAC real_ss [REAL_ARITH ``-y + x = x - y:real``] THEN
  SIMP_TAC std_ss [GSYM extreal_of_num_def, mul_lone] THEN

  Q_TAC SUFF_TAC `!y. g y * pos_fn_integral lborel
   (\x. max 0 ((\x. f (x - y) * indicator_fn A x) x)) =
                            pos_fn_integral lborel
   (\x. max 0 (g y * ((\x. f (x - y) * indicator_fn A x) x)))` THENL
  [SIMP_TAC std_ss [] THEN DISC_RW_KILL,
   GEN_TAC THEN MATCH_MP_TAC (GSYM pos_fn_integral_cmult) THEN
   ASM_SIMP_TAC std_ss [] THEN MATCH_MP_TAC IN_MEASURABLE_BOREL_TIMES THEN
   Q.EXISTS_TAC `(\x. f (x - y))` THEN Q.EXISTS_TAC `(\x. indicator_fn A x)` THEN
   ASM_SIMP_TAC std_ss [] THEN
   CONJ_TAC THENL
   [ALL_TAC,
    MATCH_MP_TAC IN_MEASURABLE_BOREL_INDICATOR THEN Q.EXISTS_TAC `A` THEN
    ASM_SIMP_TAC std_ss [subsets_def] THEN
    METIS_TAC [measure_space_def]] THEN
   SIMP_TAC std_ss [GSYM o_DEF] THEN MATCH_MP_TAC MEASURABLE_COMP THEN
   Q.EXISTS_TAC `(m_space lborel,measurable_sets lborel)` THEN
   ASM_SIMP_TAC std_ss [] THEN
   SIMP_TAC std_ss [GSYM space_borel, m_space_def, measurable_sets_def, lborel] THEN
   SIMP_TAC std_ss [SPACE, GSYM borel_measurable] THEN MATCH_MP_TAC borel_measurable_sub THEN
   Q.EXISTS_TAC `(\x. x)` THEN Q.EXISTS_TAC `(\x. y)` THEN ASM_SIMP_TAC std_ss [] THEN
   SIMP_TAC std_ss [sigma_algebra_borel, borel_measurable_const] THEN
   SIMP_TAC std_ss [borel_measurable, METIS [I_THM] ``(\y. y) = I``] THEN
   MATCH_MP_TAC MEASURABLE_I THEN SIMP_TAC std_ss [sigma_algebra_borel]] THEN

  Q_TAC SUFF_TAC `pos_fn_integral lborel
   (\y. pos_fn_integral lborel
       (\x. (\(x,y). max 0 (g y * (f (x - y) * indicator_fn A x))) (x,y))) =
                  pos_fn_integral lborel
   (\x. pos_fn_integral lborel
       (\y. (\(x,y). max 0 (g y * (f (x - y) * indicator_fn A x))) (x,y)))` THENL
  [SIMP_TAC std_ss [] THEN DISC_RW_KILL,
   MATCH_MP_TAC (GSYM fubini) THEN
   ASM_SIMP_TAC std_ss [sigma_finite_measure_lborel] THEN
   CONJ_TAC THENL
   [GEN_TAC THEN `?a b. x = (a,b)` by METIS_TAC [pair_CASES] THEN
    ASM_SIMP_TAC std_ss [le_max1], ALL_TAC] THEN
   Q_TAC SUFF_TAC `(\(x,y). max 0 (g y * (f (x - y) * indicator_fn A x))) =
          (\z. max 0 (g (SND z) * (f (FST z - SND z) * indicator_fn A (FST z))))` THENL
   [DISC_RW_KILL,
    SIMP_TAC std_ss [FUN_EQ_THM] THEN GEN_TAC THEN
    `?a b. z = (a,b)` by METIS_TAC [pair_CASES] THEN ASM_SIMP_TAC std_ss []] THEN
   Q_TAC SUFF_TAC `(\z. max ((\z. 0) z)
                   ((\z. (g (SND z) * (f (FST z - SND z) * indicator_fn A (FST z)))) z)) IN
    measurable (m_space (pair_measure lborel lborel),
                measurable_sets (pair_measure lborel lborel)) Borel` THENL
   [SIMP_TAC std_ss [], ALL_TAC] THEN
   MATCH_MP_TAC IN_MEASURABLE_BOREL_MAX THEN
   `measure_space (pair_measure lborel lborel)` by
    METIS_TAC [measure_space_pair_measure', sigma_finite_measure_lborel] THEN
   CONJ_TAC THENL [METIS_TAC [measure_space_def], ALL_TAC] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST THEN
    METIS_TAC [measure_space_def], ALL_TAC] THEN
   MATCH_MP_TAC IN_MEASURABLE_BOREL_TIMES THEN Q.EXISTS_TAC `(\z. g (SND z))` THEN
   Q.EXISTS_TAC `(\z. f (FST z - SND z) * indicator_fn A (FST z))` THEN
   ASM_SIMP_TAC std_ss [] THEN CONJ_TAC THENL
   [SIMP_TAC std_ss [GSYM o_DEF] THEN MATCH_MP_TAC MEASURABLE_COMP THEN
    Q.EXISTS_TAC `(m_space lborel,measurable_sets lborel)` THEN ASM_SIMP_TAC std_ss [] THEN
    SIMP_TAC std_ss [IN_MEASURABLE, sigma_algebra_borel] THEN
    CONJ_TAC THENL [METIS_TAC [measure_space_def], ALL_TAC] THEN
    CONJ_TAC THENL [METIS_TAC [measure_space_def], ALL_TAC] THEN
    SIMP_TAC std_ss [IN_FUNSET, space_def, subsets_def] THEN CONJ_TAC THENL
    [SIMP_TAC std_ss [IN_UNIV, space_def, lborel, m_space_def], ALL_TAC] THEN
    SIMP_TAC std_ss [pair_measure, measure_of, m_space_def, measurable_sets_def] THEN
    Q.ABBREV_TAC `M = lborel` THEN
    Q_TAC SUFF_TAC `!s:real->bool. PREIMAGE SND s = univ(:real) CROSS s` THENL
    [DISCH_TAC,
     RW_TAC std_ss [PREIMAGE_def, EXTENSION, CROSS_DEF] THEN
     SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD, IN_UNIV]] THEN
    Q_TAC SUFF_TAC `{a CROSS b | a IN measurable_sets M /\ b IN measurable_sets M}
                  SUBSET POW (m_space M CROSS m_space M)` THENL
    [DISCH_TAC,
     SIMP_TAC std_ss [CROSS_DEF, SUBSET_DEF, POW_DEF, GSPECIFICATION, EXISTS_PROD] THEN
     RW_TAC std_ss [] THEN FULL_SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD] THEN
     `p_1 SUBSET m_space M` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
     `p_2 SUBSET m_space M` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
     ASM_SET_TAC []] THEN
    ASM_SIMP_TAC std_ss [CROSS_INTER_CROSS] THEN RW_TAC std_ss [INTER_UNIV] THEN
    `s IN measurable_sets M` by METIS_TAC [density, measurable_sets_def, lborel] THEN
    `s SUBSET m_space M` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
    `s INTER m_space M = s` by ASM_SET_TAC [] THEN
    ASM_SIMP_TAC std_ss [] THEN MATCH_MP_TAC sigma_sets_basic THEN
    SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD] THEN
    Q.EXISTS_TAC `m_space M` THEN Q.EXISTS_TAC `s` THEN
    ASM_SIMP_TAC std_ss [MEASURE_SPACE_MSPACE_MEASURABLE],
    ALL_TAC] THEN
   MATCH_MP_TAC IN_MEASURABLE_BOREL_TIMES THEN Q.EXISTS_TAC `(\z. f (FST z - SND z))` THEN
   Q.EXISTS_TAC `(\z. indicator_fn A (FST z))` THEN
   ASM_SIMP_TAC std_ss [] THEN CONJ_TAC THENL
   [ALL_TAC,
    MATCH_MP_TAC IN_MEASURABLE_BOREL_INDICATOR THEN
    Q.EXISTS_TAC `PREIMAGE (\z. FST z) A` THEN
    CONJ_TAC THENL [METIS_TAC [measure_space_def], ALL_TAC] THEN
    CONJ_TAC THENL [ALL_TAC, SIMP_TAC std_ss [indicator_fn_def, IN_PREIMAGE]] THEN
    SIMP_TAC std_ss [subsets_def] THEN
    Q_TAC SUFF_TAC `(\z. FST z) = (\(x,y:real). x:real)` THENL
    [DISC_RW_KILL,
     SIMP_TAC std_ss [FUN_EQ_THM] THEN GEN_TAC THEN
     `?a b. z = (a,b)` by METIS_TAC [pair_CASES] THEN ASM_SIMP_TAC std_ss []] THEN
    Q.ABBREV_TAC `M = lborel` THEN
    Q_TAC SUFF_TAC `(\(x,y). x) IN measurable
     (m_space (pair_measure M M), measurable_sets (pair_measure M M))
     (m_space M, measurable_sets M)` THENL
    [RW_TAC std_ss [IN_MEASURABLE, space_def, subsets_def] THEN
     POP_ASSUM MP_TAC THEN
     ASM_SIMP_TAC std_ss [pair_measure, measure_of, m_space_def, measurable_sets_def] THEN
     Q_TAC SUFF_TAC `{a CROSS b | a IN measurable_sets M /\ b IN measurable_sets M}
                   SUBSET POW (m_space M CROSS m_space M)` THENL
     [DISCH_TAC,
      SIMP_TAC std_ss [CROSS_DEF, SUBSET_DEF, POW_DEF, GSPECIFICATION, EXISTS_PROD] THEN
      RW_TAC std_ss [] THEN FULL_SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD] THEN
      `p_1 SUBSET m_space M` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
      `p_2 SUBSET m_space M` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
      ASM_SET_TAC []] THEN
     ASM_SIMP_TAC std_ss [] THEN DISCH_THEN (MP_TAC o Q.SPEC `A`) THEN
     ASM_SIMP_TAC std_ss [] THEN
     Q_TAC SUFF_TAC `PREIMAGE (\(x,y). x) A = A CROSS univ(:real)` THENL
     [DISC_RW_KILL,
      SIMP_TAC std_ss [EXTENSION, CROSS_DEF, IN_PREIMAGE] THEN
      SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD, IN_UNIV] THEN
      GEN_TAC THEN `?a b. x = (a,b)` by METIS_TAC [pair_CASES] THEN
      ASM_SIMP_TAC std_ss []] THEN
     SIMP_TAC std_ss [CROSS_INTER_CROSS, INTER_UNIV] THEN
     `A SUBSET m_space M` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
     `A INTER m_space M = A` by ASM_SET_TAC [] THEN
     METIS_TAC [lborel, m_space_def], ALL_TAC] THEN
    Q_TAC SUFF_TAC `(\(x,y:real). x:real) = FST` THENL
    [DISC_RW_KILL,
     SIMP_TAC std_ss [FUN_EQ_THM] THEN GEN_TAC THEN
     `?a b. x = (a,b)` by METIS_TAC [pair_CASES] THEN ASM_SIMP_TAC std_ss []] THEN
     SIMP_TAC std_ss [IN_MEASURABLE, sigma_algebra_borel] THEN
     CONJ_TAC THENL [METIS_TAC [measure_space_def], ALL_TAC] THEN
     CONJ_TAC THENL [METIS_TAC [measure_space_def], ALL_TAC] THEN
     SIMP_TAC std_ss [IN_FUNSET, space_def, subsets_def] THEN CONJ_TAC THENL
     [METIS_TAC [lborel, m_space_def, IN_UNIV], ALL_TAC] THEN
     SIMP_TAC std_ss [pair_measure, measure_of, m_space_def, measurable_sets_def] THEN

     Q_TAC SUFF_TAC `!s:real->bool. PREIMAGE FST s = s CROSS univ(:real)` THENL
     [DISCH_TAC,
      RW_TAC std_ss [PREIMAGE_def, EXTENSION, CROSS_DEF] THEN
      SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD, IN_UNIV]] THEN
     Q_TAC SUFF_TAC `{a CROSS b | a IN measurable_sets M /\ b IN measurable_sets M}
                   SUBSET POW (m_space M CROSS m_space M)` THENL
     [DISCH_TAC,
      SIMP_TAC std_ss [CROSS_DEF, SUBSET_DEF, POW_DEF, GSPECIFICATION, EXISTS_PROD] THEN
      RW_TAC std_ss [] THEN FULL_SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD] THEN
      `p_1 SUBSET m_space M` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
      `p_2 SUBSET m_space M` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
      ASM_SET_TAC []] THEN
     ASM_SIMP_TAC std_ss [CROSS_INTER_CROSS] THEN RW_TAC std_ss [INTER_UNIV] THEN
     `s IN measurable_sets M` by METIS_TAC [density, measurable_sets_def, lborel] THEN
     `s SUBSET m_space M` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
     `s INTER m_space M = s` by ASM_SET_TAC [] THEN
     ASM_SIMP_TAC std_ss [] THEN MATCH_MP_TAC sigma_sets_basic THEN
     SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD] THEN
     Q.EXISTS_TAC `s` THEN Q.EXISTS_TAC `m_space M` THEN
     ASM_SIMP_TAC std_ss [MEASURE_SPACE_MSPACE_MEASURABLE]] THEN

   SIMP_TAC std_ss [GSYM o_DEF] THEN MATCH_MP_TAC MEASURABLE_COMP THEN
   Q.EXISTS_TAC `(m_space lborel,measurable_sets lborel)` THEN ASM_SIMP_TAC std_ss [] THEN
   SIMP_TAC std_ss [IN_MEASURABLE, sigma_algebra_borel] THEN
   CONJ_TAC THENL [METIS_TAC [measure_space_def], ALL_TAC] THEN
   CONJ_TAC THENL [METIS_TAC [measure_space_def], ALL_TAC] THEN
   SIMP_TAC std_ss [IN_FUNSET, space_def, subsets_def] THEN CONJ_TAC THENL
   [SIMP_TAC std_ss [IN_UNIV, space_def, lborel, m_space_def], ALL_TAC] THEN
   SIMP_TAC std_ss [pair_measure, measure_of, m_space_def, measurable_sets_def] THEN
   Q.ABBREV_TAC `M = lborel` THEN
   Q_TAC SUFF_TAC `{a CROSS b | a IN measurable_sets M /\ b IN measurable_sets M}
                 SUBSET POW (m_space M CROSS m_space M)` THENL
   [DISCH_TAC,
    SIMP_TAC std_ss [CROSS_DEF, SUBSET_DEF, POW_DEF, GSPECIFICATION, EXISTS_PROD] THEN
    RW_TAC std_ss [] THEN FULL_SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD] THEN
    `p_1 SUBSET m_space M` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
    `p_2 SUBSET m_space M` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
    ASM_SET_TAC []] THEN ASM_SIMP_TAC std_ss [] THEN
   RW_TAC std_ss [] THEN
   Q_TAC SUFF_TAC `(\z. FST z - SND z) = (\(x,y). x - y:real)` THENL
   [DISC_RW_KILL,
    SIMP_TAC std_ss [FUN_EQ_THM] THEN GEN_TAC THEN
    `?a b. z = (a,b)` by METIS_TAC [pair_CASES] THEN ASM_SIMP_TAC std_ss []] THEN
   Q_TAC SUFF_TAC `(\(x,y). x - y) IN measurable
    (m_space (pair_measure M M), measurable_sets (pair_measure M M))
    (m_space M, measurable_sets M)` THENL
   [RW_TAC std_ss [IN_MEASURABLE, space_def, subsets_def] THEN
    POP_ASSUM MP_TAC THEN
    ASM_SIMP_TAC std_ss [pair_measure, measure_of, m_space_def, measurable_sets_def],
    ALL_TAC] THEN
   Q.UNABBREV_TAC `M` THEN SIMP_TAC std_ss [lborel, m_space_def, measurable_sets_def] THEN
   SIMP_TAC std_ss [GSYM lborel, GSYM space_borel, SPACE, GSYM borel_measurable] THEN
   Q_TAC SUFF_TAC `(\(x,y). x - y:real) = (\z. FST z - SND z)` THENL
   [DISC_RW_KILL,
    SIMP_TAC std_ss [FUN_EQ_THM] THEN GEN_TAC THEN
    `?a b. z = (a,b)` by METIS_TAC [pair_CASES] THEN ASM_SIMP_TAC std_ss []] THEN

    MATCH_MP_TAC borel_measurable_sub THEN Q.EXISTS_TAC `FST` THEN Q.EXISTS_TAC `SND` THEN
    ASM_SIMP_TAC std_ss [] THEN
    CONJ_TAC THENL [METIS_TAC [measure_space_def], ALL_TAC] THEN
    SIMP_TAC std_ss [borel_measurable] THEN CONJ_TAC THENL
    [SIMP_TAC std_ss [IN_MEASURABLE, sigma_algebra_borel] THEN
     CONJ_TAC THENL [METIS_TAC [measure_space_def], ALL_TAC] THEN
     SIMP_TAC std_ss [IN_FUNSET, space_def, subsets_def] THEN CONJ_TAC THENL
     [SIMP_TAC std_ss [space_borel, IN_UNIV], ALL_TAC] THEN
     SIMP_TAC std_ss [pair_measure, measure_of, m_space_def, measurable_sets_def] THEN
     Q.ABBREV_TAC `M = lborel` THEN
     Q_TAC SUFF_TAC `!s:real->bool. PREIMAGE FST s = s CROSS univ(:real)` THENL
     [DISCH_TAC,
      RW_TAC std_ss [PREIMAGE_def, EXTENSION, CROSS_DEF] THEN
      SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD, IN_UNIV]] THEN
     Q_TAC SUFF_TAC `{a CROSS b | a IN measurable_sets M /\ b IN measurable_sets M}
                   SUBSET POW (m_space M CROSS m_space M)` THENL
     [DISCH_TAC,
      SIMP_TAC std_ss [CROSS_DEF, SUBSET_DEF, POW_DEF, GSPECIFICATION, EXISTS_PROD] THEN
      RW_TAC std_ss [] THEN FULL_SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD] THEN
      `p_1 SUBSET m_space M` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
      `p_2 SUBSET m_space M` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
      ASM_SET_TAC []] THEN
     ASM_SIMP_TAC std_ss [CROSS_INTER_CROSS] THEN RW_TAC std_ss [INTER_UNIV] THEN
     `s' IN measurable_sets M` by METIS_TAC [measurable_sets_def, lborel] THEN
     `s' SUBSET m_space M` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
     `s' INTER m_space M = s'` by ASM_SET_TAC [] THEN
     ASM_SIMP_TAC std_ss [] THEN MATCH_MP_TAC sigma_sets_basic THEN
     SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD] THEN
     Q.EXISTS_TAC `s'` THEN Q.EXISTS_TAC `m_space M` THEN
     ASM_SIMP_TAC std_ss [MEASURE_SPACE_MSPACE_MEASURABLE],
     ALL_TAC] THEN
   SIMP_TAC std_ss [IN_MEASURABLE, sigma_algebra_borel] THEN
   CONJ_TAC THENL [METIS_TAC [measure_space_def], ALL_TAC] THEN
   SIMP_TAC std_ss [IN_FUNSET, space_def, subsets_def] THEN CONJ_TAC THENL
   [SIMP_TAC std_ss [space_borel, IN_UNIV], ALL_TAC] THEN
   SIMP_TAC std_ss [pair_measure, measure_of, m_space_def, measurable_sets_def] THEN
   Q.ABBREV_TAC `M = lborel` THEN
   Q_TAC SUFF_TAC `!s:real->bool. PREIMAGE SND s = univ(:real) CROSS s` THENL
   [DISCH_TAC,
    RW_TAC std_ss [PREIMAGE_def, EXTENSION, CROSS_DEF] THEN
    SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD, IN_UNIV]] THEN
   Q_TAC SUFF_TAC `{a CROSS b | a IN measurable_sets M /\ b IN measurable_sets M}
                 SUBSET POW (m_space M CROSS m_space M)` THENL
   [DISCH_TAC,
    SIMP_TAC std_ss [CROSS_DEF, SUBSET_DEF, POW_DEF, GSPECIFICATION, EXISTS_PROD] THEN
    RW_TAC std_ss [] THEN FULL_SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD] THEN
    `p_1 SUBSET m_space M` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
    `p_2 SUBSET m_space M` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
    ASM_SET_TAC []] THEN
   ASM_SIMP_TAC std_ss [CROSS_INTER_CROSS] THEN RW_TAC std_ss [INTER_UNIV] THEN
   `s' IN measurable_sets M` by METIS_TAC [density, measurable_sets_def, lborel] THEN
   `s' SUBSET m_space M` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
   `s' INTER m_space M = s'` by ASM_SET_TAC [] THEN
   ASM_SIMP_TAC std_ss [] THEN MATCH_MP_TAC sigma_sets_basic THEN
   SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD] THEN
   Q.EXISTS_TAC `m_space M` THEN Q.EXISTS_TAC `s'` THEN
   ASM_SIMP_TAC std_ss [MEASURE_SPACE_MSPACE_MEASURABLE]] THEN

  ASM_SIMP_TAC std_ss [extreal_max_def, pos_fn_integral_pos, le_mul, indicator_fn_pos_le] THEN
  MATCH_MP_TAC positive_integral_cong THEN
  ASM_SIMP_TAC std_ss [extreal_max_def, pos_fn_integral_pos, le_mul, indicator_fn_pos_le] THEN
  RW_TAC std_ss [indicator_fn_def, mul_rzero, mul_rone] THEN
  ASM_SIMP_TAC std_ss [pos_fn_integral_zero] THEN
  GEN_REWR_TAC (LAND_CONV o ONCE_DEPTH_CONV) [mul_comm] THEN
  SIMP_TAC std_ss []);

val measure_measure_of = store_thm ("measure_measure_of",
 ``!M1 M2 s. measure_space M1 /\ measure_space M2 /\
            (measure_of M1 = measure_of M2) /\ s IN measurable_sets M1 ==>
            (measure M1 s = measure M2 s)``,
  REPEAT GEN_TAC THEN
  `(M1 = (m_space M1, measurable_sets M1, measure M1)) /\
   (M2 = (m_space M2, measurable_sets M2, measure M2))` by
   METIS_TAC [MEASURE_SPACE_REDUCE] THEN
  POP_ASSUM (fn th => ONCE_REWRITE_TAC [th]) THEN
  POP_ASSUM (fn th => ONCE_REWRITE_TAC [th]) THEN
  SIMP_TAC std_ss [measure_of, measure_def] THEN
  REPEAT STRIP_TAC THEN FULL_SIMP_TAC std_ss [measurable_sets_def, FUN_EQ_THM] THEN
  FIRST_X_ASSUM (MP_TAC o Q.SPEC `s`) THEN
  FULL_SIMP_TAC std_ss [MEASURE_SPACE_REDUCE] THEN
  `sigma_sets (m_space M1) (measurable_sets M1) = measurable_sets M1` by
   METIS_TAC [sigma_sets_eq, measure_space_def] THEN
  `sigma_sets (m_space M2) (measurable_sets M2) = measurable_sets M2` by
   METIS_TAC [sigma_sets_eq, measure_space_def] THEN
  FULL_SIMP_TAC std_ss [MEASURE_SPACE_REDUCE] THEN
  `measurable_sets M1 SUBSET POW (m_space M1)` by
   METIS_TAC [measure_space_def, sigma_algebra_iff2] THEN
  `measurable_sets M2 SUBSET POW (m_space M2)` by
   METIS_TAC [measure_space_def, sigma_algebra_iff2] THEN
  METIS_TAC []);

val measure_convolution_density = store_thm ("measure_convolution_density",
  ``!f g A. f IN measurable (m_space lborel, measurable_sets lborel) Borel /\
            g IN measurable (m_space lborel, measurable_sets lborel) Borel /\
          finite_measure (density lborel f) /\ finite_measure (density lborel g) /\
          (!x. 0 <= f x) /\ (!x. 0 <= g x) /\ A IN measurable_sets lborel ==>
          (measure (convolution (density lborel f) (density lborel g)) A =
           measure (density lborel (\x. pos_fn_integral lborel (\y. f (x - y) * g y))) A)``,
  RW_TAC std_ss [] THEN MATCH_MP_TAC measure_measure_of THEN
  `(measure_of (convolution (density lborel f) (density lborel g)) =
    measure_of (density lborel (\x. pos_fn_integral lborel (\y. f (x - y) * g y))))` by
   METIS_TAC [convolution_density] THEN ASM_SIMP_TAC std_ss [] THEN
  ASSUME_TAC measure_space_lborel THEN
  `measure_space (density lborel f)` by METIS_TAC [measure_space_density] THEN
  `measure_space (density lborel g)` by METIS_TAC [measure_space_density] THEN
  Q_TAC SUFF_TAC `sigma_finite_measure (density lborel g)` THENL
  [DISCH_TAC,
   FULL_SIMP_TAC std_ss [sigma_finite_measure, finite_measure] THEN
   Q.EXISTS_TAC `{m_space (density lborel g)}` THEN
   SIMP_TAC std_ss [countable_sing, BIGUNION_SING] THEN
   ASM_SIMP_TAC std_ss [MEASURE_SPACE_MSPACE_MEASURABLE, SUBSET_DEF, IN_SING]] THEN
  CONJ_TAC THENL
  [SIMP_TAC std_ss [convolution] THEN MATCH_MP_TAC measure_space_distr THEN
   ASM_SIMP_TAC std_ss [measure_space_pair_measure', measure_space_borel] THEN
   SIMP_TAC std_ss [m_space_def, measurable_sets_def, SPACE, GSYM borel_measurable] THEN
   Q_TAC SUFF_TAC `(\(x,y). x + y:real) = (\z. FST z + SND z)` THENL
   [DISC_RW_KILL,
    SIMP_TAC std_ss [FUN_EQ_THM] THEN GEN_TAC THEN
    `?a b. z = (a,b)` by METIS_TAC [pair_CASES] THEN ASM_SIMP_TAC std_ss []] THEN
   MATCH_MP_TAC borel_measurable_add THEN Q.EXISTS_TAC `FST` THEN Q.EXISTS_TAC `SND` THEN
   ASM_SIMP_TAC std_ss [] THEN
   `measure_space (pair_measure (density lborel f) (density lborel g))` by
    ASM_SIMP_TAC std_ss [measure_space_pair_measure'] THEN
   CONJ_TAC THENL [METIS_TAC [measure_space_def], ALL_TAC] THEN
   SIMP_TAC std_ss [borel_measurable] THEN CONJ_TAC THENL
   [SIMP_TAC std_ss [IN_MEASURABLE, sigma_algebra_borel] THEN
    CONJ_TAC THENL [METIS_TAC [measure_space_def], ALL_TAC] THEN
    SIMP_TAC std_ss [IN_FUNSET, space_def, subsets_def] THEN CONJ_TAC THENL
    [SIMP_TAC std_ss [space_borel, IN_UNIV], ALL_TAC] THEN
    SIMP_TAC std_ss [pair_measure, measure_of, m_space_def, measurable_sets_def] THEN
    Q.ABBREV_TAC `M1 = density lborel f` THEN
    Q.ABBREV_TAC `M2 = density lborel g` THEN
    Q_TAC SUFF_TAC `!s:real->bool. PREIMAGE FST s = s CROSS univ(:real)` THENL
    [DISCH_TAC,
     RW_TAC std_ss [PREIMAGE_def, EXTENSION, CROSS_DEF] THEN
     SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD, IN_UNIV]] THEN
    Q_TAC SUFF_TAC `{a CROSS b | a IN measurable_sets M1 /\ b IN measurable_sets M2}
                  SUBSET POW (m_space M1 CROSS m_space M2)` THENL
    [DISCH_TAC,
     SIMP_TAC std_ss [CROSS_DEF, SUBSET_DEF, POW_DEF, GSPECIFICATION, EXISTS_PROD] THEN
     RW_TAC std_ss [] THEN FULL_SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD] THEN
     `p_1 SUBSET m_space M1` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
     `p_2 SUBSET m_space M2` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
     ASM_SET_TAC []] THEN
    ASM_SIMP_TAC std_ss [CROSS_INTER_CROSS] THEN RW_TAC std_ss [INTER_UNIV] THEN
    `s IN measurable_sets M1` by METIS_TAC [density, measurable_sets_def, lborel] THEN
    `s SUBSET m_space M1` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
    `s INTER m_space M1 = s` by ASM_SET_TAC [] THEN
    ASM_SIMP_TAC std_ss [] THEN MATCH_MP_TAC sigma_sets_basic THEN
    SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD] THEN
    Q.EXISTS_TAC `s` THEN Q.EXISTS_TAC `m_space M2` THEN
    ASM_SIMP_TAC std_ss [MEASURE_SPACE_MSPACE_MEASURABLE],
    ALL_TAC] THEN
   SIMP_TAC std_ss [IN_MEASURABLE, sigma_algebra_borel] THEN
   CONJ_TAC THENL [METIS_TAC [measure_space_def], ALL_TAC] THEN
   SIMP_TAC std_ss [IN_FUNSET, space_def, subsets_def] THEN CONJ_TAC THENL
   [SIMP_TAC std_ss [space_borel, IN_UNIV], ALL_TAC] THEN
   SIMP_TAC std_ss [pair_measure, measure_of, m_space_def, measurable_sets_def] THEN
   Q.ABBREV_TAC `M1 = density lborel f` THEN
   Q.ABBREV_TAC `M2 = density lborel g` THEN
   Q_TAC SUFF_TAC `!s:real->bool. PREIMAGE SND s = univ(:real) CROSS s` THENL
   [DISCH_TAC,
    RW_TAC std_ss [PREIMAGE_def, EXTENSION, CROSS_DEF] THEN
    SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD, IN_UNIV]] THEN
   Q_TAC SUFF_TAC `{a CROSS b | a IN measurable_sets M1 /\ b IN measurable_sets M2}
                 SUBSET POW (m_space M1 CROSS m_space M2)` THENL
   [DISCH_TAC,
    SIMP_TAC std_ss [CROSS_DEF, SUBSET_DEF, POW_DEF, GSPECIFICATION, EXISTS_PROD] THEN
    RW_TAC std_ss [] THEN FULL_SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD] THEN
    `p_1 SUBSET m_space M1` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
    `p_2 SUBSET m_space M2` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
    ASM_SET_TAC []] THEN
   ASM_SIMP_TAC std_ss [CROSS_INTER_CROSS] THEN RW_TAC std_ss [INTER_UNIV] THEN
   `s IN measurable_sets M2` by METIS_TAC [density, measurable_sets_def, lborel] THEN
   `s SUBSET m_space M2` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
   `s INTER m_space M2 = s` by ASM_SET_TAC [] THEN
   ASM_SIMP_TAC std_ss [] THEN MATCH_MP_TAC sigma_sets_basic THEN
   SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD] THEN
   Q.EXISTS_TAC `m_space M1` THEN Q.EXISTS_TAC `s` THEN
   ASM_SIMP_TAC std_ss [MEASURE_SPACE_MSPACE_MEASURABLE],
   ALL_TAC] THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC measure_space_density THEN SIMP_TAC std_ss [measure_space_lborel] THEN
   Q_TAC SUFF_TAC `(\x. pos_fn_integral lborel (\y. f (x - y) * g y)) =
      (\x. pos_fn_integral lborel (\y. max 0 (if x IN m_space lborel
           then (\(x,y). (\y. f (x - y) * g y) y) (x,y) else 0)))` THENL
   [DISC_RW_KILL,
    ABS_TAC THEN MATCH_MP_TAC positive_integral_cong THEN
    ASM_SIMP_TAC std_ss [le_mul, le_max1] THEN
    SIMP_TAC std_ss [m_space_def, lborel, space_borel, IN_UNIV] THEN
    ASM_SIMP_TAC std_ss [extreal_max_def, le_mul]] THEN
   MATCH_MP_TAC borel_measurable_pos_integral_fst THEN
   ASM_SIMP_TAC std_ss [measure_space_lborel, sigma_finite_measure_lborel] THEN
   CONJ_TAC THENL
   [GEN_TAC THEN `?a b. x = (a,b)` by METIS_TAC [pair_CASES] THEN
    ASM_SIMP_TAC std_ss [le_mul], ALL_TAC] THEN
   Q_TAC SUFF_TAC `(\(x,y). f (x - y) * g y) = (\z. f (FST z - SND z) * g (SND z))` THENL
   [DISC_RW_KILL,
    SIMP_TAC std_ss [FUN_EQ_THM] THEN GEN_TAC THEN
    `?a b. z = (a,b)` by METIS_TAC [pair_CASES] THEN
    ASM_SIMP_TAC std_ss []] THEN
   MATCH_MP_TAC IN_MEASURABLE_BOREL_TIMES THEN
   Q.EXISTS_TAC `(\z. f (FST z - SND z))` THEN Q.EXISTS_TAC `(\z. g (SND z))` THEN
   ASSUME_TAC sigma_finite_measure_lborel THEN
   ASM_SIMP_TAC std_ss [measure_space_pair_measure', GSYM o_DEF] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC MEASURABLE_COMP THEN
    Q.EXISTS_TAC `(m_space lborel,measurable_sets lborel)` THEN
    ASM_SIMP_TAC std_ss [lborel, m_space_def, measurable_sets_def] THEN
    SIMP_TAC std_ss [GSYM lborel, SPACE, GSYM borel_measurable, GSYM space_borel] THEN
    MATCH_MP_TAC borel_measurable_sub THEN Q.EXISTS_TAC `FST` THEN
    Q.EXISTS_TAC `SND` THEN SIMP_TAC std_ss [] THEN
    `measure_space (pair_measure lborel lborel)` by
     ASM_SIMP_TAC std_ss [measure_space_pair_measure'] THEN
    CONJ_TAC THENL [METIS_TAC [measure_space_def], ALL_TAC] THEN
    SIMP_TAC std_ss [borel_measurable] THEN CONJ_TAC THENL
    [SIMP_TAC std_ss [IN_MEASURABLE, sigma_algebra_borel] THEN
     CONJ_TAC THENL [METIS_TAC [measure_space_def], ALL_TAC] THEN
     SIMP_TAC std_ss [IN_FUNSET, space_def, subsets_def] THEN CONJ_TAC THENL
     [SIMP_TAC std_ss [space_borel, IN_UNIV], ALL_TAC] THEN
     SIMP_TAC std_ss [pair_measure, measure_of, m_space_def, measurable_sets_def] THEN
     Q_TAC SUFF_TAC `!s:real->bool. PREIMAGE FST s = s CROSS univ(:real)` THENL
     [DISCH_TAC,
      RW_TAC std_ss [PREIMAGE_def, EXTENSION, CROSS_DEF] THEN
      SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD, IN_UNIV]] THEN
     Q_TAC SUFF_TAC `{a CROSS b | a IN measurable_sets lborel /\ b IN measurable_sets lborel}
                     SUBSET POW (m_space lborel CROSS m_space lborel)` THENL
     [DISCH_TAC,
      SIMP_TAC std_ss [CROSS_DEF, SUBSET_DEF, POW_DEF, GSPECIFICATION, EXISTS_PROD] THEN
      RW_TAC std_ss [] THEN FULL_SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD] THEN
      `p_1 SUBSET m_space lborel` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
      `p_2 SUBSET m_space lborel` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
      ASM_SET_TAC []] THEN
     ASM_SIMP_TAC std_ss [CROSS_INTER_CROSS] THEN RW_TAC std_ss [INTER_UNIV] THEN
     `s IN measurable_sets lborel` by METIS_TAC [density, measurable_sets_def, lborel] THEN
     `s SUBSET m_space lborel` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
     `s INTER m_space lborel = s` by ASM_SET_TAC [] THEN
     ASM_SIMP_TAC std_ss [] THEN MATCH_MP_TAC sigma_sets_basic THEN
     SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD] THEN
     Q.EXISTS_TAC `s` THEN Q.EXISTS_TAC `m_space lborel` THEN
     ASM_SIMP_TAC std_ss [MEASURE_SPACE_MSPACE_MEASURABLE],
     ALL_TAC] THEN
    SIMP_TAC std_ss [IN_MEASURABLE, sigma_algebra_borel] THEN
    CONJ_TAC THENL [METIS_TAC [measure_space_def], ALL_TAC] THEN
    SIMP_TAC std_ss [IN_FUNSET, space_def, subsets_def] THEN CONJ_TAC THENL
    [SIMP_TAC std_ss [space_borel, IN_UNIV], ALL_TAC] THEN
    SIMP_TAC std_ss [pair_measure, measure_of, m_space_def, measurable_sets_def] THEN
    Q_TAC SUFF_TAC `!s:real->bool. PREIMAGE SND s = univ(:real) CROSS s` THENL
    [DISCH_TAC,
     RW_TAC std_ss [PREIMAGE_def, EXTENSION, CROSS_DEF] THEN
     SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD, IN_UNIV]] THEN
    Q_TAC SUFF_TAC `{a CROSS b | a IN measurable_sets lborel /\ b IN measurable_sets lborel}
                    SUBSET POW (m_space lborel CROSS m_space lborel)` THENL
    [DISCH_TAC,
     SIMP_TAC std_ss [CROSS_DEF, SUBSET_DEF, POW_DEF, GSPECIFICATION, EXISTS_PROD] THEN
     RW_TAC std_ss [] THEN FULL_SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD] THEN
     `p_1 SUBSET m_space lborel` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
     `p_2 SUBSET m_space lborel` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
     ASM_SET_TAC []] THEN
    ASM_SIMP_TAC std_ss [CROSS_INTER_CROSS] THEN RW_TAC std_ss [INTER_UNIV] THEN
    `s IN measurable_sets lborel` by METIS_TAC [density, measurable_sets_def, lborel] THEN
    `s SUBSET m_space lborel` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
    `s INTER m_space lborel = s` by ASM_SET_TAC [] THEN
    ASM_SIMP_TAC std_ss [] THEN MATCH_MP_TAC sigma_sets_basic THEN
    SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD] THEN
    Q.EXISTS_TAC `m_space lborel` THEN Q.EXISTS_TAC `s` THEN
    ASM_SIMP_TAC std_ss [MEASURE_SPACE_MSPACE_MEASURABLE],
    ALL_TAC] THEN
   MATCH_MP_TAC MEASURABLE_COMP THEN
   Q.EXISTS_TAC `(m_space lborel,measurable_sets lborel)` THEN
   ASM_SIMP_TAC std_ss [] THEN
   SIMP_TAC std_ss [lborel, m_space_def, measurable_sets_def] THEN
   SIMP_TAC std_ss [GSYM lborel, GSYM space_borel, SPACE] THEN
   SIMP_TAC std_ss [IN_MEASURABLE, sigma_algebra_borel] THEN
   `measure_space (pair_measure lborel lborel)` by
     ASM_SIMP_TAC std_ss [measure_space_pair_measure'] THEN
   CONJ_TAC THENL [METIS_TAC [measure_space_def], ALL_TAC] THEN
   SIMP_TAC std_ss [IN_FUNSET, space_def, subsets_def] THEN CONJ_TAC THENL
   [SIMP_TAC std_ss [space_borel, IN_UNIV], ALL_TAC] THEN
   SIMP_TAC std_ss [pair_measure, measure_of, m_space_def, measurable_sets_def] THEN
   Q_TAC SUFF_TAC `!s:real->bool. PREIMAGE SND s = univ(:real) CROSS s` THENL
   [DISCH_TAC,
    RW_TAC std_ss [PREIMAGE_def, EXTENSION, CROSS_DEF] THEN
    SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD, IN_UNIV]] THEN
   Q_TAC SUFF_TAC `{a CROSS b | a IN measurable_sets lborel /\ b IN measurable_sets lborel}
                   SUBSET POW (m_space lborel CROSS m_space lborel)` THENL
   [DISCH_TAC,
    SIMP_TAC std_ss [CROSS_DEF, SUBSET_DEF, POW_DEF, GSPECIFICATION, EXISTS_PROD] THEN
    RW_TAC std_ss [] THEN FULL_SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD] THEN
    `p_1 SUBSET m_space lborel` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
    `p_2 SUBSET m_space lborel` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
    ASM_SET_TAC []] THEN
   ASM_SIMP_TAC std_ss [CROSS_INTER_CROSS] THEN RW_TAC std_ss [INTER_UNIV] THEN
   `s IN measurable_sets lborel` by METIS_TAC [density, measurable_sets_def, lborel] THEN
   `s SUBSET m_space lborel` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
   `s INTER m_space lborel = s` by ASM_SET_TAC [] THEN
   ASM_SIMP_TAC std_ss [] THEN MATCH_MP_TAC sigma_sets_basic THEN
   SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD] THEN
   Q.EXISTS_TAC `m_space lborel` THEN Q.EXISTS_TAC `s` THEN
   ASM_SIMP_TAC std_ss [MEASURE_SPACE_MSPACE_MEASURABLE],
   ALL_TAC] THEN
  ASM_SIMP_TAC std_ss [convolution, distr, measurable_sets_def] THEN
  METIS_TAC [lborel, measurable_sets_def]);

val conv_normal_density_zero_mean = store_thm
  ("conv_normal_density_zero_mean",
  ``!sig1 sig2 p X Y x. 0 < sig1 /\ 0 < sig2 /\
      normal_rv X p 0 sig1 ==>
       (pos_fn_integral lborel
         (\y. Normal (normal_density 0 sig1 (x - y)) * Normal (normal_density 0 sig2 y)) =
        Normal (normal_density 0 (sqrt (sig1 pow 2 + sig2 pow 2)) x))``,
  RW_TAC std_ss [] THEN
  `0 < sig1 pow 2 /\ 0 < sig2 pow 2` by METIS_TAC [REAL_POW_LT] THEN
  Q_TAC SUFF_TAC `pos_fn_integral lborel
   (\y. Normal (normal_density 0 sig1 (x - y)) *
        Normal (normal_density 0 sig2 y)) =
   pos_fn_integral lborel (\y. Normal (normal_density 0 (sqrt (sig1 pow 2 + sig2 pow 2)) x) *
        Normal (normal_density (sig2 pow 2 * x / (sig1 pow 2 + sig2 pow 2))
                (sqrt (sig1 pow 2 * sig2 pow 2 / (sig1 pow 2 + sig2 pow 2))) y))` THENL
  [DISC_RW_KILL,
   Q.ABBREV_TAC `sig1' = sig1 pow 2` THEN Q.ABBREV_TAC `sig2' = sig2 pow 2` THEN
   Q.ABBREV_TAC `sig = sig1' * sig2' / (sig1' + sig2')` THEN
   `!mu sig x. 0 <= Normal (normal_density mu sig x)` by
    METIS_TAC [extreal_of_num_def, extreal_le_def, normal_density_nonneg] THEN
   MATCH_MP_TAC positive_integral_cong THEN ASM_SIMP_TAC std_ss [le_mul] THEN
   SIMP_TAC std_ss [measure_space_lborel] THEN Q.X_GEN_TAC `y` THEN
   RW_TAC real_ss [extreal_mul_def, extreal_11, normal_density] THEN
   `0 <= sig1' + sig2'` by ASM_SIMP_TAC real_ss [REAL_LE_ADD, REAL_LT_IMP_LE] THEN
   POP_ASSUM (ASSUME_TAC o MATCH_MP SQRT_POW_2) THEN ASM_SIMP_TAC std_ss [] THEN
   `0 < sig1' * sig2' / (sig1' + sig2')` by
     ASM_SIMP_TAC std_ss [REAL_LT_MUL, REAL_LT_DIV, REAL_LT_ADD] THEN
   `0 <= sig` by METIS_TAC [REAL_LT_IMP_LE] THEN
   POP_ASSUM (ASSUME_TAC o MATCH_MP SQRT_POW_2) THEN ASM_SIMP_TAC std_ss [] THEN
   ONCE_REWRITE_TAC [REAL_ARITH ``a * exp b * (c * exp d) = (a * c) * (exp b * exp d:real)``] THEN
   MATCH_MP_TAC (METIS [] ``(a1 = a2) /\ (b1 = b2) ==> (a1 * b1:real = a2 * b2:real)``) THEN
   CONJ_TAC THENL
   [SIMP_TAC real_ss [real_div] THEN ASSUME_TAC PI_POS THEN
    `0 < 2 * pi * sig1'` by ASM_SIMP_TAC real_ss [REAL_LT_MUL] THEN
    `0 < 2 * pi * sig2'` by ASM_SIMP_TAC real_ss [REAL_LT_MUL] THEN
    `0 < 2 * pi * (sig1' + sig2')` by ASM_SIMP_TAC real_ss [REAL_LT_MUL, REAL_LT_ADD] THEN
    `0 < sig` by METIS_TAC [] THEN
    `0 < 2 * pi * sig` by ASM_SIMP_TAC real_ss [REAL_LT_MUL] THEN
    `sqrt (2 * pi * sig1') <> 0` by (ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
     MATCH_MP_TAC REAL_LT_IMP_NE THEN ASM_SIMP_TAC std_ss [SQRT_POS_LT]) THEN
    `sqrt (2 * pi * sig2') <> 0` by (ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
     MATCH_MP_TAC REAL_LT_IMP_NE THEN ASM_SIMP_TAC std_ss [SQRT_POS_LT]) THEN
    `sqrt (2 * pi * (sig1' + sig2')) <> 0` by (ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
     MATCH_MP_TAC REAL_LT_IMP_NE THEN ASM_SIMP_TAC std_ss [SQRT_POS_LT]) THEN
    `sqrt (2 * pi * sig) <> 0` by (ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
     MATCH_MP_TAC REAL_LT_IMP_NE THEN ASM_SIMP_TAC std_ss [SQRT_POS_LT]) THEN
    ASM_SIMP_TAC std_ss [GSYM REAL_INV_MUL, REAL_INV_INJ] THEN
    ASM_SIMP_TAC real_ss [GSYM SQRT_MUL, REAL_LT_IMP_LE] THEN
    AP_TERM_TAC THEN ONCE_REWRITE_TAC [REAL_ARITH
     ``a * b * c * (a * b * d) = (a * b * a * b) * (c * d:real)``] THEN
    AP_TERM_TAC THEN Q.UNABBREV_TAC `sig` THEN ONCE_REWRITE_TAC [REAL_MUL_COMM] THEN
    `(sig1' + sig2') <> 0` by ASM_SIMP_TAC real_ss [REAL_LT_ADD, REAL_LT_IMP_NE] THEN
    ASM_SIMP_TAC real_ss [REAL_DIV_RMUL] THEN METIS_TAC [REAL_MUL_COMM],
    ALL_TAC] THEN
   ASM_SIMP_TAC std_ss [GSYM EXP_ADD] THEN AP_TERM_TAC THEN
   SIMP_TAC real_ss [real_div] THEN
   REWRITE_TAC [REAL_ARITH ``(-a + -b = -c + -d) = (a + b = c + d:real)``] THEN
   Q.UNABBREV_TAC `sig` THEN SIMP_TAC std_ss [real_div, POW_2] THEN
   ONCE_REWRITE_TAC [REAL_ARITH
    ``!a b. (a - b) * (a - b) = (a * a) - (2 * a * b:real) + (b * b)``] THEN
   SIMP_TAC std_ss [REAL_MUL_ASSOC] THEN Q.ABBREV_TAC `sig = sig1' + sig2'` THEN
   REWRITE_TAC [REAL_ARITH ``!a b. (a + b) * c = a * c + b * c:real``] THEN
   REWRITE_TAC [REAL_ARITH ``!a b. (a - b) * c = a * c - b * c:real``] THEN
   Q_TAC SUFF_TAC `2 * y * sig2' * x * inv sig * inv (2 * sig1' * sig2' * inv sig) =
      2 * x * y * inv (2 * sig1')` THENL
   [DISC_RW_KILL,
    `2 <> 0:real` by REAL_ARITH_TAC THEN
    `sig1' <> 0 /\ sig2' <> 0` by METIS_TAC [REAL_LT_IMP_NE, EQ_SYM_EQ] THEN
    `0 < sig1' + sig2'` by ASM_SIMP_TAC std_ss [REAL_LT_ADD] THEN
    `0 < inv sig` by METIS_TAC [REAL_INV_POS] THEN
    `inv sig <> 0` by METIS_TAC [REAL_LT_IMP_NE, EQ_SYM_EQ] THEN
    ASM_SIMP_TAC std_ss [REAL_MUL_NZ, REAL_INV_MUL, REAL_INV_INV] THEN
    SIMP_TAC std_ss [REAL_MUL_ASSOC] THEN `sig <> 0` by METIS_TAC [REAL_LT_IMP_NE] THEN
    ONCE_REWRITE_TAC [REAL_ARITH
     ``2 * y * sig2' * x * inv sig * inv 2 * inv sig1' * inv sig2' * sig:real =
       2 * x * y * inv 2 * inv sig1' * (inv sig2' * sig2') * (inv sig * sig)``] THEN
    ASM_SIMP_TAC real_ss [REAL_MUL_LINV]] THEN
   Q.ABBREV_TAC `DONE1 = 2 * x * y * inv (2 * sig1')` THEN
   `2 <> 0:real` by REAL_ARITH_TAC THEN
   `sig1' <> 0 /\ sig2' <> 0` by METIS_TAC [REAL_LT_IMP_NE, EQ_SYM_EQ] THEN
   `0 < sig1' + sig2'` by ASM_SIMP_TAC std_ss [REAL_LT_ADD] THEN
   `0 < inv sig` by METIS_TAC [REAL_INV_POS] THEN
   `inv sig <> 0` by METIS_TAC [REAL_LT_IMP_NE, EQ_SYM_EQ] THEN
   ASM_SIMP_TAC std_ss [REAL_MUL_NZ, REAL_INV_MUL, REAL_INV_INV, REAL_MUL_ASSOC] THEN
   Q_TAC SUFF_TAC `y * y * inv 2 * inv sig1' * inv sig2' * sig =
                   y * y * inv 2 * inv sig1' + y * y * inv 2 * inv sig2'` THENL
   [DISC_RW_KILL,
    Q.UNABBREV_TAC `sig` THEN
    ONCE_REWRITE_TAC [REAL_ARITH ``!a b c. a * (b + c) = a * b + a * c:real``] THEN
    REWRITE_TAC [REAL_ARITH ``y * y * inv 2 * inv sig1' * inv sig2' * sig1':real =
                             y * y * inv 2 * inv sig2' * (sig1' * inv sig1')``] THEN
    REWRITE_TAC [REAL_ARITH ``y * y * inv 2 * inv sig1' * inv sig2' * sig2':real =
                             y * y * inv 2 * inv sig1' * (sig2' * inv sig2')``] THEN
    ASM_SIMP_TAC real_ss [REAL_MUL_RINV] THEN METIS_TAC [REAL_ADD_COMM]] THEN
   Q.ABBREV_TAC `DONE2 = y * y * inv 2 * inv sig1'` THEN
   Q.ABBREV_TAC `DONE3 = y * y * inv 2 * inv sig2'` THEN
   SIMP_TAC std_ss [REAL_ADD_ASSOC] THEN
   ONCE_REWRITE_TAC [REAL_ARITH ``!a b c. a + (b) + c = a + c + b:real``] THEN
   ONCE_REWRITE_TAC [REAL_ARITH ``a + b - c = -c + b + a:real``] THEN
   SIMP_TAC std_ss [REAL_ADD_ASSOC, real_sub] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
   AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
   `sig <> 0` by METIS_TAC [REAL_LT_IMP_NE] THEN
   ASM_SIMP_TAC std_ss [REAL_INV_MUL, REAL_MUL_ASSOC] THEN
   ONCE_REWRITE_TAC [REAL_ARITH
   ``sig2' * x * inv sig * sig2' * x * inv sig * inv 2 * inv sig1' * inv sig2' * sig:real =
     x * x * inv 2 * (inv sig1' * (sig * inv sig) * (sig2' * inv sig2') * (sig2' * inv sig))``] THEN
   ASM_SIMP_TAC real_ss [REAL_MUL_RINV] THEN
   ONCE_REWRITE_TAC [REAL_ARITH ``x * x * inv 2 * a + x * x * inv 2 * b:real =
                                  x * x * inv 2 * (a + b:real)``] THEN
   AP_TERM_TAC THEN SIMP_TAC std_ss [REAL_MUL_ASSOC] THEN
   ONCE_REWRITE_TAC [REAL_ARITH ``inv sig + inv sig1' * sig2' * inv sig:real =
                                  inv sig * (1 + (sig2' * inv sig1'))``] THEN
   Q_TAC SUFF_TAC `(1 + sig2' * inv sig1') = (sig * inv sig1')` THENL
   [DISC_RW_KILL,
    ASM_SIMP_TAC real_ss [GSYM real_div, REAL_EQ_RDIV_EQ] THEN
    ONCE_REWRITE_TAC [REAL_ARITH ``!a b c. (a + b) * c = a * c + b * c:real``] THEN
    ASM_SIMP_TAC real_ss [real_div, GSYM REAL_MUL_ASSOC, REAL_MUL_LINV]] THEN
   ASM_SIMP_TAC real_ss [REAL_MUL_ASSOC, REAL_MUL_LINV]] THEN
  Q.ABBREV_TAC `c = Normal (normal_density 0 (sqrt (sig1 pow 2 + sig2 pow 2)) x)` THEN
  Q_TAC SUFF_TAC `pos_fn_integral lborel (\y. max 0 (c *
     (\y. Normal (normal_density (sig2 pow 2 * x / (sig1 pow 2 + sig2 pow 2))
             (sqrt (sig1 pow 2 * sig2 pow 2 / (sig1 pow 2 + sig2 pow 2))) y)) y)) =
              c * pos_fn_integral lborel (\y. max 0
    ((\y. Normal (normal_density (sig2 pow 2 * x / (sig1 pow 2 + sig2 pow 2))
             (sqrt (sig1 pow 2 * sig2 pow 2 / (sig1 pow 2 + sig2 pow 2))) y)) y))` THENL
  [ALL_TAC,
   MATCH_MP_TAC pos_fn_integral_cmult THEN SIMP_TAC std_ss [measure_space_lborel] THEN
   Q.UNABBREV_TAC `c` THEN `!mu sig x. 0 <= Normal (normal_density mu sig x)` by
    METIS_TAC [extreal_of_num_def, extreal_le_def, normal_density_nonneg] THEN
   ASM_SIMP_TAC std_ss [IN_MEASURABLE_BOREL_normal_density]] THEN
  `!mu sig x. 0 <= Normal (normal_density mu sig x)` by
    METIS_TAC [extreal_of_num_def, extreal_le_def, normal_density_nonneg] THEN
  `0 <= c` by METIS_TAC [] THEN
  ASM_SIMP_TAC real_ss [extreal_max_def, le_mul] THEN DISC_RW_KILL THEN
  `0 <= sig1 pow 2` by ASM_SIMP_TAC std_ss [REAL_LT_IMP_LE] THEN
  `0 < (sig1 pow 2 + sig2 pow 2)` by ASM_SIMP_TAC real_ss [REAL_LT_ADD] THEN
  SIMP_TAC std_ss [real_div] THEN
  ONCE_REWRITE_TAC [REAL_ARITH ``sig2 pow 2 * x * inv (sig1 pow 2 + sig2 pow 2):real =
                                 x * sig2 pow 2 * inv (sig1 pow 2 + sig2 pow 2)``] THEN
  ONCE_REWRITE_TAC [GSYM REAL_MUL_ASSOC] THEN SIMP_TAC std_ss [GSYM real_div] THEN
  Q.ABBREV_TAC `b = sig2 pow 2 / (sig1 pow 2 + sig2 pow 2)` THEN
  `0 < b` by METIS_TAC [REAL_LT_DIV] THEN
  `0 <= b` by ASM_SIMP_TAC std_ss [REAL_LT_IMP_LE] THEN
  `0 <= sig1` by ASM_SIMP_TAC std_ss [REAL_LT_IMP_LE] THEN
  ASM_SIMP_TAC std_ss [SQRT_MUL, POW_2_SQRT] THEN
  ONCE_REWRITE_TAC [REAL_MUL_COMM] THEN
  GEN_REWR_TAC RAND_CONV [GSYM mul_rone] THEN AP_TERM_TAC THEN
  `0 < sqrt b` by METIS_TAC [SQRT_POS_LT] THEN
  `sqrt b <> 0` by METIS_TAC [REAL_LT_IMP_NE] THEN Q.ABBREV_TAC `a = sqrt b` THEN
  Q.ABBREV_TAC `XX = (\z. (b * x) + a * X z)` THEN
  `!z. XX z = (b * x) + a * X z` by METIS_TAC [] THEN
  `normal_rv XX p ((b * x) + a * 0) (abs a * sig1)` by METIS_TAC [normal_rv_affine'] THEN
  POP_ASSUM MP_TAC THEN `abs a = a` by METIS_TAC [ABS_REFL, REAL_LT_IMP_LE] THEN
  ASM_SIMP_TAC real_ss [] THEN DISCH_TAC THEN
  `(\x. PDF p XX x) = PDF p XX` by METIS_TAC [ETA_AX] THEN
  `integral lborel (PDF p XX) = 1` by METIS_TAC [normal_pdf_integral_eq_1] THEN
  `!x. 0 <= PDF p XX x` by METIS_TAC [normal_pdf_nonneg] THEN
  ASSUME_TAC measure_space_lborel THEN
  `pos_fn_integral lborel (\x. PDF p XX x) = 1` by METIS_TAC [integral_pos_fn] THEN
  `UNIV IN measurable_sets lborel` by
   METIS_TAC [lborel, m_space_def, MEASURE_SPACE_MSPACE_MEASURABLE] THEN
  `pos_fn_integral lborel (\z. PDF p XX z * indicator_fn UNIV z) =
      pos_fn_integral lborel
        (\z. Normal (normal_density (b * x) (a * sig1) z) * indicator_fn UNIV z)`
   by METIS_TAC [integral_normal_pdf_eq_density] THEN
  POP_ASSUM MP_TAC THEN SIMP_TAC std_ss [indicator_fn_def, IN_UNIV, mul_rone] THEN
  METIS_TAC []);

val sum_indep_normal = store_thm ("sum_indep_normal",
  ``!p X Y mu1 mu2 sig1 sig2.
     prob_space p /\ 0 < sig1 /\ 0 < sig2 /\
     indep_var p (space borel, subsets borel, (\x. 0)) X
                 (space borel, subsets borel, (\x. 0)) Y /\
     normal_rv X p mu1 sig1 /\ normal_rv Y p mu2 sig2 ==>
     normal_rv (\x. X x + Y x) p (mu1 + mu2) (sqrt (sig1 pow 2 + sig2 pow 2))``,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  Q_TAC SUFF_TAC `indep_var p
   (space borel, subsets borel, (\x. 0)) ((\x. -mu1 + x) o X)
   (space borel, subsets borel, (\x. 0)) ((\x. -mu2 + x) o Y)` THENL
  [SIMP_TAC std_ss [] THEN DISCH_TAC,
   MATCH_MP_TAC indep_var_compose THEN
   Q.EXISTS_TAC `(space borel, subsets borel, (\x. 0))` THEN
   Q.EXISTS_TAC `(space borel, subsets borel, (\x. 0))` THEN
   ASM_SIMP_TAC std_ss [measure_space_borel] THEN
   SIMP_TAC std_ss [m_space_def, measurable_sets_def, SPACE] THEN
   SIMP_TAC std_ss [GSYM borel_measurable] THEN
   CONJ_TAC THEN (MATCH_MP_TAC borel_measurable_add) THENL
   [Q.EXISTS_TAC `(\x. -mu1)` THEN Q.EXISTS_TAC `(\x. x)` THEN
    ASSUME_TAC sigma_algebra_borel THEN
    ASM_SIMP_TAC std_ss [borel_measurable_const] THEN
    Q_TAC SUFF_TAC `(\x:real. x) = I` THENL
    [DISC_RW_KILL, SIMP_TAC std_ss [FUN_EQ_THM]] THEN
    METIS_TAC [borel_measurable, MEASURABLE_I],
    ALL_TAC] THEN
   Q.EXISTS_TAC `(\x. -mu2)` THEN Q.EXISTS_TAC `(\x. x)` THEN
   ASSUME_TAC sigma_algebra_borel THEN
   ASM_SIMP_TAC std_ss [borel_measurable_const] THEN
   Q_TAC SUFF_TAC `(\x:real. x) = I` THENL
   [DISC_RW_KILL, SIMP_TAC std_ss [FUN_EQ_THM]] THEN
   METIS_TAC [borel_measurable, MEASURABLE_I]] THEN
  Q_TAC SUFF_TAC `normal_rv (\x. -mu1 + 1 * X x) p (-mu1 + 1 * mu1) (abs 1 * sig1)` THENL
  [DISCH_TAC,
   MATCH_MP_TAC normal_rv_affine' THEN SIMP_TAC real_ss [] THEN
   METIS_TAC []] THEN
  Q_TAC SUFF_TAC `normal_rv (\x. -mu2 + 1 * Y x) p (-mu2 + 1 * mu2) (abs 1 * sig2)` THENL
  [DISCH_TAC,
   MATCH_MP_TAC normal_rv_affine' THEN SIMP_TAC real_ss [] THEN
   METIS_TAC []] THEN
  Q_TAC SUFF_TAC
  `normal_rv (\x. -mu1 + X x + (-mu2 + Y x)) p 0 (sqrt (sig1 pow 2 + sig2 pow 2))` THENL
  [DISCH_TAC,
   SIMP_TAC std_ss [normal_rv] THEN CONJ_TAC THENL
   [ASM_SIMP_TAC std_ss [random_variable_def, GSYM borel_measurable] THEN
    MATCH_MP_TAC borel_measurable_add THEN Q.EXISTS_TAC `(\x. -mu1 + X x)` THEN
    Q.EXISTS_TAC `(\x. -mu2 + Y x)` THEN SIMP_TAC std_ss [] THEN
    FULL_SIMP_TAC real_ss [normal_rv, random_variable_def, borel_measurable] THEN
    METIS_TAC [prob_space_def, measure_space_def, p_space_def, events_def],
    ALL_TAC] THEN
   SIMP_TAC std_ss [normal_pmeasure, measurable_distr] THEN ABS_TAC THEN
   `s IN subsets borel = s IN measurable_sets lborel` by
    METIS_TAC [lborel, measurable_sets_def] THEN
   POP_ASSUM MP_TAC THEN RW_TAC std_ss [] THEN
   Q.ABBREV_TAC `XX = ((\x. -mu1 + x) o X)` THEN
   Q.ABBREV_TAC `YY = ((\x. -mu2 + x) o Y)` THEN
   Q_TAC SUFF_TAC `!a. a IN measurable_sets (space borel,subsets borel,(\x. 0)) ==>
        (distribution p (\x. XX x + YY x) a =
         measure (convolution
              (distr' p (space borel,subsets borel,(\x. 0)) XX)
              (distr' p (space borel,subsets borel,(\x. 0)) YY)) a)` THENL
   [DISCH_TAC, MATCH_MP_TAC sum_indep_random_variable THEN ASM_SIMP_TAC std_ss []] THEN
   POP_ASSUM (MP_TAC o Q.SPEC `s`) THEN ASM_SIMP_TAC std_ss [measurable_sets_def] THEN
   DISCH_TAC THEN FULL_SIMP_TAC real_ss [o_DEF] THEN
   `distr' p (space borel,subsets borel,(\x. 0)) XX = distr' p lborel XX` by
    METIS_TAC [m_space_def, measurable_sets_def, lborel, space_borel, distr'] THEN
   `distr' p (space borel,subsets borel,(\x. 0)) YY = distr' p lborel YY` by
    METIS_TAC [m_space_def, measurable_sets_def, lborel, space_borel, distr'] THEN
   FULL_SIMP_TAC real_ss [REAL_ARITH ``-x + x = 0:real``, ETA_AX] THEN
   Q_TAC SUFF_TAC `distr' p lborel XX =
    density lborel (\x. Normal (normal_density 0 sig1 x))` THENL
   [DISC_RW_KILL,
    `!x. 0 <= Normal (normal_density 0 sig1 x)` by
     METIS_TAC [extreal_of_num_def, extreal_le_def, normal_density_nonneg] THEN
    SIMP_TAC std_ss [distr', density, GSYM prob_def] THEN ABS_TAC THEN
    `!s. s IN measurable_sets lborel = s IN subsets borel` by
     METIS_TAC [lborel, measurable_sets_def] THEN
    ASM_SIMP_TAC std_ss [extreal_max_def, le_mul, indicator_fn_pos_le] THEN
    FULL_SIMP_TAC std_ss [normal_rv, measurable_distr, distribution_def, FUN_EQ_THM] THEN
    FULL_SIMP_TAC std_ss [normal_pmeasure, p_space_def]] THEN
   Q_TAC SUFF_TAC `distr' p lborel YY =
    density lborel (\x. Normal (normal_density 0 sig2 x))` THENL
   [DISC_RW_KILL,
    `!x. 0 <= Normal (normal_density 0 sig2 x)` by
     METIS_TAC [extreal_of_num_def, extreal_le_def, normal_density_nonneg] THEN
    SIMP_TAC std_ss [distr', density, GSYM prob_def] THEN ABS_TAC THEN
    `!s. s IN measurable_sets lborel = s IN subsets borel` by
     METIS_TAC [lborel, measurable_sets_def] THEN
    ASM_SIMP_TAC std_ss [extreal_max_def, le_mul, indicator_fn_pos_le] THEN
    FULL_SIMP_TAC std_ss [normal_rv, measurable_distr, distribution_def, FUN_EQ_THM] THEN
    FULL_SIMP_TAC std_ss [normal_pmeasure, p_space_def]] THEN

   Q.ABBREV_TAC `f = (\x. Normal (normal_density 0 sig1 x))` THEN
   Q.ABBREV_TAC `g = (\x. Normal (normal_density 0 sig2 x))` THEN
   Q_TAC SUFF_TAC `measure (convolution (density lborel f) (density lborel g)) s =
    measure (density lborel (\x. pos_fn_integral lborel (\y. f (x - y) * g y))) s` THENL
   [DISC_RW_KILL,
    MATCH_MP_TAC measure_convolution_density THEN
    Q.UNABBREV_TAC `f` THEN Q.UNABBREV_TAC `g` THEN
    ASM_SIMP_TAC std_ss [IN_MEASURABLE_BOREL_normal_density] THEN
    ASM_SIMP_TAC std_ss [normal_density_nonneg, extreal_of_num_def, extreal_le_def] THEN
    Q_TAC SUFF_TAC `sigma_finite_measure
     (density lborel (\x. Normal (normal_density 0 sig1 x)))` THENL
    [DISCH_TAC,
     SIMP_TAC std_ss [sigma_finite_measure] THEN
     SIMP_TAC std_ss [density, m_space_def, measurable_sets_def, measure_def] THEN
     Q.EXISTS_TAC `{m_space lborel}` THEN SIMP_TAC std_ss [countable_sing] THEN
     SIMP_TAC std_ss [BIGUNION_SING, SUBSET_DEF, IN_SING] THEN
     SIMP_TAC std_ss [measure_space_lborel, MEASURE_SPACE_MSPACE_MEASURABLE] THEN
     `m_space lborel = UNIV` by METIS_TAC [lborel, m_space_def] THEN
     ASM_SIMP_TAC std_ss [indicator_fn_def, IN_UNIV, mul_rone] THEN
     `!mu sig x. 0 <= Normal (normal_density mu sig x)` by
      METIS_TAC [extreal_of_num_def, extreal_le_def, normal_density_nonneg] THEN
     ASM_SIMP_TAC std_ss [extreal_max_def] THEN
     `!x. 0 <= PDF p XX x` by METIS_TAC [normal_pdf_nonneg] THEN
     `pos_fn_integral lborel (PDF p XX) = 1` by
      METIS_TAC [normal_pdf_integral_eq_1, integral_pos_fn, measure_space_lborel] THEN
     `m_space lborel IN measurable_sets lborel` by
      METIS_TAC [MEASURE_SPACE_MSPACE_MEASURABLE, measure_space_lborel] THEN
     `pos_fn_integral lborel (\x. PDF p XX x * indicator_fn UNIV x) =
       pos_fn_integral lborel
         (\x. Normal (normal_density 0 sig1 x) * indicator_fn UNIV x)` by
      METIS_TAC [integral_normal_pdf_eq_density] THEN
     FULL_SIMP_TAC std_ss [indicator_fn_def, IN_UNIV, mul_rone] THEN
     POP_ASSUM (ASSUME_TAC o ONCE_REWRITE_RULE [EQ_SYM_EQ]) THEN
     `(\x. PDF p XX x) = PDF p XX` by METIS_TAC [ETA_AX] THEN
     ASM_SIMP_TAC std_ss [num_not_infty]] THEN
    Q_TAC SUFF_TAC `sigma_finite_measure
     (density lborel (\x. Normal (normal_density 0 sig2 x)))` THENL
    [DISCH_TAC,
     SIMP_TAC std_ss [sigma_finite_measure] THEN
     SIMP_TAC std_ss [density, m_space_def, measurable_sets_def, measure_def] THEN
     Q.EXISTS_TAC `{m_space lborel}` THEN SIMP_TAC std_ss [countable_sing] THEN
     SIMP_TAC std_ss [BIGUNION_SING, SUBSET_DEF, IN_SING] THEN
     SIMP_TAC std_ss [measure_space_lborel, MEASURE_SPACE_MSPACE_MEASURABLE] THEN
     `m_space lborel = UNIV` by METIS_TAC [lborel, m_space_def] THEN
     ASM_SIMP_TAC std_ss [indicator_fn_def, IN_UNIV, mul_rone] THEN
     `!mu sig x. 0 <= Normal (normal_density mu sig x)` by
      METIS_TAC [extreal_of_num_def, extreal_le_def, normal_density_nonneg] THEN
     ASM_SIMP_TAC std_ss [extreal_max_def] THEN
     `!x. 0 <= PDF p YY x` by METIS_TAC [normal_pdf_nonneg] THEN
     `pos_fn_integral lborel (PDF p YY) = 1` by
      METIS_TAC [normal_pdf_integral_eq_1, integral_pos_fn, measure_space_lborel] THEN
     `m_space lborel IN measurable_sets lborel` by
      METIS_TAC [MEASURE_SPACE_MSPACE_MEASURABLE, measure_space_lborel] THEN
     `pos_fn_integral lborel (\x. PDF p YY x * indicator_fn UNIV x) =
       pos_fn_integral lborel
         (\x. Normal (normal_density 0 sig2 x) * indicator_fn UNIV x)` by
      METIS_TAC [integral_normal_pdf_eq_density] THEN
     FULL_SIMP_TAC std_ss [indicator_fn_def, IN_UNIV, mul_rone] THEN
     POP_ASSUM (ASSUME_TAC o ONCE_REWRITE_RULE [EQ_SYM_EQ]) THEN
     `(\x. PDF p YY x) = PDF p YY` by METIS_TAC [ETA_AX] THEN
     ASM_SIMP_TAC std_ss [num_not_infty]] THEN
    ASM_SIMP_TAC std_ss [finite_measure, density, m_space_def, measure_def] THEN
    SIMP_TAC std_ss [measure_space_lborel, MEASURE_SPACE_MSPACE_MEASURABLE] THEN
    `m_space lborel = UNIV` by METIS_TAC [lborel, m_space_def] THEN
    ASM_SIMP_TAC std_ss [indicator_fn_def, IN_UNIV, mul_rone] THEN
    `!mu sig x. 0 <= Normal (normal_density mu sig x)` by
     METIS_TAC [extreal_of_num_def, extreal_le_def, normal_density_nonneg] THEN
    ASM_SIMP_TAC std_ss [extreal_max_def] THEN
    `!x. 0 <= PDF p XX x` by METIS_TAC [normal_pdf_nonneg] THEN
    `pos_fn_integral lborel (PDF p XX) = 1` by
     METIS_TAC [normal_pdf_integral_eq_1, integral_pos_fn, measure_space_lborel] THEN
    `m_space lborel IN measurable_sets lborel` by
     METIS_TAC [MEASURE_SPACE_MSPACE_MEASURABLE, measure_space_lborel] THEN
    `pos_fn_integral lborel (\x. PDF p XX x * indicator_fn UNIV x) =
      pos_fn_integral lborel
        (\x. Normal (normal_density 0 sig1 x) * indicator_fn UNIV x)` by
     METIS_TAC [integral_normal_pdf_eq_density] THEN
    FULL_SIMP_TAC std_ss [indicator_fn_def, IN_UNIV, mul_rone] THEN
    POP_ASSUM (ASSUME_TAC o ONCE_REWRITE_RULE [EQ_SYM_EQ]) THEN
    `(\x. PDF p XX x) = PDF p XX` by METIS_TAC [ETA_AX] THEN
    ASM_SIMP_TAC std_ss [num_not_infty] THEN
    `!x. 0 <= PDF p YY x` by METIS_TAC [normal_pdf_nonneg] THEN
    `pos_fn_integral lborel (PDF p YY) = 1` by
     METIS_TAC [normal_pdf_integral_eq_1, integral_pos_fn, measure_space_lborel] THEN
    `m_space lborel IN measurable_sets lborel` by
     METIS_TAC [MEASURE_SPACE_MSPACE_MEASURABLE, measure_space_lborel] THEN
    `pos_fn_integral lborel (\x. PDF p YY x * indicator_fn UNIV x) =
      pos_fn_integral lborel
        (\x. Normal (normal_density 0 sig2 x) * indicator_fn UNIV x)` by
     METIS_TAC [integral_normal_pdf_eq_density] THEN
    FULL_SIMP_TAC std_ss [indicator_fn_def, IN_UNIV, mul_rone] THEN
    POP_ASSUM (ASSUME_TAC o ONCE_REWRITE_RULE [EQ_SYM_EQ]) THEN
    `(\x. PDF p YY x) = PDF p YY` by METIS_TAC [ETA_AX] THEN
    ASM_SIMP_TAC std_ss [num_not_infty]] THEN
   ASM_SIMP_TAC std_ss [density, measure_def, normal_pmeasure] THEN
   Q.UNABBREV_TAC `f` THEN Q.UNABBREV_TAC `g` THEN SIMP_TAC std_ss [] THEN
   Q_TAC SUFF_TAC
   `!x. pos_fn_integral lborel
        (\y. Normal (normal_density 0 sig1 (x - y)) *
             Normal (normal_density 0 sig2 y)) =
      Normal (normal_density 0 (sqrt (sig1 pow 2 + sig2 pow 2)) x)` THENL
   [DISC_RW_KILL, MATCH_MP_TAC conv_normal_density_zero_mean THEN METIS_TAC []] THEN
   `!mu sig x. 0 <= Normal (normal_density mu sig x)` by
     METIS_TAC [extreal_of_num_def, extreal_le_def, normal_density_nonneg] THEN
   ASM_SIMP_TAC std_ss [extreal_max_def, le_mul, indicator_fn_pos_le]] THEN
  Q_TAC SUFF_TAC `normal_rv (\x. X x + Y x) p ((mu1 + mu2) + 1 * 0)
                            (abs 1 * (sqrt (sig1 pow 2 + sig2 pow 2)))` THENL
  [ALL_TAC,
   MATCH_MP_TAC normal_rv_affine' THEN
   Q.EXISTS_TAC `(\x. -mu1 + X x + (-mu2 + Y x))` THEN
   `0 < sig1 pow 2 /\ 0 < sig2 pow 2` by METIS_TAC [REAL_POW_LT] THEN
   `0 < (sig1 pow 2 + sig2 pow 2)` by ASM_SIMP_TAC real_ss [REAL_LT_ADD] THEN
   ASM_SIMP_TAC real_ss [SQRT_POS_LT] THEN REAL_ARITH_TAC] THEN
  RW_TAC real_ss []);

val indep_vars_subset = store_thm ("indep_vars_subset",
  ``!p M X ii J. indep_vars p M X ii /\ J SUBSET ii ==>
                 indep_vars p M X J``,
  RW_TAC std_ss [indep_vars, indep_sets] THEN ASM_SET_TAC []);

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* ------------------------------------------------------------------------- *)

val Pi_mem = store_thm ("Pi_mem",
  ``!f A B x. f IN Pi A B ==> x IN A ==> f x IN B x``,
  SIMP_TAC std_ss [Pi_iff]);

val undefined = Define `undefined = @x. x IN {}`;

val extensional = Define
   `extensional A = {f | !x. x NOTIN A ==> (f x = undefined)}`;

val extensional_empty = store_thm ("extensional_empty",
  ``extensional {} = {\x. undefined}``,
  SIMP_TAC std_ss [extensional, NOT_IN_EMPTY] THEN SET_TAC []);

val restrict = Define `restrict f A = (\x. if x IN A then f x else undefined)`;

val restrict_extensional = store_thm ("restrict_extensional",
  ``!f A. restrict f A IN extensional A``,
  RW_TAC std_ss [restrict, extensional, GSPECIFICATION]);

val PiE = Define `PiE s t = Pi s t INTER extensional s`;

val PiE_iff = store_thm ("PiE_iff",
  ``!f ii X. f IN PiE ii X = (!i. i IN ii ==> (f i IN X i)) /\ f IN extensional ii``,
  RW_TAC std_ss [Pi_iff, PiE, IN_INTER]);

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* ------------------------------------------------------------------------- *)

val prod_emb = Define
   `prod_emb ii M k X = (PREIMAGE (\x. restrict x k) X) INTER (PiE ii (\i. m_space (M i)))`;

val prod_emb_iff = store_thm ("prod_emb_iff",
  ``!f ii M k X. f IN prod_emb ii M k X =
     f IN extensional ii /\ restrict f k IN X /\ (!i. i IN ii ==> f i IN m_space (M i))``,
  RW_TAC std_ss [prod_emb, PiE, Pi_iff, IN_PREIMAGE, IN_INTER] THEN
  SET_TAC []);

val prod_emb_empty = store_thm ("prod_emb_empty",
  ``!ii M k. prod_emb ii M k {} = {}``,
  SIMP_TAC std_ss [prod_emb, PREIMAGE_def] THEN SET_TAC []);

val prod_emb_Un = store_thm ("prod_emb_Un",
  ``!ii M k A B. prod_emb ii M k (A UNION B) = prod_emb ii M k A UNION prod_emb ii M k B``,
  RW_TAC std_ss [prod_emb, PREIMAGE_def] THEN SET_TAC []);

val prod_emb_Int = store_thm ("prod_emb_Int",
  ``!ii M k A B. prod_emb ii M k (A INTER B) = prod_emb ii M k A INTER prod_emb ii M k B``,
  RW_TAC std_ss [prod_emb, PREIMAGE_def] THEN SET_TAC []);

val prod_emb_UN = store_thm ("prod_emb_UN",
  ``!ii M k f. prod_emb ii M k (BIGUNION {f i | i IN UNIV}) =
               BIGUNION {prod_emb ii M k (f i) | i IN UNIV}``,
  RW_TAC std_ss [prod_emb, PREIMAGE_def] THEN
  SIMP_TAC std_ss [GSPECIFICATION, EXTENSION, IN_INTER, IN_BIGUNION] THEN
  GEN_TAC THEN EQ_TAC THEN RW_TAC std_ss [] THENL
  [ALL_TAC, ASM_SET_TAC [], ASM_SET_TAC []] THEN
  Q.EXISTS_TAC `PiE ii (\i. m_space (M i)) INTER (\x. restrict x k IN s)` THEN
  ASM_SET_TAC []);

val prod_emb_INT = store_thm ("prod_emb_INT",
  ``!ii M k f. prod_emb ii M k (BIGINTER {f i | i IN UNIV}) =
               BIGINTER {prod_emb ii M k (f i) | i IN UNIV}``,
  RW_TAC std_ss [prod_emb, PREIMAGE_def] THEN
  SIMP_TAC std_ss [GSPECIFICATION, EXTENSION, IN_INTER, IN_BIGINTER] THEN
  GEN_TAC THEN EQ_TAC THEN RW_TAC std_ss [] THENL
  [ASM_SIMP_TAC std_ss [] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN SET_TAC [],
   MATCH_MP_TAC (SET_RULE ``x IN PiE ii (\i. m_space (M i)) /\ B ==> B``) THEN
   FIRST_X_ASSUM (MP_TAC o Q.SPEC `PiE ii (\i. m_space (M i)) INTER (\x. restrict x k IN P)`) THEN
   SIMP_TAC std_ss [IN_INTER, IN_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN
   Q.EXISTS_TAC `i` THEN FULL_SIMP_TAC std_ss [IN_DEF] THEN METIS_TAC [],
   ALL_TAC] THEN
  MATCH_MP_TAC (SET_RULE ``A /\ (restrict x k IN f i) ==> A``) THEN
  FIRST_X_ASSUM (MP_TAC o Q.SPEC `PiE ii (\i. m_space (M i)) INTER (\x. restrict x k IN f i)`) THEN
  SIMP_TAC std_ss [IN_INTER, IN_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN
  Q.EXISTS_TAC `i` THEN `i IN UNIV` by SET_TAC [] THEN
  FULL_SIMP_TAC std_ss [IN_DEF] THEN METIS_TAC []);

val prod_emb_Diff = store_thm ("prod_emb_Diff",
  ``!ii M k A B. prod_emb ii M k (A DIFF B) = prod_emb ii M k A DIFF prod_emb ii M k B``,
  RW_TAC std_ss [prod_emb, PREIMAGE_def] THEN SET_TAC []);

val prod_emb_PiE = store_thm ("prod_emb_PiE",
  ``!J ii E M. J SUBSET ii ==> (!i. i IN J ==> E i SUBSET m_space (M i)) ==>
     (prod_emb ii M J (PiE J (\i. E i)) =
      PiE ii (\i. if i IN J then E i else m_space (M i)))``,
  RW_TAC std_ss [prod_emb, PiE_iff, EXTENSION, IN_INTER, IN_PREIMAGE] THEN
  SIMP_TAC std_ss [restrict_extensional] THEN EQ_TAC THEN
  RW_TAC std_ss [] THENL
  [RW_TAC std_ss [] THEN FULL_SIMP_TAC std_ss [restrict],
   RW_TAC std_ss [restrict] THEN ASM_SET_TAC [],
   ALL_TAC] THEN
  ASM_SET_TAC []);

val prod_emb_PiE_same_index = store_thm ("prod_emb_PiE_same_index",
  ``!ii E M. (!i. i IN ii ==> E i SUBSET m_space (M i)) ==>
             (prod_emb ii M ii (PiE ii E) = PiE ii E)``,
  RW_TAC std_ss [prod_emb, PiE_iff, EXTENSION, IN_INTER, IN_PREIMAGE] THEN
  SIMP_TAC std_ss [restrict_extensional] THEN EQ_TAC THEN
  RW_TAC std_ss [] THENL
  [RW_TAC std_ss [] THEN FULL_SIMP_TAC std_ss [restrict],
   RW_TAC std_ss [restrict] THEN ASM_SET_TAC [],
   ALL_TAC] THEN
  ASM_SET_TAC []);

val extend_measure = Define
   `extend_measure sp ii G u =
    if ?u'. (!i. i IN ii ==> (u' (G i) = u i)) /\ (?i. i IN ii /\ (u i <> 0))
    then measure_of (sp, (IMAGE G ii), (@u'. (!i. i IN ii ==> (u' (G i) = u i))))
    else measure_of (sp, (IMAGE G ii), (\x. 0))`;

val space_extend_measure = store_thm ("space_extend_measure",
  ``!sp ii G u. (m_space (extend_measure sp ii G u) = sp)``,
  RW_TAC std_ss [extend_measure, measure_of, m_space_def]);

val sets_extend_measure = store_thm ("sets_extend_measure",
  ``!G ii sp u. IMAGE G ii SUBSET POW sp ==>
      (measurable_sets (extend_measure sp ii G u) = sigma_sets sp (IMAGE G ii))``,
  RW_TAC std_ss [extend_measure, measurable_sets_def, measure_of]);

val measure_space_extend_measure = store_thm ("measure_space_extend_measure",
  ``!sp ii G u v i. (M = extend_measure sp ii G u) /\
                (!i. i IN ii ==> (v (G i) = u i)) /\ IMAGE G ii SUBSET POW sp /\
                positive (m_space M, measurable_sets M, v) /\
                countably_additive (m_space M, measurable_sets M, v) /\
                i IN ii ==> measure_space M``,
  RW_TAC std_ss [] THEN SIMP_TAC std_ss [extend_measure] THEN
  Q_TAC SUFF_TAC `measurable_sets (extend_measure sp ii G u) =
                  sigma_sets sp (IMAGE G ii)` THENL
  [DISCH_TAC,
   MATCH_MP_TAC sets_extend_measure THEN ASM_SIMP_TAC std_ss []] THEN
  FULL_SIMP_TAC std_ss [space_extend_measure, sets_extend_measure] THEN
  COND_CASES_TAC THENL
  [ALL_TAC,
   SIMP_TAC std_ss [measure_space_def, measure_of] THEN
   SIMP_TAC std_ss [m_space_def, measurable_sets_def, measure_def] THEN
   ASM_SIMP_TAC std_ss [] THEN CONJ_TAC THENL
   [MATCH_MP_TAC sigma_algebra_sigma_sets THEN ASM_SIMP_TAC std_ss [], ALL_TAC] THEN
   CONJ_TAC THENL [SIMP_TAC std_ss [positive_def, measure_def, le_refl], ALL_TAC] THEN
   SIMP_TAC std_ss [countably_additive_def] THEN
   RW_TAC std_ss [IN_FUNSET, measure_def, suminf_0, o_DEF]] THEN
  SIMP_TAC std_ss [measure_space_def, measure_of] THEN
  SIMP_TAC std_ss [m_space_def, measurable_sets_def, measure_def] THEN
  ASM_SIMP_TAC std_ss [] THEN CONJ_TAC THENL
  [MATCH_MP_TAC sigma_algebra_sigma_sets THEN ASM_SIMP_TAC std_ss [], ALL_TAC] THEN
  CONJ_TAC THENL
  [SIMP_TAC std_ss [positive_def, measure_def, measurable_sets_def] THEN
   RW_TAC std_ss [le_refl], ALL_TAC] THEN
  SIMP_TAC std_ss [countably_additive_def, measure_def, measurable_sets_def] THEN
  RW_TAC std_ss [m_space_def, o_DEF, suminf_0] THEN
  FULL_SIMP_TAC std_ss [IN_FUNSET, IN_UNIV]);

val measure_space_extend_measure_Pair = store_thm ("measure_space_extend_measure_Pair",
  ``!sp ii G u v i j.
      (M = extend_measure sp {(i,j) | (i,j) IN ii} (\(i,j). G (i,j)) (\(i,j). u (i,j))) /\
      (!(i,j). (i,j) IN ii ==> (v (G (i,j)) = u (i,j))) /\
      (!(i,j). (i,j) IN ii ==> G (i,j) IN POW sp) /\
      positive (m_space M, measurable_sets M, v) /\
      countably_additive (m_space M, measurable_sets M, v) /\
      (i,j) IN ii ==> (measure_space M)``,
  RW_TAC std_ss [] THEN Q.ABBREV_TAC `k = (i,j)` THEN
  Q.ABBREV_TAC `M = extend_measure sp ii G u` THEN
  Q_TAC SUFF_TAC `
      (M = extend_measure sp ii G u) /\
      (!i. i IN ii ==> (v (G i) = u i)) /\
      (IMAGE G ii SUBSET POW sp) /\
      positive (m_space M, measurable_sets M, v) /\
      countably_additive (m_space M, measurable_sets M, v) /\
      k IN ii` THENL
  [DISCH_THEN (MP_TAC o MATCH_MP measure_space_extend_measure) THEN
   Q.UNABBREV_TAC `M` THEN Q.UNABBREV_TAC `k` THEN
   Q_TAC SUFF_TAC `!i j. {(i,j) | (i,j) IN ii} = ii` THENL
   [DISC_RW_KILL,
    RW_TAC std_ss [EXTENSION, GSPECIFICATION, EXISTS_PROD] THEN
    METIS_TAC [pair_CASES]] THEN
   Q_TAC SUFF_TAC `!i j. (\(i,j). G (i,j)) = G` THENL
   [DISC_RW_KILL,
    RW_TAC std_ss [FUN_EQ_THM] THEN
    `?a b. x = (a,b)` by METIS_TAC [pair_CASES] THEN
    ASM_SIMP_TAC std_ss []] THEN
   Q_TAC SUFF_TAC `!i j. (\(i,j). u (i,j)) = u` THENL
   [ALL_TAC,
    RW_TAC std_ss [FUN_EQ_THM] THEN
    `?a b. x = (a,b)` by METIS_TAC [pair_CASES] THEN
    ASM_SIMP_TAC std_ss []] THEN
   SIMP_TAC std_ss [], ALL_TAC] THEN
  Q.UNABBREV_TAC `M` THEN Q.UNABBREV_TAC `k` THEN
  ASM_SIMP_TAC std_ss [IMAGE_DEF, SUBSET_DEF, GSPECIFICATION] THEN
  Q_TAC SUFF_TAC `!i j. ii = {(i,j) | (i,j) IN ii}` THENL
  [DISC_RW_KILL,
   RW_TAC std_ss [EXTENSION, GSPECIFICATION, EXISTS_PROD] THEN
   METIS_TAC [pair_CASES]] THEN
  Q_TAC SUFF_TAC `!i j. G = (\(i,j). G (i,j))` THENL
  [DISC_RW_KILL,
   RW_TAC std_ss [FUN_EQ_THM] THEN
   `?a b. x = (a,b)` by METIS_TAC [pair_CASES] THEN
   ASM_SIMP_TAC std_ss []] THEN
  Q_TAC SUFF_TAC `!i j. u = (\(i,j). u (i,j))` THENL
  [DISC_RW_KILL,
   RW_TAC std_ss [FUN_EQ_THM] THEN
   `?a b. x = (a,b)` by METIS_TAC [pair_CASES] THEN
   ASM_SIMP_TAC std_ss []] THEN
  ASM_SIMP_TAC std_ss [] THEN RW_TAC std_ss [] THENL
  [FULL_SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD] THEN
   POP_ASSUM MP_TAC THEN Q.SPEC_TAC (`p_2`, `p_2`) THEN
   Q.SPEC_TAC (`p_1`, `p_1`) THEN
   Q_TAC SUFF_TAC `!p_1 p_2. (\p_1 p_2. (p_1,p_2) IN ii ==>
                             (v (G (p_1,p_2)) = u (p_1,p_2))) p_1 p_2` THENL
   [SIMP_TAC std_ss [], ALL_TAC] THEN
   REWRITE_TAC [PFORALL_THM] THEN ASM_SIMP_TAC std_ss [],
   ALL_TAC] THEN
  FULL_SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD] THEN
  POP_ASSUM MP_TAC THEN Q.SPEC_TAC (`p_2`, `p_2`) THEN
  Q.SPEC_TAC (`p_1`, `p_1`) THEN
  Q_TAC SUFF_TAC `!p_1 p_2. (\p_1 p_2. (p_1,p_2) IN ii ==> G (p_1,p_2) IN POW sp) p_1 p_2` THENL
  [SIMP_TAC std_ss [], ALL_TAC] THEN
  REWRITE_TAC [PFORALL_THM] THEN ASM_SIMP_TAC std_ss []);

val PiM = Define `PiM ii M =
      extend_measure (PiE ii (\i. m_space (M i)))
      {(J,X) | (J <> {} \/ (ii = {})) /\ FINITE J /\ J SUBSET ii /\
               X IN Pi J (\i. measurable_sets (M i))}
      (\(J,X). prod_emb ii M J (PiE J (\i. X i)))
      (\(J,X). Normal (product (J UNION {i | i IN ii /\ measure (M i) (m_space (M i)) <> 1})
                  (\j. if j IN J then real (measure (M j)(X j))
                                 else real (measure (M j)(m_space (M j))))))`;

val prod_algebra = Define
   `prod_algebra ii M = IMAGE (\(J,X). prod_emb ii M J (PiE J (\i. X i)))
     {(J,X) | (J <> {} \/ (ii = {})) /\ FINITE J /\ J SUBSET ii /\
               X IN Pi J (\i. measurable_sets (M i))}`;

val prod_algebraI = store_thm ("prod_algebraI",
  ``!ii M J X E. (J <> {} \/ (ii = {})) /\ FINITE J /\ J SUBSET ii /\
               (!i. i IN J ==> E i IN measurable_sets (M i)) /\
                X IN Pi J (\i. measurable_sets (M i)) ==>
          prod_emb ii M J (PiE J (\i. X i)) IN prod_algebra ii M``,
  SIMP_TAC std_ss [prod_algebra, IN_IMAGE] THEN REPEAT GEN_TAC THEN
  REPEAT DISCH_TAC THEN Q.EXISTS_TAC `(J,X)` THEN SIMP_TAC std_ss [] THEN
  ASM_SET_TAC []);

val prod_algebraE = store_thm ("prod_algebraE",
  ``!A ii M. A IN prod_algebra ii M ==>
    ?J E. (A = prod_emb ii M J (PiE J (\j. E j))) /\ FINITE J /\
              (J <> {} \/ (ii = {})) /\ J SUBSET ii /\
              (!i. i IN J ==> E i IN measurable_sets (M i))``,
  RW_TAC std_ss [prod_algebra, IN_IMAGE, GSPECIFICATION, EXISTS_PROD] THEN
  Q.EXISTS_TAC `p_1` THEN Q.EXISTS_TAC `p_2` THEN
  FULL_SIMP_TAC std_ss [Pi_iff]);

val prod_algebra_sets_into_space = store_thm ("prod_algebra_sets_into_space",
  ``!ii M. prod_algebra ii M SUBSET POW (PiE ii (\i. m_space (M i)))``,
  RW_TAC std_ss [prod_algebra, prod_emb, SUBSET_DEF, IN_POW] THEN
  FULL_SIMP_TAC std_ss [PiE, Pi_iff, IN_IMAGE, IN_INTER] THEN
  POP_ASSUM MP_TAC THEN ASM_SIMP_TAC std_ss [] THEN
  `?a b. x'' = (a,b)` by METIS_TAC [pair_CASES] THEN
  FULL_SIMP_TAC std_ss [IN_PREIMAGE, IN_INTER] THEN
  RW_TAC std_ss [Pi_iff]);

val space_PiM = store_thm ("space_PiM",
  ``!ii M. m_space (PiM ii (\i. M i)) = PiE ii (\i. m_space (M i))``,
  RW_TAC std_ss [PiM, prod_algebra, m_space_def, space_extend_measure]);

val sets_PiM = store_thm ("sets_PiM",
  ``!ii M. measurable_sets (PiM ii (\i. M i)) =
           sigma_sets (PiE ii (\i. m_space (M i))) (prod_algebra ii M)``,
  RW_TAC std_ss [prod_algebra, PiM, ETA_AX] THEN
  MATCH_MP_TAC sets_extend_measure THEN
  SIMP_TAC std_ss [SIMP_RULE std_ss [ETA_AX] (GSYM prod_algebra)] THEN
  SIMP_TAC std_ss [prod_algebra_sets_into_space]);

val sigma_sets_eqI = store_thm ("sigma_sets_eqI",
 ``!A B M. (!a. a IN A ==> a IN sigma_sets M B) /\
           (!b. b IN B ==> b IN sigma_sets M A) ==>
           (sigma_sets M A = sigma_sets M B)``,
  RW_TAC std_ss [FUN_EQ_THM] THEN EQ_TAC THEN
  (MATCH_MP_TAC sigma_sets_ind THEN
   FULL_SIMP_TAC std_ss [sigma_sets_rules, IN_DEF]));

val finite_INT = store_thm ("finite_INT",
  ``!ii A M. Int_stable M /\ FINITE ii /\ ii <> {} /\
                (!i. i IN ii ==> A i IN M) ==>
             BIGINTER {A i | i IN ii} IN M``,
  REPEAT GEN_TAC THEN SIMP_TAC std_ss [GSYM AND_IMP_INTRO] THEN
  DISCH_TAC THEN Q.SPEC_TAC (`ii`,`ii`) THEN SET_INDUCT_TAC THEN RW_TAC std_ss [] THEN
  Q_TAC SUFF_TAC `BIGINTER {A i | i IN e INSERT s} = BIGINTER {A i | i IN s} INTER A e` THENL
  [DISC_RW_KILL, SET_TAC []] THEN
  ASM_CASES_TAC ``s = {}:'a->bool`` THENL
  [ASM_SIMP_TAC std_ss [GSYM IMAGE_DEF, IMAGE_EMPTY, BIGINTER_EMPTY] THEN
   SIMP_TAC std_ss [INTER_UNIV] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
   SET_TAC [], ALL_TAC] THEN
  FULL_SIMP_TAC std_ss [Int_stable] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_SET_TAC []);

val sets_PiM_single = store_thm ("sets_PiM_single",
  ``!ii M. measurable_sets (PiM ii M) =
           sigma_sets (PiE ii (\i. m_space (M i)))
           {{f | f IN PiE n (\i. m_space (m i)) /\ f i IN A} | (m = M) /\ (n = ii) /\
               i IN ii /\ A IN measurable_sets (M i)}``,
  REPEAT GEN_TAC THEN SIMP_TAC std_ss [SIMP_RULE std_ss [ETA_AX] sets_PiM] THEN
  MATCH_MP_TAC sigma_sets_eqI THEN RW_TAC std_ss [] THENL
  [FIRST_ASSUM (ASSUME_TAC o MATCH_MP prod_algebraE) THEN
   ASM_CASES_TAC ``ii = {}:'a->bool`` THEN FULL_SIMP_TAC std_ss [] THENL
   [Q_TAC SUFF_TAC `prod_emb {} M J (PiE J (\j. E j)) = {(\x. undefined)}` THENL
    [DISCH_TAC THEN ASM_SIMP_TAC std_ss [],
     SIMP_TAC std_ss [prod_emb, INTER_DEF, IN_INTER, PiE, Pi_iff] THEN
     SIMP_TAC std_ss [GSPECIFICATION, IN_PREIMAGE, NOT_IN_EMPTY] THEN
     SIMP_TAC std_ss [EXTENSION, extensional_empty, GSPECIFICATION] THEN
     FULL_SIMP_TAC std_ss [IN_SING, restrict_extensional, Pi_iff] THEN GEN_TAC THEN
     Q_TAC SUFF_TAC `(!i. i IN J ==> restrict x J i IN E i)` THENL
     [DISCH_TAC THEN ASM_SIMP_TAC std_ss [FUN_EQ_THM, IN_DEF], ALL_TAC] THEN
     ASM_SET_TAC []] THEN
    Q_TAC SUFF_TAC `(PiE {} (\i. m_space (M i))) = {(\x. undefined)}` THENL
    [ASM_SIMP_TAC std_ss [sigma_sets_top], ALL_TAC] THEN
    SIMP_TAC std_ss [PiE, EXTENSION, IN_INTER, Pi_iff, NOT_IN_EMPTY] THEN
    SIMP_TAC std_ss [extensional_empty, IN_SING],
    ALL_TAC] THEN
   Q_TAC SUFF_TAC `prod_emb ii M J (PiE J (\j. E j)) =
    BIGINTER {{f | f IN PiE ii (\i. m_space (M i)) /\ f j IN E j} | j IN J}` THENL
   [DISCH_TAC THEN ASM_SIMP_TAC std_ss [],
    SIMP_TAC std_ss [prod_emb, INTER_DEF, IN_INTER, PiE, Pi_iff] THEN
    SIMP_TAC std_ss [GSPECIFICATION, IN_PREIMAGE, NOT_IN_EMPTY] THEN
    SIMP_TAC std_ss [EXTENSION, extensional_empty, GSPECIFICATION, IN_BIGINTER] THEN
    FULL_SIMP_TAC std_ss [IN_SING, restrict_extensional, Pi_iff] THEN GEN_TAC THEN
    EQ_TAC THEN RW_TAC std_ss [] THEN FULL_SIMP_TAC std_ss [restrict] THENL
    [FIRST_X_ASSUM (MP_TAC o Q.SPEC `(\x. (!i. i IN ii ==> x i IN m_space (M i)) /\
              x IN extensional ii /\ x j IN E j)`) THEN
     RW_TAC std_ss [] THEN
     Q_TAC SUFF_TAC `x IN (\x. (!i. i IN ii ==> x i IN m_space (M i)) /\
                     x IN extensional ii /\ x j IN E j)` THENL
     [ALL_TAC,
      FIRST_X_ASSUM MATCH_MP_TAC THEN Q.EXISTS_TAC `j` THEN
      ASM_SIMP_TAC std_ss [IN_DEF]] THEN
     SIMP_TAC std_ss [IN_DEF],
     FULL_SIMP_TAC std_ss [GSYM MEMBER_NOT_EMPTY] THEN
     FIRST_X_ASSUM (MP_TAC o Q.SPEC `(\x. (!i. i IN ii ==> x i IN m_space (M i)) /\
              x IN extensional ii /\ x x' IN E x')`) THEN
     RW_TAC std_ss [] THEN
     Q_TAC SUFF_TAC `x IN (\x. (!i. i IN ii ==> x i IN m_space (M i)) /\
                     x IN extensional ii /\ x x' IN E x')` THENL
     [ALL_TAC,
      FIRST_X_ASSUM MATCH_MP_TAC THEN Q.EXISTS_TAC `x'` THEN
      ASM_SIMP_TAC std_ss [IN_DEF]] THEN
     FULL_SIMP_TAC std_ss [IN_DEF],
     ALL_TAC] THEN
    FULL_SIMP_TAC std_ss [GSYM MEMBER_NOT_EMPTY] THEN
    FIRST_X_ASSUM (MP_TAC o Q.SPEC `(\x. (!i. i IN ii ==> x i IN m_space (M i)) /\
             x IN extensional ii /\ x x' IN E x')`) THEN
    RW_TAC std_ss [] THEN
    Q_TAC SUFF_TAC `x IN (\x. (!i. i IN ii ==> x i IN m_space (M i)) /\
                    x IN extensional ii /\ x x' IN E x')` THENL
    [ALL_TAC,
     FIRST_X_ASSUM MATCH_MP_TAC THEN Q.EXISTS_TAC `x'` THEN
     ASM_SIMP_TAC std_ss [IN_DEF]] THEN
    FULL_SIMP_TAC std_ss [IN_DEF]] THEN
   Q_TAC SUFF_TAC `BIGINTER
    {(\j. {f | f IN PiE ii (\i. m_space (M i)) /\ f j IN E j}) j | j IN J} IN
    sigma_sets (PiE ii (\i. m_space (M i)))
     {{f | f IN PiE n (\i. m_space (m i)) /\ f i IN A} |
      (m = M) /\ (n = ii) /\ i IN ii /\ A IN measurable_sets (M i)}` THENL
   [SIMP_TAC std_ss [], ALL_TAC] THEN
   MATCH_MP_TAC finite_INT THEN CONJ_TAC THENL
   [ALL_TAC, RW_TAC std_ss [] THEN MATCH_MP_TAC sigma_sets_basic THEN
    SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD] THEN
    Q.EXISTS_TAC `i` THEN Q.EXISTS_TAC `E i` THEN ASM_SET_TAC []] THEN
   RW_TAC std_ss [Int_stable] THEN SIMP_TAC std_ss [Int_range_binary] THEN
   MATCH_MP_TAC (SIMP_RULE std_ss [AND_IMP_INTRO] sigma_sets_Inter) THEN
   CONJ_TAC THENL [ALL_TAC, RW_TAC std_ss [binary]] THEN
   RW_TAC std_ss [SUBSET_DEF, IN_POW, GSPECIFICATION, EXISTS_PROD] THEN
   ASM_SET_TAC [], ALL_TAC] THEN
  FULL_SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD] THEN
  Q.ABBREV_TAC `i = p_1''` THEN Q.ABBREV_TAC `B = p_2` THEN
  Q_TAC SUFF_TAC `{f | f IN PiE ii (\i. m_space (M i)) /\ f i IN B} =
           prod_emb ii M {i} (PiE {i} (\i. B))` THENL
  [DISC_RW_KILL,
   SIMP_TAC std_ss [prod_emb, IN_SING, EXTENSION] THEN
   SIMP_TAC std_ss [IN_INTER, IN_PREIMAGE, GSPECIFICATION, EXISTS_PROD] THEN
   GEN_TAC THEN EQ_TAC THEN RW_TAC std_ss [PiE_iff] THENL
   [FULL_SIMP_TAC std_ss [IN_SING, restrict],
    SIMP_TAC std_ss [restrict_extensional],
    ALL_TAC] THEN
   FULL_SIMP_TAC std_ss [IN_SING, restrict]] THEN
  MATCH_MP_TAC sigma_sets_basic THEN
  Q_TAC SUFF_TAC `prod_emb ii M {i} (PiE {i} (\i. (\i. B) i)) IN prod_algebra ii M` THENL
  [SIMP_TAC std_ss [], ALL_TAC] THEN
  MATCH_MP_TAC prod_algebraI THEN Q.EXISTS_TAC `(\i. B)` THEN
  ASM_SIMP_TAC std_ss [FINITE_SING] THEN
  CONJ_TAC THENL [ASM_SET_TAC [], ALL_TAC] THEN
  CONJ_TAC THENL [ASM_SET_TAC [], ALL_TAC] THEN
  CONJ_TAC THENL [ASM_SET_TAC [], ALL_TAC] THEN
  SIMP_TAC std_ss [Pi_iff] THEN ASM_SET_TAC []);

val sets_PiM_I = store_thm ("sets_PiM_I",
  ``!J ii E M. FINITE J /\ J SUBSET ii /\
      (!i. i IN J ==> E i IN measurable_sets (M i)) ==>
      prod_emb ii M J (PiE J (\i. E i)) IN measurable_sets (PiM ii (\i. M i))``,
  RW_TAC std_ss [] THEN ASM_CASES_TAC ``J = {}:'a->bool`` THENL
  [Q_TAC SUFF_TAC `prod_emb ii M J (PiE J (\i. E i)) = PiE ii (\i. m_space (M i))` THENL
   [DISC_RW_KILL,
    ASM_SIMP_TAC std_ss [prod_emb, restrict, NOT_IN_EMPTY] THEN
    SIMP_TAC std_ss [PREIMAGE_def, PiE_iff, NOT_IN_EMPTY] THEN
    SIMP_TAC std_ss [extensional_empty, IN_SING] THEN SET_TAC []] THEN
   ASM_SIMP_TAC std_ss [sets_PiM, sigma_sets_top],
   ALL_TAC] THEN
  ASM_SIMP_TAC std_ss [prod_algebra, sets_PiM] THEN
  MATCH_MP_TAC sigma_sets_basic THEN SIMP_TAC std_ss [IN_IMAGE] THEN
  Q.EXISTS_TAC `(J,E)` THEN ASM_SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD] THEN
  FULL_SIMP_TAC std_ss [Pi_iff]);

val lemma = store_thm ("lemma",
  ``!sp (ii:('a -> bool) # ('a -> 'b -> bool) -> bool) G u v i j.
     (M =
      extend_measure sp {(i,j) | (i,j) IN ii} (\(i,j). G (i,j))
        (\(i,j). u (i,j))) /\
     (!(i,j). (i,j) IN ii ==> (v (G (i,j)) = u (i,j))) /\
     (!(i,j). (i,j) IN ii ==> G (i,j) IN POW sp) /\
     positive (m_space M,measurable_sets M,v) /\
     countably_additive (m_space M,measurable_sets M,v) /\
     (i,j) IN ii ==>
     measure_space M``,
  METIS_TAC [measure_space_extend_measure_Pair]);

val sigma_sets_empty_eq = store_thm ("sigma_sets_empty_eq",
  ``!A. sigma_sets A {} = {{}; A}``,
  GEN_TAC THEN REWRITE_TAC [EXTENSION] THEN GEN_TAC THEN EQ_TAC THENL
  [ALL_TAC,
   REWRITE_TAC [SET_RULE ``x IN {a;b} = (x = a) \/ (x = b)``] THEN
   METIS_TAC [sigma_sets_empty, sigma_sets_top]] THEN
  GEN_REWR_TAC LAND_CONV [SPECIFICATION] THEN
  Q_TAC SUFF_TAC `sigma_sets A {} x ==> (\x. x IN {{}; A}) x` THENL
  [SIMP_TAC std_ss [], ALL_TAC] THEN
  MATCH_MP_TAC sigma_sets_ind THEN
  REWRITE_TAC [SET_RULE ``x IN {a;b} = (x = a) \/ (x = b)``] THEN
  RW_TAC std_ss [] THENL
  [POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION]) THEN
   SIMP_TAC std_ss [NOT_IN_EMPTY],
   SET_TAC [], SET_TAC [], ALL_TAC] THEN
  ASM_CASES_TAC ``(BIGUNION {(A':num->'a->bool) i | i IN univ(:num)} = A)`` THEN
  ASM_SIMP_TAC std_ss [] THEN POP_ASSUM MP_TAC THEN
  ASM_SIMP_TAC std_ss [EXTENSION, NOT_IN_EMPTY, IN_BIGUNION, GSPECIFICATION] THEN
  RW_TAC std_ss [IN_UNIV] THEN
  ASM_CASES_TAC ``x':'a NOTIN s`` THEN ASM_SIMP_TAC std_ss [] THEN GEN_TAC THEN
  FULL_SIMP_TAC std_ss [] THEN
  POP_ASSUM (fn th => POP_ASSUM MP_TAC THEN ASSUME_TAC th) THEN
  ONCE_REWRITE_TAC [MONO_NOT_EQ] THEN RW_TAC std_ss [] THEN
  EQ_TAC THEN RW_TAC std_ss [] THENL [ASM_SET_TAC [], ALL_TAC] THEN
  ASM_SET_TAC []);

val sets_PiM_empty = store_thm ("sets_PiM_empty",
  ``!M. measurable_sets (PiM {} M) = {{};{(\x. undefined)}}``,
  RW_TAC std_ss [sets_PiM_single, NOT_IN_EMPTY, GSPEC_F] THEN
  ONCE_REWRITE_TAC [SET_RULE
  ``{{f | f IN PiE n (\i. m_space (m i)) /\ f i IN A} | F} = {}``] THEN
  SIMP_TAC std_ss [sigma_sets_empty_eq] THEN
  RW_TAC std_ss [PiE, Pi, NOT_IN_EMPTY, extensional_empty, INTER_UNIV, GSPEC_T]);

val space_PiM_empty = store_thm ("space_PiM_empty",
  ``!M. m_space (PiM {} M) = {(\x. undefined)}``,
  SIMP_TAC std_ss [SIMP_RULE std_ss [ETA_AX] space_PiM] THEN
  RW_TAC std_ss [PiE, Pi, NOT_IN_EMPTY, extensional_empty, INTER_UNIV, GSPEC_T]);

val countably_additiveI = store_thm ("countably_additiveI",
  ``!sp M f. (!A. IMAGE A UNIV SUBSET M ==> disjoint_family A ==>
        BIGUNION {A i | i IN UNIV} IN M ==>
        (suminf (\i. f (A i)) = f (BIGUNION {A i | i IN UNIV}))) ==>
        countably_additive (sp,M,f)``,
  RW_TAC std_ss [countably_additive_alt_eq, o_DEF]);

val suminf_finite = store_thm ("suminf_finite",
  ``!f N. FINITE N /\ (!n. n NOTIN N ==> (f n = 0)) /\
          (!n. 0 <= f n) ==>
          (suminf f = SIGMA f N)``,
  RW_TAC std_ss [] THEN
  `?a. !x. x IN N ==> x <= a` by METIS_TAC [num_FINITE] THEN
  Q_TAC SUFF_TAC `SIGMA f N = SIGMA f (count (SUC a))` THENL
  [DISC_RW_KILL THEN MATCH_MP_TAC ext_suminf_sum THEN
   ASM_SIMP_TAC std_ss [] THEN RW_TAC std_ss [] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN POP_ASSUM MP_TAC THEN
   ONCE_REWRITE_TAC [MONO_NOT_EQ] THEN RW_TAC std_ss [],
   ALL_TAC] THEN
  Q_TAC SUFF_TAC `SIGMA f (count (SUC a)) = SIGMA f (count (SUC a) INTER N)` THENL
  [DISC_RW_KILL,
   ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN `FINITE (count (SUC a))` by METIS_TAC [FINITE_COUNT] THEN
   FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP EXTREAL_SUM_IMAGE_INTER_ELIM) THEN
   ASM_SIMP_TAC std_ss [] THEN DISJ1_TAC THEN RW_TAC std_ss [] THEN
   METIS_TAC [lt_infty, lte_trans, extreal_of_num_def, extreal_le_def]] THEN
  ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN ONCE_REWRITE_TAC [INTER_COMM] THEN
  FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP EXTREAL_SUM_IMAGE_INTER_ELIM) THEN
  CONJ_TAC THENL
  [DISJ1_TAC THEN RW_TAC std_ss [] THEN
   METIS_TAC [lt_infty, lte_trans, extreal_of_num_def, extreal_le_def],
   ALL_TAC] THEN
  RW_TAC std_ss [] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC [MONO_NOT_EQ] THEN
  RW_TAC std_ss [count_def, GSPECIFICATION] THEN
  MATCH_MP_TAC LESS_EQ_LESS_TRANS THEN Q.EXISTS_TAC `a` THEN
  ASM_SIMP_TAC arith_ss []);

val additive_sum = store_thm ("additive_sum",
  ``!sp M f A t. ring t M /\ positive (t,M,f) /\
               additive (t,M,f) /\ FINITE sp /\
               IMAGE A sp SUBSET M /\ disjoint_family_on A sp ==>
               (SIGMA (f o A) sp = f (BIGUNION (IMAGE A sp)))``,
  RW_TAC std_ss [] THEN
  Q_TAC SUFF_TAC `FINITE sp /\ IMAGE A sp SUBSET M /\ disjoint_family_on A sp` THENL
  [ALL_TAC, ASM_SIMP_TAC std_ss []] THEN
  SIMP_TAC std_ss [GSYM AND_IMP_INTRO] THEN Q.SPEC_TAC (`sp`,`sp`) THEN SET_INDUCT_TAC THENL
  [SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_EMPTY, IMAGE_EMPTY, BIGUNION_EMPTY] THEN
   FULL_SIMP_TAC std_ss [positive_def, measure_def], ALL_TAC] THEN
  SIMP_TAC std_ss [IMAGE_INSERT, BIGUNION_INSERT] THEN DISCH_TAC THEN DISCH_TAC THEN
  Q_TAC SUFF_TAC `SIGMA (f o A) (e INSERT s) = (f o A) e + SIGMA (f o A) (s DELETE e)` THENL
  [DISC_RW_KILL,
   FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP EXTREAL_SUM_IMAGE_PROPERTY_NEG) THEN
   RW_TAC std_ss [o_DEF] THEN FULL_SIMP_TAC std_ss [lt_infty, positive_def] THEN
   FULL_SIMP_TAC std_ss [measure_def, measurable_sets_def] THEN
   MATCH_MP_TAC lte_trans THEN Q.EXISTS_TAC `0` THEN
   SIMP_TAC std_ss [GSYM lt_infty, num_not_infty] THEN
   ASM_SET_TAC []] THEN
  FULL_SIMP_TAC std_ss [additive_def, measure_def, measurable_sets_def] THEN
  Q_TAC SUFF_TAC `f (A e UNION BIGUNION (IMAGE A s)) =
                  f (A e) + f (BIGUNION (IMAGE A s))` THENL
  [DISC_RW_KILL THEN AP_TERM_TAC THEN
   `s DELETE e = s` by ASM_SET_TAC [] THEN
   FULL_SIMP_TAC std_ss [AND_IMP_INTRO] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
   ASM_SET_TAC [disjoint_family_on], ALL_TAC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  CONJ_TAC THENL [ASM_SET_TAC [], ALL_TAC] THEN
  CONJ_TAC THENL [ALL_TAC, ASM_SET_TAC [DISJOINT_DEF, disjoint_family_on]] THEN
  `IMAGE A s SUBSET M` by ASM_SET_TAC [] THEN
  POP_ASSUM MP_TAC THEN UNDISCH_TAC ``FINITE s`` THEN
  Q.SPEC_TAC (`s`,`s`) THEN SET_INDUCT_TAC THENL
  [SIMP_TAC std_ss [IMAGE_EMPTY, BIGUNION_EMPTY] THEN
   FULL_SIMP_TAC std_ss [ring, semiring], ALL_TAC] THEN
  RW_TAC std_ss [IMAGE_INSERT, BIGUNION_INSERT] THEN
  FULL_SIMP_TAC std_ss [ring, semiring] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SET_TAC []);

val countably_additiveI_finite = store_thm ("countably_additiveI_finite",
  ``!sp M u. ring sp M /\ FINITE sp /\ positive (sp, M, u) /\
         additive (sp,M,u) ==> countably_additive (sp,M,u)``,
  RW_TAC std_ss [] THEN MATCH_MP_TAC countably_additiveI THEN
  FULL_SIMP_TAC std_ss [ring, additive_def, positive_def] THEN
  RW_TAC std_ss [] THEN
  Q_TAC SUFF_TAC `!i. i IN {i | A i <> {}} ==> ?x. x IN A i` THENL
  [DISCH_TAC,
   RW_TAC std_ss [GSPECIFICATION] THEN ASM_SET_TAC []] THEN
  Q_TAC SUFF_TAC `!i. ?x. (\i x. i IN {i | A i <> {}} ==> x IN A i) i x` THENL
  [REWRITE_TAC [SKOLEM_THM] THEN RW_TAC std_ss [],
   METIS_TAC []] THEN
  Q_TAC SUFF_TAC `FINITE (BIGUNION {A i | i IN UNIV})` THENL
  [DISCH_TAC,
   FULL_SIMP_TAC std_ss [semiring, subset_class_def] THEN
   `BIGUNION (IMAGE A UNIV) SUBSET sp` by ASM_SET_TAC [] THEN
   METIS_TAC [SUBSET_FINITE]] THEN
  Q_TAC SUFF_TAC `{i | u (A i) <> 0} SUBSET {i | A i <> {}}` THENL
  [DISCH_TAC, RW_TAC std_ss [SUBSET_DEF, GSPECIFICATION] THEN
   METIS_TAC [measure_def]] THEN
  Q_TAC SUFF_TAC `FINITE {i | A i <> {}}` THENL
  [DISCH_TAC,
   Q_TAC SUFF_TAC `FINITE (IMAGE f {i | A i <> {}})` THENL
   [ALL_TAC,
    Q_TAC SUFF_TAC `IMAGE f {i | A i <> {}} SUBSET BIGUNION {A i | i IN univ(:num)}` THENL
    [DISCH_TAC, ASM_SET_TAC []] THEN
    METIS_TAC [SUBSET_FINITE]] THEN
   MATCH_MP_TAC EQ_IMPLIES THEN MATCH_MP_TAC FINITE_IMAGE_INJ_EQ THEN
   RW_TAC std_ss [GSPECIFICATION] THEN
   FULL_SIMP_TAC std_ss [disjoint_family, disjoint_family_on, IN_UNIV] THEN
   ASM_SET_TAC []] THEN
  `FINITE {i | u (A i) <> 0}` by METIS_TAC [FINITE_SUBSET] THEN
  Q_TAC SUFF_TAC `disjoint_family_on A {i | A i <> {}}` THENL
  [DISCH_TAC, FULL_SIMP_TAC std_ss [disjoint_family, disjoint_family_on, IN_UNIV]] THEN
  Q_TAC SUFF_TAC `suminf (\i. u (A i)) = SIGMA (\i. u (A i)) {i | u (A i) <> 0}` THENL
  [DISC_RW_KILL,
   MATCH_MP_TAC suminf_finite THEN ASM_SIMP_TAC std_ss [GSPECIFICATION] THEN
   GEN_TAC THEN FULL_SIMP_TAC std_ss [measure_def, measurable_sets_def] THEN
   ASM_SET_TAC []] THEN
  Q_TAC SUFF_TAC `SIGMA (\i. u (A i)) {i | u (A i) <> 0} =
                  SIGMA (\i. u (A i)) {i | A i <> {}}` THENL
  [DISC_RW_KILL,
   `{i | u (A i) <> 0} = {i | A i <> {}} INTER {i | u (A i) <> 0}` by ASM_SET_TAC [] THEN
   POP_ASSUM (fn th => ONCE_REWRITE_TAC [th]) THEN
   FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP EXTREAL_SUM_IMAGE_INTER_ELIM) THEN
   CONJ_TAC THENL
   [DISJ1_TAC THEN RW_TAC std_ss [GSPECIFICATION] THEN
    FULL_SIMP_TAC std_ss [measure_def, measurable_sets_def] THEN
    SIMP_TAC std_ss [lt_infty] THEN MATCH_MP_TAC lte_trans THEN
    Q.EXISTS_TAC `0` THEN SIMP_TAC std_ss [GSYM lt_infty, num_not_infty] THEN
    ASM_SET_TAC [], ALL_TAC] THEN
   RW_TAC std_ss [GSPECIFICATION]] THEN
  Q.ABBREV_TAC `N = {i | A i <> {}}` THEN
  Q_TAC SUFF_TAC `SIGMA (\i. u (A i)) N =
                  u (BIGUNION {A i | i IN N})` THENL
  [DISC_RW_KILL,
   SIMP_TAC std_ss [GSYM IMAGE_DEF, GSYM o_DEF] THEN
   MATCH_MP_TAC additive_sum THEN Q.EXISTS_TAC `M` THEN
   Q.EXISTS_TAC `sp` THEN ASM_SIMP_TAC std_ss [positive_def, additive_def] THEN
   CONJ_TAC THENL [ALL_TAC, ASM_SET_TAC []] THEN ASM_SIMP_TAC std_ss [ring]] THEN
  AP_TERM_TAC THEN ASM_SET_TAC []);

val measure_space_PiM_empty = store_thm ("measure_space_PiM_empty",
  ``!M. measure_space (PiM {} M)``,
  GEN_TAC THEN ONCE_REWRITE_TAC [PiM] THEN MATCH_MP_TAC lemma THEN
  SIMP_TAC std_ss [GSYM PiM, sets_PiM_empty, space_PiM_empty] THEN
  SIMP_TAC std_ss [PiM] THEN Q.EXISTS_TAC `(PiE {} (\i. m_space (M i)))` THEN
  Q_TAC SUFF_TAC `!i j (ii:('a -> bool) # ('a -> 'b -> bool) -> bool).
                       {(i,j) | (i,j) IN ii} = ii` THENL
  [DISC_RW_KILL,
   RW_TAC std_ss [EXTENSION, GSPECIFICATION, EXISTS_PROD] THEN
   METIS_TAC [pair_CASES]] THEN
  Q_TAC SUFF_TAC `!i j (G:('a -> bool) # ('a -> 'b -> bool) -> ('a->'b) -> bool).
                       (\(i,j). G (i,j)) = G` THENL
  [DISC_RW_KILL,
   RW_TAC std_ss [FUN_EQ_THM] THEN
   `?a b. x = (a,b)` by METIS_TAC [pair_CASES] THEN
   ASM_SIMP_TAC std_ss []] THEN
  Q_TAC SUFF_TAC `!i j (u:('a -> bool) # ('a -> 'b -> bool) -> extreal).
                       (\(i,j). u (i,j)) = u` THENL
  [DISC_RW_KILL,
   RW_TAC std_ss [FUN_EQ_THM] THEN
   `?a b. x = (a,b)` by METIS_TAC [pair_CASES] THEN
   ASM_SIMP_TAC std_ss []] THEN
  Q.EXISTS_TAC `{(J,X) | FINITE J /\ J SUBSET {} /\
      X IN Pi J (\i. measurable_sets (M i))}` THEN
  Q.EXISTS_TAC `(\(J,X). prod_emb {} M J (PiE J (\i. X i)))` THEN
  Q.EXISTS_TAC `(\(J,X). Normal (product
       (J UNION {i | i IN {} /\ measure (M i) (m_space (M i)) <> 1})
       (\j. if j IN J then real (measure (M j) (X j))
            else real (measure (M j) (m_space (M j))))))` THEN
  SIMP_TAC std_ss [NOT_IN_EMPTY, GSPEC_F, UNION_EMPTY] THEN
  Q.EXISTS_TAC `(\A. if A = {} then 0 else (1:extreal))` THEN
  Q.EXISTS_TAC `{}` THEN Q.EXISTS_TAC `(\x. undefined)` THEN
  RW_TAC std_ss [GSPECIFICATION, EXISTS_PROD, SUBSET_REFL, FINITE_EMPTY] THENL
  [Q_TAC SUFF_TAC `!(i,j).
    (\i j. FINITE i /\ i SUBSET {} /\ j IN Pi i (\i. measurable_sets (M i)) ==>
    ((if prod_emb {} M i (PiE i (\i. j i)) = {} then 0 else 1) =
     Normal (product i
        (\j'. if j' IN i then real (measure (M j') (j j'))
              else real (measure (M j') (m_space (M j'))))))) i j` THENL
   [SIMP_TAC std_ss [], REWRITE_TAC [GSYM PFORALL_THM]] THEN
   GEN_TAC THEN GEN_TAC THEN SIMP_TAC std_ss [SUBSET_EMPTY] THEN
   Q_TAC SUFF_TAC `prod_emb {} M {} (PiE {} (\i. y i)) <> {}` THENL
   [RW_TAC std_ss [],
    RW_TAC std_ss [prod_emb, INTER_DEF, PiE_iff, NOT_IN_EMPTY] THEN
    SIMP_TAC std_ss [extensional_empty, IN_PREIMAGE] THEN
    SIMP_TAC std_ss [EXTENSION, NOT_IN_EMPTY, IN_SING, PiE_iff] THEN
    SIMP_TAC std_ss [GSPECIFICATION, restrict_extensional, restrict]] THEN
   RW_TAC std_ss [PRODUCT_CLAUSES, GSYM extreal_of_num_def],
   Q_TAC SUFF_TAC `!(i,j).
    (\i j. FINITE i /\ i SUBSET {} /\ j IN Pi i (\i. measurable_sets (M i)) ==>
       prod_emb {} M i (PiE i (\i. j i)) IN POW (PiE {} (\i. m_space (M i)))) i j` THENL
   [SIMP_TAC std_ss [], REWRITE_TAC [GSYM PFORALL_THM]] THEN
   RW_TAC std_ss [SUBSET_EMPTY] THEN
   Q_TAC SUFF_TAC `prod_emb {} M {} (PiE {} (\i. y i)) IN prod_algebra {} M` THENL
   [METIS_TAC [prod_algebra_sets_into_space, SUBSET_DEF, IN_POW], ALL_TAC] THEN
   MATCH_MP_TAC prod_algebraI THEN SIMP_TAC std_ss [FINITE_EMPTY, Pi_iff] THEN
   SET_TAC [],
   SIMP_TAC std_ss [positive_def, measure_def] THEN
   RW_TAC real_ss [extreal_of_num_def, extreal_le_def],
   ALL_TAC,
   SIMP_TAC std_ss [Pi_iff, NOT_IN_EMPTY]] THEN
  MATCH_MP_TAC countably_additiveI_finite THEN
  SIMP_TAC std_ss [FINITE_SING] THEN RW_TAC std_ss [] THENL
  [ALL_TAC,
   SIMP_TAC std_ss [positive_def, measure_def, measurable_sets_def] THEN
   RW_TAC real_ss [le_refl, extreal_of_num_def, extreal_le_def],
   RW_TAC std_ss [additive_def, measure_def, measurable_sets_def] THEN
   TRY (ASM_SET_TAC []) THEN REPEAT (POP_ASSUM MP_TAC) THEN
   ONCE_REWRITE_TAC [SET_RULE ``s IN {a;b} = (s = a) \/ (s = b)``] THEN
   RW_TAC std_ss [] THEN TRY (ASM_SET_TAC []) THEN
   SIMP_TAC std_ss [add_rzero, add_lzero]] THEN
  `sigma_algebra ({(\x. undefined)}, {{}; {(\x. undefined)}})`
   by METIS_TAC [sigma_algebra_trivial] THEN
  FULL_SIMP_TAC std_ss [sigma_algebra_alt_eq, algebra_alt_eq]);

val measurable_PiM_single = store_thm ("measurable_PiM_single",
  ``!f N M ii. measure_space N /\ measure_space (PiM ii M) /\
     (!i. i IN ii ==> measure_space (M i)) /\
     f IN (m_space N -> PiE ii (\i. m_space (M i))) /\
     (!A i. i IN ii ==> A IN measurable_sets (M i) ==>
         {w | w IN m_space N /\ f w i IN A} IN measurable_sets N) ==>
     f IN measurable (m_space N, measurable_sets N)
         (m_space (PiM ii M), measurable_sets (PiM ii M))``,
  RW_TAC std_ss [] THEN MATCH_MP_TAC measurable_sigma_sets THEN
  Q.EXISTS_TAC `PiE ii (\i. m_space (M i))` THEN
  Q.EXISTS_TAC `{{f | f IN PiE n (\i. m_space (m i)) /\ f i IN A} |
        (m = M) /\ (n = ii) /\ i IN ii /\ A IN measurable_sets (M i)}` THEN
  ASM_SIMP_TAC std_ss [sets_PiM_single] THEN CONJ_TAC THENL
  [RW_TAC std_ss [SUBSET_DEF, GSPECIFICATION, EXISTS_PROD, IN_POW] THEN
   ASM_SET_TAC [], ALL_TAC] THEN
  RW_TAC std_ss [GSPECIFICATION, EXISTS_PROD] THEN
  Q.ABBREV_TAC `A =  {f | f IN PiE ii (\i. m_space (M i)) /\ f p_1'' IN p_2}` THEN
  Q_TAC SUFF_TAC `PREIMAGE f A INTER m_space N = {w | w IN m_space N /\ f w p_1'' IN p_2}` THENL
  [METIS_TAC [], ALL_TAC] THEN
  SIMP_TAC std_ss [PREIMAGE_def, EXTENSION, GSPECIFICATION] THEN
  ASM_SET_TAC [IN_FUNSET]);

val measurable_restrict = store_thm ("measurable_restrict",
  ``!ii X M N. (!i. i IN ii ==> measure_space (M i)) /\
       (!i. i IN ii ==>
              X i IN measurable (m_space N, measurable_sets N)
                                (m_space (M i), measurable_sets (M i))) /\
       measure_space N /\ measure_space (PiM ii M) ==>
       (\x i. if i IN ii then X i x else undefined) IN
       measurable (m_space N, measurable_sets N)
                  (m_space (PiM ii M), measurable_sets (PiM ii M))``,
  RW_TAC std_ss [] THEN MATCH_MP_TAC measurable_PiM_single THEN
  FULL_SIMP_TAC std_ss [IN_MEASURABLE, space_def, subsets_def] THEN
  FULL_SIMP_TAC std_ss [IN_FUNSET, PiE_iff] THEN
  Q_TAC SUFF_TAC `!x. (\i. if i IN ii then X i x else undefined) = restrict (\i. X i x) ii`  THENL
  [DISC_RW_KILL THEN SIMP_TAC std_ss [restrict_extensional], SIMP_TAC std_ss [restrict]] THEN
  RW_TAC std_ss [] THEN FIRST_X_ASSUM (MP_TAC o Q.SPEC `i`) THEN
  ASM_SIMP_TAC std_ss [] THEN RW_TAC std_ss [] THEN
  Q_TAC SUFF_TAC `{w | w IN m_space N /\ X i w IN A} =
      PREIMAGE (X i) A INTER m_space N` THENL
  [DISC_RW_KILL, ASM_SET_TAC [PREIMAGE_def]] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC std_ss []);

val sigma_sets_vimage_commute = store_thm ("sigma_sets_vimage_commute",
  ``!X sp sp' st'. X IN (sp -> sp') ==>
      ({PREIMAGE X A INTER sp | A IN sigma_sets sp' st'} =
       sigma_sets sp {PREIMAGE X A INTER sp | A IN st'})``,
  RW_TAC std_ss [IN_FUNSET] THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
  CONJ_TAC THENL
  [RW_TAC std_ss [SUBSET_DEF, GSPECIFICATION] THEN
   POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [SPECIFICATION]) THEN
   Q_TAC SUFF_TAC `sigma_sets sp' st' A ==>
    (\A. PREIMAGE X A INTER sp IN
    sigma_sets sp {PREIMAGE X A INTER sp | A IN st'}) A` THENL
   [SIMP_TAC std_ss [], MATCH_MP_TAC sigma_sets_ind] THEN
   RW_TAC std_ss [] THENL
   [SIMP_TAC std_ss [PREIMAGE_EMPTY, INTER_EMPTY, sigma_sets_empty],
    POP_ASSUM (ASSUME_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION]) THEN
    MATCH_MP_TAC sigma_sets_basic THEN ASM_SET_TAC [],
    Q_TAC SUFF_TAC `PREIMAGE X (sp' DIFF a) INTER sp =
                    sp DIFF (PREIMAGE X a INTER sp)` THENL
    [DISC_RW_KILL, ASM_SET_TAC [PREIMAGE_def]] THEN
    MATCH_MP_TAC sigma_sets_compl THEN ASM_SIMP_TAC std_ss [],
    ALL_TAC] THEN
   SIMP_TAC std_ss [PREIMAGE_BIGUNION, INTER_BIGUNION] THEN
   SIMP_TAC std_ss [IN_IMAGE, GSPECIFICATION] THEN
   Q_TAC SUFF_TAC `{x INTER sp |
     ?x'. (x = PREIMAGE X x') /\ ?i. (x' = A i) /\ i IN univ(:num)} =
                   {(\i. PREIMAGE X (A i) INTER sp) i | i IN univ(:num)}` THENL
   [DISC_RW_KILL, SET_TAC []] THEN
   MATCH_MP_TAC sigma_sets_union THEN ASM_SIMP_TAC std_ss [],
   ALL_TAC] THEN
  RW_TAC std_ss [SUBSET_DEF, GSPECIFICATION] THEN
  POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [SPECIFICATION]) THEN
  Q_TAC SUFF_TAC `sigma_sets sp {PREIMAGE X A INTER sp | A IN st'} x ==>
   (\x. ?A. (x = PREIMAGE X A INTER sp) /\ A IN sigma_sets sp' st') x` THENL
  [SIMP_TAC std_ss [], MATCH_MP_TAC sigma_sets_ind] THEN
  RW_TAC std_ss [] THENL
  [Q.EXISTS_TAC `{}` THEN
   SIMP_TAC std_ss [PREIMAGE_EMPTY, sigma_sets_empty, INTER_EMPTY],
   POP_ASSUM (ASSUME_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION]) THEN
   FULL_SIMP_TAC std_ss [GSPECIFICATION] THEN
   METIS_TAC [sigma_sets_basic],
   Q.EXISTS_TAC `(sp' DIFF A)` THEN
   CONJ_TAC THENL [ASM_SET_TAC [PREIMAGE_def], ALL_TAC] THEN
   METIS_TAC [sigma_sets_compl], ALL_TAC] THEN
  Q_TAC SUFF_TAC `!i. ?A'. (\i A'. (A i = PREIMAGE X A' INTER sp) /\
                               A' IN sigma_sets sp' st') i A'` THENL
  [REWRITE_TAC [SKOLEM_THM], ASM_SIMP_TAC std_ss []] THEN
  RW_TAC std_ss [] THEN Q.EXISTS_TAC `BIGUNION {f i | i IN UNIV}` THEN
  CONJ_TAC THENL
  [ALL_TAC, MATCH_MP_TAC sigma_sets_union THEN ASM_SIMP_TAC std_ss []] THEN
  SIMP_TAC std_ss [PREIMAGE_BIGUNION, INTER_BIGUNION] THEN
  SIMP_TAC std_ss [IN_IMAGE, GSPECIFICATION] THEN
  Q_TAC SUFF_TAC `{x INTER sp |
     ?x'. (x = PREIMAGE X x') /\ ?i. (x' = f i) /\ i IN univ(:num)} =
                   {(\i. PREIMAGE X (f i) INTER sp) i | i IN univ(:num)}` THENL
  [DISC_RW_KILL, SET_TAC []] THEN
  SIMP_TAC std_ss []);

val sigma_sets_sigma_sets_eq = store_thm ("sigma_sets_sigma_sets_eq",
  ``!sp st. st SUBSET POW sp ==> (sigma_sets sp (sigma_sets sp st) = sigma_sets sp st)``,
  RW_TAC std_ss [] THEN MATCH_MP_TAC sigma_sets_eq THEN
  MATCH_MP_TAC sigma_algebra_sigma_sets THEN ASM_SIMP_TAC std_ss []);

val sigma_sets_mono = store_thm ("sigma_sets_mono",
  ``!X A B. A SUBSET sigma_sets X B ==> sigma_sets X A SUBSET sigma_sets X B``,
  RW_TAC std_ss [SUBSET_DEF] THEN POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [SPECIFICATION]) THEN
  Q_TAC SUFF_TAC `sigma_sets X A x ==> (\x. x IN sigma_sets X B) x` THENL
  [SIMP_TAC std_ss [], MATCH_MP_TAC sigma_sets_ind] THEN
  RW_TAC std_ss [sigma_sets_empty] THENL
  [POP_ASSUM (ASSUME_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION]) THEN
   METIS_TAC [],
   MATCH_MP_TAC sigma_sets_compl THEN ASM_SIMP_TAC std_ss [],
   ALL_TAC] THEN
  MATCH_MP_TAC sigma_sets_union THEN ASM_SIMP_TAC std_ss []);

val PRODUCT_BIGUNION = store_thm ("PRODUCT_BIGUNION",
  ``!f ii A.  FINITE ii /\ (!i. i IN ii ==> FINITE (A i)) /\
    (!i j. i IN ii /\ j IN ii /\ i <> j ==> (A i INTER A j = {})) ==>
    (product (BIGUNION {A i | i IN ii}) f =
     product ii (\i. product (A i) f))``,
  REPEAT GEN_TAC THEN SIMP_TAC std_ss [GSYM AND_IMP_INTRO] THEN
  Q.SPEC_TAC (`ii`,`ii`) THEN SET_INDUCT_TAC THENL
  [SIMP_TAC std_ss [NOT_IN_EMPTY, PRODUCT_CLAUSES] THEN
   ONCE_REWRITE_TAC [SET_RULE ``{A i | i | F} = {}``] THEN
   SIMP_TAC std_ss [BIGUNION_EMPTY, PRODUCT_CLAUSES],
   ALL_TAC] THEN
  RW_TAC std_ss [] THEN
  Q_TAC SUFF_TAC `BIGUNION {A i | i IN e INSERT s} =
                  BIGUNION {A i | i IN s} UNION (A e)` THENL
  [DISC_RW_KILL, ASM_SET_TAC []] THEN
  ASM_SIMP_TAC std_ss [PRODUCT_CLAUSES] THEN
  Q_TAC SUFF_TAC `product (BIGUNION {A i | i IN s} UNION A e) f =
                  product (A e) f * product (BIGUNION {A i | i IN s}) f` THENL
  [DISC_RW_KILL,
   ONCE_REWRITE_TAC [UNION_COMM] THEN MATCH_MP_TAC PRODUCT_UNION THEN
   CONJ_TAC THENL [ASM_SET_TAC [], ALL_TAC] THEN
   CONJ_TAC THENL [MATCH_MP_TAC FINITE_BIGUNION THEN SIMP_TAC std_ss [GSYM IMAGE_DEF] THEN
    CONJ_TAC THENL [ALL_TAC, ASM_SET_TAC []] THEN MATCH_MP_TAC IMAGE_FINITE THEN
    ASM_SIMP_TAC std_ss [] , ALL_TAC] THEN
   ASM_SET_TAC []] THEN AP_TERM_TAC THEN ASM_SET_TAC []);

val indep_sets_collect_sigma = store_thm ("indep_sets_collect_sigma",
  ``!E ii J p. prob_space p /\ indep_sets p E (BIGUNION {ii j | j IN J}) /\
              (!i j. j IN J ==> i IN ii j ==> Int_stable (E i)) /\
              disjoint_family_on ii J ==>
          indep_sets p (\j. sigma_sets (m_space p) (BIGUNION {E i | i IN ii j})) J``,
  RW_TAC std_ss [] THEN
  Q.ABBREV_TAC `ee = (\j. {BIGINTER {E' k | k IN kk} |
    FINITE kk /\ kk <> {} /\ kk SUBSET ii j /\ (!k. k IN kk ==> E' k IN E k)})` THEN
  Q_TAC SUFF_TAC `!j i. j IN J ==> i IN ii j ==> E i SUBSET events p` THENL
  [DISCH_TAC,
   RW_TAC std_ss [] THEN FULL_SIMP_TAC std_ss [indep_sets] THEN ASM_SET_TAC []] THEN
  Q.ABBREV_TAC `ss = (\j. sigma_sets (m_space p) (BIGUNION {E i | i IN ii j}))` THEN
  Q_TAC SUFF_TAC `!j. j IN J ==> sigma_algebra (m_space p, ss j)` THENL
  [DISCH_TAC,
   Q.UNABBREV_TAC `ss` THEN RW_TAC std_ss [] THEN
   MATCH_MP_TAC sigma_algebra_sigma_sets THEN
   SIMP_TAC std_ss [SUBSET_DEF, IN_POW, IN_BIGUNION, GSPECIFICATION] THEN
   RW_TAC std_ss [] THEN FULL_SIMP_TAC std_ss [events_def] THEN
   `E i SUBSET measurable_sets p` by ASM_SET_TAC [] THEN
   `x IN measurable_sets p` by ASM_SET_TAC [] THEN
   FULL_SIMP_TAC std_ss [prob_space_def] THEN
   `x SUBSET m_space p` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
   ASM_SET_TAC []] THEN
  Q_TAC SUFF_TAC `!j. j IN J ==> (sigma_sets (m_space p) (ss j) =
                                  sigma_sets (m_space p) (ee j))` THENL
  [DISCH_TAC,
   Q.UNABBREV_TAC `ss` THEN RW_TAC std_ss [] THEN
   FULL_SIMP_TAC std_ss [sigma_sets_eq] THEN MATCH_MP_TAC sigma_sets_eqI THEN
   CONJ_TAC THENL
   [RW_TAC std_ss [IN_BIGUNION, GSPECIFICATION] THEN
    MATCH_MP_TAC sigma_sets_basic THEN Q.UNABBREV_TAC `ee` THEN
    SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD, IN_BIGINTER] THEN
    Q.EXISTS_TAC `(\i. a)` THEN Q.EXISTS_TAC `{i}` THEN
    ASM_SIMP_TAC std_ss [IN_SING, FINITE_SING, SUBSET_DEF] THEN
    SET_TAC [],
    ALL_TAC] THEN
   Q.UNABBREV_TAC `ee` THEN RW_TAC std_ss [IN_BIGINTER, GSPECIFICATION, EXISTS_PROD] THEN
   MATCH_MP_TAC finite_INT THEN ASM_SIMP_TAC std_ss [] THEN CONJ_TAC THENL
   [Q.ABBREV_TAC `ss = sigma_sets (m_space p) (BIGUNION {E i | i IN ii j})` THEN
    `sigma_algebra (m_space p, ss)` by METIS_TAC [] THEN
    FULL_SIMP_TAC std_ss [sigma_algebra_def, Int_stable] THEN
    METIS_TAC [ALGEBRA_INTER, space_def, subsets_def],
    ALL_TAC] THEN
   RW_TAC std_ss [] THEN MATCH_MP_TAC sigma_sets_basic THEN
   ASM_SIMP_TAC std_ss [GSPECIFICATION, IN_BIGUNION] THEN
   ASM_SET_TAC []] THEN
  Q_TAC SUFF_TAC `indep_sets p (\j. sigma_sets (m_space p) (ee j)) J` THENL
  [ALL_TAC,
   MATCH_MP_TAC (REWRITE_RULE [p_space_def] indep_sets_sigma') THEN
   ASM_SIMP_TAC std_ss [] THEN CONJ_TAC THENL
   [MATCH_MP_TAC indep_setsI THEN ASM_SIMP_TAC std_ss [] THEN
    CONJ_TAC THENL
    [Q.UNABBREV_TAC `ee` THEN
     RW_TAC std_ss [SUBSET_DEF, GSPECIFICATION, EXISTS_PROD] THEN
     MATCH_MP_TAC finite_INT THEN ASM_SIMP_TAC std_ss [] THEN
     CONJ_TAC THENL [ALL_TAC, ASM_SET_TAC []] THEN
     FULL_SIMP_TAC std_ss [prob_space_def, measure_space_def, sigma_algebra_def] THEN
     FULL_SIMP_TAC std_ss [events_def, p_space_def, Int_stable] THEN
     ONCE_REWRITE_TAC [METIS [subsets_def]
      ``measurable_sets p = subsets (m_space p, measurable_sets p)``] THEN
     METIS_TAC [ALGEBRA_INTER],
     ALL_TAC] THEN
    RW_TAC std_ss [] THEN
    Q_TAC SUFF_TAC `!j. j IN J' ==> ?E' L. (A j = BIGINTER {E' l | l IN L}) /\
     FINITE L /\ L <> {} /\ L SUBSET ii j /\ (!l. l IN L ==> E' l IN E l)` THENL
    [DISCH_TAC,
     POP_ASSUM MP_TAC THEN Q.UNABBREV_TAC `ee` THEN
     RW_TAC std_ss [GSPECIFICATION, EXISTS_PROD]] THEN
    Q_TAC SUFF_TAC `!j. ?E'. (\j E'. j IN J' ==> ?L. (A j = BIGINTER {E' l | l IN L}) /\
      FINITE L /\ L <> {} /\ L SUBSET ii j /\ (!l. l IN L ==> E' l IN E l)) j E'` THENL
    [ALL_TAC, METIS_TAC []] THEN
    REWRITE_TAC [SKOLEM_THM] THEN RW_TAC std_ss [] THEN
    Q_TAC SUFF_TAC `!x. ?L. (\x L. x IN J' ==>
             (A x = BIGINTER {f x l | l IN L}) /\ FINITE L /\ L <> {} /\
           L SUBSET ii x /\ !l. l IN L ==> f x l IN E l) x L` THENL
    [ALL_TAC, METIS_TAC []] THEN
    REWRITE_TAC [SKOLEM_THM] THEN RW_TAC std_ss [] THEN
    Q.ABBREV_TAC `E' = f` THEN Q.ABBREV_TAC `L = f'` THEN
    Q.ABBREV_TAC `kk = (\l. @k. k IN J' /\ l IN L k)` THEN
    Q.ABBREV_TAC `ee' = (\l. E' (kk l) l)` THEN
    Q_TAC SUFF_TAC `!j l. j IN J' /\ l IN L j ==> (kk l = j)` THENL
    [DISCH_TAC,
     Q.UNABBREV_TAC `kk` THEN RW_TAC std_ss [] THEN
     SELECT_ELIM_TAC THEN CONJ_TAC THENL [METIS_TAC [], ALL_TAC] THEN
     RW_TAC std_ss [] THEN FULL_SIMP_TAC std_ss [disjoint_family_on] THEN
     ASM_SET_TAC []] THEN
    Q_TAC SUFF_TAC `prob p (BIGINTER {A j | j IN J'}) =
                    prob p (BIGINTER {ee' l | l IN (BIGUNION {L k | k IN J'})})` THENL
    [DISC_RW_KILL, AP_TERM_TAC THEN ASM_SET_TAC []] THEN
    Q_TAC SUFF_TAC `prob p (BIGINTER {ee' l | l IN BIGUNION {L k | k IN J'}}) =
                    Normal (product (BIGUNION {L k | k IN J'}) (\j. real (prob p (ee' j))))` THENL
    [DISC_RW_KILL,
     MATCH_MP_TAC indep_setsD THEN Q.EXISTS_TAC `E` THEN Q.EXISTS_TAC `BIGUNION {ii j | j IN J}` THEN
     ASM_SIMP_TAC std_ss [] THEN CONJ_TAC THENL [ASM_SET_TAC [], ALL_TAC] THEN
     CONJ_TAC THENL [ASM_SET_TAC [], ALL_TAC] THEN
     CONJ_TAC THENL [ALL_TAC, ASM_SET_TAC []] THEN
     MATCH_MP_TAC FINITE_BIGUNION THEN CONJ_TAC THENL
     [SIMP_TAC std_ss [GSYM IMAGE_DEF], ASM_SET_TAC []] THEN
     MATCH_MP_TAC IMAGE_FINITE THEN ASM_SIMP_TAC std_ss []] THEN
    Q_TAC SUFF_TAC `Normal (product (BIGUNION {L k | k IN J'}) (\j. real (prob p (ee' j)))) =
          Normal (product (J') (\j. product (L j) (\l. real (prob p (E' j l)))))` THENL
    [DISC_RW_KILL,
     SIMP_TAC std_ss [extreal_11] THEN
     Q_TAC SUFF_TAC `product (BIGUNION {L k | k IN J'}) (\j. real (prob p (ee' j))) =
                     product J' (\j. product (L j) (\j. real (prob p (ee' j))))` THENL
     [DISC_RW_KILL,
      MATCH_MP_TAC PRODUCT_BIGUNION THEN ASM_SIMP_TAC std_ss [] THEN
      ASM_SET_TAC []] THEN
     Q.UNABBREV_TAC `ee'` THEN SIMP_TAC std_ss [] THEN
     MATCH_MP_TAC PRODUCT_EQ THEN RW_TAC std_ss [] THEN
     MATCH_MP_TAC PRODUCT_EQ THEN RW_TAC std_ss [] THEN
     AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_SET_TAC []] THEN
    SIMP_TAC std_ss [extreal_11] THEN MATCH_MP_TAC PRODUCT_EQ THEN
    RW_TAC std_ss [] THEN ONCE_REWRITE_TAC [GSYM extreal_11] THEN
    ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
    Q_TAC SUFF_TAC `(BIGINTER {E' x l | l | l IN L x}) IN measurable_sets p` THENL
    [DISCH_TAC,
     SIMP_TAC std_ss [GSYM events_def] THEN MATCH_MP_TAC EVENTS_COUNTABLE_INTER THEN
     ASM_SIMP_TAC std_ss [] THEN CONJ_TAC THENL [ASM_SET_TAC [], ALL_TAC] THEN
     CONJ_TAC THENL [ALL_TAC, ASM_SET_TAC []] THEN
     SIMP_TAC std_ss [GSYM IMAGE_DEF] THEN SIMP_TAC std_ss [COUNTABLE_IMAGE_NUM]] THEN
    Q_TAC SUFF_TAC `prob p (BIGINTER {E' x l | l | l IN L x}) <> NegInf` THENL
    [DISCH_TAC,
     SIMP_TAC std_ss [lt_infty] THEN MATCH_MP_TAC lte_trans THEN
     Q.EXISTS_TAC `0` THEN
     FULL_SIMP_TAC std_ss [GSYM lt_infty, num_not_infty, prob_space_def] THEN
     FULL_SIMP_TAC std_ss [prob_def, measure_space_def, positive_def]] THEN
    Q_TAC SUFF_TAC `prob p (BIGINTER {E' x l | l | l IN L x}) <> PosInf` THENL
    [DISCH_TAC,
     SIMP_TAC std_ss [lt_infty] THEN MATCH_MP_TAC let_trans THEN
     Q.EXISTS_TAC `1` THEN SIMP_TAC std_ss [GSYM lt_infty, num_not_infty] THEN
     MATCH_MP_TAC PROB_LE_1 THEN ASM_SIMP_TAC std_ss [events_def]] THEN
    ASM_SIMP_TAC std_ss [normal_real] THEN MATCH_MP_TAC indep_setsD THEN
    Q.EXISTS_TAC `E` THEN Q.EXISTS_TAC `BIGUNION {ii j | j IN J}` THEN
    ASM_SIMP_TAC std_ss [] THEN ASM_SET_TAC [],
    ALL_TAC] THEN
   RW_TAC std_ss [Int_stable] THEN Q.UNABBREV_TAC `ee` THEN
   FULL_SIMP_TAC std_ss [GSPECIFICATION, IN_BIGINTER, EXISTS_PROD] THEN
   Q.ABBREV_TAC `aa = (\k. if k IN p_2 INTER p_2' then p_1 k INTER p_1' k else
                           if k IN p_2' then p_1' k else
                           if k IN p_2 then p_1 k else {})` THEN
   Q.EXISTS_TAC `aa` THEN Q.EXISTS_TAC `p_2 UNION p_2'` THEN
   ASM_SIMP_TAC std_ss [FINITE_UNION] THEN CONJ_TAC THENL
   [SIMP_TAC std_ss [EXTENSION, IN_BIGINTER, GSPECIFICATION, IN_INTER, EXISTS_PROD] THEN
    GEN_TAC THEN EQ_TAC THEN RW_TAC std_ss [IN_UNION] THENL
    [Q.UNABBREV_TAC `aa` THEN ASM_SIMP_TAC std_ss [] THEN
     ASM_CASES_TAC ``(k:num) IN p_2'`` THENL
     [RW_TAC std_ss [IN_INTER] THENL
      [POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
       POP_ASSUM MP_TAC THEN POP_ASSUM K_TAC THEN
       RW_TAC std_ss [] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
       ASM_SET_TAC [],
       ALL_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN METIS_TAC [],
      ALL_TAC] THEN
     RW_TAC std_ss [IN_INTER] THEN
     POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
     POP_ASSUM MP_TAC THEN POP_ASSUM K_TAC THEN
     RW_TAC std_ss [] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
     ASM_SET_TAC [],
     Q.UNABBREV_TAC `aa` THEN ASM_SIMP_TAC std_ss [] THEN
     ASM_CASES_TAC ``(k:num) IN p_2`` THENL
     [RW_TAC std_ss [IN_INTER] THENL
      [POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
       POP_ASSUM MP_TAC THEN POP_ASSUM K_TAC THEN
       RW_TAC std_ss [] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
       ASM_SET_TAC [],
       ALL_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN METIS_TAC [],
      ALL_TAC] THEN
     RW_TAC std_ss [IN_INTER] THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN METIS_TAC [],
     ASM_SIMP_TAC std_ss [] THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
     FIRST_X_ASSUM (fn th => DISCH_TAC THEN DISCH_TAC THEN ASSUME_TAC th) THEN
     FIRST_X_ASSUM (MP_TAC o Q.SPEC `aa (k:num)`) THEN
     Q_TAC SUFF_TAC `?k'. (!x. x IN aa k <=> x IN aa k') /\ (k' IN p_2 \/ k' IN p_2')` THENL
     [DISCH_TAC THEN ASM_SIMP_TAC std_ss [], METIS_TAC []] THEN
     POP_ASSUM K_TAC THEN Q.UNABBREV_TAC `aa` THEN RW_TAC std_ss [] THEN
     ASM_SET_TAC [],
     ALL_TAC] THEN
    POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
    FIRST_X_ASSUM (fn th => DISCH_TAC THEN DISCH_TAC THEN ASSUME_TAC th) THEN
    FIRST_X_ASSUM (MP_TAC o Q.SPEC `aa (k:num)`) THEN
    Q_TAC SUFF_TAC `?k'. (!x. x IN aa k <=> x IN aa k') /\ (k' IN p_2 \/ k' IN p_2')` THENL
    [DISCH_TAC THEN ASM_SIMP_TAC std_ss [], METIS_TAC []] THEN
    POP_ASSUM K_TAC THEN Q.UNABBREV_TAC `aa` THEN RW_TAC std_ss [] THEN
    ASM_SET_TAC [],
    ALL_TAC] THEN
   CONJ_TAC THENL [ASM_SET_TAC [], ALL_TAC] THEN
   CONJ_TAC THENL [ASM_SET_TAC [], ALL_TAC] THEN
   Q.UNABBREV_TAC `aa` THEN RW_TAC std_ss [IN_UNION] THEN
   FULL_SIMP_TAC std_ss [Int_stable] THEN ASM_SET_TAC []] THEN
  MATCH_MP_TAC EQ_IMPLIES THEN MATCH_MP_TAC indep_sets_cong THEN
  ASM_SIMP_TAC std_ss [] THEN METIS_TAC [sigma_sets_eq]);

val indep_vars_def' = store_thm ("indep_vars_def'",
  ``!p M' X ii. prob_space p /\ (!i. i IN ii ==> measure_space (M' i)) ==>
       (indep_vars p M' X ii =
        (!i. i IN ii ==>
         random_variable (X i) p
          (m_space (M' i),measurable_sets (M' i))) /\
        indep_sets p (\i. sigma_sets (m_space p)
        {PREIMAGE f A INTER m_space p | (f = X i) /\ A IN measurable_sets (M' i)}) ii)``,
  RW_TAC std_ss [indep_vars, p_space_def] THEN AP_TERM_TAC THEN
  Q_TAC SUFF_TAC `indep_sets p
   (\i. {PREIMAGE f A INTER m_space p |
        (f = X i) /\ A IN measurable_sets (M' i)}) ii <=>
                  indep_sets p
   (\i. sigma_sets (m_space p)
       ((\i. {PREIMAGE f A INTER m_space p |
        (f = X i) /\ A IN measurable_sets (M' i)}) i)) ii` THENL
  [SIMP_TAC std_ss [], ALL_TAC] THEN
  Q.ABBREV_TAC `ff = (\i.
     {PREIMAGE f A INTER m_space p |
      (f = X i) /\ A IN measurable_sets (M' i)})` THEN
  MATCH_MP_TAC (GSYM (REWRITE_RULE [p_space_def] indep_sets_sigma_sets_iff')) THEN
  ASM_SIMP_TAC std_ss [Int_stable] THEN Q.UNABBREV_TAC `ff` THEN
  RW_TAC std_ss [] THEN FULL_SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD] THEN
  Q.EXISTS_TAC `p_2 INTER p_2'` THEN SIMP_TAC std_ss [PREIMAGE_INTER] THEN
  CONJ_TAC THENL [ASM_SET_TAC [PREIMAGE_def], ALL_TAC] THEN
  MATCH_MP_TAC MEASURE_SPACE_INTER THEN ASM_SET_TAC []);

val indep_vars_restrict = store_thm ("indep_vars_restrict",
  ``!p M' X ii kk L. prob_space p /\ indep_vars p M' X ii /\ (!j. j IN L ==> kk j SUBSET ii) /\
        (!j. j IN L ==> measure_space (PiM (kk j) M')) /\
        (!i. i IN ii ==> measure_space (M' i)) /\ disjoint_family_on kk L ==>
        indep_vars p (\j:num. PiM (kk j) M') (\j w. restrict (\i. X i w) (kk j)) L``,
  RW_TAC std_ss [indep_vars_def'] THENL
  [ASM_SIMP_TAC std_ss [random_variable_def, restrict, p_space_def, events_def] THEN
   MATCH_MP_TAC measurable_restrict THEN FULL_SIMP_TAC std_ss [prob_space_def] THEN
   CONJ_TAC THENL [ASM_SET_TAC [], ALL_TAC] THEN
   FULL_SIMP_TAC std_ss [indep_vars, random_variable_def, p_space_def, events_def] THEN
   ASM_SET_TAC [], ALL_TAC] THEN
  FULL_SIMP_TAC std_ss [indep_vars] THEN
  Q_TAC SUFF_TAC `!i. i IN ii ==> X i IN measurable (m_space p, measurable_sets p)
                                (m_space (M' i), measurable_sets (M' i))` THENL
  [DISCH_TAC, FULL_SIMP_TAC std_ss [random_variable_def, p_space_def, events_def]] THEN
  Q.ABBREV_TAC `proj = (\j s. {PREIMAGE (\w i. if i IN kk j then X i w else undefined) A INTER
                       m_space p | A IN s})` THEN
  Q.ABBREV_TAC `UN = (\j. sigma_sets (m_space p)
    (BIGUNION {{PREIMAGE (f) A INTER m_space p | (f = X i) /\ A IN measurable_sets (M' i)}|
                 (i:num) IN (kk j)}))` THEN
  Q_TAC SUFF_TAC `indep_sets p (\i. sigma_sets (m_space p)
                   (proj i (measurable_sets (PiM (kk i) M')))) L` THENL
  [DISCH_TAC,
   MATCH_MP_TAC indep_sets_mono_sets THEN Q.EXISTS_TAC `UN` THEN CONJ_TAC THENL
   [ALL_TAC,
    X_GEN_TAC ``j:num`` THEN RW_TAC std_ss [] THEN
    Q_TAC SUFF_TAC `sigma_sets (m_space p) (proj j (measurable_sets (PiM (kk j) M'))) =
       sigma_sets (m_space p) (sigma_sets (m_space p) (proj j (prod_algebra (kk j) M')))` THENL
    [DISC_RW_KILL,
     SIMP_TAC std_ss [SIMP_RULE std_ss [ETA_AX] sets_PiM] THEN
     Q.UNABBREV_TAC `proj` THEN SIMP_TAC std_ss [] THEN
     Q.ABBREV_TAC `Y = (\w i. if i IN kk j then X i w else undefined)` THEN
     Q_TAC SUFF_TAC `{PREIMAGE Y A INTER m_space p |
      A IN sigma_sets (PiE (kk j) (\i. m_space (M' i))) (prod_algebra (kk j) M')} =
      sigma_sets (m_space p) {PREIMAGE Y A INTER m_space p | A IN (prod_algebra (kk j) M')}` THENL
     [DISC_RW_KILL THEN SIMP_TAC std_ss [], ALL_TAC] THEN
     MATCH_MP_TAC sigma_sets_vimage_commute THEN Q.UNABBREV_TAC `Y` THEN
     ASM_SIMP_TAC std_ss [IN_FUNSET, PiE_iff] THEN RW_TAC std_ss [] THENL
     [FULL_SIMP_TAC std_ss [IN_MEASURABLE, space_def, subsets_def, IN_FUNSET] THEN
      ASM_SET_TAC [], ALL_TAC] THEN
     Q_TAC SUFF_TAC `(\i. if i IN kk j then X i w else undefined) =
                     restrict (\i. X i w) (kk j)` THENL
     [DISC_RW_KILL THEN SIMP_TAC std_ss [restrict_extensional], ALL_TAC] THEN
     SIMP_TAC std_ss [restrict]] THEN
    Q_TAC SUFF_TAC `sigma_sets (m_space p)
     (sigma_sets (m_space p) (proj j (prod_algebra (kk j) M'))) =
     (sigma_sets (m_space p) (proj j (prod_algebra (kk j) M')))` THENL
    [DISC_RW_KILL,
     MATCH_MP_TAC sigma_sets_sigma_sets_eq THEN
     Q.UNABBREV_TAC `proj` THEN SIMP_TAC std_ss [] THEN
     Q.ABBREV_TAC `Y = (\w i. if i IN kk j then X i w else undefined)` THEN
     RW_TAC std_ss [SUBSET_DEF, IN_POW, GSPECIFICATION] THEN
     FULL_SIMP_TAC std_ss [IN_INTER]] THEN
    Q.UNABBREV_TAC `UN` THEN SIMP_TAC std_ss [] THEN
    MATCH_MP_TAC sigma_sets_mono THEN Q.UNABBREV_TAC `proj` THEN
    RW_TAC std_ss [SUBSET_DEF, GSPECIFICATION] THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP prod_algebraE) THEN
    FULL_SIMP_TAC std_ss [] THENL
    [ALL_TAC,
     SIMP_TAC std_ss [NOT_IN_EMPTY] THEN
     Q_TAC SUFF_TAC `{{PREIMAGE f A INTER m_space p |
       (f = X i) /\ A IN measurable_sets (M' i)} | i | F} = {}` THENL
     [DISC_RW_KILL, SET_TAC []] THEN SIMP_TAC std_ss [BIGUNION_EMPTY] THEN
     SIMP_TAC std_ss [sigma_sets_empty_eq] THEN
     SIMP_TAC std_ss [prod_emb, INTER_DEF,  NOT_IN_EMPTY, PiE_iff] THEN
     SIMP_TAC std_ss [extensional_empty, PREIMAGE_def, IN_SING, GSPECIFICATION] THEN
     SIMP_TAC std_ss [restrict, PiE_iff, extensional, GSPECIFICATION] THEN
     ONCE_REWRITE_TAC [SET_RULE ``x IN {A;B} = (x = A) \/ (x = B)``] THEN
     SET_TAC []] THEN
    `kk j <> {}` by ASM_SET_TAC [] THEN
    Q.ABBREV_TAC `UN = (\j. sigma_sets (m_space p)
    (BIGUNION {{PREIMAGE (f) A INTER m_space p | (f = X i) /\ A IN measurable_sets (M' i)}|
                 (i:num) IN (kk j)}))` THEN
    Q_TAC SUFF_TAC `sigma_algebra (m_space p, UN j)` THENL
    [DISCH_TAC,
     Q.UNABBREV_TAC `UN` THEN SIMP_TAC std_ss [] THEN
     MATCH_MP_TAC sigma_algebra_sigma_sets THEN
     RW_TAC std_ss [SUBSET_DEF, IN_POW, IN_BIGUNION, GSPECIFICATION] THEN
     FULL_SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD] THEN
     POP_ASSUM MP_TAC THEN ASM_SIMP_TAC std_ss [IN_INTER, IN_PREIMAGE]] THEN
    Q_TAC SUFF_TAC `PREIMAGE (\w i. if i IN kk j then X i w else undefined)
     (prod_emb (kk j) M' J (PiE J (\j. E j))) INTER m_space p =
     BIGINTER {PREIMAGE (X i) (E i) INTER m_space p | i IN J}` THENL
    [DISC_RW_KILL,
     Q_TAC SUFF_TAC `prod_emb (kk j) M' J (PiE J (\j. E j)) =
       PiE (kk j) (\i. if i IN J then E i else m_space (M' i))` THENL
     [DISC_RW_KILL,
      FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP prod_emb_PiE) THEN
      RW_TAC std_ss [] THEN MATCH_MP_TAC MEASURE_SPACE_SUBSET_MSPACE THEN
      ASM_SET_TAC []] THEN
     SIMP_TAC std_ss [PREIMAGE_def, PiE_iff] THEN
     Q_TAC SUFF_TAC `!w. (\i. if i IN kk j then X i w else undefined) =
                     restrict (\i. X i w) (kk j)` THENL
     [DISC_RW_KILL, SIMP_TAC std_ss [restrict]] THEN
     SIMP_TAC std_ss [restrict_extensional] THEN
     SIMP_TAC std_ss [EXTENSION, IN_BIGINTER, GSPECIFICATION] THEN
     GEN_TAC THEN EQ_TAC THEN RW_TAC std_ss [] THENL
     [FULL_SIMP_TAC std_ss [GSPECIFICATION, IN_INTER] THEN
      ASM_SET_TAC [], ALL_TAC] THEN
     FULL_SIMP_TAC std_ss [GSPECIFICATION, IN_INTER] THEN
     Q_TAC SUFF_TAC `(!i. i IN kk j ==> X i x IN if i IN J then E i else m_space (M' i))` THENL
     [DISCH_TAC THEN ASM_SIMP_TAC std_ss [],
      RW_TAC std_ss [] THENL
      [FIRST_X_ASSUM (MP_TAC o Q.SPEC `(\x. X (i:num) x IN E i /\ x IN m_space p)`) THEN
       SIMP_TAC std_ss [IN_DEF] THEN
       Q_TAC SUFF_TAC `(?i'. (!x. E i (X i x) /\ m_space p x <=>
          E i' (X i' x) /\ m_space p x) /\ J i')` THENL
       [METIS_TAC [], ALL_TAC] THEN
       METIS_TAC [SPECIFICATION],
       ALL_TAC] THEN
      FULL_SIMP_TAC std_ss [IN_MEASURABLE, space_def, subsets_def, IN_FUNSET] THEN
      `kk j SUBSET ii` by (FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC std_ss []) THEN
      `i IN ii` by (POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN SET_TAC []) THEN
      `(!x'. x' IN m_space p ==> X i x' IN m_space (M' i))` by METIS_TAC [] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      FULL_SIMP_TAC std_ss [GSYM MEMBER_NOT_EMPTY] THEN
      FIRST_X_ASSUM (MP_TAC o Q.SPEC `(\x. X (x':num) x IN E x' /\ x IN m_space p)`) THEN
      SIMP_TAC std_ss [IN_DEF] THEN
      Q_TAC SUFF_TAC `(?i. (!x. E x' (X x' x) /\ m_space p x <=>
        E i (X i x) /\ m_space p x) /\ J i)` THENL
      [DISC_RW_KILL THEN SIMP_TAC std_ss [], ALL_TAC] THEN
      METIS_TAC [SPECIFICATION]] THEN
     FULL_SIMP_TAC std_ss [GSYM MEMBER_NOT_EMPTY] THEN
     FIRST_X_ASSUM (MP_TAC o Q.SPEC `(\x. X (x':num) x IN E x' /\ x IN m_space p)`) THEN
     SIMP_TAC std_ss [IN_DEF] THEN
     Q_TAC SUFF_TAC `(?i. (!x. E x' (X x' x) /\ m_space p x <=>
       E i (X i x) /\ m_space p x) /\ J i)` THENL
     [DISC_RW_KILL THEN SIMP_TAC std_ss [], ALL_TAC] THEN
     METIS_TAC [SPECIFICATION]] THEN
    ONCE_REWRITE_TAC [METIS []
     ``BIGINTER {PREIMAGE (X i) (E i) INTER m_space p | i IN J} =
       BIGINTER {(\i. PREIMAGE (X i) (E i) INTER m_space p) i | i IN J}``] THEN
    MATCH_MP_TAC sigma_sets_INTER THEN CONJ_TAC THENL
    [RW_TAC std_ss [SUBSET_DEF, IN_POW, IN_BIGUNION, GSPECIFICATION] THEN
     FULL_SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD] THEN
     POP_ASSUM MP_TAC THEN ASM_SIMP_TAC std_ss [IN_INTER, IN_PREIMAGE],
     ALL_TAC] THEN
    Q.UNABBREV_TAC `UN` THEN RW_TAC std_ss [] THEN
    MATCH_MP_TAC sigma_sets_basic THEN
    SIMP_TAC std_ss [IN_BIGUNION, GSPECIFICATION] THEN
    Q.EXISTS_TAC `{PREIMAGE f A INTER m_space p |
         (f = X i) /\ A IN measurable_sets (M' i)}` THEN
    CONJ_TAC THENL [ASM_SET_TAC [], ALL_TAC] THEN
    Q.EXISTS_TAC `i` THEN FULL_SIMP_TAC std_ss [SUBSET_DEF]] THEN
   Q.UNABBREV_TAC `UN` THEN
   Q_TAC SUFF_TAC `indep_sets p
    (\j. sigma_sets (m_space p)
       (BIGUNION
          {(\i. {PREIMAGE f A INTER m_space p |
            (f = X i) /\ A IN measurable_sets (M' i)}) i |
           i IN kk j})) L` THENL
   [SIMP_TAC std_ss [], MATCH_MP_TAC indep_sets_collect_sigma] THEN
   ASM_SIMP_TAC std_ss [] THEN CONJ_TAC THENL
   [MATCH_MP_TAC indep_sets_mono_index THEN Q.EXISTS_TAC `ii` THEN
    FULL_SIMP_TAC std_ss [p_space_def] THEN ASM_SET_TAC [],
    ALL_TAC] THEN
   RW_TAC std_ss [Int_stable] THEN
   FULL_SIMP_TAC std_ss [GSPECIFICATION, EXISTS_PROD] THEN
   Q.EXISTS_TAC `p_2 INTER p_2'` THEN SIMP_TAC std_ss [PREIMAGE_INTER] THEN
   CONJ_TAC THENL [ASM_SET_TAC [PREIMAGE_def], ALL_TAC] THEN
   MATCH_MP_TAC MEASURE_SPACE_INTER THEN ASM_SET_TAC []] THEN
  Q.UNABBREV_TAC `proj` THEN FULL_SIMP_TAC std_ss [restrict] THEN
  POP_ASSUM MP_TAC THEN MATCH_MP_TAC EQ_IMPLIES THEN
  MATCH_MP_TAC indep_sets_cong THEN ASM_SIMP_TAC std_ss [] THEN
  RW_TAC std_ss [] THEN AP_TERM_TAC THEN SET_TAC []);

val indep_var_restrict = store_thm ("indep_var_restrict",
  ``!p M' X ii A B. prob_space p /\ indep_vars p M' X ii /\
      (A INTER B = {}) /\ A SUBSET ii /\ B SUBSET ii /\
      measure_space (PiM A M') /\ measure_space (PiM B M') /\
      (!i. measure_space (M' i)) ==>
      indep_var p (PiM A M') (\w. restrict (\i. X i w) A)
                  (PiM B M') (\w. restrict (\i. X i w) B)``,
  RW_TAC std_ss [indep_var] THEN
  Q_TAC SUFF_TAC `indep_vars p (\i. PiM ((\i. if i = 0 then A else B) i) M')
                  (\i w. restrict (\i. X i w) ((\i. if i = 0 then A else B) i))
                  {x | (x = 0) \/ (x = 1)}` THENL
  [SIMP_TAC std_ss [indep_vars] THEN RW_TAC std_ss [] THENL
   [FIRST_X_ASSUM (MP_TAC o Q.SPEC `i`) THEN RW_TAC std_ss [],
    ALL_TAC] THEN
   FULL_SIMP_TAC std_ss [indep_sets] THEN CONJ_TAC THENL
   [RW_TAC std_ss [] THENL
    [FIRST_X_ASSUM (MP_TAC o Q.SPEC `0`) THEN RW_TAC std_ss [],
     ALL_TAC] THEN
    FIRST_X_ASSUM (MP_TAC o Q.SPEC `i:num`) THEN ASM_SIMP_TAC std_ss [],
    ALL_TAC] THEN
   RW_TAC std_ss [] THEN FIRST_X_ASSUM (MP_TAC o Q.SPEC `J`) THEN
   ASM_SIMP_TAC std_ss [] THEN DISCH_THEN MATCH_MP_TAC THEN
   FULL_SIMP_TAC std_ss [Pi_iff] THEN RW_TAC std_ss [] THENL
   [FIRST_X_ASSUM (MP_TAC o Q.SPEC `0`) THEN RW_TAC std_ss [],
    ALL_TAC] THEN
   FIRST_X_ASSUM (MP_TAC o Q.SPEC `i:num`) THEN ASM_SIMP_TAC std_ss [],
   ALL_TAC] THEN
  MATCH_MP_TAC indep_vars_restrict THEN Q.EXISTS_TAC `ii` THEN
  ASM_SIMP_TAC std_ss [] THEN RW_TAC std_ss [GSPECIFICATION] THEN
  RW_TAC std_ss [disjoint_family_on] THEN ASM_SET_TAC []);

val measurable_component_singleton = store_thm ("measurable_component_singleton",
  ``!ii M i. (!i. measure_space (M i)) /\
     (measure_space (PiM ii M)) /\ i IN ii ==> (\f. f i) IN measurable
     (m_space (PiM ii M), measurable_sets (PiM ii M))
     (m_space (M i), measurable_sets (M i))``,
  RW_TAC std_ss [IN_MEASURABLE] THENL
  [FULL_SIMP_TAC std_ss [measure_space_def],
   FULL_SIMP_TAC std_ss [measure_space_def],
   SIMP_TAC std_ss [space_def, IN_FUNSET] THEN
   SIMP_TAC std_ss [SIMP_RULE std_ss [ETA_AX] space_PiM] THEN
   SIMP_TAC std_ss [PiE_iff] THEN RW_TAC std_ss [],
   ALL_TAC] THEN
  SIMP_TAC std_ss [space_def, subsets_def] THEN
  Q_TAC SUFF_TAC `PREIMAGE (\f. f i) s INTER m_space (PiM ii M) =
   prod_emb ii M {i} (PiE {i} (\i. s))` THENL
  [DISC_RW_KILL,
   SIMP_TAC std_ss [prod_emb] THEN
   SIMP_TAC std_ss [SIMP_RULE std_ss [ETA_AX] space_PiM] THEN
   SIMP_TAC std_ss [EXTENSION, IN_IMAGE, IN_PREIMAGE, IN_INTER, restrict] THEN
   RW_TAC std_ss [PiE_iff] THEN EQ_TAC THEN RW_TAC std_ss [] THENL
   [ASM_SET_TAC [],
    SIMP_TAC std_ss [GSYM restrict, restrict_extensional],
    ALL_TAC] THEN
   ASM_SET_TAC []] THEN
  MATCH_MP_TAC (SIMP_RULE std_ss [ETA_AX] sets_PiM_I) THEN
  FULL_SIMP_TAC std_ss [subsets_def, FINITE_SING] THEN
  ASM_SET_TAC []);

val borel_measurable_sum = store_thm ("borel_measurable_sum",
  ``!f s M. FINITE s /\ sigma_algebra M /\
     (!i. i IN s ==> f i IN borel_measurable M) ==>
     (\x. sum s (\i. f i x)) IN borel_measurable M``,
  REPEAT GEN_TAC THEN Q.SPEC_TAC (`s`,`s`) THEN
  SIMP_TAC std_ss [GSYM AND_IMP_INTRO] THEN SET_INDUCT_TAC THENL
  [RW_TAC std_ss [SUM_CLAUSES] THEN MATCH_MP_TAC borel_measurable_const THEN
   ASM_SIMP_TAC std_ss [], ALL_TAC] THEN
  RW_TAC std_ss [] THEN ASM_SIMP_TAC std_ss [SUM_CLAUSES] THEN
  MATCH_MP_TAC borel_measurable_add THEN
  Q.EXISTS_TAC `f e` THEN Q.EXISTS_TAC `(\x. sum s (\i. f i x))` THEN
  ASM_SIMP_TAC std_ss [] THEN ASM_SET_TAC []);

val measure_space_PiM = store_thm ("measure_space_PiM",
  ``!s M. measure_space (PiM s M)``,
  RW_TAC std_ss [measure_space_def] THENL
  [SIMP_TAC std_ss [SIMP_RULE std_ss [ETA_AX] sets_PiM] THEN
   SIMP_TAC std_ss [SIMP_RULE std_ss [ETA_AX] space_PiM] THEN
   MATCH_MP_TAC sigma_algebra_sigma_sets THEN
   METIS_TAC [prod_algebra_sets_into_space],
   RW_TAC std_ss [positive_def, PiM, extend_measure, measure_of, measure_def,
    le_refl, measure_space_def, measurable_sets_def, m_space_def] THEN
   RW_TAC std_ss [le_refl],
   ALL_TAC] THEN
  RW_TAC std_ss [countably_additive_def, PiM, extend_measure, measure_of, measure_def] THEN
  RW_TAC std_ss [o_DEF, le_refl, suminf_0] THENL
  [POP_ASSUM MP_TAC THEN
   RW_TAC std_ss [le_refl, measure_space_def, measurable_sets_def, m_space_def,
    countably_additive_def] THEN
   FULL_SIMP_TAC std_ss [GSYM prod_algebra, IN_FUNSET, IN_UNIV, measurable_sets_def] THEN
   POP_ASSUM (MP_TAC o Q.SPEC `f`) THEN ASM_SIMP_TAC std_ss [o_DEF, measure_def],
   FULL_SIMP_TAC std_ss [] THENL
   [FULL_SIMP_TAC std_ss [IN_FUNSET, IN_UNIV, measurable_sets_def],
    ALL_TAC] THEN
   SIMP_TAC std_ss [o_DEF, suminf_0],
   FULL_SIMP_TAC std_ss [IN_FUNSET, IN_UNIV, measurable_sets_def, GSYM prod_algebra] THEN
   METIS_TAC [prod_algebra_sets_into_space],
   ALL_TAC] THEN
  FULL_SIMP_TAC std_ss [IN_FUNSET, IN_UNIV, measurable_sets_def, GSYM prod_algebra] THEN
  METIS_TAC [prod_algebra_sets_into_space]);

val indep_vars_setsum = store_thm ("indep_vars_setsum",
 ``!p X ii i. prob_space p /\ FINITE ii /\ i NOTIN ii /\
    indep_vars p (\x. (space borel,subsets borel,(\x. 0))) X (i INSERT ii) ==>
    indep_var p (space borel,subsets borel,(\x. 0)) (X i)
                (space borel,subsets borel,(\x. 0)) (\w. sum ii (\i. X i w))``,
  RW_TAC std_ss [] THEN
  Q_TAC SUFF_TAC `X i = (\f. f i) o (\w j. if j IN {i} then X j w else undefined)` THENL
  [DISC_RW_KILL, ASM_SET_TAC [o_DEF]] THEN
  Q_TAC SUFF_TAC `(\w. sum ii (\i. X i w)) =
          (\f. sum ii f) o (\w j. if j IN ii then X j w else undefined)` THENL
  [DISC_RW_KILL,
   SIMP_TAC std_ss [o_DEF] THEN ABS_TAC THEN MATCH_MP_TAC SUM_EQ THEN
   SET_TAC []] THEN
  MATCH_MP_TAC indep_var_compose THEN
  Q.EXISTS_TAC `PiM {i} (\i. (space borel,subsets borel,(\x. 0)))` THEN
  Q.EXISTS_TAC `PiM ii (\i. (space borel,subsets borel,(\x. 0)))` THEN
  ASM_SIMP_TAC std_ss [GSYM restrict, measure_space_borel] THEN
  Q_TAC SUFF_TAC `measure_space (PiM {i} (\i. (space borel,subsets borel,(\x. 0)))) /\
   measure_space (PiM ii (\i. (space borel,subsets borel,(\x. 0))))` THENL
  [STRIP_TAC THEN ASM_SIMP_TAC std_ss [] THEN CONJ_TAC THENL
   [MATCH_MP_TAC indep_var_restrict THEN Q.EXISTS_TAC `i INSERT ii` THEN
    ASM_SIMP_TAC std_ss [measure_space_borel] THEN ASM_SET_TAC [],
    ALL_TAC] THEN
   CONJ_TAC THENL
   [Q_TAC SUFF_TAC `(\f. f i) IN measurable
     (m_space (PiM {i} (\i. (space borel,subsets borel,(\x. 0)))),
      measurable_sets (PiM {i} (\i. (space borel,subsets borel,(\x. 0)))))
     (m_space ((\i. space borel,subsets borel,(\x. 0)) i),
      measurable_sets ((\i. space borel,subsets borel,(\x. 0)) i))` THENL
    [SIMP_TAC std_ss [], ALL_TAC] THEN
    MATCH_MP_TAC measurable_component_singleton THEN
    ASM_SIMP_TAC std_ss [IN_SING, measure_space_borel],
    ALL_TAC] THEN
   SIMP_TAC std_ss [m_space_def, measurable_sets_def, SPACE] THEN
   SIMP_TAC std_ss [GSYM borel_measurable] THEN
   Q_TAC SUFF_TAC `(\f. sum ii (\i. (\i f. f i) i f)) IN borel_measurable
    (m_space (PiM ii (\i. (space borel,subsets borel,(\x. 0)))),
     measurable_sets (PiM ii (\i. (space borel,subsets borel,(\x. 0)))))` THENL
   [SIMP_TAC std_ss [ETA_AX], ALL_TAC] THEN
   MATCH_MP_TAC borel_measurable_sum THEN ASM_SIMP_TAC std_ss [] THEN
   CONJ_TAC THENL [FULL_SIMP_TAC std_ss [measure_space_def], ALL_TAC] THEN
   RW_TAC std_ss [borel_measurable] THEN
   Q_TAC SUFF_TAC `(\f. f i') IN measurable
    (m_space (PiM ii (\i. (space borel,subsets borel,(\x. 0)))),
     measurable_sets (PiM ii (\i. (space borel,subsets borel,(\x. 0)))))
    (m_space ((\i. space borel,subsets borel,(\x. 0)) i'),
      measurable_sets ((\i. space borel,subsets borel,(\x. 0)) i'))` THENL
   [SIMP_TAC std_ss [m_space_def, measurable_sets_def, SPACE], ALL_TAC] THEN
   MATCH_MP_TAC measurable_component_singleton THEN
   ASM_SIMP_TAC std_ss [IN_SING, measure_space_borel],
   ALL_TAC] THEN
  SIMP_TAC std_ss [measure_space_PiM]);

val setsum_indep_normal = store_thm ("setsum_indep_normal",
  ``!p X mu sig ii.
     prob_space p /\ FINITE ii /\ ii <> {} /\
     indep_vars p (\i. (space borel, subsets borel, (\x. 0))) X ii /\
     (!i. i IN ii ==> 0 < sig i) /\
     (!i. i IN ii ==> normal_rv (X i) p (mu i) (sig i)) ==>
     normal_rv (\x. sum ii (\i. (X i) x)) p (sum ii (\i. mu i))
               (sqrt (sum ii (\i. (sig i) pow 2)))``,
  REPEAT GEN_TAC THEN REWRITE_TAC [GSYM AND_IMP_INTRO] THEN DISCH_TAC THEN
  Q.SPEC_TAC (`ii`,`ii`) THEN SET_INDUCT_TAC THEN RW_TAC std_ss [] THEN
  ASM_CASES_TAC ``s:num->bool = {}`` THENL
  [ASM_SIMP_TAC std_ss [INSERT_DEF, NOT_IN_EMPTY] THEN
   SIMP_TAC std_ss [SET_RULE ``{x | x = e} = {e}``, SUM_SING] THEN
   `0 < sig e` by ASM_SET_TAC [] THEN
   `0 <= sig e` by ASM_SIMP_TAC real_ss [REAL_LT_IMP_LE] THEN
   ASM_SIMP_TAC std_ss [POW_2_SQRT] THEN ASM_SET_TAC [],
   ALL_TAC] THEN
  ASM_SIMP_TAC std_ss [SUM_CLAUSES] THEN
  `0 < sig e` by ASM_SET_TAC [] THEN
  `0 <= sig e` by ASM_SIMP_TAC real_ss [REAL_LT_IMP_LE] THEN
  ASM_SIMP_TAC std_ss [POW_2_SQRT] THEN
  Q.ABBREV_TAC `Y = (\x. sum s (\i. X i x))` THEN
  Q.ABBREV_TAC `mu2 = sum s (\i. mu i)` THEN
  Q.ABBREV_TAC `sig2 = sqrt (sum s (\i. sig i pow 2))` THEN
  Q_TAC SUFF_TAC `0 < sum s (\i. sig i pow 2)` THENL
  [DISCH_TAC,
   MATCH_MP_TAC SUM_POS_LT THEN
   FULL_SIMP_TAC std_ss [GSYM MEMBER_NOT_EMPTY] THEN
    `0 < 1:real` by REAL_ARITH_TAC THEN
    `!x. x  IN s ==> 0 < sig x pow (SUC 1)` by
     (GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC POW_POS_LT THEN
      ASM_SET_TAC []) THEN
    FULL_SIMP_TAC real_ss [] THEN CONJ_TAC THENL
    [RW_TAC std_ss [] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
     ASM_SET_TAC [], ALL_TAC] THEN Q.EXISTS_TAC `x'` THEN
    ASM_SET_TAC []] THEN
  `0 <= sum s (\i. sig i pow 2)` by METIS_TAC [REAL_LT_IMP_LE] THEN
  Q_TAC SUFF_TAC `normal_rv (\x. X e x + Y x) p (mu e + mu2)
                            (sqrt (sig e pow 2 + sig2 pow 2))` THENL
  [Q.UNABBREV_TAC `Y` THEN Q.UNABBREV_TAC `sig2` THEN
   Q.UNABBREV_TAC `mu2` THEN ASM_SIMP_TAC std_ss [SQRT_POW_2],
   ALL_TAC] THEN
  MATCH_MP_TAC sum_indep_normal THEN ASM_SIMP_TAC std_ss [] THEN
  CONJ_TAC THENL
  [Q.UNABBREV_TAC `sig2` THEN ASM_SIMP_TAC std_ss [SQRT_POS_LT], ALL_TAC] THEN
  `normal_rv (X e) p (mu e) (sig e)` by ASM_SET_TAC [] THEN
  `normal_rv Y p mu2 sig2` by
   (FULL_SIMP_TAC std_ss [AND_IMP_INTRO] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    RW_TAC std_ss [] THENL [ALL_TAC, ASM_SET_TAC [], ASM_SET_TAC []] THEN
    FULL_SIMP_TAC std_ss [indep_vars] THEN
    CONJ_TAC THENL [ASM_SET_TAC [], ALL_TAC] THEN
    FULL_SIMP_TAC std_ss [indep_sets] THEN ASM_SET_TAC []) THEN
  Q.UNABBREV_TAC `Y` THEN ASM_SIMP_TAC std_ss [] THEN
  MATCH_MP_TAC indep_vars_setsum THEN ASM_SIMP_TAC std_ss []);

(* ------------------------------------------------------------------------- *)
(* Application 1                                                             *)
(* ------------------------------------------------------------------------- *)

val joint_distribution_sym = store_thm
 ("joint_distribution_sym",``!p X Y a b. prob_space p  ==>
       (joint_distribution p X Y (a CROSS b) = joint_distribution p Y X (b CROSS a))``,
  RW_TAC std_ss [joint_distribution_def] THEN
  Q_TAC SUFF_TAC
   `PREIMAGE (\x. (X x,Y x)) (a CROSS b) INTER p_space p =
    PREIMAGE (\x. (Y x,X x)) (b CROSS a) INTER p_space p` THENL
  [METIS_TAC [], ALL_TAC] THEN
  RW_TAC std_ss [EXTENSION,IN_INTER,IN_PREIMAGE,IN_CROSS] THEN
  METIS_TAC []);

val pos_fn_integral_not_neginf = store_thm ("pos_fn_integral_not_neginf",
  ``!f. (!x. 0 <= f x) ==> pos_fn_integral lborel f <> NegInf``,
  RW_TAC std_ss [lt_infty] THEN
  Q_TAC SUFF_TAC `0 <= pos_fn_integral lborel f` THENL
   [ALL_TAC, MATCH_MP_TAC pos_fn_integral_pos THEN
    ASM_SIMP_TAC std_ss [measure_space_lborel]] THEN
  DISCH_TAC THEN METIS_TAC [lt_infty, lte_trans, num_not_infty]);


val _ = export_theory();
