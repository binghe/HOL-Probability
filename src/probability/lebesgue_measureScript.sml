* ========================================================================= *)
(*                                                                           *)
(*                        Lebesgue Measure Theory                            *)
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
(* Note: This theory is inspired by Isabelle/HOL                             *)
(* Last update: Jan, 2015                                                    *)
(*                                                                           *)
(* ========================================================================= *)

open HolKernel Parse boolLib bossLib;

open numLib unwindLib tautLib Arith prim_recTheory combinTheory quotientTheory
     arithmeticTheory pairTheory listTheory mesonLib pred_setTheory pred_setLib
     optionTheory numTheory sumTheory InductiveDefinition ind_typeTheory;

(* real analysis *)
open realaxTheory realTheory realLib jrhUtils seqTheory limTheory transcTheory
     real_sigmaTheory iterateTheory cardinalTheory productTheory RealArith
     real_topologyTheory derivativeTheory integrationTheory;

(* probability *)
open hurdUtils util_probTheory extrealTheory sigma_algebraTheory measureTheory
     borelTheory lebesgueTheory;

(* NOTE: the existing "lebesgue" theory is actually "lebesgue_integration" *)
val _ = new_theory "lebesgue_measure";

fun MESON ths tm = prove(tm,MESON_TAC ths);
fun METIS ths tm = prove(tm,METIS_TAC ths);

val DISC_RW_KILL = DISCH_TAC THEN ONCE_ASM_REWRITE_TAC [] THEN
                   POP_ASSUM K_TAC;

fun ASSERT_TAC tm = SUBGOAL_THEN tm STRIP_ASSUME_TAC;
val ASM_ARITH_TAC = REPEAT (POP_ASSUM MP_TAC) THEN ARITH_TAC;

(* Minimal hol-light compatibility layer *)
val ASM_REAL_ARITH_TAC = REAL_ASM_ARITH_TAC; (* RealArith *)
val IMP_CONJ           = CONJ_EQ_IMP;        (* cardinalTheory *)
val FINITE_SUBSET      = SUBSET_FINITE_I;    (* pred_setTheory *)
val LE_0               = ZERO_LESS_EQ;       (* arithmeticTheory *)

(* ------------------------------------------------------------------------- *)
(* Measure type                                                              *)
(* ------------------------------------------------------------------------- *)

val _ = hide "positive_alt";

val positive_alt = new_definition ("positive_alt",
  ``positive_alt M u <=> (u {} = 0:extreal) /\ !a. a IN M ==> 0 <= u a``);

val positive_alt_eq = store_thm ("positive_alt_eq",
  ``!sp M u. positive (sp, M, u) = (u {} = 0) /\ !a. a IN M ==> 0 <= u a``,
  METIS_TAC [positive_def, measure_def, measurable_sets_def]);

val countably_additive_alt = new_definition ("countably_additive_alt",
  ``countably_additive_alt M (u:('a->bool)->extreal) <=>
    (!A. IMAGE A UNIV SUBSET M ==> disjoint_family A ==>
        BIGUNION {A i | i IN UNIV} IN M ==>
        ((u (BIGUNION {A i | i IN univ(:num)})) = suminf (u o A)))``);

val measure_space_alt = new_definition ("measure_space_alt",
  ``measure_space_alt sp A u <=> sigma_algebra_alt sp A /\ positive_alt A u /\
                                 countably_additive_alt A u``);

val measure_space_alt_eq = store_thm ("measure_space_alt_eq",
  ``!sp M u. measure_space (sp,M,u) =
             sigma_algebra_alt sp M /\ positive_alt M u /\
             countably_additive_alt M u``,
  SIMP_TAC std_ss [measure_space_def, m_space_def, measurable_sets_def] THEN
  SIMP_TAC std_ss [sigma_algebra_alt_eq, sigma_algebra_alt] THEN
  SIMP_TAC std_ss [positive_alt_eq, positive_alt] THEN
  SIMP_TAC std_ss [countably_additive_alt_eq, countably_additive_alt]);

val measure_of = new_definition ("measure_of",
  ``measure_of (sp,A,u) = (sp,
     (if A SUBSET POW sp then (sigma_sets sp A) else {{};sp}),
     (\a. if a IN sigma_sets sp A /\ measure_space (sp, sigma_sets sp A, u)
        then u a else 0))``);

val measure_space_0 = store_thm ("measure_space_0",
  ``!sp A. A SUBSET POW sp ==> measure_space (sp, sigma_sets sp A, (\x. 0))``,
  SIMP_TAC std_ss [measure_space_def] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  SIMP_TAC std_ss [m_space_def, measurable_sets_def] THEN
  FULL_SIMP_TAC std_ss [sigma_algebra_sigma_sets] THEN
  SIMP_TAC real_ss [positive_def, countably_additive_def] THEN
  SIMP_TAC std_ss [measure_def, le_refl, o_DEF] THEN
  RW_TAC std_ss [suminf_0]);

val sigma_algebra_trivial = store_thm ("sigma_algebra_trivial",
  ``!s. sigma_algebra (s, {{}; s})``,
  GEN_TAC THEN REWRITE_TAC [SIGMA_ALGEBRA] THEN
  REWRITE_TAC [space_def, subsets_def] THEN REWRITE_TAC [subset_class_def] THEN
  REWRITE_TAC [SET_RULE ``s IN {a;b} = ((s = a) \/ (s = b))``] THEN
  REPEAT (CONJ_TAC THENL [SET_TAC [], ALL_TAC]) THEN REPEAT STRIP_TAC THEN
  FULL_SIMP_TAC std_ss [SUBSET_DEF] THEN
  FULL_SIMP_TAC std_ss [SET_RULE ``s IN {a;b} = ((s = a) \/ (s = b))``] THEN
  SIMP_TAC std_ss [EXTENSION, BIGUNION, GSPECIFICATION] THEN
  ASM_SET_TAC []);

val measure_space_0' = store_thm ("measure_space_0'",
  ``!sp. measure_space (sp, {{}; sp}, (\x. 0))``,
  GEN_TAC THEN SIMP_TAC std_ss [measure_space_def] THEN
  SIMP_TAC real_ss [positive_def, measure_def] THEN CONJ_TAC THENL
  [ALL_TAC,
   SIMP_TAC std_ss [countably_additive_def, measure_def, o_DEF] THEN
   RW_TAC std_ss [suminf_0] THEN SIMP_TAC std_ss [le_refl]] THEN
  SIMP_TAC std_ss [sigma_algebra_iff2, SUBSET_DEF, POW_DEF] THEN
  SIMP_TAC std_ss [measurable_sets_def, m_space_def] THEN
  SIMP_TAC std_ss [SET_RULE ``a IN {b;c} = ((a = b) \/ (a = c))``] THEN
  SET_TAC []);

val measure_space_closed = store_thm ("measure_space_closed",
  ``!sp M u. measure_space (sp, M, u) ==> M SUBSET POW sp``,
  REPEAT GEN_TAC THEN SIMP_TAC std_ss [measure_space_def, sigma_algebra_iff2] THEN
  SIMP_TAC std_ss [measurable_sets_def, m_space_def]);

val positive_cong_eq = store_thm ("positive_cong_eq",
  ``!sp M u u'. ring sp M /\ (!a. a IN M ==> (u' a = u a)) ==>
                (positive (sp,M,u) = positive (sp,M,u'))``,
  SIMP_TAC std_ss [positive_def, measure_def, measurable_sets_def] THEN
  RW_TAC std_ss [ring, semiring, subset_class_def]);

val countably_additive_eq = store_thm ("countably_additive_eq",
  ``!sp M u u'. (!a. a IN M ==> (u' a = u a)) ==>
                (countably_additive (sp,M,u') = countably_additive (sp,M,u))``,
  SIMP_TAC std_ss [countably_additive_def] THEN
  REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM (MP_TAC o SPEC ``f:num->'a->bool``) THEN
  FULL_SIMP_TAC std_ss [measurable_sets_def, measure_def, o_DEF] THEN
  DISCH_TAC THEN AP_TERM_TAC THEN ABS_TAC THENL
  [ALL_TAC, ONCE_REWRITE_TAC [EQ_SYM_EQ]] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN POP_ASSUM K_TAC THEN
  POP_ASSUM K_TAC THEN POP_ASSUM K_TAC THEN POP_ASSUM MP_TAC THEN
  EVAL_TAC THEN SET_TAC []);

val measure_space_eq = store_thm ("measure_space_eq",
  ``!sp A u u'. A SUBSET POW sp /\
             (!a. a IN sigma_sets sp A ==> (u a = u' a)) ==>
             (measure_space (sp, (sigma_sets sp A), u) =
              measure_space (sp, (sigma_sets sp A), u'))``,
  REPEAT STRIP_TAC THEN POP_ASSUM MP_TAC THEN FIRST_ASSUM MP_TAC THEN
  DISCH_THEN (MP_TAC o MATCH_MP sigma_algebra_sigma_sets) THEN
  SIMP_TAC std_ss [measure_space_def] THEN REPEAT STRIP_TAC THEN
  SIMP_TAC std_ss [measurable_sets_def, m_space_def] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC (TAUT `(a = b) /\ (c = d) ==>
    ((a /\ c) = (b /\ d))`) THEN CONJ_TAC THENL
  [MATCH_MP_TAC positive_cong_eq THEN ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
   FULL_SIMP_TAC std_ss [sigma_algebra_alt_eq, algebra_alt_eq],
   MATCH_MP_TAC countably_additive_eq THEN ASM_REWRITE_TAC []]);

val measure_of_eq = store_thm ("measure_of_eq",
  ``!sp A u u'. A SUBSET POW sp /\ (!a. a IN sigma_sets sp A ==> (u a = u' a)) ==>
                (measure_of (sp,A,u) = measure_of (sp,A,u'))``,
  REPEAT GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM MP_TAC THEN
  DISCH_THEN (MP_TAC o MATCH_MP measure_space_eq) THEN
  SIMP_TAC std_ss [measure_of] THEN DISCH_TAC THEN
  ABS_TAC THEN COND_CASES_TAC THEN FULL_SIMP_TAC std_ss []);

val space_sets_measure_conv = store_thm ("space_sets_measure_conv",
  ``!sp A u. (m_space (measure_of (sp,A,u)) = sp) /\
             (measurable_sets (measure_of (sp,A,u)) =
              if A SUBSET POW sp then sigma_sets sp A else {{};sp}) /\
             (measure (measure_of (sp,A,u)) =
              (\a. if a IN sigma_sets sp A /\
               measure_space (sp, (sigma_sets sp A), u) then u a else 0))``,
  SIMP_TAC std_ss [m_space_def, measurable_sets_def, measure_of, measure_def]);

val space_measure_of_conv = store_thm ("space_measure_of_conv",
  ``!sp A u. (m_space (measure_of (sp,A,u)) = sp)``,
  SIMP_TAC std_ss [space_sets_measure_conv]);

val sets_measure_of_conv = store_thm ("sets_measure_of_conv",
  ``!sp A u. (measurable_sets (measure_of (sp,A,u)) =
              if A SUBSET POW sp then sigma_sets sp A else {{};sp})``,
  SIMP_TAC std_ss [space_sets_measure_conv]);

val measure_measure_of_conv = store_thm ("measure_measure_of_conv",
  ``!sp A u. (measure (measure_of (sp,A,u)) =
              (\a. if a IN sigma_sets sp A /\
               measure_space (sp, (sigma_sets sp A), u) then u a else 0))``,
  SIMP_TAC std_ss [space_sets_measure_conv]);

val measure_space_imp_sigma_sets_eq = store_thm ("measure_space_imp_sigma_sets_eq",
  ``!sp A u. A SUBSET POW sp /\ measure_space (sp,A,u) ==>
             (measurable_sets (sp,A,u) = sigma_sets sp A)``,
  SIMP_TAC std_ss [measure_space_def, m_space_def, measurable_sets_def] THEN
  SIMP_TAC std_ss [sigma_sets_eq]);

val sets_measure_of_eq = store_thm ("sets_measure_of_eq",
  ``!sp M u. sigma_algebra (sp,M) ==> (measurable_sets (measure_of (sp,M,u)) = M)``,
  REPEAT STRIP_TAC THEN KNOW_TAC ``M SUBSET POW sp`` THENL
  [FULL_SIMP_TAC std_ss [sigma_algebra_alt_eq, algebra_alt_eq, ring, semiring] THEN
   ASM_SET_TAC [subset_class_def, POW_DEF], DISCH_TAC] THEN
 FULL_SIMP_TAC std_ss [sets_measure_of_conv, sigma_sets_eq]);

val space_measure_of_eq = store_thm ("space_measure_of_eq",
  ``!sp M u. m_space (measure_of (sp,M,u)) = sp``,
  SIMP_TAC std_ss [space_measure_of_conv]);

(* ------------------------------------------------------------------------- *)
(* subsection {* Constructing simple @{typ "'a measure"} *}                  *)
(* ------------------------------------------------------------------------- *)

val measure_measure_of = store_thm ("measure_measure_of",
  ``!M sp A u X.
     (M = measure_of (sp,A,u)) /\ A SUBSET POW sp /\ positive (sp, measurable_sets M, u) /\
      countably_additive (sp, measurable_sets M, u) /\ X IN measurable_sets M ==>
     (measure M X = u X)``,
  RW_TAC std_ss [] THEN SIMP_TAC std_ss [measure_of, measure_def] THEN
  POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
  ASM_SIMP_TAC std_ss [sets_measure_of_conv] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC std_ss [measure_space_def, m_space_def, measurable_sets_def] THEN
  ASM_SIMP_TAC std_ss [sigma_algebra_sigma_sets]);

val measure_measure_of_sigma = store_thm ("measure_measure_of_sigma",
  ``!sp M u A. sigma_algebra (sp, M) /\ positive (sp, M, u) /\
               countably_additive (sp, M, u) /\ A IN M ==>
               (measure (measure_of (sp,M,u)) A = u A)``,
  RW_TAC std_ss [] THEN MATCH_MP_TAC measure_measure_of THEN
  EXISTS_TAC ``sp:'a->bool`` THEN EXISTS_TAC ``M:('a->bool)->bool`` THEN
  FIRST_ASSUM (ASSUME_TAC o MATCH_MP sets_measure_of_eq) THEN
  FULL_SIMP_TAC std_ss [sigma_algebra_iff2]);

val sets_eq_imp_space_eq = store_thm ("sets_eq_imp_space_eq",
  ``!M M'. measure_space M /\ measure_space M' /\
          (measurable_sets M = measurable_sets M') ==> (m_space M = m_space M')``,
  REPEAT STRIP_TAC THEN POP_ASSUM MP_TAC THEN
  FIRST_ASSUM (MP_TAC o MATCH_MP MEASURE_SPACE_MSPACE_MEASURABLE) THEN
  POP_ASSUM (MP_TAC o REWRITE_RULE [measure_space_def, sigma_algebra_iff2]) THEN
  FIRST_ASSUM (MP_TAC o MATCH_MP MEASURE_SPACE_MSPACE_MEASURABLE) THEN
  POP_ASSUM (MP_TAC o REWRITE_RULE [measure_space_def, sigma_algebra_iff2]) THEN
  REPEAT STRIP_TAC THEN FULL_SIMP_TAC std_ss [SUBSET_DEF, IN_POW] THEN
  ASM_SET_TAC []);

val measure_of_reduce = store_thm ("measure_of_reduce",
  ``!M. measure_of M = measure_of (m_space M, measurable_sets M, measure M)``,
  SIMP_TAC std_ss [MEASURE_SPACE_REDUCE]);

val measure_notin_sets = store_thm ("measure_notin_sets",
  ``!A M. measure_space M /\ A NOTIN measurable_sets M ==>
    (measure (measure_of M) A = 0)``,
  RW_TAC std_ss [] THEN ONCE_REWRITE_TAC [measure_of_reduce] THEN
  SIMP_TAC std_ss [measure_of, measure_def] THEN
  FULL_SIMP_TAC std_ss [measure_space_def, m_space_def, measurable_sets_def] THEN
  FIRST_ASSUM (ASSUME_TAC o MATCH_MP sigma_sets_eq) THEN METIS_TAC []);

val measure_eqI = store_thm ("measure_eqI",
  ``!M N. measure_space M /\ measure_space N /\
          (measurable_sets M = measurable_sets N) /\
          (!A. A IN measurable_sets M ==>
            (measure M A = measure N A)) ==>
          (measure_of M = measure_of N)``,
  RW_TAC std_ss [] THEN ONCE_REWRITE_TAC [measure_of_reduce] THEN
  KNOW_TAC ``m_space M = m_space N`` THENL
  [METIS_TAC [sets_eq_imp_space_eq], DISCH_TAC] THEN
  ASM_SIMP_TAC std_ss [] THEN MATCH_MP_TAC measure_of_eq THEN
  FULL_SIMP_TAC std_ss [measure_space_def] THEN
  FULL_SIMP_TAC std_ss [sigma_sets_eq, sigma_algebra_iff2]);

(* ------------------------------------------------------------------------- *)
(* Measurable funtions                                                       *)
(* ------------------------------------------------------------------------- *)

val measurable_space = store_thm ("measurable_space",
  ``!f M A. f IN measurable M A ==>
            !x. x IN space M ==> f x IN space A``,
  SIMP_TAC std_ss [measurable_def, GSPECIFICATION] THEN
  EVAL_TAC THEN SET_TAC []);

val measurable_sets = store_thm ("measurable_sets",
  ``!f M A. f IN measurable M A ==>
            !s. s IN subsets A ==> PREIMAGE f s INTER space M IN subsets M``,
  SIMP_TAC std_ss [measurable_def, GSPECIFICATION, IN_FUNSET]);

val measurable_sets_Collect = store_thm ("measurable_sets_Collect",
  ``!f M N P. f IN measurable M N /\ {x | x IN space N /\ P x} IN subsets N ==>
              {x | x IN space M /\ P (f x)} IN subsets M``,
  REPEAT STRIP_TAC THEN
  KNOW_TAC ``PREIMAGE (f:'a->'b) {x | x IN space N /\ P x} INTER space M =
                                 {x | x IN space M /\ P (f x)}`` THENL
  [FIRST_ASSUM (MP_TAC o MATCH_MP measurable_space) THEN
   DISCH_TAC THEN SIMP_TAC std_ss [PREIMAGE_def] THEN
   SIMP_TAC std_ss [INTER_DEF, EXTENSION, GSPECIFICATION] THEN
   ASM_SET_TAC [], DISCH_TAC] THEN METIS_TAC [measurable_sets]);

val measurable_cong_sets = store_thm ("measurable_cong_sets",
  ``!M N M' N'. measure_space M /\ measure_space M' /\
                measure_space N /\ measure_space N' /\
                (measurable_sets M = measurable_sets M') /\
                (measurable_sets N = measurable_sets N') ==>
                (measurable (m_space M, measurable_sets M)
                            (m_space N, measurable_sets N) =
                 measurable (m_space M', measurable_sets M')
                            (m_space N', measurable_sets N'))``,
  RW_TAC std_ss [] THEN
  KNOW_TAC ``(m_space M = m_space M') /\ (m_space N = m_space N')`` THENL
  [METIS_TAC [sets_eq_imp_space_eq], STRIP_TAC] THEN
  FULL_SIMP_TAC std_ss []);

val image_inter_cong = store_thm ("image_inter_cong",
  ``!(f:'a->'b) g s y. (!w. w IN s ==> (f w = g w)) ==>
              ((PREIMAGE f y) INTER s = (PREIMAGE g y) INTER s)``,
  RW_TAC std_ss [INTER_DEF, PREIMAGE_def] THEN
  ASM_SET_TAC []);

val measurable_cong = store_thm ("measurable_cong",
  ``!f g M N.
    (!w. w IN m_space M ==>  (f w = g w)) ==>
    (f IN measurable (m_space M, measurable_sets M)
                     (m_space N, measurable_sets N) =
     g IN measurable (m_space M, measurable_sets M)
                     (m_space N, measurable_sets N))``,
  RW_TAC std_ss [IN_MEASURABLE, IN_FUNSET] THEN EQ_TAC THEN
  RW_TAC std_ss [space_def, subsets_def] THEN
  FIRST_X_ASSUM (MP_TAC o MATCH_MP image_inter_cong) THEN
  METIS_TAC []);

val measurable_eqI = store_thm ("measurable_eqI",
  ``(m_space m1 = m_space m1') /\ (m_space m2 = m_space m2') /\
    (measurable_sets m1 = measurable_sets m1') /\
    (measurable_sets m2 = measurable_sets m2') ==>
    (measurable (m_space m1, measurable_sets m1)
                (m_space m2, measurable_sets m2) =
     measurable (m_space m1', measurable_sets m1')
                (m_space m2', measurable_sets m2'))``,
  FULL_SIMP_TAC std_ss []);

val measurable_compose = store_thm ("measurable_compose",
  ``!f g M N L. f IN measurable M N /\ g IN measurable N L ==>
                (\x. g (f x)) IN measurable M L``,
  REPEAT STRIP_TAC THEN SIMP_TAC std_ss [GSYM o_DEF] THEN
METIS_TAC [MEASURABLE_COMP]);

val measurable_const = store_thm ("measurable_const",
  ``!c M N. c IN m_space N /\ measure_space M /\ measure_space N ==>
       (\x. c) IN measurable (m_space M, measurable_sets M)
                             (m_space N, measurable_sets N)``,
  RW_TAC std_ss [measurable_def, IN_MEASURABLE, space_def, subsets_def] THEN
  FULL_SIMP_TAC std_ss [measure_space_def, IN_FUNSET, PREIMAGE_def] THEN
  REWRITE_TAC [SET_RULE ``{x | x | c IN s} = if c IN s then UNIV else {}``] THEN
  COND_CASES_TAC THEN SIMP_TAC std_ss [INTER_EMPTY, INTER_UNIV] THENL
  [METIS_TAC [MEASURE_SPACE_MSPACE_MEASURABLE, measure_space_def],
   FULL_SIMP_TAC std_ss [sigma_algebra_iff2]]);


(* ------------------------------------------------------------------------- *)
(* disjointed                                                                *)
(* ------------------------------------------------------------------------- *)




(* ------------------------------------------------------------------------- *)
(* dynkin_system                                                             *)
(* ------------------------------------------------------------------------- *)

val dynkin_system = new_definition ("dynkin_system",
  ``dynkin_system sp st = subset_class sp st /\ sp IN st /\
           (!A. A IN st ==> sp DIFF A IN st) /\
           (!A. disjoint_family A ==> IMAGE A UNIV SUBSET st ==>
                BIGUNION (IMAGE A univ(:num)) IN st)``);

val dynkin_systemI = store_thm ("dynkin_systemI",
  ``!sp st.
    (!A. A IN st ==> A SUBSET sp) /\ sp IN st /\
    (!A. A IN st ==> sp DIFF A IN st) /\
    (!A. disjoint_family A ==> IMAGE A UNIV SUBSET st ==>
         BIGUNION (IMAGE A univ(:num)) IN st) ==>
    dynkin_system sp st``,
  SET_TAC [dynkin_system, subset_class_def]);

val dynkin_system_trivial = store_thm ("dynkin_system_trivial",
  ``!A. dynkin_system A (POW A)``,
  RW_TAC std_ss [dynkin_system, IN_POW, subset_class_def] THENL
  [SET_TAC [], SET_TAC [], ALL_TAC] THEN
  FULL_SIMP_TAC std_ss [SUBSET_DEF, IN_POW, IN_BIGUNION] THEN
  METIS_TAC []);

val sigma_algebra_imp_dynkin_system = store_thm ("sigma_algebra_imp_dynkin_system",
  ``!sp st. sigma_algebra (sp,st) ==> dynkin_system sp st``,
  RW_TAC std_ss [dynkin_system, sigma_algebra_alt_eq, algebra_def] THEN
  FULL_SIMP_TAC std_ss [subsets_def, space_def, subset_class_def] THENL
  [FIRST_X_ASSUM (MP_TAC o Q.SPEC `{}`) THEN
   FIRST_X_ASSUM (MP_TAC o Q.SPEC `{}`) THEN
   ASM_SIMP_TAC std_ss [DIFF_EMPTY],
   ALL_TAC] THEN
  SIMP_TAC std_ss [IMAGE_DEF] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_SET_TAC []);

(* ------------------------------------------------------------------------- *)
(* Int_stable                                                                *)
(* ------------------------------------------------------------------------- *)

val Int_stable = new_definition ("Int_stable",
  ``Int_stable M = (!a b. a IN M /\ b IN M ==> a INTER b IN M)``);

val sigma_algebra_disjoint_iff = store_thm ("sigma_algebra_disjoint_iff",
  ``!sp st. sigma_algebra (sp,st) = algebra (sp,st) /\
             (!A. IMAGE A univ(:num) SUBSET st ==> disjoint_family A ==>
                  BIGUNION (IMAGE A UNIV) IN st)``,
  RW_TAC std_ss [] THEN EQ_TAC THEN RW_TAC std_ss [] THEN
  `algebra (sp,st)` by METIS_TAC [sigma_algebra_def] THENL
  [ALL_TAC, FULL_SIMP_TAC std_ss [algebra_def]] THEN
  FULL_SIMP_TAC std_ss [sigma_algebra_iff2, space_def, subsets_def] THEN
  TRY (METIS_TAC [IMAGE_DEF]) THEN
  FULL_SIMP_TAC std_ss [GSYM IMAGE_DEF, POW_DEF, subset_class_def] THEN
  CONJ_TAC THENL [ASM_SET_TAC [], ALL_TAC] THEN RW_TAC std_ss [] THEN
  `algebra (sp,st)` by
  METIS_TAC [algebra_def, subset_class_def, space_def, subsets_def] THEN
  FIRST_X_ASSUM (MP_TAC o Q.SPEC `disjointed A`) THEN
  SIMP_TAC std_ss [disjoint_family_disjoint] THEN
  Q_TAC SUFF_TAC `IMAGE (disjointed A) univ(:num) SUBSET st` THENL
  [DISCH_TAC THEN ASM_REWRITE_TAC [],
   ONCE_REWRITE_TAC [METIS [ETA_AX] ``(disjointed A) = (\i. disjointed A i)``] THEN
   MATCH_MP_TAC range_disjointed_sets THEN Q.EXISTS_TAC `sp` THEN
   ASM_SIMP_TAC std_ss [ring, semiring] THEN
   FULL_SIMP_TAC std_ss [ALGEBRA_ALT_INTER, space_def, subsets_def] THEN
   `algebra (sp,st)` by METIS_TAC [ALGEBRA_ALT_INTER, space_def, subsets_def] THEN
   RW_TAC std_ss [] THEN Q.EXISTS_TAC `{s DIFF t}` THEN
   SIMP_TAC std_ss [BIGUNION_SING, FINITE_SING, disjoint_sing] THEN
   RW_TAC std_ss [IN_SING, SUBSET_DEF] THEN
   ONCE_REWRITE_TAC [METIS [subsets_def]
    ``s DIFF t IN st = s DIFF t IN subsets (sp,st)``] THEN
   MATCH_MP_TAC ALGEBRA_DIFF THEN ASM_SIMP_TAC std_ss [subsets_def]] THEN
  SIMP_TAC std_ss [IMAGE_DEF, UN_disjointed_eq]);

val sigma_algebra_eq_Int_stable = store_thm ("sigma_algebra_eq_Int_stable",
  ``!sp st. dynkin_system sp st ==>
     (sigma_algebra (sp,st) = Int_stable st)``,
  RW_TAC std_ss [] THEN EQ_TAC THENL
  [RW_TAC std_ss [sigma_algebra_alt_eq, Int_stable] THEN
   METIS_TAC [ALGEBRA_ALT_INTER, subsets_def, space_def],
   ALL_TAC] THEN
  FULL_SIMP_TAC std_ss [dynkin_system] THEN
  RW_TAC std_ss [sigma_algebra_disjoint_iff, algebra_iff_Un] THENL
  [FULL_SIMP_TAC std_ss [POW_DEF, subset_class_def] THEN
   ASM_SET_TAC [],
   FIRST_X_ASSUM (MP_TAC o Q.SPEC `sp`) THEN
   FIRST_X_ASSUM (MP_TAC o Q.SPEC `sp`) THEN
   ASM_SIMP_TAC std_ss [DIFF_EQ_EMPTY],
   ALL_TAC] THEN
  `{} IN st` by (FIRST_X_ASSUM (MP_TAC o Q.SPEC `sp`) THEN
                 FIRST_X_ASSUM (MP_TAC o Q.SPEC `sp`) THEN
                 ASM_SIMP_TAC std_ss [DIFF_EQ_EMPTY]) THEN
  `algebra (sp,st)` by
   METIS_TAC [ALGEBRA_ALT_INTER, space_def, subsets_def, Int_stable] THEN
  METIS_TAC [algebra_def, subsets_def, space_def]);

(* ------------------------------------------------------------------------- *)
(* dynkin                                                                    *)
(* ------------------------------------------------------------------------- *)

val dynkin = new_definition ("dynkin",
  ``dynkin sp st = BIGINTER {D | dynkin_system sp D /\ st SUBSET D}``);

val dynkin_system_dynkin = store_thm ("dynkin_system_dynkin",
  ``!sp st. st SUBSET POW sp ==> dynkin_system sp (dynkin sp st)``,
  RW_TAC std_ss [] THEN MATCH_MP_TAC dynkin_systemI THEN
  CONJ_TAC THENL
  [RW_TAC std_ss [dynkin, IN_BIGINTER, GSPECIFICATION] THEN
   POP_ASSUM (MP_TAC o Q.SPEC `POW sp`) THEN
   ASM_SIMP_TAC std_ss [dynkin_system_trivial] THEN
   ASM_SET_TAC [POW_DEF],
   ALL_TAC] THEN
  CONJ_TAC THENL
  [SIMP_TAC std_ss [dynkin, IN_BIGINTER, GSPECIFICATION] THEN
   RW_TAC std_ss [SUBSET_DEF, dynkin_system],
   ALL_TAC] THEN
  CONJ_TAC THENL
  [RW_TAC std_ss [dynkin, IN_BIGINTER, GSPECIFICATION] THEN
   FULL_SIMP_TAC std_ss [dynkin_system],
   ALL_TAC] THEN
  RW_TAC std_ss [dynkin, GSPECIFICATION, IN_BIGINTER] THEN
  FULL_SIMP_TAC std_ss [SUBSET_DEF, GSPECIFICATION, IN_BIGINTER] THEN

  FULL_SIMP_TAC std_ss [dynkin_system] THEN
  POP_ASSUM (fn th => FIRST_ASSUM (MP_TAC o Q.SPEC `A`) THEN ASSUME_TAC th) THEN
  SIMP_TAC std_ss [AND_IMP_INTRO] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_SIMP_TAC std_ss [SUBSET_DEF]);

val restricted_dynkin_system = store_thm ("restricted_dynkin_system",
  ``!sp st D. dynkin_system sp st /\  D IN st ==>
       dynkin_system sp {Q | Q SUBSET sp /\ Q INTER D IN st}``,
  RW_TAC std_ss [] THEN MATCH_MP_TAC dynkin_systemI THEN
  SIMP_TAC std_ss [GSPECIFICATION, SUBSET_REFL] THEN
  CONJ_TAC THENL
  [FULL_SIMP_TAC std_ss [dynkin_system, subset_class_def] THEN
   `D SUBSET sp` by METIS_TAC [] THEN
   `sp INTER D = D` by ASM_SET_TAC [] THEN
   ASM_SIMP_TAC std_ss [], ALL_TAC] THEN
  CONJ_TAC THENL
  [FULL_SIMP_TAC std_ss [dynkin_system, subset_class_def] THEN
   RW_TAC std_ss [] THENL [ASM_SET_TAC [], ALL_TAC] THEN
   ONCE_REWRITE_TAC [SET_RULE
    ``(sp DIFF A) INTER D = sp DIFF ((sp DIFF D) UNION (A INTER D))``] THEN
   FIRST_ASSUM MATCH_MP_TAC THEN
   FIRST_X_ASSUM (MP_TAC o Q.SPEC `(\i. if i = 0 then sp DIFF D else
                                        if i = 1 then A INTER D else {})`) THEN
   Q_TAC SUFF_TAC `disjoint_family
    (\i:num. if i = 0 then sp DIFF D else if i = 1 then A INTER D else {})` THENL
   [DISCH_TAC THEN ASM_SIMP_TAC std_ss [],
    SIMP_TAC std_ss [disjoint_family, disjoint_family_on, IN_UNIV] THEN
    RW_TAC std_ss [] THEN ASM_SET_TAC []] THEN
   Q_TAC SUFF_TAC `IMAGE
    (\i. if i = 0 then sp DIFF D else if i = 1 then A INTER D else {})
    univ(:num) SUBSET st` THENL
   [DISCH_TAC THEN ASM_SIMP_TAC std_ss [],
    SIMP_TAC std_ss [SUBSET_DEF, IN_IMAGE, IN_UNIV] THEN RW_TAC std_ss [] THEN
    REPEAT (COND_CASES_TAC) THEN ASM_SIMP_TAC std_ss [] THEN
    FIRST_X_ASSUM (MP_TAC o Q.SPEC `sp`) THEN
    ASM_SIMP_TAC std_ss [DIFF_EQ_EMPTY]] THEN
   MATCH_MP_TAC EQ_IMPLIES THEN AP_THM_TAC THEN AP_TERM_TAC THEN
   SIMP_TAC std_ss [EXTENSION, IN_BIGUNION, GSPECIFICATION, IN_IMAGE, IN_UNIV] THEN
   SIMP_TAC std_ss [IN_UNION, IN_DIFF, IN_INTER] THEN GEN_TAC THEN
   EQ_TAC THEN RW_TAC std_ss [] THEN TRY (ASM_SET_TAC []) THENL
   [Q.EXISTS_TAC `sp DIFF D` THEN ASM_SIMP_TAC std_ss [IN_DIFF] THEN
    Q.EXISTS_TAC `0` THEN ASM_SET_TAC [], ALL_TAC] THEN
   Q.EXISTS_TAC `A INTER D` THEN ASM_SIMP_TAC std_ss [IN_INTER] THEN
   Q.EXISTS_TAC `1` THEN ASM_SIMP_TAC arith_ss [IN_INTER],
   ALL_TAC] THEN
  GEN_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
  Q_TAC SUFF_TAC `!i. A i SUBSET sp` THENL
  [DISCH_TAC,
   FULL_SIMP_TAC std_ss [dynkin_system, subset_class_def] THEN
   GEN_TAC THEN POP_ASSUM MP_TAC THEN
   SIMP_TAC std_ss [SUBSET_DEF, GSPECIFICATION] THEN
   SIMP_TAC std_ss [GSYM SUBSET_DEF] THEN
   DISCH_THEN (MP_TAC o Q.SPEC `A (i:num)`) THEN
   SET_TAC []] THEN
  Q_TAC SUFF_TAC `disjoint_family (\i. A i INTER D)` THENL
  [DISCH_TAC,
   FULL_SIMP_TAC std_ss [dynkin_system, subset_class_def] THEN
   FULL_SIMP_TAC std_ss [disjoint_family, disjoint_family_on, IN_UNIV] THEN
   ASM_SET_TAC []] THEN
  `IMAGE (\i. A i INTER D) UNIV SUBSET st` by ASM_SET_TAC [] THEN
  Q_TAC SUFF_TAC `BIGUNION (IMAGE A univ(:num)) INTER D =
                  BIGUNION (IMAGE (\i. A i INTER D) univ(:num))` THENL
  [DISCH_TAC,
   SIMP_TAC std_ss [EXTENSION, IN_BIGUNION, GSPECIFICATION, IN_INTER] THEN
   SIMP_TAC std_ss [IN_INTER, IN_IMAGE, IN_UNIV] THEN GEN_TAC THEN EQ_TAC THEN
   RW_TAC std_ss [] THENL
   [Q.EXISTS_TAC `A x' INTER D` THEN ASM_SET_TAC [],
    Q.EXISTS_TAC `A i` THEN ASM_SET_TAC [],
    ALL_TAC] THEN
   ASM_SET_TAC []] THEN
  FULL_SIMP_TAC std_ss [dynkin_system] THEN
  ASM_SET_TAC []);

val dynkin_subset = store_thm ("dynkin_subset",
  ``!sp N M. N SUBSET M /\ dynkin_system sp M ==> dynkin sp N SUBSET M``,
  RW_TAC std_ss [dynkin] THEN
  FULL_SIMP_TAC std_ss [SUBSET_DEF, IN_BIGINTER, GSPECIFICATION]);

val sigma_eq_dynkin = store_thm ("sigma_eq_dynkin",
  ``!sp M. M SUBSET POW sp /\ Int_stable M ==>
             (subsets (sigma sp M) = dynkin sp M)``,
  RW_TAC std_ss [] THEN
  Q_TAC SUFF_TAC `dynkin sp M SUBSET subsets (sigma sp M)` THENL
  [DISCH_TAC,
   SIMP_TAC std_ss [dynkin, SUBSET_DEF, IN_BIGINTER, GSPECIFICATION] THEN
   RW_TAC std_ss [] THEN POP_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC sigma_algebra_imp_dynkin_system THEN
    SIMP_TAC std_ss [sigma_def, subsets_def] THEN
    SIMP_TAC std_ss [GSYM sigma_def] THEN MATCH_MP_TAC SIGMA_ALGEBRA_SIGMA THEN
    ASM_SET_TAC [POW_DEF, subset_class_def],
    ALL_TAC] THEN
   SIMP_TAC std_ss [IN_SIGMA]] THEN
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
  Q_TAC SUFF_TAC `subsets (sigma (space (sp, dynkin sp M)) M) SUBSET
                  subsets (sp, dynkin sp M)` THENL
  [METIS_TAC [subsets_def, space_def], ALL_TAC] THEN
  MATCH_MP_TAC SIGMA_SUBSET THEN ASM_SIMP_TAC std_ss [subsets_def] THEN
  SET_TAC [dynkin]);

val dynkin_lemma = store_thm ("dynkin_lemma",
  ``!sp E M. Int_stable E /\ E SUBSET M /\
             M SUBSET subsets (sigma sp E) /\ dynkin_system sp M ==>
             (subsets (sigma sp E) = M)``,
  RW_TAC std_ss [] THEN
  `E SUBSET POW sp` by ASM_SET_TAC [POW_DEF, dynkin_system, subset_class_def] THEN
  `subsets (sigma sp E) = dynkin sp E` by METIS_TAC [sigma_eq_dynkin] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_SIMP_TAC std_ss [] THEN
  MATCH_MP_TAC dynkin_subset THEN ASM_SIMP_TAC std_ss []);

val sigma_sets_induct_disjoint = store_thm ("sigma_sets_induct_disjoint",
  ``!G A P sp.
    Int_stable G /\ G SUBSET POW sp /\ A IN subsets (sigma sp G) /\
    (!A. A IN G ==> P A) /\ P {} /\
    (!A. A IN subsets (sigma sp G) ==> P A ==> P (sp DIFF A)) /\
    (!A. disjoint_family A ==> IMAGE A UNIV SUBSET subsets (sigma sp G)
         ==> (!i. P (A i)) ==> P (BIGUNION (IMAGE A univ(:num)))) ==>
    P A``,
  RW_TAC std_ss [] THEN
  Q.ABBREV_TAC `dd = {A | A IN subsets (sigma sp G) /\ P A}` THEN
  Q_TAC SUFF_TAC `sigma_algebra (sigma sp G)` THENL
  [DISCH_TAC,
   MATCH_MP_TAC SIGMA_ALGEBRA_SIGMA THEN
   FULL_SIMP_TAC std_ss [subset_class_def, POW_DEF] THEN
   ASM_SET_TAC []] THEN
  Q_TAC SUFF_TAC `P (sp DIFF {})` THENL
  [RW_TAC std_ss [DIFF_EMPTY],
   FULL_SIMP_TAC std_ss [AND_IMP_INTRO] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   FULL_SIMP_TAC std_ss [sigma_algebra_def, algebra_def]] THEN
  Q_TAC SUFF_TAC `dynkin_system sp dd` THENL
  [DISCH_TAC,
   MATCH_MP_TAC dynkin_systemI THEN Q.UNABBREV_TAC `dd` THEN
   ASM_SIMP_TAC std_ss [GSPECIFICATION] THEN RW_TAC std_ss [] THENL
   [ASM_SET_TAC [SIGMA_ALGEBRA, SPACE_SIGMA, subset_class_def],
    Q_TAC SUFF_TAC `space (sigma sp G) IN subsets (sigma sp G)` THENL
    [METIS_TAC [SPACE_SIGMA], ALL_TAC] THEN
    MATCH_MP_TAC ALGEBRA_SPACE THEN METIS_TAC [sigma_algebra_def],
    MATCH_MP_TAC ALGEBRA_DIFF THEN
    FULL_SIMP_TAC std_ss [sigma_algebra_def] THEN
    Q_TAC SUFF_TAC `space (sigma sp G) IN subsets (sigma sp G)` THENL
    [METIS_TAC [SPACE_SIGMA], ALL_TAC] THEN
    MATCH_MP_TAC ALGEBRA_SPACE THEN METIS_TAC [sigma_algebra_def],
    FULL_SIMP_TAC std_ss [sigma_algebra_def] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    CONJ_TAC THENL [ALL_TAC, ASM_SET_TAC []] THEN
    METIS_TAC [image_countable, COUNTABLE_NUM],
    ALL_TAC] THEN
   ASM_SET_TAC []] THEN
  Q_TAC SUFF_TAC `subsets (sigma sp G) = dd` THENL
  [DISCH_TAC,
   MATCH_MP_TAC dynkin_lemma THEN ASM_SIMP_TAC std_ss [] THEN
   CONJ_TAC THENL [ALL_TAC, ASM_SET_TAC []] THEN
   Q.UNABBREV_TAC `dd` THEN RW_TAC std_ss [GSPECIFICATION, SUBSET_DEF] THEN
   ASM_SIMP_TAC std_ss [IN_SIGMA]] THEN
  ASM_SET_TAC []);

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* ------------------------------------------------------------------------- *)

val measurable_measure_of = store_thm ("measurable_measure",
  ``!M sp N f. measure_space M /\
     N SUBSET POW sp /\ f IN (m_space M -> sp) /\
     (!y. y IN N ==> (PREIMAGE f y) INTER m_space M IN measurable_sets M) ==>
     f IN measurable (m_space M, measurable_sets M) (sigma sp N)``,
  RW_TAC std_ss [] THEN MATCH_MP_TAC MEASURABLE_SIGMA THEN
  FULL_SIMP_TAC std_ss [measure_space_def, subset_class_def] THEN
  CONJ_TAC THENL [ASM_SET_TAC [POW_DEF], ALL_TAC] THEN
  RW_TAC std_ss [] THENL
  [SIMP_TAC std_ss [space_def, sigma_def] THEN
   POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN EVAL_TAC THEN METIS_TAC [],
   ALL_TAC] THEN
  FULL_SIMP_TAC std_ss [space_def, subsets_def]);

val borel_measurableI = store_thm ("borel_measurableI",
  ``!M f. (!s. real_topology$Open s ==>
           (PREIMAGE f s) INTER m_space M IN measurable_sets M) /\
          measure_space M ==>
           f IN measurable (m_space M, measurable_sets M) borel``,
  RW_TAC std_ss [borel] THEN MATCH_MP_TAC measurable_measure_of THEN
  ASM_SIMP_TAC std_ss [] THEN CONJ_TAC THENL [SET_TAC [POW_DEF], ALL_TAC] THEN
  CONJ_TAC THENL [EVAL_TAC THEN SET_TAC [], ALL_TAC] THEN
  ASM_SET_TAC []);

val borel_measurable_indicator = store_thm ("borel_measurable_indicator",
  ``!A M. A IN measurable_sets M /\ measure_space M ==>
          indicator A IN borel_measurable (m_space M, measurable_sets M)``,
  RW_TAC std_ss [borel_measurable, indicator] THEN
  KNOW_TAC ``borel = (m_space (space borel, subsets borel, (\x. 0)),
              measurable_sets (space borel, subsets borel, (\x. 0)))`` THENL
  [SIMP_TAC std_ss [m_space_def, measurable_sets_def, SPACE],
   DISC_RW_KILL] THEN
  ONCE_REWRITE_TAC [METIS [] ``(\x. if x IN (A:real->bool) then 1:real else 0) =
                               (\x. if x IN A then (\x. 1) x else (\x. 0) x)``] THEN
  MATCH_MP_TAC measurable_If_set THEN
  SIMP_TAC std_ss [IN_MEASURABLE, m_space_def, measurable_sets_def] THEN
  SIMP_TAC std_ss [space_def, subsets_def] THEN
  FIRST_ASSUM (ASSUME_TAC o MATCH_MP MEASURE_SPACE_MSPACE_MEASURABLE) THEN
  FULL_SIMP_TAC std_ss [measure_space_def, sigma_algebra_borel, SPACE] THEN
  RW_TAC std_ss [IN_FUNSET, space_borel, IN_UNIV, PREIMAGE_def] THEN
  ONCE_REWRITE_TAC
  [SET_RULE ``({x | x | (1:real) IN s} = if 1 IN s then UNIV else {}) /\
              ({x | x | (0:real) IN s} = if 0 IN s then UNIV else {})``] THENL
  [COND_CASES_TAC THEN ASM_SIMP_TAC std_ss [INTER_UNIV, INTER_EMPTY] THEN
   FULL_SIMP_TAC std_ss [sigma_algebra_iff2],
   COND_CASES_TAC THEN ASM_SIMP_TAC std_ss [INTER_UNIV, INTER_EMPTY] THEN
   FULL_SIMP_TAC std_ss [sigma_algebra_iff2],
   FULL_SIMP_TAC std_ss [sigma_algebra_def] THEN
   ONCE_REWRITE_TAC [METIS [subsets_def] ``measurable_sets M =
     subsets (m_space M, measurable_sets M)``] THEN
   MATCH_MP_TAC ALGEBRA_INTER THEN ASM_SIMP_TAC std_ss [subsets_def]]);

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* ------------------------------------------------------------------------- *)

val measurable_borel = store_thm ("measurable_borel",
   ``!f a. (f IN borel_measurable a) = (sigma_algebra a) /\
           (f IN (space a -> UNIV)) /\
           (!c. ((PREIMAGE f {x| x < c}) INTER (space a)) IN subsets a)``,
  RW_TAC std_ss [] THEN
  `sigma_algebra borel` by RW_TAC std_ss [sigma_algebra_borel] THEN
  `space borel = UNIV` by RW_TAC std_ss [space_borel] THEN EQ_TAC THENL
  [RW_TAC std_ss [borel_eq_halfspace_less,IN_MEASURABLE,IN_FUNSET,
                  IN_UNIV,subsets_def,GSPECIFICATION, borel_measurable] THEN
   SIMP_TAC std_ss [] THEN POP_ASSUM MATCH_MP_TAC THEN
   MATCH_MP_TAC IN_SIGMA THEN RW_TAC std_ss [IN_IMAGE,IN_UNIV] THEN
   METIS_TAC [], ALL_TAC] THEN
  RW_TAC std_ss [borel_measurable, borel_eq_halfspace_less] THEN
  MATCH_MP_TAC MEASURABLE_SIGMA THEN
  RW_TAC std_ss [subset_class_def,SUBSET_UNIV,IN_IMAGE,IN_UNIV] THEN
  METIS_TAC []);

val measurable_borel_alt1 = store_thm ("measurable_borel_alt1",
  ``!f a. (f IN borel_measurable a) = (sigma_algebra a) /\
          (f IN (space a -> UNIV)) /\
          (!c. ((PREIMAGE f {x| c < x}) INTER (space a)) IN subsets a)``,
  RW_TAC std_ss [] THEN
  `sigma_algebra borel` by RW_TAC std_ss [sigma_algebra_borel] THEN
  `space borel = UNIV` by RW_TAC std_ss [space_borel] THEN EQ_TAC THENL
  [RW_TAC std_ss [borel_eq_greaterThan,IN_MEASURABLE,IN_FUNSET,
                  IN_UNIV,subsets_def,GSPECIFICATION, borel_measurable] THEN
   SIMP_TAC std_ss [] THEN POP_ASSUM MATCH_MP_TAC THEN
   MATCH_MP_TAC IN_SIGMA THEN RW_TAC std_ss [IN_IMAGE,IN_UNIV] THEN
   METIS_TAC [], ALL_TAC] THEN
  RW_TAC std_ss [borel_measurable, borel_eq_greaterThan] THEN
  MATCH_MP_TAC MEASURABLE_SIGMA THEN
  RW_TAC std_ss [subset_class_def,SUBSET_UNIV,IN_IMAGE,IN_UNIV] THEN
  METIS_TAC []);

val in_measurable_borel = store_thm ("in_measurable_borel",
  ``!f a. f IN borel_measurable a =
	  (sigma_algebra a /\ f IN (space a -> UNIV) /\
	  !c. ({x | f x < c} INTER space a) IN subsets a)``,
  RW_TAC std_ss [] THEN
  `!c. {x | f x < c} = PREIMAGE f {x| x < c}` by
   RW_TAC std_ss [EXTENSION,IN_PREIMAGE,GSPECIFICATION] THEN
  RW_TAC std_ss [measurable_borel]);

val in_measurable_borel_alt1 = store_thm ("in_measurable_borel_alt1",
  ``!f a. f IN borel_measurable a =
	  (sigma_algebra a /\ f IN (space a -> UNIV) /\
	  !c. ({x | c < f x} INTER space a) IN subsets a)``,
  RW_TAC std_ss [] THEN
  `!c. {x | c < f x} = PREIMAGE f {x| c < x}` by
   RW_TAC std_ss [EXTENSION,IN_PREIMAGE,GSPECIFICATION] THEN
  RW_TAC std_ss [measurable_borel_alt1]);

val borel_measurable_const2 = store_thm ("borel_measurable_const2",
  ``!a k f. sigma_algebra a /\ (!x. x IN space a ==> (f x = k))
		 ==> f IN borel_measurable a``,
  RW_TAC std_ss [in_measurable_borel, IN_FUNSET, IN_UNIV] THEN
  SIMP_TAC std_ss [PREIMAGE_def] THEN
  Cases_on `c <= k` THENL
  [`{x | f x < c} INTER space a = {}`
    by  (RW_TAC std_ss [EXTENSION, GSPECIFICATION, NOT_IN_EMPTY, IN_INTER] THEN
         METIS_TAC [REAL_NOT_LE]) THEN
   METIS_TAC [sigma_algebra_def, algebra_def], ALL_TAC] THEN
  `{x | f x < c} INTER space a = space a`
      by (RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER] THEN
          METIS_TAC [REAL_NOT_LT]) THEN
  METIS_TAC [sigma_algebra_def, algebra_def, INTER_IDEMPOT, DIFF_EMPTY]);

val borel_measurable_cmul = store_thm ("borel_measurable_cmul",
 ``!a f g z. sigma_algebra a /\ f IN borel_measurable a /\
      (!x. x IN space a ==> (g x = z * f x))
                   ==> g IN borel_measurable a``,
  RW_TAC std_ss [] THEN Cases_on `z = 0` THENL
  [METIS_TAC [borel_measurable_const2, REAL_MUL_LZERO], ALL_TAC] THEN
  Cases_on `0 < z` THENL
  [RW_TAC real_ss [in_measurable_borel,IN_FUNSET,IN_UNIV] THEN
   `!c. {x | g x < c} INTER space a = {x | f x < c / z} INTER space a`
    by (RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER] THEN
        METIS_TAC [REAL_LT_RDIV_EQ, REAL_MUL_COMM, REAL_NOT_LT]) THEN
   METIS_TAC [in_measurable_borel], ALL_TAC] THEN
  `z < 0` by (POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN REAL_ARITH_TAC) THEN
  RW_TAC real_ss [in_measurable_borel, IN_FUNSET, IN_UNIV] THEN
  `!c. {x | g x < c} INTER space a = {x | c / z < f x} INTER space a`
      by (RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER] THEN
          METIS_TAC [REAL_LT_RDIV_EQ_NEG, REAL_MUL_COMM]) THEN
  METIS_TAC [in_measurable_borel_alt1]);

val borel_measurable_add = store_thm
  ("borel_measurable_add",``!a f g h. sigma_algebra a /\ f IN borel_measurable a /\
	g IN borel_measurable a /\
        (!x. x IN space a ==> (h x = f x + g x)) ==> h IN borel_measurable a``,
  REPEAT STRIP_TAC THEN RW_TAC std_ss [in_measurable_borel] THENL
  [RW_TAC std_ss [IN_FUNSET, IN_UNIV], ALL_TAC] THEN
  `{x | h x < c} INTER (space a) =
      BIGUNION (IMAGE (\r. {x | f x < r /\ r < c - g x } INTER space a) q_set)`
	by (RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_BIGUNION_IMAGE,
                           IN_UNIV, IN_INTER] THEN
	    EQ_TAC THENL
	    [RW_TAC std_ss [] THEN MATCH_MP_TAC Q_DENSE_IN_REAL THEN
       METIS_TAC [REAL_ARITH ``a < b - c = a + c < b:real``], ALL_TAC] THEN
	    REVERSE (RW_TAC std_ss []) THEN ASM_REWRITE_TAC [] THEN
	    METIS_TAC [REAL_LT_ADD_SUB,REAL_LT_TRANS]) THEN
  FULL_SIMP_TAC std_ss [] THEN MATCH_MP_TAC BIGUNION_IMAGE_QSET THEN
  RW_TAC std_ss [IN_FUNSET] THEN
  `{x | f x < r /\ r < c - g x} =
   {x | f x < r} INTER {x | r < c - g x}`
   by RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER] THEN
  `({x | f x < r} INTER space a) IN subsets a`
      by METIS_TAC [in_measurable_borel] THEN
  `!x. x IN space a ==> ((r < c - g x) = (g x < c - r))`
        by REAL_ARITH_TAC THEN
  `{x | r < c - g x} INTER space a = {x | g x < c - r} INTER space a`
       by (RW_TAC std_ss [IN_INTER, EXTENSION, GSPECIFICATION] THEN
           METIS_TAC []) THEN
  `({x | r < c - g x} INTER space a) IN subsets a`
      by METIS_TAC [in_measurable_borel] THEN
  `(({x | f x < r} INTER space a) INTER
      ({x | r < c - g x} INTER space a)) =
      ({x | f x < r} INTER {x | r < c - g x} INTER space a)`
	by (RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER] THEN
	    EQ_TAC THENL [RW_TAC std_ss [], ALL_TAC] THEN
	    RW_TAC std_ss []) THEN
  METIS_TAC [sigma_algebra_def, ALGEBRA_INTER]);

val borel_measurable_sub = store_thm ("borel_measurable_sub",
  ``!a f g h. sigma_algebra a /\
         f IN borel_measurable a /\ g IN borel_measurable a  /\
        (!x. x IN space a ==> (h x = f x - g x)) ==> h IN borel_measurable a``,
  RW_TAC std_ss [] THEN
  MATCH_MP_TAC borel_measurable_add THEN
  Q.EXISTS_TAC `f` THEN
  Q.EXISTS_TAC `(\x. - g x)` THEN
  RW_TAC std_ss [real_sub] THEN
  MATCH_MP_TAC borel_measurable_cmul THEN
  Q.EXISTS_TAC `g` THEN Q.EXISTS_TAC `-1` THEN
  ASM_SIMP_TAC real_ss []);

val _ = hide "sigma_finite_measure";

(* SIGMA_FINITE_ALT2 *)
val sigma_finite_measure = new_definition ("sigma_finite_measure",
  ``sigma_finite_measure m =
   ?A. countable A /\ A SUBSET measurable_sets m /\
       (BIGUNION A = m_space m) /\
       (!a. a IN A ==> (measure m a <> PosInf))``);

val finite_measure = new_definition ("finite_measure",
  ``finite_measure m = sigma_finite_measure m /\
                       (measure m (m_space m) <> PosInf)``);





(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* ------------------------------------------------------------------------- *)

val measure_of_eq = store_thm ("measure_of_eq",
  ``!m f. measure_space m ==>
     (pos_fn_integral m f =
      pos_fn_integral (m_space m, measurable_sets m,
                       (\A. if A IN measurable_sets m then measure m A else 0)) f)``,
  RW_TAC std_ss [pos_fn_integral_def] THEN AP_TERM_TAC THEN
  AP_TERM_TAC THEN ABS_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  ABS_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  FULL_SIMP_TAC std_ss [IN_psfis_eq] THEN EQ_TAC THENL
  [RW_TAC std_ss [] THEN Q.EXISTS_TAC `s` THEN Q.EXISTS_TAC `a` THEN
   Q.EXISTS_TAC `x` THEN FULL_SIMP_TAC std_ss [pos_simple_fn_def] THEN
   FULL_SIMP_TAC std_ss [m_space_def, measurable_sets_def] THEN
   SIMP_TAC std_ss [pos_simple_fn_integral_def] THEN
   FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP EXTREAL_SUM_IMAGE_EQ) THEN
   CONJ_TAC THENL
   [DISJ1_TAC THEN RW_TAC std_ss [measure_def] THEN
    `(!c y. 0 <= c /\ y <> NegInf ==> Normal c * y <> NegInf)`
     by METIS_TAC [mul_not_infty] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    METIS_TAC [measure_space_def, positive_def, lte_trans, lt_infty, num_not_infty],
    ALL_TAC] THEN
   RW_TAC std_ss [measure_def],
   ALL_TAC] THEN
  RW_TAC std_ss [] THEN Q.EXISTS_TAC `s` THEN Q.EXISTS_TAC `a` THEN
  Q.EXISTS_TAC `x` THEN FULL_SIMP_TAC std_ss [pos_simple_fn_def] THEN
  FULL_SIMP_TAC std_ss [m_space_def, measurable_sets_def] THEN
  SIMP_TAC std_ss [pos_simple_fn_integral_def] THEN
  FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP EXTREAL_SUM_IMAGE_EQ) THEN
  CONJ_TAC THENL
  [DISJ1_TAC THEN RW_TAC std_ss [measure_def] THEN
   `(!c y. 0 <= c /\ y <> NegInf ==> Normal c * y <> NegInf)`
    by METIS_TAC [mul_not_infty] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
   METIS_TAC [measure_space_def, positive_def, lte_trans, lt_infty, num_not_infty],
   ALL_TAC] THEN RW_TAC std_ss [measure_def]);


(* TODO *)
val pos_fn_integral_distr' = store_thm ("pos_fn_integral_distr'",
  ``! t f M M'. measure_space M /\ measure_space M' /\
     t IN measurable (m_space M, measurable_sets M) (m_space M', measurable_sets M') /\
     f IN measurable (m_space (distr M M' t), measurable_sets (distr M M' t)) Borel /\
     (!x. 0 <= f x) ==>
     (pos_fn_integral (distr M M' t) (\x. max 0 (f x)) =
      pos_fn_integral M (\x. max 0 (f (t x))))``,
  RW_TAC std_ss [] THEN
  Q_TAC SUFF_TAC `(\f. pos_fn_integral (distr M M' t) (\x. max 0 (f x)) =
                       pos_fn_integral M (\x. max 0 (f (t x)))) f` THENL
  [SIMP_TAC std_ss [], ALL_TAC] THEN
  MATCH_MP_TAC Induct_on_Borel_functions THEN Q.EXISTS_TAC `distr M M' t` THEN
  ASM_SIMP_TAC std_ss [measure_space_distr] THEN
  CONJ_TAC THENL
  [RW_TAC std_ss [] THEN
   Q_TAC SUFF_TAC `pos_fn_integral (distr M M' t) (\x. max 0 (g x)) =
                   pos_fn_integral (distr M M' t) (\x. max 0 (f' x))` THENL
   [DISC_RW_KILL,
    MATCH_MP_TAC positive_integral_cong THEN
    ASM_SIMP_TAC std_ss [le_max1, measure_space_distr]] THEN
   ASM_SIMP_TAC std_ss [] THEN MATCH_MP_TAC positive_integral_cong THEN
   ASM_SIMP_TAC std_ss [le_max1] THEN RW_TAC std_ss [] THEN
   AP_TERM_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
   FULL_SIMP_TAC std_ss [IN_MEASURABLE, space_def, subsets_def] THEN
   SIMP_TAC std_ss [distr, m_space_def] THEN FULL_SIMP_TAC std_ss [IN_FUNSET],
   ALL_TAC] THEN
  CONJ_TAC THENL
  [RW_TAC std_ss [] THEN
   ONCE_REWRITE_TAC [METIS [extreal_max_def, indicator_fn_pos_le]
    ``!x. max 0 (indicator_fn A x) = indicator_fn A x``] THEN
   ONCE_REWRITE_TAC [METIS [ETA_AX] ``(\x. indicator_fn A x) = indicator_fn A``] THEN
   `measure_space (distr M M' t)` by METIS_TAC [measure_space_distr] THEN
   ASM_SIMP_TAC std_ss [pos_fn_integral_indicator] THEN
   ASM_SIMP_TAC std_ss [distr, measure_def] THEN
   Q_TAC SUFF_TAC `PREIMAGE t A INTER m_space M IN measurable_sets M` THENL
   [DISCH_TAC,
    FULL_SIMP_TAC std_ss [IN_MEASURABLE, space_def, subsets_def] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN FULL_SIMP_TAC std_ss [distr, measurable_sets_def]] THEN
   ASM_SIMP_TAC std_ss [GSYM pos_fn_integral_indicator] THEN
   MATCH_MP_TAC positive_integral_cong THEN ASM_SIMP_TAC std_ss [indicator_fn_pos_le] THEN
   SIMP_TAC std_ss [indicator_fn_def, GSPECIFICATION, IN_INTER] THEN
   RW_TAC std_ss [IN_PREIMAGE],
   ALL_TAC] THEN
  CONJ_TAC THENL
  [RW_TAC std_ss [] THEN
   Q_TAC SUFF_TAC `pos_fn_integral (distr M M' t) (\x. max 0 (c * f' x)) =
                   c * pos_fn_integral (distr M M' t) (\x. max 0 (f' x))` THENL
   [DISC_RW_KILL,
    MATCH_MP_TAC pos_fn_integral_cmult THEN ASM_SIMP_TAC std_ss [measure_space_distr]] THEN
   ASM_REWRITE_TAC [] THEN ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
   Q_TAC SUFF_TAC `pos_fn_integral M (\x. max 0 (c * (\x. f' (t x)) x)) =
                   c * pos_fn_integral M (\x. max 0 ((\x. f' (t x)) x))` THENL
   [SIMP_TAC std_ss [], ALL_TAC] THEN
   MATCH_MP_TAC pos_fn_integral_cmult THEN ASM_SIMP_TAC std_ss [] THEN
   FULL_SIMP_TAC std_ss [IN_MEASURABLE, space_def, subsets_def] THEN
   CONJ_TAC THENL [EVAL_TAC THEN SRW_TAC[] [IN_DEF,IN_FUNSET], ALL_TAC] THEN
   RW_TAC std_ss [] THEN
   Q_TAC SUFF_TAC `PREIMAGE (\x. f' (t x)) s = PREIMAGE t {x | f' (x) IN s}` THENL
   [SIMP_TAC std_ss [] THEN DISC_RW_KILL,
    SIMP_TAC std_ss [PREIMAGE_def, GSPECIFICATION]] THEN
   Q_TAC SUFF_TAC `PREIMAGE t {x | f' x IN s} INTER m_space M =
                   PREIMAGE t (PREIMAGE f' s INTER m_space M') INTER m_space M` THENL
   [SIMP_TAC std_ss [] THEN DISC_RW_KILL,
    SIMP_TAC std_ss [PREIMAGE_def] THEN
    SIMP_TAC std_ss [INTER_DEF, IN_INTER, GSPECIFICATION] THEN
    FULL_SIMP_TAC std_ss [IN_FUNSET] THEN
    SIMP_TAC std_ss [EXTENSION, GSPECIFICATION] THEN GEN_TAC THEN EQ_TAC THEN
    RW_TAC std_ss []] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   FULL_SIMP_TAC std_ss [distr, measurable_sets_def, m_space_def],
   ALL_TAC] THEN

  CONJ_TAC THENL
  [RW_TAC std_ss [] THEN
   Q_TAC SUFF_TAC `!x. max 0 (f' x + g x) = max 0 (f' x) + max 0 (g x)` THENL
   [DISC_RW_KILL,
    ASM_SIMP_TAC std_ss [extreal_max_def] THEN GEN_TAC THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC std_ss [] THEN
    METIS_TAC [le_add]] THEN
   Q_TAC SUFF_TAC `pos_fn_integral (distr M M' t) (\x. (\x. max 0 (f' x)) x + (\x. max 0 (g x)) x) =
                   pos_fn_integral (distr M M' t) (\x. max 0 (f' x)) +
                   pos_fn_integral (distr M M' t) (\x. max 0 (g x))` THENL
   [SIMP_TAC std_ss [] THEN DISC_RW_KILL,
    MATCH_MP_TAC pos_fn_integral_add THEN ASM_SIMP_TAC std_ss [le_max1, measure_space_distr] THEN
    CONJ_TAC THENL
    [Q_TAC SUFF_TAC `(\x. max ((\x. 0) x) ((\x. f' x) x)) IN
      measurable (m_space (distr M M' t),measurable_sets (distr M M' t)) Borel` THENL
     [SIMP_TAC std_ss [], ALL_TAC] THEN
     MATCH_MP_TAC IN_MEASURABLE_BOREL_MAX THEN
     `(\x. 0) IN measurable (m_space M',measurable_sets M') Borel` by
        (MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST THEN
         METIS_TAC [measure_space_def]) THEN
     ONCE_REWRITE_TAC [METIS [ETA_AX] ``(\x. f' x) = f'``] THEN
     FULL_SIMP_TAC std_ss [distr, m_space_def, measurable_sets_def] THEN
     METIS_TAC [measure_space_def],
     ALL_TAC] THEN
    Q_TAC SUFF_TAC `(\x. max ((\x. 0) x) ((\x. g x) x)) IN
      measurable (m_space (distr M M' t),measurable_sets (distr M M' t)) Borel` THENL
    [SIMP_TAC std_ss [], ALL_TAC] THEN
    MATCH_MP_TAC IN_MEASURABLE_BOREL_MAX THEN
    `(\x. 0) IN measurable (m_space M',measurable_sets M') Borel` by
       (MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST THEN
        METIS_TAC [measure_space_def]) THEN
    ONCE_REWRITE_TAC [METIS [ETA_AX] ``(\x. g x) = g``] THEN
    FULL_SIMP_TAC std_ss [distr, m_space_def, measurable_sets_def] THEN
    METIS_TAC [measure_space_def]] THEN
   Q_TAC SUFF_TAC
   `pos_fn_integral M (\x. max 0 (f' (t x))) +
    pos_fn_integral M (\x. max 0 (g (t x))) =
    pos_fn_integral M (\x. ((\x. max 0 (f' (t x))) x) + ((\x. max 0 (g (t x))) x))` THENL
   [ASM_SIMP_TAC std_ss [], ALL_TAC] THEN
   MATCH_MP_TAC (GSYM pos_fn_integral_add) THEN ASM_SIMP_TAC std_ss [le_max1] THEN
   CONJ_TAC THENL
   [Q_TAC SUFF_TAC `(\x. max ((\x. 0) x) ((\x. f' (t x)) x)) IN
      measurable (m_space M,measurable_sets M) Borel` THENL
    [SIMP_TAC std_ss [], ALL_TAC] THEN
    MATCH_MP_TAC IN_MEASURABLE_BOREL_MAX THEN
    `(\x. 0) IN measurable (m_space M,measurable_sets M) Borel` by
       (MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST THEN
        METIS_TAC [measure_space_def]) THEN
    CONJ_TAC THENL [METIS_TAC [measure_space_def], ALL_TAC] THEN
    FULL_SIMP_TAC std_ss [IN_MEASURABLE, distr, m_space_def, measurable_sets_def] THEN
    CONJ_TAC THENL [EVAL_TAC THEN SRW_TAC[] [IN_DEF,IN_FUNSET], ALL_TAC] THEN
    FULL_SIMP_TAC std_ss [space_def, subsets_def] THEN RW_TAC std_ss [] THEN
    Q_TAC SUFF_TAC `PREIMAGE (\x. f' (t x)) s = PREIMAGE t {x | f' (x) IN s}` THENL
    [SIMP_TAC std_ss [] THEN DISC_RW_KILL,
     SIMP_TAC std_ss [PREIMAGE_def, GSPECIFICATION]] THEN
    Q_TAC SUFF_TAC `PREIMAGE t {x | f' x IN s} INTER m_space M =
                    PREIMAGE t (PREIMAGE f' s INTER m_space M') INTER m_space M` THENL
    [SIMP_TAC std_ss [] THEN DISC_RW_KILL,
     SIMP_TAC std_ss [PREIMAGE_def] THEN
     SIMP_TAC std_ss [INTER_DEF, IN_INTER, GSPECIFICATION] THEN
     FULL_SIMP_TAC std_ss [IN_FUNSET] THEN
     SIMP_TAC std_ss [EXTENSION, GSPECIFICATION] THEN GEN_TAC THEN EQ_TAC THEN
     RW_TAC std_ss []] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC std_ss [],
    ALL_TAC] THEN
   Q_TAC SUFF_TAC `(\x. max ((\x. 0) x) ((\x. g (t x)) x)) IN
      measurable (m_space M,measurable_sets M) Borel` THENL
   [SIMP_TAC std_ss [], ALL_TAC] THEN
   MATCH_MP_TAC IN_MEASURABLE_BOREL_MAX THEN
   `(\x. 0) IN measurable (m_space M,measurable_sets M) Borel` by
      (MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST THEN
       METIS_TAC [measure_space_def]) THEN
   CONJ_TAC THENL [METIS_TAC [measure_space_def], ALL_TAC] THEN
   FULL_SIMP_TAC std_ss [IN_MEASURABLE, distr, m_space_def, measurable_sets_def] THEN
   CONJ_TAC THENL [EVAL_TAC THEN SRW_TAC[] [IN_DEF,IN_FUNSET], ALL_TAC] THEN
   FULL_SIMP_TAC std_ss [space_def, subsets_def] THEN RW_TAC std_ss [] THEN
   Q_TAC SUFF_TAC `PREIMAGE (\x. g (t x)) s = PREIMAGE t {x | g (x) IN s}` THENL
   [SIMP_TAC std_ss [] THEN DISC_RW_KILL,
    SIMP_TAC std_ss [PREIMAGE_def, GSPECIFICATION]] THEN
   Q_TAC SUFF_TAC `PREIMAGE t {x | g x IN s} INTER m_space M =
                   PREIMAGE t (PREIMAGE g s INTER m_space M') INTER m_space M` THENL
   [SIMP_TAC std_ss [] THEN DISC_RW_KILL,
    SIMP_TAC std_ss [PREIMAGE_def] THEN
    SIMP_TAC std_ss [INTER_DEF, IN_INTER, GSPECIFICATION] THEN
    FULL_SIMP_TAC std_ss [IN_FUNSET] THEN
    SIMP_TAC std_ss [EXTENSION, GSPECIFICATION] THEN GEN_TAC THEN EQ_TAC THEN
    RW_TAC std_ss []] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC std_ss [],
   ALL_TAC] THEN
  RW_TAC std_ss [] THEN

  Q_TAC SUFF_TAC `pos_fn_integral (distr M M' t)
       (\x. max 0 (sup (IMAGE (\i. u i x) univ(:num)))) =
      sup (IMAGE (\i. pos_fn_integral (distr M M' t) ((\i x. max 0 (u i x)) i)) UNIV)` THENL
  [DISC_RW_KILL,
   MATCH_MP_TAC lebesgue_monotone_convergence THEN
   ASM_SIMP_TAC std_ss [measure_space_distr, le_max1] THEN
   ASM_SIMP_TAC std_ss [m_space_def, measurable_sets_def, distr] THEN
   CONJ_TAC THENL
   [GEN_TAC THEN
    Q_TAC SUFF_TAC `!x. max 0 (u i x) = max ((\x. 0) x) ((\x. u i x) x)` THENL
    [DISC_RW_KILL, SIMP_TAC std_ss []] THEN
    MATCH_MP_TAC IN_MEASURABLE_BOREL_MAX THEN
    `(\x. 0) IN measurable (m_space M',measurable_sets M') Borel` by
     (MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST THEN
      METIS_TAC [measure_space_def]) THEN
    ONCE_REWRITE_TAC [METIS [ETA_AX] ``(\x. u i x) = u i``] THEN
    METIS_TAC [measure_space_def, distr, m_space_def, measurable_sets_def], ALL_TAC] THEN
   ASM_SIMP_TAC std_ss [extreal_max_def] THEN
   GEN_TAC THEN ASM_CASES_TAC ``!i:num. u i (x:'b) = 0`` THENL
   [ASM_SIMP_TAC std_ss [IMAGE_DEF, IN_UNIV] THEN
    DISCH_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC std_ss [] THEN
    POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC [MONO_NOT_EQ] THEN
    RW_TAC std_ss [le_sup] THEN POP_ASSUM (MATCH_MP_TAC) THEN
    ONCE_REWRITE_TAC [GSYM SPECIFICATION] THEN SIMP_TAC std_ss [GSPECIFICATION] THEN
    ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN METIS_TAC [],
    ALL_TAC] THEN
   FULL_SIMP_TAC std_ss [] THEN RW_TAC std_ss [] THEN
   UNDISCH_TAC ``~(0 <= sup (IMAGE (\i. u i (x:'b)) univ(:num)))`` THEN
   ONCE_REWRITE_TAC [MONO_NOT_EQ] THEN RW_TAC std_ss [le_lt] THEN
   SIMP_TAC std_ss [GSYM sup_lt] THEN Q.EXISTS_TAC `u i x` THEN
   CONJ_TAC THENL [ALL_TAC, METIS_TAC [le_lt]] THEN
   ONCE_REWRITE_TAC [GSYM SPECIFICATION] THEN
   SIMP_TAC std_ss [IN_IMAGE, IN_UNIV] THEN METIS_TAC []] THEN
  ASM_SIMP_TAC std_ss [] THEN

  Q_TAC SUFF_TAC
   `sup (IMAGE (\i. pos_fn_integral M ((\i x. max 0 (u i (t x))) i)) univ(:num)) =
    pos_fn_integral M (\x. max 0 (sup (IMAGE (\i. u i (t x)) univ(:num))))` THENL
  [SIMP_TAC std_ss [], ALL_TAC] THEN
  MATCH_MP_TAC (GSYM lebesgue_monotone_convergence) THEN
  ASM_SIMP_TAC std_ss [le_max1] THEN CONJ_TAC THENL
  [GEN_TAC THEN
   Q_TAC SUFF_TAC `!x. max 0 (u i (t x)) = max ((\x. 0) x) ((\x. u i (t x)) x)` THENL
   [DISC_RW_KILL, SIMP_TAC std_ss []] THEN
   MATCH_MP_TAC IN_MEASURABLE_BOREL_MAX THEN
   `(\x. 0) IN measurable (m_space M,measurable_sets M) Borel` by
    (MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST THEN
     METIS_TAC [measure_space_def]) THEN
   CONJ_TAC THENL [METIS_TAC [measure_space_def], ALL_TAC] THEN
   FULL_SIMP_TAC std_ss [IN_MEASURABLE, distr, m_space_def, measurable_sets_def] THEN
   CONJ_TAC THENL [EVAL_TAC THEN SRW_TAC[] [IN_DEF,IN_FUNSET], ALL_TAC] THEN
   FULL_SIMP_TAC std_ss [space_def, subsets_def] THEN RW_TAC std_ss [] THEN
   Q_TAC SUFF_TAC `PREIMAGE (\x. u i (t x)) s = PREIMAGE t {x | u i (x) IN s}` THENL
   [SIMP_TAC std_ss [] THEN DISC_RW_KILL,
    SIMP_TAC std_ss [PREIMAGE_def, GSPECIFICATION]] THEN
   Q_TAC SUFF_TAC `PREIMAGE t {x | u i x IN s} INTER m_space M =
                   PREIMAGE t (PREIMAGE (u i) s INTER m_space M') INTER m_space M` THENL
   [SIMP_TAC std_ss [] THEN DISC_RW_KILL,
    SIMP_TAC std_ss [PREIMAGE_def] THEN
    SIMP_TAC std_ss [INTER_DEF, IN_INTER, GSPECIFICATION] THEN
    FULL_SIMP_TAC std_ss [IN_FUNSET] THEN
    SIMP_TAC std_ss [EXTENSION, GSPECIFICATION] THEN GEN_TAC THEN EQ_TAC THEN
    RW_TAC std_ss []] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC std_ss [],
   ALL_TAC] THEN
  ASM_SIMP_TAC std_ss [extreal_max_def] THEN GEN_TAC THEN DISCH_TAC THEN
  ASM_CASES_TAC ``!i:num. u i ((t:'a->'b) x) = 0`` THENL
  [ASM_SIMP_TAC std_ss [IMAGE_DEF, IN_UNIV] THEN
   COND_CASES_TAC THEN ASM_SIMP_TAC std_ss [] THEN
   POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC [MONO_NOT_EQ] THEN
   RW_TAC std_ss [le_sup] THEN POP_ASSUM (MATCH_MP_TAC) THEN
   ONCE_REWRITE_TAC [GSYM SPECIFICATION] THEN SIMP_TAC std_ss [GSPECIFICATION] THEN
   ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN METIS_TAC [],
   ALL_TAC] THEN
  FULL_SIMP_TAC std_ss [] THEN RW_TAC std_ss [] THEN
  UNDISCH_TAC ``~(0 <= sup (IMAGE (\i. u i ((t:'a->'b) x)) univ(:num)))`` THEN
  ONCE_REWRITE_TAC [MONO_NOT_EQ] THEN RW_TAC std_ss [le_lt] THEN
  SIMP_TAC std_ss [GSYM sup_lt] THEN Q.EXISTS_TAC `u i (t x)` THEN
  CONJ_TAC THENL [ALL_TAC, METIS_TAC [le_lt]] THEN
  ONCE_REWRITE_TAC [GSYM SPECIFICATION] THEN
  SIMP_TAC std_ss [IN_IMAGE, IN_UNIV] THEN METIS_TAC []);

(* measure_space_borel_trivial *)
val measure_space_borel = store_thm ("measure_space_borel",
  ``measure_space (space borel,subsets borel,(\x. 0))``,
  RW_TAC std_ss [measure_space_def, m_space_def, measurable_sets_def] THENL
  [SIMP_TAC std_ss [SPACE, sigma_algebra_borel],
   SIMP_TAC std_ss [positive_def, measure_def, measurable_sets_def, le_refl],
   ALL_TAC] THEN
  SIMP_TAC std_ss [countably_additive_alt_eq, o_DEF, suminf_0]);

val lebesgue_real_affine = store_thm
  ("lebesgue_real_affine",
  ``!c t. c <> 0 ==>
      (measure_of lborel = measure_of (density
         (distr lborel (space borel, subsets borel, (\x. 0)) (\x. t + c * x))
                       (\z. Normal (abs c))))``,
  RW_TAC std_ss [] THEN MATCH_MP_TAC lborel_eqI THEN
  CONJ_TAC THENL
  [ALL_TAC,
   CONJ_TAC THENL [ALL_TAC, METIS_TAC [density, distr, measurable_sets_def]] THEN
   MATCH_MP_TAC measure_space_density THEN CONJ_TAC THENL
   [ALL_TAC, MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST THEN
    Q.EXISTS_TAC `Normal (abs c)` THEN
    SIMP_TAC std_ss [m_space_def, measurable_sets_def, distr] THEN
    SIMP_TAC std_ss [SPACE, sigma_algebra_borel]] THEN
   MATCH_MP_TAC measure_space_distr THEN
   SIMP_TAC std_ss [measure_space_borel, measure_space_lborel] THEN
   SIMP_TAC std_ss [m_space_def, measurable_sets_def, SPACE] THEN
    SIMP_TAC std_ss [GSYM borel_measurable] THEN MATCH_MP_TAC borel_measurable_add THEN
    Q.EXISTS_TAC `(\x. t)` THEN Q.EXISTS_TAC `(\x. c * x)` THEN
    CONJ_TAC THENL [METIS_TAC [lborel, GSYM space_borel, m_space_def,
      measurable_sets_def, sigma_algebra_borel, SPACE], ALL_TAC] THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC borel_measurable_const THEN
     METIS_TAC [lborel, GSYM space_borel, m_space_def,
      measurable_sets_def, sigma_algebra_borel, SPACE],
     ALL_TAC] THEN
    SIMP_TAC std_ss [] THEN MATCH_MP_TAC borel_measurable_cmul THEN
    Q.EXISTS_TAC `(\x. x)` THEN Q.EXISTS_TAC `c` THEN
    ASM_SIMP_TAC std_ss [] THEN
    CONJ_TAC THENL [METIS_TAC [lborel, GSYM space_borel, m_space_def,
      measurable_sets_def, sigma_algebra_borel, SPACE], ALL_TAC] THEN
    Q_TAC SUFF_TAC `(\x:real. x) = I` THENL
    [DISC_RW_KILL, SIMP_TAC std_ss [FUN_EQ_THM]] THEN
    SIMP_TAC std_ss [borel_measurable, m_space_def, measurable_sets_def, SPACE, lborel] THEN
    SIMP_TAC std_ss [GSYM space_borel, SPACE] THEN MATCH_MP_TAC MEASURABLE_I THEN
    SIMP_TAC std_ss [sigma_algebra_borel]] THEN
  RW_TAC std_ss [] THEN ASM_CASES_TAC ``0 < c:real`` THENL
  [Q_TAC SUFF_TAC `PREIMAGE (\x. t + c * x) (interval [a,b]) =
                   interval [(a - t) / c, (b - t) / c]` THENL
   [SIMP_TAC std_ss [] THEN DISCH_TAC,
    SIMP_TAC std_ss [PREIMAGE_def, interval] THEN
    SIMP_TAC std_ss [EXTENSION, GSPECIFICATION] THEN
    ASM_SIMP_TAC real_ss [REAL_LE_RDIV_EQ, REAL_LE_LDIV_EQ] THEN
    REAL_ARITH_TAC] THEN
   SIMP_TAC std_ss [density, measure_def] THEN
   `interval [(a,b)] IN measurable_sets
    (distr lborel (space borel,subsets borel,(\x. 0)) (\x. t + c * x))` by
    METIS_TAC [borel_closed, CLOSED_INTERVAL, distr, measurable_sets_def] THEN
   ASM_SIMP_TAC std_ss [] THEN

   Q_TAC SUFF_TAC `pos_fn_integral
    (distr lborel (space borel,subsets borel,(\x. 0)) (\x. t + c * x))
    (\z. max 0 ((\z. Normal (abs c) * indicator_fn (interval [(a,b)]) z) z)) =
     pos_fn_integral lborel
    (\z. max 0 ((\z. Normal (abs c) * indicator_fn (interval [(a,b)]) z)
         ((\x. t + c * x) z)))` THENL
    [SIMP_TAC std_ss [] THEN DISC_RW_KILL,
     MATCH_MP_TAC pos_fn_integral_distr' THEN ASM_SIMP_TAC std_ss [measure_space_lborel] THEN
     SIMP_TAC std_ss [m_space_def, measurable_sets_def, lborel, distr, GSYM space_borel] THEN
     SIMP_TAC std_ss [measure_space_borel] THEN CONJ_TAC THENL
     [Q_TAC SUFF_TAC `(\x. t + c * x) IN
       measurable (m_space (space borel,subsets borel, (\x. 0)),
           measurable_sets (space borel,subsets borel, (\x. 0))) borel` THENL
      [SIMP_TAC std_ss [SPACE, m_space_def, measurable_sets_def], ALL_TAC] THEN
      REWRITE_TAC [GSYM borel_measurable] THEN MATCH_MP_TAC borel_measurable_add THEN
      Q.EXISTS_TAC `(\x. t)` THEN Q.EXISTS_TAC `(\x. c * x)` THEN
      CONJ_TAC THENL
      [METIS_TAC [m_space_def, measurable_sets_def, SPACE, sigma_algebra_borel],
       ALL_TAC] THEN
      CONJ_TAC THENL
      [MATCH_MP_TAC borel_measurable_const THEN
       METIS_TAC [m_space_def, measurable_sets_def, SPACE, sigma_algebra_borel],
       ALL_TAC] THEN
      CONJ_TAC THENL
      [MATCH_MP_TAC borel_measurable_cmul THEN Q.EXISTS_TAC `(\x. x)` THEN
       Q.EXISTS_TAC `c` THEN SIMP_TAC std_ss [] THEN
       CONJ_TAC THENL
       [METIS_TAC [m_space_def, measurable_sets_def, SPACE, sigma_algebra_borel],
        ALL_TAC] THEN
       Q_TAC SUFF_TAC `(\x:real. x) = I` THENL
       [DISC_RW_KILL, SIMP_TAC std_ss [FUN_EQ_THM]] THEN
       SIMP_TAC std_ss [borel_measurable, m_space_def, measurable_sets_def, SPACE] THEN
       MATCH_MP_TAC MEASURABLE_I THEN SIMP_TAC std_ss [sigma_algebra_borel],
       ALL_TAC] THEN
      SIMP_TAC std_ss [], ALL_TAC] THEN
   CONJ_TAC THENL
   [ALL_TAC,
    GEN_TAC THEN MATCH_MP_TAC le_mul THEN
    ASM_SIMP_TAC std_ss [indicator_fn_pos_le, extreal_of_num_def] THEN
    ASM_SIMP_TAC std_ss [extreal_le_def, abs, REAL_LE_LT]] THEN
   Q_TAC SUFF_TAC `(\z. (\z. Normal (abs c)) z * (\z. indicator_fn (interval [(a,b)]) z) z) IN
                      measurable (m_space (space borel,subsets borel, (\x. 0)),
                      measurable_sets (space borel,subsets borel, (\x. 0))) Borel` THENL
   [SIMP_TAC std_ss [m_space_def, measurable_sets_def], ALL_TAC] THEN
   MATCH_MP_TAC IN_MEASURABLE_BOREL_TIMES THEN Q.EXISTS_TAC `(\z. Normal (abs c))` THEN
   Q.EXISTS_TAC `(\z. indicator_fn (interval [(a,b)]) z)` THEN
   ASM_SIMP_TAC std_ss [measure_space_borel] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST THEN Q.EXISTS_TAC `Normal (abs c)` THEN
    SIMP_TAC std_ss [m_space_def, measurable_sets_def, sigma_algebra_borel, SPACE],
    ALL_TAC] THEN
   MATCH_MP_TAC IN_MEASURABLE_BOREL_INDICATOR THEN
   Q.EXISTS_TAC `(interval [(a,b)])` THEN
   ASM_SIMP_TAC std_ss [m_space_def, measurable_sets_def, sigma_algebra_borel, SPACE] THEN
   METIS_TAC [borel_closed, CLOSED_INTERVAL]] THEN

   Q_TAC SUFF_TAC `(\z. max 0
          (Normal (abs c) * indicator_fn (interval [(a,b)]) (t + c * z))) =
     (\z. (Normal (abs c) * indicator_fn (interval [(a,b)]) (t + c * z)))` THENL
   [DISC_RW_KILL,
    SIMP_TAC std_ss [FUN_EQ_THM, extreal_max_def] THEN GEN_TAC THEN
    Q_TAC SUFF_TAC `0 <= Normal (abs c) * indicator_fn (interval [(a,b)]) (t + c * z)` THENL
    [METIS_TAC [], ALL_TAC] THEN
    MATCH_MP_TAC le_mul THEN
    ASM_SIMP_TAC std_ss [indicator_fn_pos_le, extreal_of_num_def] THEN
    ASM_SIMP_TAC std_ss [extreal_le_def, abs, REAL_LE_LT]] THEN
   Q_TAC SUFF_TAC `pos_fn_integral lborel
    (\z. Normal (abs c) * (\z. indicator_fn (interval [(a,b)]) (t + c * z)) z) =
         Normal (abs c) * pos_fn_integral lborel
    (\z. indicator_fn (interval [(a,b)]) (t + c * z))` THENL
   [SIMP_TAC std_ss [] THEN DISC_RW_KILL,
    MATCH_MP_TAC pos_fn_integral_cmul THEN
    SIMP_TAC std_ss [ABS_POS, measure_space_lborel, indicator_fn_pos_le]] THEN
   Q_TAC SUFF_TAC `(\z. indicator_fn (interval [(a,b)]) (t + c * z)) =
                   (\z. indicator_fn (interval [((a - t) / c,(b - t) / c)]) z)` THENL
   [DISC_RW_KILL,
    SIMP_TAC std_ss [FUN_EQ_THM, indicator_fn_def] THEN
    RULE_ASSUM_TAC (ONCE_REWRITE_RULE [EQ_SYM_EQ]) THEN
    ASM_SIMP_TAC real_ss [IN_INTERVAL, REAL_LE_RDIV_EQ, REAL_LE_LDIV_EQ] THEN
    ONCE_REWRITE_TAC [REAL_ARITH ``a <= t + c * z /\ t + c * z <= b:real =
                                   a - t <= z * c /\ z * c <= b - t:real``] THEN
    SIMP_TAC std_ss []] THEN
   ONCE_REWRITE_TAC [METIS [ETA_AX] ``(\x. indicator_fn A x) = (indicator_fn A)``] THEN
   Q_TAC SUFF_TAC `(interval [((a - t) / c,(b - t) / c)]) IN measurable_sets lborel` THENL
   [DISCH_TAC,
    METIS_TAC [lborel, measurable_sets_def, borel_closed, CLOSED_INTERVAL]] THEN
   `measure_space lborel` by SIMP_TAC std_ss [measure_space_lborel] THEN
   ASM_SIMP_TAC std_ss [pos_fn_integral_indicator] THEN
   SIMP_TAC std_ss [measure_def, lborel, measure_lebesgue] THEN
   Q_TAC SUFF_TAC `!n. integral (line n)
      (indicator (interval [((a - t) / c,(b - t) / c)])) =
       content (interval [((a - t) / c,(b - t) / c)] INTER line n)` THENL
   [DISC_RW_KILL,
    GEN_TAC THEN MATCH_MP_TAC INTEGRAL_UNIQUE THEN
    SIMP_TAC std_ss [has_integral_interval_cube]] THEN
   SIMP_TAC std_ss [GSYM IMAGE_DEF, GSYM sup_cmul, ABS_POS] THEN
   `0 <= c` by ASM_SIMP_TAC std_ss [REAL_LT_IMP_LE] THEN
   FULL_SIMP_TAC std_ss [GSYM ABS_REFL] THEN POP_ASSUM K_TAC THEN

   ASM_CASES_TAC ``a <= b:real`` THENL
   [ALL_TAC,
    `b <= a` by FULL_SIMP_TAC real_ss [REAL_LE_LT, REAL_NOT_LE] THEN
    POP_ASSUM (ASSUME_TAC o ONCE_REWRITE_RULE [GSYM CONTENT_EQ_0]) THEN
    `0 < inv c` by ASM_SIMP_TAC std_ss [REAL_LT_INV_EQ] THEN
    `(b - t) / c <= (a - t) / c` by
     (ASM_SIMP_TAC std_ss [real_div, REAL_LE_RMUL] THEN ASM_REAL_ARITH_TAC) THEN
    POP_ASSUM (ASSUME_TAC o ONCE_REWRITE_RULE [GSYM CONTENT_EQ_0]) THEN
    ASM_SIMP_TAC std_ss [sup_eq] THEN CONJ_TAC THENL
    [GEN_TAC THEN GEN_REWR_TAC LAND_CONV [GSYM SPECIFICATION] THEN
     SIMP_TAC std_ss [IN_IMAGE, IN_UNIV] THEN RW_TAC std_ss [] THEN
     SIMP_TAC std_ss [extreal_mul_def, REAL_LE_LT, extreal_le_def] THEN
     DISJ2_TAC THEN ONCE_REWRITE_TAC [REAL_MUL_COMM] THEN
     ASM_SIMP_TAC real_ss [GSYM REAL_EQ_RDIV_EQ, real_div] THEN
     MATCH_MP_TAC CONTENT_0_SUBSET THEN Q.EXISTS_TAC `(a - t) / c` THEN
     Q.EXISTS_TAC `(b - t) / c` THEN ASM_SIMP_TAC std_ss [] THEN
     SIMP_TAC std_ss [SUBSET_DEF, IN_INTERVAL, IN_INTER] THEN
     SIMP_TAC std_ss [real_div],
     ALL_TAC] THEN
    GEN_TAC THEN DISCH_THEN MATCH_MP_TAC THEN
    ONCE_REWRITE_TAC [GSYM SPECIFICATION] THEN SIMP_TAC std_ss [IN_IMAGE, IN_UNIV] THEN
    SIMP_TAC std_ss [line, INTER_INTERVAL, GSYM interval] THEN
    Q_TAC SUFF_TAC `!n. min ((b - t) / c) (&n) <= max ((a - t) / c) (-&n)` THENL
    [RW_TAC real_ss [GSYM CONTENT_EQ_0, extreal_mul_def], ALL_TAC] THEN
    GEN_TAC THEN SIMP_TAC std_ss [min_def, max_def] THEN
    RW_TAC real_ss [REAL_LE_LDIV_EQ, REAL_LE_RDIV_EQ] THEN
    FULL_SIMP_TAC real_ss [] THEN TRY (ASM_REAL_ARITH_TAC) THENL
    [ASM_SIMP_TAC real_ss [real_div, REAL_MUL_LINV, GSYM REAL_MUL_ASSOC] THEN
     FULL_SIMP_TAC std_ss [CONTENT_EQ_0], ALL_TAC] THEN
    UNDISCH_TAC ``~(b - t <= &n * c:real)`` THEN ONCE_REWRITE_TAC [MONO_NOT_EQ] THEN
    RW_TAC std_ss [] THEN FULL_SIMP_TAC std_ss [CONTENT_EQ_0, real_div] THEN
    `0 < inv c` by ASM_SIMP_TAC std_ss [REAL_LT_INV_EQ] THEN
    FULL_SIMP_TAC std_ss [REAL_LE_RMUL, REAL_NEG_LMUL] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN Q.EXISTS_TAC `a - t` THEN
    ASM_SIMP_TAC std_ss [] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    Q.EXISTS_TAC `-&n * c` THEN ASM_SIMP_TAC std_ss [REAL_LE_RMUL] THEN
    SIMP_TAC real_ss []] THEN

   `0 < inv c` by ASM_SIMP_TAC std_ss [REAL_LT_INV_EQ] THEN
   `(a - t) / c <= (b - t) / c` by
     (ASM_SIMP_TAC std_ss [real_div, REAL_LE_RMUL] THEN ASM_REAL_ARITH_TAC) THEN
   SIMP_TAC std_ss [sup_eq] THEN CONJ_TAC THENL
   [GEN_TAC THEN GEN_REWR_TAC LAND_CONV [GSYM SPECIFICATION] THEN
    SIMP_TAC std_ss [IN_IMAGE, IN_UNIV] THEN RW_TAC std_ss [extreal_mul_def] THEN
    SIMP_TAC std_ss [extreal_le_def, line, INTER_INTERVAL, GSYM interval] THEN
    ASM_CASES_TAC ``max ((a - t) / c) (-&n) <= min ((b - t) / c) (&n:real)`` THENL
    [ALL_TAC, FULL_SIMP_TAC std_ss [REAL_NOT_LE] THEN
     `min ((b - t) / c) (&n) <= max ((a - t) / c) (-&n)`
      by ASM_SIMP_TAC std_ss [REAL_LE_LT] THEN
     POP_ASSUM (ASSUME_TAC o ONCE_REWRITE_RULE [GSYM CONTENT_EQ_0]) THEN
     ASM_SIMP_TAC real_ss [CONTENT_CLOSED_INTERVAL] THEN ASM_REAL_ARITH_TAC] THEN
    ASM_SIMP_TAC std_ss [CONTENT_CLOSED_INTERVAL] THEN
    ONCE_REWRITE_TAC [REAL_MUL_COMM] THEN ASM_SIMP_TAC std_ss [GSYM REAL_LE_RDIV_EQ] THEN
    Q_TAC SUFF_TAC `(b - a) / c = (b - t) / c - (a - t) / c` THENL
    [DISC_RW_KILL THEN FULL_SIMP_TAC std_ss [min_def, max_def] THEN
     ASM_REAL_ARITH_TAC, ALL_TAC] THEN
    SIMP_TAC std_ss [real_sub, REAL_DIV_ADD, real_div] THEN
    REAL_ARITH_TAC,
    ALL_TAC] THEN

   GEN_TAC THEN DISCH_THEN MATCH_MP_TAC THEN ONCE_REWRITE_TAC [GSYM SPECIFICATION] THEN
   SIMP_TAC std_ss [IN_IMAGE, IN_UNIV, extreal_mul_def, extreal_11] THEN
   SIMP_TAC std_ss [line, INTER_INTERVAL, GSYM interval] THEN
   `?n. abs ((a - t) / c) <= &n` by METIS_TAC [SIMP_REAL_ARCH] THEN
   `?m. abs ((b - t) / c) <= &m` by METIS_TAC [SIMP_REAL_ARCH] THEN
   Q.EXISTS_TAC `MAX n m` THEN
   Q_TAC SUFF_TAC `max ((a - t) / c) (-&MAX n m) = (a - t) / c` THENL
   [DISC_RW_KILL,
    RW_TAC std_ss [max_def, MAX_DEF] THEN FULL_SIMP_TAC std_ss [] THENL
    [ASM_SIMP_TAC std_ss [GSYM REAL_LE_ANTISYM] THEN
     UNDISCH_TAC ``abs ((b - t) / c) <= &m:real`` THEN
     UNDISCH_TAC ``abs ((a - t) / c) <= &n:real`` THEN
     FULL_SIMP_TAC real_ss [abs, REAL_LE_RDIV_EQ, REAL_LE_LDIV_EQ] THEN
     RW_TAC std_ss [] THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
     FULL_SIMP_TAC real_ss [REAL_LE_RDIV_EQ, REAL_LE_LDIV_EQ] THEN
     RW_TAC std_ss [] THEN TRY (ASM_REAL_ARITH_TAC) THENL
     [UNDISCH_TAC `` -((a - t) / c) <= &n:real`` THEN
      GEN_REWR_TAC LAND_CONV [GSYM REAL_LE_NEG] THEN
      ASM_SIMP_TAC std_ss [REAL_LE_RDIV_EQ, REAL_NEG_NEG] THEN DISCH_TAC THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN Q.EXISTS_TAC `-&n * c` THEN
      ASM_SIMP_TAC std_ss [REAL_NEG_LMUL] THEN
     ASM_SIMP_TAC real_ss [REAL_LE_RMUL],
      ALL_TAC] THEN
     UNDISCH_TAC `` -((a - t) / c) <= &n:real`` THEN
     GEN_REWR_TAC LAND_CONV [GSYM REAL_LE_NEG] THEN
     ASM_SIMP_TAC std_ss [REAL_LE_RDIV_EQ, REAL_NEG_NEG] THEN DISCH_TAC THEN
     MATCH_MP_TAC REAL_LE_TRANS THEN Q.EXISTS_TAC `-&n * c` THEN
     ASM_SIMP_TAC std_ss [REAL_NEG_LMUL] THEN
     ASM_SIMP_TAC real_ss [REAL_LE_RMUL],
     ALL_TAC] THEN
    ASM_SIMP_TAC std_ss [GSYM REAL_LE_ANTISYM] THEN
    UNDISCH_TAC ``abs ((b - t) / c) <= &m:real`` THEN
    UNDISCH_TAC ``abs ((a - t) / c) <= &n:real`` THEN
    FULL_SIMP_TAC real_ss [abs, REAL_LE_RDIV_EQ, REAL_LE_LDIV_EQ] THEN
    RW_TAC std_ss [] THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
    FULL_SIMP_TAC real_ss [REAL_LE_RDIV_EQ, REAL_LE_LDIV_EQ] THEN
    RW_TAC std_ss [] THEN TRY (ASM_REAL_ARITH_TAC) THENL
    [UNDISCH_TAC `` -((a - t) / c) <= &n:real`` THEN
     GEN_REWR_TAC LAND_CONV [GSYM REAL_LE_NEG] THEN
     ASM_SIMP_TAC std_ss [REAL_LE_RDIV_EQ, REAL_NEG_NEG] THEN DISCH_TAC THEN
     MATCH_MP_TAC REAL_LE_TRANS THEN Q.EXISTS_TAC `-&n * c` THEN
     ASM_SIMP_TAC std_ss [REAL_NEG_LMUL] THEN
     ASM_SIMP_TAC real_ss [REAL_LE_RMUL],
     ALL_TAC] THEN
    UNDISCH_TAC `` -((a - t) / c) <= &n:real`` THEN
    GEN_REWR_TAC LAND_CONV [GSYM REAL_LE_NEG] THEN
    ASM_SIMP_TAC std_ss [REAL_LE_RDIV_EQ, REAL_NEG_NEG] THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN Q.EXISTS_TAC `-&n * c` THEN
    ASM_SIMP_TAC std_ss [REAL_NEG_LMUL] THEN
    ASM_SIMP_TAC real_ss [REAL_LE_RMUL]] THEN
   Q_TAC SUFF_TAC `min ((b - t) / c) (&MAX n m) = (b - t) / c` THENL
   [DISC_RW_KILL,
    RW_TAC std_ss [min_def, MAX_DEF] THEN FULL_SIMP_TAC std_ss [] THENL
    [UNDISCH_TAC ``~((b - t) / c <= &m:real)`` THEN
     ONCE_REWRITE_TAC [MONO_NOT_EQ] THEN RW_TAC std_ss [] THEN
     UNDISCH_TAC ``abs ((b - t) / c) <= &m:real`` THEN
     UNDISCH_TAC ``abs ((a - t) / c) <= &n:real`` THEN
     FULL_SIMP_TAC real_ss [abs, REAL_LE_RDIV_EQ, REAL_LE_LDIV_EQ] THEN
     RW_TAC std_ss [] THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
     FULL_SIMP_TAC real_ss [REAL_LE_RDIV_EQ, REAL_LE_LDIV_EQ] THEN
     RW_TAC std_ss [] THEN TRY (ASM_REAL_ARITH_TAC) THEN
     UNDISCH_TAC `` -((b - t) / c) <= &m:real`` THEN
     GEN_REWR_TAC LAND_CONV [GSYM REAL_LE_NEG] THEN
     ASM_SIMP_TAC std_ss [REAL_LE_RDIV_EQ, REAL_NEG_NEG] THEN DISCH_TAC THEN
     ASM_REAL_ARITH_TAC, ALL_TAC] THEN

    UNDISCH_TAC ``~((b - t) / c <= &n:real)`` THEN
    ONCE_REWRITE_TAC [MONO_NOT_EQ] THEN RW_TAC std_ss [] THEN
    UNDISCH_TAC ``abs ((b - t) / c) <= &m:real`` THEN
    UNDISCH_TAC ``abs ((a - t) / c) <= &n:real`` THEN
    FULL_SIMP_TAC real_ss [abs, REAL_LE_RDIV_EQ, REAL_LE_LDIV_EQ] THEN
    RW_TAC std_ss [] THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
    FULL_SIMP_TAC real_ss [REAL_LE_RDIV_EQ, REAL_LE_LDIV_EQ] THEN
    RW_TAC std_ss [] THEN TRY (ASM_REAL_ARITH_TAC) THENL
    [MATCH_MP_TAC REAL_LE_TRANS THEN Q.EXISTS_TAC `&m * c` THEN
     ASM_SIMP_TAC real_ss [REAL_LE_RMUL],
     MATCH_MP_TAC REAL_LE_TRANS THEN Q.EXISTS_TAC `&m * c` THEN
     ASM_SIMP_TAC real_ss [REAL_LE_RMUL],
     ALL_TAC] THEN
    UNDISCH_TAC `` -((a - t) / c) <= &n:real`` THEN
    GEN_REWR_TAC LAND_CONV [GSYM REAL_LE_NEG] THEN
    ASM_SIMP_TAC std_ss [REAL_LE_RDIV_EQ, REAL_NEG_NEG] THEN DISCH_TAC THEN
    UNDISCH_TAC `` -((b - t) / c) <= &m:real`` THEN
    GEN_REWR_TAC LAND_CONV [GSYM REAL_LE_NEG] THEN
    ASM_SIMP_TAC std_ss [REAL_LE_RDIV_EQ, REAL_NEG_NEG] THEN DISCH_TAC THEN
    ASM_REAL_ARITH_TAC] THEN
   ASM_SIMP_TAC std_ss [CONTENT_CLOSED_INTERVAL, real_div] THEN
   SIMP_TAC std_ss [GSYM REAL_SUB_RDISTRIB] THEN
   ONCE_REWRITE_TAC [REAL_ARITH ``a * (b * c) = b * (a * c:real)``] THEN
   ASM_SIMP_TAC real_ss [REAL_MUL_RINV] THEN REAL_ARITH_TAC,
   ALL_TAC] THEN
  Q.ABBREV_TAC `r = -c` THEN
  `0 < r` by (Q.UNABBREV_TAC `r` THEN
    ONCE_REWRITE_TAC [REAL_LT_NEG] THEN ASM_REAL_ARITH_TAC) THEN
  Q_TAC SUFF_TAC `abs c = abs r` THENL
  [DISC_RW_KILL,
   `~(0 <= c)` by ASM_REAL_ARITH_TAC THEN
   `0 <= r` by ASM_REAL_ARITH_TAC THEN
   ASM_SIMP_TAC std_ss [abs]] THEN
  Q_TAC SUFF_TAC `c = -r` THENL
  [DISC_RW_KILL,
   Q.UNABBREV_TAC `r` THEN SIMP_TAC std_ss [REAL_NEG_NEG]] THEN
  `r <> 0` by ASM_SIMP_TAC std_ss [REAL_LT_IMP_NE] THEN

  Q_TAC SUFF_TAC `PREIMAGE (\x. t + -r * x) (interval [a,b]) =
                   interval [(b - t) / -r, (a - t) / -r]` THENL
   [SIMP_TAC std_ss [] THEN DISCH_TAC,
    SIMP_TAC std_ss [PREIMAGE_def, interval] THEN
    SIMP_TAC std_ss [EXTENSION, GSPECIFICATION] THEN
    ASM_SIMP_TAC std_ss [real_div, GSYM REAL_NEG_INV] THEN
    SIMP_TAC std_ss [GSYM REAL_NEG_RMUL, REAL_NEG_LMUL, GSYM real_div] THEN
    ASM_SIMP_TAC real_ss [REAL_LE_RDIV_EQ, REAL_LE_LDIV_EQ] THEN
    REAL_ARITH_TAC] THEN

   SIMP_TAC std_ss [density, measure_def] THEN
   `interval [(a,b)] IN measurable_sets
    (distr lborel (space borel,subsets borel,(\x. 0)) (\x. t + -r * x))` by
    METIS_TAC [borel_closed, CLOSED_INTERVAL, distr, measurable_sets_def] THEN
   ASM_SIMP_TAC std_ss [] THEN

   Q_TAC SUFF_TAC `pos_fn_integral
    (distr lborel (space borel,subsets borel,(\x. 0)) (\x. t + -r * x))
    (\z. max 0 ((\z. Normal (abs r) * indicator_fn (interval [(a,b)]) z) z)) =
     pos_fn_integral lborel
    (\z. max 0 ((\z. Normal (abs r) * indicator_fn (interval [(a,b)]) z)
         ((\x. t + -r * x) z)))` THENL
    [SIMP_TAC std_ss [] THEN DISC_RW_KILL,
     MATCH_MP_TAC pos_fn_integral_distr' THEN ASM_SIMP_TAC std_ss [measure_space_lborel] THEN
     SIMP_TAC std_ss [m_space_def, measurable_sets_def, lborel, distr, GSYM space_borel] THEN
     SIMP_TAC std_ss [measure_space_borel] THEN CONJ_TAC THENL
     [Q_TAC SUFF_TAC `(\x. t + -r * x) IN
       measurable (m_space (space borel,subsets borel, (\x. 0)),
           measurable_sets (space borel,subsets borel, (\x. 0))) borel` THENL
      [SIMP_TAC std_ss [SPACE, m_space_def, measurable_sets_def], ALL_TAC] THEN
      REWRITE_TAC [GSYM borel_measurable] THEN MATCH_MP_TAC borel_measurable_add THEN
      Q.EXISTS_TAC `(\x. t)` THEN Q.EXISTS_TAC `(\x. -r * x)` THEN
      CONJ_TAC THENL
      [METIS_TAC [m_space_def, measurable_sets_def, SPACE, sigma_algebra_borel],
       ALL_TAC] THEN
      CONJ_TAC THENL
      [MATCH_MP_TAC borel_measurable_const THEN
       METIS_TAC [m_space_def, measurable_sets_def, SPACE, sigma_algebra_borel],
       ALL_TAC] THEN
      CONJ_TAC THENL
      [MATCH_MP_TAC borel_measurable_cmul THEN Q.EXISTS_TAC `(\x. x)` THEN
       Q.EXISTS_TAC `-r` THEN SIMP_TAC std_ss [] THEN
       CONJ_TAC THENL
       [METIS_TAC [m_space_def, measurable_sets_def, SPACE, sigma_algebra_borel],
        ALL_TAC] THEN
       Q_TAC SUFF_TAC `(\x:real. x) = I` THENL
       [DISC_RW_KILL, SIMP_TAC std_ss [FUN_EQ_THM]] THEN
       SIMP_TAC std_ss [borel_measurable, m_space_def, measurable_sets_def, SPACE] THEN
       MATCH_MP_TAC MEASURABLE_I THEN SIMP_TAC std_ss [sigma_algebra_borel],
       ALL_TAC] THEN
      SIMP_TAC std_ss [], ALL_TAC] THEN
   CONJ_TAC THENL
   [ALL_TAC,
    GEN_TAC THEN MATCH_MP_TAC le_mul THEN
    ASM_SIMP_TAC std_ss [indicator_fn_pos_le, extreal_of_num_def] THEN
    ASM_SIMP_TAC std_ss [extreal_le_def, abs, REAL_LE_LT]] THEN
   Q_TAC SUFF_TAC `(\z. (\z. Normal (abs r)) z * (\z. indicator_fn (interval [(a,b)]) z) z) IN
                      measurable (m_space (space borel,subsets borel, (\x. 0)),
                      measurable_sets (space borel,subsets borel, (\x. 0))) Borel` THENL
   [SIMP_TAC std_ss [m_space_def, measurable_sets_def], ALL_TAC] THEN
   MATCH_MP_TAC IN_MEASURABLE_BOREL_TIMES THEN Q.EXISTS_TAC `(\z. Normal (abs r))` THEN
   Q.EXISTS_TAC `(\z. indicator_fn (interval [(a,b)]) z)` THEN
   ASM_SIMP_TAC std_ss [measure_space_borel] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST THEN Q.EXISTS_TAC `Normal (abs r)` THEN
    SIMP_TAC std_ss [m_space_def, measurable_sets_def, sigma_algebra_borel, SPACE],
    ALL_TAC] THEN
   MATCH_MP_TAC IN_MEASURABLE_BOREL_INDICATOR THEN
   Q.EXISTS_TAC `(interval [(a,b)])` THEN
   ASM_SIMP_TAC std_ss [m_space_def, measurable_sets_def, sigma_algebra_borel, SPACE] THEN
   METIS_TAC [borel_closed, CLOSED_INTERVAL]] THEN

   Q_TAC SUFF_TAC `(\z. max 0
          (Normal (abs r) * indicator_fn (interval [(a,b)]) (t + -r * z))) =
     (\z. (Normal (abs r) * indicator_fn (interval [(a,b)]) (t + -r * z)))` THENL
   [DISC_RW_KILL,
    SIMP_TAC std_ss [FUN_EQ_THM, extreal_max_def] THEN GEN_TAC THEN
    Q_TAC SUFF_TAC `0 <= Normal (abs r) * indicator_fn (interval [(a,b)]) (t + -r * z)` THENL
    [METIS_TAC [], ALL_TAC] THEN
    MATCH_MP_TAC le_mul THEN
    ASM_SIMP_TAC std_ss [indicator_fn_pos_le, extreal_of_num_def] THEN
    ASM_SIMP_TAC std_ss [extreal_le_def, abs, REAL_LE_LT]] THEN

   Q_TAC SUFF_TAC `pos_fn_integral lborel
    (\z. Normal (abs r) * (\z. indicator_fn (interval [(a,b)]) (t + -r * z)) z) =
         Normal (abs r) * pos_fn_integral lborel
    (\z. indicator_fn (interval [(a,b)]) (t + -r * z))` THENL
   [SIMP_TAC std_ss [] THEN DISC_RW_KILL,
    MATCH_MP_TAC pos_fn_integral_cmul THEN
    SIMP_TAC std_ss [ABS_POS, measure_space_lborel, indicator_fn_pos_le]] THEN
   Q_TAC SUFF_TAC `(\z. indicator_fn (interval [(a,b)]) (t + -r * z)) =
                   (\z. indicator_fn (interval [((b - t) / -r,(a - t) / -r)]) z)` THENL
   [DISC_RW_KILL,
    SIMP_TAC std_ss [FUN_EQ_THM, indicator_fn_def] THEN
    RULE_ASSUM_TAC (ONCE_REWRITE_RULE [EQ_SYM_EQ]) THEN
    SIMP_TAC real_ss [IN_INTERVAL] THEN
    ONCE_REWRITE_TAC [real_div] THEN
    `inv (-r) = -inv r` by METIS_TAC [REAL_NEG_INV] THEN
    POP_ASSUM (fn th => REWRITE_TAC [th]) THEN
    SIMP_TAC std_ss [GSYM REAL_NEG_RMUL, REAL_NEG_LMUL, GSYM real_div] THEN
    ASM_SIMP_TAC real_ss [REAL_LE_RDIV_EQ, REAL_LE_LDIV_EQ] THEN GEN_TAC THEN
    ONCE_REWRITE_TAC [REAL_ARITH ``a <= t + c * z /\ t + c * z <= b:real =
                                   t - b <= -(z * c) /\ -(z * c) <= t - a:real``] THEN
    SIMP_TAC std_ss []] THEN
   ONCE_REWRITE_TAC [METIS [ETA_AX] ``(\x. indicator_fn A x) = (indicator_fn A)``] THEN
   Q_TAC SUFF_TAC `(interval [((b - t) / -r,(a - t) / -r)]) IN measurable_sets lborel` THENL
   [DISCH_TAC,
    METIS_TAC [lborel, measurable_sets_def, borel_closed, CLOSED_INTERVAL]] THEN
   `measure_space lborel` by SIMP_TAC std_ss [measure_space_lborel] THEN
   ASM_SIMP_TAC std_ss [pos_fn_integral_indicator] THEN
   SIMP_TAC std_ss [measure_def, lborel, measure_lebesgue] THEN
   Q_TAC SUFF_TAC `!n. integral (line n)
      (indicator (interval [((b - t) / -r,(a - t) / -r)])) =
       content (interval [((b - t) / -r,(a - t) / -r)] INTER line n)` THENL
   [DISC_RW_KILL,
    GEN_TAC THEN MATCH_MP_TAC INTEGRAL_UNIQUE THEN
    SIMP_TAC std_ss [has_integral_interval_cube]] THEN
   SIMP_TAC std_ss [GSYM IMAGE_DEF, GSYM sup_cmul, ABS_POS] THEN
   `0 <= r` by ASM_SIMP_TAC std_ss [REAL_LT_IMP_LE] THEN
   FULL_SIMP_TAC std_ss [GSYM ABS_REFL] THEN POP_ASSUM K_TAC THEN

   ASM_CASES_TAC ``a <= b:real`` THENL
   [ALL_TAC,
    `b <= a` by FULL_SIMP_TAC real_ss [REAL_LE_LT, REAL_NOT_LE] THEN
    POP_ASSUM (ASSUME_TAC o ONCE_REWRITE_RULE [GSYM CONTENT_EQ_0]) THEN
    ONCE_REWRITE_TAC [real_div] THEN
    `inv (-r) = -inv r` by METIS_TAC [REAL_NEG_INV] THEN
    POP_ASSUM (fn th => REWRITE_TAC [th]) THEN
    SIMP_TAC std_ss [GSYM REAL_NEG_RMUL, REAL_NEG_LMUL, GSYM real_div] THEN
    `0 < inv r` by ASM_SIMP_TAC std_ss [REAL_LT_INV_EQ] THEN
    `-(a - t) / r <= -(b - t) / r` by
     (ASM_SIMP_TAC std_ss [real_div, REAL_LE_RMUL] THEN ASM_REAL_ARITH_TAC) THEN
    POP_ASSUM (ASSUME_TAC o ONCE_REWRITE_RULE [GSYM CONTENT_EQ_0]) THEN
    ASM_SIMP_TAC std_ss [sup_eq] THEN CONJ_TAC THENL
    [GEN_TAC THEN GEN_REWR_TAC LAND_CONV [GSYM SPECIFICATION] THEN
     SIMP_TAC std_ss [IN_IMAGE, IN_UNIV] THEN RW_TAC std_ss [] THEN
     SIMP_TAC std_ss [extreal_mul_def, REAL_LE_LT, extreal_le_def] THEN
     DISJ2_TAC THEN ONCE_REWRITE_TAC [REAL_MUL_COMM] THEN
     ASM_SIMP_TAC real_ss [GSYM REAL_EQ_RDIV_EQ, real_div] THEN
     MATCH_MP_TAC CONTENT_0_SUBSET THEN Q.EXISTS_TAC `-(b - t) / r` THEN
     Q.EXISTS_TAC `-(a - t) / r` THEN ASM_SIMP_TAC std_ss [] THEN
     SIMP_TAC std_ss [SUBSET_DEF, IN_INTERVAL, IN_INTER] THEN
     SIMP_TAC std_ss [real_div, REAL_NEG_LMUL],
     ALL_TAC] THEN
    GEN_TAC THEN DISCH_THEN MATCH_MP_TAC THEN
    ONCE_REWRITE_TAC [GSYM SPECIFICATION] THEN SIMP_TAC std_ss [IN_IMAGE, IN_UNIV] THEN
    SIMP_TAC std_ss [line, INTER_INTERVAL, GSYM interval] THEN
    Q_TAC SUFF_TAC `!n. min (-(a - t) / r) (&n) <= max (-(b - t) / r) (-&n)` THENL
    [RW_TAC real_ss [GSYM CONTENT_EQ_0, extreal_mul_def], ALL_TAC] THEN
    GEN_TAC THEN SIMP_TAC std_ss [min_def, max_def] THEN
    RW_TAC real_ss [REAL_LE_LDIV_EQ, REAL_LE_RDIV_EQ] THEN
    FULL_SIMP_TAC real_ss [] THEN TRY (ASM_REAL_ARITH_TAC) THENL
    [ASM_SIMP_TAC real_ss [real_div, REAL_MUL_LINV, GSYM REAL_MUL_ASSOC] THEN
     FULL_SIMP_TAC std_ss [CONTENT_EQ_0] THEN ASM_REAL_ARITH_TAC, ALL_TAC] THEN
    UNDISCH_TAC ``~(t - a <= &n * r:real)`` THEN ONCE_REWRITE_TAC [MONO_NOT_EQ] THEN
    RW_TAC std_ss [] THEN FULL_SIMP_TAC std_ss [CONTENT_EQ_0, real_div] THEN
    `0 < inv r` by ASM_SIMP_TAC std_ss [REAL_LT_INV_EQ] THEN
    FULL_SIMP_TAC std_ss [REAL_LE_RMUL, REAL_NEG_LMUL] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN Q.EXISTS_TAC `t - b` THEN
    ASM_SIMP_TAC std_ss [] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    Q.EXISTS_TAC `-&n * r` THEN ASM_SIMP_TAC std_ss [REAL_LE_RMUL] THEN
    SIMP_TAC real_ss []] THEN

   `0 < inv r` by ASM_SIMP_TAC std_ss [REAL_LT_INV_EQ] THEN
   ASM_SIMP_TAC std_ss [real_div, GSYM REAL_NEG_INV] THEN
   SIMP_TAC std_ss [GSYM REAL_NEG_RMUL, REAL_NEG_LMUL, GSYM real_div] THEN
   `-(b - t) / r <= -(a - t) / r` by
     (ASM_SIMP_TAC std_ss [real_div, REAL_LE_RMUL] THEN ASM_REAL_ARITH_TAC) THEN
   SIMP_TAC std_ss [sup_eq] THEN CONJ_TAC THENL
   [GEN_TAC THEN GEN_REWR_TAC LAND_CONV [GSYM SPECIFICATION] THEN
    SIMP_TAC std_ss [IN_IMAGE, IN_UNIV] THEN RW_TAC std_ss [extreal_mul_def] THEN
    SIMP_TAC std_ss [extreal_le_def, line, INTER_INTERVAL, GSYM interval] THEN
    ASM_CASES_TAC ``max (-(b - t) / r) (-&n) <= min (-(a - t) / r) (&n:real)`` THENL
    [ALL_TAC, FULL_SIMP_TAC std_ss [REAL_NOT_LE] THEN
     `min (-(a - t) / r) (&n) <= max (-(b - t) / r) (-&n)`
      by ASM_SIMP_TAC std_ss [REAL_LE_LT] THEN
     POP_ASSUM (ASSUME_TAC o ONCE_REWRITE_RULE [GSYM CONTENT_EQ_0]) THEN
     ASM_SIMP_TAC real_ss [CONTENT_CLOSED_INTERVAL] THEN ASM_REAL_ARITH_TAC] THEN
    ASM_SIMP_TAC std_ss [CONTENT_CLOSED_INTERVAL] THEN
    ONCE_REWRITE_TAC [REAL_MUL_COMM] THEN ASM_SIMP_TAC std_ss [GSYM REAL_LE_RDIV_EQ] THEN
    Q_TAC SUFF_TAC `(b - a) / r = (-(a - t) / r) - (-(b - t) / r)` THENL
    [DISC_RW_KILL THEN FULL_SIMP_TAC std_ss [min_def, max_def] THEN
     ASM_REAL_ARITH_TAC, ALL_TAC] THEN
    SIMP_TAC std_ss [real_sub, REAL_DIV_ADD, real_div] THEN
    REAL_ARITH_TAC,
    ALL_TAC] THEN

   GEN_TAC THEN DISCH_THEN MATCH_MP_TAC THEN ONCE_REWRITE_TAC [GSYM SPECIFICATION] THEN
   SIMP_TAC std_ss [IN_IMAGE, IN_UNIV, extreal_mul_def, extreal_11] THEN
   SIMP_TAC std_ss [line, INTER_INTERVAL, GSYM interval] THEN
   `?n. abs (-(b - t) / r) <= &n` by METIS_TAC [SIMP_REAL_ARCH] THEN
   `?m. abs (-(a - t) / r) <= &m` by METIS_TAC [SIMP_REAL_ARCH] THEN
   Q.EXISTS_TAC `MAX n m` THEN
   Q_TAC SUFF_TAC `max (-(b - t) / r) (-&MAX n m) = -(b - t) / r` THENL
   [DISC_RW_KILL,
    RW_TAC std_ss [max_def, MAX_DEF] THEN FULL_SIMP_TAC std_ss [] THENL
    [ASM_SIMP_TAC std_ss [GSYM REAL_LE_ANTISYM] THEN
     UNDISCH_TAC ``abs (-(a - t) / r) <= &m:real`` THEN
     UNDISCH_TAC ``abs (-(b - t) / r) <= &n:real`` THEN
     FULL_SIMP_TAC real_ss [abs, REAL_LE_RDIV_EQ, REAL_LE_LDIV_EQ] THEN
     RW_TAC std_ss [] THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
     FULL_SIMP_TAC real_ss [REAL_LE_RDIV_EQ, REAL_LE_LDIV_EQ] THEN
     RW_TAC std_ss [] THEN TRY (ASM_REAL_ARITH_TAC) THENL
     [UNDISCH_TAC `` -((t - b) / r) <= &n:real`` THEN
      GEN_REWR_TAC LAND_CONV [GSYM REAL_LE_NEG] THEN
      ASM_SIMP_TAC std_ss [REAL_LE_RDIV_EQ, REAL_NEG_NEG] THEN DISCH_TAC THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN Q.EXISTS_TAC `-&n * r` THEN
      ASM_SIMP_TAC std_ss [REAL_NEG_LMUL] THEN
     ASM_SIMP_TAC real_ss [REAL_LE_RMUL],
      ALL_TAC] THEN
     UNDISCH_TAC `` -((t - a) / r) <= &m:real`` THEN
     GEN_REWR_TAC LAND_CONV [GSYM REAL_LE_NEG] THEN
     ASM_SIMP_TAC std_ss [REAL_LE_RDIV_EQ, REAL_NEG_NEG] THEN DISCH_TAC THEN
     UNDISCH_TAC `` -((t - b) / r) <= &n:real`` THEN
     GEN_REWR_TAC LAND_CONV [GSYM REAL_LE_NEG] THEN
     ASM_SIMP_TAC std_ss [REAL_LE_RDIV_EQ, REAL_NEG_NEG] THEN DISCH_TAC THEN
     MATCH_MP_TAC REAL_LE_TRANS THEN Q.EXISTS_TAC `-&n * r` THEN
     ASM_SIMP_TAC std_ss [REAL_NEG_LMUL] THEN
     ASM_SIMP_TAC real_ss [REAL_LE_RMUL],
     ALL_TAC] THEN

    ASM_SIMP_TAC std_ss [GSYM REAL_LE_ANTISYM] THEN
    UNDISCH_TAC ``abs (-(a - t) / r) <= &m:real`` THEN
    UNDISCH_TAC ``abs (-(b - t) / r) <= &n:real`` THEN
    FULL_SIMP_TAC real_ss [abs, REAL_LE_RDIV_EQ, REAL_LE_LDIV_EQ] THEN
    RW_TAC std_ss [] THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
    FULL_SIMP_TAC real_ss [REAL_LE_RDIV_EQ, REAL_LE_LDIV_EQ] THEN
    RW_TAC std_ss [] THEN TRY (ASM_REAL_ARITH_TAC) THENL
    [UNDISCH_TAC `` -((t - b) / r) <= &n:real`` THEN
     GEN_REWR_TAC LAND_CONV [GSYM REAL_LE_NEG] THEN
     ASM_SIMP_TAC std_ss [REAL_LE_RDIV_EQ, REAL_NEG_NEG] THEN DISCH_TAC THEN
     MATCH_MP_TAC REAL_LE_TRANS THEN Q.EXISTS_TAC `-&n * r` THEN
     ASM_SIMP_TAC std_ss [REAL_NEG_LMUL] THEN
     ASM_SIMP_TAC real_ss [REAL_LE_RMUL],
     ALL_TAC] THEN
    UNDISCH_TAC `` -((t - b) / r) <= &n:real`` THEN
    GEN_REWR_TAC LAND_CONV [GSYM REAL_LE_NEG] THEN
    ASM_SIMP_TAC std_ss [REAL_LE_RDIV_EQ, REAL_NEG_NEG] THEN DISCH_TAC THEN
    UNDISCH_TAC `` -((t - a) / r) <= &m:real`` THEN
    GEN_REWR_TAC LAND_CONV [GSYM REAL_LE_NEG] THEN
    ASM_SIMP_TAC std_ss [REAL_LE_RDIV_EQ, REAL_NEG_NEG] THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN Q.EXISTS_TAC `-&n * r` THEN
    ASM_SIMP_TAC std_ss [REAL_NEG_LMUL] THEN
    ASM_SIMP_TAC real_ss [REAL_LE_RMUL]] THEN

   Q_TAC SUFF_TAC `min (-(a - t) / r) (&MAX n m) = -(a - t) / r` THENL
   [DISC_RW_KILL,
    RW_TAC std_ss [min_def, MAX_DEF] THEN FULL_SIMP_TAC std_ss [] THENL
    [UNDISCH_TAC ``~(-(a - t) / r <= &m:real)`` THEN
     ONCE_REWRITE_TAC [MONO_NOT_EQ] THEN RW_TAC std_ss [] THEN
     UNDISCH_TAC ``abs (-(a - t) / r) <= &m:real`` THEN
     UNDISCH_TAC ``abs (-(b - t) / r) <= &n:real`` THEN
     FULL_SIMP_TAC real_ss [abs, REAL_LE_RDIV_EQ, REAL_LE_LDIV_EQ] THEN
     RW_TAC std_ss [] THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
     FULL_SIMP_TAC real_ss [REAL_LE_RDIV_EQ, REAL_LE_LDIV_EQ] THEN
     RW_TAC std_ss [] THEN TRY (ASM_REAL_ARITH_TAC) THEN
     UNDISCH_TAC `` -((t - a) / r) <= &m:real`` THEN
     GEN_REWR_TAC LAND_CONV [GSYM REAL_LE_NEG] THEN
     ASM_SIMP_TAC std_ss [REAL_LE_RDIV_EQ, REAL_NEG_NEG] THEN DISCH_TAC THEN
     ASM_REAL_ARITH_TAC, ALL_TAC] THEN

    UNDISCH_TAC ``~(-(a - t) / r <= &n:real)`` THEN
    ONCE_REWRITE_TAC [MONO_NOT_EQ] THEN RW_TAC std_ss [] THEN
    UNDISCH_TAC ``abs (-(a - t) / r) <= &m:real`` THEN
    UNDISCH_TAC ``abs (-(b - t) / r) <= &n:real`` THEN
    FULL_SIMP_TAC real_ss [abs, REAL_LE_RDIV_EQ, REAL_LE_LDIV_EQ] THEN
    RW_TAC std_ss [] THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
    FULL_SIMP_TAC real_ss [REAL_LE_RDIV_EQ, REAL_LE_LDIV_EQ] THEN
    RW_TAC std_ss [] THEN TRY (ASM_REAL_ARITH_TAC) THENL
    [MATCH_MP_TAC REAL_LE_TRANS THEN Q.EXISTS_TAC `&m * r` THEN
     ASM_SIMP_TAC real_ss [REAL_LE_RMUL],
     MATCH_MP_TAC REAL_LE_TRANS THEN Q.EXISTS_TAC `&m * r` THEN
     ASM_SIMP_TAC real_ss [REAL_LE_RMUL],
     ALL_TAC] THEN
    UNDISCH_TAC `` -((t - b) / r) <= &n:real`` THEN
    GEN_REWR_TAC LAND_CONV [GSYM REAL_LE_NEG] THEN
    ASM_SIMP_TAC std_ss [REAL_LE_RDIV_EQ, REAL_NEG_NEG] THEN DISCH_TAC THEN
    UNDISCH_TAC `` -((t - a) / r) <= &m:real`` THEN
    GEN_REWR_TAC LAND_CONV [GSYM REAL_LE_NEG] THEN
    ASM_SIMP_TAC std_ss [REAL_LE_RDIV_EQ, REAL_NEG_NEG] THEN DISCH_TAC THEN
    ASM_REAL_ARITH_TAC] THEN
   ASM_SIMP_TAC std_ss [CONTENT_CLOSED_INTERVAL, real_div] THEN
   SIMP_TAC std_ss [GSYM REAL_SUB_RDISTRIB] THEN
   ONCE_REWRITE_TAC [REAL_ARITH ``a * (b * c) = b * (a * c:real)``] THEN
   ASM_SIMP_TAC real_ss [REAL_MUL_RINV] THEN REAL_ARITH_TAC);

val lebesgue_pos_integral_real_affine = store_thm ("lebesgue_pos_integral_real_affine",
  ``!f c t. c <> 0 /\ f IN measurable borel Borel ==>
     (pos_fn_integral lborel (\x. max 0 (f x)) =
      Normal (abs c) * pos_fn_integral lborel (\x. max 0 (f (t + c * x))))``,
  RW_TAC std_ss [] THEN
  Q_TAC SUFF_TAC `pos_fn_integral lborel (\x. max 0 (f x)) =
    pos_fn_integral (density
        (distr lborel (space borel,subsets borel,(\x. 0))
           (\x. t + c * x)) (\z. Normal (abs c))) (\x. max 0 (f x))` THENL
  [DISC_RW_KILL,
   Q_TAC SUFF_TAC `pos_fn_integral lborel (\x. max 0 (f x)) =
      pos_fn_integral (measure_of lborel) (\x. max 0 (f x))` THENL
   [DISC_RW_KILL,
    SIMP_TAC std_ss [pos_fn_integral_def] THEN AP_TERM_TAC THEN
    AP_TERM_TAC THEN ABS_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    ABS_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    SIMP_TAC std_ss [IN_psfis_eq] THEN AP_TERM_TAC THEN ABS_TAC THEN
    AP_TERM_TAC THEN ABS_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN
    Q_TAC SUFF_TAC `pos_simple_fn lborel g s a x =
       pos_simple_fn (measure_of lborel) g s a x` THENL
    [DISCH_TAC THEN ASM_SIMP_TAC std_ss [],
     SIMP_TAC std_ss [pos_simple_fn_def] THEN EQ_TAC THEN
     RW_TAC std_ss [measure_of, m_space_def, measurable_sets_def, measure_def, lborel] THENL
     [MATCH_MP_TAC sigma_sets_basic THEN METIS_TAC [],
      ASM_SET_TAC [POW_DEF],
      FULL_SIMP_TAC std_ss [GSYM space_borel] THEN
      `sigma_sets (space borel) (subsets borel) = subsets borel` by
      METIS_TAC [SPACE, sigma_algebra_borel, sigma_sets_eq] THEN
      METIS_TAC [], ALL_TAC] THEN
     ASM_SET_TAC [POW_DEF]] THEN
    MATCH_MP_TAC (METIS [] ``(a ==> (b = c)) ==> (a /\ b = a /\ c)``) THEN
    POP_ASSUM (ASSUME_TAC o ONCE_REWRITE_RULE [EQ_SYM_EQ]) THEN
    POP_ASSUM (fn th => REWRITE_TAC [th]) THEN DISCH_TAC THEN
    AP_TERM_TAC THEN SIMP_TAC std_ss [pos_simple_fn_integral_def] THEN
    FULL_SIMP_TAC std_ss [pos_simple_fn_def] THEN
    FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP EXTREAL_SUM_IMAGE_EQ) THEN
    CONJ_TAC THENL
    [ALL_TAC,
     RW_TAC std_ss [measure_of, measure_def, lborel] THEN
     FIRST_X_ASSUM (fn th => POP_ASSUM MP_TAC THEN ASSUME_TAC th) THEN
     ONCE_REWRITE_TAC [MONO_NOT_EQ] THEN RW_TAC std_ss [] THENL
     [MATCH_MP_TAC sigma_sets_basic THEN METIS_TAC [measurable_sets_def, lborel],
      ALL_TAC] THEN
     `sigma_sets (space borel) (subsets borel) = subsets borel` by
      METIS_TAC [SPACE, sigma_algebra_borel, sigma_sets_eq] THEN
     METIS_TAC [measure_space_lborel, GSYM lborel, space_borel]] THEN
    DISJ1_TAC THEN RW_TAC std_ss [] THENL
    [SIMP_TAC std_ss [lt_infty] THEN MATCH_MP_TAC lte_trans THEN
     Q.EXISTS_TAC `0` THEN CONJ_TAC THENL
     [METIS_TAC [lt_infty, num_not_infty, extreal_of_num_def], ALL_TAC] THEN
     MATCH_MP_TAC le_mul THEN ASM_SIMP_TAC std_ss [extreal_of_num_def, extreal_le_def] THEN
     SIMP_TAC std_ss [GSYM extreal_of_num_def] THEN ASSUME_TAC measure_space_lborel THEN
     `positive lborel` by METIS_TAC [measure_space_def] THEN
     METIS_TAC [positive_def], ALL_TAC] THEN
    SIMP_TAC std_ss [lt_infty] THEN MATCH_MP_TAC lte_trans THEN
    Q.EXISTS_TAC `0` THEN CONJ_TAC THENL
    [METIS_TAC [lt_infty, num_not_infty, extreal_of_num_def], ALL_TAC] THEN
    MATCH_MP_TAC le_mul THEN ASM_SIMP_TAC std_ss [extreal_of_num_def, extreal_le_def] THEN
    SIMP_TAC std_ss [GSYM extreal_of_num_def] THEN ASSUME_TAC measure_space_lborel THEN
    `positive lborel` by METIS_TAC [measure_space_def] THEN
    SIMP_TAC std_ss [measure_of, measure_def, lborel] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC std_ss [le_refl] THEN
    METIS_TAC [positive_def, lborel, measure_def]] THEN

   Q_TAC SUFF_TAC `pos_fn_integral (density
     (distr lborel (space borel,subsets borel,(\x. 0)) (\x. t + c * x))
     (\z. Normal (abs c))) (\x. max 0 (f x)) =
                   pos_fn_integral (measure_of (density
     (distr lborel (space borel,subsets borel,(\x. 0)) (\x. t + c * x))
     (\z. Normal (abs c)))) (\x. max 0 (f x))` THENL
   [METIS_TAC [lebesgue_real_affine], ALL_TAC] THEN

   SIMP_TAC std_ss [pos_fn_integral_def] THEN AP_TERM_TAC THEN
   AP_TERM_TAC THEN ABS_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
   ABS_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
   SIMP_TAC std_ss [IN_psfis_eq] THEN AP_TERM_TAC THEN ABS_TAC THEN
   AP_TERM_TAC THEN ABS_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN
   Q_TAC SUFF_TAC `pos_simple_fn (density
        (distr lborel (space borel,subsets borel,(\x. 0))
           (\x. t + c * x)) (\z. Normal (abs c))) g s a x =
      pos_simple_fn (measure_of (density
        (distr lborel (space borel,subsets borel,(\x. 0))
           (\x. t + c * x)) (\z. Normal (abs c)))) g s a x` THENL
   [DISCH_TAC THEN ASM_SIMP_TAC std_ss [],
    SIMP_TAC std_ss [pos_simple_fn_def] THEN EQ_TAC THEN
    RW_TAC std_ss [measure_of, m_space_def, measurable_sets_def, measure_def,
                   density, distr] THENL
    [MATCH_MP_TAC sigma_sets_basic THEN METIS_TAC [],
     ASM_SET_TAC [POW_DEF, space_borel],
     FULL_SIMP_TAC std_ss [GSYM space_borel] THEN
     `sigma_sets (space borel) (subsets borel) = subsets borel` by
     METIS_TAC [SPACE, sigma_algebra_borel, sigma_sets_eq] THEN
     METIS_TAC [], ALL_TAC] THEN
    ASM_SET_TAC [POW_DEF, space_borel]] THEN
   MATCH_MP_TAC (METIS [] ``(a ==> (b = c)) ==> (a /\ b = a /\ c)``) THEN
   POP_ASSUM (ASSUME_TAC o ONCE_REWRITE_RULE [EQ_SYM_EQ]) THEN
   POP_ASSUM (fn th => REWRITE_TAC [th]) THEN DISCH_TAC THEN
   AP_TERM_TAC THEN SIMP_TAC std_ss [pos_simple_fn_integral_def] THEN
   FULL_SIMP_TAC std_ss [pos_simple_fn_def] THEN
   FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP EXTREAL_SUM_IMAGE_EQ) THEN
   Q_TAC SUFF_TAC `measure_space (density
      (distr lborel (space borel,subsets borel,(\x. 0)) (\x. t + c * x))
      (\z. Normal (abs c)))` THENL
   [DISCH_TAC,
    MATCH_MP_TAC measure_space_density THEN CONJ_TAC THENL
    [ALL_TAC, MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST THEN
     Q.EXISTS_TAC `Normal (abs c)` THEN
     SIMP_TAC std_ss [m_space_def, measurable_sets_def, distr] THEN
     SIMP_TAC std_ss [SPACE, sigma_algebra_borel]] THEN
    MATCH_MP_TAC measure_space_distr THEN
    SIMP_TAC std_ss [measure_space_borel, measure_space_lborel] THEN
    SIMP_TAC std_ss [m_space_def, measurable_sets_def, SPACE] THEN
     SIMP_TAC std_ss [GSYM borel_measurable] THEN MATCH_MP_TAC borel_measurable_add THEN
     Q.EXISTS_TAC `(\x. t)` THEN Q.EXISTS_TAC `(\x. c * x)` THEN
     CONJ_TAC THENL [METIS_TAC [lborel, GSYM space_borel, m_space_def,
       measurable_sets_def, sigma_algebra_borel, SPACE], ALL_TAC] THEN
     CONJ_TAC THENL
     [MATCH_MP_TAC borel_measurable_const THEN
      METIS_TAC [lborel, GSYM space_borel, m_space_def,
       measurable_sets_def, sigma_algebra_borel, SPACE],
      ALL_TAC] THEN
     SIMP_TAC std_ss [] THEN MATCH_MP_TAC borel_measurable_cmul THEN
     Q.EXISTS_TAC `(\x. x)` THEN Q.EXISTS_TAC `c` THEN
     ASM_SIMP_TAC std_ss [] THEN
     CONJ_TAC THENL [METIS_TAC [lborel, GSYM space_borel, m_space_def,
       measurable_sets_def, sigma_algebra_borel, SPACE], ALL_TAC] THEN
     Q_TAC SUFF_TAC `(\x:real. x) = I` THENL
     [DISC_RW_KILL, SIMP_TAC std_ss [FUN_EQ_THM]] THEN
     SIMP_TAC std_ss [borel_measurable, m_space_def, measurable_sets_def, SPACE, lborel] THEN
     SIMP_TAC std_ss [GSYM space_borel, SPACE] THEN MATCH_MP_TAC MEASURABLE_I THEN
     SIMP_TAC std_ss [sigma_algebra_borel]] THEN
   CONJ_TAC THENL
   [ALL_TAC,
    RW_TAC std_ss [measure_of, measure_def, measurable_sets_def, m_space_def, density, distr] THEN
    FIRST_X_ASSUM (fn th => POP_ASSUM MP_TAC THEN ASSUME_TAC th) THEN
    ONCE_REWRITE_TAC [MONO_NOT_EQ] THEN RW_TAC std_ss [] THENL
    [MATCH_MP_TAC sigma_sets_basic THEN METIS_TAC [measurable_sets_def, lborel],
     ALL_TAC] THEN
    `sigma_sets (space borel) (subsets borel) = subsets borel` by
     METIS_TAC [SPACE, sigma_algebra_borel, sigma_sets_eq] THEN
    FULL_SIMP_TAC std_ss
     [density, distr, m_space_def, measurable_sets_def, measure_def]] THEN
    DISJ1_TAC THEN RW_TAC std_ss [] THENL
    [SIMP_TAC std_ss [lt_infty] THEN MATCH_MP_TAC lte_trans THEN
     Q.EXISTS_TAC `0` THEN CONJ_TAC THENL
     [METIS_TAC [lt_infty, num_not_infty, extreal_of_num_def], ALL_TAC] THEN
     MATCH_MP_TAC le_mul THEN ASM_SIMP_TAC std_ss [extreal_of_num_def, extreal_le_def] THEN
     SIMP_TAC std_ss [GSYM extreal_of_num_def] THEN
     METIS_TAC [positive_def, measure_space_def], ALL_TAC] THEN
    SIMP_TAC std_ss [lt_infty] THEN MATCH_MP_TAC lte_trans THEN
    Q.EXISTS_TAC `0` THEN CONJ_TAC THENL
    [METIS_TAC [lt_infty, num_not_infty, extreal_of_num_def], ALL_TAC] THEN
    MATCH_MP_TAC le_mul THEN ASM_SIMP_TAC std_ss [extreal_of_num_def, extreal_le_def] THEN
    SIMP_TAC std_ss [GSYM extreal_of_num_def] THEN
    SIMP_TAC std_ss [measure_of, measure_def, density, distr] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC std_ss [le_refl] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC std_ss [le_refl] THEN
    `positive (density
           (distr lborel (space borel,subsets borel,(\x. 0))
              (\x. t + c * x)) (\z. Normal (abs c)))` by
     METIS_TAC [measure_space_def] THEN
    POP_ASSUM MP_TAC THEN SIMP_TAC std_ss [positive_def] THEN STRIP_TAC THEN
    POP_ASSUM (MP_TAC o Q.SPEC `a (x':num)`) THEN
    FULL_SIMP_TAC std_ss [density, distr, m_space_def, measurable_sets_def, measure_def]] THEN
  Q_TAC SUFF_TAC `(\x. max 0 (f x)) = (\x. max 0 ((\x. max 0 (f x)) x))` THENL
  [DISC_RW_KILL,
   SIMP_TAC std_ss [le_max1, extreal_max_def, FUN_EQ_THM] THEN
   RW_TAC std_ss [] THEN FULL_SIMP_TAC std_ss []] THEN
  Q_TAC SUFF_TAC `pos_fn_integral
   (density
     (distr lborel (space borel,subsets borel,(\x. 0)) (\x. t + c * x))
     (\z. Normal (abs c))) (\x. max 0 ((\x. max 0 (f x)) x)) =
   pos_fn_integral (distr lborel (space borel,subsets borel,(\x. 0)) (\x. t + c * x))
    (\x. max 0 ((\z. Normal (abs c)) x * (\x. max 0 (f x)) x))` THENL
  [DISC_RW_KILL,
   MATCH_MP_TAC (REWRITE_RULE [GSYM density] pos_fn_integral_density') THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC measure_space_distr THEN
    SIMP_TAC std_ss [measure_space_lborel, measure_space_borel] THEN
    SIMP_TAC std_ss [m_space_def, measurable_sets_def, SPACE] THEN
    SIMP_TAC std_ss [GSYM borel_measurable] THEN MATCH_MP_TAC borel_measurable_add THEN
    Q.EXISTS_TAC `(\x. t)` THEN Q.EXISTS_TAC `(\x. c * x)` THEN
    CONJ_TAC THENL [METIS_TAC [lborel, GSYM space_borel, m_space_def,
      measurable_sets_def, sigma_algebra_borel, SPACE], ALL_TAC] THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC borel_measurable_const THEN
     METIS_TAC [lborel, GSYM space_borel, m_space_def,
      measurable_sets_def, sigma_algebra_borel, SPACE],
     ALL_TAC] THEN
    SIMP_TAC std_ss [] THEN MATCH_MP_TAC borel_measurable_cmul THEN
    Q.EXISTS_TAC `(\x. x)` THEN Q.EXISTS_TAC `c` THEN
    ASM_SIMP_TAC std_ss [] THEN
    CONJ_TAC THENL [METIS_TAC [lborel, GSYM space_borel, m_space_def,
      measurable_sets_def, sigma_algebra_borel, SPACE], ALL_TAC] THEN
    Q_TAC SUFF_TAC `(\x:real. x) = I` THENL
    [DISC_RW_KILL, SIMP_TAC std_ss [FUN_EQ_THM]] THEN
    SIMP_TAC std_ss [borel_measurable, m_space_def, measurable_sets_def, SPACE, lborel] THEN
    SIMP_TAC std_ss [GSYM space_borel, SPACE] THEN MATCH_MP_TAC MEASURABLE_I THEN
    SIMP_TAC std_ss [sigma_algebra_borel],
    ALL_TAC] THEN
   SIMP_TAC std_ss [m_space_def, measurable_sets_def, distr, le_max1] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST THEN Q.EXISTS_TAC `Normal (abs c)` THEN
    SIMP_TAC std_ss [SPACE, sigma_algebra_borel],
    ALL_TAC] THEN
   CONJ_TAC THENL
   [ALL_TAC,
    Q_TAC SUFF_TAC `(\x. max ((\x. 0) x) (f x)) IN
     measurable (space borel,subsets borel) Borel` THENL
    [SIMP_TAC std_ss [], ALL_TAC] THEN
    MATCH_MP_TAC IN_MEASURABLE_BOREL_MAX THEN
    ASM_SIMP_TAC std_ss [SPACE, sigma_algebra_borel] THEN
    MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST THEN METIS_TAC [sigma_algebra_borel]] THEN
   SIMP_TAC std_ss [AE, ae_filter, GSPECIFICATION] THEN
   SIMP_TAC std_ss [m_space_def, measurable_sets_def, measure_def,
                    null_sets, GSPECIFICATION] THEN
   Q.EXISTS_TAC `{}` THEN SIMP_TAC std_ss [OPEN_EMPTY, borel_open] THEN
   SIMP_TAC std_ss [PREIMAGE_EMPTY, INTER_EMPTY] THEN
   ASSUME_TAC measure_space_lborel THEN
   CONJ_TAC THENL [METIS_TAC [measure_space_def, positive_def], ALL_TAC] THEN
   SIMP_TAC std_ss [extreal_of_num_def, extreal_le_def, ABS_POS] THEN
   SIMP_TAC std_ss [GSPEC_F, SUBSET_REFL]] THEN

  SIMP_TAC std_ss [] THEN
  Q_TAC SUFF_TAC `pos_fn_integral
  (distr lborel (space borel,subsets borel,(\x. 0)) (\x. t + c * x))
  (\x. max 0 ((\x. Normal (abs c) * max 0 (f x)) x)) =
   pos_fn_integral lborel (\x. max 0 ((\x. Normal (abs c) * max 0 (f x))
                               ((\x. t + c * x) x)))` THENL
  [SIMP_TAC std_ss [] THEN DISC_RW_KILL,
   MATCH_MP_TAC pos_fn_integral_distr' THEN
   ASM_SIMP_TAC std_ss [measure_space_lborel, measure_space_borel] THEN
   SIMP_TAC std_ss [m_space_def, measurable_sets_def, lborel, distr, GSYM space_borel] THEN
   SIMP_TAC std_ss [SPACE, GSYM borel_measurable] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC borel_measurable_add THEN
    Q.EXISTS_TAC `(\x. t)` THEN Q.EXISTS_TAC `(\x. c * x)` THEN
    CONJ_TAC THENL [METIS_TAC [lborel, GSYM space_borel, m_space_def,
      measurable_sets_def, sigma_algebra_borel, SPACE], ALL_TAC] THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC borel_measurable_const THEN
     METIS_TAC [lborel, GSYM space_borel, m_space_def,
      measurable_sets_def, sigma_algebra_borel, SPACE],
     ALL_TAC] THEN
    SIMP_TAC std_ss [] THEN MATCH_MP_TAC borel_measurable_cmul THEN
    Q.EXISTS_TAC `(\x. x)` THEN Q.EXISTS_TAC `c` THEN
    ASM_SIMP_TAC std_ss [] THEN
    CONJ_TAC THENL [METIS_TAC [lborel, GSYM space_borel, m_space_def,
      measurable_sets_def, sigma_algebra_borel, SPACE], ALL_TAC] THEN
    Q_TAC SUFF_TAC `(\x:real. x) = I` THENL
    [DISC_RW_KILL, SIMP_TAC std_ss [FUN_EQ_THM]] THEN
    SIMP_TAC std_ss [borel_measurable, m_space_def, measurable_sets_def, SPACE, lborel] THEN
    SIMP_TAC std_ss [GSYM space_borel, SPACE] THEN MATCH_MP_TAC MEASURABLE_I THEN
    SIMP_TAC std_ss [sigma_algebra_borel],
    ALL_TAC] THEN
   CONJ_TAC THENL
   [ALL_TAC,
    GEN_TAC THEN MATCH_MP_TAC le_mul THEN
    SIMP_TAC std_ss [le_max1, extreal_of_num_def, extreal_le_def, ABS_POS]] THEN
   ONCE_REWRITE_TAC [METIS [m_space_def, measurable_sets_def, SPACE]
    ``borel = (m_space (space borel, subsets borel, (\x. 0)),
       measurable_sets (space borel, subsets borel, (\x. 0)))``] THEN
   MATCH_MP_TAC IN_MEASURABLE_BOREL_TIMES THEN Q.EXISTS_TAC `(\x. Normal (abs c))` THEN
   Q.EXISTS_TAC `(\x. max ((\x. 0) x) (f x))` THEN
   CONJ_TAC THENL [SIMP_TAC std_ss [measure_space_borel], ALL_TAC] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST THEN
    METIS_TAC [m_space_def, measurable_sets_def, SPACE, sigma_algebra_borel],
    ALL_TAC] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC IN_MEASURABLE_BOREL_MAX THEN
    ASM_SIMP_TAC std_ss [m_space_def, measurable_sets_def, SPACE, sigma_algebra_borel] THEN
    ONCE_REWRITE_TAC [METIS [m_space_def, measurable_sets_def, SPACE]
    ``borel = (m_space (space borel, subsets borel, (\x. 0)),
       measurable_sets (space borel, subsets borel, (\x. 0)))``] THEN
    MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST THEN
    METIS_TAC [m_space_def, measurable_sets_def, SPACE, sigma_algebra_borel],
    ALL_TAC] THEN
   SIMP_TAC std_ss []] THEN

  Q_TAC SUFF_TAC `(\x. max 0 (f (t + c * x))) = (\x. max 0 ((\x. max 0 (f (t + c * x))) x))` THENL
  [DISC_RW_KILL,
   SIMP_TAC std_ss [le_max1, extreal_max_def, FUN_EQ_THM] THEN
   RW_TAC std_ss [] THEN FULL_SIMP_TAC std_ss []] THEN
  SIMP_TAC std_ss [] THEN

  Q_TAC SUFF_TAC `pos_fn_integral lborel
   (\x. max 0 (Normal (abs c) * ((\x. max 0 (f (t + c * x))) x))) =
   Normal (abs c) *
   pos_fn_integral lborel (\x. max 0 ((\x. max 0 (f (t + c * x))) x))` THENL
  [SIMP_TAC std_ss [], ALL_TAC] THEN
  MATCH_MP_TAC pos_fn_integral_cmult THEN
  SIMP_TAC std_ss [measure_space_lborel] THEN CONJ_TAC THENL
  [METIS_TAC [extreal_of_num_def, extreal_le_def, ABS_POS],
   ALL_TAC] THEN
  Q_TAC SUFF_TAC `(\x. max ((\x. 0) x) ((\x. f (t + c * x)) x)) IN
          measurable (m_space lborel,measurable_sets lborel) Borel` THENL
  [SIMP_TAC std_ss [], ALL_TAC] THEN
  MATCH_MP_TAC IN_MEASURABLE_BOREL_MAX THEN
  ASSUME_TAC measure_space_lborel THEN
  CONJ_TAC THENL [METIS_TAC [measure_space_def], ALL_TAC] THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST THEN
   METIS_TAC [measure_space_def],
   ALL_TAC] THEN
  Q_TAC SUFF_TAC `(\x. f (t + c * x)) = f o (\x. t + c * x)` THENL
  [DISC_RW_KILL, SIMP_TAC std_ss [o_DEF]] THEN
  MATCH_MP_TAC MEASURABLE_COMP THEN Q.EXISTS_TAC `borel` THEN
  ASM_SIMP_TAC std_ss [GSYM borel_measurable] THEN
  MATCH_MP_TAC borel_measurable_add THEN
  Q.EXISTS_TAC `(\x. t)` THEN Q.EXISTS_TAC `(\x. c * x)` THEN
  ASSUME_TAC measure_space_lborel THEN
  CONJ_TAC THENL [METIS_TAC [measure_space_def], ALL_TAC] THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC borel_measurable_const THEN
   METIS_TAC [measure_space_def],
   ALL_TAC] THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC borel_measurable_cmul THEN Q.EXISTS_TAC `(\x. x)` THEN
   Q.EXISTS_TAC `c` THEN SIMP_TAC std_ss [] THEN
   CONJ_TAC THENL [METIS_TAC [measure_space_def], ALL_TAC] THEN
   Q_TAC SUFF_TAC `(\x:real. x) = I` THENL
   [DISC_RW_KILL, SIMP_TAC std_ss [FUN_EQ_THM]] THEN
   SIMP_TAC std_ss [borel_measurable, m_space_def, measurable_sets_def, SPACE, lborel] THEN
   SIMP_TAC std_ss [GSYM space_borel, SPACE] THEN
   MATCH_MP_TAC MEASURABLE_I THEN SIMP_TAC std_ss [sigma_algebra_borel],
   ALL_TAC] THEN
  SIMP_TAC std_ss []);

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* ------------------------------------------------------------------------- *)

(* this (nonsense) lemma is not used any more, reserved for future only *)
Theorem null_sets_density_iff[local] :
    !f A M. measure_space M /\ (!x. 0 <= f x) /\
            f IN measurable (m_space M, measurable_sets M) Borel ==>
           (A IN measurable_sets M /\
           (measure (m_space M,measurable_sets M,
             (\A. pos_fn_integral M (\x. f x * indicator_fn A x))) A = 0) <=>
           (A IN measurable_sets M /\ AE x::M. x IN A ==> f x <= 0))
Proof
    RW_TAC std_ss []
 >> MATCH_MP_TAC (METIS [] ``(a ==> (b <=> c)) ==> (a /\ b <=> a /\ c)``)
 >> DISCH_TAC
 >> Know `pos_fn_integral M (\x. f x * indicator_fn A x) =
          pos_fn_integral M (\x. max 0 (f x) * indicator_fn A x)`
 >- (ASM_SIMP_TAC std_ss [extreal_max_def]) >> DISCH_TAC
 >> Know `(pos_fn_integral M (\x. f x * indicator_fn A x) = 0) <=>
          (measure M {x | x IN m_space M /\ (max 0 (f x) * indicator_fn A x <> 0)} = 0)`
 >- (ONCE_REWRITE_TAC [METIS [] ``max 0 (f x) * indicator_fn A x =
                             (\x. max 0 (f x) * indicator_fn A x) x``] \\
     ONCE_ASM_REWRITE_TAC [] \\
     MATCH_MP_TAC pos_fn_integral_eq_0 \\
     Q_TAC SUFF_TAC `!x. max 0 (f x) = f x` >|
     [ DISC_RW_KILL, METIS_TAC [extreal_max_def] ] \\
     ASM_SIMP_TAC std_ss [nonneg_def] >> rpt STRIP_TAC >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       MATCH_MP_TAC le_mul >> art [INDICATOR_FN_POS],
       (* goal 2 (of 2) *)
       MATCH_MP_TAC IN_MEASURABLE_BOREL_MUL_INDICATOR \\
       METIS_TAC [measure_space_def, subsets_def] ]) >> DISCH_TAC
 (* below is reworked by Chun Tian *)
 >> ASM_SIMP_TAC std_ss [measure_def]
 >> POP_ASSUM K_TAC
 >> POP_ASSUM (ONCE_REWRITE_TAC o wrap o SYM)
 >> Q.ABBREV_TAC `g = \x. f x * indicator_fn A x`
 >> Know `(integral M (abs o g) = 0) <=> AE x::M. (abs o g) x = 0`
 >- (Suff `g IN measurable (m_space M, measurable_sets M) Borel`
     >- METIS_TAC [integral_abs_eq_0] \\
     Q.UNABBREV_TAC `g` \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_MUL_INDICATOR \\
     fs [measure_space_def, subsets_def])
 >> Know `!x. 0 <= g x`
 >- (GEN_TAC >> Q.UNABBREV_TAC `g` >> BETA_TAC \\
     MATCH_MP_TAC le_mul >> art [INDICATOR_FN_POS]) >> DISCH_TAC
 >> `abs o g = g` by METIS_TAC [nonneg_fn_abs, nonneg_def] >> POP_ORW
 >> Know `integral M g = pos_fn_integral M g`
 >- (MATCH_MP_TAC integral_pos_fn >> art []) >> Rewr'
 >> Rewr'
 >> EQ_TAC >> RW_TAC std_ss [AE_ALT, null_set_def] (* 2 subgoals *)
 >| [ (* goal 1 (of 2) *)
      Q.EXISTS_TAC `N` >> art [] \\
      Suff `{x | x IN m_space M /\ x IN A /\ ~(f x <= 0)} =
            {x | x IN m_space M /\ g x <> 0}` >- rw [] \\
      Q.UNABBREV_TAC `g` \\
      RW_TAC std_ss [Once EXTENSION, GSPECIFICATION] \\
      Cases_on `x IN A` >> RW_TAC std_ss [indicator_fn_def, mul_rone, mul_rzero] \\
      EQ_TAC >> RW_TAC std_ss [GSYM extreal_lt_def, lt_le],
      (* goal 2 (of 2) *)
      Q.EXISTS_TAC `N` >> art [] \\
      Suff `{x | x IN m_space M /\ g x <> 0} =
            {x | x IN m_space M /\ x IN A /\ ~(f x <= 0)}` >- rw [] \\
      Q.UNABBREV_TAC `g` \\
      RW_TAC std_ss [Once EXTENSION, GSPECIFICATION] \\
      Cases_on `x IN A` >> RW_TAC std_ss [indicator_fn_def, mul_rone, mul_rzero] \\
      EQ_TAC >> RW_TAC std_ss [GSYM extreal_lt_def, lt_le] ]
QED

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* ------------------------------------------------------------------------- *)

val space_diff_measure = store_thm ("space_diff_measure",
  ``!M N. m_space (diff_measure M N) = m_space M``,
  SIMP_TAC std_ss [diff_measure, m_space_def]);

val sets_diff_measure = store_thm ("sets_diff_measure",
  ``!M N. measurable_sets (diff_measure M N) = measurable_sets M``,
  SIMP_TAC std_ss [diff_measure, measurable_sets_def]);

val measure_diff_measure = store_thm ("measure_diff_measure",
  ``!M N. measure (diff_measure M N) = (\A. measure M A - measure N A)``,
  SIMP_TAC std_ss [diff_measure, measure_def]);

val _ = export_theory();
