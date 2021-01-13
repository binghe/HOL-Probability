(* ------------------------------------------------------------------------- *)
(* The Laws of Large Numbers (general case)                                  *)
(*                                                                           *)
(* Author: Chun Tian <binghe.lisp@gmail.com> (2020)                          *)
(* Fondazione Bruno Kessler and University of Trento, Italy                  *)
(* ------------------------------------------------------------------------- *)

open HolKernel Parse boolLib bossLib;

open arithmeticTheory pred_setTheory pred_setLib realTheory realLib seqTheory
     transcTheory real_sigmaTheory real_topologyTheory combinTheory;

open hurdUtils util_probTheory extrealTheory sigma_algebraTheory measureTheory
     real_borelTheory borelTheory lebesgueTheory martingaleTheory;

open probabilityTheory;

val _ = new_theory "large_number";

val _ = hide "S";

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


(* Theorem 5.2.2 [2]. This law of large numbers is due to Khintchine. *)
Theorem Weak_Law_of_Large_Numbers :
    !p X S m. prob_space p /\ (!n. real_random_variable (X n) p) /\
       pairwise_indep_vars p X (\n. Borel) UNIV /\
       identical_distribution p X Borel UNIV /\ integrable p (X 0) /\
       (m = expectation p (X 0)) /\
       (!n x. S n x = SIGMA (\i. X i x) (count n))
      ==>
       ((\n x. S (SUC n) x / &SUC n) --> (\x. m)) (in_probability p)
Proof
    rpt STRIP_TAC >> POP_ORW
 (* re-define S as an abbreviation *)
 >> Q.ABBREV_TAC ‘S = \n x. SIGMA (\i. X i x) (count n)’
 >> ‘!n x. SIGMA (\i. X i x) (count (SUC n)) = S (SUC n) x’ by METIS_TAC []
 >> POP_ORW
 >>
    cheat
QED

val _ = export_theory ();

(* References:

  [2] Chung, K.L.: A Course in Probability Theory, Third Edition. Academic Press (2001).
  [6] Billingsley, P.: Probability and Measure (Third Edition). Wiley-Interscience (1995).
 *)
