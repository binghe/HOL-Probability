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

(* Theorem 3.3.1 [2, p.54] *)


(* Theorem 3.3.3 [2, p.54] *)
Theorem indep_rv_expectation :
    !p X Y. prob_space p /\ real_random_variable X p /\ real_random_variable Y p /\
            indep_rv p X Y Borel Borel /\ integrable p X /\ integrable p Y ==>
            expectation p (\x. X x * Y x) = expectation p X * expectation p Y
Proof
    rw [indep_rv_def, real_random_variable_def, prob_space_def, p_space_def, events_def,
        real_random_variable_def, random_variable_def, expectation_def]
 >> Q.ABBREV_TAC ‘f = \x. (X x,Y x)’
 >> Q.ABBREV_TAC ‘u = \(x,y). x * (y :extreal)’
 >> ‘(\x. X x * Y x) = u o f’ by rw [Abbr ‘u’, Abbr ‘f’, o_DEF] >> POP_ORW
 (* this requires real_topology and the concept of continuous functions *)
 >> Know ‘u IN measurable (Borel CROSS Borel) Borel’
 >- cheat
 >> DISCH_TAC
 >> Know ‘f IN measurable (m_space p,measurable_sets p) (Borel CROSS Borel)’
 >- cheat
 >> DISCH_TAC
(* applying integral_distr *)
 >> Know ‘integral p (u o f) =
          integral (space (Borel CROSS Borel),subsets (Borel CROSS Borel),distr p f) u’
 >- (MP_TAC (ISPECL [“p :'a m_space”,
                     “Borel CROSS Borel”,
                     “f :'a -> extreal # extreal”,
                     “u :extreal # extreal -> extreal”] integral_distr) \\
     RW_TAC std_ss [SIGMA_ALGEBRA_BOREL_2D]) >> Rewr'
 >> Q.ABBREV_TAC ‘m1 = (space Borel,subsets Borel,distr p X)’
 >> Q.ABBREV_TAC ‘m2 = (space Borel,subsets Borel,distr p Y)’
 >> ‘measure_space m1 /\ measure_space m2’ by METIS_TAC [measure_space_distr, SIGMA_ALGEBRA_BOREL]
 (* applying EXISTENCE_OF_PROD_MEASURE, independence seems used here! *)
 >> Know ‘(space (Borel CROSS Borel),subsets (Borel CROSS Borel),distr p f) = m1 CROSS m2’
 >- cheat
 >> Rewr'
 (* clean up ‘f’ *)
 >> Q.PAT_X_ASSUM ‘f IN measurable (m_space p,measurable_sets p) (Borel CROSS Borel)’ K_TAC
 >> Q.UNABBREV_TAC ‘f’
 (* applying FUBINI' *)
 >> Know ‘integral (m1 CROSS m2) u =
          integral m2 (\y. integral m1 (\x. u (x,y)))’
 >- cheat
 >> Rewr'
 (* expand and clean up ‘u’, now all pairs disappear *)
 >> Q.UNABBREV_TAC ‘u’ >> simp []
 (* applying integral_cong_AE and integral_cmul, twice *)
 >> Know ‘integral m2 (\y. integral m1 (\x. x * y)) =
          integral m2 (\y. y * integral m1 (\x. x))’
 >- cheat
 >> Rewr'
 >> Know ‘integral m2 (\y. y * integral m1 (\x. x)) =
          integral m1 (\x. x) * integral m2 (\y. y)’
 >- cheat
 >> Rewr'
 >> Know ‘(\x. x) IN measurable Borel Borel’
 >- (rw [IN_MEASURABLE, SIGMA_ALGEBRA_BOREL, IN_FUNSET, PREIMAGE_def] \\
     MATCH_MP_TAC SIGMA_ALGEBRA_INTER >> rw [SIGMA_ALGEBRA_BOREL] \\
     MATCH_MP_TAC SIGMA_ALGEBRA_SPACE >> rw [SIGMA_ALGEBRA_BOREL])
 >> DISCH_TAC
(* applying integral_distr, twice *)
 >> Know ‘integral p X = integral m1 (\x. x)’
 >- (MP_TAC (ISPECL [“p :'a m_space”, “Borel”, “X :'a -> extreal”,
                     “(\x. x) :extreal -> extreal”] integral_distr) \\
     RW_TAC std_ss [Abbr ‘m1’, SIGMA_ALGEBRA_BOREL, o_DEF, ETA_AX])
 >> Rewr'
 >> Know ‘integral p Y = integral m2 (\y. y)’
 >- (MP_TAC (ISPECL [“p :'a m_space”, “Borel”, “Y :'a -> extreal”,
                     “(\x. x) :extreal -> extreal”] integral_distr) \\
     RW_TAC std_ss [Abbr ‘m2’, SIGMA_ALGEBRA_BOREL, o_DEF, ETA_AX])
 >> Rewr
QED

(* An easy corollary of Theorem 3.3.3 *)
Theorem indep_rv_uncorrelated :
    !p X Y. prob_space p /\ real_random_variable X p /\ real_random_variable Y p /\
            finite_second_moments p X /\ finite_second_moments p Y /\
            indep_rv p X Y Borel Borel ==> uncorrelated p X Y
Proof
    RW_TAC std_ss [uncorrelated_def]
 >> MATCH_MP_TAC indep_rv_expectation >> art []
 >> CONJ_TAC (* 2 subgoals, same tactics *)
 >> MATCH_MP_TAC finite_second_moments_imp_integrable >> art []
QED

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
