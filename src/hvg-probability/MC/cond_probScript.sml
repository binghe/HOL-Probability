(* ========================================================================= *)
(*                                                                           *)
(*                      Condition Probability Library                        *)
(*             This code is developed using HOL4 kanaskas 7.                 *)
(*                                                                           *)
(*                   (c) Copyright, Liya Liu, 2012                           *)
(*                       Hardware Verification Group,                        *)
(*                       Concordia University                                *)
(*                                                                           *)
(*                                                                           *)
(*                      Last update: Dec 10, 2012                            *)
(*                                                                           *)
(* ========================================================================= *)
(*loadPath := "/home/l/liy_liu/HOL_2/probability/" :: !loadPath;
loadPath := "/home/l/liy_liu/HOL_2/" :: !loadPath;
val () = app load
 ["bossLib", "metisLib", "arithmeticTheory", "pred_setTheory", "realLib",
 	"pairTheory", "combinTheory", "listTheory", "transcTheory", "numLib",
 	"prim_recTheory", "probabilityTheory", "extra_pred_setTools"];
val () = quietdec := true;

set_trace "Unicode" 0;*)

open HolKernel Parse boolLib bossLib metisLib numLib combinTheory subtypeTheory
	pred_setTheory measureTheory extra_pred_setTools
     extra_pred_setTheory arithmeticTheory realTheory realLib pairTheory
      transcTheory prim_recTheory extrealTheory probabilityTheory;

val _ = new_theory "cond_prob";

val std_ss' = simpLib.++ (std_ss, boolSimps.ETA_ss);


val EVENTS_BIGUNION = store_thm
  ("EVENTS_BIGUNION",
  ``!p f n. prob_space p /\ (f IN ((count n) -> events p)) ==>
    BIGUNION (IMAGE f (count n)) IN events p``,
    RW_TAC std_ss [IN_FUNSET, IN_COUNT]
 >> `BIGUNION (IMAGE f (count n)) = BIGUNION (IMAGE (\m. (if m < n then f m else {})) UNIV)`
     by (RW_TAC std_ss [EXTENSION,IN_BIGUNION_IMAGE, IN_COUNT, IN_UNIV] >> METIS_TAC [NOT_IN_EMPTY])
 >> POP_ORW
 >> (MATCH_MP_TAC o REWRITE_RULE [subsets_def, space_def] o
	Q.SPECL [`(p_space p, events p)`,`(\m. if m < n then A m else {})`]) SIGMA_ALGEBRA_ENUM
 >> RW_TAC std_ss [EVENTS_SIGMA_ALGEBRA] >> RW_TAC std_ss [IN_FUNSET, IN_UNIV, DISJOINT_EMPTY]
 >> METIS_TAC [EVENTS_EMPTY]);

val PROB_INTER_ZERO = store_thm(
   "PROB_INTER_ZERO",
   (--`!p A B.
       (prob_space p) /\ (A IN events p) /\ (B IN events p) /\ (prob p B = 0) ==>
         (prob p (A INTER B) = 0)`--),
       RW_TAC std_ss [] THEN POP_ASSUM (MP_TAC o SYM) THEN RW_TAC std_ss [] THEN
       `(A INTER B) SUBSET B` by RW_TAC std_ss [INTER_SUBSET] THEN
       `prob p (A INTER B) <= prob p B` by FULL_SIMP_TAC std_ss [PROB_INCREASING, EVENTS_INTER] THEN
       `0 <= prob p (A INTER B)` by FULL_SIMP_TAC std_ss [PROB_POSITIVE, EVENTS_INTER] THEN
       METIS_TAC [REAL_LE_ANTISYM]);

val PROB_ZERO_INTER = store_thm
  ("PROB_ZERO_INTER",
   (--`!p A B.
       (prob_space p) /\ (A IN events p) /\ (B IN events p) /\ (prob p A = 0) ==>
         (prob p (A INTER B) = 0)`--),
       RW_TAC std_ss [] >> (MP_TAC o Q.SPECL [`p`, `B`, `A`]) PROB_INTER_ZERO
  >> RW_TAC std_ss [INTER_COMM]);

val COND_PROB_ZERO = store_thm
  ("COND_PROB_ZERO",
   ``!p A B. prob_space p /\ A IN events p /\ B IN events p /\ (prob p B = 0) ==>
     (cond_prob p A B = 0)``,
     RW_TAC std_ss [cond_prob_def, PROB_INTER_ZERO, REAL_DIV_LZERO]);

val COND_PROB_INTER_ZERO = store_thm
  ("COND_PROB_INTER_ZERO",
   ``!p A B. prob_space p /\ A IN events p /\ B IN events p /\ (prob p A = 0) ==>
     (cond_prob p A B = 0)``,
     RW_TAC std_ss [cond_prob_def] THEN
     `prob p (A INTER B) = 0 ` by METIS_TAC [PROB_INTER_ZERO, INTER_COMM] THEN
     RW_TAC std_ss [REAL_DIV_LZERO]);

val COND_PROB_ZERO_INTER = store_thm
  ("COND_PROB_ZERO_INTER",
   ``!p A B. prob_space p /\ A IN events p /\ B IN events p /\ (prob p (A INTER B) = 0) ==>
     (cond_prob p A B = 0)``,
     RW_TAC std_ss [cond_prob_def, REAL_DIV_LZERO]);

val COND_PROB_INCREASING = store_thm
  ("COND_PROB_INCREASING",
  ``!A B C p. prob_space p /\ A IN events p /\ B IN events p /\ C IN events p ==>
   cond_prob p (A INTER B) C <= cond_prob p A C``,
    RW_TAC std_ss []
 >> Cases_on `prob p C = 0`
 >- METIS_TAC [EVENTS_INTER, COND_PROB_ZERO, REAL_LE_REFL]
 >> RW_TAC std_ss [cond_prob_def, real_div]
 >> `(A INTER B INTER C) SUBSET (A INTER C)` by PSET_TAC []
 >> METIS_TAC [PROB_POSITIVE, REAL_LT_LE, REAL_INV_POS, PROB_INCREASING,
    EVENTS_INTER, REAL_LE_RMUL]);

val POS_COND_PROB_IMP_POS_PROB = store_thm
  ("POS_COND_PROB_IMP_POS_PROB",
  ``!A B p. prob_space p /\ A IN events p /\ B IN events p /\
  	(0 < cond_prob p A B) ==> (prob p (A INTER B) <> 0)``,
    RW_TAC std_ss []
 >> `0 <= prob p B` by RW_TAC std_ss [PROB_POSITIVE]
 >> `prob p B <> 0` by (SPOSE_NOT_THEN STRIP_ASSUME_TAC
 	>> `cond_prob p A B = 0` by METIS_TAC [COND_PROB_ZERO]
 	>> METIS_TAC [REAL_LT_IMP_NE])
 >> FULL_SIMP_TAC std_ss [cond_prob_def]
 >> `0 / prob p B = 0` by METIS_TAC [REAL_DIV_LZERO]
 >> METIS_TAC [REAL_LT_IMP_NE]);

val COND_PROB_BOUNDS = store_thm
    ("COND_PROB_BOUNDS",
    (--`!p A B. prob_space p /\ A IN events p /\ B IN events p ==>
        0 <= cond_prob p A B /\ cond_prob p A B <= 1`--),
     RW_TAC std_ss []
  >- METIS_TAC [cond_prob_def, EVENTS_INTER, PROB_POSITIVE, REAL_LE_DIV]
  >> Cases_on `prob p B = 0` >- METIS_TAC [COND_PROB_ZERO, REAL_LE_01]
  >> `0 < prob p B` by METIS_TAC [PROB_POSITIVE, REAL_LT_LE]
  >> `(cond_prob p A B <= 1) = (cond_prob p A B * prob p B <= 1 * prob p B)`
  	by RW_TAC std_ss [REAL_LE_RMUL] >> POP_ORW
  >> RW_TAC std_ss [REAL_MUL_LID, cond_prob_def, REAL_DIV_RMUL]
  >> `(A INTER B) SUBSET B` by RW_TAC std_ss [INTER_SUBSET]
  >> FULL_SIMP_TAC std_ss [PROB_INCREASING, EVENTS_INTER]);

val COND_PROB_ITSELF = store_thm
  ("COND_PROB_ITSELF",
  (--`!p B. (prob_space p) /\(B IN events p) /\ (0 < prob p B) ==>
            ((cond_prob p B B = 1))`--),
	RW_TAC real_ss [cond_prob_def, INTER_IDEMPOT]
 >> `prob p B <> 0` by METIS_TAC [REAL_NEG_NZ]
 >> METIS_TAC [REAL_DIV_REFL]);

val COND_PROB_COMPL = store_thm
  ("COND_PROB_COMPL",
  (--`!A B p . (prob_space p) /\ (A IN events p) /\ (COMPL A IN events p) /\
               (B IN events p) /\ (0 < (prob p B)) ==>
        (cond_prob p (COMPL A) B = 1 - cond_prob p A B)`--),
    RW_TAC std_ss [cond_prob_def]
 >> `prob p B <> 0` by METIS_TAC [REAL_NEG_NZ]
 >> `(prob p (COMPL A INTER B) / prob p B = 1 - prob p (A INTER B) / prob p B) =
     (prob p (COMPL A INTER B) / prob p B * prob p B = (1 - prob p (A INTER B) / prob p B) * prob p B)`
     by METIS_TAC [REAL_EQ_RMUL] >> POP_ORW
 >> RW_TAC std_ss [REAL_DIV_RMUL, REAL_SUB_RDISTRIB, REAL_MUL_LID, REAL_EQ_SUB_LADD]
 >> `prob p ((COMPL A) INTER B) + prob p (A INTER B) =
       prob p (((COMPL A) INTER B) UNION (A INTER B))`
       by (ONCE_REWRITE_TAC [EQ_SYM_EQ] >> MATCH_MP_TAC PROB_ADDITIVE
          >> RW_TAC std_ss [EVENTS_INTER, DISJOINT_DEF, EXTENSION]
          >> RW_TAC std_ss [NOT_IN_EMPTY, IN_COMPL, IN_INTER] >> METIS_TAC []) >> POP_ORW
 >> `(COMPL A INTER B UNION A INTER B) = B`
        by (PSET_TAC [EXTENSION, IN_INTER, IN_UNION, IN_COMPL] >> METIS_TAC [])
 >> RW_TAC std_ss []);

(*===========================================================*)
val COND_PROB_DIFF = store_thm
  ("COND_PROB_DIFF",
  (--`!p A1 A2 B.(prob_space p) /\ (A1 IN events p) /\ (A2 IN events p) /\ (B IN events p) ==>
        (cond_prob p (A1 DIFF A2) B =
         cond_prob p A1 B - cond_prob p (A1 INTER A2) B)`--),
    RW_TAC std_ss []
 >> Cases_on `prob p B = 0`
 >- RW_TAC std_ss [COND_PROB_ZERO, REAL_SUB_RZERO, EVENTS_INTER, EVENTS_DIFF]
 >> RW_TAC std_ss [cond_prob_def]
 >> `(A1 DIFF A2) INTER B IN events p` by METIS_TAC [EVENTS_INTER, EVENTS_DIFF]
 >> `(prob p ((A1 DIFF A2) INTER B) / prob p B =
    prob p (A1 INTER B) / prob p B - prob p (A1 INTER A2 INTER B) / prob p B) =
    (prob p ((A1 DIFF A2) INTER B) / prob p B * prob p B =
    (prob p (A1 INTER B) / prob p B - prob p (A1 INTER A2 INTER B) / prob p B) * prob p B)`
    by METIS_TAC [REAL_EQ_RMUL] >> POP_ORW
 >> `A1 INTER B IN events p` by METIS_TAC [EVENTS_INTER]
 >> `A1 INTER A2 INTER B IN events p` by METIS_TAC [EVENTS_INTER]
 >> RW_TAC std_ss [REAL_DIV_RMUL, REAL_SUB_RDISTRIB, REAL_EQ_SUB_LADD]
 >> `prob p ((A1 DIFF A2) INTER B) + prob p (A1 INTER A2 INTER B) =
        prob p (((A1 DIFF A2) INTER B) UNION (A1 INTER A2 INTER B))`
        by (ONCE_REWRITE_TAC [EQ_SYM_EQ] >> MATCH_MP_TAC PROB_ADDITIVE
           >> RW_TAC std_ss [EVENTS_INTER, EVENTS_DIFF, DISJOINT_DEF, EXTENSION]
           >> RW_TAC std_ss [IN_DIFF, IN_INTER, NOT_IN_EMPTY] >> PROVE_TAC [])
 >> `((A1 DIFF A2) INTER B UNION A1 INTER A2 INTER B) = (A1 INTER B)`
        by (RW_TAC std_ss [EXTENSION, IN_INTER, IN_DIFF, IN_UNION] THEN PROVE_TAC [])
 >> RW_TAC std_ss []);

val COND_PROB_MUL_RULE = store_thm
  ("COND_PROB_MUL_RULE",
  (--`! p A B. (prob_space p) /\ (A IN events p) /\ (B IN events p) ==>
               (prob p (A INTER B) = (prob p B) * (cond_prob p A B))`--),
	RW_TAC std_ss [] THEN Cases_on `prob p B = 0` THEN1
		RW_TAC std_ss [COND_PROB_ZERO, REAL_MUL_RZERO, PROB_INTER_ZERO] THEN
	RW_TAC std_ss [cond_prob_def, REAL_DIV_LMUL]);

val COND_PROB_MUL_EQ = store_thm
  ("COND_PROB_MUL_EQ",
  ``!A B p. prob_space p /\ A IN events p /\ B IN events p ==>
        (cond_prob p A B * prob p B = cond_prob p B A * prob p A)``,
    RW_TAC std_ss []
 >> Cases_on `prob p B = 0`
 >- RW_TAC std_ss [REAL_MUL_RZERO, COND_PROB_INTER_ZERO, REAL_MUL_LZERO]
 >> Cases_on `prob p A = 0`
 >- RW_TAC std_ss [REAL_MUL_LZERO, COND_PROB_INTER_ZERO, REAL_MUL_RZERO]
 >> RW_TAC std_ss [cond_prob_def, REAL_DIV_RMUL, INTER_COMM]);

val COND_PROB_UNION = prove
  (``! p A1 A2 B.
  	(prob_space p) /\ (A1 IN events p) /\ (A2 IN events p) /\ (B IN events p)  ==>
	(cond_prob p (A1 UNION A2) B =
	(cond_prob p A1 B) + (cond_prob p A2 B) - (cond_prob p (A1 INTER A2) B))``,
    RW_TAC std_ss []
 >> `cond_prob p A1 B + cond_prob p A2 B = cond_prob p A2 B + cond_prob p A1 B`
        by RW_TAC std_ss [REAL_ADD_COMM] >> POP_ORW
 >> `cond_prob p A2 B + cond_prob p A1 B - cond_prob p (A1 INTER A2) B =
     cond_prob p A2 B + (cond_prob p A1 B - cond_prob p (A1 INTER A2) B)` by REAL_ARITH_TAC
 >> `cond_prob p A1 B - cond_prob p (A1 INTER A2) B = cond_prob p (A1 DIFF A2) B`
        by PROVE_TAC [COND_PROB_DIFF] >> RW_TAC std_ss []
 >> Cases_on `prob p B = 0`
 >- RW_TAC std_ss [COND_PROB_ZERO, EVENTS_DIFF, EVENTS_UNION, REAL_ADD_LID]
 >> `(cond_prob p (A1 UNION A2) B = cond_prob p A2 B + cond_prob p (A1 DIFF A2) B) =
     (cond_prob p (A1 UNION A2) B * prob p B =
        (cond_prob p A2 B + cond_prob p (A1 DIFF A2) B) * prob p B)` by METIS_TAC [REAL_EQ_RMUL]
 >> POP_ORW >> RW_TAC std_ss [REAL_DIV_RMUL, cond_prob_def, REAL_ADD_RDISTRIB]
 >> `(A1 UNION A2) INTER B IN events p` by METIS_TAC [EVENTS_UNION, EVENTS_INTER]
 >> `A2 INTER B IN events p` by METIS_TAC [EVENTS_INTER]
 >> `(A1 DIFF A2) INTER B IN events p` by METIS_TAC [EVENTS_INTER, EVENTS_DIFF]
 >> `prob p (A2 INTER B) + prob p ((A1 DIFF A2) INTER B) =
       prob p ((A2 INTER B) UNION ((A1 DIFF A2) INTER B))`
       by (ONCE_REWRITE_TAC [EQ_SYM_EQ] >> MATCH_MP_TAC PROB_ADDITIVE
          >> RW_TAC std_ss [EVENTS_INTER, EVENTS_DIFF, DISJOINT_DEF, EXTENSION]
          >> RW_TAC std_ss [IN_INTER, IN_DIFF, NOT_IN_EMPTY] >> PROVE_TAC [])
 >> `(A2 INTER B UNION (A1 DIFF A2) INTER B) = ((A1 UNION A2) INTER B)`
        by (RW_TAC std_ss [EXTENSION, IN_INTER, IN_DIFF, IN_UNION] THEN PROVE_TAC [])
 >> RW_TAC std_ss []);

val PROB_FINITE_ADDITIVE = store_thm
  ("PROB_FINITE_ADDITIVE",
  ``!s p f t. prob_space p /\ FINITE s /\ (!x. x IN s ==> f x IN events p) /\
       (!a b. (a:'b) IN s /\ b IN s /\ ~(a = b) ==> DISJOINT (f a) (f b)) /\
       (t = BIGUNION (IMAGE f s)) ==> (prob p t = SIGMA (prob p o f) s)``,
    Suff `!s. FINITE (s:'b -> bool) ==>
	((\s. !p f t. prob_space p  /\ (!x. x IN s ==> f x IN events p) /\
	(!a b. a IN s /\ b IN s /\ a <> b ==> DISJOINT (f a) (f b)) /\
	(t = BIGUNION (IMAGE f s)) ==> (prob p t = SIGMA (prob p o f) s)) s)` >- METIS_TAC []
 >> MATCH_MP_TAC FINITE_INDUCT >> RW_TAC std_ss [IMAGE_EMPTY]
 >- RW_TAC std_ss [REAL_SUM_IMAGE_THM, BIGUNION_EMPTY, PROB_EMPTY]
 >> `SIGMA (prob p o f) ((e:'b) INSERT s) = (prob p o f) e + SIGMA (prob p o f) (s DELETE e)`
	by RW_TAC std_ss [REAL_SUM_IMAGE_THM]
 >> `s DELETE (e:'b) = s` by FULL_SIMP_TAC std_ss [DELETE_NON_ELEMENT]
 >> RW_TAC std_ss [IMAGE_INSERT, BIGUNION_INSERT]
 >> `DISJOINT (f e)  (BIGUNION (IMAGE f s))`
        by (PSET_TAC [DISJOINT_BIGUNION, IN_IMAGE]
           >> `e IN e INSERT s` by FULL_SIMP_TAC std_ss [INSERT_THM1]
           >> `x IN e INSERT s` by FULL_SIMP_TAC std_ss [INSERT_THM2]
           >> `e <> x` by PSET_TAC [] >- METIS_TAC [] >> FULL_SIMP_TAC std_ss [])
 >> `(f e) IN events p` by FULL_SIMP_TAC std_ss [IN_FUNSET, INSERT_THM1]
 >> `BIGUNION (IMAGE f s) IN events p`
        by (MATCH_MP_TAC EVENTS_COUNTABLE_UNION >> RW_TAC std_ss []
           >- (RW_TAC std_ss [SUBSET_DEF,IN_IMAGE] THEN METIS_TAC [IN_INSERT])
           >> MATCH_MP_TAC COUNTABLE_IMAGE >> RW_TAC std_ss [FINITE_COUNTABLE])
 >> `(prob p (f e UNION BIGUNION (IMAGE f s))) = prob p (f e) + prob p (BIGUNION (IMAGE f s))`
        by (MATCH_MP_TAC PROB_ADDITIVE >> FULL_SIMP_TAC std_ss [])
 >> RW_TAC std_ss [INSERT_THM1, INSERT_THM2]);

val COND_PROB_FINITE_ADDITIVE = store_thm
  ("COND_PROB_FINITE_ADDITIVE",
  ``!p B A s. (prob_space p) /\ (B IN events p) /\ (A IN ((count n) -> events p)) /\
	(s = BIGUNION (IMAGE A (count n))) /\
        (!a b. a <> b ==> DISJOINT (A a) (A b)) ==>
        (cond_prob p s B = SIGMA (\i. cond_prob p (A i) B) (count n))``,
    RW_TAC std_ss [IN_FUNSET, IN_COUNT]
 >> `0 <= prob p (B:'a -> bool)` by RW_TAC std_ss [PROB_POSITIVE]
 >> `BIGUNION (IMAGE A (count n)) IN events p` by METIS_TAC [EVENTS_BIGUNION, IN_FUNSET, IN_COUNT]
 >> Cases_on `prob p (B:'a -> bool) = 0`
 >- (`0 = SIGMA (\i. (0:real)) (count n)`
        by ((MP_TAC o GSYM o Q.ISPEC `count n`) REAL_SUM_IMAGE_0 >> RW_TAC std_ss [FINITE_COUNT])
    >> RW_TAC std_ss [COND_PROB_ZERO] >> POP_ORW
    >> (MATCH_MP_TAC o Q.ISPEC `count n`) REAL_SUM_IMAGE_EQ
    >> PSET_TAC [FINITE_COUNT, IN_COUNT, COND_PROB_ZERO])
 >> `prob p B * SIGMA (\i. cond_prob p (A i) B) (count n) =
        SIGMA (\i. prob p B * cond_prob p (A i) B) (count n)`
        by ((MP_TAC o Q.ISPEC `count n`) REAL_SUM_IMAGE_CMUL >> RW_TAC std_ss [FINITE_COUNT])
 >> `(cond_prob p (BIGUNION (IMAGE A (count n))) B = SIGMA (\i. cond_prob p (A i) B) (count n)) =
     (prob p B * cond_prob p (BIGUNION (IMAGE A (count n))) B =
      prob p B * SIGMA (\i. cond_prob p (A i) B) (count n))`
     by METIS_TAC [REAL_EQ_LMUL] >> RW_TAC std_ss [cond_prob_def, REAL_DIV_LMUL]
 >> `SIGMA (\i. prob p (A i INTER B)) (count n) = SIGMA (prob p o (\i. A i INTER B)) (count n)`
	by METIS_TAC [] >> POP_ORW
 >> `BIGUNION (IMAGE A (count n)) INTER B = BIGUNION (IMAGE (\i. A i INTER B) (count n))`
        by (PSET_TAC [INTER_COMM, INTER_BIGUNION, EXTENSION, IN_IMAGE] >> METIS_TAC [])	>> POP_ORW
 >> RW_TAC std_ss [GSYM REAL_SUM_IMAGE_EQ_sum]
 >> `!(x:real) y. (x = y) = (y = x)` by RW_TAC std_ss [EQ_SYM_EQ] >> POP_ORW
 >> MATCH_MP_TAC PROB_FINITELY_ADDITIVE
 >> PSET_TAC [DISJOINT_DEF, IN_FUNSET, IN_COUNT, EVENTS_INTER, THREE_SETS_INTER, INTER_EMPTY]);

val BAYES_RULE = store_thm
  ("BAYES_RULE",
  (--`!A B p. (prob_space p) /\ (A IN events p) /\ (B IN events p) ==>
	(cond_prob p B A = ((cond_prob p A B) * prob p B)/(prob p A))`--),
    RW_TAC std_ss []
 >> Cases_on `prob p B = 0`
 >- RW_TAC std_ss [COND_PROB_ZERO, COND_PROB_INTER_ZERO, REAL_MUL_LZERO, REAL_DIV_LZERO]
 >> `!(x:real) y z w. x * y * z * w = x * (y * z) * w` by METIS_TAC [REAL_MUL_ASSOC]
 >> RW_TAC std_ss [cond_prob_def, real_div, REAL_DIV_RMUL, INTER_COMM, REAL_MUL_LINV, REAL_MUL_RID]);

val TOTAL_PROB_SIGMA = store_thm
  ("TOTAL_PROB_SIGMA",
  ``!p B A s. (prob_space p) /\ (A IN events p) /\ FINITE s /\
	(!x . x IN s ==> B x IN events p) /\
        (!a b. a IN s /\ b IN s /\ ~(a = b) ==> DISJOINT (B a) (B b)) /\
        (BIGUNION (IMAGE B s) = p_space p) ==>
        (prob p A = SIGMA (\i. (prob p (B i))* (cond_prob p A (B i))) s)``,
    RW_TAC std_ss []
 >> `SIGMA (\i. prob p (B i) * cond_prob p A (B i)) (s:'b -> bool) =
        SIGMA (\i. prob p (A INTER (B i))) s `
        by ((MATCH_MP_TAC o Q.ISPEC `s:'b -> bool`) REAL_SUM_IMAGE_EQ >> RW_TAC std_ss []
	   >> Cases_on `prob p (B x) = 0` >- RW_TAC std_ss [REAL_MUL_LZERO, PROB_INTER_ZERO]
	   >> RW_TAC std_ss [cond_prob_def, REAL_DIV_LMUL])
 >> RW_TAC std_ss [] >> MATCH_MP_TAC PROB_REAL_SUM_IMAGE_FN
 >> RW_TAC std_ss [EVENTS_INTER, INTER_IDEMPOT]);

val BAYES_RULE_GENERAL_SIGMA = store_thm
  ("BAYES_RULE_GENERAL_SIGMA",
  (--`!A B s k p. (prob_space p) /\ (A IN events p) /\ FINITE s /\
	(!x . x IN s ==> B x IN events p) /\ (k IN s) /\
        (!a b. a IN s /\ b IN s /\ ~(a = b) ==> DISJOINT (B a) (B b)) /\
        (BIGUNION (IMAGE B s) = p_space p) ==>
        (cond_prob p (B k) A = ((cond_prob p A (B k)) * prob p (B k))/
                (SIGMA (\i. (prob p (B i)) * (cond_prob p A (B i)))) s)`--),
	RW_TAC std_ss [GSYM TOTAL_PROB_SIGMA] THEN MATCH_MP_TAC BAYES_RULE THEN
	RW_TAC std_ss [] THEN POP_ASSUM MP_TAC THEN NTAC 3 (POP_ASSUM K_TAC) THEN
	POP_ASSUM MP_TAC THEN RW_TAC std_ss [IN_FUNSET, IN_COUNT]);

val COND_PROB_ADDITIVE = store_thm
  ("COND_PROB_ADDITIVE",
  ``!p B A s. (prob_space p) /\ FINITE s /\ (B IN events p) /\
        (!x. x IN s ==> A x IN events p) /\ (0 < prob p B) /\
	(!x y. x IN s /\ y IN s /\ x <> y ==> DISJOINT (A x) (A y)) /\
        (BIGUNION (IMAGE A s) = p_space p) ==>
        (SIGMA (\i. cond_prob p (A i) B) s = 1)``,
    RW_TAC std_ss [] >> `prob p B <> 0` by METIS_TAC [REAL_LT_LE]
 >> `(SIGMA (\i. cond_prob p (A i) B) (s:'b -> bool) = 1) =
     (prob p B * SIGMA (\i. cond_prob p (A i) B) s = prob p B * 1)`
     by METIS_TAC [REAL_EQ_MUL_LCANCEL] >> POP_ORW
 >> `prob p B * SIGMA (\i. cond_prob p (A i) B) (s:'b -> bool) =
        SIGMA (\i. prob p B * cond_prob p (A i) B) s`
        by ((MP_TAC o Q.ISPEC `s:'b -> bool`) REAL_SUM_IMAGE_CMUL >> RW_TAC std_ss [])
 >> RW_TAC std_ss [cond_prob_def, REAL_DIV_LMUL, REAL_MUL_RID, EQ_SYM_EQ, INTER_COMM]
 >> MATCH_MP_TAC PROB_REAL_SUM_IMAGE_FN
 >> RW_TAC std_ss [INTER_IDEMPOT, EVENTS_INTER]);

val COND_PROB_SWAP = store_thm
  ("COND_PROB_SWAP",
  ``!A B C p.
        prob_space p /\ A IN events p /\ B IN events p /\ C IN events p ==>
        (cond_prob p A (B INTER C) * cond_prob p B C =
         cond_prob p B (A INTER C) * cond_prob p A C)``,
    RW_TAC std_ss [] >> `B INTER C IN events p` by METIS_TAC [EVENTS_INTER]
 >> `A INTER B IN events p` by METIS_TAC [EVENTS_INTER]
 >> `A INTER C IN events p` by METIS_TAC [EVENTS_INTER]
 >> `A INTER (B INTER C) = B INTER (A INTER C)` by METIS_TAC [INTER_ASSOC', INTER_COMM]
 >> Cases_on `prob p C = 0`
 >- RW_TAC std_ss [COND_PROB_ZERO, REAL_MUL_RZERO]
 >> `0 < prob p C` by METIS_TAC [PROB_POSITIVE, REAL_LT_LE]
 >> Cases_on `prob p (B INTER C) = 0`
 >- (`cond_prob p B C = 0` by RW_TAC std_ss [cond_prob_def, REAL_DIV_LZERO]
    >> Cases_on `prob p (A INTER C) = 0`
    >- RW_TAC std_ss [COND_PROB_ZERO, REAL_MUL_RZERO, REAL_MUL_LZERO]
    >> `B INTER (A INTER C) = A INTER (B INTER C)` by METIS_TAC [INTER_ASSOC', INTER_COMM]
    >> `0 < prob p (A INTER C)` by METIS_TAC [PROB_POSITIVE,  REAL_LT_LE]
    >> `cond_prob p B (A INTER C) = 0`
        by RW_TAC std_ss [cond_prob_def, PROB_INTER_ZERO, REAL_DIV_LZERO]
    >> RW_TAC std_ss [REAL_MUL_LZERO, REAL_MUL_RZERO])
 >> Cases_on `prob p (A INTER C) = 0`
 >- (RW_TAC std_ss [COND_PROB_ZERO, REAL_MUL_LZERO]
    >> `0 < prob p (B INTER C)` by METIS_TAC [PROB_POSITIVE, REAL_LT_LE]
    >> `prob p (A INTER (B INTER C)) = 0` by METIS_TAC [PROB_INTER_ZERO]
    >> RW_TAC std_ss [cond_prob_def, REAL_DIV_LZERO, REAL_MUL_LZERO])
 >> `!(a:real) b c d. a * b * (c * d) = a * (b * c) * d` by METIS_TAC [REAL_MUL_ASSOC]
 >> RW_TAC std_ss [cond_prob_def, real_div, REAL_MUL_LINV, REAL_MUL_RID]
 >> METIS_TAC []);

val PROB_INTER_SPLIT = store_thm
  ("PROB_INTER_SPLIT",
  ``!A B C p.
        prob_space p /\ A IN events p /\ B IN events p /\ C IN events p ==>
        (prob p (A INTER B INTER C) =
         cond_prob p A (B INTER C) * cond_prob p B C * prob p C)``,
    RW_TAC std_ss [] >> `B INTER C IN events p` by METIS_TAC [EVENTS_INTER]
 >> `A INTER B IN events p` by METIS_TAC [EVENTS_INTER]
 >> Cases_on `prob p C = 0`
 >- RW_TAC std_ss [PROB_INTER_ZERO, REAL_MUL_RZERO]
 >> Cases_on `prob p (B INTER C) = 0`
 >- RW_TAC std_ss [INTER_ASSOC', PROB_INTER_ZERO, COND_PROB_ZERO, REAL_MUL_LZERO]
 >> `!(a:real) b c d e. a * b * (c * d) * e = a * (b * c) * (d * e)` by METIS_TAC [REAL_MUL_ASSOC]
 >> RW_TAC std_ss [cond_prob_def, real_div, REAL_MUL_LINV, REAL_MUL_LID, REAL_MUL_RID, INTER_ASSOC']);

val COND_PROB_INTER_SPLIT = store_thm
  ("COND_PROB_INTER_SPLIT",
  ``!A B C p.
        prob_space p /\ A IN events p /\ B IN events p /\ C IN events p ==>
        (cond_prob p (A INTER B) C = cond_prob p A (B INTER C) * cond_prob p B C)``,
    RW_TAC std_ss []
 >> Cases_on `prob p C = 0`
 >- (`A INTER B IN events p` by METIS_TAC [EVENTS_INTER]
    >> RW_TAC std_ss [COND_PROB_ZERO, REAL_MUL_RZERO])
 >> Cases_on `prob p (B INTER C) = 0`
 >- (`A INTER B INTER C IN events p` by METIS_TAC [EVENTS_INTER]
    >> `B INTER C IN events p` by METIS_TAC [EVENTS_INTER]
    >> `0 < prob p C` by METIS_TAC [PROB_POSITIVE, REAL_LT_LE]
    >> RW_TAC std_ss [COND_PROB_ZERO, REAL_MUL_LZERO, cond_prob_def, INTER_ASSOC',
        PROB_INTER_ZERO, REAL_DIV_LZERO])
 >> `!(x:real) y z w. x * y * (z * w) = x * (y * z) * w`
        by METIS_TAC [REAL_MUL_ASSOC, REAL_MUL_COMM]
 >> RW_TAC std_ss [cond_prob_def, real_div, INTER_ASSOC, REAL_MUL_LINV, REAL_MUL_RID]);

val _ = export_theory();
