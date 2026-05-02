(* ------------------------------------------------------------------------- *)
(* Probability Theory                                                        *)
(* Authors: Tarek Mhamdi, Osman Hasan, Sofiene Tahar                         *)
(* HVG Group, Concordia University, Montreal                                 *)
(* ------------------------------------------------------------------------- *)
(* Based on the work of Aaron Coble, Cambridge University                    *)
(* ------------------------------------------------------------------------- *)

(*

val () = app load
 ["bossLib", "metisLib", "arithmeticTheory", "pred_setTheory", "realLib", "pairTheory",
   "seqTheory", "transcTheory", "util_probTheory", "extreal_hvgTheory", 
   "prim_recTheory", "measure_hvgTheory", "lebesgue_hvgTheory"];

set_trace "Unicode" 0;

*)

open HolKernel Parse boolLib bossLib metisLib
     combinTheory pred_setTheory arithmeticTheory realTheory realLib pairTheory 
      seqTheory transcTheory real_sigmaTheory jrhUtils util_probTheory
      extreal_hvgTheory prim_recTheory measure_hvgTheory lebesgue_hvgTheory;

val _ = new_theory "probability_hvg";

infixr 0 ++ << || ORELSEC ## --> THENC;
infix 1 >> |->;

val !! = REPEAT;
val op++ = op THEN;
val op<< = op THENL;
val op|| = op ORELSE;
val op>> = op THEN1;

(* ------------------------------------------------------------------------- *)
(* Tools.                                                                    *)
(* ------------------------------------------------------------------------- *)

fun parse_with_goal t (asms, g) =
  let
    val ctxt = free_varsl (g::asms)
  in
    Parse.parse_in_context ctxt t
  end;


val PARSE_TAC = fn tac => fn q => W (tac o parse_with_goal q);
val Reverse = Tactical.REVERSE
val Strip = !! (POP_ASSUM MP_TAC) ++ !! STRIP_TAC;
val Simplify = RW_TAC arith_ss;
val Suff = PARSE_TAC SUFF_TAC;
val Know = PARSE_TAC KNOW_TAC;
fun wrap a = [a];
val Rewr = DISCH_THEN (REWRITE_TAC o wrap);
val Rewr' = DISCH_THEN (ONCE_REWRITE_TAC o wrap);
val STRONG_DISJ_TAC = CONV_TAC (REWR_CONV (GSYM IMP_DISJ_THM)) ++ STRIP_TAC;
val Cond =
  DISCH_THEN
  (fn mp_th =>
   let
     val cond = fst (dest_imp (concl mp_th))
   in
     KNOW_TAC cond << [ALL_TAC, DISCH_THEN (MP_TAC o MP mp_th)]
   end);

val POP_ORW = POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm]);

fun K_TAC _ = ALL_TAC;
val KILL_TAC = POP_ASSUM_LIST K_TAC;

local
  val th = prove (``!a b. a /\ (a ==> b) ==> a /\ b``, PROVE_TAC [])
in
  val STRONG_CONJ_TAC :tactic = MATCH_MP_TAC th ++ CONJ_TAC
end;

val FUN_EQ_TAC = CONV_TAC (CHANGED_CONV (ONCE_DEPTH_CONV FUN_EQ_CONV));

val FUN_EQ = prove (``!f g. (f = g) = (!x. f x = g x)``, PROVE_TAC [EQ_EXT]);
val SET_EQ = prove (``!s t. (s = t) = (!x. x IN s = x IN t)``,
                    PROVE_TAC [SPECIFICATION, FUN_EQ]);
val SET_EQ_CONV = REWR_CONV SET_EQ;
val SET_EQ_TAC = CONV_TAC (CHANGED_CONV (ONCE_DEPTH_CONV SET_EQ_CONV));

(* ------------------------------------------------------------------------- *)
(* Basic probability theory definitions.                                     *)
(* ------------------------------------------------------------------------- *)

val p_space_def = Define `p_space = m_space`;

val events_def = Define `events = measurable_sets`;

val prob_def = Define `prob = measure`;

val prob_space_def = Define
  `prob_space p = measure_space p /\ (measure p (p_space p) = 1)`;

val indep_def = Define
  `indep p a b =
   a IN events p /\ b IN events p /\
   (prob p (a INTER b) = prob p a * prob p b)`;

val probably_def = Define `probably p e = (e IN events p) /\ (prob p e = 1)`;

val possibly_def = Define `possibly p e = (e IN events p) /\ ~(prob p e = 0)`;

val random_variable_def = Define
   `random_variable X p s = prob_space p /\ X IN measurable (p_space p, events p) s`;

val real_random_variable_def = Define
   `real_random_variable X p = prob_space p /\ X IN measurable (p_space p, events p) Borel`;

val distribution_def = Define
   `distribution p X = (\s. prob p ((PREIMAGE X s) INTER (p_space p)))`;

val joint_distribution_def = Define
   `joint_distribution p X Y = (\a. prob p (PREIMAGE (\x. (X x, Y x)) a INTER p_space p))`;

val expectation_def = Define
   `expectation = integral`;

val conditional_expectation_def = Define
   `conditional_expectation p X s =
	@f. real_random_variable f p /\
	    !g. g IN s ==>
		(integral p (\x. f x * indicator_fn g x) =
		 integral p (\x. X x * indicator_fn g x))`;

val conditional_prob_def = Define
   `conditional_prob p e1 e2 = conditional_expectation p (indicator_fn e1) e2`;

val rv_conditional_expectation_def = Define
   `rv_conditional_expectation p s X Y = conditional_expectation p X (IMAGE (\a. (PREIMAGE Y a) INTER p_space p) (subsets s))`;

(* ------------------------------------------------------------------------- *)
(* Basic probability theorems, leading to:                                   *)
(* 1. s IN events p ==> (prob p (COMPL s) = 1 - prob p s)                    *)
(* ------------------------------------------------------------------------- *)

val POSITIVE_PROB = store_thm
  ("POSITIVE_PROB", ``!p. positive p = (prob p {} = 0) /\ !s. s IN events p ==> 0 <= prob p s``,
   RW_TAC std_ss [positive_def, prob_def, events_def]);

val INCREASING_PROB = store_thm
  ("INCREASING_PROB", ``!p. increasing p = !s t. s IN events p /\ t IN events p /\ s SUBSET t ==> prob p s <= prob p t``,
   RW_TAC std_ss [increasing_def, prob_def, events_def]);

val ADDITIVE_PROB = store_thm
  ("ADDITIVE_PROB", ``!p. additive p = !s t. s IN events p /\ t IN events p /\ DISJOINT s t ==>
         (prob p (s UNION t) = prob p s + prob p t)``,
   RW_TAC std_ss [additive_def, prob_def, events_def]);

val COUNTABLY_ADDITIVE_PROB = store_thm
  ("COUNTABLY_ADDITIVE_PROB", ``!p. countably_additive p =
       !f. f IN (UNIV -> events p) /\ (!m n. ~(m = n) ==> DISJOINT (f m) (f n)) /\ BIGUNION (IMAGE f UNIV) IN events p ==>
         (prob p (BIGUNION (IMAGE f UNIV)) = suminf (prob p o f))``,
   RW_TAC std_ss [countably_additive_def, prob_def, events_def]);

val PROB_SPACE = store_thm
 ("PROB_SPACE", ``!p. prob_space p = sigma_algebra (p_space p, events p) /\ positive p /\ countably_additive p /\ (prob p (p_space p) = 1)``,
   RW_TAC std_ss [prob_space_def, prob_def, events_def, measure_space_def, p_space_def]
   ++ PROVE_TAC []);

val EVENTS_SIGMA_ALGEBRA = store_thm
  ("EVENTS_SIGMA_ALGEBRA",
   ``!p. prob_space p ==> sigma_algebra (p_space p, events p)``,
   RW_TAC std_ss [PROB_SPACE]);

val EVENTS_ALGEBRA = store_thm
  ("EVENTS_ALGEBRA",
   ``!p. prob_space p ==> algebra (p_space p, events p)``,
   PROVE_TAC [SIGMA_ALGEBRA_ALGEBRA, EVENTS_SIGMA_ALGEBRA]);

val PROB_EMPTY = store_thm
  ("PROB_EMPTY",
   ``!p. prob_space p ==> (prob p {} = 0)``,
   PROVE_TAC [PROB_SPACE, POSITIVE_PROB]);

val PROB_UNIV = store_thm
  ("PROB_UNIV",
   ``!p. prob_space p ==> (prob p (p_space p) = 1)``,
   RW_TAC std_ss [PROB_SPACE]);

val PROB_SPACE_POSITIVE = store_thm
  ("PROB_SPACE_POSITIVE",
   ``!p. prob_space p ==> positive p``,
   RW_TAC std_ss [PROB_SPACE]);

val PROB_SPACE_COUNTABLY_ADDITIVE = store_thm
  ("PROB_SPACE_COUNTABLY_ADDITIVE",
   ``!p. prob_space p ==> countably_additive p``,
   RW_TAC std_ss [PROB_SPACE]);

val PROB_SPACE_ADDITIVE = store_thm
  ("PROB_SPACE_ADDITIVE",
   ``!p. prob_space p ==> additive p``,
   PROVE_TAC [PROB_SPACE_COUNTABLY_ADDITIVE, COUNTABLY_ADDITIVE_ADDITIVE,
              PROB_SPACE_POSITIVE, EVENTS_ALGEBRA, events_def, p_space_def]);

val PROB_SPACE_INCREASING = store_thm
  ("PROB_SPACE_INCREASING",
   ``!p. prob_space p ==> increasing p``,
   PROVE_TAC [ADDITIVE_INCREASING, EVENTS_ALGEBRA, PROB_SPACE_ADDITIVE,
              PROB_SPACE_POSITIVE, events_def, p_space_def]);

val PROB_POSITIVE = store_thm
  ("PROB_POSITIVE",
   ``!p s. prob_space p /\ s IN events p ==> 0 <= prob p s``,
   PROVE_TAC [POSITIVE_PROB, PROB_SPACE_POSITIVE]);

val PROB_INCREASING = store_thm
  ("PROB_INCREASING",
   ``!p s t.
       prob_space p /\ s IN events p /\ t IN events p /\ s SUBSET t ==>
       prob p s <= prob p t``,
   PROVE_TAC [INCREASING_PROB, PROB_SPACE_INCREASING]);

val PROB_ADDITIVE = store_thm
  ("PROB_ADDITIVE",
   ``!p s t u.
       prob_space p /\ s IN events p /\ t IN events p /\
       DISJOINT s t /\ (u = s UNION t) ==>
       (prob p u = prob p s + prob p t)``,
   PROVE_TAC [ADDITIVE_PROB, PROB_SPACE_ADDITIVE]);

val PROB_COUNTABLY_ADDITIVE = store_thm
  ("PROB_COUNTABLY_ADDITIVE",
   ``!p s f.
       prob_space p /\ f IN (UNIV -> events p) /\
       (!m n. ~(m = n) ==> DISJOINT (f m) (f n)) /\
       (s = BIGUNION (IMAGE f UNIV)) ==>
       (prob p s = suminf (prob p o f))``,
   RW_TAC std_ss []
   ++ Suff `BIGUNION (IMAGE f UNIV) IN events p`
   >> PROVE_TAC [COUNTABLY_ADDITIVE_PROB, PROB_SPACE_COUNTABLY_ADDITIVE]
   ++ (MATCH_MP_TAC o REWRITE_RULE [subsets_def, space_def] o
	Q.SPECL [`(p_space p, events p)`,`f`]) SIGMA_ALGEBRA_ENUM
   ++ PROVE_TAC [EVENTS_SIGMA_ALGEBRA]);

val PROB_FINITE = store_thm
("PROB_FINITE", ``!p s. prob_space p /\ s IN events p ==> (prob p s <> NegInf /\ prob p s <> PosInf)``,
  RW_TAC std_ss [prob_space_def,prob_def,events_def,positive_not_infty,MEASURE_SPACE_POSITIVE]
  ++ RW_TAC std_ss [GSYM le_infty,GSYM extreal_lt_def]
  ++ MATCH_MP_TAC let_trans
  ++ Q.EXISTS_TAC `measure p (p_space p)`
  ++ REVERSE (RW_TAC std_ss [])
  >> METIS_TAC [num_not_infty,lt_infty]
  ++ METIS_TAC [MEASURE_SPACE_SUBSET_MSPACE,INCREASING,MEASURE_SPACE_INCREASING,MEASURE_SPACE_MSPACE_MEASURABLE,p_space_def]);

val PROB_COMPL = store_thm
 ("PROB_COMPL", ``!p s. prob_space p /\ s IN events p ==> (prob p (p_space p DIFF s) = 1 - prob p s)``,
  METIS_TAC [MEASURE_SPACE_FINITE_DIFF,PROB_FINITE,prob_space_def,events_def,prob_def,p_space_def]);

val PROB_INDEP = store_thm
("PROB_INDEP", ``!p s t u. indep p s t /\ (u = s INTER t) ==> (prob p u = prob p s * prob p t)``,
  RW_TAC std_ss [indep_def]);

val PSPACE = store_thm
("PSPACE", ``!a b c. p_space (a, b, c) = a``,
  RW_TAC std_ss [p_space_def, m_space_def]);

val EVENTS = store_thm
("EVENTS", ``!a b c. events (a, b, c) = b``,
  RW_TAC std_ss [events_def, measurable_sets_def]);

val PROB = store_thm
("PROB", ``!a b c. prob (a, b, c) = c``,
  RW_TAC std_ss [prob_def, measure_def]);

val EVENTS_INTER = store_thm
("EVENTS_INTER", ``!p s t. prob_space p /\ s IN events p /\ t IN events p ==> s INTER t IN events p``,
  RW_TAC std_ss []
  ++ (MATCH_MP_TAC o REWRITE_RULE [subsets_def, space_def] o
      Q.SPEC `(p_space p, events p)`) ALGEBRA_INTER
  ++ PROVE_TAC [PROB_SPACE, SIGMA_ALGEBRA_ALGEBRA]);

val EVENTS_EMPTY = store_thm
("EVENTS_EMPTY", ``!p. prob_space p ==> {} IN events p``,
  RW_TAC std_ss []
  ++ (MATCH_MP_TAC o REWRITE_RULE [subsets_def, space_def] o
      Q.SPEC `(p_space p, events p)`) ALGEBRA_EMPTY
  ++ PROVE_TAC [SIGMA_ALGEBRA_ALGEBRA, PROB_SPACE]);

val EVENTS_SPACE = store_thm
("EVENTS_SPACE", ``!p. prob_space p ==> (p_space p) IN events p``,
  RW_TAC std_ss []
  ++ (MATCH_MP_TAC o REWRITE_RULE [subsets_def, space_def] o
      Q.SPEC `(p_space p, events p)`) ALGEBRA_SPACE
  ++ PROVE_TAC [SIGMA_ALGEBRA_ALGEBRA, PROB_SPACE]);

val EVENTS_UNION = store_thm
("EVENTS_UNION", ``!p s t. prob_space p /\ s IN events p /\ t IN events p ==> s UNION t IN events p``,
  RW_TAC std_ss []
  ++ (MATCH_MP_TAC o REWRITE_RULE [subsets_def, space_def] o
      Q.SPEC `(p_space p, events p)`) ALGEBRA_UNION
  ++ PROVE_TAC [PROB_SPACE, SIGMA_ALGEBRA_ALGEBRA]);

val INDEP_EMPTY = store_thm
("INDEP_EMPTY", ``!p s. prob_space p /\ s IN events p ==> indep p {} s``,
  RW_TAC std_ss [indep_def, EVENTS_EMPTY, PROB_EMPTY, INTER_EMPTY,mul_lzero]);

val INTER_PSPACE = store_thm
("INTER_PSPACE", ``!p s. prob_space p /\ s IN events p ==> (p_space p INTER s = s)``,
  RW_TAC std_ss [PROB_SPACE, SIGMA_ALGEBRA, space_def, subsets_def, subset_class_def, SUBSET_DEF]
  ++ RW_TAC std_ss [Once EXTENSION, IN_INTER]
  ++ PROVE_TAC []);

val INDEP_SPACE = store_thm
("INDEP_SPACE", ``!p s. prob_space p /\ s IN events p ==> indep p (p_space p) s``,
  RW_TAC std_ss [indep_def, EVENTS_SPACE, PROB_UNIV, INTER_PSPACE,mul_lone]);

val EVENTS_DIFF = store_thm
("EVENTS_DIFF", ``!p s t. prob_space p /\ s IN events p /\ t IN events p ==> s DIFF t IN events p``,
  RW_TAC std_ss []
  ++ (MATCH_MP_TAC o REWRITE_RULE [subsets_def, space_def] o
      Q.SPEC `(p_space p, events p)`) ALGEBRA_DIFF
  ++ PROVE_TAC [PROB_SPACE, SIGMA_ALGEBRA_ALGEBRA]);

val EVENTS_COMPL = store_thm
("EVENTS_COMPL", ``!p s. prob_space p /\ s IN events p ==> (p_space p) DIFF s IN events p``,
  RW_TAC std_ss []
  ++ (MATCH_MP_TAC o REWRITE_RULE [subsets_def, space_def] o
      Q.SPEC `(p_space p, events p)`) ALGEBRA_COMPL
  ++ PROVE_TAC [PROB_SPACE, SIGMA_ALGEBRA_ALGEBRA]);

val EVENTS_COUNTABLE_UNION = store_thm
("EVENTS_COUNTABLE_UNION", ``!p c. prob_space p /\ c SUBSET events p /\ countable c ==> BIGUNION c IN events p``,
  RW_TAC std_ss []
  ++ (MATCH_MP_TAC o REWRITE_RULE [subsets_def, space_def] o
      Q.SPEC `(p_space p, events p)`) SIGMA_ALGEBRA_COUNTABLE_UNION
  ++ RW_TAC std_ss [EVENTS_SIGMA_ALGEBRA]);

val PROB_ZERO_UNION = store_thm
("PROB_ZERO_UNION", ``!p s t. prob_space p /\ s IN events p /\ t IN events p /\ (prob p t = 0) ==> (prob p (s UNION t) = prob p s)``,
  RW_TAC std_ss []
  ++ Know `t DIFF s IN events p`
  >> (MATCH_MP_TAC EVENTS_DIFF
      ++ RW_TAC std_ss [])
  ++ STRIP_TAC
  ++ Know `prob p (t DIFF s) = 0`
  >> (ONCE_REWRITE_TAC [GSYM le_antisym]
      ++ REVERSE CONJ_TAC >> PROVE_TAC [PROB_POSITIVE]
      ++ Q.PAT_X_ASSUM `prob p t = 0` (ONCE_REWRITE_TAC o wrap o SYM)
      ++ MATCH_MP_TAC PROB_INCREASING
      ++ RW_TAC std_ss [DIFF_SUBSET])
  ++ STRIP_TAC
  ++ Suff `prob p (s UNION t) = prob p s + prob p (t DIFF s)`
  >> RW_TAC real_ss [add_rzero]
  ++ MATCH_MP_TAC PROB_ADDITIVE
  ++ RW_TAC std_ss [DISJOINT_DEF, DIFF_DEF, EXTENSION, IN_UNION, IN_DIFF, NOT_IN_EMPTY, IN_INTER]
  ++ PROVE_TAC []);

val PROB_EQ_COMPL = store_thm
("PROB_EQ_COMPL", ``!p s t. prob_space p /\ s IN events p /\ t IN events p /\ (prob p (p_space p DIFF s) = prob p (p_space p DIFF t)) ==> (prob p s = prob p t)``,
  RW_TAC std_ss []
  ++ Know `1 - prob p s = 1 - prob p t`
  >> (POP_ASSUM MP_TAC
      ++ RW_TAC std_ss [PROB_COMPL])
  ++ `?r1 r2. (prob p t = Normal r1) /\ (prob p s = Normal r2)` by METIS_TAC [extreal_cases,PROB_FINITE]
  ++ FULL_SIMP_TAC std_ss [extreal_of_num_def,extreal_sub_def,extreal_11]
  ++ REAL_ARITH_TAC);

val PROB_ONE_INTER = store_thm
("PROB_ONE_INTER", ``!p s t. prob_space p /\ s IN events p /\ t IN events p /\ (prob p t = 1) ==> (prob p (s INTER t) = prob p s)``,
  RW_TAC std_ss []
  ++ MATCH_MP_TAC PROB_EQ_COMPL
  ++ RW_TAC std_ss [EVENTS_INTER]
  ++ Know `p_space p DIFF s INTER t = (p_space p DIFF s) UNION (p_space p DIFF t)`
  >> (RW_TAC std_ss [Once EXTENSION, IN_INTER, IN_UNION, IN_DIFF]
      ++ DECIDE_TAC)
  ++ RW_TAC std_ss [] ++ POP_ASSUM (K ALL_TAC)
  ++ MATCH_MP_TAC PROB_ZERO_UNION
  ++ RW_TAC std_ss [PROB_COMPL, EVENTS_COMPL]
  ++ RW_TAC real_ss [extreal_of_num_def,extreal_sub_def]);

val EVENTS_COUNTABLE_INTER = store_thm
("EVENTS_COUNTABLE_INTER", ``!p c. prob_space p /\ c SUBSET events p /\ countable c /\ (~(c={})) ==> BIGINTER c IN events p``,
  RW_TAC std_ss []
  ++ Know `BIGINTER c = p_space p DIFF (p_space p DIFF (BIGINTER c))`
  >> (ONCE_REWRITE_TAC [EXTENSION] ++ RW_TAC std_ss [IN_DIFF, LEFT_AND_OVER_OR, IN_BIGINTER]
      ++ FULL_SIMP_TAC std_ss [PROB_SPACE, SIGMA_ALGEBRA, subset_class_def, subsets_def, space_def, SUBSET_DEF]
      ++ EQ_TAC
      >> (Know `(c = {}) \/ ?x t. (c = x INSERT t) /\ ~(x IN t)` >> PROVE_TAC [SET_CASES]
          ++ RW_TAC std_ss []
          ++ PROVE_TAC [IN_INSERT])
      ++ PROVE_TAC [])
  ++ Rewr'
  ++ MATCH_MP_TAC EVENTS_COMPL
  ++ Know `p_space p DIFF BIGINTER c = BIGUNION (IMAGE (\s. p_space p DIFF s) c)`
  >> (ONCE_REWRITE_TAC [EXTENSION] ++ RW_TAC std_ss [IN_DIFF, IN_BIGUNION, IN_IMAGE, IN_BIGINTER]
      ++ EQ_TAC
      >> (RW_TAC std_ss [] ++ Q.EXISTS_TAC `p_space p DIFF P`
          ++ RW_TAC std_ss [IN_DIFF] ++ Q.EXISTS_TAC `P`
          ++ RW_TAC std_ss [])
      ++ RW_TAC std_ss []
      >> FULL_SIMP_TAC std_ss [IN_DIFF]
      ++ Q.EXISTS_TAC `s'`
      ++ FULL_SIMP_TAC std_ss [IN_DIFF])
   ++ RW_TAC std_ss [] ++ POP_ASSUM (K ALL_TAC)
   ++ MATCH_MP_TAC EVENTS_COUNTABLE_UNION
   ++ Q.PAT_X_ASSUM `c SUBSET events p` MP_TAC
   ++ RW_TAC std_ss [image_countable, SUBSET_DEF, IN_IMAGE]
   ++ PROVE_TAC [EVENTS_COMPL]);

val ABS_PROB = store_thm
("ABS_PROB", ``!p s. prob_space p /\ s IN events p ==> (abs (prob p s) = prob p s)``,
  RW_TAC std_ss [extreal_abs_def]
  ++ PROVE_TAC [PROB_POSITIVE,abs_refl]);

val PROB_COMPL_LE1 = store_thm
("PROB_COMPL_LE1", ``!p s r. prob_space p /\ s IN events p ==> (prob p (p_space p DIFF s) <= r = 1 - r <= prob p s)``,
  RW_TAC std_ss [PROB_COMPL]
  ++ METIS_TAC [sub_le_switch2,PROB_FINITE,num_not_infty]);

val PROB_LE_1 = store_thm
("PROB_LE_1", ``!p s. prob_space p /\ s IN events p ==> prob p s <= 1``,
  RW_TAC std_ss []
  ++ Suff `0 <= 1 - prob p s` >> METIS_TAC [sub_zero_le,PROB_FINITE]
  ++ RW_TAC std_ss [GSYM PROB_COMPL]
  ++ RW_TAC std_ss [EVENTS_COMPL, PROB_POSITIVE]);

val PROB_EQ_BIGUNION_IMAGE = store_thm
("PROB_EQ_BIGUNION_IMAGE", ``!p. prob_space p /\ f IN (UNIV -> events p) /\ g IN (UNIV -> events p) /\
       (!m n. ~(m = n) ==> DISJOINT (f m) (f n)) /\
       (!m n. ~(m = n) ==> DISJOINT (g m) (g n)) /\
       (!n: num. prob p (f n) = prob p (g n)) ==>
       (prob p (BIGUNION (IMAGE f UNIV)) = prob p (BIGUNION (IMAGE g UNIV)))``,
   RW_TAC std_ss []
   ++ Know `prob p (BIGUNION (IMAGE f UNIV)) = suminf (prob p o f)`
   >> PROVE_TAC [PROB_COUNTABLY_ADDITIVE]
   ++ Know `prob p (BIGUNION (IMAGE g UNIV)) = suminf (prob p o g)`
   >> PROVE_TAC [PROB_COUNTABLY_ADDITIVE]
   ++ METIS_TAC [o_DEF]);

val PROB_FINITELY_ADDITIVE = store_thm
("PROB_FINITELY_ADDITIVE", ``!p s f n. prob_space p /\ f IN ((count n) -> events p) /\
       (!a b. a < n /\ b < n /\ ~(a = b) ==> DISJOINT (f a) (f b)) /\
       (s = BIGUNION (IMAGE f (count n))) ==>
        (prob p s = SIGMA (prob p o f) (count n))``,
  RW_TAC std_ss [IN_FUNSET, IN_COUNT]
  ++ Suff `(ext_suminf (prob p o (\m. if m < n then f m else {})) = prob p (BIGUNION (IMAGE f (count n)))) /\
           (ext_suminf (prob p o (\m. if m < n then f m else {})) = SIGMA (prob p o f) (count n))`
  >> METIS_TAC []
  ++ REVERSE CONJ_TAC
  >> (Know `SIGMA (prob p o f) (count n) = SIGMA (prob p o (\m. (if m < n then f m else {}))) (count n)`
      >> ((MATCH_MP_TAC o REWRITE_RULE [FINITE_COUNT] o Q.ISPEC `count n`) EXTREAL_SUM_IMAGE_EQ
          ++ RW_TAC std_ss [IN_COUNT]
          ++ METIS_TAC [PROB_FINITE])
      ++ RW_TAC std_ss []
      ++ MATCH_MP_TAC ext_suminf_sum
      ++ RW_TAC std_ss [PROB_EMPTY,PROB_POSITIVE,le_refl]
      ++ METIS_TAC [NOT_LESS])
  ++ Know `BIGUNION (IMAGE f (count n)) = BIGUNION (IMAGE (\m. (if m < n then f m else {})) UNIV)`
  >> (RW_TAC std_ss [EXTENSION,IN_BIGUNION_IMAGE, IN_COUNT, IN_UNIV]
      ++ METIS_TAC [NOT_IN_EMPTY])
  ++ Rewr
  ++ MATCH_MP_TAC (GSYM PROB_COUNTABLY_ADDITIVE)
  ++ RW_TAC std_ss [IN_FUNSET, IN_UNIV, DISJOINT_EMPTY]
  ++ METIS_TAC [EVENTS_EMPTY]);

val ABS_1_MINUS_PROB = store_thm
("ABS_1_MINUS_PROB", ``!p s. prob_space p /\ s IN events p /\ ~(prob p s = 0) ==> abs (1 - prob p s) < 1``,
  RW_TAC std_ss []
  ++ Know `0 <= prob p s` >> PROVE_TAC [PROB_POSITIVE]
  ++ Know `prob p s <= 1` >> PROVE_TAC [PROB_LE_1]
  ++ `?r. prob p s = Normal r` by METIS_TAC [PROB_FINITE,extreal_cases]
  ++ FULL_SIMP_TAC std_ss [extreal_of_num_def,extreal_sub_def,extreal_abs_def,extreal_lt_eq,extreal_le_def,extreal_11]
  ++ RW_TAC std_ss [abs]
  ++ REPEAT (POP_ASSUM MP_TAC)
  ++ REAL_ARITH_TAC);

val PROB_INCREASING_UNION = store_thm
  ("PROB_INCREASING_UNION",
   ``!p f.
       prob_space p /\ f IN (UNIV -> events p) /\ (!n. f n SUBSET f (SUC n)) ==>
       (sup (IMAGE (prob p o f) UNIV) = prob p (BIGUNION (IMAGE f UNIV)))``,
   RW_TAC std_ss [prob_space_def, events_def, prob_def, MONOTONE_CONVERGENCE]);


val PROB_SUBADDITIVE = store_thm
  ("PROB_SUBADDITIVE",
   ``!p t u.
       prob_space p /\ t IN events p /\ u IN events p ==>
       prob p (t UNION u) <= prob p t + prob p u``,
   RW_TAC std_ss []
   ++ Know `t UNION u = t UNION (u DIFF t)`
   >> (SET_EQ_TAC
       ++ RW_TAC std_ss [IN_UNION, IN_DIFF]
       ++ PROVE_TAC [])
   ++ Rewr
   ++ Know `u DIFF t IN events p`
   >> PROVE_TAC [EVENTS_DIFF]
   ++ STRIP_TAC
   ++ Know `prob p (t UNION (u DIFF t)) = prob p t + prob p (u DIFF t)`
   >> (MATCH_MP_TAC PROB_ADDITIVE
       ++ RW_TAC std_ss [DISJOINT_ALT, IN_DIFF])
   ++ Rewr
   ++ MATCH_MP_TAC le_ladd_imp
   ++ MATCH_MP_TAC PROB_INCREASING
   ++ RW_TAC std_ss [DIFF_DEF, SUBSET_DEF, GSPECIFICATION]);

val PROB_COUNTABLY_SUBADDITIVE = store_thm
  ("PROB_COUNTABLY_SUBADDITIVE",
   ``!p f.
       prob_space p /\ (IMAGE f UNIV) SUBSET events p  ==>
       prob p (BIGUNION (IMAGE f UNIV)) <= suminf (prob p o f)``,

  RW_TAC std_ss [SUBSET_DEF, IN_IMAGE, IN_UNIV,ext_suminf_def]
  ++ Suff `prob p (BIGUNION (IMAGE f UNIV)) = sup (IMAGE (prob p o (\n. BIGUNION (IMAGE f (count n)))) UNIV)`
  >> (RW_TAC std_ss []
      ++ MATCH_MP_TAC sup_mono
      ++ RW_TAC std_ss [o_DEF]
      ++ Induct_on `n`
      >> RW_TAC std_ss [COUNT_ZERO,IMAGE_EMPTY,BIGUNION_EMPTY,PROB_EMPTY,EXTREAL_SUM_IMAGE_EMPTY,le_refl]
      ++ RW_TAC std_ss [COUNT_SUC, IMAGE_INSERT, BIGUNION_INSERT]
      ++ (MP_TAC o Q.SPEC `n` o REWRITE_RULE [FINITE_COUNT,o_DEF] o Q.SPECL [`prob p o f`,`count n`] o INST_TYPE [alpha |-> ``:num``]) EXTREAL_SUM_IMAGE_PROPERTY
      ++ `(!x. x IN n INSERT count n ==> prob p (f x) <> NegInf)` by METIS_TAC [PROB_FINITE]
      ++ RW_TAC std_ss [COUNT_SUC]
      ++ `~(n < n)` by RW_TAC real_ss []
      ++ `count n DELETE n = count n` by METIS_TAC [DELETE_NON_ELEMENT,IN_COUNT]
      ++ RW_TAC std_ss []
      ++ `prob p (f n UNION BIGUNION (IMAGE f (count n))) <= prob p (f n) + prob p (BIGUNION (IMAGE f (count n)))`
          by (MATCH_MP_TAC PROB_SUBADDITIVE
              ++ RW_TAC std_ss []
	      >> METIS_TAC []
	      ++ MATCH_MP_TAC EVENTS_COUNTABLE_UNION
	      ++ RW_TAC std_ss [SUBSET_DEF, IN_IMAGE, IN_COUNT, image_countable,
                     COUNTABLE_COUNT]
	      ++ METIS_TAC [])
      ++ METIS_TAC [le_ladd_imp,le_trans])
  ++ (MP_TAC o Q.SPECL [`p`,`(\n. BIGUNION (IMAGE f (count n)))`]) PROB_INCREASING_UNION
  ++ RW_TAC std_ss []
  ++ `BIGUNION (IMAGE (\n. BIGUNION (IMAGE f (count n))) UNIV) = BIGUNION (IMAGE f UNIV)`
       by (RW_TAC std_ss [EXTENSION,IN_BIGUNION_IMAGE,IN_UNIV,IN_COUNT]
           ++ METIS_TAC [DECIDE ``x < SUC x``])
  ++ FULL_SIMP_TAC std_ss []
  ++ POP_ASSUM (K ALL_TAC)
  ++ POP_ASSUM (MATCH_MP_TAC o GSYM)
  ++ RW_TAC std_ss [IN_FUNSET,IN_UNIV]
  >> (MATCH_MP_TAC EVENTS_COUNTABLE_UNION
      ++ RW_TAC std_ss [SUBSET_DEF, IN_IMAGE, IN_COUNT, image_countable,
                        COUNTABLE_COUNT]
      ++ METIS_TAC [])
  ++ RW_TAC std_ss [SUBSET_DEF,IN_BIGUNION_IMAGE,IN_COUNT]
  ++ METIS_TAC [DECIDE ``n < SUC n``,LESS_TRANS]);

val PROB_COUNTABLY_ZERO = store_thm
("PROB_COUNTABLY_ZERO", ``!p c. prob_space p /\ countable c /\ c SUBSET events p /\
       (!x. x IN c ==> (prob p x = 0)) ==> (prob p (BIGUNION c) = 0)``,
  RW_TAC std_ss [COUNTABLE_ENUM]
  >> RW_TAC std_ss [BIGUNION_EMPTY, PROB_EMPTY]
  ++ Know `(!n. prob p (f n) = 0) /\ (!n. f n IN events p)`
  >> (FULL_SIMP_TAC std_ss [IN_IMAGE, IN_UNIV, SUBSET_DEF]
      ++ PROVE_TAC [])
  ++ NTAC 2 (POP_ASSUM K_TAC)
  ++ STRIP_TAC
  ++ ONCE_REWRITE_TAC [GSYM le_antisym]
  ++ REVERSE CONJ_TAC
  >> (MATCH_MP_TAC PROB_POSITIVE
      ++ RW_TAC std_ss []
      ++ MATCH_MP_TAC EVENTS_COUNTABLE_UNION
      ++ RW_TAC std_ss [COUNTABLE_IMAGE_NUM, SUBSET_DEF, IN_IMAGE, IN_UNIV]
      ++ RW_TAC std_ss [])
  ++ Know `suminf (prob p o f) = 0`
  >> RW_TAC std_ss [ext_suminf_def,o_DEF,EXTREAL_SUM_IMAGE_ZERO,FINITE_COUNT,sup_const_over_set,UNIV_NOT_EMPTY]
  ++ RW_TAC std_ss []
  ++ POP_ASSUM (REWRITE_TAC o wrap o SYM)
  ++ MATCH_MP_TAC PROB_COUNTABLY_SUBADDITIVE
  ++ RW_TAC std_ss [SUBSET_DEF, IN_IMAGE, IN_UNIV]
  ++ RW_TAC std_ss []);

val INDEP_SYM = store_thm
("INDEP_SYM", ``!p a b. prob_space p /\ indep p a b ==> indep p b a``,
   RW_TAC std_ss [indep_def]
   ++ PROVE_TAC [mul_comm, INTER_COMM]);

val INDEP_REFL = store_thm
("INDEP_REFL", ``!p a. prob_space p /\ a IN events p ==>
       (indep p a a = (prob p a = 0) \/ (prob p a = 1))``,
  RW_TAC std_ss [indep_def, INTER_IDEMPOT]
  ++ `?r. prob p a = Normal r` by METIS_TAC [PROB_FINITE,extreal_cases]
  ++ RW_TAC std_ss [extreal_mul_def,extreal_of_num_def,extreal_11]
  ++ METIS_TAC [REAL_MUL_IDEMPOT]);

val PROB_REAL_SUM_IMAGE = store_thm
  ("PROB_REAL_SUM_IMAGE",
   ``!p s. prob_space p /\ s IN events p /\ (!x. x IN s ==> {x} IN events p) /\ FINITE s ==>
		(prob p s = SIGMA (\x. prob p {x}) s)``,
  Suff `!s. FINITE s ==>
	(\s. !p. prob_space p /\ s IN events p /\ (!x. x IN s ==> {x} IN events p) ==>
	     (prob p s = SIGMA (\x. prob p {x}) s)) s`
  >> METIS_TAC []
  ++ MATCH_MP_TAC FINITE_INDUCT
  ++ RW_TAC std_ss [EXTREAL_SUM_IMAGE_EMPTY,PROB_EMPTY,IN_INSERT]
  ++ (MP_TAC o Q.SPEC `e` o UNDISCH o Q.SPECL [`(\x. prob p {x})`,`s`]) EXTREAL_SUM_IMAGE_PROPERTY
  ++ `!x. x IN e INSERT s ==> (\x. prob p {x}) x <> NegInf` by METIS_TAC [PROB_FINITE,IN_INSERT]
  ++ RW_TAC std_ss []
  ++ Q.PAT_X_ASSUM `!p. prob_space p /\ s IN events p /\
            (!x. x IN s ==> {x} IN events p) ==>
            (prob p s = SIGMA (\x. prob p {x}) s)` (MP_TAC o GSYM o Q.SPEC `p`)
  ++ RW_TAC std_ss []
  ++ `s IN events p`
      by (`s = (e INSERT s) DIFF {e}`
	     by (RW_TAC std_ss [EXTENSION, IN_INSERT, IN_DIFF, IN_SING] ++ METIS_TAC [GSYM DELETE_NON_ELEMENT])
	  ++ POP_ORW
	  ++ FULL_SIMP_TAC std_ss [prob_space_def, measure_space_def, sigma_algebra_def, events_def]
	  ++ METIS_TAC [space_def, subsets_def, ALGEBRA_DIFF])
  ++ FULL_SIMP_TAC std_ss [DELETE_NON_ELEMENT]
  ++ MATCH_MP_TAC PROB_ADDITIVE
  ++ RW_TAC std_ss [IN_DISJOINT, IN_SING, Once INSERT_SING_UNION]
  ++ FULL_SIMP_TAC std_ss [GSYM DELETE_NON_ELEMENT]);

val PROB_EQUIPROBABLE_FINITE_UNIONS = store_thm
  ("PROB_EQUIPROBABLE_FINITE_UNIONS",
   ``!p s. prob_space p /\ s IN events p /\ (!x. x IN s ==> {x} IN events p) /\ FINITE s /\
	   (!x y. x IN s /\ y IN s ==> (prob p {x} = prob p {y})) ==>
		(prob p s = & (CARD s) * prob p {CHOICE s})``,
  RW_TAC std_ss []
  ++ Cases_on `s = {}`
  >> RW_TAC real_ss [PROB_EMPTY, CARD_EMPTY,mul_lzero]
  ++ `prob p s = SIGMA (\x. prob p {x}) s`
      by METIS_TAC [PROB_REAL_SUM_IMAGE]
  ++ POP_ORW
  ++ `prob p {CHOICE s} = (\x. prob p {x}) (CHOICE s)` by RW_TAC std_ss []
  ++ POP_ORW
  ++ (MATCH_MP_TAC o UNDISCH o Q.SPEC `s`) EXTREAL_SUM_IMAGE_FINITE_SAME
  ++ RW_TAC std_ss [CHOICE_DEF]
  ++ METIS_TAC [PROB_FINITE]);

val PROB_REAL_SUM_IMAGE_FN = store_thm
  ("PROB_REAL_SUM_IMAGE_FN",
   ``!p f e s. prob_space p /\ e IN events p /\ (!x. x IN s ==> e INTER f x IN events p) /\ FINITE s /\
		(!x y. x IN s /\ y IN s /\ (~(x=y)) ==> DISJOINT (f x) (f y)) /\
		(BIGUNION (IMAGE f s) INTER p_space p = p_space p) ==>
		(prob p e = SIGMA (\x. prob p (e INTER f x)) s)``,
  Suff `!(s :'b -> bool). FINITE s ==>
	(\s. !(p :('a -> bool) # (('a -> bool) -> bool) # (('a -> bool) -> extreal))
       (f :'b -> 'a -> bool) (e :'a -> bool). prob_space p /\ e IN events p /\ (!x. x IN s ==> e INTER f x IN events p) /\
		(!x y. x IN s /\ y IN s /\ (~(x=y)) ==> DISJOINT (f x) (f y)) /\
		(BIGUNION (IMAGE f s) INTER p_space p = p_space p) ==>
		(prob p e = SIGMA (\x. prob p (e INTER f x)) s)) s`
  >> METIS_TAC []
  ++ MATCH_MP_TAC FINITE_INDUCT
  ++ RW_TAC std_ss [EXTREAL_SUM_IMAGE_EMPTY, PROB_EMPTY, DELETE_NON_ELEMENT, IN_INSERT, IMAGE_EMPTY, BIGUNION_EMPTY, INTER_EMPTY]
  >> METIS_TAC [PROB_UNIV, PROB_EMPTY, REAL_10,extreal_of_num_def,extreal_11]
  ++ (MP_TAC o Q.SPEC `e` o UNDISCH o Q.SPECL [`(\x. prob p (e' INTER f x))`,`s`] o INST_TYPE [alpha |-> beta]) EXTREAL_SUM_IMAGE_PROPERTY
  ++ `!x. x IN e INSERT s ==> (\x. prob p (e' INTER f x)) x <> NegInf` by METIS_TAC [PROB_FINITE,IN_INSERT]
  ++ RW_TAC std_ss []
  ++ `prob p e' = prob p (e' INTER f e) + prob p (e' DIFF f e)`
       by (MATCH_MP_TAC PROB_ADDITIVE
	   ++ RW_TAC std_ss []
	   << [`e' DIFF f e = e' DIFF (e' INTER f e)`
	         by (RW_TAC std_ss [EXTENSION, IN_DIFF, IN_INTER] ++ DECIDE_TAC)
	       ++ POP_ORW
	       ++ METIS_TAC [EVENTS_DIFF],
	       FULL_SIMP_TAC std_ss [IN_DISJOINT, IN_INTER, IN_DIFF] ++ METIS_TAC [],
	       RW_TAC std_ss [Once EXTENSION, IN_INTER, IN_UNION, IN_DIFF] ++ DECIDE_TAC])
  ++ POP_ORW
  ++ RW_TAC std_ss [EXTREAL_EQ_LADD,PROB_FINITE]
  ++ (MP_TAC o Q.ISPEC `(s :'b -> bool)`) SET_CASES
  ++ RW_TAC std_ss []
  >> (RW_TAC std_ss [EXTREAL_SUM_IMAGE_EMPTY]
      ++ `IMAGE f {e} = {f e}`
		by RW_TAC std_ss [EXTENSION, IN_IMAGE, IN_SING]
      ++ FULL_SIMP_TAC std_ss [BIGUNION_SING, DIFF_UNIV, PROB_EMPTY]
      ++ `e' DIFF f e = {}`
		by (RW_TAC std_ss [Once EXTENSION, NOT_IN_EMPTY, IN_DIFF]
		    ++ METIS_TAC [SUBSET_DEF, MEASURABLE_SETS_SUBSET_SPACE, prob_space_def,
				  events_def, p_space_def, IN_INTER])
      ++ RW_TAC std_ss [PROB_EMPTY])
  ++ Q.PAT_X_ASSUM `!p f e.
            prob_space p /\ e IN events p /\
            (!x. x IN s ==> e INTER f x IN events p) /\
            (!x y. x IN s /\ y IN s /\ ~(x = y) ==> DISJOINT (f x) (f y)) /\
            (BIGUNION (IMAGE f s) INTER p_space p = p_space p) ==>
            (prob p e = SIGMA (\x. prob p (e INTER f x)) s)`
	(MP_TAC o Q.SPECL [`p`,`(\y. if y = x then f x UNION f e else f y)`,`e' DIFF f e`])
  ++ ASM_SIMP_TAC std_ss []
  ++ `e' DIFF f e IN events p`
	by (`e' DIFF f e = e' DIFF (e' INTER f e)`
		by (RW_TAC std_ss [EXTENSION, IN_DIFF, IN_INTER] ++ DECIDE_TAC)
	        ++ POP_ORW
		++ METIS_TAC [EVENTS_DIFF])
  ++ ASM_SIMP_TAC std_ss []
  ++ `(!x'.
        x' IN x INSERT t ==>
        (e' DIFF f e) INTER (if x' = x then f x UNION f e else f x') IN
        events p)`
	by (RW_TAC std_ss []
	    >> (`(e' DIFF f e) INTER (f x UNION f e) =
		 e' INTER f x`
		by (ONCE_REWRITE_TAC [EXTENSION] ++ RW_TAC std_ss [IN_INTER, IN_DIFF, IN_UNION]
		    ++ FULL_SIMP_TAC std_ss [IN_DISJOINT, GSYM DELETE_NON_ELEMENT]
		    ++ METIS_TAC [])
	        ++ RW_TAC std_ss [])
	    ++ `(e' DIFF f e) INTER f x' =
		(e' INTER f x') DIFF (e' INTER f e)`
		by (ONCE_REWRITE_TAC [EXTENSION] ++ RW_TAC std_ss [IN_INTER, IN_DIFF]
		    ++ FULL_SIMP_TAC std_ss [IN_DISJOINT, GSYM DELETE_NON_ELEMENT]
		    ++ METIS_TAC [])
	    ++ METIS_TAC [EVENTS_DIFF])
  ++ ASM_SIMP_TAC std_ss []
  ++ `(!x' y.
        x' IN x INSERT t /\ y IN x INSERT t /\ ~(x' = y) ==>
        DISJOINT (if x' = x then f x UNION f e else f x')
          (if y = x then f x UNION f e else f y))`
	by (RW_TAC std_ss [IN_DISJOINT, IN_UNION]
	    ++ FULL_SIMP_TAC std_ss [IN_DISJOINT, GSYM DELETE_NON_ELEMENT]
	    ++ METIS_TAC [])
  ++ ASM_SIMP_TAC std_ss []
  ++ `(BIGUNION
        (IMAGE (\y. (if y = x then f x UNION f e else f y)) (x INSERT t)) INTER p_space p = p_space p)`
	by (FULL_SIMP_TAC std_ss [IMAGE_INSERT, BIGUNION_INSERT]
	    ++ `IMAGE (\y. (if y = x then f x UNION f e else f y)) t =
		IMAGE f t`
		by (ONCE_REWRITE_TAC [EXTENSION] ++ RW_TAC std_ss [IN_IMAGE]
		    ++ EQ_TAC
		    >> (RW_TAC std_ss [] ++ METIS_TAC [])
		    ++ RW_TAC std_ss [] ++ METIS_TAC [])
	    ++ POP_ORW
	    ++ METIS_TAC [UNION_COMM, UNION_ASSOC])
  ++ ASM_SIMP_TAC std_ss []
  ++ STRIP_TAC ++ POP_ASSUM (K ALL_TAC)
  ++ FULL_SIMP_TAC std_ss [FINITE_INSERT]
  ++ (MP_TAC o Q.SPEC `x` o UNDISCH o Q.SPECL [`(\x. prob p (e' INTER f x))`,`t`] o INST_TYPE [alpha |-> beta]) EXTREAL_SUM_IMAGE_PROPERTY
  ++ `!x'. x' IN x INSERT t ==> (\x. prob p (e' INTER f x)) x' <> NegInf` by METIS_TAC [PROB_FINITE,IN_INSERT]
  ++ RW_TAC std_ss []
  ++ (MP_TAC o Q.SPEC `x` o UNDISCH o Q.SPECL [`(\x'. prob p ((e' DIFF f e) INTER if x' = x then f x UNION f e else f x'))`,`t`] o INST_TYPE [alpha |-> beta]) EXTREAL_SUM_IMAGE_PROPERTY
  ++ `!x'. x' IN x INSERT t ==> (\x'. prob p ((e' DIFF f e) INTER if x' = x then f x UNION f e else f x')) x' <> NegInf` by METIS_TAC [PROB_FINITE,IN_INSERT]
  ++ RW_TAC std_ss []
  ++ FULL_SIMP_TAC std_ss [DELETE_NON_ELEMENT]
  ++ FULL_SIMP_TAC std_ss [GSYM DELETE_NON_ELEMENT]
  ++ `(e' DIFF f e) INTER (f x UNION f e) =
	e' INTER f x`
	by (ONCE_REWRITE_TAC [EXTENSION] ++ RW_TAC std_ss [IN_INTER, IN_DIFF, IN_UNION]
	    ++ FULL_SIMP_TAC std_ss [IN_DISJOINT, GSYM DELETE_NON_ELEMENT, IN_INSERT]
	    ++ METIS_TAC [])
  ++ FULL_SIMP_TAC std_ss [EXTREAL_EQ_LADD,PROB_FINITE,IN_INSERT]
  ++ (MP_TAC o Q.SPEC `(\x. prob p (e' INTER f x))` o UNDISCH o Q.ISPEC `(t :'b -> bool)`) EXTREAL_SUM_IMAGE_IN_IF
  ++ (MP_TAC o Q.SPEC `(\x'. prob p ((e' DIFF f e) INTER if x' = x then f x UNION f e else f x'))` o UNDISCH o Q.ISPEC `(t :'b -> bool)`) EXTREAL_SUM_IMAGE_IN_IF
  ++ RW_TAC std_ss []
  ++ Suff `(\x'.
         (if x' IN t then
            (\x'.
               prob p
                 ((e' DIFF f e) INTER
                  (if x' = x then f x UNION f e else f x'))) x'
          else
            0)) =
	(\x. (if x IN t then (\x. prob p (e' INTER f x)) x else 0))`
  >> RW_TAC std_ss []
  ++ RW_TAC std_ss [FUN_EQ_THM] ++ RW_TAC std_ss []
  ++ Suff `(e' DIFF f e) INTER f x' = e' INTER f x'`
  >> RW_TAC std_ss []
  ++ RW_TAC std_ss [Once EXTENSION, IN_INTER, IN_DIFF]
  ++ FULL_SIMP_TAC std_ss [IN_DISJOINT, IN_INSERT]
  ++ METIS_TAC []);

(* ************************************************************************* *)
val distribution_prob_space = store_thm
  ("distribution_prob_space",
   ``!p X s. random_variable X p s ==>
		prob_space (space s, subsets s, distribution p X)``,
   RW_TAC std_ss [random_variable_def, distribution_def, prob_space_def, measure_def, PSPACE,
		  measure_space_def, m_space_def, measurable_sets_def, IN_MEASURABLE,
		  SPACE, positive_def, PREIMAGE_EMPTY, INTER_EMPTY, PROB_EMPTY,
		  PROB_POSITIVE, space_def, subsets_def, countably_additive_def]
   >> (Q.PAT_X_ASSUM `!f.
            f IN (UNIV -> measurable_sets p) /\
            (!m n. ~(m = n) ==> DISJOINT (f m) (f n)) /\
            BIGUNION (IMAGE f UNIV) IN measurable_sets p ==>
            (measure p (BIGUNION (IMAGE f univ(:num))) = suminf (measure p o f))`
		(MP_TAC o Q.SPEC `(\x. PREIMAGE X x INTER p_space p) o f`)
       ++ RW_TAC std_ss [prob_def, o_DEF, PREIMAGE_BIGUNION, IMAGE_IMAGE]
       ++ `(BIGUNION (IMAGE (\x. PREIMAGE X (f x)) UNIV) INTER p_space p) =
	   (BIGUNION (IMAGE (\x. PREIMAGE X (f x) INTER p_space p) UNIV))`
	by (RW_TAC std_ss [Once EXTENSION, IN_BIGUNION, IN_INTER, IN_IMAGE, IN_UNIV]
	    ++ METIS_TAC [IN_INTER])
       ++ POP_ORW
       ++ POP_ASSUM MATCH_MP_TAC
       ++ FULL_SIMP_TAC std_ss [o_DEF, IN_FUNSET, IN_UNIV, events_def]
       ++ CONJ_TAC
       >> (REPEAT STRIP_TAC
	    ++ Suff `DISJOINT (PREIMAGE X (f m)) (PREIMAGE X (f n))`
	    >> (RW_TAC std_ss [IN_DISJOINT, IN_INTER] ++ METIS_TAC [])
	    ++ RW_TAC std_ss [PREIMAGE_DISJOINT])
       ++ Suff `BIGUNION (IMAGE (\x. PREIMAGE X (f x) INTER p_space p) UNIV) =
		PREIMAGE X (BIGUNION (IMAGE f UNIV)) INTER p_space p`
       >> RW_TAC std_ss []
       ++ RW_TAC std_ss [Once EXTENSION, IN_INTER, IN_BIGUNION, IN_IMAGE, IN_UNIV,
			 IN_PREIMAGE, IN_BIGUNION]
       ++ METIS_TAC [IN_INTER, IN_PREIMAGE])
   ++ Suff `PREIMAGE X (space s) INTER p_space p = p_space p`
   >> RW_TAC std_ss [prob_def]
   ++ FULL_SIMP_TAC std_ss [IN_FUNSET, EXTENSION, IN_PREIMAGE, IN_INTER]
   ++ METIS_TAC []);

val distribution_lebesgue_thm1 = store_thm
  ("distribution_lebesgue_thm1",
   ``!X p s A. random_variable X p s /\ A IN subsets s ==>
	     (distribution p X A = integral p (indicator_fn (PREIMAGE X A INTER p_space p)))``,
   RW_TAC std_ss [random_variable_def, prob_space_def, distribution_def, events_def, IN_MEASURABLE, p_space_def, prob_def,
	          subsets_def, space_def, GSYM integral_indicator]);

val distribution_lebesgue_thm2 = store_thm
  ("distribution_lebesgue_thm2",
   ``!X p s A. random_variable X p s /\ A IN subsets s ==>
	     (distribution p X A = integral (space s, subsets s, distribution p X) (indicator_fn A))``,
   REPEAT STRIP_TAC
   ++ `prob_space (space s,subsets s,distribution p X)`
	by RW_TAC std_ss [distribution_prob_space]
   ++ Q.PAT_X_ASSUM `random_variable X p s` MP_TAC
   ++ RW_TAC std_ss [random_variable_def, prob_space_def, distribution_def, events_def, IN_MEASURABLE, p_space_def, prob_def,
	          subsets_def, space_def]
   ++ `measure p (PREIMAGE X A INTER m_space p) =
       measure (space s,subsets s,(\A. measure p (PREIMAGE X A INTER m_space p))) A`
	by RW_TAC std_ss [measure_def]
   ++ POP_ORW
   ++ (MP_TAC o Q.SPECL [`(space s,subsets s,(\A. measure p (PREIMAGE X A INTER m_space p)))`,`A`] o INST_TYPE [``:'a``|->``:'b``])
	integral_indicator
   ++ FULL_SIMP_TAC std_ss [measurable_sets_def, prob_space_def, distribution_def, prob_def, p_space_def]);

(* ************************************************************************* *)
(*
val finite_expectation1 = store_thm
  ("finite_expectation1",
   ``!p X. FINITE (p_space p) /\ real_random_variable X p ==>
		(expectation p X =
		 SIGMA (\r. r * prob p (PREIMAGE X {r} INTER p_space p))
		       (IMAGE X (p_space p)))``,
   RW_TAC std_ss [expectation_def, p_space_def, prob_def, prob_space_def, real_random_variable_def, events_def]
   ++ (MATCH_MP_TAC o REWRITE_RULE [finite_space_integral_def]) finite_space_integral_reduce
   ++ RW_TAC std_ss []);

val finite_expectation = store_thm
  ("finite_expectation",
   ``!p X. FINITE (p_space p) /\ real_random_variable X p ==>
		(expectation p X =
		 SIGMA (\r. r * distribution p X {r})
		       (IMAGE X (p_space p)))``,
   RW_TAC std_ss [distribution_def]
   ++ METIS_TAC [finite_expectation1]);
*)
(* ************************************************************************* *)

val finite_marginal_product_space_POW = store_thm
  ("finite_marginal_product_space_POW",
   ``!p X Y. (POW (p_space p) = events p) /\
	     random_variable X p (IMAGE X (p_space p), POW (IMAGE X (p_space p))) /\
	     random_variable Y p (IMAGE Y (p_space p), POW (IMAGE Y (p_space p))) /\
		    FINITE (p_space p) ==>
	measure_space (((IMAGE X (p_space p)) CROSS (IMAGE Y (p_space p))),
			POW ((IMAGE X (p_space p)) CROSS (IMAGE Y (p_space p))),
			(\a. prob p (PREIMAGE (\x. (X x,Y x)) a INTER p_space p)))``,
   REPEAT STRIP_TAC
   ++ `(IMAGE X (p_space p) CROSS IMAGE Y (p_space p),
		       POW (IMAGE X (p_space p) CROSS IMAGE Y (p_space p)),
		       (\a. prob p (PREIMAGE (\x. (X x,Y x)) a INTER p_space p))) =
	(space (IMAGE X (p_space p) CROSS IMAGE Y (p_space p),
		       POW (IMAGE X (p_space p) CROSS IMAGE Y (p_space p))),
	subsets
         (IMAGE X (p_space p) CROSS IMAGE Y (p_space p),
		       POW (IMAGE X (p_space p) CROSS IMAGE Y (p_space p))),
       (\a. prob p (PREIMAGE (\x. (X x,Y x)) a INTER p_space p)))`
	by RW_TAC std_ss [space_def, subsets_def]
   ++ POP_ORW
   ++ MATCH_MP_TAC finite_additivity_sufficient_for_finite_spaces
   ++ RW_TAC std_ss [POW_SIGMA_ALGEBRA, space_def, FINITE_CROSS, subsets_def, IMAGE_FINITE]
   >> (RW_TAC std_ss [positive_def, measure_def, measurable_sets_def, PREIMAGE_EMPTY, INTER_EMPTY]
       >> FULL_SIMP_TAC std_ss [random_variable_def, PROB_EMPTY]
       ++ METIS_TAC [PROB_POSITIVE, SUBSET_DEF, IN_POW, IN_INTER, random_variable_def])
   ++ RW_TAC std_ss [additive_def, measure_def, measurable_sets_def]
   ++ MATCH_MP_TAC PROB_ADDITIVE
   ++ Q.PAT_X_ASSUM `POW (p_space p) = events p` (MP_TAC o GSYM)
   ++ FULL_SIMP_TAC std_ss [IN_POW, SUBSET_DEF, IN_PREIMAGE, IN_CROSS, IN_DISJOINT, random_variable_def, IN_INTER]
   ++ RW_TAC std_ss [] >> METIS_TAC [SND]
   ++ RW_TAC std_ss [Once EXTENSION, IN_UNION, IN_PREIMAGE, IN_INTER]
   ++ METIS_TAC []);

val finite_marginal_product_space_POW2 = store_thm
  ("finite_marginal_product_space_POW2",
   ``!p s1 s2 X Y. (POW (p_space p) = events p) /\
	     random_variable X p (s1, POW s1) /\
	     random_variable Y p (s2, POW s2) /\
		    FINITE (p_space p) /\
		    FINITE s1 /\ FINITE s2 ==>
	measure_space (s1 CROSS s2, POW (s1 CROSS s2), joint_distribution p X Y)``,
   REPEAT STRIP_TAC
   ++ `(s1 CROSS s2, POW (s1 CROSS s2), joint_distribution p X Y) =
	(space (s1 CROSS s2, POW (s1 CROSS s2)),
	subsets
         (s1 CROSS s2, POW (s1 CROSS s2)),
       joint_distribution p X Y)`
	by RW_TAC std_ss [space_def, subsets_def]
   ++ POP_ORW
   ++ MATCH_MP_TAC finite_additivity_sufficient_for_finite_spaces
   ++ RW_TAC std_ss [POW_SIGMA_ALGEBRA, space_def, FINITE_CROSS, subsets_def]
   >> (RW_TAC std_ss [positive_def, measure_def, measurable_sets_def, PREIMAGE_EMPTY, INTER_EMPTY, joint_distribution_def]
       >> FULL_SIMP_TAC std_ss [random_variable_def, PROB_EMPTY]
       ++ METIS_TAC [PROB_POSITIVE, SUBSET_DEF, IN_POW, IN_INTER, random_variable_def])
   ++ RW_TAC std_ss [additive_def, measure_def, measurable_sets_def, joint_distribution_def]
   ++ MATCH_MP_TAC PROB_ADDITIVE
   ++ Q.PAT_X_ASSUM `POW (p_space p) = events p` (MP_TAC o GSYM)
   ++ FULL_SIMP_TAC std_ss [IN_POW, SUBSET_DEF, IN_PREIMAGE, IN_CROSS, IN_DISJOINT, random_variable_def, IN_INTER]
   ++ RW_TAC std_ss [] >> METIS_TAC [SND]
   ++ RW_TAC std_ss [Once EXTENSION, IN_UNION, IN_PREIMAGE, IN_INTER]
   ++ METIS_TAC []);

val prob_x_eq_1_imp_prob_y_eq_0 = store_thm
  ("prob_x_eq_1_imp_prob_y_eq_0",
   ``!p x. prob_space p /\
	   {x} IN events p /\
	   (prob p {x} = 1) ==>
	   (!y. {y} IN events p /\
		(~(y = x)) ==>
		(prob p {y} = 0))``,
   REPEAT STRIP_TAC
   ++ (MP_TAC o Q.SPECL [`p`, `{y}`, `{x}`]) PROB_ONE_INTER
   ++ RW_TAC std_ss []
   ++ Know `{y}INTER{x} = {}` >> RW_TAC std_ss [Once EXTENSION, NOT_IN_EMPTY, IN_INTER, IN_SING]
   ++ METIS_TAC [PROB_EMPTY]);

val distribution_x_eq_1_imp_distribution_y_eq_0 = store_thm
  ("distribution_x_eq_1_imp_distribution_y_eq_0",
   ``!X p x. random_variable X p (IMAGE X (p_space p),POW (IMAGE X (p_space p))) /\
	       (distribution p X {x} = 1) ==>
	   (!y. (~(y = x)) ==>
		(distribution p X {y} = 0))``,
   REPEAT STRIP_TAC
   ++ (MP_TAC o Q.SPECL [`p`, `X`, `(IMAGE X (p_space p),POW (IMAGE X (p_space p)))`]) distribution_prob_space
   ++ RW_TAC std_ss [space_def, subsets_def]
   ++ (MP_TAC o Q.ISPECL [`(IMAGE (X :'a -> 'b)
           (p_space
              (p :
                ('a -> bool) #
                (('a -> bool) -> bool) # (('a -> bool) -> extreal))),
         POW (IMAGE X (p_space p)),distribution p X)`,
			`x:'b`]) prob_x_eq_1_imp_prob_y_eq_0
   ++ SIMP_TAC std_ss [EVENTS, IN_POW, SUBSET_DEF, IN_SING, PROB]
   ++ `x IN IMAGE X (p_space p)`
	by (FULL_SIMP_TAC std_ss [distribution_def, IN_IMAGE]
	    ++ SPOSE_NOT_THEN STRIP_ASSUME_TAC
	    ++ `PREIMAGE X {x} INTER p_space p = {}`
		by (RW_TAC std_ss [Once EXTENSION, IN_INTER, IN_SING, IN_PREIMAGE, NOT_IN_EMPTY]
		    ++ METIS_TAC [])
	    ++ METIS_TAC [random_variable_def, PROB_EMPTY, ne_01])
   ++ POP_ORW
   ++ RW_TAC std_ss []
   ++ Cases_on `y IN IMAGE X (p_space p)` >> ASM_SIMP_TAC std_ss []
   ++ FULL_SIMP_TAC std_ss [distribution_def, IN_IMAGE]
   ++ `PREIMAGE X {y} INTER p_space p = {}`
		by (RW_TAC std_ss [Once EXTENSION, IN_INTER, IN_SING, IN_PREIMAGE, NOT_IN_EMPTY]
		    ++ METIS_TAC [])
   ++ POP_ORW ++ MATCH_MP_TAC PROB_EMPTY ++ FULL_SIMP_TAC std_ss [random_variable_def]);

val _ = export_theory ();

