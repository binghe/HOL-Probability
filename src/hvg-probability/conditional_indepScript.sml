(******************************************************************************)
(*   Conditional Probability and Chain Rule                                   *)
(*              by Waqar Ahmed HVG Concordia University, Canada               *)
(*                                                                            *)
(******************************************************************************)


(*app load ["arithmeticTheory", "realTheory", "prim_recTheory", "seqTheory",
          "pred_setTheory","res_quanTheory", "res_quanTools", "listTheory", "numTheory", "dep_rewrite", 
          "transcTheory", "rich_listTheory", "pairTheory",
          "combinTheory","limTheory","sortingTheory", "realLib", "optionTheory","satTheory",
          "util_probTheory", "extrealTheory","probabilityTheory", "measureTheory" ,"real_sigmaTheory","Arith","cond_probTheory"];
*)

open HolKernel Parse boolLib bossLib limTheory arithmeticTheory realTheory prim_recTheory
     seqTheory pred_setTheory res_quanTheory sortingTheory res_quanTools listTheory transcTheory
     rich_listTheory pairTheory combinTheory realLib  optionTheory dep_rewrite
      util_probTheory real_sigmaTheory extrealTheory measureTheory probabilityTheory Arith cond_probTheory;

open HolKernel boolLib bossLib Parse;

val _ = new_theory "conditional_indep";

val pop_orw = POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm]);
(*---------------------------*)
fun SET_TAC L =
    POP_ASSUM_LIST(K ALL_TAC) THEN REPEAT COND_CASES_TAC THEN
    REWRITE_TAC (append [EXTENSION, SUBSET_DEF, PSUBSET_DEF, DISJOINT_DEF,
    SING_DEF] L) THEN SIMP_TAC std_ss [NOT_IN_EMPTY, IN_UNIV, IN_UNION,
    IN_INTER, IN_DIFF, IN_INSERT, IN_DELETE, IN_BIGINTER, IN_BIGUNION,
    IN_IMAGE, GSPECIFICATION, IN_DEF] THEN METIS_TAC [];

fun SET_RULE tm = prove(tm,SET_TAC []);


val set_rewrs
= [INTER_EMPTY, INTER_UNIV, UNION_EMPTY, UNION_UNIV, DISJOINT_UNION,
DISJOINT_INSERT, DISJOINT_EMPTY, GSYM DISJOINT_EMPTY_REFL,
DISJOINT_BIGUNION, INTER_SUBSET, INTER_IDEMPOT, UNION_IDEMPOT,
SUBSET_UNION];

val UNIONL_def = Define `(UNIONL [] = {})
/\ (UNIONL (s::ss) = (s:'a ->bool) UNION UNIONL ss)`;


val IN_UNIONL = store_thm
("IN_UNIONL",
``!l (v:'a ). v IN UNIONL l = (?s. MEM s l /\ v IN s)``,
Induct >> RW_TAC std_ss [UNIONL_def, MEM, NOT_IN_EMPTY]
\\ RW_TAC std_ss [UNIONL_def, MEM, NOT_IN_EMPTY, IN_UNION]
\\ PROVE_TAC []);


val elt_rewrs
= [SUBSET_DEF, IN_COMPL, IN_DIFF, IN_UNIV, NOT_IN_EMPTY, IN_UNION,
IN_INTER, IN_IMAGE, IN_FUNSET, IN_DFUNSET, GSPECIFICATION,
DISJOINT_DEF, IN_BIGUNION, IN_BIGINTER, IN_COUNT, IN_o,
IN_UNIONL, IN_DELETE, IN_PREIMAGE, IN_SING, IN_INSERT];


fun rewr_ss ths =
simpLib.++
(std_ss,
simpLib.SSFRAG
{ac = [],
name = NONE,
convs = [],
dprocs = [],
filter = NONE,
rewrs = set_rewrs @ elt_rewrs,
congs = []});
val pset_set_ss = rewr_ss set_rewrs;
val pset_elt_ss = rewr_ss elt_rewrs;
val pset_ss = rewr_ss (set_rewrs @ elt_rewrs);


fun PSET_TAC ths =
REPEAT (POP_ASSUM MP_TAC)
\\ RW_TAC pset_set_ss ths
\\ REPEAT (POP_ASSUM MP_TAC)
\\ RW_TAC pset_elt_ss ths;
(*--------------------*)

val PROD_IMAGE_REAL_def = Define
`PROD_IMAGE_REAL f s = ITSET (λe acc. f e * acc) s (1:real)`;

val PROD_IMAGE_REAL = store_thm("PROD_IMAGE_REAL",
  ``!f. (PROD_IMAGE_REAL f EMPTY = 1) /\
    	(!e s. FINITE s ==> (PROD_IMAGE_REAL f (e INSERT s) =
	                    f e * PROD_IMAGE_REAL f (s DELETE e)))``,
REPEAT STRIP_TAC THEN1
    SIMP_TAC (srw_ss()) [ITSET_THM, PROD_IMAGE_REAL_def] THEN
  SIMP_TAC (srw_ss()) [PROD_IMAGE_REAL_def] THEN
  Q.ABBREV_TAC `g = \e acc. f e * acc` THEN
  Q_TAC SUFF_TAC `ITSET g (e INSERT s) 1 =
                  g e (ITSET g (s DELETE e) 1)` THEN1 SRW_TAC [][Abbr`g`] THEN
  MATCH_MP_TAC COMMUTING_ITSET_RECURSES THEN
  SRW_TAC [ARITH_ss][Abbr`g`] THEN REAL_ARITH_TAC);



val chain_rule_def = Define
`chain_rule p B n =
 (prob p (BIGINTER (IMAGE B (count n)) INTER p_space p) =
  PROD_IMAGE_REAL (\a. cond_prob p (B a) (BIGINTER (IMAGE B (count a)) INTER p_space p)) (count n))`;


val chain_rule_thm = store_thm("chain_rule_thm",
  ``!p B n. prob_space p /\ (0 < n) /\
   B ∈ (count n -> events p) ==> chain_rule p B n``,
rw[]
\\ Induct_on `n`
>- rw[]
\\ rw[]
\\ Cases_on `n`
>- (rw[chain_rule_def]
   \\ rw[PROD_IMAGE_REAL]
   \\ once_rewrite_tac[ONE]
   \\ rw[COUNT_SUC,PROB_UNIV,PROD_IMAGE_REAL]
   \\ DEP_ONCE_REWRITE_TAC[COND_PROB_MUL_RULE]
   \\ rw[EVENTS_SPACE,PROB_UNIV]
   \\ fs[EXTENSION,IN_COUNT,COUNT_SUC,IN_INSERT,IN_FUNSET])
\\ rw[chain_rule_def]
\\ rw[Once COUNT_SUC]
\\ rw[GSYM INTER_ASSOC]
\\ DEP_ONCE_REWRITE_TAC[COND_PROB_MUL_RULE]
\\ Q.ABBREV_TAC `n = SUC n'`
\\ rw[COUNT_SUC, PROD_IMAGE_REAL] 
>- (fs[EXTENSION,IN_BIGINTER,IN_COUNT,COUNT_SUC,IN_INSERT,IN_FUNSET])
>- (irule EVENTS_INTER
   \\ rw[EVENTS_SPACE]
   \\ ho_match_mp_tac EVENTS_COUNTABLE_INTER
   \\ DEP_REWRITE_TAC[image_countable]
   \\ rw[COUNTABLE_COUNT]
   >- (rw[IMAGE_DEF,SUBSET_DEF]
   \\ fs[IN_FUNSET,COUNT_SUC,IN_COUNT])
   \\ rw[IN_COUNT,EXTENSION]
   \\ Q.UNABBREV_TAC `n`
   \\ Q.EXISTS_TAC `n'`
   \\ rw[])
\\ once_rewrite_tac[REAL_MUL_COMM]
\\ rw[REAL_MUL_COMM]
\\ rw[COUNT_SUC]
\\ SUBST_OCCS_TAC [([1], SPECL [``prob p (BIGINTER (IMAGE B (count n)) ∩ p_space p)``,``cond_prob p (B n) (BIGINTER (IMAGE B (count n)) ∩ p_space p)``] REAL_MUL_COMM)]
\\ rw[]
\\ DISJ2_TAC
\\ sg `count n DELETE n = count n`
>- (PSET_TAC[EXTENSION,IN_COUNT]
   \\ EQ_TAC
   >- (metis_tac[])
   \\ rw[LESS_NOT_EQ])
\\ pop_orw
\\ rw[GSYM chain_rule_def]
\\ Q.UNABBREV_TAC `n`
\\ fs[]
\\ sg `B ∈ (count (SUC n') -> events p)`
>- (fs[IN_FUNSET,COUNT_SUC,IN_COUNT])
\\ fs[]);


val cond_indep_def = Define
`cond_indep p A B =
(\C. cond_prob p (A INTER B) C = cond_prob p A C * cond_prob p B C)`;

val cond_indep_thm = store_thm("cond_indep_thm",
  ``!p A B C. prob_space p /\ A IN events p /\ B IN events p /\ C IN events p /\ (0 < prob p C) /\
  (prob p (A INTER B INTER C) =
  prob p A * cond_prob p B C * cond_prob p C A) ==>
  cond_indep p A B C``,
rw[cond_indep_def]
\\ MP_TAC (Q.ISPECL[`C:'a->bool`,`A:'a->bool`,`(p :(α -> bool) # ((α -> bool) -> bool) # ((α -> bool) -> real))`] BAYES_RULE)
\\ rw[]
\\ DEP_ASM_REWRITE_TAC[]
\\ once_rewrite_tac[mult_ratl]
\\ sg `~(prob p C = 0)`
>- (rw[REAL_LT_IMP_NE])
\\ dsimp[]
\\ rw[REAL_ARITH ``!a b c:real. a * b * c = b * c * a``]
\\ rw[cond_prob_def]);



val symmetry_CI = store_thm("symmetry_CI",
  ``!p A B. cond_indep p A B =  cond_indep p B A``,
rw[cond_indep_def,INTER_COMM,REAL_MUL_COMM]);


val cond_prob_alt = store_thm("cond_prob_alt",
  ``!A B p. (0 < prob p B) ==>
            (cond_prob p A B = prob p (A INTER B) / prob p B)``,
once_rewrite_tac [cond_prob_def]
\\ metis_tac[REAL_LT_IMP_NE]);

val cond_prob_split = store_thm("cond_prob_split",
  ``∀A f e s p.
         prob_space p ∧ A IN events p /\
	 e ∈ events p ∧
	 (∀x. x ∈ s ⇒ e ∩ f x ∈ events p) ∧
         FINITE s ∧
	 (∀x y. x ∈ s ∧ y ∈ s ∧ x ≠ y ⇒ DISJOINT (f x) (f y)) ∧
         (BIGUNION (IMAGE f s) ∩ p_space p = p_space p) /\
	 (0 < prob p A) ==>
    (cond_prob p e A = SIGMA (λx. cond_prob p (e ∩ f x) A) s)``,
rw[]
\\ DEP_REWRITE_TAC[cond_prob_alt]
\\ rw[]
\\ sg `!x. cond_prob p (e ∩ f x) A =
          prob p ((e ∩ A) INTER f x) / prob p A`
>- (rw[cond_prob_alt] \\ metis_tac[GSYM INTER_ASSOC,INTER_COMM])
\\ pop_orw
\\ DEP_REWRITE_TAC[PROB_REAL_SUM_IMAGE_FN]
\\ rw[]
>- (rw[EVENTS_INTER])
>- (SUBST_OCCS_TAC [([1], SPECL [``e:'a->bool``,``A:'a->bool``] INTER_COMM)]
   \\ once_rewrite_tac[GSYM INTER_ASSOC]
   \\ rw[EVENTS_INTER])
\\ rw[real_div]
\\ once_rewrite_tac[REAL_MUL_COMM]
\\ DEP_REWRITE_TAC[real_sigmaTheory.REAL_SUM_IMAGE_CMUL]
\\ rw[]);

val cond_prob_split = store_thm("cond_prob_split",
  ``∀A f e s p.
         prob_space p ∧ A IN events p /\
	 e ∈ events p ∧
	 (∀x. x ∈ s ⇒ e ∩ f x ∈ events p) ∧
         FINITE s ∧
	 (∀x y. x ∈ s ∧ y ∈ s ∧ x ≠ y ⇒ DISJOINT (f x) (f y)) ∧
         (BIGUNION (IMAGE f s) ∩ p_space p = p_space p) /\
	 (0 < prob p A) ==>
    (cond_prob p e A = SIGMA (λx. cond_prob p (e ∩ f x) A) s)``,
rw[]
\\ DEP_REWRITE_TAC[cond_prob_alt]
\\ rw[]
\\ sg `!x. cond_prob p (e ∩ f x) A =
          prob p ((e ∩ A) INTER f x) / prob p A`
>- (rw[cond_prob_alt] \\ metis_tac[GSYM INTER_ASSOC,INTER_COMM])
\\ pop_orw
\\ DEP_REWRITE_TAC[PROB_REAL_SUM_IMAGE_FN]
\\ rw[]
>- (rw[EVENTS_INTER])
>- (SUBST_OCCS_TAC [([1], SPECL [``e:'a->bool``,``A:'a->bool``] INTER_COMM)]
   \\ once_rewrite_tac[GSYM INTER_ASSOC]
   \\ rw[EVENTS_INTER])
\\ rw[real_div]
\\ once_rewrite_tac[REAL_MUL_COMM]
\\ DEP_REWRITE_TAC[real_sigmaTheory.REAL_SUM_IMAGE_CMUL]
\\ rw[]);



val Decomposition_CI_lemma1 = store_thm("Decomposition_CI_lemma1",
  ``!X Y Z s W' p.
     (prob_space p ∧
     X IN events p /\
     Z ∈ events p ∧
     Y ∈ events p ∧
    (∀x. x ∈ s ⇒ W' x ∈ events p) ∧
    FINITE s ∧
    (∀x y. x ∈ s ∧ y ∈ s ∧ x ≠ y ⇒ DISJOINT (W' x) (W' y)) ∧
    (BIGUNION (IMAGE W' s) ∩ p_space p = p_space p) ∧
    0 < prob p Z) /\
    (!x. x IN s ==> cond_indep p X (Y INTER W' x) Z) ==>
    (cond_indep p X Y Z) ``,
rw[cond_indep_def]
\\ MP_TAC(Q.ISPECL[`Z:'a->bool`,`W':'b->'a->bool`,`X INTER Y`,`s:'b->bool`,`(p :(α -> bool) # ((α -> bool) -> bool) # ((α -> bool) -> real))`] cond_prob_split)
\\ rw[]
\\ DEP_ASM_REWRITE_TAC[]
\\ pop_orw
\\ rw[]
>- (rw[EVENTS_INTER])
>- (rw[EVENTS_INTER])
\\ MP_TAC(Q.ISPECL[`Z:'a->bool`,`W':'b->'a->bool`,`Y:'a->bool`,`s:'b->bool`,`(p :(α -> bool) # ((α -> bool) -> bool) # ((α -> bool) -> real))`] cond_prob_split)
\\ rw[]
\\ DEP_ASM_REWRITE_TAC[]
\\ pop_orw
\\ rw[]
>- (rw[EVENTS_INTER])
\\ DEP_REWRITE_TAC[GSYM real_sigmaTheory.REAL_SUM_IMAGE_CMUL]
\\ rw[]
\\ irule real_sigmaTheory.REAL_SUM_IMAGE_EQ
\\ rw[]
\\ fs[INTER_ASSOC]);


val Decomposition_CI_lemma2 = store_thm("Decomposition_CI_lemma2",
  ``!X Y Z s W' p.
     (prob_space p ∧
     X IN events p /\
     Z ∈ events p ∧
     W' ∈ events p ∧
    (∀x. x ∈ s ⇒ Y x ∈ events p) ∧
    FINITE s ∧
    (∀x y. x ∈ s ∧ y ∈ s ∧ x ≠ y ⇒ DISJOINT (Y x) (Y y)) ∧
    (BIGUNION (IMAGE Y s) ∩ p_space p = p_space p) ∧
    0 < prob p Z) /\
    (!x. x IN s ==> cond_indep p X (Y x INTER W') Z) ==>
    (cond_indep p X W' Z)``,
rw[cond_indep_def]
\\ MP_TAC(Q.ISPECL[`Z:'a->bool`,`Y:'b->'a->bool`,`X INTER W'`,`s:'b->bool`,`(p :(α -> bool) # ((α -> bool) -> bool) # ((α -> bool) -> real))`] cond_prob_split)
\\ rw[]
\\ DEP_ASM_REWRITE_TAC[]
\\ pop_orw
\\ rw[]
>- (rw[EVENTS_INTER])
>- (rw[EVENTS_INTER])
\\ MP_TAC(Q.ISPECL[`Z:'a->bool`,`Y:'b->'a->bool`,`W':'a->bool`,`s:'b->bool`,`(p :(α -> bool) # ((α -> bool) -> bool) # ((α -> bool) -> real))`] cond_prob_split)
\\ rw[]
\\ DEP_ASM_REWRITE_TAC[]
\\ pop_orw
\\ rw[]
>- (rw[EVENTS_INTER])
\\ DEP_REWRITE_TAC[GSYM real_sigmaTheory.REAL_SUM_IMAGE_CMUL]
\\ rw[]
\\ irule real_sigmaTheory.REAL_SUM_IMAGE_EQ
\\ rw[]
\\ fs[INTER_ASSOC]
\\ metis_tac[GSYM INTER_ASSOC,INTER_COMM]);


val cond_prob_inter_swap = store_thm("cond_prob_inter_swap",
  ``!p A B C.
  0 < prob p (B INTER C) /\ 0 < prob p C ==>
  (cond_prob p (A INTER B) C = cond_prob p A (B INTER C) * cond_prob p B C)``,
rw[cond_prob_def]
\\ rw[REAL_MUL_ASSOC,INTER_ASSOC]
\\ DEP_REWRITE_TAC[REAL_DIV_INNER_CANCEL]
\\ metis_tac[]);

val cond_prob_inter_swap1 = store_thm("cond_prob_inter_swap1",
  ``!p A B C.
  0 < prob p (B INTER C) /\ 0 < prob p C ==>
 (cond_prob p A (B INTER C) =
  cond_prob p (A INTER B) C / cond_prob p B C)``,
rw[cond_prob_inter_swap]
\\ DEP_REWRITE_TAC[REAL_EQ_RDIV_EQ]
\\ rewrite_tac[cond_prob_def]
\\ rw[REAL_LT_IMP_NE,REAL_LT_RDIV_0]);

val cond_indep_equiv = store_thm("cond_indep_equiv",
  ``!p A B C.
  0 < prob p (B INTER C) /\ 0 < prob p C /\ cond_indep p A B C ==>
  (cond_prob p A (B INTER C) = cond_prob p A C)``,
rw[cond_prob_inter_swap1]
\\ fs[cond_indep_def]
\\ DEP_REWRITE_TAC[REAL_EQ_LDIV_EQ]
\\ rewrite_tac[cond_prob_def]
\\ rw[REAL_LT_IMP_NE,REAL_LT_RDIV_0]);



val weak_union = store_thm("weak_union",
  ``!p X Y W Z.
  0 < prob p (Z INTER W) /\ 0 < prob p Z /\ cond_indep p X W Z /\
		(cond_indep p X (Y INTER W) Z) ==>
       	     	(cond_indep p X Y (Z INTER W))``,
rw[cond_indep_def]
\\ sg `cond_prob p X (Z ∩ W') = cond_prob p X Z`
>- (once_rewrite_tac[INTER_COMM]
   \\ ho_match_mp_tac cond_indep_equiv
   \\ rw[cond_indep_def]
   \\ metis_tac[INTER_COMM])
\\ pop_orw
\\ once_rewrite_tac[INTER_COMM]
\\ sg `cond_prob p Y (W' ∩ Z) = cond_prob p (Y INTER W') Z / cond_prob p W' Z`
>- (ho_match_mp_tac cond_prob_inter_swap1
   \\ metis_tac[INTER_COMM])
\\ pop_orw
\\ fs[Once EQ_SYM_EQ]
\\ rw[REAL_MUL_ASSOC]
\\ once_rewrite_tac[mult_ratr]
\\ sg `cond_prob p W' Z <> 0`
>- (rw[Once EQ_SYM_EQ] \\ ho_match_mp_tac REAL_LT_IMP_NE
   \\ rewrite_tac[cond_prob_def]
   \\ rw[REAL_LT_IMP_NE,REAL_LT_RDIV_0]
   \\ metis_tac[INTER_COMM])
\\ rw[]
\\ rw[INTER_ASSOC]
\\ DEP_REWRITE_TAC[cond_prob_inter_swap1]
\\ rw[]
>- (metis_tac[INTER_COMM])
\\ metis_tac[INTER_COMM]);

val weak_union1 = store_thm("weak_union1",
  ``!p X Y W Z k s.
  prob_space p /\
  X IN events p /\
  Z IN events p /\
  W IN events p /\
  (!x. x IN s ==> Y x IN events p) /\
  FINITE s /\
  (∀x y. x ∈ s ∧ y ∈ s ∧ x ≠ y ⇒ DISJOINT (Y x) (Y y)) /\
  0 < prob p (Z INTER W) /\ 0 < prob p Z /\ (BIGUNION (IMAGE Y s) INTER p_space p = p_space p) /\ k IN s /\
		(!x. x IN s ==> cond_indep p X (Y x INTER W) Z) ==>
       	     	(cond_indep p X (Y k) (Z INTER W))``,
rw[]
\\ match_mp_tac weak_union
\\ rw[]
\\ ho_match_mp_tac Decomposition_CI_lemma2
\\ Q.EXISTS_TAC `Y`
\\ Q.EXISTS_TAC `s`
\\ rw[]);


val contraction_CI = store_thm("contraction_CI",
  ``!p X Y Z W'.
  cond_indep p X Y Z /\ 0 < prob p Z /\ 0 < prob p (Y ∩ Z) /\
  0 < prob p (W' ∩ Z) /\
  0 < prob p (W' ∩ (Y ∩ Z)) ∧
  cond_indep p X W' (Y INTER Z) ==>
  cond_indep p X (Y INTER W') Z``,
rw[cond_indep_def]
\\ sg `cond_prob p X (Y ∩ Z) = cond_prob p X Z`
>- (ho_match_mp_tac cond_indep_equiv
   \\ rw[cond_indep_def]
   \\ metis_tac[INTER_COMM])
\\ fs[EQ_SYM_EQ] \\ pop_orw
\\ sg `cond_prob p X (Y ∩ Z) = cond_prob p X (W' ∩ (Y INTER Z))`
>- (once_rewrite_tac [EQ_SYM_EQ]
   \\ rewrite_tac[GSYM INTER_ASSOC]
   \\ ho_match_mp_tac cond_indep_equiv
   \\ rw[cond_indep_def])
\\ pop_orw
\\ DEP_REWRITE_TAC[cond_prob_inter_swap]
\\ metis_tac[INTER_ASSOC,INTER_COMM]);

val prob_neq_imp_gt0 = store_thm("prob_neq_imp_gt0",
  ``!p s. prob_space p /\
  prob p s <> 0 /\
  s IN events p ==> (0 < prob p s)``,
rw[]
\\ imp_res_tac PROB_SPACE_POSITIVE
\\ fs[POSITIVE_PROB]
\\ first_x_assum (mp_tac o Q.SPEC `s`)
\\ rw[]
\\ CCONTR_TAC
\\ metis_tac[REAL_NOT_LT,REAL_LE_LT]);



val cond_prob_UNIV = store_thm("cond_prob_UNIV",
  ``!p s.
   prob_space p /\
   s IN events p /\
   (prob p s <> 0) ==>
   (cond_prob p (p_space p) s = 1)``,
rw[cond_prob_def]
\\ DEP_REWRITE_TAC[INTER_PSPACE]
\\ rw[REAL_DIV_REFL]);



val Intersection_CI = store_thm("Intersection_CI",
  ``!p X Y Z W' s k. 
  prob_space p /\
   X ∈ events p ∧
   (∀x. x ∈ s ⇒ W' x ∈ events p) ∧
   FINITE s ∧
   (∀x y. x ∈ s ∧ y ∈ s ∧ x ≠ y ⇒ DISJOINT (W' x) (W' y)) ∧
   (BIGUNION (IMAGE W' s) ∩ p_space p = p_space p) /\
  Z IN events p /\
   0 < prob p Z ∧
    (!x. x IN s ==> (0 < prob p (W' x ∩ Z) ∧
    0 < prob p (W' x ∩ (Y ∩ Z)))) ∧
   0 < prob p (Y ∩ Z) /\ k IN s /\
  (!x. x IN s ==> cond_indep p X Y (Z INTER (W' x)) /\
  cond_indep p X (W' x) (Y INTER Z)) ==>
  cond_indep p X (Y INTER (W' k)) Z``,
rw[]
\\ irule contraction_CI
\\ rw[]
\\ rw[cond_indep_def]
\\ sg `cond_prob p (X ∩ Y) Z = cond_prob p (X ∩ Y) Z * cond_prob p (p_space p) Z`
>- (DEP_REWRITE_TAC[cond_prob_UNIV]
   \\ rw[REAL_LT_IMP_NE])
\\ pop_orw
\\ irule EQ_SYM
\\ MP_TAC(Q.ISPECL[`Z:'a->bool`,`W':'b->'a->bool`,`X:'a->bool`,`s:'b->bool`,`(p :(α -> bool) # ((α -> bool) -> bool) # ((α -> bool) -> real))`] cond_prob_split)
\\ rw[]
\\ MP_TAC(Q.ISPECL[`Z:'a->bool`,`W':'b->'a->bool`,`(p_space p):'a->bool`,`s:'b->bool`,`(p :(α -> bool) # ((α -> bool) -> bool) # ((α -> bool) -> real))`] cond_prob_split)
\\ rw[]
\\ DEP_ASM_REWRITE_TAC[]
\\ pop_orw
\\ pop_orw
\\ rpt strip_tac
>- (rw[EVENTS_SPACE])
>- (rw[EVENTS_SPACE,EVENTS_INTER])
>- (rw[EVENTS_SPACE,EVENTS_INTER])
\\ DEP_REWRITE_TAC[GSYM REAL_SUM_IMAGE_CMUL]
\\ rw[]
\\ once_rewrite_tac[REAL_MUL_COMM]
\\ DEP_REWRITE_TAC[GSYM REAL_SUM_IMAGE_CMUL]
\\ rw[]
\\ irule REAL_SUM_IMAGE_EQ
\\ rw[]
\\ sg `cond_prob p X (Z INTER W' x) = cond_prob p X (Y INTER (Z INTER W' x))`
>- (irule EQ_SYM
   \\ irule cond_indep_equiv
   \\ rw[cond_indep_def]
   \\ rw[INTER_COMM]
   \\ metis_tac[INTER_COMM,INTER_ASSOC])
\\ sg `cond_prob p X (Y ∩ (Z ∩ W' x)) = cond_prob p X (Y INTER Z)`
>- (rw[INTER_ASSOC]
   \\ once_rewrite_tac[Once INTER_COMM]
   \\ irule cond_indep_equiv
   \\ rw[cond_indep_def]
\\ rw[INTER_COMM]
\\ metis_tac[INTER_COMM,INTER_ASSOC])
\\ fs[]
\\ DEP_REWRITE_TAC[INTER_PSPACE]
\\ rw[]
\\ DEP_REWRITE_TAC[cond_prob_inter_swap]
\\ rw[]
\\ once_rewrite_tac[Once INTER_COMM]
\\ once_asm_rewrite_tac[]
\\ REAL_ARITH_TAC);

val _ = export_theory();

