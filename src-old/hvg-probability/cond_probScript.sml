

(******************************************************************************)
(*   Conditional Probability Originally Developed by Dr. Osman Hasan          *)
(*   Ported to HOL-k12 by Waqar Ahmad                                         *)
(*                                                                            *)
(******************************************************************************)


(*app load ["arithmeticTheory", "realTheory", "prim_recTheory", "seqTheory",
          "pred_setTheory","res_quanTheory", "res_quanTools", "listTheory", "numTheory", "dep_rewrite", 
          "transcTheory", "rich_listTheory","realLib", "pairTheory",
          "combinTheory","limTheory","sortingTheory", "realLib", "optionTheory","satTheory",
          "util_probTheory", "extrealTheory","probabilityTheory"];
*)

open HolKernel Parse boolLib bossLib limTheory arithmeticTheory realTheory prim_recTheory
     seqTheory pred_setTheory res_quanTheory sortingTheory res_quanTools listTheory transcTheory
     rich_listTheory pairTheory combinTheory realLib  optionTheory dep_rewrite
      util_probTheory extrealTheory probabilityTheory;

open HolKernel boolLib bossLib Parse;

val _ = new_theory "cond_prob";

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





val cond_prob_def = Define
        `cond_prob p A B = 
	if (prob p B = 0) then 0 else
			(prob p (A INTER B))/ (prob p B)`;


val COND_PROB_BOUNDS = store_thm
	("COND_PROB_BOUNDS",
(``!A B p. prob_space p /\ (A IN events p) /\ (B IN events p) ==>
        ((0 <= cond_prob p A B) /\ (cond_prob p A B <= 1))``),
rw[cond_prob_def]
>- (irule REAL_LE_DIV
   \\ DEP_REWRITE_TAC[PROB_POSITIVE,EVENTS_INTER] \\ metis_tac[])
\\ sg `0 < prob p B`
>- (CCONTR_TAC
    >- (fs [REAL_NOT_LT, REAL_LE_LT] \\ pop_assum mp_tac
       \\ rw [REAL_NOT_LT]
       \\ DEP_REWRITE_TAC[PROB_POSITIVE,EVENTS_INTER] \\ metis_tac[])
    \\ metis_tac[])
\\ rw[REAL_LE_LDIV_EQ]
\\ irule PROB_INCREASING
\\ metis_tac[EVENTS_INTER,INTER_SUBSET]);

val COND_PROB_ITSELF = store_thm
("COND_PROB_ITSELF",
(``!B p. prob_space p /\ (B IN events p) /\ (0 < prob p B) ==>
          ((cond_prob p B B = 1))``),
	rw [cond_prob_def, INTER_IDEMPOT, REAL_DIV_REFL]);


val COND_PROB_COUNTABLY_ADDITIVE = store_thm
	("COND_PROB_COUNTABLY_ADDITIVE",
(``!A B p s.
  prob_space p /\ (B IN events p) /\ (A IN (UNIV -> events p)) /\
        (!a b. ~(a = b) ==> DISJOINT (A a) (A b)) /\
        (s = BIGUNION (IMAGE A UNIV)) ==>
        ((\n. cond_prob p (A n) B) sums cond_prob p s B)``),
rw[cond_prob_def]
>- (rw[sums, SUM_0, SEQ_CONST])
\\ `(\n. prob p (A n INTER B) / prob p B) =
                (\n. (\n. prob p (A n INTER B)) n / prob p B)` by rw[]
\\ asm_rewrite_tac[]
\\ WEAKEN_TAC is_eq
\\ irule SER_CDIV
\\ `(\n. prob p (A n INTER B)) =
                prob p o (\n. A n INTER B)` by rw[o_DEF]
\\ asm_rewrite_tac[]
\\ WEAKEN_TAC is_eq
\\ irule PROB_COUNTABLY_ADDITIVE
\\ fs[EVENTS_INTER,IN_FUNSET,DISJOINT_DEF,IN_BIGUNION_IMAGE,IN_BIGUNION,INTER_DEF,EXTENSION,GSPECIFICATION]
\\ metis_tac[]);

val COND_PROB_COMPL = store_thm
	("COND_PROB_COMPL",
(``!A B p. prob_space p /\
        (A IN events p) /\ (COMPL A IN events p) /\
        (B IN events p) /\ (0 < (prob p B)) ==>
        (cond_prob p (COMPL A) B = 1 - cond_prob p A B)``),
rw [cond_prob_def, REAL_EQ_LDIV_EQ, REAL_DIV_RMUL, REAL_SUB_RDISTRIB,
                REAL_EQ_SUB_LADD]
\\ sg `prob p ((COMPL A) INTER B) + prob p (A INTER B) =
        prob p (((COMPL A) INTER B) UNION
        (A INTER B))`
>- (once_rewrite_tac [EQ_SYM_EQ]
    \\ irule PROB_ADDITIVE
    \\ rw [EVENTS_INTER, DISJOINT_DEF, EXTENSION]
    \\ SRW_TAC[][GSPECIFICATION, IN_COMPL, IN_INTER]
    \\ METIS_TAC [])
\\ rewrite_tac[REAL_DIV_ADD]
\\ asm_rewrite_tac []
\\ DEP_ONCE_REWRITE_TAC[ONCE_REWRITE_RULE [UNION_COMM] (COMPL_SPLITS)]
\\  metis_tac[REAL_DIV_REFL]);

val RAND_THM = store_thm
  ("RAND_THM",
   ``!f x y. (x = y) ==> (f x = f y)``,
   RW_TAC std_ss []);

val COND_PROB_DIFF = store_thm
	("COND_PROB_DIFF",
	(``!A1 A2 B p. prob_space p /\
        (A1 IN events p) /\ (A2 IN events p) /\
        (B IN events p)  ==>
        (cond_prob p (A1 DIFF A2) B =
	(cond_prob p A1 B) - (cond_prob p (A1 INTER A2) B))``),
rw [cond_prob_def, REAL_EQ_SUB_LADD, real_div, GSYM REAL_RDISTRIB,
        REAL_EQ_RMUL]
\\ DISJ2_TAC
\\ sg `prob p ((A1 DIFF A2) INTER B) + prob p (A1 INTER A2 INTER B) =
        prob p (((A1 DIFF A2) INTER B) UNION (A1 INTER A2 INTER B))`
>- (once_rewrite_tac[EQ_SYM_EQ]
    \\ irule PROB_ADDITIVE
    \\ rw [EVENTS_INTER, DISJOINT_DEF, EXTENSION]
    >- (metis_tac[])
    \\ rw[EVENTS_INTER,EVENTS_DIFF])
\\ once_asm_rewrite_tac[]
\\ irule RAND_THM
\\ SRW_TAC[][EXTENSION,GSPECIFICATION, IN_INTER, IN_UNION, IN_DIFF]
\\ metis_tac[]);


val COND_PROB_UNION = store_thm
("COND_PROB_UNION",
(``!A1 A2 B p. prob_space p /\ 
        (A1 IN events p) /\ (A2 IN events p) /\
        (B IN events p)  ==>
        (cond_prob p (A1 UNION A2) B = (cond_prob p A1 B) +
                (cond_prob p A2 B) - (cond_prob p (A1 INTER A2) B))``),
rw[]
\\ once_rewrite_tac[REAL_ADD_SYM]
\\ `cond_prob p A1 B - cond_prob p (A1 INTER A2) B =
        cond_prob p (A1 DIFF A2) B` by metis_tac[COND_PROB_DIFF]
\\ `cond_prob p A2 B + cond_prob p A1 B - cond_prob p (A1 INTER A2) B =
        cond_prob p A2 B + (cond_prob p A1 B - cond_prob p (A1 INTER A2) B)`
	by REAL_ARITH_TAC
\\ once_asm_rewrite_tac[]
\\ WEAKEN_TAC is_eq
\\ once_asm_rewrite_tac[]
\\ WEAKEN_TAC is_eq
\\ rw [cond_prob_def, REAL_EQ_SUB_LADD, real_div, GSYM REAL_RDISTRIB,
        REAL_EQ_RMUL]
\\ DISJ2_TAC
\\ sg `prob p (A2 INTER B) + prob p ((A1 DIFF A2) INTER B) =
        prob p ((A2 INTER B) UNION ((A1 DIFF A2) INTER B))`
>- (once_rewrite_tac [EQ_SYM_EQ]
    \\ irule PROB_ADDITIVE
    \\ rw [EVENTS_INTER, DISJOINT_DEF, EXTENSION]
    >- (metis_tac[])
    \\ rw [EVENTS_INTER,EVENTS_DIFF])
\\ asm_rewrite_tac [] 
\\ AP_TERM_TAC
\\ SRW_TAC[][GSPECIFICATION, IN_INTER, IN_UNION, IN_DIFF,EXTENSION] 
\\ metis_tac[]);


val COND_PROB_MUL_RULE = store_thm
("COND_PROB_MUL_RULE",
(``!A B p. prob_space p /\
    (A IN events p) /\ (B IN events p) ==>
	(prob p (A INTER B) = (prob p B) * (cond_prob p A B))``),
rw[cond_prob_def]
\\ Cases_on `A SUBSET B`
>- (sg `(A INTER B) = A`
   >- (pop_assum mp_tac
      \\ SRW_TAC[] [GSPECIFICATION, IN_INTER, SUBSET_DEF,EXTENSION]
      \\ metis_tac[])
   \\ asm_rewrite_tac[]
   \\ rewrite_tac [GSYM REAL_LE_ANTISYM]
    \\ CONJ_TAC
    >- (fs [EQ_SYM_EQ]
        \\ rw [PROB_INCREASING])
    \\ rw[PROB_POSITIVE])
>- (Cases_on `B SUBSET A`
   >- (once_rewrite_tac [INTER_COMM]
      \\ sg `B INTER A = B`
      >- (rw [GSYM SUBSET_INTER_ABSORPTION]) 
      \\ sg `(A INTER B) SUBSET B`
      >- (fs [SUBSET_DEF, IN_INTER])
      \\ rw [GSYM REAL_LE_ANTISYM])
   \\ sg `(A INTER B) SUBSET B`
   >- (fs [SUBSET_DEF, IN_INTER])
   \\ rw[GSYM REAL_LE_ANTISYM]
   >- (fs [EQ_SYM_EQ]
      \\ rw[PROB_INCREASING,EVENTS_INTER])
   \\ rw[PROB_POSITIVE,EVENTS_INTER])
\\ rw [real_div]
\\ once_rewrite_tac [GSYM REAL_MUL_SYM]
\\ rw [GSYM REAL_MUL_ASSOC]
\\ rw [REAL_MUL_LINV]);


val BAYES_RULE = store_thm
	("BAYES_RULE",
	(``!A B p. prob_space p /\
	(A IN events p) /\ (B IN events p) /\ (0 < (prob p A)) ==>
	(cond_prob p B A = ((cond_prob p A B) * prob p B)/(prob p A))``),
rw []
\\ once_rewrite_tac [REAL_MUL_SYM]
\\ sg `prob p B * cond_prob p A B = prob p (A INTER B)`
>- (once_rewrite_tac [EQ_SYM_EQ]
    \\ irule COND_PROB_MUL_RULE
    \\ asm_rewrite_tac [])
\\ asm_rewrite_tac []
\\ WEAKEN_TAC is_eq
\\ rw[cond_prob_def]
>- (fs [])
\\ metis_tac [INTER_COMM]);

val TOTAL_PROB = store_thm
	("TOTAL_PROB",
	(``!A B n p. prob_space p /\
	(A IN events p) /\ (B IN (count n -> events p)) /\
        (!a b. a < n /\ b < n /\ ~(a = b) ==> DISJOINT (B a) (B b)) /\
        (BIGUNION (IMAGE B (count n)) = UNIV) ==>
        (prob p A = sum (0, n) (\i. (prob p (B i)) * (cond_prob p A (B i))))``),
NTAC 4 (GEN_TAC)
\\ Cases_on `n`
>- (rw[count_def, IMAGE_DEF, sum])
\\ rw [count_def, IN_COUNT, IN_BIGUNION, IN_IMAGE, IMAGE_DEF]
\\ sg `sum (0,SUC n') (\i. prob p (B i) * cond_prob p A (B i)) =
                sum (0, SUC n') (\i. prob p (A INTER (B i)))`
>- (irule SUM_EQ
   \\ rw[]
   \\ once_rewrite_tac[EQ_SYM_EQ]
   \\ irule COND_PROB_MUL_RULE
   \\ asm_rewrite_tac[]
   \\ pop_assum mp_tac
   \\ qpat_assum `B ∈ ({m | m < SUC n'} -> events p)` (mp_tac)
   \\ fs [IN_FUNSET, count_def])
\\ pop_orw
\\ sg `sum (0,SUC n') (\i. prob p (A INTER B i)) =
                prob p (BIGUNION (IMAGE (\i. (A INTER B i)) (count (SUC n'))))`
>- (sg `(\i. prob p (A INTER B i)) = prob p o (\i. A INTER B i)`
   >-(SRW_TAC[][o_DEF])
   \\ asm_rewrite_tac[]
   \\ WEAKEN_TAC is_eq
   \\ irule PROB_FINITELY_ADDITIVE
   \\ rw[IN_FUNSET,count_def,EVENTS_INTER]
   >- (fs[EXTENSION,GSPECIFICATION,DISJOINT_DEF,IN_INTER] \\ metis_tac[])
   \\ irule EVENTS_INTER
   \\ fs[IN_FUNSET])
\\ pop_orw
\\ irule RAND_THM
\\ rewrite_tac [EXTENSION]
\\ PSET_TAC [IN_BIGUNION_IMAGE, IN_INTER, GSPECIFICATION, IN_COUNT]
\\ fs[EXTENSION, IN_BIGUNION, GSPECIFICATION]
\\ EQ_TAC
>- (POP_ASSUM (MP_TAC o Q.SPEC `x`)
   \\ rw []
   \\ Q.EXISTS_TAC `x':num`
   \\ rw[]
   \\ metis_tac[])
\\ rw[] \\ metis_tac[]);

val BAYES_RULE_GENERAL = store_thm
	("BAYES_RULE_GENERAL",
	(``!A B n k p. prob_space p /\
	(A IN events p) /\ (B IN (count n -> events p)) /\
        (!a b. a < n /\ b < n /\ ~(a = b) ==> DISJOINT (B a) (B b)) /\
        (BIGUNION (IMAGE B (count n)) = UNIV) /\ (0 < (prob p A)) /\
        (k < n) ==>
        (cond_prob p (B k) A = ((cond_prob p A (B k)) * prob p (B k))/
                (sum (0, n) (\i. (prob p (B i)) * (cond_prob p A (B i)))))``),
rw[GSYM TOTAL_PROB]
\\ once_rewrite_tac[REAL_MUL_SYM]
\\ sg `prob p (B k) * cond_prob p A (B k) = prob p (A INTER (B k))`
>- (once_rewrite_tac[EQ_SYM_EQ]
   \\ irule COND_PROB_MUL_RULE
   \\ fs[IN_FUNSET,count_def])
\\ pop_orw
\\ rw[cond_prob_def]
>- (fs[])
\\ metis_tac [INTER_COMM]);

val _ = export_theory();
