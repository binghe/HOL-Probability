(* ========================================================================= *)
(*                                                                           *)
(*                    Formalization of the M/M/1 Queue                       *)
(*             This code is developed using HOL4 kanaskas 9.                 *)
(*                                                                           *)
(*                       Chaouch Donia, 2017                                 *)
(*                       Hardware Verification Group,                        *)
(*                       Concordia University                                *)
(*                                                                           *)
(*                                                                           *)
(*                      Last update: August, 2017                            *)
(*                                                                           *)
(* ========================================================================= *)


(* ========================================================================= *)
(*                 Conditional Probability 				     *)
(* ========================================================================= *)
set_trace "Unicode" 0;


app load ["bossLib", "metisLib", "arithmeticTheory", "pred_setTheory", "realLib", "pairTheory", "combinTheory", "listTheory", "transcTheory", "numLib", "prim_recTheory", "probabilityTheory" ,"mesonLib", "subtypeTheory"];


open HolKernel Parse boolLib bossLib metisLib numLib combinTheory subtypeTheory
pred_setTheory measureTheory arithmeticTheory realTheory 
realLib pairTheory transcTheory prim_recTheory extrealTheory probabilityTheory mesonLib;
	  
app load ["HolKernel", "Parse", "boolLib", "bossLib", "arithmeticTheory", "polyTheory","realTheory", "realLib",  "jrhUtils", "seqTheory", "limTheory", "transcTheory", "listTheory", "pred_setTheory", "mesonLib", "boolTheory", "probabilityTheory","measureTheory","util_probTheory","pred_setLib","numLib", "extrealTheory","combinTheory","lebesgueTheory","real_sigmaTheory"];

open HolKernel Parse boolLib bossLib arithmeticTheory  polyTheory realTheory 
realLib  jrhUtils realSimps simpLib seqTheory limTheory transcTheory listTheory
pred_setTheory mesonLib boolTheory measureTheory probabilityTheory util_probTheory 
pred_setLib numLib extrealTheory combinTheory lebesgueTheory real_sigmaTheory ;

fun SET_TAC L =
    POP_ASSUM_LIST(K ALL_TAC) THEN REPEAT COND_CASES_TAC THEN
    REWRITE_TAC (append [EXTENSION, SUBSET_DEF, PSUBSET_DEF, DISJOINT_DEF,
    SING_DEF] L) THEN SIMP_TAC std_ss [NOT_IN_EMPTY, IN_UNIV, IN_UNION,
    IN_INTER, IN_DIFF, IN_INSERT, IN_DELETE, IN_BIGINTER, IN_BIGUNION,
    IN_IMAGE, GSPECIFICATION, IN_DEF] THEN MESON_TAC [];

fun SET_RULE tm = prove(tm,SET_TAC []);


val set_rewrs
= [INTER_EMPTY, INTER_UNIV, UNION_EMPTY, UNION_UNIV, DISJOINT_UNION,
DISJOINT_INSERT, DISJOINT_EMPTY, GSYM DISJOINT_EMPTY_REFL,
DISJOINT_BIGUNION, INTER_SUBSET, INTER_IDEMPOT, UNION_IDEMPOT,
SUBSET_UNION];

val UNIONL_def = Define `(UNIONL [] = {})
/\ (UNIONL (s::ss) = (s:'a->bool) UNION UNIONL ss)`;



val elt_rewrs
= [SUBSET_DEF, IN_COMPL, IN_DIFF, IN_UNIV, NOT_IN_EMPTY, IN_UNION,
IN_INTER, IN_IMAGE, IN_FUNSET, IN_DFUNSET, GSPECIFICATION,
DISJOINT_DEF, IN_BIGUNION, IN_BIGINTER, IN_COUNT, IN_o, IN_DELETE, IN_PREIMAGE, IN_SING, IN_INSERT];


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
THEN RW_TAC pset_set_ss ths 
THEN REPEAT (POP_ASSUM MP_TAC)
THEN RW_TAC pset_elt_ss ths;

infixr 0 ++ << || ORELSEC ## --> THENC;
infix 1 >> |->;
fun parse_with_goal t (asms, g) =
  let
    val ctxt = free_varsl (g::asms)
  in
    Parse.parse_in_context ctxt t
  end;

val PARSE_TAC = fn tac => fn q => W (tac o parse_with_goal q);
val Suff = PARSE_TAC SUFF_TAC;
val POP_ORW = POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm]);
val !! = REPEAT;
val op++ = op THEN;
val op<< = op THENL;
val op|| = op ORELSE;
val op>> = op THEN1;
val std_ss' = simpLib.++ (std_ss, boolSimps.ETA_ss);

val INTER_ASSOC = GSYM INTER_ASSOC;
val UNION_ASSOC = GSYM UNION_ASSOC;

val cond_prob_def = Define
   `cond_prob p e1 e2 = (prob p (e1 INTER e2)) / (prob p e2)`;
	  
val THREE_SETS_INTER = store_thm
  ("THREE_SETS_INTER",
   ``!A B C. A INTER B INTER (C INTER B) = A INTER C INTER B``,
             METIS_TAC [INTER_COMM, INTER_IDEMPOT, INTER_ASSOC]);


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
       RW_TAC std_ss [] ++ (MP_TAC o Q.SPECL [`p`, `B`, `A`]) PROB_INTER_ZERO  
  ++ RW_TAC std_ss [INTER_COMM]); 
          
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
 ++ Cases_on `prob p C = 0` 
 >> METIS_TAC [EVENTS_INTER, COND_PROB_ZERO, REAL_LE_REFL]
 ++ RW_TAC std_ss [cond_prob_def, real_div]
 ++ `(A INTER B INTER C) SUBSET (A INTER C)` by SET_TAC []
 ++ METIS_TAC [PROB_POSITIVE, REAL_LT_LE, REAL_INV_POS, PROB_INCREASING, 
    EVENTS_INTER, REAL_LE_RMUL]);





val POS_COND_PROB_IMP_POS_PROB = store_thm
  ("POS_COND_PROB_IMP_POS_PROB",
  ``!A B p. prob_space p /\ A IN events p /\ B IN events p /\ 
  	(0 < cond_prob p A B) ==> (prob p (A INTER B) <> 0)``,
    RW_TAC std_ss []
 ++ `0 <= prob p B` by RW_TAC std_ss [PROB_POSITIVE]
 ++ `prob p B <> 0` by (SPOSE_NOT_THEN STRIP_ASSUME_TAC 
 	++ `cond_prob p A B = 0` by METIS_TAC [COND_PROB_ZERO]
 	++ METIS_TAC [REAL_LT_IMP_NE])
 ++ FULL_SIMP_TAC std_ss [cond_prob_def]
 ++ `0 / prob p B = 0` by METIS_TAC [REAL_DIV_LZERO]
 ++ METIS_TAC [REAL_LT_IMP_NE]);
              
val COND_PROB_BOUNDS = store_thm
    ("COND_PROB_BOUNDS",
    (--`!p A B. prob_space p /\ A IN events p /\ B IN events p ==> 
        0 <= cond_prob p A B /\ cond_prob p A B <= 1`--),
     RW_TAC std_ss [] 
  >> METIS_TAC [cond_prob_def, EVENTS_INTER, PROB_POSITIVE, REAL_LE_DIV]
  ++ Cases_on `prob p B = 0` >> METIS_TAC [COND_PROB_ZERO, REAL_LE_01]
  ++ `0 < prob p B` by METIS_TAC [PROB_POSITIVE, REAL_LT_LE] 
  ++ `(cond_prob p A B <= 1) = (cond_prob p A B * prob p B <= 1 * prob p B)` 
  	by RW_TAC std_ss [REAL_LE_RMUL] ++ POP_ORW
  ++ RW_TAC std_ss [REAL_MUL_LID, cond_prob_def, REAL_DIV_RMUL] 
  ++ `(A INTER B) SUBSET B` by RW_TAC std_ss [INTER_SUBSET]
  ++ FULL_SIMP_TAC std_ss [PROB_INCREASING, EVENTS_INTER]);


val REAL_NEG_NZ = store_thm
  ("REAL_NEG_NZ",``!(x:real). x<0 ==> x <>0``,
  	 RW_TAC real_ss []
 	 ++ `0<-x` by RW_TAC real_ss [REAL_NEG_GT0]         
  	 ++ `-x <>0` by FULL_SIMP_TAC real_ss [REAL_POS_NZ]
	 ++ `x<>0` by (SPOSE_NOT_THEN ASSUME_TAC ++ METIS_TAC [GSYM REAL_EQ_NEG,REAL_NEG_0])
  );

val COND_PROB_ITSELF = store_thm
  ("COND_PROB_ITSELF",
  (--`!p B. (prob_space p) /\(B IN events p) /\ (0 < prob p B) ==> 
            ((cond_prob p B B = 1))`--),
	RW_TAC real_ss [cond_prob_def, INTER_IDEMPOT]
 ++ `prob p B <> 0` by METIS_TAC [REAL_NEG_NZ]
 ++ METIS_TAC [REAL_DIV_REFL]);

val COND_PROB_COMPL = store_thm
  ("COND_PROB_COMPL",
  (--`!A B p . (prob_space p) /\ (A IN events p) /\ (COMPL A IN events p) /\
               (B IN events p) /\ (0 < (prob p B)) ==>
        (cond_prob p (COMPL A) B = 1 - cond_prob p A B)`--),
    RW_TAC std_ss [cond_prob_def]
 ++ `prob p B <> 0` by METIS_TAC [REAL_NEG_NZ]
 ++ `(prob p (COMPL A INTER B) / prob p B = 1 - prob p (A INTER B) / prob p B) =
     (prob p (COMPL A INTER B) / prob p B * prob p B = (1 - prob p (A INTER B) / prob p B) * prob p B)` 
     by METIS_TAC [REAL_EQ_RMUL] ++ POP_ORW 
 ++ RW_TAC std_ss [REAL_DIV_RMUL, REAL_SUB_RDISTRIB, REAL_MUL_LID, REAL_EQ_SUB_LADD] 
 ++ `prob p ((COMPL A) INTER B) + prob p (A INTER B) =
       prob p (((COMPL A) INTER B) UNION (A INTER B))` 
       by (ONCE_REWRITE_TAC [EQ_SYM_EQ] ++ MATCH_MP_TAC PROB_ADDITIVE 
          ++ RW_TAC std_ss [EVENTS_INTER, DISJOINT_DEF, EXTENSION]
          ++ RW_TAC std_ss [NOT_IN_EMPTY, IN_COMPL, IN_INTER] ++ METIS_TAC []) ++ POP_ORW
 ++ `(COMPL A INTER B UNION A INTER B) = B` 
        by (SET_TAC [EXTENSION, IN_INTER, IN_UNION, IN_COMPL] ++ METIS_TAC []) 
 ++ RW_TAC std_ss []);
 
(*===========================================================*)
val COND_PROB_DIFF = store_thm
  ("COND_PROB_DIFF",
  (--`!p A1 A2 B.(prob_space p) /\ (A1 IN events p) /\ (A2 IN events p) /\ (B IN events p) ==>
        (cond_prob p (A1 DIFF A2) B = 
         cond_prob p A1 B - cond_prob p (A1 INTER A2) B)`--),        
    RW_TAC std_ss [] 
 ++ Cases_on `prob p B = 0` 
 >> RW_TAC std_ss [COND_PROB_ZERO, REAL_SUB_RZERO, EVENTS_INTER, EVENTS_DIFF] 
 ++ RW_TAC std_ss [cond_prob_def] 
 ++ `(A1 DIFF A2) INTER B IN events p` by METIS_TAC [EVENTS_INTER, EVENTS_DIFF]
 ++ `(prob p ((A1 DIFF A2) INTER B) / prob p B =
    prob p (A1 INTER B) / prob p B - prob p (A1 INTER A2 INTER B) / prob p B) =
    (prob p ((A1 DIFF A2) INTER B) / prob p B * prob p B =
    (prob p (A1 INTER B) / prob p B - prob p (A1 INTER A2 INTER B) / prob p B) * prob p B)`
    by METIS_TAC [REAL_EQ_RMUL] ++ POP_ORW
 ++ `A1 INTER B IN events p` by METIS_TAC [EVENTS_INTER] 
 ++ `A1 INTER A2 INTER B IN events p` by METIS_TAC [EVENTS_INTER]
 ++ RW_TAC std_ss [REAL_DIV_RMUL, REAL_SUB_RDISTRIB, REAL_EQ_SUB_LADD]
 ++ `prob p ((A1 DIFF A2) INTER B) + prob p (A1 INTER A2 INTER B) =
        prob p (((A1 DIFF A2) INTER B) UNION (A1 INTER A2 INTER B))`
        by (ONCE_REWRITE_TAC [EQ_SYM_EQ] ++ MATCH_MP_TAC PROB_ADDITIVE 
           ++ RW_TAC std_ss [EVENTS_INTER, EVENTS_DIFF, DISJOINT_DEF, EXTENSION]
           ++ RW_TAC std_ss [IN_DIFF, IN_INTER, NOT_IN_EMPTY] ++ PROVE_TAC [])
 ++ `((A1 DIFF A2) INTER B UNION A1 INTER A2 INTER B) = (A1 INTER B)` 
        by (RW_TAC std_ss [EXTENSION, IN_INTER, IN_DIFF, IN_UNION] THEN PROVE_TAC [])
 ++ RW_TAC std_ss []);

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
 ++ Cases_on `prob p B = 0`
 >> RW_TAC std_ss [REAL_MUL_RZERO, COND_PROB_INTER_ZERO, REAL_MUL_LZERO]        
 ++ Cases_on `prob p A = 0`
 >> RW_TAC std_ss [REAL_MUL_LZERO, COND_PROB_INTER_ZERO, REAL_MUL_RZERO] 
 ++ RW_TAC std_ss [cond_prob_def, REAL_DIV_RMUL, INTER_COMM]);    
    
val COND_PROB_UNION = prove
  (``! p A1 A2 B. 
  	(prob_space p) /\ (A1 IN events p) /\ (A2 IN events p) /\ (B IN events p)  ==>
	(cond_prob p (A1 UNION A2) B = 
	(cond_prob p A1 B) + (cond_prob p A2 B) - (cond_prob p (A1 INTER A2) B))``,
    RW_TAC std_ss [] 
 ++ `cond_prob p A1 B + cond_prob p A2 B = cond_prob p A2 B + cond_prob p A1 B`
        by RW_TAC std_ss [REAL_ADD_COMM] ++ POP_ORW 
 ++ `cond_prob p A2 B + cond_prob p A1 B - cond_prob p (A1 INTER A2) B =
     cond_prob p A2 B + (cond_prob p A1 B - cond_prob p (A1 INTER A2) B)` by REAL_ARITH_TAC  
 ++ `cond_prob p A1 B - cond_prob p (A1 INTER A2) B = cond_prob p (A1 DIFF A2) B` 
        by PROVE_TAC [COND_PROB_DIFF] ++ RW_TAC std_ss [] 
 ++ Cases_on `prob p B = 0`
 >> RW_TAC std_ss [COND_PROB_ZERO, EVENTS_DIFF, EVENTS_UNION, REAL_ADD_LID] 
 ++ `(cond_prob p (A1 UNION A2) B = cond_prob p A2 B + cond_prob p (A1 DIFF A2) B) =
     (cond_prob p (A1 UNION A2) B * prob p B = 
        (cond_prob p A2 B + cond_prob p (A1 DIFF A2) B) * prob p B)` by METIS_TAC [REAL_EQ_RMUL] 
 ++ POP_ORW ++ RW_TAC std_ss [REAL_DIV_RMUL, cond_prob_def, REAL_ADD_RDISTRIB] 
 ++ `(A1 UNION A2) INTER B IN events p` by METIS_TAC [EVENTS_UNION, EVENTS_INTER] 
 ++ `A2 INTER B IN events p` by METIS_TAC [EVENTS_INTER] 
 ++ `(A1 DIFF A2) INTER B IN events p` by METIS_TAC [EVENTS_INTER, EVENTS_DIFF] 
 ++ `prob p (A2 INTER B) + prob p ((A1 DIFF A2) INTER B) =
       prob p ((A2 INTER B) UNION ((A1 DIFF A2) INTER B))` 
       by (ONCE_REWRITE_TAC [EQ_SYM_EQ] ++ MATCH_MP_TAC PROB_ADDITIVE 
          ++ RW_TAC std_ss [EVENTS_INTER, EVENTS_DIFF, DISJOINT_DEF, EXTENSION] 
          ++ RW_TAC std_ss [IN_INTER, IN_DIFF, NOT_IN_EMPTY] ++ PROVE_TAC [])
 ++ `(A2 INTER B UNION (A1 DIFF A2) INTER B) = ((A1 UNION A2) INTER B)` 
        by (RW_TAC std_ss [EXTENSION, IN_INTER, IN_DIFF, IN_UNION] THEN PROVE_TAC []) 
 ++ RW_TAC std_ss []);

val INSERT_THM1 = store_thm
("INSERT_THM1",
``!(x:'a) s. x IN (x INSERT s)``, RW_TAC std_ss [IN_INSERT]);

val INSERT_THM2 = store_thm
("INSERT_THM2",
``!(x:'a) y s. x IN s ==> x IN (y INSERT s)``, RW_TAC std_ss [IN_INSERT]);


val PROB_FINITE_ADDITIVE = store_thm
  ("PROB_FINITE_ADDITIVE",
  ``!s p f t. prob_space p /\ FINITE s /\ (!x. x IN s ==> f x IN events p) /\
       (!a b. (a:'b) IN s /\ b IN s /\ ~(a = b) ==> DISJOINT (f a) (f b)) /\
       (t = BIGUNION (IMAGE f s)) ==> (prob p t = SIGMA (prob p o f) s)``,
    Suff `!s. FINITE (s:'b -> bool) ==> 
	((\s. !p f t. prob_space p  /\ (!x. x IN s ==> f x IN events p) /\
	(!a b. a IN s /\ b IN s /\ a <> b ==> DISJOINT (f a) (f b)) /\   
	(t = BIGUNION (IMAGE f s)) ==> (prob p t = SIGMA (prob p o f) s)) s)` >> METIS_TAC []
 ++ MATCH_MP_TAC FINITE_INDUCT ++ RW_TAC std_ss [IMAGE_EMPTY] 
 >> RW_TAC std_ss [REAL_SUM_IMAGE_THM, BIGUNION_EMPTY, PROB_EMPTY] 
 ++ `SIGMA (prob p o f) ((e:'b) INSERT s) = (prob p o f) e + SIGMA (prob p o f) (s DELETE e)` 
	by RW_TAC std_ss [REAL_SUM_IMAGE_THM] 
 ++ `s DELETE (e:'b) = s` by FULL_SIMP_TAC std_ss [DELETE_NON_ELEMENT]
 ++ RW_TAC std_ss [IMAGE_INSERT, BIGUNION_INSERT] 
 ++ `DISJOINT (f e)  (BIGUNION (IMAGE f s))` 
        by (PSET_TAC [DISJOINT_BIGUNION, IN_IMAGE] 
           ++ `e IN e INSERT s` by FULL_SIMP_TAC std_ss [INSERT_THM1] 
           ++ `x IN e INSERT s` by FULL_SIMP_TAC std_ss [INSERT_THM2] 
           ++ `e <> x` by PSET_TAC [] >> METIS_TAC [] ++ FULL_SIMP_TAC std_ss []) 
 ++ `(f e) IN events p` by FULL_SIMP_TAC std_ss [IN_FUNSET, INSERT_THM1] 
 ++ `BIGUNION (IMAGE f s) IN events p`
        by (MATCH_MP_TAC EVENTS_COUNTABLE_UNION ++ RW_TAC std_ss [] 
           >> (RW_TAC std_ss [SUBSET_DEF,IN_IMAGE] THEN METIS_TAC [IN_INSERT]) 
           ++ MATCH_MP_TAC COUNTABLE_IMAGE ++ RW_TAC std_ss [FINITE_COUNTABLE]) 
 ++ `(prob p (f e UNION BIGUNION (IMAGE f s))) = prob p (f e) + prob p (BIGUNION (IMAGE f s))`
        by (MATCH_MP_TAC PROB_ADDITIVE ++ FULL_SIMP_TAC std_ss [])
 ++ RW_TAC std_ss [INSERT_THM1, INSERT_THM2]);




val INTER_BIGUNION = store_thm
  ("INTER_BIGUNION",
   ``!s a. s INTER BIGUNION a = BIGUNION (IMAGE ($INTER s) a)``,
   RW_TAC std_ss [EXTENSION, IN_INTER, IN_BIGUNION_IMAGE]
   ++ RW_TAC std_ss [IN_BIGUNION]
   ++ PROVE_TAC []);

val BAYES_RULE = store_thm
  ("BAYES_RULE",
  (--`!A B p. (prob_space p) /\ (A IN events p) /\ (B IN events p) ==>
	(cond_prob p B A = ((cond_prob p A B) * prob p B)/(prob p A))`--),
    RW_TAC std_ss []	
 ++ Cases_on `prob p B = 0` 
 >> RW_TAC std_ss [COND_PROB_ZERO, COND_PROB_INTER_ZERO, REAL_MUL_LZERO, REAL_DIV_LZERO] 
 ++ `!(x:real) y z w. x * y * z * w = x * (y * z) * w` by METIS_TAC [REAL_MUL_ASSOC]
 ++ RW_TAC std_ss [cond_prob_def, real_div, REAL_DIV_RMUL, INTER_COMM, REAL_MUL_LINV, REAL_MUL_RID]);

val TOTAL_PROB_SIGMA = store_thm
  ("TOTAL_PROB_SIGMA",
  ``!p B A s. (prob_space p) /\ (A IN events p) /\ FINITE s /\ 
	(!x . x IN s ==> B x IN events p) /\
        (!a b. a IN s /\ b IN s /\ ~(a = b) ==> DISJOINT (B a) (B b)) /\
        (BIGUNION (IMAGE B s) = p_space p) ==>
        (prob p A = SIGMA (\i. (prob p (B i))* (cond_prob p A (B i))) s)``,
    RW_TAC std_ss [] 
 ++ `SIGMA (\i. prob p (B i) * cond_prob p A (B i)) (s:'b -> bool) = 
        SIGMA (\i. prob p (A INTER (B i))) s `
        by ((MATCH_MP_TAC o Q.ISPEC `s:'b -> bool`) REAL_SUM_IMAGE_EQ ++ RW_TAC std_ss []
	   ++ Cases_on `prob p (B x) = 0` >> RW_TAC std_ss [REAL_MUL_LZERO, PROB_INTER_ZERO]
	   ++ RW_TAC std_ss [cond_prob_def, REAL_DIV_LMUL]) 
 ++ RW_TAC std_ss [] ++ MATCH_MP_TAC PROB_REAL_SUM_IMAGE_FN 
 ++ RW_TAC std_ss [EVENTS_INTER, INTER_IDEMPOT]); 

fun K_TAC _ = ALL_TAC;



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
    RW_TAC std_ss [] ++ `prob p B <> 0` by METIS_TAC [REAL_LT_LE]
 ++ `(SIGMA (\i. cond_prob p (A i) B) (s:'b -> bool) = 1) =
     (prob p B * SIGMA (\i. cond_prob p (A i) B) s = prob p B * 1)` 
     by METIS_TAC [REAL_EQ_MUL_LCANCEL] ++ POP_ORW
 ++ `prob p B * SIGMA (\i. cond_prob p (A i) B) (s:'b -> bool) = 
        SIGMA (\i. prob p B * cond_prob p (A i) B) s`
        by ((MP_TAC o Q.ISPEC `s:'b -> bool`) REAL_SUM_IMAGE_CMUL ++ RW_TAC std_ss [])
 ++ RW_TAC std_ss [cond_prob_def, REAL_DIV_LMUL, REAL_MUL_RID, EQ_SYM_EQ, INTER_COMM]
 ++ MATCH_MP_TAC PROB_REAL_SUM_IMAGE_FN
 ++ RW_TAC std_ss [INTER_IDEMPOT, EVENTS_INTER]);

val COND_PROB_SWAP = store_thm
  ("COND_PROB_SWAP",
  ``!A B C p. 
        prob_space p /\ A IN events p /\ B IN events p /\ C IN events p ==>
        (cond_prob p A (B INTER C) * cond_prob p B C = 
         cond_prob p B (A INTER C) * cond_prob p A C)``,
    RW_TAC std_ss [] ++ `B INTER C IN events p` by METIS_TAC [EVENTS_INTER]
 ++ `A INTER B IN events p` by METIS_TAC [EVENTS_INTER]
 ++ `A INTER C IN events p` by METIS_TAC [EVENTS_INTER] 
 ++ `A INTER (B INTER C) = B INTER (A INTER C)` by METIS_TAC [INTER_ASSOC, INTER_COMM]
 ++ Cases_on `prob p C = 0`
 >> RW_TAC std_ss [COND_PROB_ZERO, REAL_MUL_RZERO]
 ++ `0 < prob p C` by METIS_TAC [PROB_POSITIVE, REAL_LT_LE]
 ++ Cases_on `prob p (B INTER C) = 0`
 >> (`cond_prob p B C = 0` by RW_TAC std_ss [cond_prob_def, REAL_DIV_LZERO]
    ++ Cases_on `prob p (A INTER C) = 0`
    >> RW_TAC std_ss [COND_PROB_ZERO, REAL_MUL_RZERO, REAL_MUL_LZERO]
    ++ `B INTER (A INTER C) = A INTER (B INTER C)` by METIS_TAC [INTER_ASSOC, INTER_COMM]
    ++ `0 < prob p (A INTER C)` by METIS_TAC [PROB_POSITIVE,  REAL_LT_LE]
    ++ `cond_prob p B (A INTER C) = 0` 
        by RW_TAC std_ss [cond_prob_def, PROB_INTER_ZERO, REAL_DIV_LZERO]
    ++ RW_TAC std_ss [REAL_MUL_LZERO, REAL_MUL_RZERO])
 ++ Cases_on `prob p (A INTER C) = 0`
 >> (RW_TAC std_ss [COND_PROB_ZERO, REAL_MUL_LZERO]  
    ++ `0 < prob p (B INTER C)` by METIS_TAC [PROB_POSITIVE, REAL_LT_LE]
    ++ `prob p (A INTER (B INTER C)) = 0` by METIS_TAC [PROB_INTER_ZERO]
    ++ RW_TAC std_ss [cond_prob_def, REAL_DIV_LZERO, REAL_MUL_LZERO])
 ++ `!(a:real) b c d. a * b * (c * d) = a * (b * c) * d` by METIS_TAC [REAL_MUL_ASSOC]
 ++ RW_TAC std_ss [cond_prob_def, real_div, REAL_MUL_LINV, REAL_MUL_RID]
 ++ METIS_TAC []);
 
val PROB_INTER_SPLIT = store_thm
  ("PROB_INTER_SPLIT",
  ``!A B C p. 
        prob_space p /\ A IN events p /\ B IN events p /\ C IN events p ==>
        (prob p (A INTER B INTER C) = 
         cond_prob p A (B INTER C) * cond_prob p B C * prob p C)``,
    RW_TAC std_ss [] ++ `B INTER C IN events p` by METIS_TAC [EVENTS_INTER]
 ++ `A INTER B IN events p` by METIS_TAC [EVENTS_INTER]
 ++ Cases_on `prob p C = 0`
 >> RW_TAC std_ss [PROB_INTER_ZERO, REAL_MUL_RZERO]
 ++ Cases_on `prob p (B INTER C) = 0`
 >> RW_TAC std_ss [INTER_ASSOC, PROB_INTER_ZERO, COND_PROB_ZERO, REAL_MUL_LZERO]
 ++ `!(a:real) b c d e. a * b * (c * d) * e = a * (b * c) * (d * e)` by METIS_TAC [REAL_MUL_ASSOC]  
 ++ RW_TAC std_ss [cond_prob_def, real_div, REAL_MUL_LINV, REAL_MUL_LID, REAL_MUL_RID, INTER_ASSOC]);



val COND_PROB_INTER_SPLIT = store_thm
  ("COND_PROB_INTER_SPLIT",
  ``!A B C p. 
        prob_space p /\ A IN events p /\ B IN events p /\ C IN events p ==>
        (cond_prob p (A INTER B) C = cond_prob p A (B INTER C) * cond_prob p B C)``,
    RW_TAC std_ss []
 ++ Cases_on `prob p C = 0`
 >> (`A INTER B IN events p` by METIS_TAC [EVENTS_INTER]
    ++ RW_TAC std_ss [COND_PROB_ZERO, REAL_MUL_RZERO])
 ++ Cases_on `prob p (B INTER C) = 0`
 >> (`A INTER B INTER C IN events p` by METIS_TAC [EVENTS_INTER]
    ++ `B INTER C IN events p` by METIS_TAC [EVENTS_INTER]
    ++ `0 < prob p C` by METIS_TAC [PROB_POSITIVE, REAL_LT_LE]
    ++ FULL_SIMP_TAC real_ss [COND_PROB_ZERO, REAL_MUL_LZERO, cond_prob_def, INTER_ASSOC,PROB_INTER_ZERO, REAL_DIV_LZERO])    
 ++ `!(x:real) y z w. x * y * (z * w) = x * (y * z) * w` 
        by METIS_TAC [REAL_MUL_ASSOC, REAL_MUL_COMM]              
 ++ RW_TAC std_ss [cond_prob_def, real_div, GSYM INTER_ASSOC, REAL_MUL_LINV, REAL_MUL_RID, PROB_INTER_ZERO]
 


);
	   




(* ========================================================================= *)
(*                                 Main Script        			     *)
(* ========================================================================= *)



(*
DB.match ["arithmetic"] (Term `inv (x * y)`);
DB.match ["real"] (Term `a + b <= c`);
DB.match ["seq"] (Term `f --> x`);
*)

fun MP_REWRITE_TAC th g =
  let
    val (p,c') = dest_imp (concl (SPEC_ALL th))
    val (l,r) = (dest_eq o snd o strip_forall) c'
    fun add_context ctxt k t =
      (k (mk_conj (ctxt,t)),NONE) handle _ => (k t,SOME ctxt)
    fun common k (t,NONE) = (k t,NONE)
      | common k (t,SOME c) = add_context c k t
    fun mk_opt_conj (NONE,NONE) = NONE
      | mk_opt_conj (SOME x,NONE) = SOME x
      | mk_opt_conj (NONE,SOME x) = SOME x
      | mk_opt_conj (SOME x,SOME y) = SOME(mk_conj(x,y))
    fun new_concl t =
      let val (s,t) = match_term l t in
        add_context (subst s (inst t p)) I (subst s (inst t r))
      end
      handle _ =>
      if is_var t orelse is_const t then (t,NONE) else
        let val (v,b) = dest_abs t in
          common (curry mk_abs v) (new_concl b)
        end
        handle _ =>
        let
          val (t1,t2) = dest_comb t
          val (t1',c1) = new_concl t1
          val (t2',c2) = new_concl t2
        in
          common I (mk_comb(t1',t2'),mk_opt_conj(c1,c2))
        end
     val c = snd g
  in
    MATCH_MP_TAC (METIS_PROVE[th] (mk_imp (fst (new_concl c),c))) g
  end;

fun SET_TAC L =
    POP_ASSUM_LIST(K ALL_TAC) THEN REPEAT COND_CASES_TAC THEN
    REWRITE_TAC (append [EXTENSION, SUBSET_DEF, PSUBSET_DEF, DISJOINT_DEF,
    SING_DEF] L) THEN SIMP_TAC std_ss [NOT_IN_EMPTY, IN_UNIV, IN_UNION,
    IN_INTER, IN_DIFF, IN_INSERT, IN_DELETE, IN_BIGINTER, IN_BIGUNION,
    IN_IMAGE, GSPECIFICATION, IN_DEF] THEN MESON_TAC [];
fun SET_RULE tm = prove(tm,SET_TAC []);

val set_rewrs
= [INTER_EMPTY, INTER_UNIV, UNION_EMPTY, UNION_UNIV, DISJOINT_UNION,
DISJOINT_INSERT, DISJOINT_EMPTY, GSYM DISJOINT_EMPTY_REFL,
DISJOINT_BIGUNION, INTER_SUBSET, INTER_IDEMPOT, UNION_IDEMPOT,
SUBSET_UNION];

val UNIONL_def = Define `(UNIONL [] = {})
/\ (UNIONL (s::ss) = (s:'a->bool) UNION UNIONL ss)`;

fun K_TAC _ = ALL_TAC;

fun KNOW_PROVE_KILL tm L = 
KNOW_TAC tm THEN1 (RW_TAC real_ss L) THEN 
DISCH_TAC THEN ONCE_ASM_REWRITE_TAC [] THEN POP_ASSUM K_TAC;

val Suff = Q_TAC SUFF_TAC;

val POP_ORW = POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm]);
val Know = Q_TAC KNOW_TAC;

(* ========================================================================= *)
(*                                   Sum        			     *)
(* ========================================================================= *)


g `!f g l m. (f --> l) /\ (g --> m) ==> (lim (\x. f x + g x) = l + m)`;
e (RW_TAC std_ss [lim]);
e (SELECT_ELIM_TAC);
e (CONJ_TAC);
  e (EXISTS_TAC (--`l + m:real`--));
  e (MATCH_MP_TAC SEQ_ADD);
  e (RW_TAC std_ss []);
  e (RW_TAC std_ss []);
  e (MATCH_MP_TAC SEQ_UNIQ);
  e (EXISTS_TAC (--`(\x. f x + g x): num -> real`--));
  e (RW_TAC std_ss []);
  e (MATCH_MP_TAC SEQ_ADD);
  e (RW_TAC std_ss []);
val LIM_SEQ_ADD = top_thm();
drop();

g `!f g l m. (f --> l) /\ (g --> m) ==> (lim (\x. f x - g x) = l - m)`;
e (RW_TAC std_ss [lim]);
e (SELECT_ELIM_TAC);
e (CONJ_TAC);
  e (EXISTS_TAC (--`l - m:real`--));
  e (MATCH_MP_TAC SEQ_SUB);
  e (RW_TAC std_ss []);
  
  e (RW_TAC std_ss []);
  e (MATCH_MP_TAC SEQ_UNIQ);
  e (EXISTS_TAC (--`(\x. f x - g x): num -> real`--));
  e (RW_TAC std_ss []);
  e (MATCH_MP_TAC SEQ_SUB);
  e (RW_TAC std_ss []);
val LIM_SEQ_SUB = top_thm();
drop();

g `!f g l m. (f --> l) /\ (g --> m) ==> (lim (\x. f x * g x) = l * m)`;
e (RW_TAC std_ss [lim]);
e (SELECT_ELIM_TAC);
e (CONJ_TAC);
  e (EXISTS_TAC (--`l * m:real`--));
  e (MATCH_MP_TAC SEQ_MUL);
  e (RW_TAC std_ss []);
  
  e (RW_TAC std_ss []);
  e (MATCH_MP_TAC SEQ_UNIQ);
  e (EXISTS_TAC (--`(\x. f x * g x): num -> real`--));
  e (RW_TAC std_ss []);
  e (MATCH_MP_TAC SEQ_MUL);
  e (RW_TAC std_ss []);
val LIM_SEQ_MUL = top_thm();
drop();

g `!f l a. (f --> l) ==> (lim (\x. a * (f x)) = a * l)`;
e (RW_TAC std_ss []);
e (KNOW_TAC (--`(lim (\x. a * (f x))) = (lim (\x. (\x. a) x * (\x. f x) x))`--));
  	    e (RW_TAC std_ss []);
e (DISCH_TAC THEN ONCE_ASM_REWRITE_TAC []);
e (MATCH_MP_TAC LIM_SEQ_MUL);
e (RW_TAC std_ss [SEQ_CONST, ETA_THM]);
val LIM_SEQ_CMUL = top_thm();
drop();

g `!n f. sum (0,SUC (SUC n)) f = f(0) + f(1)+ sum (2,n) f `;
e (Induct_on `n`);
e(RW_TAC real_ss [sum]);
e(RW_TAC real_ss [sum,REAL_ADD_ASSOC,ADD1]);
val SUM_0_SUM_2= top_thm();drop();


g `!n f. (sum (0,SUC n) f = f (0) + sum (1,n) f ) `;
e (Induct_on `n` THEN RW_TAC real_ss [sum,REAL_ADD_ASSOC,ADD1]);
val SUM_0_SUM_1 = top_thm();drop();



g `!n f.  sum (1,n) f  =  - f (0)   + sum (0,SUC n) f  `;
e(RW_TAC real_ss[ SUM_0_SUM_1]);
 e(REAL_ARITH_TAC);
val SUM_0_SUM_1_ALT = top_thm();
drop();


g `!n f.  sum (2,n) f  =  - f (0) - f(1)   + sum (0,SUC (SUC n)) f  `;
e(RW_TAC real_ss[ SUM_0_SUM_2]);
 e(REAL_ARITH_TAC);
val SUM_0_SUM_2_ALT = top_thm();
drop();

g`!(f:num->real) (m:num).((\n. f n)--> p)= ((\n. f (n + m))--> p)`;

e(GEN_TAC);
e(Induct_on `m`);
e(RW_TAC real_ss[]);

e(KNOW_TAC (--`!n. n + SUC m = SUC (n+ m ) `--));
      e(GEN_TAC);
      e(RW_TAC std_ss[ADD1]);
      e(RW_TAC real_ss[]);
e (DISCH_TAC THEN ONCE_ASM_REWRITE_TAC [] THEN POP_ASSUM K_TAC);

e(KNOW_TAC(--`!(f:num->real).  (\n. f (n + m)) --> p =  (\n.(\a. (\n.f ((m + n))) (n) ) a)--> p`--));
      e(RW_TAC real_ss[]);
e (DISCH_TAC THEN ONCE_ASM_REWRITE_TAC [] THEN POP_ASSUM K_TAC);

e(KNOW_TAC(--`  !n (f:num->real). (\n. f (SUC (n + m))) --> p =  
		(\n.(\a. (\n.f ((m + n))) (SUC n) ) a)--> p `--));
      e(RW_TAC real_ss[]);
      e(RW_TAC real_ss[ADD1]);
e (DISCH_TAC THEN ONCE_ASM_REWRITE_TAC [] THEN POP_ASSUM K_TAC);
e(RW_TAC std_ss[GSYM SEQ_SUC]);
val SEQ_SUC_GENERAL= top_thm();
drop();


g` !f. suminf f = lim (\n. sum (0,n) f)`;
e(RW_TAC real_ss[suminf,lim,sums]);

val SUMINF_LIM_THM = top_thm();
drop();

g `!n f. sum (0, n) f = sum (1, n) (\i. f (i-1))`;
e (Induct_on `n` THEN RW_TAC real_ss [sum]);
val SUM_SHIFT= top_thm();drop();


g `!n f. (sum (0,SUC n) f = f (0) + sum (1,n) f ) `;
e (Induct_on `n` THEN RW_TAC real_ss [sum,REAL_ADD_ASSOC,ADD1]);
val SUM_0_SUM_1 = top_thm();drop();


g `!n f. sum (0, n) f = sum (1, n) (\i. f (i-1))`;
e (Induct_on `n` THEN RW_TAC real_ss [sum]);
val SUM_SHIFT= top_thm();drop();

(* ========================================================================= *)
(*                                   Limit       			     *)
(* ========================================================================= *)

g`!f. lim (\n. sum (0,n) f) = lim (\n. sum (0,n + 1) f)`;

e(RW_TAC real_ss[lim]);
e(KNOW_TAC(--`(\n. sum (0,n + 1) f) = 
             (\n. (\n. sum (0,n) f) (n + 1))  `--));
e(RW_TAC real_ss[]);
e(DISCH_TAC THEN ONCE_ASM_REWRITE_TAC[]);
e(REWRITE_TAC[GSYM ADD1]);
e(REWRITE_TAC[GSYM SEQ_SUC]);

val LIM_SUM_SUC = top_thm();
drop();


g`!f. lim (\n. sum (0,n) f) = lim (\n. sum (0,n + 2) f)`;

e(RW_TAC real_ss[lim]);
e(KNOW_TAC(--`(\n. sum (0,n + 2) f) = 
             (\n. (\n. sum (0,n) f) (n + 2))  `--));
e(RW_TAC real_ss[]);
e(DISCH_TAC THEN ONCE_ASM_REWRITE_TAC[]);
e(ONCE_REWRITE_TAC[GSYM SEQ_SUC_GENERAL]);
e(RW_TAC real_ss[]);;


val LIM_SUM_SUC_SUC = top_thm();
drop();


g`n + 2 = SUC ( SUC n )`;
e(RW_TAC real_ss[ADD1]);
val ADD2 = top_thm();
drop();


g`!x.  exp (x:real) = 1 + x  + lim (\n. sum (2,n) (\n. inv (&FACT n) * x pow n))  `;
e(RW_TAC std_ss[exp,SUMINF_LIM_THM]);
e(RW_TAC std_ss[LIM_SUM_SUC_SUC]);
e(REWRITE_TAC[ADD2 ]);
e(RW_TAC std_ss[SUM_0_SUM_2]);
e(RW_TAC real_ss[pow,FACT,REAL_INV1,POW_1]);
e(ONCE_REWRITE_TAC[ONE,FACT]);
e(RW_TAC real_ss[FACT,REAL_INV1]);

e(KNOW_PROVE_KILL (--`1 + x + lim (\n. sum (2,n) (\n. inv (&FACT n) * x pow n)) = 
1 + (x + lim (\n. sum (2,n) (\n. inv (&FACT n) * x pow n)))`--)
[GSYM REAL_ADD_ASSOC]);
e(KNOW_PROVE_KILL 
  (--`(\n. 1 + x + sum (2,n) (\n. inv (&FACT n) * x pow n)) = 
      (\n. (\n. 1) n + 
        (\n. x + sum (2,n) (\n. inv (&FACT n) * x pow n))n)`--) [GSYM REAL_ADD_ASSOC]);;
e(MATCH_MP_TAC LIM_SEQ_ADD);;
e(RW_TAC real_ss[SEQ_CONST]);
e(KNOW_PROVE_KILL (--`(\n. x + sum (2,n) (\n. inv (&FACT n) * x pow n)) = 
                    (\n. (\n. x) n + 
                    (\n. sum (2,n) (\n. inv (&FACT n) * x pow n)) n)`--) 
                    []);

e(MATCH_MP_TAC SEQ_ADD);;
e(RW_TAC real_ss[SEQ_CONST]);
e(RW_TAC std_ss[SUM_0_SUM_2_ALT]);
e(RW_TAC real_ss[pow,FACT,REAL_INV1,POW_1]);
e(ONCE_REWRITE_TAC[ONE,FACT]);
e(RW_TAC real_ss[FACT,REAL_INV1]);
e(RW_TAC std_ss[lim]);
e(SELECT_ELIM_TAC);
e(CONJ_TAC);
r(1);
e(RW_TAC real_ss[]);
e(EXISTS_TAC(--`-(1:real) - (x:real) + exp (x)`--));
e(KNOW_TAC (--` (-1 - (x:real) + exp x) = 
                       (-1 + (- x + exp x)) `--));
e(RW_TAC real_ss[REAL_ADD_ASSOC]);
e(RW_TAC real_ss[GSYM real_sub]);
e(DISCH_TAC THEN ONCE_ASM_REWRITE_TAC[]);
e(KNOW_TAC (--`(\n. -1 - x + sum (0,SUC (SUC n)) (\n. inv (&FACT n) * x pow n)) = 
(\n. (\n. -1) n + (\n. -x + sum (0,SUC (SUC n)) (\n. inv (&FACT n) * x pow n))n)`--) );;
e(RW_TAC std_ss[]);
e(RW_TAC real_ss[REAL_ADD_ASSOC]);
e(RW_TAC real_ss[GSYM real_sub]);
e(DISCH_TAC THEN ONCE_ASM_REWRITE_TAC[]);
e(MATCH_MP_TAC SEQ_ADD);;
e(RW_TAC real_ss[SEQ_CONST]);
e(KNOW_PROVE_KILL (--`(\n. -x + sum (0,SUC (SUC n)) (\n. inv (&FACT n) * x pow n)) = 
(\n. (\n. -x) n + (\n. sum (0,SUC (SUC n)) (\n. inv (&FACT n) * x pow n))n)`--) []);
e(MATCH_MP_TAC SEQ_ADD);;
e(RW_TAC real_ss[SEQ_CONST]);

e(KNOW_PROVE_KILL (--`(\n. sum (0,SUC (SUC n)) (\n. inv (&FACT n) * x pow n)) = 

(\n.(\n. (\n. 
    sum (0,n) (\n. inv (&FACT n) * x pow n)) (SUC n)) (SUC n))`--)
[]);

e(ONCE_REWRITE_TAC[GSYM SEQ_SUC]);
e(ONCE_REWRITE_TAC[GSYM SEQ_SUC]);
e(RW_TAC real_ss[EXP_CONVERGES,GSYM sums,GSYM exp,ETA_AX]);
e(METIS_TAC[EXP_CONVERGES,ETA_AX]);

val EXP_SPLIT_2 = top_thm();
drop();



g`!x.  exp (x:real) = 1 + lim (\n. sum (1,n) (\n. inv (&FACT n) * x pow n))  `;

e(RW_TAC std_ss[exp,SUMINF_LIM_THM]);
e(RW_TAC std_ss[LIM_SUM_SUC]);
e(RW_TAC std_ss[GSYM ADD1]);
e(RW_TAC std_ss[SUM_0_SUM_1]);
e(RW_TAC real_ss[pow,FACT,REAL_INV1]);
e(KNOW_TAC(--`(\n. 1 + sum (1,n) (\n. inv (&FACT n) * x pow n)) = 
        (\n. (\n. 1) n + 
        (\n. sum (1,n) (\n. inv (&FACT n) * x pow n)) n) `--));
e(RW_TAC real_ss[]);
e(DISCH_TAC THEN ONCE_ASM_REWRITE_TAC[]);
e(KNOW_TAC(--`lim (\n. (\n. 1) n + (\n. sum (1,n) (\n. inv (&FACT n) * x pow n)) n) = 
1 + lim (\n.sum (1,n) (\n. inv (&FACT n) * x pow n)) `-- ));
e(MATCH_MP_TAC LIM_SEQ_ADD);
e(CONJ_TAC);
e(RW_TAC real_ss[SEQ_CONST]);
e(RW_TAC std_ss[lim]);
e(SELECT_ELIM_TAC);
e(CONJ_TAC);
r(1);
e(RW_TAC real_ss[]);
e(RW_TAC std_ss[SUM_0_SUM_1_ALT]);
e(RW_TAC real_ss[pow,FACT,REAL_INV1]);
e(EXISTS_TAC(--`-(1:real) + exp x`--));
e(KNOW_TAC(--`(\n. -1 + sum (0,SUC n) (\n. inv (&FACT n) * x pow n)) = 
              (\n. (\n. -1) n  + (\n. sum (0,SUC n) (\n. inv (&FACT n) * x pow n)) n)`--));
e(RW_TAC real_ss[]);
e(DISCH_TAC THEN ONCE_ASM_REWRITE_TAC[]);
e(MATCH_MP_TAC SEQ_ADD);
e(RW_TAC real_ss[SEQ_CONST]);
e(KNOW_TAC(--`(\n. sum (0,SUC n) (\n. inv (&FACT n) * x pow n)) =
             (\n.(\n.  sum (0,n) (\n. inv (&FACT n) * x pow n)) (SUC n))  `--));
e(RW_TAC real_ss[]);
e(DISCH_TAC THEN ONCE_ASM_REWRITE_TAC[]);
e(REWRITE_TAC[GSYM SEQ_SUC]);
e(RW_TAC real_ss[EXP_CONVERGES,GSYM sums,GSYM exp,ETA_AX]);
e(METIS_TAC[EXP_CONVERGES,ETA_AX]);
e(DISCH_TAC);
e(ASM_REWRITE_TAC[]);

val EXP_SPLIT = top_thm();
drop();


(* ========================================================================= *)
(*            Binomial Coefficient 			     		     *)
(* ========================================================================= *)


g `!n f. sum (0, n) f = sum (1, n) (\i. f (i-1))`;
e (Induct_on `n` THEN RW_TAC real_ss [sum]);
val SUM_SHIFT= top_thm();drop();


g `!n f. (sum (0,SUC n) f = f (0) + sum (1,n) f ) `;
e (Induct_on `n` THEN RW_TAC real_ss [sum,REAL_ADD_ASSOC,ADD1]);
val SUM_0_SUM_1 = top_thm();drop();


g `!n f. sum (0, n) f = sum (1, n) (\i. f (i-1))`;
e (Induct_on `n` THEN RW_TAC real_ss [sum]);
val SUM_SHIFT= top_thm();drop();


val binomial_def= 
Define `(binomial n 0 = (1:num)) /\
        (binomial 0 (SUC k) = (0:num)) /\
        (binomial (SUC n) (SUC k) = binomial n (SUC k) + binomial n k)`;


g`!n. binomial n  0 = 1`;
e(Cases_on `n` THEN REWRITE_TAC [binomial_def]); 
val BINOMIAL_DEF1 = top_thm(); drop();


g`!n k. n < k ==> (binomial n k = 0)`;
e(Induct_on `n`); 
e(Cases_on `k`);
e(RW_TAC real_ss []);
e(REWRITE_TAC [binomial_def]);
e(Cases_on `k`);
e(RW_TAC real_ss []);
e(RW_TAC arith_ss [binomial_def]);
val BINOMIAL_DEF2 = top_thm(); drop();


g`!n. (binomial n n = 1)`;
e(Induct_on `n` THEN REWRITE_TAC [binomial_def] THEN RW_TAC arith_ss [BINOMIAL_DEF2]);
val BINOMIAL_DEF3 = top_thm(); drop();


g`!n k. (binomial (SUC n) (SUC k) = binomial n (SUC k) + binomial n k)`;
e(REWRITE_TAC [binomial_def]); 
val BINOMIAL_DEF4 = top_thm(); drop();


g `!a b. binomial (a+b) b * (FACT a * FACT b) = FACT (a+b)`;
e(Induct_on `b`);
e(REWRITE_TAC[BINOMIAL_DEF1,FACT,ADD_CLAUSES,MULT_CLAUSES]);
e(Induct_on `a`);
e(REWRITE_TAC[BINOMIAL_DEF3,FACT,ADD_CLAUSES,MULT_CLAUSES]);
e( `SUC a + SUC b = SUC (SUC a + b)` by RW_TAC arith_ss [ADD_CLAUSES]);
e(ASM_REWRITE_TAC[BINOMIAL_DEF4,RIGHT_ADD_DISTRIB]);
e(POP_ORW);
e( `binomial (SUC a + b) (SUC b) * (FACT (SUC a) * FACT (SUC b)) =
                   (binomial (a + SUC b) (SUC b) * (FACT a * FACT (SUC b))) * SUC a` 
by REWRITE_TAC[FACT,ADD_CLAUSES]);
e(PROVE_TAC[MULT_ASSOC,MULT_SYM]);
e(ASM_REWRITE_TAC[]);
e(POP_ORW);
e(`binomial (SUC a + b) b * (FACT (SUC a) * FACT (SUC b)) =
                       (binomial (SUC a + b) b * (FACT (SUC a) * FACT b)) * SUC b`
by REWRITE_TAC[FACT,ADD_CLAUSES]);
e(PROVE_TAC[MULT_ASSOC,MULT_SYM]);
e(ASM_REWRITE_TAC [ADD_CLAUSES, FACT]);
e(REWRITE_TAC[GSYM LEFT_ADD_DISTRIB]);
e( `SUC a + SUC b = SUC (SUC (a + b))` by RW_TAC arith_ss [ADD_CLAUSES]);
e(ASM_REWRITE_TAC[]);
e(RW_TAC arith_ss []);
val BINOMIAL_FACT= top_thm(); drop();


g`!n. (binomial (SUC n) 1 = SUC n)`;
e(RW_TAC std_ss []);
e(ONCE_REWRITE_TAC[ONE]);
e((MP_TAC o Q.SPECL [`n`,`SUC 0`]) BINOMIAL_FACT);
e(ONCE_REWRITE_TAC[FACT]);
e(ONCE_REWRITE_TAC[GSYM ONE]);
e(ONCE_REWRITE_TAC[ADD_COMM]);
e(ONCE_REWRITE_TAC[GSYM SUC_ONE_ADD]);
e(ONCE_REWRITE_TAC[FACT]);
e(STRIP_TAC);
e(FULL_SIMP_TAC real_ss [EQ_MULT_LCANCEL]);
e(METIS_TAC [FACT_LESS, NOT_ZERO_LT_ZERO]);
val BINOMIAL_DEF6 = top_thm(); drop();


g `!(a:real) (b:real) n. 
((a + b) pow n = SIGMA (\x. &(binomial n x) * a pow (n - x) * b pow x) (count (SUC n)))`;
e (Induct_on `n`);
e(RW_TAC real_ss [pow, BINOMIAL_DEF3]);
e(`count 1 = 0 INSERT {}` by RW_TAC real_ss [EXTENSION, IN_COUNT, IN_INSERT, IN_SING]);




e(POP_ORW);

e(RW_TAC real_ss [REAL_SUM_IMAGE_SING,BINOMIAL_DEF1]);
e(ONCE_REWRITE_TAC [pow]);
e(POP_ORW);
e(RW_TAC real_ss []);
e(ONCE_REWRITE_TAC [REAL_ADD_RDISTRIB]);
e(`FINITE (count (SUC n))` by METIS_TAC [COUNT_SUC, FINITE_INSERT,FINITE_COUNT]);
e (RW_TAC real_ss [GSYM REAL_SUM_IMAGE_CMUL]);
e(RW_TAC real_ss [REAL_SUM_IMAGE_COUNT]);
e(Know ` sum (0,SUC n) (\x. a* (&binomial n x * a pow (n  - x) * b pow x)) =
a pow (n+1)+ sum (1, SUC n) (\x. a*(&binomial n x * a pow (n - x) * b pow x)) `);
e(RW_TAC real_ss [SUM_0_SUM_1, BINOMIAL_DEF1,sum, BINOMIAL_DEF2,GSYM pow,ADD1]);
e (RW_TAC real_ss []);
e(POP_ORW);
e(Know ` sum (0,SUC n) (\x. b* (&binomial n x * a pow (n - x) * b pow x)) =
sum (0, n) (\x. b*(&binomial n x * a pow (n - x) * b pow x)) + b pow (n+1) `);
e (RW_TAC real_ss [sum, BINOMIAL_DEF3,GSYM pow,ADD1]);
e (RW_TAC real_ss []);
e(POP_ORW);
e (RW_TAC real_ss [GSYM ADD1,pow]);
e (RW_TAC real_ss [SUM_SHIFT]);
e (RW_TAC real_ss [REAL_ADD_ASSOC]);
e(Know ` sum (1,SUC n) (\x. a * (&binomial n x * a pow (n - x) * b pow x))=
sum (1, n) (\x. &binomial n x * a pow (n - x + 1) * b pow x)`);
e (RW_TAC real_ss [sum, BINOMIAL_DEF2]);
e(MATCH_MP_TAC SUM_EQ);
e (RW_TAC real_ss []);
e (RW_TAC real_ss [REAL_MUL_ASSOC]);
e(Know ` a * &binomial n r * a pow (n - r)= &binomial n r * a pow (n + 1 - r)`);
e(ONCE_REWRITE_TAC [REAL_MUL_COMM]);
e (RW_TAC real_ss [REAL_MUL_ASSOC]);
e(Know ` a pow (n - r) * a= a pow (n + 1 - r) `);
e(ONCE_REWRITE_TAC [REAL_MUL_COMM]);
e (RW_TAC real_ss [GSYM pow]);
e (RW_TAC real_ss [ADD1]);
e(RW_TAC real_ss []);
e(RW_TAC real_ss []);
e(RW_TAC real_ss []);
e(POP_ORW);
e(ONCE_REWRITE_TAC [REAL_ADD_COMM]);
e(Know ` sum (1,n) (\i. b * (&binomial n (i - 1) * a pow (n - (i - 1)) * b pow (i - 1)))=
sum (1,n) (\i. &binomial n (i - 1) * a pow (n - i + 1) * b pow i) `);
e(MATCH_MP_TAC SUM_EQ);
e (RW_TAC real_ss [REAL_MUL_ASSOC]);
e(ONCE_REWRITE_TAC [REAL_MUL_COMM]);
e(RW_TAC real_ss [REAL_MUL_ASSOC]);
e(Suff ` b pow (r - 1) * b= b pow r `);
e (RW_TAC real_ss []);
e(`r=SUC (r - 1)` by RW_TAC real_ss []);
e(ONCE_ASM_REWRITE_TAC []);
e(RW_TAC real_ss [pow, ADD, REAL_MUL_COMM]);
e(RW_TAC real_ss []);
e(POP_ORW);
e(Know ` sum (1,n) (\x. &binomial n x * a pow (n - x + 1) * b pow x) +
    sum (1,n) (\i. &binomial n (i - 1) * a pow (n - i + 1) * b pow i)=
sum (1,n) (\i. &binomial (SUC n) (SUC (i-1)) * a pow (n - i + 1) * b pow i)`);
e (RW_TAC real_ss [GSYM SUM_ADD]);
e(MATCH_MP_TAC SUM_EQ);
e (RW_TAC real_ss [BINOMIAL_DEF4]);
e(ONCE_REWRITE_TAC [GSYM REAL_MUL_ASSOC]);
e (RW_TAC real_ss [GSYM REAL_ADD_RDISTRIB,ADD1]);
e (RW_TAC real_ss []);
e (RW_TAC real_ss [GSYM pow]);
e(Know ` b pow (SUC n) +
    (a pow (SUC n) +
     sum (1,n) (\x. &binomial n x * a pow (n - x + 1) * b pow x)) +
    sum (1,n) (\i. &binomial n (i - 1) * a pow (n - i + 1) * b pow i)= 
b pow (SUC n)+ a pow (SUC n) +
     sum (1,n) (\i. &binomial (SUC n) (SUC (i - 1)) * a pow (n - i + 1) * b pow i)`);
e (RW_TAC real_ss []);
e(ONCE_REWRITE_TAC [GSYM REAL_ADD_ASSOC]);
e(RW_TAC real_ss [REAL_EQ_LADD]);
e(ONCE_REWRITE_TAC [GSYM REAL_ADD_ASSOC]);
e(RW_TAC real_ss [REAL_EQ_LADD]);
e (RW_TAC real_ss []);
e(POP_ORW);
e(`sum (1,SUC (SUC n))
      (\i. (\i. &binomial (SUC n) i * a pow (SUC n - i) *  b pow i) (i-1))=
sum (0,SUC (SUC n))
      (\i. &binomial (SUC n) i * a pow (SUC n - i) *  b pow i)` by RW_TAC real_ss [GSYM SUM_SHIFT]);
e (FULL_SIMP_TAC real_ss []);
e(POP_ORW);
e(ONCE_REWRITE_TAC [sum]);
e(ONCE_REWRITE_TAC [SUM_0_SUM_1]);
e (RW_TAC real_ss [pow,BINOMIAL_DEF1, BINOMIAL_DEF3]);
e(ONCE_REWRITE_TAC [GSYM pow]);
e(ONCE_REWRITE_TAC [ADD1]);
e(ONCE_REWRITE_TAC [GSYM REAL_ADD_ASSOC]);
e(`a pow (n + 1) +
    (sum (1,n) (\i. &binomial (n + 1) i * a pow (n + 1 - i) * b pow i) +
     b pow (n + 1))= b pow (n + 1) +
    (a pow (n + 1) +
    sum (1,n) (\i. &binomial (n + 1) i * a pow (n + 1 - i) * b pow i))` by REAL_ARITH_TAC);
e(POP_ORW);
e(RW_TAC real_ss [REAL_EQ_LADD]);
e(MATCH_MP_TAC SUM_EQ);
e(RW_TAC real_ss [ADD1]);
val EXP_PASCAL_REAL = top_thm();drop(); 

(* ========================================================================= *)
(*                           Binomial Coefficient 	         	     *)
(* ========================================================================= *)



g`!(a:real) (b:real) n. (a + b) pow n = a pow n + sum (1,n) (\x. &binomial n x * a pow (n - x) * b pow x)`;
e(RW_TAC real_ss [EXP_PASCAL_REAL]);
e(RW_TAC real_ss [REAL_SUM_IMAGE_COUNT]);
e(RW_TAC real_ss [SUM_0_SUM_1 ]);
e(RW_TAC real_ss [BINOMIAL_DEF1]);
val BINOMIAL_DEFN = top_thm(); drop();


g` !(a:real) b c d e. (a + b)*(c + d + e) = a*c + a*d + ( a*e + b*d + b*c + b*e)`;

e(REAL_ARITH_TAC);
val ADD_TWO_MUL_ADD_THREE  = top_thm();
drop(); 



g`! (a: real) b c d. a * b * c * d = b * a * c *d`;
e(REAL_ARITH_TAC);
val MUL_L1 = top_thm();drop();



g`! a b c. ~(b = &0) ==>
                ((a:real) + b + c = b*(a/b + 1 + c/b))`;;

e(REPEAT GEN_TAC);;
e(RW_TAC real_ss[REAL_ADD_LDISTRIB]);;
e(RW_TAC real_ss[real_div]);;
e(ONCE_REWRITE_TAC[REAL_MUL_SYM]);;
e(RW_TAC real_ss[GSYM REAL_MUL_ASSOC,REAL_MUL_LINV]);;

val COMMON_OF_ADD_3 = top_thm();drop();



g`! a b c. ~(a = &0) ==>
                ((a:real) + b  = a*(1 + b/a))`;;

e(REPEAT GEN_TAC);;
e(RW_TAC real_ss[REAL_ADD_LDISTRIB]);;
e(RW_TAC real_ss[real_div]);;
e(ONCE_REWRITE_TAC[REAL_MUL_SYM]);;
e(RW_TAC real_ss[GSYM REAL_MUL_ASSOC,REAL_MUL_LINV]);;

val COMMON_OF_ADD_2 = top_thm();drop();



g`!(a:real) (b:real) (c:real) (d:real). 
   ~(a = &0) /\ ~(b = &0) /\ ~(c = &0) /\ ~(d = &0)  ==> ~(a*b*c*d = &0)`;;
e(RW_TAC real_ss[REAL_ENTIRE]);
val REAL_MUL4_NZ = top_thm();drop();


g`!(a:real) (b:real) (c:real). 
   ~(a = &0) /\ ~(b = &0) /\ ~(c = &0) ==> ~(a*b*c = &0)`;;
e(RW_TAC real_ss[REAL_ENTIRE]);
val REAL_MUL3_NZ = top_thm();drop();


g`!(a:real) (b:real) . 
   ~(a = &0) /\ ~(b = &0)  ==> ~(a*b = &0)`;;
e(RW_TAC real_ss[REAL_ENTIRE]);
val REAL_MUL2_NZ = top_thm();drop();


g` (?g. a /\ f g) = ( a /\ ?g. f g)`;
e(METIS_TAC[]);
val EXIST_OVER_AND = top_thm();drop();

(* ========================================================================= *)
(*                                  Lemmas               		     *)
(* ========================================================================= *)

g`!X (a:real) (c:real). (real_random_variable X p) /\ (prob_space p) ==>
(real_random_variable ((\x. Normal a*(X x) + (Normal c))) p ) `;

e(REPEAT STRIP_TAC);
e(REWRITE_TAC [real_random_variable_def]);
e(CONJ_TAC THEN FULL_SIMP_TAC std_ss [real_random_variable_def]);
e(RW_TAC std_ss []); 
e(RW_TAC real_ss [GSYM extreal_distinct, mul_not_infty2, add_not_infty]); 
e(RW_TAC real_ss [GSYM extreal_distinct, mul_not_infty2, add_not_infty]); 
e(MATCH_MP_TAC IN_MEASURABLE_BOREL_ADD);
e(Q.EXISTS_TAC `(\x. Normal a * X x)`);
e(Q.EXISTS_TAC `(\x. Normal c )`);
e(RW_TAC std_ss [EVENTS_SIGMA_ALGEBRA]); 
e(MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL);
e(Q.EXISTS_TAC `X`);
e(Q.EXISTS_TAC `a`);
e(FULL_SIMP_TAC std_ss [EVENTS_SIGMA_ALGEBRA]); 
e(MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST);
e(Q.EXISTS_TAC `Normal c`);
e(FULL_SIMP_TAC std_ss [EVENTS_SIGMA_ALGEBRA]); 

val RV_X_ADD_CONST_P = top_thm(); drop();


g ` (X x  <> PosInf)  /\  (X x  <> NegInf)  ==> Normal a * X x pow 2 <> PosInf`;

e((MP_TAC o Q.SPECL [`Normal a`,`X x pow 2`]) mul_not_infty2);
e(RW_TAC std_ss[]);
e((MP_TAC o Q.SPECL [`2`,`X x`]) pow_not_infty);
e(RW_TAC std_ss[]);

val APOW_2_PosInf = top_thm(); drop();


g ` (X x  <> PosInf)  /\  (X x  <> NegInf)  ==> Normal a * X x pow 2 <> NegInf`;

e((MP_TAC o Q.SPECL [`Normal a`,`X x pow 2`]) mul_not_infty2);
e(RW_TAC std_ss[]);
e((MP_TAC o Q.SPECL [`2`,`X x`]) pow_not_infty);
e(RW_TAC std_ss[]);

val APOW_2_NegInf = top_thm(); drop();



g `!X pr (a:real).  (real_random_variable X p) /\ (prob_space p) ==> real_random_variable (\x. (Normal a) * X x pow 2) p `;

e(RW_TAC std_ss [real_random_variable_def,APOW_2_PosInf,APOW_2_NegInf]);
e((MP_TAC o Q.SPECL [`(p_space p,events p)`,`(\x. X x pow 2)`,`(\x. Normal a * X x pow 2)`,`a`]) IN_MEASURABLE_BOREL_CMUL);
e(RW_TAC std_ss[]);
e((MP_TAC o Q.SPECL [`(p_space p,events p)`,`(\x. X x)`,`(\x. X x pow 2)`]) IN_MEASURABLE_BOREL_SQR);
e(RW_TAC std_ss[]);
e(KNOW_TAC(--`(\x. X x) IN measurable (p_space p,events p) Borel`--));;
e(RW_TAC real_ss[ETA_THM]);
e(DISCH_TAC THEN ASM_REWRITE_TAC[]);
e(FULL_SIMP_TAC std_ss [EVENTS_SIGMA_ALGEBRA]);

val APOW_2_RRV_P = top_thm(); drop();

g `!p (c:real). (prob_space p) ==> (expectation p (\x. Normal c) = Normal c)`;

e(RW_TAC std_ss [expectation_def, prob_space_def]);
e((MP_TAC o Q.SPECL [`p`,`(\x. Normal c)`]) integral_mspace);
e(RW_TAC std_ss []);
e(`(m_space p IN measurable_sets p)` by FULL_SIMP_TAC real_ss [MEASURE_SPACE_MSPACE_MEASURABLE,prob_space_def]);
e(FULL_SIMP_TAC real_ss [integral_cmul_indicator,GSYM prob_def,PROB_UNIV,GSYM prob_space_def,GSYM p_space_def]);

val EXPEC_RV_CONST = top_thm();drop();





g ` Normal 2 = 2 `;
e(EVAL_TAC);
val Normal_2 = top_thm(); drop();

g `Normal pr pow 2 = Normal( pr pow 2) `;
e(EVAL_TAC);
val N_POW = top_thm(); drop();

g` !x. Normal 1 * x = x `;
e(Cases);;
e(RW_TAC real_ss[extreal_mul_def]);
e(RW_TAC real_ss[extreal_mul_def]);
e(RW_TAC real_ss[extreal_mul_def]);
val normal_lone = top_thm();drop();


(* ========================================================================= *)
(*                                  Definitions          		     *)
(* ========================================================================= *)

val indep_rv_def = Define `indep_rv p X Y s g A B= 
 (A IN subsets s) /\ (B IN subsets g)
    ==> indep p (PREIMAGE X A INTER p_space p) (PREIMAGE Y B INTER p_space p)`;

val Poisson_distr_rv_def = 
Define `Poisson_distr_rv X p (t:real) R n  = 
     (real_random_variable X p)  /\  
     ( &n IN (IMAGE X (p_space p)))
  /\ (distribution p X {&n} =  (((R * t) pow n) * (exp (- R * t) )) /((&FACT n):real) ) /\ (IMAGE X (p_space p ) SUBSET (GSPEC \(d:num). &d, d IN univ(num)))`;



val is_poisson_process = Define ` is_poisson_process X p t R h n m = ( ?g1 g2 g3. 
    cond_prob p (PREIMAGE (\t.X ((t:real) + h)) {&n + &m} INTER p_space p) 
    (PREIMAGE (\t. X t) {&n} INTER p_space p) =  
    if (m = 0) 
       then ((((R * t) pow n) * 
      (exp (- R * t)) / ((&FACT n):real)) * (1 - R * h + g1 h))
    else if (m = 1) then
       	   ( (((R * t) pow n) * 
      (exp (- R * t)) / ((&FACT n):real)) * (R  * h + g2 h) )
    else  ( (((R * t) pow n) * 
      (exp (- R * t)) / ((&FACT n):real)) * (g3 h)))`;



val marcov_property = Define ` marcov_property X p i j n h =
(real_random_variable  X p) /\ ((prob p (BIGINTER (IMAGE 
(\k. PREIMAGE (\t. X t) {&k} INTER p_space p) (count n))) <> 0) ==> 
((cond_prob p  (PREIMAGE (\t. X (t+h)) {&j} INTER p_space p) 
(PREIMAGE
(\t. X t) {&i} INTER p_space p INTER BIGINTER 
(IMAGE (\k. PREIMAGE
(\u. X u) {&k} INTER p_space p) (count i)))) = (cond_prob p  (PREIMAGE
(\t. X (t+h)) {&j} INTER p_space p)(PREIMAGE (\t. X t) {&i} INTER
p_space p))))`;


val CTMC_trans_def = Define ` 
CTMC_trans_def  (X :real -> extreal) p t R h i j n = ( ?g1 g2.
    cond_prob p (PREIMAGE (\t. X ((t:real) + h)) {&j} INTER p_space p) 
    (PREIMAGE (\t. X t) {&i} INTER p_space p) =  
    if (i <> j) 
       then (R i j * h + g1 h)
    else (1 -  (SIGMA (\j. R i j) (count n)) * h + g2 h))`;


val dist_fun = Define ` dist_fun X p t U h n m = ( ?g1 g2 g3. 
    cond_prob p (PREIMAGE (\t.X ((t:real) + h)) {((&n)) + &m} INTER p_space p) 
    (PREIMAGE (\t. X t) {&n} INTER p_space p) =  
    if (&m = 0) 
       then ((((U * t) pow n) * 
      (exp (- U * t)) / ((&FACT n):real)) * (1 - U * h + g1 h))
    else if (&m = (-1)) then
       	   ( (((U * t) pow n) * 
      (exp (- U * t)) / ((&FACT n):real)) * (U  * h + g2 h) )
    else  ( (((U * t) pow n) * 
      (exp (- U * t)) / ((&FACT n):real)) * (g3 h)))`;



val CTMC_def = Define ` CTMC_def X p t n i j FUN IFUN R h s =
  marcov_property X p i j n h  /\ 
 (!x. x IN space s ==> {x} IN subsets s)  /\
 (!i. i IN space s ==> (IFUN i = distribution p (\t. X (0:real)) {i})) /\
 (FUN t h i j =  CTMC_trans_def X p t R h i j n) `;


val CTMCTH_def = Define ` CTMCTH_def X p t n i j FUN IFUN R h s =
   CTMC_def X p t n i j FUN IFUN R h s /\
 (CTMC_trans_def X p t R h i j n =  CTMC_trans_def X p 0 R h i j n) `;


val BD_trans_def = Define ` 
BD_trans_def  (X :real -> extreal) p t R h i j n = 
    if (j = i+1) 
       then CTMC_trans_def X p t R  h i (i+1) n
    else  if (j = i-1)
       then CTMC_trans_def X p t R  h i (i-1) n
    else  CTMC_trans_def X p t R  h i i n`;

val BDP_def = Define `BDP_def X p t n i j FUN IFUN R h s =
   CTMCTH_def X p t n i j FUN IFUN R h s /\
 BD_trans_def X p t R h i j n `;



val MM1_trans_def = Define ` 
MM1_trans_def  (X :real -> extreal) p t R h (i:num) j n = 
    if (j = i+1) 
       then is_poisson_process X p t R h (i+1) i
    else  if (j = i-1)
       then BD_trans_def X p t R h 1 i n
    else  BD_trans_def X p t R h i j n`;



(* ========================================================================= *)
(*                                  Properties          		     *)
(* ========================================================================= *)


g` !n s p (t:real) h X. {&n} IN subsets s /\  indep_rv p (\t. X (t + h)) (\(t:real). X t) s s {&n} {&n} 
 ==> (prob p ((PREIMAGE (\t. X (t + h)) {&n} INTER p_space p) INTER
       (PREIMAGE (\t. X t) {&n} INTER p_space p)) =
 (prob p (PREIMAGE (\t. X (t + h)) {&n} INTER p_space p)
 * prob p (PREIMAGE (\t. X t) {&n} INTER p_space p))) `;

e(RW_TAC std_ss[]);
e(MATCH_MP_TAC PROB_INDEP);
e(REPEAT STRIP_TAC);
e(FULL_SIMP_TAC std_ss [indep_rv_def]);
e(RW_TAC std_ss[]);

val INDEP_LEMMA = top_thm();
drop();


g` !n s p (t:real) h X. {&n} IN subsets s /\ {&n + &m} IN subsets s /\  
indep_rv p (\t. X (t + h)) (\t. X t) s s {&n + &m} {&n} 
 ==> (prob p ((PREIMAGE (\(t:real). X (t + h)) {&n + &m} INTER p_space p) INTER
       (PREIMAGE (\t. X t) {&n} INTER p_space p)) =
 (prob p (PREIMAGE (\t. X (t + h)) {&n + &m} INTER p_space p)
 * prob p (PREIMAGE (\t. X t) {&n} INTER p_space p))) `;

e(RW_TAC std_ss[]);
e(MATCH_MP_TAC PROB_INDEP);
e(REPEAT STRIP_TAC);
e(FULL_SIMP_TAC std_ss [indep_rv_def]);
e(RW_TAC std_ss[]);

val INDEP_LEMMA2 = top_thm();
drop();






g`&(n + 1) = &n + 1`;
e(EVAL_TAC);
e(RW_TAC std_ss[GSYM add_ints]);
val LEMMA1 = top_thm();
drop();


g`&(n + m) = &n + &m`;
e(EVAL_TAC);
e(RW_TAC std_ss[GSYM add_ints]);
val LEMMA2 = top_thm();
drop();




g`!X p t h h n m  (R:real) s. (!i. {&n + i} IN subsets s)  /\
(!n m. indep_rv p (\t. X (t + h)) (\t. X t) s s {&m} {&n}) /\
prob p (PREIMAGE (\t. X t) {&n} INTER p_space p) <> 0 /\
(&n IN IMAGE (\t. X (t + h)) (p_space p)) /\
(R > (0:real)) /\ (t > (0:real)) /\ 
   (h > 0)
/\ (!k n. Poisson_distr_rv (\t.X (t + k)) p (t + k) R n)
    ==> 
  is_poisson_proces X p t R h n m`;

e(RW_TAC std_ss[ Poisson_distr_rv_def,is_poisson_proces]);


e (POP_ASSUM (MP_TAC o Q.SPEC `h:real`));
e(RW_TAC real_ss[ETA_THM]);
e(UNDISCH_TAC(-- ` !h.
            real_random_variable (\t. X (t + h)) p /\
            &(n + 1) IN IMAGE (\t. X (t + h)) (p_space p) /\
            (distribution p (\t. X (t + h)) {&(n + 1)} =
             (R * (t + h)) pow (n + 1) * exp (-R * (t + h)) / &FACT (n + 1)) /\
         IMAGE (\t. X (t + h)) (p_space p) SUBSET {&d | d IN univ(:num)} `--));

e (DISCH_TAC);
e (POP_ASSUM (MP_TAC o Q.SPEC `h:real`));
e(RW_TAC real_ss[ETA_THM]);


e(UNDISCH_TAC(-- ` !h.
             real_random_variable (\t. X (t + h)) p /\
             &n IN IMAGE (\t. X (t + h)) (p_space p) /\
             (distribution p (\t. X (t + h)) {&n} =
              (R * (t + h)) pow n * exp (-R * (t + h)) / &FACT n) /\
         IMAGE (\t. X (t + h)) (p_space p) SUBSET {&d | d IN univ(:num)} `--));

e (DISCH_TAC);
e (POP_ASSUM (MP_TAC o Q.SPEC `h:real`));
e(RW_TAC real_ss[ETA_THM]);

e(RW_TAC std_ss[is_poisson_process]);


e(Cases_on `m=(0:num)`);
e(RW_TAC real_ss[]);


e(RW_TAC real_ss[cond_prob_def,add_rzero]);    
e(MP_REWRITE_TAC INDEP_LEMMA);
e(RW_TAC std_ss[]);
e(KNOW_TAC (--`!x y. (x:real) * y / y = x * (y/y)`--));
e(RW_TAC real_ss[real_div, REAL_MUL_ASSOC]);
e (DISCH_TAC THEN ONCE_ASM_REWRITE_TAC []);
e(MP_REWRITE_TAC REAL_DIV_REFL);
e(RW_TAC real_ss[]);
e(FULL_SIMP_TAC real_ss[ Poisson_distr_rv_def,distribution_def]);
e(KNOW_TAC (--`!x y z. (x:real) / y * z = (x * z) / y `--));
e(RW_TAC real_ss[real_div]);
e(REAL_ARITH_TAC);
e (DISCH_TAC THEN ONCE_ASM_REWRITE_TAC []);
e(MP_REWRITE_TAC REAL_EQ_RDIV_EQ);
e(`0 < ((&FACT n):real)` by RW_TAC real_ss[FACT_LESS] );
e(FULL_SIMP_TAC std_ss []);
e(MP_REWRITE_TAC REAL_DIV_REFL);
e(`((&FACT n):real) <> 0 ` by METIS_TAC [REAL_FACT_NZ]);
e(FULL_SIMP_TAC std_ss []);
e(RW_TAC real_ss[REAL_MUL_RID]);
e(RW_TAC real_ss[POW_MUL]);
e(` exp (-((R:real) * (t + h))) =  exp (-(R * t + R * h)) ` by METIS_TAC[REAL_ADD_LDISTRIB]);
e(ASM_REWRITE_TAC[]);
e(RW_TAC std_ss[REAL_NEG_ADD]);
e(RW_TAC std_ss[EXP_ADD]);
e(REWRITE_TAC[GSYM REAL_MUL_ASSOC]);
e(MP_REWRITE_TAC (GSYM REAL_EQ_LMUL2));
e(KNOW_TAC (--`(0 :real) <> (R :real) pow n`--));
e(RW_TAC real_ss[REAL_ARITH `` (0 <> (a:real)) = (a <> 0)``]);
e(MATCH_MP_TAC POW_NZ);
e(MATCH_MP_TAC REAL_POS_NZ);
e(RW_TAC real_ss[REAL_ARITH `` (0 < (a:real)) = (a > 0) ``]);
e(FULL_SIMP_TAC std_ss []);
e (DISCH_TAC THEN ONCE_ASM_REWRITE_TAC []);
e(KNOW_TAC(--`!(x:real) y z t w k. (x * (y * z) = t * (w * k)) =
                            (y * (x * z) = w * (t * k))`--));
e(REPEAT GEN_TAC);
e(REAL_ARITH_TAC);
e (DISCH_TAC THEN ONCE_ASM_REWRITE_TAC [] THEN POP_ASSUM K_TAC);
e(MP_REWRITE_TAC (GSYM REAL_EQ_LMUL2));
e(RW_TAC real_ss[EXP_POS_LT, REAL_POS_NZ]);
e(KNOW_TAC(--`!(a:real) b c k. a*(1 - b*c + k) = a - a*b*c + a*k`--));
e(REPEAT GEN_TAC);
e(REAL_ARITH_TAC);
e (DISCH_TAC THEN ONCE_ASM_REWRITE_TAC [] THEN POP_ASSUM K_TAC);
e(RW_TAC real_ss[EXP_SPLIT_2,BINOMIAL_DEFN]);
e(RW_TAC real_ss[ADD_TWO_MUL_ADD_THREE]);
e(RW_TAC real_ss[GSYM real_sub,REAL_MUL_ASSOC]);

e(EXISTS_TAC(--`(\h. (t pow n * lim (\n. sum (2,n) (\n. inv (&FACT n) * -((R:real) * h) pow n)) -
     sum (1,n) (\x. &binomial n x * t pow (n - x) * h pow x) * R * h +
     sum (1,n) (\x. &binomial n x * t pow (n - x) * h pow x) +
     sum (1,n) (\x. &binomial n x * t pow (n - x) * h pow x) *
     lim (\n. sum (2,n) (\n. inv (&FACT n) * -(R * h) pow n)))*
      inv (t pow n))`--));
e(RW_TAC real_ss[]);
e(RW_TAC real_ss[REAL_MUL_ASSOC]);
e(KNOW_TAC(--`! (t:real) (n:num) (h:real) R.   t pow n *
    (t pow n * lim (\n. sum (2,n) (\n. inv (&FACT n) * -(R * h) pow n)) -
     sum (1,n) (\x. &binomial n x * t pow (n - x) * h pow x) * R * h +
     sum (1,n) (\x. &binomial n x * t pow (n - x) * h pow x) +
     sum (1,n) (\x. &binomial n x * t pow (n - x) * h pow x) *
     lim (\n. sum (2,n) (\n. inv (&FACT n) * -(R * h) pow n))) *
    inv (t pow n) = 
    (t pow n * lim (\n. sum (2,n) (\n. inv (&FACT n) * -(R * h) pow n)) -
     sum (1,n) (\x. &binomial n x * t pow (n - x) * h pow x) * R * h +
     sum (1,n) (\x. &binomial n x * t pow (n - x) * h pow x) +
     sum (1,n) (\x. &binomial n x * t pow (n - x) * h pow x) *
     lim (\n. sum (2,n) (\n. inv (&FACT n) * -(R * h) pow n))) *
    (inv (t pow n)* t pow n)`--));
e(REAL_ARITH_TAC);;
e (DISCH_TAC THEN ONCE_ASM_REWRITE_TAC []);
e(MP_REWRITE_TAC (REAL_MUL_LINV));
e(KNOW_TAC (--` (t :real) pow n  <>  (0 :real)`--));
e(MATCH_MP_TAC POW_NZ);
e(MATCH_MP_TAC REAL_POS_NZ);
e(RW_TAC real_ss[REAL_ARITH `` (0 < (a:real)) = (a > 0) ``]);
e(FULL_SIMP_TAC std_ss []);
e (DISCH_TAC THEN ONCE_ASM_REWRITE_TAC []);
e(RW_TAC real_ss[REAL_MUL_RID]);
e(Cases_on `m=(1:num)`);
e(RW_TAC real_ss[]);
e(RW_TAC std_ss[cond_prob_def]);    
e(MP_REWRITE_TAC INDEP_LEMMA1);
e(RW_TAC std_ss[]);
e(KNOW_TAC (--`!x y. (x:real) * y / y = x * (y/y)`--));
e(RW_TAC real_ss[real_div, REAL_MUL_ASSOC]);
e(DISCH_TAC THEN ASM_REWRITE_TAC[]);
e(MP_REWRITE_TAC REAL_DIV_REFL);
e(RW_TAC real_ss[]);
e(FULL_SIMP_TAC real_ss[ Poisson_distr_rv_def,distribution_def]);
e(FULL_SIMP_TAC real_ss[ LEMMA1]);
e(RW_TAC std_ss[GSYM ADD1]);
e(KNOW_TAC(--`!n. &FACT (SUC n) = ((SUC n) * &FACT n) `--));
e(RW_TAC real_ss[FACT]);
e(RW_TAC std_ss[]);
e(RW_TAC std_ss[GSYM REAL_MUL]);
e(KNOW_TAC (--`!x y z. (x:real) / y * z = x * z / y `--));
e(RW_TAC real_ss[real_div]);
e(REAL_ARITH_TAC);
e(DISCH_TAC THEN ASM_REWRITE_TAC[]);
e(MP_REWRITE_TAC REAL_EQ_RDIV_EQ);
e(`0 < ((&FACT n):real)` by RW_TAC real_ss[FACT_LESS] );
e(KNOW_TAC (--`0 < ((&FACT n):real)`--));
e(RW_TAC real_ss[FACT_LESS]);
e(DISCH_TAC THEN ASM_REWRITE_TAC[]);
e(MP_REWRITE_TAC REAL_DIV_RMUL_CANCEL);
e(KNOW_TAC (--`((&FACT n):real) <> 0`--));
e(RW_TAC std_ss[REAL_FACT_NZ]);
e(DISCH_TAC THEN ASM_REWRITE_TAC[]);
e(` exp (-((R:real) * (t + h))) =  exp (-(R * t + R * h)) ` by METIS_TAC[REAL_ADD_LDISTRIB]);
e(ASM_REWRITE_TAC[]);
e(RW_TAC std_ss[REAL_NEG_ADD]);
e(RW_TAC std_ss[EXP_ADD]);
e(RW_TAC std_ss[real_div]);
e(REWRITE_TAC[REAL_MUL_ASSOC]);
e(KNOW_TAC(--`!R t h n g. ((R:real) * (t + h)) pow SUC n * exp (-(R * t)) * exp (-(R * h)) *  inv (&SUC n) =  
 exp (-(R * t)) * (R * (t + h)) pow SUC n  * exp (-(R * h)) *
      inv (&SUC n) `--));
e(REPEAT GEN_TAC);
e(REAL_ARITH_TAC);
e(DISCH_TAC THEN ONCE_ASM_REWRITE_TAC [] THEN POP_ASSUM K_TAC );
e(KNOW_TAC(--`!R t h n g. ((R:real) * t) pow n * exp (-(R * t)) * (R * h + g h) =  
exp (-(R * t)) * (R * t) pow n * (R * h + g h) `--));
e(REPEAT GEN_TAC);
e(REAL_ARITH_TAC);
e(DISCH_TAC THEN ONCE_ASM_REWRITE_TAC [] THEN POP_ASSUM K_TAC );
e(REWRITE_TAC[GSYM REAL_MUL_ASSOC]);
e(MP_REWRITE_TAC (GSYM REAL_EQ_LMUL2));
e(RW_TAC real_ss[EXP_POS_LT, REAL_POS_NZ]);
e(KNOW_TAC(--`(R :real) * (t + h) = R * t + R * h `--));
e(RW_TAC real_ss[REAL_ADD_LDISTRIB]);
e(DISCH_TAC THEN ASM_REWRITE_TAC[]);
e(ONCE_REWRITE_TAC[BINOMIAL_DEFN]);
e(ONCE_REWRITE_TAC[SUM_DIFF]);
e(REWRITE_TAC[ADD_COMM,GSYM ADD1]);
e(RW_TAC real_ss[SUM_0_SUM_2,pow,POW_1,SUM_1,BINOMIAL_DEF6,binomial_def]);
e(KNOW_TAC (--`! ( R: real) ( t: real) ( h: real) n. &SUC n * (R * t) pow n * (R * h) = 
&SUC n * R pow n * t pow n * (R * h)`--));
e(RW_TAC real_ss[POW_MUL]);
e(REAL_ARITH_TAC);
e(DISCH_TAC THEN ASM_REWRITE_TAC[]);
e(MP_REWRITE_TAC COMMON_OF_ADD_3);
e(RW_TAC std_ss[EXIST_OVER_AND]);
e(MATCH_MP_TAC REAL_MUL4_NZ);
e(RW_TAC real_ss[]);
e(MATCH_MP_TAC POW_NZ);
e(MATCH_MP_TAC REAL_POS_NZ);
e(RW_TAC real_ss[REAL_ARITH `` (0 < (a:real)) = (a > 0) ``]);
e(MATCH_MP_TAC POW_NZ);
e(MATCH_MP_TAC REAL_POS_NZ);
e(RW_TAC real_ss[REAL_ARITH `` (0 < (a:real)) = (a > 0) ``]);
e(MATCH_MP_TAC REAL_MUL2_NZ);
e(RW_TAC real_ss[]);
e(MATCH_MP_TAC REAL_POS_NZ);
e(RW_TAC real_ss[REAL_ARITH `` (0 < (a:real)) = (a > 0) ``]);
e(MATCH_MP_TAC REAL_POS_NZ);
e(RW_TAC real_ss[REAL_ARITH `` (0 < (a:real)) = (a > 0) ``]);
e(RW_TAC std_ss[REAL_MUL_ASSOC]);
e(KNOW_TAC(--`! ( R: real) ( t: real) ( h: real) n. &SUC n * R pow n * t pow n * R * h *
      (R * t * (R * t) pow n / (&SUC n * R pow n * t pow n * R * h) +
       1 +
       sum (2,n)
         (\x.
            &binomial (SUC n) x * (R * t) pow (SUC n - x) *
            (R * h) pow x) / (&SUC n *  R pow n * t pow n * R * h))
 * exp (-(R * h)) * inv (&SUC n) = 
     (R pow n * t pow n * R * h *
      (R * t * (R * t) pow n / (&SUC n * R pow n * t pow n * R * h) +
       1 +
       sum (2,n)
         (\x.
            &binomial (SUC n) x * (R * t) pow (SUC n - x) *
            (R * h) pow x) / (&SUC n *  R pow n * t pow n * R * h)) *
        exp (-(R * h))) *((&SUC n)* inv (&SUC n))
`--));
e(REAL_ARITH_TAC);
e(DISCH_TAC THEN ONCE_ASM_REWRITE_TAC [] THEN POP_ASSUM K_TAC );

e(MP_REWRITE_TAC REAL_MUL_RINV);
e(RW_TAC std_ss[EXIST_OVER_AND]);
e(RW_TAC real_ss[]);
e(RW_TAC real_ss[]);
e(RW_TAC real_ss[EXP_SPLIT]);

e(RW_TAC real_ss[REAL_ARITH ``(a:real)*b*c*d*e*f = a*b*(c*d*e*f)``]);
e(RW_TAC real_ss[ POW_MUL]);
e(MP_REWRITE_TAC (GSYM REAL_EQ_LMUL2));
e(RW_TAC std_ss[EXIST_OVER_AND]);
e(RW_TAC real_ss[REAL_ARITH `` (0 <> (a:real)) = (a <> 0) ``]);
e(MATCH_MP_TAC REAL_MUL2_NZ);
e(RW_TAC real_ss[]);
e(MATCH_MP_TAC POW_NZ);
e(MATCH_MP_TAC REAL_POS_NZ);
e(RW_TAC real_ss[REAL_ARITH `` (0 < (a:real)) = (a > 0) ``]);
e(MATCH_MP_TAC POW_NZ);
e(MATCH_MP_TAC REAL_POS_NZ);
e(RW_TAC real_ss[REAL_ARITH `` (0 < (a:real)) = (a > 0) ``]);
e(RW_TAC std_ss[REAL_MUL_ASSOC]);
e(RW_TAC std_ss[REAL_ADD_SYM]);
e(RW_TAC real_ss[GSYM REAL_EQ_SUB_RADD]);
e(EXISTS_TAC(--`(\h. (R:real) * h *
      (1 +
       R * t * R pow n * t pow n / (&SUC n * R pow n * t pow n * R * h) +
       sum (2,n)
         (\x.
            &binomial (SUC n) x * R pow (SUC n - x) * t pow (SUC n - x) *
            R pow x * h pow x) / (&SUC n * R pow n * t pow n * R * h)) *
      (1 + lim (\n. sum (1,n) (\n. inv (&FACT n) * -(R * h) pow n))) -
      R * h) `-- ));
e(RW_TAC real_ss[]);

e(RW_TAC std_ss[]);
e(RW_TAC std_ss[cond_prob_def]);
e(MP_REWRITE_TAC INDEP_LEMMA2);


e(RW_TAC std_ss[]);
e(KNOW_TAC (--`!x y. (x:real) * y / y = x * (y/y)`--));
e(RW_TAC real_ss[real_div, REAL_MUL_ASSOC]);
e(DISCH_TAC THEN ASM_REWRITE_TAC[]);
e(MP_REWRITE_TAC REAL_DIV_REFL);
e(RW_TAC real_ss[]);
e(FULL_SIMP_TAC real_ss[ Poisson_distr_rv_def,distribution_def]);
e(FULL_SIMP_TAC real_ss[ LEMMA2]);
e(KNOW_TAC(--`!n m.  &n + &m = &m + &n`--));
e(RW_TAC std_ss[add_comm]);
e(RW_TAC std_ss[]);
e(RW_TAC std_ss[pow_add]);
e(` exp (-((R:real) * (t + h))) =  exp (-(R * t + R * h)) ` by METIS_TAC[REAL_ADD_LDISTRIB]);
e(ASM_REWRITE_TAC[]);
e(RW_TAC std_ss[REAL_NEG_ADD]);
e(RW_TAC std_ss[EXP_ADD]);
e(REWRITE_TAC[REAL_MUL_ASSOC]);
e(RW_TAC real_ss[real_div]);
e(KNOW_TAC(--`!R t h n m. ((R:real) * (t + h)) pow (m + n) * exp (-(R * t)) * exp (-(R * h)) *
      inv (&FACT (m + n)) =  exp (-(R * t)) * (R * (t + h)) pow (m + n) * exp (-(R * h)) *
      inv (&FACT (m + n)) `--));
e(REPEAT GEN_TAC);
e(REAL_ARITH_TAC);
e (DISCH_TAC THEN ONCE_ASM_REWRITE_TAC [] THEN POP_ASSUM K_TAC);
e(KNOW_TAC(--`!R t h n (g3 :real -> real). ((R:real) * t) pow n * exp (-(R * t)) * 
inv (&FACT n) * g3 h =  exp (-(R * t)) * (R * t) pow n * inv (&FACT n) * g3 h`--));
e(REPEAT GEN_TAC);
e(REAL_ARITH_TAC);
e (DISCH_TAC THEN ONCE_ASM_REWRITE_TAC [] THEN POP_ASSUM K_TAC);
e(REWRITE_TAC[GSYM REAL_MUL_ASSOC]);
e(MP_REWRITE_TAC (GSYM REAL_EQ_LMUL2));
e(RW_TAC real_ss[EXP_POS_LT, REAL_POS_NZ]);
e(REWRITE_TAC[REAL_MUL_ASSOC]);
e(KNOW_TAC(--`!R t h n (g3 :real -> real). ((R:real) * t) pow n * inv (&FACT n) * g3 h =  
g3 h * (R * t) pow n * inv (&FACT n) `--));
e(REPEAT GEN_TAC);
e(REAL_ARITH_TAC);
e (DISCH_TAC THEN ONCE_ASM_REWRITE_TAC [] THEN POP_ASSUM K_TAC);

e(MP_REWRITE_TAC (GSYM REAL_EQ_LDIV_EQ));
e(KNOW_TAC (--`0 < ((inv (&FACT n)):real)`--));
e(RW_TAC std_ss[REAL_LT_INV_EQ]);
e(RW_TAC real_ss[FACT_LESS]);
e(DISCH_TAC THEN ASM_REWRITE_TAC[]);
e(RW_TAC real_ss[real_div]);
e(MP_REWRITE_TAC REAL_INVINV);
e(`((&FACT n):real) <> 0 ` by METIS_TAC [REAL_FACT_NZ]);
e(FULL_SIMP_TAC std_ss []);
e(RW_TAC std_ss[POW_MUL]);
e(REWRITE_TAC[REAL_MUL_ASSOC]);
e(MP_REWRITE_TAC (GSYM REAL_EQ_LDIV_EQ));
e(KNOW_TAC (--`(0 :real) < (t :real) pow n`--));
e(MATCH_MP_TAC REAL_POW_LT);
e(RW_TAC real_ss[REAL_ARITH `` (0 < (a:real)) = (a > 0) ``]);
e(DISCH_TAC THEN ASM_REWRITE_TAC[]);
e(MP_REWRITE_TAC (GSYM REAL_EQ_LDIV_EQ));
e(KNOW_TAC (--`(0 :real) < (R :real) pow n`--));
e(MATCH_MP_TAC REAL_POW_LT);
e(RW_TAC real_ss[REAL_ARITH `` (0 < (a:real)) = (a > 0) ``]);
e(DISCH_TAC THEN ASM_REWRITE_TAC[]);
e(RW_TAC real_ss[real_div]);
e(EXISTS_TAC(--`(\h. (R:real) pow (m + n) * (t + h) pow (m + n) * exp (-(R * h)) *
      inv (&FACT (m + n)) * &FACT n * inv (t pow n) * inv (R pow n) ) `-- ));

e(RW_TAC real_ss[]);

val Poisson_LEMMA = top_thm();
drop();

g`!X (R:real) p h n m.  
     (!i. {&n + &i} IN subsets s) /\
     (!m n. indep_rv p (\t. X (t + h)) (\t. X t) s s {&m} {&n}) /\
     prob p (PREIMAGE (\t. X t) {&n} INTER p_space p)<> 0 /\
     (&n IN IMAGE (\t. X (t + h)) (p_space p)) /\
     (R > (0:real)) /\ (t > (0:real)) /\ (h > 0) /\ 
     (!k n. Poisson_distr_rv (\t. X (t + k)) p (t + k) R (n))==> 
    	is_poisson_proces X p t R h n m`;


e(REPEAT STRIP_TAC);
e(MATCH_MP_TAC Poisson_LEMMA);
e(RW_TAC real_ss[]);
e(UNDISCH_TAC(-- ` !i. {&n + &i} IN subsets s `--));
e (DISCH_TAC);
e (POP_ASSUM (MP_TAC o Q.SPEC `0`));
e(RW_TAC real_ss[GSYM LEMMA2]);
e(RW_TAC real_ss[GSYM LEMMA1]);
e(RW_TAC real_ss[GSYM LEMMA2]);
val POISSON_PROCESS = top_thm();
drop();

val Occ_def = 
Define ` Occ_def X p (f:real)t R n  = 
     (Poisson_distr_rv (\t. X t) p t R n)  /\  (Poisson_distr_rv (\t. X (f - t)) p t R n) 
==> (distribution p (\t. X ( f - t)) {&0} = distribution p (\t. X t) {&0}  )`;




val Exp_distr_rv_def = 
Define `Exp_distr_rv X p R  = (!t. distribution p X {f | f <= Normal t}= 
if t>=0 then 1 - exp (-R * t) else 0)`;



g`!X (R:real) p (T:real).prob p (PREIMAGE (\t. X t) {0} INTER p_space p) <> 0 /\ 
{&0} IN subsets s /\ indep_rv p (\t. X (T -t)) (\t. X t) s s {&0} {&0} /\ 
(Poisson_distr_rv (\t.X (T - t)) p (T - (t:real)) R 0)  ==> 
((cond_prob p (PREIMAGE (\t. X ( t+h)) {&0} INTER p_space p) 
      (PREIMAGE (\t. X  t) {&0} INTER p_space p)) = 
(prob p (PREIMAGE (\t. X t) {&0} INTER p_space p)))`;

e(RW_TAC std_ss[]);
e(RW_TAC std_ss[cond_prob_def]);    
e(MP_REWRITE_TAC INDEP_LEMMA);
e(RW_TAC std_ss[]);
e(KNOW_TAC (--`!x y. (x:real) * y / y = x * (y/y)`--));
e(RW_TAC real_ss[real_div, REAL_MUL_ASSOC]);
e(DISCH_TAC THEN ASM_REWRITE_TAC[]);
e(MP_REWRITE_TAC REAL_DIV_REFL);
e(RW_TAC real_ss[]);
e(FULL_SIMP_TAC real_ss[ Poisson_distr_rv_def,distribution_def]);


e(FULL_SIMP_TAC real_ss[indep_rv_def]);
e(FULL_SIMP_TAC real_ss[indep_def]);
e (RW_TAC real_ss[]);


val INDEP_LEMMA1 = top_thm();
drop();


g`! n. SUC n - 1 = n `;
e(RW_TAC real_ss[ADD1]);
val N_SHIFT= top_thm();drop();


fun SET_TAC L =
    POP_ASSUM_LIST(K ALL_TAC) THEN REPEAT COND_CASES_TAC THEN
    REWRITE_TAC (append [EXTENSION, SUBSET_DEF, PSUBSET_DEF, DISJOINT_DEF,
    SING_DEF] L) THEN SIMP_TAC std_ss [NOT_IN_EMPTY, IN_UNIV, IN_UNION,
    IN_INTER, IN_DIFF, IN_INSERT, IN_DELETE, IN_BIGINTER, IN_BIGUNION,
    IN_IMAGE, GSPECIFICATION, IN_DEF] THEN MESON_TAC [];

fun SET_RULE tm = prove(tm,SET_TAC []);





g` !(x:real) (a:real) b c. ~(a = 0) ==> (( a*b*c = k) = 
                         (((inv a * a)*b*c) = inv a * k) )`;;
e(ONCE_REWRITE_TAC[GSYM REAL_MUL_ASSOC]);
e(ONCE_REWRITE_TAC[GSYM REAL_MUL_ASSOC]);
e(ONCE_REWRITE_TAC[GSYM REAL_MUL_ASSOC]);
e(RW_TAC std_ss[REAL_EQ_LMUL2,REAL_INV_NZ]);
 val REAL_MUL_INV = top_thm();
drop();


 val increasing_seq = Define ` 
     increasing_seq (t:real->num) <=> 
     (!i j. i < j ==> t i < t j)`;

val counting_process = Define ` 
    counting_process N <=> ((N(&0) = 0) /\ 
    increasing_seq N)`;

val trans_fun1 = Define ` trans_fun1 (X :real -> num) p t R h n m = ( ?g1 g2 g3. 
    cond_prob p (PREIMAGE (\t.X ((t:real) + h)) {&n + &m} INTER p_space p) 
    (PREIMAGE (\t. X t) {&n} INTER p_space p) =  
    if (m = 0) 
       then ((((R * t) pow n) * 
      (exp (- R * t)) / ((&FACT n):real)) * (1 - R * h + g1 h))
    else if (m = 1) then
       	   ( (((R * t) pow n) * 
      (exp (- R * t)) / ((&FACT n):real)) * (R  * h + g2 h) )
    else  ( (((R * t) pow n) * 
      (exp (- R * t)) / ((&FACT n):real)) * (g3 h)))`;

val is_poisson_proces1 = Define `
    is_poisson_proces1 (X :real -> num) p s t R h n m = 
    (random_variable (X) p s) /\ trans_fun1 X p t R h n m /\  counting_process X`;





 g`!X p (N:real->num) (A1:real) (t:real). (N(A1) = 1) /\ (counting_process N)/\ t < A1 ==>  (prob p (PREIMAGE X {&(N(t))}  INTER p_space p) =  (distribution p X {&0}))`;

e(RW_TAC real_ss[counting_process,increasing_seq]); e(POP_ASSUM
MP_TAC); e(POP_ASSUM (MP_TAC o Q.SPEC `t:real`)); e(DISCH_TAC);
e(POP_ASSUM (MP_TAC o Q.SPEC `A1:real`)); e(RW_TAC real_ss[]);
e(FULL_SIMP_TAC real_ss[]);

e(KNOW_TAC(--`(!X (t:real).  (X t < (1:num)) ==> (X t =
(0:num)))`--));; e(DECIDE_TAC); e(DISCH_TAC); e(REPEAT(POP_ASSUM
MP_TAC)); e(METIS_TAC[distribution_def]);
val INTERARRIVAL = top_thm(); drop();


g` !N X p t R. (!n. Poisson_distr_rv X p t R n)/\ ( Exp_distr_rv Y p R ) /\ (N A1 = 1)  /\
    counting_process N /\ t < A1 /\ t>=0 ==>  (prob p (PREIMAGE X {&N t} INTER
    p_space p) =1-(distribution p  Y  {f|f <= Normal t}) )`;

e(RW_TAC real_ss[Poisson_distr_rv_def, Exp_distr_rv_def]); e(POP_ASSUM MP_TAC);e(POP_ASSUM MP_TAC);
e(POP_ASSUM MP_TAC); e(POP_ASSUM MP_TAC);e(POP_ASSUM MP_TAC);e(POP_ASSUM (MP_TAC o Q.SPEC
`0 :num `)); e(RW_TAC
real_ss[FACT,real_div,REAL_MUL_RINV,REAL_INV1]);;
e( METIS_TAC [ INTERARRIVAL]);

val INTERARRIVAL_POISSON = top_thm(); drop();



g` !n s p (t:real) h X (N :real -> num). {&N t} IN subsets s /\ {&N
 (t+h)} IN subsets s  /\  indep_rv p (\t. X (t + h)) (\t. X t) s s {&N
 (t+h)} {&N t}   ==> (prob p ((PREIMAGE (\t. X (t + h)) {&N (t+h)}
 INTER p_space p) INTER (PREIMAGE (\t. X t) {&N t} INTER p_space p)) =
 (prob p (PREIMAGE (\t. X (t + h)) {&N (t+h)} INTER p_space p) * prob
 p (PREIMAGE (\t. X t) {&N t} INTER p_space p))) `;

e(RW_TAC std_ss[]); e(MATCH_MP_TAC PROB_INDEP); e(REPEAT STRIP_TAC);
e(FULL_SIMP_TAC std_ss [indep_rv_def]); e(RW_TAC std_ss[]);

val INDEP_LEMMA_Mem = top_thm(); drop();





g` !n s p (t:real) h X (N :real -> num). {&N t} IN subsets s /\ {&N
 (t+h)} IN subsets s  /\ (PREIMAGE (\t. X (t + h)) {&N (t+h)} INTER p_space p) SUBSET (PREIMAGE (\t. X t) {&N t} INTER p_space p)  ==> (prob p ((PREIMAGE (\t. X (t + h)) {&N (t+h)} INTER p_space p) INTER (PREIMAGE (\t. X t) {&N t} INTER p_space p)) =
 (prob p (PREIMAGE (\t. X (t + h)) {&N (t+h)} INTER p_space p) )
) `;

e(RW_TAC std_ss [SUBSET_INTER_ABSORPTION]);
val Mem_LEMMA2 = top_thm(); drop();




g` !X p t R h. (prob_space p /\ PREIMAGE X {f | f <= Normal t} INTER p_space p IN events p /\ PREIMAGE X {f | f <= Normal (t+h) } INTER p_space p IN events p /\ Exp_distr_rv X p R ) /\(PREIMAGE X {f|(Normal (t+h)) < f} INTER p_space p) SUBSET (PREIMAGE X {f| (Normal t) <f} INTER p_space p) /\ t>=0 /\ h>=0 ==>  (cond_prob p (PREIMAGE X {f| (Normal(t+h) <f)} INTER p_space p) (PREIMAGE X {f|(Normal t) <f} INTER p_space p) = exp(-R *h))`;

e(RW_TAC std_ss [cond_prob_def]);
e(FULL_SIMP_TAC  std_ss [SUBSET_INTER_ABSORPTION]);


e(KNOW_TAC (--`PREIMAGE X {f | Normal t < f} INTER p_space p =  p_space p DIFF PREIMAGE X {f | f <= Normal t} INTER p_space p`--));

e(SRW_TAC[][PREIMAGE_def,EXTENSION,GSPECIFICATION]);

e(EQ_TAC);
e(RW_TAC std_ss[]);
e(RW_TAC std_ss[]);
e(FULL_SIMP_TAC real_ss [extreal_lt_def]);

e(RW_TAC std_ss[]);
e(FULL_SIMP_TAC real_ss [extreal_lt_def]);
e(RW_TAC std_ss[ ]);
e(KNOW_TAC (--`PREIMAGE X {f | Normal (t+h) < f} INTER p_space p =  p_space p DIFF PREIMAGE X {f | f <= Normal (t+h)} INTER p_space p`--));

e(SRW_TAC[][PREIMAGE_def,EXTENSION,GSPECIFICATION]);

e(EQ_TAC);
e(RW_TAC std_ss[]);
e(RW_TAC std_ss[]);
e(FULL_SIMP_TAC real_ss [extreal_lt_def]);

e(RW_TAC std_ss[]);
e(FULL_SIMP_TAC real_ss [extreal_lt_def]);
e(RW_TAC std_ss[ ]);

e(RW_TAC std_ss[]);

e(SRW_TAC[][PROB_COMPL,EXTENSION,GSPECIFICATION]);

e(KNOW_TAC (--`t+h>=0`--));
e(FULL_SIMP_TAC real_ss [real_ge, REAL_LE_ADD]);
e(RW_TAC std_ss[]);

e(UNDISCH_TAC (--`t+h>=0`--));
e(UNDISCH_TAC (--`t>=0`--));
e(UNDISCH_TAC (--`Exp_distr_rv X p R `--));
e(RW_TAC std_ss [Exp_distr_rv_def, distribution_def]);



e(RW_TAC std_ss[]);


e(RW_TAC real_ss [REAL_LDISTRIB]);

e(KNOW_TAC (--`!(R:real) (t:real). exp (-(R*t)) <> 0`--));
e(RW_TAC real_ss[EXP_NZ]);
e(RW_TAC std_ss[]);

e(KNOW_TAC (--`!(R:real) (t:real) (h:real). -(R*t+R*h) = -R*t + -R*h`--));

e(REAL_ARITH_TAC);
e(RW_TAC real_ss[]);

e(RW_TAC std_ss [transcTheory.EXP_ADD]);
e(RW_TAC real_ss [REAL_MUL_COMM]);
e(RW_TAC std_ss [real_div]);
e(RW_TAC std_ss [GSYM EXP_NEG, REAL_NEGNEG]);
e(KNOW_TAC (--`!(R:real) (t:real). exp(-(R*t)) * exp (R*t) = 1`--));
e(RW_TAC std_ss [EXP_NEG_MUL2]);

e(RW_TAC std_ss [GSYM REAL_MUL_ASSOC]);
e(RW_TAC std_ss [REAL_MUL_RID]);

val Exponential_memoryless = top_thm();
drop();






(* ========================================================================= *)
(*                                  Applications       			     *)
(* ========================================================================= *)


val _ = Hol_datatype `SIGNAL = ZERO | ONE`;


val Poisson_dist = 
Define `Poisson_distr (t:real) R n  = 
     (((R * t) pow n) * (exp (- R * t) )) /((&FACT n):real) `;


val prob_zero_sent = Define ` 
    prob_zero_sent p X A n  R_a  <=>  
    (cond_prob p X A = Poisson_distr (1:real) R_a n)` ;

val prob_one_sent = Define ` 
    prob_one_sent p X B n  R_b  <=>  
    (cond_prob p X B = Poisson_distr (1:real) R_b n)` ;


val MAP = Define ` 
          MAP p X A B <=> 
         cond_prob p A X > cond_prob p B X `;


val Decison = Define ` 
             Decison A B D =
             (D ZERO = B) /\  
             (D ONE = A)`;


(* ========================================================================= *)
(*                          MAP Decision Rule            		     *)
(* ========================================================================= *)
 
g` !(f:SIGNAL->real).  DISJOINT {ZERO} {ONE}
 ==>

  ( SIGMA (\i. f i) ({ZERO} UNION {ONE}) = f ZERO + f ONE)` ;

e(GEN_TAC);
e(DISCH_TAC);
e(MP_REWRITE_TAC REAL_SUM_IMAGE_DISJOINT_UNION);
e(REPEAT STRIP_TAC);
e(RW_TAC real_ss[FINITE_DEF]);
e(RW_TAC real_ss[FINITE_DEF]);
e(RW_TAC real_ss[DISJOINT_DEF]);
e(RW_TAC real_ss[REAL_SUM_IMAGE_SING]);

val SIGMA_UNION = top_thm();
drop();



g`!(R_a:real) R_b (n:num).   0 < R_b /\ R_b < R_a 
 ==> 

0 < (1 / 2 * (R_b pow n * exp (-R_b) / &FACT n) +
     1 / 2 * (R_a pow n * exp (-R_a) / &FACT n))`;

e(RW_TAC real_ss[GSYM REAL_ADD_LDISTRIB]);
e(MP_REWRITE_TAC REAL_LT_RMUL_0);
e(RW_TAC std_ss[REAL_HALF_BETWEEN]);
e(RW_TAC std_ss[real_div]);
e(RW_TAC real_ss[REAL_LT_RMUL_0,REAL_FACT_NZ,FACT_LESS]);
e(MATCH_MP_TAC REAL_LT_ADD);
e(RW_TAC real_ss[]);
e(MP_REWRITE_TAC REAL_LT_RMUL_0);
e(RW_TAC real_ss[]);
e(RW_TAC real_ss[EXP_POS_LT]);
e(MATCH_MP_TAC REAL_POW_LT);
e(ASM_REWRITE_TAC[]);
e(MP_REWRITE_TAC REAL_LT_RMUL_0);
e(RW_TAC real_ss[]);
e(RW_TAC real_ss[EXP_POS_LT]);
e(MATCH_MP_TAC REAL_POW_LT);
e(KNOW_TAC(--` 0 < (R_b:real)  /\   R_b < R_a ==> 0 < R_a  `--));
e(REAL_ARITH_TAC);
e(DISCH_TAC THEN ONCE_ASM_REWRITE_TAC[]);
e(FULL_SIMP_TAC std_ss[]);

val EXPR_GT_0 = top_thm();
drop();







g`  ! p X A B (n:num) (R_a :real) (R_b:real). 
               (prob p A = &1/ &2) /\  DISJOINT B A /\ 
               0 < R_b /\ R_b < R_a /\ ~(ONE:SIGNAL = ZERO) /\ 
               DISJOINT {ZERO} {ONE} /\
               (prob p B = &1/ &2) /\ Decison A B D /\
               (!x. D x IN events p) /\
  	       A IN events p /\ 
               B IN events p /\ 
               (BIGUNION (IMAGE D {ZERO; ONE}) = p_space p) /\
	       PREIMAGE X {&n} INTER p_space p IN events p /\
               prob_space p  /\ (R_a - R_b) / ln (R_a / R_b) < &n /\
prob_zero_sent p (PREIMAGE X {&n} INTER p_space p) A n  R_a  /\
prob_one_sent p (PREIMAGE X {&n} INTER p_space p) B n  R_b   

==> 
               
 MAP p (PREIMAGE X {&n} INTER p_space p) A B `;

e(RW_TAC std_ss[prob_zero_sent,   prob_one_sent, MAP]);
e (MP_REWRITE_TAC BAYES_RULE);
e(RW_TAC real_ss[]);
e(KNOW_TAC(--`prob p (PREIMAGE X {&n} INTER p_space p)  = 
              SIGMA (\i. (\i. prob p (D i) * cond_prob p (PREIMAGE X {&n} INTER p_space p)
 (D i)) i) {ZERO;ONE}`--));
e(RW_TAC real_ss[]);
e(MATCH_MP_TAC TOTAL_PROB_SIGMA);
e(RW_TAC real_ss[]);
e(RW_TAC real_ss[FINITE_DEF]);
e( `(a IN {ZERO; ONE}) =  ((a = ZERO) \/ (a = ONE))` by SET_TAC[]);
e( `(b IN {ZERO; ONE}) =  ((b = ZERO) \/ (b = ONE))` by SET_TAC[]);
e(FULL_SIMP_TAC std_ss[Decison]);
e(RW_TAC std_ss[  DISJOINT_DEF]);
e(KNOW_TAC(-- `DISJOINT B A ==> DISJOINT A B`--));
e(SET_TAC[DISJOINT_DEF]);
e(METIS_TAC[]);
e(RW_TAC std_ss[  DISJOINT_DEF]);
e(`{ZERO;ONE} = {ZERO} UNION {ONE}` by EVAL_TAC);
e(ASM_REWRITE_TAC[]);
e(RW_TAC std_ss[SIGMA_UNION]);
e(FULL_SIMP_TAC std_ss[ Decison]);
e(RW_TAC std_ss[  Poisson_dist,REAL_MUL_RID,REAL_MUL_LID]);
e(RW_TAC std_ss[real_gt]);
e(MP_REWRITE_TAC REAL_LT_RDIV);
e(RW_TAC std_ss[EXPR_GT_0]);
e(KNOW_TAC(--` (R_b:real) pow n * exp (-R_b) / &FACT n * (1 / 2) <
    R_a pow n * exp (-R_a) / &FACT n * (1 / 2) = 
        R_b pow n * exp (-R_b) / (&FACT n * (2)) <
    R_a pow n * exp (-R_a) / (&FACT n * ( 2))`--));
e(RW_TAC real_ss[real_div,REAL_INV_INV,REAL_INV_MUL]);
e(ONCE_REWRITE_TAC[GSYM REAL_OF_NUM_MUL]);
e(RW_TAC real_ss[REAL_FACT_NZ,REAL_INV_MUL]);
e(REAL_ARITH_TAC);
e(DISCH_TAC THEN ONCE_ASM_REWRITE_TAC[]);
e(MP_REWRITE_TAC REAL_LT_RDIV);
e(RW_TAC real_ss[REAL_LT_RMUL_0,REAL_FACT_NZ,FACT_LESS]);;
e(MP_REWRITE_TAC (GSYM REAL_LT_LDIV_EQ));
e(RW_TAC real_ss[]);
e(RW_TAC real_ss[EXP_POS_LT]);
e(RW_TAC std_ss[real_div]);
e(RW_TAC std_ss[GSYM REAL_MUL_ASSOC]);
e(KNOW_TAC(--` ((R_b:real) pow n * (exp (-R_b) * inv (exp (-R_a))) < R_a pow n)  
=  ((exp (-R_b) * inv (exp (-R_a))) *  R_b pow n  < R_a pow n)

`--));
e(RW_TAC std_ss[REAL_MUL_COMM]);
e(DISCH_TAC THEN ONCE_ASM_REWRITE_TAC[]);
e(MP_REWRITE_TAC (GSYM REAL_LT_RDIV_EQ));
e(RW_TAC real_ss[]);
e(MATCH_MP_TAC REAL_POW_LT);
e(RW_TAC real_ss[]);
e(RW_TAC std_ss[GSYM REAL_POW_DIV,GSYM real_div ,GSYM EXP_SUB,REAL_SUB_NEG2]);
e(MP_REWRITE_TAC (GSYM LN_MONO_LT));
e(RW_TAC real_ss[]);
e(RW_TAC real_ss[EXP_POS_LT]);
e(MATCH_MP_TAC REAL_LT_DIV);
e(RW_TAC real_ss[]);
e(MATCH_MP_TAC REAL_POW_LT);
e(KNOW_TAC(--` 0 < (R_b:real)  /\   R_b < R_a ==> 0 < R_a  `--));
e(REAL_ARITH_TAC);
e(DISCH_TAC THEN ONCE_ASM_REWRITE_TAC[]);
e(FULL_SIMP_TAC std_ss[]);
e(MATCH_MP_TAC REAL_POW_LT);
e(RW_TAC real_ss[]);
e(RW_TAC std_ss[GSYM REAL_POW_DIV]);
e(KNOW_TAC(--` ln (((R_a:real) / R_b) pow n) = &n * ln (R_a / R_b) `--));
e(MATCH_MP_TAC LN_POW);
e(MATCH_MP_TAC REAL_LT_DIV);
e(RW_TAC real_ss[]);
e(KNOW_TAC(--` 0 < (R_b:real)  /\   R_b < R_a ==> 0 < R_a  `--));
e(REAL_ARITH_TAC);
e(DISCH_TAC THEN ONCE_ASM_REWRITE_TAC[]);
e(FULL_SIMP_TAC std_ss[]);
e(DISCH_TAC THEN ONCE_ASM_REWRITE_TAC[]);
e(RW_TAC real_ss[LN_EXP]);
e(MP_REWRITE_TAC (GSYM REAL_LT_LDIV_EQ));
e(RW_TAC real_ss[]);
e(KNOW_TAC(--`ln ((R_a:real) / R_b) = ln R_a - ln R_b`--));
e(MATCH_MP_TAC LN_DIV);
e(RW_TAC real_ss[]);


e(DISCH_TAC THEN ONCE_ASM_REWRITE_TAC[]);

e(KNOW_TAC(--` 0 < (R_b:real)  /\   R_b < R_a ==> 0 < R_a  `--));
e(REAL_ARITH_TAC);
e(DISCH_TAC THEN ONCE_ASM_REWRITE_TAC[]);
e(FULL_SIMP_TAC std_ss[]);
e(DISCH_TAC THEN ONCE_ASM_REWRITE_TAC[]);
e(RW_TAC real_ss[REAL_SUB_LT]);
e(MP_REWRITE_TAC LN_MONO_LT);
e(RW_TAC real_ss[]);
e(KNOW_TAC(--` 0 < (R_b:real)  /\   R_b < R_a ==> 0 < R_a  `--));
e(REAL_ARITH_TAC);
e(DISCH_TAC THEN ONCE_ASM_REWRITE_TAC[]);
e(FULL_SIMP_TAC std_ss[]);

val MAP_threshold = top_thm();
drop();

(* ========================================================================= *)
(*                             Probability Error             		     *)
(* ========================================================================= *)

val count_mn_def = new_definition 
  ("count_mn_def", ``count_mn (m:num) (n:num) = {r | (m <= r) /\ (r <= n)}``);

val COUNT_MN_COUNT = store_thm
  ("COUNT_MN_COUNT",
   ``!n. count_mn 0 n = count (SUC n)``,
   PSET_TAC [count_mn_def, EXTENSION] ++ ARITH_TAC);  


val prob_error_zero_sent = Define ` 
    prob_error_zero_sent p X B n R_b ERROR n_0 <=>  
    (cond_prob p ERROR B = 1 - SIGMA (\i. R_b pow i * exp (-R_b) / &FACT i) (count_mn 0 &n_0))` ;

val prob_error_one_sent = Define ` 
    prob_error_one_sent p X A n R_a ERROR n_0 <=>  
    (cond_prob p ERROR A =  SIGMA (\i. R_a pow i * exp (-R_a) / &FACT i) (count_mn 0 &n_0))` ;


g`  ! (a :real) (b:real) (c: real) (d: real).a + b * -c + b * d = a + (b * (-c + d))`;
e(REAL_ARITH_TAC);
val DISTRB_ADD = top_thm();
drop();


g` !m n. FINITE (count_mn m n)`;
e(RW_TAC std_ss[]);
e(`count_mn m n = count (SUC n) DIFF (count m)` 
   by PSET_TAC [EXTENSION, count_mn_def]);
e(RW_TAC arith_ss []);

e(FULL_SIMP_TAC real_ss [FINITE_COUNT,FINITE_DIFF]);

val FINITE_COUNT_MN = top_thm();
drop();









g` ! p X A B ERROE (n:num) (R_a :real) (R_b:real) . 
               (prob p A = &1/ &2) /\  DISJOINT B A /\ 
               0 < R_b /\ R_b < R_a /\ ~(ONE:SIGNAL = ZERO) /\ 
               DISJOINT {ZERO} {ONE} /\
               (prob p B = &1/ &2) /\ Decison A B D /\
               (!x. D x IN events p) /\
  	       A IN events p /\ 
               B IN events p /\ 
               ERROR IN events p /\
               (BIGUNION (IMAGE D {ZERO; ONE}) = p_space p) /\
	       PREIMAGE X {&n} INTER p_space p IN events p /\
               prob_space p  /\ ((R_a - R_b) / ln (R_a / R_b) = &n_0) /\
 prob_error_one_sent p X A n R_a ERROR n_0 /\
 prob_error_zero_sent p X B n R_b ERROR n_0   

==>
 (prob p ERROR = (1 / 2 +
         1 / 2 *
         SIGMA
           (\x.
              R_a pow x * exp (-R_a) / &FACT x -
              R_b pow x * exp (-R_b) / &FACT x) (count_mn 0 n_0))) `;


e(RW_TAC real_ss[]);
e(KNOW_TAC(--`prob p ERROR  = 
              SIGMA (\i. (\i. prob p (D i) * cond_prob p ERROR (D i)) i) {ZERO;ONE}`--));
e(RW_TAC real_ss[]);
e(MATCH_MP_TAC TOTAL_PROB_SIGMA);
e(RW_TAC real_ss[]);
e(RW_TAC real_ss[FINITE_DEF]);
e( `(a IN {ZERO; ONE}) =  ((a = ZERO) \/ (a = ONE))` by SET_TAC[]);
e( `(b IN {ZERO; ONE}) =  ((b = ZERO) \/ (b = ONE))` by SET_TAC[]);
e(FULL_SIMP_TAC std_ss[Decison]);
e(RW_TAC std_ss[  DISJOINT_DEF]);
e(KNOW_TAC(-- `DISJOINT B A ==> DISJOINT A B`--));
e(SET_TAC[DISJOINT_DEF]);
e(METIS_TAC[]);
e(RW_TAC std_ss[  DISJOINT_DEF]);
e(`{ZERO;ONE} = {ZERO} UNION {ONE}` by EVAL_TAC);
e(ASM_REWRITE_TAC[]);
e(RW_TAC std_ss[SIGMA_UNION]);
e(FULL_SIMP_TAC std_ss[ Decison,prob_error_zero_sent,prob_error_one_sent]);
e(RW_TAC std_ss[real_sub, REAL_LDISTRIB,REAL_MUL_RID]);
e(RW_TAC real_ss[DISTRB_ADD]);
e(RW_TAC real_ss[REAL_ADD_COMM]);
e(RW_TAC real_ss[GSYM real_sub]);
e(MP_REWRITE_TAC (GSYM REAL_SUM_IMAGE_SUB));
e(RW_TAC real_ss[FINITE_COUNT_MN]);
val Prob_ERROR = top_thm();
drop();


(* ========================================================================= *)
(*                              Definitions             		     *)
(* ========================================================================= *)


val Runway_def = Define `Runway_def X p t n i j FUN IFUN R h s =
   MM1_def X p t n i j FUN IFUN R h s `;


g `!x y. ((x - y) <> NegInf) /\ ((x - y) <> PosInf) /\ (x <> NegInf) ==> (y <> PosInf)`;

e(RW_TAC std_ss []);
e(Cases_on `y <> PosInf`);
e(RW_TAC real_ss []);
e(`y = PosInf` by METIS_TAC []);
e(KNOW_TAC(--` x - y = NegInf `--));
e(Cases_on `x`);
e(METIS_TAC [extreal_sub_def]);
e(METIS_TAC [extreal_sub_def]);
e(METIS_TAC [extreal_sub_def]);
e(RW_TAC real_ss []);

val extreal_sub_x_not_infty = top_thm(); drop();


g `!x y. ((x - y) <> PosInf) /\ (y <> PosInf) ==> (x <> PosInf)`;
e(RW_TAC real_ss []);
e(Cases_on `x <> PosInf`);
e(RW_TAC real_ss []);
e(`x = PosInf` by METIS_TAC []);
e(KNOW_TAC(--` x - y = PosInf `--));
e(RW_TAC real_ss []);
e(Cases_on `y`);
e(METIS_TAC [extreal_sub_def]);
e(METIS_TAC [extreal_sub_def]);
e(METIS_TAC [extreal_sub_def]);
e(STRIP_TAC);

val extreal_sub_y_not_infty = top_thm(); drop();


g `!X Y p (a:real) (b:real). FINITE (IMAGE X (p_space p)) /\ FINITE (IMAGE Y (p_space p)) /\
(real_random_variable X p) /\ (real_random_variable Y p) 
/\ (expectation p X <> PosInf) /\ (expectation p X <> NegInf) 
/\ (expectation p Y <> PosInf) /\ (expectation p Y <> NegInf) 
==> (expectation p (\x. (Normal a) * (X x) + (Normal b) * (Y x)) = 
     (Normal a) * expectation p X + (Normal b) * expectation p Y)`;

e(RW_TAC std_ss []);
e(KNOW_TAC(--` integrable p X `--));
e(FULL_SIMP_TAC real_ss [integrable_def,real_random_variable_def,prob_space_def, p_space_def,events_def]);
e(FULL_SIMP_TAC std_ss [expectation_def,integral_def]);
e(RW_TAC std_ss []);
e(Cases_on `pos_fn_integral p (fn_minus X) = PosInf`);
e(FULL_SIMP_TAC std_ss []);
e(METIS_TAC [extreal_sub_def]);
e(METIS_TAC [extreal_sub_y_not_infty]);
e(Cases_on `pos_fn_integral p (fn_plus X) = NegInf`);
e(FULL_SIMP_TAC std_ss []);
e(METIS_TAC [extreal_sub_def]);
e(METIS_TAC [extreal_sub_x_not_infty]);
e(RW_TAC std_ss []);
e(KNOW_TAC(--` integrable p Y `--));
e(FULL_SIMP_TAC real_ss [integrable_def,real_random_variable_def,prob_space_def, p_space_def,events_def]);
e(FULL_SIMP_TAC std_ss [expectation_def,integral_def]);
e(RW_TAC std_ss []);
e(Cases_on `pos_fn_integral p (fn_minus Y) = PosInf`);
e(FULL_SIMP_TAC std_ss []);
e(METIS_TAC [extreal_sub_def]);
e(METIS_TAC [extreal_sub_y_not_infty]);
e(Cases_on `pos_fn_integral p (fn_plus Y) = NegInf`);
e(FULL_SIMP_TAC std_ss []);
e(METIS_TAC [extreal_sub_def]);
e(METIS_TAC [extreal_sub_x_not_infty]);
e(RW_TAC std_ss []);
e(FULL_SIMP_TAC real_ss [expectation_def,real_random_variable_def,prob_space_def, p_space_def,events_def]);
e((MP_TAC o Q.SPECL [`p`,`X`,`a`]) integral_cmul);
e(RW_TAC std_ss []);
e((MP_TAC o Q.SPECL [`p`,`Y`,`b`]) integral_cmul);
e(RW_TAC std_ss []);
e((MP_TAC o Q.SPECL [`p`,` (\x. Normal a * X x)`,`(\x. Normal b * Y x)`]) integral_add);
e(RW_TAC std_ss []);
e(METIS_TAC [integrable_cmul]);

val EXPEC_FN_LINEAR = top_thm(); drop();



g `! p (c:real). (prob_space p) ==> (integral p (\x. Normal c) = Normal c)`;

e(RW_TAC std_ss [prob_space_def]);
e((MP_TAC o Q.SPECL [`p`,`(\x. Normal c)`]) integral_mspace);
e(RW_TAC std_ss []);
e(`(m_space p IN measurable_sets p)` by FULL_SIMP_TAC real_ss [MEASURE_SPACE_MSPACE_MEASURABLE,prob_space_def]);
e(FULL_SIMP_TAC real_ss [integral_cmul_indicator,GSYM prob_def,PROB_UNIV,GSYM prob_space_def,GSYM p_space_def]);

val INTEGRAL_RV_CONST = top_thm();drop();


g `!X p (a:real) (c:real). FINITE (IMAGE X (p_space p)) /\
(real_random_variable X p) /\ (expectation p X <> PosInf) /\ (expectation p X <> NegInf) /\ (prob_space p) 
==> (expectation p (\x. (Normal a) * (X x) + Normal c) =  (Normal a) * expectation p X + Normal c)`;

e(RW_TAC std_ss []);
e(KNOW_TAC(--` integrable p X `--));
e(FULL_SIMP_TAC real_ss [integrable_def,real_random_variable_def,prob_space_def, p_space_def,events_def]);
e(FULL_SIMP_TAC std_ss [expectation_def,integral_def]);
e(RW_TAC std_ss []);
e(Cases_on `pos_fn_integral p (fn_minus X) = PosInf`);
e(FULL_SIMP_TAC std_ss []);
e(METIS_TAC [extreal_sub_def]);
e(METIS_TAC [extreal_sub_y_not_infty]);
e(Cases_on `pos_fn_integral p (fn_plus X) = NegInf`);
e(FULL_SIMP_TAC std_ss []);
e(METIS_TAC [extreal_sub_def]);
e(METIS_TAC [extreal_sub_x_not_infty]);
e(RW_TAC std_ss []);
e(FULL_SIMP_TAC real_ss [expectation_def,real_random_variable_def,prob_space_def, p_space_def,events_def]);
e((MP_TAC o Q.SPECL [`p`,`X`,`a`]) integral_cmul);
e(RW_TAC std_ss []);
e((MP_TAC o Q.SPECL [`p`,`c`]) integrable_const);
e(RW_TAC std_ss []);
e((MP_TAC o Q.SPECL [`p`,` (\x. Normal a * X x)`,`(\x. Normal c)`]) integral_add);
e(RW_TAC std_ss []);
e((MP_TAC o Q.SPECL [`p`,`X`,`a`]) integrable_cmul);
e(RW_TAC std_ss []);
e((MP_TAC o Q.SPECL [`p`,`c`]) INTEGRAL_RV_CONST);
e(RW_TAC std_ss []);
e(FULL_SIMP_TAC std_ss [prob_space_def,p_space_def]);

val EXPEC_LINEAR_CONST = top_thm(); drop();

g `!p (c:real). (prob_space p) ==> (expectation p (\x. Normal c) = Normal c)`;

e(RW_TAC std_ss [expectation_def, prob_space_def]);
e((MP_TAC o Q.SPECL [`p`,`(\x. Normal c)`]) integral_mspace);
e(RW_TAC std_ss []);
e(`(m_space p IN measurable_sets p)` by FULL_SIMP_TAC real_ss [MEASURE_SPACE_MSPACE_MEASURABLE,prob_space_def]);
e(FULL_SIMP_TAC real_ss [integral_cmul_indicator,GSYM prob_def,PROB_UNIV,GSYM prob_space_def,GSYM p_space_def]);

val EXPEC_RV_CONST = top_thm();drop();


