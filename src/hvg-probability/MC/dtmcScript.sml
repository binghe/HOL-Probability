(* ========================================================================= *)
(*                                                                           *)
(*               Basic Discrete-time Markov Chain Library                    *)
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
(*=================================================================*)
(* The indices of the definitions and theorems refer to the order  *)
(* that they presented in the paper.                               *)
(*=================================================================*)
val () = app load ["bossLib", "metisLib", "arithmeticTheory", "pred_setTheory", "realLib", 
        "seqTheory", "pairTheory", "combinTheory", "listTheory", "rich_listTheory", 
        "transcTheory", "numLib", "prim_recTheory", "probabilityTheory", "cond_probTheory",
        "extra_pred_setTools", "dep_rewrite", "setUsefulTheory"];

set_trace "Unicode" 0;

open HolKernel Parse boolLib bossLib metisLib numLib combinTheory subtypeTheory
     pred_setTheory measureTheory listTheory rich_listTheory numLib seqTheory
     extra_pred_setTheory arithmeticTheory realTheory realLib pairTheory extra_pred_setTools
     transcTheory prim_recTheory extrealTheory probabilityTheory cond_probTheory 
     dep_rewrite setUsefulTheory;
	  
(*val _ = new_theory "dtmcBasic";*)

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
val INTER_ASSOC = GSYM INTER_ASSOC;
val UNION_ASSOC = GSYM UNION_ASSOC;

fun MP_RW_TAC th g =
  let
    val sel = lhs o snd o strip_forall o snd o dest_imp
    val PART_MATCH = PART_MATCH sel (SPEC_ALL th)
    val th = ref TRUTH
    val _ =
      find_term (fn t => (th := PART_MATCH t; true) handle _ => false) (snd g)
  in
   (SUBGOAL_THEN (lhand (concl (!th))) (fn x =>
     REWRITE_TAC[MP (!th) x] ++ STRIP_ASSUME_TAC x)) g
end;

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
(* ------------------------------------------------------------------------- *)
(* Some definitions in condition probability theorems                        *)
(* ------------------------------------------------------------------------- *)	
val joint_pmf_def = Define
   `joint_pmf p X Y = (\(A :'a -> bool),(B :'a -> bool). 
     prob p (PREIMAGE X A INTER PREIMAGE Y B INTER p_space p))`;

val cond_pmf_def = Define
   `cond_pmf p X Y = 
        (\((A :'a -> bool),(B :'a -> bool)).
               joint_pmf p X Y (A,B) / distribution p Y B)`;

(* ------------------------------------------------------------------------- *)
(* Definition 2: Transition Probability                                      *)
(* ------------------------------------------------------------------------- *)
val Trans_def = Define `
    Trans X p s t n i j = 
    if i IN space s /\ j IN space s then
         if (n = (0:num)) then if (i = j) then (1:real) else 0
         else cond_prob p (PREIMAGE (X (t + n)) {j} INTER p_space p)
    		     (PREIMAGE (X t) {i} INTER p_space p)
    else 0`;

val Increasing_seq_def = Define `
    Increasing_seq (t:num -> num) = !i (j:num). i < j ==> t i < t j`;
    
(* ------------------------------------------------------------------------- *)
(* Important definitions in DTMC theorems                                    *)
(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)
(* Definition 1: Markov Property                                             *)
(* ------------------------------------------------------------------------- *)		
val mc_property_def = Define `
    mc_property X p s =
     (!(t:num). random_variable (X t) p s) /\ 
     (!f t (n:num). 
         Increasing_seq t /\ 
         (prob p (BIGINTER (IMAGE (\k. PREIMAGE (X (t k)) {f k} INTER p_space p) 
                                       (count n))) <> 0) ==>
         (cond_pmf p (X (t (n + 1))) (X (t n)) ({f (n + 1)}, {f n}) =
          cond_prob p (PREIMAGE (X (t (n + 1))) {f (n + 1)} INTER p_space p)
                      (PREIMAGE (X (t n)) {f n} INTER p_space p INTER
                       BIGINTER (IMAGE (\k. PREIMAGE (X (t k)) {f k} INTER p_space p) 
                                       (count n)))))`;

(* ------------------------------------------------------------------------- *)
(* Definition 3: DTMC                                                        *)
(* --------------------------------------------------------------------------*)
val dtmc_def = Define `
    dtmc X p s Linit Ltrans = 
    (mc_property X p s) /\ (!x. x IN space s ==> {x} IN subsets s) /\ 
    (!(i:'b). i IN space s ==> (Linit i = distribution p (X (0:num)) {i})) /\
    (!(i:'b) (j:'b) (t:num). distribution p (X t) {i} <> 0 ==> 
           (Ltrans t i j = Trans X p s t 1 i j))`;

(* ------------------------------------------------------------------------- *)
(* Definition 4: Time-homogeneous DTMC                                       *)
(* --------------------------------------------------------------------------*)
val th_dtmc_def = Define `
    th_dtmc X p s Linit Ltrans =
    dtmc X p s Linit Ltrans /\ FINITE (space s) /\ 
    (!t t' i j. distribution p (X t) {i} <> 0 /\ distribution p (X t') {i} <> 0 ==>
    	(Trans X p s t 1 i j = Trans X p s t' 1 i j))`;

val stationary_distribution_def = Define `
    stationary_distribution p X f s =
        (SIGMA (\k. f k) (space s) = 1) /\ 
	!i. i IN space s ==> (0 <= f i) /\ 
	(!(t:num). f i = SIGMA (\k. (f k) * Trans X p s t 1 k i) (space s))`;
	
val detailed_balance_equations_def = Define `
    detailed_balance_equations f X p s =
    !(i:'b) j (t:num).  (f i * Trans X p s t 1 i j = f j * Trans X p s t 1 j i)`;

val stationary_pmf_def = Define `
    stationary_pmf X p s = 
        !f t w n. random_variable (X t) p s /\
    (prob p (BIGINTER (IMAGE (\k. (PREIMAGE (X (w + k)) {f k} INTER p_space p)) 
    	(count n))) =
     prob p (BIGINTER (IMAGE (\k. (PREIMAGE (X (t + k)) {f k} INTER p_space p)) 
        (count n))))`;

val rmc_def = Define `
    rmc (X:num -> 'a -> 'b) p s Linit Ltrans = th_dtmc X p s Linit Ltrans /\ 
    (!(t:num). detailed_balance_equations 
    	(\(i:'b). prob p (PREIMAGE (X t) {i} INTER p_space p)) X p s)`;
                       
(* ------------------------------------------------------------------------- *)
(* Some theorems in pred_setTheory have to be loaded again                   *)
(* ------------------------------------------------------------------------- *)	
val BIGINTER_SING = store_thm
("BIGINTER_SING",
 ``!P. BIGINTER {P} = P``,
  SIMP_TAC bool_ss [EXTENSION, IN_BIGINTER, IN_SING] THEN
  SIMP_TAC bool_ss [GSYM EXTENSION]);

val BIGINTER_UNION = store_thm
("BIGINTER_UNION",
 ``!s1 s2. BIGINTER (s1 UNION s2) = BIGINTER s1 INTER BIGINTER s2``,
 SIMP_TAC bool_ss [IN_BIGINTER, IN_UNION, IN_INTER, EXTENSION] THEN PROVE_TAC []);  

val BIGINTER_EMPTY = Q.store_thm
("BIGINTER_EMPTY",
 `BIGINTER {} = UNIV`,
  REWRITE_TAC [EXTENSION, IN_BIGINTER, NOT_IN_EMPTY, IN_UNIV]);
  
val BIGUNION_SING = Q.store_thm
("BIGUNION_SING",
 `!x. BIGUNION {x} = x`,
  SIMP_TAC bool_ss [EXTENSION, IN_BIGUNION, IN_INSERT, NOT_IN_EMPTY] THEN
  SIMP_TAC bool_ss [GSYM EXTENSION]);  

val BIGINTER_INSERT = Q.store_thm
("BIGINTER_INSERT",
 `!P B. BIGINTER (P INSERT B) = P INTER BIGINTER B`,
  REPEAT GEN_TAC THEN CONV_TAC (REWR_CONV EXTENSION) THEN
  SIMP_TAC bool_ss [IN_BIGINTER, IN_INSERT, IN_INTER, DISJ_IMP_THM,
                    FORALL_AND_THM]);  
                    
(* ------------------------------------------------------------------------- *)
(* Some basic theorems related to setTheory                                  *)
(* ------------------------------------------------------------------------- *)	
val NOTIN_SPACE_EVENTS = store_thm
  ("NOTIN_SPACE_EVENTS",
  ``!X p s i t. random_variable (X t) p s /\ i NOTIN space s ==>
    (PREIMAGE (X t) {i} INTER p_space p = {})``,
    PSET_TAC [random_variable_def, IN_MEASURABLE, PREIMAGE_def, 
    	space_def, subsets_def, EXTENSION]
 ++ Cases_on `x NOTIN p_space p` >> RW_TAC std_ss []
 ++ RW_TAC std_ss []
 ++ SPOSE_NOT_THEN STRIP_ASSUME_TAC
 ++ METIS_TAC []); 
  
val DTMC_EVENTS = store_thm
  ("DTMC_EVENTS",
  ``!(X:num -> 'a -> 'c) p s Linit Ltrans j t. 
        dtmc X p s Linit Ltrans ==> (PREIMAGE (X t) {j} INTER p_space p) IN events p``,
    RW_TAC std_ss [dtmc_def, mc_property_def]
 ++ Cases_on `j NOTIN space s`
 >> (DEP_REWRITE_TAC [NOTIN_SPACE_EVENTS,EVENTS_EMPTY]
    ++ RW_TAC std_ss []
    >> (Q.EXISTS_TAC `s` ++ RW_TAC std_ss [])
    ++ PSET_TAC [random_variable_def, IN_MEASURABLE, space_def, subsets_def])
 ++ PSET_TAC [random_variable_def, IN_MEASURABLE, space_def, subsets_def]);
         
val EVENTS_BIGINTER = store_thm
  ("EVENTS_BIGINTER",
  ``!p f n. prob_space p /\ (f IN ((count (SUC n)) -> events p)) ==>
    BIGINTER (IMAGE (\k. f k) (count (SUC n))) IN events p``,
    RW_TAC std_ss [IN_FUNSET, IN_COUNT]    
 ++ Induct_on `n` >> RW_TAC std_ss [IN_FUNSET, IN_COUNT, COUNT_ONE, IMAGE_SING, BIGINTER_SING]
 ++ RW_TAC std_ss [IN_FUNSET, IN_COUNT] 
 ++ `count (SUC (SUC n)) = (SUC n) INSERT count (SUC n)` by RW_TAC std_ss [COUNT_SUC]
 ++ POP_ORW ++ RW_TAC std_ss [IMAGE_INSERT, BIGINTER_INSERT]
 ++ `!k. k <= n ==> f k IN events p` by RW_TAC arith_ss []
 ++ `f (SUC n) IN events p` by RW_TAC std_ss []
 ++ FULL_SIMP_TAC arith_ss [IN_FUNSET, IN_COUNT, EVENTS_INTER]);   
  
(* ------------------------------------------------------------------------- *)
(* Some basic theorems related to limTheory                                  *)
(* ------------------------------------------------------------------------- *)	
val TEND2LIM = store_thm 
  ("TEND2LIM",
  ``!f x. (f --> x) ==> (lim f = x)``,
	RW_TAC std_ss [lim] THEN
	SELECT_ELIM_TAC THEN
	RW_TAC std_ss [] THENL
	[PROVE_TAC [], PROVE_TAC [SEQ_UNIQ]]);

val LIM_MUL = store_thm
  ("LIM_MUL",
  ``!x x0 y y0. (x --> x0) /\ (y --> y0) ==> 
           (lim (\n. x n * y n) = x0 * y0)``,
    REPEAT GEN_TAC THEN REPEAT STRIP_TAC THEN
    KNOW_TAC ``(\n. x n * y n) --> (x0 * y0)`` THEN1
        FULL_SIMP_TAC std_ss [SEQ_MUL] THEN
    RW_TAC std_ss [TEND2LIM]);

val LIM_ADD = store_thm
  ("LIM_ADD",
  ``!x x0 y y0. (x --> x0) /\ (y --> y0) ==> 
           (lim (\n. x n + y n) = x0 + y0)``,
    REPEAT GEN_TAC THEN REPEAT STRIP_TAC THEN
    KNOW_TAC ``(\n. x n + y n) --> (x0 + y0)`` THEN1
        FULL_SIMP_TAC std_ss [SEQ_ADD] THEN
    RW_TAC std_ss [TEND2LIM]);

val LIM_MUL_CONST = store_thm
  ("LIM_MUL_CONST",
  ``!f l k. (f --> l) ==> 
    (lim (\n. f n * k) = l * k)``,
    REPEAT GEN_TAC THEN REPEAT STRIP_TAC THEN
    KNOW_TAC ``(\n. k) --> k`` THEN1
        FULL_SIMP_TAC std_ss [SEQ_CONST] THEN
    RW_TAC std_ss [LIM_MUL]);

val LIM_ADD_CONST = store_thm
  ("LIM_ADD_CONST",
  ``!f l k. (f --> l) ==> 
    (lim (\n. f n + k) = l + k)``,
    REPEAT GEN_TAC THEN REPEAT STRIP_TAC THEN
    KNOW_TAC ``(\n. k) --> k`` THEN1
        FULL_SIMP_TAC std_ss [SEQ_CONST] THEN
    RW_TAC std_ss [LIM_ADD]);

val LIM_CONST = store_thm
  ("LIM_CONST",
  ``!k. (lim (\n. k) = k)``,
    GEN_TAC THEN
    KNOW_TAC ``(\n. k) --> k`` THEN1
        FULL_SIMP_TAC std_ss [SEQ_CONST] THEN
    FULL_SIMP_TAC std_ss [TEND2LIM]);

val LIM2TEND = store_thm
  ("LIM2TEND",
  ``!f x. (?x. f --> x) ==> 
     ((lim f = x) ==> (f --> x))``,
    RW_TAC std_ss [lim] THEN
    SELECT_ELIM_TAC THEN
    PROVE_TAC []);
    
val LIM_FN_EQ_LIM_FSUCN = store_thm 
  ("LIM_FN_EQ_LIM_FSUCN",
  ``!f. lim (\ (n:num). f (SUC n)) = lim (\(n:num). f n)``,
    REPEAT STRIP_TAC 
 ++ Know `!l. (\(n:num). (f:num -> real) n) --> l = (\n. f (SUC n)) --> l` 
 >> (`(\(n:num). (f:num -> real) (SUC n)) = (\n. (\n. f n) (SUC n))` by RW_TAC std_ss []
    ++ ONCE_ASM_REWRITE_TAC [] ++ METIS_TAC [SEQ_SUC]) ++ RW_TAC std_ss [lim]);     	
 	
(* ------------------------------------------------------------------------- *)
(*  Some basic theorems related to random variables properties               *)
(* ------------------------------------------------------------------------- *)	
val PROB_SUBSET_ZERO = prove
  (``!p s t. prob_space p /\ s IN events p /\ t IN events p /\ 
	s SUBSET t /\ (prob p t = 0) ==> (prob p s = 0)``,
    RW_TAC std_ss []
 ++ MATCH_MP_TAC extra_realTheory.REAL_LE_EQ
 ++ RW_TAC std_ss []
 >> (POP_ASSUM (MP_TAC o GSYM)
    ++ RW_TAC std_ss []
    ++ MATCH_MP_TAC PROB_INCREASING
    ++ RW_TAC std_ss [])
 ++ METIS_TAC [PROB_POSITIVE]);
 
val COND_PMF_EQ_COND_PROB = store_thm
  ("COND_PMF_EQ_COND_PROB",
   ``!p X i j s m n. 
    cond_pmf p (X m) (X n) ({j},{i}) = 
    cond_prob p (PREIMAGE (X m) {j} INTER (p_space p))
                     (PREIMAGE (X n) {i} INTER (p_space p))``,
   RW_TAC std_ss [cond_pmf_def, cond_prob_def, joint_pmf_def, distribution_def] THEN
   `PREIMAGE (X m) {j} INTER PREIMAGE (X n) {i} INTER p_space p = 
    PREIMAGE (X m) {j} INTER p_space p INTER (PREIMAGE (X n) {i} INTER p_space p)`
         by METIS_TAC [GSYM THREE_SETS_INTER] THEN FULL_SIMP_TAC std_ss []);

val COND_PROB_DISJOINT_ZERO = prove
  (``!A B p. 
  	prob_space p /\ A IN events p /\ B IN events p /\ DISJOINT A B ==>
	(cond_prob p A B = 0)``,
    PSET_TAC [cond_prob_def, PROB_EMPTY, REAL_DIV_LZERO]);
             
val DISJOINT_PROC_INTER = store_thm
  ("DISJOINT_PROC_INTER",
  ``!X p (t:num) i j. i <> j ==>
         (DISJOINT (PREIMAGE (X t) {i} INTER p_space p) (PREIMAGE (X t) {j} INTER p_space p))``,
     PSET_TAC [PREIMAGE_def, IN_SING, EXTENSION] ++ METIS_TAC []);

val BIGUNION_PREIMAGEX_IS_PSPACE = store_thm 
  ("BIGUNION_PREIMAGEX_IS_PSPACE",
  ``!X p s. FINITE (space s) /\ (!(t:num). random_variable (X t) p s) /\
           (!i. i IN space s ==> {i} IN subsets s) ==>
           !t. BIGUNION (IMAGE (\x. PREIMAGE (X t) {x} INTER p_space p) (space s)) = p_space p``,
    PSET_TAC [EXTENSION, IN_BIGUNION_IMAGE, IN_PREIMAGE, IN_SING, 
        IN_MEASURABLE,random_variable_def,IN_FUNSET,space_def]
 ++ EQ_TAC >> RW_TAC std_ss [] ++ RW_TAC std_ss []);
 
val SUM_PMF_ONE = store_thm 
  ("SUM_PMF_ONE",
  ``!X p s t. (!(t:num). random_variable (X t) p s) /\ FINITE (space s) /\
	(!(x:'b). x IN space s ==> {x} IN subsets s) ==> 
	(SIGMA (\(k:'b). distribution p (X t) {k}) (space s) = 1)``,
    RW_TAC std_ss [distribution_def]
 ++ `!(x:'b). x IN space s ==> (PREIMAGE (X t) {x} INTER p_space p) IN events p`
        by PSET_TAC [random_variable_def, IN_MEASURABLE, space_def, subsets_def]
 ++ (MP_TAC o Q.SPECL [`X`, `p`, `s`]) BIGUNION_PREIMAGEX_IS_PSPACE 
 ++ RW_TAC std_ss []        
 ++ (MP_TAC o GSYM o Q.SPECL [`space s`, `p`, 
 	`(\(x:'b). PREIMAGE (X (t:num)) {x} INTER p_space p)`,
        `p_space p`]) PROB_FINITE_ADDITIVE ++ RW_TAC std_ss [] 
 ++ FULL_SIMP_TAC std_ss [random_variable_def, DISJOINT_PROC_INTER, o_DEF, PROB_UNIV]);
 
val TOTAL_PROB_EXA = store_thm
  ("TOTAL_PROB_EXA",
   ``!A B p s. (prob_space p) /\ (A IN events p) /\ FINITE s /\
        (!x. x IN s ==> B x IN events p) /\
        (!a b. a IN s /\ b IN s /\ a <> b ==> DISJOINT (B a) (B b)) /\ 
	(BIGUNION (IMAGE B s) = p_space p) ==>
        (prob p A = SIGMA (\i. (prob p A) * (cond_prob p (B i) A)) s)``,
    RW_TAC std_ss [] 
 ++ Know `SIGMA (\i. prob p A * cond_prob p (B i) A) s =
	  SIGMA (\i. prob p (B i) * cond_prob p A (B i)) s`
 >> (MATCH_MP_TAC REAL_SUM_IMAGE_EQ ++ RW_TAC std_ss []
    ++ Cases_on `prob p A = 0`
    >> RW_TAC std_ss [REAL_MUL_LZERO, COND_PROB_INTER_ZERO, REAL_MUL_RZERO] 
    ++ Cases_on `prob p (B x) = 0`
    >> RW_TAC std_ss [REAL_MUL_LZERO, COND_PROB_INTER_ZERO, REAL_MUL_RZERO]
    ++ RW_TAC std_ss [cond_prob_def, REAL_DIV_LMUL, INTER_COMM]) 
 ++ RW_TAC std_ss [TOTAL_PROB_SIGMA]);

val RV_COND_PROB = store_thm
  ("RV_COND_PROB",
  ``!X i j Linit Ltrans p s t.
	(!t. random_variable (X t) p s) /\ i IN space s /\ 
	(0 < distribution p (X t) {i}) ==> 
	(!x. x IN space s ==>
		(cond_pmf p (X (t + 1)) (X t) ({j},{x}) * 
		cond_pmf p (X t) (X (t:num)) ({x},{i}) =
		if x = i then  cond_pmf p (X (t + 1)) (X t) ({j},{i}) else 0))``,
    RW_TAC std_ss [distribution_def]
 ++ `cond_pmf p (X (t:num)) (X t) ({(i:'b)},{i}) = 1`
	by PSET_TAC [cond_pmf_def, joint_pmf_def, INTER_IDEMPOT, distribution_def, 
	        REAL_LT_LE, REAL_DIV_REFL]
 ++ RW_TAC std_ss [REAL_MUL_RID]
 ++ `PREIMAGE (X t) {x} INTER PREIMAGE (X t) {i} = {}` 
 	by (PSET_TAC [PREIMAGE_def, IN_INTER, EXTENSION] ++ METIS_TAC [])
 ++ `prob_space p` by PSET_TAC [random_variable_def]
 ++ RW_TAC std_ss [cond_pmf_def, joint_pmf_def, INTER_EMPTY, EVENTS_EMPTY, 
        PROB_EMPTY, REAL_DIV_LZERO, REAL_MUL_RZERO]);

val RV_NON_EMPTY_SPACE = store_thm
  ("RV_NON_EMPTY_SPACE",
  ``!X p s. random_variable X p s ==> space s <> {}``,
    PSET_TAC [random_variable_def, IN_MEASURABLE, space_def, subsets_def, IN_FUNSET]
 ++ `p_space p <> {}` by (SPOSE_NOT_THEN STRIP_ASSUME_TAC 
 		++ `prob p (p_space p) = 0` by METIS_TAC [PROB_EMPTY]
 		++ METIS_TAC [PROB_UNIV, REAL_LT_01, REAL_LT_IMP_NE])
 ++ PSET_TAC [GSYM MEMBER_NOT_EMPTY] ++ NTAC 2 (POP_ASSUM MP_TAC)
 ++ POP_ASSUM (MP_TAC o Q.SPEC `x`) ++ RW_TAC std_ss []
 ++ FULL_SIMP_TAC std_ss [] ++ Q.EXISTS_TAC `X x` ++ RW_TAC std_ss []);
 
val COND_INTER_MUL_SIGMA = store_thm
  ("COND_INTER_MUL_SIGMA",
  ``!A B C p s.  (prob_space p) /\ A IN events p /\ C IN events p /\ 
       (!x. x IN s ==>  B x IN events p) /\ FINITE s /\
       (!a b. a IN s /\ b IN s /\ ~(a = b) ==> DISJOINT (B a) (B b)) /\
       (BIGUNION (IMAGE B s) INTER p_space p = p_space p) ==> 
         (cond_prob p A C = 
          SIGMA (\i. cond_prob p A ((B i) INTER C) * cond_prob p (B i) C) s)``,
    REPEAT STRIP_TAC ++ RW_TAC std_ss [INTER_COMM]
 ++ `!A B. A IN events p /\ B IN events p ==> (cond_prob p A B = cond_prob p (B INTER A) B)`
 	by METIS_TAC [cond_prob_def, INTER_COMM, INTER_ASSOC, INTER_IDEMPOT]
 ++ `(SIGMA (\(i:'b). cond_prob p A (C INTER B i) * cond_prob p (B i) C) s) =
            (SIGMA (\i. cond_prob p A (C INTER B i) * cond_prob p (C INTER (B i)) C) s)`
        by (MATCH_MP_TAC REAL_SUM_IMAGE_EQ ++ RW_TAC std_ss [EVENTS_INTER, GSYM COND_PROB_MUL_RULE])
 ++ POP_ORW ++ POP_ASSUM K_TAC
 ++ Cases_on `prob p C = 0` 
 >> (RW_TAC std_ss [COND_PROB_ZERO] 
    ++ (MP_TAC o GSYM o Q.ISPEC `s:'b -> bool`) REAL_SUM_IMAGE_0 ++ RW_TAC std_ss []
    ++ POP_ORW ++ MATCH_MP_TAC REAL_SUM_IMAGE_EQ 
    ++ RW_TAC std_ss [EVENTS_INTER, COND_PROB_ZERO, REAL_MUL_RZERO])
 ++ Suff `(cond_prob p A C * prob p C =
    SIGMA (\i. cond_prob p A (C INTER B i) * cond_prob p (C INTER B i) C) s * prob p C)`
 >> RW_TAC std_ss [REAL_EQ_RMUL] ++ RW_TAC std_ss [REAL_MUL_COMM, GSYM COND_PROB_MUL_RULE]
 ++ `prob p C * SIGMA (\i. cond_prob p A (C INTER B i) * cond_prob p (C INTER B i) C) s =
     SIGMA (\i. prob p C * (cond_prob p A (C INTER B i) * cond_prob p (C INTER B i) C)) 
     (s:'b -> bool)` by RW_TAC std_ss [(UNDISCH o Q.ISPEC `s:'b->bool` o GSYM) REAL_SUM_IMAGE_CMUL]
 ++ POP_ORW ++ `(A INTER C) IN events p` by RW_TAC std_ss [EVENTS_INTER]    
 ++ `!(a:real) b c. a * (b * c) = b * (a * c)` by REAL_ARITH_TAC ++ POP_ORW
 ++ `!A B. A INTER B INTER A = A INTER B` by METIS_TAC [INTER_ASSOC, INTER_COMM, INTER_IDEMPOT]
 ++ `SIGMA (\i. cond_prob p A (C INTER B i) * (prob p C * cond_prob p (C INTER B i) C)) s =
     SIGMA (\i. cond_prob p A (C INTER B i) * prob p (C INTER B i)) (s:'b -> bool)`
        by (MATCH_MP_TAC REAL_SUM_IMAGE_EQ ++ RW_TAC std_ss [EVENTS_INTER, GSYM COND_PROB_MUL_RULE])
 ++ POP_ORW 
 ++ `SIGMA (\i. cond_prob p A (C INTER B i) * prob p (C INTER B i)) s =
     SIGMA (\i. prob p (A INTER C INTER B i)) (s:'b -> bool)` 
     by (MATCH_MP_TAC REAL_SUM_IMAGE_EQ 
        ++ RW_TAC std_ss [REAL_MUL_COMM, EVENTS_INTER, GSYM COND_PROB_MUL_RULE, INTER_ASSOC])
 ++ POP_ORW ++ MATCH_MP_TAC PROB_REAL_SUM_IMAGE_FN ++ RW_TAC std_ss [EVENTS_INTER]);

val SIGMA_ONE_NON_ZERO_TERM = store_thm
  ("SIGMA_ONE_NON_ZERO_TERM",
  ``!s k x. FINITE s ==> 
	(SIGMA (\(m:'b). if m = k then x else (0:real)) s = 
	if (k IN s) then x else (0:real))``,
   Suff `!s. FINITE s ==> 
	(\s. !k x. (SIGMA (\(m:'b). if m = k then (x:real) else 0) s = 
	if (k IN s) then x else 0)) s` 
 >> METIS_TAC [] ++ MATCH_MP_TAC FINITE_INDUCT 
 ++ RW_TAC std_ss [NOT_IN_EMPTY, REAL_SUM_IMAGE_THM] 
 ++ `s DELETE e = (s:'b -> bool)` by FULL_SIMP_TAC std_ss [DELETE_NON_ELEMENT]
 ++ RW_TAC std_ss [REAL_SUM_IMAGE_THM]
 << [FULL_SIMP_TAC std_ss [],
     FULL_SIMP_TAC std_ss [],
     RW_TAC std_ss [REAL_ADD_RID],
     FULL_SIMP_TAC std_ss [COMPONENT],
     RW_TAC std_ss [REAL_ADD_LID],
     PSET_TAC [],
     PSET_TAC [],
     RW_TAC std_ss [REAL_ADD_RID]]);  

val SWAP_SIGMA_SIGMA = store_thm
  ("SWAP_SIGMA_SIGMA",
  ``!s (f:'a -> 'a -> real). FINITE s ==> 
	(SIGMA (\k. SIGMA (\h. f k h) s) s = SIGMA (\h. SIGMA (\k. f k h) s) s)``,
    Suff `!s. FINITE s ==> (\s. !(f:'a -> 'a -> real). 
        (SIGMA (\k. SIGMA (\h. f k h) s) s = SIGMA (\h. SIGMA (\k. f k h) s) s)) s` 
 >> METIS_TAC [] ++ MATCH_MP_TAC FINITE_INDUCT ++ RW_TAC std_ss [REAL_SUM_IMAGE_THM] 
 ++ `(s DELETE e) = s` by FULL_SIMP_TAC std_ss [DELETE_NON_ELEMENT] 
 ++ `SIGMA (\h. SIGMA (\k. (f:'a -> 'a -> real) k h) (e INSERT s)) s = 
	SIGMA (\h. f e h + SIGMA (\k. f k h) s) s` 
        by (MATCH_MP_TAC REAL_SUM_IMAGE_EQ ++ RW_TAC std_ss [REAL_SUM_IMAGE_THM])
 ++ `SIGMA (\k. (f:'a -> 'a -> real) k e + SIGMA (\h. f k h) s) s = 
	SIGMA(\k. f k e) s + SIGMA (\k. SIGMA (\h. f k h) s) s` 
        by RW_TAC std_ss [REAL_SUM_IMAGE_ADD]
 ++ `SIGMA (\h. (f:'a -> 'a -> real) e h + SIGMA (\k. f k h) s) s = 
	SIGMA(\h. f e h) s + SIGMA (\h. SIGMA (\k. f k h) s) s` 
        by RW_TAC std_ss [REAL_SUM_IMAGE_ADD]
 ++ METIS_TAC [REAL_ADD_ASSOC,REAL_EQ_LADD, REAL_ADD_COMM]);

val SIGMA_SEQ = store_thm
  ("SIGMA_SEQ",
   ``!f s. (!(k:'b). k IN s ==> ?u. (\n. f n k) --> u) /\ FINITE s ==>
   (convergent (\n. SIGMA (\k. f n k) s))``,
    RW_TAC std_ss [convergent] 
 ++ Suff `!t. FINITE t ==> (\t. t SUBSET s ==>
	?l. (\n. SIGMA (\k. (f:num -> 'b -> real) n k) t) --> l) t` 
 >> METIS_TAC [SUBSET_REFL] ++ MATCH_MP_TAC FINITE_INDUCT
 ++ RW_TAC std_ss [REAL_SUM_IMAGE_THM]
 >> (Q.EXISTS_TAC `(0:real)` ++ RW_TAC std_ss [SEQ_CONST])  
 ++ `s' DELETE e = s'` by PSET_TAC [DELETE_NON_ELEMENT] ++ POP_ORW
 ++ `e IN s` by PSET_TAC [] 
 ++ POP_ASSUM_LIST (MAP_EVERY STRIP_ASSUME_TAC) 
 ++ POP_ASSUM (MP_TAC o Q.SPEC `(e:'b)`) ++ PSET_TAC []
 ++ METIS_TAC [SEQ_ADD]); 

val SIGMA_LIM = store_thm
  ("SIGMA_LIM",
  ``!f s. (!(k:'b). k IN s ==> ?u. (\n. f n k) --> u) /\ FINITE s ==>
         (lim (\n. SIGMA (\(j:'b). f n j) s) =
         SIGMA (\j. lim (\n. f n j)) s)``,
    RW_TAC std_ss [] 
 ++ Suff `!t. FINITE t ==> (\t. t SUBSET s ==>
 	(lim (\n. SIGMA (\(j:'b). f n j) t) = SIGMA (\j. lim (\n. f n j)) t)) t` 
 >> METIS_TAC [SUBSET_REFL] ++ MATCH_MP_TAC FINITE_INDUCT 
 ++ RW_TAC std_ss [REAL_SUM_IMAGE_THM] 
 >> RW_TAC std_ss [LIM_CONST] 
 ++ `s' DELETE e = s'` by PSET_TAC [DELETE_NON_ELEMENT] ++ POP_ORW 
 ++ `e IN s` by PSET_TAC [] ++ PSET_TAC [] 
 ++ `convergent (\n. SIGMA (\k. f n k) s')` by FULL_SIMP_TAC std_ss [SIGMA_SEQ]
 ++ FULL_SIMP_TAC std_ss [SEQ_LIM]
 ++ `?u. (\n. f n e) --> u` 
        by (POP_ASSUM_LIST (MAP_EVERY STRIP_ASSUME_TAC) 
           ++ POP_ASSUM (MP_TAC o Q.SPEC `(e:'b)`) ++ RW_TAC std_ss [])      
 ++ (MP_TAC o Q.SPECL [`(\n. (f:num -> 'b -> real) n e)`, `u`, 
        `(\n. SIGMA (\k. (f:num -> 'b -> real) n k) s')`, 
        `lim (\n. SIGMA (\k. (f:num -> 'b -> real) n k) s')`]) LIM_ADD 
 ++ RW_TAC std_ss [] ++ METIS_TAC [TEND2LIM]);
 
val PROB_SIGMA_ITSELF = store_thm 
  ("PROB_SIGMA_ITSELF",
  ``!X p s (t:num) i.  
        (!t. random_variable (X t) p s) /\ (FINITE (space s)) /\ (i IN (space s)) ==> 
        (prob p (PREIMAGE (X t) {i} INTER p_space p) =
        SIGMA (\k. prob p (PREIMAGE (X t) {k} INTER p_space p) *
                cond_prob p (PREIMAGE (X t) {i} INTER p_space p) 
                        (PREIMAGE (X t) {k} INTER p_space p)) (space s))``,
    REPEAT STRIP_TAC 
 ++ `prob_space p` by FULL_SIMP_TAC std_ss [random_variable_def]
 ++ Know `SIGMA (\(k:'b).
         prob (p :('a -> bool) # (('a -> bool) -> bool) # (('a -> bool) -> real)) 
                (PREIMAGE (X (t:num)) {k} INTER p_space p) *
         cond_prob p (PREIMAGE (X t) {i} INTER p_space p) 
                (PREIMAGE (X t) {k} INTER p_space p)) (space s) =
         SIGMA (\k. if k = i then prob p (PREIMAGE (X t) {k} INTER p_space p) else 0) (space s)`
 >> (MATCH_MP_TAC REAL_SUM_IMAGE_EQ ++ RW_TAC std_ss []
    >> (Cases_on `prob p (PREIMAGE (X t) {i} INTER p_space p) = 0`
       >> RW_TAC std_ss [REAL_MUL_LZERO] 
       ++ RW_TAC std_ss [cond_prob_def, REAL_DIV_LMUL, INTER_IDEMPOT])
    ++ Cases_on `prob p (PREIMAGE (X t) {x} INTER p_space p) = 0` >> RW_TAC std_ss [REAL_MUL_LZERO]
    ++ (MP_TAC o Q.SPECL [`X`, `p`, `t`, `i`, `x`]) DISJOINT_PROC_INTER ++ RW_TAC std_ss []
    ++ PSET_TAC [DISJOINT_DEF, cond_prob_def, PROB_EMPTY, EVENTS_EMPTY, REAL_DIV_LZERO, 
        REAL_MUL_RZERO]) ++ RW_TAC std_ss [SIGMA_ONE_NON_ZERO_TERM]);        		    

val EVENTS_BIGINTER_MN = store_thm
  ("EVENTS_BIGINTER_MN", 
  ``!p f m n. prob_space p /\ (m <= n) /\ 
    (!k. m <= k /\ k <= n ==> f k IN events p) ==>
    BIGINTER (IMAGE (\k. f k) (count_mn m n)) IN events p``,
    Induct_on `n` >> RW_TAC std_ss [COUNT_MN_SING, IMAGE_SING, BIGINTER_SING] 
 ++ RW_TAC std_ss [] ++ Cases_on `m = SUC n` 
 >> (RW_TAC std_ss [count_mn_def] 
    ++ KNOW_TAC ``{r | SUC n <= r /\ r <= SUC n} = {r | r = SUC n}``
    >> (PSET_TAC [EXTENSION] ++ EQ_TAC >> RW_TAC arith_ss []
       ++ RW_TAC arith_ss []) 
    ++ RW_TAC std_ss [GSPEC_EQ, IMAGE_SING, BIGINTER_SING])
 ++ `m <= n` by RW_TAC arith_ss []
 ++ `!k. m <= k /\ k <= n ==> f k IN events p` by RW_TAC arith_ss []
 ++ Cases_on `n = 0` 
 >> (RW_TAC std_ss [] ++ `m = 0` by RW_TAC arith_ss [] ++ RW_TAC std_ss []
    ++ `count_mn 0 1 = {r | r = 0} UNION {r | r = 1}` by (PSET_TAC [count_mn_def, EXTENSION]
        ++ EQ_TAC >> RW_TAC arith_ss [] ++ RW_TAC arith_ss []) ++ POP_ORW
    ++ RW_TAC std_ss [GSPEC_EQ, IMAGE_UNION, IMAGE_SING, BIGINTER_UNION, BIGINTER_SING]
    ++ `f 0 IN events p` by FULL_SIMP_TAC arith_ss []
    ++ `f 1 IN events p` by FULL_SIMP_TAC arith_ss [] ++ METIS_TAC [EVENTS_INTER])
 ++ `0 < n` by RW_TAC arith_ss []
 ++ KNOW_TAC ``count_mn m (SUC n) = (SUC n) INSERT count_mn m n``
 >> (PSET_TAC [count_mn_def, INSERT_DEF, EXTENSION] 
    ++ `(x <= SUC n) = (x < SUC n) \/ (x = SUC n)` by RW_TAC std_ss [LESS_OR_EQ]
    ++ POP_ORW ++ RW_TAC std_ss [LEFT_AND_OVER_OR] ++ EQ_TAC >> RW_TAC arith_ss []
    ++ RW_TAC arith_ss [LESS_IMP_LESS_OR_EQ]) ++ RW_TAC std_ss []
 ++ RW_TAC std_ss [IMAGE_INSERT, BIGINTER_INSERT]
 ++ `f (SUC n) IN events p` by FULL_SIMP_TAC arith_ss []
 ++ FULL_SIMP_TAC std_ss [EVENTS_INTER]);   
(* ------------------------------------------------------------------------- *)
(*              Basic time homogeneous DTMC theorems                         *)
(* ------------------------------------------------------------------------- *)	
val IMAGE_SHIFT = prove
  (``!X t n (L:'b list) p. n <> 0 ==> 
   (IMAGE (\k. PREIMAGE (X k) {(\k. EL (k - t) L) k} INTER p_space p) (count_mn t (t + n - 1)) =
     IMAGE (\k. PREIMAGE (X (t + k)) {(\k. EL k (L:'b list)) k} INTER p_space p) (count n))``,
    Induct_on `n`
 >> RW_TAC std_ss []
 ++ RW_TAC std_ss []
 ++ Cases_on `n = 0`
 >> PSET_TAC [COUNT_ONE, COUNT_MN_SING, IMAGE_SING]
 ++ `count_mn t (t + SUC n - 1) = count_mn t (t + n - 1) UNION {t + n}` 
        by (PSET_TAC [count_mn_def, EXTENSION] ++ RW_TAC arith_ss [])
 ++ POP_ORW
 ++ PSET_TAC [IMAGE_UNION, COUNT_SUC, IMAGE_INSERT, IMAGE_EMPTY]      
 ++ (MP_TAC o Q.ISPECL [`IMAGE (\k. PREIMAGE (X (t + k)) {EL k L} INTER p_space p) (count n)`,
 	`PREIMAGE (X (t + n)) {EL n (L:'b list)} INTER p_space p`]) INSERT_EQ_UNION_SING
 ++ RW_TAC std_ss []);          
                   
(* ------------------------------------------------------------------------- *)
(* Theorem 1: Joint Probability                                              *)
(* --------------------------------------------------------------------------*)
val MC_JOINT_PROB = store_thm
  ("MC_JOINT_PROB",
  ``!X p s (t:num) (n:num) (L:'b list) Linit Ltrans. 
	dtmc X p s Linit Ltrans ==>
   	(prob p (BIGINTER (IMAGE (\(k:num). PREIMAGE (X (t + k)) {EL k L} INTER p_space p)
                	(count (n + 1)))) =
    	 mulcon (0, n) (\k. (cond_pmf p (X (t + k + 1)) (X (t + k)) 
                       			({EL (k + 1) L}, {EL k L}))) * 
    	 distribution p (X t) {EL 0 L})``,
    REPEAT STRIP_TAC ++ Induct_on `n` >>
    RW_TAC std_ss [mulcon_def, BIGINTER_IMAGE_0, REAL_MUL_LID, distribution_def] 
 ++ RW_TAC std_ss [mulcon_def] 
 ++ `!(x:real) y z. x * y * z = x * z * y` by METIS_TAC [REAL_MUL_ASSOC, REAL_MUL_COMM] 
 ++ POP_ORW ++ POP_ASSUM (MP_TAC o SYM) 
 ++ RW_TAC std_ss [BIGINTER_INDUCT_LAST, COND_PMF_EQ_COND_PROB]
 ++ `PREIMAGE (X (t + (n + 1))) {EL (n + 1) L} INTER p_space p INTER
     BIGINTER (IMAGE (\k. PREIMAGE (X (t + k)) {EL k L} INTER p_space p) (count (n + 1)))
     SUBSET BIGINTER (IMAGE (\k. PREIMAGE (X (t + k)) {EL k L} INTER p_space p) (count (n + 1)))`
          by PSET_TAC [SUBSET_DEF]
 ++ `prob_space p` 
        by FULL_SIMP_TAC std_ss [th_dtmc_def, dtmc_def, mc_property_def, random_variable_def] 
 ++ Cases_on `?m. m IN count (SUC n + 1) /\ EL m L NOTIN (space s)`
 >> (PSET_TAC [IN_COUNT] 
    ++ `BIGINTER (IMAGE (\k. PREIMAGE (X (t + k)) {EL k L} INTER p_space p)
            (count (SUC n + 1))) SUBSET 
        BIGINTER (IMAGE (\k. PREIMAGE (X (t + k)) {EL k L} INTER p_space p) {m})`
        by (MATCH_MP_TAC SUBSET_BIGINTER_SUBSET
           ++ PSET_TAC [count_def, EXTENSION])
    ++ `PREIMAGE (X (t + m)) {EL m L} INTER p_space p = {}` 
    	by (MATCH_MP_TAC NOTIN_SPACE_EVENTS 
    	   ++ Q.EXISTS_TAC `s` ++ PSET_TAC [dtmc_def, mc_property_def])
    ++ Cases_on `m = n + 1` 
    >> FULL_SIMP_TAC arith_ss [IMAGE_SING, BIGINTER_SING, SUBSET_EMPTY, cond_prob_def, 
    	INTER_EMPTY, PROB_EMPTY, REAL_DIV_LZERO, REAL_MUL_RZERO]
    ++ `m < n + 1` by RW_TAC arith_ss []
    ++ `BIGINTER (IMAGE (\k. PREIMAGE (X (t + k)) {EL k L} INTER p_space p)
            (count (n + 1))) SUBSET 
        BIGINTER (IMAGE (\k. PREIMAGE (X (t + k)) {EL k L} INTER p_space p) {m})`
        by (MATCH_MP_TAC SUBSET_BIGINTER_SUBSET
           ++ PSET_TAC [count_def, EXTENSION])
    ++ POP_ASSUM MP_TAC ++ RW_TAC std_ss [IMAGE_SING, BIGINTER_SING, SUBSET_EMPTY]
    ++ FULL_SIMP_TAC arith_ss [IMAGE_SING, BIGINTER_SING, SUBSET_EMPTY, 
    	INTER_EMPTY, PROB_EMPTY, REAL_MUL_LZERO])
 ++ `!m. m <= SUC n ==> BIGINTER (IMAGE (\k. PREIMAGE (X (t + k)) {EL k L} INTER p_space p)
         	(count (m + 1))) IN events p`
    by (RW_TAC std_ss [GSYM ADD1]
       ++ `BIGINTER (IMAGE (\k. PREIMAGE (X (t + k)) {EL k L} INTER p_space p)
         	(count (SUC m))) =
           BIGINTER (IMAGE (\k. (\k. PREIMAGE (X (t + k)) {EL k L} INTER p_space p) k)
         	(count (SUC m)))` by RW_TAC std_ss [] ++ POP_ORW	
       ++ MATCH_MP_TAC EVENTS_BIGINTER ++ RW_TAC std_ss [IN_FUNSET]
       ++ METIS_TAC [IN_COUNT, DTMC_EVENTS]) 
 ++ Cases_on `n = 0` 
 >> (RW_TAC std_ss [COUNT_ONE, IMAGE_SING, BIGINTER_SING]
    ++ `count 2 = {0} UNION {1}` by (PSET_TAC [count_def, EXTENSION] ++ RW_TAC arith_ss [])
    ++ POP_ORW ++ RW_TAC std_ss [IMAGE_UNION, BIGINTER_UNION, IMAGE_SING, BIGINTER_SING]
    ++ Q.ABBREV_TAC `A = PREIMAGE (X t) {EL 0 L} INTER p_space p`
    ++ Q.ABBREV_TAC `B = PREIMAGE (X (t + 1)) {EL 1 L} INTER p_space p`
    ++ ONCE_REWRITE_TAC [INTER_COMM] ++ MATCH_MP_TAC COND_PROB_MUL_RULE
    ++ MAP_EVERY Q.UNABBREV_TAC [`A`, `B`]
    ++ RW_TAC std_ss [] ++ PROVE_TAC [DTMC_EVENTS]) 
 ++ `BIGINTER (IMAGE (\k. PREIMAGE (X (t + k)) {EL k L} INTER p_space p)
                 	(count n)) IN events p`
    by (`SUC (n - 1) = n` by RW_TAC arith_ss []
             ++ `BIGINTER (IMAGE (\k. PREIMAGE (X (t + k)) {EL k L} INTER p_space p)
         	(count n)) =
               BIGINTER (IMAGE (\k. (\k. PREIMAGE (X (t + k)) {EL k L} INTER p_space p) k)
         	(count (SUC (n - 1))))` by RW_TAC arith_ss [] ++ POP_ORW	
             ++ MATCH_MP_TAC EVENTS_BIGINTER ++ RW_TAC std_ss [IN_FUNSET]
             ++ METIS_TAC [IN_COUNT, DTMC_EVENTS])    
 ++ Cases_on `prob p (BIGINTER (IMAGE (\k. PREIMAGE (X (t + k)) {EL k L} INTER p_space p)
                 	(count n))) = 0`
 >> (`prob p (BIGINTER (IMAGE (\k. PREIMAGE (X (t + k)) {EL k L} INTER p_space p)
            (count (SUC n + 1)))) = 0` 
       by (MATCH_MP_TAC PROB_SUBSET_ZERO
 	  ++ Q.EXISTS_TAC `BIGINTER (IMAGE (\k. PREIMAGE (X (t + k)) {EL k L} INTER 
 			p_space p) (count n))` ++ RW_TAC std_ss [ADD]
          ++ MATCH_MP_TAC SUBSET_BIGINTER_SUBSET
          ++ MATCH_MP_TAC COUNT_SUBSET ++ RW_TAC arith_ss []) ++ POP_ORW
     ++ Suff `prob p (BIGINTER (IMAGE (\k. PREIMAGE (X (t + k)) {EL k L} INTER p_space p)
            (count (n + 1)))) = 0` 
     >> METIS_TAC [REAL_MUL_LZERO]
     ++ MATCH_MP_TAC PROB_SUBSET_ZERO
     ++ Q.EXISTS_TAC `BIGINTER (IMAGE (\k. PREIMAGE (X (t + k)) {EL k L} INTER 
 			p_space p) (count n))` ++ RW_TAC std_ss [ADD]
     ++ MATCH_MP_TAC SUBSET_BIGINTER_SUBSET
     ++ MATCH_MP_TAC COUNT_SUBSET ++ RW_TAC arith_ss []) 
 ++ `PREIMAGE (X (t + n + 1)) {EL (n + 1) L} INTER p_space p IN events p`
 	by METIS_TAC [DTMC_EVENTS]
 ++ `count (SUC n + 1) = {n + 1} UNION count (n + 1)` 
 	by (PSET_TAC [count_def, EXTENSION] ++ RW_TAC arith_ss [])
 ++ POP_ORW ++ RW_TAC std_ss [IMAGE_UNION, BIGINTER_UNION, IMAGE_SING, BIGINTER_SING]
 ++ (MP_TAC o Q.SPECL [`p`, `PREIMAGE (X (t + (n + 1))) {EL (n + 1) (L:'b list)} INTER p_space p`,
        `BIGINTER (IMAGE (\k. PREIMAGE (X (t + k)) {EL k L} INTER p_space p) (count (n + 1)))`])
        COND_PROB_MUL_RULE ++ RW_TAC std_ss [ADD_ASSOC] 
 ++ POP_ASSUM K_TAC
 ++ `!(x:real) y z. (x = y) ==> (z * x = z * y)` by RW_TAC std_ss [] 
 ++ POP_ASSUM MATCH_MP_TAC 
 ++ (MP_TAC o Q.SPECL [`(\k. PREIMAGE (X (t + k)) {EL k (L:'b list)} INTER p_space p)`, `n`])
        BIGINTER_INDUCT_LAST 
 ++ RW_TAC std_ss [ADD1, ADD_ASSOC] 
 ++ NTAC 2 (POP_ASSUM K_TAC)
 ++ `mc_property X p s` by METIS_TAC [dtmc_def] 
 ++ FULL_SIMP_TAC std_ss [mc_property_def]
 ++ POP_ASSUM (MP_TAC o Q.SPECL [`(\k. EL k (L:'b list))`, `(\(k:num). t + k)`, `n`]) 
 ++ RW_TAC std_ss [Increasing_seq_def, IMAGE_SHIFT, COND_PMF_EQ_COND_PROB, ADD_ASSOC]);  
    
(* ------------------------------------------------------------------------- *)
(* Theorem 3: Absolute Probabilities                                         *)
(* --------------------------------------------------------------------------*)
val N_STEP_PROB_DISTRIBUTION = store_thm 
  ("N_STEP_PROB_DISTRIBUTION",
  ``!X (n:num) t (j:'b) Linit Ltrans p s.
	dtmc X p s Linit Ltrans /\ FINITE (space s) ==> 
	(distribution p (X (t + n)) {j} = 
	SIGMA (\k. (distribution p (X t) {k}) * 
		cond_pmf p (X (t + n)) (X t) ({j}, {k})) (space s))``,
    RW_TAC std_ss [distribution_def, COND_PMF_EQ_COND_PROB]
 ++ `SIGMA (\k.  prob p (PREIMAGE ((X:num -> 'a -> 'b) t) {k} INTER p_space p) *
         cond_prob p (PREIMAGE (X (t + n)) {j} INTER p_space p)
           (PREIMAGE (X t) {k} INTER p_space p)) (space s) =
     SIGMA (\k.  prob p ((\k. (PREIMAGE (X t) {k} INTER p_space p)) k) *
         cond_prob p (PREIMAGE (X (t + n)) {j} INTER p_space p)
           ((\k. (PREIMAGE (X t) {k} INTER p_space p)) k)) (space s)` by RW_TAC std_ss []
 ++ POP_ORW ++ MATCH_MP_TAC TOTAL_PROB_SIGMA ++ RW_TAC std_ss []
 << [FULL_SIMP_TAC std_ss [dtmc_def, mc_property_def, random_variable_def],
     PROVE_TAC [DTMC_EVENTS],
     PROVE_TAC [DTMC_EVENTS],
     RW_TAC std_ss [DISJOINT_PROC_INTER],
     FULL_SIMP_TAC std_ss [dtmc_def, mc_property_def, BIGUNION_PREIMAGEX_IS_PSPACE]]);

val SUM_ROW_MATRIX_EQ_ONE = store_thm 
  ("SUM_ROW_MATRIX_EQ_ONE",
  ``!X (t:num) j m Linit Ltrans p s.
	dtmc X p s Linit Ltrans /\ 0 < distribution p (X t) {j} /\ FINITE (space s) ==> 
	(SIGMA (\k. cond_pmf p (X (t + m)) (X t) ({k},{j})) (space s) = 1)``,
	
    RW_TAC std_ss [COND_PMF_EQ_COND_PROB]
 ++ `SIGMA (\k. cond_prob p (PREIMAGE (X (t + m)) {k} INTER p_space p)
           (PREIMAGE (X t) {j} INTER p_space p)) (space s) =
     SIGMA (\k. cond_prob p ((\k. (PREIMAGE (X (t + m)) {k} INTER p_space p)) k)
           (PREIMAGE (X t) {j} INTER p_space p)) (space s)` by RW_TAC std_ss [] ++ POP_ORW
 ++ MATCH_MP_TAC COND_PROB_ADDITIVE ++ RW_TAC std_ss []
 << [FULL_SIMP_TAC std_ss [dtmc_def, mc_property_def, random_variable_def],
     PROVE_TAC [th_dtmc_def, DTMC_EVENTS],
     PROVE_TAC [th_dtmc_def, DTMC_EVENTS],
     PSET_TAC [distribution_def],
     RW_TAC std_ss [DISJOINT_PROC_INTER],
     FULL_SIMP_TAC std_ss [th_dtmc_def, dtmc_def, mc_property_def,
     	 BIGUNION_PREIMAGEX_IS_PSPACE]]);

val TEMP = prove
 (``!(t:num) n k k'. k < k' /\ 0 < n ==>
        (\k. if k = 0 then t else if k = 1 then t + n else 
                if k = 2 then t + n + 1 else t + n + k) k <
        (\k. if k = 0 then t else if k = 1 then t + n else 
                if k = 2 then t + n + 1 else t + n + k) k'``,
    RW_TAC arith_ss []);
              
(* ------------------------------------------------------------------------- *)
(* Lemma 1: Multistep Transition Probability                                 *)
(* --------------------------------------------------------------------------*)    		 
val MC_NSTEP_COND_PROB_PRE = store_thm 
  ("MC_NSTEP_COND_PROB_PRE",
  ``!X p s (n:num) (f:num -> 'b) Linit Ltrans t.        
       dtmc X p s Linit Ltrans /\ FINITE (space s) ==> 
       (cond_pmf p (X (t + n + 1)) (X t) ({f (n + 1)},{f 0}) = 
        SIGMA (\k. cond_pmf p (X (t + n + 1)) (X (t + n)) ({f (n + 1)},{k}) * 
                   cond_pmf p (X (t + n)) (X t) ({k},{f 0})) (space s))``,
    RW_TAC std_ss [] 
 ++ `prob_space p` by FULL_SIMP_TAC std_ss [dtmc_def, mc_property_def, random_variable_def]
 ++ Cases_on `f 0 NOTIN (space s)`
 >> (RW_TAC std_ss [COND_PMF_EQ_COND_PROB]
    ++ `PREIMAGE (X (t:num)) {f 0} INTER p_space p = {}`
    	by (MATCH_MP_TAC NOTIN_SPACE_EVENTS 
    	   ++ Q.EXISTS_TAC `s` ++ PSET_TAC [dtmc_def, mc_property_def])
    ++ RW_TAC std_ss [PROB_EMPTY, cond_prob_def, INTER_EMPTY, real_div, 
    	REAL_DIV_LZERO, REAL_MUL_LZERO, REAL_MUL_RZERO, REAL_SUM_IMAGE_0])
 ++ `(PREIMAGE (X (t:num)) {f 0} INTER p_space p) IN events p` by PROVE_TAC [DTMC_EVENTS]
 ++ Cases_on `f (n + 1) NOTIN (space s)`
 >> (RW_TAC std_ss [COND_PMF_EQ_COND_PROB]
    ++ `PREIMAGE (X (t + n + 1)) {f (n + 1)} INTER p_space p = {}`
    	by (MATCH_MP_TAC NOTIN_SPACE_EVENTS 
    	   ++ Q.EXISTS_TAC `s` ++ PSET_TAC [dtmc_def, mc_property_def])
    ++ RW_TAC std_ss [cond_prob_def, INTER_EMPTY, real_div, PROB_EMPTY, 
    	REAL_DIV_LZERO, REAL_MUL_LZERO, REAL_MUL_RZERO, REAL_SUM_IMAGE_0])
 ++ Cases_on `distribution p (X (t:num)) {f 0} = 0`
 >> (RW_TAC std_ss [COND_PMF_EQ_COND_PROB]
    ++ `PREIMAGE (X (t + (n:num) + 1)) {f (n + 1)} INTER p_space p IN events p` 
    	by PROVE_TAC [DTMC_EVENTS]
    ++ FULL_SIMP_TAC std_ss [distribution_def, COND_PROB_ZERO]
    ++ (MP_TAC o GSYM o Q.ISPEC `(space (s :('b -> bool) # (('b -> bool) -> bool)))`)
    	 REAL_SUM_IMAGE_0 ++ RW_TAC std_ss [] ++ POP_ORW 
    ++ MATCH_MP_TAC REAL_SUM_IMAGE_EQ ++ RW_TAC std_ss []
    ++ `PREIMAGE (X (t + n)) {x} INTER p_space p IN events p` by PROVE_TAC [DTMC_EVENTS]
    ++ RW_TAC std_ss [COND_PROB_ZERO, REAL_MUL_RZERO]) 
 ++ `0 < distribution p (X (t:num)) {f 0}` 
 	by FULL_SIMP_TAC std_ss [distribution_def, PROB_POSITIVE, REAL_LT_LE]
 ++ Cases_on `n = 0` 
 >> (PSET_TAC [dtmc_def, mc_property_def]
    ++ (MP_TAC o Q.SPECL [`X`, `(f:num -> 'b) 0`, `(f:num -> 'b) 1`, `Linit`, 
        `Ltrans`, `p`, `s`, `t`]) RV_COND_PROB 
    ++ RW_TAC std_ss [] 
    ++ (MP_TAC o Q.ISPECL [`(space (s :('b -> bool) # (('b -> bool) -> bool)))`, 
        `(\(k:'b). cond_pmf p ((X:num -> 'a -> 'b) (t + 1)) (X (t:num)) ({(f:num -> 'b) 1},{k}) *
             cond_pmf p (X t) (X t) ({k},{(f:num -> 'b) (0:num)}))`, 
	`(\k. if k = f 0 then 
	        cond_pmf p ((X:num -> 'a -> 'b) (t + 1)) (X t) 
	                ({(f:num -> 'b) 1},{(f:num -> 'b) 0}) else 0)`])
	         REAL_SUM_IMAGE_EQ ++ RW_TAC std_ss [] 
    ++ RW_TAC std_ss [SIGMA_ONE_NON_ZERO_TERM])
 ++ `0 < n` by RW_TAC arith_ss []
 ++ Know `cond_pmf p ((X:num -> 'a -> 'b) (t + n + 1)) (X t) ({f (n + 1)},{f 0}) = 
       SIGMA (\k. cond_prob p (PREIMAGE (X (t + n + 1)) {f (n + 1)} INTER p_space p)
			((PREIMAGE (X (t + n)) {k} INTER p_space p) INTER 
			(PREIMAGE (X t) {f 0} INTER p_space p)) * 
                  cond_pmf p (X (t + n)) (X t) ({k},{f 0})) (space s)`
 >> (RW_TAC std_ss [COND_PMF_EQ_COND_PROB] 
    ++ `SIGMA (\k. cond_prob p (PREIMAGE (X (t + n + 1)) {f (n + 1)} INTER p_space p)
			((PREIMAGE (X (t + n)) {k} INTER p_space p) INTER 
			(PREIMAGE (X t) {f 0} INTER p_space p)) * 
                  cond_prob p (PREIMAGE (X (t + n)) {k} INTER p_space p)
			(PREIMAGE (X t) {f 0} INTER p_space p)) (space s) =
	SIGMA (\k. cond_prob p (PREIMAGE (X (t + n + 1)) {f (n + 1)} INTER p_space p)
			(((\(k:'b). PREIMAGE (X (t + n)) {k} INTER p_space p) k) INTER 
			(PREIMAGE (X t) {f 0} INTER p_space p)) * 
                  cond_prob p ((\k. PREIMAGE (X (t + n)) {k} INTER p_space p) k)
			(PREIMAGE (X t) {f 0} INTER p_space p)) (space s)` by RW_TAC std_ss []
    ++ POP_ORW ++ MATCH_MP_TAC COND_INTER_MUL_SIGMA ++ RW_TAC std_ss []
    << [PROVE_TAC [DTMC_EVENTS],
        PROVE_TAC [DTMC_EVENTS],
        RW_TAC std_ss [DISJOINT_PROC_INTER],
        FULL_SIMP_TAC std_ss [th_dtmc_def, dtmc_def, mc_property_def, 
                BIGUNION_PREIMAGEX_IS_PSPACE, INTER_IDEMPOT]]) 
 ++ RW_TAC std_ss [COND_PMF_EQ_COND_PROB] ++ POP_ASSUM K_TAC
 ++ MATCH_MP_TAC REAL_SUM_IMAGE_EQ ++ RW_TAC std_ss [] 
 ++ Cases_on `cond_prob p (PREIMAGE (X (t + n)) {x} INTER p_space p)
      (PREIMAGE (X t) {f 0} INTER p_space p) = 0` 
 >> RW_TAC std_ss [REAL_MUL_RZERO]  
 ++ RW_TAC std_ss [REAL_EQ_RMUL] 
 ++ `prob p (PREIMAGE (X (t:num)) {f 0} INTER p_space p) <> 0` 
 			by FULL_SIMP_TAC std_ss [distribution_def]
 ++ FULL_SIMP_TAC std_ss [th_dtmc_def, dtmc_def, mc_property_def]
 ++ `EL 0 [f 0; x; f (n + 1)] = f 0` by RW_TAC std_ss [APPEND, EL, HD]
 ++ `EL 1 [f 0; x; f (n + 1)] = x` 
 	by (`1 = SUC 0` by METIS_TAC [ONE] ++ POP_ORW ++ RW_TAC std_ss [APPEND, EL, HD, TL])
 ++ `EL 2 [f 0; x; f (n + 1)] = f (n + 1)` 
 	by (`2 = SUC (SUC 0)` by RW_TAC arith_ss [] ++ POP_ORW 
 	   ++ RW_TAC std_ss [APPEND, EL, HD, TL])  
 ++ (MP_TAC o Q.SPECL [`t`, `n`]) TEMP ++ RW_TAC std_ss []
 ++ FIRST_ASSUM (MP_TAC o Q.SPECL 
        [`(\k. EL k [((f:num -> 'b) 0);x;(f (n + 1))])`, 
         `(\k. if k = 0 then t else if k = 1 then t + n else 
                if k = 2 then t + n + 1 else t + n + k)`,
         `1`])
 ++ RW_TAC std_ss [Increasing_seq_def, COUNT_ONE, IMAGE_SING, 
        BIGINTER_SING, COND_PMF_EQ_COND_PROB]);
        

val MC_NSTEP_COND_PROB = store_thm 
  ("MC_NSTEP_COND_PROB",
  ``!X p s (n:num) i j Linit Ltrans t.        
       dtmc X p s Linit Ltrans /\ FINITE (space s) ==> 
       (cond_pmf p (X (t + n + 1)) (X t) ({j},{i}) = 
        SIGMA (\k. cond_pmf p (X (t + n + 1)) (X (t + n)) ({j},{k}) * 
                   cond_pmf p (X (t + n)) (X t) ({k},{i})) (space s))``,
    RW_TAC std_ss []
 ++ (MP_TAC o Q.SPECL [`X`, `p`, `s`, `n`, 
        `(\k. if k = 0 then i else if k = n + 1 then j else j)`, `Linit`, `Ltrans`, `t`])
        MC_NSTEP_COND_PROB_PRE ++ RW_TAC std_ss []);

(* ------------------------------------------------------------------------- *)
(* Theorem 2: Chapman-Kolmogorov Equation                                    *)
(* --------------------------------------------------------------------------*) 
val TEMP_MN = prove
 (``!(t:num) m n. 0 < m /\ 0 < n ==> Increasing_seq
            (\r. if r = (0:num) then t else if r = 1 then t + m else 
 		if r = 2 then t + m + n else t + m + n + r)``,
    RW_TAC arith_ss [Increasing_seq_def]);
    
val MC_MN_PROB = store_thm 
  ("MC_MN_PROB",
  ``!X p s t m (n:num) i j k Linit Ltrans.        
       dtmc X p s Linit Ltrans /\ FINITE (space s) /\ k IN space s /\
       0 < m /\ 0 < n /\ prob p (PREIMAGE (X t) {i} INTER p_space p) <> 0 ==> 
       (cond_pmf p (X (t + m + n)) (X (t + m)) ({j},{k}) = 
        cond_prob p (PREIMAGE (X (t + m + n)) {j} INTER p_space p)
                    ((\k. PREIMAGE (X (t + m)) {k} INTER p_space p) k INTER
                     (PREIMAGE (X t) {i} INTER p_space p)))``,
    RW_TAC std_ss [dtmc_def, mc_property_def]
 ++ NTAC 8 (POP_ASSUM MP_TAC)
 ++ POP_ASSUM (MP_TAC o Q.SPECL [`(\(r:num). if r = (0:num) then (i:'b) else if r = 1 then k else j)`, 
 	`(\r. if r = (0:num) then t else if r = 1 then t + m else 
 		if r = 2 then t + m + n else t + m + n + r)`, `1`])
 ++ PSET_TAC [COUNT_ONE, IMAGE_SING, BIGINTER_SING]
 ++ FULL_SIMP_TAC std_ss [TEMP_MN]);
        
        
val DTMC_CK_EQUATION = store_thm
  ("DTMC_CK_EQUATION",
  ``!X p s Linit Ltrans t m n i j.
   dtmc X p s Linit Ltrans /\ 0 < m /\ 0 < n /\ FINITE (space s) ==> 
   (cond_prob p (PREIMAGE (X (t + m + n)) {j} INTER p_space p)
    		(PREIMAGE (X t) {i} INTER p_space p) =
    SIGMA (\k. cond_prob p (PREIMAGE (X (t + m + n)) {j} INTER p_space p)
    			(PREIMAGE (X (t + m)) {k} INTER p_space p) *
    	       cond_prob p (PREIMAGE (X (t + m)) {k} INTER p_space p)
    	       		(PREIMAGE (X t) {i} INTER p_space p)) (space s))``,
    RW_TAC std_ss []
 ++ `FINITE (space s)` by PSET_TAC [th_dtmc_def]
 ++ `prob_space p` by PSET_TAC [th_dtmc_def, dtmc_def, mc_property_def, random_variable_def] 
 ++ Cases_on `i NOTIN (space s)`
 >> (RW_TAC std_ss [] 
    ++ `PREIMAGE (X t) {i:'b} INTER p_space p = {}`
    	by (MATCH_MP_TAC NOTIN_SPACE_EVENTS 
           ++ Q.EXISTS_TAC `s` ++ PSET_TAC [dtmc_def, mc_property_def])
    ++ RW_TAC std_ss [cond_prob_def, INTER_EMPTY, real_div, PROB_EMPTY, 
    		REAL_DIV_LZERO, REAL_MUL_LZERO, REAL_MUL_RZERO, REAL_SUM_IMAGE_0])
 ++ Cases_on `j NOTIN (space s)`
 >> (RW_TAC std_ss [] 
    ++ `!t. PREIMAGE (X t) {j:'b} INTER p_space p = {}`
    	by (RW_TAC std_ss [] ++ MATCH_MP_TAC NOTIN_SPACE_EVENTS 
           ++ Q.EXISTS_TAC `s` ++ PSET_TAC [th_dtmc_def, dtmc_def, mc_property_def])
    ++ RW_TAC std_ss [cond_prob_def, INTER_EMPTY, real_div, PROB_EMPTY, 
    		REAL_DIV_LZERO, REAL_MUL_LZERO, REAL_MUL_RZERO, REAL_SUM_IMAGE_0])    		
 ++ Cases_on `prob p (PREIMAGE (X t) {i} INTER p_space p) = 0`
 >> (RW_TAC std_ss [ADD1, ADD_ASSOC]
    ++ MP_RW_TAC COND_PROB_ZERO
    >> (DEP_REWRITE_TAC [DTMC_EVENTS]
       ++ RW_TAC std_ss []
       ++ MAP_EVERY Q.EXISTS_TAC [`s`, `Linit`, `Ltrans`]
       ++ RW_TAC std_ss [])
    ++ `!k. k IN space s ==> (cond_prob p (PREIMAGE (X (t + m)) {k} INTER p_space p)
           (PREIMAGE (X t) {i} INTER p_space p) = 0)`
           by (RW_TAC std_ss [] ++ MP_RW_TAC COND_PROB_ZERO
              ++ DEP_REWRITE_TAC [DTMC_EVENTS] ++ RW_TAC std_ss []
    	      ++ MAP_EVERY Q.EXISTS_TAC [`s`, `Linit`, `Ltrans`]
              ++ RW_TAC std_ss []) 
    ++ `(0:real) = SIGMA (\k. 0) (space s)` by RW_TAC std_ss [REAL_SUM_IMAGE_0]
    ++ POP_ORW ++ MATCH_MP_TAC REAL_SUM_IMAGE_EQ
    ++ RW_TAC std_ss [REAL_MUL_RZERO])
 ++ Know `cond_prob p (PREIMAGE (X (t + m + n)) {j} INTER p_space p)
 			(PREIMAGE (X t) {i} INTER p_space p) =
 	  SIGMA (\k. cond_prob p (PREIMAGE (X (t + m + n)) {j} INTER p_space p)
 	  			 ((\k. PREIMAGE (X (t + m)) {k} INTER p_space p) k INTER
 	  			  (PREIMAGE (X t) {i} INTER p_space p)) *
 	  	     cond_prob p ((\k. PREIMAGE (X (t + m)) {k} INTER p_space p) k)
 	  	     		 (PREIMAGE (X t) {i} INTER p_space p)) (space s)`
 >> (MATCH_MP_TAC COND_INTER_MUL_SIGMA ++ RW_TAC std_ss []
   << [METIS_TAC [DTMC_EVENTS],
       METIS_TAC [DTMC_EVENTS],
       METIS_TAC [DTMC_EVENTS],
       RW_TAC std_ss [DISJOINT_PROC_INTER],
       DEP_REWRITE_TAC [BIGUNION_PREIMAGEX_IS_PSPACE]
       ++ PSET_TAC [dtmc_def, mc_property_def, INTER_IDEMPOT]])
 ++ RW_TAC std_ss [] 
 ++ MATCH_MP_TAC REAL_SUM_IMAGE_EQ
 ++ RW_TAC std_ss []  
 ++ `!(a:real) b c. (a = b) ==> (a * c = b * c)` by RW_TAC std_ss []
 ++ POP_ASSUM MATCH_MP_TAC
 ++ (MP_TAC o Q.SPECL [`X`, `p`, `s`, `t`, `m`, `n`, `i`, `j`, `x`, `Linit`, `Ltrans`]) MC_MN_PROB
 ++ RW_TAC std_ss [COND_PMF_EQ_COND_PROB]);

(* ------------------------------------------------------------------------- *)
(* Theorem : Reversibility DTMC Theorems                                    *)
(* --------------------------------------------------------------------------*) 
val BALANCE_MC_STATIONARY = store_thm
  ("BALANCE_MC_STATIONARY",
  ``!X (n:num) Linit Ltrans p s n.
	th_dtmc X p s Linit Ltrans /\ 
	(detailed_balance_equations (\i. distribution p (X n) {i}) X p s) ==> 
	stationary_distribution p X (\j. distribution p (X n) {j}) s``,
    RW_TAC std_ss [th_dtmc_def, dtmc_def] 
 ++ `prob_space p` by FULL_SIMP_TAC std_ss [mc_property_def, random_variable_def]
 ++ `!(t:num). random_variable (X t) p s` 
			by FULL_SIMP_TAC std_ss [dtmc_def, mc_property_def]
 ++ (MP_TAC o Q.SPECL [`X`, `p`, `s`]) BIGUNION_PREIMAGEX_IS_PSPACE 
 ++ RW_TAC std_ss [] 
 ++ POP_ASSUM (MP_TAC o Q.SPEC `(n:num)`) 
 ++ RW_TAC std_ss [stationary_distribution_def] 
 << [MATCH_MP_TAC SUM_PMF_ONE ++ RW_TAC std_ss [],
 
     RW_TAC std_ss [distribution_def]
     ++ MATCH_MP_TAC PROB_POSITIVE
     ++ RW_TAC std_ss []
     ++ MATCH_MP_TAC DTMC_EVENTS
     ++ MAP_EVERY Q.EXISTS_TAC [`s`, `Linit`, `Ltrans`]
     ++ RW_TAC std_ss [dtmc_def],

     PSET_TAC [distribution_def, Trans_def]
     ++ `SIGMA (\j'. prob p (PREIMAGE (X n) {j'} INTER p_space p) *
         if j' IN space s then cond_prob p (PREIMAGE (X (t + 1)) {j} INTER p_space p)
             (PREIMAGE (X t) {j'} INTER p_space p)
         else 0) (space s) =
         SIGMA (\j'. prob p (PREIMAGE (X n) {j'} INTER p_space p) *
         	cond_prob p (PREIMAGE (X (t + 1)) {j} INTER p_space p)
             (PREIMAGE (X t) {j'} INTER p_space p)) (space s)` 
             by (MATCH_MP_TAC REAL_SUM_IMAGE_EQ ++ RW_TAC std_ss [])
     ++ POP_ORW
     ++ `!j'. prob p (PREIMAGE (X n) {j'} INTER p_space p) *
               cond_prob p (PREIMAGE (X (t + 1)) {j} INTER p_space p)
                 (PREIMAGE (X t) {j'} INTER p_space p) =
            prob p (PREIMAGE (X n) {j} INTER p_space p) *
               cond_prob p (PREIMAGE (X (t + 1)) {j'} INTER p_space p)
                (PREIMAGE (X t) {j} INTER p_space p)`
		by (PSET_TAC [detailed_balance_equations_def, Trans_def]
		   ++ Cases_on `j' NOTIN space s`
		   >> (RW_TAC std_ss [] 
		      ++ `PREIMAGE (X n) {j'} INTER p_space p = {}` 
		      		by METIS_TAC [NOTIN_SPACE_EVENTS]
		      ++ `PREIMAGE (X (t + 1)) {j'} INTER p_space p = {}` 
		      		by METIS_TAC [NOTIN_SPACE_EVENTS]
		      ++ RW_TAC std_ss [cond_prob_def, INTER_EMPTY, REAL_MUL_LZERO, PROB_EMPTY,
		      		REAL_DIV_LZERO, REAL_MUL_RZERO])
		   ++ NTAC 5 (POP_ASSUM MP_TAC) ++ POP_ASSUM (MP_TAC o Q.SPECL [`j'`, `j`, `t`])
		   ++ METIS_TAC [])
    ++ POP_ORW	
    ++ `SIGMA (\j'. prob p (PREIMAGE (X n) {j} INTER p_space p) *
         cond_prob p (PREIMAGE (X (t + 1)) {j'} INTER p_space p)
           (PREIMAGE (X t) {j} INTER p_space p)) (space s) =
        SIGMA (\j'. prob p (PREIMAGE (X n) {j} INTER p_space p) *
         cond_prob p ((\j'. PREIMAGE (X (n + 1)) {j'} INTER p_space p) j')
           (PREIMAGE (X n) {j} INTER p_space p)) (space s)`
           by (MATCH_MP_TAC REAL_SUM_IMAGE_EQ 
              ++ RW_TAC std_ss []
              ++ (MP_TAC o Q.SPECL [`X`, `p`, `s`, `Linit`, `Ltrans`]) HOMO_LEMMA
              ++ RW_TAC std_ss [th_dtmc_def, dtmc_def, distribution_def, Trans_def]
              ++ METIS_TAC []) ++ POP_ORW
    ++ MATCH_MP_TAC TOTAL_PROB_EXA
    ++ RW_TAC std_ss []
    << [MATCH_MP_TAC DTMC_EVENTS ++ MAP_EVERY Q.EXISTS_TAC [`s`, `Linit`, `Ltrans`]
        ++ RW_TAC std_ss [dtmc_def, distribution_def, Trans_def],
        
        MATCH_MP_TAC DTMC_EVENTS ++ MAP_EVERY Q.EXISTS_TAC [`s`, `Linit`, `Ltrans`]
        ++ RW_TAC std_ss [dtmc_def, distribution_def, Trans_def],
        
        RW_TAC std_ss [DISJOINT_PROC_INTER],
        
        RW_TAC std_ss [BIGUNION_PREIMAGEX_IS_PSPACE]]]);
        
val MC_STATION_PMF = store_thm
  ("MC_STATION_PMF",
  ``!X (n:num) (t:num) j Linit Ltrans p s.
	th_dtmc X p s Linit Ltrans /\ stationary_pmf X p s ==> 
	(prob p (PREIMAGE (X n) {j} INTER p_space p) = 
	 prob p (PREIMAGE (X t) {j} INTER p_space p))``,
    RW_TAC std_ss [stationary_pmf_def, th_dtmc_def, dtmc_def, mc_property_def] 
 ++ POP_ASSUM (MP_TAC o Q.SPECL [`(\(k:num). j)`, `n`, `t`, `1`])
 ++ RW_TAC std_ss [COUNT_ONE, IMAGE_SING, BIGINTER_SING]);

val STATION_PROB_DISTRIBUTION = store_thm
  ("STATION_PROB_DISTRIBUTION",
  ``!X p s (n:num) (t:num) j.
	stationary_pmf X p s ==> 
	(prob p (PREIMAGE (X n) {j} INTER p_space p) = 
	 prob p (PREIMAGE (X t) {j} INTER p_space p))``,
    RW_TAC std_ss [stationary_pmf_def] 
 ++ FULL_SIMP_TAC std_ss []    
 ++ POP_ASSUM (MP_TAC o Q.SPECL [`(\(k:num). j)`, `n`, `t`, `1`])
 ++ RW_TAC std_ss [COUNT_ONE, IMAGE_SING, BIGINTER_SING]);

val STATION_PMF = store_thm
  ("STATION_PMF",
  ``!X p s Linit Ltrans i (t:num) (w:num).
	th_dtmc X p s Linit Ltrans /\ 
	stationary_distribution p X (\i. prob p (PREIMAGE (X 0) {i} INTER p_space p)) s ==>
	(prob p (PREIMAGE (X w) {i} INTER p_space p) = 
	 prob p (PREIMAGE (X t) {i} INTER p_space p))``,
    Induct_on `t`
 >> (Induct_on `w` >> RW_TAC std_ss []
    ++ RW_TAC std_ss []
    ++ `!i. prob p (PREIMAGE (X w) {i} INTER p_space p) =
             prob p (PREIMAGE (X 0) {i} INTER p_space p)` by METIS_TAC [] 
    ++ Cases_on `i NOTIN space s`
    >> (DEP_REWRITE_TAC [NOTIN_SPACE_EVENTS,EVENTS_EMPTY]
       ++ RW_TAC std_ss []
       ++ Q.EXISTS_TAC `s`
       ++ PSET_TAC [th_dtmc_def, dtmc_def, mc_property_def])
    ++ (MP_TAC o Q.SPECL [`X`, `1`, `w`, `i`, `Linit`, `Ltrans`, `p`, `s`])
    	 N_STEP_PROB_DISTRIBUTION
    ++ PSET_TAC [th_dtmc_def, distribution_def, COND_PMF_EQ_COND_PROB, ADD1] 
    ++ `prob p (PREIMAGE (X 0) {i} INTER p_space p) =
        SIGMA (\i'. prob p (PREIMAGE (X 0) {i'} INTER p_space p) *
                   Trans X p s t 1 i' i) (space s)` by PSET_TAC [stationary_distribution_def]
    ++ POP_ORW ++ MATCH_MP_TAC REAL_SUM_IMAGE_EQ
    ++ RW_TAC std_ss [Trans_def]
    ++ (MP_TAC o Q.SPECL [`X`, `p`, `s`, `Linit`, `Ltrans`]) HOMO_LEMMA
    ++ RW_TAC std_ss [th_dtmc_def] 
    ++ POP_ASSUM (MP_TAC o Q.SPECL [`w`, `t`, `x`, `i`]) ++ RW_TAC std_ss [])
 ++ RW_TAC std_ss [ADD1] 
 ++ FIRST_ASSUM (MP_TAC o Q.SPECL [`X`, `p`, `s`, `Linit`, `Ltrans`, `i`, `t + 1`]) 
 ++ RW_TAC std_ss [] ++ METIS_TAC []);
	
val TIME_MC_PROC = store_thm
  ("TIME_MC_PROC",	
  ``!X p s Linit Ltrans. 
	th_dtmc X p s Linit Ltrans /\
	stationary_distribution p X (\j. prob p (PREIMAGE (X 0) {j} INTER p_space p)) s ==>
	stationary_pmf X p s``,
    RW_TAC std_ss [stationary_pmf_def]
 >> PSET_TAC [th_dtmc_def, dtmc_def, mc_property_def]    
 ++ (MP_TAC o Q.SPECL [`X`, `p`, `s`, `Linit`, `Ltrans`]) STATION_PMF
 ++ RW_TAC std_ss []
 ++ Cases_on `n = 0`
 >> RW_TAC std_ss [COUNT_ZERO, IMAGE_EMPTY, BIGINTER_EMPTY]
 ++ `!w. BIGINTER (IMAGE (\k. PREIMAGE (X (w + k)) {f k} INTER p_space p) (count n)) =
    	 BIGINTER (IMAGE (\k. PREIMAGE (X (w + k)) 
    	 	{EL k (GENLIST (\k. f k) n)} INTER p_space p) (count n))`
     by RW_TAC arith_ss [EXTENSION, IN_BIGINTER_IMAGE, IN_COUNT]    	 	
 ++ `n - 1 + 1 = n` by RW_TAC arith_ss [] 
 ++ (MP_TAC o Q.SPECL [`X`, `p`, `s`, `w`, `n - 1`, `GENLIST (\(k:num). ((f k):'b)) n`, 
 	`Linit`, `Ltrans`]) MC_JOINT_PROB ++ PSET_TAC [th_dtmc_def, EL_GENLIST]
 ++ (MP_TAC o Q.SPECL [`X`, `p`, `s`, `t`, `n - 1`, `GENLIST (\(k:num). ((f k):'b)) n`, 
 	`Linit`, `Ltrans`]) MC_JOINT_PROB ++ PSET_TAC [th_dtmc_def, EL_GENLIST]
 ++ NTAC 4 (POP_ASSUM K_TAC) ++ POP_ASSUM MP_TAC
 ++ POP_ASSUM (MP_TAC o Q.SPECL [`EL 0 (GENLIST (\k. (f k):'b) n)`, `t`, `w`]) 
 ++ RW_TAC std_ss [distribution_def]		 
 ++ Cases_on `prob p (PREIMAGE (X t) {EL 0 (GENLIST (\k. f k) n)} INTER p_space p) = 0` 
 >> RW_TAC std_ss [REAL_MUL_RZERO]
 ++ RW_TAC std_ss [REAL_EQ_RMUL]
 ++ MATCH_MP_TAC MULCON_POS_EQ
 ++ RW_TAC std_ss [COND_PMF_EQ_COND_PROB]
 ++ METIS_TAC [HOMO_LEMMA, th_dtmc_def]);
 
val TIME_MC_INITIAL_STATIONARY = store_thm 
  ("TIME_MC_INITIAL_STATIONARY",
  ``!X p s Linit Ltrans (n:num).
	th_dtmc X p s Linit Ltrans /\ stationary_pmf X p s ==> 
	stationary_distribution p X (\i. prob p (PREIMAGE (X n) {i} INTER p_space p)) s``,
    RW_TAC std_ss [stationary_distribution_def, th_dtmc_def] 
 << [(MP_TAC o Q.SPECL [`X`, `p`, `s`, `n`]) SUM_PMF_ONE
     ++ PSET_TAC [distribution_def, dtmc_def, mc_property_def],
     
     MATCH_MP_TAC PROB_POSITIVE
     ++ DEP_REWRITE_TAC [DTMC_EVENTS] 
     ++ RW_TAC std_ss []
     >> (MAP_EVERY Q.EXISTS_TAC [`s`, `Linit`, `Ltrans`] ++ RW_TAC std_ss [])
     ++ PSET_TAC [dtmc_def, mc_property_def, random_variable_def],
     
     Know `prob p (PREIMAGE (X (n:num)) {i} INTER p_space p) = 
         prob p (PREIMAGE (X (n + 1)) {i} INTER p_space p)`
     >> (MATCH_MP_TAC STATION_PROB_DISTRIBUTION ++ Q.EXISTS_TAC `s` 
        ++ PSET_TAC [dtmc_def, mc_property_def]) ++ RW_TAC std_ss [] 
     ++ (MP_TAC o Q.SPECL [`X`, `1` , `n`, `i`, `Linit`, `Ltrans`, `p`, `s`]) 
        N_STEP_PROB_DISTRIBUTION 
     ++ PSET_TAC [th_dtmc_def, distribution_def, COND_PMF_EQ_COND_PROB]
     ++ MATCH_MP_TAC REAL_SUM_IMAGE_EQ ++ RW_TAC std_ss [Trans_def]
     ++ METIS_TAC [HOMO_LEMMA, th_dtmc_def]]);	
    
val STEADY_STATE_PROB = store_thm
  ("STEADY_STATE_PROB",
  ``!X p s Linit Ltrans. th_dtmc X p s Linit Ltrans /\ 
        (!i. ?(u:real). (\n. prob p (PREIMAGE (X n) {i} INTER p_space p)) --> u) ==> 
        stationary_distribution p X (\j. 
        lim (\(n:num). prob p (PREIMAGE (X n) {j} INTER p_space p))) s``,
    RW_TAC std_ss [stationary_distribution_def]          
 << [DEP_REWRITE_TAC [GSYM SIGMA_LIM]
    ++ PSET_TAC [th_dtmc_def]
    ++ (MP_TAC o Q.SPECL [`X`, `p`, `s`]) SUM_PMF_ONE
    ++ PSET_TAC [distribution_def, dtmc_def, mc_property_def, LIM_CONST],
 
    MATCH_MP_TAC LE_SEQ_IMP_LE_LIM
    ++ Q.EXISTS_TAC `(\n. prob p (PREIMAGE ((X:num -> 'a -> 'b) n) {j} INTER p_space p))`
    ++ RW_TAC std_ss [TEND2LIM]
    >> (MATCH_MP_TAC PROB_POSITIVE
       ++ PSET_TAC [th_dtmc_def]
       >> PSET_TAC [dtmc_def, mc_property_def, random_variable_def]
       ++ METIS_TAC [DTMC_EVENTS])
    ++ RW_TAC std_ss [GSYM SEQ_LIM, convergent],
       
    (MP_TAC o GSYM o Q.SPECL [`(\(n:num). prob p (PREIMAGE (X n) {j} INTER p_space p))`])
        LIM_FN_EQ_LIM_FSUCN ++ RW_TAC std_ss [ADD1]
    ++ Know `!n. distribution p (X (n + 1)) {j} =
          SIGMA (\k. distribution p (X n) {k} * 
          cond_pmf p (X (n + 1)) (X n) ({j},{k})) (space s)`
    >> (PSET_TAC [th_dtmc_def] 
       ++ (MP_TAC o Q.SPECL [`X`, `1` , `n`, `j`, `Linit`, `Ltrans`, `p`, `s`])
                N_STEP_PROB_DISTRIBUTION ++ RW_TAC std_ss []) 
    ++ RW_TAC std_ss [distribution_def, COND_PMF_EQ_COND_PROB] ++ POP_ASSUM K_TAC
    ++ `FINITE (space s)` by PSET_TAC [th_dtmc_def]
    ++ `!n k. cond_prob p (PREIMAGE (X (n + 1)) {j} INTER p_space p)
	         (PREIMAGE (X n) {k} INTER p_space p) = 
         	cond_prob p (PREIMAGE (X 1) {j} INTER p_space p)
      		(PREIMAGE (X 0) {k} INTER p_space p)` 
      	  by (RW_TAC std_ss [] 
             ++ (MP_TAC o Q.SPECL [`X`, `p`, `s`, `Linit`, `Ltrans`]) HOMO_LEMMA
             ++ RW_TAC std_ss [] 
             ++ POP_ASSUM (MP_TAC o Q.SPECL [`n`, `0`, `k`, `j`]) ++ RW_TAC std_ss [])
             
    ++ DEP_REWRITE_TAC [SIGMA_LIM] ++ RW_TAC std_ss []
    >> (NTAC 5 (POP_ASSUM MP_TAC) 
       ++ POP_ASSUM (MP_TAC o Q.SPEC `k`) ++ RW_TAC std_ss []
       ++ Q.EXISTS_TAC `u * cond_prob p (PREIMAGE (X 1) {j} INTER p_space p)
                        (PREIMAGE (X 0) {k} INTER p_space p)`
       ++ `(\n. prob p (PREIMAGE (X n) {k} INTER p_space p) *
       		cond_prob p (PREIMAGE (X 1) {j} INTER p_space p)
         		(PREIMAGE (X 0) {k} INTER p_space p)) =
           (\n. (\n. prob p (PREIMAGE (X n) {k} INTER p_space p)) n *
       		(\n. cond_prob p (PREIMAGE (X 1) {j} INTER p_space p)
         		(PREIMAGE (X 0) {k} INTER p_space p)) n)` by RW_TAC std_ss []
       ++ POP_ORW ++ MATCH_MP_TAC SEQ_MUL
       ++ RW_TAC std_ss [SEQ_CONST])
    ++ MATCH_MP_TAC REAL_SUM_IMAGE_EQ ++ RW_TAC std_ss [Trans_def] 
    ++ `lim (\n. prob p (PREIMAGE (X n) {x} INTER p_space p) *
         	cond_prob p (PREIMAGE (X 1) {j} INTER p_space p)
           		(PREIMAGE (X 0) {x} INTER p_space p)) =
           lim (\n. (\n. prob p (PREIMAGE (X n) {x} INTER p_space p)) n *
         	cond_prob p (PREIMAGE (X 1) {j} INTER p_space p)
           		(PREIMAGE (X 0) {x} INTER p_space p))`
           by RW_TAC std_ss [] ++ POP_ORW ++ MATCH_MP_TAC LIM_MUL_CONST          		
    ++ RW_TAC std_ss [GSYM SEQ_LIM, convergent]]); 
             
val REVERSE_JOINT_MUL = store_thm 
  ("REVERSE_JOINT_MUL",
  ``!X (t:num) n f p s. 
        (!(t:num). random_variable (X t) p s) /\ 
	(detailed_balance_equations (\i. distribution p (X t) {i}) X p s) ==> 
	(mulcon (0,n) (\k.
         	cond_pmf p (X (t + k + 1)) (X (t + k)) ({f (k + 1)},{f k})) * 
		distribution p (X t) {f 0} =
   	 mulcon (0,n) (\k.
         	cond_pmf p (X (t + k + 1)) (X (t + k)) ({f k}, {f (k + 1)})) * 
		distribution p (X t) {f n})``,
    Induct_on `n` >> RW_TAC std_ss [mulcon_def] 
 ++ RW_TAC std_ss [mulcon_def] 
 ++ `!a b (c:real). a * b * c = a * c * b` by METIS_TAC [REAL_MUL_ASSOC, REAL_MUL_COMM]
 ++ POP_ORW ++ FIRST_ASSUM (MP_TAC o Q.SPECL [`X`, `t`, `f`, `p`, `s`])
 ++ RW_TAC std_ss [] 
 ++ `!a b c (d:real) e. (b * c = d * e) ==> (a * b * c = a * d * e)` 
 	by METIS_TAC [REAL_MUL_ASSOC]
 ++ POP_ASSUM MATCH_MP_TAC ++ POP_ASSUM K_TAC
 ++ Cases_on `f n NOTIN space s`
 >> (`!t. PREIMAGE (X t) {f n} INTER p_space p = {}` by METIS_TAC [NOTIN_SPACE_EVENTS]
    ++ `prob_space p` by PSET_TAC [random_variable_def]
    ++ RW_TAC std_ss [distribution_def, COND_PMF_EQ_COND_PROB, cond_prob_def, 
    	INTER_EMPTY, PROB_EMPTY, REAL_MUL_LZERO, REAL_DIV_LZERO, REAL_MUL_RZERO])
 ++ Cases_on `f (n + 1) NOTIN space s`
 >> (`!t. PREIMAGE (X t) {f (n + 1)} INTER p_space p = {}` by METIS_TAC [NOTIN_SPACE_EVENTS]
    ++ `prob_space p` by PSET_TAC [random_variable_def]
    ++ RW_TAC std_ss [distribution_def, COND_PMF_EQ_COND_PROB, cond_prob_def, 
    	INTER_EMPTY, PROB_EMPTY, REAL_MUL_LZERO, REAL_DIV_LZERO, REAL_MUL_RZERO])   	 
 ++ FULL_SIMP_TAC std_ss [detailed_balance_equations_def, distribution_def, 
 	Trans_def, COND_PMF_EQ_COND_PROB]
 ++ NTAC 2 (POP_ASSUM MP_TAC)    	  	
 ++ POP_ASSUM (MP_TAC o Q.SPECL [`(f (n:num)):'b`, `(f (n + (1:num))):'b`, `t + n`])
 ++ RW_TAC real_ss [ADD1]
 ++ METIS_TAC []);

val SEQ_JOINT_PROB = prove
  (``!X p s Linit Ltrans (t:num) (L:'b list) n.
    th_dtmc X p s Linit Ltrans /\ n + 1 <= LENGTH L /\
    detailed_balance_equations (\i. distribution p (X t) {i}) X p s ==> 
   (mulcon (0,n)
      (\k. cond_prob p (PREIMAGE (X (t + k + 1)) {EL (k + 1) L} INTER p_space p)
           	(PREIMAGE (X (t + k)) {EL k L} INTER p_space p)) *
   prob p (PREIMAGE (X t) {EL 0 L} INTER p_space p) =
   mulcon (0,n)
      (\k. cond_prob p (PREIMAGE (X (t + k + 1)) {EL k L} INTER p_space p)
           	(PREIMAGE (X (t + k)) {EL (k + 1) L} INTER p_space p)) *
   prob p (PREIMAGE (X t) {EL n L} INTER p_space p))``,

    Induct_on `n`
 >> RW_TAC std_ss [mulcon_def]
 ++ RW_TAC std_ss [mulcon_def]
 ++ `!a b (c:real). a * b * c = a * c * b` by METIS_TAC [REAL_MUL_ASSOC, REAL_MUL_COMM]
 ++ POP_ORW ++ FIRST_ASSUM (MP_TAC o Q.SPECL [`X`, `p`, `s`, `Linit`, `Ltrans`, `t`, `L`])
 ++ RW_TAC arith_ss []
 ++ `!a b c (d:real) e. (b * c = d * e) ==> (a * b * c = a * d * e)` 
 	by METIS_TAC [REAL_MUL_ASSOC]
 ++ POP_ASSUM MATCH_MP_TAC ++ POP_ASSUM K_TAC
 ++ `!t. random_variable (X t) p s` by PSET_TAC [th_dtmc_def, dtmc_def, mc_property_def]
 ++ Cases_on `EL n (L:'b list) NOTIN space s`
 >> (`!t. PREIMAGE (X t) {EL n (L:'b list)} INTER p_space p = {}` 
 	by METIS_TAC [NOTIN_SPACE_EVENTS]
    ++ `prob_space p` by PSET_TAC [random_variable_def]
    ++ RW_TAC std_ss [distribution_def, COND_PMF_EQ_COND_PROB, cond_prob_def, 
    	INTER_EMPTY, PROB_EMPTY, REAL_MUL_LZERO, REAL_DIV_LZERO, REAL_MUL_RZERO])
 ++ Cases_on `EL (n + 1) (L:'b list) NOTIN space s`
 >> (`!t. PREIMAGE (X t) {EL (n + 1) (L:'b list)} INTER p_space p = {}` 
 	by METIS_TAC [NOTIN_SPACE_EVENTS]
    ++ `prob_space p` by PSET_TAC [random_variable_def]
    ++ RW_TAC std_ss [distribution_def, COND_PMF_EQ_COND_PROB, cond_prob_def, 
    	INTER_EMPTY, PROB_EMPTY, REAL_MUL_LZERO, REAL_DIV_LZERO, REAL_MUL_RZERO])   	 
 ++ FULL_SIMP_TAC std_ss [detailed_balance_equations_def, distribution_def, 
 	Trans_def, COND_PMF_EQ_COND_PROB]
 ++ NTAC 3 (POP_ASSUM MP_TAC)    	  	
 ++ POP_ASSUM (MP_TAC o Q.SPECL [`EL n (L:'b list)`, `EL (n + (1:num)) (L:'b list)`, `t + n`])
 ++ RW_TAC real_ss [ADD1]
 ++ METIS_TAC []);
 
val REVERSE_TH_JOINT_MUL = store_thm
  ("REVERSE_TH_JOINT_MUL",
  ``!X p s Linit Ltrans (t:num) (L:'b list) n. 
    th_dtmc X p s Linit Ltrans /\ (LENGTH L = n + 1) /\
    detailed_balance_equations (\i. distribution p (X t) {i}) X p s ==> 
   (prob p (BIGINTER (IMAGE (\k. PREIMAGE (X (t + k)) {EL k L} INTER p_space p) 
   	(count (n + 1)))) =
    prob p (BIGINTER (IMAGE (\k. PREIMAGE (X (t + k)) {EL k (REVERSE L)} INTER p_space p) 
    	(count (n + 1)))))``,
    RW_TAC std_ss [th_dtmc_def]
 ++ (MP_TAC o Q.SPECL [`X`, `p`, `s`, `Linit`, `Ltrans`]) HOMO_LEMMA
 ++ RW_TAC std_ss [th_dtmc_def]    
 ++ `mulcon (0,n) (\k.
         cond_pmf p (X (k + (t + 1))) (X (k + t))
           ({EL (k + 1) (REVERSE L)},{EL k (REVERSE L)})) =
     mulcon (0,n) (\k.
         cond_pmf p (X (k + (t + 1))) (X (k + t))
           ({EL (n - k - 1) L},{EL (n - k) L}))`
     by (MATCH_MP_TAC MULCON_POS_EQ ++ RW_TAC std_ss []
        ++ `EL (r + 1) (REVERSE L) = EL (n - r - 1) L`
        	by (`n + 1 - (r + 1) = SUC (n - r - 1)` by RW_TAC arith_ss [ADD1]
	           ++ FULL_SIMP_TAC std_ss [EL_REVERSE])
        ++ Suff `EL r (REVERSE L) = EL (n - r) L` >> METIS_TAC []
        ++ `n + 1 - r = SUC (n - r)` by RW_TAC arith_ss [ADD1]
        ++ (MP_TAC o Q.ISPECL [`r:num`, `(L:'b list)`]) EL_REVERSE
           ++ RW_TAC arith_ss [])
 ++ (MP_TAC o Q.ISPECL [`0:num`, `L:'b list`]) EL_REVERSE
 ++ RW_TAC arith_ss [GSYM ADD1, PRE]         
 ++ (MP_TAC o Q.SPECL [`X`, `p`, `s`, `t`, `n`, 
 	`(L:'b list)`, `Linit`, `Ltrans`]) MC_JOINT_PROB 
 ++ (MP_TAC o Q.SPECL [`X`, `p`, `s`, `t`, `n`,
 	`REVERSE (L:'b list)`, `Linit`, `Ltrans`]) MC_JOINT_PROB 	
 ++ RW_TAC arith_ss [ADD1]  
 ++ NTAC 4 (POP_ASSUM K_TAC)
 ++ (MP_TAC o Q.SPECL [`X`, `t`, `n`, `(\k. EL k (L:'b list))`, `p`, `s`]) REVERSE_JOINT_MUL
 ++ PSET_TAC [dtmc_def, mc_property_def]
 ++ FULL_SIMP_TAC arith_ss [COND_PMF_EQ_COND_PROB]
 ++ POP_ASSUM K_TAC
 ++ `!a b (c:real) . (a = b) ==> (a * c = b * c)` by RW_TAC real_ss []     
 ++ POP_ASSUM MATCH_MP_TAC
 ++ `!t k. cond_prob p
           (PREIMAGE (X (k + (t + 1))) {EL (n - (k + 1)) L} INTER p_space p)
           (PREIMAGE (X (k + t)) {EL (n - k) L} INTER p_space p) =
         cond_prob p
           (PREIMAGE (X (t + 1)) {EL (n - (k + 1)) L} INTER p_space p)
           (PREIMAGE (X t) {EL (n - k) L} INTER p_space p)`
      by RW_TAC std_ss [ADD_ASSOC] ++ POP_ORW
 ++ `!t k. cond_prob p
           (PREIMAGE (X (k + (t + 1))) {EL k L} INTER p_space p)
           (PREIMAGE (X (k + t)) {EL (k + 1) L} INTER p_space p) =
         cond_prob p
           (PREIMAGE (X (t + 1)) {EL k L} INTER p_space p)
           (PREIMAGE (X t) {EL (k + 1) L} INTER p_space p)`
      by RW_TAC std_ss [ADD_ASSOC] ++ POP_ORW
 ++ (MP_TAC o Q.SPECL [`(\k. cond_prob p
           (PREIMAGE ((X:num -> 'a -> 'b) (t + 1)) {EL k L} INTER p_space p)
           (PREIMAGE (X t) {EL (k + 1) L} INTER p_space p))`, `n`]) MULCON_SHIFT
 ++ RW_TAC arith_ss []  
 ++ MATCH_MP_TAC MULCON_POS_EQ
 ++ RW_TAC arith_ss []);

val REVERSE_JOINT = store_thm
  ("REVERSE_JOINT",
  ``!X p s Linit Ltrans (t:num) (L:'b list). 
    th_dtmc X p s Linit Ltrans /\ 
    detailed_balance_equations (\i. distribution p (X t) {i}) X p s ==> 
   (prob p (BIGINTER (IMAGE (\k. PREIMAGE (X (t + k)) {EL k L} INTER p_space p) 
   	(count (LENGTH L)))) =
    prob p (BIGINTER (IMAGE (\k. PREIMAGE (X (t + k)) {EL k (REVERSE L)} INTER p_space p) 
    	(count (LENGTH L)))))``,
    RW_TAC std_ss []
 ++ Cases_on `LENGTH L = 0`
 >> RW_TAC std_ss [COUNT_ZERO, IMAGE_EMPTY, BIGINTER_EMPTY]
 ++ `LENGTH L - 1 + 1 = LENGTH L` by RW_TAC arith_ss []
 ++ (MP_TAC o Q.SPECL [`X`, `p`, `s`, `Linit`, `Ltrans`, `t`, `L:'b list`, 
 	`LENGTH (L:'b list) - 1`]) REVERSE_TH_JOINT_MUL ++ RW_TAC std_ss []);

val RMC_JOINT_PROB = store_thm
  ("RMC_JOINT_PROB",
  ``!X p s Linit Ltrans (t:num) (L:'b list). rmc X p s Linit Ltrans ==>
  (prob p (BIGINTER (IMAGE (\k. PREIMAGE (X (t + k)) {EL k L} INTER p_space p) 
   	(count (LENGTH L)))) =
    prob p (BIGINTER (IMAGE (\k. PREIMAGE (X (t + k)) {EL k (REVERSE L)} INTER p_space p) 
    	(count (LENGTH L)))))``,
    RW_TAC std_ss [rmc_def]
 ++ (MP_TAC o Q.SPECL [`X`, `p`, `s`, `Linit`, `Ltrans`, `t`, `L:'b list`]) REVERSE_JOINT
 ++ RW_TAC std_ss [distribution_def]); 
 	 
(*val _ = export_theory();    *)

