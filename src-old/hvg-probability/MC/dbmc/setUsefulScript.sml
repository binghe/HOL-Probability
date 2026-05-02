(*val () = app load
 ["bossLib", "metisLib", "arithmeticTheory", "pred_setTheory", "realLib", "pairTheory", 
  "listTheory", "combinTheory", "transcTheory", "numLib", "prim_recTheory", "dep_rewrite",
  "extra_pred_setTools", "seqTheory"];

set_trace "Unicode" 0;*)

open HolKernel Parse boolLib bossLib metisLib numLib combinTheory subtypeTheory seqTheory
	pred_setTheory numLib extra_pred_setTheory arithmeticTheory realTheory dep_rewrite
	realLib pairTheory listTheory extra_pred_setTools transcTheory prim_recTheory;
	  
val _ = new_theory "setUseful";

infixr 0 ++ << || ORELSEC ## --> THENC;
infix 1 >> |->;

val !! = REPEAT;
val op++ = op THEN;
val op<< = op THENL;
val op|| = op ORELSE;
val op>> = op THEN1;
val POP_ORW = POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm]);

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

val IMAGE_SING = store_thm
 ("IMAGE_SING",
 ``!f x. IMAGE f {x} = {f x}``,
  RW_TAC std_ss [EXTENSION,IN_SING,IN_IMAGE] ++ METIS_TAC []);
  
val BIGINTER_SING = store_thm
 ("BIGINTER_SING",
  ``!P. BIGINTER {P} = P``,
  SIMP_TAC bool_ss [EXTENSION, IN_BIGINTER, IN_SING] THEN
  SIMP_TAC bool_ss [GSYM EXTENSION]);

val DISJOINT_DIFF = store_thm
 ("DISJOINT_DIFF", ``!s t. DISJOINT t (s DIFF t) /\ DISJOINT (s DIFF t) t``,
  RW_TAC std_ss [EXTENSION,DISJOINT_DEF,IN_INTER,NOT_IN_EMPTY,IN_DIFF]
  ++ METIS_TAC []);  
(* ------------------------------------------------------------------------- *)
(* Some definitions in setTheory and continued product                       *)
(* ------------------------------------------------------------------------- *)	
val count_mn_def = new_definition 
  ("count_mn_def", ``count_mn (m:num) (n:num) = {r | (m <= r) /\ (r <= n)}``);
   
(* ------------------------------------------------------------------------- *)
(* Some basic theorems related to setTheory                                  *)
(* ------------------------------------------------------------------------- *)	
val COUNT_ONE = store_thm 
  ("COUNT_ONE",
  ``count 1 = {0}``, RW_TAC real_ss [EXTENSION,IN_COUNT,IN_SING]);

val IN_COUNT_MN = store_thm
  ("IN_COUNT_MN",
  ``!m n r. r IN count_mn m n <=> (m <= r) /\ (r <= n)``,
    PSET_TAC [count_mn_def, EXTENSION]);

val COUNT_MN_COUNT = store_thm
  ("COUNT_MN_COUNT",
   ``!n. count_mn 0 n = count (SUC n)``,
   PSET_TAC [count_mn_def, EXTENSION] ++ ARITH_TAC);  

val COUNT_MN_ZERO = store_thm
  ("COUNT_MN_ZERO",
  ``count_mn 0 0 = {0:num}``,
    PSET_TAC [count_mn_def, GSPEC_EQ]);
    
val COUNT_MN_EMPTY = store_thm
  ("COUNT_MN_EMPTY",
  ``!m. (0 < m) ==> (count_mn m 0 = {})``,
    PSET_TAC [count_mn_def, EXTENSION, LESS_NOT_EQ]);

val COUNT_MN_SUCN = store_thm
  ("COUNT_MN_SUCN",
  ``!m n. m <= n ==> (count_mn m (SUC n) = count_mn m n UNION {SUC n})``,
    PSET_TAC [count_mn_def, UNION_DEF, EXTENSION]
 ++ RW_TAC arith_ss []);

val COUNT_MN_SING = store_thm
  ("COUNT_MN_SING", 
  ``!n. count_mn n n = {n}``,
   PSET_TAC [count_mn_def, GSPECIFICATION, EXTENSION] ++ RW_TAC arith_ss []);  
    
val COUNT_SUBSET = store_thm
  ("COUNT_SUBSET",
  ``!a b. (a <= b) ==> (count a SUBSET count b)``,
    PSET_TAC [count_def]
 ++ METIS_TAC [LESS_LESS_EQ_TRANS]);

val COUNT_NOT_EMPTY = store_thm
  ("COUNT_NOT_EMPTY",
  ``!n. (0 < n) ==> (count n <> {})``,
    INDUCT_TAC THEN RW_TAC std_ss [] THEN 
 Cases_on `n = 0` THEN1 RW_TAC std_ss [COUNT_ONE, NOT_SING_EMPTY] THEN 
 `(0:num) < n` by RW_TAC arith_ss [] THEN FULL_SIMP_TAC std_ss [] THEN
 KNOW_TAC ``count (SUC n) = (count n) UNION {n}`` THEN1 (
	RW_TAC std_ss [EXTENSION, UNION_DEF, IN_COUNT, IN_SING, GSPECIFICATION] THEN
			FULL_SIMP_TAC arith_ss []) THEN 
 RW_TAC std_ss [] THEN RW_TAC std_ss [IMAGE_UNION, IMAGE_SING] THEN CCONTR_TAC THEN
 RW_TAC std_ss [EMPTY_UNION]);

val COUNT_NOT_EMPTY = store_thm
  ("COUNT_NOT_EMPTY",
  ``!n. (0 < n) ==> (count n <> {})``,
    INDUCT_TAC THEN RW_TAC std_ss [] THEN 
 Cases_on `n = 0` THEN1 RW_TAC std_ss [COUNT_ONE, NOT_SING_EMPTY] THEN 
 `(0:num) < n` by RW_TAC arith_ss [] THEN FULL_SIMP_TAC std_ss [] THEN
 KNOW_TAC ``count (SUC n) = (count n) UNION {n}`` THEN1 (
	RW_TAC std_ss [EXTENSION, UNION_DEF, IN_COUNT, IN_SING, GSPECIFICATION] THEN
			FULL_SIMP_TAC arith_ss []) THEN 
 RW_TAC std_ss [] THEN RW_TAC std_ss [IMAGE_UNION, IMAGE_SING] THEN CCONTR_TAC THEN
 RW_TAC std_ss [EMPTY_UNION]);

val FINITE_SET_EXISTS_CARD = store_thm 
  ("FINITE_SET_EXISTS_CARD",   
  ``!s. FINITE s ==> ?n. n = CARD s``,
    Suff `(?n. n = CARD s) = (\s. ?n. n = CARD s) s`
 >> RW_TAC std_ss [] 
 ++ RW_TAC std_ss []);

val FINITE_SET_EXISTS_CARD = store_thm 
  ("FINITE_SET_EXISTS_CARD",   
  ``!s. FINITE s ==> ?n. n = CARD s``,
    Suff `(?n. n = CARD s) = (\s. ?n. n = CARD s) s`
 >> RW_TAC std_ss [] 
 ++ RW_TAC std_ss []);

val IMAGE_CONST = store_thm
  ("IMAGE_CONST",
  ``!s x. s <> {} ==> (IMAGE (\i. x) s = {x})``,    
    PSET_TAC [EXTENSION]
 ++ EQ_TAC >> RW_TAC std_ss []
 ++ RW_TAC std_ss [] ++ Q.EXISTS_TAC `x'` ++ RW_TAC std_ss []);
 
val BIGINTER_IMAGE_0 = store_thm
  ("BIGINTER_IMAGE_0",  
   (--`!A. (BIGINTER (IMAGE (\m. A (m:num)) (count 1)) = A 0)`--),  
    RW_TAC std_ss [IN_BIGUNION, IN_IMAGE, IMAGE_DEF, COUNT_ONE, 
    	GSPEC_EQ, IN_SING, GSPECIFICATION, EXTENSION, IN_BIGINTER]
 ++ EQ_TAC >> METIS_TAC [] ++ METIS_TAC []);
 
val BIGINTER_INDUCT_LAST = store_thm
  ("BIGINTER_INDUCT_LAST",
  (--`!(A: num -> ('a -> bool)) (k:num).
   (BIGINTER (IMAGE A (count (SUC k))) =
    (A k) INTER (BIGINTER (IMAGE A (count k))))`--),
    RW_TAC std_ss [EXTENSION, IN_BIGINTER_IMAGE, IN_INTER] 
 ++ EQ_TAC >> (RW_TAC std_ss [] 
    >> (POP_ASSUM (MP_TAC o Q.SPEC `k`) ++ PSET_TAC [IN_COUNT])
    ++ FULL_SIMP_TAC arith_ss [IN_COUNT])
 ++ RW_TAC std_ss [IN_COUNT]
 ++ Cases_on `y = k` >> RW_TAC std_ss []
 ++ FULL_SIMP_TAC arith_ss []);
 
val BIGINTER_INDUCT_0 = store_thm
  ("BIGINTER_INDUCT_0",
  (``!(A: num -> ('a -> bool)) (n: num) (k:num).
   (BIGINTER (IMAGE A (count (SUC k))) =
    (A 0) INTER (BIGINTER (IMAGE A (count_mn 1 k))))``),
    RW_TAC std_ss [EXTENSION, IN_BIGINTER_IMAGE, IN_INTER] 
 ++ EQ_TAC >> (RW_TAC std_ss [] 
    >> (POP_ASSUM (MP_TAC o Q.SPEC `0`) ++ PSET_TAC [IN_COUNT])
    ++ FULL_SIMP_TAC arith_ss [IN_COUNT]
    ++ PSET_TAC [IN_COUNT_MN]
    ++ Cases_on `y = 0` >> RW_TAC std_ss []
    ++ FULL_SIMP_TAC arith_ss [])
 ++ PSET_TAC [IN_COUNT_MN]
 ++ Cases_on `y = 0` >> RW_TAC std_ss []
 ++ FULL_SIMP_TAC arith_ss []);
 
val SUBSET_BIGINTER_SUBSET = store_thm
  ("SUBSET_BIGINTER_SUBSET",
  ``!s t f. t SUBSET s ==> BIGINTER (IMAGE f s) SUBSET BIGINTER (IMAGE f t)``,
    PSET_TAC [] ++ POP_ASSUM MP_TAC ++ POP_ASSUM (MP_TAC o Q.SPEC `f x'`) 
 ++ RW_TAC std_ss [] ++ METIS_TAC []);

val INTER_BIGINTER = store_thm
  ("INTER_BIGINTER",
  ``!s f g. BIGINTER (IMAGE f s) INTER BIGINTER (IMAGE g s) = 
  	    BIGINTER (IMAGE (\s. f s INTER g s) s)``,
    PSET_TAC [EXTENSION,IN_BIGINTER_IMAGE,IN_INTER]
 ++ EQ_TAC >> METIS_TAC [] ++ METIS_TAC []);

val INTER_INTER_BIGINTER = store_thm
  ("INTER_INTER_BIGINTER",
  ``!A B p s. B IN (s -> events p) /\ s <> {} ==>
   (BIGINTER (IMAGE (\k. (B k) INTER A) s) =
   A INTER (BIGINTER (IMAGE (\k. B k) s)))``,
    RW_TAC std_ss [IN_FUNSET, EXTENSION, IN_BIGINTER_IMAGE, IN_INTER, NOT_IN_EMPTY] 
 ++ EQ_TAC >> METIS_TAC [CHOICE_DEF] ++ RW_TAC std_ss []); 

val A_INTER_BIGUNION = store_thm
  ("A_INTER_BIGUNION",
  ``!A B p s. B IN (s -> events p) ==>
   (BIGUNION (IMAGE (\k. A INTER (B k)) s) =
   A INTER (BIGUNION (IMAGE (\k. B k) s)))``,
    PSET_TAC [GSPECIFICATION, EXTENSION]
 ++ EQ_TAC >> (RW_TAC std_ss []
    << [RW_TAC std_ss [],
        Q.EXISTS_TAC `k` ++ RW_TAC std_ss []])
 ++ RW_TAC std_ss []);    
 
val INTER_RINTER = store_thm
  ("INTER_RINTER",
   ``!A B C. A INTER B INTER C = (A INTER C) INTER (B INTER C)``,
   PSET_TAC [INTER_ASSOC] THEN
   `C INTER (B INTER C) = B INTER C` 
       by METIS_TAC [INTER_COMM, INTER_ASSOC, INTER_IDEMPOT] THEN
   RW_TAC std_ss []);

val INSERT_EQ_UNION_SING = store_thm
  ("INSERT_EQ_UNION_SING",
  ``!A e. (e INSERT A) = (A UNION {e})``,
    PSET_TAC [INSERT_DEF, UNION_DEF, GSPECIFICATION, EXTENSION, DISJ_COMM]);

val FINITE_COUNT_MN = store_thm
  ("FINITE_COUNT_MN",    
  ``!m n. FINITE (count_mn m n)``,
   RW_TAC std_ss []
 ++ `count_mn m n = count (SUC n) DIFF (count m)` 
        by (PSET_TAC [EXTENSION, count_mn_def] ++ RW_TAC arith_ss [])
 ++ METIS_TAC [FINITE_DIFF, FINITE_COUNT]);
 
val IMAGE_SET_NOT_EMPTY = store_thm 
  ("IMAGE_SET_NOT_EMPTY",
  ``!A (n:num). (0 < n) ==> ((IMAGE (\k. A (k:num)) (count n)) <> {})``,
	RW_TAC std_ss [] THEN CCONTR_TAC THEN RW_TAC std_ss [IMAGE_EQ_EMPTY] THEN 
	KNOW_TAC ``count n <> {}`` THEN1 (POP_ASSUM K_TAC THEN 
		RW_TAC std_ss [COUNT_NOT_EMPTY]) THEN 
	RW_TAC std_ss []);

val REAL_SUM_IMAGE_MONO_SET = store_thm
  ("REAL_SUM_IMAGE_MONO_SET",
   ``!f s t. (FINITE s /\ FINITE t /\ s SUBSET t /\ (!x. x IN t ==> (0:real) <= f x)) ==>
            REAL_SUM_IMAGE f s  <= REAL_SUM_IMAGE f t``,
     RW_TAC std_ss []
  ++ `t = s UNION (t DIFF s)` by RW_TAC std_ss [UNION_DIFF]
  ++ `FINITE (t DIFF s)` by RW_TAC std_ss [FINITE_DIFF]
  ++ `DISJOINT s (t DIFF s)` 
  	by (`DISJOINT s (t DIFF s)` by RW_TAC std_ss [DISJOINT_DEF, IN_DIFF, EXTENSION,
  		 GSPECIFICATION,NOT_IN_EMPTY,IN_INTER] ++ METIS_TAC [])
  ++ `REAL_SUM_IMAGE f t = REAL_SUM_IMAGE f s + REAL_SUM_IMAGE f (t DIFF s)` 
  	by METIS_TAC [REAL_SUM_IMAGE_DISJOINT_UNION]
  ++ POP_ORW
  ++ METIS_TAC [REAL_LE_ADD2, REAL_LE_REFL, REAL_ADD_RID, REAL_SUM_IMAGE_POS, IN_DIFF]);
 
val REAL_SUM_IMAGE_DIFF = store_thm
  ("REAL_SUM_IMAGE_DIFF",    
  ``!s t. FINITE s /\ t SUBSET s ==> 
  	!(f:'b -> real). SIGMA f s = SIGMA f t + SIGMA f (s DIFF t)``,
    RW_TAC std_ss []
 ++ `FINITE t` by METIS_TAC [SUBSET_FINITE]
 ++ `FINITE (s DIFF t)` by PSET_TAC [FINITE_DIFF]
 ++ `DISJOINT t (s DIFF t)` by PSET_TAC [DISJOINT_DIFF]
 ++ (MP_TAC o Q.ISPECL [`(t:'b -> bool)`, `s DIFF (t:'b -> bool)`]) 
 	REAL_SUM_IMAGE_DISJOINT_UNION
 ++ RW_TAC std_ss [UNION_DIFF]);  
 
val CARD_DIFF_SUM = store_thm
  ("CARD_DIFF_SUM",
  ``!s t. FINITE s /\ t SUBSET s ==> (CARD t + CARD (s DIFF t) = CARD s)``,
    RW_TAC std_ss [] ++ `FINITE t` by METIS_TAC [SUBSET_FINITE]
 ++ `FINITE (s DIFF t)` by PSET_TAC [FINITE_DIFF]
 ++ `(s DIFF t) INTER t = {}` by METIS_TAC [DISJOINT_DIFF, DISJOINT_DEF]
 ++ ASSUME_TAC ((UNDISCH o Q.SPEC `s DIFF t`) CARD_UNION) 
 ++ POP_ASSUM (MP_TAC o Q.SPEC `t`) 
 ++ PSET_TAC [UNION_DIFF, CARD_DEF, ADD_0, ADD_COMM]);	

val CARD_GT_2 = store_thm
  ("CARD_GT_2",
  ``!a b s. FINITE s /\ a IN s /\ b IN s /\ a <> b ==> 2 <= CARD s``,
    RW_TAC std_ss []
 ++ Cases_on `s DELETE a DELETE b = {}`
 >> (RW_TAC std_ss [] ++ `CARD (s DELETE a DELETE b) = 0` by METIS_TAC [CARD_DEF]
    ++ `a NOTIN (s DELETE a DELETE b)` by PSET_TAC []
    ++ `a IN (s DELETE b)` by PSET_TAC [IN_DELETE]
    ++ `a INSERT s DELETE a DELETE b = s DELETE b` 
    	by METIS_TAC [DELETE_COMM, INSERT_DELETE]
    ++ `CARD (a INSERT (s DELETE a DELETE b)) = SUC 0` by METIS_TAC [CARD_INSERT, FINITE_DELETE]
    ++ PSET_TAC [] ++ `b NOTIN (s DELETE b)` by PSET_TAC []
    ++ `CARD (b INSERT (s DELETE b)) = SUC (CARD (s DELETE b))` 
    	by METIS_TAC [CARD_INSERT, FINITE_DELETE] 
    ++ PSET_TAC [INSERT_DELETE, ADD1, LESS_EQ_REFL])
 ++ `1 <= CARD (s DELETE a DELETE b)` 
 	by (SPOSE_NOT_THEN STRIP_ASSUME_TAC 
 	   ++ `CARD (s DELETE a DELETE b) = 0` by RW_TAC arith_ss []
 	   ++ METIS_TAC [CARD_EQ_0, FINITE_DELETE])
 ++ `a NOTIN (s DELETE a DELETE b)` by PSET_TAC []
 ++ `a IN (s DELETE b)` by PSET_TAC [IN_DELETE]
 ++ `a INSERT s DELETE a DELETE b = s DELETE b` 
    	by METIS_TAC [DELETE_COMM, INSERT_DELETE]
 ++ `CARD (a INSERT (s DELETE a DELETE b)) = SUC (CARD (s DELETE a DELETE b))` 
 	by METIS_TAC [CARD_INSERT, FINITE_DELETE]
 ++ PSET_TAC []	
 ++ `SUC 1 <= CARD (s DELETE b)` by METIS_TAC [LESS_EQ_MONO, ADD1] 	
 ++ `s DELETE b SUBSET s` by PSET_TAC [] 
 ++ `CARD (s DELETE b) <= CARD s` by PSET_TAC [CARD_SUBSET]
 ++ RW_TAC arith_ss [LESS_EQ_TRANS]); 

val LENGTH_ONE = store_thm 
  ("LENGTH_ONE",
  ``!L. (LENGTH L = 1) <=> ?x. L = [x]``,
    GEN_TAC ++ MP_TAC (Q.SPEC `L` list_CASES) ++ STRIP_TAC
 >> (ASM_REWRITE_TAC [LENGTH, GSYM NOT_CONS_NIL] ++ ARITH_TAC)
 ++ ASM_REWRITE_TAC [LENGTH, ONE, INV_SUC_EQ, LENGTH_NIL]
 ++ METIS_TAC [list_11]);
  
val FINITE_RND_PATH_SET = store_thm
  ("FINITE_RND_PATH_SET",
  ``!s. FINITE s ==>
           !n. FINITE {L | EVERY (\x. x IN s) L /\ (LENGTH L = n + 1)}``,
    RW_TAC std_ss [] ++ Induct_on `n`
 >> (MATCH_MP_TAC (ISPEC ``HD`` FINITE_INJ) ++ Q.EXISTS_TAC `s`
    ++ RW_TAC arith_ss [LENGTH_ONE,HD,EVERY_DEF,INJ_DEF] 
    ++ PSET_TAC[HD,EVERY_DEF])
 ++ MATCH_MP_TAC (ISPEC ``\L. TL L, HD L`` FINITE_INJ)
 ++ POP_ASSUM (fn L => POP_ASSUM (ASSUME_TAC o MATCH_MP FINITE_CROSS o CONJ L))
 ++ POP_ASSUM (fn h => EXISTS_TAC (rand (concl h)) ++ REWRITE_TAC[h,INJ_DEF])
 ++ FULL_SIMP_TAC arith_ss [ADD,LENGTH_CONS] ++ PSET_TAC[IN_CROSS,HD,EVERY_DEF,TL,LENGTH]);

val REAL_SUM_IMAGE_EXISTS_POS = store_thm
  ("REAL_SUM_IMAGE_EXISTS_POS",
   ``!f s. FINITE s /\ (!x. x IN s ==> 0 <= f x) /\ (?x. x IN s /\ 0 < f x) ==>
	(0:real) < SIGMA f s``,
    RW_TAC std_ss []	
 ++ `s = {x} UNION (s DIFF {x})` by PSET_TAC [UNION_DIFF]  
 ++ POP_ORW 
 ++ DEP_REWRITE_TAC [REAL_SUM_IMAGE_DISJOINT_UNION, REAL_SUM_IMAGE_SING]	
 ++ RW_TAC std_ss [FINITE_SING, FINITE_DIFF, DISJOINT_DIFF]
 ++ MATCH_MP_TAC REAL_LTE_ADD
 ++ RW_TAC std_ss []
 ++ MATCH_MP_TAC REAL_SUM_IMAGE_POS
 ++ RW_TAC std_ss [FINITE_DIFF, IN_DIFF]); 

(* 
val REAL_SUM_IMAGE_SPOS = prove
  (``!f s. FINITE s  /\ (!x. x IN s ==> 0 <= f x) /\ (?x. x IN s /\ 0 < f x) ==>
  	(0:real) < SIGMA f s``,
    RW_TAC std_ss []	
 ++ `s = {x} UNION (s DIFF {x})` by PSET_TAC [UNION_DIFF]  
 ++ POP_ORW 
 ++ DEP_REWRITE_TAC [REAL_SUM_IMAGE_DISJOINT_UNION, REAL_SUM_IMAGE_SING]	
 ++ RW_TAC std_ss [FINITE_SING, FINITE_DIFF, DISJOINT_DIFF]
 ++ MATCH_MP_TAC REAL_LTE_ADD
 ++ RW_TAC std_ss []
 ++ MATCH_MP_TAC REAL_SUM_IMAGE_POS
 ++ RW_TAC std_ss [FINITE_DIFF, IN_DIFF]); *)
(* ------------------------------------------------------------------------- *)
(* Some definitions in setTheory and continued product                       *)
(* ------------------------------------------------------------------------- *)	
val mulcon_def = Define`
  (mulcon (n, 0) f = (1:real)) /\
  (mulcon (n, SUC m) f = mulcon (n,m) f * f (n + m))`;    
  
(* ------------------------------------------------------------------------- *)
(*            Some basic theorems related to product defintion               *)
(* ------------------------------------------------------------------------- *)	
val MULCON_POS_EQ = store_thm
  ("MULCON_POS_EQ",
  ``!f g (m:num) n. (!r. m <= r /\ r < (m + n) ==> (f r = g r)) ==> 
	(mulcon (m,n) f = mulcon (m,n) g)``,
        EVERY [GEN_TAC, GEN_TAC, GEN_TAC] THEN INDUCT_TAC THEN REWRITE_TAC[mulcon_def] THEN 
	DISCH_TAC THEN BINOP_TAC THEN FULL_SIMP_TAC arith_ss []);

val MULCON_ONE = store_thm 
  ("MULCON_ONE", 
  ``!f. mulcon (0, 1) f = f 0``,
   REWRITE_TAC [ONE] ++ RW_TAC std_ss [mulcon_def, REAL_MUL_LID]);
   	
val MULCON_TWO = store_thm
  ("MULCON_TWO",  
    (--`!f n p. mulcon (0,n) f * mulcon (n,p) f = 
        mulcon (0,n + p) f`--),  
    NTAC 2 (GEN_TAC) ++ INDUCT_TAC >> RW_TAC std_ss [mulcon_def, REAL_MUL_RID] 
 ++ ASM_REWRITE_TAC [mulcon_def, ADD_CLAUSES] ++ RW_TAC std_ss [REAL_MUL_ASSOC]); 
 
val MULCON_1 = store_thm
  ("MULCON_1",  
    (--`!f m. mulcon (m,1) f = f m`--),  
    REWRITE_TAC[num_CONV (--`1:num`--)] 
 ++ RW_TAC std_ss [mulcon_def, REAL_MUL_RZERO, REAL_MUL_LID]);

val MULCON_FT = store_thm
  ("MULCON_FT",  
    (--`!f t (n:num). 
   	(mulcon (0, n) (\k. f (t + k)) = 
    	 mulcon (t, n) (\k. f k))`--),  
    Induct_on `n` ++ RW_TAC std_ss [mulcon_def]);  	

val MULCON_MUL = store_thm
  ("MULCON_MUL",
  ``!m n f. 0 < n ==> (mulcon (m, n) f = f m * mulcon (m + 1, n - 1) f)``,
    Induct_on `n`
 >> RW_TAC std_ss []
 ++ RW_TAC arith_ss [mulcon_def]
 ++ Cases_on `n = 0`
 >> RW_TAC arith_ss [mulcon_def, REAL_MUL_LID, REAL_MUL_RID]
 ++ `mulcon (m,n) f = f m * mulcon (m + 1,n - 1) f` by FULL_SIMP_TAC arith_ss []
 ++ POP_ORW ++ `n = SUC (n - 1)` by RW_TAC arith_ss []
 ++ `mulcon (m + 1,n) f = mulcon (m + 1,SUC (n - 1)) f` by METIS_TAC []
 ++ POP_ORW ++ RW_TAC arith_ss [mulcon_def, REAL_MUL_ASSOC]);
 
val MULCON_SHIFT = store_thm
  ("MULCON_SHIFT",  
  ``!f (n:num). mulcon (0, n) (\k. f k) = mulcon (0, n) (\k. f (n - k - 1))``,  
    GEN_TAC ++ INDUCT_TAC >> RW_TAC std_ss [mulcon_def]
 ++ RW_TAC std_ss [ADD1] ++ `!(k:num). n + 1 - k - 1 = n - k` by ARITH_TAC
 ++ POP_ORW ++ (MP_TAC o Q.SPECL [`(\(k:num). f (n - k))`, `1`, `n`]) MULCON_TWO
 ++ RW_TAC std_ss [] 
 ++ FULL_SIMP_TAC std_ss [ADD_COMM, MULCON_1] ++ POP_ASSUM (MP_TAC o GSYM)
 ++ `!(k:num). n - (1 + k) = n - k - 1` by ARITH_TAC 
 ++ (MP_TAC o Q.SPECL [`(\(k:num). f (n - k))`, `1`, `n`]) MULCON_FT 
 ++ RW_TAC std_ss [GSYM ADD1, mulcon_def, REAL_MUL_COMM]);

val MULCON_SPLIT = store_thm
  ("MULCON_SPLIT",  
    (--`!n f g. mulcon (0,n) f * mulcon (0,n) g = 
        mulcon (0,n) (\k. f k * g k)`--),  
    INDUCT_TAC >> RW_TAC std_ss [mulcon_def, REAL_MUL_RID] 
 ++ RW_TAC std_ss [mulcon_def] 
 ++ `!(a:real) b c d. a * b * (c * d) = a * c * (b * d)` 
 	by METIS_TAC [REAL_MUL_ASSOC, REAL_MUL_COMM]
 ++ POP_ORW ++RW_TAC std_ss []); 

val MULCON_MUL = store_thm
  ("MULCON_MUL",
  ``!m n f. 0 < n ==> (mulcon (m, n) f = f m * mulcon (m + 1, n - 1) f)``,
    Induct_on `n`
 >> RW_TAC std_ss []
 ++ RW_TAC arith_ss [mulcon_def]
 ++ Cases_on `n = 0`
 >> RW_TAC arith_ss [mulcon_def, REAL_MUL_LID, REAL_MUL_RID]
 ++ `mulcon (m,n) f = f m * mulcon (m + 1,n - 1) f` by FULL_SIMP_TAC arith_ss []
 ++ POP_ORW ++ `n = SUC (n - 1)` by RW_TAC arith_ss []
 ++ `mulcon (m + 1,n) f = mulcon (m + 1,SUC (n - 1)) f` by METIS_TAC []
 ++ POP_ORW ++ RW_TAC arith_ss [mulcon_def, REAL_MUL_ASSOC]);

val MULCON_EQ_MUL_TWO = store_thm
  ("MULCON_EQ_MUL_TWO",
  ``!f m n p. mulcon (m, n + p) f = mulcon (m, p) f * mulcon (m + p, n) f``,
    Induct_on `n` 
 >> RW_TAC std_ss [mulcon_def, REAL_MUL_RID]
 ++ RW_TAC std_ss [ADD, mulcon_def]
 ++ METIS_TAC [ADD_COMM, ADD_ASSOC, REAL_MUL_ASSOC]);

val MULCON_TRE_SING = store_thm
  ("MULCON_TRE_SING",
  ``!(f:num -> real) n k. k < n ==> 
        (mulcon (0, n) f = mulcon (0, k) f * (f k) * mulcon (k + 1, n - k - 1) f)``,
    RW_TAC std_ss []
 ++ (MP_TAC o GSYM o Q.SPECL [`f`, `k`, `n - k`]) MULCON_TWO
 ++ RW_TAC arith_ss []
 ++ (MP_TAC o GSYM o Q.SPECL [`f`, `k`, `n - k - 1`, `1`]) MULCON_EQ_MUL_TWO
 ++ RW_TAC arith_ss [GSYM REAL_MUL_ASSOC, MULCON_1]);
 
val MULCON_CONST = store_thm
  ("MULCON_CONST",
  ``!c m n. mulcon (m, n) (\i. c) = c pow n``,
    Induct_on `n`
 >> RW_TAC std_ss [mulcon_def, pow]    
 ++ RW_TAC std_ss [mulcon_def, pow, REAL_MUL_COMM]);
  
val REAL_DIV_RSHIFT = store_thm
   ("REAL_DIV_RSHIFT",
   ``!x y (z:real). y <> 0 ==> ((x * y = z) = (x = z / y))``,
    RW_TAC std_ss [] 
 ++ EQ_TAC >> METIS_TAC [real_div, GSYM REAL_MUL_ASSOC, REAL_MUL_COMM, REAL_MUL_LINV, REAL_MUL_LID] 
 ++ METIS_TAC [real_div, GSYM REAL_MUL_ASSOC, REAL_MUL_LINV, REAL_MUL_RID]);       

val REAL_SUB_DIV = store_thm
  ("REAL_SUB_DIV",
  ``!(a:real) b c. a <> 0 ==> ((b - c) / a = b / a - c / a)``,
    RW_TAC std_ss []
 ++ Suff `(b - c) / a * a = (b / a - c / a) * a` >> METIS_TAC [REAL_EQ_RMUL_IMP]
 ++ RW_TAC std_ss [REAL_DIV_RMUL, REAL_SUB_RDISTRIB]);
 
val REAL_NEG_SUB_DIV = store_thm
  ("REAL_NEG_SUB_DIV", 
  ``!(a:real) b c d. (a - b) / (c - d) = (b - a) / (d - c)``,
    RW_TAC std_ss []
 ++ Cases_on `c = d` 
 >> RW_TAC std_ss [REAL_SUB_REFL, real_div, REAL_INV_0, REAL_MUL_RZERO]
 ++ `!(c:real) d. c <> d ==> (c - d <> 0) /\ (d - c <> 0)` 
 	by METIS_TAC [REAL_SUB_0] 	
 ++ `(b - a) / (d - c) = -(a - b) / -(c - d)` by RW_TAC std_ss [REAL_NEG_SUB]
 ++ RW_TAC std_ss [real_div, GSYM REAL_NEG_INV, REAL_NEG_MUL2]);   

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
    
val SEQ_CMUL = store_thm
  ("SEQ_CMUL",
  ``!f l (c:real). f --> l ==> (\n. c * f n) --> (c * l)``,
    RW_TAC std_ss []
 ++ `(\n. c * f n) = (\n. (\n. c) n * f n)` by RW_TAC std_ss []
 ++ POP_ORW ++ MATCH_MP_TAC SEQ_MUL
 ++ RW_TAC std_ss [SEQ_CONST]);

val LIM_CMUL = store_thm
  ("LIM_CMUL",
  ``!f l (c:real). f --> l ==> (lim (\n. c * f n) = c * l)``,
    METIS_TAC [TEND2LIM, SEQ_CMUL]);

val LIM_SUC = store_thm
  ("LIM_SUC",
  ``!f l. f --> l ==> (lim (\n. f (SUC n)) = lim (\n. f n))``,
    RW_TAC std_ss []
 ++ `(\n. f (SUC n)) --> l` by METIS_TAC [SEQ_SUC]
 ++ METIS_TAC [TEND2LIM]);
 
 val LIM_SUC_SUC = store_thm
  ("LIM_SUC_SUC",
  ``!f l. f --> l ==> (lim (\n. f n) = lim (\n. f (SUC (n + 1))))``,
    RW_TAC std_ss []
 ++ `lim (\n. f n) = lim (\n. f (SUC n))` by METIS_TAC [LIM_SUC]   
 ++ POP_ORW
 ++ `lim (\n. f (SUC (n + 1))) = lim (\n. (\n. f (n + 1)) (SUC n))` 
 	by RW_TAC std_ss [ADD]
 ++ `lim (\n. f (SUC n)) = lim (\n. (\n. f (n + 1)) n)` by RW_TAC std_ss [ADD1]	
 ++ NTAC 2 (POP_ORW) ++ MATCH_MP_TAC (GSYM LIM_SUC) 
 ++ Q.EXISTS_TAC `l` ++ RW_TAC std_ss [GSYM ADD1]
 ++ ONCE_ASM_REWRITE_TAC [GSYM SEQ_SUC]
 ++ RW_TAC std_ss []);
 
val REAL_ADD_POW_2 = store_thm
  ("REAL_ADD_POW_2", 
   ``!(a:real) b. (a + b) pow 2 = a pow 2 + b pow 2 + 2 * a * b``,
    RW_TAC real_ss [POW_2,REAL_ADD_LDISTRIB,REAL_ADD_RDISTRIB,REAL_ADD_ASSOC]
    ++ REAL_ARITH_TAC); 
   
 val _ = export_theory();
