<html>
<head>
</head>

<body>
<pre>
(* ========================================================================= *)
(*                                                                           *)
(*                 Formalization of Birth-Death Process                      *)
(*             This code is developed using HOL4 kanaskas 7.                 *)
(*                                                                           *)
(*                   (c) Copyright, Liya Liu, 2013                           *)
(*                       Hardware Verification Group,                        *)
(*                       Concordia University                                *)
(*                                                                           *)
(*                                                                           *)
(*                      Last update: April 10, 2013                          *)
(*                                                                           *)
(* ========================================================================= *)
val () = app load
 ["bossLib", "metisLib", "arithmeticTheory", "pred_setTheory", "realLib", "seqTheory",
 	"pairTheory", "combinTheory", "numLib", "dep_rewrite",
 	"prim_recTheory", "probabilityTheory", "cond_probTheory", "extra_pred_setTools",
 	"dtmcBasicTheory", "Tactic", "setUsefulTheory", "cdtmcTheory"];

set_trace "Unicode" 0;

open HolKernel Parse boolLib bossLib metisLib numLib combinTheory subtypeTheory
	pred_setTheory numLib seqTheory dep_rewrite cdtmcTheory
     extra_pred_setTheory arithmeticTheory realTheory realLib pairTheory extra_pred_setTools
      prim_recTheory extrealTheory probabilityTheory cond_probTheory 
      dtmcBasicTheory Tactic setUsefulTheory;
                       
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

fun def_nth_conj i def = List.nth (strip_conj (rhs (concl (SPEC_ALL def))), i-1);

fun DEF_NTH_CONJS is def =
  GEN_ALL (prove(mk_imp(lhs (concl (SPEC_ALL def)),list_mk_conj (List.map (fn i => def_nth_conj i def) is)),SIMP_TAC std_ss [def] ++ METIS_TAC[]));
  
val DBLt_def = Define `
    DBLt (a:num -> real) (b:num -> real) (d:num -> real) t i j = 
    if (i = (0:num)) /\ (j = 0) then (a 0):real else 
    if (i = 0) /\ (j = 1) then b 0 else
    if (0 < i) /\ (i - j = 1) then d i else
    if (0 < i) /\ (i = j) then a i else
    if (0 < i) /\ (j - i = 1) then b i else 0`;      

(*******************************************************************************)
(*                  Definition of Birth_Death Process Model     	           *)
(*******************************************************************************)
val DB_model_def = Define `
    DB_model (X :num -> 'a -> num) p a b d n Linit = 
    APERIODIC_MC X p (count n, POW (count n)) Linit (DBLt a b d) /\ 
    IRREDUCIABLE_MC X p (count n, POW (count n)) Linit (DBLt a b d) /\
    1 < n /\ (a 0 + b 0 = 1) /\ 
    (!j. 0 < j /\ j < n ==> (a j + b j + d j = (1:real))) /\
    (!j. j < n ==> 0 < a j /\ 0 < b j /\ 0 < d j)`;

val REAL_DIV_MUL_ADD = prove
  (``!(a:real) b c. 0 < b /\ 0 < c /\ 0 < 1 - b /\ (a = b * a + c * d) ==> 
	(d = (1 - b) / c * (b * a + c * d))``,
    RW_TAC std_ss []
 ++ POP_ASSUM (MP_TAC o GSYM) ++ RW_TAC std_ss []
 ++ MATCH_MP_TAC REAL_EQ_LMUL_IMP
 ++ Q.EXISTS_TAC `c` ++ RW_TAC std_ss []
 >> METIS_TAC [REAL_LT_LE]
 ++ RW_TAC std_ss [REAL_MUL_ASSOC]
 ++ DEP_REWRITE_TAC [REAL_DIV_LMUL]
 ++ RW_TAC std_ss []
 >> METIS_TAC [REAL_LT_LE]
 ++ RW_TAC std_ss [REAL_SUB_RDISTRIB, REAL_EQ_SUB_LADD, REAL_MUL_LID, REAL_ADD_COMM]);
 
val DB_LIM_0 = prove
  (``!X p a b d n i Linit.                      
	DB_model X p a b d n Linit ==> 
	(lim (\n. prob p (PREIMAGE (X n) {1} INTER p_space p)) = 
	 (b 0 / d 1) * 
	 lim (\n. prob p (PREIMAGE (X n) {0} INTER p_space p)))``,
    PSET_TAC [DB_model_def]
 ++ `stationary_distribution p X (\i. lim (\n. prob p (PREIMAGE (X n) {i} INTER p_space p)))
 	 (count n, POW (count n))` by METIS_TAC [STEADY_PROB] 
 ++ PSET_TAC [stationary_distribution_def, measureTheory.space_def, IN_COUNT_MN] 
 ++ Know `lim (\n. prob p (PREIMAGE (X n) {0} INTER p_space p)) =
 	a 0 * lim (\n. prob p (PREIMAGE (X n) {0} INTER p_space p)) + 
 	d 1 * lim (\n. prob p (PREIMAGE (X n) {1} INTER p_space p))`
 >> (POP_ASSUM (MP_TAC o Q.SPEC `0`)  ++ RW_TAC arith_ss []
    ++ POP_ASSUM (MP_TAC o Q.SPEC `0`) ++ DISCH_TAC 
    ++ `SIGMA (\i'.  lim (\n. prob p (PREIMAGE (X n) {i'} INTER p_space p)) *
               Trans X p (count n,POW (count n)) 0 1 i' 0) (count n) =
        SIGMA (\i'.  lim (\n. prob p (PREIMAGE (X n) {i'} INTER p_space p)) *
               cond_prob p (PREIMAGE (X 1) {0} INTER p_space p)
                 (PREIMAGE (X 0) {i'} INTER p_space p)) (count n)`
        by (MATCH_MP_TAC REAL_SUM_IMAGE_EQ 
           ++ RW_TAC arith_ss [Trans_def, FINITE_COUNT, measureTheory.space_def, IN_COUNT])
    ++ Suff `SIGMA (\i'.  lim (\n. prob p (PREIMAGE (X n) {i'} INTER p_space p)) *
               cond_prob p (PREIMAGE (X 1) {0} INTER p_space p)
                 (PREIMAGE (X 0) {i'} INTER p_space p)) (count n) =
        a 0 * lim (\n. prob p (PREIMAGE (X n) {0} INTER p_space p)) +
        d 1 * lim (\n. prob p (PREIMAGE (X n) {1} INTER p_space p))` 
    >> METIS_TAC []
    ++ NTAC 2 (POP_ASSUM K_TAC)
    ++ `count n = {0} UNION {1} UNION count_mn 2 (n - 1)` 
    	by (PSET_TAC [count_def, count_mn_def, EXTENSION] ++ RW_TAC arith_ss [])   
    ++ POP_ORW ++ DEP_REWRITE_TAC [REAL_SUM_IMAGE_DISJOINT_UNION, REAL_SUM_IMAGE_SING]
    ++ PSET_TAC [FINITE_UNION, FINITE_SING, FINITE_COUNT_MN, IN_COUNT_MN]
    ++ `SIGMA (\i'. lim (\n'. prob p (PREIMAGE (X n') {i'} INTER p_space p)) *
         cond_prob p (PREIMAGE (X 1) {0} INTER p_space p)
           (PREIMAGE (X 0) {i'} INTER p_space p)) (count_mn 2 (n - 1)) = 0`
           by ((MP_TAC o Q.ISPEC `count_mn 2 (n - 1)`) (GSYM REAL_SUM_IMAGE_0)
              ++ RW_TAC std_ss [FINITE_COUNT_MN] ++ POP_ORW
              ++ MATCH_MP_TAC REAL_SUM_IMAGE_EQ 
              ++ RW_TAC std_ss [FINITE_COUNT_MN, IN_COUNT_MN]
              ++ Suff `cond_prob p (PREIMAGE (X 1) {0} INTER p_space p)
		      (PREIMAGE (X 0) {x} INTER p_space p) = 0` >> RW_TAC std_ss [REAL_MUL_RZERO]
              ++ Cases_on `prob p (PREIMAGE (X 0) {x} INTER p_space p) = 0`
              >> (MP_REWRITE_TAC COND_PROB_ZERO 
                 ++ PSET_TAC [APERIODIC_MC_def, th_dtmc_def]		      
                 << [PSET_TAC [dtmc_def, mc_property_def, random_variable_def],
                     MATCH_MP_TAC DTMC_EVENTS 
                     ++ MAP_EVERY Q.EXISTS_TAC [`(count n, POW (count n))`, `Linit`, `DBLt a b d`]
                     ++ RW_TAC std_ss [],
                     MATCH_MP_TAC DTMC_EVENTS 
                     ++ MAP_EVERY Q.EXISTS_TAC [`(count n, POW (count n))`, `Linit`, `DBLt a b d`]
                     ++ RW_TAC std_ss []])
              ++ PSET_TAC [APERIODIC_MC_def, th_dtmc_def, dtmc_def, DBLt_def,
              		 measureTheory.space_def, distribution_def, Trans_def,
              		 COND_PMF_EQ_COND_PROB]
              ++ NTAC 13 (POP_ASSUM MP_TAC) ++ POP_ASSUM (MP_TAC o Q.SPECL [`x`, `0`, `0`])
              ++ RW_TAC arith_ss []) 
    ++ RW_TAC std_ss [REAL_ADD_RID] ++ POP_ASSUM K_TAC
    ++ (MP_TAC o Q.ISPECL [`X:num -> 'a -> num`, 
                `p: ('a -> bool) # (('a -> bool) -> bool) # (('a -> bool) -> real)`, 
                `(count (n:num), POW (count n))`, `Linit:num -> real`, 
                `(DBLt (a:num -> real) (b:num -> real) (d:num -> real):num -> num -> num -> real)`,
                `0:num`]) APERIODIC_MC_POS_PROB 
    ++ RW_TAC arith_ss [measureTheory.space_def, IN_COUNT]
    ++ `prob p (PREIMAGE (X 0) {0} INTER p_space p) <> 0` by METIS_TAC [REAL_LT_IMP_NE]
    ++ `cond_prob p (PREIMAGE (X 1) {0} INTER p_space p)
       (PREIMAGE (X 0) {0} INTER p_space p) = a 0`
       by (PSET_TAC [APERIODIC_MC_def, th_dtmc_def, dtmc_def, DBLt_def, measureTheory.space_def, 
              		 distribution_def, Trans_def, COND_PMF_EQ_COND_PROB]
          ++ NTAC 12 (POP_ASSUM MP_TAC) ++ POP_ASSUM (MP_TAC o Q.SPECL [`0`, `0`, `0`])
          ++ RW_TAC arith_ss [])
    ++ (MP_TAC o Q.ISPECL [`X:num -> 'a -> num`, 
                `p: ('a -> bool) # (('a -> bool) -> bool) # (('a -> bool) -> real)`, 
                `(count (n:num), POW (count n))`, `Linit:num -> real`, 
                `(DBLt (a:num -> real) (b:num -> real) (d:num -> real):num -> num -> num -> real)`,
                `1:num`]) APERIODIC_MC_POS_PROB 
    ++ RW_TAC arith_ss [measureTheory.space_def, IN_COUNT]
    ++ `prob p (PREIMAGE (X 0) {1} INTER p_space p) <> 0` by METIS_TAC [REAL_LT_IMP_NE]
    ++ `cond_prob p (PREIMAGE (X 1) {0} INTER p_space p)
       (PREIMAGE (X 0) {1} INTER p_space p) = d 1`
       by (PSET_TAC [APERIODIC_MC_def, th_dtmc_def, dtmc_def, DBLt_def, measureTheory.space_def, 
              		 distribution_def, Trans_def, COND_PMF_EQ_COND_PROB]
          ++ NTAC 15 (POP_ASSUM MP_TAC) ++ POP_ASSUM (MP_TAC o Q.SPECL [`1`, `0`, `0`])
          ++ RW_TAC arith_ss []) 
    ++ RW_TAC std_ss [REAL_MUL_COMM]) ++ RW_TAC std_ss []
 ++ `a 0 = 1 - b 0` by METIS_TAC [REAL_EQ_SUB_LADD] ++ ONCE_ASM_REWRITE_TAC []
 ++ `b 0 = 1 - a 0` by METIS_TAC [REAL_EQ_SUB_LADD, REAL_ADD_COMM] ++ POP_ORW 
 ++ MATCH_MP_TAC REAL_DIV_MUL_ADD ++ POP_ASSUM K_TAC
 ++ RW_TAC arith_ss [] 
 ++ `1 - a 0 = b 0` by METIS_TAC [REAL_EQ_SUB_LADD, REAL_ADD_COMM] 
 ++ RW_TAC arith_ss []);

val COUNT_SPLIT_I = prove
  (``!i n. i + 1 < n /\ 0 < i ==> (count n = 
  	{i - 1} UNION {i} UNION {i + 1} UNION (count n DIFF {i - 1; i; i + 1}))``,
    PSET_TAC [count_def, IN_DIFF, EXTENSION] ++ RW_TAC arith_ss []);

val DB_ZERO_CASE = prove
  (``!X p a b d n i Linit.                      
	DB_model X p a b d n Linit /\ i + 1 < n /\ 0 < i /\ x < n /\
	x <> i - 1 /\ x <> i /\ x <> i + 1 ==> 
	(cond_prob p (PREIMAGE (X 1) {i} INTER p_space p)
       (PREIMAGE (X 0) {x} INTER p_space p) = 0)``,
    RW_TAC std_ss [DB_model_def]        
 ++ `i < n` by RW_TAC arith_ss []
 ++ (MP_TAC o Q.ISPECL [`X:num -> 'a -> num`, 
                `p: ('a -> bool) # (('a -> bool) -> bool) # (('a -> bool) -> real)`, 
                `(count (n:num), POW (count n))`, `Linit:num -> real`, 
                `(DBLt (a:num -> real) (b:num -> real) (d:num -> real):num -> num -> num -> real)`,
                `x:num`]) APERIODIC_MC_POS_PROB 
 ++ RW_TAC arith_ss [measureTheory.space_def, IN_COUNT]
 ++ `prob p (PREIMAGE (X 0) {x} INTER p_space p) <> 0` by METIS_TAC [REAL_LT_IMP_NE]
 ++ MAP_EVERY (IMP_RES_THEN ASSUME_TAC o REWRITE_RULE [satTheory.AND_IMP] o 
 	uncurry DEF_NTH_CONJS) [([1],APERIODIC_MC_def),([1, 3],th_dtmc_def),([4],dtmc_def)]
 ++ POP_ASSUM (MP_TAC o Q.SPECL [`0`, `x`]) 
 ++ RW_TAC std_ss [distribution_def, DBLt_def, Trans_def, measureTheory.space_def, IN_COUNT]
 ++ POP_ASSUM (MP_TAC o Q.SPEC `i`) 
 ++ RW_TAC arith_ss [COND_PMF_EQ_COND_PROB]);
 
val DB_B_CASE = prove
  (``!X p a b d n i Linit.                      
	DB_model X p a b d n Linit /\ i + 1 < n /\ 0 < i ==> 
	(cond_prob p (PREIMAGE (X 1) {i} INTER p_space p)
       (PREIMAGE (X 0) {i - 1} INTER p_space p) = b (i - 1))``,
    RW_TAC std_ss [DB_model_def]        
 ++ Cases_on `i = 1` 
 >> (RW_TAC std_ss [] ++ `0 < n` by RW_TAC arith_ss []
    ++ (MP_TAC o Q.ISPECL [`X:num -> 'a -> num`, 
                `p: ('a -> bool) # (('a -> bool) -> bool) # (('a -> bool) -> real)`, 
                `(count (n:num), POW (count n))`, `Linit:num -> real`, 
                `(DBLt (a:num -> real) (b:num -> real) (d:num -> real):num -> num -> num -> real)`,
                `0:num`]) APERIODIC_MC_POS_PROB 
    ++ RW_TAC arith_ss [measureTheory.space_def, IN_COUNT]
    ++ `prob p (PREIMAGE (X 0) {0} INTER p_space p) <> 0` by METIS_TAC [REAL_LT_IMP_NE]
    ++ MAP_EVERY (IMP_RES_THEN ASSUME_TAC o REWRITE_RULE [satTheory.AND_IMP] o 
 	uncurry DEF_NTH_CONJS) [([1],APERIODIC_MC_def),([1, 3],th_dtmc_def),([4],dtmc_def)]
    ++ POP_ASSUM (MP_TAC o Q.SPECL [`0`, `0`]) 
    ++ RW_TAC std_ss [distribution_def, DBLt_def, Trans_def, measureTheory.space_def, IN_COUNT]
    ++ POP_ASSUM (MP_TAC o Q.SPEC `1`) ++ RW_TAC std_ss [COND_PMF_EQ_COND_PROB])
 ++ `i < 1 + n /\ 0 < n` by RW_TAC arith_ss [] 
 ++ (MP_TAC o Q.ISPECL [`X:num -> 'a -> num`, 
                `p: ('a -> bool) # (('a -> bool) -> bool) # (('a -> bool) -> real)`, 
                `(count (n:num), POW (count n))`, `Linit:num -> real`, 
                `(DBLt (a:num -> real) (b:num -> real) (d:num -> real):num -> num -> num -> real)`,
                `(i - 1):num`]) APERIODIC_MC_POS_PROB 
 ++ RW_TAC arith_ss [measureTheory.space_def, IN_COUNT]
 ++ `prob p (PREIMAGE (X 0) {i - 1} INTER p_space p) <> 0` by METIS_TAC [REAL_LT_IMP_NE]  
 ++ MAP_EVERY (IMP_RES_THEN ASSUME_TAC o REWRITE_RULE [satTheory.AND_IMP] o 
 	uncurry DEF_NTH_CONJS) [([1],APERIODIC_MC_def),([1, 3],th_dtmc_def),([4],dtmc_def)]
 ++ POP_ASSUM (MP_TAC o Q.SPECL [`0`, `i - 1`]) 
 ++ RW_TAC std_ss [distribution_def, DBLt_def, Trans_def, measureTheory.space_def, IN_COUNT]
 ++ POP_ASSUM (MP_TAC o Q.SPEC `i`) 
 ++ RW_TAC arith_ss [COND_PMF_EQ_COND_PROB]);     

val DB_A_CASE = prove
  (``!X p a b d n i Linit.                      
	DB_model X p a b d n Linit /\ i + 1 < n /\ 0 < i ==> 
	(cond_prob p (PREIMAGE (X 1) {i} INTER p_space p)
       (PREIMAGE (X 0) {i} INTER p_space p) = a i)``,
    RW_TAC std_ss [DB_model_def]        
 ++ `i < n` by RW_TAC arith_ss []
 ++ MAP_EVERY (IMP_RES_THEN ASSUME_TAC o REWRITE_RULE [satTheory.AND_IMP] o 
 	uncurry DEF_NTH_CONJS) [([1],APERIODIC_MC_def),([1, 3],th_dtmc_def),([4],dtmc_def)]
 ++ POP_ASSUM (MP_TAC o Q.SPECL [`0`, `i`])
 ++ (MP_TAC o Q.ISPECL [`(X:num -> 'a -> num)`, 
 	`p:('a -> bool) # (('a -> bool) -> bool) # (('a -> bool) -> real)`, 
 	`(count (n:num), POW (count n))`, `Linit:num -> real`, 
 	`(DBLt a b d):num -> num -> num -> real`])
 	APERIODIC_MC_POS_PROB 
 ++ RW_TAC std_ss [measureTheory.space_def, IN_COUNT, DBLt_def, distribution_def, Trans_def]
 ++ `prob p (PREIMAGE (X 0) {i} INTER p_space p) <> 0` by METIS_TAC [REAL_POS_NZ]
 ++ FULL_SIMP_TAC std_ss [] ++ POP_ASSUM K_TAC
 ++ POP_ASSUM (MP_TAC o Q.SPEC `i`)  
 ++ RW_TAC arith_ss [] );  

val DB_D_CASE = prove
  (``!X p a b d n i Linit.                      
	DB_model X p a b d n Linit /\ i + 1 < n /\ 0 < i ==> 
	(cond_prob p (PREIMAGE (X 1) {i} INTER p_space p)
       (PREIMAGE (X 0) {i + 1} INTER p_space p) = d (i + 1))``,
    RW_TAC std_ss [DB_model_def]          
 ++ MAP_EVERY (IMP_RES_THEN ASSUME_TAC o REWRITE_RULE [satTheory.AND_IMP] o 
 	uncurry DEF_NTH_CONJS) [([1],APERIODIC_MC_def),([1, 3],th_dtmc_def),([4],dtmc_def)]
 ++ POP_ASSUM (MP_TAC o Q.SPECL [`0`, `i + 1`]) 
 ++ (MP_TAC o Q.ISPECL [`(X:num -> 'a -> num)`, 
 	`p:('a -> bool) # (('a -> bool) -> bool) # (('a -> bool) -> real)`, 
 	`(count (n:num), POW (count n))`, `Linit:num -> real`, 
 	`(DBLt a b d):num -> num -> num -> real`])
 	APERIODIC_MC_POS_PROB  
 ++ RW_TAC std_ss [measureTheory.space_def, IN_COUNT, DBLt_def, distribution_def, Trans_def]
 ++ `prob p (PREIMAGE (X 0) {i + 1} INTER p_space p) <> 0` by METIS_TAC [REAL_POS_NZ]
 ++ FULL_SIMP_TAC std_ss [] ++ POP_ASSUM K_TAC 
 ++ POP_ASSUM (MP_TAC o Q.SPEC `i`) 
 ++ RW_TAC arith_ss []);
            
val DB_GEN_CASE = prove
  (``!X p a b d n i Linit.                      
	DB_model X p a b d n Linit /\ i + 1 < n /\ 0 < i ==> 
	(lim (\t. prob p (PREIMAGE (X t) {i} INTER p_space p)) = 
	 b (i - 1) * lim (\t. prob p (PREIMAGE (X t) {i - 1} INTER p_space p)) +
	 a i * lim (\t. prob p (PREIMAGE (X t) {i} INTER p_space p)) +
	 d (i + 1) * lim (\t. prob p (PREIMAGE (X t) {i + 1} INTER p_space p)))``,
    RW_TAC std_ss [] 
 ++ `stationary_distribution p X (\i. lim (\n. prob p (PREIMAGE (X n) {i} INTER p_space p)))
 	 (count n, POW (count n))` by METIS_TAC [DB_model_def, STEADY_PROB] 
 ++ PSET_TAC [stationary_distribution_def, measureTheory.space_def, IN_COUNT]
 ++ POP_ASSUM (MP_TAC o Q.SPEC `i`)  ++ RW_TAC arith_ss []
 ++ POP_ASSUM (MP_TAC o Q.SPEC `0`) ++ DISCH_TAC 
 ++ Suff `b (i - 1) * lim (\t. prob p (PREIMAGE (X t) {i - 1} INTER p_space p)) +
	 a i * lim (\t. prob p (PREIMAGE (X t) {i} INTER p_space p)) +
	 d (i + 1) * lim (\t. prob p (PREIMAGE (X t) {i + 1} INTER p_space p)) =
	 SIGMA (\i'. lim (\n. prob p (PREIMAGE (X n) {i'} INTER p_space p)) *
               cond_prob p (PREIMAGE (X 1) {i} INTER p_space p)
                 (PREIMAGE (X 0) {i'} INTER p_space p)) (count n)` 
 >> (RW_TAC std_ss [] 
    ++ MATCH_MP_TAC REAL_SUM_IMAGE_EQ 
    ++ RW_TAC arith_ss [Trans_def, FINITE_COUNT, measureTheory.space_def, IN_COUNT])
 ++ POP_ASSUM K_TAC 
 ++ MP_REWRITE_TAC COUNT_SPLIT_I ++ RW_TAC arith_ss []
 ++ DEP_REWRITE_TAC [REAL_SUM_IMAGE_DISJOINT_UNION, REAL_SUM_IMAGE_SING]
 ++ PSET_TAC [FINITE_UNION, FINITE_DIFF, FINITE_COUNT, FINITE_SING]
 << [RW_TAC arith_ss [],
     RW_TAC arith_ss [],
     RW_TAC arith_ss [],
     Know `SIGMA (\i'. lim (\n. prob p (PREIMAGE (X n) {i'} INTER p_space p)) *
         cond_prob p (PREIMAGE (X 1) {i} INTER p_space p)
           (PREIMAGE (X 0) {i'} INTER p_space p)) (count n DIFF {i - 1; i; i + 1}) = 0`
     >> (`FINITE (count n DIFF {i - 1; i; i + 1})` by METIS_TAC [FINITE_DIFF, FINITE_COUNT]     
        ++ (MP_TAC o Q.ISPEC `count n DIFF {i - 1; i; i + 1}`) (GSYM REAL_SUM_IMAGE_0)
        ++ RW_TAC std_ss [] ++ POP_ORW ++ MATCH_MP_TAC REAL_SUM_IMAGE_EQ
        ++ PSET_TAC [IN_DIFF, IN_COUNT]
        ++ Suff `cond_prob p (PREIMAGE (X 1) {i} INTER p_space p)
		      (PREIMAGE (X 0) {x} INTER p_space p) = 0` >> RW_TAC std_ss [REAL_MUL_RZERO]
        ++ MATCH_MP_TAC DB_ZERO_CASE
        ++ MAP_EVERY Q.EXISTS_TAC [`a`, `b`, `d`, `n`, `Linit`]
        ++ RW_TAC std_ss []) ++ RW_TAC std_ss [REAL_ADD_RID] ++ POP_ASSUM K_TAC  
        ++ DEP_REWRITE_TAC [DB_A_CASE, DB_B_CASE, DB_D_CASE]
        ++ RW_TAC std_ss []
        << [MAP_EVERY Q.EXISTS_TAC [`b`, `d`, `n`, `Linit`] ++ RW_TAC std_ss [],
            MAP_EVERY Q.EXISTS_TAC [`a`, `d`, `n`, `Linit`] ++ RW_TAC std_ss [],
            MAP_EVERY Q.EXISTS_TAC [`a`, `b`, `n`, `Linit`] ++ RW_TAC std_ss [],
            METIS_TAC [REAL_MUL_COMM]]]);

val REAL_MUL_MUL_INV_MUL = prove 
  (``!(x:real) y a b. b <> 0 /\ (x * b = a * y) ==> (x = a / b * y)``,
    RW_TAC std_ss []
 ++ MATCH_MP_TAC REAL_EQ_RMUL_IMP
 ++ Q.EXISTS_TAC `b` ++ RW_TAC std_ss []
 ++ `!(m:real) n r. m * n * r = m * r * n` 
 	by METIS_TAC [REAL_MUL_ASSOC, REAL_MUL_COMM] ++ POP_ORW
 ++ DEP_REWRITE_TAC [REAL_DIV_RMUL] ++ RW_TAC std_ss []);

val REAL_MUL_MUL = prove 
  (``!(x:real) y a b. b <> 0 /\ (x = a / b * y) ==> (x * b = a * y)``,
    RW_TAC std_ss []
 ++ MATCH_MP_TAC REAL_EQ_RMUL_IMP
 ++ Q.EXISTS_TAC `inv b` ++ RW_TAC std_ss [REAL_INV_NZ]
 ++ RW_TAC std_ss [GSYM REAL_MUL_ASSOC, REAL_MUL_RINV, REAL_MUL_RID, real_div] 
 ++ RW_TAC std_ss [REAL_MUL_COMM]);

val PARTN_DB_DIV = prove
  (``!X p a b d n i Linit.                      
	DB_model X p a b d n Linit /\ i + 1 < n ==> 
	(lim (\t. prob p (PREIMAGE (X t) {i + 1} INTER p_space p)) =
	 (b i / d (i + 1)) * lim (\t. prob p (PREIMAGE (X t) {i} INTER p_space p)))``,
    Induct_on `i` 
 >> (RW_TAC std_ss [] 
    ++ DEP_REWRITE_TAC [DB_LIM_0] 
    ++ MAP_EVERY Q.EXISTS_TAC [`a`, `n`, `Linit`] ++ RW_TAC std_ss [])
 ++ PSET_TAC [ADD1, IN_COUNT]  
 ++ MATCH_MP_TAC REAL_MUL_MUL_INV_MUL
 ++ RW_TAC std_ss []
 >> (PSET_TAC [DB_model_def] ++ FULL_SIMP_TAC arith_ss [REAL_LT_LE])
 ++ `!(x:real) y z w. (w = x + y + z) <=> (z = w - (x + y))` 
 	by METIS_TAC [REAL_EQ_SUB_RADD, REAL_ADD_COMM, REAL_ADD_ASSOC] 
 ++ `!(a:real) b c. a - (b + c) = a - b - c` by REAL_ARITH_TAC 	
 ++ (MP_TAC o Q.SPECL [`X:num -> 'a -> num`, `p`, `a`, `b`, `d`,`n`, `i + 1`, `Linit`])
 	DB_GEN_CASE
 ++ RW_TAC arith_ss [REAL_MUL_COMM]
 ++ NTAC 3 (POP_ASSUM K_TAC)
 ++ `!(a:real) b c d. a - b - c = a - c - b` by REAL_ARITH_TAC
 ++ POP_ORW 
 ++ `!(x:real) y. x - y * x = x * (1 - y)` 
 	by RW_TAC std_ss [REAL_SUB_LDISTRIB, REAL_MUL_RID, REAL_MUL_COMM] 
 ++ POP_ORW 
 ++ `!(a:real) b c x y w. (c * w = b * y - a * x) ==> (b * y - c * w = a * x)` 
 	by REAL_ARITH_TAC ++ POP_ASSUM MATCH_MP_TAC  
 ++ `!(a:real) b c. a * b - c * a = a * (b - c)` by REAL_ARITH_TAC ++ POP_ORW
 ++ `1 - a (i + 1) - b (i + 1) = d (i + 1)` 
 	by (PSET_TAC [DB_model_def] 
 	   ++ `!(a:real) b c d. (a + b + c = d) ==> (d - a - b = c)` by REAL_ARITH_TAC 
 	   ++ POP_ASSUM MATCH_MP_TAC ++ RW_TAC arith_ss []) ++ POP_ORW
 ++ `!(x:real) y. (x = y) ==> (y = x)` by METIS_TAC [EQ_SYM_EQ] ++ POP_ASSUM MATCH_MP_TAC
 ++ MATCH_MP_TAC REAL_MUL_MUL ++ RW_TAC std_ss []
 >> (PSET_TAC [DB_model_def] ++ FULL_SIMP_TAC arith_ss [REAL_LT_LE])	
 ++ FIRST_ASSUM (MP_TAC o Q.SPECL [`X:num -> 'a -> num`, `p`, `a`, `b`, `d`, `n`, `Linit`])
 ++ RW_TAC arith_ss []);

val DB_SUC_PROB = prove
  (``!X p a b d n i Linit.                      
	DB_model X p a b d n Linit /\ i + 1 < n ==> 
	(lim (\t. prob p (PREIMAGE (X t) {i + 1} INTER p_space p)) = 
	 lim (\t. prob p (PREIMAGE (X t) {0} INTER p_space p)) *
	 mulcon (1, i + 1) (\n. b (n - 1) / d n))``,
    Induct_on `i` 
 >> (RW_TAC std_ss [MULCON_1, REAL_MUL_COMM] ++ METIS_TAC [DB_LIM_0])
 ++ RW_TAC std_ss [ADD, mulcon_def, REAL_MUL_ASSOC]
 ++ (MP_TAC o Q.SPECL [`X:num -> 'a -> num`, `p`, `a`, `b`, `d`, `n`, `i + 1`, `Linit`])
 	PARTN_DB_DIV ++ RW_TAC arith_ss [ADD1, REAL_MUL_COMM]
 ++ FIRST_ASSUM (MP_TAC o Q.SPECL [`X:num -> 'a -> num`, `p`, `a`, `b`, `d`, `n`, `Linit`])
 ++ RW_TAC arith_ss []);
 
val DB_LIM_ZERO_PROB = prove
  (``!X p a b d n Linit.                      
	DB_model X p a b d n Linit ==> 
	(lim (\t. prob p (PREIMAGE (X t) {0} INTER p_space p)) = 
	 1 / SIGMA (\i. mulcon (1, i) (\n. b (n - 1) / d n)) (count n))``,
    RW_TAC std_ss [DB_model_def]
 ++ Know `SIGMA (\i. lim (\n. prob p (PREIMAGE (X n) {i} INTER p_space p))) (count n) =
     lim (\n. prob p (PREIMAGE (X n) {0} INTER p_space p)) +
     SIGMA (\i. lim (\t. prob p (PREIMAGE (X t) {0} INTER p_space p)) *
	 mulcon (1, i) (\n. b (n - 1) / d n)) (count_mn 1 (n - 1))`
 >> (RW_TAC std_ss []	 
    ++ `count n = {0} UNION count_mn 1 (n - 1)` 
    	by (PSET_TAC [count_mn_def, count_def, EXTENSION] ++ RW_TAC arith_ss [])
    ++ POP_ORW ++ DEP_REWRITE_TAC [REAL_SUM_IMAGE_DISJOINT_UNION, REAL_SUM_IMAGE_SING]
    ++ PSET_TAC [FINITE_SING, FINITE_COUNT_MN, IN_COUNT_MN] 
    ++ RW_TAC std_ss [REAL_EQ_LADD] ++ MATCH_MP_TAC REAL_SUM_IMAGE_EQ
    ++ PSET_TAC [FINITE_COUNT_MN, IN_COUNT_MN] 
    ++ `x = (x - 1) + 1` by RW_TAC arith_ss [] 
    ++ POP_ORW ++ MATCH_MP_TAC DB_SUC_PROB
    ++ RW_TAC arith_ss []
    ++ MAP_EVERY Q.EXISTS_TAC [`a`, `n`, `Linit`]
    ++ RW_TAC arith_ss [DB_model_def]) ++ RW_TAC std_ss []
 ++ `SIGMA (\i. lim (\t. prob p (PREIMAGE (X t) {0} INTER p_space p)) *
	 mulcon (1, i) (\n. b (n - 1) / d n)) (count_mn 1 (n - 1)) = 
     lim (\t. prob p (PREIMAGE (X t) {0} INTER p_space p)) *
     SIGMA (\i. mulcon (1, i) (\n. b (n - 1) / d n)) (count_mn 1 (n - 1))`
     by (DEP_REWRITE_TAC [REAL_SUM_IMAGE_CMUL] ++ RW_TAC std_ss [FINITE_COUNT_MN])
 ++ `lim (\n. prob p (PREIMAGE (X n) {0} INTER p_space p)) +
     lim (\t. prob p (PREIMAGE (X t) {0} INTER p_space p)) *
     SIGMA (\i. mulcon (1,i) (\n. b (n - 1) / d n)) (count_mn 1 (n - 1)) =
     lim (\t. prob p (PREIMAGE (X t) {0} INTER p_space p)) *
     SIGMA (\i. mulcon (1,i) (\n. b (n - 1) / d n)) (count n)`
     by(`count n = {0} UNION count_mn 1 (n - 1)` 
    		by (PSET_TAC [count_mn_def, count_def, EXTENSION] ++ RW_TAC arith_ss [])
       ++ POP_ORW ++ DEP_REWRITE_TAC [REAL_SUM_IMAGE_DISJOINT_UNION, REAL_SUM_IMAGE_SING]
       ++ PSET_TAC [FINITE_SING, FINITE_COUNT_MN, IN_COUNT_MN, mulcon_def, 
       		REAL_LDISTRIB, REAL_MUL_RID] )
 ++ `stationary_distribution p X (\i. lim (\n. prob p (PREIMAGE (X n) {i} INTER p_space p)))
 	 (count n, POW (count n))` by METIS_TAC [STEADY_PROB] 
 ++ PSET_TAC [stationary_distribution_def, measureTheory.space_def, IN_COUNT]
 ++ POP_ASSUM K_TAC 
 ++ PSET_TAC [real_div, REAL_MUL_LID] 
 ++ METIS_TAC [REAL_RINV_UNIQ, REAL_MUL_COMM]);
 
</script>
</body>
</html>