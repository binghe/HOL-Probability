(*=================================================================*)
(* The indices of the definitions and theorems refer to the order  *)
(* that they presented in the paper.                               *)
(*=================================================================*)
(*val () = app load
 ["bossLib", "metisLib", "arithmeticTheory", "pred_setTheory", "realLib", "seqTheory",
 	"pairTheory", "combinTheory", "numLib", "dividesTheory", "dep_rewrite", "listTheory",
 	"prim_recTheory", "probabilityTheory", "cond_probTheory", "extra_pred_setTools",
 	"dtmcBasicTheory", "Tactic", "setUsefulTheory", "gcd_of_setTheory"];

set_trace "Unicode" 0;*)

open HolKernel Parse boolLib bossLib metisLib numLib combinTheory subtypeTheory
	pred_setTheory numLib seqTheory dividesTheory dep_rewrite listTheory
     extra_pred_setTheory arithmeticTheory realTheory realLib pairTheory extra_pred_setTools
      prim_recTheory extrealTheory probabilityTheory cond_probTheory 
      dtmcBasicTheory Tactic setUsefulTheory gcd_of_setTheory;

val _ = new_theory "classified_dtmc";
                 
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
  
val gcd_set_def = Define `
    gcd_set A = {(r:num)| !x. x IN A ==> divides r x}`;

(* ------------------------------------------------------------------------- *)
(* Definition 8: gcd of a Set                                                *)
(* ------------------------------------------------------------------------- *) 
val GCD_OF_SET_def = Define `
    GCD_OF_SET A = MAX_SET (gcd_set A)`;
    
(* ------------------------------------------------------------------------- *)
(* Important definitions in DTMC theorems                                    *)
(* ------------------------------------------------------------------------- *)	
(* ------------------------------------------------------------------------- *)
(* Definition 5: Stationary Distribution                                     *)
(* ------------------------------------------------------------------------- *)
val stationary_distribution_def = Define `
    stationary_distribution p X f s =
        (SIGMA (\k. f k) (space s) = 1) /\ 
	!i. i IN space s ==> (0 <= f i) /\ 
	(!(t:num). f i = SIGMA (\k. (f k) * Trans X p s t 1 k i) (space s))`;
	
(* ------------------------------------------------------------------------- *)
(* Definition 6: First Passage Time                                          *)
(* ------------------------------------------------------------------------- *)	
val FPT_def = Define `
    FPT (X:num -> 'a -> 'b) (j:'b) x = MIN_SET {(t:num)| (0 < t) /\ (X t x = j)}`;

(* ------------------------------------------------------------------------- *)
(* Definition 7: Probability of First Passage Events                         *)
(* ------------------------------------------------------------------------- *)    
val f_ijn_def = Define `
    f_ijn X p (j:'b) (i:'b) n = 
	  cond_prob p ({x | (FPT X j x = n) /\ (x IN p_space p)}) 
	                   (PREIMAGE (X 0) {i} INTER p_space p)`;                 

val PERSISTENT_STATE_def = Define `
    PERSISTENT_STATE X p (j:'b) = 
    (!x. ?t. x IN p_space p /\ 0 < t /\ (X t x = j)) /\ ((\(n:num). f_ijn X p j j n) sums 1)`;

val TRANSIENT_STATE_def = Define `
    TRANSIENT_STATE X p j = 
    (!x. ?t. x IN p_space p /\ 0 < t /\ (X t x = j)) /\ 
    (?s. s < 1 /\ (\(n:num). f_ijn X p j j n) sums s)`;
    
val NON_NULL_STATE_def = Define `
    NON_NULL_STATE X p j = 
    (!x. ?t. x IN p_space p /\ 0 < t /\ (X t x = j)) /\ 
    (summable (\(n:num). &n * f_ijn X p j j n))`;

val NULL_STATE_def = Define `
    NULL_STATE X p j = ~(summable (\(n:num). &n * f_ijn X p j j n))`;  

val PERIOD_SET_def = Define `
    PERIOD_SET X p s (j:'b) = {(n:num)| (0 < n) /\ (!t. 0 < Trans X p s t n j j)}`;  
                                       
val PERIOD_def = Define `
    PERIOD X p s (j:'b) = GCD_OF_SET (PERIOD_SET X p s j)`;
    
val PERIODIC_STATE_def = Define `
    PERIODIC_STATE X p s (j:'b) = (1 < PERIOD X p s j) /\ (PERIOD_SET X p s j <> {})`;

val APERIODIC_STATE_def = Define `
    APERIODIC_STATE X p s (j:'b) = (PERIOD X p s j = 1) /\ (PERIOD_SET X p s j <> {})`;

val ACCESSIBILITY_def = Define `
    ACCESSIBILITY (X:num -> 'a -> 'b) p s i j = 
    ?n. !t. 0 < Trans X p s t n i j`;

val COMMUNICATE_STATES_def = Define `
    COMMUNICATE_STATES (X:num -> 'a -> 'b) p s i j = 
          (ACCESSIBILITY X p s i j) /\ (ACCESSIBILITY X p s j i)`;

(* ------------------------------------------------------------------------- *)
(* Definition 9: Irreducible DTMC                                            *)
(* ------------------------------------------------------------------------- *) 
val IRREDUCIABLE_MC_def = Define `
    IRREDUCIABLE_MC X p s Linit Ltrans = 
    th_dtmc X p s Linit Ltrans /\ (!i j. COMMUNICATE_STATES X p s i j)`;

(* ------------------------------------------------------------------------- *)
(* Definition 10: Reducible DTMC                                             *)
(* ------------------------------------------------------------------------- *) 
val REDUCIABLE_MC_def = Define `
    REDUCIABLE_MC X p s Linit Ltrans = 
    th_dtmc X p s Linit Ltrans /\ (?i j. ~(COMMUNICATE_STATES X p s i j))`;
    
(* ------------------------------------------------------------------------- *)
(* Definition 11: Aperiodic DTMC                                             *)
(* ------------------------------------------------------------------------- *) 
val APERIODIC_MC_def = Define `
    APERIODIC_MC X p s Linit Ltrans = 
    th_dtmc X p s Linit Ltrans /\ (!j. j IN space s ==> APERIODIC_STATE X p s j)`;

(* ------------------------------------------------------------------------- *)
(* Definition 12: Periodic DTMC                                             *)
(* ------------------------------------------------------------------------- *)
val PREIODIC_MC_def = Define `
    PREIODIC_MC X p s Linit Ltrans = 
    (th_dtmc X p s Linit Ltrans) /\ (?j. j IN space s /\ PERIODIC_STATE X p s j)`;

(* ------------------------------------------------------------------------- *)
(* Definition 13: Absorbing DTMC                                             *)
(* ------------------------------------------------------------------------- *)    
val ABSORBING_MC_def = Define `
    ABSORBING_MC X p s Linit Ltrans = 
    th_dtmc X p s Linit Ltrans /\ 
    (?i. !t. (Trans X p s t 1 i i = 1) /\ 
    (!j. j IN space s ==> COMMUNICATE_STATES X p s i j))`;
    
(* ------------------------------------------------------------------------- *)
(* Definition 14: Regular DTMC                                               *)
(* ------------------------------------------------------------------------- *)
val REGULAR_MC_def = Define `
    REGULAR_MC X p s Linit Ltrans =
    th_dtmc X p s Linit Ltrans /\ 
    (?n.  !i j t. i IN space s /\ j IN space s ==> 0 < Trans X p s t n i j)`;
					
val mins_def = Define `
    mins (X:num -> 'a -> 'b) p s i j = 
    MIN_SET {n | !m. n <= m ==> 0 < cond_pmf p (X m) (X 0) ({j}, {i})}`;
  
(* ------------------------------------------------------------------------- *)
(*        Some theorems related to Maximum & Minimum element of a set        *)
(* ------------------------------------------------------------------------- *)	    
val max_def = Define `
    max (m:real) n = if m < n then n else m`;

val min_def = Define `
    min (m:real) n = if n < m then n else m`;
    
val max_lemma = prove (
  ``!s. FINITE s ==> s <> ({}:real -> bool) ==>
	?x. x IN s /\ !y. y IN s ==> y <= x``,
    HO_MATCH_MP_TAC FINITE_INDUCT 
 ++ SIMP_TAC bool_ss [NOT_INSERT_EMPTY, IN_INSERT] 
 ++ REPEAT STRIP_TAC ++ Q.ISPEC_THEN `s` STRIP_ASSUME_TAC SET_CASES 
 << [PSET_TAC [NOT_IN_EMPTY, REAL_LE_REFL],
    `~(s = {})` by PROVE_TAC [NOT_INSERT_EMPTY] 
    ++ `?m. m IN s /\ !y. y IN s ==> y <= m` by PROVE_TAC [] 
    ++ Cases_on `e <= m` >> PROVE_TAC []
    ++ `m <= e` by METIS_TAC [real_lt, REAL_LT_IMP_LE] 
    ++ PROVE_TAC [REAL_LE_REFL, REAL_LE_TRANS]]);

val min_lemma = prove (
  ``!s. FINITE s ==> s <> ({}:real -> bool) ==>
	?x. x IN s /\ !y. y IN s ==> x <= y``,
    HO_MATCH_MP_TAC FINITE_INDUCT 
 ++ SIMP_TAC bool_ss [NOT_INSERT_EMPTY, IN_INSERT] 
 ++ REPEAT STRIP_TAC ++ Q.ISPEC_THEN `s` STRIP_ASSUME_TAC SET_CASES 
 << [PSET_TAC [NOT_IN_EMPTY, REAL_LE_REFL],
    `~(s = {})` by PROVE_TAC [NOT_INSERT_EMPTY] 
    ++ `?m. m IN s /\ !y. y IN s ==> m <= y` by PROVE_TAC [] 
    ++ Cases_on `m <= e` >> PROVE_TAC []
    ++ `e <= m` by METIS_TAC [real_lt, REAL_LT_IMP_LE] 
    ++ PROVE_TAC [REAL_LE_REFL, REAL_LE_TRANS]]);    
    
val max_set_def = new_specification (
  "max_set_def", ["max_set"],
  SIMP_RULE bool_ss [AND_IMP_INTRO, GSYM RIGHT_EXISTS_IMP_THM,
                     SKOLEM_THM] max_lemma);

val min_set_def = new_specification (
  "min_set_def", ["min_set"],
  SIMP_RULE bool_ss [AND_IMP_INTRO, GSYM RIGHT_EXISTS_IMP_THM,
                     SKOLEM_THM] min_lemma);
                     
val max_set_elim = store_thm(
  "max_set_elim",
  ``!P Q. FINITE P /\ ~(P = {}) /\ (!x. (!y. y IN P ==> y <= x) /\ x IN P ==> Q x) ==>
          Q (max_set P)``,
  PROVE_TAC [max_set_def]);
    
val min_set_elim = store_thm(
  "min_set_elim",
  ``!P Q. FINITE P /\ ~(P = {}) /\ (!x. (!y. y IN P ==> x <= y) /\ x IN P ==> Q x) ==>
          Q (min_set P)``,
  PROVE_TAC [min_set_def]);

val max_min_eq = prove
  (``!s. FINITE s /\ s <> ({}:real -> bool) /\ (max_set s = min_set s) ==>
   !e. e IN s ==> (e = min_set s) /\ (e = max_set s)``,
    RW_TAC std_ss []
 ++ `e <= max_set s` by METIS_TAC [max_set_def]
 ++ `min_set s <= e` by METIS_TAC [min_set_def]
 ++ `e <= min_set s` by METIS_TAC []
 ++ METIS_TAC [REAL_LE_ANTISYM]);

val max_min_in_sing = prove
  (``!s. FINITE s /\ s <> ({}:real -> bool) /\ (max_set s = min_set s) ==>
	!e. e IN s ==> (s = {e})``,
    RW_TAC std_ss [GSYM UNIQUE_MEMBER_SING] ++ METIS_TAC [max_min_eq]);
    
val Mjn_def = Define `
    Mjn (X:num -> 'a -> 'b) p s j n = 
    max_set (IMAGE (\i. cond_prob p (PREIMAGE (X n) {j} INTER p_space p)
    				(PREIMAGE (X 0) {i} INTER p_space p)) (space s))`;
    
val mjn_def = Define `
    mjn (X:num -> 'a -> 'b) p s j n = 
    min_set (IMAGE (\i. cond_prob p (PREIMAGE (X n) {j} INTER p_space p)
    				(PREIMAGE (X 0) {i} INTER p_space p)) (space s))`;

val max_set_sing = store_thm
  ("max_set_sing",
  ``!e. max_set {e} = e``,
    RW_TAC std_ss []   				
 ++ Q.SPECL_THEN [`{e}`, `\x. x = e`] (MATCH_MP_TAC o BETA_RULE) max_set_elim
 ++ PSET_TAC [FINITE_SING, NOT_SING_EMPTY]);  
 
val min_set_sing = store_thm
  ("min_set_sing",
  ``!e. min_set {e} = e``,
    RW_TAC std_ss [] 
 ++ Q.SPECL_THEN [`{e}`, `\x. x = e`] (MATCH_MP_TAC o BETA_RULE) min_set_elim
 ++ PSET_TAC [FINITE_SING, NOT_SING_EMPTY]);

val max_set_sing_const = prove 
  (``!s x. FINITE s /\ s <> {} /\ (!e. e IN s ==> (x:real) <= e) /\ (max_set s = x) ==> 
   (s = {(x:real)})``,
    METIS_TAC [UNIQUE_MEMBER_SING, REAL_LE_ANTISYM, max_set_def]);
    
val min_set_le_max_set = prove
  (``!s. FINITE s /\ s <> ({}:real -> bool) ==> (min_set s <= max_set s)``,
    RW_TAC std_ss [max_set_def, min_set_def]);         

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
      
(* ------------------------------------------------------------------------- *)
(*     Some useful theorems related to aperiodic dtmc                        *)
(* ------------------------------------------------------------------------- *)

val EXISTS_FUN_EQ_PERIOD_SET = store_thm 
  ("EXISTS_FUN_EQ_PERIOD_SET",
  ``!X p s (j:'b) Linit Ltrans. APERIODIC_MC X p s Linit Ltrans /\ j IN space s ==> 
	?(a:num -> num). (IMAGE (\i. a i) univ(:num) = PERIOD_SET X p s j) /\ (!i. 0 < a i)``,
    PSET_TAC [APERIODIC_MC_def]
 ++ `!x. x IN (PERIOD_SET X p s (j:'b)) ==> 0 < x` by PSET_TAC [PERIOD_SET_def]
 ++ `(PERIOD_SET X p s (j:'b)) <> {}` by PSET_TAC [APERIODIC_STATE_def, PERIOD_def] 
 ++ PSET_TAC [GSYM MEMBER_NOT_EMPTY]
 ++ Q.EXISTS_TAC `(\(k:num). if k IN PERIOD_SET X p s j then k else x)`
 ++ RW_TAC std_ss [SET_EQ_SUBSET]
 >> PSET_TAC [GSPECIFICATION]
 ++ PSET_TAC [GSPECIFICATION]
 ++ Q.EXISTS_TAC `x'`
 ++ RW_TAC std_ss []);

(* ------------------------------------------------------------------------- *)
(* Theorem 4: Cloased Period Set                                             *)
(* ------------------------------------------------------------------------- *) 
val CLOSED_PERIOD_SET = store_thm
  ("CLOSED_PERIOD_SET",
  ``!X p (i:'b) s Linit Ltrans. 
	APERIODIC_MC X p s Linit Ltrans ==> 
	(!(a:num) (b:num). a IN PERIOD_SET X p s i /\ b IN PERIOD_SET X p s i ==> 
		(a + b) IN PERIOD_SET X p s i)``,
    PSET_TAC [APERIODIC_MC_def, PERIOD_SET_def, Trans_def]
 >> METIS_TAC [ZERO_LESS_ADD] 
 ++ `FINITE (space s)` by PSET_TAC [th_dtmc_def]
 ++ `prob_space p` by PSET_TAC [th_dtmc_def, dtmc_def, mc_property_def, random_variable_def]
 ++ (MP_TAC o Q.SPECL [`X`, `p`, `s`, `a`, `b`, `i`, `i`, `Linit`, `Ltrans`]) THMC_MNGT_CK_EQ
 ++ RW_TAC std_ss [COND_PMF_EQ_COND_PROB] 
 ++ (MP_TAC o Q.SPECL [`X`, `p`, `s`, `t`, `a + b`, `0`, `i`, `i`, `Linit`, `Ltrans`])
 	THMC_TRANS_N ++ RW_TAC std_ss [ZERO_LESS_ADD, Trans_def]
 ++ NTAC 2 (POP_ASSUM K_TAC)
 ++ `0 < cond_prob p (PREIMAGE (X (t + a)) {i} INTER p_space p)
                (PREIMAGE (X t) {i} INTER p_space p)` by METIS_TAC [LESS_NOT_EQ]
 ++ `0 < cond_prob p (PREIMAGE (X (t + b)) {i} INTER p_space p)
                (PREIMAGE (X t) {i} INTER p_space p)` by METIS_TAC [LESS_NOT_EQ] 
 ++ MATCH_MP_TAC REAL_SUM_IMAGE_EXISTS_POS 
 ++ PSET_TAC [th_dtmc_def] 
 << [MATCH_MP_TAC REAL_LE_MUL
     ++ RW_TAC std_ss [COND_PMF_EQ_COND_PROB]
     ++ MATCH_MP_TAC (MATCH_MP (METIS_PROVE [] ``(a ==> b /\ c) ==> (a ==> b)``) 
        	(SPEC_ALL COND_PROB_BOUNDS)) 
     ++ RW_TAC std_ss []
     ++ PROVE_TAC [DTMC_EVENTS],   
                
     Q.EXISTS_TAC `i` ++ RW_TAC std_ss []
     ++ (MP_TAC o GSYM o Q.SPECL [`X`, `p`, `s`, `t`, `a`, `0`, `i`, `i`, `Linit`, `Ltrans`])
 	THMC_TRANS_N ++ RW_TAC std_ss [ZERO_LESS_ADD, th_dtmc_def, Trans_def] 
     ++ (MP_TAC o GSYM o Q.SPECL [`X`, `p`, `s`, `t`, `b`, `0`, `i`, `i`, `Linit`, `Ltrans`])
 	THMC_TRANS_N ++ RW_TAC arith_ss [ZERO_LESS_ADD, th_dtmc_def, Trans_def]
     ++ MATCH_MP_TAC REAL_LT_MUL ++ METIS_TAC [ADD_COMM],
     
     MATCH_MP_TAC REAL_LE_MUL
     ++ RW_TAC std_ss [COND_PMF_EQ_COND_PROB]
     ++ MATCH_MP_TAC (MATCH_MP (METIS_PROVE [] ``(a ==> b /\ c) ==> (a ==> b)``) 
        	(SPEC_ALL COND_PROB_BOUNDS)) 
     ++ RW_TAC std_ss []
     ++ PROVE_TAC [DTMC_EVENTS],
     
     Q.EXISTS_TAC `i` ++ RW_TAC std_ss []
     ++ (MP_TAC o GSYM o Q.SPECL [`X`, `p`, `s`, `t`, `a`, `0`, `i`, `i`, `Linit`, `Ltrans`])
 	THMC_TRANS_N ++ RW_TAC std_ss [th_dtmc_def, Trans_def] 
     >> FULL_SIMP_TAC arith_ss []
     ++ (MP_TAC o GSYM o Q.SPECL [`X`, `p`, `s`, `t`, `b`, `0`, `i`, `i`, `Linit`, `Ltrans`])
 	THMC_TRANS_N ++ RW_TAC arith_ss [ZERO_LESS_ADD, th_dtmc_def, Trans_def]
     ++ MATCH_MP_TAC REAL_LT_MUL ++ METIS_TAC [ADD_COMM]]);
 
(* ------------------------------------------------------------------------- *)
(*           Aperiodic & irreduciable dtmc properties                        *)
(* ------------------------------------------------------------------------- *)	     
val RETURN_PROB_GT = store_thm
  ("RETURN_PROB_GT",
  ``!X p s Linit Ltrans (i:'b). APERIODIC_MC X p s Linit Ltrans /\ i IN space s ==> 
	  ?m. !(n:num). (m <= n) ==>
	(0 < cond_prob p (PREIMAGE (X n) {i:'b} INTER p_space p)
		(PREIMAGE (X 0) {i:'b} INTER p_space p))``,
    RW_TAC std_ss []
 ++ (MP_TAC o Q.SPECL [`X`, `p`, `i`, `s`, `Linit`, `Ltrans`]) CLOSED_PERIOD_SET
 ++ RW_TAC std_ss []
 ++ (MP_TAC o Q.SPECL [`X`, `p`, `s`, `i`, `Linit`, `Ltrans`]) EXISTS_FUN_EQ_PERIOD_SET
 ++ RW_TAC std_ss [] 
 ++ `APERIODIC_STATE X p s i` by PSET_TAC [APERIODIC_MC_def] 
 ++ (MP_TAC o Q.SPECL [`PERIOD_SET X p s i`, `a`]) EXISTS_SUBSET_POSINT 
 ++ PSET_TAC [APERIODIC_STATE_def, PERIOD_def]
 ++ Q.EXISTS_TAC `k` ++ RW_TAC std_ss []
 ++ POP_ASSUM MP_TAC ++ POP_ASSUM (MP_TAC o Q.SPEC `n`) ++ RW_TAC std_ss []
 ++ FULL_SIMP_TAC arith_ss [] 
 ++ `!t. 0 < cond_prob p (PREIMAGE (X (t + n)) {i} INTER p_space p)
                (PREIMAGE (X t) {i} INTER p_space p)`
        by (PSET_TAC [PERIOD_SET_def, Trans_def] ++ POP_ASSUM K_TAC
           ++ POP_ASSUM (MP_TAC o Q.SPEC `t`) ++ RW_TAC arith_ss [LESS_NOT_EQ]) 
 ++ POP_ASSUM (MP_TAC o Q.SPEC `0`) ++ RW_TAC arith_ss []);

(* ------------------------------------------------------------------------- *)
(* Theorem 5: Positive Return Probability                                    *)
(* ------------------------------------------------------------------------- *) 
val RETURN_TRAN_GT = store_thm
  ("RETURN_TRAN_GT",
  ``!X p s Linit Ltrans (i:'b) t. APERIODIC_MC X p s Linit Ltrans /\ i IN space s ==> 
	  ?m. !(n:num). m <= n ==> 0 < Trans X p s t n i i``,
    RW_TAC std_ss [Trans_def]
 ++ (MP_TAC o Q.SPECL [`X`, `p`, `s`, `Linit`, `Ltrans`, `i`]) RETURN_PROB_GT
 ++ RW_TAC std_ss []
 ++ Q.EXISTS_TAC `m` ++ RW_TAC real_ss []
 ++ PSET_TAC [APERIODIC_MC_def]
 ++ (MP_TAC o Q.SPECL [`X`, `p`, `s`, `t`, `n`, `0`, `i`, `i`, `Linit`, `Ltrans`]) THMC_TRANS_N
 ++ RW_TAC arith_ss [Trans_def]);
          	
val ABS_POS_SUB = store_thm
  ("ABS_POS_SUB",  
  ``!(x:real) y. (x <= y) ==> (abs (y - x) = y - x)``,
    RW_TAC std_ss []
 ++ `0 <= y - x` by METIS_TAC [REAL_SUB_LE]
 ++ METIS_TAC [ABS_REFL]);
 
val N_TRANSPROB = prove
  (``!X p s Linit Ltrans (j:'b) k (t:num) m.
        th_dtmc X p s Linit Ltrans /\ m < t ==> 
        (cond_prob p (PREIMAGE (X t) {j} INTER p_space p)
                (PREIMAGE (X m) {k} INTER p_space p) =
        cond_prob p (PREIMAGE (X (t - m)) {j} INTER p_space p) 
        	(PREIMAGE (X 0) {k} INTER p_space p))``,
    RW_TAC std_ss []
 ++ `prob_space p` by PSET_TAC [th_dtmc_def, dtmc_def, mc_property_def, random_variable_def]    
 ++ `?n. t = m + n` by METIS_TAC [LESS_IMP_LESS_OR_EQ, LESS_EQ_EXISTS]   
 ++ RW_TAC std_ss []
 ++ `0 < n` by RW_TAC arith_ss []
 ++ (MP_TAC o GSYM o Q.SPECL [`X`, `p`, `s`, `m`, `n`, `0`, `k`, `j`, `Linit`, `Ltrans`])
 	THMC_TRANS_N ++ RW_TAC arith_ss [Trans_def]  
 ++ Cases_on `~(k IN space s)`
 >> (`!t. PREIMAGE (X t) {k} INTER p_space p = {}` 
 	by (RW_TAC std_ss [] ++ MATCH_MP_TAC NOTIN_SPACE_EVENTS 
           ++ Q.EXISTS_TAC `s` 
           ++ PSET_TAC [th_dtmc_def, dtmc_def, mc_property_def])
    ++ RW_TAC std_ss [cond_prob_def, INTER_EMPTY, real_div, PROB_EMPTY, REAL_DIV_LZERO])
 ++ FULL_SIMP_TAC bool_ss []
 ++ `!t. PREIMAGE (X t) {j} INTER p_space p = {}` 
 	by (RW_TAC std_ss [] ++ MATCH_MP_TAC NOTIN_SPACE_EVENTS 
           ++ Q.EXISTS_TAC `s` 
           ++ PSET_TAC [th_dtmc_def, dtmc_def, mc_property_def])
    ++ RW_TAC std_ss [cond_prob_def, INTER_EMPTY, PROB_EMPTY, REAL_DIV_LZERO]);

val TEMP_FUN = prove
  (``!(m:num) n t (k:num) k'. n < m /\ m < t /\ k < k' ==> 
        (if k = 0 then n 
        else if k = 1 then m
        else if k = 2 then t
        else t + k) <
         (if k' = 0 then n 
        else if k' = 1 then m
        else if k' = 2 then t
        else t + k')``,
   RW_TAC arith_ss []);
   
   
val ARBIT_STEPS_TRANS_PROB = store_thm
  ("ARBIT_STEPS_TRANS_PROB",
  ``!X p s Linit Ltrans (i:'b) (j:'b) k (t:num) m n.
	th_dtmc X p s Linit Ltrans /\ (n < m) /\ (m < t) /\ 
	(prob p ((PREIMAGE (X m) {k} INTER p_space p) INTER 
		PREIMAGE (X n) {i} INTER p_space p) <> 0) ==> 
	(cond_prob p (PREIMAGE (X t) {j} INTER p_space p)
		((PREIMAGE (X m) {k} INTER p_space p) INTER 
		 (PREIMAGE (X n) {i} INTER p_space p)) =
	cond_prob p (PREIMAGE (X t) {j} INTER p_space p) 
	            (PREIMAGE (X m) {k} INTER p_space p))``,
    RW_TAC std_ss [th_dtmc_def]
 ++ `prob p (PREIMAGE (X n) {i} INTER p_space p) <> 0`
        by (SPOSE_NOT_THEN STRIP_ASSUME_TAC 
           ++ `prob p (PREIMAGE (X m) {k} INTER p_space p INTER
                     PREIMAGE (X n) {i} INTER p_space p) = 0`
             	by (POP_ASSUM MP_TAC ++ POP_ASSUM K_TAC 
             	   ++ RW_TAC std_ss [] 
             	   ++ DEP_REWRITE_TAC [PROB_SUBSET_ZERO]
             	   ++ Q.EXISTS_TAC `PREIMAGE ((X:num -> 'a -> 'b) n) {i} INTER p_space p`
             	   ++ PSET_TAC [random_variable_def, INTER_SUBSET]
             	   << [PSET_TAC [dtmc_def, mc_property_def, random_variable_def],
             	       Suff `PREIMAGE (X m) {k} INTER p_space p IN events p /\ 
             	   	PREIMAGE (X n) {i} INTER p_space p IN events p` 
             	       >> METIS_TAC [dtmc_def, mc_property_def, random_variable_def, 
             	                        EVENTS_INTER, INTER_ASSOC]
             	       ++ DEP_REWRITE_TAC [DTMC_EVENTS]
             	       ++ MAP_EVERY Q.EXISTS_TAC [`s`, `Linit`, `Ltrans`]
             	       ++ RW_TAC std_ss [],
             	       DEP_REWRITE_TAC [DTMC_EVENTS]
             	       ++ MAP_EVERY Q.EXISTS_TAC [`s`, `Linit`, `Ltrans`]
             	       ++ RW_TAC std_ss []]))             	       
 ++ `EL 0 [(i:'b);k;j] = i` by RW_TAC std_ss [APPEND, EL, HD]
 ++ `EL 1 [(i:'b);k;j] = k` 
 	by (`1 = SUC 0` by METIS_TAC [ONE] ++ POP_ORW ++ RW_TAC std_ss [APPEND, EL, HD, TL])
 ++ `EL 2 [(i:'b);k;j] = j` 
 	by (`2 = SUC (SUC 0)` by RW_TAC arith_ss [] ++ POP_ORW 
 	   ++ RW_TAC std_ss [APPEND, EL, HD, TL])
 ++ PSET_TAC [dtmc_def, mc_property_def]
 ++ NTAC 12 (POP_ASSUM MP_TAC)
 ++ POP_ASSUM (MP_TAC o Q.SPECL [`(\r. EL r [(i:'b);k;j])`, 
    `(\k. if k = 0 then n else if k = 1 then m else 
                if k = 2 then t else t + k)`, `1`])
 ++ RW_TAC std_ss [Increasing_seq_def, COUNT_ONE, IMAGE_SING, BIGINTER_SING, COND_PMF_EQ_COND_PROB]
 ++ FULL_SIMP_TAC std_ss [TEMP_FUN]);  	            
	            

val THDTMC_SING_CONVERGENT = prove
  (``!X p s Linit Ltrans j. 
  th_dtmc X p s Linit Ltrans /\ ((space s) = {j}) ==>
  (convergent (\n. cond_prob p (PREIMAGE (X n) {j} INTER p_space p) 
   	 		       (PREIMAGE (X 0) {j} INTER p_space p)))``,
    RW_TAC std_ss [] ++ `j IN space s` by PSET_TAC []
 ++ `prob_space p` by FULL_SIMP_TAC std_ss [th_dtmc_def, dtmc_def, 
 	mc_property_def, random_variable_def] 
 ++ `!n. PREIMAGE (X n) {j} INTER p_space p IN events p` 
 	by METIS_TAC [th_dtmc_def, DTMC_EVENTS]
 ++ Cases_on `prob p (PREIMAGE (X 0) {j} INTER p_space p) = 0`
 >> (RW_TAC std_ss [COND_PROB_ZERO, convergent] 
    ++ Q.EXISTS_TAC `0` 
    ++ RW_TAC std_ss [SEQ_CONST])
 ++ `0 < prob p (PREIMAGE (X 0) {j} INTER p_space p)` 
 	by METIS_TAC [PROB_POSITIVE, REAL_LT_LE]
 ++ Know `!n. cond_prob p (PREIMAGE (X n) {j} INTER p_space p)
           (PREIMAGE (X 0) {j} INTER p_space p) = 1`
 >> (RW_TAC std_ss []
    ++ (MP_TAC o Q.SPECL [`X`, `0`, `j`, `n`, `Linit`, `Ltrans`, `p`, `s`])
    	 SUM_ROW_MATRIX_EQ_ONE 
    ++ PSET_TAC [distribution_def, COND_PMF_EQ_COND_PROB, REAL_SUM_IMAGE_SING])
 ++ RW_TAC std_ss [convergent] 
 ++ Q.EXISTS_TAC `(1:real)` 
 ++ RW_TAC std_ss [SEQ_CONST]);

val APERIODIC_MC_POS_PROB = store_thm
  ("APERIODIC_MC_POS_PROB",
  ``!X p s Linit Ltrans (i:'b). 
	APERIODIC_MC X p s Linit Ltrans /\ i IN space s ==>
	0 < prob p (PREIMAGE (X 0) {i:'b} INTER p_space p)``,
    RW_TAC std_ss [APERIODIC_MC_def, APERIODIC_STATE_def, GSYM MEMBER_NOT_EMPTY]
 ++ `prob_space p` 
 	by FULL_SIMP_TAC std_ss [th_dtmc_def, dtmc_def, mc_property_def, random_variable_def]     
 ++ `?x. x IN PERIOD_SET X p s i` by RW_TAC std_ss []   
 ++ PSET_TAC [PERIOD_SET_def, Trans_def] 
 ++ POP_ASSUM (MP_TAC o Q.SPEC `0`) ++ RW_TAC arith_ss [] 
 ++ SPOSE_NOT_THEN STRIP_ASSUME_TAC 
 ++ `PREIMAGE (X 0) {i:'b} INTER p_space p IN events p` 
 	by METIS_TAC [th_dtmc_def, DTMC_EVENTS]
 ++ `PREIMAGE (X x) {i:'b} INTER p_space p IN events p` 
 	by METIS_TAC [th_dtmc_def, DTMC_EVENTS] 		
 ++ `0 <= prob p (PREIMAGE (X 0) {i:'b} INTER p_space p)` by METIS_TAC [PROB_POSITIVE]
 ++ `prob p (PREIMAGE (X 0) {i:'b} INTER p_space p) = 0` by METIS_TAC [REAL_LT_LE]
 ++ `cond_prob p (PREIMAGE (X x) {i} INTER p_space p)
		(PREIMAGE (X 0) {i} INTER p_space p) = 0` 
	by (NTAC 5 (POP_ASSUM MP_TAC) ++ POP_ASSUM K_TAC ++ METIS_TAC [COND_PROB_ZERO])
 ++ METIS_TAC [REAL_LT_IMP_NE]);	

val TRANS_PROB_GT = store_thm
  ("TRANS_PROB_GT",
  ``!X p s Linit Ltrans (i:'b) (j:'b). 
	APERIODIC_MC X p s Linit Ltrans /\ IRREDUCIABLE_MC X p s Linit Ltrans /\ 
	i IN space s /\ j IN space s ==> 
	?m. !(n:num). (m <= n) ==>
	(0 < cond_prob p (PREIMAGE (X n) {j:'b} INTER p_space p)
		(PREIMAGE (X 0) {i:'b} INTER p_space p))``,
    RW_TAC std_ss [IRREDUCIABLE_MC_def, COMMUNICATE_STATES_def, ACCESSIBILITY_def]
 ++ (IMP_RES_TAC o Q.SPECL [`X`, `p`, `s`, `Linit`, `Ltrans`, `j'`]) APERIODIC_MC_POS_PROB
 ++ Cases_on `i = j` 
 >> ((MP_TAC o Q.SPECL [`X`, `p`, `s`, `Linit`, `Ltrans`, `i`]) RETURN_PROB_GT 
    ++ RW_TAC std_ss [])
 ++ NTAC 5 (POP_ASSUM MP_TAC)    
 ++ POP_ASSUM (MP_TAC o Q.SPECL [`i`, `j`]) ++ RW_TAC std_ss []
 ++ FULL_SIMP_TAC std_ss [Trans_def]
 ++ `n <> 0` by (SPOSE_NOT_THEN STRIP_ASSUME_TAC ++ FULL_SIMP_TAC real_ss [])
 ++ FULL_SIMP_TAC real_ss []
 ++ (MP_TAC o Q.SPECL [`X`, `p`, `s`, `Linit`, `Ltrans`, `i`]) RETURN_PROB_GT 
 ++ RW_TAC std_ss [] ++ NTAC 7 (POP_ASSUM MP_TAC) ++ POP_ASSUM K_TAC 
 ++ RW_TAC std_ss []
 ++ Q.EXISTS_TAC `m + n + 1` ++ RW_TAC arith_ss [] 
 ++ `m <= n' - n` by RW_TAC arith_ss [] ++ `m <= n'` by RW_TAC arith_ss []
 ++ `0 < cond_prob p (PREIMAGE (X (n' - n)) {i} INTER p_space p)
               (PREIMAGE (X 0) {i} INTER p_space p)` by RW_TAC std_ss []
 ++ `0 < cond_prob p (PREIMAGE (X n') {i} INTER p_space p)
            (PREIMAGE (X 0) {i} INTER p_space p)` by RW_TAC arith_ss []
 ++ `0 < cond_prob p (PREIMAGE (X (n + m)) {i} INTER p_space p)
            (PREIMAGE (X 0) {i} INTER p_space p)` by RW_TAC arith_ss []
 ++ `prob_space p` 
 	by FULL_SIMP_TAC std_ss [th_dtmc_def, dtmc_def, mc_property_def, random_variable_def]
 ++ `PREIMAGE (X 0) {i} INTER p_space p IN events p` 
 	by METIS_TAC [th_dtmc_def,DTMC_EVENTS]
 ++ `PREIMAGE (X n') {j} INTER p_space p IN events p` 
 	by METIS_TAC [th_dtmc_def,DTMC_EVENTS]
 ++ `PREIMAGE (X (n' - n)) {i} INTER p_space p IN events p` 
 	by METIS_TAC [th_dtmc_def,DTMC_EVENTS]
 ++ Q.ABBREV_TAC `B = PREIMAGE (X n') {j} INTER p_space p`
 ++ Q.ABBREV_TAC `A = PREIMAGE (X (n' - n)) {i} INTER p_space p`
 ++ Q.ABBREV_TAC `C = PREIMAGE (X 0) {i} INTER p_space p`  
 ++ (MP_TAC o Q.SPECL [`B`, `A`, `C`, `p`]) COND_PROB_INCREASING ++ RW_TAC std_ss []
 ++ `cond_prob p (A INTER B) C <= cond_prob p B C` by METIS_TAC [INTER_COMM]
 ++ (MP_TAC o Q.SPECL [`B`, `A`, `C`, `p`]) COND_PROB_INTER_SPLIT ++ RW_TAC std_ss []
 ++ Q.UNABBREV_TAC `A` ++ Q.UNABBREV_TAC `B` ++ Q.UNABBREV_TAC `C` 
 ++ Suff `0 < cond_prob p (PREIMAGE (X n') {j} INTER p_space p)
             (PREIMAGE (X (n' - n)) {i} INTER p_space p INTER
              (PREIMAGE ((X:num -> 'a -> 'b) (0:num)) {i:'b} INTER p_space p))`
 >> (RW_TAC std_ss [] 
    ++ `0 < cond_prob p (PREIMAGE (X n') {j} INTER p_space p)
             (PREIMAGE (X (n' - n)) {i} INTER p_space p INTER
              (PREIMAGE (X 0) {i} INTER p_space p)) *
           cond_prob p (PREIMAGE (X (n' - n)) {i} INTER p_space p)
             (PREIMAGE ((X:num -> 'a -> 'b) (0:num)) {i:'b} INTER p_space p)` 
             by METIS_TAC [REAL_LT_MUL]
    ++ METIS_TAC [REAL_LTE_TRANS]) ++ NTAC 3 (POP_ASSUM K_TAC)
 ++ Cases_on `n' = n` 
 >> (RW_TAC arith_ss [INTER_IDEMPOT]
    ++ NTAC 17 (POP_ASSUM K_TAC) 
    ++ POP_ASSUM (MP_TAC o Q.SPEC `0`)
    ++ RW_TAC arith_ss [])
 ++ `0 < n' - n` by RW_TAC arith_ss []
 ++ `0 < n'` by RW_TAC arith_ss []
 ++ Know `prob p (PREIMAGE (X (n' - n)) {i} INTER p_space p INTER
              PREIMAGE (X (0:num)) {i} INTER p_space p) <> 0`
 >> (SPOSE_NOT_THEN STRIP_ASSUME_TAC
    ++ `cond_prob p (PREIMAGE (X (n' - n)) {i} INTER p_space p)
             (PREIMAGE (X (0:num)) {i} INTER p_space p) = 0`
    	by (NTAC 10 (POP_ASSUM MP_TAC) ++ POP_ASSUM K_TAC
       ++ RW_TAC std_ss [cond_prob_def, GSYM INTER_ASSOC, REAL_DIV_LZERO])
       ++ METIS_TAC [REAL_LT_IMP_NE]) ++ RW_TAC std_ss []
 ++ (MP_TAC o Q.SPECL [`X`, `p`, `s`, `Linit`, `Ltrans`, `i`, `j`, `i`, `n'`, `n' - n`, `0`])
	ARBIT_STEPS_TRANS_PROB  ++ RW_TAC std_ss []
 ++ (MP_TAC o Q.SPECL [`X`, `p`, `s`, `Linit`, `Ltrans`, `j`, `i`, `n'`, `n' - n`])
	 N_TRANSPROB  ++ RW_TAC arith_ss []  
 ++ NTAC 23 (POP_ASSUM K_TAC) 	 
 ++ POP_ASSUM (MP_TAC o Q.SPEC `0`)
 ++ RW_TAC arith_ss []);

(* ------------------------------------------------------------------------- *)
(* Theorem 6: Existence of Positive Transition Probabilities                 *)
(* ------------------------------------------------------------------------- *)  
val POS_TRANS_IA_MC = store_thm
  ("POS_TRANS_IA_MC",
  ``!X p s Linit Ltrans (i:'b) (j:'b) t. 
	APERIODIC_MC X p s Linit Ltrans /\ IRREDUCIABLE_MC X p s Linit Ltrans /\ 
	i IN space s /\ j IN space s ==> 
	?m. !(n:num). (m <= n) ==> 0 < Trans X p s t n i j``,
    RW_TAC std_ss [Trans_def]
 >> ((MP_TAC o Q.SPECL [`X`, `p`, `s`, `Linit`, `Ltrans`, `i`]) RETURN_PROB_GT
    ++ RW_TAC std_ss []
    ++ Q.EXISTS_TAC `m` ++ RW_TAC real_ss []
    ++ (MP_TAC o Q.SPECL [`X`, `p`, `s`, `t`, `n`, `0`, `i`, `i`, `Linit`, `Ltrans`]) 
    	THMC_TRANS_N ++ PSET_TAC [APERIODIC_MC_def, Trans_def]
    ++ FULL_SIMP_TAC arith_ss [])
 ++ (MP_TAC o Q.SPECL [`X`, `p`, `s`, `Linit`, `Ltrans`, `i`, `j`]) TRANS_PROB_GT
 ++ RW_TAC std_ss []
 ++ Q.EXISTS_TAC `m` ++ RW_TAC real_ss []
 >> (SPOSE_NOT_THEN STRIP_ASSUME_TAC ++ RW_TAC arith_ss []
    ++ POP_ASSUM (MP_TAC o Q.SPEC `0`) ++ STRIP_TAC 
    ++ FULL_SIMP_TAC arith_ss []
    ++ `prob_space p` by PSET_TAC [APERIODIC_MC_def, th_dtmc_def, dtmc_def, 
    	mc_property_def, random_variable_def]
    ++ `cond_prob p (PREIMAGE (X 0) {j} INTER p_space p)
              (PREIMAGE (X 0) {i} INTER p_space p) = 0`
           by PSET_TAC [cond_prob_def, REWRITE_RULE [DISJOINT_DEF] DISJOINT_PROC_INTER,
           	 PROB_EMPTY, REAL_DIV_LZERO] 
    ++ METIS_TAC [REAL_LT_IMP_NE])
 ++ `0 < n` by RW_TAC arith_ss []
 ++ (MP_TAC o Q.SPECL [`X`, `p`, `s`, `t`, `n`, `0`, `i`, `j`, `Linit`, `Ltrans`]) 
    	THMC_TRANS_N ++ PSET_TAC [APERIODIC_MC_def, Trans_def]
 ++ FULL_SIMP_TAC arith_ss []);
    
val APID_MC_POS_COND = store_thm
  ("APID_MC_POS_COND",
  ``!X p s Linit Ltrans. 
   APERIODIC_MC X p s Linit Ltrans /\ IRREDUCIABLE_MC X p s Linit Ltrans ==>
   (?N. !i j n. i IN space s /\ j IN space s /\ N <= n ==> 
   	0 < cond_pmf p (X n) (X 0) ({j}, {i}))``,
    RW_TAC std_ss []
 ++ `FINITE (space s)` by FULL_SIMP_TAC std_ss [APERIODIC_MC_def, th_dtmc_def] 
    
 ++ Q.EXISTS_TAC `MAX_SET {n | ?i j. i IN space s /\ j IN space s /\ (n = mins X p s i j)}`
 ++ RW_TAC std_ss [] 
 ++ (MP_TAC o Q.SPECL [`X`, `p`, `s`, `Linit`, `Ltrans`, `i`, `j`]) TRANS_PROB_GT   
 ++ RW_TAC std_ss [COND_PMF_EQ_COND_PROB] 
 ++ `{n | !m. n <= m ==> 0 < cond_pmf p (X m) (X 0) ({j}, {i})} <> {}`
    	by (PSET_TAC [EXTENSION, mins_def] ++ Q.EXISTS_TAC `m` ++ RW_TAC std_ss []
    	   ++ Cases_on `m' < m` >> METIS_TAC [COND_PMF_EQ_COND_PROB]
    	   ++ FULL_SIMP_TAC arith_ss [NOT_LESS] ++ METIS_TAC [COND_PMF_EQ_COND_PROB])    	
 ++ `{n | ?i j. i IN space s /\ j IN space s /\ (n = mins X p s i j)} <> {}` 
 	by (POP_ASSUM K_TAC ++ PSET_TAC [EXTENSION] 
 	   ++ MAP_EVERY Q.EXISTS_TAC [`i`, `j`] ++ RW_TAC std_ss [])   
 ++ Suff `FINITE {n | ?i j. i IN space s /\ j IN space s /\ (n = mins X p s i j)}`
 >> (RW_TAC std_ss [] 
    ++ `MAX_SET {n | ?i j. i IN space s /\ j IN space s /\ (n = mins X p s i j)} IN 
 	{n | ?i j. i IN space s /\ j IN space s /\ (n = mins X p s i j)}` 
 	by METIS_TAC [MAX_SET_DEF]
    ++ `mins X p s i j IN {n | ?i j. i IN space s /\ j IN space s /\ (n = mins X p s i j)}`
    	by (PSET_TAC [EXTENSION] 
    	   ++ MAP_EVERY Q.EXISTS_TAC [`i`, `j`] 
    	   ++ RW_TAC std_ss [])
    ++ `mins X p s i j <= 
    	MAX_SET {n | ?i j. i IN space s /\ j IN space s /\ (n = mins X p s i j)}` 
    	by METIS_TAC [MAX_SET_DEF]
    ++ `!k. mins X p s i j <= k ==> 0 < cond_prob p (PREIMAGE (X k) {j} INTER p_space p)
              (PREIMAGE (X 0) {i} INTER p_space p)` 
           by (RW_TAC std_ss [mins_def] 
              ++ `MIN_SET {n | !m. n <= m ==> 0 < cond_pmf p (X m) (X 0) ({j},{i})} IN 
                  {n | !m. n <= m ==> 0 < cond_pmf p (X m) (X 0) ({j},{i})}` 
                  by METIS_TAC [MIN_SET_LEM] ++ PSET_TAC [] 
              ++ METIS_TAC [COND_PMF_EQ_COND_PROB])
    ++ METIS_TAC [LESS_EQ_TRANS])
 ++ Suff `{n | ?i j. i IN space s /\ j IN space s /\ (n = mins X p s i j)} =
     BIGUNION (IMAGE (\(i, j). 	{n | (n = mins X p s i j)}) (space s CROSS space s))`
 >> (RW_TAC std_ss [] ++ MATCH_MP_TAC FINITE_BIGUNION ++ PSET_TAC [IN_IMAGE]
    >> (MATCH_MP_TAC IMAGE_FINITE ++ RW_TAC std_ss [FINITE_CROSS])    
    ++ PSET_TAC [IN_CROSS] ++ `x = (FST x, SND x)` by PSET_TAC [PAIR] ++ POP_ORW
    ++ RW_TAC std_ss [GSPEC_EQ, FINITE_SING])      
 ++ PSET_TAC [EXTENSION, IN_BIGUNION_IMAGE] ++ EQ_TAC 
 >> (RW_TAC std_ss [] ++ Q.EXISTS_TAC `(i'', j'')` 
    ++ RW_TAC std_ss [IN_CROSS] ++ PSET_TAC [])
 ++ RW_TAC std_ss [IN_CROSS] 
 ++ `x'' = (FST x'', SND x'')` by PSET_TAC [PAIR]
 ++ `x' IN (\(i, j). {n | n = mins X p s i j}) (FST x'', SND x'')` by METIS_TAC [] 
 ++ PSET_TAC [] ++ RW_TAC std_ss []
 ++ MAP_EVERY Q.EXISTS_TAC [`FST x''`, `SND x''`] 
 ++ RW_TAC std_ss []);

val APID_MC_POS_TRANS = store_thm
  ("APID_MC_POS_TRANS",
  ``!X p s Linit Ltrans t. 
   APERIODIC_MC X p s Linit Ltrans /\ IRREDUCIABLE_MC X p s Linit Ltrans ==>
   (?N. !i j n. i IN space s /\ j IN space s /\ N <= n ==> 
   	0 < Trans X p s t n i j)``,
    RW_TAC std_ss [Trans_def]
 ++ (MP_TAC o Q.SPECL [`X`, `p`, `s`, `Linit`, `Ltrans`]) APID_MC_POS_COND
 ++ PSET_TAC [APERIODIC_MC_def, Trans_def]   
 ++ Q.EXISTS_TAC `N` ++ RW_TAC real_ss []
 >> (Cases_on `i NOTIN space s` >> RW_TAC std_ss []
    ++ Cases_on `j NOTIN space s` >> RW_TAC std_ss []
    ++ Suff `N <> 0` >> RW_TAC std_ss []
    ++ SPOSE_NOT_THEN STRIP_ASSUME_TAC 
    ++ FIRST_ASSUM (MP_TAC o Q.SPECL [`i`, `j`, `0`])
    ++ STRIP_TAC
    ++ `0 < cond_pmf p (X 0) (X 0) ({j},{i})` by FULL_SIMP_TAC std_ss [] 
    ++ `prob_space p` by PSET_TAC [APERIODIC_MC_def, th_dtmc_def, dtmc_def, 
    	mc_property_def, random_variable_def]	
    ++ `cond_pmf p (X 0) (X 0) ({j},{i}) = 0`
           by PSET_TAC [COND_PMF_EQ_COND_PROB, cond_prob_def, 
           		REWRITE_RULE [DISJOINT_DEF] DISJOINT_PROC_INTER,
 	                PROB_EMPTY, REAL_DIV_LZERO] 
    ++ METIS_TAC [REAL_LT_IMP_NE])
 ++ `0 < n` by RW_TAC arith_ss []
 ++ (MP_TAC o Q.SPECL [`X`, `p`, `s`, `t`, `n`, `0`, `i`, `j`, `Linit`, `Ltrans`]) 
    	THMC_TRANS_N ++ PSET_TAC [APERIODIC_MC_def, Trans_def]
 ++ FULL_SIMP_TAC arith_ss [COND_PMF_EQ_COND_PROB]);  
    	
val POS_EXIST_MAX_MIN = prove
  (``!X p s Linit Ltrans j i. 
  APERIODIC_MC X p s Linit Ltrans /\ IRREDUCIABLE_MC X p s Linit Ltrans /\ (i <> j) /\
   (i IN space s) /\ (j IN space s) /\ (?N. (Mjn X p s j N = mjn X p s j N)) ==>
   (?n. 0 < n /\ (Mjn X p s j n = mjn X p s j n))``,
    RW_TAC std_ss [IRREDUCIABLE_MC_def, COMMUNICATE_STATES_def, COND_PMF_EQ_COND_PROB,
    		   Mjn_def, mjn_def]
 ++ `prob_space p` by FULL_SIMP_TAC std_ss [th_dtmc_def, dtmc_def, 
 	mc_property_def, random_variable_def]    		   
 ++ `!i. PREIMAGE (X 0) {i} INTER p_space p IN events p` 
 	by METIS_TAC [th_dtmc_def, DTMC_EVENTS]    
 ++ `0 < prob p (PREIMAGE (X 0) {j} INTER p_space p)` 
 	by METIS_TAC [APERIODIC_MC_POS_PROB]   
 ++ `0 < prob p (PREIMAGE (X 0) {i} INTER p_space p)` 
 	by METIS_TAC [APERIODIC_MC_POS_PROB] 
 ++ `FINITE (space s)` by FULL_SIMP_TAC std_ss [th_dtmc_def]      		   
 ++ Know `N <> 0`
 >> (SPOSE_NOT_THEN STRIP_ASSUME_TAC
    ++ `cond_prob p (PREIMAGE (X 0) {j} INTER p_space p)
      		(PREIMAGE (X 0) {j} INTER p_space p) IN 
      (IMAGE (\i. cond_prob p (PREIMAGE (X 0) {j} INTER p_space p)
              (PREIMAGE ((X:num -> 'a -> 'b) 0) {i} INTER p_space p)) (space s))` 
           by (PSET_TAC [IN_IMAGE] ++ Q.EXISTS_TAC `(j:'b)` ++ RW_TAC std_ss [])
    ++ `cond_prob p (PREIMAGE (X 0) {j} INTER p_space p)
      (PREIMAGE (X 0) {i} INTER p_space p) IN 
      (IMAGE (\i. cond_prob p (PREIMAGE (X 0) {j} INTER p_space p)
              (PREIMAGE ((X:num -> 'a -> 'b) 0) {i} INTER p_space p)) (space s))` 
           by (PSET_TAC [IN_IMAGE] ++ Q.EXISTS_TAC `(i:'b)` ++ RW_TAC std_ss [])
    ++ `cond_prob p (PREIMAGE (X 0) {j} INTER p_space p)
             (PREIMAGE (X 0) {i} INTER p_space p) = 0` 
             by ((MP_TAC o Q.SPECL [`X`, `p`, `0`, `i`, `j`]) DISJOINT_PROC_INTER 
                ++ RW_TAC std_ss [DISJOINT_DEF, cond_prob_def, INTER_COMM, 
 		            PROB_EMPTY, REAL_DIV_LZERO])
    ++ `cond_prob p (PREIMAGE (X 0) {j} INTER p_space p)
             (PREIMAGE (X 0) {j} INTER p_space p) = 1` 
             by METIS_TAC [COND_PROB_ITSELF, PROB_POSITIVE, REAL_LT_LE]	
    ++ FULL_SIMP_TAC std_ss [] ++ NTAC 2 (POP_ASSUM K_TAC) 
    ++ `FINITE (IMAGE (\i. cond_prob p (PREIMAGE (X 0) {j} INTER p_space p)
                  (PREIMAGE (X 0) {i} INTER p_space p)) (space s))` 
	by (MATCH_MP_TAC IMAGE_FINITE ++ RW_TAC std_ss [th_dtmc_def]) 
    ++ `(IMAGE (\i. cond_prob p (PREIMAGE (X 0) {j} INTER p_space p)
                  (PREIMAGE (X 0) {i} INTER p_space p)) (space s)) <> {}` 
        by METIS_TAC [MEMBER_NOT_EMPTY]     
    ++ `!e. e IN (IMAGE (\i. cond_prob p (PREIMAGE (X 0) {j} INTER p_space p)
                  (PREIMAGE (X 0) {i} INTER p_space p)) (space s)) ==> 
        (e = min_set (IMAGE (\i. cond_prob p (PREIMAGE (X 0) {j} INTER p_space p)
                  (PREIMAGE (X 0) {i} INTER p_space p)) (space s))) /\ 
        (e = max_set (IMAGE (\i. cond_prob p (PREIMAGE (X 0) {j} INTER p_space p)
                  (PREIMAGE (X 0) {i} INTER p_space p)) (space s)))` 
                  by METIS_TAC [max_min_eq]
    ++ FIRST_ASSUM (MP_TAC o Q.SPEC `(0:real)`) 
    ++ FIRST_ASSUM (MP_TAC o Q.SPEC `(1:real)`)
    ++ REPEAT STRIP_TAC ++ METIS_TAC [REAL_LT_01, REAL_LT_IMP_NE])
 ++ RW_TAC std_ss [] ++ Q.EXISTS_TAC `N` ++ RW_TAC arith_ss []);
   
val AIMC_SING_CONVERGENT = prove
  (``!X p s Linit Ltrans j. 
  APERIODIC_MC X p s Linit Ltrans /\ IRREDUCIABLE_MC X p s Linit Ltrans /\
   ((space s) = {j}) ==>
  (convergent (\n. cond_prob p (PREIMAGE (X n) {j} INTER p_space p) 
   	 		       (PREIMAGE (X 0) {j} INTER p_space p)))``,
    RW_TAC std_ss [IRREDUCIABLE_MC_def, COMMUNICATE_STATES_def, COND_PMF_EQ_COND_PROB]
 ++ `prob_space p` by FULL_SIMP_TAC std_ss [th_dtmc_def, dtmc_def, 
 	mc_property_def, random_variable_def] ++ `j IN space s` by PSET_TAC [] 
 ++ `PREIMAGE (X 0) {j} INTER p_space p IN events p` 
 	by METIS_TAC [th_dtmc_def, DTMC_EVENTS] 
 ++ Know `!n. cond_prob p (PREIMAGE (X n) {j} INTER p_space p)
           (PREIMAGE (X 0) {j} INTER p_space p) = 1`
 >> (RW_TAC std_ss []
    ++ `0 < prob p (PREIMAGE (X 0) {j} INTER p_space p)` 
    	by METIS_TAC [APERIODIC_MC_POS_PROB]  
    ++ (MP_TAC o Q.SPECL [`X`, `0`, `j`, `n`, `Linit`, `Ltrans`, `p`, `s`])
    	 SUM_ROW_MATRIX_EQ_ONE 
    ++ RW_TAC std_ss [distribution_def, COND_PMF_EQ_COND_PROB, REAL_SUM_IMAGE_SING])
 ++ RW_TAC std_ss [convergent] 
 ++ Q.EXISTS_TAC `(1:real)` 
 ++ RW_TAC std_ss [SEQ_CONST]);

val AIMC_CONV_CASE1 = prove
  (``!X p s Linit Ltrans j i. 
  	APERIODIC_MC X p s Linit Ltrans /\ IRREDUCIABLE_MC X p s Linit Ltrans /\ 
  	i <> j /\ i IN space s /\ j IN space s /\ 
  	(?N. (Mjn X p s j N = mjn X p s j N)) ==>
  	(convergent (\n. cond_prob p (PREIMAGE (X n) {j} INTER p_space p) 
   	 		       (PREIMAGE (X 0) {i} INTER p_space p)))``,
    RW_TAC std_ss []
 ++ Know `?N. Mjn X p s j N = mjn X p s j N`
 >> METIS_TAC [] ++ DISCH_TAC
 ++ `?N. 0 < N /\ (Mjn X p s j N = mjn X p s j N)` by METIS_TAC [POS_EXIST_MAX_MIN]
 ++ NTAC 2 (POP_ASSUM MP_TAC) ++ NTAC 2 (POP_ASSUM K_TAC)	  
 ++ RW_TAC std_ss [Mjn_def, mjn_def, GSYM SEQ_CAUCHY, cauchy] 
 ++ FULL_SIMP_TAC std_ss [IRREDUCIABLE_MC_def, COMMUNICATE_STATES_def, COND_PMF_EQ_COND_PROB]
 ++ Q.EXISTS_TAC `N' + 1` ++ RW_TAC std_ss []
 ++ `prob_space p` by FULL_SIMP_TAC std_ss [th_dtmc_def, dtmc_def, 
 	mc_property_def, random_variable_def]
 ++ `FINITE (space s)` by FULL_SIMP_TAC std_ss [th_dtmc_def]
 ++ `!n. PREIMAGE (X n) {j} INTER p_space p IN events p` 
 	by METIS_TAC [th_dtmc_def, DTMC_EVENTS]
 ++ `!n. PREIMAGE (X n) {i} INTER p_space p IN events p` 
 	by METIS_TAC [th_dtmc_def, DTMC_EVENTS] 
 ++ `prob p (PREIMAGE (X 0) {i} INTER p_space p) <> 0` 
    	by METIS_TAC [APERIODIC_MC_POS_PROB, REAL_LT_LE]  	
 ++ `FINITE (IMAGE (\i. cond_prob p (PREIMAGE (X N') {j} INTER p_space p)
                  (PREIMAGE (X 0) {i} INTER p_space p)) (space s))` 
	by (MATCH_MP_TAC IMAGE_FINITE ++ RW_TAC std_ss [th_dtmc_def]) 
 ++ `!t. random_variable (X t) p s` 
 	by FULL_SIMP_TAC std_ss [th_dtmc_def, dtmc_def, mc_property_def] 
 ++ `space s <> {}` by METIS_TAC [RV_NON_EMPTY_SPACE] 
 ++ Suff `abs (cond_prob p (PREIMAGE (X n) {j} INTER p_space p)
         (PREIMAGE (X 0) {i} INTER p_space p) -
       cond_prob p (PREIMAGE (X n') {j} INTER p_space p)
         (PREIMAGE (X 0) {i} INTER p_space p)) = 0` 
 >> RW_TAC std_ss []
 ++ Know `!i k. i IN space s /\ k IN space s ==> 
 		(cond_prob p (PREIMAGE (X N') {j} INTER p_space p) 
 			     (PREIMAGE (X 0) {i} INTER p_space p) = 
 	         cond_prob p (PREIMAGE (X N') {j} INTER p_space p) 
 			     (PREIMAGE (X 0) {k} INTER p_space p))`
 >> (RW_TAC std_ss []	
    ++ `(IMAGE (\i. cond_prob p (PREIMAGE (X N') {j} INTER p_space p)
                  (PREIMAGE (X 0) {i} INTER p_space p)) (space s)) <> {}`
        by (SPOSE_NOT_THEN STRIP_ASSUME_TAC 
           ++ METIS_TAC [IMAGE_EQ_EMPTY])   		
    ++ (MP_TAC o Q.SPEC `(IMAGE (\i. cond_prob p (PREIMAGE (X N') {j} INTER p_space p)
              (PREIMAGE ((X:num -> 'a -> 'b) 0) {i} INTER p_space p)) (space s))`) max_min_eq
    ++ RW_TAC std_ss []
    ++ `cond_prob p (PREIMAGE (X N') {j} INTER p_space p)
      (PREIMAGE (X 0) {i'} INTER p_space p) IN 
      (IMAGE (\i. cond_prob p (PREIMAGE (X N') {j} INTER p_space p)
              (PREIMAGE ((X:num -> 'a -> 'b) 0) {i} INTER p_space p)) (space s))` 
           by (PSET_TAC [IN_IMAGE] 
              ++ Q.EXISTS_TAC `(i':'b)` 
              ++ RW_TAC std_ss [])
    ++ `cond_prob p (PREIMAGE (X N') {j} INTER p_space p)
      (PREIMAGE (X 0) {k} INTER p_space p) IN 
      (IMAGE (\i. cond_prob p (PREIMAGE (X N') {j} INTER p_space p)
              (PREIMAGE ((X:num -> 'a -> 'b) 0) {i} INTER p_space p)) (space s))` 
           by (PSET_TAC [IN_IMAGE] 
              ++ Q.EXISTS_TAC `(k:'b)` 
              ++ RW_TAC std_ss [])
    ++ METIS_TAC []) 
 ++ RW_TAC std_ss []
 ++ Know `!a b. N' + 1 <= a /\ N' + 1 <= b ==>
 	(cond_prob p (PREIMAGE (X a) {j} INTER p_space p)
                (PREIMAGE (X 0) {i} INTER p_space p) =
         cond_prob p (PREIMAGE (X b) {j} INTER p_space p)
                (PREIMAGE (X 0) {i} INTER p_space p))`
 >> (RW_TAC std_ss [] ++ `0 < a - N'` by RW_TAC arith_ss []
    ++ `a - N' + N' = a` by RW_TAC arith_ss []
    ++ (MP_TAC o Q.SPECL [`(X:num -> 'a -> 'b)`, `p`, `s`, `a - N'`, `N'`, `i`, 
    		`j`, `Linit`, `Ltrans`]) THMC_MNGT_CK_EQ
    ++ `0 < b - N'` by RW_TAC arith_ss []
    ++ `b - N' + N' = b` by RW_TAC arith_ss []
    ++ (MP_TAC o Q.SPECL [`(X:num -> 'a -> 'b)`, `p`, `s`, `b - N'`, `N'`, `i`, 
    		`j`, `Linit`, `Ltrans`]) THMC_MNGT_CK_EQ		
    ++ RW_TAC std_ss [COND_PMF_EQ_COND_PROB]
    ++ `SIGMA (\k. cond_prob p (PREIMAGE (X N') {j} INTER p_space p)
           (PREIMAGE (X 0) {k} INTER p_space p) *
         cond_prob p (PREIMAGE (X (a - N')) {k} INTER p_space p)
           (PREIMAGE (X 0) {i} INTER p_space p)) (space s) =
           SIGMA (\k. cond_prob p (PREIMAGE (X N') {j} INTER p_space p)
           (PREIMAGE (X 0) {i} INTER p_space p) *
         cond_prob p (PREIMAGE (X (a - N')) {k} INTER p_space p)
           (PREIMAGE (X 0) {i} INTER p_space p)) (space s)`
           by (MATCH_MP_TAC REAL_SUM_IMAGE_EQ 
              ++ RW_TAC std_ss [] ++ METIS_TAC [])
    ++ `SIGMA (\k. cond_prob p (PREIMAGE (X N') {j} INTER p_space p)
           (PREIMAGE (X 0) {k} INTER p_space p) *
         cond_prob p (PREIMAGE (X (b - N')) {k} INTER p_space p)
           (PREIMAGE (X 0) {i} INTER p_space p)) (space s) =
           SIGMA (\k. cond_prob p (PREIMAGE (X N') {j} INTER p_space p)
           (PREIMAGE (X 0) {i} INTER p_space p) *
         cond_prob p (PREIMAGE (X (b - N')) {k} INTER p_space p)
           (PREIMAGE (X 0) {i} INTER p_space p)) (space s)`
           by (MATCH_MP_TAC REAL_SUM_IMAGE_EQ 
              ++ RW_TAC std_ss [] ++ METIS_TAC [])
    ++ NTAC 2 POP_ORW 
    ++ RW_TAC std_ss [REAL_SUM_IMAGE_CMUL] 
    ++ NTAC 7 (POP_ASSUM K_TAC)         
    ++ `!i. i IN space s ==> {i} IN subsets s` 
       		by FULL_SIMP_TAC std_ss [th_dtmc_def, dtmc_def]       
    ++ `!x t. PREIMAGE (X t) {x} INTER p_space p IN events p`
       	   by METIS_TAC [th_dtmc_def, DTMC_EVENTS]
    ++ (MP_TAC o Q.SPECL [`p`, `PREIMAGE ((X:num -> 'a -> 'b) 0) {i} INTER p_space p`,
       	`(\k. PREIMAGE ((X:num -> 'a -> 'b) (a - N')) {k} INTER p_space p)`, `space s`])
       	  	COND_PROB_ADDITIVE 
    ++ (MP_TAC o Q.SPECL [`p`, `PREIMAGE ((X:num -> 'a -> 'b) 0) {i} INTER p_space p`,
        `(\k. PREIMAGE ((X:num -> 'a -> 'b) (b - N')) {k} INTER p_space p)`, `space s`])
       	  	COND_PROB_ADDITIVE        
    ++ RW_TAC std_ss [PROB_POSITIVE, REAL_LT_LE, DISJOINT_PROC_INTER,
       		 BIGUNION_PREIMAGEX_IS_PSPACE, REAL_MUL_RID]) 
 ++ RW_TAC std_ss []
 ++ FULL_SIMP_TAC std_ss [GREATER_EQ]       		 
 ++ POP_ASSUM (MP_TAC o Q.SPECL [`n`, `n'`]) 
 ++ RW_TAC std_ss [REAL_SUB_REFL, ABS_0]);
 
val MAX_DECREASING = prove
  (``!X p s Linit Ltrans j n. 
	th_dtmc X p s Linit Ltrans /\ j IN space s /\ 1 < CARD (space s) /\ 0 < n ==>
	Mjn X p s j (n + 1) <= Mjn X p s j n``,
    RW_TAC std_ss [Mjn_def]    
 ++ `?i. i IN space s /\ i <> j` 
 	by (SPOSE_NOT_THEN STRIP_ASSUME_TAC 
 	   ++ `space s = {j}` by (PSET_TAC [EXTENSION] ++ METIS_TAC [])
 	   ++ METIS_TAC [CARD_SING, LESS_REFL])    
 ++ `!k i. PREIMAGE (X k) {i} INTER p_space p IN events p` 
 	by METIS_TAC [th_dtmc_def, DTMC_EVENTS] 	   
 ++ `FINITE (space s)` by FULL_SIMP_TAC std_ss [th_dtmc_def]
 ++ `prob_space p` 
 	by FULL_SIMP_TAC std_ss [th_dtmc_def, dtmc_def, mc_property_def, random_variable_def]
 ++ `!t. random_variable (X t) p s` 
 	by FULL_SIMP_TAC std_ss [th_dtmc_def, dtmc_def, mc_property_def] 
 ++ `space s <> {}` by METIS_TAC [RV_NON_EMPTY_SPACE] 
 ++ `!N. (IMAGE (\i. cond_prob p (PREIMAGE (X N) {j} INTER p_space p)
                  (PREIMAGE (X 0) {i} INTER p_space p)) (space s)) <> {}`
        by (SPOSE_NOT_THEN STRIP_ASSUME_TAC ++ METIS_TAC [IMAGE_EQ_EMPTY])
 ++ `!N. FINITE (IMAGE (\i. cond_prob p (PREIMAGE (X N) {j} INTER p_space p)
                  (PREIMAGE (X 0) {i} INTER p_space p)) (space s))` 
	by (MATCH_MP_TAC IMAGE_FINITE ++ RW_TAC std_ss [])
 ++ `!N x. x IN (IMAGE (\i. cond_prob p (PREIMAGE (X N) {j} INTER p_space p)
                  (PREIMAGE (X 0) {i} INTER p_space p)) (space s)) ==> x <= 1`
        by (PSET_TAC [IN_IMAGE]	++ METIS_TAC [COND_PROB_BOUNDS])	
 ++ `!N x. x IN (IMAGE (\i. cond_prob p (PREIMAGE (X N) {j} INTER p_space p)
                  (PREIMAGE (X 0) {i} INTER p_space p)) (space s)) ==> 
           x <= max_set (IMAGE (\i. cond_prob p (PREIMAGE (X N) {j} INTER p_space p)
                  (PREIMAGE (X 0) {i} INTER p_space p)) (space s))`
        by METIS_TAC [max_set_def] 
 ++ Know `!x. x IN IMAGE (\i. cond_prob p (PREIMAGE (X (n + 1)) {j} INTER p_space p)
              (PREIMAGE (X 0) {i} INTER p_space p)) (space s) ==> 
              x <= Mjn X p s j n`
 >> (PSET_TAC [Mjn_def, IN_IMAGE] 
    ++ (MP_TAC o Q.SPECL [`(X:num -> 'a -> 'b)`, `p`, `s`, `1`, `n`, `i'`, 
    		`j`, `Linit`, `Ltrans`]) THMC_MNGT_CK_EQ 
    ++ RW_TAC std_ss [COND_PMF_EQ_COND_PROB, ADD_COMM]
    ++ (MP_TAC o Q.ISPEC `(space s):'b->bool`) REAL_SUM_IMAGE_MONO ++ RW_TAC std_ss []
    ++ `SIGMA (\k. cond_prob p (PREIMAGE (X n) {j} INTER p_space p)
           (PREIMAGE (X 0) {k} INTER p_space p) *
         cond_prob p (PREIMAGE (X 1) {k} INTER p_space p)
           (PREIMAGE (X 0) {i'} INTER p_space p)) (space s) <=
        SIGMA (\k. Mjn X p s j n * cond_prob p (PREIMAGE (X 1) {k} INTER p_space p)
           (PREIMAGE (X 0) {i'} INTER p_space p)) (space s)` 
         by (POP_ASSUM MATCH_MP_TAC ++ RW_TAC std_ss [] ++ MATCH_MP_TAC REAL_LE_RMUL_IMP
            ++ RW_TAC std_ss [Mjn_def] 
            >> RW_TAC std_ss [COND_PROB_BOUNDS]               
            ++ `cond_prob p (PREIMAGE (X n) {j} INTER p_space p)
              	(PREIMAGE (X 0) {x} INTER p_space p) IN 
        	IMAGE (\i. cond_prob p (PREIMAGE (X n) {j} INTER p_space p)
              	(PREIMAGE (X 0) {i} INTER p_space p)) (space s)`
             	by (PSET_TAC [IN_IMAGE] ++ Q.EXISTS_TAC `(x:'b)` ++ RW_TAC std_ss [])
     	    ++ RW_TAC std_ss [max_set_def])
     ++ Suff `SIGMA (\k. Mjn X p s j n * cond_prob p (PREIMAGE (X 1) {k} INTER p_space p)
                  (PREIMAGE (X 0) {i'} INTER p_space p)) (space s) <= 
              max_set (IMAGE (\i. cond_prob p (PREIMAGE (X n) {j} INTER p_space p)
              (PREIMAGE (X 0) {i} INTER p_space p)) (space s))` 
     >> METIS_TAC [REAL_LE_TRANS]
     ++ RW_TAC std_ss [REAL_SUM_IMAGE_CMUL] ++ NTAC 2 (POP_ASSUM K_TAC)
     ++ Cases_on `prob p (PREIMAGE ((X:num -> 'a -> 'b) 0) {i'} INTER p_space p) = 0`
     >> (RW_TAC std_ss []
        ++ `!x. x IN IMAGE (\i. cond_prob p (PREIMAGE (X n) {j} INTER p_space p)
              (PREIMAGE (X 0) {i} INTER p_space p)) (space s)  ==> 0 <= x`
              by (PSET_TAC [IN_IMAGE] ++ METIS_TAC [COND_PROB_BOUNDS])     
        ++ `SIGMA (\k. cond_prob p (PREIMAGE (X 1) {k} INTER p_space p)
           (PREIMAGE (X 0) {i'} INTER p_space p)) (space s) = SIGMA (\k. (0:real)) (space s)`
           by (MATCH_MP_TAC REAL_SUM_IMAGE_EQ ++ RW_TAC std_ss [] ++ METIS_TAC [COND_PROB_ZERO])
        ++ RW_TAC std_ss [REAL_SUM_IMAGE_0, REAL_MUL_RZERO, max_set_def]) 
     ++ `0 < prob p (PREIMAGE (X 0) {i'} INTER p_space p)` 
     		by METIS_TAC [PROB_POSITIVE, REAL_LT_LE]
     ++ `!i. i IN space s ==> {i} IN subsets s` 
       		by FULL_SIMP_TAC std_ss [th_dtmc_def, dtmc_def]       
     ++ (MP_TAC o Q.SPECL [`p`, `PREIMAGE ((X:num -> 'a -> 'b) 0) {i'} INTER p_space p`,
        `(\k. PREIMAGE ((X:num -> 'a -> 'b) 1) {k} INTER p_space p)`, `space s`])
       	  	COND_PROB_ADDITIVE 
     ++ RW_TAC std_ss [PROB_POSITIVE, REAL_LT_LE, DISJOINT_PROC_INTER,
    		 BIGUNION_PREIMAGEX_IS_PSPACE, REAL_MUL_RID, Mjn_def, REAL_LE_REFL])
 ++ METIS_TAC [Mjn_def, max_set_def]);
  
val MAX_DECREASE = prove
  (``!X p s Linit Ltrans j n m. 
	th_dtmc X p s Linit Ltrans /\ j IN space s /\ 
	1 < CARD (space s) /\ 0 < n ==>
	Mjn X p s j (m + n) <= Mjn X p s j n``,
    Induct_on `m` >> RW_TAC std_ss [REAL_LE_REFL]
 ++ RW_TAC std_ss [] 
 ++ Suff `Mjn X p s j (SUC m + n) <= Mjn X p s j (m + n)` 
 >> METIS_TAC [REAL_LE_TRANS]
 ++ `SUC m + n = (m + n) + 1` by RW_TAC arith_ss [] 
 ++ POP_ORW
 ++ `0 < m + n` by RW_TAC arith_ss []
 ++ METIS_TAC [MAX_DECREASING]);
   
val MIN_INCREASING = prove
  (``!X p s Linit Ltrans j n. 
	th_dtmc X p s Linit Ltrans /\ j IN space s /\ 1 < CARD (space s) ==>
	mjn X p s j n <= mjn X p s j (n + 1)``,
    RW_TAC std_ss []
 ++ `?i. i IN space s /\ i <> j` 
 	by (SPOSE_NOT_THEN STRIP_ASSUME_TAC 
 	   ++ `space s = {j}` by (PSET_TAC [EXTENSION] ++ METIS_TAC [])
 	   ++ METIS_TAC [CARD_SING, LESS_REFL])    
 ++ `!k i. PREIMAGE (X k) {i} INTER p_space p IN events p` 
 	by METIS_TAC [th_dtmc_def, DTMC_EVENTS] 	 	   
 ++ `FINITE (space s)` by FULL_SIMP_TAC std_ss [th_dtmc_def]
 ++ `prob_space p` 
 	by FULL_SIMP_TAC std_ss [th_dtmc_def, dtmc_def, mc_property_def, random_variable_def]
 ++ `!t. random_variable (X t) p s` 
 	by FULL_SIMP_TAC std_ss [th_dtmc_def, dtmc_def, mc_property_def] 
 ++ `space s <> {}` by METIS_TAC [RV_NON_EMPTY_SPACE] 
 ++ `!N. (IMAGE (\i. cond_prob p (PREIMAGE (X N) {j} INTER p_space p)
                  (PREIMAGE (X 0) {i} INTER p_space p)) (space s)) <> {}`
        by (SPOSE_NOT_THEN STRIP_ASSUME_TAC ++ METIS_TAC [IMAGE_EQ_EMPTY])
 ++ `!N. FINITE (IMAGE (\i. cond_prob p (PREIMAGE (X N) {j} INTER p_space p)
                  (PREIMAGE (X 0) {i} INTER p_space p)) (space s))` 
	by (MATCH_MP_TAC IMAGE_FINITE ++ RW_TAC std_ss [])
 ++ `!N x. x IN (IMAGE (\i. cond_prob p (PREIMAGE (X N) {j} INTER p_space p)
                  (PREIMAGE (X 0) {i} INTER p_space p)) (space s)) ==> 0 <= x`
        by (PSET_TAC [IN_IMAGE]	++ METIS_TAC [COND_PROB_BOUNDS])	
 ++ `!N x. x IN (IMAGE (\i. cond_prob p (PREIMAGE (X N) {j} INTER p_space p)
                  (PREIMAGE (X 0) {i} INTER p_space p)) (space s)) ==> 
           min_set (IMAGE (\i. cond_prob p (PREIMAGE (X N) {j} INTER p_space p)
                  (PREIMAGE (X 0) {i} INTER p_space p)) (space s)) <= x`
        by METIS_TAC [min_set_def]             
 ++ Cases_on `n = 0`
 >> (RW_TAC std_ss []
    ++ `!i j. i IN space s /\ j IN space s /\ i <> j ==>
    	cond_prob p (PREIMAGE (X 0) {j} INTER p_space p) 
    		(PREIMAGE (X 0) {i} INTER p_space p) IN
    	(IMAGE (\i. cond_prob p (PREIMAGE (X 0) {j} INTER p_space p)
                  (PREIMAGE (X 0) {i} INTER p_space p)) (space s))`
        by (PSET_TAC [IN_IMAGE] ++ Q.EXISTS_TAC `i'` ++ RW_TAC std_ss [])
    ++ `!i j. i IN space s /\ j IN space s /\ i <> j ==>
       (cond_prob p (PREIMAGE (X 0) {j} INTER p_space p) 
       		(PREIMAGE (X 0) {i} INTER p_space p) = 0)`
        	by METIS_TAC [cond_prob_def, DISJOINT_PROC_INTER, DISJOINT_DEF, 
        		PROB_EMPTY, REAL_DIV_LZERO] 
    ++ `min_set (IMAGE (\i. cond_prob p (PREIMAGE (X 0) {j} INTER p_space p)
                       (PREIMAGE (X 0) {i} INTER p_space p)) (space s)) <= 0` 
                by METIS_TAC []
    ++ `0 <= min_set (IMAGE (\i. cond_prob p (PREIMAGE (X 0) {j} INTER p_space p)
               (PREIMAGE (X 0) {i} INTER p_space p)) (space s))` 
                by METIS_TAC [min_set_def]
    ++ METIS_TAC [mjn_def, REAL_LE_ANTISYM, min_set_def])
 ++ `(0:num) < n` by RW_TAC arith_ss []    
 ++ Know `!x. x IN IMAGE (\i. cond_prob p (PREIMAGE (X (n + 1)) {j} INTER p_space p)
              (PREIMAGE (X 0) {i} INTER p_space p)) (space s) ==> mjn X p s j n <= x`
 >> (PSET_TAC [mjn_def, IN_IMAGE] 
    ++ (MP_TAC o Q.SPECL [`(X:num -> 'a -> 'b)`, `p`, `s`, `1`, `n`, `i'`, 
    		`j`, `Linit`, `Ltrans`]) THMC_MNGT_CK_EQ 
    ++ RW_TAC std_ss [COND_PMF_EQ_COND_PROB, ADD_COMM]
    ++ (MP_TAC o Q.ISPEC `(space s):'b->bool`) REAL_SUM_IMAGE_MONO ++ RW_TAC std_ss []
    ++ `SIGMA (\k. mjn X p s j n * cond_prob p (PREIMAGE (X 1) {k} INTER p_space p)
           (PREIMAGE (X 0) {i'} INTER p_space p)) (space s) <=
        SIGMA (\k. cond_prob p (PREIMAGE (X n) {j} INTER p_space p)
           (PREIMAGE (X 0) {k} INTER p_space p) *
         cond_prob p (PREIMAGE (X 1) {k} INTER p_space p)
           (PREIMAGE (X 0) {i'} INTER p_space p)) (space s)` 
         by (POP_ASSUM MATCH_MP_TAC ++ RW_TAC std_ss [] ++ MATCH_MP_TAC REAL_LE_RMUL_IMP
            ++ RW_TAC std_ss [mjn_def] 
            >> RW_TAC std_ss [COND_PROB_BOUNDS]               
            ++ `cond_prob p (PREIMAGE (X n) {j} INTER p_space p)
              	(PREIMAGE (X 0) {x} INTER p_space p) IN 
        	IMAGE (\i. cond_prob p (PREIMAGE (X n) {j} INTER p_space p)
              	(PREIMAGE (X 0) {i} INTER p_space p)) (space s)`
             	by (PSET_TAC [IN_IMAGE] ++ Q.EXISTS_TAC `(x:'b)` ++ RW_TAC std_ss [])
     	    ++ RW_TAC std_ss [min_set_def])
     ++ Suff `min_set (IMAGE (\i. cond_prob p (PREIMAGE (X n) {j} INTER p_space p)
              (PREIMAGE (X 0) {i} INTER p_space p)) (space s)) <=
             SIGMA (\k. mjn X p s j n * cond_prob p (PREIMAGE (X 1) {k} INTER p_space p)
                  (PREIMAGE (X 0) {i'} INTER p_space p)) (space s)` 
     >> METIS_TAC [REAL_LE_TRANS]
     ++ RW_TAC std_ss [REAL_SUM_IMAGE_CMUL] ++ NTAC 2 (POP_ASSUM K_TAC)
     ++ Cases_on `prob p (PREIMAGE ((X:num -> 'a -> 'b) 0) {i'} INTER p_space p) = 0`
     >> (RW_TAC std_ss []
        ++ `!x. x IN IMAGE (\i. cond_prob p (PREIMAGE (X n) {j} INTER p_space p)
              (PREIMAGE (X 0) {i} INTER p_space p)) (space s)  ==> 0 <= x`
              by (PSET_TAC [IN_IMAGE] ++ METIS_TAC [COND_PROB_BOUNDS])     
        ++ `cond_prob p (PREIMAGE (X n) {j} INTER p_space p)
              	(PREIMAGE (X 0) {i'} INTER p_space p) IN 
        	IMAGE (\i. cond_prob p (PREIMAGE (X n) {j} INTER p_space p)
              	(PREIMAGE (X 0) {i} INTER p_space p)) (space s)`
             	by (PSET_TAC [IN_IMAGE] ++ Q.EXISTS_TAC `(i':'b)` ++ RW_TAC std_ss [])
        ++ `cond_prob p (PREIMAGE (X n) {j} INTER p_space p)
             (PREIMAGE (X 0) {i'} INTER p_space p) = 0` by METIS_TAC [COND_PROB_ZERO]
        ++ `min_set (IMAGE (\i. cond_prob p (PREIMAGE (X n) {j} INTER p_space p)
              	(PREIMAGE (X 0) {i} INTER p_space p)) (space s)) = 0` 
              	by METIS_TAC [min_set_def, REAL_LE_ANTISYM] ++ POP_ORW
        ++ MATCH_MP_TAC REAL_LE_MUL ++ RW_TAC std_ss [mjn_def]
        >> (`!x. x IN IMAGE (\i. cond_prob p (PREIMAGE (X n) {j} INTER p_space p)
              (PREIMAGE (X 0) {i} INTER p_space p)) (space s)  ==> 0 <= x`
              by (PSET_TAC [IN_IMAGE] ++ METIS_TAC [COND_PROB_BOUNDS])
           ++ METIS_TAC [min_set_def]) ++ MATCH_MP_TAC REAL_SUM_IMAGE_POS
        ++ METIS_TAC [COND_PROB_BOUNDS]) 
     ++ `!i. i IN space s ==> {i} IN subsets s` 
       		by FULL_SIMP_TAC std_ss [th_dtmc_def, dtmc_def]       
     ++ `!x. PREIMAGE (X 1) {x} INTER p_space p IN events p`
       	   by METIS_TAC [th_dtmc_def, DTMC_EVENTS] 
     ++ (MP_TAC o Q.SPECL [`p`, `PREIMAGE ((X:num -> 'a -> 'b) 0) {i'} INTER p_space p`,
        `(\k. PREIMAGE ((X:num -> 'a -> 'b) 1) {k} INTER p_space p)`, `space s`])
       	  	COND_PROB_ADDITIVE 
     ++ RW_TAC std_ss [PROB_POSITIVE, REAL_LT_LE, DISJOINT_PROC_INTER,
    		 BIGUNION_PREIMAGEX_IS_PSPACE, REAL_MUL_RID, mjn_def, REAL_LE_REFL])
 ++ METIS_TAC [mjn_def, min_set_def]); 

val MIN_INCREASE = prove
  (``!X p s Linit Ltrans j n m. 
	th_dtmc X p s Linit Ltrans /\ j IN space s /\ 1 < CARD (space s) ==>
	mjn X p s j m <= mjn X p s j (m + n)``,
    Induct_on `n` 
 >> RW_TAC std_ss [REAL_LE_REFL]
 ++ RW_TAC std_ss [] 
 ++ Suff `mjn X p s j (m + n) <= mjn X p s j (m + SUC n)` 
 >> METIS_TAC [REAL_LE_TRANS]
 ++ `m + SUC n = (m + n) + 1` by RW_TAC arith_ss [] 
 ++ POP_ORW
 ++ METIS_TAC [MIN_INCREASING]);
  
val THDTMC_MAX_MIN_COND_PROB = prove  
  (``!X p s Linit Ltrans j n. 
   th_dtmc X p s Linit Ltrans /\ j IN space s ==> 
   mjn X p s j n <= Mjn X p s j n``,
     RW_TAC std_ss [Mjn_def, mjn_def] 
 ++ MATCH_MP_TAC min_set_le_max_set
 ++ `!t. random_variable (X t) p s` 
 	by FULL_SIMP_TAC std_ss [th_dtmc_def, dtmc_def, mc_property_def] 
 ++ `space s <> {}` by METIS_TAC [RV_NON_EMPTY_SPACE] 
 ++ CONJ_TAC >> (MATCH_MP_TAC IMAGE_FINITE ++ RW_TAC std_ss [] ++ METIS_TAC [th_dtmc_def])
 ++ SPOSE_NOT_THEN STRIP_ASSUME_TAC ++ METIS_TAC [IMAGE_EQ_EMPTY]);

val SUB_SEQ_MAX_MIN_CONV = prove
  (``!X p s Linit Ltrans j f. 
   th_dtmc X p s Linit Ltrans /\ 1 < CARD (space s) /\ 
   0 < prob p (PREIMAGE (X 0) {j} INTER p_space p) /\
   (\k. Mjn X p s j (f k) - mjn X p s j (f k)) --> 0 ==>
   (\n. Mjn X p s j n - mjn X p s j n) --> 0``,                   
    RW_TAC std_ss []
 ++ `prob_space p` 
 	by FULL_SIMP_TAC std_ss [th_dtmc_def, dtmc_def, mc_property_def, random_variable_def]
 ++ `j IN space s` 
 	by (SPOSE_NOT_THEN STRIP_ASSUME_TAC
 	   ++ `PREIMAGE (X 0) {j} INTER p_space p = {}`
 	   	by (MATCH_MP_TAC NOTIN_SPACE_EVENTS 
    	           ++ Q.EXISTS_TAC `s` 
    	           ++ PSET_TAC [th_dtmc_def, dtmc_def, mc_property_def])
    	   ++ FULL_SIMP_TAC real_ss [PROB_EMPTY])
 ++ Know `!a b. a <= b ==> 
 	(Mjn X p s j b - mjn X p s j b <= Mjn X p s j a - mjn X p s j a)`
 >> (Induct_on `b`
    >> (Induct_on `a` >> RW_TAC std_ss [REAL_LE_REFL] ++ RW_TAC std_ss []) 
    ++ RW_TAC std_ss [ADD1]
    ++ Cases_on `a = b + 1` 
    >> RW_TAC std_ss [REAL_LE_REFL] 
    ++ `a <= b` by RW_TAC arith_ss []
    ++ `!n i. PREIMAGE (X n) {i} INTER p_space p IN events p` 
    	by METIS_TAC [th_dtmc_def, DTMC_EVENTS]
    ++ `prob_space p` by FULL_SIMP_TAC std_ss [th_dtmc_def, dtmc_def, 
 	mc_property_def, random_variable_def]
    ++ `FINITE (space s)` by FULL_SIMP_TAC std_ss [th_dtmc_def] 	
    ++ Cases_on `b = 0` 
    >> (`a = 0` by RW_TAC arith_ss [] 
       ++ RW_TAC std_ss [Mjn_def, mjn_def]
       ++ `!e n. e IN (IMAGE (\i. cond_prob p (PREIMAGE (X n) {j} INTER p_space p)
                  (PREIMAGE (X 0) {i} INTER p_space p)) (space s)) ==> 
                  0 <= e /\ e <= 1`
              by (PSET_TAC [IN_IMAGE] ++ METIS_TAC [COND_PROB_BOUNDS] 
                 ++ METIS_TAC [COND_PROB_BOUNDS])
       ++ `cond_prob p (PREIMAGE (X 0) {j} INTER p_space p)
              (PREIMAGE (X 0) {j} INTER p_space p) IN 
           IMAGE (\i. cond_prob p (PREIMAGE (X 0) {j} INTER p_space p)
              (PREIMAGE (X 0) {i} INTER p_space p)) (space s)` 
              by (PSET_TAC [IN_IMAGE] ++ Q.EXISTS_TAC `j` ++ RW_TAC std_ss [])
       ++ `?i. i IN space s /\ i <> j` 
       		by (SPOSE_NOT_THEN STRIP_ASSUME_TAC 
       		   ++ `space s = {j}` by PSET_TAC [SET_EQ_SUBSET]
       		   ++ METIS_TAC [CARD_SING, LESS_REFL])
       ++ `!n. cond_prob p (PREIMAGE (X n) {j} INTER p_space p)
              (PREIMAGE (X 0) {i} INTER p_space p) IN 
           IMAGE (\i. cond_prob p (PREIMAGE (X n) {j} INTER p_space p)
              (PREIMAGE (X 0) {i} INTER p_space p)) (space s)` 
              by (PSET_TAC [IN_IMAGE] ++ Q.EXISTS_TAC `i` ++ RW_TAC std_ss [])
       ++ `cond_prob p (PREIMAGE (X 0) {j} INTER p_space p)
             (PREIMAGE (X 0) {i} INTER p_space p) = 0` 
             by ((MP_TAC o Q.SPECL [`X`, `p`, `0`, `i`, `j`]) DISJOINT_PROC_INTER 
                ++ RW_TAC std_ss [DISJOINT_DEF, cond_prob_def, INTER_COMM, 
 		            PROB_EMPTY, REAL_DIV_LZERO])
       ++ `cond_prob p (PREIMAGE (X 0) {j} INTER p_space p)
             (PREIMAGE (X 0) {j} INTER p_space p) = 1` 
             by METIS_TAC [COND_PROB_ITSELF, PROB_POSITIVE, REAL_LT_LE]	
       ++ `!n. FINITE (IMAGE (\i. cond_prob p (PREIMAGE (X n) {j} INTER p_space p)
                  (PREIMAGE (X 0) {i} INTER p_space p)) (space s))` 
	by (MATCH_MP_TAC IMAGE_FINITE ++ RW_TAC std_ss [th_dtmc_def]) 
       ++ `!n. (IMAGE (\i. cond_prob p (PREIMAGE (X n) {j} INTER p_space p)
                  (PREIMAGE (X 0) {i} INTER p_space p)) (space s)) <> {}` 
        by METIS_TAC [MEMBER_NOT_EMPTY] ++ FULL_SIMP_TAC std_ss []    
       ++ `!e. e IN (IMAGE (\i. cond_prob p (PREIMAGE (X 0) {j} INTER p_space p)
                  (PREIMAGE (X 0) {i} INTER p_space p)) (space s)) ==> 
        (min_set (IMAGE (\i. cond_prob p (PREIMAGE (X 0) {j} INTER p_space p)
                  (PREIMAGE (X 0) {i} INTER p_space p)) (space s)) <= e)` 
        by METIS_TAC [min_set_def] ++ POP_ASSUM (MP_TAC o Q.SPEC `(0:real)`) 
       ++ `!e. e IN (IMAGE (\i. cond_prob p (PREIMAGE (X 0) {j} INTER p_space p)
                  (PREIMAGE (X 0) {i} INTER p_space p)) (space s)) ==>             
        	(e <= max_set (IMAGE (\i. cond_prob p (PREIMAGE (X 0) {j} INTER p_space p)
                  (PREIMAGE (X 0) {i} INTER p_space p)) (space s)))` 
                  by METIS_TAC [max_set_def, min_set_def]
       ++ POP_ASSUM (MP_TAC o Q.SPEC `(1:real)`) ++ RW_TAC std_ss []
       ++ `max_set (IMAGE (\i. cond_prob p (PREIMAGE (X 0) {j} INTER p_space p)
              (PREIMAGE (X 0) {i} INTER p_space p)) (space s)) = 1` 
              by METIS_TAC [max_set_def, REAL_LE_ANTISYM]
       ++ `min_set (IMAGE (\i. cond_prob p (PREIMAGE (X 0) {j} INTER p_space p)
              (PREIMAGE (X 0) {i} INTER p_space p)) (space s)) = 0`
              by METIS_TAC [min_set_def, REAL_LE_ANTISYM] 
       ++ RW_TAC std_ss [REAL_SUB_RZERO, REAL_LE_SUB_RADD]
       ++ `max_set (IMAGE (\i. cond_prob p (PREIMAGE (X 1) {j} INTER p_space p)
              (PREIMAGE (X 0) {i} INTER p_space p)) (space s)) = 
           max_set (IMAGE (\i. cond_prob p (PREIMAGE (X 1) {j} INTER p_space p)
              (PREIMAGE (X 0) {i} INTER p_space p)) (space s)) + 0` 
              by RW_TAC std_ss [REAL_ADD_RID]
       ++ POP_ORW ++ MATCH_MP_TAC REAL_LE_ADD2 
       ++ METIS_TAC [max_set_def, min_set_def])
    ++ `0 < b` by RW_TAC arith_ss [] ++ FULL_SIMP_TAC std_ss []  
    ++ (MP_TAC o Q.SPECL [`X`, `p`, `s`, `Linit`, `Ltrans`, `j`, `b`]) MAX_DECREASING 
    ++ RW_TAC std_ss []
    ++ (MP_TAC o Q.SPECL [`X`, `p`, `s`, `Linit`, `Ltrans`, `j`, `b`]) MIN_INCREASING 
    ++ RW_TAC std_ss [] 
    ++ `- mjn X p s j (b + 1) <= - mjn X p s j b` by METIS_TAC [REAL_LE_NEG]
    ++ `Mjn X p s j (b + 1) - mjn X p s j (b + 1) <= Mjn X p s j b - mjn X p s j b`
    	by METIS_TAC [REAL_LE_ADD2, real_sub] ++ METIS_TAC [REAL_LE_TRANS])
 ++ RW_TAC std_ss []	
 ++ (MP_TAC o Q.SPECL [`(\k. Mjn X p s j (f k) - mjn X p s j (f k))`, `(0:real)`]) SEQ
 ++ RW_TAC std_ss [SEQ] 
 ++ `?N. !n. n >= N ==> abs (Mjn X p s j (f n) - mjn X p s j (f n)) < e` 
 	by METIS_TAC [REAL_SUB_RZERO]
 ++ Q.EXISTS_TAC `f N` ++ RW_TAC std_ss [REAL_SUB_RZERO]
 ++ `!n. mjn X p s j n <= Mjn X p s j n` 
 	by METIS_TAC [THDTMC_MAX_MIN_COND_PROB]
 ++ `!n. 0 <= Mjn X p s j n - mjn X p s j n` by RW_TAC std_ss [REAL_SUB_LE]
 ++ `!n. abs (Mjn X p s j n - mjn X p s j n) = Mjn X p s j n - mjn X p s j n` 
 	by METIS_TAC [ABS_REFL] 
 ++ `f N <= n` by RW_TAC arith_ss [GREATER_EQ]
 ++ `Mjn X p s j n - mjn X p s j n <= Mjn X p s j (f N) - mjn X p s j (f N)` 
 	by RW_TAC std_ss []
 ++ `abs (Mjn X p s j (f N) - mjn X p s j (f N)) < e` by RW_TAC std_ss [GREATER_EQ]
 ++ `abs (Mjn X p s j (f N) - mjn X p s j (f N)) = Mjn X p s j (f N) - mjn X p s j (f N)` 
 	by METIS_TAC []  ++ FULL_SIMP_TAC std_ss [] 
 ++ METIS_TAC [REAL_LET_TRANS]);

val MAX_SUB_MIN_TENDS_0 = prove
  (``!X p s Linit Ltrans j x N n. 
   th_dtmc X p s Linit Ltrans /\ 0 <= x /\ x < 1 /\
   (!k. 1 <= k ==> Mjn X p s j (k * N + n) - mjn X p s j (k * N + n) <= 
   	(Mjn X p s j n - mjn X p s j n) * x pow k) ==>
   (\k. Mjn X p s j (k * N + n) - mjn X p s j (k * N + n)) --> 0``,
    RW_TAC std_ss [] 
 ++ `prob_space p` 
 	by FULL_SIMP_TAC std_ss [th_dtmc_def, dtmc_def, mc_property_def, random_variable_def]
 ++ Cases_on `j NOTIN space s`
 >> (RW_TAC std_ss [Mjn_def, mjn_def]
    ++ `!k. PREIMAGE (X (k * N + n)) {j} INTER p_space p = {}`
    	by (RW_TAC std_ss [] 
    	   ++ MATCH_MP_TAC NOTIN_SPACE_EVENTS 
    	   ++ Q.EXISTS_TAC `s` 
    	   ++ PSET_TAC [th_dtmc_def, dtmc_def, mc_property_def]) 
    ++ `!t. random_variable (X t) p s` 
 	by FULL_SIMP_TAC std_ss [th_dtmc_def, dtmc_def, mc_property_def] 
    ++ `space s <> {}` by METIS_TAC [RV_NON_EMPTY_SPACE]    	   
    ++ `{(0:real) | i | i IN space s} = {0:real}` 
    	by (PSET_TAC [GSPECIFICATION, EXTENSION]
    	   ++ EQ_TAC >> RW_TAC std_ss [] 
    	   ++ RW_TAC std_ss []
    	   ++ Q.EXISTS_TAC `x'`
    	   ++ RW_TAC std_ss [])
    ++ RW_TAC std_ss [cond_prob_def, INTER_EMPTY, PROB_EMPTY, REAL_DIV_LZERO, 
    	IMAGE_DEF, EXTENSION, max_set_sing, min_set_sing, REAL_SUB_REFL, SEQ_CONST])
 ++ MATCH_MP_TAC SER_ZERO ++ MATCH_MP_TAC SER_COMPAR
 ++ Q.EXISTS_TAC `(\k. (Mjn X p s j n - mjn X p s j n) * x pow k)`
 ++ RW_TAC std_ss []
 >> (Q.EXISTS_TAC `1` ++ RW_TAC std_ss []
    ++ `!n. 0 <= Mjn X p s j n - mjn X p s j n` 
       by METIS_TAC [THDTMC_MAX_MIN_COND_PROB, REAL_SUB_LE]
    ++ `abs (Mjn X p s j (n' * N + n) - mjn X p s j (n' * N + n)) = 
        Mjn X p s j (n' * N + n) - mjn X p s j (n' * N + n)` 
        by METIS_TAC [ABS_REFL]
    ++ POP_ORW ++ METIS_TAC [GREATER_EQ])
 ++ RW_TAC std_ss [summable, sums, SUM_CMUL]
 ++ Q.EXISTS_TAC `(Mjn X p s j n - mjn X p s j n) * (1 / (1 - x))`
 ++ `(\n'. (Mjn X p s j n - mjn X p s j n) * sum (0,n') (\k. x pow k)) = 
     (\n'. (\n'. (Mjn X p s j n - mjn X p s j n)) n' * 
     	   (\n'. sum (0,n') (\k. x pow k)) n')` by RW_TAC std_ss [] 
 ++ POP_ORW
 ++ MATCH_MP_TAC SEQ_MUL 
 ++ RW_TAC std_ss [SEQ_CONST, GSYM REAL_INV_1OVER, GSYM sums] 
 ++ MATCH_MP_TAC GP ++ METIS_TAC [ABS_REFL]);

val SUBSET_SPACES_SIGMA_NEG_EQ_R = prove
  (``!X p s Linit Ltrans k i0 j0. 
   let E = {r | r IN space s /\ cond_pmf p (X k) (X 0) ({r}, {j0}) <= 
   	cond_pmf p (X k) (X 0) ({r}, {i0})} in
   th_dtmc X p s Linit Ltrans /\ 
   0 < prob p (PREIMAGE (X 0) {j0} INTER p_space p) /\
   0 < prob p (PREIMAGE (X 0) {i0} INTER p_space p) ==>
   (SIGMA (\r. cond_pmf p (X k) (X 0) ({r}, {i0}) - cond_pmf p (X k) (X 0) ({r}, {j0})) E =
    - SIGMA (\r. cond_pmf p (X k) (X 0) ({r}, {i0}) - cond_pmf p (X k) (X 0) ({r}, {j0})) 
    (space s DIFF E))``,
    RW_TAC std_ss [GSYM REAL_LNEG_UNIQ] 
 ++ `FINITE (space s)` by FULL_SIMP_TAC std_ss [IRREDUCIABLE_MC_def, th_dtmc_def]
 ++ `prob_space p` 
 	by FULL_SIMP_TAC std_ss [th_dtmc_def, dtmc_def, mc_property_def, random_variable_def]
 ++ `i0 IN space s`
 	by (SPOSE_NOT_THEN STRIP_ASSUME_TAC
 	   ++ `PREIMAGE (X 0) {i0} INTER p_space p = {}`
 	   	by (MATCH_MP_TAC NOTIN_SPACE_EVENTS 
    	   	   ++ Q.EXISTS_TAC `s` 
    	           ++ PSET_TAC [th_dtmc_def, dtmc_def, mc_property_def]) 
    	   ++ FULL_SIMP_TAC real_ss [PROB_EMPTY])
 ++ `j0 IN space s`
 	by (SPOSE_NOT_THEN STRIP_ASSUME_TAC
 	   ++ `PREIMAGE (X 0) {j0} INTER p_space p = {}`
 	   	by (MATCH_MP_TAC NOTIN_SPACE_EVENTS 
    	   	   ++ Q.EXISTS_TAC `s` 
    	           ++ PSET_TAC [th_dtmc_def, dtmc_def, mc_property_def]) 
    	   ++ FULL_SIMP_TAC real_ss [PROB_EMPTY])    	   
 ++ Suff `0 = SIGMA (\r. cond_pmf p (X k) (X 0) ({r},{i0}) -
         cond_pmf p (X k) (X 0) ({r},{j0})) (space s)` 
 >> (RW_TAC std_ss [] 
    ++ `E SUBSET (space s)` by (Q.UNABBREV_TAC `E` ++ PSET_TAC [])
    ++ `FINITE E` by (Q.UNABBREV_TAC `E` ++ METIS_TAC [SUBSET_FINITE])   		
    ++ (MP_TAC o GSYM o Q.ISPECL [`E:'b->bool`,
       `space s DIFF (E:'b->bool)`]) REAL_SUM_IMAGE_DISJOINT_UNION 
    ++ PSET_TAC [UNION_DIFF, DISJOINT_DIFF, FINITE_DIFF]) 
 ++ RW_TAC std_ss [REAL_SUM_IMAGE_SUB, COND_PMF_EQ_COND_PROB]
 ++ Suff `!i. i IN space s /\ 0 < prob p (PREIMAGE (X 0) {i} INTER p_space p) ==> 
 	(SIGMA (\r. cond_prob p (PREIMAGE (X k) {r} INTER p_space p)
           (PREIMAGE (X 0) {i} INTER p_space p)) (space s) = 1)`
 >> RW_TAC std_ss [REAL_SUB_REFL]  
 ++ FULL_SIMP_TAC std_ss [IRREDUCIABLE_MC_def, COMMUNICATE_STATES_def,COND_PMF_EQ_COND_PROB]
 ++ `prob_space p` by FULL_SIMP_TAC std_ss [th_dtmc_def, dtmc_def, mc_property_def,
    		random_variable_def] ++ RW_TAC std_ss []
 ++ `SIGMA (\r. cond_prob p (PREIMAGE (X k) {r} INTER p_space p)
           (PREIMAGE (X 0) {i} INTER p_space p)) (space s) =
        SIGMA (\r. cond_prob p ((\r. PREIMAGE (X k) {r} INTER p_space p) r)
           (PREIMAGE (X 0) {i} INTER p_space p)) (space s)` by RW_TAC std_ss [] ++ POP_ORW
 ++ MATCH_MP_TAC COND_PROB_ADDITIVE ++ RW_TAC std_ss []
 << [METIS_TAC [th_dtmc_def, DTMC_EVENTS],
     METIS_TAC [th_dtmc_def, DTMC_EVENTS],
     RW_TAC std_ss [DISJOINT_PROC_INTER],
     METIS_TAC [th_dtmc_def, dtmc_def, mc_property_def, 
       		 random_variable_def, BIGUNION_PREIMAGEX_IS_PSPACE]]);

val SUM_LE_MUL_MIN = prove
  (``!X p s Linit Ltrans k N i0 j0. 
   let cond_pmf_at_j k j x0 = cond_pmf p (X k) (X 0) ({j},{x0}) in
   let t = IMAGE (\(i, j). cond_pmf p (X k) (X 0) ({j}, {i})) ((space s) CROSS (space s)) in
   let E = {(r:'b) | r IN space s /\ cond_pmf_at_j k r j0 <= cond_pmf_at_j k r i0} in
   th_dtmc X p s Linit Ltrans /\ N <= k /\
   (i0 IN space s) /\ (j0 IN space s) /\   
   (!i j. i IN space s /\ j IN space s ==> 0 < cond_pmf_at_j N j i) ==>
   SIGMA (\r. cond_pmf_at_j k r i0 - cond_pmf_at_j k r j0) E <=
    (1 - (&(CARD E) + &(CARD (space s DIFF E))) * min_set t)``,
    RW_TAC std_ss []     
 ++ `FINITE (space s)` by FULL_SIMP_TAC std_ss [th_dtmc_def]
 ++ `prob_space p` by FULL_SIMP_TAC std_ss [th_dtmc_def, dtmc_def,
 		 mc_property_def, random_variable_def]
 ++ `!t. random_variable (X t) p s` 
 	by FULL_SIMP_TAC std_ss [th_dtmc_def, dtmc_def, mc_property_def] 
 ++ `space s <> {}` by METIS_TAC [RV_NON_EMPTY_SPACE]
 ++ `!N. FINITE (IMAGE (\(i,j). cond_pmf_at_j N j i) ((space s) CROSS (space s)))`
        by (Q.UNABBREV_TAC `cond_pmf_at_j` ++ MATCH_MP_TAC IMAGE_FINITE 
           ++ RW_TAC std_ss [FINITE_CROSS, COND_PMF_EQ_COND_PROB])
 ++ `!N. IMAGE (\(i,j). cond_pmf_at_j N j i) ((space s) CROSS (space s)) <> {}`
        by (SPOSE_NOT_THEN STRIP_ASSUME_TAC ++ Q.UNABBREV_TAC `cond_pmf_at_j`
           ++ `(j0, j0) IN ((space s) CROSS (space s))` by PSET_TAC [IN_CROSS]
           ++ METIS_TAC [IMAGE_EQ_EMPTY, MEMBER_NOT_EMPTY, COND_PMF_EQ_COND_PROB])           
 ++ `E SUBSET (space s)` by (Q.UNABBREV_TAC `E` ++ PSET_TAC [])                
 ++ `FINITE E` by METIS_TAC [SUBSET_FINITE] 
 ++ `!x. x IN IMAGE (\(i,j). cond_pmf_at_j N j i) ((space s) CROSS (space s)) ==> 0 < x`  
 	by (Q.UNABBREV_TAC `cond_pmf_at_j` 
 	   ++ PSET_TAC [IN_IMAGE, IN_CROSS, COND_PMF_EQ_COND_PROB] 
                   ++ `x' = ((FST x'), (SND x'))` by METIS_TAC [PAIR] 
                   ++ POP_ORW ++ RW_TAC std_ss [])
 ++ `!x. x IN IMAGE (\(i,j). cond_pmf_at_j N j i) ((space s) CROSS (space s)) ==> 
     min_set (IMAGE (\(i,j'). cond_pmf_at_j N j' i) (((space s):'b -> bool) CROSS space s)) <= x`
        by (Q.UNABBREV_TAC `cond_pmf_at_j` ++ METIS_TAC [min_set_def, COND_PMF_EQ_COND_PROB])
 ++ `!i k. PREIMAGE (X k) {i} INTER p_space p IN events p`
    	by METIS_TAC [th_dtmc_def, DTMC_EVENTS]      
 ++ Cases_on `prob p (PREIMAGE (X 0) {i0} INTER p_space p) = 0`
 >> (Know `SIGMA (\r. cond_pmf_at_j k r i0 - cond_pmf_at_j k r j0) E <= 0`
    >> (RW_TAC std_ss [] ++ (MP_TAC o GSYM o Q.ISPEC `(E:'b -> bool)`) REAL_SUM_IMAGE_0
       ++ RW_TAC std_ss [] ++ POP_ORW 
       ++ (MP_TAC o Q.ISPEC `(E:'b -> bool)`) REAL_SUM_IMAGE_MONO ++ RW_TAC std_ss []
       ++ POP_ASSUM MATCH_MP_TAC ++ RW_TAC std_ss [REAL_LE_SUB_RADD, REAL_ADD_LID] 
       ++ `x IN space s` by (Q.UNABBREV_TAC `E` ++ PSET_TAC [])
       ++ `PREIMAGE (X k) {x} INTER p_space p IN events p` 
       		by METIS_TAC [th_dtmc_def, DTMC_EVENTS]
       ++ `PREIMAGE (X 0) {j0} INTER p_space p IN events p` 
       		by METIS_TAC [th_dtmc_def, DTMC_EVENTS]
       ++ Q.UNABBREV_TAC `cond_pmf_at_j` 
       ++ RW_TAC std_ss [COND_PMF_EQ_COND_PROB, COND_PROB_ZERO, COND_PROB_BOUNDS])
    ++ RW_TAC std_ss []       
    ++ Suff `0 <= 1 - (&CARD E + &CARD (space s DIFF E)) * min_set t` >> METIS_TAC [REAL_LE_TRANS]
    ++ RW_TAC std_ss [REAL_LE_SUB_LADD, REAL_ADD_LID]
    ++ Know `min_set t = 0` 
    >> (`cond_pmf p (X k) (X 0) ({j0}, {i0}) IN t` 
           by (Q.UNABBREV_TAC `t` ++ PSET_TAC [] 
              ++ Q.EXISTS_TAC `(i0, j0)` 
              ++ PSET_TAC [IN_CROSS])
       ++ `cond_pmf p (X k) (X 0) ({j0}, {i0}) = 0`
           by METIS_TAC [COND_PMF_EQ_COND_PROB, COND_PROB_ZERO]
       ++ `!x. x IN t ==> 0 <= x` by (Q.UNABBREV_TAC `t` 
       		++ RW_TAC std_ss [IN_IMAGE, COND_PMF_EQ_COND_PROB, IN_CROSS]
       		++ `!y n. PREIMAGE (X n) {y} INTER p_space p IN events p` 
       			by METIS_TAC [th_dtmc_def, DTMC_EVENTS]
       		++ `x' = (FST x', SND x')` by METIS_TAC [PAIR] ++ POP_ORW
       		++ RW_TAC std_ss [COND_PROB_BOUNDS]) 
       	++ `t <> {}` by (Q.UNABBREV_TAC `t` ++ SPOSE_NOT_THEN STRIP_ASSUME_TAC 
                      ++ METIS_TAC [MEMBER_NOT_EMPTY])
        ++ `FINITE t` by (Q.UNABBREV_TAC `t` ++ MATCH_MP_TAC IMAGE_FINITE 
           		++ RW_TAC std_ss [FINITE_CROSS])                     
       	++ METIS_TAC [min_set_def, REAL_LE_ANTISYM]) 
     ++ METIS_TAC [REAL_MUL_RZERO, REAL_LT_01, REAL_LT_IMP_LE])
 ++ `0 < prob p (PREIMAGE (X 0) {i0} INTER p_space p)` 
 	by METIS_TAC [PROB_POSITIVE, REAL_LT_LE]
 ++ Suff `SIGMA (\r.  cond_pmf_at_j k r i0 - cond_pmf_at_j k r j0) E =
     1 - SIGMA (\r. cond_pmf_at_j k r j0) E - 
     SIGMA (\r. cond_pmf_at_j k r i0) ((space s) DIFF E)`
 >> (RW_TAC std_ss [] ++ POP_ASSUM K_TAC 
    ++ RW_TAC std_ss [real_sub, GSYM REAL_ADD_ASSOC, REAL_LE_LADD, GSYM REAL_NEG_ADD, 
    	REAL_LE_NEG, REAL_RDISTRIB] ++ MATCH_MP_TAC REAL_LE_ADD2 
    ++ RW_TAC std_ss []
    >> (`!x. x IN E ==> min_set t <= cond_pmf_at_j k x j0` 
           by (RW_TAC std_ss [] ++ Q.UNABBREV_TAC `E` ++ Q.UNABBREV_TAC `cond_pmf_at_j`
              ++ Q.UNABBREV_TAC `t` ++ `x IN space s` by PSET_TAC [IN_DIFF]
              ++ `cond_pmf p (X k) (X 0) ({x},{j0}) IN 
        		(IMAGE (\(i,j). cond_pmf p (X k) (X 0) ({j},{i})) (space s CROSS space s))`
             	  by (PSET_TAC [IN_IMAGE] ++ Q.EXISTS_TAC `((j0:'b), (x:'b))` 
             	     ++ RW_TAC std_ss [IN_CROSS]) ++ METIS_TAC [min_set_def]) 
       ++ (MP_TAC o Q.ISPEC `(E:'b -> bool)`) REAL_SUM_IMAGE_MONO ++ RW_TAC std_ss [] 
       ++ POP_ASSUM (MP_TAC o Q.SPECL [`(\(r:'b). min_set t)`,
       	 `(\(r:'b). cond_pmf_at_j (k:num) r (j0:'b))`]) ++ RW_TAC std_ss [] 
       ++ Suff `&CARD E * min_set t = SIGMA (\r. min_set t) E` >> METIS_TAC []
       ++ (MP_TAC o Q.ISPEC `(E:'b -> bool)` o GSYM)
          REAL_SUM_IMAGE_FINITE_CONST ++ RW_TAC std_ss [])
     ++ `!x. x IN ((space s):'b -> bool) DIFF E ==> min_set t <= cond_pmf_at_j k x i0` 
           by (RW_TAC std_ss [] ++ Q.UNABBREV_TAC `t` ++ Q.UNABBREV_TAC `cond_pmf_at_j`
              ++ `x IN space s` by PSET_TAC [IN_DIFF]
              ++ `cond_pmf p (X k) (X 0) ({x},{i0}) IN 
        		(IMAGE (\(i,j). cond_pmf p (X k) (X 0) ({j},{i})) (space s CROSS space s))`
             	  by (PSET_TAC [IN_IMAGE] ++ Q.EXISTS_TAC `((i0:'b), (x:'b))` 
             	     ++ RW_TAC std_ss [IN_CROSS]) ++ METIS_TAC [min_set_def])
     ++ (MP_TAC o Q.ISPEC `((space s):'b -> bool) DIFF E`) REAL_SUM_IMAGE_MONO 
     ++ RW_TAC std_ss [FINITE_DIFF] 
     ++ POP_ASSUM (MP_TAC o Q.SPECL [`(\(r:'b). min_set t)`,
       	 `(\(r:'b). cond_pmf_at_j (k:num) r (i0:'b))`]) ++ RW_TAC std_ss [] 
     ++ Suff `&CARD (space s DIFF E) * min_set t = 
           SIGMA (\r. min_set t) (space s DIFF E)` >> METIS_TAC []          
     ++ `FINITE (space s DIFF E)` by PSET_TAC [FINITE_DIFF]
     ++ (MP_TAC o Q.ISPEC `(space s DIFF (E:'b -> bool))` o GSYM) REAL_SUM_IMAGE_FINITE_CONST 
     ++ RW_TAC std_ss [])
 ++ `!(x:real) y z. x - y - z = x - z - y` 
 	by METIS_TAC [real_sub, REAL_ADD_ASSOC, REAL_ADD_COMM] 
 ++ POP_ORW 
 ++ RW_TAC std_ss [REAL_EQ_SUB_LADD, COND_PMF_EQ_COND_PROB, GSYM REAL_SUM_IMAGE_ADD, REAL_SUB_ADD]
 ++ Suff `SIGMA (\r. cond_pmf_at_j k r i0) (space s) = 1` 
 >> (RW_TAC std_ss [EQ_SYM_EQ] ++ POP_ORW
    ++ (MP_TAC o Q.SPECL [`(space s):'b -> bool`, `(E:'b -> bool)`])
		REAL_SUM_IMAGE_DIFF ++ RW_TAC std_ss []) 
 ++ Q.UNABBREV_TAC `cond_pmf_at_j` 
 ++ RW_TAC std_ss [COND_PMF_EQ_COND_PROB]
 ++ `SIGMA (\r. cond_prob p (PREIMAGE (X k) {r} INTER p_space p)
           (PREIMAGE (X 0) {i0} INTER p_space p)) (space s) =
     SIGMA (\r. cond_prob p ((\r. PREIMAGE (X k) {r} INTER p_space p) r)
           (PREIMAGE (X 0) {i0} INTER p_space p)) (space s)` by RW_TAC std_ss [] 
 ++ POP_ORW
 ++ MATCH_MP_TAC COND_PROB_ADDITIVE ++ RW_TAC std_ss []
 >> RW_TAC std_ss [DISJOINT_PROC_INTER] 
 ++ METIS_TAC [th_dtmc_def, dtmc_def, mc_property_def, 
       		 random_variable_def, BIGUNION_PREIMAGEX_IS_PSPACE]);
       		       		       		 
val POSITIVE_SUME = prove
  (``!(X:num -> 'a -> 'b) p s k i0 j0. 
   FINITE (space s) /\ i0 IN space s /\ j0 IN space s ==>
   0 <= SIGMA (\r. cond_pmf p (X k) (X 0) ({r},{i0}) - cond_pmf p (X k) (X 0) ({r},{j0})) 
   	{(r:'b) | r IN space s /\ 
   		cond_pmf p (X k) (X 0) ({r},{j0}) <= cond_pmf p (X k) (X 0) ({r},{i0})}``,
    RW_TAC std_ss []	
 ++ `{(r:'b) | r IN space s /\ 
 	cond_pmf p (X k) (X 0) ({r},{j0}) <= cond_pmf p (X k) (X 0) ({r},{i0})} SUBSET space s`
 	by PSET_TAC []    
 ++ MATCH_MP_TAC REAL_SUM_IMAGE_POS 
 ++ RW_TAC std_ss [(UNDISCH o Q.ISPEC `(space s):'b -> bool`) SUBSET_FINITE] 
 ++ PSET_TAC [REAL_SUB_LE]);
    
val MAX_SUB_MIN_LE_IMP_SUMS_1 = prove
  (``!X p s Linit Ltrans j N n i0 j0. 
   let cond_pmf_at_j k j x0 = cond_pmf p (X k) (X 0) ({j},{x0}) in
   let s' = {r | r IN space s /\ cond_pmf_at_j N r j0 <= cond_pmf_at_j N r i0} in
   let Mjn = Mjn X p s j and mjn = mjn X p s j in
   let t = IMAGE (\(i, j). cond_pmf p (X N) (X 0) ({j}, {i})) ((space s) CROSS (space s)) in 
   th_dtmc X p s Linit Ltrans /\ j IN space s /\ 0 < n /\
   i0 IN space s /\ j0 IN space s /\ 0 < N /\ 0 < prob p (PREIMAGE (X 0) {j} INTER p_space p) /\
   (!i j. i IN space s /\ j IN space s ==> 0 < cond_pmf_at_j N j i) ==>
   cond_pmf_at_j (N+n) j i0 - cond_pmf_at_j (N+n) j j0 <= 
    (Mjn n - mjn n) * (1 - (&(CARD s') + &(CARD (space s DIFF s'))) * min_set t)``,
   	
    RW_TAC std_ss [] 
 ++ `prob_space p` by PSET_TAC [th_dtmc_def, dtmc_def, mc_property_def, random_variable_def] 
 ++ `FINITE (space s)` by FULL_SIMP_TAC std_ss [th_dtmc_def]
 ++ `!t. random_variable (X t) p s` 
 	by FULL_SIMP_TAC std_ss [th_dtmc_def, dtmc_def, mc_property_def]  
 ++ `space s <> {}` by METIS_TAC [RV_NON_EMPTY_SPACE] 
 ++ `!n. FINITE (IMAGE (\i. cond_prob p (PREIMAGE (X n) {j} INTER p_space p)
              (PREIMAGE (X 0) {i} INTER p_space p)) (space s))` 
              by (MATCH_MP_TAC IMAGE_FINITE ++ RW_TAC std_ss [])
 ++ `!n. (IMAGE (\i. cond_prob p (PREIMAGE (X n) {j} INTER p_space p)
              (PREIMAGE (X 0) {i} INTER p_space p)) (space s)) <> {}`
              by (SPOSE_NOT_THEN STRIP_ASSUME_TAC ++ METIS_TAC [IMAGE_EQ_EMPTY])  
 ++ `!N. FINITE (IMAGE (\(i,j). cond_pmf_at_j N j i) ((space s) CROSS (space s)))`
        by (Q.UNABBREV_TAC `cond_pmf_at_j` ++ MATCH_MP_TAC IMAGE_FINITE 
           ++ RW_TAC std_ss [FINITE_CROSS, COND_PMF_EQ_COND_PROB])
 ++ `!N. IMAGE (\(i,j). cond_pmf_at_j N j i) ((space s) CROSS (space s)) <> {}`
        by (SPOSE_NOT_THEN STRIP_ASSUME_TAC ++ Q.UNABBREV_TAC `cond_pmf_at_j`
           ++ `(j, j) IN ((space s) CROSS (space s))` by PSET_TAC [IN_CROSS]
           ++ METIS_TAC [IMAGE_EQ_EMPTY, MEMBER_NOT_EMPTY, COND_PMF_EQ_COND_PROB])     
 ++ `!i k. PREIMAGE (X k) {i} INTER p_space p IN events p`
    	by METIS_TAC [th_dtmc_def, DTMC_EVENTS]
 ++ Cases_on `prob p (PREIMAGE (X 0) {i0} INTER p_space p) = 0`
 >> (`- cond_pmf_at_j (N + n) j j0 <= 0` by (RW_TAC std_ss [REAL_NEG_LE0] 
 		++ Q.UNABBREV_TAC `cond_pmf_at_j` 
 		++ METIS_TAC [COND_PMF_EQ_COND_PROB, COND_PROB_BOUNDS])
    ++ `cond_pmf_at_j (N + n) j i0 = 0` 
    	by (Q.UNABBREV_TAC `cond_pmf_at_j` ++ METIS_TAC [COND_PMF_EQ_COND_PROB, COND_PROB_ZERO])
    ++ RW_TAC std_ss [REAL_SUB_LZERO]
    ++ Suff `0 <= (Mjn' n - mjn' n) * 
    		(1 - (&CARD s' + &CARD (space s DIFF s')) * min_set t)`
    >> METIS_TAC [REAL_LE_TRANS]
    ++ MATCH_MP_TAC REAL_LE_MUL	++ RW_TAC std_ss [REAL_LE_SUB_LADD, REAL_ADD_LID]
    >> (Q.UNABBREV_TAC `mjn'` ++ Q.UNABBREV_TAC `Mjn'` ++ METIS_TAC [THDTMC_MAX_MIN_COND_PROB])
    ++ Know `min_set t = 0` 
    >> (`cond_pmf_at_j N j i0 IN t` 
           by (Q.UNABBREV_TAC `t` ++ Q.UNABBREV_TAC `cond_pmf_at_j` ++ PSET_TAC [] 
              ++ Q.EXISTS_TAC `(i0, j)` ++ PSET_TAC [IN_CROSS])
       ++ `cond_pmf p (X N) (X 0) ({j}, {i0}) = 0`
           by METIS_TAC [COND_PMF_EQ_COND_PROB, COND_PROB_ZERO]
       ++ `!x. x IN t ==> 0 <= x` by (Q.UNABBREV_TAC `t` 
       		++ RW_TAC std_ss [IN_IMAGE, COND_PMF_EQ_COND_PROB, IN_CROSS]
       		++ `x' = (FST x', SND x')` by METIS_TAC [PAIR] ++ POP_ORW
       		++ RW_TAC std_ss [COND_PROB_BOUNDS]) 
       	++ `t <> {}` by (Q.UNABBREV_TAC `t` ++ SPOSE_NOT_THEN STRIP_ASSUME_TAC 
                      ++ METIS_TAC [MEMBER_NOT_EMPTY])
        ++ `FINITE t` by (Q.UNABBREV_TAC `t` ++ MATCH_MP_TAC IMAGE_FINITE 
           		++ RW_TAC std_ss [FINITE_CROSS])                     
       	++ METIS_TAC [min_set_def, REAL_LE_ANTISYM]) 
     ++ METIS_TAC [REAL_MUL_RZERO, REAL_LT_01, REAL_LT_IMP_LE])
 ++ Cases_on `prob p (PREIMAGE (X 0) {j0} INTER p_space p) = 0`
 >> (`cond_pmf_at_j (N + n) j j0 = 0` 
    	by (Q.UNABBREV_TAC `cond_pmf_at_j` 
    	   ++ METIS_TAC [COND_PMF_EQ_COND_PROB, COND_PROB_ZERO])
    ++ `mjn' n = 0` by (Q.UNABBREV_TAC `mjn'` ++ RW_TAC std_ss [mjn_def]
         ++ `cond_prob p (PREIMAGE (X n) {j} INTER p_space p)
              (PREIMAGE (X 0) {j0} INTER p_space p) IN 
              IMAGE (\i. cond_prob p (PREIMAGE (X n) {j} INTER p_space p)
              (PREIMAGE (X 0) {i} INTER p_space p)) (space s)`
              by (PSET_TAC [] ++ Q.EXISTS_TAC `j0` ++ RW_TAC std_ss [])
         ++ `cond_prob p (PREIMAGE (X n) {j} INTER p_space p)
              (PREIMAGE (X 0) {j0} INTER p_space p) = 0` by METIS_TAC [COND_PROB_ZERO]
         ++ Q.UNABBREV_TAC `cond_pmf_at_j` 
         ++ `!x. x IN IMAGE (\i. cond_prob p (PREIMAGE (X n) {j} INTER p_space p)
              (PREIMAGE (X 0) {i} INTER p_space p)) (space s) ==> 0 <= x` 
              by (RW_TAC std_ss [IN_IMAGE] ++ METIS_TAC [COND_PROB_BOUNDS])
         ++ METIS_TAC [min_set_def, REAL_LE_ANTISYM]) 
    ++ Know `min_set t = 0` 
    >> (`cond_pmf_at_j N j j0 IN t` 
           by (Q.UNABBREV_TAC `t` ++ Q.UNABBREV_TAC `cond_pmf_at_j` ++ PSET_TAC [] 
              ++ Q.EXISTS_TAC `(j0, j)` ++ PSET_TAC [IN_CROSS])
       ++ `cond_pmf p (X N) (X 0) ({j}, {j0}) = 0`
           by METIS_TAC [COND_PMF_EQ_COND_PROB, COND_PROB_ZERO]
       ++ `!x. x IN t ==> 0 <= x` by (Q.UNABBREV_TAC `t` 
       		++ RW_TAC std_ss [IN_IMAGE, COND_PMF_EQ_COND_PROB, IN_CROSS]
       		++ `x' = (FST x', SND x')` by METIS_TAC [PAIR] ++ POP_ORW
       		++ RW_TAC std_ss [COND_PROB_BOUNDS]) 
       	++ `t <> {}` by (Q.UNABBREV_TAC `t` ++ SPOSE_NOT_THEN STRIP_ASSUME_TAC 
                      ++ METIS_TAC [MEMBER_NOT_EMPTY])
        ++ `FINITE t` by (Q.UNABBREV_TAC `t` ++ MATCH_MP_TAC IMAGE_FINITE 
           		++ RW_TAC std_ss [FINITE_CROSS])                     
       	++ METIS_TAC [min_set_def, REAL_LE_ANTISYM]) 
    ++ RW_TAC std_ss [REAL_SUB_RZERO, REAL_MUL_RZERO, REAL_MUL_RID]
    ++ Suff `cond_pmf_at_j (N + n) j i0 <= Mjn' (N + n)`
    >> (Suff `Mjn' (N + n) <= Mjn' n` >> METIS_TAC [REAL_LE_TRANS] 
       ++ `i0 <> j0` by (SPOSE_NOT_THEN STRIP_ASSUME_TAC ++ METIS_TAC [])
       ++ (MP_TAC o Q.ISPEC `(space s):'b -> bool`) CARD_PSUBSET 
       		++ RW_TAC std_ss [FINITE_EMPTY] ++ POP_ASSUM (MP_TAC o Q.SPEC `{}:'b -> bool`) 
       		++ RW_TAC std_ss [PSUBSET_DEF, EMPTY_SUBSET, CARD_DEF]
       ++ `2 <= CARD (space s)` by METIS_TAC [CARD_GT_2]
       ++ `1 < CARD (space s)` by RW_TAC arith_ss [] ++ METIS_TAC [MAX_DECREASE])	
    ++ Q.UNABBREV_TAC `Mjn'` ++ Q.UNABBREV_TAC `cond_pmf_at_j`
    ++ RW_TAC std_ss [Mjn_def, COND_PMF_EQ_COND_PROB]
    ++ `cond_prob p (PREIMAGE (X (N + n)) {j} INTER p_space p)
              (PREIMAGE (X 0) {i0} INTER p_space p) IN 
              IMAGE (\i. cond_prob p (PREIMAGE (X (N + n)) {j} INTER p_space p)
              (PREIMAGE (X 0) {i} INTER p_space p)) (space s)`
              by (PSET_TAC [] ++ Q.EXISTS_TAC `i0` ++ RW_TAC std_ss [])
    ++ METIS_TAC [max_set_def])
 ++ `0 < prob p (PREIMAGE (X 0) {j0} INTER p_space p) /\ 
 	0 < prob p (PREIMAGE (X 0) {i0} INTER p_space p)` 
 	by METIS_TAC [PROB_POSITIVE, REAL_LT_LE]
 ++ NTAC 2 (POP_ASSUM MP_TAC) ++ NTAC 2 (POP_ASSUM K_TAC) ++ RW_TAC std_ss []
 ++ Know `cond_pmf_at_j (N + n) j i0 - cond_pmf_at_j (N + n) j j0 <=
      SIGMA (\k. cond_pmf p (X N) (X 0) ({k}, {i0}) - cond_pmf p (X N) (X 0) ({k}, {j0})) s' *
      	 (Mjn' n - mjn' n)`
 >> (RW_TAC std_ss []
    ++ Know `cond_pmf_at_j (N + n) j i0 - cond_pmf_at_j (N + n) j j0 =
             SIGMA (\k. cond_pmf_at_j n j k * cond_pmf p (X N) (X 0) ({k}, {i0}) -
                        cond_pmf_at_j n j k * cond_pmf p (X N) (X 0) ({k}, {j0})) (space s)`
    >> (Q.UNABBREV_TAC `cond_pmf_at_j` 
       ++ (MP_TAC o Q.SPECL [`(X:num -> 'a -> 'b)`, `p`, `s`, `N`, `n`, `i0`, 
    		`j`, `Linit`, `Ltrans`]) THMC_MNGT_CK_EQ 
       ++ RW_TAC std_ss [COND_PMF_EQ_COND_PROB, ADD_COMM]
       ++ (MP_TAC o Q.SPECL [`(X:num -> 'a -> 'b)`, `p`, `s`, `N`, `n`, `j0`, 
    		`j`, `Linit`, `Ltrans`]) THMC_MNGT_CK_EQ 
       ++ RW_TAC std_ss [COND_PMF_EQ_COND_PROB, ADD_COMM, REAL_SUM_IMAGE_SUB]) 
    ++ RW_TAC std_ss [GSYM REAL_SUB_LDISTRIB]
    ++ POP_ASSUM K_TAC 
    ++ `s' SUBSET (space s)` 
    	by (Q.UNABBREV_TAC `s'` ++ Q.UNABBREV_TAC `cond_pmf_at_j` ++ PSET_TAC [])
    ++ (MP_TAC o Q.SPECL [`(space s)`, `s'`]) REAL_SUM_IMAGE_DIFF 
    ++ RW_TAC std_ss [REAL_SUB_LDISTRIB, real_sub, GSYM REAL_MUL_LNEG] ++ POP_ASSUM K_TAC 
    ++ Know `-SIGMA (\k. cond_pmf p (X N) (X 0) ({k},{i0}) + 
    			-cond_pmf p (X N) (X 0) ({k},{j0})) s' =
    	     SIGMA (\k. cond_pmf p (X N) (X 0) ({k},{i0}) + 
    			-cond_pmf p (X N) (X 0) ({k},{j0})) (space s DIFF s')`
    >> (Q.UNABBREV_TAC `s'` ++ Q.UNABBREV_TAC `cond_pmf_at_j` 
       ++ (MP_TAC o Q.SPECL [`(X:num -> 'a -> 'b)`, `p`, `s`, `Linit`, `Ltrans`, `N`, 
    	`i0`, `j0`]) SUBSET_SPACES_SIGMA_NEG_EQ_R 
       ++ RW_TAC std_ss [IRREDUCIABLE_MC_def, COND_PMF_EQ_COND_PROB, GSYM real_sub, REAL_NEG_EQ]
       ++ METIS_TAC []) ++ RW_TAC std_ss []
    ++ MATCH_MP_TAC REAL_LE_ADD2 ++ POP_ASSUM K_TAC ++ `FINITE s'` by METIS_TAC [SUBSET_FINITE]
    ++ RW_TAC std_ss [REAL_MUL_COMM, REAL_MUL_LNEG, GSYM real_sub, GSYM REAL_SUB_LDISTRIB, 
    		GSYM  REAL_SUM_IMAGE_CMUL] 
    >> ((MP_TAC o Q.ISPEC `(s':'b -> bool)`) REAL_SUM_IMAGE_MONO 
       ++ RW_TAC std_ss [] ++ POP_ASSUM MATCH_MP_TAC ++ RW_TAC std_ss []
       ++ `0 <= cond_pmf p (X N) (X 0) ({x},{i0}) - cond_pmf p (X N) (X 0) ({x},{j0})`
       		by (Q.UNABBREV_TAC `s'` ++ Q.UNABBREV_TAC `cond_pmf_at_j` 
       		   ++ PSET_TAC [REAL_SUB_LE, COND_PMF_EQ_COND_PROB])
       ++ MATCH_MP_TAC REAL_LE_RMUL_IMP ++ RW_TAC std_ss [] ++ Q.UNABBREV_TAC `Mjn'` 
       ++ Q.UNABBREV_TAC `cond_pmf_at_j`
       ++ PSET_TAC [IN_DEF, GSYM real_sub, REAL_SUB_LE, Mjn_def, COND_PMF_EQ_COND_PROB]
       ++ `cond_prob p (PREIMAGE (X n) {j} INTER p_space p)
      			(PREIMAGE (X 0) {x} INTER p_space p) IN
      	      IMAGE (\i. cond_prob p (PREIMAGE (X n) {j} INTER p_space p)
              (PREIMAGE (X 0) {i} INTER p_space p)) (space s)` 
              by (PSET_TAC [IN_IMAGE] ++ Q.EXISTS_TAC `x` ++ RW_TAC std_ss [IN_DEF])
       ++ METIS_TAC [max_set_def])	
    ++ RW_TAC std_ss [GSYM REAL_SUM_IMAGE_CMUL, FINITE_DIFF]	
    ++ (MP_TAC o Q.ISPEC `space s DIFF (s':'b -> bool)`) REAL_SUM_IMAGE_MONO 
    ++ RW_TAC std_ss [FINITE_DIFF] ++ POP_ASSUM MATCH_MP_TAC ++ RW_TAC std_ss []
    ++ `cond_pmf p (X N) (X 0) ({x},{i0}) - cond_pmf p (X N) (X 0) ({x},{j0}) =
       -(cond_pmf p (X N) (X 0) ({x},{j0}) - cond_pmf p (X N) (X 0) ({x},{i0}))`
           by METIS_TAC [COND_PMF_EQ_COND_PROB, REAL_NEG_SUB] ++ POP_ORW 
    ++ RW_TAC std_ss [REAL_MUL_RNEG, REAL_LE_NEG]
    ++ `0 <= cond_pmf p (X N) (X 0) ({x},{j0}) - cond_pmf p (X N) (X 0) ({x},{i0})`
     	by (Q.UNABBREV_TAC `s'` ++ PSET_TAC [COND_PMF_EQ_COND_PROB, REAL_NOT_LE, REAL_SUB_LE] 
        ++ METIS_TAC [REAL_LT_IMP_LE])
    ++ MATCH_MP_TAC REAL_LE_RMUL_IMP ++ RW_TAC std_ss [] ++ Q.UNABBREV_TAC `cond_pmf_at_j`
    ++ Q.UNABBREV_TAC `mjn'` ++ RW_TAC std_ss [mjn_def, COND_PMF_EQ_COND_PROB]
    ++ `cond_prob p (PREIMAGE (X n) {j} INTER p_space p)
      			(PREIMAGE (X 0) {x} INTER p_space p) IN
      	      IMAGE (\i. cond_prob p (PREIMAGE (X n) {j} INTER p_space p)
              (PREIMAGE (X 0) {i} INTER p_space p)) (space s)` 
              by (PSET_TAC [IN_IMAGE] ++ Q.EXISTS_TAC `x` ++ RW_TAC std_ss [IN_DEF])
    ++ METIS_TAC [min_set_def]) 
 ++ RW_TAC std_ss []
 ++ Suff `SIGMA
      (\k.
         cond_pmf p (X N) (X 0) ({k},{i0}) -
         cond_pmf p (X N) (X 0) ({k},{j0})) s' * (Mjn' n - mjn' n) <= (Mjn' n - mjn' n) *
    (1 - (&CARD s' + &CARD (space s DIFF s')) * min_set t)` 
 >> METIS_TAC [REAL_LE_TRANS] 
 ++ `0 <= Mjn' n - mjn' n` 
 	by (Q.UNABBREV_TAC `mjn'` ++ Q.UNABBREV_TAC `Mjn'` 
 	   ++ RW_TAC std_ss [mjn_def, Mjn_def, min_set_le_max_set, REAL_SUB_LE])
 ++ RW_TAC std_ss [REAL_MUL_COMM] ++ MATCH_MP_TAC REAL_LE_LMUL_IMP ++ RW_TAC std_ss [] 
 ++ `min_set t * (&CARD s' + &CARD (space s DIFF s')) = 
 	(&CARD s' + &CARD (space s DIFF s')) * min_set t` by RW_TAC std_ss [REAL_MUL_COMM]
 ++ POP_ORW ++ Q.UNABBREV_TAC `s'` ++ Q.UNABBREV_TAC `cond_pmf_at_j` ++ Q.UNABBREV_TAC `t`
 ++ (ASSUME_TAC o BETA_RULE o REWRITE_RULE[LET_DEF] o 
 	Q.SPECL [`X`, `p`, `s`, `Linit`, `Ltrans`, `N`, `N`, `i0`, `j0`]) SUM_LE_MUL_MIN
 ++ FULL_SIMP_TAC std_ss [IRREDUCIABLE_MC_def, COND_PMF_EQ_COND_PROB]); 
     
val MAX_SUB_MIN_LE_IMP_SUMS = prove
  (``!X p s Linit Ltrans j N n k i0 j0. 
   let cond_pmf_at_j k j x0 = cond_pmf p (X k) (X 0) ({j},{x0}) in
   let t = IMAGE (\(i, j). cond_pmf_at_j N j i) (space s CROSS space s) in
   let E = {(r:'b) | r IN space s /\ cond_pmf_at_j N r j0 <= cond_pmf_at_j N r i0} in
   let Mjn = Mjn X p s j and mjn = mjn X p s j in
   th_dtmc X p s Linit Ltrans /\ j IN space s /\ 1 <= k /\ 0 < n /\
   i0 IN space s /\ j0 IN space s /\ 0 < N /\
   0 < prob p (PREIMAGE (X 0) {j} INTER p_space p) /\
   (!i j. i IN space s /\ j IN space s ==> 0 < cond_pmf_at_j N j i) ==>
   cond_pmf_at_j (k * N + n) j i0 - cond_pmf_at_j (k * N + n) j j0 <= 
   (Mjn n - mjn n) * (1 - (&(CARD E) + &(CARD (space s DIFF E))) * min_set t) pow k``,   	
    Induct_on `k` >> (RW_TAC std_ss [] ++ RW_TAC std_ss [])
 ++ RW_TAC std_ss [IRREDUCIABLE_MC_def, COND_PMF_EQ_COND_PROB] 
 ++ `FINITE (space s)` by FULL_SIMP_TAC std_ss [IRREDUCIABLE_MC_def, th_dtmc_def]
 ++ `prob_space p` by FULL_SIMP_TAC std_ss [IRREDUCIABLE_MC_def,th_dtmc_def, dtmc_def,
 		 mc_property_def, random_variable_def]
 ++ `!t. random_variable (X t) p s` 
 	by FULL_SIMP_TAC std_ss [IRREDUCIABLE_MC_def, th_dtmc_def, dtmc_def, mc_property_def] 
 ++ `space s <> {}` by METIS_TAC [RV_NON_EMPTY_SPACE]
 ++ `!N. FINITE (IMAGE (\i. cond_pmf_at_j N j i) (space s))` 
        by (MATCH_MP_TAC IMAGE_FINITE ++ RW_TAC std_ss [])
 ++ `!N. (IMAGE (\i. cond_pmf_at_j N j i) (space s)) <> {}`
              by (SPOSE_NOT_THEN STRIP_ASSUME_TAC ++ METIS_TAC [IMAGE_EQ_EMPTY])
 ++ `E SUBSET (space s)` by (Q.UNABBREV_TAC `E` ++ PSET_TAC [])                
 ++ `FINITE E` by METIS_TAC [SUBSET_FINITE]   
 ++ Cases_on `k = 0`
 >> (RW_TAC std_ss [POW_1] ++ Q.UNABBREV_TAC `E` ++ Q.UNABBREV_TAC `cond_pmf_at_j`
    ++ Q.UNABBREV_TAC `mjn'` ++ Q.UNABBREV_TAC `Mjn'` 
    ++ Q.UNABBREV_TAC `t` ++ (ASSUME_TAC o BETA_RULE o REWRITE_RULE[LET_DEF] o 
       Q.SPECL [`X`, `p`, `s`, `Linit`, `Ltrans`, `j`, `N`, `n`, `i0`, `j0`])
       MAX_SUB_MIN_LE_IMP_SUMS_1
    ++ FULL_SIMP_TAC std_ss [IRREDUCIABLE_MC_def, COND_PMF_EQ_COND_PROB])
 ++ `1 <= k` by RW_TAC arith_ss []
 ++ `!i k. PREIMAGE (X k) {i} INTER p_space p IN events p`
    	by METIS_TAC [th_dtmc_def, DTMC_EVENTS]
 ++ Cases_on `prob p (PREIMAGE (X 0) {i0} INTER p_space p) = 0`
 >> (`- cond_pmf_at_j (SUC k * N + n) j j0 <= 0` by (RW_TAC std_ss [REAL_NEG_LE0] 
 		++ Q.UNABBREV_TAC `cond_pmf_at_j` 
 		++ METIS_TAC [COND_PMF_EQ_COND_PROB, COND_PROB_BOUNDS])
    ++ `cond_pmf_at_j (SUC k * N + n) j i0 = 0` 
    	by (Q.UNABBREV_TAC `cond_pmf_at_j` ++ METIS_TAC [COND_PMF_EQ_COND_PROB, COND_PROB_ZERO])
    ++ RW_TAC std_ss [REAL_SUB_LZERO]
    ++ Suff `0 <= (Mjn' n - mjn' n) * 
    		(1 - (&CARD E + &CARD (space s DIFF E)) * min_set t) pow SUC k`
    >> METIS_TAC [REAL_LE_TRANS]
    ++ MATCH_MP_TAC REAL_LE_MUL	++ RW_TAC std_ss [REAL_LE_SUB_LADD, REAL_ADD_LID]
    >> (Q.UNABBREV_TAC `mjn'` ++ Q.UNABBREV_TAC `Mjn'` ++ METIS_TAC [THDTMC_MAX_MIN_COND_PROB])
    ++ Know `min_set t = 0` 
    >> (`cond_pmf_at_j N j i0 IN t` 
           by (Q.UNABBREV_TAC `t` ++ Q.UNABBREV_TAC `cond_pmf_at_j` ++ PSET_TAC [] 
              ++ Q.EXISTS_TAC `(i0, j)` ++ PSET_TAC [IN_CROSS])
       ++ `cond_pmf p (X N) (X 0) ({j}, {i0}) = 0`
           by METIS_TAC [COND_PMF_EQ_COND_PROB, COND_PROB_ZERO]
       ++ `!x. x IN t ==> 0 <= x` by (Q.UNABBREV_TAC `t` ++ Q.UNABBREV_TAC `cond_pmf_at_j`
       		++ RW_TAC std_ss [IN_IMAGE, COND_PMF_EQ_COND_PROB, IN_CROSS]
       		++ `x' = (FST x', SND x')` by METIS_TAC [PAIR] ++ POP_ORW
       		++ RW_TAC std_ss [COND_PROB_BOUNDS]) 
       	++ `t <> {}` by (Q.UNABBREV_TAC `t` ++ SPOSE_NOT_THEN STRIP_ASSUME_TAC 
                      ++ METIS_TAC [MEMBER_NOT_EMPTY])
        ++ `FINITE t` by (Q.UNABBREV_TAC `t` ++ MATCH_MP_TAC IMAGE_FINITE 
           		++ RW_TAC std_ss [FINITE_CROSS]) 
        ++ Q.UNABBREV_TAC `cond_pmf_at_j` ++ FULL_SIMP_TAC std_ss [COND_PMF_EQ_COND_PROB]
       	++ METIS_TAC [min_set_def, REAL_LE_ANTISYM]) 
     ++ METIS_TAC [REAL_MUL_RZERO, REAL_SUB_RZERO, POW_ONE, REAL_LT_01, REAL_LT_IMP_LE])
 ++ Cases_on `prob p (PREIMAGE (X 0) {j0} INTER p_space p) = 0`
 >> (`cond_pmf_at_j (SUC k * N + n) j j0 = 0` 
    	by (Q.UNABBREV_TAC `cond_pmf_at_j` ++ METIS_TAC [COND_PMF_EQ_COND_PROB, COND_PROB_ZERO])
    ++ `mjn' n = 0` by (Q.UNABBREV_TAC `mjn'` ++ RW_TAC std_ss [mjn_def]
         ++ `cond_prob p (PREIMAGE (X n) {j} INTER p_space p)
              (PREIMAGE (X 0) {j0} INTER p_space p) IN 
              IMAGE (\i. cond_prob p (PREIMAGE (X n) {j} INTER p_space p)
              (PREIMAGE (X 0) {i} INTER p_space p)) (space s)`
              by (PSET_TAC [] ++ Q.EXISTS_TAC `j0` ++ RW_TAC std_ss [])
         ++ `cond_prob p (PREIMAGE (X n) {j} INTER p_space p)
              (PREIMAGE (X 0) {j0} INTER p_space p) = 0` by METIS_TAC [COND_PROB_ZERO]
         ++ Q.UNABBREV_TAC `cond_pmf_at_j` 
         ++ `!x. x IN IMAGE (\i. cond_prob p (PREIMAGE (X n) {j} INTER p_space p)
              (PREIMAGE (X 0) {i} INTER p_space p)) (space s) ==> 0 <= x` 
              by (RW_TAC std_ss [IN_IMAGE] ++ METIS_TAC [COND_PROB_BOUNDS])
         ++ METIS_TAC [min_set_def, REAL_LE_ANTISYM]) 
    ++ Know `min_set t = 0` 
    >> (`cond_pmf_at_j N j j0 IN t` 
           by (Q.UNABBREV_TAC `t` ++ Q.UNABBREV_TAC `cond_pmf_at_j` ++ PSET_TAC [] 
              ++ Q.EXISTS_TAC `(j0, j)` ++ PSET_TAC [IN_CROSS])
       ++ `cond_pmf p (X N) (X 0) ({j}, {j0}) = 0`
           by METIS_TAC [COND_PMF_EQ_COND_PROB, COND_PROB_ZERO]
       ++ `!x. x IN t ==> 0 <= x` by (Q.UNABBREV_TAC `t` ++ Q.UNABBREV_TAC `cond_pmf_at_j`
       		++ RW_TAC std_ss [IN_IMAGE, COND_PMF_EQ_COND_PROB, IN_CROSS]
       		++ `x' = (FST x', SND x')` by METIS_TAC [PAIR] ++ POP_ORW
       		++ RW_TAC std_ss [COND_PROB_BOUNDS]) 
       ++ `t <> {}` by (Q.UNABBREV_TAC `t` ++ SPOSE_NOT_THEN STRIP_ASSUME_TAC 
                      ++ METIS_TAC [MEMBER_NOT_EMPTY])
       ++ `FINITE t` by (Q.UNABBREV_TAC `t` ++ MATCH_MP_TAC IMAGE_FINITE 
           		++ RW_TAC std_ss [FINITE_CROSS])                     
       ++  Q.UNABBREV_TAC `cond_pmf_at_j` ++ FULL_SIMP_TAC std_ss [COND_PMF_EQ_COND_PROB]
       ++ METIS_TAC [min_set_def, REAL_LE_ANTISYM]) 
    ++ RW_TAC std_ss [REAL_SUB_RZERO, REAL_MUL_RZERO, POW_ONE, REAL_MUL_RID]
    ++ Suff `cond_pmf_at_j (SUC k * N + n) j i0 <= Mjn' (SUC k * N + n)`
    >> (Suff `Mjn' (SUC k * N + n) <= Mjn' n` >> METIS_TAC [REAL_LE_TRANS] 
       ++ `i0 <> j0` by (SPOSE_NOT_THEN STRIP_ASSUME_TAC ++ METIS_TAC [])
       ++ `2 <= CARD (space s)` by METIS_TAC [CARD_GT_2]
       ++ `1 < CARD (space s)` by RW_TAC arith_ss [] ++ METIS_TAC [MAX_DECREASE])	
    ++ Q.UNABBREV_TAC `Mjn'` ++ Q.UNABBREV_TAC `cond_pmf_at_j`
    ++ RW_TAC std_ss [Mjn_def, COND_PMF_EQ_COND_PROB]
    ++ `cond_prob p (PREIMAGE (X (SUC k * N + n)) {j} INTER p_space p)
              (PREIMAGE (X 0) {i0} INTER p_space p) IN 
              IMAGE (\i. cond_prob p (PREIMAGE (X (SUC k * N + n)) {j} INTER p_space p)
              (PREIMAGE (X 0) {i} INTER p_space p)) (space s)`
              by (PSET_TAC [] ++ Q.EXISTS_TAC `i0` ++ RW_TAC std_ss [])
    ++ METIS_TAC [max_set_def]) 
 ++ `0 < prob p (PREIMAGE (X 0) {j0} INTER p_space p) /\ 
 	0 < prob p (PREIMAGE (X 0) {i0} INTER p_space p)` 
 	by METIS_TAC [PROB_POSITIVE, REAL_LT_LE]
 ++ NTAC 2 (POP_ASSUM MP_TAC) ++ NTAC 2 (POP_ASSUM K_TAC) ++ RW_TAC std_ss []  
 ++ Know `cond_pmf_at_j (SUC k * N + n) j i0 - cond_pmf_at_j (SUC k * N + n) j j0 <=	
	(SIGMA (\k. cond_pmf_at_j N k i0 - cond_pmf_at_j N k j0) E) * 
	(Mjn' (k * N + n) - mjn' (k * N + n))`
 >> (RW_TAC std_ss []
    ++ Know `cond_pmf_at_j (SUC k * N + n) j i0 - cond_pmf_at_j (SUC k * N + n) j j0 =
             SIGMA (\r. cond_pmf_at_j (k * N + n) j r * cond_pmf_at_j N r i0 -
                        cond_pmf_at_j (k * N + n) j r * cond_pmf_at_j N r j0) (space s)`
    >> (Q.UNABBREV_TAC `cond_pmf_at_j` ++ `0 < n + k * N` by RW_TAC arith_ss []
       ++ `SUC k * N + n = N + (k * N + n)` 
    		by RW_TAC arith_ss [ADD1, RIGHT_ADD_DISTRIB, MULT_CLAUSES] ++ RW_TAC std_ss []
       ++ (MP_TAC o Q.SPECL [`(X:num -> 'a -> 'b)`, `p`, `s`, `N`, `k * N + n`, `i0`, 
    		`j`, `Linit`, `Ltrans`]) THMC_MNGT_CK_EQ 
       ++ RW_TAC std_ss [COND_PMF_EQ_COND_PROB, ADD_COMM] 
       ++ (MP_TAC o Q.SPECL [`(X:num -> 'a -> 'b)`, `p`, `s`, `N`, `k * N + n`, `j0`, 
    		`j`, `Linit`, `Ltrans`]) THMC_MNGT_CK_EQ 
       ++ RW_TAC std_ss [COND_PMF_EQ_COND_PROB, ADD_COMM, GSYM REAL_SUM_IMAGE_SUB, 
    	GSYM REAL_SUB_LDISTRIB]) ++ RW_TAC std_ss [GSYM REAL_SUB_LDISTRIB] ++ POP_ASSUM K_TAC
     ++ (MP_TAC o Q.SPECL [`(space s)`, `E`]) REAL_SUM_IMAGE_DIFF 
     ++ RW_TAC std_ss [REAL_SUB_LDISTRIB, real_sub, GSYM REAL_MUL_LNEG] ++ POP_ASSUM K_TAC 
     ++ Know `-SIGMA (\r. cond_pmf_at_j N r i0 - cond_pmf_at_j N r j0) E =
    	     SIGMA (\r. cond_pmf_at_j N r i0 - cond_pmf_at_j N r j0) 
    	     (space s DIFF E)`
     >> (Q.UNABBREV_TAC `E` 
        ++ (MP_TAC o Q.SPECL [`(X:num -> 'a -> 'b)`, `p`, `s`, `Linit`, `Ltrans`, `N`, 
    	`i0`, `j0`]) SUBSET_SPACES_SIGMA_NEG_EQ_R 
        ++ RW_TAC std_ss [IRREDUCIABLE_MC_def, COND_PMF_EQ_COND_PROB, GSYM real_sub, REAL_NEG_EQ]
        ++ Q.UNABBREV_TAC `cond_pmf_at_j` ++ METIS_TAC []) ++ RW_TAC std_ss []
    ++ MATCH_MP_TAC REAL_LE_ADD2 
    ++ RW_TAC std_ss [REAL_MUL_COMM, REAL_MUL_LNEG, GSYM real_sub, GSYM REAL_SUB_RDISTRIB, 
    		GSYM  REAL_SUM_IMAGE_CMUL] 
    >> ((MP_TAC o Q.ISPEC `(E:'b -> bool)`) REAL_SUM_IMAGE_MONO 
       ++ RW_TAC std_ss [] ++ POP_ASSUM MATCH_MP_TAC ++ RW_TAC std_ss []
       ++ `0 <= cond_pmf_at_j N x i0 - cond_pmf_at_j N x j0`
       		by (Q.UNABBREV_TAC `E` ++ Q.UNABBREV_TAC `cond_pmf_at_j` 
       		   ++ PSET_TAC [REAL_SUB_LE, COND_PMF_EQ_COND_PROB])
       ++ MATCH_MP_TAC REAL_LE_RMUL_IMP ++ RW_TAC std_ss [] ++ Q.UNABBREV_TAC `Mjn'` 
       ++ Q.UNABBREV_TAC `cond_pmf_at_j`
       ++ PSET_TAC [IN_DEF, GSYM real_sub, REAL_SUB_LE, Mjn_def]
       ++ `cond_prob p (PREIMAGE (X (k * N + n)) {j} INTER p_space p)
      			(PREIMAGE (X 0) {x} INTER p_space p) IN
      	      IMAGE (\i. cond_prob p (PREIMAGE (X (k * N + n)) {j} INTER p_space p)
              (PREIMAGE (X 0) {i} INTER p_space p)) (space s)` 
              by (Q.UNABBREV_TAC `E` ++ PSET_TAC [IN_IMAGE] 
                 ++ Q.EXISTS_TAC `x` ++ RW_TAC std_ss [IN_DEF])                 
       ++ METIS_TAC [max_set_def]) 
    ++ RW_TAC std_ss [REAL_SUM_IMAGE_CMUL, REAL_NEG_RMUL]
    ++ RW_TAC std_ss [GSYM REAL_SUM_IMAGE_CMUL, FINITE_DIFF]	
    ++ (MP_TAC o Q.ISPEC `space s DIFF (E:'b -> bool)`) REAL_SUM_IMAGE_MONO 
    ++ RW_TAC std_ss [FINITE_DIFF] ++ POP_ASSUM MATCH_MP_TAC ++ RW_TAC std_ss []
    ++ `cond_pmf_at_j N x i0 - cond_pmf_at_j N x j0 = 
    	-(cond_pmf_at_j N x j0 - cond_pmf_at_j N x i0)` by METIS_TAC [REAL_NEG_SUB] ++ POP_ORW 
    ++ RW_TAC std_ss [REAL_MUL_RNEG, REAL_LE_NEG]
    ++ `0 <= cond_pmf_at_j N x j0 - cond_pmf_at_j N x i0`
     	by (Q.UNABBREV_TAC `E` ++ Q.UNABBREV_TAC `cond_pmf_at_j` 
     	   ++ PSET_TAC [COND_PMF_EQ_COND_PROB, REAL_NOT_LE, REAL_SUB_LE] 
           ++ METIS_TAC [REAL_LT_IMP_LE])
    ++ MATCH_MP_TAC REAL_LE_RMUL_IMP ++ RW_TAC std_ss [] ++ Q.UNABBREV_TAC `cond_pmf_at_j`
    ++ Q.UNABBREV_TAC `mjn'` ++ RW_TAC std_ss [mjn_def]
    ++ `cond_prob p (PREIMAGE (X (k * N + n)) {j} INTER p_space p)
      			(PREIMAGE (X 0) {x} INTER p_space p) IN
      	      IMAGE (\i. cond_prob p (PREIMAGE (X (k * N + n)) {j} INTER p_space p)
              (PREIMAGE (X 0) {i} INTER p_space p)) (space s)` 
              by (PSET_TAC [IN_IMAGE] ++ Q.EXISTS_TAC `x` ++ RW_TAC std_ss [IN_DEF])
    ++ METIS_TAC [min_set_def]) ++ RW_TAC std_ss []
 ++ Suff `SIGMA (\k. cond_pmf_at_j N k i0 - cond_pmf_at_j N k j0) E * 
 	(Mjn' (k * N + n) - mjn' (k * N + n)) <= 
 	(Mjn' n - mjn' n) * (1 - (&CARD E + &CARD (space s DIFF E)) * min_set t) pow SUC k` 
 >> METIS_TAC [REAL_LE_TRANS] ++ POP_ASSUM K_TAC 
 ++ Know `SIGMA (\k. cond_pmf_at_j N k i0 - cond_pmf_at_j N k j0) E <= 
 	1 - (&CARD E + &CARD (space s DIFF E)) * min_set t`
 >> (RW_TAC std_ss [] ++ Q.UNABBREV_TAC `cond_pmf_at_j` 
    ++ Q.UNABBREV_TAC `E` ++ Q.UNABBREV_TAC `t`
    ++ (ASSUME_TAC o BETA_RULE o REWRITE_RULE[LET_DEF] o 
    	Q.SPECL [`X`, `p`, `s`, `Linit`, `Ltrans`,`N`, `N`, `i0`, `j0`]) SUM_LE_MUL_MIN 
    ++ FULL_SIMP_TAC std_ss [IRREDUCIABLE_MC_def, COND_PMF_EQ_COND_PROB]) ++ RW_TAC std_ss []
 ++ `0 <= Mjn' (k * N + n) - mjn' (k * N + n)` 
 	by (Q.UNABBREV_TAC `mjn'` ++ Q.UNABBREV_TAC `Mjn'` ++ Q.UNABBREV_TAC `cond_pmf_at_j` 
 	   ++ RW_TAC std_ss [mjn_def, Mjn_def, REAL_SUB_LE] ++ FULL_SIMP_TAC std_ss []
 	   ++ METIS_TAC [min_set_le_max_set])   
 ++ `SIGMA (\k. cond_pmf_at_j N k i0 - cond_pmf_at_j N k j0) E *
    (Mjn' (k * N + n) - mjn' (k * N + n)) <= 
    (1 - (&CARD E + &CARD (space s DIFF E)) * min_set t) * (Mjn' (k * N + n) - mjn' (k * N + n))`
    by METIS_TAC [REAL_LE_RMUL_IMP]
 ++ Suff `(1 - (&CARD E + &CARD (space s DIFF E)) * min_set t) *
           (Mjn' (k * N + n) - mjn' (k * N + n)) <= (Mjn' n - mjn' n) *
    (1 - (&CARD E + &CARD (space s DIFF E)) * min_set t) pow SUC k` >> METIS_TAC [REAL_LE_TRANS]
 ++ RW_TAC std_ss [pow, REAL_MUL_COMM]    
 ++ `!(x:real) y z. x * (y * z) = x * z * y` by METIS_TAC [REAL_MUL_ASSOC, REAL_MUL_COMM]
 ++ POP_ORW ++ MATCH_MP_TAC REAL_LE_RMUL_IMP ++ RW_TAC std_ss []
 >> (`min_set t * (&CARD E + &CARD (space s DIFF E)) =
     (&CARD E + &CARD (space s DIFF E)) * min_set t` by METIS_TAC [REAL_MUL_COMM] ++ POP_ORW 
    ++ Suff `0 <= SIGMA (\k. cond_pmf_at_j N k i0 - cond_pmf_at_j N k j0) E` 
    >> METIS_TAC [REAL_LE_TRANS, REAL_MUL_COMM] 
    ++ Q.UNABBREV_TAC `cond_pmf_at_j` ++ Q.UNABBREV_TAC `E` 
    ++ RW_TAC std_ss [GSYM COND_PMF_EQ_COND_PROB] ++ MATCH_MP_TAC POSITIVE_SUME
    ++ RW_TAC std_ss []) 
 ++ Q.UNABBREV_TAC `Mjn'` ++ Q.UNABBREV_TAC `mjn'` ++ NTAC 3 (POP_ASSUM K_TAC)
 ++ `Mjn X p s j (k * N + n) IN (IMAGE (\r. cond_pmf_at_j (k * N + n) j r) (space s))`
    	by (RW_TAC std_ss [Mjn_def] ++ Q.UNABBREV_TAC `cond_pmf_at_j` ++ METIS_TAC [max_set_def])
 ++ `mjn X p s j (k * N + n) IN (IMAGE (\r. cond_pmf_at_j (k * N + n) j r) (space s))`
    	by (RW_TAC std_ss [mjn_def] ++ Q.UNABBREV_TAC `cond_pmf_at_j` ++ METIS_TAC [min_set_def])
 ++ FULL_SIMP_TAC std_ss [IN_IMAGE]    	
 ++ Know `((&CARD E):real) + &CARD (space s DIFF E) =
          &CARD {m | m IN space s /\ cond_pmf_at_j N m r' <= cond_pmf_at_j N m r} + 
          &CARD (space s DIFF {m | m IN space s /\ cond_pmf_at_j N m r' <= cond_pmf_at_j N m r})`
 >> (RW_TAC std_ss [REAL_ADD] 
    ++ `{m | m IN space s /\ cond_pmf_at_j N m r' <= cond_pmf_at_j N m r} SUBSET space s`
    	by PSET_TAC [] ++ RW_TAC std_ss [CARD_DIFF_SUM]) ++ RW_TAC std_ss [] ++ POP_ASSUM K_TAC
 ++ Q.UNABBREV_TAC `cond_pmf_at_j` ++ Q.UNABBREV_TAC `E` ++ Q.UNABBREV_TAC `t`
 ++ FIRST_ASSUM (MP_TAC o BETA_RULE o REWRITE_RULE[LET_DEF] 
 	o Q.SPECL [`X`, `p`, `s`, `Linit`, `Ltrans`, `j`, `N`, `n`, `r`,`r'`])
 ++ RW_TAC std_ss [IRREDUCIABLE_MC_def, COND_PMF_EQ_COND_PROB, REAL_MUL_COMM] 
 ++ FULL_SIMP_TAC std_ss []);  

val APERIODIC_MC_SUB_MAX_MIN_COND = prove 	
  (``!X p s Linit Ltrans j. 
   APERIODIC_MC X p s Linit Ltrans /\ IRREDUCIABLE_MC X p s Linit Ltrans /\ 
   1 < CARD (space s) ==>
   (\n. Mjn X p s j n - mjn X p s j n) --> 0``,
    RW_TAC std_ss [] 
 ++ `!t. random_variable (X t) p s` 
 	by FULL_SIMP_TAC std_ss [IRREDUCIABLE_MC_def, th_dtmc_def, 
 	dtmc_def, mc_property_def]    
 ++ `prob_space p` by FULL_SIMP_TAC std_ss [IRREDUCIABLE_MC_def,th_dtmc_def, dtmc_def,
 		 mc_property_def, random_variable_def] 	  
 ++ `space s <> {}` by METIS_TAC [RV_NON_EMPTY_SPACE]  		 
 ++ Cases_on `j NOTIN space s`
 >> (RW_TAC std_ss [Mjn_def, mjn_def]   
    ++ `!n. PREIMAGE (X n) {j} INTER p_space p = {}`
    	by (RW_TAC std_ss [] 
    	   ++ MATCH_MP_TAC NOTIN_SPACE_EVENTS 
    	   ++ Q.EXISTS_TAC `s` 
    	   ++ PSET_TAC [dtmc_def, mc_property_def])
    ++ `{(0:real) | i | i IN space s} = {0:real}` 
    	by (PSET_TAC [GSPECIFICATION, EXTENSION]
    	   ++ EQ_TAC >> RW_TAC std_ss [] 
    	   ++ RW_TAC std_ss []
    	   ++ Q.EXISTS_TAC `x`
    	   ++ RW_TAC std_ss [])  	   
    ++ RW_TAC std_ss [cond_prob_def, INTER_EMPTY, PROB_EMPTY, REAL_DIV_LZERO, IMAGE_DEF,
    	EXTENSION, max_set_sing, min_set_sing, REAL_SUB_REFL, SEQ_CONST])
 ++ MATCH_MP_TAC SUB_SEQ_MAX_MIN_CONV
 ++ (MP_TAC o Q.SPECL [`X`, `p`, `s`, `Linit`, `Ltrans`]) APID_MC_POS_COND 
 ++ RW_TAC std_ss []
 ++ `th_dtmc X p s Linit Ltrans` by FULL_SIMP_TAC std_ss [APERIODIC_MC_def]
 ++ `FINITE (space s)` by FULL_SIMP_TAC std_ss [th_dtmc_def]
 ++ `!N. FINITE (IMAGE (\(i,j). cond_pmf p (X N) (X 0) ({j},{i})) ((space s) CROSS (space s)))`
        by (MATCH_MP_TAC IMAGE_FINITE ++ RW_TAC std_ss [FINITE_CROSS])
 ++ `!N. IMAGE (\(i,j). cond_pmf p (X N) (X 0) ({j},{i})) ((space s) CROSS (space s)) <> {}`
        by (SPOSE_NOT_THEN STRIP_ASSUME_TAC 
           ++ `(j, j) IN ((space s) CROSS (space s))` by PSET_TAC [IN_CROSS]
           ++ METIS_TAC [IMAGE_EQ_EMPTY, MEMBER_NOT_EMPTY, COND_PMF_EQ_COND_PROB]) 
 ++ `!N. FINITE (IMAGE (\i. cond_pmf p (X N) (X 0) ({j},{i})) (space s))` 
        by (MATCH_MP_TAC IMAGE_FINITE ++ RW_TAC std_ss [])
 ++ `!N. (IMAGE (\i. cond_pmf p (X N) (X 0) ({j},{i})) (space s)) <> {}`
              by (SPOSE_NOT_THEN STRIP_ASSUME_TAC ++ METIS_TAC [IMAGE_EQ_EMPTY])           
 ++ MAP_EVERY Q.EXISTS_TAC [`Linit`, `Ltrans`, `(\k. k * (N + 1) + (n + 1))`]
 ++ RW_TAC std_ss [] 
 >> (IMP_RES_TAC o Q.SPECL [`X`, `p`, `s`, `Linit`, `Ltrans`, `j'`]) APERIODIC_MC_POS_PROB
 ++ `0 < n + 1` by RW_TAC arith_ss [] ++ Q.ABBREV_TAC `m = n + 1` 
 ++ `0 < N + 1` by RW_TAC arith_ss [] ++ `N <= N + 1` by RW_TAC arith_ss []
 ++ Q.ABBREV_TAC `N' = N + 1` 
 ++ MATCH_MP_TAC MAX_SUB_MIN_TENDS_0
 ++ MAP_EVERY Q.EXISTS_TAC [`Linit`, `Ltrans`] ++ RW_TAC std_ss []
 ++ Q.EXISTS_TAC `1 - &(CARD (space s)) * 
     	min_set (IMAGE (\(i, j). cond_pmf p (X N') (X 0) ({j}, {i})) (space s CROSS space s))`
 ++ RW_TAC std_ss []
 << [`{r | r IN space s /\ 
 	cond_pmf p (X N') (X 0) ({r},{j}) <= cond_pmf p (X N') (X 0) ({r},{j})}
 	SUBSET (space s)` by PSET_TAC []
     ++ `FINITE {r | r IN space s /\ 
     	cond_pmf p (X N') (X 0) ({r},{j}) <= cond_pmf p (X N') (X 0) ({r},{j})}` 
     	by METIS_TAC [SUBSET_FINITE]
     ++ `!i j'. i IN space s /\ j' IN space s ==>
              0 < cond_pmf p (X N) (X 0) ({j'},{i})`
              by (RW_TAC std_ss [] 
                 ++ FIRST_ASSUM (MP_TAC o Q.SPECL [`i`, `j'`])
                 ++ RW_TAC std_ss [] ++ POP_ASSUM (MP_TAC o Q.SPEC `N`)
                 ++ RW_TAC std_ss [])
     ++ (MP_TAC o BETA_RULE o REWRITE_RULE [LET_DEF] o Q.SPECL 
         [`X`, `p`, `s`, `Linit`, `Ltrans`, `N'`, `N`, `j`, `j`]) SUM_LE_MUL_MIN 
     ++ Q.UNABBREV_TAC `N'`
     ++ RW_TAC arith_ss [REAL_ADD, CARD_DIFF_SUM, REAL_SUB_REFL, REAL_SUM_IMAGE_0],
     
     RW_TAC std_ss [REAL_LT_SUB_RADD, REAL_LT_ADDR] ++ MATCH_MP_TAC REAL_LT_MUL
     ++ RW_TAC std_ss [REAL_LT]
     >> (SPOSE_NOT_THEN STRIP_ASSUME_TAC ++ `CARD (space s) = 0` by RW_TAC arith_ss []
        ++ FULL_SIMP_TAC std_ss [CARD_EQ_0])
     ++ `!x. x IN IMAGE (\(i,j). cond_pmf p (X N') (X 0) ({j},{i}))
         (space s CROSS space s) ==> 0 < x`
         by (PSET_TAC [IN_IMAGE, IN_CROSS] ++ `x' = ((FST x'), (SND x'))` by METIS_TAC [PAIR] 
            ++ POP_ORW ++ RW_TAC std_ss [])
     ++ METIS_TAC [min_set_def],  
     
     `Mjn X p s j (k * N' + m) IN (IMAGE (\i. cond_pmf p (X (k * N' + m)) (X 0) ({j},{i}))
          (space s))`
          by FULL_SIMP_TAC std_ss [Mjn_def, COND_PMF_EQ_COND_PROB, max_set_def]
     ++ `mjn X p s j (k * N' + m) IN (IMAGE (\i. cond_pmf p (X (k * N' + m)) (X 0) ({j},{i}))
          (space s))`
          by FULL_SIMP_TAC std_ss [mjn_def, COND_PMF_EQ_COND_PROB, min_set_def]     
     ++ PSET_TAC [IN_IMAGE]
     ++ (IMP_RES_TAC o Q.SPECL [`X`, `p`, `s`, `Linit`, `Ltrans`, `j'`]) APERIODIC_MC_POS_PROB
     ++ `{r | r IN space s /\ cond_pmf p (X N') (X 0) ({r},{i'}) <= 
     		cond_pmf p (X N') (X 0) ({r},{i})} SUBSET (space s)` by PSET_TAC []
     ++ `FINITE {r | r IN space s /\ cond_pmf p (X N') (X 0) ({r},{i'}) <= 
     		cond_pmf p (X N') (X 0) ({r},{i})}` 
     	by METIS_TAC [SUBSET_FINITE]     
     ++ (MP_TAC o BETA_RULE o REWRITE_RULE [LET_DEF] o Q.SPECL 
         [`X`, `p`, `s`, `Linit`, `Ltrans`, `j`, `N'`, `m`, `k`, `i`, `i'`])
          MAX_SUB_MIN_LE_IMP_SUMS
     ++ RW_TAC std_ss [REAL_ADD, CARD_DIFF_SUM]]);

val APERIODIC_MC_CONVERGENT = store_thm 
  ("APERIODIC_MC_CONVERGENT",
  ``!X p s Linit Ltrans i j. 
   APERIODIC_MC X p s Linit Ltrans /\ IRREDUCIABLE_MC X p s Linit Ltrans ==>
   convergent (\n. cond_pmf p (X n) (X 0) ({j}, {i}))``,   
    RW_TAC std_ss [COND_PMF_EQ_COND_PROB]      
 ++ `FINITE (space s)` by FULL_SIMP_TAC std_ss [APERIODIC_MC_def, th_dtmc_def]    
 ++ `!t. random_variable (X t) p s` 
 	by FULL_SIMP_TAC std_ss [APERIODIC_MC_def, th_dtmc_def, dtmc_def, mc_property_def]       
 ++ `space s <> {}` by METIS_TAC [RV_NON_EMPTY_SPACE] 
 ++ `prob_space p` by FULL_SIMP_TAC std_ss [random_variable_def]  
 ++ `0 < CARD (space s)` by (SPOSE_NOT_THEN STRIP_ASSUME_TAC 
 	   ++ `CARD (space s) = 0` by RW_TAC arith_ss [] 
 	   ++ METIS_TAC [CARD_EQ_0]) 	
 ++ Cases_on `i NOTIN space s`
 >> (RW_TAC std_ss [convergent]
    ++ `PREIMAGE (X 0) {i} INTER p_space p = {}`
    	by (MATCH_MP_TAC NOTIN_SPACE_EVENTS 
    	   ++ Q.EXISTS_TAC `s` 
    	   ++ PSET_TAC [APERIODIC_MC_def, th_dtmc_def, dtmc_def, mc_property_def])
    ++ RW_TAC std_ss [cond_prob_def, INTER_EMPTY, PROB_EMPTY, REAL_DIV_LZERO]	
    ++ Q.EXISTS_TAC `(0:real)`
    ++ RW_TAC std_ss [SEQ_CONST])	
 ++ Cases_on `j NOTIN space s`
 >> (RW_TAC std_ss [convergent]
    ++ `!n. PREIMAGE (X n) {j} INTER p_space p = {}`
    	by (RW_TAC std_ss []
    	   ++ MATCH_MP_TAC NOTIN_SPACE_EVENTS 
    	   ++ Q.EXISTS_TAC `s` 
    	   ++ PSET_TAC [APERIODIC_MC_def, th_dtmc_def, dtmc_def, mc_property_def])
    ++ RW_TAC std_ss [cond_prob_def, INTER_EMPTY, PROB_EMPTY, REAL_DIV_LZERO]	
    ++ Q.EXISTS_TAC `(0:real)`
    ++ RW_TAC std_ss [SEQ_CONST]) 
 ++ Cases_on `CARD (space s) = 1`
 >> (RW_TAC std_ss [] 
    ++ `i = j` by (SPOSE_NOT_THEN STRIP_ASSUME_TAC 
       ++ (MP_TAC o Q.ISPECL [`i:'b`, `j:'b`, `(space s):'b -> bool`]) CARD_GT_2
    		 ++ RW_TAC arith_ss []) ++ RW_TAC std_ss []
       ++ `space s = {i}` by (PSET_TAC [SET_EQ_SUBSET]  
    		 ++ SPOSE_NOT_THEN STRIP_ASSUME_TAC
    		 ++ (MP_TAC o Q.ISPECL [`x':'b`, `i:'b`, `(space s):'b -> bool`]) CARD_GT_2
    		 ++ RW_TAC arith_ss []) 
       ++ (MP_TAC o Q.SPECL [`X`, `p`, `s`, `Linit`, `Ltrans`, `i`]) THDTMC_SING_CONVERGENT
       ++ PSET_TAC [APERIODIC_MC_def]) ++ `1 < CARD (space s)` by RW_TAC arith_ss []
 ++ RW_TAC std_ss [GSYM SEQ_CAUCHY, cauchy] 
 ++ (MP_TAC o Q.SPECL [`X`, `p`, `s`, `Linit`, `Ltrans`, `j`])  APERIODIC_MC_SUB_MAX_MIN_COND
 ++ RW_TAC std_ss []
 ++ FULL_SIMP_TAC std_ss [SEQ, REAL_SUB_RZERO]
 ++ POP_ASSUM (MP_TAC o Q.SPEC `e`) ++ RW_TAC std_ss []
 ++ Q.EXISTS_TAC `N + 1` ++ RW_TAC std_ss []
 ++ `!N. FINITE (IMAGE (\i. cond_pmf p (X N) (X 0) ({j},{i})) (space s))` 
        by (MATCH_MP_TAC IMAGE_FINITE ++ RW_TAC std_ss [])
 ++ `!N. (IMAGE (\i. cond_pmf p (X N) (X 0) ({j},{i})) (space s)) <> {}`
              by (SPOSE_NOT_THEN STRIP_ASSUME_TAC ++ METIS_TAC [IMAGE_EQ_EMPTY]) 
 ++ `!N. cond_pmf p (X N) (X 0) ({j},{i}) IN 
    		(IMAGE (\i. cond_pmf p (X N) (X 0) ({j},{i})) (space s))`
    	      by (PSET_TAC [COND_PMF_EQ_COND_PROB, IN_IMAGE] 
    	         ++ Q.EXISTS_TAC `i` ++ RW_TAC std_ss [])  
 ++ `!N. abs (Mjn X p s j N - mjn X p s j N) = Mjn X p s j N - mjn X p s j N` 
 	by (RW_TAC std_ss [] ++ (MP_TAC o Q.SPECL [`X`, `p`, `s`, `Linit`, `Ltrans`, `j`, `N'`])
 		 THDTMC_MAX_MIN_COND_PROB ++ FULL_SIMP_TAC std_ss [APERIODIC_MC_def, ABS_POS_SUB])
 ++ `!n. n >= N + 1 ==> abs (Mjn X p s j n - mjn X p s j n) < e	` by RW_TAC arith_ss []
 ++ Cases_on `n' <= n`
 >> (RW_TAC std_ss []     	      
    ++ Suff `abs (cond_prob p (PREIMAGE (X n) {j} INTER p_space p)
         (PREIMAGE (X 0) {i} INTER p_space p) -
       cond_prob p (PREIMAGE (X n') {j} INTER p_space p)
         (PREIMAGE (X 0) {i} INTER p_space p)) <= abs (Mjn X p s j n' - mjn X p s j n')`
    >> METIS_TAC [REAL_LET_TRANS] ++ `0 < n'` by RW_TAC arith_ss []
    ++ `?q. n = q + n'` by METIS_TAC [LESS_EQ_EXISTS, ADD_COMM]
    ++ `Mjn X p s j n <= Mjn X p s j n'` by METIS_TAC [MAX_DECREASE, APERIODIC_MC_def]
    ++ RW_TAC std_ss [ABS_BOUNDS]
    >> (Cases_on `cond_pmf p (X n') (X 0) ({j},{i}) <= cond_pmf p (X (q + n')) (X 0) ({j},{i})`
       >> (RW_TAC std_ss [] 
          ++ `-(Mjn X p s j n' - mjn X p s j n') <= 0` 
       	      by METIS_TAC [REAL_NEG_LE0, REAL_SUB_LE, THDTMC_MAX_MIN_COND_PROB, APERIODIC_MC_def]
          ++ METIS_TAC [COND_PMF_EQ_COND_PROB, REAL_SUB_LE, REAL_LE_TRANS])
       ++ `cond_pmf p (X (q + n')) (X 0) ({j},{i}) - cond_pmf p (X n') (X 0) ({j},{i}) = 
        	-(cond_pmf p (X n') (X 0) ({j},{i}) - cond_pmf p (X (q + n')) (X 0) ({j},{i}))` 
        	by METIS_TAC [REAL_NEG_SUB] ++ POP_ASSUM MP_TAC 
       ++ RW_TAC std_ss [COND_PMF_EQ_COND_PROB] ++ POP_ASSUM K_TAC 
       ++ RW_TAC std_ss [REAL_LE_NEG, real_sub] ++ MATCH_MP_TAC REAL_LE_ADD2
       ++ RW_TAC std_ss [REAL_LE_NEG, Mjn_def] 
       >> FULL_SIMP_TAC std_ss [COND_PMF_EQ_COND_PROB, max_set_def]
       ++ `mjn X p s j n' <= mjn X p s j (q + n')` 
    		by METIS_TAC [MIN_INCREASE, APERIODIC_MC_def, ADD_COMM]
       ++ `mjn X p s j (q + n') <= cond_prob p (PREIMAGE (X (q + n')) {j} INTER p_space p)
      		(PREIMAGE (X 0) {i} INTER p_space p)` 
      		by FULL_SIMP_TAC std_ss [mjn_def, COND_PMF_EQ_COND_PROB, min_set_def]
       ++ METIS_TAC [REAL_LE_TRANS])
    ++ `mjn X p s j n' <= cond_prob p (PREIMAGE (X n') {j} INTER p_space p)
      (PREIMAGE (X 0) {i} INTER p_space p)` 
      	by FULL_SIMP_TAC std_ss [mjn_def, COND_PMF_EQ_COND_PROB, min_set_def]
    ++ RW_TAC std_ss [real_sub] ++ MATCH_MP_TAC REAL_LE_ADD2 ++ RW_TAC std_ss [REAL_LE_NEG] 
    ++ `cond_prob p (PREIMAGE (X (q + n')) {j} INTER p_space p)
      (PREIMAGE (X 0) {i} INTER p_space p) <= Mjn X p s j (q + n')`
      by FULL_SIMP_TAC std_ss [Mjn_def, COND_PMF_EQ_COND_PROB, max_set_def]
    ++ METIS_TAC [REAL_LE_TRANS]) 
 ++ `n <= n'` by METIS_TAC [NOT_LESS_EQUAL, LESS_IMP_LESS_OR_EQ]
 ++ Suff `abs (cond_prob p (PREIMAGE (X n) {j} INTER p_space p)
         (PREIMAGE (X 0) {i} INTER p_space p) -
       cond_prob p (PREIMAGE (X n') {j} INTER p_space p)
         (PREIMAGE (X 0) {i} INTER p_space p)) <= abs (Mjn X p s j n - mjn X p s j n)`
 >> METIS_TAC [REAL_LET_TRANS] 
 ++ `0 < n` by RW_TAC arith_ss []
 ++ `?q. n' = q + n` by METIS_TAC [LESS_EQ_EXISTS, ADD_COMM]
 ++ `Mjn X p s j n' <= Mjn X p s j n` by METIS_TAC [MAX_DECREASE, APERIODIC_MC_def]
 ++ RW_TAC std_ss [ABS_BOUNDS]
 >> (Cases_on `cond_pmf p (X (q + n)) (X 0) ({j},{i}) <= cond_pmf p (X n) (X 0) ({j},{i})`
    >> (RW_TAC std_ss [] 
       ++ `-(Mjn X p s j n - mjn X p s j n) <= 0` 
       	       by METIS_TAC [REAL_NEG_LE0, REAL_SUB_LE, 
       	       		THDTMC_MAX_MIN_COND_PROB, APERIODIC_MC_def]
       ++ METIS_TAC [COND_PMF_EQ_COND_PROB, REAL_SUB_LE, REAL_LE_TRANS])
    ++ `cond_pmf p (X n) (X 0) ({j},{i}) - cond_pmf p (X (q + n)) (X 0) ({j},{i}) =
          -(cond_pmf p (X (q + n)) (X 0) ({j},{i}) - cond_pmf p (X n) (X 0) ({j},{i}))` 
        by METIS_TAC [REAL_NEG_SUB] 
    ++ POP_ASSUM MP_TAC ++ RW_TAC std_ss [COND_PMF_EQ_COND_PROB]
    ++ POP_ASSUM K_TAC ++ RW_TAC std_ss [REAL_LE_NEG, real_sub] ++ MATCH_MP_TAC REAL_LE_ADD2
    ++ RW_TAC std_ss [REAL_LE_NEG, mjn_def] 
    >> (`cond_prob p (PREIMAGE (X (q + n)) {j} INTER p_space p)
      		(PREIMAGE (X 0) {i} INTER p_space p) <= Mjn X p s j (q + n)`
      		by FULL_SIMP_TAC std_ss [Mjn_def, COND_PMF_EQ_COND_PROB, max_set_def]
       ++ METIS_TAC [REAL_LE_TRANS]) 
    ++ FULL_SIMP_TAC std_ss [COND_PMF_EQ_COND_PROB, min_set_def])
 ++ RW_TAC std_ss [real_sub] ++ MATCH_MP_TAC REAL_LE_ADD2 ++ RW_TAC std_ss [REAL_LE_NEG] 
 ++ FULL_SIMP_TAC std_ss [Mjn_def, COND_PMF_EQ_COND_PROB, max_set_def]
 ++ `mjn X p s j n <= mjn X p s j (q + n)` 
      	by METIS_TAC [MIN_INCREASE, APERIODIC_MC_def, ADD_COMM]
 ++ `mjn X p s j (q + n) <= cond_prob p (PREIMAGE (X (q + n)) {j} INTER p_space p)
      			(PREIMAGE (X 0) {i} INTER p_space p)`
      	by FULL_SIMP_TAC std_ss [mjn_def, COND_PMF_EQ_COND_PROB, min_set_def]
 ++ METIS_TAC [REAL_LE_TRANS]);

(* ------------------------------------------------------------------------- *)
(* Theorem 7: Existence of Long-run Transition Probabilities                 *)
(* ------------------------------------------------------------------------- *) 
val IA_MC_CONVERGENT_TRANS = store_thm 
  ("IA_MC_CONVERGENT_TRANS",
  ``!X p s Linit Ltrans i j t. 
   APERIODIC_MC X p s Linit Ltrans /\ IRREDUCIABLE_MC X p s Linit Ltrans ==>
   convergent (\n. Trans X p s t n i j)``, 
    RW_TAC std_ss [Trans_def]
 >> (Cases_on `i NOTIN space s`
    >> (RW_TAC std_ss [convergent]   
       ++ Q.EXISTS_TAC `0`
       ++ RW_TAC std_ss [SEQ_CONST])
    ++ RW_TAC std_ss [convergent]
    ++ (MP_TAC o Q.SPECL [`X`, `p`, `s`, `Linit`, `Ltrans`, `i`, `i`]) APERIODIC_MC_CONVERGENT
    ++ RW_TAC std_ss [COND_PMF_EQ_COND_PROB, convergent]
    ++ POP_ASSUM MP_TAC
    ++ ONCE_REWRITE_TAC [SEQ_SUC] 
    ++ RW_TAC arith_ss [] 
    ++ Q.EXISTS_TAC `l`
    ++ RW_TAC std_ss []
    ++ Suff `!n. cond_prob p (PREIMAGE (X (t + SUC n)) {i} INTER p_space p)
         (PREIMAGE (X t) {i} INTER p_space p) = 
         cond_prob p (PREIMAGE (X (SUC n)) {i} INTER p_space p)
               (PREIMAGE (X 0) {i} INTER p_space p)`
    >> RW_TAC std_ss []
    ++ RW_TAC std_ss []
    ++ (MP_TAC o Q.SPECL [`X`, `p`, `s`, `t`, `SUC n`, `0`, `i`, `i`, `Linit`, `Ltrans`])
    	 THMC_TRANS_N ++ PSET_TAC [APERIODIC_MC_def, Trans_def])
 ++ Cases_on `i NOTIN space s`
 >> (RW_TAC std_ss [convergent]   
    ++ Q.EXISTS_TAC `0`
    ++ RW_TAC std_ss [SEQ_CONST])
 ++ Cases_on `j NOTIN space s`
 >> (RW_TAC std_ss [convergent]   
    ++ Q.EXISTS_TAC `0`
    ++ RW_TAC std_ss [SEQ_CONST])
 ++ RW_TAC std_ss [convergent]
 ++ (MP_TAC o Q.SPECL [`X`, `p`, `s`, `Linit`, `Ltrans`, `i`, `j`]) APERIODIC_MC_CONVERGENT
 ++ RW_TAC std_ss [COND_PMF_EQ_COND_PROB, convergent]
 ++ POP_ASSUM MP_TAC
 ++ ONCE_REWRITE_TAC [SEQ_SUC] 
 ++ RW_TAC arith_ss [] 
 ++ Q.EXISTS_TAC `l`
 ++ RW_TAC std_ss []
 ++ Suff `!n. cond_prob p (PREIMAGE (X (t + SUC n)) {j} INTER p_space p)
         (PREIMAGE (X t) {i} INTER p_space p) = 
         cond_prob p (PREIMAGE (X (SUC n)) {j} INTER p_space p)
               (PREIMAGE (X 0) {i} INTER p_space p)`
 >> RW_TAC std_ss []
 ++ RW_TAC std_ss []
 ++ (MP_TAC o Q.SPECL [`X`, `p`, `s`, `t`, `SUC n`, `0`, `i`, `j`, `Linit`, `Ltrans`])
    	 THMC_TRANS_N ++ PSET_TAC [APERIODIC_MC_def, Trans_def]);

(* ------------------------------------------------------------------------- *)
(* Theorem 8: Existence of Long-run Probabilities Distributions              *)
(* ------------------------------------------------------------------------- *)       
val APERIODIC_MC_SEQ = store_thm
  ("APERIODIC_MC_SEQ",
  ``!X p s Linit Ltrans i. 
   APERIODIC_MC X p s Linit Ltrans /\ IRREDUCIABLE_MC X p s Linit Ltrans ==>
        ?(u:real). (\n. prob p (PREIMAGE (X n) {i} INTER p_space p)) --> u``,
    RW_TAC std_ss []
 ++ Cases_on `i NOTIN space s`
 >> (RW_TAC std_ss [convergent]
    ++ `!n. PREIMAGE (X n) {i} INTER p_space p = {}`
    	by (RW_TAC std_ss []
    	   ++ MATCH_MP_TAC NOTIN_SPACE_EVENTS 
    	   ++ Q.EXISTS_TAC `s` 
    	   ++ PSET_TAC [APERIODIC_MC_def, th_dtmc_def, dtmc_def, mc_property_def])
    ++ `prob_space p` by FULL_SIMP_TAC std_ss [IRREDUCIABLE_MC_def,th_dtmc_def, dtmc_def,
 		 mc_property_def, random_variable_def]   	   
    ++ RW_TAC std_ss [PROB_EMPTY, REAL_DIV_LZERO]	
    ++ Q.EXISTS_TAC `(0:real)`
    ++ RW_TAC std_ss [SEQ_CONST])
 ++ ONCE_ASM_REWRITE_TAC [SEQ_SUC] 
 ++ RW_TAC std_ss [ADD1, GSYM convergent]  
 ++ `!n. distribution p (X (n + 1)) {i} =
         SIGMA (\k. distribution p (X 0) {k} * 
         	cond_pmf p (X (n + 1)) (X 0) ({i},{k})) (space s)`
    by (RW_TAC std_ss []
       ++ (MP_TAC o Q.SPECL [`X`, `n + 1`, `0`, `i`, `Linit`, `Ltrans`, `p`, `s`])
       		 N_STEP_PROB_DISTRIBUTION 
       ++ FULL_SIMP_TAC std_ss [APERIODIC_MC_def, th_dtmc_def])
 ++ POP_ASSUM MP_TAC ++ RW_TAC std_ss [distribution_def, COND_PMF_EQ_COND_PROB]
 ++ POP_ASSUM K_TAC 
 ++ `FINITE (space s)` by FULL_SIMP_TAC std_ss [APERIODIC_MC_def, th_dtmc_def]
 ++ `!n. (\k. prob p (PREIMAGE (X 0) {k} INTER p_space p) *
              cond_prob p (PREIMAGE (X (n + 1)) {i} INTER p_space p)
                (PREIMAGE (X 0) {k} INTER p_space p)) =
      (\k. (\n k. prob p (PREIMAGE (X 0) {k} INTER p_space p) *
              cond_prob p (PREIMAGE (X (n + 1)) {i} INTER p_space p)
                (PREIMAGE (X 0) {k} INTER p_space p)) n k)` by RW_TAC std_ss [] 
 ++ POP_ORW         
 ++ MATCH_MP_TAC SIGMA_SEQ ++ RW_TAC std_ss []
 ++ `convergent (\n. cond_prob p (PREIMAGE (X (n + 1)) {i} INTER p_space p)
               (PREIMAGE (X 0) {k} INTER p_space p))` 
       by ((MP_TAC o Q.SPECL [`X`, `p`, `s`, `Linit`, `Ltrans`, `k`, `i`]) APERIODIC_MC_CONVERGENT
          ++ RW_TAC std_ss [convergent, COND_PMF_EQ_COND_PROB] 
          ++ Q.EXISTS_TAC `l` ++ RW_TAC std_ss [GSYM ADD1, GSYM SEQ_SUC])
 ++ FULL_SIMP_TAC std_ss [convergent] 
 ++ Q.EXISTS_TAC `prob p (PREIMAGE (X 0) {k} INTER p_space p) * l`
 ++ `(\n. prob p (PREIMAGE (X 0) {k} INTER p_space p) *
     cond_prob p (PREIMAGE (X (n + 1)) {i} INTER p_space p) 
     	(PREIMAGE (X 0) {k} INTER p_space p)) =
     (\n. (\n. prob p (PREIMAGE (X 0) {k} INTER p_space p)) n * 
          (\n. cond_prob p (PREIMAGE (X (n + 1)) {i} INTER p_space p) 
          	(PREIMAGE (X 0) {k} INTER p_space p)) n)` by RW_TAC std_ss [] 
 ++ POP_ORW  
 ++ MATCH_MP_TAC SEQ_MUL ++ RW_TAC std_ss [SEQ_CONST]);

(* ------------------------------------------------------------------------- *)
(* Theorem 9: Existence of Steady State Probability                          *)
(* ------------------------------------------------------------------------- *)
val STEADY_PROB = store_thm
  ("STEADY_PROB",
  ``!X p s Linit Ltrans. 
   APERIODIC_MC X p s Linit Ltrans /\ IRREDUCIABLE_MC X p s Linit Ltrans ==>
   stationary_distribution p X (\i. lim (\n. prob p (PREIMAGE (X n) {i} INTER p_space p))) s``,
    RW_TAC std_ss [stationary_distribution_def, Trans_def]   
 << [DEP_REWRITE_TAC [GSYM SIGMA_LIM]
     ++ `FINITE (space s)` by FULL_SIMP_TAC std_ss [IRREDUCIABLE_MC_def, th_dtmc_def]
     ++ RW_TAC std_ss [] 
     >> METIS_TAC [APERIODIC_MC_SEQ]
     ++ FULL_SIMP_TAC std_ss [APERIODIC_MC_def, th_dtmc_def, dtmc_def, mc_property_def]
     ++ `!n. SIGMA (\k. prob p (PREIMAGE (X n) {k} INTER p_space p)) (space s) = 1`
     		by (RW_TAC std_ss [] ++ (MP_TAC o Q.SPECL [`X`, `p`, `s`, `n`]) SUM_PMF_ONE
     		   ++ RW_TAC std_ss [distribution_def]) ++ RW_TAC std_ss [LIM_CONST],
     
     (IMP_RES_TAC o Q.SPECL [`X`, `p`, `s`, `Linit`, `Ltrans`, `i`]) APERIODIC_MC_SEQ
     ++ MATCH_MP_TAC LE_SEQ_IMP_LE_LIM
     ++ Q.EXISTS_TAC `(\n. prob p (PREIMAGE (X n) {i} INTER p_space p))` 
     ++ `convergent (\n. prob p (PREIMAGE (X n) {i} INTER p_space p))` by METIS_TAC [convergent]
     ++ PSET_TAC [SEQ_LIM] 
     ++ `prob_space p` by FULL_SIMP_TAC std_ss [APERIODIC_MC_def, th_dtmc_def, dtmc_def,
 	 mc_property_def, random_variable_def]
     ++ `!j n. PREIMAGE (X n) {j} INTER p_space p IN events p`
 	by METIS_TAC [APERIODIC_MC_def, th_dtmc_def, DTMC_EVENTS]  
     ++ METIS_TAC [PROB_POSITIVE],
     	   
     `FINITE (space s)` by FULL_SIMP_TAC std_ss [IRREDUCIABLE_MC_def, th_dtmc_def]
     ++ `SIGMA (\k. lim (\n. prob p (PREIMAGE (X n) {k} INTER p_space p)) *
         if k IN space s then
           cond_prob p (PREIMAGE (X (t + 1)) {i} INTER p_space p)
             (PREIMAGE (X t) {k} INTER p_space p) else 0) (space s) =
         SIGMA (\k. lim (\n. prob p (PREIMAGE (X n) {k} INTER p_space p)) *
         cond_prob p (PREIMAGE (X (t + 1)) {i} INTER p_space p)
           (PREIMAGE (X t) {k} INTER p_space p)) (space s)`
           by (MATCH_MP_TAC REAL_SUM_IMAGE_EQ ++ RW_TAC std_ss []) ++ POP_ORW
     ++ `SIGMA (\k. lim (\n. prob p (PREIMAGE (X n) {k} INTER p_space p)) *
         cond_prob p (PREIMAGE (X (t + 1)) {i} INTER p_space p)
           (PREIMAGE (X t) {k} INTER p_space p)) (space s) =
      SIGMA (\k. lim (\n. prob p (PREIMAGE (X n) {k} INTER p_space p) *
         cond_prob p (PREIMAGE (X (t + 1)) {i} INTER p_space p)
         	(PREIMAGE (X t) {k} INTER p_space p))) (space s)`
         by (MATCH_MP_TAC REAL_SUM_IMAGE_EQ ++ RW_TAC std_ss [] 
            ++ `convergent (\n. prob p (PREIMAGE (X n) {x} INTER p_space p))` 
            	by METIS_TAC [convergent, APERIODIC_MC_SEQ]
            ++ FULL_SIMP_TAC std_ss [SEQ_LIM] 
            ++ `lim (\n. prob p (PREIMAGE (X n) {x} INTER p_space p) *
		         cond_prob p (PREIMAGE (X (t + 1)) {i} INTER p_space p)
		           (PREIMAGE (X t) {x} INTER p_space p)) =
		lim (\n. (\n. prob p (PREIMAGE (X n) {x} INTER p_space p)) n *
		         cond_prob p (PREIMAGE (X (t + 1)) {i} INTER p_space p)
		           (PREIMAGE (X t) {x} INTER p_space p))` by RW_TAC std_ss []
            ++ POP_ORW ++ MATCH_MP_TAC (GSYM LIM_MUL_CONST) ++ RW_TAC std_ss [])
     ++ POP_ORW ++ DEP_REWRITE_TAC [GSYM SIGMA_LIM] ++ RW_TAC std_ss []      
     >> (`?u. (\n. prob p (PREIMAGE (X n) {k} INTER p_space p)) --> u` 
            	by METIS_TAC [APERIODIC_MC_SEQ] 
        ++ Q.EXISTS_TAC `u * cond_prob p (PREIMAGE (X (t + 1)) {i} INTER p_space p)
           		(PREIMAGE ((X:num -> 'a -> 'b) t) {k} INTER p_space p)`
        ++ `(\n. prob p (PREIMAGE (X n) {k} INTER p_space p) *
       	      cond_prob p (PREIMAGE (X (t + 1)) {i} INTER p_space p)
         	(PREIMAGE (X t) {k} INTER p_space p)) =          
         (\n. (\n. prob p (PREIMAGE (X n) {k} INTER p_space p)) n *
       	      (\n. cond_prob p (PREIMAGE (X (t + 1)) {i} INTER p_space p)
         	(PREIMAGE (X t) {k} INTER p_space p)) n)` by RW_TAC std_ss [] ++ POP_ORW
        ++ MATCH_MP_TAC SEQ_MUL ++ RW_TAC std_ss [SEQ_CONST])
     ++ Suff `!n. (SIGMA (\k. prob p (PREIMAGE (X n) {k} INTER p_space p) *
              cond_prob p (PREIMAGE (X (t + 1)) {i} INTER p_space p)
                (PREIMAGE (X t) {k} INTER p_space p)) (space s) = 
                prob p (PREIMAGE (X (n + 1)) {i} INTER p_space p))`
     >> (RW_TAC std_ss []
        ++ `lim (\n. prob p (PREIMAGE (X n) {i} INTER p_space p)) =
            lim (\n. (\n. prob p (PREIMAGE (X n) {i} INTER p_space p)) n)`
            by RW_TAC std_ss [] ++ POP_ORW
        ++ `lim (\n. prob p (PREIMAGE (X (n + 1)) {i} INTER p_space p)) =
            lim (\n. (\n. prob p (PREIMAGE (X n) {i} INTER p_space p)) (SUC n))`
            by RW_TAC std_ss [ADD1] ++ POP_ORW ++ RW_TAC std_ss [LIM_FN_EQ_LIM_FSUCN])
     ++ RW_TAC std_ss []
     ++ `SIGMA (\k. prob p (PREIMAGE (X n) {k} INTER p_space p) *
         cond_prob p (PREIMAGE (X (t + 1)) {i} INTER p_space p)
           (PREIMAGE (X t) {k} INTER p_space p)) (space s) =
         SIGMA (\k. prob p (PREIMAGE (X n) {k} INTER p_space p) *
         cond_prob p (PREIMAGE (X (n + 1)) {i} INTER p_space p)
           (PREIMAGE (X n) {k} INTER p_space p)) (space s)`
           by (MATCH_MP_TAC REAL_SUM_IMAGE_EQ ++ RW_TAC std_ss []
              ++ (MP_TAC o Q.SPECL [`X`, `p`, `s`, `Linit`, `Ltrans`]) HOMO_LEMMA
              ++ PSET_TAC [APERIODIC_MC_def]
              ++ METIS_TAC [])
     ++ POP_ORW
     ++ ASSUME_TAC (REWRITE_RULE [distribution_def, COND_PMF_EQ_COND_PROB] 
     	(GSYM N_STEP_PROB_DISTRIBUTION)) ++ FULL_SIMP_TAC std_ss [APERIODIC_MC_def, th_dtmc_def]
     ++ POP_ASSUM (MP_TAC o Q.SPECL [`X`, `1`, `n`, `i`, `Linit`, `Ltrans`, `p`, `s`])
     ++ RW_TAC std_ss []]);  
     
val STATIONARY_DISTRIBUTION_EXISTENCE = store_thm
  ("STATIONARY_DISTRIBUTION_EXISTENCE",
  ``!X p s Linit Ltrans. 
   APERIODIC_MC X p s Linit Ltrans /\ IRREDUCIABLE_MC X p s Linit Ltrans ==>
        ?f. stationary_distribution p X f s``,
    RW_TAC std_ss [] 
 ++ Q.EXISTS_TAC `(\i. lim (\n. prob p (PREIMAGE (X n) {i} INTER p_space p)))`
 ++ METIS_TAC [STEADY_PROB]);
     
val _ = export_theory();  
