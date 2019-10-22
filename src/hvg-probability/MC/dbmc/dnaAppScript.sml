(* ========================================================================= *)
(*                                                                           *)
(*                    A Formal DNA Sequence Analysis                         *)
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
(*val () = app load
 ["bossLib", "metisLib", "arithmeticTheory", "pred_setTheory", "realLib", "seqTheory",
 	"pairTheory", "combinTheory", "listTheory", "rich_listTheory", "transcTheory", "numLib", 
 	"prim_recTheory", "probabilityTheory", "hmmTheory", 
 	"cond_probTheory","dep_rewrite", "extra_pred_setTools",
 	"dtmcBasicTheory", "setUsefulTheory"];

set_trace "Unicode" 0;*)

open HolKernel Parse boolLib bossLib metisLib numLib combinTheory subtypeTheory
	pred_setTheory measureTheory listTheory rich_listTheory numLib seqTheory dep_rewrite
     extra_pred_setTheory arithmeticTheory realTheory realLib pairTheory extra_pred_setTools
      transcTheory prim_recTheory extrealTheory probabilityTheory hmmTheory cond_probTheory 
      dtmcBasicTheory setUsefulTheory;

val _ = new_theory "dnaApp";

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

(*========  Define the type of DNA and its states   =========*)

val _ = Hol_datatype `dna = A | G | T | C`;
val _ = Hol_datatype `state = START | E | I | FIVE | END`;

(*========   state initial distribution function    =========*)
val ini_distribution_def = Define `
    ini_distribution (i:state) = if (i = START) then (1:real) else 0`;

(*========  state transition probability function   =========*)     
val trans_distribution_def = Define `
    trans_distribution (t:num) (i:state) (j:state) = 
        if (i = START) /\ (j = E) then 1 else
    	if (i = E) /\ (j = E) then 0.9 else 
    	if (i = E) /\ (j = FIVE) then 0.1 else 
    	if (i = FIVE) /\ (j = I) then 1 else
    	if (i = I) /\ (j = I) then 0.9 else 
    	if (i = I) /\ (j = END) then 0.1 else (0:real)`;   

(*====  emission probability function for observation sequence  ====*)
val emission_distribution_def = Define `
    emission_distribution (t:num) (a:dna) (i:state) = 
    	if (i = E) then 0.25 else
        if (i = FIVE) then
             if (a = A) then 0.05 else
             if (a = G) then 0.95 else (0:real) else
        if (i = I) then 
             if (a = A) \/ (a = T) then 0.4 else 0.1 else 0`; 
                                   
(*======== dna sequence to be analyzed in this application  =========*)
val dna_seq_def = Define `
    (dna_seq:dna list) = 
    [C;T;T;C;A;T;G;T;G;A;A;A;G;C;A;G;A;C;G;T;A;A;G;T;C;A]`;

val state_path_def = Define `
    (state_path:state list) = 
    [E;E;E;E;E;E;E;E;E;E;E;E;E;E;E;E;E;E;FIVE;I;I;I;I;I;I;I]`;     

val states_def = Define `
    (states:state list) = [START;E;E;E;E;E;E;E;E;E;E;E;E;E;E;E;E;E;E;FIVE;I;I;I;I;I;I;I;END]`;
(* ------------------------------------------------------------------------- *)
(*========              definition of 5' splice dna model           =========*)   
(* ------------------------------------------------------------------------- *)  
val dna_model_def = Define `
    dna_model X Y p s s1 =
    thmm (X:num -> 'a -> state) (Y:num -> 'a -> dna) p s s1 
    	ini_distribution trans_distribution emission_distribution /\ 
    (space s = univ(:state)) /\ (space s1 = univ(:dna))`; 
          
(*========  some subgoals for prove the property of this DNA model  =========*)
val REAL_SUM_IMAGE_EXISTS_POS = prove
  (``!f s. FINITE s /\ (!x. x IN s ==> 0 <= f x) /\ (?x. x IN s /\ 0 < f x) ==>
	(0:real) < SIGMA f s``,
    RW_TAC std_ss []	
 ++ `s = {x} UNION (s DIFF {x})` by PSET_TAC [UNION_DIFF]
 ++ Cases_on `s DIFF {x} = {}`
 >> (RW_TAC std_ss []	
    ++ `s = {x}` by METIS_TAC [UNION_EMPTY]
    ++ RW_TAC std_ss [REAL_SUM_IMAGE_SING])
 ++ ONCE_ASM_REWRITE_TAC []
 ++ MP_REWRITE_TAC REAL_SUM_IMAGE_DISJOINT_UNION
 ++ PSET_TAC [FINITE_SING, FINITE_DIFF, DISJOINT_DIFF, REAL_SUM_IMAGE_SING]
 ++ MATCH_MP_TAC REAL_LTE_ADD 
 ++ RW_TAC std_ss []
 ++ MATCH_MP_TAC REAL_SUM_IMAGE_POS 
 ++ PSET_TAC [FINITE_DIFF, IN_DIFF]);

val POS_DISTRIBUTION_E = prove
  (``!X Y p s s1. dna_model X Y p s s1 ==>
   0 < distribution p (X 1) {E}``,
    RW_TAC std_ss [dna_model_def, thmm_def, hmm_def]
 ++ `prob_space p` by PSET_TAC [hmm_def, random_variable_def]
 ++ `!n x. x IN univ(:state) ==> 0 <= distribution p (X n) {x}` 
 	by (RW_TAC std_ss [distribution_def] 
 	++ MATCH_MP_TAC PROB_POSITIVE 
 	++ PROVE_TAC [DTMC_EVENTS])    
 ++ (MP_TAC o Q.ISPECL [`X:num -> 'a -> state`, `1:num`, `0:num`, `E:state`, 
    	`ini_distribution: state -> real`, `trans_distribution:num -> state -> state -> real`,  
    	`p:('a -> bool) # (('a -> bool) -> bool) # (('a -> bool) -> real)`, 
    	`s:(state -> bool) # ((state -> bool) -> bool)`])
    	N_STEP_PROB_DISTRIBUTION ++ PSET_TAC []
 ++ MATCH_MP_TAC REAL_SUM_IMAGE_EXISTS_POS 	
 ++ PSET_TAC []
 << [METIS_TAC [],
     MATCH_MP_TAC REAL_LE_MUL
     ++ RW_TAC std_ss [COND_PMF_EQ_COND_PROB]
     ++ `E IN univ(:state)` by PSET_TAC []
     ++ MATCH_MP_TAC (MATCH_MP (METIS_PROVE [] ``(a ==> b /\ c) ==> (a ==> b)``) 
        	(SPEC_ALL COND_PROB_BOUNDS)) 
     ++ RW_TAC std_ss []
     >> PROVE_TAC [DTMC_EVENTS]
     ++ Cases_on `x NOTIN (space s)`
     >> (`PREIMAGE (X 0) {x} INTER p_space p = {}` 
        	by (MATCH_MP_TAC NOTIN_SPACE_EVENTS ++ Q.EXISTS_TAC `s` 
       		   ++ PSET_TAC [hmm_def, dtmc_def, mc_property_def])
        ++ METIS_TAC [EVENTS_EMPTY])
     ++ PROVE_TAC [DTMC_EVENTS],
     Q.EXISTS_TAC `START` ++ PSET_TAC [dtmc_def]
     ++ `START IN univ(:state)` by PSET_TAC [] 
     ++ `distribution p (X 0) {START} = ini_distribution START` by METIS_TAC []
     ++ FULL_SIMP_TAC std_ss [ini_distribution_def, REAL_MUL_LID]
     ++ `Trans X p s 0 1 START E = trans_distribution 0 START E` 
     	by (FIRST_ASSUM (MP_TAC o GSYM o Q.SPECL [`START`, `E`, `0`])
     		++ PSET_TAC [] ++ METIS_TAC [REAL_LT_01, REAL_LT_IMP_NE])
     ++ PSET_TAC [trans_distribution_def, Trans_def, COND_PMF_EQ_COND_PROB]
     ++ METIS_TAC [REAL_LT_01, REAL_LT_IMP_NE]]);

val POS_DISTR_E = prove
  (``!X Y p s s1 n. dna_model X Y p s s1 /\ 0 < n ==>
   0 < distribution p (X n) {E}``,
    Induct_on `n` >> RW_TAC std_ss []
 ++ RW_TAC std_ss []
 ++ Cases_on `n = 0`
 >> (RW_TAC arith_ss [] ++ METIS_TAC [POS_DISTRIBUTION_E])
 ++ `0 < n` by RW_TAC arith_ss []
 ++ `0 < distribution p (X n) {E}` by METIS_TAC []
 ++ `prob_space p` by PSET_TAC [dna_model_def, thmm_def, hmm_def, random_variable_def] 
 ++ `!n x. x IN univ(:state) ==> 0 <= distribution p (X n) {x}` 
 	by (RW_TAC std_ss [distribution_def] 
 	++ MATCH_MP_TAC PROB_POSITIVE 
 	++ PROVE_TAC [dna_model_def, thmm_def, hmm_def,DTMC_EVENTS])    
 ++ POP_ASSUM_LIST (MAP_EVERY STRIP_ASSUME_TAC)
 ++ POP_ASSUM K_TAC  	
 ++ (MP_TAC o Q.ISPECL [`X:num -> 'a -> state`, `1:num`, `n:num`, `E:state`, 
    	`ini_distribution: state -> real`, `trans_distribution:num -> state -> state -> real`,  
    	`p:('a -> bool) # (('a -> bool) -> bool) # (('a -> bool) -> real)`, 
    	`s:(state -> bool) # ((state -> bool) -> bool)`])
    	N_STEP_PROB_DISTRIBUTION ++ PSET_TAC [ADD1, dna_model_def, thmm_def, hmm_def]
 ++ MATCH_MP_TAC REAL_SUM_IMAGE_EXISTS_POS 
 ++ PSET_TAC []
 << [METIS_TAC [],
     MATCH_MP_TAC REAL_LE_MUL
     ++ RW_TAC std_ss [COND_PMF_EQ_COND_PROB]
     ++ `E IN univ(:state)` by PSET_TAC []
     ++ MATCH_MP_TAC (MATCH_MP (METIS_PROVE [] ``(a ==> b /\ c) ==> (a ==> b)``) 
        	(SPEC_ALL COND_PROB_BOUNDS)) 
     ++ RW_TAC std_ss []
     >> PROVE_TAC [DTMC_EVENTS]
     ++ Cases_on `x NOTIN (space s)`
     >> (`PREIMAGE (X n) {x} INTER p_space p = {}` 
        	by (MATCH_MP_TAC NOTIN_SPACE_EVENTS ++ Q.EXISTS_TAC `s` 
       		   ++ PSET_TAC [hmm_def, dtmc_def, mc_property_def])
        ++ METIS_TAC [EVENTS_EMPTY])
     ++ PROVE_TAC [DTMC_EVENTS],

     Q.EXISTS_TAC `E` ++ PSET_TAC [dtmc_def]
     ++ `E IN univ(:state)` by PSET_TAC [] 
     ++ MATCH_MP_TAC REAL_LT_MUL
     ++ RW_TAC std_ss []
     ++ `distribution p (X n) {E} <> 0` by METIS_TAC [REAL_POS_NZ]
     ++ FULL_SIMP_TAC std_ss [ini_distribution_def, REAL_MUL_LID]
     ++ `Trans X p s n 1 E E = trans_distribution n E E` 
     	by (FIRST_ASSUM (MP_TAC o GSYM o Q.SPECL [`E`, `E`, `n`]) ++ PSET_TAC [])
     ++ PSET_TAC [trans_distribution_def, Trans_def, COND_PMF_EQ_COND_PROB]
     ++ RW_TAC real_ss []]);
     
val START_DISTR = prove
  (``!X Y p s s1. dna_model X Y p s s1 ==>
	(distribution p (X 0) {START} = 1)``,
    RW_TAC std_ss []
 ++ `START IN space s` by PSET_TAC [dna_model_def]
 ++ `!i. i IN space s ==>
      (ini_distribution i = prob p (PREIMAGE (X 0) {i} INTER p_space p))`
      by PSET_TAC [dna_model_def, thmm_def, hmm_def, dtmc_def, distribution_def]
 ++ POP_ASSUM (MP_TAC o GSYM o Q.SPEC `START`)
 ++ RW_TAC real_ss [ini_distribution_def, distribution_def]);
	
val POS_START_FIVE = prove
  (``!X Y p s s1. dna_model X Y p s s1 ==>
   0 < cond_pmf p (X 2) (X 0) ({FIVE},{START})``,
    RW_TAC std_ss []
 ++ `distribution p (X 1) {E} <> 0` 
 	by (MATCH_MP_TAC REAL_POS_NZ ++ MATCH_MP_TAC POS_DISTR_E 
 	   ++ MAP_EVERY Q.EXISTS_TAC [`Y`, `s`, `s1`]
 	   ++ RW_TAC real_ss [])    
 ++ `distribution p (X 0) {START} <> 0` 
 	by (MATCH_MP_TAC REAL_POS_NZ ++ MP_RW_TAC START_DISTR ++ RW_TAC real_ss [])
 ++ PSET_TAC [dna_model_def, thmm_def, hmm_def, COND_PMF_EQ_COND_PROB]
 ++ `prob_space p` by PSET_TAC [random_variable_def]    
 ++ (MP_TAC o Q.ISPECL [`X:num -> 'a -> state`, 
    	`p:('a -> bool) # (('a -> bool) -> bool) # (('a -> bool) -> real)`, 
    	`s:(state -> bool) # ((state -> bool) -> bool)`, `1:num`, `START:state`,  
 	`FIVE:state`, `ini_distribution: state -> real`, 
    	`trans_distribution:num -> state -> state -> real`, `0:num`])
    	MC_NSTEP_COND_PROB ++ RW_TAC std_ss [COND_PMF_EQ_COND_PROB]
 ++ `START IN univ(:state)` by PSET_TAC []
 ++ `FIVE IN univ(:state)` by PSET_TAC []    	
 ++ MATCH_MP_TAC REAL_SUM_IMAGE_EXISTS_POS
 ++ RW_TAC std_ss []
 << [METIS_TAC [],
     
     MATCH_MP_TAC REAL_LE_MUL
     ++ RW_TAC std_ss []
     ++ MATCH_MP_TAC (MATCH_MP (METIS_PROVE [] ``(a ==> b /\ c) ==> (a ==> b)``) 
        	(SPEC_ALL COND_PROB_BOUNDS)) 
     ++ RW_TAC std_ss []
     ++ PROVE_TAC [DTMC_EVENTS],
     
     Q.EXISTS_TAC `E` ++ PSET_TAC [dtmc_def]
     ++ `Trans X p s 0 1 START E = trans_distribution 0 START E` 
     	by (FIRST_ASSUM (MP_TAC o GSYM o Q.SPECL [`START`, `E`, `0`]) ++ PSET_TAC [])
     ++ `Trans X p s 1 1 E FIVE = trans_distribution 1 E FIVE` 
     	by (FIRST_ASSUM (MP_TAC o GSYM o Q.SPECL [`E`, `FIVE`, `1`]) ++ PSET_TAC [])
     ++ PSET_TAC [Trans_def, trans_distribution_def, REAL_MUL_RID]
     ++ RW_TAC real_ss []]);
     
val POS_DISTRIBUTION_5 = prove
  (``!X Y p s s1 n. dna_model X Y p s s1 /\ 1 < n ==>
   0 < distribution p (X n) {FIVE}``,
    Induct_on `n` >> RW_TAC std_ss []
 ++ RW_TAC std_ss [COND_PMF_EQ_COND_PROB]
 ++ `prob_space p` by PSET_TAC [dna_model_def, thmm_def, hmm_def, random_variable_def]
 ++ `distribution p (X 1) {E} <> 0` 
 	by (MATCH_MP_TAC REAL_POS_NZ ++ MATCH_MP_TAC POS_DISTR_E 
 	   ++ MAP_EVERY Q.EXISTS_TAC [`Y`, `s`, `s1`]
 	   ++ RW_TAC real_ss [dna_model_def, thmm_def, hmm_def])    
 ++ `0 < distribution p (X 0) {START}` 
 	by (MP_RW_TAC START_DISTR 
 	   ++ RW_TAC real_ss [dna_model_def, thmm_def, hmm_def])    
 ++ `0 < cond_pmf p (X 2) (X 0) ({FIVE},{START})` 
 	by (MATCH_MP_TAC POS_START_FIVE	++ MAP_EVERY Q.EXISTS_TAC [`Y`, `s`, `s1`]
 	   ++ RW_TAC real_ss [dna_model_def, thmm_def, hmm_def])
 ++ Cases_on `n = 1`
 >> (PSET_TAC [dna_model_def, thmm_def, hmm_def]
     ++ (MP_TAC o Q.ISPECL [`X:num -> 'a -> state`, `2:num`, `0:num`, `FIVE:state`, 
    	`ini_distribution: state -> real`, `trans_distribution:num -> state -> state -> real`,  
    	`p:('a -> bool) # (('a -> bool) -> bool) # (('a -> bool) -> real)`, 
    	`s:(state -> bool) # ((state -> bool) -> bool)`])
    	N_STEP_PROB_DISTRIBUTION ++ RW_TAC std_ss []
     ++ MATCH_MP_TAC REAL_SUM_IMAGE_EXISTS_POS
     ++ RW_TAC std_ss []
     << [METIS_TAC [],
         MATCH_MP_TAC REAL_LE_MUL
         ++ RW_TAC std_ss [distribution_def, COND_PMF_EQ_COND_PROB]
         >> (MATCH_MP_TAC PROB_POSITIVE
            ++ PROVE_TAC [DTMC_EVENTS])
         ++ MATCH_MP_TAC (MATCH_MP (METIS_PROVE [] ``(a ==> b /\ c) ==> (a ==> b)``) 
        	(SPEC_ALL COND_PROB_BOUNDS)) 
         ++ RW_TAC std_ss []
         ++ PROVE_TAC [DTMC_EVENTS],
         
         Q.EXISTS_TAC `START` ++ PSET_TAC [dtmc_def]
         ++ MATCH_MP_TAC REAL_LT_MUL 
         ++ RW_TAC std_ss [COND_PMF_EQ_COND_PROB]])
 ++ `dtmc X p s ini_distribution trans_distribution /\ FINITE (space s)`
 	by PSET_TAC [dna_model_def, thmm_def, hmm_def]
 ++ (MP_TAC o Q.ISPECL [`X:num -> 'a -> state`, `1:num`, `n:num`, `FIVE:state`, 
    	`ini_distribution: state -> real`, `trans_distribution:num -> state -> state -> real`,  
    	`p:('a -> bool) # (('a -> bool) -> bool) # (('a -> bool) -> real)`, 
    	`s:(state -> bool) # ((state -> bool) -> bool)`])
    	N_STEP_PROB_DISTRIBUTION ++ RW_TAC std_ss [GSYM ADD1, dna_model_def, thmm_def, hmm_def]
 ++ MATCH_MP_TAC REAL_SUM_IMAGE_EXISTS_POS
 ++ RW_TAC std_ss []
 >> (MATCH_MP_TAC REAL_LE_MUL
     ++ RW_TAC std_ss [distribution_def, COND_PMF_EQ_COND_PROB]
     >> (MATCH_MP_TAC PROB_POSITIVE
         ++ PROVE_TAC [DTMC_EVENTS])
     ++ MATCH_MP_TAC (MATCH_MP (METIS_PROVE [] ``(a ==> b /\ c) ==> (a ==> b)``) 
        	(SPEC_ALL COND_PROB_BOUNDS)) 
     ++ RW_TAC std_ss []
     ++ PROVE_TAC [DTMC_EVENTS])
 ++ Q.EXISTS_TAC `E` ++ PSET_TAC []
 >> PSET_TAC [dna_model_def, thmm_def, hmm_def]
 ++ MATCH_MP_TAC REAL_LT_MUL
 ++ RW_TAC std_ss [] 
 >> (MATCH_MP_TAC POS_DISTR_E
    ++ MAP_EVERY Q.EXISTS_TAC [`Y`, `s`, `s1`]
    ++ FULL_SIMP_TAC arith_ss []) 
 ++ `th_dtmc X p s ini_distribution trans_distribution`
 	by PSET_TAC [dna_model_def, thmm_def, hmm_def, th_dtmc_def]
 ++ (IMP_RES_TAC o Q.ISPECL [`X:num -> 'a -> state`, 
 	`p:('a -> bool) # (('a -> bool) -> bool) # (('a -> bool) -> real)`,
 	`s:(state -> bool) # ((state -> bool) -> bool)`,
 	`ini_distribution: state -> real`, `trans_distribution:num -> state -> state -> real`])
 	HOMO_LEMMA ++ RW_TAC std_ss [COND_PMF_EQ_COND_PROB, ADD1]
 ++ POP_ASSUM (MP_TAC o Q.SPECL [`n`, `1`, `FIVE`, `E`])
 ++ RW_TAC std_ss [] 
 ++ PSET_TAC [dtmc_def]
 ++ `Trans X p s 1 1 E FIVE = trans_distribution 1 E FIVE`
 	by (FIRST_ASSUM (MP_TAC o GSYM o Q.SPECL [`E`, `FIVE`, `1`]) ++ PSET_TAC [])
 ++ `E IN space s` by PSET_TAC [dna_model_def, thmm_def, hmm_def]
 ++ `FIVE IN space s` by PSET_TAC [dna_model_def, thmm_def, hmm_def]    	
 ++ FULL_SIMP_TAC std_ss [Trans_def, trans_distribution_def]
 ++ RW_TAC real_ss []);
         	  
val POS_FIVE_I = prove
  (``!X Y p s s1. dna_model X Y p s s1 ==>
   0 < cond_prob p (PREIMAGE (X 3) {I} INTER p_space p)
      (PREIMAGE (X 2) {FIVE} INTER p_space p)``,
    RW_TAC std_ss [dna_model_def, thmm_def, hmm_def]
 ++ `prob_space p` by PSET_TAC [random_variable_def]
 ++ `distribution p (X 2) {FIVE} <> 0`
 	by (MATCH_MP_TAC REAL_POS_NZ ++ MATCH_MP_TAC POS_DISTRIBUTION_5
 	   ++ MAP_EVERY Q.EXISTS_TAC [`Y`, `s`, `s1`]
 	   ++ RW_TAC real_ss [dna_model_def, thmm_def, hmm_def])     
 ++ `I IN univ(:state)` by PSET_TAC []
 ++ `FIVE IN univ(:state)` by PSET_TAC []    	
 ++ `!i j t. distribution p (X t) {i} <> 0 ==>
           (trans_distribution t i j = Trans X p s t 1 i j)`
        by PSET_TAC [dtmc_def]	   
 ++ POP_ASSUM (MP_TAC o GSYM o Q.SPECL [`FIVE`, `I`, `2`])
 ++ RW_TAC real_ss [Trans_def, trans_distribution_def]);
             
val POS_DISTRIBUTION_I = prove
  (``!X Y p s s1 n. 2 < n /\ dna_model X Y p s s1 ==>
   	0 < distribution p (X n) {I}``,
    Induct_on `n` >> RW_TAC std_ss []
 ++ RW_TAC std_ss [COND_PMF_EQ_COND_PROB]
 ++ `prob_space p` by PSET_TAC [dna_model_def, thmm_def, hmm_def, random_variable_def]
 ++ `0 < distribution p (X 2) {FIVE}`
 	by (MATCH_MP_TAC POS_DISTRIBUTION_5
 	   ++ MAP_EVERY Q.EXISTS_TAC [`Y`, `s`, `s1`]
 	   ++ RW_TAC real_ss [dna_model_def, thmm_def, hmm_def])      
 ++ `distribution p (X 2) {FIVE} <> 0` 
 	by (MATCH_MP_TAC REAL_POS_NZ ++ RW_TAC std_ss [])     
 ++ `0 < cond_prob p (PREIMAGE (X 3) {I} INTER p_space p)
      (PREIMAGE (X 2) {FIVE} INTER p_space p)` 
      by (MATCH_MP_TAC POS_FIVE_I ++ MAP_EVERY Q.EXISTS_TAC [`Y`, `s`, `s1`]
         ++ RW_TAC std_ss [])	
 ++ `dtmc X p s ini_distribution trans_distribution /\ FINITE (space s)`
 	by PSET_TAC [dna_model_def, thmm_def, hmm_def] 	   
 ++ Cases_on `n = 2`
 >> (PSET_TAC [dna_model_def, thmm_def, hmm_def]
     ++ (MP_TAC o Q.ISPECL [`X:num -> 'a -> state`, `1:num`, `2:num`, `I:state`, 
    	`ini_distribution: state -> real`, `trans_distribution:num -> state -> state -> real`,  
    	`p:('a -> bool) # (('a -> bool) -> bool) # (('a -> bool) -> real)`, 
    	`s:(state -> bool) # ((state -> bool) -> bool)`])
    	N_STEP_PROB_DISTRIBUTION ++ RW_TAC std_ss []
     ++ MATCH_MP_TAC REAL_SUM_IMAGE_EXISTS_POS
     ++ RW_TAC std_ss []
     << [METIS_TAC [],
         MATCH_MP_TAC REAL_LE_MUL
         ++ RW_TAC std_ss [distribution_def, COND_PMF_EQ_COND_PROB]
         >> (MATCH_MP_TAC PROB_POSITIVE
            ++ PROVE_TAC [DTMC_EVENTS])
         ++ MATCH_MP_TAC (MATCH_MP (METIS_PROVE [] ``(a ==> b /\ c) ==> (a ==> b)``) 
        	(SPEC_ALL COND_PROB_BOUNDS)) 
         ++ RW_TAC std_ss []
         ++ PROVE_TAC [DTMC_EVENTS],
         
         Q.EXISTS_TAC `FIVE` ++ PSET_TAC [dtmc_def]
         ++ MATCH_MP_TAC REAL_LT_MUL 
         ++ RW_TAC std_ss [COND_PMF_EQ_COND_PROB]])
 ++ `0 < distribution p (X n) {I}` by (`2 < n` by RW_TAC arith_ss [] ++ METIS_TAC [])         
 ++ (MP_TAC o Q.ISPECL [`X:num -> 'a -> state`, `1:num`, `n:num`, `I:state`, 
    	`ini_distribution: state -> real`, `trans_distribution:num -> state -> state -> real`,  
    	`p:('a -> bool) # (('a -> bool) -> bool) # (('a -> bool) -> real)`, 
    	`s:(state -> bool) # ((state -> bool) -> bool)`])
    	N_STEP_PROB_DISTRIBUTION ++ RW_TAC std_ss [GSYM ADD1, dna_model_def, thmm_def, hmm_def]
 ++ MATCH_MP_TAC REAL_SUM_IMAGE_EXISTS_POS
 ++ RW_TAC std_ss []
 >> (MATCH_MP_TAC REAL_LE_MUL
     ++ RW_TAC std_ss [distribution_def, COND_PMF_EQ_COND_PROB]
     >> (MATCH_MP_TAC PROB_POSITIVE
         ++ PROVE_TAC [DTMC_EVENTS])
     ++ MATCH_MP_TAC (MATCH_MP (METIS_PROVE [] ``(a ==> b /\ c) ==> (a ==> b)``) 
        	(SPEC_ALL COND_PROB_BOUNDS)) 
     ++ RW_TAC std_ss []
     ++ PROVE_TAC [DTMC_EVENTS])
 ++ Q.EXISTS_TAC `I` ++ PSET_TAC []
 >> PSET_TAC [dna_model_def, thmm_def, hmm_def]
 ++ MATCH_MP_TAC REAL_LT_MUL
 ++ RW_TAC std_ss [] 
 ++ `distribution p (X n) {I} <> 0` by METIS_TAC [REAL_POS_NZ]
 ++ `!i j t. distribution p (X t) {i} <> 0 ==>
           (trans_distribution t i j = Trans X p s t 1 i j)`
        by PSET_TAC [dtmc_def]	   
 ++ POP_ASSUM (MP_TAC o GSYM o Q.SPECL [`I`, `I`, `n`])
 ++ RW_TAC real_ss [COND_PMF_EQ_COND_PROB, ADD1, Trans_def, trans_distribution_def]);

(* ------------------------------------------------------------------------- *)
(*========              Probability of this DNA sequence            =========*)   
(* ------------------------------------------------------------------------- *)  

val dna_recognition_thm = store_thm
  ("dna_recognition_thm",
  ``!X Y p s s1. dna_model X Y p s s1 ==>
    (prob p (BIGINTER (IMAGE (\(k:num). PREIMAGE (X k) {EL k states} INTER p_space p)
                	(count 28)) INTER 
            BIGINTER (IMAGE (\(k:num). PREIMAGE (Y (k + 1)) {EL k dna_seq} INTER p_space p)
                	(count 26))) =
    (0.25 pow 18) * (0.9 pow 23) * (0.1 pow 4) * 0.95 * (0.4 pow 5))``,
    RW_TAC std_ss [dna_model_def, thmm_def]
 ++ `LENGTH dna_seq = 26` by RW_TAC arith_ss [dna_seq_def, LENGTH]
 ++ `LENGTH states = 28` by RW_TAC arith_ss [states_def, LENGTH]  
 ++ (MP_TAC o Q.ISPECL [`X:num -> 'a -> state`, `Y:num -> 'a -> dna`, 
 	`p:('a -> bool) # (('a -> bool) -> bool) # (('a -> bool) -> real)`, 
 	`s:(state -> bool) # ((state -> bool) -> bool)`, 
 	`s1:(dna -> bool) # ((dna -> bool) -> bool)`, 
 	`ini_distribution: state -> real`, `trans_distribution:num -> state -> state -> real`,
 	`emission_distribution: num -> dna -> state -> real`, `0:num`, `25:num`, 
 	`states:state list`, `dna_seq:dna list`]) HMM_START_END_PROB
 ++ PSET_TAC [thmm_def] ++ POP_ASSUM K_TAC
 ++ `!i. prob p (PREIMAGE (X 0) {i} INTER p_space p) = ini_distribution i`
    	by PSET_TAC [hmm_def, th_dtmc_def, dtmc_def, distribution_def] 
 ++ `!t a i. distribution p (X t) {i} <> 0 ==>
 	(cond_prob p (PREIMAGE (Y t) {a} INTER p_space p)
               (PREIMAGE (X t) {i} INTER p_space p) = emission_distribution t a i)` 
        by PSET_TAC [hmm_def]        
 ++ `!t n i j. cond_prob p (PREIMAGE (X (t + 1)) {j} INTER p_space p)
             (PREIMAGE (X t) {i} INTER p_space p) =
           cond_prob p (PREIMAGE (X (n + 1)) {j} INTER p_space p)
             (PREIMAGE (X n) {i} INTER p_space p)` 
        by METIS_TAC [HOMO_LEMMA, th_dtmc_def, hmm_def]
 ++ `distribution p (X 26) {I} <> 0`
 	by (MATCH_MP_TAC REAL_POS_NZ ++ MATCH_MP_TAC POS_DISTRIBUTION_I 
 	   ++ MAP_EVERY Q.EXISTS_TAC [`Y`, `s`, `s1`]
 	   ++ RW_TAC real_ss [dna_model_def, thmm_def])    
 ++ `!i j t. distribution p (X t) {i} <> 0 ==>
 	(cond_prob p (PREIMAGE (X (t + 1)) {j} INTER p_space p)
               (PREIMAGE (X t) {i} INTER p_space p) = trans_distribution t i j)` 
 	by PSET_TAC [hmm_def, th_dtmc_def, dtmc_def, Trans_def] 
 ++ `cond_prob p (PREIMAGE (X 27) {END} INTER p_space p)
      (PREIMAGE (X 26) {I} INTER p_space p) = trans_distribution 0 I END`
      by (POP_ASSUM (MP_TAC o Q.SPECL [`I`, `END`, `26`])
         ++ RW_TAC arith_ss [trans_distribution_def]) 
 ++ `trans_distribution 0 I END = 0.1` by RW_TAC arith_ss [trans_distribution_def]
 ++ `distribution p (X 0) {START} = 1` 
 	by (MATCH_MP_TAC START_DISTR ++ MAP_EVERY Q.EXISTS_TAC [`Y`, `s`, `s1`]
           ++ RW_TAC real_ss [dna_model_def, thmm_def])
 ++ `distribution p (X 0) {START} <> 0` 
 	by (MATCH_MP_TAC REAL_POS_NZ 
 	   ++ RW_TAC real_ss [])
 ++ `cond_prob p (PREIMAGE (X 1) {E} INTER p_space p)
       (PREIMAGE (X 0) {START} INTER p_space p) = trans_distribution 0 START E`
       by (FIRST_ASSUM (MP_TAC o Q.SPECL [`START`, `E`, `0`])
         ++ DISCH_TAC ++ FULL_SIMP_TAC arith_ss [])  
 ++ `trans_distribution 0 START E = 1` by RW_TAC arith_ss [trans_distribution_def]
 ++ `!n. 0 < n ==> distribution p (X n) {E} <> 0` 
 	by (RW_TAC std_ss [] ++ MATCH_MP_TAC REAL_POS_NZ
 	   ++ MATCH_MP_TAC POS_DISTR_E
           ++ MAP_EVERY Q.EXISTS_TAC [`Y`, `s`, `s1`]
           ++ RW_TAC real_ss [dna_model_def, thmm_def])
 ++ `!n. 1 < n ==> distribution p (X n) {FIVE} <> 0` 
 	by (RW_TAC std_ss [] ++ MATCH_MP_TAC REAL_POS_NZ
 	   ++ MATCH_MP_TAC POS_DISTRIBUTION_5
           ++ MAP_EVERY Q.EXISTS_TAC [`Y`, `s`, `s1`]
           ++ RW_TAC real_ss [dna_model_def, thmm_def])
 ++ `!n. 2 < n ==> distribution p (X n) {I} <> 0` 
 	by (RW_TAC std_ss [] ++ MATCH_MP_TAC REAL_POS_NZ
 	   ++ MATCH_MP_TAC POS_DISTRIBUTION_I
           ++ MAP_EVERY Q.EXISTS_TAC [`Y`, `s`, `s1`]
           ++ RW_TAC real_ss [dna_model_def, thmm_def])             
 ++ RW_TAC std_ss [CONV_RULE SUC_TO_NUMERAL_DEFN_CONV (CONJ EL mulcon_def), dna_seq_def,
 		 states_def,HD,TL, ini_distribution_def, emission_distribution_def,
 		 trans_distribution_def]
 ++ RW_TAC real_ss []);
       
 val _ = export_theory();   
