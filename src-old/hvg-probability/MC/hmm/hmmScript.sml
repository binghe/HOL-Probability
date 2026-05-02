(*=================================================================*)
(* The indices of the theorems refer to the order that the theorem *)
(* presented in the paper.                                         *)
(* Those theorems, which are not numbered in this file,            *)
(* have not been presented in the paper                            *)
(*=================================================================*)

(*val () = app load
 ["bossLib", "metisLib", "arithmeticTheory", "pred_setTheory", "realLib", "seqTheory",
 	"pairTheory", "combinTheory", "listTheory", "rich_listTheory", "transcTheory", "numLib", 
 	"prim_recTheory", "probabilityTheory", "satTheory", "cond_probTheory", 		"extra_pred_setTools", "dep_rewrite",
 	"dtmcBasicTheory", "setUsefulTheory"];

set_trace "Unicode" 0;*)

open HolKernel Parse boolLib bossLib metisLib numLib combinTheory subtypeTheory
	pred_setTheory measureTheory listTheory rich_listTheory numLib seqTheory dep_rewrite
     extra_pred_setTheory arithmeticTheory realTheory realLib pairTheory extra_pred_setTools
      transcTheory prim_recTheory extrealTheory probabilityTheory satTheory cond_probTheory 
      dtmcBasicTheory setUsefulTheory;

val _ = new_theory "hmm";

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
(* Definition of HMM                                                         *)
(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)
(* Definition 5: HMM                                                         *)
(* ------------------------------------------------------------------------- *)  
val hmm_def = Define `
    hmm X Y p s s1 Linit Ltrans (Btrans: num -> 'c -> 'b -> real) =
    dtmc X p s Linit Ltrans /\ (!(t:num). random_variable ((Y:num -> 'a -> 'c) t) p s1) /\ 
    (!(i:'c). i IN space s1 ==> {i} IN subsets s1) /\ 
    (!t a i. distribution p (X t) {i} <> 0 ==>
        (Btrans t a i = cond_prob p (PREIMAGE (Y t) {a} INTER p_space p) 
                                    (PREIMAGE (X t) {i} INTER p_space p))) /\ 
    (!a i t u v (Lx:'b list) (Ly:'c list) Ltx Lty. 
        t NOTIN {u + r | r IN Lty} /\ t NOTIN {v + r | r IN Ltx} /\
        (prob p (BIGINTER (IMAGE (\k. PREIMAGE (Y (u + k)) {EL k Ly} INTER p_space p) Lty)
        	 INTER
                 BIGINTER (IMAGE (\k. PREIMAGE (X (v + k)) {EL k Lx} INTER p_space p) Ltx)) 
                <> 0) ==> 
        (cond_prob p (PREIMAGE (Y t) {a} INTER p_space p)
                     ((PREIMAGE (X t) {i} INTER p_space p) INTER
        	     (BIGINTER (IMAGE (\k. PREIMAGE (Y (u + k)) {EL k Ly} INTER p_space p) Lty))
        	      INTER
                     (BIGINTER (IMAGE (\k. PREIMAGE (X (v + k)) {EL k Lx} INTER p_space p) Ltx)))
                      =
         cond_prob p (PREIMAGE (Y t) {a} INTER p_space p)
                     (PREIMAGE (X t) {i} INTER p_space p)))`;

(* ------------------------------------------------------------------------- *)
(* Definition 6: Time-homogeneous HMM                                        *)
(* ------------------------------------------------------------------------- *) 
val thmm_def = Define `
    thmm X Y p s s1 Linit Ltrans Btrans =
    hmm X Y p s s1 Linit Ltrans Btrans /\ FINITE (space s1) /\ FINITE (space s) /\
    !t i j a. (Trans X p s (t + 1) 1 i j = Trans X p s t 1 i j) /\
           (Btrans (t + 1) a i = Btrans t a i)`;              

(*======== some theorems for preparing =========*)
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
 
val PREIMAGE_X_IN_EVENTS = store_thm
  ("PREIMAGE_X_IN_EVENTS",
  ``!(X:num -> 'a -> 'c) p s. (!(t:num). random_variable (X t) p s) /\ 
  	(!i. i IN space s ==> {i} IN subsets s) ==> 
        !j t. j IN space s ==> (PREIMAGE (X t) {j} INTER p_space p) IN events p``,
    RW_TAC std_ss [random_variable_def]
 ++ PSET_TAC [IN_MEASURABLE, space_def, subsets_def]);

val BIGINTER_SUBSET_SING = store_thm
  ("BIGINTER_SUBSET_SING",
   ``!f s m. m IN s ==> BIGINTER (IMAGE f s) SUBSET (f m)``,
    PSET_TAC [IN_BIGINTER_IMAGE, EXTENSION]);
    
val COND_PROB_ZERO_INTER = store_thm 
  ("COND_PROB_ZERO_INTER",
   ``!p A B. prob_space p /\ A IN events p /\ B IN events p /\ (prob p (A INTER B) = 0) ==> 
     (cond_prob p A B = 0)``,
     RW_TAC std_ss [cond_prob_def, REAL_DIV_LZERO]);

val PROB_ZERO_INTER = store_thm(
   "PROB_ZERO_INTER",
   (--`!p A B.
       (prob_space p) /\ (A IN events p) /\ (B IN events p) /\ (prob p A = 0) ==>
         (prob p (A INTER B) = 0)`--),
       RW_TAC std_ss [] ++ (MP_TAC o Q.SPECL [`p`, `B`, `A`]) PROB_INTER_ZERO  ++ RW_TAC std_ss [INTER_COMM]);
            
fun def_nth_conj i def = List.nth (strip_conj (rhs (concl (SPEC_ALL def))), i-1);

fun DEF_NTH_CONJS is def =
  GEN_ALL (prove(mk_imp(lhs (concl (SPEC_ALL def)),list_mk_conj (List.map (fn i => def_nth_conj i def) is)),SIMP_TAC std_ss [def]));;

fun ASM_CSQS_THEN is def ttac = FIRST_ASSUM (ttac o MATCH_MP (DEF_NTH_CONJS is def));

val BIGINTER_SUBSET_BIGINTER = prove
  (``!f s t. t SUBSET s ==> BIGINTER (IMAGE f s) SUBSET BIGINTER (IMAGE f t)``,
    PSET_TAC [IN_BIGINTER_IMAGE]);

val PROB_SUBSET_NZ = prove
  (``!p A B. prob_space p /\ (prob p A <> 0) /\ A SUBSET B /\
  	A IN events p /\ B IN events p ==> (prob p B <> 0)``,
    SPOSE_NOT_THEN STRIP_ASSUME_TAC 
 ++ `prob p A = 0` by (NTAC 4 (POP_ASSUM MP_TAC) ++ POP_ASSUM K_TAC ++ REPEAT DISCH_TAC
 ++ METIS_TAC [PROB_INCREASING, PROB_POSITIVE, REAL_LE_ANTISYM]));

val INTER_SUBSET_INTER = prove
  (``!A B C. A SUBSET B ==> C INTER A SUBSET C INTER B``,
        PSET_TAC []);

val REAL_SUM_IMAGE_SUBSET_0 = prove
  (``!f s t. t SUBSET s /\ FINITE s /\ (SIGMA f (s DIFF t) = (0:real)) ==> 
  	(SIGMA f t = SIGMA f s)``,
    RW_TAC std_ss []
 ++ `s = t UNION (s DIFF t)` by PSET_TAC [UNION_DIFF]
 ++ POP_ORW
 ++ DEP_REWRITE_TAC [REAL_SUM_IMAGE_DISJOINT_UNION]
 ++ PSET_TAC [DISJOINT_DIFF, FINITE_DIFF, REAL_ADD_RID]
 ++ DEP_REWRITE_TAC [SUBSET_FINITE]
 ++ Q.EXISTS_TAC `s` ++ PSET_TAC []); 

 
val PRE_HMM_JOINT_PROB = store_thm
  ("PRE_HMM_JOINT_PROB",  
  ``!X Y p s s1 Linit Ltrans (Btrans: num -> 'c -> 'b -> real) t m n (Lx:'b list) (Ly:'c list).
   thmm X Y p s s1 Linit Ltrans Btrans /\ m <= n /\ 1 <= m /\
   (prob p (BIGINTER (IMAGE (\k. PREIMAGE (X (t + k)) {EL k Lx} INTER p_space p)
            (count (n + 1)))) <> 0) ==>
   (cond_prob p (BIGINTER (IMAGE (\k. PREIMAGE (Y (t + k)) {EL k Ly} INTER p_space p) 
 		(count (m + 1))))
            (BIGINTER (IMAGE (\k. PREIMAGE (X (t + k)) {EL k Lx} INTER p_space p) 
            	(count (n + 1)))) =
    cond_prob p (PREIMAGE (Y t) {EL 0 Ly} INTER p_space p) 
    		(PREIMAGE (X t) {EL 0 Lx} INTER p_space p) *
    mulcon (0,m) (\k. cond_prob p (PREIMAGE (Y (t + k + 1)) {EL (k + 1) Ly} INTER p_space p)
           (PREIMAGE (X (t + k + 1)) {EL (k + 1) Lx} INTER p_space p)))``,
    Induct_on `m` >> RW_TAC std_ss []
 ++ RW_TAC std_ss [ADD, COUNT_SUC, IMAGE_INSERT, BIGINTER_INSERT, mulcon_def]
 ++ `prob_space p` by FULL_SIMP_TAC std_ss [thmm_def, hmm_def, random_variable_def]
 ++ `~(?m. m IN count (n + 1) /\ EL m Lx NOTIN space s)`
 	by (SPOSE_NOT_THEN STRIP_ASSUME_TAC
 	   ++ `BIGINTER (IMAGE (\k. PREIMAGE (X (t + k)) {EL k Lx} INTER p_space p)
       		(count (n + 1))) SUBSET (\k. PREIMAGE (X (t + k)) {EL k Lx} INTER p_space p) m'` 
                by (`PREIMAGE (X (t + m')) {EL m' Lx} INTER p_space p =
                   	(\k. PREIMAGE (X (t + k)) {EL k Lx} INTER p_space p) m'` by RW_TAC std_ss []
                   ++ POP_ORW ++ MATCH_MP_TAC BIGINTER_SUBSET_SING ++ RW_TAC std_ss [])
           ++ `PREIMAGE (X (t + m')) {EL m' Lx} INTER p_space p = {}`
       		by (MATCH_MP_TAC NOTIN_SPACE_EVENTS ++ Q.EXISTS_TAC `s` 
       		   ++ PSET_TAC [thmm_def, hmm_def, dtmc_def, mc_property_def])                   
 	   ++ METIS_TAC [SUBSET_EMPTY, PROB_EMPTY])
 ++ Cases_on `m = 0`
 >> (RW_TAC std_ss [COUNT_ONE, IMAGE_SING, BIGINTER_SING, mulcon_def, REAL_MUL_LID]
    ++ Cases_on `EL 1 Ly NOTIN (space s1)`
    >> (`PREIMAGE (Y (t + 1)) {EL 1 Ly} INTER p_space p = {}`
    	by (MATCH_MP_TAC NOTIN_SPACE_EVENTS ++ Q.EXISTS_TAC `s1` 
       		   ++ PSET_TAC [thmm_def, hmm_def, dtmc_def, mc_property_def])
       ++ RW_TAC std_ss [INTER_EMPTY, cond_prob_def, PROB_EMPTY, REAL_DIV_LZERO, real_div,
       		REAL_MUL_RZERO, REAL_MUL_LZERO])
    ++ Cases_on `EL 0 Ly NOTIN (space s1)`
    >> (`PREIMAGE (Y t) {EL 0 Ly} INTER p_space p = {}`
    	by (MATCH_MP_TAC NOTIN_SPACE_EVENTS ++ Q.EXISTS_TAC `s1` 
       		   ++ PSET_TAC [thmm_def, hmm_def, dtmc_def, mc_property_def])
       ++ RW_TAC std_ss [INTER_EMPTY, cond_prob_def, PROB_EMPTY, REAL_DIV_LZERO, real_div,
       		REAL_MUL_RZERO, REAL_MUL_LZERO])
    ++ `PREIMAGE (Y (t + 1)) {EL 1 Ly} INTER p_space p IN events p`
    	by METIS_TAC [thmm_def, hmm_def, PREIMAGE_X_IN_EVENTS]
    ++ `PREIMAGE (Y t) {EL 0 Ly} INTER p_space p IN events p`
    	by METIS_TAC [thmm_def, hmm_def, PREIMAGE_X_IN_EVENTS]    
    ++ MP_RW_TAC COND_PROB_INTER_SPLIT 
    >> (RW_TAC std_ss [GSYM ADD1]
        ++ `BIGINTER (IMAGE (\k. PREIMAGE (X (t + k)) {EL k Lx} INTER p_space p) (count (SUC n))) =
        BIGINTER (IMAGE (\k. (\k. PREIMAGE (X (t + k)) {EL k Lx} INTER p_space p) k) 
        	(count (SUC n)))` by RW_TAC std_ss [] ++ POP_ORW
        ++ MATCH_MP_TAC EVENTS_BIGINTER ++ PSET_TAC [IN_FUNSET]
        ++ METIS_TAC [thmm_def, hmm_def, DTMC_EVENTS])
    ++ `t NOTIN {t + r | r IN count_mn 1 n}`
          	by (PSET_TAC [IN_COUNT_MN, EXTENSION] ++ RW_TAC arith_ss [])    
    ++ `BIGINTER (IMAGE (\k. (\k. PREIMAGE (X (t + k)) {EL k Lx} INTER p_space p) k)
                (count_mn 1 n)) IN events p` 
       		by (MATCH_MP_TAC EVENTS_BIGINTER_MN ++ RW_TAC arith_ss []
        	   ++ METIS_TAC [thmm_def, hmm_def, DTMC_EVENTS]) 
    ++ POP_ASSUM MP_TAC ++ RW_TAC std_ss []        	   
    ++ `prob p (BIGINTER (IMAGE (\k. PREIMAGE (X (t + k)) {EL k Lx} INTER p_space p) 
    	(count_mn 1 n))) <> 0`
    		by (MATCH_MP_TAC PROB_SUBSET_NZ
    	   	   ++ Q.EXISTS_TAC `BIGINTER (IMAGE (\k. PREIMAGE (X (t + k)) {EL k Lx} INTER
    	   		p_space p) (count (n + 1)))` ++ RW_TAC std_ss []
    	           >> (MATCH_MP_TAC BIGINTER_SUBSET_BIGINTER 
    	              ++ PSET_TAC [count_mn_def, count_def, EXTENSION]
    	              ++ RW_TAC arith_ss []))  
    ++ `BIGINTER (IMAGE (\k. PREIMAGE (X (t + k)) {EL k Lx} INTER p_space p) (count (n + 1))) =
           (PREIMAGE (X t) {EL 0 Lx} INTER p_space p) INTER 
            BIGINTER (IMAGE (\k. PREIMAGE (X (t + k)) {EL k Lx} INTER p_space p) (count_mn 1 n))`
           	by (`count (n + 1) = {(0:num)} UNION (count_mn 1 n)` 
           		by (PSET_TAC [count_def, count_mn_def, EXTENSION] ++ RW_TAC arith_ss [])
              	   ++ RW_TAC std_ss [IMAGE_UNION, BIGINTER_UNION, IMAGE_SING, BIGINTER_SING]
                   ++ Q.ABBREV_TAC `A = PREIMAGE (Y t) {EL 0 Ly} INTER p_space p`
                   ++ Q.ABBREV_TAC `B = PREIMAGE (X t) {EL 0 Lx} INTER p_space p`
                   ++ METIS_TAC [INTER_ASSOC, INTER_COMM]) 
    ++ PSET_TAC [thmm_def, hmm_def, ADD1] 
    ++ `0 NOTIN count_mn 1 n` by PSET_TAC [count_mn_def]
    ++ `0 NOTIN {}:num -> bool` by PSET_TAC []
    ++ FIRST_ASSUM (MP_TAC o GSYM o Q.SPECL [`EL 0 Ly`, `EL 0 Lx`, `t`, `t`, `t`, `Lx`, `Ly`, 
    		`count_mn 1 n`, `{}:num -> bool`]) 
    ++ RW_TAC std_ss [IMAGE_EMPTY, BIGINTER_EMPTY, INTER_UNIV] ++ NTAC 3 (POP_ASSUM K_TAC)
    ++ Cases_on `prob p (PREIMAGE (Y t) {EL 0 Ly} INTER p_space p INTER
        	BIGINTER (IMAGE (\k. PREIMAGE (X (t + k)) {EL k Lx} INTER p_space p) 
       		 (count (n + 1)))) = 0` 
    >> (`cond_prob p (PREIMAGE (Y t) {EL 0 Ly} INTER p_space p)
      		(PREIMAGE (X t) {EL 0 Lx} INTER p_space p INTER
       		BIGINTER (IMAGE (\k. PREIMAGE (X (t + k)) {EL k Lx} INTER p_space p)
            (count_mn 1 n))) = 0` by PSET_TAC [cond_prob_def, REAL_DIV_LZERO]
           ++ RW_TAC std_ss [ADD1, REAL_MUL_LZERO, REAL_MUL_RZERO]) ++ POP_ASSUM MP_TAC
    ++ NTAC 3 (POP_ASSUM K_TAC) ++ DISCH_TAC
    ++ `!(a:real) b c. (a = b) ==> (a * c = c * b)` by RW_TAC std_ss [REAL_MUL_COMM]
    ++ POP_ASSUM MATCH_MP_TAC 
    ++ `1 NOTIN {0} UNION count_mn 2 n` by PSET_TAC [count_mn_def]
    ++ `1 NOTIN {0:num}` by PSET_TAC []
    ++ `BIGINTER (IMAGE (\k. PREIMAGE (X (t + k)) {EL k Lx} INTER p_space p) (count_mn 1 n)) =
        	PREIMAGE (X (t + 1)) {EL 1 Lx} INTER p_space p INTER
            BIGINTER (IMAGE (\k. PREIMAGE (X (t + k)) {EL k Lx} INTER p_space p) (count_mn 2 n))`
        	by (`count_mn 1 n = {1} UNION count_mn 2 n` by (PSET_TAC [IN_COUNT_MN, EXTENSION] 
        	   ++ RW_TAC arith_ss []) ++ POP_ORW 
                   ++ RW_TAC std_ss [IMAGE_UNION, BIGINTER_UNION, IMAGE_SING, BIGINTER_SING])
    ++ POP_ORW   
    ++ `!A B C D E. A INTER B INTER (C INTER B INTER (D INTER B INTER E)) = 
    		D INTER B INTER (A INTER B INTER C INTER B INTER E)` 
    		by METIS_TAC [INTER_ASSOC, INTER_COMM] ++ POP_ORW
    ++ Suff `prob p (PREIMAGE (Y t) {EL 0 Ly} INTER p_space p INTER
            	BIGINTER (IMAGE (\k. PREIMAGE (X (t + k)) {EL k Lx} INTER p_space p)
                   ({0} UNION count_mn 2 n))) <> 0`
    >> (RW_TAC std_ss [] ++ NTAC 17 (POP_ASSUM MP_TAC)
       ++ POP_ASSUM (MP_TAC o GSYM o Q.SPECL [`EL 1 Ly`, `EL 1 Lx`, `t + 1`, `t`, 
       		`t`, `Lx`, `Ly`, `{0} UNION count_mn 2 n`, `{(0:num)}`]) 
       ++ RW_TAC std_ss [IMAGE_UNION, BIGINTER_UNION, IMAGE_SING, BIGINTER_SING, IN_SING]   
       ++ FULL_SIMP_TAC std_ss [GSYM INTER_ASSOC])
    ++ NTAC 2 (POP_ASSUM K_TAC) 
    ++ MATCH_MP_TAC PROB_SUBSET_NZ
    ++ Q.EXISTS_TAC `PREIMAGE (Y t) {EL 0 Ly} INTER p_space p INTER
    	   	BIGINTER (IMAGE (\k. PREIMAGE (X (t + k)) {EL k Lx} INTER
    	   		p_space p) (count (n + 1)))` ++ RW_TAC std_ss []
    << [Q.ABBREV_TAC `A = PREIMAGE (Y t) {EL 0 Ly} INTER p_space p`
           ++ MATCH_MP_TAC INTER_SUBSET_INTER
           ++ MATCH_MP_TAC BIGINTER_SUBSET_BIGINTER
           ++ PSET_TAC [IN_COUNT_MN, EXTENSION] 
           >> RW_TAC arith_ss [] ++ RW_TAC arith_ss [],
              
            MATCH_MP_TAC EVENTS_INTER ++ RW_TAC std_ss []
            ++ `count (n + 1) = {0} UNION count_mn 1 n` 
    		by (PSET_TAC [count_def, count_mn_def, EXTENSION] ++ RW_TAC arith_ss [])
            ++ POP_ORW 
            ++ RW_TAC std_ss [IMAGE_UNION, BIGINTER_UNION, IMAGE_SING, BIGINTER_SING],

            MATCH_MP_TAC EVENTS_INTER ++ RW_TAC std_ss []
            ++ MATCH_MP_TAC EVENTS_COUNTABLE_INTER 
            ++ `{0} UNION count_mn 2 n <> {}` 
           	by (PSET_TAC [IN_UNION, count_mn_def, EXTENSION]
        		++ Q.EXISTS_TAC `0` ++ RW_TAC std_ss []) 
            ++ PSET_TAC [IN_COUNT_MN] 
            << [METIS_TAC [DTMC_EVENTS],
                METIS_TAC [DTMC_EVENTS],
                MATCH_MP_TAC COUNTABLE_IMAGE 
                ++ MATCH_MP_TAC COUNTABLE_SUBSET
                ++ Q.EXISTS_TAC `count (n + 1)` 
                ++ PSET_TAC [COUNTABLE_COUNT, count_mn_def, count_def] 
                ++ RW_TAC arith_ss [],
                PSET_TAC [IMAGE_EQ_EMPTY, EMPTY_UNION, NOT_SING_EMPTY]]])
 ++ `1 <= m /\ m <= n` by RW_TAC arith_ss []
 ++ FIRST_ASSUM (MP_TAC o GSYM o Q.SPECL [`X`, `Y`, `p`, `s`, `s1`, `Linit`, `Ltrans`, `Btrans`, 
 	`t`, `n`, `Lx`, `Ly`]) ++ RW_TAC std_ss [REAL_MUL_ASSOC] ++ NTAC 3 (POP_ASSUM K_TAC)
 ++ `BIGINTER (IMAGE (\(k:num). (\k. PREIMAGE (Y (t + k)) {EL k Ly} INTER p_space p) k)
                	(count (m + 1))) IN events p`
       by (`count (m + 1) = count_mn 0 m` 
       		by PSET_TAC [count_def, count_mn_def, EXTENSION, LE_LT1] ++ POP_ORW
          ++ MATCH_MP_TAC EVENTS_BIGINTER_MN ++ RW_TAC arith_ss []
          >> (Cases_on `EL k Ly NOTIN (space s1)`
             >> (`PREIMAGE (Y (k + t)) {EL k Ly} INTER p_space p = {}` 
    		by (MATCH_MP_TAC NOTIN_SPACE_EVENTS 
    	   	   ++ Q.EXISTS_TAC `s1` ++ PSET_TAC [thmm_def, hmm_def])
    	        ++ METIS_TAC [EVENTS_EMPTY]) 
          ++ METIS_TAC [thmm_def, hmm_def, PREIMAGE_X_IN_EVENTS]))
 ++ MP_RW_TAC COND_PROB_INTER_SPLIT 
 >> (RW_TAC std_ss []
    << [Cases_on `EL (m + 1) Ly NOTIN (space s1)`
        >> (`PREIMAGE (Y (t + (m + 1))) {EL (m + 1) Ly} INTER p_space p = {}` 
    		by (MATCH_MP_TAC NOTIN_SPACE_EVENTS 
    	   ++ Q.EXISTS_TAC `s1` ++ PSET_TAC [thmm_def, hmm_def])
    	++ METIS_TAC [EVENTS_EMPTY])
        ++ METIS_TAC [thmm_def, hmm_def, PREIMAGE_X_IN_EVENTS],
        
        RW_TAC std_ss [GSYM ADD1]
        ++ `BIGINTER (IMAGE (\k. PREIMAGE (Y (t + k)) {EL k Ly} INTER p_space p) (count (SUC m))) =
     		BIGINTER (IMAGE (\k. (\k. PREIMAGE (Y (t + k)) {EL k Ly} INTER p_space p) k) 
     		(count (SUC m)))` by RW_TAC std_ss [] ++ POP_ORW
        ++ MATCH_MP_TAC EVENTS_BIGINTER ++ RW_TAC std_ss [IN_FUNSET]
        ++ Cases_on `EL k Ly NOTIN (space s1)`
        >> (`PREIMAGE (Y (t + k)) {EL k Ly} INTER p_space p = {}` 
    		by (MATCH_MP_TAC NOTIN_SPACE_EVENTS 
    	           ++ Q.EXISTS_TAC `s1` ++ PSET_TAC [thmm_def, hmm_def])
    	   ++ METIS_TAC [EVENTS_EMPTY])
        ++ METIS_TAC [thmm_def, hmm_def, PREIMAGE_X_IN_EVENTS],
        
        RW_TAC std_ss [GSYM ADD1]
        ++ `BIGINTER (IMAGE (\k. PREIMAGE (X (t + k)) {EL k Lx} INTER p_space p) (count (SUC n))) =
     		BIGINTER (IMAGE (\k. (\k. PREIMAGE (X (t + k)) {EL k Lx} INTER p_space p) k) 
     		(count (SUC n)))` by RW_TAC std_ss [] ++ POP_ORW
        ++ MATCH_MP_TAC EVENTS_BIGINTER ++ RW_TAC std_ss [IN_FUNSET]
        ++ METIS_TAC [thmm_def, hmm_def, DTMC_EVENTS]])
    
 ++ Cases_on `prob p (BIGINTER (IMAGE (\k. PREIMAGE (Y (t + k)) {EL k Ly} INTER p_space p)
            (count (m + 1))) INTER  
     BIGINTER (IMAGE (\k. PREIMAGE (X (t + k)) {EL k Lx} INTER p_space p) (count (n + 1)))) = 0`
 >> ((MP_TAC o Q.SPECL [`p`, 
        `BIGINTER (IMAGE (\k. PREIMAGE (Y (t + k)) {EL k (Ly:'c list)} INTER p_space p) 
        	(count (m + 1)))`,
   	`BIGINTER (IMAGE (\k. PREIMAGE (X (t + k)) {EL k (Lx:'b list)} INTER p_space p) 
   		(count (n + 1)))`]) COND_PROB_ZERO_INTER 
       ++ RW_TAC std_ss [EVENTS_INTER, REAL_MUL_LZERO, REAL_MUL_RZERO])
 ++ `!(a:real) b c. (a = c) ==> (a * b = b * c)` by RW_TAC std_ss [REAL_MUL_COMM] 
 ++ POP_ASSUM MATCH_MP_TAC 
 ++ `BIGINTER (IMAGE (\k. PREIMAGE (X (t + k)) {EL k Lx} INTER p_space p) (count (n + 1))) =
     	PREIMAGE (X (t + m + 1)) {EL (m + 1) Lx} INTER p_space p INTER
     	BIGINTER (IMAGE (\k. PREIMAGE (X (t + k)) {EL k Lx} INTER p_space p) 
     	(count (n + 1) DIFF {m + 1}))`
     	by (`count (n + 1) = {m + 1} UNION (count (n + 1) DIFF {m + 1})`
     		by (PSET_TAC [count_def, EXTENSION] ++ RW_TAC arith_ss [])
           ++ `BIGINTER (IMAGE (\k. PREIMAGE (X (t + k)) {EL k Lx} INTER p_space p) 
        	(count (n + 1))) =
            BIGINTER (IMAGE (\k. PREIMAGE (X (t + k)) {EL k Lx} INTER p_space p) 
        	({m + 1} UNION (count (n + 1) DIFF {m + 1})))` by METIS_TAC []
           ++ POP_ORW ++ POP_ASSUM K_TAC
           ++ RW_TAC std_ss [IMAGE_UNION, BIGINTER_UNION, IMAGE_SING, BIGINTER_SING, 
        	GSYM INTER_ASSOC, ADD_ASSOC]) ++ POP_ORW
 ++ Cases_on `EL (m + 1) Ly NOTIN (space s1)`
 >> (`PREIMAGE (Y (t + m + 1)) {EL (m + 1) Ly} INTER p_space p = {}`
 	by (MATCH_MP_TAC NOTIN_SPACE_EVENTS 
    	   ++ Q.EXISTS_TAC `s1` ++ PSET_TAC [thmm_def, hmm_def])
    	++ RW_TAC std_ss [ADD_ASSOC, cond_prob_def, INTER_EMPTY, PROB_EMPTY, REAL_DIV_LZERO])
 ++ `!A B C D. A INTER (B INTER C INTER D) = B INTER C INTER (A INTER D)` 
 	by METIS_TAC [INTER_ASSOC, INTER_COMM] ++ POP_ORW    	
 ++ Suff `prob p (BIGINTER (IMAGE (\k. PREIMAGE (Y (t + k)) {EL k Ly} INTER p_space p)
             (count (m + 1))) INTER 
             BIGINTER (IMAGE (\k. PREIMAGE (X (t + k)) {EL k Lx} INTER p_space p)
             (count (n + 1) DIFF {m + 1}))) <> 0`
 >> (`t + (m + 1) NOTIN {t + r | r IN count (m + 1)}`
 		by (PSET_TAC [IN_COUNT, EXTENSION] ++ RW_TAC arith_ss [])
    ++ `t + (m + 1) NOTIN {t + r | r IN count (n + 1) DIFF {m + 1}}`
        	by PSET_TAC [IN_COUNT, EXTENSION] 		
    ++ FULL_SIMP_TAC std_ss [thmm_def, hmm_def] ++ NTAC 17 (POP_ASSUM MP_TAC)
    ++ POP_ASSUM (MP_TAC o Q.SPECL [`EL (m + 1) Ly`, `EL (m + 1) Lx`, `t + (m + 1)`, `t`, 
    		`t`, `Lx`, `Ly`, `count (n + 1) DIFF {m + 1}`, `count (m + 1)`]) 
    ++ RW_TAC std_ss [GSYM INTER_ASSOC, ADD_ASSOC])
              
 ++ MATCH_MP_TAC PROB_SUBSET_NZ
 ++ Q.EXISTS_TAC `BIGINTER (IMAGE (\k. PREIMAGE (Y (t + k)) {EL k Ly} INTER p_space p)
          (count (m + 1))) INTER  
   	   BIGINTER (IMAGE (\k. PREIMAGE (X (t + k)) {EL k Lx} INTER p_space p) (count (n + 1)))` 
 ++ RW_TAC std_ss []
 << [MATCH_MP_TAC INTER_SUBSET_INTER
    ++ MATCH_MP_TAC BIGINTER_SUBSET_BIGINTER
    ++ RW_TAC std_ss [DIFF_SUBSET],
      	     
    MATCH_MP_TAC EVENTS_INTER ++ RW_TAC std_ss [],
  	     
    MATCH_MP_TAC EVENTS_INTER ++ RW_TAC std_ss []
    ++ MATCH_MP_TAC EVENTS_COUNTABLE_INTER 
    ++ `count (n + 1) DIFF {m + 1} <> {}` 
    	   by (PSET_TAC [count_def, EXTENSION]
    	      ++ Q.EXISTS_TAC `m` ++ RW_TAC arith_ss []) 
    ++ PSET_TAC [IN_COUNT]
    << [METIS_TAC [thmm_def, hmm_def, DTMC_EVENTS],
        MATCH_MP_TAC COUNTABLE_IMAGE
        ++ MATCH_MP_TAC COUNTABLE_SUBSET
        ++ Q.EXISTS_TAC `count (n + 1)` 
        ++ PSET_TAC [COUNTABLE_COUNT, count_def], 
        RW_TAC std_ss [IMAGE_EQ_EMPTY, EMPTY_UNION, NOT_SING_EMPTY]]]);
           	 
(* ------------------------------------------------------------------------- *)
(* Theorem 4: Joint Probability of HMM                                       *)
(* ------------------------------------------------------------------------- *)
val HMM_JOINT_PROB = store_thm
  ("HMM_JOINT_PROB",  
  ``!X Y p s s1 Linit Ltrans (Btrans: num -> 'c -> 'b -> real) t n (Lx:'b list) (Ly:'c list).
    thmm X Y p s s1 Linit Ltrans Btrans ==>
   (prob p (BIGINTER (IMAGE (\(k:num). PREIMAGE (X (t + k)) {EL k Lx} INTER p_space p)
                	(count (n + 1))) INTER 
            BIGINTER (IMAGE (\(k:num). PREIMAGE (Y (t + k)) {EL k Ly} INTER p_space p)
                	(count (n + 1)))) =
    prob p (PREIMAGE (X t) {EL 0 Lx} INTER p_space p) * 
    cond_prob p (PREIMAGE (Y t) {EL 0 Ly} INTER p_space p)
                        (PREIMAGE (X t) {EL 0 Lx} INTER p_space p) *
    mulcon (0, n) (\k. cond_prob p (PREIMAGE (X (t + k + 1)) {EL (k + 1) Lx} INTER p_space p)
                        (PREIMAGE (X (t + k)) {EL k Lx} INTER p_space p) *
                        cond_prob p (PREIMAGE (Y (t + k + 1)) {EL (k + 1) Ly} INTER p_space p)
                        (PREIMAGE (X (t + k + 1)) {EL (k + 1) Lx} INTER p_space p)))``,
    RW_TAC std_ss [] 
 ++ `prob_space p` by FULL_SIMP_TAC std_ss [thmm_def, hmm_def, random_variable_def]
 ++ Cases_on `n = 0`
 >> (RW_TAC std_ss [mulcon_def, REAL_MUL_RID, COUNT_ONE, IMAGE_SING, BIGINTER_SING]
    ++ Cases_on `EL 0 Ly NOTIN (space s1)`
    >> (`PREIMAGE (Y t) {EL 0 Ly} INTER p_space p = {}`
    	by (MATCH_MP_TAC NOTIN_SPACE_EVENTS ++ Q.EXISTS_TAC `s1` 
       		   ++ PSET_TAC [thmm_def, hmm_def, dtmc_def, mc_property_def])
       ++ RW_TAC std_ss [INTER_EMPTY, cond_prob_def, PROB_EMPTY, REAL_DIV_LZERO, real_div,
       		REAL_MUL_RZERO, REAL_MUL_LZERO])
    ++ Cases_on `EL 0 Lx NOTIN (space s)`
    >> (`PREIMAGE (X t) {EL 0 Lx} INTER p_space p = {}`
    	by (MATCH_MP_TAC NOTIN_SPACE_EVENTS ++ Q.EXISTS_TAC `s` 
       		   ++ PSET_TAC [thmm_def, hmm_def, dtmc_def, mc_property_def])
       ++ RW_TAC std_ss [INTER_EMPTY, cond_prob_def, PROB_EMPTY, REAL_DIV_LZERO, real_div,
       		REAL_MUL_RZERO, REAL_MUL_LZERO])
    ++ Q.ABBREV_TAC `A = PREIMAGE (X t) {EL 0 Lx} INTER p_space p`
    ++ Q.ABBREV_TAC `B = PREIMAGE (Y t) {EL 0 Ly} INTER p_space p`
    ++ ONCE_REWRITE_TAC [INTER_COMM] 
    ++ MATCH_MP_TAC COND_PROB_MUL_RULE
    ++ MAP_EVERY Q.UNABBREV_TAC [`A`, `B`]
    ++ METIS_TAC [thmm_def, hmm_def, DTMC_EVENTS, PREIMAGE_X_IN_EVENTS])
 ++ `1 <= n` by RW_TAC arith_ss []
 ++ RW_TAC std_ss [GSYM MULCON_SPLIT] 
 ++ `!(a:real) b c d. a * b * (c * d) = c * a * (b * d)` 
 	by METIS_TAC [REAL_MUL_ASSOC, REAL_MUL_COMM] ++ POP_ORW
 ++ `dtmc X p s Linit Ltrans` by PSET_TAC [thmm_def, hmm_def, th_dtmc_def]
 ++ PSET_TAC [IN_COUNT, GSYM LE_LT1]
 ++ (MP_TAC o GSYM o Q.SPECL [`X`, `p`, `s`, `t`, `n`, `Lx`, `Linit`, `Ltrans`])
 	 MC_JOINT_PROB          
 ++ RW_TAC std_ss [COND_PMF_EQ_COND_PROB, distribution_def] 
 ++ `prob_space p` by FULL_SIMP_TAC std_ss [thmm_def, hmm_def, random_variable_def]  
 ++ `BIGINTER (IMAGE (\(k:num). (\k. PREIMAGE (X (t + k)) {EL k Lx} INTER p_space p) k)
                	(count (n + 1))) IN events p`
       by (`count (n + 1) = count_mn 0 n` 
       		by PSET_TAC [count_def, count_mn_def, GSPECIFICATION, EXTENSION, LE_LT1] ++ POP_ORW
          ++ MATCH_MP_TAC EVENTS_BIGINTER_MN ++ RW_TAC std_ss [] 
          ++ Cases_on `EL k Lx NOTIN space s` 
          >> (`PREIMAGE (X (t + k)) {EL k Lx} INTER p_space p = {}`
    		by (MATCH_MP_TAC NOTIN_SPACE_EVENTS ++ Q.EXISTS_TAC `s` 
       		   ++ PSET_TAC [thmm_def, hmm_def, dtmc_def, mc_property_def])
             ++ METIS_TAC [EVENTS_EMPTY]) ++ METIS_TAC [thmm_def, hmm_def, DTMC_EVENTS])
 ++ POP_ASSUM MP_TAC ++ RW_TAC std_ss []   
 ++ `BIGINTER (IMAGE (\(k:num). (\k. PREIMAGE (Y (t + k)) {EL k Ly} INTER p_space p) k)
                	(count (n + 1))) IN events p`
       by (`count (n + 1) = count_mn 0 n` 
       		by PSET_TAC [count_def, count_mn_def, GSPECIFICATION, EXTENSION, LE_LT1] ++ POP_ORW
          ++ MATCH_MP_TAC EVENTS_BIGINTER_MN ++ RW_TAC std_ss []
          ++ Cases_on `EL k Ly NOTIN space s1` 
          >> (`PREIMAGE (Y (t + k)) {EL k Ly} INTER p_space p = {}`
    		by (MATCH_MP_TAC NOTIN_SPACE_EVENTS ++ Q.EXISTS_TAC `s1` 
       		   ++ PSET_TAC [thmm_def, hmm_def, dtmc_def, mc_property_def])
             ++ METIS_TAC [EVENTS_EMPTY]) ++ METIS_TAC [thmm_def, hmm_def, PREIMAGE_X_IN_EVENTS]) 
 ++ POP_ASSUM MP_TAC ++ RW_TAC std_ss []  
 ++ Cases_on `prob p (BIGINTER (IMAGE (\k. PREIMAGE (X (t + k)) {EL k Lx} INTER p_space p)
            (count (n + 1)))) = 0`
 >> ((MP_TAC o Q.SPECL [`p`, 
   	`BIGINTER (IMAGE (\k. PREIMAGE (X (t + k)) {EL k (Lx:'b list)} INTER p_space p) 
   		(count (n + 1)))`,
   	`BIGINTER (IMAGE (\k. PREIMAGE (Y (t + k)) {EL k (Ly:'c list)} INTER p_space p) 
   	(count (n + 1)))`]) PROB_ZERO_INTER ++ RW_TAC std_ss [REAL_MUL_LZERO])
 ++ (MP_TAC o GSYM o Q.SPECL [`X`, `Y`, `p`, `s`, `s1`, `Linit`, `Ltrans`, `Btrans`, `t`, 
 	`n`, `n`, `Lx`, `Ly`]) PRE_HMM_JOINT_PROB ++ RW_TAC std_ss []
 ++ METIS_TAC [INTER_COMM, COND_PROB_MUL_RULE]); 

(* ------------------------------------------------------------------------- *)
(* Theorem : Joint Probability of Observation Sequence of a HMM              *)
(* ------------------------------------------------------------------------- *)
val HMM_OBS_SEQ_PROB = store_thm
  ("HMM_OBS_SEQ_PROB",   
  ``!X Y p s s1 Linit Ltrans (Btrans: num -> 'c -> 'b -> real) t n (Ly:'c list).
   thmm X Y p s s1 Linit Ltrans Btrans ==>
   (prob p (BIGINTER (IMAGE (\(k:num). PREIMAGE (Y (t + k)) {EL k Ly} INTER p_space p)
                	(count (n + 1)))) =
    SIGMA (\Lx. prob p (PREIMAGE (X t) {EL 0 Lx} INTER p_space p) * 
    	       cond_prob p (PREIMAGE (Y t) {EL 0 Ly} INTER p_space p)
                           (PREIMAGE (X t) {EL 0 Lx} INTER p_space p) *
    	       mulcon (0, n) (\k. 
    	       		      cond_prob p (PREIMAGE (X (t + k + 1)) {EL (k + 1) Lx} INTER p_space p)
                                          (PREIMAGE (X (t + k)) {EL k Lx} INTER p_space p) *
                              cond_prob p (PREIMAGE (Y (t + k + 1)) {EL (k + 1) Ly} INTER p_space p)
                        	          (PREIMAGE (X (t + k + 1)) {EL (k + 1) Lx} INTER p_space p)))
           {L | EVERY (\x. x IN space s) L /\ (LENGTH L = n + 1)})``,
    RW_TAC std_ss []
 ++ `prob_space p` by FULL_SIMP_TAC std_ss [thmm_def, hmm_def, random_variable_def]
 ++ `FINITE (space s)` by FULL_SIMP_TAC std_ss [thmm_def] 
 ++ `BIGINTER (IMAGE (\k. (\k. PREIMAGE (Y (t + k)) {EL k Ly} INTER p_space p) k) 
 	(count (n + 1))) IN events p`
       by (`count (n + 1) = count_mn 0 n` 
       		by PSET_TAC [ADD1, count_def, count_mn_def, GSPECIFICATION, EXTENSION, LE_LT1] 
          ++ POP_ORW ++ MATCH_MP_TAC EVENTS_BIGINTER_MN ++ RW_TAC std_ss []
          ++ Cases_on `EL k Ly NOTIN space s1` 
          >> (`PREIMAGE (Y (t + k)) {EL k Ly} INTER p_space p = {}`
    		by (MATCH_MP_TAC NOTIN_SPACE_EVENTS ++ Q.EXISTS_TAC `s1` 
       		   ++ PSET_TAC [thmm_def, hmm_def, dtmc_def, mc_property_def])
             ++ METIS_TAC [EVENTS_EMPTY]) 
          ++ METIS_TAC [thmm_def, hmm_def, PREIMAGE_X_IN_EVENTS]) 
 ++ POP_ASSUM MP_TAC ++ RW_TAC std_ss []
 ++ `!x. x IN {L | EVERY (\x. x IN space s) L /\ (LENGTH L = n + 1)} ==> 
 	(BIGINTER (IMAGE (\k. PREIMAGE (Y (t + k)) {EL k Ly} INTER p_space p) (count (n + 1))) INTER
 	(\L. BIGINTER (IMAGE (\k. PREIMAGE (X (t + k)) {EL k L} INTER p_space p) (count (n + 1)))) x) 
 	IN events p` 
  	by (PSET_TAC [GSYM ADD1, EVERY_EL, GSYM COUNT_MN_COUNT] ++ MATCH_MP_TAC EVENTS_INTER 
  	   ++ RW_TAC std_ss [] 
  	   ++ `BIGINTER (IMAGE (\k. PREIMAGE (X (t + k)) {EL k x} INTER p_space p) 
  	   		(count_mn 0 n)) =
  	       BIGINTER (IMAGE (\k. (\k. PREIMAGE (X (t + k)) {EL k x} INTER p_space p) k)
  	   		(count_mn 0 n))` by RW_TAC std_ss [] ++ POP_ORW
  	   ++ MATCH_MP_TAC EVENTS_BIGINTER_MN ++ RW_TAC std_ss [] 
  	   ++ `k < LENGTH x` by RW_TAC arith_ss []
  	   ++ METIS_TAC [thmm_def, hmm_def, th_dtmc_def, DTMC_EVENTS]) 
 ++ `!x y. x IN {L | EVERY (\x. x IN space s) L /\ (LENGTH L = n + 1)} /\
           y IN {L | EVERY (\x. x IN space s) L /\ (LENGTH L = n + 1)} /\ x <> y ==>
     DISJOINT (BIGINTER (IMAGE (\k. PREIMAGE (X (t + k)) {EL k x} INTER p_space p) (count (n + 1))))
              (BIGINTER (IMAGE (\k. PREIMAGE (X (t + k)) {EL k y} INTER p_space p) (count (n + 1))))` 
  	by (PSET_TAC [DISJOINT_DEF, INTER_BIGINTER]
  	   ++ `?k. k < n + 1 /\ EL k x <> EL k y` 
  	   	by (SPOSE_NOT_THEN STRIP_ASSUME_TAC ++ METIS_TAC [LIST_EQ])
  	   ++ `count (n + 1) = {k} UNION (count (n + 1) DIFF {k})` 
  	   	by (PSET_TAC [DIFF_DEF, UNION_DEF, count_def, EXTENSION] ++ RW_TAC arith_ss [])
  	   ++ POP_ORW ++ RW_TAC std_ss [IMAGE_UNION, BIGINTER_UNION, IMAGE_SING, BIGINTER_SING]
  	   ++ METIS_TAC [DISJOINT_PROC_INTER, DISJOINT_DEF, INTER_EMPTY])
 ++ Suff `(BIGUNION (IMAGE (\L. BIGINTER (IMAGE (\k. PREIMAGE (X (t + k)) {EL k L} INTER p_space p)
                        (count (n + 1))))
             {L | EVERY (\x. x IN space s) L /\ (LENGTH L = n + 1)}) INTER p_space p = p_space p)`
 >> ((MP_TAC o Q.SPECL [`p`, 
 	`(\L. BIGINTER (IMAGE (\k. PREIMAGE (X (t + k)) {EL k L} INTER p_space p) (count (n + 1))))`, 
 	`BIGINTER (IMAGE (\k. PREIMAGE (Y (t + k)) {EL k (Ly:'c list)} INTER p_space p) 
 		(count (n + 1)))`,
 	`{L | EVERY (\x. x IN space s) L /\ (LENGTH L = n + 1)}`] 
 	o INST_TYPE [``:'b`` |-> ``:'b list``]) PROB_REAL_SUM_IMAGE_FN 
 	++ RW_TAC std_ss [FINITE_RND_PATH_SET]
     ++ MATCH_MP_TAC REAL_SUM_IMAGE_EQ ++ RW_TAC std_ss [FINITE_RND_PATH_SET]
     ++ `!k. k <= n ==> EL k x IN space s`
        by (POP_ASSUM MP_TAC ++ NTAC 5 (POP_ASSUM K_TAC) ++ PSET_TAC [EVERY_EL] 
           ++ FULL_SIMP_TAC arith_ss [])
     ++ METIS_TAC [HMM_JOINT_PROB, INTER_COMM]) ++ NTAC 3 (POP_ASSUM K_TAC)
 ++ POP_ASSUM MP_TAC ++ POP_ASSUM K_TAC ++ DISCH_TAC
 ++ Induct_on `n`
 >> (RW_TAC std_ss [COUNT_ONE, IMAGE_SING, BIGINTER_SING]
    ++ `IMAGE (\L. PREIMAGE (X t) {EL 0 L} INTER p_space p) 
    		{L | EVERY (\x. x IN space s) L /\ (LENGTH L = 1)} =
    	IMAGE (\x. PREIMAGE (X t) {x} INTER p_space p) (space s)`
    	by (PSET_TAC [IMAGE_DEF, EXTENSION] ++ EQ_TAC
    	   >> (RW_TAC std_ss [] ++ Q.EXISTS_TAC `EL 0 (L:'b list)` ++ FULL_SIMP_TAC std_ss [EVERY_EL])
    	   ++ RW_TAC std_ss [LENGTH_ONE] ++ Q.EXISTS_TAC `[x']` ++ RW_TAC std_ss [EVERY_EL, EL, HD]
    	   ++ `LENGTH [x'] = 1` by RW_TAC std_ss [LENGTH_ONE]    	      	
    	   ++ `n = 0` by RW_TAC arith_ss [] ++ RW_TAC std_ss [EL, HD])
     ++ POP_ORW ++ FULL_SIMP_TAC std_ss [thmm_def, hmm_def, dtmc_def, mc_property_def,
     			 BIGUNION_PREIMAGEX_IS_PSPACE, INTER_IDEMPOT])
 ++ PSET_TAC [EXTENSION, IN_BIGUNION_IMAGE, IN_BIGINTER_IMAGE] ++ FULL_SIMP_TAC arith_ss []
 ++ EQ_TAC >> RW_TAC std_ss [] ++ RW_TAC std_ss []
 ++ `(?L.
             (EVERY (\x. x IN space s) L /\ (LENGTH L = n + 1)) /\
             !k. k < n + 1 ==> (X (k + t) x = EL k L) /\ x IN p_space p) /\
          x IN p_space p` by FULL_SIMP_TAC std_ss []
 ++ Q.EXISTS_TAC `L ++ [X (SUC n + t) x]` ++ RW_TAC std_ss [EVERY_APPEND, EVERY_DEF]
 << [PSET_TAC [thmm_def, hmm_def, dtmc_def, mc_property_def, random_variable_def, 
 	IN_MEASURABLE, space_def],
    RW_TAC std_ss [LENGTH_APPEND, LENGTH, ADD1],
    Cases_on `k = SUC n` >> (RW_TAC std_ss [ADD1, EL_APPEND2] ++ RW_TAC std_ss [EL, HD])
    ++ `k < n + 1` by RW_TAC arith_ss [] ++ FULL_SIMP_TAC std_ss [EL_APPEND1]]); 

(* ------------------------------------------------------------------------- *)
(* Theorem 5: Joint Probability of State Path of a HMM                       *)
(* ------------------------------------------------------------------------- *)
val HMM_STATE_PATH_PROB = store_thm
  ("HMM_STATE_PATH_PROB",  
  ``!X Y p s s1 Linit Ltrans (Btrans: num -> 'c -> 'b -> real) t n (Lx:'b list).
   thmm X Y p s s1 Linit Ltrans Btrans ==>
   (prob p (BIGINTER (IMAGE (\(k:num). PREIMAGE (X (t + k)) {EL k Lx} INTER p_space p)
                	(count (n + 1)))) =
    SIGMA (\Ly. prob p (PREIMAGE (X t) {EL 0 Lx} INTER p_space p) * 
    	       cond_prob p (PREIMAGE (Y t) {EL 0 Ly} INTER p_space p)
                           (PREIMAGE (X t) {EL 0 Lx} INTER p_space p) *
    	       mulcon (0, n) (\k. 
    	       		      cond_prob p (PREIMAGE (X (t + k + 1)) {EL (k + 1) Lx} INTER p_space p)
                                          (PREIMAGE (X (t + k)) {EL k Lx} INTER p_space p) *
                              cond_prob p (PREIMAGE (Y (t + k + 1)) {EL (k + 1) Ly} INTER p_space p)
                        	          (PREIMAGE (X (t + k + 1)) {EL (k + 1) Lx} INTER p_space p)))
           {L | EVERY (\y. y IN space s1) L /\ (LENGTH L = n + 1)})``,
    RW_TAC std_ss []
 ++ `prob_space p` by FULL_SIMP_TAC std_ss [thmm_def, hmm_def, random_variable_def]
 ++ `FINITE (space s1)` by FULL_SIMP_TAC std_ss [thmm_def, hmm_def]
 ++ `BIGINTER (IMAGE (\k. (\k. PREIMAGE (Y (t + k)) {EL k Ly} INTER p_space p) k) 
 	(count (n + 1))) IN events p`
       by (`count (n + 1) = count_mn 0 n` 
       		by PSET_TAC [ADD1, count_def, count_mn_def, GSPECIFICATION, EXTENSION, LE_LT1] 
          ++ POP_ORW ++ MATCH_MP_TAC EVENTS_BIGINTER_MN ++ RW_TAC std_ss []
          ++ Cases_on `EL k Ly NOTIN space s1` 
          >> (`PREIMAGE (Y (t + k)) {EL k Ly} INTER p_space p = {}`
    		by (MATCH_MP_TAC NOTIN_SPACE_EVENTS ++ Q.EXISTS_TAC `s1` 
       		   ++ PSET_TAC [thmm_def, hmm_def, dtmc_def, mc_property_def])
             ++ METIS_TAC [EVENTS_EMPTY]) 
          ++ METIS_TAC [thmm_def, hmm_def, PREIMAGE_X_IN_EVENTS]) 
 ++ POP_ASSUM MP_TAC ++ RW_TAC std_ss []          
 ++ `!x. x IN {L | EVERY (\x. x IN space s1) L /\ (LENGTH L = n + 1)} ==> 
 	(BIGINTER (IMAGE (\k. PREIMAGE (X (t + k)) {EL k Lx} INTER p_space p) (count (n + 1))) INTER
 	(\L. BIGINTER (IMAGE (\k. PREIMAGE (Y (t + k)) {EL k L} INTER p_space p) (count (n + 1)))) x) 
 	IN events p` 
  	by (PSET_TAC [GSYM ADD1, EVERY_EL, GSYM COUNT_MN_COUNT] ++ MATCH_MP_TAC EVENTS_INTER 
  	   ++ RW_TAC std_ss []
  	   >> (`BIGINTER (IMAGE (\k. PREIMAGE (X (t + k)) {EL k Lx} INTER p_space p) 
  	   		(count_mn 0 n)) =
  	       BIGINTER (IMAGE (\k. (\k. PREIMAGE (X (t + k)) {EL k Lx} INTER p_space p) k)
  	   		(count_mn 0 n))` by RW_TAC std_ss [] ++ POP_ORW
  	      ++ MATCH_MP_TAC EVENTS_BIGINTER_MN ++ RW_TAC std_ss []
  	      ++ METIS_TAC [thmm_def, hmm_def, DTMC_EVENTS])  
  	   ++ `BIGINTER (IMAGE (\k. PREIMAGE (Y (t + k)) {EL k x} INTER p_space p) 
  	   		(count_mn 0 n)) =
  	       BIGINTER (IMAGE (\k. (\k. PREIMAGE (Y (t + k)) {EL k x} INTER p_space p) k)
  	   		(count_mn 0 n))` by RW_TAC std_ss [] ++ POP_ORW
  	   ++ MATCH_MP_TAC EVENTS_BIGINTER_MN ++ RW_TAC std_ss [] 
  	   ++ `k < LENGTH x` by RW_TAC arith_ss []
  	   ++ Cases_on `EL k x NOTIN space s1` 
           >> (`PREIMAGE (Y (t + k)) {EL k x} INTER p_space p = {}`
    			by (MATCH_MP_TAC NOTIN_SPACE_EVENTS ++ Q.EXISTS_TAC `s1` 
       		           ++ PSET_TAC [thmm_def, hmm_def, dtmc_def, mc_property_def])
              ++ METIS_TAC [EVENTS_EMPTY]) 
           ++ METIS_TAC [thmm_def, hmm_def, PREIMAGE_X_IN_EVENTS]) 
 ++ `!x y. x IN {L | EVERY (\x. x IN space s1) L /\ (LENGTH L = n + 1)} /\
           y IN {L | EVERY (\x. x IN space s1) L /\ (LENGTH L = n + 1)} /\ x <> y ==>
     DISJOINT (BIGINTER (IMAGE (\k. PREIMAGE (Y (t + k)) {EL k x} INTER p_space p) (count (n + 1))))
              (BIGINTER (IMAGE (\k. PREIMAGE (Y (t + k)) {EL k y} INTER p_space p) (count (n + 1))))` 
  	by (PSET_TAC [DISJOINT_DEF, INTER_BIGINTER]
  	   ++ `?k. k < n + 1 /\ EL k x <> EL k y` 
  	   	by (SPOSE_NOT_THEN STRIP_ASSUME_TAC ++ METIS_TAC [LIST_EQ])
  	   ++ `count (n + 1) = {k} UNION (count (n + 1) DIFF {k})` 
  	   	by (PSET_TAC [DIFF_DEF, UNION_DEF, count_def, EXTENSION] ++ RW_TAC arith_ss [])
  	   ++ POP_ORW ++ RW_TAC std_ss [IMAGE_UNION, BIGINTER_UNION, IMAGE_SING, BIGINTER_SING]
  	   ++ METIS_TAC [DISJOINT_PROC_INTER, DISJOINT_DEF, INTER_EMPTY])
 ++ `BIGINTER (IMAGE (\(k:num). (\k. PREIMAGE (X (t + k)) {EL k Lx} INTER p_space p) k)
                	(count (n + 1))) IN events p`
       by (`count (n + 1) = count_mn 0 n` 
       		by PSET_TAC [count_def, count_mn_def, GSPECIFICATION, EXTENSION, LE_LT1] ++ POP_ORW
          ++ MATCH_MP_TAC EVENTS_BIGINTER_MN ++ RW_TAC std_ss [] 
          ++ Cases_on `EL k Lx NOTIN space s` 
          >> (`PREIMAGE (X (t + k)) {EL k Lx} INTER p_space p = {}`
    		by (MATCH_MP_TAC NOTIN_SPACE_EVENTS ++ Q.EXISTS_TAC `s` 
       		   ++ PSET_TAC [thmm_def, hmm_def, dtmc_def, mc_property_def])
             ++ METIS_TAC [EVENTS_EMPTY]) ++ METIS_TAC [thmm_def, hmm_def, DTMC_EVENTS])
 ++ POP_ASSUM MP_TAC ++ RW_TAC std_ss []    	   
 ++ Suff `(BIGUNION (IMAGE (\L. BIGINTER (IMAGE (\k. PREIMAGE (Y (t + k)) {EL k L} INTER p_space p)
                        (count (n + 1))))
             {L | EVERY (\x. x IN space s1) L /\ (LENGTH L = n + 1)}) INTER p_space p = p_space p)`
 >> ((MP_TAC o Q.SPECL [`p`, 
 	`(\(L:'c list). BIGINTER (IMAGE (\k. PREIMAGE (Y (t + k)) {EL k L} INTER p_space p) 
 		(count (n + 1))))`, 
 	`BIGINTER (IMAGE (\k. PREIMAGE (X (t + k)) {EL k (Lx:'b list)} INTER p_space p) 
 		(count (n + 1)))`,
 	`{L | EVERY (\x. x IN space s1) L /\ (LENGTH L = n + 1)}`] 
 	o INST_TYPE [``:'b`` |-> ``:'c list``]) PROB_REAL_SUM_IMAGE_FN 
 	++ RW_TAC std_ss [FINITE_RND_PATH_SET]
     ++ MATCH_MP_TAC REAL_SUM_IMAGE_EQ ++ RW_TAC std_ss [FINITE_RND_PATH_SET]
     ++ `!k. k <= n ==> EL k x IN space s1`
        by (POP_ASSUM MP_TAC ++ NTAC 5 (POP_ASSUM K_TAC) ++ PSET_TAC [EVERY_EL] 
           ++ FULL_SIMP_TAC arith_ss [])
     ++ METIS_TAC [HMM_JOINT_PROB, INTER_COMM]) 
 ++ NTAC 4 (POP_ASSUM K_TAC) 
 ++ Induct_on `n`
 >> (RW_TAC std_ss [COUNT_ONE, IMAGE_SING, BIGINTER_SING]
    ++ `IMAGE (\L. PREIMAGE (Y t) {EL 0 L} INTER p_space p) 
    		{L | EVERY (\x. x IN space s1) L /\ (LENGTH L = 1)} =
    	IMAGE (\x. PREIMAGE (Y t) {x} INTER p_space p) (space s1)`
    	by (PSET_TAC [IMAGE_DEF, EXTENSION] ++ EQ_TAC
    	   >> (RW_TAC std_ss [] ++ Q.EXISTS_TAC `EL 0 (L:'c list)` ++ FULL_SIMP_TAC std_ss [EVERY_EL])
    	   ++ RW_TAC std_ss [LENGTH_ONE] ++ Q.EXISTS_TAC `[x']` ++ RW_TAC std_ss [EVERY_EL, EL, HD]
    	   ++ `LENGTH [x'] = 1` by RW_TAC std_ss [LENGTH_ONE]    	      	
    	   ++ `n = 0` by RW_TAC arith_ss [] ++ RW_TAC std_ss [EL, HD]) ++ POP_ORW 
     ++ FULL_SIMP_TAC std_ss [thmm_def, hmm_def, BIGUNION_PREIMAGEX_IS_PSPACE, INTER_IDEMPOT])
 ++ PSET_TAC [EXTENSION, IN_BIGUNION_IMAGE, IN_BIGINTER_IMAGE] ++ FULL_SIMP_TAC arith_ss []
 ++ EQ_TAC >> RW_TAC std_ss [] ++ RW_TAC std_ss []
 ++ `(?L. (EVERY (\x. x IN space s1) L /\ (LENGTH L = n + 1)) /\
             !k. k < n + 1 ==> (Y (k + t) x = EL k L) /\ x IN p_space p) /\
          x IN p_space p` by FULL_SIMP_TAC std_ss []
 ++ Q.EXISTS_TAC `L ++ [Y (SUC n + t) x]` ++ RW_TAC std_ss [EVERY_APPEND, EVERY_DEF]
 ++ PSET_TAC [thmm_def, hmm_def, random_variable_def, IN_MEASURABLE, space_def]
 ++ RW_TAC std_ss [LENGTH_APPEND, LENGTH, ADD1]
 ++ Cases_on `k = SUC n` >> (RW_TAC std_ss [ADD1, EL_APPEND2] ++ RW_TAC std_ss [EL, HD])
 ++ `k < n + 1` by RW_TAC arith_ss [] ++ FULL_SIMP_TAC std_ss [EL_APPEND1]);
     
val REAL_SUM_IMAGE_SUBSET = prove
  (``!f s t. FINITE s /\ t SUBSET s /\ 
	(!i. i IN (s DIFF t) ==> (f i = (0:real))) ==> (SIGMA f s = SIGMA f t)``,
    RW_TAC std_ss []
 ++ `s = t UNION (s DIFF t)` by PSET_TAC [UNION_DIFF]   
 ++ POP_ORW ++ DEP_REWRITE_TAC [REAL_SUM_IMAGE_DISJOINT_UNION]
 ++ RW_TAC std_ss [(UNDISCH o Q.SPEC `s`) SUBSET_FINITE, FINITE_DIFF, 
 	DISJOINT_DIFF, REAL_ADD_RID_UNIQ]
 ++ (MP_TAC o Q.SPEC `s DIFF t`) (GSYM REAL_SUM_IMAGE_0)
 ++ RW_TAC std_ss [FINITE_DIFF] ++ POP_ORW
 ++ MATCH_MP_TAC REAL_SUM_IMAGE_EQ
 ++ PSET_TAC [FINITE_DIFF, IN_DIFF]);

val MULCON_EQ_MUL_TWO = store_thm
  ("MULCON_EQ_MUL_TWO",
  ``!f m n p. mulcon (m, n + p) f = mulcon (m, p) f * mulcon (m + p, n) f``,
    Induct_on `n` 
 >> RW_TAC std_ss [mulcon_def, REAL_MUL_RID]
 ++ RW_TAC std_ss [ADD, mulcon_def]
 ++ METIS_TAC [ADD_COMM, ADD_ASSOC, REAL_MUL_ASSOC]);

val MULCON_EQ_ZERO = prove
  (``!f n. (?t. t < n /\ (f t = 0)) ==> (mulcon (0, n) f = 0)``,
    RW_TAC std_ss []
 ++ `SUC t <= n` by RW_TAC arith_ss []   
 ++ `?p. n = (SUC t) + p` by METIS_TAC [LESS_EQ_EXISTS]   
 ++ POP_ORW 
 ++ RW_TAC std_ss [GSYM MULCON_TWO, mulcon_def, REAL_MUL_RZERO, REAL_MUL_LZERO]);

val HMM_MULCON_0 = prove
  (``!X Y p s s1 Linit Ltrans (Btrans: num -> 'c -> 'b -> real) t n (Ly:'c list) Lx r.
   thmm X Y p s s1 Linit Ltrans Btrans /\ r < n /\ 
   (Btrans (t + r) (EL r Ly) (EL r Lx) = 0) ==>
   (prob p (PREIMAGE (X t) {EL 0 Lx} INTER p_space p) *
         cond_prob p (PREIMAGE (Y t) {EL 0 Ly} INTER p_space p)
           (PREIMAGE (X t) {EL 0 Lx} INTER p_space p) *
         mulcon (0,n)
           (\k.
              cond_prob p
                (PREIMAGE (X (t + k + 1)) {EL (k + 1) Lx} INTER p_space p)
                (PREIMAGE (X (t + k)) {EL k Lx} INTER p_space p) *
              cond_prob p
                (PREIMAGE (Y (t + k + 1)) {EL (k + 1) Ly} INTER p_space p)
                (PREIMAGE (X (t + k + 1)) {EL (k + 1) Lx} INTER p_space p)) = 0)``,
    RW_TAC std_ss []
 ++ `!t a i. distribution p (X t) {i} <> 0 ==>
            (Btrans t a i = cond_prob p (PREIMAGE (Y t) {a} INTER p_space p)
               (PREIMAGE (X t) {i} INTER p_space p))` by FULL_SIMP_TAC std_ss [thmm_def, hmm_def] 
 ++ `prob_space p` by FULL_SIMP_TAC std_ss [thmm_def, hmm_def, random_variable_def]                  
 ++ Cases_on `r = 0`
 >> (RW_TAC std_ss [] 
    ++ Cases_on `distribution p (X t) {EL 0 Lx} = 0`
    >> PSET_TAC [distribution_def, REAL_MUL_LZERO]
    ++ NTAC 2 (POP_ASSUM MP_TAC)
    ++ POP_ASSUM (MP_TAC o GSYM o Q.SPECL [`t`, `EL 0 (Ly:'c list)`, `EL 0 (Lx:'b list)`]) 
    ++ RW_TAC arith_ss [] 
    ++ FULL_SIMP_TAC std_ss [REAL_MUL_RZERO, REAL_MUL_LZERO])       
 ++ Suff `mulcon (0,n) (\k.
              cond_prob p
                (PREIMAGE (X (t + k + 1)) {EL (k + 1) Lx} INTER p_space p)
                (PREIMAGE (X (t + k)) {EL k Lx} INTER p_space p) *
              cond_prob p
                (PREIMAGE (Y (t + k + 1)) {EL (k + 1) Ly} INTER p_space p)
                (PREIMAGE (X (t + k + 1)) {EL (k + 1) Lx} INTER p_space p)) = 0`
 >> RW_TAC std_ss [REAL_MUL_RZERO]  
 ++ `?p. n = r + p` by METIS_TAC [LESS_IMP_LESS_OR_EQ, GSYM LE_LT1, LESS_EQ_EXISTS] 
 ++ `0 < p'` by RW_TAC arith_ss []
 ++ RW_TAC std_ss [GSYM MULCON_TWO]
 ++ `r = r - 1 + 1` by RW_TAC arith_ss [] ++ POP_ORW		
 ++ RW_TAC arith_ss [GSYM MULCON_TWO, MULCON_1]
 ++ Cases_on `distribution p (X (t + r)) {EL r Lx} = 0`
 >> (`cond_prob p (PREIMAGE (Y (t + r)) {EL r Ly} INTER p_space p)
       (PREIMAGE (X (t + r)) {EL r Lx} INTER p_space p) = 0`
       by (MATCH_MP_TAC COND_PROB_ZERO 
          ++ RW_TAC std_ss []
          << [Cases_on `EL r Ly NOTIN (space s1)`
              >> (`PREIMAGE (Y (t + r)) {EL r Ly} INTER p_space p = {}`
       			by (MATCH_MP_TAC NOTIN_SPACE_EVENTS ++ Q.EXISTS_TAC `s1` 
       		           ++ PSET_TAC [thmm_def, hmm_def, dtmc_def, mc_property_def])
       		 ++ METIS_TAC [EVENTS_EMPTY])
              ++ METIS_TAC [thmm_def, hmm_def, PREIMAGE_X_IN_EVENTS],
              Cases_on `EL r Lx NOTIN (space s)`
              >> (`PREIMAGE (X (t + r)) {EL r Lx} INTER p_space p = {}`
       			by (MATCH_MP_TAC NOTIN_SPACE_EVENTS ++ Q.EXISTS_TAC `s` 
       		   	   ++ PSET_TAC [thmm_def, hmm_def, dtmc_def, mc_property_def])
       		 ++ METIS_TAC [EVENTS_EMPTY])
              ++ METIS_TAC [thmm_def, hmm_def, DTMC_EVENTS],
              PSET_TAC [distribution_def]])
    ++ ONCE_REWRITE_TAC [ADD_COMM]
    ++ RW_TAC std_ss [REAL_MUL_RZERO, REAL_MUL_LZERO])
 ++ `r + t = t + r` by RW_TAC arith_ss []    
 ++ NTAC 5 (POP_ASSUM MP_TAC)
 ++ POP_ASSUM (MP_TAC o GSYM o Q.SPECL [`r + t`, `EL r (Ly:'c list)`,
 	`EL r (Lx:'b list)`]) ++ RW_TAC std_ss []
 ++ FULL_SIMP_TAC arith_ss [REAL_MUL_RZERO, REAL_MUL_LZERO]);
 
val REAL_SUM_IMAGE_FUN_0 = prove
  (``!f s. FINITE s /\ (!x. x IN s ==> (f x = 0)) ==> 
  	(SIGMA f s = (0:real))``,
    RW_TAC std_ss []
 ++ (MP_TAC o UNDISCH o Q.SPEC `s` o GSYM) REAL_SUM_IMAGE_0
 ++ RW_TAC std_ss [] ++ POP_ORW
 ++ MATCH_MP_TAC REAL_SUM_IMAGE_EQ
 ++ RW_TAC std_ss []);

val HMM_OBS_SIMP_PROB = store_thm
  ("HMM_OBS_SIMP_PROB",   
  ``!X Y p s s1 Linit Ltrans (Btrans: num -> 'c -> 'b -> real) t n (Ly:'c list).
   thmm X Y p s s1 Linit Ltrans Btrans ==>
   (prob p (BIGINTER (IMAGE (\(k:num). PREIMAGE (Y (t + k)) {EL k Ly} INTER p_space p)
                	(count (n + 1)))) =
    SIGMA (\Lx. prob p (PREIMAGE (X t) {EL 0 Lx} INTER p_space p) * 
    	       cond_prob p (PREIMAGE (Y t) {EL 0 Ly} INTER p_space p)
                           (PREIMAGE (X t) {EL 0 Lx} INTER p_space p) *
    	       mulcon (0, n) (\k. 
    	       		   cond_prob p (PREIMAGE (X (t + k + 1)) {EL (k + 1) Lx} INTER p_space p)
                                       (PREIMAGE (X (t + k)) {EL k Lx} INTER p_space p) *
                           cond_prob p (PREIMAGE (Y (t + k + 1)) {EL (k + 1) Ly} INTER p_space p)
                                       (PREIMAGE (X (t + k + 1)) {EL (k + 1) Lx} INTER p_space p)))
           {L | EVERY (\x. x IN space s) L /\ (LENGTH L = n + 1) /\ 
           	!m. m < n ==> Btrans (t + m) (EL m Ly) (EL m L) <> 0})``,
    RW_TAC std_ss []
 ++ `prob_space p` by FULL_SIMP_TAC std_ss [thmm_def, hmm_def, random_variable_def]
 ++ `FINITE (space s)` by FULL_SIMP_TAC std_ss [thmm_def, hmm_def, th_dtmc_def]
 ++ MP_RW_TAC HMM_OBS_SEQ_PROB
 >> RW_TAC std_ss []
 ++ MATCH_MP_TAC (GSYM REAL_SUM_IMAGE_SUBSET_0)
 ++ RW_TAC std_ss [FINITE_RND_PATH_SET]
 >> PSET_TAC []
 ++ MATCH_MP_TAC (GSYM REAL_SUM_IMAGE_FUN_0)
 ++ PSET_TAC [FINITE_DIFF, FINITE_RND_PATH_SET]
 ++ Cases_on `m = 0`
 >> (RW_TAC std_ss []
    ++ Cases_on `distribution p (X t) {EL 0 x} = 0`
    >> PSET_TAC [distribution_def, REAL_MUL_LZERO]
    ++ `EL 0 x IN space s` by (SPOSE_NOT_THEN STRIP_ASSUME_TAC
    	++ METIS_TAC [thmm_def, hmm_def, dtmc_def, mc_property_def, NOTIN_SPACE_EVENTS, 
    		distribution_def, PROB_EMPTY])
    ++ Cases_on `EL 0 Ly NOTIN space s1`
    >> METIS_TAC [thmm_def, hmm_def, NOTIN_SPACE_EVENTS, cond_prob_def, INTER_EMPTY, PROB_EMPTY,
    		 REAL_DIV_LZERO, REAL_MUL_RZERO, REAL_MUL_LZERO]
    ++ `cond_prob p (PREIMAGE (Y t) {EL 0 Ly} INTER p_space p)
       (PREIMAGE (X t) {EL 0 x} INTER p_space p) = Btrans t (EL 0 Ly) (EL 0 x)` 
       by METIS_TAC [thmm_def, hmm_def] ++ POP_ORW
    ++ FULL_SIMP_TAC arith_ss [REAL_MUL_RZERO, REAL_MUL_LZERO])
 ++ `?p. n = m + p` by METIS_TAC [LESS_IMP_LESS_OR_EQ, GSYM LE_LT1, LESS_EQ_EXISTS] 
 ++ `0 < p'` by RW_TAC arith_ss []
 ++ RW_TAC std_ss [GSYM MULCON_TWO]
 ++ `m - 1 + 1 = m` by RW_TAC arith_ss []      		
 ++ `m = (m - 1) + 1` by RW_TAC arith_ss [] ++ POP_ORW
 ++ RW_TAC std_ss [GSYM MULCON_TWO, MULCON_1]
 ++ `t + (m - 1) + 1 = t + m` by RW_TAC arith_ss [] ++ POP_ORW
 ++ Cases_on `distribution p (X (t + m)) {EL m x} = 0`
 >> PSET_TAC [distribution_def, cond_prob_def, real_div, REAL_INV_0, REAL_MUL_LZERO, REAL_MUL_RZERO]
 ++ `EL m x IN space s` by (SPOSE_NOT_THEN STRIP_ASSUME_TAC
    	++ METIS_TAC [thmm_def, hmm_def, dtmc_def, mc_property_def, NOTIN_SPACE_EVENTS, 
    		distribution_def, PROB_EMPTY])
 ++ Cases_on `EL m Ly NOTIN space s1`
 >> METIS_TAC [thmm_def, hmm_def, NOTIN_SPACE_EVENTS, cond_prob_def, INTER_EMPTY, PROB_EMPTY,
    		 REAL_DIV_LZERO, REAL_MUL_RZERO, REAL_MUL_LZERO]    		
 ++ `cond_prob p (PREIMAGE (Y (t + m)) {EL m Ly} INTER p_space p)
       (PREIMAGE (X (t + m)) {EL m x} INTER p_space p) = Btrans (t + m) (EL m Ly) (EL m x)` 
       by METIS_TAC [thmm_def, hmm_def] ++ POP_ORW
 ++ FULL_SIMP_TAC std_ss [REAL_MUL_RZERO, REAL_MUL_LZERO]);
                     	
val HMM_X = store_thm
  ("HMM_X",   
  ``!X Y p s s1 Linit Ltrans (Btrans: num -> 'c -> 'b -> real) t n (Lx:'b list) (Ly:'c list).
   thmm X Y p s s1 Linit Ltrans Btrans ==>
   (prob p ((PREIMAGE (X (t + n + 1)) {EL (n + 1) Lx} INTER p_space p) INTER
            BIGINTER (IMAGE (\(k:num). PREIMAGE (X (t + k)) {EL k Lx} INTER p_space p)
                	(count (n + 1))) INTER 
            BIGINTER (IMAGE (\(k:num). PREIMAGE (Y (t + k)) {EL k Ly} INTER p_space p)
                	(count (n + 1)))) =
    SIGMA (\i. prob p ((PREIMAGE (X (t + n + 1)) {EL (n + 1) Lx} INTER p_space p) INTER
    		(PREIMAGE (Y (t + n + 1)) {i} INTER p_space p) INTER
            BIGINTER (IMAGE (\(k:num). PREIMAGE (X (t + k)) {EL k Lx} INTER p_space p)
                	(count (n + 1))) INTER 
            BIGINTER (IMAGE (\(k:num). PREIMAGE (Y (t + k)) {EL k Ly} INTER p_space p)
                	(count (n + 1))))) (space s1))``,
    RW_TAC std_ss []  
 ++ `prob_space p` by PSET_TAC [thmm_def, hmm_def, dtmc_def, mc_property_def,
 	 random_variable_def] 
 ++ `FINITE (space s)` by PSET_TAC [thmm_def, hmm_def, dtmc_def] 	   
 ++ `!A B C D E. A INTER B INTER (C INTER B) INTER D INTER E =
          A INTER B INTER D INTER E INTER (C INTER B)` by METIS_TAC [INTER_ASSOC, INTER_COMM]
 ++ POP_ORW
 ++ Cases_on `EL (n + 1) Lx NOTIN space s`
 >> (`PREIMAGE (X (t + n + 1)) {EL (n + 1) Lx} INTER p_space p = {}`
 	by METIS_TAC [thmm_def, hmm_def, dtmc_def, mc_property_def, NOTIN_SPACE_EVENTS]
    ++ RW_TAC std_ss [INTER_EMPTY, PROB_EMPTY]
    ++ MATCH_MP_TAC (GSYM REAL_SUM_IMAGE_0)
    ++ PSET_TAC [thmm_def, hmm_def])
 ++ Cases_on `?m. m IN count (n + 1) /\ EL m Lx NOTIN space s`
 >> (PSET_TAC [IN_COUNT]
    ++ `BIGINTER (IMAGE (\k. PREIMAGE (X (t + k)) {EL k Lx} INTER p_space p)
       		(count (n + 1))) SUBSET (\k. PREIMAGE (X (t + k)) {EL k Lx} INTER p_space p) m` 
                by (MATCH_MP_TAC BIGINTER_SUBSET_SING ++ RW_TAC std_ss [IN_COUNT])    
    ++ `PREIMAGE (X (t + m)) {EL m Lx} INTER p_space p = {}`
       		by (MATCH_MP_TAC NOTIN_SPACE_EVENTS ++ Q.EXISTS_TAC `s` 
       		   ++ PSET_TAC [thmm_def, hmm_def, dtmc_def, mc_property_def])
    ++ `PREIMAGE (X (t + n + 1)) {EL (n + 1) Lx} INTER p_space p INTER
       BIGINTER (IMAGE (\k. PREIMAGE (X (t + k)) {EL k Lx} INTER p_space p)
            (count (n + 1))) INTER
       BIGINTER (IMAGE (\k. PREIMAGE (Y (t + k)) {EL k Ly} INTER p_space p)
            (count (n + 1))) = {}`
      		by FULL_SIMP_TAC std_ss [SUBSET_EMPTY, INTER_EMPTY] 
    ++ PSET_TAC [INTER_EMPTY, PROB_EMPTY, thmm_def, hmm_def, REAL_SUM_IMAGE_0])
 ++ Cases_on `?m. m IN count (n + 1) /\ EL m Ly NOTIN space s1`   	
 >> (PSET_TAC [IN_COUNT]
    ++ `BIGINTER (IMAGE (\k. PREIMAGE (Y (t + k)) {EL k Ly} INTER p_space p)
       		(count (n + 1))) SUBSET (\k. PREIMAGE (Y (t + k)) {EL k Ly} INTER p_space p) m` 
                by (MATCH_MP_TAC BIGINTER_SUBSET_SING ++ RW_TAC std_ss [IN_COUNT])     
    ++ `PREIMAGE (Y (t + m)) {EL m Ly} INTER p_space p = {}`
       		by (MATCH_MP_TAC NOTIN_SPACE_EVENTS ++ Q.EXISTS_TAC `s1` 
       		   ++ PSET_TAC [thmm_def, hmm_def, dtmc_def, mc_property_def])
    ++ `PREIMAGE (X (t + n + 1)) {EL (n + 1) Lx} INTER p_space p INTER
       BIGINTER (IMAGE (\k. PREIMAGE (X (t + k)) {EL k Lx} INTER p_space p)
            (count (n + 1))) INTER
       BIGINTER (IMAGE (\k. PREIMAGE (Y (t + k)) {EL k Ly} INTER p_space p)
            (count (n + 1))) = {}`
      		by FULL_SIMP_TAC std_ss [SUBSET_EMPTY, INTER_EMPTY]       		   
    ++ PSET_TAC [INTER_EMPTY, PROB_EMPTY, thmm_def, hmm_def, REAL_SUM_IMAGE_0]) 
 ++ `SIGMA (\i. prob p (PREIMAGE (X (t + n + 1)) {EL (n + 1) Lx} INTER p_space p INTER
            BIGINTER (IMAGE (\k. PREIMAGE (X (t + k)) {EL k Lx} INTER p_space p)
                 (count (n + 1))) INTER
            BIGINTER (IMAGE (\k. PREIMAGE (Y (t + k)) {EL k Ly} INTER p_space p)
                 (count (n + 1))) INTER
            (PREIMAGE (Y (t + n + 1)) {i} INTER p_space p))) (space s1) =
     SIGMA (\i. prob p (PREIMAGE (X (t + n + 1)) {EL (n + 1) Lx} INTER p_space p INTER
            BIGINTER (IMAGE (\k. PREIMAGE (X (t + k)) {EL k Lx} INTER p_space p)
                 (count (n + 1))) INTER
            BIGINTER (IMAGE (\k. PREIMAGE (Y (t + k)) {EL k Ly} INTER p_space p)
                 (count (n + 1))) INTER
            (\i. PREIMAGE (Y (t + n + 1)) {i} INTER p_space p) i)) (space s1)` 
        by RW_TAC std_ss [] ++ POP_ORW
 ++ MATCH_MP_TAC PROB_REAL_SUM_IMAGE_FN 
 ++ `PREIMAGE (X (t + n + 1)) {EL (n + 1) Lx} INTER p_space p INTER
    BIGINTER (IMAGE (\k. PREIMAGE (X (t + k)) {EL k Lx} INTER p_space p) (count (n + 1))) INTER
    BIGINTER (IMAGE (\k. PREIMAGE (Y (t + k)) {EL k Ly} INTER p_space p) (count (n + 1))) 
    	IN events p`
    	by (MATCH_MP_TAC EVENTS_INTER ++ RW_TAC std_ss []
           >> (MATCH_MP_TAC EVENTS_INTER ++ RW_TAC std_ss []
              >> METIS_TAC [thmm_def, hmm_def, DTMC_EVENTS]
              ++ `BIGINTER (IMAGE (\k. PREIMAGE (X (t + k)) {EL k Lx} INTER p_space p) (
              		count (n + 1))) = 
              	  BIGINTER (IMAGE (\k. (\k. PREIMAGE (X (t + k)) {EL k Lx} INTER p_space p) k)
                	(count (n + 1)))` by RW_TAC std_ss [] ++ POP_ORW
              ++ `count (n + 1) = count_mn 0 n` 
       			by PSET_TAC [count_def, count_mn_def, GSPECIFICATION, EXTENSION, LE_LT1] 
       	      ++ POP_ORW ++ MATCH_MP_TAC EVENTS_BIGINTER_MN 
       	      ++ PSET_TAC [thmm_def, hmm_def, random_variable_def]
              ++ `EL k Lx IN space s` by METIS_TAC [LE_LT1] 
              ++ METIS_TAC [thmm_def, hmm_def, DTMC_EVENTS])
           ++ `BIGINTER (IMAGE (\k. PREIMAGE (Y (t + k)) {EL k Ly} INTER p_space p) 
              		(count (n + 1))) =
               BIGINTER (IMAGE (\(k:num). (\k. PREIMAGE (Y (t + k)) {EL k Ly} INTER p_space p) k)
                 	(count (n + 1)))` by RW_TAC std_ss [] ++ POP_ORW
           ++ `count (n + 1) = count_mn 0 n` 
         		by PSET_TAC [count_def, count_mn_def, GSPECIFICATION, EXTENSION, LE_LT1] 
           ++ POP_ORW ++ MATCH_MP_TAC EVENTS_BIGINTER_MN ++ RW_TAC std_ss []
           ++ `EL k Ly IN space s1` by METIS_TAC [IN_COUNT, LE_LT1] 
           ++ METIS_TAC [thmm_def, hmm_def, PREIMAGE_X_IN_EVENTS])
 ++ PSET_TAC [thmm_def, hmm_def]        	
 << [Q.ABBREV_TAC `A = PREIMAGE (X (t + n + 1)) {EL (n + 1) Lx} INTER p_space p INTER
           BIGINTER (IMAGE (\k. PREIMAGE (X (t + k)) {EL k Lx} INTER p_space p)
           	 (count (n + 1))) INTER
           BIGINTER (IMAGE (\k. PREIMAGE (Y (t + k)) {EL k Ly} INTER p_space p)
                (count (n + 1)))` ++ MATCH_MP_TAC EVENTS_INTER ++ RW_TAC std_ss []
     ++ METIS_TAC [thmm_def, hmm_def, PREIMAGE_X_IN_EVENTS],
     RW_TAC std_ss [(REWRITE_RULE [DISJOINT_DEF]) DISJOINT_PROC_INTER],
     RW_TAC std_ss [BIGUNION_PREIMAGEX_IS_PSPACE, INTER_IDEMPOT]]);    

val IMAGE_EQ = prove
  (``!f g s. (!i. i IN s ==> (f i = g i)) ==> (IMAGE f s = IMAGE g s)``,
   PSET_TAC [IMAGE_DEF, EXTENSION] ++ METIS_TAC []);

val HMM_Y = store_thm
  ("HMM_Y",   
  ``!X Y p s s1 Linit Ltrans (Btrans: num -> 'c -> 'b -> real) t n (Lx:'b list) (Ly:'c list).
   thmm X Y p s s1 Linit Ltrans Btrans /\ (LENGTH Ly = n + 1) ==>
   (SIGMA (\i. prob p ((PREIMAGE (X (t + n + 1)) {EL (n + 1) Lx} INTER p_space p) INTER
    		(PREIMAGE (Y (t + n + 1)) {i} INTER p_space p) INTER
            BIGINTER (IMAGE (\(k:num). PREIMAGE (X (t + k)) {EL k Lx} INTER p_space p)
                	(count (n + 1))) INTER 
            BIGINTER (IMAGE (\(k:num). PREIMAGE (Y (t + k)) {EL k Ly} INTER p_space p)
                	(count (n + 1))))) (space s1) =
    SIGMA (\i. prob p (PREIMAGE (X t) {EL 0 Lx} INTER p_space p) * 
    cond_prob p (PREIMAGE (Y t) {EL 0 Ly} INTER p_space p)
                        (PREIMAGE (X t) {EL 0 Lx} INTER p_space p) *
    mulcon (0, n) (\k. cond_prob p (PREIMAGE (X (t + k + 1)) {EL (k + 1) Lx} INTER p_space p)
                        (PREIMAGE (X (t + k)) {EL k Lx} INTER p_space p) *
                        cond_prob p (PREIMAGE (Y (t + k + 1)) {EL (k + 1) Ly} INTER p_space p)
                        (PREIMAGE (X (t + k + 1)) {EL (k + 1) Lx} INTER p_space p)) *
    cond_prob p (PREIMAGE (X (t + n + 1)) {EL (n + 1) Lx} INTER p_space p)
                        (PREIMAGE (X (t + n)) {EL n Lx} INTER p_space p) *
    (\i. cond_prob p (PREIMAGE (Y (t + n + 1)) {i} INTER p_space p)
                     (PREIMAGE (X (t + n + 1)) {EL (n + 1) Lx} INTER p_space p)) i) (space s1))``,
    RW_TAC std_ss []
 ++ `FINITE (space s1)` by PSET_TAC [thmm_def, hmm_def]
 ++ `prob_space p` by PSET_TAC [thmm_def, hmm_def, random_variable_def] 
 ++ MATCH_MP_TAC REAL_SUM_IMAGE_EQ ++ RW_TAC std_ss []
 ++ Cases_on `EL (n + 1) Lx NOTIN space s`
 >> (`PREIMAGE (X (t + n + 1)) {EL (n + 1) Lx} INTER p_space p = {}`
 	by METIS_TAC [thmm_def, hmm_def, dtmc_def, mc_property_def, NOTIN_SPACE_EVENTS]
    ++ RW_TAC std_ss [INTER_EMPTY, PROB_EMPTY, cond_prob_def, INTER_EMPTY, 
    	PROB_EMPTY, REAL_DIV_LZERO, REAL_MUL_LZERO, REAL_MUL_RZERO])
 ++ Cases_on `?m. m IN count (n + 1) /\ EL m Lx NOTIN space s`
 >> (PSET_TAC [IN_COUNT]
    ++ `BIGINTER (IMAGE (\k. PREIMAGE (X (t + k)) {EL k Lx} INTER p_space p)
       		(count (n + 1))) SUBSET (\k. PREIMAGE (X (t + k)) {EL k Lx} INTER p_space p) m` 
                by (MATCH_MP_TAC BIGINTER_SUBSET_SING ++ RW_TAC std_ss [IN_COUNT])    
    ++ `PREIMAGE (X (t + m)) {EL m Lx} INTER p_space p = {}`
       		by (MATCH_MP_TAC NOTIN_SPACE_EVENTS ++ Q.EXISTS_TAC `s` 
       		   ++ PSET_TAC [thmm_def, hmm_def, dtmc_def, mc_property_def])
    ++ `BIGINTER (IMAGE (\k. PREIMAGE (X (t + k)) {EL k Lx} INTER p_space p)
            (count (n + 1))) = {}`
      		by FULL_SIMP_TAC std_ss [SUBSET_EMPTY] 
    ++ Cases_on `m = n`
    >> RW_TAC std_ss [cond_prob_def, INTER_EMPTY, PROB_EMPTY, real_div, REAL_INV_0, 
    		REAL_MUL_RZERO, REAL_MUL_LZERO]
    ++ Cases_on `m = 0`
    >> FULL_SIMP_TAC arith_ss [INTER_EMPTY, PROB_EMPTY, REAL_MUL_LZERO]
    ++ `?p. n = m + p` by METIS_TAC [LESS_IMP_LESS_OR_EQ, GSYM LE_LT1, LESS_EQ_EXISTS] 
    ++ `0 < p'` by RW_TAC arith_ss []
    ++ RW_TAC std_ss [GSYM MULCON_TWO]
    ++ `m - 1 + 1 = m` by RW_TAC arith_ss []      		
    ++ `m = (m - 1) + 1` by RW_TAC arith_ss [] ++ POP_ORW
    ++ RW_TAC std_ss [GSYM MULCON_TWO, MULCON_1]
    ++ `t + (m - 1) + 1 = t + m` by RW_TAC arith_ss [] ++ POP_ORW
    ++ RW_TAC std_ss [cond_prob_def, INTER_EMPTY, PROB_EMPTY, real_div, REAL_INV_0, 
    		REAL_MUL_RZERO, REAL_MUL_LZERO])
 ++ Cases_on `?m. m IN count (n + 1) /\ EL m Ly NOTIN space s1`   	
 >> (PSET_TAC [IN_COUNT]
    ++ `BIGINTER (IMAGE (\k. PREIMAGE (Y (t + k)) {EL k Ly} INTER p_space p)
       		(count (n + 1))) SUBSET (\k. PREIMAGE (Y (t + k)) {EL k Ly} INTER p_space p) m` 
                by (MATCH_MP_TAC BIGINTER_SUBSET_SING ++ RW_TAC std_ss [IN_COUNT])     
    ++ `PREIMAGE (Y (t + m)) {EL m Ly} INTER p_space p = {}`
       		by (MATCH_MP_TAC NOTIN_SPACE_EVENTS ++ Q.EXISTS_TAC `s1` 
       		   ++ PSET_TAC [thmm_def, hmm_def, dtmc_def, mc_property_def])
    ++ `BIGINTER (IMAGE (\k. PREIMAGE (Y (t + k)) {EL k Ly} INTER p_space p)
            (count (n + 1))) = {}` by FULL_SIMP_TAC std_ss [SUBSET_EMPTY] 
    ++ Cases_on `m = 0`
    >> FULL_SIMP_TAC arith_ss [cond_prob_def, INTER_EMPTY, PROB_EMPTY, REAL_DIV_LZERO,
    		REAL_MUL_RZERO, REAL_MUL_LZERO]  
    ++ FULL_SIMP_TAC std_ss [INTER_EMPTY, PROB_EMPTY]         
    ++ Cases_on `m = n`
    >> (`n = SUC (n - 1)` by RW_TAC arith_ss [] ++ POP_ORW
       ++ `(m - 1) + 1 = m` by RW_TAC arith_ss []
       ++ RW_TAC std_ss [mulcon_def, GSYM ADD_ASSOC, cond_prob_def, INTER_EMPTY, PROB_EMPTY, 
       		REAL_DIV_LZERO,	REAL_MUL_RZERO, REAL_MUL_LZERO])
    ++ `?p. n = m + p` by METIS_TAC [LESS_IMP_LESS_OR_EQ, GSYM LE_LT1, LESS_EQ_EXISTS] 
    ++ `0 < p'` by RW_TAC arith_ss []
    ++ RW_TAC std_ss [GSYM MULCON_TWO]
    ++ `m = SUC (m - 1)` by RW_TAC arith_ss [] ++ POP_ORW
    ++ `m - 1 + 1 = m` by RW_TAC arith_ss []      		
    ++ `t + (m - 1) + 1 = t + m` by RW_TAC arith_ss [] 
    ++ RW_TAC std_ss [mulcon_def, cond_prob_def, INTER_EMPTY, PROB_EMPTY, 
    		REAL_DIV_LZERO,	REAL_MUL_RZERO, REAL_MUL_LZERO])
 ++ `PREIMAGE (X (t + n + 1)) {EL (n + 1) Lx} INTER p_space p INTER
       (PREIMAGE (Y (t + n + 1)) {x} INTER p_space p) INTER
     BIGINTER (IMAGE (\k. PREIMAGE (X (t + k)) {EL k Lx} INTER p_space p) (count (n + 1))) INTER
     BIGINTER (IMAGE (\k. PREIMAGE (Y (t + k)) {EL k Ly} INTER p_space p) (count (n + 1))) =
     BIGINTER (IMAGE (\k. PREIMAGE (X (t + k)) {EL k Lx} INTER p_space p) (count (n + 2))) INTER
     BIGINTER (IMAGE (\k. PREIMAGE (Y (t + k)) {EL k (Ly ++ [x])} INTER p_space p) 
     	(count (n + 2)))`
     by (`count (n + 2) = {n + 1} UNION count (n + 1)` 
     		by (PSET_TAC [IN_COUNT, EXTENSION] ++ RW_TAC arith_ss []) ++ POP_ORW
     	++ FULL_SIMP_TAC std_ss []
     	++ `EL (n + 1) (Ly ++ [x]) = x` by RW_TAC std_ss [EL_APPEND2, EL, HD]
        ++ RW_TAC std_ss [IMAGE_UNION, BIGINTER_UNION, IMAGE_SING, BIGINTER_SING]     	
     	++ `IMAGE (\k. PREIMAGE (Y (t + k)) {EL k (Ly ++ [x])} INTER p_space p) (count (n + 1)) =
	    IMAGE (\k. PREIMAGE (Y (t + k)) {EL k Ly} INTER p_space p) (count (n + 1))`
	    by (MATCH_MP_TAC IMAGE_EQ ++ RW_TAC std_ss [IN_COUNT, EL_APPEND1]) ++ POP_ORW
	++ RW_TAC std_ss [ADD_ASSOC]
	++ `!A B C D E. A INTER B INTER (C INTER B) INTER D INTER E =
	    A INTER B INTER D INTER (C INTER B INTER E)` by METIS_TAC [INTER_ASSOC, INTER_COMM]
        ++ RW_TAC std_ss []) ++ POP_ORW
 ++ (MP_TAC o Q.SPECL [`X`, `Y`, `p`, `s`, `s1`, `Linit`, `Ltrans`, `Btrans`, `t`, `n + 1`,
 	`Lx`, `Ly ++ [x]`]) HMM_JOINT_PROB ++ RW_TAC arith_ss []
 ++ `EL 0 [x] = x` by RW_TAC std_ss [EL, HD] 
 ++ RW_TAC arith_ss [GSYM ADD1, mulcon_def, EL_APPEND1, EL_APPEND2]
 ++ `!(a:real) b c d e f. (c = f) ==> (a * b * (c * (d * e)) = a * b * f * d * e)`
 	by (RW_TAC std_ss [] ++ METIS_TAC [REAL_MUL_ASSOC, REAL_MUL_COMM])
 ++ POP_ASSUM MATCH_MP_TAC ++ MATCH_MP_TAC MULCON_POS_EQ ++ RW_TAC std_ss []
 ++ `!(a:real) b c. (a = b) ==> (c * a = c * b)` by RW_TAC std_ss []
 ++ POP_ASSUM MATCH_MP_TAC
 ++ Suff `EL (SUC r) (Ly ++ [x]) = EL (SUC r) Ly` >> RW_TAC std_ss []
 ++ RW_TAC arith_ss [EL_APPEND1]);

val HMM_SUCX_PROB = store_thm
  ("HMM_SUCX_PROB",   
  ``!X Y p s s1 Linit Ltrans (Btrans: num -> 'c -> 'b -> real) t n (Lx:'b list) (Ly:'c list).
   thmm X Y p s s1 Linit Ltrans Btrans /\ (LENGTH Ly = n + 1) ==>
   (prob p (BIGINTER (IMAGE (\(k:num). PREIMAGE (X (t + k)) {EL k Lx} INTER p_space p)
                	(count (n + 2))) INTER 
            BIGINTER (IMAGE (\(k:num). PREIMAGE (Y (t + k)) {EL k Ly} INTER p_space p)
                	(count (n + 1)))) =
    prob p (PREIMAGE (X t) {EL 0 Lx} INTER p_space p) * 
    cond_prob p (PREIMAGE (Y t) {EL 0 Ly} INTER p_space p)
                        (PREIMAGE (X t) {EL 0 Lx} INTER p_space p) *
    mulcon (0, n) (\k. cond_prob p (PREIMAGE (X (t + k + 1)) {EL (k + 1) Lx} INTER p_space p)
                        (PREIMAGE (X (t + k)) {EL k Lx} INTER p_space p) *
                        cond_prob p (PREIMAGE (Y (t + k + 1)) {EL (k + 1) Ly} INTER p_space p)
                        (PREIMAGE (X (t + k + 1)) {EL (k + 1) Lx} INTER p_space p)) *
    cond_prob p (PREIMAGE (X (t + n + 1)) {EL (n + 1) Lx} INTER p_space p)
                        (PREIMAGE (X (t + n)) {EL n Lx} INTER p_space p))``,
    RW_TAC std_ss [] 
 ++ `prob_space p` by FULL_SIMP_TAC std_ss [thmm_def, hmm_def, random_variable_def] 
 ++ `count (n + 2) = {n + 1} UNION count (n + 1)` 
 	by (PSET_TAC [IN_COUNT, EXTENSION] ++ RW_TAC arith_ss []) ++ POP_ORW
 ++ PSET_TAC [IMAGE_UNION, BIGINTER_UNION, IMAGE_SING, BIGINTER_SING, ADD_ASSOC]
 ++ DEP_REWRITE_TAC [HMM_X] ++ RW_TAC std_ss []
 >> (MAP_EVERY Q.EXISTS_TAC [`s`, `Linit`, `Ltrans`, `Btrans`] ++ RW_TAC std_ss [])
 ++ DEP_REWRITE_TAC [HMM_Y] ++ STRIP_TAC
 >> (MAP_EVERY Q.EXISTS_TAC [`s`, `Linit`, `Ltrans`, `Btrans`] ++ RW_TAC std_ss [])
 ++ `!(a:real) b c d e. a * b * e * (c * d) = a * b * e * c * d` 
 	by METIS_TAC [REAL_MUL_ASSOC, REAL_MUL_COMM] ++ POP_ORW
 ++ MP_RW_TAC REAL_SUM_IMAGE_CMUL >> PSET_TAC [thmm_def, hmm_def]
 ++ Cases_on `EL (n + 1) Lx NOTIN (space s)` 
 >> (`PREIMAGE (X (t + n + 1)) {EL (n + 1) Lx} INTER p_space p = {}` 
    		by METIS_TAC [thmm_def, hmm_def, dtmc_def, mc_property_def, NOTIN_SPACE_EVENTS] 
    ++ RW_TAC std_ss [cond_prob_def, INTER_EMPTY, PROB_EMPTY, REAL_DIV_LZERO, 
    	REAL_MUL_LZERO, REAL_MUL_RZERO])
 ++ Cases_on `EL n Lx NOTIN (space s)` 
 >> (`PREIMAGE (X (t + n)) {EL n Lx} INTER p_space p = {}` 
    		by METIS_TAC [thmm_def, hmm_def, dtmc_def, mc_property_def, NOTIN_SPACE_EVENTS] 
    ++ RW_TAC std_ss [cond_prob_def, PROB_EMPTY, real_div, REAL_INV_0, 
    	REAL_MUL_LZERO, REAL_MUL_RZERO])
 ++ Cases_on `prob p (PREIMAGE (X (t + n + 1)) {EL (n + 1) Lx} INTER p_space p) = 0`
 >> (RW_TAC std_ss []
    ++ Suff `cond_prob p (PREIMAGE (X (t + n + 1)) {EL (n + 1) Lx} INTER p_space p)
      (PREIMAGE (X (t + n)) {EL n Lx} INTER p_space p) = 0`
    >> RW_TAC std_ss [REAL_MUL_RZERO, REAL_MUL_LZERO]
    ++ MATCH_MP_TAC COND_PROB_INTER_ZERO ++ RW_TAC std_ss []
    >> METIS_TAC [thmm_def, hmm_def, DTMC_EVENTS]
    ++ METIS_TAC [thmm_def, hmm_def, DTMC_EVENTS])
 ++ `0 < prob p (PREIMAGE (X (t + n + 1)) {EL (n + 1) Lx} INTER p_space p)`
 	by (`PREIMAGE (X (t + n + 1)) {EL (n + 1) Lx} INTER p_space p IN events p`
 		by METIS_TAC [thmm_def, hmm_def, DTMC_EVENTS]
           ++ METIS_TAC [PROB_POSITIVE, REAL_LT_LE])
 ++ Suff `SIGMA (\i. cond_prob p (PREIMAGE (Y (t + n + 1)) {i} INTER p_space p)
           (PREIMAGE (X (t + n + 1)) {EL (n + 1) Lx} INTER p_space p)) (space s1) = 1`
 >> RW_TAC std_ss [REAL_MUL_ASSOC, REAL_MUL_RID]
 ++ DEP_REWRITE_TAC [COND_PROB_ADDITIVE] ++ PSET_TAC [thmm_def, hmm_def]
 << [METIS_TAC [DTMC_EVENTS],
     METIS_TAC [PREIMAGE_X_IN_EVENTS],
     RW_TAC std_ss [(REWRITE_RULE [DISJOINT_DEF]) DISJOINT_PROC_INTER],
     RW_TAC std_ss [BIGUNION_PREIMAGEX_IS_PSPACE, INTER_IDEMPOT]]); 

val HMM_EVENTS_SUC0 = prove
  (``!X Y p s s1 Linit Ltrans (Btrans: num -> 'c -> 'b -> real) t n (Lx:'b list) (Ly:'c list) i j.
   thmm X Y p s s1 Linit Ltrans Btrans ==>
   (PREIMAGE (X (t + n + 2)) {j} INTER p_space p) INTER
            BIGINTER (IMAGE (\(k:num). PREIMAGE (X (t + k + 1)) {EL k Lx} INTER p_space p)
                	(count (n + 1))) INTER 
            BIGINTER (IMAGE (\(k:num). PREIMAGE (Y (t + k + 1)) {EL k Ly} INTER p_space p)
                	(count (n + 1))) INTER
            PREIMAGE (X t) {i} INTER p_space p IN events p``,
    RW_TAC std_ss []  
 ++ `prob_space p` by PSET_TAC [thmm_def, hmm_def, th_dtmc_def, dtmc_def, mc_property_def,
 	 random_variable_def]    
 ++ `!A B C D E. A INTER B INTER C INTER D INTER E INTER B = 
 	A INTER B INTER C INTER D INTER (E INTER B)` by METIS_TAC [INTER_ASSOC] ++ POP_ORW 
 ++ Cases_on `j NOTIN (space s)`
 >> (`PREIMAGE (X (t + n + 2)) {j} INTER p_space p = {}` 
 	by (MATCH_MP_TAC NOTIN_SPACE_EVENTS ++ Q.EXISTS_TAC `s` 
       		   ++ PSET_TAC [thmm_def, hmm_def, dtmc_def, mc_property_def])
    ++ RW_TAC std_ss [INTER_EMPTY, EVENTS_EMPTY])
 ++ Cases_on `i NOTIN (space s)`
 >> (`PREIMAGE (X t) {i} INTER p_space p = {}` 
 	by (MATCH_MP_TAC NOTIN_SPACE_EVENTS ++ Q.EXISTS_TAC `s` 
       		   ++ PSET_TAC [thmm_def, hmm_def, dtmc_def, mc_property_def])
    ++ RW_TAC std_ss [INTER_EMPTY, EVENTS_EMPTY])          		   
 ++ Cases_on `?m. m IN count (n + 1) /\ EL m Lx NOTIN space s`
 >> (PSET_TAC [IN_COUNT]
    ++ `BIGINTER (IMAGE (\k. PREIMAGE (X (t + k + 1)) {EL k Lx} INTER p_space p)
       		(count (n + 1))) SUBSET (\k. PREIMAGE (X (t + k + 1)) {EL k Lx} INTER p_space p) m` 
                by (MATCH_MP_TAC BIGINTER_SUBSET_SING ++ RW_TAC std_ss [IN_COUNT])    
    ++ `PREIMAGE (X (t + m + 1)) {EL m Lx} INTER p_space p = {}`
       		by (MATCH_MP_TAC NOTIN_SPACE_EVENTS ++ Q.EXISTS_TAC `s` 
       		   ++ PSET_TAC [thmm_def, hmm_def, dtmc_def, mc_property_def])
    ++ FULL_SIMP_TAC std_ss [SUBSET_EMPTY, INTER_EMPTY, EVENTS_EMPTY])
 ++ Cases_on `?m. m IN count (n + 1) /\ EL m Ly NOTIN space s1`   	
 >> (PSET_TAC [IN_COUNT]
    ++ `BIGINTER (IMAGE (\k. PREIMAGE (Y (t + k + 1)) {EL k Ly} INTER p_space p)
       		(count (n + 1))) SUBSET (\k. PREIMAGE (Y (t + k + 1)) {EL k Ly} INTER p_space p) m` 
                by (MATCH_MP_TAC BIGINTER_SUBSET_SING ++ RW_TAC std_ss [IN_COUNT])     
    ++ `PREIMAGE (Y (t + m + 1)) {EL m Ly} INTER p_space p = {}`
       		by (MATCH_MP_TAC NOTIN_SPACE_EVENTS ++ Q.EXISTS_TAC `s1` 
       		   ++ PSET_TAC [thmm_def, hmm_def, dtmc_def, mc_property_def])
    ++ FULL_SIMP_TAC std_ss [SUBSET_EMPTY, INTER_EMPTY, EVENTS_EMPTY])
 ++ FULL_SIMP_TAC std_ss [IN_COUNT]    
 ++ MATCH_MP_TAC EVENTS_INTER ++ RW_TAC std_ss []
 >> (MATCH_MP_TAC EVENTS_INTER ++ RW_TAC std_ss []
    >> (MATCH_MP_TAC EVENTS_INTER ++ RW_TAC std_ss []
       >> METIS_TAC [thmm_def, hmm_def, DTMC_EVENTS]
       ++ `BIGINTER (IMAGE (\k. PREIMAGE (X (t + k + 1)) {EL k Lx} INTER p_space p) 
       		(count (n + 1))) =
           BIGINTER (IMAGE (\k. (\k. PREIMAGE (X (t + k + 1)) {EL k Lx} INTER p_space p) k)
              (count (n + 1)))` by RW_TAC std_ss [] ++ POP_ORW
       ++ `count (n + 1) = count_mn 0 n` 
       			by PSET_TAC [count_def, count_mn_def, GSPECIFICATION, EXTENSION, LE_LT1] 
       ++ POP_ORW ++ MATCH_MP_TAC EVENTS_BIGINTER_MN ++ PSET_TAC [random_variable_def]
       ++ METIS_TAC [LE_LT1, thmm_def, hmm_def, DTMC_EVENTS])
    ++ `BIGINTER (IMAGE (\k. PREIMAGE (Y (t + k + 1)) {EL k Ly} INTER p_space p) 
    		(count (n + 1))) =
        BIGINTER (IMAGE (\(k:num). (\k. PREIMAGE (Y (t + k + 1)) {EL k Ly} INTER p_space p) k)
                (count (n + 1)))` by RW_TAC std_ss [] ++ POP_ORW
    ++ `count (n + 1) = count_mn 0 n` 
         by PSET_TAC [count_def, count_mn_def, GSPECIFICATION, EXTENSION, LE_LT1] ++ POP_ORW 
    ++ MATCH_MP_TAC EVENTS_BIGINTER_MN ++ RW_TAC std_ss []
    ++ METIS_TAC [LE_LT1, thmm_def, hmm_def, PREIMAGE_X_IN_EVENTS])
 ++ METIS_TAC [thmm_def, hmm_def, DTMC_EVENTS]);

val HMM_XX = prove
  (``!X Y p s s1 Linit Ltrans (Btrans: num -> 'c -> 'b -> real) t n (Lx:'b list) (Ly:'c list) i j.
   thmm X Y p s s1 Linit Ltrans Btrans ==>
   (prob p ((PREIMAGE (X (t + n + 2)) {j} INTER p_space p) INTER
            BIGINTER (IMAGE (\(k:num). PREIMAGE (X (t + k + 1)) {EL k Lx} INTER p_space p)
                	(count (n + 1))) INTER 
            BIGINTER (IMAGE (\(k:num). PREIMAGE (Y (t + k + 1)) {EL k Ly} INTER p_space p)
                	(count (n + 1))) INTER
            PREIMAGE (X t) {i} INTER p_space p) =
    SIGMA (\k. prob p ((PREIMAGE (X (t + n + 2)) {j} INTER p_space p) INTER
            BIGINTER (IMAGE (\(k:num). PREIMAGE (X (t + k + 1)) {EL k Lx} INTER p_space p)
                	(count (n + 1))) INTER 
            BIGINTER (IMAGE (\(k:num). PREIMAGE (Y (t + k + 1)) {EL k Ly} INTER p_space p)
                	(count (n + 1))) INTER (PREIMAGE (X t) {i} INTER p_space p) INTER
            (PREIMAGE (Y t) {k} INTER p_space p))) (space s1))``,
    RW_TAC std_ss []  
 ++ `prob_space p` by PSET_TAC [thmm_def, hmm_def, th_dtmc_def, dtmc_def, mc_property_def,
 	 random_variable_def] 
 ++ `FINITE (space s1)` by PSET_TAC [thmm_def, hmm_def]  	  	    
 ++ `!A B C D E G. A INTER B INTER C INTER D INTER (E INTER B) INTER (G INTER B) =
          A INTER B INTER C INTER D INTER E INTER B INTER (G INTER B)` 
          by METIS_TAC [INTER_ASSOC] ++ POP_ORW 
        
 ++ `SIGMA (\k. prob p ((PREIMAGE (X (t + n + 2)) {j} INTER p_space p) INTER
            BIGINTER (IMAGE (\(k:num). PREIMAGE (X (t + k + 1)) {EL k Lx} INTER p_space p)
                	(count (n + 1))) INTER 
            BIGINTER (IMAGE (\(k:num). PREIMAGE (Y (t + k + 1)) {EL k Ly} INTER p_space p)
                	(count (n + 1))) INTER PREIMAGE (X t) {i} INTER p_space p INTER
            (PREIMAGE (Y t) {k} INTER p_space p))) (space s1) =
     SIGMA (\k. prob p (PREIMAGE (X (t + n + 2)) {j} INTER p_space p INTER
            BIGINTER (IMAGE (\k. PREIMAGE (X (t + k + 1)) {EL k Lx} INTER p_space p)
                 (count (n + 1))) INTER
            BIGINTER (IMAGE (\k. PREIMAGE (Y (t + k + 1)) {EL k Ly} INTER p_space p)
                 (count (n + 1))) INTER PREIMAGE (X t) {i} INTER p_space p INTER
            (\k. PREIMAGE (Y t) {k} INTER p_space p) k)) (space s1)` 
        by RW_TAC std_ss [GSYM INTER_ASSOC] ++ POP_ORW
 ++ MATCH_MP_TAC PROB_REAL_SUM_IMAGE_FN 
 ++ RW_TAC std_ss []        	
 << [MATCH_MP_TAC HMM_EVENTS_SUC0 
     ++ MAP_EVERY Q.EXISTS_TAC [`s`, `s1`, `Linit`, `Ltrans`, `Btrans`] 
     ++ RW_TAC std_ss [],
     MATCH_MP_TAC EVENTS_INTER ++ RW_TAC std_ss []
     >> (MATCH_MP_TAC HMM_EVENTS_SUC0 
        ++ MAP_EVERY Q.EXISTS_TAC [`s`, `s1`, `Linit`, `Ltrans`, `Btrans`] 
        ++ RW_TAC std_ss [])
     ++ METIS_TAC [thmm_def, hmm_def, PREIMAGE_X_IN_EVENTS],
     MATCH_MP_TAC DISJOINT_PROC_INTER ++ RW_TAC std_ss [],
     PSET_TAC [thmm_def, hmm_def, BIGUNION_PREIMAGEX_IS_PSPACE, INTER_IDEMPOT]]);
         
val IMAGE_MN_EQ = prove
  (``!Y n t Ly. 
	IMAGE (\k. PREIMAGE (Y (t + k)) {EL k (i::Ly)} INTER p_space p) (count_mn 1 (n + 1)) =
	IMAGE (\k. PREIMAGE (Y (t + k + 1)) {EL k Ly} INTER p_space p) (count (n + 1))``,
    Induct_on `n`
 >> (RW_TAC std_ss [COUNT_ONE, COUNT_MN_SING, IMAGE_SING] ++ ONCE_REWRITE_TAC [ONE]
    ++ RW_TAC std_ss [EL, HD, TL])
 ++ `count (SUC n + 1) = {SUC n} UNION count (n + 1)`
 	by (PSET_TAC [IN_COUNT, EXTENSION] ++ RW_TAC arith_ss [])
 ++ `count_mn 1 (SUC n + 1) = {SUC n + 1} UNION count_mn 1 (SUC n)`
 	by (PSET_TAC [IN_COUNT_MN, EXTENSION] ++ RW_TAC arith_ss []) 	
 ++ RW_TAC std_ss [IMAGE_UNION, IMAGE_SING, ADD1] 
 ++ `t + (n + 1 + 1) = t + (n + 1) + 1` by RW_TAC arith_ss [] ++ POP_ORW
 ++ `n + 1 + 1 = SUC (n + 1)` by RW_TAC std_ss [ADD1]
 ++ RW_TAC arith_ss [EL, TL]); 

val EL_SHIFT = prove
  (``!j l k. 0 < k ==> (EL k ([j] ++ l) = EL (k - 1) l)``,
    Induct_on `k` >> RW_TAC std_ss []
 ++ RW_TAC std_ss [EL] 
 ++ ONCE_REWRITE_TAC [GSYM CONS_APPEND]
 ++ RW_TAC std_ss [TL]);

val PATH_COMBIN = prove
  (``!X Y p s s1 Linit Ltrans (Btrans: num -> 'c -> 'b -> real) t n (Lx:'b list) (Ly:'c list) i j x.
   thmm X Y p s s1 Linit Ltrans Btrans /\ (LENGTH Lx = n + 1) /\ (LENGTH Ly = n + 1) ==> 
   (PREIMAGE (X (t + n + 2)) {j} INTER p_space p INTER
     BIGINTER (IMAGE (\k. PREIMAGE (X (t + k + 1)) {EL k Lx} INTER p_space p) 
 	(count (n + 1))) INTER
     BIGINTER (IMAGE (\k. PREIMAGE (Y (t + k + 1)) {EL k Ly} INTER p_space p) 
        (count (n + 1))) INTER
     (PREIMAGE (X t) {i} INTER p_space p) INTER (PREIMAGE (Y t) {x} INTER p_space p) =
     PREIMAGE (X (t + n + 2)) {j} INTER p_space p INTER
     BIGINTER (IMAGE (\k. PREIMAGE (X (t + k)) {EL k ([i] ++ Lx)} INTER p_space p) 
     	(count (n + 2))) INTER
     BIGINTER (IMAGE (\k. PREIMAGE (Y (t + k)) {EL k ([x] ++ Ly)} INTER p_space p) 
        (count (n + 2))))``,
    RW_TAC std_ss []  
 ++ `prob_space p` by PSET_TAC [thmm_def, hmm_def, th_dtmc_def, dtmc_def, mc_property_def,
 	 random_variable_def]    
 ++ `FINITE (space s1)` by PSET_TAC [thmm_def, hmm_def] 
 ++ `count (n + 2) = {0} UNION count_mn 1 (n + 1)` 
     		by (PSET_TAC [IN_COUNT, IN_COUNT_MN, EXTENSION] ++ RW_TAC arith_ss []) ++ POP_ORW
 ++ RW_TAC std_ss [IMAGE_UNION, BIGINTER_UNION, IMAGE_SING, BIGINTER_SING, 
       	GSYM CONS_APPEND, EL, HD, IMAGE_MN_EQ]
 ++ `!A B C D E G. G INTER B INTER A INTER E INTER (C INTER B) INTER (D INTER B) =
    G INTER B INTER C INTER B INTER A INTER (D INTER B INTER E)` 
	    by METIS_TAC [INTER_ASSOC, INTER_COMM]
 ++ RW_TAC std_ss [GSYM INTER_ASSOC]);  
        
val HMM_SIGMA_SIGMA = prove
  (``!X Y p s s1 Linit Ltrans (Btrans: num -> 'c -> 'b -> real) t n (Lx:'b list) (Ly:'c list) i j.
   thmm X Y p s s1 Linit Ltrans Btrans /\ (LENGTH Lx = n + 1) /\ (LENGTH Ly = n + 1) ==>
   (prob p ((PREIMAGE (X (t + n + 2)) {j} INTER p_space p) INTER
            BIGINTER (IMAGE (\(k:num). PREIMAGE (X (t + k + 1)) {EL k Lx} INTER p_space p)
                	(count (n + 1))) INTER 
            BIGINTER (IMAGE (\(k:num). PREIMAGE (Y (t + k + 1)) {EL k Ly} INTER p_space p)
                	(count (n + 1))) INTER
            PREIMAGE (X t) {i} INTER p_space p) =
    SIGMA (\k. SIGMA (\m. 
            prob p ((PREIMAGE (X (t + n + 2)) {j} INTER p_space p) INTER
            (PREIMAGE (Y (t + n + 2)) {m} INTER p_space p) INTER
            BIGINTER (IMAGE (\(k:num). PREIMAGE (X (t + k + 1)) {EL k Lx} INTER p_space p)
                	(count (n + 1))) INTER 
            BIGINTER (IMAGE (\(k:num). PREIMAGE (Y (t + k + 1)) {EL k Ly} INTER p_space p)
                	(count (n + 1))) INTER (PREIMAGE (X t) {i} INTER p_space p) INTER
            (PREIMAGE (Y t) {k} INTER p_space p))) (space s1)) (space s1))``,
    RW_TAC std_ss []  
 ++ `prob_space p` by PSET_TAC [thmm_def, hmm_def, th_dtmc_def, dtmc_def, mc_property_def,
 	 random_variable_def]    
 ++ `FINITE (space s1)` by PSET_TAC [thmm_def, hmm_def] 	 
 ++ DEP_REWRITE_TAC [HMM_XX] ++ RW_TAC std_ss []
 >> (MAP_EVERY Q.EXISTS_TAC [`s`, `Linit`, `Ltrans`, `Btrans`] ++ RW_TAC std_ss [])
 ++ MATCH_MP_TAC REAL_SUM_IMAGE_EQ ++ RW_TAC std_ss []
 ++ MP_RW_TAC PATH_COMBIN ++ RW_TAC std_ss []
 ++ Cases_on `i NOTIN (space s)`
 >> (`BIGINTER (IMAGE (\k. PREIMAGE (X (t + k)) {EL k ([i] ++ Lx)} INTER p_space p)
       	(count (n + 2))) SUBSET (PREIMAGE (X t) {i} INTER p_space p)` 
        by (`count (n + 2) = {0} UNION count_mn 1 (n + 1)` 
        	by (PSET_TAC [count_def, count_mn_def, EXTENSION] ++ RW_TAC arith_ss [])
           ++ POP_ORW ++ RW_TAC std_ss [IMAGE_UNION, BIGINTER_UNION, IMAGE_SING, 
           	BIGINTER_SING, INTER_SUBSET, GSYM CONS_APPEND, EL, HD, INTER_SUBSET]) 
    ++ `PREIMAGE (X t) {i} INTER p_space p = {}` 
    	by METIS_TAC [thmm_def, hmm_def, dtmc_def, mc_property_def, NOTIN_SPACE_EVENTS]
    ++ FULL_SIMP_TAC std_ss [SUBSET_EMPTY, INTER_EMPTY, PROB_EMPTY, GSYM REAL_SUM_IMAGE_0])
 ++ Cases_on `j NOTIN (space s)`
 >> (`PREIMAGE (X (t + n + 2)) {j} INTER p_space p = {}` 
    	by METIS_TAC [thmm_def, hmm_def, dtmc_def, mc_property_def, NOTIN_SPACE_EVENTS]
    ++ RW_TAC std_ss [INTER_EMPTY, PROB_EMPTY, GSYM REAL_SUM_IMAGE_0])    
 ++ Cases_on `?m. m IN count (n + 1) /\ EL m Lx NOTIN (space s)`
 >> (PSET_TAC [IN_COUNT]
    ++ `BIGINTER (IMAGE (\k. PREIMAGE (X (t + k + 1)) {EL k Lx} INTER p_space p)
       	(count (n + 1))) SUBSET (\k. PREIMAGE (X (t + k + 1)) {EL k Lx} INTER p_space p) m` 
                by (MATCH_MP_TAC BIGINTER_SUBSET_SING ++ RW_TAC std_ss [IN_COUNT])    
    ++ `BIGINTER (IMAGE (\k. PREIMAGE (X (t + k)) {EL k ([i] ++ Lx)} INTER p_space p)
       	(count (n + 2))) SUBSET 
       	(\k. PREIMAGE (X (t + k)) {EL k ([i] ++ Lx)} INTER p_space p) (m + 1)` 
                by (MATCH_MP_TAC BIGINTER_SUBSET_SING ++ RW_TAC arith_ss [IN_COUNT] ) 
    ++ `!t. PREIMAGE (X t) {EL m Lx} INTER p_space p = {}`
       		by (RW_TAC std_ss [] ++ MATCH_MP_TAC NOTIN_SPACE_EVENTS ++ Q.EXISTS_TAC `s` 
       		   ++ PSET_TAC [thmm_def, hmm_def, dtmc_def, mc_property_def])
    ++ `EL 1 ([i] ++ Lx) = EL 0 Lx` by RW_TAC arith_ss [LENGTH, LENGTH_APPEND, EL_APPEND2]
    ++ Cases_on `m = 0`
    >> FULL_SIMP_TAC std_ss [SUBSET_EMPTY, INTER_EMPTY, PROB_EMPTY, GSYM REAL_SUM_IMAGE_0]    
    ++ `EL (m + 1) ([i] ++ Lx) = EL m Lx` by RW_TAC arith_ss [LENGTH, LENGTH_APPEND, EL_APPEND2]    
    ++ FULL_SIMP_TAC std_ss [SUBSET_EMPTY, INTER_EMPTY, PROB_EMPTY, GSYM REAL_SUM_IMAGE_0])
 ++ Cases_on `?m. m IN count (n + 1) /\ EL m Ly NOTIN space s1`   	
 >> (PSET_TAC [IN_COUNT]
    ++ `BIGINTER (IMAGE (\k. PREIMAGE (Y (t + k + 1)) {EL k Ly} INTER p_space p)
       	(count (n + 1))) SUBSET (\k. PREIMAGE (Y (t + k + 1)) {EL k Ly} INTER p_space p) m` 
                by (MATCH_MP_TAC BIGINTER_SUBSET_SING ++ RW_TAC std_ss [IN_COUNT])     
    ++ `BIGINTER (IMAGE (\k. PREIMAGE (Y (t + k)) {EL k ([x] ++ Ly)} INTER p_space p)
       	(count (n + 2))) SUBSET 
       	(\k. PREIMAGE (Y (t + k)) {EL k ([x] ++ Ly)} INTER p_space p) (m + 1)` 
                by (MATCH_MP_TAC BIGINTER_SUBSET_SING ++ RW_TAC arith_ss [IN_COUNT]) 
    ++ `PREIMAGE (Y (t + m + 1)) {EL m Ly} INTER p_space p = {}`
       		by (MATCH_MP_TAC NOTIN_SPACE_EVENTS ++ Q.EXISTS_TAC `s1` 
       		   ++ PSET_TAC [thmm_def, hmm_def, dtmc_def, mc_property_def])                
    ++ `EL (m + 1) ([x] ++ Ly) = EL m Ly` by RW_TAC arith_ss [LENGTH, LENGTH_APPEND, EL_APPEND2]
    ++ FULL_SIMP_TAC std_ss [ADD_ASSOC, SUBSET_EMPTY, INTER_EMPTY, PROB_EMPTY, 
    	GSYM REAL_SUM_IMAGE_0])   
 ++ FULL_SIMP_TAC std_ss [IN_COUNT]
 ++ `!k. k <= n + 1 + 1 ==> EL k ([i:'b] ++ (Lx:'b list) ++ [j:'b]) IN space s`
 	by (RW_TAC std_ss [] ++ Cases_on `k = n + 1 + 1` 
 	   >> (`LENGTH ([i] ++ Lx) = n + 2` by RW_TAC arith_ss [LENGTH_APPEND, LENGTH]
 	      ++ RW_TAC arith_ss [EL_APPEND2, EL, HD])
 	   ++ `EL k ([i] ++ Lx ++ [j]) = EL k ([i] ++ Lx)` 
 	   	by RW_TAC arith_ss [EL_APPEND1, LENGTH_APPEND, LENGTH] ++ POP_ORW 
 	   ++ Cases_on `k = 0` >> (ONCE_REWRITE_TAC [GSYM CONS_APPEND] ++ RW_TAC std_ss [EL, HD])
 	   ++ MP_RW_TAC EL_SHIFT >> RW_TAC arith_ss [] 
 	   ++ `k - 1 < (n + 1)` by RW_TAC arith_ss []
 	   ++ METIS_TAC [])
 ++ `!k. k <= n + 1 ==> EL k ([x] ++ Ly) IN space s1` 	          
        by (RW_TAC std_ss [] ++ Cases_on `k = 0` 
           >> (ONCE_REWRITE_TAC [GSYM CONS_APPEND] ++ RW_TAC std_ss [EL, HD])
           ++ MP_RW_TAC EL_SHIFT >> RW_TAC arith_ss []
           ++ `k - 1 < (n + 1)` by RW_TAC arith_ss [] ++ METIS_TAC []) 
 ++ `EL (n + 2) ([i] ++ Lx ++ [j]) = j` 
 	by (`LENGTH ([i] ++ Lx) = n + 2` by RW_TAC arith_ss [LENGTH_APPEND, LENGTH]
 	   ++ RW_TAC arith_ss [EL_APPEND2, EL, HD])
 ++ `BIGINTER (IMAGE (\k. PREIMAGE (X (k + t)) {EL k ([i] ++ Lx ++ [j])} INTER p_space p) 
 	(count (n + 2))) = 
     BIGINTER (IMAGE (\k. PREIMAGE (X (k + t)) {EL k ([i] ++ Lx)} INTER p_space p) 
        (count (n + 2)))` by (PSET_TAC [IN_BIGINTER_IMAGE, EXTENSION]
        ++ EQ_TAC >> (RW_TAC arith_ss [EL_APPEND1, LENGTH, LENGTH_APPEND] ++ METIS_TAC []) 
        ++ (RW_TAC arith_ss [EL_APPEND1, LENGTH, LENGTH_APPEND] ++ METIS_TAC []) 
        ++ METIS_TAC []) 
 ++ (MP_TAC o Q.SPECL [`X`, `Y`, `p`, `s`, `s1`, `Linit`, `Ltrans`, `Btrans`, `t`, 
 	`n + 1`, `[i] ++ Lx ++ [j]`, `[x] ++ Ly`]) HMM_X ++ RW_TAC arith_ss []
 ++ POP_ASSUM K_TAC ++ MATCH_MP_TAC REAL_SUM_IMAGE_EQ ++ RW_TAC std_ss []
 ++ `!A B C D E G H. 
 	A INTER B INTER (C INTER B) INTER D INTER E INTER (G INTER B) INTER (H INTER B) =
        C INTER B INTER (A INTER B INTER D INTER E INTER (G INTER B) INTER (H INTER B))` 
          by METIS_TAC [INTER_ASSOC, INTER_COMM] ++ POP_ORW
 ++ (MP_TAC o Q.SPECL [`X`, `Y`, `p`, `s`, `s1`, `Linit`, `Ltrans`, `Btrans`, `t`, 
 	`n`, `Lx`, `Ly`, `i`, `j`, `x`]) PATH_COMBIN ++ RW_TAC arith_ss []
 ++ `!A B C D E G H. 
     A INTER B INTER (C INTER B INTER D INTER E) = C INTER B INTER (A INTER B) INTER D INTER E` 
          by METIS_TAC [INTER_ASSOC, INTER_COMM] ++ RW_TAC std_ss []);

val PATH_SUC_COMBIN = prove
  (``!X Y p s s1 Linit Ltrans (Btrans: num -> 'c -> 'b -> real) t n (Lx:'b list) (Ly:'c list).
   thmm X Y p s s1 Linit Ltrans Btrans /\ (LENGTH Lx = n + 1) /\ (LENGTH Ly = n + 1) ==>
   (PREIMAGE (X (t + n + 2)) {j} INTER p_space p INTER
    (PREIMAGE (Y (t + n + 2)) {m} INTER p_space p) INTER
    BIGINTER (IMAGE (\k. PREIMAGE (X (t + k + 1)) {EL k Lx} INTER p_space p) (count (n + 1)))
    INTER 
    BIGINTER (IMAGE (\k. PREIMAGE (Y (t + k + 1)) {EL k Ly} INTER p_space p) (count (n + 1)))
    INTER (PREIMAGE (X t) {i} INTER p_space p) INTER (PREIMAGE (Y t) {r} INTER p_space p) = 
    BIGINTER (IMAGE (\k. PREIMAGE (X (t + k)) {EL k ([i] ++ Lx ++ [j])} INTER p_space p) 
    	(count (n + 3)))
    INTER 
    BIGINTER (IMAGE (\k. PREIMAGE (Y (t + k)) {EL k ([r] ++ Ly ++ [m])} INTER p_space p) 
    	(count (n + 3))))``,
    RW_TAC std_ss []
 ++ `!A B C D E G H. 
 	A INTER B INTER (C INTER B) INTER D INTER E INTER (G INTER B) INTER (H INTER B) =
        C INTER B INTER (A INTER B INTER D INTER E INTER (G INTER B) INTER (H INTER B))` 
          by METIS_TAC [INTER_ASSOC, INTER_COMM] ++ POP_ORW                     
 ++ MP_RW_TAC PATH_COMBIN ++ RW_TAC std_ss []
 ++ `count (n + 3) = {n + 2} UNION count (n + 2)` 
     		by (PSET_TAC [IN_COUNT, EXTENSION] ++ RW_TAC arith_ss []) ++ POP_ORW
 ++ `EL (n + 2) (i::Lx ++ [j]) = j` 
 	by RW_TAC arith_ss [LENGTH_APPEND, LENGTH, EL_APPEND2, ADD1, EL, HD]     		
 ++ `EL (n + 2) (r::Ly ++ [m]) = m`
 	by RW_TAC arith_ss [LENGTH_APPEND, LENGTH, EL_APPEND2, ADD1, EL, HD]
 ++ `BIGINTER (IMAGE (\k. PREIMAGE (X (t + k)) {EL k (i::Lx ++ [j])} INTER p_space p) 
 	(count (n + 2))) =
     BIGINTER (IMAGE (\k. PREIMAGE (X (t + k)) {EL k (i::Lx)} INTER p_space p) (count (n + 2)))`
     by (PSET_TAC [IN_BIGINTER_IMAGE, EXTENSION] ++ EQ_TAC 
        >> (RW_TAC arith_ss [EL_APPEND1, LENGTH, LENGTH_APPEND] ++ METIS_TAC []) 
        ++ RW_TAC arith_ss [EL_APPEND1, LENGTH, LENGTH_APPEND] ++ METIS_TAC []) 
 ++ `BIGINTER (IMAGE (\k. PREIMAGE (Y (t + k)) {EL k (r::Ly ++ [m])} INTER p_space p)  
        (count (n + 2))) =
     BIGINTER (IMAGE (\k. PREIMAGE (Y (t + k)) {EL k (r::Ly)} INTER p_space p) (count (n + 2)))`
     by (PSET_TAC [IN_BIGINTER_IMAGE, EXTENSION] ++ EQ_TAC 
        >> (RW_TAC arith_ss [EL_APPEND1, LENGTH, LENGTH_APPEND] ++ METIS_TAC []) 
        ++ RW_TAC arith_ss [EL_APPEND1, LENGTH, LENGTH_APPEND] ++ METIS_TAC [])     
 ++ RW_TAC std_ss [IMAGE_UNION, BIGINTER_UNION, IMAGE_SING, BIGINTER_SING, 
       	GSYM CONS_APPEND, EL, HD, ADD_ASSOC]
 ++ `!A B C E G. G INTER B INTER (A INTER B INTER E INTER C) =
    A INTER B INTER E INTER (G INTER B INTER C)` by METIS_TAC [INTER_ASSOC, INTER_COMM]
 ++ RW_TAC std_ss []);       

val PATH_SIGMA = prove
  (``!X Y p s s1 Linit Ltrans (Btrans: num -> 'c -> 'b -> real) t n (Lx:'b list) (Ly:'c list).
   thmm X Y p s s1 Linit Ltrans Btrans /\ (LENGTH Lx = n + 1) /\ (LENGTH Ly = n + 1) ==>
   (SIGMA (\r. SIGMA (\m. prob p 
      (BIGINTER (IMAGE (\k. PREIMAGE (X (t + k)) {EL k ([i] ++ Lx ++ [j])} INTER p_space p) 
    	(count (n + 3)))  INTER 
       BIGINTER (IMAGE (\k. PREIMAGE (Y (t + k)) {EL k ([r] ++ Ly ++ [m])} INTER p_space p) 
    	(count (n + 3))))) (space s1)) (space s1) =
    SIGMA (\r. SIGMA (\m. prob p (PREIMAGE (X t) {EL 0 ([i] ++ Lx ++ [j])} INTER p_space p) *
          cond_prob p (PREIMAGE (Y t) {EL 0 ([r] ++ Ly ++ [m])} INTER p_space p)
            (PREIMAGE (X t) {EL 0 ([i] ++ Lx ++ [j])} INTER p_space p) *
          mulcon (0,n + 2)
            (\k.
               cond_prob p
                 (PREIMAGE (X (t + k + 1)) {EL (k + 1) ([i] ++ Lx ++ [j])} INTER p_space p)
                 (PREIMAGE (X (t + k)) {EL k ([i] ++ Lx ++ [j])} INTER p_space p) *
               cond_prob p
                 (PREIMAGE (Y (t + k + 1)) {EL (k + 1) ([r] ++ Ly ++ [m])} INTER p_space p)
                 (PREIMAGE (X (t + k + 1)) {EL (k + 1) ([i] ++ Lx ++ [j])} INTER
                  p_space p))) (space s1)) (space s1))``,
    RW_TAC std_ss []   
 ++ `prob_space p` by FULL_SIMP_TAC std_ss [thmm_def, hmm_def, random_variable_def]  
 ++ `FINITE (space s1)` by PSET_TAC [thmm_def, hmm_def]                    
 ++ MATCH_MP_TAC REAL_SUM_IMAGE_EQ ++ RW_TAC std_ss []
 ++ MATCH_MP_TAC REAL_SUM_IMAGE_EQ ++ RW_TAC std_ss []              
 ++ (MP_TAC o Q.SPECL [`X`, `Y`, `p`, `s`, `s1`, `Linit`, `Ltrans`, `Btrans`, `t`, 
 	`n + 2`, `[i] ++ Lx ++ [j]`, `[x] ++ Ly ++ [x']`]) HMM_JOINT_PROB 
 ++ RW_TAC arith_ss [GSYM APPEND_ASSOC, GSYM CONS_APPEND, EL, HD]);

val MULCON_THREE = prove
  (``!n f. mulcon (0, n + 2) f = f 0 * f (n + 1) * mulcon (1, n) f``,
    RW_TAC std_ss []                  
 ++ `n + 2 = SUC (n + 1)` by RW_TAC arith_ss [] 
 ++ RW_TAC std_ss [mulcon_def] ++ ONCE_REWRITE_TAC [ADD_COMM]
 ++ RW_TAC std_ss [GSYM MULCON_TWO, MULCON_1]
 ++ METIS_TAC [REAL_MUL_ASSOC, REAL_MUL_COMM]);

val SIGMA_SIGMA_CMUL = prove
  (``!f g (c:real) s t. FINITE s /\ FINITE t ==> 
	(SIGMA (\r. SIGMA (\m. c * g r * f m) s) t =
	c * SIGMA (\r. g r * SIGMA (\m. f m) s) t)``,
    RW_TAC std_ss []   
 ++ DEP_REWRITE_TAC [(UNDISCH o GSYM o Q.ISPEC `t:'b -> bool`) REAL_SUM_IMAGE_CMUL]
 ++ MATCH_MP_TAC REAL_SUM_IMAGE_EQ
 ++ RW_TAC std_ss []
 ++ DEP_REWRITE_TAC [(UNDISCH o GSYM o Q.SPEC `s`) REAL_SUM_IMAGE_CMUL]
 ++ RW_TAC std_ss [REAL_MUL_ASSOC]);
 
val PATH_MULCON = prove
  (``!X Y p s s1 Linit Ltrans (Btrans: num -> 'c -> 'b -> real) t n (Lx:'b list) (Ly:'c list) r i j m.
   thmm X Y p s s1 Linit Ltrans Btrans /\ (LENGTH Lx = n + 1) /\ (LENGTH Ly = n + 1) ==>
   (mulcon (0,n + 2) (\k. 
      cond_prob p (PREIMAGE (X (t + k + 1)) {EL (k + 1) ([i] ++ Lx ++ [j])} INTER p_space p)
                  (PREIMAGE (X (t + k)) {EL k ([i] ++ Lx ++ [j])} INTER p_space p) *
      cond_prob p (PREIMAGE (Y (t + k + 1)) {EL (k + 1) ([r] ++ Ly ++ [m])} INTER p_space p)
                 (PREIMAGE (X (t + k + 1)) {EL (k + 1) ([i] ++ Lx ++ [j])} INTER p_space p)) =
    cond_prob p (PREIMAGE (X (t + 1)) {EL 0 Lx} INTER p_space p)
                  (PREIMAGE (X t) {i} INTER p_space p) *
    cond_prob p (PREIMAGE (Y (t + 1)) {EL 0 Ly} INTER p_space p)
                  (PREIMAGE (X (t + 1)) {EL 0 Lx} INTER p_space p) *
    cond_prob p (PREIMAGE (X (t + n + 2)) {j} INTER p_space p)
                  (PREIMAGE (X (t + n + 1)) {EL n Lx} INTER p_space p) *
    cond_prob p (PREIMAGE (Y (t + n + 2)) {m} INTER p_space p)
                  (PREIMAGE (X (t + n + 2)) {j} INTER p_space p) *
    mulcon (1,n) (\k. 
      cond_prob p (PREIMAGE (X (t + k + 1)) {EL k Lx} INTER p_space p)
                  (PREIMAGE (X (t + k)) {EL (k - 1) Lx} INTER p_space p) *
      cond_prob p (PREIMAGE (Y (t + k + 1)) {EL k Ly} INTER p_space p)
                 (PREIMAGE (X (t + k + 1)) {EL k Lx} INTER p_space p)))``,
    RW_TAC std_ss [MULCON_THREE]
 ++ `EL 0 ([i] ++ Lx ++ [j]) = i` 
 	by RW_TAC std_ss [GSYM APPEND_ASSOC, GSYM CONS_APPEND, EL, HD]     
 ++ RW_TAC arith_ss [LENGTH_APPEND, LENGTH, EL_APPEND2, EL, HD]
 ++ RW_TAC arith_ss [GSYM APPEND_ASSOC, LENGTH, EL_APPEND2, EL_APPEND1]
 ++ RW_TAC std_ss [EL, HD]
 ++ `!(a:real) b c d e f. (e = f) ==> (a * b * (c * d) * e = a * b * c * d * f)`
 	by METIS_TAC [REAL_MUL_ASSOC] ++ POP_ASSUM MATCH_MP_TAC
 ++ MATCH_MP_TAC MULCON_POS_EQ
 ++ RW_TAC arith_ss [EL_APPEND1, LENGTH, EL_APPEND2]);
                                       
val HMM_SUCXX_PROB = prove
  (``!X Y p s s1 Linit Ltrans (Btrans: num -> 'c -> 'b -> real) t n (Lx:'b list) (Ly:'c list).
   thmm X Y p s s1 Linit Ltrans Btrans /\ (LENGTH Lx = n + 1) /\ (LENGTH Ly = n + 1) ==>
   (prob p (PREIMAGE (X (t + n + 2)) {j} INTER p_space p INTER
            BIGINTER (IMAGE (\(k:num). PREIMAGE (X (t + k + 1)) {EL k Lx} INTER p_space p)
                	(count (n + 1))) INTER 
            BIGINTER (IMAGE (\(k:num). PREIMAGE (Y (t + k + 1)) {EL k Ly} INTER p_space p)
                	(count (n + 1))) INTER
            PREIMAGE (X t) {i} INTER p_space p) =
    prob p (PREIMAGE (X t) {i} INTER p_space p) * 
    cond_prob p (PREIMAGE (X (t + 1)) {HD Lx} INTER p_space p)
      (PREIMAGE (X t) {i} INTER p_space p) *
    cond_prob p (PREIMAGE (Y (t + 1)) {HD Ly} INTER p_space p)
      (PREIMAGE (X (t + 1)) {HD Lx} INTER p_space p) *
    cond_prob p (PREIMAGE (X (t + n + 2)) {j} INTER p_space p)
      (PREIMAGE (X (t + n + 1)) {EL n Lx} INTER p_space p) *
    mulcon (1, n) (\k. cond_prob p (PREIMAGE (X (t + k + 1)) {EL k Lx} INTER p_space p)
                        (PREIMAGE (X (t + k)) {EL (k - 1) Lx} INTER p_space p) *
                        cond_prob p (PREIMAGE (Y (t + k + 1)) {EL k Ly} INTER p_space p)
                        (PREIMAGE (X (t + k + 1)) {EL k Lx} INTER p_space p)))``,
    RW_TAC std_ss [] 
 ++ `prob_space p` by FULL_SIMP_TAC std_ss [thmm_def, hmm_def, random_variable_def]  
 ++ `FINITE (space s1)` by PSET_TAC [thmm_def, hmm_def] 
 ++ DEP_REWRITE_TAC [HMM_SIGMA_SIGMA] ++ RW_TAC std_ss []
 >> (MAP_EVERY Q.EXISTS_TAC [`s`, `Linit`, `Ltrans`, `Btrans`] ++ RW_TAC std_ss [])
 ++ MP_RW_TAC PATH_SUC_COMBIN >> RW_TAC std_ss []
 ++ MP_RW_TAC PATH_SIGMA >> RW_TAC std_ss [] 
 ++ MP_RW_TAC PATH_MULCON >> RW_TAC std_ss [] 
 ++ RW_TAC std_ss [GSYM APPEND_ASSOC, GSYM CONS_APPEND, EL, HD]
 ++ Cases_on `j NOTIN (space s)`
 >> (`PREIMAGE (X (t + n + 2)) {j} INTER p_space p = {}`
 	by (MATCH_MP_TAC NOTIN_SPACE_EVENTS ++ Q.EXISTS_TAC `s` 
       		   ++ PSET_TAC [thmm_def, hmm_def, dtmc_def, mc_property_def])
    ++ RW_TAC std_ss [cond_prob_def, INTER_EMPTY, PROB_EMPTY, REAL_DIV_LZERO, 
    	REAL_MUL_LZERO, REAL_MUL_RZERO, REAL_SUM_IMAGE_0])    	
 ++ Cases_on `EL n Lx NOTIN (space s)`
 >> (`PREIMAGE (X (t + n + 1)) {EL n Lx} INTER p_space p = {}`
 	by (MATCH_MP_TAC NOTIN_SPACE_EVENTS ++ Q.EXISTS_TAC `s` 
       		   ++ PSET_TAC [thmm_def, hmm_def, dtmc_def, mc_property_def])
    ++ RW_TAC std_ss [cond_prob_def, INTER_EMPTY, PROB_EMPTY, real_div, REAL_INV_0,
    	REAL_MUL_LZERO, REAL_MUL_RZERO, REAL_SUM_IMAGE_0])
 ++ Cases_on `prob p (PREIMAGE (X (t + n + 2)) {j} INTER p_space p) = 0` 	
 >> (RW_TAC std_ss []
    ++ `cond_prob p (PREIMAGE (X (t + n + 2)) {j} INTER p_space p)
      (PREIMAGE (X (t + n + 1)) {EL n Lx} INTER p_space p) = 0`
      	by (MP_RW_TAC COND_PROB_INTER_ZERO ++ RW_TAC std_ss []
      	   >> METIS_TAC [thmm_def, hmm_def, DTMC_EVENTS]
      	   ++ METIS_TAC [thmm_def, hmm_def, DTMC_EVENTS])
    ++ `!m. m IN space s1 ==> (cond_prob p (PREIMAGE (Y (t + n + 2)) {m} INTER p_space p)
                 (PREIMAGE (X (t + n + 2)) {j} INTER p_space p) = 0)`  
        by (RW_TAC std_ss [] ++ MP_RW_TAC COND_PROB_ZERO ++ RW_TAC std_ss []
      	   >> METIS_TAC [thmm_def, hmm_def, PREIMAGE_X_IN_EVENTS]
      	   ++ METIS_TAC [thmm_def, hmm_def, DTMC_EVENTS])  
    ++ RW_TAC std_ss [REAL_MUL_RZERO, REAL_MUL_LZERO, REAL_SUM_IMAGE_0])
 ++ Cases_on `prob p (PREIMAGE (X t) {i} INTER p_space p) = 0`
 >> RW_TAC std_ss [REAL_MUL_LZERO, REAL_SUM_IMAGE_0] 
 ++ `!(a:real) b c d e f g. a * b * (c * d * e * f * g) = (a * c * d * e * g) * b * f`
 	by METIS_TAC [REAL_MUL_ASSOC, REAL_MUL_COMM] ++ POP_ORW
 ++ Q.ABBREV_TAC `A = prob p (PREIMAGE (X t) {i} INTER p_space p) *
              cond_prob p (PREIMAGE (X (t + 1)) {HD Lx} INTER p_space p)
                (PREIMAGE (X t) {i} INTER p_space p) *
              cond_prob p (PREIMAGE (Y (t + 1)) {HD Ly} INTER p_space p)
                (PREIMAGE (X (t + 1)) {HD Lx} INTER p_space p) *
              cond_prob p (PREIMAGE (X (t + n + 2)) {j} INTER p_space p)
                (PREIMAGE (X (t + n + 1)) {EL n Lx} INTER p_space p) *
              mulcon (1,n) (\k. cond_prob p (PREIMAGE (X (t + k + 1)) {EL k Lx} INTER p_space p)
                     (PREIMAGE (X (t + k)) {EL (k - 1) Lx} INTER p_space p) *
                   cond_prob p (PREIMAGE (Y (t + k + 1)) {EL k Ly} INTER p_space p)
                     (PREIMAGE (X (t + k + 1)) {EL k Lx} INTER p_space p))`
 ++ `SIGMA (\r. SIGMA (\m. A * cond_prob p (PREIMAGE (Y t) {r} INTER p_space p)
                (PREIMAGE (X t) {i} INTER p_space p) *
              cond_prob p (PREIMAGE (Y (t + n + 2)) {m} INTER p_space p)
                (PREIMAGE (X (t + n + 2)) {j} INTER p_space p)) (space s1)) (space s1) =
     SIGMA (\r. SIGMA (\m. A * (\r. cond_prob p (PREIMAGE (Y t) {r} INTER p_space p)
                (PREIMAGE (X t) {i} INTER p_space p)) r *
              (\m. cond_prob p (PREIMAGE (Y (t + n + 2)) {m} INTER p_space p)
                (PREIMAGE (X (t + n + 2)) {j} INTER p_space p)) m) (space s1)) (space s1)`
           by RW_TAC std_ss [] ++ POP_ORW
 ++ MP_REWRITE_TAC SIGMA_SIGMA_CMUL ++ RW_TAC std_ss []
 ++ DEP_REWRITE_TAC [COND_PROB_ADDITIVE] ++ RW_TAC std_ss [REAL_MUL_RID]
 << [METIS_TAC [thmm_def, hmm_def, DTMC_EVENTS],
     METIS_TAC [thmm_def, hmm_def, PREIMAGE_X_IN_EVENTS],
     METIS_TAC [thmm_def, hmm_def, DTMC_EVENTS, PROB_POSITIVE, REAL_LT_LE],
     RW_TAC std_ss [DISJOINT_PROC_INTER],
     PSET_TAC [thmm_def, hmm_def, BIGUNION_PREIMAGEX_IS_PSPACE, INTER_IDEMPOT],
     DEP_REWRITE_TAC [COND_PROB_ADDITIVE] ++ RW_TAC std_ss [REAL_MUL_RID]
     << [`i IN space s` by (SPOSE_NOT_THEN STRIP_ASSUME_TAC
     		++ `PREIMAGE (X t) {i} INTER p_space p = {}` 
     		by METIS_TAC [NOTIN_SPACE_EVENTS, thmm_def, hmm_def, dtmc_def, mc_property_def]
     		++ METIS_TAC [PROB_EMPTY]) ++ METIS_TAC [thmm_def, hmm_def, DTMC_EVENTS],
         METIS_TAC [thmm_def, hmm_def, PREIMAGE_X_IN_EVENTS],
         `i IN space s` by (SPOSE_NOT_THEN STRIP_ASSUME_TAC
     		++ `PREIMAGE (X t) {i} INTER p_space p = {}` 
     		by METIS_TAC [NOTIN_SPACE_EVENTS, thmm_def, hmm_def, dtmc_def, mc_property_def]
     		++ METIS_TAC [PROB_EMPTY])
         ++ METIS_TAC [thmm_def, hmm_def, DTMC_EVENTS, PROB_POSITIVE, REAL_LT_LE],
         RW_TAC std_ss [DISJOINT_PROC_INTER],
         PSET_TAC [thmm_def, hmm_def, BIGUNION_PREIMAGEX_IS_PSPACE, INTER_IDEMPOT]]]);

val IMAGE_EL_SHIFT = prove
  (``!X p i j t n Lx. (LENGTH Lx = n + 1) ==>
    (IMAGE (\k. PREIMAGE (X (t + k + 1)) {EL k Lx} INTER p_space p) (count (n + 1)) =
     IMAGE (\k. PREIMAGE (X (t + k)) {EL k (i::(Lx ++ [j]))} INTER p_space p)
         (count_mn 1 (n + 1)))``,
    PSET_TAC [IN_IMAGE, IN_COUNT, IN_COUNT_MN, EXTENSION]
 ++ EQ_TAC 
 >> (RW_TAC std_ss [] ++ Q.EXISTS_TAC `k + 1` ++ RW_TAC arith_ss []
    ++ ONCE_REWRITE_TAC [CONS_APPEND] ++ DEP_REWRITE_TAC [EL_SHIFT]
    ++ RW_TAC arith_ss [EL_APPEND1])
 ++ RW_TAC std_ss [] ++ Q.EXISTS_TAC `k - 1` ++ RW_TAC arith_ss []
 ++ ONCE_REWRITE_TAC [CONS_APPEND] ++ DEP_REWRITE_TAC [EL_SHIFT]      
 ++ RW_TAC arith_ss [EL_APPEND1]);
                          
val HMM_INTER_COMBIN = prove
  (``!X Y p s s1 Linit Ltrans (Btrans: num -> 'c -> 'b -> real) t n (Lx:'b list) (Ly:'c list) i j.
   thmm X Y p s s1 Linit Ltrans Btrans /\ (LENGTH Lx = n + 1) /\ (LENGTH Ly = n + 1) ==>
   (PREIMAGE (X (t + n + 2)) {j} INTER p_space p INTER
    BIGINTER (IMAGE (\(k:num). PREIMAGE (X (t + k + 1)) {EL k Lx} INTER p_space p)
                	(count (n + 1))) INTER 
    BIGINTER (IMAGE (\(k:num). PREIMAGE (Y (t + k + 1)) {EL k Ly} INTER p_space p)
                	(count (n + 1))) INTER PREIMAGE (X t) {i} INTER p_space p =
    BIGINTER (IMAGE (\k. PREIMAGE (X (t + k)) {EL k ([i] ++ Lx ++ [j])} INTER p_space p)
                	(count (n + 3))) INTER 
    BIGINTER (IMAGE (\(k:num). PREIMAGE (Y (t + k + 1)) {EL k Ly} INTER p_space p)
                	(count (n + 1))))``,
    RW_TAC std_ss []      
 ++ `!A B C D E G. (A INTER B INTER E INTER G INTER B = C) ==> 
 	(A INTER B INTER E INTER D INTER G INTER B = C INTER D)` 
 	by METIS_TAC [INTER_ASSOC, INTER_COMM] ++ POP_ASSUM MATCH_MP_TAC
 ++ `count (n + 3) = {n + 2} UNION count_mn 1 (n + 1) UNION {0}` 
     	by (PSET_TAC [IN_COUNT, IN_COUNT_MN, EXTENSION] ++ RW_TAC arith_ss []) ++ POP_ORW
 ++ `n + 2 = SUC (n + 1)` by RW_TAC arith_ss []     	 
 ++ `t + SUC (n + 1) = t + n + 2` by RW_TAC arith_ss []
 ++ RW_TAC std_ss [IMAGE_UNION, BIGINTER_UNION, IMAGE_SING, BIGINTER_SING, 
       	GSYM APPEND_ASSOC, GSYM CONS_APPEND, EL, HD, TL, EL_APPEND2]
 ++ `!A B C D E. (C = E) ==> 
 	(A INTER B INTER C INTER D INTER B = A INTER B INTER E INTER (D INTER B))` 
 	by METIS_TAC [INTER_ASSOC] ++ POP_ASSUM MATCH_MP_TAC
 ++ DEP_REWRITE_TAC [IMAGE_EL_SHIFT] ++ RW_TAC std_ss []);
 
val HMM_SE_PROB = prove
  (``!X Y p s s1 Linit Ltrans (Btrans: num -> 'c -> 'b -> real) t n (Lx:'b list) (Ly:'c list) i j.
   thmm X Y p s s1 Linit Ltrans Btrans /\ (LENGTH Lx = n + 1) /\ (LENGTH Ly = n + 1) ==>
   (prob p (BIGINTER (IMAGE (\k. PREIMAGE (X (t + k)) {EL k ([i] ++ Lx ++ [j])} INTER p_space p)
                	(count (n + 3))) INTER 
    	    BIGINTER (IMAGE (\(k:num). PREIMAGE (Y (t + k + 1)) {EL k Ly} INTER p_space p)
                	(count (n + 1)))) =
    prob p (PREIMAGE (X t) {i} INTER p_space p) * 
    cond_prob p (PREIMAGE (X (t + 1)) {HD Lx} INTER p_space p)
      (PREIMAGE (X t) {i} INTER p_space p) *
    cond_prob p (PREIMAGE (Y (t + 1)) {HD Ly} INTER p_space p)
      (PREIMAGE (X (t + 1)) {HD Lx} INTER p_space p) *
    cond_prob p (PREIMAGE (X (t + n + 2)) {j} INTER p_space p)
      (PREIMAGE (X (t + n + 1)) {EL n Lx} INTER p_space p) *
    mulcon (1, n) (\k. cond_prob p (PREIMAGE (X (t + k + 1)) {EL k Lx} INTER p_space p)
                        (PREIMAGE (X (t + k)) {EL (k - 1) Lx} INTER p_space p) *
                        cond_prob p (PREIMAGE (Y (t + k + 1)) {EL k Ly} INTER p_space p)
                        (PREIMAGE (X (t + k + 1)) {EL k Lx} INTER p_space p)))``,
    RW_TAC std_ss []
 ++ DEP_REWRITE_TAC [GSYM HMM_INTER_COMBIN]   
 ++ RW_TAC std_ss [] 
 >> (MAP_EVERY Q.EXISTS_TAC [`s`, `s1`,`Linit`, `Ltrans`,`Btrans`] ++ RW_TAC std_ss [])
 ++ DEP_REWRITE_TAC [HMM_SUCXX_PROB]
 ++ MAP_EVERY Q.EXISTS_TAC [`s`, `s1`,`Linit`, `Ltrans`,`Btrans`] ++ RW_TAC std_ss []);
 
val LIST_COMBIN = prove
  (``!(l:'a list) n. (LENGTH l = n + 3) ==>
    (l = [EL 0 l] ++ GENLIST (\x. EL (x + 1) l) (n + 1) ++ [EL (n + 2) l])``,
    RW_TAC std_ss []
 ++ MATCH_MP_TAC LIST_EQ 
 ++ RW_TAC arith_ss [LENGTH_APPEND, LENGTH, LENGTH_GENLIST]
 ++ Cases_on `x = 0`
 >> (RW_TAC arith_ss [GSYM APPEND_ASSOC, EL_APPEND1, LENGTH_APPEND, LENGTH]
    ++ RW_TAC std_ss [EL, HD])
 ++ Cases_on `x = n + 2`
 >> (RW_TAC arith_ss [LENGTH_GENLIST, LENGTH_APPEND, LENGTH, EL_APPEND2]
    ++ RW_TAC std_ss [EL, HD])
 ++ RW_TAC arith_ss [LENGTH_GENLIST, LENGTH_APPEND, LENGTH, EL_APPEND2, EL_APPEND1]
 ++ DEP_REWRITE_TAC [EL_GENLIST] ++ RW_TAC arith_ss []);
 
val HMM_START_END_PROB = prove
  (``!X Y p s s1 Linit Ltrans (Btrans: num -> 'c -> 'b -> real) t n (Lx:'b list) (Ly:'c list).
   thmm X Y p s s1 Linit Ltrans Btrans /\ (LENGTH Lx = n + 3) /\ (LENGTH Ly = n + 1) ==>
   (prob p (BIGINTER (IMAGE (\k. PREIMAGE (X (t + k)) {EL k Lx} INTER p_space p)
                	(count (n + 3))) INTER 
    	    BIGINTER (IMAGE (\(k:num). PREIMAGE (Y (t + k + 1)) {EL k Ly} INTER p_space p)
                	(count (n + 1)))) =
    prob p (PREIMAGE (X t) {EL 0 Lx} INTER p_space p) * 
    cond_prob p (PREIMAGE (X (t + n + 2)) {EL (n + 2) Lx} INTER p_space p)
      (PREIMAGE (X (t + n + 1)) {EL (n + 1) Lx} INTER p_space p) *
    mulcon (0, n + 1) (\k. cond_prob p (PREIMAGE (X (t + k + 1)) {EL (k + 1) Lx} INTER p_space p)
                        (PREIMAGE (X (t + k)) {EL k Lx} INTER p_space p) *
                        cond_prob p (PREIMAGE (Y (t + k + 1)) {EL k Ly} INTER p_space p)
                        (PREIMAGE (X (t + k + 1)) {EL (k + 1) Lx} INTER p_space p)))``,
    RW_TAC std_ss []
 ++ (MP_TAC o Q.ISPECL [`Lx:'b list`, `n:num`]) LIST_COMBIN ++ RW_TAC std_ss []
 ++ `BIGINTER (IMAGE (\k. PREIMAGE (X (t + k)) {EL k Lx} INTER p_space p) (count (n + 3))) =
     BIGINTER (IMAGE (\k. PREIMAGE (X (t + k)) {EL k ([EL 0 Lx] ++ 
     GENLIST (\x. EL (x + 1) Lx) (n + 1) ++ [EL (n + 2) Lx])} INTER p_space p) (count (n + 3)))`
     	by METIS_TAC [] ++ POP_ORW ++ POP_ASSUM K_TAC
 ++ DEP_REWRITE_TAC [GSYM HMM_INTER_COMBIN]   
 ++ RW_TAC std_ss [] 
 >> (MAP_EVERY Q.EXISTS_TAC [`s`, `s1`,`Linit`, `Ltrans`,`Btrans`] 
    ++ RW_TAC arith_ss [LENGTH_GENLIST, EL_GENLIST])
 ++ DEP_REWRITE_TAC [HMM_SUCXX_PROB] ++ RW_TAC std_ss []
 >> (MAP_EVERY Q.EXISTS_TAC [`s`, `s1`,`Linit`, `Ltrans`,`Btrans`] 
    ++ RW_TAC arith_ss [LENGTH_GENLIST, EL_GENLIST])
 ++ `HD (GENLIST (\x. EL (x + 1) Lx) (n + 1)) = EL 1 Lx` 
 	by (`HD (GENLIST (\x. EL (x + 1) Lx) (n + 1)) = EL 0 (GENLIST (\x. EL (x + 1) Lx) (n + 1))`
 		by RW_TAC std_ss [EL] ++ POP_ORW ++ RW_TAC arith_ss [EL_GENLIST])
 ++ `EL n (GENLIST (\x. EL (x + 1) Lx) (n + 1)) = EL (n + 1) Lx`
 	by RW_TAC arith_ss [EL_GENLIST]
 ++ RW_TAC std_ss [] ++ ONCE_REWRITE_TAC [ADD_COMM] 
 ++ RW_TAC arith_ss [GSYM MULCON_TWO, MULCON_ONE, REAL_MUL_ASSOC, EL] 	
 ++ Q.ABBREV_TAC `d = cond_prob p (PREIMAGE (X (n + (t + 2))) {EL (n + 2) Lx} INTER p_space p)
      (PREIMAGE (X (n + (t + 1))) {EL (n + 1) Lx} INTER p_space p)`
 ++ Q.ABBREV_TAC `c = cond_prob p (PREIMAGE (Y (t + 1)) {HD Ly} INTER p_space p)
      (PREIMAGE (X (t + 1)) {EL 1 Lx} INTER p_space p)`
 ++ Q.ABBREV_TAC `b = cond_prob p (PREIMAGE (X (t + 1)) {EL 1 Lx} INTER p_space p)
      (PREIMAGE (X t) {HD Lx} INTER p_space p)` 
 ++ Q.ABBREV_TAC `a = prob p (PREIMAGE (X t) {HD Lx} INTER p_space p)`            
 ++ `!(a:real) b c d e f. (e = f) ==> (a * b * c * d * e = a * d * b * c * f)`
 	by METIS_TAC [REAL_MUL_ASSOC, REAL_MUL_COMM] ++ POP_ASSUM MATCH_MP_TAC
 ++ MATCH_MP_TAC MULCON_POS_EQ ++ RW_TAC arith_ss [EL_GENLIST]);

(*======== verification of dna sequence recognition =========*)
(*========   state initial distribution function    =========*)
val _ = Hol_datatype `dna = A | G | T | C`;
val _ = Hol_datatype `state = START | E | I | FIVE | END`;

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
                                   
(*======== transition probability function of dtmc  =========*)
val dna_seq_def = Define `
    (dna_seq:dna list) = 
    [C;T;T;C;A;T;G;T;G;A;A;A;G;C;A;G;A;C;G;T;A;A;G;T;C;A]`;

val state_path_def = Define `
    (state_path:state list) = 
    [E;E;E;E;E;E;E;E;E;E;E;E;E;E;E;E;E;E;FIVE;I;I;I;I;I;I;I]`;     

val states_def = Define `
    (states:state list) = [START;E;E;E;E;E;E;E;E;E;E;E;E;E;E;E;E;E;E;FIVE;I;I;I;I;I;I;I;END]`;
(*========     definition of 5' splice dna model     =========*)     
val dna_model_def = Define `
    dna_model X Y p s s1 =
    thmm (X:num -> 'a -> state) (Y:num -> 'a -> dna) p s s1 
    	ini_distribution trans_distribution emission_distribution /\ 
    (space s = univ(:state)) /\ (space s1 = univ(:dna))`; 
          
(*======== initial probability function of dtmc for study group =========*)
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
