(* ========================================================================= *)
(*                                                                           *)
(*                      Automating HMM Computations                          *)
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
val () = app load
 ["bossLib", "metisLib", "arithmeticTheory", "pred_setTheory", "realLib", "seqTheory",
 	"pairTheory", "combinTheory", "listTheory", "rich_listTheory", "transcTheory", "numLib", 
 	"prim_recTheory", "probabilityTheory", "cond_probTheory", "extra_pred_setTools",
 	"dtmcBasicTheory", "hmmTheory", "setUsefulTheory", "satTheory", "listLib"];

set_trace "Unicode" 0;

open HolKernel Parse boolLib bossLib metisLib numLib combinTheory subtypeTheory
	pred_setTheory measureTheory listTheory rich_listTheory numLib seqTheory
     extra_pred_setTheory arithmeticTheory realTheory realLib pairTheory extra_pred_setTools
      transcTheory prim_recTheory extrealTheory probabilityTheory cond_probTheory 
      dtmcBasicTheory hmmTheory setUsefulTheory satTheory;

infixr 0 ++ << || ORELSEC ## --> THENC;
infix 1 >> |->;

val !! = REPEAT;
val op++ = op THEN;
val op<< = op THENL;
val op|| = op ORELSE;
val op>> = op THEN1;

(* ------------------------------------------------------------------------- *)
(* Powerlist Theorems                                                        *)
(* ------------------------------------------------------------------------- *)
val INTER_ASSOC = GSYM INTER_ASSOC;
val UNION_ASSOC = GSYM UNION_ASSOC;

(* PRELIMINARIES *)

val MEM_MAP_CONS = store_thm
  ("MEM_MAP_CONS",
  ``!x l. ~(MEM [] (MAP (CONS x) l)) /\ (!h t. MEM (h::t) (MAP (CONS x) l) <=> (h = x) /\ MEM t l)``,
  Induct_on `l` ++ RW_TAC std_ss [MAP,MEM] ++ METIS_TAC[]);

val NOT_APPEND_NIL = store_thm
  ("NOT_APPEND_NIL",
  ``!l1 l2 x. l1 ++ (x::l2) <> []``,
  Induct_on `l1` ++ REWRITE_TAC[APPEND,NOT_CONS_NIL]);

val NIL_MEM_MAP_APPEND = store_thm
  ("NIL_MEM_MAP_APPEND",
  ``!x l. ~(MEM [] (MAP (combin$C APPEND [x]) l))``,
  Induct_on `l` ++ RW_TAC std_ss [MAP,MEM] ++ METIS_TAC[NOT_APPEND_NIL]);

val MEM_MAP_APPEND = store_thm
  ("MEM_MAP_APPEND",
  ``!x L l. l <> [] ==> (MEM l (MAP (combin$C APPEND [x]) L) <=> (LAST l = x) /\ MEM (FRONT l) L)``,
  Induct_on `L` ++ ASM_REWRITE_TAC [MAP,MEM,C_DEF] ++ BETA_TAC
  ++ REPEAT (STRIP_TAC ORELSE EQ_TAC)
  ++ METIS_TAC[LAST_APPEND,LAST_DEF,FRONT_APPEND,FRONT_DEF,APPEND_NIL,APPEND_FRONT_LAST,NOT_CONS_NIL]);

val NON_NULL_APPEND = store_thm
  ("NON_NULL_APPEND",
  ``!x y z. ~(NULL(x ++ (y::z)))``,
  Induct_on `x` ++ REWRITE_TAC[APPEND,NULL]);

val EVERY_LAST = store_thm
  ("EVERY_LAST",
  ``!p l. l <> [] /\ EVERY p l ==> p (LAST l)``,
  Induct_on `l` ++ REWRITE_TAC[LAST_DEF,NOT_CONS_NIL,EVERY_DEF] ++ METIS_TAC[]);


(* POWER LIST formalization *)
val MULCON_ALT = store_thm
  ("MULCON_ALT",
  ``!n m f. mulcon (n,m) f = if m = 0 then 1 else mulcon (n,m-1) f * f (n + (m - 1))``,
  Cases_on `m` ++ RW_TAC arith_ss [mulcon_def]);

val power_list_def = Define
  `(power_list s f 0 = [[]]) /\
   (power_list s f (SUC n) = FLAT (MAP (\x. MAP (combin$C APPEND [x]) (power_list s f n)) (FILTER (f n) s)))`;

val POWER_LIST_ALT = store_thm
  ("POWER_LIST_ALT",
  ``!s f n. power_list s f n = if n = 0 then [[]] else FLAT (MAP (\x. MAP (combin$C APPEND [x]) (power_list s f (n-1))) (FILTER (f (n-1)) s))``,
  Cases_on `n` ++ RW_TAC arith_ss [power_list_def]);

(*
 *val power_list_example = ``power_list [A;G;T] (\n x. ~((x=A) /\ (n=0) \/ (x=G) /\ (n=1) \/ (x=T) /\ (n=2))) (SUC (SUC (SUC 0)))``;
 *
 *val POWER_LIST_CONV =
 *  REWRITE_CONV[power_list_def,FILTER] THENC REDUCE_CONV THENC REWRITE_CONV (type_rws ``:dna``)
 *  THENC REWRITE_CONV[MAP,FLAT,C_DEF] THENC DEPTH_CONV BETA_CONV THENC REWRITE_CONV[FLAT,MAP,APPEND];
 *)
(*fun PRINT_CONV s t = (print (s ^ term_to_string t ^ "\n\n"); ALL_CONV t);*)

fun ARITH_PROVE_CONV t = EQT_INTRO (ARITH_PROVE t) handle _ => EQF_INTRO
  (ARITH_PROVE (mk_neg t));

fun POWER_LIST_CONV fconv t =
  TRY_CONV
    (CHANGED_CONV (ONCE_REWRITE_CONV [power_list_def])
    THENC DEPTH_CONV (listLib.FILTER_CONV (
    DEPTH_CONV BETA_CONV THENC fconv THENC ARITH_PROVE_CONV))
    THENC POWER_LIST_CONV fconv
    THENC DEPTH_CONV (listLib.MAP_CONV 
     (BETA_CONV THENC listLib.MAP_CONV
      (REWR_CONV C_THM THENC listLib.APPEND_CONV)))
    THENC REWRITE_CONV [FLAT]
    THENC DEPTH_CONV listLib.APPEND_CONV) t;

val NIL_MEM_POWER_LIST = store_thm
  ("NIL_MEM_POWER_LIST",
  ``!s f n. MEM [] (power_list s f n) <=> (n = 0)``,
  REPEAT (STRIP_TAC ORELSE EQ_TAC) ++ RW_TAC list_ss [power_list_def] ++ Induct_on `n`
  ++ RW_TAC std_ss [power_list_def,MEM_FLAT,MEM_MAP,MEM_FILTER] ++ METIS_TAC[NIL_MEM_MAP_APPEND]);

val MEM_POWER_LIST_LAST_FRONT = store_thm
  ("MEM_POWER_LIST_LAST_FRONT",
  ``!s n f l. l <> [] ==> (MEM l (power_list s f (SUC n)) <=> MEM (LAST l) s /\ f n (LAST l) /\ MEM (FRONT l) (power_list s f n))``,
  REWRITE_TAC[power_list_def] ++ REPEAT STRIP_TAC ++ EQ_TAC
  >> (Q.SPEC_TAC (`power_list s f n`,`xss`) ++ Induct_on `s` ++ RW_TAC std_ss [FILTER,MAP,FLAT,MEM,MEM_APPEND] ++ METIS_TAC[MEM_MAP_APPEND])
  >> (RW_TAC std_ss [MEM_FLAT,MEM_MAP,MEM_FILTER] ++ METIS_TAC[MEM_MAP_APPEND]));

val POWER_LIST_EL_LENGTH = store_thm
  ("POWER_LIST_EL_LENGTH",
  ``!s f n x. MEM x (power_list s f n) ==> (LENGTH x = n)``,
  Induct_on `n`
  >> REWRITE_TAC[power_list_def,LENGTH_NIL,MEM]
  >> (REPEAT GEN_TAC ++ Q.ASM_CASES_TAC `x = []`
    >> ASM_REWRITE_TAC[NIL_MEM_POWER_LIST,numTheory.NOT_SUC]
    >> (RW_TAC std_ss [MEM_POWER_LIST_LAST_FRONT] ++ FIRST_ASSUM (fn x => ONCE_REWRITE_TAC[GSYM (MATCH_MP APPEND_BUTLAST_LAST x)]) 
    ++ RW_TAC std_ss [LENGTH_APPEND,LENGTH,ARITH_PROVE ``(x+1 = SUC y) <=> (x=y)``] ++ METIS_TAC[])));

val LENGTH_APPEND_FRONT_LAST = store_thm
  ("LENGTH_APPEND_FRONT_LAST",
  ``!n L. (LENGTH L = SUC n) <=> (L = FRONT L ++ [LAST L]) /\ (LENGTH (FRONT L) = n)``,
  REPEAT GEN_TAC THEN EQ_TAC
  >> METIS_TAC[LENGTH_NIL,numTheory.NOT_SUC,APPEND_FRONT_LAST,LENGTH_CONS,LENGTH_FRONT_CONS]
  >> METIS_TAC[LENGTH_APPEND,LENGTH,ARITH_PROVE ``n + SUC 0 = SUC n``]);

val POWER_LIST_SPEC_LEMMA = store_thm
  ("POWER_LIST_SPEC_LEMMA",
  ``!P s n. {L | EVERY (\x. x IN s) L /\ (LENGTH L = SUC n) /\ !m. m < SUC n ==> P m (EL m L)} =
    IMAGE (\(L,x). L ++ [x])
      ({L | EVERY (\x. x IN s) L /\ (LENGTH L = n) /\ !m. m < n ==> P m (EL m L)}
      CROSS
      {x | x IN s /\ P n x})``,
    REWRITE_TAC[EXTENSION,GSPECIFICATION,IN_CROSS,IN_IMAGE] ++ BETA_TAC ++ REWRITE_TAC[PAIR_EQ] ++ REPEAT (STRIP_TAC ORELSE EQ_TAC)
    >> (FIRST_ASSUM (ASSUME_TAC o MATCH_MP (METIS_PROVE[LENGTH_EQ_NUM,NOT_CONS_NIL] ``(LENGTH x = SUC y) ==> x <> []``))
    ++ Q.EXISTS_TAC `(FRONT x,LAST x)` ++ FULL_SIMP_TAC std_ss [IN_DEF]
    ++ METIS_TAC[IN_DEF,LENGTH_APPEND_FRONT_LAST,EVERY_APPEND,LESS_SUC,REWRITE_RULE[NULL_EQ] EL_FRONT,EVERY_LAST,EL_PRE_LENGTH,LESS_SUC_REFL,PRE])
    >> (Q.EXISTS_TAC `FST x' ++ [SND x']` ++ RW_TAC arith_ss [LENGTH_APPEND,EVERY_APPEND,LENGTH,EVERY_DEF]
      >> (ONCE_REWRITE_TAC[GSYM PAIR] ++ RW_TAC std_ss[])
      >> METIS_TAC[ARITH_PROVE ``m < SUC n ==> m < n \/ (m = n)``,EL_APPEND1,REWRITE_RULE[NULL_EQ] EL_LENGTH_APPEND,NOT_CONS_NIL,HD]));

val POWER_LIST_SPEC = store_thm
  ("POWER_LIST_SPEC",
  ``!n l P. { L | EVERY (\x. x IN (set l)) L /\ (LENGTH L = n) /\ !m. m < n ==> P m (EL m L) } = set (power_list l P n)``,
  Induct_on `n`
  >> RW_TAC list_ss [LENGTH_NIL,power_list_def,NOT_LESS_0,METIS_PROVE[] ``P x /\ (x = []) <=> P [] /\ (x = [])``,EXTENSION,IN_SING,GSPECIFICATION]
  >> (ASM_REWRITE_TAC[BETA_RULE POWER_LIST_SPEC_LEMMA]
  ++ RW_TAC std_ss [EXTENSION,IN_IMAGE,IN_LIST_TO_SET,IN_CROSS,GSPECIFICATION] ++ EQ_TAC
    >> (RW_TAC std_ss [] ++ MATCH_MP_TAC (MATCH_MP (METIS_PROVE[] ``(P ==> (Q <=> R)) ==> (P /\ R ==> Q)``) (SPEC_ALL MEM_POWER_LIST_LAST_FRONT))
    ++ ONCE_REWRITE_TAC[GSYM PAIR] ++ RW_TAC std_ss[NOT_APPEND_NIL,LAST_APPEND,LAST_DEF,FRONT_APPEND,FRONT_DEF,APPEND_NIL])
    >> (Q.ASM_CASES_TAC `x=[]` ++ RW_TAC std_ss [NIL_MEM_POWER_LIST,MEM_POWER_LIST_LAST_FRONT]
    ++ Q.EXISTS_TAC `(FRONT x,LAST x)` ++ RW_TAC std_ss [APPEND_FRONT_LAST])));
                  		    
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

(*======== verification of dna sequence recognition =========*)

(*======== initial probability function of dtmc for study group =========*)
fun def_nth_conj i def = List.nth (strip_conj (rhs (concl (SPEC_ALL def))), i-1);

fun DEF_NTH_CONJS is def =
  GEN_ALL (prove(mk_imp(lhs (concl (SPEC_ALL def)),list_mk_conj (List.map (fn i => def_nth_conj i def) is)),SIMP_TAC std_ss [def]));;

val COUNT_LE = store_thm
  ("COUNT_LE",
  ``!n. count (n+1) = \m. m <= n``,
  RW_TAC arith_ss [FUN_EQ_THM,count_def] );

val RVS_EVENTS = store_thm
  ("RVS_EVENTS",
  ``!(X:num -> 'a -> 'c) p s t j. 
        (!t. random_variable (X t) p s) /\  (!x. x IN space s ==> {x} IN subsets s)
        ==> (PREIMAGE (X t) {j} INTER p_space p) IN events p``,
    RW_TAC std_ss []
 ++ Cases_on `j NOTIN space s`
 >> (DEP_REWRITE_TAC [NOTIN_SPACE_EVENTS,EVENTS_EMPTY]
    ++ RW_TAC std_ss []
    >> (Q.EXISTS_TAC `s` ++ RW_TAC std_ss [])
    ++ PSET_TAC [random_variable_def, IN_MEASURABLE, space_def, subsets_def])
 ++ `{j} IN subsets s` by METIS_TAC []    
 ++ NTAC 3 (POP_ASSUM MP_TAC) 
 ++ POP_ASSUM (MP_TAC o Q.SPEC `t`) 
 ++ PSET_TAC [random_variable_def, IN_MEASURABLE, space_def, subsets_def]);

val MULCON_TRE_SING = store_thm
  ("MULCON_TRE_SING",
  ``!(f:num -> real) n k. k < n ==> 
        (mulcon (0, n) f = mulcon (0, k) f * (f k) * mulcon (k + 1, n - k - 1) f)``,
    RW_TAC std_ss []
 ++ (MP_TAC o GSYM o Q.SPECL [`f`, `k`, `n - k`]) MULCON_TWO
 ++ RW_TAC arith_ss []
 ++ (MP_TAC o GSYM o Q.SPECL [`f`, `k`, `n - k - 1`, `1`]) MULCON_EQ_MUL_TWO
 ++ RW_TAC arith_ss [GSYM REAL_MUL_ASSOC, MULCON_1]);
 
val HOMO_PROPERTY = store_thm
  ("HOMO_PROPERTY",
  ``!(X:num -> 'a -> 'b) p s Linit Ltrans i j n t. 
        th_dtmc X p s Linit Ltrans ==> 
        (Trans X p s t 1 i j = Trans X p s n 1 i j)``,
    RW_TAC std_ss [th_dtmc_def, dtmc_def]
 ++ Induct_on `n` 
 >> (Induct_on `t` >> RW_TAC std_ss []       
    ++ RW_TAC std_ss [ADD1])
 ++ RW_TAC std_ss [ADD1]);
  
val HMM_JOINT_PROB_CONCRETE = store_thm
  ("HMM_JOINT_PROB_CONCRETE",
  ``!n Lx Ly p0 pij pXY X Y p Sx Sy.
    thmm (X:num -> 'a -> 'b) (Y:num -> 'a -> 'c) p Sx Sy p0 pij pXY /\ 
    (!k. k < n /\ (prob p (PREIMAGE (X k) {EL k Lx} INTER p_space p) = 0) ==> 
    	(pij k (EL k Lx) (EL (k + 1) Lx) = 0)) /\ 
    (!k. k <= n /\ (prob p (PREIMAGE (X k) {EL k Lx} INTER p_space p) = 0) ==> 
    	(pXY k (EL k Ly) (EL k Lx) = 0)) ==>
    (prob p (BIGINTER (IMAGE (\(k:num). PREIMAGE (X k) {EL k Lx} INTER p_space p) (\m. m <= n))
      INTER BIGINTER (IMAGE (\(k:num). PREIMAGE (Y k) {EL k Ly} INTER p_space p) (\m. m <= n)))
    =
    p0 (EL 0 Lx) * pXY 0 (EL 0 Ly) (EL 0 Lx) *
    mulcon (0,n) (\k. pij k (EL k Lx) (EL (k + 1) Lx) *
      pXY (k + 1) (EL (k + 1) Ly) (EL (k + 1) Lx)))``,
    RW_TAC std_ss [GSYM COUNT_LE]
 ++ `prob_space p` by PSET_TAC [thmm_def, hmm_def, dtmc_def, mc_property_def, random_variable_def] 
 ++ Cases_on `?k. k < n /\ (prob p (PREIMAGE (X k) {EL k Lx} INTER p_space p) = 0)`
 >> (RW_TAC std_ss [] 
    ++ `(pij k (EL k Lx) (EL (k + 1) Lx) = 0) /\ (pXY k (EL k Ly) (EL k Lx) = 0)`
    	by FULL_SIMP_TAC arith_ss [] 
    ++ DEP_REWRITE_TAC [MULCON_TRE_SING]    	
    ++ RW_TAC std_ss [REAL_MUL_LZERO, REAL_MUL_RZERO, GSYM REAL_LE_ANTISYM]
    >> (NTAC 2 (POP_ASSUM K_TAC) ++ POP_ASSUM (MP_TAC o GSYM)
       ++ RW_TAC std_ss []
       ++ MATCH_MP_TAC PROB_INCREASING
       ++ RW_TAC std_ss []
       << [MATCH_MP_TAC EVENTS_INTER ++ RW_TAC std_ss []
          >> (`BIGINTER (IMAGE (\k. PREIMAGE (X k) {EL k Lx} INTER p_space p)
                     (count (n + 1))) =
               BIGINTER (IMAGE (\k. (\k. PREIMAGE (X k) {EL k Lx} INTER p_space p) k)
                         (count (SUC n)))` by RW_TAC arith_ss [ADD1] ++ POP_ORW
             ++ MATCH_MP_TAC EVENTS_BIGINTER ++ RW_TAC std_ss [IN_FUNSET, IN_COUNT]
             ++ Cases_on `EL k' Lx NOTIN (space Sx)`
             >> (`PREIMAGE (X k') {EL k' Lx} INTER p_space p = {}`
                        by (MATCH_MP_TAC NOTIN_SPACE_EVENTS 
                           ++ Q.EXISTS_TAC `Sx` 
                           ++ PSET_TAC [thmm_def, hmm_def, dtmc_def, mc_property_def])
                  ++ RW_TAC std_ss [] ++ MATCH_MP_TAC EVENTS_EMPTY
                  ++ RW_TAC std_ss [])
             ++ MATCH_MP_TAC DTMC_EVENTS
             ++ MAP_EVERY Q.EXISTS_TAC [`Sx`, `p0`, `pij`]
             ++ PSET_TAC [thmm_def, hmm_def])               
          ++ `BIGINTER (IMAGE (\k. PREIMAGE (Y k) {EL k Ly} INTER p_space p)
                         (count (n + 1))) =
              BIGINTER (IMAGE (\k. (\k. PREIMAGE (Y k) {EL k Ly} INTER p_space p) k)
                         (count (SUC n)))` by RW_TAC arith_ss [ADD1] ++ POP_ORW
          ++ MATCH_MP_TAC EVENTS_BIGINTER ++ RW_TAC std_ss [IN_FUNSET, IN_COUNT]
          ++ Cases_on `EL k' Ly NOTIN (space Sy)`
          >> (`PREIMAGE (Y k') {EL k' Ly} INTER p_space p = {}`
             by (MATCH_MP_TAC NOTIN_SPACE_EVENTS 
                ++ Q.EXISTS_TAC `Sy` 
                ++ PSET_TAC [thmm_def, hmm_def, dtmc_def, mc_property_def])
             ++ RW_TAC std_ss [] ++ MATCH_MP_TAC EVENTS_EMPTY
             ++ RW_TAC std_ss [])
          ++ MATCH_MP_TAC RVS_EVENTS
          ++ Q.EXISTS_TAC `Sy` ++ PSET_TAC [thmm_def, hmm_def],
          
          Cases_on `EL k Lx NOTIN (space Sx)`
          >> (`PREIMAGE (X k) {EL k Lx} INTER p_space p = {}`
                        by (MATCH_MP_TAC NOTIN_SPACE_EVENTS 
                           ++ Q.EXISTS_TAC `Sx` 
                           ++ PSET_TAC [thmm_def, hmm_def, dtmc_def, mc_property_def])
             ++ RW_TAC std_ss [] ++ MATCH_MP_TAC EVENTS_EMPTY
             ++ RW_TAC std_ss [])
          ++ MATCH_MP_TAC DTMC_EVENTS
          ++ MAP_EVERY Q.EXISTS_TAC [`Sx`, `p0`, `pij`]
          ++ PSET_TAC [thmm_def, hmm_def],
          
          `BIGINTER (IMAGE (\k. PREIMAGE (X k) {EL k Lx} INTER p_space p) 
                 (count (n + 1))) SUBSET (PREIMAGE (X k) {EL k Lx} INTER p_space p)`
                by (`PREIMAGE (X k) {EL k Lx} INTER p_space p =
                        (\m. PREIMAGE (X m) {EL m Lx} INTER p_space p) k` by RW_TAC std_ss []
                   ++ POP_ORW
                   ++ MATCH_MP_TAC BIGINTER_SUBSET_SING
                   ++ RW_TAC arith_ss [IN_COUNT])
          ++ MATCH_MP_TAC SUBSET_TRANS
          ++ Q.EXISTS_TAC `BIGINTER (IMAGE (\k. PREIMAGE (X k) {EL k Lx} INTER p_space p)
               (count (n + 1)))` ++ RW_TAC std_ss [INTER_SUBSET]])
               
     ++ MATCH_MP_TAC PROB_POSITIVE
     ++ RW_TAC std_ss []
     ++ MATCH_MP_TAC EVENTS_INTER
     ++ RW_TAC std_ss [GSYM ADD1]
     >> (`IMAGE (\k. PREIMAGE (X k) {EL k Lx} INTER p_space p) (count (SUC n)) =
               IMAGE (\k. (\k. PREIMAGE (X k) {EL k Lx} INTER p_space p) k) (count (SUC n))`
               by RW_TAC std_ss [] ++ POP_ORW ++ MATCH_MP_TAC EVENTS_BIGINTER
              ++ RW_TAC std_ss [IN_FUNSET, IN_COUNT]
    	      ++ MATCH_MP_TAC DTMC_EVENTS
              ++ MAP_EVERY Q.EXISTS_TAC [`Sx`, `p0`, `pij`]
    	      ++ PSET_TAC [thmm_def, hmm_def])
     ++ `IMAGE (\k. PREIMAGE (Y k) {EL k Ly} INTER p_space p) (count (SUC n)) =
         IMAGE (\k. (\k. PREIMAGE (Y k) {EL k Ly} INTER p_space p) k) (count (SUC n))`
               by RW_TAC std_ss [] ++ POP_ORW ++ MATCH_MP_TAC EVENTS_BIGINTER
     ++ RW_TAC std_ss [IN_FUNSET, IN_COUNT]
     ++ MATCH_MP_TAC RVS_EVENTS
     ++ Q.EXISTS_TAC `Sy`
     ++ PSET_TAC [thmm_def, hmm_def])
 ++ (MP_TAC o Q.SPECL [`X`, `Y`, `p`, `Sx`, `Sy`, `p0`, `pij`, `pXY`, `0`, `n`, `Lx`, `Ly`])
 	HMM_JOINT_PROB ++ PSET_TAC [thmm_def] ++ POP_ASSUM K_TAC
 ++ Cases_on `prob p (PREIMAGE (X 0) {EL 0 Lx} INTER p_space p) = 0`
 >> RW_TAC std_ss [REAL_MUL_LZERO, REAL_MUL_RZERO] 
 ++ Suff `(prob p (PREIMAGE (X 0) {EL 0 Lx} INTER p_space p) = p0 (EL 0 Lx)) /\
 	(cond_prob p (PREIMAGE (Y 0) {EL 0 Ly} INTER p_space p)
      (PREIMAGE (X 0) {EL 0 Lx} INTER p_space p) = pXY 0 (EL 0 Ly) (EL 0 Lx))`
 >> (RW_TAC std_ss []
    ++ `!(x:real) y z w. (z = w) ==> (x * y * z = x * y * w)` by RW_TAC std_ss []
    ++ POP_ASSUM MATCH_MP_TAC
    ++ MATCH_MP_TAC MULCON_POS_EQ
    ++ RW_TAC std_ss []
    ++ Cases_on `prob p (PREIMAGE (X (r + 1)) {EL (r + 1) Lx} INTER p_space p) = 0`  
    >> (NTAC 7 (POP_ASSUM MP_TAC) ++ POP_ASSUM (MP_TAC o Q.SPEC `r + 1`)
       ++ RW_TAC std_ss [] ++ FULL_SIMP_TAC arith_ss []
       ++ `cond_prob p (PREIMAGE (Y (r + 1)) {EL (r + 1) Ly} INTER p_space p)
      		(PREIMAGE (X (r + 1)) {EL (r + 1) Lx} INTER p_space p) = 0`
      		by (MATCH_MP_TAC COND_PROB_ZERO ++ RW_TAC std_ss []
      		   >> (MATCH_MP_TAC RVS_EVENTS ++ RW_TAC std_ss []
      		      ++ Q.EXISTS_TAC `Sy`
      		      ++ PSET_TAC [hmm_def, dtmc_def, mc_property_def])
      		   ++ MATCH_MP_TAC DTMC_EVENTS
      		   ++ MAP_EVERY Q.EXISTS_TAC [`Sx`, `p0`, `pij`]
      		   ++ PSET_TAC [hmm_def])
       ++ RW_TAC std_ss [REAL_MUL_RZERO])
    ++ PSET_TAC [hmm_def, distribution_def]
    ++ POP_ASSUM_LIST (MAP_EVERY STRIP_ASSUME_TAC)       
    ++ FIRST_ASSUM (MP_TAC o Q.SPECL [`r + 1`, `EL (r + 1) Ly`, `EL (r + 1) Lx`])
    ++ RW_TAC std_ss [] 
    ++ `!(x:real) y z. (x = y) ==> (x * z = y * z)` by RW_TAC std_ss []
    ++ POP_ASSUM MATCH_MP_TAC
    ++ POP_ASSUM K_TAC
    ++ `prob p (PREIMAGE (X r) {EL r Lx} INTER p_space p) <> 0` 
    	by (NTAC 11 (POP_ASSUM K_TAC) ++ METIS_TAC []) 
    ++ `pij r (EL r Lx) (EL (r + 1) Lx) = Trans X p Sx r 1 (EL r Lx) (EL (r + 1) Lx)`
    	by PSET_TAC [dtmc_def, distribution_def] ++ POP_ORW
    	    	
    ++ PSET_TAC [dtmc_def, distribution_def] ++ POP_ASSUM MP_TAC
    ++ POP_ASSUM (MP_TAC o Q.SPECL [`EL r Lx`, `EL (r + 1) Lx`, `r`])
    ++ RW_TAC std_ss [] ++ POP_ASSUM MP_TAC ++ POP_ASSUM K_TAC
    ++ RW_TAC std_ss []
    ++ `EL r Lx IN space Sx` by
 	(SPOSE_NOT_THEN STRIP_ASSUME_TAC 
 	++ `PREIMAGE (X r) {EL r Lx} INTER p_space p = {}`
 		by (POP_ASSUM MP_TAC ++ POP_ASSUM K_TAC ++ RW_TAC std_ss []
 		   ++ MATCH_MP_TAC NOTIN_SPACE_EVENTS
 		   ++ Q.EXISTS_TAC `Sx`
 		   ++ PSET_TAC [dtmc_def, mc_property_def])
 	++ METIS_TAC [PROB_EMPTY])
    ++ `EL (r + 1) Lx IN space Sx` by
 	(SPOSE_NOT_THEN STRIP_ASSUME_TAC 
 	++ `PREIMAGE (X (r + 1)) {EL (r + 1) Lx} INTER p_space p = {}`
 		by (POP_ASSUM MP_TAC ++ POP_ASSUM K_TAC ++ RW_TAC std_ss []
 		   ++ MATCH_MP_TAC NOTIN_SPACE_EVENTS
 		   ++ Q.EXISTS_TAC `Sx`
 		   ++ PSET_TAC [dtmc_def, mc_property_def])
 	++ METIS_TAC [PROB_EMPTY])
    ++ RW_TAC std_ss [Trans_def])    
 ++ PSET_TAC [thmm_def, hmm_def, dtmc_def, distribution_def]
 ++ `EL 0 Lx IN space Sx` by
 	(SPOSE_NOT_THEN STRIP_ASSUME_TAC 
 	++ `PREIMAGE (X 0) {EL 0 Lx} INTER p_space p = {}`
 		by (POP_ASSUM MP_TAC ++ POP_ASSUM K_TAC ++ RW_TAC std_ss []
 		   ++ MATCH_MP_TAC NOTIN_SPACE_EVENTS
 		   ++ Q.EXISTS_TAC `Sx`
 		   ++ PSET_TAC [mc_property_def])
 	++ METIS_TAC [PROB_EMPTY])
 ++ POP_ASSUM_LIST (MAP_EVERY STRIP_ASSUME_TAC) ++ NTAC 2 (POP_ASSUM K_TAC)       
 ++ POP_ASSUM (MP_TAC o Q.SPEC `EL 0 Lx`)
 ++ RW_TAC std_ss []);
 
(* Automation *)

fun sml_of_hol_real_op t =
  if t = ``($*):real->real->real`` then Real.*
  else if t = ``($+):real->real->real`` then Real.+
  else if t = ``($/):real->real->real`` then Real./
  else if t = ``($-):real->real->real`` then Real.-
  else failwith "Unrecognized HOL operator";

fun sml_of_hol_real t =
  let val failstring = "Symbolic expression could not be translated in a number" in
    case strip_comb t of 
       (f,[a1,a2]) => sml_of_hol_real_op f (sml_of_hol_real a1,sml_of_hol_real a2)
       | (f,[a]) =>
           if f = ``($&):num -> real``
           then Arbnum.toReal (dest_numeral a)
           else failwith failstring
       | _ => failwith failstring
  end;

val hmm_joint_distribution =
  let
    val type_check_term = ``\i t e bs cs (n:num). (i (HD bs), t (0:num) (HD bs) (HD bs), e (0:num) (HD cs) (HD bs)) :real#real#real``
    fun LENGTH_of l = mk_comb(mk_const("LENGTH",type_of l --> num),l)
    fun is_head_EL t = fst (dest_const (fst (strip_comb t))) = "EL" handle _ => false
  in
  fn p0 => fn pij => fn pXY => fn Lx => fn Ly => fn n =>
    let
      val n_thm = GSYM (REPEATC (DEPTH_CONV num_CONV) (term_of_int n))
        handle _ => failwith "The considered length should be a positive number"
      val hol_n = lhs (concl n_thm)
      val _ = list_mk_icomb(type_check_term,[p0,pij,pXY,Lx,Ly,hol_n])
        handle _ => failwith "Input has incompatible types"
      fun less_LENGTH (Li,i) =
        prove(mk_less(hol_n,LENGTH_of Li),REWRITE_TAC[LENGTH,LESS_MONO_EQ,LESS_0])
        handle _ => failwith ("The last argument should be strictly smaller than the length of the " ^ i ^ " list")
      val specialization = (UNDISCH_ALL o REWRITE_RULE[AND_IMP] o SPEC_ALL o ISPECL [hol_n,Lx,Ly,p0,pij,pXY]) HMM_JOINT_PROB_CONCRETE
      val simplified_assumptions = itlist PROVE_HYP (map less_LENGTH [(Lx,"first"),(Ly,"second")]) specialization
      val computation =
        (CONV_RULE (SIMP_CONV std_ss (pair_case_thm :: type_rws ``:dna`` @ type_rws ``:state``)) o
        CONV_RULE (DEPTH_CONV (fst (Cache.CACHE (is_head_EL,REWRITE_CONV)) [EL,HD,TL])) o
        REWRITE_RULE[GSYM ADD1] o BETA_RULE o REWRITE_RULE[LENGTH,SUC_SUB1,mulcon_def,ADD
        ]) simplified_assumptions
      val value = sml_of_hol_real (rhs (concl computation))
      val cosmetic = UNDISCH_ALL (REWRITE_RULE[n_thm(*,JOINT_PROB_ASSUM_TAKE*)] (DISCH_ALL computation))
    in
      print "Under the following assumptions:\n";
      print (String.concat (map (fn t => term_to_string t ^ "\n\n") (hyp cosmetic)));
      print "The joint probability is defined as follows (proved by HOL4):\n\n";
      print (term_to_string (concl cosmetic));
      print "\n\n";
      print "Approximate value (computed by SML from the exact value):\n";
      print (Real.toString value ^ "\n");
      print "and its logarithm:\n";
      print (Real.toString (Math.ln value) ^ "\n\n")
    end
  end;
     

 
(* Second property *)

val real_max_lemma = prove
  (``!s:real->bool. FINITE s ==> ~(s = {}) ==> ?x. x IN s /\ !y. y IN s ==> y <= x``,
  pred_setLib.SET_INDUCT_TAC ++ REWRITE_TAC[NOT_INSERT_EMPTY] ++ Cases_on `s = {}`
  >> RW_TAC pset_elt_ss [REAL_LE_REFL]
  >> (FIRST_X_ASSUM (CHANGED_TAC o IMP_RES_TAC) ++ Cases_on `e <= x`
    >> (Q.EXISTS_TAC `x` ++ PSET_TAC[])
    >> (Q.EXISTS_TAC `e` ++ PSET_TAC[REAL_LE_REFL]
      ++ METIS_TAC[REAL_ARITH ``x<=y /\ ~(z<=y:real) ==> x<=z``])));

val REAL_MAX_SET_DEF = new_specification 
  ("REAL_MAX_SET_DEF", ["REAL_MAX_SET"],
  SIMP_RULE bool_ss [AND_IMP_INTRO, GSYM RIGHT_EXISTS_IMP_THM,
                     SKOLEM_THM] real_max_lemma);

val REAL_MAX_SET_THM = store_thm
  ("REAL_MAX_SET_THM",
  ``(!e. REAL_MAX_SET {e} = e) /\
    (!s. FINITE s ==> !e1 e2.
      REAL_MAX_SET (e1 INSERT e2 INSERT s) = max e1 (REAL_MAX_SET (e2 INSERT s)))``,
  REWRITE_TAC[REWRITE_RULE[FINITE_SING,NOT_INSERT_EMPTY,IN_SING]
    (Q.SPEC `{e}` REAL_MAX_SET_DEF)]
  ++ !!STRIP_TAC ++ FIRST_ASSUM (STRIP_ASSUME_TAC o MATCH_MP (
    (REWRITE_RULE[FINITE_INSERT,NOT_INSERT_EMPTY] o Q.SPEC `e2 INSERT s`) REAL_MAX_SET_DEF))
  ++ FIRST_ASSUM (STRIP_ASSUME_TAC o MATCH_MP ((ONCE_REWRITE_RULE[IN_INSERT]
    o REWRITE_RULE[FINITE_INSERT,NOT_INSERT_EMPTY] o Q.SPEC `e1 INSERT e2 INSERT
    s`) REAL_MAX_SET_DEF))
  ++ METIS_TAC[REAL_MAX_ALT,REAL_LE_ANTISYM,REAL_LE_TRANS,max_def]);

val MAX_SELF = store_thm
  ("MAX_SELF",
  ``!x y:real. ((x = max x y) <=> y <= x) /\ ((y = max x y) <=> x <= y)``,
  RW_TAC std_ss [max_def] ++ POP_ASSUM MP_TAC ++ REAL_ARITH_TAC);

val REAL_MAX_LT = store_thm
  ("REAL_MAX_LT",
  ``!z x y:real. max x y < z <=> x < z /\ y < z``,
  RW_TAC std_ss [max_def] ++ POP_ASSUM MP_TAC ++ REAL_ARITH_TAC);

val COMPUTE_REAL_MAX_SET = store_thm
  ("COMPUTE_REAL_MAX_SET",
  ``!h t. REAL_MAX_SET (set (h::t)) =
    FOLDL (\acc x. if acc < x then x else acc) h t``,
  Induct_on `t`
  ++ FULL_SIMP_TAC std_ss [LIST_TO_SET_THM,FOLDL,REAL_MAX_SET_THM]
  ++ POP_ASSUM (fn x => REWRITE_TAC[GSYM x])
  ++ RW_TAC std_ss [FINITE_LIST_TO_SET,FINITE_INSERT,REAL_MAX_SET_THM,max_def]
  >> (Cases_on `t`
    >> FULL_SIMP_TAC std_ss [LIST_TO_SET_THM,REAL_MAX_SET_THM,REAL_NOT_LT,GSYM REAL_LE_ANTISYM]
    >> (FULL_SIMP_TAC std_ss [LIST_TO_SET_THM,REAL_MAX_SET_THM,FINITE_LIST_TO_SET,FINITE_INSERT,max_def]
      ++ RW_TAC std_ss [max_def]
      >> FULL_SIMP_TAC std_ss [max_def]
      >> ASSUM_LIST (fn xs => METIS_TAC [REAL_ARITH (mk_neg (concl (itlist CONJ xs TRUTH)))])
      >> (FULL_SIMP_TAC std_ss [max_def] ++ !!(POP_ASSUM MP_TAC) ++ REAL_ARITH_TAC)))
  >> (`h <= REAL_MAX_SET (h INSERT set t)` by METIS_TAC[FINITE_INSERT,FINITE_LIST_TO_SET,REAL_MAX_SET_DEF,COMPONENT,NOT_INSERT_EMPTY]
    ++ METIS_TAC[REAL_LT_ANTISYM,REAL_LET_TRANS,REAL_NOT_LE])
  >> (Cases_on `t` ++ FULL_SIMP_TAC std_ss [LIST_TO_SET_THM,REAL_MAX_SET_THM,
    FINITE_LIST_TO_SET,FINITE_INSERT,MAX_SELF,REAL_NOT_LE,REAL_MAX_LT]
  ++ !!(POP_ASSUM MP_TAC) ++ REAL_ARITH_TAC));

val REAL_MAXIMA_SET_DEF = new_definition
  ("REAL_MAXIMA_SET_DEF",
  ``REAL_MAXIMA_SET f s = { x | x IN s /\ (f x = REAL_MAX_SET (IMAGE f s)) }``);

val COMPUTE_REAL_MAXIMA_SET = store_thm
  ("COMPUTE_REAL_MAXIMA_SET",
  ``!f l.
    (REAL_MAXIMA_SET f (set l) =
    let fl = MAP f l in
    let m = REAL_MAX_SET (set fl) in
    (set o FST o UNZIP o FILTER (\(x,fx). fx = m) o ZIP) (l,fl))``,
  RW_TAC std_ss [LET_DEF,REAL_MAXIMA_SET_DEF,EXTENSION,GSPECIFICATION,IN_LIST_TO_SET,LIST_TO_SET_MAP]
  ++ Q.SPEC_TAC (`REAL_MAX_SET (IMAGE f (set l))`,`v`)
  ++ Induct_on `l` ++ RW_TAC list_ss [] ++ METIS_TAC []);

val IMAGE_EQ_FUN = store_thm
  ("IMAGE_EQ_FUN",
  ``!f g s. (!x. x IN s ==> (f x = g x)) ==> (IMAGE f s = IMAGE g s)``,
  RW_TAC pset_ss [IMAGE_DEF,EXTENSION] ++ METIS_TAC[]);

val REAL_MAXIMA_SET_EQ_FUN = store_thm
  ("REAL_MAXIMA_SET_EQ_FUN",
  ``!f g s. (!x. x IN s ==> (f x = g x)) ==> (REAL_MAXIMA_SET f s = REAL_MAXIMA_SET g s)``,
  RW_TAC pset_ss [REAL_MAXIMA_SET_DEF,EXTENSION] ++ METIS_TAC[IMAGE_EQ_FUN]);  
    
val COMPUTE_BEST_STATE_PATH = store_thm
  ("COMPUTE_BEST_STATE_PATH",
  ``!n Lx p0 pij pXY l X Y p Sx Sy.
    thmm (X:num -> 'a -> 'x) (Y:num -> 'a -> 'y) p Sx Sy p0 pij pXY
    /\ n < LENGTH Lx /\ (!k. k <= n ==> EL k Lx IN space Sy) /\ (space Sx = set l)
    /\ (!k x. k < n /\ (prob p (PREIMAGE (X k) {EL k x} INTER p_space p) = 0)
      ==> (pij k (EL k x) (EL (k+1) x) = 0))
    /\ (!k x. k <= n /\ (prob p (PREIMAGE (X k) {EL k x} INTER p_space p) = 0)
      ==> (pXY k (EL k Lx) (EL k x) = 0))
    ==>
    (REAL_MAXIMA_SET
      (\Ly. prob p (BIGINTER 
        (IMAGE (\(k:num). PREIMAGE (X k) {EL k Ly} INTER p_space p) (\m. m <= n))
        INTER BIGINTER (IMAGE 
          (\(k:num). PREIMAGE (Y k) {EL k Lx} INTER p_space p) (\m. m <= n))))
      {L | EVERY (\x. x IN space Sx) L /\ (LENGTH L = n + 1) /\
        !m. m < n + 1 ==> pXY m (EL m Lx) (EL m L) <> 0}
    =
    let l' = power_list l (\m x. pXY m (EL m Lx) x <> 0) (n+1) in
    let f Ly = p0 (EL 0 Ly) * pXY 0 (EL 0 Lx) (EL 0 Ly) * mulcon (0,n) (\k.
      pij k (EL k Ly) (EL (k + 1) Ly) * pXY (k+1) (EL (k + 1) Lx) (EL (k + 1) Ly))
    in
    let fl' = MAP f l' in
    let m = FOLDL (\acc x. if acc < x then x else acc) (HD fl') (TL fl') in
    (set o FST o UNZIP o FILTER (\(x,fx). fx = m) o ZIP) (l',fl'))``,
  !!GEN_TAC ++ Cases_on `l`
  >> (REWRITE_TAC[thmm_def,hmm_def,th_dtmc_def,dtmc_def,mc_property_def,LIST_TO_SET_THM]
    ++ METIS_TAC[RV_NON_EMPTY_SPACE])
  >> (PARSE_TAC (fn P => RW_TAC std_ss [(BETA_RULE o ISPEC P o Q.SPECL
    [`n+1`,`h::t`]) POWER_LIST_SPEC,GSYM COMPUTE_REAL_MAX_SET]) `\m x. pXY m (EL m Lx) x <>0`
     ++ Cases_on `l'`
    >> (Q.UNABBREV_TAC `fl'` ++ RW_TAC list_ss [] ++ RW_TAC pset_ss [GEMPTY,REAL_MAXIMA_SET_DEF])
    >> (MAP_EVERY Q.UNABBREV_TAC [`m`,`fl'`] ++ REWRITE_TAC[HD,TL,MAP]
      ++ REWRITE_TAC[GSYM MAP,GSYM (BETA_RULE (REWRITE_RULE[LET_DEF,o_THM] (COMPUTE_REAL_MAXIMA_SET)))]
      ++ MATCH_MP_TAC REAL_MAXIMA_SET_EQ_FUN ++ Q.UNABBREV_TAC `f` ++ RW_TAC std_ss []
      ++ MATCH_MP_TAC HMM_JOINT_PROB_CONCRETE
      ++ MAP_EVERY Q.EXISTS_TAC [`Sx`,`Sy`] ++ ASM_REWRITE_TAC[]
      ++ RULE_ASSUM_TAC (REWRITE_RULE[markerTheory.Abbrev_def])
      ++ POP_ASSUM MP_TAC ++ ASM_REWRITE_TAC[GSYM POWER_LIST_SPEC,GSPECIFICATION,PAIR_EQ]
      ++ BETA_TAC ++ RW_TAC std_ss [PAIR_EQ,EVERY_EL] ++ FIRST_ASSUM
      MATCH_MP_TAC)));

val best_path =
  let
    val type_check_term = ``\i t e cs (n:num) b. (i b, t (0:num) b b, e (0:num) (HD cs) b) :real#real#real``
    fun LENGTH_of l = mk_comb(mk_const("LENGTH",type_of l --> num),l)
    val head = fst o dest_const o fst o strip_comb
    fun list_of_enum ty = listSyntax.mk_list (TypeBase.constructors_of ty, ty)
    fun univ_of_enum_as_list ty =
      prove(mk_eq(mk_const("UNIV",ty-->bool),mk_comb(mk_const("LIST_TO_SET",mk_type("list",[ty]) --> ty --> bool),list_of_enum ty)),
      REWRITE_TAC[EXTENSION,IN_UNIV,IN_LIST_TO_SET,MEM,TypeBase.nchotomy_of ty]);
    fun added_assum ty = inst [alpha |-> ty] ``space Sx = univ(:'a)``
    fun BETA_REWRITE_CONV ths = DEPTH_CONV BETA_CONV THENC REWRITE_CONV ths
  in
  fn p0 => fn pij => fn pXY => fn Lx => fn n =>
    let
      val hol_n = term_of_int n
      val n_thm = GSYM (REPEATC (DEPTH_CONV num_CONV) hol_n)
        handle _ => failwith "The considered length should be a positive number"
      val hol_n_suc = lhs (concl n_thm)
      val _ = list_mk_icomb(type_check_term,[p0,pij,pXY,Lx,hol_n_suc])
        handle _ => failwith "Input has incompatible types"
      val TYx = List.hd (snd (dest_type (type_of p0)))
      val TYy = List.hd (snd (dest_type (type_of Lx)))
      val LET_THM_l' = INST_TYPE [alpha |-> mk_type("list",[mk_type("list",[TYx])]) ] LET_THM
      val LET_THM_f = INST_TYPE [alpha |-> mk_type("fun",[mk_type("list",[TYx]),``:real``]) ] LET_THM
      val less_LENGTH =
        prove(mk_less(hol_n_suc,LENGTH_of Lx),REWRITE_TAC[LENGTH,LESS_MONO_EQ,LESS_0])
        handle _ => failwith "The last argument should be strictly smaller than the length of the list"
      val pij = (rhs o concl o (REWRITE_CONV [pair_case_thm] THENC DEPTH_CONV BETA_CONV)) pij
      val pXY = (rhs o concl o (REWRITE_CONV [pair_case_thm] THENC DEPTH_CONV BETA_CONV)) pXY
      val specialization = (UNDISCH_ALL o REWRITE_RULE[AND_IMP] o SPEC_ALL o ISPECL [hol_n_suc,Lx,p0,pij,pXY,list_of_enum TYx]) COMPUTE_BEST_STATE_PATH
      val EL_CONV = fst (Cache.CACHE ((fn t => head t = "EL"),REWRITE_CONV)) [EL,HD,TL]
      val compset = realSimps.real_compset ()
      val _ = 
        (listSimps.list_rws compset;
        computeLib.add_thms
        [PAIRED_BETA_THM,FST,SND,o_THM,computeLib.strictify_thm
        LIST_TO_SET_THM,REAL_MUL_LZERO,REAL_MUL_RZERO,MULCON_ALT] compset)
      val compute =
        BETA_REWRITE_CONV [GSYM ADD1]
        THENC POWER_LIST_CONV (REWRITE_CONV (type_rws TYx)
          THENC DEPTH_CONV EL_CONV
          THENC REWRITE_CONV (type_rws TYy) THENC SIMP_CONV real_ss [])
        THENC REWRITE_CONV [LET_THM_l']
        THENC BETA_REWRITE_CONV [MAP,LET_THM_f] THENC REDEPTH_CONV BETA_CONV
        THENC REWRITE_CONV[GSYM n_thm,mulcon_def,ADD] THENC DEPTH_CONV BETA_CONV
        THENC DEPTH_CONV EL_CONV
        THENC BETA_REWRITE_CONV (HD::TL::type_rws TYy @ type_rws TYx)
        THENC computeLib.CBV_CONV compset
      val result = CONV_RULE compute specialization
      val cosmetic = (UNDISCH_ALL o REWRITE_RULE[n_thm] o DISCH_ALL) result
    in
      print "Under the following assumptions:\n";
      print (String.concat (map (fn t => term_to_string t ^ "\n\n") (hyp cosmetic)));
      print "the set of best paths is formally expressed by:\n";
      print (term_to_string (lhs (concl cosmetic)) ^ "\n\n");
      (case (pred_setSyntax.strip_set (rhs (concl cosmetic))) of
          [] => print "which actually amounts to an empty set (probably not what you want...)"
         |[x] => print ("which contains only one best path: " ^ term_to_string x)
         |xs => print ("which contains the following elements:\n"
            ^ String.concat (map (fn t => term_to_string t ^ "\n") xs)));
      print "\n(proved by HOL4)\n\n"
    end
  end;

(* Example *)

Hol_datatype `dna = A | G | T | C`;
Hol_datatype `state = E | I | FIVE`;

val ini_distribution = ``\i. if (i = E) then (1:real) else 0``;

val trans_distribution = ``\(t:num) i j. 
  if (i = E) /\ (j = E) then 9/10 else 
  if (i = E) /\ (j = FIVE) then 1/10 else 
  if (i = FIVE) /\ (j = I) then 1 else
  if (i = I) /\ (j = I) then 9/10 else 0``;   

val trans_distribution = ``\(t:num) i j. 
  case (i,j) of
     (E,E) -> 0.9
     || (E,FIVE) -> 0.1
     || (FIVE,I) -> 1
     || (I,I) -> 0.9
     || _ -> 0``;

val emission_distribution = ``\t:num a i. 
  case (i,a) of
       (E,_) -> 0.25
     || (FIVE,A) -> 0.05
     || (FIVE,G) -> 0.95
     || (FIVE,_) -> 0
     || (I,A) -> 0.4
     || (I,T) -> 0.4
     || (I,_) -> 0.1``;

val state_seq = ``[E;E;E;E;E;E;E;E;E;E;E;E;E;E;E;E;E;E;FIVE;I;I;I;I;I;I;I]``; 

val dna = ``[C;T;T;C;A;T;G;T;G;A;A;A;G;C;A;G;A;C;G;T;A;A;G;T;C;A]``;   

time (hmm_joint_distribution ini_distribution trans_distribution emission_distribution state_seq dna) 25;

time (best_path ini_distribution trans_distribution emission_distribution dna) 6;

