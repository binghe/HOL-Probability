

(* -------------------------------------------------------------------------- *)
(*      Probabilistic Inclusion Exclusion Principle                           *)
(*        Extended Real Version                                               *)
(*          by Waqar Ahmed                                                    *)
(* -------------------------------------------------------------------------- *)
(*
loadPath := "/home/yassmeen/Downloads/nrv/HOL4source" :: !loadPath;


app load ["arithmeticTheory", "realTheory", "prim_recTheory", "seqTheory",
          "pred_setTheory","res_quanTheory", "res_quanTools", "listTheory", "numTheory", "dep_rewrite", 
          "transcTheory", "rich_listTheory", "pairTheory",
          "combinTheory","limTheory","sortingTheory", "realLib", "optionTheory","satTheory",
          "util_probTheory", "card_hvgTheory", "derivative_hvgTheory", "extreal_hvgTheory", "integration_hvgTheory", "iterate_hvgTheory", "measure_hvgTheory", "probability_hvgTheory", "product_hvgTheory", "topology_hvgTheory", "lebesgue_hvgTheory", "lebesgue_measure_hvgTheory","real_sigmaTheory"];
*)
open HolKernel Parse boolLib bossLib limTheory arithmeticTheory realTheory prim_recTheory
     seqTheory pred_setTheory res_quanTheory sortingTheory res_quanTools listTheory transcTheory
     rich_listTheory pairTheory combinTheory realLib  optionTheory dep_rewrite
      util_probTheory card_hvgTheory derivative_hvgTheory extreal_hvgTheory integration_hvgTheory iterate_hvgTheory measure_hvgTheory probability_hvgTheory product_hvgTheory topology_hvgTheory lebesgue_hvgTheory lebesgue_measure_hvgTheory real_sigmaTheory satTheory numTheory;
open HolKernel boolLib bossLib Parse;

val _ = new_theory "PIE_EXTREAL";

(*----------------------------------*)
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
++ RW_TAC std_ss [UNIONL_def, MEM, NOT_IN_EMPTY, IN_UNION]
++ PROVE_TAC []);


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
++ RW_TAC pset_set_ss ths
++ REPEAT (POP_ASSUM MP_TAC)
++ RW_TAC pset_elt_ss ths;





(*--------------------*)
(* -------------------------------------------------------------------------- *)
(*                                                                            *)
(*       Inclusion-Exclusion Principle                                        *)
(*                                                                            *)
(* -------------------------------------------------------------------------- *)
(*--------------------HAS_SIZE------------------------------------*)
val has_size_def =  Define `has_size s n  =  FINITE (s) /\ (CARD s = (n))`;

(* ------------------------------------------------------------------------- *)
(*   			inter_list                                  *)
(* ------------------------------------------------------------------------- *)
val inter_list_def =  Define
 ` (inter_list p ([]) = (p_space p  )) /\ 
 	  (!h t . inter_list p (h ::t)  = ( (h)  INTER (inter_list p t )))`;

(*--------------------union list def------------------------------------*)
val union_list_def =  Define
 ` (union_list ([]) = {} ) /\ 
 	  (!h t . union_list (h ::t)  =  h  UNION (union_list t ))`;
(*-------------------------------------*)
val sum_set_def =  Define `sum_set s f =  EXTREAL_SUM_IMAGE f s`;
(*------------SUBSET_INSERT_EXISTS_NEW------------------------------------------ *)
val SUBSET_INSERT_EXISTS_NEW = store_thm("SUBSET_INSERT_EXISTS_NEW",
  ``!s x t. s SUBSET (x INSERT t) =
            (s SUBSET t) \/ 
	       (?u. u SUBSET t /\ (s = x INSERT u))``,
RW_TAC std_ss[]
++ EQ_TAC
>> ((MATCH_MP_TAC (PROVE [] (Term`((a /\ ~b ==> c) ==> (a ==> b \/ c))`)))
   ++ DISCH_TAC
   ++ EXISTS_TAC (``s DELETE (x)``)
   ++ SRW_TAC [][SUBSET_DEF,INSERT_DEF,EXTENSION,GSPECIFICATION]
   >> (METIS_TAC[])
   ++ METIS_TAC[])
++ SRW_TAC [][SUBSET_DEF,INSERT_DEF,EXTENSION,GSPECIFICATION]
>> (METIS_TAC[])
++ METIS_TAC[]);
(*----------------------FINITE_SUBSETS_RESTRICT_NEW----------------------------------*)
val FINITE_SUBSETS_RESTRICT_NEW = store_thm("FINITE_SUBSETS_RESTRICT_NEW",
  ``!s:'a->bool p. FINITE s ==> FINITE {t | t SUBSET s /\ p t}``,
REPEAT STRIP_TAC
++ MATCH_MP_TAC SUBSET_FINITE_I
++ EXISTS_TAC (``{t:'a->bool | t SUBSET s}``)
++ REWRITE_TAC[GSYM POW_DEF]
++ RW_TAC std_ss[FINITE_POW]
++ SRW_TAC[][SUBSET_DEF,POW_DEF,EXTENSION,GSPECIFICATION]
++ METIS_TAC[]);
(*----------------------FINITE_SUBSETS_RESTRICT_NEW1----------------------------------*)
val FINITE_SUBSETS_RESTRICT_NEW1 = store_thm("FINITE_SUBSETS_RESTRICT_NEW1",
  ``!s:'a->bool p. FINITE s ==> FINITE {t | t SUBSET s}``,
REPEAT STRIP_TAC
++ MATCH_MP_TAC SUBSET_FINITE_I
++ EXISTS_TAC (``{t:'a->bool | t SUBSET s}``)
++ REWRITE_TAC[GSYM POW_DEF]
++ RW_TAC std_ss[FINITE_POW]
++ SRW_TAC[][SUBSET_DEF,POW_DEF,EXTENSION,GSPECIFICATION]);
(*----------------------FINITE_SUBSETS_RESTRICT_NEW2----------------------------------*)
val FINITE_SUBSETS_RESTRICT_NEW2 = store_thm("FINITE_SUBSETS_RESTRICT_NEW2",
  ``!s:'a->bool p. FINITE s ==> FINITE {t | t SUBSET s /\ t <> EMPTY}``,
REPEAT STRIP_TAC
++ MATCH_MP_TAC SUBSET_FINITE_I
++ EXISTS_TAC (``{t:'a->bool | t SUBSET s}``)
++ REWRITE_TAC[GSYM POW_DEF]
++ RW_TAC std_ss[FINITE_POW]
++ SRW_TAC[][SUBSET_DEF,POW_DEF,EXTENSION,GSPECIFICATION]
 ++ Q.EXISTS_TAC `t`
 ++ METIS_TAC[]);
(*------------------lemma_NEW--------------------------------*)
val lemma_NEW = store_thm("lemma_NEW",
  ``!P a s. {t | t SUBSET (a INSERT s) /\ P t} =
     {t | t SUBSET s /\ P t} UNION
     {a INSERT t |t| t SUBSET s /\ P(a INSERT t)}``,
RW_TAC std_ss[SUBSET_INSERT_EXISTS_NEW]
++ ONCE_REWRITE_TAC [EXTENSION]
++ RW_TAC std_ss[GSPECIFICATION,IN_UNION]
++ METIS_TAC[]);
(*-------------------temp1--------------------------------*)
val temp1 = store_thm("temp1",
  ``!P. (!s n. has_size s n ==> P s) ==> (!s. FINITE s ==> P s)``,
RW_TAC std_ss[has_size_def]);
(*-----------------------temp3----------------------------*)
val temp3 = store_thm("temp3",
  ``!P. (!n. (!m. (m:num) < n ==> P m) ==> P n) ==> (!n. P n)``,
GEN_TAC
++ KNOW_TAC (``((\n. !m. m < n ==> P m) 0 /\
  (!n. (\n. !m. m < n ==> P m) n ==> (\n. !m. m < n ==> P m) (SUC n))
  ==> (!n. (\n. !m. m < n ==> P m) n))``)
>> (DISCH_TAC
   ++ MATCH_MP_TAC INDUCTION
   ++ RW_TAC std_ss[])
++ RW_TAC std_ss[BETA_THM]
++ KNOW_TAC (``(!n. (!m. m < n ==> P m) ==> !m. m < SUC n ==> P m)``)
>> (RW_TAC std_ss[]
   ++ FULL_SIMP_TAC std_ss[LT_SUC])
++ METIS_TAC[LT_SUC]);
(*-----------------------temp2---------------------------*)
val temp2 = store_thm("temp2",
  ``(!P (f:('a->bool) -> extreal) (A:'b->bool) (x:'b->('a->bool)) (n:num).
      (!s t. P s /\ P t /\ DISJOINT s t
               ==> (f(s UNION t) = f(s) + f(t))) /\
        P {} /\
        (!s t. P s /\ P t ==> P(s INTER t) /\ P(s UNION t) /\ P(s DIFF t)) /\
        (has_size A n) /\ (!a. a IN A ==> P(x a))
        ==> (f(BIGUNION(IMAGE x A)) =
            sum_set {B | B SUBSET A /\ ~(B = {})}
                (\B.  Normal(- &1) pow (CARD B + 1) * f(BIGINTER(IMAGE x B)))))==>(!P (f:('a->bool) -> extreal) (A:'b->bool) (x:'b->('a->bool)).
      (!s t. P s /\ P t /\ DISJOINT s t
               ==> (f(s UNION t) = f(s) + f(t))) /\
        P {} /\
        (!s t. P s /\ P t ==> P(s INTER t) /\ P(s UNION t) /\ P(s DIFF t)) /\
        FINITE A /\ (!a. a IN A ==> P(x a))
        ==> (f(BIGUNION(IMAGE x A)) =
            sum_set {B | B SUBSET A /\ ~(B = {})}
                (\B.  Normal (- &1) pow (CARD B + 1) * f(BIGINTER(IMAGE x B)))))``,
RW_TAC std_ss[has_size_def]);
(*-----------------------temp4---------------------------*)
val temp4 = store_thm("temp4",
  ``!A:'a->bool s.  has_size s 0 =  (s = {})``,
RW_TAC std_ss[has_size_def]
++ METIS_TAC[CARD_EQ_0,FINITE_EMPTY]);

(*-------------------has_size_suc-------------------------------*)
val has_size_suc = store_thm("has_size_suc",
  ``!(s:'a->bool) n. (has_size s (SUC n) =
                   (~(s = EMPTY) /\ ( !a. (a IN s) ==> has_size (s DELETE a) n )))``,
RW_TAC std_ss[has_size_def]
++ Cases_on `s:'a->bool= {}`
>> (ASM_REWRITE_TAC[CARD_DEF]
   ++ METIS_TAC[FINITE_EMPTY,NOT_SUC])
++ REWRITE_TAC [FINITE_DELETE]
++ Cases_on `FINITE (s:'a->bool)`
>> (ASM_REWRITE_TAC[NOT_FORALL_THM, MEMBER_NOT_EMPTY]
   ++ EQ_TAC
   >> (REPEAT STRIP_TAC
      ++ MP_TAC (Q.ISPECL [`s DELETE a:'a`] (CONJUNCT2 CARD_DEF))
      ++ FULL_SIMP_TAC std_ss[FINITE_DELETE]
      ++ RW_TAC std_ss[IN_DELETE]
      ++ POP_ASSUM (MP_TAC o Q.SPEC `a:'a`)
      ++ ASM_REWRITE_TAC[]
      ++ KNOW_TAC(``a INSERT (s DELETE a:'a) = s``)
      >> (POP_ASSUM MP_TAC
      	 ++ RW_TAC std_ss[INSERT_DELETE])
      ++ RW_TAC std_ss[])
   ++ KNOW_TAC(``?a:'a. a IN s:'a->bool``)
   >> (RW_TAC std_ss[MEMBER_NOT_EMPTY])
   ++ RW_TAC std_ss[]
   ++ FULL_SIMP_TAC std_ss[]
   ++ MP_TAC(Q.ISPECL [`s DELETE a:'a`] (CONJUNCT2 CARD_DEF))
   ++ FULL_SIMP_TAC std_ss[FINITE_DELETE]
   ++ RW_TAC std_ss[IN_DELETE]
   ++ POP_ASSUM (MP_TAC o Q.SPEC `a:'a`)
   ++ ASM_REWRITE_TAC[]
   ++ KNOW_TAC(``a INSERT (s DELETE a:'a) = s``)
   >> (POP_ASSUM MP_TAC
      ++ RW_TAC std_ss[INSERT_DELETE])
   ++ RW_TAC std_ss[])
++ RW_TAC std_ss[]
++ RW_TAC std_ss[MEMBER_NOT_EMPTY]);
(*------------------FORALL_INSERT--------------------------------*)
val FORALL_INSERT = store_thm("FORALL_INSERT",
  ``!P a s. (!x. x IN a INSERT s ==> P x) <=> P a /\ (!x. x IN s ==> P x)``,
RW_TAC std_ss[IN_INSERT]
++ EQ_TAC
>> (RW_TAC std_ss[])
++ RW_TAC std_ss[]
++ RW_TAC std_ss[]
++ RW_TAC std_ss[]);
(*------------------INTER_BIGUNION--------------------------------*)
val INTER_BIGUNION = store_thm("INTER_BIGUNION",
  ``(!s t. BIGUNION s INTER t = BIGUNION {x INTER t | x IN s}) /\
   (!s t. t INTER BIGUNION s = BIGUNION {t INTER x | x IN s})``,
ONCE_REWRITE_TAC[EXTENSION]
++ REWRITE_TAC[IN_BIGUNION,EXTENSION,IN_INTER]
++ RW_TAC std_ss[]
++ RW_TAC std_ss[GSPECIFICATION]
>> (METIS_TAC[IN_INTER])
++ RW_TAC std_ss[GSPECIFICATION]
++ METIS_TAC[IN_INTER]);
(*------------------has_size_clauses--------------------------------*)
val has_size_clauses = store_thm("has_size_clauses",
  ``(has_size (s:'a->bool) 0 = (s = {})) /\
    (has_size s (SUC n) =
        ?a t. has_size t n /\ ~(a IN t) /\ (s = a INSERT t))``,
REWRITE_TAC[temp4]
++ REPEAT STRIP_TAC ++ EQ_TAC
>> (REWRITE_TAC[has_size_suc]
   ++ RW_TAC std_ss[]
   ++ KNOW_TAC (``?a:'a. a IN s:'a->bool``)
   >> (RW_TAC std_ss[MEMBER_NOT_EMPTY])
   ++ RW_TAC std_ss[]
   ++ EXISTS_TAC(``a:'a``)
   ++ EXISTS_TAC(`` s:'a->bool DELETE a``)
   ++ RW_TAC std_ss[ IN_DELETE]
   ++ KNOW_TAC (`` (s:'a->bool = a INSERT (s DELETE a)) ``)
   >> (METIS_TAC[INSERT_DELETE])
   ++ RW_TAC std_ss[ IN_DELETE])
++ FULL_SIMP_TAC std_ss[GSYM LEFT_FORALL_IMP_THM]
++ FULL_SIMP_TAC std_ss[has_size_def,CARD_DEF,FINITE_INSERT]);
(*--------------------temp5------------------------------*)
val temp5 = store_thm("temp5",
  ``!s t. s UNION (t DIFF s):'a->bool = s UNION t``,
RW_TAC std_ss[]
++ SRW_TAC [][IN_UNION,DIFF_DEF,UNION_DEF,EXTENSION,GSPECIFICATION]
++ EQ_TAC
>> (RW_TAC std_ss[]
   >> (DISJ1_TAC
      ++ RW_TAC std_ss[])
   ++ DISJ2_TAC
   ++ RW_TAC std_ss[])
++ RW_TAC std_ss[]
>> (DISJ1_TAC
   ++ RW_TAC std_ss[])
++ Cases_on `(x IN s)`
>> (DISJ1_TAC
   ++ RW_TAC std_ss[])
++ DISJ2_TAC
++ RW_TAC std_ss[]);
(*----------------incl_excl_temp1----------------------------------*)
val incl_excl_temp1 = store_thm("incl_excl_temp1",
  ``!s fas fa s'. s <> PosInf /\ s <> NegInf /\ fa <> NegInf /\ fa <> PosInf ==> (((fa + s) - fas:extreal = s + s') = (fa - fas = s'))``,
REPEAT Cases
++ RW_TAC std_ss [extreal_le_def,extreal_sub_def,le_infty,le_refl,extreal_add_def,extreal_hvgTheory.extreal_eq_zero,extreal_mul_def]
++ REAL_ARITH_TAC);
(*--------------temp6------------------------------------*)
val temp6 = store_thm("temp6",
  ``!s t. (s INTER t) UNION (t DIFF s) = t``,
RW_TAC std_ss[]
++ SRW_TAC [][IN_UNION,DIFF_DEF,UNION_DEF,EXTENSION,GSPECIFICATION]
++ EQ_TAC
>> (RW_TAC std_ss[])
++ RW_TAC std_ss[]);
(*-----------------simple_image_gen---------------------------------*)
val simple_image_gen = store_thm("simple_image_gen",
  ``! f P. {f s| P s} = IMAGE f {s | P s}``,
RW_TAC std_ss[IMAGE_DEF]
++ RW_TAC std_ss[EXTENSION,GSPECIFICATION]);
(*------------------FINITE_RESTRICT--------------------------------*)
val FINITE_RESTRICT = store_thm("FINITE_RESTRICT",
  ``!(s:'a->bool) P. {x | x IN s /\ P x} SUBSET s``,
RW_TAC std_ss[SUBSET_DEF]
++ POP_ASSUM MP_TAC
++ RW_TAC std_ss[EXTENSION,GSPECIFICATION]);
(*---------------------incl_excl_temp2-----------------------------*)
val incl_excl_temp2 = store_thm("incl_excl_temp2",
  ``!a b x. (x ≠ NegInf ∧ x <> PosInf) /\ (a <> NegInf /\ a ≠ PosInf) ==> 
       	      ((x - a:extreal = x + b) = (b = -a))``,
RW_TAC std_ss[]
++ DEP_REWRITE_TAC[extreal_sub_add,EXTREAL_EQ_LADD]
++ METIS_TAC[]);
(*------------------incl_excl_temp3--------------------------------*)
val incl_excl_temp3 = store_thm("incl_excl_temp3",
  ``!f s. BIGINTER (IMAGE f s) = {y | !x. x IN s ==> y IN f x}``,
RW_TAC std_ss[IMAGE_DEF,BIGINTER]
++ RW_TAC std_ss[EXTENSION,GSPECIFICATION]
++ EQ_TAC
>> (METIS_TAC[])
++ METIS_TAC[]);
(*-----------------incl_excl_temp4---------------------------------*)
val incl_excl_temp4 = store_thm("incl_excl_temp4",
  ``!P e. {s | P s /\ ~(s = e)} = {s | P s} DELETE e``,
RW_TAC std_ss[]
++ SRW_TAC[][DELETE_DEF,DIFF_DEF,EXTENSION,GSPECIFICATION]);
(*----------------incl_excl_temp5----------------------------------*)
val incl_excl_temp5 = store_thm("incl_excl_temp5",
  ``!x s. (x IN s) ==>  (x INSERT s =  s)``,
SRW_TAC[][INSERT_DEF,EXTENSION,GSPECIFICATION]
++ METIS_TAC[]);
(*-----------------incl_excl_temp6---------------------------------*)
val incl_excl_temp6 = store_thm("incl_excl_temp6",
  ``!s. EMPTY IN {B| B SUBSET s}``,
RW_TAC std_ss[GSYM POW_DEF,IN_POW,EMPTY_SUBSET]);
(*------------incl_excl_temp7--------------------------------------*)
val incl_excl_temp7 = store_thm("incl_excl_temp7",
  ``!a b c:extreal. a ≠ NegInf ∧ a <> PosInf /\ b ≠ NegInf ∧ b <> PosInf ==> ((a = b - c) = (b = c + a))``,
REPEAT Cases 
++ RW_TAC std_ss [extreal_le_def,extreal_sub_def,le_infty,le_refl,extreal_add_def]
++ REAL_ARITH_TAC);
(*------------incl_excl_temp7_new--------------------------------------*)
val incl_excl_temp7_new = store_thm("incl_excl_temp7_new",
  ``!a b c:extreal. c ≠ NegInf ∧ c <> PosInf ==> ((a = b - c) = (b = c + a))``,
REPEAT Cases 
++ RW_TAC std_ss [extreal_le_def,extreal_sub_def,le_infty,le_refl,extreal_add_def]
++ REAL_ARITH_TAC);
(*---------------incl_excl_temp8-----------------------------------*)
val incl_excl_temp8 = store_thm("incl_excl_temp8",
  ``!f e s. e IN s /\ FINITE s /\ (!e. e IN s  ==> f e ≠ NegInf ∧ f e ≠ PosInf) ==> (sum_set (s DELETE e) f = sum_set (e INSERT s) f - f e)``,
RW_TAC std_ss[]
++ DEP_REWRITE_TAC[incl_excl_temp7_new] 
++ RW_TAC std_ss[sum_set_def]
++ DEP_REWRITE_TAC[extreal_hvgTheory.EXTREAL_SUM_IMAGE_NOT_NEG_INF]
++ DEP_REWRITE_TAC[extreal_hvgTheory.EXTREAL_SUM_IMAGE_PROPERTY]
++ RW_TAC std_ss[]
++ DISJ1_TAC
++ RW_TAC std_ss[]
++ FULL_SIMP_TAC std_ss[pred_setTheory.IN_INSERT]);
(*------------------------incl_excl_temp9--------------------------*)
val incl_excl_temp9 = store_thm("incl_excl_temp9",
  ``!f e s. e IN s /\ FINITE s /\ (!e. e IN s  ==> f e ≠ NegInf ∧ f e ≠ PosInf)==> (sum_set (s DELETE e) f = sum_set (s) f - f e)``,
RW_TAC std_ss[incl_excl_temp8]
++ RW_TAC std_ss[incl_excl_temp5]);

(*-----------------BIGINTER_SET------------------------------------------------------*)
val BIGINTER_SET = store_thm("BIGINTER_SET",
  ``!s p. FINITE s /\ prob_space p  ==> ( BIGINTER (s) INTER p_space p  =  inter_list p  (SET_TO_LIST s))``,
Induction.recInduct SET_TO_LIST_IND
++ RW_TAC bool_ss []
++ RW_TAC std_ss [SET_TO_LIST_THM]
++ RW_TAC std_ss[BIGINTER_EMPTY,inter_list_def,INTER_UNIV]
++ KNOW_TAC (``BIGINTER (s:(('a -> bool) -> bool)) =  (BIGINTER (CHOICE s INSERT REST s) )``)
>> (RW_TAC std_ss[CHOICE_INSERT_REST])
++ DISCH_TAC ++ POP_ORW
++ RW_TAC std_ss[BIGINTER_INSERT,inter_list_def]
++ FULL_SIMP_TAC std_ss[FINITE_REST]
++ NTAC 3 (POP_ASSUM MP_TAC)
++ POP_ASSUM (MP_TAC o Q.SPEC `p`)
++ RW_TAC std_ss[]
++ FULL_SIMP_TAC std_ss[]
++ RW_TAC std_ss[GSYM INTER_ASSOC]);
(*------------------INCLUSION_EXCLUSION_RESTRICTED--------------------------------*)
(*
val REAL_SUM_IMAGE_IMAGE1 = store_thm
  ("REAL_SUM_IMAGE_IMAGE1",
   ``!P f' f. FINITE P /\
	  INJ f' P (IMAGE f' P) ==>
               (REAL_SUM_IMAGE f (IMAGE f' P) = REAL_SUM_IMAGE (f o f') P)``,
	       FULL_SIMP_TAC std_ss[AND_IMP, RIGHT_FORALL_IMP_THM] THEN
   Induct_on `FINITE`
   THEN SRW_TAC [][REAL_SUM_IMAGE_THM]
   THEN `IMAGE f' P DELETE f' e = IMAGE f' P`
   by (SRW_TAC [][EXTENSION]
       THEN EQ_TAC THEN1 (METIS_TAC[])
       THEN POP_ASSUM MP_TAC
       THEN ASM_SIMP_TAC (srw_ss()) [INJ_DEF]
       THEN METIS_TAC[])
   THEN `P DELETE e = P` by METIS_TAC [DELETE_NON_ELEMENT]
   THEN SRW_TAC [][]
   THEN FIRST_X_ASSUM MATCH_MP_TAC
   THEN Q.PAT_ASSUM `INJ f' SS1 SS2` MP_TAC
   THEN CONV_TAC (BINOP_CONV (SIMP_CONV (srw_ss()) [INJ_DEF]))
   THEN METIS_TAC[]);
*)

val EXTREAL_SUM_IMAGE_IMAGE1 = store_thm
  ("EXTREAL_SUM_IMAGE_IMAGE1",
   ``!s f' f. FINITE s /\
	 INJ f' s (IMAGE f' s) /\ ((!x. x IN (IMAGE f' s) ==> f x <> NegInf) \/ (!x. x IN (IMAGE f' s) ==> f x <> PosInf)) ==> (extreal_hvg$EXTREAL_SUM_IMAGE f (IMAGE f' s) = extreal_hvg$EXTREAL_SUM_IMAGE (f o f') s)``,
METIS_TAC[AND_IMP,EXTREAL_SUM_IMAGE_IMAGE]);

val EXTREAL_SUM_IMAGE_DISJOINT_UNION1 = store_thm
  ("EXTREAL_SUM_IMAGE_DISJOINT_UNION1",
   ``!s s' f. (FINITE s /\ FINITE s' /\ DISJOINT s s') /\
		((!x. x IN s UNION s' ==> f x <> NegInf) \/ 
		(!x. x IN s UNION s' ==> f x <> PosInf)) ==> 
                    (EXTREAL_SUM_IMAGE f (s UNION s') =
		     EXTREAL_SUM_IMAGE f s +
		     EXTREAL_SUM_IMAGE f s')``,
METIS_TAC[AND_IMP,EXTREAL_SUM_IMAGE_DISJOINT_UNION]);



(*-----------------------*)
val PIE_lemma1 = store_thm("PIE_lemma1",
  ``!a:extreal. a <> NegInf /\ a <> PosInf /\ (a = a + a) ==> (a = 0)``,
Cases 
++ RW_TAC std_ss [extreal_le_def,extreal_sub_def,le_infty,le_refl,extreal_add_def,extreal_hvgTheory.extreal_eq_zero,extreal_mul_def]
++ POP_ASSUM MP_TAC
++ REAL_ARITH_TAC);
(*----------------------*)
(*----------------------*)
val PIE_lemma3 = store_thm("PIE_lemma3",
  ``!t.  FINITE t ==> 
  	  (0 <= (-1:real) pow (CARD t + 1) \/ (-1:real) pow (CARD t + 1) <= 0)``,
FULL_SIMP_TAC std_ss[AND_IMP,RIGHT_FORALL_IMP_THM]
++ GEN_TAC
++ `(0:real) ≤ -1 pow (CARD t + 1) ∨ -1 pow (CARD t + 1) <= (0:real) =
(\a. (0:real) ≤ -1 pow (CARD a + 1) ∨ -1 pow (CARD a + 1) <= (0:real)) t` by RW_TAC std_ss[]
++ POP_ORW
++ MATCH_MP_TAC FINITE_INDUCT
++ RW_TAC std_ss[]
>> (SRW_TAC [][EXTENSION,GSPECIFICATION,SUBSET_INSERT])
>> (DISJ2_TAC
   ++ ONCE_REWRITE_TAC[GSYM ADD1]
   ++ ONCE_REWRITE_TAC[pow] 
   ++ RW_TAC real_ss[]
   ++ RW_TAC real_ss[realTheory.REAL_NEG_LE0]
   ++ RW_TAC std_ss[pred_setTheory.CARD_INSERT]
   ++ RW_TAC bool_ss[ADD1])
++ DISJ1_TAC
++ RW_TAC std_ss[pred_setTheory.CARD_INSERT]
++ ONCE_REWRITE_TAC[GSYM ADD1]
++ ONCE_REWRITE_TAC[pow] 
++ RW_TAC real_ss[]
++ RW_TAC real_ss[realTheory.REAL_NEG_GE0]
++ RW_TAC bool_ss[ADD1]);
(*----------------------*)
val PIE_lemma4 = store_thm("PIE_lemma4",
  ``!c y. (0 <= c \/ c <= 0) /\ y <> NegInf /\ y <> PosInf ==> (Normal c * y <> NegInf)``,
 METIS_TAC[mul_not_infty]);

(*----------------------*)
val PIE_lemma5 = store_thm("PIE_lemma5",
  ``!a. a <> NegInf /\ a <> PosInf ==> (Normal (-1) * a = -a)``,
Cases 
++ RW_TAC std_ss[extreal_le_def,extreal_sub_def,le_infty,le_refl,extreal_add_def,extreal_hvgTheory.extreal_eq_zero,extreal_mul_def,extreal_hvgTheory.extreal_ainv_def]
++ REAL_ARITH_TAC);
(*----------------------*)
val PIE_lemma6 = store_thm("PIE_lemma6",
  ``!c y. (0 <= c \/ c <= 0) /\ y <> NegInf /\ y <> PosInf ==> (Normal c * y <> PosInf)``,
 METIS_TAC[mul_not_infty]);

(*----------------------*)
val PIE_lemma7 = store_thm("PIE_lemma7",
  ``!t.  FINITE t ==> 
  	  (0 <= (-1:real) pow (CARD t) \/ (-1:real) pow (CARD t) <= 0)``,
FULL_SIMP_TAC std_ss[AND_IMP,RIGHT_FORALL_IMP_THM]
++ GEN_TAC
++ `(0:real) ≤ -1 pow (CARD t) ∨ -1 pow (CARD t) <= (0:real) =
(\a. (0:real) ≤ -1 pow (CARD a) ∨ -1 pow (CARD a) <= (0:real)) t` by RW_TAC std_ss[]
++ POP_ORW
++ MATCH_MP_TAC FINITE_INDUCT
++ RW_TAC std_ss[]
>> (SRW_TAC [][EXTENSION,GSPECIFICATION,SUBSET_INSERT])
>> (DISJ2_TAC
   ++ RW_TAC std_ss[pred_setTheory.CARD_INSERT]
   ++ RW_TAC real_ss[pow]
   ++ RW_TAC real_ss[realTheory.REAL_NEG_LE0])
++ DISJ1_TAC
++ RW_TAC std_ss[pred_setTheory.CARD_INSERT]
++ ONCE_REWRITE_TAC[pow] 
++ RW_TAC real_ss[]
++ RW_TAC real_ss[realTheory.REAL_NEG_GE0]);
(*------------PIE_lemma8------------*)
val PIE_lemma8 = store_thm("PIE_lemma8",
  ``!a t. a NOTIN t ==> INJ (λB. a INSERT B) {B | ∀x. x ∈ B ⇒ x ∈ t}
  (IMAGE (λB. a INSERT B) {B | ∀x. x ∈ B ⇒ x ∈ t})``,
ASM_SIMP_TAC(srw_ss())[INJ_DEF,INSERT_DEF,SUBSET_DEF,EXTENSION,GSPECIFICATION]
       ++ METIS_TAC[]);
(*----------------------*)
val EXTREAL_SUM_IMAGE_NEG = store_thm("EXTREAL_SUM_IMAGE_NEG",
  ``!P. FINITE P ==>
	!f. (!x. (x IN P ==> f x <> NegInf) /\ (x IN P ==> f x <> PosInf)) ==> (EXTREAL_SUM_IMAGE (\x. ~ f x) P = ~ (EXTREAL_SUM_IMAGE f P))``,
   REPEAT STRIP_TAC
   ++ (ASSUME_TAC o Q.SPECL [`f`, `~1`] o UNDISCH o Q.SPEC `P`) EXTREAL_SUM_IMAGE_CMUL
   ++ `(∀x. x ∈ P ⇒ f x ≠ NegInf)` by RW_TAC std_ss[]
   ++ FULL_SIMP_TAC std_ss[]
   ++ `!x. (Normal (-1) * f x =  - f x)` by METIS_TAC[extreal_hvgTheory.extreal_ainv_def,extreal_of_num_def,GSYM extreal_hvgTheory.neg_minus1]
   ++ FULL_SIMP_TAC std_ss[]
   ++ `Normal (-1) * EXTREAL_SUM_IMAGE f P =  -EXTREAL_SUM_IMAGE f P` by METIS_TAC[extreal_hvgTheory.extreal_ainv_def,extreal_of_num_def,GSYM extreal_hvgTheory.neg_minus1]);

(*-----------------------------*)
val EXTREAL_SUM_IMAGE_EQ1 = store_thm("EXTREAL_SUM_IMAGE_EQ1",
  ``!s f f'. FINITE s /\
	   ((!x. x IN s ==> f x <> NegInf /\ f' x <> NegInf) \/
                   (!x. x IN s ==> f x <> PosInf /\ f' x <> PosInf)) /\ 
                   (!x. x IN s ==> (f x = f' x)) ==>
		(EXTREAL_SUM_IMAGE f s = EXTREAL_SUM_IMAGE f' s)``,
METIS_TAC[EXTREAL_SUM_IMAGE_EQ]);
(*-----------------------INCLUSION_EXCLUSION_RESTRICTED---------------------------*)
val INCLUSION_EXCLUSION_RESTRICTED = store_thm("INCLUSION_EXCLUSION_RESTRICTED",
  ``!P (f:('a->bool) -> extreal) (A:'b->bool) (x:'b->('a->bool)).
      (!a. f a <> NegInf /\ f a <> PosInf) /\
      (!s t. P s /\ P t /\ DISJOINT s t
               ==> (f(s UNION t) = f(s) + f(t))) /\
        P {} /\
        (!s t. P s /\ P t ==> P(s INTER t) /\ P(s UNION t) /\ P(s DIFF t)) /\
        FINITE A /\ (!a. a IN A ==> P(x a))
        ==> (f(BIGUNION(IMAGE x A)) =
            sum_set {B | B SUBSET A /\ ~(B = {})}
                (\B.  (Normal (- &1)) pow (CARD B + 1) * f(BIGINTER(IMAGE x B))))``,
FULL_SIMP_TAC std_ss[AND_IMP, RIGHT_FORALL_IMP_THM]
++ REWRITE_TAC [AND_IMP_INTRO]
++ REWRITE_TAC [GSYM CONJ_ASSOC]
++ REWRITE_TAC [PULL_FORALL]
++ FULL_SIMP_TAC std_ss[RIGHT_FORALL_IMP_THM]
++ FULL_SIMP_TAC std_ss[AND_IMP_INTRO]
++ RW_TAC std_ss[]
++ POP_ASSUM MP_TAC
++ POP_ASSUM MP_TAC
++ Q.SPEC_TAC (`x`, `x`) 
++ FULL_SIMP_TAC std_ss[AND_IMP,RIGHT_FORALL_IMP_THM]
++ KNOW_TAC (`` 
 (!(x:'b->('a->bool)). (!a. a IN A ==> P (x a))==>
  (f (BIGUNION (IMAGE x (A:'b->bool))) =
   sum_set {B | B SUBSET A /\ ~(B = {})}
     (\B. Normal (-1) pow (CARD B + 1) * f (BIGINTER (IMAGE (x:'b->('a->bool)) B))))) = (\A. !(x:'b->('a->bool)).  
  (!a. a IN A ==> P (x a)) ==>
  (f (BIGUNION (IMAGE x A)) =
   sum_set {B | B SUBSET A /\ ~(B={})}
     (\B. Normal (-1) pow (CARD B + 1) * f (BIGINTER (IMAGE x B))))) A ``)
>> (RW_TAC std_ss[])
++ DISCH_TAC ++ POP_ORW 
++ Q.SPEC_TAC (`A`, `A`)
++ MATCH_MP_TAC ( PROVE[has_size_def] (Term`(!A n. has_size A n ==> P A) ==> (!A. FINITE A ==> P A)`))
++ REPEAT GEN_TAC
++ FULL_SIMP_TAC std_ss[]
++ Q.SPEC_TAC (`A`, `A`) 
++ KNOW_TAC (`` 
  (!(A:'b->bool). has_size (A:('b->bool))  n ==>
!(x:'b->('a->bool)).
 (!a. a IN (A:'b->bool) ==> P (x a)) ==>
  (f (BIGUNION (IMAGE x A)) =
   sum_set {B | B SUBSET A /\ (B <> {})}
     (\B. Normal (-1) pow (CARD B + 1) * f (BIGINTER (IMAGE (x:'b->('a->bool)) B))))) = ((\n:num. !(A:'b->bool). has_size A n ==>
!(x:'b->('a->bool)).
  (!a. a IN A ==> P (x a)) ==>
  (f (BIGUNION (IMAGE x A)) =
   sum_set {B | B SUBSET A /\ (B <> {}) }
     (\B. Normal (-1) pow (CARD B + 1) * f (BIGINTER (IMAGE x B))))) n) ``)
>> (RW_TAC std_ss[])
++ DISCH_TAC ++ POP_ORW
++ Q.SPEC_TAC (`n`, `n`) 
++ MATCH_MP_TAC temp3
++ FULL_SIMP_TAC std_ss[]
++ Induct_on `n`
>> (FULL_SIMP_TAC std_ss[has_size_clauses]
   ++ RW_TAC std_ss[]
   ++ RW_TAC std_ss[IMAGE_EMPTY,BIGUNION_EMPTY,SUBSET_EMPTY]
   ++ RW_TAC std_ss[GSPEC_F, sum_set_def,extreal_hvgTheory.EXTREAL_SUM_IMAGE_EMPTY]
   ++ REPEAT(FIRST_X_ASSUM (MP_TAC o Q.SPECL [ `{}:'a->bool`]))
   ++ FULL_SIMP_TAC std_ss[UNION_EMPTY, DISJOINT_EMPTY]
   ++ RW_TAC std_ss[]
   ++ POP_ASSUM (MP_TAC o Q.SPEC `EMPTY`)
   ++ RW_TAC std_ss[]
   ++ NTAC 2 (POP_ASSUM MP_TAC)
   ++ POP_ASSUM (MP_TAC o Q.SPEC `EMPTY`)
   ++ RW_TAC std_ss[]
   ++ NTAC 3 (POP_ASSUM MP_TAC)
   ++ METIS_TAC[PIE_lemma1])
++ DISCH_TAC
++ FULL_SIMP_TAC std_ss[has_size_clauses]
++ REPEAT GEN_TAC
++ FULL_SIMP_TAC std_ss[GSYM LEFT_FORALL_IMP_THM]
++ REPEAT GEN_TAC
++ REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))
++ FULL_SIMP_TAC std_ss[FORALL_INSERT]
++ STRIP_TAC
++ REWRITE_TAC[IMAGE_INSERT,BIGUNION_INSERT]
++ STRIP_TAC
++ STRIP_TAC
++ MATCH_MP_TAC EQ_TRANS
++ EXISTS_TAC(``(f(x a) + f(BIGUNION (IMAGE (x:'b->('a->bool)) t))) -
              f(x a INTER BIGUNION (IMAGE x t)):extreal``)
++ CONJ_TAC
>> (KNOW_TAC(``P(x a) /\ P(BIGUNION(IMAGE (x:'b->('a->bool)) t))``)
   >> (ASM_REWRITE_TAC[]
      ++ POP_ASSUM MP_TAC
      ++ KNOW_TAC(``FINITE (t:'b->bool)``)
      >> (FULL_SIMP_TAC std_ss[has_size_def])
      ++ KNOW_TAC(``(!a'. a' IN t ==> P (x a')) ==> P (BIGUNION (IMAGE (x:'b->('a->bool)) t)) =
 (\ (t:'b->bool). ((!a'. a' IN t ==> P (x a')) ==> P (BIGUNION (IMAGE x t))))t``)
      >> (RW_TAC std_ss[])
      ++ DISCH_TAC ++ POP_ORW
      ++ Q.SPEC_TAC (`t`, `u`) 
      ++ MATCH_MP_TAC FINITE_INDUCT
      ++ FULL_SIMP_TAC std_ss[IMAGE_EMPTY,IMAGE_INSERT,BIGUNION_EMPTY,BIGUNION_INSERT]
      ++ FULL_SIMP_TAC std_ss[FORALL_INSERT])
   ++ FULL_SIMP_TAC std_ss[ PULL_FORALL,AND_IMP_INTRO]
   ++ PAT_ASSUM (Term `P (x a) `) MP_TAC
   ++ Q.SPEC_TAC(`BIGUNION (IMAGE x t)`,`t'`)
   ++ Q.SPEC_TAC(`x a`,`s'`)
   ++ RW_TAC std_ss[]
   ++ KNOW_TAC (``P (s' INTER t':'a->bool) /\ 
      	       	   P (t' DIFF s':'a->bool) /\ 
		   DISJOINT (s' INTER t') (t' DIFF s':'a->bool) ==> 
		    (f (s' INTER t':'a->bool UNION (t' DIFF s':'a->bool)) = 
		    (f:('a->bool) -> extreal) (s' INTER t':'a->bool) + 
		    f (t' DIFF s':'a->bool))``)
   >> (PAT_ASSUM (Term ` !s t. (P s /\ P t) /\ DISJOINT s t ==> (f (s UNION t) = f s + (f:('a->bool) -> extreal) t)`) (MP_TAC o Q.SPECL [`s' INTER t':'a->bool`, `t' DIFF s':'a->bool`])
      ++ RW_TAC std_ss[])
   ++ PAT_ASSUM (Term ` !s t. (P s /\ P t) /\ DISJOINT s t ==> (f (s UNION t) = f s + (f:('a->bool) -> extreal) t)`) MP_TAC
   ++ DISCH_THEN (MP_TAC o Q.SPECL [`s':'a->bool`, `t' DIFF s':'a->bool`])
   ++ ONCE_REWRITE_TAC[temp5,temp6]
   ++ FULL_SIMP_TAC std_ss[]
   ++ KNOW_TAC (``DISJOINT s' (t' DIFF s')``)
   >> (RW_TAC std_ss[DISJOINT_DEF]
      ++ SIMP_TAC (srw_ss()) [DISJOINT_DEF,DIFF_DEF,IN_INTER,EXTENSION,GSPECIFICATION,EXCLUDED_MIDDLE]
      ++ RW_TAC std_ss[DISJ_ASSOC]
      ++ ONCE_REWRITE_TAC[DISJ_SYM]
      ++ RW_TAC std_ss[DISJ_ASSOC])
   ++ RW_TAC std_ss[]
   ++ FULL_SIMP_TAC std_ss[]
   ++ KNOW_TAC (``DISJOINT (s' INTER t') (t' DIFF s')``)
   >> (RW_TAC std_ss[DISJOINT_DEF]
      ++ SIMP_TAC (srw_ss()) [DISJOINT_DEF,DIFF_DEF,IN_INTER,EXTENSION,GSPECIFICATION,EXCLUDED_MIDDLE]
      ++ ONCE_REWRITE_TAC[DISJ_SYM]
      ++ RW_TAC std_ss[GSYM DISJ_ASSOC]
      ++ DISJ2_TAC
      ++ RW_TAC std_ss[DISJ_ASSOC])
   ++ RW_TAC std_ss[]
   ++ FULL_SIMP_TAC std_ss[]
   ++ RW_TAC std_ss[prove(``!a b c:extreal. a <> NegInf /\ a <> PosInf /\ c <> NegInf /\ c <> PosInf ==> 
      	     		      		   (a + b = a + (c + b) - c)``, REPEAT Cases 
++ RW_TAC std_ss [extreal_le_def,extreal_sub_def,le_infty,le_refl,extreal_add_def]
++ REAL_ARITH_TAC)])
++ FULL_SIMP_TAC std_ss[INTER_BIGUNION]
++ FULL_SIMP_TAC std_ss[GSYM IMAGE_DEF]
++ FULL_SIMP_TAC std_ss[GSYM IMAGE_COMPOSE,o_DEF]
++ FIRST_X_ASSUM(MP_TAC o Q.SPEC `n:num`) 
++ REWRITE_TAC[LT_SUC]
++ DISCH_THEN(MP_TAC o Q.SPEC `t:'b->bool`) ++ ASM_REWRITE_TAC[]
++ DISCH_TAC
++ KNOW_TAC (``((!a'. a' IN t ==> P ((\s. (x:'b->('a->bool)) a INTER x s) a')) ==>
 (f (BIGUNION (IMAGE (\s. x a INTER x s) t)) =
  sum_set {B | B SUBSET t /\ B <> EMPTY}
    (\B.
       Normal (-1) pow (CARD B + 1) * f (BIGINTER (IMAGE (\s. x a INTER x s) B)))))``)
>> (PAT_ASSUM (Term ` !x.
        (!a. a IN t ==> P (x a)) ==>
        (f (BIGUNION (IMAGE x t)) =
         sum_set {B | B SUBSET t /\ B <> EMPTY}
           (\B. Normal (-1) pow (CARD B + 1) * f (BIGINTER (IMAGE x B))))`) MP_TAC
     ++ DISCH_THEN(MP_TAC o Q.SPEC `\s. (x:'b->('a->bool)) a INTER x s`) ++ ASM_REWRITE_TAC[]) 
++ POP_ASSUM MP_TAC
++ DISCH_THEN(MP_TAC o Q.SPEC `(x:'b->('a->bool))`) ++ ASM_REWRITE_TAC[]
++ REPEAT(DISCH_THEN SUBST1_TAC)
++ FULL_SIMP_TAC std_ss[lemma_NEW]
++ DISCH_TAC
++ KNOW_TAC (``sum_set
  ({B | B SUBSET t:'b->bool /\ B <> EMPTY} UNION {a INSERT B | B | B SUBSET t /\ a INSERT B <> EMPTY})
  (\B. Normal (-1) pow (CARD B + 1) * f (BIGINTER (IMAGE (x:'b->('a->bool)) B))) = sum_set
  ({B | B SUBSET t /\ B <> EMPTY})(\B. Normal (-1) pow (CARD B + 1) * f (BIGINTER (IMAGE x B))) + sum_set ( {a INSERT B | B | B SUBSET t /\ a INSERT B <> EMPTY})
  (\B. Normal (-1) pow (CARD B + 1) * f (BIGINTER (IMAGE x B)))``)
>> (REWRITE_TAC[sum_set_def]
   ++ MATCH_MP_TAC EXTREAL_SUM_IMAGE_DISJOINT_UNION1
   ++ KNOW_TAC (``FINITE {B | B SUBSET t /\ B <> EMPTY} /\
FINITE {a INSERT B | B | B SUBSET t /\ a INSERT B <> EMPTY} /\
DISJOINT {B | B SUBSET t:'b->bool /\ B <> EMPTY} {a INSERT B | B | B SUBSET t /\ a INSERT B <> EMPTY} = (FINITE( IMAGE (\B. B) {B | B SUBSET t /\ B <> EMPTY}) /\
FINITE  (IMAGE (\B. a INSERT B){ B | B SUBSET t /\ a INSERT B <> EMPTY}) /\
DISJOINT  (IMAGE (\B. B){B | B SUBSET t /\ B <> EMPTY}) ( IMAGE (\B. a INSERT B){ B | B SUBSET t /\ a INSERT B <> EMPTY}))``)
   >> (RW_TAC std_ss[GSYM simple_image_gen])
   ++ DISCH_TAC ++ PURE_ONCE_ASM_REWRITE_TAC [] ++ POP_ORW
   ++ FULL_SIMP_TAC std_ss[has_size_def]
   ++ FULL_SIMP_TAC std_ss[FINITE_SUBSETS_RESTRICT_NEW,IMAGE_FINITE]
   ++ RW_TAC std_ss[GSYM simple_image_gen]
   >> (RW_TAC std_ss[IN_DISJOINT,GSPECIFICATION]
      ++ METIS_TAC [EXTENSION,IN_INSERT,IN_UNION,IN_DELETE,SUBSET_DEF,
DISJOINT_DEF,NOT_IN_EMPTY,EXTENSION,IN_INSERT,IN_INTER,IN_DIFF,IN_UNIV])
   ++ DISJ1_TAC
   ++ PSET_TAC[]
   >> (RW_TAC std_ss[extreal_pow_def]
      ++ DEP_REWRITE_TAC[PIE_lemma4]
      ++ DEP_REWRITE_TAC[PIE_lemma3]
      ++ RW_TAC std_ss[]
      ++ DEP_REWRITE_TAC[SUBSET_FINITE_I]
      ++ RW_TAC std_ss[]
      ++ Q.EXISTS_TAC `t`
      ++ PSET_TAC[])
   ++ RW_TAC std_ss[extreal_pow_def]
   ++ DEP_REWRITE_TAC[PIE_lemma4]
   ++ DEP_REWRITE_TAC[PIE_lemma3]
   ++ RW_TAC std_ss[]
   ++ RW_TAC std_ss[pred_setTheory.FINITE_INSERT]
   ++ DEP_REWRITE_TAC[SUBSET_FINITE_I]
   ++ Q.EXISTS_TAC `t`
   ++ PSET_TAC[])
++ DISCH_THEN SUBST1_TAC
++ RW_TAC std_ss[NOT_INSERT_EMPTY]
++ DEP_REWRITE_TAC[incl_excl_temp1]
++ RW_TAC std_ss[]
>> (RW_TAC std_ss[sum_set_def]
   ++ DEP_REWRITE_TAC[extreal_hvgTheory.EXTREAL_SUM_IMAGE_NOT_POS_INF]
   ++ DEP_REWRITE_TAC[FINITE_SUBSETS_RESTRICT_NEW2]
   ++ FULL_SIMP_TAC std_ss[has_size_def]
   ++ RW_TAC std_ss[extreal_pow_def]
   ++ DEP_REWRITE_TAC[PIE_lemma6]
   ++ DEP_REWRITE_TAC[PIE_lemma3]
   ++ RW_TAC std_ss[]
   ++ DEP_REWRITE_TAC[SUBSET_FINITE_I]
   ++ Q.EXISTS_TAC `t`
   ++ PSET_TAC[])
>> (RW_TAC std_ss[sum_set_def]
   ++ DEP_REWRITE_TAC[extreal_hvgTheory.EXTREAL_SUM_IMAGE_NOT_NEG_INF]
   ++ DEP_REWRITE_TAC[FINITE_SUBSETS_RESTRICT_NEW2]
   ++ FULL_SIMP_TAC std_ss[has_size_def]
   ++ RW_TAC std_ss[extreal_pow_def]
   ++ DEP_REWRITE_TAC[PIE_lemma4]
   ++ DEP_REWRITE_TAC[PIE_lemma3]
   ++ RW_TAC std_ss[]
   ++ DEP_REWRITE_TAC[SUBSET_FINITE_I]
   ++ Q.EXISTS_TAC `t`
   ++ PSET_TAC[])
++ MATCH_MP_TAC EQ_TRANS
++ EXISTS_TAC(``f((x:'b->('a->bool)) a) +
              sum_set {B | B SUBSET t /\ ~(B = {})}
                  (\B. Normal (-(&1)) pow (CARD B) *
                       f(BIGINTER(IMAGE x (a INSERT B))))``)
++ CONJ_TAC
>> (DEP_REWRITE_TAC[incl_excl_temp2]
   ++ RW_TAC std_ss[]
   >> (RW_TAC std_ss[sum_set_def]
      ++ DEP_REWRITE_TAC[extreal_hvgTheory.EXTREAL_SUM_IMAGE_NOT_NEG_INF]
      ++ DEP_REWRITE_TAC[FINITE_SUBSETS_RESTRICT_NEW2]
      ++ FULL_SIMP_TAC std_ss[has_size_def]
      ++ RW_TAC std_ss[extreal_pow_def]
      ++ DEP_REWRITE_TAC[PIE_lemma4]
      ++ DEP_REWRITE_TAC[PIE_lemma3]
      ++ RW_TAC std_ss[]
      ++ DEP_REWRITE_TAC[SUBSET_FINITE_I]
      ++ Q.EXISTS_TAC `t`
      ++ PSET_TAC[])
   >> (RW_TAC std_ss[sum_set_def]
      ++ DEP_REWRITE_TAC[extreal_hvgTheory.EXTREAL_SUM_IMAGE_NOT_POS_INF]
      ++ DEP_REWRITE_TAC[FINITE_SUBSETS_RESTRICT_NEW2]
      ++ FULL_SIMP_TAC std_ss[has_size_def]
      ++ RW_TAC std_ss[extreal_pow_def]
      ++ DEP_REWRITE_TAC[PIE_lemma6]
      ++ DEP_REWRITE_TAC[PIE_lemma3]
      ++ RW_TAC std_ss[]
      ++ DEP_REWRITE_TAC[SUBSET_FINITE_I]
      ++ Q.EXISTS_TAC `t`
      ++ PSET_TAC[])
   ++ FULL_SIMP_TAC std_ss[has_size_def]
   ++ KNOW_TAC(``FINITE {B | B SUBSET t:'b->bool /\ B <> EMPTY}``)
   >> (RW_TAC std_ss[FINITE_SUBSETS_RESTRICT_NEW])
   ++ REWRITE_TAC[sum_set_def]
   ++ DEP_REWRITE_TAC[GSYM EXTREAL_SUM_IMAGE_NEG]
   ++ RW_TAC std_ss[FINITE_SUBSETS_RESTRICT_NEW]
   >> (ONCE_REWRITE_TAC [EQ_SYM_EQ]
      ++ RW_TAC std_ss[extreal_pow_def]
      ++ DEP_REWRITE_TAC[PIE_lemma4]
      ++ DEP_REWRITE_TAC[PIE_lemma3]
      ++ RW_TAC std_ss[]
      ++ DEP_REWRITE_TAC[SUBSET_FINITE_I]
      ++ Q.EXISTS_TAC `t`
      ++ PSET_TAC[])
   >> (ONCE_REWRITE_TAC [EQ_SYM_EQ]
      ++ RW_TAC std_ss[extreal_pow_def]
      ++ DEP_REWRITE_TAC[PIE_lemma6]
      ++ DEP_REWRITE_TAC[PIE_lemma3]
      ++ RW_TAC std_ss[]
      ++ DEP_REWRITE_TAC[SUBSET_FINITE_I]
      ++ Q.EXISTS_TAC `t`
      ++ PSET_TAC[])
   ++ MATCH_MP_TAC EXTREAL_SUM_IMAGE_EQ1
   ++ RW_TAC std_ss[FINITE_SUBSETS_RESTRICT_NEW]
   >> (DISJ1_TAC
      ++ RW_TAC std_ss[]
      >> (RW_TAC std_ss[extreal_pow_def]
      	 ++ DEP_REWRITE_TAC[PIE_lemma4]
      	 ++ DEP_REWRITE_TAC[PIE_lemma7]
      	 ++ RW_TAC std_ss[]
     	 ++ DEP_REWRITE_TAC[SUBSET_FINITE_I]
      	 ++ Q.EXISTS_TAC `t`
      	 ++ PSET_TAC[])
     ++ RW_TAC std_ss[extreal_pow_def]
     ++ RW_TAC std_ss[GSYM extreal_hvgTheory.mul_lneg,extreal_hvgTheory.extreal_ainv_def]
     ++ DEP_REWRITE_TAC[PIE_lemma4]
     ++ REWRITE_TAC[realTheory.REAL_NEG_GE0,REAL_NEG_LE0]
     ++ ONCE_REWRITE_TAC[DISJ_SYM]
     ++ DEP_REWRITE_TAC[PIE_lemma3]
     ++ RW_TAC std_ss[]
     ++ DEP_REWRITE_TAC[SUBSET_FINITE_I]
     ++ Q.EXISTS_TAC `t`
     ++ PSET_TAC[])
  ++ RW_TAC std_ss[extreal_pow_def]
  ++ RW_TAC std_ss[GSYM extreal_hvgTheory.mul_lneg,extreal_hvgTheory.extreal_ainv_def]
   ++ FULL_SIMP_TAC std_ss[IMAGE_INSERT,BIGINTER_INSERT,o_DEF,GSPECIFICATION]
   ++ REPEAT STRIP_TAC
   ++ RW_TAC real_ss[REAL_POW_ADD, POW_1, REAL_MUL_RNEG, REAL_MUL_LNEG]
   ++ AP_TERM_TAC
   ++ AP_TERM_TAC
   ++ RW_TAC real_ss[incl_excl_temp3]
   ++ POP_ASSUM MP_TAC
   ++ POP_ASSUM MP_TAC
   ++ FULL_SIMP_TAC std_ss[SUBSET_DEF,IN_INTER,EXTENSION,GSPECIFICATION]
   ++ METIS_TAC [SUBSET_DEF,EXTENSION,IN_INSERT,IN_UNION,IN_DELETE,SUBSET_DEF,DISJOINT_DEF,NOT_IN_EMPTY,EXTENSION,IN_INSERT,IN_INTER,IN_DIFF,IN_UNIV])
++ RW_TAC std_ss[incl_excl_temp4]
++ KNOW_TAC(``EMPTY IN {B | B SUBSET t:'b->bool} ``)
>> (RW_TAC std_ss[incl_excl_temp6])
++ KNOW_TAC(``FINITE  {B | B SUBSET t:'b->bool}``)
>> (FULL_SIMP_TAC std_ss[has_size_def]
   ++ RW_TAC std_ss[FINITE_SUBSETS_RESTRICT_NEW1])
++ REPEAT DISCH_TAC
++ DEP_REWRITE_TAC[incl_excl_temp9]
++ RW_TAC std_ss[]
>> (RW_TAC std_ss[extreal_pow_def]
      ++ DEP_REWRITE_TAC[PIE_lemma4]
      ++ DEP_REWRITE_TAC[PIE_lemma7]
      ++ RW_TAC std_ss[]
      ++ DEP_REWRITE_TAC[SUBSET_FINITE_I]
      ++ Q.EXISTS_TAC `t`
      ++ PSET_TAC[has_size_def])
>> (RW_TAC std_ss[extreal_pow_def]
      ++ DEP_REWRITE_TAC[PIE_lemma6]
      ++ DEP_REWRITE_TAC[PIE_lemma7]
      ++ RW_TAC std_ss[]
      ++ DEP_REWRITE_TAC[SUBSET_FINITE_I]
      ++ Q.EXISTS_TAC `t`
      ++ PSET_TAC[has_size_def])
++ FULL_SIMP_TAC std_ss[]
++ RW_TAC real_ss[CARD_EMPTY]
++ RW_TAC real_ss[IMAGE_SING,BIGINTER_SING]
++ KNOW_TAC(`` {a INSERT B | B SUBSET t:'b->bool} = (IMAGE (\B. a INSERT B) {B | B SUBSET t:'b->bool })``)
>> (RW_TAC real_ss[GSYM simple_image_gen])
++ DISCH_TAC ++ PURE_ONCE_ASM_REWRITE_TAC [] ++ POP_ORW
++ RW_TAC real_ss[extreal_pow_def]
++ RW_TAC std_ss[prove(``!a:extreal. a <> NegInf /\ a <> PosInf ==> (Normal 1 * a = a)``, Cases ++ RW_TAC std_ss [extreal_of_num_def,extreal_mul_def] ++ REAL_ARITH_TAC)]
++ RW_TAC std_ss[GSYM extreal_pow_def]
++ KNOW_TAC (``sum_set (IMAGE (\B. a INSERT B) {B | B SUBSET (t:'b->bool)})
      (\B. Normal (- &1) pow (CARD B + 1) *  (f:('a->bool) -> extreal) (BIGINTER (IMAGE (x:'b->('a->bool)) B))) =
      sum_set {B | B SUBSET (t:'b->bool)}
      ((\B. Normal (- &1) pow (CARD B + 1) * f (BIGINTER (IMAGE x B))) o
       (\B. a INSERT B))``)
>> (RW_TAC std_ss[sum_set_def]
   ++ MATCH_MP_TAC EXTREAL_SUM_IMAGE_IMAGE1
   ++ DEP_REWRITE_TAC[topology_hvgTheory.FINITE_POWERSET]
   ++ PSET_TAC[has_size_def]
   >> (ASM_SIMP_TAC(srw_ss())[INJ_DEF,INSERT_DEF,SUBSET_DEF,EXTENSION,GSPECIFICATION]
       ++ METIS_TAC[])
   ++ DISJ1_TAC
   ++ RW_TAC std_ss[]
   ++ RW_TAC std_ss[extreal_pow_def]
      ++ DEP_REWRITE_TAC[PIE_lemma4]
      ++ DEP_REWRITE_TAC[PIE_lemma3]
      ++ RW_TAC std_ss[pred_setTheory.FINITE_INSERT]
      ++ DEP_REWRITE_TAC[SUBSET_FINITE_I]
      ++ Q.EXISTS_TAC `t`
      ++ PSET_TAC[has_size_def])
++ DISCH_TAC ++ PURE_ONCE_ASM_REWRITE_TAC [] ++ POP_ORW
++ RW_TAC std_ss[prove(``!a b:extreal. a <> PosInf /\ a <> NegInf ==> (a + (b - a) = b)``,REPEAT Cases ++ RW_TAC std_ss[extreal_of_num_def,extreal_mul_def,extreal_sub_def,extreal_add_def]++ REAL_ARITH_TAC)]
++ RW_TAC real_ss[o_DEF]
++ RW_TAC real_ss[sum_set_def]
++ MATCH_MP_TAC EXTREAL_SUM_IMAGE_EQ1
++ RW_TAC real_ss[GSPECIFICATION]
>> (DISJ1_TAC
   ++ RW_TAC std_ss[]
   >> (RW_TAC std_ss[extreal_pow_def]
      ++ DEP_REWRITE_TAC[PIE_lemma4]
      ++ DEP_REWRITE_TAC[PIE_lemma7]
      ++ RW_TAC std_ss[]
      ++ DEP_REWRITE_TAC[SUBSET_FINITE_I]
      ++ Q.EXISTS_TAC `t`
      ++ PSET_TAC[has_size_def])
  ++ RW_TAC std_ss[extreal_pow_def]
  ++ DEP_REWRITE_TAC[PIE_lemma4]
  ++ DEP_REWRITE_TAC[PIE_lemma3]
  ++ RW_TAC std_ss[pred_setTheory.FINITE_INSERT]
  ++ DEP_REWRITE_TAC[SUBSET_FINITE_I]
  ++ Q.EXISTS_TAC `t`
  ++ PSET_TAC[has_size_def])
++ RW_TAC std_ss[extreal_pow_def]
++ RW_TAC real_ss[REAL_POW_ADD,REAL_NEG_NEG]
++ KNOW_TAC (``FINITE (x':'b->bool)``)
>> (MATCH_MP_TAC SUBSET_FINITE_I
   ++ EXISTS_TAC(``t:'b->bool``)
   ++ RW_TAC real_ss[has_size_def]
   ++ FULL_SIMP_TAC std_ss[has_size_def])
++ RW_TAC real_ss[CARD_INSERT]
>> (METIS_TAC[SUBSET_DEF])
++ RW_TAC real_ss[IMAGE_INSERT,pow]);
(*--------------------------*)
val prob_biginter_not_negInf = store_thm("prob_biginter_not_negInf",
  ``!p f a s t. prob_space p /\
       	  FINITE t /\
	  (∀a'. a' ∈ IMAGE f (a INSERT t) ⇒ a' ∈ events p) /\
	  (s ∈ {t' | t' ⊆ t ∧ t' ≠ ∅}) ==>
	  (prob p (BIGINTER (IMAGE f s)) ≠ NegInf /\
	   prob p (BIGINTER (IMAGE f s)) ≠ PosInf)``,
REPEAT GEN_TAC
++ REPEAT DISCH_TAC
++ DEP_REWRITE_TAC[PROB_FINITE]
++ DEP_REWRITE_TAC[EVENTS_COUNTABLE_INTER,COUNTABLE_IMAGE,finite_countable,IMAGE_FINITE]
++ DEP_REWRITE_TAC[SUBSET_FINITE_I]
 ++ FULL_SIMP_TAC std_ss[]
++ PSET_TAC[]
>> (Q.EXISTS_TAC `t`
   ++ RW_TAC std_ss[])
>> (FIRST_X_ASSUM(MP_TAC o Q.SPEC `f:'b->('a->bool) x'`)
   ++ RW_TAC std_ss[]
   ++ `(∃x. (f x' = f x) ∧ ((x = a) ∨ x ∈ t))` by (RW_TAC std_ss[]
        ++ Q.EXISTS_TAC `x'`
        ++ METIS_TAC[])
   >> (METIS_TAC[])
   ++ METIS_TAC[])
++ PSET_TAC[pred_setTheory.IMAGE_EQ_EMPTY]);
(*--------------------------*)
val prob_biginter_insert_not_negInf = store_thm(
  "prob_biginter_insert_not_negInf",
  `` !p f a s t. prob_space p /\
       	  FINITE t /\
	  (∀a'. a' ∈ IMAGE f (a INSERT t) ⇒ a' ∈ events p) /\
	  s ∈ {a INSERT t' | t' | t' ⊆ t ∧ a INSERT t' ≠ ∅} ==>
	  (Normal (-1) pow (CARD s + 1) * 
	   prob p (BIGINTER (IMAGE f s)) ≠ NegInf) ``,
REPEAT GEN_TAC
++ REPEAT DISCH_TAC
++ PSET_TAC[]
++ RW_TAC std_ss[extreal_pow_def]
++ DEP_REWRITE_TAC[PIE_lemma4]
++ DEP_REWRITE_TAC[PIE_lemma3]
++ DEP_REWRITE_TAC[PROB_FINITE,FINITE_INSERT,EVENTS_COUNTABLE_INTER,COUNTABLE_IMAGE,finite_countable,IMAGE_FINITE]
++ DEP_REWRITE_TAC[SUBSET_FINITE_I]
++ CONJ_TAC
>> (Q.EXISTS_TAC `t`
   ++ PSET_TAC[])
++ PSET_TAC[]
>> (PAT_ASSUM (Term `∀a'. (∃x. (a' = f x) ∧ ((x = a) ∨ x ∈ t)) ⇒ a' ∈ events p`) MP_TAC
	 ++ DISCH_THEN(MP_TAC o Q.SPEC `(f:'b->'a->bool) x'`) 
	 ++ RW_TAC std_ss[]
	 ++ `(∃x. ((f:'b->'a->bool) x' = f x) ∧ ((x = a) ∨ x ∈ t))` by (RW_TAC std_ss[]
	      ++ Q.EXISTS_TAC `x'`
   	      ++ RW_TAC std_ss[])
	 >> (METIS_TAC[])
	 ++ METIS_TAC[])
++ PSET_TAC[pred_setTheory.IMAGE_EQ_EMPTY]);
(*-------------------------------*)
val prob_biginter_not_infinity_lemma1 = store_thm(
  "prob_biginter_not_infinity_lemma1",
  `` !p f a s t. prob_space p /\
       	  FINITE t /\
	  (∀a'. a' ∈ IMAGE f (a INSERT t) ⇒ a' ∈ events p) /\
	  s ∈ {t' | t' ⊆ t ∧ t' ≠ ∅} ==>
	  (Normal (-1) pow (CARD s + 1) * prob p (BIGINTER (IMAGE f s)) ≠
           PosInf) ``,
REPEAT GEN_TAC
++ REPEAT DISCH_TAC
++ PSET_TAC[]
++ RW_TAC std_ss[extreal_pow_def]
++ DEP_REWRITE_TAC[PIE_lemma6]
++ DEP_REWRITE_TAC[PIE_lemma3]
++ DEP_REWRITE_TAC[PROB_FINITE,FINITE_INSERT,EVENTS_COUNTABLE_INTER,COUNTABLE_IMAGE,finite_countable,IMAGE_FINITE]
++ DEP_REWRITE_TAC[SUBSET_FINITE_I]
++ PSET_TAC[]
>> (Q.EXISTS_TAC `t`
   ++ PSET_TAC[])
>> (PAT_ASSUM (Term `∀a'. (∃x. (a' = f x) ∧ ((x = a) ∨ x ∈ t)) ⇒ a' ∈ events p`) MP_TAC
	 ++ DISCH_THEN(MP_TAC o Q.SPEC `(f:'b->'a->bool) x'`) 
	 ++ RW_TAC std_ss[]
	 ++ `(∃x. ((f:'b->'a->bool) x' = f x) ∧ ((x = a) ∨ x ∈ t))` by (RW_TAC std_ss[]
	     ++ Q.EXISTS_TAC `x'`
   	     ++ RW_TAC std_ss[])
	 >> (METIS_TAC[])
	 ++ METIS_TAC[])
++ PSET_TAC[pred_setTheory.IMAGE_EQ_EMPTY]);
(*------------------------------*)
val prob_biginter_not_negInf_lemma2 = store_thm(
  "prob_biginter_not_negInf_lemma2",
  ``!p f a s t. prob_space p /\
       	  FINITE t /\
	  (∀a'. a' ∈ IMAGE f (a INSERT t) ⇒ a' ∈ events p) /\
	  s ∈ {t' | t' ⊆ t ∧ t' ≠ ∅} ==>
	  (Normal (-1) pow CARD s * prob p (BIGINTER (IMAGE f (a INSERT s))) ≠
NegInf)  ``,
REPEAT GEN_TAC
++ REPEAT DISCH_TAC
++ PSET_TAC[]
++ RW_TAC std_ss[extreal_pow_def]
++ DEP_REWRITE_TAC[PIE_lemma4]
++ DEP_REWRITE_TAC[PIE_lemma7]
++ DEP_REWRITE_TAC[PROB_FINITE,FINITE_INSERT,EVENTS_COUNTABLE_INTER,COUNTABLE_IMAGE,finite_countable,IMAGE_FINITE]
++ DEP_REWRITE_TAC[SUBSET_FINITE_I]
++ CONJ_TAC
>> (Q.EXISTS_TAC `t`
   ++ PSET_TAC[])
++ PSET_TAC[]
>> (PAT_ASSUM (Term `∀a'. (∃x. (a' = f x) ∧ ((x = a) ∨ x ∈ t)) ⇒ a' ∈ events p`) MP_TAC
	 ++ DISCH_THEN(MP_TAC o Q.SPEC `(f:'b->'a->bool) x'`) 
	 ++ RW_TAC std_ss[]
	 ++ `(∃x. ((f:'b->'a->bool) x' = f x) ∧ ((x = a) ∨ x ∈ t))` by (RW_TAC std_ss[]
	     ++ Q.EXISTS_TAC `x'`
   	     ++ RW_TAC std_ss[])
	 >> (METIS_TAC[])
	 ++ METIS_TAC[])
++ PSET_TAC[pred_setTheory.IMAGE_EQ_EMPTY,pred_setTheory.NOT_INSERT_EMPTY]);

(*------------------------*)
val prob_biginter_not_negInf_lemma3 = store_thm(
  "prob_biginter_not_negInf_lemma3",
  ``!p f a s t. prob_space p /\
       	  FINITE t /\
	  (∀a'. a' ∈ IMAGE f (a INSERT t) ⇒ a' ∈ events p) /\
	  s ∈ {t' | t' ⊆ t} ==>
	  (Normal (-1) pow CARD s * prob p (BIGINTER (IMAGE f (a INSERT s))) ≠
NegInf)  ``,
REPEAT GEN_TAC
++ REPEAT DISCH_TAC
++ PSET_TAC[]
++ RW_TAC std_ss[extreal_pow_def]
++ DEP_REWRITE_TAC[PIE_lemma4]
++ DEP_REWRITE_TAC[PIE_lemma7]
++ DEP_REWRITE_TAC[PROB_FINITE,FINITE_INSERT,EVENTS_COUNTABLE_INTER,COUNTABLE_IMAGE,finite_countable,IMAGE_FINITE]
++ DEP_REWRITE_TAC[SUBSET_FINITE_I]
++ CONJ_TAC
>> (Q.EXISTS_TAC `t`
   ++ PSET_TAC[])
++ PSET_TAC[]
>> (PAT_ASSUM (Term `∀a'. (∃x. (a' = f x) ∧ ((x = a) ∨ x ∈ t)) ⇒ a' ∈ events p`) MP_TAC
	 ++ DISCH_THEN(MP_TAC o Q.SPEC `(f:'b->'a->bool) x'`) 
	 ++ RW_TAC std_ss[]
	 ++ `(∃x. ((f:'b->'a->bool) x' = f x) ∧ ((x = a) ∨ x ∈ t))` by (RW_TAC std_ss[]
	    ++ Q.EXISTS_TAC `x'`
   	    ++ RW_TAC std_ss[])
	 >> (METIS_TAC[])
	 ++ METIS_TAC[])
++ PSET_TAC[pred_setTheory.IMAGE_EQ_EMPTY,pred_setTheory.NOT_INSERT_EMPTY]);
(*------------------------*)
val prob_biginter_not_PosInf_lemma4 = store_thm(
  "prob_biginter_not_PosInf_lemma4",
  ``!p f a s t. prob_space p /\
       	  FINITE t /\
	  (∀a'. a' ∈ IMAGE f (a INSERT t) ⇒ a' ∈ events p) /\
	  s ∈ {t' | t' ⊆ t} ==>
	  (Normal (-1) pow CARD s * prob p (BIGINTER (IMAGE f (a INSERT s))) ≠
PosInf)  ``,
REPEAT GEN_TAC
++ REPEAT DISCH_TAC
++ PSET_TAC[]
++ RW_TAC std_ss[extreal_pow_def]
++ DEP_REWRITE_TAC[PIE_lemma6]
++ DEP_REWRITE_TAC[PIE_lemma7]
++ DEP_REWRITE_TAC[PROB_FINITE,FINITE_INSERT,EVENTS_COUNTABLE_INTER,COUNTABLE_IMAGE,finite_countable,IMAGE_FINITE]
++ DEP_REWRITE_TAC[SUBSET_FINITE_I]
++ CONJ_TAC
>> (Q.EXISTS_TAC `t`
   ++ PSET_TAC[])
++ PSET_TAC[]
>> (PAT_ASSUM (Term `∀a'. (∃x. (a' = f x) ∧ ((x = a) ∨ x ∈ t)) ⇒ a' ∈ events p`) MP_TAC
	 ++ DISCH_THEN(MP_TAC o Q.SPEC `(f:'b->'a->bool) x'`) 
	 ++ RW_TAC std_ss[]
	 ++ `(∃x. ((f:'b->'a->bool) x' = f x) ∧ ((x = a) ∨ x ∈ t))` by (RW_TAC std_ss[]
	     ++ Q.EXISTS_TAC `x'`
   	     ++ RW_TAC std_ss[])
	 >> (METIS_TAC[])
	 ++ METIS_TAC[])
++ PSET_TAC[pred_setTheory.IMAGE_EQ_EMPTY,pred_setTheory.NOT_INSERT_EMPTY]);


(*----------------------PROB_INCLUSION_EXCLUSION----------------------------------*)
val PROB_INCLUSION_EXCLUSION = store_thm("PROB_INCLUSION_EXCLUSION",
  ``!p (s:('a->bool)->bool) x. 
prob_space p /\ 
FINITE s /\ 
(!a. a IN (IMAGE x s) ==> a IN events p) ==> 
  ((prob p (BIGUNION (IMAGE x s))) =
    sum_set {t | t SUBSET s /\ ~(t = {})}
      (\t. Normal (- &1) pow (CARD t + 1) * (prob p (BIGINTER (IMAGE x t)))))``,
FULL_SIMP_TAC std_ss[AND_IMP, RIGHT_FORALL_IMP_THM]
++ REWRITE_TAC [AND_IMP_INTRO]
++ REWRITE_TAC [GSYM CONJ_ASSOC]
++ REWRITE_TAC [PULL_FORALL]
++ FULL_SIMP_TAC std_ss[RIGHT_FORALL_IMP_THM]
++ FULL_SIMP_TAC std_ss[AND_IMP_INTRO]
++ RW_TAC std_ss[]
++ POP_ASSUM MP_TAC
++ POP_ASSUM MP_TAC
++ Q.SPEC_TAC (`x`, `x`) 
++ FULL_SIMP_TAC std_ss[AND_IMP,RIGHT_FORALL_IMP_THM]
++ KNOW_TAC (`` (!x:('a->bool)->'b->bool.
 (∀a. a ∈ IMAGE x s ⇒ a ∈ events p) ⇒
(prob p (BIGUNION (IMAGE x s)) =
 sum_set {t | t ⊆ s ∧ t ≠ ∅}
   (λt. Normal (-1) pow (CARD t + 1) * prob p (BIGINTER (IMAGE x t))))) = (\A:('a->bool)->bool. (!x.
(∀a. a ∈ IMAGE x A ⇒ a ∈ events p) ⇒
(prob p (BIGUNION (IMAGE x A)) =
 sum_set {t | t ⊆ A ∧ t ≠ ∅}
   (λt. Normal (-1) pow (CARD t + 1) * prob p (BIGINTER (IMAGE x t)))))) s ``)
>> (RW_TAC std_ss[])
++ DISCH_TAC ++ POP_ORW 
++ Q.SPEC_TAC (`s`, `A`)
++ MATCH_MP_TAC (PROVE[has_size_def] (Term`(!A n. has_size A n ==> P A) ==> (!A. FINITE A ==> P A)`))
++ REPEAT GEN_TAC
++ FULL_SIMP_TAC std_ss[]
++ Q.SPEC_TAC (`A`, `A`) 
++ KNOW_TAC (`` 
  (∀A:('a->bool)->bool.
  has_size A n ⇒
  ∀x.
    (∀a. a ∈ IMAGE x A ⇒ a ∈ events p) ⇒
    (prob p (BIGUNION (IMAGE x A)) =
     sum_set {t | t ⊆ A ∧ t ≠ ∅}
       (λt. Normal (-1) pow (CARD t + 1) * prob p (BIGINTER (IMAGE x t))))) = (\n:num. (!A:('a->bool)->bool.
  has_size A n ⇒
  ∀x.
    (∀a. a ∈ IMAGE x A ⇒ a ∈ events p) ⇒
    (prob p (BIGUNION (IMAGE x A)) =
     sum_set {t | t ⊆ A ∧ t ≠ ∅}
       (λt. Normal (-1) pow (CARD t + 1) * prob p (BIGINTER (IMAGE x t)))))) n ``)
>> (RW_TAC std_ss[])
++ DISCH_TAC ++ POP_ORW
++ Q.SPEC_TAC (`n`, `n`) 
++ MATCH_MP_TAC temp3
++ FULL_SIMP_TAC std_ss[]
++ Induct_on `n`
>> (FULL_SIMP_TAC std_ss[has_size_clauses]
   ++ RW_TAC std_ss[]
   ++ RW_TAC std_ss[IMAGE_EMPTY,BIGUNION_EMPTY,SUBSET_EMPTY]
   ++ RW_TAC std_ss[GSPEC_F, sum_set_def,extreal_hvgTheory.EXTREAL_SUM_IMAGE_EMPTY]
   ++ FULL_SIMP_TAC std_ss[pred_setTheory.IMAGE_EMPTY]
   ++ RW_TAC std_ss[PROB_EMPTY])
++ DISCH_TAC
++ FULL_SIMP_TAC std_ss[has_size_clauses]
++ REPEAT GEN_TAC
++ FULL_SIMP_TAC std_ss[GSYM LEFT_FORALL_IMP_THM]
++ REPEAT GEN_TAC
++ REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))
++ FULL_SIMP_TAC std_ss[FORALL_INSERT]
++ STRIP_TAC
++ REWRITE_TAC[IMAGE_INSERT,BIGUNION_INSERT]
++ REPEAT (STRIP_TAC)
++ MATCH_MP_TAC EQ_TRANS
++ EXISTS_TAC( 
``(prob p (x a) + 
  prob p (BIGUNION (IMAGE (x:('a->bool)->('b->bool)) t))) -
  prob p (x a INTER BIGUNION (IMAGE x t)):extreal``)
++ CONJ_TAC
>> (KNOW_TAC(
``(((x:('a->bool)->'b->bool) a) IN events p) /\ 
   BIGUNION (IMAGE (x:('a->bool)->'b->bool ) t) IN events p``)
   >> (ASM_REWRITE_TAC[]
      ++ PAT_ASSUM (Term ` ∀a'. a' ∈ x a INSERT IMAGE x t ⇒ a' ∈ events p`) MP_TAC
      ++ KNOW_TAC(``FINITE (t:('a->bool)->bool)``)
      >> (FULL_SIMP_TAC std_ss[has_size_def])
      ++ KNOW_TAC(``
          (∀(a':'b->bool). 
	    a' ∈ (x:('a->bool)->('b->bool)) a INSERT 
	    IMAGE x (t:('a->bool)->bool) ⇒ a' ∈ events p) ⇒ 
		 x a ∈ events p ∧ 
	 BIGUNION (IMAGE (x:('a->bool)->('b->bool)) (t:('a->bool)->bool)) ∈ events p =
         (\ (t:('a->bool)->bool). (∀(a':'b->bool). 
	  a' ∈ x a INSERT IMAGE x t ⇒ a' ∈ events p) ⇒
	  x a ∈ events p ∧ BIGUNION (IMAGE x t) ∈ events p) t``)
      >> (RW_TAC std_ss[])
      ++ DISCH_TAC ++ POP_ORW
      ++ Q.SPEC_TAC (`t`, `u`) 
      ++ MATCH_MP_TAC FINITE_INDUCT
      ++ FULL_SIMP_TAC std_ss[IMAGE_EMPTY,IMAGE_INSERT,BIGUNION_EMPTY,BIGUNION_INSERT]
      ++ FULL_SIMP_TAC std_ss[FORALL_INSERT]
      ++ RW_TAC std_ss[EVENTS_UNION,EVENTS_EMPTY])
   ++ FULL_SIMP_TAC std_ss[ PULL_FORALL,AND_IMP_INTRO]
   ++ PAT_ASSUM (Term `P (x a) `) MP_TAC
   ++ Q.SPEC_TAC(`BIGUNION (IMAGE x t)`,`t'`)
   ++ Q.SPEC_TAC(`x a`,`s'`)
   ++ RW_TAC std_ss[]
   ++ MP_TAC (Q.ISPECL[`p:('b -> bool) # (('b -> bool) -> bool) # (('b -> bool) -> extreal)`,`(s' INTER t':'b->bool)`,`(t' DIFF s':'b->bool)`,`(s' INTER t':'b->bool UNION (t' DIFF s':'b->bool))`] PROB_ADDITIVE)
++ MP_TAC (Q.ISPECL[`p:('b -> bool) # (('b -> bool) -> bool) # (('b -> bool) -> extreal)`,`s':'b->bool`, `t' DIFF s':'b->bool`,`(s':'b->bool UNION (t' DIFF s':'b->bool))`] PROB_ADDITIVE)
   ++ ONCE_REWRITE_TAC[temp5,temp6]
   ++ FULL_SIMP_TAC std_ss[]
   ++ KNOW_TAC (``DISJOINT (s':'b->bool) (t' DIFF s')``)
   >> (RW_TAC std_ss[DISJOINT_DEF]
      ++ SIMP_TAC (srw_ss()) [DISJOINT_DEF,DIFF_DEF,IN_INTER,EXTENSION,GSPECIFICATION,EXCLUDED_MIDDLE]
      ++ RW_TAC std_ss[DISJ_ASSOC]
      ++ ONCE_REWRITE_TAC[DISJ_SYM]
      ++ RW_TAC std_ss[DISJ_ASSOC])
   ++ RW_TAC std_ss[]
   ++ FULL_SIMP_TAC std_ss[]
   ++ KNOW_TAC (``DISJOINT ((s':'b->bool) INTER t') (t' DIFF s')``)
   >> (RW_TAC std_ss[DISJOINT_DEF]
      ++ SIMP_TAC (srw_ss()) [DISJOINT_DEF,DIFF_DEF,IN_INTER,EXTENSION,GSPECIFICATION,EXCLUDED_MIDDLE]
      ++ ONCE_REWRITE_TAC[DISJ_SYM]
      ++ RW_TAC std_ss[GSYM DISJ_ASSOC]
      ++ DISJ2_TAC
      ++ RW_TAC std_ss[DISJ_ASSOC])
   ++ RW_TAC std_ss[]
   ++ `t' DIFF (s':'b->bool) ∈ events p /\ s' ∩ t' ∈ events p` by (DEP_REWRITE_TAC[EVENTS_INTER,EVENTS_DIFF] ++ RW_TAC std_ss[])


   ++ FULL_SIMP_TAC std_ss[EVENTS_INTER,EVENTS_DIFF]
   ++ ONCE_ASM_REWRITE_TAC[]
   ++ MATCH_MP_TAC (prove(``!a b c:extreal. a <> NegInf /\ a <> PosInf /\ c <> NegInf /\ c <> PosInf ==> 
      	     		      		   (a + b = a + (c + b) - c)``, REPEAT Cases 
++ RW_TAC std_ss [extreal_le_def,extreal_sub_def,le_infty,le_refl,extreal_add_def]
++ REAL_ARITH_TAC))
   ++ DEP_REWRITE_TAC[PROB_FINITE]
   ++ RW_TAC std_ss[])
++ FIRST_X_ASSUM(MP_TAC o Q.SPEC `n:num`) 
++ REWRITE_TAC[LT_SUC]
++ RW_TAC std_ss[]


++ KNOW_TAC(``(prob (p: (β -> bool) # ((β -> bool) -> bool) # ((β -> bool) -> extreal)) (BIGUNION (IMAGE (x:(α -> bool) -> β -> bool) (t:(α -> bool) -> bool))) =
           sum_set {t' | t' ⊆ t ∧ t' ≠ ∅}
             (λt. Normal (-1) pow (CARD t + 1) * prob p (BIGINTER (IMAGE x t))))``)
>> (RW_TAC std_ss[]
   ++ PAT_ASSUM (Term `∀A.
        has_size A n ⇒
        ∀x.
          (∀a. a ∈ IMAGE x A ⇒ a ∈ events p) ⇒
          (prob p (BIGUNION (IMAGE x A)) =
           sum_set {t | t ⊆ A ∧ t ≠ ∅}
             (λt. Normal (-1) pow (CARD t + 1) * prob p (BIGINTER (IMAGE x t))))`) MP_TAC
   ++ DISCH_THEN (MP_TAC o Q.SPECL [`t:('a->bool)->bool`])
   ++ RW_TAC std_ss[]
   ++ POP_ASSUM (MP_TAC o Q.SPEC `t`)
   ++ RW_TAC std_ss[]
   ++ FIRST_X_ASSUM(MP_TAC o Q.SPEC `x`)
   ++ RW_TAC std_ss[]
   ++ `(∀a. a ∈ IMAGE x t ⇒ a ∈ events p)` by ( RW_TAC std_ss[IN_IMAGE]
      ++ FIRST_X_ASSUM(MP_TAC o Q.SPEC `x (x':'a->bool)`)
      ++ RW_TAC std_ss[]
      ++ `x (x':'a->bool) ∈ x a INSERT IMAGE x t` by (RW_TAC std_ss[IN_INSERT, IN_IMAGE]
         ++ DISJ2_TAC
      	 ++ Q.EXISTS_TAC `x':'a->bool`
      ++ RW_TAC std_ss[])
   ++ FULL_SIMP_TAC std_ss[])
++ FULL_SIMP_TAC std_ss[])
++ DISCH_TAC
++ POP_ORW
++ FULL_SIMP_TAC std_ss[INTER_BIGUNION]
++ FULL_SIMP_TAC std_ss[GSYM IMAGE_DEF]
++ FULL_SIMP_TAC std_ss[GSYM IMAGE_COMPOSE,o_DEF]
++ FIRST_X_ASSUM(MP_TAC o Q.SPEC `t`) 
++ RW_TAC std_ss[]
++ FIRST_X_ASSUM(MP_TAC o Q.SPEC `(λx'. x a ∩ x x')`)
++ RW_TAC std_ss[]
++ FULL_SIMP_TAC std_ss[GSYM IMAGE_INSERT]

++ `(∀a'. (a' ∈ IMAGE (\ s. (x) a ∩ x s) t) ⇒ (a' ∈ events p))` by (RW_TAC std_ss[IN_IMAGE]
   ++ MATCH_MP_TAC EVENTS_INTER
   ++ RW_TAC std_ss[]
   >> (FIRST_X_ASSUM(MP_TAC o Q.SPEC `(x (a:'a->bool))`)
      ++ RW_TAC std_ss[]
      ++ `x a ∈ IMAGE x (a INSERT t)` by (RW_TAC std_ss[IN_IMAGE]
          ++ Q.EXISTS_TAC `a:'a->bool`
       	  ++ RW_TAC std_ss[pred_setTheory.COMPONENT])
      ++ FULL_SIMP_TAC std_ss[]
      ++ FIRST_X_ASSUM(MP_TAC o Q.SPEC `(x (s:'a->bool))`)
      ++ RW_TAC std_ss[])
   ++ `x s ∈ IMAGE x (a INSERT t)` by (RW_TAC std_ss[IN_IMAGE]
      ++ Q.EXISTS_TAC `s:'a->bool`
      ++ RW_TAC std_ss[pred_setTheory.IN_INSERT])
   ++ FULL_SIMP_TAC std_ss[])
++ FULL_SIMP_TAC std_ss[]
++ FULL_SIMP_TAC std_ss[lemma_NEW]
++ KNOW_TAC (
``sum_set
  ({t' | t' ⊆ t ∧ t' ≠ ∅} ∪
   {a INSERT t' | t' | t' ⊆ t:('a->bool)->bool ∧ a INSERT t' ≠ ∅})
     (\t. Normal (-1) pow (CARD t + 1) * 
     prob p (BIGINTER (IMAGE (x:('a->bool)->('b->bool)) t))) = 
sum_set
  ({t' | t' SUBSET t /\ t' <> EMPTY})
    (\t. Normal (-1) pow (CARD t + 1) * 
    prob p (BIGINTER (IMAGE x t))) + 
sum_set 
  ({a INSERT t' | t' | t' SUBSET t /\ a INSERT t' <> EMPTY})
   (\t. Normal (-1) pow (CARD t + 1) * 
   prob p (BIGINTER (IMAGE x t)))``)
>> (REWRITE_TAC[sum_set_def]
   ++ MATCH_MP_TAC EXTREAL_SUM_IMAGE_DISJOINT_UNION1
   ++ KNOW_TAC (
``FINITE {B | B SUBSET t:('a->bool)->bool /\ B <> EMPTY} /\
FINITE {a INSERT B | B | B SUBSET t /\ a INSERT B <> EMPTY} /\
DISJOINT {B | B SUBSET t /\ B <> EMPTY} 
	 {a INSERT B | B | B SUBSET t /\ a INSERT B <> EMPTY} = 
(FINITE( IMAGE (\B. B) {B | B SUBSET t /\ B <> EMPTY}) /\
 FINITE  (IMAGE (\B. a INSERT B) { B | B SUBSET t /\ a INSERT B <> EMPTY}) /\
 DISJOINT  (IMAGE (\B. B){B | B SUBSET t /\ B <> EMPTY}) 
 	   (IMAGE (\B. a INSERT B){ B | B SUBSET t /\ a INSERT B <> EMPTY}))``)
   >> (RW_TAC std_ss[GSYM simple_image_gen])
   ++ DISCH_TAC ++ PURE_ONCE_ASM_REWRITE_TAC [] ++ POP_ORW
   ++ FULL_SIMP_TAC std_ss[has_size_def]
   ++ FULL_SIMP_TAC std_ss[FINITE_SUBSETS_RESTRICT_NEW,IMAGE_FINITE]
   ++ RW_TAC std_ss[GSYM simple_image_gen]
   >> (RW_TAC std_ss[IN_DISJOINT,GSPECIFICATION]
      ++ METIS_TAC [EXTENSION,IN_INSERT,IN_UNION,IN_DELETE,SUBSET_DEF,
DISJOINT_DEF,NOT_IN_EMPTY,EXTENSION,IN_INSERT,IN_INTER,IN_DIFF,IN_UNIV])
   ++ DISJ1_TAC
   ++ RW_TAC std_ss[pred_setTheory.IN_UNION]
   >> (RW_TAC std_ss[extreal_pow_def]
      ++ DEP_REWRITE_TAC[PIE_lemma4]
      ++ DEP_REWRITE_TAC[PIE_lemma3]
      ++ DEP_REWRITE_TAC[prob_biginter_not_negInf]
      ++ CONJ_TAC
      >> (Q.EXISTS_TAC `a`
      	 ++ Q.EXISTS_TAC `t`
	 ++ RW_TAC std_ss[])
      ++ DEP_REWRITE_TAC[SUBSET_FINITE_I]
      ++ Q.EXISTS_TAC `t`
      ++ PSET_TAC[])
  ++ DEP_REWRITE_TAC[prob_biginter_insert_not_negInf]
  ++ Q.EXISTS_TAC `a`
  ++ Q.EXISTS_TAC `t`
  ++ RW_TAC std_ss[])
++ DISCH_THEN SUBST1_TAC
++ RW_TAC std_ss[NOT_INSERT_EMPTY]
++ DEP_REWRITE_TAC[incl_excl_temp1]
++ DEP_REWRITE_TAC[PROB_FINITE]
++ RW_TAC std_ss[]
>> (PSET_TAC[])
>> (RW_TAC std_ss[sum_set_def]
   ++ DEP_REWRITE_TAC[extreal_hvgTheory.EXTREAL_SUM_IMAGE_NOT_POS_INF]
   ++ DEP_REWRITE_TAC[FINITE_SUBSETS_RESTRICT_NEW2]
   ++ FULL_SIMP_TAC std_ss[has_size_def]
   ++ RW_TAC std_ss[]
   ++ DEP_REWRITE_TAC[prob_biginter_not_infinity_lemma1]
   ++ Q.EXISTS_TAC `a`
   ++ Q.EXISTS_TAC `t`
   ++ RW_TAC std_ss[])
>> (RW_TAC std_ss[sum_set_def]
   ++ DEP_REWRITE_TAC[extreal_hvgTheory.EXTREAL_SUM_IMAGE_NOT_NEG_INF]
   ++ DEP_REWRITE_TAC[FINITE_SUBSETS_RESTRICT_NEW2]
   ++ FULL_SIMP_TAC std_ss[has_size_def]
   ++ RW_TAC std_ss[]
   ++ RW_TAC std_ss[extreal_pow_def]
   ++ DEP_REWRITE_TAC[PIE_lemma4]
   ++ DEP_REWRITE_TAC[PIE_lemma3]
   ++ DEP_REWRITE_TAC[prob_biginter_not_negInf]
   ++ CONJ_TAC
   >> (Q.EXISTS_TAC `a`
       ++ Q.EXISTS_TAC `t`
       ++ RW_TAC std_ss[])
    ++ DEP_REWRITE_TAC[SUBSET_FINITE_I]
    ++ Q.EXISTS_TAC `t`
    ++ PSET_TAC[])
++ MATCH_MP_TAC EQ_TRANS
++ EXISTS_TAC(``prob p ((x:('a->bool)->'b->bool) a) +
              sum_set {B | B SUBSET t /\ ~(B = {})}
                  (\B. Normal (-(&1)) pow (CARD B) *
                       prob p (BIGINTER(IMAGE x (a INSERT B))))``)
++ CONJ_TAC
>> (DEP_REWRITE_TAC[incl_excl_temp2]
   ++ RW_TAC std_ss[]
   >> (PSET_TAC[PROB_FINITE])
   >> (PSET_TAC[PROB_FINITE])
   >> (RW_TAC std_ss[sum_set_def]
      ++ DEP_REWRITE_TAC[extreal_hvgTheory.EXTREAL_SUM_IMAGE_NOT_NEG_INF]
      ++ DEP_REWRITE_TAC[FINITE_SUBSETS_RESTRICT_NEW2]
      ++ FULL_SIMP_TAC std_ss[has_size_def]
      ++ RW_TAC std_ss[extreal_pow_def]
      ++ DEP_REWRITE_TAC[PIE_lemma4]
      ++ DEP_REWRITE_TAC[PIE_lemma3]
      ++ DEP_REWRITE_TAC[prob_biginter_not_negInf]
      ++ CONJ_TAC
      >> (Q.EXISTS_TAC `a`
       	 ++ Q.EXISTS_TAC `t`
       	 ++ RW_TAC std_ss[]
	 ++ PSET_TAC[]
	 ++ DEP_REWRITE_TAC[EVENTS_INTER]
	 ++ PSET_TAC[]
	 ++ PAT_ASSUM (Term `∀a'. (∃x'. (a' = x x') ∧ ((x' = a) ∨ x' ∈ t)) ⇒ a' ∈ events p`) MP_TAC
	 ++ DISCH_THEN(MP_TAC o Q.SPEC `(x:('a->bool)->'b->bool) x'`) 
	 ++ RW_TAC std_ss[]
	 ++ `(∃x''. ((x:('a->bool)->'b->bool) x' = x x'') ∧ ((x'' = a) ∨ x'' ∈ t))` by (RW_TAC std_ss[]
	    ++ Q.EXISTS_TAC `x'`
   	    ++ RW_TAC std_ss[])
	 >> (METIS_TAC[])
	 ++ METIS_TAC[])
     ++ DEP_REWRITE_TAC[SUBSET_FINITE_I]
     ++ Q.EXISTS_TAC `t`
     ++ PSET_TAC[])
   >> (RW_TAC std_ss[sum_set_def]
      ++ DEP_REWRITE_TAC[extreal_hvgTheory.EXTREAL_SUM_IMAGE_NOT_POS_INF]
      ++ DEP_REWRITE_TAC[FINITE_SUBSETS_RESTRICT_NEW2]
      ++ FULL_SIMP_TAC std_ss[has_size_def]
      ++ RW_TAC std_ss[]
      ++ DEP_REWRITE_TAC[prob_biginter_not_infinity_lemma1]
      ++ Q.EXISTS_TAC `a`
      ++ Q.EXISTS_TAC `t`
      ++ RW_TAC std_ss[]
      ++ PSET_TAC[]
      ++ DEP_REWRITE_TAC[EVENTS_INTER]
      ++ PSET_TAC[]
      ++ PAT_ASSUM (Term `∀a'. (∃x'. (a' = x x') ∧ ((x' = a) ∨ x' ∈ t)) ⇒ a' ∈ events p`) MP_TAC
      ++ DISCH_THEN(MP_TAC o Q.SPEC `(x:('a->bool)->'b->bool) x'`) 
      ++ RW_TAC std_ss[]
      ++ `(∃x''. ((x:('a->bool)->'b->bool) x' = x x'') ∧ ((x'' = a) ∨ x'' ∈ t))` by (RW_TAC std_ss[]
         ++ Q.EXISTS_TAC `x'`
       	 ++ RW_TAC std_ss[])
      >> (METIS_TAC[])
      	 ++ METIS_TAC[])
      ++ FULL_SIMP_TAC std_ss[has_size_def]
      ++ KNOW_TAC(``FINITE {B | B SUBSET t:('a->bool)->bool /\ B <> EMPTY}``)
      >> (RW_TAC std_ss[FINITE_SUBSETS_RESTRICT_NEW])
      	 ++ REWRITE_TAC[sum_set_def]
   	 ++ DEP_REWRITE_TAC[GSYM EXTREAL_SUM_IMAGE_NEG]
   	 ++ RW_TAC std_ss[FINITE_SUBSETS_RESTRICT_NEW]
      >> (  ONCE_REWRITE_TAC [EQ_SYM_EQ]
      	  ++ RW_TAC std_ss[extreal_pow_def]
      	  ++ DEP_REWRITE_TAC[PIE_lemma4]
      	  ++ DEP_REWRITE_TAC[PIE_lemma3]
      	  ++ DEP_REWRITE_TAC[prob_biginter_not_negInf]
      	  ++ CONJ_TAC
      	  >> (Q.EXISTS_TAC `a`
       	     ++ Q.EXISTS_TAC `t`
       	     ++ RW_TAC std_ss[]
	     ++ PSET_TAC[]
	     ++ DEP_REWRITE_TAC[EVENTS_INTER]
	     ++ PSET_TAC[]
	     ++ PAT_ASSUM (Term `∀a'. (∃x'. (a' = x x') ∧ ((x' = a) ∨ x' ∈ t)) ⇒ a' ∈ events p`) MP_TAC
	     ++ DISCH_THEN(MP_TAC o Q.SPEC `(x:('a->bool)->'b->bool) x'`) 
	     ++ RW_TAC std_ss[]
	     ++ `(∃x''. ((x:('a->bool)->'b->bool) x' = x x'') ∧ ((x'' = a) ∨ x'' ∈ t))` by (RW_TAC std_ss[]
	        ++ Q.EXISTS_TAC `x'`
   	     	++ RW_TAC std_ss[])
	 	>> (METIS_TAC[])
		++ METIS_TAC[])
     	     ++ DEP_REWRITE_TAC[SUBSET_FINITE_I]
     	     ++ Q.EXISTS_TAC `t`
     	     ++ PSET_TAC[])
   >> (ONCE_REWRITE_TAC [EQ_SYM_EQ]
       ++ DEP_REWRITE_TAC[prob_biginter_not_infinity_lemma1]
      ++ Q.EXISTS_TAC `a`
      ++ Q.EXISTS_TAC `t`
      ++ RW_TAC std_ss[]
      ++ PSET_TAC[]
      ++ DEP_REWRITE_TAC[EVENTS_INTER]
      ++ PSET_TAC[]
      ++ PAT_ASSUM (Term `∀a'. (∃x'. (a' = x x') ∧ ((x' = a) ∨ x' ∈ t)) ⇒ a' ∈ events p`) MP_TAC
      ++ DISCH_THEN(MP_TAC o Q.SPEC `(x:('a->bool)->'b->bool) x'`) 
      ++ RW_TAC std_ss[]
      ++ `(∃x''. ((x:('a->bool)->'b->bool) x' = x x'') ∧ ((x'' = a) ∨ x'' ∈ t))` by (RW_TAC std_ss[]
         ++ Q.EXISTS_TAC `x'`
       	 ++ RW_TAC std_ss[])
      >> (METIS_TAC[])
      	 ++ METIS_TAC[])
   ++ MATCH_MP_TAC EXTREAL_SUM_IMAGE_EQ1
   ++ RW_TAC std_ss[FINITE_SUBSETS_RESTRICT_NEW]
>> (DISJ1_TAC
   ++ RW_TAC std_ss[]
   >> (DEP_REWRITE_TAC[prob_biginter_not_negInf_lemma2]
   ++ Q.EXISTS_TAC `t`
   ++ RW_TAC std_ss[])
   ++ RW_TAC std_ss[extreal_pow_def]
     ++ RW_TAC std_ss[GSYM extreal_hvgTheory.mul_lneg,extreal_hvgTheory.extreal_ainv_def]
     ++ DEP_REWRITE_TAC[PIE_lemma4]
     ++ REWRITE_TAC[realTheory.REAL_NEG_GE0,REAL_NEG_LE0]
     ++ ONCE_REWRITE_TAC[DISJ_SYM]
     ++ DEP_REWRITE_TAC[PIE_lemma3]
     ++ DEP_REWRITE_TAC[prob_biginter_not_negInf]
      	  ++ CONJ_TAC
      	  >> (Q.EXISTS_TAC `a`
       	     ++ Q.EXISTS_TAC `t`
       	     ++ RW_TAC std_ss[]
	     ++ PSET_TAC[]
	     ++ DEP_REWRITE_TAC[EVENTS_INTER]
	     ++ PSET_TAC[]
	     ++ PAT_ASSUM (Term `∀a'. (∃x'. (a' = x x') ∧ ((x' = a) ∨ x' ∈ t)) ⇒ a' ∈ events p`) MP_TAC
	     ++ DISCH_THEN(MP_TAC o Q.SPEC `(x:('a->bool)->'b->bool) x''`) 
	     ++ RW_TAC std_ss[]
	     ++ `(∃x'. ((x:('a->bool)->'b->bool) x'' = x x'') ∧ ((x' = a) ∨ x' ∈ t))` by (RW_TAC std_ss[]
	        ++ Q.EXISTS_TAC `x''`
   	     	++ RW_TAC std_ss[])
	 	>> (METIS_TAC[])
		++ METIS_TAC[])
     	     ++ DEP_REWRITE_TAC[SUBSET_FINITE_I]
     	     ++ Q.EXISTS_TAC `t`
     	     ++ PSET_TAC[])
++ RW_TAC std_ss[extreal_pow_def]
  ++ RW_TAC std_ss[GSYM extreal_hvgTheory.mul_lneg,extreal_hvgTheory.extreal_ainv_def]
   ++ FULL_SIMP_TAC std_ss[IMAGE_INSERT,BIGINTER_INSERT,o_DEF,GSPECIFICATION]
   ++ REPEAT STRIP_TAC
   ++ RW_TAC real_ss[REAL_POW_ADD, POW_1, REAL_MUL_RNEG, REAL_MUL_LNEG]
   ++ AP_TERM_TAC
   ++ AP_TERM_TAC
   ++ RW_TAC real_ss[incl_excl_temp3]
   ++ POP_ASSUM MP_TAC
   ++ POP_ASSUM MP_TAC
   ++ FULL_SIMP_TAC std_ss[SUBSET_DEF,IN_INTER,EXTENSION,GSPECIFICATION]
   ++ METIS_TAC [SUBSET_DEF,EXTENSION,IN_INSERT,IN_UNION,IN_DELETE,SUBSET_DEF,DISJOINT_DEF,NOT_IN_EMPTY,EXTENSION,IN_INSERT,IN_INTER,IN_DIFF,IN_UNIV])
++ RW_TAC std_ss[incl_excl_temp4]
++ KNOW_TAC(``EMPTY IN {B | B SUBSET t:('a->bool)->bool} ``)
>> (RW_TAC std_ss[incl_excl_temp6])
++ KNOW_TAC(``FINITE  {B | B SUBSET t:('a->bool)->bool}``)
>> (FULL_SIMP_TAC std_ss[has_size_def]
   ++ RW_TAC std_ss[FINITE_SUBSETS_RESTRICT_NEW1])
++ REPEAT DISCH_TAC
++ DEP_REWRITE_TAC[incl_excl_temp9]
++ RW_TAC std_ss[]
>> (DEP_REWRITE_TAC[prob_biginter_not_negInf_lemma3]
   ++ Q.EXISTS_TAC `t`
   ++ FULL_SIMP_TAC std_ss[has_size_def])
>> (DEP_REWRITE_TAC[ prob_biginter_not_PosInf_lemma4]
   ++ Q.EXISTS_TAC `t`
   ++ FULL_SIMP_TAC std_ss[has_size_def])
++ FULL_SIMP_TAC std_ss[]
++ RW_TAC real_ss[CARD_EMPTY]
++ RW_TAC real_ss[IMAGE_SING,BIGINTER_SING]	
++ FULL_SIMP_TAC std_ss[GSYM SUBSET_DEF]
++ RW_TAC std_ss[NOT_INSERT_EMPTY]
++ KNOW_TAC(`` {a INSERT B | B SUBSET t:('a->bool)->bool} = (IMAGE (\B. a INSERT B) {B | B SUBSET t:('a->bool)->bool })``)
>> (RW_TAC real_ss[GSYM simple_image_gen])
++ DISCH_TAC ++ PURE_ONCE_ASM_REWRITE_TAC [] ++ POP_ORW
++ RW_TAC real_ss[extreal_pow_def]
++ DEP_REWRITE_TAC[prove(``!a:extreal. a <> NegInf /\ a <> PosInf ==> (Normal 1 * a = a)``, Cases ++ RW_TAC std_ss [extreal_of_num_def,extreal_mul_def] ++ REAL_ARITH_TAC)]
++ DEP_REWRITE_TAC[PROB_FINITE]
++ RW_TAC std_ss[]
>> (PSET_TAC[])
++ RW_TAC std_ss[GSYM extreal_pow_def]
++ KNOW_TAC (``sum_set (IMAGE (\B. a INSERT B) {B | B SUBSET (t:('a->bool)->bool)})
      (\B. Normal (- &1) pow (CARD B + 1) *  (prob p  (BIGINTER (IMAGE (x:('a->bool)->'b->bool) B)))) =
      sum_set {B | B SUBSET (t:('a->bool)->bool)}
      ((\B. Normal (- &1) pow (CARD B + 1) * prob p (BIGINTER (IMAGE (x:('a->bool)->'b->bool) B))) o
       (\B. a INSERT B))``)
>> (RW_TAC std_ss[sum_set_def]
   ++ MATCH_MP_TAC EXTREAL_SUM_IMAGE_IMAGE1
   ++ DEP_REWRITE_TAC[topology_hvgTheory.FINITE_POWERSET]
   ++ FULL_SIMP_TAC std_ss[has_size_def]
   ++ RW_TAC std_ss[]
   >> (PSET_TAC[PIE_lemma8])
   ++ DISJ1_TAC
   ++ RW_TAC std_ss[]
   ++ DEP_REWRITE_TAC[prob_biginter_insert_not_negInf]
   >> (Q.EXISTS_TAC `a`
       ++ Q.EXISTS_TAC `t`
       	     ++ RW_TAC std_ss[]
	     >> (PSET_TAC[]
	     ++ PAT_ASSUM (Term `∀x'. (∃x''. (x' = x x'') ∧ ((x'' = a) ∨ x'' ∈ t)) ⇒ x' ∈ events p`) MP_TAC
	     ++ DISCH_THEN(MP_TAC o Q.SPEC `(x:('a->bool)->'b->bool) x''`) 
	     ++ RW_TAC std_ss[]
	     ++ `(∃x'''. ((x:('a->bool)->'b->bool) x'' = x x''') ∧ ((x''' = a) ∨ x''' ∈ t))` by (RW_TAC std_ss[]
	        ++ Q.EXISTS_TAC `x''`
   	     	++ RW_TAC std_ss[])
	 	>> (METIS_TAC[])
		++ METIS_TAC[])
   ++ PSET_TAC [] ++ Q.EXISTS_TAC `B` ++ PSET_TAC[NOT_INSERT_EMPTY]))
++ DISCH_TAC ++ PURE_ONCE_ASM_REWRITE_TAC [] ++ POP_ORW
++ DEP_REWRITE_TAC[prove(``!a b:extreal. a <> PosInf /\ a <> NegInf ==> (a + (b - a) = b)``,REPEAT Cases ++ RW_TAC std_ss[extreal_of_num_def,extreal_mul_def,extreal_sub_def,extreal_add_def]++ REAL_ARITH_TAC)]
++ CONJ_TAC
>> (PSET_TAC[PROB_FINITE])
++ RW_TAC real_ss[o_DEF]
++ RW_TAC real_ss[sum_set_def]
++ MATCH_MP_TAC EXTREAL_SUM_IMAGE_EQ1
++ RW_TAC real_ss[GSPECIFICATION]
>> (DISJ1_TAC
   ++ RW_TAC std_ss[]
   >> (DEP_REWRITE_TAC[prob_biginter_not_negInf_lemma3]
      ++ Q.EXISTS_TAC `t`
       	     ++ RW_TAC std_ss[]
	     ++ PSET_TAC[has_size_def]
	     ++ PAT_ASSUM (Term `∀x'. (∃x''. (x' = x x'') ∧ ((x'' = a) ∨ x'' ∈ t)) ⇒ x' ∈ events p`) MP_TAC
	     ++ DISCH_THEN(MP_TAC o Q.SPEC `(x:('a->bool)->'b->bool) x''`) 
	     ++ RW_TAC std_ss[]
	     ++ `(∃x'''. ((x:('a->bool)->'b->bool) x'' = x x''') ∧ ((x''' = a) ∨ x''' ∈ t))` by (RW_TAC std_ss[]
	        ++ Q.EXISTS_TAC `x''`
   	     	++ RW_TAC std_ss[])
	 	>> (METIS_TAC[])
		++ METIS_TAC[])
++ DEP_REWRITE_TAC[prob_biginter_insert_not_negInf]
++ (Q.EXISTS_TAC `a`
       ++ Q.EXISTS_TAC `t`
       	     ++ RW_TAC std_ss[]
	     >> (PSET_TAC[has_size_def])
	     >> (PSET_TAC[] 
	     	++ PAT_ASSUM (Term `∀x'. (∃x''. (x' = x x'') ∧ ((x'' = a) ∨ x'' ∈ t)) ⇒ x' ∈ events p`) MP_TAC
	     ++ DISCH_THEN(MP_TAC o Q.SPEC `(x:('a->bool)->'b->bool) x''`) 
	     ++ RW_TAC std_ss[]
	     ++ `(∃x'''. ((x:('a->bool)->'b->bool) x'' = x x''') ∧ ((x''' = a) ∨ x''' ∈ t))` by (RW_TAC std_ss[]
	        ++ Q.EXISTS_TAC `x''`
   	     	++ RW_TAC std_ss[])
	 	>> (METIS_TAC[])
		++ METIS_TAC[])
   ++ PSET_TAC[NOT_INSERT_EMPTY]
   ++ Q.EXISTS_TAC `x'` ++ METIS_TAC[]))
++ RW_TAC std_ss[extreal_pow_def]
++ RW_TAC real_ss[REAL_POW_ADD,REAL_NEG_NEG]
++ KNOW_TAC (``FINITE (x':('a->bool)->bool)``)
>> (MATCH_MP_TAC SUBSET_FINITE_I
   ++ EXISTS_TAC(``t:('a->bool)->bool``)
   ++ RW_TAC real_ss[has_size_def]
   ++ FULL_SIMP_TAC std_ss[has_size_def])
++ RW_TAC real_ss[CARD_INSERT]
>> (METIS_TAC[SUBSET_DEF])
++ RW_TAC real_ss[IMAGE_INSERT,pow]);

(*--------------------------PROB_INCLUSION_EXCLUSION_EXTREAL---------------------------------*)
val PROB_INCLUSION_EXCLUSION_EXTREAL = store_thm("PROB_INCLUSION_EXCLUSION_EXTREAL",
  ``!p (s:('a->bool)->bool). 
prob_space p /\ 
FINITE s /\ 
(!a. a IN s ==> a IN events p) ==> 
  ((prob p (BIGUNION s)) =
    sum_set {t | t SUBSET s /\ ~(t = {})}
      (\t. Normal (- &1) pow (CARD t + 1) * (prob p (BIGINTER t))))``,
REPEAT STRIP_TAC
++ MP_TAC(Q.ISPECL [`p:(α -> bool) # ((α -> bool) -> bool) # ((α -> bool) -> extreal)`,`s:('a->bool)->bool`, `\x:'a->bool. x`]
        PROB_INCLUSION_EXCLUSION)
++ ASM_REWRITE_TAC[IMAGE_ID]
++ METIS_TAC[IMAGE_ID]);
(*------------------------------------------------------------*)
(*------------------PROB_INCLUSION_EXCLUSION_EXTREAL_LIST--------------------------------------*)
val PROB_INCLUSION_EXCLUSION_EXTREAL_LIST = store_thm("PROB_INCLUSION_EXCLUSION_EXTREAL_LIST",
  ``!p L. prob_space p  /\ (!x. MEM x (L) ==> x IN events p)
==> ((prob p (BIGUNION (set L))) =
                sum_set {t | t SUBSET (set L) /\ ~(t = {})}
                    (\t. Normal (- &1) pow (CARD t + 1) * (prob p (BIGINTER t))))``,
REPEAT STRIP_TAC
++ MP_TAC(Q.ISPECL [`p:(α -> bool) # ((α -> bool) -> bool) # ((α -> bool) -> extreal)`, `(set L):('a->bool)->bool`]
       PROB_INCLUSION_EXCLUSION_EXTREAL)
++ FULL_SIMP_TAC std_ss[listTheory.FINITE_LIST_TO_SET]
++ RW_TAC list_ss[]);
(*---------------BIGUNION_EQ_UNION_LIST-----------------------------------------*)
val BIGUNION_EQ_UNION_LIST = store_thm("BIGUNION_EQ_UNION_LIST",
  ``!L. BIGUNION (set L) =  union_list L``,
Induct
>> (RW_TAC std_ss[LIST_TO_SET_THM,union_list_def]
   ++ RW_TAC std_ss[BIGUNION_EMPTY])
++ RW_TAC std_ss[LIST_TO_SET_THM,union_list_def]
++ RW_TAC std_ss[BIGUNION_INSERT]);
(*--------------------PROB_INCLUSION_EXCLUSION_PRINCIPLE---------------------------------------------------*)
val PROB_INCLUSION_EXCLUSION_PRINCIPLE = store_thm(
  "PROB_INCLUSION_EXCLUSION_PRINCIPLE",
  ``! p L. prob_space p  /\ (!x. MEM x (L) ==> x IN events p)
==> ((prob p (union_list L)) =
                sum_set {t | t SUBSET (set L) /\ ~(t = {})}
                    (\t. Normal (- &1) pow (CARD t + 1) * (prob p(BIGINTER t))))``,
RW_TAC std_ss[GSYM BIGUNION_EQ_UNION_LIST, PROB_INCLUSION_EXCLUSION_EXTREAL_LIST]);


val PIE_set_alt_form_lem = store_thm("PIE_set_alt_form_lem",
  ``!A B C. {t|t SUBSET {A;B;C} /\ t <> EMPTY} = {{A};{B};{C};{A;B};{A;C};{B;C};{A;B;C}}``,
RW_TAC std_ss[]
THEN SRW_TAC[][EXTENSION,GSPECIFICATION,SUBSET_DEF]
THEN EQ_TAC
THEN1 (METIS_TAC[])
THEN METIS_TAC[]);

val real_sum_image_thm = store_thm("real_sum_image_thm",
  ``!f e s. (REAL_SUM_IMAGE f ∅ = 0) /\
       (FINITE s ⇒ (REAL_SUM_IMAGE f (e INSERT s) = f e + REAL_SUM_IMAGE f (s DELETE e)))``,
METIS_TAC[FORALL_THM,REAL_SUM_IMAGE_THM]);


val PIE_lem2 = store_thm("PIE_lem2",
  ``!A B C. ALL_DISTINCT [A;B;C] ==> 
  (({{B}; {C}; {A; B}; {A; C}; {B; C}; {A; B; C}} DELETE {A}) =
  ({{B}; {C}; {A; B}; {A; C}; {B; C}; {A; B; C}}))``,
 PSET_TAC[ALL_DISTINCT,EXTENSION,GSPECIFICATION,MEM] 
THEN METIS_TAC[]);

val PIE_lem3 = store_thm("PIE_lem3",
  ``!f A B C. ALL_DISTINCT [A;B;C] /\
       	     (∀x.
         x ∈ {{A}; {B}; {C}; {A; B}; {A; C}; {B; C}; {A; B; C}} ⇒
         f x ≠ PosInf) ==>
     (EXTREAL_SUM_IMAGE f {{A};{B};{C};{A;B};{A;C};{B;C};{A;B;C}} =		
      f {A} + EXTREAL_SUM_IMAGE f {{B};{C};{A;B};{A;C};{B;C};{A;B;C}})``,
RW_TAC std_ss[ALL_DISTINCT,MEM]
THEN MP_TAC(Q.ISPECL [`f:('a -> bool)->extreal`, `{({B}:'a->bool);{C};{A;B};{A;C};{B;C};{A;B;C}}`]
      EXTREAL_SUM_IMAGE_PROPERTY_POS)
THEN RW_TAC std_ss[]
THEN `FINITE {{B}; {C}; {A; B}; {A; C}; {B; C}; {A; B; C}}` by (SRW_TAC[][FINITE_SING]) 
THEN FULL_SIMP_TAC std_ss[]
THEN FIRST_X_ASSUM (MP_TAC o Q.SPECL [ `{A}:'a->bool`])
THEN RW_TAC std_ss[]
THEN `({{B}; {C}; {A; B}; {A; C}; {B; C}; {A; B; C}} DELETE {A}) = ({{B}; {C}; {A; B}; {A; C}; {B; C}; {A; B; C}})` by (RW_TAC std_ss[GSYM DELETE_NON_ELEMENT]
THEN SRW_TAC[][EXTENSION,GSPECIFICATION,ALL_DISTINCT,MEM] THEN METIS_TAC[])
THEN FULL_SIMP_TAC std_ss[]);

(*------------PIE_lem4------------------------*)
val PIE_lem4 = store_thm("PIE_lem4",
  ``!f A B C. ALL_DISTINCT [A;B;C] /\
       	     (∀x.
         x ∈ {{A}; {B}; {C}; {A; B}; {A; C}; {B; C}; {A; B; C}} ⇒
         f x ≠ PosInf) ==>
     (EXTREAL_SUM_IMAGE f {{A};{B};{C};{A;B};{A;C};{B;C};{A;B;C}} =		
      f {A} + f {B} + f {C} + f {A;B} + f {A;C} + f {B;C} + f {A;B;C})``,
RW_TAC std_ss[ALL_DISTINCT,MEM]
THEN MP_TAC(Q.ISPECL [`f:('a->bool)->extreal`,`{{B}:'a->bool; {C}; {A; B}; {A; C}; {B; C}; {A; B; C}}`]
      EXTREAL_SUM_IMAGE_PROPERTY_POS)
THEN FULL_SIMP_TAC std_ss[prove(``!A B C. FINITE {{B}; {C}; {A; B}; {A; C}; {B; C}; {A; B; C}}``, SRW_TAC[][FINITE_SING])]
THEN DISCH_THEN (MP_TAC o Q.SPECL [`{A}:'a->bool`])
THEN FULL_SIMP_TAC std_ss[]
THEN RW_TAC std_ss[prove(``!A B C. A <> B /\ A <> C /\ B <> C ==> (({{B}; {C}; {A; B}; {A; C}; {B; C}; {A; B; C}} DELETE {A}) = ({{B}; {C}; {A; B}; {A; C}; {B; C}; {A; B; C}}))``, SRW_TAC[][EXTENSION,GSPECIFICATION,ALL_DISTINCT,MEM] THEN METIS_TAC[])]
(*---------solving for {B}---*)
THEN MP_TAC(Q.ISPECL [`f:('a->bool)->extreal`,`{{C}:'a->bool; {A; B}; {A; C}; {B; C}; {A; B; C}}`]
      EXTREAL_SUM_IMAGE_PROPERTY_POS)
THEN FULL_SIMP_TAC std_ss[prove(``!A B C. FINITE {{C}; {A; B}; {A; C}; {B; C}; {A; B; C}}``, SRW_TAC[][FINITE_SING])]
THEN DISCH_THEN (MP_TAC o Q.SPECL [`{B}:'a->bool`])
THEN FULL_SIMP_TAC std_ss[]
THEN RW_TAC std_ss[prove(``!A B C. A <> B /\ A <> C /\ B <> C ==> (({{C}; {A; B}; {A; C}; {B; C}; {A; B; C}} DELETE {B}) = ({{C}; {A; B}; {A; C}; {B; C}; {A; B; C}}))``, SRW_TAC[][EXTENSION,GSPECIFICATION,ALL_DISTINCT,MEM] THEN METIS_TAC[])]
THEN POP_ASSUM MP_TAC
THEN `(∀x.
         x ∈ {{B}; {C}; {A; B}; {A; C}; {B; C}; {A; B; C}} ⇒
         f x ≠ PosInf)` by 
      (MATCH_MP_TAC (prove(``!A B C f. (∀x.
             x ∈ {{A}; {B}; {C:'a}; {A; B}; {A; C}; {B; C}; {A; B; C}} ⇒
             f x ≠ PosInf) ==> (∀x.
         x ∈ {{B}; {C}; {A; B}; {A:'a; C}; {B; C}; {A; B; C}} ⇒
         f x ≠ PosInf)``, SRW_TAC[][EXTENSION,GSPECIFICATION]++ METIS_TAC[]))
      THEN RW_TAC std_ss[])
THEN FULL_SIMP_TAC std_ss[]
THEN WEAKEN_TAC (equal (Term `∀x.
        x ∈ {{B:'a}; {C}; {A; B}; {A; C}; {B; C}; {A; B; C}} ⇒ f x ≠ PosInf`))
(*---------solving for {C}---*)
THEN MP_TAC(Q.ISPECL [`f:('a->bool)->extreal`,`{{A; B}; {A; C}; {B; C}; {A; B; C}:'a->bool}`]
      EXTREAL_SUM_IMAGE_PROPERTY_POS)
THEN FULL_SIMP_TAC std_ss[prove(``!A B C. FINITE {{A; B}; {A; C}; {B; C}; {A; B; C}}``, SRW_TAC[][FINITE_SING])]
THEN DISCH_THEN (MP_TAC o Q.SPECL [`{C}:'a->bool`])
THEN FULL_SIMP_TAC std_ss[]
THEN `(∀x.
         x ∈ {{C};{A; B}; {A; C}; {B; C}; {A; B; C}} ⇒
         f x ≠ PosInf)` by 
(MATCH_MP_TAC (prove(``!A B C f. (∀x.
             x ∈ {{A}; {B}; {C:'a}; {A; B}; {A; C}; {B; C}; {A; B; C}} ⇒
             f x ≠ PosInf) ==> (∀x.
         x ∈ {{C};{A; B}; {A:'a; C}; {B; C}; {A; B; C}} ⇒
         f x ≠ PosInf)``, SRW_TAC[][EXTENSION,GSPECIFICATION]++ METIS_TAC[]))
      THEN RW_TAC std_ss[])
THEN FULL_SIMP_TAC std_ss[]
THEN FULL_SIMP_TAC std_ss[prove(``!A B C. A <> B /\ A <> C /\ B <> C ==> (({{A; B}; {A; C}; {B; C}; {A; B; C}} DELETE {C}) = ({{A; B}; {A; C}; {B; C}; {A; B; C}}))``, SRW_TAC[][EXTENSION,GSPECIFICATION,ALL_DISTINCT,MEM] THEN METIS_TAC[])]
THEN REPEAT (WEAKEN_TAC is_eq)
THEN WEAKEN_TAC (equal (Term `∀x.
        x ∈ {{C}; {A; B}; {A; C}; {B; C}; {A; B; C}} ⇒ f x ≠ PosInf`))
(*---------solving for {A;B}---------*)
THEN MP_TAC(Q.ISPECL [`f:('a->bool)->extreal`,`{{A; C}; {B; C}; {A; B; C}:'a->bool}`]
      EXTREAL_SUM_IMAGE_PROPERTY_POS)
THEN FULL_SIMP_TAC std_ss[prove(``!A B C. FINITE {{A; C}; {B; C}; {A; B; C}}``, SRW_TAC[][FINITE_SING])]
THEN DISCH_THEN (MP_TAC o Q.SPECL [`{A;B}:'a->bool`])
THEN FULL_SIMP_TAC std_ss[]
THEN `(∀x.
         x ∈ {{A; B}; {A; C}; {B; C}; {A; B; C}} ⇒
         f x ≠ PosInf)` by 
 (MATCH_MP_TAC (prove(``!A B C f. (∀x.
             x ∈ {{A}; {B}; {C:'a}; {A; B}; {A; C}; {B; C}; {A; B; C}} ⇒
             f x ≠ PosInf) ==> (∀x.
         x ∈ {{A; B}; {A:'a; C}; {B; C}; {A; B; C}} ⇒
         f x ≠ PosInf)``, SRW_TAC[][EXTENSION,GSPECIFICATION]++ METIS_TAC[]))
      THEN RW_TAC std_ss[])
THEN FULL_SIMP_TAC std_ss[]
THEN FULL_SIMP_TAC std_ss[prove(``!A B C. A <> B /\ A <> C /\ B <> C ==> (({{A; C}; {B; C}; {A; B; C}} DELETE {A;B}) = ({{A; C}; {B; C}; {A; B; C}}))``, SRW_TAC[][EXTENSION,GSPECIFICATION,ALL_DISTINCT,MEM] THEN METIS_TAC[])]
THEN REPEAT (WEAKEN_TAC is_eq)
THEN WEAKEN_TAC (equal (Term `∀x.
        x ∈ {{A; B}; {A; C}; {B; C}; {A; B; C}} ⇒ f x ≠ PosInf`))
(*---------solving for {A;C}---------*)
THEN MP_TAC(Q.ISPECL [`f:('a->bool)->extreal`,`{{B; C}; {A; B; C}:'a->bool}`]
      EXTREAL_SUM_IMAGE_PROPERTY_POS)
THEN FULL_SIMP_TAC std_ss[prove(``!A B C. FINITE {{B; C}; {A; B; C}}``, SRW_TAC[][FINITE_SING])]
THEN DISCH_THEN (MP_TAC o Q.SPECL [`{A;C}:'a->bool`])
THEN FULL_SIMP_TAC std_ss[]
THEN `(∀x.
         x ∈ {{A; C}; {B; C}; {A; B; C}} ⇒
         f x ≠ PosInf)` by 
(MATCH_MP_TAC (prove(``!A B C f. (∀x.
             x ∈ {{A}; {B}; {C:'a}; {A; B}; {A; C}; {B; C}; {A; B; C}} ⇒
             f x ≠ PosInf) ==> (∀x.
         x ∈ {{A:'a; C}; {B; C}; {A; B; C}} ⇒
         f x ≠ PosInf)``, SRW_TAC[][EXTENSION,GSPECIFICATION]++ METIS_TAC[]))
      THEN RW_TAC std_ss[])
THEN FULL_SIMP_TAC std_ss[]
THEN FULL_SIMP_TAC std_ss[prove(``!A B C. A <> B /\ A <> C /\ B <> C ==> (({{B; C}; {A; B; C}} DELETE {A;C}) = ({{B; C}; {A; B; C}}))``, SRW_TAC[][EXTENSION,GSPECIFICATION,ALL_DISTINCT,MEM] THEN METIS_TAC[])]
THEN RW_TAC std_ss[]
THEN REPEAT (WEAKEN_TAC is_eq)
THEN WEAKEN_TAC (equal (Term `∀x.
        x ∈ {{A; C}; {B; C}; {A; B; C}} ⇒ f x ≠ PosInf`))
(*---------solving for {B;C}---------*)
THEN MP_TAC(Q.ISPECL [`f:('a->bool)->extreal`,`{{A; B; C}:'a->bool}`]
      EXTREAL_SUM_IMAGE_PROPERTY_POS)
THEN FULL_SIMP_TAC std_ss[prove(``!A B C. FINITE {{A; B; C}}``, SRW_TAC[][FINITE_SING])]
THEN DISCH_THEN (MP_TAC o Q.SPECL [`{B;C}:'a->bool`])
THEN FULL_SIMP_TAC std_ss[]
THEN `(∀x.
         x ∈ {{B; C}; {A; B; C}} ⇒
         f x ≠ PosInf)` by 
(MATCH_MP_TAC (prove(``!A B C f. (∀x.
             x ∈ {{A}; {B}; {C:'a}; {A; B}; {A; C}; {B; C}; {A; B; C}} ⇒
             f x ≠ PosInf) ==> (∀x.
         x ∈ {{B; C}; {A; B; C}} ⇒
         f x ≠ PosInf)``, SRW_TAC[][EXTENSION,GSPECIFICATION]++ METIS_TAC[]))
      THEN RW_TAC std_ss[])
THEN FULL_SIMP_TAC std_ss[]
THEN FULL_SIMP_TAC std_ss[prove(``!A B C. A <> B /\ A <> C /\ B <> C ==> (({{A; B; C}} DELETE {B;C}) = ({{A; B; C}}))``, SRW_TAC[][EXTENSION,GSPECIFICATION,ALL_DISTINCT,MEM] THEN METIS_TAC[])]
THEN RW_TAC std_ss[]
THEN REPEAT (WEAKEN_TAC is_eq)
THEN WEAKEN_TAC (equal (Term `∀x.
        x ∈ {{B; C}; {A; B; C}} ⇒ f x ≠ PosInf`))
(*---------solving for {A;B;C}---------*)
THEN RW_TAC std_ss[EXTREAL_SUM_IMAGE_SING]
THEN PSET_TAC[] THEN DEP_REWRITE_TAC[add_assoc,extreal_hvgTheory.add_not_infty]
THEN METIS_TAC[add_assoc,extreal_hvgTheory.add_not_infty]); 

val _ = export_theory();
