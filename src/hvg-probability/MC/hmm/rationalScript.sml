(* ================================================================= *)
(*   Rational Numbers as a subset of extended real numbers           *)
(*   -----------------------------------------------------           *)
(*   This theory is need for the proofs of measurability properties  *)
(*   Author: Tarek Mhamdi, HVG Concordia                             *)
(* ================================================================= *)

(* Interactive Mode

   app load ["realTheory", "realLib", "pred_setTheory", "extra_pred_setTheory",
             "pairTheory", "arithmeticTheory", "combinTheory", "extrealTheory"]; 
   quietdec := true;

*)

open HolKernel Parse boolLib bossLib realTheory realLib pred_setTheory extra_pred_setTheory pairTheory arithmeticTheory combinTheory extrealTheory;

(* interactive mode
   quietdec := false;
*)

val _ = new_theory "rational";

infixr 0 ++ << || THENC ORELSEC ORELSER ##;
infix 1 >>;

val op ++ = op THEN;
val op << = op THENL;
val op >> = op THEN1;
val op || = op ORELSE;
val REVERSE = Tactical.REVERSE;

val Simplify = RW_TAC arith_ss;
fun parse_with_goal t (asms, g) =
  let
    val ctxt = free_varsl (g::asms)
  in
    Parse.parse_in_context ctxt t
  end;
val PARSE_TAC = fn tac => fn q => W (tac o parse_with_goal q);
val Suff = PARSE_TAC SUFF_TAC;
val Know = PARSE_TAC KNOW_TAC;

val POP_ORW = POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm]);

val Q_set_def = Define `Q_set = {x| ?a b. (x = (&a/(&b))) /\ (0 < &b)} UNION {x | ?a b. (x = -(&a/(&b))) /\ (0 < &b)}`;


val Q_not_infty = store_thm
  ("Q_not_infty",``!x. x IN Q_set ==> ?y. x = Normal y``,
  RW_TAC std_ss [Q_set_def,GSPECIFICATION,IN_UNION]
  ++ `&b <> 0:real` by METIS_TAC [extreal_of_num_def,extreal_lt_eq,REAL_LT_IMP_NE]
  ++ RW_TAC std_ss [extreal_of_num_def,extreal_div_eq,extreal_ainv_def]);

val NUM_2D_BIJ_NZ = store_thm
  ("NUM_2D_BIJ_NZ",
   ``?f.
       BIJ f ((UNIV : num -> bool) CROSS ((UNIV : num -> bool) DIFF {0}))
       (UNIV : num -> bool)``,
   MATCH_MP_TAC BIJ_INJ_SURJ
   ++ REVERSE CONJ_TAC
   >> (Q.EXISTS_TAC `FST`
       ++ RW_TAC std_ss [SURJ_DEF, IN_UNIV, IN_CROSS,DIFF_DEF,GSPECIFICATION,IN_UNIV,IN_SING]
       ++ Q.EXISTS_TAC `(x, 1)`
       ++ RW_TAC std_ss [FST]
      )             
   ++ Q.EXISTS_TAC `UNCURRY ind_type$NUMPAIR`
   ++ RW_TAC std_ss [INJ_DEF, IN_UNIV, IN_CROSS]
   ++ Cases_on `x`
   ++ Cases_on `y`
   ++ POP_ASSUM MP_TAC
   ++ RW_TAC std_ss [UNCURRY_DEF, ind_typeTheory.NUMPAIR_INJ]);

val NUM_2D_BIJ_NZ_INV = store_thm
  ("NUM_2D_BIJ_NZ_INV",
   ``?f.
       BIJ f (UNIV : num -> bool)
       ((UNIV : num -> bool) CROSS ((UNIV : num -> bool) DIFF {0}))``,
   PROVE_TAC [NUM_2D_BIJ_NZ, BIJ_SYM]);

val NUM_2D_BIJ_NZ_ALT = store_thm
  ("NUM_2D_BIJ_NZ_ALT",
   ``?f.
       BIJ f ((UNIV : num -> bool) CROSS (UNIV : num -> bool))
       ((UNIV : num -> bool) DIFF {0})``,
   MATCH_MP_TAC BIJ_INJ_SURJ
   ++ REVERSE CONJ_TAC
   >> (Q.EXISTS_TAC `(\(x,y). x + 1:num)`
       ++ RW_TAC std_ss [SURJ_DEF, IN_UNIV, IN_CROSS]
       		>> (Cases_on `x` ++ RW_TAC std_ss [DIFF_DEF,GSPECIFICATION,IN_UNIV,IN_SING])
       ++ Q.EXISTS_TAC `(x-1,1)`
       ++ RW_TAC std_ss []
       ++ MATCH_MP_TAC SUB_ADD
       ++ FULL_SIMP_TAC real_ss [DIFF_DEF,GSPECIFICATION,IN_UNIV,IN_SING]
       )
   ++ Q.EXISTS_TAC `UNCURRY ind_type$NUMPAIR`
   ++ RW_TAC std_ss [INJ_DEF, IN_UNIV, IN_CROSS]
   >> ( Cases_on `x`
        ++ RW_TAC std_ss [UNCURRY_DEF, ind_typeTheory.NUMPAIR_INJ,DIFF_DEF,GSPECIFICATION,IN_UNIV,IN_SING]
        ++ RW_TAC real_ss [ind_typeTheory.NUMPAIR]
      )  
   ++ Cases_on `x`
   ++ Cases_on `y`
   ++ POP_ASSUM MP_TAC
   ++ RW_TAC std_ss [UNCURRY_DEF, ind_typeTheory.NUMPAIR_INJ]);

val NUM_2D_BIJ_NZ_ALT_INV = store_thm
  ("NUM_2D_BIJ_NZ_ALT_INV",
   ``?f.
       BIJ f ((UNIV : num -> bool) DIFF {0})
       ((UNIV : num -> bool) CROSS (UNIV : num -> bool))``,
   PROVE_TAC [NUM_2D_BIJ_NZ_ALT, BIJ_SYM]);

val NUM_2D_BIJ_NZ_ALT2 = store_thm
  ("NUM_2D_BIJ_NZ_ALT2",
   ``?f.
       BIJ f (((UNIV : num -> bool) DIFF {0}) CROSS ((UNIV : num -> bool) DIFF {0}))
       (UNIV : num -> bool)``,
   MATCH_MP_TAC BIJ_INJ_SURJ
   ++ REVERSE CONJ_TAC
   >> (Q.EXISTS_TAC `(\(x,y). x - 1:num)`
       ++ RW_TAC std_ss [SURJ_DEF, IN_UNIV, IN_CROSS]
       ++ Q.EXISTS_TAC `(x+1,1)`
       ++ RW_TAC std_ss [DIFF_DEF,GSPECIFICATION,IN_UNIV,IN_SING]       
       )
   ++ Q.EXISTS_TAC `UNCURRY ind_type$NUMPAIR`
   ++ RW_TAC std_ss [INJ_DEF, IN_UNIV, IN_CROSS]
   ++ Cases_on `x`
   ++ Cases_on `y`
   ++ POP_ASSUM MP_TAC
   ++ RW_TAC std_ss [UNCURRY_DEF, ind_typeTheory.NUMPAIR_INJ]);

val NUM_2D_BIJ_NZ_ALT2_INV = store_thm
  ("NUM_2D_BIJ_NZ_ALT2_INV",
   ``?f.
       BIJ f (UNIV : num -> bool)
       (((UNIV : num -> bool) DIFF {0}) CROSS ((UNIV : num -> bool) DIFF {0}))``,
   PROVE_TAC [NUM_2D_BIJ_NZ_ALT2, BIJ_SYM]);

val Q_COUNTABLE = store_thm
  ("Q_COUNTABLE", ``countable Q_set``,
  RW_TAC std_ss [Q_set_def]
  ++ MATCH_MP_TAC COUNTABLE_UNION
  ++ CONJ_TAC 
  >> (RW_TAC std_ss [countable_def]
      ++ MP_TAC NUM_2D_BIJ_NZ_INV
      ++ RW_TAC std_ss []
      ++ Q.EXISTS_TAC `(\(a,b). &a/(&b)) o f`
      ++ RW_TAC std_ss [GSPECIFICATION]
      ++ FULL_SIMP_TAC std_ss [BIJ_DEF,INJ_DEF,SURJ_DEF,IN_UNIV]
      ++ PAT_ASSUM ``!x. x IN P ==> Q x y`` (MP_TAC o Q.SPEC `(&a,&b)`)
      ++ RW_TAC std_ss []
      ++ FULL_SIMP_TAC real_ss [IN_CROSS,IN_UNIV,IN_SING,DIFF_DEF,
       			        GSPECIFICATION,GSYM REAL_LT_NZ]
      ++ `?y. f y = (a,b)` by METIS_TAC [lt_imp_ne,extreal_of_num_def,extreal_lt_eq]
      ++ Q.EXISTS_TAC `y`
      ++ RW_TAC real_ss [])
  ++ RW_TAC std_ss [countable_def]
  ++ MP_TAC NUM_2D_BIJ_NZ_INV
  ++ RW_TAC std_ss []
  ++ Q.EXISTS_TAC `(\(a,b). -(&a/(&b))) o f`
  ++ RW_TAC std_ss [GSPECIFICATION]
  ++ FULL_SIMP_TAC std_ss [BIJ_DEF,INJ_DEF,SURJ_DEF,IN_UNIV]
  ++ PAT_ASSUM ``!x. x IN P ==> Q x y`` (MP_TAC o Q.SPEC `(&a,&b)`)
  ++ RW_TAC std_ss []
  ++ FULL_SIMP_TAC real_ss [IN_CROSS,IN_UNIV,IN_SING,
	  		    DIFF_DEF,GSPECIFICATION,GSYM REAL_LT_NZ]
  ++ `?y. f y = (a,b)` by METIS_TAC [lt_imp_ne,extreal_of_num_def,extreal_lt_eq]
  ++ Q.EXISTS_TAC `y`
  ++ RW_TAC real_ss []);

val NUM_IN_Q = store_thm 
  ("NUM_IN_Q", ``!n:num. (&n IN Q_set) /\ (-&n IN Q_set)``,
  RW_TAC std_ss [Q_set_def,GSPECIFICATION,IN_UNION]
  >> (DISJ1_TAC
      ++ Q.EXISTS_TAC `n` ++ Q.EXISTS_TAC `1`
      ++ RW_TAC std_ss [div_one,lt_01])
  ++ DISJ2_TAC
  ++ Q.EXISTS_TAC `n` ++ Q.EXISTS_TAC `1`
  ++ RW_TAC std_ss [div_one,lt_01]);
   
val Q_INFINITE = store_thm
  ("Q_INFINITE", ``~(FINITE Q_set)``,
  `{x | ?n:num. x = (&n)} SUBSET Q_set` 
     by (RW_TAC std_ss [SUBSET_DEF,EXTENSION,GSPECIFICATION] 
         ++ METIS_TAC [NUM_IN_Q])
  ++ Suff `~(FINITE {x | ?n:num. x = (&n)})` 
  >> METIS_TAC [INFINITE_SUBSET,INFINITE_DEF]
  ++ RW_TAC std_ss [GSYM INFINITE_DEF]
  ++ MATCH_MP_TAC (INST_TYPE [alpha |-> ``:num``] INFINITE_INJ)
  ++ Q.EXISTS_TAC `(\n. &n)`
  ++ Q.EXISTS_TAC `UNIV`
  ++ RW_TAC real_ss [NOT_FINITE_NUM, INJ_DEF,INFINITE_DEF,GSPECIFICATION]
  >> METIS_TAC []
  ++ FULL_SIMP_TAC real_ss [extreal_11,extreal_of_num_def]);

val OPP_IN_Q = store_thm
  ("OPP_IN_Q", ``!x. x IN Q_set ==> -x IN Q_set``,
  RW_TAC std_ss [Q_set_def,EXTENSION,GSPECIFICATION,IN_UNION]
  >> (DISJ2_TAC
      ++ Q.EXISTS_TAC `a` ++ Q.EXISTS_TAC `b`
      ++ RW_TAC real_ss [])
  ++ DISJ1_TAC
  ++ Q.EXISTS_TAC `a` ++ Q.EXISTS_TAC `b`
  ++ RW_TAC real_ss [neg_neg]);

val INV_IN_Q = store_thm
  ("INV_IN_Q", ``!x. (x IN Q_set) /\ (x <> 0) ==> 1/x IN Q_set``,
  RW_TAC std_ss [Q_set_def,EXTENSION,GSPECIFICATION,IN_UNION,extreal_of_num_def]
  >> (Cases_on `0:real < &a`
      >> (DISJ1_TAC
          ++ `(&a <> 0:real) /\ (&b <> 0:real)` by FULL_SIMP_TAC real_ss [REAL_POS_NZ,GSYM REAL_LT_NZ,extreal_lt_eq]
          ++ `&a / &b <> 0:real` by FULL_SIMP_TAC real_ss [extreal_div_eq,extreal_11]
          ++ Q.EXISTS_TAC `b` ++ Q.EXISTS_TAC `a`
   	  ++ FULL_SIMP_TAC std_ss [extreal_div_eq,extreal_11]
	  ++ `1:real / (&a / &b) = (1 / 1) / (&a / &b)` by RW_TAC real_ss []
  	  ++ ASM_SIMP_TAC std_ss []
  	  ++ RW_TAC real_ss [div_rat,extreal_lt_eq])
     ++ DISJ2_TAC
     ++ `&b <> 0:real` by METIS_TAC [extreal_lt_eq,REAL_LT_IMP_NE]
     ++ FULL_SIMP_TAC std_ss [extreal_div_eq,extreal_lt_eq,extreal_11]
     ++ `&a <> 0:real` by METIS_TAC [real_div,REAL_ENTIRE]
     ++ FULL_SIMP_TAC real_ss [])
  ++ Cases_on `0:real < &a`
  >> (DISJ2_TAC
      ++ `(&a <> 0:real) /\ (&b <> 0:real)` by FULL_SIMP_TAC real_ss [REAL_POS_NZ,GSYM REAL_LT_NZ,extreal_lt_eq]
      ++ `&a / &b <> 0:real` by FULL_SIMP_TAC real_ss [extreal_div_eq,extreal_11,extreal_ainv_def,REAL_NEG_EQ0]
      ++ Q.EXISTS_TAC `b` ++ Q.EXISTS_TAC `a`
      ++ FULL_SIMP_TAC std_ss [extreal_div_eq,extreal_11,extreal_ainv_def]
      ++ RW_TAC std_ss [extreal_lt_eq,extreal_ainv_def,extreal_div_eq,real_div,REAL_INV_MUL]
      ++ `inv (&b) <> 0:real` by FULL_SIMP_TAC real_ss [REAL_POS_NZ,REAL_INV_EQ_0,REAL_POS_NZ]
      ++ RW_TAC real_ss [GSYM REAL_NEG_INV,REAL_NEG_EQ0,REAL_EQ_NEG,REAL_ENTIRE]
      ++ RW_TAC real_ss [REAL_INV_MUL,REAL_INV_INV,REAL_MUL_COMM]) 	          
  ++ DISJ2_TAC
  ++ `&b <> 0:real` by METIS_TAC [extreal_lt_eq,REAL_LT_IMP_NE]
  ++ FULL_SIMP_TAC std_ss [extreal_div_eq,extreal_lt_eq,extreal_11,extreal_ainv_def]
  ++ `&a <> 0:real` by METIS_TAC [real_div,REAL_ENTIRE,REAL_NEG_EQ0]
  ++ FULL_SIMP_TAC real_ss []);

val CMUL_IN_Q = store_thm
  ("CMUL_IN_Q", ``!z:num x. x IN Q_set ==> (&z * x IN Q_set) /\ (-&z * x IN Q_set)``,
  RW_TAC std_ss [Q_set_def,EXTENSION,GSPECIFICATION,IN_UNION,extreal_of_num_def] <<
  [DISJ1_TAC
   ++ Q.EXISTS_TAC `z*a` ++ Q.EXISTS_TAC `b`
   ++  `&b <> 0:real` by METIS_TAC [extreal_lt_eq,REAL_LT_IMP_NE]
   ++ RW_TAC real_ss [extreal_mul_def,extreal_div_eq,real_div,REAL_MUL_ASSOC],
   DISJ2_TAC
   ++ Q.EXISTS_TAC `z*a` ++ Q.EXISTS_TAC `b`
   ++  `&b <> 0:real` by METIS_TAC [extreal_lt_eq,REAL_LT_IMP_NE]
   ++ RW_TAC real_ss [extreal_ainv_def,extreal_mul_def,extreal_div_eq,real_div,REAL_MUL_ASSOC],
   DISJ2_TAC
   ++ Q.EXISTS_TAC `z*a` ++ Q.EXISTS_TAC `b`
   ++  `&b <> 0:real` by METIS_TAC [extreal_lt_eq,REAL_LT_IMP_NE]
   ++ RW_TAC real_ss [extreal_ainv_def,extreal_mul_def,extreal_div_eq,real_div,REAL_MUL_ASSOC],
   DISJ1_TAC
   ++ Q.EXISTS_TAC `z*a` ++ Q.EXISTS_TAC `b`
   ++  `&b <> 0:real` by METIS_TAC [extreal_lt_eq,REAL_LT_IMP_NE]
   ++ RW_TAC real_ss [extreal_ainv_def,extreal_mul_def,extreal_div_eq,real_div,REAL_MUL_ASSOC]]);

val ADD_IN_Q = store_thm
  ("ADD_IN_Q", ``!x y. (x IN Q_set) /\ (y IN Q_set) ==> (x+y IN Q_set)``,
  RW_TAC std_ss [Q_set_def,EXTENSION,GSPECIFICATION,IN_UNION,extreal_of_num_def] <<
  [DISJ1_TAC
   ++ `&b <> 0:real /\ &b' <> 0:real` by FULL_SIMP_TAC real_ss [extreal_lt_eq,REAL_LT_IMP_NE]
   ++ `0:real < &(b * b')` by METIS_TAC [extreal_lt_eq,REAL_LT_MUL,mult_ints]
   ++ `&(b * b') <> 0:real` by RW_TAC std_ss [REAL_LT_IMP_NE]
   ++ Q.EXISTS_TAC `(a*b' + a'*b)`
   ++ Q.EXISTS_TAC `b*b'`
   ++ RW_TAC std_ss [extreal_div_eq,extreal_add_def,extreal_11,extreal_lt_eq]
   ++ RW_TAC real_ss [REAL_ADD_RAT,REAL_MUL_COMM,REAL_LT_MUL],
  	     
   `&b <> 0:real /\ &b' <> 0:real` by FULL_SIMP_TAC real_ss [extreal_lt_eq,REAL_LT_IMP_NE]
   ++ Cases_on `&a*(&b')-(&a'* (&b)) = 0:real`
   >> (DISJ1_TAC
       ++ Q.EXISTS_TAC `0`
       ++ Q.EXISTS_TAC `1`
       ++ RW_TAC real_ss [extreal_lt_eq,extreal_div_eq,REAL_DIV_LZERO,extreal_11,extreal_ainv_def,extreal_add_def,GSYM real_sub]
       ++ RW_TAC std_ss [REAL_SUB_RAT,REAL_DIV_LZERO,REAL_MUL_COMM])
   ++ Cases_on `0:real < &a * (&b') - (&a' * (&b))`
   >> (DISJ1_TAC
       ++ Q.EXISTS_TAC `(a * b' - a' * b)`
       ++ Q.EXISTS_TAC `b * b'`
       ++ `0:real < &(b * b')` by METIS_TAC [extreal_lt_eq,REAL_LT_MUL,mult_ints]
       ++ `&(b * b') <> 0:real` by RW_TAC std_ss [REAL_LT_IMP_NE]
       ++ RW_TAC std_ss [extreal_div_eq,extreal_ainv_def,extreal_add_def,extreal_lt_eq]
       ++ RW_TAC std_ss [REAL_SUB_RAT,REAL_MUL_COMM,REAL_LT_MUL,GSYM real_sub,GSYM mult_ints]
       ++ `&a' * &b < &a * (&b'):real` by FULL_SIMP_TAC real_ss [REAL_SUB_LT]
       ++ `a' * b < a * b'` by FULL_SIMP_TAC real_ss []
       ++ `a' * b <> a * b'` by FULL_SIMP_TAC real_ss []
       ++ FULL_SIMP_TAC real_ss [REAL_SUB])  
   ++ DISJ2_TAC
   ++ Q.EXISTS_TAC `(a' * b - a * b')`
   ++ Q.EXISTS_TAC `b * b'`
   ++  `0:real < &(b * b')` by METIS_TAC [extreal_lt_eq,REAL_LT_MUL,mult_ints]
   ++ `&(b * b') <> 0:real` by RW_TAC std_ss [REAL_LT_IMP_NE]
   ++ RW_TAC std_ss [extreal_div_eq,extreal_ainv_def,extreal_add_def,extreal_lt_eq]
   ++ `&a * &b' - &a' * &b < 0:real` by (FULL_SIMP_TAC real_ss [GSYM real_lte,REAL_LE_LT] ++ FULL_SIMP_TAC real_ss [])
   ++ `&a * &b' < &a' * (&b):real` by FULL_SIMP_TAC real_ss [REAL_LT_SUB_RADD]  	     
   ++ `a' * b <> a * b'` by FULL_SIMP_TAC real_ss []
   ++ RW_TAC std_ss [REAL_SUB_RAT,REAL_MUL_COMM,REAL_LT_MUL,GSYM real_sub]
   ++ RW_TAC std_ss [GSYM mult_ints]
   ++ FULL_SIMP_TAC real_ss [REAL_NEG_SUB,REAL_SUB,neg_rat],
  	     	  
   `&b <> 0:real /\ &b' <> 0:real` by FULL_SIMP_TAC real_ss [extreal_lt_eq,REAL_LT_IMP_NE]
   ++ `0:real < &(b * b')` by METIS_TAC [extreal_lt_eq,REAL_LT_MUL,mult_ints]
   ++ `&(b * b') <> 0:real` by RW_TAC std_ss [REAL_LT_IMP_NE]
   ++ Cases_on `&a * (&b')-(&a' * (&b)) = 0:real`
   >> (DISJ1_TAC
       ++ Q.EXISTS_TAC `0`
       ++ Q.EXISTS_TAC `1`
       ++ RW_TAC real_ss [extreal_lt_eq,extreal_div_eq,REAL_DIV_LZERO,extreal_11,extreal_ainv_def,extreal_add_def]
       ++ ONCE_REWRITE_TAC [GSYM REAL_NEG_EQ0]
       ++ RW_TAC std_ss [REAL_NEG_ADD,REAL_NEG_NEG]
       ++ RW_TAC std_ss [REAL_SUB_RAT,REAL_MUL_COMM,REAL_LT_MUL,GSYM real_sub,REAL_DIV_LZERO,REAL_SUB_0])
   ++ Cases_on `0:real < &a * (&b') - (&a' * (&b))`
   >> (DISJ2_TAC
       ++ Q.EXISTS_TAC `(a * b' - a' * b)`
       ++ Q.EXISTS_TAC `b * b'`
       ++ RW_TAC real_ss [extreal_lt_eq,extreal_div_eq,REAL_DIV_LZERO,extreal_11,extreal_ainv_def,extreal_add_def]
       ++ RW_TAC std_ss [REAL_ADD_COMM,GSYM real_sub]
       ++ RW_TAC std_ss [REAL_SUB_RAT,REAL_MUL_COMM,REAL_LT_MUL,GSYM real_sub,GSYM mult_ints]
       ++ `&a' * &b < &a * (&b'):real` by FULL_SIMP_TAC real_ss [REAL_SUB_LT]
       ++ `a' * b < a * b'` by FULL_SIMP_TAC real_ss []
       ++ `a' * b <> a * b'` by FULL_SIMP_TAC real_ss []
       ++ FULL_SIMP_TAC real_ss [REAL_SUB,neg_rat])  
   ++ DISJ1_TAC
   ++ Q.EXISTS_TAC `(a' * b - a * b')`
   ++ Q.EXISTS_TAC `b * b'`
   ++ RW_TAC std_ss [REAL_ADD_COMM,GSYM real_sub,extreal_lt_eq]
   ++ `&a * &b' - &a' * &b < 0:real` by (FULL_SIMP_TAC real_ss [GSYM real_lte,REAL_LE_LT] ++ FULL_SIMP_TAC real_ss [])
   ++ `&a * &b' < &a' * (&b):real` by FULL_SIMP_TAC real_ss [REAL_LT_SUB_RADD]  	     
   ++ `a' * b <> a * b'` by FULL_SIMP_TAC real_ss []
   ++ RW_TAC std_ss [extreal_div_eq,extreal_ainv_def,extreal_add_def,extreal_11]
   ++ RW_TAC std_ss [REAL_ADD_COMM,GSYM real_sub,REAL_SUB_RAT,REAL_MUL_COMM,REAL_LT_MUL,GSYM mult_ints]
   ++ FULL_SIMP_TAC real_ss [REAL_NEG_SUB,REAL_SUB,neg_rat],
   DISJ2_TAC
   ++ `&b <> 0:real /\ &b' <> 0:real` by FULL_SIMP_TAC real_ss [extreal_lt_eq,REAL_LT_IMP_NE]
   ++ `0:real < &(b * b')` by METIS_TAC [extreal_lt_eq,REAL_LT_MUL,mult_ints]
   ++ `&(b * b') <> 0:real` by RW_TAC std_ss [REAL_LT_IMP_NE]
   ++ Q.EXISTS_TAC `(a * b' + a' * b)`
   ++ Q.EXISTS_TAC `b*b'`
   ++ RW_TAC std_ss [extreal_div_eq,extreal_ainv_def,extreal_add_def,extreal_11,extreal_lt_eq]
   ++ REWRITE_TAC [GSYM mult_ints,GSYM add_ints]
   ++ RW_TAC std_ss [REAL_SUB_LNEG,GSYM real_sub,REAL_EQ_NEG]
   ++ RW_TAC std_ss [REAL_ADD_RAT,REAL_MUL_COMM,REAL_LT_MUL]]);
  
val SUB_IN_Q = store_thm
  ("SUB_IN_Q", ``!x y. (x IN Q_set) /\ (y IN Q_set) ==> (x - y IN Q_set)``,	
  RW_TAC std_ss []
  ++ `?x1. x = Normal x1` by METIS_TAC [Q_not_infty]
  ++ `?y1. y = Normal y1` by METIS_TAC [Q_not_infty]
  ++ RW_TAC std_ss [extreal_sub_def]
  ++ METIS_TAC [OPP_IN_Q,ADD_IN_Q,extreal_add_def,extreal_sub_def,real_sub,extreal_ainv_def]);

val MUL_IN_Q = store_thm
  ("MUL_IN_Q", ``!x y. (x IN Q_set) /\ (y IN Q_set) ==> (x * y IN Q_set)``,	
  RW_TAC std_ss [Q_set_def,EXTENSION,GSPECIFICATION,IN_UNION,extreal_of_num_def] <<
 [DISJ1_TAC
  ++ `&b <> 0:real /\ &b' <> 0:real` by FULL_SIMP_TAC real_ss [extreal_lt_eq,REAL_LT_IMP_NE]
  ++ `0:real < &(b * b')` by METIS_TAC [extreal_lt_eq,REAL_LT_MUL,mult_ints]
  ++ `&(b * b') <> 0:real` by RW_TAC std_ss [REAL_LT_IMP_NE]
  ++ Q.EXISTS_TAC `a * a'`
  ++ Q.EXISTS_TAC `b * b'`
  ++ RW_TAC std_ss [extreal_div_eq,extreal_mul_def,extreal_lt_eq]
  ++ FULL_SIMP_TAC real_ss [mult_rat,REAL_LT_REFL,ZERO_LESS_MULT],
  DISJ2_TAC
  ++ `&b <> 0:real /\ &b' <> 0:real` by FULL_SIMP_TAC real_ss [extreal_lt_eq,REAL_LT_IMP_NE]
  ++ `0:real < &(b * b')` by METIS_TAC [extreal_lt_eq,REAL_LT_MUL,mult_ints]
  ++ `&(b * b') <> 0:real` by RW_TAC std_ss [REAL_LT_IMP_NE]
  ++ Q.EXISTS_TAC `a*a'`
  ++ Q.EXISTS_TAC `b*b'`
  ++ RW_TAC std_ss [extreal_div_eq,extreal_mul_def,extreal_lt_eq,extreal_ainv_def]
  ++ FULL_SIMP_TAC real_ss [mult_rat,REAL_LT_REFL,ZERO_LESS_MULT],
  DISJ2_TAC
  ++ `&b <> 0:real /\ &b' <> 0:real` by FULL_SIMP_TAC real_ss [extreal_lt_eq,REAL_LT_IMP_NE]
  ++ `0:real < &(b * b')` by METIS_TAC [extreal_lt_eq,REAL_LT_MUL,mult_ints]
  ++ `&(b * b') <> 0:real` by RW_TAC std_ss [REAL_LT_IMP_NE]
  ++ Q.EXISTS_TAC `a*a'`
  ++ Q.EXISTS_TAC `b*b'`
  ++ RW_TAC std_ss [extreal_div_eq,extreal_mul_def,extreal_lt_eq,extreal_ainv_def]
  ++ FULL_SIMP_TAC real_ss [mult_rat,REAL_LT_REFL,ZERO_LESS_MULT],
  DISJ1_TAC
  ++ `&b <> 0:real /\ &b' <> 0:real` by FULL_SIMP_TAC real_ss [extreal_lt_eq,REAL_LT_IMP_NE]
  ++ `0:real < &(b * b')` by METIS_TAC [extreal_lt_eq,REAL_LT_MUL,mult_ints]
  ++ `&(b * b') <> 0:real` by RW_TAC std_ss [REAL_LT_IMP_NE]
  ++ Q.EXISTS_TAC `a*a'`
  ++ Q.EXISTS_TAC `b*b'`
  ++ RW_TAC std_ss [extreal_div_eq,extreal_mul_def,extreal_lt_eq,extreal_ainv_def]
  ++ FULL_SIMP_TAC real_ss [mult_rat,REAL_LT_REFL,ZERO_LESS_MULT]]);  	             
  	             
val DIV_IN_Q = store_thm
  ("DIV_IN_Q", ``!x y. (x IN Q_set) /\ (y IN Q_set) /\ (y <> 0) ==> (x / y IN Q_set)``,	
  RW_TAC std_ss []
  ++ `?x1. x = Normal x1` by METIS_TAC [Q_not_infty]
  ++ `?y1. y = Normal y1` by METIS_TAC [Q_not_infty]
  ++ RW_TAC std_ss [extreal_div_def,extreal_inv_def,extreal_mul_def]
  >> METIS_TAC [extreal_of_num_def]
  ++ `Normal (inv y1) IN Q_set` by METIS_TAC [INV_IN_Q,REAL_INV_1OVER,INV_IN_Q,extreal_div_eq,extreal_inv_def,extreal_of_num_def]
  ++  METIS_TAC [MUL_IN_Q,extreal_mul_def]);

val rat_not_infty = store_thm
("rat_not_infty",``!r. r IN Q_set ==> r <> NegInf /\ r <> PosInf``,
  RW_TAC std_ss [Q_set_def,GSPECIFICATION,IN_UNION,extreal_of_num_def]
  ++ `&b <> 0:real` by METIS_TAC [extreal_lt_eq,REAL_LT_IMP_NE]
  ++ RW_TAC std_ss [extreal_div_eq,extreal_ainv_def]);

val ceiling_def = Define
        `ceiling (Normal x) = LEAST (n:num). x <= &n`;

fun LEAST_ELIM_TAC (asl, w) = let
  val least_terms = find_terms numSyntax.is_least w
  val tbc = TRY_CONV BETA_CONV
  fun doit t =
    if free_in t w then
      CONV_TAC (UNBETA_CONV t) THEN
      MATCH_MP_TAC whileTheory.LEAST_ELIM THEN
      CONV_TAC
        (FORK_CONV
           (BINDER_CONV tbc, (* ?n. P n *)
            BINDER_CONV      (* !n. (!m. m < n ==> ~P m) /\ P n ==> Q n *)
              (FORK_CONV
                 (FORK_CONV
                    (BINDER_CONV (RAND_CONV (RAND_CONV tbc)), (* !m.... *)
                     tbc), (* P n *)
                    tbc))))
    else NO_TAC
in
  FIRST (map doit least_terms)
end (asl, w);

val CEILING_LBOUND = store_thm
  ("CEILING_LBOUND",``!x. Normal x <= &(ceiling (Normal x))``,
  RW_TAC std_ss [ceiling_def]
  ++ LEAST_ELIM_TAC
  ++ REWRITE_TAC [SIMP_REAL_ARCH]
  ++ METIS_TAC [extreal_of_num_def,extreal_le_def]);

val CEILING_UBOUND = store_thm
  ("CEILING_UBOUND", ``!x. (0 <= x) ==> &(ceiling( Normal x)) < (Normal x) + 1``,
  RW_TAC std_ss [ceiling_def,extreal_of_num_def,extreal_add_def,extreal_lt_eq]
  ++ LEAST_ELIM_TAC
  ++ REWRITE_TAC [SIMP_REAL_ARCH]
  ++ RW_TAC real_ss []	
  ++ FULL_SIMP_TAC real_ss [GSYM real_lt]
  ++ PAT_ASSUM ``!m. P`` (MP_TAC o Q.SPEC `n-1`)
  ++ RW_TAC real_ss []
  ++ Cases_on `n = 0` >> METIS_TAC [REAL_LET_ADD2,REAL_LT_01,REAL_ADD_RID]
  ++ `0 < n` by RW_TAC real_ss []
  ++ `&(n - 1) < x:real` by RW_TAC real_ss []
  ++ `0 <= n-1` by RW_TAC real_ss []
  ++ `0:real <= (&(n-1))` by RW_TAC real_ss []	
  ++ `0 < x` by METIS_TAC [REAL_LET_TRANS]
  ++ Cases_on `n = 1` >> METIS_TAC [REAL_LE_REFL,REAL_ADD_RID,REAL_LTE_ADD2,REAL_ADD_COMM]
  ++ `0 <> n-1` by RW_TAC real_ss []
  ++ `&n - 1 < x` by RW_TAC real_ss [REAL_SUB]
  ++ FULL_SIMP_TAC real_ss [REAL_LT_SUB_RADD]);

val Q_DENSE_IN_R_LEMMA = store_thm
  ("Q_DENSE_IN_R_LEMMA",``!x y. (0 <= x) /\ (x < y) ==> ?r. (r IN Q_set) /\ (x < r) /\ (r < y)``,
  (REPEAT Cases ++ RW_TAC std_ss [le_infty,lt_infty,extreal_of_num_def,extreal_not_infty])
  >> (Q.EXISTS_TAC `(&ceiling (Normal r)) + 1`
      ++ RW_TAC std_ss [extreal_of_num_def,extreal_add_def,lt_infty,extreal_lt_eq]
      >> METIS_TAC [ADD_IN_Q,NUM_IN_Q,extreal_add_def,extreal_of_num_def]
      ++ METIS_TAC [extreal_lt_eq,let_trans,REAL_LT_ADDR,REAL_LT_01,extreal_le_def,CEILING_LBOUND,extreal_of_num_def])
  ++ FULL_SIMP_TAC std_ss [extreal_le_def,extreal_lt_eq]
  ++ Cases_on `1 < r' - r`
  >> (Q.EXISTS_TAC `Normal (&(ceiling (Normal r')) - 1)`
      ++ CONJ_TAC >> METIS_TAC [SUB_IN_Q,NUM_IN_Q,extreal_sub_def,extreal_of_num_def]
      ++ RW_TAC std_ss [extreal_lt_eq]
      >> METIS_TAC [REAL_LT_SUB_LADD,REAL_LT_ADD_SUB,REAL_ADD_COMM,REAL_LTE_TRANS,CEILING_LBOUND,extreal_of_num_def,extreal_lt_eq,extreal_le_def]
      ++ METIS_TAC [REAL_LT_SUB_RADD,CEILING_UBOUND,REAL_LET_TRANS,REAL_LT_IMP_LE,extreal_of_num_def,extreal_lt_eq,extreal_le_def,extreal_sub_def,extreal_add_def])         
  ++ `0 < r' - r` by RW_TAC real_ss [REAL_SUB_LT]
  ++ (MP_TAC o Q.SPEC `1`) (((UNDISCH o Q.SPEC `r' - r`) REAL_ARCH))
  ++ RW_TAC real_ss []
  ++ Suff `?r2. r2 IN Q_set /\ &n * Normal (r) < r2 /\ r2 < &n * Normal (r')`
  >> (RW_TAC real_ss []
      ++ `0 < n` by ( RW_TAC real_ss [] ++ SPOSE_NOT_THEN ASSUME_TAC ++ `n = 0` by RW_TAC real_ss [] ++ FULL_SIMP_TAC real_ss [])	
      ++ `0 < (&n)` by RW_TAC real_ss [extreal_lt_eq,extreal_of_num_def]
      ++ Q.EXISTS_TAC `r2 / (&n)`
      ++ RW_TAC real_ss [DIV_IN_Q,NUM_IN_Q,lt_imp_ne]
      >> (`?y. r2 = Normal y` by METIS_TAC [Q_not_infty]
          ++ FULL_SIMP_TAC real_ss [extreal_of_num_def,extreal_div_eq,extreal_lt_eq,extreal_mul_def]
	  ++ FULL_SIMP_TAC real_ss [REAL_LT_RDIV_EQ,REAL_MUL_COMM,REAL_LT_IMP_NE])
      ++ `?y. r2 = Normal y` by METIS_TAC [Q_not_infty]
      ++ FULL_SIMP_TAC real_ss [extreal_of_num_def,extreal_div_eq,extreal_lt_eq,extreal_mul_def]
      ++ FULL_SIMP_TAC real_ss [REAL_LT_LDIV_EQ,REAL_MUL_COMM,REAL_LT_IMP_NE])
   ++ `1 < &n * r' - &n * r` by FULL_SIMP_TAC real_ss [REAL_SUB_LDISTRIB]
   ++ Q.EXISTS_TAC `&(ceiling (&n * Normal (r'))) - 1`
   ++ CONJ_TAC >> METIS_TAC [SUB_IN_Q,NUM_IN_Q,extreal_sub_def,extreal_of_num_def]
   ++ RW_TAC std_ss [extreal_of_num_def,extreal_mul_def,extreal_sub_def,extreal_lt_eq,extreal_le_def]
   >> METIS_TAC [REAL_LT_SUB_LADD,REAL_LT_ADD_SUB,REAL_ADD_COMM,REAL_LTE_TRANS,CEILING_LBOUND,extreal_of_num_def,extreal_lt_eq,extreal_le_def]
   ++ `0:real <= &n` by RW_TAC real_ss []
   ++ `0:real <= &n * r'` by METIS_TAC [REAL_LE_MUL,REAL_LET_TRANS,REAL_LT_IMP_LE]
   ++ METIS_TAC [REAL_LT_SUB_RADD,CEILING_UBOUND,REAL_LET_TRANS,REAL_LT_IMP_LE,extreal_of_num_def,extreal_lt_eq,extreal_le_def,extreal_sub_def,extreal_add_def,extreal_mul_def]);

val Q_DENSE_IN_R = store_thm
  ("Q_DENSE_IN_R",``!x y. (x < y) ==> ?r. (r IN Q_set) /\ (x < r) /\ (r < y)``,
 RW_TAC std_ss []
 ++ Cases_on `0<=x` >> RW_TAC std_ss [Q_DENSE_IN_R_LEMMA]
 ++ FULL_SIMP_TAC std_ss [GSYM extreal_lt_def]
 ++ `y <> NegInf` by METIS_TAC [lt_infty]
 ++ (Cases_on `y` ++ RW_TAC std_ss [])
 >> (Q.EXISTS_TAC `0` ++ METIS_TAC [NUM_IN_Q,extreal_of_num_def,extreal_not_infty,lt_infty])
 ++ `x <> PosInf` by METIS_TAC [lt_infty,lt_trans,extreal_not_infty,extreal_of_num_def]
 ++ Cases_on `x = NegInf`
 >> (Cases_on `0<=r`
     >> (Q.EXISTS_TAC `&ceiling (Normal r)- 1`
         ++ RW_TAC std_ss [extreal_of_num_def,extreal_sub_def,extreal_not_infty,lt_infty,extreal_lt_eq]
         >> METIS_TAC [SUB_IN_Q,NUM_IN_Q,extreal_sub_def,extreal_of_num_def]
         ++ METIS_TAC [CEILING_UBOUND,REAL_LT_SUB_RADD,extreal_of_num_def,extreal_lt_eq,extreal_add_def])
     ++ Q.EXISTS_TAC `- &ceiling (Normal (-r)) - 1`
     ++ RW_TAC std_ss [extreal_of_num_def,extreal_sub_def,extreal_not_infty,lt_infty,extreal_lt_eq,extreal_ainv_def]
     >> METIS_TAC [SUB_IN_Q,NUM_IN_Q,extreal_sub_def,extreal_of_num_def,OPP_IN_Q,extreal_ainv_def]
     ++ (MP_TAC o Q.SPEC `-r`) CEILING_LBOUND
     ++ RW_TAC std_ss [extreal_of_num_def,extreal_le_def]
     ++ POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM REAL_LE_NEG])
     ++ RW_TAC std_ss [REAL_NEG_NEG]
     ++ METIS_TAC [REAL_LT_SUB_RADD,REAL_LET_TRANS,REAL_LT_ADDR,REAL_LT_01])
 ++ `?r. x = Normal r` by METIS_TAC [extreal_cases]
 ++ FULL_SIMP_TAC std_ss [extreal_of_num_def,extreal_lt_eq]
 ++ `Normal (-r') <= &(ceiling (Normal (-r')))` by RW_TAC real_ss [CEILING_LBOUND]
 ++ `-Normal (r') <= &ceiling (Normal (-r'))` by METIS_TAC [extreal_ainv_def]
 ++ `0 <= Normal (r') + &(ceiling (Normal (-r')))` by METIS_TAC [le_lneg,extreal_of_num_def,extreal_add_def,extreal_not_infty]
 ++ `&(ceiling (Normal (-r'))) <> NegInf /\ &(ceiling (Normal (-r'))) <> PosInf`
     by METIS_TAC [extreal_of_num_def,extreal_not_infty]
 ++ `Normal (r') + &(ceiling (Normal (-r'))) < Normal (r) + &(ceiling (Normal (-r')))` 
    by METIS_TAC [extreal_lt_eq,lt_radd]
 ++ Suff `?r2. (r2 IN Q_set) /\ (Normal r' + &ceiling (Normal (-r')) < r2) /\ (r2<Normal r + &ceiling (Normal (-r')))`
 >> (RW_TAC std_ss []
     ++ Q.EXISTS_TAC `r2 - &ceiling (Normal (-r'))`
     ++ CONJ_TAC >> METIS_TAC [SUB_IN_Q,NUM_IN_Q,extreal_of_num_def]
     ++ `?y. r2 = Normal y` by METIS_TAC [Q_not_infty]
     ++ FULL_SIMP_TAC std_ss [extreal_of_num_def,extreal_lt_eq,extreal_le_def,extreal_sub_def,extreal_add_def]
     ++ RW_TAC std_ss [GSYM REAL_LT_ADD_SUB,REAL_LT_SUB_RADD])
 ++ RW_TAC std_ss [Q_DENSE_IN_R_LEMMA]);


val COUNTABLE_ENUM_Q = store_thm
  ("COUNTABLE_ENUM_Q",
   ``!c. countable c = (c = {}) \/ (?f:extreal->'a. c = IMAGE f Q_set)``,
  RW_TAC std_ss []
  ++ REVERSE EQ_TAC
  >> (NTAC 2 (RW_TAC std_ss [COUNTABLE_EMPTY])       
      ++ RW_TAC std_ss [COUNTABLE_IMAGE,Q_COUNTABLE])
  ++ REVERSE (RW_TAC std_ss [COUNTABLE_ALT])
  >> (DISJ2_TAC
      ++ `countable Q_set` by RW_TAC std_ss [Q_COUNTABLE]
      ++ `~(FINITE Q_set)` by RW_TAC std_ss [Q_INFINITE]
      ++ (MP_TAC o Q.SPEC `Q_set`) (INST_TYPE [alpha |-> ``:extreal``] COUNTABLE_ALT)
      ++ RW_TAC std_ss []
      ++ (MP_TAC o Q.SPECL [`enumerate Q_set`,`UNIV`,`Q_set`]) (INST_TYPE [alpha |-> ``:num``, ``:'b`` |-> ``:extreal``] BIJ_INV)
      ++ (MP_TAC o Q.SPECL [`enumerate c`,`UNIV`,`c`]) (INST_TYPE [alpha |-> ``:num``, ``:'b`` |-> ``:'a``] BIJ_INV)
      ++ RW_TAC std_ss []
      ++ Q.EXISTS_TAC `(enumerate c) o g'`
      ++ RW_TAC std_ss [IMAGE_DEF,EXTENSION,GSPECIFICATION]
      ++ EQ_TAC 
      >> (RW_TAC std_ss []
          ++ Q.EXISTS_TAC `enumerate Q_set (g x)`
          >> METIS_TAC [BIJ_DEF,INJ_DEF]
          ++ METIS_TAC [BIJ_DEF,INJ_DEF])
      ++ RW_TAC std_ss []
      ++ METIS_TAC [BIJ_DEF,INJ_DEF])
  ++ POP_ASSUM MP_TAC
  ++ Q.SPEC_TAC (`c`, `c`)
  ++ HO_MATCH_MP_TAC FINITE_INDUCT
  ++ RW_TAC std_ss []
  >> (DISJ2_TAC
      ++ Q.EXISTS_TAC `K e`
      ++ RW_TAC std_ss [EXTENSION, IN_SING, IN_IMAGE, IN_UNIV, K_THM]
      ++ EQ_TAC 
      >> (RW_TAC std_ss [] ++ Q.EXISTS_TAC `0` ++ METIS_TAC [NUM_IN_Q])
      ++ RW_TAC std_ss [])
  ++  DISJ2_TAC
  ++ ASSUME_TAC (Q.SPECL [`f:extreal->'a`,`Q_set`,`IMAGE f Q_set`] (INST_TYPE [alpha |-> ``:extreal``,``:'b`` |-> ``:'a``] INFINITE_INJ))       
  ++ `~(INJ f Q_set (IMAGE f Q_set))` by METIS_TAC [INFINITE_DEF,MONO_NOT,Q_INFINITE]
  ++ FULL_SIMP_TAC std_ss [INJ_DEF] >> METIS_TAC [IN_IMAGE]           
  ++ Q.EXISTS_TAC `(\u. if u=x then e else f u)`
  ++ `Q_set = (Q_set DIFF {x}) UNION {x}` by (RW_TAC std_ss [DIFF_DEF,UNION_DEF,EXTENSION,GSPECIFICATION,IN_SING] ++ METIS_TAC [])
  ++ `(IMAGE (\u. if u = x then e else f u) Q_set) = (IMAGE (\u. if u = x then e else f u) (Q_set DIFF {x})) UNION (IMAGE (\u. if u = x then e else f u) {x})` by METIS_TAC [IMAGE_UNION]
  ++ `IMAGE (\u. if u = x then e else f u) {x} = {e}` by RW_TAC std_ss [IMAGE_DEF,EXTENSION,GSPECIFICATION,IN_SING]
  ++ `IMAGE (\u. if u = x then e else f u) (Q_set DIFF {x}) = IMAGE f Q_set` by RW_TAC std_ss [IMAGE_DEF,EXTENSION,GSPECIFICATION,DIFF_DEF,IN_UNION,IN_SING]
  ++ `(IMAGE f Q_set) = (IMAGE f (Q_set DIFF {x})) UNION (IMAGE f {x})` by METIS_TAC [IMAGE_UNION]
  ++ `IMAGE f {x} = {f y}` by RW_TAC std_ss [IMAGE_DEF,EXTENSION,GSPECIFICATION,IN_SING]
  ++ `IMAGE f Q_set = (IMAGE f (Q_set DIFF {x})) UNION {f y}` by METIS_TAC []
  ++ `{f y} SUBSET IMAGE f (Q_set DIFF {x})` by ( RW_TAC std_ss [SUBSET_DEF,IN_IMAGE,IN_SING] ++ Q.EXISTS_TAC `y` ++ RW_TAC std_ss [IN_DIFF,IN_SING])
  ++ `IMAGE f Q_set = IMAGE f (Q_set DIFF {x})` by METIS_TAC [SUBSET_UNION_ABSORPTION,UNION_COMM]
  ++ `IMAGE (\u. if u = x then e else f u) (Q_set DIFF {x}) = IMAGE f (Q_set DIFF {x})`
     by (RW_TAC std_ss [IMAGE_DEF,EXTENSION,GSPECIFICATION,DIFF_DEF,IN_SING]
       	        ++ EQ_TAC 
                >> (RW_TAC std_ss []
         	    ++ Q.EXISTS_TAC `u`
       		    ++ RW_TAC std_ss [])
       		++ RW_TAC std_ss []
       		++ Q.EXISTS_TAC `x''`
       		++ RW_TAC std_ss [])
  ++ METIS_TAC [INSERT_SING_UNION,UNION_COMM]);

val CROSS_COUNTABLE_UNIV = store_thm
 ("CROSS_COUNTABLE_UNIV", ``countable (UNIV:num->bool CROSS UNIV:num->bool)``, 
  RW_TAC std_ss [countable_def]
  ++ `?(f :num -> num # num). BIJ f UNIV (UNIV CROSS UNIV)` by METIS_TAC [NUM_2D_BIJ_INV]
  ++ Q.EXISTS_TAC `f`
  ++ RW_TAC std_ss []
  ++ FULL_SIMP_TAC std_ss [BIJ_DEF,INJ_DEF,SURJ_DEF,CROSS_DEF,IN_UNIV]);
		    
val CROSS_COUNTABLE_LEMMA1 = store_thm
  ("CROSS_COUNTABLE_LEMMA1", ``!s. countable s /\ FINITE s /\ countable t ==> countable (s CROSS t)``,
  RW_TAC std_ss []
  ++ Q.PAT_ASSUM `FINITE s` MP_TAC
  ++ Q.SPEC_TAC (`s`, `s`)
  ++ HO_MATCH_MP_TAC FINITE_INDUCT
  ++ RW_TAC std_ss [] >> METIS_TAC [CROSS_EMPTY,COUNTABLE_EMPTY]
  ++ RW_TAC std_ss [CROSS_EQNS]
  ++ MATCH_MP_TAC COUNTABLE_UNION
  ++ RW_TAC std_ss []
  ++ RW_TAC std_ss [COUNTABLE_IMAGE]);
	
val CROSS_COUNTABLE_LEMMA2 = store_thm
  ("CROSS_COUNTABLE_LEMMA2", ``!s. countable s /\ countable t /\ FINITE t ==> countable (s CROSS t)``,
  RW_TAC std_ss []
  ++ `s CROSS t = IMAGE (\a. (SND a,FST a)) (t CROSS s)`
  	by (RW_TAC std_ss [CROSS_DEF,IMAGE_DEF,EXTENSION,GSPECIFICATION]
	    ++ EQ_TAC 
            >> (RW_TAC std_ss []
	        ++ Q.EXISTS_TAC `(SND x,FST x)`
	        ++ RW_TAC std_ss [])
            ++ RW_TAC std_ss [] >> RW_TAC std_ss []
            ++ RW_TAC std_ss [])
  ++ METIS_TAC [COUNTABLE_IMAGE,CROSS_COUNTABLE_LEMMA1]);


val CROSS_COUNTABLE = store_thm
 ("CROSS_COUNTABLE", ``!s. countable s /\ countable t ==> countable (s CROSS t)``,
  RW_TAC std_ss []
  ++ Cases_on `FINITE s` >> METIS_TAC [CROSS_COUNTABLE_LEMMA1]
  ++ Cases_on `FINITE t` >> METIS_TAC [CROSS_COUNTABLE_LEMMA2]
  ++ `BIJ (enumerate s) UNIV s` by METIS_TAC [COUNTABLE_ALT]
  ++ `BIJ (enumerate t) UNIV t` by METIS_TAC [COUNTABLE_ALT]
  ++ Q.ABBREV_TAC `f = enumerate s`
  ++ Q.ABBREV_TAC `g = enumerate t`
  ++ `s CROSS t = IMAGE (\(x,y). (f x,g y)) (UNIV CROSS UNIV)` 
	by (Q.UNABBREV_TAC `f` ++ Q.UNABBREV_TAC `g` 
	    ++ RW_TAC std_ss [CROSS_DEF,IMAGE_DEF,EXTENSION,GSPECIFICATION,IN_UNIV]
	    ++ EQ_TAC 
            >> (RW_TAC std_ss []
		++ FULL_SIMP_TAC std_ss [BIJ_DEF,SURJ_DEF,INJ_DEF,IN_UNIV]
		++ `?n1. (enumerate s) n1 = FST x` by METIS_TAC []
		++ `?n2. (enumerate t) n2 = SND x` by METIS_TAC []
		++ Q.EXISTS_TAC `(n1, n2)`
		++  RW_TAC std_ss [])
	    ++ RW_TAC std_ss []
	    >> (Cases_on `x'`
		++ RW_TAC std_ss []
		++ FULL_SIMP_TAC std_ss [BIJ_DEF,SURJ_DEF,INJ_DEF,IN_UNIV])
     	    ++ Cases_on `x'`
	    ++ RW_TAC std_ss []
	    ++ FULL_SIMP_TAC std_ss [BIJ_DEF,SURJ_DEF,INJ_DEF,IN_UNIV])
  ++ METIS_TAC [CROSS_COUNTABLE_UNIV,COUNTABLE_IMAGE]);

val open_interval_def = Define 
    `open_interval a b = {x | a < x /\ x < b}`;
    
val open_intervals_set_def = Define
    `open_intervals_set = {open_interval a b | a IN UNIV /\ b IN UNIV}`;

val rational_intervals_def = Define
	`rational_intervals = {open_interval a b | a IN Q_set /\ b IN Q_set}`;
	
val COUNTABLE_RATIONAL_INTERVALS = store_thm
 ("COUNTABLE_RATIONAL_INTERVALS", ``countable rational_intervals``,
 `rational_intervals = IMAGE (\(a,b). open_interval a b) (Q_set CROSS Q_set)` 
     by (RW_TAC std_ss [rational_intervals_def,IMAGE_DEF,EXTENSION,GSPECIFICATION,IN_CROSS]	
         ++ EQ_TAC 
         >> (RW_TAC std_ss []
 	     ++ Q.EXISTS_TAC `x'`
 	     ++ Cases_on `x'`
 	     ++ FULL_SIMP_TAC std_ss [PAIR_EQ])
	 ++ RW_TAC std_ss []
	 ++ Q.EXISTS_TAC `x'`
	 ++ Cases_on `x'`
	 ++ FULL_SIMP_TAC std_ss [PAIR_EQ,EXTENSION])
  ++ METIS_TAC [CROSS_COUNTABLE,Q_COUNTABLE,COUNTABLE_IMAGE]);
	
val _ = export_theory ();
