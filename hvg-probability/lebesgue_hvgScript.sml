(* ------------------------------------------------------------------------- *)
(* Lebesgue Theory defined on the extended real numbers                      *)
(* Authors: Tarek Mhamdi, Osman Hasan, Sofiene Tahar                         *)
(* HVG Group, Concordia University, Montreal                                 *)
(* ------------------------------------------------------------------------- *)
(* Based on the work of Aaron Coble, Cambridge University                    *)
(* ------------------------------------------------------------------------- *)

(*

val () = app load
 ["bossLib", "metisLib", "arithmeticTheory", "pred_setTheory", "realLib", "pairTheory",
   "seqTheory", "transcTheory", "util_probTheory", "extreal_hvgTheory", 
   "prim_recTheory", "measure_hvgTheory"];

set_trace "Unicode" 0;

*)

open HolKernel Parse boolLib bossLib metisLib
     combinTheory pred_setTheory arithmeticTheory realTheory realLib pairTheory 
      seqTheory transcTheory real_sigmaTheory jrhUtils util_probTheory
      extreal_hvgTheory prim_recTheory measure_hvgTheory;

val _ = new_theory "lebesgue_hvg";

infixr 0 ++ << || THENC ORELSEC ORELSER ##;
infix 1 >>;

val op ++ = op THEN;
val op << = op THENL;
val op >> = op THEN1;
val op || = op ORELSE;
val REVERSE = Tactical.REVERSE;

fun parse_with_goal t (asms, g) =
  let
    val ctxt = free_varsl (g::asms)
  in
    Parse.parse_in_context ctxt t
  end;

val PARSE_TAC = fn tac => fn q => W (tac o parse_with_goal q);

val Simplify = RW_TAC arith_ss;
val Suff = PARSE_TAC SUFF_TAC;
val Know = PARSE_TAC KNOW_TAC;
fun wrap a = [a];
val Rewr = DISCH_THEN (REWRITE_TAC o wrap);
val Rewr' = DISCH_THEN (ONCE_REWRITE_TAC o wrap);
val Cond =
  DISCH_THEN
  (fn mp_th =>
   let
     val cond = fst (dest_imp (concl mp_th))
   in
     KNOW_TAC cond << [ALL_TAC, DISCH_THEN (MP_TAC o MP mp_th)]
   end);

val POP_ORW = POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm]);

val FUN_EQ_TAC = CONV_TAC (CHANGED_CONV (ONCE_DEPTH_CONV FUN_EQ_CONV));

(* ************************************************************************* *)
(* Basic Definitions                                                         *)
(* ************************************************************************* *)


val pos_simple_fn_integral_def = Define
   `pos_simple_fn_integral m s a x =
	(SIGMA (\i:num. Normal (x i) * ((measure m) (a i))) s)`;

val psfs_def = Define
   `psfs m f = {(s,a,x) | pos_simple_fn m f s a x}`;

val psfis_def = Define
   `psfis m f = IMAGE (\(s,a,x). pos_simple_fn_integral m s a x) (psfs m f)`;

val pos_fn_integral_def = Define
   `pos_fn_integral m f = sup {r | ?g. r IN psfis m g /\ !x. g x <= f x}`;

val integral_def = Define
   `integral m f =
	(pos_fn_integral m (\x. if 0 < f x then f x else 0)) -
	(pos_fn_integral m (\x. if f x < 0 then ~ f x else 0))`;

val finite_space_integral_def = Define
   `finite_space_integral m f =
	SIGMA (\r. r * measure m (PREIMAGE f {r} INTER m_space m)) (IMAGE f (m_space m))`;


(*****************************************************************************)

val pos_simple_fn_integral_present = store_thm
  ("pos_simple_fn_integral_present",
   ``!m f (s:num->bool) a x g (s':num->bool) b y.
	measure_space m /\ pos_simple_fn m f s a x /\ pos_simple_fn m g s' b y ==>
	(?z z' c (k:num->bool).
		(!t. t IN m_space m ==> (f t = SIGMA (\i. Normal (z i) * (indicator_fn (c i) t)) k)) /\
		(!t. t IN m_space m ==> (g t = SIGMA (\i. Normal (z' i) * (indicator_fn (c i) t)) k)) /\
		(pos_simple_fn_integral m s a x = pos_simple_fn_integral m k c z) /\
		(pos_simple_fn_integral m s' b y = pos_simple_fn_integral m k c z') /\
		FINITE k /\ (!i. i IN k ==> 0 <= z i) /\ (!i. i IN k ==> 0 <= z' i) /\
		(!i j. i IN k /\ j IN k /\ (~(i=j)) ==> DISJOINT (c i) (c j)) /\
		(!i. i IN k ==> c i IN measurable_sets m) /\
		(BIGUNION (IMAGE c k) = m_space m))``,
   RW_TAC std_ss []
   ++ `?p n. BIJ p (count n) (s CROSS s')`
	by FULL_SIMP_TAC std_ss [GSYM FINITE_BIJ_COUNT, pos_simple_fn_def, FINITE_CROSS]
   ++ `?p'. BIJ p' (s CROSS s') (count n) /\
	    (!x. x IN (count n) ==> ((p' o p) x = x)) /\
	    (!x. x IN (s CROSS s') ==> ((p o p') x = x))`
	by (MATCH_MP_TAC BIJ_INV ++ RW_TAC std_ss [])
   ++ Q.EXISTS_TAC `x o FST o p`
   ++ Q.EXISTS_TAC `y o SND o p`
   ++ Q.EXISTS_TAC `(\(i,j). a i INTER b j) o p`
   ++ Q.EXISTS_TAC `IMAGE p' (s CROSS s')`
   ++ Q.ABBREV_TAC `G = IMAGE (\i j. p' (i,j)) s'`
   ++ Q.ABBREV_TAC `H = IMAGE (\j i. p' (i,j)) s`
   ++ CONJ_TAC
   >> (RW_TAC std_ss [FUN_EQ_THM] 
       ++ FULL_SIMP_TAC std_ss [pos_simple_fn_def]
       ++ `!i. i IN s ==> (\i. Normal (x i) * indicator_fn (a i) t) i <> NegInf` 
            by METIS_TAC [indicator_fn_def,mul_rzero,mul_rone,extreal_not_infty,extreal_of_num_def]
       ++ FULL_SIMP_TAC std_ss [(Once o UNDISCH o Q.ISPEC `(s :num -> bool)`) EXTREAL_SUM_IMAGE_IN_IF]
       ++ `(\x'. (if x' IN s then (\i. Normal (x i) * indicator_fn (a i) t) x' else 0)) =
	   (\x'. (if x' IN s then (\i. Normal (x i) * 
		SIGMA (\j. indicator_fn (a i INTER b j) t) s') x' else 0))`
	by (RW_TAC std_ss [FUN_EQ_THM]
	    ++ RW_TAC std_ss []
	    ++ FULL_SIMP_TAC std_ss [GSYM AND_IMP_INTRO]
	    ++ (MP_TAC o Q.ISPEC `(a :num -> 'a -> bool) (x' :num)` o 
		UNDISCH_ALL o REWRITE_RULE [GSYM AND_IMP_INTRO] o 
		Q.ISPECL 
		[`(s' :num -> bool)`,
		 `m_space (m:('a -> bool) #
          	  (('a -> bool) -> bool) # (('a -> bool) -> extreal))`,
		 `(b :num -> 'a -> bool)`]) indicator_fn_split
	    ++ Q.PAT_X_ASSUM `!i. i IN s ==> (a:num->'a->bool) i IN measurable_sets m`
		(ASSUME_TAC o UNDISCH o Q.SPEC `x'`)
	    ++ `!a m. measure_space m /\
	      a IN measurable_sets m ==> a SUBSET m_space m`
		by RW_TAC std_ss [measure_space_def, sigma_algebra_def, algebra_def,
 			   	  subset_class_def, subsets_def, space_def]
	    ++ POP_ASSUM (ASSUME_TAC o UNDISCH_ALL o REWRITE_RULE [GSYM AND_IMP_INTRO] o
			  Q.ISPECL [`(a :num -> 'a -> bool) (x' :num)`,
				    `(m : ('a -> bool) #
				     (('a -> bool) -> bool) # (('a -> bool) -> extreal))`])
	    ++ ASM_SIMP_TAC std_ss [])
       ++ FULL_SIMP_TAC std_ss []
       ++ `!i j. j IN s' ==> (\j. indicator_fn (a i INTER b j) t) j <> NegInf`
            by METIS_TAC [extreal_of_num_def,extreal_not_infty,indicator_fn_def]
       ++ `!(x':num) (i:num). Normal (x i) * SIGMA (\j. indicator_fn (a i INTER b j) t) s' =
		    SIGMA (\j. Normal (x i) * indicator_fn (a i INTER b j) t) s'`
	   by (RW_TAC std_ss []
               ++ (MP_TAC o UNDISCH o Q.SPEC `s'` o GSYM o INST_TYPE [alpha |-> ``:num``]) EXTREAL_SUM_IMAGE_CMUL
	       ++ FULL_SIMP_TAC std_ss [])
       ++ POP_ORW
       ++ `FINITE (s CROSS s')` by RW_TAC std_ss [FINITE_CROSS]
       ++ `INJ p' (s CROSS s')
	   (IMAGE p' (s CROSS s'))`
	   by METIS_TAC [INJ_IMAGE_BIJ, BIJ_DEF]
       ++ (MP_TAC o Q.SPEC `(\i:num. Normal (x (FST (p i))) * indicator_fn ((\(i:num,j:num). a i INTER b j) (p i)) t)` o UNDISCH o Q.SPEC `p'` o UNDISCH o Q.SPEC `s CROSS s'` o INST_TYPE [alpha |-> ``:num#num``, beta |-> ``:num``]) EXTREAL_SUM_IMAGE_IMAGE
       ++ `!x'. Normal (x (FST (p x'))) * indicator_fn ((\(i,j). a i INTER b j) (p x')) t <> NegInf` 
            by METIS_TAC [indicator_fn_def,mul_rzero,mul_rone,extreal_not_infty,extreal_of_num_def]
       ++ RW_TAC std_ss []
       ++ `!x'. ((\i. Normal (x (FST (p i))) * indicator_fn ((\(i,j). a i INTER b j) (p i)) t) o p') x' <> NegInf`
             by (RW_TAC std_ss [indicator_fn_def,mul_rzero,mul_rone]
                 ++ METIS_TAC [extreal_not_infty,extreal_of_num_def])
       ++ (MP_TAC o Q.SPEC `((\i. Normal (x (FST ((p :num -> num # num) i))) * indicator_fn ((\(i,j). a i INTER b j) (p i)) t) o p')` o UNDISCH o Q.ISPEC `(s :num -> bool)CROSS(s' :num -> bool)`) EXTREAL_SUM_IMAGE_IN_IF
       ++ RW_TAC std_ss []
       ++ `(\x'.if x' IN s CROSS s' then
                Normal (x (FST x')) * indicator_fn ((\(i,j). a i INTER b j) x') t
               else 0) =
	   (\x'. (if x' IN s CROSS s' then
		(\x'. Normal (x (FST x')) * indicator_fn ((\(i,j). a i INTER b j) x') t) x'
		 else 0))` by METIS_TAC []
       ++ POP_ORW
       ++ `!x'. (\x'. Normal (x (FST x')) * indicator_fn ((\(i,j). a i INTER b j) x') t) x' <> NegInf`
            by (RW_TAC std_ss [indicator_fn_def,mul_rzero,mul_rone]
                ++ METIS_TAC [extreal_not_infty,extreal_of_num_def])
       ++ (MP_TAC o Q.SPEC `(\x'. Normal (x (FST x')) * indicator_fn ((\(i,j). a i INTER b j) x') t)` o UNDISCH o Q.ISPEC `(s :num -> bool)CROSS(s' :num -> bool)`) (GSYM EXTREAL_SUM_IMAGE_IN_IF)
       ++ RW_TAC std_ss []
       ++ `!x'. NegInf <> (\i:num. SIGMA (\j:num. Normal (x i) * indicator_fn (a i INTER b j) t) s') x'`      
            by (RW_TAC std_ss []
                ++ `!j. (\j. Normal (x x') * indicator_fn (a x' INTER b j) t) j <> NegInf`
                     by (RW_TAC std_ss [indicator_fn_def,mul_rzero,mul_rone]
                         ++ METIS_TAC [extreal_of_num_def,extreal_not_infty])
                ++ FULL_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_NOT_INFTY])
       ++ (MP_TAC o Q.SPEC `(\i:num. SIGMA (\j:num. Normal (x i) * indicator_fn (a i INTER b j) t) s')` o UNDISCH o Q.ISPEC `(s :num -> bool)`) (GSYM EXTREAL_SUM_IMAGE_IN_IF)
       ++ RW_TAC std_ss []
       ++ (MP_TAC o Q.ISPECL [`s:num->bool`,`s':num->bool`]) EXTREAL_SUM_IMAGE_EXTREAL_SUM_IMAGE
       ++ RW_TAC std_ss []
       ++ POP_ASSUM (MP_TAC o Q.SPEC `(\i j. Normal (x i) * indicator_fn (a i INTER b j) t)`)
       ++ `!x'. Normal (x (FST x')) * indicator_fn (a (FST x') INTER b (SND x')) t <> NegInf`
             by (RW_TAC std_ss [indicator_fn_def,mul_rzero,mul_rone]
                 ++ METIS_TAC [extreal_of_num_def,extreal_not_infty])
       ++ RW_TAC std_ss []
       ++ Suff `(\i. Normal (x (FST i)) * indicator_fn (a (FST i) INTER b (SND i)) t) = 
                (\x'. Normal (x (FST x')) * indicator_fn ((\(i,j). a i INTER b j) x') t)`
       >> RW_TAC std_ss []
       ++ RW_TAC std_ss [FUN_EQ_THM]
       ++ Cases_on `x'`
       ++ RW_TAC std_ss [FST,SND])
   ++ CONJ_TAC
   >> (RW_TAC std_ss [FUN_EQ_THM] ++ FULL_SIMP_TAC std_ss [pos_simple_fn_def]
       ++ (MP_TAC o Q.SPEC `(\i. Normal (y i) * indicator_fn (b i) t)` o UNDISCH o Q.ISPEC `s':num->bool`) EXTREAL_SUM_IMAGE_IN_IF
       ++ `!x. x IN s' ==> (\i. Normal (y i) * indicator_fn (b i) t) x <> NegInf`
           by (RW_TAC std_ss [indicator_fn_def,mul_rzero,mul_rone]
                 ++ METIS_TAC [extreal_of_num_def,extreal_not_infty])
       ++ RW_TAC std_ss []
       ++ `(\x. if x IN s' then Normal (y x) * indicator_fn (b x) t else 0) = 
           (\x. (if x IN s' then (\i. Normal (y i) * indicator_fn (b i) t) x else 0))`
             by RW_TAC std_ss []
       ++ POP_ORW
       ++ `(\x. (if x IN s' then (\i. Normal (y i) * indicator_fn (b i) t) x else 0)) =
	   (\x. (if x IN s' then (\i. Normal (y i) * 
		SIGMA (\j. indicator_fn (a j INTER b i) t) s) x else 0))`
	by (RW_TAC std_ss [FUN_EQ_THM]
	    ++ RW_TAC std_ss []
	    ++ FULL_SIMP_TAC std_ss [GSYM AND_IMP_INTRO]
	    ++ (MP_TAC o REWRITE_RULE [Once INTER_COMM] o 
		Q.ISPEC `(b :num -> 'a -> bool) (x' :num)` o 
		UNDISCH_ALL o REWRITE_RULE [GSYM AND_IMP_INTRO] o 
		Q.ISPECL 
		[`(s :num -> bool)`,
		 `m_space (m:('a -> bool) #
          	  (('a -> bool) -> bool) # (('a -> bool) -> extreal))`,
		 `(a :num -> 'a -> bool)`]) indicator_fn_split
	    ++ Q.PAT_X_ASSUM `!i. i IN s' ==> (b:num->'a->bool) i IN measurable_sets m`
		(ASSUME_TAC o UNDISCH o Q.SPEC `x'`)
	    ++ RW_TAC std_ss [MEASURE_SPACE_SUBSET_MSPACE])
       ++ POP_ORW
       ++ `!(x:num) (i:num). Normal (y i) * SIGMA (\j. indicator_fn (a j INTER b i) t) s =
			      SIGMA (\j. Normal (y i) * indicator_fn (a j INTER b i) t) s`
             by (RW_TAC std_ss []
                 ++ `!j. (\j. indicator_fn (a j INTER b i) t) j <> NegInf`
                      by RW_TAC std_ss [indicator_fn_def,extreal_of_num_def,extreal_not_infty]
                 ++ FULL_SIMP_TAC std_ss [GSYM EXTREAL_SUM_IMAGE_CMUL])
       ++ POP_ORW
       ++ `FINITE (s CROSS s')` by RW_TAC std_ss [FINITE_CROSS]
       ++ `INJ p' (s CROSS s')
	   (IMAGE p' (s CROSS s'))`
	     by METIS_TAC [INJ_IMAGE_BIJ, BIJ_DEF]
       ++ (MP_TAC o Q.SPEC `(\i:num. Normal (y (SND (p i))) * indicator_fn ((\(i:num,j:num). a i INTER b j) (p i)) t)` o UNDISCH o Q.SPEC `p'` o UNDISCH o Q.SPEC `s CROSS s'` o INST_TYPE [alpha |-> ``:num#num``, beta |-> ``:num``]) EXTREAL_SUM_IMAGE_IMAGE
       ++ `!x. (\i. Normal (y (SND (p i))) * indicator_fn ((\(i,j). a i INTER b j) (p i)) t) x <> NegInf`
            by METIS_TAC [indicator_fn_def,mul_rzero,mul_rone,extreal_not_infty,extreal_of_num_def]
       ++ RW_TAC std_ss []
       ++ `!x'. ((\i. Normal (y (SND (p i))) * indicator_fn ((\(i,j). a i INTER b j) (p i)) t) o p') x' <> NegInf`
             by (RW_TAC std_ss [indicator_fn_def,mul_rzero,mul_rone]
                 ++ METIS_TAC [extreal_not_infty,extreal_of_num_def])
       ++ (MP_TAC o Q.SPEC `((\i. Normal (y (SND ((p :num -> num # num) i))) * indicator_fn ((\(i,j). a i INTER b j) (p i)) t) o p')` o UNDISCH o Q.ISPEC `(s :num -> bool)CROSS(s' :num -> bool)`) EXTREAL_SUM_IMAGE_IN_IF
       ++ RW_TAC std_ss []
       ++ `(\x'.if x' IN s CROSS s' then
                Normal (y (SND x')) * indicator_fn ((\(i,j). a i INTER b j) x') t else 0) =
	   (\x'. (if x' IN s CROSS s' then
		(\x'. Normal (y (SND x')) * indicator_fn ((\(i,j). a i INTER b j) x') t) x'
		 else 0))` by METIS_TAC []
       ++ POP_ORW
       ++ `!x'. (\x'. Normal (y (SND x')) * indicator_fn ((\(i,j). a i INTER b j) x') t) x' <> NegInf`
            by (RW_TAC std_ss [indicator_fn_def,mul_rzero,mul_rone]
                ++ METIS_TAC [extreal_not_infty,extreal_of_num_def])
       ++ (MP_TAC o Q.SPEC `(\x'. Normal (y (SND x')) * indicator_fn ((\(i,j). a i INTER b j) x') t)` o UNDISCH o Q.ISPEC `(s :num -> bool)CROSS(s' :num -> bool)`) (GSYM EXTREAL_SUM_IMAGE_IN_IF)
       ++ RW_TAC std_ss []
       ++ `!x'. NegInf <> (\x:num. SIGMA (\j:num. Normal (y x) * indicator_fn (a j INTER b x) t) s) x'`      
            by (RW_TAC std_ss []
                ++ `!j. (\j. Normal (y x') * indicator_fn (a j INTER b x') t) j <> NegInf`
                     by (RW_TAC std_ss [indicator_fn_def,mul_rzero,mul_rone]
                         ++ METIS_TAC [extreal_of_num_def,extreal_not_infty])
                ++ FULL_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_NOT_INFTY])
       ++ (MP_TAC o Q.SPEC `(\x:num. SIGMA (\j:num. Normal (y x) * indicator_fn (a j INTER b x) t) s)` o UNDISCH o Q.ISPEC `(s' :num -> bool)`) (GSYM EXTREAL_SUM_IMAGE_IN_IF)
       ++ RW_TAC std_ss []
       ++ (MP_TAC o Q.ISPECL [`s':num->bool`,`s:num->bool`]) EXTREAL_SUM_IMAGE_EXTREAL_SUM_IMAGE
       ++ RW_TAC std_ss []
       ++ POP_ASSUM (MP_TAC o Q.SPEC `(\x j. Normal (y x) * indicator_fn (a j INTER b x) t)`)
       ++ `!x. Normal (y x) * indicator_fn (a j INTER b x) t <> NegInf`
             by (RW_TAC std_ss [indicator_fn_def,mul_rzero,mul_rone]
                 ++ METIS_TAC [extreal_of_num_def,extreal_not_infty])
       ++ `!x. Normal (y (FST x)) *
              indicator_fn (a (SND x) INTER b (FST x)) t <> NegInf`
             by (RW_TAC std_ss [indicator_fn_def,mul_rzero,mul_rone]
                 ++ METIS_TAC [extreal_of_num_def,extreal_not_infty])
       ++ RW_TAC std_ss []
       ++  `(s' CROSS s) = IMAGE (\x. (SND x, FST x)) (s CROSS s')`
	by (RW_TAC std_ss [Once EXTENSION, IN_CROSS, IN_IMAGE]
	    ++ (MP_TAC o Q.ISPEC `x':num#num`) pair_CASES
	    ++ RW_TAC std_ss [] ++ RW_TAC std_ss [FST,SND]
	    ++ EQ_TAC
            >> (STRIP_TAC ++ Q.EXISTS_TAC `(r,q)` ++ RW_TAC std_ss [FST,SND])
	    ++ RW_TAC std_ss [] ++ RW_TAC std_ss [])
       ++ POP_ORW
       ++ `INJ (\x. (SND x,FST x)) (s CROSS s')
		(IMAGE (\x. (SND x,FST x)) (s CROSS s'))`
	by (RW_TAC std_ss [INJ_DEF, IN_CROSS, IN_IMAGE]
	    >> METIS_TAC []
	    ++ (MP_TAC o Q.ISPEC `x':num#num`) pair_CASES
	    ++ (MP_TAC o Q.ISPEC `x'':num#num`) pair_CASES
	    ++ RW_TAC std_ss []
	    ++ FULL_SIMP_TAC std_ss [FST,SND])
       ++ (MP_TAC o Q.SPEC `(\x. Normal (y (FST x)) * indicator_fn (a (SND x) INTER b (FST x)) t)` o UNDISCH o Q.SPEC `(\x. (SND x, FST x))` o UNDISCH o 
	   Q.ISPEC `((s:num->bool) CROSS (s':num->bool))` o 
		INST_TYPE [``:'b``|->``:num#num``]) EXTREAL_SUM_IMAGE_IMAGE
       ++ `!x. (\x. Normal (y (FST x)) * indicator_fn (a (SND x) INTER b (FST x)) t) x <> NegInf`
             by (RW_TAC std_ss [indicator_fn_def,mul_rzero,mul_rone]
                 ++ METIS_TAC [extreal_of_num_def,extreal_not_infty])
       ++ RW_TAC std_ss [o_DEF]
       ++ Suff `(\x. Normal (y (SND x)) * indicator_fn (a (FST x) INTER b (SND x)) t) =
		(\x. Normal (y (SND x)) * indicator_fn ((\(i,j). a i INTER b j) x) t)`
       >> RW_TAC std_ss []
       ++ RW_TAC std_ss [FUN_EQ_THM]
       ++ Cases_on `x'`
       ++ RW_TAC std_ss [FST,SND])
   ++ CONJ_TAC
   >> (RW_TAC std_ss [pos_simple_fn_integral_def] ++ FULL_SIMP_TAC std_ss [pos_simple_fn_def]
       ++ (MP_TAC o Q.ISPEC `(\i:num. Normal (x i) * measure m (a i))` o UNDISCH o Q.ISPEC `(s :num -> bool)`) EXTREAL_SUM_IMAGE_IN_IF
       ++ `!x'. x' IN s ==> (\i. Normal (x i) * measure m (a i)) x' <> NegInf`
             by (RW_TAC std_ss []
                 ++ METIS_TAC [positive_not_infty,mul_not_infty,measure_space_def])
       ++ RW_TAC std_ss []
       ++ `(\x'. if x' IN s then Normal (x x') * measure m (a x') else 0) = 
           (\x'. (if x' IN s then (\i. Normal (x i) * measure m (a i)) x' else 0))`
            by METIS_TAC []
       ++ POP_ORW
       ++ `(\x'. (if x' IN s then (\i. Normal (x i) * measure m (a i)) x' else 0)) =
	   (\x'. (if x' IN s then (\i. Normal (x i) * 
		SIGMA (\j. measure m (a i INTER b j)) s') x' else 0))`
	by (RW_TAC std_ss [FUN_EQ_THM]
	    ++ RW_TAC std_ss []
	    ++ FULL_SIMP_TAC std_ss [GSYM AND_IMP_INTRO]
	    ++ (MP_TAC o Q.SPEC `a (x' :num)` o 
		UNDISCH_ALL o REWRITE_RULE [GSYM AND_IMP_INTRO] o 
		Q.SPECL 
		[`s'`, `b`, `m`]) measure_split
	   ++ RW_TAC std_ss [])
       ++ POP_ORW
       ++ `!i. i IN s ==> (Normal (x i) * SIGMA (\j. measure m (a i INTER b j)) s' =
			   SIGMA (\j. Normal (x i) * measure m (a i INTER b j)) s')`
   	   by (RW_TAC std_ss []
               ++ `!j. j IN s' ==> (\j. measure m (a i INTER b j)) j <> NegInf`
                     by METIS_TAC [positive_not_infty,measure_space_def,MEASURE_SPACE_INTER]
	       ++ FULL_SIMP_TAC std_ss [GSYM EXTREAL_SUM_IMAGE_CMUL])
       ++ FULL_SIMP_TAC std_ss []
       ++ `FINITE (s CROSS s')` by RW_TAC std_ss [FINITE_CROSS]
       ++ `INJ p' (s CROSS s')
	   (IMAGE p' (s CROSS s'))`
   	    by METIS_TAC [INJ_IMAGE_BIJ, BIJ_DEF]
       ++ (MP_TAC o Q.SPEC `(\i:num. Normal (x (FST (p i))) * measure m ((\(i:num,j:num). a i INTER b j) (p i)))` o UNDISCH o Q.SPEC `p'` o UNDISCH o Q.SPEC `s CROSS s'` o INST_TYPE [alpha |-> ``:num#num``, beta |-> ``:num``]) EXTREAL_SUM_IMAGE_IMAGE
       ++ `!x'. x' IN IMAGE p' (s CROSS s') ==> Normal (x (FST (p x'))) * measure m ((\(i,j). a i INTER b j) (p x'))  <> NegInf` 
           by (RW_TAC std_ss [] 
               ++ Cases_on `p x'`
	       ++ RW_TAC std_ss []
	       ++ FULL_SIMP_TAC std_ss [IN_IMAGE,IN_CROSS]
	       ++ `q IN s` by METIS_TAC [BIJ_DEF,FST,SND]
	       ++ `r IN s'` by METIS_TAC [BIJ_DEF,FST,SND]
	       ++ METIS_TAC [positive_not_infty,measure_space_def,mul_not_infty,MEASURE_SPACE_INTER])
       ++ RW_TAC std_ss []
       ++ (MP_TAC o Q.SPEC `((\i. Normal (x (FST ((p :num -> num # num) i))) * measure m ((\(i,j). a i INTER b j) (p i))) o p')` o UNDISCH o Q.ISPEC `(s :num -> bool)CROSS(s' :num -> bool)`) EXTREAL_SUM_IMAGE_IN_IF
       ++ `!x'. x' IN s CROSS s' ==> ((\i. Normal (x (FST (p i))) * measure m ((\(i,j). a i INTER b j) (p i))) o p') x' <> NegInf`
            by (RW_TAC std_ss []
                ++ Cases_on `x'`
		++ FULL_SIMP_TAC std_ss [IN_CROSS]
		++ METIS_TAC [positive_not_infty,measure_space_def,mul_not_infty,MEASURE_SPACE_INTER])
       ++ RW_TAC std_ss []
       ++ `(\x'. if x' IN s CROSS s' then
                Normal (x (FST x')) * measure m ((\(i,j). a i INTER b j) x') else 0) =
	   (\x'. (if x' IN s CROSS s' then
		(\x'. Normal (x (FST x')) * measure m ((\(i,j). a i INTER b j) x')) x' else 0))` by METIS_TAC []
       ++ POP_ORW
       ++ (MP_TAC o Q.SPEC `(\x'. Normal (x (FST x')) * measure m ((\(i,j). a i INTER b j) x'))` o UNDISCH o Q.ISPEC `(s :num -> bool)CROSS(s' :num -> bool)`) (GSYM EXTREAL_SUM_IMAGE_IN_IF)
       ++ `!x'. x' IN s CROSS s' ==>
            NegInf <> (\x'. Normal (x (FST x')) * measure m ((\(i,j). a i INTER b j) x')) x'`
             by (RW_TAC std_ss []
                 ++ Cases_on `x'`
		 ++ FULL_SIMP_TAC std_ss [IN_CROSS]
		 ++ METIS_TAC [positive_not_infty,measure_space_def,mul_not_infty,MEASURE_SPACE_INTER])
       ++ RW_TAC std_ss []
       ++ `!x'. x' IN s ==> NegInf <> (\i:num. SIGMA (\j:num. Normal (x i) * measure m (a i INTER b j)) s') x'`
            by (RW_TAC std_ss []
                ++ `!j. j IN s' ==> (\j. Normal (x x') * measure m (a x' INTER b j)) j <> NegInf`
                     by (RW_TAC std_ss []
                         ++ METIS_TAC [positive_not_infty,measure_space_def,mul_not_infty,MEASURE_SPACE_INTER])
                ++ FULL_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_NOT_INFTY])
       ++ (MP_TAC o Q.SPEC `(\i:num. SIGMA (\j:num. Normal (x i) * measure m (a i INTER b j)) s')` o UNDISCH o Q.ISPEC `(s :num -> bool)`) (GSYM EXTREAL_SUM_IMAGE_IN_IF)
       ++ RW_TAC std_ss []
       ++ (MP_TAC o Q.ISPECL [`s:num->bool`,`s':num->bool`]) EXTREAL_SUM_IMAGE_EXTREAL_SUM_IMAGE
       ++ RW_TAC std_ss []
       ++ POP_ASSUM (MP_TAC o Q.SPEC `(\i j. Normal (x i) * measure m (a i INTER b j))`)
       ++ `!x'. x' IN s CROSS s' ==> Normal (x (FST x')) * measure m (a (FST x') INTER b (SND x')) <> NegInf`
             by (RW_TAC std_ss []
		 ++ Cases_on `x'`
		 ++ FULL_SIMP_TAC std_ss [IN_CROSS]
		 ++ METIS_TAC [positive_not_infty,measure_space_def,mul_not_infty,MEASURE_SPACE_INTER])
       ++ RW_TAC std_ss []
       ++ Suff `(\i. Normal (x (FST i)) * measure m (a (FST i) INTER b (SND i))) = 
                (\x'. Normal (x (FST x')) * measure m ((\(i,j). a i INTER b j) x'))`
       >> RW_TAC std_ss []
       ++ RW_TAC std_ss [FUN_EQ_THM]
       ++ Cases_on `x'`
       ++ RW_TAC std_ss [FST,SND])
   ++ CONJ_TAC
   >> (RW_TAC std_ss [pos_simple_fn_integral_def] ++ FULL_SIMP_TAC std_ss [pos_simple_fn_def]
       ++ (MP_TAC o Q.ISPEC `(\i:num. Normal (y i) * measure m (b i))` o UNDISCH o Q.ISPEC `(s' :num -> bool)`) EXTREAL_SUM_IMAGE_IN_IF
       ++ `!x. x IN s' ==> (\i. Normal (y i) * measure m (b i)) x <> NegInf`
             by (RW_TAC std_ss []
                 ++ METIS_TAC [positive_not_infty,mul_not_infty,measure_space_def])
       ++ RW_TAC std_ss []
       ++ `(\x'. if x' IN s' then Normal (y x') * measure m (b x') else 0) = 
           (\x'. (if x' IN s' then (\i. Normal (y i) * measure m (b i)) x' else 0))`
            by METIS_TAC []
       ++ POP_ORW
       ++ `(\x'. (if x' IN s' then (\i. Normal (y i) * measure m (b i)) x' else 0)) =
	   (\x'. (if x' IN s' then (\i. Normal (y i) * 
		SIGMA (\j. measure m (b i INTER a j)) s) x' else 0))`
	by (RW_TAC std_ss [FUN_EQ_THM]
	    ++ RW_TAC std_ss []
	    ++ FULL_SIMP_TAC std_ss [GSYM AND_IMP_INTRO]
	    ++ (MP_TAC o Q.SPEC `b (x' :num)` o 
		UNDISCH_ALL o REWRITE_RULE [GSYM AND_IMP_INTRO] o 
		Q.SPECL 
		[`s`, `a`, `m`]) measure_split
	   ++ RW_TAC std_ss [])
       ++ POP_ORW
       ++ `!i. i IN s' ==> (Normal (y i) * SIGMA (\j. measure m (b i INTER a j)) s =
			   SIGMA (\j. Normal (y i) * measure m (b i INTER a j)) s)`
   	   by (RW_TAC std_ss []
               ++ `!j. j IN s ==> (\j. measure m (b i INTER a j)) j <> NegInf`
                     by METIS_TAC [positive_not_infty,measure_space_def,MEASURE_SPACE_INTER]
	       ++ FULL_SIMP_TAC std_ss [GSYM EXTREAL_SUM_IMAGE_CMUL])
       ++ FULL_SIMP_TAC std_ss []
       ++ `FINITE (s CROSS s')` by RW_TAC std_ss [FINITE_CROSS]
       ++ `INJ p' (s CROSS s')
	   (IMAGE p' (s CROSS s'))`
   	    by METIS_TAC [INJ_IMAGE_BIJ, BIJ_DEF]
       ++ (MP_TAC o Q.SPEC `(\i:num. Normal (y (SND (p i))) * measure m ((\(i:num,j:num). a i INTER b j) (p i)))` o UNDISCH o Q.SPEC `p'` o UNDISCH o Q.SPEC `s CROSS s'` o INST_TYPE [alpha |-> ``:num#num``, beta |-> ``:num``]) EXTREAL_SUM_IMAGE_IMAGE
       ++ `!x'. x' IN IMAGE p' (s CROSS s') ==> Normal (y (SND (p x'))) * measure m ((\(i,j). a i INTER b j) (p x'))  <> NegInf` 
           by (RW_TAC std_ss [] 
               ++ Cases_on `p x'`
	       ++ RW_TAC std_ss []
	       ++ FULL_SIMP_TAC std_ss [IN_IMAGE,IN_CROSS]
	       ++ `q IN s` by METIS_TAC [BIJ_DEF,FST,SND]
	       ++ `r IN s'` by METIS_TAC [BIJ_DEF,FST,SND]
	       ++ METIS_TAC [positive_not_infty,measure_space_def,mul_not_infty,MEASURE_SPACE_INTER])
       ++ RW_TAC std_ss []
       ++ (MP_TAC o Q.SPEC `((\i. Normal (y (SND ((p :num -> num # num) i))) * measure m ((\(i,j). a i INTER b j) (p i))) o p')` o UNDISCH o Q.ISPEC `(s :num -> bool)CROSS(s' :num -> bool)`) EXTREAL_SUM_IMAGE_IN_IF
       ++ `!x'. x' IN s CROSS s' ==> ((\i. Normal (y (SND (p i))) * measure m ((\(i,j). a i INTER b j) (p i))) o p') x' <> NegInf`
            by (RW_TAC std_ss []
                ++ Cases_on `x'`
		++ FULL_SIMP_TAC std_ss [IN_CROSS]
		++ METIS_TAC [positive_not_infty,measure_space_def,mul_not_infty,MEASURE_SPACE_INTER])
       ++ RW_TAC std_ss []
       ++ `(\x'. if x' IN s CROSS s' then
                Normal (y (SND x')) * measure m ((\(i,j). a i INTER b j) x') else 0) =
	   (\x'. (if x' IN s CROSS s' then
		(\x'. Normal (y (SND x')) * measure m ((\(i,j). a i INTER b j) x')) x' else 0))` by METIS_TAC []
       ++ POP_ORW
       ++ (MP_TAC o Q.SPEC `(\x'. Normal (y (SND x')) * measure m ((\(i,j). a i INTER b j) x'))` o UNDISCH o Q.ISPEC `(s :num -> bool)CROSS(s' :num -> bool)`) (GSYM EXTREAL_SUM_IMAGE_IN_IF)
       ++ `!x'. x' IN s CROSS s' ==>
            NegInf <> (\x'. Normal (y (SND x')) * measure m ((\(i,j). a i INTER b j) x')) x'`
             by (RW_TAC std_ss []
                 ++ Cases_on `x'`
		 ++ FULL_SIMP_TAC std_ss [IN_CROSS]
		 ++ METIS_TAC [positive_not_infty,measure_space_def,mul_not_infty,MEASURE_SPACE_INTER])
       ++ RW_TAC std_ss []
       ++ `!x'. x' IN s' ==> NegInf <> (\i:num. SIGMA (\j:num. Normal (y i) * measure m (b i INTER a j)) s) x'`
            by (RW_TAC std_ss []
                ++ `!j. j IN s ==> (\j. Normal (y x') * measure m (b x' INTER a j)) j <> NegInf`
                     by (RW_TAC std_ss []
                         ++ METIS_TAC [positive_not_infty,measure_space_def,mul_not_infty,MEASURE_SPACE_INTER])
                ++ FULL_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_NOT_INFTY])
       ++ (MP_TAC o Q.SPEC `(\i:num. SIGMA (\j:num. Normal (y i) * measure m (b i INTER a j)) s)` o UNDISCH o Q.ISPEC `(s' :num -> bool)`) (GSYM EXTREAL_SUM_IMAGE_IN_IF)
       ++ RW_TAC std_ss []
       ++ (MP_TAC o Q.ISPECL [`s':num->bool`,`s:num->bool`]) EXTREAL_SUM_IMAGE_EXTREAL_SUM_IMAGE
       ++ RW_TAC std_ss []
       ++ POP_ASSUM (MP_TAC o Q.SPEC `(\i j. Normal (y i) * measure m (b i INTER a j))`)
       ++ `!x'. x' IN s' CROSS s ==> Normal (y (FST x')) * measure m (b (FST x') INTER a (SND x')) <> NegInf`
             by (RW_TAC std_ss []
		 ++ Cases_on `x'`
		 ++ FULL_SIMP_TAC std_ss [IN_CROSS]
		 ++ METIS_TAC [positive_not_infty,measure_space_def,mul_not_infty,MEASURE_SPACE_INTER])
       ++ RW_TAC std_ss [o_DEF]
       ++  `(s' CROSS s) = IMAGE (\x. (SND x, FST x)) (s CROSS s')`
	by (RW_TAC std_ss [Once EXTENSION, IN_CROSS, IN_IMAGE]
	    ++ (MP_TAC o Q.ISPEC `x':num#num`) pair_CASES
	    ++ RW_TAC std_ss [] ++ RW_TAC std_ss [FST,SND]
	    ++ EQ_TAC
            >> (STRIP_TAC ++ Q.EXISTS_TAC `(r,q)` ++ RW_TAC std_ss [FST,SND])
	    ++ RW_TAC std_ss [] ++ RW_TAC std_ss [])
       ++ POP_ORW
       ++ `INJ (\x. (SND x,FST x)) (s CROSS s')
		(IMAGE (\x. (SND x,FST x)) (s CROSS s'))`
	by (RW_TAC std_ss [INJ_DEF, IN_CROSS, IN_IMAGE]
	    >> METIS_TAC []
	    ++ (MP_TAC o Q.ISPEC `x':num#num`) pair_CASES
	    ++ (MP_TAC o Q.ISPEC `x'':num#num`) pair_CASES
	    ++ RW_TAC std_ss []
	    ++ FULL_SIMP_TAC std_ss [FST,SND])
       ++ (MP_TAC o Q.SPEC `(\x. Normal (y (FST x)) * measure m (a (SND x) INTER b (FST x)))` o UNDISCH o Q.SPEC `(\x. (SND x, FST x))` o UNDISCH o 
	   Q.ISPEC `((s:num->bool) CROSS (s':num->bool))` o 
		INST_TYPE [``:'b``|->``:num#num``]) EXTREAL_SUM_IMAGE_IMAGE
       ++ `!x. x IN IMAGE (\x. (SND x,FST x)) (s CROSS s') ==>
              (\x. Normal (y (FST x)) * measure m (a (SND x) INTER b (FST x))) x <> NegInf`
              by (RW_TAC std_ss []
	          ++ Cases_on `x'`
		  ++ FULL_SIMP_TAC std_ss [IN_CROSS,IN_IMAGE]
		  ++ METIS_TAC [positive_not_infty,measure_space_def,mul_not_infty,MEASURE_SPACE_INTER])
       ++ RW_TAC std_ss [o_DEF,INTER_COMM]
       ++ Suff `(\x. Normal (y (SND x)) * measure m (a (FST x) INTER b (SND x))) =
		(\x. Normal (y (SND x)) * measure m ((\(i,j). a i INTER b j) x))`
       >> RW_TAC std_ss []
       ++ RW_TAC std_ss [FUN_EQ_THM]
       ++ Cases_on `x'`
       ++ RW_TAC std_ss [FST,SND])
   ++ CONJ_TAC
   >> FULL_SIMP_TAC std_ss [IMAGE_FINITE, FINITE_CROSS, pos_simple_fn_def]
   ++ CONJ_TAC
   >> (RW_TAC std_ss [IN_IMAGE]
       ++ FULL_SIMP_TAC std_ss [o_DEF]
       ++ (MP_TAC o Q.ISPEC `x':num#num`) pair_CASES
       ++ (MP_TAC o Q.ISPEC `x'':num#num`) pair_CASES
       ++ RW_TAC std_ss []
       ++ RW_TAC std_ss []
       ++ METIS_TAC [IN_CROSS,pos_simple_fn_def,FST])
   ++ CONJ_TAC
   >> (RW_TAC std_ss [IN_IMAGE]
       ++ FULL_SIMP_TAC std_ss [o_DEF]
       ++ (MP_TAC o Q.ISPEC `x':num#num`) pair_CASES
       ++ (MP_TAC o Q.ISPEC `x'':num#num`) pair_CASES
       ++ RW_TAC std_ss []
       ++ RW_TAC std_ss []
       ++ METIS_TAC [IN_CROSS,pos_simple_fn_def,SND])
   ++ CONJ_TAC
   >> (RW_TAC std_ss [IN_DISJOINT, IN_IMAGE,EXTENSION, NOT_IN_EMPTY, IN_INTER]
       ++ FULL_SIMP_TAC std_ss [o_DEF]
       ++ (MP_TAC o Q.ISPEC `x':num#num`) pair_CASES
       ++ (MP_TAC o Q.ISPEC `x'':num#num`) pair_CASES
       ++ RW_TAC std_ss []
       ++ RW_TAC std_ss []
       ++ SPOSE_NOT_THEN STRIP_ASSUME_TAC
       ++ FULL_SIMP_TAC std_ss [IN_INTER, IN_CROSS, FST, SND, pos_simple_fn_def,
				DISJOINT_DEF]
       ++ METIS_TAC [EXTENSION, NOT_IN_EMPTY, IN_INTER])
   ++ CONJ_TAC
   >> (RW_TAC std_ss [IN_IMAGE]
       ++ FULL_SIMP_TAC std_ss [o_DEF]
       ++ (MP_TAC o Q.ISPEC `x':num#num`) pair_CASES
       ++ RW_TAC std_ss []
       ++ FULL_SIMP_TAC std_ss [IN_CROSS, FST, SND, pos_simple_fn_def]
       ++ METIS_TAC [ALGEBRA_INTER, subsets_def, space_def, 
		     sigma_algebra_def, measure_space_def])
   ++ RW_TAC std_ss [Once EXTENSION, IN_BIGUNION, IN_IMAGE, IN_CROSS]
   ++ `!s'' x. (?x'. ((x = p' x') /\ FST x' IN s /\ SND x' IN s')) =
	   (?x1 x2. ((x = p' (x1,x2)) /\ x1 IN s /\ x2 IN s'))`
	by METIS_TAC [PAIR, FST, SND]
   ++ POP_ORW
   ++ `!s''. (?x. (s'' = (\(i,j). a i INTER b j) (p x)) /\
		  ?x1 x2. (x = p' (x1,x2)) /\ x1 IN s /\ x2 IN s') =
		 (?x1 x2. (s'' = (\(i,j). a i INTER b j) (p (p' (x1,x2)))) /\
			  x1 IN s /\ x2 IN s')`
	by METIS_TAC []
   ++ POP_ORW
   ++ FULL_SIMP_TAC std_ss [o_DEF, IN_CROSS]
   ++ `!s''. (?x1 x2. (s'' = (\(i,j). a i INTER b j) (p (p' (x1,x2)))) /\ 
		  x1 IN s /\ x2 IN s') =
		 (?x1 x2. (s'' = (\(i,j). a i INTER b j) (x1,x2)) /\ 
		  x1 IN s /\ x2 IN s')`
	by METIS_TAC [FST,SND]
   ++ POP_ORW
   ++ RW_TAC std_ss []
   ++ Suff `(?x1 x2. x' IN a x1 INTER b x2 /\ x1 IN s /\ x2 IN s') =
		x' IN m_space m`
   >> METIS_TAC []
   ++ RW_TAC std_ss [IN_INTER]
   ++ FULL_SIMP_TAC std_ss [pos_simple_fn_def]
   ++ `m_space m = (BIGUNION (IMAGE a s)) INTER (BIGUNION (IMAGE b s'))` 
		by METIS_TAC [INTER_IDEMPOT]
   ++ POP_ORW
   ++ Q.PAT_X_ASSUM `BIGUNION (IMAGE b s') = m_space m` (K ALL_TAC)
   ++ Q.PAT_X_ASSUM `BIGUNION (IMAGE a s) = m_space m` (K ALL_TAC)
   ++ RW_TAC std_ss [IN_INTER, IN_BIGUNION, IN_IMAGE]
   ++ METIS_TAC []);

val psfis_present = store_thm
  ("psfis_present",
   ``!m f g a b.
	measure_space m /\
	a IN psfis m f /\ b IN psfis m g ==>
	(?z z' c (k:num->bool).
		(!t. t IN m_space m ==> (f t = SIGMA (\i. Normal (z i) * (indicator_fn (c i) t)) k)) /\
		(!t. t IN m_space m ==> (g t = SIGMA (\i. Normal (z' i) * (indicator_fn (c i) t)) k)) /\
		(a = pos_simple_fn_integral m k c z) /\
		(b = pos_simple_fn_integral m k c z') /\
		FINITE k /\ (!i. i IN k ==> 0 <= z i) /\ (!i. i IN k ==> 0 <= z' i) /\
		(!i j. i IN k /\ j IN k /\ (~(i=j)) ==> DISJOINT (c i) (c j)) /\
		(!i. i IN k ==> c i IN measurable_sets m) /\
		(BIGUNION (IMAGE c k) = m_space m))``,
   RW_TAC std_ss [psfis_def, IN_IMAGE, psfs_def, GSPECIFICATION]
   ++ Cases_on `x'` ++ Cases_on `x` ++ Cases_on `x''` ++ Cases_on `x'''`
   ++ Cases_on `r'` ++ Cases_on `r` ++ Cases_on `r''` ++ Cases_on `r'''`
   ++ RW_TAC std_ss []
   ++ FULL_SIMP_TAC std_ss [PAIR_EQ]
   ++  MATCH_MP_TAC pos_simple_fn_integral_present
   ++ METIS_TAC []);

(* ------------------------------------------------------ *)
(*        Properties of POSTIVE SIMPLE FUNCTIONS          *)
(* ------------------------------------------------------ *)

val pos_simple_fn_thm1 = store_thm
 ("pos_simple_fn_thm1",``!m f s a x i y. measure_space m /\ pos_simple_fn m f s a x /\
			i IN s /\ y IN a i ==> (f y = Normal (x i))``,
  RW_TAC std_ss [pos_simple_fn_def]
  ++ `y IN m_space m` by METIS_TAC [MEASURE_SPACE_SUBSET_MSPACE,SUBSET_DEF]
  ++ `FINITE (s DELETE i)` by RW_TAC std_ss [FINITE_DELETE]
  ++ (MP_TAC o Q.SPEC `i` o UNDISCH o Q.SPECL [`(\i. Normal (x i) * indicator_fn (a i) y)`,`s DELETE i`]) (INST_TYPE [alpha |-> ``:num``] EXTREAL_SUM_IMAGE_PROPERTY)
  ++ `!x'. (\i. Normal (x i) * indicator_fn (a i) y) x' <> NegInf`
        by (RW_TAC std_ss [indicator_fn_def,mul_rone,mul_rzero] ++ RW_TAC std_ss [extreal_of_num_def,extreal_not_infty])
  ++ RW_TAC std_ss [INSERT_DELETE,DELETE_DELETE]
  ++ `!j. j IN (s DELETE i) ==> ~(y IN a j)` 
	    by (RW_TAC std_ss [IN_DELETE]
		++ `DISJOINT (a i) (a j)` by METIS_TAC []
		++ FULL_SIMP_TAC std_ss [DISJOINT_DEF,INTER_DEF,EXTENSION,GSPECIFICATION,NOT_IN_EMPTY]
		++ METIS_TAC [])
  ++ (MP_TAC o Q.ISPEC `(\i:num. Normal (x i) * indicator_fn (a i) y)` o UNDISCH o Q.SPEC `s DELETE i`) EXTREAL_SUM_IMAGE_IN_IF
  ++ `!x'. (\i. Normal (x i) * indicator_fn (a i) y) x' <> NegInf`
        by (RW_TAC std_ss [indicator_fn_def,mul_rone,mul_rzero] ++ RW_TAC std_ss [extreal_of_num_def,extreal_not_infty])
  ++ RW_TAC std_ss []
  ++ `!j. j IN s DELETE i ==> (indicator_fn (a j) y = 0)` by RW_TAC std_ss [indicator_fn_def,mul_rone,mul_rzero]
  ++ RW_TAC std_ss [mul_rzero,EXTREAL_SUM_IMAGE_ZERO,add_rzero,indicator_fn_def,mul_rone]);

val pos_simple_fn_le = store_thm
  ("pos_simple_fn_le",``!m f g s a x x' i. measure_space m /\ pos_simple_fn m f s a x /\ pos_simple_fn m g s a x' /\
                        (!x. x IN m_space m ==> g x <= f x) /\ 
 			(i IN s) /\ ~(a i = {}) ==> (Normal (x' i) <= Normal (x i))``,
  RW_TAC std_ss []
  ++ `!t. t IN a i ==> (f t = Normal (x i))` by METIS_TAC [pos_simple_fn_thm1]
  ++ `!t. t IN a i ==> (g t = Normal (x' i))` by METIS_TAC [pos_simple_fn_thm1]
  ++ METIS_TAC [CHOICE_DEF,pos_simple_fn_def,MEASURE_SPACE_SUBSET_MSPACE,SUBSET_DEF]);

val pos_simple_fn_cmul = store_thm
 ("pos_simple_fn_cmul", ``!m f z. measure_space m /\ pos_simple_fn m f s a x /\ 0 <= z ==> (?s' a' x'. pos_simple_fn m (\t. Normal z * f t) s' a' x')``,
  RW_TAC std_ss [pos_simple_fn_def] 
  ++ Q.EXISTS_TAC `s` ++ Q.EXISTS_TAC `a` ++ Q.EXISTS_TAC `(\i. z * (x i))`
  ++ RW_TAC std_ss [REAL_LE_MUL,GSYM extreal_mul_def]
  >> METIS_TAC [extreal_le_def,extreal_of_num_def,le_mul]
  ++ (MP_TAC o Q.SPECL [`(\i. Normal (x i) * indicator_fn (a i) t)`,`z`] o UNDISCH o Q.ISPEC `s:num->bool`) EXTREAL_SUM_IMAGE_CMUL
  ++ `!x'. (\i. Normal (x i) * indicator_fn (a i) t) x' <> NegInf`
        by (RW_TAC std_ss [indicator_fn_def,mul_rone,mul_rzero] ++ RW_TAC std_ss [extreal_of_num_def,extreal_not_infty])
  ++ FULL_SIMP_TAC std_ss [mul_assoc]);

val pos_simple_fn_cmul_alt = store_thm
("pos_simple_fn_cmul_alt", ``!m f s a x z. measure_space m /\ 0 <= z /\ pos_simple_fn m f s a x ==> pos_simple_fn m (\t. Normal z * f t) s a (\i. z * x i)``,
  RW_TAC std_ss [pos_simple_fn_def,REAL_LE_MUL,GSYM extreal_mul_def]
  >> METIS_TAC [extreal_le_def,extreal_of_num_def,le_mul]
  ++ (MP_TAC o Q.SPECL [`(\i. Normal (x i) * indicator_fn (a i) t)`,`z`] o UNDISCH o Q.ISPEC `s:num->bool`) EXTREAL_SUM_IMAGE_CMUL
  ++ `!x'. (\i. Normal (x i) * indicator_fn (a i) t) x' <> NegInf`
        by (RW_TAC std_ss [indicator_fn_def,mul_rone,mul_rzero] ++ RW_TAC std_ss [extreal_of_num_def,extreal_not_infty])
  ++ FULL_SIMP_TAC std_ss [mul_assoc]);

val pos_simple_fn_add = store_thm
 ("pos_simple_fn_add",``!m f g. measure_space m /\ pos_simple_fn m f s a x /\ pos_simple_fn m g s' a' x' ==> (?s'' a'' x''. pos_simple_fn m (\t. f t + g t) s'' a'' x'') ``,
  REPEAT STRIP_TAC 
  ++ (MP_TAC o Q.SPECL [`m`,`f`,`s`,`a`,`x`,`g`,`s'`,`a'`,`x'`]) pos_simple_fn_integral_present 
  ++ RW_TAC std_ss [] 
  ++ Q.EXISTS_TAC `k` 
  ++ Q.EXISTS_TAC `c` ++ Q.EXISTS_TAC `(\i. z i + z' i)`
  ++ RW_TAC std_ss [pos_simple_fn_def,REAL_LE_ADD,GSYM extreal_add_def]
  >> METIS_TAC [le_add,pos_simple_fn_def]
  ++ `!i. i IN k ==> Normal (z i) <> NegInf /\ Normal (z' i) <> NegInf /\ 0 <= Normal (z i) /\ 0 <= Normal (z' i)`
         by METIS_TAC [extreal_not_infty,extreal_of_num_def,extreal_le_def]
  ++ `!i. i IN k ==> (\i. (Normal (z i) + Normal (z' i)) * indicator_fn (c i) t) i <> NegInf`
         by METIS_TAC [extreal_add_def,indicator_fn_def,mul_rzero,mul_rone,extreal_of_num_def,extreal_not_infty]
  ++ (MP_TAC o Q.SPEC `(\i:num. (Normal (z i) + Normal (z' i)) *  indicator_fn (c i) t)` o UNDISCH o Q.ISPEC `k:num->bool`) EXTREAL_SUM_IMAGE_IN_IF
  ++ RW_TAC std_ss [add_rdistrib]
  ++ (MP_TAC o Q.SPEC `(\x. Normal (z x) * indicator_fn (c x) t + Normal (z' x) * indicator_fn (c x) t)` o UNDISCH o Q.ISPEC `k:num->bool` o GSYM) EXTREAL_SUM_IMAGE_IN_IF
  ++ `!x. x IN k ==>  NegInf <>
       (\x. Normal (z x) * indicator_fn (c x) t + Normal (z' x) * indicator_fn (c x) t) x`
        by (RW_TAC std_ss [extreal_add_def,indicator_fn_def,mul_rzero,mul_rone,add_rzero]
            ++ METIS_TAC [extreal_of_num_def,extreal_not_infty])
  ++ RW_TAC std_ss []
  ++ `(\x. Normal (z x) * indicator_fn (c x) t + Normal (z' x) * indicator_fn (c x) t) = 
      (\x. (\x. Normal (z x) * indicator_fn (c x) t) x + (\x. Normal (z' x) * indicator_fn (c x) t) x)`
           by METIS_TAC []
  ++ POP_ORW
  ++ (MP_TAC o Q.SPECL [`(\x:num. Normal (z x) * indicator_fn (c x) t)`,`(\x:num. Normal (z' x) * indicator_fn (c x) t)`] o UNDISCH o Q.ISPEC `k:num->bool` o GSYM) EXTREAL_SUM_IMAGE_ADD
  ++ `!x:num. x IN k ==> NegInf <> (\x:num. Normal (z x) * indicator_fn (c x) t) x /\
                         NegInf <> (\x:num. Normal (z' x) * indicator_fn (c x) t) x`
        by (RW_TAC std_ss [indicator_fn_def,mul_rone,mul_rzero,add_rzero]
            ++ METIS_TAC [extreal_of_num_def,extreal_not_infty])
  ++ METIS_TAC []);

val pos_simple_fn_add_alt = store_thm
 ("pos_simple_fn_add_alt",``!m f g s a x y. measure_space m /\ pos_simple_fn m f s a x /\ pos_simple_fn m g s a y ==> pos_simple_fn m (\t. f t + g t) s a (\i. x i + y i)``,

  RW_TAC std_ss [pos_simple_fn_def,REAL_LE_ADD,GSYM extreal_add_def,le_add]
  ++ `!i. i IN s ==> Normal (x i) <> NegInf /\ Normal (y i) <> NegInf /\ 0 <= Normal (x i) /\ 0 <= Normal (y i)`
         by METIS_TAC [extreal_not_infty,extreal_of_num_def,extreal_le_def]
  ++ `!i. i IN s ==> (\i. (Normal (x i) + Normal (y i)) * indicator_fn (a i) t) i <> NegInf`
         by METIS_TAC [extreal_add_def,indicator_fn_def,mul_rzero,mul_rone,extreal_of_num_def,extreal_not_infty]
  ++ (MP_TAC o Q.SPEC `(\i:num. (Normal (x i) + Normal (y i)) *  indicator_fn (a i) t)` o UNDISCH o Q.ISPEC `s:num->bool`) EXTREAL_SUM_IMAGE_IN_IF
  ++ RW_TAC std_ss [add_rdistrib]
  ++ (MP_TAC o Q.SPEC `(\i. Normal (x i) * indicator_fn (a i) t + Normal (y i) * indicator_fn (a i) t)` o UNDISCH o Q.ISPEC `s:num->bool` o GSYM) EXTREAL_SUM_IMAGE_IN_IF
  ++ `!i. i IN s ==>  NegInf <>
       (\i. Normal (x i) * indicator_fn (a i) t + Normal (y i) * indicator_fn (a i) t) i`
        by (RW_TAC std_ss [extreal_add_def,indicator_fn_def,mul_rzero,mul_rone,add_rzero]
            ++ METIS_TAC [extreal_of_num_def,extreal_not_infty])
  ++ RW_TAC std_ss []
  ++ `(\i. Normal (x i) * indicator_fn (a i) t + Normal (y i) * indicator_fn (a i) t) = 
      (\i. (\i. Normal (x i) * indicator_fn (a i) t) i + (\i. Normal (y i) * indicator_fn (a i) t) i)`
           by METIS_TAC []
  ++ POP_ORW
  ++ (MP_TAC o Q.SPECL [`(\i:num. Normal (x i) * indicator_fn (a i) t)`,`(\i:num. Normal (y i) * indicator_fn (a i) t)`] o UNDISCH o Q.ISPEC `s:num->bool` o GSYM) EXTREAL_SUM_IMAGE_ADD
  ++ `!i:num. i IN s ==> NegInf <> (\i:num. Normal (x i) * indicator_fn (a i) t) i /\
                         NegInf <> (\i:num. Normal (y i) * indicator_fn (a i) t) i`
        by (RW_TAC std_ss [indicator_fn_def,mul_rone,mul_rzero,add_rzero]
            ++ METIS_TAC [extreal_of_num_def,extreal_not_infty])
  ++ METIS_TAC []);

val pos_simple_fn_indicator = store_thm
("pos_simple_fn_indicator",``!m A. measure_space m /\ A IN measurable_sets m ==> ?s a x. pos_simple_fn m (indicator_fn A) s a x``,
 RW_TAC real_ss []
 ++ `FINITE {0:num;1:num}` by METIS_TAC [FINITE_INSERT,FINITE_SING]
 ++ Q.EXISTS_TAC `{0:num;1:num}`  ++ Q.EXISTS_TAC `(\i. if i = 0 then (m_space m DIFF A) else A)` ++ Q.EXISTS_TAC `(\i. if i = 0 then 0 else 1)`
 ++ RW_TAC real_ss [pos_simple_fn_def,indicator_fn_def,FINITE_SING,IN_SING,MEASURE_SPACE_MSPACE_MEASURABLE]
 << [METIS_TAC [le_01,le_refl],
     `FINITE {1:num}` by METIS_TAC [FINITE_SING]
     ++ `{1:num} DELETE 0 = {1}` by (RW_TAC real_ss [DELETE_DEF,DIFF_DEF,IN_SING] ++ RW_TAC real_ss [EXTENSION,IN_SING] ++ RW_TAC real_ss [GSPECIFICATION] ++ EQ_TAC >> RW_TAC real_ss [] ++ RW_TAC real_ss [])
     ++ (MP_TAC o Q.SPEC `0` o UNDISCH o Q.ISPECL [`(\i:num. Normal (if i = 0 then 0 else 1) * if t IN if i = 0 then m_space m DIFF A else A then 1 else 0)`, `{1:num}`]) EXTREAL_SUM_IMAGE_PROPERTY
     ++ `!x. (\i:num. Normal (if i = 0 then 0 else 1) * if t IN if i = 0 then m_space m DIFF A else A then 1 else 0) x <> NegInf`
           by (RW_TAC std_ss [mul_rone,mul_rzero] ++ RW_TAC std_ss [extreal_of_num_def,extreal_not_infty])
     ++ RW_TAC real_ss [EXTREAL_SUM_IMAGE_SING,extreal_of_num_def,extreal_mul_def,extreal_add_def],
     METIS_TAC [MEASURE_SPACE_DIFF,MEASURE_SPACE_MSPACE_MEASURABLE],
     RW_TAC real_ss [],
     FULL_SIMP_TAC std_ss [DISJOINT_DEF,EXTENSION,GSPECIFICATION,IN_INTER,IN_DIFF,NOT_IN_EMPTY,IN_INSERT,IN_SING]
     ++ METIS_TAC [],
     RW_TAC std_ss [IMAGE_DEF]
     ++ `{if i:num = 0 then m_space m DIFF A else A | i IN {0; 1}} = {m_space m DIFF A ; A}`
  	     by (RW_TAC std_ss [EXTENSION,GSPECIFICATION,IN_INSERT,IN_SING]
  		 ++ EQ_TAC >> METIS_TAC []
                 ++ RW_TAC std_ss [] >> METIS_TAC []
		 ++ Q.EXISTS_TAC `1:num`
                 ++ RW_TAC real_ss [])
     ++ RW_TAC std_ss [BIGUNION_INSERT,BIGUNION_SING]
     ++ METIS_TAC [UNION_DIFF,MEASURE_SPACE_SUBSET_MSPACE]]);

val pos_simple_fn_indicator_alt = store_thm
("pos_simple_fn_indicator_alt",``!m s. measure_space m /\ s IN measurable_sets m ==> 
   pos_simple_fn m (indicator_fn s) {0:num;1:num} (\i:num. if i = 0 then (m_space m DIFF s) else s) (\i. if i = 0 then 0 else 1)``,
  RW_TAC std_ss []
  ++ `FINITE {0:num;1:num}` by METIS_TAC [FINITE_INSERT,FINITE_SING]
  ++ RW_TAC real_ss [pos_simple_fn_def,indicator_fn_def,FINITE_SING,IN_SING,MEASURE_SPACE_MSPACE_MEASURABLE]
  << [METIS_TAC [le_01,le_refl],
      `FINITE {1:num}` by METIS_TAC [FINITE_SING]
     ++ `{1:num} DELETE 0 = {1}` by (RW_TAC real_ss [DELETE_DEF,DIFF_DEF,IN_SING] ++ RW_TAC real_ss [EXTENSION,IN_SING] ++ RW_TAC real_ss [GSPECIFICATION] ++ EQ_TAC >> RW_TAC real_ss [] ++ RW_TAC real_ss [])
     ++ (MP_TAC o Q.SPEC `0` o UNDISCH o Q.ISPECL [`(\i:num. Normal (if i = 0 then 0 else 1) * if t IN if i = 0 then m_space m DIFF s else s then 1 else 0)`, `{1:num}`]) EXTREAL_SUM_IMAGE_PROPERTY
     ++ `!x. (\i:num. Normal (if i = 0 then 0 else 1) * if t IN if i = 0 then m_space m DIFF s else s then 1 else 0) x <> NegInf`
           by (RW_TAC std_ss [mul_rone,mul_rzero] ++ RW_TAC std_ss [extreal_of_num_def,extreal_not_infty])
     ++ RW_TAC real_ss [EXTREAL_SUM_IMAGE_SING,extreal_of_num_def,extreal_mul_def,extreal_add_def],
     METIS_TAC [MEASURE_SPACE_DIFF,MEASURE_SPACE_MSPACE_MEASURABLE],
     RW_TAC real_ss [],
     FULL_SIMP_TAC std_ss [DISJOINT_DEF,EXTENSION,GSPECIFICATION,IN_INTER,IN_DIFF,NOT_IN_EMPTY,IN_INSERT,IN_SING]
     ++ METIS_TAC [],
     RW_TAC std_ss [IMAGE_DEF]
     ++ `{if i:num = 0 then m_space m DIFF s else s | i IN {0; 1}} = {m_space m DIFF s ; s}`
  	     by (RW_TAC std_ss [EXTENSION,GSPECIFICATION,IN_INSERT,IN_SING]
  		 ++ EQ_TAC >> METIS_TAC []
                 ++ RW_TAC std_ss [] >> METIS_TAC []
		 ++ Q.EXISTS_TAC `1:num`
                 ++ RW_TAC real_ss [])
     ++ RW_TAC std_ss [BIGUNION_INSERT,BIGUNION_SING]
     ++ METIS_TAC [UNION_DIFF,MEASURE_SPACE_SUBSET_MSPACE]]);

val pos_simple_fn_max = store_thm
("pos_simple_fn_max",``!m f (s:num->bool) a x g (s':num->bool) b y.
	measure_space m /\ pos_simple_fn m f s a x /\ pos_simple_fn m g s' b y ==>
	?s'' a'' x''. pos_simple_fn m (\x. max (f x) (g x)) s'' a'' x''``,
  RW_TAC std_ss []
  ++ `?p n. BIJ p (count n) (s CROSS s')`	by FULL_SIMP_TAC std_ss [GSYM FINITE_BIJ_COUNT, pos_simple_fn_def, FINITE_CROSS]
  ++ `?p'. BIJ p' (s CROSS s') (count n) /\ (!x. x IN (count n) ==> ((p' o p) x = x)) /\ (!x. x IN (s CROSS s') ==> ((p o p') x = x))` by (MATCH_MP_TAC BIJ_INV ++ RW_TAC std_ss [])
  ++ Q.EXISTS_TAC `IMAGE p' (s CROSS s')`
  ++ Q.EXISTS_TAC `(\(i,j). a i INTER b j) o p`
  ++ Q.EXISTS_TAC `(\n. max ((x o FST o p) n) ((y o SND o p)n))`
  ++ RW_TAC std_ss [FUN_EQ_THM] 
  ++ FULL_SIMP_TAC std_ss [pos_simple_fn_def,extreal_max_def]
  ++ `!i j. i IN IMAGE p' (s CROSS s') /\ j IN IMAGE p' (s CROSS s') /\ i <> j ==> DISJOINT (((\(i,j). a i INTER b j) o p) i) (((\(i,j). a i INTER b j) o p) j)`
    by (RW_TAC std_ss [DISJOINT_DEF, IN_IMAGE]
	++ RW_TAC std_ss [Once EXTENSION, NOT_IN_EMPTY, IN_INTER]
	++ FULL_SIMP_TAC std_ss [o_DEF]
        ++ (MP_TAC o Q.ISPEC `x':num#num`) pair_CASES
        ++ (MP_TAC o Q.ISPEC `x'':num#num`) pair_CASES
        ++ RW_TAC std_ss []
        ++ RW_TAC std_ss []
        ++ SPOSE_NOT_THEN STRIP_ASSUME_TAC
	++ FULL_SIMP_TAC std_ss [IN_INTER, IN_CROSS, FST, SND, pos_simple_fn_def,DISJOINT_DEF]
        ++ METIS_TAC [EXTENSION, NOT_IN_EMPTY, IN_INTER])
  ++ `!i. i IN IMAGE p' (s CROSS s') ==>  ((\(i,j). a i INTER b j) o p) i IN measurable_sets m`
    by (RW_TAC std_ss [IN_IMAGE]
        ++ FULL_SIMP_TAC std_ss [o_DEF]
        ++ (MP_TAC o Q.ISPEC `x':num#num`) pair_CASES
       	++ RW_TAC std_ss []
	++ FULL_SIMP_TAC std_ss [IN_CROSS, FST, SND, pos_simple_fn_def]
        ++ METIS_TAC [ALGEBRA_INTER, subsets_def, space_def,sigma_algebra_def, measure_space_def])
  ++ `BIGUNION (IMAGE ((\(i,j). a i INTER b j) o p) (IMAGE p' (s CROSS s'))) =  m_space m`
     by (RW_TAC std_ss [Once EXTENSION, IN_BIGUNION, IN_IMAGE, IN_CROSS]
	++ `!s'' x. (?x'. ((x = p' x') /\ FST x' IN s /\ SND x' IN s')) = (?x1 x2. ((x = p' (x1,x2)) /\ x1 IN s /\ x2 IN s'))` 
            by METIS_TAC [PAIR, FST, SND]
	++ POP_ORW
        ++ `!s''. (?x. (s'' = (\(i,j). a i INTER b j) (p x)) /\ ?x1 x2. (x = p' (x1,x2)) /\ x1 IN s /\ x2 IN s') = 
                  (?x1 x2. (s'' = (\(i,j). a i INTER b j) (p (p' (x1,x2)))) /\  x1 IN s /\ x2 IN s')` 
            by METIS_TAC []
        ++ POP_ORW
        ++ FULL_SIMP_TAC std_ss [o_DEF, IN_CROSS]
        ++ `!s''. (?x1 x2. (s'' = (\(i,j). a i INTER b j) (p (p' (x1,x2)))) /\  x1 IN s /\ x2 IN s') = (?x1 x2. (s'' = (\(i,j). a i INTER b j) (x1,x2)) /\ x1 IN s /\ x2 IN s')` by METIS_TAC [FST,SND]
        ++ POP_ORW
       	++ RW_TAC std_ss []
        ++ Suff `(?x1 x2. x' IN a x1 INTER b x2 /\ x1 IN s /\ x2 IN s') = x' IN m_space m`
        >> METIS_TAC []
       	++ RW_TAC std_ss [IN_INTER]
        ++ FULL_SIMP_TAC std_ss [pos_simple_fn_def]
       	++ `m_space m = (BIGUNION (IMAGE a s)) INTER (BIGUNION (IMAGE b s'))` by METIS_TAC [INTER_IDEMPOT]
        ++ POP_ORW
       	++ Q.PAT_X_ASSUM `BIGUNION (IMAGE b s') = m_space m` (K ALL_TAC)
 	++ Q.PAT_X_ASSUM `BIGUNION (IMAGE a s) = m_space m` (K ALL_TAC)
	++ RW_TAC std_ss [IN_INTER, IN_BIGUNION, IN_IMAGE]
	++ METIS_TAC [])
  ++ `FINITE (s CROSS s')` by RW_TAC std_ss [FINITE_CROSS]
  ++ `INJ p' (s CROSS s')(IMAGE p' (s CROSS s'))` by METIS_TAC [INJ_IMAGE_BIJ, BIJ_DEF]
  ++ `FINITE (IMAGE p' (s CROSS s'))` by RW_TAC std_ss [IMAGE_FINITE]
  ++ FULL_SIMP_TAC std_ss []
  ++ CONJ_TAC >> METIS_TAC []
  ++ REVERSE CONJ_TAC
  >> (RW_TAC std_ss [max_def] ++ FULL_SIMP_TAC std_ss [IN_IMAGE,IN_CROSS])
  ++ RW_TAC std_ss []
  >> ((MP_TAC o Q.SPEC `(\i. Normal (y i) * indicator_fn (b i) x')` o UNDISCH o Q.ISPEC `(s' :num -> bool)`) EXTREAL_SUM_IMAGE_IN_IF
      ++ `!x. (\i. Normal (y i) * indicator_fn (b i) x') x <> NegInf`
           by (RW_TAC std_ss [indicator_fn_def,mul_rone,mul_rzero]
               ++ RW_TAC std_ss [extreal_of_num_def,extreal_not_infty])
      ++ RW_TAC std_ss []
      ++ POP_ASSUM (K ALL_TAC)
      ++ `(\x. (if x IN s' then (\i. Normal (y i) * indicator_fn (b i) x') x else 0)) = (\x. (if x IN s' then (\i. Normal (y i) * SIGMA (\j. indicator_fn (a j INTER b i) x') s) x else 0))`
	  by (RW_TAC std_ss [FUN_EQ_THM]
		++ RW_TAC std_ss []
		++ FULL_SIMP_TAC std_ss [GSYM AND_IMP_INTRO]
		++ (MP_TAC o REWRITE_RULE [Once INTER_COMM] o Q.ISPEC `(b :num -> 'a -> bool) (x'' :num)` o UNDISCH_ALL o REWRITE_RULE [GSYM AND_IMP_INTRO] o Q.ISPECL [`(s :num -> bool)`, `m_space (m:('a -> bool) # (('a -> bool) -> bool) # (('a -> bool) -> extreal))`, `(a :num -> 'a -> bool)`]) indicator_fn_split
		++ Q.PAT_X_ASSUM `!i. i IN s' ==> (b:num->'a->bool) i IN measurable_sets m` (ASSUME_TAC o UNDISCH o Q.SPEC `x''`)
		++ `!a m. measure_space m /\ a IN measurable_sets m ==> a SUBSET m_space m` by RW_TAC std_ss [measure_space_def, sigma_algebra_def, algebra_def,subset_class_def, subsets_def, space_def]
		++ POP_ASSUM (ASSUME_TAC o UNDISCH_ALL o REWRITE_RULE [GSYM AND_IMP_INTRO] o Q.ISPECL [`(b :num -> 'a -> bool) (x'' :num)`,`(m : ('a -> bool) # (('a -> bool) -> bool) # (('a -> bool) -> extreal))`])
		++ ASM_SIMP_TAC std_ss [])
      ++ `(\x. if x IN s' then Normal (y x) * indicator_fn (b x) x' else 0) = 
        (\x. if x IN s' then (\i. Normal (y i) * indicator_fn (b i) x') x else 0)`
          by METIS_TAC []
      ++ POP_ORW
      ++ POP_ORW
      ++ `!(x:num) (i:num). Normal (y i) * SIGMA (\j. indicator_fn (a j INTER b i) x') s = SIGMA (\j. Normal (y i) * indicator_fn (a j INTER b i) x') s` 
           by (RW_TAC std_ss []
               ++ (MP_TAC o Q.SPECL [`(\j. indicator_fn (a j INTER (b:num->'a->bool) i) x')`,`y (i:num)`] o UNDISCH o Q.ISPEC `s:num->bool` o GSYM o INST_TYPE [alpha |-> ``:num``, beta |-> ``:num``]) EXTREAL_SUM_IMAGE_CMUL
	       ++ `!x. NegInf <> (\j. indicator_fn (a j INTER b i) x') x`
                     by RW_TAC std_ss [indicator_fn_def,extreal_of_num_def,extreal_not_infty]
	       ++ RW_TAC std_ss [])
      ++ POP_ORW
      ++ (MP_TAC o Q.ISPEC `(\n':num. Normal (max (x (FST (p n'))) (y (SND (p n')))) * 
                           indicator_fn ((\(i:num,j:num). a i INTER b j) (p n')) x')` o 
                   UNDISCH o Q.SPEC `p'` o UNDISCH o 
                   Q.ISPEC `((s:num->bool) CROSS (s':num->bool))` o 
                   INST_TYPE [``:'b``|->``:num``]) EXTREAL_SUM_IMAGE_IMAGE
      ++ `!x''. (\n'. Normal (max (x (FST (p n'))) (y (SND (p n')))) *
                 indicator_fn ((\(i,j). a i INTER b j) (p n')) x') x'' <> NegInf`
                 by (RW_TAC std_ss [indicator_fn_def,mul_rone,mul_rzero]
                     ++ RW_TAC std_ss [extreal_of_num_def,extreal_not_infty])
      ++ RW_TAC std_ss [o_DEF]
      ++ POP_ASSUM (K ALL_TAC)
      ++ (MP_TAC o Q.SPEC `(\x''. Normal (max (x (FST ((p :num -> num # num) (p' x'')))) (y (SND (p (p' x''))))) * 
                           indicator_fn ((\(i:num,j:num). a i INTER b j) (p (p' x''))) x')` o 
                   UNDISCH o Q.ISPEC `(s :num -> bool)CROSS(s' :num -> bool)`) 
                   EXTREAL_SUM_IMAGE_IN_IF
      ++ `!x''. (\x''. Normal (max (x (FST (p (p' x'')))) (y (SND (p (p' x''))))) *
                      indicator_fn ((\(i,j). a i INTER b j) (p (p' x''))) x') x'' <> NegInf`
                 by (RW_TAC std_ss [indicator_fn_def,mul_rone,mul_rzero]
                     ++ RW_TAC std_ss [extreal_of_num_def,extreal_not_infty])
      ++ RW_TAC std_ss []
      ++ NTAC 4 (POP_ASSUM (K ALL_TAC))
      ++ `!x. (\j. Normal (y x) * indicator_fn (a j INTER b x) x') = (\x j. Normal (y x) * indicator_fn (a j INTER b x) x') x` by METIS_TAC []
      ++ POP_ORW
      ++ `!x. SIGMA ((\x j. Normal (y x) * indicator_fn (a j INTER b x) x') x) s <> NegInf`
            by (RW_TAC std_ss []
                ++ `!j. Normal (y x'') * indicator_fn (a j INTER b x'') x' <> NegInf`
                      by (RW_TAC std_ss [indicator_fn_def,mul_rone,mul_rzero]
                          ++ RW_TAC std_ss [extreal_of_num_def,extreal_not_infty])
                ++ FULL_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_NOT_INFTY])
       ++ RW_TAC std_ss [EXTREAL_SUM_IMAGE_IF_ELIM]
       ++ (MP_TAC o Q.SPEC `(\x j. Normal (y x) * indicator_fn (a j INTER b x) x')` o Q.ISPECL [`s':num->bool`,`s:num->bool`]) EXTREAL_SUM_IMAGE_EXTREAL_SUM_IMAGE
       ++ `!x. NegInf <> (\x j. Normal (y x) * indicator_fn (a j INTER b x) x') (FST x) (SND x)`
                by (RW_TAC std_ss [indicator_fn_def,mul_rone,mul_rzero]
                    ++ RW_TAC std_ss [extreal_of_num_def,extreal_not_infty])
       ++ RW_TAC std_ss []
       ++ `(s' CROSS s) = IMAGE (\x. (SND x, FST x)) (s CROSS s')`
		by (RW_TAC std_ss [Once EXTENSION, IN_CROSS, IN_IMAGE]
		    ++ (MP_TAC o Q.ISPEC `x'':num#num`) pair_CASES
		    ++ RW_TAC std_ss [] ++ RW_TAC std_ss [FST,SND]
		    ++ EQ_TAC
        	    >> (STRIP_TAC ++ Q.EXISTS_TAC `(r,q)` ++ RW_TAC std_ss [FST,SND])
		    ++ RW_TAC std_ss [] ++ RW_TAC std_ss [])
       ++ POP_ORW
       ++ `INJ (\x. (SND x,FST x)) (s CROSS s') (IMAGE (\x. (SND x,FST x)) (s CROSS s'))`
		by (RW_TAC std_ss [INJ_DEF, IN_CROSS, IN_IMAGE]
		    >> METIS_TAC []
		    ++ (MP_TAC o Q.ISPEC `x'':num#num`) pair_CASES
		    ++ (MP_TAC o Q.ISPEC `x''':num#num`) pair_CASES
		    ++ RW_TAC std_ss []
		    ++ FULL_SIMP_TAC std_ss [FST,SND])
       ++ (MP_TAC o Q.SPEC `(\x. Normal (y (FST x)) * indicator_fn (a (SND x) INTER b (FST x)) x')` o UNDISCH o Q.SPEC `(\x. (SND x, FST x))` o UNDISCH o  Q.ISPEC `((s:num->bool) CROSS (s':num->bool))` o INST_TYPE [``:'b``|->``:num#num``]) EXTREAL_SUM_IMAGE_IMAGE
       ++ `!x. (\x. Normal (y (FST x)) * indicator_fn (a (SND x) INTER b (FST x)) x') x <> NegInf`
                by (RW_TAC std_ss [indicator_fn_def,mul_rone,mul_rzero]
                    ++ RW_TAC std_ss [extreal_of_num_def,extreal_not_infty])
       ++ RW_TAC std_ss [o_DEF]
       ++ Suff `!x'''. x''' IN (s CROSS s') ==> ((\x. Normal (y (SND x)) * indicator_fn (a (FST x) INTER b (SND x)) x') x''' = (\x''. if x'' IN s CROSS s' then Normal (max (x (FST x'')) (y (SND x''))) * indicator_fn ((\(i,j). a i INTER b j) x'') x' else 0) x''')`
       >> (RW_TAC std_ss []
           ++ (MATCH_MP_TAC o UNDISCH o Q.ISPEC `(s:num->bool) CROSS (s':num->bool)`) EXTREAL_SUM_IMAGE_EQ
	   ++ RW_TAC std_ss []
	   ++ DISJ1_TAC
	   ++ RW_TAC std_ss [indicator_fn_def,mul_rone,mul_rzero]
           ++ RW_TAC std_ss [extreal_of_num_def,extreal_not_infty])
       ++ RW_TAC std_ss [FUN_EQ_THM]
       ++ Cases_on `x'''`
       ++ RW_TAC real_ss [indicator_fn_def,mul_rone,mul_rzero]
       ++ `q IN s` by METIS_TAC [IN_CROSS,FST,SND]
       ++ `x' IN (a q)` by METIS_TAC [IN_INTER]
       ++ `SIGMA (\i. Normal (x i) * indicator_fn (a i) x') s = Normal (x q)`
           by (`pos_simple_fn m f s a x` by FULL_SIMP_TAC std_ss [pos_simple_fn_def]
	       ++ METIS_TAC [pos_simple_fn_thm1])
       ++ `r IN s'` by METIS_TAC [IN_CROSS,FST,SND]
       ++ `x' IN (b r)` by METIS_TAC [IN_INTER]
       ++ `SIGMA (\i. Normal (y i) * indicator_fn (b i) x') s' = Normal (y r)`
          by (`pos_simple_fn m g s' b y` by FULL_SIMP_TAC std_ss [pos_simple_fn_def]
	      ++ METIS_TAC [pos_simple_fn_thm1])
       ++ FULL_SIMP_TAC std_ss [extreal_le_def,max_def])
  ++ (MP_TAC o Q.SPEC `(\i. Normal (x i) * indicator_fn (a i) x')` o UNDISCH o Q.ISPEC `(s :num -> bool)`) EXTREAL_SUM_IMAGE_IN_IF
  ++ `!x''. (\i. Normal (x i) * indicator_fn (a i) x') x'' <> NegInf`
         by (RW_TAC std_ss [indicator_fn_def,mul_rone,mul_rzero]
             ++ RW_TAC std_ss [extreal_of_num_def,extreal_not_infty])
  ++ RW_TAC std_ss []
  ++ POP_ASSUM (K ALL_TAC)
  ++ `(\x''. if x'' IN s then Normal (x x'') * indicator_fn (a x'') x' else 0) = 
      (\x''. if x'' IN s then (\i. Normal (x i) * indicator_fn (a i) x') x'' else 0)`
          by METIS_TAC []
  ++ POP_ORW
  ++ `(\x''. (if x'' IN s then (\i. Normal (x i) * indicator_fn (a i) x') x'' else 0)) = (\x''. (if x'' IN s then (\i. Normal (x i) * SIGMA (\j. indicator_fn (a i INTER b j) x') s') x'' else 0))`
	 by (RW_TAC std_ss [FUN_EQ_THM]
	     ++ RW_TAC std_ss []
	     ++ FULL_SIMP_TAC std_ss [GSYM AND_IMP_INTRO]
	     ++ (MP_TAC o Q.ISPEC `(a:num -> 'a -> bool) (x'':num)` o UNDISCH_ALL o REWRITE_RULE [GSYM AND_IMP_INTRO] o Q.ISPECL [`(s':num -> bool)`, `m_space (m:('a -> bool) # (('a -> bool) -> bool) # (('a -> bool) -> extreal))`, `(b :num -> 'a -> bool)`]) indicator_fn_split
	     ++ `a x'' SUBSET m_space m` by METIS_TAC [MEASURE_SPACE_SUBSET_MSPACE]
	     ++ RW_TAC std_ss [])
  ++ POP_ORW
  ++ `!(i:num). Normal (x i) * SIGMA (\j. indicator_fn (a i INTER b j) x') s' = SIGMA (\j. Normal (x i) * indicator_fn (a i INTER b j) x') s'` 
         by (RW_TAC std_ss []
             ++ (MP_TAC o Q.SPECL [`(\j. indicator_fn ((a:num->'a->bool) i INTER b j) x')`,`x (i:num)`] o UNDISCH o Q.ISPEC `s':num->bool` o GSYM o INST_TYPE [alpha |-> ``:num``, beta |-> ``:num``]) EXTREAL_SUM_IMAGE_CMUL
	     ++ `!x. NegInf <> (\j. indicator_fn (a i INTER b j) x') x`
                    by RW_TAC std_ss [indicator_fn_def,extreal_of_num_def,extreal_not_infty]
	     ++ RW_TAC std_ss [])
  ++ POP_ORW
  ++ (MP_TAC o Q.ISPEC `(\n':num. Normal (max (x (FST (p n'))) (y (SND (p n')))) * 
                         indicator_fn ((\(i:num,j:num). a i INTER b j) (p n')) x')` o 
               UNDISCH o Q.SPEC `p'` o UNDISCH o 
               Q.ISPEC `((s:num->bool) CROSS (s':num->bool))` o 
               INST_TYPE [``:'b``|->``:num``]) EXTREAL_SUM_IMAGE_IMAGE
  ++ `!x''. (\n'. Normal (max (x (FST (p n'))) (y (SND (p n')))) *
             indicator_fn ((\(i,j). a i INTER b j) (p n')) x') x'' <> NegInf`
              by (RW_TAC std_ss [indicator_fn_def,mul_rone,mul_rzero]
                  ++ RW_TAC std_ss [extreal_of_num_def,extreal_not_infty])
  ++ RW_TAC std_ss [o_DEF]
  ++ POP_ASSUM (K ALL_TAC)
  ++ (MP_TAC o Q.SPEC `(\x''. Normal (max (x (FST ((p :num -> num # num) (p' x'')))) (y (SND (p (p' x''))))) * 
                       indicator_fn ((\(i:num,j:num). a i INTER b j) (p (p' x''))) x')` o 
               UNDISCH o Q.ISPEC `(s :num -> bool)CROSS(s' :num -> bool)`) 
               EXTREAL_SUM_IMAGE_IN_IF
  ++ `!x''. (\x''. Normal (max (x (FST (p (p' x'')))) (y (SND (p (p' x''))))) *
                  indicator_fn ((\(i,j). a i INTER b j) (p (p' x''))) x') x'' <> NegInf`
             by (RW_TAC std_ss [indicator_fn_def,mul_rone,mul_rzero]
                 ++ RW_TAC std_ss [extreal_of_num_def,extreal_not_infty])
  ++ RW_TAC std_ss []
  ++ NTAC 4 (POP_ASSUM (K ALL_TAC))
  ++ `!x''. (\j. Normal (x x'') * indicator_fn (a x'' INTER b j) x') = (\x'' j. Normal (x x'') * indicator_fn (a x'' INTER b j) x') x''` by METIS_TAC []
  ++ POP_ORW
  ++ `!x''. SIGMA ((\x'' j. Normal (x x'') * indicator_fn (a x'' INTER b j) x') x'') s' <> NegInf`
        by (RW_TAC std_ss []
            ++ `!j. Normal (x x'') * indicator_fn (a x'' INTER b j) x' <> NegInf`
                  by (RW_TAC std_ss [indicator_fn_def,mul_rone,mul_rzero]
                      ++ RW_TAC std_ss [extreal_of_num_def,extreal_not_infty])
            ++ FULL_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_NOT_INFTY])
  ++ RW_TAC std_ss [EXTREAL_SUM_IMAGE_IF_ELIM]
  ++ (MP_TAC o Q.SPEC `(\x'' j. Normal (x x'') * indicator_fn (a x'' INTER b j) x')` o Q.ISPECL [`s:num->bool`,`s':num->bool`]) EXTREAL_SUM_IMAGE_EXTREAL_SUM_IMAGE
  ++ `!x''. NegInf <> (\x'' j. Normal (x x'') * indicator_fn (a x'' INTER b j) x') (FST x'') (SND x'')`
            by (RW_TAC std_ss [indicator_fn_def,mul_rone,mul_rzero]
                ++ RW_TAC std_ss [extreal_of_num_def,extreal_not_infty])
  ++ RW_TAC std_ss []
  ++ Suff `!x'''. x''' IN (s CROSS s') ==> ( (\x''. Normal (x (FST x'')) * indicator_fn (a (FST x'') INTER b (SND x'')) x') x''' = (\x''. if x'' IN s CROSS s' then Normal (max (x (FST x'')) (y (SND x''))) * indicator_fn ((\(i,j). a i INTER b j) x'') x' else 0) x''')`
  >> (RW_TAC std_ss []
      ++ (MATCH_MP_TAC o UNDISCH o Q.ISPEC `(s:num->bool) CROSS (s':num->bool)`) EXTREAL_SUM_IMAGE_EQ
      ++ RW_TAC std_ss []
      ++ DISJ1_TAC
      ++ RW_TAC std_ss [indicator_fn_def,mul_rone,mul_rzero]
      ++ RW_TAC std_ss [extreal_of_num_def,extreal_not_infty])
  ++ RW_TAC std_ss [FUN_EQ_THM]
  ++ Cases_on `x'''`
  ++ RW_TAC real_ss [indicator_fn_def,mul_rone,mul_rzero]
  ++ `q IN s` by METIS_TAC [IN_CROSS,FST,SND]
  ++ `x' IN (a q)` by METIS_TAC [IN_INTER]
  ++ `SIGMA (\i. Normal (x i) * indicator_fn (a i) x') s = Normal (x q)`
        by (`pos_simple_fn m f s a x` by FULL_SIMP_TAC std_ss [pos_simple_fn_def]
            ++ METIS_TAC [pos_simple_fn_thm1])
  ++ `r IN s'` by METIS_TAC [IN_CROSS,FST,SND]
  ++ `x' IN (b r)` by METIS_TAC [IN_INTER]
  ++ `SIGMA (\i. Normal (y i) * indicator_fn (b i) x') s' = Normal (y r)`
        by (`pos_simple_fn m g s' b y` by FULL_SIMP_TAC std_ss [pos_simple_fn_def]
            ++ METIS_TAC [pos_simple_fn_thm1])
  ++ FULL_SIMP_TAC std_ss [extreal_le_def,max_def]);

val pos_simple_fn_not_infty = store_thm
("pos_simple_fn_not_infty",``!m f s a x. pos_simple_fn m f s a x ==> (!x. x IN m_space m ==> f x <> NegInf /\ f x <> PosInf)``, 
  RW_TAC std_ss [pos_simple_fn_def]
  ++ `(!i. i IN s ==> (\i. Normal (x i) * indicator_fn (a i) x') i <> NegInf)`
       by (RW_TAC std_ss [indicator_fn_def,mul_rzero,mul_rone]
           ++ RW_TAC std_ss [extreal_of_num_def,extreal_not_infty])
  ++ `(!i. i IN s ==> (\i. Normal (x i) * indicator_fn (a i) x') i <> PosInf)`
       by (RW_TAC std_ss [indicator_fn_def,mul_rzero,mul_rone]
           ++ RW_TAC std_ss [extreal_of_num_def,extreal_not_infty])
  ++ FULL_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_NOT_INFTY]);

(* ************************************************************************* *)
(* Properties of Integrals of Positive Simple Functions                      *)
(* ************************************************************************* *)

val pos_simple_fn_integral_add = store_thm
  ("pos_simple_fn_integral_add",
   ``!m f (s:num->bool) a x
        g (s':num->bool) b y.
	measure_space m /\
	pos_simple_fn m f s a x /\ pos_simple_fn m g s' b y ==>
	?s'' c z. pos_simple_fn m (\x. f x + g x) s'' c z /\
		(pos_simple_fn_integral m s a x +
		 pos_simple_fn_integral m s' b y =
		 pos_simple_fn_integral m s'' c z)``,
   REPEAT STRIP_TAC
   ++ (MP_TAC o Q.SPECL [`m`,`f`,`s`,`a`,`x`,`g`,`s'`,`b`,`y`]) pos_simple_fn_integral_present
   ++ RW_TAC std_ss [] ++ ASM_SIMP_TAC std_ss []
   ++ Q.EXISTS_TAC `k` ++ Q.EXISTS_TAC `c` ++ Q.EXISTS_TAC `(\i. z i + z' i)`
   ++ FULL_SIMP_TAC std_ss [pos_simple_fn_def, pos_simple_fn_integral_def]
   ++ REVERSE CONJ_TAC
   >> (RW_TAC std_ss [GSYM extreal_add_def]
       ++ `!i. i IN k ==> Normal (z i) <> NegInf /\ Normal (z' i) <> NegInf /\ 0 <= Normal (z i) /\ 0 <= Normal (z' i)`
           by METIS_TAC [extreal_not_infty,extreal_of_num_def,extreal_le_def]
       ++ `!i. i IN k ==> (\i. (Normal (z i) + Normal (z' i)) * measure m (c i)) i <> NegInf`
           by METIS_TAC [extreal_add_def,mul_not_infty,positive_not_infty,measure_space_def,REAL_LE_ADD]
       ++ (MP_TAC o Q.SPEC `(\i:num. (Normal (z i) + Normal (z' i)) * measure m (c i))` o UNDISCH o Q.ISPEC `k:num->bool`) EXTREAL_SUM_IMAGE_IN_IF
       ++ RW_TAC std_ss [add_rdistrib]
       ++ (MP_TAC o Q.SPEC `(\x. Normal (z x) * measure m (c x) + Normal (z' x) * measure m (c x))` o UNDISCH o Q.ISPEC `k:num->bool` o GSYM) EXTREAL_SUM_IMAGE_IN_IF
       ++ `!x. x IN k ==>  NegInf <>
           (\x. Normal (z x) * measure m (c x) + Normal (z' x) * measure m (c x)) x`
             by METIS_TAC [extreal_add_def,mul_not_infty,positive_not_infty,measure_space_def,REAL_LE_ADD,add_not_infty]
       ++ RW_TAC std_ss []
       ++ `(\x. Normal (z x) * measure m (c x) + Normal (z' x) * measure m (c x)) = 
           (\x. (\x. Normal (z x) * measure m (c x)) x + (\x. Normal (z' x) * measure m (c x)) x)`
              by METIS_TAC []
       ++ POP_ORW
       ++ (MATCH_MP_TAC o UNDISCH o Q.ISPEC `k:num->bool` o GSYM) EXTREAL_SUM_IMAGE_ADD
       ++ DISJ1_TAC
       ++ METIS_TAC [mul_not_infty,positive_not_infty,measure_space_def,extreal_not_infty])
   ++ RW_TAC std_ss [REAL_LE_ADD,le_add]
   ++ RW_TAC std_ss [GSYM extreal_add_def]
   ++ `!i. i IN k ==> Normal (z i) <> NegInf /\ Normal (z' i) <> NegInf /\ 0 <= Normal (z i) /\ 0 <= Normal (z' i)`
         by METIS_TAC [extreal_not_infty,extreal_of_num_def,extreal_le_def]
   ++ `!i. i IN k ==> (\i. (Normal (z i) + Normal (z' i)) * indicator_fn (c i) x') i <> NegInf`
         by METIS_TAC [extreal_add_def,indicator_fn_def,mul_rzero,mul_rone,extreal_of_num_def,extreal_not_infty]
   ++ (MP_TAC o Q.SPEC `(\i:num. (Normal (z i) + Normal (z' i)) *  indicator_fn (c i) x')` o UNDISCH o Q.ISPEC `k:num->bool`) EXTREAL_SUM_IMAGE_IN_IF
   ++ RW_TAC std_ss [add_rdistrib]
   ++ (MP_TAC o Q.SPEC `(\x. Normal (z x) * indicator_fn (c x) x' + Normal (z' x) * indicator_fn (c x) x')` o UNDISCH o Q.ISPEC `k:num->bool` o GSYM) EXTREAL_SUM_IMAGE_IN_IF
   ++ `!x. x IN k ==>  NegInf <>
        (\x. Normal (z x) * indicator_fn (c x) x' + Normal (z' x) * indicator_fn (c x) x') x`
         by (RW_TAC std_ss [extreal_add_def,indicator_fn_def,mul_rzero,mul_rone,add_rzero]
             ++ METIS_TAC [extreal_of_num_def,extreal_not_infty])
   ++ RW_TAC std_ss []
   ++ `(\x. Normal (z x) * indicator_fn (c x) x' + Normal (z' x) * indicator_fn (c x) x') = 
       (\x. (\x. Normal (z x) * indicator_fn (c x) x') x + (\x. Normal (z' x) * indicator_fn (c x) x') x)`
            by METIS_TAC []
   ++ POP_ORW
   ++ (MP_TAC o Q.SPECL [`(\x:num. Normal (z x) * indicator_fn (c x) x')`,`(\x:num. Normal (z' x) * indicator_fn (c x) x')`] o UNDISCH o Q.ISPEC `k:num->bool` o GSYM) EXTREAL_SUM_IMAGE_ADD
   ++ `!x:num. x IN k ==> NegInf <> (\x:num. Normal (z x) * indicator_fn (c x) x') x /\
                          NegInf <> (\x:num. Normal (z' x) * indicator_fn (c x) x') x`
         by (RW_TAC std_ss [indicator_fn_def,mul_rone,mul_rzero,add_rzero]
             ++ METIS_TAC [extreal_of_num_def,extreal_not_infty])
   ++ METIS_TAC []);

val pos_simple_fn_integral_add_alt = store_thm
  ("pos_simple_fn_integral_add_alt", ``!m f s a x g y.	measure_space m /\ 
        pos_simple_fn m f s a x /\ pos_simple_fn m g s a y ==>
  	  (pos_simple_fn_integral m s a x + 
           pos_simple_fn_integral m s a y =
 	   pos_simple_fn_integral m s a (\i. x i + y i))``,

   RW_TAC std_ss [pos_simple_fn_def, pos_simple_fn_integral_def,GSYM extreal_add_def]
   ++ `!i. i IN s ==> Normal (x i) <> NegInf /\ Normal (y i) <> NegInf /\ 0 <= Normal (x i) /\ 0 <= Normal (y i)`
        by METIS_TAC [extreal_not_infty,extreal_of_num_def,extreal_le_def]
   ++ `!i. i IN s ==> (\i. (Normal (x i) + Normal (y i)) * measure m (a i)) i <> NegInf`
        by METIS_TAC [extreal_add_def,mul_not_infty,positive_not_infty,measure_space_def,REAL_LE_ADD]
   ++ (MP_TAC o Q.SPEC `(\i:num. (Normal (x i) + Normal (y i)) * measure m (a i))` o UNDISCH o Q.ISPEC `s:num->bool`) EXTREAL_SUM_IMAGE_IN_IF
   ++ RW_TAC std_ss [add_rdistrib]
   ++ (MP_TAC o Q.SPEC `(\i. Normal (x i) * measure m (a i) + Normal (y i) * measure m (a i))` o UNDISCH o Q.ISPEC `s:num->bool` o GSYM) EXTREAL_SUM_IMAGE_IN_IF
   ++ `!i. i IN s ==>  NegInf <>
        (\i. Normal (x i) * measure m (a i) + Normal (y i) * measure m (a i)) i`
           by METIS_TAC [extreal_add_def,mul_not_infty,positive_not_infty,measure_space_def,REAL_LE_ADD,add_not_infty]
   ++ RW_TAC std_ss []
   ++ `(\i. Normal (x i) * measure m (a i) + Normal (y i) * measure m (a i)) = 
       (\i. (\i. Normal (x i) * measure m (a i)) i + (\i. Normal (y i) * measure m (a i)) i)`
          by METIS_TAC []
   ++ POP_ORW
   ++ (MATCH_MP_TAC o UNDISCH o Q.ISPEC `s:num->bool` o GSYM) EXTREAL_SUM_IMAGE_ADD
   ++ DISJ1_TAC
   ++ METIS_TAC [mul_not_infty,positive_not_infty,measure_space_def,extreal_not_infty]);

val psfis_add = store_thm
  ("psfis_add",
   ``!m f g a b.
	measure_space m /\
	a IN psfis m f /\ b IN psfis m g ==>
	a + b IN psfis m (\x. f x + g x)``,
 RW_TAC std_ss [psfis_def, IN_IMAGE, psfs_def, GSPECIFICATION]
 ++ Cases_on `x'` ++ Cases_on `x` ++ Cases_on `x''` ++ Cases_on `x'''`
 ++ Cases_on `r'` ++ Cases_on `r` ++ Cases_on `r''` ++ Cases_on `r'''`
 ++ RW_TAC std_ss []
 ++ FULL_SIMP_TAC std_ss [PAIR_EQ]
 ++ Suff `?s a x. (pos_simple_fn_integral m q q''''' r' +
 	           pos_simple_fn_integral m q''' q''''''' r'' =
		   pos_simple_fn_integral m s a x) /\
	    pos_simple_fn m (\x. f x + g x) s a x`
 >> (RW_TAC std_ss [] ++ Q.EXISTS_TAC `(s,a,x)`
     ++ RW_TAC std_ss [] ++ Q.EXISTS_TAC `(s,a,x)`
     ++ RW_TAC std_ss [PAIR_EQ])
 ++ ONCE_REWRITE_TAC [CONJ_COMM]
 ++ MATCH_MP_TAC pos_simple_fn_integral_add ++ RW_TAC std_ss []);

val pos_simple_fn_integral_mono = store_thm
("pos_simple_fn_integral_mono",
   ``!m f (s:num->bool) a x
        g (s':num->bool) b y.
	measure_space m /\
	pos_simple_fn m f s a x /\ pos_simple_fn m g s' b y /\
	(!x. x IN m_space m ==> f x <= g x) ==>
	pos_simple_fn_integral m s a x <= pos_simple_fn_integral m s' b y``,
  REPEAT STRIP_TAC
  ++ (MP_TAC o Q.SPECL [`m`,`f`,`s`,`a`,`x`,`g`,`s'`,`b`,`y`]) pos_simple_fn_integral_present
  ++ RW_TAC std_ss [] ++ ASM_SIMP_TAC std_ss []
  ++ RW_TAC std_ss [pos_simple_fn_integral_def]
  ++ (MATCH_MP_TAC o UNDISCH o Q.ISPEC `k:num->bool`) EXTREAL_SUM_IMAGE_MONO
  ++ RW_TAC std_ss []
  >> (DISJ1_TAC
      ++ RW_TAC std_ss []
      ++ `measure m (c x') <> NegInf` by METIS_TAC [measure_space_def,positive_not_infty]
      ++ Cases_on `measure m (c x')` ++ RW_TAC std_ss [extreal_mul_def,extreal_not_infty]
      ++ METIS_TAC [real_lte,REAL_LE_ANTISYM])
  ++ Cases_on `c x' = {}`
  >> RW_TAC real_ss [MEASURE_EMPTY,mul_rzero,le_refl]
  ++ `pos_simple_fn m f k c z` by FULL_SIMP_TAC std_ss [pos_simple_fn_def] 
  ++ `pos_simple_fn m g k c z'` by FULL_SIMP_TAC std_ss [pos_simple_fn_def] 
  ++ `?t. t IN c x'` by METIS_TAC [CHOICE_DEF]
  ++ `f t = Normal (z x')` by METIS_TAC [pos_simple_fn_thm1]
  ++ `g t = Normal (z' x')` by METIS_TAC [pos_simple_fn_thm1]
  ++ `Normal (z x') <= Normal (z' x')` by METIS_TAC [MEASURE_SPACE_SUBSET_MSPACE,SUBSET_DEF]
  ++ Cases_on `measure m (c x') = 0` >> RW_TAC std_ss [mul_rzero,le_refl]
  ++ MATCH_MP_TAC le_rmul_imp
  ++ RW_TAC std_ss []
  ++ METIS_TAC [MEASURE_SPACE_POSITIVE,positive_def,lt_le]);

val psfis_mono = store_thm
("psfis_mono", ``!m f g a b. measure_space m /\ a IN psfis m f /\ b IN psfis m g /\
	(!x. x IN m_space m ==> f x <= g x) ==>	a <= b``,
  RW_TAC std_ss [psfis_def, IN_IMAGE, psfs_def, GSPECIFICATION]
  ++ Cases_on `x'` ++ Cases_on `x` ++ Cases_on `x''` ++ Cases_on `x'''`
  ++ Cases_on `r'` ++ Cases_on `r` ++ Cases_on `r''` ++ Cases_on `r'''` 
  ++ RW_TAC std_ss []
  ++ FULL_SIMP_TAC std_ss [PAIR_EQ]
  ++ MATCH_MP_TAC pos_simple_fn_integral_mono
  ++ METIS_TAC []);

val pos_simple_fn_integral_unique = store_thm
 ("pos_simple_fn_integral_unique", ``!m f (s:num->bool) a x (s':num->bool) b y.
	measure_space m /\ pos_simple_fn m f s a x /\ pos_simple_fn m f s' b y ==>
	(pos_simple_fn_integral m s a x = pos_simple_fn_integral m s' b y)``,
   METIS_TAC [le_antisym, le_refl, pos_simple_fn_integral_mono]);

val psfis_unique = store_thm
 ("psfis_unique", ``!m f a b.
	measure_space m /\ a IN psfis m f /\ b IN psfis m f ==>	(a = b)``,
   METIS_TAC [le_antisym, le_refl, psfis_mono]);

val pos_simple_fn_integral_indicator = store_thm
 ("pos_simple_fn_integral_indicator", ``!m A. measure_space m /\ A IN measurable_sets m ==>
	(?s a x. pos_simple_fn m (indicator_fn A) s a x /\
		 (pos_simple_fn_integral m s a x = measure m A))``,
  RW_TAC std_ss []
  ++ Q.EXISTS_TAC `{0;1}`
  ++ Q.EXISTS_TAC `\i. if i = 0 then m_space m DIFF A else A`
  ++ Q.EXISTS_TAC `\i. if i = 0 then 0 else 1`
  ++ RW_TAC std_ss [pos_simple_fn_indicator_alt,pos_simple_fn_integral_def]
  ++ (MP_TAC o Q.SPEC `0:num` o REWRITE_RULE [FINITE_SING] o Q.ISPECL [`(\i:num. Normal (if i = 0 then 0 else 1) * measure m (if i = 0 then m_space m DIFF A else A))`,`{1:num}`]) EXTREAL_SUM_IMAGE_PROPERTY
  ++ `!x:num. x IN {0; 1} ==> (\i. Normal (if i = 0 then 0 else 1) *
           measure m (if i = 0 then m_space m DIFF A else A)) x <>  NegInf`
       by (RW_TAC std_ss [GSYM extreal_of_num_def,mul_lzero,mul_lone]
           ++ METIS_TAC [extreal_of_num_def,extreal_not_infty,positive_not_infty,MEASURE_SPACE_POSITIVE])
  ++ RW_TAC std_ss [GSYM extreal_of_num_def,mul_lzero,add_lzero]
  ++ `{1:num} DELETE 0 = {1}`
	by RW_TAC real_ss [Once EXTENSION, IN_SING, IN_DELETE]
  ++ RW_TAC std_ss [EXTREAL_SUM_IMAGE_SING,GSYM extreal_of_num_def,mul_lone]);

val psfis_indicator = store_thm
  ("psfis_indicator",
   ``!m A. measure_space m /\ A IN measurable_sets m ==>
		measure m A IN psfis m (indicator_fn A)``,
   RW_TAC std_ss [psfis_def, IN_IMAGE, psfs_def, GSPECIFICATION]
   ++ Suff `?s a x. pos_simple_fn m (indicator_fn A) s a x /\
		    (pos_simple_fn_integral m s a x = measure m A)`
   >> (RW_TAC std_ss [] ++ Q.EXISTS_TAC `(s,a,x)`
       ++ RW_TAC std_ss [] ++ Q.EXISTS_TAC `(s,a,x)`
       ++ RW_TAC std_ss [PAIR_EQ])
   ++ MATCH_MP_TAC pos_simple_fn_integral_indicator
   ++ ASM_REWRITE_TAC []);

val pos_simple_fn_integral_cmul = store_thm
 ("pos_simple_fn_integral_cmul", ``!m f s a x z. measure_space m /\ pos_simple_fn m f s a x /\ 0 <= z ==>
	    (pos_simple_fn m (\x. Normal z * f x) s a (\i. z * x i) /\
	    (pos_simple_fn_integral m s a (\i. z * x i) = Normal z * pos_simple_fn_integral m s a x))``,
  RW_TAC std_ss [pos_simple_fn_integral_def, pos_simple_fn_def,REAL_LE_MUL,GSYM extreal_mul_def]
  << [METIS_TAC [le_mul,extreal_le_def,extreal_of_num_def],
      `(\i. Normal z * Normal (x i) * indicator_fn (a i) x') = 
       (\i. Normal z * (\i. Normal (x i) * indicator_fn (a i) x') i)`
         by METIS_TAC [mul_assoc]
      ++ POP_ORW
      ++ (MATCH_MP_TAC o UNDISCH o Q.ISPEC `s:num->bool` o GSYM) EXTREAL_SUM_IMAGE_CMUL
      ++ DISJ1_TAC
      ++ RW_TAC std_ss [indicator_fn_def,mul_rone,mul_rzero]
      ++ RW_TAC std_ss [extreal_of_num_def,extreal_not_infty],
      `(\i. Normal z * Normal (x i) * measure m (a i)) = 
         (\i. Normal z * (\i. Normal (x i) * measure m (a i)) i)` by METIS_TAC [mul_assoc]
      ++ POP_ORW
      ++ (MATCH_MP_TAC o UNDISCH o Q.ISPEC `s:num->bool`) EXTREAL_SUM_IMAGE_CMUL
      ++ DISJ1_TAC
      ++ RW_TAC std_ss []
      ++ METIS_TAC [mul_not_infty,positive_not_infty,MEASURE_SPACE_POSITIVE]]);

val psfis_cmul = store_thm
 ("psfis_cmul", ``!m f a z. measure_space m /\ a IN psfis m f /\ 0 <= z ==>
	Normal z * a IN psfis m (\x. Normal z * f x)``,
  RW_TAC std_ss [psfis_def, IN_IMAGE, psfs_def, GSPECIFICATION]
  ++ Cases_on `x'`
  ++ Cases_on `r`
  ++ FULL_SIMP_TAC std_ss [PAIR_EQ]
  ++ Q.EXISTS_TAC `(q,q',(\i. z * r' i))`
  ++ RW_TAC std_ss []
  >> METIS_TAC [pos_simple_fn_integral_cmul]
  ++ Q.EXISTS_TAC `(q,q',(\i. z * r' i))`
  ++ RW_TAC std_ss []
  ++ METIS_TAC [pos_simple_fn_integral_cmul]);

val pos_simple_fn_integral_cmul_alt = store_thm
("pos_simple_fn_integral_cmul_alt",``!m f s a x z. measure_space m /\ 0 <= z /\ pos_simple_fn m f s a x ==> (?s' a' x'. (pos_simple_fn m (\t. Normal z * f t) s' a' x') /\ (pos_simple_fn_integral m s' a' x' = Normal z * pos_simple_fn_integral m s a x))``,
  RW_TAC real_ss []
  ++ Q.EXISTS_TAC `s` ++ Q.EXISTS_TAC `a` ++ Q.EXISTS_TAC `(\i. z * x i)`
  ++ RW_TAC std_ss [pos_simple_fn_cmul_alt]
  ++ FULL_SIMP_TAC real_ss [pos_simple_fn_integral_def,pos_simple_fn_def,mul_assoc,GSYM extreal_mul_def]
  ++ `(\i. Normal z * Normal (x i) * measure m (a i)) = 
      (\j. Normal z * (\i. Normal (x i) * measure m (a i)) j)`
        by RW_TAC std_ss [FUN_EQ_THM,mul_assoc]
  ++ POP_ORW
  ++ (MATCH_MP_TAC o UNDISCH o Q.ISPEC `s:num->bool`) EXTREAL_SUM_IMAGE_CMUL
  ++ DISJ1_TAC
  ++ METIS_TAC [mul_not_infty,extreal_not_infty,positive_not_infty,MEASURE_SPACE_POSITIVE]);

val IN_psfis = store_thm
  ("IN_psfis",
   ``!m r f. r IN psfis m f ==>	?s a x. pos_simple_fn m f s a x /\ (r = pos_simple_fn_integral m s a x)``,
   RW_TAC std_ss [psfis_def, IN_IMAGE, psfs_def, GSPECIFICATION]
   ++ Cases_on `x'`++ Cases_on `x` ++ Cases_on `r` ++ Cases_on `r'`
   ++ RW_TAC std_ss []
   ++ FULL_SIMP_TAC std_ss [PAIR_EQ]
   ++ METIS_TAC []);

val IN_psfis_eq = store_thm
  ("IN_psfis_eq",
   ``!m r f. r IN psfis m f = ?s a x. pos_simple_fn m f s a x /\ (r = pos_simple_fn_integral m s a x)``,
   RW_TAC std_ss []
   ++ EQ_TAC
   >> RW_TAC std_ss [IN_psfis]
   ++ RW_TAC std_ss [psfis_def,psfs_def,IN_IMAGE,GSPECIFICATION]
   ++ Q.EXISTS_TAC `(s,a,x)`
   ++ RW_TAC std_ss []
   ++ Q.EXISTS_TAC `(s,a,x)`
   ++ RW_TAC std_ss []);

val psfis_pos = store_thm
 ("psfis_pos",
   ``!m f a. measure_space m /\ a IN psfis m f ==> (!x. x IN m_space m ==> 0 <= f x)``,
  RW_TAC std_ss [psfis_def, IN_IMAGE, psfs_def, GSPECIFICATION]
  ++ Cases_on `x'`
  ++ Cases_on `r`
  ++ FULL_SIMP_TAC std_ss [PAIR_EQ,pos_simple_fn_def]
  ++ MATCH_MP_TAC EXTREAL_SUM_IMAGE_POS
  ++ RW_TAC std_ss [indicator_fn_def,mul_rzero,mul_rone,le_refl]
  ++ RW_TAC std_ss [extreal_of_num_def,extreal_le_def]);

val pos_simple_fn_integral_zero = store_thm
("pos_simple_fn_integral_zero",``!m s a x. measure_space m /\ pos_simple_fn m (\t. 0) s a x ==> (pos_simple_fn_integral m s a x = 0)``,
  RW_TAC std_ss []
  ++ `pos_simple_fn m (\t. 0) {1:num} (\i:num. if i=1 then (m_space m) else {}) (\i:num. 0) /\ 
     (pos_simple_fn_integral m  {1:num} (\i:num. if i=1 then (m_space m) else {}) (\i:num. 0) = 0)` 
      by  RW_TAC real_ss [pos_simple_fn_integral_def, pos_simple_fn_def,FINITE_SING, EXTREAL_SUM_IMAGE_SING, EXTREAL_SUM_IMAGE_SING, IMAGE_SING,BIGUNION_SING,IN_SING,MEASURE_SPACE_MSPACE_MEASURABLE,GSYM extreal_of_num_def,mul_lzero,le_refl]
  ++ METIS_TAC [pos_simple_fn_integral_unique]);   

val pos_simple_fn_integral_zero_alt = store_thm
("pos_simple_fn_integral_zero_alt",``!m s a x. measure_space m /\ pos_simple_fn m g s a x /\ (!x. x IN m_space m ==> (g x = 0))  
                                      ==> (pos_simple_fn_integral m s a x = 0)``,
  RW_TAC std_ss [pos_simple_fn_integral_def]
  ++ MATCH_MP_TAC EXTREAL_SUM_IMAGE_0
  ++ CONJ_TAC >> FULL_SIMP_TAC std_ss [pos_simple_fn_def]
  ++ RW_TAC std_ss []
  ++ Cases_on `a x' = {}` >> FULL_SIMP_TAC std_ss [MEASURE_EMPTY,mul_rzero]
  ++ Suff `Normal (x x') = 0` >> FULL_SIMP_TAC std_ss [mul_lzero]
  ++ `?y. y IN a x'` by METIS_TAC [CHOICE_DEF]
  ++ METIS_TAC [pos_simple_fn_thm1,MEASURE_SPACE_SUBSET_MSPACE,pos_simple_fn_def,SUBSET_DEF]);

val psfis_zero = store_thm
 ("psfis_zero", ``!m a. measure_space m ==> ((a IN psfis m (\x. 0)) = (a = 0))``,
  RW_TAC std_ss []
  ++ EQ_TAC  >> METIS_TAC [IN_psfis_eq,pos_simple_fn_integral_zero]
  ++ RW_TAC std_ss [IN_psfis_eq]
  ++ Q.EXISTS_TAC `{1}` ++ Q.EXISTS_TAC `(\i. m_space m)` ++ Q.EXISTS_TAC `(\i. 0)`
  ++ RW_TAC real_ss [pos_simple_fn_integral_def, pos_simple_fn_def,FINITE_SING,
 		     EXTREAL_SUM_IMAGE_SING, REAL_SUM_IMAGE_SING,IMAGE_SING,BIGUNION_SING,IN_SING,MEASURE_SPACE_MSPACE_MEASURABLE,mul_lzero,GSYM extreal_of_num_def,le_refl]);

val pos_simple_fn_integral_not_infty = store_thm
 ("pos_simple_fn_integral_not_infty", ``!m f s a x. measure_space m /\ pos_simple_fn m f s a x
	==> pos_simple_fn_integral m s a x <> NegInf``,
  RW_TAC std_ss [pos_simple_fn_integral_def,pos_simple_fn_def]
  ++ Suff `!i. i IN s ==> (\i. Normal (x i) * measure m (a i)) i <> NegInf`
  >> FULL_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_NOT_INFTY]
  ++ METIS_TAC [mul_not_infty,extreal_le_def,extreal_of_num_def,positive_not_infty,MEASURE_SPACE_POSITIVE]);

val psfis_not_infty = store_thm
 ("psfis_not_infty", ``!m f a. measure_space m  /\ a IN psfis m f ==> a <> NegInf``,
  METIS_TAC [IN_psfis_eq,pos_simple_fn_integral_not_infty]);

val pos_simple_fn_integral_sum = store_thm
  ("pos_simple_fn_integral_sum",
   ``!m f s a x P. measure_space m /\
	(!i. i IN P ==> pos_simple_fn m (f i) s a (x i)) /\
	(!i t. i IN P ==> f i t <> NegInf) /\ FINITE P /\ P <> {} ==>
	(pos_simple_fn m (\t. SIGMA (\i. f i t) P) s a (\i. SIGMA (\j. x j i) P) /\
		    (pos_simple_fn_integral m s a (\j. SIGMA (\i. x i j) P) =
		     SIGMA (\i. pos_simple_fn_integral m s a (x i)) P))``,
  Suff `!P:'b->bool. FINITE P ==>
        (\P:'b->bool. !m f s a x. measure_space m /\
	(!i. i IN P ==> pos_simple_fn m (f i) s a (x i)) /\
	(!i t. i IN P ==> f i t <> NegInf) /\ P <> {} ==>
	(pos_simple_fn m (\t. SIGMA (\i. f i t) P) s a (\i. SIGMA (\j. x j i) P) /\
		    (pos_simple_fn_integral m s a (\j. SIGMA (\i. x i j) P) =
		     SIGMA (\i. pos_simple_fn_integral m s a (x i)) P))) P`
  >> METIS_TAC []
  ++ MATCH_MP_TAC FINITE_INDUCT
  ++ CONJ_TAC
  >> RW_TAC std_ss [NOT_IN_EMPTY,EXTREAL_SUM_IMAGE_EMPTY,REAL_SUM_IMAGE_THM] 
  ++ RW_TAC std_ss [REAL_SUM_IMAGE_THM,DELETE_NON_ELEMENT]
  >> (`(\t. SIGMA (\i. f i t) (e INSERT s)) = (\t. f e t + (\t. SIGMA (\i. f i t) s) t)`
          by (RW_TAC std_ss [FUN_EQ_THM] 
             ++ (MP_TAC o UNDISCH o Q.SPECL [`(\i. f i t)`,`s`] o INST_TYPE [alpha |-> beta]) EXTREAL_SUM_IMAGE_PROPERTY
	     ++ FULL_SIMP_TAC std_ss [DELETE_NON_ELEMENT])
      ++ POP_ORW
      ++ `(\i. x e i + SIGMA (\j. x j i) s) = (\i. x e i + (\i. SIGMA (\j. x j i) s) i)`
             by METIS_TAC []
      ++ POP_ORW
      ++ MATCH_MP_TAC pos_simple_fn_add_alt
      ++ RW_TAC std_ss [] >> METIS_TAC [IN_INSERT]
      ++ Q.PAT_X_ASSUM `!m f s' a x. Q` (MP_TAC o Q.SPECL [`m`,`f`,`s'`,`a`,`x`])
      ++ RW_TAC std_ss []
      ++ Cases_on `s <> {}` >> METIS_TAC [IN_INSERT]
      ++ FULL_SIMP_TAC real_ss [EXTREAL_SUM_IMAGE_EMPTY,REAL_SUM_IMAGE_THM,pos_simple_fn_def,IN_SING,le_refl,GSYM extreal_of_num_def,mul_lzero,EXTREAL_SUM_IMAGE_0])
  ++ (MP_TAC o Q.SPEC `e` o UNDISCH o Q.SPEC `s` o Q.SPEC `(\i. pos_simple_fn_integral m s' a (x i))` o INST_TYPE [alpha |-> beta]) EXTREAL_SUM_IMAGE_PROPERTY
  ++ `!x'. x' IN e INSERT s ==> (\i. pos_simple_fn_integral m s' a (x i)) x' <> NegInf`
        by (RW_TAC std_ss []
            ++ METIS_TAC [IN_INSERT,pos_simple_fn_integral_not_infty])
  ++ RW_TAC std_ss []
  ++ Q.PAT_X_ASSUM `!n f s a z. Q` (MP_TAC o Q.SPECL [`m`,`f`,`s'`,`a`,`x`])
  ++ FULL_SIMP_TAC std_ss [IN_INSERT]
  ++ RW_TAC std_ss []
  ++ Cases_on `s = {}`
  >> (RW_TAC real_ss [EXTREAL_SUM_IMAGE_EMPTY,REAL_SUM_IMAGE_THM,add_rzero]
      ++ METIS_TAC [])
  ++ FULL_SIMP_TAC std_ss []
  ++ `SIGMA (\i. pos_simple_fn_integral m s' a (x i)) s = pos_simple_fn_integral m s' a (\j. SIGMA (\i. x i j) s)`
      by METIS_TAC []
  ++ POP_ORW
  ++ `(\j. x e j + SIGMA (\i. x i j) s) = 
      (\j. x e j + (\j. SIGMA (\i. x i j) s) j)` by METIS_TAC []
  ++ POP_ORW
  ++(MATCH_MP_TAC o GSYM) pos_simple_fn_integral_add_alt
  ++ METIS_TAC []);

val pos_simple_fn_integral_sum_alt = store_thm
  ("pos_simple_fn_integral_sum_alt",
   ``!m f s a x P. measure_space m /\
	(!i. i IN P ==> pos_simple_fn m (f i) (s i) (a i) (x i)) /\
	(!i t. i IN P ==> f i t <> NegInf) /\ FINITE P /\ P <> {} ==>
        ?c k z. (pos_simple_fn m (\t. SIGMA (\i. f i t) P) k c z /\
		(pos_simple_fn_integral m k c z =
		 SIGMA (\i. pos_simple_fn_integral m (s i) (a i) (x i)) P))``,

  Suff `!P:'b->bool. FINITE P ==>
        (\P:'b->bool. !m f s a x. measure_space m /\ (!i. i IN P ==> pos_simple_fn m (f i) (s i) (a i) (x i)) /\
	(!i t. i IN P ==> f i t <> NegInf) /\ P <> {} ==>
        ?c k z. (pos_simple_fn m (\t. SIGMA (\i. f i t) P) k c z /\
		(pos_simple_fn_integral m k c z =
		 SIGMA (\i. pos_simple_fn_integral m (s i) (a i) (x i)) P))) P`
  >> METIS_TAC []
  ++ MATCH_MP_TAC FINITE_INDUCT
  ++ RW_TAC std_ss []
  ++ Cases_on `s = {}` >> (RW_TAC std_ss [EXTREAL_SUM_IMAGE_SING] ++ METIS_TAC [IN_SING])
  ++ `?c k z. pos_simple_fn m (\t. SIGMA (\i. f i t) s) k c z /\
        (pos_simple_fn_integral m k c z =
         SIGMA (\i. pos_simple_fn_integral m (s' i) (a i) (x i)) s)`
        by METIS_TAC [IN_INSERT]  
  ++ `!i. i IN e INSERT s ==> (\i. pos_simple_fn_integral m (s' i) (a i) (x i)) i <> NegInf` 
       by METIS_TAC [pos_simple_fn_integral_not_infty,IN_INSERT]
  ++ FULL_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_PROPERTY]
  ++ (MP_TAC o Q.SPECL [`m`,`f (e:'b)`,`s' (e:'b)`,`a (e:'b)`,`x (e:'b)`,`(\t. SIGMA (\i:'b. f i t) s)`,`k`,`c`,`z`]) pos_simple_fn_integral_present
  ++ FULL_SIMP_TAC std_ss [IN_INSERT,DELETE_NON_ELEMENT]
  ++ RW_TAC std_ss [] 
  ++ METIS_TAC [pos_simple_fn_integral_add]);

val psfis_sum = store_thm
  ("psfis_sum",
   ``!m f a P.	measure_space m /\ (!i. i IN P ==> a i IN psfis m (f i)) /\
	 (!i t. i IN P ==> f i t <> NegInf) /\ FINITE P ==>
	(SIGMA a P) IN psfis m (\t. SIGMA (\i. f i t) P)``,
  Suff `!P:'b->bool. FINITE P ==>
        (\P:'b->bool. !m f a. measure_space m /\ (!i. i IN P ==> a i IN psfis m (f i)) /\
	 (!i t. i IN P ==> f i t <> NegInf) ==>
	(SIGMA a P) IN psfis m (\t. SIGMA (\i. f i t) P)) P`
  >> METIS_TAC []
  ++ MATCH_MP_TAC FINITE_INDUCT
  ++ RW_TAC std_ss [EXTREAL_SUM_IMAGE_EMPTY,psfis_zero,DELETE_NON_ELEMENT, IN_INSERT]
  ++ `!x. x IN e INSERT s ==> a x <> NegInf` by METIS_TAC [IN_INSERT,psfis_not_infty]
  ++ `!x t. x IN e INSERT s ==> (\x. f x t) x <> NegInf` by METIS_TAC [IN_INSERT]
  ++ `!t. (\i. f i t) = (\i. (\i. f i t) i)` by METIS_TAC []
  ++ POP_ORW
  ++ RW_TAC std_ss [EXTREAL_SUM_IMAGE_PROPERTY]
  ++ `(\t. f e t + SIGMA (\i. f i t) s) = (\t. f e t + (\t. SIGMA (\i. f i t) s) t)`
       by METIS_TAC []
  ++ POP_ORW
  ++ MATCH_MP_TAC psfis_add
  ++ RW_TAC std_ss []);

val psfis_intro = store_thm
 ("psfis_intro",
   ``!m a x P. measure_space m /\ (!i. i IN P ==> a i IN measurable_sets m) /\ (!i. i IN P ==> 0 <= x i) /\ 
	FINITE P ==> (SIGMA (\i. Normal (x i) * measure m (a i)) P) IN psfis m (\t. SIGMA (\i. Normal (x i) * indicator_fn (a i) t) P)``,
  RW_TAC std_ss []
  ++ `!t. (\i. Normal (x i) * indicator_fn (a i) t) =
	   (\i. (\i t. Normal (x i) * indicator_fn (a i) t) i t)`
	by METIS_TAC []
  ++ POP_ORW
  ++ MATCH_MP_TAC psfis_sum
  ++ RW_TAC std_ss []
  >> METIS_TAC [psfis_cmul, psfis_indicator]
  ++ RW_TAC std_ss [indicator_fn_def,mul_rone,mul_rzero]
  ++ METIS_TAC [extreal_of_num_def,extreal_not_infty]);

val pos_simple_fn_integral_sub = store_thm
  ("pos_simple_fn_integral_sub",
   ``!m f s a x g s' b y.
	measure_space m /\ (measure m (m_space m) <> PosInf) /\ 
	(!x. g x <= f x) /\ (!x. g x <> PosInf) /\ 
	pos_simple_fn m f s a x /\ pos_simple_fn m g s' b y ==>
	?s'' c z. pos_simple_fn m (\x. f x - g x) s'' c z /\
		(pos_simple_fn_integral m s a x -
		 pos_simple_fn_integral m s' b y =
		 pos_simple_fn_integral m s'' c z)``,
   REPEAT STRIP_TAC
   ++ (MP_TAC o Q.SPECL [`m`,`f`,`s`,`a`,`x`,`g`,`s'`,`b`,`y`]) pos_simple_fn_integral_present
   ++ RW_TAC std_ss [] ++ ASM_SIMP_TAC std_ss []
   ++ Q.EXISTS_TAC `k` 
   ++ Q.EXISTS_TAC `c` 
   ++ Q.EXISTS_TAC `(\i. if (i IN k /\ ~(c i = {})) then (z i - z' i) else 0)`
   ++ FULL_SIMP_TAC std_ss [pos_simple_fn_def, pos_simple_fn_integral_def]
   ++ `pos_simple_fn m f k c z` by FULL_SIMP_TAC std_ss [pos_simple_fn_def]
   ++ `pos_simple_fn m g k c z'` by FULL_SIMP_TAC std_ss [pos_simple_fn_def]
   ++ `!x. k x = x IN k` by METIS_TAC [SPECIFICATION]
   ++ `!x. x IN k ==> Normal (z x - z' x) * measure m (c x) <> NegInf`
         by (RW_TAC std_ss []
             ++ Cases_on `c x' = {}` >> METIS_TAC [MEASURE_EMPTY,mul_rzero,extreal_of_num_def,extreal_not_infty]
             ++ `?y. y IN c x'` by METIS_TAC [CHOICE_DEF]
	     ++ `f y' = Normal (z x')` by METIS_TAC [pos_simple_fn_def,pos_simple_fn_thm1]
	     ++ `g y' = Normal (z' x')` by METIS_TAC [pos_simple_fn_def,pos_simple_fn_thm1]
             ++ `0 <= z x' - z' x'` by METIS_TAC [extreal_le_def,REAL_SUB_LE,extreal_of_num_def]
             ++ METIS_TAC [mul_not_infty,positive_not_infty,MEASURE_SPACE_POSITIVE])
   ++ REVERSE CONJ_TAC
   >> (`!i. (Normal (if (i IN k /\ ~(c i = {})) then z i - z' i else 0) * measure m (c i)) = 
	(Normal (if i IN k then z i - z' i else 0) * measure m (c i))`
		by (RW_TAC std_ss [] ++ FULL_SIMP_TAC real_ss [MEASURE_EMPTY,mul_rzero])
	++ POP_ORW
	++ `SIGMA (\i. Normal (if i IN k then z i - z' i else 0) * measure m (c i)) k = 
	    SIGMA (\i. Normal (z i - z' i) * measure m (c i)) k`
	      by ((MP_TAC o REWRITE_RULE [SPECIFICATION] o Q.SPECL [`k`,`k`,`(\i. Normal (z i - z' i) * measure m (c i))`])(INST_TYPE [alpha |-> ``:num``] EXTREAL_SUM_IMAGE_IF_ELIM)
		  ++ RW_TAC real_ss []
                  ++ `(\x. if x IN k then Normal (z x - z' x) * measure m (c x) else 0) = 
                      (\i. Normal (if i IN k then z i - z' i else 0) * measure m (c i))` 
                        by (RW_TAC real_ss [FUN_EQ_THM]
		            ++ Cases_on `i IN k` >> METIS_TAC []
			    ++ RW_TAC real_ss [mul_lzero, GSYM extreal_of_num_def])
		  ++ FULL_SIMP_TAC real_ss [])
       ++ POP_ORW
       ++ RW_TAC std_ss [GSYM extreal_sub_def]
       ++ `!i. i IN k ==> measure m (c i) <= measure m (m_space m)` by METIS_TAC [INCREASING,MEASURE_SPACE_INCREASING,MEASURE_SPACE_MSPACE_MEASURABLE,MEASURE_SPACE_SUBSET_MSPACE]
       ++ `!i. i IN k ==> measure m (c i) <> PosInf` by METIS_TAC [le_infty]
       ++ (MP_TAC o Q.SPEC `(\i. (Normal (z i) - Normal (z' i)) * measure m (c i))` o UNDISCH o Q.ISPEC `k:num->bool`) EXTREAL_SUM_IMAGE_IN_IF
       ++ `!x. x IN k ==> (\i. (Normal (z i) - Normal (z' i)) * measure m (c i)) x <> NegInf`
            by RW_TAC std_ss [extreal_sub_def]
       ++ RW_TAC std_ss []
       ++ `!x. x IN k ==> ((Normal (z x) - Normal (z' x)) * measure m (c x) = 
             Normal (z x) * measure m (c x) - Normal (z' x) *  measure m (c x))`
                by (RW_TAC std_ss []
                    ++ `measure m (c x') <> NegInf` by METIS_TAC [positive_not_infty,MEASURE_SPACE_POSITIVE]
                    ++ `?r. measure m (c x') = Normal r` by METIS_TAC [extreal_cases]
                    ++ RW_TAC std_ss [extreal_sub_def,extreal_mul_def,REAL_SUB_RDISTRIB])
       ++ (MP_TAC o Q.SPECL [`k:num->bool`,`k`,`(\x:num. Normal (z x) * measure m (c x) - Normal (z' x) * measure m (c x))`] o INST_TYPE [alpha |-> ``:num``]) EXTREAL_SUM_IMAGE_IF_ELIM
       ++ RW_TAC std_ss []
       ++ FULL_SIMP_TAC std_ss []
       ++ `(\x. Normal (z x) * measure m (c x) - Normal (z' x) * measure m (c x)) =
           (\x. (\x. Normal (z x) * measure m (c x)) x - (\x. Normal (z' x) * measure m (c x)) x)` by METIS_TAC []
												 
       ++ POP_ORW
       ++ (MATCH_MP_TAC o UNDISCH o Q.SPEC `k` o GSYM o INST_TYPE [alpha |-> ``:num``]) EXTREAL_SUM_IMAGE_SUB
       ++ DISJ1_TAC 
       ++ RW_TAC std_ss []
       >> METIS_TAC [mul_not_infty,positive_not_infty,MEASURE_SPACE_POSITIVE]
       ++ METIS_TAC [mul_not_infty])
  ++ `!x. g x <> NegInf` by METIS_TAC [lt_infty,lte_trans,extreal_not_infty,extreal_of_num_def]
  ++ CONJ_TAC 
  >> METIS_TAC [le_sub_imp,add_lzero]
  ++ REVERSE (RW_TAC real_ss [])
  >> (`?q. q IN c i` by METIS_TAC [CHOICE_DEF]
      ++ METIS_TAC [pos_simple_fn_thm1,REAL_SUB_LE,extreal_le_def])
  ++ `!i. (Normal (if (i IN k /\ ~(c i = {})) then z i - z' i else 0) * indicator_fn (c i) x') = 
	(Normal (if i IN k then z i - z' i else 0) * indicator_fn (c i) x')`
	by (RW_TAC std_ss [] ++ FULL_SIMP_TAC real_ss [indicator_fn_def,mul_rzero,mul_rone,NOT_IN_EMPTY])
  ++ POP_ORW

  ++ `SIGMA (\i. Normal (if i IN k then z i - z' i else 0) * indicator_fn (c i) x') k = 
      SIGMA (\i. Normal (z i - z' i) * indicator_fn (c i) x') k`
         by ((MP_TAC o REWRITE_RULE [SPECIFICATION] o Q.SPECL [`k`,`k`,`(\i. Normal (z i - z' i) * indicator_fn (c i) x')`])(INST_TYPE [alpha |-> ``:num``] EXTREAL_SUM_IMAGE_IF_ELIM)
	     ++ RW_TAC real_ss []
	     ++ `!x. (\i. Normal (z i - z' i) * indicator_fn (c i) x') x <> NegInf`
                  by (RW_TAC std_ss [indicator_fn_def,mul_rzero,mul_rone]
                      ++ RW_TAC std_ss [extreal_of_num_def,extreal_not_infty])
             ++ RW_TAC std_ss []
             ++ `(\x. if x IN k then Normal (z x - z' x) * indicator_fn (c x) x' else 0) = 
                 (\i. Normal (if i IN k then z i - z' i else 0) * indicator_fn (c i) x')` 
                   by (RW_TAC real_ss [FUN_EQ_THM,indicator_fn_def,mul_rzero,mul_rone]
	               ++ Cases_on `i IN k` >> METIS_TAC []
		       ++ RW_TAC real_ss [mul_lzero, GSYM extreal_of_num_def])
	     ++ FULL_SIMP_TAC real_ss [])
  ++ POP_ORW
  ++ RW_TAC std_ss [GSYM extreal_sub_def]
  ++ (MP_TAC o Q.SPEC `(\i. (Normal (z i) - Normal (z' i)) * indicator_fn (c i) x')` o UNDISCH o Q.ISPEC `k:num->bool`) EXTREAL_SUM_IMAGE_IN_IF
  ++ `!x. x IN k ==> (\i. (Normal (z i) - Normal (z' i)) * indicator_fn (c i) x') x <> NegInf`
        by (RW_TAC std_ss [extreal_sub_def,indicator_fn_def,mul_rzero,mul_rone]
            ++ RW_TAC std_ss [extreal_of_num_def,extreal_not_infty])
  ++ RW_TAC std_ss []
  ++ `!x. x IN k ==> ((Normal (z x) - Normal (z' x)) * indicator_fn (c x) x' = 
         Normal (z x) *  indicator_fn (c x) x' - Normal (z' x) *   indicator_fn (c x) x')`
            by RW_TAC std_ss [indicator_fn_def,mul_rone,mul_rzero,sub_rzero]
  ++ RW_TAC std_ss []
  ++ NTAC 3 (POP_ASSUM (K ALL_TAC))

  ++ (MP_TAC o Q.SPEC `(\x:num. Normal (z x) * indicator_fn (c x) x' - Normal (z' x) * indicator_fn (c x) x')` o UNDISCH o Q.SPEC `k` o GSYM o INST_TYPE [alpha |-> ``:num``]) EXTREAL_SUM_IMAGE_IN_IF
  ++ `!x. NegInf <> (\x. Normal (z x) * indicator_fn (c x) x' - Normal (z' x) * indicator_fn (c x) x') x`
        by (RW_TAC std_ss [indicator_fn_def,mul_rone,mul_rzero,sub_rzero,extreal_sub_def]
            ++ RW_TAC std_ss [extreal_of_num_def,extreal_not_infty])
  ++ RW_TAC std_ss []
  ++ FULL_SIMP_TAC std_ss []
  ++ `SIGMA (\i. Normal (x i) * indicator_fn (a i) x') s = 
      SIGMA (\i. Normal (z i) * indicator_fn (c i) x') k` by METIS_TAC []
  ++ `SIGMA (\i. Normal (y i) * indicator_fn (b i) x') s' = 
      SIGMA (\i. Normal (z' i) * indicator_fn (c i) x') k` by METIS_TAC []
  ++ POP_ORW
  ++ POP_ORW
  ++ `(\x. Normal (z x) * indicator_fn (c x) x' - Normal (z' x) * indicator_fn (c x) x') =
      (\x. (\x. Normal (z x) * indicator_fn (c x) x') x - (\x. Normal (z' x) * indicator_fn (c x) x') x)` by METIS_TAC []
  ++ POP_ORW
  ++ (MATCH_MP_TAC o UNDISCH o Q.SPEC `k` o GSYM o INST_TYPE [alpha |-> ``:num``]) EXTREAL_SUM_IMAGE_SUB
  ++ DISJ1_TAC 
  ++ RW_TAC std_ss [indicator_fn_def,mul_rzero,mul_rone]
  ++ RW_TAC std_ss [extreal_of_num_def,extreal_not_infty]);

val psfis_sub = store_thm
  ("psfis_sub",
   ``!m f g a b.
	measure_space m /\ measure m (m_space m) <> PosInf /\ (!x. g x <= f x) /\ (!x. g x <> PosInf) /\ 
	a IN psfis m f /\ b IN psfis m g ==>
	a - b IN psfis m (\x. f x - g x)``,
   RW_TAC std_ss [psfis_def, IN_IMAGE, psfs_def, GSPECIFICATION]
   ++ Cases_on `x'` ++ Cases_on `x` ++ Cases_on `x''` ++ Cases_on `x'''`
   ++ RW_TAC std_ss []
   ++ Cases_on `r'` ++ Cases_on `r` ++ Cases_on `r''` ++ Cases_on `r'''`
   ++ RW_TAC std_ss []
   ++ FULL_SIMP_TAC std_ss [PAIR_EQ]
   ++ Suff `?s a x. (pos_simple_fn_integral m q q''''' r' -
		      pos_simple_fn_integral m q''' q''''''' r'' =
		      pos_simple_fn_integral m s a x) /\
	    pos_simple_fn m (\x. f x - g x) s a x`
   >> (RW_TAC std_ss [] ++ Q.EXISTS_TAC `(s,a,x)`
       ++ RW_TAC std_ss [] ++ Q.EXISTS_TAC `(s,a,x)`
       ++ RW_TAC std_ss [PAIR_EQ])
   ++ ONCE_REWRITE_TAC [CONJ_COMM]
   ++ MATCH_MP_TAC pos_simple_fn_integral_sub ++ RW_TAC std_ss []);

(* ---------------------------------------------------- *)
(* Properties of Integrals of Positive Functions        *)
(* ---------------------------------------------------- *)

val pos_fn_integral_pos_simple_fn = store_thm
("pos_fn_integral_pos_simple_fn",``!m f s a x. measure_space m /\ pos_simple_fn m f s a x ==> (pos_fn_integral m f = pos_simple_fn_integral m s a x)``,
  RW_TAC std_ss [pos_fn_integral_def,sup_eq,IN_psfis_eq]
  >> (POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION]) 
      ++ RW_TAC std_ss [GSPECIFICATION]
      ++ METIS_TAC [pos_simple_fn_integral_mono])
  ++ POP_ASSUM MATCH_MP_TAC
  ++ ONCE_REWRITE_TAC [GSYM SPECIFICATION]
  ++ RW_TAC std_ss [GSPECIFICATION]
  ++ METIS_TAC [le_refl]);
 
val pos_fn_integral_mspace = store_thm
  ("pos_fn_integral_mspace",``!m f. measure_space m  /\ (!x. 0 <= f x)
	 ==> (pos_fn_integral m f = pos_fn_integral m (\x. f x * indicator_fn (m_space m) x))``,
  RW_TAC std_ss [pos_fn_integral_def,sup_eq]
  >> (RW_TAC real_ss [le_sup] 
      ++ POP_ASSUM MATCH_MP_TAC
      ++ ONCE_REWRITE_TAC [GSYM SPECIFICATION]
      ++ POP_ASSUM (MP_TAC o REWRITE_RULE [Once (GSYM SPECIFICATION)])
      ++ RW_TAC real_ss [GSPECIFICATION,indicator_fn_def]
      ++ Q.EXISTS_TAC `(\x. g x * indicator_fn (m_space m) x)`
      ++ REVERSE (RW_TAC real_ss [indicator_fn_def,IN_psfis_eq,mul_rone,mul_rzero,le_refl])
      ++ FULL_SIMP_TAC std_ss [IN_psfis_eq,pos_simple_fn_def]
      ++ Q.EXISTS_TAC `s`
      ++ Q.EXISTS_TAC `a`
      ++ Q.EXISTS_TAC `x`
      ++ RW_TAC real_ss [mul_rzero,le_refl,mul_rone]
      ++ MATCH_MP_TAC EXTREAL_SUM_IMAGE_POS
      ++ RW_TAC std_ss [mul_rzero,le_refl,mul_rone,indicator_fn_def]
      ++ METIS_TAC [extreal_of_num_def,extreal_le_def])
  ++ RW_TAC real_ss [sup_le] 
  ++ POP_ASSUM (MP_TAC o REWRITE_RULE [Once (GSYM SPECIFICATION)])
  ++ RW_TAC real_ss [GSPECIFICATION]
  ++ Q.PAT_X_ASSUM `!z. Q z ==> z <= y` MATCH_MP_TAC
  ++ RW_TAC std_ss [Once (GSYM SPECIFICATION),GSPECIFICATION]
  ++ Q.EXISTS_TAC `(\x. g x * indicator_fn (m_space m) x)`
  ++ RW_TAC std_ss [IN_psfis_eq]
  >> (FULL_SIMP_TAC real_ss [IN_psfis_eq,pos_simple_fn_def,indicator_fn_def] 
      ++ Q.EXISTS_TAC `s`
      ++ Q.EXISTS_TAC `a`
      ++ Q.EXISTS_TAC `x`
      ++ RW_TAC real_ss [le_refl,mul_rzero,mul_rone]
      ++MATCH_MP_TAC EXTREAL_SUM_IMAGE_POS
      ++ RW_TAC std_ss [mul_rzero,le_refl,mul_rone,indicator_fn_def]
      ++ METIS_TAC [extreal_of_num_def,extreal_le_def])
  ++ FULL_SIMP_TAC std_ss [indicator_fn_def,le_refl,mul_rzero,mul_rone]
  ++ METIS_TAC [mul_rone,mul_rzero]);

val pos_fn_integral_zero = store_thm
("pos_fn_integral_zero",``!m. measure_space m ==> (pos_fn_integral m (\x. 0) = 0)``,
  RW_TAC std_ss [pos_fn_integral_def,sup_eq]
  >> (POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
      ++ RW_TAC std_ss [GSPECIFICATION]
      ++ MATCH_MP_TAC psfis_mono
      ++ Q.EXISTS_TAC `m` ++ Q.EXISTS_TAC `g` ++ Q.EXISTS_TAC `(\x. 0)`
      ++ RW_TAC std_ss [psfis_zero])
  ++ POP_ASSUM MATCH_MP_TAC
  ++ ONCE_REWRITE_TAC [GSYM SPECIFICATION]
  ++ RW_TAC std_ss [GSPECIFICATION]
  ++ Q.EXISTS_TAC `(\x. 0)`
  ++ RW_TAC std_ss [le_refl,psfis_zero]);

val pos_fn_integral_mono = store_thm
("pos_fn_integral_mono",``!f g. ((!x. 0 <= f x /\ f x <= g x) ==> (pos_fn_integral m f <= pos_fn_integral m g))``,
  RW_TAC std_ss [pos_fn_integral_def]
  ++ MATCH_MP_TAC sup_le_sup_imp
  ++ RW_TAC std_ss []
  ++ Q.EXISTS_TAC `x`
  ++ RW_TAC std_ss [le_refl]
  ++ `x IN {r | ?g. r IN psfis m g /\ !x. g x <= f x}` by METIS_TAC [IN_DEF]
  ++ ONCE_REWRITE_TAC [GSYM SPECIFICATION]
  ++ `?g. x IN psfis m g /\ !x. g x <= f x` by (FULL_SIMP_TAC std_ss [GSPECIFICATION] ++ METIS_TAC [])
  ++ FULL_SIMP_TAC std_ss [GSPECIFICATION]
  ++ METIS_TAC [le_trans]);

val pos_fn_integral_mono_mspace = store_thm
  ("pos_fn_integral_mono_mspace",``!m f g. measure_space m /\ (!x. x IN m_space m ==> g x <= f x) /\ 
   (!x. 0 <= f x) /\ (!x. 0 <= g x) ==> (pos_fn_integral m g <= pos_fn_integral m f)``,
  RW_TAC std_ss [Once pos_fn_integral_mspace]
  ++ `pos_fn_integral m f = pos_fn_integral m (\x. f x * indicator_fn (m_space m) x)`
      by RW_TAC std_ss [Once pos_fn_integral_mspace]
  ++ POP_ORW
  ++ MATCH_MP_TAC pos_fn_integral_mono
  ++ RW_TAC std_ss [indicator_fn_def,mul_rone,mul_rzero,le_refl]);

val pos_fn_integral_pos = store_thm
("pos_fn_integral_pos",``!m f. measure_space m /\ (!x. 0 <= f x) ==> 0 <= pos_fn_integral m f``,
  RW_TAC std_ss []
  ++ `0 = pos_fn_integral m (\x. 0)` by METIS_TAC [pos_fn_integral_zero]
  ++ POP_ORW
  ++ MATCH_MP_TAC pos_fn_integral_mono
  ++ RW_TAC std_ss [le_refl]);

val pos_fn_integral_cmul = store_thm
("pos_fn_integral_cmul",``!f c. measure_space m /\ (!x. x IN m_space m ==> 0 <= f x) /\ 0 <= c ==> (pos_fn_integral m (\x. Normal c * f x) =  Normal c * pos_fn_integral m f)``,
  RW_TAC std_ss []
  ++ Cases_on `c = 0`
  >> RW_TAC std_ss [GSYM extreal_of_num_def,mul_lzero,pos_fn_integral_zero]
  ++ `0 < c` by FULL_SIMP_TAC std_ss [REAL_LT_LE]
  ++ RW_TAC std_ss [pos_fn_integral_def,sup_eq]
  >> (Suff `y / (Normal c) <= sup {r | ?g. r IN psfis m g /\ !x. g x <= f x}`
      >> METIS_TAC [le_ldiv,mul_comm]
      ++ RW_TAC std_ss [le_sup]
      ++ POP_ASSUM MATCH_MP_TAC
      ++ ONCE_REWRITE_TAC [GSYM SPECIFICATION]
      ++ POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
      ++ RW_TAC std_ss [GSPECIFICATION]
      ++ Q.EXISTS_TAC `(\x. g x / (Normal c))`
      ++ REVERSE (RW_TAC std_ss [])
      >> METIS_TAC [mul_comm,le_ldiv]
      ++ RW_TAC std_ss [extreal_div_def]
	  ++ `inv (Normal c) * y IN psfis m (\x. inv (Normal c) * g x)` by METIS_TAC [psfis_cmul,extreal_inv_def,REAL_LE_INV]
          ++ `(\x. g x * inv (Normal c)) = (\x. inv (Normal c) * g x)` by RW_TAC std_ss [FUN_EQ_THM,mul_comm] 
          ++ RW_TAC std_ss [Once mul_comm])
  ++ Suff `sup {r | ?g. r IN psfis m g /\ !x. g x <= f x} <= y / Normal c`
  >> METIS_TAC [le_rdiv,extreal_not_infty,mul_comm]
  ++ RW_TAC std_ss [sup_le]
  ++ POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
  ++ RW_TAC std_ss [GSPECIFICATION]
  ++ Suff `y' * Normal c <= y` >> METIS_TAC [le_rdiv,extreal_not_infty]
  ++ Q.PAT_X_ASSUM `!z. {r | ?g. r IN psfis m g /\ !x. g x <= Normal c * f x} z ==>( z <= y)` MATCH_MP_TAC
  ++ ONCE_REWRITE_TAC [GSYM SPECIFICATION]
  ++ RW_TAC std_ss [GSPECIFICATION]
  ++ Q.EXISTS_TAC `(\x. Normal c * g x)`
  ++ RW_TAC std_ss []
  >> METIS_TAC [psfis_cmul,mul_comm,extreal_not_infty]
  ++ METIS_TAC [le_lmul_imp,extreal_of_num_def,extreal_lt_eq,lt_le]);

val pos_fn_integral_indicator = store_thm
  ("pos_fn_integral_indicator",
   ``!m s. measure_space m /\ s IN measurable_sets m ==>
	   (pos_fn_integral m (indicator_fn s) = measure m s)``,
  METIS_TAC [pos_fn_integral_pos_simple_fn,pos_simple_fn_integral_indicator]);

val pos_fn_integral_cmul_indicator = store_thm
  ("pos_fn_integral_cmul_indicator",
   ``!m s c. measure_space m /\ s IN measurable_sets m /\ 0 <= c ==>
	   (pos_fn_integral m (\x. Normal c * indicator_fn s x) = Normal c * measure m s)``,
  RW_TAC std_ss []
  ++ `!x. 0 <= indicator_fn s x` by RW_TAC std_ss [indicator_fn_def,le_refl,le_01]
  ++ RW_TAC std_ss [pos_fn_integral_cmul]
  ++ METIS_TAC [pos_fn_integral_pos_simple_fn,pos_simple_fn_integral_indicator]);

val pos_fn_integral_sum_cmul_indicator = store_thm
("pos_fn_integral_sum_cmul_indicator",
   ``!m s a x. measure_space m /\ FINITE s /\ (!i:num. i IN s ==> 0 <= x i) /\ 
            (!i:num. i IN s ==> a i IN measurable_sets m)  ==>
	   (pos_fn_integral m (\t. SIGMA (\i:num. Normal (x i) * indicator_fn (a i) t) s) = 
            SIGMA (\i. Normal (x i) * measure m (a i)) s)``,
  RW_TAC std_ss []
  ++ Cases_on `s = {}` >> RW_TAC std_ss [EXTREAL_SUM_IMAGE_EMPTY,pos_fn_integral_zero]
  ++ `!i. i IN s ==> pos_simple_fn m (indicator_fn (a i)) {0:num; 1} (\n. if n = 0 then m_space m DIFF (a i) else (a i)) (\n:num. if n = 0 then 0 else 1)` by METIS_TAC [pos_simple_fn_indicator_alt]
  ++ `!i. i IN s ==> pos_simple_fn m (\t. Normal (x i) * indicator_fn (a i) t) {0:num; 1} (\n:num. if n = 0 then m_space m DIFF (a i) else (a i)) (\n:num. (x i) * (if n = 0 then 0 else 1))` by METIS_TAC [pos_simple_fn_cmul_alt]
  ++ (MP_TAC o Q.SPECL [`m`,`(\i. (\t. Normal (x i) * indicator_fn (a i) t))`,`(\i. {0; 1})`,`(\i. (\n. if n = 0 then m_space m DIFF a i else a i))`,`(\i. (\n. x i * if n = 0 then 0 else 1))`,`s`] o INST_TYPE [beta |-> ``:num``]) pos_simple_fn_integral_sum_alt
  ++ `!i t. i IN s ==> Normal (x i) * indicator_fn (a i) t <> NegInf`
       by RW_TAC std_ss [indicator_fn_def,mul_rzero,mul_rone,num_not_infty]
  ++ RW_TAC std_ss []
  ++ `{1:num} DELETE 0 = {1}` by METIS_TAC [DELETE_NON_ELEMENT,EVAL ``0=1:num``,EXTENSION,IN_DELETE,IN_SING,NOT_IN_EMPTY]
  ++ `FINITE {1:num}` by RW_TAC std_ss [FINITE_SING]
  ++ `!i:num. i IN s ==> (pos_simple_fn_integral m {0:num; 1} (\n:num. if n = 0 then m_space m DIFF a i else a i) (\n:num. x i * if n = 0 then 0 else 1) = Normal (x i) * measure m (a i))`
       by (RW_TAC real_ss [pos_simple_fn_integral_def]
           ++ `!n:num. n IN {0;1} ==> (\n. Normal (x i * if n = 0 then 0 else 1) *
                         measure m (if n = 0 then m_space m DIFF a i else a i)) n <> NegInf`
                  by (RW_TAC real_ss [GSYM extreal_of_num_def,num_not_infty,mul_lzero]
		      ++ METIS_TAC [mul_not_infty,positive_not_infty,MEASURE_SPACE_POSITIVE,IN_INSERT])
           ++ (MP_TAC o Q.SPEC `0` o UNDISCH o Q.SPECL [`(\n. Normal (x (i:num) * if n = 0 then 0 else 1) * measure m (if n = 0 then m_space m DIFF a i else a i))`,`{1}`] o INST_TYPE [alpha |-> ``:num``]) EXTREAL_SUM_IMAGE_PROPERTY
           ++ RW_TAC real_ss [mul_lzero,add_lzero,EXTREAL_SUM_IMAGE_SING,GSYM extreal_of_num_def])
 
  ++ (MP_TAC o Q.SPEC `(\i:num. pos_simple_fn_integral m {0:num; 1} (\n:num. if n = 0 then m_space m DIFF a i else a i) (\n:num. x i * if n = 0 then 0 else 1:real))` o UNDISCH o Q.SPEC `s` o INST_TYPE [alpha |-> ``:num``]) EXTREAL_SUM_IMAGE_IN_IF
  ++ `!x'. x' IN s ==> (\i. pos_simple_fn_integral m {0; 1}
             (\n. if n = 0 then m_space m DIFF a i else a i)
             (\n. x i * if n = 0 then 0 else 1)) x' <> NegInf`
         by (RW_TAC std_ss []
             ++ METIS_TAC [mul_not_infty,positive_not_infty,MEASURE_SPACE_POSITIVE,IN_INSERT])
  ++ RW_TAC std_ss []
  ++ FULL_SIMP_TAC std_ss []
  ++ (MP_TAC o Q.SPECL [`s:num->bool`,`s`,`(\i:num. Normal (x i) * measure m (a i))`] o INST_TYPE [alpha |-> ``:num``]) EXTREAL_SUM_IMAGE_IF_ELIM
  ++ `!x'. x' IN s ==> Normal (x x') * measure m (a x') <> NegInf` by METIS_TAC [mul_not_infty,positive_not_infty,MEASURE_SPACE_POSITIVE,IN_INSERT]
  ++ RW_TAC std_ss []
  ++ FULL_SIMP_TAC std_ss [SPECIFICATION]
  ++ NTAC 7 (POP_ASSUM (K ALL_TAC))
  ++ POP_ASSUM (MP_TAC o GSYM)
  ++ RW_TAC std_ss []
  ++ RW_TAC std_ss [pos_fn_integral_def,sup_eq]
  >> (POP_ASSUM  (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
      ++ RW_TAC std_ss [GSPECIFICATION,IN_psfis_eq]
      ++ MATCH_MP_TAC pos_simple_fn_integral_mono
      ++ Q.EXISTS_TAC `g`
      ++ Q.EXISTS_TAC `(\t. SIGMA (\i. Normal (x i) * indicator_fn (a i) t) s)`
      ++ RW_TAC std_ss [])
  ++ POP_ASSUM MATCH_MP_TAC
  ++ ONCE_REWRITE_TAC [GSYM SPECIFICATION]
  ++ RW_TAC std_ss [GSPECIFICATION,IN_psfis_eq]
  ++ Q.EXISTS_TAC `(\t. SIGMA (\i. Normal (x i) * indicator_fn (a i) t) s)`
  ++ RW_TAC real_ss []
  ++ METIS_TAC [le_refl]);


(***************************************************************************)
(*                       Sequences - Convergence                           *)
(***************************************************************************)

val pos_mono_conv_mono_borel = store_thm
  ("pos_mono_conv_mono_borel",
    ``!m f fi g r'.
	measure_space m /\
	(!i. fi i IN measurable (m_space m, measurable_sets m) Borel) /\
	(!x. mono_increasing (\i. fi i x)) /\
        (!x. x IN m_space m ==> (sup (IMAGE (\i. fi i x) UNIV) = f x)) /\
 	(r' IN psfis m g) /\ (!x. g x <= f x) /\ (!i x. 0 <= fi i x) ==>
	r' <= sup (IMAGE (\i. pos_fn_integral m (fi i)) UNIV)``,
  REPEAT STRIP_TAC
  ++ Q.ABBREV_TAC `r = sup (IMAGE (\i. pos_fn_integral m (fi i)) UNIV)`
  ++ Q.ABBREV_TAC `ri = (\i. pos_fn_integral m (fi i))`
  ++ MATCH_MP_TAC le_mul_epsilon
  ++ RW_TAC std_ss []
  ++ (Cases_on `z` ++ FULL_SIMP_TAC std_ss [le_infty,lt_infty,extreal_not_infty,extreal_of_num_def])
  ++ FULL_SIMP_TAC std_ss [extreal_le_def,extreal_lt_eq]
  ++ Q.ABBREV_TAC `b = \n. {t | Normal r'' * g t <= (fi n) t}`
  ++ `?s a x. pos_simple_fn m g s a x` by METIS_TAC [IN_psfis]
  ++ `!i j. i <= j ==> ri i <= ri j` 
      by (Q.UNABBREV_TAC `ri` 
          ++ RW_TAC std_ss [] 
          ++ MATCH_MP_TAC pos_fn_integral_mono 
	  ++ FULL_SIMP_TAC std_ss [ext_mono_increasing_def, GSYM extreal_of_num_def])
  ++ `f IN measurable (m_space m, measurable_sets m) Borel` 
      by (MATCH_MP_TAC IN_MEASURABLE_BOREL_MONO_SUP
          ++ Q.EXISTS_TAC `fi`
	  ++ RW_TAC std_ss [space_def]
	  >> FULL_SIMP_TAC std_ss [measure_space_def]
	  ++ FULL_SIMP_TAC std_ss [ext_mono_increasing_def,ext_mono_increasing_suc])
  ++ `g IN measurable (m_space m, measurable_sets m) Borel` by METIS_TAC [IN_psfis_eq,IN_MEASURABLE_BOREL_POS_SIMPLE_FN]
  ++ `(\t. Normal r'' * g t) IN measurable (m_space m, measurable_sets m) Borel`
	by ( MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL
	     ++ Q.EXISTS_TAC `g` ++ Q.EXISTS_TAC `r''`
	     ++ RW_TAC real_ss [extreal_not_infty]
	     ++ METIS_TAC [measure_space_def])
  ++ `!n:num. {t | Normal r'' * g t <= fi n t} INTER m_space m = {t | 0 <= (fi n t) - Normal r'' * (g t)} INTER m_space m` 
	by (RW_TAC real_ss [EXTENSION,GSPECIFICATION,IN_INTER]
            ++ METIS_TAC [pos_simple_fn_not_infty,mul_not_infty,add_lzero,le_sub_eq,num_not_infty])
  ++ `!n. (\t. fi n t - Normal r'' * g t) IN measurable (m_space m, measurable_sets m) Borel` 
	by ( RW_TAC std_ss [] 
      	     ++ MATCH_MP_TAC IN_MEASURABLE_BOREL_SUB
	     ++ Q.EXISTS_TAC `fi n`
	     ++ Q.EXISTS_TAC `(\t. Normal r'' * g t)`
	     ++ RW_TAC std_ss [space_def]
             << [FULL_SIMP_TAC std_ss [measure_space_def],
		 METIS_TAC [lt_infty,lte_trans,extreal_not_infty,extreal_of_num_def],
		 METIS_TAC [pos_simple_fn_not_infty,mul_not_infty]])
  ++ `!n. {t | Normal r'' * g t <= fi n t} INTER m_space m IN measurable_sets m` 
	by METIS_TAC [IN_MEASURABLE_BOREL_ALL,m_space_def,space_def,
			subsets_def,measurable_sets_def,measure_space_def,extreal_of_num_def]
  ++ `!n. b n INTER m_space m IN measurable_sets m` by ( Q.UNABBREV_TAC `b` ++ METIS_TAC [])
  ++ Suff  `r' = sup (IMAGE (\n. pos_fn_integral m (\x. g x * indicator_fn (b n INTER m_space m) x)) UNIV )`
  >> (Q.UNABBREV_TAC `r`
      ++ RW_TAC std_ss [le_sup]
      ++ Cases_on `r'' = 0` 
      >> (RW_TAC std_ss [mul_lzero,GSYM extreal_of_num_def]
          ++ MATCH_MP_TAC le_trans
	  ++ Q.EXISTS_TAC `ri (1:num)`
	  ++ REVERSE (RW_TAC std_ss [])
	  >> (POP_ASSUM MATCH_MP_TAC
              ++ ONCE_REWRITE_TAC [GSYM SPECIFICATION]
	      ++ RW_TAC std_ss [IN_IMAGE,IN_UNIV]
	      ++ METIS_TAC [])
	  ++ Q.UNABBREV_TAC `ri`
	  ++ RW_TAC std_ss []
	  ++ METIS_TAC [pos_fn_integral_pos,extreal_of_num_def])
      ++ `0 < r''` by METIS_TAC [REAL_LT_LE]
      ++ `0 < Normal r''` by METIS_TAC [extreal_lt_eq,extreal_of_num_def,REAL_LE_REFL]
      ++ ONCE_REWRITE_TAC [mul_comm]
      ++ RW_TAC std_ss [le_rdiv]
      ++ RW_TAC std_ss [sup_le]
      ++ POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
      ++ RW_TAC std_ss [IN_IMAGE,IN_UNIV]
      ++ RW_TAC std_ss [GSYM le_rdiv]
      ++ ONCE_REWRITE_TAC [mul_comm]
      ++ `!x. 0 <= (\x. g x * indicator_fn (b n INTER m_space m) x) x`
            by (RW_TAC std_ss [indicator_fn_def,mul_rone,mul_rzero,le_refl]
                ++ FULL_SIMP_TAC std_ss [pos_simple_fn_def])
      ++ FULL_SIMP_TAC std_ss [GSYM pos_fn_integral_cmul]
      ++ `!x. (\x. Normal r'' * (g x * indicator_fn (b n INTER m_space m) x)) x <= fi n x`
            by (Q.UNABBREV_TAC `b`
                ++ RW_TAC real_ss [indicator_fn_def,GSPECIFICATION,IN_INTER,mul_rzero,mul_rone]
		++ METIS_TAC [extreal_of_num_def])
      ++ MATCH_MP_TAC le_trans
      ++ Q.EXISTS_TAC `pos_fn_integral m (fi n)`
      ++ CONJ_TAC >> (MATCH_MP_TAC pos_fn_integral_mono ++ METIS_TAC [le_mul,lt_le])
      ++ RW_TAC std_ss []
      ++ Q.PAT_X_ASSUM `!z. IMAGE ri UNIV z ==> z <= y'` MATCH_MP_TAC
      ++ ONCE_REWRITE_TAC [GSYM SPECIFICATION]
      ++ RW_TAC std_ss [IN_IMAGE,IN_UNIV]
      ++ Q.EXISTS_TAC `n`
      ++ Q.UNABBREV_TAC `ri`
      ++ RW_TAC std_ss [])
  ++ `!n:num. (\x. g x * indicator_fn (b n INTER m_space m) x) = 
      (\t. SIGMA (\i. Normal (x i) * indicator_fn (a i INTER (b n INTER m_space m)) t) s)`
        by (RW_TAC std_ss [] ++ FUN_EQ_TAC
	    ++ RW_TAC std_ss []
	    ++ Cases_on `~(x' IN m_space m)`
	    >> (RW_TAC real_ss [indicator_fn_def,IN_INTER,mul_rone,mul_rzero] ++ METIS_TAC [pos_simple_fn_def,EXTREAL_SUM_IMAGE_ZERO])
	    ++ RW_TAC real_ss [indicator_fn_def,IN_INTER,mul_rone,mul_rzero]
	    >> FULL_SIMP_TAC real_ss [pos_simple_fn_def,indicator_fn_def]
	    ++ FULL_SIMP_TAC std_ss [pos_simple_fn_def,EXTREAL_SUM_IMAGE_ZERO])
  ++ RW_TAC std_ss []
  ++ `!n:num i. i IN s ==> (a i INTER (b n INTER m_space m)) IN measurable_sets m`
         by METIS_TAC [MEASURE_SPACE_INTER,pos_simple_fn_def] 
  ++ `FINITE s` by FULL_SIMP_TAC std_ss [pos_simple_fn_def]
  ++ `!n:num. (pos_fn_integral m (\t. SIGMA (\i. Normal (x i) * indicator_fn ((\i. a i INTER (b n INTER m_space m)) i) t) s) =
           SIGMA (\i. Normal (x i) * measure m ((\i. a i INTER (b n INTER m_space m)) i)) s)`
              by (RW_TAC std_ss [] 
	          ++ (MP_TAC o Q.SPECL [`m`,`s:num->bool`,`(\i:num. a i INTER (b (n:num) INTER m_space m))`,`(x:num->real)`]) pos_fn_integral_sum_cmul_indicator
		  ++ FULL_SIMP_TAC std_ss [pos_simple_fn_def])
  ++ FULL_SIMP_TAC std_ss []
  ++ Know `!i. i IN s ==> !n.
            (\i n. Normal (x i) * measure m (a i INTER (b n INTER m_space m))) i n <=  
	    (\i n. Normal (x i) * measure m (a i INTER (b n INTER m_space m))) i (SUC n)`
  >> (RW_TAC std_ss []
      ++ MATCH_MP_TAC le_lmul_imp
      ++ RW_TAC std_ss []
      >> METIS_TAC [pos_simple_fn_def,extreal_le_def,extreal_of_num_def]
      ++ MATCH_MP_TAC INCREASING
      ++ RW_TAC std_ss [MEASURE_SPACE_INCREASING]
      ++ RW_TAC std_ss [SUBSET_DEF,IN_INTER]
      ++ Q.UNABBREV_TAC `b`
      ++ FULL_SIMP_TAC std_ss [GSPECIFICATION]
      ++ MATCH_MP_TAC le_trans
      ++ Q.EXISTS_TAC `fi n x'`
      ++ RW_TAC real_ss []
      ++ FULL_SIMP_TAC real_ss [ext_mono_increasing_suc])
  ++ `!i. i IN s ==> !n. 0 <= (\i n. Normal (x i) * measure m (a i INTER (b n INTER m_space m))) i n`
         by (RW_TAC std_ss [] ++ METIS_TAC [le_mul,extreal_le_def,extreal_of_num_def,MEASURE_SPACE_POSITIVE,positive_def,MEASURE_SPACE_INTER,pos_simple_fn_def])
  ++ FULL_SIMP_TAC std_ss [sup_sum_mono]
  ++ RW_TAC std_ss []
  ++ `!i. i IN s ==> (sup (IMAGE (\n.  Normal (x i) * measure m (a i INTER (b n INTER m_space m))) UNIV) =
		       Normal (x i) * sup (IMAGE (\n. measure m (a i INTER (b n INTER m_space m))) UNIV))`
           by METIS_TAC [sup_cmul,pos_simple_fn_def]
  ++ (MP_TAC o Q.SPEC `(\i.sup (IMAGE (\n. Normal (x i) * measure m (a i INTER (b (n:num) INTER m_space m)))UNIV))` o UNDISCH o Q.SPEC `s` o INST_TYPE [alpha |-> ``:num``]) EXTREAL_SUM_IMAGE_IN_IF
  ++ `!x':num. x' IN s ==> (\i:num. sup (IMAGE (\n. Normal (x i) * measure m (a i INTER (b (n:num) INTER m_space m))) UNIV)) x' <> NegInf`
        by (RW_TAC std_ss [lt_infty]
            ++ MATCH_MP_TAC lte_trans
	    ++ Q.EXISTS_TAC `0`
	    ++ RW_TAC std_ss []
	    >> METIS_TAC [lt_infty,num_not_infty]
	    ++ RW_TAC std_ss [le_sup]
	    ++ MATCH_MP_TAC le_trans
	    ++ Q.EXISTS_TAC `Normal (x x') * measure m ((a x') INTER ((b 1) INTER m_space m))`
            ++ RW_TAC std_ss []
	    ++ MATCH_MP_TAC le_lmul_imp
	    ++ CONJ_TAC >> METIS_TAC [extreal_le_def,extreal_of_num_def,pos_simple_fn_def]
	    ++ RW_TAC std_ss [le_sup]
	    ++ POP_ASSUM MATCH_MP_TAC
	    ++ ONCE_REWRITE_TAC [GSYM SPECIFICATION]
	    ++ RW_TAC std_ss [IN_IMAGE,IN_UNIV]
	    ++ METIS_TAC [])
  ++ RW_TAC std_ss []
  ++ `!i. BIGUNION (IMAGE (\n. a i INTER (b n INTER m_space m)) UNIV) = a i INTER m_space m`
       by (RW_TAC std_ss [EXTENSION,IN_BIGUNION_IMAGE,IN_INTER,IN_UNIV]
           ++ EQ_TAC >> METIS_TAC []
	   ++ RW_TAC std_ss []
	   ++ Q.UNABBREV_TAC `b`
	   ++ RW_TAC real_ss [GSPECIFICATION]
	   ++ `f x' = sup (IMAGE (\i. fi i x') UNIV)` by FULL_SIMP_TAC std_ss []
	   ++ Cases_on `g x' = 0` >> METIS_TAC [mul_rzero,extreal_of_num_def]
           ++ `Normal r'' * g x' < f x'` 
                by (Cases_on `g x' = f x'`
                    >> (`0 < f x'` by METIS_TAC [le_lt,pos_simple_fn_def]
                        ++ METIS_TAC [lt_rmul,mul_lone,IN_psfis_eq,pos_simple_fn_not_infty,extreal_lt_eq,extreal_of_num_def])
		    ++ `g x' < f x'` by METIS_TAC [le_lt]
		    ++ METIS_TAC [lt_mul2,mul_lone,extreal_not_infty,pos_simple_fn_not_infty,extreal_lt_eq,extreal_of_num_def,extreal_le_def,psfis_pos])
	   ++ Suff `?n. Normal r'' * g x' <= (\n. fi n x') n` >> RW_TAC std_ss []
           ++ MATCH_MP_TAC sup_le_mono
	   ++ CONJ_TAC >> FULL_SIMP_TAC std_ss [ext_mono_increasing_def,ext_mono_increasing_suc]
	   ++ METIS_TAC []) 
  ++ `!i. i IN s==> (a i INTER m_space m = a i)`
       by METIS_TAC [pos_simple_fn_def,SUBSET_INTER1,MEASURE_SPACE_SUBSET_MSPACE]
  ++ `!i. i IN s ==> (sup (IMAGE (measure m o (\n. a i INTER (b n INTER m_space m))) UNIV) = measure m (a i))`
       by (RW_TAC std_ss []
           ++ MATCH_MP_TAC MONOTONE_CONVERGENCE
           ++ RW_TAC std_ss [IN_FUNSET,IN_UNIV]
           ++ RW_TAC std_ss [SUBSET_DEF,IN_INTER]
           ++ Q.UNABBREV_TAC `b`
           ++ FULL_SIMP_TAC std_ss [GSPECIFICATION]
           ++ MATCH_MP_TAC le_trans
           ++ Q.EXISTS_TAC `fi n x'`
           ++ RW_TAC real_ss []
           ++ FULL_SIMP_TAC real_ss [ext_mono_increasing_suc])
  ++ FULL_SIMP_TAC std_ss [o_DEF]
  ++ `r' = SIGMA (\i. Normal (x i) * measure m (a i)) s`
       by METIS_TAC [IN_psfis_eq,psfis_unique,pos_simple_fn_integral_def,pos_simple_fn_integral_unique]
  ++ POP_ORW
  ++ `!i. i IN s ==> (\i. Normal (x i) * measure m (a i)) i <> NegInf`
      by METIS_TAC [] 
  ++ (MP_TAC o Q.SPEC `(\i. Normal (x i) * measure m (a i))` o UNDISCH o Q.ISPEC `s:num->bool`) EXTREAL_SUM_IMAGE_IN_IF
  ++ RW_TAC std_ss []);

(************************************************************)
(* LEBESGUE MONOTONE CONVERGENCE *)
(************************************************************)

val lebesgue_monotone_convergence = store_thm
  ("lebesgue_monotone_convergence", ``!m f fi. measure_space m /\ 
	(!i. fi i IN measurable (m_space m, measurable_sets m) Borel) /\
        (!i x. 0 <= fi i x) /\ (!x. 0 <= f x) /\
	(!x. mono_increasing (\i. fi i x)) /\
	(!x. x IN m_space m ==> (sup (IMAGE (\i. fi i x) UNIV) = f x)) ==>
	(pos_fn_integral m f = sup (IMAGE (\i. pos_fn_integral m (fi i)) UNIV))``,
  REVERSE (RW_TAC std_ss [GSYM le_antisym])
  >> (RW_TAC std_ss [sup_le]
      ++ POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
      ++ RW_TAC std_ss [IN_IMAGE,IN_UNIV]
      ++ MATCH_MP_TAC pos_fn_integral_mono_mspace
      ++ RW_TAC std_ss []
      ++ Q.PAT_X_ASSUM `!x. x IN m_space m ==> P` (MP_TAC o GSYM o UNDISCH o Q.SPEC `x`)
      ++ RW_TAC std_ss []
      ++ FULL_SIMP_TAC std_ss [sup_le]
      ++ POP_ASSUM (K ALL_TAC)
      ++ POP_ASSUM MATCH_MP_TAC
      ++ ONCE_REWRITE_TAC [GSYM SPECIFICATION]
      ++ RW_TAC std_ss [IN_IMAGE,IN_UNIV]
      ++ METIS_TAC [])
  ++ Q.ABBREV_TAC `r = sup (IMAGE (\i. pos_fn_integral m (fi i)) UNIV)`
  ++ RW_TAC std_ss [pos_fn_integral_def,sup_le]
  ++ POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
  ++ RW_TAC std_ss [GSPECIFICATION]
  ++ METIS_TAC [pos_mono_conv_mono_borel,le_antisym]);


val lebesgue_monotone_convergence_subset = store_thm
  ("lebesgue_monotone_convergence_subset", ``!m f fi A. measure_space m /\ 
	(!i. fi i IN measurable (m_space m, measurable_sets m) Borel) /\ (!i x. 0 <= fi i x) /\ (!x. 0 <= f x) /\ 
	(!x. x IN m_space m ==> (sup (IMAGE (\i. fi i x) UNIV) = f x)) /\ 
	(!x. mono_increasing (\i. fi i x)) /\ (A IN measurable_sets m) ==>
	(pos_fn_integral m (\x. f x * indicator_fn A x) = sup (IMAGE (\i. pos_fn_integral m (\x. fi i x * indicator_fn A x)) UNIV))``,
  RW_TAC std_ss []
  ++ (MP_TAC o Q.SPECL [`m`,`(\x. f x * indicator_fn A x)`,`(\i. (\x. fi i x * indicator_fn A x))`]) lebesgue_monotone_convergence
  ++ RW_TAC std_ss []
  ++ POP_ASSUM MATCH_MP_TAC
  ++ CONJ_TAC >> METIS_TAC [IN_MEASURABLE_BOREL_MUL_INDICATOR,measure_space_def,subsets_def,measurable_sets_def]
  ++ CONJ_TAC >> RW_TAC std_ss [indicator_fn_def,mul_rone,mul_rzero,le_refl]
  ++ CONJ_TAC >> RW_TAC std_ss [indicator_fn_def,mul_rone,mul_rzero,le_refl]
  ++ CONJ_TAC >> (RW_TAC std_ss [indicator_fn_def,mul_rone,mul_rzero,le_refl,ext_mono_increasing_def] ++ FULL_SIMP_TAC std_ss [ext_mono_increasing_def])
  ++ RW_TAC std_ss [indicator_fn_def,mul_rone,mul_rzero]
  ++ Suff `IMAGE (\i:num. 0:extreal) UNIV = (\y. y = 0)` >> RW_TAC std_ss [sup_const]
  ++ RW_TAC std_ss [EXTENSION,IN_ABS,IN_IMAGE,IN_UNIV]);

(**********************************************************)
(*  Existence of Convergent sequence                      *)
(**********************************************************)


(**** Define the sequence ****)
val fn_seq_def = Define `fn_seq m f = (\n. 
         (\x. SIGMA (\k. (&k / (2 pow n)) * indicator_fn {x | x IN m_space m /\ (&k / (2 pow n) <= f x) /\ (f x < (&k + 1) /(2 pow n))} x) (count (4 ** n)) + 
              2 pow (n) * indicator_fn {x | x IN m_space m /\ 2 pow n <= f x} x))`;

(**** Define their integrals ****)
val fn_seq_integral_def = Define `fn_seq_integral m f = (\n. SIGMA (\k. (&k / (2 pow n)) * measure m {x | x IN m_space m /\ &k / 2 pow n <= f x /\ f x < (&k + 1) / 2 pow n}) (count (4 ** n)) + (2 pow n) * measure m {x | x IN m_space m /\ 2 pow n <= f x} )`;



(******************************************************)
(****   f_n(x) = &k / 2 pow n in the k^th interval ****)
(******************************************************)

val lemma_fn_1 = store_thm 
  ("lemma_fn_1",``!m f n x k. x IN m_space m /\ 
			  k IN count (4 ** n) /\ 
			  &k / 2 pow n <= f x /\ 
			  f x < (&k + 1) / 2 pow n ==>
			  (fn_seq m f n x = &k / 2 pow n)``,
  RW_TAC std_ss []
  ++ `0:real < 2 pow n` by RW_TAC real_ss [REAL_POW_LT]
  ++ `0:real <> 2 pow n` by RW_TAC real_ss [REAL_LT_IMP_NE]
  ++ FULL_SIMP_TAC real_ss [fn_seq_def,indicator_fn_def,GSPECIFICATION,IN_COUNT,mul_rone,mul_rzero,extreal_of_num_def,extreal_pow_def,extreal_div_eq,extreal_add_def]
  ++ `f x <> PosInf` by METIS_TAC [lt_infty,lt_trans]
  ++ `f x <> NegInf` by METIS_TAC [lt_infty,lte_trans]
  ++ `?r. f x = Normal r` by METIS_TAC [extreal_cases]
  ++ FULL_SIMP_TAC std_ss [extreal_lt_eq,extreal_le_def]
  ++ `(\k'. Normal (&k' / 2 pow n) * if &k' / 2 pow n <= r /\ r < &(k' + 1) / 2 pow n then Normal 1 else Normal 0) = 
      (\k'. Normal((&k' / 2 pow n) * if &k' / 2 pow n <= r /\ r < &(k' + 1) / 2 pow n then 1 else 0))`
         by (RW_TAC std_ss [FUN_EQ_THM] ++ METIS_TAC [extreal_add_def,extreal_mul_def])
  ++ POP_ORW
  ++ `FINITE (count (4 ** n))` by RW_TAC std_ss [FINITE_COUNT]
  ++ RW_TAC real_ss [EXTREAL_SUM_IMAGE_NORMAL,extreal_11,extreal_mul_def,extreal_add_def]
  >> (`k + 1 <= 4 ** n` by RW_TAC real_ss [LESS_EQ]
      ++ `&(k + 1) <= (4:real) pow n` by RW_TAC real_ss [REAL_OF_NUM_POW]
      ++ FULL_SIMP_TAC real_ss [REAL_LT_RDIV_EQ]
      ++ `r * 2 pow n < 4 pow n` by METIS_TAC [REAL_LTE_TRANS]
      ++ METIS_TAC [REAL_LT_RDIV_EQ,REAL_POW_DIV,EVAL ``4/2:real``,real_lte])
  ++ FULL_SIMP_TAC real_ss [GSYM real_lt]
  ++ (MP_TAC o UNDISCH o Q.SPECL [`k`,`count (4 ** n)`] o CONJUNCT2 o Q.SPEC `(\k'. &k' / 2 pow n *
           if &k' / 2 pow n <= r:real /\ r < &(k' + 1) / 2 pow n then 1 else 0)`) (INST_TYPE [alpha |-> ``:num``] REAL_SUM_IMAGE_THM)
  ++ RW_TAC real_ss []
  ++ `count (4 ** n) = k INSERT (count (4 ** n))` by RW_TAC std_ss [GSYM ABSORPTION,IN_COUNT]
  ++ POP_ORW
  ++ RW_TAC std_ss [REAL_SUM_IMAGE_THM]
  ++ Suff `SIGMA (\k'. &k' / 2 pow n * if &k' / 2 pow n <= r /\ r < &(k' + 1) / 2 pow n then 1 else 0)
                 (count (4 ** n) DELETE k) = 0:real`
  >> RW_TAC real_ss []
  ++ `FINITE (count (4 ** n) DELETE k)` by RW_TAC std_ss [FINITE_COUNT,FINITE_DELETE]
  ++ ONCE_REWRITE_TAC [(UNDISCH o Q.SPEC `count (4 ** n) DELETE k` o INST_TYPE [alpha |-> ``:num``]) REAL_SUM_IMAGE_IN_IF]
  ++ Suff `(\x. if x IN count (4 ** n) DELETE k then (\k'. &k' / 2 pow n *
              if &k' / 2 pow n <= r:real /\ r < &(k' + 1) / 2 pow n then
                1 else 0) x else 0) = (\x:num. 0:real)`
  >> FULL_SIMP_TAC real_ss [REAL_SUM_IMAGE_0]
  ++ RW_TAC real_ss [FUN_EQ_THM,IN_COUNT,IN_DELETE]
  ++ RW_TAC real_ss [COND_EXPAND]
  ++ Cases_on `&x'<=((&k):real)`
  >> (`&(x'+1)<=(&k):real` by FULL_SIMP_TAC real_ss [LESS_EQ,REAL_LE_LT]
      ++ `r * 2 pow n < &(x' + 1)` by METIS_TAC [REAL_LT_RDIV_EQ]
      ++ `r:real * 2 pow n < &k` by METIS_TAC [REAL_LTE_TRANS]
      ++ METIS_TAC [REAL_LT_RDIV_EQ,real_lte])
  ++ FULL_SIMP_TAC std_ss [GSYM real_lt]
  ++ `&(k+1)<=(&x'):real` by FULL_SIMP_TAC real_ss [LESS_EQ,REAL_LE_LT]
  ++ `&x' <= r * 2 pow n` by METIS_TAC [REAL_LE_LDIV_EQ]
  ++ `&(k+1) <= r * 2 pow n` by METIS_TAC [REAL_LE_TRANS]
  ++ METIS_TAC [REAL_LE_LDIV_EQ,real_lte]);


(**********************************************)
(****   f_n(x) = 2 pow n if 2 pow n <= f x ****)
(**********************************************)

val lemma_fn_2 = store_thm 
  ("lemma_fn_2",``!m f n x. x IN m_space m /\ 2 pow n <= f x ==> (fn_seq m f n x = 2 pow n)``,
  RW_TAC real_ss [fn_seq_def,indicator_fn_def,GSPECIFICATION,mul_rone]
  ++ `FINITE (count (4 ** n))` by RW_TAC std_ss [FINITE_COUNT]
  ++ `0:real < 2 pow n` by RW_TAC real_ss [REAL_POW_LT]
  ++ `0:real <> 2 pow n` by RW_TAC real_ss [REAL_LT_IMP_NE]
  ++ Suff `SIGMA (\k. &k / 2 pow n *  if &k / 2 pow n <= f x /\ f x < (&k + 1) / 2 pow n then 1 else 0) (count (4 ** n)) = 0`
  >> RW_TAC real_ss [add_lzero]
  ++ (MP_TAC o Q.SPEC `(\k. &k / 2 pow n * if &k / 2 pow n <= f x /\ f x < (&k + 1) / 2 pow n then 1 else 0)` o UNDISCH o Q.SPEC `count (4 ** n)` o INST_TYPE [alpha |-> ``:num``]) EXTREAL_SUM_IMAGE_IN_IF
  ++ `!x'. (\k. &k / 2 pow n * if &k / 2 pow n <= f x /\ f x < (&k + 1) / 2 pow n then 1 else 0) x' <> NegInf` 
      by (RW_TAC std_ss [mul_rone,mul_rzero]
          ++ RW_TAC std_ss [extreal_of_num_def,extreal_pow_def,extreal_mul_def,extreal_div_eq,extreal_not_infty])
  ++ Suff `(\x'. if x' IN count (4 ** n) then &x' / 2 pow n * if &x' / 2 pow n <= f x /\ f x < (&x' + 1) / 2 pow n then 1 else 0 else 0) = (\x. 0)`
  >> RW_TAC std_ss [EXTREAL_SUM_IMAGE_ZERO]
  ++ RW_TAC real_ss [FUN_EQ_THM,IN_COUNT]
  ++ RW_TAC real_ss [COND_EXPAND,mul_rzero,mul_rone]
  ++ `&(x' + 1):real <= 4 pow n` by RW_TAC real_ss [LESS_EQ,REAL_OF_NUM_POW]
  ++ `&(x' + 1):real / 2 pow n <= 4 pow n / 2 pow n` by RW_TAC real_ss [REAL_LE_LDIV_EQ,REAL_POS_NZ,REAL_DIV_RMUL] 
  ++ `(&x' + 1) / 2 pow n <= 4 pow n / 2 pow n` by RW_TAC real_ss [extreal_div_eq,extreal_pow_def,extreal_add_def,extreal_of_num_def,extreal_le_def]
  ++ `f x < 4 pow n / 2 pow n` by METIS_TAC [lte_trans]
  ++ `4 pow n / 2 pow n = 2 pow n` by RW_TAC std_ss [extreal_pow_def,extreal_div_eq,extreal_of_num_def,GSYM REAL_POW_DIV,EVAL ``4/2:real``]
  ++ METIS_TAC [extreal_lt_def]);

(************************************************************************)
(*** f(x) is either larger than 2 pow n or is inside some k interval ****)
(************************************************************************)

val lemma_fn_3 = store_thm 
  ("lemma_fn_3",``!m f n x. x IN m_space m /\ 0 <= f x ==> (2 pow n <= f x) \/ (?k. k IN count (4 ** n) /\ &k / 2 pow n <= f x /\ f x < (&k + 1) / 2 pow n)``,
  RW_TAC real_ss [IN_COUNT]
  ++ Cases_on `2 pow n <= f x`
  >> RW_TAC std_ss []
  ++ `f x < 2 pow n` by FULL_SIMP_TAC std_ss [extreal_lt_def]
  ++ `f x <> PosInf` by METIS_TAC [extreal_of_num_def,extreal_pow_def,extreal_not_infty,lt_infty,lt_trans]
  ++ `f x <> NegInf` by METIS_TAC [lt_infty,lte_trans,extreal_of_num_def,extreal_not_infty]
  ++ `?r. f x = Normal r` by METIS_TAC [extreal_cases]
  ++ `0:real < 2 pow n` by RW_TAC real_ss [REAL_POW_LT]
  ++ `0:real <> 2 pow n` by RW_TAC real_ss [REAL_LT_IMP_NE]
  ++ FULL_SIMP_TAC real_ss [extreal_of_num_def,extreal_pow_def,extreal_le_def,extreal_lt_eq,extreal_div_eq,extreal_add_def]
  ++ Q.EXISTS_TAC `flr (2 pow n * r)`
  ++ CONJ_TAC
  >> (`2 pow n * r < 2 pow n * 2 pow n` by RW_TAC real_ss [REAL_LT_LMUL]
    ++ `2 pow n * 2 pow n = 4:real pow n` by RW_TAC real_ss [GSYM POW_MUL]
    ++ `0 <= 2 pow n * r` by RW_TAC real_ss [REAL_LT_LE_MUL]
    ++ `&(4 ** n) = 4:real pow n` by RW_TAC real_ss [GSYM REAL_OF_NUM_POW]
    ++ FULL_SIMP_TAC real_ss []
    ++ `&flr (2 pow n * r) <= 2 pow n * r` by RW_TAC real_ss [NUM_FLOOR_LE]
    ++ `&flr (2 pow n * r) < 4:real pow n` by METIS_TAC [REAL_LET_TRANS]
    ++ METIS_TAC [REAL_LT])
  ++ CONJ_TAC
  >> (`0 <= 2 pow n * r` by RW_TAC real_ss [REAL_LT_LE_MUL]
     ++ `&flr (2 pow n * r) <= 2 pow n * r` by RW_TAC real_ss [NUM_FLOOR_LE]
     ++ `&flr (2 pow n * r) / 2 pow n <= 2 pow n * r / 2 pow n`
        by RW_TAC real_ss [REAL_LE_LDIV_EQ,REAL_POS_NZ,REAL_DIV_RMUL]
     ++ METIS_TAC [REAL_EQ_LDIV_EQ,REAL_MUL_COMM])
  ++ `0 <= 2 pow n * r` by RW_TAC real_ss [REAL_LT_LE_MUL]
  ++ `2 pow n * r < &(flr (2 pow n * r) + 1)` by METIS_TAC [NUM_FLOOR_DIV_LOWERBOUND,REAL_LT_01,REAL_OVER1,REAL_MUL_RID]
  ++ `2 pow n * r / 2 pow n < &(flr (2 pow n * r) + 1) / 2 pow n`
      by RW_TAC real_ss [REAL_LT_LDIV_EQ,REAL_POS_NZ,REAL_DIV_RMUL]
  ++ METIS_TAC [REAL_EQ_LDIV_EQ,REAL_MUL_COMM]);


(*********************************)
(*   fn_(x) = 0 outside m_space  *)
(*********************************)

val lemma_fn_4 = store_thm 
("lemma_fn_4",``!m f n x. ~(x IN m_space m) ==> (fn_seq m f n x = 0)``,
  RW_TAC real_ss [fn_seq_def,indicator_fn_def,GSPECIFICATION,mul_rzero,add_rzero]
  ++ METIS_TAC [FINITE_COUNT,EXTREAL_SUM_IMAGE_ZERO]);


(*********************************)
(*       fn_(x) positive         *)
(*********************************)

val lemma_fn_5 = store_thm 
  ("lemma_fn_5",``!m f n x. 0 <= f x ==> (0 <= fn_seq m f n x)``,
  RW_TAC real_ss []
  ++ `0:real < 2 pow n` by RW_TAC real_ss [REAL_POW_LT]
  ++ `0:real <> 2 pow n` by RW_TAC real_ss [REAL_LT_IMP_NE]
  ++ `0 < 2 pow n` by METIS_TAC [extreal_of_num_def,extreal_pow_def,extreal_lt_eq]
  ++ Cases_on `~(x IN m_space m)`
  >> RW_TAC std_ss [lemma_fn_4,le_refl]
  ++ FULL_SIMP_TAC std_ss []
  ++ (MP_TAC o Q.SPECL [`m`,`f`,`n`,`x`]) lemma_fn_3
  ++ RW_TAC real_ss []
  >> RW_TAC real_ss [lt_imp_le,lemma_fn_2]
  ++ `fn_seq m f n x = &k / 2 pow n` by RW_TAC real_ss [lemma_fn_1]
  ++ ASM_SIMP_TAC std_ss []
  ++ RW_TAC std_ss [extreal_of_num_def,extreal_pow_def,extreal_div_eq,extreal_le_def]
  ++ MATCH_MP_TAC REAL_LE_DIV
  ++ RW_TAC real_ss [REAL_POW_LT,REAL_LT_IMP_LE]);
 

(*******************************************************************************)
(*                        MONOTONICALLY INCREASING                             *)
(*******************************************************************************)

val lemma_fn_mono_increasing = store_thm
("lemma_fn_mono_increasing",``!m f x. 0 <= f x ==> mono_increasing (\n. fn_seq m f n x)``,
  RW_TAC std_ss [ext_mono_increasing_suc,ADD1]
  ++ Cases_on `~(x IN m_space m)`
  >> RW_TAC real_ss [lemma_fn_4,le_refl]
  ++ FULL_SIMP_TAC std_ss []
  ++ `!n x k. x IN m_space m /\ (k IN count (4 ** n)) /\ (&k / 2 pow n <= f x /\ f x < (&k + 1) / 2 pow n) ==> (fn_seq m f n x = &k / 2 pow n)`
      by RW_TAC std_ss [lemma_fn_1]
  ++ `!n x. x IN m_space m /\ 2 pow n <= f x ==> (fn_seq m f n x = 2 pow n)`
       by RW_TAC std_ss [lemma_fn_2]
  ++ `!n. 0:real < 2 pow n` by RW_TAC real_ss [REAL_POW_LT]
  ++ `!n. 0:real <> 2 pow n` by RW_TAC real_ss [REAL_LT_IMP_NE]
  ++ `!n k. (k IN count (4 ** (n + 1))) /\ (&k / 2 pow (n + 1) <= f x /\ f x < (&k + 1) / 2 pow (n + 1)) ==> (fn_seq m f n x <= fn_seq m f (n + 1) x)`
       by (RW_TAC real_ss []
   	   ++ `fn_seq m f (n + 1) x = &k / (2 pow (n + 1))` by RW_TAC real_ss []
           ++ `f x <> NegInf` by METIS_TAC [lt_infty,lte_trans,extreal_of_num_def,extreal_not_infty]
           ++ `f x <> PosInf` by METIS_TAC [extreal_of_num_def,extreal_pow_def,extreal_not_infty,lt_infty,lt_trans]
           ++ `?r. f x = Normal r` by METIS_TAC [extreal_cases]
	   ++ `0:real <> 2 pow (n + 1)` by RW_TAC real_ss []
           ++ FULL_SIMP_TAC std_ss [extreal_of_num_def,extreal_pow_def,extreal_div_eq,extreal_add_def,extreal_mul_def,extreal_le_def,extreal_lt_eq]
	   ++ `&(k + 1) / (2 pow (n + 1)):real = (&(k + 1) / 2) / (2 pow (n + 1) / 2)` by RW_TAC real_ss [REAL_DIV_DENOM_CANCEL]
	   ++ `2 pow (n + 1) / 2 = (2 pow n):real` by (RW_TAC std_ss [GSYM ADD1,pow] ++ RW_TAC real_ss [REAL_EQ_LDIV_EQ,REAL_MUL_COMM])
	   ++ `&k / 2 pow (n + 1) = (&k / 2) / (2 pow (n + 1) / 2):real` by RW_TAC real_ss [REAL_DIV_DENOM_CANCEL] 
	   ++ FULL_SIMP_TAC std_ss []
	   ++ STRUCT_CASES_TAC (Q.SPEC `k` EVEN_OR_ODD)
	   >> (FULL_SIMP_TAC std_ss [EVEN_EXISTS]
               ++ FULL_SIMP_TAC real_ss []
	       ++ `&k / 2:real = &m'` by RW_TAC real_ss [REAL_EQ_LDIV_EQ]
	       ++ `&(2 * m' + 1):real < &(2 * m' + 2)` by RW_TAC real_ss []
	       ++ `&(2 * m' + 1) / 2:real < &(2 * m' + 2) / 2` by RW_TAC real_ss [REAL_LT_RDIV]
	       ++ `&(2 * m' + 1) / 2 / (2 pow n):real < &(2 * m' + 2) / 2 / 2 pow n` by RW_TAC real_ss [REAL_LT_RDIV]
	       ++ `&(2 * m' + 2) / 2 = &(m'+1):real` by RW_TAC real_ss [REAL_EQ_LDIV_EQ,REAL_ADD_LDISTRIB]
	       ++ `r < &(m' + 1) / 2 pow n` by METIS_TAC [REAL_LT_TRANS]
               ++ `&(2 * m') / 2 / 2 pow n = &m' / (2 pow n):real` by METIS_TAC []
	       ++ FULL_SIMP_TAC real_ss []
	       ++ Cases_on `m' IN count (4 ** n)`
	       >> (`fn_seq m f n x = Normal (&m' / 2 pow n)` by METIS_TAC [extreal_le_def,extreal_lt_eq]
		   ++ RW_TAC std_ss [le_refl])
	       ++ FULL_SIMP_TAC real_ss [IN_COUNT,NOT_LESS]
	       ++ `4:real pow n <= &m'` by RW_TAC real_ss [REAL_OF_NUM_POW]
	       ++ `4:real pow n / 2 pow n <= &m' / 2 pow n` by RW_TAC real_ss [REAL_LE_LDIV_EQ,REAL_POS_NZ,REAL_DIV_RMUL]
	       ++ `2 pow n <= r` by METIS_TAC [REAL_LE_TRANS,REAL_POW_DIV,EVAL ``4/2:real``]
	       ++ `fn_seq m f n x = Normal (2 pow n)` by METIS_TAC [extreal_le_def,extreal_lt_eq]
	       ++ `(2 pow n):real <= &m' / 2 pow n` by METIS_TAC [REAL_POW_DIV,EVAL ``4/2:real``]
	       ++ `&(2*m')/2 = &m':real` by RW_TAC real_ss []
	       ++ RW_TAC std_ss [extreal_le_def])
	   ++ FULL_SIMP_TAC std_ss [ODD_EXISTS]
	   ++ `(k - 1) < k` by RW_TAC real_ss []
	   ++ `&(k - 1) / 2 < (&k) / 2:real` by RW_TAC real_ss [REAL_LT_LDIV_EQ,REAL_DIV_RMUL]
	   ++ `&(k - 1) / 2 / 2 pow n < (&k) / 2 / (2 pow n):real` by RW_TAC real_ss [REAL_LT_LDIV_EQ,REAL_DIV_RMUL,REAL_POS_NZ]
	   ++ `&(k - 1) / 2 / 2 pow n <= r` by METIS_TAC [REAL_LTE_TRANS,REAL_LT_IMP_LE]
	   ++ `&(k - 1):real = 2 * &m'` by RW_TAC real_ss []
	   ++ `!x. 2 * x / 2 = x:real` by RW_TAC real_ss [REAL_EQ_LDIV_EQ,REAL_MUL_COMM]
           ++ `&m' / (2 pow n) <= r` by METIS_TAC [REAL_MUL]
 	   ++ `&(k + 1):real = 2 * (&m' + 1)` by RW_TAC real_ss []  
           ++ FULL_SIMP_TAC real_ss []
	   ++ `r < &(m' + 1) / (2 pow n)` by METIS_TAC [REAL_MUL,REAL_ADD]
    	   ++ Cases_on `m' IN count (4 ** n)`
	   >> (Q.PAT_X_ASSUM `!n x k. Q` (MP_TAC o Q.SPECL [`n`,`x`, `m'`])
               ++ RW_TAC std_ss [extreal_le_def,extreal_lt_eq]
	       ++ `&(2 * m'):real <= &SUC (2*m')` by RW_TAC real_ss []
	       ++ `&(2 * m') / 2:real <= &SUC (2 * m') / 2` by RW_TAC real_ss [REAL_LE_LDIV_EQ,REAL_DIV_RMUL]
	       ++ `&(2 * m') / 2 / 2 pow n <= &SUC (2 * m') / 2 / (2 pow n):real` by RW_TAC real_ss [REAL_LE_LDIV_EQ,REAL_DIV_RMUL,REAL_POS_NZ]
	       ++ `&(2 * m') / 2:real = &m'` by RW_TAC real_ss [REAL_EQ_LDIV_EQ]
	       ++ FULL_SIMP_TAC real_ss [REAL_LE_TRANS])
	   ++ FULL_SIMP_TAC real_ss [IN_COUNT,NOT_LESS]
	   ++ `4 pow n <= &m':real` by RW_TAC real_ss [REAL_OF_NUM_POW]
	   ++ `4:real pow n / 2 pow n <= &m' / 2 pow n` by RW_TAC real_ss [REAL_LE_LDIV_EQ,REAL_POS_NZ,REAL_DIV_RMUL]
	   ++ `&(k - 1):real = 2 * &m'` by RW_TAC real_ss []
	   ++ `&m' < &k / 2:real` by METIS_TAC []
	   ++ `&m' / (2 pow n):real  < &k / 2 / 2 pow n` by RW_TAC real_ss [REAL_LT_LDIV_EQ,REAL_POS_NZ,REAL_DIV_RMUL]
	   ++ `2 pow n <= r` by METIS_TAC [REAL_POW_DIV,EVAL ``4/2:real``,REAL_LET_TRANS,REAL_LTE_TRANS,REAL_LT_IMP_LE]
	   ++ `fn_seq m f n x = Normal (2 pow n)` by METIS_TAC [extreal_le_def,extreal_lt_eq]
	   ++ `2 pow n <= &m' / (2 pow n):real` by METIS_TAC [REAL_POW_DIV,EVAL ``4/2:real``]
	   ++ `&(2 * m'):real <= &SUC (2 * m')` by RW_TAC real_ss []
	   ++ `&(2 * m') / 2:real <= &SUC (2 * m') / 2` by RW_TAC real_ss [REAL_LE_LDIV_EQ,REAL_DIV_RMUL]
	   ++ `&(2 * m') / 2 / 2 pow n <= &SUC (2 * m') / 2 / (2 pow n):real` by RW_TAC real_ss [REAL_LE_LDIV_EQ,REAL_DIV_RMUL,REAL_POS_NZ]
	   ++ `&(2 * m') / 2:real = &m'` by RW_TAC real_ss [REAL_EQ_LDIV_EQ]
	   ++ METIS_TAC [REAL_LE_TRANS,extreal_le_def])
   ++ `!n. 2 pow (n + 1) <= f x ==> (fn_seq m f n x <= fn_seq m f (n + 1) x)`
        by (RW_TAC real_ss []
	    ++ `2:real pow n < 2 pow (n + 1)` by RW_TAC real_ss [REAL_POW_MONO_LT]
	    ++ `2 pow n < 2 pow (n + 1)` by METIS_TAC [extreal_pow_def,extreal_of_num_def,extreal_lt_eq]
            ++ METIS_TAC [extreal_le_def,extreal_lt_eq,lte_trans,lt_imp_le])
   ++ (MP_TAC o Q.SPECL [`m`,`f`,`n + 1`,`x`]) lemma_fn_3
   ++ RW_TAC std_ss []
   >> RW_TAC std_ss []
   ++ METIS_TAC []);


 
(*******************************************************************************)
(*                            UPPER BOUNDED BY f                               *)
(*******************************************************************************)

val lemma_fn_upper_bounded = store_thm
("lemma_fn_upper_bounded",``!m f n x. 0 <= f x ==> (fn_seq m f n x <= f x)``,
  RW_TAC std_ss []
  ++ Cases_on `~(x IN m_space m)` >> RW_TAC real_ss [lemma_fn_4]
  ++ FULL_SIMP_TAC std_ss []
  ++ (MP_TAC o Q.SPECL [`m`,`f`,`n`,`x`]) lemma_fn_3
  ++ RW_TAC real_ss []
  >> METIS_TAC [lemma_fn_2,le_refl]
  ++ `fn_seq m f n x =  &k / 2 pow n` by RW_TAC real_ss [lemma_fn_1]
  ++ RW_TAC std_ss []);

(*******************************************************************************)
(*                            f Supremum of fn_seq                             *)
(*******************************************************************************)

val lemma_fn_sup = store_thm
  ("lemma_fn_sup",``!m f x. x IN m_space m /\ 0 <= f x ==> (sup (IMAGE (\n. fn_seq m f n x) UNIV) = f x)``,
  RW_TAC std_ss []
  ++ Cases_on `f x = PosInf`
  >> (`!n:num. fn_seq m f n x = 2 pow n` by METIS_TAC [le_infty,lemma_fn_2]
      ++ RW_TAC std_ss [sup_eq,le_infty]
      ++ `!n. 2 pow n <= y` 
            by (RW_TAC std_ss [] 
		++ POP_ASSUM MATCH_MP_TAC
                ++ ONCE_REWRITE_TAC [GSYM SPECIFICATION]
	        ++ RW_TAC std_ss [IN_IMAGE,IN_UNIV]
	        ++ METIS_TAC [])
      ++ SPOSE_NOT_THEN ASSUME_TAC
      ++ METIS_TAC [EXTREAL_ARCH_POW,extreal_lt_def])
  ++ `!n.  fn_seq m f n x <= f x` by METIS_TAC [lemma_fn_upper_bounded]
  ++ `?r. f x = Normal r` by METIS_TAC [extreal_cases,lt_infty,lte_trans,extreal_of_num_def]
  ++ `!n. fn_seq m f n x <> PosInf` by METIS_TAC [lt_infty,let_trans]
  ++ `!n. fn_seq m f n x <> NegInf` by METIS_TAC [lt_infty,lte_trans,lemma_fn_5,extreal_of_num_def]
  ++ `?r. !n. fn_seq m f n x = Normal (r n)` 
         by (Q.EXISTS_TAC `\n. @r. fn_seq m f n x = Normal r`
             ++ GEN_TAC ++ RW_TAC std_ss [] 
             ++ SELECT_ELIM_TAC
   	     ++ RW_TAC std_ss []
	     ++ METIS_TAC [extreal_cases])
  ++ `?N. f x < 2 pow N` by RW_TAC std_ss [EXTREAL_ARCH_POW]
  ++ `!p n. p <= n ==> 2 pow p <= 2 pow n` by METIS_TAC [pow_le_mono,EVAL ``1<=2``]
  ++ `!n. N <= n ==> f x < 2 pow n` by METIS_TAC [lte_trans]
  ++ `!n. N <= n ==> ?k. k IN count (4 ** n) /\ &k / 2 pow n <= f x /\ f x < (&k + 1) / 2 pow n` by METIS_TAC [lemma_fn_3,extreal_lt_def]
  ++ `!n. 0:real < 2 pow n` by RW_TAC real_ss [REAL_POW_LT]
  ++ `!n. 0:real <> 2 pow n` by RW_TAC real_ss [REAL_LT_IMP_NE]
  ++ `!n k. &k / 2 pow n = Normal (&k / 2 pow n)` by METIS_TAC [extreal_of_num_def,extreal_pow_def,extreal_div_eq]
  ++ `!n z. Normal z / 2 pow n = Normal (z / 2 pow n)` by METIS_TAC [extreal_pow_def,extreal_div_eq,extreal_of_num_def]
  ++ `!n. N <= n ==> (f x - 1 / 2 pow n < fn_seq m f n x)`
        by (RW_TAC real_ss []
	    ++ `?k. k IN count (4 ** n) /\ &k / 2 pow n <= f x /\ f x < (&k + 1) / 2 pow n` by METIS_TAC []
	    ++ `fn_seq m f n x = &k / 2 pow n` by METIS_TAC [lemma_fn_1]
            ++ `Normal (&k + 1) / Normal (2 pow n) = Normal ((&k + 1) / (2 pow n))` by METIS_TAC [extreal_div_eq]
            ++ `Normal r < Normal ((&k + 1) /  (2 pow n))` by METIS_TAC [extreal_pow_def,extreal_of_num_def,extreal_add_def]
            ++ FULL_SIMP_TAC std_ss [extreal_lt_eq,GSYM REAL_DIV_ADD,extreal_pow_def,extreal_sub_def,extreal_of_num_def,extreal_div_eq,extreal_lt_eq,REAL_LT_SUB_RADD]
	    ++ `r' n = &k / 2 pow n` by METIS_TAC [extreal_div_eq,extreal_11]
            ++ FULL_SIMP_TAC std_ss [])
  ++ FULL_SIMP_TAC std_ss []
  ++ `!n. N <= n ==> (r - 1 / 2 pow n < r' n)` 
        by (FULL_SIMP_TAC std_ss [extreal_le_def,extreal_lt_eq,extreal_of_num_def,extreal_pow_def,extreal_div_eq,extreal_add_def]
            ++ RW_TAC std_ss []
	    ++ METIS_TAC [extreal_sub_def,extreal_lt_eq])
  ++ `mono_increasing (\n. fn_seq m f n x)` by METIS_TAC [lemma_fn_mono_increasing]
  ++ `mono_increasing r'` by (FULL_SIMP_TAC std_ss [ext_mono_increasing_def,mono_increasing_def] ++ METIS_TAC [extreal_le_def])
  ++ FULL_SIMP_TAC std_ss [extreal_le_def,extreal_lt_eq,extreal_of_num_def,extreal_pow_def,extreal_div_eq,extreal_add_def,extreal_sub_def,extreal_not_infty]
  ++ RW_TAC std_ss [GSYM sup_seq,SEQ,GREATER_EQ]
  ++ `!n. 1:real / 2 pow n = (1 / 2) pow n` by RW_TAC real_ss [POW_ONE,REAL_POW_DIV]
  ++ `!n. r' n < r + 1 / 2 pow n` by METIS_TAC [POW_HALF_POS,REAL_LT_ADDR,REAL_LET_TRANS,REAL_LT_IMP_LE]
  ++ `!n. N <= n ==> (abs (r' n - r) < 1 / 2 pow n)` by METIS_TAC [ABS_BETWEEN,POW_HALF_POS]
  ++ `?N1. (1 / 2) pow N1 < e:real` by RW_TAC std_ss [POW_HALF_SMALL]
  ++ `!n. N1 <= n ==> ((1 / 2:real) pow n <= (1 / 2) pow N1)` by RW_TAC std_ss [POW_HALF_MONO]
  ++ `!n. N1 <= n ==> ((1 / 2:real) pow n < e)` by METIS_TAC [REAL_LET_TRANS]
  ++ Q.EXISTS_TAC `N + N1`
  ++ RW_TAC real_ss []
  ++ `N <= N + N1` by RW_TAC std_ss [LESS_EQ_ADD]
  ++ `N1 <= N + N1` by RW_TAC std_ss [LESS_EQ_ADD]
  ++ `N <= n /\ N1 <= n` by METIS_TAC [LESS_EQ_TRANS]
  ++ METIS_TAC [REAL_LT_TRANS]);


(*******************************************************************************)
(*          SEQ Positive Simple Functions and Define Integral                  *)
(*******************************************************************************)

val lemma_fn_in_psfis = store_thm
  ("lemma_fn_in_psfis",``!m f n.  (!x. 0 <= f x) /\ measure_space m /\ f IN measurable (m_space m,measurable_sets m) Borel
			 ==> (fn_seq_integral m f n IN psfis m (fn_seq m f n))``,
  RW_TAC std_ss [IN_psfis_eq,pos_simple_fn_def]
  ++ Q.EXISTS_TAC `count (4 ** n + 1)`
  ++ Q.EXISTS_TAC `(\k. if k IN count (4 ** n) then {x | x IN m_space m /\ &k / 2 pow n <= f x /\ f x < (&k + 1) / 2 pow n} else {x | x IN m_space m /\ 2 pow n <= f x} )`
  ++ Q.EXISTS_TAC `(\k. if k IN count (4 ** n) then &k / 2 pow n else 2 pow n )`
  ++ `FINITE (count (4 ** n))` by RW_TAC std_ss [FINITE_COUNT]
  ++ `FINITE (count (4 ** n + 1))` by RW_TAC std_ss [FINITE_COUNT]
  ++ `!n. 0:real < 2 pow n` by RW_TAC real_ss [REAL_POW_LT]
  ++ `!n. 0:real <> 2 pow n` by RW_TAC real_ss [REAL_LT_IMP_NE]
  ++ `!n k. &k / 2 pow n = Normal (&k / 2 pow n)` by METIS_TAC [extreal_of_num_def,extreal_pow_def,extreal_div_eq]
  ++ `!n z. Normal z / 2 pow n = Normal (z / 2 pow n)` by METIS_TAC [extreal_pow_def,extreal_div_eq,extreal_of_num_def]
  ++ CONJ_TAC
  >> (CONJ_TAC 
      >> RW_TAC std_ss [lemma_fn_5]
      ++ CONJ_TAC  
      >> (RW_TAC real_ss [fn_seq_def,IN_COUNT,GSYM ADD1,COUNT_SUC]
          ++ `(\i. Normal (if i < 4 ** n then &i / 2 pow n else 2 pow n) *
		   indicator_fn (if i < 4 ** n then
		   {x | x IN m_space m /\ Normal (&i / 2 pow n) <= f x /\ f x < (&i + 1) / 2 pow n}
                   else {x | x IN m_space m /\ 2 pow n <= f x}) t) = 
	      (\i. if i < 4 ** n then &i / 2 pow n  *
                   indicator_fn {x | x IN m_space m /\ &i / 2 pow n <= f x /\ f x < (&i + 1) / 2 pow n} t
                   else 2 pow n * indicator_fn {x | x IN m_space m /\ 2 pow n <= f x} t)`
                by (RW_TAC std_ss [FUN_EQ_THM]
                    ++ Cases_on `i < 4 ** n` >> RW_TAC std_ss []
                    ++ RW_TAC std_ss [extreal_of_num_def,extreal_pow_def])
	  ++ POP_ORW
	  ++ (MP_TAC o Q.SPEC `4 ** n` o UNDISCH o Q.SPECL [`(\i. if i < 4 ** n then &i / 2 pow n * indicator_fn {x | x IN m_space m /\ &i / 2 pow n <= f x /\ f x < (&i + 1) / 2 pow n} t
               else 2 pow n * indicator_fn {x | x IN m_space m /\ 2 pow n <= f x} t)`,`count (4 ** n)`] o INST_TYPE [alpha |-> ``:num``]) EXTREAL_SUM_IMAGE_PROPERTY
          ++ `!x. (\i. if i < 4 ** n then &i / 2 pow n * indicator_fn {x | x IN m_space m /\ &i / 2 pow n <= f x /\ f x < (&i + 1) / 2 pow n} t
                else 2 pow n * indicator_fn {x | x IN m_space m /\ 2 pow n <= f x} t) x <> NegInf`
               by (RW_TAC std_ss [indicator_fn_def,mul_rone,mul_rzero,num_not_infty]
                   ++ METIS_TAC [extreal_of_num_def,extreal_pow_def,extreal_not_infty])
          ++ RW_TAC std_ss []
	  ++ `count (4 ** n) DELETE 4 ** n = count (4 ** n)` 
              by METIS_TAC [DELETE_NON_ELEMENT,IN_COUNT,LESS_EQ_REFL,NOT_LESS]
          ++ RW_TAC std_ss []
	  ++ Q.PAT_X_ASSUM `SIGMA f s = Q` (K ALL_TAC)
          ++ FULL_SIMP_TAC std_ss [GSYM IN_COUNT]
          ++ `!i. Normal (&i / 2 pow n) = &i / 2 pow n` by METIS_TAC []
          ++ POP_ORW
	  ++ Q.PAT_X_ASSUM `!n k. &k / 2 pow n = Normal (&k / 2 pow n)` (K ALL_TAC)
          ++ `!i.  (\i. &i / 2 pow n * indicator_fn {x | x IN m_space m /\ &i / 2 pow n <= f x /\ f x < (&i + 1) / 2 pow n} t) i <> NegInf`
               by (RW_TAC std_ss [indicator_fn_def,mul_rone,mul_rzero,num_not_infty]
                   ++ METIS_TAC [extreal_of_num_def,extreal_pow_def,extreal_not_infty])
          ++ (MP_TAC o Q.SPECL [`count (4 ** n)`,`(\k. &k / 2 pow n * indicator_fn {x | x IN m_space m /\ &k / 2 pow n <= f x /\ f x < (&k + 1) / 2 pow n} t)`,` 2 pow n * indicator_fn {x | x IN m_space m /\ 2 pow n <= f x} t`] o INST_TYPE [alpha |-> ``:num``] o GSYM) EXTREAL_SUM_IMAGE_IN_IF_ALT
	  ++ RW_TAC std_ss []
	  ++ MATCH_MP_TAC add_comm
	  ++ DISJ1_TAC
	  ++ REVERSE CONJ_TAC
	  >> (RW_TAC std_ss [indicator_fn_def,mul_rone,mul_rzero,num_not_infty]
              ++ METIS_TAC [extreal_of_num_def,extreal_pow_def,extreal_not_infty])
	  ++ FULL_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_NOT_INFTY])
      ++ CONJ_TAC  
      >> (RW_TAC real_ss []
	  >> (`{x | x IN m_space m /\ Normal (&i / 2 pow n) <= f x /\ f x < (&i + 1) / 2 pow n} = 
	       {x | Normal (&i / 2 pow n) <= f x /\ f x < Normal (&(i + 1) / 2 pow n)} INTER m_space m`
	         by (RW_TAC std_ss [EXTENSION,GSPECIFICATION,IN_INTER,CONJ_COMM]
                     ++ `(&i + 1:extreal) = &(i + 1)` by RW_TAC std_ss [extreal_add_def,extreal_of_num_def,REAL_ADD]
                     ++ METIS_TAC [])
	      ++ METIS_TAC [IN_MEASURABLE_BOREL_ALL, measurable_sets_def,subsets_def,space_def,m_space_def])
	  ++ `{x | x IN m_space m /\ 2 pow n <= f x} = {x | Normal (2 pow n) <= f x} INTER m_space m`
	        by RW_TAC std_ss [EXTENSION,GSPECIFICATION,IN_INTER,CONJ_COMM,extreal_of_num_def,extreal_pow_def]
          ++ METIS_TAC [IN_MEASURABLE_BOREL_ALL, measurable_sets_def,subsets_def,space_def,m_space_def])
      ++ CONJ_TAC
      >> RW_TAC std_ss []
      ++ CONJ_TAC
      >> RW_TAC real_ss [extreal_of_num_def,extreal_pow_def,extreal_le_def,REAL_LT_IMP_LE,POW_POS,REAL_LE_DIV]
      ++ CONJ_TAC
      >> (RW_TAC real_ss [DISJOINT_DEF,IN_COUNT,IN_INTER,EXTENSION,GSPECIFICATION]
         << [REVERSE EQ_TAC
	     >> RW_TAC std_ss [NOT_IN_EMPTY]
   	     ++ RW_TAC real_ss []
	     ++ RW_TAC std_ss [NOT_IN_EMPTY]
	     ++ Cases_on `i<j`
	     >> (`i + 1 <= j` by RW_TAC real_ss []
	         ++ `&(i + 1) / 2:real pow n <= &j / 2 pow n` by RW_TAC real_ss [REAL_LE_RDIV_EQ,REAL_POW_LT,REAL_DIV_RMUL,REAL_POS_NZ] 
                 ++ `&(i + 1) / 2 pow n <= &j / 2 pow n` by RW_TAC std_ss [extreal_of_num_def,extreal_add_def,extreal_pow_def,extreal_div_eq,extreal_lt_eq,extreal_le_def]
                 ++ `&j / 2 pow n <= f x` by METIS_TAC []
                 ++ `(&i + 1) = &(i + 1)` by METIS_TAC [extreal_of_num_def,extreal_add_def,REAL_ADD]
	         ++ METIS_TAC [lte_trans,extreal_lt_def])
	     ++ `j < i` by RW_TAC real_ss [LESS_OR_EQ]
	     ++ `j + 1 <= i` by RW_TAC real_ss []
	     ++ `&(j + 1) / 2 pow n <= &i / 2:real pow n` by RW_TAC real_ss [REAL_LE_RDIV_EQ,REAL_POW_LT,REAL_DIV_RMUL,REAL_POS_NZ] 
	     ++ `&(j + 1) / 2 pow n <= &i / 2 pow n` by RW_TAC std_ss [extreal_of_num_def,extreal_add_def,extreal_pow_def,extreal_div_eq,extreal_lt_eq,extreal_le_def]
             ++ `(&j + 1) = &(j + 1)` by METIS_TAC [extreal_of_num_def,extreal_add_def,REAL_ADD]
	     ++ METIS_TAC [lte_trans,extreal_lt_def],

	     REVERSE EQ_TAC >> RW_TAC std_ss [NOT_IN_EMPTY]
             ++ RW_TAC std_ss []
	     ++ RW_TAC real_ss [NOT_IN_EMPTY]
	     ++ `&(i + 1) <= &(4 ** n):real` by RW_TAC real_ss []
	     ++ FULL_SIMP_TAC std_ss [GSYM REAL_OF_NUM_POW]
 	     ++ `&(i + 1) / 2 pow n <= 4 pow n / 2:real pow n` by RW_TAC real_ss [REAL_LE_RDIV_EQ,REAL_POW_LT,REAL_DIV_RMUL,REAL_POS_NZ] 
 	     ++ `&(i + 1) / 2 pow n <= 2:real pow n` by METIS_TAC [REAL_POW_DIV,EVAL ``4/2:real``] 
 	     ++ `&(i + 1) / 2 pow n <= 2 pow n` by RW_TAC std_ss [extreal_of_num_def,extreal_add_def,extreal_pow_def,extreal_div_eq,extreal_lt_eq,extreal_le_def]
             ++ `(&i + 1) = &(i + 1)` by METIS_TAC [extreal_of_num_def,extreal_add_def,REAL_ADD]
	     ++ METIS_TAC [le_trans,extreal_lt_def],

	     REVERSE EQ_TAC >> RW_TAC std_ss [NOT_IN_EMPTY]
	     ++ RW_TAC real_ss []
	     ++ RW_TAC std_ss [NOT_IN_EMPTY]
	     ++ `&(j + 1) <= &(4 ** n):real` by RW_TAC real_ss []
	     ++ FULL_SIMP_TAC std_ss [GSYM REAL_OF_NUM_POW]
 	     ++ `&(j + 1) / 2 pow n <= 4:real pow n / 2 pow n` by RW_TAC real_ss [REAL_LE_RDIV_EQ,REAL_POW_LT,REAL_DIV_RMUL,REAL_POS_NZ] 
 	     ++ `&(j + 1) / 2 pow n <= 2:real pow n` by  METIS_TAC [REAL_POW_DIV,EVAL ``4/2:real``] 
 	     ++ `&(j + 1) / 2 pow n <= 2 pow n` by RW_TAC std_ss [extreal_of_num_def,extreal_add_def,extreal_pow_def,extreal_div_eq,extreal_lt_eq,extreal_le_def]
             ++ `(&j + 1) = &(j + 1)` by METIS_TAC [extreal_of_num_def,extreal_add_def,REAL_ADD]
	     ++ METIS_TAC [lte_trans,extreal_lt_def]])
     ++ RW_TAC std_ss [EXTENSION,IN_BIGUNION_IMAGE,GSPECIFICATION]
     ++ EQ_TAC 
     >> (RW_TAC std_ss []
	 ++ Cases_on `k IN count (4 ** n)`
	 >> FULL_SIMP_TAC std_ss [GSPECIFICATION,lemma_fn_3]
	 ++ FULL_SIMP_TAC std_ss [GSPECIFICATION,lemma_fn_3])
     ++ RW_TAC real_ss [IN_COUNT]
     ++ `2 pow n <= f x \/ ?k. k IN count (4 ** n) /\ &k / 2 pow n <= f x /\ f x < (&k + 1) / 2 pow n` by METIS_TAC [lemma_fn_3]
     >> (Q.EXISTS_TAC `4 ** n`
	 ++ RW_TAC real_ss [GSPECIFICATION])
     ++ Q.EXISTS_TAC `k` 
     ++ FULL_SIMP_TAC real_ss [IN_COUNT,GSPECIFICATION]
     ++ METIS_TAC [])
  ++ RW_TAC real_ss [pos_simple_fn_integral_def,fn_seq_integral_def]
  ++ `4 ** n + 1 = SUC (4 ** n)` by RW_TAC real_ss []
  ++ ASM_SIMP_TAC std_ss []
  ++ RW_TAC std_ss [COUNT_SUC,IN_COUNT]
  ++ `(\i. Normal (if i < 4 ** n then &i / 2 pow n else 2 pow n) *
		   measure m (if i < 4 ** n then
		   {x | x IN m_space m /\ Normal (&i / 2 pow n) <= f x /\ f x < (&i + 1) / 2 pow n}
                   else {x | x IN m_space m /\ 2 pow n <= f x})) = 
	      (\i. if i < 4 ** n then &i / 2 pow n  *
                   measure m {x | x IN m_space m /\ &i / 2 pow n <= f x /\ f x < (&i + 1) / 2 pow n}
                   else 2 pow n * measure m {x | x IN m_space m /\ 2 pow n <= f x})`
                by (RW_TAC std_ss [FUN_EQ_THM]
                    ++ Cases_on `i < 4 ** n` >> RW_TAC std_ss []
                    ++ RW_TAC std_ss [extreal_of_num_def,extreal_pow_def])
  ++ POP_ORW
  ++ (MP_TAC o Q.SPEC `4 ** n` o UNDISCH o Q.SPECL [`(\i. if i < 4 ** n then &i / 2 pow n * measure m {x | x IN m_space m /\ &i / 2 pow n <= f x /\ f x < (&i + 1) / 2 pow n}
         else 2 pow n * measure m {x | x IN m_space m /\ 2 pow n <= f x})`,`count (4 ** n)`] o INST_TYPE [alpha |-> ``:num``]) EXTREAL_SUM_IMAGE_PROPERTY
  ++ `!x. (\i. if i < 4 ** n then &i / 2 pow n * measure m {x | x IN m_space m /\ &i / 2 pow n <= f x /\ f x < (&i + 1) / 2 pow n} 
           else 2 pow n * measure m {x | x IN m_space m /\ 2 pow n <= f x}) x <> NegInf`
             by (RW_TAC std_ss []
                   >> (`0 <= &x / 2:real pow n` by RW_TAC real_ss [REAL_LE_DIV,REAL_LT_IMP_LE]
                       ++ Suff `measure m {x' | x' IN m_space m /\ Normal (&x / 2 pow n) <= f x' /\ f x' < (&x + 1) / 2 pow n} <> NegInf`
                       >> METIS_TAC [mul_not_infty]
		       ++ Suff `{x' | x' IN m_space m /\ Normal (&x / 2 pow n) <= f x' /\ f x' < (&x + 1) / 2 pow n} IN measurable_sets m`
                       >> METIS_TAC [positive_not_infty,MEASURE_SPACE_POSITIVE]
		       ++ `{x' | x' IN m_space m /\ Normal (&x / 2 pow n) <= f x' /\ f x' < (&x + 1) / 2 pow n} =
			   {x' | Normal (&x / 2 pow n) <= f x' /\ f x' < (&x + 1) / 2 pow n} INTER m_space m`
                             by (RW_TAC std_ss [EXTENSION,GSPECIFICATION,IN_INTER] ++ METIS_TAC [])
		       ++ `!x. &x + 1 =  &(x + 1)` by METIS_TAC [extreal_of_num_def,extreal_add_def,REAL_ADD]
                       ++ METIS_TAC [IN_MEASURABLE_BOREL_ALL, measurable_sets_def,subsets_def,space_def,m_space_def])
                   ++ RW_TAC std_ss [extreal_of_num_def,extreal_pow_def]
		   ++ `0:real <= 2 pow n` by FULL_SIMP_TAC std_ss [REAL_LT_IMP_LE]
                   ++ Suff `{x | x IN m_space m /\ Normal (2 pow n) <= f x} IN measurable_sets m`
                   >> METIS_TAC [mul_not_infty,positive_not_infty,MEASURE_SPACE_POSITIVE]
		   ++ `{x | x IN m_space m /\ Normal (2 pow n) <= f x} = {x | Normal (2 pow n) <= f x} INTER m_space m`
                         by (RW_TAC std_ss [EXTENSION,GSPECIFICATION,IN_INTER] ++ METIS_TAC [])
	           ++ METIS_TAC [IN_MEASURABLE_BOREL_ALL, measurable_sets_def,subsets_def,space_def,m_space_def])
  ++ RW_TAC std_ss []
  ++ `count (4 ** n) DELETE 4 ** n = count (4 ** n)` 
             by METIS_TAC [DELETE_NON_ELEMENT,IN_COUNT,LESS_EQ_REFL,NOT_LESS]
  ++ RW_TAC std_ss []
  ++ Q.PAT_X_ASSUM `SIGMA f s = Q` (K ALL_TAC)
  ++ FULL_SIMP_TAC std_ss [GSYM IN_COUNT]


  ++ `!i. (\i. Normal (&i / 2 pow n) * measure m {x | x IN m_space m /\ Normal (&i / 2 pow n) <= f x /\ f x < (&i + 1) / 2 pow n}) i <> NegInf`
        by (RW_TAC std_ss []
            ++ `0 <= &i / 2:real pow n` by RW_TAC real_ss [REAL_LE_DIV,REAL_LT_IMP_LE]
            ++ Suff `{x | x IN m_space m /\ Normal (&i / 2 pow n) <= f x /\ f x < (&i + 1) / 2 pow n} IN measurable_sets m`
	    >> METIS_TAC [mul_not_infty,positive_not_infty,MEASURE_SPACE_POSITIVE]
	    ++ `{x | x IN m_space m /\ Normal (&i / 2 pow n) <= f x /\ f x < (&i + 1) / 2 pow n} = 
                {x | Normal (&i / 2 pow n) <= f x /\ f x < (&i + 1) / 2 pow n} INTER m_space m`
                    by (RW_TAC std_ss [EXTENSION,GSPECIFICATION,IN_INTER] ++ METIS_TAC [])
	    ++ `!x. &x + 1 =  &(x + 1)` by METIS_TAC [extreal_of_num_def,extreal_add_def,REAL_ADD]
            ++ METIS_TAC [IN_MEASURABLE_BOREL_ALL, measurable_sets_def,subsets_def,space_def,m_space_def])
  ++ (MP_TAC o Q.SPECL [`count (4 ** n)`,`(\k. &k / 2 pow n * measure m {x | x IN m_space m /\ &k / 2 pow n <= f x /\ f x < (&k + 1) / 2 pow n})`,` 2 pow n * measure m {x | x IN m_space m /\ 2 pow n <= f x}`] o INST_TYPE [alpha |-> ``:num``] o GSYM) EXTREAL_SUM_IMAGE_IN_IF_ALT
  ++ RW_TAC std_ss []
  ++ FULL_SIMP_TAC std_ss []
  ++ MATCH_MP_TAC add_comm
  ++ DISJ1_TAC
  ++ REVERSE CONJ_TAC
  >> (RW_TAC std_ss [extreal_of_num_def,extreal_pow_def]
      ++ `0:real <= 2 pow n` by FULL_SIMP_TAC std_ss [REAL_LT_IMP_LE]
      ++ Suff `{x | x IN m_space m /\ Normal (2 pow n) <= f x} IN measurable_sets m`
      >> METIS_TAC [mul_not_infty,positive_not_infty,MEASURE_SPACE_POSITIVE]
      ++ `{x | x IN m_space m /\ Normal (2 pow n) <= f x} = {x | Normal (2 pow n) <= f x} INTER m_space m`
            by (RW_TAC std_ss [EXTENSION,GSPECIFICATION,IN_INTER] ++ METIS_TAC [])
      ++ METIS_TAC [IN_MEASURABLE_BOREL_ALL, measurable_sets_def,subsets_def,space_def,m_space_def])
  ++ FULL_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_NOT_INFTY]);




(*****************************************************************)


val integral_sequence = store_thm
  ("integral_sequence",``!m f.  (!x. 0 <= f x) /\ measure_space m /\  
                        f IN measurable (m_space m,measurable_sets m) Borel
			==> (pos_fn_integral m f = sup (IMAGE (\i. pos_fn_integral m (fn_seq m f i)) UNIV))``,	
  RW_TAC std_ss []
  ++ MATCH_MP_TAC lebesgue_monotone_convergence
  ++ RW_TAC std_ss [lemma_fn_sup,lemma_fn_mono_increasing,lemma_fn_upper_bounded,lemma_fn_5]
  ++ METIS_TAC [lemma_fn_in_psfis,IN_MEASURABLE_BOREL_POS_SIMPLE_FN,IN_psfis_eq]);


val measurable_sequence = store_thm
("measurable_sequence",``!m f. measure_space m /\ f IN measurable (m_space m,measurable_sets m) Borel ==> 	
	(?fi ri. (!x. mono_increasing (\i. fi i x)) /\
	(!x. x IN m_space m ==> (sup (IMAGE (\i. fi i x) UNIV) = fn_plus f x)) /\
	(!i. ri i IN psfis m (fi i)) /\ 
	(!i x. fi i x <= fn_plus f x) /\
        (!i x. 0 <= fi i x) /\  
	(pos_fn_integral m (fn_plus f) = sup (IMAGE (\i. pos_fn_integral m (fi i)) UNIV))) /\

	(?gi vi. (!x. mono_increasing (\i. gi i x)) /\
	(!x. x IN m_space m ==> (sup (IMAGE (\i. gi i x) UNIV) = fn_minus f x)) /\
	(!i. vi i IN psfis m (gi i)) /\
	(!i x. (gi i) x <= fn_minus f x) /\ 
        (!i x. 0 <= gi i x) /\  
	(pos_fn_integral m (fn_minus f) = sup (IMAGE (\i. pos_fn_integral m (gi i)) UNIV)))``,
  REPEAT STRIP_TAC
  >> (Q.EXISTS_TAC `(\n. fn_seq m (fn_plus f) n)`
      ++ Q.EXISTS_TAC `(\n. fn_seq_integral m (fn_plus f) n)`
      ++ CONJ_TAC 
      >> RW_TAC std_ss [FN_PLUS_POS,lemma_fn_mono_increasing]
      ++ CONJ_TAC 
      >> RW_TAC std_ss [FN_PLUS_POS,lemma_fn_sup]
      ++ CONJ_TAC 
      >> FULL_SIMP_TAC std_ss [FN_PLUS_POS,lemma_fn_in_psfis,IN_MEASURABLE_BOREL_FN_PLUS]
      ++ CONJ_TAC 
      >> METIS_TAC [FN_PLUS_POS,lemma_fn_upper_bounded]
      ++ CONJ_TAC 
      >> METIS_TAC [FN_PLUS_POS,lemma_fn_5]
      ++ METIS_TAC [FN_PLUS_POS,integral_sequence,IN_MEASURABLE_BOREL_FN_PLUS])
  ++ Q.EXISTS_TAC `(\n. fn_seq m (fn_minus f) n)`
  ++ Q.EXISTS_TAC `(\n. fn_seq_integral m (fn_minus f) n)`
  ++ CONJ_TAC 
  >> RW_TAC std_ss [FN_MINUS_POS,lemma_fn_mono_increasing]
  ++ CONJ_TAC 
  >> RW_TAC std_ss [FN_MINUS_POS,lemma_fn_sup]
  ++ CONJ_TAC 
  >> FULL_SIMP_TAC std_ss [FN_MINUS_POS,lemma_fn_in_psfis,IN_MEASURABLE_BOREL_FN_MINUS]
  ++ CONJ_TAC 
  >> METIS_TAC [FN_MINUS_POS,lemma_fn_upper_bounded]
  ++ CONJ_TAC 
  >> METIS_TAC [FN_MINUS_POS,lemma_fn_5]
  ++ METIS_TAC [FN_MINUS_POS,integral_sequence,IN_MEASURABLE_BOREL_FN_MINUS]);

val pos_fn_integral_add = store_thm
  ("pos_fn_integral_add",``!m f g. measure_space m /\ (!x. 0 <= f x /\ 0 <= g x) /\
            f IN measurable (m_space m,measurable_sets m) Borel /\ 
            g IN measurable (m_space m,measurable_sets m) Borel  ==> 
            (pos_fn_integral m (\x. f x + g x) = pos_fn_integral m f + pos_fn_integral m g)``,
  RW_TAC std_ss []
  ++ `?fi ui.
       (!x. mono_increasing (\i. fi i x)) /\
       (!x. x IN m_space m ==> (sup (IMAGE (\i. fi i x) UNIV) = f x)) /\
       (!i. ui i IN psfis m (fi i)) /\ 
       (!i x. fi i x <= f x) /\
       (!i x. 0 <= fi i x) /\ 
       (pos_fn_integral m f = sup (IMAGE (\i. pos_fn_integral m (fi i)) UNIV))`
  	  by METIS_TAC [measurable_sequence,FN_PLUS_POS_ID]
  ++ `?gi vi.
       (!x. mono_increasing (\i. gi i x)) /\
       (!x. x IN m_space m ==> (sup (IMAGE (\i. gi i x) UNIV) = g x)) /\
       (!i. vi i IN psfis m (gi i)) /\ 
       (!i x. gi i x <= g x) /\
       (!i x. 0 <= gi i x) /\ 
       (pos_fn_integral m g = sup (IMAGE (\i. pos_fn_integral m (gi i)) UNIV))`
  	  by METIS_TAC [measurable_sequence,FN_PLUS_POS_ID]
  ++ `sup (IMAGE (\i. pos_fn_integral m (fi i)) UNIV) + sup (IMAGE (\i. pos_fn_integral m (gi i)) UNIV) = 
      sup (IMAGE (\i. (\n. pos_fn_integral m (fi n)) i + (\n. pos_fn_integral m (gi n)) i) UNIV)`
       by (MATCH_MP_TAC (GSYM sup_add_mono)
           ++ FULL_SIMP_TAC std_ss [pos_fn_integral_pos,ext_mono_increasing_suc,pos_fn_integral_mono])
  ++ FULL_SIMP_TAC std_ss []
  ++ `!i. (\x. fi i x + gi i x) IN  measurable (m_space m,measurable_sets m) Borel`
		by METIS_TAC [IN_MEASURABLE_BOREL_POS_SIMPLE_FN,IN_psfis_eq,psfis_add]
  ++ `!x. mono_increasing (\i. (\i x. fi i x + gi i x) i x)` by FULL_SIMP_TAC std_ss [ext_mono_increasing_def,le_add2]
  ++ `!x. x IN m_space m ==> (sup (IMAGE (\i. fi i x + gi i x) UNIV) = f x + g x)`
       by (RW_TAC std_ss []
           ++ `f x = sup (IMAGE (\i. fi i x) UNIV)` by FULL_SIMP_TAC std_ss []
           ++ `g x = sup (IMAGE (\i. gi i x) UNIV)` by FULL_SIMP_TAC std_ss []
	   ++ POP_ORW ++ POP_ORW
	   ++ FULL_SIMP_TAC std_ss [pos_fn_integral_pos,sup_add_mono,ext_mono_increasing_suc,pos_fn_integral_mono])
  ++ (MP_TAC o Q.SPECL [`m`,`(\x. f x + g x)`,`(\i. (\x. fi i x + gi i x))`]) lebesgue_monotone_convergence
  ++ RW_TAC std_ss []
  ++ Suff `(\i. pos_fn_integral m (fi i) + pos_fn_integral m (gi i)) = (\i. pos_fn_integral m (\x. fi i x + gi i x))`  
  >> RW_TAC std_ss [le_add]
  ++ RW_TAC std_ss [FUN_EQ_THM]
  ++ METIS_TAC [IN_psfis_eq,psfis_add,pos_fn_integral_pos_simple_fn]);

val pos_fn_integral_sum = store_thm
  ("pos_fn_integral_sum",``!m f s. FINITE s /\ measure_space m /\ (!i. i IN s ==> (!x. 0 <= f i x)) /\
	(!i. i IN s ==> f i IN measurable (m_space m,measurable_sets m) Borel)  
	    ==> (pos_fn_integral m (\x. SIGMA (\i. (f i) x) s) = SIGMA (\i. pos_fn_integral m (f i)) s)``,
  Suff `!s:'b->bool. FINITE s ==> (\s:'b->bool. !m f. measure_space m /\ (!i. i IN s ==> (!x. 0 <= f i x)) /\
	   (!i. i IN s ==> f i IN measurable (m_space m,measurable_sets m) Borel)              
   	    ==> (pos_fn_integral m (\x. SIGMA (\i. (f i) x) s) = SIGMA (\i. pos_fn_integral m (f i)) s)) s`
  >> METIS_TAC []
  ++ MATCH_MP_TAC FINITE_INDUCT
  ++ RW_TAC std_ss [EXTREAL_SUM_IMAGE_EMPTY,pos_fn_integral_zero]
  ++ `!x. SIGMA (\i. f i x) (e INSERT s) = f e x + SIGMA (\i. f i x) s`
       by (RW_TAC std_ss []
           ++ (MP_TAC o Q.SPEC `e` o UNDISCH o Q.SPECL [`(\i. f i x)`,`s`] o INST_TYPE [alpha |-> beta]) EXTREAL_SUM_IMAGE_PROPERTY
           ++ `!i. i IN e INSERT s ==> (\i. f i x) i <> NegInf`
                by (RW_TAC std_ss [] ++ METIS_TAC [lt_infty,extreal_of_num_def,extreal_not_infty,lte_trans])
           ++ FULL_SIMP_TAC std_ss [DELETE_NON_ELEMENT])

  ++ RW_TAC std_ss []
  ++ `!i. i IN e INSERT s ==> (\i. pos_fn_integral m (f i)) i <> NegInf`
        by (RW_TAC std_ss [] ++ METIS_TAC [lt_infty,extreal_of_num_def,extreal_not_infty,lte_trans,pos_fn_integral_pos])
  ++ (MP_TAC o Q.SPEC `e` o UNDISCH o Q.SPECL [`(\i. pos_fn_integral m (f i))`,`s`] o INST_TYPE [alpha |-> beta]) EXTREAL_SUM_IMAGE_PROPERTY
  ++ RW_TAC std_ss []
  ++ `SIGMA (\i. pos_fn_integral m (f i)) s = pos_fn_integral m (\x. SIGMA (\i. f i x) s)`
       by METIS_TAC [IN_INSERT]
  ++ FULL_SIMP_TAC std_ss [DELETE_NON_ELEMENT]
  ++ `(\x. f e x + SIGMA (\i. f i x) s) = (\x. f e x + (\x. SIGMA (\i. f i x) s) x)` by METIS_TAC []
  ++ POP_ORW
  ++ MATCH_MP_TAC pos_fn_integral_add
  ++ FULL_SIMP_TAC std_ss [IN_INSERT]
  ++ RW_TAC std_ss []
  >> FULL_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_POS]
  ++ MATCH_MP_TAC IN_MEASURABLE_BOREL_SUM
  ++ Q.EXISTS_TAC `f` ++ Q.EXISTS_TAC `s`
  ++ METIS_TAC [measure_space_def,measurable_sets_def,subsets_def,m_space_def,space_def,extreal_of_num_def,extreal_not_infty,lt_infty,lte_trans]);

val pos_fn_integral_disjoint_sets = store_thm
  ("pos_fn_integral_disjoint_sets",``!m f s t. measure_space m /\ DISJOINT s t /\ s IN measurable_sets m /\ t IN measurable_sets m /\ 
		f IN measurable (m_space m,measurable_sets m) Borel /\ (!x. 0 <= f x)
		==> (pos_fn_integral m (\x. f x * indicator_fn (s UNION t) x) = 
		     pos_fn_integral m (\x. f x * indicator_fn s x) + pos_fn_integral m (\x. f x * indicator_fn t x))``,
  RW_TAC std_ss []
  ++ `(\x. f x * indicator_fn (s UNION t) x) = (\x. (\x. f x * indicator_fn s x) x + (\x. f x * indicator_fn t x) x)`
       by (RW_TAC std_ss [FUN_EQ_THM,indicator_fn_def,IN_DISJOINT,IN_UNION,mul_rone,mul_rzero]
           ++ Cases_on `x IN s` >> (RW_TAC std_ss [mul_rone,mul_rzero,add_rzero] ++ METIS_TAC [EXTENSION,IN_DISJOINT])
	   ++ RW_TAC std_ss [mul_rone,mul_rzero,add_lzero])
  ++ POP_ORW
  ++ `!s. s IN measurable_sets m ==> (\x. f x * indicator_fn s x) IN measurable (m_space m,measurable_sets m) Borel`
      by METIS_TAC [IN_MEASURABLE_BOREL_MUL_INDICATOR,measure_space_def,subsets_def,space_def]
  ++ MATCH_MP_TAC pos_fn_integral_add
  ++ FULL_SIMP_TAC std_ss [indicator_fn_def,mul_rone,mul_rzero]
  ++ RW_TAC std_ss [le_refl,mul_rzero,mul_rone]);

val pos_fn_integral_disjoint_sets_sum = store_thm
  ("pos_fn_integral_disjoint_sets_sum",``!m f s a. FINITE s /\ measure_space m /\
	(!i. i IN s ==> a i IN measurable_sets m) /\ (!x. 0 <= f x) /\ 
	(!i j. i IN s /\ j IN s /\ i <> j ==> DISJOINT (a i) (a j)) /\
	f IN measurable (m_space m,measurable_sets m) Borel 
	==> (pos_fn_integral m (\x. f x * indicator_fn (BIGUNION (IMAGE a s)) x) = 
	     SIGMA (\i. pos_fn_integral m (\x. f x * indicator_fn (a i) x)) s)``,

  Suff `!s:'b->bool. FINITE s ==> (\s:'b->bool. !m f a.  measure_space m /\
       (!i. i IN s ==> a i IN measurable_sets m) /\  (!x. 0 <= f x) /\ 
	(!i j. i IN s /\ j IN s /\ i <> j ==> DISJOINT (a i) (a j)) /\
	f IN measurable (m_space m,measurable_sets m) Borel 
	==> (pos_fn_integral m (\x. f x * indicator_fn (BIGUNION (IMAGE a s)) x) = 
	     SIGMA (\i. pos_fn_integral m (\x. f x * indicator_fn (a i) x)) s) ) s`
  >> RW_TAC std_ss []
  ++ MATCH_MP_TAC FINITE_INDUCT
  ++ RW_TAC std_ss [EXTREAL_SUM_IMAGE_EMPTY,IMAGE_EMPTY,BIGUNION_EMPTY,FINITE_INSERT,DELETE_NON_ELEMENT,IN_INSERT,BIGUNION_INSERT,IMAGE_INSERT]
  >> RW_TAC std_ss [indicator_fn_def,mul_rzero,mul_rone,NOT_IN_EMPTY,pos_fn_integral_zero]
  ++ (MP_TAC o Q.SPEC `e` o UNDISCH o Q.SPECL [`(\i. pos_fn_integral m (\x. f x * indicator_fn (a i) x))`,`s`] o INST_TYPE [alpha |-> beta]) EXTREAL_SUM_IMAGE_PROPERTY
  ++ `!x. (\i. pos_fn_integral m (\x. f x * indicator_fn (a i) x)) x <> NegInf`
       by (RW_TAC std_ss []
           ++ Suff `0 <= pos_fn_integral m (\x'. f x' * indicator_fn (a x) x')`
           >> METIS_TAC [lt_infty,extreal_not_infty,extreal_of_num_def,lte_trans]
	   ++ MATCH_MP_TAC pos_fn_integral_pos
	   ++ RW_TAC std_ss [indicator_fn_def,mul_rone,mul_rzero,le_refl])
  ++ RW_TAC std_ss []
  ++  `~(e IN s)` by METIS_TAC [DELETE_NON_ELEMENT]
  ++ `DISJOINT (a e) (BIGUNION (IMAGE a s))` 
       by (RW_TAC std_ss [DISJOINT_BIGUNION,IN_IMAGE] ++ METIS_TAC [])
  ++ `countable (IMAGE a s)` by METIS_TAC [image_countable,finite_countable]
  ++ `(IMAGE a s) SUBSET measurable_sets m` 
       by (RW_TAC std_ss [SUBSET_DEF,IMAGE_DEF,GSPECIFICATION]
	   ++ METIS_TAC [])
  ++ `BIGUNION (IMAGE a s) IN measurable_sets m`
	by METIS_TAC [sigma_algebra_def,measure_space_def,subsets_def,measurable_sets_def]
  ++ METIS_TAC [pos_fn_integral_disjoint_sets]);

val pos_fn_integral_suminf = store_thm
("pos_fn_integral_suminf", ``!m f. measure_space m /\ (!i x. 0 <= f i x) /\
      (!i. f i IN measurable (m_space m,measurable_sets m) Borel) ==>
      (pos_fn_integral m (\x. suminf (\i. f i x)) = suminf (\i. pos_fn_integral m (f i)))``,
  RW_TAC std_ss [ext_suminf_def]
  ++ RW_TAC std_ss [GSYM pos_fn_integral_sum,FINITE_COUNT]
  ++ `(\n. pos_fn_integral m (\x. SIGMA (\i. f i x) (count n))) = 
      (\n. pos_fn_integral m ((\n. (\x. SIGMA (\i. f i x) (count n)))n))` by METIS_TAC []
  ++ POP_ORW
  ++ MATCH_MP_TAC lebesgue_monotone_convergence
  ++ CONJ_TAC >> RW_TAC std_ss []
  ++ CONJ_TAC 
  >> (RW_TAC std_ss []
      ++ (MATCH_MP_TAC o INST_TYPE [beta |-> ``:num``]) IN_MEASURABLE_BOREL_SUM
      ++ Q.EXISTS_TAC `f`
      ++ Q.EXISTS_TAC `count i`
      ++ RW_TAC std_ss [FINITE_COUNT]
      >> FULL_SIMP_TAC std_ss [measure_space_def]
      ++ METIS_TAC [lt_infty,lte_trans,num_not_infty])
  ++ CONJ_TAC >> RW_TAC std_ss [FINITE_COUNT,EXTREAL_SUM_IMAGE_POS]
  ++ CONJ_TAC
  >> (RW_TAC std_ss [FINITE_COUNT,EXTREAL_SUM_IMAGE_POS,le_sup]
      ++ MATCH_MP_TAC le_trans
      ++ Q.EXISTS_TAC `SIGMA (\i. f i x) (count 1)`
      ++ RW_TAC std_ss [FINITE_COUNT,EXTREAL_SUM_IMAGE_POS]
      ++ POP_ASSUM MATCH_MP_TAC
      ++ ONCE_REWRITE_TAC [GSYM SPECIFICATION]
      ++ RW_TAC std_ss [IN_IMAGE,IN_UNIV]
      ++ METIS_TAC [])
  ++ RW_TAC std_ss [ext_mono_increasing_def]
  ++ MATCH_MP_TAC EXTREAL_SUM_IMAGE_MONO_SET
  ++ RW_TAC std_ss [FINITE_COUNT,SUBSET_DEF,IN_COUNT]
  ++ DECIDE_TAC);

(* ------------------------------------------------------------------------- *)
(* Integral for arbitrary functions                                          *)
(* ------------------------------------------------------------------------- *)


val integral_pos_fn = store_thm
("integral_pos_fn",``!m f. measure_space m /\ (!x. 0 <= f x) ==> (integral m f = pos_fn_integral m f)``,
  RW_TAC std_ss [integral_def]
  ++ Suff `((\x. if 0 < f x then f x else 0) = f) /\ ((\x. if f x < 0 then -f x else 0) = (\x. 0))`
  >> RW_TAC std_ss [pos_fn_integral_zero,sub_rzero]
  ++ RW_TAC std_ss [FUN_EQ_THM,lt_le]
  ++ METIS_TAC [lt_le,extreal_lt_def]);

val integral_indicator = store_thm
("integral_indicator",``!m s. measure_space m /\ s IN measurable_sets m ==>
         (integral m (indicator_fn s) = measure m s)``,
  RW_TAC std_ss []
  ++ `!x. 0 <= indicator_fn s x` by RW_TAC std_ss [indicator_fn_def,mul_rone,mul_rzero,le_refl,le_01]
  ++ METIS_TAC [pos_fn_integral_indicator,integral_pos_fn]);


(*
val finite_space_integral_reduce = store_thm
  ("finite_space_integral_reduce",
   ``!m f. measure_space m /\
	     f IN measurable (m_space m, measurable_sets m) Borel /\
	     FINITE (m_space m) ==>
		(integral m f = finite_space_integral m f)``,
   REPEAT STRIP_TAC
   ++ `?c n. BIJ c (count n) (IMAGE f (m_space m))` by RW_TAC std_ss [GSYM FINITE_BIJ_COUNT, IMAGE_FINITE]


   ++ `pos_simple_fn m (fn_plus f)
	(count n) (\i. PREIMAGE f {c i} INTER m_space m) (\i. if 0 <= real (c i) then real (c i) else 0) /\
	pos_simple_fn m (fn_minus f)
	(count n) (\i. PREIMAGE f {c i} INTER m_space m) (\i. if real (c i) <= 0:real then ~ real (c i) else 0)`
    by (RW_TAC std_ss [pos_simple_fn_def, FINITE_COUNT]

Suff `pos_simple_fn m (fn_plus f)
	(count n) (\i. PREIMAGE f {c i} INTER m_space m) (\i. if 0 <= real (c i) then real (c i) else 0) /\
	pos_simple_fn m (fn_minus f)
	(count n) (\i. PREIMAGE f {c i} INTER m_space m) (\i. if real (c i) <= 0:real then ~ real (c i) else 0)`
   

Q.EXISTS_TAC `\m. if m = n then e else c m`

   ++ `pos_simple_fn m (fn_plus f)
	(count n) (\i. PREIMAGE f {c i} INTER m_space m) (\i. if 0 <= c i then c i else 0) /\
	pos_simple_fn m (fn_minus f)
	(count n) (\i. PREIMAGE f {c i} INTER m_space m) (\i. if c i <= 0:real then ~ c i else 0)`
    by (RW_TAC std_ss [pos_simple_fn_def, FINITE_COUNT]
   << [RW_TAC real_ss [pos_part_def],
       `FINITE (count n)` by RW_TAC std_ss [FINITE_COUNT]
       ++ ONCE_REWRITE_TAC [(UNDISCH o Q.ISPEC `count n`) REAL_SUM_IMAGE_IN_IF]
       ++ FULL_SIMP_TAC std_ss [BIJ_DEF, INJ_DEF, SURJ_DEF, IN_IMAGE]
       ++ `?i. i IN count n /\ (f t = c i)` by METIS_TAC []
       ++ `(\x. (if x IN count n then (if 0 <= c x then c x else 0) *
			indicator_fn (PREIMAGE f {c x} INTER m_space m) t else 0)) =
		(\x. if (x = i) /\ 0 <= c i then c i else 0)`
		by (RW_TAC std_ss [FUN_EQ_THM]
		    ++ RW_TAC real_ss [indicator_fn_def, IN_PREIMAGE, IN_INTER]
		    ++ FULL_SIMP_TAC real_ss [IN_SING]
		    ++ METIS_TAC [])
       ++ POP_ORW
       ++ `count n = i INSERT ((count n) DELETE i)`
		by (RW_TAC std_ss [EXTENSION, IN_INSERT, IN_DELETE] ++ METIS_TAC [])
       ++ POP_ORW
       ++ ASM_SIMP_TAC std_ss [FINITE_INSERT, FINITE_DELETE, FINITE_COUNT,
			       REAL_SUM_IMAGE_THM, DELETE_DELETE]
       ++ `FINITE (count n DELETE i)` by RW_TAC std_ss [FINITE_COUNT, FINITE_DELETE]
       ++ ONCE_REWRITE_TAC [(UNDISCH o Q.ISPEC `count n DELETE i`) REAL_SUM_IMAGE_IN_IF]
       ++ SIMP_TAC std_ss [IN_DELETE]
       ++ (MP_TAC o Q.SPECL [`\x.0`, `0`] o UNDISCH o Q.ISPEC `count n DELETE i`)
		REAL_SUM_IMAGE_FINITE_CONST
       ++ RW_TAC real_ss [pos_part_def],
       `PREIMAGE f {c i} INTER m_space m =
	{w | w IN m_space m /\ (f w = (\n. c i) w)}`
		by (ONCE_REWRITE_TAC [EXTENSION] ++ RW_TAC std_ss [IN_INTER, IN_PREIMAGE, IN_SING, GSPECIFICATION, CONJ_SYM])
	++ POP_ORW
	++ MATCH_MP_TAC borel_measurable_eq_borel_measurable
	++ METIS_TAC [borel_measurable_const, measure_space_def],
	RW_TAC real_ss [],
	RW_TAC std_ss [DISJOINT_DEF]
        ++ ONCE_REWRITE_TAC [EXTENSION] ++ RW_TAC std_ss [IN_INTER, NOT_IN_EMPTY, IN_PREIMAGE, IN_SING]
	++ FULL_SIMP_TAC std_ss [BIJ_DEF, INJ_DEF, SURJ_DEF, IN_IMAGE] ++ METIS_TAC [],
	ONCE_REWRITE_TAC [EXTENSION] ++ RW_TAC std_ss [IN_BIGUNION_IMAGE, IN_INTER, IN_PREIMAGE, IN_SING]
       	++ FULL_SIMP_TAC std_ss [BIJ_DEF, INJ_DEF, SURJ_DEF, IN_IMAGE]
	++ METIS_TAC [],
	RW_TAC real_ss [neg_part_def, REAL_LT_IMP_LE, REAL_LE_RNEG]
        ++ FULL_SIMP_TAC std_ss [GSYM real_lt, REAL_LT_IMP_LE],
	`FINITE (count n)` by RW_TAC std_ss [FINITE_COUNT]
       ++ ONCE_REWRITE_TAC [(UNDISCH o Q.ISPEC `count n`) REAL_SUM_IMAGE_IN_IF]
       ++ FULL_SIMP_TAC std_ss [BIJ_DEF, INJ_DEF, SURJ_DEF, IN_IMAGE]
       ++ `?i. i IN count n /\ (f t = c i)` by METIS_TAC []
       ++ `(\x. (if x IN count n then (if c x <= 0 then ~ c x else 0) *
			indicator_fn (PREIMAGE f {c x} INTER m_space m) t else 0)) =
		(\x. if (x = i) /\ c i <= 0 then ~ c i else 0)`
		by (RW_TAC std_ss [FUN_EQ_THM]
		    ++ RW_TAC real_ss [indicator_fn_def, IN_PREIMAGE, IN_INTER]
		    ++ FULL_SIMP_TAC real_ss [IN_SING]
		    ++ METIS_TAC [])
       ++ POP_ORW
       ++ `count n = i INSERT ((count n) DELETE i)`
		by (RW_TAC std_ss [EXTENSION, IN_INSERT, IN_DELETE] ++ METIS_TAC [])
       ++ POP_ORW
       ++ ASM_SIMP_TAC std_ss [FINITE_INSERT, FINITE_DELETE, FINITE_COUNT,
			       REAL_SUM_IMAGE_THM, DELETE_DELETE]
       ++ `FINITE (count n DELETE i)` by RW_TAC std_ss [FINITE_COUNT, FINITE_DELETE]
       ++ ONCE_REWRITE_TAC [(UNDISCH o Q.ISPEC `count n DELETE i`) REAL_SUM_IMAGE_IN_IF]
       ++ SIMP_TAC std_ss [IN_DELETE]
       ++ (MP_TAC o Q.SPECL [`\x.0`, `0`] o UNDISCH o Q.ISPEC `count n DELETE i`)
		REAL_SUM_IMAGE_FINITE_CONST
       ++ RW_TAC real_ss [neg_part_def] ++ METIS_TAC [real_lt, REAL_LT_ANTISYM, REAL_LE_ANTISYM, REAL_NEG_0],
       `PREIMAGE f {c i} INTER m_space m =
	{w | w IN m_space m /\ (f w = (\n. c i) w)}`
		by (ONCE_REWRITE_TAC [EXTENSION] ++ RW_TAC std_ss [IN_INTER, IN_PREIMAGE, IN_SING, GSPECIFICATION, CONJ_SYM])
	++ POP_ORW
	++ MATCH_MP_TAC borel_measurable_eq_borel_measurable
	++ METIS_TAC [borel_measurable_const, measure_space_def],
	RW_TAC real_ss [REAL_LE_RNEG],
	RW_TAC std_ss [DISJOINT_DEF]
        ++ ONCE_REWRITE_TAC [EXTENSION] ++ RW_TAC std_ss [IN_INTER, NOT_IN_EMPTY, IN_PREIMAGE, IN_SING]
	++ FULL_SIMP_TAC std_ss [BIJ_DEF, INJ_DEF, SURJ_DEF, IN_IMAGE] ++ METIS_TAC [],
	ONCE_REWRITE_TAC [EXTENSION] ++ RW_TAC std_ss [IN_BIGUNION_IMAGE, IN_INTER, IN_PREIMAGE, IN_SING]
       	++ FULL_SIMP_TAC std_ss [BIJ_DEF, INJ_DEF, SURJ_DEF, IN_IMAGE]
	++ METIS_TAC []])

   ++ RW_TAC std_ss [integral_def,finite_space_integral_def,GSYM fn_plus_def,GSYM fn_minus_def]
   ++ (MP_TAC o Q.SPECL [`m`,`fn_plus (f :'a -> extreal)`,`count n`,`(\i. PREIMAGE (f :'a -> extreal) {c i} INTER m_space m)`,`(\i. if 0 <= real (c i) then real (c i) else 0)`]) pos_fn_integral_pos_simple_fn  
   ++ (MP_TAC o Q.SPECL [`m`,`fn_minus (f :'a -> extreal)`,`count n`,`(\i. PREIMAGE (f :'a -> extreal) {c i} INTER m_space m)`,`(\i. if real (c i) <= 0 then -real (c i) else 0)`]) pos_fn_integral_pos_simple_fn 
   ++ RW_TAC std_ss [pos_simple_fn_integral_def]

   ++ RW_TAC std_ss [pos_simple_fn_integral_def, real_sub]
   ++ `!x. ~x = ~1 * x` by RW_TAC real_ss [] ++ POP_ORW

   ++ RW_TAC std_ss [GSYM REAL_SUM_IMAGE_CMUL, FINITE_COUNT, GSYM REAL_SUM_IMAGE_ADD]
   ++ `(\i.
         (if 0 <= c i then c i else 0) * measure m (PREIMAGE f {c i} INTER m_space m) +
         ~1 *
         ((if c i <= 0 then ~c i else 0) * measure m (PREIMAGE f {c i} INTER m_space m))) =
	(\i. c i * measure m (PREIMAGE f {c i} INTER m_space m))`
	by (RW_TAC std_ss [FUN_EQ_THM] ++ RW_TAC real_ss []
	    ++ METIS_TAC [REAL_LE_TOTAL, REAL_LE_ANTISYM, REAL_MUL_LZERO, REAL_ADD_RID])
   ++ POP_ORW
   ++ `FINITE (count n)` by RW_TAC std_ss [FINITE_COUNT]
   ++ (MP_TAC o Q.ISPEC `c:num->real` o UNDISCH o Q.ISPEC `count n` o GSYM) REAL_SUM_IMAGE_IMAGE
   ++ Know `INJ c (count n) (IMAGE c (count n))`
   >> (FULL_SIMP_TAC std_ss [BIJ_DEF, INJ_DEF, IN_IMAGE] ++ METIS_TAC [])
   ++ SIMP_TAC std_ss [] ++ STRIP_TAC ++ STRIP_TAC
   ++ POP_ASSUM (MP_TAC o Q.SPEC `(\x:real. x * measure m (PREIMAGE f {x} INTER m_space m))`)
   ++ RW_TAC std_ss [o_DEF]
   ++ POP_ASSUM (K ALL_TAC) ++ POP_ASSUM (K ALL_TAC)
   ++ `(IMAGE c (count n)) = (IMAGE f (m_space m))`
	by (ONCE_REWRITE_TAC [EXTENSION] ++ RW_TAC std_ss [IN_IMAGE]
	    ++ FULL_SIMP_TAC std_ss [BIJ_DEF, INJ_DEF, SURJ_DEF, IN_IMAGE]
	    ++ METIS_TAC [])
   ++ RW_TAC std_ss []);
*)


(* ------------------------------------------------------------------------- *)
(* Radon Nikodym Theorem                                                     *)
(* ------------------------------------------------------------------------- *)


val seq_sup_def = Define `(seq_sup P 0 = @r. r IN P /\ sup P < r + 1) /\
       (seq_sup P (SUC n) = @r. r IN P /\ sup P < r + Normal ((1 / 2) pow (SUC n)) /\ (seq_sup P n) < r /\ r < sup P)`;



val EXTREAL_SUP_SEQ = store_thm
  ("EXTREAL_SUP_SEQ",``!P. (?x. P x) /\ (?z. z <> PosInf /\ !x. P x ==> x <= z) ==>
                    ?x. (!n. x n IN P) /\ (!n. x n <= x (SUC n)) /\ (sup (IMAGE x UNIV) = sup P)``,
  RW_TAC std_ss []
  ++ Cases_on `?z. P z /\ (z = sup P)`
  >> (Q.EXISTS_TAC `(\i. sup P)` 
      ++ RW_TAC std_ss [le_refl,SPECIFICATION]
      ++ `IMAGE (\i:num. sup P) UNIV = (\i. i = sup P)` by RW_TAC std_ss [EXTENSION,IN_IMAGE,IN_UNIV,IN_ABS]
      ++ RW_TAC std_ss [sup_const])
  ++ Cases_on `!x. P x ==> (x = NegInf)`
  >> (`sup P = NegInf` by METIS_TAC [sup_const_alt]
      ++ Q.EXISTS_TAC `(\n. NegInf)`
      ++ FULL_SIMP_TAC std_ss [le_refl]
      ++ RW_TAC std_ss []
      >> METIS_TAC []
      ++ METIS_TAC [UNIV_NOT_EMPTY,sup_const_over_set])
  ++ FULL_SIMP_TAC std_ss []
  ++ Q.EXISTS_TAC `seq_sup P`
  ++ FULL_SIMP_TAC std_ss []
  ++ `sup P <> PosInf` by METIS_TAC [sup_le,lt_infty,let_trans]
  ++ `!x. P x ==> x < sup P` by METIS_TAC [lt_le,le_sup_imp]
  ++ `!e. 0 < e ==> ?x. P x /\ sup P < x + e` by (RW_TAC std_ss [] ++ MATCH_MP_TAC sup_lt_epsilon ++ METIS_TAC [])
  ++ `!n. 0:real < (1 / 2) pow n` by METIS_TAC [HALF_POS,REAL_POW_LT]
  ++ `!n. 0 < Normal ((1 / 2) pow n)` by METIS_TAC [extreal_lt_eq,extreal_of_num_def]
  ++ `!n. seq_sup P n IN P`
      by (Induct
          >> (RW_TAC std_ss [seq_sup_def] 
	      ++ SELECT_ELIM_TAC
	      ++ RW_TAC std_ss []
	      ++ METIS_TAC [lt_01,SPECIFICATION])
          ++ RW_TAC std_ss [seq_sup_def] 
          ++ SELECT_ELIM_TAC
          ++ RW_TAC std_ss []
          ++ `?x. P x /\ seq_sup P n < x` by METIS_TAC [sup_lt,SPECIFICATION]
          ++ `?x. P x /\ sup P < x + Normal ((1 / 2) pow (SUC n))` by METIS_TAC []
          ++ Q.EXISTS_TAC `max x'' x'''` 
          ++ RW_TAC std_ss [extreal_max_def,SPECIFICATION]
          >> (`x''' < x''` by FULL_SIMP_TAC std_ss [GSYM extreal_lt_def]
              ++ `x''' +  Normal ((1 / 2) pow (SUC n)) <= x'' +  Normal ((1 / 2) pow (SUC n))` by METIS_TAC [lt_radd,lt_le,extreal_not_infty]
              ++ METIS_TAC [lte_trans])
          ++ METIS_TAC [lte_trans])
  ++ `!n. seq_sup P n <= seq_sup P (SUC n)`
      by (RW_TAC std_ss [seq_sup_def]
          ++ SELECT_ELIM_TAC
          ++ RW_TAC std_ss []
          >> (`?x. P x /\ seq_sup P n < x` by METIS_TAC [sup_lt,SPECIFICATION]
              ++ `?x. P x /\ sup P < x + Normal ((1 / 2) pow (SUC n))` by METIS_TAC []
              ++ Q.EXISTS_TAC `max x'' x'''` 
              ++ RW_TAC std_ss [extreal_max_def,SPECIFICATION] 
	      >> (`x''' < x''` by FULL_SIMP_TAC std_ss [GSYM extreal_lt_def]
                  ++ `x''' + Normal ((1 / 2) pow (SUC n)) <= x'' + Normal ((1 / 2) pow (SUC n))` by METIS_TAC [lt_radd,lt_le,extreal_not_infty]
                  ++ METIS_TAC [lte_trans])
	      ++ METIS_TAC [lte_trans])
	  ++ METIS_TAC [lt_le])
  ++ RW_TAC std_ss []
  ++ `!n. sup P <= seq_sup P n + Normal ((1 / 2) pow n)`
      by (Induct
	  >> (RW_TAC std_ss [seq_sup_def,pow,GSYM extreal_of_num_def]
	      ++ SELECT_ELIM_TAC
	      ++ RW_TAC std_ss []
	      >> METIS_TAC [lt_01,SPECIFICATION]
	      ++ METIS_TAC [lt_le])
	  ++ RW_TAC std_ss [seq_sup_def]
          ++ SELECT_ELIM_TAC
	  ++ RW_TAC std_ss []
	  >> (`?x. P x /\ seq_sup P n < x` by METIS_TAC [sup_lt,SPECIFICATION]
              ++ `?x. P x /\ sup P < x + Normal ((1 / 2) pow (SUC n))` by METIS_TAC []
              ++ Q.EXISTS_TAC `max x'' x'''` 
	      ++ RW_TAC std_ss [extreal_max_def,SPECIFICATION] 
	      >> (`x''' < x''` by FULL_SIMP_TAC std_ss [GSYM extreal_lt_def]
                  ++ `x''' + Normal ((1 / 2) pow (SUC n)) <= x'' + Normal ((1 / 2) pow (SUC n))` by METIS_TAC [lt_radd,lt_le,extreal_not_infty]
                  ++ METIS_TAC [lte_trans])
	      ++ METIS_TAC [lte_trans])
	  ++ METIS_TAC [lt_le])
  ++ RW_TAC std_ss [sup_eq] 
  >> (POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
      ++ RW_TAC std_ss [IN_IMAGE,IN_UNIV]
      ++ METIS_TAC [SPECIFICATION,lt_le])
  ++ MATCH_MP_TAC le_epsilon
  ++ RW_TAC std_ss []
  ++ `e <> NegInf` by METIS_TAC [lt_infty,extreal_of_num_def,lt_trans]
  ++ `?r. e = Normal r` by METIS_TAC [extreal_cases]
  ++ FULL_SIMP_TAC std_ss []
  ++ `?n. Normal ((1 / 2) pow n) < Normal r` by METIS_TAC [EXTREAL_ARCH_POW_INV]
  ++ MATCH_MP_TAC le_trans
  ++ Q.EXISTS_TAC `seq_sup P n + Normal ((1 / 2) pow n)`
  ++ RW_TAC std_ss []
  ++ MATCH_MP_TAC le_add2
  ++ FULL_SIMP_TAC std_ss [lt_le]
  ++ Q.PAT_X_ASSUM `!z. IMAGE (seq_sup P) UNIV z ==> z <= y` MATCH_MP_TAC
  ++ ONCE_REWRITE_TAC [GSYM SPECIFICATION]
  ++ RW_TAC std_ss [IN_UNIV,IN_IMAGE]
  ++ METIS_TAC []);
 
val EXTREAL_SUP_FUN_SEQ_IMAGE = store_thm
("EXTREAL_SUP_FUN_SEQ_IMAGE", ``!(P:extreal->bool) (P':('a->extreal)->bool) f. 
		(?x. P x) /\ (?z. z <> PosInf /\ !x. P x ==> x <= z) /\ (P = IMAGE f P')  
  	  	 ==> ?g. (!n:num. g n IN P') /\ (sup (IMAGE (\n. f (g n)) UNIV) = sup P)``,
  REPEAT STRIP_TAC
  ++ `?y. (!n. y n IN P) /\ (!n. y n <= y (SUC n)) /\ (sup (IMAGE y UNIV) = sup P)` by METIS_TAC [EXTREAL_SUP_SEQ]
  ++ Q.EXISTS_TAC `(\n. @r. (r IN P') /\ (f r  = y n))`
  ++ `(\n. f (@(r :α -> extreal). r IN (P' :(α -> extreal) -> bool) /\ ((f :(α -> extreal) -> extreal) r = (y :num -> extreal) n))) = y` by (rw [FUN_EQ_THM] ++ SELECT_ELIM_TAC
      ++ RW_TAC std_ss []
      ++ METIS_TAC [IN_IMAGE])
  ++ ASM_SIMP_TAC std_ss []
  ++ RW_TAC std_ss []
  >> (SELECT_ELIM_TAC
      ++ RW_TAC std_ss []
      ++ METIS_TAC [IN_IMAGE]));


val max_fn_seq_def = Define `(max_fn_seq g 0 x  = g 0 x ) /\
	 ((max_fn_seq g (SUC n) x) = max (max_fn_seq g n x) (g (SUC n) x))`;

val max_fn_seq_mono = store_thm
  ("max_fn_seq_mono", ``!g n x. max_fn_seq g n x <= max_fn_seq g (SUC n) x``,
   RW_TAC std_ss [max_fn_seq_def,extreal_max_def,le_refl]);


val EXTREAL_SUP_FUN_SEQ_MONO_IMAGE = store_thm
  ("EXTREAL_SUP_FUN_SEQ_MONO_IMAGE", ``!(P:extreal->bool) (P':('a->extreal)->bool). 
		(?x. P x) /\ (?z. z <> PosInf /\ !x. P x ==> x <= z) /\ (P = IMAGE f P') /\ 
  	  	(!g1 g2. (g1 IN P' /\ g2 IN P' /\ (!x. g1 x <= g2 x))  ==> f g1 <= f g2) /\
		(!g1 g2. g1 IN P' /\ g2 IN P' ==> (\x. max (g1 x) (g2 x)) IN P')  ==>
              ?g. (!n. g n IN P') /\ (!x n. g n x <= g (SUC n) x) /\ (sup (IMAGE (\n. f (g n)) UNIV) = sup P)``,
  REPEAT STRIP_TAC
  ++ `?g. (!n:num. g n IN P') /\ (sup (IMAGE (\n. f (g n)) UNIV) = sup P)` by METIS_TAC [EXTREAL_SUP_FUN_SEQ_IMAGE]
  ++ Q.EXISTS_TAC `max_fn_seq g`
  ++ `!n. max_fn_seq g n IN P'` 
      by (Induct
 	  >> (`max_fn_seq g 0 = g 0` by RW_TAC std_ss [FUN_EQ_THM,max_fn_seq_def]
	      ++ METIS_TAC [])
	      ++ `max_fn_seq g (SUC n) = (\x. max (max_fn_seq g n x) (g (SUC n) x))` by RW_TAC std_ss [FUN_EQ_THM,max_fn_seq_def]
	      ++ RW_TAC std_ss []
	      ++ METIS_TAC [])
  ++ `!g n x. max_fn_seq g n x <= max_fn_seq g (SUC n) x` by RW_TAC real_ss [max_fn_seq_def,extreal_max_def,le_refl]
  ++ CONJ_TAC >> RW_TAC std_ss []
  ++ CONJ_TAC >> RW_TAC std_ss []
  ++ `!n. (!x. g n x <= max_fn_seq g n x)` 
      by (Induct >> RW_TAC std_ss [max_fn_seq_def,le_refl]
	  ++ METIS_TAC [le_max2,max_fn_seq_def])
  ++ `!n. f (g n) <= f (max_fn_seq g n)` by METIS_TAC []
  ++ `sup (IMAGE (\n. f (g n)) UNIV) <= sup (IMAGE (\n. f (max_fn_seq g n)) UNIV)`
      by (MATCH_MP_TAC sup_le_sup_imp
          ++ RW_TAC std_ss []
	  ++ POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
	  ++ RW_TAC std_ss [IN_IMAGE,IN_UNIV]
	  ++ Q.EXISTS_TAC `f (max_fn_seq g n)`
	  ++ RW_TAC std_ss []
	  ++ ONCE_REWRITE_TAC [GSYM SPECIFICATION]
	  ++ RW_TAC std_ss [IN_IMAGE,IN_UNIV]
	  ++ METIS_TAC [])
  ++ `sup (IMAGE (\n. f (max_fn_seq g n)) UNIV) <= sup P`
      by (RW_TAC std_ss [sup_le]
          ++ POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
	  ++ RW_TAC std_ss [IN_IMAGE,IN_UNIV]
	  ++ MATCH_MP_TAC le_sup_imp
	  ++ ONCE_REWRITE_TAC [GSYM SPECIFICATION]
	  ++ RW_TAC std_ss [IN_IMAGE]
	  ++ METIS_TAC [])
  ++ METIS_TAC [le_antisym]);


val signed_measure_space_def = Define `
    signed_measure_space m = sigma_algebra (m_space m,measurable_sets m) /\ countably_additive m`;

val negative_set_def = Define `
    negative_set m A = A IN measurable_sets m /\ 
                      (!s. s IN measurable_sets m /\ s SUBSET A ==> measure m s <= 0)`;



(*

g `!m s. signed_measure_space m /\ s IN measurable_sets m /\ measure m s <= 0 ==> 
        ?A. negative_set m A /\ A SUBSET s /\ measure m A <= measure m s`;

A 0 = s 
t n = sup (IMAGE (measure m) {B | B IN measurable_sets m /\ B SUBSET A n})
0 <= t n
*)






(**********************************************************)
(*  Radon Nikodym Theorem                                 *)
(**********************************************************)


val RADON_F_def = Define `RADON_F m v = 
             {f |f IN measurable (m_space m,measurable_sets m) Borel /\ (!x. 0 <= f x) /\
	     !A. A IN measurable_sets m ==> (pos_fn_integral m (\x. f x * indicator_fn A x) <= measure v A)}`;

val RADON_F_integrals_def = Define `
	RADON_F_integrals m v = {r | ?f. (r = pos_fn_integral m f) /\ f IN RADON_F m v}`;

val measure_absolutely_continuous_def = Define `
	measure_absolutely_continuous m v = (!A. A IN measurable_sets m /\ (measure v A = 0) ==> (measure m A = 0))`;

val lemma_radon_max_in_F = store_thm
  ("lemma_radon_max_in_F",``!f g m v. (measure_space m /\ measure_space v /\ 
	(m_space v = m_space m) /\ (measurable_sets v = measurable_sets m) /\
        f IN RADON_F m v /\ g IN RADON_F m v)
	     ==> (\x. max (f x) (g x)) IN RADON_F m v``,
    RW_TAC real_ss [RADON_F_def,GSPECIFICATION,max_le,le_max]
    >> FULL_SIMP_TAC std_ss [IN_MEASURABLE_BOREL_MAX,measure_space_def]
    ++ Q.ABBREV_TAC `A1 = {x | x IN A /\ g x < f x}`
    ++ Q.ABBREV_TAC `A2 = {x | x IN A /\ f x <= g x}`
    ++ `DISJOINT A1 A2` 
         by (Q.UNABBREV_TAC `A1` ++ Q.UNABBREV_TAC `A2`
	   ++ RW_TAC std_ss [IN_DISJOINT,GSPECIFICATION]
	   ++ METIS_TAC [extreal_lt_def])
   ++ `A1 UNION A2 = A`
       by (Q.UNABBREV_TAC `A1` ++ Q.UNABBREV_TAC `A2`
	   ++ RW_TAC std_ss [IN_UNION,EXTENSION,GSPECIFICATION]
	   ++ METIS_TAC [extreal_lt_def])
   ++ `(\x. max (f x) (g x) * indicator_fn A x) = 
	   (\x. (\x. max (f x) (g x) * indicator_fn A1 x) x + 
	   (\x. max (f x) (g x) * indicator_fn A2 x) x)`
       by (Q.UNABBREV_TAC `A1` ++ Q.UNABBREV_TAC `A2`
	   ++ RW_TAC std_ss [indicator_fn_def,GSPECIFICATION,FUN_EQ_THM]
	   ++ Cases_on `g x < f x`
	   >> (RW_TAC std_ss [mul_rone,mul_rzero,add_rzero] ++ METIS_TAC [extreal_lt_def])
	   ++ RW_TAC real_ss [mul_rone,mul_rzero,add_lzero] ++ METIS_TAC [extreal_lt_def])
   ++ `additive v` by METIS_TAC [measure_space_def,sigma_algebra_def,COUNTABLY_ADDITIVE_ADDITIVE]
   ++ `A SUBSET m_space m` by RW_TAC std_ss [MEASURE_SPACE_SUBSET_MSPACE]
   ++ `A1 = ({x | g x < f x} INTER m_space m) INTER A` 
       by (Q.UNABBREV_TAC `A1` 
           ++ RW_TAC std_ss [EXTENSION,IN_INTER,GSPECIFICATION,CONJ_SYM]
	   ++ METIS_TAC [SUBSET_DEF])
   ++ `A2 = ({x | f x <= g x} INTER m_space m) INTER A`
       by (Q.UNABBREV_TAC `A2` 
           ++ RW_TAC std_ss [EXTENSION,IN_INTER,GSPECIFICATION,CONJ_SYM]
	   ++ METIS_TAC [SUBSET_DEF])
   ++ `A1 IN measurable_sets m`
       by (ASM_SIMP_TAC std_ss []
	   ++ MATCH_MP_TAC MEASURE_SPACE_INTER
	   ++ RW_TAC std_ss []
	   ++ METIS_TAC [IN_MEASURABLE_BOREL_LT,m_space_def,space_def,subsets_def,measurable_sets_def])
   ++ `A2 IN measurable_sets m`
       by (ASM_SIMP_TAC std_ss []
	   ++ MATCH_MP_TAC MEASURE_SPACE_INTER
	   ++ RW_TAC std_ss []
	   ++ METIS_TAC [IN_MEASURABLE_BOREL_LE,m_space_def,space_def,subsets_def,measurable_sets_def])
   ++ `measure v A = measure v A1 + measure v A2` by METIS_TAC [ADDITIVE]
   ++ Q.PAT_X_ASSUM `A1 = M` (K ALL_TAC)
   ++ Q.PAT_X_ASSUM `A2 = M` (K ALL_TAC)
   ++ `!x. max (f x) (g x) * indicator_fn A1 x = f x * indicator_fn A1 x`
       by (Q.UNABBREV_TAC `A1`
	   ++ RW_TAC std_ss [extreal_max_def,indicator_fn_def,GSPECIFICATION,mul_rone,mul_rzero]
	   ++ METIS_TAC [extreal_lt_def])
   ++ `!x. max (f x) (g x) * indicator_fn A2 x = g x * indicator_fn A2 x`
       by (Q.UNABBREV_TAC `A2`
	   ++ RW_TAC std_ss [extreal_max_def,indicator_fn_def,GSPECIFICATION,mul_rone,mul_rzero]
	   ++ METIS_TAC [extreal_lt_def])
   ++ ASM_SIMP_TAC std_ss []
   ++ `(\x. f x * indicator_fn A1 x) IN  measurable (m_space m,measurable_sets m) Borel` 
           by METIS_TAC [IN_MEASURABLE_BOREL_MUL_INDICATOR,measure_space_def,measurable_sets_def,subsets_def]
   ++ `(\x. g x * indicator_fn A2 x) IN  measurable (m_space m,measurable_sets m) Borel` 
           by METIS_TAC [IN_MEASURABLE_BOREL_MUL_INDICATOR,measure_space_def,measurable_sets_def,subsets_def]
   ++ `!x. 0 <= (\x. f x * indicator_fn A1 x) x` by RW_TAC std_ss [indicator_fn_def,mul_rone,mul_rzero,le_01,le_refl]
   ++ `!x. 0 <= (\x. g x * indicator_fn A2 x) x` by RW_TAC std_ss [indicator_fn_def,mul_rone,mul_rzero,le_01,le_refl]
   ++ FULL_SIMP_TAC std_ss [le_add2,pos_fn_integral_add]);

val lemma_radon_seq_conv_sup = store_thm
  ("lemma_radon_seq_conv_sup",``!f m v. (measure_space m /\ measure_space v /\ 
     (m_space v = m_space m) /\ (measurable_sets v = measurable_sets m)) /\ 
        (measure v (m_space v) <> PosInf) ==>
	?f_n. (!n. f_n n IN RADON_F m v) /\ (!x n. f_n n x <= f_n (SUC n) x) /\
	 (sup (IMAGE (\n. pos_fn_integral m (f_n n)) UNIV) = sup (RADON_F_integrals m v))``,
    RW_TAC std_ss [RADON_F_integrals_def]
    ++ MATCH_MP_TAC EXTREAL_SUP_FUN_SEQ_MONO_IMAGE
    ++ CONJ_TAC
    >> (Q.EXISTS_TAC `0`
	++ ONCE_REWRITE_TAC [GSYM SPECIFICATION]
	++ RW_TAC std_ss [GSPECIFICATION]
	++ Q.EXISTS_TAC `(\x. 0)`
	++ RW_TAC real_ss [RADON_F_def,GSPECIFICATION,pos_fn_integral_zero,mul_lzero,le_refl]
	>> (MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST
            ++ METIS_TAC [space_def,measure_space_def])
	++ METIS_TAC [measure_space_def,positive_def])
    ++ CONJ_TAC
    >> (Q.EXISTS_TAC `measure v (m_space v)`
	++ RW_TAC std_ss []
	++ POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
	++ RW_TAC std_ss [GSPECIFICATION,RADON_F_def]
	++ POP_ASSUM (MP_TAC o Q.SPEC `m_space m`)
	++ RW_TAC std_ss [MEASURE_SPACE_MSPACE_MEASURABLE, GSYM pos_fn_integral_mspace])
    ++  CONJ_TAC
    >> RW_TAC std_ss [EXTENSION,GSPECIFICATION,IN_IMAGE,RADON_F_def]
    ++ CONJ_TAC
    >> RW_TAC std_ss [RADON_F_def,GSPECIFICATION,pos_fn_integral_mono]
    ++ RW_TAC std_ss [lemma_radon_max_in_F]);


val RN_lemma1 = store_thm
("RN_lemma1",``!m v e. measure_space m /\ measure_space v /\ 0 < e /\ 
                       (m_space v = m_space m) /\
                       (measurable_sets v = measurable_sets m) /\ 
                       measure v (m_space m) <> PosInf /\ 
                       measure m (m_space m) <> PosInf ==>
       (?A. A IN measurable_sets m /\ measure m (m_space m) - measure v (m_space m) <= measure m A - measure v A /\
        !B. B IN measurable_sets m /\ B SUBSET A ==> -e < measure m B - measure v B)``,
  RW_TAC std_ss []
  ++ `!A. A IN measurable_sets m ==> measure m A <> NegInf` by METIS_TAC [MEASURE_SPACE_POSITIVE,positive_not_infty]
  ++ `!A. A IN measurable_sets m ==> measure m A <=  measure m (m_space m)` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE,MEASURE_SPACE_MSPACE_MEASURABLE,INCREASING,MEASURE_SPACE_INCREASING]
  ++ `!A. A IN measurable_sets m ==> measure m A <> PosInf` by METIS_TAC [lt_infty,let_trans]
  ++ `!A. A IN measurable_sets m ==> measure v A <> NegInf` by METIS_TAC [MEASURE_SPACE_POSITIVE,positive_not_infty,measure_def,measurable_sets_def]
  ++ `!A. A IN measurable_sets m ==> measure v A <=  measure v (m_space m)` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE,MEASURE_SPACE_MSPACE_MEASURABLE,INCREASING,MEASURE_SPACE_INCREASING]
  ++ `!A. A IN measurable_sets m ==> measure v A <> PosInf` by METIS_TAC [lt_infty,let_trans]
  ++ Q.ABBREV_TAC `d = (\A. measure m A - measure v A)`
  ++ `!A. A IN measurable_sets m ==> d A <> NegInf` by METIS_TAC [sub_not_infty]
  ++ `!A. A IN measurable_sets m ==> d A <> PosInf` by METIS_TAC [sub_not_infty]
  ++ `e <> NegInf` by METIS_TAC [lt_infty,lt_trans,num_not_infty]
  ++ Cases_on `e = PosInf`
  >> (Q.EXISTS_TAC `m_space m`
      ++ METIS_TAC [MEASURE_SPACE_MSPACE_MEASURABLE,le_refl,lt_infty,extreal_ainv_def])
  ++ Q.ABBREV_TAC `h = (\A. if (!B. B IN measurable_sets m /\ B SUBSET (m_space m DIFF A) ==> -e < d B) 
                            then {} else @B. B IN measurable_sets m /\ B SUBSET (m_space m DIFF A) /\ d B <= -e )`
  ++ `!A. A IN measurable_sets m ==> h A  IN measurable_sets m`
        by (RW_TAC std_ss [] 
	    ++ METIS_TAC [MEASURE_SPACE_EMPTY_MEASURABLE,extreal_lt_def])
  ++ Q.ABBREV_TAC `A = SIMP_REC {} (\a. a UNION h a)` 
  ++ `A 0 = {}` by METIS_TAC [SIMP_REC_THM]
  ++ `!n. A (SUC n) = (A n) UNION (h (A n))` by (Q.UNABBREV_TAC `A` ++ RW_TAC std_ss [SIMP_REC_THM])
  ++ `!n. A n IN measurable_sets m`
        by (Induct >> RW_TAC std_ss [MEASURE_SPACE_EMPTY_MEASURABLE]
	    ++ RW_TAC std_ss [MEASURE_SPACE_UNION])
  ++ `!n. (?B. B IN measurable_sets m /\ B SUBSET (m_space m DIFF (A n)) /\ d B <= -e) ==> 
               d (A (SUC n)) <= d (A n) - e`
       by (RW_TAC std_ss []
           ++ `~(!B. B IN measurable_sets m /\ B SUBSET (m_space m DIFF (A n)) ==> -e < d B)`
                 by METIS_TAC [extreal_lt_def]
           ++ `h (A n) = (@B. B IN measurable_sets m /\ B SUBSET m_space m DIFF (A n) /\ d B <= -e)`
                by (Q.UNABBREV_TAC `h` ++ RW_TAC std_ss [])
           ++ POP_ORW
	   ++ SELECT_ELIM_TAC
	   ++ RW_TAC std_ss []
	   >> METIS_TAC []
           ++ `DISJOINT (A n) x` 
               by (RW_TAC std_ss [DISJOINT_DEF,EXTENSION,IN_INTER,NOT_IN_EMPTY]
                   ++ METIS_TAC [SUBSET_DEF,IN_DIFF])
           ++ `d ((A n) UNION x) = d (A n) + d x`
                 by (Q.UNABBREV_TAC `d`
                     ++ RW_TAC std_ss []
		     ++ `measure m (A n UNION x) = measure m (A n) + measure m x`
                           by (MATCH_MP_TAC ADDITIVE
                               ++ FULL_SIMP_TAC std_ss [MEASURE_SPACE_ADDITIVE])
		     ++ `measure v (A n UNION x) = measure v (A n) + measure v x`
                           by (MATCH_MP_TAC ADDITIVE
                               ++ FULL_SIMP_TAC std_ss [MEASURE_SPACE_ADDITIVE])
		     ++ POP_ORW ++ POP_ORW
		     ++ `?r1. measure v (A n) = Normal r1` by METIS_TAC [extreal_cases]
		     ++ `?r2. measure v x = Normal r2` by METIS_TAC [extreal_cases]
		     ++ RW_TAC std_ss [extreal_add_def]
		     ++ Cases_on `measure m (A n)`
		     ++ Cases_on `measure m x`
		     ++ RW_TAC std_ss [extreal_add_def,extreal_sub_def,REAL_ADD2_SUB2]
		     ++ METIS_TAC [])
          ++ POP_ORW
	  ++ `d (A n) - e = d (A n) + -e` by METIS_TAC [extreal_sub_add]
	  ++ METIS_TAC [le_ladd])
  ++ `!n. d (A (SUC n)) <= d (A n)`
        by (RW_TAC std_ss []
            ++ Cases_on `(?B. B IN measurable_sets m /\ B SUBSET m_space m DIFF A n /\ d B <= -e)`
            >> (`d (A n) <= d (A n) + e` by METIS_TAC [lt_le,le_addr_imp]
		++ `d (A n) - e <= d (A n)` 
                     by (Cases_on `d(A n)` ++ Cases_on `e`
			 ++ RW_TAC std_ss [extreal_add_def,extreal_sub_def,extreal_le_def,extreal_not_infty,lt_infty,le_infty]
			 ++ METIS_TAC [extreal_add_def,extreal_le_def,REAL_LE_SUB_RADD])
		++ METIS_TAC [le_trans])
	    ++ `!B. B IN measurable_sets m /\ B SUBSET m_space m DIFF A n ==> -e < d B` by METIS_TAC [extreal_lt_def]
	    ++ METIS_TAC [UNION_EMPTY,le_refl])
  ++ Cases_on `?n. !B. ((B IN measurable_sets m /\ B SUBSET (m_space m DIFF (A n))) ==> -e < d B)`
  >> (Q.PAT_X_ASSUM `!n. A (SUC n) = a UNION b` (K ALL_TAC)
      ++ FULL_SIMP_TAC std_ss []
      ++ `!n. m_space m DIFF (A n) IN measurable_sets m` by METIS_TAC [MEASURE_SPACE_DIFF,MEASURE_SPACE_MSPACE_MEASURABLE]
      ++ Suff `!n. d (m_space m) <= d (m_space m DIFF (A n))`
      >> METIS_TAC []
      ++ Induct
      >> RW_TAC std_ss [DIFF_EMPTY,le_refl]
      ++ `measure m (m_space m DIFF A (SUC n')) = measure m (m_space m) - measure m (A (SUC n'))`
           by METIS_TAC [MEASURE_SPACE_FINITE_DIFF]
      ++ `measure v (m_space m DIFF A (SUC n')) = measure v (m_space m) - measure v (A (SUC n'))`
           by METIS_TAC [MEASURE_SPACE_FINITE_DIFF,measure_def,measurable_sets_def,m_space_def]
      ++ `measure m (m_space m DIFF A n') = measure m (m_space m) - measure m (A n')`
           by METIS_TAC [MEASURE_SPACE_FINITE_DIFF]
      ++ `measure v (m_space m DIFF A n') = measure v (m_space m) - measure v (A n')`
           by METIS_TAC [MEASURE_SPACE_FINITE_DIFF,measure_def,measurable_sets_def,m_space_def]
      ++ `d (m_space m DIFF A n') = d (m_space m) - d (A n')`
             by (Q.UNABBREV_TAC `d`
                 ++ FULL_SIMP_TAC std_ss []
		 ++ `?r1. measure m (m_space m) = Normal r1` by METIS_TAC [extreal_cases,MEASURE_SPACE_MSPACE_MEASURABLE]
		 ++ `?r2. measure v (m_space m) = Normal r2` by METIS_TAC [extreal_cases,MEASURE_SPACE_MSPACE_MEASURABLE]
		 ++ `?r3. measure m (A n') = Normal r3` by METIS_TAC [extreal_cases]
		 ++ `?r4. measure v (A n') = Normal r4` by METIS_TAC [extreal_cases]
                 ++ FULL_SIMP_TAC std_ss [extreal_add_def,extreal_sub_def,extreal_lt_def,extreal_11]
		 ++ REAL_ARITH_TAC)
      ++ `d (m_space m DIFF A (SUC n')) = d (m_space m) - d (A (SUC n'))`
             by (Q.UNABBREV_TAC `d`
                 ++ FULL_SIMP_TAC std_ss []
		 ++ `?r1. measure m (m_space m) = Normal r1` by METIS_TAC [extreal_cases,MEASURE_SPACE_MSPACE_MEASURABLE]
		 ++ `?r2. measure v (m_space m) = Normal r2` by METIS_TAC [extreal_cases,MEASURE_SPACE_MSPACE_MEASURABLE]
		 ++ `?r3. measure m (A (SUC n')) = Normal r3` by METIS_TAC [extreal_cases]
		 ++ `?r4. measure v (A (SUC n')) = Normal r4` by METIS_TAC [extreal_cases]
                 ++ FULL_SIMP_TAC std_ss [extreal_add_def,extreal_sub_def,extreal_lt_def,extreal_11]
		 ++ REAL_ARITH_TAC)
      ++ FULL_SIMP_TAC std_ss []
      ++ `d (m_space m) - d (A n') <= d (m_space m) - d (A (SUC n'))`
           by METIS_TAC [extreal_sub_add,MEASURE_SPACE_MSPACE_MEASURABLE,le_ladd_imp,le_neg]
      ++ METIS_TAC [le_trans])
  ++ `!n. ?B. B IN measurable_sets m /\ B SUBSET (m_space m DIFF (A n)) /\ d B <= -e`
        by METIS_TAC [extreal_lt_def]
  ++ `!n. d (A n) <= - &n * e`
       by (Induct
           >> METIS_TAC [mul_lzero,neg_0,le_refl,MEASURE_EMPTY,measure_def,sub_rzero]
           ++ `d (A (SUC n)) <= d (A n) - e` by METIS_TAC []
           ++ `?r1. d (A n) = Normal r1` by METIS_TAC [extreal_cases]
           ++ `?r2. d (A (SUC n)) = Normal r2` by METIS_TAC [extreal_cases]
	   ++ `e <> PosInf` by ( METIS_TAC [extreal_sub_def,le_infty,extreal_not_infty])
	   ++ `?r3. e = Normal r3` by METIS_TAC [extreal_cases]
	   ++ FULL_SIMP_TAC std_ss [extreal_sub_def,extreal_le_def,extreal_ainv_def,extreal_of_num_def,extreal_mul_def]
	   ++ RW_TAC std_ss [ADD1,GSYM REAL_ADD,REAL_NEG_ADD,REAL_ADD_RDISTRIB,GSYM REAL_NEG_MINUS1]
	   ++ `r1 + -r3 <= -&n * r3 + -r3` by METIS_TAC [REAL_LE_ADD2,REAL_LE_REFL]
	   ++ METIS_TAC [real_sub,REAL_LE_TRANS])
  ++ `!n. - d (A n) <= - d (A (SUC n))` by METIS_TAC [le_neg]
  ++ `!n. A n SUBSET A (SUC n)` by METIS_TAC [SUBSET_UNION]
  ++ `sup (IMAGE (measure m o A) UNIV) = measure m (BIGUNION (IMAGE A UNIV))`
       by METIS_TAC [MONOTONE_CONVERGENCE2,IN_FUNSET,IN_UNIV,measure_def,measurable_sets_def]
  ++ `sup (IMAGE (measure v o A) UNIV) = measure v (BIGUNION (IMAGE A UNIV))`
       by METIS_TAC [MONOTONE_CONVERGENCE2,IN_FUNSET,IN_UNIV,measure_def,measurable_sets_def]
  ++ FULL_SIMP_TAC std_ss [o_DEF]
  ++ `?r1. !n. measure m (A n) = Normal (r1 n)` 
       by (Q.EXISTS_TAC `(\n. @r. measure m (A n) = Normal r)`
           ++ RW_TAC std_ss []
	   ++ SELECT_ELIM_TAC
	   ++ METIS_TAC [extreal_cases])
  ++ `?r2. !n. measure v (A n) = Normal (r2 n)` 
       by (Q.EXISTS_TAC `(\n. @r. measure v (A n) = Normal r)`
           ++ RW_TAC std_ss []
	   ++ SELECT_ELIM_TAC
	   ++ METIS_TAC [extreal_cases])
  ++ `BIGUNION (IMAGE A UNIV) IN measurable_sets m` by METIS_TAC [SIGMA_ALGEBRA_ENUM,measure_space_def,subsets_def,measurable_sets_def,IN_FUNSET,IN_UNIV]
  ++ `?l1. measure m (BIGUNION (IMAGE A UNIV)) = Normal l1` by METIS_TAC [extreal_cases]
  ++ `?l2. measure v (BIGUNION (IMAGE A UNIV)) = Normal l2` by METIS_TAC [extreal_cases]
  ++ FULL_SIMP_TAC std_ss []
  ++ `mono_increasing r1` by METIS_TAC [mono_increasing_def,mono_increasing_suc,MEASURE_SPACE_INCREASING,increasing_def,extreal_le_def]		
  ++ `mono_increasing r2` by METIS_TAC [mono_increasing_def,mono_increasing_suc,MEASURE_SPACE_INCREASING,increasing_def,extreal_le_def,measure_def,measurable_sets_def]
  ++ FULL_SIMP_TAC std_ss [GSYM sup_seq]
  ++ `!n. -d (A n) = Normal (r2 n - r1 n)` 
        by (Q.UNABBREV_TAC `d`
            ++ RW_TAC std_ss [extreal_sub_def,extreal_ainv_def,REAL_NEG_SUB])
  ++ Q.ABBREV_TAC `r = (\n. r2 n - r1 n)`
  ++ `mono_increasing r` by METIS_TAC [mono_increasing_suc, extreal_le_def]
  ++ `r --> (l2 - l1)` by (Q.UNABBREV_TAC `r` ++ METIS_TAC [SEQ_SUB])
  ++ `sup (IMAGE (\n. Normal (r n)) UNIV) = Normal (l2 - l1)` by METIS_TAC [sup_seq]
  ++ `sup (IMAGE (\n. -d (A n)) UNIV) = -d (BIGUNION (IMAGE A UNIV))` 
        by (`(\n. -d (A n)) = (\n. Normal (r n))` by METIS_TAC []
            ++ POP_ORW
	    ++ Q.UNABBREV_TAC `d`
	    ++ RW_TAC std_ss [extreal_sub_def,extreal_ainv_def,REAL_NEG_SUB])
  ++ `d (BIGUNION (IMAGE A UNIV)) <> NegInf` by METIS_TAC []
  ++ `- d (BIGUNION (IMAGE A UNIV)) <> PosInf` by METIS_TAC [extreal_ainv_def,extreal_cases,extreal_not_infty]
  ++ `?n. - d (BIGUNION (IMAGE A UNIV)) < &n * e` by METIS_TAC [EXTREAL_ARCH]
  ++ `&n * e <= -d (A n)` by METIS_TAC [le_neg,neg_neg,mul_lneg]
  ++ `-d (BIGUNION (IMAGE A univ(:num))) < -d (A n)` by METIS_TAC [lte_trans]
  ++ `-d (A n) <= - d (BIGUNION (IMAGE A UNIV))`
       by (RW_TAC std_ss []
           ++ Q.PAT_X_ASSUM `sup P = -d Q` (MP_TAC o GSYM)
           ++ DISCH_THEN (fn th => REWRITE_TAC [th])
	   ++ MATCH_MP_TAC le_sup_imp
           ++ ONCE_REWRITE_TAC [GSYM SPECIFICATION]
           ++ RW_TAC std_ss [IN_IMAGE,IN_UNIV]
	   ++ METIS_TAC [])
  ++ METIS_TAC [extreal_lt_def]);
   

val RN_lemma2 = store_thm
("RN_lemma2",``!m v. measure_space m /\ measure_space v /\ 
         (m_space v = m_space m) /\
         (measurable_sets v = measurable_sets m) /\
         measure v (m_space m) <> PosInf /\
         measure m (m_space m) <> PosInf ==>
         (?A. A IN measurable_sets m /\ measure m (m_space m) - measure v (m_space m) <= measure m A - measure v A /\
         !B. B IN measurable_sets m /\ B SUBSET A ==> 0 <= measure m B - measure v B)``,
  RW_TAC std_ss []
  ++ Q.ABBREV_TAC `d = (\a. measure m a - measure v a)`
  ++ Q.ABBREV_TAC `p = (\a b n. a IN measurable_sets m /\ a SUBSET b /\ d b <= d a /\ (!c. c IN measurable_sets m /\ c SUBSET a ==> -(Normal ((1 / 2) pow n)) < d c))`
  ++ Q.ABBREV_TAC `sts = (\s. IMAGE (\A. s INTER A) (measurable_sets m))`
  ++ `!s t. s IN measurable_sets m /\ t IN sts s ==> t IN measurable_sets m`
        by (RW_TAC std_ss []
            ++ Q.UNABBREV_TAC `sts`
	    ++ FULL_SIMP_TAC std_ss [IN_IMAGE,MEASURE_SPACE_INTER])
  ++ `!s t. t IN sts s ==> t SUBSET s`
        by (RW_TAC std_ss []
            ++ Q.UNABBREV_TAC `sts`
	    ++ FULL_SIMP_TAC std_ss [IN_IMAGE,INTER_SUBSET])
  ++ `!s. s IN measurable_sets m ==> measure_space (s, sts s, measure m)` by METIS_TAC [MEASURE_SPACE_RESTRICTED]
  ++ `!s. s IN measurable_sets m ==> measure_space (s, sts s, measure v)` by METIS_TAC [MEASURE_SPACE_RESTRICTED]
  ++ `!n. 0 < Normal ((1 / 2) pow n)` by METIS_TAC [extreal_lt_eq,extreal_of_num_def,POW_HALF_POS]
  ++ `!s. s IN measurable_sets m ==> measure m s <> PosInf` by METIS_TAC [MEASURE_SPACE_FINITE_MEASURE]
  ++ `!s. s IN measurable_sets m ==> measure v s <> PosInf` by METIS_TAC [MEASURE_SPACE_FINITE_MEASURE]
  ++ `!s. s IN measurable_sets m ==> measure m s <> NegInf` by METIS_TAC [MEASURE_SPACE_POSITIVE,positive_not_infty]
  ++ `!s. s IN measurable_sets m ==> measure v s <> NegInf` by METIS_TAC [MEASURE_SPACE_POSITIVE,positive_not_infty]
  ++ `!s n. s IN measurable_sets m ==> ?A. p A s n`
         by (RW_TAC std_ss []
             ++ `?A. A IN (sts s) /\ measure m s - measure v s <= measure m A - measure v A /\
                (!B. B IN (sts s) /\ B SUBSET A ==>  -Normal ((1 / 2) pow n) < measure m B - measure v B)` 
                 by (RW_TAC std_ss []
                     ++ (MP_TAC o Q.SPECL [`(s,sts s,measure m)`,`(s,sts s,measure v)`,`Normal ((1 / 2) pow n)`]) RN_lemma1
	             ++ RW_TAC std_ss [m_space_def,measure_def,measurable_sets_def])
	     ++ Q.EXISTS_TAC `A`
	     ++ Q.UNABBREV_TAC `p`
	     ++ FULL_SIMP_TAC std_ss [measure_def]
             ++ RW_TAC std_ss []
	     << [METIS_TAC [],METIS_TAC [],

                 `A SUBSET s` by METIS_TAC []
		 ++ Suff `c IN sts s`
		 >> METIS_TAC []
                 ++ Q.UNABBREV_TAC `sts`
		 ++ FULL_SIMP_TAC std_ss [IN_IMAGE]
		 ++ Q.EXISTS_TAC `c`
		 ++ METIS_TAC [SUBSET_INTER2,SUBSET_TRANS]])
  ++ Q.ABBREV_TAC `A = PRIM_REC (m_space m) (\a n. @b. p b a n)` 
  ++ `A 0 = m_space m` by METIS_TAC [PRIM_REC_THM]
  ++ `!n. A (SUC n) = @b. p b (A n) n` 
        by (Q.UNABBREV_TAC `A` ++ RW_TAC std_ss [PRIM_REC_THM])
  ++ `!n. A n IN measurable_sets m`
       by (Induct >> METIS_TAC [MEASURE_SPACE_MSPACE_MEASURABLE]
           ++ RW_TAC std_ss []
	   ++ SELECT_ELIM_TAC
	   ++ FULL_SIMP_TAC std_ss []
 	   ++ METIS_TAC [])
  ++ `!n. p (A (SUC n)) (A n) n` by METIS_TAC []
  ++ `!n. A (SUC n) SUBSET (A n)` by METIS_TAC []
  ++ `!n. d (A n) <= d (A (SUC n))` by METIS_TAC []
  ++ `!n c. (c IN measurable_sets m /\ c SUBSET (A (SUC n)) ==> - Normal ((1 / 2) pow n) < d c)` by METIS_TAC []
  ++ Q.EXISTS_TAC `BIGINTER (IMAGE A UNIV)`
  ++ CONJ_TAC
  >> METIS_TAC [SIGMA_ALGEBRA_FN_BIGINTER,IN_UNIV,IN_FUNSET,subsets_def,measurable_sets_def,measure_space_def]
  ++ REVERSE CONJ_TAC
  >> (RW_TAC std_ss []
      ++ SPOSE_NOT_THEN ASSUME_TAC
      ++ FULL_SIMP_TAC std_ss [GSYM extreal_lt_def]
      ++ `0 < - (measure m B - measure v B)` by METIS_TAC [lt_neg,neg_0]
      ++ `?n. measure m B - measure v B < -Normal ((1 / 2) pow n)` by METIS_TAC [EXTREAL_ARCH_POW_INV,lt_neg,neg_neg]
      ++ `d B < -Normal ((1 / 2) pow n)` by METIS_TAC []
      ++ `!n. B SUBSET A n` by METIS_TAC [SUBSET_BIGINTER,IN_IMAGE,IN_UNIV]
      ++ METIS_TAC [lt_antisym])
  ++ `measure m (BIGINTER (IMAGE A UNIV)) = inf (IMAGE (measure m o A) UNIV)`
        by (MATCH_MP_TAC (GSYM MONOTONE_CONVERGENCE_BIGINTER2)
            ++ RW_TAC std_ss [IN_UNIV,IN_FUNSET])
  ++ `measure v (BIGINTER (IMAGE A UNIV)) = inf (IMAGE (measure v o A) UNIV)`
        by (MATCH_MP_TAC (GSYM MONOTONE_CONVERGENCE_BIGINTER2)
            ++ RW_TAC std_ss [IN_UNIV,IN_FUNSET])
  ++ `?r1. !n. measure m (A n) = Normal (r1 n)` 
       by (Q.EXISTS_TAC `(\n. @r. measure m (A n) = Normal r)`
           ++ RW_TAC std_ss []
	   ++ SELECT_ELIM_TAC
	   ++ METIS_TAC [extreal_cases])
  ++ `?r2. !n. measure v (A n) = Normal (r2 n)` 
       by (Q.EXISTS_TAC `(\n. @r. measure v (A n) = Normal r)`
           ++ RW_TAC std_ss []
	   ++ SELECT_ELIM_TAC
	   ++ METIS_TAC [extreal_cases])
  ++ `BIGINTER (IMAGE A UNIV) IN measurable_sets m` by METIS_TAC [MEASURE_SPACE_BIGINTER]
  ++ `?l1. measure m (BIGINTER (IMAGE A UNIV)) = Normal l1` by METIS_TAC [extreal_cases]
  ++ `?l2. measure v (BIGINTER (IMAGE A UNIV)) = Normal l2` by METIS_TAC [extreal_cases]
  ++ FULL_SIMP_TAC std_ss [o_DEF]
  ++ Q.PAT_X_ASSUM `Normal l1 = Q` (MP_TAC o GSYM)
  ++ Q.PAT_X_ASSUM `Normal l2 = Q` (MP_TAC o GSYM)
  ++ RW_TAC std_ss [extreal_sub_def]
  ++ `mono_decreasing r1` by METIS_TAC [mono_decreasing_def,mono_decreasing_suc,MEASURE_SPACE_INCREASING,increasing_def,extreal_le_def]		
  ++ `mono_decreasing r2` by METIS_TAC [mono_decreasing_def,mono_decreasing_suc,MEASURE_SPACE_INCREASING,increasing_def,extreal_le_def,measure_def,measurable_sets_def]
  ++ FULL_SIMP_TAC std_ss [GSYM inf_seq]
  ++ `!n. -d (A n) = Normal (r2 n - r1 n)` 
        by (Q.UNABBREV_TAC `d`
            ++ RW_TAC std_ss [extreal_sub_def,extreal_ainv_def,REAL_NEG_SUB])
  ++ Q.ABBREV_TAC `r = (\n. r2 n - r1 n)`
  ++ `!n. -d (A (SUC n)) <= -d (A n)` by METIS_TAC [le_neg]
  ++ `mono_decreasing r` by METIS_TAC [mono_decreasing_suc, extreal_le_def,extreal_ainv_def]
  ++ `r --> (l2 - l1)` by (Q.UNABBREV_TAC `r` ++ METIS_TAC [SEQ_SUB])
  ++ `inf (IMAGE (\n. Normal (r n)) UNIV) = Normal (l2 - l1)` by METIS_TAC [inf_seq]
  ++ `inf (IMAGE (\n. -d (A n)) UNIV) = -d (BIGINTER (IMAGE A UNIV))` 
        by (`(\n. -d (A n)) = (\n. Normal (r n))` by METIS_TAC []
            ++ POP_ORW
	    ++ Q.UNABBREV_TAC `d`
	    ++ RW_TAC std_ss [extreal_sub_def,extreal_ainv_def,REAL_NEG_SUB])
  ++ FULL_SIMP_TAC std_ss [inf_eq]
  ++ `-d (BIGINTER (IMAGE A univ(:num))) <= -d (A 0)`
         by (Q.PAT_X_ASSUM `!y. Q ==> -d (BIGINTER (IMAGE A univ(:num))) <= y` MATCH_MP_TAC
             ++ ONCE_REWRITE_TAC [GSYM SPECIFICATION]
	     ++ RW_TAC std_ss [IN_IMAGE,IN_UNIV]
	     ++ METIS_TAC [])
  ++ `d (m_space m) <= d (BIGINTER (IMAGE A UNIV))` by METIS_TAC [le_neg]
  ++ Suff `d (BIGINTER (IMAGE A UNIV)) = Normal (l1 - l2)`
  >> METIS_TAC []
  ++ Q.UNABBREV_TAC `d`
  ++ METIS_TAC [extreal_sub_def]);

val Radon_Nikodym = store_thm
  ("Radon_Nikodym",``!m v. measure_space m /\ measure_space v /\ (m_space v = m_space m) /\
         (measurable_sets v = measurable_sets m) /\
         (measure v (m_space v) <> PosInf) /\ (measure m (m_space m) <> PosInf) /\ 
          measure_absolutely_continuous v m
            ==> (?f. f IN measurable (m_space m,measurable_sets m) Borel /\ (!x. 0 <= f x) /\  
                (!A. A IN measurable_sets m ==> (pos_fn_integral m (\x. f x * indicator_fn A x) = measure v A)))``,
  RW_TAC std_ss []
  ++ `?f_n. (!n. f_n n IN RADON_F m v) /\ (!x n. f_n n x <= f_n (SUC n) x) /\
           (sup (IMAGE (\n. pos_fn_integral m (f_n n)) univ(:num)) = sup (RADON_F_integrals m v))` 
       by RW_TAC std_ss [lemma_radon_seq_conv_sup]
  ++ Q.ABBREV_TAC `g = (\x. sup (IMAGE (\n. f_n n x) UNIV))`
  ++ Q.EXISTS_TAC `g`
  ++ `g IN measurable (m_space m,measurable_sets m) Borel`
      by (MATCH_MP_TAC IN_MEASURABLE_BOREL_MONO_SUP
          ++ Q.EXISTS_TAC `f_n`
          ++ FULL_SIMP_TAC std_ss [RADON_F_def,GSPECIFICATION,measure_space_def,space_def]
          ++ Q.UNABBREV_TAC `g`
          ++ RW_TAC std_ss [])
  ++ `!x. 0 <= g x` 
       by (Q.UNABBREV_TAC `g`
           ++ RW_TAC std_ss [le_sup]
           ++ MATCH_MP_TAC le_trans
	   ++ Q.EXISTS_TAC `f_n 0 x`
	   ++ RW_TAC std_ss []
	   >> FULL_SIMP_TAC std_ss [RADON_F_def,GSPECIFICATION]
	   ++ POP_ASSUM MATCH_MP_TAC
	   ++ ONCE_REWRITE_TAC [GSYM SPECIFICATION]
	   ++ RW_TAC std_ss [IN_IMAGE,IN_UNIV]
	   ++ METIS_TAC [])
  ++ RW_TAC std_ss []
  ++ `!A. A IN measurable_sets m ==> (pos_fn_integral m (\x. g x * indicator_fn A x) = sup (IMAGE (\n. pos_fn_integral m (\x. f_n n x * indicator_fn A x)) UNIV))`
       by (RW_TAC std_ss []
	   ++ MATCH_MP_TAC lebesgue_monotone_convergence_subset
           ++ FULL_SIMP_TAC std_ss [RADON_F_def,GSPECIFICATION,ext_mono_increasing_suc]
	   ++ RW_TAC std_ss []
	   ++ Q.UNABBREV_TAC `g`
	   ++ METIS_TAC [])
  ++ `g IN RADON_F m v` 
      by (FULL_SIMP_TAC std_ss [RADON_F_def,GSPECIFICATION,sup_le]
          ++ RW_TAC std_ss []
	  ++ POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
	  ++ RW_TAC std_ss [IN_IMAGE,IN_UNIV]
	  ++ METIS_TAC [])
  ++ `pos_fn_integral m g = sup (IMAGE (\n:num. pos_fn_integral m (f_n n)) UNIV)`
       by (MATCH_MP_TAC lebesgue_monotone_convergence
           ++ FULL_SIMP_TAC std_ss [RADON_F_def,GSPECIFICATION,ext_mono_increasing_suc]
	   ++ Q.UNABBREV_TAC `g`
	   ++ METIS_TAC [])
  ++ `pos_fn_integral m g = sup (RADON_F_integrals m v)` by FULL_SIMP_TAC std_ss []
  ++ Q.ABBREV_TAC `nu = (\A. measure v A - pos_fn_integral m (\x. g x * indicator_fn A x))`
  ++ `!A. A IN measurable_sets m ==> pos_fn_integral m (\x. g x * indicator_fn A x) <= measure v A`
       by FULL_SIMP_TAC std_ss [RADON_F_def,GSPECIFICATION]
  ++ `!A. A IN measurable_sets m ==> measure v A <> PosInf` by METIS_TAC [lt_infty,INCREASING,MEASURE_SPACE_INCREASING,MEASURE_SPACE_SUBSET_MSPACE,MEASURE_SPACE_MSPACE_MEASURABLE,let_trans]
  ++ `!A. A IN measurable_sets m ==> measure m A <> PosInf` by METIS_TAC [lt_infty,INCREASING,MEASURE_SPACE_INCREASING,MEASURE_SPACE_SUBSET_MSPACE,MEASURE_SPACE_MSPACE_MEASURABLE,let_trans]
  ++ `!A x. 0 <= (\x. g x * indicator_fn A x) x` by RW_TAC std_ss [indicator_fn_def,mul_rzero,mul_rone,le_01,le_refl]
  ++ `!A. A IN measurable_sets m ==> 0 <= pos_fn_integral m (\x. g x * indicator_fn A x)` 
          by (REPEAT STRIP_TAC ++ MATCH_MP_TAC pos_fn_integral_pos ++ METIS_TAC [])
  ++ `!A. A IN measurable_sets m ==> pos_fn_integral m (\x. g x * indicator_fn A x) <> NegInf` by METIS_TAC [lt_infty,extreal_of_num_def,extreal_not_infty,lte_trans]
  ++ `!A. A IN measurable_sets m ==> pos_fn_integral m (\x. g x * indicator_fn A x) <> PosInf` by METIS_TAC [let_trans,lt_infty]
  ++ `!A. A IN measurable_sets m ==> 0 <= nu A`
       by (RW_TAC std_ss []
           ++ FULL_SIMP_TAC std_ss [RADON_F_def,GSPECIFICATION]
	   ++ `pos_fn_integral m (\x. g x * indicator_fn A' x) <= measure v A'` by FULL_SIMP_TAC std_ss []
           ++ `pos_fn_integral m (\x. g x * indicator_fn A' x) <> PosInf` by METIS_TAC [lt_infty,INCREASING,MEASURE_SPACE_INCREASING,MEASURE_SPACE_SUBSET_MSPACE,MEASURE_SPACE_MSPACE_MEASURABLE,let_trans]
           ++ Q.UNABBREV_TAC `nu` ++ METIS_TAC [sub_zero_le])
  ++ `positive (m_space m,measurable_sets m,nu)`
       by (RW_TAC std_ss [positive_def,measure_def,measurable_sets_def]
	   ++ Q.UNABBREV_TAC `nu`
	   ++ RW_TAC std_ss [MEASURE_EMPTY,indicator_fn_def,NOT_IN_EMPTY,pos_fn_integral_zero,mul_rzero,mul_rone,sub_rzero])
  ++ Q.PAT_X_ASSUM `!A. A IN measurable_sets m ==> (pos_fn_integral m (\x. g x * indicator_fn A x) = Q)` (K ALL_TAC)
  ++ RW_TAC std_ss []
  ++ `measure_space (m_space m,measurable_sets m,nu)` 
      by (FULL_SIMP_TAC std_ss [measure_space_def,m_space_def,measurable_sets_def,countably_additive_def,measure_def]
          ++ Q.UNABBREV_TAC `nu`
          ++ RW_TAC std_ss [o_DEF]
	  ++ `suminf (\x. measure v (f x)) = measure v (BIGUNION (IMAGE f univ(:num)))`
               by METIS_TAC [o_DEF,countably_additive_def]
	  ++ `suminf (\x. measure v (f x)) <> PosInf` by METIS_TAC []
          ++ `suminf (\x. measure v (f x) - pos_fn_integral m (\x'. g x' * indicator_fn (f x) x')) = 
              suminf (\x. measure v (f x)) - suminf (\x. pos_fn_integral m (\x'. g x' * indicator_fn (f x) x'))`
                by  (`(\x. measure v (f x) - pos_fn_integral m (\x'. g x' * indicator_fn (f x) x')) = 
                      (\x. (\x. measure v (f x)) x - (\x. pos_fn_integral m (\x'. g x' * indicator_fn (f x) x')) x)`
                         by METIS_TAC []
                     ++ POP_ORW
	             ++ MATCH_MP_TAC ext_suminf_sub
		     ++ RW_TAC std_ss []
		     >> (MATCH_MP_TAC pos_fn_integral_pos
                         ++ RW_TAC std_ss [indicator_fn_def,mul_rzero,mul_rone,le_refl]
			 ++ METIS_TAC [measure_space_def,countably_additive_def])
		     ++ METIS_TAC [IN_FUNSET,IN_UNIV])
          ++ POP_ORW
	  ++ Suff `pos_fn_integral m (\x. g x * indicator_fn (BIGUNION (IMAGE f univ(:num))) x) = 
                   suminf (\x. pos_fn_integral m (\x'. g x' * indicator_fn (f x) x'))`
          >> RW_TAC std_ss []
	  ++ `measure_space m` by METIS_TAC [measure_space_def,countably_additive_def]
	  ++ `(!i x. 0 <= (\i x. g x * indicator_fn (f i) x) i x)` by RW_TAC std_ss [mul_rzero,mul_rone,indicator_fn_def,le_refl]
	  ++ `(!i. (\i x. g x * indicator_fn (f i) x) i IN measurable (m_space m,measurable_sets m) Borel)`
               by (RW_TAC std_ss []
		   ++ METIS_TAC [IN_MEASURABLE_BOREL_MUL_INDICATOR,IN_FUNSET,IN_UNIV,measurable_sets_def,subsets_def])
	  ++ (MP_TAC o Q.SPECL [`m`,`(\i:num. (\x. g x * indicator_fn (f i) x))`]) pos_fn_integral_suminf
	  ++ RW_TAC std_ss []
	  ++ POP_ASSUM (MP_TAC o GSYM)
	  ++ RW_TAC std_ss []
	  ++ Suff `(\x. g x * indicator_fn (BIGUNION (IMAGE f univ(:num))) x) = 
                   (\x'. suminf (\x. g x' * indicator_fn (f x) x'))`
          >> RW_TAC std_ss []
	  ++ RW_TAC std_ss [FUN_EQ_THM]
	  ++ `suminf (\x. g x' * (\x. indicator_fn (f x) x') x) = g x' * suminf (\x. indicator_fn (f x) x')`
              by (MATCH_MP_TAC ext_suminf_cmul
                  ++ RW_TAC std_ss [mul_rone,mul_rzero,le_refl,indicator_fn_def,le_01])
          ++ FULL_SIMP_TAC std_ss []
	  ++ Suff `suminf (\i. indicator_fn (f i) x') = indicator_fn (BIGUNION (IMAGE f univ(:num))) x'`
          >> RW_TAC std_ss []
	  ++ FULL_SIMP_TAC std_ss [indicator_fn_suminf])
  ++ `!A. A IN measurable_sets m ==> nu A <= nu (m_space m)` by METIS_TAC [MEASURE_SPACE_INCREASING,INCREASING,MEASURE_SPACE_SUBSET_MSPACE,measure_def,measurable_sets_def,m_space_def,MEASURE_SPACE_MSPACE_MEASURABLE]
  ++ Cases_on `nu A = 0` >> METIS_TAC [sub_0]
  ++ `0 < nu A` by METIS_TAC [lt_le,MEASURE_SPACE_POSITIVE,positive_def]
  ++ `0 < nu (m_space m)` by METIS_TAC [lte_trans]
  ++ `0 <> measure m (m_space m)` 
       by (SPOSE_NOT_THEN ASSUME_TAC
           ++ `measure v (m_space m) = 0` by METIS_TAC [MEASURE_SPACE_MSPACE_MEASURABLE,measure_absolutely_continuous_def]
           ++ `pos_fn_integral m (\x. g x * indicator_fn (m_space m) x) <= 0` by METIS_TAC [MEASURE_SPACE_MSPACE_MEASURABLE]
           ++ `pos_fn_integral m (\x. g x * indicator_fn (m_space m) x) =  0` by METIS_TAC [le_antisym,MEASURE_SPACE_MSPACE_MEASURABLE]
           ++ `nu (m_space m) = 0` by (Q.UNABBREV_TAC `nu` ++ METIS_TAC [sub_rzero])
           ++ METIS_TAC [lt_imp_ne])
  ++ `0 < measure m (m_space m)` by METIS_TAC [lt_le,MEASURE_SPACE_POSITIVE,positive_def,MEASURE_SPACE_MSPACE_MEASURABLE]
  ++ Q.ABBREV_TAC `z = nu (m_space m) / (2 * measure m (m_space m)) `
  ++ `nu (m_space m) <> NegInf` by METIS_TAC [lt_trans,lt_infty,num_not_infty]
  ++ `measure m (m_space m) <> NegInf` by METIS_TAC [lt_trans,lt_infty,num_not_infty]
  ++ `nu (m_space m) <> PosInf` 
       by (Q.UNABBREV_TAC `nu` 
           ++ RW_TAC std_ss []
	   ++ METIS_TAC [sub_not_infty,MEASURE_SPACE_MSPACE_MEASURABLE])
  ++ `?e. 0 < e /\ (z = Normal e)`
       by (Q.UNABBREV_TAC `z`
	   ++ `?r1. nu (m_space m) = Normal r1` by METIS_TAC [extreal_cases]
	   ++ `?r2. measure m (m_space m) = Normal r2` by METIS_TAC [extreal_cases]
	   ++ RW_TAC std_ss [extreal_mul_def,extreal_of_num_def]
	   ++ `0 < r1` by METIS_TAC [extreal_of_num_def,extreal_lt_eq]
	   ++ `0 < r2` by METIS_TAC [extreal_of_num_def,extreal_lt_eq]
           ++ `0 < 2 * r2` by RW_TAC real_ss [REAL_LT_MUL]
           ++ FULL_SIMP_TAC std_ss [extreal_div_eq,REAL_LT_IMP_NE]
	   ++ `0 < r1 / (2 * r2)` by RW_TAC std_ss [REAL_LT_DIV]
	   ++ METIS_TAC [])
  ++ Q.ABBREV_TAC `snu = (\A. nu A - Normal e * (measure m A))`
  ++ `?A'. A' IN measurable_sets m /\ snu(m_space m) <= snu (A') /\ 
       (!B. B IN measurable_sets m /\ B SUBSET A' ==> 0 <= snu (B))`
        by (Q.UNABBREV_TAC `snu`
            ++ RW_TAC std_ss []
	    ++ (MP_TAC o Q.SPECL [`(m_space m, measurable_sets m, nu)`,`(m_space m, measurable_sets m, (\A. Normal e * measure m A))`]) RN_lemma2 
	    ++ RW_TAC std_ss [m_space_def,measurable_sets_def,measure_def]
	    ++ METIS_TAC [MEASURE_SPACE_CMUL,REAL_LT_IMP_LE,mul_not_infty,extreal_not_infty])
  ++ Q.ABBREV_TAC `g' = (\x. g x + Normal e * indicator_fn (A') x)`
  ++ `!A. A IN measurable_sets m ==> 
          (pos_fn_integral m (\x. g' x * indicator_fn A x) = 
           pos_fn_integral m (\x. g x * indicator_fn A x) + Normal e * measure m (A INTER A'))`
       by (REPEAT STRIP_TAC
           ++ `measure m (A'' INTER A') = pos_fn_integral m (indicator_fn (A'' INTER A'))`
                by METIS_TAC [pos_fn_integral_indicator,MEASURE_SPACE_INTER]
           ++ POP_ORW
	   ++ `Normal e * pos_fn_integral m (indicator_fn (A'' INTER A')) = 
               pos_fn_integral m (\x. Normal e * indicator_fn (A'' INTER A') x)`
                by ((MATCH_MP_TAC o GSYM) pos_fn_integral_cmul
                    ++ RW_TAC real_ss [REAL_LT_IMP_LE,indicator_fn_def,le_01,le_refl])
           ++ POP_ORW
	   ++ Q.UNABBREV_TAC `g'`
	   ++ `(\x. (\x. g x + Normal e * indicator_fn A' x) x * indicator_fn A'' x) =
               (\x. (\x. g x * indicator_fn A'' x) x + (\x. Normal e * indicator_fn (A'' INTER A') x) x)`
                by (RW_TAC std_ss [FUN_EQ_THM,indicator_fn_def,IN_INTER]
                    ++ METIS_TAC [mul_rone,mul_rzero,add_rzero,indicator_fn_def,IN_INTER])
           ++ POP_ORW
	   ++ MATCH_MP_TAC pos_fn_integral_add
	   ++ FULL_SIMP_TAC std_ss []
	   ++ CONJ_TAC >> (RW_TAC std_ss [indicator_fn_def,le_01,le_refl,mul_rone,mul_rzero] 
                           ++ FULL_SIMP_TAC std_ss [extreal_of_num_def,extreal_le_def,REAL_LT_IMP_LE])
           ++ RW_TAC std_ss []
	   >> METIS_TAC [IN_MEASURABLE_BOREL_MUL_INDICATOR,measure_space_def,measurable_sets_def,subsets_def]
	   ++ MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL
	   ++ RW_TAC std_ss []
	   ++ Q.EXISTS_TAC `indicator_fn (A'' INTER A')`
	   ++ Q.EXISTS_TAC `e`
	   ++ RW_TAC std_ss []
	   >> FULL_SIMP_TAC std_ss [measure_space_def]
	   ++ MATCH_MP_TAC IN_MEASURABLE_BOREL_INDICATOR
	   ++ METIS_TAC [measure_space_def,measurable_sets_def,subsets_def,MEASURE_SPACE_INTER,space_def])
  ++ `!A. A IN measurable_sets m ==> ((A INTER A') IN measurable_sets m /\ (A INTER A') SUBSET A')`
         by METIS_TAC [INTER_SUBSET,MEASURE_SPACE_INTER]
  ++ `!A. A IN measurable_sets m ==> 0 <= nu (A INTER A') - Normal e * measure m (A INTER A')`
         by (Q.UNABBREV_TAC `snu` ++ METIS_TAC [])
  ++ `!A. A IN measurable_sets m ==> Normal e * measure m (A INTER A') <= nu (A INTER A')`
         by (RW_TAC std_ss []
             ++ `Normal e * measure m (A'' INTER A') <> PosInf`
                  by FULL_SIMP_TAC std_ss [mul_not_infty,REAL_LT_IMP_LE,MEASURE_SPACE_INTER]
             ++ `Normal e * measure m (A'' INTER A') <> NegInf`
                  by METIS_TAC [mul_not_infty,REAL_LT_IMP_LE,MEASURE_SPACE_INTER,MEASURE_SPACE_POSITIVE,positive_not_infty]
             ++ METIS_TAC [sub_zero_le])
  ++ `!A. A IN measurable_sets m ==> 
          pos_fn_integral m (\x. g x * indicator_fn A x) + Normal e * measure m (A INTER A') <=
          pos_fn_integral m (\x. g x * indicator_fn A x) + nu (A INTER A')`
         by METIS_TAC [le_ladd_imp]
  ++ `!A. A IN measurable_sets m ==> nu (A INTER A') <= nu A`
         by (RW_TAC std_ss [] 
             ++ (MATCH_MP_TAC o REWRITE_RULE [measurable_sets_def,measure_def] o Q.SPEC `(m_space m,measurable_sets m,nu)`) INCREASING
	     ++ METIS_TAC [MEASURE_SPACE_INCREASING,MEASURE_SPACE_INTER,INTER_SUBSET])
  ++ `!A. A IN measurable_sets m ==> 
          pos_fn_integral m (\x. g x * indicator_fn A x) + Normal e * measure m (A INTER A') <=
          pos_fn_integral m (\x. g x * indicator_fn A x) + nu (A)`
           by METIS_TAC [le_ladd_imp,le_trans]
  ++ `!A. A IN measurable_sets m ==> 
          pos_fn_integral m (\x. g x * indicator_fn A x) + Normal e * measure m (A INTER A') <= measure v A`
           by (Q.UNABBREV_TAC `nu`
               ++ FULL_SIMP_TAC std_ss []
               ++ RW_TAC std_ss []
               ++ METIS_TAC [sub_add2])
  ++ `!A. A IN measurable_sets m ==> pos_fn_integral m (\x. g' x * indicator_fn A x) <= measure v A`
        by METIS_TAC []
  ++ `g' IN RADON_F m v` 
         by (RW_TAC std_ss [RADON_F_def,GSPECIFICATION]
             >> (Q.UNABBREV_TAC `g'`
                 ++ MATCH_MP_TAC IN_MEASURABLE_BOREL_ADD
                 ++ Q.EXISTS_TAC `g`
		 ++ Q.EXISTS_TAC `(\x. Normal e * indicator_fn A' x)`
		 ++ CONJ_TAC >> FULL_SIMP_TAC std_ss [measure_space_def]
		 ++ FULL_SIMP_TAC std_ss []
		 ++ CONJ_TAC 
		 >> (MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL
		     ++ METIS_TAC [measure_space_def,subsets_def,measurable_sets_def,IN_MEASURABLE_BOREL_INDICATOR])
		 ++ RW_TAC std_ss [indicator_fn_def,mul_rone,mul_rzero,num_not_infty,space_def]
		 ++ METIS_TAC [lt_infty,lte_trans,num_not_infty])
	     ++ Q.UNABBREV_TAC `g'`
	     ++ RW_TAC std_ss [indicator_fn_def,mul_rone,mul_rzero,add_rzero]
	     ++ METIS_TAC [le_add2,add_rzero,le_trans,lt_imp_le,extreal_lt_eq,extreal_of_num_def])
  ++ `pos_fn_integral m g' IN RADON_F_integrals m v` 
       by (FULL_SIMP_TAC std_ss [RADON_F_integrals_def,GSPECIFICATION]
           ++ METIS_TAC [])
  ++ `pos_fn_integral m (\x. g' x * indicator_fn (m_space m) x) =
      pos_fn_integral m (\x. g x * indicator_fn (m_space m) x) +
      Normal e * measure m A'`
         by METIS_TAC [MEASURE_SPACE_MSPACE_MEASURABLE,MEASURE_SPACE_SUBSET_MSPACE,SUBSET_INTER2]
  ++ `!x. 0 <= g' x`
      by (Q.UNABBREV_TAC `g'`
          ++ RW_TAC std_ss [indicator_fn_def,mul_rone,mul_rzero,add_rzero]
	  ++ METIS_TAC [le_add2,add_rzero,le_trans,lt_imp_le,extreal_lt_eq,extreal_of_num_def])
  ++ `pos_fn_integral m g' = pos_fn_integral m g + Normal e * measure m A'`
       by METIS_TAC [pos_fn_integral_mspace]
  ++ `0 < snu (m_space m)` 
       by (Q.UNABBREV_TAC `snu`
           ++ RW_TAC std_ss []
           ++ `?r1. nu (m_space m) = Normal r1` by METIS_TAC [extreal_cases]
 	   ++ `?r2. measure m (m_space m) = Normal r2` by METIS_TAC [extreal_cases]
	   ++ `0 < r1` by METIS_TAC [extreal_of_num_def,extreal_lt_eq]
	   ++ `0 < r2` by METIS_TAC [extreal_of_num_def,extreal_lt_eq]
           ++ `0 < 2 * r2` by RW_TAC real_ss [REAL_LT_MUL]
           ++ `Normal e = nu (m_space m) / (2 * measure m (m_space m))` by RW_TAC std_ss []
           ++ POP_ORW
	   ++ REWRITE_TAC [extreal_of_num_def]
           ++ FULL_SIMP_TAC std_ss [extreal_mul_def,extreal_div_eq,REAL_LT_IMP_NE,extreal_sub_def,extreal_lt_eq]
	   ++ RW_TAC real_ss [real_div,REAL_INV_MUL,REAL_LT_IMP_NE,REAL_MUL_ASSOC]
	   ++ `inv 2 * inv r2 * r2 = inv 2` by METIS_TAC [REAL_LT_IMP_NE,REAL_MUL_LINV,REAL_MUL_ASSOC,REAL_MUL_RID]
           ++ `r1 - r1 * inv 2 * inv r2 * r2 = r1 / 2` by METIS_TAC [REAL_NEG_HALF,real_div,REAL_MUL_ASSOC]
           ++ FULL_SIMP_TAC real_ss [REAL_LT_DIV])
  ++ `0 < snu A'` by METIS_TAC [lte_trans]
  ++ `Normal e * measure m A' <> PosInf` by METIS_TAC [REAL_LT_IMP_LE,mul_not_infty]
  ++ `Normal e * measure m A' <> NegInf` by METIS_TAC [REAL_LT_IMP_LE,mul_not_infty,MEASURE_SPACE_POSITIVE,positive_not_infty]
  ++ `Normal e * measure m A' < nu (A')` by METIS_TAC [sub_zero_lt2]
  ++ `0 <= Normal e * measure m A'` by METIS_TAC [le_mul,REAL_LT_IMP_LE,extreal_le_def,MEASURE_SPACE_POSITIVE,positive_def,extreal_of_num_def]   
  ++ `0 < nu A'` by METIS_TAC [let_trans]
  ++ `0 <> measure m A'` 
        by (SPOSE_NOT_THEN ASSUME_TAC
            ++ `measure v A' = 0` by METIS_TAC [MEASURE_SPACE_MSPACE_MEASURABLE,measure_absolutely_continuous_def]
            ++ `pos_fn_integral m (\x. g x * indicator_fn A' x) <= 0` by METIS_TAC []
            ++ `pos_fn_integral m (\x. g x * indicator_fn A' x) =  0` by METIS_TAC [le_antisym]
            ++ `nu A' = 0` by (Q.UNABBREV_TAC `nu` ++ METIS_TAC [sub_rzero])
            ++ METIS_TAC [lt_imp_ne])
  ++ `0 < measure m A'` by METIS_TAC [lt_le,MEASURE_SPACE_POSITIVE,positive_def,MEASURE_SPACE_MSPACE_MEASURABLE]
  ++ `0 < Normal e * measure m A'` by METIS_TAC [lt_mul,extreal_lt_eq,extreal_of_num_def]
  ++ `pos_fn_integral m g <> NegInf` by METIS_TAC [pos_fn_integral_pos,lt_infty,num_not_infty,lte_trans]
  ++ `pos_fn_integral m g <> PosInf` by METIS_TAC [MEASURE_SPACE_MSPACE_MEASURABLE,pos_fn_integral_mspace]
  ++ `pos_fn_integral m g < pos_fn_integral m g'` by METIS_TAC [let_add2,le_refl,num_not_infty,add_rzero]
  ++ `pos_fn_integral m g' <= pos_fn_integral m g` by METIS_TAC [le_sup_imp,SPECIFICATION]
  ++ METIS_TAC [extreal_lt_def]);

val _ = export_theory ();
