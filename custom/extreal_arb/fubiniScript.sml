(* ------------------------------------------------------------------------- *)
(* Fubini's Theorem under the old extreal definitions                        *)
(*                                                                           *)
(* Author: Chun Tian (2020)                                                  *)
(* Fondazione Bruno Kessler and University of Trento, Italy                  *)
(* ------------------------------------------------------------------------- *)

open HolKernel Parse boolLib bossLib;

open pairTheory relationTheory prim_recTheory arithmeticTheory
     pred_setTheory combinTheory realTheory realLib seqTheory;

open hurdUtils util_probTheory extrealTheory sigma_algebraTheory
     measureTheory borelTheory lebesgueTheory martingaleTheory;

val _ = new_theory "fubini";

(* To build this theory, the following version of definitions must be present in
   your extrealTheory:

val extreal_add_def = Define
  `(extreal_add (Normal x) (Normal y) = Normal (x + y)) /\
   (extreal_add PosInf a = PosInf) /\
   (extreal_add a PosInf = PosInf) /\
   (extreal_add NegInf b = NegInf) /\
   (extreal_add c NegInf = NegInf)`;

val extreal_sub_def = Define
  `(extreal_sub (Normal x) (Normal y) = Normal (x - y)) /\
   (extreal_sub PosInf a = PosInf) /\
   (extreal_sub b PosInf = NegInf) /\
   (extreal_sub NegInf NegInf = PosInf) /\
   (extreal_sub NegInf c = NegInf) /\
   (extreal_sub c NegInf = PosInf)`;
 *)

(* removed antecedents:
     (x <> NegInf /\ y <> NegInf) \/ (x <> PosInf /\ y <> PosInf)
 *)
Theorem add_comm__new :
    !x y. x + y = y + x
Proof
    Cases >> Cases_on `y`
 >> RW_TAC std_ss [extreal_add_def, REAL_ADD_COMM]
QED

(* removed antecedents:
     (x <> NegInf /\ y <> PosInf) \/ (x <> PosInf /\ y <> NegInf)
 *)
Theorem extreal_sub_add__new :
    !x y. x - y = x + -y
Proof
    rpt Cases
 >> RW_TAC std_ss [extreal_ainv_def, extreal_sub_def, extreal_add_def, real_sub]
QED

(* FAILED: removed antecedents: x <> NegInf /\ y <> NegInf
Theorem lt_sub_imp__new :
    !x y z. y + x < z ==> y < z - x
Proof
    rpt Cases
 >> RW_TAC std_ss [extreal_lt_def, extreal_le_def, extreal_add_def, extreal_sub_def]
 >> METIS_TAC [real_lt, REAL_LT_ADD_SUB]
QED
 *)

(* FAILED: removed antecedents: x <> NegInf /\ y <> NegInf
Theorem lt_sub__new :
    !x y z. z <> NegInf /\ z <> PosInf ==> (y + x < z <=> y < z - x)
Proof
    rpt Cases
 >> RW_TAC std_ss [extreal_lt_def, extreal_le_def, extreal_add_def,
                   extreal_sub_def, le_infty]
 >> METIS_TAC [REAL_LE_SUB_RADD]
QED

(* removed antecedents:

     (!x. x IN space a ==> (f x <> NegInf /\ g x <> NegInf) \/
                           (f x <> PosInf /\ g x <> PosInf))

   used custom theorems:

   1. lt_sub_imp__new
   2. lt_sub_custom
   3. add_comm__new
 *)
Theorem IN_MEASURABLE_BOREL_ADD__new :
    !a f g h. sigma_algebra a /\ f IN measurable a Borel /\ g IN measurable a Borel /\
              (!x. x IN space a ==> (h x = f x + g x))
          ==> h IN measurable a Borel
Proof
    rpt STRIP_TAC
 >> RW_TAC std_ss [IN_MEASURABLE_BOREL] >- RW_TAC std_ss [IN_FUNSET, IN_UNIV]
 >> Know `!c. {x | h x < Normal c} INTER (space a) =
              BIGUNION (IMAGE (\r. {x | f x < r /\ r < Normal c - g x} INTER space a) Q_set)`
 >- (RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_BIGUNION_IMAGE, IN_UNIV, IN_INTER] \\
     EQ_TAC >- (RW_TAC std_ss [] \\
                MATCH_MP_TAC Q_DENSE_IN_R \\
                METIS_TAC [lt_sub_imp__new]) \\
     reverse (RW_TAC std_ss []) >- art [] \\
    ‘h x = f x + g x’ by PROVE_TAC [] >> POP_ORW \\
    ‘f x < Normal c - g x’ by PROVE_TAC [lt_trans] \\
     METIS_TAC [lt_sub__new, extreal_not_infty])
 >> DISCH_TAC
 >> FULL_SIMP_TAC std_ss []
 >> MATCH_MP_TAC BIGUNION_IMAGE_Q
 >> RW_TAC std_ss [IN_FUNSET]
 >> `?y. r = Normal y` by METIS_TAC [Q_not_infty, extreal_cases]
 >> `{x | f x < Normal y /\ Normal y < Normal c - g x} =
     {x | f x < Normal y} INTER {x | Normal y < Normal c - g x}`
     by RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER]
 >> `({x | f x < Normal y} INTER space a) IN subsets a` by RW_TAC std_ss [IN_MEASURABLE_BOREL_ALL]
 >> Know `!x. x IN space a ==> (Normal y < Normal c - g x <=> g x < Normal c - Normal y)`
 >- (rpt STRIP_TAC \\
     METIS_TAC [lt_sub__new, extreal_not_infty, add_comm__new])
 >> DISCH_TAC
 >> `{x | Normal y < Normal c - g x} INTER space a = {x | g x < Normal c - Normal y} INTER space a`
     by (RW_TAC std_ss [IN_INTER, EXTENSION, GSPECIFICATION] >> METIS_TAC [])
 >> `({x | Normal y < Normal c - g x} INTER space a) IN subsets a`
     by METIS_TAC [IN_MEASURABLE_BOREL_ALL, extreal_sub_def]
 >> `({x | f x < Normal y} INTER space a) INTER ({x | Normal y < Normal c - g x} INTER space a) =
     ({x | f x < Normal y} INTER {x | Normal y < Normal c - g x} INTER space a)`
     by (RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER] \\
         EQ_TAC >> RW_TAC std_ss [])
 >> METIS_TAC [sigma_algebra_def, ALGEBRA_INTER]
QED

(* removed antecedents:

     (!x. x IN space a ==> (f x <> NegInf /\ g x <> PosInf) \/
                           (f x <> PosInf /\ g x <> NegInf))

   used custom theorems:

   1. IN_MEASURABLE_BOREL_ADD__new
   2. extreal_sub_add__new
 *)
Theorem IN_MEASURABLE_BOREL_SUB__new :
    !a f g h. sigma_algebra a /\ f IN measurable a Borel /\ g IN measurable a Borel /\
             (!x. x IN space a ==> (h x = f x - g x))
          ==> h IN measurable a Borel
Proof
    RW_TAC std_ss []
 >> MATCH_MP_TAC IN_MEASURABLE_BOREL_ADD__new
 >> qexistsl_tac [`f`, `\x. - g x`]
 >> RW_TAC std_ss []
 >| [ (* goal 1 (of 3) *)
      MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL \\
      Q.EXISTS_TAC `g` \\
      Q.EXISTS_TAC `-1` \\
      RW_TAC std_ss [GSYM extreal_ainv_def, GSYM extreal_of_num_def, GSYM neg_minus1],
      (* goal 3 (of 3) *)
      REWRITE_TAC [extreal_sub_add__new] ]
QED

(* removed antecedents:

     (!x. x IN m_space m ==> f1 x <> PosInf \/ f2 x <> PosInf)

   used custom theorems:

   - none (except for extreal_add_def and extreal_sub_def)
 *)
Theorem integral_add_lemma__new :
    !m f f1 f2.
       measure_space m /\ integrable m f /\
       integrable m f1 /\ integrable m f2 /\
      (!x. x IN m_space m ==> (f x = f1 x - f2 x)) /\
      (!x. x IN m_space m ==> 0 <= f1 x) /\
      (!x. x IN m_space m ==> 0 <= f2 x) ==>
      (integral m f = pos_fn_integral m f1 - pos_fn_integral m f2)
Proof
    rpt STRIP_TAC
 >> REWRITE_TAC [integral_def]
 >> `!x. x IN m_space m ==> f1 x <> NegInf` by METIS_TAC [pos_not_neginf]
 >> `!x. x IN m_space m ==> f2 x <> NegInf` by METIS_TAC [pos_not_neginf]
 >> Q.ABBREV_TAC `h1 = (\x. fn_plus f x + f2 x)`
 >> Q.ABBREV_TAC `h2 = (\x. fn_minus f x + f1 x)`
 >> Know `!x. x IN m_space m ==> (h1 x = h2 x)`
 >- (RW_TAC std_ss [Abbr ‘h1’, Abbr ‘h2’] \\
    ‘f1 x <> NegInf /\ f2 x <> NegInf’ by PROVE_TAC [] \\
     SIMP_TAC std_ss [fn_plus_def, fn_minus_def, add_lzero] \\
     Cases_on `f1 x` >> Cases_on `f2 x` \\
     FULL_SIMP_TAC std_ss [extreal_sub_def, extreal_add_def, extreal_ainv_def,
                           extreal_11, add_lzero, extreal_of_num_def, GSYM lt_infty,
                           extreal_lt_eq, extreal_not_infty] \\
     Cases_on ‘0 < r - r'’
     >- (‘~(r - r' < 0)’ by METIS_TAC [REAL_LT_ANTISYM] \\
         fs [extreal_add_def, extreal_sub_def, add_lzero] >> REAL_ARITH_TAC) \\
     Cases_on ‘r - r' < 0’
     >- (fs [extreal_add_def, extreal_sub_def, add_lzero] >> REAL_ARITH_TAC) \\
     fs [extreal_add_def, extreal_11] \\
    ‘r - r' = 0’ by METIS_TAC [REAL_LE_ANTISYM, real_lt] >> POP_ASSUM MP_TAC \\
     REAL_ARITH_TAC)
 >> DISCH_TAC
 >> Know `pos_fn_integral m h1 = pos_fn_integral m h2`
 >- (MATCH_MP_TAC pos_fn_integral_cong >> simp [] \\
     RW_TAC std_ss [Abbr ‘h2’] \\
     MATCH_MP_TAC le_add >> rw [FN_MINUS_POS]) >> DISCH_TAC
 >> `pos_fn_integral m h1 =
     pos_fn_integral m (fn_plus f) + pos_fn_integral m f2`
      by (Q.UNABBREV_TAC `h1`
          >> MATCH_MP_TAC pos_fn_integral_add
          >> FULL_SIMP_TAC std_ss [integrable_def]
          >> RW_TAC std_ss [le_refl, lt_le, IN_MEASURABLE_BOREL_FN_PLUS, FN_PLUS_POS])
 >> `pos_fn_integral m h2 =
     pos_fn_integral m (fn_minus f) + pos_fn_integral m f1`
      by (Q.UNABBREV_TAC `h2`
          >> MATCH_MP_TAC pos_fn_integral_add
          >> METIS_TAC [FN_MINUS_POS, IN_MEASURABLE_BOREL_FN_MINUS, integrable_def])
 >> `pos_fn_integral m f2 <> PosInf` by METIS_TAC [integrable_pos]
 >> `pos_fn_integral m (fn_minus f) <> PosInf`
      by METIS_TAC [integrable_def]
 >> `pos_fn_integral m f2 <> NegInf`
      by METIS_TAC [pos_fn_integral_pos, lt_infty, lte_trans, num_not_infty]
 >> `0 <= pos_fn_integral m (fn_minus f)`
      by METIS_TAC [pos_fn_integral_pos, FN_MINUS_POS]
 >> `pos_fn_integral m (fn_minus f) <> NegInf`
      by METIS_TAC [lt_infty, lte_trans, num_not_infty]
 >> METIS_TAC [eq_add_sub_switch]
QED

(* removed antecedents:

     (!y. y IN Y ==> pos_fn_integral (X,A,u) (\x. (abs o f) (x,y)) <> PosInf) /\
     (!x. x IN X ==> pos_fn_integral (Y,B,v) (\y. (abs o f) (x,y)) <> PosInf)

   used custom theorems:

   1. IN_MEASURABLE_BOREL_SUB__new
   2. integral_add_lemma__new
 *)

val _ = export_theory ();
val _ = html_theory "fubini";
