(* ------------------------------------------------------------------------- *)
(* Fubini's Theorem under special extreal definitions                        *)
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

Definition extreal_add_def :
   (extreal_add (Normal x) (Normal y) = Normal (x + y)) /\
   (extreal_add (Normal _) a = a) /\
   (extreal_add b (Normal _) = b) /\
   (extreal_add NegInf NegInf = NegInf) /\
   (extreal_add PosInf PosInf = PosInf) /\
   (extreal_add PosInf NegInf = Normal 0) /\
   (extreal_add NegInf PosInf = Normal 0)
End

Definition extreal_sub_def :
   (extreal_sub (Normal x) (Normal y) = Normal (x - y)) /\
   (extreal_sub a (Normal _) = a) /\
   (extreal_sub (Normal _) NegInf = PosInf) /\
   (extreal_sub (Normal _) PosInf = NegInf) /\
   (extreal_sub NegInf PosInf = NegInf) /\
   (extreal_sub PosInf NegInf = PosInf) /\
   (extreal_sub PosInf PosInf = Normal 0) /\
   (extreal_sub NegInf NegInf = Normal 0)
End
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

(* removed antecedents:

     (!x. x IN space a ==> (f x <> NegInf /\ g x <> NegInf) \/
                           (f x <> PosInf /\ g x <> PosInf))

   used custom theorems:

   - none (except for the very definitions)
 *)
Theorem IN_MEASURABLE_BOREL_ADD__new :
    !a f g h. sigma_algebra a /\ f IN measurable a Borel /\ g IN measurable a Borel /\
              (!x. x IN space a ==> (h x = f x + g x))
          ==> h IN measurable a Borel
Proof
    rpt STRIP_TAC
 >> RW_TAC std_ss [IN_MEASURABLE_BOREL, IN_FUNSET, IN_UNIV]
 >> Know `!c. {x | h x < Normal c} INTER (space a) =
              {x | f x + g x < Normal c} INTER (space a)`
 >- (rw [Once EXTENSION] >> METIS_TAC []) >> Rewr'
 >> Know `!c. {x | f x + g x < Normal c} INTER (space a) =
                ({x | f x + g x < Normal c /\ g x <> PosInf /\ g x <> NegInf} INTER (space a)) UNION
                (({x | f x + g x < Normal c /\ g x = PosInf} INTER (space a)) UNION
                 ({x | f x + g x < Normal c /\ g x = NegInf} INTER (space a)))`
 >- (rw [Once EXTENSION] \\
     Cases_on ‘g x = PosInf’ >- rw [] \\
     Cases_on ‘g x = NegInf’ >- rw [] \\
     rw []) >> Rewr'
 >> MATCH_MP_TAC SIGMA_ALGEBRA_UNION >> rw []
 >- (Know `!c. {x | f x + g x < Normal c /\ g x <> PosInf /\ g x <> NegInf} INTER (space a) =
               BIGUNION (IMAGE (\r. {x | f x < r /\ r < Normal c - g x /\
                                         g x <> PosInf /\ g x <> NegInf} INTER space a) Q_set)`
     >- (RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_BIGUNION_IMAGE, IN_UNIV, IN_INTER] \\
         EQ_TAC >- (RW_TAC std_ss [] \\
                    MATCH_MP_TAC Q_DENSE_IN_R \\
                    METIS_TAC [lt_sub_imp2]) \\
         reverse (RW_TAC std_ss []) >- art [] >- art [] >- art [] \\
        ‘f x < Normal c - g x’ by PROVE_TAC [lt_trans] \\
         Cases_on ‘f x = PosInf’
         >- (‘?e. g x = Normal e’ by METIS_TAC [extreal_cases] \\
             fs [lt_infty]) \\
         METIS_TAC [lt_sub', extreal_not_infty]) >> Rewr' \\
     MATCH_MP_TAC BIGUNION_IMAGE_Q \\
     RW_TAC std_ss [IN_FUNSET] \\
    `?y. r = Normal y` by METIS_TAC [Q_not_infty, extreal_cases] >> POP_ORW \\
    `{x | f x < Normal y /\ Normal y < Normal c - g x /\ g x <> PosInf /\ g x <> NegInf} =
     {x | f x < Normal y} INTER {x | Normal y < Normal c - g x /\ g x <> PosInf /\ g x <> NegInf}`
       by RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER] >> POP_ORW \\
    ‘{x | f x < Normal y} INTER
     {x | Normal y < Normal c - g x /\ g x <> PosInf /\ g x <> NegInf} INTER space a =
       ({x | f x < Normal y} INTER space a) INTER
       ({x | Normal y < Normal c - g x /\ g x <> PosInf /\ g x <> NegInf} INTER space a)’
       by SET_TAC [] >> POP_ORW \\
     MATCH_MP_TAC SIGMA_ALGEBRA_INTER >> art [] \\
     CONJ_TAC >- METIS_TAC [IN_MEASURABLE_BOREL_ALL] \\
     Know `{x | Normal y < Normal c - g x /\ g x <> PosInf /\ g x <> NegInf} INTER space a =
           {x | g x < Normal c - Normal y /\ g x <> PosInf /\ g x <> NegInf} INTER space a`
     >- (rw [Once EXTENSION] \\
         EQ_TAC >> rw [] >| (* 2 subgoals *)
         [ (* goal 1 (of 2) *)
          ‘?e. g x = Normal e’ by METIS_TAC [extreal_cases] \\
           fs [extreal_sub_def, extreal_lt_eq] \\
           Q.PAT_X_ASSUM ‘y < c − e’ MP_TAC >> REAL_ARITH_TAC,
           (* goal 2 (of 2) *)
           ‘?e. g x = Normal e’ by METIS_TAC [extreal_cases] \\
           fs [extreal_sub_def, extreal_lt_eq] \\
           Q.PAT_X_ASSUM ‘e < c − y’ MP_TAC >> REAL_ARITH_TAC ]) >> Rewr' \\
    ‘{x | g x < Normal c - Normal y /\ g x <> PosInf /\ g x <> NegInf} INTER space a =
       ({x | g x < Normal c - Normal y} INTER space a) INTER
       (({x | g x <> PosInf} INTER space a) INTER
        ({x | g x <> NegInf} INTER space a))’ by SET_TAC [] >> POP_ORW \\
     MATCH_MP_TAC SIGMA_ALGEBRA_INTER >> art [extreal_sub_def] \\
     CONJ_TAC >- METIS_TAC [IN_MEASURABLE_BOREL_ALL] \\
     MATCH_MP_TAC SIGMA_ALGEBRA_INTER >> art [] \\
     METIS_TAC [IN_MEASURABLE_BOREL_ALL])
 >> MATCH_MP_TAC SIGMA_ALGEBRA_UNION >> rw [] (* 2 subgoals *)
 >| [ (* goal 1 (of 2) *)
      Know ‘{x | f x + g x < Normal c /\ g x = PosInf} INTER space a =
            ({x | f x + g x < Normal c /\ g x = PosInf /\ f x = PosInf} INTER space a) UNION
            ({x | f x + g x < Normal c /\ g x = PosInf /\ f x = NegInf} INTER space a) UNION
            ({x | f x + g x < Normal c /\ g x = PosInf /\ f x <> PosInf /\ f x <> NegInf} INTER space a)’
      >- (rw [Once EXTENSION] \\
          EQ_TAC >> rw [] >> art [] \\
          METIS_TAC []) >> Rewr' \\
      Know ‘{x | f x + g x < Normal c /\ g x = PosInf /\ f x = PosInf} = EMPTY’
      >- (rw [Once EXTENSION, NOT_IN_EMPTY] \\
          STRONG_DISJ_TAC >> CCONTR_TAC >> fs [extreal_add_def, lt_infty]) >> Rewr' \\
      Know ‘{x | f x + g x < Normal c /\ g x = PosInf /\ f x <> PosInf /\ f x <> NegInf} = EMPTY’
      >- (rw [Once EXTENSION, NOT_IN_EMPTY] \\
          NTAC 2 STRONG_DISJ_TAC \\
          CCONTR_TAC >> fs [] >> ‘?e. f x = Normal e’ by METIS_TAC [extreal_cases] \\
          fs [extreal_add_def, lt_infty]) >> Rewr' \\
      simp [] \\
      Know ‘{x | f x + g x < Normal c /\ g x = PosInf /\ f x = NegInf} INTER space a =
             ({x | x | 0 < Normal c} INTER space a) INTER
             (({x | g x = PosInf} INTER space a) INTER
              ({x | f x = NegInf} INTER space a))’
      >- (rw [Once EXTENSION] >> EQ_TAC >> rw [extreal_add_def] \\
          art [GSYM extreal_of_num_def] \\
          fs [extreal_of_num_def, extreal_add_def]) >> Rewr' \\
      MATCH_MP_TAC SIGMA_ALGEBRA_INTER >> art [] \\
      reverse CONJ_TAC
      >- (MATCH_MP_TAC SIGMA_ALGEBRA_INTER >> METIS_TAC [IN_MEASURABLE_BOREL_ALL]) \\
      Cases_on ‘0 < Normal c’ >> rw [] >| (* 2 subgoals *)
      [ MATCH_MP_TAC SIGMA_ALGEBRA_SPACE >> art [],
        MATCH_MP_TAC SIGMA_ALGEBRA_EMPTY >> art [] ],
      (* goal 2 (of 2) *)
      Know ‘{x | f x + g x < Normal c /\ g x = NegInf} INTER space a =
            ({x | f x + g x < Normal c /\ g x = NegInf /\ f x = PosInf} INTER space a) UNION
            ({x | f x + g x < Normal c /\ g x = NegInf /\ f x = NegInf} INTER space a) UNION
            ({x | f x + g x < Normal c /\ g x = NegInf /\ f x <> PosInf /\ f x <> NegInf} INTER space a)’
      >- (rw [Once EXTENSION] \\
          EQ_TAC >> rw [] >> art [] \\
          METIS_TAC []) >> Rewr' \\
      MATCH_MP_TAC SIGMA_ALGEBRA_UNION >> art [] \\
      reverse CONJ_TAC
      >- (Know ‘{x | f x + g x < Normal c /\ g x = NegInf /\ f x <> PosInf /\
                     f x <> NegInf} INTER space a =
                space a INTER ({x | g x = NegInf} INTER space a)
                        INTER ({x | f x <> PosInf} INTER space a)
                        INTER ({x | f x <> NegInf} INTER space a)’
          >- (rw [Once EXTENSION] >> EQ_TAC >> rw [] >> art [] \\
             ‘?r. f x = Normal r’ by METIS_TAC [extreal_cases] \\
              rw [extreal_add_def, lt_infty]) >> Rewr' \\
          MATCH_MP_TAC SIGMA_ALGEBRA_INTER >> art [] \\
          reverse CONJ_TAC >- METIS_TAC [IN_MEASURABLE_BOREL_ALL] \\
          MATCH_MP_TAC SIGMA_ALGEBRA_INTER >> art [] \\
          reverse CONJ_TAC >- METIS_TAC [IN_MEASURABLE_BOREL_ALL] \\
          MATCH_MP_TAC SIGMA_ALGEBRA_INTER >> art [] \\
          reverse CONJ_TAC >- METIS_TAC [IN_MEASURABLE_BOREL_ALL] \\
          MATCH_MP_TAC SIGMA_ALGEBRA_SPACE >> art []) \\
      MATCH_MP_TAC SIGMA_ALGEBRA_UNION >> art [] \\
      CONJ_TAC
      >- (Know ‘{x | f x + g x < Normal c /\ g x = NegInf /\ f x = PosInf} INTER space a =
                ({x | x | 0 < Normal c} INTER space a) INTER
                ({x | g x = NegInf} INTER space a) INTER
                ({x | f x = PosInf} INTER space a)’
          >- (rw [Once EXTENSION] >> EQ_TAC >> rw [extreal_add_def] \\
              art [GSYM extreal_of_num_def] \\
              fs [extreal_of_num_def, extreal_add_def]) >> Rewr' \\
          MATCH_MP_TAC SIGMA_ALGEBRA_INTER >> art [] \\
          reverse CONJ_TAC >- METIS_TAC [IN_MEASURABLE_BOREL_ALL] \\
          MATCH_MP_TAC SIGMA_ALGEBRA_INTER >> art [] \\
          reverse CONJ_TAC >- METIS_TAC [IN_MEASURABLE_BOREL_ALL] \\
          Cases_on ‘0 < Normal c’ >> rw [] >| (* 2 subgoals *)
          [ MATCH_MP_TAC SIGMA_ALGEBRA_SPACE >> art [],
            MATCH_MP_TAC SIGMA_ALGEBRA_EMPTY >> art [] ]) \\
      Know ‘{x | f x + g x < Normal c /\ g x = NegInf /\ f x = NegInf} INTER space a =
            ({x | g x = NegInf} INTER space a) INTER
            ({x | f x = NegInf} INTER space a)’
      >- (rw [Once EXTENSION] >> EQ_TAC >> rw [] >> art [] \\
          rw [extreal_add_def, lt_infty]) >> Rewr' \\
      MATCH_MP_TAC SIGMA_ALGEBRA_INTER >> art [] \\
      METIS_TAC [IN_MEASURABLE_BOREL_ALL] ]
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
                           extreal_lt_eq, extreal_not_infty]
     >- (‘~(0 < 0)’ by PROVE_TAC [lt_refl] \\
         rw [extreal_add_def]) \\
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
Theorem FUBINI__new :
    !(X :'a set) (Y :'b set) A B u v f.
        sigma_finite_measure_space (X,A,u) /\
        sigma_finite_measure_space (Y,B,v) /\
        f IN measurable ((X,A) CROSS (Y,B)) Borel /\
     (* if at least one of the three integrals is finite (P \/ Q \/ R) *)
       (pos_fn_integral ((X,A,u) CROSS (Y,B,v)) (abs o f) <> PosInf \/
        pos_fn_integral (Y,B,v)
          (\y. pos_fn_integral (X,A,u) (\x. (abs o f) (x,y))) <> PosInf \/
        pos_fn_integral (X,A,u)
          (\x. pos_fn_integral (Y,B,v) (\y. (abs o f) (x,y))) <> PosInf)
       ==>
     (* then all three integrals are finite (P /\ Q /\ R) *)
        pos_fn_integral ((X,A,u) CROSS (Y,B,v)) (abs o f) <> PosInf /\
        pos_fn_integral (Y,B,v)
          (\y. pos_fn_integral (X,A,u) (\x. (abs o f) (x,y))) <> PosInf /\
        pos_fn_integral (X,A,u)
          (\x. pos_fn_integral (Y,B,v) (\y. (abs o f) (x,y))) <> PosInf /\
        integrable ((X,A,u) CROSS (Y,B,v)) f /\
       (AE y::(Y,B,v). integrable (X,A,u) (\x. f (x,y))) /\
       (AE x::(X,A,u). integrable (Y,B,v) (\y. f (x,y))) /\
        integrable (X,A,u) (\x. integral (Y,B,v) (\y. f (x,y))) /\
        integrable (Y,B,v) (\y. integral (X,A,u) (\x. f (x,y))) /\
       (integral ((X,A,u) CROSS (Y,B,v)) f =
        integral (Y,B,v) (\y. integral (X,A,u) (\x. f (x,y)))) /\
       (integral ((X,A,u) CROSS (Y,B,v)) f =
        integral (X,A,u) (\x. integral (Y,B,v) (\y. f (x,y))))
Proof
    rpt GEN_TAC
 (* prevent from separating ‘P \/ Q \/ R’ *)
 >> ONCE_REWRITE_TAC [DECIDE “(A /\ B /\ C /\ D ==> E) <=>
                              (A ==> B ==> C ==> D ==> E)”]
 >> rpt DISCH_TAC
 >> ‘measure_space ((X,A,u) CROSS (Y,B,v))’
      by PROVE_TAC [measure_space_prod_measure]
 >> ‘sigma_algebra ((X,A) CROSS (Y,B))’
      by (MATCH_MP_TAC SIGMA_ALGEBRA_PROD_SIGMA \\
          fs [sigma_algebra_def, algebra_def, sigma_finite_measure_space_def,
              measure_space_def])
 >> ‘(abs o f) IN Borel_measurable ((X,A) CROSS (Y,B))’
      by (MATCH_MP_TAC IN_MEASURABLE_BOREL_ABS' >> art [])
 >> ‘!s. s IN X CROSS Y ==> 0 <= (abs o f) s’ by rw [o_DEF, abs_pos]
 (* applying TONELLI on ‘abs o f’ *)
 >> Know ‘(!y. y IN Y ==> (\x. (abs o f) (x,y)) IN Borel_measurable (X,A)) /\
          (!x. x IN X ==> (\y. (abs o f) (x,y)) IN Borel_measurable (Y,B)) /\
          (\x. pos_fn_integral (Y,B,v) (\y. (abs o f) (x,y))) IN Borel_measurable (X,A) /\
          (\y. pos_fn_integral (X,A,u) (\x. (abs o f) (x,y))) IN Borel_measurable (Y,B) /\
          pos_fn_integral ((X,A,u) CROSS (Y,B,v)) (abs o f) =
          pos_fn_integral (Y,B,v) (\y. pos_fn_integral (X,A,u) (\x. (abs o f) (x,y))) /\
          pos_fn_integral ((X,A,u) CROSS (Y,B,v)) (abs o f) =
          pos_fn_integral (X,A,u) (\x. pos_fn_integral (Y,B,v) (\y. (abs o f) (x,y)))’
 >- (MATCH_MP_TAC (Q.SPECL [‘X’, ‘Y’, ‘A’, ‘B’, ‘u’, ‘v’, ‘abs o f’] TONELLI) \\
     rw []) >> STRIP_TAC
 >> Q.PAT_X_ASSUM ‘!s. s IN X CROSS Y ==> 0 <= (abs o f) s’ K_TAC
 (* group the first subgoals together *)
 >> NTAC 2 (ONCE_REWRITE_TAC [CONJ_ASSOC])
 >> STRONG_CONJ_TAC >- METIS_TAC []
 (* replace one of three finite integrals by all finite integrals *)
 >> Q.PAT_X_ASSUM ‘P \/ Q \/ R’ K_TAC
 >> STRIP_TAC (* P /\ Q /\ R *)
 >> Know ‘space ((X,A) CROSS (Y,B)) = X CROSS Y’
 >- (rw [prod_sigma_def] >> REWRITE_TAC [SPACE_SIGMA]) >> DISCH_TAC
 >> ‘m_space ((X,A,u) CROSS (Y,B,v)) = X CROSS Y’ by rw [prod_measure_def]
 >> ‘measurable_sets ((X,A,u) CROSS (Y,B,v)) =
       subsets ((X,A) CROSS (Y,B))’ by rw [prod_measure_def]
 >> ‘(X CROSS Y,subsets ((X,A) CROSS (Y,B))) = (X,A) CROSS (Y,B)’
       by METIS_TAC [SPACE]
 >> STRONG_CONJ_TAC
 >- (MATCH_MP_TAC integrable_from_abs >> simp [integrable_def] \\
     ASM_SIMP_TAC bool_ss [FN_PLUS_ABS_SELF, FN_MINUS_ABS_ZERO, pos_fn_integral_zero] \\
     rw [] (* 0 <> PosInf *)) >> DISCH_TAC
 (* applying TONELLI again on both f^+ and f^- *)
 >> ‘(fn_plus f) IN measurable ((X,A) CROSS (Y,B)) Borel’
      by PROVE_TAC [IN_MEASURABLE_BOREL_FN_PLUS]
 >> ‘!s. s IN X CROSS Y ==> 0 <= (fn_plus f) s’ by rw [FN_PLUS_POS]
 >> Know ‘(!y. y IN Y ==> (\x. (fn_plus f) (x,y)) IN Borel_measurable (X,A)) /\
          (!x. x IN X ==> (\y. (fn_plus f) (x,y)) IN Borel_measurable (Y,B)) /\
          (\x. pos_fn_integral (Y,B,v) (\y. (fn_plus f) (x,y))) IN Borel_measurable (X,A) /\
          (\y. pos_fn_integral (X,A,u) (\x. (fn_plus f) (x,y))) IN Borel_measurable (Y,B) /\
          pos_fn_integral ((X,A,u) CROSS (Y,B,v)) (fn_plus f) =
          pos_fn_integral (Y,B,v) (\y. pos_fn_integral (X,A,u) (\x. (fn_plus f) (x,y))) /\
          pos_fn_integral ((X,A,u) CROSS (Y,B,v)) (fn_plus f) =
          pos_fn_integral (X,A,u) (\x. pos_fn_integral (Y,B,v) (\y. (fn_plus f) (x,y)))’
 >- (MATCH_MP_TAC (Q.SPECL [‘X’, ‘Y’, ‘A’, ‘B’, ‘u’, ‘v’, ‘fn_plus f’] TONELLI) \\
     rw []) >> STRIP_TAC
 >> Q.PAT_X_ASSUM ‘!s. s IN X CROSS Y ==> 0 <= (fn_plus f) s’ K_TAC
 >> ‘(fn_minus f) IN measurable ((X,A) CROSS (Y,B)) Borel’
      by PROVE_TAC [IN_MEASURABLE_BOREL_FN_MINUS]
 >> ‘!s. s IN X CROSS Y ==> 0 <= (fn_minus f) s’ by rw [FN_MINUS_POS]
 >> Know ‘(!y. y IN Y ==> (\x. (fn_minus f) (x,y)) IN Borel_measurable (X,A)) /\
          (!x. x IN X ==> (\y. (fn_minus f) (x,y)) IN Borel_measurable (Y,B)) /\
          (\x. pos_fn_integral (Y,B,v) (\y. (fn_minus f) (x,y))) IN Borel_measurable (X,A) /\
          (\y. pos_fn_integral (X,A,u) (\x. (fn_minus f) (x,y))) IN Borel_measurable (Y,B) /\
          pos_fn_integral ((X,A,u) CROSS (Y,B,v)) (fn_minus f) =
          pos_fn_integral (Y,B,v) (\y. pos_fn_integral (X,A,u) (\x. (fn_minus f) (x,y))) /\
          pos_fn_integral ((X,A,u) CROSS (Y,B,v)) (fn_minus f) =
          pos_fn_integral (X,A,u) (\x. pos_fn_integral (Y,B,v) (\y. (fn_minus f) (x,y)))’
 >- (MATCH_MP_TAC (Q.SPECL [‘X’, ‘Y’, ‘A’, ‘B’, ‘u’, ‘v’, ‘fn_minus f’] TONELLI) \\
     rw []) >> STRIP_TAC
 >> Q.PAT_X_ASSUM ‘!s. s IN X CROSS Y ==> 0 <= (fn_minus f) s’ K_TAC
 >> Q.PAT_X_ASSUM ‘sigma_finite_measure_space (X,A,u)’
      (STRIP_ASSUME_TAC o (REWRITE_RULE [sigma_finite_measure_space_def]))
 >> Q.PAT_X_ASSUM ‘sigma_finite_measure_space (Y,B,v)’
      (STRIP_ASSUME_TAC o (REWRITE_RULE [sigma_finite_measure_space_def]))
 (* some shared properties *)
 >> Know ‘pos_fn_integral (Y,B,v)
            (\y. pos_fn_integral (X,A,u) (\x. (fn_plus f) (x,y))) <> PosInf’
 >- (REWRITE_TAC [lt_infty] \\
     MATCH_MP_TAC let_trans \\
     Q.EXISTS_TAC ‘pos_fn_integral (Y,B,v)
                     (\y. pos_fn_integral (X,A,u) (\x. (abs o f) (x,y)))’ \\
     reverse CONJ_TAC >- PROVE_TAC [lt_infty] \\
     Q.PAT_X_ASSUM ‘pos_fn_integral ((X,A,u) CROSS (Y,B,v)) (fn_plus f) =
                    pos_fn_integral (Y,B,v) (\y. pos_fn_integral (X,A,u) (\x. (fn_plus f) (x,y)))’
       (ONCE_REWRITE_TAC o wrap o SYM) \\
     Q.PAT_X_ASSUM ‘pos_fn_integral ((X,A,u) CROSS (Y,B,v)) (abs o f) =
                    pos_fn_integral (Y,B,v) (\y. pos_fn_integral (X,A,u) (\x. (abs o f) (x,y)))’
       (ONCE_REWRITE_TAC o wrap o SYM) \\
     MATCH_MP_TAC pos_fn_integral_mono \\
     rw [FN_PLUS_POS, FN_PLUS_LE_ABS]) >> DISCH_TAC
 >> Know ‘pos_fn_integral (X,A,u)
            (\x. pos_fn_integral (Y,B,v) (\y. (fn_plus f) (x,y))) <> PosInf’
 >- (REWRITE_TAC [lt_infty] \\
     MATCH_MP_TAC let_trans \\
     Q.EXISTS_TAC ‘pos_fn_integral (X,A,u)
                     (\x. pos_fn_integral (Y,B,v) (\y. (abs o f) (x,y)))’ \\
     reverse CONJ_TAC >- PROVE_TAC [lt_infty] \\
     Q.PAT_X_ASSUM ‘pos_fn_integral ((X,A,u) CROSS (Y,B,v)) (fn_plus f) =
                    pos_fn_integral (X,A,u) (\x. pos_fn_integral (Y,B,v) (\y. (fn_plus f) (x,y)))’
       (ONCE_REWRITE_TAC o wrap o SYM) \\
     Q.PAT_X_ASSUM ‘pos_fn_integral ((X,A,u) CROSS (Y,B,v)) (abs o f) =
                    pos_fn_integral (X,A,u) (\x. pos_fn_integral (Y,B,v) (\y. (abs o f) (x,y)))’
       (ONCE_REWRITE_TAC o wrap o SYM) \\
     MATCH_MP_TAC pos_fn_integral_mono \\
     rw [FN_PLUS_POS, FN_PLUS_LE_ABS]) >> DISCH_TAC
 >> Know ‘pos_fn_integral (Y,B,v)
            (\y. pos_fn_integral (X,A,u) (\x. (fn_minus f) (x,y))) <> PosInf’
 >- (REWRITE_TAC [lt_infty] \\
     MATCH_MP_TAC let_trans \\
     Q.EXISTS_TAC ‘pos_fn_integral (Y,B,v)
                     (\y. pos_fn_integral (X,A,u) (\x. (abs o f) (x,y)))’ \\
     reverse CONJ_TAC >- PROVE_TAC [lt_infty] \\
     Q.PAT_X_ASSUM ‘pos_fn_integral ((X,A,u) CROSS (Y,B,v)) (fn_minus f) =
                    pos_fn_integral (Y,B,v) (\y. pos_fn_integral (X,A,u) (\x. (fn_minus f) (x,y)))’
       (ONCE_REWRITE_TAC o wrap o SYM) \\
     Q.PAT_X_ASSUM ‘pos_fn_integral ((X,A,u) CROSS (Y,B,v)) (abs o f) =
                    pos_fn_integral (Y,B,v) (\y. pos_fn_integral (X,A,u) (\x. (abs o f) (x,y)))’
       (ONCE_REWRITE_TAC o wrap o SYM) \\
     MATCH_MP_TAC pos_fn_integral_mono \\
     rw [FN_MINUS_POS, FN_MINUS_LE_ABS]) >> DISCH_TAC
 >> Know ‘pos_fn_integral (X,A,u)
            (\x. pos_fn_integral (Y,B,v) (\y. (fn_minus f) (x,y))) <> PosInf’
 >- (REWRITE_TAC [lt_infty] \\
     MATCH_MP_TAC let_trans \\
     Q.EXISTS_TAC ‘pos_fn_integral (X,A,u)
                     (\x. pos_fn_integral (Y,B,v) (\y. (abs o f) (x,y)))’ \\
     reverse CONJ_TAC >- PROVE_TAC [lt_infty] \\
     Q.PAT_X_ASSUM ‘pos_fn_integral ((X,A,u) CROSS (Y,B,v)) (fn_minus f) =
                    pos_fn_integral (X,A,u) (\x. pos_fn_integral (Y,B,v) (\y. (fn_minus f) (x,y)))’
       (ONCE_REWRITE_TAC o wrap o SYM) \\
     Q.PAT_X_ASSUM ‘pos_fn_integral ((X,A,u) CROSS (Y,B,v)) (abs o f) =
                    pos_fn_integral (X,A,u) (\x. pos_fn_integral (Y,B,v) (\y. (abs o f) (x,y)))’
       (ONCE_REWRITE_TAC o wrap o SYM) \\
     MATCH_MP_TAC pos_fn_integral_mono \\
     rw [FN_MINUS_POS, FN_MINUS_LE_ABS]) >> DISCH_TAC
 (* clean up useless assumptions *)
 >> Q.PAT_X_ASSUM ‘sigma_finite (X,A,u)’ K_TAC
 >> Q.PAT_X_ASSUM ‘sigma_finite (Y,B,v)’ K_TAC
 (* push ‘fn_plus/fn_minus’ inside *)
 >> ‘!y. fn_plus (\x. f (x,y)) = (\x. (fn_plus f) (x,y))’   by rw [FUN_EQ_THM, FN_PLUS_ALT]
 >> ‘!y. fn_minus (\x. f (x,y)) = (\x. (fn_minus f) (x,y))’ by rw [FUN_EQ_THM, FN_MINUS_ALT]
 >> ‘!x. fn_plus (\y. f (x,y)) = (\y. (fn_plus f) (x,y))’   by rw [FUN_EQ_THM, FN_PLUS_ALT]
 >> ‘!x. fn_minus (\y. f (x,y)) = (\y. (fn_minus f) (x,y))’ by rw [FUN_EQ_THM, FN_MINUS_ALT]
 (* goal: AE y::(Y,B,v). integrable (X,A,u) (\x. f (x,y)) *)
 >> STRONG_CONJ_TAC
 >- (rw [Once FN_DECOMP, integrable_def] \\
  (* applying pos_fn_integral_infty_null *)
     Know ‘null_set (Y,B,v) {y | y IN m_space (Y,B,v) /\
                                 ((\y. pos_fn_integral (X,A,u) (\x. (fn_plus f) (x,y))) y = PosInf)}’
     >- (MATCH_MP_TAC pos_fn_integral_infty_null >> simp [] \\
         Q.X_GEN_TAC ‘y’ >> DISCH_TAC \\
         MATCH_MP_TAC pos_fn_integral_pos >> rw [FN_PLUS_POS]) \\
     simp [] >> DISCH_TAC \\
     Know ‘null_set (Y,B,v) {y | y IN m_space (Y,B,v) /\
                                 ((\y. pos_fn_integral (X,A,u) (\x. (fn_minus f) (x,y))) y = PosInf)}’
     >- (MATCH_MP_TAC pos_fn_integral_infty_null >> simp [] \\
         Q.X_GEN_TAC ‘y’ >> DISCH_TAC \\
         MATCH_MP_TAC pos_fn_integral_pos >> rw [FN_MINUS_POS]) \\
     simp [] >> DISCH_TAC \\
     rw [AE_THM, almost_everywhere_def] \\
     Q.EXISTS_TAC ‘{y | y IN Y /\ pos_fn_integral (X,A,u) (\x. (fn_plus f) (x,y)) = PosInf} UNION
                   {y | y IN Y /\ pos_fn_integral (X,A,u) (\x. (fn_minus f) (x,y)) = PosInf}’ \\
     CONJ_TAC >- (PROVE_TAC [NULL_SET_UNION, GSYM IN_NULL_SET]) \\
     Q.X_GEN_TAC ‘y’ >> rw []
     >- (‘!x. (fn_plus f) (x,y) - (fn_minus f) (x,y) = f (x,y)’
            by METIS_TAC [FN_DECOMP] >> POP_ORW \\
         simp [Once IN_MEASURABLE_BOREL_PLUS_MINUS]) \\
     art []) >> DISCH_TAC
 (* goal: AE x::(X,A,u). integrable (Y,B,v) (\y. f (x,y)) *)
 >> STRONG_CONJ_TAC
 >- (rw [Once FN_DECOMP, integrable_def] \\
  (* applying pos_fn_integral_infty_null *)
     Know ‘null_set (X,A,u) {x | x IN m_space (X,A,u) /\
                                 ((\x. pos_fn_integral (Y,B,v) (\y. (fn_plus f) (x,y))) x = PosInf)}’
     >- (MATCH_MP_TAC pos_fn_integral_infty_null >> simp [] \\
         Q.X_GEN_TAC ‘x’ >> DISCH_TAC \\
         MATCH_MP_TAC pos_fn_integral_pos >> rw [FN_PLUS_POS]) \\
     simp [] >> DISCH_TAC \\
     Know ‘null_set (X,A,u) {x | x IN m_space (X,A,u) /\
                                 ((\x. pos_fn_integral (Y,B,v) (\y. (fn_minus f) (x,y))) x = PosInf)}’
     >- (MATCH_MP_TAC pos_fn_integral_infty_null >> simp [] \\
         Q.X_GEN_TAC ‘x’ >> DISCH_TAC \\
         MATCH_MP_TAC pos_fn_integral_pos >> rw [FN_MINUS_POS]) \\
     simp [] >> DISCH_TAC \\
     rw [AE_THM, almost_everywhere_def] \\
     Q.EXISTS_TAC ‘{x | x IN X /\ pos_fn_integral (Y,B,v) (\y. (fn_plus f) (x,y)) = PosInf} UNION
                   {x | x IN X /\ pos_fn_integral (Y,B,v) (\y. (fn_minus f) (x,y)) = PosInf}’ \\
     CONJ_TAC >- (PROVE_TAC [NULL_SET_UNION, GSYM IN_NULL_SET]) \\
     Q.X_GEN_TAC ‘x’ >> rw []
     >- (‘!y. (fn_plus f) (x,y) - (fn_minus f) (x,y) = f (x,y)’
            by METIS_TAC [FN_DECOMP] >> POP_ORW \\
         simp [Once IN_MEASURABLE_BOREL_PLUS_MINUS]) \\
     art []) >> DISCH_TAC
 (* goal: integrable (X,A,u) (\x. integral (Y,B,v) (\y. f (x,y))) *)
 >> STRONG_CONJ_TAC
 >- (rw [integrable_def] >| (* 3 subgoals *)
     [ (* goal 1 (of 3) *)
       MATCH_MP_TAC (REWRITE_RULE [m_space_def, measurable_sets_def]
                                  (Q.SPEC ‘(X,A,u)’ IN_MEASURABLE_BOREL_EQ)) \\
       Q.EXISTS_TAC ‘\x. pos_fn_integral (Y,B,v) (\y. fn_plus f (x,y)) -
                         pos_fn_integral (Y,B,v) (\y. fn_minus f (x,y))’ >> BETA_TAC \\
       CONJ_TAC >- RW_TAC std_ss [integral_def] \\
       MATCH_MP_TAC IN_MEASURABLE_BOREL_SUB__new \\
       FULL_SIMP_TAC std_ss [measure_space_def, space_def, m_space_def, measurable_sets_def] \\
       qexistsl_tac [‘\x. pos_fn_integral (Y,B,v) (\y. fn_plus f (x,y))’,
                     ‘\x. pos_fn_integral (Y,B,v) (\y. fn_minus f (x,y))’] >> simp [],
       (* goal 2 (of 3) *)
       REWRITE_TAC [lt_infty] >> MATCH_MP_TAC let_trans \\
       Q.EXISTS_TAC ‘pos_fn_integral (X,A,u) (\x. pos_fn_integral (Y,B,v) (\y. (abs o f) (x,y)))’ \\
       reverse CONJ_TAC >- art [GSYM lt_infty] \\
       MATCH_MP_TAC pos_fn_integral_mono_AE >> rw [FN_PLUS_POS]
       >- (MATCH_MP_TAC pos_fn_integral_pos >> rw [abs_pos]) \\
       Q.PAT_X_ASSUM ‘AE x::(X,A,u). integrable (Y,B,v) (\y. f (x,y))’ MP_TAC \\
       rw [AE_THM, almost_everywhere_def] \\
       Q.EXISTS_TAC ‘N’ >> rw [] \\
       MATCH_MP_TAC le_trans \\
       Q.EXISTS_TAC ‘abs ((\x. integral (Y,B,v) (\y. f (x,y))) x)’ \\
       CONJ_TAC >- REWRITE_TAC [FN_PLUS_LE_ABS] >> BETA_TAC \\
       MP_TAC (Q.SPECL [‘(Y,B,v)’, ‘(\y. f (x,y))’]
                       (INST_TYPE [alpha |-> beta] integral_triangle_ineq')) \\
       simp [o_DEF],
       (* goal 3 (of 3) *)
       REWRITE_TAC [lt_infty] >> MATCH_MP_TAC let_trans \\
       Q.EXISTS_TAC ‘pos_fn_integral (X,A,u) (\x. pos_fn_integral (Y,B,v) (\y. (abs o f) (x,y)))’ \\
       reverse CONJ_TAC >- art [GSYM lt_infty] \\
       MATCH_MP_TAC pos_fn_integral_mono_AE >> rw [FN_MINUS_POS]
       >- (MATCH_MP_TAC pos_fn_integral_pos >> rw [abs_pos]) \\
       Q.PAT_X_ASSUM ‘AE x::(X,A,u). integrable (Y,B,v) (\y. f (x,y))’ MP_TAC \\
       rw [AE_THM, almost_everywhere_def] \\
       Q.EXISTS_TAC ‘N’ >> rw [] \\
       MATCH_MP_TAC le_trans \\
       Q.EXISTS_TAC ‘abs ((\x. integral (Y,B,v) (\y. f (x,y))) x)’ \\
       CONJ_TAC >- REWRITE_TAC [FN_MINUS_LE_ABS] >> BETA_TAC \\
       MP_TAC (Q.SPECL [‘(Y,B,v)’, ‘(\y. f (x,y))’]
                       (INST_TYPE [alpha |-> beta] integral_triangle_ineq')) \\
       simp [o_DEF] ]) >> DISCH_TAC
 (* goal: integrable (Y,B,v) (\y. integral (X,A,u) (\y. f (x,y))) *)
 >> STRONG_CONJ_TAC
 >- (rw [integrable_def] >| (* 3 subgoals *)
     [ (* goal 1 (of 3) *)
       MATCH_MP_TAC (REWRITE_RULE [m_space_def, measurable_sets_def]
                                  (ISPEC “(Y,B,v) :'b m_space” IN_MEASURABLE_BOREL_EQ)) \\
       Q.EXISTS_TAC ‘\y. pos_fn_integral (X,A,u) (\x. fn_plus f (x,y)) -
                         pos_fn_integral (X,A,u) (\x. fn_minus f (x,y))’ >> BETA_TAC \\
       CONJ_TAC >- RW_TAC std_ss [integral_def] \\
       MATCH_MP_TAC IN_MEASURABLE_BOREL_SUB__new \\
       FULL_SIMP_TAC std_ss [measure_space_def, space_def, m_space_def, measurable_sets_def] \\
       qexistsl_tac [‘\y. pos_fn_integral (X,A,u) (\x. fn_plus f (x,y))’,
                     ‘\y. pos_fn_integral (X,A,u) (\x. fn_minus f (x,y))’] >> simp [],
       (* goal 2 (of 3) *)
       REWRITE_TAC [lt_infty] >> MATCH_MP_TAC let_trans \\
       Q.EXISTS_TAC ‘pos_fn_integral (Y,B,v) (\y. pos_fn_integral (X,A,u) (\x. (abs o f) (x,y)))’ \\
       reverse CONJ_TAC >- art [GSYM lt_infty] \\
       MATCH_MP_TAC pos_fn_integral_mono_AE >> rw [FN_PLUS_POS]
       >- (MATCH_MP_TAC pos_fn_integral_pos >> rw [abs_pos]) \\
       Q.PAT_X_ASSUM ‘AE y::(Y,B,v). integrable (X,A,u) (\x. f (x,y))’ MP_TAC \\
       rw [AE_THM, almost_everywhere_def] \\
       Q.EXISTS_TAC ‘N’ >> rw [] >> rename1 ‘y IN Y’ \\
       MATCH_MP_TAC le_trans \\
       Q.EXISTS_TAC ‘abs ((\y. integral (X,A,u) (\x. f (x,y))) y)’ \\
       CONJ_TAC >- REWRITE_TAC [FN_PLUS_LE_ABS] >> BETA_TAC \\
       MP_TAC (Q.SPECL [‘(X,A,u)’, ‘(\x. f (x,y))’] integral_triangle_ineq') \\
       simp [o_DEF],
       (* goal 3 (of 3) *)
       REWRITE_TAC [lt_infty] >> MATCH_MP_TAC let_trans \\
       Q.EXISTS_TAC ‘pos_fn_integral (Y,B,v) (\y. pos_fn_integral (X,A,u) (\x. (abs o f) (x,y)))’ \\
       reverse CONJ_TAC >- art [GSYM lt_infty] \\
       MATCH_MP_TAC pos_fn_integral_mono_AE >> rw [FN_MINUS_POS]
       >- (MATCH_MP_TAC pos_fn_integral_pos >> rw [abs_pos]) \\
       Q.PAT_X_ASSUM ‘AE y::(Y,B,v). integrable (X,A,u) (\x. f (x,y))’ MP_TAC \\
       rw [AE_THM, almost_everywhere_def] \\
       Q.EXISTS_TAC ‘N’ >> rw [] >> rename1 ‘y IN Y’ \\
       MATCH_MP_TAC le_trans \\
       Q.EXISTS_TAC ‘abs ((\y. integral (X,A,u) (\x. f (x,y))) y)’ \\
       CONJ_TAC >- REWRITE_TAC [FN_MINUS_LE_ABS] >> BETA_TAC \\
       MP_TAC (Q.SPECL [‘(X,A,u)’, ‘(\x. f (x,y))’] integral_triangle_ineq') \\
       simp [o_DEF] ]) >> DISCH_TAC
 (* final goals *)
 >> CONJ_TAC
 >| [ (* goal 1 (of 2) *)
      GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) empty_rewrites [integral_def] \\
      Know ‘integral (Y,B,v) (\y. integral (X,A,u) (\x. f (x,y))) =
            integral (Y,B,v) (\y. pos_fn_integral (X,A,u) (\x. fn_plus f (x,y)) -
                                  pos_fn_integral (X,A,u) (\x. fn_minus f (x,y)))’
      >- (MATCH_MP_TAC integral_cong >> simp [] \\
          Q.X_GEN_TAC ‘y’ >> rw [integral_def]) >> Rewr' \\
      Q.PAT_X_ASSUM ‘pos_fn_integral ((X,A,u) CROSS (Y,B,v)) (fn_plus f) =
                     pos_fn_integral (Y,B,v) (\y. pos_fn_integral (X,A,u) (\x. fn_plus f (x,y)))’
          (ONCE_REWRITE_TAC o wrap) \\
      Q.PAT_X_ASSUM ‘pos_fn_integral ((X,A,u) CROSS (Y,B,v)) (fn_minus f) =
                     pos_fn_integral (Y,B,v) (\y. pos_fn_integral (X,A,u) (\x. fn_minus f (x,y)))’
          (ONCE_REWRITE_TAC o wrap) \\
      MATCH_MP_TAC EQ_SYM \\
      MATCH_MP_TAC integral_add_lemma__new >> rw [] >| (* 5 subgoals *)
      [ (* goal 1.1 (of 5) *)
        MATCH_MP_TAC integrable_eq >> simp [] \\
        Q.EXISTS_TAC ‘\y. integral (X,A,u) (\x. f (x,y))’ >> simp [integral_def],
        (* goal 1.2 (of 5) *)
        Q.ABBREV_TAC ‘g = \y. pos_fn_integral (X,A,u) (\x. fn_plus f (x,y))’ \\
        Know ‘integrable (Y,B,v) g <=>
              g IN Borel_measurable (Y,B) /\ pos_fn_integral (Y,B,v) g <> PosInf’
        >- (MATCH_MP_TAC
              (REWRITE_RULE [m_space_def, measurable_sets_def]
                            (Q.SPEC ‘(Y,B,v)’ (INST_TYPE [alpha |-> beta] integrable_pos))) \\
            rw [Abbr ‘g’] \\
            MATCH_MP_TAC pos_fn_integral_pos >> rw [FN_PLUS_POS]) >> Rewr' \\
        Q.UNABBREV_TAC ‘g’ >> art [],
        (* goal 1.3 (of 5) *)
        Q.ABBREV_TAC ‘g = \y. pos_fn_integral (X,A,u) (\x. fn_minus f (x,y))’ \\
        Know ‘integrable (Y,B,v) g <=>
              g IN Borel_measurable (Y,B) /\ pos_fn_integral (Y,B,v) g <> PosInf’
        >- (MATCH_MP_TAC
              (REWRITE_RULE [m_space_def, measurable_sets_def]
                            (Q.SPEC ‘(Y,B,v)’ (INST_TYPE [alpha |-> beta] integrable_pos))) \\
            rw [Abbr ‘g’] \\
            MATCH_MP_TAC pos_fn_integral_pos >> rw [FN_MINUS_POS]) >> Rewr' \\
        Q.UNABBREV_TAC ‘g’ >> art [],
        (* goal 1.4 (of 5) *)
        MATCH_MP_TAC pos_fn_integral_pos >> rw [FN_PLUS_POS],
        (* goal 1.5 (of 5) *)
        MATCH_MP_TAC pos_fn_integral_pos >> rw [FN_MINUS_POS] ],
      (* goal 2 (of 2) *)
      GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) empty_rewrites [integral_def] \\
      Know ‘integral (X,A,u) (\x. integral (Y,B,v) (\y. f (x,y))) =
            integral (X,A,u) (\x. pos_fn_integral (Y,B,v) (\y. fn_plus f (x,y)) -
                                  pos_fn_integral (Y,B,v) (\y. fn_minus f (x,y)))’
      >- (MATCH_MP_TAC integral_cong >> simp [] \\
          Q.X_GEN_TAC ‘x’ >> rw [integral_def]) >> Rewr' \\
      Q.PAT_X_ASSUM ‘pos_fn_integral ((X,A,u) CROSS (Y,B,v)) (fn_plus f) =
                     pos_fn_integral (X,A,u) (\x. pos_fn_integral (Y,B,v) (\y. fn_plus f (x,y)))’
          (ONCE_REWRITE_TAC o wrap) \\
      Q.PAT_X_ASSUM ‘pos_fn_integral ((X,A,u) CROSS (Y,B,v)) (fn_minus f) =
                     pos_fn_integral (X,A,u) (\x. pos_fn_integral (Y,B,v) (\y. fn_minus f (x,y)))’
          (ONCE_REWRITE_TAC o wrap) \\
      MATCH_MP_TAC EQ_SYM \\
      MATCH_MP_TAC integral_add_lemma__new >> rw [] >| (* 5 subgoals *)
      [ (* goal 2.1 (of 5) *)
        MATCH_MP_TAC integrable_eq >> simp [] \\
        Q.EXISTS_TAC ‘\x. integral (Y,B,v) (\y. f (x,y))’ >> simp [integral_def],
        (* goal 2.2 (of 5) *)
        Q.ABBREV_TAC ‘g = \x. pos_fn_integral (Y,B,v) (\y. fn_plus f (x,y))’ \\
        Know ‘integrable (X,A,u) g <=>
              g IN Borel_measurable (X,A) /\ pos_fn_integral (X,A,u) g <> PosInf’
        >- (MATCH_MP_TAC (REWRITE_RULE [m_space_def, measurable_sets_def]
                                       (Q.SPEC ‘(X,A,u)’ integrable_pos)) \\
            rw [Abbr ‘g’] \\
            MATCH_MP_TAC pos_fn_integral_pos >> rw [FN_PLUS_POS]) >> Rewr' \\
        Q.UNABBREV_TAC ‘g’ >> art [],
        (* goal 2.3 (of 5) *)
        Q.ABBREV_TAC ‘g = \x. pos_fn_integral (Y,B,v) (\y. fn_minus f (x,y))’ \\
        Know ‘integrable (X,A,u) g <=>
              g IN Borel_measurable (X,A) /\ pos_fn_integral (X,A,u) g <> PosInf’
        >- (MATCH_MP_TAC (REWRITE_RULE [m_space_def, measurable_sets_def]
                                       (Q.SPEC ‘(X,A,u)’ integrable_pos)) \\
            rw [Abbr ‘g’] \\
            MATCH_MP_TAC pos_fn_integral_pos >> rw [FN_MINUS_POS]) >> Rewr' \\
        Q.UNABBREV_TAC ‘g’ >> art [],
        (* goal 2.4 (of 5) *)
        MATCH_MP_TAC pos_fn_integral_pos >> rw [FN_PLUS_POS],
        (* goal 2.5 (of 5) *)
        MATCH_MP_TAC pos_fn_integral_pos >> rw [FN_MINUS_POS] ] ]
QED

val _ = export_theory ();
val _ = html_theory "fubini";
