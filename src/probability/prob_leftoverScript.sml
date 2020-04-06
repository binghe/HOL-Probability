open HolKernel Parse boolLib bossLib;

open hurdUtils util_probTheory extrealTheory sigma_algebraTheory
     measureTheory borelTheory lebesgueTheory martingaleTheory
     probabilityTheory;

val _ = new_theory "leftover";

(*** lebesgueTheory ***)

(* from (old) real_lebesgueScript.sml, the FIRST result about `RN_deriv`,
   for the first time, division (/) of extreals is used. (0 / 0 is undefined)
 
Theorem finite_POW_RN_deriv_reduce :
    !m v. measure_space m /\ FINITE (m_space m) /\
          measure m (m_space m) < PosInf /\ (* newly added *)
                  v (m_space m) < PosInf /\ (* newly added *)
          measure_space (m_space m,measurable_sets m,v) /\
          (POW (m_space m) = measurable_sets m) /\
          (!x. (measure m {x} = 0) ==> (v {x} = 0)) ==>
       !x. x IN m_space m /\ measure m {x} <> 0 ==>
           (RN_deriv v m x = v {x} / measure m {x})
Proof
    RW_TAC std_ss [RN_deriv_def, density_def]
 >> Suff `(\f. f x = v {x} / measure m {x})
            (@f. f IN borel_measurable (m_space m,measurable_sets m) /\
                 (!x. x IN m_space m ==> 0 <= f x) /\
                 !a. a IN measurable_sets m ==>
                    (integral m (\x. f x * indicator_fn a x) = v a))`
 >- RW_TAC std_ss []
 >> MATCH_MP_TAC SELECT_ELIM_THM
 >> RW_TAC std_ss [] (* 2 subgoals *)
 >- (Q.EXISTS_TAC `\x. if measure m {x} = 0 then 0 else v {x} / measure m {x}` \\
     SIMP_TAC std_ss [] \\
     STRONG_CONJ_TAC
     >- (Q.PAT_X_ASSUM `P = Q` (MP_TAC o GSYM)
         >> RW_TAC std_ss [IN_MEASURABLE_BOREL, space_def, subsets_def, IN_FUNSET, IN_UNIV,
                           POW_SIGMA_ALGEBRA]
         >> RW_TAC std_ss [IN_POW, INTER_SUBSET]) \\
     DISCH_TAC >> STRONG_CONJ_TAC
     >- (rpt STRIP_TAC \\
        `{x'} IN measurable_sets m` by PROVE_TAC [IN_POW, IN_SING, SUBSET_DEF] \\
         Cases_on `measure m {x'} = 0` >- PROVE_TAC [le_refl] \\
         fs [] \\ (* now: 0 <= v {x'} / measure m {x'} *)
         Know `measure (m_space m,measurable_sets m,v) {x'} <> NegInf /\
               measure (m_space m,measurable_sets m,v) {x'} <> PosInf`
         >- (CONJ_TAC >- (MATCH_MP_TAC pos_not_neginf \\
                          fs [measure_space_def, positive_def, measurable_sets_def,
                              measure_def]) \\
             MATCH_MP_TAC MEASURE_SPACE_FINITE_MEASURE \\
             RW_TAC std_ss [m_space_def, measurable_sets_def, measure_def, lt_infty]) \\
         DISCH_THEN (STRIP_ASSUME_TAC o (REWRITE_RULE [measure_def])) \\
         Cases_on `(measure m {x'} = NegInf) \/ (measure m {x'} = PosInf)`
         >- METIS_TAC [div_infty, le_refl] >> fs [] \\
        `?c. measure m {x'} = Normal c` by PROVE_TAC [extreal_cases] \\
         Know `0 <= Normal c`
         >- (POP_ASSUM (ONCE_REWRITE_TAC o wrap o SYM) \\
             PROVE_TAC [measure_space_def, positive_def]) \\
         DISCH_TAC \\
        `0 < c` by PROVE_TAC [le_lt, extreal_lt_eq, extreal_of_num_def] \\
         POP_ASSUM (STRIP_ASSUME_TAC o (MATCH_MP le_rdiv)) \\
         Q.PAT_X_ASSUM `measure m {x'} = Normal c` (ONCE_REWRITE_TAC o wrap) \\
         POP_ASSUM (ONCE_REWRITE_TAC o wrap o GSYM) \\
         REWRITE_TAC [mul_lzero] \\
         fs [measure_space_def, positive_def, measure_def, measurable_sets_def]) \\
     DISCH_TAC \\
     Q.ABBREV_TAC `dvm = \x. if measure m {x} = 0 then 0 else v {x} / measure m {x}` \\
     fs [] \\
     GEN_TAC >> DISCH_TAC \\
     MP_TAC (Q.ISPECL [`(m :'a m_space)`, `\x':'a. dvm x' * indicator_fn a x'`]
                      finite_space_POW_integral_reduce) \\
     Know `!x. x IN m_space m ==> dvm x * indicator_fn a x <> NegInf /\
                                  dvm x * indicator_fn a x <> PosInf`
     >- (Q.X_GEN_TAC `y` >> DISCH_TAC \\
        `0 <= indicator_fn a y` by PROVE_TAC [INDICATOR_FN_POS] \\
        `?c. indicator_fn a y = Normal c`
           by PROVE_TAC [INDICATOR_FN_NOT_INFTY, extreal_cases] \\
         POP_ASSUM ((FULL_SIMP_TAC std_ss) o wrap) \\
         POP_ASSUM (ASSUME_TAC o (REWRITE_RULE [extreal_of_num_def, extreal_le_eq])) \\
         ONCE_REWRITE_TAC [mul_comm] \\
         CONJ_TAC >- METIS_TAC [mul_not_infty, pos_not_neginf] \\
         Suff `dvm y <> PosInf` >- METIS_TAC [mul_not_infty] \\
         Q.UNABBREV_TAC `dvm` >> BETA_TAC \\
         Cases_on `measure m {y} = 0`
         >- METIS_TAC [extreal_of_num_def, extreal_not_infty] \\
         rw [] \\
        `{y} IN measurable_sets m` by PROVE_TAC [IN_POW, IN_SING, SUBSET_DEF] \\
         Know `measure (m_space m,measurable_sets m,v) {y} <> NegInf /\
               measure (m_space m,measurable_sets m,v) {y} <> PosInf`
         >- (CONJ_TAC >- (MATCH_MP_TAC pos_not_neginf \\
                          fs [measure_space_def, positive_def, measurable_sets_def,
                              measure_def]) \\
             MATCH_MP_TAC MEASURE_SPACE_FINITE_MEASURE \\
             RW_TAC std_ss [m_space_def, measurable_sets_def, measure_def, lt_infty]) \\
         DISCH_THEN (STRIP_ASSUME_TAC o (REWRITE_RULE [measure_def])) \\
        `?r. v {y} = Normal r` by PROVE_TAC [extreal_cases] >> rw [] \\
         PROVE_TAC [div_not_infty]) \\
     RW_TAC std_ss [] \\

(* TODO *)

     ONCE_REWRITE_TAC [(UNDISCH o Q.SPEC `m_space m`) REAL_SUM_IMAGE_IN_IF]
     >> `(\x.
         (if x IN m_space m then
            (\x'. v {x'} / measure m {x'} * indicator_fn a x' * measure m {x'}) x
          else
            0)) =
           (\x. if x IN m_space m then
                (\x'. (\x'. v {x'}) x' * indicator_fn a x') x else 0)`
        by (RW_TAC std_ss [FUN_EQ_THM] >> RW_TAC std_ss [real_div]
            >> Cases_on `measure m {x'} = 0`
            >- RW_TAC real_ss []
            >> `v {x'} * inv (measure m {x'}) * indicator_fn a x' * measure m {x'} =
                (inv (measure m {x'}) * measure m {x'}) * v {x'} * indicator_fn a x'`
                by REAL_ARITH_TAC
            >> POP_ORW
            >> RW_TAC real_ss [REAL_MUL_LINV])
       >> POP_ORW
       >> ASM_SIMP_TAC std_ss [GSYM REAL_SUM_IMAGE_IN_IF]
       >> `a SUBSET m_space m` by METIS_TAC [IN_POW]
       >> `m_space m = a UNION (m_space m DIFF a)`
                by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_DIFF, IN_UNION] \\
                    METIS_TAC [SUBSET_DEF])
       >> POP_ORW
       >> `DISJOINT a (m_space m DIFF a)`
                by (RW_TAC std_ss [IN_DISJOINT, IN_DIFF] >> DECIDE_TAC)
       >> `SIGMA (\x'. v {x'} * indicator_fn a x') (a UNION (m_space m DIFF a)) =
           SIGMA (\x'. v {x'} * indicator_fn a x') a +
           SIGMA (\x'. v {x'} * indicator_fn a x') (m_space m DIFF a)`
        by (MATCH_MP_TAC REAL_SUM_IMAGE_DISJOINT_UNION >> METIS_TAC [FINITE_DIFF, SUBSET_FINITE])
       >> POP_ORW
       >> `FINITE a` by METIS_TAC [SUBSET_FINITE]
       >> `FINITE (m_space m DIFF a)` by RW_TAC std_ss [FINITE_DIFF]
       >> ONCE_REWRITE_TAC [(UNDISCH o Q.SPEC `a`) REAL_SUM_IMAGE_IN_IF]
       >> ONCE_REWRITE_TAC [(UNDISCH o Q.SPEC `m_space m DIFF a`) REAL_SUM_IMAGE_IN_IF]
       >> `(\x.
         (if x IN m_space m DIFF a then
            (\x'. v {x'} * indicator_fn a x') x
          else
            0)) = (\x. 0)`
        by (RW_TAC std_ss [FUN_EQ_THM] >> RW_TAC real_ss [IN_DIFF, indicator_fn_def])
       >> RW_TAC real_ss [REAL_SUM_IMAGE_0]
       >> `(\x'. (if x' IN a then v {x'} * indicator_fn a x' else 0)) =
           (\x'. if x' IN a then (\x'. v {x'}) x' else 0)`
        by (RW_TAC std_ss [FUN_EQ_THM] >> RW_TAC real_ss [indicator_fn_def])
       >> POP_ORW >> ASM_SIMP_TAC std_ss [GSYM REAL_SUM_IMAGE_IN_IF]
       >> `!x. v = measure (m_space m,measurable_sets m,v)` by RW_TAC std_ss [measure_def]
       >> POP_ORW
       >> ONCE_REWRITE_TAC [EQ_SYM_EQ]
       >> MATCH_MP_TAC MEASURE_REAL_SUM_IMAGE
       >> RW_TAC std_ss [measurable_sets_def]
       >> METIS_TAC [SUBSET_DEF, IN_POW, IN_SING])
 >> POP_ASSUM (MP_TAC o Q.SPEC `{x}`)
 >> `{x} IN measurable_sets m` by METIS_TAC [SUBSET_DEF, IN_POW, IN_SING]
 >> ASM_SIMP_TAC std_ss []
 >> (MP_TAC o Q.SPECL [`m`,`(\x''. x' x'' * indicator_fn {x} x'')`])
      finite_space_POW_integral_reduce
 >> ASM_SIMP_TAC std_ss []
 >> STRIP_TAC >> POP_ASSUM (K ALL_TAC)
 >> `x IN m_space m` by METIS_TAC [IN_POW, SUBSET_DEF, IN_SING]
 >> `m_space m = {x} UNION (m_space m DIFF {x})`
                by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_UNION, IN_DIFF, IN_SING] \\
                    METIS_TAC [])
 >> POP_ORW
 >> `DISJOINT {x} (m_space m DIFF {x})`
                by (RW_TAC std_ss [IN_DISJOINT, IN_DIFF, IN_SING] >> METIS_TAC [])
 >> `SIGMA (\x''. x' x'' * indicator_fn {x} x'' * measure m {x''}) ({x} UNION (m_space m DIFF {x}))
         = SIGMA (\x''. x' x'' * indicator_fn {x} x'' * measure m {x''}) {x} +
           SIGMA (\x''. x' x'' * indicator_fn {x} x'' * measure m {x''}) (m_space m DIFF {x})`
        by (MATCH_MP_TAC REAL_SUM_IMAGE_DISJOINT_UNION >> METIS_TAC [FINITE_DIFF, FINITE_SING])
 >> POP_ORW
 >> SIMP_TAC std_ss [REAL_SUM_IMAGE_SING]
 >> `FINITE (m_space m DIFF {x})` by RW_TAC std_ss [FINITE_DIFF]
 >> ONCE_REWRITE_TAC [(UNDISCH o Q.SPEC `m_space m DIFF {x}`) REAL_SUM_IMAGE_IN_IF]
 >> `(\x''.
          (if x'' IN m_space m DIFF {x} then
             (\x''. x' x'' * indicator_fn {x} x'' * measure m {x''}) x''
           else
             0)) = (\x. 0)`
        by (RW_TAC std_ss [FUN_EQ_THM] >> RW_TAC real_ss [IN_DIFF, indicator_fn_def])
 >> POP_ORW
 >> ASM_SIMP_TAC real_ss [REAL_SUM_IMAGE_0]
 >> `0 < measure m {x}`
        by METIS_TAC [measure_space_def, positive_def, REAL_LE_LT]
 >> ASM_SIMP_TAC real_ss [REAL_EQ_RDIV_EQ, indicator_fn_def, IN_SING]
QED

val finite_POW_prod_measure_reduce = store_thm
  ("finite_POW_prod_measure_reduce",
  ``!m0 m1. measure_space m0 /\ measure_space m1 /\
            FINITE (m_space m0) /\ FINITE (m_space m1) /\
           (POW (m_space m0) = measurable_sets m0) /\
           (POW (m_space m1) = measurable_sets m1)
        ==> !a0 a1. a0 IN measurable_sets m0 /\ a1 IN measurable_sets m1 ==>
                   (prod_measure m0 m1 (a0 CROSS a1) = measure m0 a0 * measure m1 a1)``,
 (* proof *)
    RW_TAC std_ss [prod_measure_def, measure_def, finite_space_POW_integral_reduce,
                   extreal_not_infty]
 >> RW_TAC std_ss [extreal_mul_def, EXTREAL_SUM_IMAGE_NORMAL, real_normal]
 >> `!s0 s1 x. PREIMAGE (\s1. (x,s1)) (a0 CROSS a1) SUBSET (m_space m1)`
     by (RW_TAC std_ss [SUBSET_DEF, IN_PREIMAGE, IN_CROSS]
         >> METIS_TAC [MEASURE_SPACE_SUBSET_MSPACE, SUBSET_DEF])
 >> `(m_space m0) = a0 UNION ((m_space m0) DIFF a0)`
     by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_UNION, IN_DIFF]
         >> METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE, SUBSET_DEF])
 >> POP_ORW
 >> `DISJOINT a0 (m_space m0 DIFF a0)`
     by (RW_TAC std_ss [IN_DISJOINT, IN_DIFF] >> DECIDE_TAC)
 >> `FINITE a0` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE, SUBSET_FINITE]
 >> RW_TAC std_ss [REAL_SUM_IMAGE_DISJOINT_UNION, FINITE_DIFF]
 >> `FINITE (m_space m0 DIFF a0)` by RW_TAC std_ss [FINITE_DIFF]
 >> ONCE_REWRITE_TAC [(UNDISCH o Q.SPEC `(m_space m0 DIFF a0)`) REAL_SUM_IMAGE_IN_IF]
 >> `(\x. (if x IN m_space m0 DIFF a0 then
              (\s0. measure m1 (PREIMAGE (\s1. (s0,s1)) (a0 CROSS a1)) * measure m0 {s0}) x
           else 0)) =
     (\x. 0)`
        by (RW_TAC std_ss [FUN_EQ_THM, IN_DIFF]
            >> RW_TAC std_ss []
            >> `PREIMAGE (\s1. (x,s1)) (a0 CROSS a1) = {}`
                by (ONCE_REWRITE_TAC [EXTENSION]
                    >> RW_TAC std_ss [NOT_IN_EMPTY, IN_PREIMAGE, IN_CROSS])
            >> RW_TAC real_ss [MEASURE_EMPTY])
 >> RW_TAC real_ss [REAL_SUM_IMAGE_0]
 >> ONCE_REWRITE_TAC [(UNDISCH o Q.SPEC `a0`) REAL_SUM_IMAGE_IN_IF]
 >> `(\x. (if x IN a0 then (\s0. measure m1 (PREIMAGE (\s1. (s0,s1)) (a0 CROSS a1)) *
              measure m0 {s0}) x else 0)) =
     (\x. if x IN a0 then (\s0. measure m1 a1 * measure m0 {s0}) x else 0)`
        by (RW_TAC std_ss [FUN_EQ_THM] >> RW_TAC std_ss []
            >> `PREIMAGE (\s1. (x,s1)) (a0 CROSS a1) = a1`
                by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_PREIMAGE, IN_CROSS])
            >> RW_TAC std_ss [])
 >> POP_ORW >> ASM_SIMP_TAC std_ss [GSYM REAL_SUM_IMAGE_IN_IF]
 >> RW_TAC std_ss [REAL_SUM_IMAGE_CMUL]
 >> Suff `SIGMA (\x. measure m0 {x}) a0 = measure m0 a0`
 >- RW_TAC real_ss [REAL_MUL_COMM]
 >> MATCH_MP_TAC (GSYM MEASURE_EXTREAL_SUM_IMAGE)
 >> METIS_TAC [IN_SING, IN_POW, SUBSET_DEF]);

val measure_space_finite_prod_measure_POW1 = store_thm
  ("measure_space_finite_prod_measure_POW1",
  ``!m0 m1. measure_space m0 /\ measure_space m1 /\
            FINITE (m_space m0) /\ FINITE (m_space m1) /\
           (POW (m_space m0) = measurable_sets m0) /\
           (POW (m_space m1) = measurable_sets m1) ==>
            measure_space (prod_measure_space m0 m1)``,
  rpt STRIP_TAC
  >> RW_TAC std_ss [prod_measure_space_def]
  >> `(m_space m0 CROSS m_space m1,
       subsets (sigma (m_space m0 CROSS m_space m1)
                      (prod_sets (measurable_sets m0) (measurable_sets m1))),
       prod_measure m0 m1) =
      (space (sigma (m_space m0 CROSS m_space m1)
            (prod_sets (measurable_sets m0) (measurable_sets m1))),
        subsets (sigma (m_space m0 CROSS m_space m1)
                       (prod_sets (measurable_sets m0) (measurable_sets m1))),
        prod_measure m0 m1)`
        by RW_TAC std_ss [sigma_def, space_def]
  >> POP_ORW
  >> MATCH_MP_TAC finite_additivity_sufficient_for_finite_spaces
  >> `sigma_algebra (sigma (m_space m0 CROSS m_space m1)
                     (prod_sets (measurable_sets m0) (measurable_sets m1)))`
     by (MATCH_MP_TAC SIGMA_ALGEBRA_SIGMA
         >> RW_TAC std_ss [subset_class_def, prod_sets_def, GSPECIFICATION, IN_CROSS]
         >> (MP_TAC o Q.ISPEC `(x' :('a -> bool) # ('b -> bool))`) pair_CASES
         >> RW_TAC std_ss [] >> FULL_SIMP_TAC std_ss [PAIR_EQ]
         >> RW_TAC std_ss [SUBSET_DEF, IN_CROSS]
         >> (MP_TAC o Q.ISPEC `(x :('a # 'b))`) pair_CASES
         >> RW_TAC std_ss []
         >> FULL_SIMP_TAC std_ss [FST, SND]
         >> METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE, SUBSET_DEF])
  >> RW_TAC std_ss [m_space_def, SPACE_SIGMA, FINITE_CROSS, measurable_sets_def, SIGMA_REDUCE]
  >- (RW_TAC std_ss [positive_def, measure_def, measurable_sets_def]
      >- (`{} = {} CROSS {}` by RW_TAC std_ss [CROSS_EMPTY]
          >> POP_ORW
          >> METIS_TAC [finite_POW_prod_measure_reduce,
                         measure_space_def, SIGMA_ALGEBRA, subsets_def, space_def,
                         MEASURE_EMPTY, REAL_MUL_LZERO])
      >> `!x. (PREIMAGE (\s1. (x,s1)) s) SUBSET m_space m1`
        by (RW_TAC std_ss [IN_PREIMAGE, SUBSET_DEF]
            >> FULL_SIMP_TAC std_ss [sigma_def, subsets_def, IN_BIGINTER, GSPECIFICATION]
            >> Q.PAT_X_ASSUM `!s'. P s' ==> s IN s'`
                (MP_TAC o Q.SPEC `POW (m_space m0 CROSS m_space m1)`)
            >> SIMP_TAC std_ss [POW_SIGMA_ALGEBRA]
            >> `prod_sets (measurable_sets m0) (measurable_sets m1) SUBSET
                POW (m_space m0 CROSS m_space m1)`
                by (RW_TAC std_ss [SUBSET_DEF, IN_POW, IN_CROSS, prod_sets_def, GSPECIFICATION]
                    >> (MP_TAC o Q.ISPEC `(x''' :('a -> bool) # ('b -> bool))`) pair_CASES
                    >> RW_TAC std_ss [] >> FULL_SIMP_TAC std_ss [PAIR_EQ]
                    >> `x'''' IN q CROSS r` by RW_TAC std_ss []
                    >> FULL_SIMP_TAC std_ss [IN_CROSS]
                    >> METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE, SUBSET_DEF, IN_POW])
            >> ASM_SIMP_TAC std_ss []
            >> RW_TAC std_ss [IN_POW, SUBSET_DEF, IN_CROSS]
            >> METIS_TAC [SND])
      >> FULL_SIMP_TAC std_ss [prod_measure_def, finite_space_POW_integral_reduce, real_normal,
                               extreal_not_infty, extreal_mul_def, EXTREAL_SUM_IMAGE_NORMAL]
      >> MATCH_MP_TAC REAL_SUM_IMAGE_POS
      >> RW_TAC std_ss [] >> MATCH_MP_TAC REAL_LE_MUL
      >> FULL_SIMP_TAC std_ss [measure_space_def, positive_def]
      >> METIS_TAC [IN_POW, IN_SING, SUBSET_DEF])
  >> RW_TAC std_ss [additive_def, measure_def, measurable_sets_def]
  >> FULL_SIMP_TAC std_ss [prod_measure_def, finite_space_POW_integral_reduce, extreal_not_infty,
                           extreal_mul_def, EXTREAL_SUM_IMAGE_NORMAL, real_normal,
                           GSYM REAL_SUM_IMAGE_ADD, GSYM REAL_ADD_RDISTRIB]
  >> MATCH_MP_TAC REAL_SUM_IMAGE_EQ
  >> RW_TAC std_ss []
  >> Suff `measure m1 (PREIMAGE (\s1. (x,s1)) (s UNION t)) =
           measure m1 (PREIMAGE (\s1. (x,s1)) s) + measure m1 (PREIMAGE (\s1. (x,s1)) t)`
  >- RW_TAC std_ss []
  >> MATCH_MP_TAC MEASURE_ADDITIVE
  >> CONJ_TAC >- RW_TAC std_ss []
  >> CONJ_TAC
  >- (Suff `PREIMAGE (\s1. (x,s1)) s SUBSET (m_space m1)`
      >- METIS_TAC [IN_POW]
      >> RW_TAC std_ss [IN_PREIMAGE, SUBSET_DEF]
      >> FULL_SIMP_TAC std_ss [sigma_def, subsets_def, IN_BIGINTER, GSPECIFICATION]
      >> Q.PAT_X_ASSUM `!s'. P s' ==> s IN s'`
        (MP_TAC o Q.SPEC `POW (m_space m0 CROSS m_space m1)`)
      >> SIMP_TAC std_ss [POW_SIGMA_ALGEBRA]
      >> `prod_sets (measurable_sets m0) (measurable_sets m1) SUBSET
            POW (m_space m0 CROSS m_space m1)`
           by (RW_TAC std_ss [SUBSET_DEF, IN_POW, IN_CROSS, prod_sets_def, GSPECIFICATION]
               >> (MP_TAC o Q.ISPEC `(x''' :('a -> bool) # ('b -> bool))`) pair_CASES
               >> RW_TAC std_ss [] >> FULL_SIMP_TAC std_ss [PAIR_EQ]
               >> `x'''' IN q CROSS r` by RW_TAC std_ss []
               >> FULL_SIMP_TAC std_ss [IN_CROSS]
               >> METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE, SUBSET_DEF, IN_POW])
       >> ASM_SIMP_TAC std_ss []
       >> RW_TAC std_ss [IN_POW, SUBSET_DEF, IN_CROSS]
       >> METIS_TAC [SND])
  >> `prod_sets (measurable_sets m0) (measurable_sets m1) SUBSET
         POW (m_space m0 CROSS m_space m1)`
      by (RW_TAC std_ss [SUBSET_DEF, IN_POW, IN_CROSS, prod_sets_def, GSPECIFICATION]
          >> Cases_on `x''`
          >> FULL_SIMP_TAC std_ss []
          >> METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE, SUBSET_DEF, IN_POW,IN_CROSS])
  >> `!x. (PREIMAGE (\s1. (x,s1)) s) SUBSET m_space m1`
        by (RW_TAC std_ss [IN_PREIMAGE, SUBSET_DEF]
            >> FULL_SIMP_TAC std_ss [sigma_def, subsets_def, IN_BIGINTER, GSPECIFICATION]
            >> Q.PAT_X_ASSUM `!s'. P s' ==> s IN s'`
                (MP_TAC o Q.SPEC `POW (m_space m0 CROSS m_space m1)`)
            >> SIMP_TAC std_ss [POW_SIGMA_ALGEBRA]
            >> `prod_sets (measurable_sets m0) (measurable_sets m1) SUBSET
                POW (m_space m0 CROSS m_space m1)`
                by (RW_TAC std_ss [SUBSET_DEF, IN_POW, IN_CROSS, prod_sets_def, GSPECIFICATION]
                    >> (MP_TAC o Q.ISPEC `(x''' :('a -> bool) # ('b -> bool))`) pair_CASES
                    >> RW_TAC std_ss [] >> FULL_SIMP_TAC std_ss [PAIR_EQ]
                    >> `x'''' IN q CROSS r` by RW_TAC std_ss []
                    >> FULL_SIMP_TAC std_ss [IN_CROSS]
                    >> METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE, SUBSET_DEF, IN_POW])
            >> ASM_SIMP_TAC std_ss []
            >> RW_TAC std_ss [IN_POW, SUBSET_DEF, IN_CROSS]
            >> METIS_TAC [SND])
  >> `!x. (PREIMAGE (\s1. (x,s1)) t) SUBSET m_space m1`
        by (RW_TAC std_ss [IN_PREIMAGE, SUBSET_DEF]
            >> FULL_SIMP_TAC std_ss [sigma_def, subsets_def, IN_BIGINTER, GSPECIFICATION]
            >> Q.PAT_X_ASSUM `!s'. P s' ==> t IN s'`
                (MP_TAC o Q.SPEC `POW (m_space m0 CROSS m_space m1)`)
            >> SIMP_TAC std_ss [POW_SIGMA_ALGEBRA]
            >> `prod_sets (measurable_sets m0) (measurable_sets m1) SUBSET
                POW (m_space m0 CROSS m_space m1)`
                by (RW_TAC std_ss [SUBSET_DEF, IN_POW, IN_CROSS, prod_sets_def, GSPECIFICATION]
                    >> (MP_TAC o Q.ISPEC `(x''' :('a -> bool) # ('b -> bool))`) pair_CASES
                    >> RW_TAC std_ss [] >> FULL_SIMP_TAC std_ss [PAIR_EQ]
                    >> `x'''' IN q CROSS r` by RW_TAC std_ss []
                    >> FULL_SIMP_TAC std_ss [IN_CROSS]
                    >> METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE, SUBSET_DEF, IN_POW])
            >> ASM_SIMP_TAC std_ss []
            >> RW_TAC std_ss [IN_POW, SUBSET_DEF, IN_CROSS]
            >> METIS_TAC [SND])
  >> `(s UNION t) IN subsets (sigma (m_space m0 CROSS m_space m1)
                                    (prod_sets (measurable_sets m0) (measurable_sets m1)))`
          by METIS_TAC [ALGEBRA_UNION,SIGMA_ALGEBRA_SIGMA,sigma_algebra_def]
  >> `!x. (PREIMAGE (\s1. (x,s1)) (s UNION t)) SUBSET m_space m1`
        by (RW_TAC std_ss [IN_PREIMAGE, SUBSET_DEF]
            >> FULL_SIMP_TAC std_ss [sigma_def, subsets_def, IN_BIGINTER, GSPECIFICATION]
            >> Q.PAT_X_ASSUM `!s'. P s' ==> (s UNION t) IN s'`
                (MP_TAC o Q.SPEC `POW (m_space m0 CROSS m_space m1)`)
            >> SIMP_TAC std_ss [POW_SIGMA_ALGEBRA]
            >> `prod_sets (measurable_sets m0) (measurable_sets m1) SUBSET
                POW (m_space m0 CROSS m_space m1)`
                by (RW_TAC std_ss [SUBSET_DEF, IN_POW, IN_CROSS, prod_sets_def, GSPECIFICATION]
                    >> (MP_TAC o Q.ISPEC `(x''' :('a -> bool) # ('b -> bool))`) pair_CASES
                    >> RW_TAC std_ss [] >> FULL_SIMP_TAC std_ss [PAIR_EQ]
                    >> `x'''' IN q CROSS r` by RW_TAC std_ss []
                    >> FULL_SIMP_TAC std_ss [IN_CROSS]
                    >> METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE, SUBSET_DEF, IN_POW])
            >> ASM_SIMP_TAC std_ss []
            >> RW_TAC std_ss [IN_POW, SUBSET_DEF, IN_CROSS]
            >> METIS_TAC [SND])
  >> CONJ_TAC >- METIS_TAC [IN_POW]
  >> CONJ_TAC
  >- (RW_TAC std_ss [EXTENSION,IN_DISJOINT,IN_PREIMAGE]
      >> SPOSE_NOT_THEN ASSUME_TAC
      >> METIS_TAC [DISJOINT_DEF, NOT_IN_EMPTY, IN_INTER, EXTENSION])
  >> RW_TAC std_ss [EXTENSION,IN_PREIMAGE,IN_UNION]);

val measure_space_finite_prod_measure_POW2 = store_thm
  ("measure_space_finite_prod_measure_POW2",
   ``!m0 m1. measure_space m0 /\ measure_space m1 /\
             FINITE (m_space m0) /\ FINITE (m_space m1) /\
             (POW (m_space m0) = measurable_sets m0) /\
             (POW (m_space m1) = measurable_sets m1) ==>
        measure_space (m_space m0 CROSS m_space m1,
                       POW (m_space m0 CROSS m_space m1),
                       prod_measure m0 m1)``,
  rpt STRIP_TAC
  >> `(m_space m0 CROSS m_space m1, POW (m_space m0 CROSS m_space m1), prod_measure m0 m1) =
      (space (m_space m0 CROSS m_space m1, POW (m_space m0 CROSS m_space m1)),
         subsets (m_space m0 CROSS m_space m1, POW (m_space m0 CROSS m_space m1)),
                          prod_measure m0 m1)`
        by RW_TAC std_ss [space_def, subsets_def]
  >> POP_ORW
  >> MATCH_MP_TAC finite_additivity_sufficient_for_finite_spaces
  >> RW_TAC std_ss [POW_SIGMA_ALGEBRA, space_def, FINITE_CROSS, subsets_def]
  >- (RW_TAC std_ss [positive_def, measure_def, measurable_sets_def]
      >- (`{} = {} CROSS {}` by RW_TAC std_ss [CROSS_EMPTY]
          >> POP_ORW
          >> METIS_TAC [finite_POW_prod_measure_reduce,
                        measure_space_def, SIGMA_ALGEBRA, subsets_def, space_def,
                        MEASURE_EMPTY, REAL_MUL_RZERO])
      >> `!x. (PREIMAGE (\s1. (x,s1)) s) SUBSET m_space m1`
        by (RW_TAC std_ss [IN_PREIMAGE, SUBSET_DEF]
            >> FULL_SIMP_TAC std_ss [IN_POW, SUBSET_DEF, IN_CROSS]
            >> METIS_TAC [SND])
      >> FULL_SIMP_TAC std_ss [prod_measure_def, finite_space_POW_integral_reduce,
                               extreal_not_infty, extreal_mul_def, EXTREAL_SUM_IMAGE_NORMAL,
                               real_normal]
      >> MATCH_MP_TAC REAL_SUM_IMAGE_POS
      >> RW_TAC std_ss [] >> MATCH_MP_TAC REAL_LE_MUL
      >> FULL_SIMP_TAC std_ss [measure_space_def, positive_def]
      >> METIS_TAC [IN_POW, IN_SING, SUBSET_DEF])
  >> RW_TAC std_ss [additive_def, measure_def, measurable_sets_def]
  >> `!x. (PREIMAGE (\s1. (x,s1)) s) SUBSET m_space m1`
        by (RW_TAC std_ss [IN_PREIMAGE, SUBSET_DEF]
            >> FULL_SIMP_TAC std_ss [IN_POW, SUBSET_DEF, IN_CROSS]
            >> METIS_TAC [SND])
  >> `!x. (PREIMAGE (\s1. (x,s1)) t) SUBSET m_space m1`
        by (RW_TAC std_ss [IN_PREIMAGE, SUBSET_DEF]
            >> FULL_SIMP_TAC std_ss [IN_POW, SUBSET_DEF, IN_CROSS]
            >> METIS_TAC [SND])
  >> `(s UNION t) IN POW (m_space m0 CROSS m_space m1)` by METIS_TAC [IN_POW,UNION_SUBSET]
  >> `!x. (PREIMAGE (\s1. (x,s1)) (s UNION t)) SUBSET m_space m1`
        by (RW_TAC std_ss [IN_PREIMAGE, SUBSET_DEF]
            >> FULL_SIMP_TAC std_ss [IN_POW, SUBSET_DEF, IN_CROSS]
            >> METIS_TAC [SND])
  >> FULL_SIMP_TAC std_ss [prod_measure_def, finite_space_POW_integral_reduce, extreal_not_infty,
                           extreal_mul_def, EXTREAL_SUM_IMAGE_NORMAL, real_normal,
                           GSYM REAL_SUM_IMAGE_ADD]
  >> MATCH_MP_TAC REAL_SUM_IMAGE_EQ
  >> RW_TAC std_ss [FUN_EQ_THM, GSYM REAL_ADD_RDISTRIB]
  >> Suff `measure m1 (PREIMAGE (\s1. (x,s1)) (s UNION t)) =
          (measure m1 (PREIMAGE (\s1. (x,s1)) s) + measure m1 (PREIMAGE (\s1. (x,s1)) t))`
  >- RW_TAC std_ss []
  >> MATCH_MP_TAC MEASURE_ADDITIVE
  >> Q.PAT_X_ASSUM `POW (m_space m1) = measurable_sets m1` (MP_TAC o GSYM)
  >> Q.PAT_X_ASSUM `POW (m_space m0) = measurable_sets m0` (MP_TAC o GSYM)
  >> FULL_SIMP_TAC std_ss [IN_POW, SUBSET_DEF, IN_PREIMAGE, IN_CROSS, IN_DISJOINT]
  >> RW_TAC std_ss []
  >| [ METIS_TAC [SND],
       METIS_TAC [SND],
       ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_UNION, IN_PREIMAGE] ]);

val finite_prod_measure_space_POW = store_thm
  ("finite_prod_measure_space_POW",
  ``!s1 s2 u v. FINITE s1 /\ FINITE s2  ==>
          (prod_measure_space (s1, POW s1, u) (s2, POW s2, v) =
          (s1 CROSS s2, POW (s1 CROSS s2), prod_measure (s1, POW s1, u) (s2, POW s2, v)))``,
  RW_TAC std_ss [prod_measure_space_def, m_space_def, subsets_def, EXTENSION, subsets_def,
                 sigma_def, prod_sets_def, IN_POW, IN_BIGINTER, measurable_sets_def, SUBSET_DEF,
                 IN_CROSS, GSPECIFICATION]
  >> RW_TAC std_ss [GSYM EXTENSION]
  >> EQ_TAC
  >- (RW_TAC std_ss [] \\ (* 2 sub-goals here, same tacticals *)
      (Q.PAT_X_ASSUM `!s. P ==> x IN s` (MP_TAC o Q.SPEC `POW (s1 CROSS s2)`)
       >> RW_TAC std_ss [IN_POW, SUBSET_DEF, IN_CROSS, POW_SIGMA_ALGEBRA]
       >> Suff `(!x''. (?x'. (x'',T) = (\(s,t). (s CROSS t,
                              (!x. x IN s ==> x IN s1) /\ !x. x IN t ==> x IN s2))
                        x') ==> !x. x IN x'' ==> FST x IN s1 /\ SND x IN s2)` >- METIS_TAC []
        >> RW_TAC std_ss []
        >> Cases_on `x'''`
        >> FULL_SIMP_TAC std_ss []
        >> METIS_TAC [IN_CROSS] ))
  >> RW_TAC std_ss []
  >> `x = BIGUNION (IMAGE (\a. {a}) x)`
    by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_BIGUNION_IMAGE, IN_SING])
  >> POP_ORW
  >> FULL_SIMP_TAC std_ss [SIGMA_ALGEBRA, subsets_def]
  >> POP_ASSUM MATCH_MP_TAC
  >> CONJ_TAC
  >- (MATCH_MP_TAC finite_countable >> MATCH_MP_TAC IMAGE_FINITE
      >> (MP_TAC o Q.ISPEC `(s1 :'a -> bool) CROSS (s2 :'b -> bool)`) SUBSET_FINITE
      >> RW_TAC std_ss [FINITE_CROSS]
      >> POP_ASSUM MATCH_MP_TAC
      >> METIS_TAC [SUBSET_DEF, IN_CROSS])
  >> RW_TAC std_ss [SUBSET_DEF, IN_IMAGE, IN_SING]
  >> Q.PAT_X_ASSUM `!x. Q ==> x IN s` MATCH_MP_TAC
  >> Q.EXISTS_TAC `({FST a}, {SND a})` >> RW_TAC std_ss [PAIR_EQ, IN_SING]
  >> ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_CROSS, IN_SING]
  >> METIS_TAC [PAIR_EQ, PAIR, FST, SND]);

val finite_POW_prod_measure_reduce3 = store_thm
  ("finite_POW_prod_measure_reduce3",
   ``!m0 m1 m2. measure_space m0 /\ measure_space m1 /\ measure_space m2 /\
                FINITE (m_space m0) /\ FINITE (m_space m1) /\ FINITE (m_space m2) /\
                (POW (m_space m0) = measurable_sets m0) /\
                (POW (m_space m1) = measurable_sets m1) /\
                (POW (m_space m2) = measurable_sets m2) ==>
             (!a0 a1 a2. a0 IN measurable_sets m0 /\
                         a1 IN measurable_sets m1 /\
                         a2 IN measurable_sets m2
             ==> ((prod_measure3 m0 m1 m2) (a0 CROSS (a1 CROSS a2)) =
                  measure m0 a0 * measure m1 a1 * measure m2 a2))``,
  RW_TAC std_ss [prod_measure3_def, measure_def]
  >> `measure_space (prod_measure_space m1 m2)`
      by METIS_TAC [measure_space_finite_prod_measure_POW1]
  >> `FINITE (m_space (prod_measure_space m1 m2))`
      by METIS_TAC [prod_measure_space_def,m_space_def,FINITE_CROSS]
  >> `m_space (prod_measure_space m1 m2) = m_space m1 CROSS (m_space m2)`
         by RW_TAC std_ss [prod_measure_space_def,m_space_def]
  >> `measurable_sets (prod_measure_space m1 m2) =
      POW (m_space m1 CROSS (m_space m2))`
        by (`m1 = (m_space m1,measurable_sets m1,measure m1)`
             by RW_TAC std_ss [MEASURE_SPACE_REDUCE]
            >> `m2 = (m_space m2, measurable_sets m2, measure m2)`
             by RW_TAC std_ss [MEASURE_SPACE_REDUCE]
            >> METIS_TAC [finite_prod_measure_space_POW, m_space_def, measurable_sets_def])
  >> `a1 CROSS a2 IN measurable_sets (prod_measure_space m1 m2)`
        by (RW_TAC std_ss [IN_POW,SUBSET_DEF,IN_CROSS]
            >> METIS_TAC [MEASURE_SPACE_SUBSET_MSPACE,SUBSET_DEF])
  >> RW_TAC std_ss [finite_POW_prod_measure_reduce]
  >> RW_TAC std_ss [prod_measure_space_def, measure_def]
  >> METIS_TAC [finite_POW_prod_measure_reduce, REAL_MUL_ASSOC]);

val measure_space_finite_prod_measure_POW3 = store_thm
  ("measure_space_finite_prod_measure_POW3",
  ``!m0 m1 m2. measure_space m0 /\ measure_space m1 /\ measure_space m2 /\
               FINITE (m_space m0) /\ FINITE (m_space m1) /\ FINITE (m_space m2) /\
              (POW (m_space m0) = measurable_sets m0) /\
              (POW (m_space m1) = measurable_sets m1) /\
              (POW (m_space m2) = measurable_sets m2) ==>
        measure_space (m_space m0 CROSS (m_space m1 CROSS m_space m2),
                       POW (m_space m0 CROSS (m_space m1 CROSS m_space m2)),
                       prod_measure3 m0 m1 m2)``,
   rpt STRIP_TAC
   >> `(m_space m0 CROSS (m_space m1 CROSS m_space m2),
        POW (m_space m0 CROSS (m_space m1 CROSS m_space m2)),
        prod_measure3 m0 m1 m2) =
        (space (m_space m0 CROSS (m_space m1 CROSS m_space m2),
         POW (m_space m0 CROSS (m_space m1 CROSS m_space m2))),
         subsets (m_space m0 CROSS (m_space m1 CROSS m_space m2),
                  POW (m_space m0 CROSS (m_space m1 CROSS m_space m2))), prod_measure3 m0 m1 m2)`
        by RW_TAC std_ss [space_def, subsets_def]
   >> POP_ORW
   >> `measure_space (prod_measure_space m1 m2)`
       by METIS_TAC [measure_space_finite_prod_measure_POW1]
   >> `prod_measure_space m1 m2 =
       (m_space m1 CROSS m_space m2, POW (m_space m1 CROSS m_space m2), prod_measure m1 m2)`
           by METIS_TAC [MEASURE_SPACE_REDUCE,finite_prod_measure_space_POW]
   >> `!x s. s IN POW (m_space m0 CROSS (m_space m1 CROSS m_space m2)) ==>
           (PREIMAGE (\s1. (x,s1)) s) SUBSET (m_space m1 CROSS (m_space m2))`
                by (RW_TAC std_ss [IN_PREIMAGE, SUBSET_DEF]
                    >> FULL_SIMP_TAC std_ss [IN_POW, SUBSET_DEF, IN_CROSS]
                    >> METIS_TAC [SND])
  >> MATCH_MP_TAC finite_additivity_sufficient_for_finite_spaces
  >> RW_TAC std_ss [POW_SIGMA_ALGEBRA, space_def, FINITE_CROSS, subsets_def]
  >- (RW_TAC std_ss [positive_def, measure_def, measurable_sets_def]
      >- (`{} = {} CROSS ({} CROSS {})` by RW_TAC std_ss [CROSS_EMPTY]
          >> POP_ORW
          >> RW_TAC std_ss [finite_POW_prod_measure_reduce3, MEASURE_SPACE_EMPTY_MEASURABLE,
                            MEASURE_EMPTY, REAL_MUL_LZERO])
      >> RW_TAC std_ss [Once prod_measure_def,prod_measure3_def, finite_space_POW_integral_reduce,
                        extreal_not_infty, extreal_mul_def, EXTREAL_SUM_IMAGE_NORMAL, real_normal]
      >> MATCH_MP_TAC REAL_SUM_IMAGE_POS
      >> RW_TAC std_ss []
      >> MATCH_MP_TAC REAL_LE_MUL
      >> Reverse CONJ_TAC
      >- METIS_TAC [IN_POW, IN_SING, SUBSET_DEF, MEASURE_SPACE_POSITIVE, positive_def]
      >> RW_TAC std_ss [measure_def,prod_measure_def, finite_space_POW_integral_reduce,
                        extreal_not_infty, EXTREAL_SUM_IMAGE_NORMAL, extreal_mul_def, real_normal]
      >> MATCH_MP_TAC REAL_SUM_IMAGE_POS
      >> RW_TAC std_ss []
      >> MATCH_MP_TAC REAL_LE_MUL
      >> Reverse CONJ_TAC
      >- METIS_TAC [IN_POW, IN_SING, SUBSET_DEF, MEASURE_SPACE_POSITIVE, positive_def]
      >> Suff `(PREIMAGE (\s1. (x',s1)) (PREIMAGE (\s1. (x,s1)) s)) SUBSET (m_space m2)`
      >- METIS_TAC [IN_POW, IN_SING, SUBSET_DEF, MEASURE_SPACE_POSITIVE, positive_def]
      >> RW_TAC std_ss [SUBSET_DEF,IN_PREIMAGE]
      >> METIS_TAC [IN_CROSS,IN_POW,SUBSET_DEF, FST, SND])
  >> RW_TAC std_ss [additive_def, measure_def, measurable_sets_def]
  >> RW_TAC std_ss [prod_measure3_def]
  >> ONCE_REWRITE_TAC [prod_measure_def]
  >> RW_TAC std_ss [measure_def]
  >> RW_TAC std_ss [finite_space_POW_integral_reduce, extreal_not_infty, EXTREAL_SUM_IMAGE_NORMAL,
                    real_normal, extreal_mul_def, GSYM REAL_SUM_IMAGE_ADD]
  >> MATCH_MP_TAC REAL_SUM_IMAGE_EQ
  >> RW_TAC std_ss [GSYM REAL_ADD_RDISTRIB]
  >> Suff `prod_measure m1 m2 (PREIMAGE (\s1. (x,s1)) (s UNION t)) =
           (prod_measure m1 m2 (PREIMAGE (\s1. (x,s1)) s) +
            prod_measure m1 m2 (PREIMAGE (\s1. (x,s1)) t))`
  >- RW_TAC std_ss []
  >> RW_TAC std_ss [prod_measure_def, finite_space_POW_integral_reduce, extreal_not_infty,
                    EXTREAL_SUM_IMAGE_NORMAL, real_normal, extreal_mul_def,
                    GSYM REAL_SUM_IMAGE_ADD]
  >> MATCH_MP_TAC REAL_SUM_IMAGE_EQ
  >> RW_TAC std_ss [GSYM REAL_ADD_RDISTRIB]
  >> Suff `measure m2 (PREIMAGE (\s1. (x',s1)) (PREIMAGE (\s1. (x,s1)) (s UNION t))) =
           measure m2 (PREIMAGE (\s1. (x',s1)) (PREIMAGE (\s1. (x,s1)) s)) +
           measure m2 (PREIMAGE (\s1. (x',s1)) (PREIMAGE (\s1. (x,s1)) t))`
  >- RW_TAC std_ss []
  >> MATCH_MP_TAC MEASURE_ADDITIVE
  >> CONJ_TAC >- RW_TAC std_ss []
  >> CONJ_TAC
  >- (Suff `PREIMAGE (\s1. (x',s1)) (PREIMAGE (\s1. (x,s1)) s) SUBSET m_space m2`
      >- METIS_TAC [IN_POW]
      >> RW_TAC std_ss [SUBSET_DEF,IN_PREIMAGE]
      >> METIS_TAC [IN_POW, IN_CROSS, SUBSET_DEF, FST, SND])
  >> CONJ_TAC
  >- (Suff `PREIMAGE (\s1. (x',s1)) (PREIMAGE (\s1. (x,s1)) t) SUBSET m_space m2`
      >- METIS_TAC [IN_POW]
      >> RW_TAC std_ss [SUBSET_DEF,IN_PREIMAGE]
      >> METIS_TAC [IN_POW, IN_CROSS, SUBSET_DEF, FST, SND])
  >> CONJ_TAC
  >- (RW_TAC std_ss [DISJOINT_DEF, EXTENSION, IN_INTER, NOT_IN_EMPTY, IN_PREIMAGE]
      >> METIS_TAC [IN_POW, IN_CROSS, SUBSET_DEF, FST, SND, DISJOINT_DEF, EXTENSION,
                    IN_INTER,NOT_IN_EMPTY])
  >> RW_TAC std_ss [EXTENSION,IN_PREIMAGE,IN_UNION]);

val finite_prod_measure_space_POW3 = store_thm
  ("finite_prod_measure_space_POW3",
  ``!s1 s2 s3 u v w.
         FINITE s1 /\ FINITE s2 /\ FINITE s3 ==>
         (prod_measure_space3 (s1,POW s1,u) (s2,POW s2,v) (s3,POW s3,w) =
          (s1 CROSS (s2 CROSS s3),POW (s1 CROSS (s2 CROSS s3)),
           prod_measure3 (s1,POW s1,u) (s2,POW s2,v) (s3,POW s3,w)))``,
  RW_TAC std_ss [prod_measure_space3_def,m_space_def, subsets_def, EXTENSION, subsets_def,
                sigma_def, prod_sets3_def, IN_POW, IN_BIGINTER, measurable_sets_def, SUBSET_DEF,
                IN_CROSS, GSPECIFICATION]
  >> RW_TAC std_ss [GSYM EXTENSION]
  >> EQ_TAC
  >- (RW_TAC std_ss [] \\ (* 3 sub-goals here, same tacticals *)
      (Q.PAT_X_ASSUM `!s. P ==> x IN s` (MP_TAC o Q.SPEC `POW (s1 CROSS (s2 CROSS s3))`)
       >> RW_TAC std_ss [IN_POW, SUBSET_DEF, IN_CROSS, POW_SIGMA_ALGEBRA]
       >> Suff `(!x''. (?x'. (x'',T) =
               (\(s,t,u'). (s CROSS (t CROSS u'),
               (!x. x IN s ==> x IN s1) /\ (!x. x IN t ==> x IN s2) /\
                !x. x IN u' ==> x IN s3)) x') ==>
                !x. x IN x'' ==> FST x IN s1 /\ FST (SND x) IN s2 /\ SND (SND x) IN s3)`
       >- METIS_TAC []
       >> RW_TAC std_ss []
       >> Cases_on `x'''` >> Cases_on `r`
       >> FULL_SIMP_TAC std_ss []
       >> METIS_TAC [IN_CROSS] ))
  >> RW_TAC std_ss []
  >> `x = BIGUNION (IMAGE (\a. {a}) x)`
    by (ONCE_REWRITE_TAC [EXTENSION]
        >> RW_TAC std_ss [IN_BIGUNION_IMAGE, IN_SING])
  >> POP_ORW
  >> FULL_SIMP_TAC std_ss [SIGMA_ALGEBRA, subsets_def]
  >> POP_ASSUM MATCH_MP_TAC
  >> CONJ_TAC
  >- (MATCH_MP_TAC finite_countable >> MATCH_MP_TAC IMAGE_FINITE
      >> (MP_TAC o
          Q.ISPEC `(s1 :'a -> bool) CROSS ((s2 :'b -> bool) CROSS (s3:'c -> bool))`)
                SUBSET_FINITE
      >> RW_TAC std_ss [FINITE_CROSS]
      >> POP_ASSUM MATCH_MP_TAC
      >> RW_TAC std_ss [SUBSET_DEF, IN_CROSS])
  >> RW_TAC std_ss [SUBSET_DEF, IN_IMAGE, IN_SING]
  >> Q.PAT_X_ASSUM `!x. Q ==> x IN s` MATCH_MP_TAC
  >> Q.EXISTS_TAC `({FST a}, {FST (SND a)}, {SND(SND a)})` >> RW_TAC std_ss [IN_SING]
  >> RW_TAC std_ss [IN_SING,EXTENSION,IN_CROSS,PAIR]
  >> METIS_TAC [PAIR]);
*)

(* ------------------------------------------------------------------------- *)
(*  Convergence theorems and their applications [1, Chapter 9 & 12]         *)
(* ------------------------------------------------------------------------- *)

(* Another convergence theorem, named after P. Fatou, usually called Fatou's lemma,
   named after Pierre Fatou (1878-1929), a French mathematician and astronomer [3].

   This is mainly to prove the validity of the definition of `ext_liminf`. The value
   of any of the integrals may be infinite. (`!n. integrable m (u n)` is not needed)

   We use the more general statements from [6, p.223] involving both liminf/limsup.
   Taking `f = \x. 0`, we get the simple version - Theorem 9.11 of [1, p.78].

val fatou_lemma_liminf = store_thm (* new *)
  ("fatou_lemma_liminf",
  ``!m u f. measure_space m /\
         (!n. u n IN measurable (m_space m,measurable_sets m) Borel) /\
         (!x n. x IN m_space m ==> f x <= u n x) /\ NegInf < integral m f
       ==>
         (\x. liminf (\n. u n x)) IN borel_measurable (m_space m,measurable_sets m) /\
         (integral m (\x. liminf (\n. u n x)) <= liminf (\n. integral m (u n)))``,
    cheat);

(* This is also called Reverse Fatou Lemma, c.f. [1, p. 80] (taking `f = \x. 0`) *)
val fatou_lemma_limsup = store_thm (* new *)
  ("fatou_lemma_limsup",
  ``!m u f. measure_space m /\
         (!n. u n IN measurable (m_space m,measurable_sets m) Borel) /\
         (!x n. x IN m_space m ==> u n x <= f x) /\ integral m f < PosInf
       ==>
         (\x. limsup (\n. u n x)) IN measurable (m_space m,measurable_sets m) Borel /\
         (limsup (\n. integral m (u n)) <= integral m (\x. limsup (\n. u n x)))``,
    cheat);

(* A generalization of Beppo Levi's Theorem 9.6 (lebesgue_monotone_convergence)
   This is Theorem 12.1 (monotone convergence) of [1, p.96].
 *)
val integrable_monotone_convergence_sup = store_thm (* new *)
  ("integrable_monotone_convergence_sup",
  ``!m f u. measure_space m /\
        (!n. u n IN measurable (m_space m, measurable_sets m) Borel) /\
        (!x. x IN m_space m ==> mono_increasing (\n. u n x)) /\
        (!x. x IN m_space m ==> (sup (IMAGE (\n. u n x) UNIV) = f x)) /\
        sup (IMAGE (\n. integral m (u n)) UNIV) < PosInf
      ==>
        integrable m f /\
        (integral m f = sup (IMAGE (\n. integral m (u n)) UNIV))``,
    cheat);

val integrable_monotone_convergence_inf = store_thm (* new *)
  ("integrable_monotone_convergence_inf",
  ``!m f u. measure_space m /\
        (!n. u n IN measurable (m_space m, measurable_sets m) Borel) /\
        (!x. x IN m_space m ==> mono_decreasing (\n. u n x)) /\
        (!x. x IN m_space m ==> (inf (IMAGE (\n. u n x) UNIV) = f x)) /\
        NegInf < inf (IMAGE (\n. integral m (u n)) UNIV)
      ==>
        integrable m f /\
        (integral m f = inf (IMAGE (\n. integral m (u n)) UNIV))``,
    cheat);

(* Lebesgue's dominated convergence (Theorem 12.2 [1, p.97])

  "Lebesgue`s theorem gives merely sufficient - but easily verifiable - conditions
   for the interchange of limits and integrals; the ultimate version for such a result
   with necessary and sufficient conditions will be given in the form of Vitali`s
   convergence theorem."
 *)
val uniformly_bounded_def = Define
   `uniformly_bounded m (u :num -> 'a -> extreal) =
      ?w. w IN measurable (m_space m, measurable_sets m) Borel /\
          integrable m w /\
          (!x. x IN m_space m ==> 0 <= w x) /\
          (AE x::m. !n. abs (u n x) <= w x)`;

val lebesgue_dominated_convergence = store_thm (* new *)
  ("lebesgue_dominated_convergence",
  ``!m w f u. measure_space m /\
        (!n. u n IN measurable (m_space m, measurable_sets m) Borel) /\
        (!n. integrable m (u n)) /\ uniformly_bounded m u /\
        (AE x::m. (\n. real (u n x)) --> real (f x))
      ==>
        (\n. real (integral m (\x. abs (u n x - f x)))) --> 0 /\
        (\n. real (integral m (u n))) --> real (integral m f)``,
    cheat);

(* To be used by Vitali's convergence theorem [1].
  "It follows the universal formulation due to G. A. Hunt [2, p. 33]." [1, p.163] *)
val uniformly_integrable_def = Define
   `uniformly_integrable m (f :num -> 'a -> extreal) =
    !e. 0 < e ==>
        ?w. nonneg w /\ integrable m w /\
            sup {r | ?u n. (u = f n) /\
                           (r = ((abs o u) * m) {x | w x < (abs o u) x})} < e`;
 *)

(* Theorem 22.7 (Vitali) [1, p. 262], which generalizes Lebesgue`s dominated
   convergence theorem (Lebesgue_dominated_convergence).

   named after Giuseppe Vitali (1875-1932), an Italian mathematician [5].

val vitali_uniform_convergence = store_thm (* new *)
  ("vitali_uniform_convergence",
  ``not expressible at this moment``,
    cheat);
 *)

(*** martingaleTheory ***)

(* alternative definition: using generator instead of sigma-algebra *)
val martingale_alt = store_thm
  ("martingale_alt",
  ``!m a u. martingale m a u <=>
            sigma_finite_FMS m a /\ (!n. integrable m (u n)) /\
            ?g. (!n. subset_class (space (g n)) (subsets (g n))) /\
                (!n. a n = sigma (space (g n)) (subsets (g n))) /\
                !n s. s IN (subsets (g n)) ==>
                     (integral m (\x. u (SUC n) x * indicator_fn s x) =
                      integral m (\x. u n x * indicator_fn s x))``,
    RW_TAC std_ss [martingale_def]
 >> EQ_TAC >> RW_TAC std_ss [sigma_finite_FMS_alt]
 >- (Q.EXISTS_TAC `a` \\
     fs [filtered_measure_space_alt, filtration_def, sub_sigma_algebra_def, space_def] \\
     CONJ_TAC >- METIS_TAC [sigma_algebra_def, algebra_def] \\
     GEN_TAC >> METIS_TAC [SIGMA_OF_SIGMA_ALGEBRA])
 >> 
    cheat);

(* for sub- or supermartingle we need, in addition, `g n` is a semiring *)
val sub_martingale_alt = store_thm
  ("sub_martingale_alt",
  ``!m a u. sub_martingale m a u <=>
            sigma_finite_FMS m a /\ (!n. integrable m (u n)) /\
            ?g. (!n. semiring (g n)) /\
                (!n. a n = sigma (space (g n)) (subsets (g n))) /\
                !n s. s IN (subsets (a n)) ==>
                     (integral m (\x. u n x * indicator_fn s x) <=
                      integral m (\x. u (SUC n) x * indicator_fn s x))``,
    RW_TAC std_ss [sub_martingale_def]
 >> EQ_TAC >> RW_TAC std_ss [sigma_finite_FMS_alt]
 >- (Q.EXISTS_TAC `a` \\
     fs [filtered_measure_space_alt, filtration_def, sub_sigma_algebra_def, space_def] \\
     CONJ_TAC
     >- (GEN_TAC >> MATCH_MP_TAC ALGEBRA_IMP_SEMIRING \\
         METIS_TAC [sigma_algebra_def]) \\
     GEN_TAC >> METIS_TAC [SIGMA_OF_SIGMA_ALGEBRA])
 >> 
    cheat);

val super_martingale_alt = store_thm
  ("super_martingale_alt",
  ``!m a u. super_martingale m a u <=>
            sigma_finite_FMS m a /\ (!n. integrable m (u n)) /\
            ?g. (!n. semiring (g n)) /\
                (!n. a n = sigma (space (g n)) (subsets (g n))) /\
                !n s. s IN (subsets (a n)) ==>
                     (integral m (\x. u (SUC n) x * indicator_fn s x) <=
                      integral m (\x. u n x * indicator_fn s x))``,
    RW_TAC std_ss [super_martingale_def]
 >> EQ_TAC >> RW_TAC std_ss [sigma_finite_FMS_alt]
 >- (Q.EXISTS_TAC `a` \\
     fs [filtered_measure_space_alt, filtration_def, sub_sigma_algebra_def, space_def] \\
     CONJ_TAC
     >- (GEN_TAC >> MATCH_MP_TAC ALGEBRA_IMP_SEMIRING \\
         METIS_TAC [sigma_algebra_def]) \\
     GEN_TAC >> METIS_TAC [SIGMA_OF_SIGMA_ALGEBRA])
 >> 
    cheat);

(*** probabilityTheory ***)

(* (pairwise) independence implies uncorrelatedness, provided second moments are
   finite [2, p.108]. (This requires Fibini's theorem.)
val indep_imp_uncorrelated = store_thm
  ("indep_imp_uncorrelated",
  ``!p X Y. finite_second_moments p X /\
            finite_second_moments p Y /\
            indep_rv p X Y Borel Borel ==> uncorrelated p X Y``,
    cheat);
 *)

(* additions in martingaleTheory

Theorem SPACE_SIGMA_FUNCTION :
    !sp A f. space (sigma_function sp A f) = sp
Proof
    RW_TAC std_ss [sigma_function_def, space_def]
QED

Theorem SIGMA_FUNCTION_SUBSET :
    !sp sts A f. subset_class (space A) (subsets A) /\
                 sigma_algebra (sp,sts) /\ f IN (sp -> space A) ==>
                 subsets (sigma_function sp A f) SUBSET sts
Proof
    RW_TAC std_ss [sigma_function_def, SUBSET_DEF, subsets_def,
                   IN_IMAGE, IN_FUNSET]
 >> RW_TAC std_ss [PREIMAGE_def]

QED
 *)

(* The sigma-algebra generated from any A/B-measurable function X is
   a sub-sigma-algebra of A (really?)
Theorem SIGMA_FUNCTION_SUB_SIGMA_ALGEBRA :
    !X A B. X IN measurable A B ==>
            sub_sigma_algebra (sigma_function (space A) B X) A
Proof
    RW_TAC std_ss [IN_MEASURABLE, space_def]
 >> `X IN measurable (sigma (space A) B X) B` by PROVE_TAC [SIGMA_MEASURABLE]
 >> fs [IN_MEASURABLE, sub_sigma_algebra_def, SPACE_SIGMA_FUNCTION]
 >> 
QED
 *)

val _ = export_theory ();
