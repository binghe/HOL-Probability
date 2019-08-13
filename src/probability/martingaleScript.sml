(* ------------------------------------------------------------------------- *)
(* The theory of martingales for sigma-finite measure spaces                 *)
(*                                                                           *)
(* Author: Chun Tian (2019)                                                  *)
(* Fondazione Bruno Kessler and University of Trento, Italy                  *)
(* ------------------------------------------------------------------------- *)

open HolKernel Parse boolLib bossLib;

open pairTheory relationTheory optionTheory prim_recTheory arithmeticTheory
     pred_setTheory combinTheory realTheory realLib seqTheory transcTheory
     real_sigmaTheory;

open hurdUtils util_probTheory extrealTheory sigma_algebraTheory measureTheory
     borelTheory lebesgueTheory;

val _ = new_theory "martingale";

(* "The theory of martingales as we know it now goes back to
    Doob and most of the material of this and the following chapter can be found in
    his seminal monograph [2] from 1953.

    We want to understand martingales as an analysis tool which will be useful
    for the study of L^p- and almost everywhere convergence and, in particular,
    for the further development of measure and integration theory. Our presentation
    differs somewhat from the standard way to introduce martingales - conditional
    expectations will be defined later in Chapter 22 - but the results and their
    proofs are pretty much the usual ones."

  -- Rene L. Schilling, "Measures, Integrals and Martingales" [1]

   "Martingale theory illustrates the history of mathematical probability: the
    basic definitions are inspired by crude notions of gambling, but the theory
    has become a sophisticated tool of modern abstract mathematics, drawing from
    and contributing to other field."

  -- J. L. Doob, "What is a Martingale?" [3] *)

(* ------------------------------------------------------------------------- *)
(*  Basic version of martingales (Chapter 17 of [1])                         *)
(* ------------------------------------------------------------------------- *)

val sub_sigma_algebra_def = Define
   `sub_sigma_algebra a b <=> sigma_algebra a /\ sigma_algebra b /\
                             (space a = space b) /\ (subsets a) SUBSET (subsets b)`;

(* sub_sigma_algebra is a partial-order between sigma-algebras *)
val SUB_SIGMA_ALGEBRA_REFL = store_thm
  ("SUB_SIGMA_ALGEBRA_REFL",
  ``!a. sigma_algebra a ==> sub_sigma_algebra a a``,
    RW_TAC std_ss [sub_sigma_algebra_def, SUBSET_REFL]);

val SUB_SIGMA_ALGEBRA_TRANS = store_thm
  ("SUB_SIGMA_ALGEBRA_TRANS",
  ``!a b c. sub_sigma_algebra a b /\ sub_sigma_algebra b c ==> sub_sigma_algebra a c``,
    RW_TAC std_ss [sub_sigma_algebra_def]
 >> MATCH_MP_TAC SUBSET_TRANS
 >> Q.EXISTS_TAC `subsets b` >> art []);

val SUB_SIGMA_ALGEBRA_ANTISYM = store_thm
  ("SUB_SIGMA_ALGEBRA_ANTISYM",
  ``!a b. sub_sigma_algebra a b /\ sub_sigma_algebra b a ==> (a = b)``,
    RW_TAC std_ss [sub_sigma_algebra_def]
 >> Q.PAT_X_ASSUM `space b = space a` K_TAC
 >> ONCE_REWRITE_TAC [GSYM SPACE]
 >> ASM_REWRITE_TAC [CLOSED_PAIR_EQ]
 >> MATCH_MP_TAC SUBSET_ANTISYM >> art []);

val SUB_SIGMA_ALGEBRA_ORDER = store_thm
  ("SUB_SIGMA_ALGEBRA_ORDER", ``Order sub_sigma_algebra``,
    RW_TAC std_ss [Order, antisymmetric_def, transitive_def]
 >- (MATCH_MP_TAC SUB_SIGMA_ALGEBRA_ANTISYM >> art [])
 >> IMP_RES_TAC SUB_SIGMA_ALGEBRA_TRANS);

val SUB_SIGMA_ALGEBRA_MEASURE_SPACE = store_thm
  ("SUB_SIGMA_ALGEBRA_MEASURE_SPACE",
  ``!m a. measure_space m /\ sub_sigma_algebra a (m_space m,measurable_sets m) ==>
          measure_space (m_space m,subsets a,measure m)``,
    RW_TAC std_ss [sub_sigma_algebra_def, space_def, subsets_def]
 >> MATCH_MP_TAC MEASURE_SPACE_RESTRICTION
 >> Q.EXISTS_TAC `measurable_sets m`
 >> simp [MEASURE_SPACE_REDUCE]
 >> METIS_TAC [SPACE]);

(* `filtration A` is the set of all filtrations of A *)
val filtration_def = Define
   `filtration A (a :num -> 'a algebra) <=>
      (!n. sub_sigma_algebra (a n) A) /\
      (!i j. i <= j ==> subsets (a i) SUBSET subsets (a j))`;

val FILTRATION_BOUNDED = store_thm
  ("FILTRATION_BOUNDED",
  ``!A a. filtration A a ==> !n. sub_sigma_algebra (a n) A``,
    PROVE_TAC [filtration_def]);

val FILTRATION_MONO = store_thm
  ("FILTRATION_MONO",
  ``!A a. filtration A a ==> !i j. i <= j ==> subsets (a i) SUBSET subsets (a j)``,
    PROVE_TAC [filtration_def]);

(* all sigma-algebras in `filtration A` are subset of A *)
val FILTRATION_SUBSETS = store_thm
  ("FILTRATION_SUBSETS",
  ``!A a. filtration A a ==> !n. subsets (a n) SUBSET (subsets A)``,
    RW_TAC std_ss [filtration_def, sub_sigma_algebra_def]);

val FILTRATION = store_thm
  ("FILTRATION",
  ``!A a. filtration A a <=> (!n. sub_sigma_algebra (a n) A) /\
                             (!n. subsets (a n) SUBSET (subsets A)) /\
                             (!i j. i <= j ==> subsets (a i) SUBSET subsets (a j))``,
    rpt GEN_TAC >> EQ_TAC
 >- (DISCH_TAC >> IMP_RES_TAC FILTRATION_SUBSETS >> fs [filtration_def])
 >> RW_TAC std_ss [filtration_def]);

val filtered_measure_space_def = Define
   `filtered_measure_space (sp,sts,m) a <=>
             measure_space (sp,sts,m) /\ filtration (sp,sts) a`;

val filtered_measure_space_alt = store_thm
  ("filtered_measure_space_alt",
  ``!m a. filtered_measure_space m a <=>
          measure_space m /\ filtration (m_space m,measurable_sets m) a``,
    rpt GEN_TAC
 >> Cases_on `m` >> Cases_on `r`
 >> REWRITE_TAC [filtered_measure_space_def, m_space_def, measurable_sets_def]);

(* `sigma_finite_FMS = sigma_finite_filtered_measure_space` *)
val sigma_finite_FMS_def = Define
   `sigma_finite_FMS (sp,sts,m) a <=>
    filtered_measure_space (sp,sts,m) a /\ sigma_finite (sp,subsets (a 0),m)`;

val sigma_finite_FMS_alt = store_thm
  ("sigma_finite_FMS_alt",
  ``!m a. sigma_finite_FMS m a <=>
          filtered_measure_space m a /\ sigma_finite (m_space m,subsets (a 0),measure m)``,
    rpt GEN_TAC
 >> Cases_on `m` >> Cases_on `r`
 >> REWRITE_TAC [sigma_finite_FMS_def, m_space_def, measure_def]);

(* all sub measure spaces of a sigma-finite fms are also sigma-finite *)
val SIGMA_FINITE_FMS_IMP = store_thm
  ("SIGMA_FINITE_FMS_IMP",
  ``!sp sts a m. sigma_finite_FMS (sp,sts,m) a ==> !n. sigma_finite (sp,subsets (a n),m)``,
 (* proof *)
    RW_TAC std_ss [sigma_finite_FMS_def, filtered_measure_space_def, filtration_def]
 >> Know `measure_space (sp,subsets (a 0),m) /\
          measure_space (sp,subsets (a n),m)`
 >- (CONJ_TAC \\ (* 2 subgoals, same tactics *)
     MATCH_MP_TAC
       (REWRITE_RULE [m_space_def, measurable_sets_def, measure_def]
                     (Q.SPEC `(sp,sts,m)` SUB_SIGMA_ALGEBRA_MEASURE_SPACE)) >> art [])
 >> STRIP_TAC
 >> POP_ASSUM (simp o wrap o (MATCH_MP SIGMA_FINITE_ALT))
 >> POP_ASSUM (fs o wrap o (MATCH_MP SIGMA_FINITE_ALT))
 >> Q.EXISTS_TAC `f`
 >> fs [IN_FUNSET, IN_UNIV, measurable_sets_def, m_space_def, measure_def]
 >> `0 <= n` by RW_TAC arith_ss []
 >> METIS_TAC [SUBSET_DEF]);

(* extended definition *)
val SIGMA_FINITE_FMS = store_thm
  ("SIGMA_FINITE_FMS",
  ``!sp sts a m. sigma_finite_FMS (sp,sts,m) a <=>
                 filtered_measure_space (sp,sts,m) a /\
                 !n. sigma_finite (sp,subsets (a n),m)``,
    rpt GEN_TAC >> EQ_TAC
 >- (DISCH_TAC >> IMP_RES_TAC SIGMA_FINITE_FMS_IMP \\
     fs [sigma_finite_FMS_def])
 >> RW_TAC std_ss [sigma_finite_FMS_def]);

(* the smallest sigma-algebra generated by all (a n) *)
val infty_sigma_algebra_def = Define
   `infty_sigma_algebra sp a = sigma sp (BIGUNION (IMAGE (\(i :num). subsets (a i)) UNIV))`;

val INFTY_SIGMA_ALGEBRA_BOUNDED = store_thm
  ("INFTY_SIGMA_ALGEBRA_BOUNDED",
  ``!A a. filtration A a ==>
          sub_sigma_algebra (infty_sigma_algebra (space A) a) A``,
    RW_TAC std_ss [sub_sigma_algebra_def, FILTRATION, infty_sigma_algebra_def]
 >- (MATCH_MP_TAC SIGMA_ALGEBRA_SIGMA \\
     RW_TAC std_ss [subset_class_def, IN_BIGUNION_IMAGE, IN_UNIV] \\
    `x IN subsets A` by PROVE_TAC [SUBSET_DEF] \\
     METIS_TAC [sigma_algebra_def, algebra_def, subset_class_def, space_def, subsets_def])
 >- REWRITE_TAC [SPACE_SIGMA]
 >> MATCH_MP_TAC SIGMA_SUBSET >> art []
 >> RW_TAC std_ss [SUBSET_DEF, IN_BIGUNION_IMAGE, IN_UNIV]
 >> PROVE_TAC [SUBSET_DEF]);

val INFTY_SIGMA_ALGEBRA_MAXIMAL = store_thm
  ("INFTY_SIGMA_ALGEBRA_MAXIMAL",
  ``!A a. filtration A a ==> !n. sub_sigma_algebra (a n) (infty_sigma_algebra (space A) a)``,
 (* proof *)
    RW_TAC std_ss [sub_sigma_algebra_def, FILTRATION, infty_sigma_algebra_def]
 >- (MATCH_MP_TAC SIGMA_ALGEBRA_SIGMA \\
     RW_TAC std_ss [subset_class_def, IN_BIGUNION_IMAGE, IN_UNIV] \\
    `x IN subsets A` by PROVE_TAC [SUBSET_DEF] \\
     METIS_TAC [sigma_algebra_def, algebra_def, subset_class_def, space_def, subsets_def])
 >- REWRITE_TAC [SPACE_SIGMA]
 >> MATCH_MP_TAC SUBSET_TRANS
 >> Q.EXISTS_TAC `BIGUNION (IMAGE (\i. subsets (a i)) univ(:num))`
 >> CONJ_TAC
 >- (RW_TAC std_ss [SUBSET_DEF, IN_BIGUNION_IMAGE, IN_UNIV] \\
     Q.EXISTS_TAC `n` >> art [])
 >> REWRITE_TAC [SIGMA_SUBSET_SUBSETS]);

(* `prob_martingale` will be the probability version of `martingale` *)
val martingale_def = Define
   `martingale m a u <=>
      sigma_finite_FMS m a /\ (!n. integrable m (u n)) /\
      !n s. s IN (subsets (a n)) ==>
           (integral m (\x. u (SUC n) x * indicator_fn s x) =
            integral m (\x. u n x * indicator_fn s x))`;

(* super-martingale: changed `=` with `<=` *)
val super_martingale_def = Define
   `super_martingale m a u <=>
      sigma_finite_FMS m a /\ (!n. integrable m (u n)) /\
      !n s. s IN (subsets (a n)) ==>
           (integral m (\x. u (SUC n) x * indicator_fn s x) <=
            integral m (\x. u n x * indicator_fn s x))`;

(* sub-martingale: integral (u n) <= integral (u (SUC n)), looks more natural *)
val sub_martingale_def = Define
   `sub_martingale m a u <=>
      sigma_finite_FMS m a /\ (!n. integrable m (u n)) /\
      !n s. s IN (subsets (a n)) ==>
           (integral m (\x. u n x * indicator_fn s x) <=
            integral m (\x. u (SUC n) x * indicator_fn s x))`;

(* u is a martingale if, and only if, it is both a sub- and a supermartingale *)
val MARTINGALE_BOTH_SUB_SUPER = store_thm
  ("MARTINGALE_BOTH_SUB_SUPER",
  ``!m a u. martingale m a u <=> sub_martingale m a u /\ super_martingale m a u``,
    RW_TAC std_ss [martingale_def, sub_martingale_def, super_martingale_def]
 >> EQ_TAC >> RW_TAC std_ss [le_refl]
 >> ASM_SIMP_TAC std_ss [GSYM le_antisym]);

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

(* ------------------------------------------------------------------------- *)
(*  General version of martingales with poset indexes (Chapter 19 of [1])    *)
(* ------------------------------------------------------------------------- *)

open posetTheory;

val POSET_NUM_LE = store_thm
  ("POSET_NUM_LE", ``poset (univ(:num),$<=)``,
    RW_TAC std_ss [poset_def]
 >- (Q.EXISTS_TAC `0` >> REWRITE_TAC [GSYM IN_APP, IN_UNIV])
 >- (MATCH_MP_TAC LESS_EQUAL_ANTISYM >> art [])
 >> MATCH_MP_TAC LESS_EQ_TRANS
 >> Q.EXISTS_TAC `y` >> art []);

(* below J is an index set, R is a partial order on J *)
val filtration_I_def = Define
   `filtration_I A a (J,R) <=>
      poset (J,R) /\ (!n. n IN J ==> sub_sigma_algebra (a n) A) /\
      (!i j. i IN J /\ j IN J /\ R i j ==> subsets (a i) SUBSET subsets (a j))`;

val FILTRATION_FILTRATION_I = store_thm
  ("FILTRATION_FILTRATION_I",
  ``!A a. filtration A a = filtration_I A a (univ(:num),$<=)``,
    RW_TAC std_ss [filtration_def, filtration_I_def, POSET_NUM_LE, IN_UNIV]);

val filtered_measure_space_I_def = Define
   `filtered_measure_space_I (sp,sts,m) a (J,R) <=>
             measure_space (sp,sts,m) /\ filtration_I (sp,sts) a (J,R)`;

val filtered_measure_space_I_alt = store_thm
  ("filtered_measure_space_I_alt",
  ``!sp sts m a. filtered_measure_space (sp,sts,m) a <=>
                 filtered_measure_space_I (sp,sts,m) a (univ(:num),$<=)``,
    RW_TAC std_ss [filtered_measure_space_def, filtered_measure_space_I_def,
                   FILTRATION_FILTRATION_I, POSET_NUM_LE, IN_UNIV]);

val sigma_finite_FMS_I_def = Define
   `sigma_finite_FMS_I (sp,sts,m) a (J,R) <=>
          filtered_measure_space_I (sp,sts,m) a (J,R) /\
          !n. n IN J ==> sigma_finite (sp,subsets (a n),m)`;

val SIGMA_FINITE_FMS_SIGMA_FINITE_FMS_I = store_thm
  ("SIGMA_FINITE_FMS_SIGMA_FINITE_FMS_I",
  ``!sp sts m a. sigma_finite_FMS (sp,sts,m) a <=>
                 sigma_finite_FMS_I (sp,sts,m) a (univ(:num),$<=)``,
    RW_TAC std_ss [SIGMA_FINITE_FMS, sigma_finite_FMS_I_def,
                   filtered_measure_space_I_alt, IN_UNIV]);

val infty_sigma_algebra_I_def = Define
   `infty_sigma_algebra_I sp a I = sigma sp (BIGUNION (IMAGE (\i. subsets (a i)) I))`;

(* `martingale_I m a u (univ(:num),$<=) = martingale m a u` *)
val martingale_I_def = Define
   `martingale_I m a u (J,R) <=>
      sigma_finite_FMS_I m a (J,R) /\ (!n. n IN J ==> integrable m (u n)) /\
      !i j s. i IN J /\ j IN J /\ R i j /\ s IN (subsets (a i)) ==>
             (integral m (\x. u i x * indicator_fn s x) =
              integral m (\x. u j x * indicator_fn s x))`;

(* or "upwards directed" *)
val upwards_filtering_def = Define
   `upwards_filtering (J,R) <=> !a b. a IN J /\ b IN J ==> ?c. c IN J /\ R a c /\ R b c`;

(* The smallest sigma-algebra on `sp` that makes `f` measurable *)
val sigma_function_def = Define
   `sigma_function sp A f = (sp,IMAGE (\s. PREIMAGE f s INTER sp) (subsets A))`;

val _ = overload_on ("sigma", ``sigma_function``);

val SIGMA_MEASURABLE = store_thm
  ("SIGMA_MEASURABLE",
  ``!sp A f. sigma_algebra A /\ f IN (sp -> space A) ==> f IN measurable (sigma sp A f) A``,
    RW_TAC std_ss [sigma_function_def, space_def, subsets_def,
                   IN_FUNSET, IN_MEASURABLE, IN_IMAGE]
 >- (MATCH_MP_TAC PREIMAGE_SIGMA_ALGEBRA >> art [IN_FUNSET])
 >> Q.EXISTS_TAC `s` >> art []);

(* Definition 7.5 of [1, p.51], The smallest sigma-algebra on `sp` that makes all `f`
   simultaneously measurable. *)
val sigma_functions_def = Define
   `sigma_functions sp A f J =
      sigma sp (BIGUNION (IMAGE (\i. IMAGE (\s. PREIMAGE (f i) s INTER sp) (subsets (A i))) J))`;

val _ = overload_on ("sigma", ``sigma_functions``);

(* Lemma 7.5 of [1, p.51] *)
val SIGMA_SIMULTANEOUSLY_MEASURABLE = store_thm
  ("SIGMA_SIMULTANEOUSLY_MEASURABLE",
  ``!sp A f J. (!i. i IN J ==> sigma_algebra (A i)) /\
               (!i. f i IN (sp -> space (A i))) ==>
                !i. i IN J ==> f i IN measurable (sigma sp A f J) (A i)``,
    RW_TAC std_ss [IN_FUNSET, SPACE_SIGMA, sigma_functions_def, IN_MEASURABLE]
 >- (MATCH_MP_TAC SIGMA_ALGEBRA_SIGMA \\
     RW_TAC std_ss [subset_class_def, IN_BIGUNION_IMAGE, IN_IMAGE, IN_PREIMAGE, IN_INTER] \\
     REWRITE_TAC [INTER_SUBSET])
 >> Know `PREIMAGE (f i) s INTER sp IN
            (BIGUNION (IMAGE (\i. IMAGE (\s. PREIMAGE (f i) s INTER sp) (subsets (A i))) J))`
 >- (RW_TAC std_ss [IN_BIGUNION_IMAGE, IN_IMAGE] \\
     Q.EXISTS_TAC `i` >> art [] \\
     Q.EXISTS_TAC `s` >> art []) >> DISCH_TAC
 >> ASSUME_TAC
      (Q.SPECL [`sp`, `BIGUNION (IMAGE (\i. IMAGE (\s. PREIMAGE (f i) s INTER sp)
                                                  (subsets (A i))) J)`] SIGMA_SUBSET_SUBSETS)
 >> PROVE_TAC [SUBSET_DEF]);

(* ------------------------------------------------------------------------- *)
(* Radon-Nikodym Theorem (moved here from lebesgueTheory)                    *)
(* ------------------------------------------------------------------------- *)

val seq_sup_def = Define `
   (seq_sup P 0       = @r. r IN P /\ sup P < r + 1) /\
   (seq_sup P (SUC n) = @r. r IN P /\ sup P < r + Normal ((1 / 2) pow (SUC n)) /\
                            (seq_sup P n) < r /\ r < sup P)`;

val EXTREAL_SUP_SEQ = store_thm
  ("EXTREAL_SUP_SEQ",
  ``!P. (?x. P x) /\ (?z. z <> PosInf /\ !x. P x ==> x <= z) ==>
        ?x. (!n. x n IN P) /\ (!n. x n <= x (SUC n)) /\ (sup (IMAGE x UNIV) = sup P)``,
  RW_TAC std_ss []
  >> Cases_on `?z. P z /\ (z = sup P)`
  >- (Q.EXISTS_TAC `(\i. sup P)`
      >> RW_TAC std_ss [le_refl,SPECIFICATION]
      >> `IMAGE (\i:num. sup P) UNIV = (\i. i = sup P)`
           by RW_TAC std_ss [EXTENSION,IN_IMAGE,IN_UNIV,IN_ABS]
      >> RW_TAC std_ss [sup_const])
  >> Cases_on `!x. P x ==> (x = NegInf)`
  >- (`sup P = NegInf` by METIS_TAC [sup_const_alt]
      >> Q.EXISTS_TAC `(\n. NegInf)`
      >> FULL_SIMP_TAC std_ss [le_refl]
      >> RW_TAC std_ss []
      >- METIS_TAC []
      >> METIS_TAC [UNIV_NOT_EMPTY,sup_const_over_set])
  >> FULL_SIMP_TAC std_ss []
  >> Q.EXISTS_TAC `seq_sup P`
  >> FULL_SIMP_TAC std_ss []
  >> `sup P <> PosInf` by METIS_TAC [sup_le,lt_infty,let_trans]
  >> `!x. P x ==> x < sup P` by METIS_TAC [lt_le,le_sup_imp]
  >> `!e. 0 < e ==> ?x. P x /\ sup P < x + e`
       by (RW_TAC std_ss [] >> MATCH_MP_TAC sup_lt_epsilon >> METIS_TAC [])
  >> `!n. 0:real < (1 / 2) pow n` by METIS_TAC [HALF_POS,REAL_POW_LT]
  >> `!n. 0 < Normal ((1 / 2) pow n)` by METIS_TAC [extreal_lt_eq,extreal_of_num_def]
  >> `!n. seq_sup P n IN P`
      by (Induct
          >- (RW_TAC std_ss [seq_sup_def]
              >> SELECT_ELIM_TAC
              >> RW_TAC std_ss []
              >> METIS_TAC [lt_01,SPECIFICATION])
          >> RW_TAC std_ss [seq_sup_def]
          >> SELECT_ELIM_TAC
          >> RW_TAC std_ss []
          >> `?x. P x /\ seq_sup P n < x` by METIS_TAC [sup_lt,SPECIFICATION]
          >> `?x. P x /\ sup P < x + Normal ((1 / 2) pow (SUC n))` by METIS_TAC []
          >> Q.EXISTS_TAC `max x'' x'''`
          >> RW_TAC std_ss [extreal_max_def,SPECIFICATION]
          >- (`x''' < x''` by FULL_SIMP_TAC std_ss [GSYM extreal_lt_def]
              >> `x''' +  Normal ((1 / 2) pow (SUC n)) <= x'' +  Normal ((1 / 2) pow (SUC n))`
                  by METIS_TAC [lt_radd,lt_le,extreal_not_infty]
              >> METIS_TAC [lte_trans])
          >> METIS_TAC [lte_trans])
  >> `!n. seq_sup P n <= seq_sup P (SUC n)`
      by (RW_TAC std_ss [seq_sup_def]
          >> SELECT_ELIM_TAC
          >> RW_TAC std_ss []
          >- (`?x. P x /\ seq_sup P n < x` by METIS_TAC [sup_lt,SPECIFICATION]
              >> `?x. P x /\ sup P < x + Normal ((1 / 2) pow (SUC n))` by METIS_TAC []
              >> Q.EXISTS_TAC `max x'' x'''`
              >> RW_TAC std_ss [extreal_max_def,SPECIFICATION]
              >- (`x''' < x''` by FULL_SIMP_TAC std_ss [GSYM extreal_lt_def]
                  >> `x''' + Normal ((1 / 2) pow (SUC n)) <= x'' + Normal ((1 / 2) pow (SUC n))`
                      by METIS_TAC [lt_radd,lt_le,extreal_not_infty]
                  >> METIS_TAC [lte_trans])
              >> METIS_TAC [lte_trans])
          >> METIS_TAC [lt_le])
  >> RW_TAC std_ss []
  >> `!n. sup P <= seq_sup P n + Normal ((1 / 2) pow n)`
      by (Induct
          >- (RW_TAC std_ss [seq_sup_def,pow,GSYM extreal_of_num_def]
              >> SELECT_ELIM_TAC
              >> RW_TAC std_ss []
              >- METIS_TAC [lt_01,SPECIFICATION]
              >> METIS_TAC [lt_le])
          >> RW_TAC std_ss [seq_sup_def]
          >> SELECT_ELIM_TAC
          >> RW_TAC std_ss []
          >- (`?x. P x /\ seq_sup P n < x` by METIS_TAC [sup_lt,SPECIFICATION]
              >> `?x. P x /\ sup P < x + Normal ((1 / 2) pow (SUC n))` by METIS_TAC []
              >> Q.EXISTS_TAC `max x'' x'''`
              >> RW_TAC std_ss [extreal_max_def,SPECIFICATION]
              >- (`x''' < x''` by FULL_SIMP_TAC std_ss [GSYM extreal_lt_def]
                  >> `x''' + Normal ((1 / 2) pow (SUC n)) <= x'' + Normal ((1 / 2) pow (SUC n))`
                      by METIS_TAC [lt_radd,lt_le,extreal_not_infty]
                  >> METIS_TAC [lte_trans])
              >> METIS_TAC [lte_trans])
          >> METIS_TAC [lt_le])
  >> RW_TAC std_ss [sup_eq]
  >- (POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
      >> RW_TAC std_ss [IN_IMAGE,IN_UNIV]
      >> METIS_TAC [SPECIFICATION,lt_le])
  >> MATCH_MP_TAC le_epsilon
  >> RW_TAC std_ss []
  >> `e <> NegInf` by METIS_TAC [lt_infty,extreal_of_num_def,lt_trans]
  >> `?r. e = Normal r` by METIS_TAC [extreal_cases]
  >> FULL_SIMP_TAC std_ss []
  >> `?n. Normal ((1 / 2) pow n) < Normal r` by METIS_TAC [EXTREAL_ARCH_POW_INV]
  >> MATCH_MP_TAC le_trans
  >> Q.EXISTS_TAC `seq_sup P n + Normal ((1 / 2) pow n)`
  >> RW_TAC std_ss []
  >> MATCH_MP_TAC le_add2
  >> FULL_SIMP_TAC std_ss [lt_le]
  >> Q.PAT_X_ASSUM `!z. IMAGE (seq_sup P) UNIV z ==> z <= y` MATCH_MP_TAC
  >> ONCE_REWRITE_TAC [GSYM SPECIFICATION]
  >> RW_TAC std_ss [IN_UNIV,IN_IMAGE]
  >> METIS_TAC []);

val EXTREAL_SUP_FUN_SEQ_IMAGE = store_thm
  ("EXTREAL_SUP_FUN_SEQ_IMAGE",
  ``!(P:extreal->bool) (P':('a->extreal)->bool) f.
       (?x. P x) /\ (?z. z <> PosInf /\ !x. P x ==> x <= z) /\ (P = IMAGE f P')
           ==> ?g. (!n:num. g n IN P') /\
                   (sup (IMAGE (\n. f (g n)) UNIV) = sup P)``,
  rpt STRIP_TAC
  >> `?y. (!n. y n IN P) /\ (!n. y n <= y (SUC n)) /\ (sup (IMAGE y UNIV) = sup P)`
     by METIS_TAC [EXTREAL_SUP_SEQ]
  >> Q.EXISTS_TAC `(\n. @r. (r IN P') /\ (f r  = y n))`
  >> `(\n. f (@(r :'a -> extreal). r IN (P' :('a -> extreal) -> bool) /\
                                  ((f :('a -> extreal) -> extreal) r = (y :num -> extreal) n))) = y`
  by (rw [FUN_EQ_THM] >> SELECT_ELIM_TAC
      >> RW_TAC std_ss []
      >> METIS_TAC [IN_IMAGE])
  >> ASM_SIMP_TAC std_ss []
  >> RW_TAC std_ss []
  >- (SELECT_ELIM_TAC
      >> RW_TAC std_ss []
      >> METIS_TAC [IN_IMAGE]));

val max_fn_seq_def = Define `
   (max_fn_seq g 0 x  = g 0 x) /\
   (max_fn_seq g (SUC n) x = max (max_fn_seq g n x) (g (SUC n) x))`;

val max_fn_seq_mono = store_thm
  ("max_fn_seq_mono", ``!g n x. max_fn_seq g n x <= max_fn_seq g (SUC n) x``,
    RW_TAC std_ss [max_fn_seq_def,extreal_max_def,le_refl]);

val EXTREAL_SUP_FUN_SEQ_MONO_IMAGE = store_thm
  ("EXTREAL_SUP_FUN_SEQ_MONO_IMAGE",
  ``!f (P:extreal->bool) (P':('a->extreal)->bool).
                (?x. P x) /\ (?z. z <> PosInf /\ !x. P x ==> x <= z) /\ (P = IMAGE f P') /\
                (!g1 g2. (g1 IN P' /\ g2 IN P' /\ (!x. g1 x <= g2 x))  ==> f g1 <= f g2) /\
                (!g1 g2. g1 IN P' /\ g2 IN P' ==> (\x. max (g1 x) (g2 x)) IN P')
          ==> ?g. (!n. g n IN P') /\
                  (!x n. g n x <= g (SUC n) x) /\
                  (sup (IMAGE (\n. f (g n)) UNIV) = sup P)``,
  rpt STRIP_TAC
  >> `?g. (!n:num. g n IN P') /\ (sup (IMAGE (\n. f (g n)) UNIV) = sup P)`
      by METIS_TAC [EXTREAL_SUP_FUN_SEQ_IMAGE]
  >> Q.EXISTS_TAC `max_fn_seq g`
  >> `!n. max_fn_seq g n IN P'`
      by (Induct
          >- (`max_fn_seq g 0 = g 0` by RW_TAC std_ss [FUN_EQ_THM,max_fn_seq_def]
              >> METIS_TAC [])
              >> `max_fn_seq g (SUC n) = (\x. max (max_fn_seq g n x) (g (SUC n) x))`
                  by RW_TAC std_ss [FUN_EQ_THM,max_fn_seq_def]
              >> RW_TAC std_ss []
              >> METIS_TAC [])
  >> `!g n x. max_fn_seq g n x <= max_fn_seq g (SUC n) x`
      by RW_TAC real_ss [max_fn_seq_def,extreal_max_def,le_refl]
  >> CONJ_TAC >- RW_TAC std_ss []
  >> CONJ_TAC >- RW_TAC std_ss []
  >> `!n. (!x. g n x <= max_fn_seq g n x)`
      by (Induct >- RW_TAC std_ss [max_fn_seq_def,le_refl]
          >> METIS_TAC [le_max2,max_fn_seq_def])
  >> `!n. f (g n) <= f (max_fn_seq g n)` by METIS_TAC []
  >> `sup (IMAGE (\n. f (g n)) UNIV) <= sup (IMAGE (\n. f (max_fn_seq g n)) UNIV)`
      by (MATCH_MP_TAC sup_le_sup_imp
          >> RW_TAC std_ss []
          >> POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
          >> RW_TAC std_ss [IN_IMAGE,IN_UNIV]
          >> Q.EXISTS_TAC `f (max_fn_seq g n)`
          >> RW_TAC std_ss []
          >> ONCE_REWRITE_TAC [GSYM SPECIFICATION]
          >> RW_TAC std_ss [IN_IMAGE,IN_UNIV]
          >> METIS_TAC [])
  >> `sup (IMAGE (\n. f (max_fn_seq g n)) UNIV) <= sup P`
      by (RW_TAC std_ss [sup_le]
          >> POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
          >> RW_TAC std_ss [IN_IMAGE,IN_UNIV]
          >> MATCH_MP_TAC le_sup_imp
          >> ONCE_REWRITE_TAC [GSYM SPECIFICATION]
          >> RW_TAC std_ss [IN_IMAGE]
          >> METIS_TAC [])
  >> METIS_TAC [le_antisym]);

val signed_measure_space_def = Define `
    signed_measure_space m <=>
      sigma_algebra (m_space m,measurable_sets m) /\ countably_additive m`;

val negative_set_def = Define `
    negative_set m A <=> A IN measurable_sets m /\
                        (!s. s IN measurable_sets m /\ s SUBSET A ==> measure m s <= 0)`;

val RADON_F_def = Define `
    RADON_F m v =
      {f | f IN measurable (m_space m,measurable_sets m) Borel /\ (!x. 0 <= f x) /\
           !A. A IN measurable_sets m ==>
              (pos_fn_integral m (\x. f x * indicator_fn A x) <= measure v A)}`;

val RADON_F_integrals_def = Define `
    RADON_F_integrals m v = {r | ?f. (r = pos_fn_integral m f) /\ f IN RADON_F m v}`;

(*
val lemma_radon_max_in_F = store_thm
  ("lemma_radon_max_in_F",``!f g m v. (measure_space m /\ measure_space v /\
        (m_space v = m_space m) /\ (measurable_sets v = measurable_sets m) /\
        f IN RADON_F m v /\ g IN RADON_F m v)
             ==> (\x. max (f x) (g x)) IN RADON_F m v``,
  RW_TAC real_ss [RADON_F_def,GSPECIFICATION,max_le,le_max]
  >- FULL_SIMP_TAC std_ss [IN_MEASURABLE_BOREL_MAX,measure_space_def]
  >> Q.ABBREV_TAC `A1 = {x | x IN A /\ g x < f x}`
  >> Q.ABBREV_TAC `A2 = {x | x IN A /\ f x <= g x}`
  >> `DISJOINT A1 A2`
         by (Q.UNABBREV_TAC `A1` >> Q.UNABBREV_TAC `A2`
           >> RW_TAC std_ss [IN_DISJOINT,GSPECIFICATION]
           >> METIS_TAC [extreal_lt_def])
   >> `A1 UNION A2 = A`
       by (Q.UNABBREV_TAC `A1` >> Q.UNABBREV_TAC `A2`
           >> RW_TAC std_ss [IN_UNION,EXTENSION,GSPECIFICATION]
           >> METIS_TAC [extreal_lt_def])
   >> `(\x. max (f x) (g x) * indicator_fn A x) =
           (\x. (\x. max (f x) (g x) * indicator_fn A1 x) x +
           (\x. max (f x) (g x) * indicator_fn A2 x) x)`
       by (Q.UNABBREV_TAC `A1` >> Q.UNABBREV_TAC `A2`
           >> RW_TAC std_ss [indicator_fn_def,GSPECIFICATION,FUN_EQ_THM]
           >> Cases_on `g x < f x`
           >- (RW_TAC std_ss [mul_rone,mul_rzero,add_rzero] >> METIS_TAC [extreal_lt_def])
           >> RW_TAC real_ss [mul_rone,mul_rzero,add_lzero] >> METIS_TAC [extreal_lt_def])
   >> `additive v` by METIS_TAC [measure_space_def, sigma_algebra_def,
                                 ALGEBRA_COUNTABLY_ADDITIVE_ADDITIVE]
   >> `A SUBSET m_space m` by RW_TAC std_ss [MEASURE_SPACE_SUBSET_MSPACE]
   >> `A1 = ({x | g x < f x} INTER m_space m) INTER A`
       by (Q.UNABBREV_TAC `A1`
           >> RW_TAC std_ss [EXTENSION,IN_INTER,GSPECIFICATION,CONJ_SYM]
           >> METIS_TAC [SUBSET_DEF])
   >> `A2 = ({x | f x <= g x} INTER m_space m) INTER A`
       by (Q.UNABBREV_TAC `A2`
           >> RW_TAC std_ss [EXTENSION,IN_INTER,GSPECIFICATION,CONJ_SYM]
           >> METIS_TAC [SUBSET_DEF])
   >> `A1 IN measurable_sets m`
       by (ASM_SIMP_TAC std_ss []
           >> MATCH_MP_TAC MEASURE_SPACE_INTER
           >> RW_TAC std_ss []
           >> METIS_TAC [IN_MEASURABLE_BOREL_LT, m_space_def, space_def, subsets_def,
                         measurable_sets_def])
   >> `A2 IN measurable_sets m`
       by (ASM_SIMP_TAC std_ss []
           >> MATCH_MP_TAC MEASURE_SPACE_INTER
           >> RW_TAC std_ss []
           >> METIS_TAC [IN_MEASURABLE_BOREL_LE, m_space_def, space_def, subsets_def,
                         measurable_sets_def])
   >> `measure v A = measure v A1 + measure v A2` by METIS_TAC [ADDITIVE]
   >> Q.PAT_X_ASSUM `A1 = M` (K ALL_TAC)
   >> Q.PAT_X_ASSUM `A2 = M` (K ALL_TAC)
   >> `!x. max (f x) (g x) * indicator_fn A1 x = f x * indicator_fn A1 x`
       by (Q.UNABBREV_TAC `A1`
           >> RW_TAC std_ss [extreal_max_def, indicator_fn_def, GSPECIFICATION, mul_rone,
                             mul_rzero]
           >> METIS_TAC [extreal_lt_def])
   >> `!x. max (f x) (g x) * indicator_fn A2 x = g x * indicator_fn A2 x`
       by (Q.UNABBREV_TAC `A2`
           >> RW_TAC std_ss [extreal_max_def, indicator_fn_def, GSPECIFICATION, mul_rone,
                             mul_rzero]
           >> METIS_TAC [extreal_lt_def])
   >> ASM_SIMP_TAC std_ss []
   >> `(\x. f x * indicator_fn A1 x) IN measurable (m_space m, measurable_sets m) Borel`
           by METIS_TAC [IN_MEASURABLE_BOREL_MUL_INDICATOR, measure_space_def,
                         measurable_sets_def, subsets_def]
   >> `(\x. g x * indicator_fn A2 x) IN  measurable (m_space m, measurable_sets m) Borel`
           by METIS_TAC [IN_MEASURABLE_BOREL_MUL_INDICATOR, measure_space_def,
                         measurable_sets_def, subsets_def]
   >> `!x. 0 <= (\x. f x * indicator_fn A1 x) x`
        by RW_TAC std_ss [indicator_fn_def, mul_rone, mul_rzero, le_01, le_refl]
   >> `!x. 0 <= (\x. g x * indicator_fn A2 x) x`
        by RW_TAC std_ss [indicator_fn_def, mul_rone, mul_rzero, le_01, le_refl]
   >> FULL_SIMP_TAC std_ss [le_add2,pos_fn_integral_add, GSYM extreal_add_def]);

val lemma_radon_seq_conv_sup = store_thm
  ("lemma_radon_seq_conv_sup",``!f m v. (measure_space m /\ measure_space v /\
                                        (m_space v = m_space m) /\
                                        (measurable_sets v = measurable_sets m)) /\
                                        (measure v (m_space v) <> PosInf)
        ==> ?f_n. (!n. f_n n IN RADON_F m v) /\
                  (!x n. f_n n x <= f_n (SUC n) x) /\
                  (sup (IMAGE (\n. pos_fn_integral m (f_n n)) UNIV) =
                   sup (RADON_F_integrals m v))``,
  RW_TAC std_ss [RADON_F_integrals_def]
  >> MATCH_MP_TAC EXTREAL_SUP_FUN_SEQ_MONO_IMAGE
  >> CONJ_TAC
  >- (Q.EXISTS_TAC `0`
      >> ONCE_REWRITE_TAC [GSYM SPECIFICATION]
      >> RW_TAC std_ss [GSPECIFICATION]
      >> Q.EXISTS_TAC `(\x. 0)`
      >> RW_TAC real_ss [RADON_F_def,GSPECIFICATION,pos_fn_integral_zero,mul_lzero,le_refl]
      >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST
          >> METIS_TAC [space_def,measure_space_def])
      >> METIS_TAC [measure_space_def,positive_def])
  >> CONJ_TAC
  >- (Q.EXISTS_TAC `measure v (m_space v)`
      >> RW_TAC std_ss []
      >> POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
      >> RW_TAC std_ss [GSPECIFICATION,RADON_F_def]
      >> POP_ASSUM (MP_TAC o Q.SPEC `m_space m`)
      >> RW_TAC std_ss [MEASURE_SPACE_MSPACE_MEASURABLE, GSYM pos_fn_integral_mspace])
  >> CONJ_TAC
  >- RW_TAC std_ss [EXTENSION,GSPECIFICATION,IN_IMAGE,RADON_F_def]
  >> CONJ_TAC
  >- RW_TAC std_ss [RADON_F_def,GSPECIFICATION,pos_fn_integral_mono]
  >> RW_TAC std_ss [lemma_radon_max_in_F]);

val RN_lemma1 = store_thm
  ("RN_lemma1",``!m v e. measure_space m /\ measure_space v /\ 0 < e /\
                       (m_space v = m_space m) /\ (measurable_sets v = measurable_sets m)
                      /\ measure v (m_space m) <> PosInf
                      /\ measure m (m_space m) <> PosInf
       ==> (?A. A IN measurable_sets m /\
                measure m (m_space m) - measure v (m_space m) <= measure m A - measure v A /\
                !B. B IN measurable_sets m /\ B SUBSET A
                    ==> -e < measure m B - measure v B)``,
  RW_TAC std_ss []
  >> `!A. A IN measurable_sets m ==> measure m A <> NegInf` by METIS_TAC [MEASURE_SPACE_POSITIVE,positive_not_infty]
  >> `!A. A IN measurable_sets m ==> measure m A <= measure m (m_space m)` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE,MEASURE_SPACE_MSPACE_MEASURABLE,INCREASING,MEASURE_SPACE_INCREASING]
  >> `!A. A IN measurable_sets m ==> measure m A <> PosInf` by METIS_TAC [lt_infty,let_trans]
  >> `!A. A IN measurable_sets m ==> measure v A <> NegInf` by METIS_TAC [MEASURE_SPACE_POSITIVE,positive_not_infty,measure_def,measurable_sets_def]
  >> `!A. A IN measurable_sets m ==> measure v A <= measure v (m_space m)` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE,MEASURE_SPACE_MSPACE_MEASURABLE,INCREASING,MEASURE_SPACE_INCREASING]
  >> `!A. A IN measurable_sets m ==> measure v A <> PosInf` by METIS_TAC [lt_infty,let_trans]
  >> Q.ABBREV_TAC `d = (\A. measure m A - measure v A)`
  >> `!A. A IN measurable_sets m ==> d A <> NegInf` by METIS_TAC [sub_not_infty]
  >> `!A. A IN measurable_sets m ==> d A <> PosInf` by METIS_TAC [sub_not_infty]
  >> `e <> NegInf` by METIS_TAC [lt_infty,lt_trans,num_not_infty]
  >> Cases_on `e = PosInf`
  >- (Q.EXISTS_TAC `m_space m`
      >> METIS_TAC [MEASURE_SPACE_MSPACE_MEASURABLE,le_refl,lt_infty,extreal_ainv_def])
  >> Q.ABBREV_TAC `h = (\A. if (!B. B IN measurable_sets m /\ B SUBSET (m_space m DIFF A) ==> -e < d B)
                            then {} else @B. B IN measurable_sets m /\ B SUBSET (m_space m DIFF A) /\ d B <= -e )`
  >> `!A. A IN measurable_sets m ==> h A  IN measurable_sets m`
        by (RW_TAC std_ss []
            >> METIS_TAC [MEASURE_SPACE_EMPTY_MEASURABLE,extreal_lt_def])
  >> Q.ABBREV_TAC `A = SIMP_REC {} (\a. a UNION h a)`
  >> `A 0 = {}` by METIS_TAC [SIMP_REC_THM]
  >> `!n. A (SUC n) = (A n) UNION (h (A n))` by (Q.UNABBREV_TAC `A` >> RW_TAC std_ss [SIMP_REC_THM])
  >> `!n. A n IN measurable_sets m`
        by (Induct >- RW_TAC std_ss [MEASURE_SPACE_EMPTY_MEASURABLE]
            >> RW_TAC std_ss [MEASURE_SPACE_UNION])
  >> `!n. (?B. B IN measurable_sets m /\ B SUBSET (m_space m DIFF (A n)) /\ d B <= -e) ==>
               d (A (SUC n)) <= d (A n) - e`
       by (RW_TAC std_ss []
           >> `~(!B. B IN measurable_sets m /\ B SUBSET (m_space m DIFF (A n)) ==> -e < d B)`
                 by METIS_TAC [extreal_lt_def]
           >> `h (A n) = (@B. B IN measurable_sets m /\ B SUBSET m_space m DIFF (A n) /\ d B <= -e)`
                by (Q.UNABBREV_TAC `h` >> RW_TAC std_ss [])
           >> POP_ORW
           >> SELECT_ELIM_TAC
           >> RW_TAC std_ss []
           >- METIS_TAC []
           >> `DISJOINT (A n) x`
               by (RW_TAC std_ss [DISJOINT_DEF,EXTENSION,IN_INTER,NOT_IN_EMPTY]
                   >> METIS_TAC [SUBSET_DEF,IN_DIFF])
           >> `d ((A n) UNION x) = d (A n) + d x`
                 by (Q.UNABBREV_TAC `d`
                     >> RW_TAC std_ss []
                     >> `measure m (A n UNION x) = measure m (A n) + measure m x`
                           by (MATCH_MP_TAC ADDITIVE
                               >> FULL_SIMP_TAC std_ss [MEASURE_SPACE_ADDITIVE])
                     >> `measure v (A n UNION x) = measure v (A n) + measure v x`
                           by (MATCH_MP_TAC ADDITIVE
                               >> FULL_SIMP_TAC std_ss [MEASURE_SPACE_ADDITIVE])
                     >> POP_ORW >> POP_ORW
                     >> `?r1. measure v (A n) = Normal r1` by METIS_TAC [extreal_cases]
                     >> `?r2. measure v x = Normal r2` by METIS_TAC [extreal_cases]
                     >> RW_TAC std_ss [extreal_add_def]
                     >> Cases_on `measure m (A n)`
                     >> Cases_on `measure m x`
                     >> RW_TAC std_ss [extreal_add_def,extreal_sub_def,REAL_ADD2_SUB2]
                     >> METIS_TAC [])
          >> POP_ORW
          >> `d (A n) - e = d (A n) + -e` by METIS_TAC [extreal_sub_add]
          >> METIS_TAC [le_ladd])
  >> `!n. d (A (SUC n)) <= d (A n)`
        by (RW_TAC std_ss []
            >> Cases_on `(?B. B IN measurable_sets m /\ B SUBSET m_space m DIFF A n /\ d B <= -e)`
            >- (`d (A n) <= d (A n) + e` by METIS_TAC [lt_le,le_addr_imp]
                >> `d (A n) - e <= d (A n)`
                     by (Cases_on `d(A n)` >> Cases_on `e`
                         >> RW_TAC std_ss [extreal_add_def,extreal_sub_def,extreal_le_def,extreal_not_infty,lt_infty,le_infty]
                         >> METIS_TAC [extreal_add_def,extreal_le_def,REAL_LE_SUB_RADD])
                >> METIS_TAC [le_trans])
            >> `!B. B IN measurable_sets m /\ B SUBSET m_space m DIFF A n ==> -e < d B` by METIS_TAC [extreal_lt_def]
            >> METIS_TAC [UNION_EMPTY,le_refl])
  >> Cases_on `?n. !B. ((B IN measurable_sets m /\ B SUBSET (m_space m DIFF (A n))) ==> -e < d B)`
  >- (Q.PAT_X_ASSUM `!n. A (SUC n) = a UNION b` (K ALL_TAC)
      >> FULL_SIMP_TAC std_ss []
      >> `!n. m_space m DIFF (A n) IN measurable_sets m` by METIS_TAC [MEASURE_SPACE_DIFF,MEASURE_SPACE_MSPACE_MEASURABLE]
      >> Suff `!n. d (m_space m) <= d (m_space m DIFF (A n))`
      >- METIS_TAC []
      >> Induct
      >- RW_TAC std_ss [DIFF_EMPTY,le_refl]
      >> `measure m (m_space m DIFF A (SUC n')) = measure m (m_space m) - measure m (A (SUC n'))`
           by METIS_TAC [MEASURE_SPACE_FINITE_DIFF]
      >> `measure v (m_space m DIFF A (SUC n')) = measure v (m_space m) - measure v (A (SUC n'))`
           by METIS_TAC [MEASURE_SPACE_FINITE_DIFF,measure_def,measurable_sets_def,m_space_def]
      >> `measure m (m_space m DIFF A n') = measure m (m_space m) - measure m (A n')`
           by METIS_TAC [MEASURE_SPACE_FINITE_DIFF]
      >> `measure v (m_space m DIFF A n') = measure v (m_space m) - measure v (A n')`
           by METIS_TAC [MEASURE_SPACE_FINITE_DIFF,measure_def,measurable_sets_def,m_space_def]
      >> `d (m_space m DIFF A n') = d (m_space m) - d (A n')`
             by (Q.UNABBREV_TAC `d`
                 >> FULL_SIMP_TAC std_ss []
                 >> `?r1. measure m (m_space m) = Normal r1` by METIS_TAC [extreal_cases,MEASURE_SPACE_MSPACE_MEASURABLE]
                 >> `?r2. measure v (m_space m) = Normal r2` by METIS_TAC [extreal_cases,MEASURE_SPACE_MSPACE_MEASURABLE]
                 >> `?r3. measure m (A n') = Normal r3` by METIS_TAC [extreal_cases]
                 >> `?r4. measure v (A n') = Normal r4` by METIS_TAC [extreal_cases]
                 >> FULL_SIMP_TAC std_ss [extreal_add_def,extreal_sub_def,extreal_lt_def,extreal_11]
                 >> REAL_ARITH_TAC)
      >> `d (m_space m DIFF A (SUC n')) = d (m_space m) - d (A (SUC n'))`
             by (Q.UNABBREV_TAC `d`
                 >> FULL_SIMP_TAC std_ss []
                 >> `?r1. measure m (m_space m) = Normal r1` by METIS_TAC [extreal_cases,MEASURE_SPACE_MSPACE_MEASURABLE]
                 >> `?r2. measure v (m_space m) = Normal r2` by METIS_TAC [extreal_cases,MEASURE_SPACE_MSPACE_MEASURABLE]
                 >> `?r3. measure m (A (SUC n')) = Normal r3` by METIS_TAC [extreal_cases]
                 >> `?r4. measure v (A (SUC n')) = Normal r4` by METIS_TAC [extreal_cases]
                 >> FULL_SIMP_TAC std_ss [extreal_add_def,extreal_sub_def,extreal_lt_def,extreal_11]
                 >> REAL_ARITH_TAC)
      >> FULL_SIMP_TAC std_ss []
      >> `d (m_space m) - d (A n') <= d (m_space m) - d (A (SUC n'))`
           by METIS_TAC [extreal_sub_add,MEASURE_SPACE_MSPACE_MEASURABLE,le_ladd_imp,le_neg]
      >> METIS_TAC [le_trans])
  >> `!n. ?B. B IN measurable_sets m /\ B SUBSET (m_space m DIFF (A n)) /\ d B <= -e`
        by METIS_TAC [extreal_lt_def]
  >> `!n. d (A n) <= - &n * e`
       by (Induct
           >- METIS_TAC [mul_lzero,neg_0,le_refl,MEASURE_EMPTY,measure_def,sub_rzero]
           >> `d (A (SUC n)) <= d (A n) - e` by METIS_TAC []
           >> `?r1. d (A n) = Normal r1` by METIS_TAC [extreal_cases]
           >> `?r2. d (A (SUC n)) = Normal r2` by METIS_TAC [extreal_cases]
           >> `e <> PosInf` by ( METIS_TAC [extreal_sub_def,le_infty,extreal_not_infty])
           >> `?r3. e = Normal r3` by METIS_TAC [extreal_cases]
           >> FULL_SIMP_TAC std_ss [extreal_sub_def,extreal_le_def,extreal_ainv_def,extreal_of_num_def,extreal_mul_def]
           >> RW_TAC std_ss [ADD1,GSYM REAL_ADD,REAL_NEG_ADD,REAL_ADD_RDISTRIB,GSYM REAL_NEG_MINUS1]
           >> `r1 + -r3 <= -&n * r3 + -r3` by METIS_TAC [REAL_LE_ADD2,REAL_LE_REFL]
           >> METIS_TAC [real_sub,REAL_LE_TRANS])
  >> `!n. - d (A n) <= - d (A (SUC n))` by METIS_TAC [le_neg]
  >> `!n. A n SUBSET A (SUC n)` by METIS_TAC [SUBSET_UNION]
  >> `sup (IMAGE (measure m o A) UNIV) = measure m (BIGUNION (IMAGE A UNIV))`
       by METIS_TAC [MONOTONE_CONVERGENCE2,IN_FUNSET,IN_UNIV,measure_def,measurable_sets_def]
  >> `sup (IMAGE (measure v o A) UNIV) = measure v (BIGUNION (IMAGE A UNIV))`
       by METIS_TAC [MONOTONE_CONVERGENCE2,IN_FUNSET,IN_UNIV,measure_def,measurable_sets_def]
  >> FULL_SIMP_TAC std_ss [o_DEF]
  >> `?r1. !n. measure m (A n) = Normal (r1 n)`
       by (Q.EXISTS_TAC `(\n. @r. measure m (A n) = Normal r)`
           >> RW_TAC std_ss []
           >> SELECT_ELIM_TAC
           >> METIS_TAC [extreal_cases])
  >> `?r2. !n. measure v (A n) = Normal (r2 n)`
       by (Q.EXISTS_TAC `(\n. @r. measure v (A n) = Normal r)`
           >> RW_TAC std_ss []
           >> SELECT_ELIM_TAC
           >> METIS_TAC [extreal_cases])
  >> `BIGUNION (IMAGE A UNIV) IN measurable_sets m` by METIS_TAC [SIGMA_ALGEBRA_ENUM,measure_space_def,subsets_def,measurable_sets_def,IN_FUNSET,IN_UNIV]
  >> `?l1. measure m (BIGUNION (IMAGE A UNIV)) = Normal l1` by METIS_TAC [extreal_cases]
  >> `?l2. measure v (BIGUNION (IMAGE A UNIV)) = Normal l2` by METIS_TAC [extreal_cases]
  >> FULL_SIMP_TAC std_ss []
  >> `mono_increasing r1` by METIS_TAC [mono_increasing_def,mono_increasing_suc,MEASURE_SPACE_INCREASING,increasing_def,extreal_le_def]
  >> `mono_increasing r2` by METIS_TAC [mono_increasing_def,mono_increasing_suc,MEASURE_SPACE_INCREASING,increasing_def,extreal_le_def,measure_def,measurable_sets_def]
  >> FULL_SIMP_TAC std_ss [GSYM sup_seq]
  >> `!n. -d (A n) = Normal (r2 n - r1 n)`
        by (Q.UNABBREV_TAC `d`
            >> RW_TAC std_ss [extreal_sub_def,extreal_ainv_def,REAL_NEG_SUB])
  >> Q.ABBREV_TAC `r = (\n. r2 n - r1 n)`
  >> `mono_increasing r` by METIS_TAC [mono_increasing_suc, extreal_le_def]
  >> `r --> (l2 - l1)` by (Q.UNABBREV_TAC `r` >> METIS_TAC [SEQ_SUB])
  >> `sup (IMAGE (\n. Normal (r n)) UNIV) = Normal (l2 - l1)` by METIS_TAC [sup_seq]
  >> `sup (IMAGE (\n. -d (A n)) UNIV) = -d (BIGUNION (IMAGE A UNIV))`
        by (`(\n. -d (A n)) = (\n. Normal (r n))` by METIS_TAC []
            >> POP_ORW
            >> Q.UNABBREV_TAC `d`
            >> RW_TAC std_ss [extreal_sub_def,extreal_ainv_def,REAL_NEG_SUB])
  >> `d (BIGUNION (IMAGE A UNIV)) <> NegInf` by METIS_TAC []
  >> `- d (BIGUNION (IMAGE A UNIV)) <> PosInf` by METIS_TAC [extreal_ainv_def,extreal_cases,extreal_not_infty]
  >> `?n. - d (BIGUNION (IMAGE A UNIV)) < &n * e` by METIS_TAC [EXTREAL_ARCH]
  >> `&n * e <= -d (A n)` by METIS_TAC [le_neg,neg_neg,mul_lneg]
  >> `-d (BIGUNION (IMAGE A univ(:num))) < -d (A n)` by METIS_TAC [lte_trans]
  >> `-d (A n) <= - d (BIGUNION (IMAGE A UNIV))`
       by (RW_TAC std_ss []
           >> Q.PAT_X_ASSUM `sup P = -d Q` (MP_TAC o GSYM)
           >> DISCH_THEN (fn th => REWRITE_TAC [th])
           >> MATCH_MP_TAC le_sup_imp
           >> ONCE_REWRITE_TAC [GSYM SPECIFICATION]
           >> RW_TAC std_ss [IN_IMAGE,IN_UNIV]
           >> METIS_TAC [])
  >> METIS_TAC [extreal_lt_def]);

val RN_lemma2 = store_thm
  ("RN_lemma2",``!m v. measure_space m /\ measure_space v /\
                       (m_space v = m_space m) /\
                       (measurable_sets v = measurable_sets m)
                     /\ measure v (m_space m) <> PosInf
                     /\ measure m (m_space m) <> PosInf
   ==> (?A. A IN measurable_sets m /\
            measure m (m_space m) - measure v (m_space m) <= measure m A - measure v A /\
            !B. B IN measurable_sets m /\
                B SUBSET A ==> 0 <= measure m B - measure v B)``,
  RW_TAC std_ss []
  >> Q.ABBREV_TAC `d = (\a. measure m a - measure v a)`
  >> Q.ABBREV_TAC `p = (\a b n. a IN measurable_sets m /\
                                a SUBSET b /\ d b <= d a /\ (!c. c IN measurable_sets m /\ c SUBSET a ==> -(Normal ((1 / 2) pow n)) < d c))`
  >> Q.ABBREV_TAC `sts = (\s. IMAGE (\A. s INTER A) (measurable_sets m))`
  >> `!s t. s IN measurable_sets m /\ t IN sts s ==> t IN measurable_sets m`
        by (RW_TAC std_ss []
            >> Q.UNABBREV_TAC `sts`
            >> FULL_SIMP_TAC std_ss [IN_IMAGE,MEASURE_SPACE_INTER])
  >> `!s t. t IN sts s ==> t SUBSET s`
        by (RW_TAC std_ss []
            >> Q.UNABBREV_TAC `sts`
            >> FULL_SIMP_TAC std_ss [IN_IMAGE,INTER_SUBSET])
  >> `!s. s IN measurable_sets m ==> measure_space (s, sts s, measure m)` by METIS_TAC [MEASURE_SPACE_RESTRICTED]
  >> `!s. s IN measurable_sets m ==> measure_space (s, sts s, measure v)` by METIS_TAC [MEASURE_SPACE_RESTRICTED]
  >> `!n. 0 < Normal ((1 / 2) pow n)` by METIS_TAC [extreal_lt_eq,extreal_of_num_def,POW_HALF_POS]
  >> `!s. s IN measurable_sets m ==> measure m s <> PosInf` by METIS_TAC [MEASURE_SPACE_FINITE_MEASURE]
  >> `!s. s IN measurable_sets m ==> measure v s <> PosInf` by METIS_TAC [MEASURE_SPACE_FINITE_MEASURE]
  >> `!s. s IN measurable_sets m ==> measure m s <> NegInf` by METIS_TAC [MEASURE_SPACE_POSITIVE,positive_not_infty]
  >> `!s. s IN measurable_sets m ==> measure v s <> NegInf` by METIS_TAC [MEASURE_SPACE_POSITIVE,positive_not_infty]
  >> `!s n. s IN measurable_sets m ==> ?A. p A s n`
         by (RW_TAC std_ss []
             >> `?A. A IN (sts s) /\ measure m s - measure v s <= measure m A - measure v A /\
                (!B. B IN (sts s) /\ B SUBSET A ==>  -Normal ((1 / 2) pow n) < measure m B - measure v B)`
                 by (RW_TAC std_ss []
                     >> (MP_TAC o Q.SPECL [`(s,sts s,measure m)`,`(s,sts s,measure v)`,`Normal ((1 / 2) pow n)`]) RN_lemma1
                     >> RW_TAC std_ss [m_space_def,measure_def,measurable_sets_def])
             >> Q.EXISTS_TAC `A`
             >> Q.UNABBREV_TAC `p`
             >> FULL_SIMP_TAC std_ss [measure_def]
             >> RW_TAC std_ss []
             >| [METIS_TAC [],METIS_TAC [],
                 `A SUBSET s` by METIS_TAC []
                 >> Suff `c IN sts s`
                 >- METIS_TAC []
                 >> Q.UNABBREV_TAC `sts`
                 >> FULL_SIMP_TAC std_ss [IN_IMAGE]
                 >> Q.EXISTS_TAC `c`
                 >> METIS_TAC [SUBSET_INTER2,SUBSET_TRANS]])
  >> Q.ABBREV_TAC `A = PRIM_REC (m_space m) (\a n. @b. p b a n)`
  >> `A 0 = m_space m` by METIS_TAC [PRIM_REC_THM]
  >> `!n. A (SUC n) = @b. p b (A n) n`
        by (Q.UNABBREV_TAC `A` >> RW_TAC std_ss [PRIM_REC_THM])
  >> `!n. A n IN measurable_sets m`
       by (Induct >- METIS_TAC [MEASURE_SPACE_MSPACE_MEASURABLE]
           >> RW_TAC std_ss []
           >> SELECT_ELIM_TAC
           >> FULL_SIMP_TAC std_ss []
           >> METIS_TAC [])
  >> `!n. p (A (SUC n)) (A n) n` by METIS_TAC []
  >> `!n. A (SUC n) SUBSET (A n)` by METIS_TAC []
  >> `!n. d (A n) <= d (A (SUC n))` by METIS_TAC []
  >> `!n c. (c IN measurable_sets m /\ c SUBSET (A (SUC n)) ==> - Normal ((1 / 2) pow n) < d c)` by METIS_TAC []
  >> Q.EXISTS_TAC `BIGINTER (IMAGE A UNIV)`
  >> CONJ_TAC
  >- METIS_TAC [SIGMA_ALGEBRA_FN_BIGINTER,IN_UNIV,IN_FUNSET,subsets_def,measurable_sets_def,measure_space_def]
  >> Reverse CONJ_TAC
  >- (RW_TAC std_ss []
      >> SPOSE_NOT_THEN ASSUME_TAC
      >> FULL_SIMP_TAC std_ss [GSYM extreal_lt_def]
      >> `0 < - (measure m B - measure v B)` by METIS_TAC [lt_neg,neg_0]
      >> `?n. measure m B - measure v B < -Normal ((1 / 2) pow n)` by METIS_TAC [EXTREAL_ARCH_POW_INV,lt_neg,neg_neg]
      >> `d B < -Normal ((1 / 2) pow n)` by METIS_TAC []
      >> `!n. B SUBSET A n` by METIS_TAC [SUBSET_BIGINTER,IN_IMAGE,IN_UNIV]
      >> METIS_TAC [lt_antisym])
  >> `measure m (BIGINTER (IMAGE A UNIV)) = inf (IMAGE (measure m o A) UNIV)`
        by (MATCH_MP_TAC (GSYM MONOTONE_CONVERGENCE_BIGINTER2)
            >> RW_TAC std_ss [IN_UNIV,IN_FUNSET])
  >> `measure v (BIGINTER (IMAGE A UNIV)) = inf (IMAGE (measure v o A) UNIV)`
        by (MATCH_MP_TAC (GSYM MONOTONE_CONVERGENCE_BIGINTER2)
            >> RW_TAC std_ss [IN_UNIV,IN_FUNSET])
  >> `?r1. !n. measure m (A n) = Normal (r1 n)`
       by (Q.EXISTS_TAC `(\n. @r. measure m (A n) = Normal r)`
           >> RW_TAC std_ss []
           >> SELECT_ELIM_TAC
           >> METIS_TAC [extreal_cases])
  >> `?r2. !n. measure v (A n) = Normal (r2 n)`
       by (Q.EXISTS_TAC `(\n. @r. measure v (A n) = Normal r)`
           >> RW_TAC std_ss []
           >> SELECT_ELIM_TAC
           >> METIS_TAC [extreal_cases])
  >> `BIGINTER (IMAGE A UNIV) IN measurable_sets m` by METIS_TAC [MEASURE_SPACE_BIGINTER]
  >> `?l1. measure m (BIGINTER (IMAGE A UNIV)) = Normal l1` by METIS_TAC [extreal_cases]
  >> `?l2. measure v (BIGINTER (IMAGE A UNIV)) = Normal l2` by METIS_TAC [extreal_cases]
  >> FULL_SIMP_TAC std_ss [o_DEF]
  >> Q.PAT_X_ASSUM `Normal l1 = Q` (MP_TAC o GSYM)
  >> Q.PAT_X_ASSUM `Normal l2 = Q` (MP_TAC o GSYM)
  >> RW_TAC std_ss [extreal_sub_def]
  >> `mono_decreasing r1` by METIS_TAC [mono_decreasing_def,mono_decreasing_suc,MEASURE_SPACE_INCREASING,increasing_def,extreal_le_def]
  >> `mono_decreasing r2` by METIS_TAC [mono_decreasing_def,mono_decreasing_suc,MEASURE_SPACE_INCREASING,increasing_def,extreal_le_def,measure_def,measurable_sets_def]
  >> FULL_SIMP_TAC std_ss [GSYM inf_seq]
  >> `!n. -d (A n) = Normal (r2 n - r1 n)`
        by (Q.UNABBREV_TAC `d`
            >> RW_TAC std_ss [extreal_sub_def,extreal_ainv_def,REAL_NEG_SUB])
  >> Q.ABBREV_TAC `r = (\n. r2 n - r1 n)`
  >> `!n. -d (A (SUC n)) <= -d (A n)` by METIS_TAC [le_neg]
  >> `mono_decreasing r` by METIS_TAC [mono_decreasing_suc, extreal_le_def,extreal_ainv_def]
  >> `r --> (l2 - l1)` by (Q.UNABBREV_TAC `r` >> METIS_TAC [SEQ_SUB])
  >> `inf (IMAGE (\n. Normal (r n)) UNIV) = Normal (l2 - l1)` by METIS_TAC [inf_seq]
  >> `inf (IMAGE (\n. -d (A n)) UNIV) = -d (BIGINTER (IMAGE A UNIV))`
        by (`(\n. -d (A n)) = (\n. Normal (r n))` by METIS_TAC []
            >> POP_ORW
            >> Q.UNABBREV_TAC `d`
            >> RW_TAC std_ss [extreal_sub_def,extreal_ainv_def,REAL_NEG_SUB])
  >> FULL_SIMP_TAC std_ss [inf_eq]
  >> `-d (BIGINTER (IMAGE A univ(:num))) <= -d (A 0)`
         by (Q.PAT_X_ASSUM `!y. Q ==> -d (BIGINTER (IMAGE A univ(:num))) <= y` MATCH_MP_TAC
             >> ONCE_REWRITE_TAC [GSYM SPECIFICATION]
             >> RW_TAC std_ss [IN_IMAGE,IN_UNIV]
             >> METIS_TAC [])
  >> `d (m_space m) <= d (BIGINTER (IMAGE A UNIV))` by METIS_TAC [le_neg]
  >> Suff `d (BIGINTER (IMAGE A UNIV)) = Normal (l1 - l2)`
  >- METIS_TAC []
  >> Q.UNABBREV_TAC `d`
  >> METIS_TAC [extreal_sub_def]);

val Radon_Nikodym = store_thm (* rename to: "RADON_NIKODYM_finite_space" *)
  ("Radon_Nikodym",
  ``!m v. measure_space m /\ measure_space v /\ (m_space v = m_space m) /\
         (measurable_sets v = measurable_sets m) /\
          measure v (m_space v) <> PosInf /\
          measure m (m_space m) <> PosInf /\
          measure_absolutely_continuous v m ==>
      ?f. f IN measurable (m_space m, measurable_sets m) Borel /\ (!x. 0 <= f x) /\
          !A. A IN measurable_sets m ==>
              (pos_fn_integral m (\x. f x * indicator_fn A x) = measure v A)``,
    RW_TAC std_ss []
 >> `?f_n. (!n. f_n n IN RADON_F m v) /\ (!x n. f_n n x <= f_n (SUC n) x) /\
           (sup (IMAGE (\n. pos_fn_integral m (f_n n)) univ(:num)) =
            sup (RADON_F_integrals m v))`
       by RW_TAC std_ss [lemma_radon_seq_conv_sup]
  >> Q.ABBREV_TAC `g = (\x. sup (IMAGE (\n. f_n n x) UNIV))`
  >> Q.EXISTS_TAC `g`
  >> `g IN measurable (m_space m,measurable_sets m) Borel`
      by (MATCH_MP_TAC IN_MEASURABLE_BOREL_MONO_SUP
          >> Q.EXISTS_TAC `f_n`
          >> FULL_SIMP_TAC std_ss [RADON_F_def, GSPECIFICATION, measure_space_def, space_def]
          >> Q.UNABBREV_TAC `g`
          >> RW_TAC std_ss [])
  >> `!x. 0 <= g x`
       by (Q.UNABBREV_TAC `g`
           >> RW_TAC std_ss [le_sup]
           >> MATCH_MP_TAC le_trans
           >> Q.EXISTS_TAC `f_n 0 x`
           >> RW_TAC std_ss []
           >- FULL_SIMP_TAC std_ss [RADON_F_def, GSPECIFICATION]
           >> POP_ASSUM MATCH_MP_TAC
           >> ONCE_REWRITE_TAC [GSYM SPECIFICATION]
           >> RW_TAC std_ss [IN_IMAGE, IN_UNIV]
           >> METIS_TAC [])
  >> RW_TAC std_ss []
  >> `!A. A IN measurable_sets m ==>
          (pos_fn_integral m (\x. g x * indicator_fn A x) =
           sup (IMAGE (\n. pos_fn_integral m (\x. f_n n x * indicator_fn A x)) UNIV))`
       by (RW_TAC std_ss []
           >> MATCH_MP_TAC lebesgue_monotone_convergence_subset
           >> FULL_SIMP_TAC std_ss [RADON_F_def, GSPECIFICATION, ext_mono_increasing_suc]
           >> RW_TAC std_ss []
           >> Q.UNABBREV_TAC `g`
           >> METIS_TAC [])
  >> `g IN RADON_F m v`
      by (FULL_SIMP_TAC std_ss [RADON_F_def, GSPECIFICATION, sup_le]
          >> RW_TAC std_ss []
          >> POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
          >> RW_TAC std_ss [IN_IMAGE,IN_UNIV]
          >> METIS_TAC [])
  >> `pos_fn_integral m g = sup (IMAGE (\n:num. pos_fn_integral m (f_n n)) UNIV)`
       by (MATCH_MP_TAC lebesgue_monotone_convergence
           >> FULL_SIMP_TAC std_ss [RADON_F_def, GSPECIFICATION, ext_mono_increasing_suc]
           >> Q.UNABBREV_TAC `g`
           >> METIS_TAC [])
  >> `pos_fn_integral m g = sup (RADON_F_integrals m v)` by FULL_SIMP_TAC std_ss []
  >> Q.ABBREV_TAC `nu = (\A. measure v A - pos_fn_integral m (\x. g x * indicator_fn A x))`
  >> `!A. A IN measurable_sets m ==> pos_fn_integral m (\x. g x * indicator_fn A x) <= measure v A`
       by FULL_SIMP_TAC std_ss [RADON_F_def,GSPECIFICATION]
  >> `!A. A IN measurable_sets m ==> measure v A <> PosInf` by METIS_TAC [lt_infty,INCREASING,MEASURE_SPACE_INCREASING,MEASURE_SPACE_SUBSET_MSPACE,MEASURE_SPACE_MSPACE_MEASURABLE,let_trans]
  >> `!A. A IN measurable_sets m ==> measure m A <> PosInf` by METIS_TAC [lt_infty,INCREASING,MEASURE_SPACE_INCREASING,MEASURE_SPACE_SUBSET_MSPACE,MEASURE_SPACE_MSPACE_MEASURABLE,let_trans]
  >> `!A x. 0 <= (\x. g x * indicator_fn A x) x` by RW_TAC std_ss [indicator_fn_def,mul_rzero,mul_rone,le_01,le_refl]
  >> `!A. A IN measurable_sets m ==> 0 <= pos_fn_integral m (\x. g x * indicator_fn A x)`
          by (rpt STRIP_TAC >> MATCH_MP_TAC pos_fn_integral_pos >> METIS_TAC [])
  >> `!A. A IN measurable_sets m ==> pos_fn_integral m (\x. g x * indicator_fn A x) <> NegInf` by METIS_TAC [lt_infty,extreal_of_num_def,extreal_not_infty,lte_trans]
  >> `!A. A IN measurable_sets m ==> pos_fn_integral m (\x. g x * indicator_fn A x) <> PosInf` by METIS_TAC [let_trans,lt_infty]
  >> `!A. A IN measurable_sets m ==> 0 <= nu A`
       by (RW_TAC std_ss []
           >> FULL_SIMP_TAC std_ss [RADON_F_def,GSPECIFICATION]
           >> `pos_fn_integral m (\x. g x * indicator_fn A' x) <= measure v A'` by FULL_SIMP_TAC std_ss []
           >> `pos_fn_integral m (\x. g x * indicator_fn A' x) <> PosInf` by METIS_TAC [lt_infty,INCREASING,MEASURE_SPACE_INCREASING,MEASURE_SPACE_SUBSET_MSPACE,MEASURE_SPACE_MSPACE_MEASURABLE,let_trans]
           >> Q.UNABBREV_TAC `nu` >> METIS_TAC [sub_zero_le])
  >> `positive (m_space m,measurable_sets m,nu)`
       by (RW_TAC std_ss [positive_def,measure_def,measurable_sets_def]
           >> Q.UNABBREV_TAC `nu`
           >> RW_TAC std_ss [MEASURE_EMPTY,indicator_fn_def,NOT_IN_EMPTY,pos_fn_integral_zero,mul_rzero,mul_rone,sub_rzero])
  >> Q.PAT_X_ASSUM `!A. A IN measurable_sets m ==> (pos_fn_integral m (\x. g x * indicator_fn A x) = Q)` (K ALL_TAC)
  >> RW_TAC std_ss []
  >> `measure_space (m_space m,measurable_sets m,nu)`
      by (FULL_SIMP_TAC std_ss [measure_space_def,m_space_def,measurable_sets_def,countably_additive_def,measure_def]
          >> Q.UNABBREV_TAC `nu`
          >> RW_TAC std_ss [o_DEF]
          >> `suminf (\x. measure v (f x)) = measure v (BIGUNION (IMAGE f univ(:num)))`
               by METIS_TAC [o_DEF,countably_additive_def]
          >> `suminf (\x. measure v (f x)) <> PosInf` by METIS_TAC []
          >> `suminf (\x. measure v (f x) - pos_fn_integral m (\x'. g x' * indicator_fn (f x) x')) =
              suminf (\x. measure v (f x)) - suminf (\x. pos_fn_integral m (\x'. g x' * indicator_fn (f x) x'))`
                by  (`(\x. measure v (f x) - pos_fn_integral m (\x'. g x' * indicator_fn (f x) x')) =
                      (\x. (\x. measure v (f x)) x - (\x. pos_fn_integral m (\x'. g x' * indicator_fn (f x) x')) x)`
                         by METIS_TAC []
                     >> POP_ORW
                     >> MATCH_MP_TAC ext_suminf_sub
                     >> RW_TAC std_ss []
                     >- (MATCH_MP_TAC pos_fn_integral_pos
                         >> RW_TAC std_ss [indicator_fn_def,mul_rzero,mul_rone,le_refl]
                         >> METIS_TAC [measure_space_def,countably_additive_def])
                     >> METIS_TAC [IN_FUNSET,IN_UNIV])
          >> POP_ORW
          >> Suff `pos_fn_integral m (\x. g x * indicator_fn (BIGUNION (IMAGE f univ(:num))) x) =
                   suminf (\x. pos_fn_integral m (\x'. g x' * indicator_fn (f x) x'))`
          >- RW_TAC std_ss []
          >> `measure_space m` by METIS_TAC [measure_space_def,countably_additive_def]
          >> `(!i x. 0 <= (\i x. g x * indicator_fn (f i) x) i x)` by RW_TAC std_ss [mul_rzero,mul_rone,indicator_fn_def,le_refl]
          >> `(!i. (\i x. g x * indicator_fn (f i) x) i IN measurable (m_space m,measurable_sets m) Borel)`
               by (RW_TAC std_ss []
                   >> METIS_TAC [IN_MEASURABLE_BOREL_MUL_INDICATOR,IN_FUNSET,IN_UNIV,measurable_sets_def,subsets_def])
          >> (MP_TAC o Q.SPECL [`m`,`(\i:num. (\x. g x * indicator_fn (f i) x))`]) pos_fn_integral_suminf
          >> RW_TAC std_ss []
          >> POP_ASSUM (MP_TAC o GSYM)
          >> RW_TAC std_ss []
          >> Suff `(\x. g x * indicator_fn (BIGUNION (IMAGE f univ(:num))) x) =
                   (\x'. suminf (\x. g x' * indicator_fn (f x) x'))`
          >- RW_TAC std_ss []
          >> RW_TAC std_ss [FUN_EQ_THM]
          >> `suminf (\x. g x' * (\x. indicator_fn (f x) x') x) = g x' * suminf (\x. indicator_fn (f x) x')`
              by (MATCH_MP_TAC ext_suminf_cmul
                  >> RW_TAC std_ss [mul_rone,mul_rzero,le_refl,indicator_fn_def,le_01])
          >> FULL_SIMP_TAC std_ss []
          >> Suff `suminf (\i. indicator_fn (f i) x') = indicator_fn (BIGUNION (IMAGE f univ(:num))) x'`
          >- RW_TAC std_ss []
          >> FULL_SIMP_TAC std_ss [indicator_fn_suminf])
  >> `!A. A IN measurable_sets m ==> nu A <= nu (m_space m)` by METIS_TAC [MEASURE_SPACE_INCREASING,INCREASING,MEASURE_SPACE_SUBSET_MSPACE,measure_def,measurable_sets_def,m_space_def,MEASURE_SPACE_MSPACE_MEASURABLE]
  >> Cases_on `nu A = 0` >- METIS_TAC [sub_0]
  >> `0 < nu A` by METIS_TAC [lt_le,MEASURE_SPACE_POSITIVE,positive_def]
  >> `0 < nu (m_space m)` by METIS_TAC [lte_trans]
  >> `0 <> measure m (m_space m)`
       by (SPOSE_NOT_THEN ASSUME_TAC
           >> `measure v (m_space m) = 0` by METIS_TAC [MEASURE_SPACE_MSPACE_MEASURABLE,measure_absolutely_continuous_def]
           >> `pos_fn_integral m (\x. g x * indicator_fn (m_space m) x) <= 0` by METIS_TAC [MEASURE_SPACE_MSPACE_MEASURABLE]
           >> `pos_fn_integral m (\x. g x * indicator_fn (m_space m) x) =  0` by METIS_TAC [le_antisym,MEASURE_SPACE_MSPACE_MEASURABLE]
           >> `nu (m_space m) = 0` by (Q.UNABBREV_TAC `nu` >> METIS_TAC [sub_rzero])
           >> METIS_TAC [lt_imp_ne])
  >> `0 < measure m (m_space m)` by METIS_TAC [lt_le,MEASURE_SPACE_POSITIVE,positive_def,MEASURE_SPACE_MSPACE_MEASURABLE]
  >> Q.ABBREV_TAC `z = nu (m_space m) / (2 * measure m (m_space m)) `
  >> `nu (m_space m) <> NegInf` by METIS_TAC [lt_trans,lt_infty,num_not_infty]
  >> `measure m (m_space m) <> NegInf` by METIS_TAC [lt_trans,lt_infty,num_not_infty]
  >> `nu (m_space m) <> PosInf`
       by (Q.UNABBREV_TAC `nu`
           >> RW_TAC std_ss []
           >> METIS_TAC [sub_not_infty,MEASURE_SPACE_MSPACE_MEASURABLE])
  >> `?e. 0 < e /\ (z = Normal e)`
       by (Q.UNABBREV_TAC `z`
           >> `?r1. nu (m_space m) = Normal r1` by METIS_TAC [extreal_cases]
           >> `?r2. measure m (m_space m) = Normal r2` by METIS_TAC [extreal_cases]
           >> RW_TAC std_ss [extreal_mul_def,extreal_of_num_def]
           >> `0 < r1` by METIS_TAC [extreal_of_num_def,extreal_lt_eq]
           >> `0 < r2` by METIS_TAC [extreal_of_num_def,extreal_lt_eq]
           >> `0 < 2 * r2` by RW_TAC real_ss [REAL_LT_MUL]
           >> FULL_SIMP_TAC std_ss [extreal_div_eq,REAL_LT_IMP_NE]
           >> `0 < r1 / (2 * r2)` by RW_TAC std_ss [REAL_LT_DIV]
           >> METIS_TAC [])
  >> Q.ABBREV_TAC `snu = (\A. nu A - Normal e * (measure m A))`
  >> `?A'. A' IN measurable_sets m /\ snu(m_space m) <= snu (A') /\
       (!B. B IN measurable_sets m /\ B SUBSET A' ==> 0 <= snu (B))`
        by (Q.UNABBREV_TAC `snu`
            >> RW_TAC std_ss []
            >> (MP_TAC o Q.SPECL [`(m_space m, measurable_sets m, nu)`,`(m_space m, measurable_sets m, (\A. Normal e * measure m A))`]) RN_lemma2
            >> RW_TAC std_ss [m_space_def,measurable_sets_def,measure_def]
            >> METIS_TAC [MEASURE_SPACE_CMUL,REAL_LT_IMP_LE,mul_not_infty,extreal_not_infty])
  >> Q.ABBREV_TAC `g' = (\x. g x + Normal e * indicator_fn (A') x)`
  >> `!A. A IN measurable_sets m ==>
          (pos_fn_integral m (\x. g' x * indicator_fn A x) =
           pos_fn_integral m (\x. g x * indicator_fn A x) + Normal e * measure m (A INTER A'))`
       by (rpt STRIP_TAC
           >> `measure m (A'' INTER A') = pos_fn_integral m (indicator_fn (A'' INTER A'))`
                by METIS_TAC [pos_fn_integral_indicator,MEASURE_SPACE_INTER]
           >> POP_ORW
           >> `Normal e * pos_fn_integral m (indicator_fn (A'' INTER A')) =
               pos_fn_integral m (\x. Normal e * indicator_fn (A'' INTER A') x)`
                by ((MATCH_MP_TAC o GSYM) pos_fn_integral_cmul
                    >> RW_TAC real_ss [REAL_LT_IMP_LE,indicator_fn_def,le_01,le_refl])
           >> POP_ORW
           >> Q.UNABBREV_TAC `g'`
           >> `(\x. (\x. g x + Normal e * indicator_fn A' x) x * indicator_fn A'' x) =
               (\x. (\x. g x * indicator_fn A'' x) x + (\x. Normal e * indicator_fn (A'' INTER A') x) x)`
                by (RW_TAC std_ss [FUN_EQ_THM,indicator_fn_def,IN_INTER]
                    >> METIS_TAC [mul_rone,mul_rzero,add_rzero,indicator_fn_def,IN_INTER])
           >> POP_ORW
           >> MATCH_MP_TAC pos_fn_integral_add
           >> FULL_SIMP_TAC std_ss []
           >> CONJ_TAC >- (RW_TAC std_ss [indicator_fn_def,le_01,le_refl,mul_rone,mul_rzero]
                           >> FULL_SIMP_TAC std_ss [extreal_of_num_def,extreal_le_def,REAL_LT_IMP_LE])
           >> RW_TAC std_ss []
           >- METIS_TAC [IN_MEASURABLE_BOREL_MUL_INDICATOR, measure_space_def,
                         measurable_sets_def, subsets_def]
           >> MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL
           >> RW_TAC std_ss []
           >> Q.EXISTS_TAC `indicator_fn (A'' INTER A')`
           >> Q.EXISTS_TAC `e`
           >> RW_TAC std_ss []
           >- FULL_SIMP_TAC std_ss [measure_space_def]
           >> MATCH_MP_TAC IN_MEASURABLE_BOREL_INDICATOR
           >> METIS_TAC [measure_space_def,measurable_sets_def,subsets_def,MEASURE_SPACE_INTER,space_def])
  >> `!A. A IN measurable_sets m ==> ((A INTER A') IN measurable_sets m /\ (A INTER A') SUBSET A')`
         by METIS_TAC [INTER_SUBSET,MEASURE_SPACE_INTER]
  >> `!A. A IN measurable_sets m ==> 0 <= nu (A INTER A') - Normal e * measure m (A INTER A')`
         by (Q.UNABBREV_TAC `snu` >> METIS_TAC [])
  >> `!A. A IN measurable_sets m ==> Normal e * measure m (A INTER A') <= nu (A INTER A')`
         by (RW_TAC std_ss []
             >> `Normal e * measure m (A'' INTER A') <> PosInf`
                  by FULL_SIMP_TAC std_ss [mul_not_infty,REAL_LT_IMP_LE,MEASURE_SPACE_INTER]
             >> `Normal e * measure m (A'' INTER A') <> NegInf`
                  by METIS_TAC [mul_not_infty,REAL_LT_IMP_LE,MEASURE_SPACE_INTER,MEASURE_SPACE_POSITIVE,positive_not_infty]
             >> METIS_TAC [sub_zero_le])
  >> `!A. A IN measurable_sets m ==>
          pos_fn_integral m (\x. g x * indicator_fn A x) + Normal e * measure m (A INTER A') <=
          pos_fn_integral m (\x. g x * indicator_fn A x) + nu (A INTER A')`
         by METIS_TAC [le_ladd_imp]
  >> `!A. A IN measurable_sets m ==> nu (A INTER A') <= nu A`
         by (RW_TAC std_ss []
             >> (MATCH_MP_TAC o REWRITE_RULE [measurable_sets_def,measure_def] o Q.SPEC `(m_space m,measurable_sets m,nu)`) INCREASING
             >> METIS_TAC [MEASURE_SPACE_INCREASING,MEASURE_SPACE_INTER,INTER_SUBSET])
  >> `!A. A IN measurable_sets m ==>
          pos_fn_integral m (\x. g x * indicator_fn A x) + Normal e * measure m (A INTER A') <=
          pos_fn_integral m (\x. g x * indicator_fn A x) + nu (A)`
           by METIS_TAC [le_ladd_imp,le_trans]
  >> `!A. A IN measurable_sets m ==>
          pos_fn_integral m (\x. g x * indicator_fn A x) + Normal e * measure m (A INTER A') <= measure v A`
           by (Q.UNABBREV_TAC `nu`
               >> FULL_SIMP_TAC std_ss []
               >> RW_TAC std_ss []
               >> METIS_TAC [sub_add2])
  >> `!A. A IN measurable_sets m ==> pos_fn_integral m (\x. g' x * indicator_fn A x) <= measure v A`
        by METIS_TAC []
  >> `g' IN RADON_F m v`
         by (RW_TAC std_ss [RADON_F_def,GSPECIFICATION]
             >- (Q.UNABBREV_TAC `g'`
                 >> MATCH_MP_TAC IN_MEASURABLE_BOREL_ADD
                 >> Q.EXISTS_TAC `g`
                 >> Q.EXISTS_TAC `(\x. Normal e * indicator_fn A' x)`
                 >> CONJ_TAC >- FULL_SIMP_TAC std_ss [measure_space_def]
                 >> FULL_SIMP_TAC std_ss []
                 >> CONJ_TAC
                 >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL
                     >> METIS_TAC [measure_space_def,subsets_def,measurable_sets_def,IN_MEASURABLE_BOREL_INDICATOR])
                 >> RW_TAC std_ss [indicator_fn_def,mul_rone,mul_rzero,num_not_infty,space_def]
                 >> METIS_TAC [lt_infty,lte_trans,num_not_infty])
             >> Q.UNABBREV_TAC `g'`
             >> RW_TAC std_ss [indicator_fn_def, mul_rone, mul_rzero, add_rzero]
             >> METIS_TAC [le_add2, add_rzero, le_trans, lt_imp_le, extreal_lt_eq,
                           extreal_of_num_def])
  >> `pos_fn_integral m g' IN RADON_F_integrals m v`
       by (FULL_SIMP_TAC std_ss [RADON_F_integrals_def, GSPECIFICATION]
           >> METIS_TAC [])
  >> `pos_fn_integral m (\x. g' x * indicator_fn (m_space m) x) =
      pos_fn_integral m (\x. g x * indicator_fn (m_space m) x) +
      Normal e * measure m A'`
         by METIS_TAC [MEASURE_SPACE_MSPACE_MEASURABLE,MEASURE_SPACE_SUBSET_MSPACE,SUBSET_INTER2]
  >> `!x. 0 <= g' x`
      by (Q.UNABBREV_TAC `g'`
          >> RW_TAC std_ss [indicator_fn_def,mul_rone,mul_rzero,add_rzero]
          >> METIS_TAC [le_add2,add_rzero,le_trans,lt_imp_le,extreal_lt_eq,extreal_of_num_def])
  >> `pos_fn_integral m g' = pos_fn_integral m g + Normal e * measure m A'`
       by METIS_TAC [pos_fn_integral_mspace]
  >> `0 < snu (m_space m)`
       by (Q.UNABBREV_TAC `snu`
           >> RW_TAC std_ss []
           >> `?r1. nu (m_space m) = Normal r1` by METIS_TAC [extreal_cases]
           >> `?r2. measure m (m_space m) = Normal r2` by METIS_TAC [extreal_cases]
           >> `0 < r1` by METIS_TAC [extreal_of_num_def,extreal_lt_eq]
           >> `0 < r2` by METIS_TAC [extreal_of_num_def,extreal_lt_eq]
           >> `0 < 2 * r2` by RW_TAC real_ss [REAL_LT_MUL]
           >> `Normal e = nu (m_space m) / (2 * measure m (m_space m))` by RW_TAC std_ss []
           >> POP_ORW
           >> REWRITE_TAC [extreal_of_num_def]
           >> FULL_SIMP_TAC std_ss [extreal_mul_def,extreal_div_eq,REAL_LT_IMP_NE,extreal_sub_def,extreal_lt_eq]
           >> RW_TAC real_ss [real_div,REAL_INV_MUL,REAL_LT_IMP_NE,REAL_MUL_ASSOC]
           >> `inv 2 * inv r2 * r2 = inv 2` by METIS_TAC [REAL_LT_IMP_NE,REAL_MUL_LINV,REAL_MUL_ASSOC,REAL_MUL_RID]
           >> `r1 - r1 * inv 2 * inv r2 * r2 = r1 / 2` by METIS_TAC [REAL_NEG_HALF,real_div,REAL_MUL_ASSOC]
           >> FULL_SIMP_TAC real_ss [REAL_LT_DIV])
  >> `0 < snu A'` by METIS_TAC [lte_trans]
  >> `Normal e * measure m A' <> PosInf` by METIS_TAC [REAL_LT_IMP_LE,mul_not_infty]
  >> `Normal e * measure m A' <> NegInf` by METIS_TAC [REAL_LT_IMP_LE,mul_not_infty,MEASURE_SPACE_POSITIVE,positive_not_infty]
  >> `Normal e * measure m A' < nu (A')` by METIS_TAC [sub_zero_lt2]
  >> `0 <= Normal e * measure m A'` by METIS_TAC [le_mul,REAL_LT_IMP_LE,extreal_le_def,MEASURE_SPACE_POSITIVE,positive_def,extreal_of_num_def]
  >> `0 < nu A'` by METIS_TAC [let_trans]
  >> `0 <> measure m A'`
        by (SPOSE_NOT_THEN ASSUME_TAC
            >> `measure v A' = 0` by METIS_TAC [MEASURE_SPACE_MSPACE_MEASURABLE,measure_absolutely_continuous_def]
            >> `pos_fn_integral m (\x. g x * indicator_fn A' x) <= 0` by METIS_TAC []
            >> `pos_fn_integral m (\x. g x * indicator_fn A' x) =  0` by METIS_TAC [le_antisym]
            >> `nu A' = 0` by (Q.UNABBREV_TAC `nu` >> METIS_TAC [sub_rzero])
            >> METIS_TAC [lt_imp_ne])
  >> `0 < measure m A'` by METIS_TAC [lt_le,MEASURE_SPACE_POSITIVE,positive_def,MEASURE_SPACE_MSPACE_MEASURABLE]
  >> `0 < Normal e * measure m A'` by METIS_TAC [lt_mul,extreal_lt_eq,extreal_of_num_def]
  >> `pos_fn_integral m g <> NegInf` by METIS_TAC [pos_fn_integral_pos,lt_infty,num_not_infty,lte_trans]
  >> `pos_fn_integral m g <> PosInf` by METIS_TAC [MEASURE_SPACE_MSPACE_MEASURABLE,pos_fn_integral_mspace]
  >> `pos_fn_integral m g < pos_fn_integral m g'` by METIS_TAC [let_add2,le_refl,num_not_infty,add_rzero]
  >> `pos_fn_integral m g' <= pos_fn_integral m g` by METIS_TAC [le_sup_imp,SPECIFICATION]
  >> METIS_TAC [extreal_lt_def]);

(* NOTE: comparing with Radon_Nikodym, this theorem
         added: `(!x. f x <> PosInf)`, removed: `measure m (m_space m) <> PosInf`
 *)
val Radon_Nikodym2 = store_thm
  ("Radon_Nikodym2",
  ``!m v. measure_space m /\ measure_space v /\ (m_space v = m_space m) /\
         (measurable_sets v = measurable_sets m) /\
          measure_absolutely_continuous v m ==>
      ?f. f IN measurable (m_space m,measurable_sets m) Borel /\
          (!x. 0 <= f x) /\ (!x. f x <> PosInf) /\
          !A. A IN measurable_sets m ==>
              (pos_fn_integral m (\x. f x * indicator_fn A x) = measure v A)``,
  RW_TAC std_ss []
  >> `?g. g IN measurable (m_space m,measurable_sets m) Borel /\
          (!x. 0 <= g x) /\
          (!A. A IN measurable_sets m ==>
               (pos_fn_integral m (\x. g x * indicator_fn A x) = Normal (measure v A)))`
      by METIS_TAC [Radon_Nikodym]
  >> Q.EXISTS_TAC `\x. if g x = PosInf then 0 else g x`
  >> RW_TAC std_ss [le_refl,num_not_infty]
  >- (`integrable m g` by METIS_TAC [integrable_pos, pos_fn_integral_mspace,
                                     MEASURE_SPACE_MSPACE_MEASURABLE, extreal_not_infty]
      >> METIS_TAC [integrable_not_infty_alt2, integrable_def])
  >> `pos_fn_integral m (\x. g x * indicator_fn A x) = Normal (measure v A)` by METIS_TAC []
  >> `!x. 0 <= g x * indicator_fn A x` by METIS_TAC [indicator_fn_def,mul_rzero,le_refl,mul_rone]
  >> `integrable m (\x. g x * indicator_fn A x)`
      by (MATCH_MP_TAC integrable_bounded
          >> Q.EXISTS_TAC `g`
          >> RW_TAC std_ss []
          >|[METIS_TAC [integrable_pos,pos_fn_integral_mspace,MEASURE_SPACE_MSPACE_MEASURABLE,
                        extreal_not_infty],
             METIS_TAC [IN_MEASURABLE_BOREL_MUL_INDICATOR, measurable_sets_def, measure_space_def,
                        subsets_def],
             METIS_TAC [abs_refl, mul_rone, mul_rzero, le_refl, indicator_fn_def]])
  >> (MP_TAC o Q.SPECL [`m`,`(\x. g x * indicator_fn A x)`]) integrable_not_infty_alt2
  >> Suff `(\x. (if g x = PosInf then 0 else g x) * indicator_fn A x) =
           (\x. if g x * indicator_fn A x = PosInf then 0 else g x * indicator_fn A x)`
  >- RW_TAC std_ss []
  >> RW_TAC std_ss [FUN_EQ_THM]
  >> METIS_TAC [mul_lzero,mul_rzero,mul_lone,mul_rone,num_not_infty,indicator_fn_def]);
*)

val _ = export_theory ();

(* References:

  [1] Schilling, R.L.: Measures, Integrals and Martingales (Second Edition).
      Cambridge University Press (2017).
  [2] Doob, J.L.: Stochastic processes. Wiley-Interscience (1990).
  [3] Doob, J.L.: What is a Martingale? Amer. Math. Monthly. 78(5), 451-463 (1971).
  [4] Pintacuda, N.: Probabilita'. Zanichelli, Bologna (1995).
 *)
