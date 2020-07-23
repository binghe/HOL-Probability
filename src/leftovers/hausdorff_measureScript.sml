(* ------------------------------------------------------------------------- *)
(* Metric Outer Measure Space and Hausdorff Measure                          *)
(*                                                                           *)
(* Author: Chun Tian (2019)                                                  *)
(* Fondazione Bruno Kessler and University of Trento, Italy                  *)
(* ------------------------------------------------------------------------- *)

open HolKernel Parse boolLib bossLib;

open pred_setTheory combinTheory topologyTheory metricTheory realTheory
     hurdUtils util_probTheory real_topologyTheory;

open extrealTheory sigma_algebraTheory measureTheory;

val _ = new_theory "hausdorff_measure";

(* ------------------------------------------------------------------------- *)
(*  Metric outer measure space                                               *)
(* ------------------------------------------------------------------------- *)

(* c.f. `diameter` in real_topologyTheory, now with a parameter d *)
val set_diameter_def = Define
   `set_diameter (d :'a metric) (s :'a set) =
      if s = {} then (0 :real)
      else sup {dist d (x,y) | x IN s /\ y IN s}`;

(* c.f. `setdist` in real_topologyTheory, now with a parameter `d` *)
val set_dist_def = Define
   `set_dist (d :'a metric) ((s,t) :'a set # 'a set) =
      if (s = {}) \/ (t = {}) then (0 :real)
      else inf {dist d (x,y) | x IN s /\ y IN t}`;

val _ = overload_on ("diameter", ``set_diameter``);
val _ = overload_on ("dist",     ``set_dist``);

(* (OM4) in Theorem 18.5 [1] *)
val metric_additive_def = Define
   `metric_additive (d :'a metric) (m :'a m_space) =
      !s t. s IN measurable_sets m /\ t IN measurable_sets m /\
            s UNION t IN measurable_sets m /\ 0 < (dist d) (s,t)
        ==> (measure m (s UNION t) = measure m s + measure m t)`;

(* `metric_outer_measure_space (sp,POW sp,u) d` is more often used *)
val metric_outer_measure_space_def = Define
   `metric_outer_measure_space d m <=>
           outer_measure_space m /\ metric_additive d m`;

(* Definition 18.4 [1] (countable diameter-restrict covering)
   c.f. countable_covers_def in measureTheory)
 *)
val countable_e_covers_def = Define
   `countable_e_covers (sts :'a set set) (d :'a metric) (e :real) =
      \a. {f | f IN (univ(:num) -> sts) /\ (!i. diameter d (f i) <= e) /\
               a SUBSET (BIGUNION (IMAGE f UNIV))}`;

(* Definition 18.4 [1] (metric outer measure) *)
val metric_outer_measure_def = Define
   `metric_outer_measure (d :'a metric) (m :'a m_space) =
      \a. sup {r | ?e. 0 < e /\
                      (r = outer_measure (measure m)
                             (countable_e_covers (measurable_sets m) d e) a)}`;

val rich_system_def = Define
   `rich_system sp sts (d :'a metric) <=>
      subset_class sp sts /\ {} IN sts /\
      !x e. x IN sp /\ 0 < e ==> ?s. x IN s /\ s IN sts /\ diameter d s < e`;

Theorem coutable_e_covers_empty :
    !u sts d e. (!s. s IN sts ==> 0 <= u s) /\ {} IN sts /\
                (u {} = 0) /\ 0 < e ==>
                outer_measure u (countable_e_covers sts d e) {} = 0
Proof
    RW_TAC std_ss [outer_measure_def]
 >> ONCE_REWRITE_TAC [GSYM le_antisym]
 >> Reverse CONJ_TAC
 >- (RW_TAC std_ss [le_inf', GSPECIFICATION] \\
     MATCH_MP_TAC ext_suminf_pos >> RW_TAC std_ss [o_DEF] \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     fs [countable_e_covers_def, GSPECIFICATION, IN_FUNSET, IN_UNIV])
 >> RW_TAC std_ss [inf_le', GSPECIFICATION]
 >> POP_ASSUM MATCH_MP_TAC
 >> Q.EXISTS_TAC `\n. {}`
 >> RW_TAC std_ss [countable_e_covers_def, GSPECIFICATION, IN_FUNSET, IN_UNIV]
 >| [ (* goal 1 (of 3) *)
      rw [set_diameter_def] \\
      IMP_RES_TAC REAL_LT_IMP_LE,
      (* goal 2 (of 3) *)
      rw [SUBSET_DEF, NOT_IN_EMPTY],
      (* goal 3 (of 3) *)
      MATCH_MP_TAC ext_suminf_zero >> rw [] ]
QED

(* TODO: move to sigma_algebraTheory, not used any more *)
Theorem algebra_decomposition :
    !(a :'a algebra). ?sp sts. (space a = sp) /\ (subsets a = sts)
Proof
    GEN_TAC >> Cases_on `a`
 >> take [`q`, `r`]
 >> rw [space_def, subsets_def]
QED

(* TODO: move to measureTheory, not used any more *)
Theorem measure_space_decomposition :
    !(m :'a m_space). ?sp sts u. (m_space m = sp) /\
                                 (measurable_sets m = sts) /\
                                 (measure m = u)
Proof
    GEN_TAC >> Cases_on `m` >> Cases_on `r`
 >> take [`q`, `q'`, `r'`]
 >> rw [m_space_def, measurable_sets_def, measure_def]
QED

Theorem METRIC_OUTER_MEASURE_EMPTY :
    !sp sts u d. subset_class sp sts /\ {} IN sts /\ positive (sp,sts,u) ==>
                 (metric_outer_measure d (sp,sts,u) {} = 0)
Proof
    RW_TAC std_ss [metric_outer_measure_def, positive_def,
                   measure_def, measurable_sets_def]
 >> RW_TAC std_ss [sup_eq', GSPECIFICATION]
 >- PROVE_TAC [coutable_e_covers_empty, le_refl]
 >> POP_ASSUM MATCH_MP_TAC
 >> Q.EXISTS_TAC `1` >> REWRITE_TAC [REAL_LT_01]
 >> MATCH_MP_TAC EQ_SYM
 >> MATCH_MP_TAC coutable_e_covers_empty >> rw [REAL_LT_01]
QED

Theorem METRIC_OUTER_MEASURE_POSITIVE :
    !sp sts u d. subset_class sp sts /\ {} IN sts /\ positive (sp,sts,u) ==>
                 !s. s SUBSET sp ==> 0 <= metric_outer_measure d (sp,sts,u) s
Proof
    RW_TAC std_ss [metric_outer_measure_def, positive_def,
                   measure_def, measurable_sets_def]
 >> RW_TAC std_ss [le_sup', GSPECIFICATION]
 >> MATCH_MP_TAC le_trans
 >> Q.EXISTS_TAC `outer_measure u (countable_e_covers sts d 1) s`
 >> Reverse CONJ_TAC
 >- (POP_ASSUM MATCH_MP_TAC \\
     Q.EXISTS_TAC `1` >> rw [REAL_LT_01])
 >> POP_ASSUM K_TAC
 >> RW_TAC std_ss [outer_measure_def, le_inf', GSPECIFICATION]
 >> MATCH_MP_TAC ext_suminf_pos >> RW_TAC std_ss [o_DEF]
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> fs [countable_e_covers_def, GSPECIFICATION, IN_FUNSET, IN_UNIV]
QED

(* Theorem 18.5 [1] *)
Theorem METRIC_OUTER_MEASURE_CONSTRUCTION :
    !sp sts d u v. rich_system sp sts d /\ positive (sp,sts,u) /\
                   (v = metric_outer_measure d (sp,sts,u))
               ==> metric_outer_measure_space d (sp,POW sp,v)
Proof
    rpt STRIP_TAC
 >> REWRITE_TAC [metric_outer_measure_space_def]
 >> STRONG_CONJ_TAC
 >- (RW_TAC std_ss [outer_measure_space_def, m_space_def, measurable_sets_def,
                    subset_class_POW, EMPTY_IN_POW] >| (* 3 subgoals *)
     [ (* goal 1 (of 3) *)
       RW_TAC std_ss [positive_def, measure_def, measurable_sets_def, IN_POW]
       >- (MATCH_MP_TAC METRIC_OUTER_MEASURE_EMPTY \\
           fs [rich_system_def]) \\
       irule METRIC_OUTER_MEASURE_POSITIVE >> fs [rich_system_def],
       (* goal 2 (of 3) *)
       
       cheat,
       (* goal 3 (of 3) *)
       cheat ])
 >> cheat
QED

(* Lemma 18.6 (Caratheodory) [1]: CARATHEODORY_LEMMA *)

(* Theorem 18.7 [1]: HAUSDORFF_MEASURE *)

val _ = export_theory ();

(* References:

  [1] Schilling, R.L.: Measures, Integrals and Martingales (Second Edition).
      Cambridge University Press (2017).
 *)
