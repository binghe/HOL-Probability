(* ------------------------------------------------------------------------- *)
(* Metric Outer Measure Space and Hausdorff Measure                          *)
(*                                                                           *)
(* Author: Chun Tian (2019)                                                  *)
(* Fondazione Bruno Kessler and University of Trento, Italy                  *)
(* ------------------------------------------------------------------------- *)

open HolKernel Parse boolLib bossLib;

open pred_setTheory fcpTheory topologyTheory metricTheory real_topologyTheory;

open hurdUtils util_probTheory extrealTheory sigma_algebraTheory measureTheory
     borelTheory;

val _ = new_theory "hausdorff_measure";

(* ------------------------------------------------------------------------- *)
(*  Metric outer measure space                                               *)
(* ------------------------------------------------------------------------- *)

val set_diameter_def = Define (* c.f. `diameter` in real_topologyTheory *)
   `set_diameter (d :'a metric) (s :'a set) =
      if s = {} then 0
      else sup {dist d (x,y) | x IN s /\ y IN s}`;

val set_dist_def = Define     (* c.f. `setdist` in real_topologyTheory *)
   `set_dist (d :'a metric) ((s,t) :'a set # 'a set) =
      if (s = {}) \/ (t = {}) then 0
      else inf {dist d (x,y) | x IN s /\ y IN t}`;

val _ = overload_on ("diameter", ``set_diameter``);
val _ = overload_on ("dist",     ``set_dist``);

(* (OM4) in Theorem 18.5 [1] *)
val metric_additive_def = Define
   `metric_additive (m :'a m_space) (d :'a metric) =
    !s t. s IN measurable_sets m /\ t IN measurable_sets m /\
          s UNION t IN measurable_sets m /\ 0 < (dist d) (s,t)
      ==> (measure m (s UNION t) = measure m s + measure m t)`;

(* `metric_outer_measure_space (sp,POW sp,u) d` is more often used *)
val metric_outer_measure_space_def = Define
   `metric_outer_measure_space m d <=> outer_measure_space m /\ metric_additive m d`;

(* Definition 18.4 [1] (countable diameter-restrict covering)
   c.f. countable_covers_def in measureTheory)
 *)
val countable_d_covers_def = Define
   `countable_d_covers (sts :'a set set) (d :'a metric) (e :real) =
      \a. {f | f IN (univ(:num) -> sts) /\ a SUBSET (BIGUNION (IMAGE f UNIV)) /\
               !i. diameter d (f i) <= e}`;

(* Definition 18.4 [1] (metric outer measure) *)
val metric_outer_measure_def = Define
   `metric_outer_measure (m :'a m_space) (d :'a metric) =
      \a. sup {r | ?e. 0 < e /\
                      (r = outer_measure (measure m)
                                         (countable_d_covers (measurable_sets m) d e) a)}`;

val rich_system_def = Define
   `rich_system (a :'a algebra) (d :'a metric) <=>
      !x e. x IN (space a) /\ 0 < e ==> ?s. x IN s /\ s IN (subsets a) /\ diameter d s < e`;

val _ = type_abbrev ("metric_space", ``:'a set # 'a metric``);

(* Theorem 18.5 [1], c.f. measureTheory.MUNROE_METHOD_I *)
Theorem MUNROE_METHOD_II :
    !sp sts m u d. subset_class sp sts /\ {} IN sts /\ positive (sp,sts,m) /\
                   (u = metric_outer_measure (sp,sts,m) d) /\ rich_system (sp,sts) d
               ==> metric_outer_measure_space (sp,POW sp,u) d
Proof
    rpt STRIP_TAC
 >> REWRITE_TAC [metric_outer_measure_space_def]
 >> STRONG_CONJ_TAC
 >- (RW_TAC std_ss [outer_measure_space_def, m_space_def, measurable_sets_def,
                    subset_class_POW, IN_POW] >| (* 4 subgoals here *)
     [ (* goal 1 (of 4) *)
       fs [subset_class_def],
       (* goal 2 (of 4) *)
       cheat,
       cheat,
       cheat ])
 >> cheat
QED

val _ = export_theory ();

(* References:

  [1] Schilling, R.L.: Measures, Integrals and Martingales (Second Edition).
      Cambridge University Press (2017).
 *)
