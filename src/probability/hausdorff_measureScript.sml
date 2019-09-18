(* ------------------------------------------------------------------------- *)
(* Metric Outer Measure Space and Hausdorff Measure                          *)
(*                                                                           *)
(* Author: Chun Tian (2019)                                                  *)
(* Fondazione Bruno Kessler and University of Trento, Italy                  *)
(* ------------------------------------------------------------------------- *)

open HolKernel Parse boolLib bossLib;

open pred_setTheory combinTheory fcpTheory topologyTheory metricTheory
     real_topologyTheory;

open hurdUtils util_probTheory extrealTheory sigma_algebraTheory measureTheory
     borelTheory;

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

Theorem OUTER_MEASURE_EMPTY :
    !mu sts d e. outer_measure mu (countable_e_covers sts d e) {} = 0
Proof
    RW_TAC std_ss [outer_measure_def]
 >> ONCE_REWRITE_TAC [GSYM le_antisym]
 >> Reverse CONJ_TAC
 >- (REWRITE_TAC [le_inf'] \\
     RW_TAC std_ss [GSPECIFICATION] \\
     cheat)
 >> cheat
QED

Theorem METRIC_OUTER_MEASURE_EMPTY :
    !d m. metric_outer_measure d m {} = 0
Proof
    cheat
QED

Theorem METRIC_OUTER_MEASURE_POSITIVE :
    !d m s. 0 <= metric_outer_measure d m s
Proof
    cheat
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
                    subset_class_POW, EMPTY_IN_POW]
  (* OM1 *)
     >- (RW_TAC std_ss [positive_def, measure_def, measurable_sets_def]
         >- art [METRIC_OUTER_MEASURE_EMPTY] \\
         rw [METRIC_OUTER_MEASURE_POSITIVE]) \\
  (* OM2, OM3 *)
     cheat)
 >> cheat
QED

(* Lemma 18.6 (Caratheodory) [1]: CARATHEODORY_LEMMA *)

(* Theorem 18.7 [1]: HAUSDORFF_MEASURE *)

val _ = export_theory ();

(* References:

  [1] Schilling, R.L.: Measures, Integrals and Martingales (Second Edition).
      Cambridge University Press (2017).
 *)
