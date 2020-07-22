(* ------------------------------------------------------------------------- *)
(* Fubini's Theorem under the old extreal definitions                        *)
(*                                                                           *)
(* Author: Chun Tian (2020)                                                  *)
(* Fondazione Bruno Kessler and University of Trento, Italy                  *)
(* ------------------------------------------------------------------------- *)

open HolKernel Parse boolLib bossLib;

open pairTheory relationTheory prim_recTheory arithmeticTheory fcpTheory
     pred_setTheory combinTheory realTheory realLib seqTheory posetTheory;

open hurdUtils util_probTheory extrealTheory sigma_algebraTheory
     measureTheory real_borelTheory borelTheory lebesgueTheory martingaleTheory;

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



val _ = export_theory ();
