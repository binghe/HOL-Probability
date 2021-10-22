(* ------------------------------------------------------------------------- *)
(*  Tools for reasoning about extended reals (extreal)                       *)
(* ------------------------------------------------------------------------- *)

structure extrealLib :> extrealLib =
struct

open HolKernel Parse boolLib bossLib;

open realTheory realLib simpLib extrealTheory;

(* learnt from "examples/pgcl" *)
val extreal_SS = SSFRAG
  {name = SOME "extreal",
   ac = [],
   congs = [],
   convs = [],
   dprocs = [],
   filter = NONE,
   rewrs = [(* addition *)
            add_lzero, add_rzero,
            (* subtraction *)
            sub_lzero, sub_rzero,
            (* less than or equal *)
            le_refl, le_infty, le_ladd, le_radd,
            (* less than *)
            lt_infty, lt_ladd, lt_radd,
            (* multiplication *)
            mul_lzero, mul_rzero, mul_lone, mul_rone,
            (* reciprocal *)
            inv_zero, inv_one, inv_infty, inv_eq_zero, inv_antimono, inv_inj,
            inv_one_le, inv_le_one, inv_eq_infty, inv_eq_one, inv_inv,
            (* division *)
            div_one,
            (* cancellations *)
	    add_sub, add_sub2, sub_add, sub_add2, sub_add_normal,
	    half_cancel, third_cancel, fourth_cancel,
            (* halves *)
            half_between,
            (* thirds *)
            thirds_between,
            (* injecting from the naturals *)
            extreal_of_num_def,
	    extreal_le_eq, extreal_lt_eq, extreal_add_eq, extreal_sub_eq,
            (* injecting from the reals *)
            extreal_not_infty,
            (* min *)
            min_le1, min_le2, min_refl, min_linfty, min_rinfty,
            min_lzero, min_rzero,
            (* max *)
            le_max1, le_max2, max_refl, max_linfty, max_rinfty,
            max_lzero, max_rzero,
            (* bound1 *)
            bound1_basic, bound1_infty]};

val extreal_ss = realSimps.real_ss ++ extreal_SS;

end; (* struct *)
