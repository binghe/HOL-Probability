(* ========================================================================= *)
(*                                                                           *)
(*                        Lebesgue Measure Theory                            *)
(*                                                                           *)
(*        (c) Copyright,                                                     *)
(*                       Muhammad Qasim,                                     *)
(*                       Osman Hasan,                                        *)
(*                       Hardware Verification Group,                        *)
(*                       Concordia University                                *)
(*                                                                           *)
(*            Contact:  <m_qasi@ece.concordia.ca>                            *)
(*                                                                           *)
(*                                                                           *)
(* Note: This theory is inspired by Isabelle/HOL                             *)
(* Last update: Jan, 2015                                                    *)
(*                                                                           *)
(* ========================================================================= *)

open HolKernel Parse boolLib bossLib;

open numLib unwindLib tautLib Arith prim_recTheory combinTheory quotientTheory
     arithmeticTheory pairTheory listTheory mesonLib pred_setTheory pred_setLib
     optionTheory numTheory sumTheory InductiveDefinition ind_typeTheory;

(* real analysis *)
open realaxTheory realTheory realLib jrhUtils seqTheory limTheory transcTheory
     real_sigmaTheory iterateTheory cardinalTheory productTheory RealArith
     real_topologyTheory derivativeTheory integrationTheory;

(* probability *)
open hurdUtils util_probTheory extrealTheory sigma_algebraTheory measureTheory
     borelTheory lebesgueTheory;

(* NOTE: the existing "lebesgue" theory is actually "lebesgue_integration" *)
val _ = new_theory "lebesgue_measure";

fun MESON ths tm = prove(tm,MESON_TAC ths);
fun METIS ths tm = prove(tm,METIS_TAC ths);

val DISC_RW_KILL = DISCH_TAC THEN ONCE_ASM_REWRITE_TAC [] THEN
                   POP_ASSUM K_TAC;

fun ASSERT_TAC tm = SUBGOAL_THEN tm STRIP_ASSUME_TAC;
val ASM_ARITH_TAC = REPEAT (POP_ASSUM MP_TAC) THEN ARITH_TAC;

(* Minimal hol-light compatibility layer *)
val ASM_REAL_ARITH_TAC = REAL_ASM_ARITH_TAC; (* RealArith *)
val IMP_CONJ           = CONJ_EQ_IMP;        (* cardinalTheory *)
val FINITE_SUBSET      = SUBSET_FINITE_I;    (* pred_setTheory *)
val LE_0               = ZERO_LESS_EQ;       (* arithmeticTheory *)

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* ------------------------------------------------------------------------- *)

val IN_FUN_SET = IN_FUNSET;

(* ------------------------------------------------------------------------- *)
(* Disjoint Sets                                                             *)
(* ------------------------------------------------------------------------- *)

val disjoint = new_definition ("disjoint",
 ``!A. disjoint A = !a b. a IN A /\ b IN A /\ (a <> b) ==> (a INTER b = {})``);

val disjointI = store_thm ("disjointI",
 ``(!a b . a IN A ==> b IN A ==> (a <> b) ==> (a INTER b = {})) ==> disjoint A``,
 METIS_TAC [disjoint]);

val disjointD = store_thm ("disjointD",
 ``disjoint A ==> a IN A ==> b IN A ==> (a <> b) ==> (a INTER b = {})``,
 METIS_TAC [disjoint]);

val disjoint_empty = store_thm ("disjoint_empty",
 ``disjoint {}``,
 SET_TAC [disjoint]);

val disjoint_union = store_thm ("disjoint_union",
 ``!C B.
     disjoint C /\ disjoint B /\
     (BIGUNION C INTER BIGUNION B = {}) ==>
     disjoint (C UNION B)``,
 SET_TAC [disjoint]);

val disjoint_sing = store_thm ("disjoint_sing",
 ``!A. disjoint {A}``,
  SET_TAC [disjoint]);

val semiring = new_definition ("semiring",
 ``semiring sp sts = subset_class sp sts /\ {} IN sts /\
                (!s t. s IN sts /\ t IN sts ==> s INTER t IN sts) /\
                (!s t. s IN sts /\ t IN sts ==>
                 ?c. c SUBSET sts /\ FINITE c /\ disjoint c /\
                     (s DIFF t = BIGUNION c))``);

val Int_space_eq1 = store_thm ("Int_space_eq1",
 ``!sp sts . subset_class sp sts ==> !x. x IN sts ==> (sp INTER x = x)``,
  REPEAT GEN_TAC THEN SET_TAC [subset_class_def]);

val Int_space_eq2 = store_thm ("Int_space_eq2",
 ``!sp sts. subset_class sp sts ==> !x. x IN sts ==> (x INTER sp = x)``,
  REPEAT GEN_TAC THEN SET_TAC [subset_class_def]);

val sets_Collect_conj = store_thm ("sets_Collect_conj",
 ``!sp sts P Q. semiring sp sts /\
    {x | x IN sp /\ P x} IN sts /\ {x | x IN sp /\ Q x} IN sts ==>
    {x | x IN sp /\ P x /\ Q x} IN sts``,
 REPEAT GEN_TAC THEN SIMP_TAC std_ss [semiring] THEN
 REPEAT STRIP_TAC THEN
 FIRST_X_ASSUM (K_TAC o SPECL
  [``{x | x IN sp /\ P x}``,``{x | x IN sp /\ Q x}``]) THEN
 FIRST_X_ASSUM (MP_TAC o SPECL
  [``{x | x IN sp /\ P x}``,``{x | x IN sp /\ Q x}``]) THEN
 ASM_SIMP_TAC std_ss [GSPECIFICATION, INTER_DEF] THEN
 REWRITE_TAC [SET_RULE ``(A /\ B) /\ A /\ C = A /\ B /\ C``]);

val ring = new_definition ("ring",
 ``ring sp sts = semiring sp sts /\
    !a b. a IN sts /\ b IN sts ==> a UNION b IN sts``);

val finite_Union = store_thm ("finite_Union",
 ``!X sp sts. ring sp sts /\ FINITE X ==> X SUBSET sts ==> BIGUNION X IN sts``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [ring] THEN STRIP_TAC THEN POP_ASSUM MP_TAC THEN
  SPEC_TAC (``X:('a->bool)->bool``,``X:('a->bool)->bool``) THEN
  SET_INDUCT_TAC THENL
  [FULL_SIMP_TAC std_ss [semiring, BIGUNION_EMPTY], ALL_TAC] THEN
  DISCH_TAC THEN REWRITE_TAC [BIGUNION_INSERT] THEN FIRST_ASSUM MATCH_MP_TAC THEN
  ASM_SET_TAC []);

val finite_UN = store_thm ("finite_UN",
 ``!A N sp sts. ring sp sts /\ FINITE N /\ (!i. i IN N ==> A i IN sts) ==>
   BIGUNION {A i | i IN N} IN sts``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [ring] THEN STRIP_TAC THEN POP_ASSUM MP_TAC THEN
  POP_ASSUM MP_TAC THEN SPEC_TAC (``N:'a->bool``,``N:'a->bool``) THEN
  SET_INDUCT_TAC THENL
  [REWRITE_TAC [SET_RULE ``{A i | i IN {}} = {}``, BIGUNION_EMPTY] THEN
   FULL_SIMP_TAC std_ss [semiring], ALL_TAC] THEN
  DISCH_TAC THEN REWRITE_TAC [IN_INSERT] THEN
  REWRITE_TAC [SET_RULE ``BIGUNION {A i | (i = e) \/ i IN s} =
               BIGUNION {A e} UNION BIGUNION {A i | i IN s}``] THEN
  FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC [BIGUNION_SING] THEN
  ASM_SET_TAC []);

val Diff = store_thm ("Diff",
 ``!a b sp sts. ring sp sts /\ a IN sts /\ b IN sts ==> a DIFF b IN sts``,
  REPEAT GEN_TAC THEN REWRITE_TAC [ring, semiring] THEN STRIP_TAC THEN
  POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
  FIRST_ASSUM (MP_TAC o SPECL [``a:'a->bool``,``b:'a->bool``]) THEN
  REPEAT STRIP_TAC THEN FULL_SIMP_TAC std_ss [] THEN
  UNDISCH_TAC ``c SUBSET sts:('a->bool)->bool`` THEN MATCH_MP_TAC finite_Union THEN
  EXISTS_TAC ``sp:'a->bool`` THEN FULL_SIMP_TAC std_ss [ring, semiring]);

val ring_of_setsI = store_thm ("ring_of_setsI",
 ``!sp sts. sts SUBSET POW sp /\ {} IN sts /\
    (!a b. a IN sts /\ b IN sts ==> a UNION b IN sts) /\
    (!a b. a IN sts /\ b IN sts ==> a DIFF b IN sts) ==> ring sp sts``,
  REWRITE_TAC [ring, semiring, subset_class_def, POW_DEF] THEN
  REWRITE_TAC [SET_RULE ``sts SUBSET {s | s SUBSET sp} =
                !x. x IN sts ==> x SUBSET sp``] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC std_ss [] THENL
  [REWRITE_TAC [SET_RULE ``s INTER t = s DIFF (s DIFF t)``] THEN
   ASM_SET_TAC [], ALL_TAC] THEN
  REWRITE_TAC [disjoint] THEN EXISTS_TAC ``{(s:'a->bool) DIFF t}`` THEN
  SIMP_TAC std_ss [BIGUNION_SING, FINITE_SING, IN_SING, SUBSET_DEF] THEN
  ASM_SET_TAC []);

val ring_of_sets_iff = store_thm ("ring_of_sets_iff",
 ``!sp sts. ring sp sts = sts SUBSET POW sp /\ {} IN sts /\
      (!s t. s IN sts /\ t IN sts ==> s UNION t IN sts) /\
      (!s t. s IN sts /\ t IN sts ==> s DIFF t IN sts)``,
  REPEAT GEN_TAC THEN EQ_TAC THENL
  [ALL_TAC, METIS_TAC [ring_of_setsI]] THEN
  REWRITE_TAC [ring, semiring, subset_class_def, POW_DEF] THEN
  REWRITE_TAC [SET_RULE ``sts SUBSET {s | s SUBSET sp} =
                !x. x IN sts ==> x SUBSET sp``] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC std_ss [] THEN
  MATCH_MP_TAC Diff THEN EXISTS_TAC ``sp:'a->bool`` THEN
  ASM_SIMP_TAC std_ss [ring, semiring, subset_class_def]);

val insert_in_sets = store_thm ("insert_in_sets",
 ``!x A sp sts. ring sp sts /\ {x} IN sts /\ A IN sts ==> x INSERT A IN sts``,
  REWRITE_TAC [ring] THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC [SET_RULE ``x INSERT A = {x} UNION A``] THEN
  ASM_SET_TAC []);

val sets_Collect_disj = store_thm ("sets_Collect_disj",
  ``!sp sts P Q. ring sp sts /\ {x | x IN sp /\ P x} IN sts /\
      {x | x IN sp /\ Q x} IN sts ==> {x | x IN sp /\ P x /\ Q x} IN sts``,
  REPEAT GEN_TAC THEN SIMP_TAC std_ss [ring, semiring] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM (K_TAC o SPECL
   [``{x | x IN sp /\ P x}``,``{x | x IN sp /\ Q x}``]) THEN
  FIRST_X_ASSUM (MP_TAC o SPECL
   [``{x | x IN sp /\ P x}``,``{x | x IN sp /\ Q x}``]) THEN
  ASM_SIMP_TAC std_ss [GSPECIFICATION, INTER_DEF] THEN
  STRIP_TAC THEN
  REWRITE_TAC [SET_RULE ``{x | x IN sp /\ P x /\ Q x} =
                {x | x IN sp /\ P x} INTER {x | x IN sp /\ Q x}``] THEN
  ASM_SET_TAC []);

val sets_collect_finite_Ex = store_thm ("sets_collect_finite_Ex",
 ``!sp sts s P. ring sp sts /\ (!i. i IN s ==> {x | x IN sp /\ P i x} IN sts) /\
      FINITE s ==> {x | x IN sp /\ (?i. i IN s /\ P i x)} IN sts``,
  REPEAT GEN_TAC THEN SIMP_TAC std_ss [ring, semiring] THEN
  REPEAT STRIP_TAC THEN
  KNOW_TAC ``{x | x IN sp /\ (?i. i IN s /\ P i x)} =
              BIGUNION {{x | x IN sp /\ P i x} | i IN s}`` THENL
  [SIMP_TAC std_ss [EXTENSION, BIGUNION, GSPECIFICATION] THEN
   GEN_TAC THEN EQ_TAC THENL [ALL_TAC, ASM_SET_TAC []] THEN
   STRIP_TAC THEN EXISTS_TAC ``{x | x IN sp /\ P i x}`` THEN
   CONJ_TAC THENL [ALL_TAC, ASM_SET_TAC []] THEN EXISTS_TAC ``i:'b`` THEN
   ASM_SIMP_TAC std_ss [GSPECIFICATION], ALL_TAC] THEN
  DISC_RW_KILL THEN
  KNOW_TAC ``{{x | x IN sp /\ P i x} | i IN s} SUBSET sts`` THENL
  [SIMP_TAC std_ss [SUBSET_DEF, GSPECIFICATION] THEN GEN_TAC THEN
   STRIP_TAC THEN ASM_REWRITE_TAC [] THEN FIRST_ASSUM MATCH_MP_TAC THEN
   ASM_REWRITE_TAC [], MATCH_MP_TAC finite_Union] THEN
  EXISTS_TAC ``sp:'a->bool`` THEN CONJ_TAC THENL
  [FULL_SIMP_TAC std_ss [ring, semiring], ALL_TAC] THEN
  ONCE_REWRITE_TAC [METIS [] ``{x | x IN sp /\ P i x} =
                          (\i. {x | x IN sp /\ P i x}) i``] THEN
  ONCE_REWRITE_TAC [GSYM IMAGE_DEF] THEN METIS_TAC [IMAGE_FINITE]);

val algebra_alt = new_definition ("algebra_alt",
 ``algebra_alt sp sts = ring sp sts /\ sp IN sts``);

val algebra_alt_eq  = store_thm ("algebra_alt_eq",
 ``!sp sts. algebra (sp, sts) = ring sp sts /\ sp IN sts``,
  REPEAT GEN_TAC THEN REWRITE_TAC [algebra_def, space_def, subsets_def] THEN
  REWRITE_TAC [ring, semiring] THEN EQ_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC [] THENL
  [ALL_TAC, GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC Diff THEN
   EXISTS_TAC ``sp:'a->bool`` THEN FULL_SIMP_TAC std_ss [ring, semiring]] THEN
  CONJ_TAC THENL
  [ALL_TAC, POP_ASSUM K_TAC THEN POP_ASSUM (MP_TAC o SPEC ``{}``) THEN
   ASM_SIMP_TAC std_ss [DIFF_EMPTY]] THEN
  CONJ_TAC THENL
  [REPEAT STRIP_TAC THEN KNOW_TAC ``s SUBSET sp /\ t SUBSET sp ==>
    (s INTER t = sp DIFF ((sp DIFF s) UNION (sp DIFF t)))`` THENL
   [SET_TAC [], ALL_TAC] THEN
   FULL_SIMP_TAC std_ss [subset_class_def], ALL_TAC] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC [disjoint] THEN EXISTS_TAC ``{s DIFF t}`` THEN
  SIMP_TAC std_ss [SUBSET_DEF, GSPECIFICATION, FINITE_SING, IN_SING] THEN
  FULL_SIMP_TAC std_ss [BIGUNION_SING, subset_class_def] THEN
  KNOW_TAC ``s SUBSET sp /\ t SUBSET sp ==>
            (s DIFF t = sp DIFF ((sp DIFF s) UNION t))``
  THENL [SET_TAC [], ALL_TAC] THEN FULL_SIMP_TAC std_ss []);

val compl_sets = store_thm ("compl_sets",
 ``!sp sts a. algebra (sp,sts) /\ a IN sts ==> sp DIFF a IN sts``,
  REWRITE_TAC [algebra_alt_eq, ring, semiring] THEN
  REPEAT STRIP_TAC THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
  POP_ASSUM MP_TAC THEN
  FIRST_ASSUM (MP_TAC o SPECL [``sp:'a->bool``,``a:'a->bool``]) THEN
  REPEAT STRIP_TAC THEN FULL_SIMP_TAC std_ss [] THEN
  UNDISCH_TAC ``c SUBSET (sts:('a->bool)->bool)`` THEN
  MATCH_MP_TAC finite_Union THEN
  EXISTS_TAC ``sp:'a->bool`` THEN FULL_SIMP_TAC std_ss [ring, semiring]);

val algebra_iff_Un = store_thm ("algebra_iff_Un",
 ``!sp sts. algebra (sp,sts) = sts SUBSET POW sp /\ {} IN sts /\
             (!a. a IN sts ==> sp DIFF a IN sts) /\
             (!a b. a IN sts /\ b IN sts ==> a UNION b IN sts)``,
  REPEAT STRIP_TAC THEN REWRITE_TAC [algebra_def, subsets_def, space_def] THEN
  REWRITE_TAC [subset_class_def, POW_DEF] THEN
  REWRITE_TAC [SET_RULE ``sts SUBSET {s | s SUBSET sp} =
                          (!x. x IN sts ==> x SUBSET sp)``]);

val algebra_iff_Int = store_thm ("algebra_if_Int",
 ``!sp sts. algebra (sp,sts) = sts SUBSET POW sp /\ {} IN sts /\
             (!a. a IN sts ==> sp DIFF a IN sts) /\
             (!a b. a IN sts /\  b IN sts ==> a INTER b IN sts)``,
  REPEAT STRIP_TAC THEN REWRITE_TAC [algebra_def, subsets_def, space_def] THEN
  REWRITE_TAC [subset_class_def, POW_DEF] THEN
  REWRITE_TAC [SET_RULE ``sts SUBSET {s | s SUBSET sp} =
                          (!x. x IN sts ==> x SUBSET sp)``] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THENL
  [REPEAT STRIP_TAC THEN KNOW_TAC ``a SUBSET sp /\ b SUBSET sp ==>
    (a INTER b = sp DIFF ((sp DIFF a) UNION (sp DIFF b)))`` THENL
   [SET_TAC [], ALL_TAC]
   THEN FULL_SIMP_TAC std_ss [], ALL_TAC] THEN
  REPEAT STRIP_TAC THEN KNOW_TAC ``s SUBSET sp /\ t SUBSET sp ==>
   (s UNION t = sp DIFF ((sp DIFF s) INTER (sp DIFF t)))`` THENL
  [SET_TAC [], ALL_TAC] THEN
  FULL_SIMP_TAC std_ss []);

val sets_Collect_neg = store_thm ("sets_Collect_neg",
 ``!sp sts P. algebra (sp,sts) /\ {x | x IN sp /\ P x} IN sts ==>
             {x | x IN sp /\ ~P x} IN sts``,
  REPEAT GEN_TAC THEN REWRITE_TAC [algebra_def, space_def, subsets_def] THEN
  RW_TAC std_ss [subset_class_def] THEN
  KNOW_TAC ``{x | x IN sp /\ ~P x} = sp DIFF {x | x IN sp /\ P x}`` THENL
  [ALL_TAC, DISC_RW_KILL THEN FULL_SIMP_TAC std_ss []] THEN SET_TAC []);

val sets_Collect_imp = store_thm ("sets_Collect_imp",
 ``!sp sts P Q. algebra (sp,sts) /\ {x | x IN sp /\ P x} IN sts ==>
                 {x | x IN sp /\ Q x} IN sts ==>
                 {x | x IN sp /\ (Q x ==> P x)} IN sts``,
  REPEAT GEN_TAC THEN REWRITE_TAC [algebra_alt_eq, ring, semiring] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC [IMP_DISJ_THM] THEN
  REWRITE_TAC [SET_RULE ``{x | x IN sp /\ (~Q x \/ P x)} =
                          {x | x IN sp /\ ~Q x} UNION {x | x IN sp /\ P x}``] THEN
  FIRST_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC std_ss [] THEN
  MATCH_MP_TAC sets_Collect_neg THEN
  FULL_SIMP_TAC std_ss [algebra_alt_eq, ring, semiring]);

val sets_Collect_const = store_thm ("sets_Collect_const",
 ``!sp sts P. algebra (sp,sts) ==> {x | x IN sp /\ P} IN sts``,
  REWRITE_TAC [algebra_alt_eq] THEN REPEAT STRIP_TAC THEN
  Cases_on `P` THENL
  [REWRITE_TAC [SET_RULE ``{x | x IN sp /\ T} = sp``] THEN ASM_REWRITE_TAC [],
   FULL_SIMP_TAC std_ss [GSPEC_F, ring, semiring]]);

val algebra_single_set = store_thm ("algebra_single_set",
 ``!X S. X SUBSET S ==> algebra (S, {{};X;S DIFF X; S})``,
  RW_TAC std_ss [algebra_def, subsets_def, space_def, subset_class_def] THEN
  FULL_SIMP_TAC std_ss [SET_RULE ``x IN {a;b;c;d} =
        (x = a) \/ (x = b) \/ (x = c) \/ (x = d)``] THEN TRY (ASM_SET_TAC []));

(* ------------------------------------------------------------------------- *)
(* Retricted Algebras                                                        *)
(* ------------------------------------------------------------------------- *)

val restricted_algebra = store_thm ("restricted_algebra",
 ``!sp sts a. algebra (sp,sts) /\ a IN sts ==>
              algebra (a,IMAGE (\s. s INTER a) sts)``,
  REWRITE_TAC [algebra_alt_eq, ring, semiring, subset_class_def] THEN
  REPEAT STRIP_TAC THEN
  FULL_SIMP_TAC std_ss [IMAGE_DEF, GSPECIFICATION] THENL
  [REWRITE_TAC [INTER_SUBSET],
   EXISTS_TAC ``{}`` THEN ASM_SIMP_TAC std_ss [INTER_EMPTY],
   EXISTS_TAC ``s' INTER (s'' INTER a)`` THEN
   CONJ_TAC THENL [SET_TAC [], ALL_TAC] THEN
   FULL_SIMP_TAC std_ss [],
   EXISTS_TAC ``{s' INTER a DIFF s'' INTER a}`` THEN
   SIMP_TAC std_ss [SUBSET_DEF, GSPECIFICATION, FINITE_SING, IN_SING, disjoint] THEN
   FULL_SIMP_TAC std_ss [BIGUNION_SING, subset_class_def] THEN
   EXISTS_TAC ``s' DIFF s''`` THEN CONJ_TAC THENL [SET_TAC [], ALL_TAC] THEN
   MATCH_MP_TAC Diff THEN EXISTS_TAC ``sp:'a->bool`` THEN
   FULL_SIMP_TAC std_ss [ring, semiring, subset_class_def],
   Q.EXISTS_TAC `s UNION s'` THEN CONJ_TAC THENL [SET_TAC [], ALL_TAC] THEN
   FULL_SIMP_TAC std_ss [],
   EXISTS_TAC ``a:'a->bool`` THEN ASM_SET_TAC []]);

(* ------------------------------------------------------------------------- *)
(* Sigma Algebras                                                            *)
(* ------------------------------------------------------------------------- *)

val sigma_algebra_alt = new_definition ("sigma_algebra_alt",
  ``sigma_algebra_alt sp sts = algebra (sp,sts) /\
     !A. IMAGE A UNIV SUBSET sts ==> BIGUNION {A i | i IN univ(:num)} IN sts``);

val sigma_algebra_alt_eq = store_thm ("sigma_algebra_alt_eq",
  ``!sp sts. sigma_algebra (sp,sts) = algebra (sp,sts) /\
     !A. IMAGE A UNIV SUBSET sts ==> BIGUNION {A i | i IN univ(:num)} IN sts``,
  REPEAT GEN_TAC THEN REWRITE_TAC [SIGMA_ALGEBRA_ALT] THEN EQ_TAC THEN
  STRIP_TAC THEN ASM_REWRITE_TAC [] THEN X_GEN_TAC ``A:num->'a->bool`` THEN
  POP_ASSUM (MP_TAC o SPEC ``A:num->'a->bool``) THEN
  SIMP_TAC std_ss [IMAGE_DEF, subsets_def] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM MATCH_MP_TAC THEN POP_ASSUM MP_TAC THEN EVAL_TAC THEN
  SRW_TAC[] [IN_UNIV,SUBSET_DEF,IN_FUN_SET] THEN METIS_TAC[]);

val is_sigma_algebra = store_thm ("is_sigma_algebra",
  ``!sp sts. algebra (sp,sts) /\ FINITE sts ==> sigma_algebra (sp,sts)``,
  REPEAT STRIP_TAC THEN
  KNOW_TAC ``!A. IMAGE A UNIV SUBSET sts ==>
   (BIGUNION {A i | i IN univ(:num)} =
    BIGUNION {s | s IN sts INTER IMAGE A UNIV})`` THENL
  [ASM_SET_TAC [], DISCH_TAC] THEN
  REWRITE_TAC [sigma_algebra_alt_eq] THEN ASM_SIMP_TAC std_ss [] THEN
  GEN_TAC THEN POP_ASSUM K_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC (REWRITE_RULE [AND_IMP_INTRO] finite_Union) THEN
  EXISTS_TAC ``sp:'a->bool`` THEN FULL_SIMP_TAC std_ss [algebra_alt_eq] THEN
  CONJ_TAC THENL [ALL_TAC, ASM_SET_TAC []] THEN
  REWRITE_TAC [SET_RULE ``{s | s IN sts /\ s IN IMAGE A univ(:num)} =
                          sts INTER {s | s IN IMAGE A UNIV}``, IN_INTER] THEN
  MATCH_MP_TAC FINITE_INTER THEN ASM_SIMP_TAC std_ss []);

val countable_Union = store_thm ("countable_Union",
 ``!sp sts c. sigma_algebra (sp,sts) /\ countable c /\ c SUBSET sts ==>
            BIGUNION c IN sts``,
  FULL_SIMP_TAC std_ss [sigma_algebra_def, subsets_def, lemma]);

val countable_UN = store_thm ("countable_UN",
 ``!sp sts A X. sigma_algebra (sp,sts) /\ IMAGE (A:num->'a->bool) X SUBSET sts ==>
               BIGUNION {A x | x IN X} IN sts``,
  REPEAT STRIP_TAC THEN
  KNOW_TAC
  ``(IMAGE (\i. if i IN X then (A:num->'a->bool) i else {}) UNIV) SUBSET sts``
  THENL [POP_ASSUM MP_TAC THEN
   SIMP_TAC std_ss [SUBSET_DEF, IN_IMAGE] THEN REPEAT STRIP_TAC THEN
   FULL_SIMP_TAC std_ss [] THEN COND_CASES_TAC THENL [METIS_TAC [], ALL_TAC] THEN
   FULL_SIMP_TAC std_ss [sigma_algebra_alt_eq, algebra_def, ring, semiring,
    subsets_def], ALL_TAC] THEN DISCH_TAC THEN KNOW_TAC
    ``BIGUNION {(\i. if i IN X then (A:num->'a->bool) i else {}) x | x IN UNIV}
       IN sts``
  THENL [SIMP_TAC std_ss [] THEN MATCH_MP_TAC countable_Union THEN
   EXISTS_TAC ``sp:'a->bool`` THEN FULL_SIMP_TAC std_ss [] THEN
   CONJ_TAC THENL [ALL_TAC, ASM_SET_TAC []] THEN
   SIMP_TAC arith_ss [GSYM IMAGE_DEF] THEN
   METIS_TAC [COUNTABLE_IMAGE_NUM], DISCH_TAC] THEN KNOW_TAC ``
  BIGUNION {(\i. if i IN X then (A:num->'a->bool) i else {}) x | x IN univ(:num)} =
  BIGUNION {A x | x IN X}`` THENL [ALL_TAC, METIS_TAC []] THEN
  SIMP_TAC std_ss [EXTENSION, IN_BIGUNION, GSPECIFICATION] THEN GEN_TAC THEN
  EQ_TAC THEN REPEAT STRIP_TAC THENL
  [EXISTS_TAC ``s:'a->bool`` THEN FULL_SIMP_TAC std_ss [] THEN
   POP_ASSUM K_TAC THEN POP_ASSUM K_TAC THEN POP_ASSUM MP_TAC THEN
   COND_CASES_TAC THEN ASM_SET_TAC [], ALL_TAC] THEN
  EXISTS_TAC ``s:'a->bool`` THEN FULL_SIMP_TAC std_ss [IN_UNIV] THEN
  EXISTS_TAC ``x':num`` THEN ASM_SET_TAC []);

val countable_UN' = store_thm ("countable_UN'",
 ``!sp sts A X. sigma_algebra (sp,sts) /\ countable X /\ IMAGE A X SUBSET sts ==>
                BIGUNION {(A:num->'a->bool) x | x IN X} IN sts``,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC countable_UN THEN
  METIS_TAC []);

val countable_INT = store_thm ("countable_INT",
 ``!sp sts A X. sigma_algebra (sp,sts) /\ IMAGE (A:num->'a->bool) X SUBSET sts /\
                (X <> {}) ==> BIGINTER {(A:num->'a->bool) x | x IN X} IN sts``,
  REPEAT STRIP_TAC THEN FULL_SIMP_TAC std_ss [GSYM MEMBER_NOT_EMPTY] THEN
  KNOW_TAC ``!x. x IN X ==> (A:num->'a->bool) x IN sts`` THENL
  [ASM_SET_TAC [], DISCH_TAC] THEN
  KNOW_TAC ``sp DIFF BIGUNION {sp DIFF (A:num->'a->bool) x | x IN X} IN sts`` THENL
  [MATCH_MP_TAC Diff THEN EXISTS_TAC ``sp:'a->bool`` THEN
   FULL_SIMP_TAC std_ss [sigma_algebra_alt_eq, algebra_alt_eq] THEN
   ONCE_REWRITE_TAC [METIS [] ``sp DIFF A x = (\x. sp DIFF A x) x``] THEN
   MATCH_MP_TAC countable_UN THEN EXISTS_TAC ``sp:'a->bool`` THEN
   FULL_SIMP_TAC std_ss [sigma_algebra_alt_eq, algebra_alt_eq] THEN
   SIMP_TAC std_ss [SUBSET_DEF, IN_IMAGE] THEN REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC [] THEN MATCH_MP_TAC Diff THEN EXISTS_TAC ``sp:'a->bool`` THEN
   ASM_SET_TAC [], DISCH_TAC] THEN
  KNOW_TAC ``BIGINTER {(A:num->'a->bool) x | x IN X} =
             sp DIFF BIGUNION {sp DIFF A x | x IN X}`` THENL
  [ALL_TAC, METIS_TAC []] THEN SIMP_TAC std_ss [EXTENSION] THEN GEN_TAC THEN
  KNOW_TAC ``sts SUBSET POW sp`` THENL
  [FULL_SIMP_TAC std_ss [sigma_algebra_alt_eq, algebra_alt_eq, ring, semiring,
    subset_class_def] THEN ASM_SET_TAC [POW_DEF], RW_TAC std_ss [POW_DEF]] THEN
  EQ_TAC THEN REPEAT STRIP_TAC THENL
  [SIMP_TAC std_ss [IN_DIFF] THEN CONJ_TAC THENL [ASM_SET_TAC [], ALL_TAC] THEN
   FULL_SIMP_TAC std_ss [BIGINTER, BIGUNION, GSPECIFICATION] THEN GEN_TAC THEN
   ASM_CASES_TAC ``x' NOTIN (s:'a->bool)`` THEN ASM_REWRITE_TAC [] THEN
   GEN_TAC THEN ASM_CASES_TAC ``x'' NOTIN (X:num->bool)`` THEN
   FULL_SIMP_TAC std_ss [SUBSET_DEF, GSPECIFICATION] THEN
   SIMP_TAC std_ss [DIFF_DEF, EXTENSION, GSPECIFICATION] THEN
   EXISTS_TAC ``x':'a`` THEN FULL_SIMP_TAC std_ss [] THEN
   ASM_CASES_TAC ``x' NOTIN (sp:'a->bool)`` THEN FULL_SIMP_TAC std_ss [] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SET_TAC [], ALL_TAC] THEN
  SIMP_TAC std_ss [BIGINTER, GSPECIFICATION] THEN GEN_TAC THEN
  STRIP_TAC THEN ASM_REWRITE_TAC [] THEN POP_ASSUM MP_TAC THEN
  POP_ASSUM K_TAC THEN FULL_SIMP_TAC std_ss [IN_DIFF, BIGUNION, GSPECIFICATION] THEN
  STRIP_TAC THEN CCONTR_TAC THEN UNDISCH_TAC
   ``!s. (!x. s <> sp DIFF (A:num->'a->bool) x \/ x NOTIN X) \/ x' NOTIN s`` THEN
  SIMP_TAC std_ss [] THEN EXISTS_TAC ``sp DIFF (A:num->'a->bool) x''`` THEN
  CONJ_TAC THENL [METIS_TAC [], ALL_TAC] THEN
  ASM_SIMP_TAC std_ss [IN_DIFF]);

val countable_INT' = store_thm ("countable_INT'",
 ``!sp sts A X. sigma_algebra (sp,sts) /\ countable X /\ (X <> {}) /\
                IMAGE (A:num->'a->bool) X SUBSET sts ==>
                BIGINTER {(A:num->'a->bool) x | x IN X} IN sts``,
  METIS_TAC [countable_INT]);

val ring_of_sets_Pow = store_thm ("ring_of_sets_Pow",
 ``!sp. ring sp (POW sp)``,
  REWRITE_TAC [ring_of_sets_iff, IN_POW] THEN SET_TAC [SUBSET_REFL]);

val algebra_Pow = store_thm ("algebra_Pow",
 ``!sp. algebra (sp, (POW sp))``,
  REWRITE_TAC [algebra_iff_Un, IN_POW] THEN SET_TAC []);

val sigma_algebra_iff = store_thm ("sigma_algebra_iff",
 ``!sp sts. sigma_algebra (sp,sts) = algebra (sp,sts) /\
        !A. IMAGE A UNIV SUBSET sts ==>
            BIGUNION {(A:num->'a->bool) x | x IN UNIV} IN sts``,
  SIMP_TAC std_ss [sigma_algebra_alt_eq]);

val sigma_algebra_Pow = store_thm ("sigma_algebra_Pow",
 ``!sp. sigma_algebra (sp, (POW sp))``,
  SIMP_TAC std_ss [sigma_algebra_alt_eq, algebra_iff_Int] THEN
  SET_TAC [IN_POW]);

val sets_Collect_countable_All = store_thm ("sets_Collect_countable_All",
 ``!sp sts P. sigma_algebra (sp,sts) /\ (!i. {x | x IN sp /\ P i x} IN sts) ==>
                {x | x IN sp /\ !i. (P:num->'a->bool) i x} IN sts``,
  REPEAT STRIP_TAC THEN KNOW_TAC ``{x | x IN sp /\ !i. P i x} =
   BIGINTER {{x | x IN sp /\ (P:num->'a->bool) i x} | i IN UNIV}`` THENL
  [SIMP_TAC std_ss [EXTENSION, IN_UNIV, IN_BIGINTER, GSPECIFICATION] THEN
   GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [ASM_SET_TAC [],
    ALL_TAC, ALL_TAC] THEN
   (POP_ASSUM (MP_TAC o SPEC ``{x | x IN sp /\ (P:num->'a->bool) i x}``) THEN
    SIMP_TAC std_ss [GSPECIFICATION] THEN
    KNOW_TAC ``(?(i' :num).
    !(x :'a). x IN (sp :'a -> bool) /\ P i x <=>
      x IN sp /\ (P :num -> 'a -> bool) i' x)`` THENL
    [SET_TAC [], DISCH_TAC THEN ASM_REWRITE_TAC [] THEN POP_ASSUM K_TAC]) THEN
    ASM_SET_TAC [], ALL_TAC] THEN DISC_RW_KILL THEN
  ONCE_REWRITE_TAC [METIS [] ``{x | x IN sp /\ P i x} =
                          (\i. {x | x IN sp /\ P i x} ) i``] THEN
  MATCH_MP_TAC countable_INT THEN EXISTS_TAC ``sp:'a->bool`` THEN
  ASM_SET_TAC []);

val sets_Collect_countable_Ex = store_thm ("sets_Collect_countable_Ex",
 ``!sp sts P. sigma_algebra (sp,sts) /\ (!i. {x | x IN sp /\ P i x} IN sts) ==>
                {x | x IN sp /\ ?i. (P:num->'a->bool) i x} IN sts``,
  REPEAT STRIP_TAC THEN KNOW_TAC ``{x | x IN sp /\ ?i. P i x} =
   BIGUNION {{x | x IN sp /\ (P:num->'a->bool) i x} | i IN UNIV}`` THENL
  [SIMP_TAC std_ss [EXTENSION, IN_UNIV, IN_BIGUNION, GSPECIFICATION] THEN
   GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL
   [ALL_TAC, ASM_SET_TAC [], ASM_SET_TAC []] THEN
   EXISTS_TAC ``{x | x IN sp /\ (P:num->'a->bool) i x}`` THEN
   ASM_SET_TAC [], ALL_TAC] THEN DISC_RW_KILL THEN
  ONCE_REWRITE_TAC [METIS [] ``{x | x IN sp /\ P i x} =
                          (\i. {x | x IN sp /\ P i x} ) i``] THEN
  MATCH_MP_TAC countable_UN THEN EXISTS_TAC ``sp:'a->bool`` THEN
  ASM_SET_TAC []);

(* ------------------------------------------------------------------------- *)
(* Binary Unions                                                             *)
(* ------------------------------------------------------------------------- *)

val binary = new_definition ("binary",
 ``binary a b = (\x:num. if x = 0 then a else b)``);

val range_binary_eq = store_thm ("range_binary_eq",
  ``!a b. IMAGE (binary a b) UNIV = {a;b}``,
  RW_TAC std_ss [IMAGE_DEF, binary] THEN
  SIMP_TAC std_ss [EXTENSION, GSPECIFICATION, SET_RULE
   ``x IN {a;b} = (x = a) \/ (x = b)``] THEN
  GEN_TAC THEN EQ_TAC THEN STRIP_TAC THENL
  [METIS_TAC [], METIS_TAC [IN_UNIV],
   EXISTS_TAC ``1:num`` THEN ASM_SIMP_TAC arith_ss [IN_UNIV]]);

val Un_range_binary = store_thm ("Un_range_binary",
  ``!a b. a UNION b = BIGUNION {binary a b i | i IN UNIV}``,
  SIMP_TAC arith_ss [GSYM IMAGE_DEF] THEN
  REWRITE_TAC [METIS [ETA_AX] ``(\i. binary a b i) = binary a b``] THEN
  SIMP_TAC std_ss [range_binary_eq] THEN SET_TAC []);

val Int_range_binary = store_thm ("Int_range_binary",
  ``!a b. a INTER b = BIGINTER {binary a b i | i IN UNIV}``,
  SIMP_TAC arith_ss [GSYM IMAGE_DEF] THEN
  REWRITE_TAC [METIS [ETA_AX] ``(\i. binary a b i) = binary a b``] THEN
  SIMP_TAC std_ss [range_binary_eq] THEN SET_TAC []);

val sigma_algebra_iff2 = store_thm ("sigma_algebra_iff2",
 ``!sp sts. sigma_algebra (sp,sts) = sts SUBSET POW sp /\ {} IN sts /\
            (!s. s IN sts ==> sp DIFF s IN sts) /\
            (!A. IMAGE A UNIV SUBSET sts ==>
                 BIGUNION {(A:num->'a->bool) i | i IN UNIV} IN sts)``,
  SIMP_TAC std_ss [sigma_algebra_alt_eq, algebra_def, space_def, subsets_def] THEN
  REPEAT GEN_TAC THEN SIMP_TAC std_ss [subset_class_def, POW_DEF] THEN
  EQ_TAC THENL [ASM_SET_TAC [], ALL_TAC] THEN
  REPEAT STRIP_TAC THENL [ASM_SET_TAC [], ASM_SET_TAC [], ASM_SET_TAC [],
   ALL_TAC, ASM_SET_TAC []] THEN
  SIMP_TAC std_ss [Un_range_binary] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  SIMP_TAC std_ss [range_binary_eq] THEN ASM_SET_TAC []);

val countable_UN' = store_thm ("countable_UN'",
 ``!sp sts A X. sigma_algebra (sp,sts) /\ IMAGE A X SUBSET sts /\
                countable X ==> BIGUNION {A x | x IN X} IN sts``,
  RW_TAC std_ss [] THEN
  KNOW_TAC ``(IMAGE (\i. if i IN X then (A:'b->'a->bool) i else {}) UNIV)
              SUBSET sts`` THENL
  [SIMP_TAC std_ss [SUBSET_DEF, IN_IMAGE, IN_UNIV] THEN RW_TAC std_ss [] THEN
   COND_CASES_TAC THENL [ASM_SET_TAC [], FULL_SIMP_TAC std_ss [sigma_algebra_iff2]],
   DISCH_TAC] THEN
  KNOW_TAC ``BIGUNION {(\i. if i IN X then A i else {}) x | x IN UNIV}
             IN sts`` THENL
  [ALL_TAC, DISCH_TAC THEN
   KNOW_TAC ``
    BIGUNION {(\i. if i IN X then (A:'b->'a->bool) i else {}) x | x IN univ(:'b)} =
    BIGUNION {A x | x IN X}`` THENL [ALL_TAC, METIS_TAC []] THEN
   SIMP_TAC std_ss [EXTENSION, IN_BIGUNION, GSPECIFICATION] THEN GEN_TAC THEN
   EQ_TAC THEN REPEAT STRIP_TAC THENL
   [EXISTS_TAC ``s:'a->bool`` THEN FULL_SIMP_TAC std_ss [] THEN
    POP_ASSUM K_TAC THEN POP_ASSUM K_TAC THEN POP_ASSUM MP_TAC THEN
    COND_CASES_TAC THEN ASM_SET_TAC [], ALL_TAC] THEN
   EXISTS_TAC ``s:'a->bool`` THEN FULL_SIMP_TAC std_ss [IN_UNIV] THEN
   EXISTS_TAC ``x':'b`` THEN FULL_SIMP_TAC std_ss []] THEN
  RULE_ASSUM_TAC (SIMP_RULE std_ss [SIGMA_ALGEBRA]) THEN
  REPEAT (POP_ASSUM MP_TAC) THEN REWRITE_TAC [subsets_def] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_SIMP_TAC std_ss [GSYM IMAGE_DEF] THEN
  KNOW_TAC ``countable (IMAGE (A:'b->'a->bool) X)`` THENL
  [rw[image_countable], DISCH_TAC] THEN
  ONCE_REWRITE_TAC [SET_RULE ``IMAGE (\x. if x IN X then A x else {}) univ(:'b) =
                    (IMAGE A X) UNION IMAGE (\x. {}) (UNIV DIFF X)``] THEN
  MATCH_MP_TAC union_countable THEN CONJ_TAC THENL
  [FULL_SIMP_TAC std_ss [COUNTABLE_ALT] THEN
   METIS_TAC [], ALL_TAC] THEN
  SIMP_TAC std_ss [pred_setTheory.COUNTABLE_ALT] THEN Q.EXISTS_TAC `(\n. {}):num->'a->bool` THEN
  SIMP_TAC std_ss [IN_IMAGE] THEN METIS_TAC []);

(* ------------------------------------------------------------------------- *)
(* Initial Sigma Algebra                                                     *)
(* ------------------------------------------------------------------------- *)

val (sigma_sets_rules, sigma_sets_ind, sigma_sets_cases) = Hol_reln `
  (sigma_sets sp st {}) /\
  (!a. st a ==> sigma_sets sp st a) /\
  (!a. sigma_sets sp st a ==> sigma_sets sp st (sp DIFF a)) /\
  (!A. (!i. sigma_sets sp st ((A:num->'a->bool) i)) ==>
             sigma_sets sp st (BIGUNION {A i | i IN UNIV}))`;

val sigma_sets_basic = store_thm ("sigma_sets_basic",
 ``!sp st a. a IN st ==> a IN sigma_sets sp st``,
  SIMP_TAC std_ss [SPECIFICATION, sigma_sets_rules]);

val sigma_sets_empty = store_thm ("sigma_sets_empty",
 ``!sp st. {} IN sigma_sets sp st``,
  SIMP_TAC std_ss [SPECIFICATION, sigma_sets_rules]);

val sigma_sets_compl = store_thm ("sigma_sets_compl",
  ``!sp st a. a IN sigma_sets sp st ==> sp DIFF a IN sigma_sets sp st``,
  SIMP_TAC std_ss [SPECIFICATION, sigma_sets_rules]);

val sigma_sets_union = store_thm ("sigma_sets_union",
  ``!sp st A. (!i. (A:num->'a->bool) i IN sigma_sets sp st) ==>
                BIGUNION {A i | i IN UNIV} IN sigma_sets sp st``,
  SIMP_TAC std_ss [SPECIFICATION, sigma_sets_rules]);

val sigma_sets_subset = store_thm ("sigma_sets_subset",
  ``!sp sts st. sigma_algebra (sp,sts) /\ st SUBSET sts ==>
                sigma_sets sp st SUBSET sts``,
  REPEAT STRIP_TAC THEN SIMP_TAC std_ss [SPECIFICATION, SUBSET_DEF] THEN
  HO_MATCH_MP_TAC sigma_sets_ind THEN FULL_SIMP_TAC std_ss [sigma_algebra_alt_eq,
    algebra_alt_eq, ring, semiring, subset_class_def] THEN
  REPEAT STRIP_TAC THENL
  [ASM_SET_TAC [],
   ASM_SET_TAC [],
   ONCE_REWRITE_TAC [GSYM SPECIFICATION] THEN MATCH_MP_TAC Diff THEN
   FULL_SIMP_TAC std_ss [ring, semiring, subset_class_def] THEN ASM_SET_TAC [],
   ONCE_REWRITE_TAC [GSYM SPECIFICATION] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
   REPEAT STRIP_TAC THEN ASM_SET_TAC []]);

val sigma_sets_into_sp = store_thm ("sigma_sets_into_sp",
 ``!sp st. st SUBSET POW sp ==> !x. x IN sigma_sets sp st ==> x SUBSET sp``,
  REPEAT GEN_TAC THEN DISCH_TAC THEN SIMP_TAC std_ss [SPECIFICATION] THEN
  HO_MATCH_MP_TAC sigma_sets_ind THEN FULL_SIMP_TAC std_ss [POW_DEF] THEN
  REPEAT STRIP_TAC THEN ASM_SET_TAC []);

val sigma_algebra_sigma_sets = store_thm ("sigma_algebra_sigma_sets",
 ``!sp st. st SUBSET POW sp ==> sigma_algebra (sp, sigma_sets sp st)``,
  RW_TAC std_ss [sigma_algebra_iff2] THENL
  [SIMP_TAC std_ss [SUBSET_DEF] THEN
   SIMP_TAC std_ss [POW_DEF, GSPECIFICATION] THEN
   METIS_TAC [sigma_sets_into_sp],
   METIS_TAC [sigma_sets_empty],
   METIS_TAC [sigma_sets_compl],
   MATCH_MP_TAC sigma_sets_union THEN ASM_SET_TAC []]);

val sigma_sets_least_sigma_algebra = store_thm ("sigma_sets_least_sigma_algebra",
 ``!sp A. A SUBSET POW sp ==>
          (sigma_sets sp A =
           BIGINTER {B | A SUBSET B /\ sigma_algebra (sp,B)})``,
  REPEAT STRIP_TAC THEN
  KNOW_TAC ``!B X. A SUBSET B /\ sigma_algebra (sp,B) /\
                   X IN sigma_sets sp A ==> X IN B`` THENL
  [REPEAT STRIP_TAC THEN UNDISCH_TAC ``A SUBSET (B:('a->bool)->bool)`` THEN
   UNDISCH_TAC ``sigma_algebra (sp, B)`` THEN REWRITE_TAC [AND_IMP_INTRO] THEN
   DISCH_THEN (MP_TAC o MATCH_MP sigma_sets_subset) THEN ASM_SET_TAC [],
   DISCH_TAC] THEN
  KNOW_TAC
   ``!X. X IN BIGINTER {B | A SUBSET B /\ sigma_algebra (sp,B)} ==>
         !B. A SUBSET B ==> sigma_algebra (sp,B) ==> X IN B`` THENL
  [STRIP_TAC THEN ASM_SIMP_TAC std_ss [IN_BIGINTER, GSPECIFICATION],
   DISCH_TAC] THEN
  SIMP_TAC std_ss [EXTENSION] THEN GEN_TAC THEN EQ_TAC THENL
  [DISCH_TAC THEN SIMP_TAC std_ss [IN_BIGINTER, GSPECIFICATION] THEN
   REPEAT STRIP_TAC THEN FULL_SIMP_TAC std_ss [SUBSET_DEF], ALL_TAC] THEN
  DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o SPEC ``x:'a->bool``) THEN
  ASM_REWRITE_TAC [] THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  REPEAT CONJ_TAC THENL
  [ASM_SIMP_TAC std_ss [SUBSET_DEF, sigma_sets_basic],
   ASM_SIMP_TAC std_ss [sigma_algebra_sigma_sets],
   ALL_TAC] THEN
  FULL_SIMP_TAC std_ss [AND_IMP_INTRO] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_SIMP_TAC std_ss [sigma_algebra_sigma_sets] THEN
  ASM_SIMP_TAC std_ss [SUBSET_DEF, sigma_sets_basic]);

val sigma_sets_top = store_thm ("sigma_sets_top",
 ``!sp A. sp IN sigma_sets sp A``,
 METIS_TAC [sigma_sets_compl, sigma_sets_empty, DIFF_EMPTY]);

val sigma_sets_Un = store_thm ("sigma_sets_Un",
 ``!sp st a b. a IN sigma_sets sp st /\ b IN sigma_sets sp st ==>
               a UNION b IN sigma_sets sp st``,
  REPEAT STRIP_TAC THEN REWRITE_TAC [Un_range_binary] THEN
  MATCH_MP_TAC sigma_sets_union THEN GEN_TAC THEN
  RW_TAC std_ss [binary]);

val sigma_sets_Inter = store_thm ("sigma_sets_Inter",
 ``!sp st A. st SUBSET POW sp ==>
          (!i. (A:num->'a->bool) i IN sigma_sets sp st) ==>
          BIGINTER {A i | i IN UNIV} IN sigma_sets sp st``,
  REPEAT STRIP_TAC THEN
  KNOW_TAC ``(!i:num. A i IN sigma_sets sp st) ==>
             (!i:num. sp DIFF A i IN sigma_sets sp st)`` THENL
  [METIS_TAC [sigma_sets_compl], DISCH_TAC] THEN
  KNOW_TAC ``BIGUNION {sp DIFF A i | (i:num) IN UNIV} IN sigma_sets sp st`` THENL
  [ONCE_REWRITE_TAC [METIS [] ``sp DIFF A i = (\i. sp DIFF A i) i``] THEN
   MATCH_MP_TAC sigma_sets_union THEN METIS_TAC [], DISCH_TAC] THEN
  KNOW_TAC
   ``sp DIFF BIGUNION {sp DIFF A i | (i:num) IN UNIV} IN sigma_sets sp st`` THENL
  [MATCH_MP_TAC sigma_sets_compl THEN METIS_TAC [], DISCH_TAC] THEN
  KNOW_TAC ``sp DIFF BIGUNION {sp DIFF A i | i IN UNIV} =
             BIGINTER {A i | (i:num) IN UNIV}`` THENL
  [ALL_TAC, METIS_TAC[]] THEN
  SIMP_TAC std_ss [EXTENSION] THEN GEN_TAC THEN EQ_TAC THENL
  [SIMP_TAC std_ss [IN_DIFF, IN_BIGUNION, IN_BIGINTER, GSPECIFICATION] THEN
   RW_TAC std_ss [] THEN POP_ASSUM K_TAC THEN
   POP_ASSUM (MP_TAC o SPEC ``sp DIFF (A:num->'a->bool) i``) THEN
   ASM_SET_TAC [], ALL_TAC] THEN
  SIMP_TAC std_ss [IN_BIGINTER, IN_DIFF, IN_BIGUNION, GSPECIFICATION] THEN
  RW_TAC std_ss [IN_UNIV] THENL
  [FIRST_X_ASSUM (MP_TAC o SPEC ``(A:num->'a->bool) i``) THEN
   KNOW_TAC ``(?i'. A i = (A:num->'a->bool) i')`` THENL
   [METIS_TAC [], DISCH_TAC THEN ASM_REWRITE_TAC []] THEN
   SPEC_TAC (``x``,``x``) THEN REWRITE_TAC [GSYM SUBSET_DEF] THEN
   UNDISCH_TAC ``st SUBSET POW (sp:'a->bool)`` THEN
   DISCH_THEN (MP_TAC o MATCH_MP sigma_sets_into_sp) THEN
   METIS_TAC [], ALL_TAC] THEN
  ASM_CASES_TAC ``x NOTIN s`` THEN FULL_SIMP_TAC std_ss [] THEN
  RW_TAC std_ss [EXTENSION] THEN EXISTS_TAC ``x`` THEN
  ASM_SIMP_TAC std_ss [IN_DIFF] THEN DISJ2_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN METIS_TAC []);

val sigma_sets_INTER = store_thm ("sigma_sets_INTER",
 ``!sp st A N. st SUBSET POW sp /\  (!i:num. i IN N ==> A i IN sigma_sets sp st) /\
           (N <> {}) ==> BIGINTER {A i | i IN N} IN sigma_sets sp st``,
  REPEAT STRIP_TAC THEN
  KNOW_TAC ``!i:num. (if i IN N then A i else sp) IN sigma_sets sp st`` THENL
  [GEN_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC std_ss [] THEN
   SIMP_TAC std_ss [sigma_sets_top], DISCH_TAC] THEN
  KNOW_TAC ``BIGINTER {(if i IN N then (A:num->'a->bool) i else sp) | i IN UNIV} IN
             sigma_sets sp st`` THENL
  [ASM_SIMP_TAC std_ss [sigma_sets_Inter], DISCH_TAC] THEN
  KNOW_TAC ``BIGINTER {(if i IN N then (A:num->'a->bool) i else sp) | i IN UNIV} =
             BIGINTER {A i | i IN N}`` THENL
  [ALL_TAC, METIS_TAC []] THEN
  UNDISCH_TAC ``st SUBSET POW (sp:'a->bool)``  THEN
  DISCH_THEN (MP_TAC o MATCH_MP sigma_sets_into_sp) THEN DISCH_TAC THEN
  ASM_SET_TAC []);

val sigma_sets_eq = store_thm ("sigma_sets_eq",
 ``!sp sts. sigma_algebra (sp,sts) ==>
            (sigma_sets sp sts = sts)``,
  REPEAT STRIP_TAC THEN EVAL_TAC THEN CONJ_TAC THENL
  [MATCH_MP_TAC sigma_sets_subset THEN ASM_SIMP_TAC std_ss [SUBSET_REFL],
   SIMP_TAC std_ss [SUBSET_DEF, sigma_sets_basic]]);

val sigma_sets_superset_generator = store_thm ("sigma_sets_superset_generator",
  ``!X A. A SUBSET sigma_sets X A``,
  SIMP_TAC std_ss [SUBSET_DEF, sigma_sets_basic]);

(* ------------------------------------------------------------------------- *)
(* Disjoint families                                                         *)
(* ------------------------------------------------------------------------- *)

val disjoint_family_on = new_definition ("disjoint_family_on",
  ``disjoint_family_on a s =
    (!m n. m IN s /\ n IN s /\ (m <> n) ==> (a m INTER a n = {}))``);

val disjoint_family = new_definition ("disjoint_family",
  ``disjoint_family A = disjoint_family_on A UNIV``);

(* ------------------------------------------------------------------------- *)
(* Measure type                                                              *)
(* ------------------------------------------------------------------------- *)

val _ = hide "positive_alt";

val positive_alt = new_definition ("positive_alt",
  ``positive_alt M u <=> (u {} = 0:extreal) /\ !a. a IN M ==> 0 <= u a``);

val positive_alt_eq = store_thm ("positive_alt_eq",
  ``!sp M u. positive (sp, M, u) = (u {} = 0) /\ !a. a IN M ==> 0 <= u a``,
  METIS_TAC [positive_def, measure_def, measurable_sets_def]);

val countably_additive_alt = new_definition ("countably_additive_alt",
  ``countably_additive_alt M (u:('a->bool)->extreal) <=>
    (!A. IMAGE A UNIV SUBSET M ==> disjoint_family A ==>
        BIGUNION {A i | i IN UNIV} IN M ==>
        ((u (BIGUNION {A i | i IN univ(:num)})) = suminf (u o A)))``);

val lemma1 = store_thm ("lemma1",
  ``!A sp M u. A IN (univ(:num) -> measurable_sets (sp,M,u)) =
              IMAGE A UNIV SUBSET M``,
  REPEAT STRIP_TAC THEN SIMP_TAC std_ss [measurable_sets_def] THEN
  EVAL_TAC THEN SRW_TAC[] [IN_FUN_SET,IN_UNIV,SUBSET_DEF,IMAGE_DEF] THEN METIS_TAC[]);

val lemma2 = store_thm ("lemma2",
  ``!A. (!m n. m <> n ==> DISJOINT (A m) (A n)) = disjoint_family A``,
  STRIP_TAC THEN SIMP_TAC std_ss [disjoint_family, disjoint_family_on] THEN
  SET_TAC []);

val lemma3 = store_thm ("lemma3",
  ``!A sp M u. BIGUNION (IMAGE A univ(:num)) IN measurable_sets (sp,M,u) =
               BIGUNION {A i | i IN UNIV} IN M``,
  REPEAT STRIP_TAC THEN SIMP_TAC std_ss [measurable_sets_def, IMAGE_DEF]);

val countably_additive_alt_eq = store_thm ("countably_additive_alt_eq",
  ``!sp M u. countably_additive (sp,M,u) <=>
    (!A. IMAGE A UNIV SUBSET M ==> disjoint_family A ==>
        BIGUNION {A i | i IN UNIV} IN M ==>
        ((u (BIGUNION {A i | i IN univ(:num)})) = suminf (u o A)))``,
  SIMP_TAC std_ss [countably_additive_def] THEN REPEAT STRIP_TAC THEN
  SIMP_TAC std_ss [measure_def, o_DEF, lemma2, lemma3] THEN
  SIMP_TAC std_ss [GSYM IMAGE_DEF, SUBSET_DEF, measurable_sets_def] THEN
  EQ_TAC THEN RW_TAC std_ss [] THENL
  [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC std_ss [] THEN
   EVAL_TAC THEN ASM_SET_TAC [IN_IMAGE,IN_FUNSET], ALL_TAC] THEN
  FIRST_X_ASSUM (MP_TAC o Q.SPEC `f`) THEN ASM_SIMP_TAC std_ss [] THEN
  DISCH_THEN (MATCH_MP_TAC) THEN POP_ASSUM K_TAC THEN POP_ASSUM K_TAC THEN
  POP_ASSUM MP_TAC THEN EVAL_TAC THEN SET_TAC []);

val measure_space_alt = new_definition ("measure_space_alt",
  ``measure_space_alt sp A u <=> sigma_algebra_alt sp A /\ positive_alt A u /\
                                 countably_additive_alt A u``);

val measure_space_alt_eq = store_thm ("measure_space_alt_eq",
  ``!sp M u. measure_space (sp,M,u) =
             sigma_algebra_alt sp M /\ positive_alt M u /\
             countably_additive_alt M u``,
  SIMP_TAC std_ss [measure_space_def, m_space_def, measurable_sets_def] THEN
  SIMP_TAC std_ss [sigma_algebra_alt_eq, sigma_algebra_alt] THEN
  SIMP_TAC std_ss [positive_alt_eq, positive_alt] THEN
  SIMP_TAC std_ss [countably_additive_alt_eq, countably_additive_alt]);

val measure_of = new_definition ("measure_of",
  ``measure_of (sp,A,u) = (sp,
     (if A SUBSET POW sp then (sigma_sets sp A) else {{};sp}),
     (\a. if a IN sigma_sets sp A /\ measure_space (sp, sigma_sets sp A, u)
        then u a else 0))``);

val sup_sing = store_thm ("sup_sing",
  ``!a:extreal. sup {a} = a``,
  REWRITE_TAC [METIS [EXTENSION, IN_SING, IN_DEF] ``{a} = (\x. x = a)``] THEN
  SIMP_TAC std_ss [sup_const]);

val suminf_0 = store_thm ("suminf_0",
  ``suminf (\x. 0) = 0:extreal``,
  RW_TAC std_ss [ext_suminf_def] THEN
  SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_ZERO, FINITE_COUNT] THEN
  SIMP_TAC std_ss [IMAGE_DEF, IN_UNIV] THEN
  ONCE_REWRITE_TAC [SET_RULE ``{0 | n | T} = {0}``] THEN
  METIS_TAC [sup_sing]);

val measure_space_0 = store_thm ("measure_space_0",
  ``!sp A. A SUBSET POW sp ==> measure_space (sp, sigma_sets sp A, (\x. 0))``,
  SIMP_TAC std_ss [measure_space_def] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  SIMP_TAC std_ss [m_space_def, measurable_sets_def] THEN
  FULL_SIMP_TAC std_ss [sigma_algebra_sigma_sets] THEN
  SIMP_TAC real_ss [positive_def, countably_additive_def] THEN
  SIMP_TAC std_ss [measure_def, le_refl, o_DEF] THEN
  RW_TAC std_ss [suminf_0]);

val sigma_algebra_trivial = store_thm ("sigma_algebra_trivial",
  ``!s. sigma_algebra (s, {{}; s})``,
  GEN_TAC THEN REWRITE_TAC [SIGMA_ALGEBRA] THEN
  REWRITE_TAC [space_def, subsets_def] THEN REWRITE_TAC [subset_class_def] THEN
  REWRITE_TAC [SET_RULE ``s IN {a;b} = ((s = a) \/ (s = b))``] THEN
  REPEAT (CONJ_TAC THENL [SET_TAC [], ALL_TAC]) THEN REPEAT STRIP_TAC THEN
  FULL_SIMP_TAC std_ss [SUBSET_DEF] THEN
  FULL_SIMP_TAC std_ss [SET_RULE ``s IN {a;b} = ((s = a) \/ (s = b))``] THEN
  SIMP_TAC std_ss [EXTENSION, BIGUNION, GSPECIFICATION] THEN
  ASM_SET_TAC []);

val measure_space_0' = store_thm ("measure_space_0'",
  ``!sp. measure_space (sp, {{}; sp}, (\x. 0))``,
  GEN_TAC THEN SIMP_TAC std_ss [measure_space_def] THEN
  SIMP_TAC real_ss [positive_def, measure_def] THEN CONJ_TAC THENL
  [ALL_TAC,
   SIMP_TAC std_ss [countably_additive_def, measure_def, o_DEF] THEN
   RW_TAC std_ss [suminf_0] THEN SIMP_TAC std_ss [le_refl]] THEN
  SIMP_TAC std_ss [sigma_algebra_iff2, SUBSET_DEF, POW_DEF] THEN
  SIMP_TAC std_ss [measurable_sets_def, m_space_def] THEN
  SIMP_TAC std_ss [SET_RULE ``a IN {b;c} = ((a = b) \/ (a = c))``] THEN
  SET_TAC []);

val measure_space_closed = store_thm ("measure_space_closed",
  ``!sp M u. measure_space (sp, M, u) ==> M SUBSET POW sp``,
  REPEAT GEN_TAC THEN SIMP_TAC std_ss [measure_space_def, sigma_algebra_iff2] THEN
  SIMP_TAC std_ss [measurable_sets_def, m_space_def]);

val positive_cong_eq = store_thm ("positive_cong_eq",
  ``!sp M u u'. ring sp M /\ (!a. a IN M ==> (u' a = u a)) ==>
                (positive (sp,M,u) = positive (sp,M,u'))``,
  SIMP_TAC std_ss [positive_def, measure_def, measurable_sets_def] THEN
  RW_TAC std_ss [ring, semiring, subset_class_def]);

val countably_additive_eq = store_thm ("countably_additive_eq",
  ``!sp M u u'. (!a. a IN M ==> (u' a = u a)) ==>
                (countably_additive (sp,M,u') = countably_additive (sp,M,u))``,
  SIMP_TAC std_ss [countably_additive_def] THEN
  REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM (MP_TAC o SPEC ``f:num->'a->bool``) THEN
  FULL_SIMP_TAC std_ss [measurable_sets_def, measure_def, o_DEF] THEN
  DISCH_TAC THEN AP_TERM_TAC THEN ABS_TAC THENL
  [ALL_TAC, ONCE_REWRITE_TAC [EQ_SYM_EQ]] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN POP_ASSUM K_TAC THEN
  POP_ASSUM K_TAC THEN POP_ASSUM K_TAC THEN POP_ASSUM MP_TAC THEN
  EVAL_TAC THEN SET_TAC []);

val measure_space_eq = store_thm ("measure_space_eq",
  ``!sp A u u'. A SUBSET POW sp /\
             (!a. a IN sigma_sets sp A ==> (u a = u' a)) ==>
             (measure_space (sp, (sigma_sets sp A), u) =
              measure_space (sp, (sigma_sets sp A), u'))``,
  REPEAT STRIP_TAC THEN POP_ASSUM MP_TAC THEN FIRST_ASSUM MP_TAC THEN
  DISCH_THEN (MP_TAC o MATCH_MP sigma_algebra_sigma_sets) THEN
  SIMP_TAC std_ss [measure_space_def] THEN REPEAT STRIP_TAC THEN
  SIMP_TAC std_ss [measurable_sets_def, m_space_def] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC (TAUT `(a = b) /\ (c = d) ==>
    ((a /\ c) = (b /\ d))`) THEN CONJ_TAC THENL
  [MATCH_MP_TAC positive_cong_eq THEN ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
   FULL_SIMP_TAC std_ss [sigma_algebra_alt_eq, algebra_alt_eq],
   MATCH_MP_TAC countably_additive_eq THEN ASM_REWRITE_TAC []]);

val measure_of_eq = store_thm ("measure_of_eq",
  ``!sp A u u'. A SUBSET POW sp /\ (!a. a IN sigma_sets sp A ==> (u a = u' a)) ==>
                (measure_of (sp,A,u) = measure_of (sp,A,u'))``,
  REPEAT GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM MP_TAC THEN
  DISCH_THEN (MP_TAC o MATCH_MP measure_space_eq) THEN
  SIMP_TAC std_ss [measure_of] THEN DISCH_TAC THEN
  ABS_TAC THEN COND_CASES_TAC THEN FULL_SIMP_TAC std_ss []);

val space_sets_measure_conv = store_thm ("space_sets_measure_conv",
  ``!sp A u. (m_space (measure_of (sp,A,u)) = sp) /\
             (measurable_sets (measure_of (sp,A,u)) =
              if A SUBSET POW sp then sigma_sets sp A else {{};sp}) /\
             (measure (measure_of (sp,A,u)) =
              (\a. if a IN sigma_sets sp A /\
               measure_space (sp, (sigma_sets sp A), u) then u a else 0))``,
  SIMP_TAC std_ss [m_space_def, measurable_sets_def, measure_of, measure_def]);

val space_measure_of_conv = store_thm ("space_measure_of_conv",
  ``!sp A u. (m_space (measure_of (sp,A,u)) = sp)``,
  SIMP_TAC std_ss [space_sets_measure_conv]);

val sets_measure_of_conv = store_thm ("sets_measure_of_conv",
  ``!sp A u. (measurable_sets (measure_of (sp,A,u)) =
              if A SUBSET POW sp then sigma_sets sp A else {{};sp})``,
  SIMP_TAC std_ss [space_sets_measure_conv]);

val measure_measure_of_conv = store_thm ("measure_measure_of_conv",
  ``!sp A u. (measure (measure_of (sp,A,u)) =
              (\a. if a IN sigma_sets sp A /\
               measure_space (sp, (sigma_sets sp A), u) then u a else 0))``,
  SIMP_TAC std_ss [space_sets_measure_conv]);

val measure_space_imp_sigma_sets_eq = store_thm ("measure_space_imp_sigma_sets_eq",
  ``!sp A u. A SUBSET POW sp /\ measure_space (sp,A,u) ==>
             (measurable_sets (sp,A,u) = sigma_sets sp A)``,
  SIMP_TAC std_ss [measure_space_def, m_space_def, measurable_sets_def] THEN
  SIMP_TAC std_ss [sigma_sets_eq]);

val sets_measure_of_eq = store_thm ("sets_measure_of_eq",
  ``!sp M u. sigma_algebra (sp,M) ==> (measurable_sets (measure_of (sp,M,u)) = M)``,
  REPEAT STRIP_TAC THEN KNOW_TAC ``M SUBSET POW sp`` THENL
  [FULL_SIMP_TAC std_ss [sigma_algebra_alt_eq, algebra_alt_eq, ring, semiring] THEN
   ASM_SET_TAC [subset_class_def, POW_DEF], DISCH_TAC] THEN
 FULL_SIMP_TAC std_ss [sets_measure_of_conv, sigma_sets_eq]);

val space_measure_of_eq = store_thm ("space_measure_of_eq",
  ``!sp M u. m_space (measure_of (sp,M,u)) = sp``,
  SIMP_TAC std_ss [space_measure_of_conv]);

(* ------------------------------------------------------------------------- *)
(* subsection {* Constructing simple @{typ "'a measure"} *}                  *)
(* ------------------------------------------------------------------------- *)

val measure_measure_of = store_thm ("measure_measure_of",
  ``!M sp A u X.
     (M = measure_of (sp,A,u)) /\ A SUBSET POW sp /\ positive (sp, measurable_sets M, u) /\
      countably_additive (sp, measurable_sets M, u) /\ X IN measurable_sets M ==>
     (measure M X = u X)``,
  RW_TAC std_ss [] THEN SIMP_TAC std_ss [measure_of, measure_def] THEN
  POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
  ASM_SIMP_TAC std_ss [sets_measure_of_conv] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC std_ss [measure_space_def, m_space_def, measurable_sets_def] THEN
  ASM_SIMP_TAC std_ss [sigma_algebra_sigma_sets]);

val measure_measure_of_sigma = store_thm ("measure_measure_of_sigma",
  ``!sp M u A. sigma_algebra (sp, M) /\ positive (sp, M, u) /\
               countably_additive (sp, M, u) /\ A IN M ==>
               (measure (measure_of (sp,M,u)) A = u A)``,
  RW_TAC std_ss [] THEN MATCH_MP_TAC measure_measure_of THEN
  EXISTS_TAC ``sp:'a->bool`` THEN EXISTS_TAC ``M:('a->bool)->bool`` THEN
  FIRST_ASSUM (ASSUME_TAC o MATCH_MP sets_measure_of_eq) THEN
  FULL_SIMP_TAC std_ss [sigma_algebra_iff2]);

val sets_eq_imp_space_eq = store_thm ("sets_eq_imp_space_eq",
  ``!M M'. measure_space M /\ measure_space M' /\
          (measurable_sets M = measurable_sets M') ==> (m_space M = m_space M')``,
  REPEAT STRIP_TAC THEN POP_ASSUM MP_TAC THEN
  FIRST_ASSUM (MP_TAC o MATCH_MP MEASURE_SPACE_MSPACE_MEASURABLE) THEN
  POP_ASSUM (MP_TAC o REWRITE_RULE [measure_space_def, sigma_algebra_iff2]) THEN
  FIRST_ASSUM (MP_TAC o MATCH_MP MEASURE_SPACE_MSPACE_MEASURABLE) THEN
  POP_ASSUM (MP_TAC o REWRITE_RULE [measure_space_def, sigma_algebra_iff2]) THEN
  REPEAT STRIP_TAC THEN FULL_SIMP_TAC std_ss [SUBSET_DEF, IN_POW] THEN
  ASM_SET_TAC []);

val measure_of_reduce = store_thm ("measure_of_reduce",
  ``!M. measure_of M = measure_of (m_space M, measurable_sets M, measure M)``,
  SIMP_TAC std_ss [MEASURE_SPACE_REDUCE]);

val measure_notin_sets = store_thm ("measure_notin_sets",
  ``!A M. measure_space M /\ A NOTIN measurable_sets M ==>
    (measure (measure_of M) A = 0)``,
  RW_TAC std_ss [] THEN ONCE_REWRITE_TAC [measure_of_reduce] THEN
  SIMP_TAC std_ss [measure_of, measure_def] THEN
  FULL_SIMP_TAC std_ss [measure_space_def, m_space_def, measurable_sets_def] THEN
  FIRST_ASSUM (ASSUME_TAC o MATCH_MP sigma_sets_eq) THEN METIS_TAC []);

val measure_eqI = store_thm ("measure_eqI",
  ``!M N. measure_space M /\ measure_space N /\
          (measurable_sets M = measurable_sets N) /\
          (!A. A IN measurable_sets M ==>
            (measure M A = measure N A)) ==>
          (measure_of M = measure_of N)``,
  RW_TAC std_ss [] THEN ONCE_REWRITE_TAC [measure_of_reduce] THEN
  KNOW_TAC ``m_space M = m_space N`` THENL
  [METIS_TAC [sets_eq_imp_space_eq], DISCH_TAC] THEN
  ASM_SIMP_TAC std_ss [] THEN MATCH_MP_TAC measure_of_eq THEN
  FULL_SIMP_TAC std_ss [measure_space_def] THEN
  FULL_SIMP_TAC std_ss [sigma_sets_eq, sigma_algebra_iff2]);

(* ------------------------------------------------------------------------- *)
(* Measurable funtions                                                       *)
(* ------------------------------------------------------------------------- *)

val measurable_space = store_thm ("measurable_space",
  ``!f M A. f IN measurable M A ==>
            !x. x IN space M ==> f x IN space A``,
  SIMP_TAC std_ss [measurable_def, GSPECIFICATION] THEN
  EVAL_TAC THEN SET_TAC []);

val measurable_sets = store_thm ("measurable_sets",
  ``!f M A. f IN measurable M A ==>
            !s. s IN subsets A ==> PREIMAGE f s INTER space M IN subsets M``,
  SIMP_TAC std_ss [measurable_def, GSPECIFICATION, IN_FUNSET]);

val measurable_sets_Collect = store_thm ("measurable_sets_Collect",
  ``!f M N P. f IN measurable M N /\ {x | x IN space N /\ P x} IN subsets N ==>
              {x | x IN space M /\ P (f x)} IN subsets M``,
  REPEAT STRIP_TAC THEN
  KNOW_TAC ``PREIMAGE (f:'a->'b) {x | x IN space N /\ P x} INTER space M =
                                 {x | x IN space M /\ P (f x)}`` THENL
  [FIRST_ASSUM (MP_TAC o MATCH_MP measurable_space) THEN
   DISCH_TAC THEN SIMP_TAC std_ss [PREIMAGE_def] THEN
   SIMP_TAC std_ss [INTER_DEF, EXTENSION, GSPECIFICATION] THEN
   ASM_SET_TAC [], DISCH_TAC] THEN METIS_TAC [measurable_sets]);

val measurable_cong_sets = store_thm ("measurable_cong_sets",
  ``!M N M' N'. measure_space M /\ measure_space M' /\
                measure_space N /\ measure_space N' /\
                (measurable_sets M = measurable_sets M') /\
                (measurable_sets N = measurable_sets N') ==>
                (measurable (m_space M, measurable_sets M)
                            (m_space N, measurable_sets N) =
                 measurable (m_space M', measurable_sets M')
                            (m_space N', measurable_sets N'))``,
  RW_TAC std_ss [] THEN
  KNOW_TAC ``(m_space M = m_space M') /\ (m_space N = m_space N')`` THENL
  [METIS_TAC [sets_eq_imp_space_eq], STRIP_TAC] THEN
  FULL_SIMP_TAC std_ss []);

val image_inter_cong = store_thm ("image_inter_cong",
  ``!(f:'a->'b) g s y. (!w. w IN s ==> (f w = g w)) ==>
              ((PREIMAGE f y) INTER s = (PREIMAGE g y) INTER s)``,
  RW_TAC std_ss [INTER_DEF, PREIMAGE_def] THEN
  ASM_SET_TAC []);

val measurable_cong = store_thm ("measurable_cong",
  ``!f g M N.
    (!w. w IN m_space M ==>  (f w = g w)) ==>
    (f IN measurable (m_space M, measurable_sets M)
                     (m_space N, measurable_sets N) =
     g IN measurable (m_space M, measurable_sets M)
                     (m_space N, measurable_sets N))``,
  RW_TAC std_ss [IN_MEASURABLE, IN_FUNSET] THEN EQ_TAC THEN
  RW_TAC std_ss [space_def, subsets_def] THEN
  FIRST_X_ASSUM (MP_TAC o MATCH_MP image_inter_cong) THEN
  METIS_TAC []);

val measurable_eqI = store_thm ("measurable_eqI",
  ``(m_space m1 = m_space m1') /\ (m_space m2 = m_space m2') /\
    (measurable_sets m1 = measurable_sets m1') /\
    (measurable_sets m2 = measurable_sets m2') ==>
    (measurable (m_space m1, measurable_sets m1)
                (m_space m2, measurable_sets m2) =
     measurable (m_space m1', measurable_sets m1')
                (m_space m2', measurable_sets m2'))``,
  FULL_SIMP_TAC std_ss []);

val measurable_compose = store_thm ("measurable_compose",
  ``!f g M N L. f IN measurable M N /\ g IN measurable N L ==>
                (\x. g (f x)) IN measurable M L``,
  REPEAT STRIP_TAC THEN SIMP_TAC std_ss [GSYM o_DEF] THEN
METIS_TAC [MEASURABLE_COMP]);

val measurable_const = store_thm ("measurable_const",
  ``!c M N. c IN m_space N /\ measure_space M /\ measure_space N ==>
       (\x. c) IN measurable (m_space M, measurable_sets M)
                             (m_space N, measurable_sets N)``,
  RW_TAC std_ss [measurable_def, IN_MEASURABLE, space_def, subsets_def] THEN
  FULL_SIMP_TAC std_ss [measure_space_def, IN_FUN_SET, PREIMAGE_def] THEN
  REWRITE_TAC [SET_RULE ``{x | x | c IN s} = if c IN s then UNIV else {}``] THEN
  COND_CASES_TAC THEN SIMP_TAC std_ss [INTER_EMPTY, INTER_UNIV] THENL
  [METIS_TAC [MEASURE_SPACE_MSPACE_MEASURABLE, measure_space_def],
   FULL_SIMP_TAC std_ss [sigma_algebra_iff2]]);

val measurable_If = store_thm ("measurable_If",
  ``!f g M N P. f IN measurable (m_space M, measurable_sets M)
                                (m_space N, measurable_sets N) /\
                g IN measurable (m_space M, measurable_sets M)
                                (m_space N, measurable_sets N) /\
             {x | x IN m_space M /\ P x} IN measurable_sets M /\
              measure_space M ==>
             (\x. if P x then f x else g x) IN
            measurable (m_space M, measurable_sets M)
                       (m_space N, measurable_sets N)``,
  RW_TAC std_ss [measurable_def, IN_MEASURABLE, space_def, subsets_def] THENL
  [FULL_SIMP_TAC std_ss [IN_FUNSET] THEN METIS_TAC [], ALL_TAC] THEN
  KNOW_TAC ``PREIMAGE (\x. if P x then f x else g x) s INTER m_space M =
   (((PREIMAGE f s) INTER m_space M) INTER {x | x IN m_space M /\ P x}) UNION
   (((PREIMAGE g s) INTER m_space M) INTER
     (m_space M DIFF {x | x IN m_space M /\ P x}))`` THENL
  [SIMP_TAC std_ss [PREIMAGE_def] THEN
   SET_TAC [], ALL_TAC] THEN
  ONCE_REWRITE_TAC [METIS  [subsets_def] ``measurable_sets M =
                       subsets (m_space M, measurable_sets M)``] THEN
  SIMP_TAC std_ss [] THEN DISC_RW_KILL THEN
  MATCH_MP_TAC ALGEBRA_UNION THEN FULL_SIMP_TAC std_ss [sigma_algebra_def] THEN
  CONJ_TAC THEN MATCH_MP_TAC ALGEBRA_INTER THEN
  FULL_SIMP_TAC std_ss [] THENL
  [METIS_TAC [subsets_def], ALL_TAC] THEN
  CONJ_TAC THENL [METIS_TAC [subsets_def], ALL_TAC] THEN
  MATCH_MP_TAC ALGEBRA_DIFF THEN FULL_SIMP_TAC std_ss [subsets_def] THEN
  MATCH_MP_TAC MEASURE_SPACE_MSPACE_MEASURABLE THEN ASM_REWRITE_TAC []);

val measurable_If_set = store_thm ("measurable_If_set",
  ``!f g M N A.
                f IN measurable (m_space M, measurable_sets M)
                                (m_space N, measurable_sets N) /\
                g IN measurable (m_space M, measurable_sets M)
                                (m_space N, measurable_sets N) /\
                A INTER m_space M IN measurable_sets M /\
                measure_space M ==> (\x. if x IN A then f x else g x) IN
           measurable (m_space M, measurable_sets M)
                      (m_space N, measurable_sets N)``,
  RW_TAC std_ss [] THEN
  ONCE_REWRITE_TAC [METIS [] ``(\x. if x IN A then f x else g x) =
                               (\x. if (\x. x IN A) x then f x else g x)``] THEN
  MATCH_MP_TAC measurable_If THEN ASM_SIMP_TAC std_ss [] THEN
  ONCE_REWRITE_TAC [SET_RULE ``{x | x IN m_space M /\ x IN A} =
                               A INTER m_space M``] THEN
  ASM_SIMP_TAC std_ss []);

(* ------------------------------------------------------------------------- *)
(* disjointed                                                                *)
(* ------------------------------------------------------------------------- *)

val disjointed = new_definition ("disjointed",
  ``!A n. disjointed A n =
     A n DIFF BIGUNION {A i | i IN {x:num | 0 <= x /\ x < n}}``);

val finite_UN_disjointed_eq = store_thm ("finite_UN_disjointed_eq",
  ``!A n. BIGUNION {disjointed A i | i IN {x | 0 <= x /\ x < n}} =
          BIGUNION {A i | i IN {x | 0 <= x /\ x < n}}``,
  GEN_TAC THEN INDUCT_TAC THENL
  [FULL_SIMP_TAC real_ss [GSPECIFICATION] THEN SET_TAC [], ALL_TAC] THEN
  FULL_SIMP_TAC real_ss [GSPECIFICATION] THEN
  GEN_REWR_TAC (LAND_CONV o ONCE_DEPTH_CONV)
   [ARITH_PROVE ``i < SUC n = i < n \/ (i = n)``] THEN
  REWRITE_TAC [SET_RULE ``BIGUNION {(A:num->'a->bool) i | i < n \/ (i = n)} =
                          BIGUNION {A i | i < n} UNION A n``] THEN
  ASM_REWRITE_TAC [disjointed] THEN SIMP_TAC std_ss [GSPECIFICATION] THEN
  SIMP_TAC std_ss [UNION_DEF] THEN
  REWRITE_TAC [ARITH_PROVE ``i < SUC n = i < n \/ (i = n)``] THEN
  REWRITE_TAC [SET_RULE ``BIGUNION {(A:num->'a->bool) i | i < n \/ (i = n)} =
                          BIGUNION {A i | i < n} UNION A n``] THEN
  SET_TAC []);

val atLeast0LessThan = store_thm ("atLeast0LessThan",
  ``{x:num | 0 <= x /\ x < n} = {x | x < n}``,
  SIMP_TAC arith_ss [EXTENSION, GSPECIFICATION]);

val UN_UN_finite_eq = store_thm ("UN_UN_finite_eq",
  ``!A.
     BIGUNION {BIGUNION {A i | i IN {x | 0 <= x /\ x < n}} | n IN univ(:num)} =
     BIGUNION {A n | n IN UNIV}``,
  SIMP_TAC std_ss [atLeast0LessThan] THEN
  RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_BIGUNION, IN_UNIV] THEN
  EQ_TAC THEN RW_TAC std_ss [] THENL
  [POP_ASSUM (MP_TAC o Q.SPEC `x`) THEN ASM_REWRITE_TAC [] THEN
   RW_TAC std_ss [] THEN METIS_TAC [], ALL_TAC] THEN
  Q.EXISTS_TAC `BIGUNION {A i | i IN {x | 0 <= x /\ x < SUC n}}` THEN
  RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_BIGUNION, IN_UNIV] THENL
  [ALL_TAC, METIS_TAC []] THEN Q.EXISTS_TAC `A n` THEN
  FULL_SIMP_TAC std_ss [] THEN Q.EXISTS_TAC `n` THEN
  SIMP_TAC arith_ss []);

val UN_finite_subset = store_thm ("UN_finite_subset",
  ``!A C. (!n. BIGUNION {A i | i IN {x | 0 <= x /\ x < n}} SUBSET C) ==>
               BIGUNION {A n | n IN univ(:num)} SUBSET C``,
  RW_TAC std_ss [] THEN ONCE_REWRITE_TAC [GSYM UN_UN_finite_eq] THEN
  FULL_SIMP_TAC std_ss [SUBSET_DEF] THEN RW_TAC std_ss [] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  FULL_SIMP_TAC std_ss [EXTENSION, GSPECIFICATION, IN_BIGUNION, IN_UNIV] THEN
  POP_ASSUM (MP_TAC o Q.SPEC `x`) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN
  Q.EXISTS_TAC `n` THEN Q.EXISTS_TAC `s'` THEN METIS_TAC []);

val UN_finite2_subset = store_thm ("UN_finite2_subset",
  ``!A B n k.
    (!n. BIGUNION {A i | i IN {x | 0 <= x /\ x < n}} SUBSET
         BIGUNION {B i | i IN {x | 0 <= x /\ x < n + k}}) ==>
         BIGUNION {A n | n IN univ(:num)} SUBSET BIGUNION {B n | n IN univ(:num)}``,
  RW_TAC std_ss [] THEN MATCH_MP_TAC UN_finite_subset THEN
  ONCE_REWRITE_TAC [GSYM UN_UN_finite_eq] THEN
  FULL_SIMP_TAC std_ss [SUBSET_DEF, IN_BIGUNION, GSPECIFICATION, IN_UNIV] THEN
  RW_TAC std_ss [] THEN FIRST_X_ASSUM (MP_TAC o Q.SPECL [`n`,`x`]) THEN
  Q_TAC SUFF_TAC `(?s. x IN s /\ ?i. (s = A i) /\ i < n)` THENL
  [ALL_TAC, METIS_TAC []] THEN DISCH_TAC THEN ASM_REWRITE_TAC [] THEN
  STRIP_TAC THEN Q.EXISTS_TAC `BIGUNION {B i | i < n + k}` THEN
  CONJ_TAC THENL [ALL_TAC, METIS_TAC []] THEN
  SIMP_TAC std_ss [IN_BIGUNION, GSPECIFICATION] THEN METIS_TAC []);

val UN_finite2_eq = store_thm ("UN_finite2_eq",
  ``!A B k.
    (!n. BIGUNION {A i | i IN {x | 0 <= x /\ x < n}} =
         BIGUNION {B i | i IN {x | 0 <= x /\ x < n + k}}) ==>
    (BIGUNION {A n | n IN univ(:num)} = BIGUNION {B n | n IN univ(:num)})``,
  RW_TAC std_ss [] THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
  [MATCH_MP_TAC  UN_finite2_subset THEN REWRITE_TAC [atLeast0LessThan] THEN
   METIS_TAC [SUBSET_REFL], ALL_TAC] THEN
  FULL_SIMP_TAC std_ss [SUBSET_DEF, IN_BIGUNION, IN_UNIV, GSPECIFICATION] THEN
  RW_TAC std_ss [] THEN FIRST_X_ASSUM (MP_TAC o Q.SPEC `SUC n`) THEN
  GEN_REWR_TAC LAND_CONV [EXTENSION] THEN
  DISCH_THEN (MP_TAC o Q.SPEC `x`) THEN
  SIMP_TAC std_ss [SUBSET_DEF, IN_BIGUNION, IN_UNIV, GSPECIFICATION] THEN
  Q_TAC SUFF_TAC `?s. x IN s /\ ?i. (s = B i) /\ i < SUC n + k` THENL
  [ALL_TAC,
   Q.EXISTS_TAC `B n` THEN ASM_REWRITE_TAC [] THEN
   Q.EXISTS_TAC `n` THEN SIMP_TAC arith_ss []] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC [] THEN RW_TAC std_ss [] THEN
  METIS_TAC []);

val UN_disjointed_eq = store_thm ("UN_disjointed_eq",
  ``!A. BIGUNION {disjointed A i | i IN UNIV} =
        BIGUNION {A i | i IN UNIV}``,
  GEN_TAC THEN MATCH_MP_TAC UN_finite2_eq THEN
  Q.EXISTS_TAC `0` THEN RW_TAC arith_ss [GSPECIFICATION] THEN
  ASSUME_TAC finite_UN_disjointed_eq THEN
  FULL_SIMP_TAC arith_ss [GSPECIFICATION]);

val disjoint_family_disjoint = store_thm ("disjoint_family_disjoint",
  ``!A. disjoint_family (disjointed A)``,
  SIMP_TAC std_ss [disjoint_family, disjoint_family_on, IN_UNIV] THEN
  RW_TAC std_ss [disjointed, EXTENSION, GSPECIFICATION, IN_INTER] THEN
  SIMP_TAC std_ss [NOT_IN_EMPTY, IN_DIFF, IN_BIGUNION] THEN
  ASM_CASES_TAC ``(x NOTIN A (m:num) \/ ?s. x IN s /\ s IN {A i | i < m})`` THEN
  ASM_REWRITE_TAC [] THEN RW_TAC std_ss [] THEN
  ASM_CASES_TAC ``x NOTIN A (n:num)`` THEN FULL_SIMP_TAC std_ss [] THEN
  FULL_SIMP_TAC std_ss [GSPECIFICATION] THEN
  ASM_CASES_TAC ``m < n:num`` THENL [METIS_TAC [], ALL_TAC] THEN
  `n < m:num` by ASM_SIMP_TAC arith_ss [] THEN METIS_TAC []);

val disjointed_subset = store_thm ("disjointed_subset",
  ``!A n. disjointed A n SUBSET A n``,
  RW_TAC std_ss [disjointed] THEN ASM_SET_TAC []);

val UNION_in_sets = store_thm ("UNION_in_sets",
  ``!sp sts A:num->'a->bool n.
       ring sp sts /\ IMAGE A UNIV SUBSET sts ==>
       BIGUNION {A i | i IN {x | 0 <= x /\ x < n}} IN sts``,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
  [SIMP_TAC real_ss [GSPECIFICATION] THEN
   REWRITE_TAC [SET_RULE ``{A i | i | F} = {}``] THEN
   SIMP_TAC std_ss [BIGUNION_EMPTY, ring, semiring],
   ALL_TAC] THEN
  FULL_SIMP_TAC std_ss [GSPECIFICATION] THEN
  RW_TAC std_ss [ARITH_PROVE ``i < SUC n = i < n \/ (i = n)``] THEN
  REWRITE_TAC [SET_RULE ``BIGUNION {(A:num->'a->bool) i | i < n \/ (i = n)} =
                          BIGUNION {A i | i < n} UNION A n``] THEN
  FULL_SIMP_TAC std_ss [ring_of_sets_iff] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN FULL_SIMP_TAC std_ss [SUBSET_DEF] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN SET_TAC []);

val range_disjointed_sets = store_thm ("range_disjointed_sets",
  ``!sp sts A. ring sp sts /\ IMAGE A UNIV SUBSET sts ==>
       IMAGE (\n. disjointed A n) UNIV SUBSET sts``,
  RW_TAC std_ss [disjointed] THEN
  SIMP_TAC std_ss [IN_IMAGE, SUBSET_DEF, IN_UNIV] THEN
  FULL_SIMP_TAC std_ss [GSPECIFICATION, ring_of_sets_iff] THEN
  RW_TAC std_ss [] THEN FIRST_ASSUM MATCH_MP_TAC THEN
  KNOW_TAC
  ``BIGUNION {(A:num->'a->bool) i | i IN {x | 0 <= x /\ x < n}} IN sts`` THENL
  [MATCH_MP_TAC UNION_in_sets THEN SIMP_TAC std_ss [ring_of_sets_iff] THEN
   METIS_TAC [], DISCH_TAC] THEN
  FULL_SIMP_TAC std_ss [GSPECIFICATION, SUBSET_DEF] THEN ASM_SET_TAC []);

(* ------------------------------------------------------------------------- *)
(* dynkin_system                                                             *)
(* ------------------------------------------------------------------------- *)

val dynkin_system = new_definition ("dynkin_system",
  ``dynkin_system sp st = subset_class sp st /\ sp IN st /\
           (!A. A IN st ==> sp DIFF A IN st) /\
           (!A. disjoint_family A ==> IMAGE A UNIV SUBSET st ==>
                BIGUNION (IMAGE A univ(:num)) IN st)``);

val dynkin_systemI = store_thm ("dynkin_systemI",
  ``!sp st.
    (!A. A IN st ==> A SUBSET sp) /\ sp IN st /\
    (!A. A IN st ==> sp DIFF A IN st) /\
    (!A. disjoint_family A ==> IMAGE A UNIV SUBSET st ==>
         BIGUNION (IMAGE A univ(:num)) IN st) ==>
    dynkin_system sp st``,
  SET_TAC [dynkin_system, subset_class_def]);

val dynkin_system_trivial = store_thm ("dynkin_system_trivial",
  ``!A. dynkin_system A (POW A)``,
  RW_TAC std_ss [dynkin_system, IN_POW, subset_class_def] THENL
  [SET_TAC [], SET_TAC [], ALL_TAC] THEN
  FULL_SIMP_TAC std_ss [SUBSET_DEF, IN_POW, IN_BIGUNION] THEN
  METIS_TAC []);

val sigma_algebra_imp_dynkin_system = store_thm ("sigma_algebra_imp_dynkin_system",
  ``!sp st. sigma_algebra (sp,st) ==> dynkin_system sp st``,
  RW_TAC std_ss [dynkin_system, sigma_algebra_alt_eq, algebra_def] THEN
  FULL_SIMP_TAC std_ss [subsets_def, space_def, subset_class_def] THENL
  [FIRST_X_ASSUM (MP_TAC o Q.SPEC `{}`) THEN
   FIRST_X_ASSUM (MP_TAC o Q.SPEC `{}`) THEN
   ASM_SIMP_TAC std_ss [DIFF_EMPTY],
   ALL_TAC] THEN
  SIMP_TAC std_ss [IMAGE_DEF] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_SET_TAC []);

(* ------------------------------------------------------------------------- *)
(* Int_stable                                                                *)
(* ------------------------------------------------------------------------- *)

val Int_stable = new_definition ("Int_stable",
  ``Int_stable M = (!a b. a IN M /\ b IN M ==> a INTER b IN M)``);

val sigma_algebra_disjoint_iff = store_thm ("sigma_algebra_disjoint_iff",
  ``!sp st. sigma_algebra (sp,st) = algebra (sp,st) /\
             (!A. IMAGE A univ(:num) SUBSET st ==> disjoint_family A ==>
                  BIGUNION (IMAGE A UNIV) IN st)``,
  RW_TAC std_ss [] THEN EQ_TAC THEN RW_TAC std_ss [] THEN
  `algebra (sp,st)` by METIS_TAC [sigma_algebra_def] THENL
  [ALL_TAC, FULL_SIMP_TAC std_ss [algebra_def]] THEN
  FULL_SIMP_TAC std_ss [sigma_algebra_iff2, space_def, subsets_def] THEN
  TRY (METIS_TAC [IMAGE_DEF]) THEN
  FULL_SIMP_TAC std_ss [GSYM IMAGE_DEF, POW_DEF, subset_class_def] THEN
  CONJ_TAC THENL [ASM_SET_TAC [], ALL_TAC] THEN RW_TAC std_ss [] THEN
  `algebra (sp,st)` by
  METIS_TAC [algebra_def, subset_class_def, space_def, subsets_def] THEN
  FIRST_X_ASSUM (MP_TAC o Q.SPEC `disjointed A`) THEN
  SIMP_TAC std_ss [disjoint_family_disjoint] THEN
  Q_TAC SUFF_TAC `IMAGE (disjointed A) univ(:num) SUBSET st` THENL
  [DISCH_TAC THEN ASM_REWRITE_TAC [],
   ONCE_REWRITE_TAC [METIS [ETA_AX] ``(disjointed A) = (\i. disjointed A i)``] THEN
   MATCH_MP_TAC range_disjointed_sets THEN Q.EXISTS_TAC `sp` THEN
   ASM_SIMP_TAC std_ss [ring, semiring] THEN
   FULL_SIMP_TAC std_ss [ALGEBRA_ALT_INTER, space_def, subsets_def] THEN
   `algebra (sp,st)` by METIS_TAC [ALGEBRA_ALT_INTER, space_def, subsets_def] THEN
   RW_TAC std_ss [] THEN Q.EXISTS_TAC `{s DIFF t}` THEN
   SIMP_TAC std_ss [BIGUNION_SING, FINITE_SING, disjoint_sing] THEN
   RW_TAC std_ss [IN_SING, SUBSET_DEF] THEN
   ONCE_REWRITE_TAC [METIS [subsets_def]
    ``s DIFF t IN st = s DIFF t IN subsets (sp,st)``] THEN
   MATCH_MP_TAC ALGEBRA_DIFF THEN ASM_SIMP_TAC std_ss [subsets_def]] THEN
  SIMP_TAC std_ss [IMAGE_DEF, UN_disjointed_eq]);

val sigma_algebra_eq_Int_stable = store_thm ("sigma_algebra_eq_Int_stable",
  ``!sp st. dynkin_system sp st ==>
     (sigma_algebra (sp,st) = Int_stable st)``,
  RW_TAC std_ss [] THEN EQ_TAC THENL
  [RW_TAC std_ss [sigma_algebra_alt_eq, Int_stable] THEN
   METIS_TAC [ALGEBRA_ALT_INTER, subsets_def, space_def],
   ALL_TAC] THEN
  FULL_SIMP_TAC std_ss [dynkin_system] THEN
  RW_TAC std_ss [sigma_algebra_disjoint_iff, algebra_iff_Un] THENL
  [FULL_SIMP_TAC std_ss [POW_DEF, subset_class_def] THEN
   ASM_SET_TAC [],
   FIRST_X_ASSUM (MP_TAC o Q.SPEC `sp`) THEN
   FIRST_X_ASSUM (MP_TAC o Q.SPEC `sp`) THEN
   ASM_SIMP_TAC std_ss [DIFF_EQ_EMPTY],
   ALL_TAC] THEN
  `{} IN st` by (FIRST_X_ASSUM (MP_TAC o Q.SPEC `sp`) THEN
                 FIRST_X_ASSUM (MP_TAC o Q.SPEC `sp`) THEN
                 ASM_SIMP_TAC std_ss [DIFF_EQ_EMPTY]) THEN
  `algebra (sp,st)` by
   METIS_TAC [ALGEBRA_ALT_INTER, space_def, subsets_def, Int_stable] THEN
  METIS_TAC [algebra_def, subsets_def, space_def]);

(* ------------------------------------------------------------------------- *)
(* dynkin                                                                    *)
(* ------------------------------------------------------------------------- *)

val dynkin = new_definition ("dynkin",
  ``dynkin sp st = BIGINTER {D | dynkin_system sp D /\ st SUBSET D}``);

val dynkin_system_dynkin = store_thm ("dynkin_system_dynkin",
  ``!sp st. st SUBSET POW sp ==> dynkin_system sp (dynkin sp st)``,
  RW_TAC std_ss [] THEN MATCH_MP_TAC dynkin_systemI THEN
  CONJ_TAC THENL
  [RW_TAC std_ss [dynkin, IN_BIGINTER, GSPECIFICATION] THEN
   POP_ASSUM (MP_TAC o Q.SPEC `POW sp`) THEN
   ASM_SIMP_TAC std_ss [dynkin_system_trivial] THEN
   ASM_SET_TAC [POW_DEF],
   ALL_TAC] THEN
  CONJ_TAC THENL
  [SIMP_TAC std_ss [dynkin, IN_BIGINTER, GSPECIFICATION] THEN
   RW_TAC std_ss [SUBSET_DEF, dynkin_system],
   ALL_TAC] THEN
  CONJ_TAC THENL
  [RW_TAC std_ss [dynkin, IN_BIGINTER, GSPECIFICATION] THEN
   FULL_SIMP_TAC std_ss [dynkin_system],
   ALL_TAC] THEN
  RW_TAC std_ss [dynkin, GSPECIFICATION, IN_BIGINTER] THEN
  FULL_SIMP_TAC std_ss [SUBSET_DEF, GSPECIFICATION, IN_BIGINTER] THEN

  FULL_SIMP_TAC std_ss [dynkin_system] THEN
  POP_ASSUM (fn th => FIRST_ASSUM (MP_TAC o Q.SPEC `A`) THEN ASSUME_TAC th) THEN
  SIMP_TAC std_ss [AND_IMP_INTRO] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_SIMP_TAC std_ss [SUBSET_DEF]);

val restricted_dynkin_system = store_thm ("restricted_dynkin_system",
  ``!sp st D. dynkin_system sp st /\  D IN st ==>
       dynkin_system sp {Q | Q SUBSET sp /\ Q INTER D IN st}``,
  RW_TAC std_ss [] THEN MATCH_MP_TAC dynkin_systemI THEN
  SIMP_TAC std_ss [GSPECIFICATION, SUBSET_REFL] THEN
  CONJ_TAC THENL
  [FULL_SIMP_TAC std_ss [dynkin_system, subset_class_def] THEN
   `D SUBSET sp` by METIS_TAC [] THEN
   `sp INTER D = D` by ASM_SET_TAC [] THEN
   ASM_SIMP_TAC std_ss [], ALL_TAC] THEN
  CONJ_TAC THENL
  [FULL_SIMP_TAC std_ss [dynkin_system, subset_class_def] THEN
   RW_TAC std_ss [] THENL [ASM_SET_TAC [], ALL_TAC] THEN
   ONCE_REWRITE_TAC [SET_RULE
    ``(sp DIFF A) INTER D = sp DIFF ((sp DIFF D) UNION (A INTER D))``] THEN
   FIRST_ASSUM MATCH_MP_TAC THEN
   FIRST_X_ASSUM (MP_TAC o Q.SPEC `(\i. if i = 0 then sp DIFF D else
                                        if i = 1 then A INTER D else {})`) THEN
   Q_TAC SUFF_TAC `disjoint_family
    (\i:num. if i = 0 then sp DIFF D else if i = 1 then A INTER D else {})` THENL
   [DISCH_TAC THEN ASM_SIMP_TAC std_ss [],
    SIMP_TAC std_ss [disjoint_family, disjoint_family_on, IN_UNIV] THEN
    RW_TAC std_ss [] THEN ASM_SET_TAC []] THEN
   Q_TAC SUFF_TAC `IMAGE
    (\i. if i = 0 then sp DIFF D else if i = 1 then A INTER D else {})
    univ(:num) SUBSET st` THENL
   [DISCH_TAC THEN ASM_SIMP_TAC std_ss [],
    SIMP_TAC std_ss [SUBSET_DEF, IN_IMAGE, IN_UNIV] THEN RW_TAC std_ss [] THEN
    REPEAT (COND_CASES_TAC) THEN ASM_SIMP_TAC std_ss [] THEN
    FIRST_X_ASSUM (MP_TAC o Q.SPEC `sp`) THEN
    ASM_SIMP_TAC std_ss [DIFF_EQ_EMPTY]] THEN
   MATCH_MP_TAC EQ_IMPLIES THEN AP_THM_TAC THEN AP_TERM_TAC THEN
   SIMP_TAC std_ss [EXTENSION, IN_BIGUNION, GSPECIFICATION, IN_IMAGE, IN_UNIV] THEN
   SIMP_TAC std_ss [IN_UNION, IN_DIFF, IN_INTER] THEN GEN_TAC THEN
   EQ_TAC THEN RW_TAC std_ss [] THEN TRY (ASM_SET_TAC []) THENL
   [Q.EXISTS_TAC `sp DIFF D` THEN ASM_SIMP_TAC std_ss [IN_DIFF] THEN
    Q.EXISTS_TAC `0` THEN ASM_SET_TAC [], ALL_TAC] THEN
   Q.EXISTS_TAC `A INTER D` THEN ASM_SIMP_TAC std_ss [IN_INTER] THEN
   Q.EXISTS_TAC `1` THEN ASM_SIMP_TAC arith_ss [IN_INTER],
   ALL_TAC] THEN
  GEN_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
  Q_TAC SUFF_TAC `!i. A i SUBSET sp` THENL
  [DISCH_TAC,
   FULL_SIMP_TAC std_ss [dynkin_system, subset_class_def] THEN
   GEN_TAC THEN POP_ASSUM MP_TAC THEN
   SIMP_TAC std_ss [SUBSET_DEF, GSPECIFICATION] THEN
   SIMP_TAC std_ss [GSYM SUBSET_DEF] THEN
   DISCH_THEN (MP_TAC o Q.SPEC `A (i:num)`) THEN
   SET_TAC []] THEN
  Q_TAC SUFF_TAC `disjoint_family (\i. A i INTER D)` THENL
  [DISCH_TAC,
   FULL_SIMP_TAC std_ss [dynkin_system, subset_class_def] THEN
   FULL_SIMP_TAC std_ss [disjoint_family, disjoint_family_on, IN_UNIV] THEN
   ASM_SET_TAC []] THEN
  `IMAGE (\i. A i INTER D) UNIV SUBSET st` by ASM_SET_TAC [] THEN
  Q_TAC SUFF_TAC `BIGUNION (IMAGE A univ(:num)) INTER D =
                  BIGUNION (IMAGE (\i. A i INTER D) univ(:num))` THENL
  [DISCH_TAC,
   SIMP_TAC std_ss [EXTENSION, IN_BIGUNION, GSPECIFICATION, IN_INTER] THEN
   SIMP_TAC std_ss [IN_INTER, IN_IMAGE, IN_UNIV] THEN GEN_TAC THEN EQ_TAC THEN
   RW_TAC std_ss [] THENL
   [Q.EXISTS_TAC `A x' INTER D` THEN ASM_SET_TAC [],
    Q.EXISTS_TAC `A i` THEN ASM_SET_TAC [],
    ALL_TAC] THEN
   ASM_SET_TAC []] THEN
  FULL_SIMP_TAC std_ss [dynkin_system] THEN
  ASM_SET_TAC []);

val dynkin_subset = store_thm ("dynkin_subset",
  ``!sp N M. N SUBSET M /\ dynkin_system sp M ==> dynkin sp N SUBSET M``,
  RW_TAC std_ss [dynkin] THEN
  FULL_SIMP_TAC std_ss [SUBSET_DEF, IN_BIGINTER, GSPECIFICATION]);

val sigma_eq_dynkin = store_thm ("sigma_eq_dynkin",
  ``!sp M. M SUBSET POW sp /\ Int_stable M ==>
             (subsets (sigma sp M) = dynkin sp M)``,
  RW_TAC std_ss [] THEN
  Q_TAC SUFF_TAC `dynkin sp M SUBSET subsets (sigma sp M)` THENL
  [DISCH_TAC,
   SIMP_TAC std_ss [dynkin, SUBSET_DEF, IN_BIGINTER, GSPECIFICATION] THEN
   RW_TAC std_ss [] THEN POP_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC sigma_algebra_imp_dynkin_system THEN
    SIMP_TAC std_ss [sigma_def, subsets_def] THEN
    SIMP_TAC std_ss [GSYM sigma_def] THEN MATCH_MP_TAC SIGMA_ALGEBRA_SIGMA THEN
    ASM_SET_TAC [POW_DEF, subset_class_def],
    ALL_TAC] THEN
   SIMP_TAC std_ss [IN_SIGMA]] THEN
  `dynkin_system sp (dynkin sp M)` by METIS_TAC [dynkin_system_dynkin] THEN
  Q_TAC SUFF_TAC `sigma_algebra (sp, dynkin sp M)` THENL
  [DISCH_TAC,
   ASM_SIMP_TAC std_ss [sigma_algebra_eq_Int_stable, Int_stable] THEN
   RW_TAC std_ss [] THEN
   Q.ABBREV_TAC `D = (\E. {Q | Q SUBSET sp /\ Q INTER E IN dynkin sp M})` THEN
   Q_TAC SUFF_TAC `M SUBSET D b` THENL
   [DISCH_TAC,
    RW_TAC std_ss [SUBSET_DEF] THEN
    Q_TAC SUFF_TAC `x IN dynkin sp M` THENL
    [DISCH_TAC,
     SIMP_TAC std_ss [dynkin, IN_BIGINTER, GSPECIFICATION] THEN
     RW_TAC std_ss [SUBSET_DEF]] THEN
    Q_TAC SUFF_TAC `dynkin sp M SUBSET D x` THENL
    [DISCH_TAC,
     MATCH_MP_TAC dynkin_subset THEN Q.UNABBREV_TAC `D` THEN
     RW_TAC std_ss [] THENL
     [ALL_TAC,
      MATCH_MP_TAC restricted_dynkin_system THEN
      ASM_SIMP_TAC std_ss []] THEN
     RW_TAC std_ss [SUBSET_DEF, GSPECIFICATION] THENL
     [ASM_SET_TAC [POW_DEF], ALL_TAC] THEN
     SIMP_TAC std_ss [dynkin, IN_BIGINTER, GSPECIFICATION] THEN
     RW_TAC std_ss [SUBSET_DEF] THEN FIRST_ASSUM MATCH_MP_TAC THEN
     FULL_SIMP_TAC std_ss [Int_stable]] THEN
    `b IN D x` by ASM_SET_TAC [] THEN
    Q.UNABBREV_TAC `D` THEN SIMP_TAC std_ss [GSPECIFICATION] THEN
    CONJ_TAC THENL [ASM_SET_TAC [POW_DEF], ALL_TAC] THEN
    FULL_SIMP_TAC std_ss [GSPECIFICATION] THEN METIS_TAC [INTER_COMM]] THEN
   Q_TAC SUFF_TAC `dynkin sp M SUBSET D b` THENL
   [DISCH_TAC,
    MATCH_MP_TAC dynkin_subset THEN Q.UNABBREV_TAC `D` THEN
    RW_TAC std_ss [] THEN MATCH_MP_TAC restricted_dynkin_system THEN
    ASM_SIMP_TAC std_ss []] THEN
   POP_ASSUM MP_TAC THEN Q.UNABBREV_TAC `D` THEN
   ASM_SIMP_TAC std_ss [GSPECIFICATION, SUBSET_DEF]] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_SIMP_TAC std_ss [] THEN
  Q_TAC SUFF_TAC `subsets (sigma (space (sp, dynkin sp M)) M) SUBSET
                  subsets (sp, dynkin sp M)` THENL
  [METIS_TAC [subsets_def, space_def], ALL_TAC] THEN
  MATCH_MP_TAC SIGMA_SUBSET THEN ASM_SIMP_TAC std_ss [subsets_def] THEN
  SET_TAC [dynkin]);

val dynkin_lemma = store_thm ("dynkin_lemma",
  ``!sp E M. Int_stable E /\ E SUBSET M /\
             M SUBSET subsets (sigma sp E) /\ dynkin_system sp M ==>
             (subsets (sigma sp E) = M)``,
  RW_TAC std_ss [] THEN
  `E SUBSET POW sp` by ASM_SET_TAC [POW_DEF, dynkin_system, subset_class_def] THEN
  `subsets (sigma sp E) = dynkin sp E` by METIS_TAC [sigma_eq_dynkin] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_SIMP_TAC std_ss [] THEN
  MATCH_MP_TAC dynkin_subset THEN ASM_SIMP_TAC std_ss []);

val sigma_sets_induct_disjoint = store_thm ("sigma_sets_induct_disjoint",
  ``!G A P sp.
    Int_stable G /\ G SUBSET POW sp /\ A IN subsets (sigma sp G) /\
    (!A. A IN G ==> P A) /\ P {} /\
    (!A. A IN subsets (sigma sp G) ==> P A ==> P (sp DIFF A)) /\
    (!A. disjoint_family A ==> IMAGE A UNIV SUBSET subsets (sigma sp G)
         ==> (!i. P (A i)) ==> P (BIGUNION (IMAGE A univ(:num)))) ==>
    P A``,
  RW_TAC std_ss [] THEN
  Q.ABBREV_TAC `dd = {A | A IN subsets (sigma sp G) /\ P A}` THEN
  Q_TAC SUFF_TAC `sigma_algebra (sigma sp G)` THENL
  [DISCH_TAC,
   MATCH_MP_TAC SIGMA_ALGEBRA_SIGMA THEN
   FULL_SIMP_TAC std_ss [subset_class_def, POW_DEF] THEN
   ASM_SET_TAC []] THEN
  Q_TAC SUFF_TAC `P (sp DIFF {})` THENL
  [RW_TAC std_ss [DIFF_EMPTY],
   FULL_SIMP_TAC std_ss [AND_IMP_INTRO] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   FULL_SIMP_TAC std_ss [sigma_algebra_def, algebra_def]] THEN
  Q_TAC SUFF_TAC `dynkin_system sp dd` THENL
  [DISCH_TAC,
   MATCH_MP_TAC dynkin_systemI THEN Q.UNABBREV_TAC `dd` THEN
   ASM_SIMP_TAC std_ss [GSPECIFICATION] THEN RW_TAC std_ss [] THENL
   [ASM_SET_TAC [SIGMA_ALGEBRA, SPACE_SIGMA, subset_class_def],
    Q_TAC SUFF_TAC `space (sigma sp G) IN subsets (sigma sp G)` THENL
    [METIS_TAC [SPACE_SIGMA], ALL_TAC] THEN
    MATCH_MP_TAC ALGEBRA_SPACE THEN METIS_TAC [sigma_algebra_def],
    MATCH_MP_TAC ALGEBRA_DIFF THEN
    FULL_SIMP_TAC std_ss [sigma_algebra_def] THEN
    Q_TAC SUFF_TAC `space (sigma sp G) IN subsets (sigma sp G)` THENL
    [METIS_TAC [SPACE_SIGMA], ALL_TAC] THEN
    MATCH_MP_TAC ALGEBRA_SPACE THEN METIS_TAC [sigma_algebra_def],
    FULL_SIMP_TAC std_ss [sigma_algebra_def] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    CONJ_TAC THENL [ALL_TAC, ASM_SET_TAC []] THEN
    METIS_TAC [image_countable, COUNTABLE_NUM],
    ALL_TAC] THEN
   ASM_SET_TAC []] THEN
  Q_TAC SUFF_TAC `subsets (sigma sp G) = dd` THENL
  [DISCH_TAC,
   MATCH_MP_TAC dynkin_lemma THEN ASM_SIMP_TAC std_ss [] THEN
   CONJ_TAC THENL [ALL_TAC, ASM_SET_TAC []] THEN
   Q.UNABBREV_TAC `dd` THEN RW_TAC std_ss [GSPECIFICATION, SUBSET_DEF] THEN
   ASM_SIMP_TAC std_ss [IN_SIGMA]] THEN
  ASM_SET_TAC []);

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* ------------------------------------------------------------------------- *)

val borel = new_definition ("borel",
  ``borel = sigma UNIV {s| open s}``);

val borel_measurable = new_definition ("borel_measurable",
  ``borel_measurable M = measurable M borel``);

val sigma_algebra_borel = store_thm ("sigma_algebra_borel",
  ``sigma_algebra borel``,
  SIMP_TAC std_ss [borel] THEN MATCH_MP_TAC SIGMA_ALGEBRA_SIGMA THEN
  SIMP_TAC std_ss [subset_class_def, SUBSET_UNIV]);

val in_borel_measurable = store_thm ("in_borel_measurable",
  ``!f M. f IN borel_measurable M =
          (sigma_algebra M) /\
          (!s. s IN subsets (sigma UNIV {s | open s}) ==>
           (PREIMAGE f s) INTER (space M) IN subsets M)``,
  REPEAT GEN_TAC THEN RW_TAC std_ss [borel_measurable, measurable_def] THEN
  SIMP_TAC std_ss [GSPECIFICATION] THEN EQ_TAC THEN REPEAT STRIP_TAC THEN
  FULL_SIMP_TAC std_ss [] THENL
  [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC std_ss [borel],
   SIMP_TAC std_ss [sigma_algebra_borel],
   EVAL_TAC THEN SIMP_TAC std_ss [borel, sigma_def, space_def] THEN
   SIMP_TAC std_ss [IN_UNIV] THEN SIMP_TAC std_ss [IN_DEF] THEN rw[IN_FUNSET],
   FIRST_X_ASSUM MATCH_MP_TAC THEN POP_ASSUM MP_TAC THEN
   SIMP_TAC std_ss [borel, sigma_def, subsets_def, IN_BIGINTER] THEN
   SIMP_TAC std_ss [GSPECIFICATION] THEN REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC [SUBSET_DEF, sigma_sets_basic] THEN
   MATCH_MP_TAC sigma_algebra_sigma_sets THEN REWRITE_TAC [POW_DEF] THEN
   SET_TAC []]);

val in_borel_measurable_borel = store_thm ("in_borel_measurable_borel",
  ``!f M. f IN borel_measurable M =
        (sigma_algebra M) /\
        (!s. s IN subsets borel ==> (PREIMAGE f s) INTER (space M) IN subsets M)``,
  SIMP_TAC std_ss [in_borel_measurable, borel]);

val space_borel = store_thm ("space_borel",
  ``space borel = UNIV``,
  SIMP_TAC std_ss [borel, sigma_def, space_def]);

val space_in_borel = store_thm ("space_in_borel",
  ``UNIV IN subsets borel``,
  SIMP_TAC std_ss [borel, sigma_def, subsets_def] THEN
  SIMP_TAC std_ss [IN_BIGINTER, GSPECIFICATION, SUBSET_DEF] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  SIMP_TAC std_ss [OPEN_UNIV]);

val borel_open = store_thm ("borel_open",
  ``!A. real_topology$Open A ==> A IN subsets borel``,
  SIMP_TAC std_ss [borel, sigma_def, subsets_def] THEN
  SIMP_TAC std_ss [IN_BIGINTER, GSPECIFICATION, SUBSET_DEF]);

val borel_closed = store_thm ("borel_closed",
  ``!A. closed A ==> A IN subsets borel``,
  GEN_TAC THEN REWRITE_TAC [closed_def] THEN
  DISCH_THEN (ASSUME_TAC o MATCH_MP borel_open) THEN
  FULL_SIMP_TAC std_ss [borel, sigma_def, subsets_def] THEN
  FULL_SIMP_TAC std_ss [IN_BIGINTER, GSPECIFICATION, SUBSET_DEF] THEN
  GEN_TAC THEN FIRST_X_ASSUM (MP_TAC o SPEC ``P:(real->bool)->bool``) THEN
  REPEAT STRIP_TAC THEN FULL_SIMP_TAC std_ss [sigma_algebra_def, algebra_def] THEN
  FULL_SIMP_TAC std_ss [subsets_def, space_def] THEN POP_ASSUM K_TAC THEN
  POP_ASSUM K_TAC THEN FIRST_X_ASSUM (MP_TAC o SPEC ``univ(:real) DIFF A``) THEN
  ASM_SIMP_TAC std_ss [SET_RULE ``UNIV DIFF (UNIV DIFF A) = A``]);

val borel_singleton = store_thm ("borel_singleton",
  ``!A x. A IN subsets borel ==> x INSERT A IN subsets borel``,
  REPEAT GEN_TAC THEN ASSUME_TAC borel_closed THEN
  FULL_SIMP_TAC std_ss [borel, sigma_def, subsets_def] THEN
  FULL_SIMP_TAC std_ss [IN_BIGINTER, GSPECIFICATION, SUBSET_DEF] THEN
  REPEAT STRIP_TAC THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
  FIRST_X_ASSUM (MP_TAC o SPEC ``P:(real->bool)->bool``) THEN
  FIRST_X_ASSUM (MP_TAC o SPEC ``{x}:real->bool``) THEN
  SIMP_TAC std_ss [CLOSED_SING] THEN DISCH_TAC THEN
  FIRST_X_ASSUM (MP_TAC o SPEC ``P:(real->bool)->bool``) THEN
  REPEAT STRIP_TAC THEN FULL_SIMP_TAC std_ss [] THEN
  FULL_SIMP_TAC std_ss [sigma_algebra_def, algebra_def, subsets_def] THEN
  REWRITE_TAC [INSERT_DEF] THEN SIMP_TAC std_ss [GSYM IN_SING, GSYM UNION_DEF] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN METIS_TAC []);

val borel_comp = store_thm ("borel_comp",
 ``!A. A IN subsets borel ==> (UNIV DIFF A) IN subsets borel``,
  REPEAT GEN_TAC THEN
  FULL_SIMP_TAC std_ss [borel, sigma_def, subsets_def] THEN
  FULL_SIMP_TAC std_ss [IN_BIGINTER, GSPECIFICATION, SUBSET_DEF] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o SPEC ``P:(real->bool)->bool``) THEN
FULL_SIMP_TAC std_ss [sigma_algebra_def, algebra_def, subsets_def, space_def]);

val borel_measurable_image = store_thm ("borel_measurable_image",
  ``!f M x. f IN borel_measurable M ==>
            (PREIMAGE f {x}) INTER space M IN subsets M``,
  REPEAT GEN_TAC THEN SIMP_TAC std_ss [borel_measurable, measurable_def] THEN
  SIMP_TAC std_ss [GSPECIFICATION] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC borel_closed THEN
  SIMP_TAC std_ss [CLOSED_SING]);

val measurable_measure_of = store_thm ("measurable_measure",
  ``!M sp N f. measure_space M /\
     N SUBSET POW sp /\ f IN (m_space M -> sp) /\
     (!y. y IN N ==> (PREIMAGE f y) INTER m_space M IN measurable_sets M) ==>
     f IN measurable (m_space M, measurable_sets M) (sigma sp N)``,
  RW_TAC std_ss [] THEN MATCH_MP_TAC MEASURABLE_SIGMA THEN
  FULL_SIMP_TAC std_ss [measure_space_def, subset_class_def] THEN
  CONJ_TAC THENL [ASM_SET_TAC [POW_DEF], ALL_TAC] THEN
  RW_TAC std_ss [] THENL
  [SIMP_TAC std_ss [space_def, sigma_def] THEN
   POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN EVAL_TAC THEN METIS_TAC [],
   ALL_TAC] THEN
  FULL_SIMP_TAC std_ss [space_def, subsets_def]);

val borel_measurableI = store_thm ("borel_measurableI",
  ``!M f. (!s. real_topology$Open s ==>
           (PREIMAGE f s) INTER m_space M IN measurable_sets M) /\
          measure_space M ==>
           f IN measurable (m_space M, measurable_sets M) borel``,
  RW_TAC std_ss [borel] THEN MATCH_MP_TAC measurable_measure_of THEN
  ASM_SIMP_TAC std_ss [] THEN CONJ_TAC THENL [SET_TAC [POW_DEF], ALL_TAC] THEN
  CONJ_TAC THENL [EVAL_TAC THEN SET_TAC [], ALL_TAC] THEN
  ASM_SET_TAC []);

val borel_measurable_const = store_thm ("borel_measurable_const",
  ``!M c. sigma_algebra M ==> (\x. c) IN borel_measurable M``,
  REPEAT STRIP_TAC THEN SIMP_TAC std_ss [borel_measurable, measurable_def] THEN
  SIMP_TAC std_ss [GSPECIFICATION] THEN ASM_REWRITE_TAC [sigma_algebra_borel] THEN
  CONJ_TAC THENL [EVAL_TAC THEN SIMP_TAC std_ss [space_borel, IN_UNIV] THEN
   SIMP_TAC std_ss[IN_DEF], ALL_TAC] THEN
  SIMP_TAC std_ss [borel, sigma_def, subsets_def] THEN
  SIMP_TAC std_ss [IN_BIGINTER, SUBSET_DEF, GSPECIFICATION] THEN
  REPEAT STRIP_TAC THEN
  simp[PREIMAGE_def, INTER_DEF, GSPECIFICATION,IN_FUNSET] THEN
  ASM_CASES_TAC ``(c:real) IN s`` THENL
  [ASM_SIMP_TAC std_ss [SET_RULE ``{x | x IN s} = s``] THEN
   MATCH_MP_TAC ALGEBRA_SPACE THEN FULL_SIMP_TAC std_ss [sigma_algebra_def],
   ALL_TAC] THEN
  ASM_SIMP_TAC std_ss [GSPEC_F] THEN MATCH_MP_TAC ALGEBRA_EMPTY THEN
  FULL_SIMP_TAC std_ss [sigma_algebra_def]);

val borel_measurable_indicator = store_thm ("borel_measurable_indicator",
  ``!A M. A IN measurable_sets M /\ measure_space M ==>
          indicator A IN borel_measurable (m_space M, measurable_sets M)``,
  RW_TAC std_ss [borel_measurable, indicator] THEN
  KNOW_TAC ``borel = (m_space (space borel, subsets borel, (\x. 0)),
              measurable_sets (space borel, subsets borel, (\x. 0)))`` THENL
  [SIMP_TAC std_ss [m_space_def, measurable_sets_def, SPACE],
   DISC_RW_KILL] THEN
  ONCE_REWRITE_TAC [METIS [] ``(\x. if x IN (A:real->bool) then 1:real else 0) =
                               (\x. if x IN A then (\x. 1) x else (\x. 0) x)``] THEN
  MATCH_MP_TAC measurable_If_set THEN
  SIMP_TAC std_ss [IN_MEASURABLE, m_space_def, measurable_sets_def] THEN
  SIMP_TAC std_ss [space_def, subsets_def] THEN
  FIRST_ASSUM (ASSUME_TAC o MATCH_MP MEASURE_SPACE_MSPACE_MEASURABLE) THEN
  FULL_SIMP_TAC std_ss [measure_space_def, sigma_algebra_borel, SPACE] THEN
  RW_TAC std_ss [IN_FUNSET, space_borel, IN_UNIV, PREIMAGE_def] THEN
  ONCE_REWRITE_TAC
  [SET_RULE ``({x | x | (1:real) IN s} = if 1 IN s then UNIV else {}) /\
              ({x | x | (0:real) IN s} = if 0 IN s then UNIV else {})``] THENL
  [COND_CASES_TAC THEN ASM_SIMP_TAC std_ss [INTER_UNIV, INTER_EMPTY] THEN
   FULL_SIMP_TAC std_ss [sigma_algebra_iff2],
   COND_CASES_TAC THEN ASM_SIMP_TAC std_ss [INTER_UNIV, INTER_EMPTY] THEN
   FULL_SIMP_TAC std_ss [sigma_algebra_iff2],
   FULL_SIMP_TAC std_ss [sigma_algebra_def] THEN
   ONCE_REWRITE_TAC [METIS [subsets_def] ``measurable_sets M =
     subsets (m_space M, measurable_sets M)``] THEN
   MATCH_MP_TAC ALGEBRA_INTER THEN ASM_SIMP_TAC std_ss [subsets_def]]);

val borel_sigma_sets_subset = store_thm ("borel_sigma_sets_subset",
  ``!A. A SUBSET subsets borel ==> (sigma_sets UNIV A) SUBSET subsets borel``,
  RW_TAC std_ss [] THEN MATCH_MP_TAC sigma_sets_subset THEN
  ASM_SIMP_TAC std_ss [GSYM space_borel, SPACE, sigma_algebra_borel]);

val borel_eq_sigmaI1 = store_thm ("borel_eq_sigmaI1",
  ``!X A f. (borel = sigma UNIV X) /\
     (!x. x IN X ==> x IN subsets (sigma UNIV (IMAGE f A))) /\
     (!i. i IN A ==> f i IN subsets borel) ==>
     (borel = sigma UNIV (IMAGE f A))``,
  RW_TAC std_ss [borel] THEN SIMP_TAC std_ss [sigma_def] THEN
  FULL_SIMP_TAC std_ss [sigma_def, subsets_def, GSYM SUBSET_DEF] THEN
  SIMP_TAC std_ss [EXTENSION, IN_BIGINTER, GSPECIFICATION] THEN
  GEN_TAC THEN FULL_SIMP_TAC std_ss [GSPECIFICATION] THEN
  EQ_TAC THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_SET_TAC []);

val borel_eq_sigmaI2 = store_thm ("borel_eq_sigmaI2",
  ``!G f A B. (borel = sigma UNIV (IMAGE (\(i,j). G i j) B)) /\
            (!i j. (i,j) IN B ==>
                   G i j IN subsets (sigma UNIV (IMAGE (\(i,j). f i j) A))) /\
            (!i j. (i,j) IN A ==> f i j IN subsets borel) ==>
            (borel = sigma UNIV (IMAGE (\(i,j). f i j) A))``,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC borel_eq_sigmaI1 THEN
  EXISTS_TAC ``(IMAGE (\(i,j). (G:'a->'b->real->bool) i j) B)`` THEN
  FULL_SIMP_TAC std_ss [sigma_def, subsets_def, borel] THEN
  FULL_SIMP_TAC std_ss [IN_BIGINTER, GSPECIFICATION] THEN
  CONJ_TAC THENL
  [RW_TAC std_ss [IN_IMAGE] THEN MP_TAC (ISPEC ``x':'a#'b`` ABS_PAIR_THM) THEN
   STRIP_TAC THEN FULL_SIMP_TAC std_ss [], ALL_TAC] THEN
  RW_TAC std_ss [] THEN MP_TAC (ISPEC ``i:'c#'d`` ABS_PAIR_THM) THEN
  STRIP_TAC THEN FULL_SIMP_TAC std_ss [] THEN ASM_SET_TAC []);

val borel_eq_sigmaI3 = store_thm ("borel_eq_sigmaI3",
  ``!f A X. (borel = sigma UNIV X) /\
          (!x. x IN X ==> x IN subsets (sigma UNIV (IMAGE (\(i,j). f i j) A))) /\
          (!i j. (i,j) IN A ==> f i j IN subsets borel) ==>
          (borel = sigma UNIV (IMAGE (\(i,j). f i j) A))``,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC borel_eq_sigmaI1 THEN
  EXISTS_TAC ``X:(real->bool)->bool`` THEN
  FULL_SIMP_TAC std_ss [sigma_def, subsets_def, borel] THEN
  FULL_SIMP_TAC std_ss [IN_BIGINTER, GSPECIFICATION] THEN
  RW_TAC std_ss [] THEN MP_TAC (ISPEC ``i:'a#'b`` ABS_PAIR_THM) THEN
   STRIP_TAC THEN FULL_SIMP_TAC std_ss [] THEN ASM_SET_TAC []);

val borel_eq_sigmaI4 = store_thm ("borel_eq_sigmaI4",
  ``!G f A. (borel = sigma UNIV (IMAGE (\(i,j). G i j) A)) /\
            (!i j. (i,j) IN A ==>
                   G i j IN subsets (sigma UNIV (IMAGE f UNIV))) /\
            (!i. f i IN subsets borel) ==>
            (borel = sigma UNIV (IMAGE f UNIV))``,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC borel_eq_sigmaI1 THEN
  EXISTS_TAC ``(IMAGE (\(i,j). (G:'a->'b->real->bool) i j) A)`` THEN
  FULL_SIMP_TAC std_ss [sigma_def, subsets_def, borel] THEN
  FULL_SIMP_TAC std_ss [IN_BIGINTER, GSPECIFICATION] THEN
  CONJ_TAC THENL
  [RW_TAC std_ss [IN_IMAGE] THEN MP_TAC (ISPEC ``x':'a#'b`` ABS_PAIR_THM) THEN
   STRIP_TAC THEN FULL_SIMP_TAC std_ss [], ALL_TAC] THEN
  RW_TAC std_ss [IN_UNIV] THEN ASM_SET_TAC []);

val borel_eq_sigmaI5 = store_thm ("borel_eq_sigmaI5",
  ``!G f. (borel = sigma UNIV (IMAGE G UNIV)) /\
          (!i. G i IN subsets (sigma UNIV (IMAGE (\(i,j). f i j) UNIV))) /\
          (!i j. f i j IN subsets borel) ==>
          (borel = sigma UNIV (IMAGE (\(i,j). f i j) UNIV))``,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC borel_eq_sigmaI1 THEN
  EXISTS_TAC ``(IMAGE (G:'a->real->bool) UNIV)`` THEN
  FULL_SIMP_TAC std_ss [sigma_def, subsets_def, borel] THEN
  FULL_SIMP_TAC std_ss [IN_BIGINTER, GSPECIFICATION] THEN
  CONJ_TAC THENL
  [RW_TAC std_ss [IN_IMAGE] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
   ASM_SIMP_TAC std_ss [], ALL_TAC] THEN
  RW_TAC std_ss [IN_UNIV] THEN
  MP_TAC (ISPEC ``i:'b#'c`` ABS_PAIR_THM) THEN STRIP_TAC THEN
  ASM_SIMP_TAC std_ss [] THEN ASM_SET_TAC []);

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* ------------------------------------------------------------------------- *)

(* Q_set (extrealTheory) *)
val Qset_def = new_definition ("Qset_def",
  ``Qset = {x:real | ?a b. (x = (&a/(&b))) /\ (0:real < &b)} UNION
           {x:real | ?a b. (x = -(&a/(&b))) /\ (0:real < &b)}``);

val QSET_COUNTABLE = store_thm ("QSET_COUNTABLE",
  ``countable Qset``,
  RW_TAC std_ss [Qset_def] THEN
  MATCH_MP_TAC union_countable THEN CONJ_TAC THENL
  [RW_TAC std_ss [pred_setTheory.COUNTABLE_ALT] THEN
   MP_TAC NUM_2D_BIJ_NZ_INV THEN RW_TAC std_ss [] THEN
   Q.EXISTS_TAC `(\(a,b). &a/(&b)) o f` THEN RW_TAC std_ss [GSPECIFICATION] THEN
   FULL_SIMP_TAC std_ss [BIJ_DEF,INJ_DEF,SURJ_DEF,IN_UNIV] THEN
   PAT_X_ASSUM ``!x. x IN P ==> Q x y`` (MP_TAC o Q.SPEC `(&a,&b)`) THEN
   RW_TAC std_ss [] THEN
   FULL_SIMP_TAC real_ss [IN_CROSS,IN_UNIV,IN_SING,DIFF_DEF,
                          GSPECIFICATION,GSYM REAL_LT_NZ] THEN
   `?y. f y = (a,b)` by METIS_TAC [] THEN
   Q.EXISTS_TAC `y` THEN RW_TAC real_ss [], ALL_TAC] THEN
  RW_TAC std_ss [pred_setTheory.COUNTABLE_ALT] THEN
  MP_TAC NUM_2D_BIJ_NZ_INV THEN
  RW_TAC std_ss [] THEN Q.EXISTS_TAC `(\(a,b). -(&a/(&b))) o f` THEN
  RW_TAC std_ss [GSPECIFICATION] THEN
  FULL_SIMP_TAC std_ss [BIJ_DEF,INJ_DEF,SURJ_DEF,IN_UNIV] THEN
  PAT_X_ASSUM ``!x. x IN P ==> Q x y`` (MP_TAC o Q.SPEC `(&a,&b)`) THEN
  RW_TAC std_ss [] THEN
  FULL_SIMP_TAC real_ss [IN_CROSS,IN_UNIV,IN_SING,
                         DIFF_DEF,GSPECIFICATION,GSYM REAL_LT_NZ] THEN
  `?y. f y = (a,b)` by METIS_TAC [] THEN Q.EXISTS_TAC `y` THEN
  RW_TAC real_ss []);

val NUM_IN_QSET = store_thm ("NUM_IN_QSET",
  ``!n. &n IN Qset /\ -&n IN Qset``,
  FULL_SIMP_TAC std_ss [Qset_def, IN_UNION, GSPECIFICATION] THEN
  RW_TAC std_ss [] THENL
  [DISJ1_TAC THEN EXISTS_TAC ``n:num`` THEN EXISTS_TAC ``1:num`` THEN
   SIMP_TAC real_ss [],
   DISJ2_TAC THEN EXISTS_TAC ``n:num`` THEN EXISTS_TAC ``1:num`` THEN
   SIMP_TAC real_ss []]);

val OPP_IN_QSET = store_thm ("OPP_IN_QSET",
  ``!x. x IN Qset ==> -x IN Qset``,
  RW_TAC std_ss [Qset_def,EXTENSION,GSPECIFICATION,IN_UNION] THENL
  [DISJ2_TAC THEN Q.EXISTS_TAC `a` THEN Q.EXISTS_TAC `b` THEN
   RW_TAC real_ss [], ALL_TAC] THEN
  DISJ1_TAC THEN Q.EXISTS_TAC `a` THEN Q.EXISTS_TAC `b` THEN
  RW_TAC real_ss [neg_neg]);

val INV_IN_QSET = store_thm ("INV_IN_QSET",
  ``!x. (x IN Qset) /\ (x <> 0) ==> 1/x IN Qset``,
  RW_TAC std_ss [Qset_def,EXTENSION,GSPECIFICATION,IN_UNION] THENL
  [Cases_on `0:real < &a` THENL
   [DISJ1_TAC THEN
    `(&a <> 0:real) /\ (&b <> 0:real)` by FULL_SIMP_TAC real_ss [REAL_POS_NZ,GSYM REAL_LT_NZ] THEN
    Q.EXISTS_TAC `b` THEN Q.EXISTS_TAC `a` THEN FULL_SIMP_TAC std_ss [] THEN
  `1:real / (&a / &b) = (1 / 1) / (&a / &b)` by RW_TAC real_ss [] THEN
    ASM_SIMP_TAC std_ss [] THEN RW_TAC real_ss [div_rat], ALL_TAC] THEN
    DISJ2_TAC THEN
    `&b <> 0:real` by METIS_TAC [REAL_LT_IMP_NE] THEN
    FULL_SIMP_TAC std_ss [] THEN
    `&a <> 0:real` by METIS_TAC [real_div,REAL_ENTIRE] THEN
    FULL_SIMP_TAC real_ss [], ALL_TAC] THEN
  Cases_on `0:real < &a` THENL
  [DISJ2_TAC THEN
   `(&a <> 0:real) /\ (&b <> 0:real)` by
    FULL_SIMP_TAC real_ss [REAL_POS_NZ,GSYM REAL_LT_NZ] THEN
   `&a / &b <> 0:real` by FULL_SIMP_TAC real_ss [REAL_NEG_EQ0] THEN
   Q.EXISTS_TAC `b` THEN Q.EXISTS_TAC `a` THEN FULL_SIMP_TAC std_ss [neg_rat] THEN
   RW_TAC std_ss [real_div, REAL_INV_MUL, REAL_INV_NZ] THEN
   `inv (&b) <> 0:real` by
    FULL_SIMP_TAC real_ss [REAL_POS_NZ,REAL_INV_EQ_0,REAL_POS_NZ] THEN
   RW_TAC real_ss [GSYM REAL_NEG_INV,REAL_NEG_EQ0,REAL_EQ_NEG,REAL_ENTIRE] THEN
   RW_TAC real_ss [REAL_INV_MUL,REAL_INV_INV,REAL_MUL_COMM], ALL_TAC] THEN
  DISJ2_TAC THEN `&b <> 0:real` by METIS_TAC [REAL_LT_IMP_NE] THEN
  `&a <> 0:real` by METIS_TAC [real_div,REAL_ENTIRE,REAL_NEG_EQ0] THEN
  FULL_SIMP_TAC real_ss []);

val ADD_IN_QSET = store_thm ("ADD_IN_QSET",
  ``!x y. (x IN Qset) /\ (y IN Qset) ==> (x+y IN Qset)``,
  RW_TAC std_ss [Qset_def,EXTENSION,GSPECIFICATION,IN_UNION] THENL
  [DISJ1_TAC THEN
   `(&b <> 0:real) /\ (&b' <> 0:real)` by
    FULL_SIMP_TAC real_ss [REAL_LT_IMP_NE] THEN
   `0:real < &(b * b')` by METIS_TAC [REAL_LT_MUL,mult_ints] THEN
   `&(b * b') <> 0:real` by RW_TAC std_ss [REAL_LT_IMP_NE] THEN
   Q.EXISTS_TAC `(a*b' + a'*b)` THEN Q.EXISTS_TAC `b*b'` THEN
   RW_TAC real_ss [REAL_ADD_RAT,REAL_MUL_COMM,REAL_LT_MUL],
   `&b <> 0:real /\ &b' <> 0:real` by FULL_SIMP_TAC real_ss [REAL_LT_IMP_NE]
   THEN Cases_on `&a*(&b')-(&a'* (&b)) = 0:real` THENL
   [DISJ1_TAC THEN Q.EXISTS_TAC `0` THEN Q.EXISTS_TAC `1` THEN
    RW_TAC real_ss [REAL_DIV_LZERO, GSYM real_sub] THEN
    RW_TAC std_ss [REAL_SUB_RAT,REAL_DIV_LZERO,REAL_MUL_COMM], ALL_TAC] THEN
   Cases_on `0:real < &a * (&b') - (&a' * (&b))` THENL
   [DISJ1_TAC THEN Q.EXISTS_TAC `(a * b' - a' * b)` THEN
    Q.EXISTS_TAC `b * b'` THEN `0:real < &(b * b')` by
                               METIS_TAC [REAL_LT_MUL,mult_ints] THEN
    `&(b * b') <> 0:real` by RW_TAC std_ss [REAL_LT_IMP_NE] THEN
    RW_TAC std_ss [REAL_SUB_RAT,REAL_MUL_COMM,REAL_LT_MUL,
                   GSYM real_sub,GSYM mult_ints] THEN
    `&a' * &b < &a * (&b'):real` by FULL_SIMP_TAC real_ss [REAL_SUB_LT] THEN
    `a' * b < a * b'` by FULL_SIMP_TAC real_ss [] THEN
    `a' * b <> a * b'` by FULL_SIMP_TAC real_ss [] THEN
    FULL_SIMP_TAC real_ss [REAL_SUB],
    ALL_TAC] THEN
   DISJ2_TAC THEN Q.EXISTS_TAC `(a' * b - a * b')` THEN Q.EXISTS_TAC `b * b'` THEN
   `0:real < &(b * b')` by METIS_TAC [REAL_LT_MUL, mult_ints] THEN
   `&(b * b') <> 0:real` by RW_TAC std_ss [REAL_LT_IMP_NE] THEN
   `&a * &b' - &a' * &b < 0:real` by
    (FULL_SIMP_TAC real_ss [GSYM real_lte,REAL_LE_LT] THEN
    FULL_SIMP_TAC real_ss []) THEN
   `&a * &b' < &a' * (&b):real` by FULL_SIMP_TAC real_ss [REAL_LT_SUB_RADD] THEN
   `a' * b <> a * b'` by FULL_SIMP_TAC real_ss [] THEN
   RW_TAC std_ss [REAL_SUB_RAT,REAL_MUL_COMM,REAL_LT_MUL,GSYM real_sub] THEN
   RW_TAC std_ss [GSYM mult_ints] THEN
   FULL_SIMP_TAC real_ss [REAL_NEG_SUB,REAL_SUB,neg_rat],
   `&b <> 0:real /\ &b' <> 0:real` by
    FULL_SIMP_TAC real_ss [extreal_lt_eq,REAL_LT_IMP_NE] THEN
   `0:real < &(b * b')` by METIS_TAC [REAL_LT_MUL,mult_ints] THEN
   `&(b * b') <> 0:real` by RW_TAC std_ss [REAL_LT_IMP_NE] THEN
   Cases_on `&a * (&b')-(&a' * (&b)) = 0:real` THENL
   [DISJ1_TAC THEN Q.EXISTS_TAC `0` THEN Q.EXISTS_TAC `1` THEN
    RW_TAC real_ss [REAL_DIV_LZERO] THEN ONCE_REWRITE_TAC [GSYM REAL_NEG_EQ0] THEN
    RW_TAC std_ss [REAL_NEG_ADD,REAL_NEG_NEG] THEN
    RW_TAC std_ss [REAL_SUB_RAT,REAL_MUL_COMM,REAL_LT_MUL,
                   GSYM real_sub,REAL_DIV_LZERO,REAL_SUB_0],
    ALL_TAC] THEN
   Cases_on `0:real < &a * (&b') - (&a' * (&b))` THENL
   [DISJ2_TAC THEN Q.EXISTS_TAC `(a * b' - a' * b)` THEN Q.EXISTS_TAC `b * b'` THEN
    RW_TAC real_ss [REAL_DIV_LZERO] THEN
    RW_TAC std_ss [REAL_ADD_COMM,GSYM real_sub] THEN
    RW_TAC std_ss [REAL_SUB_RAT,REAL_MUL_COMM,REAL_LT_MUL,
                   GSYM real_sub,GSYM mult_ints] THEN
    `&a' * &b < &a * (&b'):real` by FULL_SIMP_TAC real_ss [REAL_SUB_LT] THEN
    `a' * b < a * b'` by FULL_SIMP_TAC real_ss [] THEN
    `a' * b <> a * b'` by FULL_SIMP_TAC real_ss [] THEN
    FULL_SIMP_TAC real_ss [REAL_SUB,neg_rat], ALL_TAC] THEN
   DISJ1_TAC THEN Q.EXISTS_TAC `(a' * b - a * b')` THEN Q.EXISTS_TAC `b * b'` THEN
   RW_TAC std_ss [REAL_ADD_COMM,GSYM real_sub] THEN
   `&a * &b' - &a' * &b < 0:real` by
    (FULL_SIMP_TAC real_ss [GSYM real_lte,REAL_LE_LT] THEN
    FULL_SIMP_TAC real_ss []) THEN
   `&a * &b' < &a' * (&b):real` by FULL_SIMP_TAC real_ss [REAL_LT_SUB_RADD] THEN
   `a' * b <> a * b'` by FULL_SIMP_TAC real_ss [] THEN
   RW_TAC std_ss [REAL_ADD_COMM,GSYM real_sub,REAL_SUB_RAT,
                  REAL_MUL_COMM,REAL_LT_MUL,GSYM mult_ints] THEN
   FULL_SIMP_TAC real_ss [REAL_NEG_SUB,REAL_SUB,neg_rat],
   DISJ2_TAC THEN
   `&b <> 0:real /\ &b' <> 0:real` by FULL_SIMP_TAC real_ss [REAL_LT_IMP_NE] THEN
   `0:real < &(b * b')` by METIS_TAC [extreal_lt_eq,REAL_LT_MUL,mult_ints] THEN
   `&(b * b') <> 0:real` by RW_TAC std_ss [REAL_LT_IMP_NE] THEN
   Q.EXISTS_TAC `(a * b' + a' * b)` THEN Q.EXISTS_TAC `b*b'` THEN
   REWRITE_TAC [GSYM mult_ints,GSYM add_ints] THEN
   RW_TAC std_ss [REAL_SUB_LNEG,GSYM real_sub,REAL_EQ_NEG] THEN
   RW_TAC std_ss [REAL_ADD_RAT,REAL_MUL_COMM,REAL_LT_MUL]]);

val SUB_IN_QSET = store_thm ("SUB_IN_QSET",
  ``!x y. (x IN Qset) /\ (y IN Qset) ==> (x - y IN Qset)``,
  RW_TAC std_ss [real_sub] THEN METIS_TAC [OPP_IN_QSET,ADD_IN_QSET]);

val MUL_IN_QSET = store_thm ("MUL_IN_QSET",
  ``!x y. (x IN Qset) /\ (y IN Qset) ==> (x * y IN Qset)``,
  RW_TAC std_ss [Qset_def,EXTENSION,GSPECIFICATION,IN_UNION] THENL
  [DISJ1_TAC THEN
   `&b <> 0:real /\ &b' <> 0:real` by FULL_SIMP_TAC real_ss [REAL_LT_IMP_NE] THEN
   `0:real < &(b * b')` by METIS_TAC [extreal_lt_eq,REAL_LT_MUL,mult_ints] THEN
   `&(b * b') <> 0:real` by RW_TAC std_ss [REAL_LT_IMP_NE] THEN
   Q.EXISTS_TAC `a * a'` THEN Q.EXISTS_TAC `b * b'` THEN
   FULL_SIMP_TAC real_ss [mult_rat,REAL_LT_REFL,ZERO_LESS_MULT],
   DISJ2_TAC THEN
   `&b <> 0:real /\ &b' <> 0:real` by FULL_SIMP_TAC real_ss [REAL_LT_IMP_NE] THEN
   `0:real < &(b * b')` by METIS_TAC [extreal_lt_eq,REAL_LT_MUL,mult_ints] THEN
   `&(b * b') <> 0:real` by RW_TAC std_ss [REAL_LT_IMP_NE] THEN
   Q.EXISTS_TAC `a*a'` THEN Q.EXISTS_TAC `b*b'` THEN
   FULL_SIMP_TAC real_ss [mult_rat,REAL_LT_REFL,ZERO_LESS_MULT],
   DISJ2_TAC THEN
   `&b <> 0:real /\ &b' <> 0:real` by FULL_SIMP_TAC real_ss [REAL_LT_IMP_NE] THEN
   `0:real < &(b * b')` by METIS_TAC [extreal_lt_eq,REAL_LT_MUL,mult_ints] THEN
   `&(b * b') <> 0:real` by RW_TAC std_ss [REAL_LT_IMP_NE] THEN
   Q.EXISTS_TAC `a*a'` THEN Q.EXISTS_TAC `b*b'` THEN
   FULL_SIMP_TAC real_ss [mult_rat,REAL_LT_REFL,ZERO_LESS_MULT],
   DISJ1_TAC THEN
   `&b <> 0:real /\ &b' <> 0:real` by FULL_SIMP_TAC real_ss [REAL_LT_IMP_NE] THEN
   `0:real < &(b * b')` by METIS_TAC [extreal_lt_eq,REAL_LT_MUL,mult_ints] THEN
   `&(b * b') <> 0:real` by RW_TAC std_ss [REAL_LT_IMP_NE] THEN
   Q.EXISTS_TAC `a*a'` THEN Q.EXISTS_TAC `b*b'` THEN
   FULL_SIMP_TAC real_ss [mult_rat,REAL_LT_REFL,ZERO_LESS_MULT]]);

val DIV_IN_QSET = store_thm ("DIV_IN_QSET",
  ``!x y. (x IN Qset) /\ (y IN Qset) /\ (y <> 0) ==> (x / y IN Qset)``,
  RW_TAC std_ss [] THEN
  `(inv y) IN Qset` by METIS_TAC [INV_IN_QSET, REAL_INV_1OVER, INV_IN_QSET] THEN
  METIS_TAC [MUL_IN_QSET, real_div]);

val CLG_UBOUND = store_thm ("CLG_UBOUND",
  ``!x. (0 <= x) ==> &(clg(x)) < (x) + 1``,
  RW_TAC std_ss [NUM_CEILING_def] THEN LEAST_ELIM_TAC THEN
  REWRITE_TAC [SIMP_REAL_ARCH] THEN RW_TAC real_ss [] THEN
  FULL_SIMP_TAC real_ss [GSYM real_lt] THEN
  PAT_X_ASSUM ``!m. P`` (MP_TAC o Q.SPEC `n-1`) THEN
  RW_TAC real_ss [] THEN Cases_on `n = 0` THENL
  [METIS_TAC [REAL_LET_ADD2,REAL_LT_01,REAL_ADD_RID], ALL_TAC] THEN
  `0 < n` by RW_TAC real_ss [] THEN
  `&(n - 1) < x:real` by RW_TAC real_ss [] THEN
  `0 <= n-1` by RW_TAC real_ss [] THEN
  `0:real <= (&(n-1))` by RW_TAC real_ss [] THEN
  `0 < x` by METIS_TAC [REAL_LET_TRANS] THEN Cases_on `n = 1` THENL
  [METIS_TAC [REAL_LE_REFL,REAL_ADD_RID,REAL_LTE_ADD2,REAL_ADD_COMM], ALL_TAC] THEN
  `0 <> n-1` by RW_TAC real_ss [] THEN
  `&n - 1 < x` by RW_TAC real_ss [REAL_SUB] THEN
  FULL_SIMP_TAC real_ss [REAL_LT_SUB_RADD]);

val Q_DENSE_IN_REAL_LEMMA = store_thm ("Q_DENSE_IN_REAL_LEMMA",
  ``!x y. (0 <= x) /\ (x < y) ==> ?r. (r IN Qset) /\ (x < r) /\ (r < y)``,
  RW_TAC std_ss [] THEN Cases_on `1:real < y - x` THENL
  [Q.EXISTS_TAC `&(clg y) - 1:real` THEN CONJ_TAC THENL
   [METIS_TAC [SUB_IN_QSET,NUM_IN_QSET], ALL_TAC] THEN
   RW_TAC std_ss [] THENL
   [METIS_TAC [REAL_LT_SUB_LADD,REAL_LT_ADD_SUB,REAL_ADD_COMM,
               REAL_LTE_TRANS,LE_NUM_CEILING], ALL_TAC] THEN
    METIS_TAC [REAL_LT_SUB_RADD,CLG_UBOUND,REAL_LET_TRANS,
               REAL_LT_IMP_LE], ALL_TAC] THEN
  `0 < y - x:real` by RW_TAC real_ss [REAL_SUB_LT] THEN
  (MP_TAC o Q.SPEC `1`) (((UNDISCH o Q.SPEC `y - x`) REAL_ARCH)) THEN
  RW_TAC real_ss [] THEN
  Q_TAC SUFF_TAC `?z. z IN Qset /\ &n * x < z /\ z < &n * y` THENL
  [RW_TAC real_ss [] THEN
   `0 < n` by ( RW_TAC real_ss [] THEN SPOSE_NOT_THEN ASSUME_TAC THEN
   `n = 0` by RW_TAC real_ss [] THEN FULL_SIMP_TAC real_ss []) THEN
   `0 < (&n):real` by RW_TAC real_ss [lt_int] THEN Q.EXISTS_TAC `z / (&n)` THEN
   RW_TAC real_ss [DIV_IN_QSET,NUM_IN_QSET] THENL
   [FULL_SIMP_TAC real_ss [REAL_LT_RDIV_EQ] THEN METIS_TAC [REAL_MUL_SYM],
    ALL_TAC] THEN
   FULL_SIMP_TAC real_ss [REAL_LT_RDIV_EQ,REAL_MUL_COMM,REAL_LT_IMP_NE] THEN
   FULL_SIMP_TAC real_ss [REAL_LT_LDIV_EQ,REAL_MUL_COMM,REAL_LT_IMP_NE],
   ALL_TAC] THEN
  `1 < &n * y - &n * x` by FULL_SIMP_TAC real_ss [REAL_SUB_LDISTRIB] THEN
  Q.EXISTS_TAC `&(clg (&n * y)) - 1` THEN CONJ_TAC THENL
  [METIS_TAC [SUB_IN_QSET,NUM_IN_QSET], ALL_TAC] THEN RW_TAC std_ss [] THENL
  [METIS_TAC [REAL_LT_SUB_LADD,REAL_LT_ADD_SUB,REAL_ADD_COMM,
              REAL_LTE_TRANS,LE_NUM_CEILING], ALL_TAC] THEN
  `0:real <= &n` by RW_TAC real_ss [] THEN
  `0:real <= &n * y` by METIS_TAC [REAL_LE_MUL,REAL_LET_TRANS,REAL_LT_IMP_LE] THEN
  METIS_TAC [REAL_LT_SUB_RADD,CLG_UBOUND,REAL_LET_TRANS,REAL_LT_IMP_LE]);

val Q_DENSE_IN_REAL = store_thm ("Q_DENSE_IN_REAL",
  ``!x y. (x < y) ==> ?r. (r IN Qset) /\ (x < r) /\ (r < y)``,
  RW_TAC std_ss [] THEN Cases_on `0 <= x` THENL
  [RW_TAC std_ss [Q_DENSE_IN_REAL_LEMMA], ALL_TAC] THEN
  FULL_SIMP_TAC std_ss [REAL_NOT_LE] THEN
  `-x <= &(clg (-x))` by RW_TAC real_ss [LE_NUM_CEILING] THEN
  `0:real <= x + &clg (-x)` by METIS_TAC [REAL_LE_LNEG] THEN
  `x + &(clg (-x)) < y + &(clg (-x))` by METIS_TAC [REAL_LT_RADD] THEN
  Q_TAC SUFF_TAC `?z. (z IN Qset) /\ (x + &clg (-x) < z) /\
                      (z < y + &clg (-x))` THENL
  [RW_TAC std_ss [] THEN Q.EXISTS_TAC `z - &clg (-x)` THEN
   CONJ_TAC THENL [METIS_TAC [SUB_IN_QSET,NUM_IN_QSET], ALL_TAC] THEN
   RW_TAC std_ss [GSYM REAL_LT_ADD_SUB,REAL_LT_SUB_RADD], ALL_TAC] THEN
  RW_TAC std_ss [Q_DENSE_IN_REAL_LEMMA]);

val BIGUNION_IMAGE_QSET = store_thm
  ("BIGUNION_IMAGE_QSET",
   ``!a f: real -> 'a -> bool. sigma_algebra a /\ f IN (Qset -> subsets a)
            ==> BIGUNION (IMAGE f Qset) IN subsets a``,
   RW_TAC std_ss [SIGMA_ALGEBRA, IN_FUN_SET, IN_UNIV, SUBSET_DEF] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN RW_TAC std_ss [IN_IMAGE] THEN
   ASM_SIMP_TAC std_ss [] THEN MATCH_MP_TAC image_countable THEN
   SIMP_TAC std_ss [QSET_COUNTABLE]);

(* i.e. open interval *)
val box = new_definition ("box",
  ``box a b = {x:real | a < x /\ x < b}``);

val rational_boxes = store_thm ("rational_boxes",
  ``!x e. 0 < e ==> ?a b. a IN Qset /\ b IN Qset /\ x IN box a b /\
                          box a b SUBSET ball (x,e)``,
  RW_TAC std_ss [] THEN
  `0:real < e / 2` by FULL_SIMP_TAC real_ss [] THEN
  KNOW_TAC ``?y. y IN Qset /\ y < x /\ x - y < e / 2`` THENL
  [MP_TAC (ISPECL [``x - e / 2:real``,``x:real``] Q_DENSE_IN_REAL) THEN
   DISCH_TAC THEN
   REWRITE_TAC [REAL_ARITH ``y < x /\ x - y < e:real = x - e < y /\ y < x``] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC, STRIP_TAC] THEN
  KNOW_TAC ``?y. y IN Qset /\ x < y /\ y - x < e / 2`` THENL
  [MP_TAC (ISPECL [``x:real``,``x + e / 2:real``] Q_DENSE_IN_REAL) THEN
   DISCH_TAC THEN
   REWRITE_TAC [REAL_ARITH ``x < y /\ y - x < e:real = x < y /\ y < x + e``] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN METIS_TAC [REAL_LT_ADDR], STRIP_TAC] THEN
  EXISTS_TAC ``y:real`` THEN EXISTS_TAC ``y':real`` THEN
  FULL_SIMP_TAC std_ss [box, GSPECIFICATION, IN_BALL, SUBSET_DEF, dist] THEN
  RW_TAC real_ss [] THEN GEN_REWR_TAC RAND_CONV [GSYM REAL_HALF_DOUBLE] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC ``(x - y) + (y' - x):real`` THEN
  CONJ_TAC THENL [ALL_TAC, METIS_TAC [REAL_LT_ADD2]] THEN
  ASM_REAL_ARITH_TAC);

val open_UNION_box = store_thm ("open_UNION_box",
  ``!M. real_topology$Open M ==> (M = BIGUNION {box a b | box a b SUBSET M})``,
  RW_TAC std_ss [OPEN_CONTAINS_BALL] THEN
  SIMP_TAC std_ss [EXTENSION, IN_BIGUNION, GSPECIFICATION, EXISTS_PROD] THEN
  GEN_TAC THEN EQ_TAC THEN STRIP_TAC THENL
  [FIRST_X_ASSUM (MP_TAC o SPEC ``x:real``) THEN ASM_REWRITE_TAC [] THEN
   STRIP_TAC THEN
   FIRST_ASSUM (MP_TAC o SPEC ``x:real`` o MATCH_MP rational_boxes) THEN
   STRIP_TAC THEN METIS_TAC [SUBSET_DEF], ALL_TAC] THEN
  FULL_SIMP_TAC std_ss [SUBSET_DEF]);

val open_union_box = store_thm ("open_union_box",
  ``!M. real_topology$Open M ==> (M = BIGUNION
        {box (FST (f)) (SND (f)) | f IN {f | box (FST(f)) (SND(f)) SUBSET M}})``,
  RW_TAC std_ss [OPEN_CONTAINS_BALL] THEN
  SIMP_TAC std_ss [EXTENSION, IN_BIGUNION, GSPECIFICATION, EXISTS_PROD] THEN
  GEN_TAC THEN EQ_TAC THEN STRIP_TAC THENL
  [FIRST_X_ASSUM (MP_TAC o SPEC ``x:real``) THEN ASM_REWRITE_TAC [] THEN
   STRIP_TAC THEN
   FIRST_ASSUM (MP_TAC o SPEC ``x:real`` o MATCH_MP rational_boxes) THEN
   STRIP_TAC THEN METIS_TAC [SUBSET_DEF], ALL_TAC] THEN
  FULL_SIMP_TAC std_ss [SUBSET_DEF]);

val open_union_box = store_thm ("open_union_box",
  ``!M. real_topology$Open M ==> (M = BIGUNION
        {box (FST (f)) (SND (f)) | f IN {f | (?q r. (f = (q,r)) /\
            q IN Qset /\ r IN Qset) /\ box (FST(f)) (SND(f)) SUBSET M}})``,
  RW_TAC std_ss [OPEN_CONTAINS_BALL] THEN
  SIMP_TAC std_ss [EXTENSION, IN_BIGUNION, GSPECIFICATION, EXISTS_PROD] THEN
  GEN_TAC THEN EQ_TAC THEN STRIP_TAC THENL
  [FIRST_X_ASSUM (MP_TAC o SPEC ``x:real``) THEN ASM_REWRITE_TAC [] THEN
   STRIP_TAC THEN
   FIRST_ASSUM (MP_TAC o SPEC ``x:real`` o MATCH_MP rational_boxes) THEN
   STRIP_TAC THEN METIS_TAC [SUBSET_DEF], ALL_TAC] THEN
  FULL_SIMP_TAC std_ss [SUBSET_DEF]);

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* ------------------------------------------------------------------------- *)

val borel_eq_box = store_thm ("borel_eq_box",
  ``borel = sigma UNIV (IMAGE (\(a,b). box a b) UNIV)``,
  SIMP_TAC std_ss [box] THEN MATCH_MP_TAC borel_eq_sigmaI1 THEN
  EXISTS_TAC ``{s | real_topology$Open s}`` THEN SIMP_TAC std_ss [borel] THEN
  CONJ_TAC THENL
  [ALL_TAC,
   FULL_SIMP_TAC std_ss [sigma_def, subsets_def] THEN
   FULL_SIMP_TAC std_ss [IN_BIGINTER, GSPECIFICATION] THEN
   RW_TAC std_ss [] THEN
   FULL_SIMP_TAC std_ss [SUBSET_DEF] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
   SIMP_TAC std_ss [GSPECIFICATION] THEN
   MP_TAC (ISPEC ``i:real#real`` ABS_PAIR_THM) THEN STRIP_TAC THEN
   FULL_SIMP_TAC std_ss [GSYM interval, OPEN_INTERVAL]] THEN
  RW_TAC std_ss [GSPECIFICATION] THEN
  FIRST_ASSUM (ASSUME_TAC o MATCH_MP open_union_box) THEN
  ONCE_ASM_REWRITE_TAC [] THEN
  ONCE_REWRITE_TAC [METIS []
   ``box (FST f) (SND f) = (\f. box (FST f) (SND f)) f``] THEN
  MATCH_MP_TAC countable_UN' THEN EXISTS_TAC ``univ(:real)`` THEN
  RW_TAC std_ss [] THENL
  [KNOW_TAC ``sigma_algebra
   (space (sigma univ(:real)
         (IMAGE (\(a,b). {x | a < x /\ x < b}) univ(:real # real))),
    subsets (sigma univ(:real)
         (IMAGE (\(a,b). {x | a < x /\ x < b}) univ(:real # real))))`` THENL
   [ALL_TAC, METIS_TAC [SPACE_SIGMA]] THEN SIMP_TAC std_ss [SPACE] THEN
   MATCH_MP_TAC SIGMA_ALGEBRA_SIGMA THEN SIMP_TAC std_ss [subset_class_def] THEN
   SIMP_TAC std_ss [SUBSET_UNIV],
   RW_TAC std_ss [SUBSET_DEF, IN_IMAGE, subsets_def, sigma_def, GSPECIFICATION] THEN
   RW_TAC std_ss [IN_BIGINTER, GSPECIFICATION, IN_UNIV] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC ``(q:real, r:real)`` THEN
   SIMP_TAC std_ss [box], ALL_TAC] THEN
  MATCH_MP_TAC pred_setTheory.COUNTABLE_SUBSET THEN
  EXISTS_TAC ``{f | (?q r. (f = (q,r)) /\ q IN Qset /\ r IN Qset)}`` THEN
  CONJ_TAC THENL [SET_TAC [], ALL_TAC] THEN
  ONCE_REWRITE_TAC [SET_RULE ``{f | ?q r. (f = (q,r)) /\ q IN Qset /\ r IN Qset} =
                               {f | FST f IN Qset /\ SND f IN Qset}``] THEN
  SIMP_TAC std_ss [GSYM CROSS_DEF] THEN
  MATCH_MP_TAC CROSS_COUNTABLE THEN
  SIMP_TAC std_ss [QSET_COUNTABLE]);

val borel_eq_greaterThanLessThan = store_thm ("borel_eq_greaterThanLessThan",
  ``borel = sigma UNIV (IMAGE (\(a,b). {x | a < x /\ x < b}) UNIV)``,
  SIMP_TAC std_ss [borel_eq_box, box]);

val halfspace_gt_in_halfspace = store_thm ("halfspace_gt_in_halfspace",
  ``!a. {x | x < a} IN
        subsets (sigma univ(:real) (IMAGE (\(a,i). {x | x < a}) UNIV))``,
  RW_TAC std_ss [sigma_def, subsets_def, IN_BIGINTER, GSPECIFICATION,
                 SUBSET_DEF] THEN ASM_SET_TAC []);

val borel_eq_halfspace_less = store_thm ("borel_eq_halfspace_less",
  ``borel = sigma UNIV (IMAGE (\a. {x | x < a}) UNIV)``,
  ONCE_REWRITE_TAC [SET_RULE
   ``(IMAGE (\a. {x | x < a}) univ(:real)) =
     (IMAGE (\(a:real,i:num). (\a i. {x | x < a}) a i) UNIV)``] THEN
  KNOW_TAC `` (borel = sigma univ(:real) (IMAGE (\(i,j). box i j) UNIV)) /\
  (!i j. (i,j) IN UNIV ==>
     box i j IN subsets (sigma univ(:real)
          (IMAGE (\(i,j). (\a i. {x | x < a}) i j)
             univ(:real # num)))) /\
  !i j. (i,j) IN univ(:real # num) ==>
    (\a i. {x | x < a}) i j IN subsets borel`` THENL
  [ALL_TAC, DISCH_THEN (MP_TAC o MATCH_MP borel_eq_sigmaI2) THEN
   SIMP_TAC std_ss []] THEN SIMP_TAC std_ss [borel_eq_box] THEN
  SIMP_TAC std_ss [GSYM borel_eq_box, IN_UNIV] THEN
  KNOW_TAC ``!a b. box a b =
    {x | x IN space (sigma UNIV (IMAGE (\a. {x | x < a}) UNIV)) /\
         (\x. a < x) x /\ (\x. x < b) x}`` THENL
  [SIMP_TAC std_ss [SPACE_SIGMA, box, EXTENSION, GSPECIFICATION, IN_UNIV],
   DISCH_TAC] THEN CONJ_TAC THENL
  [ONCE_ASM_REWRITE_TAC [] THEN
   REPEAT GEN_TAC THEN MATCH_MP_TAC sets_Collect_conj THEN CONJ_TAC THENL
   [RW_TAC std_ss [semiring] THENL
    [SIMP_TAC std_ss [subset_class_def, SPACE_SIGMA, SUBSET_UNIV],
     RW_TAC std_ss [sigma_def, subsets_def, IN_BIGINTER,
                    GSPECIFICATION, SUBSET_DEF] THEN
     FULL_SIMP_TAC std_ss [sigma_algebra_iff2],
     RW_TAC std_ss [sigma_def, subsets_def, IN_BIGINTER,
                    GSPECIFICATION, SUBSET_DEF] THEN
     ONCE_REWRITE_TAC [METIS [subsets_def] ``P = subsets (univ(:real), P)``] THEN
     MATCH_MP_TAC ALGEBRA_INTER THEN
     ASM_SIMP_TAC std_ss [SIGMA_ALGEBRA_ALGEBRA] THEN
     FULL_SIMP_TAC std_ss [sigma_def, subsets_def, IN_BIGINTER,
                           GSPECIFICATION, SUBSET_DEF],
     ALL_TAC] THEN Q.EXISTS_TAC `{s DIFF t}` THEN
    SIMP_TAC std_ss [BIGUNION_SING, FINITE_SING, disjoint_sing] THEN
    FULL_SIMP_TAC std_ss [sigma_def, subsets_def, IN_BIGINTER,
                          GSPECIFICATION, SUBSET_DEF] THEN
    RW_TAC std_ss [IN_SING] THEN
    ONCE_REWRITE_TAC [METIS [subsets_def] ``P = subsets (univ(:real), P)``] THEN
    MATCH_MP_TAC ALGEBRA_DIFF THEN ASM_SIMP_TAC std_ss [SIGMA_ALGEBRA_ALGEBRA] THEN
    FULL_SIMP_TAC std_ss [sigma_def, subsets_def, IN_BIGINTER,
                          GSPECIFICATION, SUBSET_DEF],
    ALL_TAC] THEN CONJ_TAC THENL
   [ALL_TAC, SIMP_TAC std_ss [SPACE_SIGMA, halfspace_gt_in_halfspace, IN_UNIV]] THEN
   SIMP_TAC std_ss [SPACE_SIGMA, IN_UNIV] THEN POP_ASSUM K_TAC THEN
   KNOW_TAC ``!a. {x | a < x} = UNIV DIFF {x:real | x <= a}`` THENL
   [RW_TAC std_ss [GSPECIFICATION, EXTENSION, IN_UNIV, IN_DIFF] THEN
    REAL_ARITH_TAC, DISC_RW_KILL] THEN MATCH_MP_TAC ALGEBRA_DIFF THEN
   RW_TAC std_ss [] THENL
   [RW_TAC std_ss [algebra_def, sigma_def, subsets_def, space_def] THENL
    [SIMP_TAC std_ss [subset_class_def, SUBSET_UNIV],
     SIMP_TAC std_ss [IN_BIGINTER, GSPECIFICATION] THEN
     FULL_SIMP_TAC std_ss [sigma_algebra_iff2],
     FULL_SIMP_TAC std_ss [IN_BIGINTER, GSPECIFICATION] THEN
     RW_TAC std_ss [] THEN FULL_SIMP_TAC std_ss [sigma_algebra_iff2],
     FULL_SIMP_TAC std_ss [IN_BIGINTER, GSPECIFICATION] THEN RW_TAC std_ss [] THEN
     ONCE_REWRITE_TAC [METIS [subsets_def] ``P = subsets (univ(:real), P)``] THEN
     MATCH_MP_TAC ALGEBRA_UNION THEN
     FULL_SIMP_TAC std_ss [SIGMA_ALGEBRA_ALGEBRA] THEN
     FULL_SIMP_TAC std_ss [subsets_def]],
    RW_TAC std_ss [algebra_def, sigma_def, subsets_def, space_def] THEN
    SIMP_TAC std_ss [IN_BIGINTER, GSPECIFICATION] THEN RW_TAC std_ss [] THEN
    FULL_SIMP_TAC std_ss [sigma_algebra_iff2] THEN
    FIRST_X_ASSUM (MP_TAC o SPEC ``{}:real->bool``) THEN ASM_REWRITE_TAC [] THEN
    SIMP_TAC std_ss [DIFF_EMPTY],
    ALL_TAC] THEN
   RW_TAC std_ss [] THEN
  KNOW_TAC ``!c. {x:real | x <= c} =
   BIGINTER (IMAGE (\n:num. {x | x < (c + (1/2) pow n)}) UNIV)`` THENL
  [RW_TAC std_ss [EXTENSION, IN_BIGINTER_IMAGE, IN_UNIV,IN_INTER] THEN EQ_TAC THENL
   [RW_TAC std_ss [GSPECIFICATION] THEN
     `0:real < (1/2) pow n` by RW_TAC real_ss [REAL_POW_LT] THEN
     `0:real < ((1 / 2) pow n)` by METIS_TAC [util_probTheory.POW_HALF_POS] THEN
     ASM_REAL_ARITH_TAC, ALL_TAC] THEN
    RW_TAC std_ss [GSPECIFICATION] THEN
    `!n. x:real < (c + (1 / 2) pow n)` by METIS_TAC [] THEN
    `(\n. c + (1 / 2) pow n) = (\n. (\n. c) n + (\n. (1 / 2) pow n) n) `
     by RW_TAC real_ss [FUN_EQ_THM] THEN
    ASSUME_TAC (ISPEC ``c:real`` SEQ_CONST) THEN
    MP_TAC (ISPEC ``1 / (2:real)`` SEQ_POWER) THEN
    KNOW_TAC ``abs (1 / 2) < 1:real`` THENL
    [REWRITE_TAC [abs] THEN COND_CASES_TAC THEN
     SIMP_TAC std_ss [REAL_HALF_BETWEEN] THEN
     REWRITE_TAC [real_div, REAL_NEG_LMUL] THEN SIMP_TAC std_ss [GSYM real_div] THEN
     SIMP_TAC real_ss [REAL_LT_LDIV_EQ], DISCH_TAC THEN ASM_REWRITE_TAC [] THEN
     POP_ASSUM K_TAC THEN DISCH_TAC] THEN
    MP_TAC (Q.SPECL [`(\n. c)`,`c`,`(\n. (1/2) pow n)`,`0`] SEQ_ADD) THEN
    ASM_REWRITE_TAC [] THEN BETA_TAC THEN SIMP_TAC std_ss [REAL_ADD_RID] THEN
    DISCH_TAC THEN METIS_TAC [REAL_LT_IMP_LE,
     Q.SPECL [`r`,`c`,`(\n. c + (1 / 2) pow n)`] LE_SEQ_IMP_LE_LIM], ALL_TAC] THEN
   FULL_SIMP_TAC std_ss [] THEN DISCH_TAC THEN
   KNOW_TAC ``sigma_algebra  (sigma univ(:real)
               (IMAGE (\(i',j). {x | x < i'}) univ(:real # num)))`` THENL
   [MATCH_MP_TAC SIGMA_ALGEBRA_SIGMA THEN
    SIMP_TAC std_ss [subset_class_def, SUBSET_UNIV],
    DISCH_TAC] THEN
   (MP_TAC o UNDISCH o Q.SPEC `(sigma univ(:real) (IMAGE (\(i',j). {x | x < i'})
                                univ(:real # num)))`)
    (INST_TYPE [alpha |-> ``:real``] SIGMA_ALGEBRA_FN_BIGINTER)  THEN
   RW_TAC std_ss [] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
   RW_TAC std_ss [IN_FUNSET, IN_UNIV] THEN MATCH_MP_TAC IN_SIGMA THEN
   SIMP_TAC std_ss [IN_IMAGE, IN_UNIV] THEN
   Q.EXISTS_TAC `(i + (1 / 2) pow n, 1)` THEN
   SIMP_TAC std_ss [], ALL_TAC] THEN
  METIS_TAC [OPEN_HALFSPACE_COMPONENT_LT, borel_open]);

val reals_Archimedean = store_thm ("reals_Archimedean",
  ``!x:real. 0 < x ==> ?n. inv &(SUC n) < x``,
  RW_TAC real_ss [REAL_INV_1OVER] THEN SIMP_TAC real_ss [REAL_LT_LDIV_EQ] THEN
  ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN
  ASM_SIMP_TAC real_ss [GSYM REAL_LT_LDIV_EQ] THEN
  MP_TAC (ISPEC ``1 / x:real`` SIMP_REAL_ARCH) THEN STRIP_TAC THEN
  Q.EXISTS_TAC `n` THEN FULL_SIMP_TAC real_ss [real_div] THEN
  RULE_ASSUM_TAC (ONCE_REWRITE_RULE [GSYM REAL_LT_INV_EQ]) THEN
  REWRITE_TAC [ADD1, GSYM add_ints] THEN ASM_REAL_ARITH_TAC);

val borel_eq_halfspace_le = store_thm ("borel_eq_halfspace_le",
  ``borel = sigma UNIV (IMAGE (\a. {x | x <= a}) UNIV)``,
  ONCE_REWRITE_TAC [SET_RULE
   `` (IMAGE (\a. {x | x <= a}) univ(:real)) =
      (IMAGE (\(a:real,i:num). (\a i. {x | x <= a}) a i) UNIV)``] THEN
  KNOW_TAC `` (borel = sigma univ(:real)
  (IMAGE (\(i:real,j:num). (\a i. {x | x < a}) i j) UNIV)) /\
  (!i j. (i:real,j:num) IN UNIV ==>
     (\a i. {x | x < a}) i j IN
     subsets (sigma univ(:real)
          (IMAGE (\(i,j). (\a i. {x | x <= a}) i j)
             univ(:real # num)))) /\
  !i j. (i,j) IN univ(:real # num) ==>
    (\a i. {x | x <= a}) i j IN subsets borel`` THENL
  [ALL_TAC, DISCH_THEN (MP_TAC o MATCH_MP borel_eq_sigmaI2) THEN
   SIMP_TAC std_ss []] THEN
  ONCE_REWRITE_TAC [SET_RULE
   ``(IMAGE (\(i:real,j:num). (\a i. {x | x < a}) i j) UNIV) =
     (IMAGE (\a. {x | x < a}) univ(:real))``] THEN
  SIMP_TAC std_ss [borel_eq_halfspace_less, IN_UNIV] THEN
  KNOW_TAC ``!a:real. {x | x < a} =
    BIGUNION {{x | x <= a - 1 / &(SUC n)} | n IN UNIV}`` THENL
  [RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_BIGUNION, IN_UNIV] THEN
   ASM_CASES_TAC ``x < a:real`` THENL
   [ASM_REWRITE_TAC [] THEN MP_TAC (ISPEC ``a - x:real`` reals_Archimedean) THEN
    ASM_REWRITE_TAC [REAL_SUB_LT] THEN STRIP_TAC THEN
    RULE_ASSUM_TAC (ONCE_REWRITE_RULE [REAL_ARITH
     ``a < b - c = c < b - a:real``]) THEN
    Q.EXISTS_TAC `{x:real | x <= a - inv (&SUC n)}` THEN
    ASM_SIMP_TAC std_ss [GSPECIFICATION] THEN
    GEN_REWR_TAC LAND_CONV [REAL_LE_LT] THEN ASM_SIMP_TAC real_ss [real_div] THEN
    METIS_TAC [], ALL_TAC] THEN
   ASM_SIMP_TAC std_ss [] THEN RW_TAC std_ss [] THEN
   ASM_CASES_TAC ``(x:real) NOTIN s`` THEN
   ASM_SIMP_TAC std_ss [] THEN GEN_TAC THEN FULL_SIMP_TAC std_ss [REAL_NOT_LT] THEN
   EXISTS_TAC ``x:real`` THEN ASM_SIMP_TAC std_ss [REAL_NOT_LE] THEN
   KNOW_TAC ``0:real < 1 / &SUC n`` THENL [ALL_TAC, ASM_REAL_ARITH_TAC] THEN
   SIMP_TAC real_ss [REAL_LT_RDIV_EQ], DISCH_TAC] THEN
  ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
  [RW_TAC std_ss [subsets_def, sigma_def, IN_BIGINTER,
                  GSPECIFICATION, SUBSET_DEF] THEN
   FULL_SIMP_TAC std_ss [SIGMA_ALGEBRA, subsets_def] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   CONJ_TAC THENL
   [SIMP_TAC std_ss [GSYM IMAGE_DEF] THEN
    MATCH_MP_TAC image_countable THEN
    SIMP_TAC std_ss [pred_setTheory.COUNTABLE_NUM], ALL_TAC] THEN
   RW_TAC std_ss [SUBSET_DEF, GSPECIFICATION] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
   SET_TAC [], ALL_TAC] THEN
  RULE_ASSUM_TAC (ONCE_REWRITE_RULE [EQ_SYM_EQ]) THEN ASM_REWRITE_TAC [] THEN
  SIMP_TAC std_ss [GSYM borel_eq_halfspace_less] THEN GEN_TAC THEN
  MATCH_MP_TAC borel_closed THEN SIMP_TAC std_ss [CLOSED_HALFSPACE_COMPONENT_LE]);

val borel_eq_greaterThan = store_thm ("borel_eq_greaterThan",
  ``borel = sigma UNIV (IMAGE (\a. {x | a < x}) UNIV)``,
  KNOW_TAC ``(borel = sigma univ(:real) (IMAGE (\(i,j). (\a i. {x | x <= a}) i j) univ(:real#num))) /\
  (!i j.
     (i:real,j:num) IN UNIV ==>
     (\a i. {x | x <= a}) i j IN
     subsets
       (sigma univ(:real) (IMAGE (\a. {x | a < x}) univ(:real)))) /\
  !i. (\a. {x | a < x}) i IN subsets borel`` THENL
  [ALL_TAC, DISCH_THEN (MP_TAC o MATCH_MP borel_eq_sigmaI4) THEN
   SIMP_TAC std_ss []] THEN SIMP_TAC std_ss [borel_eq_halfspace_le] THEN
  ONCE_REWRITE_TAC [SET_RULE
   `` (IMAGE (\a. {x | x <= a}) univ(:real)) =
      (IMAGE (\(a:real,i:num). (\a i. {x | x <= a}) a i) UNIV)``] THEN
  SIMP_TAC std_ss [IN_UNIV] THEN CONJ_TAC THENL
  [ALL_TAC,
   ONCE_REWRITE_TAC [SET_RULE ``(IMAGE (\(a:real,i:num). {x | x <= a}) UNIV) =
                                (IMAGE (\a. {x | x <= a}) univ(:real))``] THEN
   SIMP_TAC std_ss [GSYM borel_eq_halfspace_le] THEN GEN_TAC THEN
   MATCH_MP_TAC borel_open THEN SIMP_TAC std_ss [OPEN_INTERVAL_RIGHT]] THEN
  KNOW_TAC ``!a:real. {x | x <= a} = UNIV DIFF {x | a < x}`` THENL
  [RW_TAC std_ss [EXTENSION, IN_DIFF, GSPECIFICATION, IN_UNIV] THEN
   REAL_ARITH_TAC, DISCH_TAC] THEN
  RW_TAC std_ss [sigma_def, subsets_def, IN_BIGINTER, GSPECIFICATION,
                 IN_UNIV, SUBSET_DEF] THEN
  ONCE_REWRITE_TAC [METIS [subsets_def] ``P = subsets (univ(:real), P)``] THEN
  MATCH_MP_TAC ALGEBRA_DIFF THEN ASM_SIMP_TAC std_ss [SIGMA_ALGEBRA_ALGEBRA] THEN
  CONJ_TAC THENL
  [FULL_SIMP_TAC std_ss [sigma_algebra_iff2, subsets_def] THEN
   ONCE_REWRITE_TAC [SET_RULE ``UNIV = UNIV DIFF {}``] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [],
   ALL_TAC] THEN
  SIMP_TAC std_ss [subsets_def] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  SIMP_TAC std_ss [IN_IMAGE, IN_UNIV] THEN METIS_TAC []);

val borel_eq_atLeastAtMost = store_thm ("borel_eq_atLeastAtMost",
  ``borel = sigma UNIV (IMAGE (\(a,b). {x | a <= x /\ x <= b}) UNIV)``,
  ONCE_REWRITE_TAC [METIS [] ``{x | a <= x /\ x <= b} =
                   (\a b. {x:real | a <= x /\ x <= b}) a b``] THEN
  KNOW_TAC ``(borel = sigma univ(:real) (IMAGE (\a. {x | x <= a}) univ(:real))) /\
  (!i.
     (\a. {x | x <= a}) i IN
     subsets
       (sigma univ(:real)
          (IMAGE (\(i,j). (\a b. {x | a <= x /\ x <= b}) i j)
             univ(:real # real)))) /\
  !i j. (\a b. {x | a <= x /\ x <= b}) i j IN subsets borel`` THENL
  [ALL_TAC,
   DISCH_THEN (MP_TAC o MATCH_MP borel_eq_sigmaI5) THEN SIMP_TAC std_ss []] THEN
  SIMP_TAC std_ss [borel_eq_halfspace_le] THEN
  KNOW_TAC ``!a. {x | x <= a} =
       BIGUNION {{x:real | -&n <= x /\ x <= a} | n IN UNIV}`` THENL
  [RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_BIGUNION, IN_UNIV] THEN
   EQ_TAC THENL
   [ALL_TAC, STRIP_TAC THEN POP_ASSUM (MP_TAC o SPEC ``x:real``) THEN
    ASM_REWRITE_TAC [] THEN REAL_ARITH_TAC] THEN
   DISCH_TAC THEN MP_TAC (ISPEC ``-x:real`` SIMP_REAL_ARCH) THEN STRIP_TAC THEN
   POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM REAL_LE_NEG]) THEN
   RW_TAC std_ss [REAL_NEG_NEG] THEN Q.EXISTS_TAC `{x | -&n <= x /\ x <= a}` THEN
   ASM_SIMP_TAC std_ss [GSPECIFICATION] THEN METIS_TAC [], DISCH_TAC] THEN
  CONJ_TAC THENL
  [ALL_TAC, SIMP_TAC std_ss [GSYM borel_eq_halfspace_le] THEN
   REPEAT GEN_TAC THEN MATCH_MP_TAC borel_closed THEN
   SIMP_TAC std_ss [GSYM interval, CLOSED_INTERVAL]] THEN
  RW_TAC std_ss [subsets_def, sigma_def, IN_BIGINTER,
                 GSPECIFICATION, SUBSET_DEF] THEN
  ONCE_REWRITE_TAC [METIS [] ``{x | -&n <= x /\ x <= i} =
                     (\n. {x:real | -&n <= x /\ x <= i}) n``] THEN
  MATCH_MP_TAC countable_UN THEN EXISTS_TAC ``univ(:real)`` THEN
  ASM_SIMP_TAC std_ss [COUNTABLE_NUM] THEN
  RW_TAC std_ss [SUBSET_DEF, IN_IMAGE, IN_UNIV] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  SET_TAC []);

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* ------------------------------------------------------------------------- *)

val measurable_borel = store_thm ("measurable_borel",
   ``!f a. (f IN borel_measurable a) = (sigma_algebra a) /\
           (f IN (space a -> UNIV)) /\
           (!c. ((PREIMAGE f {x| x < c}) INTER (space a)) IN subsets a)``,
  RW_TAC std_ss [] THEN
  `sigma_algebra borel` by RW_TAC std_ss [sigma_algebra_borel] THEN
  `space borel = UNIV` by RW_TAC std_ss [space_borel] THEN EQ_TAC THENL
  [RW_TAC std_ss [borel_eq_halfspace_less,IN_MEASURABLE,IN_FUN_SET,
                  IN_UNIV,subsets_def,GSPECIFICATION, borel_measurable] THEN
   SIMP_TAC std_ss [] THEN POP_ASSUM MATCH_MP_TAC THEN
   MATCH_MP_TAC IN_SIGMA THEN RW_TAC std_ss [IN_IMAGE,IN_UNIV] THEN
   METIS_TAC [], ALL_TAC] THEN
  RW_TAC std_ss [borel_measurable, borel_eq_halfspace_less] THEN
  MATCH_MP_TAC MEASURABLE_SIGMA THEN
  RW_TAC std_ss [subset_class_def,SUBSET_UNIV,IN_IMAGE,IN_UNIV] THEN
  METIS_TAC []);

val measurable_borel_alt1 = store_thm ("measurable_borel_alt1",
  ``!f a. (f IN borel_measurable a) = (sigma_algebra a) /\
          (f IN (space a -> UNIV)) /\
          (!c. ((PREIMAGE f {x| c < x}) INTER (space a)) IN subsets a)``,
  RW_TAC std_ss [] THEN
  `sigma_algebra borel` by RW_TAC std_ss [sigma_algebra_borel] THEN
  `space borel = UNIV` by RW_TAC std_ss [space_borel] THEN EQ_TAC THENL
  [RW_TAC std_ss [borel_eq_greaterThan,IN_MEASURABLE,IN_FUN_SET,
                  IN_UNIV,subsets_def,GSPECIFICATION, borel_measurable] THEN
   SIMP_TAC std_ss [] THEN POP_ASSUM MATCH_MP_TAC THEN
   MATCH_MP_TAC IN_SIGMA THEN RW_TAC std_ss [IN_IMAGE,IN_UNIV] THEN
   METIS_TAC [], ALL_TAC] THEN
  RW_TAC std_ss [borel_measurable, borel_eq_greaterThan] THEN
  MATCH_MP_TAC MEASURABLE_SIGMA THEN
  RW_TAC std_ss [subset_class_def,SUBSET_UNIV,IN_IMAGE,IN_UNIV] THEN
  METIS_TAC []);

val in_measurable_borel = store_thm ("in_measurable_borel",
  ``!f a. f IN borel_measurable a =
	  (sigma_algebra a /\ f IN (space a -> UNIV) /\
	  !c. ({x | f x < c} INTER space a) IN subsets a)``,
  RW_TAC std_ss [] THEN
  `!c. {x | f x < c} = PREIMAGE f {x| x < c}` by
   RW_TAC std_ss [EXTENSION,IN_PREIMAGE,GSPECIFICATION] THEN
  RW_TAC std_ss [measurable_borel]);

val in_measurable_borel_alt1 = store_thm ("in_measurable_borel_alt1",
  ``!f a. f IN borel_measurable a =
	  (sigma_algebra a /\ f IN (space a -> UNIV) /\
	  !c. ({x | c < f x} INTER space a) IN subsets a)``,
  RW_TAC std_ss [] THEN
  `!c. {x | c < f x} = PREIMAGE f {x| c < x}` by
   RW_TAC std_ss [EXTENSION,IN_PREIMAGE,GSPECIFICATION] THEN
  RW_TAC std_ss [measurable_borel_alt1]);

val borel_measurable_const2 = store_thm ("borel_measurable_const2",
  ``!a k f. sigma_algebra a /\ (!x. x IN space a ==> (f x = k))
		 ==> f IN borel_measurable a``,
  RW_TAC std_ss [in_measurable_borel, IN_FUN_SET, IN_UNIV] THEN
  SIMP_TAC std_ss [PREIMAGE_def] THEN
  Cases_on `c <= k` THENL
  [`{x | f x < c} INTER space a = {}`
    by  (RW_TAC std_ss [EXTENSION, GSPECIFICATION, NOT_IN_EMPTY, IN_INTER] THEN
         METIS_TAC [REAL_NOT_LE]) THEN
   METIS_TAC [sigma_algebra_def, algebra_def], ALL_TAC] THEN
  `{x | f x < c} INTER space a = space a`
      by (RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER] THEN
          METIS_TAC [REAL_NOT_LT]) THEN
  METIS_TAC [sigma_algebra_def, algebra_def, INTER_IDEMPOT, DIFF_EMPTY]);

val borel_measurable_cmul = store_thm ("borel_measurable_cmul",
 ``!a f g z. sigma_algebra a /\ f IN borel_measurable a /\
      (!x. x IN space a ==> (g x = z * f x))
                   ==> g IN borel_measurable a``,
  RW_TAC std_ss [] THEN Cases_on `z = 0` THENL
  [METIS_TAC [borel_measurable_const2, REAL_MUL_LZERO], ALL_TAC] THEN
  Cases_on `0 < z` THENL
  [RW_TAC real_ss [in_measurable_borel,IN_FUN_SET,IN_UNIV] THEN
   `!c. {x | g x < c} INTER space a = {x | f x < c / z} INTER space a`
    by (RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER] THEN
        METIS_TAC [REAL_LT_RDIV_EQ, REAL_MUL_COMM, REAL_NOT_LT]) THEN
   METIS_TAC [in_measurable_borel], ALL_TAC] THEN
  `z < 0` by (POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN REAL_ARITH_TAC) THEN
  RW_TAC real_ss [in_measurable_borel, IN_FUN_SET, IN_UNIV] THEN
  `!c. {x | g x < c} INTER space a = {x | c / z < f x} INTER space a`
      by (RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER] THEN
          METIS_TAC [REAL_LT_RDIV_EQ_NEG, REAL_MUL_COMM]) THEN
  METIS_TAC [in_measurable_borel_alt1]);

val borel_measurable_add = store_thm
  ("borel_measurable_add",``!a f g h. sigma_algebra a /\ f IN borel_measurable a /\
	g IN borel_measurable a /\
        (!x. x IN space a ==> (h x = f x + g x)) ==> h IN borel_measurable a``,
  REPEAT STRIP_TAC THEN RW_TAC std_ss [in_measurable_borel] THENL
  [RW_TAC std_ss [IN_FUN_SET, IN_UNIV], ALL_TAC] THEN
  `{x | h x < c} INTER (space a) =
      BIGUNION (IMAGE (\r. {x | f x < r /\ r < c - g x } INTER space a) Qset)`
	by (RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_BIGUNION_IMAGE,
                           IN_UNIV, IN_INTER] THEN
	    EQ_TAC THENL
	    [RW_TAC std_ss [] THEN MATCH_MP_TAC Q_DENSE_IN_REAL THEN
       METIS_TAC [REAL_ARITH ``a < b - c = a + c < b:real``], ALL_TAC] THEN
	    REVERSE (RW_TAC std_ss []) THEN ASM_REWRITE_TAC [] THEN
	    METIS_TAC [REAL_LT_ADD_SUB,REAL_LT_TRANS]) THEN
  FULL_SIMP_TAC std_ss [] THEN MATCH_MP_TAC BIGUNION_IMAGE_QSET THEN
  RW_TAC std_ss [IN_FUN_SET] THEN
  `{x | f x < r /\ r < c - g x} =
   {x | f x < r} INTER {x | r < c - g x}`
   by RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER] THEN
  `({x | f x < r} INTER space a) IN subsets a`
      by METIS_TAC [in_measurable_borel] THEN
  `!x. x IN space a ==> ((r < c - g x) = (g x < c - r))`
        by REAL_ARITH_TAC THEN
  `{x | r < c - g x} INTER space a = {x | g x < c - r} INTER space a`
       by (RW_TAC std_ss [IN_INTER, EXTENSION, GSPECIFICATION] THEN
           METIS_TAC []) THEN
  `({x | r < c - g x} INTER space a) IN subsets a`
      by METIS_TAC [in_measurable_borel] THEN
  `(({x | f x < r} INTER space a) INTER
      ({x | r < c - g x} INTER space a)) =
      ({x | f x < r} INTER {x | r < c - g x} INTER space a)`
	by (RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER] THEN
	    EQ_TAC THENL [RW_TAC std_ss [], ALL_TAC] THEN
	    RW_TAC std_ss []) THEN
  METIS_TAC [sigma_algebra_def, ALGEBRA_INTER]);

val borel_measurable_sub = store_thm ("borel_measurable_sub",
  ``!a f g h. sigma_algebra a /\
         f IN borel_measurable a /\ g IN borel_measurable a  /\
        (!x. x IN space a ==> (h x = f x - g x)) ==> h IN borel_measurable a``,
  RW_TAC std_ss [] THEN
  MATCH_MP_TAC borel_measurable_add THEN
  Q.EXISTS_TAC `f` THEN
  Q.EXISTS_TAC `(\x. - g x)` THEN
  RW_TAC std_ss [real_sub] THEN
  MATCH_MP_TAC borel_measurable_cmul THEN
  Q.EXISTS_TAC `g` THEN Q.EXISTS_TAC `-1` THEN
  ASM_SIMP_TAC real_ss []);

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* ------------------------------------------------------------------------- *)

val real_set = new_definition ("real_set",
 ``real_set s = {real x | x <> PosInf /\ x <> NegInf /\ x IN s}``);

val borel_IMP_Borel = store_thm ("borel_IMP_Borel",
  ``!f m. f IN measurable (m_space m,measurable_sets m) borel ==>
         (\x. Normal (f x)) IN measurable (m_space m,measurable_sets m) Borel``,
  RW_TAC std_ss [IN_MEASURABLE, SIGMA_ALGEBRA_BOREL] THENL
  [EVAL_TAC THEN SRW_TAC[] [IN_DEF,IN_FUNSET], ALL_TAC] THEN
  FULL_SIMP_TAC std_ss [space_def, subsets_def] THEN
  KNOW_TAC ``PREIMAGE (\x. Normal ((f:'a->real) x)) s =
             PREIMAGE f (real_set s)`` THENL
  [SIMP_TAC std_ss [PREIMAGE_def, EXTENSION, GSPECIFICATION] THEN
   RW_TAC std_ss [real_set, GSPECIFICATION] THEN EQ_TAC THEN RW_TAC std_ss [] THENL
   [Q.EXISTS_TAC `Normal (f x)` THEN
    ASM_SIMP_TAC std_ss [extreal_not_infty, real_normal],
    ALL_TAC] THEN ASM_SIMP_TAC std_ss [normal_real],
   DISCH_TAC] THEN FULL_SIMP_TAC std_ss [] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN UNDISCH_TAC ``s IN subsets Borel`` THEN
  FULL_SIMP_TAC std_ss [borel_eq_halfspace_less, Borel_def] THEN
  RW_TAC std_ss [subsets_def, sigma_def, IN_BIGINTER,
                 GSPECIFICATION, SUBSET_DEF] THEN
  FIRST_X_ASSUM (MP_TAC o Q.SPEC `{s | real_set s IN P}`) THEN
  RW_TAC std_ss [IN_IMAGE, IN_UNIV, GSPECIFICATION] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
  [RW_TAC std_ss [real_set] THEN SIMP_TAC std_ss [GSPECIFICATION] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN SIMP_TAC std_ss [IN_IMAGE, IN_UNIV] THEN
   SIMP_TAC std_ss [EXTENSION, GSPECIFICATION] THEN Q.EXISTS_TAC `a` THEN
   GEN_TAC THEN EQ_TAC THEN RW_TAC std_ss [] THENL
   [ONCE_REWRITE_TAC [GSYM extreal_lt_eq] THEN ASM_SIMP_TAC std_ss [normal_real],
    ALL_TAC] THEN Q.EXISTS_TAC `Normal x` THEN
   ASM_SIMP_TAC std_ss [extreal_lt_eq, extreal_not_infty, real_normal],
   ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN RW_TAC std_ss [sigma_algebra_iff2] THENL
  [SIMP_TAC std_ss [SUBSET_DEF, IN_POW, IN_UNIV],
   SIMP_TAC std_ss [GSPECIFICATION, real_set, NOT_IN_EMPTY] THEN
   ASM_SIMP_TAC std_ss [SET_RULE ``{real x | F} = {}``],
   POP_ASSUM MP_TAC THEN SIMP_TAC std_ss [GSPECIFICATION] THEN DISCH_TAC THEN
   FIRST_X_ASSUM (MP_TAC o Q.SPEC `real_set s'`) THEN ASM_REWRITE_TAC [] THEN
   SIMP_TAC std_ss [real_set, GSPECIFICATION, IN_DIFF, IN_UNIV] THEN
   SIMP_TAC std_ss [DIFF_DEF, IN_UNIV, GSPECIFICATION] THEN
   MATCH_MP_TAC EQ_IMPLIES THEN AP_THM_TAC THEN AP_TERM_TAC THEN
   SIMP_TAC std_ss [EXTENSION, GSPECIFICATION] THEN GEN_TAC THEN EQ_TAC THENL
   [RW_TAC std_ss [] THEN Q.EXISTS_TAC `Normal x` THEN
    POP_ASSUM (MP_TAC o Q.SPEC `Normal x`) THEN
    SIMP_TAC std_ss [real_normal, extreal_not_infty], ALL_TAC] THEN
   RW_TAC std_ss [] THEN ASM_CASES_TAC ``real x' <> real x''`` THEN
   ASM_REWRITE_TAC [] THEN
   ASM_CASES_TAC ``x'' = PosInf`` THEN ASM_REWRITE_TAC [] THEN
   ASM_CASES_TAC ``x'' = NegInf`` THEN ASM_REWRITE_TAC [] THEN
   FULL_SIMP_TAC std_ss [] THEN UNDISCH_TAC ``real x' = real x''`` THEN
   ONCE_REWRITE_TAC [GSYM extreal_11] THEN FULL_SIMP_TAC std_ss [normal_real] THEN
   METIS_TAC [],
   ALL_TAC] THEN
  SIMP_TAC std_ss [GSPECIFICATION] THEN
  FIRST_X_ASSUM (MP_TAC o Q.SPEC `(\i. real_set (A i))`) THEN
  KNOW_TAC ``real_set (BIGUNION {A i | i IN univ(:num)}) =
             BIGUNION {(\i. real_set (A i)) i | i IN univ(:num)}`` THENL
  [ALL_TAC,
   DISC_RW_KILL THEN DISCH_THEN (MATCH_MP_TAC) THEN POP_ASSUM MP_TAC THEN
   RW_TAC std_ss [SUBSET_DEF, IN_IMAGE, IN_UNIV, GSPECIFICATION] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN METIS_TAC []] THEN
  SIMP_TAC std_ss [real_set, EXTENSION, GSPECIFICATION, IN_BIGUNION] THEN
  GEN_TAC THEN EQ_TAC THEN RW_TAC std_ss [] THENL
  [Q.EXISTS_TAC `real_set s'` THEN CONJ_TAC THENL
   [SIMP_TAC std_ss [real_set, GSPECIFICATION] THEN METIS_TAC [],
    ALL_TAC] THEN SIMP_TAC std_ss [IN_UNIV] THEN
   Q.EXISTS_TAC `i` THEN GEN_TAC THEN
   SIMP_TAC std_ss [real_set, GSPECIFICATION] THEN
   METIS_TAC [], ALL_TAC] THEN
  UNDISCH_TAC ``(x:real) IN s'`` THEN ASM_REWRITE_TAC [] THEN
  RW_TAC std_ss [] THEN Q.EXISTS_TAC `x'` THEN
  ASM_REWRITE_TAC [IN_UNIV] THEN Q.EXISTS_TAC `A i` THEN
  METIS_TAC []);

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* ------------------------------------------------------------------------- *)

val BOREL_MEASURABLE_INFINITY = new_axiom ("BOREL_MEASURABLE_INFINITY",
 ``{PosInf} IN subsets Borel /\ {NegInf} IN subsets Borel``);

val IN_MEASURABLE_BOREL_TIMES = store_thm ("IN_MEASURABLE_BOREL_TIMES",
 ``!m f g h.
     measure_space m /\
     f IN measurable (m_space m, measurable_sets m) Borel /\
     g IN measurable (m_space m, measurable_sets m) Borel /\
     (!x. x IN m_space m ==> (h x = f x * g x)) ==>
     h IN measurable (m_space m, measurable_sets m) Borel``,
  RW_TAC std_ss [] THEN
  Q_TAC SUFF_TAC `(\x. f x * g x) IN measurable (m_space m,measurable_sets m) Borel` THENL
  [RW_TAC std_ss [IN_MEASURABLE, space_def] THENL
   [EVAL_TAC THEN SRW_TAC[][IN_DEF,IN_FUNSET], ALL_TAC] THEN
   FIRST_X_ASSUM (MP_TAC o Q.SPEC `s`) THEN ASM_REWRITE_TAC [] THEN
   SIMP_TAC std_ss [INTER_DEF] THEN
   Q_TAC SUFF_TAC `{x | x IN PREIMAGE (\x. f x * g x) s /\ x IN m_space m} =
                   {x | x IN PREIMAGE h s /\ x IN m_space m}` THENL
   [METIS_TAC [], ALL_TAC] THEN
   SIMP_TAC std_ss [EXTENSION, GSPECIFICATION, IN_PREIMAGE] THEN
   ASM_SET_TAC [], ALL_TAC] THEN

  Q_TAC SUFF_TAC `(\x. PosInf) IN measurable (m_space m,measurable_sets m) Borel /\
                  (\x. NegInf) IN measurable (m_space m,measurable_sets m) Borel` THENL
  [STRIP_TAC,
   CONJ_TAC THEN MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST THEN
   METIS_TAC [measure_space_def]] THEN

  ONCE_REWRITE_TAC [METIS [SPACE, m_space_def, measurable_sets_def]
    ``Borel = (m_space (space Borel, subsets Borel, (\x. 0)),
       measurable_sets (space Borel, subsets Borel, (\x. 0)))``] THEN
  Q_TAC SUFF_TAC `(\x. f x * g x) =
                  (\x. if {x | ((f x = PosInf) \/ (f x = NegInf))} x
                       then (\x. if f x = PosInf then PosInf * g x
                                                 else NegInf * g x) x
                       else (\x. Normal (real (f x)) * g x) x)` THENL
  [DISC_RW_KILL,
   SIMP_TAC std_ss [FUN_EQ_THM] THEN GEN_TAC THEN COND_CASES_TAC THENL
   [POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION]) THEN
    SIMP_TAC std_ss [GSPECIFICATION] THEN METIS_TAC [],
    ALL_TAC] THEN
   POP_ASSUM MP_TAC THEN
   GEN_REWR_TAC (LAND_CONV o RAND_CONV) [GSYM SPECIFICATION] THEN
   SIMP_TAC std_ss [GSPECIFICATION] THEN METIS_TAC [normal_real]] THEN

  MATCH_MP_TAC measurable_If THEN
  RW_TAC std_ss [m_space_def, measurable_sets_def, SPACE] THENL
  [ALL_TAC, ALL_TAC,
   Q_TAC SUFF_TAC
   `{x | x IN m_space m /\ {x | (f x = PosInf) \/ (f x = NegInf)} x} =
    PREIMAGE f {x | (x = PosInf) \/ (x = NegInf)} INTER m_space m` THENL
   [DISC_RW_KILL,
    SIMP_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER, IN_PREIMAGE] THEN
    GEN_TAC THEN GEN_REWR_TAC (LAND_CONV o RAND_CONV) [GSYM SPECIFICATION] THEN
    SET_TAC []] THEN
   FULL_SIMP_TAC std_ss [IN_MEASURABLE, space_def, subsets_def] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   ONCE_REWRITE_TAC [SET_RULE ``{x | (x = PosInf) \/ (x = NegInf)} =
                                {PosInf} UNION {NegInf}``] THEN
   MATCH_MP_TAC ALGEBRA_UNION THEN
   METIS_TAC [measure_space_def, sigma_algebra_def,
              BOREL_MEASURABLE_INFINITY]] THENL
  [ALL_TAC,
   ONCE_REWRITE_TAC [METIS [SPACE, m_space_def, measurable_sets_def]
    ``Borel = (m_space (space Borel, subsets Borel, (\x. 0)),
       measurable_sets (space Borel, subsets Borel, (\x. 0)))``] THEN
   Q_TAC SUFF_TAC `(\x. Normal (real (f x)) * g x) =
           (\x. if {x | ((g x = PosInf) \/ (g x = NegInf))} x
                then (\x. if g x = PosInf then Normal (real (f x)) * PosInf
                                          else Normal (real (f x)) * NegInf) x
                else (\x. Normal (real (f x)) * Normal (real (g x))) x)` THENL
   [DISC_RW_KILL,
    SIMP_TAC std_ss [FUN_EQ_THM] THEN GEN_TAC THEN COND_CASES_TAC THENL
    [POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION]) THEN
     SIMP_TAC std_ss [GSPECIFICATION] THEN METIS_TAC [],
     ALL_TAC] THEN
    POP_ASSUM MP_TAC THEN
    GEN_REWR_TAC (LAND_CONV o RAND_CONV) [GSYM SPECIFICATION] THEN
    SIMP_TAC std_ss [GSPECIFICATION] THEN METIS_TAC [normal_real]] THEN
   MATCH_MP_TAC measurable_If THEN
   RW_TAC std_ss [m_space_def, measurable_sets_def, SPACE] THENL
   [ALL_TAC,
    `(\x. 0) IN measurable (m_space m,measurable_sets m) Borel` by
     (MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST THEN
      METIS_TAC [measure_space_def]) THEN
    MATCH_MP_TAC IN_MEASURABLE_BOREL_MUL THEN
    Q.EXISTS_TAC `(\x. Normal (real (f x)))` THEN
    Q.EXISTS_TAC `(\x. Normal (real (g x)))` THEN
    FULL_SIMP_TAC std_ss [measure_space_def, extreal_not_infty] THEN
    ONCE_REWRITE_TAC [METIS [SPACE, m_space_def, measurable_sets_def]
    ``Borel = (m_space (space Borel, subsets Borel, (\x. 0)),
       measurable_sets (space Borel, subsets Borel, (\x. 0)))``] THEN
    CONJ_TAC THENL
    [Q_TAC SUFF_TAC `(\x. Normal (real (f x))) =
      (\x. if {x | (f x = PosInf) \/ (f x = NegInf)} x then (\x. 0) x else f x)` THENL
     [DISC_RW_KILL,
      ABS_TAC THEN COND_CASES_TAC THENL
      [POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION]) THEN
       SIMP_TAC std_ss [GSPECIFICATION] THEN METIS_TAC [real_def, extreal_of_num_def],
       ALL_TAC] THEN
      POP_ASSUM MP_TAC THEN
      GEN_REWR_TAC (LAND_CONV o RAND_CONV) [GSYM SPECIFICATION] THEN
      SIMP_TAC std_ss [GSPECIFICATION] THEN METIS_TAC [normal_real]] THEN
     MATCH_MP_TAC measurable_If THEN
     RW_TAC std_ss [m_space_def, measurable_sets_def, SPACE] THENL
     [ALL_TAC, METIS_TAC [measure_space_def]] THEN
     Q_TAC SUFF_TAC `{x | x IN m_space m /\
                     {x | (f x = PosInf) \/ (f x = NegInf)} x} =
          PREIMAGE f {x | (x = PosInf) \/ (x = NegInf)} INTER m_space m` THENL
     [DISC_RW_KILL,
      SIMP_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER, IN_PREIMAGE] THEN
      GEN_TAC THEN GEN_REWR_TAC (LAND_CONV o RAND_CONV) [GSYM SPECIFICATION] THEN
      SET_TAC []] THEN
     FULL_SIMP_TAC std_ss [IN_MEASURABLE, space_def, subsets_def] THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN
     ONCE_REWRITE_TAC [SET_RULE
     ``{x | (x = PosInf) \/ (x = NegInf)} = {PosInf} UNION {NegInf}``] THEN
     MATCH_MP_TAC ALGEBRA_UNION THEN
     METIS_TAC [measure_space_def, sigma_algebra_def, BOREL_MEASURABLE_INFINITY],
     ALL_TAC] THEN
    Q_TAC SUFF_TAC `(\x. Normal (real (g x))) =
      (\x. if {x | (g x = PosInf) \/ (g x = NegInf)} x then (\x. 0) x else g x)` THENL
     [DISC_RW_KILL,
      ABS_TAC THEN COND_CASES_TAC THENL
      [POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION]) THEN
       SIMP_TAC std_ss [GSPECIFICATION] THEN
       METIS_TAC [real_def, extreal_of_num_def],
       ALL_TAC] THEN
      POP_ASSUM MP_TAC THEN
      GEN_REWR_TAC (LAND_CONV o RAND_CONV) [GSYM SPECIFICATION] THEN
      SIMP_TAC std_ss [GSPECIFICATION] THEN METIS_TAC [normal_real]] THEN
     MATCH_MP_TAC measurable_If THEN
     RW_TAC std_ss [m_space_def, measurable_sets_def, SPACE] THENL
     [ALL_TAC, METIS_TAC [measure_space_def]] THEN
     Q_TAC SUFF_TAC `{x | x IN m_space m /\
                     {x | (g x = PosInf) \/ (g x = NegInf)} x} =
          PREIMAGE g {x | (x = PosInf) \/ (x = NegInf)} INTER m_space m` THENL
     [DISC_RW_KILL,
      SIMP_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER, IN_PREIMAGE] THEN
      GEN_TAC THEN GEN_REWR_TAC (LAND_CONV o RAND_CONV) [GSYM SPECIFICATION] THEN
      SET_TAC []] THEN
     FULL_SIMP_TAC std_ss [IN_MEASURABLE, space_def, subsets_def] THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN
     ONCE_REWRITE_TAC [SET_RULE
     ``{x | (x = PosInf) \/ (x = NegInf)} = {PosInf} UNION {NegInf}``] THEN
     MATCH_MP_TAC ALGEBRA_UNION THEN
     METIS_TAC [measure_space_def, sigma_algebra_def, BOREL_MEASURABLE_INFINITY],

     Q_TAC SUFF_TAC `{x | x IN m_space m /\ {x | (g x = PosInf) \/ (g x = NegInf)} x} =
                  PREIMAGE g {x | (x = PosInf) \/ (x = NegInf)} INTER m_space m` THENL
     [DISC_RW_KILL,
      SIMP_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER, IN_PREIMAGE] THEN
      GEN_TAC THEN GEN_REWR_TAC (LAND_CONV o RAND_CONV) [GSYM SPECIFICATION] THEN
      SET_TAC []] THEN
     FULL_SIMP_TAC std_ss [IN_MEASURABLE, space_def, subsets_def] THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN
     ONCE_REWRITE_TAC [SET_RULE ``{x | (x = PosInf) \/ (x = NegInf)} = {PosInf} UNION {NegInf}``] THEN
     MATCH_MP_TAC ALGEBRA_UNION THEN
     METIS_TAC [measure_space_def, sigma_algebra_def, BOREL_MEASURABLE_INFINITY]] THEN

    ONCE_REWRITE_TAC [METIS [SPACE, m_space_def, measurable_sets_def]
     ``Borel = (m_space (space Borel, subsets Borel, (\x. 0)),
       measurable_sets (space Borel, subsets Borel, (\x. 0)))``] THEN
    Q_TAC SUFF_TAC `(\x. if g x = PosInf then Normal (real (f x)) * PosInf
                         else Normal (real (f x)) * NegInf) =
                    (\x. if (\x. g x = PosInf) x then (\x. Normal (real (f x)) * PosInf) x
                         else (\x. Normal (real (f x)) * NegInf) x)` THENL
    [DISC_RW_KILL, SIMP_TAC std_ss []] THEN
    `(\x. 0) IN measurable (m_space m,measurable_sets m) Borel` by
     (MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST THEN
      METIS_TAC [measure_space_def]) THEN
    MATCH_MP_TAC measurable_If THEN RW_TAC std_ss [] THENL

    [SIMP_TAC std_ss [extreal_mul_def] THEN
     Q_TAC SUFF_TAC `(\x. if real (f x) = 0 then Normal 0
                         else if 0 < real (f x) then PosInf
                         else NegInf) =
                    (\x. if (\x. real (f x) = 0) x then (\x. Normal 0) x
                         else (\x. if 0 < real (f x) then PosInf
                         else NegInf) x)` THENL
     [DISC_RW_KILL, SIMP_TAC std_ss []] THEN MATCH_MP_TAC measurable_If THEN
     RW_TAC std_ss [] THENL
     [ASM_SIMP_TAC std_ss [m_space_def, measurable_sets_def, SPACE, GSYM extreal_of_num_def],
      ALL_TAC,
      SIMP_TAC std_ss [GSYM extreal_11, GSYM extreal_of_num_def] THEN
      Q_TAC SUFF_TAC `{x | x IN m_space m /\ (Normal (real (f x)) = 0)} =
                      PREIMAGE f {x | (x = 0) \/ (x = PosInf) \/ (x = NegInf)} INTER m_space m` THENL
      [DISC_RW_KILL,
       SIMP_TAC std_ss [PREIMAGE_def] THEN
       SIMP_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER] THEN
       GEN_TAC THEN EQ_TAC THEN RW_TAC std_ss [real_def, extreal_of_num_def, real_normal] THEN
       FULL_SIMP_TAC std_ss [GSYM extreal_of_num_def] THEN
       TRY (METIS_TAC [extreal_of_num_def, extreal_11, normal_real])] THEN
      FULL_SIMP_TAC std_ss [IN_MEASURABLE, space_def, subsets_def] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      ONCE_REWRITE_TAC [SET_RULE ``{x | (x = 0) \/ (x = PosInf) \/ (x = NegInf)} =
                                   {0} UNION ({PosInf} UNION {NegInf})``] THEN
      MATCH_MP_TAC ALGEBRA_UNION THEN
      `algebra Borel` by METIS_TAC [sigma_algebra_def, SIGMA_ALGEBRA_BOREL] THEN
      ASM_SIMP_TAC std_ss [BOREL_MEASURABLE_SETS_SING, extreal_of_num_def] THEN
      MATCH_MP_TAC ALGEBRA_UNION THEN ASM_SIMP_TAC std_ss [BOREL_MEASURABLE_INFINITY]] THEN
     SIMP_TAC std_ss [GSYM extreal_11, GSYM extreal_of_num_def] THEN

     Q_TAC SUFF_TAC `(\x. if 0 < real (f x) then PosInf else NegInf) =
                (\x. if (\x. 0 < real (f x)) x then (\x. PosInf) x else (\x. NegInf) x)` THENL
     [DISC_RW_KILL, SIMP_TAC std_ss []] THEN
     MATCH_MP_TAC measurable_If THEN RW_TAC std_ss [] THENL
     [ASM_SIMP_TAC std_ss [m_space_def, measurable_sets_def, SPACE],
      ASM_SIMP_TAC std_ss [m_space_def, measurable_sets_def, SPACE],
      ALL_TAC] THEN
     SIMP_TAC std_ss [GSYM extreal_lt_eq, GSYM extreal_of_num_def] THEN
     Q_TAC SUFF_TAC `{x | x IN m_space m /\ 0 < Normal (real (f x))} =
                      PREIMAGE f {x | 0 < x /\ (x <> PosInf) /\ (x <> NegInf)} INTER m_space m` THENL
     [DISC_RW_KILL,
      SIMP_TAC std_ss [PREIMAGE_def] THEN
      SIMP_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER] THEN
      GEN_TAC THEN EQ_TAC THEN RW_TAC std_ss [real_def, extreal_of_num_def, real_normal] THEN
      FULL_SIMP_TAC std_ss [GSYM extreal_of_num_def, lt_refl] THEN
      TRY (METIS_TAC [extreal_of_num_def, extreal_11, normal_real, extreal_lt_eq])] THEN

     FULL_SIMP_TAC std_ss [IN_MEASURABLE, space_def, subsets_def] THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN
     ONCE_REWRITE_TAC [SET_RULE ``{x | 0 < x /\ x <> PosInf /\ x <> NegInf} =
                                  {x | 0 < x} INTER ((UNIV DIFF {PosInf}) INTER (UNIV DIFF {NegInf}))``] THEN
     MATCH_MP_TAC ALGEBRA_INTER THEN
     `algebra Borel` by METIS_TAC [sigma_algebra_def, SIGMA_ALGEBRA_BOREL] THEN
     ASM_SIMP_TAC std_ss [BOREL_MEASURABLE_SETS_OR, extreal_of_num_def] THEN
     MATCH_MP_TAC ALGEBRA_INTER THEN ASM_SIMP_TAC std_ss [GSYM SPACE_BOREL] THEN
     CONJ_TAC THEN (MATCH_MP_TAC ALGEBRA_DIFF THEN
      ASM_SIMP_TAC std_ss [BOREL_MEASURABLE_INFINITY, ALGEBRA_SPACE]),

     ALL_TAC,
     Q_TAC SUFF_TAC `{x | x IN m_space m /\ (g x = PosInf)} =
                    PREIMAGE g {x | x = PosInf} INTER m_space m` THENL
     [DISC_RW_KILL,
      SIMP_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER, IN_PREIMAGE] THEN
      GEN_TAC THEN GEN_REWR_TAC (LAND_CONV o RAND_CONV) [GSYM SPECIFICATION] THEN
      SET_TAC []] THEN
     FULL_SIMP_TAC std_ss [IN_MEASURABLE, space_def, subsets_def] THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN
     ONCE_REWRITE_TAC [SET_RULE ``{x | x = PosInf} = {PosInf}``] THEN
     SIMP_TAC std_ss [BOREL_MEASURABLE_INFINITY]] THEN

    SIMP_TAC std_ss [extreal_mul_def] THEN
     Q_TAC SUFF_TAC `(\x. if real (f x) = 0 then Normal 0
                         else if 0 < real (f x) then NegInf
                         else PosInf) =
                    (\x. if (\x. real (f x) = 0) x then (\x. Normal 0) x
                         else (\x. if 0 < real (f x) then NegInf
                         else PosInf) x)` THENL
     [DISC_RW_KILL, SIMP_TAC std_ss []] THEN MATCH_MP_TAC measurable_If THEN
     RW_TAC std_ss [] THENL
     [ASM_SIMP_TAC std_ss [m_space_def, measurable_sets_def, SPACE, GSYM extreal_of_num_def],
      ALL_TAC,
      SIMP_TAC std_ss [GSYM extreal_11, GSYM extreal_of_num_def] THEN
      Q_TAC SUFF_TAC `{x | x IN m_space m /\ (Normal (real (f x)) = 0)} =
                      PREIMAGE f {x | (x = 0) \/ (x = PosInf) \/ (x = NegInf)} INTER m_space m` THENL
      [DISC_RW_KILL,
       SIMP_TAC std_ss [PREIMAGE_def] THEN
       SIMP_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER] THEN
       GEN_TAC THEN EQ_TAC THEN RW_TAC std_ss [real_def, extreal_of_num_def, real_normal] THEN
       FULL_SIMP_TAC std_ss [GSYM extreal_of_num_def] THEN
       TRY (METIS_TAC [extreal_of_num_def, extreal_11, normal_real])] THEN
      FULL_SIMP_TAC std_ss [IN_MEASURABLE, space_def, subsets_def] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      ONCE_REWRITE_TAC [SET_RULE ``{x | (x = 0) \/ (x = PosInf) \/ (x = NegInf)} =
                                   {0} UNION ({PosInf} UNION {NegInf})``] THEN
      MATCH_MP_TAC ALGEBRA_UNION THEN
      `algebra Borel` by METIS_TAC [sigma_algebra_def, SIGMA_ALGEBRA_BOREL] THEN
      ASM_SIMP_TAC std_ss [BOREL_MEASURABLE_SETS_SING, extreal_of_num_def] THEN
      MATCH_MP_TAC ALGEBRA_UNION THEN ASM_SIMP_TAC std_ss [BOREL_MEASURABLE_INFINITY]] THEN
     SIMP_TAC std_ss [GSYM extreal_11, GSYM extreal_of_num_def] THEN

     Q_TAC SUFF_TAC `(\x. if 0 < real (f x) then NegInf else PosInf) =
                (\x. if (\x. 0 < real (f x)) x then (\x. NegInf) x else (\x. PosInf) x)` THENL
     [DISC_RW_KILL, SIMP_TAC std_ss []] THEN
     MATCH_MP_TAC measurable_If THEN RW_TAC std_ss [] THENL
     [ASM_SIMP_TAC std_ss [m_space_def, measurable_sets_def, SPACE],
      ASM_SIMP_TAC std_ss [m_space_def, measurable_sets_def, SPACE],
      ALL_TAC] THEN
     SIMP_TAC std_ss [GSYM extreal_lt_eq, GSYM extreal_of_num_def] THEN
     Q_TAC SUFF_TAC `{x | x IN m_space m /\ 0 < Normal (real (f x))} =
                      PREIMAGE f {x | 0 < x /\ (x <> PosInf) /\ (x <> NegInf)} INTER m_space m` THENL
     [DISC_RW_KILL,
      SIMP_TAC std_ss [PREIMAGE_def] THEN
      SIMP_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER] THEN
      GEN_TAC THEN EQ_TAC THEN RW_TAC std_ss [real_def, extreal_of_num_def, real_normal] THEN
      FULL_SIMP_TAC std_ss [GSYM extreal_of_num_def, lt_refl] THEN
      TRY (METIS_TAC [extreal_of_num_def, extreal_11, normal_real, extreal_lt_eq])] THEN

     FULL_SIMP_TAC std_ss [IN_MEASURABLE, space_def, subsets_def] THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN
     ONCE_REWRITE_TAC [SET_RULE
     ``{x | 0 < x /\ x <> PosInf /\ x <> NegInf} =
       {x | 0 < x} INTER ((UNIV DIFF {PosInf}) INTER (UNIV DIFF {NegInf}))``] THEN
     MATCH_MP_TAC ALGEBRA_INTER THEN
     `algebra Borel` by METIS_TAC [sigma_algebra_def, SIGMA_ALGEBRA_BOREL] THEN
     ASM_SIMP_TAC std_ss [BOREL_MEASURABLE_SETS_OR, extreal_of_num_def] THEN
     MATCH_MP_TAC ALGEBRA_INTER THEN ASM_SIMP_TAC std_ss [GSYM SPACE_BOREL] THEN
     CONJ_TAC THEN (MATCH_MP_TAC ALGEBRA_DIFF THEN
      ASM_SIMP_TAC std_ss [BOREL_MEASURABLE_INFINITY, ALGEBRA_SPACE])] THEN

  ONCE_REWRITE_TAC [METIS [SPACE, m_space_def, measurable_sets_def]
    ``Borel = (m_space (space Borel, subsets Borel, (\x. 0)),
       measurable_sets (space Borel, subsets Borel, (\x. 0)))``] THEN
  Q_TAC SUFF_TAC `(\x. if (\x. f x = PosInf) x then (\x. PosInf * g x) x else (\x. NegInf * g x) x) IN
                    measurable (m_space m,measurable_sets m)
                               (m_space (space Borel,subsets Borel,(\x. 0)),
                                measurable_sets (space Borel,subsets Borel,(\x. 0)))` THENL
  [SIMP_TAC std_ss [], ALL_TAC] THEN
  MATCH_MP_TAC measurable_If THEN RW_TAC std_ss [] THENL
  [Q_TAC SUFF_TAC `(\x. PosInf * g x) =
                   (\x. if {x | ((g x = PosInf) \/ (g x = NegInf))} x
                        then (\x. if g x = PosInf then PosInf else NegInf) x
                        else (\x. PosInf * Normal (real (g x))) x)` THENL
   [DISC_RW_KILL,
    ABS_TAC THEN COND_CASES_TAC THENL
    [POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION]) THEN
     SIMP_TAC std_ss [GSPECIFICATION] THEN METIS_TAC [extreal_mul_def],
     ALL_TAC] THEN
    POP_ASSUM MP_TAC THEN GEN_REWR_TAC (LAND_CONV o RAND_CONV) [GSYM SPECIFICATION] THEN
    SIMP_TAC std_ss [GSPECIFICATION] THEN
    METIS_TAC [normal_real]] THEN
   MATCH_MP_TAC measurable_If THEN RW_TAC std_ss [] THENL
   [Q_TAC SUFF_TAC `(\x. if g x = PosInf then PosInf else NegInf) =
               (\x. if (\x. g x = PosInf) x then (\x. PosInf) x else (\x. NegInf) x)` THENL
    [DISC_RW_KILL, SIMP_TAC std_ss []] THEN
    MATCH_MP_TAC measurable_If THEN RW_TAC std_ss [] THENL
    [ASM_SIMP_TAC std_ss [m_space_def, measurable_sets_def, SPACE],
     ASM_SIMP_TAC std_ss [m_space_def, measurable_sets_def, SPACE],
     ALL_TAC] THEN
    Q_TAC SUFF_TAC `{x | x IN m_space m /\ (g x = PosInf)} =
                    PREIMAGE g {x | x = PosInf} INTER m_space m` THENL
    [DISC_RW_KILL,
     SIMP_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER, IN_PREIMAGE] THEN
     GEN_TAC THEN GEN_REWR_TAC (LAND_CONV o RAND_CONV) [GSYM SPECIFICATION] THEN
     SET_TAC []] THEN
    FULL_SIMP_TAC std_ss [IN_MEASURABLE, space_def, subsets_def] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ONCE_REWRITE_TAC [SET_RULE ``{x | x = PosInf} = {PosInf}``] THEN
    SIMP_TAC std_ss [BOREL_MEASURABLE_INFINITY],
    ALL_TAC,
    Q_TAC SUFF_TAC `{x | x IN m_space m /\ {x | (g x = PosInf) \/ (g x = NegInf)} x} =
                   PREIMAGE g {x | (x = PosInf) \/ (x = NegInf)} INTER m_space m` THENL
    [DISC_RW_KILL,
     SIMP_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER, IN_PREIMAGE] THEN
     GEN_TAC THEN GEN_REWR_TAC (LAND_CONV o RAND_CONV) [GSYM SPECIFICATION] THEN
     SET_TAC []] THEN
    FULL_SIMP_TAC std_ss [IN_MEASURABLE, space_def, subsets_def] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ONCE_REWRITE_TAC [SET_RULE
    ``{x | (x = PosInf) \/ (x = NegInf)} = {PosInf} UNION {NegInf}``] THEN
    MATCH_MP_TAC ALGEBRA_UNION THEN
    METIS_TAC [measure_space_def, sigma_algebra_def, BOREL_MEASURABLE_INFINITY]] THEN

   `(\x. 0) IN measurable (m_space m,measurable_sets m) Borel` by
     (MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST THEN
      METIS_TAC [measure_space_def]) THEN
   SIMP_TAC std_ss [extreal_mul_def] THEN
   Q_TAC SUFF_TAC `(\x. if real (g x) = 0 then Normal 0
                        else if 0 < real (g x) then PosInf
                        else NegInf) =
                   (\x. if (\x. real (g x) = 0) x then (\x. Normal 0) x
                        else (\x. if 0 < real (g x) then PosInf
                        else NegInf) x)` THENL
   [DISC_RW_KILL, SIMP_TAC std_ss []] THEN MATCH_MP_TAC measurable_If THEN
   RW_TAC std_ss [] THENL
   [ASM_SIMP_TAC std_ss [m_space_def, measurable_sets_def, SPACE, GSYM extreal_of_num_def],
    ALL_TAC,
    SIMP_TAC std_ss [GSYM extreal_11, GSYM extreal_of_num_def] THEN
    Q_TAC SUFF_TAC `{x | x IN m_space m /\ (Normal (real (g x)) = 0)} =
                    PREIMAGE g {x | (x = 0) \/ (x = PosInf) \/ (x = NegInf)} INTER m_space m` THENL
    [DISC_RW_KILL,
     SIMP_TAC std_ss [PREIMAGE_def] THEN
     SIMP_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER] THEN
     GEN_TAC THEN EQ_TAC THEN RW_TAC std_ss [real_def, extreal_of_num_def, real_normal] THEN
     FULL_SIMP_TAC std_ss [GSYM extreal_of_num_def] THEN
     TRY (METIS_TAC [extreal_of_num_def, extreal_11, normal_real])] THEN
    FULL_SIMP_TAC std_ss [IN_MEASURABLE, space_def, subsets_def] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ONCE_REWRITE_TAC [SET_RULE ``{x | (x = 0) \/ (x = PosInf) \/ (x = NegInf)} =
                                 {0} UNION ({PosInf} UNION {NegInf})``] THEN
    MATCH_MP_TAC ALGEBRA_UNION THEN
    `algebra Borel` by METIS_TAC [sigma_algebra_def, SIGMA_ALGEBRA_BOREL] THEN
    ASM_SIMP_TAC std_ss [BOREL_MEASURABLE_SETS_SING, extreal_of_num_def] THEN
    MATCH_MP_TAC ALGEBRA_UNION THEN ASM_SIMP_TAC std_ss [BOREL_MEASURABLE_INFINITY]] THEN

   Q_TAC SUFF_TAC `(\x. if 0 < real (g x) then PosInf else NegInf) =
              (\x. if (\x. 0 < real (g x)) x then (\x. PosInf) x else (\x. NegInf) x)` THENL
   [DISC_RW_KILL, SIMP_TAC std_ss []] THEN
   MATCH_MP_TAC measurable_If THEN RW_TAC std_ss [] THENL
   [ASM_SIMP_TAC std_ss [m_space_def, measurable_sets_def, SPACE],
    ASM_SIMP_TAC std_ss [m_space_def, measurable_sets_def, SPACE],
    ALL_TAC] THEN
   SIMP_TAC std_ss [GSYM extreal_lt_eq, GSYM extreal_of_num_def] THEN
   Q_TAC SUFF_TAC `{x | x IN m_space m /\ 0 < Normal (real (g x))} =
                    PREIMAGE g {x | 0 < x /\ (x <> PosInf) /\ (x <> NegInf)} INTER m_space m` THENL
   [DISC_RW_KILL,
    SIMP_TAC std_ss [PREIMAGE_def] THEN
    SIMP_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER] THEN
    GEN_TAC THEN EQ_TAC THEN RW_TAC std_ss [real_def, extreal_of_num_def, real_normal] THEN
    FULL_SIMP_TAC std_ss [GSYM extreal_of_num_def, lt_refl] THEN
    TRY (METIS_TAC [extreal_of_num_def, extreal_11, normal_real, extreal_lt_eq])] THEN

   FULL_SIMP_TAC std_ss [IN_MEASURABLE, space_def, subsets_def] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   ONCE_REWRITE_TAC [SET_RULE
   ``{x | 0 < x /\ x <> PosInf /\ x <> NegInf} =
     {x | 0 < x} INTER ((UNIV DIFF {PosInf}) INTER (UNIV DIFF {NegInf}))``] THEN
   MATCH_MP_TAC ALGEBRA_INTER THEN
   `algebra Borel` by METIS_TAC [sigma_algebra_def, SIGMA_ALGEBRA_BOREL] THEN
   ASM_SIMP_TAC std_ss [BOREL_MEASURABLE_SETS_OR, extreal_of_num_def] THEN
   MATCH_MP_TAC ALGEBRA_INTER THEN ASM_SIMP_TAC std_ss [GSYM SPACE_BOREL] THEN
   CONJ_TAC THEN (MATCH_MP_TAC ALGEBRA_DIFF THEN
    ASM_SIMP_TAC std_ss [BOREL_MEASURABLE_INFINITY, ALGEBRA_SPACE]),
   ALL_TAC,
   Q_TAC SUFF_TAC `{x | x IN m_space m /\ (f x = PosInf)} =
                    PREIMAGE f {x | x = PosInf} INTER m_space m` THENL
   [DISC_RW_KILL,
    SIMP_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER, IN_PREIMAGE] THEN
    GEN_TAC THEN GEN_REWR_TAC (LAND_CONV o RAND_CONV) [GSYM SPECIFICATION] THEN
    SET_TAC []] THEN
   FULL_SIMP_TAC std_ss [IN_MEASURABLE, space_def, subsets_def] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   ONCE_REWRITE_TAC [SET_RULE ``{x | x = PosInf} = {PosInf}``] THEN
   SIMP_TAC std_ss [BOREL_MEASURABLE_INFINITY]] THEN

  Q_TAC SUFF_TAC `(\x. NegInf * g x) =
                  (\x. if {x | ((g x = PosInf) \/ (g x = NegInf))} x
                       then (\x. if g x = PosInf then NegInf else PosInf) x
                       else (\x. NegInf * Normal (real (g x))) x)` THENL
   [DISC_RW_KILL,
    ABS_TAC THEN COND_CASES_TAC THENL
    [POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION]) THEN
     SIMP_TAC std_ss [GSPECIFICATION] THEN METIS_TAC [extreal_mul_def],
     ALL_TAC] THEN
    POP_ASSUM MP_TAC THEN GEN_REWR_TAC (LAND_CONV o RAND_CONV) [GSYM SPECIFICATION] THEN
    SIMP_TAC std_ss [GSPECIFICATION] THEN
    METIS_TAC [normal_real]] THEN
   MATCH_MP_TAC measurable_If THEN RW_TAC std_ss [] THENL
   [Q_TAC SUFF_TAC `(\x. if g x = PosInf then NegInf else PosInf) =
               (\x. if (\x. g x = PosInf) x then (\x. NegInf) x else (\x. PosInf) x)` THENL
    [DISC_RW_KILL, SIMP_TAC std_ss []] THEN
    MATCH_MP_TAC measurable_If THEN RW_TAC std_ss [] THENL
    [ASM_SIMP_TAC std_ss [m_space_def, measurable_sets_def, SPACE],
     ASM_SIMP_TAC std_ss [m_space_def, measurable_sets_def, SPACE],
     ALL_TAC] THEN
    Q_TAC SUFF_TAC `{x | x IN m_space m /\ (g x = PosInf)} =
                    PREIMAGE g {x | x = PosInf} INTER m_space m` THENL
    [DISC_RW_KILL,
     SIMP_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER, IN_PREIMAGE] THEN
     GEN_TAC THEN GEN_REWR_TAC (LAND_CONV o RAND_CONV) [GSYM SPECIFICATION] THEN
     SET_TAC []] THEN
    FULL_SIMP_TAC std_ss [IN_MEASURABLE, space_def, subsets_def] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ONCE_REWRITE_TAC [SET_RULE ``{x | x = PosInf} = {PosInf}``] THEN
    SIMP_TAC std_ss [BOREL_MEASURABLE_INFINITY],
    ALL_TAC,
    Q_TAC SUFF_TAC `{x | x IN m_space m /\ {x | (g x = PosInf) \/ (g x = NegInf)} x} =
                   PREIMAGE g {x | (x = PosInf) \/ (x = NegInf)} INTER m_space m` THENL
    [DISC_RW_KILL,
     SIMP_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER, IN_PREIMAGE] THEN
     GEN_TAC THEN GEN_REWR_TAC (LAND_CONV o RAND_CONV) [GSYM SPECIFICATION] THEN
     SET_TAC []] THEN
    FULL_SIMP_TAC std_ss [IN_MEASURABLE, space_def, subsets_def] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ONCE_REWRITE_TAC [SET_RULE
    ``{x | (x = PosInf) \/ (x = NegInf)} = {PosInf} UNION {NegInf}``] THEN
    MATCH_MP_TAC ALGEBRA_UNION THEN
    METIS_TAC [measure_space_def, sigma_algebra_def, BOREL_MEASURABLE_INFINITY]] THEN

    `(\x. 0) IN measurable (m_space m,measurable_sets m) Borel` by
     (MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST THEN
      METIS_TAC [measure_space_def]) THEN
   SIMP_TAC std_ss [extreal_mul_def] THEN
   Q_TAC SUFF_TAC `(\x. if real (g x) = 0 then Normal 0
                        else if 0 < real (g x) then NegInf
                        else PosInf) =
                   (\x. if (\x. real (g x) = 0) x then (\x. Normal 0) x
                        else (\x. if 0 < real (g x) then NegInf
                        else PosInf) x)` THENL
   [DISC_RW_KILL, SIMP_TAC std_ss []] THEN MATCH_MP_TAC measurable_If THEN
   RW_TAC std_ss [] THENL
   [ASM_SIMP_TAC std_ss [m_space_def, measurable_sets_def, SPACE, GSYM extreal_of_num_def],
    ALL_TAC,
    SIMP_TAC std_ss [GSYM extreal_11, GSYM extreal_of_num_def] THEN
    Q_TAC SUFF_TAC `{x | x IN m_space m /\ (Normal (real (g x)) = 0)} =
                    PREIMAGE g {x | (x = 0) \/ (x = PosInf) \/ (x = NegInf)} INTER m_space m` THENL
    [DISC_RW_KILL,
     SIMP_TAC std_ss [PREIMAGE_def] THEN
     SIMP_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER] THEN
     GEN_TAC THEN EQ_TAC THEN RW_TAC std_ss [real_def, extreal_of_num_def, real_normal] THEN
     FULL_SIMP_TAC std_ss [GSYM extreal_of_num_def] THEN
     TRY (METIS_TAC [extreal_of_num_def, extreal_11, normal_real])] THEN
    FULL_SIMP_TAC std_ss [IN_MEASURABLE, space_def, subsets_def] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ONCE_REWRITE_TAC [SET_RULE ``{x | (x = 0) \/ (x = PosInf) \/ (x = NegInf)} =
                                 {0} UNION ({PosInf} UNION {NegInf})``] THEN
    MATCH_MP_TAC ALGEBRA_UNION THEN
    `algebra Borel` by METIS_TAC [sigma_algebra_def, SIGMA_ALGEBRA_BOREL] THEN
    ASM_SIMP_TAC std_ss [BOREL_MEASURABLE_SETS_SING, extreal_of_num_def] THEN
    MATCH_MP_TAC ALGEBRA_UNION THEN ASM_SIMP_TAC std_ss [BOREL_MEASURABLE_INFINITY]] THEN

   Q_TAC SUFF_TAC `(\x. if 0 < real (g x) then NegInf else PosInf) =
              (\x. if (\x. 0 < real (g x)) x then (\x. NegInf) x else (\x. PosInf) x)` THENL
   [DISC_RW_KILL, SIMP_TAC std_ss []] THEN
   MATCH_MP_TAC measurable_If THEN RW_TAC std_ss [] THENL
   [ASM_SIMP_TAC std_ss [m_space_def, measurable_sets_def, SPACE],
    ASM_SIMP_TAC std_ss [m_space_def, measurable_sets_def, SPACE],
    ALL_TAC] THEN
   SIMP_TAC std_ss [GSYM extreal_lt_eq, GSYM extreal_of_num_def] THEN
   Q_TAC SUFF_TAC `{x | x IN m_space m /\ 0 < Normal (real (g x))} =
                    PREIMAGE g {x | 0 < x /\ (x <> PosInf) /\ (x <> NegInf)}
                    INTER m_space m` THENL
   [DISC_RW_KILL,
    SIMP_TAC std_ss [PREIMAGE_def] THEN
    SIMP_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER] THEN
    GEN_TAC THEN EQ_TAC THEN
    RW_TAC std_ss [real_def, extreal_of_num_def, real_normal] THEN
    FULL_SIMP_TAC std_ss [GSYM extreal_of_num_def, lt_refl] THEN
    TRY (METIS_TAC [extreal_of_num_def, extreal_11, normal_real, extreal_lt_eq])]
   THEN FULL_SIMP_TAC std_ss [IN_MEASURABLE, space_def, subsets_def] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   ONCE_REWRITE_TAC [SET_RULE
    ``{x | 0 < x /\ x <> PosInf /\ x <> NegInf} =
      {x | 0 < x} INTER ((UNIV DIFF {PosInf}) INTER (UNIV DIFF {NegInf}))``] THEN
   MATCH_MP_TAC ALGEBRA_INTER THEN
   `algebra Borel` by METIS_TAC [sigma_algebra_def, SIGMA_ALGEBRA_BOREL] THEN
   ASM_SIMP_TAC std_ss [BOREL_MEASURABLE_SETS_OR, extreal_of_num_def] THEN
   MATCH_MP_TAC ALGEBRA_INTER THEN ASM_SIMP_TAC std_ss [GSYM SPACE_BOREL] THEN
   CONJ_TAC THEN (MATCH_MP_TAC ALGEBRA_DIFF THEN
    ASM_SIMP_TAC std_ss [BOREL_MEASURABLE_INFINITY, ALGEBRA_SPACE]));

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* ------------------------------------------------------------------------- *)

val indicator_fn_pos_le = store_thm ("indicator_fn_pos_le",
  ``!s x. 0 <= indicator_fn s x``,
  RW_TAC std_ss [indicator_fn_def] THEN
  SIMP_TAC real_ss [le_refl, extreal_of_num_def, extreal_le_def]);

val absolutely_integrable_on_indicator = store_thm
  ("absolutely_integrable_on_indicator",
  ``!A X. indicator A absolutely_integrable_on X =
          indicator A integrable_on X``,
  REPEAT GEN_TAC THEN REWRITE_TAC [absolutely_integrable_on] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
  KNOW_TAC ``!x. abs(indicator A x) = indicator A x`` THENL
  [ALL_TAC, DISCH_TAC THEN FULL_SIMP_TAC std_ss [] THEN METIS_TAC [ETA_AX]] THEN
  RW_TAC real_ss [indicator]);

val has_integral_indicator_UNIV = store_thm ("has_integral_indicator_UNIV",
 ``!s A x. (indicator (s INTER A) has_integral x) UNIV =
           (indicator s has_integral x) A``,
  KNOW_TAC ``!s A. (\x. if x IN A then indicator s x else 0) = indicator (s INTER A)`` THENL
  [SET_TAC [indicator], ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN DISCH_TAC] THEN
  RW_TAC std_ss [HAS_INTEGRAL_RESTRICT_UNIV] THEN METIS_TAC [ETA_AX]);

val integral_indicator_UNIV = store_thm ("integral_indicator_UNIV",
  ``!s A. integral UNIV (indicator (s INTER A)) =
          integral A (indicator s)``,
  REWRITE_TAC [integral] THEN REPEAT STRIP_TAC THEN AP_TERM_TAC THEN
  ABS_TAC THEN METIS_TAC [has_integral_indicator_UNIV]);

val integrable_indicator_UNIV = store_thm ("integrable_indicator_UNIV",
  ``!s A. (indicator (s INTER A)) integrable_on UNIV =
          (indicator s) integrable_on A``,
  RW_TAC std_ss [integrable_on] THEN AP_TERM_TAC THEN
  ABS_TAC THEN METIS_TAC [has_integral_indicator_UNIV]);

val MEASURE_HOLLIGHT_EQ_ISABELLE = store_thm ("MEASURE_HOLLIGHT_EQ_ISABELLE",
  ``!A. integral A (\x. 1) = integral univ(:real) (indicator A)``,
  ONCE_REWRITE_TAC [METIS [SET_RULE ``A = A INTER A``]
   ``indicator A = indicator (A INTER A)``] THEN
  SIMP_TAC std_ss [integral_indicator_UNIV] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC INTEGRAL_EQ THEN SIMP_TAC std_ss [indicator]);

(* ------------------------------------------------------------------------- *)
(* Standard Cubes                                                            *)
(* ------------------------------------------------------------------------- *)

val _ = hide "line";

val line = new_definition ("line",
  ``line n = {x:real| -&n <= x /\ x <= &n}``);

val borel_line = store_thm ("borel_line",
  ``!n. line n IN subsets borel``,
  RW_TAC std_ss [line] THEN MATCH_MP_TAC borel_closed THEN
  SIMP_TAC std_ss [GSYM interval, CLOSED_INTERVAL]);

val line_closed = store_thm ("line_closed",
  ``!n. closed (line n)``,
  RW_TAC std_ss [GSYM interval, line, CLOSED_INTERVAL]);

val line_subset = store_thm ("line_subset",
  ``!n N. n <= N ==> line n SUBSET line N``,
  FULL_SIMP_TAC std_ss [line, SUBSET_DEF, GSPECIFICATION] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THENL
  [EXISTS_TAC ``-&n:real`` THEN ASM_SIMP_TAC real_ss [],
   EXISTS_TAC ``&n:real`` THEN ASM_SIMP_TAC real_ss []]);

val line_subset_iff = store_thm ("line_subset_iff",
  ``!n N. line n SUBSET line N = n <= N``,
  REPEAT GEN_TAC THEN EQ_TAC THENL
  [ALL_TAC, REWRITE_TAC [line_subset]] THEN
  SIMP_TAC std_ss [line, SUBSET_DEF, GSPECIFICATION] THEN
  DISCH_THEN (MP_TAC o SPEC ``&n:real``) THEN
  KNOW_TAC ``-&n <= &n:real /\ &n <= &n:real`` THENL
  [SIMP_TAC std_ss [REAL_LE_REFL] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC ``0:real`` THEN
   GEN_REWR_TAC (LAND_CONV o RAND_CONV) [GSYM REAL_NEG_0] THEN
   SIMP_TAC std_ss [REAL_LE_NEG, REAL_POS], ALL_TAC] THEN
  DISC_RW_KILL THEN SIMP_TAC real_ss []);

val ball_subset_line = store_thm ("ball_subset_line",
  ``!n. ball (0,&n) SUBSET line n``,
  GEN_TAC THEN SIMP_TAC std_ss [ball, line, SUBSET_DEF, GSPECIFICATION] THEN
  GEN_TAC THEN SIMP_TAC std_ss [DIST_0] THEN REAL_ARITH_TAC);

val mem_big_line = store_thm ("mem_big_line",
 ``!x. ?n. x IN line n``,
 GEN_TAC THEN MP_TAC (ISPEC ``x:real`` SIMP_REAL_ARCH) THEN
 STRIP_TAC THEN SIMP_TAC std_ss [line, GSPECIFICATION] THEN
 ASM_CASES_TAC ``0 <= x:real`` THENL
 [EXISTS_TAC ``n:num`` THEN ASM_REAL_ARITH_TAC, ALL_TAC] THEN
 MP_TAC (ISPEC ``-x:real`` SIMP_REAL_ARCH) THEN STRIP_TAC THEN
 EXISTS_TAC ``n':num`` THEN ASM_REAL_ARITH_TAC);

val line_subset_Suc = store_thm ("line_subset_Suc",
  ``!n. line n SUBSET line (SUC n)``,
  GEN_TAC THEN MATCH_MP_TAC line_subset THEN ARITH_TAC);

val has_integral_interval_cube = store_thm ("has_integral_interval_cube",
  ``!a b n. (indicator (interval [a,b]) has_integral
              content (interval [a,b] INTER (line n))) (line n)``,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [GSYM has_integral_indicator_UNIV] THEN
  SIMP_TAC std_ss [indicator, HAS_INTEGRAL_RESTRICT_UNIV] THEN
  SIMP_TAC std_ss [line, GSYM interval, INTER_INTERVAL] THEN
  ONCE_REWRITE_TAC [REAL_ARITH ``content (interval [(max a (-&n),min b (&n))]) =
                        content (interval [(max a (-&n),min b (&n))]) * 1``] THEN
  METIS_TAC [HAS_INTEGRAL_CONST]);

(* ------------------------------------------------------------------------- *)
(* Lebesgue measure                                                          *)
(* ------------------------------------------------------------------------- *)

val _ = hide "lebesgue";

(* This is based on non-standard "gauge integral" method. Instead, I use
   Caratheodory's extension theorem. --Chun Tian

   The type is ``:real m_space``, so is lborel. Is this enough?
 *)
val lebesgue = new_definition ("lebesgue",
  ``lebesgue = (univ(:real), {A | !n. (indicator A) integrable_on (line n)},
                (\A. sup {Normal (integral (line n) (indicator A)) | n IN UNIV}))``);

val space_lebesgue = store_thm ("space_lebesgue",
  ``m_space lebesgue = UNIV``,
  SIMP_TAC std_ss [lebesgue, m_space_def]);

val lebesgueI = store_thm ("lebesgueI",
  ``!A. (!n. indicator A integrable_on line n) ==> A IN measurable_sets lebesgue``,
  SIMP_TAC std_ss [lebesgue, measurable_sets_def] THEN SET_TAC []);

val LIMSEQ_indicator_UN = store_thm ("LIMSEQ_indicator_UN",
  ``!A x. ((\k. indicator (BIGUNION {(A:num->real->bool) i | i < k}) x) -->
           (indicator (BIGUNION {A i | i IN UNIV}) x)) sequentially``,
  REPEAT GEN_TAC THEN ASM_CASES_TAC ``?i. x IN (A:num->real->bool) i`` THENL
  [ALL_TAC, FULL_SIMP_TAC std_ss [indicator, IN_BIGUNION] THEN
   SIMP_TAC std_ss [GSPECIFICATION, IN_UNIV] THEN
   KNOW_TAC ``~(?s. x IN s /\ ?i. s = (A:num->real->bool) i)`` THENL
   [METIS_TAC [], DISCH_TAC] THEN
   KNOW_TAC ``!k. ~(?s. x IN s /\ ?i. (s = (A:num->real->bool) i) /\ i < k)`` THENL
   [METIS_TAC [], DISCH_TAC] THEN ASM_SIMP_TAC std_ss [LIM_CONST]] THEN
  FULL_SIMP_TAC std_ss [] THEN
  KNOW_TAC ``!k. indicator (BIGUNION {(A:num->real->bool) j | j < k + SUC i}) x = 1`` THENL
  [RW_TAC real_ss [indicator, GSPECIFICATION, IN_BIGUNION] THEN
   UNDISCH_TAC ``~?s. x IN s /\ ?j. (s = (A:num->real->bool) j) /\ j < k + SUC i`` THEN
   SIMP_TAC std_ss [] THEN EXISTS_TAC ``(A:num->real->bool) i`` THEN
   ASM_SIMP_TAC std_ss [] THEN EXISTS_TAC  ``i:num`` THEN ASM_SIMP_TAC std_ss [] THEN
   ARITH_TAC, DISCH_TAC] THEN
  KNOW_TAC ``indicator (BIGUNION {(A:num->real->bool) i | i IN univ(:num)}) x = 1`` THENL
  [RW_TAC real_ss [indicator, GSPECIFICATION, IN_BIGUNION] THEN
   POP_ASSUM MP_TAC THEN SIMP_TAC std_ss [IN_UNIV] THEN METIS_TAC [], DISCH_TAC] THEN
  MATCH_MP_TAC SEQ_OFFSET_REV THEN EXISTS_TAC ``SUC i`` THEN
  ASM_SIMP_TAC std_ss [LIM_CONST]);

val sigma_algebra_lebesgue = store_thm ("sigma_algebra_lebesgue",
  ``sigma_algebra (UNIV, {A | !n. (indicator A) integrable_on (line n)})``,
  RW_TAC std_ss [sigma_algebra_iff2] THENL
  [REWRITE_TAC [POW_DEF] THEN SET_TAC [],
   SIMP_TAC std_ss [GSPECIFICATION] THEN KNOW_TAC ``indicator {} = (\x. 0)`` THENL
   [SET_TAC [indicator], DISCH_TAC THEN ASM_REWRITE_TAC []] THEN
   SIMP_TAC std_ss [INTEGRABLE_0],
   FULL_SIMP_TAC std_ss [GSPECIFICATION] THEN
   KNOW_TAC ``indicator (univ(:real) DIFF s) = (\x. 1 - indicator s x)`` THENL
   [SIMP_TAC std_ss [indicator] THEN ABS_TAC THEN
    SIMP_TAC std_ss [IN_DIFF, IN_UNIV] THEN COND_CASES_TAC THEN
    FULL_SIMP_TAC real_ss [], DISCH_TAC THEN ASM_REWRITE_TAC []] THEN
   ONCE_REWRITE_TAC [METIS [] ``(\x. 1 - indicator s x) =
                   (\x. (\x. 1) x - (\x. indicator s x) x)``] THEN
   GEN_TAC THEN MATCH_MP_TAC INTEGRABLE_SUB THEN CONJ_TAC THENL
   [SIMP_TAC std_ss [line, GSYM interval, INTEGRABLE_CONST],
    METIS_TAC [ETA_AX]],
   ALL_TAC] THEN
  FULL_SIMP_TAC std_ss [GSPECIFICATION] THEN
  KNOW_TAC ``!k n. indicator (BIGUNION {(A:num->real->bool) i | i < k})
              integrable_on (line n)`` THENL
  [Induct_on `k` THENL
   [SIMP_TAC std_ss [LT] THEN REWRITE_TAC [SET_RULE ``BIGUNION {A i | i | F} = {}``] THEN
    KNOW_TAC ``indicator {} = (\x. 0)`` THENL [SET_TAC [indicator], DISCH_TAC THEN ASM_REWRITE_TAC []] THEN
    SIMP_TAC std_ss [INTEGRABLE_0], ALL_TAC] THEN
   KNOW_TAC ``BIGUNION {A i | i < SUC k} =
              BIGUNION {(A:num->real->bool) i | i < k} UNION A k`` THENL
   [SIMP_TAC std_ss [ADD1, ARITH_PROVE ``i < SUC k = (i < k \/ (i = k))``] THEN
    SET_TAC [], DISCH_TAC THEN ASM_REWRITE_TAC []] THEN
   KNOW_TAC ``indicator (BIGUNION {(A:num->real->bool) i | i < k} UNION A k) =
              (\x. max (indicator (BIGUNION {A i | i < k}) x) (indicator (A k) x))`` THENL
   [SIMP_TAC std_ss [FUN_EQ_THM] THEN GEN_TAC THEN
    SIMP_TAC std_ss [max_def, indicator] THEN
    REPEAT COND_CASES_TAC THEN FULL_SIMP_TAC std_ss [IN_UNION] THEN
    POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN FULL_SIMP_TAC real_ss [],
    DISCH_TAC] THEN
   REWRITE_TAC [GSYM absolutely_integrable_on_indicator] THEN GEN_TAC THEN
   ASM_SIMP_TAC std_ss [] THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_MAX THEN
   ASM_SIMP_TAC std_ss [absolutely_integrable_on_indicator] THEN
   FULL_SIMP_TAC std_ss [SUBSET_DEF, GSPECIFICATION, IN_IMAGE, IN_UNIV] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN METIS_TAC [], DISCH_TAC] THEN GEN_TAC THEN
  MP_TAC (ISPECL [``(\k. indicator (BIGUNION {(A:num->real->bool) i | i < k}))``,
                  ``indicator (BIGUNION {(A:num->real->bool) i | i IN univ(:num)})``,
                  ``(\x:real. 1:real)``, ``line n``] DOMINATED_CONVERGENCE) THEN
KNOW_TAC ``(!k.
    (\k. indicator (BIGUNION {(A:num->real->bool) i | i < k})) k integrable_on line n) /\
 (\x. 1) integrable_on line n /\
 (!k x.
    x IN line n ==>
    abs ((\k. indicator (BIGUNION {A i | i < k})) k x) <= (\x. 1) x) /\
 (!x.
    x IN line n ==>
    ((\k. (\k. indicator (BIGUNION {A i | i < k})) k x) -->
     indicator (BIGUNION {A i | i IN univ(:num)}) x) sequentially)`` THENL
 [ALL_TAC, METIS_TAC []] THEN REPEAT CONJ_TAC THENL
[FULL_SIMP_TAC std_ss [],
 SIMP_TAC std_ss [line, GSYM interval, INTEGRABLE_CONST],
 SIMP_TAC std_ss [DROP_INDICATOR_ABS_LE_1],
 METIS_TAC [LIMSEQ_indicator_UN]]);

val sets_lebesgue = store_thm ("sets_lebesgue",
  ``measurable_sets lebesgue = {A | !n. (indicator A) integrable_on (line n)}``,
  SIMP_TAC std_ss [lebesgue, measurable_sets_def]);

val lebesgueD = store_thm ("lebesgueD",
  ``!A n. A IN measurable_sets lebesgue ==>
          indicator A integrable_on line n``,
SIMP_TAC std_ss [sets_lebesgue, GSPECIFICATION]);

val measure_lebesgue = store_thm ("measure_lebesgue",
  ``measure lebesgue = (\A. sup { Normal (integral (line n) (indicator A)) | n IN UNIV})``,
SIMP_TAC std_ss [measure_def, lebesgue]);

val indicator_empty = store_thm ("indicator_empty",
  ``indicator {} = (\x. 0)``,
SET_TAC [indicator]);

val INTEGRAL_COMPONENT_LE = store_thm ("INTEGRAL_COMPONENT_LE",
 ``!f:real->real g:real->real s.
        f integrable_on s /\ g integrable_on s /\
        (!x. x IN s ==> (f x) <= (g x))
        ==> (integral s f) <= (integral s g)``,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_INTEGRAL_COMPONENT_LE THEN
  ASM_MESON_TAC[INTEGRABLE_INTEGRAL]);

val positive_lebesgue = store_thm ("positive_lebesgue",
  ``positive lebesgue``,
  SIMP_TAC std_ss [lebesgue, positive_def, sets_lebesgue, measure_lebesgue] THEN
  SIMP_TAC std_ss [indicator_empty, IN_UNIV, INTEGRAL_0, extreal_of_num_def] THEN
   REWRITE_TAC [SET_RULE ``{Normal 0 | n | T} = {Normal 0}``, sup_sing] THEN
  RW_TAC std_ss [] THEN MATCH_MP_TAC le_sup_imp THEN
  ONCE_REWRITE_TAC [GSYM SPECIFICATION] THEN SIMP_TAC std_ss [GSPECIFICATION] THEN
  EXISTS_TAC ``0:num`` THEN SIMP_TAC std_ss [extreal_11, line, GSYM interval] THEN
  SIMP_TAC std_ss [REAL_NEG_0, INTEGRAL_REFL]);

val suminf_ereal_eq_SUP = store_thm ("suminf_ereal_eq_SUP",
  ``!f. (!i:num. 0:extreal <= f i) ==>
      (suminf (\x. f x) = sup {SIGMA (\i. f i) (count n) | n IN UNIV})``,
  RW_TAC std_ss [ext_suminf_def, IMAGE_DEF]);

val SUP_commute = store_thm ("SUP_commute",
  ``!f. sup {sup {f i j | j IN univ(:num)} | i IN univ(:num)} =
        sup {sup {f i j | i IN univ(:num)} | j IN univ(:num)}``,
  RW_TAC std_ss [sup_eq] THENL
  [POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION]) THEN
   RW_TAC std_ss [GSPECIFICATION] THEN SIMP_TAC std_ss [sup_le] THEN
   GEN_TAC THEN GEN_REWR_TAC LAND_CONV [GSYM SPECIFICATION] THEN
   RW_TAC std_ss [GSPECIFICATION] THEN SIMP_TAC std_ss [le_sup] THEN
   GEN_TAC THEN DISCH_THEN (MP_TAC o Q.SPEC `sup {f i (j:num) | i IN univ(:num)}`) THEN
   Q_TAC SUFF_TAC `{sup {f i j | i IN univ(:num)} | j IN univ(:num)}
    (sup {f i j | i IN univ(:num)})` THENL
   [DISCH_TAC, ONCE_REWRITE_TAC [GSYM SPECIFICATION] THEN SET_TAC []] THEN
   RW_TAC std_ss [] THEN MATCH_MP_TAC le_trans THEN
   Q.EXISTS_TAC `sup {f i j | i IN univ(:num)}` THEN ASM_REWRITE_TAC [le_sup] THEN
   GEN_TAC THEN DISCH_THEN MATCH_MP_TAC THEN
   ONCE_REWRITE_TAC [GSYM SPECIFICATION] THEN SET_TAC [],
   ALL_TAC] THEN
  SIMP_TAC std_ss [sup_le] THEN GEN_TAC THEN
  GEN_REWR_TAC LAND_CONV [GSYM SPECIFICATION] THEN
  RW_TAC std_ss [GSPECIFICATION] THEN SIMP_TAC std_ss [sup_le] THEN
  GEN_TAC THEN GEN_REWR_TAC LAND_CONV [GSYM SPECIFICATION] THEN
  RW_TAC std_ss [GSPECIFICATION] THEN
  FIRST_X_ASSUM (MP_TAC o Q.SPEC `sup {f (i:num) j | j IN univ(:num)}`) THEN
  Q_TAC SUFF_TAC `{sup {f i j | j IN univ(:num)} | i IN univ(:num)}
   (sup {f i j | j IN univ(:num)})` THENL
  [ALL_TAC, ONCE_REWRITE_TAC [GSYM SPECIFICATION] THEN SET_TAC []] THEN
  RW_TAC std_ss [] THEN MATCH_MP_TAC le_trans THEN
  Q.EXISTS_TAC `sup {f i j | j IN univ(:num)}` THEN ASM_SIMP_TAC std_ss [le_sup] THEN
  GEN_TAC THEN DISCH_THEN MATCH_MP_TAC THEN
  ONCE_REWRITE_TAC [GSYM SPECIFICATION] THEN SET_TAC []);

val lemma = store_thm ("lemma",
  ``!f n'. (!i. (!m n. m <= n ==> (\x. f x i) m <= (\x. f x i) n)) /\
        (!n i. 0 <= f n i) ==>
        (SIGMA (\i. sup {f k i | k IN univ(:num)}) (count n') =
         sup {SIGMA (\i. f k i) (count n') | k IN UNIV})``,
  RW_TAC std_ss [] THEN Q.ABBREV_TAC `s = count n'` THEN
  `FINITE s` by METIS_TAC [FINITE_COUNT] THEN POP_ASSUM MP_TAC THEN
  Q.SPEC_TAC (`s`,`s`) THEN SET_INDUCT_TAC THENL
  [SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_EMPTY, IN_UNIV] THEN
   ONCE_REWRITE_TAC [SET_RULE ``{0 | k | T} = {0}``] THEN
   SIMP_TAC std_ss [sup_sing],
   ALL_TAC] THEN
  Q_TAC SUFF_TAC `sup {SIGMA (\i. f k i) s' + SIGMA (\i. f k i) {e} | k IN univ(:num)} =
   sup {SIGMA (\i. f k i) s' | k IN univ(:num)} +
   sup {SIGMA (\i. f k i) {e} | k IN univ(:num)}` THENL
  [ALL_TAC,
   SIMP_TAC std_ss [GSYM IMAGE_DEF] THEN
   ONCE_REWRITE_TAC [METIS [] ``SIGMA (\i. f k i) s' + SIGMA (\i. f k i) {e} =
     (\k. SIGMA (\i. f k i) s') k + (\k. SIGMA (\i. f k i) {e}) k``] THEN
   MATCH_MP_TAC sup_add_mono THEN RW_TAC std_ss [] THENL
   [MATCH_MP_TAC EXTREAL_SUM_IMAGE_POS THEN ASM_SIMP_TAC std_ss [],
    FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP EXTREAL_SUM_IMAGE_MONO) THEN
    RW_TAC std_ss [] THEN DISJ1_TAC THEN GEN_TAC THEN
    SIMP_TAC std_ss [lt_infty] THEN DISCH_TAC THEN
    METIS_TAC [lte_trans, num_not_infty, lt_infty],
    ASM_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_SING],
    ALL_TAC] THEN
   RW_TAC std_ss [EXTREAL_SUM_IMAGE_SING]] THEN
  DISCH_TAC THEN `FINITE {e}` by SIMP_TAC std_ss [FINITE_SING] THEN
  `DISJOINT s' {e}` by ASM_SET_TAC [] THEN
  `!k.
   (!x. x IN (s' UNION {e}) ==> (\i. f k i) x <> NegInf) \/
   (!x. x IN (s' UNION {e}) ==> (\i. f k i) x <> PosInf) ==>
   (SIGMA (\i. f k i) (s' UNION {e}) = SIGMA (\i. f k i) s' + SIGMA (\i. f k i) {e})` by
   METIS_TAC [EXTREAL_SUM_IMAGE_DISJOINT_UNION] THEN
  Q_TAC SUFF_TAC `!k. (SIGMA (\i. f k i) (s' UNION {e}) =
       SIGMA (\i. f k i) s' + SIGMA (\i. f k i) {e})` THENL
  [ALL_TAC,
   GEN_TAC THEN POP_ASSUM MATCH_MP_TAC THEN DISJ1_TAC THEN
   RW_TAC std_ss [lt_infty] THEN METIS_TAC [lte_trans, num_not_infty, lt_infty]] THEN
  DISCH_TAC THEN ONCE_REWRITE_TAC [SET_RULE ``e INSERT s' = s' UNION {e}``] THEN
  ASM_REWRITE_TAC [] THEN
  `(!x. x IN s' UNION {e} ==> (\i. sup {f k i | k IN univ(:num)}) x <> NegInf) \/
   (!x. x IN s' UNION {e} ==> (\i. sup {f k i | k IN univ(:num)}) x <> PosInf) ==>
   (SIGMA (\i. sup {f k i | k IN univ(:num)}) (s' UNION {e}) =
    SIGMA (\i. sup {f k i | k IN univ(:num)}) s' + SIGMA (\i. sup {f k i | k IN univ(:num)}) {e})`
   by (MATCH_MP_TAC EXTREAL_SUM_IMAGE_DISJOINT_UNION THEN ASM_SIMP_TAC std_ss []) THEN
  Q_TAC SUFF_TAC `(SIGMA (\i. sup {f k i | k IN univ(:num)}) (s' UNION {e}) =
        SIGMA (\i. sup {f k i | k IN univ(:num)}) s' +
        SIGMA (\i. sup {f k i | k IN univ(:num)}) {e})` THENL
  [ALL_TAC,
   POP_ASSUM MATCH_MP_TAC THEN DISJ1_TAC THEN RW_TAC std_ss [sup_eq] THEN
   DISJ1_TAC THEN Q.EXISTS_TAC `f k x` THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC [GSYM SPECIFICATION] THEN SET_TAC [], ALL_TAC] THEN
   SIMP_TAC std_ss [GSYM extreal_lt_def] THEN
   METIS_TAC [lte_trans, num_not_infty, lt_infty]] THEN
  DISC_RW_KILL THEN ASM_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_SING]);

val suminf_SUP_eq = store_thm ("suminf_SUP_eq",
  ``!(f:num->num->extreal).
     (!i. (!m n. m <= n ==> (\x. f x i) m <= (\x. f x i) n)) /\
     (!n i. 0 <= f n i) ==>
     (suminf (\i. sup {f n i | n IN UNIV}) =
      sup {suminf (\i. f n i) | n IN UNIV})``,
  RW_TAC std_ss [ext_suminf_def, IMAGE_DEF] THEN
  Q_TAC SUFF_TAC `!n. SIGMA (\i. sup {f k i | k IN univ(:num)}) (count n) =
           sup {SIGMA (\i. f k i) (count n) | k IN UNIV}` THENL
  [DISCH_TAC THEN
   Q_TAC SUFF_TAC `sup {SIGMA (\i. sup {f n i | n IN univ(:num)}) (count n) | n IN univ(:num)} =
                   sup {sup {SIGMA (\i. f k i) (count n) | k IN univ(:num)} | n IN univ(:num)}` THENL
   [ALL_TAC,
    AP_TERM_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN METIS_TAC []] THEN
   DISC_RW_KILL THEN Q_TAC SUFF_TAC
    `sup {sup {(\k n. SIGMA (\i. f k i) (count n)) k n | k IN univ(:num)} | n IN univ(:num)} =
     sup {sup {(\k n. SIGMA (\i. f k i) (count n)) k n | n IN univ(:num)} | k IN univ(:num)}` THENL
   [ALL_TAC, Q.ABBREV_TAC `g = (\k n. SIGMA (\i. f k i) (count n))` THEN
    SIMP_TAC std_ss [SUP_commute]] THEN METIS_TAC [],
   ALL_TAC] THEN
  ASM_SIMP_TAC std_ss [lemma]);

val seq_le_imp_lim_le = store_thm
  ("seq_le_imp_lim_le",
   ``!x y f. (!n. f n <= x) /\ (f --> y) sequentially ==> y <= x``,
   RW_TAC boolSimps.bool_ss [LIM_SEQUENTIALLY]
   THEN MATCH_MP_TAC REAL_LE_EPSILON
   THEN RW_TAC boolSimps.bool_ss []
   THEN Q.PAT_X_ASSUM `!e. P e` (MP_TAC o Q.SPEC `e`)
   THEN RW_TAC boolSimps.bool_ss []
   THEN POP_ASSUM (MP_TAC o Q.SPEC `N`)
   THEN Q.PAT_X_ASSUM `!n. P n` (MP_TAC o Q.SPEC `N`)
   THEN REWRITE_TAC [dist]
   THEN (RW_TAC boolSimps.bool_ss
         [GREATER_EQ, LESS_EQ_REFL, abs, REAL_LE_SUB_LADD, REAL_ADD_LID]
         THEN simpLib.FULL_SIMP_TAC boolSimps.bool_ss
              [REAL_NOT_LE, REAL_NEG_SUB, REAL_LT_SUB_RADD])
   THENL [MATCH_MP_TAC REAL_LE_TRANS
          THEN Q.EXISTS_TAC `x`
          THEN (CONJ_TAC THEN1 PROVE_TAC [REAL_LE_TRANS])
          THEN PROVE_TAC [REAL_LE_ADDR, REAL_LT_LE],
          MATCH_MP_TAC REAL_LE_TRANS
          THEN Q.EXISTS_TAC `f N + e`
          THEN (CONJ_TAC THEN1 PROVE_TAC [REAL_LT_LE, REAL_ADD_SYM])
          THEN PROVE_TAC [REAL_LE_ADD2, REAL_LE_REFL]]);

val seq_mono_le = store_thm ("seq_mono_le",
   ``!f x n. (!n. f n <= f (n + 1)) /\ (f --> x) sequentially ==> f n <= x``,
   RW_TAC boolSimps.bool_ss [LIM_SEQUENTIALLY] THEN MATCH_MP_TAC REAL_LE_EPSILON THEN
   RW_TAC boolSimps.bool_ss [] THEN Q.PAT_X_ASSUM `!e. P e` (MP_TAC o Q.SPEC `e`) THEN
   RW_TAC boolSimps.bool_ss [GREATER_EQ] THEN MP_TAC (Q.SPECL [`N`, `n`] LESS_EQ_CASES) THEN
   STRIP_TAC THENL
   [Q.PAT_X_ASSUM `!n. P n` (MP_TAC o Q.SPEC `n`) THEN ASM_REWRITE_TAC [dist] THEN
    REAL_ARITH_TAC, ALL_TAC] THEN FULL_SIMP_TAC std_ss [dist] THEN
   (SUFF_TAC ``!i : num. f (N - i) <= x + (e : real)`` THEN1 PROVE_TAC [LESS_EQUAL_DIFF]) THEN
   numLib.INDUCT_TAC
   THENL [Q.PAT_X_ASSUM `!n. P n` (MP_TAC o Q.SPEC `N`)
          THEN RW_TAC boolSimps.bool_ss [abs, LESS_EQ_REFL, SUB_0]
          THEN simpLib.FULL_SIMP_TAC boolSimps.bool_ss
               [REAL_LT_SUB_RADD, REAL_NEG_SUB, REAL_NOT_LE, REAL_ADD_LID,
                REAL_LE_SUB_LADD]
          THEN PROVE_TAC
               [REAL_LT_LE, REAL_ADD_SYM, REAL_LE_TRANS, REAL_LE_ADDR],
          MP_TAC (numLib.ARITH_PROVE
                  ``(N - i = N - SUC i) \/ (N - i = (N - SUC i) + 1)``)
          THEN PROVE_TAC [REAL_LE_REFL, REAL_LE_TRANS]]);

val sup_sequence = store_thm ("sup_sequence",
  ``!f l. mono_increasing f ==> ((f --> l) sequentially =
          (sup (IMAGE (\n. Normal (f n)) UNIV) = Normal l))``,
  RW_TAC std_ss [] THEN EQ_TAC THENL
  [RW_TAC std_ss [sup_eq] THENL
   [POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION]) THEN
    RW_TAC std_ss [IN_IMAGE,IN_UNIV] THEN RW_TAC std_ss [extreal_le_def] THEN
    METIS_TAC [mono_increasing_suc,seq_mono_le,ADD1], ALL_TAC] THEN
   KNOW_TAC ``!n:num. Normal (f n) <= y`` THENL
   [RW_TAC std_ss [] THEN POP_ASSUM MATCH_MP_TAC THEN
    ONCE_REWRITE_TAC [GSYM SPECIFICATION] THEN RW_TAC std_ss [IN_IMAGE,IN_UNIV] THEN
    METIS_TAC [], ALL_TAC] THEN
   Cases_on `y` THENL
   [METIS_TAC [le_infty,extreal_not_infty],
    METIS_TAC [le_infty],
    METIS_TAC [seq_le_imp_lim_le,extreal_le_def]], ALL_TAC] THEN
  RW_TAC std_ss [extreal_sup_def] THEN
  KNOW_TAC ``(\r. IMAGE (\n. Normal ((f:num->real) n)) UNIV (Normal r)) =
                  IMAGE f UNIV`` THENL
  [RW_TAC std_ss [EXTENSION,IN_ABS,IN_IMAGE,IN_UNIV] THEN EQ_TAC THENL
   [RW_TAC std_ss [] THEN POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION]) THEN
    RW_TAC std_ss [IN_IMAGE,IN_UNIV], ALL_TAC] THEN
   RW_TAC std_ss [] THEN ONCE_REWRITE_TAC [GSYM SPECIFICATION] THEN
   RW_TAC std_ss [IN_UNIV,IN_IMAGE] THEN METIS_TAC [], ALL_TAC] THEN
  FULL_SIMP_TAC std_ss [] THEN KNOW_TAC ``!n:num. Normal (f n) <= x`` THENL
  [RW_TAC std_ss [] THEN Q.PAT_X_ASSUM `!y. P` MATCH_MP_TAC THEN
   ONCE_REWRITE_TAC [GSYM SPECIFICATION] THEN RW_TAC std_ss [IN_UNIV,IN_IMAGE] THEN
   METIS_TAC [], ALL_TAC] THEN
  `x <> NegInf` by METIS_TAC [lt_infty,extreal_not_infty,lte_trans] THEN
  `?z. x = Normal z` by METIS_TAC [extreal_cases] THEN
  KNOW_TAC ``!n:num. f n <= z:real`` THENL
  [RW_TAC std_ss [GSYM extreal_le_def] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
   ONCE_REWRITE_TAC [GSYM SPECIFICATION] THEN SIMP_TAC std_ss [IN_IMAGE, IN_UNIV] THEN
   METIS_TAC [], ALL_TAC] THEN
  RW_TAC std_ss [LIM_SEQUENTIALLY, dist] THEN
  (MP_TAC o Q.ISPECL [`IMAGE (f:num->real) UNIV`,`e:real/2`]) SUP_EPSILON THEN
  SIMP_TAC std_ss [REAL_LT_HALF1] THEN
  KNOW_TAC ``!y x z. IMAGE f UNIV x = x IN IMAGE (f:num->real) UNIV`` THENL
  [RW_TAC std_ss [SPECIFICATION], DISCH_TAC] THEN
  STRIP_TAC THEN KNOW_TAC ``(?z. !x. x IN IMAGE (f:num->real) UNIV ==> x <= z)`` THENL
  [Q.EXISTS_TAC `z:real` THEN RW_TAC std_ss [IN_IMAGE,IN_UNIV] THEN
   METIS_TAC [], DISCH_TAC] THEN
  KNOW_TAC ``?x. x IN IMAGE (f:num->real) UNIV`` THENL
  [RW_TAC std_ss [IN_UNIV,IN_IMAGE], ALL_TAC] THEN
  RW_TAC std_ss [] THEN KNOW_TAC ``?x. x IN IMAGE (f:num->real) UNIV /\
                                   real$sup (IMAGE f UNIV) <= x + e / 2`` THENL
  [METIS_TAC [], DISCH_TAC] THEN
  RW_TAC std_ss [GSYM ABS_BETWEEN, GREATER_EQ] THEN
  FULL_SIMP_TAC std_ss [IN_IMAGE,IN_UNIV] THEN
  Q.EXISTS_TAC `x''''` THEN RW_TAC std_ss [REAL_LT_SUB_RADD] THENL
  [MATCH_MP_TAC REAL_LET_TRANS THEN Q.EXISTS_TAC `f x'''' + e / 2` THEN
   RW_TAC std_ss [] THEN MATCH_MP_TAC REAL_LET_TRANS THEN
   Q.EXISTS_TAC `(f:num->real) n + e / 2` THEN REVERSE CONJ_TAC THENL
   [METIS_TAC [REAL_LET_ADD2,REAL_LT_HALF2,REAL_LE_REFL], ALL_TAC] THEN
   RW_TAC std_ss [REAL_LE_RADD] THEN
   METIS_TAC [extreal_hvgTheory.mono_increasing_def], ALL_TAC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN Q.EXISTS_TAC `real$sup (IMAGE f UNIV)` THEN
  RW_TAC std_ss [REAL_LT_ADDR] THEN
  Q_TAC SUFF_TAC `!y. (\y. y IN IMAGE f UNIV) y ==> y <= real$sup (IMAGE f UNIV)` THENL
  [METIS_TAC [IN_IMAGE, IN_UNIV], ALL_TAC] THEN
  SIMP_TAC std_ss [IN_DEF] THEN
  MATCH_MP_TAC REAL_SUP_UBOUND_LE THEN
  KNOW_TAC ``!y x z. IMAGE (f:num->bool) UNIV x = x IN IMAGE f UNIV`` THENL
  [RW_TAC std_ss [IN_DEF], DISCH_TAC] THEN
  RW_TAC std_ss [IN_IMAGE, IN_UNIV] THEN
  Q.EXISTS_TAC `z'` THEN RW_TAC std_ss []);

val countably_additive_lebesgue = store_thm ("countably_additive_lebesgue",
  ``countably_additive lebesgue``,
  RW_TAC std_ss [countably_additive_def] THEN
  KNOW_TAC ``!A. IMAGE A univ(:num) SUBSET measurable_sets lebesgue ==>
                 !i n. indicator (A i) integrable_on line n`` THENL
  [REPEAT STRIP_TAC THEN MATCH_MP_TAC lebesgueD THEN
   FULL_SIMP_TAC std_ss [SUBSET_DEF] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
   METIS_TAC [IN_IMAGE, IN_UNIV], DISCH_TAC] THEN
  KNOW_TAC ``!i n. 0 <= integral (line n) (indicator ((f:num->real->bool) i))`` THENL
  [REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_COMPONENT_POS THEN
   SIMP_TAC std_ss [DROP_INDICATOR_POS_LE] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
   FULL_SIMP_TAC std_ss [IN_FUNSET, SUBSET_DEF, IN_IMAGE] THEN
   METIS_TAC [], DISCH_TAC] THEN
  KNOW_TAC ``BIGUNION {f i | i IN UNIV} IN measurable_sets lebesgue ==>
             !i n. (indicator ((f:num->real->bool) i)) integrable_on line n`` THENL
  [RW_TAC std_ss [] THEN MATCH_MP_TAC lebesgueD THEN
   FULL_SIMP_TAC std_ss [IN_FUNSET, IN_UNIV],
   FULL_SIMP_TAC std_ss [GSYM IMAGE_DEF] THEN DISCH_TAC] THEN
  SIMP_TAC std_ss [o_DEF, measure_lebesgue] THEN
  KNOW_TAC ``suminf (\i. sup {(\n i. Normal (integral (line n) (indicator (f i)))) n i | n IN univ(:num)}) =
             sup {suminf (\i. (\n i. Normal (integral (line n) (indicator (f i)))) n i) | n IN UNIV}`` THENL
  [MATCH_MP_TAC suminf_SUP_eq THEN SIMP_TAC std_ss [extreal_of_num_def] THEN
   CONJ_TAC THENL
   [SIMP_TAC std_ss [extreal_le_def] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC INTEGRAL_SUBSET_COMPONENT_LE THEN
    FULL_SIMP_TAC std_ss [line_subset, DROP_INDICATOR_POS_LE], ALL_TAC] THEN
   SIMP_TAC std_ss [extreal_le_def] THEN REPEAT GEN_TAC THEN
   MATCH_MP_TAC INTEGRAL_COMPONENT_POS THEN
   FULL_SIMP_TAC std_ss [DROP_INDICATOR_POS_LE],
   RW_TAC std_ss [] THEN POP_ASSUM K_TAC] THEN
  KNOW_TAC ``!n. Normal (integral (line n) (indicator (BIGUNION (IMAGE f univ(:num))))) =
    suminf (\x. Normal (integral (line n) (indicator ((f:num->real->bool) x))))`` THENL
  [ALL_TAC, DISCH_TAC THEN ASM_SIMP_TAC std_ss []] THEN
  SIMP_TAC std_ss [ext_suminf_def, FINITE_COUNT, EXTREAL_SUM_IMAGE_NORMAL] THEN
  GEN_TAC THEN KNOW_TAC ``mono_increasing
   (\n'. SIGMA (\x. integral (line n) (indicator ((f:num->real->bool) x))) (count n'))`` THENL
   [SIMP_TAC std_ss [extreal_hvgTheory.mono_increasing_def] THEN
    REPEAT STRIP_TAC THEN SIMP_TAC std_ss [GSYM extreal_le_def] THEN
    SIMP_TAC std_ss [FINITE_COUNT, GSYM EXTREAL_SUM_IMAGE_NORMAL] THEN
    MATCH_MP_TAC EXTREAL_SUM_IMAGE_MONO_SET THEN
    ASM_SIMP_TAC real_ss [count_def, GSPECIFICATION, FINITE_COUNT, SUBSET_DEF] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC [extreal_of_num_def, extreal_le_def] THEN
    MATCH_MP_TAC INTEGRAL_COMPONENT_POS THEN
    ASM_SIMP_TAC std_ss [DROP_INDICATOR_POS_LE], DISCH_TAC] THEN
  ASM_SIMP_TAC std_ss [GSYM sup_sequence, REAL_SUM_IMAGE_COUNT] THEN
  KNOW_TAC ``!n m. sum (0,m) (\x. integral (line n) (indicator ((f:num->real->bool) x))) =
                 integral (line n) (indicator (BIGUNION {f i | i < m}))`` THENL
[GEN_TAC THEN Induct_on `m` THENL
 [REWRITE_TAC [realTheory.sum, LT] THEN
  REWRITE_TAC [SET_RULE ``{f i | i | F} = {}``, BIGUNION_EMPTY] THEN
  SIMP_TAC real_ss [indicator_empty, INTEGRAL_0], ALL_TAC] THEN
 KNOW_TAC ``!m. BIGUNION {(f:num->real->bool) i | i < m} IN
                measurable_sets lebesgue`` THENL
 [GEN_TAC THEN MATCH_MP_TAC lebesgueI THEN GEN_TAC THEN
  ASSUME_TAC sigma_algebra_lebesgue THEN
  FULL_SIMP_TAC std_ss [SIGMA_ALGEBRA, GSPECIFICATION, subsets_def, space_def] THEN
  POP_ASSUM MATCH_MP_TAC THEN
  ASM_SIMP_TAC std_ss [SUBSET_DEF, GSPECIFICATION, IN_UNIV] THEN CONJ_TAC THENL
  [REWRITE_TAC [pred_setTheory.COUNTABLE_ALT] THEN SET_TAC [], ALL_TAC] THEN METIS_TAC [],
  DISCH_TAC] THEN
 KNOW_TAC ``!m. BIGUNION {(f:num->real->bool) i | i < m} INTER f m = {}`` THENL
 [GEN_TAC THEN SIMP_TAC std_ss [INTER_DEF, IN_BIGUNION, GSPECIFICATION] THEN
  SIMP_TAC std_ss [EXTENSION, GSPECIFICATION, NOT_IN_EMPTY] THEN
  GEN_TAC THEN ASM_CASES_TAC ``x NOTIN (f:num->real->bool) m'`` THEN
  ASM_REWRITE_TAC [] THEN GEN_TAC THEN
  ASM_CASES_TAC ``x IN (s:real->bool)`` THEN FULL_SIMP_TAC std_ss [] THEN
  GEN_TAC THEN ASM_CASES_TAC ``~(i < m':num)`` THEN FULL_SIMP_TAC std_ss [] THEN
  EXISTS_TAC ``x:real`` THEN FULL_SIMP_TAC std_ss [DISJOINT_DEF] THEN
  POP_ASSUM MP_TAC THEN DISCH_THEN (ASSUME_TAC o MATCH_MP LESS_NOT_EQ) THEN
  ASM_SET_TAC [], DISCH_TAC] THEN
 KNOW_TAC ``!x. indicator (BIGUNION {(f:num->real->bool) i | i < SUC m}) x =
                indicator (BIGUNION {f i | i < m}) x +
                indicator (f m) x`` THENL
 [GEN_TAC THEN SIMP_TAC std_ss [indicator] THEN
  ASM_CASES_TAC ``x IN ((f:num->real->bool) m)`` THEN ASM_SIMP_TAC std_ss [] THENL
  [KNOW_TAC ``x NOTIN BIGUNION {(f:num->real->bool) i | i < m}`` THENL
   [ASM_SET_TAC [], DISCH_TAC] THEN ASM_SIMP_TAC real_ss [IN_BIGUNION] THEN
   SIMP_TAC std_ss [GSPECIFICATION] THEN
   KNOW_TAC ``?s. x IN s /\ ?i. (s = (f:num->real->bool) i) /\ i < SUC m`` THENL
   [ALL_TAC, METIS_TAC []] THEN EXISTS_TAC ``(f:num->real->bool) m`` THEN
   ASM_REWRITE_TAC [] THEN EXISTS_TAC ``m:num`` THEN SIMP_TAC arith_ss [], ALL_TAC] THEN
   FULL_SIMP_TAC real_ss [IN_BIGUNION, GSPECIFICATION] THEN COND_CASES_TAC THENL
   [ALL_TAC, COND_CASES_TAC THENL [ALL_TAC, SIMP_TAC real_ss []] THEN
    FULL_SIMP_TAC std_ss [] THEN FIRST_X_ASSUM (MP_TAC o SPEC ``s:real->bool``) THEN
    ASM_SIMP_TAC std_ss [] THEN DISCH_THEN (MP_TAC o SPEC ``i:num``) THEN
    ASM_SIMP_TAC arith_ss []] THEN FULL_SIMP_TAC std_ss [] THEN
   COND_CASES_TAC THENL [SIMP_TAC std_ss [], ALL_TAC] THEN
   FULL_SIMP_TAC std_ss [] THEN FIRST_X_ASSUM (MP_TAC o SPEC ``(f:num->real->bool) i``) THEN
   ASM_SIMP_TAC std_ss [] THEN DISCH_THEN (MP_TAC o SPEC ``i:num``) THEN
   RW_TAC std_ss [] THEN KNOW_TAC ``i = m:num`` THENL
   [ASM_SIMP_TAC arith_ss [], DISCH_TAC] THEN FULL_SIMP_TAC std_ss [],
   DISCH_TAC] THEN
  ONCE_REWRITE_TAC [realTheory.sum] THEN ASM_REWRITE_TAC [] THEN
  ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN REWRITE_TAC [ADD] THEN
  GEN_REWR_TAC (RAND_CONV o ONCE_DEPTH_CONV) [METIS [] ``!f. indicator f = (\x. indicator f x)``] THEN
  SIMP_TAC std_ss [] THEN
  KNOW_TAC ``integral (line n') (indicator (BIGUNION {f i | i < SUC m})) =
             integral (line n') ((\x. (\x. indicator (BIGUNION {f i | i < m}) x) x +
                                 (\x. indicator ((f:num->real->bool) m) x) x))`` THENL
  [FIRST_X_ASSUM (ASSUME_TAC o ONCE_REWRITE_RULE [EQ_SYM_EQ]) THEN
   ASM_SIMP_TAC std_ss [] THEN METIS_TAC [], DISC_RW_KILL] THEN
  MATCH_MP_TAC INTEGRAL_ADD THEN METIS_TAC [lebesgueD], DISCH_TAC] THEN
  ASM_SIMP_TAC std_ss [] THEN
  MATCH_MP_TAC (METIS [] ``!P. (P /\ Q) ==> Q``) THEN
  ONCE_REWRITE_TAC [METIS []
        ``(indicator (BIGUNION {(f:num->real->bool) i | i < n'})) =
     (\n'. indicator (BIGUNION {f i | i < n'})) n'``] THEN
  EXISTS_TAC ``(indicator (BIGUNION (IMAGE (f:num->real->bool) univ(:num))))
                integrable_on (line n)`` THEN
  MATCH_MP_TAC DOMINATED_CONVERGENCE THEN EXISTS_TAC ``\x:real. 1:real`` THEN
  REPEAT CONJ_TAC THENL
  [KNOW_TAC ``!m. BIGUNION {(f:num->real->bool) i | i < m} IN
                measurable_sets lebesgue`` THENL
  [GEN_TAC THEN MATCH_MP_TAC lebesgueI THEN GEN_TAC THEN
   ASSUME_TAC sigma_algebra_lebesgue THEN
   FULL_SIMP_TAC std_ss [SIGMA_ALGEBRA, GSPECIFICATION, subsets_def, space_def] THEN
   POP_ASSUM MATCH_MP_TAC THEN
   ASM_SIMP_TAC std_ss [SUBSET_DEF, GSPECIFICATION, IN_UNIV] THEN CONJ_TAC THENL
   [REWRITE_TAC [pred_setTheory.COUNTABLE_ALT] THEN SET_TAC [], ALL_TAC] THEN METIS_TAC [],
    DISCH_TAC] THEN METIS_TAC [lebesgueD],
   SIMP_TAC std_ss [line, GSYM interval, INTEGRABLE_CONST],
   FULL_SIMP_TAC std_ss [DROP_INDICATOR_ABS_LE_1], ALL_TAC] THEN
  METIS_TAC [LIMSEQ_indicator_UN, IMAGE_DEF]);

val measure_space_lebesgue = store_thm ("measure_space_lebesgue",
  ``measure_space lebesgue``,
  SIMP_TAC std_ss [measure_space_def, positive_lebesgue] THEN
  SIMP_TAC std_ss [sets_lebesgue, space_lebesgue, sigma_algebra_lebesgue] THEN
  SIMP_TAC std_ss [countably_additive_lebesgue]);

val lebesgueI_borel = store_thm ("lebesgueI_borel",
  ``!s. s IN subsets borel ==> s IN measurable_sets lebesgue``,
  RW_TAC std_ss [] THEN
  KNOW_TAC ``s IN subsets (sigma (m_space lebesgue) (IMAGE (\(a,b). {x:real | a <= x /\ x <= b}) UNIV))`` THENL
  [ASM_SIMP_TAC std_ss [space_lebesgue, GSYM borel_eq_atLeastAtMost], ALL_TAC] THEN
  ONCE_REWRITE_TAC [METIS [space_def] ``m_space lebesgue =
                                 space (m_space lebesgue, measurable_sets lebesgue)``] THEN
  GEN_REWR_TAC (RAND_CONV o ONCE_DEPTH_CONV) [METIS [subsets_def] ``measurable_sets lebesgue =
                                         subsets (m_space lebesgue, measurable_sets lebesgue)``] THEN
  Q.SPEC_TAC (`s`,`s`) THEN SIMP_TAC std_ss [GSYM SUBSET_DEF] THEN
  MATCH_MP_TAC SIGMA_SUBSET THEN SIMP_TAC std_ss [space_lebesgue, sets_lebesgue, sigma_algebra_lebesgue] THEN
  SIMP_TAC std_ss [subsets_def] THEN RW_TAC std_ss [SUBSET_DEF, IN_IMAGE, IN_UNIV] THEN
  MP_TAC (ISPEC ``x':real#real`` ABS_PAIR_THM) THEN RW_TAC std_ss [] THEN
  SIMP_TAC std_ss [GSYM sets_lebesgue] THEN MATCH_MP_TAC lebesgueI THEN
  REWRITE_TAC [integrable_on, GSYM interval] THEN
  METIS_TAC [has_integral_interval_cube]);

val borel_measurable_lebesgueI = store_thm ("borel_measurable_lebesgueI",
  ``!f. f IN borel_measurable (space borel, subsets borel) ==>
        f IN borel_measurable (m_space lebesgue, measurable_sets lebesgue)``,
  RW_TAC std_ss [borel_measurable, measurable_def, GSPECIFICATION] THENL
  [SIMP_TAC std_ss [sigma_algebra_lebesgue, sets_lebesgue, space_lebesgue],
   FULL_SIMP_TAC std_ss [space_lebesgue, space_borel, space_def],
   FULL_SIMP_TAC std_ss [space_def, subsets_def]] THEN
  FULL_SIMP_TAC std_ss [space_borel, space_lebesgue, INTER_UNIV] THEN
  MATCH_MP_TAC lebesgueI_borel THEN ASM_SET_TAC []);

val lebesgueI_negligible = store_thm ("lebesgueI_negligible",
  ``!s. negligible s ==> s IN measurable_sets lebesgue``,
  RW_TAC std_ss [negligible] THEN MATCH_MP_TAC lebesgueI THEN
METIS_TAC [integrable_on, line, GSYM interval]);

val lmeasure_eq_0 = store_thm ("lmeasure_eq_0",
  ``!s. negligible s ==> (measure lebesgue s = 0)``,
  RW_TAC std_ss [measure_lebesgue] THEN
  KNOW_TAC ``!n. integral (line n) (indicator s) = 0`` THENL
  [FULL_SIMP_TAC std_ss [integral, negligible, line, GSYM interval] THEN
   GEN_TAC THEN MATCH_MP_TAC SELECT_UNIQUE THEN GEN_TAC THEN EQ_TAC THENL
   [ALL_TAC, METIS_TAC []] THEN METIS_TAC [HAS_INTEGRAL_UNIQUE],
   DISCH_TAC] THEN ASM_REWRITE_TAC [] THEN
  SIMP_TAC std_ss [GSYM extreal_of_num_def] THEN
  REWRITE_TAC [SET_RULE ``{0 | n IN UNIV} = {0}``] THEN
  SIMP_TAC std_ss [sup_sing]);

val lmeasure_iff_LIMSEQ = store_thm ("lmeasure_iff_LIMSEQ",
  ``!A m. A IN measurable_sets lebesgue /\ 0 <= m ==>
         ((measure lebesgue A = Normal m) =
          ((\n. integral (line n) (indicator A)) --> m) sequentially)``,
  RW_TAC std_ss [] THEN ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
  `!n. Normal (integral (line n) (indicator A)) =
  Normal ((\n. integral (line n) (indicator A)) n)` by METIS_TAC [] THEN
  SIMP_TAC std_ss [measure_lebesgue, GSYM IMAGE_DEF] THEN
  ONCE_ASM_REWRITE_TAC [] THEN MATCH_MP_TAC sup_sequence THEN
  RW_TAC std_ss [mono_increasing_def] THEN MATCH_MP_TAC INTEGRAL_SUBSET_COMPONENT_LE THEN
  ASM_SIMP_TAC std_ss [line_subset, lebesgueD, DROP_INDICATOR_POS_LE]);

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* ------------------------------------------------------------------------- *)

val _ = hide "sigma_finite_measure";

val sigma_finite_measure = new_definition ("sigma_finite_measure",
  ``sigma_finite_measure m =
   ?A. countable A /\ A SUBSET measurable_sets m /\
       (BIGUNION A = m_space m) /\
       (!a. a IN A ==> (measure m a <> PosInf))``);

val finite_measure = new_definition ("finite_measure",
  ``finite_measure m = sigma_finite_measure m /\
                       (measure m (m_space m) <> PosInf)``);

val sigma_finite = store_thm ("sigma_finite",
  ``!m. measure_space m /\ sigma_finite_measure m ==>
        ?A. IMAGE A UNIV SUBSET measurable_sets m /\
            (BIGUNION {A i | i IN UNIV} = m_space m) /\
            (!i:num. measure m (A i) <> PosInf)``,
  RW_TAC std_ss [sigma_finite_measure] THEN
  ASM_CASES_TAC ``(A:('a->bool)->bool) = {}`` THENL
  [FULL_SIMP_TAC std_ss [NOT_IN_EMPTY, BIGUNION_EMPTY] THEN
   RW_TAC std_ss [] THEN Q.EXISTS_TAC `(\n. {})` THEN
   SIMP_TAC std_ss [IMAGE_DEF, SUBSET_DEF] THEN
   REWRITE_TAC [SET_RULE ``{{} | i IN univ(:num)} = {{}}``] THEN
   ASM_SIMP_TAC std_ss [BIGUNION_SING, IN_SING] THEN
   ASM_SIMP_TAC std_ss [MEASURE_SPACE_MSPACE_MEASURABLE] THEN
   METIS_TAC [MEASURE_EMPTY, num_not_infty], ALL_TAC] THEN
  FULL_SIMP_TAC std_ss [COUNTABLE_ENUM] THEN
  Q.EXISTS_TAC `f` THEN RW_TAC std_ss [GSYM IMAGE_DEF] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN SET_TAC []);

val sigma_finite_disjoint = store_thm ("sigma_finite_disjoint",
  ``!m. measure_space m /\ sigma_finite_measure m ==>
      ?A. IMAGE A UNIV SUBSET measurable_sets m /\
          (BIGUNION {A i | i IN UNIV} = m_space m) /\
          (!i:num. measure m (A i) <> PosInf) /\
          disjoint_family A``,
  RW_TAC std_ss [] THEN
  `?A. IMAGE A univ(:num) SUBSET measurable_sets m /\
       (BIGUNION {A i | i IN univ(:num)} = m_space m) /\
       !i. measure m (A i) <> PosInf` by METIS_TAC [sigma_finite] THEN
  KNOW_TAC ``!i. measure m (disjointed A i) <= measure m (A i)`` THENL
  [GEN_TAC THEN
   MATCH_MP_TAC INCREASING THEN SIMP_TAC std_ss [disjointed_subset] THEN
   REPEAT CONJ_TAC THENL
   [ALL_TAC,
    `IMAGE (\n. disjointed A n) UNIV SUBSET measurable_sets m`
      by METIS_TAC [measure_space_def, sigma_algebra_alt_eq, algebra_alt_eq,
                    range_disjointed_sets] THEN ASM_SET_TAC [],
    ASM_SET_TAC []] THEN
   FULL_SIMP_TAC std_ss [MEASURE_SPACE_INCREASING], DISCH_TAC] THEN
  KNOW_TAC ``!i. measure m (disjointed A i) <> PosInf`` THENL
  [FULL_SIMP_TAC std_ss [lt_infty] THEN METIS_TAC [let_trans],
   DISCH_TAC] THEN
  Q.EXISTS_TAC `(\n. disjointed A n)` THEN RW_TAC std_ss [] THENL
  [MATCH_MP_TAC range_disjointed_sets THEN Q.EXISTS_TAC `m_space m` THEN
   FULL_SIMP_TAC std_ss [measure_space_def, sigma_algebra_alt_eq, algebra_alt_eq],
   ALL_TAC, METIS_TAC [disjoint_family_disjoint, ETA_AX]] THEN
  ASM_SIMP_TAC std_ss [UN_disjointed_eq]);

(* ------------------------------------------------------------------------- *)
(* Almost Everywhere                                                         *)
(* ------------------------------------------------------------------------- *)

val null_sets = new_definition ("null_sets",
  ``null_sets M = {N | N IN measurable_sets M /\ (measure M N = 0)}``);

val ae_filter = new_definition ("ae_filter",
 ``ae_filter M = {P | ?N. N IN null_sets M /\
                       {x | x IN m_space M /\ x NOTIN P} SUBSET N}``);

val AE = new_definition ("AE",
  ``AE M P = P IN ae_filter M``);

val AE_I = store_thm ("AE_I",
  ``!N M P. N IN null_sets M ==> {x | x IN m_space M /\ x NOTIN P} SUBSET N ==>
            AE M P``,
  RW_TAC std_ss [] THEN FULL_SIMP_TAC std_ss [AE, ae_filter, null_sets] THEN
  FULL_SIMP_TAC std_ss [SUBSET_DEF, GSPECIFICATION] THEN METIS_TAC []);

val AE_iff_null = store_thm ("AE_iff_null",
  ``!M P. measure_space M /\
          {x | x IN m_space M /\ x NOTIN P} IN measurable_sets M ==>
          (AE M P = {x | x IN m_space M /\ x NOTIN P} IN null_sets M)``,
  RW_TAC std_ss [AE, ae_filter, null_sets, GSPECIFICATION] THEN EQ_TAC THEN
  RW_TAC std_ss [] THENL [ALL_TAC, METIS_TAC [SUBSET_REFL]] THEN
  Q_TAC SUFF_TAC `measure M {x | x IN m_space M /\ x NOTIN P} <=
                  measure M N` THENL
  [DISCH_TAC THEN ONCE_REWRITE_TAC [GSYM le_antisym] THEN
   METIS_TAC [measure_space_def, positive_def], ALL_TAC] THEN
  MATCH_MP_TAC INCREASING THEN METIS_TAC [MEASURE_SPACE_INCREASING]);

val AE_iff_null_sets = store_thm ("AE_iff_null_sets",
  ``!N M. measure_space M /\ N IN measurable_sets M ==>
          (N IN null_sets M = AE M {x | x NOTIN N})``,
  REPEAT STRIP_TAC THEN EQ_TAC THEN RW_TAC std_ss [] THEN
  FULL_SIMP_TAC std_ss [AE, ae_filter, null_sets] THENL
  [FULL_SIMP_TAC std_ss [GSPECIFICATION] THEN ASM_SET_TAC [], ALL_TAC] THEN
  FULL_SIMP_TAC std_ss [GSPECIFICATION] THEN
  Q_TAC SUFF_TAC `measure M N <= measure M N'` THENL
  [DISCH_TAC THEN ONCE_REWRITE_TAC [GSYM le_antisym] THEN
   METIS_TAC [measure_space_def, positive_def], ALL_TAC] THEN
  MATCH_MP_TAC INCREASING THEN ASM_SIMP_TAC std_ss [MEASURE_SPACE_INCREASING] THEN
  `N SUBSET m_space M` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
  ASM_SET_TAC []);

val AE_not_in = store_thm ("AE_not_in",
  ``!N M. N IN null_sets M ==> AE M {x | x NOTIN N}``,
  RW_TAC std_ss [AE, ae_filter, GSPECIFICATION] THEN Q.EXISTS_TAC `N` THEN
  ASM_SIMP_TAC std_ss [SUBSET_DEF, GSPECIFICATION]);

val AE_iff_measurable = store_thm ("AE_iff_measurable",
  ``!N M P. measure_space M /\ N IN measurable_sets M ==>
           ({x | x IN m_space M /\ x NOTIN P} = N) ==>
           (AE M P = (measure M N = 0))``,
  RW_TAC std_ss [AE, ae_filter, GSPECIFICATION] THEN
  EQ_TAC THEN RW_TAC std_ss [] THENL
  [FULL_SIMP_TAC std_ss [null_sets, GSPECIFICATION] THEN
   Q_TAC SUFF_TAC `measure M {x | x IN m_space M /\ x NOTIN P} <= measure M N'` THENL
   [DISCH_TAC THEN ONCE_REWRITE_TAC [GSYM le_antisym] THEN
    METIS_TAC [measure_space_def, positive_def], ALL_TAC] THEN
   MATCH_MP_TAC INCREASING THEN ASM_SIMP_TAC std_ss [MEASURE_SPACE_INCREASING],
   ALL_TAC] THEN
  FULL_SIMP_TAC std_ss [null_sets, GSPECIFICATION] THEN
  METIS_TAC [SUBSET_REFL]);

(* Induct_on_Borel_functions *)

val Induct_on_Borel_functions = store_thm ("Induct_on_Borel_functions",
 ``!f m P. measure_space m /\
  f IN measurable (m_space m, measurable_sets m) Borel /\ (!x. 0 <= f x) /\
  (!f g. f IN measurable (m_space m, measurable_sets m) Borel /\
         g IN measurable (m_space m, measurable_sets m) Borel /\
         (!x. x IN m_space m ==> (f x = g x)) /\ P f ==> P g) /\
  (!A. A IN measurable_sets m ==> P (indicator_fn A)) /\
  (!f c. f IN measurable (m_space m, measurable_sets m) Borel /\
         0 <= c /\ (!x. 0 <= f x) /\ P f ==> P (\x. c * f x)) /\
  (!f g. f IN measurable (m_space m, measurable_sets m) Borel /\
         g IN measurable (m_space m, measurable_sets m) Borel /\
         (!x. 0 <= f x) /\ P f /\ (!x. 0 <= g x) /\ P g ==>
         P (\x. f x + g x)) /\
  (!u. (!i:num. (u i) IN measurable (m_space m, measurable_sets m) Borel) /\
       (!i x. 0 <= u i x) /\ (!x. mono_increasing (\i. u i x)) /\
       (!i. P (u i)) ==> P (\x. sup (IMAGE (\i. u i x) UNIV))) ==> P f``,

  RW_TAC std_ss [] THEN

  FIRST_ASSUM MATCH_MP_TAC THEN
  Q.EXISTS_TAC `(\x. sup (IMAGE (\i. fn_seq m f i x) univ(:num)))` THEN
  ASM_SIMP_TAC std_ss [lemma_fn_sup] THEN

  Q_TAC SUFF_TAC `!i. (\x. SIGMA
          (\k. &k / 2 pow i *
             indicator_fn {x |
                x IN m_space m /\ &k / 2 pow i <= f x /\
                f x < (&k + 1) / 2 pow i} x) (count (4 ** i)))
          IN measurable (m_space m, measurable_sets m) Borel` THENL
  [DISCH_TAC,
   GEN_TAC THEN
   Q.ABBREV_TAC `s = count (4 ** i)` THEN
   Q.ABBREV_TAC `g = (\k x. &k / 2 pow i *
        indicator_fn
          {x |
           x IN m_space m /\ &k / 2 pow i <= f x /\
           f x < (&k + 1) / 2 pow i} x)` THEN

   Q_TAC SUFF_TAC `FINITE s /\ sigma_algebra (m_space m, measurable_sets m) /\
     (!i. i IN s ==> g i IN measurable (m_space m, measurable_sets m) Borel) /\
     (!i x. i IN s /\ x IN space (m_space m, measurable_sets m) ==> g i x <> NegInf) /\
     (!x. x IN space (m_space m, measurable_sets m) ==>
      ((\x. SIGMA
     (\k. &k / 2 pow i *
        indicator_fn {x |
           x IN m_space m /\ &k / 2 pow i <= f x /\
           f x < (&k + 1) / 2 pow i} x) s) x = SIGMA (\i. g i x) s))` THENL
   [DISCH_THEN (MP_TAC o MATCH_MP IN_MEASURABLE_BOREL_SUM) THEN
    SIMP_TAC std_ss [], ALL_TAC] THEN
   Q.UNABBREV_TAC `s` THEN Q.UNABBREV_TAC `g` THEN
   FULL_SIMP_TAC std_ss [measure_space_def, FINITE_COUNT] THEN
   SIMP_TAC std_ss [space_def, IN_UNIV] THEN CONJ_TAC THENL
   [ALL_TAC,
    RW_TAC std_ss [lt_infty] THEN MATCH_MP_TAC lte_trans THEN
    Q.EXISTS_TAC `0` THEN SIMP_TAC std_ss [GSYM lt_infty, num_not_infty] THEN
    MATCH_MP_TAC le_mul THEN SIMP_TAC std_ss [extreal_div_def, indicator_fn_def] THEN
    CONJ_TAC THENL
    [ALL_TAC, COND_CASES_TAC THEN
     SIMP_TAC real_ss [le_refl, extreal_of_num_def, extreal_le_def]] THEN
    MATCH_MP_TAC le_mul THEN SIMP_TAC std_ss [le_num] THEN
    `2 pow i <> NegInf /\ 2 pow i <> PosInf` by
    METIS_TAC [pow_not_infty, num_not_infty] THEN
    `2 pow i = Normal (real (2 pow i))` by METIS_TAC [normal_real] THEN
    POP_ASSUM (fn th => ONCE_REWRITE_TAC [th]) THEN
    SIMP_TAC real_ss [extreal_inv_def] THEN
    COND_CASES_TAC THEN SIMP_TAC std_ss [le_infty] THEN
    SIMP_TAC std_ss [extreal_of_num_def, extreal_le_def] THEN
    SIMP_TAC std_ss [REAL_LE_INV_EQ] THEN SIMP_TAC std_ss [GSYM extreal_le_def] THEN
    ASM_SIMP_TAC std_ss [normal_real, GSYM extreal_of_num_def] THEN
    SIMP_TAC std_ss [extreal_of_num_def, extreal_pow_def, extreal_le_def] THEN
    MATCH_MP_TAC POW_POS THEN SIMP_TAC real_ss []] THEN

   RW_TAC std_ss [] THEN MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL THEN
   Q.EXISTS_TAC `(\x. indicator_fn
          {x | x IN m_space m /\ &i' / 2 pow i <= f x /\ f x < (&i' + 1) / 2 pow i} x)` THEN
   Q.EXISTS_TAC `real (&i' / 2 pow i)` THEN
   Q_TAC SUFF_TAC `&i' / 2 pow i <> NegInf /\ &i' / 2 pow i <> PosInf` THENL
   [STRIP_TAC,
    SIMP_TAC std_ss [extreal_div_def] THEN ONCE_REWRITE_TAC [mul_comm] THEN
    `2 pow i <> NegInf /\ 2 pow i <> PosInf` by
    METIS_TAC [pow_not_infty, num_not_infty] THEN
    `2 pow i = Normal (real (2 pow i))` by METIS_TAC [normal_real] THEN
    POP_ASSUM (fn th => ONCE_REWRITE_TAC [th]) THEN
    ONCE_REWRITE_TAC [extreal_inv_def] THEN
    Q_TAC SUFF_TAC `real (2 pow i) <> 0` THENL
    [DISCH_TAC,
     REWRITE_TAC [GSYM extreal_11] THEN ASM_SIMP_TAC std_ss [normal_real] THEN
     ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN SIMP_TAC std_ss [extreal_of_num_def] THEN
     SIMP_TAC std_ss [extreal_pow_def] THEN SIMP_TAC std_ss [extreal_11] THEN
     MATCH_MP_TAC REAL_LT_IMP_NE THEN SIMP_TAC real_ss [REAL_LT_POW2]] THEN
    ASM_SIMP_TAC std_ss [] THEN
    `(!c y. 0 <= c /\ y <> NegInf ==> Normal c * y <> NegInf)`
     by METIS_TAC [mul_not_infty] THEN
    `(!c y. 0 <= c /\ y <> PosInf ==> Normal c * y <> PosInf)`
     by METIS_TAC [mul_not_infty] THEN
    Q_TAC SUFF_TAC `0 <= inv (real (2 pow i))` THENL
    [DISCH_TAC,
     REWRITE_TAC [REAL_LE_INV_EQ] THEN SIMP_TAC std_ss [GSYM extreal_le_def] THEN
     ASM_SIMP_TAC std_ss [normal_real, extreal_of_num_def] THEN
     SIMP_TAC std_ss [extreal_pow_def, extreal_le_def] THEN
     MATCH_MP_TAC REAL_LT_IMP_LE THEN SIMP_TAC std_ss [REAL_LT_POW2]] THEN
    CONJ_TAC THEN (FIRST_X_ASSUM MATCH_MP_TAC THEN
     ASM_SIMP_TAC std_ss [num_not_infty])] THEN
   ASM_SIMP_TAC std_ss [normal_real] THEN
   MATCH_MP_TAC IN_MEASURABLE_BOREL_INDICATOR THEN
   Q.EXISTS_TAC `{x | x IN m_space m /\ &i' / 2 pow i <= f x /\ f x < (&i' + 1) / 2 pow i}` THEN
   ASM_SIMP_TAC std_ss [] THEN
   Q_TAC SUFF_TAC
   `{x | x IN m_space m /\ &i' / 2 pow i <= f x /\ f x < (&i' + 1) / 2 pow i} =
    PREIMAGE f {x | &i' / 2 pow i <= x /\ x < (&i' + 1) / 2 pow i} INTER
    space (m_space m, measurable_sets m)` THENL
   [DISC_RW_KILL,
    SIMP_TAC std_ss [PREIMAGE_def, space_def, INTER_UNIV] THEN
    SET_TAC []] THEN
   FULL_SIMP_TAC std_ss [IN_MEASURABLE] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN

   Q_TAC SUFF_TAC `(&i' + 1) / 2 pow i <> NegInf /\ (&i' + 1) / 2 pow i <> PosInf` THENL
   [STRIP_TAC THEN METIS_TAC [BOREL_MEASURABLE_SETS_CO, normal_real],
    ALL_TAC] THEN
   SIMP_TAC std_ss [extreal_div_def] THEN ONCE_REWRITE_TAC [mul_comm] THEN
    `2 pow i <> NegInf /\ 2 pow i <> PosInf` by
    METIS_TAC [pow_not_infty, num_not_infty] THEN
    `2 pow i = Normal (real (2 pow i))` by METIS_TAC [normal_real] THEN
    POP_ASSUM (fn th => ONCE_REWRITE_TAC [th]) THEN
    ONCE_REWRITE_TAC [extreal_inv_def] THEN
    Q_TAC SUFF_TAC `real (2 pow i) <> 0` THENL
    [DISCH_TAC,
     REWRITE_TAC [GSYM extreal_11] THEN ASM_SIMP_TAC std_ss [normal_real] THEN
     ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN SIMP_TAC std_ss [extreal_of_num_def] THEN
     SIMP_TAC std_ss [extreal_pow_def] THEN SIMP_TAC std_ss [extreal_11] THEN
     MATCH_MP_TAC REAL_LT_IMP_NE THEN SIMP_TAC real_ss [REAL_LT_POW2]] THEN
    ASM_SIMP_TAC std_ss [] THEN
    `(!c y. 0 <= c /\ y <> NegInf ==> Normal c * y <> NegInf)`
     by METIS_TAC [mul_not_infty] THEN
    `(!c y. 0 <= c /\ y <> PosInf ==> Normal c * y <> PosInf)`
     by METIS_TAC [mul_not_infty] THEN
    Q_TAC SUFF_TAC `0 <= inv (real (2 pow i))` THENL
    [DISCH_TAC,
     REWRITE_TAC [REAL_LE_INV_EQ] THEN SIMP_TAC std_ss [GSYM extreal_le_def] THEN
     ASM_SIMP_TAC std_ss [normal_real, extreal_of_num_def] THEN
     SIMP_TAC std_ss [extreal_pow_def, extreal_le_def] THEN
     MATCH_MP_TAC REAL_LT_IMP_LE THEN SIMP_TAC std_ss [REAL_LT_POW2]] THEN
    `!x y. (x <> NegInf /\ y <> NegInf ==> x + y <> NegInf)` by METIS_TAC [add_not_infty] THEN
    `!x y. (x <> PosInf /\ y <> PosInf ==> x + y <> PosInf)` by METIS_TAC [add_not_infty] THEN
    CONJ_TAC THEN (FIRST_X_ASSUM MATCH_MP_TAC THEN
     ASM_SIMP_TAC std_ss [] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
     SIMP_TAC std_ss [num_not_infty])] THEN

  Q_TAC SUFF_TAC `!i. (\x. 2 pow i * indicator_fn {x | x IN m_space m /\ 2 pow i <= f x} x)
                      IN measurable (m_space m, measurable_sets m) Borel` THENL
  [DISCH_TAC,
   GEN_TAC THEN MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL THEN
   `2 pow i <> NegInf /\ 2 pow i <> PosInf` by
    METIS_TAC [pow_not_infty, num_not_infty] THEN
   Q.EXISTS_TAC `(\x. indicator_fn {x | x IN m_space m /\ 2 pow i <= f x} x)` THEN
   Q.EXISTS_TAC `real (2 pow i)` THEN ASM_SIMP_TAC std_ss [normal_real] THEN
   FULL_SIMP_TAC std_ss [measure_space_def] THEN
   MATCH_MP_TAC IN_MEASURABLE_BOREL_INDICATOR THEN
   Q.EXISTS_TAC `{x | x IN m_space m /\ 2 pow i <= f x}` THEN
   ASM_SIMP_TAC std_ss [space_def, IN_UNIV] THEN
   Q_TAC SUFF_TAC `{x | x IN m_space m /\ 2 pow i <= f x} =
    PREIMAGE f {x | 2 pow i <= x} INTER space (m_space m,measurable_sets m)` THENL
   [DISC_RW_KILL,
    SIMP_TAC std_ss [PREIMAGE_def, space_def, INTER_UNIV] THEN
    SET_TAC []] THEN
   FULL_SIMP_TAC std_ss [IN_MEASURABLE] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN METIS_TAC [BOREL_MEASURABLE_SETS_CR, normal_real]] THEN

  Q_TAC SUFF_TAC `(!i. fn_seq m f i IN measurable (m_space m,measurable_sets m) Borel)` THENL
  [DISCH_TAC,
   SIMP_TAC std_ss [fn_seq_def] THEN GEN_TAC THEN
   MATCH_MP_TAC IN_MEASURABLE_BOREL_ADD THEN
   Q.EXISTS_TAC `(\x. SIGMA
          (\k. &k / 2 pow i *
             indicator_fn {x |
                x IN m_space m /\ &k / 2 pow i <= f x /\
                f x < (&k + 1) / 2 pow i} x) (count (4 ** i)))` THEN
   Q.EXISTS_TAC `(\x. 2 pow i * indicator_fn {x | x IN m_space m /\ 2 pow i <= f x} x)` THEN
   POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN FULL_SIMP_TAC std_ss [measure_space_def] THEN
   RW_TAC std_ss [] THENL
   [SIMP_TAC std_ss [lt_infty] THEN MATCH_MP_TAC lte_trans THEN
    Q.EXISTS_TAC `0` THEN SIMP_TAC std_ss [GSYM lt_infty, num_not_infty] THEN
    MATCH_MP_TAC EXTREAL_SUM_IMAGE_POS THEN RW_TAC std_ss [FINITE_COUNT, IN_UNIV] THEN
    MATCH_MP_TAC le_mul THEN CONJ_TAC THENL
    [ALL_TAC,
     SIMP_TAC std_ss [indicator_fn_def] THEN COND_CASES_TAC THEN
     SIMP_TAC real_ss [le_refl, extreal_le_def, extreal_of_num_def]] THEN
    SIMP_TAC std_ss [extreal_div_def] THEN MATCH_MP_TAC le_mul THEN
    SIMP_TAC std_ss [le_num] THEN
    `2 pow i <> NegInf /\ 2 pow i <> PosInf` by
    METIS_TAC [pow_not_infty, num_not_infty] THEN
    `2 pow i = Normal (real (2 pow i))` by METIS_TAC [normal_real] THEN
    POP_ASSUM (fn th => ONCE_REWRITE_TAC [th]) THEN
    SIMP_TAC real_ss [extreal_inv_def] THEN
    COND_CASES_TAC THEN SIMP_TAC std_ss [le_infty] THEN
    SIMP_TAC std_ss [extreal_of_num_def, extreal_le_def] THEN
    SIMP_TAC std_ss [REAL_LE_INV_EQ] THEN SIMP_TAC std_ss [GSYM extreal_le_def] THEN
    ASM_SIMP_TAC std_ss [normal_real, GSYM extreal_of_num_def] THEN
    SIMP_TAC std_ss [extreal_of_num_def, extreal_pow_def, extreal_le_def] THEN
    MATCH_MP_TAC POW_POS THEN SIMP_TAC real_ss [],
    ALL_TAC] THEN
   SIMP_TAC std_ss [lt_infty] THEN MATCH_MP_TAC lte_trans THEN
   Q.EXISTS_TAC `0` THEN SIMP_TAC std_ss [GSYM lt_infty, num_not_infty] THEN
   MATCH_MP_TAC le_mul THEN CONJ_TAC THENL
   [ALL_TAC,
    SIMP_TAC std_ss [indicator_fn_def] THEN COND_CASES_TAC THEN
    SIMP_TAC real_ss [le_refl, extreal_le_def, extreal_of_num_def]] THEN
   SIMP_TAC std_ss [extreal_of_num_def, extreal_pow_def, extreal_le_def] THEN
   MATCH_MP_TAC POW_POS THEN SIMP_TAC real_ss []] THEN

  CONJ_TAC THENL
  [MATCH_MP_TAC IN_MEASURABLE_BOREL_MONO_SUP THEN
   Q.EXISTS_TAC `fn_seq m f` THEN SIMP_TAC std_ss [] THEN
   CONJ_TAC THENL
   [METIS_TAC [measure_space_def], ALL_TAC] THEN
   CONJ_TAC THENL
   [ALL_TAC,
    GEN_TAC THEN GEN_TAC THEN
    `mono_increasing (\n. fn_seq m f n x)` by METIS_TAC [lemma_fn_mono_increasing] THEN
    FULL_SIMP_TAC std_ss [ext_mono_increasing_def] THEN
    FIRST_X_ASSUM MATCH_MP_TAC] THEN ASM_SIMP_TAC std_ss [],
   ALL_TAC] THEN

  FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_SIMP_TAC std_ss [lemma_fn_mono_increasing, lemma_fn_5] THEN


  GEN_TAC THEN SIMP_TAC std_ss [fn_seq_def] THEN
  Q_TAC SUFF_TAC `P (\x.
    (\x. SIGMA
      (\k. &k / 2 pow i *
         indicator_fn {x |
            x IN m_space m /\ &k / 2 pow i <= f x /\
            f x < (&k + 1) / 2 pow i} x) (count (4 ** i))) x +
    (\x. 2 pow i * indicator_fn {x | x IN m_space m /\ 2 pow i <= f x} x) x)` THENL
  [SIMP_TAC std_ss [], ALL_TAC] THEN
  FIRST_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC std_ss [IN_UNIV] THEN
  CONJ_TAC THENL
  [GEN_TAC THEN
   MATCH_MP_TAC EXTREAL_SUM_IMAGE_POS THEN RW_TAC std_ss [FINITE_COUNT, IN_UNIV] THEN
   MATCH_MP_TAC le_mul THEN CONJ_TAC THENL
   [ALL_TAC,
    SIMP_TAC std_ss [indicator_fn_def] THEN COND_CASES_TAC THEN
    SIMP_TAC real_ss [le_refl, extreal_le_def, extreal_of_num_def]] THEN
   SIMP_TAC std_ss [extreal_div_def] THEN MATCH_MP_TAC le_mul THEN
   SIMP_TAC std_ss [le_num] THEN
   `2 pow i <> NegInf /\ 2 pow i <> PosInf` by
   METIS_TAC [pow_not_infty, num_not_infty] THEN
   `2 pow i = Normal (real (2 pow i))` by METIS_TAC [normal_real] THEN
   POP_ASSUM (fn th => ONCE_REWRITE_TAC [th]) THEN
   SIMP_TAC real_ss [extreal_inv_def] THEN
   COND_CASES_TAC THEN SIMP_TAC std_ss [le_infty] THEN
   SIMP_TAC std_ss [extreal_of_num_def, extreal_le_def] THEN
   SIMP_TAC std_ss [REAL_LE_INV_EQ] THEN SIMP_TAC std_ss [GSYM extreal_le_def] THEN
   ASM_SIMP_TAC std_ss [normal_real, GSYM extreal_of_num_def] THEN
   SIMP_TAC std_ss [extreal_of_num_def, extreal_pow_def, extreal_le_def] THEN
   MATCH_MP_TAC POW_POS THEN SIMP_TAC real_ss [],
   ALL_TAC] THEN

  CONJ_TAC THENL
  [`FINITE (count (4 ** i))` by SIMP_TAC std_ss [FINITE_COUNT] THEN
   Q_TAC SUFF_TAC `(\s. P
    (\x. SIGMA
       (\k. &k / 2 pow i *
          indicator_fn {x | x IN m_space m /\ &k / 2 pow i <= f x /\ f x < (&k + 1) / 2 pow i} x) (s)))
         (count (4 ** i))` THENL
   [SIMP_TAC std_ss [], ALL_TAC] THEN
   POP_ASSUM MP_TAC THEN
   Q.ABBREV_TAC `s = count (4 ** i)` THEN Q.SPEC_TAC (`s`,`s`) THEN
   MATCH_MP_TAC FINITE_INDUCT THEN
   Q.UNABBREV_TAC `s` THEN SIMP_TAC std_ss [FINITE_COUNT] THEN
   SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_EMPTY] THEN
   CONJ_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN Q.EXISTS_TAC `indicator_fn {}` THEN
    RW_TAC std_ss [] THENL
    [MATCH_MP_TAC IN_MEASURABLE_BOREL_INDICATOR THEN Q.EXISTS_TAC `{}` THEN
     FULL_SIMP_TAC std_ss [measure_space_def] THEN METIS_TAC [SIGMA_ALGEBRA],
     MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST THEN Q.EXISTS_TAC `0` THEN
     FULL_SIMP_TAC std_ss [measure_space_def],
     SIMP_TAC std_ss [indicator_fn_def, NOT_IN_EMPTY],
     ALL_TAC] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN
    FULL_SIMP_TAC std_ss [measure_space_def, SIGMA_ALGEBRA, subsets_def],
    ALL_TAC] THEN
   RW_TAC std_ss [] THEN
   Q_TAC SUFF_TAC `!x.
     SIGMA
       (\k.
          &k / 2 pow i *
          indicator_fn
            {x | x IN m_space m /\ &k / 2 pow i <= f x /\ f x < (&k + 1) / 2 pow i} x)
       (e INSERT s) =
      (\k. &k / 2 pow i *
      indicator_fn {x | x IN m_space m /\ &k / 2 pow i <= f x /\ f x < (&k + 1) / 2 pow i} x) e +
      SIGMA
       (\k.
          &k / 2 pow i *
          indicator_fn
            {x | x IN m_space m /\ &k / 2 pow i <= f x /\ f x < (&k + 1) / 2 pow i} x)
       (s DELETE e)` THENL
   [DISC_RW_KILL,
    GEN_TAC THEN FIRST_ASSUM (MP_TAC o MATCH_MP EXTREAL_SUM_IMAGE_PROPERTY) THEN
    DISCH_THEN MATCH_MP_TAC THEN DISJ1_TAC THEN
    GEN_TAC THEN DISCH_TAC THEN
    SIMP_TAC std_ss [lt_infty] THEN MATCH_MP_TAC lte_trans THEN
    Q.EXISTS_TAC `0` THEN SIMP_TAC std_ss [GSYM lt_infty, num_not_infty] THEN
    MATCH_MP_TAC le_mul THEN
    CONJ_TAC THENL
    [ALL_TAC,
     SIMP_TAC std_ss [indicator_fn_def] THEN COND_CASES_TAC THEN
     SIMP_TAC real_ss [le_refl, extreal_le_def, extreal_of_num_def]] THEN
    SIMP_TAC std_ss [extreal_div_def] THEN MATCH_MP_TAC le_mul THEN
    SIMP_TAC std_ss [le_num] THEN
    `2 pow i <> NegInf /\ 2 pow i <> PosInf` by
    METIS_TAC [pow_not_infty, num_not_infty] THEN
    `2 pow i = Normal (real (2 pow i))` by METIS_TAC [normal_real] THEN
    POP_ASSUM (fn th => ONCE_REWRITE_TAC [th]) THEN
    SIMP_TAC real_ss [extreal_inv_def] THEN
    COND_CASES_TAC THEN SIMP_TAC std_ss [le_infty] THEN
    SIMP_TAC std_ss [extreal_of_num_def, extreal_le_def] THEN
    SIMP_TAC std_ss [REAL_LE_INV_EQ] THEN SIMP_TAC std_ss [GSYM extreal_le_def] THEN
    ASM_SIMP_TAC std_ss [normal_real, GSYM extreal_of_num_def] THEN
    SIMP_TAC std_ss [extreal_of_num_def, extreal_pow_def, extreal_le_def] THEN
    MATCH_MP_TAC POW_POS THEN SIMP_TAC real_ss []] THEN
   ASM_SIMP_TAC std_ss [SET_RULE ``e NOTIN s ==> (s DELETE e = s)``] THEN
   Q_TAC SUFF_TAC `P (\x.
     (\x. &e / 2 pow i *
     indicator_fn {x | x IN m_space m /\ &e / 2 pow i <= f x /\ f x < (&e + 1) / 2 pow i}
       x) x +
     (\x. SIGMA
       (\k. &k / 2 pow i *
     indicator_fn {x | x IN m_space m /\ &k / 2 pow i <= f x /\ f x < (&k + 1) / 2 pow i} x) s) x)` THENL
   [SIMP_TAC std_ss [], ALL_TAC] THEN
   FIRST_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC std_ss [] THEN

   CONJ_TAC THENL
   [MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL THEN
    Q_TAC SUFF_TAC `&e / 2 pow i <> NegInf /\ &e / 2 pow i <> PosInf` THENL
    [STRIP_TAC,
     SIMP_TAC std_ss [extreal_div_def] THEN ONCE_REWRITE_TAC [mul_comm] THEN
     `2 pow i <> NegInf /\ 2 pow i <> PosInf` by
     METIS_TAC [pow_not_infty, num_not_infty] THEN
     `2 pow i = Normal (real (2 pow i))` by METIS_TAC [normal_real] THEN
     POP_ASSUM (fn th => ONCE_REWRITE_TAC [th]) THEN
     ONCE_REWRITE_TAC [extreal_inv_def] THEN
     Q_TAC SUFF_TAC `real (2 pow i) <> 0` THENL
     [DISCH_TAC,
      REWRITE_TAC [GSYM extreal_11] THEN ASM_SIMP_TAC std_ss [normal_real] THEN
      ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN SIMP_TAC std_ss [extreal_of_num_def] THEN
      SIMP_TAC std_ss [extreal_pow_def] THEN SIMP_TAC std_ss [extreal_11] THEN
      MATCH_MP_TAC REAL_LT_IMP_NE THEN SIMP_TAC real_ss [REAL_LT_POW2]] THEN
     ASM_SIMP_TAC std_ss [] THEN
     `(!c y. 0 <= c /\ y <> NegInf ==> Normal c * y <> NegInf)`
      by METIS_TAC [mul_not_infty] THEN
     `(!c y. 0 <= c /\ y <> PosInf ==> Normal c * y <> PosInf)`
      by METIS_TAC [mul_not_infty] THEN
     Q_TAC SUFF_TAC `0 <= inv (real (2 pow i))` THENL
     [DISCH_TAC,
      REWRITE_TAC [REAL_LE_INV_EQ] THEN SIMP_TAC std_ss [GSYM extreal_le_def] THEN
      ASM_SIMP_TAC std_ss [normal_real, extreal_of_num_def] THEN
      SIMP_TAC std_ss [extreal_pow_def, extreal_le_def] THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN SIMP_TAC std_ss [REAL_LT_POW2]] THEN
     CONJ_TAC THEN (FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_SIMP_TAC std_ss [num_not_infty])] THEN

    Q.EXISTS_TAC `(\x. indicator_fn
          {x | x IN m_space m /\ &e / 2 pow i <= f x /\ f x < (&e + 1) / 2 pow i} x)` THEN
    Q.EXISTS_TAC `real (&e / 2 pow i)` THEN ASM_SIMP_TAC std_ss [normal_real] THEN
    FULL_SIMP_TAC std_ss [measure_space_def] THEN
    MATCH_MP_TAC IN_MEASURABLE_BOREL_INDICATOR THEN
    Q.EXISTS_TAC `{x | x IN m_space m /\ &e / 2 pow i <= f x /\ f x < (&e + 1) / 2 pow i}` THEN
    ASM_SIMP_TAC std_ss [space_def, IN_UNIV] THEN
    Q_TAC SUFF_TAC `{x | x IN m_space m /\ &e / 2 pow i <= f x /\ f x < (&e + 1) / 2 pow i} =
     PREIMAGE f {x | &e / 2 pow i <= x /\ x < (&e + 1) / 2 pow i} INTER
     space (m_space m, measurable_sets m)` THENL
    [DISC_RW_KILL,
     SIMP_TAC std_ss [PREIMAGE_def, space_def, INTER_UNIV] THEN
     SET_TAC []] THEN
    FULL_SIMP_TAC std_ss [IN_MEASURABLE] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN

    Q_TAC SUFF_TAC `(&e + 1) / 2 pow i <> NegInf /\ (&e + 1) / 2 pow i <> PosInf` THENL
   [STRIP_TAC THEN METIS_TAC [BOREL_MEASURABLE_SETS_CO, normal_real],
    ALL_TAC] THEN
   SIMP_TAC std_ss [extreal_div_def] THEN ONCE_REWRITE_TAC [mul_comm] THEN
    `2 pow i <> NegInf /\ 2 pow i <> PosInf` by
    METIS_TAC [pow_not_infty, num_not_infty] THEN
    `2 pow i = Normal (real (2 pow i))` by METIS_TAC [normal_real] THEN
    POP_ASSUM (fn th => ONCE_REWRITE_TAC [th]) THEN
    ONCE_REWRITE_TAC [extreal_inv_def] THEN
    Q_TAC SUFF_TAC `real (2 pow i) <> 0` THENL
    [DISCH_TAC,
     REWRITE_TAC [GSYM extreal_11] THEN ASM_SIMP_TAC std_ss [normal_real] THEN
     ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN SIMP_TAC std_ss [extreal_of_num_def] THEN
     SIMP_TAC std_ss [extreal_pow_def] THEN SIMP_TAC std_ss [extreal_11] THEN
     MATCH_MP_TAC REAL_LT_IMP_NE THEN SIMP_TAC real_ss [REAL_LT_POW2]] THEN
    ASM_SIMP_TAC std_ss [] THEN
    `(!c y. 0 <= c /\ y <> NegInf ==> Normal c * y <> NegInf)`
     by METIS_TAC [mul_not_infty] THEN
    `(!c y. 0 <= c /\ y <> PosInf ==> Normal c * y <> PosInf)`
     by METIS_TAC [mul_not_infty] THEN
    Q_TAC SUFF_TAC `0 <= inv (real (2 pow i))` THENL
    [DISCH_TAC,
     REWRITE_TAC [REAL_LE_INV_EQ] THEN SIMP_TAC std_ss [GSYM extreal_le_def] THEN
     ASM_SIMP_TAC std_ss [normal_real, extreal_of_num_def] THEN
     SIMP_TAC std_ss [extreal_pow_def, extreal_le_def] THEN
     MATCH_MP_TAC REAL_LT_IMP_LE THEN SIMP_TAC std_ss [REAL_LT_POW2]] THEN
    `!x y. (x <> NegInf /\ y <> NegInf ==> x + y <> NegInf)` by METIS_TAC [add_not_infty] THEN
    `!x y. (x <> PosInf /\ y <> PosInf ==> x + y <> PosInf)` by METIS_TAC [add_not_infty] THEN
    CONJ_TAC THEN (FIRST_X_ASSUM MATCH_MP_TAC THEN
     ASM_SIMP_TAC std_ss [] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
     SIMP_TAC std_ss [num_not_infty]), ALL_TAC] THEN

   CONJ_TAC THENL
   [Q.ABBREV_TAC `g = (\k x.
             &k / 2 pow i *
             indicator_fn
               {x | x IN m_space m /\ &k / 2 pow i <= f x /\ f x < (&k + 1) / 2 pow i} x)` THEN

    Q_TAC SUFF_TAC `FINITE s /\ sigma_algebra (m_space m, measurable_sets m) /\
     (!i. i IN s ==> g i IN measurable (m_space m, measurable_sets m) Borel) /\
     (!i x. i IN s /\ x IN space (m_space m, measurable_sets m) ==> g i x <> NegInf) /\
     (!x. x IN space (m_space m, measurable_sets m) ==>
      ((\x. SIGMA
     (\k.
        &k / 2 pow i *
        indicator_fn
          {x | x IN m_space m /\ &k / 2 pow i <= f x /\ f x < (&k + 1) / 2 pow i} x) s) x =
      SIGMA (\i. g i x) s))` THENL
   [DISCH_THEN (MP_TAC o MATCH_MP IN_MEASURABLE_BOREL_SUM) THEN
    ASM_SIMP_TAC std_ss [], ALL_TAC] THEN
   Q.UNABBREV_TAC `g` THEN
   FULL_SIMP_TAC std_ss [measure_space_def, FINITE_COUNT] THEN
   SIMP_TAC std_ss [space_def, IN_UNIV] THEN CONJ_TAC THENL
   [ALL_TAC,
    RW_TAC std_ss [lt_infty] THEN MATCH_MP_TAC lte_trans THEN
    Q.EXISTS_TAC `0` THEN SIMP_TAC std_ss [GSYM lt_infty, num_not_infty] THEN
    MATCH_MP_TAC le_mul THEN SIMP_TAC std_ss [extreal_div_def, indicator_fn_def] THEN
    CONJ_TAC THENL
    [ALL_TAC, COND_CASES_TAC THEN
     SIMP_TAC real_ss [le_refl, extreal_of_num_def, extreal_le_def]] THEN
    MATCH_MP_TAC le_mul THEN SIMP_TAC std_ss [le_num] THEN
    `2 pow i <> NegInf /\ 2 pow i <> PosInf` by
    METIS_TAC [pow_not_infty, num_not_infty] THEN
    `2 pow i = Normal (real (2 pow i))` by METIS_TAC [normal_real] THEN
    POP_ASSUM (fn th => ONCE_REWRITE_TAC [th]) THEN
    SIMP_TAC real_ss [extreal_inv_def] THEN
    COND_CASES_TAC THEN SIMP_TAC std_ss [le_infty] THEN
    SIMP_TAC std_ss [extreal_of_num_def, extreal_le_def] THEN
    SIMP_TAC std_ss [REAL_LE_INV_EQ] THEN SIMP_TAC std_ss [GSYM extreal_le_def] THEN
    ASM_SIMP_TAC std_ss [normal_real, GSYM extreal_of_num_def] THEN
    SIMP_TAC std_ss [extreal_of_num_def, extreal_pow_def, extreal_le_def] THEN
    MATCH_MP_TAC POW_POS THEN SIMP_TAC real_ss []] THEN
   RW_TAC std_ss [] THEN MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL THEN
   Q.EXISTS_TAC `(\x. indicator_fn
          {x | x IN m_space m /\ &i' / 2 pow i <= f x /\ f x < (&i' + 1) / 2 pow i} x)` THEN
   Q.EXISTS_TAC `real (&i' / 2 pow i)` THEN
   Q_TAC SUFF_TAC `&i' / 2 pow i <> NegInf /\ &i' / 2 pow i <> PosInf` THENL
   [STRIP_TAC,
    SIMP_TAC std_ss [extreal_div_def] THEN ONCE_REWRITE_TAC [mul_comm] THEN
    `2 pow i <> NegInf /\ 2 pow i <> PosInf` by
    METIS_TAC [pow_not_infty, num_not_infty] THEN
    `2 pow i = Normal (real (2 pow i))` by METIS_TAC [normal_real] THEN
    POP_ASSUM (fn th => ONCE_REWRITE_TAC [th]) THEN
    ONCE_REWRITE_TAC [extreal_inv_def] THEN
    Q_TAC SUFF_TAC `real (2 pow i) <> 0` THENL
    [DISCH_TAC,
     REWRITE_TAC [GSYM extreal_11] THEN ASM_SIMP_TAC std_ss [normal_real] THEN
     ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN SIMP_TAC std_ss [extreal_of_num_def] THEN
     SIMP_TAC std_ss [extreal_pow_def] THEN SIMP_TAC std_ss [extreal_11] THEN
     MATCH_MP_TAC REAL_LT_IMP_NE THEN SIMP_TAC real_ss [REAL_LT_POW2]] THEN
    ASM_SIMP_TAC std_ss [] THEN
    `(!c y. 0 <= c /\ y <> NegInf ==> Normal c * y <> NegInf)`
     by METIS_TAC [mul_not_infty] THEN
    `(!c y. 0 <= c /\ y <> PosInf ==> Normal c * y <> PosInf)`
     by METIS_TAC [mul_not_infty] THEN
    Q_TAC SUFF_TAC `0 <= inv (real (2 pow i))` THENL
    [DISCH_TAC,
     REWRITE_TAC [REAL_LE_INV_EQ] THEN SIMP_TAC std_ss [GSYM extreal_le_def] THEN
     ASM_SIMP_TAC std_ss [normal_real, extreal_of_num_def] THEN
     SIMP_TAC std_ss [extreal_pow_def, extreal_le_def] THEN
     MATCH_MP_TAC REAL_LT_IMP_LE THEN SIMP_TAC std_ss [REAL_LT_POW2]] THEN
    CONJ_TAC THEN (FIRST_X_ASSUM MATCH_MP_TAC THEN
     ASM_SIMP_TAC std_ss [num_not_infty])] THEN
   ASM_SIMP_TAC std_ss [normal_real] THEN
   MATCH_MP_TAC IN_MEASURABLE_BOREL_INDICATOR THEN
   Q.EXISTS_TAC `{x | x IN m_space m /\ &i' / 2 pow i <= f x /\ f x < (&i' + 1) / 2 pow i}` THEN
   ASM_SIMP_TAC std_ss [] THEN
   Q_TAC SUFF_TAC
   `{x | x IN m_space m /\ &i' / 2 pow i <= f x /\ f x < (&i' + 1) / 2 pow i} =
    PREIMAGE f {x | &i' / 2 pow i <= x /\ x < (&i' + 1) / 2 pow i} INTER
    space (m_space m,measurable_sets m)` THENL
   [DISC_RW_KILL,
    SIMP_TAC std_ss [PREIMAGE_def, space_def, INTER_UNIV] THEN
    SET_TAC []] THEN
   FULL_SIMP_TAC std_ss [IN_MEASURABLE] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN

   Q_TAC SUFF_TAC `(&i' + 1) / 2 pow i <> NegInf /\ (&i' + 1) / 2 pow i <> PosInf` THENL
   [STRIP_TAC THEN METIS_TAC [BOREL_MEASURABLE_SETS_CO, normal_real],
    ALL_TAC] THEN
   SIMP_TAC std_ss [extreal_div_def] THEN ONCE_REWRITE_TAC [mul_comm] THEN
    `2 pow i <> NegInf /\ 2 pow i <> PosInf` by
    METIS_TAC [pow_not_infty, num_not_infty] THEN
    `2 pow i = Normal (real (2 pow i))` by METIS_TAC [normal_real] THEN
    POP_ASSUM (fn th => ONCE_REWRITE_TAC [th]) THEN
    ONCE_REWRITE_TAC [extreal_inv_def] THEN
    Q_TAC SUFF_TAC `real (2 pow i) <> 0` THENL
    [DISCH_TAC,
     REWRITE_TAC [GSYM extreal_11] THEN ASM_SIMP_TAC std_ss [normal_real] THEN
     ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN SIMP_TAC std_ss [extreal_of_num_def] THEN
     SIMP_TAC std_ss [extreal_pow_def] THEN SIMP_TAC std_ss [extreal_11] THEN
     MATCH_MP_TAC REAL_LT_IMP_NE THEN SIMP_TAC real_ss [REAL_LT_POW2]] THEN
    ASM_SIMP_TAC std_ss [] THEN
    `(!c y. 0 <= c /\ y <> NegInf ==> Normal c * y <> NegInf)`
     by METIS_TAC [mul_not_infty] THEN
    `(!c y. 0 <= c /\ y <> PosInf ==> Normal c * y <> PosInf)`
     by METIS_TAC [mul_not_infty] THEN
    Q_TAC SUFF_TAC `0 <= inv (real (2 pow i))` THENL
    [DISCH_TAC,
     REWRITE_TAC [REAL_LE_INV_EQ] THEN SIMP_TAC std_ss [GSYM extreal_le_def] THEN
     ASM_SIMP_TAC std_ss [normal_real, extreal_of_num_def] THEN
     SIMP_TAC std_ss [extreal_pow_def, extreal_le_def] THEN
     MATCH_MP_TAC REAL_LT_IMP_LE THEN SIMP_TAC std_ss [REAL_LT_POW2]] THEN
    `!x y. (x <> NegInf /\ y <> NegInf ==> x + y <> NegInf)` by METIS_TAC [add_not_infty] THEN
    `!x y. (x <> PosInf /\ y <> PosInf ==> x + y <> PosInf)` by METIS_TAC [add_not_infty] THEN
    CONJ_TAC THEN (FIRST_X_ASSUM MATCH_MP_TAC THEN
     ASM_SIMP_TAC std_ss [] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
     SIMP_TAC std_ss [num_not_infty]), ALL_TAC] THEN

   CONJ_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC le_mul THEN CONJ_TAC THENL
    [ALL_TAC,
     SIMP_TAC std_ss [indicator_fn_def] THEN COND_CASES_TAC THEN
     SIMP_TAC real_ss [le_refl, extreal_le_def, extreal_of_num_def]] THEN
    SIMP_TAC std_ss [extreal_div_def] THEN MATCH_MP_TAC le_mul THEN
    SIMP_TAC std_ss [le_num] THEN
    `2 pow i <> NegInf /\ 2 pow i <> PosInf` by
    METIS_TAC [pow_not_infty, num_not_infty] THEN
    `2 pow i = Normal (real (2 pow i))` by METIS_TAC [normal_real] THEN
    POP_ASSUM (fn th => ONCE_REWRITE_TAC [th]) THEN
    SIMP_TAC real_ss [extreal_inv_def] THEN
    COND_CASES_TAC THEN SIMP_TAC std_ss [le_infty] THEN
    SIMP_TAC std_ss [extreal_of_num_def, extreal_le_def] THEN
    SIMP_TAC std_ss [REAL_LE_INV_EQ] THEN SIMP_TAC std_ss [GSYM extreal_le_def] THEN
    ASM_SIMP_TAC std_ss [normal_real, GSYM extreal_of_num_def] THEN
    SIMP_TAC std_ss [extreal_of_num_def, extreal_pow_def, extreal_le_def] THEN
    MATCH_MP_TAC POW_POS THEN SIMP_TAC real_ss [], ALL_TAC] THEN
   CONJ_TAC THENL
   [ALL_TAC,
    GEN_TAC THEN
    MATCH_MP_TAC EXTREAL_SUM_IMAGE_POS THEN RW_TAC std_ss [FINITE_COUNT, IN_UNIV] THEN
    MATCH_MP_TAC le_mul THEN CONJ_TAC THENL
    [ALL_TAC,
     SIMP_TAC std_ss [indicator_fn_def] THEN COND_CASES_TAC THEN
     SIMP_TAC real_ss [le_refl, extreal_le_def, extreal_of_num_def]] THEN
    SIMP_TAC std_ss [extreal_div_def] THEN MATCH_MP_TAC le_mul THEN
    SIMP_TAC std_ss [le_num] THEN
    `2 pow i <> NegInf /\ 2 pow i <> PosInf` by
    METIS_TAC [pow_not_infty, num_not_infty] THEN
    `2 pow i = Normal (real (2 pow i))` by METIS_TAC [normal_real] THEN
    POP_ASSUM (fn th => ONCE_REWRITE_TAC [th]) THEN
    SIMP_TAC real_ss [extreal_inv_def] THEN
    COND_CASES_TAC THEN SIMP_TAC std_ss [le_infty] THEN
    SIMP_TAC std_ss [extreal_of_num_def, extreal_le_def] THEN
    SIMP_TAC std_ss [REAL_LE_INV_EQ] THEN SIMP_TAC std_ss [GSYM extreal_le_def] THEN
    ASM_SIMP_TAC std_ss [normal_real, GSYM extreal_of_num_def] THEN
    SIMP_TAC std_ss [extreal_of_num_def, extreal_pow_def, extreal_le_def] THEN
    MATCH_MP_TAC POW_POS THEN SIMP_TAC real_ss []] THEN
   Q_TAC SUFF_TAC `P (\x. &e / 2 pow i *
     (\x. indicator_fn {x | x IN m_space m /\ &e / 2 pow i <= f x /\ f x < (&e + 1) / 2 pow i}
       x) x)` THENL
   [SIMP_TAC std_ss [], ALL_TAC] THEN
   FIRST_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC std_ss [] THEN

   CONJ_TAC THENL
   [MATCH_MP_TAC IN_MEASURABLE_BOREL_INDICATOR THEN
    Q.EXISTS_TAC `{x | x IN m_space m /\ &e / 2 pow i <= f x /\ f x < (&e + 1) / 2 pow i}` THEN
    ASM_SIMP_TAC std_ss [space_def, IN_UNIV] THEN
    Q_TAC SUFF_TAC `{x | x IN m_space m /\ &e / 2 pow i <= f x /\ f x < (&e + 1) / 2 pow i} =
     PREIMAGE f {x | &e / 2 pow i <= x /\ x < (&e + 1) / 2 pow i} INTER
     space (m_space m,measurable_sets m)` THENL
    [DISC_RW_KILL,
     SIMP_TAC std_ss [PREIMAGE_def, space_def, INTER_UNIV] THEN
     SET_TAC []] THEN
    FULL_SIMP_TAC std_ss [IN_MEASURABLE] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    Q_TAC SUFF_TAC `&e / 2 pow i <> NegInf /\ &e / 2 pow i <> PosInf` THENL
    [STRIP_TAC,
     SIMP_TAC std_ss [extreal_div_def] THEN ONCE_REWRITE_TAC [mul_comm] THEN
     `2 pow i <> NegInf /\ 2 pow i <> PosInf` by
     METIS_TAC [pow_not_infty, num_not_infty] THEN
     `2 pow i = Normal (real (2 pow i))` by METIS_TAC [normal_real] THEN
     POP_ASSUM (fn th => ONCE_REWRITE_TAC [th]) THEN
     ONCE_REWRITE_TAC [extreal_inv_def] THEN
     Q_TAC SUFF_TAC `real (2 pow i) <> 0` THENL
     [DISCH_TAC,
      REWRITE_TAC [GSYM extreal_11] THEN ASM_SIMP_TAC std_ss [normal_real] THEN
      ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN SIMP_TAC std_ss [extreal_of_num_def] THEN
      SIMP_TAC std_ss [extreal_pow_def] THEN SIMP_TAC std_ss [extreal_11] THEN
      MATCH_MP_TAC REAL_LT_IMP_NE THEN SIMP_TAC real_ss [REAL_LT_POW2]] THEN
     ASM_SIMP_TAC std_ss [] THEN
     `(!c y. 0 <= c /\ y <> NegInf ==> Normal c * y <> NegInf)`
      by METIS_TAC [mul_not_infty] THEN
     `(!c y. 0 <= c /\ y <> PosInf ==> Normal c * y <> PosInf)`
      by METIS_TAC [mul_not_infty] THEN
     Q_TAC SUFF_TAC `0 <= inv (real (2 pow i))` THENL
     [DISCH_TAC,
      REWRITE_TAC [REAL_LE_INV_EQ] THEN SIMP_TAC std_ss [GSYM extreal_le_def] THEN
      ASM_SIMP_TAC std_ss [normal_real, extreal_of_num_def] THEN
      SIMP_TAC std_ss [extreal_pow_def, extreal_le_def] THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN SIMP_TAC std_ss [REAL_LT_POW2]] THEN
     CONJ_TAC THEN (FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_SIMP_TAC std_ss [num_not_infty])] THEN
    Q_TAC SUFF_TAC `(&e + 1) / 2 pow i <> NegInf /\ (&e + 1) / 2 pow i <> PosInf` THENL
   [STRIP_TAC THEN METIS_TAC [BOREL_MEASURABLE_SETS_CO, normal_real],
    ALL_TAC] THEN
   SIMP_TAC std_ss [extreal_div_def] THEN ONCE_REWRITE_TAC [mul_comm] THEN
    `2 pow i <> NegInf /\ 2 pow i <> PosInf` by
    METIS_TAC [pow_not_infty, num_not_infty] THEN
    `2 pow i = Normal (real (2 pow i))` by METIS_TAC [normal_real] THEN
    POP_ASSUM (fn th => ONCE_REWRITE_TAC [th]) THEN
    ONCE_REWRITE_TAC [extreal_inv_def] THEN
    Q_TAC SUFF_TAC `real (2 pow i) <> 0` THENL
    [DISCH_TAC,
     REWRITE_TAC [GSYM extreal_11] THEN ASM_SIMP_TAC std_ss [normal_real] THEN
     ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN SIMP_TAC std_ss [extreal_of_num_def] THEN
     SIMP_TAC std_ss [extreal_pow_def] THEN SIMP_TAC std_ss [extreal_11] THEN
     MATCH_MP_TAC REAL_LT_IMP_NE THEN SIMP_TAC real_ss [REAL_LT_POW2]] THEN
    ASM_SIMP_TAC std_ss [] THEN
    `(!c y. 0 <= c /\ y <> NegInf ==> Normal c * y <> NegInf)`
     by METIS_TAC [mul_not_infty] THEN
    `(!c y. 0 <= c /\ y <> PosInf ==> Normal c * y <> PosInf)`
     by METIS_TAC [mul_not_infty] THEN
    Q_TAC SUFF_TAC `0 <= inv (real (2 pow i))` THENL
    [DISCH_TAC,
     REWRITE_TAC [REAL_LE_INV_EQ] THEN SIMP_TAC std_ss [GSYM extreal_le_def] THEN
     ASM_SIMP_TAC std_ss [normal_real, extreal_of_num_def] THEN
     SIMP_TAC std_ss [extreal_pow_def, extreal_le_def] THEN
     MATCH_MP_TAC REAL_LT_IMP_LE THEN SIMP_TAC std_ss [REAL_LT_POW2]] THEN
    `!x y. (x <> NegInf /\ y <> NegInf ==> x + y <> NegInf)` by METIS_TAC [add_not_infty] THEN
    `!x y. (x <> PosInf /\ y <> PosInf ==> x + y <> PosInf)` by METIS_TAC [add_not_infty] THEN
    CONJ_TAC THEN (FIRST_X_ASSUM MATCH_MP_TAC THEN
     ASM_SIMP_TAC std_ss [] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
     SIMP_TAC std_ss [num_not_infty]), ALL_TAC] THEN

   CONJ_TAC THENL
   [SIMP_TAC std_ss [extreal_div_def] THEN MATCH_MP_TAC le_mul THEN
    SIMP_TAC std_ss [le_num] THEN
    `2 pow i <> NegInf /\ 2 pow i <> PosInf` by
    METIS_TAC [pow_not_infty, num_not_infty] THEN
    `2 pow i = Normal (real (2 pow i))` by METIS_TAC [normal_real] THEN
    POP_ASSUM (fn th => ONCE_REWRITE_TAC [th]) THEN
    SIMP_TAC real_ss [extreal_inv_def] THEN
    COND_CASES_TAC THEN SIMP_TAC std_ss [le_infty] THEN
    SIMP_TAC std_ss [extreal_of_num_def, extreal_le_def] THEN
    SIMP_TAC std_ss [REAL_LE_INV_EQ] THEN SIMP_TAC std_ss [GSYM extreal_le_def] THEN
    ASM_SIMP_TAC std_ss [normal_real, GSYM extreal_of_num_def] THEN
    SIMP_TAC std_ss [extreal_of_num_def, extreal_pow_def, extreal_le_def] THEN
    MATCH_MP_TAC POW_POS THEN SIMP_TAC real_ss [], ALL_TAC] THEN

   CONJ_TAC THENL
   [GEN_TAC THEN SIMP_TAC std_ss [indicator_fn_def] THEN COND_CASES_TAC THEN
    SIMP_TAC real_ss [le_refl, extreal_le_def, extreal_of_num_def],
    ALL_TAC] THEN
   Q_TAC SUFF_TAC `P
     (indicator_fn {x | x IN m_space m /\ &e / 2 pow i <= f x /\ f x < (&e + 1) / 2 pow i})` THENL
   [METIS_TAC [ETA_AX], ALL_TAC] THEN
   FIRST_ASSUM MATCH_MP_TAC THEN

   ONCE_REWRITE_TAC [METIS [subsets_def]
    ``measurable_sets m = subsets (m_space m, measurable_sets m)``] THEN
   Q_TAC SUFF_TAC `{x | x IN m_space m /\ &e / 2 pow i <= f x /\ f x < (&e + 1) / 2 pow i} =
     PREIMAGE f {x | &e / 2 pow i <= x /\ x < (&e + 1) / 2 pow i} INTER
     space (m_space m,measurable_sets m)` THENL
    [DISC_RW_KILL,
     SIMP_TAC std_ss [PREIMAGE_def, space_def, INTER_UNIV] THEN
     SET_TAC []] THEN
    FULL_SIMP_TAC std_ss [IN_MEASURABLE] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    Q_TAC SUFF_TAC `&e / 2 pow i <> NegInf /\ &e / 2 pow i <> PosInf` THENL
    [STRIP_TAC,
     SIMP_TAC std_ss [extreal_div_def] THEN ONCE_REWRITE_TAC [mul_comm] THEN
     `2 pow i <> NegInf /\ 2 pow i <> PosInf` by
     METIS_TAC [pow_not_infty, num_not_infty] THEN
     `2 pow i = Normal (real (2 pow i))` by METIS_TAC [normal_real] THEN
     POP_ASSUM (fn th => ONCE_REWRITE_TAC [th]) THEN
     ONCE_REWRITE_TAC [extreal_inv_def] THEN
     Q_TAC SUFF_TAC `real (2 pow i) <> 0` THENL
     [DISCH_TAC,
      REWRITE_TAC [GSYM extreal_11] THEN ASM_SIMP_TAC std_ss [normal_real] THEN
      ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN SIMP_TAC std_ss [extreal_of_num_def] THEN
      SIMP_TAC std_ss [extreal_pow_def] THEN SIMP_TAC std_ss [extreal_11] THEN
      MATCH_MP_TAC REAL_LT_IMP_NE THEN SIMP_TAC real_ss [REAL_LT_POW2]] THEN
     ASM_SIMP_TAC std_ss [] THEN
     `(!c y. 0 <= c /\ y <> NegInf ==> Normal c * y <> NegInf)`
      by METIS_TAC [mul_not_infty] THEN
     `(!c y. 0 <= c /\ y <> PosInf ==> Normal c * y <> PosInf)`
      by METIS_TAC [mul_not_infty] THEN
     Q_TAC SUFF_TAC `0 <= inv (real (2 pow i))` THENL
     [DISCH_TAC,
      REWRITE_TAC [REAL_LE_INV_EQ] THEN SIMP_TAC std_ss [GSYM extreal_le_def] THEN
      ASM_SIMP_TAC std_ss [normal_real, extreal_of_num_def] THEN
      SIMP_TAC std_ss [extreal_pow_def, extreal_le_def] THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN SIMP_TAC std_ss [REAL_LT_POW2]] THEN
     CONJ_TAC THEN (FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_SIMP_TAC std_ss [num_not_infty])] THEN
    Q_TAC SUFF_TAC `(&e + 1) / 2 pow i <> NegInf /\ (&e + 1) / 2 pow i <> PosInf` THENL
   [STRIP_TAC THEN METIS_TAC [BOREL_MEASURABLE_SETS_CO, normal_real],
    ALL_TAC] THEN
   SIMP_TAC std_ss [extreal_div_def] THEN ONCE_REWRITE_TAC [mul_comm] THEN
    `2 pow i <> NegInf /\ 2 pow i <> PosInf` by
    METIS_TAC [pow_not_infty, num_not_infty] THEN
    `2 pow i = Normal (real (2 pow i))` by METIS_TAC [normal_real] THEN
    POP_ASSUM (fn th => ONCE_REWRITE_TAC [th]) THEN
    ONCE_REWRITE_TAC [extreal_inv_def] THEN
    Q_TAC SUFF_TAC `real (2 pow i) <> 0` THENL
    [DISCH_TAC,
     REWRITE_TAC [GSYM extreal_11] THEN ASM_SIMP_TAC std_ss [normal_real] THEN
     ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN SIMP_TAC std_ss [extreal_of_num_def] THEN
     SIMP_TAC std_ss [extreal_pow_def] THEN SIMP_TAC std_ss [extreal_11] THEN
     MATCH_MP_TAC REAL_LT_IMP_NE THEN SIMP_TAC real_ss [REAL_LT_POW2]] THEN
    ASM_SIMP_TAC std_ss [] THEN
    `(!c y. 0 <= c /\ y <> NegInf ==> Normal c * y <> NegInf)`
     by METIS_TAC [mul_not_infty] THEN
    `(!c y. 0 <= c /\ y <> PosInf ==> Normal c * y <> PosInf)`
     by METIS_TAC [mul_not_infty] THEN
    Q_TAC SUFF_TAC `0 <= inv (real (2 pow i))` THENL
    [DISCH_TAC,
     REWRITE_TAC [REAL_LE_INV_EQ] THEN SIMP_TAC std_ss [GSYM extreal_le_def] THEN
     ASM_SIMP_TAC std_ss [normal_real, extreal_of_num_def] THEN
     SIMP_TAC std_ss [extreal_pow_def, extreal_le_def] THEN
     MATCH_MP_TAC REAL_LT_IMP_LE THEN SIMP_TAC std_ss [REAL_LT_POW2]] THEN
    `!x y. (x <> NegInf /\ y <> NegInf ==> x + y <> NegInf)` by METIS_TAC [add_not_infty] THEN
    `!x y. (x <> PosInf /\ y <> PosInf ==> x + y <> PosInf)` by METIS_TAC [add_not_infty] THEN
    CONJ_TAC THEN (FIRST_X_ASSUM MATCH_MP_TAC THEN
     ASM_SIMP_TAC std_ss [] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
     SIMP_TAC std_ss [num_not_infty]),
   ALL_TAC] THEN
  CONJ_TAC THENL
  [GEN_TAC THEN MATCH_MP_TAC le_mul THEN SIMP_TAC std_ss [indicator_fn_def] THEN
   CONJ_TAC THENL
   [ALL_TAC, COND_CASES_TAC THEN
    SIMP_TAC real_ss [le_refl, extreal_of_num_def, extreal_le_def]] THEN
   SIMP_TAC std_ss [extreal_of_num_def, extreal_pow_def, extreal_le_def] THEN
   MATCH_MP_TAC POW_POS THEN SIMP_TAC real_ss [], ALL_TAC] THEN

  Q_TAC SUFF_TAC `P (\x. 2 pow i *
     (\x. indicator_fn {x |  x IN m_space m /\ 2 pow i <= f x} x) x)` THENL
  [SIMP_TAC std_ss [], ALL_TAC] THEN
  FIRST_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC std_ss [] THEN

  CONJ_TAC THENL
  [MATCH_MP_TAC IN_MEASURABLE_BOREL_INDICATOR THEN
   Q.EXISTS_TAC `{x | x IN m_space m /\ 2 pow i <= f x}` THEN
   ASM_SIMP_TAC std_ss [space_def, IN_UNIV] THEN
   Q_TAC SUFF_TAC `{x | x IN m_space m /\ 2 pow i <= f x} =
   PREIMAGE f {x | 2 pow i <= x} INTER
    space (m_space m,measurable_sets m)` THENL
   [DISC_RW_KILL,
    SIMP_TAC std_ss [PREIMAGE_def, space_def, INTER_UNIV] THEN
    SET_TAC []] THEN
   FULL_SIMP_TAC std_ss [IN_MEASURABLE] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   `2 pow i <> NegInf /\ 2 pow i <> PosInf` by
    METIS_TAC [pow_not_infty, num_not_infty] THEN
   METIS_TAC [BOREL_MEASURABLE_SETS_CR, normal_real], ALL_TAC] THEN
  CONJ_TAC THENL
  [SIMP_TAC std_ss [extreal_of_num_def, extreal_pow_def, extreal_le_def] THEN
   MATCH_MP_TAC POW_POS THEN SIMP_TAC real_ss [], ALL_TAC] THEN
  CONJ_TAC THENL
  [GEN_TAC THEN SIMP_TAC std_ss [indicator_fn_def] THEN COND_CASES_TAC THEN
   SIMP_TAC real_ss [le_refl, extreal_of_num_def, extreal_le_def], ALL_TAC] THEN
  Q_TAC SUFF_TAC `P (indicator_fn {x | x IN m_space m /\ 2 pow i <= f x})` THENL
  [METIS_TAC [ETA_AX], ALL_TAC] THEN
  FIRST_ASSUM MATCH_MP_TAC THEN
  ONCE_REWRITE_TAC [METIS [subsets_def]
    ``measurable_sets m = subsets (m_space m, measurable_sets m)``] THEN
  Q_TAC SUFF_TAC `{x | x IN m_space m /\ 2 pow i <= f x} = PREIMAGE f {x | 2 pow i <= x} INTER
     space (m_space m,measurable_sets m)` THENL
  [DISC_RW_KILL,
   SIMP_TAC std_ss [PREIMAGE_def, space_def, INTER_UNIV] THEN
   SET_TAC []] THEN
  FULL_SIMP_TAC std_ss [IN_MEASURABLE] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  `2 pow i <> NegInf /\ 2 pow i <> PosInf` by
    METIS_TAC [pow_not_infty, num_not_infty] THEN
  METIS_TAC [BOREL_MEASURABLE_SETS_CR, normal_real]);

val density = new_definition ("density",
  ``density M f = (m_space M, measurable_sets M,
      (\A. if A IN measurable_sets M then
          pos_fn_integral M (\x. max 0 (f x * indicator_fn A x)) else 0))``);

val measure_space_density = store_thm ("measure_space_density",
  ``!M f. measure_space M /\ f IN measurable (m_space M, measurable_sets M) Borel
      ==> measure_space (density M f)``,
  RW_TAC std_ss [measure_space_def, density, m_space_def, measurable_sets_def] THENL
  [FULL_SIMP_TAC std_ss [positive_def, measure_def, measurable_sets_def] THEN
   `measure_space M` by METIS_TAC [measure_space_def, positive_def] THEN
   CONJ_TAC THENL
   [SIMP_TAC std_ss [indicator_fn_def, GSPECIFICATION, NOT_IN_EMPTY] THEN
    ASM_SIMP_TAC std_ss [mul_rzero, pos_fn_integral_zero, max_refl],
    ALL_TAC] THEN
   RW_TAC std_ss [] THEN MATCH_MP_TAC pos_fn_integral_pos THEN
   ASM_SIMP_TAC std_ss [le_max1], ALL_TAC] THEN POP_ASSUM MP_TAC THEN
  POP_ASSUM (ASSUME_TAC o ONCE_REWRITE_RULE [GSYM MEASURE_SPACE_REDUCE]) THEN
  `measure_space M` by METIS_TAC [measure_space_def, MEASURE_SPACE_REDUCE] THEN
  FULL_SIMP_TAC std_ss [countably_additive_alt_eq] THEN RW_TAC std_ss [] THEN
  `!i. A i IN measurable_sets M` by ASM_SET_TAC [] THEN
  Q_TAC SUFF_TAC `!i. (\x. max ((\x. 0) x) ((\x. f x * indicator_fn (A i) x) x)) IN
    measurable (m_space M, measurable_sets M) Borel` THENL
  [RW_TAC std_ss [],
   GEN_TAC THEN
   MATCH_MP_TAC IN_MEASURABLE_BOREL_MAX THEN ASM_SIMP_TAC std_ss [] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST THEN Q.EXISTS_TAC `0` THEN
    ASM_SIMP_TAC std_ss [], ALL_TAC] THEN
   MATCH_MP_TAC IN_MEASURABLE_BOREL_MUL_INDICATOR THEN
   METIS_TAC [subsets_def]] THEN
  ASM_SIMP_TAC std_ss [o_DEF] THEN
  Q_TAC SUFF_TAC `suminf (\x. pos_fn_integral M ((\x x'. max 0 (f x' * indicator_fn (A x) x')) x)) =
               pos_fn_integral M (\x'. suminf (\x. (\x x'. max 0 (f x' * indicator_fn (A x) x')) x x'))` THENL
  [ASM_SIMP_TAC std_ss [] THEN DISC_RW_KILL,
   MATCH_MP_TAC (GSYM pos_fn_integral_suminf) THEN
   ASM_SIMP_TAC std_ss [le_max1]] THEN
  `!x x'. max 0 (f x' * indicator_fn (A x) x') = max 0 (f x') * (indicator_fn (A x) x')` by
    (REPEAT GEN_TAC THEN SIMP_TAC std_ss [indicator_fn_def] THEN COND_CASES_TAC THEN
     SIMP_TAC std_ss [mul_rone, mul_rzero, max_refl]) THEN
  POP_ASSUM (fn th => REWRITE_TAC [th]) THEN
  Q_TAC SUFF_TAC `!x'. suminf (\x. max 0 (f x') * (\x. indicator_fn (A x) x') x) =
                       max 0 (f x') * suminf (\x. indicator_fn (A x) x')` THENL
  [SIMP_TAC std_ss [] THEN DISC_RW_KILL,
   GEN_TAC THEN MATCH_MP_TAC ext_suminf_cmul THEN
   SIMP_TAC std_ss [indicator_fn_def, le_max1] THEN
   GEN_TAC THEN COND_CASES_TAC THEN
   SIMP_TAC real_ss [le_refl, extreal_of_num_def, extreal_le_def]] THEN
  Q_TAC SUFF_TAC `!x'. suminf (\x. indicator_fn (A x) x') =
                       indicator_fn (BIGUNION (IMAGE A UNIV)) x'` THENL
  [DISC_RW_KILL,
   GEN_TAC THEN MATCH_MP_TAC indicator_fn_suminf THEN
   FULL_SIMP_TAC std_ss [disjoint_family, disjoint_family_on] THEN
   ASM_SET_TAC []] THEN
  AP_TERM_TAC THEN ABS_TAC THEN SIMP_TAC std_ss [IMAGE_DEF] THEN
  SIMP_TAC std_ss [indicator_fn_def] THEN COND_CASES_TAC THEN
  SIMP_TAC std_ss [mul_rone, mul_rzero, max_refl]);

val sup_cmult = store_thm ("sup_cmult",
  ``!f c. (!i. 0 <= f i) /\ 0 <= c ==>
          (sup (IMAGE (\n. c * f n) univ(:'a)) =
           c * sup (IMAGE f univ(:'a)))``,
  RW_TAC std_ss [] THEN ASM_CASES_TAC ``c = PosInf`` THENL
  [ASM_CASES_TAC ``!i. f i = 0`` THENL
   [`IMAGE f UNIV = {0}` by ASM_SET_TAC [] THEN
    `{0 | n | T} = {0}` by ASM_SET_TAC [] THEN
    ASM_SIMP_TAC std_ss [sup_sing, mul_rzero, IMAGE_DEF, IN_UNIV],
    ALL_TAC] THEN
   FULL_SIMP_TAC std_ss [] THEN
   Q_TAC SUFF_TAC `0 < sup (IMAGE f univ(:'a))` THENL
   [DISCH_TAC,
    REWRITE_TAC [GSYM sup_lt] THEN Q.EXISTS_TAC `f i` THEN
    CONJ_TAC THENL [ALL_TAC, METIS_TAC [le_lt]] THEN
    ONCE_REWRITE_TAC [GSYM SPECIFICATION] THEN
    SIMP_TAC std_ss [IN_IMAGE, IN_UNIV] THEN METIS_TAC []] THEN
   `sup (IMAGE f univ(:'a)) <> NegInf` by
   METIS_TAC [lt_infty, lt_trans, num_not_infty] THEN
   Q_TAC SUFF_TAC `PosInf * sup (IMAGE f univ(:'a)) = PosInf` THENL
   [DISC_RW_KILL,
    ASM_CASES_TAC ``sup (IMAGE f univ(:'a)) = PosInf`` THEN
    ASM_SIMP_TAC std_ss [extreal_mul_def] THEN
    `sup (IMAGE f univ(:'a)) = Normal (real (sup (IMAGE f univ(:'a))))`
     by METIS_TAC [normal_real] THEN
    POP_ASSUM (fn th => ONCE_REWRITE_TAC [th]) THEN
    ASM_SIMP_TAC std_ss [extreal_mul_def, GSYM extreal_lt_eq, GSYM extreal_11] THEN
    ASM_SIMP_TAC std_ss [GSYM extreal_of_num_def, normal_real] THEN
    ASM_SIMP_TAC std_ss [lt_imp_ne]] THEN
   SIMP_TAC std_ss [sup_eq] THEN CONJ_TAC THENL
   [SIMP_TAC std_ss [le_infty], ALL_TAC] THEN
   GEN_TAC THEN DISCH_THEN MATCH_MP_TAC THEN
   ONCE_REWRITE_TAC [GSYM SPECIFICATION] THEN SIMP_TAC std_ss [IN_IMAGE, IN_UNIV] THEN
   Q.EXISTS_TAC `i` THEN
   `f i <> NegInf` by
   METIS_TAC [lt_infty, lte_trans, num_not_infty] THEN
   ASM_CASES_TAC ``f i = PosInf`` THEN
   ASM_SIMP_TAC std_ss [extreal_mul_def] THEN
   `f i = Normal (real (f i))` by METIS_TAC [normal_real] THEN
   POP_ASSUM (fn th => ONCE_REWRITE_TAC [th]) THEN
   ASM_SIMP_TAC std_ss [extreal_mul_def, GSYM extreal_lt_eq, GSYM extreal_11] THEN
   ASM_SIMP_TAC std_ss [GSYM extreal_of_num_def, normal_real] THEN
   `0 < f i` by METIS_TAC [le_lt] THEN ASM_SIMP_TAC std_ss [],
   ALL_TAC] THEN
  `c <> NegInf` by METIS_TAC [lt_infty, lte_trans, num_not_infty] THEN
  `?r. c = Normal r` by METIS_TAC [extreal_cases] THEN
  ASM_SIMP_TAC std_ss [] THEN MATCH_MP_TAC sup_cmul THEN
  POP_ASSUM (ASSUME_TAC o ONCE_REWRITE_RULE [EQ_SYM_EQ]) THEN
  METIS_TAC [GSYM extreal_le_def, GSYM extreal_of_num_def, le_refl]);

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* ------------------------------------------------------------------------- *)

val SUP_mono = store_thm ("SUP_mono",
  ``!f g A B. (!n. n IN A ==> ?m. m IN B /\ f n <= g m) ==>
             sup {f n | n IN A} <= sup {g n | n IN B}``,
  RW_TAC std_ss [] THEN MATCH_MP_TAC sup_le_sup_imp THEN
  GEN_TAC THEN GEN_REWR_TAC LAND_CONV [GSYM SPECIFICATION] THEN
  RW_TAC std_ss [GSPECIFICATION] THEN FIRST_X_ASSUM (MP_TAC o Q.SPEC `n`) THEN
  RW_TAC std_ss [] THEN Q.EXISTS_TAC `g m` THEN
  GEN_REWR_TAC LAND_CONV [GSYM SPECIFICATION] THEN ASM_SET_TAC []);

val measure_Diff = store_thm ("measure_Diff",
  ``!m s t.
     measure_space m /\ s IN measurable_sets m /\
     t IN measurable_sets m /\ t SUBSET s /\ measure m t <> PosInf ==>
     (measure m (s DIFF t) = measure m s - measure m t)``,
  RW_TAC std_ss []
  THEN `!s. s IN measurable_sets m ==> measure m s <> NegInf` by METIS_TAC [MEASURE_SPACE_POSITIVE,positive_not_infty]
  THEN `measure m s = measure m (s DIFF t) + measure m t`
       by (MATCH_MP_TAC ADDITIVE THEN
           METIS_TAC [MEASURE_SPACE_ADDITIVE,UNION_DIFF,DISJOINT_DIFF,ADDITIVE,MEASURE_SPACE_DIFF])
  THEN `measure m t = Normal (real (measure m t))` by METIS_TAC [normal_real]
  THEN FIRST_ASSUM (fn th => ONCE_REWRITE_TAC [th])
  THEN REWRITE_TAC [eq_sub_ladd_normal] THEN METIS_TAC [normal_real]);

val positive_integral_mono_AE = store_thm ("positive_integral_mono_AE",
  ``!M u v. (!x. 0 <= u x) /\ (!x. 0 <= v x) /\
            measure_space M /\ AE M {x | u x <= v x} ==>
          pos_fn_integral M u <= pos_fn_integral M v``,
  RW_TAC std_ss [pos_fn_integral_def] THEN MATCH_MP_TAC sup_le_sup_imp THEN
  GEN_TAC THEN GEN_REWR_TAC LAND_CONV [GSYM SPECIFICATION] THEN
  RW_TAC std_ss [GSPECIFICATION] THEN
  GEN_REWR_TAC (QUANT_CONV o LAND_CONV) [GSYM SPECIFICATION] THEN
  FULL_SIMP_TAC std_ss [GSPECIFICATION, IN_psfis_eq] THEN
  FULL_SIMP_TAC std_ss [AE, ae_filter, GSPECIFICATION] THEN
  Q_TAC SUFF_TAC `AE M {x | x NOTIN N}` THENL
  [DISCH_TAC, MATCH_MP_TAC AE_not_in THEN ASM_SIMP_TAC std_ss []] THEN
  Q.ABBREV_TAC `nn = (\x. g x * indicator_fn (m_space M DIFF N) x)` THEN
  Q_TAC SUFF_TAC `AE M {x | g x <= nn x}` THENL
  [DISCH_TAC,
   FULL_SIMP_TAC std_ss [AE, ae_filter, GSPECIFICATION] THEN Q.EXISTS_TAC `N'` THEN
   FULL_SIMP_TAC std_ss [SUBSET_DEF, GSPECIFICATION] THEN RW_TAC std_ss [] THEN
   FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN POP_ASSUM MP_TAC THEN
   Q.UNABBREV_TAC `nn` THEN ONCE_REWRITE_TAC [MONO_NOT_EQ] THEN
   RW_TAC std_ss [indicator_fn_def, mul_rzero, mul_rone, le_refl] THEN
   ASM_SET_TAC []] THEN
  Q_TAC SUFF_TAC `!x. nn x <= v x` THENL
  [DISCH_TAC,
   GEN_TAC THEN Q.UNABBREV_TAC `nn` THEN ASM_SIMP_TAC std_ss [indicator_fn_def] THEN
   COND_CASES_TAC THEN ASM_SIMP_TAC std_ss [mul_rone, mul_rzero] THEN
   FULL_SIMP_TAC std_ss [SUBSET_DEF, GSPECIFICATION, IN_DIFF] THEN
   POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC [MONO_NOT_EQ] THEN
   RW_TAC std_ss [] THEN FIRST_ASSUM MATCH_MP_TAC THEN
   FULL_SIMP_TAC std_ss [GSYM extreal_lt_def] THEN METIS_TAC [lte_trans]] THEN
  FULL_SIMP_TAC std_ss [null_sets, GSPECIFICATION] THEN
  `?e. e NOTIN s` by METIS_TAC [num_FINITE_AVOID, pos_simple_fn_def] THEN
  Q_TAC SUFF_TAC `pos_simple_fn M nn (e INSERT s)
   (\i. if i = e then N else a i DIFF N)
   (\i. if i = e then 0 else x' i)` THENL
  [ALL_TAC,
   FULL_SIMP_TAC std_ss [pos_simple_fn_def] THEN
   Q.UNABBREV_TAC `nn` THEN RW_TAC real_ss [] THEN TRY (ASM_SET_TAC []) THENL
   [MATCH_MP_TAC le_mul THEN ASM_SIMP_TAC std_ss [indicator_fn_def] THEN
    COND_CASES_TAC THEN SIMP_TAC real_ss [le_refl, extreal_of_num_def, extreal_le_def],
    ALL_TAC,
    ONCE_REWRITE_TAC [METIS [subsets_def]
     ``measurable_sets M = subsets (m_space M, measurable_sets M)``] THEN
    MATCH_MP_TAC ALGEBRA_DIFF THEN `i IN s` by ASM_SET_TAC [] THEN
    FULL_SIMP_TAC std_ss [subsets_def, measure_space_def, sigma_algebra_def],
    METIS_TAC [FINITE_INSERT],
    SIMP_TAC std_ss [EXTENSION, IN_BIGUNION, IN_IMAGE, GSPECIFICATION, IN_DIFF] THEN
    GEN_TAC THEN EQ_TAC THENL
    [RW_TAC std_ss [] THEN UNDISCH_TAC ``x IN s'`` THEN ASM_REWRITE_TAC [] THEN
     `N SUBSET m_space M` by (MATCH_MP_TAC MEASURABLE_SETS_SUBSET_SPACE THEN ASM_SIMP_TAC std_ss []) THEN
     `!i. i IN s ==> a i SUBSET m_space M` by (RW_TAC std_ss [] THEN
      MATCH_MP_TAC MEASURABLE_SETS_SUBSET_SPACE THEN ASM_SIMP_TAC std_ss []) THEN
     ASM_SET_TAC [],
     ALL_TAC] THEN
    DISCH_TAC THEN `?i. x IN a i /\ i IN s` by ASM_SET_TAC [] THEN
    ASM_CASES_TAC ``x IN N`` THENL
    [Q.EXISTS_TAC `N` THEN ASM_SIMP_TAC std_ss [] THEN
     Q.EXISTS_TAC `e` THEN ASM_SET_TAC [],
     ALL_TAC] THEN
    Q.EXISTS_TAC `a i DIFF N` THEN CONJ_TAC THENL [ASM_SET_TAC [], ALL_TAC] THEN
    Q.EXISTS_TAC `i` THEN ASM_SET_TAC []] THEN
   ASM_CASES_TAC ``t IN N`` THEN ASM_SIMP_TAC std_ss [indicator_fn_def, IN_DIFF] THENL
   [SIMP_TAC std_ss [mul_rzero] THEN ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
    MATCH_MP_TAC EXTREAL_SUM_IMAGE_0 THEN ASM_SIMP_TAC std_ss [FINITE_INSERT] THEN
    RW_TAC std_ss [IN_INSERT, GSYM extreal_of_num_def, mul_rzero, mul_lzero, mul_rone] THEN
    ASM_SET_TAC [], ALL_TAC] THEN
   ASM_SIMP_TAC std_ss [mul_rone] THEN
   Q.ABBREV_TAC `f = (\i. Normal (if i = e then 0 else x' i) *
                          if t IN if i = e then N else a i DIFF N then 1 else 0)` THEN
   ONCE_REWRITE_TAC [SET_RULE ``e INSERT s = {e} UNION s``] THEN
   Q_TAC SUFF_TAC `(!x. x IN {e} UNION s ==> f x <> NegInf) \/
                   (!x. x IN {e} UNION s ==> f x <> PosInf) ==>
                   (SIGMA f ({e} UNION s) = SIGMA f {e} + SIGMA f s)` THENL
   [ALL_TAC,
    MATCH_MP_TAC EXTREAL_SUM_IMAGE_DISJOINT_UNION THEN
    ASM_SIMP_TAC std_ss [FINITE_SING] THEN ASM_SET_TAC []] THEN
   DISCH_TAC THEN Q_TAC SUFF_TAC `(SIGMA f ({e} UNION s) = SIGMA f {e} + SIGMA f s)` THENL
   [ALL_TAC,
    POP_ASSUM MATCH_MP_TAC THEN DISJ1_TAC THEN Q.UNABBREV_TAC `f` THEN
    RW_TAC std_ss [IN_UNION] THENL
    [SIMP_TAC std_ss [GSYM extreal_of_num_def, mul_lzero, num_not_infty],
     SIMP_TAC std_ss [GSYM extreal_of_num_def, mul_lzero, num_not_infty],
     SIMP_TAC std_ss [mul_rone, extreal_not_infty],
     SIMP_TAC std_ss [mul_rone, extreal_not_infty],
     SIMP_TAC std_ss [mul_rzero, num_not_infty],
     SIMP_TAC std_ss [mul_rzero, num_not_infty]]] THEN
   DISC_RW_KILL THEN Q.UNABBREV_TAC `f` THEN RW_TAC std_ss [EXTREAL_SUM_IMAGE_SING] THEN
   SIMP_TAC std_ss [mul_rzero, add_lzero] THEN
   FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP EXTREAL_SUM_IMAGE_EQ) THEN RW_TAC std_ss [] THENL
   [ALL_TAC, ASM_SET_TAC [], ASM_SET_TAC []] THEN
   DISJ1_TAC THEN RW_TAC std_ss [] THEN `x <> e` by ASM_SET_TAC [] THENL
   [SIMP_TAC std_ss [mul_rone, extreal_not_infty],
    SIMP_TAC std_ss [mul_rone, extreal_not_infty],
    SIMP_TAC std_ss [mul_rzero, num_not_infty],
    SIMP_TAC std_ss [mul_rzero, num_not_infty],
    SIMP_TAC std_ss [mul_rone, extreal_not_infty],
    ALL_TAC] THEN
   SIMP_TAC std_ss [mul_rzero, num_not_infty]] THEN DISCH_TAC THEN
  Q.EXISTS_TAC `pos_simple_fn_integral M (e INSERT s)
   (\i. if i = e then N else a i DIFF N) (\i. if i = e then 0 else x' i)` THEN
  CONJ_TAC THENL [METIS_TAC [], ALL_TAC] THEN
  SIMP_TAC std_ss [pos_simple_fn_integral_def] THEN
  Q.ABBREV_TAC `f = (\i. Normal (if i = e then 0 else x' i) *
     measure M (if i = e then N else a i DIFF N))` THEN
  ONCE_REWRITE_TAC [SET_RULE ``e INSERT s = {e} UNION s``] THEN
  Q_TAC SUFF_TAC `(!x. x IN {e} UNION s ==> f x <> NegInf) \/
                  (!x. x IN {e} UNION s ==> f x <> PosInf) ==>
                  (SIGMA f ({e} UNION s) = SIGMA f {e} + SIGMA f s)` THENL
  [ALL_TAC,
   MATCH_MP_TAC EXTREAL_SUM_IMAGE_DISJOINT_UNION THEN
   ASM_SIMP_TAC std_ss [FINITE_SING] THEN ASM_SET_TAC [pos_simple_fn_def]] THEN
  DISCH_TAC THEN Q_TAC SUFF_TAC `(SIGMA f ({e} UNION s) = SIGMA f {e} + SIGMA f s)` THENL
  [ALL_TAC,
   POP_ASSUM MATCH_MP_TAC THEN DISJ1_TAC THEN Q.UNABBREV_TAC `f` THEN
   RW_TAC std_ss [IN_UNION] THENL
   [SIMP_TAC std_ss [mul_rzero, num_not_infty], ASM_SET_TAC [],
    ALL_TAC] THEN
   SIMP_TAC std_ss [lt_infty] THEN MATCH_MP_TAC lte_trans THEN
   Q.EXISTS_TAC `0` THEN SIMP_TAC std_ss [GSYM lt_infty, num_not_infty] THEN
   MATCH_MP_TAC le_mul THEN SIMP_TAC std_ss [extreal_of_num_def, extreal_le_def] THEN
   FULL_SIMP_TAC std_ss [pos_simple_fn_def, measure_space_def, positive_def] THEN
   SIMP_TAC std_ss [GSYM extreal_of_num_def] THEN FIRST_ASSUM MATCH_MP_TAC THEN
   ONCE_REWRITE_TAC [METIS [subsets_def]
     ``measurable_sets M = subsets (m_space M, measurable_sets M)``] THEN
   MATCH_MP_TAC ALGEBRA_DIFF THEN
   FULL_SIMP_TAC std_ss [subsets_def, measure_space_def, sigma_algebra_def]] THEN
  DISC_RW_KILL THEN Q.UNABBREV_TAC `f` THEN RW_TAC std_ss [EXTREAL_SUM_IMAGE_SING] THEN
  SIMP_TAC std_ss [mul_rzero, add_lzero] THEN `FINITE s` by METIS_TAC [pos_simple_fn_def] THEN
  FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP EXTREAL_SUM_IMAGE_MONO) THEN RW_TAC std_ss [] THENL
  [DISJ1_TAC THEN RW_TAC std_ss [] THENL
   [SIMP_TAC std_ss [lt_infty] THEN MATCH_MP_TAC lte_trans THEN
    Q.EXISTS_TAC `0` THEN SIMP_TAC std_ss [GSYM lt_infty, num_not_infty] THEN
    MATCH_MP_TAC le_mul THEN SIMP_TAC std_ss [extreal_of_num_def, extreal_le_def] THEN
    FULL_SIMP_TAC std_ss [pos_simple_fn_def, measure_space_def, positive_def] THEN
    SIMP_TAC std_ss [GSYM extreal_of_num_def] THEN FIRST_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC std_ss [], ALL_TAC] THEN
   SIMP_TAC std_ss [lt_infty] THEN MATCH_MP_TAC lte_trans THEN
   Q.EXISTS_TAC `0` THEN SIMP_TAC std_ss [GSYM lt_infty, num_not_infty] THEN
   MATCH_MP_TAC le_mul THEN SIMP_TAC std_ss [extreal_of_num_def, extreal_le_def] THEN
   FULL_SIMP_TAC std_ss [pos_simple_fn_def, measure_space_def, positive_def] THEN
   SIMP_TAC std_ss [GSYM extreal_of_num_def] THEN FIRST_ASSUM MATCH_MP_TAC THEN
   ONCE_REWRITE_TAC [METIS [subsets_def]
     ``measurable_sets M = subsets (m_space M, measurable_sets M)``] THEN
   MATCH_MP_TAC ALGEBRA_DIFF THEN
   FULL_SIMP_TAC std_ss [subsets_def, measure_space_def, sigma_algebra_def],
   ALL_TAC] THEN
  ONCE_REWRITE_TAC [SET_RULE ``a DIFF b = a DIFF (a INTER b)``] THEN
  Q_TAC SUFF_TAC `measure M (a x DIFF a x INTER N) = measure M (a x) - measure M (a x INTER N)` THENL
  [ALL_TAC,
   MATCH_MP_TAC measure_Diff THEN FULL_SIMP_TAC std_ss [pos_simple_fn_def] THEN
   CONJ_TAC THENL
   [ONCE_REWRITE_TAC [METIS [subsets_def]
     ``measurable_sets M = subsets (m_space M, measurable_sets M)``] THEN
    MATCH_MP_TAC ALGEBRA_INTER THEN
    FULL_SIMP_TAC std_ss [subsets_def, measure_space_def, sigma_algebra_def],
    ALL_TAC] THEN
   CONJ_TAC THENL [ASM_SET_TAC [], ALL_TAC] THEN
   SIMP_TAC std_ss [lt_infty] THEN MATCH_MP_TAC let_trans THEN
   Q.EXISTS_TAC `measure M N` THEN CONJ_TAC THENL
   [ALL_TAC, METIS_TAC [lt_infty, num_not_infty]] THEN
   MATCH_MP_TAC INCREASING THEN ASM_SIMP_TAC std_ss [MEASURE_SPACE_INCREASING] THEN
   CONJ_TAC THENL [SET_TAC [], ALL_TAC] THEN
   ONCE_REWRITE_TAC [METIS [subsets_def]
     ``measurable_sets M = subsets (m_space M, measurable_sets M)``] THEN
   MATCH_MP_TAC ALGEBRA_INTER THEN
   FULL_SIMP_TAC std_ss [subsets_def, measure_space_def, sigma_algebra_def]] THEN
  DISC_RW_KILL THEN Q_TAC SUFF_TAC `measure M (a x INTER N) = 0` THENL
  [SIMP_TAC std_ss [le_refl, sub_rzero], ALL_TAC] THEN
  SIMP_TAC std_ss [GSYM le_antisym] THEN CONJ_TAC THENL
  [ALL_TAC,
   FULL_SIMP_TAC std_ss [measure_space_def, positive_def] THEN
   FIRST_ASSUM MATCH_MP_TAC THEN FULL_SIMP_TAC std_ss [pos_simple_fn_def] THEN
   ONCE_REWRITE_TAC [METIS [subsets_def]
     ``measurable_sets M = subsets (m_space M, measurable_sets M)``] THEN
   MATCH_MP_TAC ALGEBRA_INTER THEN
   FULL_SIMP_TAC std_ss [subsets_def, measure_space_def, sigma_algebra_def]] THEN
  `0 = measure M N` by METIS_TAC [] THEN FIRST_X_ASSUM (fn th => ONCE_REWRITE_TAC [th]) THEN
  MATCH_MP_TAC INCREASING THEN ASM_SIMP_TAC std_ss [MEASURE_SPACE_INCREASING] THEN
  CONJ_TAC THENL [SET_TAC [], ALL_TAC] THEN FULL_SIMP_TAC std_ss [pos_simple_fn_def] THEN
  ONCE_REWRITE_TAC [METIS [subsets_def]
    ``measurable_sets M = subsets (m_space M, measurable_sets M)``] THEN
  MATCH_MP_TAC ALGEBRA_INTER THEN
  FULL_SIMP_TAC std_ss [subsets_def, measure_space_def, sigma_algebra_def]);

val positive_integral_cong_AE = store_thm ("positive_integral_cong_AE",
  ``!M u v. (!x. 0 <= u x) /\ (!x. 0 <= v x) /\
            measure_space M /\ AE M {x | u x = v x} ==>
            (pos_fn_integral M u = pos_fn_integral M v)``,
  RW_TAC std_ss [GSYM le_antisym] THENL
  [MATCH_MP_TAC positive_integral_mono_AE THEN
   FULL_SIMP_TAC std_ss [AE, SUBSET_DEF, ae_filter, GSPECIFICATION] THEN
   METIS_TAC [], ALL_TAC] THEN
  MATCH_MP_TAC positive_integral_mono_AE THEN
  FULL_SIMP_TAC std_ss [AE, SUBSET_DEF, ae_filter, GSPECIFICATION] THEN
  METIS_TAC []);

val positive_integral_cong = store_thm ("positive_integral_cong",
  ``!M u v. (!x. 0 <= u x) /\ (!x. 0 <= v x) /\
            measure_space M /\ (!x. x IN m_space M ==> (u x = v x)) ==>
            (pos_fn_integral M u = pos_fn_integral M v)``,
  RW_TAC std_ss [] THEN MATCH_MP_TAC positive_integral_cong_AE THEN
  FULL_SIMP_TAC std_ss [AE, ae_filter, GSPECIFICATION] THEN
  `{x | x IN m_space M /\ u x <> v x} = {}` by ASM_SET_TAC [] THEN
  Q.EXISTS_TAC `{}` THEN ASM_SIMP_TAC std_ss [SUBSET_REFL, null_sets, GSPECIFICATION] THEN
  METIS_TAC [measure_space_def, positive_def, sigma_algebra_iff2]);

val positive_integral_null_set = store_thm ("positive_integral_null_set",
  ``!M N u. (!x. 0 <= u x) /\ measure_space M /\ N IN null_sets M ==>
     (pos_fn_integral M (\x. u x * indicator_fn N x) = 0)``,
  RW_TAC std_ss [null_sets, GSPECIFICATION] THEN
  Q_TAC SUFF_TAC `pos_fn_integral M (\x. u x * indicator_fn N x) =
                  pos_fn_integral M (\x. 0)` THENL
  [METIS_TAC [pos_fn_integral_zero], ALL_TAC] THEN
  `!x. 0 <= u x * indicator_fn N x` by
   (GEN_TAC THEN MATCH_MP_TAC le_mul THEN ASM_SIMP_TAC std_ss [indicator_fn_def] THEN
    COND_CASES_TAC THEN SIMP_TAC real_ss [le_refl, extreal_of_num_def, extreal_le_def]) THEN
  SIMP_TAC std_ss [GSYM le_antisym] THEN CONJ_TAC THENL
  [MATCH_MP_TAC positive_integral_mono_AE THEN ASM_SIMP_TAC std_ss [le_refl] THEN
   SIMP_TAC std_ss [AE, ae_filter, GSPECIFICATION] THEN Q.EXISTS_TAC `N` THEN
   ASM_SIMP_TAC std_ss [null_sets, GSPECIFICATION, SUBSET_DEF] THEN
   GEN_TAC THEN STRIP_TAC THEN POP_ASSUM MP_TAC THEN
   ONCE_REWRITE_TAC [MONO_NOT_EQ] THEN SIMP_TAC std_ss [indicator_fn_def] THEN
   SIMP_TAC std_ss [mul_rzero, le_refl],
   ALL_TAC] THEN
  MATCH_MP_TAC pos_fn_integral_mono THEN ASM_SIMP_TAC std_ss [le_refl]);

val positive_integral_Markov_inequality = store_thm ("positive_integral_Markov_inequality",
  ``!M A u c.
     measure_space M /\ u IN measurable (m_space M, measurable_sets M) Borel /\
     AE M {x | 0 <= u x} /\ A IN measurable_sets M /\ (!x. 0 <= u x) ==>
     measure M ({x | x IN m_space M /\ 1 <= &c * u x} INTER A) <=
      &c * pos_fn_integral M (\x. u x * indicator_fn A x)``,
  RW_TAC std_ss [] THEN
  Q.ABBREV_TAC `AA = ({x | x IN m_space M /\ 1 <= &c * u x} INTER A)` THEN
  Q_TAC SUFF_TAC `AA IN measurable_sets M` THENL
  [DISCH_TAC,
   Q.UNABBREV_TAC `AA` THEN
   ONCE_REWRITE_TAC [METIS [subsets_def]
     ``measurable_sets M = subsets (m_space M, measurable_sets M)``] THEN
   MATCH_MP_TAC ALGEBRA_INTER THEN
   CONJ_TAC THENL [METIS_TAC [measure_space_def, sigma_algebra_def], ALL_TAC] THEN
   CONJ_TAC THENL [ALL_TAC, ASM_SIMP_TAC std_ss [subsets_def]] THEN
   ONCE_REWRITE_TAC [SET_RULE ``{x | x IN m_space M /\ 1 <= c * u x} =
      {x | u x IN {x | 1 <= c * x}} INTER m_space M``] THEN
   REWRITE_TAC [GSYM PREIMAGE_def] THEN FULL_SIMP_TAC std_ss [IN_MEASURABLE] THEN
   FULL_SIMP_TAC std_ss [space_def, subsets_def] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
   ONCE_REWRITE_TAC [mul_comm] THEN ASM_CASES_TAC ``&c = 0`` THENL
   [ASM_SIMP_TAC real_ss [mul_rzero] THEN
    SIMP_TAC real_ss [extreal_of_num_def, extreal_le_def, GSPEC_F] THEN
    METIS_TAC [sigma_algebra_def, algebra_def],
    ALL_TAC] THEN
   `&c <> NegInf /\ &c <> PosInf` by METIS_TAC [num_not_infty] THEN
   `&c = Normal (real (&c))` by METIS_TAC [normal_real] THEN
   `0 <= &c` by METIS_TAC [le_num] THEN `0 < &c` by METIS_TAC [le_lt] THEN
   `0 < real (&c)` by METIS_TAC [extreal_lt_eq, normal_real, extreal_of_num_def] THEN
   ONCE_ASM_REWRITE_TAC [] THEN ASM_SIMP_TAC std_ss [le_ldiv] THEN
   `real (&c) <> 0` by METIS_TAC [REAL_LT_IMP_NE] THEN POP_ASSUM MP_TAC THEN
   SIMP_TAC std_ss [extreal_of_num_def, extreal_div_eq] THEN
   METIS_TAC [BOREL_MEASURABLE_SETS_CR]] THEN
  ASM_SIMP_TAC std_ss [GSYM pos_fn_integral_indicator] THEN
  Q_TAC SUFF_TAC `&c * pos_fn_integral M (\x. u x * indicator_fn A x) =
             pos_fn_integral M (\x. &c * (\x. u x * indicator_fn A x) x)` THENL
  [DISC_RW_KILL,
   `&c <> NegInf /\ &c <> PosInf` by METIS_TAC [num_not_infty] THEN
   `&c = Normal (real (&c))` by METIS_TAC [normal_real] THEN
   ONCE_ASM_REWRITE_TAC [] THEN MATCH_MP_TAC (GSYM pos_fn_integral_cmul) THEN
   POP_ASSUM (ASSUME_TAC o ONCE_REWRITE_RULE [EQ_SYM_EQ]) THEN
   ASM_SIMP_TAC std_ss [GSYM extreal_le_def, le_num, GSYM extreal_of_num_def] THEN
   SIMP_TAC std_ss [le_refl] THEN RW_TAC std_ss [] THEN MATCH_MP_TAC le_mul THEN
   ASM_SIMP_TAC std_ss [indicator_fn_def] THEN COND_CASES_TAC THEN
   SIMP_TAC real_ss [le_refl, extreal_of_num_def, extreal_le_def]] THEN
  MATCH_MP_TAC positive_integral_mono_AE THEN ASM_SIMP_TAC std_ss [] THEN
  CONJ_TAC THENL
  [GEN_TAC THEN SIMP_TAC std_ss [indicator_fn_def] THEN COND_CASES_TAC THEN
   SIMP_TAC real_ss [le_refl, extreal_of_num_def, extreal_le_def], ALL_TAC] THEN
  CONJ_TAC THENL
  [GEN_TAC THEN MATCH_MP_TAC le_mul THEN SIMP_TAC std_ss [le_num] THEN
   MATCH_MP_TAC le_mul THEN ASM_SIMP_TAC std_ss [indicator_fn_def] THEN
   COND_CASES_TAC THEN ASM_SIMP_TAC real_ss [le_refl, extreal_of_num_def, extreal_le_def],
   ALL_TAC] THEN
  FULL_SIMP_TAC std_ss [AE, ae_filter, GSPECIFICATION] THEN
  Q.EXISTS_TAC `N` THEN ASM_SIMP_TAC std_ss [] THEN
  Q_TAC SUFF_TAC `!x. (indicator_fn AA x <= &c * (u x * indicator_fn A x))` THENL
  [RW_TAC std_ss [], ALL_TAC] THEN
  Q.UNABBREV_TAC `AA` THEN RW_TAC std_ss [indicator_fn_def] THEN
  SIMP_TAC std_ss [mul_rone, mul_rzero, le_refl] THEN TRY (ASM_SET_TAC []) THEN
  MATCH_MP_TAC le_mul THEN ASM_SIMP_TAC std_ss [le_num]);

val extreal_not_lt = store_thm ("extreal_not_lt",
  ``!x y:extreal. ~(x < y) <=> y <= x``,
  REWRITE_TAC [TAUT `(~a = b) = (a = ~b)`] THEN
  SIMP_TAC std_ss [extreal_lt_def]);

val positive_integral_0_iff = store_thm ("positive_integral_0_iff",
  ``!u M. u IN measurable (m_space M, measurable_sets M) Borel /\
        measure_space M /\ AE M {x | 0 <= u x} /\ (!x. 0 <= u x) ==>
        ((pos_fn_integral M u = 0) =
         (measure M {x | x IN m_space M /\ u x <> 0} = 0))``,
  RW_TAC std_ss [] THEN
  Q.ABBREV_TAC `A = {x | x IN m_space M /\ u x <> 0}` THEN
  Q_TAC SUFF_TAC `pos_fn_integral M (\x. u x * indicator_fn A x) = pos_fn_integral M u` THENL
  [DISCH_TAC,
   MATCH_MP_TAC positive_integral_cong THEN Q.UNABBREV_TAC `A` THEN
   RW_TAC std_ss [indicator_fn_def, mul_rone, mul_rzero, le_refl] THEN
   ASM_SET_TAC []] THEN
  Q_TAC SUFF_TAC `A IN measurable_sets M` THENL
  [DISCH_TAC,
   Q.UNABBREV_TAC `A` THEN
   ONCE_REWRITE_TAC [SET_RULE ``{x | x IN m_space M /\ u x <> 0} =
     {x | u x IN {x | x <> 0}} INTER m_space M``] THEN
   REWRITE_TAC [GSYM PREIMAGE_def] THEN
   FULL_SIMP_TAC std_ss [IN_MEASURABLE, space_def, subsets_def] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   ONCE_REWRITE_TAC [SET_RULE ``{x | x <> 0} = UNIV DIFF {0}``] THEN
   `algebra Borel` by METIS_TAC [sigma_algebra_def] THEN
   MATCH_MP_TAC ALGEBRA_DIFF THEN
   ASM_SIMP_TAC std_ss [extreal_of_num_def, BOREL_MEASURABLE_SETS_SING] THEN
   ONCE_REWRITE_TAC [SET_RULE ``UNIV = UNIV DIFF {}``] THEN
   FULL_SIMP_TAC std_ss [algebra_def, GSYM SPACE_BOREL]] THEN
  Q_TAC SUFF_TAC `(measure M A = 0) ==> (pos_fn_integral M u = 0)` THENL
  [DISCH_TAC, POP_ASSUM MP_TAC THEN
   POP_ASSUM (ASSUME_TAC o ONCE_REWRITE_RULE [EQ_SYM_EQ]) THEN
   RW_TAC std_ss [] THEN MATCH_MP_TAC positive_integral_null_set THEN
   ASM_SIMP_TAC std_ss [null_sets, GSPECIFICATION]] THEN
  EQ_TAC THEN ASM_SIMP_TAC std_ss [] THEN DISCH_TAC THEN
  Q_TAC SUFF_TAC `!r n. 1 <= &n * r ==> 0 < &n * r /\ 0 <= r` THENL
  [DISCH_TAC,
   REPEAT GEN_TAC THEN DISCH_TAC THEN
   `0 < &n * r` by (MATCH_MP_TAC lte_trans THEN Q.EXISTS_TAC `1` THEN
       ASM_SIMP_TAC real_ss [extreal_of_num_def, extreal_lt_eq]) THEN
   ASM_SIMP_TAC std_ss [] THEN POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC [MONO_NOT_EQ] THEN
   RW_TAC std_ss [extreal_not_lt, GSYM extreal_lt_def] THEN
   `?x. r = -x` by (Q.EXISTS_TAC `-r` THEN RW_TAC std_ss [neg_neg]) THEN
   FULL_SIMP_TAC std_ss [mul_rneg] THEN ONCE_REWRITE_TAC [GSYM le_neg] THEN
   SIMP_TAC std_ss [neg_neg, neg_0] THEN MATCH_MP_TAC le_mul THEN
   SIMP_TAC std_ss [le_num, le_lt] THEN DISJ1_TAC THEN ONCE_REWRITE_TAC [GSYM lt_neg] THEN
   ASM_SIMP_TAC std_ss [neg_0]] THEN
  Q.ABBREV_TAC `MM = (\n:num. {x | x IN m_space M /\ 1 <= &n * u x})` THEN
  Q_TAC SUFF_TAC `0 = (sup {measure M (MM n INTER A) | n IN UNIV})` THENL
  [DISCH_TAC,
   Q_TAC SUFF_TAC `!n. measure M (MM n INTER A) <= 0` THENL
   [DISCH_TAC,
    GEN_TAC THEN Q.UNABBREV_TAC `MM` THEN SIMP_TAC std_ss [] THEN MATCH_MP_TAC le_trans THEN
    Q.EXISTS_TAC `&n * pos_fn_integral M (\x. u x * indicator_fn A x)` THEN
    CONJ_TAC THENL [ALL_TAC, ASM_SIMP_TAC std_ss [le_refl, mul_rzero]] THEN
    MATCH_MP_TAC positive_integral_Markov_inequality THEN
    ASM_SIMP_TAC std_ss []] THEN
   Q_TAC SUFF_TAC `!n. 0 <= measure M (MM n INTER A)` THENL
   [DISCH_TAC,
    GEN_TAC THEN FULL_SIMP_TAC std_ss [measure_space_def, positive_def] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ONCE_REWRITE_TAC [METIS [subsets_def]
     ``measurable_sets M = subsets (m_space M, measurable_sets M)``] THEN
    MATCH_MP_TAC ALGEBRA_INTER THEN
    CONJ_TAC THENL [METIS_TAC [measure_space_def, sigma_algebra_def], ALL_TAC] THEN
    CONJ_TAC THENL [ALL_TAC, ASM_SIMP_TAC std_ss [subsets_def]] THEN
    Q.UNABBREV_TAC `MM` THEN SIMP_TAC std_ss [] THEN
    ONCE_REWRITE_TAC [SET_RULE ``{x | x IN m_space M /\ 1 <= c * u x} =
      {x | u x IN {x | 1 <= c * x}} INTER m_space M``] THEN
    REWRITE_TAC [GSYM PREIMAGE_def] THEN FULL_SIMP_TAC std_ss [IN_MEASURABLE] THEN
    FULL_SIMP_TAC std_ss [space_def, subsets_def] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ONCE_REWRITE_TAC [mul_comm] THEN ASM_CASES_TAC ``&n = 0`` THENL
    [ASM_SIMP_TAC real_ss [mul_rzero] THEN
     SIMP_TAC real_ss [extreal_of_num_def, extreal_le_def, GSPEC_F] THEN
     METIS_TAC [sigma_algebra_def, algebra_def],
     ALL_TAC] THEN
    `&n <> NegInf /\ &n <> PosInf` by METIS_TAC [num_not_infty] THEN
    `&n = Normal (real (&n))` by METIS_TAC [normal_real] THEN
    `0 <= &n` by METIS_TAC [le_num] THEN `0 < &n` by METIS_TAC [le_lt] THEN
    `0 < real (&n)` by METIS_TAC [extreal_lt_eq, normal_real, extreal_of_num_def] THEN
    ONCE_ASM_REWRITE_TAC [] THEN ASM_SIMP_TAC std_ss [le_ldiv] THEN
    `real (&n) <> 0` by METIS_TAC [REAL_LT_IMP_NE] THEN POP_ASSUM MP_TAC THEN
    SIMP_TAC std_ss [extreal_of_num_def, extreal_div_eq] THEN
    METIS_TAC [BOREL_MEASURABLE_SETS_CR]] THEN
   `!n. measure M (MM n INTER A) = 0` by METIS_TAC [le_antisym] THEN
   ASM_SIMP_TAC std_ss [SET_RULE ``{0 | n IN univ(:num)} = {0}``] THEN
   SIMP_TAC std_ss [sup_sing]] THEN
  Q_TAC SUFF_TAC `!n. MM n IN measurable_sets M` THENL
  [DISCH_TAC,
   GEN_TAC THEN
   Q.UNABBREV_TAC `MM` THEN SIMP_TAC std_ss [] THEN
   ONCE_REWRITE_TAC [SET_RULE ``{x | x IN m_space M /\ 1 <= c * u x} =
     {x | u x IN {x | 1 <= c * x}} INTER m_space M``] THEN
   REWRITE_TAC [GSYM PREIMAGE_def] THEN FULL_SIMP_TAC std_ss [IN_MEASURABLE] THEN
   FULL_SIMP_TAC std_ss [space_def, subsets_def] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
   ONCE_REWRITE_TAC [mul_comm] THEN ASM_CASES_TAC ``&n = 0`` THENL
   [FIRST_X_ASSUM (fn th => SIMP_TAC std_ss [th, mul_rzero]) THEN
    SIMP_TAC real_ss [extreal_of_num_def, extreal_le_def, GSPEC_F] THEN
    METIS_TAC [sigma_algebra_def, algebra_def],
    ALL_TAC] THEN
   `&n <> NegInf /\ &n <> PosInf` by METIS_TAC [num_not_infty] THEN
   `&n = Normal (real (&n))` by METIS_TAC [normal_real] THEN
   `0 <= &n` by METIS_TAC [le_num] THEN `0 < &n` by METIS_TAC [le_lt] THEN
   `0 < real (&n)` by METIS_TAC [extreal_lt_eq, normal_real, extreal_of_num_def] THEN
   ONCE_ASM_REWRITE_TAC [] THEN ASM_SIMP_TAC std_ss [le_ldiv] THEN
   `real (&n) <> 0` by METIS_TAC [REAL_LT_IMP_NE] THEN POP_ASSUM MP_TAC THEN
   SIMP_TAC std_ss [extreal_of_num_def, extreal_div_eq] THEN
   METIS_TAC [BOREL_MEASURABLE_SETS_CR]] THEN
  Q_TAC SUFF_TAC `sup {measure M (MM n INTER A) | n IN univ(:num)} =
            measure M (BIGUNION {(MM n) INTER A | n IN UNIV})` THENL
  [DISCH_TAC,
   SIMP_TAC std_ss [GSYM IMAGE_DEF] THEN
   GEN_REWR_TAC (LAND_CONV o ONCE_DEPTH_CONV) [METIS []
               ``(MM n INTER A) = (\n. MM n INTER A) n``] THEN
   MATCH_MP_TAC (SIMP_RULE std_ss [o_DEF] MEASURE_COUNTABLE_INCREASING) THEN
   ASM_SIMP_TAC std_ss [] THEN CONJ_TAC THENL
   [RW_TAC std_ss [IN_FUNSET, IN_UNIV] THEN
    ONCE_REWRITE_TAC [METIS [subsets_def]
     ``measurable_sets M = subsets (m_space M, measurable_sets M)``] THEN
    MATCH_MP_TAC ALGEBRA_INTER THEN ASM_SIMP_TAC std_ss [subsets_def] THEN
    METIS_TAC [measure_space_def, sigma_algebra_def],
    ALL_TAC] THEN
   CONJ_TAC THENL
   [Q.UNABBREV_TAC `MM` THEN
    SIMP_TAC real_ss [mul_lzero, extreal_of_num_def, extreal_le_def] THEN
    SET_TAC [],
    ALL_TAC] THEN
   Q.UNABBREV_TAC `MM` THEN SIMP_TAC std_ss [SUBSET_DEF, GSPECIFICATION, IN_INTER] THEN
   RW_TAC std_ss [] THEN MATCH_MP_TAC le_trans THEN Q.EXISTS_TAC `&n * u x` THEN
   ASM_SIMP_TAC std_ss [] THEN ASM_CASES_TAC ``u (x:'a) = 0`` THENL
   [METIS_TAC [mul_rzero, le_refl], ALL_TAC] THEN MATCH_MP_TAC le_rmul_imp THEN
   CONJ_TAC THENL [METIS_TAC [le_lt], ALL_TAC] THEN
   SIMP_TAC real_ss [extreal_of_num_def, extreal_le_def, ADD1]] THEN
  Q_TAC SUFF_TAC `measure M (BIGUNION {MM n INTER A | n IN univ(:num)}) =
                  measure M {x | x IN m_space M /\ 0 < u x}` THENL
  [DISCH_TAC,
   AP_TERM_TAC THEN SIMP_TAC std_ss [EXTENSION, GSPECIFICATION, IN_BIGUNION, IN_UNIV] THEN
   GEN_TAC THEN ASM_CASES_TAC ``u (x:'a) = 0`` THENL
   [FIRST_ASSUM MP_TAC THEN SIMP_TAC std_ss [lt_refl] THEN RW_TAC std_ss [] THEN
    ASM_CASES_TAC ``x NOTIN s`` THEN POP_ASSUM MP_TAC THEN RW_TAC std_ss [] THEN
    Q.UNABBREV_TAC `MM` THEN SIMP_TAC std_ss [GSPECIFICATION, IN_INTER] THEN
    Q.EXISTS_TAC `x` THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
    SIMP_TAC std_ss [mul_rzero] THEN SIMP_TAC real_ss [extreal_of_num_def, extreal_le_def],
    ALL_TAC] THEN
   Q.UNABBREV_TAC `MM` THEN SIMP_TAC std_ss [GSPECIFICATION, IN_INTER] THEN EQ_TAC THENL
   [REPEAT STRIP_TAC THENL [ASM_SET_TAC [], ALL_TAC] THEN
    METIS_TAC [le_lt], ALL_TAC] THEN
   STRIP_TAC THEN ASM_CASES_TAC ``u (x:'a) = PosInf`` THENL
   [Q.EXISTS_TAC `{x | (x IN m_space M /\ 1 <= &1 * u x) /\ x IN A}` THEN
    CONJ_TAC THENL [ALL_TAC, SET_TAC []] THEN
    Q.UNABBREV_TAC `A` THEN ASM_SIMP_TAC std_ss [GSPECIFICATION] THEN
    SIMP_TAC std_ss [mul_lone, le_infty],
    ALL_TAC] THEN
   `u x <> NegInf` by METIS_TAC [lt_infty, lte_trans, num_not_infty] THEN
   `real (u x) <> 0` by METIS_TAC [extreal_11, extreal_of_num_def, normal_real] THEN
   `(1 / (u x)) <> PosInf` by METIS_TAC [lt_infty, normal_real, extreal_div_eq, extreal_of_num_def] THEN
   `?n. (1 / (u x)) <= &n` by METIS_TAC [SIMP_EXTREAL_ARCH] THEN
   Q.EXISTS_TAC `{x | (x IN m_space M /\ 1 <= &n * u x) /\ x IN A}` THEN
   CONJ_TAC THENL [ALL_TAC, SET_TAC []] THEN
   Q.UNABBREV_TAC `A` THEN SIMP_TAC std_ss [GSPECIFICATION] THEN
   ASM_SIMP_TAC std_ss [] THEN POP_ASSUM MP_TAC THEN
   MATCH_MP_TAC EQ_IMPLIES THEN ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
   `u x = Normal (real (u x))` by METIS_TAC [normal_real] THEN
   ONCE_ASM_REWRITE_TAC [] THEN MATCH_MP_TAC le_ldiv THEN
   METIS_TAC [extreal_lt_eq, extreal_of_num_def, normal_real]] THEN
  Q_TAC SUFF_TAC `measure M {x | x IN m_space M /\ 0 < u x} = 0` THENL
  [Q.UNABBREV_TAC `A` THEN MATCH_MP_TAC EQ_IMPLIES THEN AP_THM_TAC THEN
   AP_TERM_TAC THEN AP_TERM_TAC THEN SIMP_TAC std_ss [EXTENSION, GSPECIFICATION] THEN
   GEN_TAC THEN AP_TERM_TAC THEN EQ_TAC THENL [METIS_TAC [lt_imp_ne], ALL_TAC] THEN
   METIS_TAC [le_lt], ALL_TAC] THEN
  METIS_TAC []);

val pos_fn_integral_cmul_infty = store_thm
  ("pos_fn_integral_cmul_infty",``!m s. measure_space m /\ s IN measurable_sets m ==>
       (pos_fn_integral m (\x. PosInf * indicator_fn s x) = PosInf * (measure m s))``,
    RW_TAC std_ss [] THEN
    Q.ABBREV_TAC `fi = (\i:num x. &i)` THEN
    Q.ABBREV_TAC `f = (\x. PosInf)` THEN
    `!x. x IN m_space m ==> (sup (IMAGE (\i. fi i x) UNIV) = f x)`
         by (RW_TAC std_ss [] THEN Q.UNABBREV_TAC `fi` THEN
  	         Q.UNABBREV_TAC `f` THEN RW_TAC std_ss [] THEN
  	         Q_TAC SUFF_TAC `IMAGE (\i. &i) univ(:num) = (\x. ?n. x = &n)` THENL
  	         [RW_TAC std_ss [sup_num], ALL_TAC] THEN
  	         RW_TAC std_ss [EXTENSION,IN_IMAGE,IN_ABS,IN_UNIV]) THEN
    `!x. mono_increasing (\i. fi i x)`
         by (RW_TAC std_ss [ext_mono_increasing_def] THEN
             Q.UNABBREV_TAC `fi` THEN
             RW_TAC real_ss [extreal_of_num_def,extreal_le_def]) THEN
    `!i x. 0 <= fi i x` by (Q.UNABBREV_TAC `fi` THEN
    RW_TAC real_ss [extreal_of_num_def,extreal_le_def]) THEN
    `!x. 0 <= f x` by METIS_TAC [le_infty] THEN
    `!i. fi i IN measurable (m_space m, measurable_sets m) Borel`
         by (RW_TAC std_ss [] THEN
             MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST THEN
  	         METIS_TAC [measure_space_def]) THEN
    (MP_TAC o Q.SPECL [`m`,`f`,`fi`,`s`]) lebesgue_monotone_convergence_subset THEN
    RW_TAC std_ss [] THEN Q.UNABBREV_TAC `f` THEN
    Q.UNABBREV_TAC `fi` THEN FULL_SIMP_TAC real_ss [] THEN
    RW_TAC real_ss [extreal_of_num_def,pos_fn_integral_cmul_indicator] THEN
    RW_TAC std_ss [Once mul_comm,(Once o GSYM) extreal_mul_def] THEN
    `0 <= measure m s` by METIS_TAC [MEASURE_SPACE_POSITIVE,positive_def] THEN
    `measure m s <> NegInf` by METIS_TAC [lt_infty, lte_trans, num_not_infty] THEN
    ASM_CASES_TAC ``measure m s = PosInf`` THENL
    [ASM_REWRITE_TAC [extreal_mul_def] THEN REWRITE_TAC [sup_eq] THEN
     CONJ_TAC THENL
     [GEN_TAC THEN GEN_REWR_TAC LAND_CONV [GSYM SPECIFICATION] THEN
      SIMP_TAC std_ss [GSPECIFICATION, IN_IMAGE, IN_UNIV] THEN
      RW_TAC std_ss [le_infty], ALL_TAC] THEN
     GEN_TAC THEN DISCH_THEN (MATCH_MP_TAC) THEN ONCE_REWRITE_TAC [GSYM SPECIFICATION] THEN
     SIMP_TAC std_ss [IN_IMAGE, IN_UNIV] THEN Q.EXISTS_TAC `1` THEN
     SIMP_TAC real_ss [], ALL_TAC] THEN
    `?r. measure m s = Normal r` by METIS_TAC [extreal_cases] THEN
    `0 <= r` by METIS_TAC [GSYM extreal_le_def, GSYM extreal_of_num_def] THEN
    RW_TAC std_ss [sup_cmul] THEN
    Q_TAC SUFF_TAC `sup (IMAGE (\i. Normal (&i)) UNIV) = PosInf` THENL
    [METIS_TAC [mul_comm, extreal_mul_def], ALL_TAC] THEN
    Q_TAC SUFF_TAC`IMAGE (\i:num. Normal (&i)) UNIV = (\x. ?n. x = &n)` THENL
    [RW_TAC std_ss [sup_num], ALL_TAC] THEN
    RW_TAC std_ss [EXTENSION,IN_IMAGE,IN_ABS,IN_UNIV] THEN
    METIS_TAC [extreal_of_num_def]);

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* ------------------------------------------------------------------------- *)

val pos_fn_integral_cmult = store_thm ("pos_fn_integral_cmult",
  ``!f c m. measure_space m /\ 0 <= c /\
          f IN measurable (m_space m, measurable_sets m) Borel ==>
     (pos_fn_integral m (\x. max 0 (c * f x)) =
      c * pos_fn_integral m (\x. max 0 (f x)))``,

  RW_TAC std_ss [] THEN Q.ABBREV_TAC `g = (\x. max 0 (f x))` THEN
  Q_TAC SUFF_TAC `!x. max 0 (c * f x) = c * g x` THENL
  [DISC_RW_KILL,
   Q.UNABBREV_TAC `g` THEN RW_TAC std_ss [extreal_max_def, mul_rzero] THENL
   [UNDISCH_TAC ``0 <= c * f x`` THEN ONCE_REWRITE_TAC [MONO_NOT_EQ] THEN
    RW_TAC std_ss [GSYM extreal_lt_def] THEN ONCE_REWRITE_TAC [GSYM lt_neg] THEN
    SIMP_TAC std_ss [neg_0, GSYM mul_rneg] THEN MATCH_MP_TAC lt_mul THEN
    CONJ_TAC THENL
    [SIMP_TAC std_ss [extreal_lt_def] THEN POP_ASSUM MP_TAC THEN
     ONCE_REWRITE_TAC [MONO_NOT_EQ] THEN RW_TAC std_ss [] THEN
     `c = 0` by METIS_TAC [le_antisym] THEN ASM_SIMP_TAC std_ss [mul_lzero],
     ALL_TAC] THEN
    ONCE_REWRITE_TAC [GSYM lt_neg] THEN
    ASM_SIMP_TAC std_ss [neg_0, extreal_lt_def, neg_neg],
    ALL_TAC] THEN
   REWRITE_TAC [GSYM le_antisym] THEN CONJ_TAC THENL
   [METIS_TAC [le_mul], ALL_TAC] THEN METIS_TAC [le_lt, extreal_lt_def]] THEN
  Q_TAC SUFF_TAC `g IN measurable (m_space m,measurable_sets m) Borel` THENL
  [DISCH_TAC,
   Q.UNABBREV_TAC `g` THEN ONCE_REWRITE_TAC [METIS []
    ``!x. (\x. max 0 (f x)) = (\x. max ((\x. 0) x) ((\x. f x) x))``] THEN
   MATCH_MP_TAC IN_MEASURABLE_BOREL_MAX THEN
   ONCE_REWRITE_TAC [METIS [ETA_AX]  ``(\x. f x) = f``] THEN
   FULL_SIMP_TAC std_ss [measure_space_def] THEN
   MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST THEN METIS_TAC []] THEN
  `!x. 0 <= g x` by METIS_TAC [le_max1] THEN

  RW_TAC std_ss [] THEN ASM_CASES_TAC ``c = PosInf`` THENL
  [ASM_SIMP_TAC std_ss [] THEN
   Q_TAC SUFF_TAC `pos_fn_integral m (\x. (\x. c * g x) x *
      indicator_fn (({x | g x = 0} INTER m_space m) UNION ({x | 0 < g x} INTER m_space m)) x) =
    pos_fn_integral m (\x. (\x. c * g x) x * indicator_fn ({x | g x = 0} INTER m_space m) x) +
    pos_fn_integral m (\x. (\x. c * g x) x * indicator_fn ({x | 0 < g x} INTER m_space m) x)` THENL
   [ALL_TAC,
    MATCH_MP_TAC pos_fn_integral_disjoint_sets THEN ASM_SIMP_TAC std_ss [] THEN
    CONJ_TAC THENL
    [SIMP_TAC std_ss [DISJOINT_DEF, IN_INTER, EXTENSION, NOT_IN_EMPTY] THEN
     GEN_TAC THEN SIMP_TAC std_ss [GSPECIFICATION] THEN
     ASM_CASES_TAC ``g (x:'a) <> 0:extreal`` THEN FULL_SIMP_TAC std_ss [lt_refl],
     ALL_TAC] THEN
    CONJ_TAC THENL
    [`{x | g x = 0} = PREIMAGE g {x | x = 0}` by SET_TAC [PREIMAGE_def] THEN
     POP_ASSUM (fn th => REWRITE_TAC [th]) THEN FULL_SIMP_TAC std_ss [IN_MEASURABLE] THEN
     FULL_SIMP_TAC std_ss [space_def, subsets_def] THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN
     ONCE_REWRITE_TAC [SET_RULE ``{x | x = 0} = {0}``] THEN
     SIMP_TAC std_ss [BOREL_MEASURABLE_SETS_SING, extreal_of_num_def],
     ALL_TAC] THEN
    CONJ_TAC THENL
    [`{x | 0 < g x} = PREIMAGE g {x | 0 < x}` by SET_TAC [PREIMAGE_def] THEN
     POP_ASSUM (fn th => REWRITE_TAC [th]) THEN FULL_SIMP_TAC std_ss [IN_MEASURABLE] THEN
     FULL_SIMP_TAC std_ss [space_def, subsets_def] THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN
     SIMP_TAC std_ss [BOREL_MEASURABLE_SETS_OR, extreal_of_num_def],
     ALL_TAC] THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC IN_MEASURABLE_BOREL_TIMES THEN Q.EXISTS_TAC `(\x. PosInf)` THEN
     Q.EXISTS_TAC `g` THEN ASM_SIMP_TAC std_ss [] THEN
     MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST THEN Q.EXISTS_TAC `PosInf` THEN
     METIS_TAC [measure_space_def],
     ALL_TAC] THEN
    GEN_TAC THEN MATCH_MP_TAC le_mul THEN ASM_SIMP_TAC std_ss [le_infty]] THEN
   RW_TAC std_ss [] THEN
   Q_TAC SUFF_TAC `pos_fn_integral m (\x. PosInf * g x) =
    pos_fn_integral m (\x. PosInf * g x *
           indicator_fn
             ({x | g x = 0} INTER m_space m UNION
              {x | 0 < g x} INTER m_space m) x)` THENL
   [DISC_RW_KILL,
    MATCH_MP_TAC positive_integral_cong THEN ASM_SIMP_TAC std_ss [le_mul, le_infty] THEN
    CONJ_TAC THENL
    [GEN_TAC THEN MATCH_MP_TAC le_mul THEN ASM_SIMP_TAC std_ss [le_mul, le_infty] THEN
     SIMP_TAC std_ss [indicator_fn_pos_le], ALL_TAC] THEN
    RW_TAC std_ss [UNION_DEF, IN_INTER, GSPECIFICATION] THEN
    ASM_SIMP_TAC std_ss [indicator_fn_def, GSPECIFICATION] THEN
    ONCE_REWRITE_TAC [DISJ_COMM] THEN
    GEN_REWR_TAC (RAND_CONV o ONCE_DEPTH_CONV) [EQ_SYM_EQ] THEN
    ASM_SIMP_TAC std_ss [GSYM le_lt, mul_rone]] THEN
   ASM_SIMP_TAC std_ss [] THEN
   Q_TAC SUFF_TAC `pos_fn_integral m
    (\x. PosInf * g x * indicator_fn ({x | g x = 0} INTER m_space m) x) =
                   pos_fn_integral m (\x. 0)` THENL
   [DISC_RW_KILL,
    MATCH_MP_TAC positive_integral_cong THEN ASM_SIMP_TAC std_ss [le_refl] THEN
    CONJ_TAC THENL
    [GEN_TAC THEN MATCH_MP_TAC le_mul THEN ASM_SIMP_TAC std_ss [le_infty, le_mul] THEN
     SIMP_TAC std_ss [indicator_fn_pos_le], ALL_TAC] THEN
    RW_TAC std_ss [] THEN ASM_SIMP_TAC std_ss [indicator_fn_def, GSPECIFICATION, IN_INTER] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC std_ss [mul_rone, mul_rzero]] THEN
   ASM_SIMP_TAC std_ss [pos_fn_integral_zero, add_lzero] THEN
   Q_TAC SUFF_TAC `pos_fn_integral m (\x. g x *
    indicator_fn (({x | g x = 0} INTER m_space m) UNION ({x | 0 < g x} INTER m_space m)) x) =
     pos_fn_integral m (\x. g x * indicator_fn (({x | g x = 0} INTER m_space m)) x) +
     pos_fn_integral m (\x. g x * indicator_fn (({x | 0 < g x} INTER m_space m)) x)` THENL
   [SIMP_TAC std_ss [] THEN DISCH_TAC,
    MATCH_MP_TAC pos_fn_integral_disjoint_sets THEN ASM_SIMP_TAC std_ss [] THEN
    CONJ_TAC THENL
    [SIMP_TAC std_ss [DISJOINT_DEF, IN_INTER, EXTENSION, NOT_IN_EMPTY] THEN
     GEN_TAC THEN SIMP_TAC std_ss [GSPECIFICATION] THEN
     ASM_CASES_TAC ``g (x:'a) <> 0:extreal`` THEN FULL_SIMP_TAC std_ss [lt_refl],
     ALL_TAC] THEN
    CONJ_TAC THENL
    [`{x | g x = 0} = PREIMAGE g {x | x = 0}` by SET_TAC [PREIMAGE_def] THEN
     POP_ASSUM (fn th => REWRITE_TAC [th]) THEN FULL_SIMP_TAC std_ss [IN_MEASURABLE] THEN
     FULL_SIMP_TAC std_ss [space_def, subsets_def] THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN
     ONCE_REWRITE_TAC [SET_RULE ``{x | x = 0} = {0}``] THEN
     SIMP_TAC std_ss [BOREL_MEASURABLE_SETS_SING, extreal_of_num_def],
     ALL_TAC] THEN
    `{x | 0 < g x} = PREIMAGE g {x | 0 < x}` by SET_TAC [PREIMAGE_def] THEN
    POP_ASSUM (fn th => REWRITE_TAC [th]) THEN FULL_SIMP_TAC std_ss [IN_MEASURABLE] THEN
    FULL_SIMP_TAC std_ss [space_def, subsets_def] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    SIMP_TAC std_ss [BOREL_MEASURABLE_SETS_OR, extreal_of_num_def]] THEN
   Q_TAC SUFF_TAC `pos_fn_integral m g =
    pos_fn_integral m (\x. g x *
           indicator_fn
             ({x | g x = 0} INTER m_space m UNION
              {x | 0 < g x} INTER m_space m) x)` THENL
   [DISC_RW_KILL,
    MATCH_MP_TAC positive_integral_cong THEN ASM_SIMP_TAC std_ss [le_mul, indicator_fn_pos_le] THEN
    RW_TAC std_ss [] THEN ASM_SIMP_TAC std_ss [UNION_DEF, INTER_DEF, indicator_fn_def, GSPECIFICATION] THEN
    ONCE_REWRITE_TAC [DISJ_COMM] THEN
    GEN_REWR_TAC (RAND_CONV o ONCE_DEPTH_CONV) [EQ_SYM_EQ] THEN
    ASM_SIMP_TAC std_ss [GSYM le_lt, mul_rone]] THEN
   ASM_SIMP_TAC std_ss [] THEN
   Q_TAC SUFF_TAC `pos_fn_integral m
    (\x. g x * indicator_fn ({x | g x = 0} INTER m_space m) x) =
                   pos_fn_integral m (\x. 0)` THENL
   [DISC_RW_KILL,
    MATCH_MP_TAC positive_integral_cong THEN ASM_SIMP_TAC std_ss [le_refl] THEN
    CONJ_TAC THENL
    [GEN_TAC THEN MATCH_MP_TAC le_mul THEN ASM_SIMP_TAC std_ss [le_infty, le_mul] THEN
     SIMP_TAC std_ss [indicator_fn_pos_le], ALL_TAC] THEN
    RW_TAC std_ss [] THEN ASM_SIMP_TAC std_ss [indicator_fn_def, GSPECIFICATION, IN_INTER] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC std_ss [mul_rone, mul_rzero]] THEN
   ASM_SIMP_TAC std_ss [pos_fn_integral_zero, add_lzero] THEN
   Q_TAC SUFF_TAC `pos_fn_integral m
     (\x. PosInf * g x * indicator_fn ({x | 0 < g x} INTER m_space m) x) =
    pos_fn_integral m (\x. PosInf * indicator_fn ({x | 0 < g x} INTER m_space m) x)` THENL
   [DISC_RW_KILL,
    MATCH_MP_TAC positive_integral_cong THEN ASM_SIMP_TAC std_ss [le_infty] THEN
    ASM_SIMP_TAC std_ss [le_mul, indicator_fn_pos_le, le_infty] THEN
    RW_TAC std_ss [] THEN ASM_SIMP_TAC std_ss [indicator_fn_def, GSPECIFICATION, IN_INTER] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC std_ss [mul_rone, mul_rzero] THEN
    `g x <> NegInf` by METIS_TAC [lt_infty, lte_trans, num_not_infty] THEN
    ASM_CASES_TAC ``g x = PosInf`` THEN ASM_SIMP_TAC std_ss [extreal_mul_def] THEN
    `g x = Normal (real (g x))` by ASM_SIMP_TAC std_ss [normal_real] THEN
    POP_ASSUM (fn th => ONCE_REWRITE_TAC [th]) THEN
    SIMP_TAC std_ss [extreal_mul_def, GSYM extreal_11, GSYM extreal_lt_eq] THEN
    ASM_SIMP_TAC std_ss [GSYM extreal_of_num_def, normal_real] THEN
    `g x <> 0` by METIS_TAC [lt_imp_ne] THEN ASM_SIMP_TAC std_ss []] THEN
   Q_TAC SUFF_TAC `{x | 0 < g x} INTER m_space m IN measurable_sets m` THENL
   [DISCH_TAC,
    `{x | 0 < g x} = PREIMAGE g {x | 0 < x}` by SET_TAC [PREIMAGE_def] THEN
    POP_ASSUM (fn th => REWRITE_TAC [th]) THEN FULL_SIMP_TAC std_ss [IN_MEASURABLE] THEN
    FULL_SIMP_TAC std_ss [space_def, subsets_def] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    SIMP_TAC std_ss [BOREL_MEASURABLE_SETS_OR, extreal_of_num_def]] THEN
   ASM_SIMP_TAC std_ss [pos_fn_integral_cmul_infty] THEN
   ASM_CASES_TAC ``measure m ({x | 0 < g x} INTER m_space m) = 0`` THENL
   [Q_TAC SUFF_TAC `pos_fn_integral m
     (\x. g x * indicator_fn ({x | 0 < g x} INTER m_space m) x) = 0` THENL
    [DISC_RW_KILL,
     MATCH_MP_TAC positive_integral_null_set THEN
     ASM_SIMP_TAC std_ss [null_sets, GSPECIFICATION]] THEN
    SIMP_TAC std_ss [mul_rzero],
    ALL_TAC] THEN
   Q_TAC SUFF_TAC `measure m ({x | 0 < g x} INTER m_space m) =
      measure m ({x | x IN m_space m /\
       (\x. g x * indicator_fn ({x | 0 < g x} INTER m_space m) x) x <> 0})` THENL
   [DISCH_TAC,
    AP_TERM_TAC THEN SIMP_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER] THEN
    GEN_TAC THEN EQ_TAC THEN RW_TAC std_ss [] THENL
    [ASM_SIMP_TAC std_ss [indicator_fn_def, GSPECIFICATION, IN_INTER] THEN
     ASM_SIMP_TAC std_ss [lt_imp_ne, mul_rone], ALL_TAC] THEN
    POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC [MONO_NOT_EQ] THEN RW_TAC std_ss [] THEN
    FULL_SIMP_TAC std_ss [extreal_not_lt] THEN `g x = 0` by METIS_TAC [le_antisym] THEN
    ASM_SIMP_TAC std_ss [mul_lzero]] THEN
   Q.ABBREV_TAC `ff = (\x. g x * indicator_fn ({x | 0 < g x} INTER m_space m) x)` THEN
   `measure m {x | x IN m_space m /\ ff x <> 0} <> 0` by METIS_TAC [] THEN
   Q_TAC SUFF_TAC `measure m {x | x IN m_space m /\ ff x <> 0} <> 0 =
                   pos_fn_integral m ff <> 0` THENL
   [DISCH_TAC,
    ONCE_REWRITE_TAC [METIS [] ``(a = b:bool) = (~b = ~a)``] THEN
    SIMP_TAC std_ss [] THEN MATCH_MP_TAC positive_integral_0_iff THEN
    Q.UNABBREV_TAC `ff` THEN ASM_SIMP_TAC std_ss [le_mul, indicator_fn_pos_le] THEN
    CONJ_TAC THENL
    [ALL_TAC,
     SIMP_TAC std_ss [AE, ae_filter, GSPECIFICATION] THEN
     SIMP_TAC std_ss [GSPEC_F, EMPTY_SUBSET, null_sets, GSPECIFICATION] THEN
     Q.EXISTS_TAC `{}` THEN METIS_TAC [measure_space_def, SIGMA_ALGEBRA, positive_def, subsets_def]] THEN
    MATCH_MP_TAC IN_MEASURABLE_BOREL_TIMES THEN Q.EXISTS_TAC `g` THEN
    Q.EXISTS_TAC `indicator_fn ({x | 0 < g x} INTER m_space m)` THEN
    ASM_SIMP_TAC std_ss [] THEN MATCH_MP_TAC IN_MEASURABLE_BOREL_INDICATOR THEN
    Q.EXISTS_TAC `{x | 0 < g x} INTER m_space m` THEN
    CONJ_TAC THENL [METIS_TAC [measure_space_def], ALL_TAC] THEN
    ASM_SIMP_TAC std_ss [] THEN
    `{x | 0 < g x} = PREIMAGE g {x | 0 < x}` by SET_TAC [PREIMAGE_def] THEN
    POP_ASSUM (fn th => REWRITE_TAC [th]) THEN FULL_SIMP_TAC std_ss [IN_MEASURABLE] THEN
    FULL_SIMP_TAC std_ss [space_def, subsets_def] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    SIMP_TAC std_ss [BOREL_MEASURABLE_SETS_OR, extreal_of_num_def]] THEN
   Q_TAC SUFF_TAC `0 <= pos_fn_integral m ff` THENL
   [DISCH_TAC,
    MATCH_MP_TAC pos_fn_integral_pos THEN Q.UNABBREV_TAC `ff` THEN
    ASM_SIMP_TAC std_ss [le_mul, indicator_fn_pos_le]] THEN
   `0 < pos_fn_integral m ff` by METIS_TAC [le_lt] THEN
   `pos_fn_integral m ff <> NegInf` by METIS_TAC [lt_infty, num_not_infty, lte_trans] THEN
   Q_TAC SUFF_TAC `PosInf * pos_fn_integral m ff = PosInf` THENL
   [DISC_RW_KILL,
    ASM_CASES_TAC ``pos_fn_integral m ff = PosInf`` THEN ASM_SIMP_TAC std_ss [extreal_mul_def] THEN
    `pos_fn_integral m ff = Normal (real (pos_fn_integral m ff))` by METIS_TAC [normal_real] THEN
    POP_ASSUM (fn th => ONCE_REWRITE_TAC[th]) THEN REWRITE_TAC [extreal_mul_def] THEN
    ASM_SIMP_TAC std_ss [GSYM extreal_11, GSYM extreal_lt_eq, GSYM extreal_of_num_def] THEN
    ASM_SIMP_TAC std_ss [normal_real] THEN METIS_TAC []] THEN
   Q_TAC SUFF_TAC `0 <= measure m {x | x IN m_space m /\ ff x <> 0}` THENL
   [DISCH_TAC, FULL_SIMP_TAC std_ss [measure_space_def, positive_def] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN
    Q_TAC SUFF_TAC `{x | x IN m_space m /\ ff x <> 0} = PREIMAGE ff {x | x <> 0} INTER m_space m` THENL
    [DISC_RW_KILL, SIMP_TAC std_ss [PREIMAGE_def] THEN SET_TAC []] THEN
    Q_TAC SUFF_TAC `ff IN measurable (m_space m,measurable_sets m) Borel` THENL
    [DISCH_TAC,
     Q.UNABBREV_TAC `ff` THEN MATCH_MP_TAC IN_MEASURABLE_BOREL_TIMES THEN Q.EXISTS_TAC `g` THEN
     Q.EXISTS_TAC `indicator_fn ({x | 0 < g x} INTER m_space m)` THEN
     ASM_SIMP_TAC std_ss [measure_space_def, positive_def] THEN
     MATCH_MP_TAC IN_MEASURABLE_BOREL_INDICATOR THEN
     Q.EXISTS_TAC `{x | 0 < g x} INTER m_space m` THEN
     CONJ_TAC THENL [METIS_TAC [measure_space_def], ALL_TAC] THEN
     ASM_SIMP_TAC std_ss [] THEN
     `{x | 0 < g x} = PREIMAGE g {x | 0 < x}` by SET_TAC [PREIMAGE_def] THEN
     POP_ASSUM (fn th => REWRITE_TAC [th]) THEN FULL_SIMP_TAC std_ss [IN_MEASURABLE] THEN
     FULL_SIMP_TAC std_ss [space_def, subsets_def] THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN
     SIMP_TAC std_ss [BOREL_MEASURABLE_SETS_OR, extreal_of_num_def]] THEN
    FULL_SIMP_TAC std_ss [IN_MEASURABLE, subsets_def, space_def] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ONCE_REWRITE_TAC [SET_RULE ``{x | x <> 0} = UNIV DIFF {0}``] THEN
    MATCH_MP_TAC ALGEBRA_DIFF THEN SIMP_TAC std_ss [extreal_of_num_def, GSYM SPACE_BOREL] THEN
    ASSUME_TAC SIGMA_ALGEBRA_BOREL THEN `algebra Borel` by METIS_TAC [sigma_algebra_def] THEN
    ASM_SIMP_TAC std_ss [ALGEBRA_SPACE, BOREL_MEASURABLE_SETS_SING]] THEN
   `0 < measure m {x | x IN m_space m /\ ff x <> 0}` by METIS_TAC [le_lt] THEN
   Q.ABBREV_TAC `gg = {x | x IN m_space m /\ ff x <> 0}` THEN
   `measure m gg <> NegInf` by METIS_TAC [lt_infty, lte_trans, num_not_infty] THEN
   ASM_CASES_TAC ``measure m gg = PosInf`` THEN ASM_SIMP_TAC std_ss [extreal_mul_def] THEN
   `measure m gg = Normal (real (measure m gg))` by METIS_TAC [normal_real] THEN
   POP_ASSUM (fn th => ONCE_REWRITE_TAC[th]) THEN SIMP_TAC std_ss [extreal_mul_def] THEN
   ASM_SIMP_TAC std_ss [GSYM extreal_11, GSYM extreal_lt_eq, GSYM extreal_of_num_def] THEN
   ASM_SIMP_TAC std_ss [normal_real],
   ALL_TAC] THEN
  `c <> NegInf` by METIS_TAC [le_infty, le_trans, num_not_infty] THEN
  `c = Normal (real c)` by METIS_TAC [normal_real] THEN
  POP_ASSUM (fn th => ONCE_REWRITE_TAC [th]) THEN
  MATCH_MP_TAC pos_fn_integral_cmul THEN ASM_SIMP_TAC std_ss [] THEN
  ASM_SIMP_TAC std_ss [GSYM extreal_le_def, normal_real, GSYM extreal_of_num_def] THEN
  METIS_TAC [normal_real]);

val lebesgue_monotone_convergence_AE = store_thm
 ("lebesgue_monotone_convergence_AE",
  ``!m f fi.
     measure_space m /\
     (!i. fi i IN measurable (m_space m,measurable_sets m) Borel) /\
     (AE m {x | !i. fi i x <= fi (SUC i) x /\ 0 <= fi i x}) /\
     (!x. x IN m_space m ==>
        (sup (IMAGE (\i. fi i x) univ(:num)) = f x)) ==>
     (pos_fn_integral m (\x. max 0 (f x)) =
      sup (IMAGE (\i. pos_fn_integral m (\x. max 0 (fi i x))) univ(:num)))``,
  RW_TAC std_ss [] THEN
  FULL_SIMP_TAC std_ss [AE, ae_filter, GSPECIFICATION] THEN
  Q.ABBREV_TAC `ff = (\i x. if x IN m_space m DIFF N then fi i x else 0)` THEN
  Q_TAC SUFF_TAC `AE m {x | !i. ff i x = fi i x}` THENL
  [DISCH_TAC,
   MATCH_MP_TAC (REWRITE_RULE [AND_IMP_INTRO] AE_I) THEN
   Q.UNABBREV_TAC `ff` THEN Q.EXISTS_TAC `N` THEN
   ASM_SIMP_TAC std_ss [SUBSET_DEF, GSPECIFICATION, IN_DIFF] THEN
   GEN_TAC THEN REWRITE_TAC [GSYM AND_IMP_INTRO] THEN DISCH_TAC THEN
   ASM_REWRITE_TAC [] THEN ASM_CASES_TAC ``x NOTIN N`` THEN METIS_TAC []] THEN

  Q_TAC SUFF_TAC `pos_fn_integral m (\x. max 0 (f x)) =
    pos_fn_integral m (\x. max 0 (sup (IMAGE (\i. ff i x) univ(:num))))` THENL
  [DISC_RW_KILL,
   MATCH_MP_TAC positive_integral_cong_AE THEN ASM_SIMP_TAC std_ss [le_max1] THEN
   FULL_SIMP_TAC std_ss [GSPECIFICATION, AE, ae_filter] THEN
   Q.EXISTS_TAC `N'` THEN Q.UNABBREV_TAC `ff` THEN
   FULL_SIMP_TAC std_ss [SUBSET_DEF, GSPECIFICATION] THEN
   RW_TAC std_ss [] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
   ASM_SIMP_TAC std_ss [] THEN POP_ASSUM MP_TAC THEN
   ONCE_REWRITE_TAC [MONO_NOT_EQ] THEN RW_TAC std_ss []] THEN

  Q_TAC SUFF_TAC `pos_fn_integral m (\x. max 0 (sup (IMAGE (\i. ff i x) univ(:num)))) =
          sup (IMAGE (\i. pos_fn_integral m ((\i x. max 0 (ff i x)) i)) univ(:num))` THENL
  [DISC_RW_KILL,
   MATCH_MP_TAC lebesgue_monotone_convergence THEN ASM_SIMP_TAC std_ss [le_max1] THEN
   `(\x. 0) IN measurable (m_space m,measurable_sets m) Borel` by
      (MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST THEN
       METIS_TAC [measure_space_def]) THEN
   CONJ_TAC THENL
   [GEN_TAC THEN ONCE_REWRITE_TAC [METIS []
     ``!x. (\x. max 0 (ff i x)) = (\x. max ((\x. 0) x) ((\x. ff i x) x))``] THEN
    MATCH_MP_TAC IN_MEASURABLE_BOREL_MAX THEN Q.UNABBREV_TAC `ff` THEN
    FULL_SIMP_TAC std_ss [measure_space_def] THEN
    KNOW_TAC ``Borel = (m_space (space Borel, subsets Borel, (\x. 0)),
               measurable_sets (space Borel, subsets Borel, (\x. 0)))`` THENL
    [SIMP_TAC std_ss [m_space_def, measurable_sets_def, SPACE],
     DISC_RW_KILL] THEN
    Q_TAC SUFF_TAC `(\x. if x IN m_space m DIFF N then fi i x else 0) =
               (\x. if (\x. x IN m_space m DIFF N) x then (\x. fi i x) x else (\x. 0) x)` THENL
    [DISC_RW_KILL, SIMP_TAC std_ss []] THEN
    MATCH_MP_TAC measurable_If THEN
    ASM_SIMP_TAC std_ss [m_space_def, measurable_sets_def, SPACE, measure_space_def] THEN
    CONJ_TAC THENL
    [ONCE_REWRITE_TAC [METIS [ETA_AX] ``(\x. fi i x) = fi i``] THEN
     ASM_SIMP_TAC std_ss [], ALL_TAC] THEN
    ONCE_REWRITE_TAC [METIS [subsets_def]
    ``measurable_sets m = subsets (m_space m, measurable_sets m)``] THEN
    `{x | x IN m_space m /\ x IN m_space m DIFF N} = m_space m DIFF N` by SET_TAC [] THEN
    POP_ASSUM (fn th => REWRITE_TAC [th]) THEN MATCH_MP_TAC ALGEBRA_DIFF THEN
    FULL_SIMP_TAC std_ss [subsets_def, null_sets, GSPECIFICATION] THEN
    METIS_TAC [MEASURE_SPACE_MSPACE_MEASURABLE, measure_space_def, sigma_algebra_def],
    ALL_TAC] THEN
   CONJ_TAC THENL
   [GEN_TAC THEN Q.UNABBREV_TAC `ff` THEN SIMP_TAC std_ss [ext_mono_increasing_def] THEN
    RW_TAC std_ss [] THEN MATCH_MP_TAC max_le2_imp THEN SIMP_TAC std_ss [le_refl] THEN
    POP_ASSUM MP_TAC THEN UNDISCH_TAC ``{x | x IN m_space m /\
        ?i. ~(fi i x <= fi (SUC i) x) \/ ~(0 <= fi i x)} SUBSET N`` THEN
    FULL_SIMP_TAC std_ss [SUBSET_DEF, GSPECIFICATION, IN_DIFF] THEN
    DISCH_THEN (MP_TAC o Q.SPEC `x`) THEN FULL_SIMP_TAC std_ss [] THEN
    DISCH_TAC THEN Induct_on `i'` THEN ASM_SIMP_TAC std_ss [le_refl] THEN
    ASM_CASES_TAC ``i = SUC i'`` THEN ASM_SIMP_TAC std_ss [le_refl] THEN
    DISCH_TAC THEN MATCH_MP_TAC le_trans THEN Q.EXISTS_TAC `fi i' x` THEN
    ASM_SIMP_TAC std_ss [] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC arith_ss [],
    ALL_TAC] THEN
   GEN_TAC THEN Q_TAC SUFF_TAC `!i:num. 0 <= ff i x` THENL
   [RW_TAC std_ss [extreal_max_def] THEN
    UNDISCH_TAC ``~(0 <= sup (IMAGE (\i. ff i x) univ(:num)))`` THEN
    ONCE_REWRITE_TAC [MONO_NOT_EQ] THEN RW_TAC std_ss [] THEN
    ASM_CASES_TAC ``!i:num. ff i x = 0`` THENL
    [ASM_SIMP_TAC std_ss [IMAGE_DEF, IN_UNIV] THEN
     ONCE_REWRITE_TAC [SET_RULE ``{0 | i | T} = {0}``] THEN
     SIMP_TAC std_ss [sup_sing, le_refl],
     ALL_TAC] THEN
    SIMP_TAC std_ss [le_lt] THEN DISJ1_TAC THEN
    SIMP_TAC std_ss [GSYM sup_lt] THEN FULL_SIMP_TAC std_ss [] THEN
    Q.EXISTS_TAC `ff i x` THEN CONJ_TAC THENL [ALL_TAC, METIS_TAC [le_lt]] THEN
    ONCE_REWRITE_TAC [GSYM SPECIFICATION] THEN SET_TAC [],
    Q.UNABBREV_TAC `ff` THEN SIMP_TAC std_ss []] THEN
   GEN_TAC THEN ASM_CASES_TAC ``x IN m_space m DIFF N`` THEN
   ASM_SIMP_TAC std_ss [le_refl] THEN
   UNDISCH_TAC ``{x | x IN m_space m /\
       ?i. ~(fi i x <= fi (SUC i) x) \/ ~(0 <= fi i x)} SUBSET N`` THEN
   ONCE_REWRITE_TAC [MONO_NOT_EQ] THEN RW_TAC std_ss [SUBSET_DEF, GSPECIFICATION] THEN
   METIS_TAC [IN_DIFF]] THEN
  AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN
  SIMP_TAC std_ss [] THEN MATCH_MP_TAC positive_integral_cong_AE THEN
  FULL_SIMP_TAC std_ss [le_max1, AE, ae_filter, GSPECIFICATION] THEN
  Q.EXISTS_TAC `N'` THEN FULL_SIMP_TAC std_ss [SUBSET_DEF, GSPECIFICATION] THEN
  RW_TAC std_ss [] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  METIS_TAC []);

val pos_fn_integral_density' = store_thm ("pos_fn_integral_density'",
  ``!f g M. measure_space M /\
     f IN measurable (m_space M, measurable_sets M) Borel /\ AE M {x | 0 <= f x} /\
     g IN measurable (m_space M, measurable_sets M) Borel /\ (!x. 0 <= g x) ==>
     (pos_fn_integral (m_space M, measurable_sets M,
       (\A. if A IN measurable_sets M then pos_fn_integral M (\x. max 0 (f x * indicator_fn A x))
            else 0)) (\x. max 0 (g x)) = pos_fn_integral M (\x. max 0 (f x * g x)))``,

  RW_TAC std_ss [GSYM density] THEN
  Q_TAC SUFF_TAC `(\g. pos_fn_integral (density M f) (\x. max 0 (g x)) = pos_fn_integral M (\x. max 0 (f x * g x))) g` THENL
  [SIMP_TAC std_ss [], ALL_TAC] THEN
  MATCH_MP_TAC Induct_on_Borel_functions THEN Q.EXISTS_TAC `M` THEN
  ASM_SIMP_TAC std_ss [] THEN
  CONJ_TAC THENL
  [RW_TAC std_ss [] THEN
   Q_TAC SUFF_TAC `pos_fn_integral (density M f) (\x. max 0 (g' x)) = pos_fn_integral (density M f) (\x. max 0 (f' x))` THENL
   [DISC_RW_KILL,
    MATCH_MP_TAC positive_integral_cong THEN ASM_SIMP_TAC std_ss [le_max1] THEN
    CONJ_TAC THENL [ALL_TAC, METIS_TAC [density, m_space_def]] THEN
    MATCH_MP_TAC measure_space_density THEN ASM_SIMP_TAC std_ss []] THEN
   ASM_SIMP_TAC std_ss [] THEN MATCH_MP_TAC positive_integral_cong THEN
   ASM_SIMP_TAC std_ss [le_max1],
   ALL_TAC] THEN
  CONJ_TAC THENL
  [GEN_TAC THEN ONCE_REWRITE_TAC [METIS [extreal_max_def, indicator_fn_pos_le]
    ``!x. max 0 (indicator_fn A x) = indicator_fn A x``] THEN
   ONCE_REWRITE_TAC [METIS [ETA_AX] ``(\x. indicator_fn A x) = indicator_fn A``] THEN
   DISCH_TAC THEN `A IN measurable_sets (density M f)` by
    ASM_SIMP_TAC std_ss [density, measurable_sets_def] THEN
   `measure_space (density M f)` by METIS_TAC [measure_space_density] THEN
   ASM_SIMP_TAC std_ss [pos_fn_integral_indicator] THEN
   ASM_SIMP_TAC std_ss [density, measure_def],
   ALL_TAC] THEN
  CONJ_TAC THENL
  [RW_TAC std_ss [] THEN
   Q_TAC SUFF_TAC `pos_fn_integral (density M f) (\x. max 0 (c * f' x)) =
                   c * pos_fn_integral (density M f) (\x. max 0 (f' x))` THENL
   [DISC_RW_KILL,
    MATCH_MP_TAC pos_fn_integral_cmult THEN
    `measure_space (density M f)` by METIS_TAC [measure_space_density] THEN
    ASM_SIMP_TAC std_ss [density, m_space_def, measurable_sets_def]] THEN
   ASM_SIMP_TAC std_ss [] THEN
   Q_TAC SUFF_TAC `c * pos_fn_integral M (\x. max 0 ((\x. f x * f' x) x)) =
                   pos_fn_integral M (\x. max 0 (c * (\x. f x * f' x) x))` THENL
   [SIMP_TAC std_ss [] THEN DISC_RW_KILL,
    MATCH_MP_TAC (GSYM pos_fn_integral_cmult) THEN
    ASM_SIMP_TAC std_ss [] THEN MATCH_MP_TAC IN_MEASURABLE_BOREL_TIMES THEN
    METIS_TAC []] THEN
   AP_TERM_TAC THEN ABS_TAC THEN AP_TERM_TAC THEN
   METIS_TAC [mul_comm, mul_assoc],
   ALL_TAC] THEN
  CONJ_TAC THENL
  [RW_TAC std_ss [] THEN ASM_SIMP_TAC std_ss [add_ldistrib_pos] THEN
   Q_TAC SUFF_TAC `!x. max 0 (f' x + g' x) = max 0 (f' x) + max 0 (g' x)` THENL
   [DISC_RW_KILL, METIS_TAC [extreal_max_def, le_add]] THEN
   Q_TAC SUFF_TAC `pos_fn_integral (density M f) (\x. (\x. max 0 (f' x)) x + (\x. max 0 (g' x)) x) =
                   pos_fn_integral (density M f) (\x. max 0 (f' x)) +
                   pos_fn_integral (density M f) (\x. max 0 (g' x))` THENL
   [SIMP_TAC std_ss [] THEN DISC_RW_KILL,
    MATCH_MP_TAC pos_fn_integral_add THEN
    `measure_space (density M f)` by METIS_TAC [measure_space_density] THEN
    ASM_SIMP_TAC std_ss [le_max1] THEN ASM_SIMP_TAC std_ss [extreal_max_def] THEN
    ASM_SIMP_TAC std_ss [ETA_AX, density, m_space_def, measurable_sets_def]] THEN
   Q_TAC SUFF_TAC `pos_fn_integral M (\x. max 0 (f x * f' x + f x * g' x)) =
                   pos_fn_integral M (\x. (\x. max 0 (f x * f' x)) x + (\x. max 0 (f x * g' x)) x)` THENL
   [DISC_RW_KILL,
    MATCH_MP_TAC positive_integral_cong_AE THEN
    ASM_SIMP_TAC std_ss [le_max1, le_mul, le_add] THEN
    FULL_SIMP_TAC std_ss [AE, ae_filter, GSPECIFICATION, null_sets] THEN
    Q.EXISTS_TAC `N` THEN ASM_SIMP_TAC std_ss [] THEN
    FULL_SIMP_TAC std_ss [SUBSET_DEF, GSPECIFICATION] THEN RW_TAC std_ss [] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC std_ss [] THEN
    POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC [MONO_NOT_EQ] THEN
    RW_TAC std_ss [extreal_max_def, add_rzero, add_lzero] THEN
    TRY (METIS_TAC [le_mul, le_add])] THEN
   MATCH_MP_TAC (GSYM pos_fn_integral_add) THEN
   ASM_SIMP_TAC std_ss [le_max1] THEN
   ONCE_REWRITE_TAC [METIS [] ``!g. (\x. max 0 (f x * g x)) = (\x. max ((\x. 0) x) ((\x. f x * g x) x))``] THEN
   `(\x. 0) IN measurable (m_space M,measurable_sets M) Borel` by
     (MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST THEN
      METIS_TAC [measure_space_def]) THEN
   CONJ_TAC THEN MATCH_MP_TAC IN_MEASURABLE_BOREL_MAX THEN
   FULL_SIMP_TAC std_ss [measure_space_def] THEN
   MATCH_MP_TAC IN_MEASURABLE_BOREL_TIMES THEN METIS_TAC [measure_space_def],
   ALL_TAC] THEN
  RW_TAC std_ss [] THEN
  Q_TAC SUFF_TAC `AE M {x | f x * sup (IMAGE (\i. u i x) UNIV) = sup (IMAGE (\i. f x * u i x) UNIV)}` THENL
  [DISCH_TAC,
   FULL_SIMP_TAC std_ss [AE, ae_filter, GSPECIFICATION, null_sets, SUBSET_DEF] THEN
   Q.EXISTS_TAC `N` THEN ASM_SIMP_TAC std_ss [] THEN RW_TAC std_ss [] THEN
   FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN
   POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC [MONO_NOT_EQ] THEN
   RW_TAC std_ss [] THEN
   Q_TAC SUFF_TAC `f x * sup (IMAGE (\i. u i x) UNIV) =
     sup (IMAGE (\i. f x * (\i. u i x) i) UNIV)` THENL
   [SIMP_TAC std_ss [], ALL_TAC] THEN
   MATCH_MP_TAC (GSYM sup_cmult) THEN ASM_SIMP_TAC std_ss []] THEN
  Q_TAC SUFF_TAC `pos_fn_integral (density M f)
       (\x. max 0 (sup (IMAGE (\i. u i x) univ(:num)))) =
      sup (IMAGE (\i. pos_fn_integral (density M f) ((\i x. max 0 (u i x)) i)) UNIV)` THENL
  [DISC_RW_KILL,
   MATCH_MP_TAC lebesgue_monotone_convergence THEN
   ASM_SIMP_TAC std_ss [measure_space_density, le_max1] THEN
   ASM_SIMP_TAC std_ss [m_space_def, measurable_sets_def, density] THEN
   CONJ_TAC THENL
   [GEN_TAC THEN
    Q_TAC SUFF_TAC `!x. max 0 (u i x) = max ((\x. 0) x) ((\x. u i x) x)` THENL
    [DISC_RW_KILL, SIMP_TAC std_ss []] THEN
    MATCH_MP_TAC IN_MEASURABLE_BOREL_MAX THEN
    `(\x. 0) IN measurable (m_space M,measurable_sets M) Borel` by
     (MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST THEN
      METIS_TAC [measure_space_def]) THEN
    ONCE_REWRITE_TAC [METIS [ETA_AX] ``(\x. u i x) = u i``] THEN
    METIS_TAC [measure_space_def], ALL_TAC] THEN
   ASM_SIMP_TAC std_ss [extreal_max_def] THEN
   GEN_TAC THEN ASM_CASES_TAC ``!i:num. u i x = 0`` THENL
   [ASM_SIMP_TAC std_ss [IMAGE_DEF, IN_UNIV] THEN
    DISCH_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC std_ss [] THEN
    POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC [MONO_NOT_EQ] THEN
    RW_TAC std_ss [le_sup] THEN POP_ASSUM (MATCH_MP_TAC) THEN
    ONCE_REWRITE_TAC [GSYM SPECIFICATION] THEN SIMP_TAC std_ss [GSPECIFICATION] THEN
    ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN METIS_TAC [],
    ALL_TAC] THEN
   FULL_SIMP_TAC std_ss [] THEN RW_TAC std_ss [] THEN
   UNDISCH_TAC ``~(0 <= sup (IMAGE (\i. u i x) univ(:num)))`` THEN
   ONCE_REWRITE_TAC [MONO_NOT_EQ] THEN RW_TAC std_ss [le_lt] THEN
   SIMP_TAC std_ss [GSYM sup_lt] THEN Q.EXISTS_TAC `u i x` THEN
   CONJ_TAC THENL [ALL_TAC, METIS_TAC [le_lt]] THEN
   ONCE_REWRITE_TAC [GSYM SPECIFICATION] THEN
   SIMP_TAC std_ss [IN_IMAGE, IN_UNIV] THEN METIS_TAC []] THEN
  ASM_SIMP_TAC std_ss [] THEN
  Q_TAC SUFF_TAC `pos_fn_integral M (\x. max 0 (f x * sup (IMAGE (\i. u i x) univ(:num)))) =
                  pos_fn_integral M (\x. max 0 (sup (IMAGE (\i. f x * u i x) univ(:num))))` THENL
  [DISC_RW_KILL,
   MATCH_MP_TAC positive_integral_cong_AE THEN ASM_SIMP_TAC std_ss [le_max1] THEN
   FULL_SIMP_TAC std_ss [AE, ae_filter, GSPECIFICATION, SUBSET_DEF, null_sets] THEN
   Q.EXISTS_TAC `N'` THEN ASM_SIMP_TAC std_ss [] THEN RW_TAC std_ss [] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN
   POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC [MONO_NOT_EQ] THEN RW_TAC std_ss []] THEN

  Q_TAC SUFF_TAC
   `sup (IMAGE (\i. pos_fn_integral M (\x. max 0 ((\i x. f x * u i x) i x))) univ(:num)) =
    pos_fn_integral M (\x. max 0 ((\x. sup (IMAGE (\i. f x * u i x) univ(:num))) x))` THENL
  [SIMP_TAC std_ss [], ALL_TAC] THEN
  MATCH_MP_TAC (GSYM lebesgue_monotone_convergence_AE) THEN
  ASM_SIMP_TAC std_ss [] THEN CONJ_TAC THENL
  [GEN_TAC THEN MATCH_MP_TAC IN_MEASURABLE_BOREL_TIMES THEN
   Q.EXISTS_TAC `f` THEN Q.EXISTS_TAC `u i` THEN ASM_SIMP_TAC std_ss [],
   ALL_TAC] THEN
  FULL_SIMP_TAC std_ss [AE, ae_filter, GSPECIFICATION] THEN
  Q.EXISTS_TAC `N` THEN FULL_SIMP_TAC std_ss [SUBSET_DEF, GSPECIFICATION] THEN
  RW_TAC std_ss [] THEN FIRST_X_ASSUM MATCH_MP_TAC THENL
  [ASM_SIMP_TAC std_ss [] THEN POP_ASSUM MP_TAC THEN
   ONCE_REWRITE_TAC [MONO_NOT_EQ] THEN RW_TAC std_ss [] THEN
   MATCH_MP_TAC le_lmul_imp THEN FULL_SIMP_TAC std_ss [ext_mono_increasing_def],
   ALL_TAC] THEN
  ASM_SIMP_TAC std_ss [] THEN POP_ASSUM MP_TAC THEN
  ONCE_REWRITE_TAC [MONO_NOT_EQ] THEN RW_TAC std_ss [] THEN
  METIS_TAC [le_mul]);

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* ------------------------------------------------------------------------- *)

val _ = hide "lborel";

(* But they're the same thing!

val lebesgue = new_definition ("lebesgue",
  ``lebesgue = (univ(:real), {A | !n. (indicator A) integrable_on (line n)},
                (\A. sup {Normal (integral (line n) (indicator A)) | n IN UNIV}))``);
 *)
val lborel = new_definition ("lborel",
  ``lborel = (univ(:real), subsets borel, measure lebesgue)``);

val measure_space_lborel = store_thm ("measure_space_lborel",
  ``measure_hvg$measure_space lborel``,
  SIMP_TAC std_ss [measure_space_def, lborel, m_space_def, measurable_sets_def] THEN
  SIMP_TAC std_ss [GSYM space_borel, SPACE, sigma_algebra_borel] THEN
  CONJ_TAC THENL
  [ASSUME_TAC positive_lebesgue THEN FULL_SIMP_TAC std_ss [positive_def] THEN
   FULL_SIMP_TAC std_ss [measure_def, measurable_sets_def] THEN
   GEN_TAC THEN DISCH_THEN (MP_TAC o MATCH_MP lebesgueI_borel) THEN
   METIS_TAC [], ALL_TAC] THEN
  ASSUME_TAC countably_additive_lebesgue THEN
  FULL_SIMP_TAC std_ss [countably_additive_def] THEN GEN_TAC THEN
  POP_ASSUM (MP_TAC o Q.SPEC `f`) THEN RW_TAC std_ss [measure_def] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN FULL_SIMP_TAC std_ss [measurable_sets_def] THEN
  FULL_SIMP_TAC std_ss [IN_FUNSET, lebesgueI_borel]);

val sigma_finite_measure_lborel = store_thm ("sigma_finite_measure_lborel",
 ``sigma_finite_measure lborel``,
  RW_TAC std_ss [sigma_finite_measure] THEN Q.EXISTS_TAC `{line n | n IN UNIV}` THEN
  REPEAT CONJ_TAC THENL
  [SIMP_TAC std_ss [GSYM IMAGE_DEF] THEN
   MATCH_MP_TAC image_countable THEN
   SIMP_TAC std_ss [COUNTABLE_NUM],
   SIMP_TAC std_ss [SUBSET_DEF, GSPECIFICATION, lborel, measurable_sets_def] THEN
   REPEAT STRIP_TAC THEN RW_TAC std_ss [borel_line],
   SIMP_TAC std_ss [EXTENSION, lborel, m_space_def, IN_UNIV] THEN
   SIMP_TAC std_ss [IN_BIGUNION, GSPECIFICATION] THEN GEN_TAC THEN
   ASSUME_TAC mem_big_line THEN POP_ASSUM (MP_TAC o Q.SPEC `x`) THEN
   SET_TAC [],
   ALL_TAC] THEN
  RW_TAC std_ss [GSPECIFICATION, measure_def, lborel, measure_lebesgue] THEN
  SIMP_TAC std_ss [lt_infty, extreal_lt_def, le_sup] THEN
  Q.EXISTS_TAC `Normal (integral UNIV (indicator (line n)))` THEN
  SIMP_TAC std_ss [extreal_le_def] THEN GEN_TAC THEN
  GEN_REWR_TAC LAND_CONV [GSYM SPECIFICATION] THEN
  RW_TAC std_ss [GSPECIFICATION] THEN SIMP_TAC std_ss [extreal_le_def] THEN
  GEN_REWR_TAC LAND_CONV [GSYM integral_indicator_UNIV] THEN
  (MP_TAC o Q.SPECL [`n`, `n'`]) LESS_EQ_CASES THEN STRIP_TAC THEN
  FIRST_ASSUM (MP_TAC o MATCH_MP line_subset) THEN DISCH_TAC THENL
  [`line n INTER line n' = line n` by ASM_SET_TAC [] THEN
   METIS_TAC [REAL_LE_REFL],
   ALL_TAC] THEN
  `line n INTER line n' = line n'` by ASM_SET_TAC [] THEN
  ASM_REWRITE_TAC [] THEN MATCH_MP_TAC INTEGRAL_COMPONENT_LE THEN
  REPEAT STRIP_TAC THENL
  [ONCE_REWRITE_TAC [SET_RULE ``line n = line n INTER line n``] THEN
   REWRITE_TAC [integrable_indicator_UNIV] THEN
   SIMP_TAC std_ss [integrable_on] THEN
   Q.EXISTS_TAC `content (line n' INTER line n')` THEN
   METIS_TAC [has_integral_interval_cube, line, interval],
   ONCE_REWRITE_TAC [SET_RULE ``line n = line n INTER line n``] THEN
   REWRITE_TAC [integrable_indicator_UNIV] THEN
   SIMP_TAC std_ss [integrable_on] THEN
   Q.EXISTS_TAC `content (line n INTER line n)` THEN
   METIS_TAC [has_integral_interval_cube, line, interval],
   ALL_TAC] THEN
  SIMP_TAC std_ss [indicator] THEN REPEAT COND_CASES_TAC THEN
  SIMP_TAC real_ss [] THEN ASM_SET_TAC []);

val measure_of_eq = store_thm ("measure_of_eq",
  ``!m f. measure_space m ==>
     (pos_fn_integral m f = pos_fn_integral (m_space m, measurable_sets m,
      (\A. if A IN measurable_sets m then measure m A else 0)) f)``,
  RW_TAC std_ss [pos_fn_integral_def] THEN AP_TERM_TAC THEN
  AP_TERM_TAC THEN ABS_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  ABS_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  FULL_SIMP_TAC std_ss [IN_psfis_eq] THEN EQ_TAC THENL
  [RW_TAC std_ss [] THEN Q.EXISTS_TAC `s` THEN Q.EXISTS_TAC `a` THEN
   Q.EXISTS_TAC `x` THEN FULL_SIMP_TAC std_ss [pos_simple_fn_def] THEN
   FULL_SIMP_TAC std_ss [m_space_def, measurable_sets_def] THEN
   SIMP_TAC std_ss [pos_simple_fn_integral_def] THEN
   FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP EXTREAL_SUM_IMAGE_EQ) THEN
   CONJ_TAC THENL
   [DISJ1_TAC THEN RW_TAC std_ss [measure_def] THEN
    `(!c y. 0 <= c /\ y <> NegInf ==> Normal c * y <> NegInf)`
     by METIS_TAC [mul_not_infty] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    METIS_TAC [measure_space_def, positive_def, lte_trans, lt_infty, num_not_infty],
    ALL_TAC] THEN
   RW_TAC std_ss [measure_def],
   ALL_TAC] THEN
  RW_TAC std_ss [] THEN Q.EXISTS_TAC `s` THEN Q.EXISTS_TAC `a` THEN
  Q.EXISTS_TAC `x` THEN FULL_SIMP_TAC std_ss [pos_simple_fn_def] THEN
  FULL_SIMP_TAC std_ss [m_space_def, measurable_sets_def] THEN
  SIMP_TAC std_ss [pos_simple_fn_integral_def] THEN
  FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP EXTREAL_SUM_IMAGE_EQ) THEN
  CONJ_TAC THENL
  [DISJ1_TAC THEN RW_TAC std_ss [measure_def] THEN
   `(!c y. 0 <= c /\ y <> NegInf ==> Normal c * y <> NegInf)`
    by METIS_TAC [mul_not_infty] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
   METIS_TAC [measure_space_def, positive_def, lte_trans, lt_infty, num_not_infty],
   ALL_TAC] THEN RW_TAC std_ss [measure_def]);

val suminf_measure = store_thm ("suminf_measure",
  ``!M A.
    measure_space M /\ IMAGE (\i:num. A i) UNIV SUBSET measurable_sets M /\
    disjoint_family A ==>
    (suminf (\i. measure M (A i)) = measure M (BIGUNION {A i | i IN UNIV}))``,
  RW_TAC std_ss [GSYM IMAGE_DEF] THEN
  MATCH_MP_TAC (SIMP_RULE std_ss [o_DEF] MEASURE_COUNTABLY_ADDITIVE) THEN
  FULL_SIMP_TAC std_ss [IN_FUNSET, disjoint_family_on, disjoint_family] THEN
  ASM_SET_TAC []);

val measure_eqI_generator_eq = store_thm ("measure_eqI_generator_eq",
  ``!E sp M N A:num->'a->bool.
           measure_space M /\ measure_space N /\
           Int_stable E /\ E SUBSET POW sp /\
           (!X. X IN E ==> (measure M X = measure N X)) /\
           (measurable_sets M = subsets (sigma sp E)) /\
           (measurable_sets N = subsets (sigma sp E)) /\
           IMAGE A UNIV SUBSET E /\ (BIGUNION {A i | i IN UNIV} = sp) /\
           (!i. measure M (A i) <> PosInf) ==>
           (measure_of M = measure_of N)``,
  RW_TAC std_ss [] THEN
  Q_TAC SUFF_TAC `sigma_algebra (sigma (BIGUNION {A i | i IN univ(:num)}) E)` THENL
  [DISCH_TAC,
   MATCH_MP_TAC SIGMA_ALGEBRA_SIGMA THEN
   FULL_SIMP_TAC std_ss [subset_class_def, POW_DEF] THEN ASM_SET_TAC []] THEN
  Q_TAC SUFF_TAC `m_space M = BIGUNION {A i | i IN univ(:num)}` THENL
  [DISCH_TAC,
   MATCH_MP_TAC SUBSET_ANTISYM THEN RW_TAC std_ss [] THENL
   [ALL_TAC,
    RW_TAC std_ss [BIGUNION_SUBSET] THEN
    MATCH_MP_TAC MEASURABLE_SETS_SUBSET_SPACE THEN
    ASM_SIMP_TAC std_ss [subsets_def, sigma_def, IN_BIGINTER, GSPECIFICATION] THEN
    RW_TAC std_ss [SUBSET_DEF] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SET_TAC []] THEN
   `m_space M IN measurable_sets M` by METIS_TAC [MEASURE_SPACE_MSPACE_MEASURABLE] THEN
   POP_ASSUM MP_TAC THEN FULL_SIMP_TAC std_ss [IN_POW, SUBSET_DEF, sigma_def, subsets_def] THEN
   SIMP_TAC std_ss [IN_BIGINTER, GSPECIFICATION] THEN
   DISCH_THEN (MP_TAC o Q.SPEC `POW (BIGUNION {A i | i IN univ(:num)})`) THEN
   FULL_SIMP_TAC std_ss [POW_SIGMA_ALGEBRA, IN_POW, SUBSET_DEF] THEN
   ASM_SET_TAC []] THEN
  Q_TAC SUFF_TAC `!ff dd. ff IN E ==> measure M ff <> PosInf ==> dd IN measurable_sets M ==>
                    (measure M (ff INTER dd) = measure N (ff INTER dd))` THENL
  [DISCH_TAC,
   RW_TAC std_ss [] THEN
   `ff IN subsets (sigma (BIGUNION {A i | i IN univ(:num)}) E)`
    by METIS_TAC [IN_SIGMA] THEN
   Q_TAC SUFF_TAC `(\dd. measure M (ff INTER dd) = measure N (ff INTER dd)) dd` THENL
   [SIMP_TAC std_ss [], ALL_TAC] THEN
   MATCH_MP_TAC sigma_sets_induct_disjoint THEN Q.EXISTS_TAC `E` THEN
   Q.EXISTS_TAC `m_space M` THEN ASM_SIMP_TAC std_ss [] THEN
   RW_TAC std_ss [] THENL
   [FULL_SIMP_TAC std_ss [Int_stable],
    FULL_SIMP_TAC std_ss [INTER_EMPTY, measure_space_def, positive_def],
    Q.ABBREV_TAC `sp = BIGUNION {A i | i IN univ(:num)}` THEN
    Q_TAC SUFF_TAC `ff INTER (sp DIFF A') = ff DIFF (ff INTER A')` THENL
    [DISCH_TAC THEN ASM_REWRITE_TAC [],
     Q_TAC SUFF_TAC `ff INTER A' IN subsets (sigma sp E)` THENL
     [DISCH_TAC,
      MATCH_MP_TAC ALGEBRA_INTER THEN ASM_SIMP_TAC std_ss [] THEN
      FULL_SIMP_TAC std_ss [sigma_algebra_def]] THEN
     `ff SUBSET sp` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
     ASM_SET_TAC []] THEN
    Q_TAC SUFF_TAC `measure N (ff INTER A') <= measure N ff` THENL
    [DISCH_TAC,
     MATCH_MP_TAC INCREASING THEN ASM_SIMP_TAC std_ss [MEASURE_SPACE_INCREASING] THEN
     Q_TAC SUFF_TAC `ff INTER A' IN subsets (sigma sp E)` THENL
     [DISCH_TAC,
      MATCH_MP_TAC ALGEBRA_INTER THEN ASM_SIMP_TAC std_ss [] THEN
      FULL_SIMP_TAC std_ss [sigma_algebra_def]] THEN
     ASM_SET_TAC []] THEN
    Q_TAC SUFF_TAC `measure N (ff INTER A') <> PosInf` THENL
    [DISCH_TAC, METIS_TAC [let_trans, lt_infty]] THEN
    Q_TAC SUFF_TAC `measure M (ff INTER A') <= measure M ff` THENL
    [DISCH_TAC,
     MATCH_MP_TAC INCREASING THEN ASM_SIMP_TAC std_ss [MEASURE_SPACE_INCREASING] THEN
     Q_TAC SUFF_TAC `ff INTER A' IN subsets (sigma sp E)` THENL
     [DISCH_TAC,
      MATCH_MP_TAC ALGEBRA_INTER THEN ASM_SIMP_TAC std_ss [] THEN
      FULL_SIMP_TAC std_ss [sigma_algebra_def]] THEN
     ASM_SET_TAC []] THEN
    Q_TAC SUFF_TAC `measure M (ff INTER A') <> PosInf` THENL
    [DISCH_TAC, METIS_TAC [let_trans, lt_infty]] THEN
    Q_TAC SUFF_TAC `measure M (ff INTER (sp DIFF A')) =
                    measure M ff - measure M (ff INTER A')` THENL
    [ASM_SIMP_TAC std_ss [] THEN DISCH_TAC,
     Q_TAC SUFF_TAC `measure M ff - measure M (ff INTER A') = measure M (ff DIFF ff INTER A')` THENL
     [METIS_TAC [], ALL_TAC] THEN
     MATCH_MP_TAC (GSYM MEASURE_SPACE_FINITE_DIFF_SUBSET) THEN
     Q_TAC SUFF_TAC `ff INTER A' IN subsets (sigma sp E)` THENL
     [DISCH_TAC,
      MATCH_MP_TAC ALGEBRA_INTER THEN ASM_SIMP_TAC std_ss [] THEN
      FULL_SIMP_TAC std_ss [sigma_algebra_def]] THEN
     ASM_SET_TAC []] THEN
    Q_TAC SUFF_TAC `measure N (ff INTER (sp DIFF A')) =
                    measure N ff - measure M (ff INTER A')` THENL
    [DISCH_TAC,
     Q_TAC SUFF_TAC `measure N ff - measure N (ff INTER A') = measure N (ff DIFF ff INTER A')` THENL
     [METIS_TAC [], ALL_TAC] THEN
     MATCH_MP_TAC (GSYM MEASURE_SPACE_FINITE_DIFF_SUBSET) THEN
     Q_TAC SUFF_TAC `ff INTER A' IN subsets (sigma sp E)` THENL
     [DISCH_TAC,
      MATCH_MP_TAC ALGEBRA_INTER THEN ASM_SIMP_TAC std_ss [] THEN
      FULL_SIMP_TAC std_ss [sigma_algebra_def]] THEN
     ASM_SET_TAC []] THEN
    METIS_TAC [],
    ALL_TAC] THEN
   SIMP_TAC std_ss [IMAGE_DEF, INTER_BIGUNION] THEN
   ONCE_REWRITE_TAC [SET_RULE
    ``{ff INTER x | x IN {A x | x IN univ(:num)}} =
              {ff INTER (A x) | x IN univ(:num)}``] THEN
   SIMP_TAC std_ss [GSYM IMAGE_DEF] THEN
   `IMAGE (\x. (\x. ff INTER A' x) x) univ(:num) SUBSET measurable_sets M`
    by (SIMP_TAC std_ss [SUBSET_DEF, IN_IMAGE, IN_UNIV] THEN
        RW_TAC std_ss [] THEN MATCH_MP_TAC ALGEBRA_INTER THEN
        ASM_SET_TAC [sigma_algebra_def]) THEN
   `IMAGE (\x. (\x. ff INTER A' x) x)  univ(:num) SUBSET measurable_sets N`
    by (SIMP_TAC std_ss [SUBSET_DEF, IN_IMAGE, IN_UNIV] THEN
        RW_TAC std_ss [] THEN MATCH_MP_TAC ALGEBRA_INTER THEN
        ASM_SET_TAC [sigma_algebra_def]) THEN
   Q_TAC SUFF_TAC `disjoint_family (\x. ff INTER A' x)` THENL
   [DISCH_TAC,
    FULL_SIMP_TAC std_ss [disjoint_family, disjoint_family_on] THEN
    ASM_SET_TAC []] THEN
   Q.ABBREV_TAC `AA = (\x. ff INTER A' x)` THEN
   ASM_SIMP_TAC std_ss [GSYM (REWRITE_RULE [GSYM IMAGE_DEF] suminf_measure)] THEN
   AP_TERM_TAC THEN ABS_TAC THEN Q.UNABBREV_TAC `AA` THEN
   ASM_SIMP_TAC std_ss []] THEN
  MATCH_MP_TAC measure_eqI THEN RW_TAC std_ss [] THEN
  Q_TAC SUFF_TAC `!i. A i IN measurable_sets M` THENL
  [DISCH_TAC,
   GEN_TAC THEN ASM_SIMP_TAC std_ss [] THEN MATCH_MP_TAC IN_SIGMA THEN
   ASM_SET_TAC []] THEN
  Q.ABBREV_TAC `dd = disjointed (\i. A' INTER A i)` THEN
  Q_TAC SUFF_TAC `A' = BIGUNION {dd i | i IN UNIV}` THENL
  [DISCH_TAC,
   Q.UNABBREV_TAC `dd` THEN SIMP_TAC std_ss [UN_disjointed_eq] THEN
   ONCE_REWRITE_TAC [SET_RULE ``{A' INTER A i | i IN univ(:num)} =
     {A' INTER x | x IN IMAGE A UNIV}``] THEN
   SIMP_TAC std_ss [GSYM INTER_BIGUNION] THEN
   MATCH_MP_TAC (GSYM SUBSET_INTER1) THEN
   RULE_ASSUM_TAC (ONCE_REWRITE_RULE [EQ_SYM_EQ]) THEN
   ASM_SIMP_TAC std_ss [IMAGE_DEF] THEN
   MATCH_MP_TAC MEASURABLE_SETS_SUBSET_SPACE THEN
   METIS_TAC []] THEN
  Q_TAC SUFF_TAC `!i. dd i IN measurable_sets M` THENL
  [DISCH_TAC, Q.UNABBREV_TAC `dd` THEN
   Q_TAC SUFF_TAC
    `IMAGE (\i. disjointed (\i. A' INTER A i) i) UNIV SUBSET measurable_sets M` THENL
   [SET_TAC [], ALL_TAC] THEN
   MATCH_MP_TAC range_disjointed_sets THEN Q.EXISTS_TAC `m_space M` THEN
   CONJ_TAC THENL
   [METIS_TAC [measure_space_def, sigma_algebra_alt_eq, algebra_alt_eq],
    ALL_TAC] THEN
   SIMP_TAC std_ss [IN_IMAGE, SUBSET_DEF, IN_UNIV] THEN REPEAT STRIP_TAC THEN
   POP_ASSUM (fn th => REWRITE_TAC[th]) THEN
   MATCH_MP_TAC MEASURE_SPACE_INTER THEN ASM_SIMP_TAC std_ss []] THEN
  Q_TAC SUFF_TAC `disjoint_family dd` THENL
  [DISCH_TAC,
   Q.UNABBREV_TAC `dd` THEN SIMP_TAC std_ss [disjoint_family_disjoint]] THEN
  Q_TAC SUFF_TAC `suminf (\i. measure M (dd i)) = suminf (\i. measure N (dd i))` THENL
  [DISCH_TAC,
   Q.UNABBREV_TAC `dd` THEN AP_TERM_TAC THEN ABS_TAC THEN
   Q_TAC SUFF_TAC `disjointed (\i. A' INTER A i) i =
     A i INTER disjointed (\i. A' INTER A i) i` THENL
   [DISC_RW_KILL,
    SIMP_TAC std_ss [disjointed] THEN SET_TAC []] THEN
   FIRST_X_ASSUM (MP_TAC o Q.SPECL [`A (i:num)`,`disjointed (\i. A' INTER A i) i`]) THEN
   SIMP_TAC std_ss [AND_IMP_INTRO] THEN DISCH_THEN MATCH_MP_TAC THEN
   ASM_SIMP_TAC std_ss [] THEN ASM_SET_TAC []] THEN
  POP_ASSUM MP_TAC THEN
  `IMAGE (\i. dd i) univ(:num) SUBSET measurable_sets M` by ASM_SET_TAC [] THEN
  `IMAGE (\i. dd i) univ(:num) SUBSET measurable_sets N` by ASM_SET_TAC [] THEN
  ASM_SIMP_TAC std_ss [suminf_measure]);

val lborel_eqI = store_thm ("lborel_eqI",
  ``!M. (!a b. measure M (interval [a,b]) =
         Normal (content (interval [a,b]))) /\
      measure_space M /\
      (measurable_sets M = subsets borel) ==>
      (measure_of lborel = measure_of M)``,
  RW_TAC std_ss [] THEN MATCH_MP_TAC measure_eqI_generator_eq THEN
  Q.EXISTS_TAC `IMAGE (\(a,b). interval [a,b]) UNIV` THEN Q.EXISTS_TAC `UNIV` THEN
  SIMP_TAC std_ss [interval, GSYM borel_eq_atLeastAtMost] THEN
  ASM_SIMP_TAC std_ss [lborel,measurable_sets_def, measure_space_lborel] THEN
  SIMP_TAC std_ss [GSYM lborel, SUBSET_DEF, IN_POW, SUBSET_UNIV] THEN
  Q.EXISTS_TAC `line` THEN CONJ_TAC THENL
  [RW_TAC std_ss [IN_IMAGE, Int_stable, IN_UNIV] THEN
   `?a b. x = (a,b)` by SIMP_TAC std_ss [ABS_PAIR_THM] THEN
   `?c d. x' = (c,d)` by SIMP_TAC std_ss [ABS_PAIR_THM] THEN
   ASM_SIMP_TAC real_ss [INTER_DEF, EXTENSION, GSPECIFICATION, EXISTS_PROD] THEN
   Q.EXISTS_TAC `max a c` THEN Q.EXISTS_TAC `min b d` THEN
   SIMP_TAC std_ss [min_def, max_def] THEN REAL_ARITH_TAC,
   ALL_TAC] THEN
  Q_TAC SUFF_TAC `(!X.
   X IN IMAGE (\(a,b). {x | a <= x /\ x <= b}) univ(:real # real) ==>
   (measure lborel X = measure M X))` THENL
  [DISCH_TAC,
   RW_TAC std_ss [IN_IMAGE, IN_UNIV] THEN
   `?a b. x = (a,b)` by SIMP_TAC std_ss [ABS_PAIR_THM] THEN
   FULL_SIMP_TAC std_ss [interval] THEN
   SIMP_TAC std_ss [lborel, measure_def, measure_lebesgue] THEN
   SIMP_TAC std_ss [sup_eq] THEN CONJ_TAC THEN GEN_TAC THENL
   [GEN_REWR_TAC LAND_CONV [GSYM SPECIFICATION] THEN
    SIMP_TAC std_ss [GSPECIFICATION, IN_UNIV] THEN
    STRIP_TAC THEN ASM_SIMP_TAC std_ss [extreal_le_def] THEN
    ONCE_REWRITE_TAC [GSYM integral_indicator_UNIV] THEN
    ONCE_REWRITE_TAC [INTER_COMM] THEN REWRITE_TAC [integral_indicator_UNIV] THEN
    SIMP_TAC std_ss [GSYM interval] THEN
    GEN_REWR_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC INTEGRAL_COMPONENT_UBOUND THEN SIMP_TAC std_ss [DROP_INDICATOR_LE_1] THEN
    ONCE_REWRITE_TAC [GSYM integrable_indicator_UNIV] THEN
    SIMP_TAC std_ss [INTER_INTERVAL, line, GSYM interval, indicator] THEN
    ONCE_REWRITE_TAC [METIS [] ``1 = (\x:real. 1:real) x``] THEN
    REWRITE_TAC [INTEGRABLE_RESTRICT_UNIV, INTEGRABLE_CONST],
    ALL_TAC] THEN
   DISCH_THEN MATCH_MP_TAC THEN ONCE_REWRITE_TAC [GSYM SPECIFICATION] THEN
   SIMP_TAC std_ss [GSPECIFICATION] THEN RW_TAC std_ss [IN_UNIV] THEN
   (MP_TAC o Q.SPECL [`abs a`,`abs b`]) REAL_LE_TOTAL THEN
   ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN STRIP_TAC THENL
   [`?n. abs b <= &n` by SIMP_TAC std_ss [SIMP_REAL_ARCH] THEN
    Q.EXISTS_TAC `n` THEN MATCH_MP_TAC INTEGRAL_UNIQUE THEN
    Q_TAC SUFF_TAC `{x | a <= x /\ x <= b} = {x | a <= x /\ x <= b} INTER line n` THENL
    [METIS_TAC [has_integral_interval_cube, GSYM interval], ALL_TAC] THEN
    SIMP_TAC std_ss [EXTENSION, IN_INTER, GSPECIFICATION, line] THEN
    GEN_TAC THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN REAL_ARITH_TAC,
    ALL_TAC] THEN
   `?n. abs a <= &n` by SIMP_TAC std_ss [SIMP_REAL_ARCH] THEN
    Q.EXISTS_TAC `n` THEN MATCH_MP_TAC INTEGRAL_UNIQUE THEN
    Q_TAC SUFF_TAC `{x | a <= x /\ x <= b} = {x | a <= x /\ x <= b} INTER line n` THENL
    [METIS_TAC [has_integral_interval_cube, GSYM interval], ALL_TAC] THEN
    SIMP_TAC std_ss [EXTENSION, IN_INTER, GSPECIFICATION, line] THEN
    GEN_TAC THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN REAL_ARITH_TAC] THEN
   ASM_SIMP_TAC std_ss [] THEN CONJ_TAC THENL
   [RW_TAC std_ss [line, IN_IMAGE, GSPECIFICATION, IN_UNIV] THEN
    Q.EXISTS_TAC `(-&x', &x')` THEN SIMP_TAC std_ss [],
    ALL_TAC] THEN
  CONJ_TAC THENL
  [SIMP_TAC std_ss [EXTENSION, IN_BIGUNION, IN_UNIV, line, GSPECIFICATION] THEN
   GEN_TAC THEN `?n. abs x <= &n` by SIMP_TAC std_ss [SIMP_REAL_ARCH] THEN
   Q.EXISTS_TAC `line n` THEN SIMP_TAC std_ss [line, GSPECIFICATION] THEN
   CONJ_TAC THENL [POP_ASSUM MP_TAC THEN REAL_ARITH_TAC, ALL_TAC] THEN
   METIS_TAC [],
   ALL_TAC] THEN
  GEN_TAC THEN Q_TAC SUFF_TAC `measure lborel (line i) = measure M (line i)` THENL
  [DISCH_TAC,
   FIRST_X_ASSUM MATCH_MP_TAC THEN SIMP_TAC std_ss [line, IN_IMAGE, IN_UNIV] THEN
   Q.EXISTS_TAC `(-&i, &i)` THEN SIMP_TAC std_ss []] THEN
  ASM_REWRITE_TAC [line, GSYM interval, lt_infty]);

val distr = new_definition ("distr",
  ``distr M N f = (m_space N, measurable_sets N, (\A. measure M (PREIMAGE f A INTER m_space M)))``);

val measure_space_distr = store_thm ("measure_space_distr",
  ``!M M' t. measure_space M /\ measure_space M' /\
             t IN measurable (m_space M, measurable_sets M) (m_space M', measurable_sets M')
             ==> measure_space (distr M M' t)``,
  RW_TAC std_ss [measure_space_def] THENL
  [METIS_TAC [distr, m_space_def, measurable_sets_def],
   FULL_SIMP_TAC std_ss [positive_def, distr, measure_def, measurable_sets_def] THEN
   ASM_SIMP_TAC std_ss [INTER_EMPTY, PREIMAGE_EMPTY] THEN
   FULL_SIMP_TAC std_ss [IN_MEASURABLE, space_def, subsets_def],
   ALL_TAC] THEN
  RULE_ASSUM_TAC (ONCE_REWRITE_RULE [GSYM MEASURE_SPACE_REDUCE]) THEN
  FULL_SIMP_TAC std_ss [countably_additive_alt_eq, distr] THEN
  FULL_SIMP_TAC std_ss [MEASURE_SPACE_REDUCE] THEN RW_TAC std_ss [] THEN
  `!i. A i IN measurable_sets M'` by ASM_SET_TAC [] THEN
  Q_TAC SUFF_TAC `IMAGE (\i. PREIMAGE t (A i) INTER m_space M) UNIV SUBSET measurable_sets M` THENL
  [DISCH_TAC,
   FULL_SIMP_TAC std_ss [IN_MEASURABLE, space_def, subsets_def, SUBSET_DEF] THEN
   FULL_SIMP_TAC std_ss [IN_IMAGE, IN_UNIV] THEN METIS_TAC []] THEN
  Q_TAC SUFF_TAC
  `BIGUNION {PREIMAGE t (A i) INTER m_space M | i IN UNIV} IN measurable_sets M` THENL
  [DISCH_TAC, FULL_SIMP_TAC std_ss [sigma_algebra_alt_eq]] THEN
  Q_TAC SUFF_TAC `disjoint_family (\i. PREIMAGE t (A i) INTER m_space M)` THENL
  [DISCH_TAC,
   FULL_SIMP_TAC std_ss [disjoint_family, disjoint_family_on, IN_UNIV] THEN
   FULL_SIMP_TAC std_ss [PREIMAGE_def] THEN ASM_SET_TAC []] THEN
  SIMP_TAC std_ss [PREIMAGE_BIGUNION, o_DEF] THEN
  Q_TAC SUFF_TAC `IMAGE (PREIMAGE t) {A i | i IN univ(:num)} =
                  IMAGE (\i. PREIMAGE t (A i)) UNIV` THENL
  [ONCE_REWRITE_TAC [METIS [ETA_AX] ``PREIMAGE t = (\s. PREIMAGE t s)``] THEN
   ONCE_REWRITE_TAC [METIS [ETA_AX] ``PREIMAGE t = (\s. PREIMAGE t s)``] THEN
   SIMP_TAC std_ss [] THEN DISC_RW_KILL,
   ASM_SET_TAC []] THEN
  Q_TAC SUFF_TAC `BIGUNION (IMAGE (\i. PREIMAGE t (A i)) univ(:num)) INTER m_space M =
                  BIGUNION (IMAGE (\i. PREIMAGE t (A i) INTER m_space M) univ(:num))` THENL
  [SIMP_TAC std_ss [] THEN DISC_RW_KILL,
   FULL_SIMP_TAC std_ss [EXTENSION, IN_INTER, IN_BIGUNION] THEN
   RW_TAC std_ss [] THEN EQ_TAC THEN
   RW_TAC std_ss [IN_IMAGE, IN_UNIV, IN_INTER, IN_PREIMAGE] THENL
   [Q.EXISTS_TAC `PREIMAGE t (A i) INTER m_space M` THEN
    FULL_SIMP_TAC std_ss [] THEN ASM_SET_TAC [],
    FULL_SIMP_TAC std_ss [IN_INTER] THEN METIS_TAC [],
    ALL_TAC] THEN
   FULL_SIMP_TAC std_ss [IN_INTER]] THEN
  Q_TAC SUFF_TAC `measure M
  (BIGUNION (IMAGE (\i. PREIMAGE t (A i) INTER m_space M) univ(:num))) =
   suminf (\x. measure M ((\x. PREIMAGE t (A x) INTER m_space M) x))` THENL
  [SIMP_TAC std_ss [], ALL_TAC] THEN
  MATCH_MP_TAC (GSYM (REWRITE_RULE [GSYM IMAGE_DEF] suminf_measure)) THEN
  FULL_SIMP_TAC std_ss [measure_space_def] THEN
  ONCE_REWRITE_TAC [GSYM MEASURE_SPACE_REDUCE] THEN
  METIS_TAC [countably_additive_alt_eq, space_def, subsets_def]);

val pos_fn_integral_distr' = store_thm ("pos_fn_integral_distr'",
  ``! t f M M'. measure_space M /\ measure_space M' /\
     t IN measurable (m_space M, measurable_sets M) (m_space M', measurable_sets M') /\
     f IN measurable (m_space (distr M M' t), measurable_sets (distr M M' t)) Borel /\
     (!x. 0 <= f x) ==>
     (pos_fn_integral (distr M M' t) (\x. max 0 (f x)) =
      pos_fn_integral M (\x. max 0 (f (t x))))``,
  RW_TAC std_ss [] THEN
  Q_TAC SUFF_TAC `(\f. pos_fn_integral (distr M M' t) (\x. max 0 (f x)) =
                       pos_fn_integral M (\x. max 0 (f (t x)))) f` THENL
  [SIMP_TAC std_ss [], ALL_TAC] THEN
  MATCH_MP_TAC Induct_on_Borel_functions THEN Q.EXISTS_TAC `distr M M' t` THEN
  ASM_SIMP_TAC std_ss [measure_space_distr] THEN
  CONJ_TAC THENL
  [RW_TAC std_ss [] THEN
   Q_TAC SUFF_TAC `pos_fn_integral (distr M M' t) (\x. max 0 (g x)) =
                   pos_fn_integral (distr M M' t) (\x. max 0 (f' x))` THENL
   [DISC_RW_KILL,
    MATCH_MP_TAC positive_integral_cong THEN
    ASM_SIMP_TAC std_ss [le_max1, measure_space_distr]] THEN
   ASM_SIMP_TAC std_ss [] THEN MATCH_MP_TAC positive_integral_cong THEN
   ASM_SIMP_TAC std_ss [le_max1] THEN RW_TAC std_ss [] THEN
   AP_TERM_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
   FULL_SIMP_TAC std_ss [IN_MEASURABLE, space_def, subsets_def] THEN
   SIMP_TAC std_ss [distr, m_space_def] THEN FULL_SIMP_TAC std_ss [IN_FUNSET],
   ALL_TAC] THEN
  CONJ_TAC THENL
  [RW_TAC std_ss [] THEN
   ONCE_REWRITE_TAC [METIS [extreal_max_def, indicator_fn_pos_le]
    ``!x. max 0 (indicator_fn A x) = indicator_fn A x``] THEN
   ONCE_REWRITE_TAC [METIS [ETA_AX] ``(\x. indicator_fn A x) = indicator_fn A``] THEN
   `measure_space (distr M M' t)` by METIS_TAC [measure_space_distr] THEN
   ASM_SIMP_TAC std_ss [pos_fn_integral_indicator] THEN
   ASM_SIMP_TAC std_ss [distr, measure_def] THEN
   Q_TAC SUFF_TAC `PREIMAGE t A INTER m_space M IN measurable_sets M` THENL
   [DISCH_TAC,
    FULL_SIMP_TAC std_ss [IN_MEASURABLE, space_def, subsets_def] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN FULL_SIMP_TAC std_ss [distr, measurable_sets_def]] THEN
   ASM_SIMP_TAC std_ss [GSYM pos_fn_integral_indicator] THEN
   MATCH_MP_TAC positive_integral_cong THEN ASM_SIMP_TAC std_ss [indicator_fn_pos_le] THEN
   SIMP_TAC std_ss [indicator_fn_def, GSPECIFICATION, IN_INTER] THEN
   RW_TAC std_ss [IN_PREIMAGE],
   ALL_TAC] THEN
  CONJ_TAC THENL
  [RW_TAC std_ss [] THEN
   Q_TAC SUFF_TAC `pos_fn_integral (distr M M' t) (\x. max 0 (c * f' x)) =
                   c * pos_fn_integral (distr M M' t) (\x. max 0 (f' x))` THENL
   [DISC_RW_KILL,
    MATCH_MP_TAC pos_fn_integral_cmult THEN ASM_SIMP_TAC std_ss [measure_space_distr]] THEN
   ASM_REWRITE_TAC [] THEN ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
   Q_TAC SUFF_TAC `pos_fn_integral M (\x. max 0 (c * (\x. f' (t x)) x)) =
                   c * pos_fn_integral M (\x. max 0 ((\x. f' (t x)) x))` THENL
   [SIMP_TAC std_ss [], ALL_TAC] THEN
   MATCH_MP_TAC pos_fn_integral_cmult THEN ASM_SIMP_TAC std_ss [] THEN
   FULL_SIMP_TAC std_ss [IN_MEASURABLE, space_def, subsets_def] THEN
   CONJ_TAC THENL [EVAL_TAC THEN SRW_TAC[] [IN_DEF,IN_FUNSET], ALL_TAC] THEN
   RW_TAC std_ss [] THEN
   Q_TAC SUFF_TAC `PREIMAGE (\x. f' (t x)) s = PREIMAGE t {x | f' (x) IN s}` THENL
   [SIMP_TAC std_ss [] THEN DISC_RW_KILL,
    SIMP_TAC std_ss [PREIMAGE_def, GSPECIFICATION]] THEN
   Q_TAC SUFF_TAC `PREIMAGE t {x | f' x IN s} INTER m_space M =
                   PREIMAGE t (PREIMAGE f' s INTER m_space M') INTER m_space M` THENL
   [SIMP_TAC std_ss [] THEN DISC_RW_KILL,
    SIMP_TAC std_ss [PREIMAGE_def] THEN
    SIMP_TAC std_ss [INTER_DEF, IN_INTER, GSPECIFICATION] THEN
    FULL_SIMP_TAC std_ss [IN_FUNSET] THEN
    SIMP_TAC std_ss [EXTENSION, GSPECIFICATION] THEN GEN_TAC THEN EQ_TAC THEN
    RW_TAC std_ss []] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   FULL_SIMP_TAC std_ss [distr, measurable_sets_def, m_space_def],
   ALL_TAC] THEN

  CONJ_TAC THENL
  [RW_TAC std_ss [] THEN
   Q_TAC SUFF_TAC `!x. max 0 (f' x + g x) = max 0 (f' x) + max 0 (g x)` THENL
   [DISC_RW_KILL,
    ASM_SIMP_TAC std_ss [extreal_max_def] THEN GEN_TAC THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC std_ss [] THEN
    METIS_TAC [le_add]] THEN
   Q_TAC SUFF_TAC `pos_fn_integral (distr M M' t) (\x. (\x. max 0 (f' x)) x + (\x. max 0 (g x)) x) =
                   pos_fn_integral (distr M M' t) (\x. max 0 (f' x)) +
                   pos_fn_integral (distr M M' t) (\x. max 0 (g x))` THENL
   [SIMP_TAC std_ss [] THEN DISC_RW_KILL,
    MATCH_MP_TAC pos_fn_integral_add THEN ASM_SIMP_TAC std_ss [le_max1, measure_space_distr] THEN
    CONJ_TAC THENL
    [Q_TAC SUFF_TAC `(\x. max ((\x. 0) x) ((\x. f' x) x)) IN
      measurable (m_space (distr M M' t),measurable_sets (distr M M' t)) Borel` THENL
     [SIMP_TAC std_ss [], ALL_TAC] THEN
     MATCH_MP_TAC IN_MEASURABLE_BOREL_MAX THEN
     `(\x. 0) IN measurable (m_space M',measurable_sets M') Borel` by
        (MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST THEN
         METIS_TAC [measure_space_def]) THEN
     ONCE_REWRITE_TAC [METIS [ETA_AX] ``(\x. f' x) = f'``] THEN
     FULL_SIMP_TAC std_ss [distr, m_space_def, measurable_sets_def] THEN
     METIS_TAC [measure_space_def],
     ALL_TAC] THEN
    Q_TAC SUFF_TAC `(\x. max ((\x. 0) x) ((\x. g x) x)) IN
      measurable (m_space (distr M M' t),measurable_sets (distr M M' t)) Borel` THENL
    [SIMP_TAC std_ss [], ALL_TAC] THEN
    MATCH_MP_TAC IN_MEASURABLE_BOREL_MAX THEN
    `(\x. 0) IN measurable (m_space M',measurable_sets M') Borel` by
       (MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST THEN
        METIS_TAC [measure_space_def]) THEN
    ONCE_REWRITE_TAC [METIS [ETA_AX] ``(\x. g x) = g``] THEN
    FULL_SIMP_TAC std_ss [distr, m_space_def, measurable_sets_def] THEN
    METIS_TAC [measure_space_def]] THEN
   Q_TAC SUFF_TAC
   `pos_fn_integral M (\x. max 0 (f' (t x))) +
    pos_fn_integral M (\x. max 0 (g (t x))) =
    pos_fn_integral M (\x. ((\x. max 0 (f' (t x))) x) + ((\x. max 0 (g (t x))) x))` THENL
   [ASM_SIMP_TAC std_ss [], ALL_TAC] THEN
   MATCH_MP_TAC (GSYM pos_fn_integral_add) THEN ASM_SIMP_TAC std_ss [le_max1] THEN
   CONJ_TAC THENL
   [Q_TAC SUFF_TAC `(\x. max ((\x. 0) x) ((\x. f' (t x)) x)) IN
      measurable (m_space M,measurable_sets M) Borel` THENL
    [SIMP_TAC std_ss [], ALL_TAC] THEN
    MATCH_MP_TAC IN_MEASURABLE_BOREL_MAX THEN
    `(\x. 0) IN measurable (m_space M,measurable_sets M) Borel` by
       (MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST THEN
        METIS_TAC [measure_space_def]) THEN
    CONJ_TAC THENL [METIS_TAC [measure_space_def], ALL_TAC] THEN
    FULL_SIMP_TAC std_ss [IN_MEASURABLE, distr, m_space_def, measurable_sets_def] THEN
    CONJ_TAC THENL [EVAL_TAC THEN SRW_TAC[] [IN_DEF,IN_FUNSET], ALL_TAC] THEN
    FULL_SIMP_TAC std_ss [space_def, subsets_def] THEN RW_TAC std_ss [] THEN
    Q_TAC SUFF_TAC `PREIMAGE (\x. f' (t x)) s = PREIMAGE t {x | f' (x) IN s}` THENL
    [SIMP_TAC std_ss [] THEN DISC_RW_KILL,
     SIMP_TAC std_ss [PREIMAGE_def, GSPECIFICATION]] THEN
    Q_TAC SUFF_TAC `PREIMAGE t {x | f' x IN s} INTER m_space M =
                    PREIMAGE t (PREIMAGE f' s INTER m_space M') INTER m_space M` THENL
    [SIMP_TAC std_ss [] THEN DISC_RW_KILL,
     SIMP_TAC std_ss [PREIMAGE_def] THEN
     SIMP_TAC std_ss [INTER_DEF, IN_INTER, GSPECIFICATION] THEN
     FULL_SIMP_TAC std_ss [IN_FUNSET] THEN
     SIMP_TAC std_ss [EXTENSION, GSPECIFICATION] THEN GEN_TAC THEN EQ_TAC THEN
     RW_TAC std_ss []] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC std_ss [],
    ALL_TAC] THEN
   Q_TAC SUFF_TAC `(\x. max ((\x. 0) x) ((\x. g (t x)) x)) IN
      measurable (m_space M,measurable_sets M) Borel` THENL
   [SIMP_TAC std_ss [], ALL_TAC] THEN
   MATCH_MP_TAC IN_MEASURABLE_BOREL_MAX THEN
   `(\x. 0) IN measurable (m_space M,measurable_sets M) Borel` by
      (MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST THEN
       METIS_TAC [measure_space_def]) THEN
   CONJ_TAC THENL [METIS_TAC [measure_space_def], ALL_TAC] THEN
   FULL_SIMP_TAC std_ss [IN_MEASURABLE, distr, m_space_def, measurable_sets_def] THEN
   CONJ_TAC THENL [EVAL_TAC THEN SRW_TAC[] [IN_DEF,IN_FUNSET], ALL_TAC] THEN
   FULL_SIMP_TAC std_ss [space_def, subsets_def] THEN RW_TAC std_ss [] THEN
   Q_TAC SUFF_TAC `PREIMAGE (\x. g (t x)) s = PREIMAGE t {x | g (x) IN s}` THENL
   [SIMP_TAC std_ss [] THEN DISC_RW_KILL,
    SIMP_TAC std_ss [PREIMAGE_def, GSPECIFICATION]] THEN
   Q_TAC SUFF_TAC `PREIMAGE t {x | g x IN s} INTER m_space M =
                   PREIMAGE t (PREIMAGE g s INTER m_space M') INTER m_space M` THENL
   [SIMP_TAC std_ss [] THEN DISC_RW_KILL,
    SIMP_TAC std_ss [PREIMAGE_def] THEN
    SIMP_TAC std_ss [INTER_DEF, IN_INTER, GSPECIFICATION] THEN
    FULL_SIMP_TAC std_ss [IN_FUNSET] THEN
    SIMP_TAC std_ss [EXTENSION, GSPECIFICATION] THEN GEN_TAC THEN EQ_TAC THEN
    RW_TAC std_ss []] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC std_ss [],
   ALL_TAC] THEN
  RW_TAC std_ss [] THEN

  Q_TAC SUFF_TAC `pos_fn_integral (distr M M' t)
       (\x. max 0 (sup (IMAGE (\i. u i x) univ(:num)))) =
      sup (IMAGE (\i. pos_fn_integral (distr M M' t) ((\i x. max 0 (u i x)) i)) UNIV)` THENL
  [DISC_RW_KILL,
   MATCH_MP_TAC lebesgue_monotone_convergence THEN
   ASM_SIMP_TAC std_ss [measure_space_distr, le_max1] THEN
   ASM_SIMP_TAC std_ss [m_space_def, measurable_sets_def, distr] THEN
   CONJ_TAC THENL
   [GEN_TAC THEN
    Q_TAC SUFF_TAC `!x. max 0 (u i x) = max ((\x. 0) x) ((\x. u i x) x)` THENL
    [DISC_RW_KILL, SIMP_TAC std_ss []] THEN
    MATCH_MP_TAC IN_MEASURABLE_BOREL_MAX THEN
    `(\x. 0) IN measurable (m_space M',measurable_sets M') Borel` by
     (MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST THEN
      METIS_TAC [measure_space_def]) THEN
    ONCE_REWRITE_TAC [METIS [ETA_AX] ``(\x. u i x) = u i``] THEN
    METIS_TAC [measure_space_def, distr, m_space_def, measurable_sets_def], ALL_TAC] THEN
   ASM_SIMP_TAC std_ss [extreal_max_def] THEN
   GEN_TAC THEN ASM_CASES_TAC ``!i:num. u i (x:'b) = 0`` THENL
   [ASM_SIMP_TAC std_ss [IMAGE_DEF, IN_UNIV] THEN
    DISCH_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC std_ss [] THEN
    POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC [MONO_NOT_EQ] THEN
    RW_TAC std_ss [le_sup] THEN POP_ASSUM (MATCH_MP_TAC) THEN
    ONCE_REWRITE_TAC [GSYM SPECIFICATION] THEN SIMP_TAC std_ss [GSPECIFICATION] THEN
    ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN METIS_TAC [],
    ALL_TAC] THEN
   FULL_SIMP_TAC std_ss [] THEN RW_TAC std_ss [] THEN
   UNDISCH_TAC ``~(0 <= sup (IMAGE (\i. u i (x:'b)) univ(:num)))`` THEN
   ONCE_REWRITE_TAC [MONO_NOT_EQ] THEN RW_TAC std_ss [le_lt] THEN
   SIMP_TAC std_ss [GSYM sup_lt] THEN Q.EXISTS_TAC `u i x` THEN
   CONJ_TAC THENL [ALL_TAC, METIS_TAC [le_lt]] THEN
   ONCE_REWRITE_TAC [GSYM SPECIFICATION] THEN
   SIMP_TAC std_ss [IN_IMAGE, IN_UNIV] THEN METIS_TAC []] THEN
  ASM_SIMP_TAC std_ss [] THEN

  Q_TAC SUFF_TAC
   `sup (IMAGE (\i. pos_fn_integral M ((\i x. max 0 (u i (t x))) i)) univ(:num)) =
    pos_fn_integral M (\x. max 0 (sup (IMAGE (\i. u i (t x)) univ(:num))))` THENL
  [SIMP_TAC std_ss [], ALL_TAC] THEN
  MATCH_MP_TAC (GSYM lebesgue_monotone_convergence) THEN
  ASM_SIMP_TAC std_ss [le_max1] THEN CONJ_TAC THENL
  [GEN_TAC THEN
   Q_TAC SUFF_TAC `!x. max 0 (u i (t x)) = max ((\x. 0) x) ((\x. u i (t x)) x)` THENL
   [DISC_RW_KILL, SIMP_TAC std_ss []] THEN
   MATCH_MP_TAC IN_MEASURABLE_BOREL_MAX THEN
   `(\x. 0) IN measurable (m_space M,measurable_sets M) Borel` by
    (MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST THEN
     METIS_TAC [measure_space_def]) THEN
   CONJ_TAC THENL [METIS_TAC [measure_space_def], ALL_TAC] THEN
   FULL_SIMP_TAC std_ss [IN_MEASURABLE, distr, m_space_def, measurable_sets_def] THEN
   CONJ_TAC THENL [EVAL_TAC THEN SRW_TAC[] [IN_DEF,IN_FUNSET], ALL_TAC] THEN
   FULL_SIMP_TAC std_ss [space_def, subsets_def] THEN RW_TAC std_ss [] THEN
   Q_TAC SUFF_TAC `PREIMAGE (\x. u i (t x)) s = PREIMAGE t {x | u i (x) IN s}` THENL
   [SIMP_TAC std_ss [] THEN DISC_RW_KILL,
    SIMP_TAC std_ss [PREIMAGE_def, GSPECIFICATION]] THEN
   Q_TAC SUFF_TAC `PREIMAGE t {x | u i x IN s} INTER m_space M =
                   PREIMAGE t (PREIMAGE (u i) s INTER m_space M') INTER m_space M` THENL
   [SIMP_TAC std_ss [] THEN DISC_RW_KILL,
    SIMP_TAC std_ss [PREIMAGE_def] THEN
    SIMP_TAC std_ss [INTER_DEF, IN_INTER, GSPECIFICATION] THEN
    FULL_SIMP_TAC std_ss [IN_FUNSET] THEN
    SIMP_TAC std_ss [EXTENSION, GSPECIFICATION] THEN GEN_TAC THEN EQ_TAC THEN
    RW_TAC std_ss []] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC std_ss [],
   ALL_TAC] THEN
  ASM_SIMP_TAC std_ss [extreal_max_def] THEN GEN_TAC THEN DISCH_TAC THEN
  ASM_CASES_TAC ``!i:num. u i ((t:'a->'b) x) = 0`` THENL
  [ASM_SIMP_TAC std_ss [IMAGE_DEF, IN_UNIV] THEN
   COND_CASES_TAC THEN ASM_SIMP_TAC std_ss [] THEN
   POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC [MONO_NOT_EQ] THEN
   RW_TAC std_ss [le_sup] THEN POP_ASSUM (MATCH_MP_TAC) THEN
   ONCE_REWRITE_TAC [GSYM SPECIFICATION] THEN SIMP_TAC std_ss [GSPECIFICATION] THEN
   ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN METIS_TAC [],
   ALL_TAC] THEN
  FULL_SIMP_TAC std_ss [] THEN RW_TAC std_ss [] THEN
  UNDISCH_TAC ``~(0 <= sup (IMAGE (\i. u i ((t:'a->'b) x)) univ(:num)))`` THEN
  ONCE_REWRITE_TAC [MONO_NOT_EQ] THEN RW_TAC std_ss [le_lt] THEN
  SIMP_TAC std_ss [GSYM sup_lt] THEN Q.EXISTS_TAC `u i (t x)` THEN
  CONJ_TAC THENL [ALL_TAC, METIS_TAC [le_lt]] THEN
  ONCE_REWRITE_TAC [GSYM SPECIFICATION] THEN
  SIMP_TAC std_ss [IN_IMAGE, IN_UNIV] THEN METIS_TAC []);

val measure_space_borel = store_thm ("measure_space_borel",
  ``measure_space (space borel,subsets borel,(\x. 0))``,
  RW_TAC std_ss [measure_space_def, m_space_def, measurable_sets_def] THENL
  [SIMP_TAC std_ss [SPACE, sigma_algebra_borel],
   SIMP_TAC std_ss [positive_def, measure_def, measurable_sets_def, le_refl],
   ALL_TAC] THEN
  SIMP_TAC std_ss [countably_additive_alt_eq, o_DEF, suminf_0]);

val lebesgue_real_affine = store_thm ("lebesgue_real_affine",
  ``!c t. c <> 0 ==>
      (measure_of lborel = measure_of (density
         (distr lborel (space borel, subsets borel, (\x. 0)) (\x. t + c * x))
                       (\z. Normal (abs c))))``,
  RW_TAC std_ss [] THEN MATCH_MP_TAC lborel_eqI THEN
  CONJ_TAC THENL
  [ALL_TAC,
   CONJ_TAC THENL [ALL_TAC, METIS_TAC [density, distr, measurable_sets_def]] THEN
   MATCH_MP_TAC measure_space_density THEN CONJ_TAC THENL
   [ALL_TAC, MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST THEN
    Q.EXISTS_TAC `Normal (abs c)` THEN
    SIMP_TAC std_ss [m_space_def, measurable_sets_def, distr] THEN
    SIMP_TAC std_ss [SPACE, sigma_algebra_borel]] THEN
   MATCH_MP_TAC measure_space_distr THEN
   SIMP_TAC std_ss [measure_space_borel, measure_space_lborel] THEN
   SIMP_TAC std_ss [m_space_def, measurable_sets_def, SPACE] THEN
    SIMP_TAC std_ss [GSYM borel_measurable] THEN MATCH_MP_TAC borel_measurable_add THEN
    Q.EXISTS_TAC `(\x. t)` THEN Q.EXISTS_TAC `(\x. c * x)` THEN
    CONJ_TAC THENL [METIS_TAC [lborel, GSYM space_borel, m_space_def,
      measurable_sets_def, sigma_algebra_borel, SPACE], ALL_TAC] THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC borel_measurable_const THEN
     METIS_TAC [lborel, GSYM space_borel, m_space_def,
      measurable_sets_def, sigma_algebra_borel, SPACE],
     ALL_TAC] THEN
    SIMP_TAC std_ss [] THEN MATCH_MP_TAC borel_measurable_cmul THEN
    Q.EXISTS_TAC `(\x. x)` THEN Q.EXISTS_TAC `c` THEN
    ASM_SIMP_TAC std_ss [] THEN
    CONJ_TAC THENL [METIS_TAC [lborel, GSYM space_borel, m_space_def,
      measurable_sets_def, sigma_algebra_borel, SPACE], ALL_TAC] THEN
    Q_TAC SUFF_TAC `(\x:real. x) = I` THENL
    [DISC_RW_KILL, SIMP_TAC std_ss [FUN_EQ_THM]] THEN
    SIMP_TAC std_ss [borel_measurable, m_space_def, measurable_sets_def, SPACE, lborel] THEN
    SIMP_TAC std_ss [GSYM space_borel, SPACE] THEN MATCH_MP_TAC MEASURABLE_I THEN
    SIMP_TAC std_ss [sigma_algebra_borel]] THEN
  RW_TAC std_ss [] THEN ASM_CASES_TAC ``0 < c:real`` THENL
  [Q_TAC SUFF_TAC `PREIMAGE (\x. t + c * x) (interval [a,b]) =
                   interval [(a - t) / c, (b - t) / c]` THENL
   [SIMP_TAC std_ss [] THEN DISCH_TAC,
    SIMP_TAC std_ss [PREIMAGE_def, interval] THEN
    SIMP_TAC std_ss [EXTENSION, GSPECIFICATION] THEN
    ASM_SIMP_TAC real_ss [REAL_LE_RDIV_EQ, REAL_LE_LDIV_EQ] THEN
    REAL_ARITH_TAC] THEN
   SIMP_TAC std_ss [density, measure_def] THEN
   `interval [(a,b)] IN measurable_sets
    (distr lborel (space borel,subsets borel,(\x. 0)) (\x. t + c * x))` by
    METIS_TAC [borel_closed, CLOSED_INTERVAL, distr, measurable_sets_def] THEN
   ASM_SIMP_TAC std_ss [] THEN

   Q_TAC SUFF_TAC `pos_fn_integral
    (distr lborel (space borel,subsets borel,(\x. 0)) (\x. t + c * x))
    (\z. max 0 ((\z. Normal (abs c) * indicator_fn (interval [(a,b)]) z) z)) =
     pos_fn_integral lborel
    (\z. max 0 ((\z. Normal (abs c) * indicator_fn (interval [(a,b)]) z)
         ((\x. t + c * x) z)))` THENL
    [SIMP_TAC std_ss [] THEN DISC_RW_KILL,
     MATCH_MP_TAC pos_fn_integral_distr' THEN ASM_SIMP_TAC std_ss [measure_space_lborel] THEN
     SIMP_TAC std_ss [m_space_def, measurable_sets_def, lborel, distr, GSYM space_borel] THEN
     SIMP_TAC std_ss [measure_space_borel] THEN CONJ_TAC THENL
     [Q_TAC SUFF_TAC `(\x. t + c * x) IN
       measurable (m_space (space borel,subsets borel, (\x. 0)),
           measurable_sets (space borel,subsets borel, (\x. 0))) borel` THENL
      [SIMP_TAC std_ss [SPACE, m_space_def, measurable_sets_def], ALL_TAC] THEN
      REWRITE_TAC [GSYM borel_measurable] THEN MATCH_MP_TAC borel_measurable_add THEN
      Q.EXISTS_TAC `(\x. t)` THEN Q.EXISTS_TAC `(\x. c * x)` THEN
      CONJ_TAC THENL
      [METIS_TAC [m_space_def, measurable_sets_def, SPACE, sigma_algebra_borel],
       ALL_TAC] THEN
      CONJ_TAC THENL
      [MATCH_MP_TAC borel_measurable_const THEN
       METIS_TAC [m_space_def, measurable_sets_def, SPACE, sigma_algebra_borel],
       ALL_TAC] THEN
      CONJ_TAC THENL
      [MATCH_MP_TAC borel_measurable_cmul THEN Q.EXISTS_TAC `(\x. x)` THEN
       Q.EXISTS_TAC `c` THEN SIMP_TAC std_ss [] THEN
       CONJ_TAC THENL
       [METIS_TAC [m_space_def, measurable_sets_def, SPACE, sigma_algebra_borel],
        ALL_TAC] THEN
       Q_TAC SUFF_TAC `(\x:real. x) = I` THENL
       [DISC_RW_KILL, SIMP_TAC std_ss [FUN_EQ_THM]] THEN
       SIMP_TAC std_ss [borel_measurable, m_space_def, measurable_sets_def, SPACE] THEN
       MATCH_MP_TAC MEASURABLE_I THEN SIMP_TAC std_ss [sigma_algebra_borel],
       ALL_TAC] THEN
      SIMP_TAC std_ss [], ALL_TAC] THEN
   CONJ_TAC THENL
   [ALL_TAC,
    GEN_TAC THEN MATCH_MP_TAC le_mul THEN
    ASM_SIMP_TAC std_ss [indicator_fn_pos_le, extreal_of_num_def] THEN
    ASM_SIMP_TAC std_ss [extreal_le_def, abs, REAL_LE_LT]] THEN
   Q_TAC SUFF_TAC `(\z. (\z. Normal (abs c)) z * (\z. indicator_fn (interval [(a,b)]) z) z) IN
                      measurable (m_space (space borel,subsets borel, (\x. 0)),
                      measurable_sets (space borel,subsets borel, (\x. 0))) Borel` THENL
   [SIMP_TAC std_ss [m_space_def, measurable_sets_def], ALL_TAC] THEN
   MATCH_MP_TAC IN_MEASURABLE_BOREL_TIMES THEN Q.EXISTS_TAC `(\z. Normal (abs c))` THEN
   Q.EXISTS_TAC `(\z. indicator_fn (interval [(a,b)]) z)` THEN
   ASM_SIMP_TAC std_ss [measure_space_borel] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST THEN Q.EXISTS_TAC `Normal (abs c)` THEN
    SIMP_TAC std_ss [m_space_def, measurable_sets_def, sigma_algebra_borel, SPACE],
    ALL_TAC] THEN
   MATCH_MP_TAC IN_MEASURABLE_BOREL_INDICATOR THEN
   Q.EXISTS_TAC `(interval [(a,b)])` THEN
   ASM_SIMP_TAC std_ss [m_space_def, measurable_sets_def, sigma_algebra_borel, SPACE] THEN
   METIS_TAC [borel_closed, CLOSED_INTERVAL]] THEN

   Q_TAC SUFF_TAC `(\z. max 0
          (Normal (abs c) * indicator_fn (interval [(a,b)]) (t + c * z))) =
     (\z. (Normal (abs c) * indicator_fn (interval [(a,b)]) (t + c * z)))` THENL
   [DISC_RW_KILL,
    SIMP_TAC std_ss [FUN_EQ_THM, extreal_max_def] THEN GEN_TAC THEN
    Q_TAC SUFF_TAC `0 <= Normal (abs c) * indicator_fn (interval [(a,b)]) (t + c * z)` THENL
    [METIS_TAC [], ALL_TAC] THEN
    MATCH_MP_TAC le_mul THEN
    ASM_SIMP_TAC std_ss [indicator_fn_pos_le, extreal_of_num_def] THEN
    ASM_SIMP_TAC std_ss [extreal_le_def, abs, REAL_LE_LT]] THEN
   Q_TAC SUFF_TAC `pos_fn_integral lborel
    (\z. Normal (abs c) * (\z. indicator_fn (interval [(a,b)]) (t + c * z)) z) =
         Normal (abs c) * pos_fn_integral lborel
    (\z. indicator_fn (interval [(a,b)]) (t + c * z))` THENL
   [SIMP_TAC std_ss [] THEN DISC_RW_KILL,
    MATCH_MP_TAC pos_fn_integral_cmul THEN
    SIMP_TAC std_ss [ABS_POS, measure_space_lborel, indicator_fn_pos_le]] THEN
   Q_TAC SUFF_TAC `(\z. indicator_fn (interval [(a,b)]) (t + c * z)) =
                   (\z. indicator_fn (interval [((a - t) / c,(b - t) / c)]) z)` THENL
   [DISC_RW_KILL,
    SIMP_TAC std_ss [FUN_EQ_THM, indicator_fn_def] THEN
    RULE_ASSUM_TAC (ONCE_REWRITE_RULE [EQ_SYM_EQ]) THEN
    ASM_SIMP_TAC real_ss [IN_INTERVAL, REAL_LE_RDIV_EQ, REAL_LE_LDIV_EQ] THEN
    ONCE_REWRITE_TAC [REAL_ARITH ``a <= t + c * z /\ t + c * z <= b:real =
                                   a - t <= z * c /\ z * c <= b - t:real``] THEN
    SIMP_TAC std_ss []] THEN
   ONCE_REWRITE_TAC [METIS [ETA_AX] ``(\x. indicator_fn A x) = (indicator_fn A)``] THEN
   Q_TAC SUFF_TAC `(interval [((a - t) / c,(b - t) / c)]) IN measurable_sets lborel` THENL
   [DISCH_TAC,
    METIS_TAC [lborel, measurable_sets_def, borel_closed, CLOSED_INTERVAL]] THEN
   `measure_space lborel` by SIMP_TAC std_ss [measure_space_lborel] THEN
   ASM_SIMP_TAC std_ss [pos_fn_integral_indicator] THEN
   SIMP_TAC std_ss [measure_def, lborel, measure_lebesgue] THEN
   Q_TAC SUFF_TAC `!n. integral (line n)
      (indicator (interval [((a - t) / c,(b - t) / c)])) =
       content (interval [((a - t) / c,(b - t) / c)] INTER line n)` THENL
   [DISC_RW_KILL,
    GEN_TAC THEN MATCH_MP_TAC INTEGRAL_UNIQUE THEN
    SIMP_TAC std_ss [has_integral_interval_cube]] THEN
   SIMP_TAC std_ss [GSYM IMAGE_DEF, GSYM sup_cmul, ABS_POS] THEN
   `0 <= c` by ASM_SIMP_TAC std_ss [REAL_LT_IMP_LE] THEN
   FULL_SIMP_TAC std_ss [GSYM ABS_REFL] THEN POP_ASSUM K_TAC THEN

   ASM_CASES_TAC ``a <= b:real`` THENL
   [ALL_TAC,
    `b <= a` by FULL_SIMP_TAC real_ss [REAL_LE_LT, REAL_NOT_LE] THEN
    POP_ASSUM (ASSUME_TAC o ONCE_REWRITE_RULE [GSYM CONTENT_EQ_0]) THEN
    `0 < inv c` by ASM_SIMP_TAC std_ss [REAL_LT_INV_EQ] THEN
    `(b - t) / c <= (a - t) / c` by
     (ASM_SIMP_TAC std_ss [real_div, REAL_LE_RMUL] THEN ASM_REAL_ARITH_TAC) THEN
    POP_ASSUM (ASSUME_TAC o ONCE_REWRITE_RULE [GSYM CONTENT_EQ_0]) THEN
    ASM_SIMP_TAC std_ss [sup_eq] THEN CONJ_TAC THENL
    [GEN_TAC THEN GEN_REWR_TAC LAND_CONV [GSYM SPECIFICATION] THEN
     SIMP_TAC std_ss [IN_IMAGE, IN_UNIV] THEN RW_TAC std_ss [] THEN
     SIMP_TAC std_ss [extreal_mul_def, REAL_LE_LT, extreal_le_def] THEN
     DISJ2_TAC THEN ONCE_REWRITE_TAC [REAL_MUL_COMM] THEN
     ASM_SIMP_TAC real_ss [GSYM REAL_EQ_RDIV_EQ, real_div] THEN
     MATCH_MP_TAC CONTENT_0_SUBSET THEN Q.EXISTS_TAC `(a - t) / c` THEN
     Q.EXISTS_TAC `(b - t) / c` THEN ASM_SIMP_TAC std_ss [] THEN
     SIMP_TAC std_ss [SUBSET_DEF, IN_INTERVAL, IN_INTER] THEN
     SIMP_TAC std_ss [real_div],
     ALL_TAC] THEN
    GEN_TAC THEN DISCH_THEN MATCH_MP_TAC THEN
    ONCE_REWRITE_TAC [GSYM SPECIFICATION] THEN SIMP_TAC std_ss [IN_IMAGE, IN_UNIV] THEN
    SIMP_TAC std_ss [line, INTER_INTERVAL, GSYM interval] THEN
    Q_TAC SUFF_TAC `!n. min ((b - t) / c) (&n) <= max ((a - t) / c) (-&n)` THENL
    [RW_TAC real_ss [GSYM CONTENT_EQ_0, extreal_mul_def], ALL_TAC] THEN
    GEN_TAC THEN SIMP_TAC std_ss [min_def, max_def] THEN
    RW_TAC real_ss [REAL_LE_LDIV_EQ, REAL_LE_RDIV_EQ] THEN
    FULL_SIMP_TAC real_ss [] THEN TRY (ASM_REAL_ARITH_TAC) THENL
    [ASM_SIMP_TAC real_ss [real_div, REAL_MUL_LINV, GSYM REAL_MUL_ASSOC] THEN
     FULL_SIMP_TAC std_ss [CONTENT_EQ_0], ALL_TAC] THEN
    UNDISCH_TAC ``~(b - t <= &n * c:real)`` THEN ONCE_REWRITE_TAC [MONO_NOT_EQ] THEN
    RW_TAC std_ss [] THEN FULL_SIMP_TAC std_ss [CONTENT_EQ_0, real_div] THEN
    `0 < inv c` by ASM_SIMP_TAC std_ss [REAL_LT_INV_EQ] THEN
    FULL_SIMP_TAC std_ss [REAL_LE_RMUL, REAL_NEG_LMUL] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN Q.EXISTS_TAC `a - t` THEN
    ASM_SIMP_TAC std_ss [] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    Q.EXISTS_TAC `-&n * c` THEN ASM_SIMP_TAC std_ss [REAL_LE_RMUL] THEN
    SIMP_TAC real_ss []] THEN

   `0 < inv c` by ASM_SIMP_TAC std_ss [REAL_LT_INV_EQ] THEN
   `(a - t) / c <= (b - t) / c` by
     (ASM_SIMP_TAC std_ss [real_div, REAL_LE_RMUL] THEN ASM_REAL_ARITH_TAC) THEN
   SIMP_TAC std_ss [sup_eq] THEN CONJ_TAC THENL
   [GEN_TAC THEN GEN_REWR_TAC LAND_CONV [GSYM SPECIFICATION] THEN
    SIMP_TAC std_ss [IN_IMAGE, IN_UNIV] THEN RW_TAC std_ss [extreal_mul_def] THEN
    SIMP_TAC std_ss [extreal_le_def, line, INTER_INTERVAL, GSYM interval] THEN
    ASM_CASES_TAC ``max ((a - t) / c) (-&n) <= min ((b - t) / c) (&n:real)`` THENL
    [ALL_TAC, FULL_SIMP_TAC std_ss [REAL_NOT_LE] THEN
     `min ((b - t) / c) (&n) <= max ((a - t) / c) (-&n)`
      by ASM_SIMP_TAC std_ss [REAL_LE_LT] THEN
     POP_ASSUM (ASSUME_TAC o ONCE_REWRITE_RULE [GSYM CONTENT_EQ_0]) THEN
     ASM_SIMP_TAC real_ss [CONTENT_CLOSED_INTERVAL] THEN ASM_REAL_ARITH_TAC] THEN
    ASM_SIMP_TAC std_ss [CONTENT_CLOSED_INTERVAL] THEN
    ONCE_REWRITE_TAC [REAL_MUL_COMM] THEN ASM_SIMP_TAC std_ss [GSYM REAL_LE_RDIV_EQ] THEN
    Q_TAC SUFF_TAC `(b - a) / c = (b - t) / c - (a - t) / c` THENL
    [DISC_RW_KILL THEN FULL_SIMP_TAC std_ss [min_def, max_def] THEN
     ASM_REAL_ARITH_TAC, ALL_TAC] THEN
    SIMP_TAC std_ss [real_sub, REAL_DIV_ADD, real_div] THEN
    REAL_ARITH_TAC,
    ALL_TAC] THEN

   GEN_TAC THEN DISCH_THEN MATCH_MP_TAC THEN ONCE_REWRITE_TAC [GSYM SPECIFICATION] THEN
   SIMP_TAC std_ss [IN_IMAGE, IN_UNIV, extreal_mul_def, extreal_11] THEN
   SIMP_TAC std_ss [line, INTER_INTERVAL, GSYM interval] THEN
   `?n. abs ((a - t) / c) <= &n` by METIS_TAC [SIMP_REAL_ARCH] THEN
   `?m. abs ((b - t) / c) <= &m` by METIS_TAC [SIMP_REAL_ARCH] THEN
   Q.EXISTS_TAC `MAX n m` THEN
   Q_TAC SUFF_TAC `max ((a - t) / c) (-&MAX n m) = (a - t) / c` THENL
   [DISC_RW_KILL,
    RW_TAC std_ss [max_def, MAX_DEF] THEN FULL_SIMP_TAC std_ss [] THENL
    [ASM_SIMP_TAC std_ss [GSYM REAL_LE_ANTISYM] THEN
     UNDISCH_TAC ``abs ((b - t) / c) <= &m:real`` THEN
     UNDISCH_TAC ``abs ((a - t) / c) <= &n:real`` THEN
     FULL_SIMP_TAC real_ss [abs, REAL_LE_RDIV_EQ, REAL_LE_LDIV_EQ] THEN
     RW_TAC std_ss [] THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
     FULL_SIMP_TAC real_ss [REAL_LE_RDIV_EQ, REAL_LE_LDIV_EQ] THEN
     RW_TAC std_ss [] THEN TRY (ASM_REAL_ARITH_TAC) THENL
     [UNDISCH_TAC `` -((a - t) / c) <= &n:real`` THEN
      GEN_REWR_TAC LAND_CONV [GSYM REAL_LE_NEG] THEN
      ASM_SIMP_TAC std_ss [REAL_LE_RDIV_EQ, REAL_NEG_NEG] THEN DISCH_TAC THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN Q.EXISTS_TAC `-&n * c` THEN
      ASM_SIMP_TAC std_ss [REAL_NEG_LMUL] THEN
     ASM_SIMP_TAC real_ss [REAL_LE_RMUL],
      ALL_TAC] THEN
     UNDISCH_TAC `` -((a - t) / c) <= &n:real`` THEN
     GEN_REWR_TAC LAND_CONV [GSYM REAL_LE_NEG] THEN
     ASM_SIMP_TAC std_ss [REAL_LE_RDIV_EQ, REAL_NEG_NEG] THEN DISCH_TAC THEN
     MATCH_MP_TAC REAL_LE_TRANS THEN Q.EXISTS_TAC `-&n * c` THEN
     ASM_SIMP_TAC std_ss [REAL_NEG_LMUL] THEN
     ASM_SIMP_TAC real_ss [REAL_LE_RMUL],
     ALL_TAC] THEN
    ASM_SIMP_TAC std_ss [GSYM REAL_LE_ANTISYM] THEN
    UNDISCH_TAC ``abs ((b - t) / c) <= &m:real`` THEN
    UNDISCH_TAC ``abs ((a - t) / c) <= &n:real`` THEN
    FULL_SIMP_TAC real_ss [abs, REAL_LE_RDIV_EQ, REAL_LE_LDIV_EQ] THEN
    RW_TAC std_ss [] THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
    FULL_SIMP_TAC real_ss [REAL_LE_RDIV_EQ, REAL_LE_LDIV_EQ] THEN
    RW_TAC std_ss [] THEN TRY (ASM_REAL_ARITH_TAC) THENL
    [UNDISCH_TAC `` -((a - t) / c) <= &n:real`` THEN
     GEN_REWR_TAC LAND_CONV [GSYM REAL_LE_NEG] THEN
     ASM_SIMP_TAC std_ss [REAL_LE_RDIV_EQ, REAL_NEG_NEG] THEN DISCH_TAC THEN
     MATCH_MP_TAC REAL_LE_TRANS THEN Q.EXISTS_TAC `-&n * c` THEN
     ASM_SIMP_TAC std_ss [REAL_NEG_LMUL] THEN
     ASM_SIMP_TAC real_ss [REAL_LE_RMUL],
     ALL_TAC] THEN
    UNDISCH_TAC `` -((a - t) / c) <= &n:real`` THEN
    GEN_REWR_TAC LAND_CONV [GSYM REAL_LE_NEG] THEN
    ASM_SIMP_TAC std_ss [REAL_LE_RDIV_EQ, REAL_NEG_NEG] THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN Q.EXISTS_TAC `-&n * c` THEN
    ASM_SIMP_TAC std_ss [REAL_NEG_LMUL] THEN
    ASM_SIMP_TAC real_ss [REAL_LE_RMUL]] THEN
   Q_TAC SUFF_TAC `min ((b - t) / c) (&MAX n m) = (b - t) / c` THENL
   [DISC_RW_KILL,
    RW_TAC std_ss [min_def, MAX_DEF] THEN FULL_SIMP_TAC std_ss [] THENL
    [UNDISCH_TAC ``~((b - t) / c <= &m:real)`` THEN
     ONCE_REWRITE_TAC [MONO_NOT_EQ] THEN RW_TAC std_ss [] THEN
     UNDISCH_TAC ``abs ((b - t) / c) <= &m:real`` THEN
     UNDISCH_TAC ``abs ((a - t) / c) <= &n:real`` THEN
     FULL_SIMP_TAC real_ss [abs, REAL_LE_RDIV_EQ, REAL_LE_LDIV_EQ] THEN
     RW_TAC std_ss [] THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
     FULL_SIMP_TAC real_ss [REAL_LE_RDIV_EQ, REAL_LE_LDIV_EQ] THEN
     RW_TAC std_ss [] THEN TRY (ASM_REAL_ARITH_TAC) THEN
     UNDISCH_TAC `` -((b - t) / c) <= &m:real`` THEN
     GEN_REWR_TAC LAND_CONV [GSYM REAL_LE_NEG] THEN
     ASM_SIMP_TAC std_ss [REAL_LE_RDIV_EQ, REAL_NEG_NEG] THEN DISCH_TAC THEN
     ASM_REAL_ARITH_TAC, ALL_TAC] THEN

    UNDISCH_TAC ``~((b - t) / c <= &n:real)`` THEN
    ONCE_REWRITE_TAC [MONO_NOT_EQ] THEN RW_TAC std_ss [] THEN
    UNDISCH_TAC ``abs ((b - t) / c) <= &m:real`` THEN
    UNDISCH_TAC ``abs ((a - t) / c) <= &n:real`` THEN
    FULL_SIMP_TAC real_ss [abs, REAL_LE_RDIV_EQ, REAL_LE_LDIV_EQ] THEN
    RW_TAC std_ss [] THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
    FULL_SIMP_TAC real_ss [REAL_LE_RDIV_EQ, REAL_LE_LDIV_EQ] THEN
    RW_TAC std_ss [] THEN TRY (ASM_REAL_ARITH_TAC) THENL
    [MATCH_MP_TAC REAL_LE_TRANS THEN Q.EXISTS_TAC `&m * c` THEN
     ASM_SIMP_TAC real_ss [REAL_LE_RMUL],
     MATCH_MP_TAC REAL_LE_TRANS THEN Q.EXISTS_TAC `&m * c` THEN
     ASM_SIMP_TAC real_ss [REAL_LE_RMUL],
     ALL_TAC] THEN
    UNDISCH_TAC `` -((a - t) / c) <= &n:real`` THEN
    GEN_REWR_TAC LAND_CONV [GSYM REAL_LE_NEG] THEN
    ASM_SIMP_TAC std_ss [REAL_LE_RDIV_EQ, REAL_NEG_NEG] THEN DISCH_TAC THEN
    UNDISCH_TAC `` -((b - t) / c) <= &m:real`` THEN
    GEN_REWR_TAC LAND_CONV [GSYM REAL_LE_NEG] THEN
    ASM_SIMP_TAC std_ss [REAL_LE_RDIV_EQ, REAL_NEG_NEG] THEN DISCH_TAC THEN
    ASM_REAL_ARITH_TAC] THEN
   ASM_SIMP_TAC std_ss [CONTENT_CLOSED_INTERVAL, real_div] THEN
   SIMP_TAC std_ss [GSYM REAL_SUB_RDISTRIB] THEN
   ONCE_REWRITE_TAC [REAL_ARITH ``a * (b * c) = b * (a * c:real)``] THEN
   ASM_SIMP_TAC real_ss [REAL_MUL_RINV] THEN REAL_ARITH_TAC,
   ALL_TAC] THEN
  Q.ABBREV_TAC `r = -c` THEN
  `0 < r` by (Q.UNABBREV_TAC `r` THEN
    ONCE_REWRITE_TAC [REAL_LT_NEG] THEN ASM_REAL_ARITH_TAC) THEN
  Q_TAC SUFF_TAC `abs c = abs r` THENL
  [DISC_RW_KILL,
   `~(0 <= c)` by ASM_REAL_ARITH_TAC THEN
   `0 <= r` by ASM_REAL_ARITH_TAC THEN
   ASM_SIMP_TAC std_ss [abs]] THEN
  Q_TAC SUFF_TAC `c = -r` THENL
  [DISC_RW_KILL,
   Q.UNABBREV_TAC `r` THEN SIMP_TAC std_ss [REAL_NEG_NEG]] THEN
  `r <> 0` by ASM_SIMP_TAC std_ss [REAL_LT_IMP_NE] THEN

  Q_TAC SUFF_TAC `PREIMAGE (\x. t + -r * x) (interval [a,b]) =
                   interval [(b - t) / -r, (a - t) / -r]` THENL
   [SIMP_TAC std_ss [] THEN DISCH_TAC,
    SIMP_TAC std_ss [PREIMAGE_def, interval] THEN
    SIMP_TAC std_ss [EXTENSION, GSPECIFICATION] THEN
    ASM_SIMP_TAC std_ss [real_div, GSYM REAL_NEG_INV] THEN
    SIMP_TAC std_ss [GSYM REAL_NEG_RMUL, REAL_NEG_LMUL, GSYM real_div] THEN
    ASM_SIMP_TAC real_ss [REAL_LE_RDIV_EQ, REAL_LE_LDIV_EQ] THEN
    REAL_ARITH_TAC] THEN

   SIMP_TAC std_ss [density, measure_def] THEN
   `interval [(a,b)] IN measurable_sets
    (distr lborel (space borel,subsets borel,(\x. 0)) (\x. t + -r * x))` by
    METIS_TAC [borel_closed, CLOSED_INTERVAL, distr, measurable_sets_def] THEN
   ASM_SIMP_TAC std_ss [] THEN

   Q_TAC SUFF_TAC `pos_fn_integral
    (distr lborel (space borel,subsets borel,(\x. 0)) (\x. t + -r * x))
    (\z. max 0 ((\z. Normal (abs r) * indicator_fn (interval [(a,b)]) z) z)) =
     pos_fn_integral lborel
    (\z. max 0 ((\z. Normal (abs r) * indicator_fn (interval [(a,b)]) z)
         ((\x. t + -r * x) z)))` THENL
    [SIMP_TAC std_ss [] THEN DISC_RW_KILL,
     MATCH_MP_TAC pos_fn_integral_distr' THEN ASM_SIMP_TAC std_ss [measure_space_lborel] THEN
     SIMP_TAC std_ss [m_space_def, measurable_sets_def, lborel, distr, GSYM space_borel] THEN
     SIMP_TAC std_ss [measure_space_borel] THEN CONJ_TAC THENL
     [Q_TAC SUFF_TAC `(\x. t + -r * x) IN
       measurable (m_space (space borel,subsets borel, (\x. 0)),
           measurable_sets (space borel,subsets borel, (\x. 0))) borel` THENL
      [SIMP_TAC std_ss [SPACE, m_space_def, measurable_sets_def], ALL_TAC] THEN
      REWRITE_TAC [GSYM borel_measurable] THEN MATCH_MP_TAC borel_measurable_add THEN
      Q.EXISTS_TAC `(\x. t)` THEN Q.EXISTS_TAC `(\x. -r * x)` THEN
      CONJ_TAC THENL
      [METIS_TAC [m_space_def, measurable_sets_def, SPACE, sigma_algebra_borel],
       ALL_TAC] THEN
      CONJ_TAC THENL
      [MATCH_MP_TAC borel_measurable_const THEN
       METIS_TAC [m_space_def, measurable_sets_def, SPACE, sigma_algebra_borel],
       ALL_TAC] THEN
      CONJ_TAC THENL
      [MATCH_MP_TAC borel_measurable_cmul THEN Q.EXISTS_TAC `(\x. x)` THEN
       Q.EXISTS_TAC `-r` THEN SIMP_TAC std_ss [] THEN
       CONJ_TAC THENL
       [METIS_TAC [m_space_def, measurable_sets_def, SPACE, sigma_algebra_borel],
        ALL_TAC] THEN
       Q_TAC SUFF_TAC `(\x:real. x) = I` THENL
       [DISC_RW_KILL, SIMP_TAC std_ss [FUN_EQ_THM]] THEN
       SIMP_TAC std_ss [borel_measurable, m_space_def, measurable_sets_def, SPACE] THEN
       MATCH_MP_TAC MEASURABLE_I THEN SIMP_TAC std_ss [sigma_algebra_borel],
       ALL_TAC] THEN
      SIMP_TAC std_ss [], ALL_TAC] THEN
   CONJ_TAC THENL
   [ALL_TAC,
    GEN_TAC THEN MATCH_MP_TAC le_mul THEN
    ASM_SIMP_TAC std_ss [indicator_fn_pos_le, extreal_of_num_def] THEN
    ASM_SIMP_TAC std_ss [extreal_le_def, abs, REAL_LE_LT]] THEN
   Q_TAC SUFF_TAC `(\z. (\z. Normal (abs r)) z * (\z. indicator_fn (interval [(a,b)]) z) z) IN
                      measurable (m_space (space borel,subsets borel, (\x. 0)),
                      measurable_sets (space borel,subsets borel, (\x. 0))) Borel` THENL
   [SIMP_TAC std_ss [m_space_def, measurable_sets_def], ALL_TAC] THEN
   MATCH_MP_TAC IN_MEASURABLE_BOREL_TIMES THEN Q.EXISTS_TAC `(\z. Normal (abs r))` THEN
   Q.EXISTS_TAC `(\z. indicator_fn (interval [(a,b)]) z)` THEN
   ASM_SIMP_TAC std_ss [measure_space_borel] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST THEN Q.EXISTS_TAC `Normal (abs r)` THEN
    SIMP_TAC std_ss [m_space_def, measurable_sets_def, sigma_algebra_borel, SPACE],
    ALL_TAC] THEN
   MATCH_MP_TAC IN_MEASURABLE_BOREL_INDICATOR THEN
   Q.EXISTS_TAC `(interval [(a,b)])` THEN
   ASM_SIMP_TAC std_ss [m_space_def, measurable_sets_def, sigma_algebra_borel, SPACE] THEN
   METIS_TAC [borel_closed, CLOSED_INTERVAL]] THEN

   Q_TAC SUFF_TAC `(\z. max 0
          (Normal (abs r) * indicator_fn (interval [(a,b)]) (t + -r * z))) =
     (\z. (Normal (abs r) * indicator_fn (interval [(a,b)]) (t + -r * z)))` THENL
   [DISC_RW_KILL,
    SIMP_TAC std_ss [FUN_EQ_THM, extreal_max_def] THEN GEN_TAC THEN
    Q_TAC SUFF_TAC `0 <= Normal (abs r) * indicator_fn (interval [(a,b)]) (t + -r * z)` THENL
    [METIS_TAC [], ALL_TAC] THEN
    MATCH_MP_TAC le_mul THEN
    ASM_SIMP_TAC std_ss [indicator_fn_pos_le, extreal_of_num_def] THEN
    ASM_SIMP_TAC std_ss [extreal_le_def, abs, REAL_LE_LT]] THEN

   Q_TAC SUFF_TAC `pos_fn_integral lborel
    (\z. Normal (abs r) * (\z. indicator_fn (interval [(a,b)]) (t + -r * z)) z) =
         Normal (abs r) * pos_fn_integral lborel
    (\z. indicator_fn (interval [(a,b)]) (t + -r * z))` THENL
   [SIMP_TAC std_ss [] THEN DISC_RW_KILL,
    MATCH_MP_TAC pos_fn_integral_cmul THEN
    SIMP_TAC std_ss [ABS_POS, measure_space_lborel, indicator_fn_pos_le]] THEN
   Q_TAC SUFF_TAC `(\z. indicator_fn (interval [(a,b)]) (t + -r * z)) =
                   (\z. indicator_fn (interval [((b - t) / -r,(a - t) / -r)]) z)` THENL
   [DISC_RW_KILL,
    SIMP_TAC std_ss [FUN_EQ_THM, indicator_fn_def] THEN
    RULE_ASSUM_TAC (ONCE_REWRITE_RULE [EQ_SYM_EQ]) THEN
    SIMP_TAC real_ss [IN_INTERVAL] THEN
    ONCE_REWRITE_TAC [real_div] THEN
    `inv (-r) = -inv r` by METIS_TAC [REAL_NEG_INV] THEN
    POP_ASSUM (fn th => REWRITE_TAC [th]) THEN
    SIMP_TAC std_ss [GSYM REAL_NEG_RMUL, REAL_NEG_LMUL, GSYM real_div] THEN
    ASM_SIMP_TAC real_ss [REAL_LE_RDIV_EQ, REAL_LE_LDIV_EQ] THEN GEN_TAC THEN
    ONCE_REWRITE_TAC [REAL_ARITH ``a <= t + c * z /\ t + c * z <= b:real =
                                   t - b <= -(z * c) /\ -(z * c) <= t - a:real``] THEN
    SIMP_TAC std_ss []] THEN
   ONCE_REWRITE_TAC [METIS [ETA_AX] ``(\x. indicator_fn A x) = (indicator_fn A)``] THEN
   Q_TAC SUFF_TAC `(interval [((b - t) / -r,(a - t) / -r)]) IN measurable_sets lborel` THENL
   [DISCH_TAC,
    METIS_TAC [lborel, measurable_sets_def, borel_closed, CLOSED_INTERVAL]] THEN
   `measure_space lborel` by SIMP_TAC std_ss [measure_space_lborel] THEN
   ASM_SIMP_TAC std_ss [pos_fn_integral_indicator] THEN
   SIMP_TAC std_ss [measure_def, lborel, measure_lebesgue] THEN
   Q_TAC SUFF_TAC `!n. integral (line n)
      (indicator (interval [((b - t) / -r,(a - t) / -r)])) =
       content (interval [((b - t) / -r,(a - t) / -r)] INTER line n)` THENL
   [DISC_RW_KILL,
    GEN_TAC THEN MATCH_MP_TAC INTEGRAL_UNIQUE THEN
    SIMP_TAC std_ss [has_integral_interval_cube]] THEN
   SIMP_TAC std_ss [GSYM IMAGE_DEF, GSYM sup_cmul, ABS_POS] THEN
   `0 <= r` by ASM_SIMP_TAC std_ss [REAL_LT_IMP_LE] THEN
   FULL_SIMP_TAC std_ss [GSYM ABS_REFL] THEN POP_ASSUM K_TAC THEN

   ASM_CASES_TAC ``a <= b:real`` THENL
   [ALL_TAC,
    `b <= a` by FULL_SIMP_TAC real_ss [REAL_LE_LT, REAL_NOT_LE] THEN
    POP_ASSUM (ASSUME_TAC o ONCE_REWRITE_RULE [GSYM CONTENT_EQ_0]) THEN
    ONCE_REWRITE_TAC [real_div] THEN
    `inv (-r) = -inv r` by METIS_TAC [REAL_NEG_INV] THEN
    POP_ASSUM (fn th => REWRITE_TAC [th]) THEN
    SIMP_TAC std_ss [GSYM REAL_NEG_RMUL, REAL_NEG_LMUL, GSYM real_div] THEN
    `0 < inv r` by ASM_SIMP_TAC std_ss [REAL_LT_INV_EQ] THEN
    `-(a - t) / r <= -(b - t) / r` by
     (ASM_SIMP_TAC std_ss [real_div, REAL_LE_RMUL] THEN ASM_REAL_ARITH_TAC) THEN
    POP_ASSUM (ASSUME_TAC o ONCE_REWRITE_RULE [GSYM CONTENT_EQ_0]) THEN
    ASM_SIMP_TAC std_ss [sup_eq] THEN CONJ_TAC THENL
    [GEN_TAC THEN GEN_REWR_TAC LAND_CONV [GSYM SPECIFICATION] THEN
     SIMP_TAC std_ss [IN_IMAGE, IN_UNIV] THEN RW_TAC std_ss [] THEN
     SIMP_TAC std_ss [extreal_mul_def, REAL_LE_LT, extreal_le_def] THEN
     DISJ2_TAC THEN ONCE_REWRITE_TAC [REAL_MUL_COMM] THEN
     ASM_SIMP_TAC real_ss [GSYM REAL_EQ_RDIV_EQ, real_div] THEN
     MATCH_MP_TAC CONTENT_0_SUBSET THEN Q.EXISTS_TAC `-(b - t) / r` THEN
     Q.EXISTS_TAC `-(a - t) / r` THEN ASM_SIMP_TAC std_ss [] THEN
     SIMP_TAC std_ss [SUBSET_DEF, IN_INTERVAL, IN_INTER] THEN
     SIMP_TAC std_ss [real_div, REAL_NEG_LMUL],
     ALL_TAC] THEN
    GEN_TAC THEN DISCH_THEN MATCH_MP_TAC THEN
    ONCE_REWRITE_TAC [GSYM SPECIFICATION] THEN SIMP_TAC std_ss [IN_IMAGE, IN_UNIV] THEN
    SIMP_TAC std_ss [line, INTER_INTERVAL, GSYM interval] THEN
    Q_TAC SUFF_TAC `!n. min (-(a - t) / r) (&n) <= max (-(b - t) / r) (-&n)` THENL
    [RW_TAC real_ss [GSYM CONTENT_EQ_0, extreal_mul_def], ALL_TAC] THEN
    GEN_TAC THEN SIMP_TAC std_ss [min_def, max_def] THEN
    RW_TAC real_ss [REAL_LE_LDIV_EQ, REAL_LE_RDIV_EQ] THEN
    FULL_SIMP_TAC real_ss [] THEN TRY (ASM_REAL_ARITH_TAC) THENL
    [ASM_SIMP_TAC real_ss [real_div, REAL_MUL_LINV, GSYM REAL_MUL_ASSOC] THEN
     FULL_SIMP_TAC std_ss [CONTENT_EQ_0] THEN ASM_REAL_ARITH_TAC, ALL_TAC] THEN
    UNDISCH_TAC ``~(t - a <= &n * r:real)`` THEN ONCE_REWRITE_TAC [MONO_NOT_EQ] THEN
    RW_TAC std_ss [] THEN FULL_SIMP_TAC std_ss [CONTENT_EQ_0, real_div] THEN
    `0 < inv r` by ASM_SIMP_TAC std_ss [REAL_LT_INV_EQ] THEN
    FULL_SIMP_TAC std_ss [REAL_LE_RMUL, REAL_NEG_LMUL] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN Q.EXISTS_TAC `t - b` THEN
    ASM_SIMP_TAC std_ss [] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    Q.EXISTS_TAC `-&n * r` THEN ASM_SIMP_TAC std_ss [REAL_LE_RMUL] THEN
    SIMP_TAC real_ss []] THEN

   `0 < inv r` by ASM_SIMP_TAC std_ss [REAL_LT_INV_EQ] THEN
   ASM_SIMP_TAC std_ss [real_div, GSYM REAL_NEG_INV] THEN
   SIMP_TAC std_ss [GSYM REAL_NEG_RMUL, REAL_NEG_LMUL, GSYM real_div] THEN
   `-(b - t) / r <= -(a - t) / r` by
     (ASM_SIMP_TAC std_ss [real_div, REAL_LE_RMUL] THEN ASM_REAL_ARITH_TAC) THEN
   SIMP_TAC std_ss [sup_eq] THEN CONJ_TAC THENL
   [GEN_TAC THEN GEN_REWR_TAC LAND_CONV [GSYM SPECIFICATION] THEN
    SIMP_TAC std_ss [IN_IMAGE, IN_UNIV] THEN RW_TAC std_ss [extreal_mul_def] THEN
    SIMP_TAC std_ss [extreal_le_def, line, INTER_INTERVAL, GSYM interval] THEN
    ASM_CASES_TAC ``max (-(b - t) / r) (-&n) <= min (-(a - t) / r) (&n:real)`` THENL
    [ALL_TAC, FULL_SIMP_TAC std_ss [REAL_NOT_LE] THEN
     `min (-(a - t) / r) (&n) <= max (-(b - t) / r) (-&n)`
      by ASM_SIMP_TAC std_ss [REAL_LE_LT] THEN
     POP_ASSUM (ASSUME_TAC o ONCE_REWRITE_RULE [GSYM CONTENT_EQ_0]) THEN
     ASM_SIMP_TAC real_ss [CONTENT_CLOSED_INTERVAL] THEN ASM_REAL_ARITH_TAC] THEN
    ASM_SIMP_TAC std_ss [CONTENT_CLOSED_INTERVAL] THEN
    ONCE_REWRITE_TAC [REAL_MUL_COMM] THEN ASM_SIMP_TAC std_ss [GSYM REAL_LE_RDIV_EQ] THEN
    Q_TAC SUFF_TAC `(b - a) / r = (-(a - t) / r) - (-(b - t) / r)` THENL
    [DISC_RW_KILL THEN FULL_SIMP_TAC std_ss [min_def, max_def] THEN
     ASM_REAL_ARITH_TAC, ALL_TAC] THEN
    SIMP_TAC std_ss [real_sub, REAL_DIV_ADD, real_div] THEN
    REAL_ARITH_TAC,
    ALL_TAC] THEN

   GEN_TAC THEN DISCH_THEN MATCH_MP_TAC THEN ONCE_REWRITE_TAC [GSYM SPECIFICATION] THEN
   SIMP_TAC std_ss [IN_IMAGE, IN_UNIV, extreal_mul_def, extreal_11] THEN
   SIMP_TAC std_ss [line, INTER_INTERVAL, GSYM interval] THEN
   `?n. abs (-(b - t) / r) <= &n` by METIS_TAC [SIMP_REAL_ARCH] THEN
   `?m. abs (-(a - t) / r) <= &m` by METIS_TAC [SIMP_REAL_ARCH] THEN
   Q.EXISTS_TAC `MAX n m` THEN
   Q_TAC SUFF_TAC `max (-(b - t) / r) (-&MAX n m) = -(b - t) / r` THENL
   [DISC_RW_KILL,
    RW_TAC std_ss [max_def, MAX_DEF] THEN FULL_SIMP_TAC std_ss [] THENL
    [ASM_SIMP_TAC std_ss [GSYM REAL_LE_ANTISYM] THEN
     UNDISCH_TAC ``abs (-(a - t) / r) <= &m:real`` THEN
     UNDISCH_TAC ``abs (-(b - t) / r) <= &n:real`` THEN
     FULL_SIMP_TAC real_ss [abs, REAL_LE_RDIV_EQ, REAL_LE_LDIV_EQ] THEN
     RW_TAC std_ss [] THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
     FULL_SIMP_TAC real_ss [REAL_LE_RDIV_EQ, REAL_LE_LDIV_EQ] THEN
     RW_TAC std_ss [] THEN TRY (ASM_REAL_ARITH_TAC) THENL
     [UNDISCH_TAC `` -((t - b) / r) <= &n:real`` THEN
      GEN_REWR_TAC LAND_CONV [GSYM REAL_LE_NEG] THEN
      ASM_SIMP_TAC std_ss [REAL_LE_RDIV_EQ, REAL_NEG_NEG] THEN DISCH_TAC THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN Q.EXISTS_TAC `-&n * r` THEN
      ASM_SIMP_TAC std_ss [REAL_NEG_LMUL] THEN
     ASM_SIMP_TAC real_ss [REAL_LE_RMUL],
      ALL_TAC] THEN
     UNDISCH_TAC `` -((t - a) / r) <= &m:real`` THEN
     GEN_REWR_TAC LAND_CONV [GSYM REAL_LE_NEG] THEN
     ASM_SIMP_TAC std_ss [REAL_LE_RDIV_EQ, REAL_NEG_NEG] THEN DISCH_TAC THEN
     UNDISCH_TAC `` -((t - b) / r) <= &n:real`` THEN
     GEN_REWR_TAC LAND_CONV [GSYM REAL_LE_NEG] THEN
     ASM_SIMP_TAC std_ss [REAL_LE_RDIV_EQ, REAL_NEG_NEG] THEN DISCH_TAC THEN
     MATCH_MP_TAC REAL_LE_TRANS THEN Q.EXISTS_TAC `-&n * r` THEN
     ASM_SIMP_TAC std_ss [REAL_NEG_LMUL] THEN
     ASM_SIMP_TAC real_ss [REAL_LE_RMUL],
     ALL_TAC] THEN

    ASM_SIMP_TAC std_ss [GSYM REAL_LE_ANTISYM] THEN
    UNDISCH_TAC ``abs (-(a - t) / r) <= &m:real`` THEN
    UNDISCH_TAC ``abs (-(b - t) / r) <= &n:real`` THEN
    FULL_SIMP_TAC real_ss [abs, REAL_LE_RDIV_EQ, REAL_LE_LDIV_EQ] THEN
    RW_TAC std_ss [] THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
    FULL_SIMP_TAC real_ss [REAL_LE_RDIV_EQ, REAL_LE_LDIV_EQ] THEN
    RW_TAC std_ss [] THEN TRY (ASM_REAL_ARITH_TAC) THENL
    [UNDISCH_TAC `` -((t - b) / r) <= &n:real`` THEN
     GEN_REWR_TAC LAND_CONV [GSYM REAL_LE_NEG] THEN
     ASM_SIMP_TAC std_ss [REAL_LE_RDIV_EQ, REAL_NEG_NEG] THEN DISCH_TAC THEN
     MATCH_MP_TAC REAL_LE_TRANS THEN Q.EXISTS_TAC `-&n * r` THEN
     ASM_SIMP_TAC std_ss [REAL_NEG_LMUL] THEN
     ASM_SIMP_TAC real_ss [REAL_LE_RMUL],
     ALL_TAC] THEN
    UNDISCH_TAC `` -((t - b) / r) <= &n:real`` THEN
    GEN_REWR_TAC LAND_CONV [GSYM REAL_LE_NEG] THEN
    ASM_SIMP_TAC std_ss [REAL_LE_RDIV_EQ, REAL_NEG_NEG] THEN DISCH_TAC THEN
    UNDISCH_TAC `` -((t - a) / r) <= &m:real`` THEN
    GEN_REWR_TAC LAND_CONV [GSYM REAL_LE_NEG] THEN
    ASM_SIMP_TAC std_ss [REAL_LE_RDIV_EQ, REAL_NEG_NEG] THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN Q.EXISTS_TAC `-&n * r` THEN
    ASM_SIMP_TAC std_ss [REAL_NEG_LMUL] THEN
    ASM_SIMP_TAC real_ss [REAL_LE_RMUL]] THEN

   Q_TAC SUFF_TAC `min (-(a - t) / r) (&MAX n m) = -(a - t) / r` THENL
   [DISC_RW_KILL,
    RW_TAC std_ss [min_def, MAX_DEF] THEN FULL_SIMP_TAC std_ss [] THENL
    [UNDISCH_TAC ``~(-(a - t) / r <= &m:real)`` THEN
     ONCE_REWRITE_TAC [MONO_NOT_EQ] THEN RW_TAC std_ss [] THEN
     UNDISCH_TAC ``abs (-(a - t) / r) <= &m:real`` THEN
     UNDISCH_TAC ``abs (-(b - t) / r) <= &n:real`` THEN
     FULL_SIMP_TAC real_ss [abs, REAL_LE_RDIV_EQ, REAL_LE_LDIV_EQ] THEN
     RW_TAC std_ss [] THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
     FULL_SIMP_TAC real_ss [REAL_LE_RDIV_EQ, REAL_LE_LDIV_EQ] THEN
     RW_TAC std_ss [] THEN TRY (ASM_REAL_ARITH_TAC) THEN
     UNDISCH_TAC `` -((t - a) / r) <= &m:real`` THEN
     GEN_REWR_TAC LAND_CONV [GSYM REAL_LE_NEG] THEN
     ASM_SIMP_TAC std_ss [REAL_LE_RDIV_EQ, REAL_NEG_NEG] THEN DISCH_TAC THEN
     ASM_REAL_ARITH_TAC, ALL_TAC] THEN

    UNDISCH_TAC ``~(-(a - t) / r <= &n:real)`` THEN
    ONCE_REWRITE_TAC [MONO_NOT_EQ] THEN RW_TAC std_ss [] THEN
    UNDISCH_TAC ``abs (-(a - t) / r) <= &m:real`` THEN
    UNDISCH_TAC ``abs (-(b - t) / r) <= &n:real`` THEN
    FULL_SIMP_TAC real_ss [abs, REAL_LE_RDIV_EQ, REAL_LE_LDIV_EQ] THEN
    RW_TAC std_ss [] THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
    FULL_SIMP_TAC real_ss [REAL_LE_RDIV_EQ, REAL_LE_LDIV_EQ] THEN
    RW_TAC std_ss [] THEN TRY (ASM_REAL_ARITH_TAC) THENL
    [MATCH_MP_TAC REAL_LE_TRANS THEN Q.EXISTS_TAC `&m * r` THEN
     ASM_SIMP_TAC real_ss [REAL_LE_RMUL],
     MATCH_MP_TAC REAL_LE_TRANS THEN Q.EXISTS_TAC `&m * r` THEN
     ASM_SIMP_TAC real_ss [REAL_LE_RMUL],
     ALL_TAC] THEN
    UNDISCH_TAC `` -((t - b) / r) <= &n:real`` THEN
    GEN_REWR_TAC LAND_CONV [GSYM REAL_LE_NEG] THEN
    ASM_SIMP_TAC std_ss [REAL_LE_RDIV_EQ, REAL_NEG_NEG] THEN DISCH_TAC THEN
    UNDISCH_TAC `` -((t - a) / r) <= &m:real`` THEN
    GEN_REWR_TAC LAND_CONV [GSYM REAL_LE_NEG] THEN
    ASM_SIMP_TAC std_ss [REAL_LE_RDIV_EQ, REAL_NEG_NEG] THEN DISCH_TAC THEN
    ASM_REAL_ARITH_TAC] THEN
   ASM_SIMP_TAC std_ss [CONTENT_CLOSED_INTERVAL, real_div] THEN
   SIMP_TAC std_ss [GSYM REAL_SUB_RDISTRIB] THEN
   ONCE_REWRITE_TAC [REAL_ARITH ``a * (b * c) = b * (a * c:real)``] THEN
   ASM_SIMP_TAC real_ss [REAL_MUL_RINV] THEN REAL_ARITH_TAC);

val lebesgue_pos_integral_real_affine = store_thm ("lebesgue_pos_integral_real_affine",
  ``!f c t. c <> 0 /\ f IN measurable borel Borel ==>
     (pos_fn_integral lborel (\x. max 0 (f x)) =
      Normal (abs c) * pos_fn_integral lborel (\x. max 0 (f (t + c * x))))``,
  RW_TAC std_ss [] THEN
  Q_TAC SUFF_TAC `pos_fn_integral lborel (\x. max 0 (f x)) =
    pos_fn_integral (density
        (distr lborel (space borel,subsets borel,(\x. 0))
           (\x. t + c * x)) (\z. Normal (abs c))) (\x. max 0 (f x))` THENL
  [DISC_RW_KILL,
   Q_TAC SUFF_TAC `pos_fn_integral lborel (\x. max 0 (f x)) =
      pos_fn_integral (measure_of lborel) (\x. max 0 (f x))` THENL
   [DISC_RW_KILL,
    SIMP_TAC std_ss [pos_fn_integral_def] THEN AP_TERM_TAC THEN
    AP_TERM_TAC THEN ABS_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    ABS_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    SIMP_TAC std_ss [IN_psfis_eq] THEN AP_TERM_TAC THEN ABS_TAC THEN
    AP_TERM_TAC THEN ABS_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN
    Q_TAC SUFF_TAC `pos_simple_fn lborel g s a x =
       pos_simple_fn (measure_of lborel) g s a x` THENL
    [DISCH_TAC THEN ASM_SIMP_TAC std_ss [],
     SIMP_TAC std_ss [pos_simple_fn_def] THEN EQ_TAC THEN
     RW_TAC std_ss [measure_of, m_space_def, measurable_sets_def, measure_def, lborel] THENL
     [MATCH_MP_TAC sigma_sets_basic THEN METIS_TAC [],
      ASM_SET_TAC [POW_DEF],
      FULL_SIMP_TAC std_ss [GSYM space_borel] THEN
      `sigma_sets (space borel) (subsets borel) = subsets borel` by
      METIS_TAC [SPACE, sigma_algebra_borel, sigma_sets_eq] THEN
      METIS_TAC [], ALL_TAC] THEN
     ASM_SET_TAC [POW_DEF]] THEN
    MATCH_MP_TAC (METIS [] ``(a ==> (b = c)) ==> (a /\ b = a /\ c)``) THEN
    POP_ASSUM (ASSUME_TAC o ONCE_REWRITE_RULE [EQ_SYM_EQ]) THEN
    POP_ASSUM (fn th => REWRITE_TAC [th]) THEN DISCH_TAC THEN
    AP_TERM_TAC THEN SIMP_TAC std_ss [pos_simple_fn_integral_def] THEN
    FULL_SIMP_TAC std_ss [pos_simple_fn_def] THEN
    FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP EXTREAL_SUM_IMAGE_EQ) THEN
    CONJ_TAC THENL
    [ALL_TAC,
     RW_TAC std_ss [measure_of, measure_def, lborel] THEN
     FIRST_X_ASSUM (fn th => POP_ASSUM MP_TAC THEN ASSUME_TAC th) THEN
     ONCE_REWRITE_TAC [MONO_NOT_EQ] THEN RW_TAC std_ss [] THENL
     [MATCH_MP_TAC sigma_sets_basic THEN METIS_TAC [measurable_sets_def, lborel],
      ALL_TAC] THEN
     `sigma_sets (space borel) (subsets borel) = subsets borel` by
      METIS_TAC [SPACE, sigma_algebra_borel, sigma_sets_eq] THEN
     METIS_TAC [measure_space_lborel, GSYM lborel, space_borel]] THEN
    DISJ1_TAC THEN RW_TAC std_ss [] THENL
    [SIMP_TAC std_ss [lt_infty] THEN MATCH_MP_TAC lte_trans THEN
     Q.EXISTS_TAC `0` THEN CONJ_TAC THENL
     [METIS_TAC [lt_infty, num_not_infty, extreal_of_num_def], ALL_TAC] THEN
     MATCH_MP_TAC le_mul THEN ASM_SIMP_TAC std_ss [extreal_of_num_def, extreal_le_def] THEN
     SIMP_TAC std_ss [GSYM extreal_of_num_def] THEN ASSUME_TAC measure_space_lborel THEN
     `positive lborel` by METIS_TAC [measure_space_def] THEN
     METIS_TAC [positive_def], ALL_TAC] THEN
    SIMP_TAC std_ss [lt_infty] THEN MATCH_MP_TAC lte_trans THEN
    Q.EXISTS_TAC `0` THEN CONJ_TAC THENL
    [METIS_TAC [lt_infty, num_not_infty, extreal_of_num_def], ALL_TAC] THEN
    MATCH_MP_TAC le_mul THEN ASM_SIMP_TAC std_ss [extreal_of_num_def, extreal_le_def] THEN
    SIMP_TAC std_ss [GSYM extreal_of_num_def] THEN ASSUME_TAC measure_space_lborel THEN
    `positive lborel` by METIS_TAC [measure_space_def] THEN
    SIMP_TAC std_ss [measure_of, measure_def, lborel] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC std_ss [le_refl] THEN
    METIS_TAC [positive_def, lborel, measure_def]] THEN

   Q_TAC SUFF_TAC `pos_fn_integral (density
     (distr lborel (space borel,subsets borel,(\x. 0)) (\x. t + c * x))
     (\z. Normal (abs c))) (\x. max 0 (f x)) =
                   pos_fn_integral (measure_of (density
     (distr lborel (space borel,subsets borel,(\x. 0)) (\x. t + c * x))
     (\z. Normal (abs c)))) (\x. max 0 (f x))` THENL
   [METIS_TAC [lebesgue_real_affine], ALL_TAC] THEN

   SIMP_TAC std_ss [pos_fn_integral_def] THEN AP_TERM_TAC THEN
   AP_TERM_TAC THEN ABS_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
   ABS_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
   SIMP_TAC std_ss [IN_psfis_eq] THEN AP_TERM_TAC THEN ABS_TAC THEN
   AP_TERM_TAC THEN ABS_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN
   Q_TAC SUFF_TAC `pos_simple_fn (density
        (distr lborel (space borel,subsets borel,(\x. 0))
           (\x. t + c * x)) (\z. Normal (abs c))) g s a x =
      pos_simple_fn (measure_of (density
        (distr lborel (space borel,subsets borel,(\x. 0))
           (\x. t + c * x)) (\z. Normal (abs c)))) g s a x` THENL
   [DISCH_TAC THEN ASM_SIMP_TAC std_ss [],
    SIMP_TAC std_ss [pos_simple_fn_def] THEN EQ_TAC THEN
    RW_TAC std_ss [measure_of, m_space_def, measurable_sets_def, measure_def,
                   density, distr] THENL
    [MATCH_MP_TAC sigma_sets_basic THEN METIS_TAC [],
     ASM_SET_TAC [POW_DEF, space_borel],
     FULL_SIMP_TAC std_ss [GSYM space_borel] THEN
     `sigma_sets (space borel) (subsets borel) = subsets borel` by
     METIS_TAC [SPACE, sigma_algebra_borel, sigma_sets_eq] THEN
     METIS_TAC [], ALL_TAC] THEN
    ASM_SET_TAC [POW_DEF, space_borel]] THEN
   MATCH_MP_TAC (METIS [] ``(a ==> (b = c)) ==> (a /\ b = a /\ c)``) THEN
   POP_ASSUM (ASSUME_TAC o ONCE_REWRITE_RULE [EQ_SYM_EQ]) THEN
   POP_ASSUM (fn th => REWRITE_TAC [th]) THEN DISCH_TAC THEN
   AP_TERM_TAC THEN SIMP_TAC std_ss [pos_simple_fn_integral_def] THEN
   FULL_SIMP_TAC std_ss [pos_simple_fn_def] THEN
   FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP EXTREAL_SUM_IMAGE_EQ) THEN
   Q_TAC SUFF_TAC `measure_space (density
      (distr lborel (space borel,subsets borel,(\x. 0)) (\x. t + c * x))
      (\z. Normal (abs c)))` THENL
   [DISCH_TAC,
    MATCH_MP_TAC measure_space_density THEN CONJ_TAC THENL
    [ALL_TAC, MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST THEN
     Q.EXISTS_TAC `Normal (abs c)` THEN
     SIMP_TAC std_ss [m_space_def, measurable_sets_def, distr] THEN
     SIMP_TAC std_ss [SPACE, sigma_algebra_borel]] THEN
    MATCH_MP_TAC measure_space_distr THEN
    SIMP_TAC std_ss [measure_space_borel, measure_space_lborel] THEN
    SIMP_TAC std_ss [m_space_def, measurable_sets_def, SPACE] THEN
     SIMP_TAC std_ss [GSYM borel_measurable] THEN MATCH_MP_TAC borel_measurable_add THEN
     Q.EXISTS_TAC `(\x. t)` THEN Q.EXISTS_TAC `(\x. c * x)` THEN
     CONJ_TAC THENL [METIS_TAC [lborel, GSYM space_borel, m_space_def,
       measurable_sets_def, sigma_algebra_borel, SPACE], ALL_TAC] THEN
     CONJ_TAC THENL
     [MATCH_MP_TAC borel_measurable_const THEN
      METIS_TAC [lborel, GSYM space_borel, m_space_def,
       measurable_sets_def, sigma_algebra_borel, SPACE],
      ALL_TAC] THEN
     SIMP_TAC std_ss [] THEN MATCH_MP_TAC borel_measurable_cmul THEN
     Q.EXISTS_TAC `(\x. x)` THEN Q.EXISTS_TAC `c` THEN
     ASM_SIMP_TAC std_ss [] THEN
     CONJ_TAC THENL [METIS_TAC [lborel, GSYM space_borel, m_space_def,
       measurable_sets_def, sigma_algebra_borel, SPACE], ALL_TAC] THEN
     Q_TAC SUFF_TAC `(\x:real. x) = I` THENL
     [DISC_RW_KILL, SIMP_TAC std_ss [FUN_EQ_THM]] THEN
     SIMP_TAC std_ss [borel_measurable, m_space_def, measurable_sets_def, SPACE, lborel] THEN
     SIMP_TAC std_ss [GSYM space_borel, SPACE] THEN MATCH_MP_TAC MEASURABLE_I THEN
     SIMP_TAC std_ss [sigma_algebra_borel]] THEN
   CONJ_TAC THENL
   [ALL_TAC,
    RW_TAC std_ss [measure_of, measure_def, measurable_sets_def, m_space_def, density, distr] THEN
    FIRST_X_ASSUM (fn th => POP_ASSUM MP_TAC THEN ASSUME_TAC th) THEN
    ONCE_REWRITE_TAC [MONO_NOT_EQ] THEN RW_TAC std_ss [] THENL
    [MATCH_MP_TAC sigma_sets_basic THEN METIS_TAC [measurable_sets_def, lborel],
     ALL_TAC] THEN
    `sigma_sets (space borel) (subsets borel) = subsets borel` by
     METIS_TAC [SPACE, sigma_algebra_borel, sigma_sets_eq] THEN
    FULL_SIMP_TAC std_ss
     [density, distr, m_space_def, measurable_sets_def, measure_def]] THEN
    DISJ1_TAC THEN RW_TAC std_ss [] THENL
    [SIMP_TAC std_ss [lt_infty] THEN MATCH_MP_TAC lte_trans THEN
     Q.EXISTS_TAC `0` THEN CONJ_TAC THENL
     [METIS_TAC [lt_infty, num_not_infty, extreal_of_num_def], ALL_TAC] THEN
     MATCH_MP_TAC le_mul THEN ASM_SIMP_TAC std_ss [extreal_of_num_def, extreal_le_def] THEN
     SIMP_TAC std_ss [GSYM extreal_of_num_def] THEN
     METIS_TAC [positive_def, measure_space_def], ALL_TAC] THEN
    SIMP_TAC std_ss [lt_infty] THEN MATCH_MP_TAC lte_trans THEN
    Q.EXISTS_TAC `0` THEN CONJ_TAC THENL
    [METIS_TAC [lt_infty, num_not_infty, extreal_of_num_def], ALL_TAC] THEN
    MATCH_MP_TAC le_mul THEN ASM_SIMP_TAC std_ss [extreal_of_num_def, extreal_le_def] THEN
    SIMP_TAC std_ss [GSYM extreal_of_num_def] THEN
    SIMP_TAC std_ss [measure_of, measure_def, density, distr] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC std_ss [le_refl] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC std_ss [le_refl] THEN
    `positive (density
           (distr lborel (space borel,subsets borel,(\x. 0))
              (\x. t + c * x)) (\z. Normal (abs c)))` by
     METIS_TAC [measure_space_def] THEN
    POP_ASSUM MP_TAC THEN SIMP_TAC std_ss [positive_def] THEN STRIP_TAC THEN
    POP_ASSUM (MP_TAC o Q.SPEC `a (x':num)`) THEN
    FULL_SIMP_TAC std_ss [density, distr, m_space_def, measurable_sets_def, measure_def]] THEN
  Q_TAC SUFF_TAC `(\x. max 0 (f x)) = (\x. max 0 ((\x. max 0 (f x)) x))` THENL
  [DISC_RW_KILL,
   SIMP_TAC std_ss [le_max1, extreal_max_def, FUN_EQ_THM] THEN
   RW_TAC std_ss [] THEN FULL_SIMP_TAC std_ss []] THEN
  Q_TAC SUFF_TAC `pos_fn_integral
   (density
     (distr lborel (space borel,subsets borel,(\x. 0)) (\x. t + c * x))
     (\z. Normal (abs c))) (\x. max 0 ((\x. max 0 (f x)) x)) =
   pos_fn_integral (distr lborel (space borel,subsets borel,(\x. 0)) (\x. t + c * x))
    (\x. max 0 ((\z. Normal (abs c)) x * (\x. max 0 (f x)) x))` THENL
  [DISC_RW_KILL,
   MATCH_MP_TAC (REWRITE_RULE [GSYM density] pos_fn_integral_density') THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC measure_space_distr THEN
    SIMP_TAC std_ss [measure_space_lborel, measure_space_borel] THEN
    SIMP_TAC std_ss [m_space_def, measurable_sets_def, SPACE] THEN
    SIMP_TAC std_ss [GSYM borel_measurable] THEN MATCH_MP_TAC borel_measurable_add THEN
    Q.EXISTS_TAC `(\x. t)` THEN Q.EXISTS_TAC `(\x. c * x)` THEN
    CONJ_TAC THENL [METIS_TAC [lborel, GSYM space_borel, m_space_def,
      measurable_sets_def, sigma_algebra_borel, SPACE], ALL_TAC] THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC borel_measurable_const THEN
     METIS_TAC [lborel, GSYM space_borel, m_space_def,
      measurable_sets_def, sigma_algebra_borel, SPACE],
     ALL_TAC] THEN
    SIMP_TAC std_ss [] THEN MATCH_MP_TAC borel_measurable_cmul THEN
    Q.EXISTS_TAC `(\x. x)` THEN Q.EXISTS_TAC `c` THEN
    ASM_SIMP_TAC std_ss [] THEN
    CONJ_TAC THENL [METIS_TAC [lborel, GSYM space_borel, m_space_def,
      measurable_sets_def, sigma_algebra_borel, SPACE], ALL_TAC] THEN
    Q_TAC SUFF_TAC `(\x:real. x) = I` THENL
    [DISC_RW_KILL, SIMP_TAC std_ss [FUN_EQ_THM]] THEN
    SIMP_TAC std_ss [borel_measurable, m_space_def, measurable_sets_def, SPACE, lborel] THEN
    SIMP_TAC std_ss [GSYM space_borel, SPACE] THEN MATCH_MP_TAC MEASURABLE_I THEN
    SIMP_TAC std_ss [sigma_algebra_borel],
    ALL_TAC] THEN
   SIMP_TAC std_ss [m_space_def, measurable_sets_def, distr, le_max1] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST THEN Q.EXISTS_TAC `Normal (abs c)` THEN
    SIMP_TAC std_ss [SPACE, sigma_algebra_borel],
    ALL_TAC] THEN
   CONJ_TAC THENL
   [ALL_TAC,
    Q_TAC SUFF_TAC `(\x. max ((\x. 0) x) (f x)) IN
     measurable (space borel,subsets borel) Borel` THENL
    [SIMP_TAC std_ss [], ALL_TAC] THEN
    MATCH_MP_TAC IN_MEASURABLE_BOREL_MAX THEN
    ASM_SIMP_TAC std_ss [SPACE, sigma_algebra_borel] THEN
    MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST THEN METIS_TAC [sigma_algebra_borel]] THEN
   SIMP_TAC std_ss [AE, ae_filter, GSPECIFICATION] THEN
   SIMP_TAC std_ss [m_space_def, measurable_sets_def, measure_def,
                    null_sets, GSPECIFICATION] THEN
   Q.EXISTS_TAC `{}` THEN SIMP_TAC std_ss [OPEN_EMPTY, borel_open] THEN
   SIMP_TAC std_ss [PREIMAGE_EMPTY, INTER_EMPTY] THEN
   ASSUME_TAC measure_space_lborel THEN
   CONJ_TAC THENL [METIS_TAC [measure_space_def, positive_def], ALL_TAC] THEN
   SIMP_TAC std_ss [extreal_of_num_def, extreal_le_def, ABS_POS] THEN
   SIMP_TAC std_ss [GSPEC_F, SUBSET_REFL]] THEN

  SIMP_TAC std_ss [] THEN
  Q_TAC SUFF_TAC `pos_fn_integral
  (distr lborel (space borel,subsets borel,(\x. 0)) (\x. t + c * x))
  (\x. max 0 ((\x. Normal (abs c) * max 0 (f x)) x)) =
   pos_fn_integral lborel (\x. max 0 ((\x. Normal (abs c) * max 0 (f x))
                               ((\x. t + c * x) x)))` THENL
  [SIMP_TAC std_ss [] THEN DISC_RW_KILL,
   MATCH_MP_TAC pos_fn_integral_distr' THEN
   ASM_SIMP_TAC std_ss [measure_space_lborel, measure_space_borel] THEN
   SIMP_TAC std_ss [m_space_def, measurable_sets_def, lborel, distr, GSYM space_borel] THEN
   SIMP_TAC std_ss [SPACE, GSYM borel_measurable] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC borel_measurable_add THEN
    Q.EXISTS_TAC `(\x. t)` THEN Q.EXISTS_TAC `(\x. c * x)` THEN
    CONJ_TAC THENL [METIS_TAC [lborel, GSYM space_borel, m_space_def,
      measurable_sets_def, sigma_algebra_borel, SPACE], ALL_TAC] THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC borel_measurable_const THEN
     METIS_TAC [lborel, GSYM space_borel, m_space_def,
      measurable_sets_def, sigma_algebra_borel, SPACE],
     ALL_TAC] THEN
    SIMP_TAC std_ss [] THEN MATCH_MP_TAC borel_measurable_cmul THEN
    Q.EXISTS_TAC `(\x. x)` THEN Q.EXISTS_TAC `c` THEN
    ASM_SIMP_TAC std_ss [] THEN
    CONJ_TAC THENL [METIS_TAC [lborel, GSYM space_borel, m_space_def,
      measurable_sets_def, sigma_algebra_borel, SPACE], ALL_TAC] THEN
    Q_TAC SUFF_TAC `(\x:real. x) = I` THENL
    [DISC_RW_KILL, SIMP_TAC std_ss [FUN_EQ_THM]] THEN
    SIMP_TAC std_ss [borel_measurable, m_space_def, measurable_sets_def, SPACE, lborel] THEN
    SIMP_TAC std_ss [GSYM space_borel, SPACE] THEN MATCH_MP_TAC MEASURABLE_I THEN
    SIMP_TAC std_ss [sigma_algebra_borel],
    ALL_TAC] THEN
   CONJ_TAC THENL
   [ALL_TAC,
    GEN_TAC THEN MATCH_MP_TAC le_mul THEN
    SIMP_TAC std_ss [le_max1, extreal_of_num_def, extreal_le_def, ABS_POS]] THEN
   ONCE_REWRITE_TAC [METIS [m_space_def, measurable_sets_def, SPACE]
    ``borel = (m_space (space borel, subsets borel, (\x. 0)),
       measurable_sets (space borel, subsets borel, (\x. 0)))``] THEN
   MATCH_MP_TAC IN_MEASURABLE_BOREL_TIMES THEN Q.EXISTS_TAC `(\x. Normal (abs c))` THEN
   Q.EXISTS_TAC `(\x. max ((\x. 0) x) (f x))` THEN
   CONJ_TAC THENL [SIMP_TAC std_ss [measure_space_borel], ALL_TAC] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST THEN
    METIS_TAC [m_space_def, measurable_sets_def, SPACE, sigma_algebra_borel],
    ALL_TAC] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC IN_MEASURABLE_BOREL_MAX THEN
    ASM_SIMP_TAC std_ss [m_space_def, measurable_sets_def, SPACE, sigma_algebra_borel] THEN
    ONCE_REWRITE_TAC [METIS [m_space_def, measurable_sets_def, SPACE]
    ``borel = (m_space (space borel, subsets borel, (\x. 0)),
       measurable_sets (space borel, subsets borel, (\x. 0)))``] THEN
    MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST THEN
    METIS_TAC [m_space_def, measurable_sets_def, SPACE, sigma_algebra_borel],
    ALL_TAC] THEN
   SIMP_TAC std_ss []] THEN

  Q_TAC SUFF_TAC `(\x. max 0 (f (t + c * x))) = (\x. max 0 ((\x. max 0 (f (t + c * x))) x))` THENL
  [DISC_RW_KILL,
   SIMP_TAC std_ss [le_max1, extreal_max_def, FUN_EQ_THM] THEN
   RW_TAC std_ss [] THEN FULL_SIMP_TAC std_ss []] THEN
  SIMP_TAC std_ss [] THEN

  Q_TAC SUFF_TAC `pos_fn_integral lborel
   (\x. max 0 (Normal (abs c) * ((\x. max 0 (f (t + c * x))) x))) =
   Normal (abs c) *
   pos_fn_integral lborel (\x. max 0 ((\x. max 0 (f (t + c * x))) x))` THENL
  [SIMP_TAC std_ss [], ALL_TAC] THEN
  MATCH_MP_TAC pos_fn_integral_cmult THEN
  SIMP_TAC std_ss [measure_space_lborel] THEN CONJ_TAC THENL
  [METIS_TAC [extreal_of_num_def, extreal_le_def, ABS_POS],
   ALL_TAC] THEN
  Q_TAC SUFF_TAC `(\x. max ((\x. 0) x) ((\x. f (t + c * x)) x)) IN
          measurable (m_space lborel,measurable_sets lborel) Borel` THENL
  [SIMP_TAC std_ss [], ALL_TAC] THEN
  MATCH_MP_TAC IN_MEASURABLE_BOREL_MAX THEN
  ASSUME_TAC measure_space_lborel THEN
  CONJ_TAC THENL [METIS_TAC [measure_space_def], ALL_TAC] THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST THEN
   METIS_TAC [measure_space_def],
   ALL_TAC] THEN
  Q_TAC SUFF_TAC `(\x. f (t + c * x)) = f o (\x. t + c * x)` THENL
  [DISC_RW_KILL, SIMP_TAC std_ss [o_DEF]] THEN
  MATCH_MP_TAC MEASURABLE_COMP THEN Q.EXISTS_TAC `borel` THEN
  ASM_SIMP_TAC std_ss [GSYM borel_measurable] THEN
  MATCH_MP_TAC borel_measurable_add THEN
  Q.EXISTS_TAC `(\x. t)` THEN Q.EXISTS_TAC `(\x. c * x)` THEN
  ASSUME_TAC measure_space_lborel THEN
  CONJ_TAC THENL [METIS_TAC [measure_space_def], ALL_TAC] THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC borel_measurable_const THEN
   METIS_TAC [measure_space_def],
   ALL_TAC] THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC borel_measurable_cmul THEN Q.EXISTS_TAC `(\x. x)` THEN
   Q.EXISTS_TAC `c` THEN SIMP_TAC std_ss [] THEN
   CONJ_TAC THENL [METIS_TAC [measure_space_def], ALL_TAC] THEN
   Q_TAC SUFF_TAC `(\x:real. x) = I` THENL
   [DISC_RW_KILL, SIMP_TAC std_ss [FUN_EQ_THM]] THEN
   SIMP_TAC std_ss [borel_measurable, m_space_def, measurable_sets_def, SPACE, lborel] THEN
   SIMP_TAC std_ss [GSYM space_borel, SPACE] THEN
   MATCH_MP_TAC MEASURABLE_I THEN SIMP_TAC std_ss [sigma_algebra_borel],
   ALL_TAC] THEN
  SIMP_TAC std_ss []);

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* ------------------------------------------------------------------------- *)

val null_sets_density_iff = store_thm ("null_sets_density_iff",
  ``!f A M. measure_space M /\ (!x. 0 <= f x) /\
     f IN measurable (m_space M, measurable_sets M) Borel ==>
    (A IN measurable_sets M /\
     (measure ((m_space M,measurable_sets M,
        (\A.
           if A IN measurable_sets M then
             pos_fn_integral M (\x. f x * indicator_fn A x)
           else 0))) A = 0) =
     (A IN measurable_sets M /\ AE M {x | x IN A ==> f x <= 0}))``,
  RW_TAC std_ss [] THEN
  MATCH_MP_TAC (METIS [] ``(a ==> (b = c)) ==> (a /\ b = a /\ c)``) THEN
  DISCH_TAC THEN
  Q_TAC SUFF_TAC`
   (pos_fn_integral M (\x. f x * indicator_fn A x) =
    pos_fn_integral M (\x. max 0 (f x) * indicator_fn A x))` THENL
  [DISCH_TAC, ASM_SIMP_TAC std_ss [extreal_max_def]] THEN
  Q_TAC SUFF_TAC `(pos_fn_integral M (\x. f x * indicator_fn A x) = 0) =
    (measure M {x | x IN m_space M /\ (max 0 (f x) * indicator_fn A x <> 0)} = 0)` THENL
  [DISCH_TAC,
   ONCE_REWRITE_TAC [METIS [] ``max 0 (f x) * indicator_fn A x =
                           (\x. max 0 (f x) * indicator_fn A x) x``] THEN
   ONCE_ASM_REWRITE_TAC [] THEN MATCH_MP_TAC positive_integral_0_iff THEN
   ASM_SIMP_TAC std_ss [] THEN REPEAT STRIP_TAC THENL
   [Q_TAC SUFF_TAC `!x. max 0 (f x) = f x` THENL
    [DISC_RW_KILL, METIS_TAC [extreal_max_def]] THEN
    MATCH_MP_TAC IN_MEASURABLE_BOREL_MUL_INDICATOR THEN
    METIS_TAC [measure_space_def, subsets_def],
    ALL_TAC,
    MATCH_MP_TAC le_mul THEN CONJ_TAC THENL
    [METIS_TAC [extreal_max_def, le_refl], ALL_TAC] THEN
    SIMP_TAC std_ss [indicator_fn_def] THEN COND_CASES_TAC THEN
    SIMP_TAC real_ss [le_refl, extreal_of_num_def, extreal_le_def]] THEN
   SIMP_TAC std_ss [AE, ae_filter, GSPECIFICATION] THEN Q.EXISTS_TAC `{}` THEN
   Q_TAC SUFF_TAC `!x. 0 <= max 0 (f x) * indicator_fn A x` THENL
   [DISCH_TAC THEN ASM_SIMP_TAC std_ss [GSPEC_F, SUBSET_REFL] THEN
    SIMP_TAC std_ss [null_sets, GSPECIFICATION] THEN
    METIS_TAC [measure_space_def, positive_def, sigma_algebra_iff2],
    ALL_TAC] THEN
   GEN_TAC THEN MATCH_MP_TAC le_mul THEN SIMP_TAC std_ss [le_max1, indicator_fn_def] THEN
   COND_CASES_TAC THEN SIMP_TAC real_ss [le_refl, extreal_of_num_def, extreal_le_def]] THEN
  ASM_SIMP_TAC std_ss [measure_def] THEN
  Q_TAC SUFF_TAC `!x. max 0 (f x) = f x` THENL
   [DISC_RW_KILL, METIS_TAC [extreal_max_def]] THEN
  ASM_REWRITE_TAC [] THEN ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
  MATCH_MP_TAC (REWRITE_RULE [AND_IMP_INTRO] AE_iff_measurable) THEN
  ASM_SIMP_TAC std_ss [GSPECIFICATION] THEN CONJ_TAC THENL
  [ALL_TAC,
   SIMP_TAC std_ss [EXTENSION, GSPECIFICATION] THEN GEN_TAC THEN
   EQ_TAC THEN RW_TAC std_ss [] THENL
   [ASM_SIMP_TAC std_ss [indicator_fn_def, extreal_max_def, mul_rone] THEN
    ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN MATCH_MP_TAC lt_imp_ne THEN
    ASM_SIMP_TAC std_ss [extreal_lt_def],
    POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC [MONO_NOT_EQ] THEN
    SIMP_TAC std_ss [indicator_fn_def, mul_rzero],
    ALL_TAC] THEN
   POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC [MONO_NOT_EQ] THEN
   SIMP_TAC std_ss [] THEN DISCH_TAC THEN
   `f x = 0` by METIS_TAC [le_antisym] THEN
   ASM_SIMP_TAC std_ss [max_refl, mul_lzero]] THEN
   ONCE_REWRITE_TAC [SET_RULE
    ``!x. (max 0 (f x) * indicator_fn A x <> 0) =
       x IN {x | max 0 (f x) * indicator_fn A x <> 0}``] THEN
   REWRITE_TAC [GSYM INTER_DEF] THEN
   UNDISCH_TAC ``f IN measurable (m_space M,measurable_sets M) Borel`` THEN
   SIMP_TAC std_ss [IN_MEASURABLE, SIGMA_ALGEBRA_BOREL, space_def, IN_FUNSET] THEN
   REPEAT STRIP_TAC THEN
   Q_TAC SUFF_TAC `{x | max 0 (f x) * indicator_fn A x <> 0} = A DIFF {x | f x = 0}` THENL
   [ALL_TAC,
    SIMP_TAC std_ss [EXTENSION, GSPECIFICATION] THEN GEN_TAC THEN
    EQ_TAC THENL
    [ONCE_REWRITE_TAC [MONO_NOT_EQ] THEN
     SIMP_TAC std_ss [IN_DIFF, GSPECIFICATION] THEN RW_TAC std_ss [] THEN
     ASM_SIMP_TAC std_ss [indicator_fn_def, mul_rzero, max_refl, mul_lzero],
     ALL_TAC] THEN
    SIMP_TAC std_ss [IN_DIFF, GSPECIFICATION] THEN STRIP_TAC THEN
    ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN MATCH_MP_TAC lt_imp_ne THEN
    `0 < f x` by METIS_TAC [le_lt] THEN MATCH_MP_TAC lt_mul THEN
    ASM_SIMP_TAC std_ss [indicator_fn_def, mul_rone, extreal_max_def] THEN
    SIMP_TAC real_ss [extreal_of_num_def, extreal_lt_eq]] THEN
   DISC_RW_KILL THEN
   ONCE_REWRITE_TAC [SET_RULE ``a INTER (b DIFF c) = (a INTER b) DIFF (a INTER c)``] THEN
   ONCE_REWRITE_TAC [METIS [subsets_def] ``measurable_sets M =
     subsets (m_space M, measurable_sets M)``] THEN
   MATCH_MP_TAC ALGEBRA_DIFF THEN REPEAT CONJ_TAC THENL
   [METIS_TAC [measure_space_def, sigma_algebra_def],
    MATCH_MP_TAC ALGEBRA_INTER THEN REPEAT CONJ_TAC THENL
    [METIS_TAC [measure_space_def, sigma_algebra_def],
     METIS_TAC [subsets_def, MEASURE_SPACE_MSPACE_MEASURABLE],
     ALL_TAC] THEN
    ASM_SIMP_TAC std_ss [subsets_def],
    ALL_TAC] THEN
   ONCE_REWRITE_TAC [INTER_COMM] THEN
   ONCE_REWRITE_TAC [SET_RULE ``{x | f x = 0} = {x | f x IN {s | s = 0}}``] THEN
   REWRITE_TAC [GSYM PREIMAGE_def] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
   ONCE_REWRITE_TAC [SET_RULE ``{s | s = 0} = {0}``] THEN
   SIMP_TAC std_ss [BOREL_MEASURABLE_SETS_SING, extreal_of_num_def]);

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* ------------------------------------------------------------------------- *)

val diff_measure = new_definition ("diff_measure",
  ``diff_measure M N =
     (m_space M, measurable_sets M, (\A. measure M A - measure N A))``);

val space_diff_measure = store_thm ("space_diff_measure",
  ``!M N. m_space (diff_measure M N) = m_space M``,
  SIMP_TAC std_ss [diff_measure, m_space_def]);

val sets_diff_measure = store_thm ("sets_diff_measure",
  ``!M N. measurable_sets (diff_measure M N) = measurable_sets M``,
  SIMP_TAC std_ss [diff_measure, measurable_sets_def]);

val measure_diff_measure = store_thm ("measure_diff_measure",
  ``!M N. measure (diff_measure M N) = (\A. measure M A - measure N A)``,
  SIMP_TAC std_ss [diff_measure, measure_def]);

val ereal_0_gt_inverse = store_thm ("ereal_0_gt_inverse",
  ``!x. 0 < inv x = (x <> PosInf) /\ 0 <= x``,
  GEN_TAC THEN EQ_TAC THEN RW_TAC std_ss [] THENL
  [POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC [MONO_NOT_EQ] THEN
   SIMP_TAC std_ss [extreal_inv_def, extreal_not_lt, extreal_of_num_def, le_refl],
   POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC [MONO_NOT_EQ] THEN
   ASM_CASES_TAC ``x = NegInf`` THENL
   [ASM_SIMP_TAC std_ss [extreal_inv_def, le_refl, extreal_of_num_def,
     extreal_not_lt], ALL_TAC] THEN
   RW_TAC std_ss [GSYM extreal_lt_def, extreal_not_lt] THEN
   `x <> PosInf` by METIS_TAC [lt_trans, num_not_infty, GSYM lt_infty] THEN
   `x <> 0` by METIS_TAC [lt_imp_ne] THEN
   `x = Normal (real x)` by METIS_TAC [normal_real] THEN
   ONCE_ASM_REWRITE_TAC [] THEN POP_ASSUM K_TAC THEN
   ASM_SIMP_TAC std_ss [extreal_inv_def] THEN
   `?r. x = Normal r` by METIS_TAC [extreal_cases] THEN
   ASM_REWRITE_TAC [real_normal] THEN COND_CASES_TAC THENL
   [FULL_SIMP_TAC std_ss [extreal_of_num_def], ALL_TAC] THEN
   SIMP_TAC std_ss [extreal_of_num_def, extreal_le_def] THEN
   CCONTR_TAC THEN FULL_SIMP_TAC std_ss [REAL_NOT_LE, REAL_LT_INV_EQ] THEN
   POP_ASSUM MP_TAC THEN ASM_SIMP_TAC std_ss [REAL_NOT_LT, REAL_LE_LT] THEN
   ASM_SIMP_TAC std_ss [GSYM extreal_lt_eq, GSYM extreal_of_num_def],
   ALL_TAC] THEN
 `x <> NegInf` by METIS_TAC [lte_trans, lt_infty, num_not_infty] THEN
 `x = Normal (real x)` by METIS_TAC [normal_real] THEN
 ONCE_ASM_REWRITE_TAC [] THEN SIMP_TAC std_ss [extreal_inv_def] THEN
 POP_ASSUM K_TAC THEN `?r. x = Normal r` by METIS_TAC [extreal_cases] THEN
 ASM_SIMP_TAC std_ss [real_normal] THEN COND_CASES_TAC THENL
 [SIMP_TAC std_ss [GSYM lt_infty, num_not_infty], ALL_TAC] THEN
 SIMP_TAC std_ss [extreal_of_num_def, extreal_lt_eq] THEN
 FULL_SIMP_TAC std_ss [extreal_of_num_def, extreal_le_def] THEN
 FULL_SIMP_TAC std_ss [REAL_LE_LT, REAL_LT_INV_EQ]);

val normal_inv_eq = store_thm ("normal_inv_eq",
  ``!x. x <> 0 ==> (Normal (inv x) = inv (Normal x))``,
  METIS_TAC [extreal_inv_def]);

val suminf_half_series_ereal = store_thm ("suminf_half_series_ereal",
  ``suminf (\i. (1 / 2) pow SUC i) = 1:extreal``,
  GEN_REWR_TAC RAND_CONV [extreal_of_num_def] THEN
  SIMP_TAC std_ss [ext_suminf_def] THEN
  Q_TAC SUFF_TAC `!i. (1 / 2) pow SUC i <> NegInf /\ (1 / 2) pow SUC i <> PosInf` THENL
  [DISCH_TAC,
   MATCH_MP_TAC pow_not_infty THEN SIMP_TAC std_ss [extreal_of_num_def] THEN
   SIMP_TAC real_ss [extreal_div_eq, lt_infty]] THEN
  `(\i. (1 / 2) pow SUC i) = (\i. Normal (real ((1 / 2) pow SUC i)))`
    by METIS_TAC [normal_real] THEN
  ASM_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_NORMAL, FINITE_COUNT] THEN
  ONCE_REWRITE_TAC [METIS [] ``(SIGMA (\i. real ((1 / 2) pow SUC i)) (count n)) =
                            (\n. SIGMA (\i. real ((1 / 2) pow SUC i)) (count n)) n``] THEN
  KNOW_TAC ``mono_increasing (\n. SIGMA (\i. real ((1 / 2) pow SUC i)) (count n))`` THENL
  [ALL_TAC,
   RW_TAC std_ss [GSYM sup_seq] THEN SIMP_TAC std_ss [GSYM REAL_SUM_IMAGE_EQ_sum] THEN
   SIMP_TAC std_ss [GSYM seqTheory.sums, ADD1] THEN
   Q_TAC SUFF_TAC `!i. real ((1 / 2) pow (i + 1)) = ((1 / 2:real) pow (i + 1))` THENL
   [RW_TAC std_ss [],
    GEN_TAC THEN SIMP_TAC std_ss [GSYM ADD1, extreal_of_num_def] THEN
    SIMP_TAC real_ss [extreal_div_eq, extreal_pow_def, real_normal]] THEN
   SIMP_TAC std_ss [POW_HALF_SER]] THEN
  SIMP_TAC std_ss [mono_increasing_def] THEN RW_TAC std_ss [] THEN
  MATCH_MP_TAC REAL_SUM_IMAGE_MONO_SET THEN SIMP_TAC std_ss [FINITE_COUNT] THEN
  CONJ_TAC THENL
  [ASM_SIMP_TAC real_ss [SUBSET_DEF, count_def, GSPECIFICATION], ALL_TAC] THEN
  Q_TAC SUFF_TAC `!i. real ((1 / 2) pow (i + 1)) = ((1 / 2:real) pow (i + 1))` THENL
  [RW_TAC std_ss [ADD1],
   GEN_TAC THEN SIMP_TAC std_ss [GSYM ADD1, extreal_of_num_def] THEN
   SIMP_TAC real_ss [extreal_div_eq, extreal_pow_def, real_normal]] THEN
  MATCH_MP_TAC POW_POS THEN SIMP_TAC std_ss [REAL_HALF_BETWEEN]);

val suminf_cmult_indicator = store_thm ("suminf_cmult_indicator",
  ``!A f x i. disjoint_family A /\ x IN A i /\ (!i. 0 <= f i) ==>
              (suminf (\n. f n * indicator_fn (A n) x) = f i)``,
  RW_TAC std_ss [disjoint_family, disjoint_family_on, IN_UNIV] THEN
  Q_TAC SUFF_TAC `!n. f n * indicator_fn (A n) x = if n = i then f n else 0` THENL
  [DISCH_TAC,
   RW_TAC std_ss [indicator_fn_def, mul_rone, mul_rzero] THEN
   ASM_SET_TAC []] THEN
  Q_TAC SUFF_TAC `f i = SIGMA (\i. f i * indicator_fn (A i) x) (count (SUC i))` THENL
  [DISCH_THEN (fn th => ONCE_REWRITE_TAC [th]) THEN MATCH_MP_TAC ext_suminf_sum THEN
   RW_TAC std_ss [le_refl] THEN POP_ASSUM MP_TAC THEN ASM_SIMP_TAC arith_ss [ADD1],
   ASM_SIMP_TAC std_ss []] THEN
  `count (SUC i) <> {}` by (SIMP_TAC std_ss [GSYM MEMBER_NOT_EMPTY] THEN
     Q.EXISTS_TAC `i` THEN SIMP_TAC arith_ss [GSPECIFICATION, count_def]) THEN
  Q_TAC SUFF_TAC `count (SUC i) = count i UNION {i}` THENL
  [RW_TAC std_ss [],
   SIMP_TAC arith_ss [count_def, EXTENSION, IN_UNION, GSPECIFICATION, IN_SING]] THEN
  Q_TAC SUFF_TAC `SIGMA (\i'. if i' = i then f i else 0) (count i UNION {i}) =
                  SIGMA (\i'. if i' = i then f i else 0) (count i) +
                  SIGMA (\i'. if i' = i then f i else 0) ({i})` THENL
  [RW_TAC std_ss [],
   ABBREV_TAC ``g = (\i'. if i' = i then (f:num->extreal) i else 0)`` THEN
   Q_TAC SUFF_TAC `(!x. x IN (count i UNION {i}) ==> g x <> NegInf) \/
                   (!x. x IN (count i UNION {i}) ==> g x <> PosInf)` THENL
   [Q.SPEC_TAC (`g`,`g`) THEN MATCH_MP_TAC EXTREAL_SUM_IMAGE_DISJOINT_UNION THEN
    SIMP_TAC std_ss [FINITE_COUNT, FINITE_SING, DISJOINT_DEF] THEN
    SIMP_TAC std_ss [EXTENSION, IN_INTER, IN_SING, NOT_IN_EMPTY, count_def] THEN
    SIMP_TAC arith_ss [GSPECIFICATION],
    DISJ1_TAC] THEN
   EXPAND_TAC "g" THEN POP_ASSUM K_TAC THEN RW_TAC std_ss [lt_infty] THENL
   [ALL_TAC, METIS_TAC [lt_infty, num_not_infty]] THEN
   MATCH_MP_TAC lte_trans THEN Q.EXISTS_TAC `0` THEN ASM_REWRITE_TAC [] THEN
   METIS_TAC [lt_infty, num_not_infty]] THEN
  SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_SING] THEN
  Q_TAC SUFF_TAC `SIGMA (\i'. if i' = i then f i else 0) (count i) = 0` THENL
  [SIMP_TAC std_ss [add_lzero],
   MATCH_MP_TAC EXTREAL_SUM_IMAGE_0] THEN
  RW_TAC std_ss [FINITE_COUNT] THEN POP_ASSUM MP_TAC THEN
  ONCE_REWRITE_TAC [MONO_NOT_EQ] THEN RW_TAC std_ss [] THEN
  SIMP_TAC arith_ss [count_def, GSPECIFICATION]);

val Ex_finite_integrable_function = store_thm ("Ex_finite_integrable_function",
  ``!m. measure_space m /\ sigma_finite_measure m ==>
        ?h. h IN measurable (m_space m, measurable_sets m) Borel /\
          (pos_fn_integral m h <> PosInf) /\
          (!x. x IN m_space m ==> 0 < h x /\ h x < PosInf) /\
          (!x. 0 <= h x)``,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM (ASSUME_TAC o MATCH_MP sigma_finite_disjoint) THEN
  FULL_SIMP_TAC std_ss [] THEN ABBREV_TAC ``B = (\i. 2 pow (SUC i) * measure m (A i))`` THEN
  KNOW_TAC ``!i:num. ?x. 0 < x /\ x < inv (B i)`` THENL
  [EXPAND_TAC "B" THEN GEN_TAC THEN
   Q_TAC SUFF_TAC `0 < inv (2 pow SUC i * measure m (A i))` THENL
   [DISCH_THEN (MP_TAC o MATCH_MP Q_DENSE_IN_R) THEN METIS_TAC [],
    ALL_TAC] THEN
   REWRITE_TAC [ereal_0_gt_inverse] THEN
   `(2 pow SUC i <> NegInf) /\ (2 pow SUC i <> PosInf)`
    by METIS_TAC [pow_not_infty, num_not_infty] THEN
   KNOW_TAC ``measure m ((A:num->'a->bool) i) <> NegInf`` THENL
   [FULL_SIMP_TAC std_ss [measure_space_def, positive_def, lt_infty] THEN
    MATCH_MP_TAC lte_trans THEN Q.EXISTS_TAC `0` THEN
    SIMP_TAC std_ss [num_not_infty,  GSYM lt_infty] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SET_TAC [],
    DISCH_TAC] THEN CONJ_TAC THENL
   [`?r. measure m (A i) = Normal r` by METIS_TAC [extreal_cases] THEN
    ASM_REWRITE_TAC [] THEN KNOW_TAC ``0:real <= r`` THENL
    [REWRITE_TAC [GSYM extreal_le_def] THEN
     FIRST_X_ASSUM (ASSUME_TAC o ONCE_REWRITE_RULE [EQ_SYM_EQ]) THEN
     ASM_SIMP_TAC std_ss [GSYM extreal_of_num_def] THEN
     FULL_SIMP_TAC std_ss [measure_space_def, positive_def] THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SET_TAC [], DISCH_TAC] THEN
    ONCE_REWRITE_TAC [mul_comm] THEN METIS_TAC [mul_not_infty],
    ALL_TAC] THEN
   `2 pow SUC i = Normal (real (2 pow SUC i))` by METIS_TAC [normal_real] THEN
   `measure m (A i) = Normal (real (measure m (A i)))` by METIS_TAC [normal_real] THEN
   MATCH_MP_TAC le_mul THEN CONJ_TAC THENL
   [ALL_TAC,
   FULL_SIMP_TAC std_ss [measure_space_def, positive_def] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SET_TAC []] THEN
   MATCH_MP_TAC pow_pos_le THEN
   SIMP_TAC real_ss [extreal_le_def, extreal_of_num_def],
   DISCH_TAC] THEN
  Q_TAC SUFF_TAC `?f. !x. 0 < f x /\ f x < inv (2 pow SUC x * measure m (A x))` THENL
  [STRIP_TAC, METIS_TAC []] THEN
  Q_TAC SUFF_TAC `!x. 0 <= f x` THENL
  [DISCH_TAC, ASM_SIMP_TAC std_ss [le_lt]] THEN
  ABBREV_TAC ``h = (\x. suminf (\i. f i * indicator_fn (A i) x))`` THEN
  Q_TAC SUFF_TAC `!i. A i IN measurable_sets m` THENL
  [DISCH_TAC, ASM_SET_TAC []] THEN
  Q_TAC SUFF_TAC `pos_fn_integral m h = suminf (\i. f i * measure m (A i))` THENL
  [DISCH_TAC,
   EXPAND_TAC "h" THEN
   Q_TAC SUFF_TAC `pos_fn_integral m (\x. suminf (\i. (\i x. f i * indicator_fn (A i) x) i x)) =
                       suminf (\i. pos_fn_integral m ((\i x. f i * indicator_fn (A i) x) i))` THENL
   [ALL_TAC,
    MATCH_MP_TAC pos_fn_integral_suminf THEN RW_TAC std_ss [] THENL
    [MATCH_MP_TAC le_mul THEN ASM_SIMP_TAC std_ss [indicator_fn_def] THEN
     COND_CASES_TAC THEN SIMP_TAC std_ss [le_refl] THEN
     SIMP_TAC real_ss [extreal_le_def, extreal_of_num_def], ALL_TAC] THEN
    ONCE_REWRITE_TAC [METIS [] ``(\x. f i * indicator_fn (A i) x) =
                         (\x. (\x. f i) x * indicator_fn (A i) x)``] THEN
    MATCH_MP_TAC IN_MEASURABLE_BOREL_MUL_INDICATOR THEN
    FULL_SIMP_TAC std_ss [measure_space_def, subsets_def] THEN
    MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST THEN Q.EXISTS_TAC `f i` THEN
    ASM_SIMP_TAC std_ss []] THEN
   RW_TAC std_ss [] THEN POP_ASSUM K_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN
   Q_TAC SUFF_TAC `(f i <> NegInf) /\ (f i <> PosInf)` THENL
   [STRIP_TAC THEN `f i = Normal (real (f i))` by METIS_TAC [GSYM normal_real] THEN
    ONCE_ASM_REWRITE_TAC [] THEN MATCH_MP_TAC pos_fn_integral_cmul_indicator THEN
    POP_ASSUM K_TAC THEN ASM_SIMP_TAC std_ss [] THEN
    SIMP_TAC std_ss [GSYM extreal_le_def, GSYM extreal_of_num_def] THEN
    ASM_SIMP_TAC std_ss [normal_real], ALL_TAC] THEN
   CONJ_TAC THENL
   [SIMP_TAC std_ss [lt_infty] THEN MATCH_MP_TAC lte_trans THEN
    Q.EXISTS_TAC `0` THEN ASM_SIMP_TAC std_ss [num_not_infty, GSYM lt_infty],
    ALL_TAC] THEN SIMP_TAC std_ss [lt_infty] THEN
   ASM_CASES_TAC ``measure m ((A:num->'a->bool) i) = 0`` THENL
   [POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
    POP_ASSUM (MP_TAC o Q.SPEC `i`) THEN
    RW_TAC std_ss [] THEN FULL_SIMP_TAC std_ss [mul_rzero] THEN
    UNDISCH_TAC ``(f:num->extreal) i < inv 0`` THEN
    SIMP_TAC std_ss [extreal_of_num_def, extreal_inv_def],
    ALL_TAC] THEN
   MATCH_MP_TAC lt_trans THEN
   Q.EXISTS_TAC `inv (2 pow SUC i * measure m (A i))` THEN
   ASM_SIMP_TAC std_ss [] THEN
   `(2 pow SUC i <> NegInf) /\ (2 pow SUC i <> PosInf)`
     by METIS_TAC [pow_not_infty, num_not_infty] THEN
   KNOW_TAC ``measure m ((A:num->'a->bool) i) <> NegInf`` THENL
   [FULL_SIMP_TAC std_ss [measure_space_def, positive_def, lt_infty] THEN
    MATCH_MP_TAC lte_trans THEN Q.EXISTS_TAC `0` THEN
    SIMP_TAC std_ss [num_not_infty,  GSYM lt_infty] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SET_TAC [],
    DISCH_TAC] THEN
   `2 pow SUC i = Normal (real (2 pow SUC i))` by METIS_TAC [normal_real] THEN
   `measure m (A i) = Normal (real (measure m (A i)))` by METIS_TAC [normal_real] THEN
   ONCE_ASM_REWRITE_TAC [] THEN SIMP_TAC std_ss [extreal_mul_def] THEN
   SIMP_TAC std_ss [extreal_inv_def] THEN
   Q_TAC SUFF_TAC `real (2 pow SUC i) * real (measure m (A i)) <> 0` THENL
   [RW_TAC std_ss [lt_infty], ALL_TAC] THEN
   ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN MATCH_MP_TAC REAL_LT_IMP_NE THEN
   MATCH_MP_TAC REAL_LT_MUL THEN ONCE_REWRITE_TAC [GSYM extreal_lt_eq] THEN
   POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
   RW_TAC std_ss [GSYM extreal_of_num_def] THENL
   [ALL_TAC,
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP MEASURE_SPACE_POSITIVE) THEN
    FULL_SIMP_TAC std_ss [positive_def] THEN
    POP_ASSUM (MP_TAC o Q.SPEC `A (i:num)`) THEN ASM_SIMP_TAC std_ss [] THEN
    FULL_SIMP_TAC std_ss [le_lt]] THEN
   MATCH_MP_TAC pow_pos_lt THEN SIMP_TAC real_ss [extreal_lt_eq, extreal_of_num_def]] THEN
  Q_TAC SUFF_TAC `suminf (\i. f i * measure m (A i)) <= suminf (\i. (1 / 2) pow SUC i)` THENL
  [DISCH_TAC,
   MATCH_MP_TAC ext_suminf_mono THEN RW_TAC std_ss [lt_infty] THENL
   [MATCH_MP_TAC lte_trans THEN Q.EXISTS_TAC `Normal 0` THEN
    SIMP_TAC std_ss [lt_infty] THEN REWRITE_TAC [GSYM extreal_of_num_def] THEN
    MATCH_MP_TAC le_mul THEN FULL_SIMP_TAC std_ss [measure_space_def, positive_def],
    ALL_TAC] THEN
   POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
   POP_ASSUM (MP_TAC o Q.SPEC `n`) THEN RW_TAC std_ss [] THEN
   MATCH_MP_TAC le_trans THEN
   Q.EXISTS_TAC `inv (2 pow SUC n * measure m (A n)) * measure m (A n)` THEN
   CONJ_TAC THENL
   [ASM_CASES_TAC ``measure m ((A:num->'a->bool) n) = 0`` THENL
    [ASM_REWRITE_TAC [] THEN SIMP_TAC std_ss [mul_rzero, le_lt], ALL_TAC] THEN
    MATCH_MP_TAC le_rmul_imp THEN FULL_SIMP_TAC std_ss [measure_space_def, le_lt] THEN
    FULL_SIMP_TAC std_ss [positive_def, le_lt] THEN METIS_TAC [], ALL_TAC] THEN
   `(2 pow SUC n <> NegInf) /\ (2 pow SUC n <> PosInf)`
      by METIS_TAC [pow_not_infty, num_not_infty] THEN
   KNOW_TAC ``measure m ((A:num->'a->bool) n) <> NegInf`` THENL
   [FULL_SIMP_TAC std_ss [measure_space_def, positive_def, lt_infty] THEN
    MATCH_MP_TAC lte_trans THEN Q.EXISTS_TAC `0` THEN
    SIMP_TAC std_ss [num_not_infty,  GSYM lt_infty] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SET_TAC [],
    DISCH_TAC] THEN
   ASM_CASES_TAC ``measure m ((A:num->'a->bool) n) = 0`` THENL
   [ASM_SIMP_TAC std_ss [mul_rzero] THEN MATCH_MP_TAC pow_pos_le THEN
    SIMP_TAC std_ss [half_between], ALL_TAC] THEN
   `2 pow SUC n = Normal (real (2 pow SUC n))` by METIS_TAC [normal_real] THEN
   `measure m (A n) = Normal (real (measure m (A n)))` by METIS_TAC [normal_real] THEN
   ONCE_ASM_REWRITE_TAC [] THEN SIMP_TAC std_ss [extreal_mul_def] THEN
   SIMP_TAC std_ss [extreal_inv_def] THEN
   Q_TAC SUFF_TAC `real (2 pow SUC n) * real (measure m (A n)) <> 0` THENL
   [RW_TAC std_ss [],
    ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN MATCH_MP_TAC REAL_LT_IMP_NE THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ONCE_REWRITE_TAC [GSYM extreal_lt_eq] THEN
    POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
    RW_TAC std_ss [GSYM extreal_of_num_def] THENL
    [ALL_TAC,
     FIRST_ASSUM (ASSUME_TAC o MATCH_MP MEASURE_SPACE_POSITIVE) THEN
     FULL_SIMP_TAC std_ss [positive_def] THEN
     POP_ASSUM (MP_TAC o Q.SPEC `A (n:num)`) THEN ASM_SIMP_TAC std_ss [] THEN
     FULL_SIMP_TAC std_ss [le_lt]] THEN
    MATCH_MP_TAC pow_pos_lt THEN SIMP_TAC real_ss [extreal_lt_eq, extreal_of_num_def]] THEN
   `real (measure m (A n)) <> 0` by METIS_TAC [extreal_of_num_def, extreal_11] THEN
   KNOW_TAC ``real (2 pow SUC n) <> 0`` THENL
   [SIMP_TAC std_ss [GSYM extreal_11, GSYM extreal_of_num_def] THEN
    RULE_ASSUM_TAC (ONCE_REWRITE_RULE [EQ_SYM_EQ]) THEN ASM_REWRITE_TAC [] THEN
    ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN MATCH_MP_TAC lt_imp_ne THEN
    MATCH_MP_TAC pow_pos_lt THEN SIMP_TAC real_ss [extreal_lt_eq, extreal_of_num_def],
    DISCH_TAC] THEN
   ASM_SIMP_TAC std_ss [REAL_INV_MUL, GSYM extreal_mul_def] THEN
   Q_TAC SUFF_TAC `Normal (inv (real (measure m (A n)))) *
                   Normal (real (measure m (A n))) = 1` THENL
   [DISCH_TAC, SIMP_TAC std_ss [extreal_mul_def] THEN
    GEN_REWR_TAC RAND_CONV [extreal_of_num_def] THEN
    SIMP_TAC std_ss [extreal_11] THEN ASM_SIMP_TAC std_ss [REAL_MUL_LINV]] THEN
   RW_TAC std_ss [mul_rone] THEN
   Q_TAC SUFF_TAC `Normal (inv (real (2 pow SUC n))) <= (1 / 2) pow SUC n` THENL
   [GEN_REWR_TAC (LAND_CONV o LAND_CONV) [GSYM mul_rone] THEN
    POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [EQ_SYM_EQ]) THEN
    DISCH_THEN (fn th => REWRITE_TAC [th]) THEN SIMP_TAC std_ss [mul_assoc],
    ALL_TAC] THEN ASM_SIMP_TAC std_ss [normal_inv_eq] THEN
   GEN_REWR_TAC LAND_CONV [GSYM mul_lone] THEN REWRITE_TAC [GSYM extreal_div_def] THEN
   Q_TAC SUFF_TAC `0 < real (2 pow SUC n)` THENL
   [DISCH_TAC,
    REWRITE_TAC [GSYM extreal_lt_eq] THEN RULE_ASSUM_TAC (ONCE_REWRITE_RULE [EQ_SYM_EQ]) THEN
    ASM_SIMP_TAC std_ss [GSYM extreal_of_num_def] THEN
    MATCH_MP_TAC pow_pos_lt THEN SIMP_TAC real_ss [extreal_lt_eq, extreal_of_num_def]] THEN
   ASM_SIMP_TAC std_ss [GSYM le_ldiv] THEN POP_ASSUM K_TAC THEN POP_ASSUM K_TAC THEN
   RULE_ASSUM_TAC (ONCE_REWRITE_RULE [EQ_SYM_EQ]) THEN ASM_SIMP_TAC std_ss [GSYM pow_mul] THEN
   MATCH_MP_TAC le_trans THEN Q.EXISTS_TAC `(1 / 2 * 2) pow 0` THEN
   CONJ_TAC THENL [SIMP_TAC std_ss [pow_0, le_lt], ALL_TAC] THEN
   MATCH_MP_TAC pow_le_mono THEN SIMP_TAC arith_ss [] THEN
   SIMP_TAC real_ss [extreal_le_def, extreal_of_num_def, extreal_div_eq, extreal_mul_def,
                     GSYM REAL_LE_LDIV_EQ]] THEN
  FULL_SIMP_TAC std_ss [suminf_half_series_ereal] THEN
  `pos_fn_integral m h <> PosInf` by METIS_TAC [lt_infty, num_not_infty, let_trans] THEN
  Q_TAC SUFF_TAC `!x. x IN m_space m ==> ?i. x IN A i` THENL
  [DISCH_TAC,
   RULE_ASSUM_TAC (ONCE_REWRITE_RULE [EQ_SYM_EQ]) THEN
   FULL_SIMP_TAC std_ss [IN_BIGUNION, IN_UNIV, GSPECIFICATION] THEN
   METIS_TAC []] THEN
  Q_TAC SUFF_TAC `!x i. x IN A i ==> (h x = f i)` THENL
  [DISCH_TAC,
   RW_TAC std_ss [] THEN MATCH_MP_TAC suminf_cmult_indicator THEN
   ASM_SIMP_TAC std_ss []] THEN
  Q_TAC SUFF_TAC `!x. x IN m_space m ==> 0 < h x /\ h x < PosInf` THENL
  [DISCH_TAC,
   RW_TAC std_ss [] THENL
   [FIRST_X_ASSUM (MP_TAC o Q.SPEC `x`) THEN
    FIRST_X_ASSUM (MP_TAC o Q.SPEC `x`) THEN ASM_REWRITE_TAC [] THEN
    STRIP_TAC THEN DISCH_THEN (MP_TAC o Q.SPEC `i`) THEN
    ASM_REWRITE_TAC [] THEN RW_TAC std_ss [], ALL_TAC] THEN
   FIRST_X_ASSUM (MP_TAC o Q.SPEC `x`) THEN
   FIRST_X_ASSUM (MP_TAC o Q.SPEC `x`) THEN ASM_REWRITE_TAC [] THEN
   STRIP_TAC THEN DISCH_THEN (MP_TAC o Q.SPEC `i`) THEN
   ASM_REWRITE_TAC [] THEN RW_TAC std_ss [] THEN
   UNDISCH_TAC ``!x. 0 < f x /\ f x < inv (2 pow SUC x * measure m (A x))`` THEN
   DISCH_THEN (MP_TAC o Q.SPEC `i`) THEN
   ASM_CASES_TAC ``measure m ((A:num->'a->bool) i) = 0`` THENL
   [ASM_SIMP_TAC std_ss [mul_rzero] THEN
    SIMP_TAC std_ss [extreal_of_num_def, extreal_inv_def],
    ALL_TAC] THEN
   STRIP_TAC THEN MATCH_MP_TAC lte_trans THEN
   Q.EXISTS_TAC `inv (2 pow SUC i * measure m (A i))` THEN
   ASM_REWRITE_TAC [] THEN
   `(2 pow SUC i <> NegInf) /\ (2 pow SUC i <> PosInf)`
      by METIS_TAC [pow_not_infty, num_not_infty] THEN
   KNOW_TAC ``measure m ((A:num->'a->bool) i) <> NegInf`` THENL
   [FULL_SIMP_TAC std_ss [measure_space_def, positive_def, lt_infty] THEN
    MATCH_MP_TAC lte_trans THEN Q.EXISTS_TAC `0` THEN
    SIMP_TAC std_ss [num_not_infty,  GSYM lt_infty] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SET_TAC [],
    DISCH_TAC] THEN
   `2 pow SUC i = Normal (real (2 pow SUC i))` by METIS_TAC [normal_real] THEN
   `measure m (A i) = Normal (real (measure m (A i)))` by METIS_TAC [normal_real] THEN
   ONCE_ASM_REWRITE_TAC [] THEN SIMP_TAC std_ss [extreal_mul_def] THEN
   SIMP_TAC std_ss [extreal_inv_def] THEN COND_CASES_TAC THEN
   SIMP_TAC std_ss [le_lt, lt_infty]] THEN
  Q_TAC SUFF_TAC `!x. 0 <= h x` THENL
  [DISCH_TAC, GEN_TAC THEN
   ASM_CASES_TAC ``x IN m_space m`` THENL [METIS_TAC [], ALL_TAC] THEN
   POP_ASSUM MP_TAC THEN RULE_ASSUM_TAC (ONCE_REWRITE_RULE [EQ_SYM_EQ]) THEN
   ASM_SIMP_TAC std_ss [IN_BIGUNION, IN_UNIV, GSPECIFICATION] THEN
   DISCH_TAC THEN ONCE_REWRITE_TAC [GSYM suminf_0] THEN
   MATCH_MP_TAC ext_suminf_mono THEN SIMP_TAC std_ss [num_not_infty] THEN
   RW_TAC std_ss [indicator_fn_def] THEN
   ASM_SIMP_TAC std_ss [mul_rone, mul_rzero, le_refl]] THEN
  Q.EXISTS_TAC `h` THEN ASM_SIMP_TAC std_ss [] THEN
  EXPAND_TAC "h" THEN SIMP_TAC std_ss [ext_suminf_def] THEN
  MATCH_MP_TAC IN_MEASURABLE_BOREL_MONO_SUP THEN
  Q.EXISTS_TAC `(\n x. SIGMA (\i. f i * indicator_fn (A i) x) (count n))` THEN
  FULL_SIMP_TAC std_ss [measure_space_def] THEN CONJ_TAC THENL
  [ALL_TAC,
   RW_TAC std_ss [] THEN MATCH_MP_TAC EXTREAL_SUM_IMAGE_MONO_SET THEN
   SIMP_TAC real_ss [FINITE_COUNT, count_def, GSPECIFICATION, SUBSET_DEF] THEN
   RW_TAC std_ss [] THEN MATCH_MP_TAC le_mul THEN
   ASM_SIMP_TAC std_ss [indicator_fn_def] THEN COND_CASES_TAC THEN
   SIMP_TAC real_ss [le_refl, extreal_le_def, extreal_of_num_def]] THEN
  GEN_TAC THEN Q_TAC SUFF_TAC `FINITE (count n) /\ sigma_algebra (m_space m,measurable_sets m) /\
  (!i. i IN (count n) ==>
     (\i x. f i * indicator_fn (A i) x) i IN measurable (m_space m,measurable_sets m) Borel) /\
  (!i x. i IN (count n) /\ x IN space (m_space m,measurable_sets m) ==>
     (\i x. f i * indicator_fn (A i) x) i x <> NegInf) /\
  !x. x IN space (m_space m,measurable_sets m) ==>
    ((\x. SIGMA (\i. f i * indicator_fn (A i) x) (count n)) x =
     SIGMA (\i:num. (\i x. f i * indicator_fn (A i) x) i x) (count n))` THENL
  [ABBREV_TAC ``g = (\i:num x. f i * indicator_fn (A i) x)`` THEN
   ABBREV_TAC ``h = (\x. SIGMA (\i. f i * indicator_fn (A i) x) (count n))`` THEN
   METIS_TAC [IN_MEASURABLE_BOREL_SUM], ALL_TAC] THEN
  FULL_SIMP_TAC std_ss [FINITE_COUNT, measure_space_def] THEN CONJ_TAC THENL
  [ALL_TAC, RW_TAC std_ss [lt_infty] THEN MATCH_MP_TAC lte_trans THEN
   Q.EXISTS_TAC `0` THEN ASM_SIMP_TAC real_ss [indicator_fn_def] THEN
   SIMP_TAC std_ss [GSYM lt_infty, num_not_infty] THEN
   COND_CASES_TAC THEN ASM_SIMP_TAC real_ss [mul_rone, mul_rzero, le_refl]] THEN
  RW_TAC std_ss [] THEN
  ONCE_REWRITE_TAC [METIS [] ``(\x. f i * indicator_fn (A i) x) =
                       (\x. (\x. f i) x * indicator_fn (A i) x)``] THEN
  MATCH_MP_TAC IN_MEASURABLE_BOREL_MUL_INDICATOR THEN
  FULL_SIMP_TAC std_ss [measure_space_def, subsets_def] THEN
  MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST THEN METIS_TAC []);

val Radon_Nikodym_finite_measure = store_thm ("Radon_Nikodym_finite_measure",
  ``!M N. measure_space M /\ measure_space N /\
          finite_measure M /\ finite_measure N /\
          (measurable_sets M = measurable_sets N) /\
          (measure_absolutely_continuous N M) ==>
          ?f. f IN measurable (m_space M,measurable_sets M) Borel /\
               (!x. 0 <= f x) /\
               !A. A IN measurable_sets M ==>
                 (pos_fn_integral M (\x. f x * indicator_fn A x) = measure N A)``,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC Radon_Nikodym THEN
  FULL_SIMP_TAC std_ss [sets_eq_imp_space_eq, finite_measure]);

val Sup_le_iff = store_thm ("Sup_le_iff",
  ``!A b. sup A <= b = !a. a IN A ==> a <= b``,
  METIS_TAC [sup_le, SPECIFICATION]);

val less_Sup_iff = store_thm ("less_Sup_iff",
  ``!a s. a < sup s = ?x. x IN s /\ a < x``,
  METIS_TAC [sup_lt, SPECIFICATION]);

val Sup_ereal_close = store_thm ("Sup_ereal_close",
 ``!e s. 0 < e /\ (abs (sup s) <> PosInf) /\ (s <> {}) ==>
         ?x. x IN s /\ sup s - e < x``,
  RW_TAC std_ss [] THEN
  `?r. sup s = Normal r` by METIS_TAC [extreal_cases, extreal_abs_def] THEN
  `e <> NegInf` by METIS_TAC [lt_infty, num_not_infty, lt_trans] THEN
  Q_TAC SUFF_TAC `Normal r - e < sup s` THENL
  [SIMP_TAC std_ss [less_Sup_iff] THEN RW_TAC std_ss [],
   ASM_REWRITE_TAC [] THEN ASM_CASES_TAC ``e = PosInf`` THENL
   [ASM_REWRITE_TAC [extreal_sub_def, lt_infty], ALL_TAC] THEN
   `?k. e = Normal k` by METIS_TAC [extreal_cases] THEN
   ASM_SIMP_TAC std_ss [extreal_sub_def, extreal_lt_eq] THEN
   MATCH_MP_TAC (REAL_ARITH ``0 < k ==> a - k < a:real``) THEN
   ONCE_REWRITE_TAC [GSYM extreal_lt_eq] THEN
   METIS_TAC [extreal_of_num_def]]);

val ex_inverse_of_nat_less = store_thm ("ex_inverse_of_nat_less",
  ``!x:real. 0 < x ==> ?n. inv (&n) < x``,
  RW_TAC std_ss [] THEN FIRST_ASSUM (MP_TAC o MATCH_MP reals_Archimedean) THEN
  METIS_TAC []);

val Sup_countable_SUPR = store_thm ("Sup_countable_SUPR",
  ``!A. A <> {} ==> ?f:num->extreal. IMAGE f UNIV SUBSET A /\
                      (sup A = sup {f n | n IN UNIV})``,
  RW_TAC std_ss [] THEN ASM_CASES_TAC ``?r. sup A = Normal r`` THENL
  [FULL_SIMP_TAC std_ss [] THEN
   Q_TAC SUFF_TAC `!n:num. ?x. x IN A /\ sup A < x + 1 / &n` THENL
   [DISCH_TAC,
    GEN_TAC THEN Q_TAC SUFF_TAC `?x. x IN A /\ sup A - 1 / &n < x` THENL
    [RW_TAC std_ss [],
     MATCH_MP_TAC Sup_ereal_close THEN
     ASM_SIMP_TAC std_ss [extreal_abs_def, lt_infty] THEN
     SIMP_TAC std_ss [extreal_div_def, mul_lone] THEN
     ASM_SIMP_TAC std_ss [extreal_inv_def, extreal_of_num_def] THEN
     COND_CASES_TAC THENL [SIMP_TAC std_ss [lt_infty], ALL_TAC] THEN
     ASM_SIMP_TAC std_ss [extreal_lt_eq, REAL_LT_INV_EQ] THEN
     METIS_TAC [REAL_POS, REAL_LE_LT]] THEN
    Q.EXISTS_TAC `x` THEN ASM_REWRITE_TAC [] THEN
    FULL_SIMP_TAC std_ss [extreal_div_def, mul_lone] THEN
    FULL_SIMP_TAC std_ss [extreal_inv_def, extreal_of_num_def] THEN
    COND_CASES_TAC THEN FULL_SIMP_TAC std_ss [] THENL
    [FULL_SIMP_TAC std_ss [extreal_sub_def, GSYM lt_infty] THEN
     ASM_CASES_TAC ``x = PosInf`` THENL
     [ASM_SIMP_TAC std_ss [extreal_add_def, lt_infty], ALL_TAC] THEN
     `x = Normal (real x)` by METIS_TAC [normal_real] THEN
     METIS_TAC [extreal_add_def, lt_infty], ALL_TAC] THEN
    ASM_CASES_TAC ``x = PosInf`` THENL
    [METIS_TAC [extreal_add_def, lt_infty], ALL_TAC] THEN
    ASM_CASES_TAC ``x = NegInf`` THENL
    [METIS_TAC [extreal_sub_def, lt_infty], ALL_TAC] THEN
    `x = Normal (real x)` by METIS_TAC [normal_real] THEN
    ONCE_ASM_REWRITE_TAC [] THEN
    SIMP_TAC std_ss [extreal_lt_eq, extreal_add_def] THEN
    ONCE_REWRITE_TAC [REAL_ARITH ``a < b + c = a - c < b:real``] THEN
    SIMP_TAC std_ss [GSYM extreal_lt_eq, GSYM extreal_sub_def] THEN
    METIS_TAC [normal_real]] THEN
   Q_TAC SUFF_TAC `?f:num->extreal. !x. f x IN A /\ sup A < f x + 1 / &x` THENL
   [STRIP_TAC, METIS_TAC []] THEN
   Q_TAC SUFF_TAC `sup {f n | n IN univ(:num)} = sup A` THENL
   [DISCH_TAC,
    Q_TAC SUFF_TAC `!i. f i <= sup A` THENL
    [DISCH_TAC,
     GEN_TAC THEN MATCH_MP_TAC le_sup_imp THEN
     ONCE_REWRITE_TAC [GSYM SPECIFICATION] THEN METIS_TAC []] THEN
    Q_TAC SUFF_TAC `!y. (!i. i IN univ(:num) ==> f i <= y) ==>
                      sup A <= y` THENL
    [DISCH_TAC,
     RW_TAC std_ss [] THEN MATCH_MP_TAC le_epsilon THEN RW_TAC std_ss [] THEN
     `e <> NegInf` by METIS_TAC [lt_trans, lt_infty] THEN
     `e = Normal (real e)` by METIS_TAC [normal_real] THEN
     ONCE_ASM_REWRITE_TAC [] THEN
     Q_TAC SUFF_TAC `?n. inv &n < real e /\ 0 < n` THENL
     [STRIP_TAC,
      Q_TAC SUFF_TAC `0 < real e` THENL
      [GEN_REWR_TAC LAND_CONV [REAL_ARCH_INV],
       ASM_SIMP_TAC std_ss [GSYM extreal_lt_eq, normal_real] THEN
       ASM_SIMP_TAC std_ss [GSYM extreal_of_num_def]] THEN
      STRIP_TAC THEN Q.EXISTS_TAC `n` THEN ASM_SIMP_TAC arith_ss []] THEN
     MATCH_MP_TAC le_trans THEN Q.EXISTS_TAC `f n + 1 / &n` THEN
     CONJ_TAC THENL [METIS_TAC [le_lt], ALL_TAC] THEN
     MATCH_MP_TAC le_add2 THEN ASM_SIMP_TAC std_ss [IN_UNIV] THEN
     SIMP_TAC std_ss [extreal_div_def, mul_lone] THEN
     SIMP_TAC std_ss [extreal_of_num_def, extreal_inv_def] THEN
     COND_CASES_TAC THENL
     [POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN REWRITE_TAC [GSYM REAL_LT] THEN
      SIMP_TAC real_ss [], ALL_TAC] THEN
     ASM_SIMP_TAC std_ss [extreal_le_def, REAL_LE_LT]] THEN
    SIMP_TAC std_ss [sup_eq] THEN CONJ_TAC THEN RW_TAC std_ss [] THENL
    [POP_ASSUM MP_TAC THEN GEN_REWR_TAC LAND_CONV [GSYM SPECIFICATION] THEN
     SIMP_TAC std_ss [GSPECIFICATION, IN_UNIV] THEN RW_TAC std_ss [] THEN
     METIS_TAC [], ALL_TAC] THEN
    RULE_ASSUM_TAC (ONCE_REWRITE_RULE [EQ_SYM_EQ]) THEN ASM_REWRITE_TAC [] THEN
    POP_ASSUM MP_TAC THEN POP_ASSUM (fn th => DISCH_TAC THEN MATCH_MP_TAC th) THEN
    RW_TAC std_ss [IN_UNIV] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ONCE_REWRITE_TAC [GSYM SPECIFICATION] THEN SET_TAC []] THEN
   Q.EXISTS_TAC `f` THEN ASM_SET_TAC [], ALL_TAC] THEN
  ASM_CASES_TAC ``sup A = PosInf`` THENL
  [FULL_SIMP_TAC std_ss [GSYM MEMBER_NOT_EMPTY] THEN
   ASM_CASES_TAC ``PosInf IN A`` THENL
   [Q.EXISTS_TAC `(\x. PosInf)` THEN CONJ_TAC THENL [ASM_SET_TAC [], ALL_TAC] THEN
    SIMP_TAC std_ss [] THEN REWRITE_TAC [SET_RULE ``{PosInf | n IN univ(:num)} = {PosInf}``] THEN
    SIMP_TAC std_ss [sup_sing], ALL_TAC] THEN
   Q_TAC SUFF_TAC `?x. x IN A /\ 0 <= x` THENL
   [STRIP_TAC,
    UNDISCH_TAC ``sup A = PosInf`` THEN ONCE_REWRITE_TAC [MONO_NOT_EQ] THEN
    SIMP_TAC std_ss [sup_eq] THEN RW_TAC std_ss [lt_infty, GSYM extreal_lt_def] THEN
    Q.EXISTS_TAC `0` THEN SIMP_TAC std_ss [GSYM lt_infty, num_not_infty] THEN
    GEN_TAC THEN GEN_REWR_TAC LAND_CONV [GSYM SPECIFICATION] THEN DISCH_TAC THEN
    FIRST_X_ASSUM (MP_TAC o Q.SPEC `z`) THEN ASM_SIMP_TAC std_ss [le_lt]] THEN
   Q_TAC SUFF_TAC `!n. ?f. f IN A /\ x' + Normal (&n) <= f` THENL
   [DISCH_TAC,
    CCONTR_TAC THEN Q_TAC SUFF_TAC `?n. sup A <= x' + Normal (&n)` THENL
    [RW_TAC std_ss [GSYM extreal_lt_def] THEN
     `x' <> PosInf` by METIS_TAC [] THEN
     ASM_CASES_TAC ``x' = NegInf`` THENL
     [FULL_SIMP_TAC std_ss [extreal_add_def, lt_infty], ALL_TAC] THEN
     `?r. x' = Normal r` by METIS_TAC [extreal_cases] THEN
     ASM_SIMP_TAC std_ss [extreal_add_def, lt_infty],
     ALL_TAC] THEN
    SIMP_TAC std_ss [sup_le] THEN FULL_SIMP_TAC std_ss [GSYM extreal_lt_def] THEN
    Q.EXISTS_TAC `n` THEN GEN_TAC THEN GEN_REWR_TAC LAND_CONV [GSYM SPECIFICATION] THEN
    DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o Q.SPEC `y`) THEN ASM_REWRITE_TAC [] THEN
    SIMP_TAC std_ss [le_lt]] THEN
   Q_TAC SUFF_TAC `?f. !z. f z IN A /\ x' + Normal (&z) <= f z` THENL
   [STRIP_TAC, METIS_TAC []] THEN
   Q_TAC SUFF_TAC `sup {f n | n IN UNIV} = PosInf` THENL
   [DISCH_TAC THEN Q.EXISTS_TAC `f` THEN ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
    ASM_REWRITE_TAC [] THEN ASM_SET_TAC [],
    ALL_TAC] THEN
   Q_TAC SUFF_TAC `!n. ?i. Normal (&n) <= f i` THENL
   [DISCH_TAC,
    GEN_TAC THEN POP_ASSUM (MP_TAC o Q.SPEC `n`) THEN STRIP_TAC THEN
    Q.EXISTS_TAC `n` THEN MATCH_MP_TAC le_trans THEN
    Q.EXISTS_TAC `x' + Normal (&n)` THEN ASM_REWRITE_TAC [] THEN
    `x' <> PosInf` by METIS_TAC [] THEN
    `x' <> NegInf` by (METIS_TAC [lt_infty, lte_trans, num_not_infty]) THEN
    `?r. x' = Normal r` by (METIS_TAC [extreal_cases]) THEN
    ASM_SIMP_TAC std_ss [extreal_add_def, extreal_le_def] THEN
    MATCH_MP_TAC (REAL_ARITH ``0 <= b ==> a <= b + a:real``) THEN
    METIS_TAC [extreal_le_def, extreal_of_num_def]] THEN
   SIMP_TAC std_ss [sup_eq] THEN CONJ_TAC THENL [SIMP_TAC std_ss [le_infty], ALL_TAC] THEN
   RW_TAC std_ss [] THEN POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC [MONO_NOT_EQ] THEN
   RW_TAC std_ss [GSYM extreal_lt_def, GSYM lt_infty] THEN
   POP_ASSUM (MP_TAC o MATCH_MP SIMP_EXTREAL_ARCH) THEN STRIP_TAC THEN
   FIRST_X_ASSUM (MP_TAC o Q.SPEC `SUC n`) THEN STRIP_TAC THEN
   Q.EXISTS_TAC `f i` THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC [GSYM SPECIFICATION] THEN SIMP_TAC std_ss [GSPECIFICATION] THEN
    METIS_TAC [IN_UNIV], ALL_TAC] THEN
   MATCH_MP_TAC lte_trans THEN Q.EXISTS_TAC `Normal (&SUC n)` THEN
   ASM_REWRITE_TAC [] THEN MATCH_MP_TAC let_trans THEN Q.EXISTS_TAC `&n` THEN
   ASM_REWRITE_TAC [] THEN SIMP_TAC real_ss [extreal_of_num_def, extreal_lt_eq],
   ALL_TAC] THEN
  `sup A = NegInf` by METIS_TAC [extreal_cases] THEN
  POP_ASSUM (MP_TAC o REWRITE_RULE [sup_eq]) THEN RW_TAC std_ss [le_infty] THEN
  `A = {NegInf}` by ASM_SET_TAC [] THEN
  ASM_REWRITE_TAC [] THEN Q.EXISTS_TAC `(\n. NegInf)` THEN
  CONJ_TAC THENL [SET_TAC [], ALL_TAC] THEN SIMP_TAC std_ss [] THEN
  AP_TERM_TAC THEN SET_TAC []);

val SUPR_countable_SUPR = store_thm ("SUPR_countable_SUPR",
  ``!A g. A <> {} ==> ?f:num->extreal. IMAGE f UNIV SUBSET IMAGE g A /\
          (sup {g n | n IN A} = sup {f n | n IN UNIV})``,
  RW_TAC std_ss [] THEN ASSUME_TAC Sup_countable_SUPR THEN
  POP_ASSUM (MP_TAC o Q.SPEC `IMAGE g A`) THEN
  SIMP_TAC std_ss [GSYM IMAGE_DEF] THEN DISCH_THEN (MATCH_MP_TAC) THEN
  ASM_SET_TAC []);

val measure_subadditive_finite = store_thm ("measure_subadditive_finite",
 ``!I A M. measure_space M /\ FINITE I /\
           IMAGE A I SUBSET measurable_sets M ==>
           measure M (BIGUNION {A i | (i:num) IN I}) <=
           SIGMA (\i. measure M (A i)) I``,
  RW_TAC std_ss [] THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
  Q.SPEC_TAC (`I'`,`I'`) THEN SET_INDUCT_TAC THENL
  [SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_EMPTY, NOT_IN_EMPTY] THEN
   REWRITE_TAC [SET_RULE ``{A i | i | F} = {}``] THEN
   FULL_SIMP_TAC std_ss [BIGUNION_EMPTY, measure_space_def, positive_def] THEN
   SIMP_TAC std_ss [le_refl], ALL_TAC] THEN
  REWRITE_TAC [SET_RULE ``BIGUNION {A i | i IN e INSERT s} =
                          BIGUNION {A i | i IN s} UNION A e``] THEN
  DISCH_TAC THEN MATCH_MP_TAC le_trans THEN
  Q.EXISTS_TAC `measure M (BIGUNION {A i | i IN s}) + measure M (A e)` THEN
  CONJ_TAC THENL
  [Q_TAC SUFF_TAC `measure M (BIGUNION {A i | i IN s} UNION A e) =
                   measure M (BIGUNION {A i | i IN s}) +
                   measure M (A e DIFF BIGUNION {A i | i IN s})` THENL
   [DISC_RW_KILL,
    MATCH_MP_TAC ADDITIVE THEN ASM_SIMP_TAC std_ss [MEASURE_SPACE_ADDITIVE] THEN
    REPEAT CONJ_TAC THENL
    [ONCE_REWRITE_TAC [METIS [subsets_def]
     ``measurable_sets m = subsets (m_space m, measurable_sets m)``] THEN
     MATCH_MP_TAC SIGMA_ALGEBRA_COUNTABLE_UNION THEN
     FULL_SIMP_TAC std_ss [measure_space_def] THEN
     CONJ_TAC THENL [SIMP_TAC std_ss [GSYM IMAGE_DEF] THEN
      MATCH_MP_TAC image_countable THEN
      SIMP_TAC std_ss [pred_setTheory.COUNTABLE_NUM], ALL_TAC] THEN
     SIMP_TAC std_ss [GSYM IMAGE_DEF, SUBSET_DEF, IN_IMAGE, subsets_def, GSPECIFICATION] THEN
     GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN ASM_SET_TAC [],
     ALL_TAC,
     ASM_SIMP_TAC std_ss [DISJOINT_DEF] THEN SET_TAC [],
     SET_TAC []] THEN
    ONCE_REWRITE_TAC [METIS [subsets_def]
     ``measurable_sets m = subsets (m_space m, measurable_sets m)``] THEN
    MATCH_MP_TAC ALGEBRA_DIFF THEN
    FULL_SIMP_TAC std_ss [measure_space_def, sigma_algebra_def] THEN
    SIMP_TAC std_ss [subsets_def] THEN CONJ_TAC THENL [ASM_SET_TAC [], ALL_TAC] THEN
    ONCE_REWRITE_TAC [METIS [subsets_def]
     ``measurable_sets m = subsets (m_space m, measurable_sets m)``] THEN
    MATCH_MP_TAC SIGMA_ALGEBRA_COUNTABLE_UNION THEN
    FULL_SIMP_TAC std_ss [sigma_algebra_def] THEN
    CONJ_TAC THENL [SIMP_TAC std_ss [GSYM IMAGE_DEF] THEN
     MATCH_MP_TAC image_countable THEN
     SIMP_TAC std_ss [pred_setTheory.COUNTABLE_NUM], ALL_TAC] THEN
    SIMP_TAC std_ss [GSYM IMAGE_DEF, SUBSET_DEF, IN_IMAGE, subsets_def, GSPECIFICATION] THEN
    GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN ASM_SET_TAC []] THEN
   MATCH_MP_TAC le_ladd_imp THEN MATCH_MP_TAC INCREASING THEN
   ASM_SIMP_TAC std_ss [MEASURE_SPACE_INCREASING] THEN
   CONJ_TAC THENL [ASM_SET_TAC [], ALL_TAC] THEN
   CONJ_TAC THENL [ALL_TAC, ASM_SET_TAC []] THEN
   ONCE_REWRITE_TAC [METIS [subsets_def]
    ``measurable_sets m = subsets (m_space m, measurable_sets m)``] THEN
    MATCH_MP_TAC ALGEBRA_DIFF THEN
    FULL_SIMP_TAC std_ss [measure_space_def, sigma_algebra_def] THEN
    CONJ_TAC THENL [ASM_SET_TAC [subsets_def], ALL_TAC] THEN
    MATCH_MP_TAC SIGMA_ALGEBRA_COUNTABLE_UNION THEN
    FULL_SIMP_TAC std_ss [sigma_algebra_def] THEN
    CONJ_TAC THENL [SIMP_TAC std_ss [GSYM IMAGE_DEF] THEN
     MATCH_MP_TAC image_countable THEN
     SIMP_TAC std_ss [pred_setTheory.COUNTABLE_NUM], ALL_TAC] THEN
    SIMP_TAC std_ss [GSYM IMAGE_DEF, SUBSET_DEF, IN_IMAGE, subsets_def, GSPECIFICATION] THEN
    GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN ASM_SET_TAC [], ALL_TAC] THEN
   Q_TAC SUFF_TAC `SIGMA (\i. measure M (A i)) (e INSERT s) =
    SIGMA (\i. measure M (A i)) (s DELETE e) + (\i. measure M (A i)) e` THENL
   [DISC_RW_KILL THEN SIMP_TAC std_ss [] THEN MATCH_MP_TAC le_radd_imp THEN
    ASM_SIMP_TAC std_ss [SET_RULE ``e NOTIN s ==> (s DELETE e = s)``] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SET_TAC [],
    ALL_TAC] THEN
   ASM_CASES_TAC ``!x:num. x IN e INSERT s ==> ((\i. measure M (A i)) x <> PosInf)`` THENL
   [`(\i. measure M (A i)) e <> PosInf` by (FIRST_ASSUM MATCH_MP_TAC THEN ASM_SET_TAC []) THEN
    `SIGMA (\i. measure M (A i)) (s DELETE e) <> PosInf`
     by (MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_POS_INF THEN
         ASM_SIMP_TAC std_ss [SET_RULE ``e NOTIN s ==> (s DELETE e = s)``] THEN
         ASM_SET_TAC []) THEN
    `SIGMA (\i. measure M (A i)) (s DELETE e) + (\i. measure M (A i)) e =
     (\i. measure M (A i)) e + SIGMA (\i. measure M (A i)) (s DELETE e)`
      by METIS_TAC [add_comm] THEN ONCE_ASM_REWRITE_TAC [] THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP EXTREAL_SUM_IMAGE_PROPERTY_POS) THEN
    POP_ASSUM MATCH_MP_TAC THEN FULL_SIMP_TAC std_ss [],
    ALL_TAC] THEN FULL_SIMP_TAC std_ss [] THEN
   Q_TAC SUFF_TAC `!x. x IN s ==> (\i. measure M (A i)) x <= SIGMA (\i. measure M (A i)) s` THENL
   [DISCH_TAC,
    MATCH_MP_TAC EXTREAL_SUM_IMAGE_POS_MEM_LE THEN RW_TAC std_ss [] THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP MEASURE_SPACE_POSITIVE) THEN
    FULL_SIMP_TAC std_ss [positive_def] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SET_TAC []] THEN
   Q_TAC SUFF_TAC `!x. x IN (e INSERT s) ==>
    (\i. measure M (A i)) x <= SIGMA (\i. measure M (A i)) (e INSERT s)` THENL
   [DISCH_TAC,
    MATCH_MP_TAC EXTREAL_SUM_IMAGE_POS_MEM_LE THEN RW_TAC std_ss [FINITE_INSERT] THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP MEASURE_SPACE_POSITIVE) THEN
    FULL_SIMP_TAC std_ss [positive_def] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SET_TAC []] THEN
   POP_ASSUM (MP_TAC o Q.SPEC `x`) THEN ASM_SIMP_TAC std_ss [le_infty] THEN
   DISCH_TAC THEN UNDISCH_TAC ``(x:num) IN e INSERT s`` THEN
   Q_TAC SUFF_TAC `SIGMA (\i. measure M (A i)) (s DELETE e) <> NegInf` THENL
   [DISCH_TAC,
    MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_NEG_INF THEN
    ASM_SIMP_TAC std_ss [SET_RULE ``e NOTIN s ==> (s DELETE e = s)``] THEN
    RW_TAC std_ss [lt_infty] THEN MATCH_MP_TAC lte_trans THEN
    Q.EXISTS_TAC `0` THEN SIMP_TAC std_ss [GSYM lt_infty, num_not_infty] THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP MEASURE_SPACE_POSITIVE) THEN
    FULL_SIMP_TAC std_ss [positive_def] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SET_TAC []] THEN
   RW_TAC std_ss [INSERT_DEF, GSPECIFICATION] THENL
   [ASM_REWRITE_TAC [] THEN
    ASM_CASES_TAC ``SIGMA (\i:num. measure M (A i)) (s DELETE e) = PosInf`` THENL
    [FULL_SIMP_TAC std_ss [extreal_add_def], ALL_TAC] THEN
    METIS_TAC [normal_real, extreal_add_def],
    ALL_TAC] THEN
   FIRST_X_ASSUM (MP_TAC o Q.SPEC `x`) THEN ASM_SIMP_TAC std_ss [le_infty] THEN
   ASM_SIMP_TAC std_ss [SET_RULE ``e NOTIN s ==> (s DELETE e = s)``] THEN
   DISCH_TAC THEN Q_TAC SUFF_TAC `measure M (A e) <> NegInf` THENL
   [DISCH_TAC,
    RW_TAC std_ss [lt_infty] THEN MATCH_MP_TAC lte_trans THEN
    Q.EXISTS_TAC `0` THEN SIMP_TAC std_ss [GSYM lt_infty, num_not_infty] THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP MEASURE_SPACE_POSITIVE) THEN
    FULL_SIMP_TAC std_ss [positive_def] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SET_TAC []] THEN
   ASM_CASES_TAC ``measure M (A (e:num)) = PosInf`` THENL
   [FULL_SIMP_TAC std_ss [extreal_add_def], ALL_TAC] THEN
   METIS_TAC [normal_real, extreal_add_def]);

val split_space_into_finite_sets_and_rest = store_thm ("split_space_into_finite_sets_and_rest",
  ``!M N. measure_space M /\ measure_space N /\
          finite_measure M /\ measure_absolutely_continuous N M /\
          (measurable_sets M = measurable_sets N) ==>
          ?A0 B. A0 IN measurable_sets M /\ disjoint_family B /\
                 IMAGE B univ(:num) SUBSET measurable_sets M /\
                 (A0 = m_space M DIFF BIGUNION {B i | i IN UNIV}) /\
                 (!A. A IN measurable_sets M /\ A SUBSET A0 ==>
                  (((measure M A = 0) /\ (measure N A = 0)) \/
                   (0 < measure M A /\ (measure N A = PosInf)))) /\
                 (!i. measure N (B i) <> PosInf)``,
  RW_TAC std_ss [] THEN
  ABBREV_TAC ``Q = {x | x IN measurable_sets M /\ (measure N x <> PosInf)}`` THEN
  ABBREV_TAC ``a = sup {measure M x | x IN Q}`` THEN
  Q_TAC SUFF_TAC `{} IN Q` THENL
  [DISCH_TAC,
   RW_TAC std_ss [GSPECIFICATION] THEN
   FULL_SIMP_TAC std_ss [measure_space_def, positive_def, num_not_infty, sigma_algebra_iff2]] THEN
  `Q <> {}` by ASM_SET_TAC [] THEN
  Q_TAC SUFF_TAC `a <= measure M (m_space M)` THENL
  [DISCH_TAC,
   EXPAND_TAC "a" THEN REWRITE_TAC [sup_le] THEN GEN_TAC THEN
   GEN_REWR_TAC LAND_CONV [GSYM SPECIFICATION] THEN
   SIMP_TAC std_ss [GSPECIFICATION] THEN RW_TAC std_ss [] THEN
   MATCH_MP_TAC INCREASING THEN
   ASM_SIMP_TAC std_ss [MEASURE_SPACE_MSPACE_MEASURABLE, MEASURE_SPACE_INCREASING] THEN
   FULL_SIMP_TAC std_ss [GSPECIFICATION, MEASURE_SPACE_SUBSET_MSPACE]] THEN
  Q_TAC SUFF_TAC `a <> PosInf` THENL
  [DISCH_TAC,
   EXPAND_TAC "a" THEN FULL_SIMP_TAC std_ss [finite_measure, lt_infty] THEN
   MATCH_MP_TAC let_trans THEN Q.EXISTS_TAC `measure M (m_space M)` THEN
   ASM_SIMP_TAC std_ss []] THEN
  Q_TAC SUFF_TAC `?Q''. IMAGE Q'' UNIV SUBSET IMAGE (measure M) Q /\
                        (a = sup {Q'' i | i IN univ(:num)})` THENL
  [STRIP_TAC,
   FIRST_ASSUM (ASSUME_TAC o MATCH_MP SUPR_countable_SUPR) THEN
   POP_ASSUM (MP_TAC o Q.SPEC `(\x. measure M x)`) THEN STRIP_TAC THEN
   Q.EXISTS_TAC `f` THEN METIS_TAC []] THEN
  Q_TAC SUFF_TAC `!i. ?Q'. (Q'' i = measure M Q') /\ Q' IN Q` THENL
  [STRIP_TAC, ASM_SET_TAC []] THEN
  Q_TAC SUFF_TAC `?Q'. !i. (Q'' i = measure M (Q' i)) /\ Q' i IN Q` THENL
  [STRIP_TAC, METIS_TAC []] THEN
  Q_TAC SUFF_TAC `a = sup {measure M (Q' i) | i IN univ(:num)}` THENL
  [DISCH_TAC, FULL_SIMP_TAC std_ss []] THEN
  ABBREV_TAC ``D = (\n. BIGUNION {Q' i | i <= n:num})`` THEN
  Q_TAC SUFF_TAC `sup {measure M (D i) | i IN univ(:num)} =
                  measure M (BIGUNION {D i | i IN univ(:num)})` THENL
  [DISCH_TAC, SIMP_TAC std_ss [GSYM IMAGE_DEF] THEN
   MATCH_MP_TAC (REWRITE_RULE [o_DEF] MONOTONE_CONVERGENCE2) THEN
   ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
   [EVAL_TAC THEN SRW_TAC[] [IN_DEF,IN_FUNSET]  THEN
    ONCE_REWRITE_TAC [GSYM SPECIFICATION] THEN RW_TAC std_ss [] THEN
    ONCE_REWRITE_TAC [SET_RULE ``{Q' i' | i' <= i} =
             IMAGE (\i':num. Q' i') {i' | i' <= i}``] THEN
    ONCE_REWRITE_TAC [METIS [subsets_def]
     ``measurable_sets m = subsets (m_space m, measurable_sets m)``] THEN
    MATCH_MP_TAC SIGMA_ALGEBRA_COUNTABLE_UNION THEN
    FULL_SIMP_TAC std_ss [measure_space_def] THEN
    CONJ_TAC THENL [MATCH_MP_TAC image_countable THEN
     SIMP_TAC std_ss [pred_setTheory.COUNTABLE_NUM], ALL_TAC] THEN
    SIMP_TAC std_ss [SUBSET_DEF, IN_IMAGE, subsets_def, GSPECIFICATION] THEN
    GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    FIRST_X_ASSUM (MP_TAC o Q.SPEC `i'`) THEN
    SIMP_TAC std_ss [GSPECIFICATION] THEN METIS_TAC [], ALL_TAC] THEN
   RW_TAC std_ss [SUBSET_DEF, IN_BIGUNION, GSPECIFICATION] THEN
   Q.EXISTS_TAC `Q' i` THEN ASM_REWRITE_TAC [] THEN
   Q.EXISTS_TAC `i` THEN ASM_SIMP_TAC arith_ss []] THEN
  Q_TAC SUFF_TAC `!i. Q' i IN measurable_sets M` THENL
  [DISCH_TAC,
   GEN_TAC THEN FIRST_X_ASSUM (MP_TAC o Q.SPEC `i`) THEN
   RW_TAC std_ss [GSPECIFICATION] THEN METIS_TAC []] THEN
  Q_TAC SUFF_TAC `!i. D i IN measurable_sets M` THENL
  [DISCH_TAC,
   RW_TAC std_ss [] THEN
   ONCE_REWRITE_TAC [SET_RULE ``{Q' i' | i' <= i} =
            IMAGE (\i':num. Q' i') {i' | i' <= i}``] THEN
   ONCE_REWRITE_TAC [METIS [subsets_def]
    ``measurable_sets m = subsets (m_space m, measurable_sets m)``] THEN
   MATCH_MP_TAC SIGMA_ALGEBRA_COUNTABLE_UNION THEN
   FULL_SIMP_TAC std_ss [measure_space_def] THEN
   CONJ_TAC THENL [MATCH_MP_TAC image_countable THEN
    SIMP_TAC std_ss [pred_setTheory.COUNTABLE_NUM], ALL_TAC] THEN
   SIMP_TAC std_ss [SUBSET_DEF, IN_IMAGE, subsets_def, GSPECIFICATION] THEN
   GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN METIS_TAC []] THEN
  Q_TAC SUFF_TAC `!i. D i IN Q` THENL
  [DISCH_TAC,
   Q_TAC SUFF_TAC `!i. IMAGE Q' {x | x <= i} SUBSET measurable_sets M` THENL
   [DISCH_TAC,
    RW_TAC std_ss [SUBSET_DEF, IN_IMAGE] THEN METIS_TAC []] THEN
   Q_TAC SUFF_TAC `!i. measure N (D i) <= SIGMA (\i. measure N (Q' i)) {x | x <= i}` THENL
   [DISCH_TAC THEN GEN_TAC THEN EXPAND_TAC "Q" THEN
    FULL_SIMP_TAC std_ss [GSPECIFICATION] THEN CONJ_TAC THENL
    [METIS_TAC [], ALL_TAC] THEN
    REWRITE_TAC [lt_infty] THEN MATCH_MP_TAC let_trans THEN
    Q.EXISTS_TAC `SIGMA (\i. measure N (Q' i)) {x | x <= i}` THEN
    ASM_REWRITE_TAC [GSYM lt_infty] THEN
    MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_POS_INF THEN
    SIMP_TAC std_ss [FINITE_NUMSEG_LE, GSPECIFICATION] THEN
    GEN_TAC THEN DISCH_TAC THEN
    PAT_X_ASSUM ``!i. (Q'' i = measure M (Q' i)) /\ Q' i IN Q`` MP_TAC THEN
    DISCH_THEN (MP_TAC o Q.SPEC `x`) THEN EXPAND_TAC "Q" THEN
    SIMP_TAC std_ss [GSPECIFICATION],
    ALL_TAC] THEN
   GEN_TAC THEN EXPAND_TAC "D" THEN
   ONCE_REWRITE_TAC [SET_RULE ``(BIGUNION {Q' i' | i' <= i:num}) =
                      (BIGUNION {Q' i' | i' IN {x | x <= i}})``] THEN
   MATCH_MP_TAC measure_subadditive_finite THEN
   ASM_SIMP_TAC std_ss [FINITE_NUMSEG_LE] THEN METIS_TAC []] THEN
  Q_TAC SUFF_TAC `!n. D n SUBSET D (SUC n)` THENL
  [DISCH_TAC,
   EXPAND_TAC "D" THEN GEN_TAC THEN SIMP_TAC std_ss [SUBSET_DEF, IN_BIGUNION] THEN
   GEN_TAC THEN SIMP_TAC std_ss [GSPECIFICATION] THEN STRIP_TAC THEN
   Q.EXISTS_TAC `Q' i` THEN FULL_SIMP_TAC std_ss [] THEN
   Q.EXISTS_TAC `i` THEN FULL_SIMP_TAC arith_ss []] THEN
  Q_TAC SUFF_TAC `a = measure M (BIGUNION {D i | i IN univ(:num)})` THENL
  [DISCH_TAC,
   REWRITE_TAC [GSYM le_antisym] THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC [sup_le] THEN GEN_TAC THEN
    GEN_REWR_TAC LAND_CONV [GSYM SPECIFICATION] THEN
    SIMP_TAC std_ss [GSPECIFICATION] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC INCREASING THEN ASM_SIMP_TAC std_ss [MEASURE_SPACE_INCREASING] THEN
    CONJ_TAC THENL
    [ALL_TAC,
     ONCE_REWRITE_TAC [METIS [subsets_def]
      ``measurable_sets m = subsets (m_space m, measurable_sets m)``] THEN
     MATCH_MP_TAC SIGMA_ALGEBRA_COUNTABLE_UNION THEN
     FULL_SIMP_TAC std_ss [measure_space_def, GSYM IMAGE_DEF] THEN
     CONJ_TAC THENL [MATCH_MP_TAC image_countable THEN
      SIMP_TAC std_ss [pred_setTheory.COUNTABLE_NUM], ALL_TAC] THEN
     SIMP_TAC std_ss [SUBSET_DEF, IN_IMAGE, subsets_def, GSPECIFICATION] THEN
     GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN METIS_TAC []] THEN
    EXPAND_TAC "D" THEN SIMP_TAC std_ss [SUBSET_DEF, IN_BIGUNION, GSPECIFICATION] THEN
    GEN_TAC THEN STRIP_TAC THEN Q.EXISTS_TAC `BIGUNION {Q' x | x <= i}` THEN
    CONJ_TAC THENL [ALL_TAC, METIS_TAC [IN_UNIV]] THEN
    ASM_SIMP_TAC arith_ss [IN_BIGUNION, GSPECIFICATION] THEN
    METIS_TAC [LESS_OR_EQ], ALL_TAC] THEN
   UNDISCH_TAC ``sup {measure M (D i) | i IN univ(:num)} =
       measure M (BIGUNION {D i | i IN univ(:num)})`` THEN
   GEN_REWR_TAC LAND_CONV [EQ_SYM_EQ] THEN SIMP_TAC std_ss [] THEN DISCH_TAC THEN
   Q_TAC SUFF_TAC `!n. BIGUNION {Q' i | i <= n} = D n` THENL
   [DISCH_TAC, METIS_TAC []] THEN
   Q_TAC SUFF_TAC `!n. ?x. x IN Q /\ measure M (BIGUNION {Q' i | i <= n}) <= measure M x` THENL
   [DISCH_TAC,
    GEN_TAC THEN Q.EXISTS_TAC `D n` THEN ASM_SIMP_TAC std_ss [le_refl]] THEN
   EXPAND_TAC "a" THEN SIMP_TAC std_ss [GSYM IMAGE_DEF] THEN
   MATCH_MP_TAC sup_le_sup_imp THEN GEN_TAC THEN
   GEN_REWR_TAC LAND_CONV [GSYM SPECIFICATION] THEN
   SIMP_TAC std_ss [IN_IMAGE] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
   FIRST_X_ASSUM (MP_TAC o Q.SPEC `i`) THEN STRIP_TAC THEN
   Q.EXISTS_TAC `measure M x'` THEN EXPAND_TAC "D" THEN ASM_REWRITE_TAC [] THEN
   ONCE_REWRITE_TAC [GSYM SPECIFICATION] THEN SIMP_TAC std_ss [IN_IMAGE] THEN
   METIS_TAC []] THEN
  ABBREV_TAC ``O_o = BIGUNION {(D:num->'a->bool) i | i IN UNIV}`` THEN
  Q_TAC SUFF_TAC `O_o IN measurable_sets M` THENL
  [DISCH_TAC,
   EXPAND_TAC "O_o" THEN
   ONCE_REWRITE_TAC [METIS [subsets_def]
    ``measurable_sets m = subsets (m_space m, measurable_sets m)``] THEN
   MATCH_MP_TAC SIGMA_ALGEBRA_COUNTABLE_UNION THEN
   FULL_SIMP_TAC std_ss [measure_space_def, GSYM IMAGE_DEF] THEN
   CONJ_TAC THENL [MATCH_MP_TAC image_countable THEN
    SIMP_TAC std_ss [pred_setTheory.COUNTABLE_NUM], ALL_TAC] THEN
   SIMP_TAC std_ss [SUBSET_DEF, IN_IMAGE, subsets_def, GSPECIFICATION] THEN
   GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN METIS_TAC []] THEN
  ABBREV_TAC ``(QQ) = (\i. if i = 0 then (Q':num->'a->bool) 0
                         else D i DIFF (D:num->'a->bool) (i - 1))`` THEN
  Q_TAC SUFF_TAC `!i. QQ i IN measurable_sets M` THENL
  [DISCH_TAC,
   GEN_TAC THEN ASM_CASES_TAC ``i = 0:num`` THENL
   [ASM_REWRITE_TAC [] THEN EXPAND_TAC "QQ" THEN ASM_SIMP_TAC std_ss [] THEN
    METIS_TAC [], ALL_TAC] THEN
   Q_TAC SUFF_TAC `?n. i = SUC n` THENL
   [STRIP_TAC,
    Q.EXISTS_TAC `PRE i` THEN ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
    REWRITE_TAC [GSYM SUC_PRE] THEN ASM_SIMP_TAC arith_ss []] THEN
   ASM_REWRITE_TAC [] THEN EXPAND_TAC "QQ" THEN ASM_SIMP_TAC arith_ss [] THEN
   ONCE_REWRITE_TAC [METIS [subsets_def]
    ``measurable_sets m = subsets (m_space m, measurable_sets m)``] THEN
   MATCH_MP_TAC ALGEBRA_DIFF THEN SIMP_TAC std_ss [subsets_def] THEN
   CONJ_TAC THENL [ALL_TAC, METIS_TAC []] THEN
   FULL_SIMP_TAC std_ss [measure_space_def, sigma_algebra_def]] THEN
  Q.EXISTS_TAC `QQ` THEN CONJ_TAC THENL
  [ONCE_REWRITE_TAC [METIS [subsets_def]
    ``measurable_sets m = subsets (m_space m, measurable_sets m)``] THEN
   MATCH_MP_TAC ALGEBRA_DIFF THEN CONJ_TAC THENL
   [FULL_SIMP_TAC std_ss [measure_space_def, sigma_algebra_def],
    ALL_TAC] THEN CONJ_TAC THENL
   [METIS_TAC [MEASURE_SPACE_MSPACE_MEASURABLE, subsets_def],
    ALL_TAC] THEN
   MATCH_MP_TAC SIGMA_ALGEBRA_COUNTABLE_UNION THEN
   FULL_SIMP_TAC std_ss [measure_space_def, GSYM IMAGE_DEF] THEN
   CONJ_TAC THENL [MATCH_MP_TAC image_countable THEN
    SIMP_TAC std_ss [pred_setTheory.COUNTABLE_NUM], ALL_TAC] THEN
   SIMP_TAC std_ss [SUBSET_DEF, IN_IMAGE, subsets_def, GSPECIFICATION] THEN
   GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN METIS_TAC [], ALL_TAC] THEN
  CONJ_TAC THENL
  [SIMP_TAC std_ss [disjoint_family, disjoint_family_on, IN_UNIV] THEN
   REPEAT STRIP_TAC THEN EXPAND_TAC "QQ" THEN
   SIMP_TAC std_ss [INTER_DEF, EXTENSION, NOT_IN_EMPTY, GSPECIFICATION] THEN
   GEN_TAC THEN REPEAT COND_CASES_TAC THENL
   [FULL_SIMP_TAC arith_ss [],
    ASM_CASES_TAC ``(x:'a) NOTIN Q' (0:num)`` THEN FULL_SIMP_TAC std_ss [] THEN
    `1 <= n` by ASM_SIMP_TAC arith_ss [] THEN EXPAND_TAC "D" THEN
    SIMP_TAC std_ss [IN_DIFF, IN_BIGUNION, GSPECIFICATION] THEN
    ASM_CASES_TAC ``(!s. x NOTIN s \/ !i. s <> (Q':num->'a->bool) i \/ ~(i <= n))`` THEN
    ASM_REWRITE_TAC [] THEN FULL_SIMP_TAC std_ss [] THEN
    Q.EXISTS_TAC `Q' 0` THEN ASM_SIMP_TAC std_ss [] THEN
    Q.EXISTS_TAC `0` THEN SIMP_TAC arith_ss [],
    ASM_CASES_TAC ``(x:'a) NOTIN Q' (0:num)`` THEN FULL_SIMP_TAC std_ss [] THEN
    `1 <= m` by ASM_SIMP_TAC arith_ss [] THEN EXPAND_TAC "D" THEN
    SIMP_TAC std_ss [IN_DIFF, IN_BIGUNION, GSPECIFICATION] THEN
    ASM_CASES_TAC ``(!s. x NOTIN s \/ !i. s <> (Q':num->'a->bool) i \/ ~(i <= m))`` THEN
    ASM_REWRITE_TAC [] THEN FULL_SIMP_TAC std_ss [] THEN
    Q.EXISTS_TAC `Q' 0` THEN ASM_SIMP_TAC std_ss [] THEN
    Q.EXISTS_TAC `0` THEN SIMP_TAC arith_ss [],
    ALL_TAC] THEN
   ASM_CASES_TAC ``x NOTIN (D:num->'a->bool) m DIFF D (m - 1)`` THEN
   FULL_SIMP_TAC std_ss [IN_DIFF] THEN
   ASM_CASES_TAC ``m < n:num`` THENL
   [ASM_CASES_TAC ``x NOTIN (D:num->'a->bool) n`` THEN ASM_SIMP_TAC std_ss [] THEN
    POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
    POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN EXPAND_TAC "D" THEN
    SIMP_TAC std_ss [IN_BIGUNION, GSPECIFICATION] THEN REPEAT STRIP_TAC THEN
    Q.EXISTS_TAC `s` THEN ASM_REWRITE_TAC [] THEN Q.EXISTS_TAC `i` THEN
    ASM_SIMP_TAC arith_ss [], ALL_TAC] THEN
   ASM_CASES_TAC ``x IN (D:num->'a->bool) (n - 1)`` THEN ASM_SIMP_TAC std_ss [] THEN
   POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
   POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN EXPAND_TAC "D" THEN
   SIMP_TAC std_ss [IN_BIGUNION, GSPECIFICATION] THEN REPEAT STRIP_TAC THEN
   `n < m` by FULL_SIMP_TAC arith_ss [] THEN
   POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
   FIRST_X_ASSUM (MP_TAC o Q.SPEC `s'`) THEN REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC [] THEN DISJ2_TAC THEN GEN_TAC THEN
   FIRST_X_ASSUM (MP_TAC o Q.SPEC `i':num`) THEN STRIP_TAC THEN
   ASM_REWRITE_TAC [] THEN DISJ2_TAC THEN
   FULL_SIMP_TAC arith_ss [NOT_LESS_EQUAL], ALL_TAC] THEN
  CONJ_TAC THENL
  [ASM_SET_TAC [], ALL_TAC] THEN
  CONJ_TAC THENL
  [ALL_TAC,
   GEN_TAC THEN EXPAND_TAC "QQ" THEN
   ASM_CASES_TAC ``i = 0:num`` THEN ASM_SIMP_TAC std_ss [] THENL
   [ASM_SET_TAC [], ALL_TAC] THEN
   SIMP_TAC std_ss [lt_infty] THEN MATCH_MP_TAC let_trans THEN
   Q.EXISTS_TAC `measure N (D i) - measure N (D (i - 1))` THEN
   CONJ_TAC THENL
   [SIMP_TAC std_ss [le_lt] THEN DISJ2_TAC THEN
    MATCH_MP_TAC MEASURE_SPACE_FINITE_DIFF_SUBSET THEN
    ASM_SIMP_TAC std_ss [] THEN REPEAT (CONJ_TAC THENL [ASM_SET_TAC [], ALL_TAC]) THEN
    CONJ_TAC THENL [METIS_TAC [ARITH_PROVE ``i <> 0 ==> (i = SUC (i - 1))``], ALL_TAC] THEN
    ASM_SET_TAC [], ALL_TAC] THEN
   REWRITE_TAC [GSYM lt_infty] THEN MATCH_MP_TAC (METIS [sub_not_infty]
    ``x <> PosInf /\ y <> NegInf ==> x - y <> PosInf``) THEN
   CONJ_TAC THENL [ASM_SET_TAC [], ALL_TAC] THEN
   `positive N` by METIS_TAC [MEASURE_SPACE_POSITIVE] THEN
   FULL_SIMP_TAC std_ss [positive_def, lt_infty] THEN
   MATCH_MP_TAC lte_trans THEN Q.EXISTS_TAC `0` THEN
   SIMP_TAC std_ss [GSYM lt_infty, num_not_infty] THEN
   FIRST_ASSUM MATCH_MP_TAC THEN METIS_TAC []] THEN
  GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC ``0 < measure M A ==> (measure N (A:'a->bool) <> PosInf)`` THENL
  [ALL_TAC, FULL_SIMP_TAC std_ss []] THEN
  ASM_CASES_TAC ``measure M (A:'a->bool) = 0`` THENL
  [FULL_SIMP_TAC std_ss [measure_absolutely_continuous_def], ALL_TAC] THEN
  `positive M` by METIS_TAC [MEASURE_SPACE_POSITIVE] THEN
  FULL_SIMP_TAC std_ss [positive_def] THEN POP_ASSUM (MP_TAC o Q.SPEC `A`) THEN
  ASM_REWRITE_TAC [le_lt] THEN STRIP_TAC THENL [ALL_TAC, METIS_TAC []] THEN
  ASM_REWRITE_TAC [] THEN UNDISCH_TAC ``0 < measure M A ==> measure N A <> PosInf`` THEN
  ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
  Q_TAC SUFF_TAC `measure M O_o + measure M A = measure M (O_o UNION A)` THENL
  [DISCH_TAC,
   ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN MATCH_MP_TAC ADDITIVE THEN
   ASM_SIMP_TAC std_ss [MEASURE_SPACE_ADDITIVE, DISJOINT_DEF] THEN
   UNDISCH_TAC ``(A:'a->bool) SUBSET m_space M DIFF BIGUNION {QQ i | i IN univ(:num)}`` THEN
   EXPAND_TAC "QQ" THEN EXPAND_TAC "O_o" THEN
   Q_TAC SUFF_TAC `BIGUNION {D i | i IN univ(:num)} =
    BIGUNION {if i = 0 then Q' 0 else D i DIFF D (i - 1) | i IN univ(:num)}` THENL
   [SET_TAC [], ALL_TAC] THEN
   SIMP_TAC std_ss [EXTENSION, IN_BIGUNION, GSPECIFICATION, IN_UNIV] THEN
   GEN_TAC THEN EQ_TAC THEN STRIP_TAC THENL
   [FULL_SIMP_TAC std_ss [] THEN POP_ASSUM K_TAC THEN
    ASM_CASES_TAC ``x IN (D:num->'a->bool) 0`` THENL
    [Q.EXISTS_TAC `D 0` THEN FULL_SIMP_TAC std_ss [] THEN
     Q.EXISTS_TAC `0` THEN EXPAND_TAC "D" THEN SIMP_TAC std_ss [] THEN
     SET_TAC [], ALL_TAC] THEN
    Q_TAC SUFF_TAC `?i. i <> 0 /\ x IN D i DIFF D (i - 1)` THENL
    [STRIP_TAC THEN Q.EXISTS_TAC `D i' DIFF D (i' - 1)` THEN
     ASM_REWRITE_TAC [] THEN METIS_TAC [], ALL_TAC] THEN
    Induct_on `i` THENL [METIS_TAC [], ALL_TAC] THEN
    DISCH_TAC THEN ASM_CASES_TAC ``x IN D (SUC i) DIFF ((D:num->'a->bool) i)`` THENL
    [Q.EXISTS_TAC `SUC i` THEN ASM_SIMP_TAC arith_ss [], ALL_TAC] THEN
    ASM_SET_TAC [], ALL_TAC] THEN
   FULL_SIMP_TAC std_ss [] THEN POP_ASSUM K_TAC THEN
   ASM_CASES_TAC ``i = 0:num`` THENL
   [Q.EXISTS_TAC `Q' 0` THEN FULL_SIMP_TAC std_ss  [] THEN
    EXPAND_TAC "D" THEN Q.EXISTS_TAC `0` THEN SET_TAC [],
    ALL_TAC] THEN
   FULL_SIMP_TAC std_ss [] THEN Q.EXISTS_TAC `D i` THEN CONJ_TAC THENL
   [ALL_TAC, METIS_TAC []] THEN
   ASM_SET_TAC []] THEN
  Q_TAC SUFF_TAC `measure M (BIGUNION {D i | i IN univ(:num)} UNION A) =
             sup {measure M ((D i) UNION A) | i IN univ(:num)}` THENL
  [DISCH_TAC,
   SIMP_TAC std_ss [GSYM IMAGE_DEF] THEN
   `(\i. measure M (D i UNION A)) = measure M o (\i. (D:num->'a->bool) i UNION A)`
     by SIMP_TAC std_ss [o_DEF] THEN
   FIRST_X_ASSUM (fn th => ONCE_REWRITE_TAC [th]) THEN
   ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN MATCH_MP_TAC MONOTONE_CONVERGENCE THEN
   ASM_SIMP_TAC std_ss [] THEN CONJ_TAC THENL
   [EVAL_TAC THEN SRW_TAC[][IN_DEF,IN_FUNSET]  THEN
    ONCE_REWRITE_TAC [GSYM SPECIFICATION] THEN
    ONCE_REWRITE_TAC [METIS [subsets_def]
     ``measurable_sets m = subsets (m_space m, measurable_sets m)``] THEN
    MATCH_MP_TAC ALGEBRA_UNION THEN
    FULL_SIMP_TAC std_ss [measure_space_def, sigma_algebra_def] THEN
    METIS_TAC [subsets_def], ALL_TAC] THEN
   CONJ_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC (SET_RULE ``a SUBSET c /\ b SUBSET d ==>
                  a UNION b SUBSET c UNION d``) THEN
    ASM_SIMP_TAC std_ss [SUBSET_REFL], ALL_TAC] THEN
   GEN_REWR_TAC (LAND_CONV o RAND_CONV) [SET_RULE ``A = BIGUNION {A}``] THEN
   REWRITE_TAC [GSYM BIGUNION_UNION] THEN
   SIMP_TAC std_ss [EXTENSION, IN_BIGUNION, IN_IMAGE, IN_UNIV, GSPECIFICATION, IN_UNION] THEN
   GEN_TAC THEN EQ_TAC THEN STRIP_TAC THENL
   [Q.EXISTS_TAC `D x' UNION A` THEN ASM_SET_TAC [],
    Q.EXISTS_TAC `D x' UNION A` THEN ASM_SET_TAC [],
    ASM_SET_TAC []]] THEN
  Q_TAC SUFF_TAC `sup {measure M ((D i) UNION A) | i IN univ(:num)} <= a` THENL
  [DISCH_TAC,
   REWRITE_TAC [sup_le] THEN GEN_TAC THEN
   GEN_REWR_TAC LAND_CONV [GSYM SPECIFICATION] THEN
   SIMP_TAC std_ss [GSPECIFICATION] THEN STRIP_TAC THEN
   UNDISCH_TAC ``sup {measure M x | x IN Q} = sup {measure M (Q' i) | i IN univ(:num)}`` THEN
   GEN_REWR_TAC LAND_CONV [EQ_SYM_EQ] THEN DISCH_TAC THEN
   ASM_REWRITE_TAC [] THEN
   Q_TAC SUFF_TAC `!i. D i UNION A IN Q` THENL
   [DISCH_TAC,
    Q_TAC SUFF_TAC `!i. D i UNION A IN measurable_sets M` THENL
    [DISCH_TAC,
     GEN_TAC THEN ONCE_REWRITE_TAC [METIS [subsets_def]
      ``measurable_sets m = subsets (m_space m, measurable_sets m)``] THEN
     MATCH_MP_TAC ALGEBRA_UNION THEN
     FULL_SIMP_TAC std_ss [measure_space_def, sigma_algebra_def] THEN
     METIS_TAC [subsets_def]] THEN
    GEN_TAC THEN EXPAND_TAC "Q" THEN ASM_SIMP_TAC std_ss [GSPECIFICATION] THEN
    CONJ_TAC THENL [METIS_TAC [], ALL_TAC] THEN
    SIMP_TAC std_ss [lt_infty] THEN MATCH_MP_TAC let_trans THEN
    Q.EXISTS_TAC `measure N (D i') + measure N A` THEN CONJ_TAC THENL
    [ALL_TAC,
     SIMP_TAC std_ss [GSYM lt_infty] THEN
     MATCH_MP_TAC (METIS [add_not_infty]
      ``x <> PosInf /\ y <> PosInf ==> x + y <> PosInf``) THEN
     ASM_SIMP_TAC std_ss [] THEN `D i' IN Q` by METIS_TAC [] THEN
     POP_ASSUM MP_TAC THEN EXPAND_TAC "Q" THEN
     SIMP_TAC std_ss [GSPECIFICATION]] THEN
    REWRITE_TAC [le_lt] THEN DISJ2_TAC THEN MATCH_MP_TAC ADDITIVE THEN
    FULL_SIMP_TAC std_ss [MEASURE_SPACE_ADDITIVE] THEN
    CONJ_TAC THENL [METIS_TAC [], ALL_TAC] THEN SIMP_TAC std_ss [DISJOINT_DEF] THEN
    SIMP_TAC std_ss [EXTENSION, IN_INTER, NOT_IN_EMPTY] THEN
    GEN_TAC THEN ASM_CASES_TAC ``(x:'a) NOTIN A`` THEN
    FULL_SIMP_TAC std_ss [] THEN
    UNDISCH_TAC ``(A:'a->bool) SUBSET m_space M DIFF BIGUNION {QQ i | i IN univ(:num)}`` THEN
    EXPAND_TAC "QQ" THEN
    Q_TAC SUFF_TAC `BIGUNION {D i | i IN univ(:num)} =
     BIGUNION {if i = 0 then Q' 0 else D i DIFF D (i - 1) | i IN univ(:num)}` THENL
    [GEN_REWR_TAC LAND_CONV [EQ_SYM_EQ] THEN DISC_RW_KILL THEN
     SIMP_TAC std_ss [SUBSET_DEF] THEN DISCH_THEN (MP_TAC o Q.SPEC `x`) THEN
     ASM_REWRITE_TAC [] THEN ASM_SET_TAC [], ALL_TAC] THEN
    SIMP_TAC std_ss [EXTENSION, IN_BIGUNION, GSPECIFICATION, IN_UNIV] THEN
    GEN_TAC THEN EQ_TAC THEN STRIP_TAC THENL
    [FULL_SIMP_TAC std_ss [] THEN POP_ASSUM K_TAC THEN
     ASM_CASES_TAC ``x' IN (D:num->'a->bool) 0`` THENL
     [Q.EXISTS_TAC `D 0` THEN FULL_SIMP_TAC std_ss [] THEN
      Q.EXISTS_TAC `0` THEN EXPAND_TAC "D" THEN SIMP_TAC std_ss [] THEN
      SET_TAC [], ALL_TAC] THEN
     Q_TAC SUFF_TAC `?i. i <> 0 /\ x' IN D i DIFF D (i - 1)` THENL
     [STRIP_TAC THEN Q.EXISTS_TAC `D i'' DIFF D (i'' - 1)` THEN
      ASM_REWRITE_TAC [] THEN METIS_TAC [], ALL_TAC] THEN
     Induct_on `i'` THENL [METIS_TAC [], ALL_TAC] THEN
     DISCH_TAC THEN ASM_CASES_TAC ``x' IN D (SUC i') DIFF ((D:num->'a->bool) i')`` THENL
     [Q.EXISTS_TAC `SUC i'` THEN ASM_SIMP_TAC arith_ss [], ALL_TAC] THEN
     ASM_SET_TAC [], ALL_TAC] THEN
    FULL_SIMP_TAC std_ss [] THEN POP_ASSUM K_TAC THEN
    ASM_CASES_TAC ``i' = 0:num`` THENL
    [Q.EXISTS_TAC `Q' 0` THEN FULL_SIMP_TAC std_ss  [] THEN
     EXPAND_TAC "D" THEN Q.EXISTS_TAC `0` THEN SET_TAC [],
     ALL_TAC] THEN
    FULL_SIMP_TAC std_ss [] THEN Q.EXISTS_TAC `D i'` THEN CONJ_TAC THENL
    [ALL_TAC, METIS_TAC []] THEN
    ASM_SET_TAC []] THEN
   MATCH_MP_TAC le_sup_imp THEN ONCE_REWRITE_TAC [GSYM SPECIFICATION] THEN
   SIMP_TAC std_ss [GSPECIFICATION] THEN METIS_TAC []] THEN
  Q_TAC SUFF_TAC `measure M A = 0` THENL
  [METIS_TAC [], ALL_TAC] THEN
  ASM_SIMP_TAC std_ss [] THEN POP_ASSUM MP_TAC THEN
  SIMP_TAC std_ss [GSYM extreal_lt_def] THEN
  ONCE_ASM_REWRITE_TAC [] THEN POP_ASSUM MP_TAC THEN
  POP_ASSUM (ASSUME_TAC o ONCE_REWRITE_RULE [EQ_SYM_EQ]) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (ASSUME_TAC o ONCE_REWRITE_RULE [EQ_SYM_EQ]) THEN
  FIRST_ASSUM (fn th => REWRITE_TAC [th]) THEN
  Q_TAC SUFF_TAC `sup {measure M (Q' i) | i IN univ(:num)} <> NegInf` THENL
  [DISCH_TAC,
   SIMP_TAC std_ss [lt_infty] THEN MATCH_MP_TAC lte_trans THEN
   Q.EXISTS_TAC `0` THEN SIMP_TAC std_ss [GSYM lt_infty, num_not_infty] THEN
   GEN_REWR_TAC LAND_CONV [GSYM sup_sing] THEN
   MATCH_MP_TAC sup_le_sup_imp THEN GEN_TAC THEN
   GEN_REWR_TAC LAND_CONV [GSYM SPECIFICATION] THEN
   SIMP_TAC std_ss [IN_SING] THEN DISCH_TAC THEN Q.EXISTS_TAC `measure M (Q' i)` THEN
   FULL_SIMP_TAC std_ss [measure_space_def, positive_def] THEN
   CONJ_TAC THENL
   [ONCE_REWRITE_TAC [GSYM SPECIFICATION] THEN SET_TAC [], ALL_TAC] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN METIS_TAC []] THEN
  GEN_REWR_TAC LAND_CONV [GSYM add_rzero] THEN METIS_TAC [lt_ladd]);

val measure_restricted = store_thm ("measure_restricted",
 ``!s t  M. measure_space M /\
         s IN measurable_sets M /\ t IN measurable_sets M ==>
        (measure (m_space M, measurable_sets M,
             (\A. if A IN measurable_sets M then
                  pos_fn_integral M (\x. indicator_fn s x * indicator_fn A x)
                else 0)) t =
         measure M (s INTER t))``,
  RW_TAC std_ss [] THEN
  `algebra (m_space M, measurable_sets M)` by
    METIS_TAC [measure_space_def, sigma_algebra_def] THEN
  `s INTER t IN measurable_sets M` by METIS_TAC [ALGEBRA_INTER, subsets_def] THEN
  Q.ABBREV_TAC `m = (m_space M,measurable_sets M,
   (\A.
      if A IN measurable_sets M then
        pos_fn_integral M (\x. indicator_fn s x * indicator_fn A x)
      else 0))` THEN
  Q_TAC SUFF_TAC `measure_space m` THENL
  [DISCH_TAC THEN `t IN measurable_sets m` by METIS_TAC [measurable_sets_def] THEN
   ASM_SIMP_TAC std_ss [GSYM pos_fn_integral_indicator] THEN
   ONCE_REWRITE_TAC [METIS [INDICATOR_FN_MUL_INTER]
    ``indicator_fn (s INTER t) = (\x. indicator_fn s x * indicator_fn t x)``] THEN
   ASM_CASES_TAC ``m_space M = {}`` THENL
   [Q_TAC SUFF_TAC `measurable_sets M = {{}}` THENL
    [DISCH_TAC,
     FULL_SIMP_TAC std_ss [measure_space_def, sigma_algebra_def, algebra_def] THEN
     FULL_SIMP_TAC std_ss [space_def, subsets_def, subset_class_def] THEN
     UNDISCH_TAC ``!x. x IN measurable_sets M ==> x SUBSET {}`` THEN
     SIMP_TAC std_ss [SUBSET_EMPTY, EXTENSION, IN_SING] THEN DISCH_TAC THEN
     GEN_TAC THEN EQ_TAC THEN ASM_SIMP_TAC std_ss [] THEN DISCH_TAC THEN
     `x = {}` by ASM_SET_TAC [] THEN METIS_TAC []] THEN
    FULL_SIMP_TAC std_ss [IN_SING] THEN
    SIMP_TAC std_ss [indicator_fn_def, NOT_IN_EMPTY, mul_rzero] THEN
    ASM_SIMP_TAC std_ss [pos_fn_integral_zero],
    ALL_TAC] THEN
   Q.UNABBREV_TAC `m` THEN
   Q_TAC SUFF_TAC `pos_fn_integral
   (m_space M,measurable_sets M,
    (\A.
       if A IN measurable_sets M then
         pos_fn_integral M (\x. max 0 (indicator_fn s x * indicator_fn A x))
      else 0)) (\x. max 0 (indicator_fn t x)) =
    pos_fn_integral M (\x. max 0 (indicator_fn s x * indicator_fn t x))` THENL
   [SIMP_TAC std_ss [extreal_max_def, le_mul, indicator_fn_pos_le] THEN
    METIS_TAC [], ALL_TAC] THEN
   MATCH_MP_TAC pos_fn_integral_density' THEN
   ASM_SIMP_TAC std_ss [] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC IN_MEASURABLE_BOREL_INDICATOR THEN
    METIS_TAC [subsets_def, measure_space_def],
    ALL_TAC] THEN
   CONJ_TAC THENL
   [SIMP_TAC std_ss [AE, ae_filter, GSPECIFICATION, null_sets] THEN
    SIMP_TAC std_ss [SUBSET_DEF, GSPECIFICATION] THEN Q.EXISTS_TAC `{}` THEN
    FULL_SIMP_TAC std_ss [measure_space_def, sigma_algebra_iff2] THEN
    FULL_SIMP_TAC std_ss [positive_def, NOT_IN_EMPTY] THEN
    GEN_TAC THEN DISJ2_TAC THEN
    SIMP_TAC std_ss [indicator_fn_def] THEN COND_CASES_TAC THEN
    SIMP_TAC real_ss [le_refl, extreal_of_num_def, extreal_le_def],
    ALL_TAC] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC IN_MEASURABLE_BOREL_INDICATOR THEN
    METIS_TAC [subsets_def, measure_space_def],
    ALL_TAC] THEN GEN_TAC THEN
   SIMP_TAC std_ss [indicator_fn_def] THEN COND_CASES_TAC THEN
   SIMP_TAC real_ss [le_refl, extreal_of_num_def, extreal_le_def],
   ALL_TAC] THEN
  Q.UNABBREV_TAC `m` THEN
  FULL_SIMP_TAC std_ss [measure_space_def, m_space_def, measurable_sets_def] THEN
  CONJ_TAC THENL
  [SIMP_TAC std_ss [positive_def, measure_def, measurable_sets_def] THEN
   SIMP_TAC std_ss [indicator_fn_def, NOT_IN_EMPTY, mul_rzero] THEN
   FULL_SIMP_TAC std_ss [COND_ID, pos_fn_integral_zero, measure_space_def] THEN
   GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC pos_fn_integral_pos THEN
   FULL_SIMP_TAC std_ss [measure_space_def] THEN GEN_TAC THEN
   REPEAT COND_CASES_TAC THEN
   SIMP_TAC real_ss [le_refl, extreal_of_num_def, extreal_le_def, mul_rone, mul_rzero],
   ALL_TAC] THEN
  SIMP_TAC std_ss [countably_additive_alt_eq, INDICATOR_FN_MUL_INTER] THEN
  REPEAT STRIP_TAC THEN SIMP_TAC std_ss [o_DEF] THEN
  `!x. A x IN measurable_sets M` by ASM_SET_TAC [] THEN
  ASM_SIMP_TAC std_ss [INTER_BIGUNION, GSPECIFICATION, IN_UNIV] THEN
  REWRITE_TAC [SET_RULE ``{s INTER x | ?i'. x = A i'} = {s INTER A i' | i' IN UNIV}``] THEN
  SIMP_TAC std_ss [GSYM IMAGE_DEF] THEN
  Q_TAC SUFF_TAC `!x. indicator_fn (BIGUNION (IMAGE (\i'. s INTER A i') univ(:num))) x =
   suminf (\j. indicator_fn ((\i'. s INTER A i') j) x)` THENL
  [DISCH_TAC THEN ASM_SIMP_TAC std_ss [],
   GEN_TAC THEN ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN MATCH_MP_TAC indicator_fn_suminf THEN
  FULL_SIMP_TAC std_ss [disjoint_family, disjoint_family_on, DISJOINT_DEF] THEN
  ASM_SET_TAC []] THEN ONCE_REWRITE_TAC [METIS [ETA_AX]
   ``(\x'. indicator_fn (s INTER A x) x') = (\x. indicator_fn (s INTER A x)) x``] THEN
  ONCE_REWRITE_TAC [METIS [] ``suminf (\j. indicator_fn (s INTER A j) x) =
                       suminf (\j. (\k. indicator_fn (s INTER A k)) j x)``] THEN
  MATCH_MP_TAC pos_fn_integral_suminf THEN ASM_SIMP_TAC std_ss [measure_space_def] THEN
  CONJ_TAC THENL
  [SIMP_TAC std_ss [indicator_fn_def] THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN
   SIMP_TAC real_ss [le_refl, extreal_of_num_def, extreal_le_def], ALL_TAC] THEN
  GEN_TAC THEN MATCH_MP_TAC IN_MEASURABLE_BOREL_INDICATOR THEN
  Q.EXISTS_TAC `s INTER A i` THEN ASM_SIMP_TAC std_ss [] THEN
  MATCH_MP_TAC ALGEBRA_INTER THEN
  FULL_SIMP_TAC std_ss [sigma_algebra_def, subsets_def] THEN
  METIS_TAC []);

val Radon_Nikodym_finite_measure_infinite = store_thm
  ("Radon_Nikodym_finite_measure_infinite",
 ``!M N. measure_space M /\ measure_space N /\
         finite_measure M /\ measure_absolutely_continuous N M /\
         (measurable_sets M = measurable_sets N) ==>
         ?f. f IN measurable (m_space M,measurable_sets M) Borel /\
              (!x. 0 <= f x) /\
              !A. A IN measurable_sets M ==>
                (pos_fn_integral M (\x. f x * indicator_fn A x) = measure N A)``,
  GEN_TAC THEN GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM (MP_TAC o MATCH_MP split_space_into_finite_sets_and_rest) THEN
  DISCH_THEN (X_CHOOSE_TAC ``Q0:'a->bool``) THEN POP_ASSUM MP_TAC THEN
  DISCH_THEN (X_CHOOSE_TAC ``Q:num->'a->bool``) THEN FULL_SIMP_TAC std_ss [] THEN
  Q_TAC SUFF_TAC `!i. Q i IN measurable_sets M` THENL
  [DISCH_TAC, ASM_SET_TAC []] THEN
  ABBREV_TAC ``NN = (\i:num. (m_space M, measurable_sets M,
    (\A. if A IN measurable_sets M then
      pos_fn_integral N (\x. indicator_fn (Q i) x * indicator_fn A x) else 0)))`` THEN
  ABBREV_TAC ``MM = (\i:num. (m_space M, measurable_sets M,
    (\A. if A IN measurable_sets M then
     pos_fn_integral M (\x. indicator_fn (Q i) x * indicator_fn A x) else 0)))`` THEN
  Q_TAC SUFF_TAC `!i. (?f. f IN measurable (m_space (MM i), measurable_sets (MM i)) Borel /\
    (!x. 0 <= f x) /\ !A. A IN measurable_sets (MM i) ==>
    (pos_fn_integral (MM i) (\x. f x * indicator_fn A x) = measure (NN i) A))` THENL
  [DISCH_TAC,
   GEN_TAC THEN MATCH_MP_TAC Radon_Nikodym_finite_measure THEN
   Q_TAC SUFF_TAC `finite_measure (MM i)` THENL
   [DISCH_TAC THEN ASM_REWRITE_TAC [],
    REWRITE_TAC [finite_measure] THEN EXPAND_TAC "MM" THEN
    SIMP_TAC std_ss [measure_def, m_space_def] THEN
    ASM_SIMP_TAC std_ss [MEASURE_SPACE_MSPACE_MEASURABLE] THEN
    FULL_SIMP_TAC std_ss [finite_measure] THEN CONJ_TAC THENL
    [ALL_TAC,
     SIMP_TAC std_ss [INDICATOR_FN_MUL_INTER] THEN
     `Q i SUBSET m_space M` by METIS_TAC [MEASURE_SPACE_SUBSET_MSPACE] THEN
     ASM_SIMP_TAC std_ss [SET_RULE ``a SUBSET b ==> (a INTER b = a)``] THEN
     REWRITE_TAC [METIS [ETA_AX] ``(\x. indicator_fn (Q i) x) = indicator_fn (Q i)``] THEN
     ASM_SIMP_TAC std_ss [pos_fn_integral_indicator] THEN
     SIMP_TAC std_ss [lt_infty] THEN MATCH_MP_TAC let_trans THEN
     Q.EXISTS_TAC `measure M (m_space M)` THEN ASM_REWRITE_TAC [GSYM lt_infty] THEN
     MATCH_MP_TAC INCREASING THEN ASM_SIMP_TAC std_ss [MEASURE_SPACE_MSPACE_MEASURABLE] THEN
     ASM_SIMP_TAC std_ss [MEASURE_SPACE_INCREASING]] THEN
    FULL_SIMP_TAC std_ss [sigma_finite_measure, measure_def, measurable_sets_def] THEN
    Q.EXISTS_TAC `A` THEN FULL_SIMP_TAC std_ss [m_space_def] THEN GEN_TAC THEN
    DISCH_TAC THEN `a IN measurable_sets N` by ASM_SET_TAC [] THEN ASM_REWRITE_TAC [] THEN
    SIMP_TAC std_ss [INDICATOR_FN_MUL_INTER] THEN
    REWRITE_TAC [METIS [ETA_AX] ``(\x. indicator_fn (Q i) x) = indicator_fn (Q i)``] THEN
    `Q i INTER a IN subsets (m_space M, measurable_sets M)` by
     METIS_TAC [ALGEBRA_INTER, measure_space_def, sigma_algebra_def, subsets_def] THEN
    FULL_SIMP_TAC std_ss [subsets_def, pos_fn_integral_indicator] THEN
    SIMP_TAC std_ss [lt_infty] THEN MATCH_MP_TAC let_trans THEN
    Q.EXISTS_TAC `measure M (m_space M)` THEN ASM_REWRITE_TAC [GSYM lt_infty] THEN
    MATCH_MP_TAC INCREASING THEN ASM_SIMP_TAC std_ss [MEASURE_SPACE_MSPACE_MEASURABLE] THEN
    ASM_SIMP_TAC std_ss [MEASURE_SPACE_INCREASING] THEN
    MATCH_MP_TAC MEASURE_SPACE_SUBSET_MSPACE THEN ASM_REWRITE_TAC []] THEN
   Q_TAC SUFF_TAC `finite_measure (NN i)` THENL
   [DISCH_TAC THEN ASM_REWRITE_TAC [],
    REWRITE_TAC [finite_measure] THEN EXPAND_TAC "NN" THEN
    SIMP_TAC std_ss [measure_def, m_space_def] THEN
    ASM_SIMP_TAC std_ss [MEASURE_SPACE_MSPACE_MEASURABLE] THEN
    FULL_SIMP_TAC std_ss [finite_measure] THEN CONJ_TAC THENL
    [ALL_TAC,
     SIMP_TAC std_ss [INDICATOR_FN_MUL_INTER] THEN
     `Q i SUBSET m_space M` by METIS_TAC [MEASURE_SPACE_SUBSET_MSPACE] THEN
     ASM_SIMP_TAC std_ss [SET_RULE ``a SUBSET b ==> (a INTER b = a)``] THEN
     REWRITE_TAC [METIS [ETA_AX] ``(\x. indicator_fn (Q i) x) = indicator_fn (Q i)``] THEN
     `pos_fn_integral N (indicator_fn (Q i)) = measure N (Q i)`
      by METIS_TAC [pos_fn_integral_indicator] THEN
     ASM_SIMP_TAC std_ss []] THEN
    FULL_SIMP_TAC std_ss [sigma_finite_measure, measure_def, measurable_sets_def] THEN
    Q.EXISTS_TAC `A` THEN FULL_SIMP_TAC std_ss [m_space_def] THEN GEN_TAC THEN
    DISCH_TAC THEN `a IN measurable_sets N` by ASM_SET_TAC [] THEN ASM_REWRITE_TAC [] THEN
    SIMP_TAC std_ss [INDICATOR_FN_MUL_INTER] THEN
    REWRITE_TAC [METIS [ETA_AX] ``(\x. indicator_fn (Q i) x) = indicator_fn (Q i)``] THEN
    `Q i INTER a IN subsets (m_space N, measurable_sets N)` by
     METIS_TAC [ALGEBRA_INTER, measure_space_def, sigma_algebra_def, subsets_def] THEN
    FULL_SIMP_TAC std_ss [subsets_def, pos_fn_integral_indicator] THEN
    SIMP_TAC std_ss [lt_infty] THEN MATCH_MP_TAC let_trans THEN
    Q.EXISTS_TAC `measure N (Q i)` THEN ASM_REWRITE_TAC [GSYM lt_infty] THEN
    MATCH_MP_TAC INCREASING THEN ASM_SIMP_TAC std_ss [MEASURE_SPACE_INCREASING] THEN
    CONJ_TAC THENL [ALL_TAC, METIS_TAC []] THEN SET_TAC []] THEN
   `measurable_sets (MM i) = measurable_sets (NN i)` by METIS_TAC [measurable_sets_def] THEN
   ASM_REWRITE_TAC [] THEN
   Q_TAC SUFF_TAC `measure_absolutely_continuous (NN i) (MM i)` THENL
   [DISCH_TAC THEN ASM_REWRITE_TAC [],
    FULL_SIMP_TAC std_ss [measure_absolutely_continuous_def] THEN
    EXPAND_TAC "MM" THEN EXPAND_TAC "NN" THEN
    SIMP_TAC std_ss [measure_def, measurable_sets_def] THEN
    SIMP_TAC std_ss [INDICATOR_FN_MUL_INTER] THEN
    REWRITE_TAC [METIS [ETA_AX] ``(\x. indicator_fn (Q i) x) = indicator_fn (Q i)``] THEN
    GEN_TAC THEN STRIP_TAC THEN POP_ASSUM MP_TAC THEN
    FIRST_ASSUM (fn th => REWRITE_TAC [th]) THEN
    `Q i INTER A IN subsets (m_space N, measurable_sets N)` by
     METIS_TAC [ALGEBRA_INTER, measure_space_def, sigma_algebra_def, subsets_def] THEN
    FULL_SIMP_TAC std_ss [subsets_def, pos_fn_integral_indicator]] THEN
   FULL_SIMP_TAC std_ss [measure_space_def] THEN
   EXPAND_TAC "MM" THEN EXPAND_TAC "NN" THEN
   ASM_SIMP_TAC std_ss [m_space_def, measurable_sets_def] THEN
   REWRITE_TAC [GSYM CONJ_ASSOC] THEN CONJ_TAC THENL
   [SIMP_TAC std_ss [positive_def, measure_def, measurable_sets_def] THEN
    `{} IN measurable_sets N` by METIS_TAC [measure_space_def, sigma_algebra_iff2] THEN
    ASM_SIMP_TAC std_ss [] THEN CONJ_TAC THENL
    [SIMP_TAC std_ss [indicator_fn_def, NOT_IN_EMPTY, mul_rzero] THEN
     METIS_TAC [pos_fn_integral_zero, measure_space_def], ALL_TAC] THEN
    RW_TAC std_ss [] THEN MATCH_MP_TAC pos_fn_integral_pos THEN
    REWRITE_TAC [INDICATOR_FN_MUL_INTER] THEN ASM_SIMP_TAC std_ss [measure_space_def] THEN
    SIMP_TAC std_ss [indicator_fn_def] THEN GEN_TAC THEN COND_CASES_TAC THEN
    SIMP_TAC real_ss [le_refl, extreal_of_num_def, extreal_le_def],
    ALL_TAC] THEN
   CONJ_TAC THENL
   [SIMP_TAC std_ss [countably_additive_alt_eq, INDICATOR_FN_MUL_INTER] THEN
    REPEAT STRIP_TAC THEN SIMP_TAC std_ss [o_DEF] THEN
    `!x. A x IN measurable_sets N` by ASM_SET_TAC [] THEN
    ASM_SIMP_TAC std_ss [INTER_BIGUNION, GSPECIFICATION, IN_UNIV] THEN
    REWRITE_TAC [SET_RULE ``{Q i INTER x | ?i'. x = A i'} = {Q i INTER A i' | i' IN UNIV}``] THEN
    SIMP_TAC std_ss [GSYM IMAGE_DEF] THEN
    Q_TAC SUFF_TAC `!x. indicator_fn (BIGUNION (IMAGE (\i'. Q i INTER A i') univ(:num))) x =
      suminf (\j. indicator_fn ((\i'. Q i INTER A i') j) x)` THENL
    [DISCH_TAC THEN ASM_SIMP_TAC std_ss [],
     GEN_TAC THEN ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN MATCH_MP_TAC indicator_fn_suminf THEN
     FULL_SIMP_TAC std_ss [disjoint_family, disjoint_family_on, DISJOINT_DEF] THEN
     ASM_SET_TAC []] THEN ONCE_REWRITE_TAC [METIS [ETA_AX]
      ``(\x'. indicator_fn (Q i INTER A x) x') = (\x. indicator_fn (Q i INTER A x)) x``] THEN
    ONCE_REWRITE_TAC [METIS [] ``suminf (\j. indicator_fn (Q i INTER A j) x) =
                          suminf (\j. (\k. indicator_fn (Q i INTER A k)) j x)``] THEN
    MATCH_MP_TAC pos_fn_integral_suminf THEN ASM_SIMP_TAC std_ss [measure_space_def] THEN
    CONJ_TAC THENL
    [SIMP_TAC std_ss [indicator_fn_def] THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN
     SIMP_TAC real_ss [le_refl, extreal_of_num_def, extreal_le_def], ALL_TAC] THEN
    GEN_TAC THEN MATCH_MP_TAC IN_MEASURABLE_BOREL_INDICATOR THEN
    Q.EXISTS_TAC `Q i INTER A i'` THEN ASM_SIMP_TAC std_ss [] THEN
    MATCH_MP_TAC ALGEBRA_INTER THEN
    FULL_SIMP_TAC std_ss [sigma_algebra_def, subsets_def] THEN
    METIS_TAC [], ALL_TAC] THEN
   CONJ_TAC THENL
   [SIMP_TAC std_ss [positive_def, measure_def, measurable_sets_def] THEN
    `{} IN measurable_sets N` by METIS_TAC [measure_space_def, sigma_algebra_iff2] THEN
    ASM_SIMP_TAC std_ss [] THEN CONJ_TAC THENL
    [SIMP_TAC std_ss [indicator_fn_def, NOT_IN_EMPTY, mul_rzero] THEN
     METIS_TAC [pos_fn_integral_zero, measure_space_def], ALL_TAC] THEN
    RW_TAC std_ss [] THEN MATCH_MP_TAC pos_fn_integral_pos THEN
    REWRITE_TAC [INDICATOR_FN_MUL_INTER] THEN ASM_SIMP_TAC std_ss [measure_space_def] THEN
    SIMP_TAC std_ss [indicator_fn_def] THEN GEN_TAC THEN COND_CASES_TAC THEN
    SIMP_TAC real_ss [le_refl, extreal_of_num_def, extreal_le_def],
    ALL_TAC] THEN
   SIMP_TAC std_ss [countably_additive_alt_eq, INDICATOR_FN_MUL_INTER] THEN
   REPEAT STRIP_TAC THEN SIMP_TAC std_ss [o_DEF] THEN
    `!x. A x IN measurable_sets N` by ASM_SET_TAC [] THEN
   ASM_SIMP_TAC std_ss [INTER_BIGUNION, GSPECIFICATION, IN_UNIV] THEN
   REWRITE_TAC [SET_RULE ``{Q i INTER x | ?i'. x = A i'} = {Q i INTER A i' | i' IN UNIV}``] THEN
   SIMP_TAC std_ss [GSYM IMAGE_DEF] THEN
   Q_TAC SUFF_TAC `!x. indicator_fn (BIGUNION (IMAGE (\i'. Q i INTER A i') univ(:num))) x =
           suminf (\j. indicator_fn ((\i'. Q i INTER A i') j) x)` THENL
   [DISCH_TAC THEN ASM_SIMP_TAC std_ss [],
    GEN_TAC THEN ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN MATCH_MP_TAC indicator_fn_suminf THEN
    FULL_SIMP_TAC std_ss [disjoint_family, disjoint_family_on, DISJOINT_DEF] THEN
    ASM_SET_TAC []] THEN ONCE_REWRITE_TAC [METIS [ETA_AX]
     ``(\x'. indicator_fn (Q i INTER A x) x') = (\x. indicator_fn (Q i INTER A x)) x``] THEN
   ONCE_REWRITE_TAC [METIS [] ``suminf (\j. indicator_fn (Q i INTER A j) x) =
                           suminf (\j. (\k. indicator_fn (Q i INTER A k)) j x)``] THEN
   MATCH_MP_TAC pos_fn_integral_suminf THEN ASM_SIMP_TAC std_ss [measure_space_def] THEN
   CONJ_TAC THENL
   [SIMP_TAC std_ss [indicator_fn_def] THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN
    SIMP_TAC real_ss [le_refl, extreal_of_num_def, extreal_le_def], ALL_TAC] THEN
   GEN_TAC THEN MATCH_MP_TAC IN_MEASURABLE_BOREL_INDICATOR THEN
   Q.EXISTS_TAC `Q i INTER A i'` THEN ASM_SIMP_TAC std_ss [] THEN
   MATCH_MP_TAC ALGEBRA_INTER THEN
   FULL_SIMP_TAC std_ss [sigma_algebra_def, subsets_def] THEN
   METIS_TAC []] THEN
  Q_TAC SUFF_TAC `?f. (!i. f i IN measurable (m_space (MM i), measurable_sets (MM i)) Borel) /\
                      (!i x. 0 <= f i x) /\ !i A. A IN measurable_sets (MM i) ==>
                      (pos_fn_integral (MM i) (\x. (f i) x * indicator_fn A x) = measure (NN i) A)` THENL
  [STRIP_TAC, METIS_TAC []] THEN
  ABBREV_TAC ``ff = (\x. suminf (\i. f i x * indicator_fn (Q i) x) + PosInf * indicator_fn (Q0) x)`` THEN
  Q_TAC SUFF_TAC `ff IN measurable (m_space M,measurable_sets M) Borel` THENL
  [DISCH_TAC,
   Q_TAC SUFF_TAC `ff = (\x. if x IN Q0 then (\x. PosInf) x
                           else (\x. suminf (\i. f i x * indicator_fn (Q i) x)) x)` THENL
   [DISCH_TAC,
    EXPAND_TAC "ff" THEN SIMP_TAC std_ss [FUN_EQ_THM] THEN GEN_TAC THEN
    COND_CASES_TAC THENL
    [POP_ASSUM (fn th => SIMP_TAC std_ss [indicator_fn_def, th, mul_rone]) THEN
     Q_TAC SUFF_TAC `!x. 0 <= x ==> (x + PosInf = PosInf)` THENL
     [DISCH_THEN (MATCH_MP_TAC) THEN SIMP_TAC std_ss [ext_suminf_def, le_sup] THEN
      GEN_TAC THEN DISCH_THEN (MATCH_MP_TAC) THEN ONCE_REWRITE_TAC [GSYM SPECIFICATION] THEN
      SIMP_TAC std_ss [GSPECIFICATION, IN_IMAGE, IN_UNIV] THEN Q.EXISTS_TAC `0` THEN
      SIMP_TAC std_ss [count_def, GSPEC_F, EXTREAL_SUM_IMAGE_EMPTY],
      ALL_TAC] THEN
     GEN_TAC THEN DISCH_TAC THEN
     `x <> NegInf` by METIS_TAC [lt_infty, lte_trans, num_not_infty] THEN
     ASM_CASES_TAC ``x = PosInf`` THENL [METIS_TAC [extreal_add_def], ALL_TAC] THEN
     METIS_TAC [extreal_cases, extreal_add_def], ALL_TAC] THEN
    POP_ASSUM (fn th => SIMP_TAC std_ss [indicator_fn_def, th, mul_rzero]) THEN
    SIMP_TAC std_ss [add_rzero]] THEN
   ONCE_REWRITE_TAC [METIS [SPACE, m_space_def, measurable_sets_def]
    ``Borel = (m_space (space Borel, subsets Borel, (\x. 0)),
       measurable_sets (space Borel, subsets Borel, (\x. 0)))``] THEN
   FIRST_X_ASSUM (ASSUME_TAC o ONCE_REWRITE_RULE [SPECIFICATION]) THEN
   POP_ASSUM (fn th => ONCE_REWRITE_TAC [th]) THEN
   ONCE_REWRITE_TAC [METIS [] ``PosInf = (\x. PosInf) x``] THEN
   MATCH_MP_TAC measurable_If THEN REPEAT CONJ_TAC THENL
   [SIMP_TAC std_ss [SPACE, m_space_def, measurable_sets_def] THEN
    MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST THEN Q.EXISTS_TAC `PosInf` THEN
    METIS_TAC [measure_space_def],
    ALL_TAC,
    ONCE_REWRITE_TAC [prove (``{x | x IN m_space M /\ Q0 x} = {x | x IN m_space M /\ x IN Q0}``,
     SIMP_TAC std_ss [SPECIFICATION])] THEN SIMP_TAC std_ss [GSYM INTER_DEF] THEN
    ONCE_REWRITE_TAC [METIS [subsets_def]
     ``measurable_sets M = subsets (m_space M, measurable_sets M)``] THEN
    MATCH_MP_TAC ALGEBRA_INTER THEN SIMP_TAC std_ss [subsets_def] THEN
    CONJ_TAC THENL [METIS_TAC [measure_space_def, sigma_algebra_def], ALL_TAC] THEN
    METIS_TAC [MEASURE_SPACE_MSPACE_MEASURABLE],
    ASM_REWRITE_TAC []] THEN
   SIMP_TAC std_ss [SPACE, m_space_def, measurable_sets_def, ext_suminf_def] THEN
   Q_TAC SUFF_TAC `!x. (\n. SIGMA (\i. f i x * indicator_fn (Q i) x) (count n)) =
                       (\n. (\n x. SIGMA (\i. f i x * indicator_fn (Q i) x) (count n)) n x)` THENL
   [DISC_RW_KILL, METIS_TAC []] THEN MATCH_MP_TAC IN_MEASURABLE_BOREL_MONO_SUP THEN
   Q.EXISTS_TAC `(\n x. SIGMA (\i. f i x * indicator_fn (Q i) x) (count n))` THEN
   SIMP_TAC std_ss [] THEN CONJ_TAC THENL [METIS_TAC [measure_space_def], ALL_TAC] THEN
   CONJ_TAC THENL
   [ALL_TAC,
    GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC EXTREAL_SUM_IMAGE_MONO_SET THEN
    SIMP_TAC std_ss [FINITE_COUNT, count_def] THEN
    SIMP_TAC arith_ss [SUBSET_DEF, GSPECIFICATION] THEN GEN_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC le_mul THEN ASM_SIMP_TAC std_ss [indicator_fn_def] THEN COND_CASES_TAC THEN
    SIMP_TAC std_ss [le_refl] THEN SIMP_TAC real_ss [extreal_of_num_def, extreal_le_def]] THEN
   GEN_TAC THEN
   MP_TAC (ISPECL [``(m_space (M:('a->bool)#(('a->bool)->bool)#(('a->bool)->extreal)),
                      measurable_sets M)``,
                   ``(\i x.  (f:num->'a->extreal) i x * indicator_fn (Q i) x)``,
                   ``(\x. SIGMA (\i. (f:num->'a->extreal) i x * indicator_fn (Q i) x) (count n))``,
                   ``count n``] IN_MEASURABLE_BOREL_SUM) THEN
   ASM_REWRITE_TAC [] THEN DISCH_THEN (MATCH_MP_TAC) THEN
   SIMP_TAC std_ss [FINITE_COUNT] THEN CONJ_TAC THENL [METIS_TAC [measure_space_def], ALL_TAC] THEN
   CONJ_TAC THENL
   [ALL_TAC,
    REPEAT GEN_TAC THEN STRIP_TAC THEN SIMP_TAC std_ss [lt_infty] THEN
    MATCH_MP_TAC lte_trans THEN Q.EXISTS_TAC `0` THEN
    SIMP_TAC std_ss [GSYM lt_infty, num_not_infty] THEN
    MATCH_MP_TAC le_mul THEN ASM_SIMP_TAC std_ss [indicator_fn_def] THEN
    COND_CASES_TAC THEN SIMP_TAC real_ss [le_refl, extreal_of_num_def, extreal_le_def]] THEN
   GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC IN_MEASURABLE_BOREL_MUL_INDICATOR THEN
   METIS_TAC [subsets_def, measure_space_def, m_space_def, measurable_sets_def]] THEN
  Q_TAC SUFF_TAC `!x. 0 <= ff x` THENL
  [DISCH_TAC,
   EXPAND_TAC "ff" THEN GEN_TAC THEN
   ASM_CASES_TAC ``(x:'a) IN Q0`` THENL
   [POP_ASSUM (fn th => SIMP_TAC std_ss [indicator_fn_def, th, mul_rone]) THEN
    Q_TAC SUFF_TAC `suminf (\i. f i x * if x IN Q i then 1 else 0) + PosInf = PosInf` THENL
    [METIS_TAC [le_infty], ALL_TAC] THEN
    Q_TAC SUFF_TAC `!x. 0 <= x ==> (x + PosInf = PosInf)` THENL
    [DISCH_THEN (MATCH_MP_TAC) THEN SIMP_TAC std_ss [ext_suminf_def, le_sup] THEN
     GEN_TAC THEN DISCH_THEN (MATCH_MP_TAC) THEN ONCE_REWRITE_TAC [GSYM SPECIFICATION] THEN
     SIMP_TAC std_ss [GSPECIFICATION, IN_IMAGE, IN_UNIV] THEN Q.EXISTS_TAC `0` THEN
     SIMP_TAC std_ss [count_def, GSPEC_F, EXTREAL_SUM_IMAGE_EMPTY],
     ALL_TAC] THEN
    GEN_TAC THEN DISCH_TAC THEN
    `x <> NegInf` by METIS_TAC [lt_infty, lte_trans, num_not_infty] THEN
    ASM_CASES_TAC ``x = PosInf`` THENL [METIS_TAC [extreal_add_def], ALL_TAC] THEN
    METIS_TAC [extreal_cases, extreal_add_def], ALL_TAC] THEN
   POP_ASSUM (fn th => SIMP_TAC std_ss [indicator_fn_def, th, mul_rzero]) THEN
   SIMP_TAC std_ss [add_rzero] THEN
   GEN_REWR_TAC LAND_CONV [GSYM suminf_0] THEN MATCH_MP_TAC ext_suminf_mono THEN
   SIMP_TAC std_ss [num_not_infty] THEN GEN_TAC THEN MATCH_MP_TAC le_mul THEN
   ASM_SIMP_TAC std_ss [] THEN COND_CASES_TAC THEN
   SIMP_TAC real_ss [le_refl, extreal_of_num_def, extreal_le_def]] THEN
  Q.EXISTS_TAC `ff` THEN ASM_SIMP_TAC std_ss [] THEN
  CONJ_TAC THENL [METIS_TAC [], ALL_TAC] THEN GEN_TAC THEN DISCH_TAC THEN
  ASM_CASES_TAC ``m_space M = {}`` THENL
  [`m_space M = m_space N` by METIS_TAC [sets_eq_imp_space_eq] THEN
   `A SUBSET m_space M` by METIS_TAC [MEASURE_SPACE_SUBSET_MSPACE] THEN
   `positive N` by METIS_TAC [MEASURE_SPACE_POSITIVE] THEN
   `A = {}` by ASM_SET_TAC [] THEN FULL_SIMP_TAC std_ss [positive_def] THEN
   SIMP_TAC std_ss [indicator_fn_def, NOT_IN_EMPTY, mul_rzero] THEN
   METIS_TAC [pos_fn_integral_zero],
   ALL_TAC] THEN
  Q_TAC SUFF_TAC `(!i. (\x. f i x * indicator_fn (Q i INTER A) x) IN
                     measurable (m_space M, measurable_sets M) Borel) /\
                  (!i. ?x. x IN m_space M /\ 0 <= f i x * indicator_fn (Q i INTER A) x)` THENL
  [STRIP_TAC,
   CONJ_TAC THENL
   [ALL_TAC,
    GEN_TAC THEN FULL_SIMP_TAC std_ss [GSYM MEMBER_NOT_EMPTY] THEN
    Q.EXISTS_TAC `x` THEN ASM_SIMP_TAC std_ss [] THEN
    MATCH_MP_TAC le_mul THEN ASM_SIMP_TAC std_ss [indicator_fn_def] THEN
    COND_CASES_TAC THEN SIMP_TAC real_ss [le_refl, extreal_of_num_def, extreal_le_def]] THEN
   GEN_TAC THEN MATCH_MP_TAC IN_MEASURABLE_BOREL_MUL_INDICATOR THEN
   CONJ_TAC THENL [METIS_TAC [measure_space_def], ALL_TAC] THEN
   CONJ_TAC THENL [METIS_TAC [m_space_def, measurable_sets_def], ALL_TAC] THEN
   MATCH_MP_TAC ALGEBRA_INTER THEN CONJ_TAC THENL
   [ALL_TAC, METIS_TAC [subsets_def]] THEN
   METIS_TAC [measure_space_def, sigma_algebra_def]] THEN
  Q_TAC SUFF_TAC `pos_fn_integral M (\x. ff x * indicator_fn A x) =
                  pos_fn_integral M (\x. suminf (\i. f i x * indicator_fn (Q i INTER A) x) +
                   PosInf * indicator_fn (Q0 INTER A) x)` THENL
  [DISCH_TAC,
   EXPAND_TAC  "ff" THEN
   Q_TAC SUFF_TAC `!x. 0 <= suminf (\i. f i x * indicator_fn (Q i) x)` THENL
   [DISCH_TAC,
    GEN_TAC THEN GEN_REWR_TAC LAND_CONV [GSYM suminf_0] THEN
    MATCH_MP_TAC ext_suminf_mono THEN SIMP_TAC std_ss [num_not_infty] THEN
    GEN_TAC THEN MATCH_MP_TAC le_mul THEN ASM_SIMP_TAC std_ss [indicator_fn_def] THEN
    COND_CASES_TAC THEN SIMP_TAC real_ss [le_refl, extreal_of_num_def, extreal_le_def]] THEN
   Q_TAC SUFF_TAC `!x. 0 <= PosInf * indicator_fn Q0 x` THENL
   [DISCH_TAC, GEN_TAC THEN
    MATCH_MP_TAC le_mul THEN SIMP_TAC std_ss [le_infty, indicator_fn_def] THEN
    COND_CASES_TAC THEN SIMP_TAC real_ss [le_refl, extreal_of_num_def, extreal_le_def]] THEN
   `!x. (suminf (\i. f i x * indicator_fn (Q i) x) +
        PosInf * indicator_fn Q0 x) * indicator_fn A x =
        (suminf (\i. f i x * indicator_fn (Q i) x) * indicator_fn A x) +
        ((PosInf * indicator_fn Q0 x) * indicator_fn A x)` by METIS_TAC [add_rdistrib] THEN
   POP_ASSUM (fn th => REWRITE_TAC [th]) THEN REWRITE_TAC [GSYM mul_assoc] THEN
   ONCE_REWRITE_TAC [METIS [INDICATOR_FN_MUL_INTER]
    ``indicator_fn Q0 x * indicator_fn A x = indicator_fn (Q0 INTER A) x``] THEN
   Q_TAC SUFF_TAC `!x. suminf (\i. f i x * indicator_fn (Q i) x) * indicator_fn A x =
                       suminf (\i. f i x * indicator_fn (Q i INTER A) x)` THENL
   [DISCH_TAC THEN ASM_SIMP_TAC std_ss [], ALL_TAC] THEN
   GEN_TAC THEN
   ONCE_REWRITE_TAC [METIS [INDICATOR_FN_MUL_INTER]
    ``indicator_fn (Q i INTER A) x = indicator_fn (Q i) x * indicator_fn A x``] THEN
   ASM_CASES_TAC ``(x:'a) IN A`` THEN ASM_SIMP_TAC std_ss [indicator_fn_def, mul_rone, mul_rzero] THEN
   SIMP_TAC std_ss [suminf_0]] THEN
  Q_TAC SUFF_TAC `pos_fn_integral M (\x. suminf (\i. f i x * indicator_fn (Q i INTER A) x) +
                   PosInf * indicator_fn (Q0 INTER A) x) =
                  pos_fn_integral M (\x. suminf (\i. f i x * indicator_fn (Q i INTER A) x)) +
                   PosInf * measure M (Q0 INTER A)` THENL
  [DISCH_TAC,
   Q_TAC SUFF_TAC `pos_fn_integral M (\x. (\x. suminf (\i. f i x * indicator_fn (Q i INTER A) x)) x +
                                          (\x. PosInf * indicator_fn (Q0 INTER A) x) x) =
                   pos_fn_integral M (\x. suminf (\i. f i x * indicator_fn (Q i INTER A) x)) +
                   pos_fn_integral M (\x. PosInf * indicator_fn (Q0 INTER A) x)` THENL
   [SIMP_TAC std_ss [] THEN DISCH_TAC THEN POP_ASSUM (fn th => REWRITE_TAC [th]),
    MATCH_MP_TAC pos_fn_integral_add THEN SIMP_TAC std_ss [] THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN
    Q_TAC SUFF_TAC `!x. 0 <= suminf (\i. f i x * indicator_fn (Q i INTER A) x)` THENL
    [DISCH_TAC,
     GEN_TAC THEN GEN_REWR_TAC LAND_CONV [GSYM suminf_0] THEN
     MATCH_MP_TAC ext_suminf_mono THEN SIMP_TAC std_ss [num_not_infty] THEN
     GEN_TAC THEN MATCH_MP_TAC le_mul THEN ASM_SIMP_TAC std_ss [indicator_fn_def] THEN
     COND_CASES_TAC THEN SIMP_TAC real_ss [le_refl, extreal_of_num_def, extreal_le_def]] THEN
    Q_TAC SUFF_TAC `!x. 0 <= PosInf * indicator_fn (Q0 INTER A) x` THENL
    [DISCH_TAC, GEN_TAC THEN
     MATCH_MP_TAC le_mul THEN SIMP_TAC std_ss [le_infty, indicator_fn_def] THEN
     COND_CASES_TAC THEN SIMP_TAC real_ss [le_refl, extreal_of_num_def, extreal_le_def]] THEN
    CONJ_TAC THENL [METIS_TAC [], ALL_TAC] THEN
    CONJ_TAC THENL
    [SIMP_TAC std_ss [ext_suminf_def] THEN
     Q_TAC SUFF_TAC `!x. (\n. SIGMA (\i. f i x * indicator_fn (Q i INTER A) x) (count n)) =
                         (\n. (\n x. SIGMA (\i. f i x * indicator_fn (Q i INTER A) x) (count n)) n x)` THENL
     [DISC_RW_KILL, METIS_TAC []] THEN MATCH_MP_TAC IN_MEASURABLE_BOREL_MONO_SUP THEN
     Q.EXISTS_TAC `(\n x. SIGMA (\i. f i x * indicator_fn (Q i INTER A) x) (count n))` THEN
     SIMP_TAC std_ss [] THEN CONJ_TAC THENL [METIS_TAC [measure_space_def], ALL_TAC] THEN
     CONJ_TAC THENL
     [ALL_TAC,
      GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC EXTREAL_SUM_IMAGE_MONO_SET THEN
      SIMP_TAC std_ss [FINITE_COUNT, count_def] THEN
      SIMP_TAC arith_ss [SUBSET_DEF, GSPECIFICATION] THEN GEN_TAC THEN DISCH_TAC THEN
      MATCH_MP_TAC le_mul THEN ASM_SIMP_TAC std_ss [indicator_fn_def] THEN COND_CASES_TAC THEN
      SIMP_TAC std_ss [le_refl] THEN SIMP_TAC real_ss [extreal_of_num_def, extreal_le_def]] THEN
      GEN_TAC THEN
      MP_TAC (ISPECL [``(m_space (M:('a->bool)#(('a->bool)->bool)#(('a->bool)->extreal)),
                         measurable_sets M)``,
                      ``(\i x.  (f:num->'a->extreal) i x * indicator_fn (Q i INTER A) x)``,
                      ``(\x. SIGMA (\i. (f:num->'a->extreal) i x * indicator_fn (Q i INTER A) x) (count n))``,
                      ``count n``] IN_MEASURABLE_BOREL_SUM) THEN
      ASM_REWRITE_TAC [] THEN DISCH_THEN (MATCH_MP_TAC) THEN
      SIMP_TAC std_ss [FINITE_COUNT] THEN CONJ_TAC THENL [METIS_TAC [measure_space_def], ALL_TAC] THEN
      CONJ_TAC THENL
      [ALL_TAC,
       REPEAT GEN_TAC THEN STRIP_TAC THEN SIMP_TAC std_ss [lt_infty] THEN
       MATCH_MP_TAC lte_trans THEN Q.EXISTS_TAC `0` THEN
       SIMP_TAC std_ss [GSYM lt_infty, num_not_infty] THEN
       MATCH_MP_TAC le_mul THEN ASM_SIMP_TAC std_ss [indicator_fn_def] THEN
       COND_CASES_TAC THEN SIMP_TAC real_ss [le_refl, extreal_of_num_def, extreal_le_def]] THEN
      GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC IN_MEASURABLE_BOREL_MUL_INDICATOR THEN
      METIS_TAC [subsets_def, measure_space_def, m_space_def, measurable_sets_def,
                 ALGEBRA_INTER, sigma_algebra_def], ALL_TAC] THEN
    ONCE_REWRITE_TAC [METIS [] ``(\x. PosInf * indicator_fn (Q0 INTER A) x) =
                                 (\x. (\x. PosInf) x * indicator_fn (Q0 INTER A) x)``] THEN
    MATCH_MP_TAC IN_MEASURABLE_BOREL_MUL_INDICATOR THEN
    CONJ_TAC THENL [METIS_TAC [measure_space_def], ALL_TAC] THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST THEN Q.EXISTS_TAC `PosInf` THEN
     METIS_TAC [measure_space_def], ALL_TAC] THEN
    METIS_TAC [ALGEBRA_INTER, measure_space_def, sigma_algebra_def, subsets_def]] THEN

   MATCH_MP_TAC (METIS [] ``(b = c) ==> (a + b = a + c)``) THEN
   MATCH_MP_TAC pos_fn_integral_cmul_infty THEN
   CONJ_TAC THENL [METIS_TAC [], ALL_TAC] THEN
   ONCE_REWRITE_TAC [METIS [subsets_def]
    ``measurable_sets M = subsets (m_space M, measurable_sets M)``] THEN
   METIS_TAC [measure_space_def, sigma_algebra_def, ALGEBRA_INTER, subsets_def]] THEN
  Q_TAC SUFF_TAC `!A i. A IN measurable_sets M ==>
    (pos_fn_integral M (\x. f i x * indicator_fn (Q i INTER A) x) =
     measure (m_space (MM i), measurable_sets (MM i),
       (\A. if A IN measurable_sets (MM i) then
        pos_fn_integral (MM i) (\x. f i x * indicator_fn A x) else 0)) A)` THENL
  [DISCH_TAC,
   GEN_TAC THEN GEN_TAC THEN SIMP_TAC std_ss [measure_def] THEN
   `measurable_sets (MM i) = measurable_sets M` by METIS_TAC [measurable_sets_def] THEN
   POP_ASSUM (fn th => REWRITE_TAC [th]) THEN DISCH_TAC THEN
   FIRST_ASSUM (fn th => REWRITE_TAC [th]) THEN
   Q_TAC SUFF_TAC `pos_fn_integral (MM i) (\x. f i x * indicator_fn A' x) =
                   pos_fn_integral M (\x. indicator_fn (Q i) x * (\x. f i x * indicator_fn A' x) x)` THENL
   [ALL_TAC, EXPAND_TAC "MM" THEN
    ONCE_REWRITE_TAC [METIS [] ``(\x. indicator_fn (Q i) x * (f i x * indicator_fn A' x)) =
                             (\x. indicator_fn (Q i) x * (\x. f i x * indicator_fn A' x) x)``] THEN
    Q_TAC SUFF_TAC `pos_fn_integral
     (m_space M,measurable_sets M,
      (\A. if A IN measurable_sets M then
            pos_fn_integral M (\x. max 0 (indicator_fn (Q i) x * indicator_fn A x))
           else 0)) (\x. max 0 ((\x. f i x * indicator_fn A' x) x)) =
                    pos_fn_integral M
      (\x. max 0 (indicator_fn (Q i) x * (\x. f i x * indicator_fn A' x) x))` THENL
    [ASM_SIMP_TAC std_ss [extreal_max_def, indicator_fn_pos_le, le_mul], ALL_TAC] THEN
    MATCH_MP_TAC pos_fn_integral_density' THEN ASM_SIMP_TAC std_ss [] THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC IN_MEASURABLE_BOREL_INDICATOR THEN Q.EXISTS_TAC `Q i` THEN
     ASM_SIMP_TAC std_ss [] THEN METIS_TAC [measure_space_def, subsets_def],
     ALL_TAC] THEN
    CONJ_TAC THENL
    [SIMP_TAC std_ss [AE, ae_filter, GSPECIFICATION, null_sets] THEN
     SIMP_TAC std_ss [SUBSET_DEF, GSPECIFICATION] THEN Q.EXISTS_TAC `{}` THEN
     FULL_SIMP_TAC std_ss [measure_space_def, sigma_algebra_iff2] THEN
     FULL_SIMP_TAC std_ss [positive_def, NOT_IN_EMPTY] THEN
     GEN_TAC THEN DISJ2_TAC THEN
     SIMP_TAC std_ss [indicator_fn_def] THEN COND_CASES_TAC THEN
     SIMP_TAC real_ss [le_refl, extreal_of_num_def, extreal_le_def],
     ALL_TAC] THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC IN_MEASURABLE_BOREL_MUL_INDICATOR THEN
     METIS_TAC [measure_space_def, subsets_def, m_space_def, measurable_sets_def],
     ALL_TAC] THEN
    SIMP_TAC std_ss [] THEN GEN_TAC THEN MATCH_MP_TAC le_mul THEN
    ASM_SIMP_TAC std_ss [indicator_fn_def] THEN COND_CASES_TAC THEN
    SIMP_TAC real_ss [le_refl, extreal_of_num_def, extreal_le_def]] THEN
   DISC_RW_KILL THEN SIMP_TAC std_ss [mul_assoc] THEN
   ONCE_REWRITE_TAC [mul_comm] THEN SIMP_TAC std_ss [mul_assoc] THEN
   ONCE_REWRITE_TAC [METIS [INDICATOR_FN_MUL_INTER]
    ``indicator_fn A' x * indicator_fn (Q i) x = indicator_fn (A' INTER Q i) x``] THEN
   METIS_TAC [INTER_COMM]] THEN
  Q_TAC SUFF_TAC `!i. measure (m_space (MM i),measurable_sets (MM i),
                  (\A. if A IN measurable_sets (MM i) then
                       pos_fn_integral (MM i)
                         (\x. f i x * indicator_fn A x)
                     else 0)) A = measure N (Q i INTER A)` THENL
  [DISCH_TAC,
   GEN_TAC THEN Q_TAC SUFF_TAC `measure N (Q i INTER A) =
    measure (m_space N,measurable_sets N,
     (\s. if s IN measurable_sets N then
          pos_fn_integral N (\x. indicator_fn (Q i) x * indicator_fn s x)
          else 0)) A` THENL
   [DISC_RW_KILL,
    MATCH_MP_TAC (GSYM measure_restricted) THEN METIS_TAC []] THEN
   SIMP_TAC std_ss [measure_def] THEN
   `measurable_sets (MM i) = measurable_sets (N)` by METIS_TAC [measurable_sets_def] THEN
   ASM_SIMP_TAC std_ss [] THEN EXPAND_TAC "NN" THEN SIMP_TAC std_ss [measure_def] THEN
   ASM_SIMP_TAC std_ss []] THEN
  Q_TAC SUFF_TAC `!i. measure N (Q i INTER A) =
   pos_fn_integral M (\x. f i x * indicator_fn (Q i INTER A) x)` THENL
  [DISCH_TAC, METIS_TAC []] THEN
  Q_TAC SUFF_TAC `pos_fn_integral M (\x. suminf (\i. f i x * indicator_fn (Q i INTER A) x)) +
                   PosInf * measure M (Q0 INTER A) =
                  suminf (\i. measure N (Q i INTER A)) + PosInf * measure M (Q0 INTER A)` THENL
  [DISCH_TAC,
   MATCH_MP_TAC (METIS [] ``(b = c) ==> (b + a = c + a)``) THEN
   Q_TAC SUFF_TAC `pos_fn_integral M (\x. suminf (\i. (\i x. f i x * indicator_fn (Q i INTER A) x) i x)) =
                    suminf (\i. pos_fn_integral M ((\i x. f i x * indicator_fn (Q i INTER A) x) i))` THENL
   [SIMP_TAC std_ss [] THEN DISC_RW_KILL,
    MATCH_MP_TAC pos_fn_integral_suminf THEN ASM_SIMP_TAC std_ss [] THEN
    CONJ_TAC THENL
    [GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC le_mul THEN
     ASM_SIMP_TAC std_ss [indicator_fn_def] THEN COND_CASES_TAC THEN
     SIMP_TAC real_ss [le_refl, extreal_of_num_def, extreal_le_def],
     ALL_TAC] THEN METIS_TAC []] THEN METIS_TAC []] THEN
  Q_TAC SUFF_TAC `suminf (\i. measure N (Q i INTER A)) =
       measure N (BIGUNION {Q i | i IN UNIV} INTER A)` THENL
  [DISCH_TAC,
   SIMP_TAC std_ss [INTER_BIGUNION, GSPECIFICATION, IN_UNIV] THEN
   ONCE_REWRITE_TAC [SET_RULE ``BIGUNION {x INTER A | ?i. x = Q i} =
                                BIGUNION {Q i INTER A | i IN UNIV}``] THEN
   ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
   `countably_additive N` by METIS_TAC [measure_space_def] THEN
   POP_ASSUM MP_TAC THEN SIMP_TAC std_ss [countably_additive_def] THEN
   SIMP_TAC std_ss [GSYM IMAGE_DEF] THEN
   DISCH_THEN (MP_TAC o Q.SPEC `(\i. Q i INTER A)`) THEN
   SIMP_TAC std_ss [o_DEF] THEN DISCH_THEN (MATCH_MP_TAC) THEN
   CONJ_TAC THENL
   [EVAL_TAC THEN ASM_SIMP_TAC std_ss [IN_DEF,IN_FUNSET] THEN SRW_TAC[][] THEN
     ONCE_REWRITE_TAC [GSYM SPECIFICATION] THEN
    METIS_TAC [ALGEBRA_INTER, subsets_def, measure_space_def, sigma_algebra_def],
    ALL_TAC] THEN
   CONJ_TAC THENL
   [ASM_SET_TAC [DISJOINT_DEF, disjoint_family, disjoint_family_on], ALL_TAC] THEN
   ONCE_REWRITE_TAC [METIS [subsets_def] ``measurbale_sets M =
                       subsets (m_space M, measurbale_sets M)``] THEN
   MATCH_MP_TAC SIGMA_ALGEBRA_COUNTABLE_UNION THEN
   CONJ_TAC THENL [METIS_TAC [measure_space_def], ALL_TAC] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC image_countable THEN
    SIMP_TAC std_ss [pred_setTheory.COUNTABLE_NUM], ALL_TAC] THEN
   ASM_SIMP_TAC std_ss [SUBSET_DEF, IN_IMAGE] THEN GEN_TAC THEN
   METIS_TAC [ALGEBRA_INTER, measure_space_def, sigma_algebra_def, subsets_def]] THEN
  Q_TAC SUFF_TAC `PosInf * measure M (Q0 INTER A) = measure N (Q0 INTER A)` THENL
  [DISCH_TAC,
   UNDISCH_TAC ``!A.
        A IN measurable_sets M /\ A SUBSET Q0 ==>
        (measure M A = 0) /\ (measure N A = 0) \/
        0 < measure M A /\ (measure N A = PosInf)`` THEN
   DISCH_THEN (MP_TAC o Q.SPEC `Q0 INTER A`) THEN
   `Q0 INTER A SUBSET Q0` by SET_TAC [] THEN
   `Q0 INTER A IN measurable_sets M` by
    METIS_TAC [ALGEBRA_INTER, subsets_def, measure_space_def, sigma_algebra_def] THEN
   POP_ASSUM (fn th => REWRITE_TAC [th]) THEN POP_ASSUM (fn th => REWRITE_TAC [th]) THEN
   STRIP_TAC THEN ASM_SIMP_TAC std_ss [mul_rzero] THEN
   Q_TAC SUFF_TAC `(m_space M DIFF BIGUNION {Q i | i IN univ(:num)}) INTER A
     IN measurable_sets M` THENL
   [DISCH_TAC,
    ONCE_REWRITE_TAC [METIS [subsets_def]
     ``measurable_sets M = subsets (m_space M, measurable_sets M)``] THEN
    MATCH_MP_TAC ALGEBRA_INTER THEN
    CONJ_TAC THENL [METIS_TAC [measure_space_def, sigma_algebra_def], ALL_TAC] THEN
    CONJ_TAC THENL [ALL_TAC, ASM_SIMP_TAC std_ss [subsets_def]] THEN
    MATCH_MP_TAC ALGEBRA_DIFF THEN
    CONJ_TAC THENL [METIS_TAC [measure_space_def, sigma_algebra_def], ALL_TAC] THEN
    CONJ_TAC THENL [METIS_TAC [subsets_def, MEASURE_SPACE_MSPACE_MEASURABLE], ALL_TAC] THEN
    MATCH_MP_TAC SIGMA_ALGEBRA_COUNTABLE_UNION THEN
    CONJ_TAC THENL [METIS_TAC [measure_space_def], ALL_TAC] THEN
    CONJ_TAC THENL
    [SIMP_TAC std_ss [GSYM IMAGE_DEF] THEN
     MATCH_MP_TAC image_countable THEN
     SIMP_TAC std_ss [pred_setTheory.COUNTABLE_NUM], ALL_TAC] THEN
    ASM_SIMP_TAC std_ss [SUBSET_DEF, GSPECIFICATION, IN_UNIV] THEN GEN_TAC THEN
    METIS_TAC [subsets_def]] THEN
   `!A. A IN measurable_sets M ==> 0 <= measure M A`
     by METIS_TAC [measure_space_def, positive_def] THEN
   POP_ASSUM (MP_TAC o Q.SPEC `(m_space M DIFF BIGUNION {Q i | i IN univ(:num)}) INTER A`) THEN
   ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
   Q_TAC SUFF_TAC `0 < measure M ((m_space M DIFF BIGUNION {Q i | i IN univ(:num)}) INTER A)` THENL
   [DISCH_TAC,
    MATCH_MP_TAC lte_trans THEN Q.EXISTS_TAC `measure M (Q0 INTER A)` THEN
    ASM_SIMP_TAC std_ss [le_refl]] THEN
   `measure M ((m_space M DIFF BIGUNION {Q i | i IN univ(:num)}) INTER A) <> NegInf` by
     METIS_TAC [lte_trans, lt_infty, num_not_infty] THEN
   ASM_CASES_TAC ``measure M ((m_space M DIFF BIGUNION {Q i | i IN univ(:num)}) INTER A) = PosInf`` THENL
   [ASM_SIMP_TAC std_ss [extreal_mul_def], ALL_TAC] THEN
   `?r. measure M ((m_space M DIFF BIGUNION {Q i | i IN univ(:num)}) INTER A) = Normal r` by
     METIS_TAC [extreal_cases] THEN FULL_SIMP_TAC std_ss [] THEN
   SIMP_TAC std_ss [extreal_mul_def] THEN
   `0 < r` by METIS_TAC [extreal_lt_eq, extreal_of_num_def] THEN
   METIS_TAC [REAL_LT_IMP_NE]] THEN
  Q_TAC SUFF_TAC `Q0 INTER A IN measurable_sets M /\
                  (BIGUNION {Q i | i IN UNIV} INTER A) IN measurable_sets M` THENL
  [DISCH_TAC,
   CONJ_TAC THENL
   [METIS_TAC [ALGEBRA_INTER, subsets_def, measure_space_def, sigma_algebra_def],
    ALL_TAC] THEN
   ONCE_REWRITE_TAC [METIS [subsets_def] ``measurbale_sets M =
                       subsets (m_space M, measurbale_sets M)``] THEN
   MATCH_MP_TAC ALGEBRA_INTER THEN CONJ_TAC THENL
   [METIS_TAC [measure_space_def, sigma_algebra_def], ALL_TAC] THEN
   CONJ_TAC THENL [ALL_TAC, METIS_TAC [subsets_def]] THEN
   MATCH_MP_TAC SIGMA_ALGEBRA_COUNTABLE_UNION THEN
   CONJ_TAC THENL [METIS_TAC [measure_space_def], ALL_TAC] THEN
   CONJ_TAC THENL
   [SIMP_TAC std_ss [GSYM IMAGE_DEF] THEN
    MATCH_MP_TAC image_countable THEN
    SIMP_TAC std_ss [pred_setTheory.COUNTABLE_NUM], ALL_TAC] THEN
   ASM_SIMP_TAC std_ss [SUBSET_DEF, GSPECIFICATION, IN_UNIV] THEN GEN_TAC THEN
   METIS_TAC [subsets_def]] THEN
  Q_TAC SUFF_TAC `((BIGUNION {Q i | i IN UNIV} INTER A) UNION (Q0 INTER A) = A) /\
                  ((BIGUNION {Q i | i IN UNIV} INTER A) INTER (Q0 INTER A) = {})` THENL
  [DISCH_TAC,
   CONJ_TAC THENL [ALL_TAC, ASM_SET_TAC [disjoint_family, disjoint_family_on]] THEN
   UNDISCH_TAC ``Q0 = m_space M DIFF BIGUNION {Q i | i IN univ(:num)}`` THEN
   UNDISCH_TAC ``disjoint_family (Q:num->'a->bool)`` THEN
   SIMP_TAC std_ss [disjoint_family, disjoint_family_on, IN_UNIV] THEN
   FULL_SIMP_TAC std_ss [measure_space_def, sigma_algebra_iff2, POW_DEF] THEN
   ASM_SET_TAC []] THEN
  ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC ADDITIVE THEN
  CONJ_TAC THENL [METIS_TAC [MEASURE_SPACE_ADDITIVE], ALL_TAC] THEN
  CONJ_TAC THENL [METIS_TAC [], ALL_TAC] THEN
  CONJ_TAC THENL [METIS_TAC [], ALL_TAC] THEN ASM_SET_TAC [DISJOINT_DEF]);

val add_pow02 = store_thm ("add_pow02",
 ``!x y. 0 < x /\ x <> PosInf /\ 0 <= y ==>
        ((x + y) pow 2 = x pow 2 + y pow 2 + 2 * x * y)``,
  RW_TAC std_ss [] THEN
  `x <> NegInf` by METIS_TAC [lt_trans, lt_infty, num_not_infty] THEN
  `y <> NegInf` by METIS_TAC [lte_trans, lt_infty, num_not_infty] THEN
  ASM_CASES_TAC ``y = PosInf`` THENL [ALL_TAC, METIS_TAC [add_pow2]] THEN
  ASM_SIMP_TAC std_ss [] THEN
  `x = Normal (real x)` by METIS_TAC [normal_real] THEN
  ONCE_ASM_REWRITE_TAC [] THEN
  SIMP_TAC std_ss [extreal_add_def, extreal_mul_def, extreal_of_num_def] THEN
  Q_TAC SUFF_TAC `PosInf pow 2 = PosInf` THENL
  [DISCH_TAC, REWRITE_TAC [pow_2, extreal_mul_def]] THEN
  ONCE_ASM_REWRITE_TAC [] THEN REPEAT COND_CASES_TAC THEN
  ASM_SIMP_TAC std_ss [extreal_pow_def, extreal_add_def] THEN
  POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC [MONO_NOT_EQ] THEN
  RW_TAC std_ss [real_normal, REAL_MUL_POS_LT] THEN DISJ1_TAC THEN
  ASM_SIMP_TAC real_ss [GSYM extreal_lt_eq, normal_real, GSYM extreal_of_num_def]);

val mul2_zero = store_thm ("mul2_zero",
   ``!a b. (a * b = 0) = (a = 0) \/  (b = 0)``,
   RW_TAC std_ss [] THEN EQ_TAC THENL
   [ALL_TAC, METIS_TAC [mul_lzero, mul_rzero]] THEN
   ONCE_REWRITE_TAC [MONO_NOT_EQ] THEN RW_TAC std_ss [] THEN
   ASM_CASES_TAC ``a = PosInf`` THEN ASM_CASES_TAC ``b = PosInf`` THENL
   [ASM_SIMP_TAC std_ss [extreal_mul_def, num_not_infty],
    ASM_CASES_TAC ``b = NegInf`` THEN
    ASM_SIMP_TAC std_ss [extreal_mul_def, num_not_infty] THEN
    `b = Normal (real b)` by METIS_TAC [normal_real] THEN
    ONCE_ASM_REWRITE_TAC [] THEN SIMP_TAC std_ss [extreal_mul_def] THEN
    ASM_SIMP_TAC std_ss [GSYM extreal_11, normal_real, GSYM extreal_of_num_def] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC std_ss [num_not_infty],
    ASM_CASES_TAC ``a = NegInf`` THEN
    ASM_SIMP_TAC std_ss [extreal_mul_def, num_not_infty] THEN
    `a = Normal (real a)` by METIS_TAC [normal_real] THEN
    ONCE_ASM_REWRITE_TAC [] THEN SIMP_TAC std_ss [extreal_mul_def] THEN
    ASM_SIMP_TAC std_ss [GSYM extreal_11, normal_real, GSYM extreal_of_num_def] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC std_ss [num_not_infty],
    ALL_TAC] THEN
   ASM_CASES_TAC ``a = NegInf`` THEN ASM_CASES_TAC ``b = NegInf`` THENL
   [ASM_SIMP_TAC std_ss [extreal_mul_def, num_not_infty],
    `b = Normal (real b)` by METIS_TAC [normal_real] THEN
    ONCE_ASM_REWRITE_TAC [] THEN SIMP_TAC std_ss [extreal_mul_def] THEN
    ASM_SIMP_TAC std_ss [GSYM extreal_11, normal_real, GSYM extreal_of_num_def] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC std_ss [num_not_infty],
    `a = Normal (real a)` by METIS_TAC [normal_real] THEN
    ONCE_ASM_REWRITE_TAC [] THEN SIMP_TAC std_ss [extreal_mul_def] THEN
    ASM_SIMP_TAC std_ss [GSYM extreal_11, normal_real, GSYM extreal_of_num_def] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC std_ss [num_not_infty],
    ALL_TAC] THEN
   `a = Normal (real a)` by METIS_TAC [normal_real] THEN
   `b = Normal (real b)` by METIS_TAC [normal_real] THEN
   ONCE_ASM_REWRITE_TAC [] THEN
   ASM_SIMP_TAC real_ss [extreal_mul_def, extreal_of_num_def, extreal_11] THEN
   `real a <> 0` by METIS_TAC [extreal_11, extreal_of_num_def] THEN
   `real b <> 0` by METIS_TAC [extreal_11, extreal_of_num_def] THEN
   METIS_TAC [REAL_ENTIRE]);

val countable_sing = store_thm ("countable_sing",
  ``!x. countable {x}``,
  RW_TAC std_ss [pred_setTheory.COUNTABLE_ALT, IN_SING] THEN
  Q.EXISTS_TAC `(\n. x)` THEN METIS_TAC []);

val IN_MEASURABLE_BOREL_EQ = store_thm ("IN_MEASURABLE_BOREL_EQ",
 ``!f g M. (!x. x IN m_space M ==> (f x = g x)) /\
      g IN measurable (m_space M,measurable_sets M) Borel ==>
      f IN measurable (m_space M,measurable_sets M) Borel``,
  RW_TAC std_ss [] THEN FULL_SIMP_TAC std_ss [IN_MEASURABLE_BOREL] THEN
  CONJ_TAC THENL
  [EVAL_TAC THEN SRW_TAC[] [IN_DEF, space_def,IN_FUNSET], ALL_TAC] THEN
  GEN_TAC THEN POP_ASSUM (MP_TAC o Q.SPEC `c`) THEN
  MATCH_MP_TAC EQ_IMPLIES THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  ASM_SET_TAC [space_def]);


val RADON_NIKODYM = store_thm ("RADON_NIKODYM",
  ``!M N. sigma_finite_measure M /\
          measure_space M /\ measure_space N /\
          measure_absolutely_continuous N M /\
          (measurable_sets M = measurable_sets N) ==>
      ?f. f IN measurable (m_space M,measurable_sets M) Borel /\
           (!x. 0 <= f x) /\
           !A. A IN measurable_sets M ==>
             (pos_fn_integral M (\x. f x * indicator_fn A x) = measure N A)``,
  REPEAT STRIP_TAC THEN
  `{PosInf} IN subsets Borel` by METIS_TAC [BOREL_MEASURABLE_INFINITY] THEN
  `?h. h IN measurable (m_space M,measurable_sets M) Borel /\
       pos_fn_integral M h <> PosInf /\
       (!x. x IN m_space M ==> 0 < h x /\ h x < PosInf) /\ !x. 0 <= h x`
     by METIS_TAC [Ex_finite_integrable_function] THEN
  ABBREV_TAC ``t = (\A. pos_fn_integral M (\x. h x * indicator_fn A x))`` THEN
  ABBREV_TAC ``mt = (m_space M, measurable_sets M, (\A. if A IN measurable_sets M
    then pos_fn_integral M (\x. h x * indicator_fn A x) else 0))`` THEN
  Q_TAC SUFF_TAC `finite_measure mt` THENL
  [DISCH_TAC,
   SIMP_TAC std_ss [finite_measure] THEN EXPAND_TAC "mt" THEN
   SIMP_TAC std_ss [measure_def, m_space_def] THEN
   ASM_SIMP_TAC std_ss [MEASURE_SPACE_MSPACE_MEASURABLE] THEN
   CONJ_TAC THENL
   [ALL_TAC,
    Q_TAC SUFF_TAC `pos_fn_integral M (\x. h x * indicator_fn (m_space M) x) =
                    pos_fn_integral M h` THENL
    [METIS_TAC [], ALL_TAC] THEN
    MATCH_MP_TAC (GSYM pos_fn_integral_mspace) THEN ASM_SIMP_TAC std_ss []] THEN
   ASM_SIMP_TAC std_ss [sigma_finite_measure] THEN Q.EXISTS_TAC `{m_space mt}` THEN
   SIMP_TAC std_ss [countable_sing, BIGUNION_SING] THEN
   CONJ_TAC THENL
   [SIMP_TAC std_ss [SUBSET_DEF, IN_SING] THEN
    `m_space mt = m_space M` by METIS_TAC [m_space_def] THEN
    `measurable_sets mt = measurable_sets M` by METIS_TAC [measurable_sets_def] THEN
    METIS_TAC [MEASURE_SPACE_MSPACE_MEASURABLE],
    ALL_TAC] THEN
   GEN_TAC THEN SIMP_TAC std_ss [IN_SING] THEN DISCH_TAC THEN ASM_REWRITE_TAC [] THEN
   EXPAND_TAC "mt" THEN SIMP_TAC std_ss [measure_def, m_space_def] THEN
   ASM_SIMP_TAC std_ss [MEASURE_SPACE_MSPACE_MEASURABLE] THEN
   Q_TAC SUFF_TAC `pos_fn_integral M (\x. h x * indicator_fn (m_space M) x) =
                   pos_fn_integral M h` THENL
   [METIS_TAC [], ALL_TAC] THEN
   MATCH_MP_TAC (GSYM pos_fn_integral_mspace) THEN ASM_SIMP_TAC std_ss []] THEN
  Q_TAC SUFF_TAC `measure_space mt` THENL
  [DISCH_TAC,
   EXPAND_TAC "mt" THEN
   FULL_SIMP_TAC std_ss [measure_space_def, m_space_def, measurable_sets_def] THEN
   CONJ_TAC THENL
   [EXPAND_TAC "mt" THEN
    SIMP_TAC std_ss [positive_def, measure_def, measurable_sets_def] THEN
    SIMP_TAC std_ss [indicator_fn_def, NOT_IN_EMPTY, mul_rzero] THEN
    ASM_SIMP_TAC std_ss [pos_fn_integral_zero, measure_space_def] THEN
    GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC pos_fn_integral_pos THEN
    ASM_SIMP_TAC std_ss [measure_space_def] THEN GEN_TAC THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC real_ss [le_refl, mul_rone, mul_rzero], ALL_TAC] THEN
   EXPAND_TAC "mt" THEN SIMP_TAC std_ss [countably_additive_alt_eq] THEN
   REPEAT STRIP_TAC THEN SIMP_TAC std_ss [o_DEF] THEN
   `!x. A x IN measurable_sets M` by ASM_SET_TAC [] THEN
   ASM_SIMP_TAC std_ss [GSYM IMAGE_DEF] THEN
   Q_TAC SUFF_TAC `!x. indicator_fn (BIGUNION (IMAGE A univ(:num))) x =
    suminf (\j. indicator_fn (A j) x)` THENL
   [DISCH_TAC THEN ASM_SIMP_TAC std_ss [],
    GEN_TAC THEN ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN MATCH_MP_TAC indicator_fn_suminf THEN
    FULL_SIMP_TAC std_ss [disjoint_family, disjoint_family_on, DISJOINT_DEF] THEN
    ASM_SET_TAC []] THEN
   Q_TAC SUFF_TAC `!x. h x * suminf (\j. indicator_fn (A j) x) =
                       suminf (\j. h x * (\j. indicator_fn (A j) x) j)` THENL
   [DISC_RW_KILL,
    GEN_TAC THEN MATCH_MP_TAC (GSYM ext_suminf_cmul) THEN
    ASM_SIMP_TAC std_ss [indicator_fn_def] THEN GEN_TAC THEN COND_CASES_TAC THEN
    SIMP_TAC real_ss [le_refl, extreal_of_num_def, extreal_le_def]] THEN
   SIMP_TAC std_ss [] THEN
   ONCE_REWRITE_TAC [METIS [] ``(\x'. h x' * indicator_fn (A x) x') =
                           (\x. (\x'. h x' * indicator_fn (A x) x')) x``] THEN
   ONCE_REWRITE_TAC [METIS [] ``suminf (\j. h x * indicator_fn (A j) x) =
                                suminf (\j. (\x x'. h x' * indicator_fn (A x) x') j x)``] THEN
   MATCH_MP_TAC pos_fn_integral_suminf THEN ASM_SIMP_TAC std_ss [measure_space_def] THEN
   CONJ_TAC THENL
   [SIMP_TAC std_ss [indicator_fn_def] THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC real_ss [le_refl, mul_rone, mul_rzero], ALL_TAC] THEN
   GEN_TAC THEN MATCH_MP_TAC IN_MEASURABLE_BOREL_MUL_INDICATOR THEN
   METIS_TAC [subsets_def, measurable_sets_def]] THEN
  ASM_CASES_TAC ``m_space M = {}`` THENL
  [Q_TAC SUFF_TAC `measurable_sets M = {{}}` THENL
   [DISCH_TAC,
    FULL_SIMP_TAC std_ss [measure_space_def, sigma_algebra_iff2, POW_DEF] THEN
    FULL_SIMP_TAC std_ss [SUBSET_EMPTY] THEN
    UNDISCH_TAC ``measurable_sets N SUBSET {s:'a->bool | s = {}}`` THEN
    SIMP_TAC std_ss [SUBSET_DEF, GSPECIFICATION, EXTENSION, IN_SING] THEN
    SIMP_TAC std_ss [NOT_IN_EMPTY] THEN
    ONCE_REWRITE_TAC [SET_RULE ``(!x'. x' NOTIN x) = (x = {})``] THEN
    DISCH_TAC THEN GEN_TAC THEN POP_ASSUM (MP_TAC o Q.SPEC `x`) THEN
    STRIP_TAC THEN EQ_TAC THENL [ASM_SET_TAC [], METIS_TAC []]] THEN
   Q.EXISTS_TAC `(\x. 0)` THEN ASM_SIMP_TAC std_ss [le_refl, IN_SING] THEN
   FULL_SIMP_TAC std_ss [mul_lzero, measure_space_def, positive_def] THEN
   CONJ_TAC THENL [ALL_TAC, MATCH_MP_TAC pos_fn_integral_zero THEN
    METIS_TAC [measure_space_def, positive_def]] THEN
   SIMP_TAC std_ss [IN_MEASURABLE_BOREL] THEN ASM_SIMP_TAC std_ss [] THEN
   ASM_SIMP_TAC std_ss [space_def, INTER_EMPTY, subsets_def] THEN
   CONJ_TAC THENL [EVAL_TAC THEN SRW_TAC[][IN_DEF,IN_FUNSET], ALL_TAC] THEN
   METIS_TAC [IN_SING], ALL_TAC] THEN
  Q_TAC SUFF_TAC `measure_absolutely_continuous N mt /\
   (measurable_sets N = measurable_sets mt)` THENL
  [STRIP_TAC THEN
   `?f. f IN measurable (m_space mt,measurable_sets mt) Borel /\
      (!x. 0 <= f x) /\
      !A. A IN measurable_sets mt ==>
       (pos_fn_integral mt (\x. f x * indicator_fn A x) = measure N A)`
    by METIS_TAC [Radon_Nikodym_finite_measure_infinite] THEN
   Q_TAC SUFF_TAC `!A. A IN measurable_sets mt ==>
    (pos_fn_integral mt (\x. f x * indicator_fn A x) =
     pos_fn_integral M (\x. h x * (\x. f x * indicator_fn A x) x))` THENL
   [DISCH_TAC,
    GEN_TAC THEN DISCH_TAC THEN EXPAND_TAC "mt" THEN
    ONCE_REWRITE_TAC [METIS [] ``pos_fn_integral M (\x. h x * (f x * indicator_fn A x)) =
                             pos_fn_integral M (\x. h x * (\x. f x * indicator_fn A x) x)``] THEN
    Q_TAC SUFF_TAC `pos_fn_integral
     (m_space M,measurable_sets M,
      (\A. if A IN measurable_sets M then
            pos_fn_integral M (\x. max 0 (h x * indicator_fn A x))
           else 0)) (\x. max 0 ((\x. f x * indicator_fn A x) x)) =
     pos_fn_integral M (\x. max 0 (h x * (\x. f x * indicator_fn A x) x))` THENL
    [ASM_SIMP_TAC std_ss [extreal_max_def, le_mul, indicator_fn_pos_le] THEN
     METIS_TAC [], ALL_TAC] THEN
    MATCH_MP_TAC pos_fn_integral_density' THEN ASM_SIMP_TAC std_ss [] THEN
    CONJ_TAC THENL
    [SIMP_TAC std_ss [AE, ae_filter, GSPECIFICATION, null_sets, GSPEC_T] THEN
     Q.EXISTS_TAC `{}` THEN SIMP_TAC std_ss [IN_UNIV, GSPEC_F, SUBSET_REFL] THEN
     METIS_TAC [measure_space_def, sigma_algebra_iff2, positive_def],
     ALL_TAC] THEN
    CONJ_TAC THENL [ALL_TAC, GEN_TAC THEN MATCH_MP_TAC le_mul THEN
     ASM_SIMP_TAC std_ss [indicator_fn_def] THEN COND_CASES_TAC THEN
     ASM_SIMP_TAC real_ss [le_refl, extreal_of_num_def, extreal_le_def]] THEN
    MATCH_MP_TAC IN_MEASURABLE_BOREL_MUL_INDICATOR THEN
    METIS_TAC [subsets_def, measure_space_def, measurable_sets_def, m_space_def]] THEN
   Q.EXISTS_TAC `(\x. h x * f x)` THEN `m_space mt = m_space M` by METIS_TAC [m_space_def] THEN
   `measurable_sets mt = measurable_sets M` by METIS_TAC [measurable_sets_def] THEN
   CONJ_TAC THENL
   [ALL_TAC,
    CONJ_TAC THENL
    [GEN_TAC THEN SIMP_TAC std_ss [] THEN MATCH_MP_TAC le_mul THEN METIS_TAC [],
     ALL_TAC] THEN
    GEN_TAC THEN DISCH_TAC THEN FULL_SIMP_TAC std_ss [mul_assoc]] THEN
   MATCH_MP_TAC IN_MEASURABLE_BOREL_EQ THEN
   Q.EXISTS_TAC `(\x. if x IN {x | f x NOTIN {PosInf}}
                    then ((\x. h x * Normal(real(f x))) x) else PosInf)` THEN
   CONJ_TAC THENL
   [GEN_TAC THEN STRIP_TAC THEN SIMP_TAC std_ss [GSPECIFICATION, IN_SING] THEN
    `h x <> NegInf` by METIS_TAC [lt_infty, num_not_infty, lte_trans] THEN
    `f x <> NegInf` by METIS_TAC [lt_infty, num_not_infty, lte_trans] THEN
    `h x <> PosInf` by METIS_TAC [lt_infty] THEN
    `h x = Normal (real (h x))` by METIS_TAC [normal_real] THEN
    `h x <> 0` by METIS_TAC [lt_imp_ne] THEN COND_CASES_TAC THENL
    [ALL_TAC, FULL_SIMP_TAC std_ss [] THEN
     ONCE_ASM_REWRITE_TAC [] THEN SIMP_TAC std_ss [extreal_mul_def] THEN
     `real (h x) <> 0` by METIS_TAC [extreal_11, extreal_of_num_def, normal_real] THEN
     `0 < real (h x)` by METIS_TAC [extreal_lt_eq, normal_real, extreal_of_num_def] THEN
     ASM_SIMP_TAC std_ss []] THEN
    METIS_TAC [normal_real], ALL_TAC] THEN
   ONCE_REWRITE_TAC [METIS [SPECIFICATION]
    ``x IN {x | f x NOTIN {PosInf}} = {x | f x NOTIN {PosInf}} x``] THEN
   ONCE_REWRITE_TAC [METIS [SPACE, m_space_def, measurable_sets_def]
    ``Borel = (m_space (space Borel, subsets Borel, (\x. 0)),
       measurable_sets (space Borel, subsets Borel, (\x. 0)))``] THEN
   ONCE_REWRITE_TAC [METIS [] ``PosInf = (\x. PosInf) x``] THEN
   MATCH_MP_TAC measurable_If THEN REPEAT CONJ_TAC THENL
   [SIMP_TAC std_ss [m_space_def, measurable_sets_def, SPACE] THEN
    MATCH_MP_TAC IN_MEASURABLE_BOREL_MUL THEN Q.EXISTS_TAC `h` THEN
    Q.EXISTS_TAC `(\x. Normal (real (f x)))` THEN
    FULL_SIMP_TAC std_ss [measure_space_def] THEN CONJ_TAC THENL
    [METIS_TAC [lt_infty, lte_trans, num_not_infty, space_def],
     ALL_TAC] THEN
    Q_TAC SUFF_TAC `(\x. Normal (real (f x))) =
     (\x. if x IN {x | f x = PosInf} then (\x. 0) x else f x)` THENL
    [ALL_TAC,
     ABS_TAC THEN SIMP_TAC std_ss [GSPECIFICATION] THEN COND_CASES_TAC THENL
     [ASM_REWRITE_TAC [] THEN METIS_TAC [real_def, extreal_of_num_def],
      ALL_TAC] THEN
     `f x <> NegInf` by METIS_TAC [lte_trans, num_not_infty, lt_infty] THEN
     METIS_TAC [normal_real]] THEN
    DISC_RW_KILL THEN ONCE_REWRITE_TAC [METIS [SPECIFICATION]
     ``!x. x IN {x | f x = PosInf} = {x | f x = PosInf} x``] THEN
    ONCE_REWRITE_TAC [METIS [SPACE, m_space_def, measurable_sets_def]
     ``Borel = (m_space (space Borel, subsets Borel, (\x. 0)),
        measurable_sets (space Borel, subsets Borel, (\x. 0)))``] THEN
    ONCE_REWRITE_TAC [METIS [] ``0 = (\x. 0) x``] THEN
    MATCH_MP_TAC measurable_If THEN
    ASM_SIMP_TAC std_ss [m_space_def, measurable_sets_def, SPACE] THEN
    REPEAT CONJ_TAC THENL
    [MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST THEN Q.EXISTS_TAC `0` THEN
     METIS_TAC [], ALL_TAC, METIS_TAC [measure_space_def]] THEN
    Q_TAC SUFF_TAC `{x | x IN m_space M /\ {x | f x = PosInf} x} =
                    PREIMAGE f {PosInf} INTER m_space M` THENL
    [DISC_RW_KILL THEN
     FULL_SIMP_TAC std_ss [IN_MEASURABLE, space_def, subsets_def], (* assumption used*)
     ALL_TAC] THEN
    SIMP_TAC std_ss [PREIMAGE_def, INTER_DEF] THEN
    SIMP_TAC std_ss [EXTENSION, GSPECIFICATION] THEN GEN_TAC THEN
    GEN_REWR_TAC (LAND_CONV o RAND_CONV) [GSYM SPECIFICATION] THEN
    SET_TAC [],
    SIMP_TAC std_ss [m_space_def, measurable_sets_def, SPACE] THEN
    MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST THEN Q.EXISTS_TAC `PosInf` THEN
    METIS_TAC [measure_space_def],
    ALL_TAC, ASM_REWRITE_TAC []] THEN
   FULL_SIMP_TAC std_ss [IN_MEASURABLE, space_def, subsets_def] THEN
   Q_TAC SUFF_TAC `{x | x IN m_space M /\ {x | f x NOTIN {PosInf}} x} =
                  m_space M INTER {x | f x NOTIN {PosInf}}` THENL
   [ALL_TAC,
    SIMP_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER] THEN GEN_TAC THEN
    GEN_REWR_TAC (LAND_CONV o RAND_CONV) [GSYM SPECIFICATION] THEN
    SET_TAC []] THEN
   DISC_RW_KILL THEN ONCE_REWRITE_TAC [INTER_COMM] THEN
   ONCE_REWRITE_TAC [SET_RULE ``{x | f x NOTIN {PosInf}} = {x | f x IN {x | x <> PosInf}}``] THEN
   SIMP_TAC std_ss [GSYM PREIMAGE_def] THEN FIRST_ASSUM MATCH_MP_TAC THEN
   ONCE_REWRITE_TAC [SET_RULE ``{x | x <> PosInf} = UNIV DIFF {PosInf}``] THEN
   MATCH_MP_TAC ALGEBRA_DIFF THEN
   ASM_SIMP_TAC std_ss [SIGMA_ALGEBRA_BOREL, SIGMA_ALGEBRA_ALGEBRA] THEN
   SIMP_TAC std_ss [GSYM SPACE_BOREL] THEN MATCH_MP_TAC ALGEBRA_SPACE THEN
   SIMP_TAC std_ss [SIGMA_ALGEBRA_BOREL, SIGMA_ALGEBRA_ALGEBRA],
   ALL_TAC] THEN
  CONJ_TAC THENL [ALL_TAC, METIS_TAC [measurable_sets_def]] THEN
   FULL_SIMP_TAC std_ss [measure_absolutely_continuous_def] THEN
   REPEAT STRIP_TAC THEN
   `measurable_sets mt = measurable_sets N`
     by METIS_TAC [measurable_sets_def] THEN FULL_SIMP_TAC std_ss [] THEN
   Q_TAC SUFF_TAC `A IN null_sets mt ==>
    (A IN measurable_sets M /\ AE M {x | x IN A ==> h x <= 0})` THENL
   [ASM_SIMP_TAC std_ss [null_sets, GSPECIFICATION] THEN DISCH_TAC THEN
    Q_TAC SUFF_TAC `AE M {x | x NOTIN A}` THENL
    [ALL_TAC,
     FULL_SIMP_TAC std_ss [AE, ae_filter, GSPECIFICATION] THEN
     Q.EXISTS_TAC `N'` THEN FULL_SIMP_TAC std_ss [SUBSET_DEF, GSPECIFICATION] THEN
     GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
     ASM_SIMP_TAC std_ss [GSYM extreal_lt_def]] THEN
    DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC std_ss [] THEN
    POP_ASSUM MP_TAC THEN SIMP_TAC std_ss [AE, ae_filter, GSPECIFICATION] THEN
    SIMP_TAC std_ss [null_sets, SUBSET_DEF, GSPECIFICATION] THEN
    REPEAT STRIP_TAC THEN
    Q_TAC SUFF_TAC `measure M A <= measure M N'` THENL
    [DISCH_TAC THEN ONCE_REWRITE_TAC [GSYM le_antisym] THEN
     METIS_TAC [measure_space_def, positive_def], ALL_TAC] THEN
    MATCH_MP_TAC INCREASING THEN ASM_SIMP_TAC std_ss [MEASURE_SPACE_INCREASING] THEN
    `A SUBSET m_space M` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
    ASM_SET_TAC [], ALL_TAC] THEN
   DISCH_TAC THEN ASM_SIMP_TAC std_ss [GSYM null_sets_density_iff]);

val _ = export_theory();
