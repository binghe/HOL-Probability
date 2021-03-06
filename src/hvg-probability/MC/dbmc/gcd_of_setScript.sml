(* ================================ *)
(*         GCD_OF_SET Theorems      *)
(* ================================ *)

(*val () = app load ["bossLib", "metisLib", "arithmeticTheory", "pred_setTheory", "realLib", 
 	"pairTheory", "combinTheory", "seqTheory", "listTheory", "transcTheory", "numLib", 
 	"prim_recTheory", "integerTheory", "extra_pred_setTools", "integerSumTheory",
 	"gcdTheory", "setUsefulTheory"];
val () = quietdec := true;

set_trace "Unicode" 0;*)


open HolKernel Parse boolLib bossLib metisLib numLib extra_boolTheory combinTheory
     pred_setTheory arithmeticTheory realTheory realLib pairTheory combinTheory
     extra_pred_setTheory extra_pred_setTools gcdTheory subtypeTheory seqTheory 
     listTheory transcTheory prim_recTheory integerTheory dividesTheory 
     integerSumTheory setUsefulTheory;
	  
(*
val () = quietdec := false;
*)

(* ------------------------------------------------------------------------- *)
(* Start a new theory called "gcd_of_set"                                       *)
(* ------------------------------------------------------------------------- *)

val _ = new_theory "gcd_of_set";

(* ------------------------------------------------------------------------- *)
(* Helpful proof tools                                                       *)
(* ------------------------------------------------------------------------- *)
infixr 0 ++ << || ORELSEC ## --> THENC;
infix 1 >> |->;

val !! = REPEAT;
val op++ = op THEN;
val op<< = op THENL;
val op|| = op ORELSE;
val op>> = op THEN1;

val INTER_ASSOC = GSYM INTER_ASSOC;
val UNION_ASSOC = GSYM UNION_ASSOC;

(* ------------------------------------------------------------------------- *)
(* Some important definitions                                                  *)
(* ------------------------------------------------------------------------- *)
val gcd_set_def = Define `
    gcd_set A = {(r:num)| !x. x IN A ==> divides r x}`;

val GCD_OF_SET_def = Define `
    GCD_OF_SET A = MAX_SET (gcd_set A)`;

val BB_def = Define `
    (BB (0:num) (s:num -> bool) = {MIN_SET s}) /\
    (BB (SUC n) s = (BB n s) UNION 
	(if ({x | x IN (s DIFF (BB n s)) /\
		GCD_OF_SET ((BB n s) UNION {x}) <> GCD_OF_SET (BB n s)} = {}) then {}
	else {r | r = MIN_SET {x | x IN (s DIFF (BB n s)) /\
		GCD_OF_SET ((BB n s) UNION {x}) <> GCD_OF_SET (BB n s)}}))`;

val POS_PART1_def = Define `
    POS_PART1 (i:num) (n:num -> int) = if 0 <= n i then n i else 0`;

val POS_PART2_def = Define `
    POS_PART2 (i:num) (n:num -> int) = if n i < 0 then -(n i) else 0`;

val EXISTS_FUN_EQ_SET = prove
  (``!t. t <> {} /\ FINITE t ==> ?f. !i. i < CARD t ==> f i IN t``,
    RW_TAC std_ss [] ++ Q.EXISTS_TAC `(\i. @x. x IN t)` ++ RW_TAC std_ss []
 ++ SELECT_ELIM_TAC ++ METIS_TAC [CHOICE_DEF]);

val FINITE_SET_EQ_IMAGE_FUN_COUNT = prove
  (``!t. FINITE (t:num -> bool) ==> ?f. (IMAGE (\i. f i) (count (CARD t)) = t)``,
    RW_TAC std_ss []
 ++ `?f. t = {f n | n < CARD t}` by METIS_TAC [FINITE_ISO_NUM]
 ++ Cases_on `t = {}` >> PSET_TAC [CARD_DEF, COUNT_ZERO, IMAGE_EMPTY]
 ++ `{f n | n < CARD t} = IMAGE (\i. (f:num -> num) i) (count (CARD t))`
             by PSET_TAC [GSPECIFICATION, EXTENSION]
 ++ Q.EXISTS_TAC `(f:num -> num)` ++  RW_TAC std_ss []
 ++ FULL_SIMP_TAC std_ss []
             
 ++ FULL_SIMP_TAC std_ss []
 ++ `countable t` by METIS_TAC [FINITE_COUNTABLE] 
 ++ FULL_SIMP_TAC std_ss [countable_def]
 ++ `?(f:num -> num). !i. i < CARD (t:num -> bool) ==> f i IN t`
             by FULL_SIMP_TAC std_ss [EXISTS_FUN_EQ_SET]);

(****************************************)
val FINITE_BB = prove (
  ``!n s. (!x. x IN s ==> 0 < x) /\ s <> {}==> FINITE (BB n s)``,
       INDUCT_TAC
 >> RW_TAC std_ss [BB_def, FINITE_SING] 
 ++ RW_TAC std_ss [BB_def] >> PSET_TAC [UNION_EMPTY]
 ++ PSET_TAC [GSPEC_EQ]
 ++ RW_TAC std_ss [GSYM INSERT_EQ_UNION_SING]
 ++ METIS_TAC [GSYM FINITE_INSERT]);

val SUBSET_BB = prove (
  ``!n s. (!x. x IN s ==> 0 < x) /\ s <> {} ==> 
	(BB n s) SUBSET (BB (n + 1) s)``,
    RW_TAC std_ss [BB_def] 
 ++ `n + 1 = SUC n` by RW_TAC arith_ss [] ++ POP_ORW
 ++ RW_TAC std_ss [BB_def] >> RW_TAC std_ss [UNION_EMPTY, SUBSET_REFL]
 ++ RW_TAC std_ss [GSPEC_EQ, SUBSET_UNION]);

val NON_EMPTY_BB = prove (
  ``!n s. (!x. x IN s ==> 0 < x) /\ s <> {}==> (BB n s) <> {}``,
    INDUCT_TAC
 >> (RW_TAC std_ss [BB_def] ++ `MIN_SET s IN {MIN_SET s}` by PSET_TAC []
    ++ METIS_TAC [MEMBER_NOT_EMPTY]) 
 ++ RW_TAC std_ss [BB_def, UNION_EMPTY] 
 ++ RW_TAC std_ss [GSPEC_EQ]
 ++ `MIN_SET {x | x IN s DIFF BB n s /\ GCD_OF_SET (BB n s UNION {x}) <> GCD_OF_SET (BB n s)} IN 
	{x | x IN s DIFF BB n s /\ GCD_OF_SET (BB n s UNION {x}) <> GCD_OF_SET (BB n s)}` 
	by METIS_TAC [MIN_SET_LEM]
 ++ `MIN_SET {x | x IN s DIFF BB n s /\ GCD_OF_SET (BB n s UNION {x}) <> GCD_OF_SET (BB n s)} IN 
	BB n s UNION {MIN_SET {x | x IN s DIFF BB n s /\
        GCD_OF_SET (BB n s UNION {x}) <> GCD_OF_SET (BB n s)}}` by PSET_TAC [] 
 ++ METIS_TAC [MEMBER_NOT_EMPTY]);

val POS_BB = prove (
  ``!n x s. (!x. x IN s ==> 0 < x) /\ s <> {} /\ x IN (BB n s) ==> 0 < x``,
    INDUCT_TAC
 >> (RW_TAC std_ss [BB_def, IN_SING] ++ `MIN_SET s IN s` by METIS_TAC [MIN_SET_LEM]
    ++ RW_TAC std_ss [])
 ++ PSET_TAC [BB_def] >> METIS_TAC [] 
 ++ `MIN_SET {x | (x IN s /\ x NOTIN BB n s) /\
	 GCD_OF_SET (BB n s UNION {x}) <> GCD_OF_SET (BB n s)} IN 
	{x | (x IN s /\ x NOTIN BB n s) /\ GCD_OF_SET (BB n s UNION {x}) <> GCD_OF_SET (BB n s)}`
	by METIS_TAC [MIN_SET_LEM]
 ++ `{x | (x IN s /\ x NOTIN BB n s) /\ GCD_OF_SET (BB n s UNION {x}) <> GCD_OF_SET (BB n s)} SUBSET s`
	by PSET_TAC []
 ++ Q.ABBREV_TAC `y = MIN_SET {x | (x IN s /\ x NOTIN BB n s) /\
	 GCD_OF_SET (BB n s UNION {x}) <> GCD_OF_SET (BB n s)}` 
 ++ Q.ABBREV_TAC `A = {x | (x IN s /\ x NOTIN BB n s) /\ 
	GCD_OF_SET (BB n s UNION {x}) <> GCD_OF_SET (BB n s)}`
 ++ `y IN s` by PSET_TAC [] ++ FULL_SIMP_TAC std_ss []);

val GCD_SET_THM = prove
  (``!A. (A <> {}) /\ (!r. r IN A ==> 0 < r) ==> 
	(gcd_set A <> {}) /\ (!x. x IN gcd_set A ==> (0 < x)) /\
	(!x. x IN gcd_set A ==> (x <= MIN_SET A))``,

    PSET_TAC [GSYM MEMBER_NOT_EMPTY, gcd_set_def]
 << [Q.EXISTS_TAC `1:num` ++ RW_TAC std_ss [ONE_DIVIDES_ALL],
    PSET_TAC [divides_def]
    ++ POP_ASSUM (MP_TAC o Q.SPEC `x`) ++ RW_TAC std_ss [] 
    ++ POP_ASSUM (MP_TAC o Q.SPEC `(q:num) * x'`) ++ RW_TAC std_ss [] 
    ++ FULL_SIMP_TAC std_ss [ZERO_LESS_MULT],

    `A <> {}` by (PSET_TAC [GSYM MEMBER_NOT_EMPTY] ++ Q.EXISTS_TAC `x` 
		++ RW_TAC std_ss []) ++ POP_ASSUM MP_TAC 
    ++ POP_ASSUM (MP_TAC o Q.SPEC `MIN_SET A`) ++ RW_TAC std_ss [] 
    ++ FULL_SIMP_TAC std_ss [MIN_SET_LEM]
    ++ Q.PAT_ASSUM `!(r:num). r IN A ==> 0 < r` (MP_TAC o Q.SPEC `MIN_SET A`) 
    ++ RW_TAC std_ss [MIN_SET_LEM]
    ++ FULL_SIMP_TAC std_ss [DIVIDES_LE]]);

val FINITE_GCD_SET = prove
  (``!A. (A <> {}) /\ (!r. r IN A ==> 0 < r) ==> 
	(FINITE (gcd_set A))``,
    PSET_TAC []
 ++ `gcd_set A SUBSET count (SUC (MIN_SET A))` 
	by (PSET_TAC [count_def, LESS_THM]
 	++ (MP_TAC o Q.SPEC `A`) GCD_SET_THM ++ RW_TAC std_ss [] 
 	++ POP_ASSUM (MP_TAC o Q.SPEC `x`) ++ RW_TAC std_ss [] 
 	++ DECIDE_TAC)
 ++ `FINITE (count (SUC (MIN_SET A)))` by RW_TAC std_ss [FINITE_COUNT]
 ++ MATCH_MP_TAC SUBSET_FINITE_I ++ RW_TAC std_ss [] 
 ++ Q.EXISTS_TAC `count (SUC (MIN_SET A))` ++ RW_TAC std_ss []);

val SUBSET_GCD_THM = prove
  (``!(A:num -> bool) B.  (A <> {}) /\ 
	(!x. x IN B ==> 0 < x) /\ (A SUBSET B) ==> (MAX_SET (gcd_set B) IN gcd_set A)``,
    RW_TAC std_ss []
 ++ `(B:num -> bool) <> {}` by (SPOSE_NOT_THEN STRIP_ASSUME_TAC ++ METIS_TAC [SUBSET_EMPTY])
 ++ `FINITE (gcd_set B)` by METIS_TAC [SUBSET_FINITE, FINITE_GCD_SET]
 ++ (MP_TAC o Q.SPEC `B`) GCD_SET_THM ++ RW_TAC std_ss [] ++ POP_ASSUM K_TAC
 ++ `MAX_SET (gcd_set B) IN (gcd_set B)` by METIS_TAC [MAX_SET_DEF]
 ++ PSET_TAC [gcd_set_def, divides_def]);

val DECREASE_GCD_BB = prove (
  ``!n s. (!x. x IN s ==> 0 < x) /\ s <> {}==> 
	(MAX_SET (gcd_set (BB (n + 1) s)) <= MAX_SET (gcd_set (BB n s)))``,
    RW_TAC std_ss []
 ++ `(BB n s) SUBSET (BB (n + 1) s)` by RW_TAC std_ss [SUBSET_BB]
 ++ `(BB n s) <> {}` by RW_TAC std_ss [NON_EMPTY_BB]
 ++ `!x. x IN (BB (n + 1) s) ==> 0 < x` by METIS_TAC [POS_BB]
 ++ (MP_TAC o Q.SPECL [`(BB (n:num) s)`, `(BB ((n:num) + 1) s)`]) SUBSET_GCD_THM 
 ++ RW_TAC std_ss []
 ++ `(gcd_set (BB n s)) <> {}` by METIS_TAC [GSYM MEMBER_NOT_EMPTY]
 ++ `FINITE (gcd_set (BB n s))` by METIS_TAC [FINITE_GCD_SET, POS_BB, NON_EMPTY_BB]
 ++ METIS_TAC [MAX_SET_DEF]);

val LT_GCD_BB = prove (
  ``!n s. (!x. x IN s ==> 0 < x) /\ s <> {} /\ ({x | x IN s DIFF BB n s /\
            GCD_OF_SET (BB n s UNION {x}) <> GCD_OF_SET (BB n s)} <> {})==> 
	(GCD_OF_SET (BB (n + 1) s) < GCD_OF_SET (BB n s))``,
    RW_TAC std_ss []
 ++ `MAX_SET (gcd_set (BB (SUC n) s)) <= MAX_SET (gcd_set (BB n s))` 
	by RW_TAC std_ss [ADD1, DECREASE_GCD_BB]
 ++ `GCD_OF_SET (BB (SUC n) s) <= GCD_OF_SET (BB n s)` by RW_TAC std_ss [GCD_OF_SET_def]
 ++ KNOW_TAC ``GCD_OF_SET (BB (SUC n) s) <> GCD_OF_SET (BB n s)``
 >> (RW_TAC std_ss [BB_def, GSPEC_EQ] 
    ++ `{x | (x IN s /\ x <> MIN_SET s) /\ 
	GCD_OF_SET ({MIN_SET s} UNION {x}) <> GCD_OF_SET {MIN_SET s}} SUBSET s` by PSET_TAC []
    ++ `{MIN_SET {x | x IN s DIFF BB n s /\
           GCD_OF_SET (BB n s UNION {x}) <> GCD_OF_SET (BB n s)}} SUBSET 
	{x | x IN s DIFF BB n s /\ GCD_OF_SET (BB n s UNION {x}) <> GCD_OF_SET (BB n s)}`
        by RW_TAC std_ss [SUBSET_DEF, IN_SING, MIN_SET_LEM]	 
    ++ PSET_TAC [])
 ++ RW_TAC std_ss [GSYM ADD1] ++ DECIDE_TAC);

val GCD_SET_SING = prove
  (``!e. (0 < e) ==> (GCD_OF_SET {e} = e)``,
    PSET_TAC [GCD_OF_SET_def]
 ++ `{e:num} <> {}` by RW_TAC std_ss [NOT_SING_EMPTY]
 ++ `!r. r IN {e} ==> 0 < r` by PSET_TAC []
 ++ `FINITE (gcd_set {e})` by RW_TAC std_ss [FINITE_GCD_SET]
 ++ `e IN gcd_set {e}` by (PSET_TAC [gcd_set_def, divides_def] 
		++ Q.EXISTS_TAC `1` ++ RW_TAC std_ss [MULT_LEFT_1])
 ++ `(gcd_set {e}) <> {}` by METIS_TAC [MEMBER_NOT_EMPTY]
 ++ (MP_TAC o Q.SPEC `gcd_set {e}`) MAX_SET_DEF ++ RW_TAC std_ss []
 ++ POP_ASSUM (MP_TAC o Q.SPEC `e`) ++ RW_TAC std_ss []
 ++ (MP_TAC o Q.SPEC `{e:num}`) GCD_SET_THM ++ RW_TAC std_ss []
 ++ POP_ASSUM (MP_TAC o Q.SPEC `MAX_SET (gcd_set {e})`) 
 ++ RW_TAC std_ss [MAX_SET_DEF, MIN_SET_THM]
 ++ METIS_TAC [EQ_LESS_EQ]);

val GCD_SET_BB_LESS = prove (
  ``!s. (!x. x IN s ==> 0 < x) /\ s <> {} ==>
	(!n. (0 < n) /\ (n <= MIN_SET s) /\ 
	({x | x IN s DIFF BB n s /\ GCD_OF_SET (BB n s UNION {x}) <> GCD_OF_SET (BB n s)} <> {}) ==> 
	(GCD_OF_SET (BB n s) <= (MIN_SET s - n)))``,
    RW_TAC std_ss []
 ++ Induct_on `n` 
 >> RW_TAC std_ss [] ++ RW_TAC std_ss []
 ++ KNOW_TAC ``{x | x IN s DIFF BB n s /\ GCD_OF_SET (BB n s UNION {x}) <>
           GCD_OF_SET (BB n s)} <> {}``
 >> (SPOSE_NOT_THEN STRIP_ASSUME_TAC
    ++ `BB (SUC n) s = BB n s` by RW_TAC std_ss [BB_def, UNION_EMPTY]
    ++ `GCD_OF_SET (BB (SUC n) s) = GCD_OF_SET (BB n s)` by RW_TAC std_ss [RAND_THM]
    ++ FULL_SIMP_TAC std_ss [])
 ++ RW_TAC std_ss []
 ++ `GCD_OF_SET (BB (SUC n) s) < GCD_OF_SET (BB n s)` by RW_TAC std_ss [ADD1, LT_GCD_BB]
 ++ `n <= MIN_SET s` by DECIDE_TAC
 ++ Cases_on `n = 0` 
 >> (RW_TAC std_ss [] 
    ++ `GCD_OF_SET (BB 1 s) < GCD_OF_SET (BB 0 s)` by FULL_SIMP_TAC std_ss [ADD1, LT_GCD_BB]
    ++ `0 < MIN_SET s` by DECIDE_TAC
    ++ `GCD_OF_SET (BB 0 s) = MIN_SET s` by RW_TAC std_ss [BB_def, GCD_SET_SING]
    ++ FULL_SIMP_TAC arith_ss [])
    ++ `0 < n` by DECIDE_TAC
 ++ FULL_SIMP_TAC arith_ss []);

val POS_GCD_BB = prove (
  ``!n s. (!x. x IN s ==> 0 < x) /\ s <> {} ==> (0 < GCD_OF_SET (BB n s))``,
    INDUCT_TAC
 >> (RW_TAC std_ss [BB_def] ++ `0 < MIN_SET s` by METIS_TAC [MIN_SET_LEM] 
    ++ RW_TAC std_ss [GCD_SET_SING])
 ++ RW_TAC std_ss [GCD_OF_SET_def]
 ++ `FINITE (gcd_set (BB (SUC n) s))` by METIS_TAC [FINITE_GCD_SET, NON_EMPTY_BB, POS_BB]
 ++ `gcd_set (BB (SUC n) s) <> {}` by METIS_TAC [NON_EMPTY_BB, POS_BB, GCD_SET_THM]
 ++ `MAX_SET (gcd_set (BB (SUC n) s)) IN gcd_set (BB (SUC n) s)` by RW_TAC std_ss [MAX_SET_DEF]
 ++ METIS_TAC [NON_EMPTY_BB, POS_BB,GCD_SET_THM]);

val EMPTY_EXISTS_BB = prove (
  ``!s. (!x. x IN s ==> 0 < x) /\ s <> {} ==>
	(!n. (MIN_SET s < n) ==>
	({x | x IN s DIFF BB n s /\ GCD_OF_SET (BB n s UNION {x}) <> GCD_OF_SET (BB n s)} = {}))``,
    RW_TAC std_ss []
 ++ Induct_on `n` 
 >> RW_TAC std_ss [MIN_SET_LEM] ++ RW_TAC std_ss []
 ++ Cases_on `{x | x IN s DIFF BB n s /\
           GCD_OF_SET (BB n s UNION {x}) <> GCD_OF_SET (BB n s)} = {}`
 >> (`BB (SUC n) s = BB n s` by RW_TAC std_ss [BB_def, UNION_EMPTY]
          ++ `GCD_OF_SET (BB (SUC n) s) = GCD_OF_SET (BB n s)` by RW_TAC std_ss [RAND_THM]
          ++ FULL_SIMP_TAC std_ss []) ++ RW_TAC std_ss []
 ++ Cases_on `n = MIN_SET s` 
 >> (SPOSE_NOT_THEN STRIP_ASSUME_TAC 
    ++ KNOW_TAC ``GCD_OF_SET (BB n s) <= MIN_SET s - n``
    >> (`!n. 0 < n /\ n <= MIN_SET s /\ {x | x IN s DIFF BB n s /\
            GCD_OF_SET (BB n s UNION {x}) <> GCD_OF_SET (BB n s)} <> {} ==>
           GCD_OF_SET (BB n s) <= MIN_SET s - n` by METIS_TAC [GCD_SET_BB_LESS]
       ++ `0 < n` by METIS_TAC [MIN_SET_LEM] ++ `n <= MIN_SET s` by DECIDE_TAC
       ++ NTAC 4 (POP_ASSUM MP_TAC) ++ POP_ASSUM K_TAC ++ RW_TAC std_ss [])
    ++ DISCH_TAC
    ++ `0 < GCD_OF_SET (BB n s)` by METIS_TAC [POS_GCD_BB]
    ++ FULL_SIMP_TAC arith_ss [])
 ++ `MIN_SET s < n` by DECIDE_TAC 
 ++ FULL_SIMP_TAC std_ss []);

val GCD_OF_BB_UNION_SING = prove (
  ``!s. (!x. x IN s ==> 0 < x) /\ s <> {} ==>
	(!n x. (MIN_SET s < n) /\ (x IN s)==>
	(GCD_OF_SET (BB n s UNION {x}) = GCD_OF_SET (BB n s)))``,
    RW_TAC std_ss []
 ++ Cases_on `x IN BB n s` 
 >> (`(BB n s UNION {x}) = BB n s` by(PSET_TAC [GSPECIFICATION, EXTENSION] 
		++ EQ_TAC >> METIS_TAC [] ++ RW_TAC std_ss [])
    ++ RW_TAC std_ss [])
 ++ `x IN s DIFF BB n s` by PSET_TAC []
 ++ `!n. (MIN_SET s < n) ==>
	({x | x IN s DIFF BB n s /\ GCD_OF_SET (BB n s UNION {x}) <> GCD_OF_SET (BB n s)} = {})`
	by RW_TAC std_ss [EMPTY_EXISTS_BB]
 ++ POP_ASSUM (MP_TAC o Q.SPEC `n`) ++ RW_TAC std_ss []
 ++ PSET_TAC [GSPECIFICATION, EXTENSION]
 ++ POP_ASSUM (MP_TAC o Q.SPEC `x`) ++ RW_TAC std_ss []);

val BB_SUBSET_S = prove (
  ``!s n. (!x. x IN s ==> 0 < x) /\ s <> {} ==> BB n s SUBSET s``,
    Induct_on `n` >> PSET_TAC [BB_def, MIN_SET_LEM] 
 ++ RW_TAC std_ss [BB_def, UNION_EMPTY, GSPEC_EQ, UNION_SUBSET, EMPTY_SUBSET] 
 ++ `{x | x IN s DIFF BB n s /\ 
	GCD_OF_SET (BB n s UNION {x}) <> GCD_OF_SET (BB n s)} SUBSET s`	by PSET_TAC [] 
 ++ `MIN_SET {x | x IN s DIFF BB n s /\ GCD_OF_SET (BB n s UNION {x}) <> GCD_OF_SET (BB n s)}
	IN {x | x IN s DIFF BB n s /\ GCD_OF_SET (BB n s UNION {x}) <> GCD_OF_SET (BB n s)}`
	by METIS_TAC [MIN_SET_LEM]
 ++ `{MIN_SET {x | x IN s DIFF BB n s /\ GCD_OF_SET (BB n s UNION {x}) <> GCD_OF_SET (BB n s)}}
	SUBSET {x | x IN s DIFF BB n s /\ GCD_OF_SET (BB n s UNION {x}) <> GCD_OF_SET (BB n s)}`
		by PSET_TAC []
    ++ METIS_TAC [SUBSET_TRANS]);
val GCD_S_EQ_SOME_GCD_K = prove (
  ``!s n. (!x. x IN s ==> 0 < x) /\ s <> {} /\ (MIN_SET s < n) ==>
	(GCD_OF_SET s = GCD_OF_SET (BB n s))``,
    RW_TAC std_ss []
 ++ `BB n s SUBSET s` by RW_TAC std_ss [BB_SUBSET_S] ++ RW_TAC std_ss [] 
 ++ `BB n s <> {}` by RW_TAC std_ss [NON_EMPTY_BB]
 ++ `GCD_OF_SET s IN gcd_set (BB n s)` by RW_TAC std_ss [GCD_OF_SET_def, SUBSET_GCD_THM]
 ++ `FINITE (gcd_set (BB n s))` by METIS_TAC [FINITE_GCD_SET, POS_BB]
 ++ `gcd_set (BB n s) <> {}` by METIS_TAC [GCD_SET_THM, POS_BB]
 ++ `GCD_OF_SET s <= GCD_OF_SET (BB n s)` by FULL_SIMP_TAC std_ss [GCD_OF_SET_def, MAX_SET_DEF]
 ++ KNOW_TAC ``!x. x IN s ==> divides (GCD_OF_SET (BB n s)) x``
 >> (RW_TAC std_ss []
    ++ `GCD_OF_SET (BB n s) = GCD_OF_SET (BB n s UNION {x})` 
	by RW_TAC std_ss [GCD_OF_BB_UNION_SING, EQ_SYM_EQ] ++ POP_ORW
    ++ KNOW_TAC ``GCD_OF_SET (BB n s UNION {x}) IN gcd_set (BB n s UNION {x})``
    >> (RW_TAC std_ss [GCD_OF_SET_def]
       ++ `BB n s UNION {x} = x INSERT (BB n s)` by PSET_TAC [INSERT_DEF, UNION_DEF, DISJ_COMM]
       ++ `(BB n s UNION {x}) <> {}` by PSET_TAC [NOT_INSERT_EMPTY]
       ++ `!r. r IN (BB n s UNION {x}) ==> 0 < r` by PSET_TAC []
       ++ `FINITE (gcd_set (BB n s UNION {x}))` by METIS_TAC [FINITE_GCD_SET] 
       ++ `(gcd_set (BB n s UNION {x})) <> {}` by METIS_TAC [GCD_SET_THM]
       ++ RW_TAC std_ss [MAX_SET_DEF]) 
    ++ PSET_TAC [gcd_set_def])
 ++ RW_TAC std_ss [] 
 ++ `GCD_OF_SET (BB n s) IN gcd_set s` by PSET_TAC [gcd_set_def]
 ++ `FINITE (gcd_set s)` by RW_TAC std_ss [FINITE_GCD_SET]
 ++ `(gcd_set s) <> {}` by PSET_TAC [GCD_SET_THM]
 ++ `GCD_OF_SET (BB n s) <= GCD_OF_SET s` by METIS_TAC [GCD_OF_SET_def, MAX_SET_DEF]
 ++ FULL_SIMP_TAC std_ss [LESS_EQUAL_ANTISYM]);

val EXISTS_SOME_GCD_K_EQ_GCD_S = prove
  (``!a A. (!x. 0 < (a:num -> num) x) /\ (A = IMAGE (\i. a i) (univ(:num))) ==>
	?t. FINITE t /\ t <> {} /\ t SUBSET A /\ (GCD_OF_SET A = GCD_OF_SET t)``,
    RW_TAC std_ss []
 ++ Q.EXISTS_TAC `BB (MIN_SET (IMAGE (\i. a i) (univ(:num))) + 1) (IMAGE (\i. a i) (univ(:num)))` 
 ++ RW_TAC std_ss []
 << [MATCH_MP_TAC FINITE_BB ++ PSET_TAC [IN_IMAGE]
    ++ SPOSE_NOT_THEN STRIP_ASSUME_TAC ++ `univ(:num) = {}` by METIS_TAC [GSYM IMAGE_EQ_EMPTY] 
    ++ METIS_TAC [UNIV_NEQ_EMPTY],
    MATCH_MP_TAC NON_EMPTY_BB ++ PSET_TAC [IN_IMAGE]
    ++ SPOSE_NOT_THEN STRIP_ASSUME_TAC ++ `univ(:num) = {}` by METIS_TAC [GSYM IMAGE_EQ_EMPTY] 
    ++ METIS_TAC [UNIV_NEQ_EMPTY],
    MATCH_MP_TAC BB_SUBSET_S ++ PSET_TAC [IN_IMAGE]
    ++ SPOSE_NOT_THEN STRIP_ASSUME_TAC ++ `univ(:num) = {}` by METIS_TAC [GSYM IMAGE_EQ_EMPTY] 
    ++ METIS_TAC [UNIV_NEQ_EMPTY],
    MATCH_MP_TAC GCD_S_EQ_SOME_GCD_K ++ PSET_TAC [IN_IMAGE]
    ++ SPOSE_NOT_THEN STRIP_ASSUME_TAC ++ `univ(:num) = {}` by METIS_TAC [GSYM IMAGE_EQ_EMPTY] 
    ++ METIS_TAC [UNIV_NEQ_EMPTY]]); 

val SUBSET_OF_SUMI = prove
  (``!f k. (0 < k) ==> 
	((IMAGE (\(i:num). &f i) (count k)) SUBSET 
	{(r:int) | ?(n:num -> int). r = sumI (0, k) (\i. n i * &f i)})``,
	PSET_TAC [GSPECIFICATION, EXTENSION] 
    ++ Q.EXISTS_TAC `(\r. if r = i then (1:int) else (0:int))`
    ++ RW_TAC std_ss [SUMI_IF_MUL, SUMI_ONE_NON_ZERO_TERM]); 

val SUBSET_SUMI_NOT_EMPTY = prove
  (``!(f:num -> num) k. (0 < k) /\ (!i. 0 < f i) ==> 
	({r | 0 < r /\ &r IN {r | ?n. r = sumI (0,k) (\i. n i * &f i)}} <> {})``,
    SPOSE_NOT_THEN STRIP_ASSUME_TAC 
 ++ `IMAGE (\i. f i) (count k) <> {}` by METIS_TAC [IMAGE_NUMSET_NOTEMPTY]
 ++ KNOW_TAC ``IMAGE (\(i:num). f i) (count k) SUBSET 
	{r | 0 < r /\ &r IN {r | ?n. r = sumI (0,k) (\i. n i * &f i)}}``
 >> (PSET_TAC [GSPECIFICATION, EXTENSION] 
    ++ Q.EXISTS_TAC `(\r. if r = i' then (1:int) else (0:int))`
    ++ RW_TAC std_ss [SUMI_IF_MUL, SUMI_ONE_NON_ZERO_TERM])
 ++ (MP_TAC o Q.SPECL [`f`, `k`]) SUBSET_OF_SUMI ++ RW_TAC std_ss [SUBSET_EMPTY]);

val MINSET_LE_SUBSET = prove (
  ``!x. (0 < k) /\ (!i. 0 < f i) ==> 
	(MIN_SET {r | 0 < r /\ &r IN {r | ?n. r = sumI (0,k) (\i. n i * &f i)}} <= 
	MIN_SET (IMAGE (\i. f i) (count k)))``,
    RW_TAC std_ss []
 ++ `IMAGE (\i. f i) (count k) <> {}` by METIS_TAC [IMAGE_NUMSET_NOTEMPTY]
 ++ `{r | 0 < r /\ &r IN {r | ?n. r = sumI (0,k) (\i. n i * &f i)}} <> {}` 
	by METIS_TAC [SUBSET_SUMI_NOT_EMPTY]
 ++ KNOW_TAC ``IMAGE (\(i:num). f i) (count k) SUBSET 
	{r | 0 < r /\ &r IN {r | ?n. r = sumI (0,k) (\i. n i * &f i)}}``
 >> (PSET_TAC [GSPECIFICATION, EXTENSION] 
    ++ Q.EXISTS_TAC `(\r. if r = i' then (1:int) else (0:int))`
    ++ RW_TAC std_ss [SUMI_IF_MUL, SUMI_ONE_NON_ZERO_TERM])
 ++ RW_TAC std_ss [SUBSET_DEF] 
 ++ POP_ASSUM (MP_TAC o Q.SPEC `MIN_SET (IMAGE (\i. f i) (count k))`) 
 ++ RW_TAC std_ss [MIN_SET_LEM]);

val GCD_GT_ZERO = prove (
  ``!a b. 0 < a /\ 0 < b ==> 0 < gcd a b``,
    RW_TAC std_ss[]
 ++ `0 <= gcd a b` by RW_TAC std_ss[ZERO_LESS_EQ]
 ++ KNOW_TAC ``gcd a b <> 0``
 >> (SPOSE_NOT_THEN STRIP_ASSUME_TAC ++ `a <> 0` by DECIDE_TAC ++ `b <> 0` by DECIDE_TAC
    ++ (MP_TAC o Q.SPECL [`a`, `b`]) FACTOR_OUT_GCD ++ RW_TAC std_ss[])
 ++ RW_TAC std_ss[] ++ DECIDE_TAC);

val IN_SET = prove (
  ``!f k t. (0 < k) /\ (t < k) ==> 
		(&f t IN {(r:int) | ?n. r = sumI (0, k) (\i. n i * &f i)})``,
		PSET_TAC [GSPECIFICATION, EXTENSION] 
 ++ Q.EXISTS_TAC `(\i. if i = t then (1:int) else (0:int))`
 ++ BETA_TAC ++ RW_TAC std_ss [SUMI_IF_MUL, SUMI_ONE_NON_ZERO_TERM]); 

val SUMI_EQ_TWO_SUMI_SUB = prove (
  ``!r (n:num -> int) (t:num -> int). 
	(!(x:num). (0:int) <= POS_PART1 x n) /\ (!(x:num). 0 <= POS_PART2 x n) /\ 
	(!(x:num). n x = (POS_PART1 x n) - (POS_PART2 x n))``,
    RW_TAC std_ss []
 << [RW_TAC std_ss [POS_PART1_def, INT_LE_REFL],
    Cases_on `0 <= n x`
    >> FULL_SIMP_TAC std_ss [POS_PART2_def, int_le, INT_LT_REFL]
    ++ `n x < 0` by METIS_TAC [int_le] 
    ++ RW_TAC std_ss [POS_PART2_def, INT_NEG_GT0, INT_LT_IMP_LE],
    Cases_on `0 <= n x`
    >> FULL_SIMP_TAC std_ss [POS_PART1_def, POS_PART2_def, int_le, INT_SUB_RZERO] 
    ++ `n x < 0` by METIS_TAC [int_le] 
    ++ RW_TAC std_ss [POS_PART1_def, POS_PART2_def, INT_SUB_LZERO, INT_NEGNEG]]);

val POSINTSET_NOT_EMPTY = prove (
  ``!(f:num -> num) k. (0 < k) ==> 
	({(r:int) | ?(n:num -> int). r = sumI (0, k) (\i. n i * &f i)} <> {})``,
    SPOSE_NOT_THEN STRIP_ASSUME_TAC 
 ++ `IMAGE (\(i:num). &f i) (count k) <> {}` by RW_TAC std_ss [IMAGE_POS_INTSET_NOTEMPTY]
 ++ (MP_TAC o Q.SPECL [`f`, `k`]) SUBSET_OF_SUMI ++ RW_TAC std_ss [SUBSET_EMPTY]);

val POSINT_IN_SET = prove (
  ``!(f:num -> num) k. (0 < k) /\ (!i. 0 < f i) ==>
   ?n. 0 < n /\ n IN {(r:int) | ?(n:num -> int). r = sumI (0, k) (\i. n i * &f i)}``,
    PSET_TAC [GSYM MEMBER_NOT_EMPTY] 
 ++ `IMAGE (\(i:num). &f i) (count k) <> {}` by RW_TAC std_ss [IMAGE_POS_INTSET_NOTEMPTY]
 ++ `!i. 0 < &f i` by RW_TAC std_ss [INT_LT]
 ++ Q.EXISTS_TAC `&f (k - 1)` ++ RW_TAC std_ss []
 ++ Q.EXISTS_TAC `(\r. if r = k - 1 then (1:int) else (0:int))`
    ++ RW_TAC std_ss [SUMI_IF_MUL, SUMI_ONE_NON_ZERO_TERM]); 

val POSINT_IN_SUMISET = prove (
  ``!(f:num -> num) k. (0 < k) /\ (!i. (i < k) ==> 0 < f i) ==>
   ?n. 0 < n /\ n IN IMAGE (\(i:num). &f i) (count k) /\ 
	n IN {(r:int) | ?(n:num -> int). r = sumI (0, k) (\i. n i * &f i)}``,
    PSET_TAC [GSYM MEMBER_NOT_EMPTY] 
 ++ `IMAGE (\(i:num). &f i) (count k) <> {}` by RW_TAC std_ss [IMAGE_POS_INTSET_NOTEMPTY]
 ++ PSET_TAC [GSYM MEMBER_NOT_EMPTY]
 ++ `!i. (i < k) ==> 0 < &f i` by RW_TAC std_ss [INT_LT]
 ++ Q.EXISTS_TAC `&f i` ++ RW_TAC std_ss [] 
 >> (Q.EXISTS_TAC `i` ++ RW_TAC std_ss [])
 ++ Q.EXISTS_TAC `(\r. if r = i then (1:int) else (0:int))`
 ++ RW_TAC std_ss [SUMI_IF_MUL, SUMI_ONE_NON_ZERO_TERM]); 

val INTEGER_LEMMA1 = prove (
  (``!s. (?z. z <> 0 /\ z IN s) /\
	(!a b. a IN s /\ b IN s ==> (a + b) IN s /\ (b - a) IN s)
	==> ?x. x IN s /\ 0 < x /\ (!y. y IN s /\ 0 < y ==> x <= y)
	/\ (s = {(r:int) | ?(k:int). (r = k * x)})``),
    PSET_TAC [] 
 ++ KNOW_TAC ``(0:int) IN s`` 
 >> (POP_ASSUM (MP_TAC o Q.SPECL [`z`, `z`]) ++ RW_TAC std_ss [INT_SUB_REFL])
 ++ RW_TAC std_ss []
 ++ KNOW_TAC ``{(r:num) | 0 < r /\ &r IN s} <> {}``
 >> (PSET_TAC [] ++ Cases_on `0 < z` 
       >> (SPOSE_NOT_THEN STRIP_ASSUME_TAC 
       ++ PSET_TAC [GSPECIFICATION, EXTENSION] ++ `0 <= z` by FULL_SIMP_TAC std_ss [INT_LT_IMP_LE] 
       ++ `z = &Num z` by FULL_SIMP_TAC std_ss [INT_OF_NUM] 
       ++ `0 < Num z` by METIS_TAC [INT_LT] 
       ++ Q.EXISTS_TAC `Num z` ++ RW_TAC std_ss [] ++ POP_ASSUM K_TAC 
       ++ POP_ASSUM (MP_TAC o GSYM) ++ RW_TAC std_ss [])
    ++ `0 <= ~z` by FULL_SIMP_TAC std_ss [INT_NOT_LT, INT_LT_LE, INT_NEG_GT0, INT_LT_IMP_LE]
    ++ Q.PAT_ASSUM `!a b. a IN s /\ b IN s ==> a + b IN s /\ b - a IN s` 
		(MP_TAC o Q.SPECL [`z`, `0`]) ++ RW_TAC std_ss [INT_SUB_LZERO]
    ++ `0 < ~z` by METIS_TAC [INT_NOT_LT, INT_LT_LE, INT_NEG_GT0]
    ++ `~z = &Num (~z)` by FULL_SIMP_TAC std_ss [INT_OF_NUM] 
    ++ `0 < &Num (~z)` by METIS_TAC [INT_LT] 
    ++ `0 < Num (~z)` by METIS_TAC [INT_LT] 
    ++ PSET_TAC [GSPECIFICATION, EXTENSION] ++ Q.EXISTS_TAC `Num (~z)` ++ RW_TAC std_ss [] 
    ++ NTAC 2 (POP_ASSUM K_TAC) ++ POP_ASSUM (MP_TAC o GSYM) ++ RW_TAC std_ss [])
 ++ RW_TAC std_ss [] 
 ++ KNOW_TAC ``&MIN_SET {r | 0 < r /\ &r IN s} IN s``
 >> (RW_TAC std_ss []  
    ++ `MIN_SET {r | 0 < r /\ &r IN s} IN {r | 0 < r /\ &r IN s}` by RW_TAC std_ss [MIN_SET_LEM]
    ++ `IMAGE (\x. &x) {r | 0 < r /\ &r IN s} SUBSET s` by PSET_TAC []
    ++ PSET_TAC []) ++ RW_TAC std_ss [] 
 ++ KNOW_TAC ``0 < &MIN_SET {r | 0 < r /\ &r IN s}``
 >> (`!x. x IN IMAGE (\y. &y) {r | 0 < r /\ &r IN s} ==> 0 < x` 
	by (PSET_TAC [] ++ RW_TAC std_ss [INT_LT])
    ++ `MIN_SET {r | 0 < r /\ &r IN s} IN {r | 0 < r /\ &r IN s}` by RW_TAC std_ss [MIN_SET_LEM]
    ++ `IMAGE (\x. &x) {r | 0 < r /\ &r IN s} SUBSET s` by PSET_TAC []
    ++ `&MIN_SET {r | 0 < r /\ &r IN s} IN IMAGE (\x. &x) {r | 0 < r /\ &r IN s}`
       		by (PSET_TAC [] ++ Q.EXISTS_TAC `MIN_SET {r | 0 < r /\ &r IN s}` 
    			++ RW_TAC std_ss [] ++ FULL_SIMP_TAC std_ss []) 
    ++ RW_TAC std_ss [])
 ++ RW_TAC std_ss []
 ++ KNOW_TAC ``!y. y IN s /\ 0 < y ==> &MIN_SET {(r:num) | 0 < r /\ &r IN s} <= y``
 >> (PSET_TAC [] ++ `0 <= y` by FULL_SIMP_TAC std_ss [INT_LT_IMP_LE] 
    ++ `y = &Num y` by FULL_SIMP_TAC std_ss [INT_OF_NUM] 
    ++ KNOW_TAC ``Num y IN {(r:num) | 0 < r /\ &r IN s}``
    >> (PSET_TAC [] ++ METIS_TAC [INT_LT] ++ POP_ASSUM (MP_TAC o GSYM) ++ RW_TAC std_ss [])
    ++ RW_TAC std_ss [] 
    ++ `MIN_SET {(r:num) | 0 < r /\ &r IN s} <= Num y` by METIS_TAC [MIN_SET_LEM]
    ++ METIS_TAC [INT_LE])
 ++ RW_TAC std_ss []
 ++ Q.EXISTS_TAC `&MIN_SET {(r:num) | 0 < r /\ &r IN s}` ++ RW_TAC std_ss []
 ++ KNOW_TAC ``!v. 0 <= v ==> {(r:int) | (r = v * &MIN_SET {(r:num) | 0 < r /\ &r IN s})} SUBSET s`` 
    >> (PSET_TAC [] ++ `v = &Num v` by FULL_SIMP_TAC std_ss [INT_LT_IMP_LE, INT_OF_NUM] 
    ++ POP_ORW
    ++ Induct_on `Num v`
       >> (RW_TAC std_ss [] ++ `Num v = 0` by FULL_SIMP_TAC std_ss [EQ_SYM_EQ] ++ POP_ORW 
       ++ FULL_SIMP_TAC std_ss [INT_MUL_LZERO])
    ++ RW_TAC std_ss [ADD1] ++ Cases_on `v = 0` 
       >> (RW_TAC std_ss [LESS_EQ_REFL] ++ `&Num 0 = 0` by FULL_SIMP_TAC std_ss [INT_OF_NUM]
       ++ RW_TAC std_ss [INT_MUL_LZERO])
    ++ `0 < v` by FULL_SIMP_TAC std_ss [INT_LT_LE]
    ++ `Num v = v' + 1` by FULL_SIMP_TAC std_ss [EQ_SYM_EQ] ++ POP_ORW
    ++ `&(v' + 1) = &v' + (1:int)` by RW_TAC std_ss [GSYM INT_ADD] ++ POP_ORW
    ++ RW_TAC std_ss [INT_RDISTRIB, INT_MUL_LID] 
    ++ `&Num v = v` by FULL_SIMP_TAC std_ss [INT_OF_NUM]
    ++ (MP_TAC o Q.SPECL [`(0:num)`, `Num v`]) INT_LT ++ RW_TAC std_ss []
    ++ `0 < v' + 1` by FULL_SIMP_TAC std_ss []
    ++ `1 <= v' + 1` by FULL_SIMP_TAC arith_ss []
    ++ `0 <= v'` by FULL_SIMP_TAC arith_ss []
    ++ KNOW_TAC ``v' = Num (&v')``
       >> (RW_TAC std_ss [Num] ++ SELECT_ELIM_TAC 
       ++ CONJ_TAC 
       >> (Q.EXISTS_TAC `(v':num)` ++ RW_TAC std_ss [])
       ++ RW_TAC std_ss [INT_EQ_CALCULATE]) ++ RW_TAC std_ss [] ++ ONCE_ASM_REWRITE_TAC []
       ++ Q.PAT_ASSUM `!k. (v' = Num v) ==> 0 <= v ==> &Num v * x IN s` 
		(MP_TAC o Q.SPEC `&(v':num)`) ++ RW_TAC std_ss [INT_OF_NUM, INT_LE])
 ++ RW_TAC std_ss []
 ++ KNOW_TAC ``!v. v < 0 ==> {r | r = v * &MIN_SET {(r:num) | 0 < r /\ &r IN s}} SUBSET s``
    >> (PSET_TAC [] ++ `0 < (~v)` by FULL_SIMP_TAC std_ss [INT_NEG_GT0] 
    ++ `0 <= (~v)` by FULL_SIMP_TAC std_ss [INT_LT_IMP_LE]
    ++ `~v * &MIN_SET {(r:num) | 0 < r /\ &r IN s} IN s` by FULL_SIMP_TAC std_ss []
    ++ Q.PAT_ASSUM `!a b. a IN s /\ b IN s ==> a + b IN s /\ b - a IN s` 
		(MP_TAC o Q.SPECL [`~v * &MIN_SET {(r:num) | 0 < r /\ &r IN s}`, `0`]) 
    ++ RW_TAC std_ss [INT_MUL_CALCULATE, INT_SUB_RNEG, INT_ADD_CALCULATE])
 ++ RW_TAC std_ss [] 
 ++ `!v. {r | r = v * &MIN_SET {r | 0 < r /\ &r IN s}} SUBSET s` 
	by (RW_TAC std_ss [] ++ Cases_on `0 <= v` >> RW_TAC std_ss [] 
	    ++ `v < 0` by FULL_SIMP_TAC std_ss [INT_NOT_LE] ++ FULL_SIMP_TAC std_ss [])
 ++ KNOW_TAC ``{(r:int) | ?k. (r = k * &MIN_SET {(r:num) | 0 < r /\ &r IN s})} SUBSET s`` 
    >> (PSET_TAC [] ++ Cases_on `0 <= k` >> RW_TAC std_ss [] 
    ++ `k < 0` by FULL_SIMP_TAC std_ss [INT_NOT_LE] ++ FULL_SIMP_TAC std_ss [])
 ++ RW_TAC std_ss [] 
 ++ `&MIN_SET {(r:num) | 0 < r /\ &r IN s} <> 0` by FULL_SIMP_TAC std_ss [INT_LT_IMP_NE]
 ++ KNOW_TAC ``s SUBSET {(r:int) | ?k. (r = k * &MIN_SET {(r:num) | 0 < r /\ &r IN s})}``
 >> (PSET_TAC [] 
    ++ (MP_TAC o Q.SPECL [`x`, `&MIN_SET {(r:num) | 0 < r /\ &r IN s}`]) INT_MOD_BOUNDS
    ++ RW_TAC std_ss [] >> METIS_TAC [INT_LT_ANTISYM] ++ RW_TAC std_ss []
    ++ KNOW_TAC ``x % &MIN_SET {(r:num) | 0 < r /\ &r IN s} IN s``
    >> (RW_TAC std_ss [] 
       ++ KNOW_TAC ``x - x / &MIN_SET {(r:num) | 0 < r /\ &r IN s} * 
		&MIN_SET {(r:num) | 0 < r /\ &r IN s} = x % &MIN_SET {(r:num) | 0 < r /\ &r IN s}``
       >> (FULL_SIMP_TAC std_ss [INT_ADD_COMM, INT_EQ_SUB_LADD, EQ_SYM_EQ]
          ++ (MP_TAC o Q.SPEC `&MIN_SET {(r:num) | 0 < r /\ &r IN s}`) INT_DIVISION 
          ++ RW_TAC std_ss [] ++ POP_ASSUM (MP_TAC o Q.SPEC `x`) ++ RW_TAC std_ss [INT_ADD_COMM]) 
       ++ RW_TAC std_ss [EQ_SYM_EQ])
    ++ RW_TAC std_ss []
    ++ KNOW_TAC ``x % &MIN_SET {r | 0 < r /\ &r IN s} = 0``
    >> (RW_TAC std_ss [] ++ SPOSE_NOT_THEN STRIP_ASSUME_TAC 
       ++ `0 < x % &MIN_SET {r | 0 < r /\ &r IN s}` by METIS_TAC [INT_LT_LE]
       ++ Q.PAT_ASSUM `!y. y IN s /\ 0 < y ==> &MIN_SET {r | 0 < r /\ &r IN s} <= y`
		(MP_TAC o Q.SPEC `x % &MIN_SET {r | 0 < r /\ &r IN s}`) 
       ++ RW_TAC std_ss [INT_NOT_LE])
    ++ RW_TAC std_ss []
    ++ Q.EXISTS_TAC `x / &MIN_SET {(r:num) | 0 < r /\ &r IN s}`
    ++ RW_TAC std_ss [INT_DIV_MUL_ID])
 ++ RW_TAC std_ss []  
 ++ PSET_TAC [GSPECIFICATION, EXTENSION] ++ EQ_TAC 
 >> RW_TAC std_ss [] ++ RW_TAC std_ss []);

val MAX_DIVISOR = prove (
  ``!x s. (0 < x) /\ x IN s /\ (s = {(r:int) | ?(k:int). (r = k * x)}) ==> 
	(x <= &MAX_SET (gcd_set {r | 0 < r /\ &r IN s}))``,
    RW_TAC std_ss []
 ++ `{(r:int) | ?(k:int). (r = k * x)} <> {}` by METIS_TAC [MEMBER_NOT_EMPTY]
 ++ `x = &Num x` by METIS_TAC [INT_LT_IMP_LE, GSYM INT_OF_NUM]
 ++ ONCE_ASM_REWRITE_TAC [] ++ RW_TAC std_ss [INT_LE]
 ++ `0 < Num x` by METIS_TAC [INT_LT]
 ++ KNOW_TAC ``Num x IN {r | 0 < r /\ &r IN {r | ?k. r = k * &Num x}}``
    >> (PSET_TAC [] ++ Q.EXISTS_TAC `1` ++ RW_TAC std_ss [INT_MUL_LID])
 ++ RW_TAC std_ss []
 ++ `{r | 0 < r /\ &r IN {r | ?k. r = k * &Num x}} <> {}` 
	by (PSET_TAC [GSYM MEMBER_NOT_EMPTY] ++ Q.EXISTS_TAC `Num x` ++ RW_TAC std_ss []
            ++ Q.EXISTS_TAC `k'` ++ RW_TAC std_ss [INT_MUL_LID])
 ++ `!r. r IN {r | 0 < r /\ &r IN {r | ?k. r = k * &Num x}} ==> (0 < r)` by PSET_TAC []
 ++ (MP_TAC o Q.SPEC `{r | 0 < r /\ &r IN {r | ?k. r = k * &Num x}}`) GCD_SET_THM
 ++ RW_TAC std_ss [] ++ POP_ASSUM K_TAC 
 ++ `FINITE (gcd_set {r | 0 < r /\ &r IN {r | ?k. r = k * &Num x}})` by RW_TAC std_ss [FINITE_GCD_SET]
 ++ KNOW_TAC ``{r | 0 < r /\ &r IN {r | ?k. r = k * x}} <> {}``
 >> (RW_TAC std_ss [] 
    ++ `(Num x) IN {r | 0 < r /\ &r IN {r | ?k. r = k * x}}` by (PSET_TAC [] 
         ++ Q.EXISTS_TAC `(1:int)` ++ RW_TAC std_ss [INT_MUL_LID, NUM_OF_INT])
    ++ METIS_TAC [MEMBER_NOT_EMPTY]) ++ DISCH_TAC 
 ++ KNOW_TAC ``Num x IN gcd_set {r | 0 < r /\ &r IN {r | ?k. r = k * x}}``
 >> (PSET_TAC [gcd_set_def] 
    ++ `x' = Num &x'` by RW_TAC std_ss [NUM_OF_INT]
    ++ POP_ORW ++ `divides (Num x) (Num (&x')) = divides (Num x) (Num (k'' * x))` by RW_TAC std_ss [] 
    ++ POP_ORW ++ RW_TAC std_ss [divides_def] ++ `0 < k'' * x` by METIS_TAC [INT_LT]
    ++ KNOW_TAC ``0 < k''`` 
    >> (SPOSE_NOT_THEN STRIP_ASSUME_TAC ++ FULL_SIMP_TAC std_ss[GSYM int_le] 
       ++ Cases_on `k'' = 0` >> METIS_TAC [INT_MUL_LZERO, INT_LT_REFL] 
       ++ `k'' < 0` by METIS_TAC [GSYM INT_LT_LE] 
       ++ (MP_TAC o GSYM o Q.SPECL [`k''`, `x`]) INT_MUL_SIGN_CASES 
       ++ RW_TAC std_ss [GSYM int_le, INT_LT_IMP_LE]) 
    ++ RW_TAC std_ss [] ++ `k'' = &Num k''` by METIS_TAC [INT_LT_IMP_LE, GSYM INT_OF_NUM, EQ_SYM_EQ]
    ++ Q.EXISTS_TAC `Num k''` ++ RW_TAC std_ss [] 
    ++ `&(Num (k'' * x)) = k'' * x` by METIS_TAC [INT_LT_IMP_LE, GSYM INT_OF_NUM]
    ++ `&(Num k'' * Num x) = k'' * x` by METIS_TAC [GSYM INT_MUL, INT_LT_IMP_LE, GSYM INT_OF_NUM]
    ++ FULL_SIMP_TAC std_ss [GSYM INT_INJ])
 ++ RW_TAC std_ss [] 
 ++ `Num x IN gcd_set {r | 0 < r /\ &r IN {r | ?k. r = k * &Num x}}` 
	by (`&Num x = x` by METIS_TAC [EQ_SYM_EQ] ++ POP_ORW ++ RW_TAC std_ss []) 
 ++ (MP_TAC o Q.SPEC `gcd_set {r | 0 < r /\ &r IN {r | ?k. r = k * &Num x}}`) MAX_SET_DEF
 ++ RW_TAC std_ss [] ++ POP_ASSUM (MP_TAC o Q.SPEC `Num x`) ++ RW_TAC std_ss []);

val NON_EMPTY_POSINT = prove (
  ``!s. (?z. z <> 0 /\ z IN s) /\
	(!a b. a IN s /\ b IN s ==> (a + b) IN s /\ (b - a) IN s)
	==> ((0:int) IN s) /\ ({(r:num) | 0 < r /\ &r IN s} <> {})``,

	RW_TAC std_ss [] 
    << [RW_TAC std_ss [] 
       ++ POP_ASSUM (MP_TAC o Q.SPECL [`z`, `z`]) ++ RW_TAC std_ss [INT_SUB_REFL],
       `(0:int) IN s` by (RW_TAC std_ss [] ++ POP_ASSUM (MP_TAC o Q.SPECL [`z`, `z`]) 
			++ RW_TAC std_ss [INT_SUB_REFL])
       ++ (Cases_on `0 < z` 
       >> (SPOSE_NOT_THEN STRIP_ASSUME_TAC 
       ++ PSET_TAC [GSPECIFICATION, EXTENSION] ++ `0 <= z` by FULL_SIMP_TAC std_ss [INT_LT_IMP_LE] 
       ++ `z = &Num z` by FULL_SIMP_TAC std_ss [INT_OF_NUM] 
       ++ `0 < Num z` by METIS_TAC [INT_LT] 
       ++ Q.EXISTS_TAC `Num z` ++ RW_TAC std_ss [] ++ POP_ASSUM K_TAC 
       ++ POP_ASSUM (MP_TAC o GSYM) ++ RW_TAC std_ss [])
       ++ `0 <= ~z` by FULL_SIMP_TAC std_ss [INT_NOT_LT, INT_LT_LE, INT_NEG_GT0, INT_LT_IMP_LE]
       ++ Q.PAT_ASSUM `!a b. a IN s /\ b IN s ==> a + b IN s /\ b - a IN s` 
		(MP_TAC o Q.SPECL [`z`, `0`]) ++ RW_TAC std_ss [INT_SUB_LZERO]
       ++ `0 < ~z` by METIS_TAC [INT_NOT_LT, INT_LT_LE, INT_NEG_GT0]
       ++ `~z = &Num (~z)` by FULL_SIMP_TAC std_ss [INT_OF_NUM] 
       ++ `0 < &Num (~z)` by METIS_TAC [INT_LT] 
       ++ `0 < Num (~z)` by METIS_TAC [INT_LT] 
       ++ PSET_TAC [GSPECIFICATION, EXTENSION] ++ Q.EXISTS_TAC `Num (~z)` ++ RW_TAC std_ss [] 
       ++ NTAC 2 (POP_ASSUM K_TAC) ++ POP_ASSUM (MP_TAC o GSYM) ++ RW_TAC std_ss [])]);

(* ------------------------------------------------------------------------- *)
(* Lemma 2: Positive Element in a Closet Set                                 *)
(* ------------------------------------------------------------------------- *)
val POSINT_MIN_SET_THM = prove (
  (``!s. (?z. z <> 0 /\ z IN s) /\
	(!a b. a IN s /\ b IN s ==> (a + b) IN s /\ (b - a) IN s)
	==> (&MIN_SET {r | 0 < r /\ &r IN s} IN s) /\ 0 < &MIN_SET {r | 0 < r /\ &r IN s} /\ 
	(!y. y IN s /\ 0 < y ==> &MIN_SET {r | 0 < r /\ &r IN s} <= y) /\ 
	(s = {(r:int) | ?(k:int). (r = k * &MIN_SET {r | 0 < r /\ &r IN s})})``),
    PSET_TAC [] 
 << [RW_TAC std_ss [] 
    ++ KNOW_TAC ``(?z. z <> 0 /\ z IN s) /\
	(!a b. a IN s /\ b IN s ==> (a + b) IN s /\ (b - a) IN s)``
    >> (RW_TAC std_ss [] ++ Q.EXISTS_TAC `z` ++ RW_TAC std_ss []) 
    ++ DISCH_TAC 
    ++ (MP_TAC o Q.SPEC `s`) NON_EMPTY_POSINT 
    ++ RW_TAC std_ss [] 
    ++ NTAC 2 (POP_ASSUM K_TAC)
    ++ `MIN_SET {r | 0 < r /\ &r IN s} IN {r | 0 < r /\ &r IN s}` 
    	by RW_TAC std_ss [MIN_SET_LEM]
    ++ `IMAGE (\x. &x) {r | 0 < r /\ &r IN s} SUBSET s` by PSET_TAC []
    ++ PSET_TAC [],
    
       RW_TAC std_ss []
    ++ KNOW_TAC ``(?z. z <> 0 /\ z IN s) /\
	(!a b. a IN s /\ b IN s ==> (a + b) IN s /\ (b - a) IN s)``
    >> (RW_TAC std_ss [] ++ Q.EXISTS_TAC `z` ++ RW_TAC std_ss []) 
    ++ DISCH_TAC
    ++ (MP_TAC o Q.SPEC `s`) NON_EMPTY_POSINT ++ RW_TAC std_ss [] 
    ++ NTAC 2 (POP_ASSUM K_TAC)
    ++ `!x. x IN IMAGE (\y. &y) {r | 0 < r /\ &r IN s} ==> 0 < x` 
	by (PSET_TAC [] ++ RW_TAC std_ss [INT_LT])
    ++ `MIN_SET {r | 0 < r /\ &r IN s} IN {r | 0 < r /\ &r IN s}` 
    	by RW_TAC std_ss [MIN_SET_LEM]
    ++ PSET_TAC [INT_LT],

       RW_TAC std_ss []
 ++ `0 <= y` by RW_TAC std_ss [INT_LT_IMP_LE]
 ++ `y = &Num y` by METIS_TAC [GSYM INT_OF_NUM] 
 ++ POP_ORW ++ RW_TAC std_ss [INT_LE]
 ++ KNOW_TAC ``Num y IN {(r:num) | 0 < r /\ &r IN s}``
    >> (PSET_TAC [] >> METIS_TAC [GSYM INT_OF_NUM, INT_LT]
	++ METIS_TAC [GSYM INT_OF_NUM])
 ++ RW_TAC std_ss [] 
 ++ `{r | 0 < r /\ &r IN s} <> {}` by (PSET_TAC [GSYM MEMBER_NOT_EMPTY] 
		++ Q.EXISTS_TAC `Num y` ++ RW_TAC std_ss [])
 ++ (MP_TAC o Q.SPEC `{r | 0 < r /\ &r IN s}`) MIN_SET_LEM 
 ++ RW_TAC std_ss [],

       RW_TAC std_ss []
 ++ KNOW_TAC ``(?z. z <> 0 /\ z IN s) /\
	(!a b. a IN s /\ b IN s ==> (a + b) IN s /\ (b - a) IN s)``
 >> (RW_TAC std_ss [] ++ Q.EXISTS_TAC `z` ++ RW_TAC std_ss []) 
 ++ DISCH_TAC
 ++ (MP_TAC o Q.SPEC `s`) NON_EMPTY_POSINT 
 ++ RW_TAC std_ss [] ++ NTAC 2 (POP_ASSUM K_TAC)
 ++ `&MIN_SET {r | 0 < r /\ &r IN s} IN s` by (RW_TAC std_ss [] 
	++ `MIN_SET {r | 0 < r /\ &r IN s} IN {r | 0 < r /\ &r IN s}` by RW_TAC std_ss [MIN_SET_LEM]
    	++ `IMAGE (\x. &x) {r | 0 < r /\ &r IN s} SUBSET s` by PSET_TAC []
    	++ PSET_TAC [])
 ++ `0 < &MIN_SET {(r:num) | 0 < r /\ &r IN s}` by 
	(`!x. x IN IMAGE (\y. &y) {r | 0 < r /\ &r IN s} ==> 0 < x` 
	by (PSET_TAC [] 
	   ++ RW_TAC std_ss [INT_LT])
    	   ++ `MIN_SET {r | 0 < r /\ &r IN s} IN {r | 0 < r /\ &r IN s}` 
    	   	by RW_TAC std_ss [MIN_SET_LEM]
    	++ PSET_TAC [INT_LT])
 ++ KNOW_TAC ``!v. 0 <= v ==> 
 	{(r:int) | (r = v * &MIN_SET {(r:num) | 0 < r /\ &r IN s})} SUBSET s`` 
 >> (PSET_TAC [] 
    ++ `v = &Num v` by FULL_SIMP_TAC std_ss [INT_LT_IMP_LE, INT_OF_NUM] 
    ++ POP_ORW
    ++ Induct_on `Num v`
    >> (RW_TAC std_ss [] 
       ++ `Num v = 0` by FULL_SIMP_TAC std_ss [EQ_SYM_EQ] ++ POP_ORW 
       ++ FULL_SIMP_TAC std_ss [INT_MUL_LZERO])
    ++ RW_TAC std_ss [ADD1] ++ Cases_on `v = 0` 
    >> (RW_TAC std_ss [LESS_EQ_REFL] 
       ++ `&Num 0 = 0` by FULL_SIMP_TAC std_ss [INT_OF_NUM]
       ++ RW_TAC std_ss [INT_MUL_LZERO])
    ++ `0 < v` by FULL_SIMP_TAC std_ss [INT_LT_LE]
    ++ `Num v = v' + 1` by FULL_SIMP_TAC std_ss [EQ_SYM_EQ] 
    ++ POP_ORW
    ++ `&(v' + 1) = &v' + (1:int)` by RW_TAC std_ss [GSYM INT_ADD] 
    ++ POP_ORW
    ++ RW_TAC std_ss [INT_RDISTRIB, INT_MUL_LID] 
    ++ `&Num v = v` by FULL_SIMP_TAC std_ss [INT_OF_NUM]
    ++ (MP_TAC o Q.SPECL [`(0:num)`, `Num v`]) INT_LT 
    ++ RW_TAC std_ss []
    ++ `0 < v' + 1` by FULL_SIMP_TAC std_ss []
    ++ `1 <= v' + 1` by FULL_SIMP_TAC arith_ss []
    ++ `0 <= v'` by FULL_SIMP_TAC arith_ss []
    ++ KNOW_TAC ``v' = Num (&v')``
    >> (RW_TAC std_ss [Num] ++ SELECT_ELIM_TAC 
       ++ CONJ_TAC 
       >> (Q.EXISTS_TAC `(v':num)` ++ RW_TAC std_ss [])
       ++ RW_TAC std_ss [INT_EQ_CALCULATE]) 
    ++ RW_TAC std_ss [] 
    ++ ONCE_ASM_REWRITE_TAC []
    ++ Q.PAT_ASSUM `!v. (v' = Num v) ==>
            0 <= v ==> &Num v * &MIN_SET {r | 0 < r /\ &r IN s} IN s` 
	(MP_TAC o Q.SPEC `&(v':num)`) 
    ++ RW_TAC std_ss [INT_OF_NUM, INT_LE])
 ++ RW_TAC std_ss []
 ++ KNOW_TAC ``!v. v < 0 ==> {r | r = v * &MIN_SET {(r:num) | 0 < r /\ &r IN s}} SUBSET s``
 >> (PSET_TAC [] ++ `0 < (~v)` by FULL_SIMP_TAC std_ss [INT_NEG_GT0] 
    ++ `0 <= (~v)` by FULL_SIMP_TAC std_ss [INT_LT_IMP_LE]
    ++ `~v * &MIN_SET {(r:num) | 0 < r /\ &r IN s} IN s` by FULL_SIMP_TAC std_ss []
    ++ Q.PAT_ASSUM `!a b. a IN s /\ b IN s ==> a + b IN s /\ b - a IN s` 
		(MP_TAC o Q.SPECL [`~v * &MIN_SET {(r:num) | 0 < r /\ &r IN s}`, `0`]) 
    ++ RW_TAC std_ss [INT_MUL_CALCULATE, INT_SUB_RNEG, INT_ADD_CALCULATE])
 ++ RW_TAC std_ss [] 
 ++ `!v. {r | r = v * &MIN_SET {r | 0 < r /\ &r IN s}} SUBSET s` 
	by (RW_TAC std_ss [] ++ Cases_on `0 <= v` >> RW_TAC std_ss [] 
	    ++ `v < 0` by FULL_SIMP_TAC std_ss [INT_NOT_LE] ++ FULL_SIMP_TAC std_ss [])
 ++ KNOW_TAC ``{(r:int) | ?k. (r = k * &MIN_SET {(r:num) | 0 < r /\ &r IN s})} SUBSET s`` 
    >> (PSET_TAC [] ++ Cases_on `0 <= k` >> RW_TAC std_ss [] 
    ++ `k < 0` by FULL_SIMP_TAC std_ss [INT_NOT_LE] ++ FULL_SIMP_TAC std_ss [])
 ++ RW_TAC std_ss [] 
 ++ `&MIN_SET {(r:num) | 0 < r /\ &r IN s} <> 0` by FULL_SIMP_TAC std_ss [INT_LT_IMP_NE]
 ++ KNOW_TAC ``s SUBSET {(r:int) | ?k. (r = k * &MIN_SET {(r:num) | 0 < r /\ &r IN s})}``
 >> (PSET_TAC [] 
    ++ (MP_TAC o Q.SPECL [`x`, `&MIN_SET {(r:num) | 0 < r /\ &r IN s}`]) INT_MOD_BOUNDS
    ++ RW_TAC std_ss [] >> METIS_TAC [INT_LT_ANTISYM] 
    ++ KNOW_TAC ``x % &MIN_SET {(r:num) | 0 < r /\ &r IN s} IN s``
    >> (RW_TAC std_ss [] 
       ++ KNOW_TAC ``x - x / &MIN_SET {(r:num) | 0 < r /\ &r IN s} * 
		&MIN_SET {(r:num) | 0 < r /\ &r IN s} = x % &MIN_SET {(r:num) | 0 < r /\ &r IN s}``
       >> (FULL_SIMP_TAC std_ss [INT_ADD_COMM, INT_EQ_SUB_LADD, EQ_SYM_EQ]
          ++ (MP_TAC o Q.SPEC `&MIN_SET {(r:num) | 0 < r /\ &r IN s}`) INT_DIVISION 
          ++ RW_TAC std_ss [] ++ POP_ASSUM (MP_TAC o Q.SPEC `x`) ++ RW_TAC std_ss [INT_ADD_COMM]) 
       ++ RW_TAC std_ss [EQ_SYM_EQ])
    ++ RW_TAC std_ss []
    ++ KNOW_TAC ``x % &MIN_SET {r | 0 < r /\ &r IN s} = 0``
    >> (SPOSE_NOT_THEN STRIP_ASSUME_TAC 
       ++ `0 < x % &MIN_SET {r | 0 < r /\ &r IN s}` by METIS_TAC [INT_LT_LE]
       ++ `!y. y IN s /\ 0 < y ==> &MIN_SET {r | 0 < r /\ &r IN s} <= y` 
		by (RW_TAC std_ss [] ++ `0 <= y` by RW_TAC std_ss [INT_LT_IMP_LE]
 		++ `y = &Num y` by METIS_TAC [GSYM INT_OF_NUM] ++ POP_ORW ++ RW_TAC std_ss [INT_LE]
 		++ KNOW_TAC ``Num y IN {(r:num) | 0 < r /\ &r IN s}``
    		>> (PSET_TAC [] >> METIS_TAC [GSYM INT_OF_NUM, INT_LT]
			++ METIS_TAC [GSYM INT_OF_NUM]) ++ RW_TAC std_ss [] 
 			++ `{r | 0 < r /\ &r IN s} <> {}` by (PSET_TAC [GSYM MEMBER_NOT_EMPTY] 
			++ Q.EXISTS_TAC `Num y` ++ RW_TAC std_ss [])
 		++ (MP_TAC o Q.SPEC `{r | 0 < r /\ &r IN s}`) MIN_SET_LEM ++ RW_TAC std_ss [])
       ++ POP_ASSUM (MP_TAC o Q.SPEC `x % &MIN_SET {r | 0 < r /\ &r IN s}`) 
       ++ RW_TAC std_ss [INT_NOT_LE])
    ++ RW_TAC std_ss []
    ++ Q.EXISTS_TAC `x / &MIN_SET {(r:num) | 0 < r /\ &r IN s}`
    ++ RW_TAC std_ss [INT_DIV_MUL_ID])
 ++ RW_TAC std_ss []  
 ++ PSET_TAC [GSPECIFICATION, EXTENSION] ++ EQ_TAC 
 >> RW_TAC std_ss [] ++ RW_TAC std_ss []]);

val NUM_INT_ADD = prove (
  ``!a b.  (0 <= a) /\ (0 <= b) ==> 
	(Num (a + b) = (Num a + Num b))``,
    RW_TAC std_ss [] 
 ++ `0 <= a + b` by METIS_TAC [INT_LT_IMP_LE, INT_LE_ADD]
 ++ `0 <= a` by METIS_TAC [INT_LT_IMP_LE]
 ++ `&Num (a + b) = a + b` by RW_TAC std_ss [INT_OF_NUM]
 ++ `&Num a = a` by RW_TAC std_ss [INT_OF_NUM]
 ++ `&Num b = b` by RW_TAC std_ss [INT_OF_NUM]
 ++ `&Num a + &Num b = a + b` by METIS_TAC []
 ++ `&(Num a + Num b) = &Num a + &Num b` by METIS_TAC [GSYM INT_ADD]
 ++ `&Num (a + b) = &(Num a + Num b)` by FULL_SIMP_TAC std_ss [EQ_SYM_EQ]
 ++ METIS_TAC [INT_INJ]);

val NUM_INT_SUB = prove (
  ``!a b.  (0 < a) /\ (0 < b) /\ (0 < a - b) ==> 
	(Num (a - b) = (Num a - Num b))``,
    RW_TAC std_ss [] 
 ++ `0 <= a - b` by METIS_TAC [INT_LT_IMP_LE]
 ++ `0 <= a` by METIS_TAC [INT_LT_IMP_LE]
 ++ `0 <= b` by METIS_TAC [INT_LT_IMP_LE]
 ++ `&Num (a - b) = a - b` by RW_TAC std_ss [INT_OF_NUM]
 ++ `&Num a = a` by RW_TAC std_ss [INT_OF_NUM]
 ++ `&Num b = b` by RW_TAC std_ss [INT_OF_NUM]
 ++ `&Num a - &Num b = a - b` by METIS_TAC []
 ++ `b <= a` by METIS_TAC [INT_SUB_LE]
 ++ `Num b <= Num a` by METIS_TAC [INT_LE]
 ++ `&(Num a - Num b) = &Num a - &Num b` by METIS_TAC [INT_SUB]
 ++ `&Num (a - b) = &(Num a - Num b)` by FULL_SIMP_TAC std_ss [EQ_SYM_EQ]
 ++ METIS_TAC [INT_INJ]);

val NUM_INT_ADD_NEG = prove (
  ``!a b.  (0 < a + b) /\ (0 < a) /\ (b < 0)==> (Num (a + b) = Num a - Num (-b))``,
    RW_TAC std_ss [] 
 ++ `0 <= a + b` by METIS_TAC [INT_LT_IMP_LE]
 ++ `0 <= a` by METIS_TAC [INT_LT_IMP_LE]
 ++ `&Num (a + b) = a + b` by RW_TAC std_ss [INT_OF_NUM]
 ++ `&Num a = a` by RW_TAC std_ss [INT_OF_NUM]
 ++ `0 <= -b` by METIS_TAC [INT_NOT_LE, INT_LE_NEGTOTAL, INT_OF_NUM]
 ++ `&Num (-b) = -b` by RW_TAC std_ss [INT_OF_NUM]
 ++ `&Num a - &Num (-b) = a + b` by METIS_TAC [INT_SUB_RNEG]
 ++ `-b <= a` by METIS_TAC [GSYM INT_LE_SUB_RADD, INT_SUB_REDUCE]
 ++ `Num (-b) <= Num a` by METIS_TAC [EQ_SYM_EQ, INT_LE]
 ++ `&Num a - &Num (-b) = &(Num a - Num (-b))` by METIS_TAC [GSYM INT_SUB]
 ++ `&Num (a + b) = &(Num a - Num (-b))` by FULL_SIMP_TAC std_ss [EQ_SYM_EQ]
 ++ METIS_TAC [INT_INJ]);

val NUM_INT_MUL = prove (
  ``!a b. 0 <= a /\ 0 <= b ==> (Num (a * b) = Num a * Num b)``,
    RW_TAC std_ss [] 
 ++ `0 <= a * b` by METIS_TAC [INT_LE_MUL]
 ++ `&Num (a * b) = a * b` by RW_TAC std_ss [INT_OF_NUM]
 ++ `&Num a = a` by RW_TAC std_ss [INT_OF_NUM]
 ++ `&Num b = b` by RW_TAC std_ss [INT_OF_NUM]
 ++ `&Num a * &Num b = a * b` by RW_TAC std_ss []
 ++ `&Num a * &Num b = &(Num a * Num b)` by METIS_TAC [INT_MUL]
 ++ METIS_TAC [INT_INJ]);

val SUMI_MUL_DIVIDES_GCD = prove (
  ``!f n k m. (0 < k) /\ (!i. 0 < f i) /\ 
	(!k. 0 < k ==> 0 < sumI (0,k) (\i. n i * &f i)) /\ (m <= k) /\ (0 < m) ==> 
	divides (MAX_SET (gcd_set (IMAGE (\i. f i) (count k)))) 
	        (Num (sumI (0,m) (\i. n i * &f i)))``,
    RW_TAC std_ss []
 ++ KNOW_TAC ``!i. (i < k) ==> 
	divides (MAX_SET (gcd_set (IMAGE (\i. f i) (count k)))) (Num (&f i))``
 >> (PSET_TAC [] 
    ++ `f i IN IMAGE (\i. f i) (count k)` 
	by (PSET_TAC [IN_IMAGE] ++ Q.EXISTS_TAC `i` ++ RW_TAC std_ss [])
    ++ `IMAGE (\i. f i) (count k) <> {}` by METIS_TAC [IMAGE_NUMSET_NOTEMPTY]
    ++ `!r. r IN IMAGE (\i. f i) (count k) ==> 0 < r` by (PSET_TAC [IN_IMAGE] 
	++ `0 < f i'` by RW_TAC std_ss [] ++ METIS_TAC [GSYM INT_LT])
    ++ `gcd_set (IMAGE (\i. f i) (count k)) <> {}` by METIS_TAC [GCD_SET_THM]
    ++ `FINITE (gcd_set (IMAGE (\i. f i) (count k)))` by FULL_SIMP_TAC std_ss [FINITE_GCD_SET]
    ++ (MP_TAC o Q.SPEC `gcd_set (IMAGE (\i. f i) (count k))`) MAX_SET_DEF ++ RW_TAC std_ss []
    ++ POP_ASSUM K_TAC 
    ++ `!x y A.  y IN A /\ x IN gcd_set A ==> (?p. y = p * x)` 
	by (PSET_TAC [gcd_set_def] 
    ++ POP_ASSUM (MP_TAC o Q.SPEC `y`) ++ RW_TAC std_ss [divides_def])
    ++ POP_ASSUM (MP_TAC o Q.SPECL [`MAX_SET (gcd_set (IMAGE (\i. f i) (count k)))`, 
    	`(f:num -> num) i`, `IMAGE (\i. f i) (count k)`]) 
    ++ RW_TAC std_ss [divides_def] 
    ++ Q.EXISTS_TAC `p` ++ RW_TAC std_ss []
    ++ `0 <= f i` by METIS_TAC [LESS_IMP_LESS_OR_EQ] ++ RW_TAC std_ss [NUM_OF_INT])
 ++ RW_TAC std_ss []
 ++ `!i t. (i < k) /\ (0 <= t) ==> 
	divides (MAX_SET (gcd_set (IMAGE (\i. f i) (count k)))) (Num (t * &f i))`
	by (RW_TAC std_ss [] ++  `0 <= &f i` by METIS_TAC [LESS_IMP_LESS_OR_EQ, GSYM INT_LE] 
	    ++ `Num (t * &f i) = Num t * Num (&f i)` by RW_TAC std_ss [NUM_INT_MUL]
	    ++ METIS_TAC [MULT_COMM, DIVIDES_MULT])
 ++ Induct_on `m`
 >> RW_TAC std_ss []
 ++ RW_TAC std_ss [sumI]
 ++ Cases_on `m = 0`
 >> (RW_TAC std_ss [sumI, INT_ADD_LID] 
    ++ `0 < sumI (0, 1) (\i. n i * &(f:num -> num) i)` by RW_TAC std_ss []
    ++ FULL_SIMP_TAC std_ss [SUMI_1]
    ++ `0 < &f 0` by METIS_TAC [GSYM INT_LT]
    ++ FULL_SIMP_TAC std_ss [INT_MUL_SIGN_CASES]
    >> (`0 <= (n:num -> int) 0` by METIS_TAC [INT_LT_IMP_LE]
       ++ `0 <= &f 0` by METIS_TAC [INT_LT_IMP_LE] 
       ++ `Num (n 0 * &f 0) = Num (n 0) * Num (&f 0)` by RW_TAC std_ss [NUM_INT_MUL]
       ++ METIS_TAC [MULT_COMM, DIVIDES_MULT]) 
    ++ FULL_SIMP_TAC std_ss [INT_LT_GT])
 ++ `0 < m` by RW_TAC arith_ss [] 
 ++ `m < k` by RW_TAC arith_ss []
 ++ `m <= k` by RW_TAC arith_ss [LESS_IMP_LESS_OR_EQ]
 ++ FULL_SIMP_TAC std_ss []
 ++ `0 < sumI (0, SUC m) (\i. n i * &f i)` by RW_TAC std_ss [] 
 ++ FULL_SIMP_TAC std_ss [sumI]
 ++ `0 < sumI (0, m) (\i. n i * &f i)` by RW_TAC std_ss []
 ++ `0 <= sumI (0, m) (\i. n i * &f i)` by METIS_TAC [INT_LT_IMP_LE]
 ++ Cases_on `0 <= n m` 
 >> (`0 <= &f m` by METIS_TAC [GSYM INT_LT, INT_LT_IMP_LE]
    ++ `0 <= (n:num -> int) m * &f m` by RW_TAC std_ss [INT_LE_MUL]
    ++ RW_TAC std_ss [NUM_INT_ADD] 
    ++ MATCH_MP_TAC DIVIDES_ADD_1 
    ++ RW_TAC std_ss [])
 ++ `(n:num -> int) m < 0` by METIS_TAC [INT_NOT_LE]  
 ++ `0 <= -(n:num -> int) m` by METIS_TAC [GSYM INT_NEG_GT0, INT_LT_IMP_LE]
 ++ `0 < &f m` by METIS_TAC [GSYM INT_LT] 
 ++ `(n:num -> int) m * &(f:num -> num) m < 0` by METIS_TAC [GSYM INT_MUL_SIGN_CASES]
 ++ RW_TAC std_ss [NUM_INT_ADD_NEG]
 ++ MATCH_MP_TAC DIVIDES_SUB ++ RW_TAC std_ss [INT_NEG_LMUL]);

val GCD_OF_SET_THM = prove (
  ``!k i. (0 < k) /\ (i < k) /\ (!i. (i < k) ==> 0 < f i) ==> 
	divides (MAX_SET (gcd_set (IMAGE (\i. f i) (count k)))) (f i)``,
    PSET_TAC [] 
    ++ `f i IN IMAGE (\i. f i) (count k)` 
	by (PSET_TAC [IN_IMAGE] ++ Q.EXISTS_TAC `i` ++ RW_TAC std_ss [])
    ++ `IMAGE (\i. f i) (count k) <> {}` by METIS_TAC [IMAGE_NUMSET_NOTEMPTY]
    ++ `!r. r IN IMAGE (\i. f i) (count k) ==> 0 < r` by (PSET_TAC [IN_IMAGE] 
	++ `0 < f i` by RW_TAC std_ss [] ++ METIS_TAC [GSYM INT_LT])
    ++ `gcd_set (IMAGE (\i. f i) (count k)) <> {}` by METIS_TAC [GCD_SET_THM]
    ++ `FINITE (gcd_set (IMAGE (\i. f i) (count k)))` by FULL_SIMP_TAC std_ss [FINITE_GCD_SET]
    ++ (MP_TAC o Q.SPEC `gcd_set (IMAGE (\i. f i) (count k))`) MAX_SET_DEF ++ RW_TAC std_ss []
    ++ POP_ASSUM K_TAC 
    ++ `!x y A.  y IN A /\ x IN gcd_set A ==> (?p. y = p * x)` 
	by (PSET_TAC [gcd_set_def] ++ POP_ASSUM (MP_TAC o Q.SPEC `y`) 
    ++ RW_TAC std_ss [divides_def])
    ++ POP_ASSUM (MP_TAC o Q.SPECL [`MAX_SET (gcd_set (IMAGE (\i. f i) (count k)))`, 
    	`(f:num -> num) i`, `IMAGE (\i. f i) (count k)`]) ++ RW_TAC std_ss [divides_def] 
    ++ Q.EXISTS_TAC `p` ++ RW_TAC std_ss []);

val SUMI_MUL_INT_DIVIDES_GCD = prove (
  ``!f n k m. (0 < k) /\ (!i. (i < k) ==> 0 < f i) /\ (m <= k) ==> 
	(&MAX_SET (gcd_set (IMAGE (\i. f i) (count k)))) int_divides 
	(sumI (0,m) (\i. n i * &f i))``,
    RW_TAC std_ss []
 ++ KNOW_TAC ``!i. (i < k) ==> 
	divides (MAX_SET (gcd_set (IMAGE (\i. f i) (count k)))) (Num (&f i))``
 >> (PSET_TAC [] 
    ++ `f i IN IMAGE (\i. f i) (count k)` 
	by (PSET_TAC [IN_IMAGE] ++ Q.EXISTS_TAC `i` ++ RW_TAC std_ss [])
    ++ `IMAGE (\i. f i) (count k) <> {}` by METIS_TAC [IMAGE_NUMSET_NOTEMPTY]
    ++ `!r. r IN IMAGE (\i. f i) (count k) ==> 0 < r` by (PSET_TAC [IN_IMAGE] 
	++ `0 < f i'` by RW_TAC std_ss [] ++ METIS_TAC [GSYM INT_LT])
    ++ `gcd_set (IMAGE (\i. f i) (count k)) <> {}` by METIS_TAC [GCD_SET_THM]
    ++ `FINITE (gcd_set (IMAGE (\i. f i) (count k)))` by FULL_SIMP_TAC std_ss [FINITE_GCD_SET]
    ++ (MP_TAC o Q.SPEC `gcd_set (IMAGE (\i. f i) (count k))`) MAX_SET_DEF ++ RW_TAC std_ss []
    ++ POP_ASSUM K_TAC 
    ++ `!x y A.  y IN A /\ x IN gcd_set A ==> (?p. y = p * x)` 
	by (PSET_TAC [gcd_set_def] 
    ++ POP_ASSUM (MP_TAC o Q.SPEC `y`) ++ RW_TAC std_ss [divides_def])
    ++ POP_ASSUM (MP_TAC o Q.SPECL [`MAX_SET (gcd_set (IMAGE (\i. f i) (count k)))`, 
    	`(f:num -> num) i`, `IMAGE (\i. f i) (count k)`]) 
    ++ RW_TAC std_ss [divides_def] 
    ++ Q.EXISTS_TAC `p` ++ RW_TAC std_ss []
    ++ `0 <= f i` by METIS_TAC [LESS_IMP_LESS_OR_EQ] ++ RW_TAC std_ss [NUM_OF_INT])
 ++ RW_TAC std_ss []
 ++ `!i t. (i < k) /\ (0 <= t) ==> 
	divides (MAX_SET (gcd_set (IMAGE (\i. f i) (count k)))) (Num (t * &f i))`
	by (RW_TAC std_ss [] 
	    ++  `0 <= &f i` by METIS_TAC [LESS_IMP_LESS_OR_EQ, GSYM INT_LE] 
	    ++ `Num (t * &f i) = Num t * Num (&f i)` by RW_TAC std_ss [NUM_INT_MUL]
	    ++ METIS_TAC [MULT_COMM, DIVIDES_MULT])
 ++ Induct_on `m`
 >> RW_TAC std_ss [sumI, INT_DIVIDES_0]
 ++ RW_TAC std_ss [sumI]
 ++ Cases_on `m = 0`
 >> (RW_TAC std_ss [sumI, INT_ADD_LID] 
    ++ (MP_TAC o Q.SPECL [`(k:num)`, `(0:num)`]) GCD_OF_SET_THM 
    ++ RW_TAC std_ss [divides_def]
    ++ POP_ORW ++ RW_TAC std_ss [GSYM INT_MUL, INT_MUL_ASSOC, INT_DIVIDES] 
    ++ Q.EXISTS_TAC `n 0 * &q` ++ RW_TAC std_ss [])
 ++ `0 < m` by RW_TAC arith_ss [] ++ `m < k` by RW_TAC arith_ss []
 ++ `m <= k` by RW_TAC arith_ss [LESS_IMP_LESS_OR_EQ] 
 ++ `&MAX_SET (gcd_set (IMAGE (\i. f i) (count k))) int_divides
            sumI (0,m) (\i. n i * &f i)` by FULL_SIMP_TAC std_ss [] 
 ++ RW_TAC std_ss [INT_DIVIDES_LADD]
 ++ (MP_TAC o Q.SPECL [`(k:num)`, `(m:num)`]) GCD_OF_SET_THM 
 ++ RW_TAC std_ss [divides_def]
 ++ POP_ORW ++ RW_TAC std_ss [GSYM INT_MUL, INT_MUL_ASSOC, INT_DIVIDES] 
    ++ Q.EXISTS_TAC `n m * &q` ++ RW_TAC std_ss []);

val INT_DIVIDES_CONV_DIVIDES = prove (
  ``!a b. 0 < a /\ 0 < b /\ a int_divides b ==> divides (Num a) (Num b)``,
    RW_TAC std_ss [INT_DIVIDES]
 ++ `0 <= a` by METIS_TAC [INT_LT_IMP_LE]
 ++ KNOW_TAC ``0 < m``
 >> (SPOSE_NOT_THEN STRIP_ASSUME_TAC ++ `m <= 0` by METIS_TAC [GSYM int_le] 
    ++ Cases_on `m = 0` >> (RW_TAC std_ss [] ++ FULL_SIMP_TAC std_ss [INT_MUL_LZERO])
    ++ `m < 0` by METIS_TAC [GSYM INT_LT_LE]
    ++ `m * a < 0` by METIS_TAC [GSYM INT_MUL_SIGN_CASES] 
    ++ FULL_SIMP_TAC std_ss [INT_LT_GT])
 ++ RW_TAC std_ss []
 ++ `0 <= m` by METIS_TAC [INT_LT_IMP_LE]
 ++ `Num (m * a) = Num m * Num a` by RW_TAC std_ss [NUM_INT_MUL]
 ++ RW_TAC std_ss [divides_def] ++ Q.EXISTS_TAC `Num m` ++ RW_TAC std_ss []);

(* ------------------------------------------------------------------------- *)
(* Lemma 3: Linearity of Two Integer Sequences                               *)
(* ------------------------------------------------------------------------- *)
val GCD_OF_SET_EQ_MINSET_POSINT = prove (
  ``!(f:num -> num) k. (0 < k) /\ (!i. (i < k) ==> 0 < f i) ==>
	(?n. &MAX_SET (gcd_set (IMAGE (\i. f i) (count k))) = 
	sumI (0, k) (\i. n i * &f i))``,
    RW_TAC std_ss []
 ++ `IMAGE (\i. f i) (count k) <> {}` by METIS_TAC [IMAGE_NUMSET_NOTEMPTY]
 ++ `!r. r IN IMAGE (\i. f i) (count k) ==> 0 < r` by (PSET_TAC [IN_IMAGE] 
	++ `0 < f i'` by RW_TAC std_ss [] ++ METIS_TAC [GSYM INT_LT])
 ++ `FINITE (gcd_set (IMAGE (\i. f i) (count k)))` by FULL_SIMP_TAC std_ss [FINITE_GCD_SET]
 ++ (MP_TAC o Q.SPEC `IMAGE (\i. f i) (count k)`) GCD_SET_THM ++ RW_TAC std_ss []
 ++ (MP_TAC o Q.SPEC `gcd_set (IMAGE (\i. f i) (count k))`) MAX_SET_DEF ++ RW_TAC std_ss []
 ++ NTAC 2 (POP_ASSUM MP_TAC) 
 ++ POP_ASSUM (MP_TAC o Q.SPEC `MAX_SET (gcd_set (IMAGE (\i. f i) (count k)))`) 
 ++ RW_TAC std_ss []
 ++ FULL_SIMP_TAC std_ss []

 ++ (MP_TAC o Q.SPECL [`{r | ?n. r = sumI (0,k) (\i. n i * &f i)}`, `f`, `k`]) SUMI_CLOSE_ADD_SUM 
 ++ RW_TAC std_ss []
 ++ (MP_TAC o Q.SPECL [`f`, `k`]) POSINTSET_NOT_EMPTY ++ RW_TAC std_ss []
 ++ (MP_TAC o Q.SPECL [`f`, `k`]) POSINT_IN_SUMISET ++ RW_TAC std_ss []
 ++ KNOW_TAC ``?z. z <> 0 /\ z IN {r | ?n. r = sumI (0,k) (\i. n i * &f i)}``
 >> (RW_TAC std_ss [] ++ Q.EXISTS_TAC `n` ++ RW_TAC std_ss [INT_LT_IMP_NE])
 ++ DISCH_TAC 
 ++ (MP_TAC o Q.SPEC `{r | ?n. r = sumI (0,k) (\i. n i * &f i)}`) POSINT_MIN_SET_THM 
 ++ RW_TAC std_ss [] ++ NTAC 2 (POP_ASSUM K_TAC) ++ NTAC 4 (POP_ASSUM MP_TAC) ++ NTAC 3 (POP_ASSUM K_TAC) 
 ++ PSET_TAC [] 
 ++ (MP_TAC o Q.SPECL [`f`, `n`, `k`, `k`]) SUMI_MUL_INT_DIVIDES_GCD ++ RW_TAC std_ss [] 
 ++ `!r. r IN (IMAGE (\i. f i) (count k)) ==> 0 < r` by PSET_TAC []
 ++ `(IMAGE (\i. f i) (count k)) <> {}` by METIS_TAC [IMAGE_NUMSET_NOTEMPTY]
 ++ `0 < &MAX_SET (gcd_set (IMAGE (\i. f i) (count k)))` by METIS_TAC [GCD_SET_THM, INT_LT] 
 ++ `divides (Num &MAX_SET (gcd_set (IMAGE (\i. f i) (count k)))) (Num (sumI (0,k) (\i. n i * &f i)))`
	by METIS_TAC [INT_DIVIDES_CONV_DIVIDES] 
 ++ `sumI (0,k) (\i. n i * &f i) = &MIN_SET {r | 0 < r /\ ?n. &r = sumI (0,k) (\i. n i * &f i)}` 
	by RW_TAC std_ss [EQ_SYM_EQ] 
 ++ `divides (MAX_SET (gcd_set (IMAGE (\i. f i) (count k))))
             (MIN_SET {r | 0 < r /\ ?n. &r = sumI (0,k) (\i. n i * &f i)})` 
	by METIS_TAC [NUM_OF_INT]
 ++ `0 < MIN_SET {r | 0 < r /\ ?n. &r = sumI (0,k) (\i. n i * &f i)}` by METIS_TAC [INT_LT]
 ++ `MAX_SET (gcd_set (IMAGE (\i. f i) (count k))) <= 
	MIN_SET {r | 0 < r /\ ?n. &r = sumI (0,k) (\i. n i * &f i)}` by RW_TAC std_ss [DIVIDES_LE]
 ++ KNOW_TAC ``MIN_SET {r | 0 < r /\ ?n. &r = sumI (0,k) (\i. n i * &f i)} IN 
	gcd_set (IMAGE (\i. f i) (count k))``
 >> (PSET_TAC [gcd_set_def] ++ `0 <= f i` by RW_TAC std_ss [LESS_IMP_LESS_OR_EQ]
     ++ `0 <= &MIN_SET {r | 0 < r /\ ?n. &r = sumI (0,k) (\i. n i * &f i)}` 
	by RW_TAC std_ss [INT_LT_IMP_LE]
     ++ `f i = Num (&f i)` by METIS_TAC [NUM_OF_INT] 
     ++ `MIN_SET {r | 0 < r /\ ?n. &r = sumI (0,k) (\i. n i * &f i)} =
	Num (&MIN_SET {r | 0 < r /\ ?n. &r = sumI (0,k) (\i. n i * &f i)})` by METIS_TAC [NUM_OF_INT] 
     ++ NTAC 2 (POP_ORW) ++ NTAC 2 (POP_ASSUM K_TAC) ++ `0 < &f i` by METIS_TAC [INT_LT]
     ++ MATCH_MP_TAC INT_DIVIDES_CONV_DIVIDES ++ RW_TAC std_ss [] 
     ++ `&f i IN {r | ?n. r = sumI (0,k) (\i. n i * &f i)}` by RW_TAC std_ss [IN_SET]
     ++ `&f i IN {r | ?k'. r = k' * &MIN_SET {r | 0 < r /\ ?n. &r = sumI (0,k) (\i. n i * &f i)}}` 
		by METIS_TAC [] ++ PSET_TAC [INT_DIVIDES] ++ POP_ORW 
     ++ Q.EXISTS_TAC `k'` ++ RW_TAC std_ss [])
 ++ RW_TAC std_ss [] 
 ++ Q.PAT_ASSUM `!y.
            y IN gcd_set (IMAGE (\i. f i) (count k)) ==>
            y <= MAX_SET (gcd_set (IMAGE (\i. f i) (count k)))`
	(MP_TAC o Q.SPEC `MIN_SET {r | 0 < r /\ ?n. &r = sumI (0,k) (\i. n i * &f i)}`) 
 ++ RW_TAC std_ss []
 ++ `MIN_SET {r | 0 < r /\ ?n. &r = sumI (0,k) (\i. n i * &f i)} =
           MAX_SET (gcd_set (IMAGE (\i. f i) (count k)))` by FULL_SIMP_TAC std_ss [EQ_LESS_EQ]
 ++ `&MIN_SET {r | 0 < r /\ ?n. &r = sumI (0,k) (\i. n i * &f i)} =
           &MAX_SET (gcd_set (IMAGE (\i. f i) (count k)))` by METIS_TAC [GSYM INT_INJ]
 ++ `&MAX_SET (gcd_set (IMAGE (\i. f i) (count k))) = sumI (0,k) (\i. n i * &f i)` by METIS_TAC []
 ++ POP_ORW ++ Q.EXISTS_TAC `(n:num -> int)` ++ RW_TAC std_ss []);

val INT_EQ_TWO_POSINT_SUB = prove (
  ``!(n:num -> int). 
	(!(x:num). (0:int) <= POS_PART1 x n) /\ (!(x:num). 0 <= POS_PART2 x n) /\ 
	(!(x:num). n x = (POS_PART1 x n) - (POS_PART2 x n))``,
    RW_TAC std_ss []
 << [RW_TAC std_ss [POS_PART1_def, INT_LE_REFL],
    Cases_on `0 <= n x`
    >> FULL_SIMP_TAC std_ss [POS_PART2_def, int_le, INT_LT_REFL]
    ++ `n x < 0` by METIS_TAC [int_le] 
    ++ RW_TAC std_ss [POS_PART2_def, INT_NEG_GT0, INT_LT_IMP_LE],
    Cases_on `0 <= n x`
    >> FULL_SIMP_TAC std_ss [POS_PART1_def, POS_PART2_def, int_le, INT_SUB_RZERO] 
    ++ `n x < 0` by METIS_TAC [int_le] 
    ++ RW_TAC std_ss [POS_PART1_def, POS_PART2_def, INT_SUB_LZERO, INT_NEGNEG]]);

val SUMI_EQ_TWO_SUMI_SUB = prove (
  ``!a n k. (sumI (0, k) (\i. n i * &a i) = 
	sumI (0, k) (\i. POS_PART1 i n * &a i) - sumI (0, k) (\i. POS_PART2 i n * &a i))``,
    RW_TAC std_ss []
 ++ `!(x:num). n x = (POS_PART1 x n) - (POS_PART2 x n)` by METIS_TAC [INT_EQ_TWO_POSINT_SUB]
 ++ `sumI (0,k) (\i. n i * &a i) = sumI (0, k) (\i. (POS_PART1 i n - POS_PART2 i n) * &a i)`
	by RW_TAC std_ss [] ++ POP_ORW ++ POP_ASSUM K_TAC 
 ++ RW_TAC std_ss [INT_SUB_RDISTRIB, SUMI_SUB]);

val SUMI_PART1_POS = prove (
  ``!(n:num -> int) k (a:num -> num). (0 < sumI (0, k) (\x. n x * &(a x))) /\ (0 < k) /\ 
	(!i. i < k ==> (0 < a i)) ==> 
	((0:int) < sumI (0, k) (\x. POS_PART1 x n * &(a x)))``,
    RW_TAC std_ss []
 ++ KNOW_TAC ``!m. (0 < m) /\ (m <= k) ==> (0:int) <= sumI (0, m) (\x. POS_PART2 x n * &(a x))``
 >> (Induct_on `m` >> RW_TAC std_ss []
    ++ RW_TAC std_ss [sumI] 
    ++ Cases_on `m = 0` 
    >> (RW_TAC std_ss [sumI, INT_ADD_LID, POS_PART2_def] 
       >> (`0 < -n 0` by METIS_TAC [INT_NEG_GT0]
	  ++ `0 < a 0` by RW_TAC std_ss [] ++ METIS_TAC [INT_LT, INT_LT_IMP_LE, INT_LE_MUL])
       ++ RW_TAC std_ss [INT_MUL_LZERO, INT_LE_REFL])
    ++ `0 < m` by DECIDE_TAC ++ `m <= k` by DECIDE_TAC ++ FULL_SIMP_TAC std_ss []
    ++ KNOW_TAC ``0 <= POS_PART2 m n * &a m``
    >> (RW_TAC std_ss [POS_PART2_def] 
	>> (`0 < -n m` by METIS_TAC [INT_NEG_GT0] ++ `m < k` by DECIDE_TAC
	   ++ `0 < a m` by RW_TAC std_ss [] ++ METIS_TAC [INT_LT, INT_LT_IMP_LE, INT_LE_MUL])
        ++ RW_TAC std_ss [INT_MUL_LZERO, INT_LE_REFL])
    ++ RW_TAC std_ss [INT_LE_ADD])
 ++ RW_TAC std_ss [] ++ `0 <= sumI (0, k) (\x. POS_PART2 x n * &a x)` by RW_TAC std_ss []
 ++ KNOW_TAC ``!m. (0 < m) /\ (m <= k) ==> (0:int) <= sumI (0, m) (\x. POS_PART1 x n * &(a x))``
 >> (Induct_on `m` >> RW_TAC std_ss []
    ++ RW_TAC std_ss [sumI] 
    ++ Cases_on `m = 0` 
    >> (RW_TAC std_ss [sumI, INT_ADD_LID, POS_PART1_def] 
       >> (`0 < k` by DECIDE_TAC ++ `0 < a 0` by RW_TAC std_ss [] 
          ++ METIS_TAC [INT_LT, INT_LT_IMP_LE, INT_LE_MUL]) 
       ++ RW_TAC std_ss [INT_MUL_LZERO, INT_LE_REFL])
    ++ `0 < m` by DECIDE_TAC ++ `m <= k` by DECIDE_TAC ++ FULL_SIMP_TAC std_ss []  
    ++ KNOW_TAC ``0 <= POS_PART1 m n * &a m``
    >> (RW_TAC std_ss [POS_PART1_def] 
       >> (`m < k` by DECIDE_TAC ++ `0 < a m` by RW_TAC std_ss [] 
	  ++ METIS_TAC [INT_LT, INT_LT_IMP_LE, INT_LE_MUL])
       ++ RW_TAC std_ss [INT_MUL_LZERO, INT_LE_REFL])
    ++ RW_TAC std_ss [INT_LE_ADD])
 ++ RW_TAC std_ss [] ++ `0 <= sumI (0, k) (\x. POS_PART1 x n * &a x)` by RW_TAC std_ss []
 ++ `0 < sumI (0, k) (\x. POS_PART1 x n * &a x) - sumI (0, k) (\x. POS_PART2 x n * &a x)`
	by METIS_TAC [SUMI_EQ_TWO_SUMI_SUB]
 ++ KNOW_TAC ``sumI (0,k) (\x. POS_PART1 x n * &a x) <> 0``
 >> (SPOSE_NOT_THEN STRIP_ASSUME_TAC 
    ++ `-sumI (0,k) (\x. POS_PART2 x n * &a x) <= 0` by METIS_TAC [INT_NEG_LE0] 
    ++ METIS_TAC [INT_SUB_LZERO, INT_NOT_LE])
 ++ RW_TAC std_ss [INT_LT_LE]);

val INT_MUL_IN_SET = prove (
  ``!s P M. (!x y. x IN s /\ y IN s ==> (x + y) IN s) /\ 
  		(P IN s) /\ (0 < M) ==>	(P * M IN s)``,
			RW_TAC std_ss []
 ++ `0 <= M` by METIS_TAC [INT_LT_IMP_LE]
 ++ `M = &Num M` by METIS_TAC [INT_OF_NUM]
 ++ `0 < Num M` by METIS_TAC [INT_LT]
 ++ Induct_on `Num M` >> RW_TAC std_ss []
 ++ RW_TAC std_ss [] ++ `M = &(SUC v)` by METIS_TAC [] ++ POP_ORW
 ++ `&SUC v = &v + 1` by METIS_TAC [ADD1, INT_ADD] ++ POP_ORW 
 ++ RW_TAC std_ss [INT_LDISTRIB, INT_MUL_RID]
 ++ NTAC 5 (POP_ASSUM MP_TAC) ++ POP_ASSUM (MP_TAC o Q.SPEC `&v`) ++ RW_TAC std_ss []
 ++ Cases_on `v = 0` >> METIS_TAC [INT_OF_NUM, INT_MUL_RZERO, INT_ADD_LID]
 ++ `0 < v` by DECIDE_TAC 
 ++ `P * &v IN s` by METIS_TAC [INT_LT, NUM_OF_INT, NUM_OF_INT, INT_LT_IMP_LE]
 ++ FULL_SIMP_TAC std_ss []);

val N_IN_SET = prove (
  ``!s a (r:int) P M. (!x y. x IN s /\ y IN s ==> (x + y) IN s) /\ (P IN s) /\  
  		(M IN s) /\ (0 <= r) /\ (r < a) ==> ((a - r) * P + r * M IN s)``,
		RW_TAC std_ss []  		
 ++ `0 < a - r` by METIS_TAC [INT_SUB_LT]
 ++ (MP_TAC o Q.SPECL [`s`, `P`, `(a - r)`]) INT_MUL_IN_SET ++ RW_TAC std_ss []
 ++ Cases_on `r = 0` >> RW_TAC std_ss [INT_MUL_LZERO, INT_ADD_RID, INT_MUL_COMM]
 ++ `0 < r` by METIS_TAC [INT_LT_LE]
 ++ (MP_TAC o Q.SPECL [`s`, `M`, `r`]) INT_MUL_IN_SET ++ RW_TAC std_ss []
 ++ METIS_TAC [INT_MUL_COMM]);

val EXIST_INT_COND = prove (                    
  ``!p n. (p * (p - 1) <= n) /\ (0 < p) /\ (0 < n) ==> 
	?a r. (n = a * p + r) /\ (r <= p - 1) /\ (0 <= r) /\ ((p - 1) <= a)``,
    RW_TAC std_ss [] 
 ++ `0 <= (p:int)` by METIS_TAC [INT_LT_IMP_LE]
 ++ `p = &Num p` by METIS_TAC [INT_OF_NUM]
 ++ `0 < Num p` by METIS_TAC [INT_LT]
 ++ `0 <= (n:int)` by METIS_TAC [INT_LT_IMP_LE]
 ++ `n = &Num n` by METIS_TAC [INT_OF_NUM]
 ++ (MP_TAC o Q.SPECL [`Num n`, `Num p`]) DA ++ RW_TAC std_ss [] 
 ++ `&Num n = &(q * Num p + r)` by METIS_TAC [RAND_THM]
 ++ Q.EXISTS_TAC `&q` ++ Q.EXISTS_TAC `&r` ++ RW_TAC std_ss []	
 << [`&(q * Num p + r) = &q * p + &r` by METIS_TAC [INT_ADD, INT_MUL, EQ_SYM_EQ]
     ++ METIS_TAC [],

     `r <= Num p - 1` by RW_TAC std_ss [SUB_LESS_OR] ++ `&r <= &(Num p - 1)` by METIS_TAC [INT_LE]
     ++ `1 <= p` by METIS_TAC [INT_LT_LE1, INT_ADD_LID] 
     ++ `1 <= &Num p` by METIS_TAC [] ++ `(1:num) <= Num p` by METIS_TAC [INT_LE]
     ++ (MP_TAC o Q.SPECL [`Num p`, `(1:num)`]) INT_SUB ++ RW_TAC std_ss [] 
     ++ METIS_TAC [EQ_SYM_EQ, INT_OF_NUM],

     `(0:num) <= r` by RW_TAC arith_ss [] ++ METIS_TAC [INT_LE],

     `1 <= Num p` by RW_TAC arith_ss [] 
     ++ Cases_on `Num p = 1` 
     >> (`Num p - 1 = 0` by RW_TAC arith_ss [] 
        ++ `p - 1 = &(Num p - 1)` by METIS_TAC [INT_SUB] 
        ++ METIS_TAC [SUB_EQUAL_0, ZERO_LESS_EQ, INT_LE])
     ++ `2 <= Num p` by RW_TAC arith_ss [] 
     ++ Cases_on `Num p = 2` 
     >> (`Num p - 1 = 1` by RW_TAC arith_ss [] 
        ++ `Num n = q * 2 + r` by RW_TAC arith_ss [] ++ `p = 2` by METIS_TAC [INT_INJ]
        ++ `p - 1 = 1` by METIS_TAC [INT_INJ, INT_OF_NUM, INT_SUB, NUM_OF_INT]
	++ FULL_SIMP_TAC arith_ss [NUM_OF_INT, INT_MUL_RID] 
	++ SPOSE_NOT_THEN STRIP_ASSUME_TAC ++ `q < 1` by METIS_TAC [INT_NOT_LE, INT_LT]
        ++ `q = 0` by RW_TAC arith_ss [] ++ `&(2 * q + r) = &r` by METIS_TAC [MULT_0, ADD]
        ++ `2 <= r` by METIS_TAC [INT_LE] ++ METIS_TAC [NOT_LESS])
    ++ `2 < Num p` by RW_TAC arith_ss [] ++ `1 <= Num p` by RW_TAC arith_ss []
    ++ `p - 1 = &(Num p - 1)` by METIS_TAC [INT_SUB] ++ SPOSE_NOT_THEN STRIP_ASSUME_TAC 
    ++ `&q < p - 1` by METIS_TAC [INT_NOT_LE] ++ `q < (Num p - 1)` by METIS_TAC [INT_LT]
    ++ `q <= Num p - 2` by RW_TAC arith_ss [SUB_LESS_OR] 
    ++ `q * Num p + r <= (Num p - 2) * Num p + r` by METIS_TAC [LESS_MONO_MULT, LESS_EQ_MONO_ADD_EQ]
    ++ `(Num p - 2) * Num p + r < (Num p - 2) * Num p + 1 * Num p` 
		by METIS_TAC [LT_ADD_LCANCEL, MULT_LEFT_1]
    ++ `(Num p - 2) * Num p + 1 * Num p = (Num p - 2 + 1) * Num p` by METIS_TAC [RIGHT_ADD_DISTRIB] 
    ++ KNOW_TAC ``Num p - 2 + 1 = Num p - 1``
    >> (NTAC 10 (POP_ASSUM K_TAC) ++ `Num p - 2 + 1 = Num p + 1 - 2` by RW_TAC arith_ss [SUB_LESS_OR]
       ++ `Num p + 1 - 2 =  Num p - (2 - 1)` by RW_TAC arith_ss [SUB_SUB] 
       ++ FULL_SIMP_TAC arith_ss [])
    ++ DISCH_TAC ++ `q * Num p + r < (Num p - 1) * Num p` by METIS_TAC [LESS_EQ_LESS_TRANS]
    ++ `&(q * Num p + r) < &(Num p - 1) * &Num p` by METIS_TAC [INT_LT, INT_MUL]
    ++ `&Num n < (p - 1) * p` by METIS_TAC [INT_SUB, INT_OF_NUM] 
    ++ `n < p * (p - 1)` by METIS_TAC [INT_OF_NUM, INT_MUL_COMM] ++ METIS_TAC [INT_NOT_LE]]);

val MULTI_FUN_IN_SET = prove (
  ``!(a:num) (k:num) s. (!x y. x IN s /\ y IN s ==> (x + y) IN s) /\ 
	(0 < k) /\ (a IN s) ==> (k * a IN s)``,
    Induct_on `k`
 >> RW_TAC std_ss []
 ++ RW_TAC std_ss [ADD1, RIGHT_ADD_DISTRIB] 
 ++ Cases_on `k = 0` >> RW_TAC std_ss [MULT, ADD]
 ++ `0 < k` by DECIDE_TAC ++ FULL_SIMP_TAC std_ss []);

val NUM_IN_SET = prove (
  ``!s a (r:num) P M. (!x y. x IN s /\ y IN s ==> (x + y) IN s) /\ (P IN s) /\  
  		(M IN s) /\ (0 <= r) /\ (r < a) ==> ((a - r) * P + r * M IN s)``,
    RW_TAC std_ss []  		
 ++ `0 < a - r` by METIS_TAC [SUB_LESS_0]
 ++ (MP_TAC o Q.SPECL [`P`, `a - r`, `s`]) MULTI_FUN_IN_SET ++ RW_TAC std_ss []
 ++ Cases_on `r = 0` >> METIS_TAC [MULT, ADD_0]
 ++ `0 < r` by RW_TAC arith_ss [] 
 ++ (MP_TAC o Q.SPECL [`M`, `r`, `s`]) MULTI_FUN_IN_SET ++ RW_TAC std_ss []);

val EXIST_NUM_COND = prove (                    
  ``!p (n:num). (p * (p - 1) <= n) /\ (1 <= p) ==> 
	?a r. (n = a * p + r) /\ (r <= p - 1) /\ ((p - 1) <= a)``,
    RW_TAC std_ss [] 
 ++ `0 < (p:num)` by RW_TAC arith_ss []
 ++ Cases_on `p = 1` >> RW_TAC std_ss [MULT_RIGHT_1]
 ++ `2 <= (p:num)` by RW_TAC arith_ss []
 ++ `1 <= (2:num)` by RW_TAC arith_ss [] 
 ++ `p - 2 + 1 = p - 1` by RW_TAC arith_ss [SUB_RIGHT_ADD, SUB_SUB] 
 ++ (MP_TAC o Q.SPECL [`n`, `p`]) DA ++ RW_TAC std_ss [] 
 ++ Q.EXISTS_TAC `q` ++ Q.EXISTS_TAC `r` ++ RW_TAC std_ss []	
 >> METIS_TAC [SUB_LESS_OR] 
 ++ SPOSE_NOT_THEN STRIP_ASSUME_TAC 
 ++ KNOW_TAC ``q * p + r < (p - 1) * (p:num)``
 >> (NTAC 7 (POP_ASSUM MP_TAC) ++ POP_ASSUM K_TAC ++ RW_TAC std_ss [] 
    ++ `1 + q < (p:num)` by RW_TAC arith_ss [] ++ `(q:num) <= p - 2` by RW_TAC arith_ss [] 
    ++ `q * p + r <= (p - 2) * p + r` by RW_TAC arith_ss [LESS_MONO_MULT, LESS_EQ_MONO_ADD_EQ] 
    ++ `(p - 2) * p + r < (p - 2) * p + p` by RW_TAC arith_ss [LT_ADD_LCANCEL] 
    ++ `(p - 2) * p + p = (p - 2 + 1) * p` by METIS_TAC [MULT_LEFT_1, RIGHT_ADD_DISTRIB] 
    ++ METIS_TAC [LESS_EQ_LESS_TRANS]) ++ DISCH_TAC ++ RW_TAC arith_ss []);

val POS_PART2_LT = prove (
 ``!(n:num -> int) k (f:num -> num). (?i. i < k /\ n i < 0) /\ (0 < k) /\ 
	(!i. i < k ==> 2 <= f i) ==> (2 <= sumI (0, k) (\i. POS_PART2 i n * &f i))``,
    Induct_on `k` >> RW_TAC std_ss []
 ++ RW_TAC std_ss [sumI]
 ++ `!i. 0 <= POS_PART2 i n` by METIS_TAC [INT_EQ_TWO_POSINT_SUB]
 ++ `!i. i < k ==> 0 <= f i` by RW_TAC arith_ss []
 ++ `!i. i < k ==> 0 <= &f i` by METIS_TAC [INT_LE]
 ++ `!i. i < k ==> 0 <= POS_PART2 i n * &f i` by RW_TAC std_ss [INT_LE_MUL]
 ++ `0 <= sumI (0,k) (\i. POS_PART2 i n * &f i)` by RW_TAC std_ss [SUMI_NFUN_POS]
 ++ Cases_on `i = k` 
 >> (KNOW_TAC ``2 <= POS_PART2 k n * &f k``
    >> (RW_TAC std_ss [POS_PART2_def] ++ `0 < -(n:num ->int) i` by METIS_TAC [INT_NEG_GT0]
        ++ `1 <= -(n:num ->int) i` by METIS_TAC [INT_LT_LE1, INT_ADD_LID]
	++ `2 <= &f i` by METIS_TAC [INT_LE] 
        ++ `0 <= -(n:num ->int) i` by METIS_TAC [INT_LT_01, INT_LTE_TRANS, INT_LT_IMP_LE]
        ++ `0 <= (2:num)` by RW_TAC arith_ss [] ++ `0 <= (2:int)` by METIS_TAC [NUM_OF_INT, INT_LE]
	++ `0 <= &f i` by METIS_TAC [INT_LE_TRANS]
	++ (MP_TAC o Q.SPECL [`1`, `-(n:num -> int) i`, `2`, `&(f:num -> num) i`]) INT_LT_MUL1 
	++ RW_TAC std_ss [INT_LT_01, INT_LT_IMP_LE, INT_MUL_LID])
    ++ RW_TAC std_ss [] ++ `(2:int) = 0 + 2` by METIS_TAC [INT_ADD_LID] ++ POP_ORW
    ++ METIS_TAC [INT_LE_ADD2])
 ++ `i < k` by RW_TAC arith_ss [] 
 ++ KNOW_TAC ``k <> (0:num)``
 >> (SPOSE_NOT_THEN STRIP_ASSUME_TAC ++ `0 <= i` by RW_TAC std_ss [ZERO_LESS_EQ] 
    ++ METIS_TAC [NOT_LESS]) ++ `0 < k` by RW_TAC arith_ss [] ++ RW_TAC std_ss [] ++ POP_ASSUM K_TAC
 ++ KNOW_TAC ``2 <= sumI (0,k) (\i. POS_PART2 i n * &f i)``
 >> (FIRST_X_ASSUM MATCH_MP_TAC ++ RW_TAC arith_ss [] ++ Q.EXISTS_TAC `i` ++ RW_TAC std_ss [])
 ++ RW_TAC std_ss []
 ++ `0 <= f k` by RW_TAC arith_ss []
 ++ `0 <= POS_PART2 k n` by RW_TAC std_ss []
 ++ `0 <= POS_PART2 k n * &f k` by METIS_TAC [INT_LE, INT_LE_MUL]
 ++ `(2:int) = 2 + 0` by METIS_TAC [INT_ADD_RID] ++ POP_ORW
 ++ METIS_TAC [INT_LE_ADD2]);

val POS_PART1_IN_SET = prove (
 ``!(n:num -> int) k (f:num -> num) s. (0 < k) /\ (IMAGE (\i. f i) (count k) SUBSET s) /\
        (!x y. x IN s /\ y IN s ==> (x + y) IN s) /\ (!i. i < k ==> 0 < f i) /\ 
	(0 < sumI (0, k) (\i. POS_PART1 i n * &f i)) ==> 
	(Num (sumI (0, k) (\i. POS_PART1 i n * &f i)) IN s)``,
    Induct_on `k` >> RW_TAC std_ss []
 ++ RW_TAC std_ss [sumI] ++ `!k. 0 <= POS_PART1 k n` by METIS_TAC [INT_EQ_TWO_POSINT_SUB]
 ++ `!r. r < SUC k ==> (f:num -> num) r IN s` by (PSET_TAC [] 
	++ KNOW_TAC ``(?i. ((f:num -> num) r = f i) /\ i < SUC k)`` 
        >> (RW_TAC std_ss [] ++ Q.EXISTS_TAC `(r:num)` ++ RW_TAC arith_ss []) 
	++ DISCH_TAC ++ RW_TAC std_ss [])
 ++ `!i. i < k ==> 0 < (f:num -> num) i` by RW_TAC arith_ss []
 ++ `!i. i < k ==> 0 <= &f i` by METIS_TAC [INT_LT, INT_LT_IMP_LE]
 ++ `!i. i < k ==> 0 <= POS_PART1 i n * &f i` by RW_TAC std_ss [INT_LE_MUL]
 ++ Cases_on `k = 0` 
 >> (PSET_TAC [sumI, INT_ADD_LID, COUNT_ONE, GSPEC_EQ, GSPECIFICATION, EXTENSION] 
    ++ `(f:num -> num) 0 IN s` by RW_TAC arith_ss [] 
    ++ `POS_PART1 0 n <> 0` by (SPOSE_NOT_THEN STRIP_ASSUME_TAC 
    	++ METIS_TAC [INT_MUL_LZERO, INT_LT_REFL])
    ++ `0 <= POS_PART1 0 n` by METIS_TAC [INT_LT_LE, INT_LT_IMP_LE] 
    ++ `0 <= &(f:num -> num) 0` by RW_TAC arith_ss [INT_LT_IMP_LE, INT_LE]
    ++ `Num (POS_PART1 0 n * &f 0) = Num (POS_PART1 0 n) * (f 0)` 
	by METIS_TAC [INT_LT_IMP_LE, NUM_INT_MUL, NUM_OF_INT] ++ POP_ORW 
    ++ `(POS_PART1 0 n) = &Num (POS_PART1 0 n)` by METIS_TAC [INT_LT_IMP_LE, INT_OF_NUM]
    ++ `0 < Num (POS_PART1 0 n)` by METIS_TAC [INT_LT_LE, INT_LT] 
    ++ RW_TAC std_ss [MULTI_FUN_IN_SET])
 ++ `0 < k` by RW_TAC arith_ss []
 ++ Cases_on `sumI (0,k) (\i. POS_PART1 i n * &f i) = 0`
 >> (FULL_SIMP_TAC std_ss [INT_ADD_LID] 
    ++ `(f:num -> num) k IN s` by RW_TAC arith_ss []
    ++ `POS_PART1 k n <> 0` by (SPOSE_NOT_THEN STRIP_ASSUME_TAC 
    ++ METIS_TAC [INT_MUL_LZERO, INT_LT_REFL])
    ++ `0 <= &(f:num -> num) k` by RW_TAC arith_ss [INT_LT_IMP_LE, INT_LE]
    ++ `0 < POS_PART1 k n` by METIS_TAC [INT_LT_LE] 
    ++ `Num (POS_PART1 k n * &f k) = Num (POS_PART1 k n) * (f k)` 
	by METIS_TAC [INT_LT_IMP_LE, NUM_INT_MUL, NUM_OF_INT] ++ POP_ORW 
    ++ `(POS_PART1 k n) = &Num (POS_PART1 k n)` 
    	by METIS_TAC [INT_LT_IMP_LE, INT_OF_NUM]
    ++ `0 < Num (POS_PART1 k n)` by METIS_TAC [INT_LT] 
    ++ RW_TAC std_ss [MULTI_FUN_IN_SET])
 ++ `0 <= sumI (0,k) (\i. POS_PART1 i n * &f i)` by RW_TAC std_ss [SUMI_NFUN_POS]
 ++ `0 < sumI (0,k) (\i. POS_PART1 i n * &f i)` by METIS_TAC [INT_LT_LE]
 ++ `0 <= &(f:num -> num) k` by RW_TAC arith_ss [INT_LT_IMP_LE, INT_LE]
 ++ `0 <= POS_PART1 k n * &(f:num -> num) k` by METIS_TAC [INT_LE_MUL]
 ++ `Num (sumI (0,k) (\i. POS_PART1 i n * &f i) + POS_PART1 k n * &f k) = 
     Num (sumI (0,k) (\i. POS_PART1 i n * &f i)) + Num (POS_PART1 k n * &f k)` 
	by METIS_TAC [NUM_INT_ADD] ++ POP_ORW 
 ++ `IMAGE (\i. (f:num -> num) i) (count k) SUBSET IMAGE (\i. f i) (count (SUC k))` 
	by (MATCH_MP_TAC IMAGE_SUBSET ++ RW_TAC arith_ss [COUNT_SUBSET])
 ++ `IMAGE (\i. (f:num -> num) i) (count k) SUBSET s` by METIS_TAC [SUBSET_TRANS]
 ++ `Num (sumI (0,k) (\i. POS_PART1 i (n:num -> int) * &(f:num -> num) i)) IN s` by METIS_TAC []
 ++ Cases_on `POS_PART1 k n = 0` >> RW_TAC std_ss [INT_MUL_LZERO, NUM_OF_INT]
 ++ `0 < POS_PART1 k n` by METIS_TAC [INT_LT_LE]
 ++ `Num (POS_PART1 k n * &f k) = Num (POS_PART1 k n) * (f k)` 
	by METIS_TAC [INT_LT_IMP_LE, NUM_INT_MUL, NUM_OF_INT] ++ POP_ORW 
 ++ `(POS_PART1 k n) = &Num (POS_PART1 k n)` 
 	by METIS_TAC [INT_LT_IMP_LE, INT_OF_NUM]
 ++ `0 < Num (POS_PART1 k n)` by METIS_TAC [INT_LT]
 ++ RW_TAC arith_ss [MULTI_FUN_IN_SET]);

val POS_PART2_IN_SET = prove (
 ``!(n:num -> int) k (f:num -> num) s. 
 	(0 < k) /\ (IMAGE (\i. f i) (count k) SUBSET s) /\
        (!x y. x IN s /\ y IN s ==> (x + y) IN s) /\ (!i. i < k ==> 0 < f i) /\ 
	(0 < sumI (0, k) (\i. POS_PART2 i n * &f i)) ==> 
	(Num (sumI (0, k) (\i. POS_PART2 i n * &f i)) IN s)``,
    Induct_on `k` >> RW_TAC std_ss []
 ++ RW_TAC std_ss [sumI] 
 ++ `!k. 0 <= POS_PART2 k n` by METIS_TAC [INT_EQ_TWO_POSINT_SUB]
 ++ `!r. r < SUC k ==> (f:num -> num) r IN s` by (PSET_TAC [] 
	++ KNOW_TAC ``(?i. ((f:num -> num) r = f i) /\ i < SUC k)`` 
        >> (RW_TAC std_ss [] 
           ++ Q.EXISTS_TAC `(r:num)` 
           ++ RW_TAC arith_ss []) 
	++ DISCH_TAC ++ RW_TAC std_ss [])
 ++ `!i. i < k ==> 0 < (f:num -> num) i` by RW_TAC arith_ss []
 ++ `!i. i < k ==> 0 <= &f i` by METIS_TAC [INT_LT, INT_LT_IMP_LE]
 ++ `!i. i < k ==> 0 <= POS_PART2 i n * &f i` 
 	by RW_TAC std_ss [INT_LE_MUL]
 ++ Cases_on `k = 0` 
 >> (PSET_TAC [sumI, INT_ADD_LID, COUNT_ONE, GSPEC_EQ, GSPECIFICATION, EXTENSION] 
    ++ `(f:num -> num) 0 IN s` by RW_TAC arith_ss [] 
    ++ `POS_PART2 0 n <> 0` by (SPOSE_NOT_THEN STRIP_ASSUME_TAC 
    ++ METIS_TAC [INT_MUL_LZERO, INT_LT_REFL])
    ++ `0 < POS_PART2 0 n` by METIS_TAC [INT_LT_LE] 
    ++ `0 <= &(f:num -> num) 0` by RW_TAC arith_ss [INT_LT_IMP_LE, INT_LE]
    ++ `Num (POS_PART2 0 n * &f 0) = Num (POS_PART2 0 n) * (f 0)` 
	by METIS_TAC [INT_LT_IMP_LE, NUM_INT_MUL, NUM_OF_INT] ++ POP_ORW 
    ++ `(POS_PART2 0 n) = &Num (POS_PART2 0 n)` 
    	by METIS_TAC [INT_LT_IMP_LE, INT_OF_NUM]
    ++ `0 < Num (POS_PART2 0 n)` by METIS_TAC [INT_LT] 
    ++ RW_TAC std_ss [MULTI_FUN_IN_SET])
 ++ `0 < k` by RW_TAC arith_ss []
 ++ Cases_on `sumI (0,k) (\i. POS_PART2 i n * &f i) = 0`
 >> (FULL_SIMP_TAC std_ss [INT_ADD_LID] 
    ++ `(f:num -> num) k IN s` by RW_TAC arith_ss []
    ++ `POS_PART2 k n <> 0` by (SPOSE_NOT_THEN STRIP_ASSUME_TAC 
    	++ METIS_TAC [INT_MUL_LZERO, INT_LT_REFL])
    ++ `0 <= &(f:num -> num) k` by RW_TAC arith_ss [INT_LT_IMP_LE, INT_LE]
    ++ `0 < POS_PART2 k n` by METIS_TAC [INT_LT_LE] 
    ++ `Num (POS_PART2 k n * &f k) = Num (POS_PART2 k n) * (f k)` 
	by METIS_TAC [INT_LT_IMP_LE, NUM_INT_MUL, NUM_OF_INT] ++ POP_ORW 
    ++ `(POS_PART2 k n) = &Num (POS_PART2 k n)` 
    	by METIS_TAC [INT_LT_IMP_LE, INT_OF_NUM]
    ++ `0 < Num (POS_PART2 k n)` by METIS_TAC [INT_LT] 
    ++ RW_TAC std_ss [MULTI_FUN_IN_SET])
 ++ `0 <= sumI (0,k) (\i. POS_PART2 i n * &f i)` by RW_TAC std_ss [SUMI_NFUN_POS]
 ++ `0 < sumI (0,k) (\i. POS_PART2 i n * &f i)` by METIS_TAC [INT_LT_LE]
 ++ `0 <= &(f:num -> num) k` by RW_TAC arith_ss [INT_LT_IMP_LE, INT_LE]
 ++ `0 <= POS_PART2 k n * &(f:num -> num) k` by METIS_TAC [INT_LE_MUL]
 ++ `Num (sumI (0,k) (\i. POS_PART2 i n * &f i) + POS_PART2 k n * &f k) = 
     Num (sumI (0,k) (\i. POS_PART2 i n * &f i)) + Num (POS_PART2 k n * &f k)` 
	by METIS_TAC [NUM_INT_ADD] ++ POP_ORW 
 ++ `IMAGE (\i. (f:num -> num) i) (count k) SUBSET IMAGE (\i. f i) (count (SUC k))` 
	by (MATCH_MP_TAC IMAGE_SUBSET 
           ++ RW_TAC arith_ss [COUNT_SUBSET])
 ++ `IMAGE (\i. (f:num -> num) i) (count k) SUBSET s` by METIS_TAC [SUBSET_TRANS]
 ++ `Num (sumI (0,k) (\i. POS_PART2 i (n:num -> int) * &(f:num -> num) i)) IN s` 
 	by METIS_TAC []
 ++ Cases_on `POS_PART2 k n = 0` 
 >> RW_TAC std_ss [INT_MUL_LZERO, NUM_OF_INT]
 ++ `0 < POS_PART2 k n` by METIS_TAC [INT_LT_LE]
 ++ `Num (POS_PART2 k n * &f k) = Num (POS_PART2 k n) * (f k)` 
	by METIS_TAC [INT_LT_IMP_LE, NUM_INT_MUL, NUM_OF_INT] ++ POP_ORW 
 ++ `(POS_PART2 k n) = &Num (POS_PART2 k n)` by METIS_TAC [INT_LT_IMP_LE, INT_OF_NUM]
 ++ `0 < Num (POS_PART2 k n)` by METIS_TAC [INT_LT]
 ++ RW_TAC arith_ss [MULTI_FUN_IN_SET]);

val EXISTS_NEG_FUN = prove (
  ``!(n:num -> int) k (f:num -> num). (0 < k) /\ (!i. i < k ==> 2 <= f i) /\ 
	(?i. i < k /\ 0 < n i) /\ (sumI (0, k) (\i. n i * &f i) = 1) ==> 
	(?i. i < k /\ n i < 0)``,
    RW_TAC std_ss [] 
 ++ `0 < sumI (0,k) (\i. n i * &f i)` by RW_TAC std_ss [INT_LT_01] 
 ++ `!i. i < k ==> 0 <= f i` by RW_TAC arith_ss []
 ++ `!i. i < k ==> 0 <= &f i` by METIS_TAC [INT_LE]
 ++ Cases_on `i = k - 1` 
 >> (`k = SUC (k - 1)` by RW_TAC arith_ss [] 
    ++ `sumI (0,k) (\i. n i * &f i) = sumI (0, SUC (k - 1)) (\i. n i * &f i)` by METIS_TAC []
    ++ FULL_SIMP_TAC std_ss [sumI] 
    ++ NTAC 2 (POP_ASSUM K_TAC)
    ++ `1 <= (n:num -> int) (k - 1)` by METIS_TAC [INT_LT_LE1, INT_ADD_LID] 
    ++ `2 <= f (k - 1)` by RW_TAC arith_ss []
    ++ `2 <= &f (k - 1)` by METIS_TAC [INT_LE]
    ++ `2 <= (n:num -> int) (k - 1) * &f (k - 1)`
	by (RW_TAC std_ss [] 
	   ++ `(0:num) < 2` by RW_TAC arith_ss [] 
	   ++ `(0:int) < 2` by METIS_TAC [INT_LT]
	   ++ `(2:int) = 1 * 2` by  METIS_TAC [INT_MUL_LID] ++ POP_ORW 
	   ++ MATCH_MP_TAC INT_LT_MUL1 
	   ++ RW_TAC std_ss [INT_LT_01, INT_LT_IMP_LE])
    ++ `sumI (0,k - 1) (\i. n i * &f i) + 2 <= sumI (0,k - 1) (\i. n i * &f i) + 
	(n:num -> int) (k - 1) * &f (k - 1)` by METIS_TAC [INT_LE_LADD]
    ++ `sumI (0,k - 1) (\i. (n:num -> int) i * &(f:num -> num) i) + 2 <= 1` 
    	by METIS_TAC []
    ++ `sumI (0,k - 1) (\i. (n:num -> int) i * &(f:num -> num) i) <= 1 - 2` 
		by METIS_TAC [INT_LE_SUB_LADD]
    ++ `1 - (2:int) < 0` by (`(1:num) < 2` by RW_TAC arith_ss [] 
		++ RW_TAC std_ss [INT_LT_SUB_RADD, INT_ADD_LID, INT_LT])
    ++ `sumI (0,k - 1) (\i. (n:num -> int) i * &(f:num -> num) i) < 0` 
    	by METIS_TAC [INT_LET_TRANS]
    ++ SPOSE_NOT_THEN STRIP_ASSUME_TAC
    ++ `!i. i < k ==> 0 <= (n:num -> int) i` by METIS_TAC [INT_NOT_LT] 
    ++ `!i. i < k ==> 0 <= f i` by RW_TAC arith_ss [] 
    ++ `!i. i < k ==> 0 <= (n:num -> int) i * &f i` by METIS_TAC [INT_LE_MUL]
    ++ `!i. i < k - 1 ==> 0 <= (n:num -> int) i * &f i` by RW_TAC arith_ss []
    ++ (MP_TAC o Q.SPECL [`(\i. (n:num -> int) i * &(f:num -> num) i)`, `k - 1`]) SUMI_NFUN_POS
    ++ RW_TAC std_ss [INT_NOT_LE])
 ++ `i < k - 1` by RW_TAC arith_ss [] 
 ++ `1 <= (n:num -> int) i` by METIS_TAC [INT_LT_LE1, INT_ADD_LID]
 ++ `k - 1 + 1 = k` by RW_TAC arith_ss [SUB_ADD]
 ++ (MP_TAC o Q.SPECL 
 	[`(\i. (n:num -> int) i * &(f:num -> num) i)`, `k - 1`, `i`, `0`]) SUMI_SPLIT_TRE
 ++ RW_TAC std_ss [SUMI_1] 
 ++ `!i. i < k ==> 2 <= &f i` by METIS_TAC [INT_LE]
 ++ `0 <= (2:int)` 
 	by (RW_TAC std_ss [] 
 	   ++ `(0:num) <= 2` by RW_TAC arith_ss [] 
	   ++ METIS_TAC [INT_LE])
 ++ `2 <= (n:num -> int) i * &(f:num -> num) i` 
	by METIS_TAC [INT_LT_01, INT_LT_IMP_LE, INT_LT_MUL1, INT_MUL_LID]
 ++ `sumI (0,i) (\i. (n:num -> int) i * &(f:num -> num) i) + n i * &f i + 
     sumI (i + 1,k - 1 - i) (\i. n i * &f i) =
     sumI (0,i) (\i. n i * &f i) + 
     sumI (i + 1,k - 1 - i) (\i. n i * &f i) + n i * &f i`
	by METIS_TAC [INT_ADD_ASSOC, INT_ADD_COMM] 
 ++ FULL_SIMP_TAC std_ss [] ++ POP_ASSUM K_TAC
 ++ `sumI (0,i) (\i. (n:num -> int) i * &(f:num -> num) i) + 
     sumI (i + 1,k - 1 - i) (\i. n i * &f i) + 2 <= 
     sumI (0,i) (\i. n i * &f i) + 
     sumI (i + 1,k - 1 - i) (\i. n i * &f i) + n i * &f i` by METIS_TAC [INT_LE_LADD]
 ++ `sumI (0,i) (\i. (n:num -> int) i * &(f:num -> num) i) + 
     sumI (i + 1,k - 1 - i) (\i. n i * &f i) + 2 <= 1` by METIS_TAC []
 ++ `sumI (0,i) (\i. (n:num -> int) i * &(f:num -> num) i) + 
     sumI (i + 1,k - 1 - i) (\i. n i * &f i) <= 1 - 2` by METIS_TAC [INT_LE_SUB_LADD]
 ++ `1 - (2:int) < 0` by (NTAC 17 (POP_ASSUM K_TAC) 
 ++ `(1:num) < 2` by RW_TAC arith_ss [] 
 ++ RW_TAC std_ss [INT_LT_SUB_RADD, INT_ADD_LID, INT_LT])
 ++ `sumI (0,i) (\i. (n:num -> int) i * &(f:num -> num) i) + 
     sumI (i + 1,k - 1 - i) (\i. n i * &f i) < 0` by METIS_TAC [INT_LET_TRANS] 
 ++ POP_ASSUM MP_TAC ++ NTAC 6 (POP_ASSUM K_TAC) 
 ++ RW_TAC std_ss [] 
 ++ SPOSE_NOT_THEN STRIP_ASSUME_TAC
 ++ `!i. i < k ==> (0 <= (n:num -> int) i)` by METIS_TAC [int_le]
 ++ `!r. r < k ==> (0 <= (n:num -> int) r * &f r)` by METIS_TAC [INT_LE_MUL]
 ++ `!r. r < i ==> (0 <= (n:num -> int) r * &f r)` by RW_TAC arith_ss []
 ++ (MP_TAC o Q.SPECL [`(\i. (n:num -> int) i * &(f:num -> num) i)`, `i`]) SUMI_NFUN_POS
 ++ RW_TAC std_ss [] 
 ++ KNOW_TAC ``0 <= sumI (0, i) (\i. (n:num -> int) i * &(f:num -> num) i)``
 >> (MATCH_MP_TAC SUMI_NFUN_POS ++ RW_TAC std_ss []) ++ DISCH_TAC
 ++ `i + 1 + (k - 1 - i) = k` 
 	by RW_TAC arith_ss [ADD_COMM, SUB_RIGHT_SUB, SUB_ADD]
 ++ KNOW_TAC ``0 <= sumI  (i + 1,k - 1 - i) (\i. (n:num -> int) i * &(f:num -> num) i)``
 >> (MATCH_MP_TAC SUMI_POS_GEN 
    ++ RW_TAC std_ss []) ++ DISCH_TAC
 ++ `0 <= sumI (0,i) (\i. (n:num -> int) i * &(f:num -> num) i) + 
	sumI (i + 1,k - 1 - i) (\i. n i * &f i)` by RW_TAC std_ss [INT_LE_ADD]
 ++ METIS_TAC [INT_NOT_LE]);

val SUMI_POSPART1_SUB_POSPART2 = prove (
  ``!(n:num -> int) k (f:num -> num). (!i. i < k ==> 0 < f i) ==>
	(sumI (0,k) (\i. n i * &f i) = sumI (0,k) (\i. POS_PART1 i n * &f i) - 
	sumI (0,k) (\i. POS_PART2 i n * &f i))``,
    RW_TAC std_ss []
 ++ `!x. n x = POS_PART1 x n - POS_PART2 x n` 
 	by RW_TAC std_ss [INT_EQ_TWO_POSINT_SUB]
 ++ `!x. x < k ==> 0 < &f x` by METIS_TAC [INT_LT]
 ++ `!x. x < k ==> &f x <> 0` by METIS_TAC [INT_LT_IMP_NE]
 ++ `!x. x < k ==> (n x * &f x = (POS_PART1 x n - POS_PART2 x n) * &f x)` 
 	by METIS_TAC [INT_EQ_RMUL]
 ++ RW_TAC std_ss [GSYM SUMI_SUB] 
 ++ MATCH_MP_TAC SUMI_EQ 
 ++ RW_TAC std_ss [INT_SUB_RDISTRIB]);

val NUM_PART = prove (
  ``!(a:num) (b:num) c d. ((c - b) = 1) /\ 2 <= b /\ (d <= a) ==> 
	(a * b + d = (a - d) * b + d * c)``,
    RW_TAC std_ss [RIGHT_SUB_DISTRIB] 
 ++ KNOW_TAC ``d * b <= a * (b:num)``
 >> (Cases_on `b = 0` >> RW_TAC std_ss [MULT_CLAUSES, LESS_EQ_REFL] 
    ++ RW_TAC std_ss [LE_MULT_RCANCEL]) ++ DISCH_TAC
 ++ Cases_on `d * b = a * (b:num)` 
 >> (RW_TAC std_ss [] 
    ++ `(c:num) = 1 + b` 
    	by ((MP_TAC o Q.SPECL [`(c:num)`, `(b:num)`, `1`]) SUB_RIGHT_EQ 
	   ++ RW_TAC std_ss [ADD_COMM]) ++ POP_ORW
    ++ RW_TAC std_ss [LEFT_ADD_DISTRIB, ADD_COMM])
 ++ `d * b < a * (b:num)` by METIS_TAC [LESS_OR_EQ] 
 ++ `~(a * b <= d * (b:num))` by METIS_TAC [NOT_LESS_EQUAL] 
 ++ RW_TAC std_ss [SUB_RIGHT_ADD]
 ++ `(0:num) < c - b` by RW_TAC arith_ss [] 
 ++ `b < (c:num)` by RW_TAC arith_ss [SUB_LEFT_LESS, ADD]
 ++ Cases_on `d = (0:num)` 
 >> RW_TAC std_ss [ADD_0, MULT_CLAUSES, SUB_EQUAL_0, ADD_0]
 ++ `0 < (d:num)` by RW_TAC arith_ss [] 
 ++ `d * b < d * (c:num)` by METIS_TAC [LT_MULT_LCANCEL]
 ++ `a * b + d * c - d * b = a * b + (d * c - d * b)` 
 	by METIS_TAC [NOT_LESS_EQUAL, SUB_LEFT_ADD] 
 ++ POP_ORW ++ RW_TAC arith_ss [GSYM LEFT_SUB_DISTRIB]);

(* ------------------------------------------------------------------------- *)
(* Lemma 4: Least Number                                                     *)
(* ------------------------------------------------------------------------- *)  
val EXISTS_SUBSET_POSINT = store_thm
  ("EXISTS_SUBSET_POSINT",
  ``!A a. (!i. 0 < a i) /\ (A = IMAGE (\i. a i) (univ(:num))) /\ (GCD_OF_SET A = 1) /\
  	(!x y. x IN A /\ y IN A ==> (x + y) IN A) ==> 
  	?k. ({n | k <= n} SUBSET A)``,
    RW_TAC std_ss []
 ++ `(IMAGE (\i. a i) (univ(:num))) <> {}` 
		by (SPOSE_NOT_THEN STRIP_ASSUME_TAC 
 ++ METIS_TAC [IMAGE_EQ_EMPTY, UNIV_NOT_EMPTY])
 ++ `MIN_SET (IMAGE (\i. a i) univ(:num)) IN (IMAGE (\i. a i) (univ(:num)))` 
		by RW_TAC std_ss [MIN_SET_LEM] 
 ++ Cases_on `MIN_SET (IMAGE (\i. a i) (univ(:num))) = 1`
 >> (`(2:num) IN IMAGE (\i. a i) univ(:num)` 
		by (`(1:num) + 1 = 2` by RW_TAC arith_ss [] ++ METIS_TAC []) 
    ++ `(2:num) IN (IMAGE (\i. a i) univ(:num) DIFF {(1:num)})` by PSET_TAC [] 
    ++ KNOW_TAC ``2 <= MIN_SET ((IMAGE (\i. a i) (univ(:num))) DIFF {(1:num)})``
    >> (KNOW_TAC ``!x. x IN (IMAGE (\i. a i) univ(:num) DIFF {(1:num)}) ==> 2 <= x``
       >> (SPOSE_NOT_THEN STRIP_ASSUME_TAC 
          ++ `x < 2` by RW_TAC arith_ss [] 
	  ++ `(1:num) NOTIN IMAGE (\i. a i) univ(:num) DIFF {1}` 
	  	by PSET_TAC [IN_IMAGE, DIFF_DEF]
          ++ `(x:num) <> (1:num)` by (SPOSE_NOT_THEN STRIP_ASSUME_TAC 
		++ `(1:num) IN IMAGE (\i. a i) univ(:num) DIFF {1}` 
			by RW_TAC std_ss [] 
		++ PSET_TAC [IN_IMAGE, DIFF_DEF])
          ++ KNOW_TAC ``(x:num) <> 0``
	  >> (SPOSE_NOT_THEN STRIP_ASSUME_TAC ++ RW_TAC std_ss []
	     ++ `0 IN IMAGE (\i. (a:num -> num) i) univ(:num)` 
		by (NTAC 4 (POP_ASSUM K_TAC) 
		   ++ POP_ASSUM MP_TAC 
		   ++ NTAC 8 (POP_ASSUM K_TAC)
		   ++ PSET_TAC [DIFF_DEF])
          ++ `!(i:num). (a:num -> num) i <> 0` by METIS_TAC [LESS_REFL]
	  ++ METIS_TAC [IN_IMAGE, DIFF_DEF, LESS_REFL]) ++ DISCH_TAC ++ RW_TAC arith_ss [])
       ++ RW_TAC std_ss []
       ++ `(IMAGE (\i. a i) univ(:num) DIFF {1}) <> {}` by METIS_TAC [MEMBER_NOT_EMPTY]
       ++ METIS_TAC [MIN_SET_LEM]) ++ RW_TAC std_ss []
    ++ `1 <= MIN_SET (IMAGE (\i. (a:num -> num) i) univ(:num) DIFF {1})` 
	by RW_TAC arith_ss [LESS_IMP_LESS_OR_EQ]
    ++ Q.EXISTS_TAC `MIN_SET ((IMAGE (\i. a i) (univ(:num))) DIFF {(1:num)}) * 
		(MIN_SET ((IMAGE (\i. a i) (univ(:num))) DIFF {(1:num)}) - 1)` 
    ++ RW_TAC std_ss [SUBSET_DEF] ++ `MIN_SET ((IMAGE (\i. a i) (univ(:num))) DIFF {(1:num)}) * 
		(MIN_SET ((IMAGE (\i. a i) (univ(:num))) DIFF {(1:num)}) - 1) <= x` 
		by PSET_TAC []
    ++ (MP_TAC o Q.SPECL 
    	[`MIN_SET ((IMAGE (\i. (a:num -> num) i) (univ(:num))) DIFF {(1:num)})`, `x`]) 
	EXIST_NUM_COND ++ RW_TAC std_ss [] 
    ++ `(IMAGE (\i. (a:num -> num) i) univ(:num) DIFF {1}) <> {}` 
    	by METIS_TAC [MEMBER_NOT_EMPTY]	 
    ++ `MIN_SET (IMAGE (\i. a i) univ(:num) DIFF {1}) IN 
	  	(IMAGE (\i. (a:num -> num) i) univ(:num) DIFF {1})` by METIS_TAC [MIN_SET_LEM]
    ++ `!(x:num). x IN (IMAGE (\i. (a:num -> num) i) univ(:num) DIFF {1:num}) ==> 
	  		x IN IMAGE (\i. a i) univ(:num)` by PSET_TAC [DIFF_DEF]
    ++ POP_ASSUM (MP_TAC o Q.SPEC 
    	`MIN_SET (IMAGE (\i. (a:num -> num) i) univ(:num) DIFF {1:num})`)
    ++ RW_TAC std_ss []
    ++ `(1:num) IN (IMAGE (\i. (a:num -> num) i) univ(:num))` by METIS_TAC []
    ++ `2 <= (1:num) + a'` by RW_TAC arith_ss []
    ++ `0 < a'` by RW_TAC arith_ss []
    ++ `a' * MIN_SET (IMAGE (\i. a i) univ(:num) DIFF {1}) IN IMAGE (\i. a i) univ(:num)` 
	by METIS_TAC [MULTI_FUN_IN_SET]
    ++ Cases_on `r = 0` >> RW_TAC std_ss [ADD_0] 
    ++ `0 < r` by RW_TAC arith_ss []
    ++ `(r:num) = r * 1` by RW_TAC std_ss [MULT_RIGHT_1] ++ POP_ORW	 
    ++ `r * (1:num) IN IMAGE (\i. a i) univ(:num)` 
    	by METIS_TAC [MULTI_FUN_IN_SET]    ++ METIS_TAC []) 
 ++ `!x. x IN (IMAGE (\i. a i) univ(:num)) ==> 0 < x` by PSET_TAC []
 ++ `0 < MIN_SET (IMAGE (\i. a i) univ(:num))` by METIS_TAC []
 ++ `2 <= MIN_SET (IMAGE (\i. a i) univ(:num))` by RW_TAC arith_ss []
 ++ `!x. x IN (IMAGE (\i. (a:num -> num) i) univ(:num)) ==> 
	MIN_SET (IMAGE (\i. (a:num -> num) i) univ(:num)) <= x` 
	by METIS_TAC [MIN_SET_LEM]
 ++ `!x. x IN (IMAGE (\i. (a:num -> num) i) univ(:num)) ==> 2 <= x` 
 	by METIS_TAC [LESS_EQ_TRANS]
 ++ KNOW_TAC ``?t. FINITE t /\ t <> {} /\ t SUBSET (IMAGE (\i. a i) (univ(:num))) /\ 
	(GCD_OF_SET (IMAGE (\i. a i) (univ(:num))) = GCD_OF_SET t)``
 >> (REWRITE_TAC [] 
    ++ MATCH_MP_TAC EXISTS_SOME_GCD_K_EQ_GCD_S 
    ++ Q.EXISTS_TAC `a` 
    ++ RW_TAC std_ss []) 
 ++ RW_TAC std_ss []
 ++ `?f. (t = IMAGE (\i. f i) (count (CARD t)))` 
 	by METIS_TAC [FINITE_SET_EQ_IMAGE_FUN_COUNT, EQ_SYM_EQ]
 ++ KNOW_TAC ``0 < CARD (t:num -> bool)``
 >> (`{} PSUBSET t` by PSET_TAC [PSUBSET_DEF]
    ++ `!s. s PSUBSET t ==> CARD s < CARD t` by FULL_SIMP_TAC std_ss [CARD_PSUBSET]
    ++ POP_ASSUM (MP_TAC o Q.SPEC `{}`) 
    ++ RW_TAC std_ss [CARD_DEF])
 ++ RW_TAC std_ss []
 ++ KNOW_TAC ``1 < CARD (t:num -> bool)``
 >> (SPOSE_NOT_THEN STRIP_ASSUME_TAC 
    ++ `CARD (t:num -> bool) = 1` by RW_TAC arith_ss []
    ++ KNOW_TAC ``t = {(f:num -> num) 0}``
    >> (RW_TAC std_ss [] ++ `(t:num -> bool) =  IMAGE (\(i :num). (f :num -> num) i) (count 1)`
	by FULL_SIMP_TAC std_ss [] 
       ++ POP_ASSUM MP_TAC ++ NTAC 19 (POP_ASSUM K_TAC) 
       ++ PSET_TAC [COUNT_ONE, IMAGE_DEF, GSPEC_EQ, GSPECIFICATION, EXTENSION]
       ++ EQ_TAC 
       >> (RW_TAC std_ss [] 
          ++ `i = 0` by RW_TAC arith_ss [] 
          ++ RW_TAC std_ss [])
       ++ RW_TAC std_ss [] 
       ++ Q.EXISTS_TAC `(0:num)` 
       ++ RW_TAC arith_ss []) 
    ++ DISCH_TAC
    ++ `!x. x IN (t:num -> bool) ==> 2 <= x` by PSET_TAC [SUBSET_DEF]
    ++ `2 <= (f:num -> num) 0` by METIS_TAC [IN_SING] 
    ++ `0 < (f:num -> num) 0` by RW_TAC arith_ss []
    ++ `GCD_OF_SET {(f:num -> num) 0} = f 0` by METIS_TAC [GCD_SET_SING] 
    ++ RW_TAC arith_ss [])
 ++ RW_TAC std_ss [] 
 ++ `2 <= CARD (t:num -> bool)` by RW_TAC arith_ss []
 ++ POP_ASSUM MP_TAC 
 ++ POP_ASSUM K_TAC ++ RW_TAC std_ss []
 ++ KNOW_TAC ``!i. i < CARD (t:num -> bool) ==> (f:num -> num) i IN t``
 >> (RW_TAC std_ss [] 
    ++ `(f:num -> num) i IN (t:num -> bool) = f i IN IMAGE (\i. f i) (count (CARD t))` 
    	by METIS_TAC [] ++ POP_ORW 
    ++ PSET_TAC [IN_IMAGE] 
    ++ Q.EXISTS_TAC `i` 
    ++ RW_TAC std_ss []) 
 ++ RW_TAC std_ss []
 ++ `!x. x IN t ==> x IN (IMAGE (\i. (a:num -> num) i) univ(:num))` by METIS_TAC [SUBSET_DEF]
 ++ `!i. i < CARD (t:num -> bool) ==> 0 < (f:num -> num) i` by METIS_TAC []
 ++ `?n. &GCD_OF_SET (IMAGE (\(i:num). f i) (count (CARD (t:num -> bool)))) = 
	sumI (0, CARD (t:num -> bool)) (\i. n i * &f i)` 
	by RW_TAC std_ss [GCD_OF_SET_def, GCD_OF_SET_EQ_MINSET_POSINT]
 ++ `&GCD_OF_SET (IMAGE (\i. (f:num -> num) i) (count (CARD (t:num -> bool)))) = 1` 
	by METIS_TAC [INT_OF_NUM] 
 ++ `sumI (0,CARD t) (\i. (n:num -> int) i * &(f:num -> num) i) = 1` by METIS_TAC [EQ_SYM_EQ]
 ++ POP_ASSUM MP_TAC 
 ++ NTAC 2 (POP_ASSUM K_TAC) 
 ++ DISCH_TAC
 ++ KNOW_TAC ``?i. i < CARD (t:num -> bool) /\ ((n:num -> int) i < 0)``
 >> (RW_TAC std_ss [] 
    ++ `!i. i < CARD (t:num -> bool) ==> 
    	(f:num -> num) i IN IMAGE (\i. (a:num -> num) i) univ(:num)` 
	by PSET_TAC [IN_IMAGE] 
    ++ `!i. i < CARD (t:num -> bool) ==> 2 <= (f:num -> num) i ` by RW_TAC std_ss []
    ++ KNOW_TAC ``?i. i < CARD (t:num -> bool) /\ (0 < (n:num -> int) i)``
    >> (SPOSE_NOT_THEN STRIP_ASSUME_TAC 
       ++ `!i. i < CARD (t:num -> bool) ==> n i <= 0` by METIS_TAC [INT_NOT_LE] 
       ++ `!i. i < CARD (t:num -> bool) ==> n i * &f i <= 0` 
		by METIS_TAC [INT_LT, INT_LT_IMP_LE, INT_MUL_NEG_LE, INT_MUL_COMM]
       ++ `sumI (0, CARD (t:num -> bool)) (\i. (n:num -> int) i * &(f:num -> num) i) <= 0`
		by RW_TAC std_ss [SUMI_NEG_GEN] 
       ++ METIS_TAC [INT_LT_01, INT_NOT_LT]) 
    ++ DISCH_TAC
    ++ (MP_TAC o Q.SPECL [`(n:num -> int)`, `CARD (t:num -> bool)`, `(f:num -> num)`])
    	 EXISTS_NEG_FUN ++ RW_TAC std_ss []) ++ DISCH_TAC
 ++ (MP_TAC o Q.SPECL [`(n:num -> int)`, `CARD (t:num -> bool)`, `(f:num -> num)`]) POS_PART2_LT 
 ++ RW_TAC std_ss [] 
 ++ NTAC 2 (POP_ASSUM K_TAC) 
 ++ `&GCD_OF_SET t = 1` by METIS_TAC [EQ_SYM_EQ, INT_INJ] 
 ++ `0 < &GCD_OF_SET t` by METIS_TAC [INT_LT_01]
 ++ `0 < sumI (0,CARD t) (\i. n i * &f i)` by METIS_TAC [INT_LT_01]
 ++ (MP_TAC o Q.SPECL [`(n:num -> int)`, `CARD (t:num -> bool)`, `(f:num -> num)`])
 	SUMI_PART1_POS ++ RW_TAC std_ss [] 
 ++ `IMAGE (\i. (f:num -> num) i) (count (CARD t)) SUBSET 
 	IMAGE (\i. (a:num -> num) i) univ(:num)` by METIS_TAC []
 ++ (MP_TAC o Q.SPECL [`(n:num -> int)`, `CARD (t:num -> bool)`, `(f:num -> num)`, 
	`IMAGE (\i. (a:num -> num) i) univ(:num)`]) POS_PART1_IN_SET
 ++ RW_TAC std_ss [] 
 ++ `(0:num) < 2` by RW_TAC arith_ss [] 
 ++ `(0:int) < 2` by METIS_TAC [NUM_OF_INT, INT_LT]
 ++ `0 < sumI (0,CARD t) (\i. POS_PART2 i n * &f i)` by METIS_TAC [INT_LTE_TRANS]
 ++ POP_ASSUM MP_TAC 
 ++ NTAC 2 (POP_ASSUM K_TAC) ++ RW_TAC std_ss [] 
 ++ (MP_TAC o Q.SPECL [`(n:num -> int)`, `CARD (t:num -> bool)`, `(f:num -> num)`, 
	`IMAGE (\i. (a:num -> num) i) univ(:num)`]) POS_PART2_IN_SET
 ++ RW_TAC std_ss [] 
 ++ `sumI (0,CARD t) (\i. n i * &f i) = sumI (0,CARD t) (\i. POS_PART1 i n * &f i) - 
	sumI (0,CARD t) (\i. POS_PART2 i n * &f i)` 
	by METIS_TAC [SUMI_POSPART1_SUB_POSPART2]
 ++ `1 = sumI (0,CARD t) (\i. POS_PART1 i n * &f i) - 
	sumI (0,CARD t) (\i. POS_PART2 i n * &f i)` by METIS_TAC []
 ++ `0 < sumI (0,CARD t) (\i. POS_PART1 i n * &f i) - 
	sumI (0,CARD t) (\i. POS_PART2 i n * &f i)` 
	by METIS_TAC [INT_LT_01, INT_LTE_TRANS]
 ++ `Num (sumI (0,CARD t) (\i. POS_PART1 i n * &f i) - 
	sumI (0,CARD t) (\i. POS_PART2 i n * &f i)) = 
	Num (sumI (0,CARD t) (\i. POS_PART1 i n * &f i)) - 
	Num (sumI (0,CARD t) (\i. POS_PART2 i n * &f i))` 
	by METIS_TAC [NUM_INT_SUB]
 ++ `Num (sumI (0,CARD t) (\i. POS_PART1 i n * &f i)) - 
	Num (sumI (0,CARD t) (\i. POS_PART2 i n * &f i)) = 1` 
	by METIS_TAC [NUM_OF_INT, EQ_SYM_EQ]
 ++ POP_ASSUM MP_TAC ++ NTAC 4 (POP_ASSUM K_TAC)
 ++ `2 <= Num (sumI (0,CARD (t:num -> bool)) (\i. POS_PART2 i n * &f i))` 
	by METIS_TAC [INT_LT_IMP_LE, INT_OF_NUM, INT_LE]
 ++ NTAC 4 (POP_ASSUM MP_TAC) 
 ++ NTAC 6 (POP_ASSUM K_TAC) ++ NTAC 2 (POP_ASSUM MP_TAC) 
 ++ NTAC 7 (POP_ASSUM K_TAC) 
 ++ REPEAT STRIP_TAC 
 ++ `1 <= Num (sumI (0,CARD t) (\i. POS_PART2 i n * &f i))` by RW_TAC arith_ss [] 
 ++ Q.EXISTS_TAC `Num (sumI (0,CARD t) (\i. POS_PART2 i n * &f i)) * 
	(Num (sumI (0,CARD t) (\i. POS_PART2 i n * &f i)) - 1)` 
 ++ RW_TAC std_ss [SUBSET_DEF, GSPECIFICATION, EXTENSION] 
 ++ (MP_TAC o Q.SPECL [`Num (sumI (0,CARD (t:num -> bool)) (\i. POS_PART2 i n * &f i))`, `x`])
	 EXIST_NUM_COND ++ RW_TAC arith_ss [] 
 ++ Q.ABBREV_TAC `b = 
 	Num (sumI (0,CARD (t:num -> bool)) (\i. POS_PART2 i n * &(f:num -> num) i))`
 ++ Q.ABBREV_TAC `c = 
 	Num (sumI (0,CARD (t:num -> bool)) (\i. POS_PART1 i n * &(f:num -> num) i))`
 ++ RW_TAC std_ss [] 
 ++ `b - 1 <= a'` by RW_TAC std_ss [ADD_COMM, SUB_LESS_EQ_ADD]
 ++ `r <= a'` by METIS_TAC [LESS_EQ_TRANS]
 ++ (MP_TAC o Q.SPECL [`a'`, `(b:num)`, `c`, `(r:num)`]) NUM_PART ++ RW_TAC std_ss [] 
 ++ `(r:num) + a' * b = a' * b + r` by METIS_TAC [ADD_COMM] ++ NTAC 2 (POP_ORW)
 ++ `(a:num -> num) i' IN IMAGE (\i. (a:num -> num) i) univ(:num)` 
	by (PSET_TAC [] ++ Q.EXISTS_TAC `(i':num)` ++ RW_TAC std_ss [])
 ++ `(1:num) <= a'` by RW_TAC arith_ss [] 
 ++ `(0:num) < a'` by RW_TAC arith_ss []
 ++ Cases_on `r = 0` 
 >> RW_TAC std_ss [SUB_0, MULT_CLAUSES, ADD_0, NUM_IN_SET]
 ++ `(0:num) < r` by RW_TAC arith_ss []
 ++ Cases_on `r = a'` 
 >> RW_TAC std_ss [SUB_0, MULT_CLAUSES, ADD_CLAUSES, MULTI_FUN_IN_SET]
 ++ `r < a'` by RW_TAC arith_ss []
 ++ RW_TAC std_ss [NUM_IN_SET]);
 
 val _ = export_theory();
