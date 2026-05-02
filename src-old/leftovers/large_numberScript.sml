(*
Theorem density_RN_deriv :
    !M N. sigma_finite_measure_space M /\ measure_space N /\
          measure_absolutely_continuous (measure N) M /\
          measurable_sets M = measurable_sets N ==>
          measure_space_eq (density M (RN_deriv M N)) N
Proof
  RW_TAC std_ss [] THEN MATCH_MP_TAC RN_derivI THEN
  Q_TAC SUFF_TAC `sigma_finite_measure M /\ measure_space M /\
    measure_space N /\ measure_absolutely_continuous N M /\
   (measurable_sets M = measurable_sets N)` THENL
  [DISCH_THEN (MP_TAC o MATCH_MP RADON_NIKODYM),
   ASM_SIMP_TAC std_ss []] THEN
  RW_TAC std_ss [] THEN Q.EXISTS_TAC `f` THEN
  ASM_SIMP_TAC std_ss [density] THEN
  `m_space M = m_space N` by METIS_TAC [sets_eq_imp_space_eq] THEN
  Q_TAC SUFF_TAC `measurable_sets N SUBSET POW (m_space N)` THENL
  [DISCH_TAC,
   FULL_SIMP_TAC std_ss [measure_space_def, sigma_algebra_iff2]] THEN
  `sigma_sets (m_space N) (measurable_sets N) = measurable_sets N`
   by METIS_TAC [sigma_sets_eq, measure_space_def] THEN
  GEN_REWR_TAC (RAND_CONV o RAND_CONV) [GSYM MEASURE_SPACE_REDUCE] THEN
  ASM_SIMP_TAC std_ss [FUN_EQ_THM, measure_of, MEASURE_SPACE_REDUCE] THEN
  ASM_SIMP_TAC std_ss [extreal_max_def, le_mul, indicator_fn_pos_le]);

val RN_deriv_positive_integral = store_thm ("RN_deriv_positive_integral",
  ``!M N f. sigma_finite_measure M /\ measure_space M /\ measure_space N /\
          measure_absolutely_continuous N M /\
          (measurable_sets M = measurable_sets N) /\
          f IN measurable (m_space M, measurable_sets M) Borel ==>
          (pos_fn_integral N f =
           pos_fn_integral (density M (RN_deriv M N)) f)``,
  RW_TAC std_ss [] THEN
  Q_TAC SUFF_TAC `pos_fn_integral N f = pos_fn_integral (measure_of N) f` THENL
  [METIS_TAC [density_RN_deriv], ALL_TAC] THEN
  ONCE_REWRITE_TAC [METIS [MEASURE_SPACE_REDUCE]
   ``measure_of N = measure_of (m_space N, measurable_sets N, measure N)``] THEN
  Q_TAC SUFF_TAC `measurable_sets N SUBSET POW (m_space N)` THENL
  [DISCH_TAC,
   FULL_SIMP_TAC std_ss [measure_space_def, sigma_algebra_iff2]] THEN
  `sigma_sets (m_space N) (measurable_sets N) = measurable_sets N`
   by METIS_TAC [sigma_sets_eq, measure_space_def] THEN
  ASM_SIMP_TAC std_ss [measure_of] THEN
  SIMP_TAC std_ss [pos_fn_integral_def] THEN AP_TERM_TAC THEN
  AP_TERM_TAC THEN ABS_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  ABS_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC std_ss [IN_psfis_eq, MEASURE_SPACE_REDUCE] THEN
  AP_TERM_TAC THEN ABS_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN
  AP_TERM_TAC THEN ABS_TAC THEN
  Q_TAC SUFF_TAC `pos_simple_fn N g s a x =
   pos_simple_fn (m_space N,measurable_sets N,
    (\a. if a IN measurable_sets N then measure N a else 0)) g s a x` THENL
  [DISCH_TAC THEN ASM_SIMP_TAC std_ss [],
   SIMP_TAC std_ss [pos_simple_fn_def] THEN EQ_TAC THEN
   RW_TAC std_ss [measure_of, m_space_def, measurable_sets_def, measure_def]] THEN
  MATCH_MP_TAC (METIS [] ``(a ==> (b = c)) ==> (a /\ b = a /\ c)``) THEN
  POP_ASSUM (ASSUME_TAC o ONCE_REWRITE_RULE [EQ_SYM_EQ]) THEN
  POP_ASSUM (fn th => REWRITE_TAC [th]) THEN DISCH_TAC THEN
  AP_TERM_TAC THEN SIMP_TAC std_ss [pos_simple_fn_integral_def] THEN
  FULL_SIMP_TAC std_ss [pos_simple_fn_def] THEN
  FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP EXTREAL_SUM_IMAGE_EQ) THEN
  CONJ_TAC THENL [ALL_TAC, RW_TAC std_ss [measure_def]] THEN
  DISJ1_TAC THEN RW_TAC std_ss [] THENL
  [SIMP_TAC std_ss [lt_infty] THEN MATCH_MP_TAC lte_trans THEN
   Q.EXISTS_TAC `0` THEN CONJ_TAC THENL
   [METIS_TAC [lt_infty, num_not_infty, extreal_of_num_def], ALL_TAC] THEN
   MATCH_MP_TAC le_mul THEN ASM_SIMP_TAC std_ss [extreal_of_num_def, extreal_le_def] THEN
   ASM_SIMP_TAC std_ss [GSYM extreal_of_num_def] THEN
   METIS_TAC [measure_space_def, positive_def], ALL_TAC] THEN
  SIMP_TAC std_ss [lt_infty] THEN MATCH_MP_TAC lte_trans THEN
  Q.EXISTS_TAC `0` THEN CONJ_TAC THENL
  [METIS_TAC [lt_infty, num_not_infty, extreal_of_num_def], ALL_TAC] THEN
  MATCH_MP_TAC le_mul THEN ASM_SIMP_TAC std_ss [extreal_of_num_def, extreal_le_def] THEN
  ASM_SIMP_TAC std_ss [GSYM extreal_of_num_def, measure_def] THEN
  METIS_TAC [measure_space_def, positive_def]);
*)

