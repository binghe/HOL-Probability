(*----------------------------------------------------------------*)   
(*---      Section 12    Verification An Application           ---*)
(*----------------------------------------------------------------*)  
(*=====================================================*)
(*==      1.  binary channels model definition       ==*)
(*=====================================================*)
val Linit_def = Define `
    Linit (c:real) (d:real) (i:num) = 
    	if i = 0 then c else 
        if i = 1 then d else 0`;
              
val Lt_def = Define `
    Lt (a:real) (b:real) (t:num) (i:num) (j:num) = 
        if (i = 0) /\ (j = 0) then 1 - a else
        if (i = 0) /\ (j = 1) then a else
        if (i = 1) /\ (j = 0) then b else
        if (i = 1) /\ (j = 1) then 1 - b else 0`;
          
val BINARY_CHANNELS_MODEL_def = Define `
    BINARY_CHANNELS_MODEL X p (a:real) (b:real) (c:real) (d:real) = 
       (th_dtmc X p (count 2, POW (count 2)) (Linit c d) (Lt a b)) /\
       (abs (1 - a - b) < 1) /\
       (a <= 1) /\ (0 <= a) /\ (b <= 1) /\ (0 <= b) /\
       (c + d = 1) /\ (0 < c) /\ (0 < d) /\ (c < 1) /\ (d < 1) `;

(*====================================================*)
(*==    2. some prepared theorems being used later  ==*)
(*====================================================*)
val BI_TERNNAL_TRANS_00_PROBABILITY = prove
  (``!(a:real) b (n:num). (0 <= a) /\ (a <= 1) /\ (b <= 1) /\ (0 <= b) /\
   (abs (1 - a - b) < 1) ==>
   ((1 - a) * ((b + a * (1 - a - b) pow n) / (a + b)) +
    b * (1 - (b + a * (1 - a - b) pow n) / (a + b)) =
    (b + a * (1 - a - b) pow (n + 1)) / (a + b))``,
    RW_TAC std_ss [REAL_POW_ADD,POW_1,REAL_MUL_ASSOC]
 ++ Q.ABBREV_TAC `c = (1 - a - b) pow n`
 ++ `0 <= (a + b)` by RW_TAC std_ss [REAL_LE_ADD]
 ++ Know `~(a + b = 0)`
 >> (SPOSE_NOT_THEN STRIP_ASSUME_TAC
    ++ `(1 - a - b) = 1 - (a + b)` by REAL_ARITH_TAC
    ++ FULL_SIMP_TAC std_ss [REAL_SUB_RZERO, ABS_1,REAL_LT_REFL])
 ++ RW_TAC std_ss []
 ++ `(((1 - a) * ((b + a * c) / (a + b)) + 
      b * (1 - (b + a * c) / (a + b))) * (a + b) =
     (b + a * c * (1 - a - b)) / (a + b) * (a + b)) =
   ((1 - a) * ((b + a * c) / (a + b)) + 
      b * (1 - (b + a * c) / (a + b)) =
    (b + a * c * (1 - a - b)) / (a + b))` 
    by FULL_SIMP_TAC std_ss [REAL_EQ_RMUL]
 ++ POP_ASSUM (MP_TAC o GSYM)
 ++ RW_TAC std_ss [REAL_ADD_RDISTRIB, GSYM REAL_MUL_ASSOC, 
 	REAL_SUB_RDISTRIB, REAL_ADD_RDISTRIB, REAL_DIV_RMUL, REAL_MUL_LID]
 ++ REAL_ARITH_TAC);
 
 
val BI_TERNNAL_TRANS_00_PROBABILITY = prove
  (``!(a:real) b (n:num). (0 <= a) /\ (a <= 1) /\ (b <= 1) /\ (0 <= b) /\
   (abs (1 - a - b) < 1) ==>
   ((1 - a) * (b + a * (1 - a - b) pow n) +
    b * (a - a * (1 - a - b) pow (n + 1)) =
    b + a * (1 - a - b) pow (n + 1))``,
    RW_TAC real_ss [REAL_POW_ADD,POW_1,REAL_MUL_ASSOC, REAL_ADD_LDISTRIB]
 ++ Q.ABBREV_TAC `c = a * (1 - a - b) pow n`
 ++ `0 <= (a + b)` by RW_TAC std_ss [REAL_LE_ADD]
 ++ Know `~(a + b = 0)`
 >> (SPOSE_NOT_THEN STRIP_ASSUME_TAC
    ++ `(1 - a - b) = 1 - (a + b)` by REAL_ARITH_TAC
    ++ FULL_SIMP_TAC std_ss [REAL_SUB_RZERO, ABS_1,REAL_LT_REFL])
 ++ RW_TAC std_ss []
 ++ `(((1 - a) * ((b + a * c) / (a + b)) + 
      b * (1 - (b + a * c) / (a + b))) * (a + b) =
     (b + a * c * (1 - a - b)) / (a + b) * (a + b)) =
   ((1 - a) * ((b + a * c) / (a + b)) + 
      b * (1 - (b + a * c) / (a + b)) =
    (b + a * c * (1 - a - b)) / (a + b))` 
    by FULL_SIMP_TAC std_ss [REAL_EQ_RMUL]
 ++ POP_ASSUM (MP_TAC o GSYM)
 ++ RW_TAC std_ss [REAL_ADD_RDISTRIB, GSYM REAL_MUL_ASSOC, 
 	REAL_SUB_RDISTRIB, REAL_ADD_RDISTRIB, REAL_DIV_RMUL, REAL_MUL_LID]
 ++ REAL_ARITH_TAC);

(*===============================================*)
val BI_TERNNAL_TRANS_10_PROBABILITY = prove
  (``!(a:real) b (n:num). (0 <= a) /\ (a <= 1) /\ (b <= 1) /\ (0 <= b) /\
   (abs (1 - a - b) < 1) ==> 
   ((1 - a) * ((b - b * (1 - a - b) pow n) / (a + b)) +
    b * (1 - (b - b * (1 - a - b) pow n) / (a + b)) =
    (b - b * (1 - a - b) pow (n + 1)) / (a + b))``,
    RW_TAC std_ss [REAL_POW_ADD,POW_1,REAL_MUL_ASSOC]
 ++ Q.ABBREV_TAC `c = (1 - a - b) pow n`    
 ++ `0 <= (a + b)` by RW_TAC std_ss [REAL_LE_ADD]
 ++ Know `~(a + b = 0)`
 >> (SPOSE_NOT_THEN STRIP_ASSUME_TAC
    ++ `(1 - a - b) = 1 - (a + b)` by REAL_ARITH_TAC
    ++ FULL_SIMP_TAC std_ss [REAL_SUB_RZERO, ABS_1,REAL_LT_REFL])
 ++ RW_TAC std_ss []
 ++ `(((1 - a) * ((b - b * c) / (a + b)) + 
 	b * (1 - (b - b * c) / (a + b))) * (a + b) =
    ((b - b * c * (1 - a - b)) / (a + b)) * (a + b)) =
   ((1 - a) * ((b - b * c) / (a + b)) + b * (1 - (b - b * c) / (a + b)) =
    (b - b * c * (1 - a - b)) / (a + b))` 
   	by FULL_SIMP_TAC std_ss [REAL_EQ_RMUL]
 ++ POP_ASSUM (MP_TAC o GSYM)
 ++ RW_TAC std_ss [GSYM REAL_MUL_ASSOC, REAL_SUB_RDISTRIB, 
 	REAL_ADD_RDISTRIB, REAL_DIV_RMUL, REAL_MUL_LID]
 ++ REAL_ARITH_TAC);

val MATRIX_01 = prove
  (``!(a:real) b. a <= 1 /\ 0 <= a /\ b <= 1 /\ 0 <= b /\
	abs (1 - a - b) < 1 ==> ((b + a * (1 - a - b)) / (a + b) = 1 - a)``,
    RW_TAC std_ss [real_sub, GSYM REAL_ADD_ASSOC, GSYM REAL_NEG_ADD, 
    	REAL_ADD_LDISTRIB, REAL_MUL_RID, real_div, REAL_ADD_RDISTRIB, REAL_MUL_RNEG]
 ++ Know `~(a + b = 0)`
 >> (SPOSE_NOT_THEN STRIP_ASSUME_TAC
    ++ FULL_SIMP_TAC real_ss [])  
 ++ RW_TAC std_ss []  	
 ++ `b * inv (a + b) + a * inv (a + b) = 1`
 	by METIS_TAC [REAL_ADD_RDISTRIB, REAL_ADD_COMM, REAL_MUL_RINV]   	
 ++ RW_TAC std_ss [REAL_ADD_ASSOC]
 ++ RW_TAC std_ss [GSYM REAL_ADD_LDISTRIB, REAL_MUL_LNEG, 
 	GSYM REAL_MUL_ASSOC, REAL_MUL_RINV, REAL_MUL_RID]);
	
(*===========================================================*)
(*==  3. four theorems for n-step transition probabilities ==*)
(*===========================================================*)
val matrix_00 = prove
  (``!X p (a:real) b (n:num) c d.        
       (BINARY_CHANNELS_MODEL X p a b c d) ==>    
       (cond_prob p (PREIMAGE (X 1) {0} INTER p_space p)
      		(PREIMAGE (X 0) {0} INTER p_space p) = 1 - a)``,
    RW_TAC std_ss [BINARY_CHANNELS_MODEL_def, th_dtmc_def, dtmc_def]
 ++ `prob p (PREIMAGE (X 0) {0} INTER p_space p) <> 0`
 	by (PSET_TAC [th_dtmc_def, dtmc_def, mc_property_def, random_variable_def, 
    		distribution_def, measureTheory.space_def, Linit_def]
           ++ NTAC 13 (POP_ASSUM MP_TAC)
           ++ POP_ASSUM (MP_TAC o Q.SPEC `0`)
           ++ RW_TAC arith_ss[REAL_LT_IMP_NE])
 ++ NTAC 13 (POP_ASSUM MP_TAC)  
 ++ POP_ASSUM (MP_TAC o Q.SPECL [`0`, `0`, `0`])         
 ++ RW_TAC real_ss [distribution_def, Lt_def, Trans_def]
 ++ FULL_SIMP_TAC real_ss [measureTheory.space_def, IN_COUNT]);

val matrix_01 = prove
  (``!X p (a:real) b (n:num) c d.        
       (BINARY_CHANNELS_MODEL X p a b c d) ==>    
       (cond_prob p (PREIMAGE (X 1) {1} INTER p_space p)
      		(PREIMAGE (X 0) {0} INTER p_space p) = a)``,
    RW_TAC std_ss [BINARY_CHANNELS_MODEL_def, th_dtmc_def, dtmc_def]
 ++ `prob p (PREIMAGE (X 0) {0} INTER p_space p) <> 0`
 	by (PSET_TAC [th_dtmc_def, dtmc_def, mc_property_def, random_variable_def, 
    		distribution_def, measureTheory.space_def, Linit_def]
           ++ NTAC 13 (POP_ASSUM MP_TAC)
           ++ POP_ASSUM (MP_TAC o Q.SPEC `0`)
           ++ RW_TAC arith_ss[REAL_LT_IMP_NE])
 ++ NTAC 13 (POP_ASSUM MP_TAC)  
 ++ POP_ASSUM (MP_TAC o Q.SPECL [`0`, `1`, `0`])         
 ++ PSET_TAC [distribution_def, Lt_def, Trans_def, measureTheory.space_def, IN_COUNT]);
 
val matrix_10 = prove
  (``!X p (a:real) b (n:num) c d.        
       (BINARY_CHANNELS_MODEL X p a b c d) ==>    
       (cond_prob p (PREIMAGE (X 1) {0} INTER p_space p)
      		(PREIMAGE (X 0) {1} INTER p_space p) = b)``,
    RW_TAC std_ss [BINARY_CHANNELS_MODEL_def, th_dtmc_def, dtmc_def]
 ++ `prob p (PREIMAGE (X 0) {1} INTER p_space p) <> 0`
 	by (PSET_TAC [th_dtmc_def, dtmc_def, mc_property_def, random_variable_def, 
    		distribution_def, measureTheory.space_def, Linit_def]
           ++ NTAC 13 (POP_ASSUM MP_TAC)
           ++ POP_ASSUM (MP_TAC o Q.SPEC `1`)
           ++ RW_TAC arith_ss[REAL_LT_IMP_NE])
 ++ NTAC 13 (POP_ASSUM MP_TAC)  
 ++ POP_ASSUM (MP_TAC o Q.SPECL [`1`, `0`, `0`])         
 ++ PSET_TAC [distribution_def, Lt_def, Trans_def, measureTheory.space_def, IN_COUNT]);
 
val matrix_11 = prove
  (``!X p (a:real) b (n:num) c d.        
       (BINARY_CHANNELS_MODEL X p a b c d) ==>    
       (cond_prob p (PREIMAGE (X 1) {1} INTER p_space p)
      		(PREIMAGE (X 0) {1} INTER p_space p) = 1 - b)``,
    RW_TAC std_ss [BINARY_CHANNELS_MODEL_def, th_dtmc_def, dtmc_def]
 ++ `prob p (PREIMAGE (X 0) {1} INTER p_space p) <> 0`
 	by (PSET_TAC [th_dtmc_def, dtmc_def, mc_property_def, random_variable_def, 
    		distribution_def, measureTheory.space_def, Linit_def]
           ++ NTAC 13 (POP_ASSUM MP_TAC)
           ++ POP_ASSUM (MP_TAC o Q.SPEC `1`)
           ++ RW_TAC arith_ss[REAL_LT_IMP_NE])
 ++ NTAC 13 (POP_ASSUM MP_TAC)  
 ++ POP_ASSUM (MP_TAC o Q.SPECL [`1`, `1`, `0`])         
 ++ PSET_TAC [distribution_def, Lt_def, Trans_def, measureTheory.space_def, IN_COUNT]); 

val REAL_DIV_ADD_SAME = prove
  (``!a b c (d:real) e f. (e * b + f * c = d) ==> 
  	(e * (b / a) + f * (c / a) = d / a)``,
    RW_TAC real_ss [real_div]
 ++ REAL_ARITH_TAC);

val BI_PROB_01 = prove
  (``!X p (a:real) b (n:num) c d.        
       BINARY_CHANNELS_MODEL X p a b c d /\ 
       (prob p (PREIMAGE (X n) {0} INTER p_space p) = 0) ==>  
       (prob p (PREIMAGE (X n) {1} INTER p_space p) = 1)``,
    RW_TAC std_ss [BINARY_CHANNELS_MODEL_def, th_dtmc_def]
 ++ `!t. random_variable (X t) p (count 2,POW (count 2))` 
        by PSET_TAC [dtmc_def, mc_property_def]   
 ++ `!x. x IN space (count 2,POW (count 2)) ==> {x} IN subsets (count 2,POW (count 2))`
        by PSET_TAC [dtmc_def, mc_property_def]
 ++ `count 2 = {0} UNION {1:num}` 
 	by (PSET_TAC [count_def, EXTENSION] ++ RW_TAC arith_ss [])  
 ++ RW_TAC std_ss []   
 ++ (MP_TAC o Q.SPECL [`X`, `p`, `(count 2,POW (count 2))`, `n`] o INST_TYPE [``:'b`` |-> ``:num``])
        SUM_PMF_ONE ++ RW_TAC std_ss [dtmc_def, distribution_def, measureTheory.space_def]
 ++ POP_ASSUM MP_TAC ++ DEP_REWRITE_TAC [REAL_SUM_IMAGE_DISJOINT_UNION, REAL_SUM_IMAGE_SING]
 ++ PSET_TAC [FINITE_SING, REAL_ADD_LID]);
      
val BI_COND_PROB_01 = prove
  (``!X p (a:real) b (n:num) c d.        
       BINARY_CHANNELS_MODEL X p a b c d /\
       (cond_prob p (PREIMAGE (X n) {(0:num)} INTER p_space p) 
                  (PREIMAGE (X 0) {(0:num)} INTER p_space p) = 
                  (b + a * (1 - a - b) pow n) / (a + b)) ==>                                    
       (cond_prob p (PREIMAGE (X n) {(1:num)} INTER p_space p) 
                  (PREIMAGE (X 0) {(0:num)} INTER p_space p) = 
       (a - a * (1 - a - b) pow n) / (a + b))``,
    RW_TAC std_ss [BINARY_CHANNELS_MODEL_def, th_dtmc_def, dtmc_def]
 ++ `prob_space p` by PSET_TAC [mc_property_def, random_variable_def]   
 ++ `prob p (PREIMAGE (X 0) {0} INTER p_space p) <> 0`
 	by (PSET_TAC [th_dtmc_def, dtmc_def, mc_property_def, random_variable_def, 
    		distribution_def, measureTheory.space_def, Linit_def]
           ++ NTAC 14 (POP_ASSUM MP_TAC)
           ++ POP_ASSUM (MP_TAC o Q.SPEC `0`)
           ++ RW_TAC arith_ss[REAL_LT_IMP_NE])             
 ++ `count 2 = {0} UNION {1:num}` 
 	by (PSET_TAC [count_def, EXTENSION] ++ RW_TAC arith_ss [])            
 ++ `SIGMA (\k. cond_pmf p (X (0 + n)) (X 0) ({k}, {0})) (space (count 2, POW (count 2))) = 1`
        by (MATCH_MP_TAC SUM_ROW_MATRIX_EQ_ONE ++ MAP_EVERY Q.EXISTS_TAC [`Linit c d`, `Lt a b`]
           ++ RW_TAC std_ss [dtmc_def, distribution_def, measureTheory.space_def, FINITE_COUNT, REAL_LT_LE]
           ++ MATCH_MP_TAC PROB_POSITIVE ++ RW_TAC std_ss []
           ++ MATCH_MP_TAC DTMC_EVENTS
           ++ MAP_EVERY Q.EXISTS_TAC [`(count 2, POW (count 2))`, `Linit c d`, `Lt a b`]
           ++ RW_TAC std_ss [dtmc_def]) 
 ++ PSET_TAC [measureTheory.space_def, COND_PMF_EQ_COND_PROB, count_def] 	           
 ++ POP_ASSUM MP_TAC
 ++ DEP_REWRITE_TAC [REAL_SUM_IMAGE_DISJOINT_UNION, REAL_SUM_IMAGE_SING]
 ++ ONCE_REWRITE_TAC [REAL_ADD_COMM]
 ++ PSET_TAC [FINITE_SING, GSYM REAL_EQ_SUB_LADD]        
 ++ ONCE_REWRITE_TAC [EQ_SYM_EQ]
 ++ `b + a = a + b` by RW_TAC std_ss [REAL_ADD_COMM]
 ++ RW_TAC std_ss [REAL_EQ_SUB_LADD, REAL_DIV_ADD, REAL_ADD_ASSOC]
 ++ `!(a:real) b c. a - b + c + b = a + c` by (RW_TAC real_ss [] ++ REAL_ARITH_TAC)
 ++ POP_ORW ++ MATCH_MP_TAC REAL_DIV_REFL
 ++ SPOSE_NOT_THEN STRIP_ASSUME_TAC
 ++ `(1 - a - b) = 1 - (a + b)` by REAL_ARITH_TAC
 ++ FULL_SIMP_TAC std_ss [REAL_SUB_RZERO, ABS_1,REAL_LT_REFL]);
 
val BI_TERNNAL_NSTEP_00_PROBABILITY = prove
  (``!X p (a:real) b (n:num) c d.        
       (BINARY_CHANNELS_MODEL X p a b c d) ==>                                    
       (cond_prob p (PREIMAGE (X n) {(0:num)} INTER p_space p) 
                  (PREIMAGE (X 0) {(0:num)} INTER p_space p) = 
        (b + a * (1 - a - b) pow n) / (a + b))``,
    RW_TAC std_ss [BINARY_CHANNELS_MODEL_def]
 ++ `prob_space p` by PSET_TAC [th_dtmc_def, dtmc_def, mc_property_def, random_variable_def]    
 ++ `0 <= (a + b)` by RW_TAC std_ss [REAL_LE_ADD]
 ++ Know `~(a + b = 0)`
 >> (SPOSE_NOT_THEN STRIP_ASSUME_TAC
    ++ `(1 - a - b) = 1 - (a + b)` by REAL_ARITH_TAC
    ++ FULL_SIMP_TAC std_ss [REAL_SUB_RZERO, ABS_1,REAL_LT_REFL])
 ++ RW_TAC std_ss []   
 ++ `!t. PREIMAGE (X t) {0} INTER p_space p IN events p`
 	by (PSET_TAC [th_dtmc_def] ++ METIS_TAC [DTMC_EVENTS])
 ++ `!t. PREIMAGE (X t) {1} INTER p_space p IN events p`
 	by (PSET_TAC [th_dtmc_def] ++ METIS_TAC [DTMC_EVENTS])
 ++ Induct_on `n`
 >> (RW_TAC std_ss [pow, REAL_MUL_RID, REAL_ADD_COMM, REAL_DIV_REFL]
    ++ MATCH_MP_TAC COND_PROB_ITSELF
    ++ PSET_TAC [th_dtmc_def, dtmc_def, mc_property_def, random_variable_def, 
    	distribution_def, measureTheory.space_def, Linit_def]
    ++ NTAC 17 (POP_ASSUM MP_TAC)
    ++ POP_ASSUM (MP_TAC o Q.SPEC `0`)
    ++ RW_TAC arith_ss[])
 ++ (MP_TAC o Q.SPECL [`X`, `p`, `(count 2, POW (count 2))`, `n`, `0`, `0`, 
 	`Linit c d`, `Lt a b`, `0`] o INST_TYPE [``:'b`` |-> ``:num``])
 	MC_NSTEP_COND_PROB 
 ++ PSET_TAC [ADD1, th_dtmc_def, COND_PMF_EQ_COND_PROB, measureTheory.space_def]
 ++ `count 2 = {0} UNION {1:num}` 
 	by (PSET_TAC [count_def, EXTENSION] ++ RW_TAC arith_ss [])  
 ++ RW_TAC std_ss [] ++ POP_ASSUM K_TAC 
 ++ DEP_REWRITE_TAC [REAL_SUM_IMAGE_DISJOINT_UNION, REAL_SUM_IMAGE_SING]	    
 ++ PSET_TAC [FINITE_SING] ++ POP_ASSUM K_TAC 
 ++ (MP_TAC o Q.SPECL [`a`, `b`, `n`]) BI_TERNNAL_TRANS_00_PROBABILITY
 ++ RW_TAC std_ss []
 ++ Cases_on `prob p (PREIMAGE (X n) {0} INTER p_space p) = 0`
 >> (`cond_prob p (PREIMAGE (X n) {1} INTER p_space p)
           (PREIMAGE (X 0) {0} INTER p_space p) = (a - a * (1 - a - b) pow n) / (a + b)`
           by (MATCH_MP_TAC BI_COND_PROB_01 ++ MAP_EVERY Q.EXISTS_TAC [`c`, `d`]
              ++ RW_TAC std_ss [BINARY_CHANNELS_MODEL_def, th_dtmc_def, 
                        measureTheory.space_def, FINITE_COUNT]) ++ POP_ORW
    ++ `cond_prob p (PREIMAGE (X (n + 1)) {0} INTER p_space p)
      (PREIMAGE (X n) {0} INTER p_space p) = 0` 
      by (DEP_REWRITE_TAC [COND_PROB_ZERO, DTMC_EVENTS]
         ++ RW_TAC std_ss []
         ++ MAP_EVERY Q.EXISTS_TAC [`(count 2, POW (count 2))`, `Linit c d`, `Lt a b`]
         ++ RW_TAC std_ss []) ++ RW_TAC std_ss [REAL_MUL_LZERO, REAL_ADD_LID]
    ++ `cond_prob p (PREIMAGE (X (n + 1)) {0} INTER p_space p)
             (PREIMAGE (X n) {1} INTER p_space p) = b` 
        by (`prob p (PREIMAGE (X n) {1} INTER p_space p) = 1` 
                by (MATCH_MP_TAC BI_PROB_01 ++ MAP_EVERY Q.EXISTS_TAC [`a`, `b`, `c`, `d`]
                   ++ RW_TAC std_ss [BINARY_CHANNELS_MODEL_def, th_dtmc_def, 
                        measureTheory.space_def, FINITE_COUNT])
           ++ PSET_TAC [dtmc_def, distribution_def, measureTheory.space_def]                        
           ++ POP_ASSUM MP_TAC ++ NTAC 5 (POP_ASSUM K_TAC) ++ NTAC 16 (POP_ASSUM MP_TAC)
           ++ POP_ASSUM (MP_TAC o GSYM o Q.SPECL [`1`, `0`, `n`])
           ++ RW_TAC real_ss [Lt_def, Trans_def, measureTheory.space_def, IN_COUNT]
           ++ FULL_SIMP_TAC real_ss []) ++ POP_ORW
    ++ `cond_prob p (PREIMAGE (X n) {0} INTER p_space p)
                (PREIMAGE (X 0) {0} INTER p_space p) = 0` 
      by (DEP_REWRITE_TAC [COND_PROB_INTER_ZERO, DTMC_EVENTS]
         ++ RW_TAC std_ss []
         ++ MAP_EVERY Q.EXISTS_TAC [`(count 2, POW (count 2))`, `Linit c d`, `Lt a b`]
         ++ RW_TAC std_ss []) ++ `(b + a * (1 - a - b) pow n) / (a + b) = 0` by METIS_TAC []
    ++ FULL_SIMP_TAC std_ss [REAL_MUL_RZERO, REAL_SUB_RZERO, REAL_MUL_RID, REAL_ADD_LID]     
    ++ `(b + a * (1 - a - b) pow (n + 1)) / (a + b) = b` by METIS_TAC [] ++ POP_ORW
    ++ Suff `a - a * (1 - a - b) pow n = a + b`
    >> RW_TAC std_ss [REAL_DIV_REFL, REAL_MUL_RID]
    ++ RW_TAC std_ss [real_sub, REAL_EQ_LADD]
    ++ ONCE_REWRITE_TAC [EQ_SYM_EQ]
    ++ RW_TAC std_ss [GSYM REAL_RNEG_UNIQ, GSYM real_sub] ++ ONCE_REWRITE_TAC [REAL_ADD_COMM]
    ++ `inv (a + b) <> 0` by METIS_TAC [REAL_INV_NZ]   
    ++ FULL_SIMP_TAC real_ss [real_div, REAL_ENTIRE, REAL_INV_0])
 ++ Cases_on `prob p (PREIMAGE (X n) {1} INTER p_space p) = 0`
 >> (`cond_prob p (PREIMAGE (X (n + 1)) {0} INTER p_space p)
      (PREIMAGE (X n) {1} INTER p_space p) = 0` 
      by (DEP_REWRITE_TAC [COND_PROB_ZERO, DTMC_EVENTS]
         ++ RW_TAC std_ss []
         ++ MAP_EVERY Q.EXISTS_TAC [`(count 2, POW (count 2))`, `Linit c d`, `Lt a b`]
         ++ RW_TAC std_ss []) ++ RW_TAC std_ss [REAL_MUL_LZERO, REAL_ADD_RID]
    ++ `cond_prob p (PREIMAGE (X (n + 1)) {0} INTER p_space p)
             (PREIMAGE (X n) {0} INTER p_space p) = 1 - a` 
        by (PSET_TAC [dtmc_def, distribution_def, measureTheory.space_def]                        
           ++ NTAC 2 (POP_ASSUM K_TAC) ++ NTAC 4 (POP_ASSUM MP_TAC) ++ NTAC 16 (POP_ASSUM MP_TAC)
           ++ POP_ASSUM (MP_TAC o GSYM o Q.SPECL [`0`, `0`, `n`])
           ++ RW_TAC real_ss [Lt_def, Trans_def, measureTheory.space_def, IN_COUNT]
           ++ FULL_SIMP_TAC real_ss []) ++ POP_ORW
    ++ RW_TAC std_ss [REAL_MUL_LZERO, REAL_ADD_RID]
    ++ NTAC 3 (POP_ASSUM MP_TAC) ++ POP_ASSUM (MP_TAC o GSYM)
    ++ RW_TAC std_ss []
    ++ ONCE_REWRITE_TAC [EQ_SYM_EQ]
    ++ RW_TAC std_ss [REAL_ADD_RID_UNIQ]
    ++ Cases_on `b = 0` >> RW_TAC std_ss [REAL_MUL_LZERO]
    ++ RW_TAC std_ss [REAL_ENTIRE, REAL_SUB_0]
    ++ ONCE_REWRITE_TAC [EQ_SYM_EQ]
    ++ (MP_TAC o Q.SPECL [`X`, `p`, `a`, `b`, `n`, `c`, `d`]) BI_COND_PROB_01
    ++ RW_TAC std_ss [BINARY_CHANNELS_MODEL_def, th_dtmc_def, measureTheory.space_def, FINITE_COUNT]
    ++ `cond_prob p (PREIMAGE (X n) {1} INTER p_space p)
           (PREIMAGE (X 0) {0} INTER p_space p) = 0`
           by (DEP_REWRITE_TAC [COND_PROB_INTER_ZERO, DTMC_EVENTS] 
              ++ RW_TAC std_ss []
              ++ MAP_EVERY Q.EXISTS_TAC [`(count 2, POW (count 2))`, `Linit c d`, `Lt a b`]
              ++ RW_TAC std_ss []) ++ FULL_SIMP_TAC std_ss []
    ++ `!(x:real) y. y <> 0 /\ (x / y = 0) ==> (x = 0)`
        by METIS_TAC [real_div, REAL_ENTIRE, REAL_INV_NZ]
    ++ `a - a * (1 - a - b) pow n = 0` by METIS_TAC []      
    ++ `a * (1 - a - b) pow n = a` by METIS_TAC [REAL_SUB_0] ++ POP_ORW 
    ++ METIS_TAC [REAL_ADD_COMM, REAL_DIV_REFL])
 ++ `cond_prob p (PREIMAGE (X (n + 1)) {0} INTER p_space p)
             (PREIMAGE (X n) {0} INTER p_space p) = 1 - a` 
        by (PSET_TAC [dtmc_def, distribution_def, measureTheory.space_def]                        
           ++ NTAC 21 (POP_ASSUM MP_TAC)
           ++ POP_ASSUM (MP_TAC o GSYM o Q.SPECL [`0`, `0`, `n`])
           ++ RW_TAC real_ss [Lt_def, Trans_def, measureTheory.space_def, IN_COUNT]
           ++ FULL_SIMP_TAC real_ss []) ++ POP_ORW
 ++ `cond_prob p (PREIMAGE (X (n + 1)) {0} INTER p_space p)
             (PREIMAGE (X n) {1} INTER p_space p) = b` 
        by (PSET_TAC [dtmc_def, distribution_def, measureTheory.space_def]                        
           ++ NTAC 21 (POP_ASSUM MP_TAC)
           ++ POP_ASSUM (MP_TAC o GSYM o Q.SPECL [`1`, `0`, `n`])
           ++ RW_TAC real_ss [Lt_def, Trans_def, measureTheory.space_def, IN_COUNT]
           ++ FULL_SIMP_TAC real_ss []) ++ POP_ORW
 ++ DEP_REWRITE_TAC [BI_COND_PROB_01]
 ++ RW_TAC std_ss []
 >> (MAP_EVERY Q.EXISTS_TAC [`c`, `d`]
    ++ RW_TAC std_ss [BINARY_CHANNELS_MODEL_def, th_dtmc_def, measureTheory.space_def, FINITE_COUNT])
 ++ NTAC 2 (POP_ASSUM K_TAC)
 ++ POP_ASSUM (MP_TAC o GSYM)
 ++ RW_TAC std_ss [REAL_EQ_LADD]  
 ++ Cases_on `b = 0` >> RW_TAC std_ss [REAL_MUL_LZERO]
 ++ `!(x:real) y z. x - y + z + y = x + z` by REAL_ARITH_TAC 
 ++ RW_TAC std_ss [REAL_EQ_LMUL, REAL_EQ_SUB_LADD, REAL_DIV_ADD, REAL_ADD_ASSOC, REAL_DIV_REFL]);

val BI_TERNNAL_NSTEP_01_PROBABILITY = prove
  (``!X p (a:real) b (n:num) c d.        
       (BINARY_CHANNELS_MODEL X p a b c d) ==>                                    
       (cond_prob p (PREIMAGE (X n) {(1:num)} INTER p_space p) 
                  (PREIMAGE (X 0) {(0:num)} INTER p_space p) = 
        (a - a * (1 - a - b) pow n) / (a + b))``,
    RW_TAC std_ss []
 ++ MATCH_MP_TAC BI_COND_PROB_01
 ++ MAP_EVERY Q.EXISTS_TAC [`c`, `d`]
 ++ RW_TAC std_ss []
 ++ MATCH_MP_TAC BI_TERNNAL_NSTEP_00_PROBABILITY
 ++ MAP_EVERY Q.EXISTS_TAC [`c`, `d`]
 ++ RW_TAC std_ss []);
 
val BI_COND_PROB_11 = prove
  (``!X p (a:real) b (n:num) c d.        
       BINARY_CHANNELS_MODEL X p a b c d /\
       (cond_prob p (PREIMAGE (X n) {(0:num)} INTER p_space p) 
                  (PREIMAGE (X 0) {(1:num)} INTER p_space p) = 
        (b - b * (1 - a - b) pow n) / (a + b)) ==>                                    
       (cond_prob p (PREIMAGE (X n) {(1:num)} INTER p_space p) 
                  (PREIMAGE (X 0) {(1:num)} INTER p_space p) = 
        (a + b * (1 - a - b) pow n) / (a + b))``,
    RW_TAC std_ss [BINARY_CHANNELS_MODEL_def, th_dtmc_def, dtmc_def]
 ++ `prob_space p` by PSET_TAC [mc_property_def, random_variable_def]   
 ++ `prob p (PREIMAGE (X 0) {1} INTER p_space p) <> 0`
 	by (PSET_TAC [th_dtmc_def, dtmc_def, mc_property_def, random_variable_def, 
    		distribution_def, measureTheory.space_def, Linit_def]
           ++ NTAC 14 (POP_ASSUM MP_TAC)
           ++ POP_ASSUM (MP_TAC o Q.SPEC `1`)
           ++ RW_TAC arith_ss[REAL_LT_IMP_NE])             
 ++ `count 2 = {0} UNION {1:num}` 
 	by (PSET_TAC [count_def, EXTENSION] ++ RW_TAC arith_ss [])            
 ++ `SIGMA (\k. cond_pmf p (X (0 + n)) (X 0) ({k}, {1})) (space (count 2, POW (count 2))) = 1`
        by (MATCH_MP_TAC SUM_ROW_MATRIX_EQ_ONE ++ MAP_EVERY Q.EXISTS_TAC [`Linit c d`, `Lt a b`]
           ++ RW_TAC std_ss [dtmc_def, distribution_def, measureTheory.space_def, FINITE_COUNT, REAL_LT_LE]
           ++ MATCH_MP_TAC PROB_POSITIVE ++ RW_TAC std_ss []
           ++ MATCH_MP_TAC DTMC_EVENTS
           ++ MAP_EVERY Q.EXISTS_TAC [`(count 2, POW (count 2))`, `Linit c d`, `Lt a b`]
           ++ RW_TAC std_ss [dtmc_def]) 
 ++ PSET_TAC [measureTheory.space_def, COND_PMF_EQ_COND_PROB, count_def] 	           
 ++ POP_ASSUM MP_TAC
 ++ DEP_REWRITE_TAC [REAL_SUM_IMAGE_DISJOINT_UNION, REAL_SUM_IMAGE_SING]
 ++ ONCE_REWRITE_TAC [REAL_ADD_COMM]
 ++ PSET_TAC [FINITE_SING, GSYM REAL_EQ_SUB_LADD, REAL_EQ_SUB_RADD]  
 ++ ONCE_REWRITE_TAC [EQ_SYM_EQ]
 ++ `b + a = a + b` by RW_TAC std_ss [REAL_ADD_COMM]
 ++ RW_TAC std_ss [REAL_EQ_SUB_LADD, REAL_DIV_ADD, REAL_ADD_ASSOC]
 ++ `!(a:real) b c. b + a + (c - b) = a + c` by REAL_ARITH_TAC
 ++ `~(a + b = 0)` by (SPOSE_NOT_THEN STRIP_ASSUME_TAC
    ++ `(1 - a - b) = 1 - (a + b)` by REAL_ARITH_TAC
    ++ FULL_SIMP_TAC std_ss [REAL_SUB_RZERO, ABS_1,REAL_LT_REFL]) 
 ++ RW_TAC std_ss [REAL_DIV_REFL]);
 
val BI_TERNNAL_NSTEP_10_PROBABILITY = prove
  (``!X p (a:real) b (n:num) c d.        
       (BINARY_CHANNELS_MODEL X p a b c d) ==>                                    
       (cond_prob p (PREIMAGE (X n) {(0:num)} INTER p_space p) 
                  (PREIMAGE (X 0) {(1:num)} INTER p_space p) = 
        (b - b * (1 - a - b) pow n) / (a + b))``,
    RW_TAC std_ss [BINARY_CHANNELS_MODEL_def]
 ++ `prob_space p` by PSET_TAC [th_dtmc_def, dtmc_def, mc_property_def, random_variable_def]    
 ++ `0 <= (a + b)` by RW_TAC std_ss [REAL_LE_ADD]
 ++ `~(a + b = 0)` by (SPOSE_NOT_THEN STRIP_ASSUME_TAC
    ++ `(1 - a - b) = 1 - (a + b)` by REAL_ARITH_TAC
    ++ FULL_SIMP_TAC std_ss [REAL_SUB_RZERO, ABS_1,REAL_LT_REFL])
 ++ RW_TAC std_ss []   
 ++ Induct_on `n`
 >> (RW_TAC std_ss [pow, REAL_MUL_RID, REAL_SUB_REFL, REAL_DIV_LZERO, cond_prob_def]
    ++ `DISJOINT (PREIMAGE (X 0) {0} INTER p_space p)
       (PREIMAGE (X 0) {1} INTER p_space p)` 
        by (MATCH_MP_TAC DISJOINT_PROC_INTER ++ RW_TAC arith_ss [])
    ++ PSET_TAC [PROB_EMPTY, REAL_DIV_LZERO])
 ++ (MP_TAC o Q.SPECL [`X`, `p`, `(count 2, POW (count 2))`, `n`, `1`, `0`, 
 	`Linit c d`, `Lt a b`, `0`] o INST_TYPE [``:'b`` |-> ``:num``])
 	MC_NSTEP_COND_PROB 
 ++ PSET_TAC [ADD1, th_dtmc_def, COND_PMF_EQ_COND_PROB, measureTheory.space_def]
 ++ `count 2 = {0} UNION {1:num}` 
 	by (PSET_TAC [count_def, EXTENSION] ++ RW_TAC arith_ss [])  
 ++ RW_TAC std_ss [] ++ POP_ASSUM K_TAC 
 ++ DEP_REWRITE_TAC [REAL_SUM_IMAGE_DISJOINT_UNION, REAL_SUM_IMAGE_SING]	    
 ++ PSET_TAC [FINITE_SING] ++ POP_ASSUM K_TAC 
 ++ Cases_on `prob p (PREIMAGE (X n) {0} INTER p_space p) = 0`
 >> (`cond_prob p (PREIMAGE (X (n + 1)) {0} INTER p_space p)
      (PREIMAGE (X n) {0} INTER p_space p) = 0` 
      by (DEP_REWRITE_TAC [COND_PROB_ZERO, DTMC_EVENTS]
         ++ RW_TAC std_ss []
         ++ MAP_EVERY Q.EXISTS_TAC [`(count 2, POW (count 2))`, `Linit c d`, `Lt a b`]
         ++ RW_TAC std_ss []) ++ RW_TAC std_ss [REAL_MUL_LZERO, REAL_ADD_LID]
    ++ `prob p (PREIMAGE (X n) {1} INTER p_space p) = 1` 
                by (MATCH_MP_TAC BI_PROB_01 ++ MAP_EVERY Q.EXISTS_TAC [`a`, `b`, `c`, `d`]
                   ++ RW_TAC std_ss [BINARY_CHANNELS_MODEL_def, th_dtmc_def, 
                        measureTheory.space_def, FINITE_COUNT])      
    ++ `cond_prob p (PREIMAGE (X (n + 1)) {0} INTER p_space p)
             (PREIMAGE (X n) {1} INTER p_space p) = b` 
        by (PSET_TAC [dtmc_def, distribution_def, measureTheory.space_def]                        
           ++ NTAC 19 (POP_ASSUM MP_TAC)
           ++ POP_ASSUM (MP_TAC o GSYM o Q.SPECL [`1`, `0`, `n`])
           ++ RW_TAC real_ss [Lt_def, Trans_def, measureTheory.space_def, IN_COUNT]
           ++ FULL_SIMP_TAC real_ss []) ++ POP_ORW
    ++ DEP_REWRITE_TAC [BI_COND_PROB_11]
    ++ RW_TAC real_ss [BI_TERNNAL_TRANS_10_PROBABILITY]
    >> (MAP_EVERY Q.EXISTS_TAC [`c`, `d`]
       ++ RW_TAC std_ss [BINARY_CHANNELS_MODEL_def, th_dtmc_def, measureTheory.space_def, FINITE_COUNT]) 
    ++ `cond_prob p (PREIMAGE (X n) {0} INTER p_space p)
                (PREIMAGE (X 0) {1} INTER p_space p) = 0` 
      by (DEP_REWRITE_TAC [COND_PROB_INTER_ZERO, DTMC_EVENTS]
         ++ RW_TAC std_ss []
         ++ MAP_EVERY Q.EXISTS_TAC [`(count 2, POW (count 2))`, `Linit c d`, `Lt a b`]
         ++ RW_TAC std_ss []) ++ FULL_SIMP_TAC std_ss []
    ++ `(b - b * (1 - a - b) pow n) / (a + b) = 0` by METIS_TAC [] 
    ++ `!(x:real) y. y <> 0 /\ (x / y = 0) ==> (x = 0)`
        by METIS_TAC [real_div, REAL_ENTIRE, REAL_INV_NZ] 
    ++ `b * (1 - a - b) pow n = b` by METIS_TAC [REAL_SUB_0] 
    ++ ONCE_REWRITE_TAC [GSYM ADD1] ++ ONCE_REWRITE_TAC [pow]
    ++ `!(x:real) y z. x * (y * z) = y * (x * z)` by METIS_TAC [REAL_MUL_ASSOC, REAL_MUL_COMM]
    ++ NTAC 2 (POP_ORW) ++ `b - (1 - a - b) * b = b * (a + b)` by REAL_ARITH_TAC ++ POP_ORW
    ++ METIS_TAC [real_div, REAL_MUL_ASSOC])
 ++ Cases_on `prob p (PREIMAGE (X n) {1} INTER p_space p) = 0`       
 >> (`cond_prob p (PREIMAGE (X (n + 1)) {0} INTER p_space p)
             (PREIMAGE (X n) {1} INTER p_space p) = 0` 
      by (DEP_REWRITE_TAC [COND_PROB_ZERO, DTMC_EVENTS]
         ++ RW_TAC std_ss []
         ++ MAP_EVERY Q.EXISTS_TAC [`(count 2, POW (count 2))`, `Linit c d`, `Lt a b`]
         ++ RW_TAC std_ss []) ++ RW_TAC std_ss [REAL_MUL_LZERO, REAL_ADD_RID]
    ++ `cond_prob p (PREIMAGE (X (n + 1)) {0} INTER p_space p)
             (PREIMAGE (X n) {0} INTER p_space p) = 1 - a` 
        by (PSET_TAC [dtmc_def, distribution_def, measureTheory.space_def]                        
           ++ NTAC 19 (POP_ASSUM MP_TAC)
           ++ POP_ASSUM (MP_TAC o GSYM o Q.SPECL [`0`, `0`, `n`])
           ++ RW_TAC real_ss [Lt_def, Trans_def, measureTheory.space_def, IN_COUNT]
           ++ FULL_SIMP_TAC real_ss []) ++ POP_ORW    
    ++ DEP_REWRITE_TAC [GSYM BI_TERNNAL_TRANS_10_PROBABILITY]
    ++ RW_TAC real_ss [] ++ ONCE_REWRITE_TAC [EQ_SYM_EQ] ++ RW_TAC std_ss [REAL_ADD_RID_UNIQ]    
    ++ Cases_on `b = 0` >> RW_TAC real_ss []
    ++ RW_TAC real_ss [REAL_ENTIRE, REAL_SUB_0]
    ++ NTAC 4 (POP_ASSUM MP_TAC) ++ POP_ASSUM (MP_TAC o GSYM)
    ++ RW_TAC std_ss [] ++ ONCE_REWRITE_TAC [EQ_SYM_EQ]
    ++ `prob p (PREIMAGE (X 0) {1} INTER p_space p) <> 0`
 	by (PSET_TAC [th_dtmc_def, dtmc_def, mc_property_def, random_variable_def, 
    		distribution_def, measureTheory.space_def, Linit_def]
           ++ NTAC 20 (POP_ASSUM MP_TAC)
           ++ POP_ASSUM (MP_TAC o Q.SPEC `1`)
           ++ RW_TAC arith_ss[REAL_LT_IMP_NE])             
    ++ `count 2 = {0} UNION {1:num}` 
 	by (PSET_TAC [count_def, EXTENSION] ++ RW_TAC arith_ss []) 
    ++ `cond_prob p (PREIMAGE (X n) {1} INTER p_space p)
                    (PREIMAGE (X 0) {1} INTER p_space p) = 0`
        by (DEP_REWRITE_TAC [COND_PROB_INTER_ZERO, DTMC_EVENTS]
           ++ RW_TAC std_ss []
           ++ MAP_EVERY Q.EXISTS_TAC [`(count 2, POW (count 2))`, `Linit c d`, `Lt a b`]
           ++ RW_TAC std_ss [])
    ++ `SIGMA (\k. cond_pmf p (X (0 + n)) (X 0) ({k}, {1})) (space (count 2, POW (count 2))) = 1`
        by (MATCH_MP_TAC SUM_ROW_MATRIX_EQ_ONE 
           ++ MAP_EVERY Q.EXISTS_TAC [`Linit c d`, `Lt a b`] 
              ++ RW_TAC std_ss [distribution_def, measureTheory.space_def, FINITE_UNION, 
                FINITE_SING, REAL_LT_LE]
              ++ MATCH_MP_TAC PROB_POSITIVE ++ RW_TAC std_ss []
              ++ MATCH_MP_TAC DTMC_EVENTS
              ++ MAP_EVERY Q.EXISTS_TAC [`(count 2, POW (count 2))`, `Linit c d`, `Lt a b`]
              ++ RW_TAC std_ss []) 
    ++ PSET_TAC [measureTheory.space_def, COND_PMF_EQ_COND_PROB] 
    ++ POP_ASSUM MP_TAC ++ DEP_REWRITE_TAC [REAL_SUM_IMAGE_DISJOINT_UNION, REAL_SUM_IMAGE_SING]      
    ++ PSET_TAC [FINITE_SING, REAL_EQ_SUB_LADD, REAL_ADD_RID])
 ++ `cond_prob p (PREIMAGE (X (n + 1)) {0} INTER p_space p)
             (PREIMAGE (X n) {0} INTER p_space p) = 1 - a` 
        by (PSET_TAC [dtmc_def, distribution_def, measureTheory.space_def]                        
           ++ NTAC 18 (POP_ASSUM MP_TAC)
           ++ POP_ASSUM (MP_TAC o GSYM o Q.SPECL [`0`, `0`, `n`])
           ++ RW_TAC real_ss [Lt_def, Trans_def, measureTheory.space_def, IN_COUNT]
           ++ FULL_SIMP_TAC real_ss []) ++ POP_ORW            
 ++ `cond_prob p (PREIMAGE (X (n + 1)) {0} INTER p_space p)
             (PREIMAGE (X n) {1} INTER p_space p) = b` 
        by (PSET_TAC [dtmc_def, distribution_def, measureTheory.space_def]                        
           ++ NTAC 18 (POP_ASSUM MP_TAC)
           ++ POP_ASSUM (MP_TAC o GSYM o Q.SPECL [`1`, `0`, `n`])
           ++ RW_TAC real_ss [Lt_def, Trans_def, measureTheory.space_def, IN_COUNT]
           ++ FULL_SIMP_TAC real_ss []) ++ POP_ORW
 ++ DEP_REWRITE_TAC [BI_COND_PROB_11]
 ++ RW_TAC std_ss [GSYM BI_TERNNAL_TRANS_10_PROBABILITY]
 >> (MAP_EVERY Q.EXISTS_TAC [`c`, `d`]
    ++ RW_TAC std_ss [BINARY_CHANNELS_MODEL_def, th_dtmc_def, 
                        measureTheory.space_def, FINITE_COUNT])
 ++ RW_TAC std_ss [REAL_EQ_LADD]
 ++ Cases_on `b = 0` >> RW_TAC std_ss [REAL_MUL_LZERO]
 ++ `!(x:real) y z. x + y + (z - y) = x + z` by REAL_ARITH_TAC 
 ++ RW_TAC std_ss [REAL_EQ_LMUL, REAL_EQ_SUB_LADD, REAL_DIV_ADD, REAL_ADD_ASSOC, REAL_DIV_REFL]);
 
val BI_TERNNAL_NSTEP_11_PROBABILITY = prove
  (``!X p (a:real) b (n:num) c d.        
       (BINARY_CHANNELS_MODEL X p a b c d) ==>                                    
       (cond_prob p (PREIMAGE (X n) {(1:num)} INTER p_space p) 
                  (PREIMAGE (X 0) {(1:num)} INTER p_space p) = 
        (a + b * (1 - a - b) pow n) / (a + b))``,
    RW_TAC std_ss []
 ++ MATCH_MP_TAC BI_COND_PROB_11
 ++ MAP_EVERY Q.EXISTS_TAC [`c`, `d`]
 ++ RW_TAC std_ss []
 ++ MATCH_MP_TAC BI_TERNNAL_NSTEP_10_PROBABILITY
 ++ MAP_EVERY Q.EXISTS_TAC [`c`, `d`]
 ++ RW_TAC std_ss []); 
                         	

(*===================================================================*)
(*==   4.  some prepared theorems for proving limit probabilities  ==*)
(*===================================================================*)
val PART_COMM_00_LIM = prove
  (``!(a:real) (b:real).        
   (abs (1 - a - b) < 1) /\ (a <= 1) /\ (0 <= a) /\ (b <= 1) /\ (0 <= b) ==> 
   ((\n. (b + a * ((1:real) - a - b) pow n)) --> b)``,
     RW_TAC std_ss []
 ++ `((\n. b + a * (1 - a - b) pow n) --> b) = ((\n. b + a * (1 - a - b) pow n) --> (b + 0))` 
 	by RW_TAC real_ss [GSYM REAL_ADD_RID] ++ POP_ORW
 ++ `((\n. b + a * (1 - a - b) pow n)) = 
     (\n. (\n. b) n + (\n. a * (1 - a - b) pow n) n)` by RW_TAC std_ss []
 ++ POP_ORW
 ++ MATCH_MP_TAC SEQ_ADD
 ++ RW_TAC real_ss [SEQ_CONST]
 ++ `0 = a * 0` by RW_TAC real_ss [GSYM REAL_MUL_RZERO] ++ POP_ORW
 ++ `(\n. a * (1 - a - b) pow n) = (\n. (\n. a) n * (\n. (1 - a - b) pow n) n)`
   	by RW_TAC std_ss [] ++ POP_ORW
 ++ MATCH_MP_TAC SEQ_MUL
 ++ RW_TAC real_ss [SEQ_CONST]
 ++ MATCH_MP_TAC SEQ_POWER
 ++ RW_TAC std_ss []);

val PART_COMM_10_LIM = prove
  (``!(a:real) (b:real).        
   (abs (1 - a - b) < 1) /\ (a <= 1) /\ (0 <= a) /\ (b <= 1) /\ (0 <= b) ==> 
   ((\n. (b - b * ((1:real) - a - b) pow n)) --> b)``,
    RW_TAC std_ss []
 ++ `((\n. b - b * (1 - a - b) pow n) --> b) = ((\n. b - b * (1 - a - b) pow n) --> (b - 0))` 
 	by RW_TAC real_ss [GSYM REAL_ADD_RID] ++ POP_ORW
 ++ `((\n. b - b * (1 - a - b) pow n)) = 
   (\n. (\n. b) n - (\n. b * (1 - a - b) pow n) n)` by RW_TAC std_ss [] ++ POP_ORW
 ++ MATCH_MP_TAC SEQ_SUB
 ++ RW_TAC real_ss [SEQ_CONST]
 ++ `0 = b * 0` by RW_TAC real_ss [GSYM REAL_MUL_RZERO]
 ++ `(\n. b * (1 - a - b) pow n) = (\n. (\n. b) n * (\n. (1 - a - b) pow n) n)`
	by RW_TAC std_ss [] ++ ONCE_ASM_REWRITE_TAC []
 ++ MATCH_MP_TAC SEQ_MUL
 ++ RW_TAC real_ss [SEQ_CONST]
 ++ MATCH_MP_TAC SEQ_POWER
 ++ RW_TAC std_ss []);

val N_TRANSIENT_MATRIX_00_LIM = prove
  (``!(a:real) (b:real).        
   (abs (1 - a - b) < 1) /\ (a <= 1) /\ (0 <= a) /\ (b <= 1) /\ (0 <= b) ==> 
   ((\n. (b + a * ((1:real) - a - b) pow n) / (a + b)) --> (b / (a + b)))``,
   RW_TAC std_ss [real_div]
 ++ `(\n. (b + a * (1 - a - b) pow n) * inv (a + b)) = 
   (\n. (\n. (b + a * (1 - a - b) pow n)) n * (\n. inv (a + b)) n)`
   	by RW_TAC std_ss [] ++ ONCE_ASM_REWRITE_TAC []
 ++ MATCH_MP_TAC SEQ_MUL
 ++ RW_TAC real_ss [SEQ_CONST]
 ++ RW_TAC std_ss [PART_COMM_00_LIM]);

val N_TRANSIENT_MATRIX_01_LIM = prove
  (``!(a:real) (b:real).        
   (abs (1 - a - b) < 1) /\ (a <= 1) /\ (0 <= a) /\ (b <= 1) /\ (0 <= b) ==> 
   ((\n. (a - a * ((1:real) - a - b) pow n) / (a + b)) --> (a / (a + b)))``,
    RW_TAC std_ss [real_div]
 ++ `0 <= (a + b)` by RW_TAC std_ss [REAL_LE_ADD]
 ++ `(\n. (a - a * (1 - a - b) pow n) * inv (a + b)) = 
   (\n. (\n. (a - a * (1 - a - b) pow n)) n * (\n. inv (a + b)) n)`
   by RW_TAC std_ss [] ++ ONCE_ASM_REWRITE_TAC []
 ++ MATCH_MP_TAC SEQ_MUL
 ++ RW_TAC real_ss [SEQ_CONST]
 ++ `1 - a - b = 1 - b - a` by REAL_ARITH_TAC
 ++ ONCE_ASM_REWRITE_TAC []
 ++ MATCH_MP_TAC PART_COMM_10_LIM
 ++ RW_TAC std_ss []
 ++ POP_ASSUM (MP_TAC o GSYM)
 ++ RW_TAC std_ss []);

(*===============================================================*)
(*==    5.  four limit probabilities theorems for proving      ==*)
(*===============================================================*)
val BINARY_STEADY_STATE = store_thm
  ("BINARY_STEADY_STATE",
   ``!X p (a:real) b c d.        
       (BINARY_CHANNELS_MODEL X p a b c d) ==> 
       (lim (\n. cond_prob p (PREIMAGE (X n) {(0:num)} INTER p_space p)
       			(PREIMAGE (X 0) {(0:num)} INTER p_space p)) = b / (a + b)) /\
       (lim (\n. cond_prob p (PREIMAGE (X n) {(1:num)} INTER p_space p)
       			(PREIMAGE (X 0) {(0:num)} INTER p_space p)) = a / (a + b)) /\
       (lim (\n. cond_prob p (PREIMAGE (X n) {(0:num)} INTER p_space p)
       			(PREIMAGE (X 0) {(1:num)} INTER p_space p)) = b / (a + b)) /\
       (lim (\n. cond_prob p (PREIMAGE (X n) {(1:num)} INTER p_space p)
       			(PREIMAGE (X 0) {(1:num)} INTER p_space p)) = a / (a + b))``,
    RW_TAC std_ss []
 << [`!(n:num). cond_prob p (PREIMAGE (X n) {(0:num)} INTER p_space p)
       			(PREIMAGE (X 0) {(0:num)} INTER p_space p) =
        (b + a * (1 - a - b) pow n) / (a + b)`
      by METIS_TAC [BI_TERNNAL_NSTEP_00_PROBABILITY] 
     ++ FULL_SIMP_TAC std_ss [BINARY_CHANNELS_MODEL_def, th_dtmc_def] 
     ++ MATCH_MP_TAC TEND2LIM
     ++ METIS_TAC [N_TRANSIENT_MATRIX_00_LIM],
     
     `!(n:num). cond_prob p (PREIMAGE (X n) {(1:num)} INTER p_space p)
       			(PREIMAGE (X 0) {(0:num)} INTER p_space p) = 
        (a - a * (1 - a - b) pow n) / (a + b)`
      by METIS_TAC [BI_TERNNAL_NSTEP_01_PROBABILITY] 
     ++ FULL_SIMP_TAC std_ss [BINARY_CHANNELS_MODEL_def, th_dtmc_def]
     ++ MATCH_MP_TAC TEND2LIM
     ++ METIS_TAC [N_TRANSIENT_MATRIX_01_LIM],
     
     `!n. cond_prob p (PREIMAGE (X n) {(0:num)} INTER p_space p)
       			(PREIMAGE (X 0) {(1:num)} INTER p_space p) = 
        (b - b * (1 - a - b) pow n) / (a + b)`
       by (RW_TAC std_ss [] ++ `1 - a - b = 1 - b - a` by REAL_ARITH_TAC
          ++ METIS_TAC [BI_TERNNAL_NSTEP_10_PROBABILITY])
     ++ FULL_SIMP_TAC std_ss [BINARY_CHANNELS_MODEL_def, th_dtmc_def] 
     ++ MATCH_MP_TAC TEND2LIM
     ++ `1 - a - b = 1 - b - a` by REAL_ARITH_TAC
     ++ ONCE_ASM_REWRITE_TAC [REAL_ADD_COMM]
     ++ MATCH_MP_TAC N_TRANSIENT_MATRIX_01_LIM
     ++ POP_ASSUM (MP_TAC o GSYM)
     ++ RW_TAC std_ss [],
     
     `!(n:num). cond_prob p (PREIMAGE (X n) {(1:num)} INTER p_space p)
       			(PREIMAGE (X 0) {(1:num)} INTER p_space p) = 
        (a + b * (1 - a - b) pow n) / (a + b)`
       by (RW_TAC std_ss [] ++ `1 - a - b = 1 - b - a` by REAL_ARITH_TAC
          ++ METIS_TAC [BI_TERNNAL_NSTEP_11_PROBABILITY, REAL_ADD_COMM])
       ++ FULL_SIMP_TAC std_ss [BINARY_CHANNELS_MODEL_def, th_dtmc_def]
       ++ MATCH_MP_TAC TEND2LIM
       ++ `1 - a - b = 1 - b - a` by REAL_ARITH_TAC
       ++ `a + b = b + a` by REAL_ARITH_TAC
       ++ ONCE_ASM_REWRITE_TAC []
       ++ MATCH_MP_TAC N_TRANSIENT_MATRIX_00_LIM
       ++ POP_ASSUM K_TAC
       ++ POP_ASSUM (MP_TAC o GSYM)
       ++ RW_TAC std_ss []]);
