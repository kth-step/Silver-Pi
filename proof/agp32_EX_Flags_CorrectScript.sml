open hardwarePreamble translatorTheory translatorLib arithmeticTheory wordsExtraTheory dep_rewrite blastLib bitstringSyntax fcpSyntax listSyntax wordsSyntax agp32StateTheory agp32EnvironmentTheory agp32ProcessorTheory ag32Theory ag32ExtraTheory ag32UtilitiesTheory agp32RelationTheory agp32UpdateTheory agp32InternalTheory agp32SpecialTheory agp32_EX_CorrectTheory;

(* correctness of EX stage flags with respect to the ISA *)
val _ = new_theory "agp32_EX_Flags_Correct";

val _ = prefer_num ();
val _ = guess_lengths ();


(** lemma **)
Theorem overflow_rewrite[local]:
  !x y.
    w2i x + w2i y <> w2i (x + y) <=>
    (word_msb x <=> word_msb y) /\ (word_msb x <> word_msb (x + y))
Proof
  METIS_TAC [integer_wordTheory.overflow]
QED

Theorem sub_overflow_rewrite[local]:
  !x y.
    w2i x - w2i y <> w2i (x - y) <=>
    (word_msb x <> word_msb y) /\ (word_msb x <> word_msb (x - y))
Proof
  METIS_TAC [integer_wordTheory.sub_overflow]
QED

(** when EX is NONE, the EX_carry_flag and EX_overflow_flag are unchanged **)
Theorem agp32_Rel_EX_NONE_flags_unchanged:
  !fext fbits a t I.
    is_sch I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (3,SUC t) = NONE ==>
    ((agp32 fext fbits (SUC t)).EX.EX_carry_flag = (agp32 fext fbits t).EX.EX_carry_flag) /\
    ((agp32 fext fbits (SUC t)).EX.EX_overflow_flag = (agp32 fext fbits t).EX.EX_overflow_flag)
Proof
  rpt gen_tac >> rpt disch_tac >>
  Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state;WB_pipeline;MEM_pipeline;EX_pipeline;
                            REG_write;ID_pipeline;IF_PC_update;Acc_compute] (fext t) s s` >>
  Q.ABBREV_TAC `s'' = procs [IF_instr_update;ID_opc_func_update;ID_imm_update;ID_data_update;
                             ID_data_check_update;EX_ALU_input_imm_update] (fext (SUC t)) s' s'` >>
  `((agp32 fext fbits (SUC t)).EX.EX_carry_flag =
    (EX_ALU_update (fext (SUC t)) s' s'').EX.EX_carry_flag) /\
  ((agp32 fext fbits (SUC t)).EX.EX_overflow_flag =
   (EX_ALU_update (fext (SUC t)) s' s'').EX.EX_overflow_flag)`
    by fs [agp32_EX_ALU_items_updated_by_EX_ALU_update] >>
  `(s''.ID.ID_EX_write_enable = s.ID.ID_EX_write_enable) /\
  (s''.EX.EX_overflow_flag = s.EX.EX_overflow_flag) /\
  (s''.EX.EX_carry_flag = s.EX.EX_carry_flag)`
    by METIS_TAC [agp32_same_items_until_EX_ALU_update,Abbr `s`,Abbr `s'`,Abbr `s''`] >>
  `(s''.EX.EX_ALU_input1 = (agp32 fext fbits (SUC t)).EX.EX_ALU_input1) /\
  (s''.EX.EX_ALU_input2 = (agp32 fext fbits (SUC t)).EX.EX_ALU_input2) /\
  (s''.EX.EX_func = (agp32 fext fbits (SUC t)).EX.EX_func) /\
  (s''.EX.EX_opc = (agp32 fext fbits (SUC t)).EX.EX_opc)`
    by METIS_TAC [agp32_same_EX_ALU_input_until_ALU_update,agp32_same_EX_opc_func_until_ALU_update,
                  Abbr `s`,Abbr `s'`,Abbr `s''`] >>
  Cases_on `enable_stg 3 (agp32 fext fbits t)` >-
   (`s''.ID.ID_EX_write_enable` by fs [enable_stg_def,Abbr `s`] >>
    `((agp32 fext fbits (SUC t)).EX.EX_opc = 16w) \/ ((agp32 fext fbits (SUC t)).EX.EX_opc = 15w)`
      by METIS_TAC [EX_instr_index_NONE_opc_flush] >>
    `(s''.EX.EX_func = 9w) \/ (s''.EX.EX_func = 12w) \/ (s''.EX.EX_func = 13w) \/
    (s''.EX.EX_func = 14w) \/ (s''.EX.EX_func = 15w)`
      by fs [agp32_EX_opc_implies_EX_func] >>
    fs [EX_ALU_update_def]) >>
  `~s''.ID.ID_EX_write_enable` by fs [enable_stg_def,Abbr `s`] >>
  fs [EX_ALU_update_def]
QED


(** EX_carry_flag **)
Theorem agp32_Rel_ag32_EX_ALU_carry_flag_correct:
  !fext fbits a t I.
    is_sch I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (3,SUC t) <> NONE ==>
    (agp32 fext fbits (SUC t)).EX.EX_carry_flag = (FUNPOW Next (THE (I (3,SUC t))) a).CarryFlag
Proof
  rw [] >> Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state;WB_pipeline;MEM_pipeline;EX_pipeline;
                            REG_write;ID_pipeline;IF_PC_update;Acc_compute] (fext t) s s` >>
  Q.ABBREV_TAC `s'' = procs [IF_instr_update;ID_opc_func_update;ID_imm_update;ID_data_update;
                             ID_data_check_update;EX_ALU_input_imm_update] (fext (SUC t)) s' s'` >>
  `(agp32 fext fbits (SUC t)).EX.EX_carry_flag = (EX_ALU_update (fext (SUC t)) s' s'').EX.EX_carry_flag`
    by fs [agp32_EX_ALU_items_updated_by_EX_ALU_update] >>
  `(s''.ID.ID_EX_write_enable = s.ID.ID_EX_write_enable) /\
  (s''.EX.EX_overflow_flag = s.EX.EX_overflow_flag) /\
  (s''.EX.EX_carry_flag = s.EX.EX_carry_flag) /\
  (s''.EX.EX_ALU_res = s.EX.EX_ALU_res)`
    by METIS_TAC [agp32_same_items_until_EX_ALU_update,Abbr `s`,Abbr `s'`,Abbr `s''`] >>
  `(s''.EX.EX_ALU_input1 = (agp32 fext fbits (SUC t)).EX.EX_ALU_input1) /\
  (s''.EX.EX_ALU_input2 = (agp32 fext fbits (SUC t)).EX.EX_ALU_input2) /\
  (s''.EX.EX_func = (agp32 fext fbits (SUC t)).EX.EX_func) /\
  (s''.EX.EX_opc = (agp32 fext fbits (SUC t)).EX.EX_opc)`
    by METIS_TAC [agp32_same_EX_ALU_input_until_ALU_update,agp32_same_EX_opc_func_until_ALU_update,
                  Abbr `s`,Abbr `s'`,Abbr `s''`] >>
  Cases_on `enable_stg 3 (agp32 fext fbits t)` >-
   (`s''.ID.ID_EX_write_enable` by fs [enable_stg_def,Abbr `s`] >>
    `s''.EX.EX_func = func (FUNPOW Next (THE (I' (3,SUC t)) − 1) a)`
      by fs [is_sch_def,agp32_Rel_ag32_EX_func_correct] >>
    `s''.EX.EX_opc = opc (FUNPOW Next (THE (I' (3,SUC t)) − 1) a)`
      by fs [is_sch_def,agp32_Rel_ag32_EX_opc_correct] >>
    `s''.EX.EX_ALU_input1 = ALU_input1 (FUNPOW Next (THE (I' (3,SUC t)) − 1) a)`
      by fs [is_sch_def,agp32_Rel_ag32_EX_ALU_input1_correct] >>
    `s''.EX.EX_ALU_input2 = ALU_input2 (FUNPOW Next (THE (I' (3,SUC t)) − 1) a)`
      by fs [is_sch_def,agp32_Rel_ag32_EX_ALU_input2_correct] >>
    Cases_on `I' (3,t) <> NONE` >-
     (`THE (I' (3,SUC t)) = SUC (THE (I' (3,t)))`
        by METIS_TAC [EX_instr_index_t_SUC_t_enable,ADD1] >> fs [FUNPOW_SUC] >>
      Q.ABBREV_TAC `ai = FUNPOW Next (THE (I' (3,t))) a` >>
      rw [Next_def,GSYM word_at_addr_def,GSYM align_addr_def] >>
      Cases_on `Decode (word_at_addr ai.MEM (align_addr ai.PC))` >-
       (PairCases_on `p` >> rw [Run_def,dfn'Accelerator_def,incPC_def] >>
        `opc ai = 8w` by fs [ag32_Decode_Acc_opc_8w] >>
        `(s''.EX.EX_func = 9w) \/ (s''.EX.EX_func = 12w) \/ (s''.EX.EX_func = 13w) \/
        (s''.EX.EX_func = 14w) \/ (s''.EX.EX_func = 15w)`
          by fs [agp32_EX_opc_implies_EX_func] >>
        fs [EX_ALU_update_def,Rel_def]) >-
       (rw [Run_def,dfn'In_def,incPC_def] >>
        `opc ai = 7w` by fs [ag32_Decode_In_opc_7w] >>
        `(s''.EX.EX_func = 9w) \/ (s''.EX.EX_func = 12w) \/ (s''.EX.EX_func = 13w) \/
        (s''.EX.EX_func = 14w) \/ (s''.EX.EX_func = 15w)`
          by fs [agp32_EX_opc_implies_EX_func] >>
        fs [EX_ALU_update_def,Rel_def]) >-
       (rw [Run_def,dfn'Interrupt_def,incPC_def] >>
        `opc ai = 12w` by fs [ag32_Decode_Interrupt_opc_12w] >>
        `(s''.EX.EX_func = 9w) \/ (s''.EX.EX_func = 12w) \/ (s''.EX.EX_func = 13w) \/
        (s''.EX.EX_func = 14w) \/ (s''.EX.EX_func = 15w)`
          by fs [agp32_EX_opc_implies_EX_func] >>
        fs [EX_ALU_update_def,Rel_def]) >-
       (PairCases_on `p` >> rw [Run_def,dfn'Jump_def] >>
        `opc ai = 9w` by fs [ag32_Decode_Jump_opc_9w] >>
        pairarg_tac >> fs [] >>
        Cases_on `p0 = fAdd` >-
         (fs [ALU_def] >> rw [] >>
          `func ai = 0w` by fs [ag32_Decode_Jump_fAdd_func_0w] >> fs [] >>
          rw [EX_ALU_update_def,ALU_correct_carry_lem,WORD_LS,word_add_def,w2n_w2w] >>
          fs [ALU_input1_def,ALU_input2_def] >>
          `dataA ai = ri2word p2 ai` by fs [ag32_Decode_Jump_dataA] >>
          rw [] >> METIS_TAC [w2n_add_MOD_itself]) >>
        Cases_on `p0 = fAddWithCarry` >-
         (fs [ALU_def] >> rw [] >>
          `func ai = 1w` by fs [ag32_Decode_Jump_fAddWithCarry_func_1w] >> fs [] >>
          rw [EX_ALU_update_def,ALU_correct_carry_lem,WORD_LS,word_add_def,w2n_w2w] >>
          fs [ALU_input1_def,ALU_input2_def] >>
          `dataA ai = ri2word p2 ai` by fs [ag32_Decode_Jump_dataA] >-
           (`s.EX.EX_carry_flag` by fs [Rel_def] >>
            rw [v2w_single_1w,ALU_correct_v2w_carry33_lem] >>
            METIS_TAC [w2n_add_MOD_itself_1]) >>
          `~s.EX.EX_carry_flag` by fs [Rel_def] >>
          rw [v2w_single_0w,ALU_correct_v2w_carry33_lem] >>
          METIS_TAC [w2n_add_MOD_itself]) >>
        fs [] >> rename1 `(v,ai')` >>
        `ai'.CarryFlag = ai.CarryFlag` by (fs [ALU_def] >> Cases_on `p0` >> fs [] >> rw []) >>
        `(func ai <> 0w) /\ (func ai <> 1w)` by fs [ag32_Decode_Jump_func_not_0w_1w] >>
        fs [EX_ALU_update_def,Rel_def] >>
        Cases_on_word_value `(agp32 fext fbits (SUC t)).EX.EX_func` >> fs []) >-
       (PairCases_on `p` >> rw [Run_def,dfn'JumpIfNotZero_def] >>
        `opc ai = 11w` by fs [ag32_Decode_JumpIfNotZero_opc_11w] >>
        pairarg_tac >> fs [] >>
        Cases_on `p0 = fAdd` >-
         (fs [ALU_def] >> rw [] >>
          `func ai = 0w` by fs [ag32_Decode_JumpIfNotZero_fAdd_func_0w] >> fs [] >>
          rw [EX_ALU_update_def,ALU_correct_carry_lem,WORD_LS,word_add_def,w2n_w2w] >>
          fs [ALU_input1_def,ALU_input2_def] >>
          `(dataA ai = ri2word p2 ai) /\ (dataB ai = ri2word p3 ai)`
            by fs [ag32_Decode_JumpIfNotZero_dataA,ag32_Decode_JumpIfNotZero_dataB] >>
          rw [incPC_def] >> METIS_TAC [w2n_add_MOD_itself]) >>
        Cases_on `p0 = fAddWithCarry` >-
         (fs [ALU_def] >> rw [] >>
          `func ai = 1w` by fs [ag32_Decode_JumpIfNotZero_fAddWithCarry_func_1w] >> fs [] >>
          rw [EX_ALU_update_def,ALU_correct_carry_lem,WORD_LS,word_add_def,w2n_w2w] >>
          fs [ALU_input1_def,ALU_input2_def] >>
          `(dataA ai = ri2word p2 ai) /\ (dataB ai = ri2word p3 ai)`
            by fs [ag32_Decode_JumpIfNotZero_dataA,ag32_Decode_JumpIfNotZero_dataB] >-
           (`s.EX.EX_carry_flag` by fs [Rel_def] >>
            rw [v2w_single_1w,ALU_correct_v2w_carry33_lem] >>
            METIS_TAC [w2n_add_MOD_itself_1]) >-
           (`~s.EX.EX_carry_flag` by fs [Rel_def] >>
            rw [v2w_single_0w,ALU_correct_v2w_carry33_lem] >>
            METIS_TAC [w2n_add_MOD_itself]) >-
           (`s.EX.EX_carry_flag` by fs [Rel_def] >>
            rw [v2w_single_1w,ALU_correct_v2w_carry33_lem,incPC_def] >>
            METIS_TAC [w2n_add_MOD_itself_1]) >>
          `~s.EX.EX_carry_flag` by fs [Rel_def] >>
          rw [v2w_single_0w,ALU_correct_v2w_carry33_lem,incPC_def] >>
          METIS_TAC [w2n_add_MOD_itself]) >>
        fs [] >> rename1 `(v,ai')` >>
        `ai'.CarryFlag = ai.CarryFlag` by (fs [ALU_def] >> Cases_on `p0` >> fs [] >> rw []) >>
        `(func ai <> 0w) /\ (func ai <> 1w)` by fs [ag32_Decode_JumpIfNotZero_func_not_0w_1w] >>
        Cases_on `v` >> rw [incPC_def] >>
        fs [EX_ALU_update_def,Rel_def,incPC_def] >>
        Cases_on_word_value `(agp32 fext fbits (SUC t)).EX.EX_func` >> fs []) >-
       (PairCases_on `p` >> rw [Run_def,dfn'JumpIfZero_def] >>
        `opc ai = 10w` by fs [ag32_Decode_JumpIfZero_opc_10w] >>
        pairarg_tac >> fs [] >>
        Cases_on `p0 = fAdd` >-
         (fs [ALU_def] >> rw [] >>
          `func ai = 0w` by fs [ag32_Decode_JumpIfZero_fAdd_func_0w] >> fs [] >>
          rw [EX_ALU_update_def,ALU_correct_carry_lem,WORD_LS,word_add_def,w2n_w2w] >>
          fs [ALU_input1_def,ALU_input2_def] >>
          `(dataA ai = ri2word p2 ai) /\ (dataB ai = ri2word p3 ai)`
            by fs [ag32_Decode_JumpIfZero_dataA,ag32_Decode_JumpIfZero_dataB] >>
          rw [incPC_def] >> METIS_TAC [w2n_add_MOD_itself]) >>
        Cases_on `p0 = fAddWithCarry` >-
         (fs [ALU_def] >> rw [] >>
          `func ai = 1w` by fs [ag32_Decode_JumpIfZero_fAddWithCarry_func_1w] >> fs [] >>
          rw [EX_ALU_update_def,ALU_correct_carry_lem,WORD_LS,word_add_def,w2n_w2w] >>
          fs [ALU_input1_def,ALU_input2_def] >>
          `(dataA ai = ri2word p2 ai) /\ (dataB ai = ri2word p3 ai)`
            by fs [ag32_Decode_JumpIfZero_dataA,ag32_Decode_JumpIfZero_dataB] >-
           (`s.EX.EX_carry_flag` by fs [Rel_def] >>
            rw [v2w_single_1w,ALU_correct_v2w_carry33_lem] >>
            METIS_TAC [w2n_add_MOD_itself_1]) >-
           (`~s.EX.EX_carry_flag` by fs [Rel_def] >>
            rw [v2w_single_0w,ALU_correct_v2w_carry33_lem] >>
            METIS_TAC [w2n_add_MOD_itself]) >-
           (`s.EX.EX_carry_flag` by fs [Rel_def] >>
            rw [v2w_single_1w,ALU_correct_v2w_carry33_lem,incPC_def] >>
            METIS_TAC [w2n_add_MOD_itself_1]) >>
          `~s.EX.EX_carry_flag` by fs [Rel_def] >>
          rw [v2w_single_0w,ALU_correct_v2w_carry33_lem,incPC_def] >>
          METIS_TAC [w2n_add_MOD_itself]) >>
        fs [] >> rename1 `(v,ai')` >>
        `ai'.CarryFlag = ai.CarryFlag` by (fs [ALU_def] >> Cases_on `p0` >> fs [] >> rw []) >>
        `(func ai <> 0w) /\ (func ai <> 1w)` by fs [ag32_Decode_JumpIfZero_func_not_0w_1w] >>
        Cases_on `v` >> rw [incPC_def] >>
        fs [EX_ALU_update_def,Rel_def,incPC_def] >>
        Cases_on_word_value `(agp32 fext fbits (SUC t)).EX.EX_func` >> fs []) >-
       (PairCases_on `p` >> rw [Run_def,dfn'LoadConstant_def,incPC_def] >>
        `opc ai = 13w` by fs [ag32_Decode_LoadConstant_opc_13w] >>
        `(s''.EX.EX_func = 9w) \/ (s''.EX.EX_func = 12w) \/ (s''.EX.EX_func = 13w) \/
        (s''.EX.EX_func = 14w) \/ (s''.EX.EX_func = 15w)`
          by fs [agp32_EX_opc_implies_EX_func] >>
        fs [EX_ALU_update_def,Rel_def]) >-
       (PairCases_on `p` >> rw [Run_def,dfn'LoadMEM_def,incPC_def] >>
        `opc ai = 4w` by fs [ag32_Decode_LoadMEM_opc_4w] >>
        `(s''.EX.EX_func = 9w) \/ (s''.EX.EX_func = 12w) \/ (s''.EX.EX_func = 13w) \/
        (s''.EX.EX_func = 14w) \/ (s''.EX.EX_func = 15w)`
          by fs [agp32_EX_opc_implies_EX_func] >>
        fs [EX_ALU_update_def,Rel_def]) >-
       (PairCases_on `p` >> rw [Run_def,dfn'LoadMEMByte_def,incPC_def] >>
        `opc ai = 5w` by fs [ag32_Decode_LoadMEMByte_opc_5w] >>
        `(s''.EX.EX_func = 9w) \/ (s''.EX.EX_func = 12w) \/ (s''.EX.EX_func = 13w) \/
        (s''.EX.EX_func = 14w) \/ (s''.EX.EX_func = 15w)`
          by fs [agp32_EX_opc_implies_EX_func] >>
        fs [EX_ALU_update_def,Rel_def]) >-
       (PairCases_on `p` >> rw [Run_def,dfn'LoadUpperConstant_def,incPC_def] >>
        `opc ai = 14w` by fs [ag32_Decode_LoadUpperConstant_opc_14w] >>
        `(s''.EX.EX_func = 9w) \/ (s''.EX.EX_func = 12w) \/ (s''.EX.EX_func = 13w) \/
        (s''.EX.EX_func = 14w) \/ (s''.EX.EX_func = 15w)`
          by fs [agp32_EX_opc_implies_EX_func] >>
        fs [EX_ALU_update_def,Rel_def]) >-
       (PairCases_on `p` >> rw [Run_def,dfn'Normal_def,norm_def,incPC_def] >>
        `opc ai = 0w` by fs [ag32_Decode_Normal_opc_0w] >>
        pairarg_tac >> fs [] >>
        Cases_on `p0 = fAdd` >-
         (fs [ALU_def] >> rw [] >>
          `func ai = 0w` by fs [ag32_Decode_Normal_fAdd_func_0w] >> fs [] >>
          rw [EX_ALU_update_def,ALU_correct_carry_lem,WORD_LS,word_add_def,w2n_w2w] >>
          fs [ALU_input1_def,ALU_input2_def] >>
          `(dataA ai = ri2word p2 ai) /\ (dataB ai = ri2word p3 ai)`
            by fs [ag32_Decode_Normal_dataA,ag32_Decode_Normal_dataB] >>
          rw [] >> METIS_TAC [w2n_add_MOD_itself]) >>
        Cases_on `p0 = fAddWithCarry` >-
         (fs [ALU_def] >> rw [] >>
          `func ai = 1w` by fs [ag32_Decode_Normal_fAddWithCarry_func_1w] >> fs [] >>
          rw [EX_ALU_update_def,ALU_correct_carry_lem,WORD_LS,word_add_def,w2n_w2w] >>
          fs [ALU_input1_def,ALU_input2_def] >>
          `(dataA ai = ri2word p2 ai) /\ (dataB ai = ri2word p3 ai)`
            by fs [ag32_Decode_Normal_dataA,ag32_Decode_Normal_dataB] >-
           (`s.EX.EX_carry_flag` by fs [Rel_def] >>
            rw [v2w_single_1w,ALU_correct_v2w_carry33_lem] >>
            METIS_TAC [w2n_add_MOD_itself_1]) >>
          `~s.EX.EX_carry_flag` by fs [Rel_def] >>
          rw [v2w_single_0w,ALU_correct_v2w_carry33_lem] >>
          METIS_TAC [w2n_add_MOD_itself]) >>
        fs [] >> rename1 `(v,ai')` >>
        `ai'.CarryFlag = ai.CarryFlag` by (fs [ALU_def] >> Cases_on `p0` >> fs [] >> rw []) >>
        `(func ai <> 0w) /\ (func ai <> 1w)` by fs [ag32_Decode_Normal_func_not_0w_1w] >>
        fs [EX_ALU_update_def,Rel_def] >>
        Cases_on_word_value `(agp32 fext fbits (SUC t)).EX.EX_func` >> fs []) >-
       (PairCases_on `p` >> rw [Run_def,dfn'Out_def,norm_def,incPC_def] >>
        `opc ai = 6w` by fs [ag32_Decode_Out_opc_6w] >>
        pairarg_tac >> fs [] >>
        Cases_on `p0 = fAdd` >-
         (fs [ALU_def] >> rw [] >>
          `func ai = 0w` by fs [ag32_Decode_Out_fAdd_func_0w] >> fs [] >>
          rw [EX_ALU_update_def,ALU_correct_carry_lem,WORD_LS,word_add_def,w2n_w2w] >>
          fs [ALU_input1_def,ALU_input2_def] >>
          `(dataA ai = ri2word p2 ai) /\ (dataB ai = ri2word p3 ai)`
            by fs [ag32_Decode_Out_dataA,ag32_Decode_Out_dataB] >>
          rw [] >> METIS_TAC [w2n_add_MOD_itself]) >>
        Cases_on `p0 = fAddWithCarry` >-
         (fs [ALU_def] >> rw [] >>
          `func ai = 1w` by fs [ag32_Decode_Out_fAddWithCarry_func_1w] >> fs [] >>
          rw [EX_ALU_update_def,ALU_correct_carry_lem,WORD_LS,word_add_def,w2n_w2w] >>
          fs [ALU_input1_def,ALU_input2_def] >>
          `(dataA ai = ri2word p2 ai) /\ (dataB ai = ri2word p3 ai)`
            by fs [ag32_Decode_Out_dataA,ag32_Decode_Out_dataB] >-
           (`s.EX.EX_carry_flag` by fs [Rel_def] >>
            rw [v2w_single_1w,ALU_correct_v2w_carry33_lem] >>
            METIS_TAC [w2n_add_MOD_itself_1]) >>
          `~s.EX.EX_carry_flag` by fs [Rel_def] >>
          rw [v2w_single_0w,ALU_correct_v2w_carry33_lem] >>
          METIS_TAC [w2n_add_MOD_itself]) >>
        fs [] >> rename1 `(v,ai')` >>
        `ai'.CarryFlag = ai.CarryFlag` by (fs [ALU_def] >> Cases_on `p0` >> fs [] >> rw []) >>
        `(func ai <> 0w) /\ (func ai <> 1w)` by fs [ag32_Decode_Out_func_not_0w_1w] >>
        fs [EX_ALU_update_def,Rel_def] >>
        Cases_on_word_value `(agp32 fext fbits (SUC t)).EX.EX_func` >> fs []) >-
       (rw [Run_def,dfn'ReservedInstr_def,incPC_def] >>
        `opc ai = 15w` by fs [ag32_Decode_ReservedInstr_opc_15w] >>
        `(s''.EX.EX_func = 9w) \/ (s''.EX.EX_func = 12w) \/ (s''.EX.EX_func = 13w) \/
        (s''.EX.EX_func = 14w) \/ (s''.EX.EX_func = 15w)`
          by fs [agp32_EX_opc_implies_EX_func] >>
        fs [EX_ALU_update_def,Rel_def]) >-
       (PairCases_on `p` >> rw [Run_def,dfn'Shift_def,incPC_def] >>
        `opc ai = 1w` by fs [ag32_Decode_Shift_opc_1w] >>
        `(s''.EX.EX_func = 9w) \/ (s''.EX.EX_func = 12w) \/ (s''.EX.EX_func = 13w) \/
        (s''.EX.EX_func = 14w) \/ (s''.EX.EX_func = 15w)`
          by fs [agp32_EX_opc_implies_EX_func] >>
        fs [EX_ALU_update_def,Rel_def]) >-
       (PairCases_on `p` >> rw [Run_def,dfn'StoreMEM_def,incPC_def] >>
        `opc ai = 2w` by fs [ag32_Decode_StoreMEM_opc_2w] >>
        `(s''.EX.EX_func = 9w) \/ (s''.EX.EX_func = 12w) \/ (s''.EX.EX_func = 13w) \/
        (s''.EX.EX_func = 14w) \/ (s''.EX.EX_func = 15w)`
          by fs [agp32_EX_opc_implies_EX_func] >>
        fs [EX_ALU_update_def,Rel_def]) >>
      PairCases_on `p` >> rw [Run_def,dfn'StoreMEMByte_def,incPC_def] >>
      `opc ai = 3w` by fs [ag32_Decode_StoreMEMByte_opc_3w] >>
      `(s''.EX.EX_func = 9w) \/ (s''.EX.EX_func = 12w) \/ (s''.EX.EX_func = 13w) \/
      (s''.EX.EX_func = 14w) \/ (s''.EX.EX_func = 15w)`
        by fs [agp32_EX_opc_implies_EX_func] >>
      fs [EX_ALU_update_def,Rel_def]) >>
    subgoal `I' (3,SUC t) = I' (2,t)` >-
     (fs [is_sch_def,is_sch_execute_def] >>
      Cases_on `isJump_hw_op (agp32 fext fbits t)` >>
      Cases_on `reg_data_hazard (agp32 fext fbits t)` >>
      METIS_TAC []) >> fs [] >>
    `THE (I' (2,t)) = SUC (THE (I' (2,t)) - 1)`
      by (Cases_on `THE (I' (2,t))` >- METIS_TAC [ID_instr_index_not_0] >> fs []) >>
    `(FUNPOW Next (THE (I' (2,t))) a).CarryFlag =
    (FUNPOW Next (SUC (THE (I' (2,t)) - 1)) a).CarryFlag` by METIS_TAC [] >>       
    fs [FUNPOW_SUC] >>
    Q.ABBREV_TAC `ai = FUNPOW Next (THE (I' (2,t)) - 1) a` >>
    rw [Next_def,GSYM word_at_addr_def,GSYM align_addr_def] >>
    Cases_on `Decode (word_at_addr ai.MEM (align_addr ai.PC))` >-
     (PairCases_on `p` >> rw [Run_def,dfn'Accelerator_def,incPC_def] >>
      `opc ai = 8w` by fs [ag32_Decode_Acc_opc_8w] >>
      `(s''.EX.EX_func = 9w) \/ (s''.EX.EX_func = 12w) \/ (s''.EX.EX_func = 13w) \/
      (s''.EX.EX_func = 14w) \/ (s''.EX.EX_func = 15w)`         
        by fs [agp32_EX_opc_implies_EX_func] >>
      fs [EX_ALU_update_def,Rel_def]) >-
     (rw [Run_def,dfn'In_def,incPC_def] >>
      `opc ai = 7w` by fs [ag32_Decode_In_opc_7w] >>
      `(s''.EX.EX_func = 9w) \/ (s''.EX.EX_func = 12w) \/ (s''.EX.EX_func = 13w) \/
      (s''.EX.EX_func = 14w) \/ (s''.EX.EX_func = 15w)`
        by fs [agp32_EX_opc_implies_EX_func] >>
      fs [EX_ALU_update_def,Rel_def]) >-
     (rw [Run_def,dfn'Interrupt_def,incPC_def] >>
      `opc ai = 12w` by fs [ag32_Decode_Interrupt_opc_12w] >>
      `(s''.EX.EX_func = 9w) \/ (s''.EX.EX_func = 12w) \/ (s''.EX.EX_func = 13w) \/
      (s''.EX.EX_func = 14w) \/ (s''.EX.EX_func = 15w)`
        by fs [agp32_EX_opc_implies_EX_func] >>
      fs [EX_ALU_update_def,Rel_def]) >-
     (PairCases_on `p` >> rw [Run_def,dfn'Jump_def] >>
      `opc ai = 9w` by fs [ag32_Decode_Jump_opc_9w] >>
      pairarg_tac >> fs [] >>
      Cases_on `p0 = fAdd` >-
       (fs [ALU_def] >> rw [] >>
        `func ai = 0w` by fs [ag32_Decode_Jump_fAdd_func_0w] >> fs [] >>
        rw [EX_ALU_update_def,ALU_correct_carry_lem,WORD_LS,word_add_def,w2n_w2w] >>
        fs [ALU_input1_def,ALU_input2_def] >>
        `dataA ai = ri2word p2 ai` by fs [ag32_Decode_Jump_dataA] >>
        rw [] >> METIS_TAC [w2n_add_MOD_itself]) >>
      Cases_on `p0 = fAddWithCarry` >-
       (fs [ALU_def] >> rw [] >>
        `func ai = 1w` by fs [ag32_Decode_Jump_fAddWithCarry_func_1w] >> fs [] >>
        rw [EX_ALU_update_def,ALU_correct_carry_lem,WORD_LS,word_add_def,w2n_w2w] >>
        fs [ALU_input1_def,ALU_input2_def] >>
        `dataA ai = ri2word p2 ai` by fs [ag32_Decode_Jump_dataA] >-
         (`s.EX.EX_carry_flag` by fs [Rel_def] >>
          rw [v2w_single_1w,ALU_correct_v2w_carry33_lem] >>
          METIS_TAC [w2n_add_MOD_itself_1]) >>
        `~s.EX.EX_carry_flag` by fs [Rel_def] >>
        rw [v2w_single_0w,ALU_correct_v2w_carry33_lem] >>
        METIS_TAC [w2n_add_MOD_itself]) >>
      fs [] >> rename1 `(v,ai')` >>
      `ai'.CarryFlag = ai.CarryFlag` by (fs [ALU_def] >> Cases_on `p0` >> fs [] >> rw []) >>
      `(func ai <> 0w) /\ (func ai <> 1w)` by fs [ag32_Decode_Jump_func_not_0w_1w] >>
      fs [EX_ALU_update_def,Rel_def] >>
      Cases_on_word_value `(agp32 fext fbits (SUC t)).EX.EX_func` >> fs []) >-
     (PairCases_on `p` >> rw [Run_def,dfn'JumpIfNotZero_def] >>
      `opc ai = 11w` by fs [ag32_Decode_JumpIfNotZero_opc_11w] >>
      pairarg_tac >> fs [] >>
      Cases_on `p0 = fAdd` >-
       (fs [ALU_def] >> rw [] >>
        `func ai = 0w` by fs [ag32_Decode_JumpIfNotZero_fAdd_func_0w] >> fs [] >>
        rw [EX_ALU_update_def,ALU_correct_carry_lem,WORD_LS,word_add_def,w2n_w2w] >>
        fs [ALU_input1_def,ALU_input2_def] >>
        `(dataA ai = ri2word p2 ai) /\ (dataB ai = ri2word p3 ai)`
          by fs [ag32_Decode_JumpIfNotZero_dataA,ag32_Decode_JumpIfNotZero_dataB] >>
        rw [incPC_def] >> METIS_TAC [w2n_add_MOD_itself]) >>
      Cases_on `p0 = fAddWithCarry` >-
       (fs [ALU_def] >> rw [] >>
        `func ai = 1w` by fs [ag32_Decode_JumpIfNotZero_fAddWithCarry_func_1w] >> fs [] >>
        rw [EX_ALU_update_def,ALU_correct_carry_lem,WORD_LS,word_add_def,w2n_w2w] >>
        fs [ALU_input1_def,ALU_input2_def] >>
        `(dataA ai = ri2word p2 ai) /\ (dataB ai = ri2word p3 ai)`
          by fs [ag32_Decode_JumpIfNotZero_dataA,ag32_Decode_JumpIfNotZero_dataB] >-
         (`s.EX.EX_carry_flag` by fs [Rel_def] >>
          rw [v2w_single_1w,ALU_correct_v2w_carry33_lem] >>
          METIS_TAC [w2n_add_MOD_itself_1]) >-
         (`~s.EX.EX_carry_flag` by fs [Rel_def] >>
          rw [v2w_single_0w,ALU_correct_v2w_carry33_lem] >>
          METIS_TAC [w2n_add_MOD_itself]) >-
         (`s.EX.EX_carry_flag` by fs [Rel_def] >>
          rw [v2w_single_1w,ALU_correct_v2w_carry33_lem,incPC_def] >>
          METIS_TAC [w2n_add_MOD_itself_1]) >>
        `~s.EX.EX_carry_flag` by fs [Rel_def] >>
        rw [v2w_single_0w,ALU_correct_v2w_carry33_lem,incPC_def] >>
        METIS_TAC [w2n_add_MOD_itself]) >>
      fs [] >> rename1 `(v,ai')` >>
      `ai'.CarryFlag = ai.CarryFlag` by (fs [ALU_def] >> Cases_on `p0` >> fs [] >> rw []) >>
      `(func ai <> 0w) /\ (func ai <> 1w)` by fs [ag32_Decode_JumpIfNotZero_func_not_0w_1w] >>
      Cases_on `v` >> rw [incPC_def] >>
      fs [EX_ALU_update_def,Rel_def,incPC_def] >>
      Cases_on_word_value `(agp32 fext fbits (SUC t)).EX.EX_func` >> fs []) >-
     (PairCases_on `p` >> rw [Run_def,dfn'JumpIfZero_def] >>
      `opc ai = 10w` by fs [ag32_Decode_JumpIfZero_opc_10w] >>
      pairarg_tac >> fs [] >>
      Cases_on `p0 = fAdd` >-
       (fs [ALU_def] >> rw [] >>
        `func ai = 0w` by fs [ag32_Decode_JumpIfZero_fAdd_func_0w] >> fs [] >>
        rw [EX_ALU_update_def,ALU_correct_carry_lem,WORD_LS,word_add_def,w2n_w2w] >>
        fs [ALU_input1_def,ALU_input2_def] >>
        `(dataA ai = ri2word p2 ai) /\ (dataB ai = ri2word p3 ai)`
          by fs [ag32_Decode_JumpIfZero_dataA,ag32_Decode_JumpIfZero_dataB] >>
        rw [incPC_def] >> METIS_TAC [w2n_add_MOD_itself]) >>
      Cases_on `p0 = fAddWithCarry` >-
       (fs [ALU_def] >> rw [] >>
        `func ai = 1w` by fs [ag32_Decode_JumpIfZero_fAddWithCarry_func_1w] >> fs [] >>
        rw [EX_ALU_update_def,ALU_correct_carry_lem,WORD_LS,word_add_def,w2n_w2w] >>
        fs [ALU_input1_def,ALU_input2_def] >>
        `(dataA ai = ri2word p2 ai) /\ (dataB ai = ri2word p3 ai)`
          by fs [ag32_Decode_JumpIfZero_dataA,ag32_Decode_JumpIfZero_dataB] >-
         (`s.EX.EX_carry_flag` by fs [Rel_def] >>
          rw [v2w_single_1w,ALU_correct_v2w_carry33_lem] >>
          METIS_TAC [w2n_add_MOD_itself_1]) >-
         (`~s.EX.EX_carry_flag` by fs [Rel_def] >>
          rw [v2w_single_0w,ALU_correct_v2w_carry33_lem] >>
          METIS_TAC [w2n_add_MOD_itself]) >-
         (`s.EX.EX_carry_flag` by fs [Rel_def] >>
          rw [v2w_single_1w,ALU_correct_v2w_carry33_lem,incPC_def] >>
          METIS_TAC [w2n_add_MOD_itself_1]) >>
        `~s.EX.EX_carry_flag` by fs [Rel_def] >>
        rw [v2w_single_0w,ALU_correct_v2w_carry33_lem,incPC_def] >>
        METIS_TAC [w2n_add_MOD_itself]) >>
      fs [] >> rename1 `(v,ai')` >>
      `ai'.CarryFlag = ai.CarryFlag` by (fs [ALU_def] >> Cases_on `p0` >> fs [] >> rw []) >>
      `(func ai <> 0w) /\ (func ai <> 1w)` by fs [ag32_Decode_JumpIfZero_func_not_0w_1w] >>
      Cases_on `v` >> rw [incPC_def] >>
      fs [EX_ALU_update_def,Rel_def,incPC_def] >>
      Cases_on_word_value `(agp32 fext fbits (SUC t)).EX.EX_func` >> fs []) >-
     (PairCases_on `p` >> rw [Run_def,dfn'LoadConstant_def,incPC_def] >>
      `opc ai = 13w` by fs [ag32_Decode_LoadConstant_opc_13w] >>
      `(s''.EX.EX_func = 9w) \/ (s''.EX.EX_func = 12w) \/ (s''.EX.EX_func = 13w) \/
      (s''.EX.EX_func = 14w) \/ (s''.EX.EX_func = 15w)`
        by fs [agp32_EX_opc_implies_EX_func] >>
      fs [EX_ALU_update_def,Rel_def]) >-
     (PairCases_on `p` >> rw [Run_def,dfn'LoadMEM_def,incPC_def] >>
      `opc ai = 4w` by fs [ag32_Decode_LoadMEM_opc_4w] >>
      `(s''.EX.EX_func = 9w) \/ (s''.EX.EX_func = 12w) \/ (s''.EX.EX_func = 13w) \/
      (s''.EX.EX_func = 14w) \/ (s''.EX.EX_func = 15w)`
        by fs [agp32_EX_opc_implies_EX_func] >>
      fs [EX_ALU_update_def,Rel_def]) >-
     (PairCases_on `p` >> rw [Run_def,dfn'LoadMEMByte_def,incPC_def] >>
      `opc ai = 5w` by fs [ag32_Decode_LoadMEMByte_opc_5w] >>
      `(s''.EX.EX_func = 9w) \/ (s''.EX.EX_func = 12w) \/ (s''.EX.EX_func = 13w) \/
      (s''.EX.EX_func = 14w) \/ (s''.EX.EX_func = 15w)`
        by fs [agp32_EX_opc_implies_EX_func] >>
      fs [EX_ALU_update_def,Rel_def]) >-
     (PairCases_on `p` >> rw [Run_def,dfn'LoadUpperConstant_def,incPC_def] >>
      `opc ai = 14w` by fs [ag32_Decode_LoadUpperConstant_opc_14w] >>
      `(s''.EX.EX_func = 9w) \/ (s''.EX.EX_func = 12w) \/ (s''.EX.EX_func = 13w) \/
      (s''.EX.EX_func = 14w) \/ (s''.EX.EX_func = 15w)`
        by fs [agp32_EX_opc_implies_EX_func] >>
      fs [EX_ALU_update_def,Rel_def]) >-
     (PairCases_on `p` >> rw [Run_def,dfn'Normal_def,norm_def,incPC_def] >>
      `opc ai = 0w` by fs [ag32_Decode_Normal_opc_0w] >>
      pairarg_tac >> fs [] >>
      Cases_on `p0 = fAdd` >-
       (fs [ALU_def] >> rw [] >>
        `func ai = 0w` by fs [ag32_Decode_Normal_fAdd_func_0w] >> fs [] >>
        rw [EX_ALU_update_def,ALU_correct_carry_lem,WORD_LS,word_add_def,w2n_w2w] >>
        fs [ALU_input1_def,ALU_input2_def] >>
        `(dataA ai = ri2word p2 ai) /\ (dataB ai = ri2word p3 ai)`
          by fs [ag32_Decode_Normal_dataA,ag32_Decode_Normal_dataB] >>
        rw [] >> METIS_TAC [w2n_add_MOD_itself]) >>
      Cases_on `p0 = fAddWithCarry` >-
       (fs [ALU_def] >> rw [] >>
        `func ai = 1w` by fs [ag32_Decode_Normal_fAddWithCarry_func_1w] >> fs [] >>
        rw [EX_ALU_update_def,ALU_correct_carry_lem,WORD_LS,word_add_def,w2n_w2w] >>
        fs [ALU_input1_def,ALU_input2_def] >>
        `(dataA ai = ri2word p2 ai) /\ (dataB ai = ri2word p3 ai)`
          by fs [ag32_Decode_Normal_dataA,ag32_Decode_Normal_dataB] >-
         (`s.EX.EX_carry_flag` by fs [Rel_def] >>
          rw [v2w_single_1w,ALU_correct_v2w_carry33_lem] >>
          METIS_TAC [w2n_add_MOD_itself_1]) >>
        `~s.EX.EX_carry_flag` by fs [Rel_def] >>
        rw [v2w_single_0w,ALU_correct_v2w_carry33_lem] >>
        METIS_TAC [w2n_add_MOD_itself]) >>
      fs [] >> rename1 `(v,ai')` >>
      `ai'.CarryFlag = ai.CarryFlag` by (fs [ALU_def] >> Cases_on `p0` >> fs [] >> rw []) >>
      `(func ai <> 0w) /\ (func ai <> 1w)` by fs [ag32_Decode_Normal_func_not_0w_1w] >>
      fs [EX_ALU_update_def,Rel_def] >>
      Cases_on_word_value `(agp32 fext fbits (SUC t)).EX.EX_func` >> fs []) >-
     (PairCases_on `p` >> rw [Run_def,dfn'Out_def,norm_def,incPC_def] >>
      `opc ai = 6w` by fs [ag32_Decode_Out_opc_6w] >>
      pairarg_tac >> fs [] >>
      Cases_on `p0 = fAdd` >-
       (fs [ALU_def] >> rw [] >>
        `func ai = 0w` by fs [ag32_Decode_Out_fAdd_func_0w] >> fs [] >>
        rw [EX_ALU_update_def,ALU_correct_carry_lem,WORD_LS,word_add_def,w2n_w2w] >>
        fs [ALU_input1_def,ALU_input2_def] >>
        `(dataA ai = ri2word p2 ai) /\ (dataB ai = ri2word p3 ai)`
          by fs [ag32_Decode_Out_dataA,ag32_Decode_Out_dataB] >>
        rw [] >> METIS_TAC [w2n_add_MOD_itself]) >>
      Cases_on `p0 = fAddWithCarry` >-
       (fs [ALU_def] >> rw [] >>
        `func ai = 1w` by fs [ag32_Decode_Out_fAddWithCarry_func_1w] >> fs [] >>
        rw [EX_ALU_update_def,ALU_correct_carry_lem,WORD_LS,word_add_def,w2n_w2w] >>
        fs [ALU_input1_def,ALU_input2_def] >>
        `(dataA ai = ri2word p2 ai) /\ (dataB ai = ri2word p3 ai)`
          by fs [ag32_Decode_Out_dataA,ag32_Decode_Out_dataB] >-
         (`s.EX.EX_carry_flag` by fs [Rel_def] >>
          rw [v2w_single_1w,ALU_correct_v2w_carry33_lem] >>
          METIS_TAC [w2n_add_MOD_itself_1]) >>
        `~s.EX.EX_carry_flag` by fs [Rel_def] >>
        rw [v2w_single_0w,ALU_correct_v2w_carry33_lem] >>
        METIS_TAC [w2n_add_MOD_itself]) >>
      fs [] >> rename1 `(v,ai')` >>
      `ai'.CarryFlag = ai.CarryFlag` by (fs [ALU_def] >> Cases_on `p0` >> fs [] >> rw []) >>
      `(func ai <> 0w) /\ (func ai <> 1w)` by fs [ag32_Decode_Out_func_not_0w_1w] >>
      fs [EX_ALU_update_def,Rel_def] >>
      Cases_on_word_value `(agp32 fext fbits (SUC t)).EX.EX_func` >> fs []) >-
     (rw [Run_def,dfn'ReservedInstr_def,incPC_def] >>
      `opc ai = 15w` by fs [ag32_Decode_ReservedInstr_opc_15w] >>
      `(s''.EX.EX_func = 9w) \/ (s''.EX.EX_func = 12w) \/ (s''.EX.EX_func = 13w) \/
      (s''.EX.EX_func = 14w) \/ (s''.EX.EX_func = 15w)`
        by fs [agp32_EX_opc_implies_EX_func] >>
      fs [EX_ALU_update_def,Rel_def]) >-
     (PairCases_on `p` >> rw [Run_def,dfn'Shift_def,incPC_def] >>
      `opc ai = 1w` by fs [ag32_Decode_Shift_opc_1w] >>
      `(s''.EX.EX_func = 9w) \/ (s''.EX.EX_func = 12w) \/ (s''.EX.EX_func = 13w) \/
      (s''.EX.EX_func = 14w) \/ (s''.EX.EX_func = 15w)`
        by fs [agp32_EX_opc_implies_EX_func] >>
      fs [EX_ALU_update_def,Rel_def]) >-
     (PairCases_on `p` >> rw [Run_def,dfn'StoreMEM_def,incPC_def] >>
      `opc ai = 2w` by fs [ag32_Decode_StoreMEM_opc_2w] >>
      `(s''.EX.EX_func = 9w) \/ (s''.EX.EX_func = 12w) \/ (s''.EX.EX_func = 13w) \/
      (s''.EX.EX_func = 14w) \/ (s''.EX.EX_func = 15w)`
        by fs [agp32_EX_opc_implies_EX_func] >>
      fs [EX_ALU_update_def,Rel_def]) >>
    PairCases_on `p` >> rw [Run_def,dfn'StoreMEMByte_def,incPC_def] >>
    `opc ai = 3w` by fs [ag32_Decode_StoreMEMByte_opc_3w] >>
    `(s''.EX.EX_func = 9w) \/ (s''.EX.EX_func = 12w) \/ (s''.EX.EX_func = 13w) \/
    (s''.EX.EX_func = 14w) \/ (s''.EX.EX_func = 15w)`
      by fs [agp32_EX_opc_implies_EX_func] >>
    fs [EX_ALU_update_def,Rel_def]) >>
  `I' (3,SUC t) = I' (3,t)` by fs [is_sch_def,is_sch_disable_def] >>
  `~s''.ID.ID_EX_write_enable` by fs [enable_stg_def,Abbr `s`] >>
  rw [EX_ALU_update_def] >>
  fs [Rel_def,EX_Rel_def]
QED


(** EX_carry_flag and EX_overflow_flag when EX is NONE and ID is not NONE **)
Theorem agp32_Rel_ag32_EX_ALU_flags_correct_ID_not_NONE:
  !fext fbits a t I.
    is_sch I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (3,SUC t) = NONE ==>
    I (2,SUC t) <> NONE ==>
    ((agp32 fext fbits (SUC t)).EX.EX_carry_flag = (FUNPOW Next (THE (I (2,SUC t)) - 1) a).CarryFlag) /\
    ((agp32 fext fbits (SUC t)).EX.EX_overflow_flag = (FUNPOW Next (THE (I (2,SUC t)) - 1) a).OverflowFlag)
Proof
  rpt gen_tac >> rpt disch_tac >>
  `((agp32 fext fbits (SUC t)).EX.EX_carry_flag = (agp32 fext fbits t).EX.EX_carry_flag) /\
  ((agp32 fext fbits (SUC t)).EX.EX_overflow_flag = (agp32 fext fbits t).EX.EX_overflow_flag)`
    by METIS_TAC [agp32_Rel_EX_NONE_flags_unchanged] >>
  fs [] >> Cases_on `enable_stg 2 (agp32 fext fbits t)` >-
   (Cases_on `isJump_isa_op (I' (2,t)) a \/ isJump_hw_op (agp32 fext fbits t)` >-
     (fs [is_sch_def,is_sch_decode_def] >> METIS_TAC []) >>
    `I' (2,SUC t) = I' (1,t)` by fs [is_sch_def,is_sch_decode_def] >> fs [] >>
    `enable_stg 3 (agp32 fext fbits t)`
      by fs [enable_stg_def,agp32_ID_ID_write_enable_and_ID_EX_write_enable] >>
    Cases_on `reg_data_hazard (agp32 fext fbits t)` >-
     (fs [isJump_hw_op_def,enable_stg_def] >>
      METIS_TAC [agp32_ID_ID_write_enable_EX_jump_sel_then_no_reg_data_hazard]) >>
    `I' (3,SUC t) = I' (2,t)` by METIS_TAC [is_sch_def,is_sch_execute_def] >> fs [] >>
    Cases_on `I' (3,t) <> NONE` >> fs [] >-
     METIS_TAC [IF_EX_instr_NOT_NONE_ID_NOT_NONE] >>
    fs [Rel_def]) >>
  `I' (2,SUC t) = I' (2,t)` by fs [is_sch_def,is_sch_disable_def] >> fs [] >>
  Cases_on `I' (3,t) = NONE` >-
   fs [Rel_def] >>
  `THE (I' (2,t)) = THE (I' (3,t)) + 1`
    by METIS_TAC [ID_instr_index_with_EX_instr_plus_1] >> fs [Rel_def]
QED


(** EX_carry_flag and EX_overflow_flag when EX and ID are NONE and IF is not NONE **)
Theorem agp32_Rel_ag32_EX_ALU_flags_correct_IF_not_NONE:
  !fext fbits a t I.
    is_sch I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (3,SUC t) = NONE ==>
    I (2,SUC t) = NONE ==>
    I (1,SUC t) <> NONE ==>
    ((agp32 fext fbits (SUC t)).EX.EX_carry_flag = (FUNPOW Next (THE (I (1,SUC t)) - 1) a).CarryFlag) /\
    ((agp32 fext fbits (SUC t)).EX.EX_overflow_flag = (FUNPOW Next (THE (I (1,SUC t)) - 1) a).OverflowFlag)
Proof
  rpt gen_tac >> rpt disch_tac >>
  `((agp32 fext fbits (SUC t)).EX.EX_carry_flag = (agp32 fext fbits t).EX.EX_carry_flag) /\
  ((agp32 fext fbits (SUC t)).EX.EX_overflow_flag = (agp32 fext fbits t).EX.EX_overflow_flag)`
    by METIS_TAC [agp32_Rel_EX_NONE_flags_unchanged] >>
  fs [] >> Cases_on `enable_stg 1 (agp32 fext fbits t)` >-
   (Cases_on `isJump_hw_op (agp32 fext fbits t)` >-
     (`I' (1,SUC t) = SOME (THE (I' (3,t)) + 1)` by fs [is_sch_def,is_sch_fetch_def] >> fs [] >>
      `isJump_isa_op (I' (3,t)) a` by fs [isJump_hw_op_def,Rel_def,EX_Rel_spec_def] >>
      `I' (3,t) <> NONE` by METIS_TAC [isJump_isa_op_not_none] >>
      fs [Rel_def]) >>
    Cases_on `isJump_isa_op (I' (1,t)) a \/ isJump_isa_op (I' (2,t)) a \/ I' (1,t) = NONE` >-
     (fs [is_sch_def,is_sch_fetch_def] >> METIS_TAC []) >> fs [] >>
    `enable_stg 2 (agp32 fext fbits t)`
      by fs [enable_stg_def,agp32_IF_PC_write_enable_and_ID_ID_write_enable] >>
    `I' (2,SUC t) = I' (1,t)` by METIS_TAC [is_sch_def,is_sch_decode_def] >> fs []) >>
  `~enable_stg 2 (agp32 fext fbits t)`
    by METIS_TAC [enable_stg_def,agp32_IF_PC_write_enable_and_ID_ID_write_enable] >>
  Cases_on `~enable_stg 3 (agp32 fext fbits t)` >> fs [] >-
   (fs [is_sch_def,is_sch_disable_def,Rel_def] >> METIS_TAC []) >>
  `(I' (1,SUC t) = I' (1,t)) /\ (I' (2,SUC t) = I' (2,t))`
    by METIS_TAC [is_sch_def,is_sch_disable_def] >> fs [] >>
  Cases_on `I' (3,t) = NONE` >-
   fs [Rel_def] >>
  METIS_TAC [IF_EX_instr_NOT_NONE_ID_NOT_NONE]
QED


(** EX_overflow_flag **)
Theorem agp32_Rel_ag32_EX_ALU_overflow_flag_correct:
  !fext fbits a t I.
    is_sch I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (3,SUC t) <> NONE ==>
    (agp32 fext fbits (SUC t)).EX.EX_overflow_flag = (FUNPOW Next (THE (I (3,SUC t))) a).OverflowFlag
Proof
  rw [] >> Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state;WB_pipeline;MEM_pipeline;EX_pipeline;
                            REG_write;ID_pipeline;IF_PC_update;Acc_compute] (fext t) s s` >>
  Q.ABBREV_TAC `s'' = procs [IF_instr_update;ID_opc_func_update;ID_imm_update;ID_data_update;
                             ID_data_check_update;EX_ALU_input_imm_update] (fext (SUC t)) s' s'` >>
  `(agp32 fext fbits (SUC t)).EX.EX_overflow_flag = (EX_ALU_update (fext (SUC t)) s' s'').EX.EX_overflow_flag`
    by fs [agp32_EX_ALU_items_updated_by_EX_ALU_update] >>
  `(s''.ID.ID_EX_write_enable = s.ID.ID_EX_write_enable) /\
  (s''.EX.EX_overflow_flag = s.EX.EX_overflow_flag) /\
  (s''.EX.EX_carry_flag = s.EX.EX_carry_flag) /\
  (s''.EX.EX_ALU_res = s.EX.EX_ALU_res)`
    by METIS_TAC [agp32_same_items_until_EX_ALU_update,Abbr `s`,Abbr `s'`,Abbr `s''`] >>
  `(s''.EX.EX_ALU_input1 = (agp32 fext fbits (SUC t)).EX.EX_ALU_input1) /\
  (s''.EX.EX_ALU_input2 = (agp32 fext fbits (SUC t)).EX.EX_ALU_input2) /\
  (s''.EX.EX_func = (agp32 fext fbits (SUC t)).EX.EX_func) /\
  (s''.EX.EX_opc = (agp32 fext fbits (SUC t)).EX.EX_opc)`
    by METIS_TAC [agp32_same_EX_ALU_input_until_ALU_update,agp32_same_EX_opc_func_until_ALU_update,
                  Abbr `s`,Abbr `s'`,Abbr `s''`] >>
  Cases_on `enable_stg 3 (agp32 fext fbits t)` >-
   (`s''.ID.ID_EX_write_enable` by fs [enable_stg_def,Abbr `s`] >>
    `s''.EX.EX_func = func (FUNPOW Next (THE (I' (3,SUC t)) − 1) a)`
      by fs [is_sch_def,agp32_Rel_ag32_EX_func_correct] >>
    `s''.EX.EX_opc = opc (FUNPOW Next (THE (I' (3,SUC t)) − 1) a)`
      by fs [is_sch_def,agp32_Rel_ag32_EX_opc_correct] >>
    `s''.EX.EX_ALU_input1 = ALU_input1 (FUNPOW Next (THE (I' (3,SUC t)) − 1) a)`
      by fs [is_sch_def,agp32_Rel_ag32_EX_ALU_input1_correct] >>
    `s''.EX.EX_ALU_input2 = ALU_input2 (FUNPOW Next (THE (I' (3,SUC t)) − 1) a)`
      by fs [is_sch_def,agp32_Rel_ag32_EX_ALU_input2_correct] >>
    Cases_on `I' (3,t) <> NONE` >-
     (`THE (I' (3,SUC t)) = SUC (THE (I' (3,t)))`
        by METIS_TAC [EX_instr_index_t_SUC_t_enable,ADD1] >> fs [FUNPOW_SUC] >>
      Q.ABBREV_TAC `ai = FUNPOW Next (THE (I' (3,t))) a` >>
      rw [Next_def,GSYM word_at_addr_def,GSYM align_addr_def] >>
      Cases_on `Decode (word_at_addr ai.MEM (align_addr ai.PC))` >-
       (PairCases_on `p` >> rw [Run_def,dfn'Accelerator_def,incPC_def] >>
        `opc ai = 8w` by fs [ag32_Decode_Acc_opc_8w] >>
        `(s''.EX.EX_func = 9w) \/ (s''.EX.EX_func = 12w) \/ (s''.EX.EX_func = 13w) \/
        (s''.EX.EX_func = 14w) \/ (s''.EX.EX_func = 15w)`
          by fs [agp32_EX_opc_implies_EX_func] >>
        fs [EX_ALU_update_def,Rel_def]) >-
       (rw [Run_def,dfn'In_def,incPC_def] >>
        `opc ai = 7w` by fs [ag32_Decode_In_opc_7w] >>
        `(s''.EX.EX_func = 9w) \/ (s''.EX.EX_func = 12w) \/ (s''.EX.EX_func = 13w) \/
        (s''.EX.EX_func = 14w) \/ (s''.EX.EX_func = 15w)`
          by fs [agp32_EX_opc_implies_EX_func] >>
        fs [EX_ALU_update_def,Rel_def]) >-
       (rw [Run_def,dfn'Interrupt_def,incPC_def] >>
        `opc ai = 12w` by fs [ag32_Decode_Interrupt_opc_12w] >>
        `(s''.EX.EX_func = 9w) \/ (s''.EX.EX_func = 12w) \/ (s''.EX.EX_func = 13w) \/
        (s''.EX.EX_func = 14w) \/ (s''.EX.EX_func = 15w)`
          by fs [agp32_EX_opc_implies_EX_func] >>
        fs [EX_ALU_update_def,Rel_def]) >-
       (PairCases_on `p` >> rw [Run_def,dfn'Jump_def] >>
        `opc ai = 9w` by fs [ag32_Decode_Jump_opc_9w] >>
        pairarg_tac >> fs [] >>
        Cases_on `p0 = fAdd` >-
         (fs [ALU_def] >> rw [] >>
          `func ai = 0w` by fs [ag32_Decode_Jump_fAdd_func_0w] >> fs [] >>
          rw [EX_ALU_update_def] >>
          fs [ALU_input1_def,ALU_input2_def] >>
          `dataA ai = ri2word p2 ai` by fs [ag32_Decode_Jump_dataA] >>
          `ri2word p2 ai = (agp32 fext fbits (SUC t)).EX.EX_ALU_input2` by fs [] >>
          rw [integer_wordTheory.overflow,word_msb] >> BBLAST_TAC) >>
        Cases_on `p0 = fAddWithCarry` >-
         (fs [ALU_def] >> rw [] >>
          `func ai = 1w` by fs [ag32_Decode_Jump_fAddWithCarry_func_1w] >> fs [] >>
          fs [EX_ALU_update_def,Rel_def]) >>
        Cases_on `p0 = fSub` >-
         (fs [ALU_def] >> rw [] >>
          `func ai = 2w` by fs [ag32_Decode_Jump_fSub_func_2w] >> fs [] >>
          rw [EX_ALU_update_def] >>
          fs [ALU_input1_def,ALU_input2_def] >>
          `dataA ai = ri2word p2 ai` by fs [ag32_Decode_Jump_dataA] >>
          `ri2word p2 ai = (agp32 fext fbits (SUC t)).EX.EX_ALU_input2` by fs [] >> fs [] >>
          Q.ABBREV_TAC `da = (agp32 fext fbits (SUC t)).EX.EX_ALU_input1` >>
          Q.ABBREV_TAC `db = (agp32 fext fbits (SUC t)).EX.EX_ALU_input2` >>
          `da + -1w * db = da - db` by WORD_DECIDE_TAC >>
          pop_assum (fn th => rewrite_tac [th]) >>
          rewrite_tac [integer_wordTheory.sub_overflow,word_msb] >> BBLAST_TAC) >>
        fs [] >> rename1 `(v,ai')` >>
        `ai'.OverflowFlag = ai.OverflowFlag` by (fs [ALU_def] >> Cases_on `p0` >> fs [] >> rw []) >>
        `(func ai <> 0w) /\ (func ai <> 1w) /\ (func ai <> 2w)`
          by fs [ag32_Decode_Jump_func_not_0w_1w_2w] >>
        fs [EX_ALU_update_def,Rel_def] >>
        Cases_on_word_value `(agp32 fext fbits (SUC t)).EX.EX_func` >> fs []) >-
       (PairCases_on `p` >> rw [Run_def,dfn'JumpIfNotZero_def] >>
        `opc ai = 11w` by fs [ag32_Decode_JumpIfNotZero_opc_11w] >>
        pairarg_tac >> fs [] >>
        Cases_on `p0 = fAdd` >-
         (fs [ALU_def] >> rw [] >>
          `func ai = 0w` by fs [ag32_Decode_JumpIfNotZero_fAdd_func_0w] >> fs [] >>
          rw [EX_ALU_update_def] >>
          fs [ALU_input1_def,ALU_input2_def] >>
          `(dataA ai = ri2word p2 ai) /\ (dataB ai = ri2word p3 ai)`
            by fs [ag32_Decode_JumpIfNotZero_dataA,ag32_Decode_JumpIfNotZero_dataB] >>
          `ri2word p2 ai = (agp32 fext fbits (SUC t)).EX.EX_ALU_input1 /\
          ri2word p3 ai = (agp32 fext fbits (SUC t)).EX.EX_ALU_input2` by fs [] >-
           (rw [integer_wordTheory.overflow,word_msb] >> BBLAST_TAC) >>
          rw [incPC_def] >>
          Q.ABBREV_TAC `da = (agp32 fext fbits (SUC t)).EX.EX_ALU_input1` >>
          Q.ABBREV_TAC `db = (agp32 fext fbits (SUC t)).EX.EX_ALU_input2` >>
          `0w = da + db` by fs [] >>
          pop_assum (fn th => rewrite_tac [th]) >>
          rewrite_tac [overflow_rewrite,word_msb] >> BBLAST_TAC) >>
        Cases_on `p0 = fAddWithCarry` >-
         (fs [ALU_def] >> rw [incPC_def] >>
          `func ai = 1w` by fs [ag32_Decode_JumpIfNotZero_fAddWithCarry_func_1w] >> fs [] >>
          fs [EX_ALU_update_def,Rel_def]) >>
        Cases_on `p0 = fSub` >-
         (fs [ALU_def] >> rw [] >>
          `func ai = 2w` by fs [ag32_Decode_JumpIfNotZero_fSub_func_2w] >> fs [] >>
          rw [EX_ALU_update_def,incPC_def] >>
          fs [ALU_input1_def,ALU_input2_def] >>
          `(dataA ai = ri2word p2 ai) /\ (dataB ai = ri2word p3 ai)`
            by fs [ag32_Decode_JumpIfNotZero_dataA,ag32_Decode_JumpIfNotZero_dataB] >>
          `ri2word p2 ai = (agp32 fext fbits (SUC t)).EX.EX_ALU_input1 /\
          ri2word p3 ai = (agp32 fext fbits (SUC t)).EX.EX_ALU_input2` by fs [] >> fs [] >>
          Q.ABBREV_TAC `da = (agp32 fext fbits (SUC t)).EX.EX_ALU_input1` >>
          Q.ABBREV_TAC `db = (agp32 fext fbits (SUC t)).EX.EX_ALU_input2` >-
           (`da + -1w * db = da - db` by WORD_DECIDE_TAC >>
            pop_assum (fn th => rewrite_tac [th]) >>
            rewrite_tac [integer_wordTheory.sub_overflow,word_msb] >> BBLAST_TAC) >>
          `0w = da - db` by fs [] >>
          pop_assum (fn th => rewrite_tac [th]) >>
          simp [sub_overflow_rewrite,word_msb]) >>
        fs [] >> rename1 `(v,ai')` >>
        `ai'.OverflowFlag = ai.OverflowFlag` by (fs [ALU_def] >> Cases_on `p0` >> fs [] >> rw []) >>
        `(func ai <> 0w) /\ (func ai <> 1w) /\ (func ai <> 2w)`
          by fs [ag32_Decode_JumpIfNotZero_func_not_0w_1w_2w] >>
        Cases_on `v` >> rw [incPC_def] >>
        fs [EX_ALU_update_def,Rel_def] >>
        Cases_on_word_value `(agp32 fext fbits (SUC t)).EX.EX_func` >> fs []) >-  
       (PairCases_on `p` >> rw [Run_def,dfn'JumpIfZero_def] >>
        `opc ai = 10w` by fs [ag32_Decode_JumpIfZero_opc_10w] >>
        pairarg_tac >> fs [] >>
        Cases_on `p0 = fAdd` >-
         (fs [ALU_def] >> rw [] >>
          `func ai = 0w` by fs [ag32_Decode_JumpIfZero_fAdd_func_0w] >> fs [] >>
          rw [EX_ALU_update_def] >>
          fs [ALU_input1_def,ALU_input2_def] >>
          `(dataA ai = ri2word p2 ai) /\ (dataB ai = ri2word p3 ai)`
            by fs [ag32_Decode_JumpIfZero_dataA,ag32_Decode_JumpIfZero_dataB] >>
          `ri2word p2 ai = (agp32 fext fbits (SUC t)).EX.EX_ALU_input1 /\
          ri2word p3 ai = (agp32 fext fbits (SUC t)).EX.EX_ALU_input2` by fs [] >-
           (fs [] >> Q.ABBREV_TAC `da = (agp32 fext fbits (SUC t)).EX.EX_ALU_input1` >>
            Q.ABBREV_TAC `db = (agp32 fext fbits (SUC t)).EX.EX_ALU_input2` >>              
            `0w = da + db` by fs [] >>     
            pop_assum (fn th => rewrite_tac [th]) >>
            rewrite_tac [overflow_rewrite,word_msb] >> BBLAST_TAC) >>
          rw [integer_wordTheory.overflow,word_msb,incPC_def] >> BBLAST_TAC) >>
        Cases_on `p0 = fAddWithCarry` >-
         (fs [ALU_def] >> rw [incPC_def] >>
          `func ai = 1w` by fs [ag32_Decode_JumpIfZero_fAddWithCarry_func_1w] >> fs [] >>
          fs [EX_ALU_update_def,Rel_def]) >>
        Cases_on `p0 = fSub` >-
         (fs [ALU_def] >> rw [] >>
          `func ai = 2w` by fs [ag32_Decode_JumpIfZero_fSub_func_2w] >> fs [] >>
          rw [EX_ALU_update_def,incPC_def] >>
          fs [ALU_input1_def,ALU_input2_def] >>
          `(dataA ai = ri2word p2 ai) /\ (dataB ai = ri2word p3 ai)`
            by fs [ag32_Decode_JumpIfZero_dataA,ag32_Decode_JumpIfZero_dataB] >>
          `ri2word p2 ai = (agp32 fext fbits (SUC t)).EX.EX_ALU_input1 /\
          ri2word p3 ai = (agp32 fext fbits (SUC t)).EX.EX_ALU_input2` by fs [] >> fs [] >>
          Q.ABBREV_TAC `da = (agp32 fext fbits (SUC t)).EX.EX_ALU_input1` >>
          Q.ABBREV_TAC `db = (agp32 fext fbits (SUC t)).EX.EX_ALU_input2` >-
           (`0w = da - db` by fs [] >>
            pop_assum (fn th => rewrite_tac [th]) >>
            simp [sub_overflow_rewrite,word_msb]) >>
          `da + -1w * db = da - db` by WORD_DECIDE_TAC >>
          pop_assum (fn th => rewrite_tac [th]) >>
          rewrite_tac [integer_wordTheory.sub_overflow,word_msb] >> BBLAST_TAC) >>
        fs [] >> rename1 `(v,ai')` >>
        `ai'.OverflowFlag = ai.OverflowFlag` by (fs [ALU_def] >> Cases_on `p0` >> fs [] >> rw []) >>
        `(func ai <> 0w) /\ (func ai <> 1w) /\ (func ai <> 2w)`
          by fs [ag32_Decode_JumpIfZero_func_not_0w_1w_2w] >>
        Cases_on `v` >> rw [incPC_def] >>
        fs [EX_ALU_update_def,Rel_def] >>
        Cases_on_word_value `(agp32 fext fbits (SUC t)).EX.EX_func` >> fs []) >-
       (PairCases_on `p` >> rw [Run_def,dfn'LoadConstant_def,incPC_def] >>
        `opc ai = 13w` by fs [ag32_Decode_LoadConstant_opc_13w] >>
        `(s''.EX.EX_func = 9w) \/ (s''.EX.EX_func = 12w) \/ (s''.EX.EX_func = 13w) \/
        (s''.EX.EX_func = 14w) \/ (s''.EX.EX_func = 15w)`
          by fs [agp32_EX_opc_implies_EX_func] >>
        fs [EX_ALU_update_def,Rel_def]) >-
       (PairCases_on `p` >> rw [Run_def,dfn'LoadMEM_def,incPC_def] >>
        `opc ai = 4w` by fs [ag32_Decode_LoadMEM_opc_4w] >>
        `(s''.EX.EX_func = 9w) \/ (s''.EX.EX_func = 12w) \/ (s''.EX.EX_func = 13w) \/
        (s''.EX.EX_func = 14w) \/ (s''.EX.EX_func = 15w)`
          by fs [agp32_EX_opc_implies_EX_func] >>
        fs [EX_ALU_update_def,Rel_def]) >-
       (PairCases_on `p` >> rw [Run_def,dfn'LoadMEMByte_def,incPC_def] >>
        `opc ai = 5w` by fs [ag32_Decode_LoadMEMByte_opc_5w] >>
        `(s''.EX.EX_func = 9w) \/ (s''.EX.EX_func = 12w) \/ (s''.EX.EX_func = 13w) \/
        (s''.EX.EX_func = 14w) \/ (s''.EX.EX_func = 15w)`
          by fs [agp32_EX_opc_implies_EX_func] >>
        fs [EX_ALU_update_def,Rel_def]) >-
       (PairCases_on `p` >> rw [Run_def,dfn'LoadUpperConstant_def,incPC_def] >>
        `opc ai = 14w` by fs [ag32_Decode_LoadUpperConstant_opc_14w] >>
        `(s''.EX.EX_func = 9w) \/ (s''.EX.EX_func = 12w) \/ (s''.EX.EX_func = 13w) \/
        (s''.EX.EX_func = 14w) \/ (s''.EX.EX_func = 15w)`
          by fs [agp32_EX_opc_implies_EX_func] >>
        fs [EX_ALU_update_def,Rel_def]) >-
       (PairCases_on `p` >> rw [Run_def,dfn'Normal_def,norm_def,incPC_def] >>
        `opc ai = 0w` by fs [ag32_Decode_Normal_opc_0w] >>
        pairarg_tac >> fs [] >>
        Cases_on `p0 = fAdd` >-
         (fs [ALU_def] >> rw [] >>
          `func ai = 0w` by fs [ag32_Decode_Normal_fAdd_func_0w] >> fs [] >>
          rw [EX_ALU_update_def] >>
          fs [ALU_input1_def,ALU_input2_def] >>
          `(dataA ai = ri2word p2 ai) /\ (dataB ai = ri2word p3 ai)`
            by fs [ag32_Decode_Normal_dataA,ag32_Decode_Normal_dataB] >>
          `ri2word p2 ai = (agp32 fext fbits (SUC t)).EX.EX_ALU_input1 /\
          ri2word p3 ai = (agp32 fext fbits (SUC t)).EX.EX_ALU_input2` by fs [] >> fs [] >>
          rw [integer_wordTheory.overflow,word_msb] >> BBLAST_TAC) >>
        Cases_on `p0 = fAddWithCarry` >-
         (fs [ALU_def] >> rw [] >>
          `func ai = 1w` by fs [ag32_Decode_Normal_fAddWithCarry_func_1w] >> fs [] >>
          fs [EX_ALU_update_def,Rel_def]) >>
        Cases_on `p0 = fSub` >-
         (fs [ALU_def] >> rw [] >>
          `func ai = 2w` by fs [ag32_Decode_Normal_fSub_func_2w] >> fs [] >>
          rw [EX_ALU_update_def] >>
          fs [ALU_input1_def,ALU_input2_def] >>
          `(dataA ai = ri2word p2 ai) /\ (dataB ai = ri2word p3 ai)`
            by fs [ag32_Decode_Normal_dataA,ag32_Decode_Normal_dataB] >>
          `ri2word p2 ai = (agp32 fext fbits (SUC t)).EX.EX_ALU_input1 /\
          ri2word p3 ai = (agp32 fext fbits (SUC t)).EX.EX_ALU_input2` by fs [] >> fs [] >>
          Q.ABBREV_TAC `da = (agp32 fext fbits (SUC t)).EX.EX_ALU_input1` >>
          Q.ABBREV_TAC `db = (agp32 fext fbits (SUC t)).EX.EX_ALU_input2` >>
          `da + -1w * db = da - db` by WORD_DECIDE_TAC >>
          pop_assum (fn th => rewrite_tac [th]) >>
          rewrite_tac [integer_wordTheory.sub_overflow,word_msb] >> BBLAST_TAC) >>
        fs [] >> rename1 `(v,ai')` >>
        `ai'.OverflowFlag = ai.OverflowFlag` by (fs [ALU_def] >> Cases_on `p0` >> fs [] >> rw []) >>
        `(func ai <> 0w) /\ (func ai <> 1w) /\ (func ai <> 2w)`
          by fs [ag32_Decode_Normal_func_not_0w_1w_2w] >>
        fs [EX_ALU_update_def,Rel_def] >>
        Cases_on_word_value `(agp32 fext fbits (SUC t)).EX.EX_func` >> fs []) >-
       (PairCases_on `p` >> rw [Run_def,dfn'Out_def,norm_def,incPC_def] >>
        `opc ai = 6w` by fs [ag32_Decode_Out_opc_6w] >>
        pairarg_tac >> fs [] >>
        Cases_on `p0 = fAdd` >-
         (fs [ALU_def] >> rw [] >>
          `func ai = 0w` by fs [ag32_Decode_Out_fAdd_func_0w] >> fs [] >>
          rw [EX_ALU_update_def] >>
          fs [ALU_input1_def,ALU_input2_def] >>
          `(dataA ai = ri2word p2 ai) /\ (dataB ai = ri2word p3 ai)`
            by fs [ag32_Decode_Out_dataA,ag32_Decode_Out_dataB] >>
          `ri2word p2 ai = (agp32 fext fbits (SUC t)).EX.EX_ALU_input1 /\
          ri2word p3 ai = (agp32 fext fbits (SUC t)).EX.EX_ALU_input2` by fs [] >> fs [] >>
          rw [integer_wordTheory.overflow,word_msb] >> BBLAST_TAC) >>
        Cases_on `p0 = fAddWithCarry` >-
         (fs [ALU_def] >> rw [] >>
          `func ai = 1w` by fs [ag32_Decode_Out_fAddWithCarry_func_1w] >> fs [] >>
          fs [EX_ALU_update_def,Rel_def]) >>
        Cases_on `p0 = fSub` >-
         (fs [ALU_def] >> rw [] >>
          `func ai = 2w` by fs [ag32_Decode_Out_fSub_func_2w] >> fs [] >>
          rw [EX_ALU_update_def] >>
          fs [ALU_input1_def,ALU_input2_def] >>
          `(dataA ai = ri2word p2 ai) /\ (dataB ai = ri2word p3 ai)`
            by fs [ag32_Decode_Out_dataA,ag32_Decode_Out_dataB] >>
          `ri2word p2 ai = (agp32 fext fbits (SUC t)).EX.EX_ALU_input1 /\
          ri2word p3 ai = (agp32 fext fbits (SUC t)).EX.EX_ALU_input2` by fs [] >> fs [] >>
          Q.ABBREV_TAC `da = (agp32 fext fbits (SUC t)).EX.EX_ALU_input1` >>
          Q.ABBREV_TAC `db = (agp32 fext fbits (SUC t)).EX.EX_ALU_input2` >>
          `da + -1w * db = da - db` by WORD_DECIDE_TAC >>
          pop_assum (fn th => rewrite_tac [th]) >>
          rewrite_tac [integer_wordTheory.sub_overflow,word_msb] >> BBLAST_TAC) >>
        fs [] >> rename1 `(v,ai')` >>
        `ai'.OverflowFlag = ai.OverflowFlag` by (fs [ALU_def] >> Cases_on `p0` >> fs [] >> rw []) >>
        `(func ai <> 0w) /\ (func ai <> 1w) /\ (func ai <> 2w)`
          by fs [ag32_Decode_Out_func_not_0w_1w_2w] >>
        fs [EX_ALU_update_def,Rel_def] >>
        Cases_on_word_value `(agp32 fext fbits (SUC t)).EX.EX_func` >> fs []) >-
       (rw [Run_def,dfn'ReservedInstr_def,incPC_def] >>
        `opc ai = 15w` by fs [ag32_Decode_ReservedInstr_opc_15w] >>
        `(s''.EX.EX_func = 9w) \/ (s''.EX.EX_func = 12w) \/ (s''.EX.EX_func = 13w) \/
        (s''.EX.EX_func = 14w) \/ (s''.EX.EX_func = 15w)`
          by fs [agp32_EX_opc_implies_EX_func] >>
        fs [EX_ALU_update_def,Rel_def]) >-
       (PairCases_on `p` >> rw [Run_def,dfn'Shift_def,incPC_def] >>
        `opc ai = 1w` by fs [ag32_Decode_Shift_opc_1w] >>
        `(s''.EX.EX_func = 9w) \/ (s''.EX.EX_func = 12w) \/ (s''.EX.EX_func = 13w) \/
        (s''.EX.EX_func = 14w) \/ (s''.EX.EX_func = 15w)`
          by fs [agp32_EX_opc_implies_EX_func] >>
        fs [EX_ALU_update_def,Rel_def]) >-
       (PairCases_on `p` >> rw [Run_def,dfn'StoreMEM_def,incPC_def] >>
        `opc ai = 2w` by fs [ag32_Decode_StoreMEM_opc_2w] >>
        `(s''.EX.EX_func = 9w) \/ (s''.EX.EX_func = 12w) \/ (s''.EX.EX_func = 13w) \/
        (s''.EX.EX_func = 14w) \/ (s''.EX.EX_func = 15w)`
          by fs [agp32_EX_opc_implies_EX_func] >>
        fs [EX_ALU_update_def,Rel_def]) >>
      PairCases_on `p` >> rw [Run_def,dfn'StoreMEMByte_def,incPC_def] >>
      `opc ai = 3w` by fs [ag32_Decode_StoreMEMByte_opc_3w] >>
      `(s''.EX.EX_func = 9w) \/ (s''.EX.EX_func = 12w) \/ (s''.EX.EX_func = 13w) \/
      (s''.EX.EX_func = 14w) \/ (s''.EX.EX_func = 15w)`
        by fs [agp32_EX_opc_implies_EX_func] >>
      fs [EX_ALU_update_def,Rel_def]) >>
    subgoal `I' (3,SUC t) = I' (2,t)` >-
     (fs [is_sch_def,is_sch_execute_def] >>
      Cases_on `isJump_hw_op (agp32 fext fbits t)` >>
      Cases_on `reg_data_hazard (agp32 fext fbits t)` >>
      METIS_TAC []) >> fs [] >>
    `THE (I' (2,t)) = SUC (THE (I' (2,t)) - 1)`
      by (Cases_on `THE (I' (2,t))` >- METIS_TAC [ID_instr_index_not_0] >> fs []) >>
    `(FUNPOW Next (THE (I' (2,t))) a).OverflowFlag =
    (FUNPOW Next (SUC (THE (I' (2,t)) - 1)) a).OverflowFlag` by METIS_TAC [] >>       
    fs [FUNPOW_SUC] >>
    Q.ABBREV_TAC `ai = FUNPOW Next (THE (I' (2,t)) - 1) a` >>
    rw [Next_def,GSYM word_at_addr_def,GSYM align_addr_def] >>
    Cases_on `Decode (word_at_addr ai.MEM (align_addr ai.PC))` >-
     (PairCases_on `p` >> rw [Run_def,dfn'Accelerator_def,incPC_def] >>
      `opc ai = 8w` by fs [ag32_Decode_Acc_opc_8w] >>
      `(s''.EX.EX_func = 9w) \/ (s''.EX.EX_func = 12w) \/ (s''.EX.EX_func = 13w) \/
      (s''.EX.EX_func = 14w) \/ (s''.EX.EX_func = 15w)`         
        by fs [agp32_EX_opc_implies_EX_func] >>
      fs [EX_ALU_update_def,Rel_def]) >-
     (rw [Run_def,dfn'In_def,incPC_def] >>
      `opc ai = 7w` by fs [ag32_Decode_In_opc_7w] >>
      `(s''.EX.EX_func = 9w) \/ (s''.EX.EX_func = 12w) \/ (s''.EX.EX_func = 13w) \/
      (s''.EX.EX_func = 14w) \/ (s''.EX.EX_func = 15w)`
        by fs [agp32_EX_opc_implies_EX_func] >>
      fs [EX_ALU_update_def,Rel_def]) >-
     (rw [Run_def,dfn'Interrupt_def,incPC_def] >>
      `opc ai = 12w` by fs [ag32_Decode_Interrupt_opc_12w] >>
      `(s''.EX.EX_func = 9w) \/ (s''.EX.EX_func = 12w) \/ (s''.EX.EX_func = 13w) \/
      (s''.EX.EX_func = 14w) \/ (s''.EX.EX_func = 15w)`
        by fs [agp32_EX_opc_implies_EX_func] >>
      fs [EX_ALU_update_def,Rel_def]) >-
     (PairCases_on `p` >> rw [Run_def,dfn'Jump_def] >>
      `opc ai = 9w` by fs [ag32_Decode_Jump_opc_9w] >>
      pairarg_tac >> fs [] >>
      Cases_on `p0 = fAdd` >-
       (fs [ALU_def] >> rw [] >>
        `func ai = 0w` by fs [ag32_Decode_Jump_fAdd_func_0w] >> fs [] >>
        rw [EX_ALU_update_def] >>
        fs [ALU_input1_def,ALU_input2_def] >>
        `dataA ai = ri2word p2 ai` by fs [ag32_Decode_Jump_dataA] >>
        `ri2word p2 ai = (agp32 fext fbits (SUC t)).EX.EX_ALU_input2` by fs [] >>
        rw [integer_wordTheory.overflow,word_msb] >> BBLAST_TAC) >>
      Cases_on `p0 = fAddWithCarry` >-
       (fs [ALU_def] >> rw [] >>
        `func ai = 1w` by fs [ag32_Decode_Jump_fAddWithCarry_func_1w] >> fs [] >>
        fs [EX_ALU_update_def,Rel_def]) >>
      Cases_on `p0 = fSub` >-
       (fs [ALU_def] >> rw [] >>
        `func ai = 2w` by fs [ag32_Decode_Jump_fSub_func_2w] >> fs [] >>
        rw [EX_ALU_update_def] >>
        fs [ALU_input1_def,ALU_input2_def] >>
        `dataA ai = ri2word p2 ai` by fs [ag32_Decode_Jump_dataA] >>
        `ri2word p2 ai = (agp32 fext fbits (SUC t)).EX.EX_ALU_input2` by fs [] >> fs [] >>
        Q.ABBREV_TAC `da = (agp32 fext fbits (SUC t)).EX.EX_ALU_input1` >>
        Q.ABBREV_TAC `db = (agp32 fext fbits (SUC t)).EX.EX_ALU_input2` >>
        `da + -1w * db = da - db` by WORD_DECIDE_TAC >>
        pop_assum (fn th => rewrite_tac [th]) >>
        rewrite_tac [integer_wordTheory.sub_overflow,word_msb] >> BBLAST_TAC) >>
      fs [] >> rename1 `(v,ai')` >>
      `ai'.OverflowFlag = ai.OverflowFlag` by (fs [ALU_def] >> Cases_on `p0` >> fs [] >> rw []) >>
      `(func ai <> 0w) /\ (func ai <> 1w) /\ (func ai <> 2w)`
        by fs [ag32_Decode_Jump_func_not_0w_1w_2w] >>
      fs [EX_ALU_update_def,Rel_def] >>
      Cases_on_word_value `(agp32 fext fbits (SUC t)).EX.EX_func` >> fs []) >-
     (PairCases_on `p` >> rw [Run_def,dfn'JumpIfNotZero_def] >>
      `opc ai = 11w` by fs [ag32_Decode_JumpIfNotZero_opc_11w] >>
      pairarg_tac >> fs [] >>
      Cases_on `p0 = fAdd` >-
       (fs [ALU_def] >> rw [] >>
        `func ai = 0w` by fs [ag32_Decode_JumpIfNotZero_fAdd_func_0w] >> fs [] >>
        rw [EX_ALU_update_def] >>
        fs [ALU_input1_def,ALU_input2_def] >>
        `(dataA ai = ri2word p2 ai) /\ (dataB ai = ri2word p3 ai)`
          by fs [ag32_Decode_JumpIfNotZero_dataA,ag32_Decode_JumpIfNotZero_dataB] >>
        `ri2word p2 ai = (agp32 fext fbits (SUC t)).EX.EX_ALU_input1 /\
        ri2word p3 ai = (agp32 fext fbits (SUC t)).EX.EX_ALU_input2` by fs [] >-
         (rw [integer_wordTheory.overflow,word_msb] >> BBLAST_TAC) >>
        rw [incPC_def] >>
        Q.ABBREV_TAC `da = (agp32 fext fbits (SUC t)).EX.EX_ALU_input1` >>
        Q.ABBREV_TAC `db = (agp32 fext fbits (SUC t)).EX.EX_ALU_input2` >>
        `0w = da + db` by fs [] >>
        pop_assum (fn th => rewrite_tac [th]) >>
        rewrite_tac [overflow_rewrite,word_msb] >> BBLAST_TAC) >>
      Cases_on `p0 = fAddWithCarry` >-
       (fs [ALU_def] >> rw [incPC_def] >>
        `func ai = 1w` by fs [ag32_Decode_JumpIfNotZero_fAddWithCarry_func_1w] >> fs [] >>
        fs [EX_ALU_update_def,Rel_def]) >>
      Cases_on `p0 = fSub` >-
       (fs [ALU_def] >> rw [] >>
        `func ai = 2w` by fs [ag32_Decode_JumpIfNotZero_fSub_func_2w] >> fs [] >>
        rw [EX_ALU_update_def,incPC_def] >>
        fs [ALU_input1_def,ALU_input2_def] >>
        `(dataA ai = ri2word p2 ai) /\ (dataB ai = ri2word p3 ai)`
          by fs [ag32_Decode_JumpIfNotZero_dataA,ag32_Decode_JumpIfNotZero_dataB] >>
        `ri2word p2 ai = (agp32 fext fbits (SUC t)).EX.EX_ALU_input1 /\
        ri2word p3 ai = (agp32 fext fbits (SUC t)).EX.EX_ALU_input2` by fs [] >> fs [] >>
        Q.ABBREV_TAC `da = (agp32 fext fbits (SUC t)).EX.EX_ALU_input1` >>
        Q.ABBREV_TAC `db = (agp32 fext fbits (SUC t)).EX.EX_ALU_input2` >-
         (`da + -1w * db = da - db` by WORD_DECIDE_TAC >>
          pop_assum (fn th => rewrite_tac [th]) >>
          rewrite_tac [integer_wordTheory.sub_overflow,word_msb] >> BBLAST_TAC) >>
        `0w = da - db` by fs [] >>
        pop_assum (fn th => rewrite_tac [th]) >>
        simp [sub_overflow_rewrite,word_msb]) >>
      fs [] >> rename1 `(v,ai')` >>
      `ai'.OverflowFlag = ai.OverflowFlag` by (fs [ALU_def] >> Cases_on `p0` >> fs [] >> rw []) >>
      `(func ai <> 0w) /\ (func ai <> 1w) /\ (func ai <> 2w)`
        by fs [ag32_Decode_JumpIfNotZero_func_not_0w_1w_2w] >>
      Cases_on `v` >> rw [incPC_def] >>
      fs [EX_ALU_update_def,Rel_def] >>
      Cases_on_word_value `(agp32 fext fbits (SUC t)).EX.EX_func` >> fs []) >-
     (PairCases_on `p` >> rw [Run_def,dfn'JumpIfZero_def] >>
      `opc ai = 10w` by fs [ag32_Decode_JumpIfZero_opc_10w] >>
      pairarg_tac >> fs [] >>
      Cases_on `p0 = fAdd` >-
       (fs [ALU_def] >> rw [] >>
        `func ai = 0w` by fs [ag32_Decode_JumpIfZero_fAdd_func_0w] >> fs [] >>
        rw [EX_ALU_update_def] >>
        fs [ALU_input1_def,ALU_input2_def] >>
        `(dataA ai = ri2word p2 ai) /\ (dataB ai = ri2word p3 ai)`
          by fs [ag32_Decode_JumpIfZero_dataA,ag32_Decode_JumpIfZero_dataB] >>
        `ri2word p2 ai = (agp32 fext fbits (SUC t)).EX.EX_ALU_input1 /\
        ri2word p3 ai = (agp32 fext fbits (SUC t)).EX.EX_ALU_input2` by fs [] >-
         (fs [] >> Q.ABBREV_TAC `da = (agp32 fext fbits (SUC t)).EX.EX_ALU_input1` >>
          Q.ABBREV_TAC `db = (agp32 fext fbits (SUC t)).EX.EX_ALU_input2` >>
          `0w = da + db` by fs [] >>                   
          pop_assum (fn th => rewrite_tac [th]) >>
          rewrite_tac [overflow_rewrite,word_msb] >> BBLAST_TAC) >>
        rw [integer_wordTheory.overflow,word_msb,incPC_def] >> BBLAST_TAC) >>
      Cases_on `p0 = fAddWithCarry` >-
       (fs [ALU_def] >> rw [incPC_def] >>
        `func ai = 1w` by fs [ag32_Decode_JumpIfZero_fAddWithCarry_func_1w] >> fs [] >>
        fs [EX_ALU_update_def,Rel_def]) >>
      Cases_on `p0 = fSub` >-
       (fs [ALU_def] >> rw [] >>
        `func ai = 2w` by fs [ag32_Decode_JumpIfZero_fSub_func_2w] >> fs [] >>
        rw [EX_ALU_update_def,incPC_def] >>
        fs [ALU_input1_def,ALU_input2_def] >>
        `(dataA ai = ri2word p2 ai) /\ (dataB ai = ri2word p3 ai)`
          by fs [ag32_Decode_JumpIfZero_dataA,ag32_Decode_JumpIfZero_dataB] >>
        `ri2word p2 ai = (agp32 fext fbits (SUC t)).EX.EX_ALU_input1 /\
        ri2word p3 ai = (agp32 fext fbits (SUC t)).EX.EX_ALU_input2` by fs [] >> fs [] >>
        Q.ABBREV_TAC `da = (agp32 fext fbits (SUC t)).EX.EX_ALU_input1` >>
        Q.ABBREV_TAC `db = (agp32 fext fbits (SUC t)).EX.EX_ALU_input2` >-
         (`0w = da - db` by fs [] >>
          pop_assum (fn th => rewrite_tac [th]) >>
          simp [sub_overflow_rewrite,word_msb]) >>
        `da + -1w * db = da - db` by WORD_DECIDE_TAC >>
        pop_assum (fn th => rewrite_tac [th]) >>
        rewrite_tac [integer_wordTheory.sub_overflow,word_msb] >> BBLAST_TAC) >>
      fs [] >> rename1 `(v,ai')` >>
      `ai'.OverflowFlag = ai.OverflowFlag` by (fs [ALU_def] >> Cases_on `p0` >> fs [] >> rw []) >>
      `(func ai <> 0w) /\ (func ai <> 1w) /\ (func ai <> 2w)`
        by fs [ag32_Decode_JumpIfZero_func_not_0w_1w_2w] >>
      Cases_on `v` >> rw [incPC_def] >>
      fs [EX_ALU_update_def,Rel_def] >>
      Cases_on_word_value `(agp32 fext fbits (SUC t)).EX.EX_func` >> fs []) >-
     (PairCases_on `p` >> rw [Run_def,dfn'LoadConstant_def,incPC_def] >>
      `opc ai = 13w` by fs [ag32_Decode_LoadConstant_opc_13w] >>
      `(s''.EX.EX_func = 9w) \/ (s''.EX.EX_func = 12w) \/ (s''.EX.EX_func = 13w) \/
      (s''.EX.EX_func = 14w) \/ (s''.EX.EX_func = 15w)`
        by fs [agp32_EX_opc_implies_EX_func] >>
      fs [EX_ALU_update_def,Rel_def]) >-
     (PairCases_on `p` >> rw [Run_def,dfn'LoadMEM_def,incPC_def] >>
      `opc ai = 4w` by fs [ag32_Decode_LoadMEM_opc_4w] >>
      `(s''.EX.EX_func = 9w) \/ (s''.EX.EX_func = 12w) \/ (s''.EX.EX_func = 13w) \/
      (s''.EX.EX_func = 14w) \/ (s''.EX.EX_func = 15w)`
        by fs [agp32_EX_opc_implies_EX_func] >>
      fs [EX_ALU_update_def,Rel_def]) >-
     (PairCases_on `p` >> rw [Run_def,dfn'LoadMEMByte_def,incPC_def] >>
      `opc ai = 5w` by fs [ag32_Decode_LoadMEMByte_opc_5w] >>
      `(s''.EX.EX_func = 9w) \/ (s''.EX.EX_func = 12w) \/ (s''.EX.EX_func = 13w) \/
      (s''.EX.EX_func = 14w) \/ (s''.EX.EX_func = 15w)`
        by fs [agp32_EX_opc_implies_EX_func] >>
      fs [EX_ALU_update_def,Rel_def]) >-
     (PairCases_on `p` >> rw [Run_def,dfn'LoadUpperConstant_def,incPC_def] >>
      `opc ai = 14w` by fs [ag32_Decode_LoadUpperConstant_opc_14w] >>
      `(s''.EX.EX_func = 9w) \/ (s''.EX.EX_func = 12w) \/ (s''.EX.EX_func = 13w) \/
      (s''.EX.EX_func = 14w) \/ (s''.EX.EX_func = 15w)`
        by fs [agp32_EX_opc_implies_EX_func] >>
      fs [EX_ALU_update_def,Rel_def]) >-
     (PairCases_on `p` >> rw [Run_def,dfn'Normal_def,norm_def,incPC_def] >>
      `opc ai = 0w` by fs [ag32_Decode_Normal_opc_0w] >>
      pairarg_tac >> fs [] >>
      Cases_on `p0 = fAdd` >-
       (fs [ALU_def] >> rw [] >>
        `func ai = 0w` by fs [ag32_Decode_Normal_fAdd_func_0w] >> fs [] >>
        rw [EX_ALU_update_def] >>
        fs [ALU_input1_def,ALU_input2_def] >>
        `(dataA ai = ri2word p2 ai) /\ (dataB ai = ri2word p3 ai)`
          by fs [ag32_Decode_Normal_dataA,ag32_Decode_Normal_dataB] >>
        `ri2word p2 ai = (agp32 fext fbits (SUC t)).EX.EX_ALU_input1 /\
        ri2word p3 ai = (agp32 fext fbits (SUC t)).EX.EX_ALU_input2` by fs [] >> fs [] >>
        rw [integer_wordTheory.overflow,word_msb] >> BBLAST_TAC) >>
      Cases_on `p0 = fAddWithCarry` >-
       (fs [ALU_def] >> rw [] >>
        `func ai = 1w` by fs [ag32_Decode_Normal_fAddWithCarry_func_1w] >> fs [] >>
        fs [EX_ALU_update_def,Rel_def]) >>
      Cases_on `p0 = fSub` >-
       (fs [ALU_def] >> rw [] >>
        `func ai = 2w` by fs [ag32_Decode_Normal_fSub_func_2w] >> fs [] >>
        rw [EX_ALU_update_def] >>
        fs [ALU_input1_def,ALU_input2_def] >>
        `(dataA ai = ri2word p2 ai) /\ (dataB ai = ri2word p3 ai)`
          by fs [ag32_Decode_Normal_dataA,ag32_Decode_Normal_dataB] >>
        `ri2word p2 ai = (agp32 fext fbits (SUC t)).EX.EX_ALU_input1 /\
        ri2word p3 ai = (agp32 fext fbits (SUC t)).EX.EX_ALU_input2` by fs [] >> fs [] >>
        Q.ABBREV_TAC `da = (agp32 fext fbits (SUC t)).EX.EX_ALU_input1` >>
        Q.ABBREV_TAC `db = (agp32 fext fbits (SUC t)).EX.EX_ALU_input2` >>
        `da + -1w * db = da - db` by WORD_DECIDE_TAC >>
        pop_assum (fn th => rewrite_tac [th]) >>
        rewrite_tac [integer_wordTheory.sub_overflow,word_msb] >> BBLAST_TAC) >>
      fs [] >> rename1 `(v,ai')` >>
      `ai'.OverflowFlag = ai.OverflowFlag` by (fs [ALU_def] >> Cases_on `p0` >> fs [] >> rw []) >>
      `(func ai <> 0w) /\ (func ai <> 1w) /\ (func ai <> 2w)`
        by fs [ag32_Decode_Normal_func_not_0w_1w_2w] >>
      fs [EX_ALU_update_def,Rel_def] >>
      Cases_on_word_value `(agp32 fext fbits (SUC t)).EX.EX_func` >> fs []) >-
     (PairCases_on `p` >> rw [Run_def,dfn'Out_def,norm_def,incPC_def] >>
      `opc ai = 6w` by fs [ag32_Decode_Out_opc_6w] >>
      pairarg_tac >> fs [] >>
      Cases_on `p0 = fAdd` >-
       (fs [ALU_def] >> rw [] >>
        `func ai = 0w` by fs [ag32_Decode_Out_fAdd_func_0w] >> fs [] >>
        rw [EX_ALU_update_def] >>
        fs [ALU_input1_def,ALU_input2_def] >>
        `(dataA ai = ri2word p2 ai) /\ (dataB ai = ri2word p3 ai)`
          by fs [ag32_Decode_Out_dataA,ag32_Decode_Out_dataB] >>
        `ri2word p2 ai = (agp32 fext fbits (SUC t)).EX.EX_ALU_input1 /\
        ri2word p3 ai = (agp32 fext fbits (SUC t)).EX.EX_ALU_input2` by fs [] >> fs [] >>
        rw [integer_wordTheory.overflow,word_msb] >> BBLAST_TAC) >>
      Cases_on `p0 = fAddWithCarry` >-
       (fs [ALU_def] >> rw [] >>
        `func ai = 1w` by fs [ag32_Decode_Out_fAddWithCarry_func_1w] >> fs [] >>
        fs [EX_ALU_update_def,Rel_def]) >>
      Cases_on `p0 = fSub` >-
       (fs [ALU_def] >> rw [] >>
        `func ai = 2w` by fs [ag32_Decode_Out_fSub_func_2w] >> fs [] >>
        rw [EX_ALU_update_def] >>
        fs [ALU_input1_def,ALU_input2_def] >>
        `(dataA ai = ri2word p2 ai) /\ (dataB ai = ri2word p3 ai)`
          by fs [ag32_Decode_Out_dataA,ag32_Decode_Out_dataB] >>
        `ri2word p2 ai = (agp32 fext fbits (SUC t)).EX.EX_ALU_input1 /\
        ri2word p3 ai = (agp32 fext fbits (SUC t)).EX.EX_ALU_input2` by fs [] >> fs [] >>
        Q.ABBREV_TAC `da = (agp32 fext fbits (SUC t)).EX.EX_ALU_input1` >>
        Q.ABBREV_TAC `db = (agp32 fext fbits (SUC t)).EX.EX_ALU_input2` >>
        `da + -1w * db = da - db` by WORD_DECIDE_TAC >>
        pop_assum (fn th => rewrite_tac [th]) >>
        rewrite_tac [integer_wordTheory.sub_overflow,word_msb] >> BBLAST_TAC) >>
      fs [] >> rename1 `(v,ai')` >>
      `ai'.OverflowFlag = ai.OverflowFlag` by (fs [ALU_def] >> Cases_on `p0` >> fs [] >> rw []) >>
      `(func ai <> 0w) /\ (func ai <> 1w) /\ (func ai <> 2w)`
        by fs [ag32_Decode_Out_func_not_0w_1w_2w] >>
      fs [EX_ALU_update_def,Rel_def] >>
      Cases_on_word_value `(agp32 fext fbits (SUC t)).EX.EX_func` >> fs []) >-
     (rw [Run_def,dfn'ReservedInstr_def,incPC_def] >>
      `opc ai = 15w` by fs [ag32_Decode_ReservedInstr_opc_15w] >>
      `(s''.EX.EX_func = 9w) \/ (s''.EX.EX_func = 12w) \/ (s''.EX.EX_func = 13w) \/
      (s''.EX.EX_func = 14w) \/ (s''.EX.EX_func = 15w)`
        by fs [agp32_EX_opc_implies_EX_func] >>
      fs [EX_ALU_update_def,Rel_def]) >-
     (PairCases_on `p` >> rw [Run_def,dfn'Shift_def,incPC_def] >>
      `opc ai = 1w` by fs [ag32_Decode_Shift_opc_1w] >>
      `(s''.EX.EX_func = 9w) \/ (s''.EX.EX_func = 12w) \/ (s''.EX.EX_func = 13w) \/
      (s''.EX.EX_func = 14w) \/ (s''.EX.EX_func = 15w)`
        by fs [agp32_EX_opc_implies_EX_func] >>
      fs [EX_ALU_update_def,Rel_def]) >-
     (PairCases_on `p` >> rw [Run_def,dfn'StoreMEM_def,incPC_def] >>
      `opc ai = 2w` by fs [ag32_Decode_StoreMEM_opc_2w] >>
      `(s''.EX.EX_func = 9w) \/ (s''.EX.EX_func = 12w) \/ (s''.EX.EX_func = 13w) \/
      (s''.EX.EX_func = 14w) \/ (s''.EX.EX_func = 15w)`
        by fs [agp32_EX_opc_implies_EX_func] >>
      fs [EX_ALU_update_def,Rel_def]) >>
    PairCases_on `p` >> rw [Run_def,dfn'StoreMEMByte_def,incPC_def] >>
    `opc ai = 3w` by fs [ag32_Decode_StoreMEMByte_opc_3w] >>
    `(s''.EX.EX_func = 9w) \/ (s''.EX.EX_func = 12w) \/ (s''.EX.EX_func = 13w) \/
    (s''.EX.EX_func = 14w) \/ (s''.EX.EX_func = 15w)`
      by fs [agp32_EX_opc_implies_EX_func] >>
    fs [EX_ALU_update_def,Rel_def]) >>
  `I' (3,SUC t) = I' (3,t)` by fs [is_sch_def,is_sch_disable_def] >>
  `~s''.ID.ID_EX_write_enable` by fs [enable_stg_def,Abbr `s`] >>
  rw [EX_ALU_update_def] >>
  fs [Rel_def,EX_Rel_def]
QED

val _ = export_theory ();
