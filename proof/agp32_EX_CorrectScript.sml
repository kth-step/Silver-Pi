open hardwarePreamble translatorTheory translatorLib arithmeticTheory wordsExtraTheory dep_rewrite blastLib bitstringSyntax fcpSyntax listSyntax wordsSyntax agp32StateTheory agp32EnvironmentTheory agp32ProcessorTheory ag32Theory ag32ExtraTheory ag32UtilitiesTheory agp32RelationTheory agp32UpdateTheory agp32InternalTheory;

(* correctness of EX stage items with respect to the ISA *)
val _ = new_theory "agp32_EX_Correct";

val _ = prefer_num ();
val _ = guess_lengths ();


(* MARK: keep it here for EX proof later
(* tactic *)
val update_carry_flag_when_enabled_tac =
    (Q.ABBREV_TAC `s = agp32 fext fbits t` >>
     Q.ABBREV_TAC `s' = procs [agp32_next_state;WB_pipeline;MEM_pipeline;EX_pipeline;
                               REG_write;ID_pipeline;IF_PC_update;Acc_compute]
                              (fext t) s s` >>
     Q.ABBREV_TAC `s'' = procs [ForwardA;ForwardB;ForwardW;IF_instr_update;
                                ID_opc_func_update;ID_imm_update;
                                ID_data_update;EX_ctrl_update;EX_forward_data;
                                EX_ALU_input_update;EX_compute_enable_update]
                               (fext (SUC t)) s' s'` >>                        
     `(agp32 fext fbits (SUC t)).EX.EX_carry_flag =
     (EX_ALU_update (fext (SUC t)) s' s'').EX.EX_carry_flag`
       by fs [agp32_EX_ALU_items_updated_by_EX_ALU_update,Abbr `s`,Abbr `s'`,Abbr `s''`] >> rw []);

val carry_flag_unchanged_tac =
    (Q.ABBREV_TAC `s3 = procs [agp32_next_state;WB_pipeline;MEM_pipeline] (fext t) s s` >>
     `?s4.(agp32 fext fbits (SUC t)).EX.EX_opc = (EX_pipeline (fext (SUC t)) s4 s3).EX.EX_opc`
       by fs [agp32_EX_opc_func_updated_by_EX_pipeline,Abbr `s3`,Abbr `s`] >>
     `(s3.ID.ID_EX_write_enable <=> s.ID.ID_EX_write_enable) /\ (s3.ID.ID_opc = s.ID.ID_opc)`
       by METIS_TAC [Abbr `s3`,Abbr `s`,agp32_same_items_until_MEM_pipeline] >>
     `s3.ID.ID_EX_write_enable` by fs [enable_stg_def] >>
      Cases_on `enable_stg 2 s` >-
      ((** ID is enabled at cycle t **)
       `s.ID.ID_opc = opc ai` by (fs [Rel_def] >> `2 = 3 - 1 /\ 3 <> 1` by rw [] >>
                              `I' (3,SUC t) = I' (2,t)` by METIS_TAC [Abbr `s`] >>
                              fs [ID_Rel_def]) >>
       `((agp32 fext fbits (SUC t)).EX.EX_opc = 16w) \/
       ((agp32 fext fbits (SUC t)).EX.EX_opc = s.ID.ID_opc)`
         by (fs [EX_pipeline_def] >> Cases_on `s3.EX.EX_NOP_flag` >> fs []) >>
       `(s''.EX.EX_opc = (agp32 fext fbits (SUC t)).EX.EX_opc) /\
       (s''.EX.EX_func = (agp32 fext fbits (SUC t)).EX.EX_func)`
         by METIS_TAC [agp32_same_EX_opc_func_until_ALU_update,Abbr `s`,Abbr `s'`,Abbr `s''`] >>
       `(s''.EX.EX_func = 9w) \/ (s''.EX.EX_func = 12w) \/ (s''.EX.EX_func = 13w) \/
       (s''.EX.EX_func = 14w) \/ (s''.EX.EX_func = 15w)`
         by fs [Abbr `s`,agp32_EX_opc_implies_EX_func] >>
       `s''.EX.EX_carry_flag <=> s.EX.EX_carry_flag`
         by METIS_TAC [agp32_same_EX_carry_flag_as_before,Abbr `s`,Abbr `s'`,Abbr `s''`] >>
       rw [EX_ALU_update_def] >> fs [Rel_def,Abbr `s`]) >>
     (** ID is disabled at cycle t **)
     `s.EX.EX_NOP_flag` by fs [Abbr `s`,agp32_ID_enable_flags_imply_flush_NOP_flags,enable_stg_def] >>
     `s3.EX.EX_NOP_flag <=> s.EX.EX_NOP_flag` by METIS_TAC [Abbr `s3`,Abbr `s`,agp32_same_items_until_MEM_pipeline] >>
     fs [EX_pipeline_def] >>
     `(s''.EX.EX_opc = (agp32 fext fbits (SUC t)).EX.EX_opc) /\
     (s''.EX.EX_func = (agp32 fext fbits (SUC t)).EX.EX_func)`
       by METIS_TAC [agp32_same_EX_opc_func_until_ALU_update,Abbr `s`,Abbr `s'`,Abbr `s''`] >>
     `(s''.EX.EX_func = 9w) \/ (s''.EX.EX_func = 12w) \/ (s''.EX.EX_func = 13w) \/
     (s''.EX.EX_func = 14w) \/ (s''.EX.EX_func = 15w)`
       by fs [Abbr `s`,agp32_EX_opc_implies_EX_func] >>
     `s''.EX.EX_carry_flag <=> s.EX.EX_carry_flag`
       by METIS_TAC [agp32_same_EX_carry_flag_as_before,Abbr `s`,Abbr `s'`,Abbr `s''`] >>    
     rw [EX_ALU_update_def] >> fs [Rel_def,Abbr `s`]);

val carry_flag_unchanged_by_func_tac =
    (Q.ABBREV_TAC `s3 = procs [agp32_next_state;WB_pipeline;MEM_pipeline] (fext t) s s` >>
     `?s4.(agp32 fext fbits (SUC t)).EX.EX_func = (EX_pipeline (fext (SUC t)) s4 s3).EX.EX_func`
       by fs [agp32_EX_opc_func_updated_by_EX_pipeline,Abbr `s3`,Abbr `s`] >>
     `(s3.ID.ID_EX_write_enable <=> s.ID.ID_EX_write_enable) /\ (s3.ID.ID_func = s.ID.ID_func)`
       by METIS_TAC [Abbr `s3`,Abbr `s`,agp32_same_items_until_MEM_pipeline] >>
     `s3.ID.ID_EX_write_enable` by fs [enable_stg_def] >>
      Cases_on `enable_stg 2 s` >-
      ((** ID is enabled at cycle t **)
       `s.ID.ID_func = func ai` by (fs [Rel_def] >> `2 = 3 - 1 /\ 3 <> 1` by rw [] >>
                                    `I' (3,SUC t) = I' (2,t)` by METIS_TAC [Abbr `s`] >>
                                    fs [ID_Rel_def]) >>
       `((agp32 fext fbits (SUC t)).EX.EX_func = 12w) \/
       ((agp32 fext fbits (SUC t)).EX.EX_func = s.ID.ID_func)`
         by (fs [EX_pipeline_def] >> Cases_on `s3.EX.EX_NOP_flag` >> fs []) >>
       `s''.EX.EX_func = (agp32 fext fbits (SUC t)).EX.EX_func`
         by METIS_TAC [agp32_same_EX_opc_func_until_ALU_update,Abbr `s`,Abbr `s'`,Abbr `s''`] >>
       `(s''.EX.EX_func <> 0w) /\ (s''.EX.EX_func <> 1w)` by fs [] >>
       `s''.EX.EX_carry_flag <=> s.EX.EX_carry_flag`
         by METIS_TAC [agp32_same_EX_carry_flag_as_before,Abbr `s`,Abbr `s'`,Abbr `s''`] >>
       rw [EX_ALU_update_def] >> fs [Rel_def,Abbr `s`] >>
       Cases_on_word_value `func ai` >> fs []) >>
     (** ID is disabled at cycle t **)
     `s.EX.EX_NOP_flag` by fs [Abbr `s`,agp32_ID_enable_flags_imply_flush_NOP_flags,enable_stg_def] >>
     `s3.EX.EX_NOP_flag <=> s.EX.EX_NOP_flag` by METIS_TAC [Abbr `s3`,Abbr `s`,agp32_same_items_until_MEM_pipeline] >>
     fs [EX_pipeline_def] >>
     `s''.EX.EX_func = (agp32 fext fbits (SUC t)).EX.EX_func`
       by METIS_TAC [agp32_same_EX_opc_func_until_ALU_update,Abbr `s`,Abbr `s'`,Abbr `s''`] >>
     `s''.EX.EX_carry_flag <=> s.EX.EX_carry_flag`
       by METIS_TAC [agp32_same_EX_carry_flag_as_before,Abbr `s`,Abbr `s'`,Abbr `s''`] >>    
     rw [EX_ALU_update_def] >> fs [Rel_def,Abbr `s`]);

(* lemmas *)
(** lemmas copied from the hardware/ag32 repo **)

(** copy end **)
                                              


(* carry_flag between ISA and circuit states *)
Theorem agp32_Rel_ag32_carry_flag_correct:
  !fext fbits a t I.
    (!t k. enable_stg k (agp32 fext fbits t) ==> k <> 1 ==>
           (I (k,SUC t) = I (k,t) + 1) /\ (I (k,SUC t) = I (k - 1,t))) ==>
    (!t k. ~enable_stg k (agp32 fext fbits t) ==> I (k,SUC t) = I (k,t)) ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    ((agp32 fext fbits (SUC t)).EX.EX_carry_flag <=>
     (FUNPOW Next (I (3,SUC t)) a).CarryFlag)
Proof
  rw [] >> Cases_on `enable_stg 3 (agp32 fext fbits t)` >-
   (** EX stage is enabled **)
   (`I'(3,SUC t) = SUC (I'(3,t))` by fs [] >>
    rw [FUNPOW_SUC] >>
    Q.ABBREV_TAC `ai = FUNPOW Next (I' (3,t)) a` >>             
    rw [Next_def,GSYM word_at_addr_def,GSYM align_addr_def] >>
    Cases_on `Decode (word_at_addr ai.MEM (align_addr ai.PC))` >-

     ((** Accelerator **)
     PairCases_on `p` >> rw [Run_def,dfn'Accelerator_def,incPC_def] >>
     update_carry_flag_when_enabled_tac >>
     `opc ai = 8w` by fs [ag32_Decode_Acc_opc_8w] >>
     carry_flag_unchanged_tac) >-   

     ((** In **)
     rw [Run_def,dfn'In_def,incPC_def] >>
     update_carry_flag_when_enabled_tac >>
     `opc ai = 7w` by fs [ag32_Decode_In_opc_7w] >>
     carry_flag_unchanged_tac) >-

     ((** Interrupt **)
     rw [Run_def,dfn'Interrupt_def,incPC_def] >>
     update_carry_flag_when_enabled_tac >>
     `opc ai = 12w` by fs [ag32_Decode_Interrupt_opc_12w] >>
     carry_flag_unchanged_tac) >-

     ((** Jump: CarryFlag can be changed **)
     PairCases_on `p` >> rw [Run_def,dfn'Jump_def] >>
     pairarg_tac >> fs [] >>
     Cases_on `p0 = fAdd` >-
      ((** fAdd **)
      fs [ALU_def] >> rw [] >>
      update_carry_flag_when_enabled_tac >>
      `func ai = 0w` by fs [ag32_Decode_Jump_fAdd_func_0w] >>
      `s''.EX.EX_func = 0w` by cheat >>
      `s''.EX.EX_compute_enable` by cheat >>
      rw [EX_ALU_update_def,ALU_correct_carry_lem,WORD_LS,word_add_def,w2n_w2w] >>
      `(s''.EX.EX_ALU_input1 = ai.PC) /\ (s''.EX.EX_ALU_input2 = ri2word p2 ai)` by cheat >>
      rw [] >> METIS_TAC [w2n_add_MOD_itself]) >>
     Cases_on `p0 = fAddWithCarry` >-
      ((** fAddWithCarry **)
      fs [ALU_def] >> rw [] >>
      cheat) >>
     `s.CarryFlag = ai.CarryFlag` by (fs [ALU_def] >> Cases_on `p0` >> fs [] >> rw []) >>
     fs [] >> rename1 `(v,ai')` >>
     update_carry_flag_when_enabled_tac >>
     `(func ai <> 0w) /\ (func ai <> 1w)` by fs [ag32_Decode_Jump_func_not_0w_1w] >>
     carry_flag_unchanged_by_func_tac) >-

     ((** JumpIfNotZero: CarryFlag can be changed **)
     PairCases_on `p` >> rw [Run_def,dfn'JumpIfNotZero_def] >>
     pairarg_tac >> fs [] >>
     Cases_on `p0 = fAdd` >-
      ((** fAdd **)
      fs [ALU_def,incPC_def] >> rw [] >>
      cheat) >>
     Cases_on `p0 = fAddWithCarry` >-
      ((** fAddWithCarry **)
      fs [ALU_def,incPC_def] >> rw [] >>
      cheat) >>
     `s.CarryFlag = ai.CarryFlag` by (fs [ALU_def] >> Cases_on `p0` >> fs [] >> rw []) >>
     fs [] >> rename1 `(v,ai')` >>
     update_carry_flag_when_enabled_tac >> rw [incPC_def] >>
     `(func ai <> 0w) /\ (func ai <> 1w)` by fs [ag32_Decode_JumpIfNotZero_func_not_0w_1w] >>
     carry_flag_unchanged_by_func_tac) >-

     ((** JumpIfZreo: CarryFlag can be changed **)
     PairCases_on `p` >> rw [Run_def,dfn'JumpIfZero_def] >>
     pairarg_tac >> fs [] >>
     Cases_on `p0 = fAdd` >-
      ((** fAdd **)
      fs [ALU_def,incPC_def] >> rw [] >>
      cheat) >>
     Cases_on `p0 = fAddWithCarry` >-
      ((** fAddWithCarry **)
      fs [ALU_def,incPC_def] >> rw [] >>
      cheat) >>
     `s.CarryFlag = ai.CarryFlag` by (fs [ALU_def] >> Cases_on `p0` >> fs [] >> rw []) >>
     fs [] >> rename1 `(v,ai')` >>
     update_carry_flag_when_enabled_tac >> rw [incPC_def] >>
     `(func ai <> 0w) /\ (func ai <> 1w)` by fs [ag32_Decode_JumpIfZero_func_not_0w_1w] >>
     carry_flag_unchanged_by_func_tac) >-

     ((** LoadConstant **)
     PairCases_on `p` >> rw [Run_def,dfn'LoadConstant_def,incPC_def] >>
     update_carry_flag_when_enabled_tac >>
     `opc ai = 13w` by fs [ag32_Decode_LoadConstant_opc_13w] >>
     carry_flag_unchanged_tac) >-

     ((** LoadMEM **)
     PairCases_on `p` >> rw [Run_def,dfn'LoadMEM_def,incPC_def] >>
     update_carry_flag_when_enabled_tac >>
     `opc ai = 4w` by fs [ag32_Decode_LoadMEM_opc_4w] >>
     carry_flag_unchanged_tac) >-

     ((** LoadMEMByte **)
     PairCases_on `p` >> rw [Run_def,dfn'LoadMEMByte_def,incPC_def] >>
     update_carry_flag_when_enabled_tac >>
     `opc ai = 5w` by fs [ag32_Decode_LoadMEMByte_opc_5w] >>
     carry_flag_unchanged_tac) >-

     ((** LoadUpperConstant **)
     PairCases_on `p` >> rw [Run_def,dfn'LoadUpperConstant_def,incPC_def] >>
     update_carry_flag_when_enabled_tac >>
     `opc ai = 14w` by fs [ag32_Decode_LoadUpperConstant_opc_14w] >>
     carry_flag_unchanged_tac) >-

     ((** Normal: CarryFlag can be changed **)
     PairCases_on `p` >> rw [Run_def,dfn'Normal_def,norm_def,incPC_def] >>
     pairarg_tac >> fs [] >>
     Cases_on `p0 = fAdd` >-
      ((** fAdd **)
      fs [ALU_def] >> rw [] >>
      cheat) >>
     Cases_on `p0 = fAddWithCarry` >-         
      ((** fAddWithCarry **)
      fs [ALU_def] >> rw [] >>
      cheat) >>
     `s.CarryFlag = ai.CarryFlag` by (fs [ALU_def] >> Cases_on `p0` >> fs [] >> rw []) >>
     fs [] >> rename1 `(v,ai')` >>
     update_carry_flag_when_enabled_tac >>
     `(func ai <> 0w) /\ (func ai <> 1w)` by fs [ag32_Decode_Normal_func_not_0w_1w] >>
     carry_flag_unchanged_by_func_tac) >-

     ((** Out: CarryFlag can be changed **)
     PairCases_on `p` >> rw [Run_def,dfn'Out_def,norm_def,incPC_def] >>
     pairarg_tac >> fs [] >>
     Cases_on `p0 = fAdd` >-
      ((** fAdd **)
      fs [ALU_def] >> rw [] >>
      cheat) >>
     Cases_on `p0 = fAddWithCarry` >-         
      ((** fAddWithCarry **)
      fs [ALU_def] >> rw [] >>
      cheat) >>
     `s.CarryFlag = ai.CarryFlag` by (fs [ALU_def] >> Cases_on `p0` >> fs [] >> rw []) >>
     fs [] >> rename1 `(v,ai')` >>
     update_carry_flag_when_enabled_tac >>
     `(func ai <> 0w) /\ (func ai <> 1w)` by fs [ag32_Decode_Out_func_not_0w_1w] >>
     carry_flag_unchanged_by_func_tac) >-

     ((** ReservedInstr **)
     rw [Run_def] >>
     update_carry_flag_when_enabled_tac >>
     `opc ai = 15w` by fs [ag32_Decode_ReservedInstr_opc_15w] >>
     carry_flag_unchanged_tac) >-

     ((** Shift **)
     PairCases_on `p` >> rw [Run_def,dfn'Shift_def,incPC_def] >>
     update_carry_flag_when_enabled_tac >>
     `opc ai = 1w` by fs [ag32_Decode_Shift_opc_1w] >>
     carry_flag_unchanged_tac) >-

     ((** StoreMEM **)
     PairCases_on `p` >> rw [Run_def,dfn'StoreMEM_def,incPC_def] >>
     update_carry_flag_when_enabled_tac >>
     `opc ai = 2w` by fs [ag32_Decode_StoreMEM_opc_2w] >>
     carry_flag_unchanged_tac) >>

    (** StoreMEMByte **)
    PairCases_on `p` >> rw [Run_def,dfn'StoreMEMByte_def,incPC_def] >>
    update_carry_flag_when_enabled_tac >>
    `opc ai = 3w` by fs [ag32_Decode_StoreMEMByte_opc_3w] >>
    carry_flag_unchanged_tac) >>

  (** EX stage is disabled **)
  `I' (3,SUC t) = I' (3,t)` by fs [] >>
  fs [Rel_def] >>
  update_carry_flag_when_enabled_tac >>
  reverse (Cases_on `s''.EX.EX_compute_enable`) >-
   (`s''.EX.EX_carry_flag <=> s.EX.EX_carry_flag`
      by METIS_TAC [agp32_same_EX_carry_flag_as_before,Abbr `s`,Abbr `s'`,Abbr `s''`] >>
    fs [EX_ALU_update_def]) >>
  cheat
QED
 *)


(** lemmas about words for ALU **)
Theorem ALU_correct_carry_lem:
  !(w:33 word). word_bit 32 w <=> n2w (dimword(:32)) <=+ w
Proof
  simp [] >> BBLAST_PROVE_TAC
QED

Theorem ALU_correct_v2w_carry33_lem:
  !b. v2w [b] = if b then (1w:33 word) else 0w
Proof
  Cases >> EVAL_TAC
QED

Theorem ALU_correct_v2w_carry32_lem:
  !b. v2w [b] = if b then (1w:32 word) else 0w
Proof
  Cases >> EVAL_TAC
QED


(** EX_PC_sel **)
Theorem agp32_Rel_ag32_EX_PC_sel_correct:
  !fext fbits a t I.
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    ((agp32 fext fbits (SUC t)).EX.EX_opc = 9w ==> (agp32 fext fbits (SUC t)).EX.EX_PC_sel = 1w) /\
    ((agp32 fext fbits (SUC t)).EX.EX_opc = 10w ==> (agp32 fext fbits (SUC t)).EX.EX_PC_sel = 2w) /\
    ((agp32 fext fbits (SUC t)).EX.EX_opc = 11w ==> (agp32 fext fbits (SUC t)).EX.EX_PC_sel = 3w)
Proof
  rpt gen_tac >> disch_tac >>
  Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state; WB_pipeline; MEM_pipeline; EX_pipeline;
                            REG_write; ID_pipeline; IF_PC_update; Acc_compute] (fext t) s s` >>
  Q.ABBREV_TAC `s'' = procs [IF_instr_update; ID_opc_func_update; ID_imm_update;
                             ID_data_update; ID_data_check_update] (fext (SUC t)) s' s'` >>
  `(agp32 fext fbits (SUC t)).EX.EX_PC_sel = (EX_ctrl_update (fext (SUC t)) s' s'').EX.EX_PC_sel`
    by fs [agp32_EX_PC_sel_updated_by_EX_ctrl_update] >>
  `(s'.EX.EX_opc = (agp32 fext fbits (SUC t)).EX.EX_opc)`
    by fs [agp32_same_EX_pipeline_items_after_EX_pipeline] >>
  `(s''.ID.ID_EX_write_enable = s.ID.ID_EX_write_enable) /\ (s''.EX.EX_PC_sel = s.EX.EX_PC_sel)`
    by METIS_TAC [agp32_same_items_before_EX_ctrl_update,Abbr `s`,Abbr `s'`,Abbr `s''`] >>
  Cases_on `enable_stg 3 (agp32 fext fbits t)` >>
  fs [EX_ctrl_update_def,enable_stg_def,Abbr `s`] >>
  `(agp32 fext fbits (SUC t)).EX.EX_opc = (agp32 fext fbits t).EX.EX_opc`
    by fs [agp32_EX_opc_unchanged_when_EX_disabled,enable_stg_def] >> rw [] >>
  fs [Rel_def,EX_inv_def]
QED

(** EX_inv **)
Theorem agp32_Rel_ag32_EX_inv_correct:
  !fext fbits a t I.
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    EX_inv (agp32 fext fbits (SUC t))
Proof
  rw [EX_inv_def] >>
  METIS_TAC [agp32_Rel_ag32_EX_PC_sel_correct]
QED


(** EX_PC **)
Theorem agp32_Rel_ag32_EX_PC_correct:
  !fext fbits a t I.
    is_sch_execute I (agp32 fext fbits) a ==>
    is_sch_disable I (agp32 fext fbits) ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (3,SUC t) <> NONE ==>
    (agp32 fext fbits (SUC t)).EX.EX_PC = (FUNPOW Next (THE (I (3,SUC t)) − 1) a).PC
Proof
  rw [] >> Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state;WB_pipeline;MEM_pipeline] (fext t) s s` >>
  `(agp32 fext fbits (SUC t)).EX.EX_PC = (EX_pipeline (fext t) s s').EX.EX_PC`
    by fs [agp32_EX_PC_imm_addrW_updated_by_EX_pipeline] >> rw [] >>
  `(s'.ID.ID_EX_write_enable = s.ID.ID_EX_write_enable) /\ (s'.EX.EX_PC = s.EX.EX_PC)`
    by METIS_TAC [agp32_same_EX_items_before_EX_pipeline,Abbr `s`,Abbr `s'`] >>
  Cases_on `enable_stg 3 (agp32 fext fbits t)` >-
   (fs [is_sch_execute_def] >>
    Cases_on `isJump_hw_op (agp32 fext fbits t)` >-
     METIS_TAC [] >>
    Cases_on `reg_data_hazard (agp32 fext fbits t)` >-
     METIS_TAC [] >>
    `I' (3,SUC t) = I' (2,t)` by fs [] >> fs [] >>
    `s'.ID.ID_EX_write_enable` by fs [enable_stg_def,Abbr `s`] >>
    rw [EX_pipeline_def] >> fs [Rel_def,ID_Rel_def]) >>
  `I' (3,SUC t) = I' (3,t)` by fs [is_sch_disable_def] >>
  `~s'.ID.ID_EX_write_enable` by fs [enable_stg_def,Abbr `s`] >>
  rw [EX_pipeline_def] >>
  fs [Rel_def,EX_Rel_def]
QED

(** EX_addrW **)
Theorem agp32_Rel_ag32_EX_addrW_correct:
  !fext fbits a t I.
    is_sch_execute I (agp32 fext fbits) a ==>
    is_sch_disable I (agp32 fext fbits) ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (3,SUC t) <> NONE ==>
    (agp32 fext fbits (SUC t)).EX.EX_addrW = addrW (FUNPOW Next (THE (I (3,SUC t)) − 1) a)
Proof
  rw [] >> Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state;WB_pipeline;MEM_pipeline] (fext t) s s` >>
  `(agp32 fext fbits (SUC t)).EX.EX_addrW = (EX_pipeline (fext t) s s').EX.EX_addrW`
    by fs [agp32_EX_PC_imm_addrW_updated_by_EX_pipeline] >> rw [] >>
  `(s'.ID.ID_EX_write_enable = s.ID.ID_EX_write_enable) /\ (s'.EX.EX_addrW = s.EX.EX_addrW)`
    by METIS_TAC [agp32_same_EX_items_before_EX_pipeline,Abbr `s`,Abbr `s'`] >>
  `s'.ID.ID_addrW = s.ID.ID_addrW`
    by METIS_TAC [agp32_same_ID_items_before_EX_pipeline,Abbr `s`,Abbr `s'`] >>
  Cases_on `enable_stg 3 (agp32 fext fbits t)` >-
   (fs [is_sch_execute_def] >>
    Cases_on `isJump_hw_op (agp32 fext fbits t)` >-
     METIS_TAC [] >>
    Cases_on `reg_data_hazard (agp32 fext fbits t)` >-
     METIS_TAC [] >>
    `I' (3,SUC t) = I' (2,t)` by fs [] >> fs [] >>
    `s'.ID.ID_EX_write_enable` by fs [enable_stg_def,Abbr `s`] >>
    rw [EX_pipeline_def] >> fs [Rel_def,ID_Rel_def]) >>
  `I' (3,SUC t) = I' (3,t)` by fs [is_sch_disable_def] >>
  `~s'.ID.ID_EX_write_enable` by fs [enable_stg_def,Abbr `s`] >>
  rw [EX_pipeline_def] >>
  fs [Rel_def,EX_Rel_def]
QED

(** EX_imm **)
Theorem agp32_Rel_ag32_EX_imm_correct:
  !fext fbits a t I.
    is_sch_execute I (agp32 fext fbits) a ==>
    is_sch_disable I (agp32 fext fbits) ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (3,SUC t) <> NONE ==>
    (agp32 fext fbits (SUC t)).EX.EX_imm = imm (FUNPOW Next (THE (I (3,SUC t)) − 1) a)
Proof
  rw [] >> Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state;WB_pipeline;MEM_pipeline] (fext t) s s` >>
  `(agp32 fext fbits (SUC t)).EX.EX_imm = (EX_pipeline (fext t) s s').EX.EX_imm`
    by fs [agp32_EX_PC_imm_addrW_updated_by_EX_pipeline] >> rw [] >>
  `(s'.ID.ID_EX_write_enable = s.ID.ID_EX_write_enable) /\ (s'.EX.EX_imm = s.EX.EX_imm)`
    by METIS_TAC [agp32_same_EX_items_before_EX_pipeline,Abbr `s`,Abbr `s'`] >>
  `s'.ID.ID_imm = s.ID.ID_imm`
    by METIS_TAC [agp32_same_ID_items_before_EX_pipeline,Abbr `s`,Abbr `s'`] >>
  Cases_on `enable_stg 3 (agp32 fext fbits t)` >-
   (fs [is_sch_execute_def] >>
    Cases_on `isJump_hw_op (agp32 fext fbits t)` >-
     METIS_TAC [] >>
    Cases_on `reg_data_hazard (agp32 fext fbits t)` >-
     METIS_TAC [] >>
    `I' (3,SUC t) = I' (2,t)` by fs [] >> fs [] >>
    `s'.ID.ID_EX_write_enable` by fs [enable_stg_def,Abbr `s`] >>
    rw [EX_pipeline_def] >> fs [Rel_def,ID_Rel_def]) >>
  `I' (3,SUC t) = I' (3,t)` by fs [is_sch_disable_def] >>
  `~s'.ID.ID_EX_write_enable` by fs [enable_stg_def,Abbr `s`] >>
  rw [EX_pipeline_def] >>
  fs [Rel_def,EX_Rel_def]
QED

(** EX_opc **)
Theorem agp32_Rel_ag32_EX_opc_correct:
  !fext fbits a t I.
    is_sch_execute I (agp32 fext fbits) a ==>
    is_sch_disable I (agp32 fext fbits) ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (3,SUC t) <> NONE ==>
    (agp32 fext fbits (SUC t)).EX.EX_opc = opc (FUNPOW Next (THE (I (3,SUC t)) − 1) a)
Proof
  rw [] >> Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state;WB_pipeline;MEM_pipeline] (fext t) s s` >>
  `(agp32 fext fbits (SUC t)).EX.EX_opc = (EX_pipeline (fext t) s s').EX.EX_opc`
    by fs [agp32_EX_opc_func_updated_by_EX_pipeline] >> rw [] >>
  `(s'.ID.ID_EX_write_enable = s.ID.ID_EX_write_enable) /\ (s'.EX.EX_opc = s.EX.EX_opc) /\
  (s'.EX.EX_NOP_flag = s.EX.EX_NOP_flag)`
    by METIS_TAC [agp32_same_EX_items_before_EX_pipeline,Abbr `s`,Abbr `s'`] >>
  `s'.ID.ID_opc = s.ID.ID_opc`
    by METIS_TAC [agp32_same_ID_items_before_EX_pipeline,Abbr `s`,Abbr `s'`] >>
  Cases_on `enable_stg 3 (agp32 fext fbits t)` >-
   (fs [is_sch_execute_def] >>
    Cases_on `isJump_hw_op (agp32 fext fbits t)` >-
     METIS_TAC [] >>
    Cases_on `reg_data_hazard (agp32 fext fbits t)` >-
     METIS_TAC [] >>
    `I' (3,SUC t) = I' (2,t)` by fs [] >> fs [] >>
    `s'.ID.ID_EX_write_enable` by fs [enable_stg_def,Abbr `s`] >>
    `~s.EX.EX_NOP_flag`
      by fs [enable_stg_def,Abbr `s`,
             agp32_ID_EX_write_enable_no_jump_or_reg_data_hazard_EX_NOP_flag_F] >>
    rw [EX_pipeline_def] >> fs [Rel_def,ID_Rel_def]) >>
  `I' (3,SUC t) = I' (3,t)` by fs [is_sch_disable_def] >>
  `~s'.ID.ID_EX_write_enable` by fs [enable_stg_def,Abbr `s`] >>
  rw [EX_pipeline_def] >>
  fs [Rel_def,EX_Rel_def]
QED

(** EX_func **)
Theorem agp32_Rel_ag32_EX_func_correct:
  !fext fbits a t I.
    is_sch_execute I (agp32 fext fbits) a ==>
    is_sch_disable I (agp32 fext fbits) ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (3,SUC t) <> NONE ==>
    (agp32 fext fbits (SUC t)).EX.EX_func = func (FUNPOW Next (THE (I (3,SUC t)) − 1) a)
Proof
  rw [] >> Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state;WB_pipeline;MEM_pipeline] (fext t) s s` >>
  `(agp32 fext fbits (SUC t)).EX.EX_func = (EX_pipeline (fext t) s s').EX.EX_func`
    by fs [agp32_EX_opc_func_updated_by_EX_pipeline] >> rw [] >>
  `(s'.ID.ID_EX_write_enable = s.ID.ID_EX_write_enable) /\ (s'.EX.EX_func = s.EX.EX_func) /\
  (s'.EX.EX_NOP_flag = s.EX.EX_NOP_flag)`
    by METIS_TAC [agp32_same_EX_items_before_EX_pipeline,Abbr `s`,Abbr `s'`] >>
  `s'.ID.ID_func = s.ID.ID_func`
    by METIS_TAC [agp32_same_ID_items_before_EX_pipeline,Abbr `s`,Abbr `s'`] >>
  Cases_on `enable_stg 3 (agp32 fext fbits t)` >-
   (fs [is_sch_execute_def] >>
    Cases_on `isJump_hw_op (agp32 fext fbits t)` >-
     METIS_TAC [] >>
    Cases_on `reg_data_hazard (agp32 fext fbits t)` >-
     METIS_TAC [] >>
    `I' (3,SUC t) = I' (2,t)` by fs [] >> fs [] >>
    `s'.ID.ID_EX_write_enable` by fs [enable_stg_def,Abbr `s`] >>
    `~s.EX.EX_NOP_flag`
      by fs [enable_stg_def,Abbr `s`,
             agp32_ID_EX_write_enable_no_jump_or_reg_data_hazard_EX_NOP_flag_F] >>
    rw [EX_pipeline_def] >> fs [Rel_def,ID_Rel_def]) >>
  `I' (3,SUC t) = I' (3,t)` by fs [is_sch_disable_def] >>
  `~s'.ID.ID_EX_write_enable` by fs [enable_stg_def,Abbr `s`] >>
  rw [EX_pipeline_def] >>
  fs [Rel_def,EX_Rel_def]
QED

(** EX_write_reg **)
Theorem agp32_Rel_ag32_EX_write_reg_correct:
  !fext fbits a t I.
    is_sch_execute I (agp32 fext fbits) a ==>
    is_sch_disable I (agp32 fext fbits) ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (3,SUC t) <> NONE ==>
    (agp32 fext fbits (SUC t)).EX.EX_write_reg = reg_iswrite (FUNPOW Next (THE (I (3,SUC t)) − 1) a)
Proof
  rw [] >> Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state;WB_pipeline;MEM_pipeline] (fext t) s s` >>
  `(agp32 fext fbits (SUC t)).EX.EX_write_reg = (EX_pipeline (fext t) s s').EX.EX_write_reg`
    by fs [agp32_EX_write_reg_updated_by_EX_pipeline] >> rw [] >>
  `(s'.ID.ID_EX_write_enable = s.ID.ID_EX_write_enable) /\ (s'.EX.EX_write_reg = s.EX.EX_write_reg) /\
  (s'.EX.EX_NOP_flag = s.EX.EX_NOP_flag)`
    by METIS_TAC [agp32_same_EX_items_before_EX_pipeline,Abbr `s`,Abbr `s'`] >>
  `s'.ID.ID_opc = s.ID.ID_opc`
    by METIS_TAC [agp32_same_ID_items_before_EX_pipeline,Abbr `s`,Abbr `s'`] >>
  Cases_on `enable_stg 3 (agp32 fext fbits t)` >-
   (fs [is_sch_execute_def] >>
    Cases_on `isJump_hw_op (agp32 fext fbits t)` >-
     METIS_TAC [] >>
    Cases_on `reg_data_hazard (agp32 fext fbits t)` >-
     METIS_TAC [] >>
    `I' (3,SUC t) = I' (2,t)` by fs [] >> fs [] >>
    `s'.ID.ID_EX_write_enable` by fs [enable_stg_def,Abbr `s`] >>
    `~s.EX.EX_NOP_flag`
      by fs [enable_stg_def,Abbr `s`,
             agp32_ID_EX_write_enable_no_jump_or_reg_data_hazard_EX_NOP_flag_F] >>
    rw [EX_pipeline_def,reg_iswrite_def] >> fs [Rel_def,ID_Rel_def]) >> 
  `I' (3,SUC t) = I' (3,t)` by fs [is_sch_disable_def] >>
  `~s'.ID.ID_EX_write_enable` by fs [enable_stg_def,Abbr `s`] >>
  rw [EX_pipeline_def] >>
  fs [Rel_def,EX_Rel_def]
QED

(** EX_dataA/B/W **)
Theorem agp32_Rel_ag32_EX_dataA_correct:
  !fext fbits a t I.
    is_sch_execute I (agp32 fext fbits) a ==>
    is_sch_disable I (agp32 fext fbits) ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (3,SUC t) <> NONE ==>
    (agp32 fext fbits (SUC t)).EX.EX_dataA = dataA (FUNPOW Next (THE (I (3,SUC t)) − 1) a)
Proof
  rw [] >> Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state;WB_pipeline;MEM_pipeline] (fext t) s s` >>
  `(agp32 fext fbits (SUC t)).EX.EX_dataA = (EX_pipeline (fext t) s s').EX.EX_dataA`
    by fs [agp32_EX_data_updated_by_EX_pipeline] >> rw [] >>
  `(s'.ID.ID_EX_write_enable = s.ID.ID_EX_write_enable) /\
  (s'.EX.EX_dataA = s.EX.EX_dataA) /\ (s'.ID.ID_dataA = s.ID.ID_dataA)`
    by METIS_TAC [Abbr `s`,Abbr `s'`,agp32_same_EX_items_before_EX_pipeline,
                  agp32_same_ID_items_before_EX_pipeline] >>
  Cases_on `enable_stg 3 (agp32 fext fbits t)` >-
   (fs [is_sch_execute_def] >>
    Cases_on `isJump_hw_op (agp32 fext fbits t)` >-
     METIS_TAC [] >>
    Cases_on `reg_data_hazard (agp32 fext fbits t)` >-
     METIS_TAC [] >>
    `I' (3,SUC t) = I' (2,t)` by fs [] >> fs [] >>
    `s'.ID.ID_EX_write_enable` by fs [enable_stg_def,Abbr `s`] >>
    rw [EX_pipeline_def] >> fs [Rel_def,ID_Rel_def,ID_reg_data_Rel_def] >>
    Cases_on `s.ID.ID_addrA_disable` >>
    fs [reg_data_hazard_def,ID_data_dep_Rel_def] >> METIS_TAC []) >> 
  `I' (3,SUC t) = I' (3,t)` by fs [is_sch_disable_def] >>
  `~s'.ID.ID_EX_write_enable` by fs [enable_stg_def,Abbr `s`] >>
  rw [EX_pipeline_def] >>
  fs [Rel_def,EX_Rel_def]
QED

Theorem agp32_Rel_ag32_EX_dataB_correct:
  !fext fbits a t I.
    is_sch_execute I (agp32 fext fbits) a ==>
    is_sch_disable I (agp32 fext fbits) ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (3,SUC t) <> NONE ==>
    (agp32 fext fbits (SUC t)).EX.EX_dataB = dataB (FUNPOW Next (THE (I (3,SUC t)) − 1) a)
Proof
  rw [] >> Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state;WB_pipeline;MEM_pipeline] (fext t) s s` >>
  `(agp32 fext fbits (SUC t)).EX.EX_dataB = (EX_pipeline (fext t) s s').EX.EX_dataB`
    by fs [agp32_EX_data_updated_by_EX_pipeline] >> rw [] >>
  `(s'.ID.ID_EX_write_enable = s.ID.ID_EX_write_enable) /\
  (s'.EX.EX_dataB = s.EX.EX_dataB) /\ (s'.ID.ID_dataB = s.ID.ID_dataB)`
    by METIS_TAC [Abbr `s`,Abbr `s'`,agp32_same_EX_items_before_EX_pipeline,
                  agp32_same_ID_items_before_EX_pipeline] >>
  Cases_on `enable_stg 3 (agp32 fext fbits t)` >-
   (fs [is_sch_execute_def] >>
    Cases_on `isJump_hw_op (agp32 fext fbits t)` >-
     METIS_TAC [] >>
    Cases_on `reg_data_hazard (agp32 fext fbits t)` >-
     METIS_TAC [] >>
    `I' (3,SUC t) = I' (2,t)` by fs [] >> fs [] >>
    `s'.ID.ID_EX_write_enable` by fs [enable_stg_def,Abbr `s`] >>
    rw [EX_pipeline_def] >> fs [Rel_def,ID_Rel_def,ID_reg_data_Rel_def] >>
    Cases_on `s.ID.ID_addrB_disable` >>
    fs [reg_data_hazard_def,ID_data_dep_Rel_def] >> METIS_TAC []) >> 
  `I' (3,SUC t) = I' (3,t)` by fs [is_sch_disable_def] >>
  `~s'.ID.ID_EX_write_enable` by fs [enable_stg_def,Abbr `s`] >>
  rw [EX_pipeline_def] >>
  fs [Rel_def,EX_Rel_def]
QED

Theorem agp32_Rel_ag32_EX_dataW_correct:
  !fext fbits a t I.
    is_sch_execute I (agp32 fext fbits) a ==>
    is_sch_disable I (agp32 fext fbits) ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (3,SUC t) <> NONE ==>
    (agp32 fext fbits (SUC t)).EX.EX_dataW = dataW (FUNPOW Next (THE (I (3,SUC t)) − 1) a)
Proof
  rw [] >> Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state;WB_pipeline;MEM_pipeline] (fext t) s s` >>
  `(agp32 fext fbits (SUC t)).EX.EX_dataW = (EX_pipeline (fext t) s s').EX.EX_dataW`
    by fs [agp32_EX_data_updated_by_EX_pipeline] >> rw [] >>
  `(s'.ID.ID_EX_write_enable = s.ID.ID_EX_write_enable) /\
  (s'.EX.EX_dataW = s.EX.EX_dataW) /\ (s'.ID.ID_dataW = s.ID.ID_dataW)`
    by METIS_TAC [Abbr `s`,Abbr `s'`,agp32_same_EX_items_before_EX_pipeline,
                  agp32_same_ID_items_before_EX_pipeline] >>
  Cases_on `enable_stg 3 (agp32 fext fbits t)` >-
   (fs [is_sch_execute_def] >>
    Cases_on `isJump_hw_op (agp32 fext fbits t)` >-
     METIS_TAC [] >>
    Cases_on `reg_data_hazard (agp32 fext fbits t)` >-
     METIS_TAC [] >>
    `I' (3,SUC t) = I' (2,t)` by fs [] >> fs [] >>
    `s'.ID.ID_EX_write_enable` by fs [enable_stg_def,Abbr `s`] >>
    rw [EX_pipeline_def] >> fs [Rel_def,ID_Rel_def,ID_reg_data_Rel_def] >>
    Cases_on `s.ID.ID_addrW_disable` >>
    fs [reg_data_hazard_def,ID_data_dep_Rel_def] >> METIS_TAC []) >> 
  `I' (3,SUC t) = I' (3,t)` by fs [is_sch_disable_def] >>
  `~s'.ID.ID_EX_write_enable` by fs [enable_stg_def,Abbr `s`] >>
  rw [EX_pipeline_def] >>
  fs [Rel_def,EX_Rel_def]
QED

(** EX_imm_updated **)
(** when opc is not 14w **)
Theorem agp32_Rel_ag32_EX_imm_updated_correct_not_LoadUpperConstant:
  !fext fbits a t I.
    is_sch_execute I (agp32 fext fbits) a ==>
    is_sch_disable I (agp32 fext fbits) ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (3,SUC t) <> NONE ==>
    (agp32 fext fbits (SUC t)).EX.EX_opc <> 14w ==>
    (agp32 fext fbits (SUC t)).EX.EX_imm_updated = imm (FUNPOW Next (THE (I (3,SUC t)) − 1) a)
Proof
  rw [] >> Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state;WB_pipeline;MEM_pipeline;EX_pipeline;
                            REG_write;ID_pipeline;IF_PC_update;Acc_compute] (fext t) s s` >>
  Q.ABBREV_TAC `s'' = procs [IF_instr_update;ID_opc_func_update;ID_imm_update;ID_data_update;
                             ID_data_check_update;EX_ctrl_update] (fext (SUC t)) s' s'` >>
  `(agp32 fext fbits (SUC t)).EX.EX_imm_updated =
  (EX_ALU_input_imm_update (fext (SUC t)) s' s'').EX.EX_imm_updated`
    by fs [agp32_EX_imm_updated_updated_by_EX_ALU_input_imm_update] >>
  `s'.EX.EX_opc = (agp32 fext fbits (SUC t)).EX.EX_opc`
    by fs [agp32_same_EX_pipeline_items_after_EX_pipeline] >>
  `s''.EX.EX_imm = (agp32 fext fbits (SUC t)).EX.EX_imm`
    by METIS_TAC [Abbr `s`,Abbr `s'`,Abbr `s''`,agp32_same_items_after_EX_ctrl_update] >>
  fs [EX_ALU_input_imm_update_def,MUX_21_def] >>
  METIS_TAC [agp32_Rel_ag32_EX_imm_correct]
QED

(** when opc is 14w **)
Theorem agp32_Rel_ag32_EX_imm_updated_correct_LoadUpperConstant:
  !fext fbits a t I.
    is_sch_execute I (agp32 fext fbits) a ==>
    is_sch_disable I (agp32 fext fbits) ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (3,SUC t) <> NONE ==>
    (agp32 fext fbits (SUC t)).EX.EX_opc = 14w ==>
    (agp32 fext fbits (SUC t)).EX.EX_imm_updated =
    (8 >< 0) (imm (FUNPOW Next (THE (I (3,SUC t)) − 1) a)) @@
             (22 >< 0) (dataW (FUNPOW Next (THE (I (3,SUC t)) − 1) a))
Proof
  rw [] >> Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state;WB_pipeline;MEM_pipeline;EX_pipeline;
                            REG_write;ID_pipeline;IF_PC_update;Acc_compute] (fext t) s s` >>
  Q.ABBREV_TAC `s'' = procs [IF_instr_update;ID_opc_func_update;ID_imm_update;ID_data_update;
                             ID_data_check_update;EX_ctrl_update] (fext (SUC t)) s' s'` >>
  `(agp32 fext fbits (SUC t)).EX.EX_imm_updated =
  (EX_ALU_input_imm_update (fext (SUC t)) s' s'').EX.EX_imm_updated`
    by fs [agp32_EX_imm_updated_updated_by_EX_ALU_input_imm_update] >>
  `s'.EX.EX_opc = (agp32 fext fbits (SUC t)).EX.EX_opc`
    by fs [agp32_same_EX_pipeline_items_after_EX_pipeline] >>
  `(s''.EX.EX_imm = (agp32 fext fbits (SUC t)).EX.EX_imm) /\
  (s''.EX.EX_dataW = (agp32 fext fbits (SUC t)).EX.EX_dataW)`
    by METIS_TAC [Abbr `s`,Abbr `s'`,Abbr `s''`,agp32_same_items_after_EX_ctrl_update] >>
  fs [EX_ALU_input_imm_update_def,MUX_21_def] >>
  METIS_TAC [agp32_Rel_ag32_EX_imm_correct,agp32_Rel_ag32_EX_dataW_correct]
QED

(** EX_ALU_input **)
Theorem agp32_Rel_ag32_EX_ALU_input1_correct:
  !fext fbits a t I.
    is_sch_execute I (agp32 fext fbits) a ==>
    is_sch_disable I (agp32 fext fbits) ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (3,SUC t) <> NONE ==>
    (agp32 fext fbits (SUC t)).EX.EX_ALU_input1 = ALU_input1 (FUNPOW Next (THE (I (3,SUC t)) − 1) a)
Proof
  rw [] >> Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state;WB_pipeline;MEM_pipeline;EX_pipeline;
                            REG_write;ID_pipeline;IF_PC_update;Acc_compute] (fext t) s s` >>
  Q.ABBREV_TAC `s'' = procs [IF_instr_update;ID_opc_func_update;ID_imm_update;ID_data_update;
                             ID_data_check_update;EX_ctrl_update] (fext (SUC t)) s' s'` >>
  `(agp32 fext fbits (SUC t)).EX.EX_ALU_input1 =
  (EX_ALU_input_imm_update (fext (SUC t)) s' s'').EX.EX_ALU_input1`
    by fs [agp32_EX_ALU_input_updated_by_EX_ALU_input_imm_update] >>
  `(s'.EX.EX_opc = (agp32 fext fbits (SUC t)).EX.EX_opc) /\
  (s'.EX.EX_PC = (agp32 fext fbits (SUC t)).EX.EX_PC) /\
  (s'.EX.EX_dataA = (agp32 fext fbits (SUC t)).EX.EX_dataA)`
    by fs [agp32_same_EX_pipeline_items_after_EX_pipeline] >>
  fs [EX_ALU_input_imm_update_def,ALU_input1_def,MUX_21_def] >>
  METIS_TAC [agp32_Rel_ag32_EX_opc_correct,agp32_Rel_ag32_EX_dataA_correct,
             agp32_Rel_ag32_EX_PC_correct]
QED

Theorem agp32_Rel_ag32_EX_ALU_input2_correct:
  !fext fbits a t I.
    is_sch_execute I (agp32 fext fbits) a ==>
    is_sch_disable I (agp32 fext fbits) ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (3,SUC t) <> NONE ==>
    (agp32 fext fbits (SUC t)).EX.EX_ALU_input2 = ALU_input2 (FUNPOW Next (THE (I (3,SUC t)) − 1) a)
Proof
  rw [] >> Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state;WB_pipeline;MEM_pipeline;EX_pipeline;
                            REG_write;ID_pipeline;IF_PC_update;Acc_compute] (fext t) s s` >>
  Q.ABBREV_TAC `s'' = procs [IF_instr_update;ID_opc_func_update;ID_imm_update;ID_data_update;
                             ID_data_check_update;EX_ctrl_update] (fext (SUC t)) s' s'` >>
  `(agp32 fext fbits (SUC t)).EX.EX_ALU_input2 =
  (EX_ALU_input_imm_update (fext (SUC t)) s' s'').EX.EX_ALU_input2`
    by fs [agp32_EX_ALU_input_updated_by_EX_ALU_input_imm_update] >>
  `(s'.EX.EX_opc = (agp32 fext fbits (SUC t)).EX.EX_opc) /\
  (s'.EX.EX_dataA = (agp32 fext fbits (SUC t)).EX.EX_dataA) /\
  (s'.EX.EX_dataB = (agp32 fext fbits (SUC t)).EX.EX_dataB)`
    by fs [agp32_same_EX_pipeline_items_after_EX_pipeline] >>
  fs [EX_ALU_input_imm_update_def,ALU_input2_def,MUX_21_def] >>
  METIS_TAC [agp32_Rel_ag32_EX_opc_correct,agp32_Rel_ag32_EX_dataA_correct,
             agp32_Rel_ag32_EX_dataB_correct]
QED

(** EX_ALU_res **)
Theorem agp32_Rel_ag32_EX_ALU_res_correct:
  !fext fbits a t I.
    is_sch I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (3,SUC t) <> NONE ==>
    (agp32 fext fbits (SUC t)).EX.EX_ALU_res = ALU_res (FUNPOW Next (THE (I (3,SUC t)) − 1) a)
Proof
  rw [] >> Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state;WB_pipeline;MEM_pipeline;EX_pipeline;
                            REG_write;ID_pipeline;IF_PC_update;Acc_compute] (fext t) s s` >>
  Q.ABBREV_TAC `s'' = procs [IF_instr_update;ID_opc_func_update;ID_imm_update;ID_data_update;
                             ID_data_check_update;EX_ctrl_update;EX_ALU_input_imm_update] (fext (SUC t)) s' s'` >>
  `(agp32 fext fbits (SUC t)).EX.EX_ALU_res = (EX_ALU_update (fext (SUC t)) s' s'').EX.EX_ALU_res`
    by fs [agp32_EX_ALU_items_updated_by_EX_ALU_update] >>
  `(s''.ID.ID_EX_write_enable = s.ID.ID_EX_write_enable) /\
  (s''.EX.EX_overflow_flag = s.EX.EX_overflow_flag) /\
  (s''.EX.EX_carry_flag = s.EX.EX_carry_flag) /\
  (s''.EX.EX_ALU_res = s.EX.EX_ALU_res)` by cheat >>
  `(s''.EX.EX_ALU_input1 = (agp32 fext fbits (SUC t)).EX.EX_ALU_input1) /\
  (s''.EX.EX_ALU_input2 = (agp32 fext fbits (SUC t)).EX.EX_ALU_input2) /\
  (s''.EX.EX_func = (agp32 fext fbits (SUC t)).EX.EX_func)` by cheat >>
  Cases_on `enable_stg 3 (agp32 fext fbits t)` >-
   (`s''.ID.ID_EX_write_enable` by fs [enable_stg_def,Abbr `s`] >>
    `s''.EX.EX_func = func (FUNPOW Next (THE (I' (3,SUC t)) − 1) a)`
      by fs [is_sch_def,agp32_Rel_ag32_EX_func_correct] >>
    `s''.EX.EX_ALU_input1 = ALU_input1 (FUNPOW Next (THE (I' (3,SUC t)) − 1) a)`
      by fs [is_sch_def,agp32_Rel_ag32_EX_ALU_input1_correct] >>
    `s''.EX.EX_ALU_input2 = ALU_input2 (FUNPOW Next (THE (I' (3,SUC t)) − 1) a)`
      by fs [is_sch_def,agp32_Rel_ag32_EX_ALU_input2_correct] >>
    fs [EX_ALU_update_def,ALU_res_def,ALU_def] >>
    Cases_on_word_value `(agp32 fext fbits (SUC t)).EX.EX_func` >> fs [] >-
     (simp [word_mul_def,w2n_w2w] >> BBLAST_TAC) >-
     (Cases_on `I' (3,t) <> NONE` >-
       (fs [Rel_def] >>
        `THE (I' (3,SUC t)) = THE (I' (3,t)) + 1`
          by METIS_TAC [EX_instr_index_t_SUC_t_enable] >> fs []) >>
      fs [] >> cheat) >-
     (Cases_on `I' (3,t) <> NONE` >-
       (fs [Rel_def] >>
        `THE (I' (3,SUC t)) = THE (I' (3,t)) + 1`
          by METIS_TAC [EX_instr_index_t_SUC_t_enable] >> fs []) >>
      fs [] >> cheat) >-
     (`s.EX.EX_carry_flag = (FUNPOW Next (THE (I' (3,SUC t)) − 1) a).CarryFlag` by cheat >>
      rw [ALU_correct_v2w_carry33_lem,ALU_correct_v2w_carry32_lem] >>
      BBLAST_TAC) >>
    BBLAST_TAC) >>
  `I' (3,SUC t) = I' (3,t)` by fs [is_sch_def,is_sch_disable_def] >>
  `~s''.ID.ID_EX_write_enable` by fs [enable_stg_def,Abbr `s`] >>
  rw [EX_ALU_update_def] >>
  fs [Rel_def,EX_Rel_def]
QED


(* EX stage *)
Theorem agp32_Rel_ag32_EX_Rel_correct:
  !fext fbits a t I.
    is_sch_execute I (agp32 fext fbits) a ==>
    is_sch_disable I (agp32 fext fbits) ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (3,SUC t) <> NONE ==>
    EX_Rel (fext (SUC t)) (agp32 fext fbits (SUC t)) a (THE (I (3,SUC t)))
Proof
  rw [EX_Rel_def] >>
  fs [agp32_Rel_ag32_EX_PC_correct,agp32_Rel_ag32_EX_addrW_correct,
      agp32_Rel_ag32_EX_imm_correct,agp32_Rel_ag32_EX_opc_correct,
      agp32_Rel_ag32_EX_func_correct,agp32_Rel_ag32_EX_write_reg_correct,
      agp32_Rel_ag32_EX_dataA_correct,agp32_Rel_ag32_EX_dataB_correct,
      agp32_Rel_ag32_EX_dataW_correct,agp32_Rel_ag32_EX_imm_updated_correct_not_LoadUpperConstant,
      agp32_Rel_ag32_EX_imm_updated_correct_LoadUpperConstant,
      agp32_Rel_ag32_EX_ALU_input1_correct,agp32_Rel_ag32_EX_ALU_input2_correct] >>
  cheat
QED

val _ = export_theory ();
