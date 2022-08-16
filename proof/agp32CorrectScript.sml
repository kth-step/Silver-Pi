open hardwarePreamble translatorTheory translatorLib arithmeticTheory dep_rewrite blastLib bitstringSyntax fcpSyntax listSyntax wordsSyntax agp32StateTheory agp32EnvironmentTheory agp32ProcessorTheory ag32Theory ag32ExtraTheory ag32UtilitiesTheory agp32RelationTheory agp32UpdateTheory agp32InternalTheory agp32StepLib agp32_IF_CorrectTheory agp32_ID_CorrectTheory;

(* correctness of the pipelined Silver circuit against the ISA *)
val _ = new_theory "agp32Correct";

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
(** copy end **)
                                              
Theorem w2n_add_MOD_itself:
  !(w1:word32) (w2:word32).
    w2n w1 + w2n w2 = (w2n w1 + w2n w2) MOD 8589934592
Proof
  rw [] >>
  `(w2n w1 < 4294967296) /\ (w2n w2 < 4294967296)` by METIS_TAC [w2n_lt,dimword_32] >>
  fs []
QED

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


(* Init relation implies Rel at cycle 0 *)
Theorem agp32_Init_implies_Rel:
  !fext fbits s a I.
    s = agp32 fext fbits ==>
    is_sch_init I ==>
    Init (fext 0) (s 0) a ==>
    Rel I (fext 0) (s 0) (s 0) a 0
Proof
  rpt strip_tac >>
  fs [Init_def,Rel_def,is_sch_init_def] >>
  rw [IF_disable_Rel_def] >-
   fs [agp32_init_IF_PC_input] >>
  fs [enable_stg_def,reg_data_vaild_def] >> fs []
QED


(* correctness of the pipelined Silver concerning the ISA *)
Theorem agp32_Rel_ag32_correct:
  !fext fbits s a t I.
    s = agp32 fext fbits ==>
    SC_self_mod_isa a ==>
    is_mem fext_accessor_circuit s fext ==>
    is_acc accelerator_f s ==>
    is_interrupt_interface fext_accessor_circuit s fext ==>
    is_data_in fext ==>
    is_sch I s a ==>
    Init (fext 0) (s 0) a ==>
    Rel I (fext t) (s (t-1)) (s t) a t
Proof
  Induct_on `t` >>
  rpt strip_tac >-
   (SIMP_TAC std_ss [] >> METIS_TAC [agp32_Init_implies_Rel,is_sch_def]) >>
  `Rel I' (fext t) (s (t-1)) (s t) a t` by METIS_TAC [] >>
  rw [Rel_def] >-
   (** data_in **)
   fs [Rel_def,is_data_in_def,ag32_data_in_unchanged_all] >-
   (** carryflag **)
   (*METIS_TAC [agp32_Rel_ag32_carry_flag_correct]*)
   cheat >-
   (** overflow flag **)
   cheat >-
   (** PC_input when jump **)
   fs [is_sch_def,agp32_Rel_ag32_IF_PC_input_jump_correct] >-
   (** PC_input when no jump **)
   fs [is_sch_def,agp32_Rel_ag32_IF_PC_input_not_jump_correct] >-
   (** memory **)
   cheat >-
   (** fext not ready, fetch disabled **)
   fs [enable_stg_def,not_fext_ready_and_agp32_IF_PC_write_disable] >-
   (** data_out **)
   cheat >-
   (** registers **)
   cheat >-
   (** IF **)
   fs [is_sch_def,agp32_Rel_ag32_IF_Rel_correct] >-
   (** IF when disable **)
   fs [is_sch_def,IF_disable_Rel_def,agp32_Rel_ag32_IF_disable_PC_correct] >-
   (** ID **)
   METIS_TAC [is_sch_def,agp32_Rel_ag32_ID_Rel_correct] >-
   (** EX **)
   cheat >-
   (** MEM **)
   cheat >>
   (** WB **)
   cheat
QED

val _ = export_theory ();
