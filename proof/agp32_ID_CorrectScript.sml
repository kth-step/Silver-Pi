open hardwarePreamble translatorTheory translatorLib arithmeticTheory wordsExtraTheory dep_rewrite blastLib bitstringSyntax fcpSyntax listSyntax wordsSyntax agp32StateTheory agp32EnvironmentTheory agp32ProcessorTheory ag32Theory ag32ExtraTheory ag32UtilitiesTheory agp32RelationTheory agp32UpdateTheory agp32InternalTheory;

(* correctness of ID stage items with respect to the ISA *)
val _ = new_theory "agp32_ID_Correct";

val _ = prefer_num ();
val _ = guess_lengths ();


(** ID_PC **)
Theorem agp32_Rel_ag32_ID_PC_correct:
  !fext fbits a t I.
    is_sch_decode I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    enable_stg 2 (agp32 fext fbits t) ==>
    I (2,SUC t) <> NONE ==>
    (agp32 fext fbits (SUC t)).ID.ID_PC = (FUNPOW Next (THE (I (2,SUC t)) − 1) a).PC
Proof
  rw [is_sch_decode_def] >>
  Cases_on `isJump_isa_op (I' (2,t)) a \/ isJump_isa_op (I' (3,t)) a` >-
   METIS_TAC [] >>
  `I' (2,SUC t) = I' (1,t)` by fs [] >> fs [] >>
  Q.ABBREV_TAC `s = agp32 fext fbits t` >>             
  Q.ABBREV_TAC `s' = procs [agp32_next_state;WB_pipeline;MEM_pipeline;EX_pipeline;
                            REG_write] (fext t) s s` >>
  `(agp32 fext fbits (SUC t)).ID.ID_PC = (ID_pipeline (fext t) s s').ID.ID_PC`
    by fs [agp32_ID_PC_instr_updated_by_ID_pipeline,Abbr `s`,Abbr `s'`] >> rw [] >>
  `s.ID.ID_ID_write_enable` by fs [enable_stg_def] >>
  `s'.ID.ID_ID_write_enable`
    by METIS_TAC [agp32_same_items_before_ID_pipeline,Abbr `s`,Abbr `s'`] >>
  rw [ID_pipeline_def] >>
  fs [Rel_def,IF_PC_Rel_def]
QED


(** ID_instr **)
Theorem agp32_Rel_ag32_ID_instr_correct:
  !fext fbits a t I.
    is_sch_decode I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    enable_stg 2 (agp32 fext fbits t) ==>
    I (2,SUC t) <> NONE ==>
    (agp32 fext fbits (SUC t)).ID.ID_instr = instr (FUNPOW Next (THE (I (2,SUC t)) − 1) a)
Proof
  rw [is_sch_decode_def] >>
  Cases_on `isJump_isa_op (I' (2,t)) a \/ isJump_isa_op (I' (3,t)) a` >-
   METIS_TAC [] >>
  `I' (2,SUC t) = I' (1,t)` by fs [] >> fs [] >>
  Q.ABBREV_TAC `s = agp32 fext fbits t` >>             
  Q.ABBREV_TAC `s' = procs [agp32_next_state;WB_pipeline;MEM_pipeline;EX_pipeline;
                            REG_write] (fext t) s s` >>
  `(agp32 fext fbits (SUC t)).ID.ID_instr = (ID_pipeline (fext t) s s').ID.ID_instr`
    by fs [agp32_ID_PC_instr_updated_by_ID_pipeline,Abbr `s`,Abbr `s'`] >> rw [] >>
  `s.ID.ID_ID_write_enable` by fs [enable_stg_def] >>
  `s'.ID.ID_ID_write_enable /\ s'.IF.IF_instr = s.IF.IF_instr`
    by METIS_TAC [agp32_same_items_before_ID_pipeline,Abbr `s`,Abbr `s'`] >>
  rw [ID_pipeline_def] >-
    (`s.ID.ID_flush_flag`
       by METIS_TAC [agp32_same_items_before_ID_pipeline,Abbr `s`,Abbr `s'`] >> 
     `s.EX.EX_jump_sel`
       by fs [agp32_ID_ID_write_enable_flush_flag_then_EX_jump_sel,Abbr `s`,enable_stg_def] >>
     `reg_data_vaild 3 s` 
       by fs [agp32_ID_ID_write_enable_MEM_state_flag,Abbr `s`,reg_data_vaild_def,enable_stg_def] >>
     fs [Rel_def,EX_Rel_spec_def]) >>
  `(fext t).ready` by METIS_TAC [enable_stg_def,agp32_ID_ID_write_enable_and_fext_ready] >>
  fs [Rel_def,IF_instr_Rel_def]
QED


(** ID_addrA/B/W **)
Theorem agp32_Rel_ag32_ID_addr_correct:
  !fext fbits a t I.
    is_sch_decode I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    enable_stg 2 (agp32 fext fbits t) ==>
    I (2,SUC t) <> NONE ==>
    ((agp32 fext fbits (SUC t)).ID.ID_addrA = addrA (FUNPOW Next (THE (I (2,SUC t)) − 1) a)) /\
    ((agp32 fext fbits (SUC t)).ID.ID_addrB = addrB (FUNPOW Next (THE (I (2,SUC t)) − 1) a)) /\
    ((agp32 fext fbits (SUC t)).ID.ID_addrW = addrW (FUNPOW Next (THE (I (2,SUC t)) − 1) a))
Proof
  rpt gen_tac >> rpt strip_tac >>
  simp [addrA_def,addrB_def,addrW_def] >>
  `(agp32 fext fbits (SUC t)).ID.ID_instr = instr (FUNPOW Next (THE (I' (2,SUC t)) − 1) a)`
    by fs [agp32_Rel_ag32_ID_instr_correct] >>
  Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state; WB_pipeline; MEM_pipeline; EX_pipeline;
                            REG_write; ID_pipeline; IF_PC_update; Acc_compute] (fext t) s s` >>
  Q.ABBREV_TAC `s'' = procs [ForwardA; ForwardB; ForwardW; IF_instr_update; ID_opc_func_update;
                             ID_imm_update] (fext (SUC t)) s' s'` >>                          
  `?s0. (agp32 fext fbits (SUC t)).ID.ID_addrA = (ID_data_update (fext (SUC t)) s0 s'').ID.ID_addrA /\
  (agp32 fext fbits (SUC t)).ID.ID_addrB = (ID_data_update (fext (SUC t)) s0 s'').ID.ID_addrB /\
  (agp32 fext fbits (SUC t)).ID.ID_addrW = (ID_data_update (fext (SUC t)) s0 s'').ID.ID_addrW`
    by fs [Abbr `s`,Abbr `s'`,Abbr `s''`,agp32_ID_addr_updated_by_ID_data_update] >>
  fs [ID_data_update_def] >>
  `s''.ID.ID_instr = (agp32 fext fbits (SUC t)).ID.ID_instr`
    by fs [Abbr `s`,Abbr `s'`,Abbr `s''`,agp32_same_ID_instr_after_ID_imm_update] >> fs []
QED


(** flagA/B/W: indicate imm or reg **)
Theorem agp32_Rel_ag32_ID_flag_correct:
  !fext fbits a t I.
    is_sch_decode I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    enable_stg 2 (agp32 fext fbits t) ==>
    I (2,SUC t) <> NONE ==>
    ((agp32 fext fbits (SUC t)).ID.ID_addrA_disable = flagA (FUNPOW Next (THE (I (2,SUC t)) − 1) a)) /\
    ((agp32 fext fbits (SUC t)).ID.ID_addrB_disable = flagB (FUNPOW Next (THE (I (2,SUC t)) − 1) a)) /\
    ((agp32 fext fbits (SUC t)).ID.ID_addrW_disable = flagW (FUNPOW Next (THE (I (2,SUC t)) − 1) a))
Proof
  rpt gen_tac >> rpt disch_tac >>
  simp [flagA_def,flagB_def,flagW_def] >>
  `(agp32 fext fbits (SUC t)).ID.ID_instr = instr (FUNPOW Next (THE (I' (2,SUC t)) − 1) a)`
    by fs [agp32_Rel_ag32_ID_instr_correct] >>
  Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state; WB_pipeline; MEM_pipeline; EX_pipeline;
                            REG_write; ID_pipeline; IF_PC_update; Acc_compute] (fext t) s s` >>
  Q.ABBREV_TAC `s'' = procs [ForwardA; ForwardB; ForwardW; IF_instr_update; ID_opc_func_update;
                             ID_imm_update] (fext (SUC t)) s' s'` >>                          
  `((agp32 fext fbits (SUC t)).ID.ID_addrA_disable <=>
    (ID_data_update (fext (SUC t)) s' s'').ID.ID_addrA_disable) /\
  ((agp32 fext fbits (SUC t)).ID.ID_addrB_disable <=>
   (ID_data_update (fext (SUC t)) s' s'').ID.ID_addrB_disable) /\
  ((agp32 fext fbits (SUC t)).ID.ID_addrW_disable <=>
   (ID_data_update (fext (SUC t)) s' s'').ID.ID_addrW_disable)`
    by fs [Abbr `s`,Abbr `s'`,Abbr `s''`,agp32_ID_flag_updated_by_ID_data_update] >>
  fs [ID_data_update_def] >>
  `s''.ID.ID_instr = (agp32 fext fbits (SUC t)).ID.ID_instr`
    by fs [Abbr `s`,Abbr `s'`,Abbr `s''`,agp32_same_ID_instr_after_ID_imm_update] >> fs []
QED


(** immA/B/W **)
Theorem agp32_Rel_ag32_ID_imm_data_correct:
  !fext fbits a t I.
    is_sch_decode I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    enable_stg 2 (agp32 fext fbits t) ==>
    I (2,SUC t) <> NONE ==>
    ((agp32 fext fbits (SUC t)).ID.ID_immA = immA (FUNPOW Next (THE (I (2,SUC t)) − 1) a)) /\
    ((agp32 fext fbits (SUC t)).ID.ID_immB = immB (FUNPOW Next (THE (I (2,SUC t)) − 1) a)) /\
    ((agp32 fext fbits (SUC t)).ID.ID_immW = immW (FUNPOW Next (THE (I (2,SUC t)) − 1) a))
Proof
  rpt gen_tac >> rpt disch_tac >>
  simp [immA_def,immB_def,immW_def] >>
  `(agp32 fext fbits (SUC t)).ID.ID_instr = instr (FUNPOW Next (THE (I' (2,SUC t)) − 1) a)`
    by fs [agp32_Rel_ag32_ID_instr_correct] >>
  Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state; WB_pipeline; MEM_pipeline; EX_pipeline;
                            REG_write; ID_pipeline; IF_PC_update; Acc_compute] (fext t) s s` >>
  Q.ABBREV_TAC `s'' = procs [ForwardA; ForwardB; ForwardW; IF_instr_update; ID_opc_func_update;
                             ID_imm_update] (fext (SUC t)) s' s'` >>                          
  `(agp32 fext fbits (SUC t)).ID.ID_immA = (ID_data_update (fext (SUC t)) s' s'').ID.ID_immA /\
  (agp32 fext fbits (SUC t)).ID.ID_immB = (ID_data_update (fext (SUC t)) s' s'').ID.ID_immB /\
  (agp32 fext fbits (SUC t)).ID.ID_immW = (ID_data_update (fext (SUC t)) s' s'').ID.ID_immW`
    by fs [Abbr `s`,Abbr `s'`,Abbr `s''`,agp32_ID_imm_data_updated_by_ID_data_update] >>
  fs [ID_data_update_def] >>
  `s''.ID.ID_instr = (agp32 fext fbits (SUC t)).ID.ID_instr`
    by fs [Abbr `s`,Abbr `s'`,Abbr `s''`,agp32_same_ID_instr_after_ID_imm_update] >> fs []
QED


(** imm for LoadConstant and LoadUpperConstant **)
Theorem agp32_Rel_ag32_ID_imm_correct:
  !fext fbits a t I.
    is_sch_decode I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    enable_stg 2 (agp32 fext fbits t) ==>
    I (2,SUC t) <> NONE ==>
    (agp32 fext fbits (SUC t)).ID.ID_imm = imm (FUNPOW Next (THE (I (2,SUC t)) − 1) a)
Proof
  rw [] >>
  `(agp32 fext fbits (SUC t)).ID.ID_instr = instr (FUNPOW Next (THE (I' (2,SUC t)) − 1) a)`
    by fs [agp32_Rel_ag32_ID_instr_correct] >>
  Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state; WB_pipeline; MEM_pipeline; EX_pipeline;
                            REG_write; ID_pipeline; IF_PC_update; Acc_compute] (fext t) s s` >>
  Q.ABBREV_TAC `s'' = procs [ForwardA; ForwardB; ForwardW; IF_instr_update; ID_opc_func_update]
                            (fext (SUC t)) s' s'` >>
  `(agp32 fext fbits (SUC t)).ID.ID_imm = (ID_imm_update (fext (SUC t)) s' s'').ID.ID_imm`
    by fs [Abbr `s`,Abbr `s'`,Abbr `s''`,agp32_ID_imm_updated_by_ID_imm_update] >>
  `s''.ID.ID_instr = (agp32 fext fbits (SUC t)).ID.ID_instr`
    by fs [Abbr `s`,Abbr `s'`,Abbr `s''`,agp32_same_ID_instr_after_ID_opc_func_update] >>
   fs [ID_imm_update_def,imm_def] >> rw []
QED


(** ID_opc **)
Theorem agp32_Rel_ag32_ID_opc_correct:
  !fext fbits a t I.
    is_sch_decode I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    enable_stg 2 (agp32 fext fbits t) ==>
    I (2,SUC t) <> NONE ==>
    (agp32 fext fbits (SUC t)).ID.ID_opc = opc (FUNPOW Next (THE (I (2,SUC t)) − 1) a)
Proof
  rw [] >>
  `(agp32 fext fbits (SUC t)).ID.ID_instr = instr (FUNPOW Next (THE (I' (2,SUC t)) − 1) a)`
    by fs [agp32_Rel_ag32_ID_instr_correct] >>
  Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state; WB_pipeline; MEM_pipeline; EX_pipeline;
                            REG_write; ID_pipeline; IF_PC_update; Acc_compute] (fext t) s s` >>
  Q.ABBREV_TAC `s'' = procs [ForwardA; ForwardB; ForwardW; IF_instr_update] (fext (SUC t)) s' s'` >>
  `?s0.(agp32 fext fbits (SUC t)).ID.ID_opc = (ID_opc_func_update (fext (SUC t)) s0 s'').ID.ID_opc`
    by fs [Abbr `s`,Abbr `s'`,Abbr `s''`,agp32_ID_opc_func_updated_by_ID_opc_func_update] >>
  `s''.ID.ID_instr = (agp32 fext fbits (SUC t)).ID.ID_instr`
    by fs [Abbr `s`,Abbr `s'`,Abbr `s''`,agp32_same_ID_instr_after_IF_instr_update] >> fs [] >>
  rw [ID_opc_func_update_def,opc_def]
QED


(** ID_func **)
(** lemmas show the relation between the ID_opc and ID_func **)
Theorem ID_opc_func_update_normal_func:
  !fext s s'.
    ((ID_opc_func_update fext s s').ID.ID_opc = 0w) \/
    ((ID_opc_func_update fext s s').ID.ID_opc = 6w) \/
    ((ID_opc_func_update fext s s').ID.ID_opc = 9w) \/
    ((ID_opc_func_update fext s s').ID.ID_opc = 10w) \/
    ((ID_opc_func_update fext s s').ID.ID_opc = 11w) ==>
    (ID_opc_func_update fext s s').ID.ID_func = (9 >< 6) s'.ID.ID_instr
Proof
  rw [] >> fs [ID_opc_func_update_def] >>
  rw [] >> fs []
QED

Theorem ID_opc_func_update_shift_func:
  !fext s s'.
    (ID_opc_func_update fext s s').ID.ID_opc = 1w ==>
    (ID_opc_func_update fext s s').ID.ID_func = (3w:word2) @@ ((7 >< 6) s'.ID.ID_instr)
Proof
  rw [ID_opc_func_update_def] >> fs [] >>
  Cases_on `word_bit 24 s'.ID.ID_instr` >> fs [] >>
  Cases_on `(5 >< 0) s'.ID.ID_instr = 10w \/ (5 >< 0) s'.ID.ID_instr = 11w \/
            (5 >< 0) s'.ID.ID_instr = 12w` >> fs [] >>
  Cases_on `word_bit 31 s'.ID.ID_instr` >> fs [] >>
  Cases_on `(5 >< 0) s'.ID.ID_instr <+ 10w` >> fs []
QED

Theorem ID_opc_func_update_other_func:
  !fext s s'.
    (ID_opc_func_update fext s s').ID.ID_opc <> 0w ==>
    (ID_opc_func_update fext s s').ID.ID_opc <> 1w ==>
    (ID_opc_func_update fext s s').ID.ID_opc <> 6w ==>
    (ID_opc_func_update fext s s').ID.ID_opc <> 9w ==>
    (ID_opc_func_update fext s s').ID.ID_opc <> 10w ==>
    (ID_opc_func_update fext s s').ID.ID_opc <> 11w ==>
    (ID_opc_func_update fext s s').ID.ID_func = 9w
Proof
  rw [ID_opc_func_update_def] >> fs [] >>
  Cases_on `word_bit 24 s'.ID.ID_instr` >> fs [] >>
  Cases_on `(5 >< 0) s'.ID.ID_instr = 10w \/ (5 >< 0) s'.ID.ID_instr = 11w \/
            (5 >< 0) s'.ID.ID_instr = 12w` >> fs [] >>
  Cases_on `word_bit 31 s'.ID.ID_instr` >> fs [] >>
  Cases_on `(5 >< 0) s'.ID.ID_instr <+ 10w` >> fs [] >>
  Cases_on `(23 >< 9) s'.ID.ID_instr = 0w` >> fs []
QED

(** ID_func is correct **)
Theorem agp32_Rel_ag32_ID_func_correct:
  !fext fbits a t I.
    is_sch_decode I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    enable_stg 2 (agp32 fext fbits t) ==>
    I (2,SUC t) <> NONE ==>
    (agp32 fext fbits (SUC t)).ID.ID_func = func (FUNPOW Next (THE (I (2,SUC t)) − 1) a)
Proof
  rw [] >>
  `(agp32 fext fbits (SUC t)).ID.ID_instr = instr (FUNPOW Next (THE (I' (2,SUC t)) − 1) a)`
    by fs [agp32_Rel_ag32_ID_instr_correct] >>
  `(agp32 fext fbits (SUC t)).ID.ID_opc = opc (FUNPOW Next (THE (I' (2,SUC t)) − 1) a)`
    by fs [agp32_Rel_ag32_ID_opc_correct] >>
  Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state; WB_pipeline; MEM_pipeline; EX_pipeline;
                            REG_write; ID_pipeline; IF_PC_update; Acc_compute] (fext t) s s` >>
  Q.ABBREV_TAC `s'' = procs [ForwardA; ForwardB; ForwardW; IF_instr_update] (fext (SUC t)) s' s'` >>
  `?s0.
    (agp32 fext fbits (SUC t)).ID.ID_opc = (ID_opc_func_update (fext (SUC t)) s0 s'').ID.ID_opc /\
  (agp32 fext fbits (SUC t)).ID.ID_func = (ID_opc_func_update (fext (SUC t)) s0 s'').ID.ID_func`
    by fs [Abbr `s`,Abbr `s'`,Abbr `s''`,agp32_ID_opc_func_updated_by_ID_opc_func_update] >>
  `s''.ID.ID_instr = (agp32 fext fbits (SUC t)).ID.ID_instr`
    by fs [Abbr `s`,Abbr `s'`,Abbr `s''`,agp32_same_ID_instr_after_IF_instr_update] >>
  Cases_on `((ID_opc_func_update (fext (SUC t)) s0 s'').ID.ID_opc = 0w) \/
  ((ID_opc_func_update (fext (SUC t)) s0 s'').ID.ID_opc = 6w) \/
  ((ID_opc_func_update (fext (SUC t)) s0 s'').ID.ID_opc = 9w) \/
  ((ID_opc_func_update (fext (SUC t)) s0 s'').ID.ID_opc = 10w) \/
  ((ID_opc_func_update (fext (SUC t)) s0 s'').ID.ID_opc = 11w)` >-
   (`(ID_opc_func_update (fext (SUC t)) s0 s'').ID.ID_func = (9 >< 6) s''.ID.ID_instr`
      by fs [ID_opc_func_update_normal_func] >>
    simp [func_def] >> fs [] >>
    rw [] >> METIS_TAC []) >>
  Cases_on `(ID_opc_func_update (fext (SUC t)) s0 s'').ID.ID_opc = 1w` >-
   (`(ID_opc_func_update (fext (SUC t)) s0 s'').ID.ID_func = (3w:word2) @@ ((7 >< 6) s''.ID.ID_instr)`
      by fs [ID_opc_func_update_shift_func] >> fs [func_def]) >>
  fs [func_def,ID_opc_func_update_other_func] >> METIS_TAC []
QED


(** ID_data: when using the imm, dataA/B/W are correct **)
Theorem agp32_Rel_ag32_ID_dataA_correct_using_immA:
  !fext fbits a t I.
    is_sch_decode I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    enable_stg 2 (agp32 fext fbits t) ==>
    I (2,SUC t) <> NONE ==>
    (agp32 fext fbits (SUC t)).ID.ID_addrA_disable ==>
    (agp32 fext fbits (SUC t)).ID.ID_dataA = dataA (FUNPOW Next (THE (I (2,SUC t)) − 1) a)
Proof
  rw [] >>
  `flagA (FUNPOW Next (THE (I' (2,SUC t)) − 1) a)` by METIS_TAC [agp32_Rel_ag32_ID_flag_correct] >>
  rw [dataA_correct_rewrite_flag_imm_reg_data,v2w_single_0w] >>
  fs [agp32_ID_addrA_disable_dataA_immA,agp32_Rel_ag32_ID_imm_data_correct]
QED

Theorem agp32_Rel_ag32_ID_dataB_correct_using_immB:
  !fext fbits a t I.
    is_sch_decode I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    enable_stg 2 (agp32 fext fbits t) ==>
    I (2,SUC t) <> NONE ==>
    (agp32 fext fbits (SUC t)).ID.ID_addrB_disable ==>
    (agp32 fext fbits (SUC t)).ID.ID_dataB = dataB (FUNPOW Next (THE (I (2,SUC t)) − 1) a)
Proof
  rw [] >>
  `flagB (FUNPOW Next (THE (I' (2,SUC t)) − 1) a)` by METIS_TAC [agp32_Rel_ag32_ID_flag_correct] >>
  rw [dataB_correct_rewrite_flag_imm_reg_data,v2w_single_0w] >>
  fs [agp32_ID_addrB_disable_dataB_immB,agp32_Rel_ag32_ID_imm_data_correct]
QED

Theorem agp32_Rel_ag32_ID_dataW_correct_using_immW:
  !fext fbits a t I.
    is_sch_decode I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    enable_stg 2 (agp32 fext fbits t) ==>
    I (2,SUC t) <> NONE ==>
    (agp32 fext fbits (SUC t)).ID.ID_addrW_disable ==>
    (agp32 fext fbits (SUC t)).ID.ID_dataW = dataW (FUNPOW Next (THE (I (2,SUC t)) − 1) a)
Proof
  rw [] >>
  `flagW (FUNPOW Next (THE (I' (2,SUC t)) − 1) a)` by METIS_TAC [agp32_Rel_ag32_ID_flag_correct] >>
  rw [dataW_correct_rewrite_flag_imm_reg_data,v2w_single_0w] >>
  fs [agp32_ID_addrW_disable_dataW_immW,agp32_Rel_ag32_ID_imm_data_correct]
QED


(** data forwarding from WB to ID stage **)
Theorem agp32_Rel_ag32_ID_Forward_flags_correct:
  !fext fbits t.
    enable_stg 2 (agp32 fext fbits t) ==>
    ((agp32 fext fbits (SUC t)).ID.ID_ForwardA <=>
     (agp32 fext fbits (SUC t)).ID.ID_addrA = (agp32 fext fbits (SUC t)).WB.WB_addrW /\
     (agp32 fext fbits (SUC t)).WB.WB_write_reg) /\
    ((agp32 fext fbits (SUC t)).ID.ID_ForwardB <=>
     (agp32 fext fbits (SUC t)).ID.ID_addrB = (agp32 fext fbits (SUC t)).WB.WB_addrW /\
     (agp32 fext fbits (SUC t)).WB.WB_write_reg) /\
    ((agp32 fext fbits (SUC t)).ID.ID_ForwardW <=>
     (agp32 fext fbits (SUC t)).ID.ID_addrW = (agp32 fext fbits (SUC t)).WB.WB_addrW /\
     (agp32 fext fbits (SUC t)).WB.WB_write_reg)
Proof
  rpt gen_tac >> rpt disch_tac >>
  fs [enable_stg_def] >> Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state; WB_pipeline; MEM_pipeline; EX_pipeline;
                            REG_write; ID_pipeline; IF_PC_update; Acc_compute] (fext t) s s` >>
  Q.ABBREV_TAC `s'' = procs [ForwardA; ForwardB; ForwardW; IF_instr_update; ID_opc_func_update;
                             ID_imm_update] (fext (SUC t)) s' s'` >>
  `((agp32 fext fbits (SUC t)).ID.ID_ForwardA = (ID_data_update (fext (SUC t)) s' s'').ID.ID_ForwardA) /\
  ((agp32 fext fbits (SUC t)).ID.ID_ForwardB = (ID_data_update (fext (SUC t)) s' s'').ID.ID_ForwardB) /\
  ((agp32 fext fbits (SUC t)).ID.ID_ForwardW = (ID_data_update (fext (SUC t)) s' s'').ID.ID_ForwardW)`
    by fs [Abbr `s`,Abbr `s'`,Abbr `s''`,agp32_ID_Forward_flags_updated_by_ID_data_update] >>
  `?s0. (agp32 fext fbits (SUC t)).ID.ID_addrA = (ID_data_update (fext (SUC t)) s0 s'').ID.ID_addrA /\
  (agp32 fext fbits (SUC t)).ID.ID_addrB = (ID_data_update (fext (SUC t)) s0 s'').ID.ID_addrB /\
  (agp32 fext fbits (SUC t)).ID.ID_addrW = (ID_data_update (fext (SUC t)) s0 s'').ID.ID_addrW`
    by fs [Abbr `s`,Abbr `s'`,Abbr `s''`,agp32_ID_addr_updated_by_ID_data_update] >>
  fs [ID_data_update_def] >>
  `s.WB.WB_state_flag` by fs [Abbr `s`,agp32_ID_ID_write_enable_WB_state_flag] >>
  `s''.WB.WB_state_flag`
    by METIS_TAC [Abbr `s`,Abbr `s'`,Abbr `s''`,agp32_same_WB_state_flag_as_before] >>
  `(s'.WB.WB_addrW = (agp32 fext fbits (SUC t)).WB.WB_addrW) /\
  (s'.WB.WB_write_reg <=> (agp32 fext fbits (SUC t)).WB.WB_write_reg)`
    by fs [Abbr `s`,Abbr `s'`,agp32_same_WB_pipeline_items_after_WB_pipeline] >> rw []
QED


(* ID stage *)
Theorem agp32_Rel_ag32_ID_Rel_correct:
  !fext fbits a t I.
    is_sch_decode I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    enable_stg 2 (agp32 fext fbits t) ==>
    I (2,SUC t) <> NONE ==>
    ID_Rel (agp32 fext fbits (SUC t)) a (THE (I (2,SUC t)))
Proof
  rw [ID_Rel_def] >>
  fs [agp32_Rel_ag32_ID_PC_correct,agp32_Rel_ag32_ID_instr_correct,agp32_Rel_ag32_ID_addr_correct,
      agp32_Rel_ag32_ID_flag_correct,agp32_Rel_ag32_ID_imm_data_correct,
      agp32_Rel_ag32_ID_imm_correct,agp32_Rel_ag32_ID_opc_correct,
      agp32_Rel_ag32_ID_func_correct,agp32_Rel_ag32_ID_dataA_correct_using_immA,
      agp32_Rel_ag32_ID_dataB_correct_using_immB,agp32_Rel_ag32_ID_dataW_correct_using_immW] >>
  METIS_TAC [agp32_Rel_ag32_ID_Forward_flags_correct]
QED


(** ID_read_dataA: when instrs in EX, MEM and WB do not change registers **)
Theorem agp32_Rel_ag32_ID_read_dataA_no_write_before:
  !fext fbits a t I.
    is_sch I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    enable_stg 2 (agp32 fext fbits t) ==>
    I (2,SUC t) <> NONE ==>
    ~reg_adr_update_isa (I (3,SUC t)) a (agp32 fext fbits (SUC t)).ID.ID_addrA ==>
    ~reg_adr_update_isa (I (4,SUC t)) a (agp32 fext fbits (SUC t)).ID.ID_addrA ==>
    ~reg_adr_update_isa (I (5,SUC t)) a (agp32 fext fbits (SUC t)).ID.ID_addrA ==>
    (agp32 fext fbits (SUC t)).ID.ID_read_dataA = reg_dataA (FUNPOW Next (THE (I (2,SUC t)) − 1) a)
Proof
  rw [reg_dataA_def,addrA_def] >>
  `(agp32 fext fbits (SUC t)).ID.ID_instr = instr (FUNPOW Next (THE (I' (2,SUC t)) − 1) a)`
    by fs [is_sch_def,agp32_Rel_ag32_ID_instr_correct] >>
  Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state; WB_pipeline; MEM_pipeline; EX_pipeline;
                            REG_write; ID_pipeline; IF_PC_update; Acc_compute] (fext t) s s` >>
  Q.ABBREV_TAC `s'' = procs [ForwardA; ForwardB; ForwardW; IF_instr_update; ID_opc_func_update;
                             ID_imm_update] (fext (SUC t)) s' s'` >>                          
  `(agp32 fext fbits (SUC t)).ID.ID_read_dataA =
  (ID_data_update (fext (SUC t)) s' s'').ID.ID_read_dataA`
    by fs [Abbr `s`,Abbr `s'`,Abbr `s''`,agp32_ID_read_data_updated_by_ID_data_update] >>
  fs [ID_data_update_def] >>
  `s''.ID.ID_instr = (agp32 fext fbits (SUC t)).ID.ID_instr`
    by fs [Abbr `s`,Abbr `s'`,Abbr `s''`,agp32_same_ID_instr_after_ID_imm_update] >> fs [] >>
  qpat_abbrev_tac `i = instr _` >>
  `s''.R = (agp32 fext fbits (SUC t)).R`
    by fs [Abbr `s`,Abbr `s'`,Abbr `s''`,agp32_same_R_after_ID_imm_update] >> fs [] >>
  Cases_on `I' (5,t) = NONE` >>
  Cases_on `I' (5,SUC t) = NONE` >>
  Cases_on `I' (4,SUC t) = NONE` >>
  Cases_on `I' (3,SUC t) = NONE` >-
   (`(agp32 fext fbits (SUC t)).R = (FUNPOW Next (THE (I' (2,SUC t)) − 1) a).R`
      by cheat >> fs []) >-      
   (`(agp32 fext fbits (SUC t)).R = (FUNPOW Next (THE (I' (3,SUC t)) − 1) a).R`
      by cheat >> fs [] >>
    `(agp32 fext fbits (SUC t)).ID.ID_addrA = (22 >< 17) i`
      by (fs [Abbr `i`,Abbr `s`,is_sch_def] >> METIS_TAC [agp32_Rel_ag32_ID_addr_correct,addrA_def]) >>
    `THE (I' (2,SUC t)) = THE (I' (3,SUC t)) + 1`
      by METIS_TAC [ID_instr_index_with_EX_instr_plus_1] >> fs [] >>
    METIS_TAC [reg_adr_update_isa_not_change_data]) >-
   (`(agp32 fext fbits (SUC t)).R = (FUNPOW Next (THE (I' (4,SUC t)) − 1) a).R`
      by cheat >> fs [] >>
    `(agp32 fext fbits (SUC t)).ID.ID_addrA = (22 >< 17) i`
      by (fs [Abbr `i`,Abbr `s`,is_sch_def] >> METIS_TAC [agp32_Rel_ag32_ID_addr_correct,addrA_def]) >>
    fs [] >>
    `(FUNPOW Next (THE (I' (4,SUC t)) − 1) a).R ((22 >< 17) i) =
    (FUNPOW Next (THE (I' (4,SUC t))) a).R ((22 >< 17) i)`
      by METIS_TAC [reg_adr_update_isa_not_change_data] >> fs [] >>
    `THE (I' (2,SUC t)) = THE (I' (4,SUC t)) + 1`
      by METIS_TAC [EX_NONE_ID_instr_index_with_MEM_instr_plus_1] >> fs []) >-
   (`(agp32 fext fbits (SUC t)).R = (FUNPOW Next (THE (I' (4,SUC t)) − 1) a).R`
      by cheat >> fs [] >>
    `(agp32 fext fbits (SUC t)).ID.ID_addrA = (22 >< 17) i`
      by (fs [Abbr `i`,Abbr `s`,is_sch_def] >> METIS_TAC [agp32_Rel_ag32_ID_addr_correct,addrA_def]) >>
    fs [] >>
    `(FUNPOW Next (THE (I' (4,SUC t)) − 1) a).R ((22 >< 17) i) =
    (FUNPOW Next (THE (I' (4,SUC t))) a).R ((22 >< 17) i)`
      by METIS_TAC [reg_adr_update_isa_not_change_data] >> fs [] >>
    `THE (I' (2,SUC t)) = THE (I' (3,SUC t)) + 1`
      by METIS_TAC [ID_instr_index_with_EX_instr_plus_1] >> fs [] >>
    `(THE (I' (3,SUC t)) = THE (I' (4,SUC t))) \/ (THE (I' (3,SUC t)) = THE (I' (4,SUC t)) + 1)`
      by METIS_TAC [EX_instr_index_with_MEM_instr_plus_1] >> fs [] >>
    `THE (I' (4,SUC t)) = THE (I' (3,SUC t)) - 1` by fs [] >> fs [] >>
    METIS_TAC [reg_adr_update_isa_not_change_data]) >-
   (`(agp32 fext fbits (SUC t)).R = (FUNPOW Next (THE (I' (5,SUC t)) − 1) a).R`
      by cheat >> fs [] >>
    `(agp32 fext fbits (SUC t)).ID.ID_addrA = (22 >< 17) i`
      by (fs [Abbr `i`,Abbr `s`,is_sch_def] >>
          METIS_TAC [agp32_Rel_ag32_ID_addr_correct,addrA_def]) >> fs [] >>
    `(FUNPOW Next (THE (I' (5,SUC t)) − 1) a).R ((22 >< 17) i) =
    (FUNPOW Next (THE (I' (5,SUC t))) a).R ((22 >< 17) i)`
      by METIS_TAC [reg_adr_update_isa_not_change_data] >> fs [] >>
    `THE (I' (2,SUC t)) = THE (I' (5,SUC t)) + 1`
      by METIS_TAC [EX_MEM_NONE_ID_instr_index_with_WB_instr_plus_1] >> fs []) >>
  `s.WB.WB_state_flag` by fs [Abbr `s`,enable_stg_def,agp32_ID_ID_write_enable_WB_state_flag] >>
  `reg_data_vaild 5 s` by fs [Abbr `s`,reg_data_vaild_def] >>
  `(agp32 fext fbits (SUC t)).R = (FUNPOW Next (THE (I' (5,t))) a).R` by cheat >> fs [] >>
  cheat
QED


(* ID register data *)
Theorem agp32_Rel_ag32_ID_reg_data_Rel_correct:
  !fext fbits a t I.
    is_sch I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    enable_stg 2 (agp32 fext fbits t) ==>
    I (2,SUC t) <> NONE ==>
    ID_reg_data_Rel (agp32 fext fbits (SUC t)) a
                    (THE (I (2,SUC t))) (I (3,SUC t)) (I (4,SUC t)) (I (5,SUC t))
Proof
  rw [ID_reg_data_Rel_def] >>
  fs [agp32_Rel_ag32_ID_read_dataA_no_write_before] >>
  cheat
QED

val _ = export_theory ();
