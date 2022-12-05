open hardwarePreamble translatorTheory translatorLib arithmeticTheory wordsExtraTheory dep_rewrite blastLib bitstringSyntax fcpSyntax listSyntax wordsSyntax agp32StateTheory agp32EnvironmentTheory agp32ProcessorTheory ag32Theory ag32ExtraTheory ag32UtilitiesTheory agp32RelationTheory agp32UpdateTheory agp32InternalTheory agp32_MEM_Data_CorrectTheory;

(* correctness of WB stage items with respect to the ISA *)
val _ = new_theory "agp32_WB_Correct";

val _ = prefer_num ();
val _ = guess_lengths ();

(* lemmas for data_in *)
Theorem agp32_data_in_unchanged_init:
  !fext t.
    is_data_in fext ==>
    (fext t).data_in = (fext 0).data_in
Proof
  rw [is_data_in_def] >>
  Induct_on `t` >> fs []
QED

Theorem agp32_Rel_ag32_data_in_correct:
  !fext fbits t a.
    is_data_in fext ==>
    Init (fext 0) (agp32 fext fbits 0) a ==>
    (!n. (fext (SUC t)).data_in = (FUNPOW Next n a).data_in)
Proof
  rw [agp32_data_in_unchanged_init,Init_def] >>
  `a.data_in = (FUNPOW Next 0 a).data_in` by rw [] >>
  METIS_TAC [ag32_data_in_unchanged_all]
QED

Theorem agp32_Rel_ag32_data_in_WB:
  !fext fbits t a I.
    is_data_in fext ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    (fext (SUC t)).data_in = (FUNPOW Next (THE (I (5,SUC t)) - 1) a).data_in
Proof
  rw [is_data_in_def,Rel_def] >>
  METIS_TAC [ag32_data_in_unchanged_all]
QED




(** WB_PC **)
Theorem agp32_Rel_ag32_WB_PC_correct:
  !fext fbits a t I.
    is_sch_writeback I (agp32 fext fbits) ==>
    is_sch_disable I (agp32 fext fbits) ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (5,SUC t) <> NONE ==>
    (agp32 fext fbits (SUC t)).WB.WB_PC = (FUNPOW Next (THE (I (5,SUC t)) − 1) a).PC
Proof
  rw [] >> Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state] (fext t) s s` >>
  `(agp32 fext fbits (SUC t)).WB.WB_PC = (WB_pipeline (fext t) s s').WB.WB_PC`
    by fs [agp32_WB_PC_imm_addrW_updated_by_WB_pipeline] >> rw [] >>
  `(s'.WB.WB_state_flag = s.WB.WB_state_flag) /\ (s'.WB.WB_PC = s.WB.WB_PC)`
    by METIS_TAC [Abbr `s`,Abbr `s'`,agp32_same_WB_items_before_WB_pipeline] >>
  Cases_on `enable_stg 5 (agp32 fext fbits t)` >-
   (`I' (5,SUC t) = I' (4,t)` by fs [is_sch_writeback_def] >> fs [] >>
    `s'.WB.WB_state_flag` by fs [enable_stg_def,Abbr `s`] >>
    fs [WB_pipeline_def,Rel_def,MEM_Rel_def]) >>
  `I' (5,SUC t) = I' (5,t)` by fs [is_sch_disable_def] >>
  `~s'.WB.WB_state_flag` by fs [enable_stg_def,Abbr `s`] >>
  fs [WB_pipeline_def,Rel_def,WB_Rel_def]
QED

(** WB_addrW **)
Theorem agp32_Rel_ag32_WB_addrW_correct:
  !fext fbits a t I.
    is_sch_writeback I (agp32 fext fbits) ==>
    is_sch_disable I (agp32 fext fbits) ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (5,SUC t) <> NONE ==>
    (agp32 fext fbits (SUC t)).WB.WB_addrW = addrW (FUNPOW Next (THE (I (5,SUC t)) − 1) a)
Proof
  rw [] >> Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state] (fext t) s s` >>
  `(agp32 fext fbits (SUC t)).WB.WB_addrW = (WB_pipeline (fext t) s s').WB.WB_addrW`
    by fs [agp32_WB_PC_imm_addrW_updated_by_WB_pipeline] >> rw [] >>
  `(s'.WB.WB_state_flag = s.WB.WB_state_flag) /\ (s'.WB.WB_addrW = s.WB.WB_addrW)`
    by METIS_TAC [Abbr `s`,Abbr `s'`,agp32_same_WB_items_before_WB_pipeline] >>
  Cases_on `enable_stg 5 (agp32 fext fbits t)` >-
   (`I' (5,SUC t) = I' (4,t)` by fs [is_sch_writeback_def] >> fs [] >>
    `s'.WB.WB_state_flag` by fs [enable_stg_def,Abbr `s`] >>
    fs [WB_pipeline_def,Rel_def,MEM_Rel_def]) >>
  `I' (5,SUC t) = I' (5,t)` by fs [is_sch_disable_def] >>
  `~s'.WB.WB_state_flag` by fs [enable_stg_def,Abbr `s`] >>
  fs [WB_pipeline_def,Rel_def,WB_Rel_def]
QED

(** WB_opc **)
Theorem agp32_Rel_ag32_WB_opc_correct:
  !fext fbits a t I.
    is_sch_writeback I (agp32 fext fbits) ==>
    is_sch_disable I (agp32 fext fbits) ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (5,SUC t) <> NONE ==>
    (agp32 fext fbits (SUC t)).WB.WB_opc = opc (FUNPOW Next (THE (I (5,SUC t)) − 1) a)
Proof
  rw [] >> Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state] (fext t) s s` >>
  `(agp32 fext fbits (SUC t)).WB.WB_opc = (WB_pipeline (fext t) s s').WB.WB_opc`
    by fs [agp32_WB_opc_updated_by_WB_pipeline] >> rw [] >>
  `(s'.WB.WB_state_flag = s.WB.WB_state_flag) /\ (s'.WB.WB_opc = s.WB.WB_opc)`
    by METIS_TAC [Abbr `s`,Abbr `s'`,agp32_same_WB_items_before_WB_pipeline] >>
  Cases_on `enable_stg 5 (agp32 fext fbits t)` >-
   (`I' (5,SUC t) = I' (4,t)` by fs [is_sch_writeback_def] >> fs [] >>
    `s'.WB.WB_state_flag` by fs [enable_stg_def,Abbr `s`] >>
    fs [WB_pipeline_def,Rel_def,MEM_Rel_def]) >>
  `I' (5,SUC t) = I' (5,t)` by fs [is_sch_disable_def] >>
  `~s'.WB.WB_state_flag` by fs [enable_stg_def,Abbr `s`] >>
  fs [WB_pipeline_def,Rel_def,WB_Rel_def]
QED

(** WB_dataA **)
Theorem agp32_Rel_ag32_WB_dataA_correct:
  !fext fbits a t I.
    is_sch_writeback I (agp32 fext fbits) ==>
    is_sch_disable I (agp32 fext fbits) ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (5,SUC t) <> NONE ==>
    (agp32 fext fbits (SUC t)).WB.WB_dataA = dataA (FUNPOW Next (THE (I (5,SUC t)) − 1) a)
Proof
  rw [] >> Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state] (fext t) s s` >>
  `(agp32 fext fbits (SUC t)).WB.WB_dataA = (WB_pipeline (fext t) s s').WB.WB_dataA`
    by fs [agp32_WB_dataA_updated_by_WB_pipeline] >> rw [] >>
  `(s'.WB.WB_state_flag = s.WB.WB_state_flag) /\ (s'.WB.WB_dataA = s.WB.WB_dataA)`
    by METIS_TAC [Abbr `s`,Abbr `s'`,agp32_same_WB_items_before_WB_pipeline] >>
  Cases_on `enable_stg 5 (agp32 fext fbits t)` >-
   (`I' (5,SUC t) = I' (4,t)` by fs [is_sch_writeback_def] >> fs [] >>
    `s'.WB.WB_state_flag` by fs [enable_stg_def,Abbr `s`] >>
    fs [WB_pipeline_def,Rel_def,MEM_Rel_def]) >>
  `I' (5,SUC t) = I' (5,t)` by fs [is_sch_disable_def] >>
  `~s'.WB.WB_state_flag` by fs [enable_stg_def,Abbr `s`] >>
  fs [WB_pipeline_def,Rel_def,WB_Rel_def]
QED

(** WB_imm **)
(** when opc is not 14w **)
Theorem agp32_Rel_ag32_WB_imm_correct_not_LoadUpperConstant:
  !fext fbits a t I.
    is_sch_writeback I (agp32 fext fbits) ==>
    is_sch_disable I (agp32 fext fbits) ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (5,SUC t) <> NONE ==>
    (agp32 fext fbits (SUC t)).WB.WB_opc <> 14w ==>
    (agp32 fext fbits (SUC t)).WB.WB_imm = imm (FUNPOW Next (THE (I (5,SUC t)) − 1) a)
Proof
  rw [] >> Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state] (fext t) s s` >>
  `(agp32 fext fbits (SUC t)).WB.WB_opc = (WB_pipeline (fext t) s s').WB.WB_opc`
    by fs [agp32_WB_opc_updated_by_WB_pipeline] >>
  `(agp32 fext fbits (SUC t)).WB.WB_imm = (WB_pipeline (fext t) s s').WB.WB_imm`
    by fs [agp32_WB_PC_imm_addrW_updated_by_WB_pipeline] >> fs [] >>
  `(s'.WB.WB_state_flag = s.WB.WB_state_flag) /\ (s'.WB.WB_imm = s.WB.WB_imm) /\
  (s'.WB.WB_opc = s.WB.WB_opc)`
    by METIS_TAC [Abbr `s`,Abbr `s'`,agp32_same_WB_items_before_WB_pipeline] >>
  `s'.MEM.MEM_imm = s.MEM.MEM_imm`
    by METIS_TAC [Abbr `s`,Abbr `s'`,agp32_same_MEM_items_before_WB_pipeline] >>
  Cases_on `enable_stg 5 (agp32 fext fbits t)` >-
   (`I' (5,SUC t) = I' (4,t)` by fs [is_sch_writeback_def] >> fs [] >>
    `s'.WB.WB_state_flag` by fs [enable_stg_def,Abbr `s`] >>
    fs [WB_pipeline_def,Rel_def,MEM_Rel_def]) >>
  `I' (5,SUC t) = I' (5,t)` by fs [is_sch_disable_def] >>
  `~s'.WB.WB_state_flag` by fs [enable_stg_def,Abbr `s`] >>
  fs [WB_pipeline_def,Rel_def,WB_Rel_def]
QED

(** when opc is 14w **)
Theorem agp32_Rel_ag32_WB_imm_correct_LoadUpperConstant:
  !fext fbits a t I.
    is_sch_writeback I (agp32 fext fbits) ==>
    is_sch_disable I (agp32 fext fbits) ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (5,SUC t) <> NONE ==>
    (agp32 fext fbits (SUC t)).WB.WB_opc = 14w ==>
    (agp32 fext fbits (SUC t)).WB.WB_imm =
    ((8 >< 0) (imm (FUNPOW Next (THE (I (5,SUC t)) − 1) a)) @@
     (22 >< 0) (dataW (FUNPOW Next (THE (I (5,SUC t)) − 1) a)))
Proof
  rw [] >> Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state] (fext t) s s` >>
  `(agp32 fext fbits (SUC t)).WB.WB_opc = (WB_pipeline (fext t) s s').WB.WB_opc`
    by fs [agp32_WB_opc_updated_by_WB_pipeline] >>
  `(agp32 fext fbits (SUC t)).WB.WB_imm = (WB_pipeline (fext t) s s').WB.WB_imm`
    by fs [agp32_WB_PC_imm_addrW_updated_by_WB_pipeline] >> fs [] >>
  `(s'.WB.WB_state_flag = s.WB.WB_state_flag) /\ (s'.WB.WB_imm = s.WB.WB_imm) /\
  (s'.WB.WB_opc = s.WB.WB_opc)`
    by METIS_TAC [Abbr `s`,Abbr `s'`,agp32_same_WB_items_before_WB_pipeline] >>
  `s'.MEM.MEM_imm = s.MEM.MEM_imm`
    by METIS_TAC [Abbr `s`,Abbr `s'`,agp32_same_MEM_items_before_WB_pipeline] >>
  Cases_on `enable_stg 5 (agp32 fext fbits t)` >-
   (`I' (5,SUC t) = I' (4,t)` by fs [is_sch_writeback_def] >> fs [] >>
    `s'.WB.WB_state_flag` by fs [enable_stg_def,Abbr `s`] >>
    fs [WB_pipeline_def,Rel_def,MEM_Rel_def]) >>
  `I' (5,SUC t) = I' (5,t)` by fs [is_sch_disable_def] >>
  `~s'.WB.WB_state_flag` by fs [enable_stg_def,Abbr `s`] >>
  fs [WB_pipeline_def,Rel_def,WB_Rel_def]
QED

(** WB_ALU_res **)
Theorem agp32_Rel_ag32_WB_ALU_res_correct:
  !fext fbits a t I.
    is_sch_writeback I (agp32 fext fbits) ==>
    is_sch_disable I (agp32 fext fbits) ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (5,SUC t) <> NONE ==>
    (agp32 fext fbits (SUC t)).WB.WB_ALU_res = ALU_res (FUNPOW Next (THE (I (5,SUC t)) − 1) a)
Proof
  rw [] >> Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state] (fext t) s s` >>
  `(agp32 fext fbits (SUC t)).WB.WB_ALU_res = (WB_pipeline (fext t) s s').WB.WB_ALU_res`
    by fs [agp32_WB_ALU_res_updated_by_WB_pipeline] >> rw [] >>
  `(s'.WB.WB_state_flag = s.WB.WB_state_flag) /\ (s'.WB.WB_ALU_res = s.WB.WB_ALU_res)`
    by METIS_TAC [Abbr `s`,Abbr `s'`,agp32_same_WB_items_before_WB_pipeline] >>
  Cases_on `enable_stg 5 (agp32 fext fbits t)` >-
   (`I' (5,SUC t) = I' (4,t)` by fs [is_sch_writeback_def] >> fs [] >>
    `s'.WB.WB_state_flag` by fs [enable_stg_def,Abbr `s`] >>
    fs [WB_pipeline_def,Rel_def,MEM_Rel_def]) >>
  `I' (5,SUC t) = I' (5,t)` by fs [is_sch_disable_def] >>
  `~s'.WB.WB_state_flag` by fs [enable_stg_def,Abbr `s`] >>
  fs [WB_pipeline_def,Rel_def,WB_Rel_def]
QED

(** WB_SHIFT_res **)
Theorem agp32_Rel_ag32_WB_SHIFT_res_correct:
  !fext fbits a t I.
    is_sch_writeback I (agp32 fext fbits) ==>
    is_sch_disable I (agp32 fext fbits) ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (5,SUC t) <> NONE ==>
    (agp32 fext fbits (SUC t)).WB.WB_opc = 1w ==>
    (agp32 fext fbits (SUC t)).WB.WB_SHIFT_res = shift_res (FUNPOW Next (THE (I (5,SUC t)) − 1) a)
Proof
  rw [] >> Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state] (fext t) s s` >>
  `(agp32 fext fbits (SUC t)).WB.WB_opc = (WB_pipeline (fext t) s s').WB.WB_opc`
    by fs [agp32_WB_opc_updated_by_WB_pipeline] >>
  `(agp32 fext fbits (SUC t)).WB.WB_SHIFT_res = (WB_pipeline (fext t) s s').WB.WB_SHIFT_res`
    by fs [agp32_WB_SHIFT_res_updated_by_WB_pipeline] >> fs [] >>
  `(s'.WB.WB_state_flag = s.WB.WB_state_flag) /\ (s'.WB.WB_SHIFT_res = s.WB.WB_SHIFT_res) /\
  (s'.WB.WB_opc = s.WB.WB_opc)`
    by METIS_TAC [Abbr `s`,Abbr `s'`,agp32_same_WB_items_before_WB_pipeline] >>
  Cases_on `enable_stg 5 (agp32 fext fbits t)` >-
   (`I' (5,SUC t) = I' (4,t)` by fs [is_sch_writeback_def] >> fs [] >>
    `s'.WB.WB_state_flag` by fs [enable_stg_def,Abbr `s`] >>
    fs [WB_pipeline_def,Rel_def,MEM_Rel_def]) >>
  `I' (5,SUC t) = I' (5,t)` by fs [is_sch_disable_def] >>
  `~s'.WB.WB_state_flag` by fs [enable_stg_def,Abbr `s`] >>
  fs [WB_pipeline_def,Rel_def,WB_Rel_def]
QED

(** WB_write_reg **)
Theorem agp32_Rel_ag32_WB_write_reg_correct:
  !fext fbits a t I.
    is_sch_writeback I (agp32 fext fbits) ==>
    is_sch_disable I (agp32 fext fbits) ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (5,SUC t) <> NONE ==>
    (agp32 fext fbits (SUC t)).WB.WB_write_reg = reg_iswrite (FUNPOW Next (THE (I (5,SUC t)) − 1) a)
Proof
  rw [] >> Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state] (fext t) s s` >>
  `(agp32 fext fbits (SUC t)).WB.WB_write_reg = (WB_pipeline (fext t) s s').WB.WB_write_reg`
    by fs [agp32_WB_write_reg_updated_by_WB_pipeline] >> fs [] >>
  `(s'.WB.WB_state_flag = s.WB.WB_state_flag) /\ (s'.WB.WB_write_reg = s.WB.WB_write_reg)`
    by METIS_TAC [Abbr `s`,Abbr `s'`,agp32_same_WB_items_before_WB_pipeline] >>
  `s'.MEM.MEM_opc = s.MEM.MEM_opc`
    by METIS_TAC [Abbr `s`,Abbr `s'`,agp32_same_MEM_items_before_WB_pipeline] >>
  Cases_on `enable_stg 5 (agp32 fext fbits t)` >-
   (`I' (5,SUC t) = I' (4,t)` by fs [is_sch_writeback_def] >> fs [] >>
    `s'.WB.WB_state_flag` by fs [enable_stg_def,Abbr `s`] >>
    fs [WB_pipeline_def,Rel_def,MEM_Rel_def,reg_iswrite_def]) >>
  `I' (5,SUC t) = I' (5,t)` by fs [is_sch_disable_def] >>
  `~s'.WB.WB_state_flag` by fs [enable_stg_def,Abbr `s`] >>
  fs [WB_pipeline_def,Rel_def,WB_Rel_def]
QED

(** WB_read_data **)
Theorem agp32_Rel_ag32_WB_read_data_correct:
  !fext fbits a t I.
    is_mem fext_accessor_circuit (agp32 fext fbits) fext ==>
    is_sch I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (5,SUC t) <> NONE ==>
    (fext (SUC t)).ready ==>
    (agp32 fext fbits (SUC t)).WB.WB_opc = 4w ==>
    (agp32 fext fbits (SUC t)).WB.WB_read_data = mem_data_rdata (FUNPOW Next (THE (I (5,SUC t)) − 1) a)
Proof
  rw [] >> Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state; WB_pipeline; MEM_pipeline; EX_pipeline;
                            REG_write; ID_pipeline; IF_PC_update; Acc_compute] (fext t) s s` >>
  Q.ABBREV_TAC `s'' = procs [IF_instr_update; ID_opc_func_update; ID_imm_update; ID_data_update;
                             ID_data_check_update; EX_ALU_input_imm_update; EX_ALU_update;
                             EX_SHIFT_update; EX_jump_sel_addr_update; IF_PC_input_update;
                             MEM_ctrl_update] (fext (SUC t)) s' s'` >>
  `(agp32 fext fbits (SUC t)).WB.WB_read_data = (WB_update (fext (SUC t)) s' s'').WB.WB_read_data`
    by fs [agp32_WB_ctrl_items_updated_by_WB_update] >>
  fs [WB_update_def] >>
  IF_CASES_TAC >> fs [] >>
  METIS_TAC [agp32_Rel_ag32_read_mem_data_rdata_correct]
QED

(** WB_read_data_byte **)
Theorem agp32_Rel_ag32_WB_read_data_byte_correct:
  !fext fbits a t I.
    is_mem fext_accessor_circuit (agp32 fext fbits) fext ==>
    is_sch I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (5,SUC t) <> NONE ==>
    (fext (SUC t)).ready ==>
    (agp32 fext fbits (SUC t)).WB.WB_opc = 5w ==>
    (agp32 fext fbits (SUC t)).WB.WB_read_data_byte =
    mem_data_rdata (FUNPOW Next (THE (I (5,SUC t)) − 1) a)
Proof
  rw [] >> Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state; WB_pipeline; MEM_pipeline; EX_pipeline;
                            REG_write; ID_pipeline; IF_PC_update; Acc_compute] (fext t) s s` >>
  Q.ABBREV_TAC `s'' = procs [IF_instr_update; ID_opc_func_update; ID_imm_update; ID_data_update;
                             ID_data_check_update; EX_ALU_input_imm_update; EX_ALU_update;
                             EX_SHIFT_update; EX_jump_sel_addr_update; IF_PC_input_update;
                             MEM_ctrl_update] (fext (SUC t)) s' s'` >>
  `(agp32 fext fbits (SUC t)).WB.WB_read_data_byte =
  (WB_update (fext (SUC t)) s' s'').WB.WB_read_data_byte`
    by fs [agp32_WB_ctrl_items_updated_by_WB_update] >>
  `s''.WB.WB_dataA = (agp32 fext fbits (SUC t)).WB.WB_dataA`
    by METIS_TAC [agp32_same_WB_items_before_WB_update,Abbr `s`,Abbr `s'`,Abbr `s''`] >>
  `(agp32 fext fbits (SUC t)).WB.WB_dataA = dataA (FUNPOW Next (THE (I' (5,SUC t)) − 1) a)`
    by gs [is_sch_def,agp32_Rel_ag32_WB_dataA_correct] >>
  fs [WB_update_def] >>
  IF_CASES_TAC >> fs [MUX_41_def] >>
  `opc (FUNPOW Next (THE (I' (5,SUC t)) − 1) a) = 5w`
    by METIS_TAC [is_sch_def,agp32_Rel_ag32_WB_opc_correct] >>
  `(fext (SUC t)).data_rdata = mem_data_rdata_extra (FUNPOW Next (THE (I' (5,SUC t)) − 1) a)`
    by METIS_TAC [agp32_Rel_ag32_read_mem_byte_data_rdata_correct] >>
  rw [mem_data_rdata_def,mem_data_rdata_extra_def,mem_data_addr_def] >>
  qpat_abbrev_tac `a1 = FUNPOW Next _ a` >>
  fs [word_at_addr_def,align_addr_def,addr_add] >>
  Cases_on_word_value `(1 >< 0) (dataA a1)` >>
  `dataA a1 = (31 >< 2) (dataA a1) @@ (1 >< 0) (dataA a1)` by rw [addr_split] >> gs [] >>
  FULL_SIMP_TAC (std_ss++WORD_ss++WORD_EXTRACT_ss) [] >> METIS_TAC []                       
QED

(** WB_isOut **)
Theorem agp32_Rel_ag32_WB_isOut_correct:
  !fext fbits a t I.
    is_sch_writeback I (agp32 fext fbits) ==>
    is_sch_disable I (agp32 fext fbits) ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (5,SUC t) <> NONE ==>
    ((agp32 fext fbits (SUC t)).WB.WB_isOut <=> isOut_isa (FUNPOW Next (THE (I (5,SUC t)) − 1) a))
Proof
  rw [] >> Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state; WB_pipeline; MEM_pipeline; EX_pipeline;
                            REG_write; ID_pipeline; IF_PC_update; Acc_compute] (fext t) s s` >>
  Q.ABBREV_TAC `s'' = procs [IF_instr_update; ID_opc_func_update; ID_imm_update; ID_data_update;
                             ID_data_check_update; EX_ALU_input_imm_update; EX_ALU_update;
                             EX_SHIFT_update; EX_jump_sel_addr_update; IF_PC_input_update;
                             MEM_ctrl_update] (fext (SUC t)) s' s'` >>
  `(agp32 fext fbits (SUC t)).WB.WB_isOut = (WB_update (fext (SUC t)) s' s'').WB.WB_isOut`
    by fs [agp32_WB_ctrl_items_updated_by_WB_update] >>
  `s''.WB.WB_opc = (agp32 fext fbits (SUC t)).WB.WB_opc`
    by METIS_TAC [agp32_same_WB_items_before_WB_update,Abbr `s`,Abbr `s'`,Abbr `s''`] >>
  `(s''.WB.WB_state_flag = (agp32 fext fbits t).WB.WB_state_flag) /\
  (s''.WB.WB_isOut = s.WB.WB_isOut)`
    by METIS_TAC [agp32_same_WB_items_until_WB_update,Abbr `s`,Abbr `s'`,Abbr `s''`] >>
  fs [WB_update_def] >>
  IF_CASES_TAC >> fs [] >-
   (rw [isOut_isa_def] >> METIS_TAC [agp32_Rel_ag32_WB_opc_correct]) >>
  `I' (5,SUC t) = I' (5,t)` by fs [is_sch_disable_def,enable_stg_def] >>
  fs [Rel_def,WB_Rel_def]
QED

(** WB_data_sel **)
Theorem agp32_Rel_ag32_WB_data_sel_correct:
  !fext fbits a t I.
    is_sch_writeback I (agp32 fext fbits) ==>
    is_sch_disable I (agp32 fext fbits) ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (5,SUC t) <> NONE ==>
    (agp32 fext fbits (SUC t)).WB.WB_data_sel = reg_wdata_sel (FUNPOW Next (THE (I (5,SUC t)) − 1) a)
Proof
  rw [] >> Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state; WB_pipeline; MEM_pipeline; EX_pipeline;
                            REG_write; ID_pipeline; IF_PC_update; Acc_compute] (fext t) s s` >>
  Q.ABBREV_TAC `s'' = procs [IF_instr_update; ID_opc_func_update; ID_imm_update; ID_data_update;
                             ID_data_check_update; EX_ALU_input_imm_update; EX_ALU_update;
                             EX_SHIFT_update; EX_jump_sel_addr_update; IF_PC_input_update;
                             MEM_ctrl_update] (fext (SUC t)) s' s'` >>
  `(agp32 fext fbits (SUC t)).WB.WB_data_sel = (WB_update (fext (SUC t)) s' s'').WB.WB_data_sel`
    by fs [agp32_WB_ctrl_items_updated_by_WB_update] >>
  `s''.WB.WB_opc = (agp32 fext fbits (SUC t)).WB.WB_opc`
    by METIS_TAC [agp32_same_WB_items_before_WB_update,Abbr `s`,Abbr `s'`,Abbr `s''`] >>
  `(s''.WB.WB_state_flag = (agp32 fext fbits t).WB.WB_state_flag) /\
  (s''.WB.WB_data_sel = s.WB.WB_data_sel)`
    by METIS_TAC [agp32_same_WB_items_until_WB_update,Abbr `s`,Abbr `s'`,Abbr `s''`] >>
  fs [WB_update_def] >>
  IF_CASES_TAC >> fs [] >-
   (simp [reg_wdata_sel_def] >> METIS_TAC [agp32_Rel_ag32_WB_opc_correct]) >>
  `I' (5,SUC t) = I' (5,t)` by fs [is_sch_disable_def,enable_stg_def] >>
  fs [Rel_def,WB_Rel_def]
QED

(** WB_write_data **)
Theorem agp32_Rel_ag32_WB_write_data_correct:
  !fext fbits a t I.
    is_mem fext_accessor_circuit (agp32 fext fbits) fext ==>
    is_sch I (agp32 fext fbits) a ==>
    is_data_in fext ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (5,SUC t) <> NONE ==>
    (agp32 fext fbits (SUC t)).WB.WB_state_flag ==>
    (agp32 fext fbits (SUC t)).WB.WB_write_data = reg_wdata (FUNPOW Next (THE (I (5,SUC t)) − 1) a)
Proof
  rw [agp32_WB_write_data_rewrite_SUC_t] >>
  `(agp32 fext fbits (SUC t)).WB.WB_data_sel = reg_wdata_sel (FUNPOW Next (THE (I' (5,SUC t)) − 1) a)`
    by gs [is_sch_def,agp32_Rel_ag32_WB_data_sel_correct] >> fs [] >>
  fs [MUX_81_def,reg_wdata_def] >>
  IF_CASES_TAC >> fs [] >-
   gs [is_sch_def,agp32_Rel_ag32_WB_ALU_res_correct] >>
  IF_CASES_TAC >> fs [] >-
   (fs [reg_wdata_sel_def] >>
    Cases_on_word_value `opc (FUNPOW Next (THE (I' (5,SUC t)) − 1) a)` >> fs [] >>
    `(agp32 fext fbits (SUC t)).WB.WB_opc = 1w`
      by METIS_TAC [is_sch_def,agp32_Rel_ag32_WB_opc_correct] >>
    gs [is_sch_def,agp32_Rel_ag32_WB_SHIFT_res_correct]) >>
  IF_CASES_TAC >> fs [] >-
   METIS_TAC [agp32_Rel_ag32_data_in_WB] >>
  IF_CASES_TAC >> fs [] >-
   gs [is_sch_def,agp32_Rel_ag32_WB_PC_correct] >>
  IF_CASES_TAC >> fs [] >- 
   (rw [imm_updated_def] >>
    `(agp32 fext fbits (SUC t)).WB.WB_opc = opc (FUNPOW Next (THE (I' (5,SUC t)) − 1) a)`
      by gs [is_sch_def,agp32_Rel_ag32_WB_opc_correct] >-
     (`(agp32 fext fbits (SUC t)).WB.WB_opc <> 14w` by fs [] >>
      gs [is_sch_def,agp32_Rel_ag32_WB_imm_correct_not_LoadUpperConstant]) >-
     gs [is_sch_def,agp32_Rel_ag32_WB_imm_correct_LoadUpperConstant] >>
    fs [reg_wdata_sel_def] >>
    Cases_on_word_value `opc (FUNPOW Next (THE (I' (5,SUC t)) − 1) a)` >> fs []) >>
  IF_CASES_TAC >> fs [] >-
   (`(fext (SUC t)).ready` by METIS_TAC [agp32_WB_state_flag_and_fext_ready] >>
    fs [reg_wdata_sel_def] >>
    Cases_on_word_value `opc (FUNPOW Next (THE (I' (5,SUC t)) − 1) a)` >> fs [] >>
    `(agp32 fext fbits (SUC t)).WB.WB_opc = 4w`
      by METIS_TAC [is_sch_def,agp32_Rel_ag32_WB_opc_correct] >>
    gs [agp32_Rel_ag32_WB_read_data_correct]) >>
  IF_CASES_TAC >> fs [] >-
   (`(fext (SUC t)).ready` by METIS_TAC [agp32_WB_state_flag_and_fext_ready] >>
    fs [reg_wdata_sel_def] >>
    Cases_on_word_value `opc (FUNPOW Next (THE (I' (5,SUC t)) − 1) a)` >> fs [] >>
    `(agp32 fext fbits (SUC t)).WB.WB_opc = 5w`
      by METIS_TAC [is_sch_def,agp32_Rel_ag32_WB_opc_correct] >>
    gs [agp32_Rel_ag32_WB_read_data_byte_correct]) >>
  IF_CASES_TAC >> fs [] >-
   (fs [reg_wdata_sel_def] >>
    Cases_on_word_value `opc (FUNPOW Next (THE (I' (5,SUC t)) − 1) a)` >> fs [] >>
    `(agp32 fext fbits (SUC t)).WB.WB_opc = 8w`
      by METIS_TAC [is_sch_def,agp32_Rel_ag32_WB_opc_correct] >>
    gs [agp32_Rel_ag32_acc_res_correct]) >>
  Cases_on_word_value `reg_wdata_sel (FUNPOW Next (THE (I' (5,SUC t)) − 1) a)` >> fs []
QED


(* WB_Rel *)
Theorem agp32_Rel_ag32_WB_Rel_correct:
  !fext fbits a t I.
    is_mem fext_accessor_circuit (agp32 fext fbits) fext ==>
    is_sch I (agp32 fext fbits) a ==>
    is_data_in fext ==>
    Init (fext 0) (agp32 fext fbits 0) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (5,SUC t) <> NONE ==>
    WB_Rel (fext (SUC t)) (agp32 fext fbits (SUC t)) a (THE (I (5,SUC t)))
Proof
  rw [WB_Rel_def] >>
  fs [is_sch_def,agp32_Rel_ag32_WB_PC_correct,
      agp32_Rel_ag32_WB_addrW_correct,agp32_Rel_ag32_WB_opc_correct,
      agp32_Rel_ag32_WB_dataA_correct,agp32_Rel_ag32_WB_imm_correct_not_LoadUpperConstant,
      agp32_Rel_ag32_WB_imm_correct_LoadUpperConstant,agp32_Rel_ag32_WB_ALU_res_correct,
      agp32_Rel_ag32_WB_SHIFT_res_correct,agp32_Rel_ag32_WB_write_reg_correct,
      agp32_Rel_ag32_WB_read_data_correct,agp32_Rel_ag32_WB_read_data_byte_correct,
      agp32_Rel_ag32_WB_isOut_correct,agp32_Rel_ag32_WB_data_sel_correct,
      agp32_Rel_ag32_WB_write_data_correct]
QED


(* registers R updated by WB stage *)
Theorem agp32_Rel_ag32_R_correct_WB_t:
  !fext fbits a t I.
    is_sch I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (5,t) <> NONE ==>
    wb_data_vaild (agp32 fext fbits t) ==>
    (agp32 fext fbits (SUC t)).R = (FUNPOW Next (THE (I (5,t))) a).R
Proof
  rw [wb_data_vaild_def] >> Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state;WB_pipeline;MEM_pipeline;EX_pipeline] (fext t) s s` >>
  `(agp32 fext fbits (SUC t)).R = (REG_write (fext t) s s').R`
    by fs [agp32_R_updated_by_REG_write] >>
  `(s'.R = s.R) /\ (s'.WB.WB_state_flag <=> s.WB.WB_state_flag) /\
  (s'.WB.WB_write_data = s.WB.WB_write_data)` by cheat >> fs [REG_write_def] >>
  Cases_on `s.WB.WB_write_reg` >> fs [] >-
   (Cases_on `I' (5,t-1) = NONE` >> fs [] >-
     (`s.R = (FUNPOW Next (THE (I' (5,t)) - 1) a).R` by fs [Rel_def] >>
      `(s.WB.WB_addrW = addrW (FUNPOW Next (THE (I' (5,t)) - 1) a)) /\
      (s.WB.WB_write_data = reg_wdata (FUNPOW Next (THE (I' (5,t)) - 1) a)) /\
      (reg_iswrite (FUNPOW Next (THE (I' (5,t)) - 1) a))`
        by fs [Rel_def,WB_Rel_def] >> rw [] >>
      `THE (I' (5,t)) <> 0` by METIS_TAC [WB_instr_index_not_0] >>
      `THE (I' (5,t)) = SUC (THE (I' (5,t)) − 1)` by fs [] >>
      `(FUNPOW Next (THE (I' (5,t))) a).R =
      (FUNPOW Next (SUC (THE (I' (5,t)) - 1)) a).R` by METIS_TAC [] >>
      rw [FUNPOW_SUC] >>
      qpat_abbrev_tac `a0 = FUNPOW Next _ _` >> cheat) >>
    fs [] >>
    cheat (** I (5,t) = I (5,t-1) + 1 ? **)) >>
  Cases_on `I' (5,t-1) = NONE` >> fs [] >-
   (`s.R = (FUNPOW Next (THE (I' (5,t)) - 1) a).R` by cheat >> rw [] >>
    `THE (I' (5,t)) <> 0` by cheat >>
    `THE (I' (5,t)) = SUC (THE (I' (5,t)) − 1)` by fs [] >>
    `(FUNPOW Next (THE (I' (5,t))) a).R =
    (FUNPOW Next (SUC (THE (I' (5,t)) - 1)) a).R` by METIS_TAC [] >>
    rw [FUNPOW_SUC] >>
    qpat_abbrev_tac `a0 = FUNPOW Next _ _` >> cheat) >>
  fs [] >> cheat
QED

val _ = export_theory ();
