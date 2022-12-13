open hardwarePreamble translatorTheory translatorLib arithmeticTheory pred_setTheory wordsExtraTheory dep_rewrite blastLib bitstringSyntax fcpSyntax listSyntax wordsSyntax agp32StateTheory agp32EnvironmentTheory agp32ProcessorTheory ag32Theory ag32ExtraTheory ag32UtilitiesTheory agp32RelationTheory agp32UpdateTheory agp32InternalTheory agp32StepLib;

(* correctness of MEM stage items with respect to the ISA *)
val _ = new_theory "agp32_MEM_Correct";

val _ = prefer_num ();
val _ = guess_lengths ();


(** MEM_PC **)
Theorem agp32_Rel_ag32_MEM_PC_correct:
  !fext fbits a t I.
    is_sch_memory I (agp32 fext fbits) a ==>
    is_sch_disable I (agp32 fext fbits) ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (4,SUC t) <> NONE ==>
    (agp32 fext fbits (SUC t)).MEM.MEM_PC = (FUNPOW Next (THE (I (4,SUC t)) − 1) a).PC
Proof
  rw [] >> Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state;WB_pipeline] (fext t) s s` >>
  `(agp32 fext fbits (SUC t)).MEM.MEM_PC = (MEM_pipeline (fext t) s s').MEM.MEM_PC`
    by fs [agp32_MEM_PC_imm_addrW_updated_by_MEM_pipeline] >> rw [] >>
  `(s'.MEM.MEM_state_flag = s.MEM.MEM_state_flag) /\ (s'.MEM.MEM_PC = s.MEM.MEM_PC)`
    by METIS_TAC [Abbr `s`,Abbr `s'`,agp32_same_items_before_MEM_pipeline] >>
  Cases_on `enable_stg 4 (agp32 fext fbits t)` >-
   (fs [is_sch_memory_def] >>
    Cases_on `isMemOp_hw_op (agp32 fext fbits t)` >-
     METIS_TAC [] >>
    `I' (4,SUC t) = I' (3,t)` by fs [] >> fs [] >>
    `s'.MEM.MEM_state_flag` by fs [enable_stg_def,Abbr `s`] >>
    rw [MEM_pipeline_def] >> fs [Rel_def,EX_Rel_def]) >>
  `I' (4,SUC t) = I' (4,t)` by fs [is_sch_disable_def] >>
  `~s'.MEM.MEM_state_flag` by fs [enable_stg_def,Abbr `s`] >>
  rw [MEM_pipeline_def] >>
  fs [Rel_def,MEM_Rel_def]
QED

(** MEM_addrW **)
Theorem agp32_Rel_ag32_MEM_addrW_correct:
  !fext fbits a t I.
    is_sch_memory I (agp32 fext fbits) a ==>
    is_sch_disable I (agp32 fext fbits) ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (4,SUC t) <> NONE ==>
    (agp32 fext fbits (SUC t)).MEM.MEM_addrW = addrW (FUNPOW Next (THE (I (4,SUC t)) − 1) a)
Proof
  rw [] >> Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state;WB_pipeline] (fext t) s s` >>
  `(agp32 fext fbits (SUC t)).MEM.MEM_addrW = (MEM_pipeline (fext t) s s').MEM.MEM_addrW`
    by fs [agp32_MEM_PC_imm_addrW_updated_by_MEM_pipeline] >> rw [] >>
  `(s'.MEM.MEM_state_flag = s.MEM.MEM_state_flag) /\ (s'.MEM.MEM_addrW = s.MEM.MEM_addrW)`
    by METIS_TAC [Abbr `s`,Abbr `s'`,agp32_same_items_before_MEM_pipeline] >>
  Cases_on `enable_stg 4 (agp32 fext fbits t)` >-
   (fs [is_sch_memory_def] >>
    Cases_on `isMemOp_hw_op (agp32 fext fbits t)` >-
     METIS_TAC [] >>
    `I' (4,SUC t) = I' (3,t)` by fs [] >> fs [] >>
    `s'.MEM.MEM_state_flag` by fs [enable_stg_def,Abbr `s`] >>
    rw [MEM_pipeline_def] >> fs [Rel_def,EX_Rel_def]) >>
  `I' (4,SUC t) = I' (4,t)` by fs [is_sch_disable_def] >>
  `~s'.MEM.MEM_state_flag` by fs [enable_stg_def,Abbr `s`] >>
  rw [MEM_pipeline_def] >>
  fs [Rel_def,MEM_Rel_def]
QED

(** MEM_data **)
Theorem agp32_Rel_ag32_MEM_data_correct:
  !fext fbits a t I.
    is_sch_memory I (agp32 fext fbits) a ==>
    is_sch_disable I (agp32 fext fbits) ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (4,SUC t) <> NONE ==>
    ((agp32 fext fbits (SUC t)).MEM.MEM_dataA = dataA (FUNPOW Next (THE (I (4,SUC t)) − 1) a)) /\
    ((agp32 fext fbits (SUC t)).MEM.MEM_dataB = dataB (FUNPOW Next (THE (I (4,SUC t)) − 1) a))
Proof
  rpt gen_tac >> rpt disch_tac >>
  Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state;WB_pipeline] (fext t) s s` >>
  `(agp32 fext fbits (SUC t)).MEM.MEM_dataA = (MEM_pipeline (fext t) s s').MEM.MEM_dataA /\
  (agp32 fext fbits (SUC t)).MEM.MEM_dataB = (MEM_pipeline (fext t) s s').MEM.MEM_dataB`
    by fs [agp32_MEM_data_updated_by_MEM_pipeline] >> fs [] >>
  `(s'.MEM.MEM_state_flag = s.MEM.MEM_state_flag) /\
  (s'.MEM.MEM_dataA = s.MEM.MEM_dataA) /\ (s'.MEM.MEM_dataB = s.MEM.MEM_dataB)`
    by METIS_TAC [Abbr `s`,Abbr `s'`,agp32_same_items_before_MEM_pipeline] >>
  Cases_on `enable_stg 4 (agp32 fext fbits t)` >-
   (fs [is_sch_memory_def] >>
    Cases_on `isMemOp_hw_op (agp32 fext fbits t)` >-
     METIS_TAC [] >>
    `I' (4,SUC t) = I' (3,t)` by fs [] >> fs [] >>
    `s'.MEM.MEM_state_flag` by fs [enable_stg_def,Abbr `s`] >>
    fs [MEM_pipeline_def,Rel_def,EX_Rel_def]) >>
  `I' (4,SUC t) = I' (4,t)` by fs [is_sch_disable_def] >>
  `~s'.MEM.MEM_state_flag` by fs [enable_stg_def,Abbr `s`] >>
  rw [MEM_pipeline_def] >>
  fs [Rel_def,MEM_Rel_def]
QED

(** MEM_opc **)
Theorem agp32_Rel_ag32_MEM_opc_correct:
  !fext fbits a t I.
    is_sch_memory I (agp32 fext fbits) a ==>
    is_sch_disable I (agp32 fext fbits) ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (4,SUC t) <> NONE ==>
    (agp32 fext fbits (SUC t)).MEM.MEM_opc = opc (FUNPOW Next (THE (I (4,SUC t)) − 1) a)
Proof
  rw [] >> Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state;WB_pipeline] (fext t) s s` >>
  `(agp32 fext fbits (SUC t)).MEM.MEM_opc = (MEM_pipeline (fext t) s s').MEM.MEM_opc`
    by fs [agp32_MEM_opc_updated_by_MEM_pipeline] >> fs [] >>
  `(s'.MEM.MEM_state_flag = s.MEM.MEM_state_flag) /\
  (s'.MEM.MEM_opc = s.MEM.MEM_opc) /\ (s'.MEM.MEM_NOP_flag = s.MEM.MEM_NOP_flag)`
    by METIS_TAC [Abbr `s`,Abbr `s'`,agp32_same_items_before_MEM_pipeline] >>
  Cases_on `enable_stg 4 (agp32 fext fbits t)` >-
   (fs [is_sch_memory_def] >>
    Cases_on `isMemOp_hw_op (agp32 fext fbits t)` >-
     METIS_TAC [] >>
    `I' (4,SUC t) = I' (3,t)` by fs [] >> fs [] >>
    `s'.MEM.MEM_state_flag` by fs [enable_stg_def,Abbr `s`] >>
    `~s.MEM.MEM_NOP_flag`
      by fs [enable_stg_def,Abbr `s`,agp32_MEM_state_flag_not_isMemOp_hw_op_MEM_NOP_flag_F] >>
    fs [MEM_pipeline_def,Rel_def,EX_Rel_def]) >>
  `I' (4,SUC t) = I' (4,t)` by fs [is_sch_disable_def] >>
  `~s'.MEM.MEM_state_flag` by fs [enable_stg_def,Abbr `s`] >>
  rw [MEM_pipeline_def] >>
  fs [Rel_def,MEM_Rel_def]
QED

(** MEM_imm **)
(** when opc is not 14w **)
Theorem agp32_Rel_ag32_MEM_imm_correct_not_LoadUpperConstant:
  !fext fbits a t I.
    is_sch_memory I (agp32 fext fbits) a ==>
    is_sch_disable I (agp32 fext fbits) ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (4,SUC t) <> NONE ==>
    (agp32 fext fbits (SUC t)).MEM.MEM_opc <> 14w ==>
    (agp32 fext fbits (SUC t)).MEM.MEM_imm = imm (FUNPOW Next (THE (I (4,SUC t)) − 1) a)
Proof
  rw [] >> Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state;WB_pipeline] (fext t) s s` >>
  `(agp32 fext fbits (SUC t)).MEM.MEM_opc = (MEM_pipeline (fext t) s s').MEM.MEM_opc`
    by fs [agp32_MEM_opc_updated_by_MEM_pipeline] >>
  `(agp32 fext fbits (SUC t)).MEM.MEM_imm = (MEM_pipeline (fext t) s s').MEM.MEM_imm`
    by fs [agp32_MEM_PC_imm_addrW_updated_by_MEM_pipeline] >> fs [] >>
  `(s'.MEM.MEM_state_flag = s.MEM.MEM_state_flag) /\ (s'.MEM.MEM_imm = s.MEM.MEM_imm) /\
  (s'.MEM.MEM_opc = s.MEM.MEM_opc) /\ (s'.MEM.MEM_NOP_flag = s.MEM.MEM_NOP_flag)`
    by METIS_TAC [Abbr `s`,Abbr `s'`,agp32_same_items_before_MEM_pipeline] >>
  `s'.EX.EX_imm_updated = s.EX.EX_imm_updated`
    by METIS_TAC [Abbr `s`,Abbr `s'`,agp32_same_EX_items_before_MEM_pipeline] >>
  Cases_on `enable_stg 4 (agp32 fext fbits t)` >-
   (fs [is_sch_memory_def] >>
    Cases_on `isMemOp_hw_op (agp32 fext fbits t)` >-
     METIS_TAC [] >>
    `I' (4,SUC t) = I' (3,t)` by fs [] >> fs [] >>
    `s'.MEM.MEM_state_flag` by fs [enable_stg_def,Abbr `s`] >>
    `~s.MEM.MEM_NOP_flag`
      by fs [enable_stg_def,Abbr `s`,agp32_MEM_state_flag_not_isMemOp_hw_op_MEM_NOP_flag_F] >>
    fs [MEM_pipeline_def,Rel_def,EX_Rel_def]) >>
  `I' (4,SUC t) = I' (4,t)` by fs [is_sch_disable_def] >>
  `~s'.MEM.MEM_state_flag` by fs [enable_stg_def,Abbr `s`] >>
  fs [MEM_pipeline_def] >>
  fs [Rel_def,MEM_Rel_def]
QED

(** when opc is 14w **)
Theorem agp32_Rel_ag32_MEM_imm_correct_LoadUpperConstant:
  !fext fbits a t I.
    is_sch_memory I (agp32 fext fbits) a ==>
    is_sch_disable I (agp32 fext fbits) ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (4,SUC t) <> NONE ==>
    (agp32 fext fbits (SUC t)).MEM.MEM_opc = 14w ==>
    (agp32 fext fbits (SUC t)).MEM.MEM_imm =
    ((8 >< 0) (imm (FUNPOW Next (THE (I (4,SUC t)) − 1) a)) @@
     (22 >< 0) (dataW (FUNPOW Next (THE (I (4,SUC t)) − 1) a)))
Proof
  rw [] >> Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state;WB_pipeline] (fext t) s s` >>
  `(agp32 fext fbits (SUC t)).MEM.MEM_opc = (MEM_pipeline (fext t) s s').MEM.MEM_opc`
    by fs [agp32_MEM_opc_updated_by_MEM_pipeline] >>
  `(agp32 fext fbits (SUC t)).MEM.MEM_imm = (MEM_pipeline (fext t) s s').MEM.MEM_imm`
    by fs [agp32_MEM_PC_imm_addrW_updated_by_MEM_pipeline] >> fs [] >>
  `(s'.MEM.MEM_state_flag = s.MEM.MEM_state_flag) /\ (s'.MEM.MEM_imm = s.MEM.MEM_imm) /\
  (s'.MEM.MEM_opc = s.MEM.MEM_opc) /\ (s'.MEM.MEM_NOP_flag = s.MEM.MEM_NOP_flag)`
    by METIS_TAC [Abbr `s`,Abbr `s'`,agp32_same_items_before_MEM_pipeline] >>
  `s'.EX.EX_imm_updated = s.EX.EX_imm_updated`
    by METIS_TAC [Abbr `s`,Abbr `s'`,agp32_same_EX_items_before_MEM_pipeline] >>
  Cases_on `enable_stg 4 (agp32 fext fbits t)` >-
   (fs [is_sch_memory_def] >>
    Cases_on `isMemOp_hw_op (agp32 fext fbits t)` >-
     METIS_TAC [] >>
    `I' (4,SUC t) = I' (3,t)` by fs [] >> fs [] >>
    `s'.MEM.MEM_state_flag` by fs [enable_stg_def,Abbr `s`] >>
    `~s.MEM.MEM_NOP_flag`
      by fs [enable_stg_def,Abbr `s`,agp32_MEM_state_flag_not_isMemOp_hw_op_MEM_NOP_flag_F] >>
    fs [MEM_pipeline_def,Rel_def,EX_Rel_def]) >>
  `I' (4,SUC t) = I' (4,t)` by fs [is_sch_disable_def] >>
  `~s'.MEM.MEM_state_flag` by fs [enable_stg_def,Abbr `s`] >>
  fs [MEM_pipeline_def] >>
  fs [Rel_def,MEM_Rel_def]
QED

(** MEM_ALU_res **)
Theorem agp32_Rel_ag32_MEM_ALU_res_correct:
  !fext fbits a t I.
    is_sch_memory I (agp32 fext fbits) a ==>
    is_sch_disable I (agp32 fext fbits) ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (4,SUC t) <> NONE ==>
    (agp32 fext fbits (SUC t)).MEM.MEM_ALU_res = ALU_res (FUNPOW Next (THE (I (4,SUC t)) − 1) a)
Proof
  rw [] >> Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state;WB_pipeline] (fext t) s s` >>
  `(agp32 fext fbits (SUC t)).MEM.MEM_ALU_res = (MEM_pipeline (fext t) s s').MEM.MEM_ALU_res`
    by fs [agp32_MEM_ALU_res_updated_by_MEM_pipeline] >> fs [] >>
  `(s'.MEM.MEM_state_flag = s.MEM.MEM_state_flag) /\ (s'.MEM.MEM_ALU_res = s.MEM.MEM_ALU_res)`
    by METIS_TAC [Abbr `s`,Abbr `s'`,agp32_same_items_before_MEM_pipeline] >>
  `s'.EX.EX_ALU_res = s.EX.EX_ALU_res`
    by METIS_TAC [Abbr `s`,Abbr `s'`,agp32_same_EX_items_before_MEM_pipeline] >>
  Cases_on `enable_stg 4 (agp32 fext fbits t)` >-
   (fs [is_sch_memory_def] >>
    Cases_on `isMemOp_hw_op (agp32 fext fbits t)` >-
     METIS_TAC [] >>
    `I' (4,SUC t) = I' (3,t)` by fs [] >> fs [] >>
    `s'.MEM.MEM_state_flag` by fs [enable_stg_def,Abbr `s`] >>
    fs [MEM_pipeline_def,Rel_def,EX_Rel_def]) >>
  `I' (4,SUC t) = I' (4,t)` by fs [is_sch_disable_def] >>
  `~s'.MEM.MEM_state_flag` by fs [enable_stg_def,Abbr `s`] >>
  rw [MEM_pipeline_def] >>
  fs [Rel_def,MEM_Rel_def]
QED

(** MEM_SHIFT_res **)
Theorem agp32_Rel_ag32_MEM_SHIFT_res_correct:
  !fext fbits a t I.
    is_sch_memory I (agp32 fext fbits) a ==>
    is_sch_disable I (agp32 fext fbits) ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (4,SUC t) <> NONE ==>
    (agp32 fext fbits (SUC t)).MEM.MEM_opc = 1w ==>
    (agp32 fext fbits (SUC t)).MEM.MEM_SHIFT_res = shift_res (FUNPOW Next (THE (I (4,SUC t)) − 1) a)
Proof
  rw [] >> Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state;WB_pipeline] (fext t) s s` >>
  `(agp32 fext fbits (SUC t)).MEM.MEM_opc = (MEM_pipeline (fext t) s s').MEM.MEM_opc`
    by fs [agp32_MEM_opc_updated_by_MEM_pipeline] >>
  `(agp32 fext fbits (SUC t)).MEM.MEM_SHIFT_res = (MEM_pipeline (fext t) s s').MEM.MEM_SHIFT_res`
    by fs [agp32_MEM_SHIFT_res_updated_by_MEM_pipeline] >> fs [] >>
  `(s'.MEM.MEM_state_flag = s.MEM.MEM_state_flag) /\ (s'.MEM.MEM_SHIFT_res = s.MEM.MEM_SHIFT_res) /\
  (s'.MEM.MEM_opc = s.MEM.MEM_opc) /\ (s'.MEM.MEM_NOP_flag = s.MEM.MEM_NOP_flag)`
    by METIS_TAC [Abbr `s`,Abbr `s'`,agp32_same_items_before_MEM_pipeline] >>
  `s'.EX.EX_SHIFT_res = s.EX.EX_SHIFT_res`
    by METIS_TAC [Abbr `s`,Abbr `s'`,agp32_same_EX_items_before_MEM_pipeline] >>
  Cases_on `enable_stg 4 (agp32 fext fbits t)` >-
   (fs [is_sch_memory_def] >>
    Cases_on `isMemOp_hw_op (agp32 fext fbits t)` >-
     METIS_TAC [] >>
    `I' (4,SUC t) = I' (3,t)` by fs [] >> fs [] >>
    `s'.MEM.MEM_state_flag` by fs [enable_stg_def,Abbr `s`] >>
    `~s.MEM.MEM_NOP_flag`
      by fs [enable_stg_def,Abbr `s`,agp32_MEM_state_flag_not_isMemOp_hw_op_MEM_NOP_flag_F] >>
    fs [MEM_pipeline_def,Rel_def,EX_Rel_def]) >>
  `I' (4,SUC t) = I' (4,t)` by fs [is_sch_disable_def] >>
  `~s'.MEM.MEM_state_flag` by fs [enable_stg_def,Abbr `s`] >>
  fs [MEM_pipeline_def,Rel_def,MEM_Rel_def]
QED

(** MEM_write_reg **)
Theorem agp32_Rel_ag32_MEM_write_reg_correct:
  !fext fbits a t I.
    is_sch_memory I (agp32 fext fbits) a ==>
    is_sch_disable I (agp32 fext fbits) ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (4,SUC t) <> NONE ==>
    (agp32 fext fbits (SUC t)).MEM.MEM_write_reg = reg_iswrite (FUNPOW Next (THE (I (4,SUC t)) − 1) a)
Proof
  rw [] >> Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state;WB_pipeline] (fext t) s s` >>
  `(agp32 fext fbits (SUC t)).MEM.MEM_write_reg = (MEM_pipeline (fext t) s s').MEM.MEM_write_reg`
    by fs [agp32_MEM_write_reg_updated_by_MEM_pipeline] >>
  `(s'.MEM.MEM_state_flag = s.MEM.MEM_state_flag) /\ (s'.MEM.MEM_write_reg = s.MEM.MEM_write_reg) /\
  (s'.MEM.MEM_NOP_flag = s.MEM.MEM_NOP_flag)`
    by METIS_TAC [Abbr `s`,Abbr `s'`,agp32_same_items_before_MEM_pipeline] >>
  `s'.EX.EX_opc = s.EX.EX_opc`
    by METIS_TAC [Abbr `s`,Abbr `s'`,agp32_same_EX_items_before_MEM_pipeline] >>
  Cases_on `enable_stg 4 (agp32 fext fbits t)` >-
   (fs [is_sch_memory_def] >>
    Cases_on `isMemOp_hw_op (agp32 fext fbits t)` >-
     METIS_TAC [] >>
    `I' (4,SUC t) = I' (3,t)` by fs [] >> fs [] >>
    `s'.MEM.MEM_state_flag` by fs [enable_stg_def,Abbr `s`] >>
    `~s.MEM.MEM_NOP_flag`
      by fs [enable_stg_def,Abbr `s`,agp32_MEM_state_flag_not_isMemOp_hw_op_MEM_NOP_flag_F] >>
    fs [MEM_pipeline_def,Rel_def,EX_Rel_def,reg_iswrite_def]) >>
  `I' (4,SUC t) = I' (4,t)` by fs [is_sch_disable_def] >>
  `~s'.MEM.MEM_state_flag` by fs [enable_stg_def,Abbr `s`] >>
  fs [MEM_pipeline_def,Rel_def,MEM_Rel_def]
QED

(** MEM_read_mem **)
Theorem agp32_Rel_ag32_MEM_read_mem_correct:
  !fext fbits a t I.
    is_sch_memory I (agp32 fext fbits) a ==>
    is_sch_disable I (agp32 fext fbits) ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (4,SUC t) <> NONE ==>
    (agp32 fext fbits (SUC t)).MEM.MEM_read_mem = mem_isread (FUNPOW Next (THE (I (4,SUC t)) − 1) a)
Proof
  rw [] >> Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state;WB_pipeline;MEM_pipeline;EX_pipeline;
                            REG_write;ID_pipeline;IF_PC_update;Acc_compute] (fext t) s s` >>
  Q.ABBREV_TAC `s'' = procs [IF_instr_update;ID_opc_func_update;ID_imm_update;ID_data_update;
                             ID_data_check_update;EX_ALU_input_imm_update;
                             EX_ALU_update;EX_SHIFT_update;EX_jump_sel_addr_update;
                              IF_PC_input_update] (fext (SUC t)) s' s'` >>
  `(agp32 fext fbits (SUC t)).MEM.MEM_read_mem =
  (MEM_ctrl_update (fext (SUC t)) s' s'').MEM.MEM_read_mem`
    by fs [agp32_MEM_ctrl_items_updated_by_MEM_ctrl_update] >>
  `s'.MEM.MEM_opc = (agp32 fext fbits (SUC t)).MEM.MEM_opc`
    by METIS_TAC [Abbr `s`,Abbr `s'`,agp32_same_MEM_pipeline_items_after_MEM_pipeline] >>
  fs [MEM_ctrl_update_def,mem_isread_def] >>
  METIS_TAC [agp32_Rel_ag32_MEM_opc_correct]
QED

(** MEM_write_mem **)
Theorem agp32_Rel_ag32_MEM_write_mem_correct:
  !fext fbits a t I.
    is_sch_memory I (agp32 fext fbits) a ==>
    is_sch_disable I (agp32 fext fbits) ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (4,SUC t) <> NONE ==>
    (agp32 fext fbits (SUC t)).MEM.MEM_write_mem = mem_iswrite (FUNPOW Next (THE (I (4,SUC t)) − 1) a)
Proof
  rw [] >> Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state;WB_pipeline;MEM_pipeline;EX_pipeline;
                            REG_write;ID_pipeline;IF_PC_update;Acc_compute] (fext t) s s` >>
  Q.ABBREV_TAC `s'' = procs [IF_instr_update;ID_opc_func_update;ID_imm_update;ID_data_update;
                             ID_data_check_update;EX_ALU_input_imm_update;
                             EX_ALU_update;EX_SHIFT_update;EX_jump_sel_addr_update;
                              IF_PC_input_update] (fext (SUC t)) s' s'` >>
  `(agp32 fext fbits (SUC t)).MEM.MEM_write_mem =
  (MEM_ctrl_update (fext (SUC t)) s' s'').MEM.MEM_write_mem`
    by fs [agp32_MEM_ctrl_items_updated_by_MEM_ctrl_update] >>
  `s'.MEM.MEM_opc = (agp32 fext fbits (SUC t)).MEM.MEM_opc`
    by METIS_TAC [Abbr `s`,Abbr `s'`,agp32_same_MEM_pipeline_items_after_MEM_pipeline] >>
  fs [MEM_ctrl_update_def,mem_iswrite_def] >>
  METIS_TAC [agp32_Rel_ag32_MEM_opc_correct]
QED

(** MEM_write_mem_byte **)
Theorem agp32_Rel_ag32_MEM_write_mem_byte_correct:
  !fext fbits a t I.
    is_sch_memory I (agp32 fext fbits) a ==>
    is_sch_disable I (agp32 fext fbits) ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (4,SUC t) <> NONE ==>
    (agp32 fext fbits (SUC t)).MEM.MEM_write_mem_byte =
    mem_iswrite_byte (FUNPOW Next (THE (I (4,SUC t)) − 1) a)
Proof
  rw [] >> Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state;WB_pipeline;MEM_pipeline;EX_pipeline;
                            REG_write;ID_pipeline;IF_PC_update;Acc_compute] (fext t) s s` >>
  Q.ABBREV_TAC `s'' = procs [IF_instr_update;ID_opc_func_update;ID_imm_update;ID_data_update;
                             ID_data_check_update;EX_ALU_input_imm_update;
                             EX_ALU_update;EX_SHIFT_update;EX_jump_sel_addr_update;
                              IF_PC_input_update] (fext (SUC t)) s' s'` >>
  `(agp32 fext fbits (SUC t)).MEM.MEM_write_mem_byte =
  (MEM_ctrl_update (fext (SUC t)) s' s'').MEM.MEM_write_mem_byte`
    by fs [agp32_MEM_ctrl_items_updated_by_MEM_ctrl_update] >>
  `s'.MEM.MEM_opc = (agp32 fext fbits (SUC t)).MEM.MEM_opc`
    by METIS_TAC [Abbr `s`,Abbr `s'`,agp32_same_MEM_pipeline_items_after_MEM_pipeline] >>
  fs [MEM_ctrl_update_def,mem_iswrite_byte_def] >>
  METIS_TAC [agp32_Rel_ag32_MEM_opc_correct]
QED

(** MEM_isAcc **)
Theorem agp32_Rel_ag32_MEM_isAcc_correct:
  !fext fbits a t I.
    is_sch_memory I (agp32 fext fbits) a ==>
    is_sch_disable I (agp32 fext fbits) ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (4,SUC t) <> NONE ==>
    (agp32 fext fbits (SUC t)).MEM.MEM_isAcc = isAcc_isa (FUNPOW Next (THE (I (4,SUC t)) − 1) a)
Proof
  rw [] >> Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state;WB_pipeline;MEM_pipeline;EX_pipeline;
                            REG_write;ID_pipeline;IF_PC_update;Acc_compute] (fext t) s s` >>
  Q.ABBREV_TAC `s'' = procs [IF_instr_update;ID_opc_func_update;ID_imm_update;ID_data_update;
                             ID_data_check_update;EX_ALU_input_imm_update;
                             EX_ALU_update;EX_SHIFT_update;EX_jump_sel_addr_update;
                              IF_PC_input_update] (fext (SUC t)) s' s'` >>
  `(agp32 fext fbits (SUC t)).MEM.MEM_isAcc = (MEM_ctrl_update (fext (SUC t)) s' s'').MEM.MEM_isAcc`
    by fs [agp32_MEM_ctrl_items_updated_by_MEM_ctrl_update] >>
  `s'.MEM.MEM_opc = (agp32 fext fbits (SUC t)).MEM.MEM_opc`
    by METIS_TAC [Abbr `s`,Abbr `s'`,agp32_same_MEM_pipeline_items_after_MEM_pipeline] >>
  fs [MEM_ctrl_update_def,isAcc_isa_def] >>
  METIS_TAC [agp32_Rel_ag32_MEM_opc_correct]
QED

(** MEM_isInterrupt **)
Theorem agp32_Rel_ag32_MEM_isInterrupt_correct:
  !fext fbits a t I.
    is_sch_memory I (agp32 fext fbits) a ==>
    is_sch_disable I (agp32 fext fbits) ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (4,SUC t) <> NONE ==>
    (agp32 fext fbits (SUC t)).MEM.MEM_isInterrupt =
    isinterrupt (FUNPOW Next (THE (I (4,SUC t)) − 1) a)
Proof
  rw [] >> Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state;WB_pipeline;MEM_pipeline;EX_pipeline;
                            REG_write;ID_pipeline;IF_PC_update;Acc_compute] (fext t) s s` >>
  Q.ABBREV_TAC `s'' = procs [IF_instr_update;ID_opc_func_update;ID_imm_update;ID_data_update;
                             ID_data_check_update;EX_ALU_input_imm_update;
                             EX_ALU_update;EX_SHIFT_update;EX_jump_sel_addr_update;
                              IF_PC_input_update] (fext (SUC t)) s' s'` >>
  `(agp32 fext fbits (SUC t)).MEM.MEM_isInterrupt =
  (MEM_ctrl_update (fext (SUC t)) s' s'').MEM.MEM_isInterrupt`
    by fs [agp32_MEM_ctrl_items_updated_by_MEM_ctrl_update] >>
  `s'.MEM.MEM_opc = (agp32 fext fbits (SUC t)).MEM.MEM_opc`
    by METIS_TAC [Abbr `s`,Abbr `s'`,agp32_same_MEM_pipeline_items_after_MEM_pipeline] >>
  fs [MEM_ctrl_update_def,isinterrupt_def] >>
  METIS_TAC [agp32_Rel_ag32_MEM_opc_correct]
QED


(* MEM_Rel *)
Theorem agp32_Rel_ag32_MEM_Rel_correct:
  !fext fbits a t I.
    is_sch I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (4,SUC t) <> NONE ==>
    MEM_Rel (agp32 fext fbits (SUC t)) a (THE (I (4,SUC t)))
Proof
  rw [MEM_Rel_def,is_sch_def] >>
  fs [agp32_Rel_ag32_MEM_PC_correct,agp32_Rel_ag32_MEM_addrW_correct,
      agp32_Rel_ag32_MEM_data_correct,agp32_Rel_ag32_MEM_opc_correct,
      agp32_Rel_ag32_MEM_imm_correct_not_LoadUpperConstant,
      agp32_Rel_ag32_MEM_imm_correct_LoadUpperConstant,
      agp32_Rel_ag32_MEM_ALU_res_correct,agp32_Rel_ag32_MEM_SHIFT_res_correct,
      agp32_Rel_ag32_MEM_write_reg_correct,agp32_Rel_ag32_MEM_read_mem_correct,
      agp32_Rel_ag32_MEM_write_mem_correct,agp32_Rel_ag32_MEM_write_mem_byte_correct,
      agp32_Rel_ag32_MEM_isAcc_correct,agp32_Rel_ag32_MEM_isInterrupt_correct]
QED


(** data_addr **)
(** lemma for data_addr/wstrb/wdata **)
Theorem agp32_data_addr_wstrb_wdata_unchanged_when_WB_disabled:
  !fext fbits t.
    ~enable_stg 5 (agp32 fext fbits t) ==>
    ((agp32 fext fbits (SUC t)).data_addr = (agp32 fext fbits t).data_addr) /\
    ((agp32 fext fbits (SUC t)).data_wstrb = (agp32 fext fbits t).data_wstrb) /\
    ((agp32 fext fbits (SUC t)).data_wdata = (agp32 fext fbits t).data_wdata)
Proof
  rpt gen_tac >> disch_tac >>
  fs [enable_stg_def] >>
  Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  `((agp32 fext fbits (SUC t)).data_addr = (agp32_next_state (fext t) s s).data_addr) /\
  ((agp32 fext fbits (SUC t)).data_wstrb = (agp32_next_state (fext t) s s).data_wstrb) /\
  ((agp32 fext fbits (SUC t)).data_wdata = (agp32_next_state (fext t) s s).data_wdata)`
    by fs [agp32_data_addr_wstrb_wdata_updated_by_agp32_next_state] >>
  fs [agp32_next_state_def] >>
  IF_CASES_TAC >> fs [] >>
  reverse IF_CASES_TAC >- rw [] >>
  IF_CASES_TAC >>
  fs [Abbr `s`] >> METIS_TAC [agp32_state_fext_ready_and_WB_state_flag]
QED

(** LoadMem **)
Theorem agp32_Rel_ag32_data_addr_correct_read_mem:
  !fext fbits a t I.
    is_mem fext_accessor_circuit (agp32 fext fbits) fext ==>
    is_sch I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (5, SUC t) <> NONE ==>
    (agp32 fext fbits (SUC t)).WB.WB_opc = 4w ==>
    align_addr (agp32 fext fbits (SUC t)).data_addr =
    mem_data_addr (FUNPOW Next (THE (I (5,SUC t)) − 1) a)
Proof
  rw [] >> Cases_on `enable_stg 5 (agp32 fext fbits t)` >-
   (Q.ABBREV_TAC `s = agp32 fext fbits t` >>              
    `(agp32 fext fbits (SUC t)).data_addr = (agp32_next_state (fext t) s s).data_addr`
      by fs [agp32_data_addr_wstrb_wdata_updated_by_agp32_next_state] >>
    `(fext t).error = 0w` by fs [is_mem_def,mem_no_errors_def] >>
    `s.MEM.MEM_opc = 4w` by fs [agp32_WB_opc_MEM_opc_when_WB_enabled,Abbr `s`] >>
    `s.MEM.MEM_read_mem` by METIS_TAC [Abbr `s`,agp32_MEM_read_mem_MEM_opc_4w_5w] >>
    `I' (5,SUC t) = I' (4,t)` by fs [is_sch_def,is_sch_writeback_def] >>
    `s.state = 0w`
      by (fs [Abbr `s`,enable_stg_def] >> Cases_on_word_value `(agp32 fext fbits t).state` >>
          METIS_TAC [agp32_WB_state_flag_and_state,agp32_state_impossible_values]) >>
    `(fext t).ready`
      by (fs [Abbr `s`,enable_stg_def] >> METIS_TAC [agp32_WB_state_flag_and_fext_ready]) >>
    fs [agp32_next_state_def] >>
    `~s.MEM.MEM_isInterrupt` by fs [Abbr `s`,agp32_MEM_read_mem_others_F] >> fs [] >>
    `opc (FUNPOW Next (THE (I' (4,t)) − 1) a) = 4w` by fs [Rel_def,MEM_Rel_def] >>
    fs [mem_data_addr_def,Rel_def,MEM_Rel_def]) >>
  `(agp32 fext fbits (SUC t)).data_addr = (agp32 fext fbits t).data_addr`
    by fs [agp32_data_addr_wstrb_wdata_unchanged_when_WB_disabled] >>
  `I' (5,SUC t) = I' (5,t)` by fs [is_sch_def,is_sch_disable_def] >>
  `(agp32 fext fbits t).WB.WB_opc = 4w` by fs [agp32_WB_opc_unchanged_when_WB_disabled] >>
  fs [Rel_def,MEM_req_rel_def]
QED

(** LoadMemByte **)
Theorem agp32_Rel_ag32_data_addr_correct_read_mem_byte:
  !fext fbits a t I.
    is_mem fext_accessor_circuit (agp32 fext fbits) fext ==>
    is_sch I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (5, SUC t) <> NONE ==>
    (agp32 fext fbits (SUC t)).WB.WB_opc = 5w ==>
    (agp32 fext fbits (SUC t)).data_addr = mem_data_addr (FUNPOW Next (THE (I (5,SUC t)) − 1) a)
Proof
  rw [] >> Cases_on `enable_stg 5 (agp32 fext fbits t)` >-
   (Q.ABBREV_TAC `s = agp32 fext fbits t` >>              
    `(agp32 fext fbits (SUC t)).data_addr = (agp32_next_state (fext t) s s).data_addr`
      by fs [agp32_data_addr_wstrb_wdata_updated_by_agp32_next_state] >>
    `(fext t).error = 0w` by fs [is_mem_def,mem_no_errors_def] >>
    `s.MEM.MEM_opc = 5w` by fs [agp32_WB_opc_MEM_opc_when_WB_enabled,Abbr `s`] >>
    `s.MEM.MEM_read_mem` by METIS_TAC [Abbr `s`,agp32_MEM_read_mem_MEM_opc_4w_5w] >>
    `I' (5,SUC t) = I' (4,t)` by fs [is_sch_def,is_sch_writeback_def] >>
    `s.state = 0w`
      by (fs [Abbr `s`,enable_stg_def] >> Cases_on_word_value `(agp32 fext fbits t).state` >>
          METIS_TAC [agp32_WB_state_flag_and_state,agp32_state_impossible_values]) >>
    `(fext t).ready`
      by (fs [Abbr `s`,enable_stg_def] >> METIS_TAC [agp32_WB_state_flag_and_fext_ready]) >>
    fs [agp32_next_state_def] >>
    `~s.MEM.MEM_isInterrupt` by fs [Abbr `s`,agp32_MEM_read_mem_others_F] >> fs [] >>
    `opc (FUNPOW Next (THE (I' (4,t)) − 1) a) = 5w` by fs [Rel_def,MEM_Rel_def] >>
    fs [mem_data_addr_def,Rel_def,MEM_Rel_def]) >>
  `(agp32 fext fbits (SUC t)).data_addr = (agp32 fext fbits t).data_addr`
    by fs [agp32_data_addr_wstrb_wdata_unchanged_when_WB_disabled] >>
  `I' (5,SUC t) = I' (5,t)` by fs [is_sch_def,is_sch_disable_def] >>
  `(agp32 fext fbits t).WB.WB_opc = 5w` by fs [agp32_WB_opc_unchanged_when_WB_disabled] >>
  fs [Rel_def,MEM_req_rel_def]
QED

(** StoreMem **)
Theorem agp32_Rel_ag32_data_addr_correct_write_mem:
  !fext fbits a t I.
    is_mem fext_accessor_circuit (agp32 fext fbits) fext ==>
    is_sch I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (5, SUC t) <> NONE ==>
    (agp32 fext fbits (SUC t)).WB.WB_opc = 2w ==>
    align_addr (agp32 fext fbits (SUC t)).data_addr =
    mem_data_addr (FUNPOW Next (THE (I (5,SUC t)) − 1) a)
Proof
  rw [] >> Cases_on `enable_stg 5 (agp32 fext fbits t)` >-
   (Q.ABBREV_TAC `s = agp32 fext fbits t` >>              
    `(agp32 fext fbits (SUC t)).data_addr = (agp32_next_state (fext t) s s).data_addr`
      by fs [agp32_data_addr_wstrb_wdata_updated_by_agp32_next_state] >>
    `(fext t).error = 0w` by fs [is_mem_def,mem_no_errors_def] >>
    `s.MEM.MEM_opc = 2w` by fs [agp32_WB_opc_MEM_opc_when_WB_enabled,Abbr `s`] >>
    `s.MEM.MEM_write_mem` by METIS_TAC [Abbr `s`,agp32_MEM_write_mem_MEM_opc_2w] >>
    `I' (5,SUC t) = I' (4,t)` by fs [is_sch_def,is_sch_writeback_def] >>
    `s.state = 0w`
      by (fs [Abbr `s`,enable_stg_def] >> Cases_on_word_value `(agp32 fext fbits t).state` >>
          METIS_TAC [agp32_WB_state_flag_and_state,agp32_state_impossible_values]) >>
    `(fext t).ready`
      by (fs [Abbr `s`,enable_stg_def] >> METIS_TAC [agp32_WB_state_flag_and_fext_ready]) >>
    fs [agp32_next_state_def] >>
    `~s.MEM.MEM_isInterrupt /\ ~s.MEM.MEM_read_mem`
      by fs [Abbr `s`,agp32_MEM_write_mem_others_F] >> fs [] >>
    `opc (FUNPOW Next (THE (I' (4,t)) − 1) a) = 2w` by fs [Rel_def,MEM_Rel_def] >>
    fs [mem_data_addr_def,Rel_def,MEM_Rel_def]) >>
  `(agp32 fext fbits (SUC t)).data_addr = (agp32 fext fbits t).data_addr`
    by fs [agp32_data_addr_wstrb_wdata_unchanged_when_WB_disabled] >>
  `I' (5,SUC t) = I' (5,t)` by fs [is_sch_def,is_sch_disable_def] >>
  `(agp32 fext fbits t).WB.WB_opc = 2w` by fs [agp32_WB_opc_unchanged_when_WB_disabled] >>
  fs [Rel_def,MEM_req_rel_def]
QED

(** StoreMemByte **)
Theorem agp32_Rel_ag32_data_addr_correct_write_mem_byte:
  !fext fbits a t I.
    is_mem fext_accessor_circuit (agp32 fext fbits) fext ==>
    is_sch I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (5, SUC t) <> NONE ==>
    (agp32 fext fbits (SUC t)).WB.WB_opc = 3w ==>
    (agp32 fext fbits (SUC t)).data_addr = mem_data_addr (FUNPOW Next (THE (I (5,SUC t)) − 1) a)
Proof
  rw [] >> Cases_on `enable_stg 5 (agp32 fext fbits t)` >-
   (Q.ABBREV_TAC `s = agp32 fext fbits t` >>              
    `(agp32 fext fbits (SUC t)).data_addr = (agp32_next_state (fext t) s s).data_addr`
      by fs [agp32_data_addr_wstrb_wdata_updated_by_agp32_next_state] >>
    `(fext t).error = 0w` by fs [is_mem_def,mem_no_errors_def] >>
    `s.MEM.MEM_opc = 3w` by fs [agp32_WB_opc_MEM_opc_when_WB_enabled,Abbr `s`] >>
    `s.MEM.MEM_write_mem_byte` by METIS_TAC [Abbr `s`,agp32_MEM_write_mem_byte_MEM_opc_3w] >>
    `I' (5,SUC t) = I' (4,t)` by fs [is_sch_def,is_sch_writeback_def] >>
    `s.state = 0w`
      by (fs [Abbr `s`,enable_stg_def] >> Cases_on_word_value `(agp32 fext fbits t).state` >>
          METIS_TAC [agp32_WB_state_flag_and_state,agp32_state_impossible_values]) >>
    `(fext t).ready`
      by (fs [Abbr `s`,enable_stg_def] >> METIS_TAC [agp32_WB_state_flag_and_fext_ready]) >>
    fs [agp32_next_state_def] >>
    `~s.MEM.MEM_isInterrupt /\ ~s.MEM.MEM_read_mem /\ ~s.MEM.MEM_write_mem`
      by fs [Abbr `s`,agp32_MEM_write_mem_byte_others_F] >> fs [] >>
    `opc (FUNPOW Next (THE (I' (4,t)) − 1) a) = 3w` by fs [Rel_def,MEM_Rel_def] >>
    Cases_on_word_value `(1 >< 0) s.MEM.MEM_dataB` >>
    fs [mem_data_addr_def,Rel_def,MEM_Rel_def]) >>
  `(agp32 fext fbits (SUC t)).data_addr = (agp32 fext fbits t).data_addr`
    by fs [agp32_data_addr_wstrb_wdata_unchanged_when_WB_disabled] >>
  `I' (5,SUC t) = I' (5,t)` by fs [is_sch_def,is_sch_disable_def] >>
  `(agp32 fext fbits t).WB.WB_opc = 3w` by fs [agp32_WB_opc_unchanged_when_WB_disabled] >>
  fs [Rel_def,MEM_req_rel_def]
QED


(** data_wstrb **)
(** StoreMem **)
Theorem agp32_Rel_ag32_data_wstrb_correct_write_mem:
  !fext fbits a t I.
    is_mem fext_accessor_circuit (agp32 fext fbits) fext ==>
    is_sch I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (5, SUC t) <> NONE ==>
    (agp32 fext fbits (SUC t)).WB.WB_opc = 2w ==>
    (agp32 fext fbits (SUC t)).data_wstrb = mem_data_wstrb (FUNPOW Next (THE (I (5,SUC t)) − 1) a)
Proof
  rw [] >> Cases_on `enable_stg 5 (agp32 fext fbits t)` >-
   (Q.ABBREV_TAC `s = agp32 fext fbits t` >>              
    `(agp32 fext fbits (SUC t)).data_wstrb = (agp32_next_state (fext t) s s).data_wstrb`
      by fs [agp32_data_addr_wstrb_wdata_updated_by_agp32_next_state] >>
    `(fext t).error = 0w` by fs [is_mem_def,mem_no_errors_def] >>
    `s.MEM.MEM_opc = 2w` by fs [agp32_WB_opc_MEM_opc_when_WB_enabled,Abbr `s`] >>
    `s.MEM.MEM_write_mem` by METIS_TAC [Abbr `s`,agp32_MEM_write_mem_MEM_opc_2w] >>
    `I' (5,SUC t) = I' (4,t)` by fs [is_sch_def,is_sch_writeback_def] >>
    `s.state = 0w`
      by (fs [Abbr `s`,enable_stg_def] >> Cases_on_word_value `(agp32 fext fbits t).state` >>
          METIS_TAC [agp32_WB_state_flag_and_state,agp32_state_impossible_values]) >>
    `(fext t).ready`
      by (fs [Abbr `s`,enable_stg_def] >> METIS_TAC [agp32_WB_state_flag_and_fext_ready]) >>
    fs [agp32_next_state_def] >>
    `~s.MEM.MEM_isInterrupt /\ ~s.MEM.MEM_read_mem`
      by fs [Abbr `s`,agp32_MEM_write_mem_others_F] >> fs [] >>
    `opc (FUNPOW Next (THE (I' (4,t)) − 1) a) = 2w` by fs [Rel_def,MEM_Rel_def] >>
    fs [mem_data_wstrb_def,Rel_def,MEM_Rel_def]) >>
  `(agp32 fext fbits (SUC t)).data_wstrb = (agp32 fext fbits t).data_wstrb`
    by fs [agp32_data_addr_wstrb_wdata_unchanged_when_WB_disabled] >>
  `I' (5,SUC t) = I' (5,t)` by fs [is_sch_def,is_sch_disable_def] >>
  `(agp32 fext fbits t).WB.WB_opc = 2w` by fs [agp32_WB_opc_unchanged_when_WB_disabled] >>
  fs [Rel_def,MEM_req_rel_def]
QED

(** StoreMemByte **)
Theorem agp32_Rel_ag32_data_wstrb_correct_write_mem_byte:
  !fext fbits a t I.
    is_mem fext_accessor_circuit (agp32 fext fbits) fext ==>
    is_sch I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (5, SUC t) <> NONE ==>
    (agp32 fext fbits (SUC t)).WB.WB_opc = 3w ==>
    (agp32 fext fbits (SUC t)).data_wstrb = mem_data_wstrb (FUNPOW Next (THE (I (5,SUC t)) − 1) a)
Proof
  rw [] >> Cases_on `enable_stg 5 (agp32 fext fbits t)` >-
   (Q.ABBREV_TAC `s = agp32 fext fbits t` >>              
    `(agp32 fext fbits (SUC t)).data_wstrb = (agp32_next_state (fext t) s s).data_wstrb`
      by fs [agp32_data_addr_wstrb_wdata_updated_by_agp32_next_state] >>
    `(fext t).error = 0w` by fs [is_mem_def,mem_no_errors_def] >>
    `s.MEM.MEM_opc = 3w` by fs [agp32_WB_opc_MEM_opc_when_WB_enabled,Abbr `s`] >>
    `s.MEM.MEM_write_mem_byte` by METIS_TAC [Abbr `s`,agp32_MEM_write_mem_byte_MEM_opc_3w] >>
    `I' (5,SUC t) = I' (4,t)` by fs [is_sch_def,is_sch_writeback_def] >>
    `s.state = 0w`
      by (fs [Abbr `s`,enable_stg_def] >> Cases_on_word_value `(agp32 fext fbits t).state` >>
          METIS_TAC [agp32_WB_state_flag_and_state,agp32_state_impossible_values]) >>
    `(fext t).ready`
      by (fs [Abbr `s`,enable_stg_def] >> METIS_TAC [agp32_WB_state_flag_and_fext_ready]) >>
    fs [agp32_next_state_def] >>
    `~s.MEM.MEM_isInterrupt /\ ~s.MEM.MEM_read_mem /\ ~s.MEM.MEM_write_mem`
      by fs [Abbr `s`,agp32_MEM_write_mem_byte_others_F] >> fs [] >>
    `opc (FUNPOW Next (THE (I' (4,t)) − 1) a) = 3w` by fs [Rel_def,MEM_Rel_def] >>
    `dataB (FUNPOW Next (THE (I' (4,t)) − 1) a) = s.MEM.MEM_dataB` by fs [Rel_def,MEM_Rel_def] >>
    Cases_on_word_value `(1 >< 0) s.MEM.MEM_dataB` >>
    fs [mem_data_wstrb_def]) >>
  `(agp32 fext fbits (SUC t)).data_wstrb = (agp32 fext fbits t).data_wstrb`
    by fs [agp32_data_addr_wstrb_wdata_unchanged_when_WB_disabled] >>
  `I' (5,SUC t) = I' (5,t)` by fs [is_sch_def,is_sch_disable_def] >>
  `(agp32 fext fbits t).WB.WB_opc = 3w` by fs [agp32_WB_opc_unchanged_when_WB_disabled] >>
  fs [Rel_def,MEM_req_rel_def]
QED


(** data_wdata **)
(** StoreMem **)
Theorem agp32_Rel_ag32_data_wdata_correct_write_mem:
  !fext fbits a t I.
    is_mem fext_accessor_circuit (agp32 fext fbits) fext ==>
    is_sch I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (5, SUC t) <> NONE ==>
    (agp32 fext fbits (SUC t)).WB.WB_opc = 2w ==>
    (agp32 fext fbits (SUC t)).data_wdata = mem_data_wdata (FUNPOW Next (THE (I (5,SUC t)) − 1) a)
Proof
  rw [] >> Cases_on `enable_stg 5 (agp32 fext fbits t)` >-
   (Q.ABBREV_TAC `s = agp32 fext fbits t` >>              
    `(agp32 fext fbits (SUC t)).data_wdata = (agp32_next_state (fext t) s s).data_wdata`
      by fs [agp32_data_addr_wstrb_wdata_updated_by_agp32_next_state] >>
    `(fext t).error = 0w` by fs [is_mem_def,mem_no_errors_def] >>
    `s.MEM.MEM_opc = 2w` by fs [agp32_WB_opc_MEM_opc_when_WB_enabled,Abbr `s`] >>
    `s.MEM.MEM_write_mem` by METIS_TAC [Abbr `s`,agp32_MEM_write_mem_MEM_opc_2w] >>
    `I' (5,SUC t) = I' (4,t)` by fs [is_sch_def,is_sch_writeback_def] >>
    `s.state = 0w`
      by (fs [Abbr `s`,enable_stg_def] >> Cases_on_word_value `(agp32 fext fbits t).state` >>
          METIS_TAC [agp32_WB_state_flag_and_state,agp32_state_impossible_values]) >>
    `(fext t).ready`
      by (fs [Abbr `s`,enable_stg_def] >> METIS_TAC [agp32_WB_state_flag_and_fext_ready]) >>
    fs [agp32_next_state_def] >>
    `~s.MEM.MEM_isInterrupt /\ ~s.MEM.MEM_read_mem`
      by fs [Abbr `s`,agp32_MEM_write_mem_others_F] >> fs [] >>
    `opc (FUNPOW Next (THE (I' (4,t)) − 1) a) = 2w` by fs [Rel_def,MEM_Rel_def] >>
    fs [mem_data_wdata_def,Rel_def,MEM_Rel_def]) >>
  `(agp32 fext fbits (SUC t)).data_wdata = (agp32 fext fbits t).data_wdata`
    by fs [agp32_data_addr_wstrb_wdata_unchanged_when_WB_disabled] >>
  `I' (5,SUC t) = I' (5,t)` by fs [is_sch_def,is_sch_disable_def] >>
  `(agp32 fext fbits t).WB.WB_opc = 2w` by fs [agp32_WB_opc_unchanged_when_WB_disabled] >>
  fs [Rel_def,MEM_req_rel_def]
QED

(** StoreMemByte **)
Theorem agp32_Rel_ag32_data_wdata_correct_write_mem_byte_word_bit_0:
  !fext fbits a t I.
    is_mem fext_accessor_circuit (agp32 fext fbits) fext ==>
    is_sch I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (5, SUC t) <> NONE ==>
    (agp32 fext fbits (SUC t)).WB.WB_opc = 3w ==>
    word_bit 0 (agp32 fext fbits (SUC t)).data_wstrb ==>
    (7 >< 0) (agp32 fext fbits (SUC t)).data_wdata =
    mem_data_wdata_byte (FUNPOW Next (THE (I (5,SUC t)) − 1) a)
Proof
  rw [] >> Cases_on `enable_stg 5 (agp32 fext fbits t)` >-
   (Q.ABBREV_TAC `s = agp32 fext fbits t` >>
    `(agp32 fext fbits (SUC t)).data_wdata = (agp32_next_state (fext t) s s).data_wdata /\
    (agp32 fext fbits (SUC t)).data_wstrb = (agp32_next_state (fext t) s s).data_wstrb`
      by fs [agp32_data_addr_wstrb_wdata_updated_by_agp32_next_state] >>
    `(fext t).error = 0w` by fs [is_mem_def,mem_no_errors_def] >>
    `s.MEM.MEM_opc = 3w` by fs [agp32_WB_opc_MEM_opc_when_WB_enabled,Abbr `s`] >>
    `s.MEM.MEM_write_mem_byte` by METIS_TAC [Abbr `s`,agp32_MEM_write_mem_byte_MEM_opc_3w] >>
    `I' (5,SUC t) = I' (4,t)` by fs [is_sch_def,is_sch_writeback_def] >>
    `s.state = 0w`
      by (fs [Abbr `s`,enable_stg_def] >> Cases_on_word_value `(agp32 fext fbits t).state` >>
          METIS_TAC [agp32_WB_state_flag_and_state,agp32_state_impossible_values]) >>
    `(fext t).ready`
      by (fs [Abbr `s`,enable_stg_def] >> METIS_TAC [agp32_WB_state_flag_and_fext_ready]) >>
    fs [agp32_next_state_def] >>
    `~s.MEM.MEM_isInterrupt /\ ~s.MEM.MEM_read_mem /\ ~s.MEM.MEM_write_mem`
      by fs [Abbr `s`,agp32_MEM_write_mem_byte_others_F] >> fs [] >>
    `opc (FUNPOW Next (THE (I' (4,t)) − 1) a) = 3w` by fs [Rel_def,MEM_Rel_def] >>
    Cases_on_word_value `(1 >< 0) s.MEM.MEM_dataB` >> fs [] >>
    simp [bit_field_insert_def,word_modify_def] >>
    fs [Rel_def,MEM_Rel_def,mem_data_wdata_byte_def] >>
    BBLAST_TAC) >>
  `(agp32 fext fbits (SUC t)).data_wdata = (agp32 fext fbits t).data_wdata /\
  (agp32 fext fbits (SUC t)).data_wstrb = (agp32 fext fbits t).data_wstrb`
    by fs [agp32_data_addr_wstrb_wdata_unchanged_when_WB_disabled] >>
  `I' (5,SUC t) = I' (5,t)` by fs [is_sch_def,is_sch_disable_def] >>
  `(agp32 fext fbits t).WB.WB_opc = 3w` by fs [agp32_WB_opc_unchanged_when_WB_disabled] >>
  fs [Rel_def,MEM_req_rel_def]
QED

Theorem agp32_Rel_ag32_data_wdata_correct_write_mem_byte_word_bit_1:
  !fext fbits a t I.
    is_mem fext_accessor_circuit (agp32 fext fbits) fext ==>
    is_sch I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (5, SUC t) <> NONE ==>
    (agp32 fext fbits (SUC t)).WB.WB_opc = 3w ==>
    word_bit 1 (agp32 fext fbits (SUC t)).data_wstrb ==>
    (15 >< 8) (agp32 fext fbits (SUC t)).data_wdata =
    mem_data_wdata_byte (FUNPOW Next (THE (I (5,SUC t)) − 1) a)
Proof
  rw [] >> Cases_on `enable_stg 5 (agp32 fext fbits t)` >-
   (Q.ABBREV_TAC `s = agp32 fext fbits t` >>
    `(agp32 fext fbits (SUC t)).data_wdata = (agp32_next_state (fext t) s s).data_wdata /\
    (agp32 fext fbits (SUC t)).data_wstrb = (agp32_next_state (fext t) s s).data_wstrb`
      by fs [agp32_data_addr_wstrb_wdata_updated_by_agp32_next_state] >>
    `(fext t).error = 0w` by fs [is_mem_def,mem_no_errors_def] >>
    `s.MEM.MEM_opc = 3w` by fs [agp32_WB_opc_MEM_opc_when_WB_enabled,Abbr `s`] >>
    `s.MEM.MEM_write_mem_byte` by METIS_TAC [Abbr `s`,agp32_MEM_write_mem_byte_MEM_opc_3w] >>
    `I' (5,SUC t) = I' (4,t)` by fs [is_sch_def,is_sch_writeback_def] >>
    `s.state = 0w`
      by (fs [Abbr `s`,enable_stg_def] >> Cases_on_word_value `(agp32 fext fbits t).state` >>
          METIS_TAC [agp32_WB_state_flag_and_state,agp32_state_impossible_values]) >>
    `(fext t).ready`
      by (fs [Abbr `s`,enable_stg_def] >> METIS_TAC [agp32_WB_state_flag_and_fext_ready]) >>
    fs [agp32_next_state_def] >>
    `~s.MEM.MEM_isInterrupt /\ ~s.MEM.MEM_read_mem /\ ~s.MEM.MEM_write_mem`
      by fs [Abbr `s`,agp32_MEM_write_mem_byte_others_F] >> fs [] >>
    `opc (FUNPOW Next (THE (I' (4,t)) − 1) a) = 3w` by fs [Rel_def,MEM_Rel_def] >>
    Cases_on_word_value `(1 >< 0) s.MEM.MEM_dataB` >> fs [] >>
    simp [bit_field_insert_def,word_modify_def] >>
    fs [Rel_def,MEM_Rel_def,mem_data_wdata_byte_def] >>
    BBLAST_TAC) >>
  `(agp32 fext fbits (SUC t)).data_wdata = (agp32 fext fbits t).data_wdata /\
  (agp32 fext fbits (SUC t)).data_wstrb = (agp32 fext fbits t).data_wstrb`
    by fs [agp32_data_addr_wstrb_wdata_unchanged_when_WB_disabled] >>
  `I' (5,SUC t) = I' (5,t)` by fs [is_sch_def,is_sch_disable_def] >>
  `(agp32 fext fbits t).WB.WB_opc = 3w` by fs [agp32_WB_opc_unchanged_when_WB_disabled] >>
  fs [Rel_def,MEM_req_rel_def]
QED

Theorem agp32_Rel_ag32_data_wdata_correct_write_mem_byte_word_bit_2:
  !fext fbits a t I.
    is_mem fext_accessor_circuit (agp32 fext fbits) fext ==>
    is_sch I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (5, SUC t) <> NONE ==>
    (agp32 fext fbits (SUC t)).WB.WB_opc = 3w ==>
    word_bit 2 (agp32 fext fbits (SUC t)).data_wstrb ==>
    (23 >< 16) (agp32 fext fbits (SUC t)).data_wdata =
    mem_data_wdata_byte (FUNPOW Next (THE (I (5,SUC t)) − 1) a)
Proof
  rw [] >> Cases_on `enable_stg 5 (agp32 fext fbits t)` >-
   (Q.ABBREV_TAC `s = agp32 fext fbits t` >>
    `(agp32 fext fbits (SUC t)).data_wdata = (agp32_next_state (fext t) s s).data_wdata /\
    (agp32 fext fbits (SUC t)).data_wstrb = (agp32_next_state (fext t) s s).data_wstrb`
      by fs [agp32_data_addr_wstrb_wdata_updated_by_agp32_next_state] >>
    `(fext t).error = 0w` by fs [is_mem_def,mem_no_errors_def] >>
    `s.MEM.MEM_opc = 3w` by fs [agp32_WB_opc_MEM_opc_when_WB_enabled,Abbr `s`] >>
    `s.MEM.MEM_write_mem_byte` by METIS_TAC [Abbr `s`,agp32_MEM_write_mem_byte_MEM_opc_3w] >>
    `I' (5,SUC t) = I' (4,t)` by fs [is_sch_def,is_sch_writeback_def] >>
    `s.state = 0w`
      by (fs [Abbr `s`,enable_stg_def] >> Cases_on_word_value `(agp32 fext fbits t).state` >>
          METIS_TAC [agp32_WB_state_flag_and_state,agp32_state_impossible_values]) >>
    `(fext t).ready`
      by (fs [Abbr `s`,enable_stg_def] >> METIS_TAC [agp32_WB_state_flag_and_fext_ready]) >>
    fs [agp32_next_state_def] >>
    `~s.MEM.MEM_isInterrupt /\ ~s.MEM.MEM_read_mem /\ ~s.MEM.MEM_write_mem`
      by fs [Abbr `s`,agp32_MEM_write_mem_byte_others_F] >> fs [] >>
    `opc (FUNPOW Next (THE (I' (4,t)) − 1) a) = 3w` by fs [Rel_def,MEM_Rel_def] >>
    Cases_on_word_value `(1 >< 0) s.MEM.MEM_dataB` >> fs [] >>
    simp [bit_field_insert_def,word_modify_def] >>
    fs [Rel_def,MEM_Rel_def,mem_data_wdata_byte_def] >>
    BBLAST_TAC) >>
  `(agp32 fext fbits (SUC t)).data_wdata = (agp32 fext fbits t).data_wdata /\
  (agp32 fext fbits (SUC t)).data_wstrb = (agp32 fext fbits t).data_wstrb`
    by fs [agp32_data_addr_wstrb_wdata_unchanged_when_WB_disabled] >>
  `I' (5,SUC t) = I' (5,t)` by fs [is_sch_def,is_sch_disable_def] >>
  `(agp32 fext fbits t).WB.WB_opc = 3w` by fs [agp32_WB_opc_unchanged_when_WB_disabled] >>
  fs [Rel_def,MEM_req_rel_def]
QED

Theorem agp32_Rel_ag32_data_wdata_correct_write_mem_byte_word_bit_3:
  !fext fbits a t I.
    is_mem fext_accessor_circuit (agp32 fext fbits) fext ==>
    is_sch I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (5, SUC t) <> NONE ==>
    (agp32 fext fbits (SUC t)).WB.WB_opc = 3w ==>
    word_bit 3 (agp32 fext fbits (SUC t)).data_wstrb ==>
    (31 >< 24) (agp32 fext fbits (SUC t)).data_wdata =
    mem_data_wdata_byte (FUNPOW Next (THE (I (5,SUC t)) − 1) a)
Proof
  rw [] >> Cases_on `enable_stg 5 (agp32 fext fbits t)` >-
   (Q.ABBREV_TAC `s = agp32 fext fbits t` >>
    `(agp32 fext fbits (SUC t)).data_wdata = (agp32_next_state (fext t) s s).data_wdata /\
    (agp32 fext fbits (SUC t)).data_wstrb = (agp32_next_state (fext t) s s).data_wstrb`
      by fs [agp32_data_addr_wstrb_wdata_updated_by_agp32_next_state] >>
    `(fext t).error = 0w` by fs [is_mem_def,mem_no_errors_def] >>
    `s.MEM.MEM_opc = 3w` by fs [agp32_WB_opc_MEM_opc_when_WB_enabled,Abbr `s`] >>
    `s.MEM.MEM_write_mem_byte` by METIS_TAC [Abbr `s`,agp32_MEM_write_mem_byte_MEM_opc_3w] >>
    `I' (5,SUC t) = I' (4,t)` by fs [is_sch_def,is_sch_writeback_def] >>
    `s.state = 0w`
      by (fs [Abbr `s`,enable_stg_def] >> Cases_on_word_value `(agp32 fext fbits t).state` >>
          METIS_TAC [agp32_WB_state_flag_and_state,agp32_state_impossible_values]) >>
    `(fext t).ready`
      by (fs [Abbr `s`,enable_stg_def] >> METIS_TAC [agp32_WB_state_flag_and_fext_ready]) >>
    fs [agp32_next_state_def] >>
    `~s.MEM.MEM_isInterrupt /\ ~s.MEM.MEM_read_mem /\ ~s.MEM.MEM_write_mem`
      by fs [Abbr `s`,agp32_MEM_write_mem_byte_others_F] >> fs [] >>
    `opc (FUNPOW Next (THE (I' (4,t)) − 1) a) = 3w` by fs [Rel_def,MEM_Rel_def] >>
    Cases_on_word_value `(1 >< 0) s.MEM.MEM_dataB` >> fs [] >>
    simp [bit_field_insert_def,word_modify_def] >>
    fs [Rel_def,MEM_Rel_def,mem_data_wdata_byte_def] >>
    BBLAST_TAC) >>
  `(agp32 fext fbits (SUC t)).data_wdata = (agp32 fext fbits t).data_wdata /\
  (agp32 fext fbits (SUC t)).data_wstrb = (agp32 fext fbits t).data_wstrb`
    by fs [agp32_data_addr_wstrb_wdata_unchanged_when_WB_disabled] >>
  `I' (5,SUC t) = I' (5,t)` by fs [is_sch_def,is_sch_disable_def] >>
  `(agp32 fext fbits t).WB.WB_opc = 3w` by fs [agp32_WB_opc_unchanged_when_WB_disabled] >>
  fs [Rel_def,MEM_req_rel_def]
QED

(** lemma for acc_arg **)
Theorem agp32_acc_arg_unchanged_when_WB_disabled:
  !fext fbits t.
    ~enable_stg 5 (agp32 fext fbits t) ==>
    (agp32 fext fbits (SUC t)).acc_arg = (agp32 fext fbits t).acc_arg
Proof
  rw [enable_stg_def] >>
  Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  `(agp32 fext fbits (SUC t)).acc_arg = (agp32_next_state (fext t) s s).acc_arg`
    by fs [agp32_acc_arg_and_ready_updated_by_agp32_next_state] >>
  fs [agp32_next_state_def] >>
  IF_CASES_TAC >> fs [] >>
  reverse IF_CASES_TAC >- rw [] >>
  IF_CASES_TAC >>
  fs [Abbr `s`] >> METIS_TAC [agp32_state_fext_ready_and_WB_state_flag]
QED

(** acc_arg **)
Theorem agp32_Rel_ag32_acc_arg_correct:
  !fext fbits a t I.
    is_mem fext_accessor_circuit (agp32 fext fbits) fext ==>
    is_sch I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (5, SUC t) <> NONE ==>
    (agp32 fext fbits (SUC t)).WB.WB_opc = 8w ==>
    (agp32 fext fbits (SUC t)).acc_arg = dataA (FUNPOW Next (THE (I (5,SUC t)) − 1) a)
Proof
  rw [] >> Cases_on `enable_stg 5 (agp32 fext fbits t)` >-
   (Q.ABBREV_TAC `s = agp32 fext fbits t` >>
    `(agp32 fext fbits (SUC t)).acc_arg = (agp32_next_state (fext t) s s).acc_arg`
      by fs [agp32_acc_arg_and_ready_updated_by_agp32_next_state] >>
    `(fext t).error = 0w` by fs [is_mem_def,mem_no_errors_def] >>
    `s.MEM.MEM_opc = 8w` by fs [agp32_WB_opc_MEM_opc_when_WB_enabled,Abbr `s`] >>
    `s.MEM.MEM_isAcc` by METIS_TAC [Abbr `s`,agp32_MEM_isAcc_MEM_opc_8w] >>
    `I' (5,SUC t) = I' (4,t)` by fs [is_sch_def,is_sch_writeback_def] >>
    `s.state = 0w`
      by (fs [Abbr `s`,enable_stg_def] >> Cases_on_word_value `(agp32 fext fbits t).state` >>
          METIS_TAC [agp32_WB_state_flag_and_state,agp32_state_impossible_values]) >>
    `(fext t).ready`
      by (fs [Abbr `s`,enable_stg_def] >> METIS_TAC [agp32_WB_state_flag_and_fext_ready]) >>
    fs [agp32_next_state_def] >>
    `~s.MEM.MEM_isInterrupt /\ ~s.MEM.MEM_read_mem /\
    ~s.MEM.MEM_write_mem /\ ~s.MEM.MEM_write_mem_byte`
      by fs [Abbr `s`,agp32_MEM_isAcc_others_F] >> fs [] >>
    fs [Rel_def,MEM_Rel_def]) >>
  `(agp32 fext fbits (SUC t)).acc_arg = (agp32 fext fbits t).acc_arg`
    by fs [agp32_acc_arg_unchanged_when_WB_disabled] >>
  `I' (5,SUC t) = I' (5,t)` by fs [is_sch_def,is_sch_disable_def] >>
  `(agp32 fext fbits t).WB.WB_opc = 8w` by fs [agp32_WB_opc_unchanged_when_WB_disabled] >>
  fs [Rel_def,MEM_req_rel_def]
QED

(** acc_arg_ready **)
Theorem agp32_acc_arg_ready_WB_enable:
  !fext fbits a t I.
    is_mem fext_accessor_circuit (agp32 fext fbits) fext ==>
    enable_stg 5 (agp32 fext fbits t) ==>
    (agp32 fext fbits (SUC t)).WB.WB_opc = 8w ==>
    (agp32 fext fbits (SUC t)).acc_arg_ready
Proof
  rw [] >> Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  `(agp32 fext fbits (SUC t)).acc_arg_ready = (agp32_next_state (fext t) s s).acc_arg_ready`
    by fs [agp32_acc_arg_and_ready_updated_by_agp32_next_state] >>
  `(fext t).error = 0w` by fs [is_mem_def,mem_no_errors_def] >>     
  `s.MEM.MEM_opc = 8w` by gs [agp32_WB_opc_MEM_opc_when_WB_enabled,Abbr `s`] >>
  `s.MEM.MEM_isAcc` by gs [Abbr `s`,agp32_MEM_isAcc_MEM_opc_8w] >>
  `s.state = 0w`
    by (fs [Abbr `s`,enable_stg_def] >> Cases_on_word_value `(agp32 fext fbits t).state` >>
        METIS_TAC [agp32_WB_state_flag_and_state,agp32_state_impossible_values]) >>     
  `(fext t).ready`
    by (fs [Abbr `s`,enable_stg_def] >> METIS_TAC [agp32_WB_state_flag_and_fext_ready]) >>
  fs [agp32_next_state_def] >>
  `~s.MEM.MEM_isInterrupt /\ ~s.MEM.MEM_read_mem /\
  ~s.MEM.MEM_write_mem /\ ~s.MEM.MEM_write_mem_byte`
    by fs [Abbr `s`,agp32_MEM_isAcc_others_F] >> fs []
QED

(** do_interrupt **)
Theorem agp32_do_interrupt_WB_enable:
  !fext fbits a t I.
    is_mem fext_accessor_circuit (agp32 fext fbits) fext ==>
    enable_stg 5 (agp32 fext fbits t) ==>
    (agp32 fext fbits (SUC t)).WB.WB_opc = 12w ==>
    (agp32 fext fbits (SUC t)).do_interrupt
Proof
  rw [] >> Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  `(agp32 fext fbits (SUC t)).do_interrupt = (agp32_next_state (fext t) s s).do_interrupt`
    by fs [agp32_interrupt_items_updated_by_agp32_next_state] >>
  `(fext t).error = 0w` by fs [is_mem_def,mem_no_errors_def] >>     
  `s.MEM.MEM_opc = 12w` by gs [agp32_WB_opc_MEM_opc_when_WB_enabled,Abbr `s`] >>
  `s.MEM.MEM_isInterrupt` by gs [Abbr `s`,agp32_MEM_isInterrupt_MEM_opc_12w] >>
  `s.state = 0w`
    by (fs [Abbr `s`,enable_stg_def] >> Cases_on_word_value `(agp32 fext fbits t).state` >>
        METIS_TAC [agp32_WB_state_flag_and_state,agp32_state_impossible_values]) >>     
  `(fext t).ready`
    by (fs [Abbr `s`,enable_stg_def] >> METIS_TAC [agp32_WB_state_flag_and_fext_ready]) >>
  fs [agp32_next_state_def]
QED


(* MEM_req_rel *)
Theorem agp32_Rel_ag32_MEM_req_rel_correct:
  !fext fbits a t I.
    is_mem fext_accessor_circuit (agp32 fext fbits) fext ==>
    is_sch I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (5,SUC t) <> NONE ==>
    MEM_req_rel (fext (SUC t)) (agp32 fext fbits t) (agp32 fext fbits (SUC t)) a (THE (I (5,SUC t)))
Proof
  rw [MEM_req_rel_def] >>
  fs [agp32_Rel_ag32_data_addr_correct_read_mem,agp32_Rel_ag32_data_addr_correct_read_mem_byte,
      agp32_Rel_ag32_data_addr_correct_write_mem,agp32_Rel_ag32_data_addr_correct_write_mem_byte,
      agp32_Rel_ag32_data_wstrb_correct_write_mem,agp32_Rel_ag32_data_wstrb_correct_write_mem_byte,
      agp32_Rel_ag32_data_wdata_correct_write_mem,
      agp32_Rel_ag32_data_wdata_correct_write_mem_byte_word_bit_0,
      agp32_Rel_ag32_data_wdata_correct_write_mem_byte_word_bit_1,
      agp32_Rel_ag32_data_wdata_correct_write_mem_byte_word_bit_2,
      agp32_Rel_ag32_data_wdata_correct_write_mem_byte_word_bit_3,
      agp32_Rel_ag32_acc_arg_correct,agp32_acc_arg_ready_WB_enable,
      agp32_do_interrupt_WB_enable]
QED


(** command: memory command **)
(** StoreMem **)
Theorem agp32_Rel_ag32_command_correct_write_mem_WB_enable:
  !fext fbits a t.
    is_mem fext_accessor_circuit (agp32 fext fbits) fext ==>   
    enable_stg 5 (agp32 fext fbits t) ==>
    (agp32 fext fbits (SUC t)).WB.WB_opc = 2w ==>
    (agp32 fext fbits (SUC t)).command = 3w
Proof
  rw [] >> Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  `(agp32 fext fbits (SUC t)).command = (agp32_next_state (fext t) s s).command`
    by fs [agp32_command_state_updated_by_agp32_next_state] >>
  `(fext t).error = 0w` by fs [is_mem_def,mem_no_errors_def] >>
  `s.MEM.MEM_opc = 2w` by METIS_TAC [agp32_WB_opc_MEM_opc_when_WB_enabled,Abbr `s`] >>
  `s.MEM.MEM_write_mem` by METIS_TAC [Abbr `s`,agp32_MEM_write_mem_MEM_opc_2w] >>
  `s.state = 0w`
    by (fs [Abbr `s`,enable_stg_def] >> Cases_on_word_value `(agp32 fext fbits t).state` >>
        METIS_TAC [agp32_WB_state_flag_and_state,agp32_state_impossible_values]) >>
  `(fext t).ready`
    by (fs [Abbr `s`,enable_stg_def] >> METIS_TAC [agp32_WB_state_flag_and_fext_ready]) >>
  fs [agp32_next_state_def,Abbr `s`,agp32_MEM_write_mem_others_F]
QED

(** StoreMemByte **)
Theorem agp32_Rel_ag32_command_correct_write_mem_byte_WB_enable:
  !fext fbits a t.
    is_mem fext_accessor_circuit (agp32 fext fbits) fext ==>
    enable_stg 5 (agp32 fext fbits t) ==>
    (agp32 fext fbits (SUC t)).WB.WB_opc = 3w ==>
    (agp32 fext fbits (SUC t)).command = 3w
Proof
  rw [] >> Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  `(agp32 fext fbits (SUC t)).command = (agp32_next_state (fext t) s s).command`
    by fs [agp32_command_state_updated_by_agp32_next_state] >>
  `(fext t).error = 0w` by fs [is_mem_def,mem_no_errors_def] >>
  `s.MEM.MEM_opc = 3w` by METIS_TAC [agp32_WB_opc_MEM_opc_when_WB_enabled,Abbr `s`] >>
  `s.MEM.MEM_write_mem_byte` by METIS_TAC [Abbr `s`,agp32_MEM_write_mem_byte_MEM_opc_3w] >>
  `s.state = 0w`
    by (fs [Abbr `s`,enable_stg_def] >> Cases_on_word_value `(agp32 fext fbits t).state` >>
        METIS_TAC [agp32_WB_state_flag_and_state,agp32_state_impossible_values]) >>
  `(fext t).ready`
    by (fs [Abbr `s`,enable_stg_def] >> METIS_TAC [agp32_WB_state_flag_and_fext_ready]) >>
  fs [agp32_next_state_def,Abbr `s`,agp32_MEM_write_mem_byte_others_F] >>
  Cases_on_word_value `(1 >< 0) (agp32 fext fbits t).MEM.MEM_dataB` >> rw []
QED

(** LoadMem **)
Theorem agp32_Rel_ag32_command_correct_read_mem_WB_enable:
  !fext fbits a t.
    is_mem fext_accessor_circuit (agp32 fext fbits) fext ==>
    enable_stg 5 (agp32 fext fbits t) ==>
    (agp32 fext fbits (SUC t)).WB.WB_opc = 4w ==>
    (agp32 fext fbits (SUC t)).command = 2w
Proof
  rw [] >> Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  `(agp32 fext fbits (SUC t)).command = (agp32_next_state (fext t) s s).command`
    by fs [agp32_command_state_updated_by_agp32_next_state] >>
  `(fext t).error = 0w` by fs [is_mem_def,mem_no_errors_def] >>
  `s.MEM.MEM_opc = 4w` by METIS_TAC [agp32_WB_opc_MEM_opc_when_WB_enabled,Abbr `s`] >>
  `s.MEM.MEM_read_mem` by METIS_TAC [Abbr `s`,agp32_MEM_read_mem_MEM_opc_4w_5w] >>
  `s.state = 0w`
    by (fs [Abbr `s`,enable_stg_def] >> Cases_on_word_value `(agp32 fext fbits t).state` >>
        METIS_TAC [agp32_WB_state_flag_and_state,agp32_state_impossible_values]) >>
  `(fext t).ready`
    by (fs [Abbr `s`,enable_stg_def] >> METIS_TAC [agp32_WB_state_flag_and_fext_ready]) >>
  fs [agp32_next_state_def,Abbr `s`,agp32_MEM_read_mem_others_F]
QED

(** LoadMemByte **)
Theorem agp32_Rel_ag32_command_correct_read_mem_byte_WB_enable:
  !fext fbits a t.
    is_mem fext_accessor_circuit (agp32 fext fbits) fext ==>
    enable_stg 5 (agp32 fext fbits t) ==>
    (agp32 fext fbits (SUC t)).WB.WB_opc = 5w ==>
    (agp32 fext fbits (SUC t)).command = 2w
Proof
  rw [] >> Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  `(agp32 fext fbits (SUC t)).command = (agp32_next_state (fext t) s s).command`
    by fs [agp32_command_state_updated_by_agp32_next_state] >>
  `(fext t).error = 0w` by fs [is_mem_def,mem_no_errors_def] >>
  `s.MEM.MEM_opc = 5w` by METIS_TAC [agp32_WB_opc_MEM_opc_when_WB_enabled,Abbr `s`] >>
  `s.MEM.MEM_read_mem` by METIS_TAC [Abbr `s`,agp32_MEM_read_mem_MEM_opc_4w_5w] >>
  `s.state = 0w`
    by (fs [Abbr `s`,enable_stg_def] >> Cases_on_word_value `(agp32 fext fbits t).state` >>
        METIS_TAC [agp32_WB_state_flag_and_state,agp32_state_impossible_values]) >>
  `(fext t).ready`
    by (fs [Abbr `s`,enable_stg_def] >> METIS_TAC [agp32_WB_state_flag_and_fext_ready]) >>
  fs [agp32_next_state_def,Abbr `s`,agp32_MEM_read_mem_others_F]
QED

(** NONE instr **)
Theorem agp32_Rel_ag32_command_correct_none_instr_WB_enable:
  !fext fbits a t.
    is_mem fext_accessor_circuit (agp32 fext fbits) fext ==>
    enable_stg 5 (agp32 fext fbits t) ==>
    ((agp32 fext fbits (SUC t)).WB.WB_opc = 16w \/ (agp32 fext fbits (SUC t)).WB.WB_opc = 15w) ==>
    (agp32 fext fbits (SUC t)).command = 1w
Proof
  rpt gen_tac >> rpt disch_tac >>
  Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  `(agp32 fext fbits (SUC t)).command = (agp32_next_state (fext t) s s).command`
    by fs [agp32_command_state_updated_by_agp32_next_state] >>
  `(fext t).error = 0w` by fs [is_mem_def,mem_no_errors_def] >>
  `s.MEM.MEM_opc = 16w \/ s.MEM.MEM_opc = 15w` by METIS_TAC [agp32_WB_opc_MEM_opc_when_WB_enabled,Abbr `s`] >>
  `~s.MEM.MEM_read_mem` by fs [Abbr `s`,agp32_MEM_read_mem_MEM_opc_4w_5w] >>
  `~s.MEM.MEM_write_mem_byte` by fs [Abbr `s`,agp32_MEM_write_mem_byte_MEM_opc_3w] >>
  `~s.MEM.MEM_write_mem` by fs [Abbr `s`,agp32_MEM_write_mem_MEM_opc_2w] >>
  `~s.MEM.MEM_isInterrupt` by fs [Abbr `s`,agp32_MEM_isInterrupt_MEM_opc_12w] >>
  `s.state = 0w`
    by (fs [Abbr `s`,enable_stg_def] >> Cases_on_word_value `(agp32 fext fbits t).state` >>
        METIS_TAC [agp32_WB_state_flag_and_state,agp32_state_impossible_values]) >>
  `(fext t).ready`
    by (fs [Abbr `s`,enable_stg_def] >> METIS_TAC [agp32_WB_state_flag_and_fext_ready]) >>
  fs [agp32_next_state_def,Abbr `s`] >> rw []
QED

(** command when the WB is disabled, WB_opc is not 16, and fext is ready at the previous cycle **)
Theorem agp32_Rel_ag32_command_correct_WB_disable_fext_ready:
  !fext fbits a t I.
    is_mem fext_accessor_circuit (agp32 fext fbits) fext ==>
    ~enable_stg 5 (agp32 fext fbits t) ==>
    (fext t).ready ==>
    (agp32 fext fbits (SUC t)).WB.WB_opc <> 16w ==>
    (agp32 fext fbits (SUC t)).command = 0w
Proof
  rw [] >> Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  `(agp32 fext fbits (SUC t)).command = (agp32_next_state (fext t) s s).command`
    by fs [agp32_command_state_updated_by_agp32_next_state] >>
  `(fext t).error = 0w` by fs [is_mem_def,mem_no_errors_def] >>
  Cases_on_word_value `s.state` >-
   fs [Abbr `s`,agp32_state_impossible_values] >-
   fs [Abbr `s`,agp32_state_impossible_values] >-
   METIS_TAC [Abbr `s`,agp32_state_impossible_5_no_fext_error] >-
   (`s.command = 0w` by fs [agp32_state_4_command_0,Abbr `s`] >>
    fs [agp32_next_state_def] >>
    IF_CASES_TAC >> fs []) >-
   METIS_TAC [agp32_state_3_WB_opc_16,Abbr `s`] >-
   fs [agp32_next_state_def] >-
   fs [agp32_next_state_def] >>
  fs [enable_stg_def,Abbr `s`] >>
  METIS_TAC [agp32_ready_not_WB_state_flag_state_not_0]
QED

(** command when the WB is disabled and fext is ready at the previous cycle **)
Theorem agp32_Rel_ag32_command_correct_WB_disable_fext_ready_extra:
  !fext fbits a t I.
    is_mem fext_accessor_circuit (agp32 fext fbits) fext ==>
    ~enable_stg 5 (agp32 fext fbits t) ==>
    (fext t).ready ==>
    (agp32 fext fbits (SUC t)).command = 0w \/ (agp32 fext fbits (SUC t)).command = 1w
Proof
  rw [] >> Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  `(agp32 fext fbits (SUC t)).command = (agp32_next_state (fext t) s s).command`
    by fs [agp32_command_state_updated_by_agp32_next_state] >>
  `(fext t).error = 0w` by fs [is_mem_def,mem_no_errors_def] >>
  Cases_on_word_value `s.state` >-
   fs [Abbr `s`,agp32_state_impossible_values] >-
   fs [Abbr `s`,agp32_state_impossible_values] >-
   METIS_TAC [Abbr `s`,agp32_state_impossible_5_no_fext_error] >-
   (`s.command = 0w` by fs [agp32_state_4_command_0,Abbr `s`] >>
    fs [agp32_next_state_def] >>
    IF_CASES_TAC >> fs []) >-
   (fs [agp32_next_state_def] >>
    IF_CASES_TAC >> fs [agp32_state_3_command_0,Abbr `s`]) >-
   fs [agp32_next_state_def] >-
   fs [agp32_next_state_def] >>
  fs [enable_stg_def,Abbr `s`] >>
  METIS_TAC [agp32_ready_not_WB_state_flag_state_not_0]
QED

(** if MEM_opc is not 2 or 3 then the command is not 3 **)
Theorem agp32_Rel_ag32_command_not_3_not_write_mem_and_byte_WB_enable:
  !fext fbits a t.
    is_mem fext_accessor_circuit (agp32 fext fbits) fext ==>   
    enable_stg 5 (agp32 fext fbits t) ==>
    (agp32 fext fbits t).MEM.MEM_opc <> 2w ==>
    (agp32 fext fbits t).MEM.MEM_opc <> 3w ==>
    (agp32 fext fbits (SUC t)).command <> 3w
Proof
  rw [] >> Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  `(agp32 fext fbits (SUC t)).command = (agp32_next_state (fext t) s s).command`
    by fs [agp32_command_state_updated_by_agp32_next_state] >>
  `(fext t).error = 0w` by fs [is_mem_def,mem_no_errors_def] >>
  `~s.MEM.MEM_write_mem` by METIS_TAC [Abbr `s`,agp32_MEM_write_mem_MEM_opc_2w] >>
  `~s.MEM.MEM_write_mem_byte` by METIS_TAC [Abbr `s`,agp32_MEM_write_mem_byte_MEM_opc_3w] >>
  `s.state = 0w`
    by (fs [Abbr `s`,enable_stg_def] >> Cases_on_word_value `(agp32 fext fbits t).state` >>
        METIS_TAC [agp32_WB_state_flag_and_state,agp32_state_impossible_values]) >>
  `(fext t).ready`
    by (fs [Abbr `s`,enable_stg_def] >> METIS_TAC [agp32_WB_state_flag_and_fext_ready]) >>
  fs [agp32_next_state_def,Abbr `s`] >>
  IF_CASES_TAC >> fs [] >>
  IF_CASES_TAC >> fs [] >>
  IF_CASES_TAC >> fs []
QED


(** lemmas for acc_res **)
(** state when acc **)
Theorem agp32_state_acc_WB_enable:
  !fext fbits a t I.
    is_mem fext_accessor_circuit (agp32 fext fbits) fext ==>
    enable_stg 5 (agp32 fext fbits t) ==>
    (agp32 fext fbits (SUC t)).WB.WB_opc = 8w ==>
    (agp32 fext fbits (SUC t)).state = 2w
Proof
  rw [] >> Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  `(agp32 fext fbits (SUC t)).state = (agp32_next_state (fext t) s s).state`
    by fs [agp32_command_state_updated_by_agp32_next_state] >>
  `(fext t).error = 0w` by fs [is_mem_def,mem_no_errors_def] >>     
  `s.MEM.MEM_opc = 8w` by gs [agp32_WB_opc_MEM_opc_when_WB_enabled,Abbr `s`] >>
  `s.MEM.MEM_isAcc` by gs [Abbr `s`,agp32_MEM_isAcc_MEM_opc_8w] >>
  `s.state = 0w`
    by (fs [Abbr `s`,enable_stg_def] >> Cases_on_word_value `(agp32 fext fbits t).state` >>
        METIS_TAC [agp32_WB_state_flag_and_state,agp32_state_impossible_values]) >>     
  `(fext t).ready`
    by (fs [Abbr `s`,enable_stg_def] >> METIS_TAC [agp32_WB_state_flag_and_fext_ready]) >>
  fs [agp32_next_state_def] >>
  `~s.MEM.MEM_isInterrupt /\ ~s.MEM.MEM_read_mem /\
  ~s.MEM.MEM_write_mem /\ ~s.MEM.MEM_write_mem_byte`
    by fs [Abbr `s`,agp32_MEM_isAcc_others_F] >> fs []
QED

val _ = export_theory ();
