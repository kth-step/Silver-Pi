open hardwarePreamble translatorTheory translatorLib arithmeticTheory wordsExtraTheory dep_rewrite blastLib bitstringSyntax fcpSyntax listSyntax wordsSyntax agp32StateTheory agp32EnvironmentTheory agp32ProcessorTheory ag32Theory ag32ExtraTheory ag32UtilitiesTheory agp32RelationTheory agp32UpdateTheory agp32InternalTheory;

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
  rw [] >> rw [] >> Q.ABBREV_TAC `s = agp32 fext fbits t` >>
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
  rw [] >> rw [] >> Q.ABBREV_TAC `s = agp32 fext fbits t` >>
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
    MEM_Rel (fext (SUC t)) (agp32 fext fbits (SUC t)) a (THE (I (4,SUC t)))
Proof
  rw [MEM_Rel_def,is_sch_def] >>
  fs [agp32_Rel_ag32_MEM_PC_correct,agp32_Rel_ag32_MEM_addrW_correct,
      agp32_Rel_ag32_MEM_data_correct,agp32_Rel_ag32_MEM_opc_correct,
      agp32_Rel_ag32_MEM_imm_correct_not_LoadUpperConstant,
      agp32_Rel_ag32_MEM_imm_correct_LoadUpperConstant,
      agp32_Rel_ag32_MEM_ALU_res_correct,agp32_Rel_ag32_MEM_SHIFT_res_correct,
      agp32_Rel_ag32_MEM_write_reg_correct,agp32_Rel_ag32_MEM_read_mem_correct,
      agp32_Rel_ag32_MEM_write_mem_correct,agp32_Rel_ag32_MEM_write_mem_byte_correct,
      agp32_Rel_ag32_MEM_isAcc_correct,agp32_Rel_ag32_MEM_isInterrupt_correct] >>
  cheat
QED


val _ = export_theory ();
