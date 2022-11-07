open hardwarePreamble translatorTheory translatorLib arithmeticTheory wordsExtraTheory dep_rewrite blastLib bitstringSyntax fcpSyntax listSyntax wordsSyntax agp32StateTheory agp32EnvironmentTheory agp32ProcessorTheory ag32Theory ag32ExtraTheory ag32UtilitiesTheory agp32RelationTheory agp32UpdateTheory agp32InternalTheory agp32_EX_CorrectTheory;

(* correctness of special invariants *)
val _ = new_theory "agp32Special";

val _ = prefer_num ();
val _ = guess_lengths ();


(** when ID and EX are not jump, IF is not NONE **)
Theorem IF_instr_index_not_none:
  !I t fext fbits a.
    is_sch I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    ~isJump_hw_op (agp32 fext fbits (SUC t)) ==>
    ~isJump_isa_op (I (2,SUC t)) a ==>
    I (1,SUC t) <> NONE
Proof
  rw [] >> Cases_on `enable_stg 1 (agp32 fext fbits t)` >-
   (Cases_on `isJump_hw_op (agp32 fext fbits t)` >-
     fs [is_sch_def,is_sch_fetch_def] >>
    Cases_on `isJump_isa_op (I' (1,t)) a` >-
     (`enable_stg 2 (agp32 fext fbits t)`
        by fs [enable_stg_def,agp32_IF_PC_write_enable_and_ID_ID_write_enable] >>
      `~isJump_isa_op (I' (2,t)) a` by METIS_TAC [IF_instr_isJump_ID_instr_not_isJump] >>
      `I' (2,SUC t) = I' (1,t)` by fs [is_sch_def,is_sch_decode_def] >> fs []) >>
    Cases_on `isJump_isa_op (I' (2,t)) a` >-
     (`enable_stg 3 (agp32 fext fbits t)`
        by fs [enable_stg_def,agp32_IF_PC_write_enable_and_ID_EX_write_enable] >>
      `~reg_data_hazard (agp32 fext fbits t)`
        by fs [enable_stg_def,isJump_hw_op_def,
               agp32_IF_PC_write_enable_EX_jump_sel_then_no_reg_data_hazard] >>
      `I' (3,SUC t) = I' (2,t)` by fs [is_sch_def,is_sch_execute_def] >>
      `isJump_isa_op (I' (3,SUC t)) a` by fs [] >>
      cheat) >>
    Cases_on `I' (1,t) = NONE` >> fs [] >>
    fs [is_sch_def,is_sch_fetch_def] >>
    fs [Rel_def,Inv_Rel_def]) >>
  `~enable_stg 2 (agp32 fext fbits t)`
    by METIS_TAC [enable_stg_def,agp32_IF_PC_write_enable_and_ID_ID_write_enable] >>  
  fs [is_sch_def,is_sch_disable_def] >>
  Cases_on `enable_stg 3 (agp32 fext fbits t)` >-
   (Cases_on `isJump_hw_op (agp32 fext fbits t)` >> fs [] >-
     METIS_TAC [enable_stg_def,agp32_ID_EX_write_enable_isJump_hw_op_IF_PC_write_enable] >>
    fs [Rel_def,Inv_Rel_def] >> METIS_TAC []) >>
  `isJump_hw_op (agp32 fext fbits (SUC t)) = isJump_hw_op (agp32 fext fbits t)`
    by cheat >>
  fs [Rel_def,Inv_Rel_def] >> METIS_TAC []
QED

(** Jump in the EX stage under special ID conditions  **)
Theorem ID_NONE_exists_a_jump:
  !I fext fbits a t.
    is_sch I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    enable_stg 2 (agp32 fext fbits t) ==>
    ~isJump_hw_op (agp32 fext fbits (SUC t)) ==>
    I (2,SUC t) = NONE ==>
    isJump_hw_op (agp32 fext fbits t)
Proof
  rw [is_sch_def] >>
  Cases_on `isJump_hw_op (agp32 fext fbits t)` >> fs [] >>
  Cases_on `isJump_isa_op (I' (2,t)) a` >-
   (`enable_stg 3 (agp32 fext fbits t)`
      by fs [enable_stg_def,agp32_ID_ID_write_enable_and_ID_EX_write_enable] >>
    `~reg_data_hazard (agp32 fext fbits t)`
      by fs [enable_stg_def,isJump_hw_op_def,
             agp32_ID_ID_write_enable_EX_jump_sel_then_no_reg_data_hazard] >>
    `I' (3,SUC t) = I' (2,t)` by fs [is_sch_execute_def] >> rw [] >>
    `isJump_isa_op (I' (3,SUC t)) a` by fs [] >>
    cheat) >>
  `I' (2,SUC t) = I' (1,t)` by METIS_TAC [is_sch_decode_def] >> fs [] >>
  Cases_on `t` >> fs [] >-
   fs [enable_stg_def,agp32_init_ctrl_flags] >>
  fs [Rel_def,Inv_Rel_def]
QED

(** there exists a jump at t-1 when I (3,SUC t) = I (2,t) = NONE **)
Theorem EX_NONE_previous_jump_special:
  !I fext fbits a t.
    is_sch I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    enable_stg 2 (agp32 fext fbits t) ==>
    enable_stg 3 (agp32 fext fbits (SUC t)) ==>
    ~isJump_hw_op (agp32 fext fbits (SUC t)) ==>
    ~reg_data_hazard (agp32 fext fbits (SUC t)) ==>
    I (3,SUC (SUC t)) = NONE ==>
    isJump_hw_op (agp32 fext fbits t)
Proof
  rw [] >>
  `I' (3,SUC (SUC t)) = I' (2,SUC t)` by METIS_TAC [is_sch_def,is_sch_execute_def] >>
  METIS_TAC [ID_NONE_exists_a_jump]
QED

(** ID_opc is 15 under certain conditions **)
Theorem ID_instr_index_NONE_opc_flush_when_disabled:
  !I t fext fbits a.
    is_sch I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    ~enable_stg 2 (agp32 fext fbits t) ==>
    ~isJump_hw_op (agp32 fext fbits (SUC t)) ==>
    I (2,SUC t) = NONE ==>
    (agp32 fext fbits (SUC t)).ID.ID_opc = 15w
Proof
  rw [] >> `I' (2,SUC t) = I' (2,t)` by METIS_TAC [is_sch_def,is_sch_disable_def] >>
  `(agp32 fext fbits (SUC t)).ID.ID_opc = (agp32 fext fbits t).ID.ID_opc`
    by fs [ID_opc_unchanged_when_ID_disabled] >>
  Cases_on `enable_stg 2 (agp32 fext fbits (t-1))` >-
   (Cases_on `~isJump_hw_op (agp32 fext fbits t)` >> fs [] >-
     (`isJump_hw_op (agp32 fext fbits (t − 1))` by fs [Rel_def,Inv_Rel_def] >>
      `(agp32 fext fbits (SUC (t-1))).ID.ID_opc = 15w` by fs [EX_isJump_hw_op_next_ID_opc] >>
      Cases_on `t` >> fs []) >>
    Cases_on `~enable_stg 3 (agp32 fext fbits t)` >-
     (`isJump_hw_op (agp32 fext fbits (SUC t)) = isJump_hw_op (agp32 fext fbits t)`
        by cheat >> fs []) >>
    fs [enable_stg_def] >>
    METIS_TAC [agp32_IF_PC_write_enable_and_ID_ID_write_enable,
               agp32_ID_EX_write_enable_isJump_hw_op_IF_PC_write_enable]) >>
  fs [] >> Cases_on `~isJump_hw_op (agp32 fext fbits t)` >> fs [] >-
   fs [Rel_def,Inv_Rel_def] >>
  Cases_on `~enable_stg 3 (agp32 fext fbits t)` >-
   (`isJump_hw_op (agp32 fext fbits (SUC t)) = isJump_hw_op (agp32 fext fbits t)`
      by cheat >> fs []) >>
  fs [enable_stg_def] >>
  METIS_TAC [agp32_IF_PC_write_enable_and_ID_ID_write_enable,
             agp32_ID_EX_write_enable_isJump_hw_op_IF_PC_write_enable]
QED

(** EX_opc is flushed **)
Theorem EX_instr_index_NONE_opc_flush:
  !I t fext fbits a.
    is_sch I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (3,SUC t) = NONE ==>
    ((agp32 fext fbits (SUC t)).EX.EX_opc = 16w) \/ ((agp32 fext fbits (SUC t)).EX.EX_opc = 15w)
Proof
  rw [] >> Cases_on `enable_stg 3 (agp32 fext fbits t)` >-
   (Cases_on `isJump_hw_op (agp32 fext fbits t)` >-
     (`(agp32 fext fbits t).EX.EX_NOP_flag`
        by fs [enable_stg_def,agp32_ID_EX_write_enable_isJump_hw_op_EX_NOP_flag] >>
      fs [agp32_EX_opc_flush_when_EX_NOP_flag]) >>
    Cases_on `reg_data_hazard (agp32 fext fbits t)` >-
     (`(agp32 fext fbits t).EX.EX_NOP_flag`
        by fs [enable_stg_def,agp32_ID_EX_write_enable_reg_data_hazard_EX_NOP_flag] >>
      fs [agp32_EX_opc_flush_when_EX_NOP_flag]) >>
    `I' (3,SUC t) = I' (2,t)` by METIS_TAC [is_sch_def,is_sch_execute_def] >> fs [] >>
    `~(agp32 fext fbits t).EX.EX_NOP_flag`
      by fs [enable_stg_def,agp32_ID_EX_write_enable_no_jump_or_reg_data_hazard_EX_NOP_flag_F] >>
    `(agp32 fext fbits (SUC t)).EX.EX_opc = (agp32 fext fbits t).ID.ID_opc`
      by fs [agp32_EX_opc_ID_opc_when_not_EX_NOP_flag] >> fs [] >>
    Cases_on `enable_stg 2 (agp32 fext fbits (t-1))` >-
     (`isJump_hw_op (agp32 fext fbits (t-1))` by fs [Rel_def,Inv_Rel_def] >>
      `(agp32 fext fbits (SUC (t-1))).ID.ID_opc = 15w` by fs [EX_isJump_hw_op_next_ID_opc] >>
      Cases_on `t` >> fs []) >>
    fs [Rel_def,Inv_Rel_def]) >>
  `I' (3,SUC t) = I' (3,t)` by METIS_TAC [is_sch_def,is_sch_disable_def] >>
  fs [agp32_EX_opc_unchanged_when_EX_disabled,Rel_def,Inv_Rel_def]
QED

(** EX_write_reg **)
Theorem EX_instr_index_NONE_EX_not_write_reg:
  !I t fext fbits a.
    is_sch I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (3,SUC t) = NONE ==>
    ~(agp32 fext fbits (SUC t)).EX.EX_write_reg
Proof
  rw [is_sch_def] >>
  Cases_on `enable_stg 3 (agp32 fext fbits t)` >-
   (Cases_on `isJump_hw_op (agp32 fext fbits t)` >-
     (`(agp32 fext fbits t).EX.EX_NOP_flag`
        by fs [enable_stg_def,agp32_ID_EX_write_enable_isJump_hw_op_EX_NOP_flag] >>
      fs [agp32_EX_write_reg_F_when_EX_NOP_flag]) >>
    Cases_on `reg_data_hazard (agp32 fext fbits t)` >-
     (`(agp32 fext fbits t).EX.EX_NOP_flag`
        by fs [enable_stg_def,agp32_ID_EX_write_enable_reg_data_hazard_EX_NOP_flag] >>
      fs [agp32_EX_write_reg_F_when_EX_NOP_flag]) >>
    `((agp32 fext fbits (SUC t)).EX.EX_opc = 16w) \/ ((agp32 fext fbits (SUC t)).EX.EX_opc = 15w)`
      by METIS_TAC [is_sch_def,EX_instr_index_NONE_opc_flush] >>
    `~(agp32 fext fbits t).EX.EX_NOP_flag`
      by fs [enable_stg_def,agp32_ID_EX_write_enable_no_jump_or_reg_data_hazard_EX_NOP_flag_F] >>
    fs [agp32_EX_write_reg_F_when_EX_opc_flushed]) >>
  `I' (3,SUC t) = I' (3,t)` by METIS_TAC [is_sch_disable_def] >>
  fs [agp32_EX_write_reg_unchanged_when_EX_disabled,Rel_def,Inv_Rel_def]
QED

(** instr index relation between IF and WB stages when ID, EX and MEM are NONE **)
Theorem IF_instr_index_with_WB_instr_ID_EX_MEM_NONE:
  !I t fext fbits a.
    is_sch I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (1,SUC t) <> NONE ==>
    I (2,SUC t) = NONE ==>
    I (3,SUC t) = NONE ==>
    I (4,SUC t) = NONE ==>
    I (5,SUC t) <> NONE ==>
    (THE (I (1,SUC t)) > THE (I (5,SUC t))) /\ (THE (I (1,SUC t)) < THE (I (5,SUC t)) + 2)
Proof
  rpt gen_tac >> rpt disch_tac >>
  Cases_on `enable_stg 1 (agp32 fext fbits t)` >-
   (Cases_on `isJump_hw_op (agp32 fext fbits t)` >-
     (`I' (1,SUC t) = SOME (THE (I' (3,t)) + 1)` by fs [is_sch_def,is_sch_fetch_def] >>
      `isJump_isa_op (I' (3,t)) a` by fs [Rel_def,EX_Rel_spec_def,isJump_hw_op_def] >>
      `I' (3,t) <> NONE` by METIS_TAC [isJump_isa_op_not_none] >>
      `enable_stg 4 (agp32 fext fbits t)`
        by fs [enable_stg_def,agp32_IF_PC_write_enable_and_MEM_flag] >>
      `enable_stg 3 (agp32 fext fbits t)`
        by fs [enable_stg_def,agp32_IF_PC_write_enable_and_ID_EX_write_enable] >>
      Cases_on `isMemOp_hw_op (agp32 fext fbits t)` >-
       (fs [enable_stg_def] >>
        METIS_TAC [MEM_stg_op_agp32_ID_EX_write_disable]) >>
      `I' (4,SUC t) = I' (3,t)` by METIS_TAC [is_sch_def,is_sch_memory_def] >> fs []) >>
    Cases_on `isJump_isa_op (I' (1,t)) a \/ isJump_isa_op (I' (2,t)) a \/ I' (1,t) = NONE` >-
     (fs [is_sch_def,is_sch_fetch_def,is_sch_execute_def] >> METIS_TAC []) >> fs [] >>
    `enable_stg 2 (agp32 fext fbits t)`
      by fs [enable_stg_def,agp32_IF_PC_write_enable_and_ID_ID_write_enable] >>
    `I' (2,SUC t) = I' (1,t)` by METIS_TAC [is_sch_def,is_sch_decode_def] >> fs []) >>
  `~enable_stg 2 (agp32 fext fbits t)`
    by METIS_TAC [enable_stg_def,agp32_IF_PC_write_enable_and_ID_ID_write_enable] >>
  Cases_on `enable_stg 5 (agp32 fext fbits t)` >-
   (`I' (5,SUC t) = I' (4,t)` by fs [is_sch_def,is_sch_writeback_def] >>
    Cases_on `~enable_stg 3 (agp32 fext fbits t)` >> fs [] >-
     (`I' (1,SUC t) = I' (1,t) /\ I' (2,SUC t) = I' (2,t) /\ I' (3,SUC t) = I' (3,t)`
        by METIS_TAC [is_sch_def,is_sch_disable_def] >> fs [] >>
      METIS_TAC [IF_instr_index_with_MEM_instr_ID_EX_NONE]) >>
    `enable_stg 4 (agp32 fext fbits t)`
      by fs [enable_stg_def,agp32_MEM_state_flag_eq_WB_state_flag] >>
    `~isMemOp_hw_op (agp32 fext fbits t)`
      by fs [enable_stg_def,agp32_ID_EX_write_enable_no_MEM_stg_op] >>
    `I' (4,SUC t) = I' (3,t)` by METIS_TAC [is_sch_def,is_sch_memory_def] >> fs [] >>
    `I' (1,SUC t) = I' (1,t) /\ I' (2,SUC t) = I' (2,t)`
      by METIS_TAC [is_sch_def,is_sch_disable_def] >> fs [] >>
    METIS_TAC [IF_instr_index_with_MEM_instr_ID_EX_NONE]) >>
  `~enable_stg 4 (agp32 fext fbits t)` by fs [enable_stg_def,agp32_MEM_state_flag_eq_WB_state_flag] >>
  `~enable_stg 3 (agp32 fext fbits t)`
    by fs [enable_stg_def,agp32_MEM_state_flag_F_and_ID_EX_write_disable] >>
  `I' (1,SUC t) = I' (1,t) /\ I' (2,SUC t) = I' (2,t) /\ I' (3,SUC t) = I' (3,t) /\
  I' (4,SUC t) = I' (4,t) /\ I' (5,SUC t) = I' (5,t)`
    by METIS_TAC [is_sch_def,is_sch_disable_def] >>
  fs [Rel_def,Inv_Rel_def]
QED


(* Inv_Rel *)
Theorem agp32_Rel_ag32_Inv_Rel_correct:
  !fext fbits a t I.
    is_sch I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    Inv_Rel I (agp32 fext fbits t) (agp32 fext fbits (SUC t)) a (SUC t)
Proof
  rw [Inv_Rel_def] >>
  METIS_TAC [IF_instr_index_not_none,ID_NONE_exists_a_jump,EX_NONE_previous_jump_special,
             ID_instr_index_NONE_opc_flush_when_disabled,EX_instr_index_NONE_opc_flush,
             EX_instr_index_NONE_EX_not_write_reg,IF_instr_index_with_WB_instr_ID_EX_MEM_NONE]
QED

val _ = export_theory ();
