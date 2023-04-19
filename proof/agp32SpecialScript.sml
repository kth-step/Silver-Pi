open hardwarePreamble translatorTheory translatorLib arithmeticTheory wordsExtraTheory dep_rewrite blastLib bitstringSyntax fcpSyntax listSyntax wordsSyntax agp32StateTheory agp32EnvironmentTheory agp32ProcessorTheory ag32Theory ag32ExtraTheory ag32UtilitiesTheory agp32RelationTheory agp32UpdateTheory agp32InternalTheory agp32_EX_CorrectTheory;

(* correctness of special invariants *)
val _ = new_theory "agp32Special";

val _ = prefer_num ();
val _ = guess_lengths ();


(** when EX is jump, ID is NONE **)
Theorem isJump_hw_op_ID_instr_index_none:
  !I t fext fbits a.
    is_sch I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    isJump_hw_op (agp32 fext fbits (SUC t)) ==>
    I (2,SUC t) = NONE
Proof
  rw [] >> Cases_on `enable_stg 2 (agp32 fext fbits t)` >-
   (Cases_on `isJump_hw_op (agp32 fext fbits t) \/ isJump_isa_op (I' (2,t)) a` >-
     fs [is_sch_def,is_sch_decode_def] >> fs [] >>
    `enable_stg 3 (agp32 fext fbits t)`
      by fs [enable_stg_def,agp32_ID_ID_write_enable_and_ID_EX_write_enable] >>
    `~reg_data_hazard (agp32 fext fbits t)`
      by fs [enable_stg_def,isJump_hw_op_def,
             agp32_ID_ID_write_enable_EX_jump_sel_then_no_reg_data_hazard] >>
    `I' (3,SUC t) = I' (2,t)` by fs [is_sch_def,is_sch_execute_def] >>
    `~isJump_isa_op (I' (3,SUC t)) a` by fs [] >>
    fs [isJump_hw_op_def] >> METIS_TAC [agp32_Rel_ag32_EX_jump_sel_correct]) >>
  Cases_on `enable_stg 3 (agp32 fext fbits t)` >-
   (Cases_on `isJump_hw_op (agp32 fext fbits t)` >-
     METIS_TAC [enable_stg_def,agp32_ID_EX_write_enable_isJump_hw_op_IF_PC_write_enable,
                agp32_IF_PC_write_enable_and_ID_ID_write_enable] >>
    Cases_on `reg_data_hazard (agp32 fext fbits t)` >> fs [] >-
     (`I' (3,SUC t) = NONE` by fs [is_sch_def,is_sch_execute_def] >>
      fs [isJump_hw_op_def] >>
      `isJump_isa_op (I' (3,SUC t)) a` by METIS_TAC [agp32_Rel_ag32_EX_jump_sel_correct] >>
      METIS_TAC [isJump_isa_op_not_none]) >>
    gs [enable_stg_def,agp32_ID_EX_write_enable_no_jump_or_reg_data_hazard_ID_ID_write_enable]) >>
  `isJump_hw_op (agp32 fext fbits (SUC t)) = isJump_hw_op (agp32 fext fbits t)`
    by fs [isJump_hw_op_def,agp32_EX_jump_sel_unchanged_when_EX_disabled] >>
  fs [Rel_def,Inv_Rel_def,is_sch_def,is_sch_disable_def]
QED

(** when EX is jump, IF is NONE **)
Theorem isJump_hw_op_IF_instr_index_none:
  !I t fext fbits a.
    is_sch I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    isJump_hw_op (agp32 fext fbits (SUC t)) ==>
    I (1,SUC t) = NONE
Proof
  rw [] >> Cases_on `enable_stg 1 (agp32 fext fbits t)` >-
   (Cases_on `isJump_hw_op (agp32 fext fbits t)` >-
     (`enable_stg 3 (agp32 fext fbits t)`
        by fs [enable_stg_def,agp32_IF_PC_write_enable_and_ID_EX_write_enable] >>
      `I' (3,SUC t) = NONE` by fs [is_sch_def,is_sch_execute_def] >>
      fs [isJump_hw_op_def] >>
      `isJump_isa_op (I' (3,SUC t)) a` by METIS_TAC [agp32_Rel_ag32_EX_jump_sel_correct] >>
      METIS_TAC [isJump_isa_op_not_none]) >>
    Cases_on `isJump_isa_op (I' (1,t)) a \/ isJump_isa_op (I' (2,t)) a \/ I' (1,t) = NONE` >-
     gs [is_sch_def,is_sch_fetch_def] >> fs [] >>
    `enable_stg 2 (agp32 fext fbits t)`
      by fs [enable_stg_def,agp32_IF_PC_write_enable_and_ID_ID_write_enable] >>
    `I' (2,SUC t) = I' (1,t)` by fs [is_sch_def,is_sch_decode_def] >>
    METIS_TAC [isJump_hw_op_ID_instr_index_none]) >>
  `~enable_stg 2 (agp32 fext fbits t)`
    by gs [enable_stg_def,agp32_IF_PC_write_enable_and_ID_ID_write_enable] >>
  Cases_on `enable_stg 3 (agp32 fext fbits t)` >-
   (Cases_on `isJump_hw_op (agp32 fext fbits t)` >-
     gs [enable_stg_def,agp32_ID_EX_write_enable_isJump_hw_op_IF_PC_write_enable] >>
    Cases_on `reg_data_hazard (agp32 fext fbits t)` >> fs [] >-
     (`I' (3,SUC t) = NONE` by fs [is_sch_def,is_sch_execute_def] >>
      fs [isJump_hw_op_def] >>
      `isJump_isa_op (I' (3,SUC t)) a` by METIS_TAC [agp32_Rel_ag32_EX_jump_sel_correct] >>
      METIS_TAC [isJump_isa_op_not_none]) >>
    gs [enable_stg_def,agp32_ID_EX_write_enable_no_jump_or_reg_data_hazard_ID_ID_write_enable]) >>
  `isJump_hw_op (agp32 fext fbits (SUC t)) = isJump_hw_op (agp32 fext fbits t)`
    by fs [isJump_hw_op_def,agp32_EX_jump_sel_unchanged_when_EX_disabled] >>
  fs [Rel_def,Inv_Rel_def,is_sch_def,is_sch_disable_def]
QED

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
      fs [isJump_hw_op_def] >> METIS_TAC [agp32_Rel_ag32_EX_jump_sel_correct]) >>
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
    by fs [isJump_hw_op_def,agp32_EX_jump_sel_unchanged_when_EX_disabled] >>
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
    fs [isJump_hw_op_def] >> METIS_TAC [is_sch_def,agp32_Rel_ag32_EX_jump_sel_correct]) >>
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
        by fs [isJump_hw_op_def,agp32_EX_jump_sel_unchanged_when_EX_disabled] >> fs []) >>
    fs [enable_stg_def] >>
    METIS_TAC [agp32_IF_PC_write_enable_and_ID_ID_write_enable,
               agp32_ID_EX_write_enable_isJump_hw_op_IF_PC_write_enable]) >>
  fs [] >> Cases_on `~isJump_hw_op (agp32 fext fbits t)` >> fs [] >-
   fs [Rel_def,Inv_Rel_def] >>
  Cases_on `~enable_stg 3 (agp32 fext fbits t)` >-
   (`isJump_hw_op (agp32 fext fbits (SUC t)) = isJump_hw_op (agp32 fext fbits t)`
      by fs [isJump_hw_op_def,agp32_EX_jump_sel_unchanged_when_EX_disabled] >> fs []) >>
  fs [enable_stg_def] >>
  METIS_TAC [agp32_IF_PC_write_enable_and_ID_ID_write_enable,
             agp32_ID_EX_write_enable_isJump_hw_op_IF_PC_write_enable]
QED

Theorem ID_instr_index_NONE_opc_flush_when_enabled:
  !I t fext fbits a.
    is_sch I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    enable_stg 2 (agp32 fext fbits t) ==>
    ~isJump_hw_op (agp32 fext fbits (SUC t)) ==>
    I (2,SUC t) = NONE ==>
    (agp32 fext fbits (SUC t)).ID.ID_opc = 15w
Proof
  rw [] >> `isJump_hw_op (agp32 fext fbits t)` by METIS_TAC [ID_NONE_exists_a_jump] >>
  gs [EX_isJump_hw_op_next_ID_opc]
QED

Theorem ID_instr_index_NONE_opc_flush:
  !I t fext fbits a.
    is_sch I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    ~isJump_hw_op (agp32 fext fbits (SUC t)) ==>
    I (2,SUC t) = NONE ==>
    (agp32 fext fbits (SUC t)).ID.ID_opc = 15w
Proof
  rw [] >> Cases_on `enable_stg 2 (agp32 fext fbits t)` >-
   METIS_TAC [ID_instr_index_NONE_opc_flush_when_enabled] >>
  METIS_TAC [ID_instr_index_NONE_opc_flush_when_disabled]
QED

(** ID_addrA/B/W_disable is true under certain conditions **)
Theorem ID_addr_disable_NONE_flush_when_disabled:
  !I t fext fbits a.
    is_sch I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    ~enable_stg 2 (agp32 fext fbits t) ==>
    ~isJump_hw_op (agp32 fext fbits (SUC t)) ==>
    I (2,SUC t) = NONE ==>
    (agp32 fext fbits (SUC t)).ID.ID_addrA_disable /\
    (agp32 fext fbits (SUC t)).ID.ID_addrB_disable /\
    (agp32 fext fbits (SUC t)).ID.ID_addrW_disable
Proof
  rpt gen_tac >> rpt disch_tac >>
  `I' (2,SUC t) = I' (2,t)` by METIS_TAC [is_sch_def,is_sch_disable_def] >>
  `((agp32 fext fbits (SUC t)).ID.ID_addrA_disable = (agp32 fext fbits t).ID.ID_addrA_disable) /\
  ((agp32 fext fbits (SUC t)).ID.ID_addrB_disable = (agp32 fext fbits t).ID.ID_addrB_disable) /\
  ((agp32 fext fbits (SUC t)).ID.ID_addrW_disable = (agp32 fext fbits t).ID.ID_addrW_disable)`
    by gs [ID_addr_disable_unchanged_when_ID_disabled] >>
  Cases_on `enable_stg 2 (agp32 fext fbits (t-1))` >-
   (Cases_on `~isJump_hw_op (agp32 fext fbits t)` >> fs [] >-
     (`isJump_hw_op (agp32 fext fbits (t − 1))` by fs [Rel_def,Inv_Rel_def] >>
      `(agp32 fext fbits (SUC (t-1))).ID.ID_addrA_disable /\
      (agp32 fext fbits (SUC (t-1))).ID.ID_addrB_disable /\
      (agp32 fext fbits (SUC (t-1))).ID.ID_addrW_disable`
        by fs [EX_isJump_hw_op_next_ID_addr_disable] >> 
      Cases_on `t` >> fs []) >>
    Cases_on `~enable_stg 3 (agp32 fext fbits t)` >-
     (`isJump_hw_op (agp32 fext fbits (SUC t)) = isJump_hw_op (agp32 fext fbits t)`
        by fs [isJump_hw_op_def,agp32_EX_jump_sel_unchanged_when_EX_disabled] >> fs []) >>
    fs [enable_stg_def] >>
    METIS_TAC [agp32_IF_PC_write_enable_and_ID_ID_write_enable,
               agp32_ID_EX_write_enable_isJump_hw_op_IF_PC_write_enable]) >>
  fs [] >> Cases_on `~isJump_hw_op (agp32 fext fbits t)` >> fs [] >-
   fs [Rel_def,Inv_Rel_def] >>
  Cases_on `~enable_stg 3 (agp32 fext fbits t)` >-
   (`isJump_hw_op (agp32 fext fbits (SUC t)) = isJump_hw_op (agp32 fext fbits t)`
      by fs [isJump_hw_op_def,agp32_EX_jump_sel_unchanged_when_EX_disabled] >> fs []) >>
  fs [enable_stg_def] >>
  METIS_TAC [agp32_IF_PC_write_enable_and_ID_ID_write_enable,
             agp32_ID_EX_write_enable_isJump_hw_op_IF_PC_write_enable]
QED

Theorem ID_addr_disable_NONE_flush_when_enabled:
  !I t fext fbits a.
    is_sch I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    enable_stg 2 (agp32 fext fbits t) ==>
    ~isJump_hw_op (agp32 fext fbits (SUC t)) ==>
    I (2,SUC t) = NONE ==>
    (agp32 fext fbits (SUC t)).ID.ID_addrA_disable /\
    (agp32 fext fbits (SUC t)).ID.ID_addrB_disable /\
    (agp32 fext fbits (SUC t)).ID.ID_addrW_disable
Proof
  rw [] >> `isJump_hw_op (agp32 fext fbits t)` by METIS_TAC [ID_NONE_exists_a_jump] >>
  gs [EX_isJump_hw_op_next_ID_addr_disable]
QED

Theorem ID_addr_disable_NONE_flush:
  !I t fext fbits a.
    is_sch I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    ~isJump_hw_op (agp32 fext fbits (SUC t)) ==>
    I (2,SUC t) = NONE ==>
    (agp32 fext fbits (SUC t)).ID.ID_addrA_disable /\
    (agp32 fext fbits (SUC t)).ID.ID_addrB_disable /\
    (agp32 fext fbits (SUC t)).ID.ID_addrW_disable
Proof
  rpt gen_tac >> rpt disch_tac >>
  Cases_on `enable_stg 2 (agp32 fext fbits t)` >-
   METIS_TAC [ID_addr_disable_NONE_flush_when_enabled] >>
  METIS_TAC [ID_addr_disable_NONE_flush_when_disabled]
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

(** EX_opc **)
Theorem EX_instr_index_not_NONE_opc_not_16:
  !I t fext fbits a.
    is_sch I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t − 1)) (agp32 fext fbits t) a t ==>
    I (3,SUC t) <> NONE ==>
    (agp32 fext fbits (SUC t)).EX.EX_opc <> 16w
Proof
  rw [] >> Cases_on `enable_stg 3 (agp32 fext fbits t)` >-
   (Cases_on `isJump_hw_op (agp32 fext fbits t)` >-
     (fs [is_sch_def,is_sch_execute_def] >> METIS_TAC []) >>
    Cases_on `reg_data_hazard (agp32 fext fbits t)` >-
     (fs [is_sch_def,is_sch_execute_def] >> METIS_TAC []) >>
    `I' (3,SUC t) = I' (2,t)` by METIS_TAC [is_sch_def,is_sch_execute_def] >> fs [] >>
    `~(agp32 fext fbits t).EX.EX_NOP_flag`
      by fs [enable_stg_def,agp32_ID_EX_write_enable_no_jump_or_reg_data_hazard_EX_NOP_flag_F] >>
    `(agp32 fext fbits (SUC t)).EX.EX_opc = (agp32 fext fbits t).ID.ID_opc`
      by fs [agp32_EX_opc_ID_opc_when_not_EX_NOP_flag] >> fs [] >>
    rw [agp32_ID_opc_not_16]) >>
  `I' (3,SUC t) = I' (3,t)` by METIS_TAC [is_sch_def,is_sch_disable_def] >>
  fs [agp32_EX_opc_unchanged_when_EX_disabled,Rel_def,Inv_Rel_def]
QED

(** MEM_opc **)
Theorem MEM_instr_index_NONE_opc_flush:
  !I t fext fbits a.
    is_sch I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t − 1)) (agp32 fext fbits t) a t ==>
    I (4,SUC t) = NONE ==>
    (agp32 fext fbits (SUC t)).MEM.MEM_opc = 16w \/ (agp32 fext fbits (SUC t)).MEM.MEM_opc = 15w
Proof
  rw [] >> Cases_on `enable_stg 4 (agp32 fext fbits t)` >-
   (Cases_on `isMemOp_hw_op (agp32 fext fbits t)` >-
     (`(agp32 fext fbits t).MEM.MEM_NOP_flag`
        by fs [enable_stg_def,agp32_MEM_state_flag_isMemOp_hw_op_MEM_NOP_flag] >>
      fs [agp32_MEM_opc_flush_when_MEM_NOP_flag]) >>
    `I' (4,SUC t) = I' (3,t)` by METIS_TAC [is_sch_def,is_sch_memory_def] >>
    `~(agp32 fext fbits t).MEM.MEM_NOP_flag`
      by fs [enable_stg_def,agp32_MEM_state_flag_not_isMemOp_hw_op_MEM_NOP_flag_F] >>
    `(agp32 fext fbits (SUC t)).MEM.MEM_opc = (agp32 fext fbits t).EX.EX_opc`
      by fs [agp32_MEM_opc_EX_opc_when_not_MEM_NOP_flag] >>
    fs [Rel_def,Inv_Rel_def]) >>
  `I' (4,SUC t) = I' (4,t)` by METIS_TAC [is_sch_def,is_sch_disable_def] >>
  fs [agp32_MEM_opc_unchanged_when_MEM_disabled,Rel_def,Inv_Rel_def]
QED

Theorem MEM_instr_index_not_NONE_opc_not_16:
  !I t fext fbits a.
    is_sch I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t − 1)) (agp32 fext fbits t) a t ==>
    I (4,SUC t) <> NONE ==>
    (agp32 fext fbits (SUC t)).MEM.MEM_opc <> 16w
Proof
  rw [] >> Cases_on `enable_stg 4 (agp32 fext fbits t)` >-
   (Cases_on `isMemOp_hw_op (agp32 fext fbits t)` >-
     (fs [is_sch_def,is_sch_memory_def] >> METIS_TAC []) >>
    `I' (4,SUC t) = I' (3,t)` by METIS_TAC [is_sch_def,is_sch_memory_def] >>
    `~(agp32 fext fbits t).MEM.MEM_NOP_flag`
      by fs [enable_stg_def,agp32_MEM_state_flag_not_isMemOp_hw_op_MEM_NOP_flag_F] >>
    `(agp32 fext fbits (SUC t)).MEM.MEM_opc = (agp32 fext fbits t).EX.EX_opc`
      by fs [agp32_MEM_opc_EX_opc_when_not_MEM_NOP_flag] >>
    fs [Rel_def,Inv_Rel_def]) >>
  `I' (4,SUC t) = I' (4,t)` by METIS_TAC [is_sch_def,is_sch_disable_def] >>
  fs [agp32_MEM_opc_unchanged_when_MEM_disabled,Rel_def,Inv_Rel_def]
QED

(** MEM_write_reg **)
Theorem MEM_instr_index_NONE_MEM_not_write_reg:
  !I t fext fbits a.
    is_sch I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (4,SUC t) = NONE ==>
    ~(agp32 fext fbits (SUC t)).MEM.MEM_write_reg
Proof
  rw [] >> Cases_on `enable_stg 4 (agp32 fext fbits t)` >-
   (Cases_on `isMemOp_hw_op (agp32 fext fbits t)` >-
     (`(agp32 fext fbits t).MEM.MEM_NOP_flag`
        by fs [enable_stg_def,agp32_MEM_state_flag_isMemOp_hw_op_MEM_NOP_flag] >>
      fs [agp32_MEM_write_reg_F_when_MEM_NOP_flag]) >>
    `I' (4,SUC t) = I' (3,t)` by METIS_TAC [is_sch_def,is_sch_memory_def] >>
    Q.ABBREV_TAC `s = agp32 fext fbits t` >>
    Q.ABBREV_TAC `s' = procs [agp32_next_state;WB_pipeline] (fext t) s s` >>
    `(agp32 fext fbits (SUC t)).MEM.MEM_write_reg = (MEM_pipeline (fext t) s s').MEM.MEM_write_reg`
      by fs [agp32_MEM_write_reg_updated_by_MEM_pipeline] >>
    `(s'.MEM.MEM_state_flag = s.MEM.MEM_state_flag)`
      by METIS_TAC [Abbr `s`,Abbr `s'`,agp32_same_items_before_MEM_pipeline] >>
    `s'.EX.EX_opc = s.EX.EX_opc`
      by METIS_TAC [Abbr `s`,Abbr `s'`,agp32_same_EX_items_before_MEM_pipeline] >>
    fs [enable_stg_def,MEM_pipeline_def,Rel_def,Inv_Rel_def]) >>
  `I' (4,SUC t) = I' (4,t)` by METIS_TAC [is_sch_def,is_sch_disable_def] >>
  fs [agp32_MEM_write_reg_unchanged_when_MEM_disabled,Rel_def,Inv_Rel_def]
QED

(** WB_opc **)
Theorem WB_instr_index_NONE_opc_flush:
  !I t fext fbits a.
    is_sch I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t − 1)) (agp32 fext fbits t) a t ==>
    I (5,SUC t) = NONE ==>
    (agp32 fext fbits (SUC t)).WB.WB_opc = 16w \/ (agp32 fext fbits (SUC t)).WB.WB_opc = 15w
Proof
  rw [] >> Cases_on `enable_stg 5 (agp32 fext fbits t)` >-
   (`I' (5,SUC t) = I' (4,t)` by METIS_TAC [is_sch_def,is_sch_writeback_def] >>
    `(agp32 fext fbits (SUC t)).WB.WB_opc = (agp32 fext fbits t).MEM.MEM_opc`
      by fs [agp32_WB_opc_MEM_opc_when_WB_enabled] >>
    fs [Rel_def,Inv_Rel_def]) >>
  `I' (5,SUC t) = I' (5,t)` by METIS_TAC [is_sch_def,is_sch_disable_def] >>
  fs [agp32_WB_opc_unchanged_when_WB_disabled,Rel_def,Inv_Rel_def]
QED

Theorem WB_instr_index_not_NONE_opc_not_16:
  !I t fext fbits a.
    is_sch I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t − 1)) (agp32 fext fbits t) a t ==>
    I (5,SUC t) <> NONE ==>
    (agp32 fext fbits (SUC t)).WB.WB_opc <> 16w
Proof
  rw [] >> Cases_on `enable_stg 5 (agp32 fext fbits t)` >-
   (`I' (5,SUC t) = I' (4,t)` by METIS_TAC [is_sch_def,is_sch_writeback_def] >>
    `(agp32 fext fbits (SUC t)).WB.WB_opc = (agp32 fext fbits t).MEM.MEM_opc`
      by fs [agp32_WB_opc_MEM_opc_when_WB_enabled] >>
    fs [Rel_def,Inv_Rel_def]) >>
  `I' (5,SUC t) = I' (5,t)` by METIS_TAC [is_sch_def,is_sch_disable_def] >>
  fs [agp32_WB_opc_unchanged_when_WB_disabled,Rel_def,Inv_Rel_def]
QED

(** WB_write_reg **)
Theorem WB_instr_index_NONE_WB_not_write_reg:
  !I t fext fbits a.
    is_sch I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (5,SUC t) = NONE ==>
    ~(agp32 fext fbits (SUC t)).WB.WB_write_reg
Proof
  rw [] >> Cases_on `enable_stg 5 (agp32 fext fbits t)` >-
   (`I' (5,SUC t) = I' (4,t)` by METIS_TAC [is_sch_def,is_sch_writeback_def] >>
    Q.ABBREV_TAC `s = agp32 fext fbits t` >>
    Q.ABBREV_TAC `s' = procs [agp32_next_state] (fext t) s s` >>
    `(agp32 fext fbits (SUC t)).WB.WB_write_reg = (WB_pipeline (fext t) s s').WB.WB_write_reg`
      by fs [agp32_WB_write_reg_updated_by_WB_pipeline] >>
    `(s'.WB.WB_state_flag = s.WB.WB_state_flag)`
      by METIS_TAC [Abbr `s`,Abbr `s'`,agp32_same_WB_items_before_WB_pipeline] >>
    `s'.MEM.MEM_opc = s.MEM.MEM_opc`
      by METIS_TAC [Abbr `s`,Abbr `s'`,agp32_same_MEM_items_before_WB_pipeline] >>
    fs [enable_stg_def,WB_pipeline_def,Rel_def,Inv_Rel_def]) >>
  `I' (5,SUC t) = I' (5,t)` by METIS_TAC [is_sch_def,is_sch_disable_def] >>
  fs [agp32_WB_write_reg_unchanged_when_WB_disabled,Rel_def,Inv_Rel_def]
QED

(** WB_isOut **)
Theorem WB_instr_index_NONE_WB_not_isOut:
  !I t fext fbits a.
    is_sch I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (5,SUC t) = NONE ==>
    ~(agp32 fext fbits (SUC t)).WB.WB_isOut
Proof
  rw [] >> Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state;WB_pipeline;MEM_pipeline;EX_pipeline;
                            REG_write; ID_pipeline; IF_PC_update; Acc_compute] (fext t) s s` >>
  Q.ABBREV_TAC `s'' = procs [IF_instr_update;ID_opc_func_update;ID_imm_update;ID_data_update;
                             ID_data_check_update;EX_ALU_input_imm_update;EX_ALU_update;
                             EX_SHIFT_update;EX_jump_sel_addr_update;IF_PC_input_update;
                             MEM_ctrl_update] (fext (SUC t)) s' s'` >>
  `(agp32 fext fbits (SUC t)).WB.WB_isOut = (WB_update (fext (SUC t)) s' s'').WB.WB_isOut`
    by fs [agp32_WB_ctrl_items_updated_by_WB_update] >>
  `(s''.WB.WB_state_flag = s.WB.WB_state_flag)`
    by METIS_TAC [Abbr `s`,Abbr `s'`,Abbr `s''`,agp32_same_WB_items_until_WB_update] >>
  Cases_on `enable_stg 5 (agp32 fext fbits t)` >-
    (`s''.WB.WB_opc = (agp32 fext fbits (SUC t)).WB.WB_opc`
       by METIS_TAC [Abbr `s`,Abbr `s'`,agp32_same_WB_items_before_WB_update] >>  
     gs [enable_stg_def,WB_update_def] >>
     `((agp32 fext fbits (SUC t)).WB.WB_opc = 16w) \/ ((agp32 fext fbits (SUC t)).WB.WB_opc = 15w)`
       by METIS_TAC [WB_instr_index_NONE_opc_flush] >> fs []) >>
  `I' (5,SUC t) = I' (5,t)` by METIS_TAC [is_sch_def,is_sch_disable_def] >>
  `(s''.WB.WB_isOut = s.WB.WB_isOut)`
    by METIS_TAC [Abbr `s`,Abbr `s'`,Abbr `s''`,agp32_same_WB_items_until_WB_update] >>
  gs [enable_stg_def,WB_update_def,Rel_def,Inv_Rel_def]
QED

(** instr index relation between IF and WB stages **)
Theorem IF_instr_index_with_WB_instr:
  !I t fext fbits a.
    is_sch I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (1,SUC t) <> NONE ==>
    I (5,SUC t) <> NONE ==>
    (THE (I (1,SUC t)) > THE (I (5,SUC t))) /\ (THE (I (1,SUC t)) < THE (I (5,SUC t)) + 5)
Proof
  rpt gen_tac >> rpt disch_tac >>
  Cases_on `enable_stg 1 (agp32 fext fbits t)` >-
   (Cases_on `isJump_hw_op (agp32 fext fbits t)` >-
     (`I' (1,SUC t) = SOME (THE (I' (3,t)) + 1)` by fs [is_sch_def,is_sch_fetch_def] >>
      `isJump_isa_op (I' (3,t)) a` by fs [Rel_def,EX_Rel_spec_def,isJump_hw_op_def] >>
      `I' (3,t) <> NONE` by METIS_TAC [isJump_isa_op_not_none] >>
      `enable_stg 5 (agp32 fext fbits t)`
        by fs [enable_stg_def,agp32_IF_PC_write_enable_and_WB_flag] >>
      `I' (5,SUC t) = I' (4,t)` by fs [is_sch_def,is_sch_writeback_def] >> fs [] >>
      `(THE (I' (3,t)) > THE (I' (4,t))) /\ (THE (I' (3,t)) < THE (I' (4,t)) + 2)`
        by METIS_TAC [EX_instr_index_with_MEM_instr] >> fs []) >>
    Cases_on `isJump_isa_op (I' (1,t)) a \/ isJump_isa_op (I' (2,t)) a \/ I' (1,t) = NONE` >-
     gs [is_sch_def,is_sch_fetch_def] >> fs [] >>
    `enable_stg 5 (agp32 fext fbits t)`
      by fs [enable_stg_def,agp32_IF_PC_write_enable_and_WB_flag] >>
    `I' (5,SUC t) = I' (4,t)` by fs [is_sch_def,is_sch_writeback_def] >> fs [] >>
    `(THE (I' (1,t)) > THE (I' (4,t))) /\ (THE (I' (1,t)) < THE (I' (4,t)) + 4)`
      by METIS_TAC [IF_instr_index_with_MEM_instr] >> fs [is_sch_def,is_sch_fetch_def]) >>
  Cases_on `enable_stg 5 (agp32 fext fbits t)` >-
   (`I' (5,SUC t) = I' (4,t)` by fs [is_sch_def,is_sch_writeback_def] >>
    `I' (1,SUC t) = I' (1,t)` by fs [is_sch_def,is_sch_disable_def] >> fs [] >>
    `(THE (I' (1,t)) > THE (I' (4,t))) /\ (THE (I' (1,t)) < THE (I' (4,t)) + 4)`
      by METIS_TAC [IF_instr_index_with_MEM_instr] >> fs []) >>
  `I' (5,SUC t) = I' (5,t) /\ I' (1,SUC t) = I' (1,t)`
    by fs [is_sch_def,is_sch_disable_def] >> fs [Rel_def,Inv_Rel_def]
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

(** similar as above but for t **)
Theorem IF_instr_index_with_WB_instr_ID_EX_MEM_NONE_t:
  !I t fext fbits a.
    is_sch I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (1,t) <> NONE ==>
    I (2,t) = NONE ==>
    I (3,t) = NONE ==>
    I (4,t) = NONE ==>
    I (5,t) <> NONE ==>
    (THE (I (1,t)) > THE (I (5,t))) /\ (THE (I (1,t)) < THE (I (5,t)) + 2)
Proof
  rw [Rel_def] >> fs [Inv_Rel_def]
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
             ID_instr_index_NONE_opc_flush,ID_addr_disable_NONE_flush,EX_instr_index_NONE_opc_flush,
             isJump_hw_op_IF_instr_index_none,isJump_hw_op_ID_instr_index_none,
             EX_instr_index_NONE_EX_not_write_reg,IF_instr_index_with_WB_instr,
             MEM_instr_index_NONE_opc_flush,MEM_instr_index_NONE_MEM_not_write_reg,
             WB_instr_index_NONE_opc_flush,WB_instr_index_NONE_WB_not_write_reg,
             WB_instr_index_NONE_WB_not_isOut,EX_instr_index_not_NONE_opc_not_16,
             MEM_instr_index_not_NONE_opc_not_16,WB_instr_index_not_NONE_opc_not_16,
             IF_instr_index_with_WB_instr_ID_EX_MEM_NONE,
             IF_instr_index_with_WB_instr_ID_EX_MEM_NONE_t] 
QED

val _ = export_theory ();
