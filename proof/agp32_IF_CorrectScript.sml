open hardwarePreamble translatorTheory translatorLib arithmeticTheory dep_rewrite blastLib bitstringSyntax fcpSyntax listSyntax wordsSyntax agp32StateTheory agp32EnvironmentTheory agp32ProcessorTheory ag32Theory ag32ExtraTheory ag32UtilitiesTheory agp32RelationTheory agp32UpdateTheory agp32InternalTheory agp32StepLib;

(* correctness of IF stage and related items against the ISA *)
val _ = new_theory "agp32_IF_Correct";

val _ = prefer_num ();
val _ = guess_lengths ();


(* lemma about the scheduling function I *)
(** instr index relation between IF and EX stages **)
Theorem IF_instr_index_with_EX_instr:
  !I t fext fbits a.
    is_sch_init I ==>
    is_sch_fetch I (agp32 fext fbits) a ==>
    is_sch_other I (agp32 fext fbits) ==>
    is_sch_disable I (agp32 fext fbits) ==>
    I (1,t) <> NONE ==>
    (THE (I (1,t)) + 1 > THE (I (3,t))) /\
    (THE (I (1,t)) < THE (I (3,t)) + 3)
Proof
  rpt gen_tac >> rpt disch_tac >>
  Induct_on `t` >-
   fs [is_sch_init_def] >>
  Cases_on `enable_stg 1 (agp32 fext fbits t)` >-
   (fs [is_sch_fetch_def] >> disch_tac >>
    Cases_on `isJump_isa (FUNPOW Next (THE (I' (3,t)) − 1) a)` >-
     (fs [] >>
      `enable_stg 3 (agp32 fext fbits t)`
        by fs [enable_stg_def,agp32_IF_PC_write_enable_and_EX_MEM_flags] >>
      fs [is_sch_other_def]) >>
    Cases_on `isJump_isa (FUNPOW Next (THE (I' (1,t)) - 1) a) \/
    isJump_isa (FUNPOW Next (THE (I' (2,t)) - 1) a) \/ I' (1,t) = NONE \/ THE (I' (1,t)) = 0` >-
     METIS_TAC [] >>
    fs [] >>
    `enable_stg 3 (agp32 fext fbits t)`
      by fs [enable_stg_def,agp32_IF_PC_write_enable_and_EX_MEM_flags] >>
    fs [is_sch_other_def]) >>
  fs [is_sch_disable_def] >> strip_tac >>
  `~enable_stg 3 (agp32 fext fbits t)`
    by fs [enable_stg_def,agp32_IF_PC_write_disable_and_EX_disable] >> fs []
QED

(** instr index relation between IF and MEM stages **)
Theorem IF_instr_index_big_then_MEM:
  !I t fext fbits a.
    is_sch_init I ==>
    is_sch_fetch I (agp32 fext fbits) a ==>
    is_sch_other I (agp32 fext fbits) ==>
    is_sch_disable I (agp32 fext fbits) ==>
    enable_stg 1 (agp32 fext fbits t) ==>
    I (1,SUC t) <> NONE ==>
    (THE (I (1,SUC t)) > THE (I (4,SUC t))) /\
    (THE (I (1,SUC t)) < THE (I (4,SUC t)) + 4)
Proof
  rpt gen_tac >>
  rpt disch_tac >>
  Cases_on `isJump_isa (FUNPOW Next (THE (I' (3,t)) − 1) a)` >-
   (`I' (1,SUC t) = SOME (THE (I' (3,t)) + 1)` by fs [is_sch_fetch_def] >>
    `enable_stg 4 (agp32 fext fbits t)`
      by fs [enable_stg_def,agp32_IF_PC_write_enable_and_EX_MEM_flags] >>
    `4 <> 1 /\ 4 <> 2` by rw [] >>
    `I' (4,SUC t) = SOME (THE (I' (4-1,t)))` by METIS_TAC [is_sch_other_def] >> fs []) >>
  Cases_on `isJump_isa (FUNPOW Next (THE (I' (1,t)) - 1) a) \/
  isJump_isa (FUNPOW Next (THE (I' (2,t)) - 1) a) \/ I' (1,t) = NONE \/ THE (I' (1,t)) = 0` >-
   METIS_TAC [is_sch_fetch_def] >> fs [] >>
  `enable_stg 4 (agp32 fext fbits t)`
    by fs [enable_stg_def,agp32_IF_PC_write_enable_and_EX_MEM_flags] >>
  `4 <> 1 /\ 4 <> 2` by rw [] >>
  `I' (4,SUC t) = SOME (THE (I' (4-1,t)))` by METIS_TAC [is_sch_other_def] >>
  `I' (1,SUC t) = SOME (THE (I' (1,t)) + 1)` by METIS_TAC [is_sch_fetch_def] >> fs [] >>
  `(THE (I' (1,t)) + 1 > THE (I' (3,t))) /\
  (THE (I' (1,t)) < THE (I' (3,t)) + 3)` by METIS_TAC [IF_instr_index_with_EX_instr] >> fs []
QED


(* IF related items *)
(** PC updated by IF between ISA and circuit states **)
Theorem agp32_Rel_ag32_IF_PC_correct:
  !fext fbits a t I.
    is_sch_fetch I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    enable_stg 1 (agp32 fext fbits t) ==>
    reg_data_vaild 3 (agp32 fext fbits t) ==>
    I (1,SUC t) <> NONE ==>
    (agp32 fext fbits (SUC t)).PC = (FUNPOW Next (THE (I (1,SUC t)) - 1) a).PC
Proof
  rw [] >> Q.ABBREV_TAC `s = agp32 fext fbits t` >>             
  Q.ABBREV_TAC `s' = procs [agp32_next_state;WB_pipeline;MEM_pipeline;EX_pipeline;
                            REG_write;ID_pipeline] (fext t) s s` >>
  `(agp32 fext fbits (SUC t)).PC = (IF_PC_update (fext t) s s').PC`
    by fs [agp32_PC_updated_by_IF_PC_update,Abbr `s`,Abbr `s'`] >> rw [] >>
  `s.IF.IF_PC_write_enable` by fs [enable_stg_def] >>
  `(s'.IF.IF_PC_write_enable <=> s.IF.IF_PC_write_enable) /\
  (s'.IF.IF_PC_input = s.IF.IF_PC_input)`
    by METIS_TAC [agp32_same_IF_items_until_ID_pipeline,Abbr `s`,Abbr `s'`] >>
  rw [IF_PC_update_def] >>
  `s.EX.EX_jump_sel <=> isJump_isa (FUNPOW Next (THE (I' (3,t)) - 1) a)`
    by fs [Rel_def,EX_Rel_spec_def] >>
  Cases_on `s.EX.EX_jump_sel` >> fs [Rel_def,is_sch_fetch_def,IF_Rel_def] >>
  Cases_on `I' (1,t) <> NONE` >> fs [] >-
   (Cases_on `isJump_isa (FUNPOW Next (THE (I' (1,t)) - 1) a) \/
    isJump_isa (FUNPOW Next (THE (I' (2,t)) - 1) a) \/ THE (I' (1,t)) = 0` >-
     METIS_TAC [Abbr `s`,enable_stg_def] >>
    `I' (1,SUC t) = SOME (THE (I' (1,t)) + 1)` by METIS_TAC [Abbr `s`,enable_stg_def] >> fs [] >>
    Q.ABBREV_TAC `i = THE (I' (1,t))` >>
    Cases_on `i` >> fs [] >>
    rw [FUNPOW_SUC] >>  METIS_TAC [ag32_not_isJump_isa_Next_PC]) >>
  fs [Abbr `s`,enable_stg_def] >> METIS_TAC []
QED

(** IF_instr **)
Theorem agp32_Rel_ag32_IF_instr_correct:
  !fext fbits a t I.
    SC_self_mod_isa a ==>
    is_mem fext_accessor_circuit (agp32 fext fbits) fext ==>
    is_sch_init I ==>
    is_sch_fetch I (agp32 fext fbits) a ==>
    is_sch_other I (agp32 fext fbits) ==>
    is_sch_disable I (agp32 fext fbits) ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    enable_stg 1 (agp32 fext fbits t) ==>
    reg_data_vaild 3 (agp32 fext fbits t) ==>
    I (1,SUC t) <> NONE ==>
    (fext (SUC t)).ready ==>
    (agp32 fext fbits (SUC t)).IF.IF_instr = instr (FUNPOW Next (THE (I (1,SUC t)) - 1) a)
Proof
  rw [] >>
  `?s s'. (agp32 fext fbits (SUC t)).IF.IF_instr =
  (IF_instr_update (fext (SUC t)) s s').IF.IF_instr`
    by rw [agp32_IF_instr_updated_by_IF_instr_update] >>
  rw [IF_instr_update_def,instr_def] >>
  `(fext t).ready` by METIS_TAC [enable_stg_def,agp32_IF_PC_write_enable_and_fext_ready] >>
  last_assum (assume_tac o is_mem_def_mem_no_errors) >>
  Cases_on_word_value `(agp32 fext fbits (SUC t)).command` >>
  fs [agp32_command_impossible_values] >-
   (** different command values **)
   ((** 4: interrupt and read instr **)
   last_assum (mp_tac o is_mem_data_flush `SUC t`) >> rw [] >>
   Cases_on `m` >> fs [] >-
    (`(agp32 fext fbits (SUC t)).PC = (FUNPOW Next (THE (I'(1,SUC t)) - 1) a).PC`
       by METIS_TAC [agp32_Rel_ag32_IF_PC_correct] >> fs [] >>
     `(fext (SUC t)).mem = (FUNPOW Next (THE (I' (4,SUC t))) a).MEM` by cheat >> fs [] >>
     `THE (I' (1,SUC t)) > THE (I' (4,SUC t)) /\
     THE (I' (1,SUC t)) < THE (I' (4,SUC t)) + 4` by METIS_TAC [IF_instr_index_big_then_MEM] >>
     METIS_TAC [SC_self_mod_isa_not_affect_fetched_instr]) >>
   (** multiple cycles **)
   `~(fext (0+SUC t)).ready` by fs [] >> fs []) >-
   ((** 3: write memory and read instr **)
   last_assum (mp_tac o is_mem_data_write `SUC t`) >> rw [] >>
   Cases_on `m` >> fs [] >-
    (`(agp32 fext fbits (SUC t)).PC = (FUNPOW Next (THE (I'(1,SUC t)) - 1) a).PC`
       by METIS_TAC [agp32_Rel_ag32_IF_PC_correct] >> fs [] >>
     qpat_abbrev_tac `newmem = mem_update _ _ _ _` >>
     `(fext (SUC t)).mem = (FUNPOW Next (THE (I' (4,SUC t))) a).MEM` by cheat >>
     `newmem = (FUNPOW Next (THE (I' (4,SUC t))) a).MEM` by fs [] >>
     `THE (I' (1,SUC t)) > THE (I' (4,SUC t)) /\ THE (I' (1,SUC t)) < THE (I' (4,SUC t)) + 4`
       by METIS_TAC [IF_instr_index_big_then_MEM] >> fs [] >>
     METIS_TAC [SC_self_mod_isa_not_affect_fetched_instr]) >>
   `~(fext (0+SUC t)).ready` by fs [] >> fs []) >-
   ((** 2: read memory and read instr **)
   last_assum (mp_tac o is_mem_data_read `SUC t`) >> rw [] >>
   Cases_on `m` >> fs [] >-
    (`(agp32 fext fbits (SUC t)).PC = (FUNPOW Next (THE (I'(1,SUC t)) - 1) a).PC`
       by METIS_TAC [agp32_Rel_ag32_IF_PC_correct] >> fs [] >>
     `(fext (SUC t)).mem = (FUNPOW Next (THE (I' (4,SUC t))) a).MEM` by cheat >> fs [] >>
     `THE (I' (1,SUC t)) > THE (I' (4,SUC t)) /\
     THE (I' (1,SUC t)) < THE (I' (4,SUC t)) + 4` by METIS_TAC [IF_instr_index_big_then_MEM] >>
     METIS_TAC [SC_self_mod_isa_not_affect_fetched_instr]) >>
   `~(fext (0+SUC t)).ready` by fs [] >> fs []) >-
   ((** 1: read instr **)
   last_assum (mp_tac o is_mem_inst_read `SUC t`) >> rw [] >>
   Cases_on `m` >> fs [] >-
    (`(agp32 fext fbits (SUC t)).PC = (FUNPOW Next (THE (I'(1,SUC t)) - 1) a).PC`
       by METIS_TAC [agp32_Rel_ag32_IF_PC_correct] >> fs [] >>
     `(fext (SUC t)).mem = (FUNPOW Next (THE (I' (4,SUC t))) a).MEM` by cheat >> fs [] >>
     `THE (I' (1,SUC t)) > THE (I' (4,SUC t)) /\
     THE (I' (1,SUC t)) < THE (I' (4,SUC t)) + 4` by METIS_TAC [IF_instr_index_big_then_MEM] >>
     METIS_TAC [SC_self_mod_isa_not_affect_fetched_instr]) >>
   `~(fext (0+SUC t)).ready` by fs [] >> fs []) >>
  (** 0: do nothing, not a possible command when fetching **)
  fs [enable_stg_def] >>
  `(agp32 fext fbits t).state = 0w`
    by (Cases_on_word_value `(agp32 fext fbits t).state` >>
        METIS_TAC [agp32_IF_PC_write_enable_and_state,agp32_state_impossible_values]) >>
  `~(agp32 fext fbits t).EX.EX_isAcc` by METIS_TAC [agp32_IF_PC_write_enable_and_EX_isAcc] >>
  `(fext t).ready` by METIS_TAC [agp32_IF_PC_write_enable_and_fext_ready] >>
  Q.ABBREV_TAC `s'' = agp32 fext fbits t` >>
  `(agp32 fext fbits (SUC t)).command = (agp32_next_state (fext t) s'' s'').command`
    by fs [Abbr `s''`,agp32_command_state_updated_by_agp32_next_state] >>
  subgoal `(agp32 fext fbits (SUC t)).command <> 0w` >>
  `(fext t).error = 0w` by fs [is_mem_def,mem_no_errors_def] >> fs [agp32_next_state_def] >>
  Cases_on `s''.state = 0w` >> fs [] >>
  Cases_on `~(fext t).ready` >> fs [] >>
  Cases_on `s''.MEM.MEM_isInterrupt` >> fs [] >>
  Cases_on `s''.MEM.MEM_read_mem` >> fs [] >>
  Cases_on `s''.MEM.MEM_write_mem` >> fs [] >>
  Cases_on `s''.MEM.MEM_write_mem_byte` >> fs [] >>
  Cases_on_word_value `(1 >< 0) s''.MEM.MEM_dataB` >> fs []
QED

(** IF_Rel between ISA and circuit states **)
Theorem agp32_Rel_ag32_IF_Rel_correct:
  !fext fbits a t I.
    SC_self_mod_isa a ==>
    is_mem fext_accessor_circuit (agp32 fext fbits) fext ==>
    is_sch_init I ==>
    is_sch_fetch I (agp32 fext fbits) a ==>
    is_sch_other I (agp32 fext fbits) ==>
    is_sch_disable I (agp32 fext fbits) ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    enable_stg 1 (agp32 fext fbits t) ==>
    I (1,SUC t) <> NONE ==>
    IF_Rel (fext (SUC t)) (agp32 fext fbits t) (agp32 fext fbits (SUC t)) a (THE (I (1,SUC t)))
Proof
  rw [IF_Rel_def] >-
   (** fetched instruction **)
   METIS_TAC [agp32_Rel_ag32_IF_instr_correct] >>
  (** PC **)
  METIS_TAC [agp32_Rel_ag32_IF_PC_correct]
QED


(** PC updated by when IF is disabled **)
Theorem agp32_Rel_ag32_IF_disable_PC_correct:
  !fext fbits a t I.
    is_sch_disable I (agp32 fext fbits) ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    ¬enable_stg 1 (agp32 fext fbits t) ==>
    I (1,SUC t) <> NONE ==>
    (agp32 fext fbits (SUC t)).PC = (FUNPOW Next (THE (I (1,SUC t)) - 1) a).PC
Proof
  rw [is_sch_disable_def] >>
  subgoal `(agp32 fext fbits (SUC t)).PC = (agp32 fext fbits t).PC` >-
   (Q.ABBREV_TAC `s = agp32 fext fbits t` >>
    Q.ABBREV_TAC `s' = procs [agp32_next_state;WB_pipeline;MEM_pipeline;EX_pipeline;
                              REG_write;ID_pipeline] (fext t) s s` >>
    `(agp32 fext fbits (SUC t)).PC = (IF_PC_update (fext t) s s').PC`
      by fs [agp32_PC_updated_by_IF_PC_update,Abbr `s`,Abbr `s'`] >>
    `~s.IF.IF_PC_write_enable` by fs [enable_stg_def] >>
    `~s'.IF.IF_PC_write_enable /\ s'.PC = s.PC`
      by METIS_TAC [agp32_same_IF_items_until_ID_pipeline,Abbr `s`,Abbr `s'`] >>
    fs [IF_PC_update_def]) >>
  fs [Rel_def,IF_Rel_def,IF_disable_Rel_def] >>
  Cases_on `enable_stg 1 (agp32 fext fbits (t − 1))` >> fs [] >>
  `(agp32 fext fbits (t-1)).MEM.MEM_state_flag`
    by fs [enable_stg_def,agp32_IF_PC_write_enable_and_EX_MEM_flags] >>
  fs [reg_data_vaild_def,enable_stg_def]
QED


(* IF_PC_input when jump *)
Theorem agp32_Rel_ag32_IF_PC_input_jump_correct:
  !fext fbits a t I.
    is_sch_other I (agp32 fext fbits) ==>
    is_sch_disable I (agp32 fext fbits) ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    reg_data_vaild 3 (agp32 fext fbits (SUC t)) ==>
    (agp32 fext fbits (SUC t)).EX.EX_jump_sel ==>
    (agp32 fext fbits (SUC t)).IF.IF_PC_input = (FUNPOW Next (THE (I (3,SUC t))) a).PC
Proof
  rw [is_sch_other_def,is_sch_disable_def] >>  Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state;WB_pipeline;MEM_pipeline;EX_pipeline;
                            REG_write;ID_pipeline;IF_PC_update;Acc_compute]
                           (fext t) s s` >>
  Q.ABBREV_TAC `s'' = procs [ForwardA; ForwardB; ForwardW; IF_instr_update; ID_opc_func_update;
                             ID_imm_update; ID_data_update; EX_ctrl_update; EX_forward_data;
                             EX_ALU_input_update; EX_compute_enable_update; EX_ALU_update;
                             EX_SHIFT_update; EX_jump_sel_addr_update; EX_data_rec_update]
                            (fext (SUC t)) s' s'` >>
  `(agp32 fext fbits (SUC t)).IF.IF_PC_input =
  (IF_PC_input_update (fext (SUC t)) s' s'').IF.IF_PC_input`
    by fs [agp32_IF_PC_input_updated_by_IF_PC_input_update,Abbr `s`,Abbr `s'`,Abbr `s''`] >>
  rw [IF_PC_input_update_def] >>
  `s''.EX.EX_jump_sel /\ (s''.EX.EX_jump_addr = (agp32 fext fbits (SUC t)).EX.EX_jump_addr)`
    by METIS_TAC [agp32_same_EX_jump_items_after_EX_jump_update,Abbr `s`,Abbr `s'`,Abbr `s''`] >>
  rw [MUX_21_def] >>
  cheat
QED


(* IF_PC_input when not jump *)
Theorem agp32_Rel_ag32_IF_PC_input_not_jump_correct:
  !fext fbits a t I.
    is_sch_fetch I (agp32 fext fbits) a ==>
    is_sch_disable I (agp32 fext fbits) ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (1,SUC t) <> NONE ==>
    ~(agp32 fext fbits (SUC t)).EX.EX_jump_sel ==>
    (agp32 fext fbits (SUC t)).IF.IF_PC_input = (FUNPOW Next (THE (I (1,SUC t)) − 1) a).PC + 4w
Proof
  rw [is_sch_other_def] >>  Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state;WB_pipeline;MEM_pipeline;EX_pipeline;
                            REG_write;ID_pipeline;IF_PC_update;Acc_compute]
                           (fext t) s s` >>
  Q.ABBREV_TAC `s'' = procs [ForwardA; ForwardB; ForwardW; IF_instr_update; ID_opc_func_update;
                             ID_imm_update; ID_data_update; EX_ctrl_update; EX_forward_data;
                             EX_ALU_input_update; EX_compute_enable_update; EX_ALU_update;
                             EX_SHIFT_update; EX_jump_sel_addr_update; EX_data_rec_update]
                            (fext (SUC t)) s' s'` >>
  `(agp32 fext fbits (SUC t)).IF.IF_PC_input =
  (IF_PC_input_update (fext (SUC t)) s' s'').IF.IF_PC_input`
    by fs [agp32_IF_PC_input_updated_by_IF_PC_input_update,Abbr `s`,Abbr `s'`,Abbr `s''`] >>
  rw [IF_PC_input_update_def] >>
  `~s''.EX.EX_jump_sel`
    by METIS_TAC [agp32_same_EX_jump_items_after_EX_jump_update,Abbr `s`,Abbr `s'`,Abbr `s''`] >>
  rw [MUX_21_def] >>
  `s'.PC = (agp32 fext fbits (SUC t)).PC`
    by fs [Abbr `s`,Abbr `s'`,agp32_same_PC_after_IF_PC_update] >> rw [] >>
  Cases_on `enable_stg 1 (agp32 fext fbits t)` >-
   (Cases_on `reg_data_vaild 3 (agp32 fext fbits t)` >-
     fs [agp32_Rel_ag32_IF_PC_correct] >>
    `(agp32 fext fbits t).MEM.MEM_state_flag`
      by fs [enable_stg_def,agp32_IF_PC_write_enable_and_EX_MEM_flags] >>
    fs [reg_data_vaild_def,enable_stg_def]) >>
  fs [agp32_Rel_ag32_IF_disable_PC_correct]
QED

val _ = export_theory ();
