open hardwarePreamble translatorTheory translatorLib arithmeticTheory pred_setTheory wordsExtraTheory dep_rewrite blastLib bitstringSyntax fcpSyntax listSyntax wordsSyntax agp32StateTheory agp32EnvironmentTheory agp32ProcessorTheory ag32Theory ag32ExtraTheory ag32UtilitiesTheory agp32RelationTheory agp32UpdateTheory agp32InternalTheory agp32StepLib agp32_MEM_CorrectTheory;

(* correctness of memory and data loading with respect to the ISA *)
val _ = new_theory "agp32_MEM_Data_Correct";

val _ = prefer_num ();
val _ = guess_lengths ();


(** memory **)
(** WB **)
(** WB enabled **)
Theorem agp32_Rel_ag32_fext_MEM_correct_WB_not_NONE_WB_enable:
  !fext fbits a t I.
    is_mem fext_accessor_circuit (agp32 fext fbits) fext ==>
    is_sch I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (5,SUC t) <> NONE ==>
    (fext (SUC t)).ready ==>
    enable_stg 5 (agp32 fext fbits t) ==>
    (fext (SUC t)).mem = (FUNPOW Next (THE (I (5,SUC t))) a).MEM
Proof
  rw [] >> `I' (5,SUC t) = I' (4,t)` by fs [is_sch_def,is_sch_writeback_def] >>
  `(fext t).ready` by (fs [enable_stg_def] >> METIS_TAC [agp32_WB_state_flag_and_fext_ready]) >>
  Cases_on `I' (5,t) <> NONE` >> fs [] >-
   (Cases_on `~is_wrMEM_isa (FUNPOW Next (THE (I' (4,t)) - 1) a)` >-
     (fs [GSYM MEM_not_changed_after_normal_instrs] >>
      last_assum (assume_tac o is_mem_def_mem_no_errors) >>
      Cases_on_word_value `(agp32 fext fbits (SUC t)).command` >>
      fs [agp32_command_impossible_values] >-
       (last_assum (mp_tac o is_mem_data_flush `SUC t`) >> rw [] >>
        Cases_on `m` >> fs [] >-
         (`THE (I' (4,t)) = THE (I' (5,t)) + 1`
            by METIS_TAC [MEM_instr_index_with_WB_instr_plus_1] >> fs [Rel_def]) >>
        `~(fext (0 + SUC t)).ready` by fs [] >> fs []) >-
       (fs [is_wrMEM_isa_def] >>
        `(agp32 fext fbits t).MEM.MEM_opc <> 2w /\
        (agp32 fext fbits t).MEM.MEM_opc <> 3w` by fs [Rel_def,MEM_Rel_def] >>
        METIS_TAC [agp32_Rel_ag32_command_not_3_not_write_mem_and_byte_WB_enable]) >-
       (last_assum (mp_tac o is_mem_data_read `SUC t`) >> rw [] >>
        Cases_on `m` >> fs [] >-
         (`THE (I' (4,t)) = THE (I' (5,t)) + 1`
            by METIS_TAC [MEM_instr_index_with_WB_instr_plus_1] >> fs [Rel_def]) >>
        `~(fext (0 + SUC t)).ready` by fs [] >> fs []) >-
       (last_assum (mp_tac o is_mem_inst_read `SUC t`) >> rw [] >>
        Cases_on `m` >> fs [] >-
         (`THE (I' (4,t)) = THE (I' (5,t)) + 1`
            by METIS_TAC [MEM_instr_index_with_WB_instr_plus_1] >> fs [Rel_def]) >>
        `~(fext (0 + SUC t)).ready` by fs [] >> fs []) >>
      last_assum (mp_tac o is_mem_do_nothing `SUC t`) >> rw [] >>
      `THE (I' (4,t)) = THE (I' (5,t)) + 1`
        by METIS_TAC [MEM_instr_index_with_WB_instr_plus_1] >> fs [Rel_def]) >> fs [] >>
    fs [is_wrMEM_isa_def] >-
     (`(agp32 fext fbits t).MEM.MEM_opc = 2w` by fs [is_wrMEM_isa_def,Rel_def,MEM_Rel_def] >>
      `(agp32 fext fbits (SUC t)).command = 3w`
        by fs [agp32_Rel_ag32_command_correct_write_mem_WB_enable,
               agp32_WB_opc_MEM_opc_when_WB_enabled] >>
      last_assum (mp_tac o is_mem_data_write `SUC t`) >> rw [] >>
      Cases_on `m` >> fs [] >-
       (cheat) >>
      `~(fext (0 + SUC t)).ready` by fs [] >> fs []) >>
    `(agp32 fext fbits t).MEM.MEM_opc = 3w` by fs [is_wrMEM_isa_def,Rel_def,MEM_Rel_def] >>
    `(agp32 fext fbits (SUC t)).command = 3w`
      by fs [agp32_Rel_ag32_command_correct_write_mem_byte_WB_enable,
             agp32_WB_opc_MEM_opc_when_WB_enabled] >>
    last_assum (mp_tac o is_mem_data_write `SUC t`) >> rw [] >>
    Cases_on `m` >> fs [] >-
     (cheat) >>
    `~(fext (0 + SUC t)).ready` by fs [] >> fs []) >>
  Cases_on `~is_wrMEM_isa (FUNPOW Next (THE (I' (4,t)) - 1) a)` >-
   (fs [GSYM MEM_not_changed_after_normal_instrs] >>
    last_assum (assume_tac o is_mem_def_mem_no_errors) >>
    Cases_on_word_value `(agp32 fext fbits (SUC t)).command` >>
    fs [agp32_command_impossible_values] >-
     (last_assum (mp_tac o is_mem_data_flush `SUC t`) >> rw [] >>
      Cases_on `m` >> fs [] >-
       fs [Rel_def] >>
      `~(fext (0 + SUC t)).ready` by fs [] >> fs []) >- 
     (fs [is_wrMEM_isa_def] >>
      `(agp32 fext fbits t).MEM.MEM_opc <> 2w /\
      (agp32 fext fbits t).MEM.MEM_opc <> 3w` by fs [Rel_def,MEM_Rel_def] >>
      METIS_TAC [agp32_Rel_ag32_command_not_3_not_write_mem_and_byte_WB_enable]) >- 
     (last_assum (mp_tac o is_mem_data_read `SUC t`) >> rw [] >>
      Cases_on `m` >> fs [] >-
       fs [Rel_def] >>
      `~(fext (0 + SUC t)).ready` by fs [] >> fs []) >-
     (last_assum (mp_tac o is_mem_inst_read `SUC t`) >> rw [] >>
      Cases_on `m` >> fs [] >-
       fs [Rel_def] >>
      `~(fext (0 + SUC t)).ready` by fs [] >> fs []) >>
    last_assum (mp_tac o is_mem_do_nothing `SUC t`) >> rw [] >> fs [Rel_def]) >> fs [] >>
  cheat
QED

Theorem agp32_Rel_ag32_fext_MEM_correct_WB_not_NONE:
  !fext fbits a t I.
    is_mem fext_accessor_circuit (agp32 fext fbits) fext ==>
    is_sch I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (5,SUC t) <> NONE ==>
    (fext (SUC t)).ready ==>
    (fext (SUC t)).mem = (FUNPOW Next (THE (I (5,SUC t))) a).MEM
Proof
  rw [] >> Cases_on `enable_stg 5 (agp32 fext fbits t)` >-
   METIS_TAC [agp32_Rel_ag32_fext_MEM_correct_WB_not_NONE_WB_enable] >>
  cheat
QED


(** data_rdata **)
(** LoadMem **)
(** WB enabled **)
Theorem agp32_Rel_ag32_read_mem_data_rdata_correct_WB_enable:
  !fext fbits a t I.
    is_mem fext_accessor_circuit (agp32 fext fbits) fext ==>
    is_sch I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (5,SUC t) <> NONE ==>
    (fext (SUC t)).ready ==>
    (agp32 fext fbits (SUC t)).WB.WB_opc = 4w ==>
    enable_stg 5 (agp32 fext fbits t) ==>
    (fext (SUC t)).data_rdata = mem_data_rdata (FUNPOW Next (THE (I (5,SUC t)) - 1) a)
Proof
  rw [] >> `I' (5,SUC t) = I' (4,t)` by fs [is_sch_def,is_sch_writeback_def] >>
  `align_addr (agp32 fext fbits (SUC t)).data_addr =
  mem_data_addr (FUNPOW Next (THE (I' (5,SUC t)) - 1) a)`
    by METIS_TAC [agp32_Rel_ag32_data_addr_correct_read_mem] >>
  `(agp32 fext fbits t).MEM.MEM_opc = 4w` by METIS_TAC [agp32_WB_opc_MEM_opc_when_WB_enabled] >>
  `(agp32 fext fbits t).MEM.MEM_read_mem` by METIS_TAC [agp32_MEM_read_mem_MEM_opc_4w_5w] >>
  `opc (FUNPOW Next (THE (I' (4,t)) - 1) a) = 4w` by fs [Rel_def,MEM_Rel_def] >>
  fs [mem_data_rdata_def] >>
  `(fext t).ready` by (fs [enable_stg_def] >> METIS_TAC [agp32_WB_state_flag_and_fext_ready]) >>
  last_assum (assume_tac o is_mem_def_mem_no_errors) >>
  `(agp32 fext fbits (SUC t)).command = 2w`
    by METIS_TAC [agp32_Rel_ag32_command_correct_read_mem_WB_enable] >>
  last_assum (mp_tac o is_mem_data_read `SUC t`) >> rw [] >>
  Cases_on `m` >> fs [] >-
   (fs [Rel_def] >>
    Cases_on `I' (5,t) = NONE` >> fs [] >>
    `THE (I' (4,t)) = THE (I' (5,t)) + 1`
      by METIS_TAC [MEM_instr_index_with_WB_instr_plus_1] >> fs []) >>
  `~(fext (0 + SUC t)).ready` by fs [] >> fs []
QED

(** WB is disabled and fext is not ready at the previous cycle **)
(** lemma **)
Theorem WB_opc_unchanged_after_disabled_cycles[local]:
  !fext fbits m n.
    (!p. p < m ==> ~(fext (p + n)).ready) ==>
    (agp32 fext fbits (m + n)).WB.WB_opc = (agp32 fext fbits n).WB.WB_opc
Proof
  rw [] >> Induct_on `m` >> rw [] >>
  `!p. p < m ==> ~(fext (n + p)).ready` by fs [] >> fs [] >>
  `m < SUC m` by rw [] >>
  `~(fext (n + m)).ready` by fs [] >>
  `~(agp32 fext fbits (n + m)).WB.WB_state_flag`
    by METIS_TAC [agp32_WB_state_flag_and_fext_ready] >>
  `(agp32 fext fbits (SUC (n + m))).WB.WB_opc = (agp32 fext fbits (n + m)).WB.WB_opc`
    by fs [agp32_WB_opc_unchanged_when_WB_disabled,enable_stg_def] >>
  `n + SUC m = SUC (n + m)` by rw [] >> rw [] >> fs []
QED

Theorem data_addr_unchanged_after_disabled_cycles[local]:
  !fext fbits m n.
    (!p. p < m ==> ~(fext (p + n)).ready) ==>
    (agp32 fext fbits (m + n)).data_addr = (agp32 fext fbits n).data_addr
Proof
  rw [] >> Induct_on `m` >> rw [] >>
  `!p. p < m ==> ~(fext (n + p)).ready` by fs [] >> fs [] >>
  `m < SUC m` by rw [] >>
  `~(fext (n + m)).ready` by fs [] >>
  `~(agp32 fext fbits (n + m)).WB.WB_state_flag`
    by METIS_TAC [agp32_WB_state_flag_and_fext_ready] >>
  `(agp32 fext fbits (SUC (n + m))).data_addr = (agp32 fext fbits (n + m)).data_addr`
    by fs [agp32_data_addr_wstrb_wdata_unchanged_when_WB_disabled,enable_stg_def] >>
  `n + SUC m = SUC (n + m)` by rw [] >> rw [] >> fs []
QED

Theorem WB_opc_unchanged_after_disabled_cycles_0[local]:
  !fext fbits m.
    (!p. p < m ==> ~(fext p).ready) ==>
    (agp32 fext fbits m).WB.WB_opc = (agp32 fext fbits 0).WB.WB_opc
Proof
  rw [] >> `!p. p < m ==> ~(fext (p + 0)).ready` by fs [] >>
  `(agp32 fext fbits (m + 0)).WB.WB_opc = (agp32 fext fbits 0).WB.WB_opc`
    by fs [WB_opc_unchanged_after_disabled_cycles] >> fs []
QED

Theorem EMPTY_no_fext_ready_cycle[local]:
  !t fext.
    {t0 | t0 < t /\ (fext t0).ready} = {} ==>
    (!t0. t0 < t ==> ~(fext t0).ready)
Proof
  rw [] >> Cases_on `(fext t0).ready` >> rw [] >>
  `t0 IN {t0 | t0 < t /\ (fext t0).ready}` by fs [] >>
  METIS_TAC [MEMBER_NOT_EMPTY]
QED

Theorem MAX_SET_0_no_fext_ready_cycle[local]:
  !t fext.
    {t0 | t0 < t /\ (fext t0).ready} <> {} ==>
    MAX_SET {t0 | t0 < t /\ (fext t0).ready} = 0 ==>
    (!t0. t0 < t - 1 ==> ~(fext (t0 + 1)).ready)
Proof
  rw [] >>
  `FINITE {t0 | t0 < t /\ (fext t0).ready}` by rw [FINITE_max_ready_cycle] >>
  Cases_on `(fext (t0 + 1)).ready` >> rw [] >>
  `t0 + 1  < t` by fs [] >>
  `t0 + 1 IN {t0 | t0 < t /\ (fext t0).ready}` by fs [] >>
  `t0 + 1 <= 0` by METIS_TAC [MAX_SET_DEF] >> rw []
QED

Theorem agp32_Rel_ag32_read_mem_data_rdata_correct_WB_disable_fext_not_ready:
  !fext fbits a t I.
    is_mem fext_accessor_circuit (agp32 fext fbits) fext ==>
    is_sch I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (5,SUC t) <> NONE ==>
    (fext (SUC t)).ready ==>
    ~(fext t).ready ==>
    (agp32 fext fbits (SUC t)).WB.WB_opc = 4w ==>
    ~enable_stg 5 (agp32 fext fbits t) ==>
    (fext (SUC t)).data_rdata = mem_data_rdata (FUNPOW Next (THE (I (5,SUC t)) - 1) a)
Proof
  rw [] >> Cases_on `MAX_SET {t0 | t0 < t /\ (fext t0).ready}` >-
   (Cases_on `{t0 | t0 < t /\ (fext t0).ready} = {}` >-
     (`!t0. t0 < t ==> ~(fext t0).ready` by METIS_TAC [EMPTY_no_fext_ready_cycle] >>
      `(agp32 fext fbits t).WB.WB_opc = (agp32 fext fbits 0).WB.WB_opc`
        by fs [WB_opc_unchanged_after_disabled_cycles_0] >>
      fs [agp32_WB_opc_unchanged_when_WB_disabled,agp32_init_WB_opc]) >>
    `!t0. t0 < t - 1 ==> ~(fext (t0 + 1)).ready`
      by METIS_TAC [MAX_SET_0_no_fext_ready_cycle] >>
    `(agp32 fext fbits (t - 1 + 1)).WB.WB_opc = (agp32 fext fbits 1).WB.WB_opc`
      by fs [WB_opc_unchanged_after_disabled_cycles] >>
    `t - 1 + 1 = t` by (Cases_on `t` >> fs []) >> fs [] >>
    `(agp32 fext fbits t).WB.WB_opc = 4w` by fs [agp32_WB_opc_unchanged_when_WB_disabled] >>
    `~enable_stg 5 (agp32 fext fbits 0)` by fs [agp32_init_ctrl_flags,enable_stg_def] >>
    `(agp32 fext fbits (SUC 0)).WB.WB_opc = 16w`
      by fs [agp32_WB_opc_unchanged_when_WB_disabled,agp32_init_WB_opc] >>
    fs [SUC_ONE_ADD]) >>
  Q.ABBREV_TAC `i = SUC n` >> `i <> 0` by fs [Abbr `i`] >>
  `FINITE {t0 | t0 < t /\ (fext t0).ready}` by fs [FINITE_max_ready_cycle] >>
  Cases_on `{t0 | t0 < t /\ (fext t0).ready} = {}` >> fs [MAX_SET_DEF] >>
  `i IN {t0 | t0 < t /\ (fext t0).ready}` by METIS_TAC [MAX_SET_DEF] >> fs [MAX_SET_DEF] >>
  last_assum (assume_tac o is_mem_def_mem_no_errors) >>
  Cases_on_word_value `(agp32 fext fbits (SUC i)).command` >>
  fs [agp32_command_impossible_values] >-
   (last_assum (mp_tac o is_mem_data_flush `SUC i`) >> simp [] >> strip_tac >>
    `m + SUC i = SUC t` by METIS_TAC [same_t_and_m_under_MAX_SET_SUC] >> fs [] >>
    `(agp32 fext fbits (SUC i)).WB.WB_opc = 4w`
      by METIS_TAC [WB_opc_unchanged_after_disabled_cycles] >>
    Cases_on `enable_stg 5 (agp32 fext fbits i)` >-
     gs [agp32_Rel_ag32_command_correct_read_mem_WB_enable] >>
    `(agp32 fext fbits (SUC i)).WB.WB_opc <> 16w` by fs [] >>
    gs [agp32_Rel_ag32_command_correct_WB_disable_fext_ready]) >-
   (last_assum (mp_tac o is_mem_data_write `SUC i`) >> simp [] >> strip_tac >>
    `m + SUC i = SUC t` by METIS_TAC [same_t_and_m_under_MAX_SET_SUC] >> fs [] >>
    `(agp32 fext fbits (SUC i)).WB.WB_opc = 4w`
      by METIS_TAC [WB_opc_unchanged_after_disabled_cycles] >>
    Cases_on `enable_stg 5 (agp32 fext fbits i)` >-
     gs [agp32_Rel_ag32_command_correct_read_mem_WB_enable] >>
    `(agp32 fext fbits (SUC i)).WB.WB_opc <> 16w` by fs [] >>
    gs [agp32_Rel_ag32_command_correct_WB_disable_fext_ready]) >-
   (last_assum (mp_tac o is_mem_data_read `SUC i`) >> simp [] >> strip_tac >>
    `m + SUC i = SUC t` by METIS_TAC [same_t_and_m_under_MAX_SET_SUC] >> fs [] >>
    `(fext (SUC t)).mem = (FUNPOW Next (THE (I' (5,SUC t))) a).MEM`
       by METIS_TAC [agp32_Rel_ag32_fext_MEM_correct_WB_not_NONE] >>
    `I' (5,SUC t) = I' (5,t)` by fs [is_sch_def,is_sch_disable_def] >> fs [] >>
    `(agp32 fext fbits (SUC t)).WB.WB_opc = (agp32 fext fbits t).WB.WB_opc`
      by fs [agp32_WB_opc_unchanged_when_WB_disabled] >>
    `opc (FUNPOW Next (THE (I' (5,t)) - 1) a) = 4w` by fs [Rel_def,WB_Rel_def] >>
    simp [mem_data_rdata_def] >>
    `(agp32 fext fbits (SUC i)).data_addr = (agp32 fext fbits (m + SUC i)).data_addr`
      by METIS_TAC [data_addr_unchanged_after_disabled_cycles] >>
    `align_addr (agp32 fext fbits (SUC t)).data_addr =
    mem_data_addr (FUNPOW Next (THE (I' (5,SUC t)) - 1) a)`
      by METIS_TAC [agp32_Rel_ag32_data_addr_correct_read_mem] >>
    `align_addr (agp32 fext fbits (SUC i)).data_addr =
    mem_data_addr (FUNPOW Next (THE (I' (5,t)) - 1) a)` by fs [Rel_def] >> fs [] >>
    `(fext (SUC i)).mem = (fext i).mem`
      by (Cases_on `m` >> fs [] >> `0 < SUC n` by rw [] >>
          `(fext (0 + SUC i)).mem = (fext i).mem` by fs [] >> fs []) >>
    `(fext (SUC i)).mem = (fext (SUC t)).mem` by fs [] >> fs [] >>
    `~is_wrMEM_isa (FUNPOW Next (THE (I' (5,t)) - 1) a)` by fs [is_wrMEM_isa_def] >>
    METIS_TAC [word_at_addr_not_changed_after_normal_instrs]) >-
   (last_assum (mp_tac o is_mem_inst_read `SUC i`) >> simp [] >> strip_tac >>
    `m + SUC i = SUC t` by METIS_TAC [same_t_and_m_under_MAX_SET_SUC] >> fs [] >>
    `(agp32 fext fbits (SUC i)).WB.WB_opc = 4w`
      by METIS_TAC [WB_opc_unchanged_after_disabled_cycles] >>
    Cases_on `enable_stg 5 (agp32 fext fbits i)` >-
     gs [agp32_Rel_ag32_command_correct_read_mem_WB_enable] >>
    `(agp32 fext fbits (SUC i)).WB.WB_opc <> 16w` by fs [] >>
    gs [agp32_Rel_ag32_command_correct_WB_disable_fext_ready]) >>
  last_assum (mp_tac o is_mem_do_nothing `SUC i`) >> simp [] >> strip_tac >>
  Cases_on `SUC i = t` >> fs [] >>
  Cases_on `SUC i > t` >> fs [] >>
  `SUC i < t` by fs [] >>
  `(SUC i) IN {t0 | t0 < t /\ (fext t0).ready}` by fs [] >>
  `(SUC i) <= i` by METIS_TAC [MAX_SET_DEF] >> fs []
QED

(** WB disabled **) 
Theorem agp32_Rel_ag32_read_mem_data_rdata_correct_WB_disable:
  !fext fbits a t I.
    is_mem fext_accessor_circuit (agp32 fext fbits) fext ==>
    is_sch I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (5,SUC t) <> NONE ==>
    (fext (SUC t)).ready ==>
    (agp32 fext fbits (SUC t)).WB.WB_opc = 4w ==>
    ~enable_stg 5 (agp32 fext fbits t) ==>
    (fext (SUC t)).data_rdata = mem_data_rdata (FUNPOW Next (THE (I (5,SUC t)) - 1) a)
Proof
  rw [] >> Cases_on `(fext t).ready` >-
   (`I' (5,SUC t) = I' (5,t)` by fs [is_sch_def,is_sch_disable_def] >>
    `(agp32 fext fbits (SUC t)).WB.WB_opc = (agp32 fext fbits t).WB.WB_opc`
      by fs [agp32_WB_opc_unchanged_when_WB_disabled] >>
    last_assum (assume_tac o is_mem_def_mem_no_errors) >>
    `(agp32 fext fbits (SUC t)).command = 0w`
      by gs [agp32_Rel_ag32_command_correct_WB_disable_fext_ready] >>
    last_assum (mp_tac o is_mem_do_nothing `SUC t`) >> rw [] >>
    fs [Rel_def,MEM_data_rel_def]) >>
  METIS_TAC [agp32_Rel_ag32_read_mem_data_rdata_correct_WB_disable_fext_not_ready]
QED

Theorem agp32_Rel_ag32_read_mem_data_rdata_correct:
  !fext fbits a t I.
    is_mem fext_accessor_circuit (agp32 fext fbits) fext ==>
    is_sch I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (5,SUC t) <> NONE ==>
    (fext (SUC t)).ready ==>
    (agp32 fext fbits (SUC t)).WB.WB_opc = 4w ==>
    (fext (SUC t)).data_rdata = mem_data_rdata (FUNPOW Next (THE (I (5,SUC t)) - 1) a)
Proof
  rw [] >> Cases_on `enable_stg 5 (agp32 fext fbits t)` >>
  METIS_TAC [agp32_Rel_ag32_read_mem_data_rdata_correct_WB_enable,
             agp32_Rel_ag32_read_mem_data_rdata_correct_WB_disable]
QED

(** LoadMemByte **)
(** WB enabled **)
Theorem agp32_Rel_ag32_read_mem_byte_data_rdata_correct_WB_enable:
  !fext fbits a t I.
    is_mem fext_accessor_circuit (agp32 fext fbits) fext ==>
    is_sch I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (5,SUC t) <> NONE ==>
    (fext (SUC t)).ready ==>
    (agp32 fext fbits (SUC t)).WB.WB_opc = 5w ==>
    enable_stg 5 (agp32 fext fbits t) ==>
    (fext (SUC t)).data_rdata = mem_data_rdata_extra (FUNPOW Next (THE (I (5,SUC t)) - 1) a)
Proof
  rw [] >> `I' (5,SUC t) = I' (4,t)` by fs [is_sch_def,is_sch_writeback_def] >>
  `(agp32 fext fbits (SUC t)).data_addr =
  mem_data_addr (FUNPOW Next (THE (I' (5,SUC t)) - 1) a)`
    by METIS_TAC [agp32_Rel_ag32_data_addr_correct_read_mem_byte] >>
  `(agp32 fext fbits t).MEM.MEM_opc = 5w` by METIS_TAC [agp32_WB_opc_MEM_opc_when_WB_enabled] >>
  `(agp32 fext fbits t).MEM.MEM_read_mem` by METIS_TAC [agp32_MEM_read_mem_MEM_opc_4w_5w] >>
  `opc (FUNPOW Next (THE (I' (4,t)) - 1) a) = 5w` by fs [Rel_def,MEM_Rel_def] >>
  fs [mem_data_rdata_extra_def] >>
  `(fext t).ready` by (fs [enable_stg_def] >> METIS_TAC [agp32_WB_state_flag_and_fext_ready]) >>
  last_assum (assume_tac o is_mem_def_mem_no_errors) >>
  `(agp32 fext fbits (SUC t)).command = 2w`
    by METIS_TAC [agp32_Rel_ag32_command_correct_read_mem_byte_WB_enable] >>
  last_assum (mp_tac o is_mem_data_read `SUC t`) >> rw [] >>
  Cases_on `m` >> fs [] >-
   (fs [Rel_def] >>
    Cases_on `I' (5,t) = NONE` >> fs [] >>
    `THE (I' (4,t)) = THE (I' (5,t)) + 1`
      by METIS_TAC [MEM_instr_index_with_WB_instr_plus_1] >> fs []) >>
  `~(fext (0 + SUC t)).ready` by fs [] >> fs []
QED

(** WB is disabled and fext is not ready at the previous cycle **)
Theorem agp32_Rel_ag32_read_mem_byte_data_rdata_correct_WB_disable_fext_not_ready:
  !fext fbits a t I.
    is_mem fext_accessor_circuit (agp32 fext fbits) fext ==>
    is_sch I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (5,SUC t) <> NONE ==>
    (fext (SUC t)).ready ==>
    ~(fext t).ready ==>
    (agp32 fext fbits (SUC t)).WB.WB_opc = 5w ==>
    ~enable_stg 5 (agp32 fext fbits t) ==>
    (fext (SUC t)).data_rdata = mem_data_rdata_extra (FUNPOW Next (THE (I (5,SUC t)) - 1) a)
Proof
  rw [] >> Cases_on `MAX_SET {t0 | t0 < t /\ (fext t0).ready}` >-
   (Cases_on `{t0 | t0 < t /\ (fext t0).ready} = {}` >-
     (`!t0. t0 < t ==> ~(fext t0).ready` by METIS_TAC [EMPTY_no_fext_ready_cycle] >>
      `(agp32 fext fbits t).WB.WB_opc = (agp32 fext fbits 0).WB.WB_opc`
        by fs [WB_opc_unchanged_after_disabled_cycles_0] >>
      fs [agp32_WB_opc_unchanged_when_WB_disabled,agp32_init_WB_opc]) >>
    `!t0. t0 < t - 1 ==> ~(fext (t0 + 1)).ready`
      by METIS_TAC [MAX_SET_0_no_fext_ready_cycle] >>
    `(agp32 fext fbits (t - 1 + 1)).WB.WB_opc = (agp32 fext fbits 1).WB.WB_opc`
      by fs [WB_opc_unchanged_after_disabled_cycles] >>
    `t - 1 + 1 = t` by (Cases_on `t` >> fs []) >> fs [] >>
    `(agp32 fext fbits t).WB.WB_opc = 5w` by fs [agp32_WB_opc_unchanged_when_WB_disabled] >>
    `~enable_stg 5 (agp32 fext fbits 0)` by fs [agp32_init_ctrl_flags,enable_stg_def] >>
    `(agp32 fext fbits (SUC 0)).WB.WB_opc = 16w`
      by fs [agp32_WB_opc_unchanged_when_WB_disabled,agp32_init_WB_opc] >>
    fs [SUC_ONE_ADD]) >>
  Q.ABBREV_TAC `i = SUC n` >> `i <> 0` by fs [Abbr `i`] >>
  `FINITE {t0 | t0 < t /\ (fext t0).ready}` by fs [FINITE_max_ready_cycle] >>
  Cases_on `{t0 | t0 < t /\ (fext t0).ready} = {}` >> fs [MAX_SET_DEF] >>
  `i IN {t0 | t0 < t /\ (fext t0).ready}` by METIS_TAC [MAX_SET_DEF] >> fs [MAX_SET_DEF] >>
  last_assum (assume_tac o is_mem_def_mem_no_errors) >>
  Cases_on_word_value `(agp32 fext fbits (SUC i)).command` >>
  fs [agp32_command_impossible_values] >-
   (last_assum (mp_tac o is_mem_data_flush `SUC i`) >> simp [] >> strip_tac >>
    `m + SUC i = SUC t` by METIS_TAC [same_t_and_m_under_MAX_SET_SUC] >> fs [] >>
    `(agp32 fext fbits (SUC i)).WB.WB_opc = 5w`
      by METIS_TAC [WB_opc_unchanged_after_disabled_cycles] >>
    Cases_on `enable_stg 5 (agp32 fext fbits i)` >-
     gs [agp32_Rel_ag32_command_correct_read_mem_byte_WB_enable] >>
    `(agp32 fext fbits (SUC i)).WB.WB_opc <> 16w` by fs [] >>
    gs [agp32_Rel_ag32_command_correct_WB_disable_fext_ready]) >-
   (last_assum (mp_tac o is_mem_data_write `SUC i`) >> simp [] >> strip_tac >>
    `m + SUC i = SUC t` by METIS_TAC [same_t_and_m_under_MAX_SET_SUC] >> fs [] >>
    `(agp32 fext fbits (SUC i)).WB.WB_opc = 5w`
      by METIS_TAC [WB_opc_unchanged_after_disabled_cycles] >>
    Cases_on `enable_stg 5 (agp32 fext fbits i)` >-
     gs [agp32_Rel_ag32_command_correct_read_mem_byte_WB_enable] >>
    `(agp32 fext fbits (SUC i)).WB.WB_opc <> 16w` by fs [] >>
    gs [agp32_Rel_ag32_command_correct_WB_disable_fext_ready]) >-
   (last_assum (mp_tac o is_mem_data_read `SUC i`) >> simp [] >> strip_tac >>
    `m + SUC i = SUC t` by METIS_TAC [same_t_and_m_under_MAX_SET_SUC] >> fs [] >>
    `(fext (SUC t)).mem = (FUNPOW Next (THE (I' (5,SUC t))) a).MEM`
       by METIS_TAC [agp32_Rel_ag32_fext_MEM_correct_WB_not_NONE] >>
    `I' (5,SUC t) = I' (5,t)` by fs [is_sch_def,is_sch_disable_def] >> fs [] >>
    `(agp32 fext fbits (SUC t)).WB.WB_opc = (agp32 fext fbits t).WB.WB_opc`
      by fs [agp32_WB_opc_unchanged_when_WB_disabled] >>
    `opc (FUNPOW Next (THE (I' (5,t)) - 1) a) = 5w` by fs [Rel_def,WB_Rel_def] >>
    simp [mem_data_rdata_extra_def] >>
    `(agp32 fext fbits (SUC i)).data_addr = (agp32 fext fbits (m + SUC i)).data_addr`
      by METIS_TAC [data_addr_unchanged_after_disabled_cycles] >>
    `(agp32 fext fbits (SUC i)).data_addr =
    mem_data_addr (FUNPOW Next (THE (I' (5,SUC t)) - 1) a)`
      by METIS_TAC [agp32_Rel_ag32_data_addr_correct_read_mem_byte] >> fs [] >>
    `(fext (SUC i)).mem = (fext i).mem`
      by (Cases_on `m` >> fs [] >> `0 < SUC n` by rw [] >>
          `(fext (0 + SUC i)).mem = (fext i).mem` by fs [] >> fs []) >>
    `~is_wrMEM_isa (FUNPOW Next (THE (I' (5,t)) - 1) a)` by fs [is_wrMEM_isa_def] >>
    METIS_TAC [word_at_addr_not_changed_after_normal_instrs]) >-
   (last_assum (mp_tac o is_mem_inst_read `SUC i`) >> simp [] >> strip_tac >>
    `m + SUC i = SUC t` by METIS_TAC [same_t_and_m_under_MAX_SET_SUC] >> fs [] >>
    `(agp32 fext fbits (SUC i)).WB.WB_opc = 5w`
      by METIS_TAC [WB_opc_unchanged_after_disabled_cycles] >>
    Cases_on `enable_stg 5 (agp32 fext fbits i)` >-
     gs [agp32_Rel_ag32_command_correct_read_mem_byte_WB_enable] >>
    `(agp32 fext fbits (SUC i)).WB.WB_opc <> 16w` by fs [] >>
    gs [agp32_Rel_ag32_command_correct_WB_disable_fext_ready]) >>
  last_assum (mp_tac o is_mem_do_nothing `SUC i`) >> simp [] >> strip_tac >>
  Cases_on `SUC i = t` >> fs [] >>
  Cases_on `SUC i > t` >> fs [] >>
  `SUC i < t` by fs [] >>
  `(SUC i) IN {t0 | t0 < t /\ (fext t0).ready}` by fs [] >>
  `(SUC i) <= i` by METIS_TAC [MAX_SET_DEF] >> fs []
QED

(** WB disabled **) 
Theorem agp32_Rel_ag32_read_mem_byte_data_rdata_correct_WB_disable:
  !fext fbits a t I.
    is_mem fext_accessor_circuit (agp32 fext fbits) fext ==>
    is_sch I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (5,SUC t) <> NONE ==>
    (fext (SUC t)).ready ==>
    (agp32 fext fbits (SUC t)).WB.WB_opc = 5w ==>
    ~enable_stg 5 (agp32 fext fbits t) ==>
    (fext (SUC t)).data_rdata = mem_data_rdata_extra (FUNPOW Next (THE (I (5,SUC t)) - 1) a)
Proof
  rw [] >> Cases_on `(fext t).ready` >-
   (`I' (5,SUC t) = I' (5,t)` by fs [is_sch_def,is_sch_disable_def] >>
    `(agp32 fext fbits (SUC t)).WB.WB_opc = (agp32 fext fbits t).WB.WB_opc`
      by fs [agp32_WB_opc_unchanged_when_WB_disabled] >>
    last_assum (assume_tac o is_mem_def_mem_no_errors) >>
    `(agp32 fext fbits (SUC t)).command = 0w`
      by gs [agp32_Rel_ag32_command_correct_WB_disable_fext_ready] >>
    last_assum (mp_tac o is_mem_do_nothing `SUC t`) >> rw [] >>
    fs [Rel_def,MEM_data_rel_def]) >>
  METIS_TAC [agp32_Rel_ag32_read_mem_byte_data_rdata_correct_WB_disable_fext_not_ready]
QED

Theorem agp32_Rel_ag32_read_mem_byte_data_rdata_correct:
  !fext fbits a t I.
    is_mem fext_accessor_circuit (agp32 fext fbits) fext ==>
    is_sch I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (5,SUC t) <> NONE ==>
    (fext (SUC t)).ready ==>
    (agp32 fext fbits (SUC t)).WB.WB_opc = 5w ==>
    (fext (SUC t)).data_rdata = mem_data_rdata_extra (FUNPOW Next (THE (I (5,SUC t)) - 1) a)
Proof
  rw [] >> Cases_on `enable_stg 5 (agp32 fext fbits t)` >>
  METIS_TAC [agp32_Rel_ag32_read_mem_byte_data_rdata_correct_WB_enable,
             agp32_Rel_ag32_read_mem_byte_data_rdata_correct_WB_disable]
QED


(* MEM_data_rel *)
Theorem agp32_Rel_ag32_MEM_data_rel_correct:
  !fext fbits a t I.
    is_mem fext_accessor_circuit (agp32 fext fbits) fext ==>
    is_sch I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (5,SUC t) <> NONE ==>
    MEM_data_rel (fext (SUC t)) (agp32 fext fbits (SUC t)) a (THE (I (5,SUC t)))
Proof
  rw [MEM_data_rel_def] >>
  METIS_TAC [agp32_Rel_ag32_read_mem_data_rdata_correct,
             agp32_Rel_ag32_read_mem_byte_data_rdata_correct]
QED

val _ = export_theory ();
