open hardwarePreamble translatorTheory translatorLib arithmeticTheory dep_rewrite blastLib bitstringSyntax fcpSyntax listSyntax wordsSyntax agp32StateTheory agp32EnvironmentTheory agp32ProcessorTheory ag32Theory ag32ExtraTheory ag32UtilitiesTheory agp32RelationTheory agp32UpdateTheory agp32InternalTheory agp32StepLib;

(* the pipelined circuit makes progress according to the environment *)
val _ = new_theory "agp32Progress";

val _ = prefer_num ();
val _ = guess_lengths ();

(** hw_work and I **)
(** WB processes an instr from the previous stage **)
Theorem agp32_hw_work_instr_processed_WB:
  !fext fbits a t I.
    is_sch I (agp32 fext fbits) a ==>
    enable_stg 5 (agp32 fext fbits t) ==>
    ?k. k >= 1 ==> k <= 5 ==>
        I (k,SUC t) = I (k - 1,t)
Proof
  rw [] >>
  `I' (5,SUC t) = I' (4,t)` by fs [is_sch_def,is_sch_writeback_def] >>
  Q.EXISTS_TAC `5` >> fs []                              
QED

(* if a pipeline stage is enabled, then something is updated *)
Theorem agp32_hw_work_instr_processed:
  !fext fbits a t I.
    is_sch I (agp32 fext fbits) a ==>
    hw_work (agp32 fext fbits t) ==>
    ?k. k >= 1 ==> k <= 5 ==>
        I (k,SUC t) = I (k - 1,t)
Proof
  rw [hw_work_def] >-
   (`enable_stg 5 (agp32 fext fbits t)`
      by gs [enable_stg_def,agp32_IF_PC_write_enable_and_WB_flag] >>
    METIS_TAC [agp32_hw_work_instr_processed_WB]) >-
   (`enable_stg 5 (agp32 fext fbits t)`
      by gs [enable_stg_def,agp32_ID_ID_write_enable_WB_state_flag] >>
    METIS_TAC [agp32_hw_work_instr_processed_WB]) >-
   (`enable_stg 5 (agp32 fext fbits t)`
      by gs [enable_stg_def,agp32_ID_EX_write_enable_WB_state_flag] >>
    METIS_TAC [agp32_hw_work_instr_processed_WB]) >-
   (`enable_stg 5 (agp32 fext fbits t)`
      by gs [enable_stg_def,agp32_MEM_state_flag_eq_WB_state_flag] >>
    METIS_TAC [agp32_hw_work_instr_processed_WB]) >>
  METIS_TAC [agp32_hw_work_instr_processed_WB]
QED                   


(** lemma **)
Theorem state_0w_fext_ready_hw_work[local]:
  !fext fbits t.
    (agp32 fext fbits t).state = 0w ==>
    (fext t).ready ==>
    hw_work (agp32 fext fbits t)
Proof
  rw [hw_work_def,enable_stg_def] >>
  fs [agp32_state_fext_ready_and_WB_state_flag]
QED

Theorem fext_not_ready_imply_future_ready[local]:
  !fext fbits t.
    is_mem fext_accessor_circuit (agp32 fext fbits) fext ==>
    (fext 0).ready ==>
    ~(fext t).ready ==>
    ?n. (fext (SUC (t + n))).ready /\
        (!p. p < n ==> ~(fext (SUC (t + p))).ready)
Proof
  rw [] >> Induct_on `t` >> rw [] >>
  Cases_on `(fext t).ready` >> fs [] >-
   (last_assum (assume_tac o is_mem_def_mem_no_errors) >>
    Cases_on_word_value `(agp32 fext fbits (SUC t)).command` >>
    fs [agp32_command_impossible_values] >-
     (last_assum (mp_tac o is_mem_data_flush `SUC t`) >> rw [] >>
      Cases_on `m` >> fs [] >>
      Q.EXISTS_TAC `n` >> fs [ADD1] >>
      rw [] >> `p + 1 < n + 1` by fs [] >>
      `~(fext (p + 1 + (t + 1))).ready` by fs [] >> fs []) >-
     (last_assum (mp_tac o is_mem_data_write `SUC t`) >> rw [] >>
      Cases_on `m` >> fs [] >>
      Q.EXISTS_TAC `n` >> fs [ADD1] >>
      rw [] >> `p + 1 < n + 1` by fs [] >>
      `~(fext (p + 1 + (t + 1))).ready` by fs [] >> fs []) >-
     (last_assum (mp_tac o is_mem_data_read `SUC t`) >> rw [] >>
      Cases_on `m` >> fs [] >>
      Q.EXISTS_TAC `n` >> fs [ADD1] >>
      rw [] >> `p + 1 < n + 1` by fs [] >>
      `~(fext (p + 1 + (t + 1))).ready` by fs [] >> fs []) >-
     (last_assum (mp_tac o is_mem_inst_read `SUC t`) >> rw [] >>
      Cases_on `m` >> fs [] >>
      Q.EXISTS_TAC `n` >> fs [ADD1] >>
      rw [] >> `p + 1 < n + 1` by fs [] >>
      `~(fext (p + 1 + (t + 1))).ready` by fs [] >> fs []) >>
    last_assum (mp_tac o is_mem_do_nothing `SUC t`) >> rw []) >>
  Cases_on `n` >> fs [] >>
  Q.EXISTS_TAC `n'` >> fs [ADD1] >>
  rw [] >> `p + 1 < n' + 1` by fs [] >>
  `~(fext (p + 1 + (t + 1))).ready` by fs [] >> fs []
QED

Theorem SUC_SUC_add[local]:
  !a b.
    a + SUC (SUC b) = (SUC a) + (SUC b)
Proof
  rw []
QED

Theorem state_1w_command_do_interrupt_unchanged_after_not_ready_cycles[local]:
  !fext fbits n t.
    is_mem fext_accessor_circuit (agp32 fext fbits) fext ==>
    (!p. p < SUC n ==> ~(fext (p + t)).ready) ==>
    (agp32 fext fbits (SUC t)).state = 1w ==>
    (agp32 fext fbits (SUC t)).command = 0w ==>
    ~(agp32 fext fbits (SUC t)).do_interrupt ==>
    ((agp32 fext fbits (t + SUC n)).state = 1w) /\
    ((agp32 fext fbits (t + SUC n)).command = 0w) /\
    (~(agp32 fext fbits (t + SUC n)).do_interrupt)   
Proof
  rpt gen_tac >> rpt disch_tac >>
  Induct_on `n` >-
   (rw [] >> fs [ADD1]) >>
  disch_tac >>
  `!p. p < SUC n ==> ~(fext (p + t)).ready` by fs [] >> fs [] >>
  `~(fext (SUC n + t)).ready` by fs [] >>
  `~(fext (t + SUC n)).ready` by fs [] >>
  Q.ABBREV_TAC `t' = t + SUC n` >>
  `t + SUC (SUC n) = SUC t'` by gs [Abbr `t'`] >> fs [] >>
  Q.ABBREV_TAC `s' = agp32 fext fbits t'` >>
  `(agp32 fext fbits (SUC t')).state = (agp32_next_state (fext t') s' s').state /\
  (agp32 fext fbits (SUC t')).command = (agp32_next_state (fext t') s' s').command`
    by fs [agp32_command_state_updated_by_agp32_next_state] >>
  `(agp32 fext fbits (SUC t')).do_interrupt = (agp32_next_state (fext t') s' s').do_interrupt`
    by fs [agp32_interrupt_items_updated_by_agp32_next_state] >>
  `(fext t').error = 0w` by fs [is_mem_def,mem_no_errors_def] >>
  fs [agp32_next_state_def]
QED

Theorem state_1w_command_do_interrupt_unchanged_after_not_ready_cycles_extra[local]:
  !fext fbits n t.
    is_mem fext_accessor_circuit (agp32 fext fbits) fext ==>
    (!p. p < SUC n ==> ~(fext (p + t)).ready) ==>
    (agp32 fext fbits (SUC t)).state = 1w ==>
    (agp32 fext fbits (SUC t)).command = 0w ==>
    (agp32 fext fbits (SUC t)).do_interrupt ==>
    ((agp32 fext fbits (t + SUC n)).state = 1w) /\
    ((agp32 fext fbits (t + SUC n)).command = 0w) /\
    ((agp32 fext fbits (t + SUC n)).do_interrupt)   
Proof
  rpt gen_tac >> rpt disch_tac >>
  Induct_on `n` >-
   (rw [] >> fs [ADD1]) >>
  disch_tac >>
  `!p. p < SUC n ==> ~(fext (p + t)).ready` by fs [] >> fs [] >>
  `~(fext (SUC n + t)).ready` by fs [] >>
  `~(fext (t + SUC n)).ready` by fs [] >>
  Q.ABBREV_TAC `t' = t + SUC n` >>
  `t + SUC (SUC n) = SUC t'` by gs [Abbr `t'`] >> fs [] >>
  Q.ABBREV_TAC `s' = agp32 fext fbits t'` >>
  `(agp32 fext fbits (SUC t')).state = (agp32_next_state (fext t') s' s').state /\
  (agp32 fext fbits (SUC t')).command = (agp32_next_state (fext t') s' s').command`
    by fs [agp32_command_state_updated_by_agp32_next_state] >>
  `(agp32 fext fbits (SUC t')).do_interrupt = (agp32_next_state (fext t') s' s').do_interrupt`
    by fs [agp32_interrupt_items_updated_by_agp32_next_state] >>
  `(fext t').error = 0w` by fs [is_mem_def,mem_no_errors_def] >>
  fs [agp32_next_state_def]
QED


(** state is 0w and fext is not ready **)
Theorem agp32_hw_work_when_state_0w_fext_not_ready:
  !fext fbits t.
    is_mem fext_accessor_circuit (agp32 fext fbits) fext ==>
    (agp32 fext fbits t).state = 0w ==>
    (fext 0).ready ==>
    ~(fext t).ready ==>
    ?n. hw_work (agp32 fext fbits (SUC (t + n)))
Proof    
  rw [] >> Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  subgoal `(agp32 fext fbits (SUC t)).state = 1w` >-
   (`(agp32 fext fbits (SUC t)).state = (agp32_next_state (fext t) s s).state`
      by fs [agp32_command_state_updated_by_agp32_next_state] >>
    `(fext t).error = 0w` by fs [is_mem_def,mem_no_errors_def] >>
    fs [agp32_next_state_def]) >>
  subgoal `~(agp32 fext fbits (SUC t)).do_interrupt` >-
   (`~s.do_interrupt` by gs [agp32_state_not_1w_no_do_interrupt,Abbr `s`] >>
    `(agp32 fext fbits (SUC t)).do_interrupt = (agp32_next_state (fext t) s s).do_interrupt`
      by fs [agp32_interrupt_items_updated_by_agp32_next_state] >>
    `(fext t).error = 0w` by fs [is_mem_def,mem_no_errors_def] >>
    fs [agp32_next_state_def]) >>
  `?n. (fext (SUC (t + n))).ready /\ (!p. p < n ==> ~(fext (SUC (t + p))).ready)`
    by METIS_TAC [fext_not_ready_imply_future_ready] >>
  Cases_on `n` >-
   (fs [] >> Q.ABBREV_TAC `t' = SUC t` >>
    Q.ABBREV_TAC `s' = agp32 fext fbits t'` >>
    `(agp32 fext fbits (SUC t')).state = (agp32_next_state (fext t') s' s').state /\
    (agp32 fext fbits (SUC t')).command = (agp32_next_state (fext t') s' s').command`
      by fs [agp32_command_state_updated_by_agp32_next_state] >>
    `(fext t').error = 0w` by fs [is_mem_def,mem_no_errors_def] >>
    fs [agp32_next_state_def] >> gs [] >>
    Cases_on `s'.command = 0w` >> fs [] >-
     (last_assum (mp_tac o is_mem_do_nothing `SUC t'`) >> rw [] >>
      Q.EXISTS_TAC `1` >> fs [Abbr `t'`,Abbr `s'`,ADD1] >>
      gs [state_0w_fext_ready_hw_work]) >>
    last_assum (mp_tac o is_mem_do_nothing `SUC t'`) >> rw [] >>
    subgoal `~(agp32 fext fbits (SUC t')).do_interrupt` >-
     (`(agp32 fext fbits (SUC t')).do_interrupt = (agp32_next_state (fext t') s' s').do_interrupt`
        by fs [agp32_interrupt_items_updated_by_agp32_next_state] >>
      `(fext t').error = 0w` by fs [is_mem_def,mem_no_errors_def] >>
      fs [agp32_next_state_def]) >>  
    Q.ABBREV_TAC `t'' = SUC t'` >>
    Q.ABBREV_TAC `s'' = agp32 fext fbits t''` >>
    `(agp32 fext fbits (SUC t'')).state = (agp32_next_state (fext t'') s'' s'').state /\
    (agp32 fext fbits (SUC t'')).command = (agp32_next_state (fext t'') s'' s'').command`
      by fs [agp32_command_state_updated_by_agp32_next_state] >>
    `(fext t'').error = 0w` by fs [is_mem_def,mem_no_errors_def] >>
    fs [agp32_next_state_def] >> gs [] >>
    last_assum (mp_tac o is_mem_do_nothing `SUC t''`) >> rw [] >>
    Q.EXISTS_TAC `2` >> fs [Abbr `t''`,Abbr `t'`,Abbr `s'`,ADD1] >>           
    gs [state_0w_fext_ready_hw_work]) >>
  `0 < SUC n'` by fs [] >>
  `~(fext (SUC (t + 0))).ready` by METIS_TAC [] >> fs [] >>
  Q.ABBREV_TAC `t' = SUC t` >>
  Q.ABBREV_TAC `s' = agp32 fext fbits t'` >>
  `(agp32 fext fbits (SUC t')).state = (agp32_next_state (fext t') s' s').state /\
  (agp32 fext fbits (SUC t')).command = (agp32_next_state (fext t') s' s').command`
    by fs [agp32_command_state_updated_by_agp32_next_state] >>
  `(agp32 fext fbits (SUC t')).do_interrupt = (agp32_next_state (fext t') s' s').do_interrupt`
    by fs [agp32_interrupt_items_updated_by_agp32_next_state] >>
  `(fext t').error = 0w` by fs [is_mem_def,mem_no_errors_def] >>
  fs [agp32_next_state_def] >> gs [SUC_ADD_SYM,SUC_SUC_add] >>
  `((agp32 fext fbits (t' + SUC n')).state = 1w) /\
  ((agp32 fext fbits (t' + SUC n')).command = 0w) /\
  (~(agp32 fext fbits (t' + SUC n')).do_interrupt)`
    by METIS_TAC [state_1w_command_do_interrupt_unchanged_after_not_ready_cycles] >>
  Q.ABBREV_TAC `t'' = t' + SUC n'` >>
  Q.ABBREV_TAC `s' = agp32 fext fbits t''` >>
  `(agp32 fext fbits (SUC t'')).state = (agp32_next_state (fext t'') s'' s'').state /\
  (agp32 fext fbits (SUC t'')).command = (agp32_next_state (fext t'') s'' s'').command`
    by fs [agp32_command_state_updated_by_agp32_next_state] >>
  `(fext t'').error = 0w` by fs [is_mem_def,mem_no_errors_def] >>
  fs [agp32_next_state_def] >> gs [] >>
  last_assum (mp_tac o is_mem_do_nothing `SUC t''`) >> rw [] >>
  Q.EXISTS_TAC `SUC (SUC n')` >> fs [Abbr `t''`,ADD1] >>
  gs [state_0w_fext_ready_hw_work]
QED


(** lemma for the interrupt interface **)
Theorem fext_InterruptReady_no_interrupt_ack[local]:
  !fext fbits t.
    is_interrupt_interface fext_accessor_circuit (agp32 fext fbits) fext ==>
    (fext t).interrupt_state = InterruptReady ==>
    ~(fext t).interrupt_ack
Proof
  rw [] >> Induct_on `t` >> rw [] >>
  qpat_assum `is_interrupt_interface _ _ _`
             (strip_assume_tac o SIMP_RULE (srw_ss())
              [is_interrupt_interface_def,fext_accessor_circuit_def]) >>
  pop_assum (qspec_then `t` assume_tac) >> rfs [] >>
  Cases_on `(fext t).interrupt_state` >> fs [] >>
  Cases_on `(agp32 fext fbits t).interrupt_req` >> fs [] >>
  Cases_on `m` >> fs [] >>
  `~(fext (SUC (0 + t))).interrupt_ack` by fs [] >> fs []
QED

Theorem fext_InterruptAck_interrupt_ack[local]:
  !fext fbits t.
    is_interrupt_interface fext_accessor_circuit (agp32 fext fbits) fext ==>
    (fext t).interrupt_state = InterruptAck ==>
    (fext t).interrupt_ack
Proof
  rw [] >> Induct_on `t` >> rw [] >>
  qpat_assum `is_interrupt_interface _ _ _`
             (strip_assume_tac o SIMP_RULE (srw_ss())
              [is_interrupt_interface_def,fext_accessor_circuit_def]) >>
  pop_assum (qspec_then `t` assume_tac) >> rfs [] >>
  Cases_on `(fext t).interrupt_state` >> fs [] >>
  Cases_on `(agp32 fext fbits t).interrupt_req` >> fs [] >>
  Cases_on `m` >> fs [] >>
  `(fext (SUC (0 + t))).interrupt_state = InterruptReady` by fs [] >> fs []
QED

Theorem state_4w_unchanged_after_not_interrupt_ack_cycles[local]:
  !fext fbits n t.
    is_mem fext_accessor_circuit (agp32 fext fbits) fext ==>
    (!p. p < SUC n ==> ~(fext (p + t)).interrupt_ack) ==>
    (agp32 fext fbits (SUC t)).state = 4w ==>
    (agp32 fext fbits (t + SUC n)).state = 4w
Proof
  rw [] >> Induct_on `n` >> rw [] >-
   fs [ADD1] >>
  `!p. p < SUC n ==> ~(fext (p + t)).interrupt_ack` by fs [] >> fs [] >>
  `~(fext (SUC n + t)).interrupt_ack` by fs [] >>
  `~(fext (t + SUC n)).interrupt_ack` by fs [] >>
  Q.ABBREV_TAC `t' = t + SUC n` >>
  `t + SUC (SUC n) = SUC t'` by gs [Abbr `t'`] >> fs [] >>
  Q.ABBREV_TAC `s' = agp32 fext fbits t'` >>
  `(agp32 fext fbits (SUC t')).state = (agp32_next_state (fext t') s' s').state`
    by fs [agp32_command_state_updated_by_agp32_next_state] >>
  `(fext t').error = 0w` by fs [is_mem_def,mem_no_errors_def] >>
  fs [agp32_next_state_def]
QED

(** state is 4w **)
Theorem agp32_hw_work_when_state_4w:
  !fext fbits t.
    is_mem fext_accessor_circuit (agp32 fext fbits) fext ==>
    is_interrupt_interface fext_accessor_circuit (agp32 fext fbits) fext ==>
    (agp32 fext fbits t).state = 4w ==>
    (fext 0).ready ==>
    ?n. hw_work (agp32 fext fbits (SUC (t + n)))
Proof
  rw [] >> qpat_assum `is_interrupt_interface _ _ _`
                      (strip_assume_tac o SIMP_RULE (srw_ss())
                       [is_interrupt_interface_def,fext_accessor_circuit_def]) >>
  pop_assum (qspec_then `t` assume_tac) >> rfs [] >>
  Cases_on `(fext t).interrupt_state` >> fs [] >-
   (`(agp32 fext fbits t).interrupt_req` by fs [agp32_state_4w_interrupt_req] >> fs [] >>
    Cases_on `m` >> fs [] >-
     (`~(fext t).interrupt_ack` by METIS_TAC [fext_InterruptReady_no_interrupt_ack] >>
      Q.ABBREV_TAC `s = agp32 fext fbits t` >>
      `(agp32 fext fbits (SUC t)).state = (agp32_next_state (fext t) s s).state`
        by fs [agp32_command_state_updated_by_agp32_next_state] >>
      `(fext t).error = 0w` by fs [is_mem_def,mem_no_errors_def] >>
      fs [agp32_next_state_def] >> gs [SUC_ADD_SYM] >>
      Q.ABBREV_TAC `t' = SUC t` >>
      Q.ABBREV_TAC `s' = agp32 fext fbits t'` >>
      `(agp32 fext fbits (SUC t')).state = (agp32_next_state (fext t') s' s').state`
        by fs [agp32_command_state_updated_by_agp32_next_state] >>
      `(fext t').error = 0w` by fs [is_mem_def,mem_no_errors_def] >>
      fs [agp32_next_state_def] >> gs [] >>
      Cases_on `(fext (SUC t')).ready` >-
       (Q.EXISTS_TAC `1` >>
        gs [state_0w_fext_ready_hw_work,ADD1]) >>
      `?n. hw_work (agp32 fext fbits (SUC ((SUC t' + n))))`
        by METIS_TAC [agp32_hw_work_when_state_0w_fext_not_ready] >>
      Q.EXISTS_TAC `SUC (SUC n)` >> fs [ADD1]) >>
    `~(fext t).interrupt_ack` by METIS_TAC [fext_InterruptReady_no_interrupt_ack] >>
    Q.ABBREV_TAC `s = agp32 fext fbits t` >>
    `(agp32 fext fbits (SUC t)).state = (agp32_next_state (fext t) s s).state`
      by fs [agp32_command_state_updated_by_agp32_next_state] >>
    `(fext t).error = 0w` by fs [is_mem_def,mem_no_errors_def] >>
    fs [agp32_next_state_def] >> gs [SUC_ADD_SYM,SUC_SUC_add] >>
    Q.ABBREV_TAC `t' = SUC t` >>
    subgoal `(agp32 fext fbits (SUC t')).state = 4w` >-
     (`~(fext (0 + t')).interrupt_ack` by fs [] >>
      Q.ABBREV_TAC `s0 = agp32 fext fbits t'` >>
      `(agp32 fext fbits (SUC t')).state = (agp32_next_state (fext t') s0 s0).state`
        by fs [agp32_command_state_updated_by_agp32_next_state] >>
      `(fext t').error = 0w` by fs [is_mem_def,mem_no_errors_def] >>
      fs [agp32_next_state_def]) >>       
    `(agp32 fext fbits (t' + SUC n)).state = 4w`
      by METIS_TAC [state_4w_unchanged_after_not_interrupt_ack_cycles] >>
    Q.ABBREV_TAC `t'' = t' + SUC n` >>
    Q.ABBREV_TAC `s' = agp32 fext fbits t''` >>
    `(agp32 fext fbits (SUC t'')).state = (agp32_next_state (fext t'') s' s').state`
      by fs [agp32_command_state_updated_by_agp32_next_state] >>
    `(fext t'').error = 0w` by fs [is_mem_def,mem_no_errors_def] >>
    fs [agp32_next_state_def] >> gs [] >>
    Cases_on `(fext (SUC t'')).ready` >-
     (Q.EXISTS_TAC `n + 2` >>
      gs [state_0w_fext_ready_hw_work,ADD1,Abbr `t''`]) >>
    `?n1. hw_work (agp32 fext fbits (SUC ((SUC t'' + n1))))`
      by METIS_TAC [agp32_hw_work_when_state_0w_fext_not_ready] >>
    Q.EXISTS_TAC `n + n1 + 3` >>
    gs [state_0w_fext_ready_hw_work,ADD1,Abbr `t''`]) >>
  `(fext t).interrupt_ack` by METIS_TAC [fext_InterruptAck_interrupt_ack] >>
  Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  `(agp32 fext fbits (SUC t)).state = (agp32_next_state (fext t) s s).state`
    by fs [agp32_command_state_updated_by_agp32_next_state] >>
  `(fext t).error = 0w` by fs [is_mem_def,mem_no_errors_def] >>
  fs [agp32_next_state_def] >> gs [] >>
  Cases_on `(fext (SUC t)).ready` >-
   (Q.EXISTS_TAC `0` >>
    gs [state_0w_fext_ready_hw_work]) >>
  rw [SUC_ADD_SYM] >>
  Q.ABBREV_TAC `t' = SUC t` >>
  `?n. hw_work (agp32 fext fbits (SUC (t' + n)))`
    by METIS_TAC [agp32_hw_work_when_state_0w_fext_not_ready] >>
  Q.EXISTS_TAC `SUC n` >> fs [ADD1]                                       
QED


(** state is 1w **)
Theorem agp32_hw_work_when_state_1w:
  !fext fbits t.
    is_mem fext_accessor_circuit (agp32 fext fbits) fext ==>
    is_interrupt_interface fext_accessor_circuit (agp32 fext fbits) fext ==>
    (agp32 fext fbits t).state = 1w ==>
    (fext 0).ready ==>
    ?n. hw_work (agp32 fext fbits (SUC (t + n)))
Proof
  rw [] >> Cases_on `(fext t).ready` >-
   (Cases_on `(agp32 fext fbits t).command = 0w` >-
     (Cases_on `~(agp32 fext fbits t).do_interrupt` >> fs [] >>
      Q.ABBREV_TAC `s = agp32 fext fbits t` >>
      `(agp32 fext fbits (SUC t)).state = (agp32_next_state (fext t) s s).state /\
      (agp32 fext fbits (SUC t)).command = (agp32_next_state (fext t) s s).command`
        by fs [agp32_command_state_updated_by_agp32_next_state] >>
      `(fext t).error = 0w` by fs [is_mem_def,mem_no_errors_def] >>
      fs [agp32_next_state_def] >> gs [] >-
       (last_assum (mp_tac o is_mem_do_nothing `SUC t`) >> rw [] >>
        Q.EXISTS_TAC `0` >>
        gs [state_0w_fext_ready_hw_work]) >>
      `?n. hw_work (agp32 fext fbits (SUC (SUC t + n)))`
        by METIS_TAC [agp32_hw_work_when_state_4w] >>
      Q.EXISTS_TAC `n + 1` >> fs [ADD1]) >>
    Cases_on `~(agp32 fext fbits t).do_interrupt` >> fs [] >>
    Q.ABBREV_TAC `s = agp32 fext fbits t` >>
    `(agp32 fext fbits (SUC t)).state = (agp32_next_state (fext t) s s).state /\
    (agp32 fext fbits (SUC t)).command = (agp32_next_state (fext t) s s).command`
      by fs [agp32_command_state_updated_by_agp32_next_state] >>
    `(agp32 fext fbits (SUC t)).do_interrupt = (agp32_next_state (fext t) s s).do_interrupt`
      by fs [agp32_interrupt_items_updated_by_agp32_next_state] >>
    `(fext t).error = 0w` by fs [is_mem_def,mem_no_errors_def] >>
    fs [agp32_next_state_def] >> gs [] >>
    last_assum (mp_tac o is_mem_do_nothing `SUC t`) >> rw [] >>
    Q.ABBREV_TAC `t' = SUC t` >>
    Q.ABBREV_TAC `s' = agp32 fext fbits t'` >>
    `(agp32 fext fbits (SUC t')).state = (agp32_next_state (fext t') s' s').state /\
    (agp32 fext fbits (SUC t')).command = (agp32_next_state (fext t') s' s').command`
      by fs [agp32_command_state_updated_by_agp32_next_state] >>
    `(fext t').error = 0w` by fs [is_mem_def,mem_no_errors_def] >>
    fs [agp32_next_state_def] >> gs [] >-
     (last_assum (mp_tac o is_mem_do_nothing `SUC t'`) >> rw [] >>
      Q.EXISTS_TAC `1` >>
      gs [state_0w_fext_ready_hw_work,ADD1]) >>
    `?n. hw_work (agp32 fext fbits (SUC (SUC t' + n)))`
      by METIS_TAC [agp32_hw_work_when_state_4w] >>
    Q.EXISTS_TAC `n + 2` >> fs [ADD1,Abbr `t'`]) >>
  `?n. (fext (SUC (t + n))).ready /\ (!p. p < n ==> ~(fext (SUC (t + p))).ready)`
    by METIS_TAC [fext_not_ready_imply_future_ready] >>
  Cases_on `n` >> fs [] >-                             
   (Cases_on `~(agp32 fext fbits t).do_interrupt` >> fs [] >>
    Q.ABBREV_TAC `s = agp32 fext fbits t` >>
    `(agp32 fext fbits (SUC t)).state = (agp32_next_state (fext t) s s).state /\
    (agp32 fext fbits (SUC t)).command = (agp32_next_state (fext t) s s).command`
      by fs [agp32_command_state_updated_by_agp32_next_state] >>
    `(agp32 fext fbits (SUC t)).do_interrupt = (agp32_next_state (fext t) s s).do_interrupt`
      by fs [agp32_interrupt_items_updated_by_agp32_next_state] >>
    `(fext t).error = 0w` by fs [is_mem_def,mem_no_errors_def] >>
    fs [agp32_next_state_def] >> gs [SUC_ADD_SYM] >>
    Q.ABBREV_TAC `t' = SUC t` >>
    Q.ABBREV_TAC `s' = agp32 fext fbits t'` >>
    `(agp32 fext fbits (SUC t')).state = (agp32_next_state (fext t') s' s').state /\
    (agp32 fext fbits (SUC t')).command = (agp32_next_state (fext t') s' s').command`
      by fs [agp32_command_state_updated_by_agp32_next_state] >>
    `(agp32 fext fbits (SUC t')).do_interrupt = (agp32_next_state (fext t') s' s').do_interrupt`
      by fs [agp32_interrupt_items_updated_by_agp32_next_state] >>
    `(fext t').error = 0w` by fs [is_mem_def,mem_no_errors_def] >>
    fs [agp32_next_state_def] >> gs [] >-
     (last_assum (mp_tac o is_mem_do_nothing `SUC t'`) >> rw [] >>
      Q.EXISTS_TAC `1` >>
      gs [state_0w_fext_ready_hw_work,ADD1]) >>
    `?n. hw_work (agp32 fext fbits (SUC (SUC t' + n)))`
      by METIS_TAC [agp32_hw_work_when_state_4w] >>
    Q.EXISTS_TAC `n + 2` >> fs [ADD1]) >>
  Cases_on `~(agp32 fext fbits t).do_interrupt` >> fs [] >>
  `0 < SUC n'` by fs [] >>
  `~(fext (SUC (t + 0))).ready` by METIS_TAC [ADD_COMM] >> fs [] >>
  Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  `(agp32 fext fbits (SUC t)).state = (agp32_next_state (fext t) s s).state /\
  (agp32 fext fbits (SUC t)).command = (agp32_next_state (fext t) s s).command`
    by fs [agp32_command_state_updated_by_agp32_next_state] >>
  `(agp32 fext fbits (SUC t)).do_interrupt = (agp32_next_state (fext t) s s).do_interrupt`
    by fs [agp32_interrupt_items_updated_by_agp32_next_state] >>
  `(fext t).error = 0w` by fs [is_mem_def,mem_no_errors_def] >>
  fs [agp32_next_state_def] >> gs [SUC_ADD_SYM] >>
  Q.ABBREV_TAC `t' = SUC t` >>
  Q.ABBREV_TAC `s' = agp32 fext fbits t'` >>
  `(agp32 fext fbits (SUC t')).state = (agp32_next_state (fext t') s' s').state /\
  (agp32 fext fbits (SUC t')).command = (agp32_next_state (fext t') s' s').command`
    by fs [agp32_command_state_updated_by_agp32_next_state] >>
  `(agp32 fext fbits (SUC t')).do_interrupt = (agp32_next_state (fext t') s' s').do_interrupt`
    by fs [agp32_interrupt_items_updated_by_agp32_next_state] >>
  `(fext t').error = 0w` by fs [is_mem_def,mem_no_errors_def] >>
  fs [agp32_next_state_def] >> gs [SUC_SUC_add] >-
   (`((agp32 fext fbits (t' + SUC n')).state = 1w) /\
    ((agp32 fext fbits (t' + SUC n')).command = 0w) /\
    (~(agp32 fext fbits (t' + SUC n')).do_interrupt)`
      by METIS_TAC [state_1w_command_do_interrupt_unchanged_after_not_ready_cycles] >>
    Q.ABBREV_TAC `t'' = t' + SUC n'` >>
    Q.ABBREV_TAC `s'' = agp32 fext fbits t''` >>
    `(agp32 fext fbits (SUC t'')).state = (agp32_next_state (fext t'') s'' s'').state /\
    (agp32 fext fbits (SUC t'')).command = (agp32_next_state (fext t'') s'' s'').command`
      by fs [agp32_command_state_updated_by_agp32_next_state] >>
    `(fext t'').error = 0w` by fs [is_mem_def,mem_no_errors_def] >>
    fs [agp32_next_state_def] >> gs [] >>      
    last_assum (mp_tac o is_mem_do_nothing `SUC t''`) >> rw [] >>
    Q.EXISTS_TAC `SUC (SUC n')` >> fs [Abbr `t''`,ADD1] >>
    gs [state_0w_fext_ready_hw_work]) >>
  `((agp32 fext fbits (t' + SUC n')).state = 1w) /\
  ((agp32 fext fbits (t' + SUC n')).command = 0w) /\
  ((agp32 fext fbits (t' + SUC n')).do_interrupt)`
    by METIS_TAC [state_1w_command_do_interrupt_unchanged_after_not_ready_cycles_extra] >>
  Q.ABBREV_TAC `t'' = t' + SUC n'` >>
  Q.ABBREV_TAC `s'' = agp32 fext fbits t''` >>
  `(agp32 fext fbits (SUC t'')).state = (agp32_next_state (fext t'') s'' s'').state`
    by fs [agp32_command_state_updated_by_agp32_next_state] >>
  `(fext t'').error = 0w` by fs [is_mem_def,mem_no_errors_def] >>
  fs [agp32_next_state_def] >> gs [] >>
  `?n. hw_work (agp32 fext fbits (SUC (SUC t'' + n)))`
    by METIS_TAC [agp32_hw_work_when_state_4w] >>
  Q.EXISTS_TAC `n' + n + 3` >> fs [ADD1,Abbr `t''`]
QED


(** lemma for mem_start_ready **)
(** state is 3 then state is 3 at all previous cycles **)
Theorem agp32_state_3_mem_start_not_ready_state_3[local]:
  !fext fbits t n.
    is_mem fext_accessor_circuit (agp32 fext fbits) fext ==>
    (agp32 fext fbits t).state = 3w ==>
    n > t ==>
    (!m. m < n ==> ~(fext m).mem_start_ready) ==>
    (agp32 fext fbits n).state = 3w
Proof
  rw [] >> Induct_on `n` >> rw [] >>
  Cases_on `t = n` >> fs [] >>
  `~(fext n).mem_start_ready` by fs [] >>
  Q.ABBREV_TAC `s = agp32 fext fbits n` >>
  `(agp32 fext fbits (SUC n)).state = (agp32_next_state (fext n) s s).state`
    by fs [agp32_command_state_updated_by_agp32_next_state] >>
  `(fext n).error = 0w` by fs [is_mem_def,mem_no_errors_def] >>
  fs [agp32_next_state_def]
QED

(** state is 3w **)
Theorem agp32_hw_work_when_state_3w:
  !fext fbits t.
    is_mem fext_accessor_circuit (agp32 fext fbits) fext ==>
    is_mem_start_interface fext ==>
    is_interrupt_interface fext_accessor_circuit (agp32 fext fbits) fext ==>
    (agp32 fext fbits t).state = 3w ==>
    (fext 0).ready ==>
    ?n. hw_work (agp32 fext fbits (SUC (t + n)))
Proof
  rw [is_mem_start_interface_def] >>
  Cases_on `n = t` >-
   (Q.ABBREV_TAC `s = agp32 fext fbits t` >>
    `(agp32 fext fbits (SUC t)).state = (agp32_next_state (fext t) s s).state`
      by fs [agp32_command_state_updated_by_agp32_next_state] >>
    `(fext t).error = 0w` by fs [is_mem_def,mem_no_errors_def] >>
    fs [agp32_next_state_def] >> gs [] >>
    `?n'. hw_work (agp32 fext fbits (SUC (SUC t + n')))`
      by METIS_TAC [agp32_hw_work_when_state_1w] >>
    Q.EXISTS_TAC `n' + 1` >> fs [ADD1]) >>
  Cases_on `n < t` >> fs [] >-
   (`(agp32 fext fbits n).state = 3w` by METIS_TAC [agp32_state_3_all_previous_state_3] >>
    Q.ABBREV_TAC `s = agp32 fext fbits n` >>
    `(agp32 fext fbits (SUC n)).state = (agp32_next_state (fext n) s s).state`
      by fs [agp32_command_state_updated_by_agp32_next_state] >>
    `(fext n).error = 0w` by fs [is_mem_def,mem_no_errors_def] >>
    fs [agp32_next_state_def] >> gs [] >>
    Cases_on `SUC n = t` >> fs [] >>
    Cases_on `SUC n > t` >> fs [] >>
    `SUC n < t` by fs [] >>
    `(agp32 fext fbits (SUC n)).state = 3w`
      by METIS_TAC [agp32_state_3_all_previous_state_3]  >> fs []) >>
  `n > t` by fs [] >> fs [] >>
  `(agp32 fext fbits n).state = 3w` by METIS_TAC [agp32_state_3_mem_start_not_ready_state_3] >>
  Q.ABBREV_TAC `s = agp32 fext fbits n` >>
  `(agp32 fext fbits (SUC n)).state = (agp32_next_state (fext n) s s).state`
    by fs [agp32_command_state_updated_by_agp32_next_state] >>
  `(fext n).error = 0w` by fs [is_mem_def,mem_no_errors_def] >>
  fs [agp32_next_state_def] >> gs [] >>
  `?n'. hw_work (agp32 fext fbits (SUC (SUC n + n')))`
    by METIS_TAC [agp32_hw_work_when_state_1w] >>
  `?p. n = t + (p + 1)` by gs [GREATER_DEF,LESS_ADD_1] >>
  Q.EXISTS_TAC `p + n' + 2` >> fs [ADD_COMM,ADD1]
QED
        

(** state is 2w **)
Theorem agp32_hw_work_when_state_2w:
  !fext fbits t.
    is_mem fext_accessor_circuit (agp32 fext fbits) fext ==>
    is_interrupt_interface fext_accessor_circuit (agp32 fext fbits) fext ==>
    (agp32 fext fbits t).state = 2w ==>
    (fext 0).ready ==>
    ?n. hw_work (agp32 fext fbits (SUC (t + n)))
Proof
  rw [] >> Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state; WB_pipeline; MEM_pipeline; EX_pipeline;
                            REG_write; ID_pipeline; IF_PC_update] (fext t) s s` >>
  `(agp32 fext fbits (SUC t)).acc_res_ready = (Acc_compute (fext t) s s').acc_res_ready /\
  (agp32 fext fbits (SUC t)).acc_state = (Acc_compute (fext t) s s').acc_state`
    by gs [agp32_acc_state_res_and_ready_updated_by_Acc_compute] >>
  fs [Acc_compute_def] >>
  Cases_on `s.acc_arg_ready` >> fs [] >-
   (`(agp32 fext fbits (SUC t)).state = (agp32_next_state (fext t) s s).state`
      by fs [agp32_command_state_updated_by_agp32_next_state] >>
    `(agp32 fext fbits (SUC t)).acc_arg_ready = (agp32_next_state (fext t) s s).acc_arg_ready`
      by fs [agp32_acc_arg_and_ready_updated_by_agp32_next_state] >>
    `(fext t).error = 0w` by fs [is_mem_def,mem_no_errors_def] >>
    fs [agp32_next_state_def] >> gs [SUC_ADD_SYM] >>
    Q.ABBREV_TAC `t' = SUC t` >>
    Q.ABBREV_TAC `s'' = agp32 fext fbits t'` >>
    Q.ABBREV_TAC `s3 = procs [agp32_next_state; WB_pipeline; MEM_pipeline; EX_pipeline;
                              REG_write; ID_pipeline; IF_PC_update] (fext t') s'' s''` >>
    `(agp32 fext fbits (SUC t')).acc_res_ready = (Acc_compute (fext t') s'' s3).acc_res_ready /\
    (agp32 fext fbits (SUC t')).acc_state = (Acc_compute (fext t') s'' s3).acc_state`
      by gs [agp32_acc_state_res_and_ready_updated_by_Acc_compute] >>
    `s3.acc_state = s''.acc_state /\ (s3.acc_res_ready = s''.acc_res_ready)`
      by METIS_TAC [Abbr `s3`,Abbr `s''`,agp32_same_acc_items_until_Acc_compute] >>
    fs [Acc_compute_def] >> gs [] >>
    `(agp32 fext fbits (SUC t')).state = (agp32_next_state (fext t') s'' s'').state`
      by fs [agp32_command_state_updated_by_agp32_next_state] >>
    `(agp32 fext fbits (SUC t')).acc_arg_ready = (agp32_next_state (fext t') s'' s'').acc_arg_ready`
      by fs [agp32_acc_arg_and_ready_updated_by_agp32_next_state] >>
    `(fext t').error = 0w` by fs [is_mem_def,mem_no_errors_def] >>
    fs [agp32_next_state_def] >> gs [] >>
    Q.ABBREV_TAC `t'' = SUC t'` >>
    Q.ABBREV_TAC `s4 = agp32 fext fbits t''` >>
    Q.ABBREV_TAC `s5 = procs [agp32_next_state; WB_pipeline; MEM_pipeline; EX_pipeline;
                              REG_write; ID_pipeline; IF_PC_update] (fext t'') s4 s4` >>
    `(agp32 fext fbits (SUC t'')).acc_res_ready = (Acc_compute (fext t'') s4 s5).acc_res_ready /\
    (agp32 fext fbits (SUC t'')).acc_state = (Acc_compute (fext t'') s4 s5).acc_state`
      by gs [agp32_acc_state_res_and_ready_updated_by_Acc_compute] >>
    `s5.acc_state = s4.acc_state /\ (s5.acc_res_ready = s4.acc_res_ready)`
      by METIS_TAC [Abbr `s5`,Abbr `s4`,agp32_same_acc_items_until_Acc_compute] >>
    fs [Acc_compute_def] >> gs [] >>
    `(agp32 fext fbits (SUC t'')).state = (agp32_next_state (fext t'') s4 s4).state`
      by fs [agp32_command_state_updated_by_agp32_next_state] >>
    `(agp32 fext fbits (SUC t'')).acc_arg_ready = (agp32_next_state (fext t'') s4 s4).acc_arg_ready`
      by fs [agp32_acc_arg_and_ready_updated_by_agp32_next_state] >>
    `(fext t'').error = 0w` by fs [is_mem_def,mem_no_errors_def] >>
    fs [agp32_next_state_def] >> gs [] >>
    Q.ABBREV_TAC `t''' = SUC t''` >>
    Q.ABBREV_TAC `s6 = agp32 fext fbits t'''` >>
    `(agp32 fext fbits (SUC t''')).state = (agp32_next_state (fext t''') s6 s6).state`
      by fs [agp32_command_state_updated_by_agp32_next_state] >>
    `(fext t''').error = 0w` by fs [is_mem_def,mem_no_errors_def] >>
    fs [agp32_next_state_def] >> gs [] >>
    Cases_on `(fext (SUC t''')).ready` >-
     (Q.EXISTS_TAC `3` >>
      gs [Abbr `t'''`,Abbr `t''`,ADD1,state_0w_fext_ready_hw_work]) >>
    `?n. hw_work (agp32 fext fbits (SUC ((SUC t''' + n))))`
      by METIS_TAC [agp32_hw_work_when_state_0w_fext_not_ready] >>
    Q.EXISTS_TAC `n + 4` >> fs [Abbr `t'''`,Abbr `t''`,ADD1]) >>
  `s'.acc_state = s.acc_state /\ (s'.acc_res_ready = s.acc_res_ready)`
    by METIS_TAC [Abbr `s'`,Abbr `s`,agp32_same_acc_items_until_Acc_compute] >>
  `(s.acc_state = 0w) \/ (s.acc_state = 1w)`
    by METIS_TAC [agp32_acc_state_possible_values,Abbr `s`] >> fs [] >-
   (Cases_on `t = 0` >-
     fs [Abbr `s`,agp32_init_state_3w] >>
    `~s.acc_res_ready` by gs [agp32_acc_state_0w_then_acc_res_not_ready,Abbr `s`] >>
    `(agp32 fext fbits (SUC t)).state = (agp32_next_state (fext t) s s).state`
      by fs [agp32_command_state_updated_by_agp32_next_state] >>
    `(agp32 fext fbits (SUC t)).acc_arg_ready = (agp32_next_state (fext t) s s).acc_arg_ready`
      by fs [agp32_acc_arg_and_ready_updated_by_agp32_next_state] >>
    `(fext t).error = 0w` by fs [is_mem_def,mem_no_errors_def] >>
    fs [agp32_next_state_def] >> gs [SUC_ADD_SYM] >>                  
    Q.ABBREV_TAC `t' = SUC t` >>
    Q.ABBREV_TAC `s'' = agp32 fext fbits t'` >>
    Q.ABBREV_TAC `s3 = procs [agp32_next_state; WB_pipeline; MEM_pipeline; EX_pipeline;
                              REG_write; ID_pipeline; IF_PC_update] (fext t') s'' s''` >>
    `(agp32 fext fbits (SUC t')).acc_res_ready = (Acc_compute (fext t') s'' s3).acc_res_ready /\
    (agp32 fext fbits (SUC t')).acc_state = (Acc_compute (fext t') s'' s3).acc_state`
      by gs [agp32_acc_state_res_and_ready_updated_by_Acc_compute] >>
    `s3.acc_state = s''.acc_state /\ (s3.acc_res_ready = s''.acc_res_ready)`
      by METIS_TAC [Abbr `s3`,Abbr `s''`,agp32_same_acc_items_until_Acc_compute] >>
    fs [Acc_compute_def] >> gs [] >>
    `(agp32 fext fbits (SUC t')).state = (agp32_next_state (fext t') s'' s'').state`
      by fs [agp32_command_state_updated_by_agp32_next_state] >>
    `(agp32 fext fbits (SUC t')).acc_arg_ready = (agp32_next_state (fext t') s'' s'').acc_arg_ready`
      by fs [agp32_acc_arg_and_ready_updated_by_agp32_next_state] >>
    `(fext t').error = 0w` by fs [is_mem_def,mem_no_errors_def] >>
    fs [agp32_next_state_def] >> gs [] >>                  
    Q.ABBREV_TAC `t'' = SUC t'` >>
    Q.ABBREV_TAC `s4 = agp32 fext fbits t''` >>
    `(agp32 fext fbits (SUC t'')).state = (agp32_next_state (fext t'') s4 s4).state`
      by fs [agp32_command_state_updated_by_agp32_next_state] >>
    `(fext t'').error = 0w` by fs [is_mem_def,mem_no_errors_def] >>
    fs [agp32_next_state_def] >> gs [] >>
    Cases_on `(fext (SUC t'')).ready` >-
     (Q.EXISTS_TAC `2` >>
      gs [Abbr `t''`,ADD1,state_0w_fext_ready_hw_work]) >>
    `?n. hw_work (agp32 fext fbits (SUC ((SUC t'' + n))))`
      by METIS_TAC [agp32_hw_work_when_state_0w_fext_not_ready] >>
    Q.EXISTS_TAC `n + 3` >> fs [Abbr `t''`,ADD1]) >>
  `(agp32 fext fbits (SUC t)).state = (agp32_next_state (fext t) s s).state`
    by fs [agp32_command_state_updated_by_agp32_next_state] >>                           
  `(agp32 fext fbits (SUC t)).acc_arg_ready = (agp32_next_state (fext t) s s).acc_arg_ready`
    by fs [agp32_acc_arg_and_ready_updated_by_agp32_next_state] >>
  `(fext t).error = 0w` by fs [is_mem_def,mem_no_errors_def] >>
  fs [agp32_next_state_def] >> gs [SUC_ADD_SYM] >>
  Cases_on `s.acc_res_ready` >> fs [] >-
   (Cases_on `(fext (SUC t)).ready` >-
     (Q.EXISTS_TAC `0` >>
      gs [state_0w_fext_ready_hw_work]) >>
    `?n. hw_work (agp32 fext fbits (SUC ((SUC t + n))))`
      by METIS_TAC [agp32_hw_work_when_state_0w_fext_not_ready] >>
    Q.EXISTS_TAC `n + 1` >> fs [ADD1]) >>
  Q.ABBREV_TAC `t' = SUC t` >>          
  Q.ABBREV_TAC `s'' = agp32 fext fbits t'` >>
  `(agp32 fext fbits (SUC t')).state = (agp32_next_state (fext t') s'' s'').state`
    by fs [agp32_command_state_updated_by_agp32_next_state] >>
  `(fext t').error = 0w` by fs [is_mem_def,mem_no_errors_def] >>
  fs [agp32_next_state_def] >> gs [] >>
  Cases_on `(fext (SUC t')).ready` >-
   (Q.EXISTS_TAC `1` >>
    gs [Abbr `t'`,state_0w_fext_ready_hw_work,ADD1]) >>
  `?n. hw_work (agp32 fext fbits (SUC ((SUC t' + n))))`
    by METIS_TAC [agp32_hw_work_when_state_0w_fext_not_ready] >>
  Q.EXISTS_TAC `n + 2` >> fs [ADD1]
QED


(* the pipelined Silver can continue to work under assumptions *)
Theorem agp32_hw_work_exists:
  !fext fbits s a t I.
    s = agp32 fext fbits ==>
    is_mem fext_accessor_circuit s fext ==>
    is_mem_start_interface fext ==>
    is_interrupt_interface fext_accessor_circuit s fext ==>
    is_sch I s a ==>
    ~hw_work (s t) ==>
    (fext 0).ready ==>
    ?n. hw_work (s (SUC (t + n)))
Proof
  rw [] >> Cases_on_word_value `(agp32 fext fbits t).state` >>
  fs [agp32_state_impossible_values] >-
   gs [agp32_state_impossible_5_no_fext_error] >-
   METIS_TAC [agp32_hw_work_when_state_4w,ADD_COMM] >-
   METIS_TAC [agp32_hw_work_when_state_3w,ADD_COMM] >-
   METIS_TAC [agp32_hw_work_when_state_2w,ADD_COMM] >-
   METIS_TAC [agp32_hw_work_when_state_1w,ADD_COMM] >>
  Cases_on `(fext t).ready` >-
   fs [hw_work_def,enable_stg_def,agp32_state_fext_ready_and_WB_state_flag] >>
  METIS_TAC [agp32_hw_work_when_state_0w_fext_not_ready,ADD_COMM]
QED


(** progress of the scheduling **)
Theorem agp32_progress_partical:
  !fext fbits s a t I.
    s = agp32 fext fbits ==>
    is_mem fext_accessor_circuit s fext ==>
    is_mem_start_interface fext ==>
    is_acc accelerator_f s ==>
    is_interrupt_interface fext_accessor_circuit s fext ==>
    is_sch I s a ==>
    ~hw_work (s t) ==>
    (fext 0).ready ==>
    ?n k. k >= 1 ==> k <= 5 ==>
          I (k,SUC (SUC (t + n))) = I (k - 1,SUC (t + n))
Proof
  rw [] >>
  `?n. hw_work (agp32 fext fbits (SUC (t + n)))` by METIS_TAC [agp32_hw_work_exists] >>
  Q.EXISTS_TAC `n` >> gs [] >>
  METIS_TAC [agp32_hw_work_instr_processed]
QED

(*
Theorem agp32_progress_none_MEM:
  !fext fbits s a t I.
    s = agp32 fext fbits ==>
    is_mem fext_accessor_circuit s fext ==>
    is_mem_start_interface fext ==>
    is_acc accelerator_f s ==>
    is_interrupt_interface fext_accessor_circuit s fext ==>
    is_sch I s a ==>
    I (4,t) = NONE ==>
    ?n. I (4,SUC (t + n)) <> NONE
Proof
  rw [] >> cheat
QED

Theorem agp32_progress_none_WB:
  !fext fbits s a t I.
    s = agp32 fext fbits ==>
    is_mem fext_accessor_circuit s fext ==>
    is_mem_start_interface fext ==>
    is_acc accelerator_f s ==>
    is_interrupt_interface fext_accessor_circuit s fext ==>
    is_sch I s a ==>
    I (5,t) = NONE ==>
    ?n. I (5,SUC (t + n)) <> NONE
Proof
  rw [] >> Cases_on `enable_stg 5 (agp32 fext fbits t)` >-
   (`I' (5,SUC t) = I' (4,t)` by gs [is_sch_def,is_sch_writeback_def] >>
    Cases_on `I' (4,t) <> NONE` >-
     (Q.EXISTS_TAC `0` >> fs []) >>
    fs [] >> `?n. I' (4,SUC (t + n)) <> NONE` by METIS_TAC [agp32_progress_none_MEM] >>
    cheat) >>
  cheat      
QED

Theorem agp32_progress_none:
  !fext fbits s a t k I.
    s = agp32 fext fbits ==>
    is_mem fext_accessor_circuit s fext ==>
    is_mem_start_interface fext ==>
    is_acc accelerator_f s ==>
    is_interrupt_interface fext_accessor_circuit s fext ==>
    is_sch I s a ==>
    k >= 1 ==>
    k <= 5 ==>
    I (k,t) = NONE ==>
    ?n. I (k,SUC (t + n)) <> NONE
Proof
  rw [] >> `k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5` by fs [] >> fs [] >-
   (Cases_on `enable_stg 1 (agp32 fext fbits t)` >-
     (Cases_on `isJump_hw_op (agp32 fext fbits t)` >-
       (Q.EXISTS_TAC `0` >> gs [is_sch_def,is_sch_fetch_def]) >>
      cheat >>
      cheat) >>
    cheat) >-
   cheat >-
   cheat >-
   METIS_TAC [agp32_progress_none_MEM,ADD_COMM] >>
  METIS_TAC [agp32_progress_none_WB,ADD_COMM]
QED

Theorem agp32_progress_not_none:
  !fext fbits s a t k I.
    s = agp32 fext fbits ==>
    is_mem fext_accessor_circuit s fext ==>
    is_mem_start_interface fext ==>
    is_acc accelerator_f s ==>
    is_interrupt_interface fext_accessor_circuit s fext ==>
    is_sch I s a ==>
    k >= 1 ==>
    k <= 5 ==>
    I (k,t) <> NONE ==>
    ?n. THE (I (k,SUC (t + n))) > THE (I (k,t))
Proof
  rw [] >> `k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5` by fs [] >> fs [] >-
   (Cases_on `enable_stg 1 (agp32 fext fbits t)` >-
     (Cases_on `isJump_hw_op (agp32 fext fbits t)` >-
       cheat >>
      Cases_on `isJump_isa_op (I' (1,t)) a \/ isJump_isa_op (I' (2,t)) a` >-
       cheat >>
      Q.EXISTS_TAC `0` >> gs [is_sch_def,is_sch_fetch_def]) >>
    cheat) >>
  cheat
QED

Theorem agp32_progress:
  !fext fbits s a t k I.
    s = agp32 fext fbits ==>
    is_mem fext_accessor_circuit s fext ==>
    is_mem_start_interface fext ==>
    is_acc accelerator_f s ==>
    is_interrupt_interface fext_accessor_circuit s fext ==>
    is_sch I s a ==>
    k >= 1 ==>
    k <= 5 ==>
    (I (k,t) <> NONE ==> ?n. THE (I (k,SUC (t + n))) > THE (I (k,t))) /\
    (I (k,t) = NONE ==> ?n. I (k,SUC (t + n)) <> NONE)
Proof
  rpt strip_tac >>
  METIS_TAC [agp32_progress_none,agp32_progress_not_none,ADD_COMM]
QED
*)

val _ = export_theory ();
