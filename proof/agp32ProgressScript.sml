open hardwarePreamble translatorTheory translatorLib arithmeticTheory dep_rewrite blastLib bitstringSyntax fcpSyntax listSyntax wordsSyntax agp32StateTheory agp32EnvironmentTheory agp32ProcessorTheory ag32Theory ag32ExtraTheory ag32UtilitiesTheory agp32RelationTheory agp32UpdateTheory agp32InternalTheory agp32StepLib;

(* the pipelined Silver circuit makes progress based on the environment *)
val _ = new_theory "agp32Progress";

val _ = prefer_num ();
val _ = guess_lengths ();


(** extra definition: help property for ready singal **)
Definition is_mem_extra_ready_def:
  is_mem_extra_ready fext =
  (!t. ~(fext t).ready ==>
       ?n. (fext (SUC (t + n))).ready /\
           (!p. p < n ==> ~(fext (SUC (t + p))).ready))
End

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
  !fext t.
    is_mem_extra_ready fext ==>
    ~(fext t).ready ==>
    ?n. (fext (SUC (t + n))).ready /\
        (!p. p < n ==> ~(fext (SUC (t + p))).ready)
Proof
  rw [is_mem_extra_ready_def]
QED

Theorem SUC_SUC_add[local]:
  !a b.
    a + SUC (SUC b) = (SUC a) + (SUC b)
Proof
  rw []
QED

Theorem state_1w_command_do_interrupt_unchanged_after_disabled_cycles[local]:
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
  `(fext t').error = 0w` by fs [is_mem_def,mem_no_errors_def]>>
  fs [agp32_next_state_def]
QED

(** state is 0w and fext is not ready **)
Theorem agp32_hw_work_when_state_0w_fext_not_ready:
  !fext fbits t.
    is_mem fext_accessor_circuit (agp32 fext fbits) fext ==>
    is_mem_extra_ready fext ==>
    (agp32 fext fbits t).state = 0w ==>
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
    by METIS_TAC [state_1w_command_do_interrupt_unchanged_after_disabled_cycles] >>
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

(** state is 4w **)
Theorem agp32_hw_work_when_state_4w:
  !fext fbits t.
    is_mem fext_accessor_circuit (agp32 fext fbits) fext ==>
    is_interrupt_interface fext_accessor_circuit (agp32 fext fbits) fext ==>
    (agp32 fext fbits t).state = 4w ==>
    ?n. hw_work (agp32 fext fbits (SUC (t + n)))
Proof
  rw [] >> qpat_assum `is_interrupt_interface _ _ _`
                      (strip_assume_tac o SIMP_RULE (srw_ss())
                       [is_interrupt_interface_def,fext_accessor_circuit_def]) >>
  pop_assum (qspec_then `t` assume_tac) >> rfs [] >>
  Cases_on `(fext t).interrupt_state` >> fs [] >-
   (`(agp32 fext fbits t).interrupt_req` by fs [agp32_state_4w_interrupt_req] >> fs [] >>
    cheat) >>
  cheat 
QED


(* the pipelined Silver can continue to work under assumptions *)
Theorem agp32_hw_work_exists:
  !fext fbits s a t I.
    s = agp32 fext fbits ==>
    is_mem fext_accessor_circuit s fext ==>
    is_mem_extra_ready fext ==>
    is_acc accelerator_f s ==>
    is_interrupt_interface fext_accessor_circuit s fext ==>
    is_sch I s a ==>
    ~hw_work (s t) ==>
    ?n. hw_work (s (SUC (t + n)))
Proof
  rw [] >> Cases_on_word_value `(agp32 fext fbits t).state` >>
  fs [agp32_state_impossible_values] >-
   gs [agp32_state_impossible_5_no_fext_error] >-
   METIS_TAC [agp32_hw_work_when_state_4w,ADD_COMM] >-
   cheat >-
   cheat >-
   cheat >>
  Cases_on `(fext t).ready` >-
   fs [hw_work_def,enable_stg_def,agp32_state_fext_ready_and_WB_state_flag] >>
  METIS_TAC [agp32_hw_work_when_state_0w_fext_not_ready,ADD_COMM]
QED


(* the pipelined Silver can make progress *)
Theorem agp32_progress:
  !fext fbits s a t I.
    s = agp32 fext fbits ==>
    is_mem fext_accessor_circuit s fext ==>
    is_mem_extra_ready fext ==>
    is_acc accelerator_f s ==>
    is_interrupt_interface fext_accessor_circuit s fext ==>
    is_sch I s a ==>
    ~hw_work (s t) ==>
    ?n k. k >= 1 ==> k <= 5 ==>
          I (k,SUC (SUC (t + n))) = I (k - 1,SUC (t + n))
Proof
  rw [] >>
  `?n. hw_work (agp32 fext fbits (SUC (t + n)))` by METIS_TAC [agp32_hw_work_exists] >>
  Q.EXISTS_TAC `n` >> gs [] >>
  METIS_TAC [agp32_hw_work_instr_processed]
QED

val _ = export_theory ();
