open hardwarePreamble translatorTheory translatorLib arithmeticTheory pred_setTheory dep_rewrite blastLib bitstringSyntax fcpSyntax listSyntax wordsSyntax agp32StateTheory agp32EnvironmentTheory agp32ProcessorTheory ag32Theory ag32ExtraTheory ag32UtilitiesTheory agp32RelationTheory agp32UpdateTheory agp32InternalTheory agp32StepLib;

(* correctness of IF stage and related items with repsect to the ISA *)
val _ = new_theory "agp32_IF_Correct";

val _ = prefer_num ();
val _ = guess_lengths ();


(* IF related items *)
(** PC **)
(** PC updated when IF is enabled **)
Theorem agp32_Rel_ag32_IF_enable_PC_correct:
  !fext fbits a t I.
    is_sch_fetch I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    enable_stg 1 (agp32 fext fbits t) ==>
    I (1,SUC t) <> NONE ==>
    (agp32 fext fbits (SUC t)).PC = (FUNPOW Next (THE (I (1,SUC t)) - 1) a).PC
Proof
  rw [] >>
  `reg_data_vaild 3 (agp32 fext fbits t)`
    by fs [enable_stg_def,reg_data_vaild_def,agp32_IF_PC_write_enable_and_EX_MEM_flags] >>
  Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state;WB_pipeline;MEM_pipeline;EX_pipeline;
                            REG_write;ID_pipeline] (fext t) s s` >>
  `(agp32 fext fbits (SUC t)).PC = (IF_PC_update (fext t) s s').PC`
    by fs [agp32_PC_updated_by_IF_PC_update,Abbr `s`,Abbr `s'`] >> rw [] >>
  `s.IF.IF_PC_write_enable` by fs [enable_stg_def] >>
  `(s'.IF.IF_PC_write_enable <=> s.IF.IF_PC_write_enable) /\
  (s'.IF.IF_PC_input = s.IF.IF_PC_input)`
    by METIS_TAC [agp32_same_IF_items_until_ID_pipeline,Abbr `s`,Abbr `s'`] >>
  rw [IF_PC_update_def] >>
  `s.EX.EX_jump_sel <=> isJump_isa_op (I' (3,t)) a` by fs [Rel_def,EX_Rel_spec_def] >>
  Cases_on `s.EX.EX_jump_sel` >> fs [Rel_def,is_sch_fetch_def,IF_PC_Rel_def] >-
   METIS_TAC [isJump_isa_op_not_none] >>
  Cases_on `I' (1,t) <> NONE` >> fs [] >-
   (Cases_on `isJump_isa_op (I' (1,t)) a \/ isJump_isa_op (I' (2,t)) a \/ THE (I' (1,t)) = 0` >-
     METIS_TAC [Abbr `s`,enable_stg_def] >>
    `I' (1,SUC t) = SOME (THE (I' (1,t)) + 1)` by METIS_TAC [Abbr `s`,enable_stg_def] >> fs [] >>
    Q.ABBREV_TAC `i = THE (I' (1,t))` >>
    Cases_on `i` >> fs [] >>
    rw [FUNPOW_SUC] >>
    `~isJump_isa (FUNPOW Next (SUC n -1) a)` by METIS_TAC [isJump_isa_op_def] >> fs [] >>
    METIS_TAC [ag32_not_isJump_isa_Next_PC]) >>
  fs [Abbr `s`,enable_stg_def] >> METIS_TAC []
QED

(** PC when IF is disabled **)
Theorem agp32_Rel_ag32_IF_disable_PC_correct:
  !fext fbits a t I.
    is_sch_disable I (agp32 fext fbits) ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    ~enable_stg 1 (agp32 fext fbits t) ==>
    I (1,SUC t) <> NONE ==>
    (agp32 fext fbits (SUC t)).PC = (FUNPOW Next (THE (I (1,SUC t)) - 1) a).PC
Proof
  rw [is_sch_disable_def] >>
  Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state;WB_pipeline;MEM_pipeline;EX_pipeline;
                            REG_write;ID_pipeline] (fext t) s s` >>
  `(agp32 fext fbits (SUC t)).PC = (IF_PC_update (fext t) s s').PC`
    by fs [agp32_PC_updated_by_IF_PC_update,Abbr `s`,Abbr `s'`] >>
  `~s.IF.IF_PC_write_enable` by fs [enable_stg_def] >>
  `~s'.IF.IF_PC_write_enable /\ s'.PC = s.PC`
    by METIS_TAC [agp32_same_IF_items_until_ID_pipeline,Abbr `s`,Abbr `s'`] >>
  fs [IF_PC_update_def,Rel_def,IF_PC_Rel_def]
QED

(** IF_PC_Rel between ISA and circuit states **)
Theorem agp32_Rel_ag32_IF_PC_Rel_correct:
  !fext fbits a t I.
    SC_self_mod_isa a ==>
    is_mem fext_accessor_circuit (agp32 fext fbits) fext ==>
    is_sch_fetch I (agp32 fext fbits) a ==>
    is_sch_disable I (agp32 fext fbits) ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (1,SUC t) <> NONE ==>
    IF_PC_Rel (agp32 fext fbits (SUC t)) a (THE (I (1,SUC t)))
Proof
  rw [IF_PC_Rel_def] >>
  Cases_on `enable_stg 1 (agp32 fext fbits t)` >-
   METIS_TAC [agp32_Rel_ag32_IF_enable_PC_correct] >>
  METIS_TAC [agp32_Rel_ag32_IF_disable_PC_correct]
QED


(** IF_instr **)
(** IF_instr when IF is enabled **)
Theorem agp32_Rel_ag32_IF_enable_instr_correct:
  !fext fbits a t I.
    SC_self_mod_isa a ==>
    is_mem fext_accessor_circuit (agp32 fext fbits) fext ==>
    is_sch I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (1,SUC t) <> NONE ==>
    (fext (SUC t)).ready ==>
    enable_stg 1 (agp32 fext fbits t) ==>
    (agp32 fext fbits (SUC t)).IF.IF_instr = instr (FUNPOW Next (THE (I (1,SUC t)) - 1) a)
Proof
  rw [] >>
  `?s s'. (agp32 fext fbits (SUC t)).IF.IF_instr = (IF_instr_update (fext (SUC t)) s s').IF.IF_instr`
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
    (`(agp32 fext fbits (SUC t)).PC = (FUNPOW Next (THE (I' (1,SUC t)) - 1) a).PC`
       by METIS_TAC [agp32_Rel_ag32_IF_enable_PC_correct,is_sch_def] >>
     Cases_on `I' (4,SUC t) <> NONE`  >> fs [] >-
      (`(fext (SUC t)).mem = (FUNPOW Next (THE (I' (4,SUC t))) a).MEM` by cheat >>
       `THE (I' (1,SUC t)) > THE (I' (4,SUC t)) /\ THE (I' (1,SUC t)) < THE (I' (4,SUC t)) + 4`
         by METIS_TAC [IF_instr_index_big_then_MEM_enable] >> fs [] >>
       METIS_TAC [SC_self_mod_isa_not_affect_fetched_instr]) >>
     Cases_on `I' (3,SUC t) <> NONE`  >> fs [] >-
      (`(fext (SUC t)).mem = (FUNPOW Next ((THE (I' (3,SUC t))) - 1) a).MEM` by cheat >>
       `THE (I' (1,SUC t)) > THE (I' (3,SUC t)) /\ THE (I' (1,SUC t)) < THE (I' (3,SUC t)) + 3`
         by METIS_TAC [IF_instr_index_with_EX_instr] >>
       `THE (I' (1,SUC t)) < THE (I' (3,SUC t)) + 4` by rw [] >> fs [] >>
       METIS_TAC [SC_self_mod_isa_not_affect_fetched_instr_extra]) >>
     Cases_on `I' (2,SUC t) <> NONE`  >> fs [] >-
      (`(fext (SUC t)).mem = (FUNPOW Next ((THE (I' (2,SUC t))) - 1) a).MEM` by cheat >>
       `THE (I' (1,SUC t)) > THE (I' (2,SUC t)) /\ THE (I' (1,SUC t)) < THE (I' (2,SUC t)) + 2`
         by METIS_TAC [IF_instr_index_with_ID_instr] >>
       `THE (I' (1,SUC t)) < THE (I' (2,SUC t)) + 4` by rw [] >> fs [] >>
       METIS_TAC [SC_self_mod_isa_not_affect_fetched_instr_extra]) >>
     `(fext (SUC t)).mem = (FUNPOW Next ((THE (I' (1,SUC t))) - 1) a).MEM` by cheat >> fs []) >>
   (** multiple cycles **)
   `~(fext (0 + SUC t)).ready` by fs [] >> fs []) >-
   ((** 3: write memory and read instr **)
   last_assum (mp_tac o is_mem_data_write `SUC t`) >> rw [] >>
   Cases_on `m` >> fs [] >-
    (`(agp32 fext fbits (SUC t)).PC = (FUNPOW Next (THE (I'(1,SUC t)) - 1) a).PC`
       by METIS_TAC [agp32_Rel_ag32_IF_enable_PC_correct,is_sch_def] >>
     qpat_abbrev_tac `newmem = mem_update _ _ _ _` >>
     Cases_on `I' (4,SUC t) <> NONE`  >> fs [] >-
      (`(fext (SUC t)).mem = (FUNPOW Next (THE (I' (4,SUC t))) a).MEM` by cheat >>
       `newmem = (FUNPOW Next (THE (I' (4,SUC t))) a).MEM` by fs [] >>
       `THE (I' (1,SUC t)) > THE (I' (4,SUC t)) /\ THE (I' (1,SUC t)) < THE (I' (4,SUC t)) + 4`
         by METIS_TAC [IF_instr_index_big_then_MEM_enable] >> fs [] >>
       METIS_TAC [SC_self_mod_isa_not_affect_fetched_instr]) >>
     Cases_on `I' (3,SUC t) <> NONE`  >> fs [] >-
      (`(fext (SUC t)).mem = (FUNPOW Next ((THE (I' (3,SUC t))) - 1) a).MEM` by cheat >>
       `newmem = (FUNPOW Next (THE (I' (3,SUC t)) - 1) a).MEM` by fs [] >>
       `THE (I' (1,SUC t)) > THE (I' (3,SUC t)) /\ THE (I' (1,SUC t)) < THE (I' (3,SUC t)) + 3`
         by METIS_TAC [IF_instr_index_with_EX_instr] >>
       `THE (I' (1,SUC t)) < THE (I' (3,SUC t)) + 4` by rw [] >> fs [] >>
       METIS_TAC [SC_self_mod_isa_not_affect_fetched_instr_extra]) >>
     Cases_on `I' (2,SUC t) <> NONE`  >> fs [] >-
      (`(fext (SUC t)).mem = (FUNPOW Next ((THE (I' (2,SUC t))) - 1) a).MEM` by cheat >>
       `newmem = (FUNPOW Next (THE (I' (2,SUC t)) - 1) a).MEM` by fs [] >>
       `THE (I' (1,SUC t)) > THE (I' (2,SUC t)) /\ THE (I' (1,SUC t)) < THE (I' (2,SUC t)) + 2`
         by METIS_TAC [IF_instr_index_with_ID_instr] >>
       `THE (I' (1,SUC t)) < THE (I' (2,SUC t)) + 4` by rw [] >> fs [] >>
       METIS_TAC [SC_self_mod_isa_not_affect_fetched_instr_extra]) >>
     `(fext (SUC t)).mem = (FUNPOW Next ((THE (I' (1,SUC t))) - 1) a).MEM` by cheat >>
     `newmem = (FUNPOW Next (THE (I' (1,SUC t)) - 1) a).MEM` by fs [] >> fs []) >>
   `~(fext (0 + SUC t)).ready` by fs [] >> fs []) >-
   ((** 2: read memory and read instr **)
   last_assum (mp_tac o is_mem_data_read `SUC t`) >> rw [] >>
   Cases_on `m` >> fs [] >-
    (`(agp32 fext fbits (SUC t)).PC = (FUNPOW Next (THE (I'(1,SUC t)) - 1) a).PC`
       by METIS_TAC [agp32_Rel_ag32_IF_enable_PC_correct,is_sch_def] >>
     Cases_on `I' (4,SUC t) <> NONE`  >> fs [] >-
      (`(fext (SUC t)).mem = (FUNPOW Next (THE (I' (4,SUC t))) a).MEM` by cheat >>
       `THE (I' (1,SUC t)) > THE (I' (4,SUC t)) /\ THE (I' (1,SUC t)) < THE (I' (4,SUC t)) + 4`
         by METIS_TAC [IF_instr_index_big_then_MEM_enable] >> fs [] >>
       METIS_TAC [SC_self_mod_isa_not_affect_fetched_instr]) >>
     Cases_on `I' (3,SUC t) <> NONE`  >> fs [] >-
      (`(fext (SUC t)).mem = (FUNPOW Next ((THE (I' (3,SUC t))) - 1) a).MEM` by cheat >>
       `THE (I' (1,SUC t)) > THE (I' (3,SUC t)) /\ THE (I' (1,SUC t)) < THE (I' (3,SUC t)) + 3`
         by METIS_TAC [IF_instr_index_with_EX_instr] >>
       `THE (I' (1,SUC t)) < THE (I' (3,SUC t)) + 4` by rw [] >> fs [] >>
       METIS_TAC [SC_self_mod_isa_not_affect_fetched_instr_extra]) >>
     Cases_on `I' (2,SUC t) <> NONE`  >> fs [] >-
      (`(fext (SUC t)).mem = (FUNPOW Next ((THE (I' (2,SUC t))) - 1) a).MEM` by cheat >>
       `THE (I' (1,SUC t)) > THE (I' (2,SUC t)) /\ THE (I' (1,SUC t)) < THE (I' (2,SUC t)) + 2`
         by METIS_TAC [IF_instr_index_with_ID_instr] >>
       `THE (I' (1,SUC t)) < THE (I' (2,SUC t)) + 4` by rw [] >> fs [] >>
       METIS_TAC [SC_self_mod_isa_not_affect_fetched_instr_extra]) >>
     `(fext (SUC t)).mem = (FUNPOW Next ((THE (I' (1,SUC t))) - 1) a).MEM` by cheat >> fs []) >>
   `~(fext (0 + SUC t)).ready` by fs [] >> fs []) >-
   ((** 1: read instr **)
   last_assum (mp_tac o is_mem_inst_read `SUC t`) >> rw [] >>
   Cases_on `m` >> fs [] >-
    (`(agp32 fext fbits (SUC t)).PC = (FUNPOW Next (THE (I'(1,SUC t)) - 1) a).PC`
       by METIS_TAC [agp32_Rel_ag32_IF_enable_PC_correct,is_sch_def] >>
     Cases_on `I' (4,SUC t) <> NONE`  >> fs [] >-
     (`(fext (SUC t)).mem = (FUNPOW Next (THE (I' (4,SUC t))) a).MEM` by cheat >>
      `THE (I' (1,SUC t)) > THE (I' (4,SUC t)) /\ THE (I' (1,SUC t)) < THE (I' (4,SUC t)) + 4`
        by METIS_TAC [IF_instr_index_big_then_MEM_enable] >> fs [] >>
      METIS_TAC [SC_self_mod_isa_not_affect_fetched_instr]) >>
     Cases_on `I' (3,SUC t) <> NONE`  >> fs [] >-
      (`(fext (SUC t)).mem = (FUNPOW Next ((THE (I' (3,SUC t))) - 1) a).MEM` by cheat >>
       `THE (I' (1,SUC t)) > THE (I' (3,SUC t)) /\ THE (I' (1,SUC t)) < THE (I' (3,SUC t)) + 3`
         by METIS_TAC [IF_instr_index_with_EX_instr] >>
       `THE (I' (1,SUC t)) < THE (I' (3,SUC t)) + 4` by rw [] >> fs [] >>
       METIS_TAC [SC_self_mod_isa_not_affect_fetched_instr_extra]) >>
     Cases_on `I' (2,SUC t) <> NONE`  >> fs [] >-
      (`(fext (SUC t)).mem = (FUNPOW Next ((THE (I' (2,SUC t))) - 1) a).MEM` by cheat >>
       `THE (I' (1,SUC t)) > THE (I' (2,SUC t)) /\ THE (I' (1,SUC t)) < THE (I' (2,SUC t)) + 2`
         by METIS_TAC [IF_instr_index_with_ID_instr] >>
       `THE (I' (1,SUC t)) < THE (I' (2,SUC t)) + 4` by rw [] >> fs [] >>
       METIS_TAC [SC_self_mod_isa_not_affect_fetched_instr_extra]) >>
     `(fext (SUC t)).mem = (FUNPOW Next ((THE (I' (1,SUC t))) - 1) a).MEM` by cheat >> fs []) >>
   `~(fext (0 + SUC t)).ready` by fs [] >> fs []) >>
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

(** IF_instr updated when IF is disabled **)
(** lemma **)
Theorem FINITE_max_ready_cycle[local]:
  !t fext.
    FINITE {t0 | t0 < t /\ (fext t0).ready}
Proof
  rw [] >>
  `{t0 | t0 < t /\ (fext t0).ready} SUBSET (count t)` by rw [count_def,SUBSET_DEF] >>
  `FINITE (count t)` by fs [FINITE_COUNT] >>
  METIS_TAC [SUBSET_FINITE_I]
QED

Theorem same_t_and_m_under_MAX_SET_0[local]:
  !fext t m.
    MAX_SET {t0 | t0 < t /\ (fext t0).ready} = 0 ==>
    (!p. p < m ==> ~(fext (p + 1)).ready) ==>
    (fext (m + 1)).ready ==>
    ~(fext t).ready ==>
    (fext (t + 1)).ready ==>
    m = t
Proof
  rw [] >> Cases_on `m = t` >> rw [] >>
  Cases_on `t < m` >-
   METIS_TAC [] >>
  `t > m` by fs [] >> fs [] >>
  Cases_on `t = m + 1` >> fs [] >>
  `t > m + 1` by fs [] >>
  `{t0 | t0 < t /\ (fext t0).ready} (m + 1)` by fs [] >>
  Cases_on `{t0 | t0 < t /\ (fext t0).ready} = {}` >-
   METIS_TAC [EMPTY_applied] >>
  `FINITE {t0 | t0 < t /\ (fext t0).ready}` by rw [FINITE_max_ready_cycle] >>
  `(m + 1) IN {t0 | t0 < t /\ (fext t0).ready}` by fs [] >>
  `m + 1 <= 0` by METIS_TAC [MAX_SET_DEF] >> rw []
QED

Theorem same_t_and_m_under_MAX_SET_SUC[local]:
  !fext t m n.
    MAX_SET {t0 | t0 < t /\ (fext t0).ready} = n ==>
    (!p. p < m ==> ~(fext (p + (SUC n))).ready) ==>
    (fext (m + SUC n)).ready ==>
    ~(fext t).ready ==>
    (fext (SUC t)).ready ==>
    n <> 0 ==>
    m + SUC n = SUC t
Proof
  rpt strip_tac >>
  `FINITE {t0 | t0 < t /\ (fext t0).ready}` by fs [FINITE_max_ready_cycle] >>
  Cases_on `{t0 | t0 < t /\ (fext t0).ready} = {}` >> fs [MAX_SET_DEF] >>
  `n IN {t0 | t0 < t /\ (fext t0).ready}` by METIS_TAC [MAX_SET_DEF] >>
  fs [MAX_SET_DEF] >>
  Cases_on `m + SUC n = SUC t` >> fs [] >>
  Cases_on `SUC t < m + SUC n` >-
   (`SUC t -SUC n < m` by rw [] >>
    `~(fext (SUC t -SUC n + SUC n)).ready` by fs [] >>
    `SUC t -SUC n + SUC n = SUC t` by rw [] >> fs []) >>
  `SUC t > m + SUC n` by fs [] >> fs [] >>
  Cases_on `t = m + SUC n` >> fs [] >>
  `t > m + SUC n` by fs [] >>
  `(m + SUC n) IN {t0 | t0 < t /\ (fext t0).ready}` by fs [] >>
  `(m + SUC n) <= n` by METIS_TAC [MAX_SET_DEF] >> fs []
QED

Theorem PC_unchanged_after_disabled_cycles[local]:
  !fext fbits m n.
    (!p. p < m ==> ~(fext (p + n)).ready) ==>
    (agp32 fext fbits (m + n)).PC = (agp32 fext fbits n).PC
Proof
  rw [] >> Induct_on `m` >> rw [] >>
  `!p. p < m ==> ~(fext (n + p)).ready` by fs [] >> fs [] >>
  `m < SUC m` by rw [] >>
  `~(fext (n + m)).ready` by fs [] >>
  `~(agp32 fext fbits (n + m)).IF.IF_PC_write_enable`
    by fs [not_fext_ready_and_agp32_IF_PC_write_disable] >>
  subgoal `(agp32 fext fbits (SUC (n + m))).PC = (agp32 fext fbits (n + m)).PC` >-
   (Q.ABBREV_TAC `t = n + m` >>
    Q.ABBREV_TAC `s1 = agp32 fext fbits t` >>
    Q.ABBREV_TAC `s2 = procs [agp32_next_state;WB_pipeline;MEM_pipeline;EX_pipeline;
                              REG_write;ID_pipeline] (fext t) s1 s1` >>
    `(agp32 fext fbits (SUC t)).PC = (IF_PC_update (fext t) s1 s2).PC`
      by fs [agp32_PC_updated_by_IF_PC_update,Abbr `s1`,Abbr `s2`] >>
    `~s2.IF.IF_PC_write_enable /\ s2.PC = s1.PC`
      by METIS_TAC [agp32_same_IF_items_until_ID_pipeline,Abbr `s1`,Abbr `s2`] >>
    fs [IF_PC_update_def]) >>
  `n + SUC m = SUC (n + m)` by rw [] >> rw [] >> fs []
QED

(** not ready at the previous cycle **)
Theorem agp32_Rel_ag32_IF_disable_instr_not_ready_before_correct:
  !fext fbits a t I.
    SC_self_mod_isa a ==>
    is_mem fext_accessor_circuit (agp32 fext fbits) fext ==>
    is_sch I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (1,SUC t) <> NONE ==>
    (fext (SUC t)).ready ==>
    ~(fext t).ready ==>
    ~enable_stg 1 (agp32 fext fbits t) ==>
    (fext (SUC t)).inst_rdata = instr (FUNPOW Next (THE (I (1,SUC t)) - 1) a)
Proof
  rw [] >> Cases_on `MAX_SET {t0 | t0 < t /\ (fext t0).ready}` >-
   ((** start fetching in the beginning **)
    last_assum (assume_tac o is_mem_def_mem_no_errors) >>
    Cases_on_word_value `(agp32 fext fbits (SUC 0)).command` >>
    fs [agp32_command_impossible_values] >-
     ((** command is 4 **)
     rw [instr_def] >>
     last_assum (mp_tac o is_mem_data_flush `SUC 0`) >> rw [] >>
     `SUC t = t + 1` by rw [] >>
     `m = t` by METIS_TAC [same_t_and_m_under_MAX_SET_0] >> rw [] >>
     `(fext 1).mem = (fext (m + 1)).mem`
       by (Cases_on `m` >> fs [] >> `0 < SUC n` by rw [] >>
           `(fext (0+1)).mem = (fext 0).mem` by fs [] >> fs []) >>
     `(agp32 fext fbits 1).PC = (agp32 fext fbits (m + 1)).PC`
       by METIS_TAC [PC_unchanged_after_disabled_cycles] >>
     `(agp32 fext fbits 1).PC = (agp32 fext fbits (SUC m)).PC` by rw [] >>
     `(agp32 fext fbits (SUC m)).PC = (FUNPOW Next (THE (I'(1,SUC m)) - 1) a).PC`
       by METIS_TAC [agp32_Rel_ag32_IF_disable_PC_correct,is_sch_def] >>
     `(fext (SUC m)).mem = (fext (m + 1)).mem` by rw [] >>
     `I' (1,m + 1) = I' (1,SUC m)` by rw [] >>
     Cases_on `I' (4,SUC m) <> NONE`  >> fs [] >-
      (`(fext (SUC m)).mem = (FUNPOW Next (THE (I' (4,SUC m))) a).MEM` by cheat >>
       `(fext 0).mem = (FUNPOW Next (THE (I' (4,SUC m))) a).MEM` by fs [] >>
       `THE (I' (1,SUC m)) > THE (I' (4,SUC m)) /\ THE (I' (1,SUC m)) < THE (I' (4,SUC m)) + 4`
         by METIS_TAC [IF_instr_index_big_then_MEM_disable] >> fs [] >>
       METIS_TAC [SC_self_mod_isa_not_affect_fetched_instr]) >>
     Cases_on `I' (3,SUC m) <> NONE`  >> fs [] >-
      (`(fext (SUC m)).mem = (FUNPOW Next ((THE (I' (3,SUC m))) - 1) a).MEM` by cheat >>
       `(fext 0).mem = (FUNPOW Next ((THE (I' (3,SUC m))) - 1) a).MEM` by fs [] >>
       `THE (I' (1,SUC m)) > THE (I' (3,SUC m)) /\ THE (I' (1,SUC m)) < THE (I' (3,SUC m)) + 3`
         by METIS_TAC [IF_instr_index_with_EX_instr] >>
       `THE (I' (1,SUC m)) < THE (I' (3,SUC m)) + 4` by fs [] >> fs [] >>
       METIS_TAC [SC_self_mod_isa_not_affect_fetched_instr_extra]) >>
     Cases_on `I' (2,SUC m) <> NONE`  >> fs [] >-
      (`(fext (SUC m)).mem = (FUNPOW Next ((THE (I' (2,SUC m))) - 1) a).MEM` by cheat >>
       `(fext 0).mem = (FUNPOW Next ((THE (I' (2,SUC m))) - 1) a).MEM` by fs [] >>
       `THE (I' (1,SUC m)) > THE (I' (2,SUC m)) /\ THE (I' (1,SUC m)) < THE (I' (2,SUC m)) + 2`
         by METIS_TAC [IF_instr_index_with_ID_instr] >>
       `THE (I' (1,SUC m)) < THE (I' (2,SUC m)) + 4` by fs [] >> fs [] >>
       METIS_TAC [SC_self_mod_isa_not_affect_fetched_instr_extra]) >>
     `(fext (SUC m)).mem = (FUNPOW Next ((THE (I' (1,SUC m))) - 1) a).MEM` by cheat >>
     `(fext 0).mem = (FUNPOW Next ((THE (I' (1,SUC m))) - 1) a).MEM` by fs [] >> fs []) >-
     ((** command is 3 **)
     rw [instr_def] >>
     last_assum (mp_tac o is_mem_data_write `SUC 0`) >> rw [] >>
     `SUC t = t + 1` by rw [] >>
     `m = t` by METIS_TAC [same_t_and_m_under_MAX_SET_0] >> rw [] >>
     qpat_abbrev_tac `newmem = mem_update _ _ _ _` >>  
     `(agp32 fext fbits 1).PC = (agp32 fext fbits (m + 1)).PC`
       by METIS_TAC [PC_unchanged_after_disabled_cycles] >>
     `(agp32 fext fbits 1).PC = (agp32 fext fbits (SUC m)).PC` by rw [] >>
     `(agp32 fext fbits (SUC m)).PC = (FUNPOW Next (THE (I'(1,SUC m)) - 1) a).PC`
       by METIS_TAC [agp32_Rel_ag32_IF_disable_PC_correct,is_sch_def] >>
     `(fext (SUC m)).mem = (fext (m + 1)).mem` by rw [] >>
     `I' (1,m + 1) = I' (1,SUC m)` by rw [] >>
     Cases_on `I' (4,SUC m) <> NONE`  >> fs [] >-
      (`(fext (SUC m)).mem = (FUNPOW Next (THE (I' (4,SUC m))) a).MEM` by cheat >>
       `newmem = (FUNPOW Next (THE (I' (4,SUC m))) a).MEM` by fs [] >>
       `THE (I' (1,SUC m)) > THE (I' (4,SUC m)) /\ THE (I' (1,SUC m)) < THE (I' (4,SUC m)) + 4`
         by METIS_TAC [IF_instr_index_big_then_MEM_disable] >> fs [] >>
       METIS_TAC [SC_self_mod_isa_not_affect_fetched_instr]) >>
     Cases_on `I' (3,SUC m) <> NONE`  >> fs [] >-
      (`(fext (SUC m)).mem = (FUNPOW Next ((THE (I' (3,SUC m))) - 1) a).MEM` by cheat >>
       `newmem = (FUNPOW Next (THE (I' (3,SUC m)) - 1) a).MEM` by fs [] >>
       `THE (I' (1,SUC m)) > THE (I' (3,SUC m)) /\ THE (I' (1,SUC m)) < THE (I' (3,SUC m)) + 3`
         by METIS_TAC [IF_instr_index_with_EX_instr] >>
       `THE (I' (1,SUC m)) < THE (I' (3,SUC m)) + 4` by rw [] >> fs [] >>
       METIS_TAC [SC_self_mod_isa_not_affect_fetched_instr_extra]) >>
      Cases_on `I' (2,SUC m) <> NONE`  >> fs [] >-
      (`(fext (SUC m)).mem = (FUNPOW Next ((THE (I' (2,SUC m))) - 1) a).MEM` by cheat >>
       `newmem = (FUNPOW Next (THE (I' (2,SUC m)) - 1) a).MEM` by fs [] >>
       `THE (I' (1,SUC m)) > THE (I' (2,SUC m)) /\ THE (I' (1,SUC m)) < THE (I' (2,SUC m)) + 2`
         by METIS_TAC [IF_instr_index_with_ID_instr] >>
       `THE (I' (1,SUC m)) < THE (I' (2,SUC m)) + 4` by rw [] >> fs [] >>
       METIS_TAC [SC_self_mod_isa_not_affect_fetched_instr_extra]) >>
     `(fext (SUC m)).mem = (FUNPOW Next ((THE (I' (1,SUC m))) - 1) a).MEM` by cheat >>
     `newmem = (FUNPOW Next (THE (I' (1,SUC m)) - 1) a).MEM` by fs [] >> fs []) >-
     ((** command is 2 **)
     rw [instr_def] >>
     last_assum (mp_tac o is_mem_data_read `SUC 0`) >> rw [] >>
     `SUC t = t + 1` by rw [] >>
     `m = t` by METIS_TAC [same_t_and_m_under_MAX_SET_0] >> rw [] >>
     `(fext 1).mem = (fext (m + 1)).mem`
       by (Cases_on `m` >> fs [] >> `0 < SUC n` by rw [] >>
           `(fext (0+1)).mem = (fext 0).mem` by fs [] >> fs []) >>
     `(agp32 fext fbits 1).PC = (agp32 fext fbits (m + 1)).PC`
       by METIS_TAC [PC_unchanged_after_disabled_cycles] >>
     `(agp32 fext fbits 1).PC = (agp32 fext fbits (SUC m)).PC` by rw [] >>
     `(agp32 fext fbits (SUC m)).PC = (FUNPOW Next (THE (I'(1,SUC m)) - 1) a).PC`
       by METIS_TAC [agp32_Rel_ag32_IF_disable_PC_correct,is_sch_def] >>
     `(fext (SUC m)).mem = (fext (m + 1)).mem` by rw [] >>
     `I' (1,m + 1) = I' (1,SUC m)` by rw [] >>
     Cases_on `I' (4,SUC m) <> NONE`  >> fs [] >-
      (`(fext (SUC m)).mem = (FUNPOW Next (THE (I' (4,SUC m))) a).MEM` by cheat >>
       `(fext 0).mem = (FUNPOW Next (THE (I' (4,SUC m))) a).MEM` by fs [] >>
       `THE (I' (1,SUC m)) > THE (I' (4,SUC m)) /\ THE (I' (1,SUC m)) < THE (I' (4,SUC m)) + 4`
         by METIS_TAC [IF_instr_index_big_then_MEM_disable] >> fs [] >>
       METIS_TAC [SC_self_mod_isa_not_affect_fetched_instr]) >>
     Cases_on `I' (3,SUC m) <> NONE`  >> fs [] >-
      (`(fext (SUC m)).mem = (FUNPOW Next ((THE (I' (3,SUC m))) - 1) a).MEM` by cheat >>
       `(fext 0).mem = (FUNPOW Next ((THE (I' (3,SUC m))) - 1) a).MEM` by fs [] >>
       `THE (I' (1,SUC m)) > THE (I' (3,SUC m)) /\ THE (I' (1,SUC m)) < THE (I' (3,SUC m)) + 3`
         by METIS_TAC [IF_instr_index_with_EX_instr] >>
       `THE (I' (1,SUC m)) < THE (I' (3,SUC m)) + 4` by fs [] >> fs [] >>
       METIS_TAC [SC_self_mod_isa_not_affect_fetched_instr_extra]) >>
     Cases_on `I' (2,SUC m) <> NONE`  >> fs [] >-
      (`(fext (SUC m)).mem = (FUNPOW Next ((THE (I' (2,SUC m))) - 1) a).MEM` by cheat >>
       `(fext 0).mem = (FUNPOW Next ((THE (I' (2,SUC m))) - 1) a).MEM` by fs [] >>
       `THE (I' (1,SUC m)) > THE (I' (2,SUC m)) /\ THE (I' (1,SUC m)) < THE (I' (2,SUC m)) + 2`
         by METIS_TAC [IF_instr_index_with_ID_instr] >>
       `THE (I' (1,SUC m)) < THE (I' (2,SUC m)) + 4` by fs [] >> fs [] >>
       METIS_TAC [SC_self_mod_isa_not_affect_fetched_instr_extra]) >>
     `(fext (SUC m)).mem = (FUNPOW Next ((THE (I' (1,SUC m))) - 1) a).MEM` by cheat >>
     `(fext 0).mem = (FUNPOW Next ((THE (I' (1,SUC m))) - 1) a).MEM` by fs [] >> fs []) >-
     ((** command is 1 **)
     rw [instr_def] >>
     last_assum (mp_tac o is_mem_inst_read `SUC 0`) >> rw [] >>
     `SUC t = t + 1` by rw [] >>
     `m = t` by METIS_TAC [same_t_and_m_under_MAX_SET_0] >> rw [] >>
     `(fext 1).mem = (fext (m + 1)).mem`
       by (Cases_on `m` >> fs [] >> `0 < SUC n` by rw [] >>
           `(fext (0+1)).mem = (fext 0).mem` by fs [] >> fs []) >>
     `(agp32 fext fbits 1).PC = (agp32 fext fbits (m + 1)).PC`
       by METIS_TAC [PC_unchanged_after_disabled_cycles] >>
     `(agp32 fext fbits 1).PC = (agp32 fext fbits (SUC m)).PC` by rw [] >>
     `(agp32 fext fbits (SUC m)).PC = (FUNPOW Next (THE (I'(1,SUC m)) - 1) a).PC`
       by METIS_TAC [agp32_Rel_ag32_IF_disable_PC_correct,is_sch_def] >>
     `(fext (SUC m)).mem = (fext (m + 1)).mem` by rw [] >>
     `I' (1,m + 1) = I' (1,SUC m)` by rw [] >>
     Cases_on `I' (4,SUC m) <> NONE`  >> fs [] >-
      (`(fext (SUC m)).mem = (FUNPOW Next (THE (I' (4,SUC m))) a).MEM` by cheat >>
       `(fext 0).mem = (FUNPOW Next (THE (I' (4,SUC m))) a).MEM` by fs [] >>
       `THE (I' (1,SUC m)) > THE (I' (4,SUC m)) /\ THE (I' (1,SUC m)) < THE (I' (4,SUC m)) + 4`
         by METIS_TAC [IF_instr_index_big_then_MEM_disable] >> fs [] >>
       METIS_TAC [SC_self_mod_isa_not_affect_fetched_instr]) >>
     Cases_on `I' (3,SUC m) <> NONE`  >> fs [] >-
      (`(fext (SUC m)).mem = (FUNPOW Next ((THE (I' (3,SUC m))) - 1) a).MEM` by cheat >>
       `(fext 0).mem = (FUNPOW Next ((THE (I' (3,SUC m))) - 1) a).MEM` by fs [] >>
       `THE (I' (1,SUC m)) > THE (I' (3,SUC m)) /\ THE (I' (1,SUC m)) < THE (I' (3,SUC m)) + 3`
         by METIS_TAC [IF_instr_index_with_EX_instr] >>
       `THE (I' (1,SUC m)) < THE (I' (3,SUC m)) + 4` by fs [] >> fs [] >>
       METIS_TAC [SC_self_mod_isa_not_affect_fetched_instr_extra]) >>
     Cases_on `I' (2,SUC m) <> NONE`  >> fs [] >-
      (`(fext (SUC m)).mem = (FUNPOW Next ((THE (I' (2,SUC m))) - 1) a).MEM` by cheat >>
       `(fext 0).mem = (FUNPOW Next ((THE (I' (2,SUC m))) - 1) a).MEM` by fs [] >>
       `THE (I' (1,SUC m)) > THE (I' (2,SUC m)) /\ THE (I' (1,SUC m)) < THE (I' (2,SUC m)) + 2`
         by METIS_TAC [IF_instr_index_with_ID_instr] >>
       `THE (I' (1,SUC m)) < THE (I' (2,SUC m)) + 4` by fs [] >> fs [] >>
       METIS_TAC [SC_self_mod_isa_not_affect_fetched_instr_extra]) >>
     `(fext (SUC m)).mem = (FUNPOW Next ((THE (I' (1,SUC m))) - 1) a).MEM` by cheat >>
     `(fext 0).mem = (FUNPOW Next ((THE (I' (1,SUC m))) - 1) a).MEM` by fs [] >> fs []) >>
    (** command is 0 **)
    last_assum (mp_tac o is_mem_do_nothing `SUC 0`) >> rw [] >>
    `!p. p < 0 ==> ~(fext (p + 1)).ready` by rw [] >>
    `SUC t = t + 1` by rw [] >>
    `(fext (0 + 1)).ready` by rw [] >>
    `0 = t` by METIS_TAC [same_t_and_m_under_MAX_SET_0] >> fs [] >>
    (*`(fext 0).ready` by cheat >> fs [] *)
    `I' (1,SUC 0) = I' (1,0)` by fs [is_sch_def,is_sch_disable_def] >>
    `I' (1,1) = I' (1,0)` by fs [] >> rw [] >>
    fs [is_sch_def,is_sch_init_def] >> cheat) >>

  (** not fetching in the beginning **)
  Q.ABBREV_TAC `i = SUC n` >> `i <> 0` by fs [Abbr `i`] >>
  `FINITE {t0 | t0 < t /\ (fext t0).ready}` by fs [FINITE_max_ready_cycle] >>
  Cases_on `{t0 | t0 < t /\ (fext t0).ready} = {}` >> fs [MAX_SET_DEF] >>
  `i IN {t0 | t0 < t /\ (fext t0).ready}` by METIS_TAC [MAX_SET_DEF] >> fs [MAX_SET_DEF] >>
  last_assum (assume_tac o is_mem_def_mem_no_errors) >>
  Cases_on_word_value `(agp32 fext fbits (SUC i)).command` >>
  fs [agp32_command_impossible_values] >-
   ((** command is 4 **)
   fs [instr_def] >>
   last_assum (mp_tac o is_mem_data_flush `SUC i`) >> simp [] >> strip_tac >>
   `m + SUC i = SUC t` by METIS_TAC [same_t_and_m_under_MAX_SET_SUC] >> simp [] >>
   `(fext (SUC i)).mem = (fext i).mem`
     by (Cases_on `m` >> fs [] >> `0 < SUC n` by rw [] >>
         `(fext (0 + SUC i)).mem = (fext i).mem` by fs [] >> fs []) >>
   `(fext (SUC i)).mem = (fext (SUC t)).mem` by fs [] >>
   `(agp32 fext fbits (SUC i)).PC = (agp32 fext fbits (m + SUC i)).PC`
     by METIS_TAC [PC_unchanged_after_disabled_cycles] >>
   `(agp32 fext fbits (SUC i)).PC = (FUNPOW Next (THE (I'(1,SUC t)) - 1) a).PC`
     by METIS_TAC [agp32_Rel_ag32_IF_disable_PC_correct,is_sch_def] >>
   Cases_on `I' (4,SUC t) <> NONE` >> fs [] >-
    (`(fext (SUC t)).mem = (FUNPOW Next (THE (I' (4,SUC t))) a).MEM` by cheat >>
     `(fext i).mem = (FUNPOW Next (THE (I' (4,SUC t))) a).MEM` by fs [] >>
     `THE (I' (1,SUC t)) > THE (I' (4,SUC t)) /\ THE (I' (1,SUC t)) < THE (I' (4,SUC t)) + 4`
       by METIS_TAC [IF_instr_index_big_then_MEM_disable] >>
     METIS_TAC [SC_self_mod_isa_not_affect_fetched_instr]) >>
   Cases_on `I' (3,SUC t) <> NONE` >> fs [] >-
    (`(fext (SUC t)).mem = (FUNPOW Next ((THE (I' (3,SUC t))) - 1) a).MEM` by cheat >>
     `(fext i).mem = (FUNPOW Next ((THE (I' (3,SUC t))) - 1) a).MEM` by fs [] >>
     `THE (I' (1,SUC t)) > THE (I' (3,SUC t)) /\ THE (I' (1,SUC t)) < THE (I' (3,SUC t)) + 3`
       by METIS_TAC [IF_instr_index_with_EX_instr] >>
     `THE (I' (1,SUC t)) < THE (I' (3,SUC t)) + 4` by fs [] >> fs [] >>
     METIS_TAC [SC_self_mod_isa_not_affect_fetched_instr_extra]) >>
   Cases_on `I' (2,SUC t) <> NONE`  >> fs [] >-
    (`(fext (SUC t)).mem = (FUNPOW Next ((THE (I' (2,SUC t))) - 1) a).MEM` by cheat >>
     `(fext i).mem = (FUNPOW Next ((THE (I' (2,SUC t))) - 1) a).MEM` by fs [] >>
     `THE (I' (1,SUC t)) > THE (I' (2,SUC t)) /\ THE (I' (1,SUC t)) < THE (I' (2,SUC t)) + 2`
       by METIS_TAC [IF_instr_index_with_ID_instr] >>
     `THE (I' (1,SUC t)) < THE (I' (2,SUC t)) + 4` by fs [] >> fs [] >>
     METIS_TAC [SC_self_mod_isa_not_affect_fetched_instr_extra]) >>
   `(fext (SUC t)).mem = (FUNPOW Next ((THE (I' (1,SUC t))) - 1) a).MEM` by cheat >>
   `(fext i).mem = (FUNPOW Next ((THE (I' (1,SUC t))) - 1) a).MEM` by fs [] >> fs []) >-
   ((** command is 3 **)
    fs [instr_def] >>
    last_assum (mp_tac o is_mem_data_write `SUC i`) >> simp [] >> strip_tac >>
    `m + SUC i = SUC t` by METIS_TAC [same_t_and_m_under_MAX_SET_SUC] >> fs [] >>
    qpat_abbrev_tac `newmem = mem_update _ _ _ _` >>
    `(agp32 fext fbits (SUC i)).PC = (agp32 fext fbits (m + SUC i)).PC`
      by METIS_TAC [PC_unchanged_after_disabled_cycles] >>
    `(agp32 fext fbits (SUC i)).PC = (FUNPOW Next (THE (I'(1,SUC t)) - 1) a).PC`
      by METIS_TAC [agp32_Rel_ag32_IF_disable_PC_correct,is_sch_def] >>
    Cases_on `I' (4,SUC t) <> NONE`  >> fs [] >-
      (`(fext (SUC t)).mem = (FUNPOW Next (THE (I' (4,SUC t))) a).MEM` by cheat >>
       `newmem = (FUNPOW Next (THE (I' (4,SUC t))) a).MEM` by fs [] >>
       `THE (I' (1,SUC t)) > THE (I' (4,SUC t)) /\ THE (I' (1,SUC t)) < THE (I' (4,SUC t)) + 4`
         by METIS_TAC [IF_instr_index_big_then_MEM_disable] >> fs [] >>
       METIS_TAC [SC_self_mod_isa_not_affect_fetched_instr]) >>
    Cases_on `I' (3,SUC t) <> NONE`  >> fs [] >-
     (`(fext (SUC t)).mem = (FUNPOW Next ((THE (I' (3,SUC t))) - 1) a).MEM` by cheat >>
      `newmem = (FUNPOW Next (THE (I' (3,SUC t)) - 1) a).MEM` by fs [] >>
      `THE (I' (1,SUC t)) > THE (I' (3,SUC t)) /\ THE (I' (1,SUC t)) < THE (I' (3,SUC t)) + 3`
        by METIS_TAC [IF_instr_index_with_EX_instr] >>
      `THE (I' (1,SUC t)) < THE (I' (3,SUC t)) + 4` by rw [] >> fs [] >>
      METIS_TAC [SC_self_mod_isa_not_affect_fetched_instr_extra]) >>
    Cases_on `I' (2,SUC t) <> NONE`  >> fs [] >-
     (`(fext (SUC t)).mem = (FUNPOW Next ((THE (I' (2,SUC t))) - 1) a).MEM` by cheat >>
      `newmem = (FUNPOW Next (THE (I' (2,SUC t)) - 1) a).MEM` by fs [] >>
      `THE (I' (1,SUC t)) > THE (I' (2,SUC t)) /\ THE (I' (1,SUC t)) < THE (I' (2,SUC t)) + 2`
        by METIS_TAC [IF_instr_index_with_ID_instr] >>
      `THE (I' (1,SUC t)) < THE (I' (2,SUC t)) + 4` by rw [] >> fs [] >>
      METIS_TAC [SC_self_mod_isa_not_affect_fetched_instr_extra]) >>
    `(fext (SUC t)).mem = (FUNPOW Next ((THE (I' (1,SUC t))) - 1) a).MEM` by cheat >>
    `newmem = (FUNPOW Next (THE (I' (1,SUC t)) - 1) a).MEM` by fs [] >> fs []) >-
   ((** command is 2 **)
   fs [instr_def] >>
   last_assum (mp_tac o is_mem_data_read `SUC i`) >> simp [] >> strip_tac >>
   `m + SUC i = SUC t` by METIS_TAC [same_t_and_m_under_MAX_SET_SUC] >> simp [] >>
   `(fext (SUC i)).mem = (fext i).mem`
     by (Cases_on `m` >> fs [] >> `0 < SUC n` by rw [] >>
         `(fext (0 + SUC i)).mem = (fext i).mem` by fs [] >> fs []) >>
   `(fext (SUC i)).mem = (fext (SUC t)).mem` by fs [] >>
   `(agp32 fext fbits (SUC i)).PC = (agp32 fext fbits (m + SUC i)).PC`
     by METIS_TAC [PC_unchanged_after_disabled_cycles] >>
   `(agp32 fext fbits (SUC i)).PC = (FUNPOW Next (THE (I'(1,SUC t)) - 1) a).PC`
     by METIS_TAC [agp32_Rel_ag32_IF_disable_PC_correct,is_sch_def] >>
   Cases_on `I' (4,SUC t) <> NONE` >> fs [] >-
    (`(fext (SUC t)).mem = (FUNPOW Next (THE (I' (4,SUC t))) a).MEM` by cheat >>
     `(fext i).mem = (FUNPOW Next (THE (I' (4,SUC t))) a).MEM` by fs [] >>
     `THE (I' (1,SUC t)) > THE (I' (4,SUC t)) /\ THE (I' (1,SUC t)) < THE (I' (4,SUC t)) + 4`
       by METIS_TAC [IF_instr_index_big_then_MEM_disable] >>
     METIS_TAC [SC_self_mod_isa_not_affect_fetched_instr]) >>
   Cases_on `I' (3,SUC t) <> NONE` >> fs [] >-
    (`(fext (SUC t)).mem = (FUNPOW Next ((THE (I' (3,SUC t))) - 1) a).MEM` by cheat >>
     `(fext i).mem = (FUNPOW Next ((THE (I' (3,SUC t))) - 1) a).MEM` by fs [] >>
     `THE (I' (1,SUC t)) > THE (I' (3,SUC t)) /\ THE (I' (1,SUC t)) < THE (I' (3,SUC t)) + 3`
       by METIS_TAC [IF_instr_index_with_EX_instr] >>
     `THE (I' (1,SUC t)) < THE (I' (3,SUC t)) + 4` by fs [] >> fs [] >>
     METIS_TAC [SC_self_mod_isa_not_affect_fetched_instr_extra]) >>
   Cases_on `I' (2,SUC t) <> NONE`  >> fs [] >-
    (`(fext (SUC t)).mem = (FUNPOW Next ((THE (I' (2,SUC t))) - 1) a).MEM` by cheat >>
     `(fext i).mem = (FUNPOW Next ((THE (I' (2,SUC t))) - 1) a).MEM` by fs [] >>
     `THE (I' (1,SUC t)) > THE (I' (2,SUC t)) /\ THE (I' (1,SUC t)) < THE (I' (2,SUC t)) + 2`
       by METIS_TAC [IF_instr_index_with_ID_instr] >>
     `THE (I' (1,SUC t)) < THE (I' (2,SUC t)) + 4` by fs [] >> fs [] >>
     METIS_TAC [SC_self_mod_isa_not_affect_fetched_instr_extra]) >>
   `(fext (SUC t)).mem = (FUNPOW Next ((THE (I' (1,SUC t))) - 1) a).MEM` by cheat >>
   `(fext i).mem = (FUNPOW Next ((THE (I' (1,SUC t))) - 1) a).MEM` by fs [] >> fs []) >-
   ((** command is 1 **)
   fs [instr_def] >>
   last_assum (mp_tac o is_mem_inst_read `SUC i`) >> simp [] >> strip_tac >>
   `m + SUC i = SUC t` by METIS_TAC [same_t_and_m_under_MAX_SET_SUC] >> simp [] >>
   `(fext (SUC i)).mem = (fext i).mem`
     by (Cases_on `m` >> fs [] >> `0 < SUC n` by rw [] >>
         `(fext (0 + SUC i)).mem = (fext i).mem` by fs [] >> fs []) >>
   `(fext (SUC i)).mem = (fext (SUC t)).mem` by fs [] >>
   `(agp32 fext fbits (SUC i)).PC = (agp32 fext fbits (m + SUC i)).PC`
     by METIS_TAC [PC_unchanged_after_disabled_cycles] >>
   `(agp32 fext fbits (SUC i)).PC = (FUNPOW Next (THE (I'(1,SUC t)) - 1) a).PC`
     by METIS_TAC [agp32_Rel_ag32_IF_disable_PC_correct,is_sch_def] >>
   Cases_on `I' (4,SUC t) <> NONE` >> fs [] >-
    (`(fext (SUC t)).mem = (FUNPOW Next (THE (I' (4,SUC t))) a).MEM` by cheat >>
     `(fext i).mem = (FUNPOW Next (THE (I' (4,SUC t))) a).MEM` by fs [] >>
     `THE (I' (1,SUC t)) > THE (I' (4,SUC t)) /\ THE (I' (1,SUC t)) < THE (I' (4,SUC t)) + 4`
       by METIS_TAC [IF_instr_index_big_then_MEM_disable] >>
     METIS_TAC [SC_self_mod_isa_not_affect_fetched_instr]) >>
   Cases_on `I' (3,SUC t) <> NONE` >> fs [] >-
    (`(fext (SUC t)).mem = (FUNPOW Next ((THE (I' (3,SUC t))) - 1) a).MEM` by cheat >>
     `(fext i).mem = (FUNPOW Next ((THE (I' (3,SUC t))) - 1) a).MEM` by fs [] >>
     `THE (I' (1,SUC t)) > THE (I' (3,SUC t)) /\ THE (I' (1,SUC t)) < THE (I' (3,SUC t)) + 3`
       by METIS_TAC [IF_instr_index_with_EX_instr] >>
     `THE (I' (1,SUC t)) < THE (I' (3,SUC t)) + 4` by fs [] >> fs [] >>
     METIS_TAC [SC_self_mod_isa_not_affect_fetched_instr_extra]) >>
   Cases_on `I' (2,SUC t) <> NONE`  >> fs [] >-
    (`(fext (SUC t)).mem = (FUNPOW Next ((THE (I' (2,SUC t))) - 1) a).MEM` by cheat >>
     `(fext i).mem = (FUNPOW Next ((THE (I' (2,SUC t))) - 1) a).MEM` by fs [] >>
     `THE (I' (1,SUC t)) > THE (I' (2,SUC t)) /\ THE (I' (1,SUC t)) < THE (I' (2,SUC t)) + 2`
       by METIS_TAC [IF_instr_index_with_ID_instr] >>
     `THE (I' (1,SUC t)) < THE (I' (2,SUC t)) + 4` by fs [] >> fs [] >>
     METIS_TAC [SC_self_mod_isa_not_affect_fetched_instr_extra]) >>
   `(fext (SUC t)).mem = (FUNPOW Next ((THE (I' (1,SUC t))) - 1) a).MEM` by cheat >>
   `(fext i).mem = (FUNPOW Next ((THE (I' (1,SUC t))) - 1) a).MEM` by fs [] >> fs []) >>
   (** command is  0: not possible **)
  last_assum (mp_tac o is_mem_do_nothing `SUC i`) >> simp [] >> strip_tac >>
  Cases_on `SUC i = t` >> fs [] >>
  Cases_on `SUC i > t` >> fs [] >>
  `SUC i < t` by fs [] >>
  `(SUC i) IN {t0 | t0 < t /\ (fext t0).ready}` by fs [] >>
  `(SUC i) <= i` by METIS_TAC [MAX_SET_DEF] >> fs []
QED

(** IF_instr when IF is disabled **)
Theorem agp32_Rel_ag32_IF_disable_instr_correct:
  !fext fbits a t I.
    SC_self_mod_isa a ==>
    is_mem fext_accessor_circuit (agp32 fext fbits) fext ==>
    is_sch I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (1,SUC t) <> NONE ==>
    (fext (SUC t)).ready ==>
    ~enable_stg 1 (agp32 fext fbits t) ==>
    (agp32 fext fbits (SUC t)).IF.IF_instr = instr (FUNPOW Next (THE (I (1,SUC t)) - 1) a)
Proof
  rw [] >>
  `?s s'. (agp32 fext fbits (SUC t)).IF.IF_instr = (IF_instr_update (fext (SUC t)) s s').IF.IF_instr`
    by rw [agp32_IF_instr_updated_by_IF_instr_update] >>
  rw [IF_instr_update_def] >>
  Cases_on `(fext t).ready` >-
   (** memory is ready at the previous cycle **)
   (last_assum (assume_tac o is_mem_def_mem_no_errors) >>
    Cases_on_word_value `(agp32 fext fbits (SUC t)).command` >>
    fs [agp32_command_impossible_values] >-
     ((** command is 4 **)
     rw [instr_def] >>
     last_assum (mp_tac o is_mem_data_flush `SUC t`) >> rw [] >>
     Cases_on `m` >> fs [] >-
      (`(agp32 fext fbits (SUC t)).PC = (FUNPOW Next (THE (I'(1,SUC t)) - 1) a).PC`
         by METIS_TAC [agp32_Rel_ag32_IF_disable_PC_correct,is_sch_def] >>
       Cases_on `I' (4,SUC t) <> NONE`  >> fs [] >-
        (`(fext (SUC t)).mem = (FUNPOW Next (THE (I' (4,SUC t))) a).MEM` by cheat >>
         `(fext t).mem = (FUNPOW Next (THE (I' (4,SUC t))) a).MEM` by fs [] >>
         `THE (I' (1,SUC t)) > THE (I' (4,SUC t)) /\ THE (I' (1,SUC t)) < THE (I' (4,SUC t)) + 4`
           by METIS_TAC [IF_instr_index_big_then_MEM_disable] >> fs [] >>
         METIS_TAC [SC_self_mod_isa_not_affect_fetched_instr]) >>
       Cases_on `I' (3,SUC t) <> NONE`  >> fs [] >-
        (`(fext (SUC t)).mem = (FUNPOW Next ((THE (I' (3,SUC t))) - 1) a).MEM` by cheat >>
         `THE (I' (1,SUC t)) > THE (I' (3,SUC t)) /\ THE (I' (1,SUC t)) < THE (I' (3,SUC t)) + 3`
           by METIS_TAC [IF_instr_index_with_EX_instr] >>
         `THE (I' (1,SUC t)) < THE (I' (3,SUC t)) + 4` by rw [] >> fs [] >>
         METIS_TAC [SC_self_mod_isa_not_affect_fetched_instr_extra]) >>
       Cases_on `I' (2,SUC t) <> NONE`  >> fs [] >-
        (`(fext (SUC t)).mem = (FUNPOW Next ((THE (I' (2,SUC t))) - 1) a).MEM` by cheat >>
         `THE (I' (1,SUC t)) > THE (I' (2,SUC t)) /\ THE (I' (1,SUC t)) < THE (I' (2,SUC t)) + 2`
           by METIS_TAC [IF_instr_index_with_ID_instr] >>
         `THE (I' (1,SUC t)) < THE (I' (2,SUC t)) + 4` by rw [] >> fs [] >>
         METIS_TAC [SC_self_mod_isa_not_affect_fetched_instr_extra]) >>
       `(fext (SUC t)).mem = (FUNPOW Next ((THE (I' (1,SUC t))) - 1) a).MEM` by cheat >> fs []) >>
     `~(fext (0 + SUC t)).ready` by fs [] >> fs []) >-
     ((** command is 3 **)
     rw [instr_def] >>
     last_assum (mp_tac o is_mem_data_write `SUC t`) >> rw [] >>
     Cases_on `m` >> fs [] >-
      (`(agp32 fext fbits (SUC t)).PC = (FUNPOW Next (THE (I'(1,SUC t)) - 1) a).PC`
         by METIS_TAC [agp32_Rel_ag32_IF_disable_PC_correct,is_sch_def] >>
       qpat_abbrev_tac `newmem = mem_update _ _ _ _` >>
       Cases_on `I' (4,SUC t) <> NONE`  >> fs [] >-
        (`(fext (SUC t)).mem = (FUNPOW Next (THE (I' (4,SUC t))) a).MEM` by cheat >>
         `newmem = (FUNPOW Next (THE (I' (4,SUC t))) a).MEM` by fs [] >>
         `THE (I' (1,SUC t)) > THE (I' (4,SUC t)) /\ THE (I' (1,SUC t)) < THE (I' (4,SUC t)) + 4`
           by METIS_TAC [IF_instr_index_big_then_MEM_disable] >> fs [] >>
         METIS_TAC [SC_self_mod_isa_not_affect_fetched_instr]) >>
       Cases_on `I' (3,SUC t) <> NONE`  >> fs [] >-
        (`(fext (SUC t)).mem = (FUNPOW Next ((THE (I' (3,SUC t))) - 1) a).MEM` by cheat >>
         `newmem = (FUNPOW Next (THE (I' (3,SUC t)) - 1) a).MEM` by fs [] >>
         `THE (I' (1,SUC t)) > THE (I' (3,SUC t)) /\ THE (I' (1,SUC t)) < THE (I' (3,SUC t)) + 3`
           by METIS_TAC [IF_instr_index_with_EX_instr] >>
         `THE (I' (1,SUC t)) < THE (I' (3,SUC t)) + 4` by rw [] >> fs [] >>
         METIS_TAC [SC_self_mod_isa_not_affect_fetched_instr_extra]) >>
       Cases_on `I' (2,SUC t) <> NONE`  >> fs [] >-
        (`(fext (SUC t)).mem = (FUNPOW Next ((THE (I' (2,SUC t))) - 1) a).MEM` by cheat >>
         `newmem = (FUNPOW Next (THE (I' (2,SUC t)) - 1) a).MEM` by fs [] >>
         `THE (I' (1,SUC t)) > THE (I' (2,SUC t)) /\ THE (I' (1,SUC t)) < THE (I' (2,SUC t)) + 2`
           by METIS_TAC [IF_instr_index_with_ID_instr] >>
         `THE (I' (1,SUC t)) < THE (I' (2,SUC t)) + 4` by rw [] >> fs [] >>
         METIS_TAC [SC_self_mod_isa_not_affect_fetched_instr_extra]) >>
       `(fext (SUC t)).mem = (FUNPOW Next ((THE (I' (1,SUC t))) - 1) a).MEM` by cheat >>
       `newmem = (FUNPOW Next (THE (I' (1,SUC t)) - 1) a).MEM` by fs [] >> fs []) >>
     `~(fext (0 + SUC t)).ready` by fs [] >> fs []) >-
     ((** command is 2 **)
     rw [instr_def] >>
     last_assum (mp_tac o is_mem_data_read `SUC t`) >> rw [] >>
     Cases_on `m` >> fs [] >-
      (`(agp32 fext fbits (SUC t)).PC = (FUNPOW Next (THE (I'(1,SUC t)) - 1) a).PC`
         by METIS_TAC [agp32_Rel_ag32_IF_disable_PC_correct,is_sch_def] >>
       Cases_on `I' (4,SUC t) <> NONE`  >> fs [] >-
        (`(fext (SUC t)).mem = (FUNPOW Next (THE (I' (4,SUC t))) a).MEM` by cheat >>
         `(fext t).mem = (FUNPOW Next (THE (I' (4,SUC t))) a).MEM` by fs [] >>
         `THE (I' (1,SUC t)) > THE (I' (4,SUC t)) /\ THE (I' (1,SUC t)) < THE (I' (4,SUC t)) + 4`
           by METIS_TAC [IF_instr_index_big_then_MEM_disable] >> fs [] >>
         METIS_TAC [SC_self_mod_isa_not_affect_fetched_instr]) >>
       Cases_on `I' (3,SUC t) <> NONE`  >> fs [] >-
        (`(fext (SUC t)).mem = (FUNPOW Next ((THE (I' (3,SUC t))) - 1) a).MEM` by cheat >>
         `THE (I' (1,SUC t)) > THE (I' (3,SUC t)) /\ THE (I' (1,SUC t)) < THE (I' (3,SUC t)) + 3`
           by METIS_TAC [IF_instr_index_with_EX_instr] >>
         `THE (I' (1,SUC t)) < THE (I' (3,SUC t)) + 4` by rw [] >> fs [] >>
         METIS_TAC [SC_self_mod_isa_not_affect_fetched_instr_extra]) >>
       Cases_on `I' (2,SUC t) <> NONE`  >> fs [] >-
        (`(fext (SUC t)).mem = (FUNPOW Next ((THE (I' (2,SUC t))) - 1) a).MEM` by cheat >>
         `THE (I' (1,SUC t)) > THE (I' (2,SUC t)) /\ THE (I' (1,SUC t)) < THE (I' (2,SUC t)) + 2`
           by METIS_TAC [IF_instr_index_with_ID_instr] >>
         `THE (I' (1,SUC t)) < THE (I' (2,SUC t)) + 4` by rw [] >> fs [] >>
         METIS_TAC [SC_self_mod_isa_not_affect_fetched_instr_extra]) >>
       `(fext (SUC t)).mem = (FUNPOW Next ((THE (I' (1,SUC t))) - 1) a).MEM` by cheat >> fs []) >>
     `~(fext (0 + SUC t)).ready` by fs [] >> fs []) >-
     ((** command is 1 **)
     rw [instr_def] >>
     last_assum (mp_tac o is_mem_inst_read `SUC t`) >> rw [] >>
     Cases_on `m` >> fs [] >-
      (`(agp32 fext fbits (SUC t)).PC = (FUNPOW Next (THE (I'(1,SUC t)) - 1) a).PC`
         by METIS_TAC [agp32_Rel_ag32_IF_disable_PC_correct,is_sch_def] >>
       Cases_on `I' (4,SUC t) <> NONE`  >> fs [] >-
        (`(fext (SUC t)).mem = (FUNPOW Next (THE (I' (4,SUC t))) a).MEM` by cheat >>
         `(fext t).mem = (FUNPOW Next (THE (I' (4,SUC t))) a).MEM` by fs [] >>
         `THE (I' (1,SUC t)) > THE (I' (4,SUC t)) /\ THE (I' (1,SUC t)) < THE (I' (4,SUC t)) + 4`
           by METIS_TAC [IF_instr_index_big_then_MEM_disable] >> fs [] >>
         METIS_TAC [SC_self_mod_isa_not_affect_fetched_instr]) >>
       Cases_on `I' (3,SUC t) <> NONE`  >> fs [] >-
        (`(fext (SUC t)).mem = (FUNPOW Next ((THE (I' (3,SUC t))) - 1) a).MEM` by cheat >>
         `THE (I' (1,SUC t)) > THE (I' (3,SUC t)) /\ THE (I' (1,SUC t)) < THE (I' (3,SUC t)) + 3`
           by METIS_TAC [IF_instr_index_with_EX_instr] >>
         `THE (I' (1,SUC t)) < THE (I' (3,SUC t)) + 4` by rw [] >> fs [] >>
         METIS_TAC [SC_self_mod_isa_not_affect_fetched_instr_extra]) >>
       Cases_on `I' (2,SUC t) <> NONE`  >> fs [] >-
        (`(fext (SUC t)).mem = (FUNPOW Next ((THE (I' (2,SUC t))) - 1) a).MEM` by cheat >>
         `THE (I' (1,SUC t)) > THE (I' (2,SUC t)) /\ THE (I' (1,SUC t)) < THE (I' (2,SUC t)) + 2`
           by METIS_TAC [IF_instr_index_with_ID_instr] >>
         `THE (I' (1,SUC t)) < THE (I' (2,SUC t)) + 4` by rw [] >> fs [] >>
         METIS_TAC [SC_self_mod_isa_not_affect_fetched_instr_extra]) >>
       `(fext (SUC t)).mem = (FUNPOW Next ((THE (I' (1,SUC t))) - 1) a).MEM` by cheat >> fs []) >>
     `~(fext (0 + SUC t)).ready` by fs [] >> fs []) >>
   (** command is 0 **)
    `I' (1,SUC t) = I' (1,t)` by fs [is_sch_def,is_sch_disable_def] >> fs [] >>
    last_assum (mp_tac o is_mem_do_nothing `SUC t`) >> rw [] >>
    `?s s'.(agp32 fext fbits t).IF.IF_instr = (IF_instr_update (fext t) s s').IF.IF_instr`
      by rw [agp32_IF_instr_exists_IF_instr_update] >>
    fs [IF_instr_update_def,Rel_def,IF_instr_Rel_def]) >>
  (** memory is NOT ready at the previous cycle **)
  METIS_TAC [agp32_Rel_ag32_IF_disable_instr_not_ready_before_correct]
QED

(** IF_instr_Rel between ISA and circuit states **)
Theorem agp32_Rel_ag32_IF_instr_Rel_correct:
  !fext fbits a t I.
    SC_self_mod_isa a ==>
    is_mem fext_accessor_circuit (agp32 fext fbits) fext ==>
    is_sch I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (1,SUC t) <> NONE ==>
    (fext (SUC t)).ready ==>
    IF_instr_Rel (agp32 fext fbits (SUC t)) a (THE (I (1,SUC t)))
Proof
  rw [IF_instr_Rel_def] >>
  Cases_on `enable_stg 1 (agp32 fext fbits t)` >-
   METIS_TAC [agp32_Rel_ag32_IF_enable_instr_correct] >>
  METIS_TAC [agp32_Rel_ag32_IF_disable_instr_correct]
QED


(* IF_PC_input when jump *)
Theorem agp32_Rel_ag32_IF_PC_input_jump_correct:
  !fext fbits a t I.
    is_sch_execute I (agp32 fext fbits) a ==>
    is_sch_disable I (agp32 fext fbits) ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (3,SUC t) <> NONE ==>
    reg_data_vaild 3 (agp32 fext fbits (SUC t)) ==>
    (agp32 fext fbits (SUC t)).EX.EX_jump_sel ==>
    (agp32 fext fbits (SUC t)).IF.IF_PC_input = (FUNPOW Next (THE (I (3,SUC t))) a).PC
Proof
  rw [is_sch_execute_def,is_sch_disable_def] >>
  Q.ABBREV_TAC `s = agp32 fext fbits t` >>
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
  rw [] >>  Q.ABBREV_TAC `s = agp32 fext fbits t` >>
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
   fs [agp32_Rel_ag32_IF_enable_PC_correct] >>
  fs [agp32_Rel_ag32_IF_disable_PC_correct]
QED

val _ = export_theory ();
