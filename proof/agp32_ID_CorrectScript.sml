open hardwarePreamble translatorTheory translatorLib arithmeticTheory dep_rewrite blastLib bitstringSyntax fcpSyntax listSyntax wordsSyntax agp32StateTheory agp32EnvironmentTheory agp32ProcessorTheory ag32Theory ag32ExtraTheory ag32UtilitiesTheory agp32RelationTheory agp32UpdateTheory agp32InternalTheory;

(* correctness of ID stage items with respect to the ISA *)
val _ = new_theory "agp32_ID_Correct";

val _ = prefer_num ();
val _ = guess_lengths ();


(** ID_PC **)
Theorem agp32_Rel_ag32_ID_PC_correct:
  !fext fbits a t I.
    is_sch_decode I (agp32 fext fbits) ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    enable_stg 2 (agp32 fext fbits t) ==>
    I (2,SUC t) <> NONE ==>
    (agp32 fext fbits (SUC t)).ID.ID_PC = (FUNPOW Next (THE (I (2,SUC t)) − 1) a).PC
Proof
  rw [is_sch_decode_def] >>
  Cases_on `I' (1,t) = NONE` >> fs [] >-
   METIS_TAC [] >>
  Q.ABBREV_TAC `s = agp32 fext fbits t` >>             
  Q.ABBREV_TAC `s' = procs [agp32_next_state;WB_pipeline;MEM_pipeline;EX_pipeline;
                            REG_write] (fext t) s s` >>
  `(agp32 fext fbits (SUC t)).ID.ID_PC = (ID_pipeline (fext t) s s').ID.ID_PC`
    by fs [agp32_ID_PC_instr_updated_by_ID_pipeline,Abbr `s`,Abbr `s'`] >> rw [] >>
  `s.ID.ID_ID_write_enable` by fs [enable_stg_def] >>
  `s'.ID.ID_ID_write_enable`
    by METIS_TAC [agp32_same_items_before_ID_pipeline,Abbr `s`,Abbr `s'`] >>
  rw [ID_pipeline_def] >>
  fs [Rel_def,IF_PC_Rel_def]
QED


(** ID_instr **)
Theorem agp32_Rel_ag32_ID_instr_correct:
  !fext fbits a t I.
    is_sch_decode I (agp32 fext fbits) ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    enable_stg 2 (agp32 fext fbits t) ==>
    I (2,SUC t) <> NONE ==>
    (agp32 fext fbits (SUC t)).ID.ID_instr = instr (FUNPOW Next (THE (I (2,SUC t)) − 1) a)
Proof
  rw [is_sch_decode_def] >>
  Cases_on `I' (1,t) = NONE` >> fs [] >-
   METIS_TAC [] >>
  Q.ABBREV_TAC `s = agp32 fext fbits t` >>             
  Q.ABBREV_TAC `s' = procs [agp32_next_state;WB_pipeline;MEM_pipeline;EX_pipeline;
                            REG_write] (fext t) s s` >>
  `(agp32 fext fbits (SUC t)).ID.ID_instr = (ID_pipeline (fext t) s s').ID.ID_instr`
    by fs [agp32_ID_PC_instr_updated_by_ID_pipeline,Abbr `s`,Abbr `s'`] >> rw [] >>
  `s.ID.ID_ID_write_enable` by fs [enable_stg_def] >>
  `s'.ID.ID_ID_write_enable /\ s'.IF.IF_instr = s.IF.IF_instr`
    by METIS_TAC [agp32_same_items_before_ID_pipeline,Abbr `s`,Abbr `s'`] >>
  rw [ID_pipeline_def] >>
  `(fext t).ready` by METIS_TAC [enable_stg_def,agp32_ID_ID_write_enable_and_fext_ready] >>
  fs [Rel_def,IF_instr_Rel_def]
QED


(** ID_addrA/B/W **)
Theorem agp32_Rel_ag32_ID_addr_correct:
  !fext fbits a t I.
    is_sch_decode I (agp32 fext fbits) ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    enable_stg 2 (agp32 fext fbits t) ==>
    I (2,SUC t) <> NONE ==>
    ((agp32 fext fbits (SUC t)).ID.ID_addrA = addrA (FUNPOW Next (THE (I (2,SUC t)) − 1) a)) /\
    ((agp32 fext fbits (SUC t)).ID.ID_addrB = addrB (FUNPOW Next (THE (I (2,SUC t)) − 1) a)) /\
    ((agp32 fext fbits (SUC t)).ID.ID_addrW = addrW (FUNPOW Next (THE (I (2,SUC t)) − 1) a))
Proof
  rpt gen_tac >> rpt strip_tac >>
  simp [addrA_def,addrB_def,addrW_def] >>
  `(agp32 fext fbits (SUC t)).ID.ID_instr = instr (FUNPOW Next (THE (I' (2,SUC t)) − 1) a)`
    by fs [agp32_Rel_ag32_ID_instr_correct] >>
  Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state; WB_pipeline; MEM_pipeline; EX_pipeline;
                            REG_write; ID_pipeline; IF_PC_update; Acc_compute] (fext t) s s` >>
  Q.ABBREV_TAC `s'' = procs [ForwardA; ForwardB; ForwardW; IF_instr_update; ID_opc_func_update;
                             ID_imm_update] (fext (SUC t)) s' s'` >>                          
  `?s0. (agp32 fext fbits (SUC t)).ID.ID_addrA = (ID_data_update (fext (SUC t)) s0 s'').ID.ID_addrA /\
  (agp32 fext fbits (SUC t)).ID.ID_addrB = (ID_data_update (fext (SUC t)) s0 s'').ID.ID_addrB /\
  (agp32 fext fbits (SUC t)).ID.ID_addrW = (ID_data_update (fext (SUC t)) s0 s'').ID.ID_addrW`
    by fs [Abbr `s`,Abbr `s'`,Abbr `s''`,agp32_ID_addr_updated_by_ID_data_update] >>
  fs [ID_data_update_def] >>
  `s''.ID.ID_instr = (agp32 fext fbits (SUC t)).ID.ID_instr`
    by fs [Abbr `s`,Abbr `s'`,Abbr `s''`,agp32_same_ID_instr_after_ID_imm_update] >> fs []
QED


(** flagA/B/W: indicate imm or reg **)
Theorem agp32_Rel_ag32_ID_flag_correct:
  !fext fbits a t I.
    is_sch_decode I (agp32 fext fbits) ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    enable_stg 2 (agp32 fext fbits t) ==>
    I (2,SUC t) <> NONE ==>
    ((agp32 fext fbits (SUC t)).ID.ID_addrA_disable = flagA (FUNPOW Next (THE (I (2,SUC t)) − 1) a)) /\
    ((agp32 fext fbits (SUC t)).ID.ID_addrB_disable = flagB (FUNPOW Next (THE (I (2,SUC t)) − 1) a)) /\
    ((agp32 fext fbits (SUC t)).ID.ID_addrW_disable = flagW (FUNPOW Next (THE (I (2,SUC t)) − 1) a))
Proof
  rpt gen_tac >> rpt disch_tac >>
  simp [flagA_def,flagB_def,flagW_def] >>
  `(agp32 fext fbits (SUC t)).ID.ID_instr = instr (FUNPOW Next (THE (I' (2,SUC t)) − 1) a)`
    by fs [agp32_Rel_ag32_ID_instr_correct] >>
  Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state; WB_pipeline; MEM_pipeline; EX_pipeline;
                            REG_write; ID_pipeline; IF_PC_update; Acc_compute] (fext t) s s` >>
  Q.ABBREV_TAC `s'' = procs [ForwardA; ForwardB; ForwardW; IF_instr_update; ID_opc_func_update;
                             ID_imm_update] (fext (SUC t)) s' s'` >>                          
  `?s0. ((agp32 fext fbits (SUC t)).ID.ID_addrA_disable <=>
         (ID_data_update (fext (SUC t)) s0 s'').ID.ID_addrA_disable) /\
  ((agp32 fext fbits (SUC t)).ID.ID_addrB_disable <=>
   (ID_data_update (fext (SUC t)) s0 s'').ID.ID_addrB_disable) /\
  ((agp32 fext fbits (SUC t)).ID.ID_addrW_disable <=>
   (ID_data_update (fext (SUC t)) s0 s'').ID.ID_addrW_disable)`
    by fs [Abbr `s`,Abbr `s'`,Abbr `s''`,agp32_ID_flag_updated_by_ID_data_update] >>
  fs [ID_data_update_def] >>
  `s''.ID.ID_instr = (agp32 fext fbits (SUC t)).ID.ID_instr`
    by fs [Abbr `s`,Abbr `s'`,Abbr `s''`,agp32_same_ID_instr_after_ID_imm_update] >> fs []
QED


(** immA/B/W **)
Theorem agp32_Rel_ag32_ID_imm_data_correct:
  !fext fbits a t I.
    is_sch_decode I (agp32 fext fbits) ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    enable_stg 2 (agp32 fext fbits t) ==>
    I (2,SUC t) <> NONE ==>
    ((agp32 fext fbits (SUC t)).ID.ID_immA = immA (FUNPOW Next (THE (I (2,SUC t)) − 1) a)) /\
    ((agp32 fext fbits (SUC t)).ID.ID_immB = immB (FUNPOW Next (THE (I (2,SUC t)) − 1) a)) /\
    ((agp32 fext fbits (SUC t)).ID.ID_immW = immW (FUNPOW Next (THE (I (2,SUC t)) − 1) a))
Proof
  rpt gen_tac >> rpt disch_tac >>
  simp [immA_def,immB_def,immW_def] >>
  `(agp32 fext fbits (SUC t)).ID.ID_instr = instr (FUNPOW Next (THE (I' (2,SUC t)) − 1) a)`
    by fs [agp32_Rel_ag32_ID_instr_correct] >>
  Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state; WB_pipeline; MEM_pipeline; EX_pipeline;
                            REG_write; ID_pipeline; IF_PC_update; Acc_compute] (fext t) s s` >>
  Q.ABBREV_TAC `s'' = procs [ForwardA; ForwardB; ForwardW; IF_instr_update; ID_opc_func_update;
                             ID_imm_update] (fext (SUC t)) s' s'` >>                          
  `?s0. (agp32 fext fbits (SUC t)).ID.ID_immA = (ID_data_update (fext (SUC t)) s0 s'').ID.ID_immA /\
  (agp32 fext fbits (SUC t)).ID.ID_immB = (ID_data_update (fext (SUC t)) s0 s'').ID.ID_immB /\
  (agp32 fext fbits (SUC t)).ID.ID_immW = (ID_data_update (fext (SUC t)) s0 s'').ID.ID_immW`
    by fs [Abbr `s`,Abbr `s'`,Abbr `s''`,agp32_ID_imm_data_updated_by_ID_data_update] >>
  fs [ID_data_update_def] >>
  `s''.ID.ID_instr = (agp32 fext fbits (SUC t)).ID.ID_instr`
    by fs [Abbr `s`,Abbr `s'`,Abbr `s''`,agp32_same_ID_instr_after_ID_imm_update] >> fs []
QED


(** imm for LoadConstant and LoadUpperConstant **)
Theorem agp32_Rel_ag32_ID_imm_correct:
  !fext fbits a t I.
    is_sch_decode I (agp32 fext fbits) ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    enable_stg 2 (agp32 fext fbits t) ==>
    I (2,SUC t) <> NONE ==>
    (agp32 fext fbits (SUC t)).ID.ID_imm = imm (FUNPOW Next (THE (I (2,SUC t)) − 1) a)
Proof
  rw [] >>
  `(agp32 fext fbits (SUC t)).ID.ID_instr = instr (FUNPOW Next (THE (I' (2,SUC t)) − 1) a)`
    by fs [agp32_Rel_ag32_ID_instr_correct] >>
  Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state; WB_pipeline; MEM_pipeline; EX_pipeline;
                            REG_write; ID_pipeline; IF_PC_update; Acc_compute] (fext t) s s` >>
  Q.ABBREV_TAC `s'' = procs [ForwardA; ForwardB; ForwardW; IF_instr_update; ID_opc_func_update]
                            (fext (SUC t)) s' s'` >>
  `(agp32 fext fbits (SUC t)).ID.ID_imm = (ID_imm_update (fext (SUC t)) s' s'').ID.ID_imm`
    by fs [Abbr `s`,Abbr `s'`,Abbr `s''`,agp32_ID_imm_updated_by_ID_imm_update] >>
  `s''.ID.ID_instr = (agp32 fext fbits (SUC t)).ID.ID_instr`
    by fs [Abbr `s`,Abbr `s'`,Abbr `s''`,agp32_same_ID_instr_after_ID_opc_func_update] >>
   fs [ID_imm_update_def,imm_def] >> rw []
QED


(* ID stage *)
Theorem agp32_Rel_ag32_ID_Rel_correct:
  !fext fbits a t I.
    is_sch_decode I (agp32 fext fbits) ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    enable_stg 2 (agp32 fext fbits t) ==>
    I (2,SUC t) <> NONE ==>
    ID_Rel (fext (SUC t)) (agp32 fext fbits (SUC t)) a (THE (I (2,SUC t)))
Proof
  rw [ID_Rel_def] >>
  fs [agp32_Rel_ag32_ID_PC_correct,agp32_Rel_ag32_ID_instr_correct,agp32_Rel_ag32_ID_addr_correct,
      agp32_Rel_ag32_ID_flag_correct,agp32_Rel_ag32_ID_imm_data_correct,
      agp32_Rel_ag32_ID_imm_correct] >>
  cheat
QED

val _ = export_theory ();
