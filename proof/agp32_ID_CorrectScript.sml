open hardwarePreamble translatorTheory translatorLib arithmeticTheory dep_rewrite blastLib bitstringSyntax fcpSyntax listSyntax wordsSyntax agp32StateTheory agp32EnvironmentTheory agp32ProcessorTheory ag32Theory ag32ExtraTheory ag32UtilitiesTheory agp32RelationTheory agp32UpdateTheory agp32InternalTheory agp32StepLib;

(* correctness of ID stage items against the ISA *)
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
  fs [Rel_def,IF_Rel_def,IF_disable_Rel_def,Abbr `s`] >>
  Cases_on `~enable_stg 1 (agp32 fext fbits (t − 1))` >> fs [] >>
  Cases_on `reg_data_vaild 3 (agp32 fext fbits (t − 1))` >> fs [] >>
  `(agp32 fext fbits (t-1)).MEM.MEM_state_flag`
    by fs [enable_stg_def,agp32_IF_PC_write_enable_and_EX_MEM_flags] >>
  fs [reg_data_vaild_def,enable_stg_def]
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
  fs [Rel_def,IF_Rel_def,IF_disable_Rel_def,Abbr `s`] >>
  Cases_on `enable_stg 1 (agp32 fext fbits (t − 1))` >> fs [] >-
   (Cases_on `reg_data_vaild 3 (agp32 fext fbits (t − 1))` >> fs [] >-
     (`(fext t).ready`
        by METIS_TAC [enable_stg_def,agp32_ID_ID_write_enable_and_fext_ready] >> fs []) >>
    `(agp32 fext fbits (t-1)).MEM.MEM_state_flag`
      by fs [enable_stg_def,agp32_IF_PC_write_enable_and_EX_MEM_flags] >>
    fs [reg_data_vaild_def,enable_stg_def]) >>
  `(fext t).ready` by METIS_TAC [enable_stg_def,agp32_ID_ID_write_enable_and_fext_ready] >>
  cheat
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
  rw [ID_Rel_def] >-
   fs [agp32_Rel_ag32_ID_PC_correct] >-
   fs [agp32_Rel_ag32_ID_instr_correct] >>
  cheat
QED

val _ = export_theory ();
