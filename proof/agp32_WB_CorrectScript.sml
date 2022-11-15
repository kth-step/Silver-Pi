open hardwarePreamble translatorTheory translatorLib arithmeticTheory wordsExtraTheory dep_rewrite blastLib bitstringSyntax fcpSyntax listSyntax wordsSyntax agp32StateTheory agp32EnvironmentTheory agp32ProcessorTheory ag32Theory ag32ExtraTheory ag32UtilitiesTheory agp32RelationTheory agp32UpdateTheory agp32InternalTheory;

(* correctness of WB stage items with respect to the ISA *)
val _ = new_theory "agp32_WB_Correct";

val _ = prefer_num ();
val _ = guess_lengths ();


(** WB_PC **)
Theorem agp32_Rel_ag32_WB_PC_correct:
  !fext fbits a t I.
    is_sch_writeback I (agp32 fext fbits) ==>
    is_sch_disable I (agp32 fext fbits) ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (5,SUC t) <> NONE ==>
    (agp32 fext fbits (SUC t)).WB.WB_PC = (FUNPOW Next (THE (I (5,SUC t)) − 1) a).PC
Proof
  rw [] >> Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state] (fext t) s s` >>
  `(agp32 fext fbits (SUC t)).WB.WB_PC = (WB_pipeline (fext t) s s').WB.WB_PC`
    by cheat >> rw [] >>
  `(s'.WB.WB_state_flag = s.WB.WB_state_flag) /\ (s'.WB.WB_PC = s.WB.WB_PC)`
    by cheat >>
  Cases_on `enable_stg 5 (agp32 fext fbits t)` >-
   (`I' (5,SUC t) = I' (4,t)` by fs [is_sch_writeback_def] >> fs [] >>
    `s'.WB.WB_state_flag` by fs [enable_stg_def,Abbr `s`] >>
    fs [WB_pipeline_def,Rel_def,MEM_Rel_def]) >>
  `I' (5,SUC t) = I' (5,t)` by fs [is_sch_disable_def] >>
  `~s'.WB.WB_state_flag` by fs [enable_stg_def,Abbr `s`] >>
  fs [WB_pipeline_def,Rel_def,WB_Rel_def]
QED

(* WB_Rel *)
Theorem agp32_Rel_ag32_WB_Rel_correct:
  !fext fbits a t I.
    is_sch I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (5,SUC t) <> NONE ==>
    WB_Rel (fext (SUC t)) (agp32 fext fbits (SUC t)) a (THE (I (5,SUC t)))
Proof
  rw [WB_Rel_def] >>
  cheat
QED


(* registers R updated by WB stage *)
Theorem agp32_Rel_ag32_R_correct:
  !fext fbits a t I.
    is_sch I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (5,t) <> NONE ==>
    wb_data_vaild (agp32 fext fbits t) ==>
    (agp32 fext fbits (SUC t)).R = (FUNPOW Next (THE (I (5,t))) a).R
Proof
  rw [] >> Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state;WB_pipeline;MEM_pipeline;EX_pipeline] (fext t) s s` >>
  `(agp32 fext fbits (SUC t)).R = (REG_write (fext t) s s').R` by cheat >>
  fs [REG_write_def,wb_data_vaild_def] >>
  `(s'.R = s.R) /\ (s'.WB.WB_state_flag <=> s.WB.WB_state_flag) /\
  (s'.WB.WB_write_data = s.WB.WB_write_data)` by cheat >> fs [] >>
  Cases_on `s.WB.WB_write_reg` >> fs [Rel_def] >-
   (Cases_on `I' (5,t-1) = NONE` >> fs [] >-
     (`s.R = (FUNPOW Next (THE (I' (5,t)) - 1) a).R` by cheat >> rw [] >>
      `THE (I' (5,t)) <> 0` by cheat >>
      `THE (I' (5,t)) = SUC (THE (I' (5,t)) − 1)` by fs [] >>
      `(FUNPOW Next (THE (I' (5,t))) a).R =
      (FUNPOW Next (SUC (THE (I' (5,t)) - 1)) a).R` by METIS_TAC [] >>
      rw [FUNPOW_SUC] >>
      qpat_abbrev_tac `a0 = FUNPOW Next _ _` >> cheat) >>
    fs [] >>
    cheat (** I (5,t) = I (5,t-1) + 1 ? **)) >>
  Cases_on `I' (5,t-1) = NONE` >> fs [] >-
   (`s.R = (FUNPOW Next (THE (I' (5,t)) - 1) a).R` by cheat >> rw [] >>
    `THE (I' (5,t)) <> 0` by cheat >>
    `THE (I' (5,t)) = SUC (THE (I' (5,t)) − 1)` by fs [] >>
    `(FUNPOW Next (THE (I' (5,t))) a).R =
    (FUNPOW Next (SUC (THE (I' (5,t)) - 1)) a).R` by METIS_TAC [] >>
    rw [FUNPOW_SUC] >>
    qpat_abbrev_tac `a0 = FUNPOW Next _ _` >> cheat) >>
  fs [] >> cheat
QED

val _ = export_theory ();
