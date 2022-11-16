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
    by fs [agp32_WB_PC_imm_addrW_updated_by_WB_pipeline] >> rw [] >>
  `(s'.WB.WB_state_flag = s.WB.WB_state_flag) /\ (s'.WB.WB_PC = s.WB.WB_PC)`
    by METIS_TAC [Abbr `s`,Abbr `s'`,agp32_same_WB_items_before_WB_pipeline] >>
  Cases_on `enable_stg 5 (agp32 fext fbits t)` >-
   (`I' (5,SUC t) = I' (4,t)` by fs [is_sch_writeback_def] >> fs [] >>
    `s'.WB.WB_state_flag` by fs [enable_stg_def,Abbr `s`] >>
    fs [WB_pipeline_def,Rel_def,MEM_Rel_def]) >>
  `I' (5,SUC t) = I' (5,t)` by fs [is_sch_disable_def] >>
  `~s'.WB.WB_state_flag` by fs [enable_stg_def,Abbr `s`] >>
  fs [WB_pipeline_def,Rel_def,WB_Rel_def]
QED

(** WB_addrW **)
Theorem agp32_Rel_ag32_WB_addrW_correct:
  !fext fbits a t I.
    is_sch_writeback I (agp32 fext fbits) ==>
    is_sch_disable I (agp32 fext fbits) ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (5,SUC t) <> NONE ==>
    (agp32 fext fbits (SUC t)).WB.WB_addrW = addrW (FUNPOW Next (THE (I (5,SUC t)) − 1) a)
Proof
  rw [] >> Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state] (fext t) s s` >>
  `(agp32 fext fbits (SUC t)).WB.WB_addrW = (WB_pipeline (fext t) s s').WB.WB_addrW`
    by fs [agp32_WB_PC_imm_addrW_updated_by_WB_pipeline] >> rw [] >>
  `(s'.WB.WB_state_flag = s.WB.WB_state_flag) /\ (s'.WB.WB_addrW = s.WB.WB_addrW)`
    by METIS_TAC [Abbr `s`,Abbr `s'`,agp32_same_WB_items_before_WB_pipeline] >>
  Cases_on `enable_stg 5 (agp32 fext fbits t)` >-
   (`I' (5,SUC t) = I' (4,t)` by fs [is_sch_writeback_def] >> fs [] >>
    `s'.WB.WB_state_flag` by fs [enable_stg_def,Abbr `s`] >>
    fs [WB_pipeline_def,Rel_def,MEM_Rel_def]) >>
  `I' (5,SUC t) = I' (5,t)` by fs [is_sch_disable_def] >>
  `~s'.WB.WB_state_flag` by fs [enable_stg_def,Abbr `s`] >>
  fs [WB_pipeline_def,Rel_def,WB_Rel_def]
QED

(** WB_opc **)
Theorem agp32_Rel_ag32_WB_opc_correct:
  !fext fbits a t I.
    is_sch_writeback I (agp32 fext fbits) ==>
    is_sch_disable I (agp32 fext fbits) ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (5,SUC t) <> NONE ==>
    (agp32 fext fbits (SUC t)).WB.WB_opc = opc (FUNPOW Next (THE (I (5,SUC t)) − 1) a)
Proof
  rw [] >> Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state] (fext t) s s` >>
  `(agp32 fext fbits (SUC t)).WB.WB_opc = (WB_pipeline (fext t) s s').WB.WB_opc`
    by fs [agp32_WB_opc_updated_by_WB_pipeline] >> rw [] >>
  `(s'.WB.WB_state_flag = s.WB.WB_state_flag) /\ (s'.WB.WB_opc = s.WB.WB_opc)`
    by METIS_TAC [Abbr `s`,Abbr `s'`,agp32_same_WB_items_before_WB_pipeline] >>
  Cases_on `enable_stg 5 (agp32 fext fbits t)` >-
   (`I' (5,SUC t) = I' (4,t)` by fs [is_sch_writeback_def] >> fs [] >>
    `s'.WB.WB_state_flag` by fs [enable_stg_def,Abbr `s`] >>
    fs [WB_pipeline_def,Rel_def,MEM_Rel_def]) >>
  `I' (5,SUC t) = I' (5,t)` by fs [is_sch_disable_def] >>
  `~s'.WB.WB_state_flag` by fs [enable_stg_def,Abbr `s`] >>
  fs [WB_pipeline_def,Rel_def,WB_Rel_def]
QED

(** WB_dataA **)
Theorem agp32_Rel_ag32_WB_dataA_correct:
  !fext fbits a t I.
    is_sch_writeback I (agp32 fext fbits) ==>
    is_sch_disable I (agp32 fext fbits) ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (5,SUC t) <> NONE ==>
    (agp32 fext fbits (SUC t)).WB.WB_dataA = dataA (FUNPOW Next (THE (I (5,SUC t)) − 1) a)
Proof
  rw [] >> Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state] (fext t) s s` >>
  `(agp32 fext fbits (SUC t)).WB.WB_dataA = (WB_pipeline (fext t) s s').WB.WB_dataA`
    by fs [agp32_WB_dataA_updated_by_WB_pipeline] >> rw [] >>
  `(s'.WB.WB_state_flag = s.WB.WB_state_flag) /\ (s'.WB.WB_dataA = s.WB.WB_dataA)`
    by METIS_TAC [Abbr `s`,Abbr `s'`,agp32_same_WB_items_before_WB_pipeline] >>
  Cases_on `enable_stg 5 (agp32 fext fbits t)` >-
   (`I' (5,SUC t) = I' (4,t)` by fs [is_sch_writeback_def] >> fs [] >>
    `s'.WB.WB_state_flag` by fs [enable_stg_def,Abbr `s`] >>
    fs [WB_pipeline_def,Rel_def,MEM_Rel_def]) >>
  `I' (5,SUC t) = I' (5,t)` by fs [is_sch_disable_def] >>
  `~s'.WB.WB_state_flag` by fs [enable_stg_def,Abbr `s`] >>
  fs [WB_pipeline_def,Rel_def,WB_Rel_def]
QED

(** WB_imm **)
(** when opc is not 14w **)
Theorem agp32_Rel_ag32_WB_imm_correct_not_LoadUpperConstant:
  !fext fbits a t I.
    is_sch_writeback I (agp32 fext fbits) ==>
    is_sch_disable I (agp32 fext fbits) ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (5,SUC t) <> NONE ==>
    (agp32 fext fbits (SUC t)).WB.WB_opc <> 14w ==>
    (agp32 fext fbits (SUC t)).WB.WB_imm = imm (FUNPOW Next (THE (I (5,SUC t)) − 1) a)
Proof
  rw [] >> Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state] (fext t) s s` >>
  `(agp32 fext fbits (SUC t)).WB.WB_opc = (WB_pipeline (fext t) s s').WB.WB_opc`
    by fs [agp32_WB_opc_updated_by_WB_pipeline] >>
  `(agp32 fext fbits (SUC t)).WB.WB_imm = (WB_pipeline (fext t) s s').WB.WB_imm`
    by fs [agp32_WB_PC_imm_addrW_updated_by_WB_pipeline] >> fs [] >>
  `(s'.WB.WB_state_flag = s.WB.WB_state_flag) /\ (s'.WB.WB_imm = s.WB.WB_imm) /\
  (s'.WB.WB_opc = s.WB.WB_opc)`
    by METIS_TAC [Abbr `s`,Abbr `s'`,agp32_same_WB_items_before_WB_pipeline] >>
  `s'.MEM.MEM_imm = s.MEM.MEM_imm`
    by cheat >>
  Cases_on `enable_stg 5 (agp32 fext fbits t)` >-
   (`I' (5,SUC t) = I' (4,t)` by fs [is_sch_writeback_def] >> fs [] >>
    `s'.WB.WB_state_flag` by fs [enable_stg_def,Abbr `s`] >>
    fs [WB_pipeline_def,Rel_def,MEM_Rel_def]) >>
  `I' (5,SUC t) = I' (5,t)` by fs [is_sch_disable_def] >>
  `~s'.WB.WB_state_flag` by fs [enable_stg_def,Abbr `s`] >>
  fs [WB_pipeline_def,Rel_def,WB_Rel_def]
QED

(** when opc is 14w **)
Theorem agp32_Rel_ag32_WB_imm_correct_LoadUpperConstant:
  !fext fbits a t I.
    is_sch_writeback I (agp32 fext fbits) ==>
    is_sch_disable I (agp32 fext fbits) ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (5,SUC t) <> NONE ==>
    (agp32 fext fbits (SUC t)).WB.WB_opc = 14w ==>
    (agp32 fext fbits (SUC t)).WB.WB_imm =
    ((8 >< 0) (imm (FUNPOW Next (THE (I (5,SUC t)) − 1) a)) @@
     (22 >< 0) (dataW (FUNPOW Next (THE (I (5,SUC t)) − 1) a)))
Proof
  rw [] >> Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state] (fext t) s s` >>
  `(agp32 fext fbits (SUC t)).WB.WB_opc = (WB_pipeline (fext t) s s').WB.WB_opc`
    by fs [agp32_WB_opc_updated_by_WB_pipeline] >>
  `(agp32 fext fbits (SUC t)).WB.WB_imm = (WB_pipeline (fext t) s s').WB.WB_imm`
    by fs [agp32_WB_PC_imm_addrW_updated_by_WB_pipeline] >> fs [] >>
  `(s'.WB.WB_state_flag = s.WB.WB_state_flag) /\ (s'.WB.WB_imm = s.WB.WB_imm) /\
  (s'.WB.WB_opc = s.WB.WB_opc)`
    by METIS_TAC [Abbr `s`,Abbr `s'`,agp32_same_WB_items_before_WB_pipeline] >>
  `s'.MEM.MEM_imm = s.MEM.MEM_imm`
    by METIS_TAC [Abbr `s`,Abbr `s'`,agp32_same_MEM_items_before_WB_pipeline] >>
  Cases_on `enable_stg 5 (agp32 fext fbits t)` >-
   (`I' (5,SUC t) = I' (4,t)` by fs [is_sch_writeback_def] >> fs [] >>
    `s'.WB.WB_state_flag` by fs [enable_stg_def,Abbr `s`] >>
    fs [WB_pipeline_def,Rel_def,MEM_Rel_def]) >>
  `I' (5,SUC t) = I' (5,t)` by fs [is_sch_disable_def] >>
  `~s'.WB.WB_state_flag` by fs [enable_stg_def,Abbr `s`] >>
  fs [WB_pipeline_def,Rel_def,WB_Rel_def]
QED

(** WB_ALU_res **)
Theorem agp32_Rel_ag32_WB_ALU_res_correct:
  !fext fbits a t I.
    is_sch_writeback I (agp32 fext fbits) ==>
    is_sch_disable I (agp32 fext fbits) ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (5,SUC t) <> NONE ==>
    (agp32 fext fbits (SUC t)).WB.WB_ALU_res = ALU_res (FUNPOW Next (THE (I (5,SUC t)) − 1) a)
Proof
  rw [] >> Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state] (fext t) s s` >>
  `(agp32 fext fbits (SUC t)).WB.WB_ALU_res = (WB_pipeline (fext t) s s').WB.WB_ALU_res`
    by fs [agp32_WB_ALU_res_updated_by_WB_pipeline] >> rw [] >>
  `(s'.WB.WB_state_flag = s.WB.WB_state_flag) /\ (s'.WB.WB_ALU_res = s.WB.WB_ALU_res)`
    by METIS_TAC [Abbr `s`,Abbr `s'`,agp32_same_WB_items_before_WB_pipeline] >>
  Cases_on `enable_stg 5 (agp32 fext fbits t)` >-
   (`I' (5,SUC t) = I' (4,t)` by fs [is_sch_writeback_def] >> fs [] >>
    `s'.WB.WB_state_flag` by fs [enable_stg_def,Abbr `s`] >>
    fs [WB_pipeline_def,Rel_def,MEM_Rel_def]) >>
  `I' (5,SUC t) = I' (5,t)` by fs [is_sch_disable_def] >>
  `~s'.WB.WB_state_flag` by fs [enable_stg_def,Abbr `s`] >>
  fs [WB_pipeline_def,Rel_def,WB_Rel_def]
QED

(** WB_SHIFT_res **)
Theorem agp32_Rel_ag32_WB_SHIFT_res_correct:
  !fext fbits a t I.
    is_sch_writeback I (agp32 fext fbits) ==>
    is_sch_disable I (agp32 fext fbits) ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (5,SUC t) <> NONE ==>
    (agp32 fext fbits (SUC t)).WB.WB_opc = 1w ==>
    (agp32 fext fbits (SUC t)).WB.WB_SHIFT_res = shift_res (FUNPOW Next (THE (I (5,SUC t)) − 1) a)
Proof
  rw [] >> Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state] (fext t) s s` >>
  `(agp32 fext fbits (SUC t)).WB.WB_opc = (WB_pipeline (fext t) s s').WB.WB_opc`
    by fs [agp32_WB_opc_updated_by_WB_pipeline] >>
  `(agp32 fext fbits (SUC t)).WB.WB_SHIFT_res = (WB_pipeline (fext t) s s').WB.WB_SHIFT_res`
    by fs [agp32_WB_SHIFT_res_updated_by_WB_pipeline] >> fs [] >>
  `(s'.WB.WB_state_flag = s.WB.WB_state_flag) /\ (s'.WB.WB_SHIFT_res = s.WB.WB_SHIFT_res) /\
  (s'.WB.WB_opc = s.WB.WB_opc)`
    by METIS_TAC [Abbr `s`,Abbr `s'`,agp32_same_WB_items_before_WB_pipeline] >>
  Cases_on `enable_stg 5 (agp32 fext fbits t)` >-
   (`I' (5,SUC t) = I' (4,t)` by fs [is_sch_writeback_def] >> fs [] >>
    `s'.WB.WB_state_flag` by fs [enable_stg_def,Abbr `s`] >>
    fs [WB_pipeline_def,Rel_def,MEM_Rel_def]) >>
  `I' (5,SUC t) = I' (5,t)` by fs [is_sch_disable_def] >>
  `~s'.WB.WB_state_flag` by fs [enable_stg_def,Abbr `s`] >>
  fs [WB_pipeline_def,Rel_def,WB_Rel_def]
QED

(** WB_write_reg **)
Theorem agp32_Rel_ag32_WB_write_reg_correct:
  !fext fbits a t I.
    is_sch_writeback I (agp32 fext fbits) ==>
    is_sch_disable I (agp32 fext fbits) ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (5,SUC t) <> NONE ==>
    (agp32 fext fbits (SUC t)).WB.WB_write_reg = reg_iswrite (FUNPOW Next (THE (I (5,SUC t)) − 1) a)
Proof
  rw [] >> Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state] (fext t) s s` >>
  `(agp32 fext fbits (SUC t)).WB.WB_write_reg = (WB_pipeline (fext t) s s').WB.WB_write_reg`
    by fs [agp32_WB_write_reg_updated_by_WB_pipeline] >> fs [] >>
  `(s'.WB.WB_state_flag = s.WB.WB_state_flag) /\ (s'.WB.WB_write_reg = s.WB.WB_write_reg)`
    by METIS_TAC [Abbr `s`,Abbr `s'`,agp32_same_WB_items_before_WB_pipeline] >>
  `s'.MEM.MEM_opc = s.MEM.MEM_opc`
    by METIS_TAC [Abbr `s`,Abbr `s'`,agp32_same_MEM_items_before_WB_pipeline] >>
  Cases_on `enable_stg 5 (agp32 fext fbits t)` >-
   (`I' (5,SUC t) = I' (4,t)` by fs [is_sch_writeback_def] >> fs [] >>
    `s'.WB.WB_state_flag` by fs [enable_stg_def,Abbr `s`] >>
    fs [WB_pipeline_def,Rel_def,MEM_Rel_def,reg_iswrite_def]) >>
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
  rw [WB_Rel_def,is_sch_def] >>
  fs [agp32_Rel_ag32_WB_PC_correct,agp32_Rel_ag32_WB_addrW_correct,agp32_Rel_ag32_WB_opc_correct,
      agp32_Rel_ag32_WB_dataA_correct,agp32_Rel_ag32_WB_imm_correct_not_LoadUpperConstant,
      agp32_Rel_ag32_WB_imm_correct_LoadUpperConstant,agp32_Rel_ag32_WB_ALU_res_correct,
      agp32_Rel_ag32_WB_SHIFT_res_correct,agp32_Rel_ag32_WB_write_reg_correct] >>
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
