open hardwarePreamble translatorTheory arithmeticTheory dep_rewrite blastLib bitstringSyntax fcpSyntax listSyntax wordsSyntax wordsLib ag32ExtraTheory agp32StateTheory agp32EnvironmentTheory agp32ProcessorTheory agp32RelationTheory agp32UpdateTheory agp32UpdateLib;

val _ = new_theory "agp32Internal";

val _ = prefer_num ();
val _ = guess_lengths ();

(** self-defined tactics **)
val check_hazard_ctrl =
 (fs [Hazard_ctrl_def] >>
  Cases_on `s'.state = 1w \/ s'.state = 2w \/ s'.state = 3w \/
            s'.state = 4w \/ s'.state = 5w` >> fs [] >>
  Cases_on `(fext t).ready` >> fs [] >>
  Cases_on `s.MEM.MEM_opc = 2w \/ s.MEM.MEM_opc = 3w \/ s.MEM.MEM_opc = 4w \/
            s.MEM.MEM_opc = 5w \/ s.MEM.MEM_opc = 8w \/ s.MEM.MEM_opc = 12w` >> fs [] >>
  Cases_on `s'.EX.EX_jump_sel` >> fs [] >>
  Cases_on `s'.EX.EX_checkA \/ s'.EX.EX_checkB \/ s'.EX.EX_checkW \/
            s'.MEM.MEM_checkA \/ s'.MEM.MEM_checkB \/ s'.MEM.MEM_checkW \/
            s'.WB.WB_checkA \/ s'.WB.WB_checkB \/ s'.WB.WB_checkW` >> fs []);
                                                                                
val rw_hazard_ctrl_checks_init =
  (clist_update_state_tac >>
   fs [Abbr `s14`,Hazard_ctrl_def] >>
   Cases_on `s13.state = 1w \/ s13.state = 2w \/ s13.state = 3w \/
             s13.state = 4w \/ s13.state = 5w` >> fs [] >>
   Cases_on `(fext 0).ready` >> fs [] >>
   Cases_on `(agp32_init fbits).MEM.MEM_opc = 2w \/ (agp32_init fbits).MEM.MEM_opc = 3w \/
             (agp32_init fbits).MEM.MEM_opc = 4w \/ (agp32_init fbits).MEM.MEM_opc = 5w \/      
             (agp32_init fbits).MEM.MEM_opc = 8w \/ (agp32_init fbits).MEM.MEM_opc = 12w` >> fs [] >>
   Cases_on `s13.EX.EX_jump_sel` >> fs [] >>
   Cases_on `s13.EX.EX_checkA \/ s13.EX.EX_checkB \/ s13.EX.EX_checkW \/
             s13.MEM.MEM_checkA \/ s13.MEM.MEM_checkB \/ s13.MEM.MEM_checkW \/   
             s13.WB.WB_checkA \/ s13.WB.WB_checkB \/ s13.WB.WB_checkW` >> fs []);
                                                             
val rw_hazard_ctrl_checks_regular =
 (qpat_abbrev_tac `s' = mk_circuit (procs _) (procs _) (agp32_init fbits) fext t` >>
  qpat_abbrev_tac `s'' = procs _ (fext t) s' s'` >>
  clist_update_state_tac >>
  fs [Abbr `s14`,Hazard_ctrl_def] >>
  Cases_on `s13.state = 1w \/ s13.state = 2w \/ s13.state = 3w \/
            s13.state = 4w \/ s13.state = 5w` >> fs [] >>
  Cases_on `(fext (SUC n)).ready` >> fs [] >>       
  Cases_on `s''.MEM.MEM_opc = 2w \/ s''.MEM.MEM_opc = 3w \/ s''.MEM.MEM_opc = 4w \/
            s''.MEM.MEM_opc = 8w \/ s''.MEM.MEM_opc = 5w \/ s''.MEM.MEM_opc = 12w` >> fs [] >>
  Cases_on `s13.EX.EX_jump_sel` >> fs [] >>
  Cases_on `s13.EX.EX_checkA \/ s13.EX.EX_checkB \/ s13.EX.EX_checkW \/
            s13.MEM.MEM_checkA \/ s13.MEM.MEM_checkB \/ s13.MEM.MEM_checkW \/   
            s13.WB.WB_checkA \/ s13.WB.WB_checkB \/ s13.WB.WB_checkW` >> fs []);

(** option from the ISA functions  **)
Theorem isJump_isa_op_not_none:
  !nop a.
    isJump_isa_op nop a ==> nop <> NONE
Proof
  rw [isJump_isa_op_def]
QED


(* internal relation between opc and func *)
(** ID stage **)
Theorem agp32_ID_opc_implies_ID_func:
  !fext fbits t.
    (agp32 fext fbits t).ID.ID_opc <> 0w ==>
    (agp32 fext fbits t).ID.ID_opc <> 6w ==>
    (agp32 fext fbits t).ID.ID_opc <> 9w ==>
    (agp32 fext fbits t).ID.ID_opc <> 10w ==>
    (agp32 fext fbits t).ID.ID_opc <> 11w ==>
    (agp32 fext fbits t).ID.ID_func = 9w \/
    (agp32 fext fbits t).ID.ID_func = 12w \/
    (agp32 fext fbits t).ID.ID_func = 13w \/
    (agp32 fext fbits t).ID.ID_func = 14w \/ 
    (agp32 fext fbits t).ID.ID_func = 15w
Proof
  rw [] >>
  `?s s'. ((agp32 fext fbits t).ID.ID_opc = (ID_opc_func_update (fext t) s s').ID.ID_opc) /\
  ((agp32 fext fbits t).ID.ID_func = (ID_opc_func_update (fext t) s s').ID.ID_func)`
    by rw [agp32_ID_opc_func_exists_ID_opc_func_update] >> fs [] >>
  Cases_on `word_bit 24 s'.ID.ID_instr` >-
   (Cases_on `word_bit 31 s'.ID.ID_instr` >-
     fs [ID_opc_func_update_def] >>
    Cases_on `(23 >< 9) s'.ID.ID_instr = 0w` >>
    fs [ID_opc_func_update_def]) >>
  Cases_on `(5 >< 0) s'.ID.ID_instr = 10w` >-
   fs  [ID_opc_func_update_def] >>
  Cases_on `(5 >< 0) s'.ID.ID_instr = 11w` >-
   fs  [ID_opc_func_update_def] >>
  Cases_on `(5 >< 0) s'.ID.ID_instr = 12w` >-
   fs  [ID_opc_func_update_def] >>
  Cases_on `word_bit 31 s'.ID.ID_instr` >-
   fs [ID_opc_func_update_def] >>
  Cases_on `(5 >< 0) s'.ID.ID_instr <+ 10w` >-
   (fs [ID_opc_func_update_def] >>
    Cases_on `(5 >< 0) s'.ID.ID_instr = 0w \/ (5 >< 0) s'.ID.ID_instr = 6w \/
              (5 >< 0) s'.ID.ID_instr = 9w` >> fs [] >>
    Cases_on `(5 >< 0) s'.ID.ID_instr = 1w` >> fs [] >>
    Cases_on_word_value `(7 >< 6) s'.ID.ID_instr` >> rw []) >>
  fs [ID_opc_func_update_def]
QED

(** relation between ID addr_disable imm and data singals **)
Theorem agp32_ID_addrA_disable_dataA_immA:
  !fext fbits t.
    (agp32 fext fbits (SUC t)).ID.ID_addrA_disable ==>
    (agp32 fext fbits (SUC t)).ID.ID_dataA = (agp32 fext fbits (SUC t)).ID.ID_immA
Proof
  rw [] >> Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state;WB_pipeline;MEM_pipeline;EX_pipeline;
                            REG_write;ID_pipeline;IF_PC_update;Acc_compute] (fext t) s s` >>
  Q.ABBREV_TAC `s'' = procs [IF_instr_update;ID_opc_func_update;ID_imm_update] (fext (SUC t)) s' s'` >>
  `((agp32 fext fbits (SUC t)).ID.ID_addrA_disable <=>
  (ID_data_update (fext (SUC t)) s' s'').ID.ID_addrA_disable) /\
  ((agp32 fext fbits (SUC t)).ID.ID_immA = (ID_data_update (fext (SUC t)) s' s'').ID.ID_immA) /\
  ((agp32 fext fbits (SUC t)).ID.ID_dataA = (ID_data_update (fext (SUC t)) s' s'').ID.ID_dataA)`
    by fs [Abbr `s`,Abbr `s'`,Abbr `s''`,agp32_ID_flag_updated_by_ID_data_update,
           agp32_ID_imm_data_updated_by_ID_data_update,agp32_ID_data_updated_by_ID_data_update] >>
  fs [ID_data_update_def,MUX_21_def]
QED

Theorem agp32_ID_addrB_disable_dataB_immB:
  !fext fbits t.
    (agp32 fext fbits (SUC t)).ID.ID_addrB_disable ==>
    (agp32 fext fbits (SUC t)).ID.ID_dataB = (agp32 fext fbits (SUC t)).ID.ID_immB
Proof
  rw [] >> Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state;WB_pipeline;MEM_pipeline;EX_pipeline;
                            REG_write;ID_pipeline;IF_PC_update;Acc_compute] (fext t) s s` >>
  Q.ABBREV_TAC `s'' = procs [IF_instr_update;ID_opc_func_update;ID_imm_update] (fext (SUC t)) s' s'` >>
  `((agp32 fext fbits (SUC t)).ID.ID_addrB_disable <=>
  (ID_data_update (fext (SUC t)) s' s'').ID.ID_addrB_disable) /\
  ((agp32 fext fbits (SUC t)).ID.ID_immB = (ID_data_update (fext (SUC t)) s' s'').ID.ID_immB) /\
  ((agp32 fext fbits (SUC t)).ID.ID_dataB = (ID_data_update (fext (SUC t)) s' s'').ID.ID_dataB)`
    by fs [Abbr `s`,Abbr `s'`,Abbr `s''`,agp32_ID_flag_updated_by_ID_data_update,
           agp32_ID_imm_data_updated_by_ID_data_update,agp32_ID_data_updated_by_ID_data_update] >>
  fs [ID_data_update_def,MUX_21_def]
QED

Theorem agp32_ID_addrW_disable_dataW_immW:
  !fext fbits t.
    (agp32 fext fbits (SUC t)).ID.ID_addrW_disable ==>
    (agp32 fext fbits (SUC t)).ID.ID_dataW = (agp32 fext fbits (SUC t)).ID.ID_immW
Proof
  rw [] >> Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state;WB_pipeline;MEM_pipeline;EX_pipeline;
                            REG_write;ID_pipeline;IF_PC_update;Acc_compute] (fext t) s s` >>
  Q.ABBREV_TAC `s'' = procs [IF_instr_update;ID_opc_func_update;ID_imm_update] (fext (SUC t)) s' s'` >>
  `((agp32 fext fbits (SUC t)).ID.ID_addrW_disable <=>
  (ID_data_update (fext (SUC t)) s' s'').ID.ID_addrW_disable) /\
  ((agp32 fext fbits (SUC t)).ID.ID_immW = (ID_data_update (fext (SUC t)) s' s'').ID.ID_immW) /\
  ((agp32 fext fbits (SUC t)).ID.ID_dataW = (ID_data_update (fext (SUC t)) s' s'').ID.ID_dataW)`
    by fs [Abbr `s`,Abbr `s'`,Abbr `s''`,agp32_ID_flag_updated_by_ID_data_update,
           agp32_ID_imm_data_updated_by_ID_data_update,agp32_ID_data_updated_by_ID_data_update] >>
  fs [ID_data_update_def,MUX_21_def]
QED

(** relation between ID addr_disable data_updated and data singals **)
Theorem agp32_ID_addrA_enable_dataA_read_dataA:
  !fext fbits t.
    ~(agp32 fext fbits (SUC t)).ID.ID_addrA_disable ==>
    (agp32 fext fbits (SUC t)).ID.ID_dataA = (agp32 fext fbits (SUC t)).ID.ID_read_dataA
Proof
  rw [] >> Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state;WB_pipeline;MEM_pipeline;EX_pipeline;
                            REG_write;ID_pipeline;IF_PC_update;Acc_compute] (fext t) s s` >>
  Q.ABBREV_TAC `s'' = procs [IF_instr_update;ID_opc_func_update;ID_imm_update] (fext (SUC t)) s' s'` >>
  `((agp32 fext fbits (SUC t)).ID.ID_addrA_disable <=>
    (ID_data_update (fext (SUC t)) s' s'').ID.ID_addrA_disable) /\
  ((agp32 fext fbits (SUC t)).ID.ID_read_dataA =
   (ID_data_update (fext (SUC t)) s' s'').ID.ID_read_dataA) /\
  ((agp32 fext fbits (SUC t)).ID.ID_dataA = (ID_data_update (fext (SUC t)) s' s'').ID.ID_dataA)`
    by fs [Abbr `s`,Abbr `s'`,Abbr `s''`,agp32_ID_flag_updated_by_ID_data_update,
           agp32_ID_read_data_updated_by_ID_data_update,
           agp32_ID_data_updated_by_ID_data_update] >>
  fs [ID_data_update_def,MUX_21_def]
QED

Theorem agp32_ID_addrB_enable_dataB_read_dataB:
  !fext fbits t.
    ~(agp32 fext fbits (SUC t)).ID.ID_addrB_disable ==>
    (agp32 fext fbits (SUC t)).ID.ID_dataB = (agp32 fext fbits (SUC t)).ID.ID_read_dataB
Proof
  rw [] >> Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state;WB_pipeline;MEM_pipeline;EX_pipeline;
                            REG_write;ID_pipeline;IF_PC_update;Acc_compute] (fext t) s s` >>
  Q.ABBREV_TAC `s'' = procs [IF_instr_update;ID_opc_func_update;ID_imm_update] (fext (SUC t)) s' s'` >>
  `((agp32 fext fbits (SUC t)).ID.ID_addrB_disable <=>
    (ID_data_update (fext (SUC t)) s' s'').ID.ID_addrB_disable) /\
  ((agp32 fext fbits (SUC t)).ID.ID_read_dataB =
   (ID_data_update (fext (SUC t)) s' s'').ID.ID_read_dataB) /\
  ((agp32 fext fbits (SUC t)).ID.ID_dataB = (ID_data_update (fext (SUC t)) s' s'').ID.ID_dataB)`
    by fs [Abbr `s`,Abbr `s'`,Abbr `s''`,agp32_ID_flag_updated_by_ID_data_update,
           agp32_ID_read_data_updated_by_ID_data_update,
           agp32_ID_data_updated_by_ID_data_update] >>
  fs [ID_data_update_def,MUX_21_def]
QED

Theorem agp32_ID_addrW_enable_dataW_read_dataW:
  !fext fbits t.
    ~(agp32 fext fbits (SUC t)).ID.ID_addrW_disable ==>
    (agp32 fext fbits (SUC t)).ID.ID_dataW = (agp32 fext fbits (SUC t)).ID.ID_read_dataW
Proof
  rw [] >> Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state;WB_pipeline;MEM_pipeline;EX_pipeline;
                            REG_write;ID_pipeline;IF_PC_update;Acc_compute] (fext t) s s` >>
  Q.ABBREV_TAC `s'' = procs [IF_instr_update;ID_opc_func_update;ID_imm_update] (fext (SUC t)) s' s'` >>
  `((agp32 fext fbits (SUC t)).ID.ID_addrW_disable <=>
    (ID_data_update (fext (SUC t)) s' s'').ID.ID_addrW_disable) /\
  ((agp32 fext fbits (SUC t)).ID.ID_read_dataW =
   (ID_data_update (fext (SUC t)) s' s'').ID.ID_read_dataW) /\
  ((agp32 fext fbits (SUC t)).ID.ID_dataW = (ID_data_update (fext (SUC t)) s' s'').ID.ID_dataW)`
    by fs [Abbr `s`,Abbr `s'`,Abbr `s''`,agp32_ID_flag_updated_by_ID_data_update,
           agp32_ID_read_data_updated_by_ID_data_update,
           agp32_ID_data_updated_by_ID_data_update] >>
  fs [ID_data_update_def,MUX_21_def]
QED


(** EX stage **)
Theorem agp32_EX_opc_implies_EX_func:
  !fext fbits t.
    enable_stg 3 (agp32 fext fbits t) ==>
    (agp32 fext fbits (SUC t)).EX.EX_opc <> 0w ==>
    (agp32 fext fbits (SUC t)).EX.EX_opc <> 6w ==>
    (agp32 fext fbits (SUC t)).EX.EX_opc <> 9w ==>
    (agp32 fext fbits (SUC t)).EX.EX_opc <> 10w ==>
    (agp32 fext fbits (SUC t)).EX.EX_opc <> 11w ==>
    (agp32 fext fbits (SUC t)).EX.EX_func = 9w \/
    (agp32 fext fbits (SUC t)).EX.EX_func = 12w \/
    (agp32 fext fbits (SUC t)).EX.EX_func = 13w \/
    (agp32 fext fbits (SUC t)).EX.EX_func = 14w \/ 
    (agp32 fext fbits (SUC t)).EX.EX_func = 15w
Proof
  rw [enable_stg_def] >>
  Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state;WB_pipeline;MEM_pipeline] (fext t) s s` >>
  `(agp32 fext fbits (SUC t)).EX.EX_opc = (EX_pipeline (fext t) s s').EX.EX_opc /\
  (agp32 fext fbits (SUC t)).EX.EX_func = (EX_pipeline (fext t) s s').EX.EX_func`
    by fs [agp32_EX_opc_func_updated_by_EX_pipeline] >>
  `s'.ID.ID_EX_write_enable = s.ID.ID_EX_write_enable`
    by METIS_TAC [Abbr `s`,Abbr `s'`,agp32_same_items_until_MEM_pipeline] >>
  fs [EX_pipeline_def] >>
  Cases_on `s.ID.ID_EX_write_enable` >> fs [] >>
  `s'.ID.ID_func = s.ID.ID_func /\ s'.ID.ID_opc = s.ID.ID_opc`
    by METIS_TAC [Abbr `s`,Abbr `s'`,agp32_same_items_until_MEM_pipeline] >>
  METIS_TAC [agp32_ID_opc_implies_ID_func]
QED

(** if the EX stage is disabled, then EX_opc is unchanged at the next cycle **)
Theorem agp32_EX_opc_unchanged_when_EX_disabled:
  !fext fbits t.
    ~enable_stg 3 (agp32 fext fbits t) ==>
    (agp32 fext fbits (SUC t)).EX.EX_opc = (agp32 fext fbits t).EX.EX_opc
Proof
  rw [enable_stg_def] >>
  Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state;WB_pipeline;MEM_pipeline] (fext t) s s` >>
  `(agp32 fext fbits (SUC t)).EX.EX_opc = (EX_pipeline (fext t) s s').EX.EX_opc`
    by fs [agp32_EX_opc_func_updated_by_EX_pipeline] >>
  `s'.ID.ID_EX_write_enable = s.ID.ID_EX_write_enable`
    by METIS_TAC [Abbr `s`,Abbr `s'`,agp32_same_items_until_MEM_pipeline] >>
  fs [EX_pipeline_def] >>
  qpat_x_assum `(agp32 fext fbits (SUC t)).EX.EX_opc = _` (fn thm => all_tac) >>
  fs [Abbr `s'`] >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `ss1 = agp32_next_state _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `ss2 = WB_pipeline _ _ _` >>
  rw [procs_def] >>
  qpat_abbrev_tac `ss3 = MEM_pipeline _ _ _` >>
  fs [Abbr `ss3`,Abbr `ss2`,Abbr `ss1`,
      MEM_pipeline_unchanged_EX_pipeline_items,
      WB_pipeline_unchanged_EX_pipeline_items,
      agp32_next_state_unchanged_EX_pipeline_items]
QED

(** when EX is enabled and EX_NOP_flag is true, EX_opc is flushed **)
Theorem agp32_EX_opc_flush_when_EX_NOP_flag:
  !fext fbits t.
    enable_stg 3 (agp32 fext fbits t) ==>
    (agp32 fext fbits t).EX.EX_NOP_flag ==>
    (agp32 fext fbits (SUC t)).EX.EX_opc = 16w
Proof
  rw [enable_stg_def] >>
  Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state;WB_pipeline;MEM_pipeline] (fext t) s s` >>
  `(agp32 fext fbits (SUC t)).EX.EX_opc = (EX_pipeline (fext t) s s').EX.EX_opc`
    by fs [agp32_EX_opc_func_updated_by_EX_pipeline] >>
  `(s'.ID.ID_EX_write_enable = s.ID.ID_EX_write_enable) /\
  (s'.EX.EX_NOP_flag = s.EX.EX_NOP_flag)`
    by METIS_TAC [Abbr `s`,Abbr `s'`,agp32_same_items_until_MEM_pipeline] >>
  fs [EX_pipeline_def]
QED

(** if the EX stage is disabled, then EX_write_reg is unchanged at the next cycle **)
Theorem agp32_EX_write_reg_unchanged_when_EX_disabled:
  !fext fbits t.
    ~enable_stg 3 (agp32 fext fbits t) ==>
    (agp32 fext fbits (SUC t)).EX.EX_write_reg = (agp32 fext fbits t).EX.EX_write_reg
Proof
  rw [enable_stg_def] >>
  Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state;WB_pipeline;MEM_pipeline] (fext t) s s` >>
  `(agp32 fext fbits (SUC t)).EX.EX_write_reg = (EX_pipeline (fext t) s s').EX.EX_write_reg`
    by fs [agp32_EX_write_reg_updated_by_EX_pipeline] >>
  `s'.ID.ID_EX_write_enable = s.ID.ID_EX_write_enable`
    by METIS_TAC [Abbr `s`,Abbr `s'`,agp32_same_items_until_MEM_pipeline] >>
  fs [EX_pipeline_def] >>
  qpat_x_assum `(agp32 fext fbits (SUC t)).EX.EX_write_reg = _` (fn thm => all_tac) >>
  fs [Abbr `s'`] >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `ss1 = agp32_next_state _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `ss2 = WB_pipeline _ _ _` >>
  rw [procs_def] >>
  qpat_abbrev_tac `ss3 = MEM_pipeline _ _ _` >>
  fs [Abbr `ss3`,Abbr `ss2`,Abbr `ss1`,
      MEM_pipeline_unchanged_EX_pipeline_items,
      WB_pipeline_unchanged_EX_pipeline_items,
      agp32_next_state_unchanged_EX_pipeline_items]
QED

(** when EX is enabled and EX_NOP_flag is true, EX_write_reg is F **)
Theorem agp32_EX_write_reg_F_when_EX_NOP_flag:
  !fext fbits t.
    enable_stg 3 (agp32 fext fbits t) ==>
    (agp32 fext fbits t).EX.EX_NOP_flag ==>
    ~(agp32 fext fbits (SUC t)).EX.EX_write_reg
Proof
  rw [enable_stg_def] >>
  Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state;WB_pipeline;MEM_pipeline] (fext t) s s` >>
  `(agp32 fext fbits (SUC t)).EX.EX_write_reg = (EX_pipeline (fext t) s s').EX.EX_write_reg`
    by fs [agp32_EX_write_reg_updated_by_EX_pipeline] >>
  `(s'.ID.ID_EX_write_enable = s.ID.ID_EX_write_enable) /\
  (s'.EX.EX_NOP_flag = s.EX.EX_NOP_flag)`
    by METIS_TAC [Abbr `s`,Abbr `s'`,agp32_same_items_until_MEM_pipeline] >>
  fs [EX_pipeline_def]
QED


(** pipeline control flags **)
(** IF_PC_write_enable **)
(** IF_PC_write_enable and ID_ID_write_enable **)
Theorem agp32_IF_PC_write_enable_and_ID_ID_write_enable:
  !fext fbits t.
    (agp32 fext fbits t).IF.IF_PC_write_enable =
    (agp32 fext fbits t).ID.ID_ID_write_enable
Proof
  rw [] >>
  `?s s'.
  ((agp32 fext fbits t).IF.IF_PC_write_enable <=> (Hazard_ctrl (fext t) s s').IF.IF_PC_write_enable) /\
  ((agp32 fext fbits t).ID.ID_ID_write_enable <=> (Hazard_ctrl (fext t) s s').ID.ID_ID_write_enable)`
    by METIS_TAC [agp32_ctrl_flags_exists_Hazard_ctrl] >>
  check_hazard_ctrl
QED

(* IF_PC_write_enable and ID_EX_write_enable *)
Theorem agp32_IF_PC_write_enable_and_ID_EX_write_enable:
  !fext fbits t.
    (agp32 fext fbits t).IF.IF_PC_write_enable ==>
    (agp32 fext fbits t).ID.ID_EX_write_enable
Proof
  rw [] >>
  `?s s'.
  ((agp32 fext fbits t).IF.IF_PC_write_enable <=> (Hazard_ctrl (fext t) s s').IF.IF_PC_write_enable) /\
  ((agp32 fext fbits t).ID.ID_EX_write_enable <=> (Hazard_ctrl (fext t) s s').ID.ID_EX_write_enable)`
    by METIS_TAC [agp32_ctrl_flags_exists_Hazard_ctrl] >> fs [] >>
  check_hazard_ctrl
QED

(* IF_PC_write_enable and MEM_state_flag *)
Theorem agp32_IF_PC_write_enable_and_MEM_flag:
  !fext fbits t.
    (agp32 fext fbits t).IF.IF_PC_write_enable ==>
    (agp32 fext fbits t).MEM.MEM_state_flag
Proof
  rw [] >>
  `?s s'.
  ((agp32 fext fbits t).IF.IF_PC_write_enable <=> (Hazard_ctrl (fext t) s s').IF.IF_PC_write_enable) /\
  ((agp32 fext fbits t).MEM.MEM_state_flag <=> (Hazard_ctrl (fext t) s s').MEM.MEM_state_flag)`
    by METIS_TAC [agp32_ctrl_flags_exists_Hazard_ctrl] >> fs [] >>
  check_hazard_ctrl
QED

(* IF_PC_write_enable and WB_state_flag *)
Theorem agp32_IF_PC_write_enable_and_WB_flag:
  !fext fbits t.
    (agp32 fext fbits t).IF.IF_PC_write_enable ==>
    (agp32 fext fbits t).WB.WB_state_flag
Proof
  rw [] >>
  `?s s'.
  ((agp32 fext fbits t).IF.IF_PC_write_enable <=> (Hazard_ctrl (fext t) s s').IF.IF_PC_write_enable) /\
  ((agp32 fext fbits t).WB.WB_state_flag <=> (Hazard_ctrl (fext t) s s').WB.WB_state_flag)`
    by METIS_TAC [agp32_ctrl_flags_exists_Hazard_ctrl] >> fs [] >>
  check_hazard_ctrl
QED

(** IF_PC_write_enable and fext t.ready **)
Theorem agp32_IF_PC_write_enable_and_fext_ready:
  !fext fbits t.
    (agp32 fext fbits t).IF.IF_PC_write_enable ==> (fext t).ready
Proof
  rw [] >>
  `?s s'.
  ((agp32 fext fbits t).IF.IF_PC_write_enable <=> (Hazard_ctrl (fext t) s s').IF.IF_PC_write_enable)`
    by METIS_TAC [agp32_ctrl_flags_exists_Hazard_ctrl] >> fs [] >>
  fs [Hazard_ctrl_def] >>
  Cases_on `s'.state = 1w \/ s'.state = 2w \/ s'.state = 3w \/
            s'.state = 4w \/ s'.state = 5w \/ s'.state = 6w` >> fs [] >>
  Cases_on `(fext t).ready` >> fs []
QED

Theorem not_fext_ready_and_agp32_IF_PC_write_disable:
  !fext fbits t.
    ~(fext t).ready ==> ~(agp32 fext fbits t).IF.IF_PC_write_enable
Proof
  rw [] >> METIS_TAC [agp32_IF_PC_write_enable_and_fext_ready]
QED

(** IF_PC_write_enable and state **)
Theorem agp32_IF_PC_write_enable_and_state:
  !fext fbits t.
    (agp32 fext fbits t).IF.IF_PC_write_enable ==>
    ((agp32 fext fbits t).state <> 1w) /\
    ((agp32 fext fbits t).state <> 2w) /\
    ((agp32 fext fbits t).state <> 3w) /\
    ((agp32 fext fbits t).state <> 4w) /\
    ((agp32 fext fbits t).state <> 5w)
Proof
  rpt gen_tac >> strip_tac >> Cases_on `t` >>
  fs [agp32_def,mk_module_def,mk_circuit_def] >-
   rw_hazard_ctrl_checks_init >>
  rw_hazard_ctrl_checks_regular
QED

(** IF_PC_write_enable and not a jump, then there is no reg_data_hazard **)
Theorem agp32_IF_PC_write_enable_EX_jump_sel_then_no_reg_data_hazard:
  !fext fbits t.
    (agp32 fext fbits t).IF.IF_PC_write_enable ==>
    ~(agp32 fext fbits t).EX.EX_jump_sel ==>
    ~reg_data_hazard (agp32 fext fbits t)
Proof
  rw [] >> Cases_on `t` >>
  fs [agp32_def,mk_module_def,mk_circuit_def,reg_data_hazard_def] >-
   rw_hazard_ctrl_checks_init >>
  rw_hazard_ctrl_checks_regular
QED

(* ID_ID_write_enable *)
(** ID_ID_write_enable and ID_EX_write_enable **)
Theorem agp32_ID_ID_write_enable_and_ID_EX_write_enable:
  !fext fbits t.
    (agp32 fext fbits t).ID.ID_ID_write_enable ==>
    (agp32 fext fbits t).ID.ID_EX_write_enable
Proof
  rw [agp32_IF_PC_write_enable_and_ID_ID_write_enable,
      agp32_IF_PC_write_enable_and_ID_EX_write_enable]
QED

(** ID_ID_write_enable and fext t.ready **)
Theorem agp32_ID_ID_write_enable_and_fext_ready:
  !fext fbits t.
    (agp32 fext fbits t).ID.ID_ID_write_enable ==>
    (fext t).ready
Proof
  rw [GSYM agp32_IF_PC_write_enable_and_ID_ID_write_enable] >>
  METIS_TAC [agp32_IF_PC_write_enable_and_fext_ready]
QED

(** ID_ID_write_enable and MEM_state_flag **)
Theorem agp32_ID_ID_write_enable_MEM_state_flag:
  !fext fbits t.
    (agp32 fext fbits t).ID.ID_ID_write_enable ==>
    (agp32 fext fbits t).MEM.MEM_state_flag
Proof
  rw [GSYM agp32_IF_PC_write_enable_and_ID_ID_write_enable] >>
  METIS_TAC [agp32_IF_PC_write_enable_and_MEM_flag]
QED

(** ID_ID_write_enable and WB_state_flag **)
Theorem agp32_ID_ID_write_enable_WB_state_flag:
  !fext fbits t.
    (agp32 fext fbits t).ID.ID_ID_write_enable ==>
    (agp32 fext fbits t).WB.WB_state_flag
Proof
  rw [GSYM agp32_IF_PC_write_enable_and_ID_ID_write_enable] >>
  METIS_TAC [agp32_IF_PC_write_enable_and_WB_flag]
QED

(** ID_ID_write_enable and ID_flush_flag, then there is a jump **)
Theorem agp32_ID_ID_write_enable_flush_flag_then_EX_jump_sel:
  !fext fbits t.
    (agp32 fext fbits t).ID.ID_ID_write_enable ==>
    (agp32 fext fbits t).ID.ID_flush_flag ==>
    (agp32 fext fbits t).EX.EX_jump_sel
Proof
  rpt GEN_TAC >> STRIP_TAC >> Cases_on `t` >>
  fs [agp32_def,mk_module_def,mk_circuit_def] >-
   rw_hazard_ctrl_checks_init >>
  rw_hazard_ctrl_checks_regular
QED

(** ID_ID_write_enable and not a jump, then there is no reg_data_hazard **)
Theorem agp32_ID_ID_write_enable_EX_jump_sel_then_no_reg_data_hazard:
  !fext fbits t.
    (agp32 fext fbits t).ID.ID_ID_write_enable ==>
    ~(agp32 fext fbits t).EX.EX_jump_sel ==>
    ~reg_data_hazard (agp32 fext fbits t)
Proof
  rw [] >> METIS_TAC [agp32_IF_PC_write_enable_and_ID_ID_write_enable,
                      agp32_IF_PC_write_enable_EX_jump_sel_then_no_reg_data_hazard]
QED

(** reg_data_hazard and not a jump, then ID_ID_write_enable is disabled  **)
Theorem agp32_not_EX_jump_sel_reg_data_hazard_then_ID_ID_write_disable:
  !fext fbits t.
    ~(agp32 fext fbits t).EX.EX_jump_sel ==>
    reg_data_hazard (agp32 fext fbits t) ==>
    ~(agp32 fext fbits t).ID.ID_ID_write_enable
Proof
  rw [] >> METIS_TAC [agp32_ID_ID_write_enable_EX_jump_sel_then_no_reg_data_hazard]
QED


(** ID_EX_write_enable **)
(** ID_EX_write_enable and MEM_state_flag **)
Theorem agp32_ID_EX_write_enable_MEM_state_flag:
  !fext fbits t.
    (agp32 fext fbits t).ID.ID_EX_write_enable ==>
    (agp32 fext fbits t).MEM.MEM_state_flag
Proof
  rw [] >>
  `?s s'.
  ((agp32 fext fbits t).ID.ID_EX_write_enable <=> (Hazard_ctrl (fext t) s s').ID.ID_EX_write_enable) /\
  ((agp32 fext fbits t).MEM.MEM_state_flag <=> (Hazard_ctrl (fext t) s s').MEM.MEM_state_flag)`
    by METIS_TAC [agp32_ctrl_flags_exists_Hazard_ctrl] >> fs [] >>
  check_hazard_ctrl
QED

Theorem agp32_MEM_state_flag_F_and_ID_EX_write_disable:
  !fext fbits t.
    ~(agp32 fext fbits t).MEM.MEM_state_flag ==>
    ~(agp32 fext fbits t).ID.ID_EX_write_enable
Proof
  rw [] >> METIS_TAC [agp32_ID_EX_write_enable_MEM_state_flag]
QED

(** ID_EX_write_enable and WB_state_flag **)
Theorem agp32_ID_EX_write_enable_WB_state_flag:
  !fext fbits t.
    (agp32 fext fbits t).ID.ID_EX_write_enable ==>
    (agp32 fext fbits t).WB.WB_state_flag
Proof
  rw [] >>
  `?s s'.
  ((agp32 fext fbits t).ID.ID_EX_write_enable <=> (Hazard_ctrl (fext t) s s').ID.ID_EX_write_enable) /\
  ((agp32 fext fbits t).WB.WB_state_flag <=> (Hazard_ctrl (fext t) s s').WB.WB_state_flag)`
    by METIS_TAC [agp32_ctrl_flags_exists_Hazard_ctrl] >> fs [] >>
  check_hazard_ctrl
QED

(** ID_EX_write_enable and MEM_opc **)
Theorem agp32_ID_EX_write_enable_no_MEM_stg_op:
  !fext fbits t.
    (agp32 fext fbits t).ID.ID_EX_write_enable ==>
    ~isMemOp_hw_op (agp32 fext fbits t)
Proof
  rw [] >> Cases_on `t` >>
  fs [agp32_def,mk_module_def,mk_circuit_def,isMemOp_hw_op_def] >-
   (clist_update_state_tac >>
    fs [Abbr `s14`,Hazard_ctrl_def] >>
    Cases_on `s13.state = 1w \/ s13.state = 2w \/ s13.state = 3w \/
              s13.state = 4w \/ s13.state = 5w` >> fs [] >>
    Cases_on `(fext 0).ready` >> fs [] >>
    Cases_on `(agp32_init fbits).MEM.MEM_opc = 2w \/ (agp32_init fbits).MEM.MEM_opc = 3w \/
              (agp32_init fbits).MEM.MEM_opc = 4w \/ (agp32_init fbits).MEM.MEM_opc = 5w \/      
              (agp32_init fbits).MEM.MEM_opc = 8w \/ (agp32_init fbits).MEM.MEM_opc = 12w` >> fs [] >>
    Cases_on `s13.EX.EX_jump_sel` >> fs [] >>
    Cases_on `s13.EX.EX_checkA \/ s13.EX.EX_checkB \/ s13.EX.EX_checkW \/
              s13.MEM.MEM_checkA \/ s13.MEM.MEM_checkB \/ s13.MEM.MEM_checkW \/   
              s13.WB.WB_checkA \/ s13.WB.WB_checkB \/ s13.WB.WB_checkW` >> fs [] >>
    fs [Abbr `s13`,Abbr `s12`,Abbr `s11`,Abbr `s10`,Abbr `s9`,Abbr `s8`,Abbr `s7`,
        Abbr `s6`,Abbr `s5`,Abbr `s4`,Abbr `s3`,Abbr `s2`,Abbr `s1`,
        WB_update_unchanged_MEM_pipeline_items,
        MEM_ctrl_update_unchanged_MEM_pipeline_items,
        IF_PC_input_update_unchanged_MEM_pipeline_items,
        EX_jump_sel_addr_update_unchanged_MEM_pipeline_items,
        EX_SHIFT_update_unchanged_MEM_pipeline_items,EX_ALU_update_unchanged_MEM_pipeline_items,
        EX_ALU_input_imm_update_unchanged_MEM_pipeline_items,
        EX_ctrl_update_unchanged_MEM_pipeline_items,
        ID_data_check_update_unchanged_MEM_pipeline_items,
        ID_data_update_unchanged_MEM_pipeline_items,ID_imm_update_unchanged_MEM_pipeline_items,
        ID_opc_func_update_unchanged_MEM_pipeline_items,
        IF_instr_update_unchanged_MEM_pipeline_items]) >>
  qpat_abbrev_tac `s' = mk_circuit (procs _) (procs _) (agp32_init fbits) fext t` >>
  qpat_abbrev_tac `s'' = procs _ (fext t) s' s'` >>
  clist_update_state_tac >>
  fs [Abbr `s14`,Hazard_ctrl_def] >>
  Cases_on `s13.state = 1w \/ s13.state = 2w \/ s13.state = 3w \/
            s13.state = 4w \/ s13.state = 5w` >> fs [] >>
  Cases_on `(fext (SUC n)).ready` >> fs [] >>
  Cases_on `s''.MEM.MEM_opc = 2w \/ s''.MEM.MEM_opc = 3w \/ s''.MEM.MEM_opc = 4w \/
            s''.MEM.MEM_opc = 8w \/ s''.MEM.MEM_opc = 5w \/ s''.MEM.MEM_opc = 12w` >> fs [] >> fs [] >>
  Cases_on `s13.EX.EX_jump_sel` >> fs [] >>
  Cases_on `s13.EX.EX_checkA \/ s13.EX.EX_checkB \/ s13.EX.EX_checkW \/
              s13.MEM.MEM_checkA \/ s13.MEM.MEM_checkB \/ s13.MEM.MEM_checkW \/   
              s13.WB.WB_checkA \/ s13.WB.WB_checkB \/ s13.WB.WB_checkW` >> fs [] >>       
  fs [Abbr `s13`,Abbr `s12`,Abbr `s11`,Abbr `s10`,Abbr `s9`,Abbr `s8`,Abbr `s7`,
      Abbr `s6`,Abbr `s5`,Abbr `s4`,Abbr `s3`,Abbr `s2`,Abbr `s1`,
      WB_update_unchanged_MEM_pipeline_items,
      MEM_ctrl_update_unchanged_MEM_pipeline_items,
      IF_PC_input_update_unchanged_MEM_pipeline_items,
      EX_jump_sel_addr_update_unchanged_MEM_pipeline_items,
      EX_SHIFT_update_unchanged_MEM_pipeline_items,EX_ALU_update_unchanged_MEM_pipeline_items,
      EX_ALU_input_imm_update_unchanged_MEM_pipeline_items,
      EX_ctrl_update_unchanged_MEM_pipeline_items,
      ID_data_check_update_unchanged_MEM_pipeline_items,
      ID_data_update_unchanged_MEM_pipeline_items,ID_imm_update_unchanged_MEM_pipeline_items,
      ID_opc_func_update_unchanged_MEM_pipeline_items,
      IF_instr_update_unchanged_MEM_pipeline_items]
QED

Theorem MEM_stg_op_agp32_ID_EX_write_disable:
  !fext fbits t.
    isMemOp_hw_op (agp32 fext fbits t) ==>
    ~(agp32 fext fbits t).ID.ID_EX_write_enable
Proof
  rw [] >> METIS_TAC [agp32_ID_EX_write_enable_no_MEM_stg_op]
QED

(** ID_EX_write_enable, jump singal and EX_NOP_flag **)
Theorem agp32_ID_EX_write_enable_isJump_hw_op_EX_NOP_flag:
  !fext fbits t.
    (agp32 fext fbits t).ID.ID_EX_write_enable ==>
    isJump_hw_op (agp32 fext fbits t) ==>
    (agp32 fext fbits t).EX.EX_NOP_flag
Proof
  rw [isJump_hw_op_def] >> Cases_on `t` >>
  fs [agp32_def,mk_module_def,mk_circuit_def] >-
   rw_hazard_ctrl_checks_init >>
  rw_hazard_ctrl_checks_regular
QED

(** ID_EX_write_enable, jump singal and EX_NOP_flag **)
Theorem agp32_ID_EX_write_enable_reg_data_hazard_EX_NOP_flag:
  !fext fbits t.
    (agp32 fext fbits t).ID.ID_EX_write_enable ==>
    reg_data_hazard (agp32 fext fbits t) ==>
    (agp32 fext fbits t).EX.EX_NOP_flag
Proof
  rw [] >> Cases_on `t` >>
  fs [agp32_def,mk_module_def,mk_circuit_def] >-
   (rw_hazard_ctrl_checks_init >> fs [reg_data_hazard_def]) >>
  rw_hazard_ctrl_checks_regular >> fs [reg_data_hazard_def]
QED

(** IF_PC_write_enable, ID_EX_write_enable and reg_data_hazard **)
Theorem agp32_IF_PC_write_disable_ID_EX_write_enable_reg_data_hazard:
  !fext fbits t.
    ~(agp32 fext fbits t).IF.IF_PC_write_enable ==>
    (agp32 fext fbits t).ID.ID_EX_write_enable ==>
    reg_data_hazard (agp32 fext fbits t)
Proof
  rw [] >> Cases_on `t` >>
  fs [agp32_def,mk_module_def,mk_circuit_def,reg_data_hazard_def] >-
   rw_hazard_ctrl_checks_init >>
  rw_hazard_ctrl_checks_regular
QED

Theorem agp32_ID_ID_write_disable_ID_EX_write_enable_reg_data_hazard:
  !fext fbits t.
    ~(agp32 fext fbits t).ID.ID_ID_write_enable ==>
    (agp32 fext fbits t).ID.ID_EX_write_enable ==>
    reg_data_hazard (agp32 fext fbits t)
Proof
  rw [] >>
  METIS_TAC [agp32_IF_PC_write_enable_and_ID_ID_write_enable,
             agp32_IF_PC_write_disable_ID_EX_write_enable_reg_data_hazard]
QED

(* MEM_state_flag *)
(** MEM_state_flag and WB_state_flag **)
Theorem agp32_MEM_state_flag_eq_WB_state_flag:
  !fext fbits t.
    (agp32 fext fbits t).MEM.MEM_state_flag = (agp32 fext fbits t).WB.WB_state_flag
Proof
  rw [] >>
  `?s s'.
  ((agp32 fext fbits t).MEM.MEM_state_flag <=> (Hazard_ctrl (fext t) s s').MEM.MEM_state_flag) /\
  ((agp32 fext fbits t).WB.WB_state_flag <=> (Hazard_ctrl (fext t) s s').WB.WB_state_flag)`
    by METIS_TAC [agp32_ctrl_flags_exists_Hazard_ctrl] >>
  check_hazard_ctrl
QED

(** ID_EX_write_enable, MEM_state_flag and MEM_opc **)
Theorem agp32_ID_EX_write_disable_MEM_state_enable_MEM_stg_op:
  !fext fbits t.
    ~(agp32 fext fbits t).ID.ID_EX_write_enable ==>
    (agp32 fext fbits t).MEM.MEM_state_flag ==>
    isMemOp_hw_op (agp32 fext fbits t)
Proof
  rw [] >> Cases_on `t` >>
  fs [agp32_def,mk_module_def,mk_circuit_def,isMemOp_hw_op_def] >-
   (clist_update_state_tac >>
    fs [Abbr `s14`,Hazard_ctrl_def] >>
    Cases_on `s13.state = 1w \/ s13.state = 2w \/ s13.state = 3w \/
              s13.state = 4w \/ s13.state = 5w` >> fs [] >>
    Cases_on `(fext 0).ready` >> fs [] >>
    Cases_on `(agp32_init fbits).MEM.MEM_opc = 2w \/ (agp32_init fbits).MEM.MEM_opc = 3w \/
              (agp32_init fbits).MEM.MEM_opc = 4w \/ (agp32_init fbits).MEM.MEM_opc = 5w \/      
              (agp32_init fbits).MEM.MEM_opc = 8w \/ (agp32_init fbits).MEM.MEM_opc = 12w` >> fs [] >>
    Cases_on `s13.EX.EX_jump_sel` >> fs [] >>
    Cases_on `s13.EX.EX_checkA \/ s13.EX.EX_checkB \/ s13.EX.EX_checkW \/
              s13.MEM.MEM_checkA \/ s13.MEM.MEM_checkB \/ s13.MEM.MEM_checkW \/   
              s13.WB.WB_checkA \/ s13.WB.WB_checkB \/ s13.WB.WB_checkW` >> fs [] >>
    fs [Abbr `s13`,Abbr `s12`,Abbr `s11`,Abbr `s10`,Abbr `s9`,Abbr `s8`,Abbr `s7`,
        Abbr `s6`,Abbr `s5`,Abbr `s4`,Abbr `s3`,Abbr `s2`,Abbr `s1`,
        WB_update_unchanged_MEM_pipeline_items,
        MEM_ctrl_update_unchanged_MEM_pipeline_items,
        IF_PC_input_update_unchanged_MEM_pipeline_items,
        EX_jump_sel_addr_update_unchanged_MEM_pipeline_items,
        EX_SHIFT_update_unchanged_MEM_pipeline_items,EX_ALU_update_unchanged_MEM_pipeline_items,
        EX_ALU_input_imm_update_unchanged_MEM_pipeline_items,
        EX_ctrl_update_unchanged_MEM_pipeline_items,
        ID_data_check_update_unchanged_MEM_pipeline_items,
        ID_data_update_unchanged_MEM_pipeline_items,ID_imm_update_unchanged_MEM_pipeline_items,
        ID_opc_func_update_unchanged_MEM_pipeline_items,
        IF_instr_update_unchanged_MEM_pipeline_items]) >>
  qpat_abbrev_tac `s' = mk_circuit (procs _) (procs _) (agp32_init fbits) fext t` >>
  qpat_abbrev_tac `s'' = procs _ (fext t) s' s'` >>
  clist_update_state_tac >>
  fs [Abbr `s14`,Hazard_ctrl_def] >>
  Cases_on `s13.state = 1w \/ s13.state = 2w \/ s13.state = 3w \/
            s13.state = 4w \/ s13.state = 5w` >> fs [] >>
  Cases_on `(fext (SUC n)).ready` >> fs [] >>
  Cases_on `s''.MEM.MEM_opc = 2w \/ s''.MEM.MEM_opc = 3w \/ s''.MEM.MEM_opc = 4w \/
            s''.MEM.MEM_opc = 8w \/ s''.MEM.MEM_opc = 5w \/ s''.MEM.MEM_opc = 12w` >> fs [] >> fs [] >>
  Cases_on `s13.EX.EX_jump_sel` >> fs [] >>
  Cases_on `s13.EX.EX_checkA \/ s13.EX.EX_checkB \/ s13.EX.EX_checkW \/
              s13.MEM.MEM_checkA \/ s13.MEM.MEM_checkB \/ s13.MEM.MEM_checkW \/   
              s13.WB.WB_checkA \/ s13.WB.WB_checkB \/ s13.WB.WB_checkW` >> fs [] >>       
  fs [Abbr `s13`,Abbr `s12`,Abbr `s11`,Abbr `s10`,Abbr `s9`,Abbr `s8`,Abbr `s7`,
      Abbr `s6`,Abbr `s5`,Abbr `s4`,Abbr `s3`,Abbr `s2`,Abbr `s1`,
      WB_update_unchanged_MEM_pipeline_items,
      MEM_ctrl_update_unchanged_MEM_pipeline_items,
      IF_PC_input_update_unchanged_MEM_pipeline_items,
      EX_jump_sel_addr_update_unchanged_MEM_pipeline_items,
      EX_SHIFT_update_unchanged_MEM_pipeline_items,EX_ALU_update_unchanged_MEM_pipeline_items,
      EX_ALU_input_imm_update_unchanged_MEM_pipeline_items,
      EX_ctrl_update_unchanged_MEM_pipeline_items,
      ID_data_check_update_unchanged_MEM_pipeline_items,
      ID_data_update_unchanged_MEM_pipeline_items,ID_imm_update_unchanged_MEM_pipeline_items,
      ID_opc_func_update_unchanged_MEM_pipeline_items,
      IF_instr_update_unchanged_MEM_pipeline_items]
QED


(* initial values *)
(** initial EX_PC_sel = 0w **)
Theorem agp32_init_EX_PC_sel:
  !fext fbits.
    (agp32 fext fbits 0).EX.EX_PC_sel = 0w
Proof
  rw [agp32_def,mk_module_def,mk_circuit_def] >>
  clist_update_state_tac >>
  fs [Abbr `s14`,Abbr `s13`,Abbr `s12`,Abbr `s11`,Abbr `s10`,
      Abbr `s9`,Abbr `s8`,Abbr `s7`,Abbr `s6`,
      Hazard_ctrl_unchanged_EX_ctrl_items,
      WB_update_unchanged_EX_ctrl_items,
      MEM_ctrl_update_unchanged_EX_ctrl_items,
      IF_PC_input_update_unchanged_EX_ctrl_items,
      EX_jump_sel_addr_update_unchanged_EX_ctrl_items,
      EX_SHIFT_update_unchanged_EX_ctrl_items,EX_ALU_update_unchanged_EX_ctrl_items,
      EX_ALU_input_imm_update_unchanged_EX_ctrl_items] >>
  Cases_on `s5.ID.ID_EX_write_enable` >-
   fs [EX_ctrl_update_def,agp32_init_def] >>
  rw [EX_ctrl_update_def] >>      
  fs [Abbr `s5`,Abbr `s4`,Abbr `s3`,Abbr `s2`,Abbr `s1`,
      ID_data_check_update_unchanged_EX_ctrl_items,
      ID_data_update_unchanged_EX_ctrl_items,
      ID_imm_update_unchanged_EX_ctrl_items,
      ID_opc_func_update_unchanged_EX_ctrl_items,
      IF_instr_update_unchanged_EX_ctrl_items] >>
   rw [agp32_init_def]
QED

(** initial EX_jump_sel is F **)
Theorem agp32_init_EX_jump_sel:
  !fext fbits.
    ~(agp32 fext fbits 0).EX.EX_jump_sel
Proof
  rw [] >> `(agp32 fext fbits 0).EX.EX_PC_sel = 0w` by rw [agp32_init_EX_PC_sel] >>
  fs [agp32_def,mk_module_def,mk_circuit_def] >>
  clist_update_state_tac >>
  fs [Abbr `s14`,Abbr `s13`,Abbr `s12`,Abbr `s11`,Abbr `s10`,
      Hazard_ctrl_unchanged_EX_jump,Hazard_ctrl_unchanged_EX_ctrl_items,
      WB_update_unchanged_EX_jump,WB_update_unchanged_EX_ctrl_items,
      MEM_ctrl_update_unchanged_EX_jump,MEM_ctrl_update_unchanged_EX_ctrl_items,
      IF_PC_input_update_unchanged_EX_jump,IF_PC_input_update_unchanged_EX_ctrl_items,
      EX_jump_sel_addr_update_unchanged_EX_ctrl_items] >>
  rw [EX_jump_sel_addr_update_def]
QED

(** initial EX_opc **)
Theorem agp32_init_EX_opc:
  !fext fbits.
    (agp32 fext fbits 0).EX.EX_opc = 16w
Proof
  rw [agp32_def,mk_module_def,mk_circuit_def] >>
  clist_update_state_tac >>
  fs [Abbr `s14`,Abbr `s13`,Abbr `s12`,Abbr `s11`,Abbr `s10`,Abbr `s9`,Abbr `s8`,
      Abbr `s7`,Abbr `s6`,Abbr `s5`,Abbr `s4`,Abbr `s3`,Abbr `s2`,Abbr `s1`,
      Hazard_ctrl_unchanged_EX_pipeline_items,WB_update_unchanged_EX_pipeline_items,
      MEM_ctrl_update_unchanged_EX_pipeline_items,IF_PC_input_update_unchanged_EX_pipeline_items,
      EX_jump_sel_addr_update_unchanged_EX_pipeline_items,EX_SHIFT_update_unchanged_EX_pipeline_items,
      EX_ALU_update_unchanged_EX_pipeline_items,EX_ALU_input_imm_update_unchanged_EX_pipeline_items,
      EX_ctrl_update_unchanged_EX_pipeline_items,ID_data_check_update_unchanged_EX_pipeline_items,
      ID_data_update_unchanged_EX_pipeline_items,ID_imm_update_unchanged_EX_pipeline_items,
      ID_opc_func_update_unchanged_EX_pipeline_items,IF_instr_update_unchanged_EX_pipeline_items] >>
  rw [agp32_init_def]
QED

(** initial EX_write_reg is F **)
Theorem agp32_init_EX_write_reg:
  !fext fbits.
    ~(agp32 fext fbits 0).EX.EX_write_reg
Proof
  rw [agp32_def,mk_module_def,mk_circuit_def] >>
  clist_update_state_tac >>
  fs [Abbr `s14`,Abbr `s13`,Abbr `s12`,Abbr `s11`,Abbr `s10`,Abbr `s9`,Abbr `s8`,
      Abbr `s7`,Abbr `s6`,Abbr `s5`,Abbr `s4`,Abbr `s3`,Abbr `s2`,Abbr `s1`,
      Hazard_ctrl_unchanged_EX_pipeline_items,WB_update_unchanged_EX_pipeline_items,
      MEM_ctrl_update_unchanged_EX_pipeline_items,IF_PC_input_update_unchanged_EX_pipeline_items,
      EX_jump_sel_addr_update_unchanged_EX_pipeline_items,EX_SHIFT_update_unchanged_EX_pipeline_items,
      EX_ALU_update_unchanged_EX_pipeline_items,EX_ALU_input_imm_update_unchanged_EX_pipeline_items,
      EX_ctrl_update_unchanged_EX_pipeline_items,ID_data_check_update_unchanged_EX_pipeline_items,
      ID_data_update_unchanged_EX_pipeline_items,ID_imm_update_unchanged_EX_pipeline_items,
      ID_opc_func_update_unchanged_EX_pipeline_items,IF_instr_update_unchanged_EX_pipeline_items] >>
  rw [agp32_init_def]
QED

(** initial IF_PC_input = PC + 4w **)
Theorem agp32_init_IF_PC_input:
  !fext fbits.
    (agp32 fext fbits 0).IF.IF_PC_input = (agp32 fext fbits 0).PC + 4w
Proof
  rw [] >> `~(agp32 fext fbits 0).EX.EX_jump_sel` by rw [agp32_init_EX_jump_sel] >>
  fs [agp32_def,mk_module_def,mk_circuit_def] >>
  clist_update_state_tac >>
  fs [Abbr `s14`,Abbr `s13`,Abbr `s12`,Abbr `s11`,
      Hazard_ctrl_unchanged_IF,Hazard_ctrl_unchanged_EX_jump,
      WB_update_unchanged_IF,WB_update_unchanged_EX_jump,
      MEM_ctrl_update_unchanged_IF,MEM_ctrl_update_unchanged_EX_jump] >>
  fs [IF_PC_input_update_def,MUX_21_def] >>
  fs [Abbr `s10`,Abbr `s9`,Abbr `s8`,Abbr `s7`,Abbr `s6`,
      Abbr `s5`,Abbr `s4`,Abbr `s3`,Abbr `s2`,Abbr `s1`,
      EX_jump_sel_addr_update_unchanged_IF,EX_SHIFT_update_unchanged_IF,
      EX_ALU_update_unchanged_IF,EX_ALU_input_imm_update_unchanged_IF,
      EX_ctrl_update_unchanged_IF,ID_data_check_update_unchanged_IF,
      ID_data_update_unchanged_IF,ID_imm_update_unchanged_IF,
      ID_opc_func_update_unchanged_IF,IF_instr_update_unchanged_IF]
QED

(** initial command is 0 **)
Theorem agp32_init_command_0w:
  !fext fbits.
    (agp32 fext fbits 0).command = 0w
Proof
  rw [agp32_def,mk_module_def,mk_circuit_def] >>
  clist_update_state_tac >>
  fs [Abbr `s14`,Abbr `s13`,Abbr `s12`,Abbr `s11`,Abbr `s10`,Abbr `s9`,Abbr `s8`,
      Abbr `s7`,Abbr `s6`,Abbr `s5`,Abbr `s4`,Abbr `s3`,Abbr `s2`,Abbr `s1`,
      Hazard_ctrl_unchanged_state_items,WB_update_unchanged_state_items,
      MEM_ctrl_update_unchanged_state_items,IF_PC_input_update_unchanged_state_items,
      EX_jump_sel_addr_update_unchanged_state_items,EX_SHIFT_update_unchanged_state_items,
      EX_ALU_update_unchanged_state_items,EX_ALU_input_imm_update_unchanged_state_items,
      EX_ctrl_update_unchanged_state_items,ID_data_check_update_unchanged_state_items,
      ID_data_update_unchanged_state_items,ID_imm_update_unchanged_state_items,
      ID_opc_func_update_unchanged_state_items,IF_instr_update_unchanged_state_items] >>
  rw [agp32_init_def]
QED

(** initial state is 3 **)
Theorem agp32_init_state_3w:
  !fext fbits.
    (agp32 fext fbits 0).state = 3w
Proof
  rw [agp32_def,mk_module_def,mk_circuit_def] >>
  clist_update_state_tac >>
  fs [Abbr `s14`,Abbr `s13`,Abbr `s12`,Abbr `s11`,Abbr `s10`,Abbr `s9`,Abbr `s8`,
      Abbr `s7`,Abbr `s6`,Abbr `s5`,Abbr `s4`,Abbr `s3`,Abbr `s2`,Abbr `s1`,
      Hazard_ctrl_unchanged_state_items,WB_update_unchanged_state_items,
      MEM_ctrl_update_unchanged_state_items,IF_PC_input_update_unchanged_state_items,
      EX_jump_sel_addr_update_unchanged_state_items,EX_SHIFT_update_unchanged_state_items,
      EX_ALU_update_unchanged_state_items,EX_ALU_input_imm_update_unchanged_state_items,
      EX_ctrl_update_unchanged_state_items,ID_data_check_update_unchanged_state_items,
      ID_data_update_unchanged_state_items,ID_imm_update_unchanged_state_items,
      ID_opc_func_update_unchanged_state_items,IF_instr_update_unchanged_state_items] >>
  rw [agp32_init_def]
QED


(* command is not possible for values 5/6/7 *)
Theorem agp32_command_impossible_values:
  !fext fbits t.
    ((agp32 fext fbits t).command <> 5w) /\
    ((agp32 fext fbits t).command <> 6w) /\
    ((agp32 fext fbits t).command <> 7w)
Proof
  rpt GEN_TAC >>
  Induct_on `t` >-
   rw [agp32_init_command_0w] >> 
  Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  `(agp32 fext fbits (SUC t)).command = (agp32_next_state (fext t) s s).command`
    by fs [agp32_command_state_updated_by_agp32_next_state,Abbr `s`] >>
  rw [agp32_next_state_def] >>
  Cases_on_word_value `(1 >< 0) s.MEM.MEM_dataB` >> fs []
QED

(* state is not possible for values 6 and 7 *)
Theorem agp32_state_impossible_values:
  !fext fbits t.
    ((agp32 fext fbits t).state <> 6w) /\
    ((agp32 fext fbits t).state <> 7w)
Proof
  rpt GEN_TAC >>
  Induct_on `t` >-
   rw [agp32_init_state_3w] >> 
  Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  `(agp32 fext fbits (SUC t)).state = (agp32_next_state (fext t) s s).state`
    by fs [agp32_command_state_updated_by_agp32_next_state,Abbr `s`] >>
  rw [agp32_next_state_def] >>
  Cases_on_word_value `(1 >< 0) s.MEM.MEM_dataB` >> fs []
QED


(* lemmas about the scheduling function I *)
(** false ID instr only flushed when jump happened in the EX stage
Theorem ID_instr_index_NONE_opc_flush:
  !I t fext fbits a.
    is_sch I (agp32 fext fbits) a ==>
    I (2,t) = NONE ==>
    (agp32 fext fbits t).ID.ID_opc = 15w
Proof
  cheat
QED
 **)

(** NONE happened **)
Theorem EX_instr_index_NONE_opc_flush:
  !I t fext fbits a.
    is_sch I (agp32 fext fbits) a ==>
    I (3,t) = NONE ==>
    (agp32 fext fbits t).EX.EX_opc = 16w
Proof
  rw [is_sch_def] >>
  Induct_on `t` >>
  rw [agp32_init_EX_opc] >>
  Cases_on `enable_stg 3 (agp32 fext fbits t)` >-
   (Cases_on `isJump_hw_op (agp32 fext fbits t)` >-
     (`(agp32 fext fbits t).EX.EX_NOP_flag`
        by fs [enable_stg_def,agp32_ID_EX_write_enable_isJump_hw_op_EX_NOP_flag] >>
      fs [agp32_EX_opc_flush_when_EX_NOP_flag]) >>
    Cases_on `reg_data_hazard (agp32 fext fbits t)` >-
     (`(agp32 fext fbits t).EX.EX_NOP_flag`
        by fs [enable_stg_def,agp32_ID_EX_write_enable_reg_data_hazard_EX_NOP_flag] >>
      fs [agp32_EX_opc_flush_when_EX_NOP_flag]) >>
    `I' (3,SUC t) = I' (2,t)` by METIS_TAC [is_sch_execute_def] >> fs [] >>
    cheat) >>
  `I' (3,SUC t) = I' (3,t)` by METIS_TAC [is_sch_disable_def] >>
  fs [agp32_EX_opc_unchanged_when_EX_disabled]
QED

Theorem EX_instr_index_NONE_EX_not_write_reg:
  !I t fext fbits a.
    is_sch I (agp32 fext fbits) a ==>
    I (3,t) = NONE ==>
    ~(agp32 fext fbits t).EX.EX_write_reg
Proof
  rw [is_sch_def] >>
  Induct_on `t` >-
  rw [agp32_init_EX_write_reg] >> rw [] >>
  Cases_on `enable_stg 3 (agp32 fext fbits t)` >-
   (Cases_on `isJump_hw_op (agp32 fext fbits t)` >-
     (`(agp32 fext fbits t).EX.EX_NOP_flag`
        by fs [enable_stg_def,agp32_ID_EX_write_enable_isJump_hw_op_EX_NOP_flag] >>
      fs [agp32_EX_write_reg_F_when_EX_NOP_flag]) >>
    Cases_on `reg_data_hazard (agp32 fext fbits t)` >-
     (`(agp32 fext fbits t).EX.EX_NOP_flag`
        by fs [enable_stg_def,agp32_ID_EX_write_enable_reg_data_hazard_EX_NOP_flag] >>
      fs [agp32_EX_write_reg_F_when_EX_NOP_flag]) >>
    `I' (3,SUC t) = I' (2,t)` by METIS_TAC [is_sch_execute_def] >> fs [] >>
    cheat) >>
  `I' (3,SUC t) = I' (3,t)` by METIS_TAC [is_sch_disable_def] >>
  fs [agp32_EX_write_reg_unchanged_when_EX_disabled]
QED

(** instr index relation between IF and EX stages **)
Theorem IF_instr_index_with_ID_instr:
  !I t fext fbits a.
    is_sch I (agp32 fext fbits) a ==>
    I (1,t) <> NONE ==>
    I (2,t) <> NONE ==>
    (THE (I (1,t)) > THE (I (2,t))) /\ (THE (I (1,t)) < THE (I (2,t)) + 2)
Proof
  rpt gen_tac >> rpt disch_tac >>
  fs [is_sch_def] >>
  Induct_on `t` >-
   fs [is_sch_init_def] >>
  rpt disch_tac >>
  Cases_on `enable_stg 1 (agp32 fext fbits t)` >-
   (Cases_on `isJump_hw_op (agp32 fext fbits t)` >-
     (`enable_stg 2 (agp32 fext fbits t)`
        by fs [enable_stg_def,agp32_IF_PC_write_enable_and_ID_ID_write_enable] >>
      fs [is_sch_fetch_def,is_sch_decode_def] >> METIS_TAC []) >>
    Cases_on `isJump_isa_op (I' (1,t)) a \/ isJump_isa_op (I' (2,t)) a \/
    I' (1,t) = NONE \/ THE (I' (1,t)) = 0` >-
     (fs [is_sch_fetch_def] >> METIS_TAC []) >>
    `enable_stg 2 (agp32 fext fbits t)`
      by fs [enable_stg_def,agp32_IF_PC_write_enable_and_ID_ID_write_enable] >>
    fs [is_sch_fetch_def,is_sch_decode_def]) >>
  `~enable_stg 2 (agp32 fext fbits t)`
    by fs [enable_stg_def,agp32_IF_PC_write_enable_and_ID_ID_write_enable] >>
  fs [is_sch_disable_def] >> METIS_TAC []
QED

(** instr index relation between IF and EX stages **)
Theorem IF_instr_index_with_EX_instr:
  !I t fext fbits a.
    is_sch I (agp32 fext fbits) a ==>
    I (1,t) <> NONE ==>
    I (3,t) <> NONE ==>
    (THE (I (1,t)) > THE (I (3,t))) /\ (THE (I (1,t)) < THE (I (3,t)) + 3)
Proof
  rpt gen_tac >> rpt disch_tac >>
  Induct_on `t` >-
   fs [is_sch_def,is_sch_init_def] >>
  rpt disch_tac >>
  Cases_on `enable_stg 1 (agp32 fext fbits t)` >-
   (Cases_on `isJump_hw_op (agp32 fext fbits t)` >-
     (`enable_stg 3 (agp32 fext fbits t)`
        by fs [enable_stg_def,agp32_IF_PC_write_enable_and_ID_EX_write_enable] >>
      fs [is_sch_def,is_sch_fetch_def,is_sch_execute_def] >>
      METIS_TAC []) >>
    Cases_on `isJump_isa_op (I' (1,t)) a \/ isJump_isa_op (I' (2,t)) a \/
    I' (1,t) = NONE \/ THE (I' (1,t)) = 0` >-
     (fs [is_sch_def,is_sch_fetch_def,is_sch_execute_def] >> METIS_TAC []) >>
    fs [] >>
    `enable_stg 3 (agp32 fext fbits t)`
      by fs [enable_stg_def,agp32_IF_PC_write_enable_and_ID_EX_write_enable] >>
    Cases_on `reg_data_hazard (agp32 fext fbits t)` >-
     (fs [is_sch_def,is_sch_fetch_def,is_sch_execute_def] >> METIS_TAC []) >>
    `I' (3,SUC t) = I' (2,t)` by fs [is_sch_def,is_sch_execute_def] >> fs [] >>
    `(THE (I' (1,t)) > THE (I' (2,t))) /\ (THE (I' (1,t)) < THE (I' (2,t)) + 2)`
      by METIS_TAC [IF_instr_index_with_ID_instr] >> fs [is_sch_def,is_sch_fetch_def]) >>
  Cases_on `~enable_stg 3 (agp32 fext fbits t)` >-
   (fs [is_sch_def,is_sch_disable_def] >> METIS_TAC []) >> fs [] >>
  Cases_on `isJump_hw_op (agp32 fext fbits t)` >-
   (fs [is_sch_def,is_sch_execute_def] >> METIS_TAC []) >>
  `reg_data_hazard (agp32 fext fbits t)`
    by fs [enable_stg_def,agp32_IF_PC_write_disable_ID_EX_write_enable_reg_data_hazard] >>
  fs [is_sch_def,is_sch_execute_def] >> METIS_TAC []
QED

(** instr index relation between IF and MEM stages **)
Theorem IF_instr_index_with_MEM_instr:
  !I t fext fbits a.
    is_sch I (agp32 fext fbits) a ==>
    I (1,t) <> NONE ==>
    I (4,t) <> NONE ==>
    (THE (I (1,t)) > THE (I (4,t))) /\ (THE (I (1,t)) < THE (I (4,t)) + 4)
Proof
  rpt gen_tac >> rpt disch_tac >>
  Induct_on `t` >-
   fs [is_sch_def,is_sch_init_def] >>
  rpt disch_tac >>
  Cases_on `enable_stg 1 (agp32 fext fbits t)` >-
   (Cases_on `isJump_hw_op (agp32 fext fbits t)` >-
     (`enable_stg 4 (agp32 fext fbits t)`
        by fs [enable_stg_def,agp32_IF_PC_write_enable_and_MEM_flag] >>
      fs [is_sch_def,is_sch_fetch_def,is_sch_memory_def] >>
      Cases_on `isMemOp_hw_op (agp32 fext fbits t)` >> fs [] >>
      METIS_TAC []) >>
    Cases_on `isJump_isa_op (I' (1,t)) a \/ isJump_isa_op (I' (2,t)) a \/
    I' (1,t) = NONE \/ THE (I' (1,t)) = 0` >-
     (fs [is_sch_def,is_sch_fetch_def,is_sch_execute_def] >> METIS_TAC []) >>
    fs [] >>
    `enable_stg 4 (agp32 fext fbits t)`
      by fs [enable_stg_def,agp32_IF_PC_write_enable_and_MEM_flag] >>
    Cases_on `isMemOp_hw_op (agp32 fext fbits t)` >-
     (fs [is_sch_def,is_sch_memory_def] >> METIS_TAC []) >>
    `I' (4,SUC t) = I' (3,t)` by fs [is_sch_def,is_sch_memory_def] >> fs [] >>
    `(THE (I' (1,t)) > THE (I' (3,t))) /\ (THE (I' (1,t)) < THE (I' (3,t)) + 3)`
      by METIS_TAC [IF_instr_index_with_EX_instr] >> fs [is_sch_def,is_sch_fetch_def]) >>
  Cases_on `enable_stg 4 (agp32 fext fbits t)` >-
   (Cases_on `isMemOp_hw_op (agp32 fext fbits t)` >-
     (fs [is_sch_def,is_sch_memory_def] >> METIS_TAC []) >>
    `I' (4,SUC t) = I' (3,t)` by METIS_TAC [is_sch_def,is_sch_memory_def] >> fs [] >>
    `I' (1,SUC t) = I' (1,t)` by fs [is_sch_def,is_sch_disable_def] >> fs [] >>
    `(THE (I' (1,t)) > THE (I' (3,t))) /\ (THE (I' (1,t)) < THE (I' (3,t)) + 3)`
      by METIS_TAC [IF_instr_index_with_EX_instr] >> fs []) >>
  `I' (4,SUC t) = I' (4,t) /\ I' (1,SUC t) = I' (1,t)`
    by fs [is_sch_def,is_sch_disable_def] >> fs []
QED

(** instr index relation between ID and EX stages **)
Theorem ID_instr_index_with_EX_instr:
  !I t fext fbits a.
    is_sch I (agp32 fext fbits) a ==>
    I (2,t) <> NONE ==>
    I (3,t) <> NONE ==>
    (THE (I (2,t)) > THE (I (3,t))) /\ (THE (I (2,t)) < THE (I (3,t)) + 2)
Proof
  rpt gen_tac >> rpt disch_tac >>
  Induct_on `t` >-
   fs [is_sch_def,is_sch_init_def] >>
  rpt disch_tac >>
  Cases_on `enable_stg 2 (agp32 fext fbits t)` >-
   (Cases_on `isJump_isa_op (I' (2,t)) a \/ isJump_hw_op (agp32 fext fbits t)` >-
     (fs [is_sch_def,is_sch_decode_def] >> METIS_TAC []) >>
    `I' (2,SUC t) = I' (1,t)` by fs [is_sch_def,is_sch_decode_def] >>
    `enable_stg 3 (agp32 fext fbits t)`
      by fs [enable_stg_def,agp32_ID_ID_write_enable_and_ID_EX_write_enable] >>
    Cases_on `reg_data_hazard (agp32 fext fbits t)` >-
     (fs [is_sch_def,is_sch_fetch_def,is_sch_execute_def] >> METIS_TAC []) >>
    `I' (3,SUC t) = I' (2,t)` by fs [is_sch_def,is_sch_execute_def] >>
    METIS_TAC [IF_instr_index_with_ID_instr]) >>
  Cases_on `~enable_stg 3 (agp32 fext fbits t)` >> fs [] >-
   (fs [is_sch_def,is_sch_disable_def] >> METIS_TAC []) >>
  Cases_on `isJump_hw_op (agp32 fext fbits t)` >-
   (fs [is_sch_def,is_sch_execute_def] >> METIS_TAC []) >>
  `reg_data_hazard (agp32 fext fbits t)`
    by fs [enable_stg_def,agp32_ID_ID_write_disable_ID_EX_write_enable_reg_data_hazard] >>
  fs [is_sch_def,is_sch_execute_def] >> METIS_TAC []
QED

(** instr index relation between ID and MEM stages **)
Theorem ID_instr_index_with_MEM_instr:
  !I t fext fbits a.
    is_sch I (agp32 fext fbits) a ==>
    I (2,t) <> NONE ==>
    I (4,t) <> NONE ==>
    (THE (I (2,t)) > THE (I (4,t))) /\ (THE (I (2,t)) < THE (I (4,t)) + 3)
Proof
  rpt gen_tac >> rpt disch_tac >>
  Induct_on `t` >-
   fs [is_sch_def,is_sch_init_def] >>
  rpt disch_tac >>
  Cases_on `enable_stg 2 (agp32 fext fbits t)` >-
   (Cases_on `isJump_isa_op (I' (2,t)) a \/ isJump_hw_op (agp32 fext fbits t)` >-
     (fs [is_sch_def,is_sch_decode_def] >> METIS_TAC []) >>
    `I' (2,SUC t) = I' (1,t)` by fs [is_sch_def,is_sch_decode_def] >>
    `enable_stg 4 (agp32 fext fbits t)`
      by fs [enable_stg_def,agp32_ID_ID_write_enable_MEM_state_flag] >>
    Cases_on `isMemOp_hw_op (agp32 fext fbits t)` >-
     (fs [is_sch_def,is_sch_memory_def] >> METIS_TAC []) >>
    `I' (4,SUC t) = I' (3,t)` by fs [is_sch_def,is_sch_memory_def] >> fs [] >>
    METIS_TAC [IF_instr_index_with_EX_instr]) >>
  Cases_on `enable_stg 4 (agp32 fext fbits t)` >-
   (Cases_on `isMemOp_hw_op (agp32 fext fbits t)` >-
     (fs [is_sch_def,is_sch_memory_def] >> METIS_TAC []) >>
    `I' (2,SUC t) = I' (2,t) /\ I' (4,SUC t) = I' (3,t)`
      by fs [is_sch_def,is_sch_memory_def,is_sch_disable_def] >> fs [] >>
    `(THE (I' (2,t)) > THE (I' (3,t))) /\ (THE (I' (2,t)) < THE (I' (3,t)) + 2)`
      by METIS_TAC [ID_instr_index_with_EX_instr] >> fs []) >>
  fs [is_sch_def,is_sch_disable_def] >> METIS_TAC []
QED

(** instr index relation between ID and WB stages **)
Theorem ID_instr_index_with_WB_instr:
  !I t fext fbits a.
    is_sch I (agp32 fext fbits) a ==>
    I (2,t) <> NONE ==>
    I (5,t) <> NONE ==>
    (THE (I (2,t)) > THE (I (5,t))) /\ (THE (I (2,t)) < THE (I (5,t)) + 4)
Proof
  rpt gen_tac >> rpt disch_tac >>
  Induct_on `t` >-
   fs [is_sch_def,is_sch_init_def] >>
  rpt disch_tac >>
  Cases_on `enable_stg 2 (agp32 fext fbits t)` >-
   (Cases_on `isJump_isa_op (I' (2,t)) a \/ isJump_hw_op (agp32 fext fbits t)` >-
     (fs [is_sch_def,is_sch_decode_def] >> METIS_TAC []) >>
    `I' (2,SUC t) = I' (1,t)` by fs [is_sch_def,is_sch_decode_def] >>
    `enable_stg 5 (agp32 fext fbits t)`
      by fs [enable_stg_def,agp32_ID_ID_write_enable_WB_state_flag] >>
    `I' (5,SUC t) = I' (4,t)` by fs [is_sch_def,is_sch_writeback_def] >> fs [] >>
    METIS_TAC [IF_instr_index_with_MEM_instr]) >>
  Cases_on `enable_stg 5 (agp32 fext fbits t)` >-
   (`I' (2,SUC t) = I' (2,t) /\ I' (5,SUC t) = I' (4,t)`
      by fs [is_sch_def,is_sch_writeback_def,is_sch_disable_def] >> fs [] >>
    `(THE (I' (2,t)) > THE (I' (4,t))) /\ (THE (I' (2,t)) < THE (I' (4,t)) + 3)`
      by METIS_TAC [ID_instr_index_with_MEM_instr] >> fs []) >>
  fs [is_sch_def,is_sch_disable_def] >> METIS_TAC []
QED

(** instr index relation between EX and MEM stages **)
Theorem EX_instr_index_with_MEM_instr:
  !I t fext fbits a.
    is_sch I (agp32 fext fbits) a ==>
    I (3,t) <> NONE ==>
    I (4,t) <> NONE ==>
    (THE (I (3,t)) > THE (I (4,t))) /\ (THE (I (3,t)) < THE (I (4,t)) + 2)
Proof
  rpt gen_tac >> rpt disch_tac >>
  Induct_on `t` >-
   fs [is_sch_def,is_sch_init_def] >>
  rpt disch_tac >>
  Cases_on `enable_stg 3 (agp32 fext fbits t)` >-
   (Cases_on `isJump_hw_op (agp32 fext fbits t)` >-
     (fs [is_sch_def,is_sch_execute_def] >> METIS_TAC []) >>
    Cases_on `reg_data_hazard (agp32 fext fbits t)` >-
     (fs [is_sch_def,is_sch_execute_def] >> METIS_TAC []) >>
    `I' (3,SUC t) = I' (2,t)` by fs [is_sch_def,is_sch_execute_def] >> fs [] >>
    `enable_stg 4 (agp32 fext fbits t)`
      by fs [enable_stg_def,agp32_ID_EX_write_enable_MEM_state_flag] >>
    Cases_on `isMemOp_hw_op (agp32 fext fbits t)` >-
     (fs [is_sch_def,is_sch_memory_def] >> METIS_TAC []) >>
    `I' (4,SUC t) = I' (3,t)` by fs [is_sch_def,is_sch_memory_def] >> fs [] >>
    METIS_TAC [ID_instr_index_with_EX_instr]) >>
  Cases_on `enable_stg 4 (agp32 fext fbits t)` >>
  fs [is_sch_def,is_sch_disable_def] >-
   (Cases_on `isMemOp_hw_op (agp32 fext fbits t)` >-
     (fs [is_sch_memory_def] >> METIS_TAC []) >>
    fs [enable_stg_def] >> METIS_TAC [agp32_ID_EX_write_disable_MEM_state_enable_MEM_stg_op]) >>
  METIS_TAC []
QED

(** instr index relation between EX and WB stages **)
Theorem EX_instr_index_with_WB_instr:
  !I t fext fbits a.
    is_sch I (agp32 fext fbits) a ==>
    I (3,t) <> NONE ==>
    I (5,t) <> NONE ==>
    (THE (I (3,t)) > THE (I (5,t))) /\ (THE (I (3,t)) < THE (I (5,t)) + 3)
Proof
  rpt gen_tac >> rpt disch_tac >>
  Induct_on `t` >-
   fs [is_sch_def,is_sch_init_def] >>
  rpt disch_tac >>
  Cases_on `enable_stg 3 (agp32 fext fbits t)` >-
   (Cases_on `isJump_hw_op (agp32 fext fbits t)` >-
     (fs [is_sch_def,is_sch_execute_def] >> METIS_TAC []) >>
    Cases_on `reg_data_hazard (agp32 fext fbits t)` >-
     (fs [is_sch_def,is_sch_execute_def] >> METIS_TAC []) >>
    `I' (3,SUC t) = I' (2,t)` by fs [is_sch_def,is_sch_execute_def] >> fs [] >>
    `enable_stg 5 (agp32 fext fbits t)`
      by fs [enable_stg_def,agp32_ID_EX_write_enable_WB_state_flag] >>
    `I' (5,SUC t) = I' (4,t)` by fs [is_sch_def,is_sch_writeback_def] >> fs [] >>
    `(THE (I' (2,t)) > THE (I' (4,t))) /\ (THE (I' (2,t)) < THE (I' (4,t)) + 3)`
      by METIS_TAC [ID_instr_index_with_MEM_instr] >> fs []) >>
  Cases_on `enable_stg 5 (agp32 fext fbits t)` >-
  (`I' (3,SUC t) = I' (3,t) /\ I' (5,SUC t) = I' (4,t)`
     by fs [is_sch_def,is_sch_writeback_def,is_sch_disable_def] >> fs [] >>
   `(THE (I' (3,t)) > THE (I' (4,t))) /\ (THE (I' (3,t)) < THE (I' (4,t)) + 2)`
     by METIS_TAC [EX_instr_index_with_MEM_instr] >> fs []) >>
  `I' (3,SUC t) = I' (3,t) /\ I' (5,SUC t) = I' (5,t)`
    by fs [is_sch_def,is_sch_disable_def] >> fs []
QED

(** instr index relation between MEM and WB stages **)
Theorem MEM_instr_index_with_WB_instr:
  !I t fext fbits a.
    is_sch I (agp32 fext fbits) a ==>
    I (4,t) <> NONE ==>
    I (5,t) <> NONE ==>
    (THE (I (4,t)) > THE (I (5,t))) /\ (THE (I (4,t)) < THE (I (5,t)) + 2)
Proof
  rpt gen_tac >> rpt disch_tac >>
  Induct_on `t` >-
   fs [is_sch_def,is_sch_init_def] >>
  rpt disch_tac >>
  Cases_on `enable_stg 4 (agp32 fext fbits t)` >-
   (Cases_on `isMemOp_hw_op (agp32 fext fbits t)` >-
     (fs [is_sch_def,is_sch_memory_def] >> METIS_TAC []) >>
    `I' (4,SUC t) = I' (3,t)` by fs [is_sch_def,is_sch_memory_def] >> fs [] >>
    `enable_stg 4 (agp32 fext fbits t)`
      by fs [enable_stg_def,agp32_ID_EX_write_enable_MEM_state_flag] >>
    `enable_stg 5 (agp32 fext fbits t)`
      by fs [enable_stg_def,agp32_MEM_state_flag_eq_WB_state_flag] >>
    `I' (5,SUC t) = I' (4,t)` by fs [is_sch_def,is_sch_writeback_def] >> fs [] >>
    METIS_TAC [EX_instr_index_with_MEM_instr]) >>
  `~enable_stg 5 (agp32 fext fbits t)`
    by fs [enable_stg_def,agp32_MEM_state_flag_eq_WB_state_flag] >>
  fs [is_sch_def,is_sch_disable_def] >> METIS_TAC []
QED

(** I (1,t) = I (2,t) + 1 **)
Theorem IF_instr_index_with_ID_instr_plus_1:
  !I t fext fbits a.
    is_sch I (agp32 fext fbits) a ==>
    I (1,t) <> NONE ==>
    I (2,t) <> NONE ==>
    THE (I (1,t)) = THE (I (2,t)) + 1
Proof
  rw [] >>
  `(THE (I' (1,t)) > THE (I' (2,t))) /\ (THE (I' (1,t)) < THE (I' (2,t)) + 2)`
    by METIS_TAC [IF_instr_index_with_ID_instr] >> fs []
QED

(** I (2,t) = I (3,t) + 1 **)
Theorem ID_instr_index_with_EX_instr_plus_1:
  !I t fext fbits a.
    is_sch I (agp32 fext fbits) a ==>
    I (2,t) <> NONE ==>
    I (3,t) <> NONE ==>
    THE (I (2,t)) = THE (I (3,t)) + 1
Proof
  rw [] >>
  `(THE (I' (2,t)) > THE (I' (3,t))) /\ (THE (I' (2,t)) < THE (I' (3,t)) + 2)`
    by METIS_TAC [ID_instr_index_with_EX_instr] >> fs []
QED

(** I (3,t) = I (4,t) + 1 **)
Theorem EX_instr_index_with_MEM_instr_plus_1:
  !I t fext fbits a.
    is_sch I (agp32 fext fbits) a ==>
    I (3,t) <> NONE ==>
    I (4,t) <> NONE ==>
    THE (I (3,t)) = THE (I (4,t)) + 1
Proof
  rw [] >>
  `(THE (I' (3,t)) > THE (I' (4,t))) /\ (THE (I' (3,t)) < THE (I' (4,t)) + 2)`
    by METIS_TAC [EX_instr_index_with_MEM_instr] >> fs []
QED

(** I (4,t) = I (5,t) + 1 **)
Theorem MEM_instr_index_with_WB_instr_plus_1:
  !I t fext fbits a.
    is_sch I (agp32 fext fbits) a ==>
    I (4,t) <> NONE ==>
    I (5,t) <> NONE ==>
    THE (I (4,t)) = THE (I (5,t)) + 1
Proof
  rw [] >>
  `(THE (I' (4,t)) > THE (I' (5,t))) /\ (THE (I' (4,t)) < THE (I' (5,t)) + 2)`
    by METIS_TAC [MEM_instr_index_with_WB_instr] >> fs []
QED

(** I (3,SUC t) = I (3,t) + 1 **)
Theorem EX_instr_index_t_SUC_t_enable:
  !I t fext fbits a.
    is_sch I (agp32 fext fbits) a ==>
    enable_stg 3 (agp32 fext fbits t) ==>
    I (3,t) <> NONE ==>
    I (3,SUC t) <> NONE ==>
    THE (I (3,SUC t)) = THE (I (3,t)) + 1
Proof
  rw [] >> Cases_on `isJump_hw_op (agp32 fext fbits t)` >-
   (fs [is_sch_def,is_sch_execute_def] >> METIS_TAC []) >>
  Cases_on `reg_data_hazard (agp32 fext fbits t)` >-
   (fs [is_sch_def,is_sch_execute_def] >> METIS_TAC []) >>
  `I' (3,SUC t) = I' (2,t)` by fs [is_sch_def,is_sch_execute_def] >> fs [] >>
  METIS_TAC [ID_instr_index_with_EX_instr_plus_1]
QED

(** I (4,SUC t) = I (4,t) + 1 **)
Theorem MEM_instr_index_t_SUC_t_enable:
  !I t fext fbits a.
    is_sch I (agp32 fext fbits) a ==>
    enable_stg 4 (agp32 fext fbits t) ==>
    I (4,t) <> NONE ==>
    I (4,SUC t) <> NONE ==>
    THE (I (4,SUC t)) = THE (I (4,t)) + 1
Proof
  rw [] >> Cases_on `isMemOp_hw_op (agp32 fext fbits t)` >-
   (fs [is_sch_def,is_sch_memory_def] >> METIS_TAC []) >>
  `I' (4,SUC t) = I' (3,t)` by fs [is_sch_def,is_sch_memory_def] >> fs [] >>
  METIS_TAC [EX_instr_index_with_MEM_instr_plus_1]
QED

(** I (5,SUC t) = I (5,t) + 1 **)
Theorem WB_instr_index_t_SUC_t_enable:
  !I t fext fbits a.
    is_sch I (agp32 fext fbits) a ==>
    enable_stg 5 (agp32 fext fbits t) ==>
    I (5,t) <> NONE ==>
    I (5,SUC t) <> NONE ==>
    THE (I (5,SUC t)) = THE (I (5,t)) + 1
Proof
  rw [] >>
  `I' (5,SUC t) = I' (4,t)` by fs [is_sch_def,is_sch_writeback_def] >> fs [] >>
  METIS_TAC [MEM_instr_index_with_WB_instr_plus_1]
QED


(** instr index relation when IF and EX stages are not NONE then ID is NOT NONE **)
Theorem IF_EX_instr_NOT_NONE_ID_NOT_NONE:
  !I t fext fbits a.
    is_sch I (agp32 fext fbits) a ==>
    I (1,t) <> NONE ==>
    I (3,t) <> NONE ==>
    I (2,t) <> NONE
Proof
  rw [] >> Induct_on `t` >-
   fs [is_sch_def,is_sch_init_def] >>
  rw [] >> Cases_on `enable_stg 1 (agp32 fext fbits t)` >-
   (Cases_on `isJump_hw_op (agp32 fext fbits t)` >-
     (`enable_stg 3 (agp32 fext fbits t)`
        by fs [enable_stg_def,agp32_IF_PC_write_enable_and_ID_EX_write_enable] >>
      fs [is_sch_def,is_sch_execute_def] >>
      METIS_TAC []) >>
    Cases_on `isJump_isa_op (I' (1,t)) a \/ isJump_isa_op (I' (2,t)) a \/
    I' (1,t) = NONE \/ THE (I' (1,t)) = 0` >-
     (fs [is_sch_def,is_sch_fetch_def] >> METIS_TAC []) >> fs [] >>
    `enable_stg 2 (agp32 fext fbits t) /\ enable_stg 3 (agp32 fext fbits t)`
      by METIS_TAC [enable_stg_def,agp32_IF_PC_write_enable_and_ID_EX_write_enable,
                    agp32_IF_PC_write_enable_and_ID_ID_write_enable] >>
    fs [is_sch_def,is_sch_decode_def] >> METIS_TAC []) >>
  `~enable_stg 2 (agp32 fext fbits t)`
    by METIS_TAC [enable_stg_def,agp32_IF_PC_write_enable_and_ID_ID_write_enable] >>
  Cases_on `~enable_stg 3 (agp32 fext fbits t)` >> fs [] >-
   (fs [is_sch_def,is_sch_disable_def] >> METIS_TAC []) >>
  Cases_on `isJump_hw_op (agp32 fext fbits t)` >-
   (fs [is_sch_def,is_sch_execute_def] >> METIS_TAC []) >>
  `reg_data_hazard (agp32 fext fbits t)`
    by fs [enable_stg_def,agp32_IF_PC_write_disable_ID_EX_write_enable_reg_data_hazard] >>
  fs [is_sch_def,is_sch_execute_def] >> METIS_TAC []
QED

(** instr index relation when IF is not NONE but ID is NONE then EX is NONE **)
Theorem IF_instr_NOT_NONE_ID_NONE_THEN_EX_NONE:
  !I t fext fbits a.
    is_sch I (agp32 fext fbits) a ==>
    I (1,t) <> NONE ==>
    I (2,t) = NONE ==>
    I (3,t) = NONE
Proof
  rw [] >> Induct_on `t` >-
   fs [is_sch_def,is_sch_init_def] >>
  rw [] >> Cases_on `enable_stg 1 (agp32 fext fbits t)` >-
   (Cases_on `isJump_hw_op (agp32 fext fbits t)` >-
     (`enable_stg 3 (agp32 fext fbits t)`
        by fs [enable_stg_def,agp32_IF_PC_write_enable_and_ID_EX_write_enable] >>
      fs [is_sch_def,is_sch_execute_def]) >>
    Cases_on `isJump_isa_op (I' (1,t)) a \/ isJump_isa_op (I' (2,t)) a \/
    I' (1,t) = NONE \/ THE (I' (1,t)) = 0` >-
     (fs [is_sch_def,is_sch_fetch_def] >> METIS_TAC []) >> fs [] >>
    `enable_stg 2 (agp32 fext fbits t)`
      by fs [enable_stg_def,agp32_IF_PC_write_enable_and_ID_ID_write_enable] >>
    fs [is_sch_def,is_sch_decode_def] >> METIS_TAC []) >>
  `~enable_stg 2 (agp32 fext fbits t)`
    by METIS_TAC [enable_stg_def,agp32_IF_PC_write_enable_and_ID_ID_write_enable] >>
  Cases_on `~enable_stg 3 (agp32 fext fbits t)` >> fs [] >-
   (fs [is_sch_def,is_sch_disable_def] >> METIS_TAC []) >>
  Cases_on `isJump_hw_op (agp32 fext fbits t)` >-
   (fs [is_sch_def,is_sch_execute_def] >> METIS_TAC []) >>
  `reg_data_hazard (agp32 fext fbits t)`
    by fs [enable_stg_def,agp32_IF_PC_write_disable_ID_EX_write_enable_reg_data_hazard] >>
  fs [is_sch_def,is_sch_execute_def] >> METIS_TAC []
QED

(** instr index relation between ID and MEM stages when EX is NONE **)
Theorem ID_instr_index_with_MEM_instr_EX_NONE:
  !I t fext fbits a.
    is_sch I (agp32 fext fbits) a ==>
    I (2,t) <> NONE ==>
    I (3,t) = NONE ==>
    I (4,t) <> NONE ==>
    (THE (I (2,t)) > THE (I (4,t))) /\ (THE (I (2,t)) < THE (I (4,t)) + 2)
Proof
  rpt gen_tac >> rpt disch_tac >>
  Induct_on `t` >-
   fs [is_sch_def,is_sch_init_def] >>
  rpt disch_tac >>
  Cases_on `enable_stg 2 (agp32 fext fbits t)` >-
   (Cases_on `isJump_isa_op (I' (2,t)) a \/ isJump_hw_op (agp32 fext fbits t)` >-
     (fs [is_sch_def,is_sch_decode_def] >> METIS_TAC []) >>
    `I' (2,SUC t) = I' (1,t)` by fs [is_sch_def,is_sch_decode_def] >>
    `enable_stg 4 (agp32 fext fbits t)`
      by fs [enable_stg_def,agp32_ID_ID_write_enable_MEM_state_flag] >>
    Cases_on `isMemOp_hw_op (agp32 fext fbits t)` >-
     (fs [is_sch_def,is_sch_memory_def] >> METIS_TAC []) >>
    `I' (4,SUC t) = I' (3,t)` by fs [is_sch_def,is_sch_memory_def] >> fs [] >>
    `enable_stg 3 (agp32 fext fbits t)`
      by fs [enable_stg_def,agp32_ID_ID_write_enable_and_ID_EX_write_enable] >>
     Cases_on `reg_data_hazard (agp32 fext fbits t)` >-
     (fs [isJump_hw_op_def,enable_stg_def] >>
      METIS_TAC [agp32_ID_ID_write_enable_EX_jump_sel_then_no_reg_data_hazard]) >>
    `I' (3,SUC t) = I' (2,t)` by METIS_TAC [is_sch_def,is_sch_execute_def] >>
    fs [] >> METIS_TAC [IF_EX_instr_NOT_NONE_ID_NOT_NONE]) >>
  Cases_on `enable_stg 4 (agp32 fext fbits t)` >-
   (Cases_on `isMemOp_hw_op (agp32 fext fbits t)` >-
     (fs [is_sch_def,is_sch_memory_def] >> METIS_TAC []) >>
    `I' (2,SUC t) = I' (2,t) /\ I' (4,SUC t) = I' (3,t)`
      by fs [is_sch_def,is_sch_memory_def,is_sch_disable_def] >> fs [] >>
    `(THE (I' (2,t)) > THE (I' (3,t))) /\ (THE (I' (2,t)) < THE (I' (3,t)) + 2)`
      by METIS_TAC [ID_instr_index_with_EX_instr] >> fs []) >>
  `~enable_stg 3 (agp32 fext fbits t)`
    by fs [enable_stg_def,agp32_MEM_state_flag_F_and_ID_EX_write_disable] >>
  fs [is_sch_def,is_sch_disable_def] >> METIS_TAC []
QED

(** I (4,t) = I (2,t) + 1 when I (3,t) is NONE **)
Theorem EX_NONE_ID_instr_index_with_MEM_instr_plus_1:
  !I t fext fbits a.
    is_sch I (agp32 fext fbits) a ==>
    I (2,t) <> NONE ==>
    I (3,t) = NONE ==>
    I (4,t) <> NONE ==>
    THE (I (2,t)) = THE (I (4,t)) + 1
Proof
  rw [] >>
  `(THE (I' (2,t)) > THE (I' (4,t))) /\ (THE (I' (2,t)) < THE (I' (4,t)) + 2)`
    by METIS_TAC [ID_instr_index_with_MEM_instr_EX_NONE] >> fs []
QED


(** instr index relation between ID and MEM stages when EX is NONE **)
Theorem EX_instr_index_with_WB_instr_MEM_NONE:
  !I t fext fbits a.
    is_sch I (agp32 fext fbits) a ==>
    I (3,t) <> NONE ==>
    I (4,t) = NONE ==>
    I (5,t) <> NONE ==>
    (THE (I (3,t)) > THE (I (5,t))) /\ (THE (I (3,t)) < THE (I (5,t)) + 2)
Proof
  rpt gen_tac >> rpt disch_tac >>
  Induct_on `t` >-
   fs [is_sch_def,is_sch_init_def] >>
  rpt disch_tac >>
  Cases_on `enable_stg 3 (agp32 fext fbits t)` >-
   (Cases_on `isJump_hw_op (agp32 fext fbits t)` >-
     (fs [is_sch_def,is_sch_execute_def] >> METIS_TAC []) >>
    Cases_on `reg_data_hazard (agp32 fext fbits t)` >-
     (fs [is_sch_def,is_sch_execute_def] >> METIS_TAC []) >>
    `I' (3,SUC t) = I' (2,t)` by fs [is_sch_def,is_sch_execute_def] >>
    `enable_stg 5 (agp32 fext fbits t)`
      by fs [enable_stg_def,agp32_ID_EX_write_enable_WB_state_flag] >>
    `I' (5,SUC t) = I' (4,t)` by fs [is_sch_def,is_sch_writeback_def] >> fs [] >>
    `enable_stg 4 (agp32 fext fbits t)`
      by fs [enable_stg_def,agp32_ID_EX_write_enable_MEM_state_flag] >>
    Cases_on `isMemOp_hw_op (agp32 fext fbits t)` >-
     (fs [enable_stg_def] >>
      METIS_TAC [agp32_ID_EX_write_enable_no_MEM_stg_op]) >>
    `I' (4,SUC t) = I' (3,t)` by METIS_TAC [is_sch_def,is_sch_memory_def] >> fs [] >>
    `(THE (I' (2,t)) > THE (I' (4,t))) /\ (THE (I' (2,t)) < THE (I' (4,t)) + 2)`
      by METIS_TAC [ID_instr_index_with_MEM_instr_EX_NONE] >> fs []) >>
  Cases_on `enable_stg 5 (agp32 fext fbits t)` >-
   (`I' (3,SUC t) = I' (3,t)`
      by fs [is_sch_def,is_sch_disable_def] >> fs [] >>
    `enable_stg 4 (agp32 fext fbits t)`
      by fs [enable_stg_def,agp32_MEM_state_flag_eq_WB_state_flag] >>
    Cases_on `isMemOp_hw_op (agp32 fext fbits t)` >-
     (`I' (5,SUC t) = I' (4,t)` by fs [is_sch_def,is_sch_writeback_def] >> fs [] >>
      METIS_TAC [EX_instr_index_with_MEM_instr]) >>
    fs [is_sch_def,is_sch_memory_def] >> METIS_TAC []) >>
  `~enable_stg 4 (agp32 fext fbits t)`
    by fs [enable_stg_def,agp32_MEM_state_flag_eq_WB_state_flag] >>
  fs [is_sch_def,is_sch_disable_def] >> METIS_TAC []
QED

(** I (3,t) = I (5,t) + 1 when I (4,t) is NONE **)
Theorem EX_instr_index_with_WB_instr_plus_1_MEM_NONE:
  !I t fext fbits a.
    is_sch I (agp32 fext fbits) a ==>
    I (3,t) <> NONE ==>
    I (4,t) = NONE ==>
    I (5,t) <> NONE ==>
    THE (I (3,t)) = THE (I (5,t)) + 1
Proof
  rw [] >>
  `(THE (I' (3,t)) > THE (I' (5,t))) /\ (THE (I' (3,t)) < THE (I' (5,t)) + 2)`
    by METIS_TAC [EX_instr_index_with_WB_instr_MEM_NONE] >> fs []
QED

(** instr index relation between IF and MEM stages when ID and MEM EX NONE **)
Theorem IF_instr_index_with_MEM_instr_ID_EX_NONE:
  !I t fext fbits a.
    is_sch I (agp32 fext fbits) a ==>
    I (1,t) <> NONE ==>
    I (2,t) = NONE ==>
    I (3,t) = NONE ==>
    I (4,t) <> NONE ==>
    (THE (I (1,t)) > THE (I (4,t))) /\ (THE (I (1,t)) < THE (I (4,t)) + 2)
Proof
  rpt gen_tac >> rpt disch_tac >>
  Induct_on `t` >-
   fs [is_sch_def,is_sch_init_def] >>
  rpt disch_tac >>
  Cases_on `enable_stg 1 (agp32 fext fbits t)` >-
   (Cases_on `isJump_hw_op (agp32 fext fbits t)` >-
     (`enable_stg 4 (agp32 fext fbits t)`
        by fs [enable_stg_def,agp32_IF_PC_write_enable_and_MEM_flag] >>
      fs [is_sch_def,is_sch_fetch_def,is_sch_memory_def] >>
      Cases_on `isMemOp_hw_op (agp32 fext fbits t)` >> fs [] >>
      METIS_TAC []) >>
    Cases_on `isJump_isa_op (I' (1,t)) a \/ isJump_isa_op (I' (2,t)) a \/
    I' (1,t) = NONE \/ THE (I' (1,t)) = 0` >-
     (fs [is_sch_def,is_sch_fetch_def,is_sch_execute_def] >> METIS_TAC []) >>
    fs [] >>
    `enable_stg 2 (agp32 fext fbits t)`
      by fs [enable_stg_def,agp32_IF_PC_write_enable_and_ID_ID_write_enable] >>
    `I' (2,SUC t) = I' (1,t)` by METIS_TAC [is_sch_def,is_sch_decode_def] >> fs []) >>
  Cases_on `enable_stg 4 (agp32 fext fbits t)` >-
   (Cases_on `isMemOp_hw_op (agp32 fext fbits t)` >-
     (fs [is_sch_def,is_sch_memory_def] >> METIS_TAC []) >>
    `I' (4,SUC t) = I' (3,t)` by fs [is_sch_def,is_sch_memory_def] >>
    Cases_on `~enable_stg 3 (agp32 fext fbits t)` >> fs [] >-
     (fs [is_sch_def,is_sch_disable_def] >> METIS_TAC []) >>
    `~enable_stg 2 (agp32 fext fbits t)`
      by fs [enable_stg_def,agp32_IF_PC_write_enable_and_ID_ID_write_enable] >>
    `(I' (1,SUC t) = I' (1,t)) /\ (I' (2,SUC t) = I' (2,t))`
      by METIS_TAC [is_sch_def,is_sch_disable_def] >> fs [] >>
    METIS_TAC [IF_instr_NOT_NONE_ID_NONE_THEN_EX_NONE]) >>
  `~enable_stg 2 (agp32 fext fbits t)`
    by METIS_TAC [enable_stg_def,agp32_IF_PC_write_enable_and_ID_ID_write_enable] >>
  `~enable_stg 3 (agp32 fext fbits t)`
    by fs [enable_stg_def,agp32_MEM_state_flag_F_and_ID_EX_write_disable] >>
  fs [is_sch_def,is_sch_disable_def] >> METIS_TAC []
QED

(** instr index relation between ID and WB stages when EX and MEM are NONE **)
Theorem ID_instr_index_with_WB_instr_EX_MEM_NONE:
  !I t fext fbits a.
    is_sch I (agp32 fext fbits) a ==>
    I (2,t) <> NONE ==>
    I (3,t) = NONE ==>
    I (4,t) = NONE ==>
    I (5,t) <> NONE ==>
    (THE (I (2,t)) > THE (I (5,t))) /\ (THE (I (2,t)) < THE (I (5,t)) + 2)
Proof
  rpt gen_tac >> rpt disch_tac >>
  Induct_on `t` >-
   fs [is_sch_def,is_sch_init_def] >>
  rpt disch_tac >>
  Cases_on `enable_stg 2 (agp32 fext fbits t)` >-
   (Cases_on `isJump_isa_op (I' (2,t)) a \/ isJump_hw_op (agp32 fext fbits t)` >-
     (fs [is_sch_def,is_sch_decode_def] >> METIS_TAC []) >>
    `I' (2,SUC t) = I' (1,t)` by fs [is_sch_def,is_sch_decode_def] >> fs [] >>
    `enable_stg 5 (agp32 fext fbits t)`
      by fs [enable_stg_def,agp32_ID_ID_write_enable_WB_state_flag] >>
    `I' (5,SUC t) = I' (4,t)` by fs [is_sch_def,is_sch_writeback_def] >> fs [] >>
    `enable_stg 4 (agp32 fext fbits t)`
      by fs [enable_stg_def,agp32_ID_ID_write_enable_MEM_state_flag] >>
    Cases_on `isMemOp_hw_op (agp32 fext fbits t)` >-
     (`enable_stg 3 (agp32 fext fbits t)`
        by fs [enable_stg_def, agp32_ID_ID_write_enable_and_ID_EX_write_enable] >>
      Cases_on `reg_data_hazard (agp32 fext fbits t)` >-
       (fs [isJump_hw_op_def,enable_stg_def] >>
        METIS_TAC [agp32_ID_ID_write_enable_EX_jump_sel_then_no_reg_data_hazard]) >>
      `I' (3,SUC t) = I' (2,t)` by METIS_TAC [is_sch_def,is_sch_execute_def] >> fs [] >>
      `I' (3,t) = NONE` by METIS_TAC [IF_instr_NOT_NONE_ID_NONE_THEN_EX_NONE] >>
      METIS_TAC [IF_instr_index_with_MEM_instr_ID_EX_NONE]) >>
    `I' (4,SUC t) = I' (3,t)` by METIS_TAC [is_sch_def,is_sch_memory_def] >>
    `enable_stg 3 (agp32 fext fbits t)`
      by fs [enable_stg_def,agp32_ID_ID_write_enable_and_ID_EX_write_enable] >>
    Cases_on `reg_data_hazard (agp32 fext fbits t)` >-
     (fs [isJump_hw_op_def,enable_stg_def] >>
      METIS_TAC [agp32_ID_ID_write_enable_EX_jump_sel_then_no_reg_data_hazard]) >>
    `I' (3,SUC t) = I' (2,t)` by METIS_TAC [is_sch_def,is_sch_execute_def] >> fs [] >>
    METIS_TAC [IF_instr_index_with_MEM_instr_ID_EX_NONE]) >>
  Cases_on `enable_stg 5 (agp32 fext fbits t)` >-
   (`I' (5,SUC t) = I' (4,t)` by fs [is_sch_def,is_sch_writeback_def] >>
    Cases_on `~enable_stg 3 (agp32 fext fbits t)` >> fs [] >-
     (`I' (2,SUC t) = I' (2,t) /\ I' (3,SUC t) = I' (3,t)`
        by METIS_TAC [is_sch_def,is_sch_disable_def] >> fs [] >>
      METIS_TAC [ID_instr_index_with_MEM_instr_EX_NONE]) >>
    `I' (2,SUC t) = I' (2,t)` by METIS_TAC [is_sch_def,is_sch_disable_def] >> fs [] >>
    `enable_stg 4 (agp32 fext fbits t)`
      by fs [enable_stg_def,agp32_MEM_state_flag_eq_WB_state_flag] >>
    `~isMemOp_hw_op (agp32 fext fbits t)`
      by fs [enable_stg_def,agp32_ID_EX_write_enable_no_MEM_stg_op] >>
    `I' (4,SUC t) = I' (3,t)` by METIS_TAC [is_sch_def,is_sch_memory_def] >> fs [] >>
    METIS_TAC [ID_instr_index_with_MEM_instr_EX_NONE]) >>
  Cases_on `enable_stg 4 (agp32 fext fbits t)` >-
   (fs [enable_stg_def] >> fs [agp32_MEM_state_flag_eq_WB_state_flag]) >>
  `~enable_stg 3 (agp32 fext fbits t)`
    by fs [enable_stg_def,agp32_MEM_state_flag_F_and_ID_EX_write_disable] >>
  fs [is_sch_def,is_sch_disable_def] >> METIS_TAC []
QED

(** I (5,t) = I (2,t) + 1 when I (3,t) and I (4,t) are NONE **)
Theorem EX_MEM_NONE_ID_instr_index_with_WB_instr_plus_1:
  !I t fext fbits a.
    is_sch I (agp32 fext fbits) a ==>
    I (2,t) <> NONE ==>
    I (3,t) = NONE ==>
    I (4,t) = NONE ==>
    I (5,t) <> NONE ==>
    THE (I (2,t)) = THE (I (5,t)) + 1
Proof
  rw [] >>
  `(THE (I' (2,t)) > THE (I' (5,t))) /\ (THE (I' (2,t)) < THE (I' (5,t)) + 2)`
    by METIS_TAC [ID_instr_index_with_WB_instr_EX_MEM_NONE] >> fs []
QED

(** instr index relation between IF and WB stages when ID, EX and MEM are NONE **)
Theorem IF_instr_index_with_WB_instr_ID_EX_MEM_NONE:
  !I t fext fbits a.
    is_sch I (agp32 fext fbits) a ==>
    I (1,t) <> NONE ==>
    I (2,t) = NONE ==>
    I (3,t) = NONE ==>
    I (4,t) = NONE ==>
    I (5,t) <> NONE ==>
    (THE (I (1,t)) > THE (I (5,t))) /\ (THE (I (1,t)) < THE (I (5,t)) + 2)
Proof
  rpt gen_tac >> rpt disch_tac >>
  Induct_on `t` >-
   fs [is_sch_def,is_sch_init_def] >>
  rpt disch_tac >>
  Cases_on `enable_stg 1 (agp32 fext fbits t)` >-
   (Cases_on `isJump_hw_op (agp32 fext fbits t)` >-
     (`I' (1,SUC t) = SOME (THE (I' (3,t)) + 1)` by fs [is_sch_def,is_sch_fetch_def] >>
      `isJump_isa_op (I' (3,t)) a` by cheat >>
      `I' (3,t) <> NONE` by METIS_TAC [isJump_isa_op_not_none] >>
      `enable_stg 4 (agp32 fext fbits t)`
        by fs [enable_stg_def,agp32_IF_PC_write_enable_and_MEM_flag] >>
      `enable_stg 3 (agp32 fext fbits t)`
        by fs [enable_stg_def,agp32_IF_PC_write_enable_and_ID_EX_write_enable] >>
      Cases_on `isMemOp_hw_op (agp32 fext fbits t)` >-
       (fs [enable_stg_def] >>
        METIS_TAC [MEM_stg_op_agp32_ID_EX_write_disable]) >>
      `I' (4,SUC t) = I' (3,t)` by METIS_TAC [is_sch_def,is_sch_memory_def] >> fs []) >>
    Cases_on `isJump_isa_op (I' (1,t)) a \/ isJump_isa_op (I' (2,t)) a \/
    I' (1,t) = NONE \/ THE (I' (1,t)) = 0` >-
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
  fs [is_sch_def,is_sch_disable_def] >> METIS_TAC []
QED

(** I (5,t) = I (1,t) + 1 when I (2,t), I (3,t) and I (4,t) are NONE **)
Theorem ID_EX_MEM_NONE_IF_instr_index_with_WB_instr_plus_1:
  !I t fext fbits a.
    is_sch I (agp32 fext fbits) a ==>
    I (1,t) <> NONE ==>
    I (2,t) = NONE ==>
    I (3,t) = NONE ==>
    I (4,t) = NONE ==>
    I (5,t) <> NONE ==>
    THE (I (1,t)) = THE (I (5,t)) + 1
Proof
  rw [] >>
  `(THE (I' (1,t)) > THE (I' (5,t))) /\ (THE (I' (1,t)) < THE (I' (5,t)) + 2)`
    by METIS_TAC [IF_instr_index_with_WB_instr_ID_EX_MEM_NONE] >> fs []
QED

val _ = export_theory ();
