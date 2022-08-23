open hardwarePreamble translatorTheory arithmeticTheory dep_rewrite blastLib bitstringSyntax fcpSyntax listSyntax wordsSyntax wordsLib agp32StateTheory agp32EnvironmentTheory agp32ProcessorTheory agp32RelationTheory agp32UpdateTheory agp32UpdateLib;

val _ = new_theory "agp32Internal";

val _ = prefer_num ();
val _ = guess_lengths ();

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
  Q.ABBREV_TAC `s' = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s'' = procs [agp32_next_state;WB_pipeline;MEM_pipeline] (fext t) s' s'` >>
  `?s.(agp32 fext fbits (SUC t)).EX.EX_opc = (EX_pipeline (fext (SUC t)) s s'').EX.EX_opc /\
  (agp32 fext fbits (SUC t)).EX.EX_func = (EX_pipeline (fext (SUC t)) s s'').EX.EX_func`
    by fs [agp32_EX_opc_func_updated_by_EX_pipeline] >>
  `s''.ID.ID_EX_write_enable <=> s'.ID.ID_EX_write_enable`
    by METIS_TAC [Abbr `s'`,Abbr `s''`,agp32_same_items_until_MEM_pipeline] >>
  fs [EX_pipeline_def] >>
  Cases_on `s'.ID.ID_EX_write_enable` >> fs [] >>
  `s''.ID.ID_func = s'.ID.ID_func /\ s''.ID.ID_opc = s'.ID.ID_opc`
    by METIS_TAC [Abbr `s'`,Abbr `s''`,agp32_same_items_until_MEM_pipeline] >>
  METIS_TAC [agp32_ID_opc_implies_ID_func]
QED


(* ID_EX_write_enable, ID_ID_write_enable and ID_flush_flag *)
Theorem agp32_ID_enable_flags_imply_flush_NOP_flags:
  !fext fbits t.
    ~((agp32 fext fbits t).ID.ID_ID_write_enable) ==>
    (agp32 fext fbits t).ID.ID_EX_write_enable ==>
    (agp32 fext fbits t).ID.ID_flush_flag /\
    (agp32 fext fbits t).EX.EX_NOP_flag
Proof
  rw [] >>
  `?s s'.
  ((agp32 fext fbits t).ID.ID_ID_write_enable <=> (Hazard_ctrl (fext t) s s').ID.ID_ID_write_enable) /\
  ((agp32 fext fbits t).ID.ID_EX_write_enable <=> (Hazard_ctrl (fext t) s s').ID.ID_EX_write_enable) /\
  ((agp32 fext fbits t).ID.ID_flush_flag <=> (Hazard_ctrl (fext t) s s').ID.ID_flush_flag) /\
  ((agp32 fext fbits t).EX.EX_NOP_flag <=> (Hazard_ctrl (fext t) s s').EX.EX_NOP_flag)`
    by METIS_TAC [agp32_ctrl_flags_exists_Hazard_ctrl] >> fs [] >>
  fs [Hazard_ctrl_def] >>
  Cases_on `s'.state = 3w \/ s'.state = 5w` >> fs [] >>
  Cases_on `s'.state = 1w \/ s'.state = 2w \/ s'.state = 4w \/ s'.state = 6w` >> fs [] >>
  Cases_on `(fext t).ready` >> fs [] >>
  Cases_on `s.MEM.MEM_opc = 2w \/ s.MEM.MEM_opc = 3w \/ s.MEM.MEM_opc = 4w \/
            s.MEM.MEM_opc = 5w \/ s.MEM.MEM_opc = 12w` >> fs [] >>
  Cases_on `s'.EX.EX_isAcc` >> fs [] >>
  Cases_on `s'.EX.EX_jump_sel` >> fs []                               
QED


(* IF_PC_write_enable and MEM_state_flag *)
Theorem agp32_IF_PC_write_enable_and_EX_MEM_flags:
  !fext fbits t.
    (agp32 fext fbits t).IF.IF_PC_write_enable ==>
    (agp32 fext fbits t).ID.ID_EX_write_enable /\
    (agp32 fext fbits t).MEM.MEM_state_flag
Proof
  rw [] >>
  `?s s'.
  ((agp32 fext fbits t).IF.IF_PC_write_enable <=> (Hazard_ctrl (fext t) s s').IF.IF_PC_write_enable) /\
  ((agp32 fext fbits t).ID.ID_EX_write_enable <=> (Hazard_ctrl (fext t) s s').ID.ID_EX_write_enable) /\
  ((agp32 fext fbits t).MEM.MEM_state_flag <=> (Hazard_ctrl (fext t) s s').MEM.MEM_state_flag)`
    by METIS_TAC [agp32_ctrl_flags_exists_Hazard_ctrl] >> fs [] >>
  fs [Hazard_ctrl_def] >>
  Cases_on `s'.state = 3w \/ s'.state = 5w` >> fs [] >>
  Cases_on `s'.state = 1w \/ s'.state = 2w \/ s'.state = 4w \/ s'.state = 6w` >> fs [] >>
  Cases_on `(fext t).ready` >> fs [] >>
  Cases_on `s.MEM.MEM_opc = 2w \/ s.MEM.MEM_opc = 3w \/ s.MEM.MEM_opc = 4w \/
            s.MEM.MEM_opc = 5w \/ s.MEM.MEM_opc = 12w` >> fs [] >>
  Cases_on `s'.EX.EX_isAcc` >> fs [] >>
  Cases_on `s'.EX.EX_jump_sel` >> fs []
QED

(* IF_PC_write_enable is F then ID_EX_write_enable is also F *)
Theorem agp32_IF_PC_write_disable_and_EX_disable:
  !fext fbits t.
    ~(agp32 fext fbits t).IF.IF_PC_write_enable ==>
    ~(agp32 fext fbits t).ID.ID_EX_write_enable
Proof
  rw [] >>
  `?s s'.
  ((agp32 fext fbits t).IF.IF_PC_write_enable <=> (Hazard_ctrl (fext t) s s').IF.IF_PC_write_enable) /\
  ((agp32 fext fbits t).ID.ID_EX_write_enable <=> (Hazard_ctrl (fext t) s s').ID.ID_EX_write_enable)`
    by METIS_TAC [agp32_ctrl_flags_exists_Hazard_ctrl] >> fs [] >>
  fs [Hazard_ctrl_def] >>
  Cases_on `s'.state = 3w \/ s'.state = 5w` >> fs [] >>
  Cases_on `s'.state = 1w \/ s'.state = 2w \/ s'.state = 4w \/ s'.state = 6w` >> fs [] >>
  Cases_on `(fext t).ready` >> fs [] >>
  Cases_on `s.MEM.MEM_opc = 2w \/ s.MEM.MEM_opc = 3w \/ s.MEM.MEM_opc = 4w \/
            s.MEM.MEM_opc = 5w \/ s.MEM.MEM_opc = 12w` >> fs [] >>
  Cases_on `s'.EX.EX_isAcc` >> fs [] >>
  Cases_on `s'.EX.EX_jump_sel` >> fs []
QED

(** IF_PC_write_enable and fext t.ready **)
Theorem agp32_IF_PC_write_enable_and_fext_ready:
  !fext fbits t.
    (agp32 fext fbits t).IF.IF_PC_write_enable ==>
    (fext t).ready
Proof
  rw [] >>
  `?s s'.
  ((agp32 fext fbits t).IF.IF_PC_write_enable <=> (Hazard_ctrl (fext t) s s').IF.IF_PC_write_enable)`
    by METIS_TAC [agp32_ctrl_flags_exists_Hazard_ctrl] >> fs [] >>
  fs [Hazard_ctrl_def] >>
  Cases_on `s'.state = 3w \/ s'.state = 5w` >> fs [] >>
  Cases_on `s'.state = 1w \/ s'.state = 2w \/ s'.state = 4w \/ s'.state = 6w` >> fs [] >>
  Cases_on `(fext t).ready` >> fs []
QED

Theorem not_fext_ready_and_agp32_IF_PC_write_disable:
  !fext fbits t.
    ~(fext t).ready ==>
    ~(agp32 fext fbits t).IF.IF_PC_write_enable
Proof
  rw [] >> METIS_TAC [agp32_IF_PC_write_enable_and_fext_ready]
QED


(* ID_ID_write_enable *)
(** ID_ID_write_enable and fext t.ready **)
Theorem agp32_ID_ID_write_enable_and_fext_ready:
  !fext fbits t.
    (agp32 fext fbits t).ID.ID_ID_write_enable ==>
    (fext t).ready
Proof
  rw [] >>
  `?s s'.
  ((agp32 fext fbits t).ID.ID_ID_write_enable <=> (Hazard_ctrl (fext t) s s').ID.ID_ID_write_enable)`
    by METIS_TAC [agp32_ctrl_flags_exists_Hazard_ctrl] >> fs [] >>
  fs [Hazard_ctrl_def] >>
  Cases_on `s'.state = 3w \/ s'.state = 5w` >> fs [] >>
  Cases_on `s'.state = 1w \/ s'.state = 2w \/ s'.state = 4w \/ s'.state = 6w` >> fs [] >>
  Cases_on `(fext t).ready` >> fs []
QED


(* initial values *)
(** initial EX_PC_sel = 0w **)
Theorem agp32_init_EX_PC_sel:
  !fext fbits.
    (agp32 fext fbits 0).EX.EX_PC_sel = 0w
Proof
  rw [agp32_def,mk_module_def,mk_circuit_def] >>
  clist_update_state_tac >>
  fs [Abbr `s20`,Abbr `s19`,Abbr `s18`,Abbr `s17`,Abbr `s16`,Abbr `s15`,
      Abbr `s14`,Abbr `s13`,Abbr `s12`,Abbr `s11`,Abbr `s10`,Abbr `s9`,Abbr `s8`,
      Hazard_ctrl_unchanged_EX_ctrl_items,WB_update_unchanged_EX_ctrl_items,
      MEM_imm_update_unchanged_EX_ctrl_items,MEM_ctrl_update_unchanged_EX_ctrl_items,
      IF_PC_input_update_def,EX_data_rec_update_unchanged_EX_ctrl_items,
      EX_jump_sel_addr_update_unchanged_EX_ctrl_items,
      EX_SHIFT_update_unchanged_EX_ctrl_items,EX_ALU_update_unchanged_EX_ctrl_items,
      EX_compute_enable_update_unchanged_EX_ctrl_items,
      EX_ALU_input_update_unchanged_EX_ctrl_items,
      EX_forward_data_unchanged_EX_ctrl_items] >>
  Cases_on `s7.ID.ID_EX_write_enable` >-
   fs [EX_ctrl_update_def,agp32_init_def] >>
  rw [EX_ctrl_update_def] >>      
  fs [Abbr `s7`,Abbr `s6`,Abbr `s5`,Abbr `s4`,Abbr `s3`,Abbr `s2`,Abbr `s1`,
      ID_data_update_unchanged_EX_ctrl_items,ID_imm_update_unchanged_EX_ctrl_items,
      ID_opc_func_update_unchanged_EX_ctrl_items,IF_instr_update_def,
      ForwardA_def,ForwardB_def,ForwardW_def] >>
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
  fs [Abbr `s20`,Abbr `s19`,Abbr `s18`,Abbr `s17`,Abbr `s16`,Abbr `s15`,Abbr `s14`,
      Hazard_ctrl_unchanged_EX_jump,Hazard_ctrl_unchanged_EX_ctrl_items,
      WB_update_unchanged_EX_jump,WB_update_unchanged_EX_ctrl_items,
      MEM_imm_update_unchanged_EX_jump,MEM_imm_update_unchanged_EX_ctrl_items,
      MEM_ctrl_update_unchanged_EX_jump,MEM_ctrl_update_unchanged_EX_ctrl_items,
      IF_PC_input_update_def,EX_data_rec_update_unchanged_EX_jump,
      EX_data_rec_update_unchanged_EX_ctrl_items,
      EX_jump_sel_addr_update_unchanged_EX_ctrl_items] >>
  rw [EX_jump_sel_addr_update_def]
QED

(** initial IF_PC_input = PC + 4w **)
Theorem agp32_init_IF_PC_input:
  !fext fbits.
    (agp32 fext fbits 0).IF.IF_PC_input = (agp32 fext fbits 0).PC + 4w
Proof
  rw [] >> `~(agp32 fext fbits 0).EX.EX_jump_sel` by rw [agp32_init_EX_jump_sel] >>
  fs [agp32_def,mk_module_def,mk_circuit_def] >>
  clist_update_state_tac >>
  fs [Abbr `s20`,Abbr `s19`,Abbr `s18`,Abbr `s17`,Abbr `s16`,
      Hazard_ctrl_unchanged_IF,Hazard_ctrl_unchanged_EX_jump,
      WB_update_unchanged_IF,WB_update_unchanged_EX_jump,
      MEM_imm_update_unchanged_IF,MEM_imm_update_unchanged_EX_jump,
      MEM_ctrl_update_unchanged_IF,MEM_ctrl_update_unchanged_EX_jump] >>
  fs [IF_PC_input_update_def,MUX_21_def] >>
  fs [Abbr `s15`,Abbr `s14`,Abbr `s13`,Abbr `s12`,Abbr `s11`,Abbr `s10`,Abbr `s9`,
      Abbr `s8`,Abbr `s7`,Abbr `s6`,Abbr `s5`,Abbr `s4`,Abbr `s3`,Abbr `s2`,Abbr `s1`,
      EX_data_rec_update_unchanged_IF,EX_jump_sel_addr_update_unchanged_IF,
      EX_SHIFT_update_unchanged_IF,EX_ALU_update_unchanged_IF,
      EX_compute_enable_update_unchanged_IF,EX_ALU_input_update_unchanged_IF,
      EX_forward_data_unchanged_IF,EX_ctrl_update_unchanged_IF,
      ID_data_update_unchanged_IF,ID_imm_update_unchanged_IF,
      ID_opc_func_update_unchanged_IF,IF_PC_input_update_def,IF_instr_update_def,
      ForwardW_def,ForwardB_def,ForwardA_def]
QED

(** initial command is 0 **)
Theorem agp32_init_command_0w:
  !fext fbits.
    (agp32 fext fbits 0).command = 0w
Proof
  rw [agp32_def,mk_module_def,mk_circuit_def] >>
  clist_update_state_tac >>
  fs [Abbr `s20`,Abbr `s19`,Abbr `s18`,Abbr `s17`,Abbr `s16`,Abbr `s15`,Abbr `s14`,
      Abbr `s13`,Abbr `s12`,Abbr `s11`,Abbr `s10`,Abbr `s9`,Abbr `s8`,Abbr `s7`,
      Abbr `s6`,Abbr `s5`,Abbr `s4`,Abbr `s3`,Abbr `s2`,Abbr `s1`,
      Hazard_ctrl_unchanged_state_items,WB_update_unchanged_state_items,
      MEM_imm_update_unchanged_state_items,MEM_ctrl_update_unchanged_state_items,
      EX_data_rec_update_unchanged_state_items,EX_jump_sel_addr_update_unchanged_state_items,
      EX_SHIFT_update_unchanged_state_items,EX_ALU_update_unchanged_state_items,
      EX_compute_enable_update_unchanged_state_items,EX_ALU_input_update_unchanged_state_items,
      EX_forward_data_unchanged_state_items,EX_ctrl_update_unchanged_state_items,
      ID_data_update_unchanged_state_items,ID_imm_update_unchanged_state_items,
      ID_opc_func_update_unchanged_state_items,IF_PC_input_update_def,IF_instr_update_def,
      ForwardW_def,ForwardB_def,ForwardA_def] >>
  rw [agp32_init_def]
QED

(** initial state is 3 **)
Theorem agp32_init_state_3w:
  !fext fbits.
    (agp32 fext fbits 0).state = 3w
Proof
  rw [agp32_def,mk_module_def,mk_circuit_def] >>
  clist_update_state_tac >>
  fs [Abbr `s20`,Abbr `s19`,Abbr `s18`,Abbr `s17`,Abbr `s16`,Abbr `s15`,Abbr `s14`,
      Abbr `s13`,Abbr `s12`,Abbr `s11`,Abbr `s10`,Abbr `s9`,Abbr `s8`,Abbr `s7`,
      Abbr `s6`,Abbr `s5`,Abbr `s4`,Abbr `s3`,Abbr `s2`,Abbr `s1`,
      Hazard_ctrl_unchanged_state_items,WB_update_unchanged_state_items,
      MEM_imm_update_unchanged_state_items,MEM_ctrl_update_unchanged_state_items,
      EX_data_rec_update_unchanged_state_items,EX_jump_sel_addr_update_unchanged_state_items,
      EX_SHIFT_update_unchanged_state_items,EX_ALU_update_unchanged_state_items,
      EX_compute_enable_update_unchanged_state_items,EX_ALU_input_update_unchanged_state_items,
      EX_forward_data_unchanged_state_items,EX_ctrl_update_unchanged_state_items,
      ID_data_update_unchanged_state_items,ID_imm_update_unchanged_state_items,
      ID_opc_func_update_unchanged_state_items,IF_PC_input_update_def,IF_instr_update_def,
      ForwardW_def,ForwardB_def,ForwardA_def] >>
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

(* state is not possible for values 7 *)
Theorem agp32_state_impossible_values:
  !fext fbits t.
    (agp32 fext fbits t).state <> 7w
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


(* properties about the scheduling function *)
Theorem well_formed_sch_SUC_t_rewrite:
  !I sf t k.
    well_formed_sch I sf t ==>
    is_sch_other I sf ==>
    enable_stg k (sf t) ==>
    k > 2 ==>
    I (k,SUC t) = SOME (THE (I (k,t)) + 1)
Proof
  rw [well_formed_sch_def,is_sch_other_def]
QED

(* TODO: sch is well_formed
Theorem well_formed_sch_agp32:
  !t I fext fbits.
    is_sch_other I (agp32 fext fbits) ==>
    is_sch_disable I (agp32 fext fbits) ==>
    well_formed_sch I (agp32 fext fbits) t
Proof
  rw [] >> Induct_on `t` >-
   (fs [is_sch_other_def,well_formed_sch_def] >> rw [] >> cheat) >>
  rw [well_formed_sch_def] >>
  `k - 1 > 1` by rw [] >>
  Cases_on `enable_stg (k - 1) (agp32 fext fbits t)` >-
   (`I' (k-1,SUC t) = SOME (THE (I' (k-1,t)) + 1)` by METIS_TAC [well_formed_sch_SUC_t_rewrite] >>
    rw [] >> fs [is_sch_other_def] >>
    `enable_stg k (agp32 fext fbits t)` by cheat >> fs []) >>
  fs [is_sch_disable_def] >>
  `enable_stg k (agp32 fext fbits t)` by cheat >> fs [is_sch_other_def]
QED
*)

val _ = export_theory ();
