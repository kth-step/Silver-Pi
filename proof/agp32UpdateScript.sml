open hardwarePreamble translatorTheory translatorLib arithmeticTheory dep_rewrite blastLib bitstringSyntax fcpSyntax listSyntax wordsSyntax wordsLib agp32StateTheory agp32EnvironmentTheory agp32ProcessorTheory;

val _ = new_theory "agp32Update";

val _ = prefer_num ();
val _ = guess_lengths ();

(* show the unchanged part of IF_state for functions used in the combinational logic *)
Theorem IF_PC_input_update_unchanged_IF:
  !fext s s'.
    ((IF_PC_input_update fext s s').IF.IF_instr = s'.IF.IF_instr) /\
    ((IF_PC_input_update fext s s').IF.IF_PC_write_enable = s'.IF.IF_PC_write_enable)
Proof
  rw [IF_PC_input_update_def]
QED

Theorem ID_opc_func_update_unchanged_IF:
  !fext s s'.
    ((ID_opc_func_update fext s s').IF.IF_PC_input = s'.IF.IF_PC_input) /\
    ((ID_opc_func_update fext s s').IF.IF_instr = s'.IF.IF_instr) /\
    ((ID_opc_func_update fext s s').IF.IF_PC_write_enable = s'.IF.IF_PC_write_enable)
Proof
  rw [ID_opc_func_update_def]
QED

Theorem ID_imm_update_unchanged_IF:
  !fext s s'.
    ((ID_imm_update fext s s').IF.IF_PC_input = s'.IF.IF_PC_input) /\
    ((ID_imm_update fext s s').IF.IF_instr = s'.IF.IF_instr) /\
    ((ID_imm_update fext s s').IF.IF_PC_write_enable = s'.IF.IF_PC_write_enable)
Proof
  rw [ID_imm_update_def]
QED

Theorem ID_data_update_unchanged_IF:
  !fext s s'.
    ((ID_data_update fext s s').IF.IF_PC_input = s'.IF.IF_PC_input) /\
    ((ID_data_update fext s s').IF.IF_instr = s'.IF.IF_instr) /\
    ((ID_data_update fext s s').IF.IF_PC_write_enable = s'.IF.IF_PC_write_enable)
Proof
  rw [ID_data_update_def]
QED

Theorem EX_ctrl_update_unchanged_IF:
  !fext s s'.
    ((EX_ctrl_update fext s s').IF.IF_PC_input = s'.IF.IF_PC_input) /\
    ((EX_ctrl_update fext s s').IF.IF_instr = s'.IF.IF_instr) /\
    ((EX_ctrl_update fext s s').IF.IF_PC_write_enable = s'.IF.IF_PC_write_enable)
Proof
  rw [EX_ctrl_update_def]
QED

Theorem EX_forward_data_unchanged_IF:
  !fext s s'.
    ((EX_forward_data fext s s').IF.IF_PC_input = s'.IF.IF_PC_input) /\
    ((EX_forward_data fext s s').IF.IF_instr = s'.IF.IF_instr) /\
    ((EX_forward_data fext s s').IF.IF_PC_write_enable = s'.IF.IF_PC_write_enable)
Proof
  rw [EX_forward_data_def]
QED

Theorem EX_ALU_input_update_unchanged_IF:
  !fext s s'.
    ((EX_ALU_input_update fext s s').IF.IF_PC_input = s'.IF.IF_PC_input) /\  
    ((EX_ALU_input_update fext s s').IF.IF_instr = s'.IF.IF_instr) /\
    ((EX_ALU_input_update fext s s').IF.IF_PC_write_enable = s'.IF.IF_PC_write_enable)
Proof
  rw [EX_ALU_input_update_def]
QED

Theorem EX_compute_enable_update_unchanged_IF:
  !fext s s'.
    ((EX_compute_enable_update fext s s').IF.IF_PC_input = s'.IF.IF_PC_input) /\
    ((EX_compute_enable_update fext s s').IF.IF_instr = s'.IF.IF_instr) /\
    ((EX_compute_enable_update fext s s').IF.IF_PC_write_enable = s'.IF.IF_PC_write_enable)
Proof
  rw [EX_compute_enable_update_def]
QED

Theorem EX_ALU_update_unchanged_IF:
  !fext s s'.
    ((EX_ALU_update fext s s').IF.IF_PC_input = s'.IF.IF_PC_input) /\
    ((EX_ALU_update fext s s').IF.IF_instr = s'.IF.IF_instr) /\
    ((EX_ALU_update fext s s').IF.IF_PC_write_enable = s'.IF.IF_PC_write_enable)
Proof
  rw [EX_ALU_update_def] >>
  Cases_on_word_value `s'.EX.EX_func` >> fs []
QED

Theorem EX_SHIFT_update_unchanged_IF:
  !fext s s'.
    ((EX_SHIFT_update fext s s').IF.IF_PC_input = s'.IF.IF_PC_input) /\
    ((EX_SHIFT_update fext s s').IF.IF_instr = s'.IF.IF_instr) /\
    ((EX_SHIFT_update fext s s').IF.IF_PC_write_enable = s'.IF.IF_PC_write_enable)
Proof
  rw [EX_SHIFT_update_def] >>
  Cases_on_word_value `(1 >< 0) s'.EX.EX_func` >> fs []
QED

Theorem EX_jump_sel_addr_update_unchanged_IF:
  !fext s s'.
    ((EX_jump_sel_addr_update fext s s').IF.IF_PC_input = s'.IF.IF_PC_input) /\
    ((EX_jump_sel_addr_update fext s s').IF.IF_instr = s'.IF.IF_instr) /\
    ((EX_jump_sel_addr_update fext s s').IF.IF_PC_write_enable = s'.IF.IF_PC_write_enable)
Proof
  rw [EX_jump_sel_addr_update_def]
QED

Theorem EX_data_rec_update_unchanged_IF:
  !fext s s'.
    ((EX_data_rec_update fext s s').IF.IF_PC_input = s'.IF.IF_PC_input) /\   
    ((EX_data_rec_update fext s s').IF.IF_instr = s'.IF.IF_instr) /\
    ((EX_data_rec_update fext s s').IF.IF_PC_write_enable = s'.IF.IF_PC_write_enable)
Proof
  rw [EX_data_rec_update_def]
QED

Theorem MEM_ctrl_update_unchanged_IF:
  !fext s s'.
    ((MEM_ctrl_update fext s s').IF.IF_PC_input = s'.IF.IF_PC_input) /\
    ((MEM_ctrl_update fext s s').IF.IF_instr = s'.IF.IF_instr) /\
    ((MEM_ctrl_update fext s s').IF.IF_PC_write_enable = s'.IF.IF_PC_write_enable)
Proof
  rw [MEM_ctrl_update_def]
QED

Theorem MEM_imm_update_unchanged_IF:
  !fext s s'.
    ((MEM_imm_update fext s s').IF.IF_PC_input = s'.IF.IF_PC_input) /\
    ((MEM_imm_update fext s s').IF.IF_instr = s'.IF.IF_instr) /\
    ((MEM_imm_update fext s s').IF.IF_PC_write_enable = s'.IF.IF_PC_write_enable)
Proof
  rw [MEM_imm_update_def]
QED

Theorem WB_update_unchanged_IF:
  !fext s s'.
    ((WB_update fext s s').IF.IF_PC_input = s'.IF.IF_PC_input) /\
    ((WB_update fext s s').IF.IF_instr = s'.IF.IF_instr) /\
    ((WB_update fext s s').IF.IF_PC_write_enable = s'.IF.IF_PC_write_enable)
Proof
  rw [WB_update_def]
QED

(* EX_jump_sel/addr are not affected by irrelevant functions *)
Theorem Hazard_ctrl_unchanged_EX_jump:
  !fext s s'.
    ((Hazard_ctrl fext s s').EX.EX_jump_sel <=> s'.EX.EX_jump_sel) /\
    ((Hazard_ctrl fext s s').EX.EX_jump_addr = s'.EX.EX_jump_addr)
Proof
  rw [Hazard_ctrl_def]
QED

(* show the unchanged part of EX_state for functions used in the sequential logic *)
Theorem Acc_compute_unchanged_EX_jump:
  !fext s s'.
    ((Acc_compute fext s s').EX.EX_jump_sel <=> s'.EX.EX_jump_sel) /\
    ((Acc_compute fext s s').EX.EX_jump_addr = s'.EX.EX_jump_addr)
Proof
  rw [Acc_compute_def]
QED

Theorem IF_PC_update_unchanged_EX_jump:
  !fext s s'.
    ((IF_PC_update fext s s').EX.EX_jump_sel <=> s'.EX.EX_jump_sel) /\
    ((IF_PC_update fext s s').EX.EX_jump_addr = s'.EX.EX_jump_addr)
Proof
  rw [IF_PC_update_def]
QED

Theorem ID_pipeline_unchanged_EX_jump:
  !fext s s'.
    ((ID_pipeline fext s s').EX.EX_jump_sel <=> s'.EX.EX_jump_sel) /\
    ((ID_pipeline fext s s').EX.EX_jump_addr = s'.EX.EX_jump_addr)
Proof
  rw [ID_pipeline_def]
QED

Theorem REG_write_unchanged_EX_jump:
  !fext s s'.
    ((REG_write fext s s').EX.EX_jump_sel <=> s'.EX.EX_jump_sel) /\
    ((REG_write fext s s').EX.EX_jump_addr = s'.EX.EX_jump_addr)
Proof
  rw [REG_write_def]
QED

Theorem EX_pipeline_unchanged_EX_jump:
  !fext s s'.
    ((EX_pipeline fext s s').EX.EX_jump_sel <=> s'.EX.EX_jump_sel) /\
    ((EX_pipeline fext s s').EX.EX_jump_addr = s'.EX.EX_jump_addr)
Proof
  rw [EX_pipeline_def]
QED

Theorem MEM_pipeline_unchanged_EX_jump:
  !fext s s'.
    ((MEM_pipeline fext s s').EX.EX_jump_sel <=> s'.EX.EX_jump_sel) /\
    ((MEM_pipeline fext s s').EX.EX_jump_addr = s'.EX.EX_jump_addr)
Proof
  rw [MEM_pipeline_def]
QED

Theorem WB_pipeline_unchanged_EX_jump:
  !fext s s'.
    ((WB_pipeline fext s s').EX.EX_jump_sel <=> s'.EX.EX_jump_sel) /\
    ((WB_pipeline fext s s').EX.EX_jump_addr = s'.EX.EX_jump_addr)
Proof
  rw [WB_pipeline_def]
QED

Theorem agp32_next_state_unchanged_EX_jump:
  !fext s s'.
    ((agp32_next_state fext s s').EX.EX_jump_sel <=> s'.EX.EX_jump_sel) /\
    ((agp32_next_state fext s s').EX.EX_jump_addr = s'.EX.EX_jump_addr)
Proof
  rw [agp32_next_state_def] >>
  Cases_on_word_value `(1 >< 0) s.MEM.MEM_dataB` >> fs []
QED
     
Theorem slist_unchanged_EX_jump:
  !fext s s'.
    ((procs [agp32_next_state;WB_pipeline;MEM_pipeline;EX_pipeline;
             REG_write;ID_pipeline;IF_PC_update;Acc_compute]
      fext s s').EX.EX_jump_sel <=> s'.EX.EX_jump_sel) /\
    ((procs [agp32_next_state;WB_pipeline;MEM_pipeline;EX_pipeline;
             REG_write;ID_pipeline;IF_PC_update;Acc_compute]
      fext s s').EX.EX_jump_addr = s'.EX.EX_jump_addr)
Proof
  rw [] >> rw [Once procs_def] >>
  Q.ABBREV_TAC `s1 = agp32_next_state fext s s'` >>
  rw [Once procs_def] >>
  Q.ABBREV_TAC `s2 = WB_pipeline fext s s1` >>
  rw [Once procs_def] >>
  Q.ABBREV_TAC `s3 = MEM_pipeline fext s s2` >>
  rw [Once procs_def] >>
  Q.ABBREV_TAC `s4 = EX_pipeline fext s s3` >>
  rw [Once procs_def] >>
  Q.ABBREV_TAC `s5 = REG_write fext s s4` >>
  rw [Once procs_def] >>
  Q.ABBREV_TAC `s6 = ID_pipeline fext s s5` >>
  rw [Once procs_def] >>
  Q.ABBREV_TAC `s7 = IF_PC_update fext s s6` >>
  rw [Once procs_def] >>
  Q.ABBREV_TAC `s8 = Acc_compute fext s s7` >>
  fs [procs_def,Abbr `s8`,Acc_compute_unchanged_EX_jump,
      Abbr `s7`,IF_PC_update_unchanged_EX_jump,
      Abbr `s6`,ID_pipeline_unchanged_EX_jump,
      Abbr `s5`,REG_write_unchanged_EX_jump,
      Abbr `s4`,EX_pipeline_unchanged_EX_jump,
      Abbr `s3`,MEM_pipeline_unchanged_EX_jump,
      Abbr `s2`,WB_pipeline_unchanged_EX_jump,
      Abbr `s1`,agp32_next_state_unchanged_EX_jump]
QED

(* IF_PC_input is only changed by the IF_PC_input_update function *)
Theorem agp32_IF_PC_input_updated_by_IF_PC_input_update:
  !fext fbits t s s'.
    s = agp32 fext fbits t ==>
    s' = procs [agp32_next_state; WB_pipeline; MEM_pipeline; EX_pipeline;
                REG_write; ID_pipeline; IF_PC_update; Acc_compute]
               (fext t) s s ==>
    (agp32 fext fbits (SUC t)).IF.IF_PC_input =
    (IF_PC_input_update (fext (SUC t)) s' s).IF.IF_PC_input
Proof
  rw [agp32_def,mk_module_def,mk_circuit_def] >>
  qpat_abbrev_tac `s = mk_circuit (procs _) (procs _) (agp32_init fbits) fext t` >>
  qpat_abbrev_tac `s0 = procs _ (fext t) s s` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s1 = Hazard_ctrl _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s2 = ForwardA _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s3 = ForwardB _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s4 = ForwardW _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s4' = IF_instr_update _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s5 = IF_PC_input_update _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s6 = ID_opc_func_update _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s7 = ID_imm_update _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s8 = ID_data_update _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s9 = EX_ctrl_update _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s10 = EX_forward_data _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s11 = EX_ALU_input_update _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s12 = EX_compute_enable_update _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s13 = EX_ALU_update _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s14 = EX_SHIFT_update _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s15 = EX_jump_sel_addr_update _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s16 = EX_data_rec_update _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s17 = MEM_ctrl_update _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s18 = MEM_imm_update _ _ _` >>
  rw [procs_def] >>
  qpat_abbrev_tac `s19 = WB_update _ _ _` >>
  fs [Abbr `s19`,WB_update_unchanged_IF,
      Abbr `s18`,MEM_imm_update_unchanged_IF,
      Abbr `s17`,MEM_ctrl_update_unchanged_IF,
      Abbr `s16`,EX_data_rec_update_unchanged_IF,
      Abbr `s15`,EX_jump_sel_addr_update_unchanged_IF,
      Abbr `s14`,EX_SHIFT_update_unchanged_IF,
      Abbr `s13`,EX_ALU_update_unchanged_IF,
      Abbr `s12`,EX_compute_enable_update_unchanged_IF,
      Abbr `s11`,EX_ALU_input_update_unchanged_IF,
      Abbr `s10`,EX_forward_data_unchanged_IF,
      Abbr `s9`,EX_ctrl_update_unchanged_IF,
      Abbr `s8`,ID_data_update_unchanged_IF,
      Abbr `s7`,ID_imm_update_unchanged_IF,
      Abbr `s6`,ID_opc_func_update_unchanged_IF,
      Abbr `s5`,IF_PC_input_update_def,
      Abbr `s4'`,IF_instr_update_def,
      Abbr `s4`,ForwardW_def,Abbr `s3`,ForwardB_def,Abbr `s2`,ForwardA_def,
      Abbr `s1`,Hazard_ctrl_unchanged_EX_jump,
      Abbr `s0`,slist_unchanged_EX_jump]
QED

(* IF_instr is only changed by the IF_instr_update function *)
Theorem agp32_IF_instr_updated_by_IF_instr_update:
  !fext fbits t s s'.
    (agp32 fext fbits (SUC t)).IF.IF_instr =
    (IF_instr_update (fext (SUC t)) s s').IF.IF_instr
Proof
  rw [agp32_def,IF_instr_update_def,mk_module_def,mk_circuit_def] >>
  qpat_abbrev_tac `s = mk_circuit (procs _) (procs _) (agp32_init fbits) fext t` >>
  qpat_abbrev_tac `s' = procs _ (fext t) s s` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s1 = Hazard_ctrl _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s2 = ForwardA _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s3 = ForwardB _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s4 = ForwardW _ _ _` >>
  rw [Once procs_def,IF_instr_update_def] >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s5 = IF_PC_input_update _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s6 = ID_opc_func_update _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s7 = ID_imm_update _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s8 = ID_data_update _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s9 = EX_ctrl_update _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s10 = EX_forward_data _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s11 = EX_ALU_input_update _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s12 = EX_compute_enable_update _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s13 = EX_ALU_update _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s14 = EX_SHIFT_update _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s15 = EX_jump_sel_addr_update _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s16 = EX_data_rec_update _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s17 = MEM_ctrl_update _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s18 = MEM_imm_update _ _ _` >>
  rw [procs_def] >>
  qpat_abbrev_tac `s19 = WB_update _ _ _` >>
  fs [Abbr `s19`,WB_update_unchanged_IF,
      Abbr `s18`,MEM_imm_update_unchanged_IF,
      Abbr `s17`,MEM_ctrl_update_unchanged_IF,
      Abbr `s16`,EX_data_rec_update_unchanged_IF,
      Abbr `s15`,EX_jump_sel_addr_update_unchanged_IF,
      Abbr `s14`,EX_SHIFT_update_unchanged_IF,
      Abbr `s13`,EX_ALU_update_unchanged_IF,
      Abbr `s12`,EX_compute_enable_update_unchanged_IF,
      Abbr `s11`,EX_ALU_input_update_unchanged_IF,
      Abbr `s10`,EX_forward_data_unchanged_IF,
      Abbr `s9`,EX_ctrl_update_unchanged_IF,
      Abbr `s8`,ID_data_update_unchanged_IF,
      Abbr `s7`,ID_imm_update_unchanged_IF,
      Abbr `s6`,ID_opc_func_update_unchanged_IF,
      Abbr `s5`,IF_PC_input_update_unchanged_IF]
QED

val _ = export_theory ();
