open hardwarePreamble translatorTheory translatorLib arithmeticTheory dep_rewrite blastLib bitstringSyntax fcpSyntax listSyntax wordsSyntax wordsLib agp32StateTheory agp32EnvironmentTheory agp32ProcessorTheory;

val _ = new_theory "agp32Update";

val _ = prefer_num ();
val _ = guess_lengths ();

(* show the unchanged part of IF_state for functions used in the combinational logic *)
Theorem IF_PC_input_update_unchanged_IF:
  !fext s s'.
    (IF_PC_input_update fext s s').IF.IF_instr = s'.IF.IF_instr
Proof
  rw [IF_PC_input_update_def]
QED

Theorem ID_opc_func_update_unchanged_IF:
  !fext s s'.
    (ID_opc_func_update fext s s').IF.IF_instr = s'.IF.IF_instr
Proof
  rw [ID_opc_func_update_def]
QED

Theorem ID_imm_update_unchanged_IF:
  !fext s s'.
    (ID_imm_update fext s s').IF.IF_instr = s'.IF.IF_instr
Proof
  rw [ID_imm_update_def]
QED

Theorem ID_data_update_unchanged_IF:
  !fext s s'.
    (ID_data_update fext s s').IF.IF_instr = s'.IF.IF_instr
Proof
  rw [ID_data_update_def]
QED

Theorem EX_ctrl_update_unchanged_IF:
  !fext s s'.
    (EX_ctrl_update fext s s').IF.IF_instr = s'.IF.IF_instr
Proof
  rw [EX_ctrl_update_def]
QED

Theorem EX_forward_data_unchanged_IF:
  !fext s s'.
    (EX_forward_data fext s s').IF.IF_instr = s'.IF.IF_instr
Proof
  rw [EX_forward_data_def]
QED

Theorem EX_ALU_input_update_unchanged_IF:
  !fext s s'.
    (EX_ALU_input_update fext s s').IF.IF_instr = s'.IF.IF_instr
Proof
  rw [EX_ALU_input_update_def]
QED

Theorem EX_compute_enable_update_unchanged_IF:
  !fext s s'.
    (EX_compute_enable_update fext s s').IF.IF_instr = s'.IF.IF_instr
Proof
  rw [EX_compute_enable_update_def]
QED

Theorem EX_ALU_update_unchanged_IF:
  !fext s s'.
    (EX_ALU_update fext s s').IF.IF_instr = s'.IF.IF_instr
Proof
  rw [EX_ALU_update_def] >>
  Cases_on_word_value `s'.EX.EX_func` >> fs []
QED

Theorem EX_SHIFT_update_unchanged_IF:
  !fext s s'.
    (EX_SHIFT_update fext s s').IF.IF_instr = s'.IF.IF_instr
Proof
  rw [EX_SHIFT_update_def] >>
  Cases_on_word_value `(1 >< 0) s'.EX.EX_func` >> fs []
QED

Theorem EX_jump_sel_addr_update_unchanged_IF:
  !fext s s'.
    (EX_jump_sel_addr_update fext s s').IF.IF_instr = s'.IF.IF_instr
Proof
  rw [EX_jump_sel_addr_update_def]
QED

Theorem EX_data_rec_update_unchanged_IF:
  !fext s s'.
    (EX_data_rec_update fext s s').IF.IF_instr = s'.IF.IF_instr
Proof
  rw [EX_data_rec_update_def]
QED

Theorem MEM_ctrl_update_unchanged_IF:
  !fext s s'.
    (MEM_ctrl_update fext s s').IF.IF_instr = s'.IF.IF_instr
Proof
  rw [MEM_ctrl_update_def]
QED

Theorem MEM_imm_update_unchanged_IF:
  !fext s s'.
    (MEM_imm_update fext s s').IF.IF_instr = s'.IF.IF_instr
Proof
  rw [MEM_imm_update_def]
QED

Theorem WB_update_unchanged_IF:
  !fext s s'.
    (WB_update fext s s').IF.IF_instr = s'.IF.IF_instr
Proof
  rw [WB_update_def]
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
