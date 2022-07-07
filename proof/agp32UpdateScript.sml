open hardwarePreamble translatorTheory arithmeticTheory dep_rewrite blastLib bitstringSyntax fcpSyntax listSyntax wordsSyntax wordsLib agp32StateTheory agp32EnvironmentTheory agp32ProcessorTheory;

(* Theorems about the pipelined circuit's state update functions *)
val _ = new_theory "agp32Update";

val _ = prefer_num ();
val _ = guess_lengths ();

(* tactic shorthand used for the proof *)
val  clist_update_state_tac =
 (rw [Once procs_def] >>
  qpat_abbrev_tac `s1 = ForwardA _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s2 = ForwardB _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s3 = ForwardW _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s4 = IF_instr_update _ _ _` >>
  rw [Once procs_def] >>  
  qpat_abbrev_tac `s5 = ID_opc_func_update _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s6 = ID_imm_update _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s7 = ID_data_update _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s8 = EX_ctrl_update _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s9 = EX_forward_data _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s10 = EX_ALU_input_update _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s11 = EX_compute_enable_update _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s12 = EX_ALU_update _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s13 = EX_SHIFT_update _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s14 = EX_jump_sel_addr_update _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s15 = EX_data_rec_update _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s16 = IF_PC_input_update _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s17 = MEM_ctrl_update _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s18 = MEM_imm_update _ _ _` >>
  rw [procs_def] >>
  qpat_abbrev_tac `s19 = WB_update _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s20 = Hazard_ctrl _ _ _`);

val clist_update_state_before_ALU_tac =
 (rw [] >> Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  qpat_abbrev_tac `s' = procs _ (fext t) s s` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s1 = ForwardA _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s2 = ForwardB _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s3 = ForwardW _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s4 = IF_instr_update _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s5 = ID_opc_func_update _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s6 = ID_imm_update _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s7 = ID_data_update _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s8 = EX_ctrl_update _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s9 = EX_forward_data _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s10 = EX_ALU_input_update _ _ _` >>
  rw [procs_def] >>
  qpat_abbrev_tac `s11 = EX_compute_enable_update _ _ _`);

val slist_update_state_tac =
 (rw [Once procs_def] >>
  qpat_abbrev_tac `ss1 = agp32_next_state _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `ss2 = WB_pipeline _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `ss3 = MEM_pipeline _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `ss4 = EX_pipeline _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `ss5 = REG_write _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `ss6 = ID_pipeline _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `ss7 = IF_PC_update _ _ _` >>
  rw [procs_def] >>
  qpat_abbrev_tac `ss8 = Acc_compute _ _ _`);

(* show the unchanged part of different circuit functions in the pipelined Silver *)
(** unchanged items by IF_PC_input_update **)
Theorem IF_PC_input_update_unchanged_IF:
  !fext s s'.
    ((IF_PC_input_update fext s s').IF.IF_instr = s'.IF.IF_instr) /\
    ((IF_PC_input_update fext s s').IF.IF_PC_write_enable = s'.IF.IF_PC_write_enable) /\
    ((IF_PC_input_update fext s s').PC = s'.PC)
Proof
  rw [IF_PC_input_update_def]
QED

(** unchanged items by ID_opc_func_update **)
Theorem ID_opc_func_update_unchanged_IF:
  !fext s s'.
    ((ID_opc_func_update fext s s').IF.IF_PC_input = s'.IF.IF_PC_input) /\
    ((ID_opc_func_update fext s s').IF.IF_instr = s'.IF.IF_instr) /\
    ((ID_opc_func_update fext s s').IF.IF_PC_write_enable = s'.IF.IF_PC_write_enable) /\
    ((ID_opc_func_update fext s s').PC = s'.PC)
Proof
  rw [ID_opc_func_update_def]
QED

Theorem ID_opc_func_update_unchanged_EX_pipeline_items:
  !fext s s'.
    ((ID_opc_func_update fext s s').EX.EX_PC = s'.EX.EX_PC) /\
    ((ID_opc_func_update fext s s').EX.EX_dataA = s'.EX.EX_dataA) /\
    ((ID_opc_func_update fext s s').EX.EX_dataB = s'.EX.EX_dataB) /\
    ((ID_opc_func_update fext s s').EX.EX_dataW = s'.EX.EX_dataW) /\
    ((ID_opc_func_update fext s s').EX.EX_imm = s'.EX.EX_imm) /\
    ((ID_opc_func_update fext s s').EX.EX_write_enable <=> s'.EX.EX_write_enable) /\
    ((ID_opc_func_update fext s s').EX.EX_addrA_disable <=> s'.EX.EX_addrA_disable) /\
    ((ID_opc_func_update fext s s').EX.EX_addrB_disable <=> s'.EX.EX_addrB_disable) /\
    ((ID_opc_func_update fext s s').EX.EX_addrW_disable <=> s'.EX.EX_addrW_disable) /\
    ((ID_opc_func_update fext s s').EX.EX_addrA = s'.EX.EX_addrA) /\
    ((ID_opc_func_update fext s s').EX.EX_addrB = s'.EX.EX_addrB) /\
    ((ID_opc_func_update fext s s').EX.EX_addrW = s'.EX.EX_addrW) /\
    ((ID_opc_func_update fext s s').EX.EX_opc = s'.EX.EX_opc) /\
    ((ID_opc_func_update fext s s').EX.EX_func = s'.EX.EX_func)
Proof
  rw [ID_opc_func_update_def]
QED

Theorem ID_opc_func_update_unchanged_EX_ALU:
  !fext s s'.
    ((ID_opc_func_update fext s s').EX.EX_ALU_res = s'.EX.EX_ALU_res) /\
    ((ID_opc_func_update fext s s').EX.EX_carry_flag = s'.EX.EX_carry_flag) /\
    ((ID_opc_func_update fext s s').EX.EX_overflow_flag = s'.EX.EX_overflow_flag)
Proof
  rw [ID_opc_func_update_def]
QED

Theorem ID_opc_func_update_unchanged_state_items:
  !fext s s'.
    ((ID_opc_func_update fext s s').command = s'.command) /\
    ((ID_opc_func_update fext s s').state = s'.state)
Proof
  rw [ID_opc_func_update_def]
QED

(** unchanged items by ID_imm_update **)
Theorem ID_imm_update_unchanged_IF:
  !fext s s'.
    ((ID_imm_update fext s s').IF.IF_PC_input = s'.IF.IF_PC_input) /\
    ((ID_imm_update fext s s').IF.IF_instr = s'.IF.IF_instr) /\
    ((ID_imm_update fext s s').IF.IF_PC_write_enable = s'.IF.IF_PC_write_enable) /\
    ((ID_imm_update fext s s').PC = s'.PC)                
Proof
  rw [ID_imm_update_def]
QED

Theorem ID_imm_update_unchanged_ID_opc_func:
  !fext s s'.
    ((ID_imm_update fext s s').ID.ID_opc = s'.ID.ID_opc) /\
    ((ID_imm_update fext s s').ID.ID_func = s'.ID.ID_func)
Proof
  rw [ID_imm_update_def]
QED

Theorem ID_imm_update_unchanged_EX_pipeline_items:
  !fext s s'.
    ((ID_imm_update fext s s').EX.EX_PC = s'.EX.EX_PC) /\
    ((ID_imm_update fext s s').EX.EX_dataA = s'.EX.EX_dataA) /\
    ((ID_imm_update fext s s').EX.EX_dataB = s'.EX.EX_dataB) /\
    ((ID_imm_update fext s s').EX.EX_dataW = s'.EX.EX_dataW) /\
    ((ID_imm_update fext s s').EX.EX_imm = s'.EX.EX_imm) /\
    ((ID_imm_update fext s s').EX.EX_write_enable <=> s'.EX.EX_write_enable) /\
    ((ID_imm_update fext s s').EX.EX_addrA_disable <=> s'.EX.EX_addrA_disable) /\
    ((ID_imm_update fext s s').EX.EX_addrB_disable <=> s'.EX.EX_addrB_disable) /\
    ((ID_imm_update fext s s').EX.EX_addrW_disable <=> s'.EX.EX_addrW_disable) /\
    ((ID_imm_update fext s s').EX.EX_addrA = s'.EX.EX_addrA) /\
    ((ID_imm_update fext s s').EX.EX_addrB = s'.EX.EX_addrB) /\
    ((ID_imm_update fext s s').EX.EX_addrW = s'.EX.EX_addrW) /\
    ((ID_imm_update fext s s').EX.EX_opc = s'.EX.EX_opc) /\
    ((ID_imm_update fext s s').EX.EX_func = s'.EX.EX_func)
Proof
  rw [ID_imm_update_def]
QED

Theorem ID_imm_update_unchanged_EX_ALU:
  !fext s s'.
    ((ID_imm_update fext s s').EX.EX_ALU_res = s'.EX.EX_ALU_res) /\
    ((ID_imm_update fext s s').EX.EX_carry_flag = s'.EX.EX_carry_flag) /\
    ((ID_imm_update fext s s').EX.EX_overflow_flag = s'.EX.EX_overflow_flag)
Proof
  rw [ID_imm_update_def]
QED

Theorem ID_imm_update_unchanged_state_items:
  !fext s s'.
    ((ID_imm_update fext s s').command = s'.command) /\
    ((ID_imm_update fext s s').state = s'.state)
Proof
  rw [ID_imm_update_def]
QED

(** unchanged items by ID_data_update **)
Theorem ID_data_update_unchanged_IF:
  !fext s s'.
    ((ID_data_update fext s s').IF.IF_PC_input = s'.IF.IF_PC_input) /\
    ((ID_data_update fext s s').IF.IF_instr = s'.IF.IF_instr) /\
    ((ID_data_update fext s s').IF.IF_PC_write_enable = s'.IF.IF_PC_write_enable) /\
    ((ID_data_update fext s s').PC = s'.PC)
Proof
  rw [ID_data_update_def]
QED

Theorem ID_data_update_unchanged_ID_opc_func:
  !fext s s'.
    ((ID_data_update fext s s').ID.ID_opc = s'.ID.ID_opc) /\
    ((ID_data_update fext s s').ID.ID_func = s'.ID.ID_func)
Proof
  rw [ID_data_update_def]
QED

Theorem ID_data_update_unchanged_EX_pipeline_items:
  !fext s s'.
    ((ID_data_update fext s s').EX.EX_PC = s'.EX.EX_PC) /\
    ((ID_data_update fext s s').EX.EX_dataA = s'.EX.EX_dataA) /\
    ((ID_data_update fext s s').EX.EX_dataB = s'.EX.EX_dataB) /\
    ((ID_data_update fext s s').EX.EX_dataW = s'.EX.EX_dataW) /\
    ((ID_data_update fext s s').EX.EX_imm = s'.EX.EX_imm) /\
    ((ID_data_update fext s s').EX.EX_write_enable <=> s'.EX.EX_write_enable) /\
    ((ID_data_update fext s s').EX.EX_addrA_disable <=> s'.EX.EX_addrA_disable) /\
    ((ID_data_update fext s s').EX.EX_addrB_disable <=> s'.EX.EX_addrB_disable) /\
    ((ID_data_update fext s s').EX.EX_addrW_disable <=> s'.EX.EX_addrW_disable) /\
    ((ID_data_update fext s s').EX.EX_addrA = s'.EX.EX_addrA) /\
    ((ID_data_update fext s s').EX.EX_addrB = s'.EX.EX_addrB) /\
    ((ID_data_update fext s s').EX.EX_addrW = s'.EX.EX_addrW) /\
    ((ID_data_update fext s s').EX.EX_opc = s'.EX.EX_opc) /\
    ((ID_data_update fext s s').EX.EX_func = s'.EX.EX_func)
Proof
  rw [ID_data_update_def]
QED

Theorem ID_data_update_unchanged_EX_ALU:
  !fext s s'.
    ((ID_data_update fext s s').EX.EX_ALU_res = s'.EX.EX_ALU_res) /\
    ((ID_data_update fext s s').EX.EX_carry_flag = s'.EX.EX_carry_flag) /\
    ((ID_data_update fext s s').EX.EX_overflow_flag = s'.EX.EX_overflow_flag)
Proof
  rw [ID_data_update_def]
QED

Theorem ID_data_update_unchanged_state_items:
  !fext s s'.
    ((ID_data_update fext s s').command = s'.command) /\
    ((ID_data_update fext s s').state = s'.state)
Proof
  rw [ID_data_update_def]
QED

(** unchanged items by EX_ctrl_update **)
Theorem EX_ctrl_update_unchanged_IF:
  !fext s s'.
    ((EX_ctrl_update fext s s').IF.IF_PC_input = s'.IF.IF_PC_input) /\
    ((EX_ctrl_update fext s s').IF.IF_instr = s'.IF.IF_instr) /\
    ((EX_ctrl_update fext s s').IF.IF_PC_write_enable = s'.IF.IF_PC_write_enable) /\
    ((EX_ctrl_update fext s s').PC = s'.PC)
Proof
  rw [EX_ctrl_update_def]
QED

Theorem EX_ctrl_update_unchanged_ID_opc_func:
  !fext s s'.
    ((EX_ctrl_update fext s s').ID.ID_opc = s'.ID.ID_opc) /\
    ((EX_ctrl_update fext s s').ID.ID_func = s'.ID.ID_func)
Proof
  rw [EX_ctrl_update_def]
QED

Theorem EX_ctrl_update_unchanged_EX_pipeline_items:
  !fext s s'.
    ((EX_ctrl_update fext s s').EX.EX_PC = s'.EX.EX_PC) /\
    ((EX_ctrl_update fext s s').EX.EX_dataA = s'.EX.EX_dataA) /\
    ((EX_ctrl_update fext s s').EX.EX_dataB = s'.EX.EX_dataB) /\
    ((EX_ctrl_update fext s s').EX.EX_dataW = s'.EX.EX_dataW) /\
    ((EX_ctrl_update fext s s').EX.EX_imm = s'.EX.EX_imm) /\
    ((EX_ctrl_update fext s s').EX.EX_write_enable <=> s'.EX.EX_write_enable) /\
    ((EX_ctrl_update fext s s').EX.EX_addrA_disable <=> s'.EX.EX_addrA_disable) /\
    ((EX_ctrl_update fext s s').EX.EX_addrB_disable <=> s'.EX.EX_addrB_disable) /\
    ((EX_ctrl_update fext s s').EX.EX_addrW_disable <=> s'.EX.EX_addrW_disable) /\
    ((EX_ctrl_update fext s s').EX.EX_addrA = s'.EX.EX_addrA) /\
    ((EX_ctrl_update fext s s').EX.EX_addrB = s'.EX.EX_addrB) /\
    ((EX_ctrl_update fext s s').EX.EX_addrW = s'.EX.EX_addrW) /\
    ((EX_ctrl_update fext s s').EX.EX_opc = s'.EX.EX_opc) /\
    ((EX_ctrl_update fext s s').EX.EX_func = s'.EX.EX_func)
Proof
  rw [EX_ctrl_update_def]
QED

Theorem EX_ctrl_update_unchanged_EX_ALU:
  !fext s s'.
    ((EX_ctrl_update fext s s').EX.EX_ALU_res = s'.EX.EX_ALU_res) /\
    ((EX_ctrl_update fext s s').EX.EX_carry_flag = s'.EX.EX_carry_flag) /\
    ((EX_ctrl_update fext s s').EX.EX_overflow_flag = s'.EX.EX_overflow_flag)
Proof
  rw [EX_ctrl_update_def]
QED
        
Theorem EX_ctrl_update_unchanged_state_items:
  !fext s s'.
    ((EX_ctrl_update fext s s').command = s'.command) /\
    ((EX_ctrl_update fext s s').state = s'.state)
Proof
  rw [EX_ctrl_update_def]
QED

(** unchanged items by EX_forward_data **)
Theorem EX_forward_data_unchanged_IF:
  !fext s s'.
    ((EX_forward_data fext s s').IF.IF_PC_input = s'.IF.IF_PC_input) /\
    ((EX_forward_data fext s s').IF.IF_instr = s'.IF.IF_instr) /\
    ((EX_forward_data fext s s').IF.IF_PC_write_enable = s'.IF.IF_PC_write_enable) /\
    ((EX_forward_data fext s s').PC = s'.PC)
Proof
  rw [EX_forward_data_def]
QED

Theorem EX_forward_data_unchanged_state_items:
  !fext s s'.
    ((EX_forward_data fext s s').command = s'.command) /\
    ((EX_forward_data fext s s').state = s'.state)
Proof
  rw [EX_forward_data_def]
QED

(** unchanged items by EX_ALU_input_update **)
Theorem EX_ALU_input_update_unchanged_IF:
  !fext s s'.
    ((EX_ALU_input_update fext s s').IF.IF_PC_input = s'.IF.IF_PC_input) /\  
    ((EX_ALU_input_update fext s s').IF.IF_instr = s'.IF.IF_instr) /\
    ((EX_ALU_input_update fext s s').IF.IF_PC_write_enable = s'.IF.IF_PC_write_enable) /\
    ((EX_ALU_input_update fext s s').PC = s'.PC)
Proof
  rw [EX_ALU_input_update_def]
QED

Theorem EX_ALU_input_update_unchanged_state_items:
  !fext s s'.
    ((EX_ALU_input_update fext s s').command = s'.command) /\
    ((EX_ALU_input_update fext s s').state = s'.state)
Proof
  rw [EX_ALU_input_update_def]
QED

(** unchanged items by EX_compute_enable_update **)
Theorem EX_compute_enable_update_unchanged_IF:
  !fext s s'.
    ((EX_compute_enable_update fext s s').IF.IF_PC_input = s'.IF.IF_PC_input) /\
    ((EX_compute_enable_update fext s s').IF.IF_instr = s'.IF.IF_instr) /\
    ((EX_compute_enable_update fext s s').IF.IF_PC_write_enable = s'.IF.IF_PC_write_enable) /\
    ((EX_compute_enable_update fext s s').PC = s'.PC)
Proof
  rw [EX_compute_enable_update_def]
QED

Theorem EX_compute_enable_update_unchanged_state_items:
  !fext s s'.
    ((EX_compute_enable_update fext s s').command = s'.command) /\
    ((EX_compute_enable_update fext s s').state = s'.state)
Proof
  rw [EX_compute_enable_update_def]
QED

(** unchanged items by EX_ALU_update **)
Theorem EX_ALU_update_unchanged_IF:
  !fext s s'.
    ((EX_ALU_update fext s s').IF.IF_PC_input = s'.IF.IF_PC_input) /\
    ((EX_ALU_update fext s s').IF.IF_instr = s'.IF.IF_instr) /\
    ((EX_ALU_update fext s s').IF.IF_PC_write_enable = s'.IF.IF_PC_write_enable) /\
    ((EX_ALU_update fext s s').PC = s'.PC)                
Proof
  rw [EX_ALU_update_def] >>
  Cases_on_word_value `s'.EX.EX_func` >> fs []
QED

Theorem EX_ALU_update_unchanged_ID_opc_func:
  !fext s s'.
    ((EX_ALU_update fext s s').ID.ID_opc = s'.ID.ID_opc) /\
    ((EX_ALU_update fext s s').ID.ID_func = s'.ID.ID_func)
Proof
  rw [EX_ALU_update_def] >>
  Cases_on_word_value `s'.EX.EX_func` >> fs []
QED

Theorem EX_ALU_update_unchanged_EX_pipeline_items:
  !fext s s'.
    ((EX_ALU_update fext s s').EX.EX_PC = s'.EX.EX_PC) /\
    ((EX_ALU_update fext s s').EX.EX_dataA = s'.EX.EX_dataA) /\
    ((EX_ALU_update fext s s').EX.EX_dataB = s'.EX.EX_dataB) /\
    ((EX_ALU_update fext s s').EX.EX_dataW = s'.EX.EX_dataW) /\
    ((EX_ALU_update fext s s').EX.EX_imm = s'.EX.EX_imm) /\
    ((EX_ALU_update fext s s').EX.EX_write_enable <=> s'.EX.EX_write_enable) /\
    ((EX_ALU_update fext s s').EX.EX_addrA_disable <=> s'.EX.EX_addrA_disable) /\
    ((EX_ALU_update fext s s').EX.EX_addrB_disable <=> s'.EX.EX_addrB_disable) /\
    ((EX_ALU_update fext s s').EX.EX_addrW_disable <=> s'.EX.EX_addrW_disable) /\
    ((EX_ALU_update fext s s').EX.EX_addrA = s'.EX.EX_addrA) /\
    ((EX_ALU_update fext s s').EX.EX_addrB = s'.EX.EX_addrB) /\
    ((EX_ALU_update fext s s').EX.EX_addrW = s'.EX.EX_addrW) /\
    ((EX_ALU_update fext s s').EX.EX_opc = s'.EX.EX_opc) /\
    ((EX_ALU_update fext s s').EX.EX_func = s'.EX.EX_func)
Proof
  rw [EX_ALU_update_def] >>
  Cases_on_word_value `s'.EX.EX_func` >> fs []
QED

Theorem EX_ALU_update_unchanged_state_items:
  !fext s s'.
    ((EX_ALU_update fext s s').command = s'.command) /\
    ((EX_ALU_update fext s s').state = s'.state)
Proof
  rw [EX_ALU_update_def] >>
  Cases_on_word_value `s'.EX.EX_func` >> fs []
QED

(** unchanged items by EX_SHIFT_update **)
Theorem EX_SHIFT_update_unchanged_IF:
  !fext s s'.
    ((EX_SHIFT_update fext s s').IF.IF_PC_input = s'.IF.IF_PC_input) /\
    ((EX_SHIFT_update fext s s').IF.IF_instr = s'.IF.IF_instr) /\
    ((EX_SHIFT_update fext s s').IF.IF_PC_write_enable = s'.IF.IF_PC_write_enable) /\
    ((EX_SHIFT_update fext s s').PC = s'.PC)                  
Proof
  rw [EX_SHIFT_update_def] >>
  Cases_on_word_value `(1 >< 0) s'.EX.EX_func` >> fs []
QED

Theorem EX_SHIFT_update_unchanged_ID_opc_func:
  !fext s s'.
    ((EX_SHIFT_update fext s s').ID.ID_opc = s'.ID.ID_opc) /\
    ((EX_SHIFT_update fext s s').ID.ID_func = s'.ID.ID_func)
Proof
  rw [EX_SHIFT_update_def] >>
  Cases_on_word_value `(1 >< 0) s'.EX.EX_func` >> fs []
QED

Theorem EX_SHIFT_update_unchanged_EX_ALU:
  !fext s s'.
    ((EX_SHIFT_update fext s s').EX.EX_ALU_res = s'.EX.EX_ALU_res) /\
    ((EX_SHIFT_update fext s s').EX.EX_carry_flag = s'.EX.EX_carry_flag) /\
    ((EX_SHIFT_update fext s s').EX.EX_overflow_flag = s'.EX.EX_overflow_flag)
Proof
  rw [EX_SHIFT_update_def] >>
  Cases_on_word_value `(1 >< 0) s'.EX.EX_func` >> fs []
QED

Theorem EX_SHIFT_update_unchanged_EX_pipeline_items:
  !fext s s'.
    ((EX_SHIFT_update fext s s').EX.EX_PC = s'.EX.EX_PC) /\
    ((EX_SHIFT_update fext s s').EX.EX_dataA = s'.EX.EX_dataA) /\
    ((EX_SHIFT_update fext s s').EX.EX_dataB = s'.EX.EX_dataB) /\
    ((EX_SHIFT_update fext s s').EX.EX_dataW = s'.EX.EX_dataW) /\
    ((EX_SHIFT_update fext s s').EX.EX_imm = s'.EX.EX_imm) /\
    ((EX_SHIFT_update fext s s').EX.EX_write_enable <=> s'.EX.EX_write_enable) /\
    ((EX_SHIFT_update fext s s').EX.EX_addrA_disable <=> s'.EX.EX_addrA_disable) /\
    ((EX_SHIFT_update fext s s').EX.EX_addrB_disable <=> s'.EX.EX_addrB_disable) /\
    ((EX_SHIFT_update fext s s').EX.EX_addrW_disable <=> s'.EX.EX_addrW_disable) /\
    ((EX_SHIFT_update fext s s').EX.EX_addrA = s'.EX.EX_addrA) /\
    ((EX_SHIFT_update fext s s').EX.EX_addrB = s'.EX.EX_addrB) /\
    ((EX_SHIFT_update fext s s').EX.EX_addrW = s'.EX.EX_addrW) /\
    ((EX_SHIFT_update fext s s').EX.EX_opc = s'.EX.EX_opc) /\
    ((EX_SHIFT_update fext s s').EX.EX_func = s'.EX.EX_func)
Proof
  rw [EX_SHIFT_update_def] >>
  Cases_on_word_value `(1 >< 0) s'.EX.EX_func` >> fs []
QED

Theorem EX_SHIFT_update_unchanged_state_items:
  !fext s s'.
    ((EX_SHIFT_update fext s s').command = s'.command) /\
    ((EX_SHIFT_update fext s s').state = s'.state)
Proof
  rw [EX_SHIFT_update_def] >>
  Cases_on_word_value `(1 >< 0) s'.EX.EX_func` >> fs []
QED

(** unchanged items by EX_jump_sel_addr_update **)
Theorem EX_jump_sel_addr_update_unchanged_IF:
  !fext s s'.
    ((EX_jump_sel_addr_update fext s s').IF.IF_PC_input = s'.IF.IF_PC_input) /\
    ((EX_jump_sel_addr_update fext s s').IF.IF_instr = s'.IF.IF_instr) /\
    ((EX_jump_sel_addr_update fext s s').IF.IF_PC_write_enable = s'.IF.IF_PC_write_enable) /\
    ((EX_jump_sel_addr_update fext s s').PC = s'.PC)
Proof
  rw [EX_jump_sel_addr_update_def]
QED

Theorem EX_jump_sel_addr_update_unchanged_ID_opc_func:
  !fext s s'.
    ((EX_jump_sel_addr_update fext s s').ID.ID_opc = s'.ID.ID_opc) /\
    ((EX_jump_sel_addr_update fext s s').ID.ID_func = s'.ID.ID_func)
Proof
  rw [EX_jump_sel_addr_update_def]
QED

Theorem EX_jump_sel_addr_update_unchanged_EX_ALU:
  !fext s s'.
    ((EX_jump_sel_addr_update fext s s').EX.EX_ALU_res = s'.EX.EX_ALU_res) /\
    ((EX_jump_sel_addr_update fext s s').EX.EX_carry_flag = s'.EX.EX_carry_flag) /\
    ((EX_jump_sel_addr_update fext s s').EX.EX_overflow_flag = s'.EX.EX_overflow_flag)
Proof
  rw [EX_jump_sel_addr_update_def]
QED

Theorem EX_jump_sel_addr_update_unchanged_EX_pipeline_items:
  !fext s s'.
    ((EX_jump_sel_addr_update fext s s').EX.EX_PC = s'.EX.EX_PC) /\
    ((EX_jump_sel_addr_update fext s s').EX.EX_dataA = s'.EX.EX_dataA) /\
    ((EX_jump_sel_addr_update fext s s').EX.EX_dataB = s'.EX.EX_dataB) /\
    ((EX_jump_sel_addr_update fext s s').EX.EX_dataW = s'.EX.EX_dataW) /\
    ((EX_jump_sel_addr_update fext s s').EX.EX_imm = s'.EX.EX_imm) /\
    ((EX_jump_sel_addr_update fext s s').EX.EX_write_enable <=> s'.EX.EX_write_enable) /\
    ((EX_jump_sel_addr_update fext s s').EX.EX_addrA_disable <=> s'.EX.EX_addrA_disable) /\
    ((EX_jump_sel_addr_update fext s s').EX.EX_addrB_disable <=> s'.EX.EX_addrB_disable) /\
    ((EX_jump_sel_addr_update fext s s').EX.EX_addrW_disable <=> s'.EX.EX_addrW_disable) /\
    ((EX_jump_sel_addr_update fext s s').EX.EX_addrA = s'.EX.EX_addrA) /\
    ((EX_jump_sel_addr_update fext s s').EX.EX_addrB = s'.EX.EX_addrB) /\
    ((EX_jump_sel_addr_update fext s s').EX.EX_addrW = s'.EX.EX_addrW) /\
    ((EX_jump_sel_addr_update fext s s').EX.EX_opc = s'.EX.EX_opc) /\
    ((EX_jump_sel_addr_update fext s s').EX.EX_func = s'.EX.EX_func)
Proof
  rw [EX_jump_sel_addr_update_def]
QED
     
Theorem EX_jump_sel_addr_update_unchanged_state_items:
  !fext s s'.
    ((EX_jump_sel_addr_update fext s s').command = s'.command) /\
    ((EX_jump_sel_addr_update fext s s').state = s'.state)
Proof
  rw [EX_jump_sel_addr_update_def]
QED

(** unchanged items by EX_data_rec_update **)
Theorem EX_data_rec_update_unchanged_IF:
  !fext s s'.
    ((EX_data_rec_update fext s s').IF.IF_PC_input = s'.IF.IF_PC_input) /\   
    ((EX_data_rec_update fext s s').IF.IF_instr = s'.IF.IF_instr) /\
    ((EX_data_rec_update fext s s').IF.IF_PC_write_enable = s'.IF.IF_PC_write_enable) /\
    ((EX_data_rec_update fext s s').PC = s'.PC)
Proof
  rw [EX_data_rec_update_def]
QED

Theorem EX_data_rec_update_unchanged_ID_opc_func:
  !fext s s'.
    ((EX_data_rec_update fext s s').ID.ID_opc = s'.ID.ID_opc) /\   
    ((EX_data_rec_update fext s s').ID.ID_func = s'.ID.ID_func)
Proof
  rw [EX_data_rec_update_def]
QED

Theorem EX_data_rec_update_unchanged_EX_ALU:
  !fext s s'.
    ((EX_data_rec_update fext s s').EX.EX_ALU_res = s'.EX.EX_ALU_res) /\   
    ((EX_data_rec_update fext s s').EX.EX_carry_flag = s'.EX.EX_carry_flag) /\
    ((EX_data_rec_update fext s s').EX.EX_overflow_flag = s'.EX.EX_overflow_flag)
Proof
  rw [EX_data_rec_update_def]
QED

Theorem EX_data_rec_update_unchanged_EX_pipeline_items:
  !fext s s'.
    ((EX_data_rec_update fext s s').EX.EX_PC = s'.EX.EX_PC) /\
    ((EX_data_rec_update fext s s').EX.EX_dataA = s'.EX.EX_dataA) /\
    ((EX_data_rec_update fext s s').EX.EX_dataB = s'.EX.EX_dataB) /\
    ((EX_data_rec_update fext s s').EX.EX_dataW = s'.EX.EX_dataW) /\
    ((EX_data_rec_update fext s s').EX.EX_imm = s'.EX.EX_imm) /\
    ((EX_data_rec_update fext s s').EX.EX_write_enable <=> s'.EX.EX_write_enable) /\
    ((EX_data_rec_update fext s s').EX.EX_addrA_disable <=> s'.EX.EX_addrA_disable) /\
    ((EX_data_rec_update fext s s').EX.EX_addrB_disable <=> s'.EX.EX_addrB_disable) /\
    ((EX_data_rec_update fext s s').EX.EX_addrW_disable <=> s'.EX.EX_addrW_disable) /\
    ((EX_data_rec_update fext s s').EX.EX_addrA = s'.EX.EX_addrA) /\
    ((EX_data_rec_update fext s s').EX.EX_addrB = s'.EX.EX_addrB) /\
    ((EX_data_rec_update fext s s').EX.EX_addrW = s'.EX.EX_addrW) /\
    ((EX_data_rec_update fext s s').EX.EX_opc = s'.EX.EX_opc) /\
    ((EX_data_rec_update fext s s').EX.EX_func = s'.EX.EX_func)
Proof
  rw [EX_data_rec_update_def]
QED

Theorem EX_data_rec_update_unchanged_state_items:
  !fext s s'.
    ((EX_data_rec_update fext s s').command = s'.command) /\
    ((EX_data_rec_update fext s s').state = s'.state)
Proof
  rw [EX_data_rec_update_def]
QED

(** unchanged items by MEM_ctrl_update **)
Theorem MEM_ctrl_update_unchanged_IF:
  !fext s s'.
    ((MEM_ctrl_update fext s s').IF.IF_PC_input = s'.IF.IF_PC_input) /\
    ((MEM_ctrl_update fext s s').IF.IF_instr = s'.IF.IF_instr) /\
    ((MEM_ctrl_update fext s s').IF.IF_PC_write_enable = s'.IF.IF_PC_write_enable) /\
    ((MEM_ctrl_update fext s s').PC = s'.PC)
Proof
  rw [MEM_ctrl_update_def]
QED

Theorem MEM_ctrl_update_unchanged_ID_opc_func:
  !fext s s'.
    ((MEM_ctrl_update fext s s').ID.ID_opc = s'.ID.ID_opc) /\
    ((MEM_ctrl_update fext s s').ID.ID_func = s'.ID.ID_func)
Proof
  rw [MEM_ctrl_update_def]
QED

Theorem MEM_ctrl_update_unchanged_EX_ALU:
  !fext s s'.
    ((MEM_ctrl_update fext s s').EX.EX_ALU_res = s'.EX.EX_ALU_res) /\
    ((MEM_ctrl_update fext s s').EX.EX_carry_flag = s'.EX.EX_carry_flag) /\
    ((MEM_ctrl_update fext s s').EX.EX_overflow_flag = s'.EX.EX_overflow_flag)
Proof
  rw [MEM_ctrl_update_def]
QED

Theorem MEM_ctrl_update_unchanged_EX_pipeline_items:
  !fext s s'.
    ((MEM_ctrl_update fext s s').EX.EX_PC = s'.EX.EX_PC) /\
    ((MEM_ctrl_update fext s s').EX.EX_dataA = s'.EX.EX_dataA) /\
    ((MEM_ctrl_update fext s s').EX.EX_dataB = s'.EX.EX_dataB) /\
    ((MEM_ctrl_update fext s s').EX.EX_dataW = s'.EX.EX_dataW) /\
    ((MEM_ctrl_update fext s s').EX.EX_imm = s'.EX.EX_imm) /\
    ((MEM_ctrl_update fext s s').EX.EX_write_enable <=> s'.EX.EX_write_enable) /\
    ((MEM_ctrl_update fext s s').EX.EX_addrA_disable <=> s'.EX.EX_addrA_disable) /\
    ((MEM_ctrl_update fext s s').EX.EX_addrB_disable <=> s'.EX.EX_addrB_disable) /\
    ((MEM_ctrl_update fext s s').EX.EX_addrW_disable <=> s'.EX.EX_addrW_disable) /\
    ((MEM_ctrl_update fext s s').EX.EX_addrA = s'.EX.EX_addrA) /\
    ((MEM_ctrl_update fext s s').EX.EX_addrB = s'.EX.EX_addrB) /\
    ((MEM_ctrl_update fext s s').EX.EX_addrW = s'.EX.EX_addrW) /\
    ((MEM_ctrl_update fext s s').EX.EX_opc = s'.EX.EX_opc) /\
    ((MEM_ctrl_update fext s s').EX.EX_func = s'.EX.EX_func)
Proof
  rw [MEM_ctrl_update_def]
QED

Theorem MEM_ctrl_update_unchanged_state_items:
  !fext s s'.
    ((MEM_ctrl_update fext s s').command = s'.command) /\
    ((MEM_ctrl_update fext s s').state = s'.state)
Proof
  rw [MEM_ctrl_update_def]
QED

(** unchanged items by MEM_imm_update **)
Theorem MEM_imm_update_unchanged_IF:
  !fext s s'.
    ((MEM_imm_update fext s s').IF.IF_PC_input = s'.IF.IF_PC_input) /\
    ((MEM_imm_update fext s s').IF.IF_instr = s'.IF.IF_instr) /\
    ((MEM_imm_update fext s s').IF.IF_PC_write_enable = s'.IF.IF_PC_write_enable) /\
    ((MEM_imm_update fext s s').PC = s'.PC)                  
Proof
  rw [MEM_imm_update_def]
QED

Theorem MEM_imm_update_unchanged_ID_opc_func:
  !fext s s'.
    ((MEM_imm_update fext s s').ID.ID_opc = s'.ID.ID_opc) /\
    ((MEM_imm_update fext s s').ID.ID_func = s'.ID.ID_func)
Proof
  rw [MEM_imm_update_def]
QED

Theorem MEM_imm_update_unchanged_EX_ALU:
  !fext s s'.
    ((MEM_imm_update fext s s').EX.EX_ALU_res = s'.EX.EX_ALU_res) /\
    ((MEM_imm_update fext s s').EX.EX_carry_flag = s'.EX.EX_carry_flag) /\
    ((MEM_imm_update fext s s').EX.EX_overflow_flag = s'.EX.EX_overflow_flag)
Proof
  rw [MEM_imm_update_def]
QED

Theorem MEM_imm_update_unchanged_state_items:
  !fext s s'.
    ((MEM_imm_update fext s s').command = s'.command) /\
    ((MEM_imm_update fext s s').state = s'.state)
Proof
  rw [MEM_imm_update_def]
QED

(** unchanged items by WB_update **)
Theorem WB_update_unchanged_IF:
  !fext s s'.
    ((WB_update fext s s').IF.IF_PC_input = s'.IF.IF_PC_input) /\
    ((WB_update fext s s').IF.IF_instr = s'.IF.IF_instr) /\
    ((WB_update fext s s').IF.IF_PC_write_enable = s'.IF.IF_PC_write_enable) /\
    ((WB_update fext s s').PC = s'.PC)            
Proof
  rw [WB_update_def]
QED

Theorem WB_update_unchanged_ID_opc_func:
  !fext s s'.
    ((WB_update fext s s').ID.ID_opc = s'.ID.ID_opc) /\
    ((WB_update fext s s').ID.ID_func = s'.ID.ID_func)
Proof
  rw [WB_update_def]
QED

Theorem WB_update_unchanged_EX_ALU:
  !fext s s'.
    ((WB_update fext s s').EX.EX_ALU_res = s'.EX.EX_ALU_res) /\
    ((WB_update fext s s').EX.EX_carry_flag = s'.EX.EX_carry_flag) /\
    ((WB_update fext s s').EX.EX_overflow_flag = s'.EX.EX_overflow_flag)
Proof
  rw [WB_update_def]
QED

Theorem WB_update_unchanged_EX_pipeline_items:
  !fext s s'.
    ((WB_update fext s s').EX.EX_PC = s'.EX.EX_PC) /\
    ((WB_update fext s s').EX.EX_dataA = s'.EX.EX_dataA) /\
    ((WB_update fext s s').EX.EX_dataB = s'.EX.EX_dataB) /\
    ((WB_update fext s s').EX.EX_dataW = s'.EX.EX_dataW) /\
    ((WB_update fext s s').EX.EX_imm = s'.EX.EX_imm) /\
    ((WB_update fext s s').EX.EX_write_enable <=> s'.EX.EX_write_enable) /\
    ((WB_update fext s s').EX.EX_addrA_disable <=> s'.EX.EX_addrA_disable) /\
    ((WB_update fext s s').EX.EX_addrB_disable <=> s'.EX.EX_addrB_disable) /\
    ((WB_update fext s s').EX.EX_addrW_disable <=> s'.EX.EX_addrW_disable) /\
    ((WB_update fext s s').EX.EX_addrA = s'.EX.EX_addrA) /\
    ((WB_update fext s s').EX.EX_addrB = s'.EX.EX_addrB) /\
    ((WB_update fext s s').EX.EX_addrW = s'.EX.EX_addrW) /\
    ((WB_update fext s s').EX.EX_opc = s'.EX.EX_opc) /\
    ((WB_update fext s s').EX.EX_func = s'.EX.EX_func)
Proof
  rw [WB_update_def]
QED

Theorem WB_update_unchanged_state_items:
  !fext s s'.
    ((WB_update fext s s').command = s'.command) /\
    ((WB_update fext s s').state = s'.state)
Proof
  rw [WB_update_def]
QED

(** unchanged items by Hazard_ctrl **)
Theorem Hazard_ctrl_unchanged_IF:
  !fext s s'.
    ((Hazard_ctrl fext s s').IF.IF_PC_input = s'.IF.IF_PC_input) /\
    ((Hazard_ctrl fext s s').IF.IF_instr = s'.IF.IF_instr) /\
    ((Hazard_ctrl fext s s').PC = s'.PC)
Proof
  rw [Hazard_ctrl_def]
QED

Theorem Hazard_ctrl_unchanged_ID_opc_func:
  !fext s s'.
    ((Hazard_ctrl fext s s').ID.ID_opc = s'.ID.ID_opc) /\
    ((Hazard_ctrl fext s s').ID.ID_func = s'.ID.ID_func)
Proof
  rw [Hazard_ctrl_def]
QED

Theorem Hazard_ctrl_unchanged_EX_jump:
  !fext s s'.
    ((Hazard_ctrl fext s s').EX.EX_jump_sel <=> s'.EX.EX_jump_sel) /\
    ((Hazard_ctrl fext s s').EX.EX_jump_addr = s'.EX.EX_jump_addr)
Proof
  rw [Hazard_ctrl_def]
QED

Theorem Hazard_ctrl_unchanged_EX_pipeline_items:
  !fext s s'.
    ((Hazard_ctrl fext s s').EX.EX_PC = s'.EX.EX_PC) /\
    ((Hazard_ctrl fext s s').EX.EX_dataA = s'.EX.EX_dataA) /\
    ((Hazard_ctrl fext s s').EX.EX_dataB = s'.EX.EX_dataB) /\
    ((Hazard_ctrl fext s s').EX.EX_dataW = s'.EX.EX_dataW) /\
    ((Hazard_ctrl fext s s').EX.EX_imm = s'.EX.EX_imm) /\
    ((Hazard_ctrl fext s s').EX.EX_write_enable <=> s'.EX.EX_write_enable) /\
    ((Hazard_ctrl fext s s').EX.EX_addrA_disable <=> s'.EX.EX_addrA_disable) /\
    ((Hazard_ctrl fext s s').EX.EX_addrB_disable <=> s'.EX.EX_addrB_disable) /\
    ((Hazard_ctrl fext s s').EX.EX_addrW_disable <=> s'.EX.EX_addrW_disable) /\
    ((Hazard_ctrl fext s s').EX.EX_addrA = s'.EX.EX_addrA) /\
    ((Hazard_ctrl fext s s').EX.EX_addrB = s'.EX.EX_addrB) /\
    ((Hazard_ctrl fext s s').EX.EX_addrW = s'.EX.EX_addrW) /\
    ((Hazard_ctrl fext s s').EX.EX_opc = s'.EX.EX_opc) /\
    ((Hazard_ctrl fext s s').EX.EX_func = s'.EX.EX_func)
Proof
  rw [Hazard_ctrl_def]
QED

Theorem Hazard_ctrl_unchanged_EX_ALU:
  !fext s s'.
    ((Hazard_ctrl fext s s').EX.EX_ALU_res = s'.EX.EX_ALU_res) /\
    ((Hazard_ctrl fext s s').EX.EX_carry_flag = s'.EX.EX_carry_flag) /\
    ((Hazard_ctrl fext s s').EX.EX_overflow_flag = s'.EX.EX_overflow_flag)
Proof
  rw [Hazard_ctrl_def]
QED

Theorem Hazard_ctrl_unchanged_state_items:
  !fext s s'.
    ((Hazard_ctrl fext s s').command = s'.command) /\
    ((Hazard_ctrl fext s s').state = s'.state)
Proof
  rw [Hazard_ctrl_def]
QED

(** unchanged items by Acc_compute **)
Theorem Acc_compute_unchanged_IF:
  !fext s s'.
    (Acc_compute fext s s').PC = s'.PC
Proof
  rw [Acc_compute_def]
QED

Theorem Acc_compute_unchanged_EX_jump:
  !fext s s'.
    ((Acc_compute fext s s').EX.EX_jump_sel <=> s'.EX.EX_jump_sel) /\
    ((Acc_compute fext s s').EX.EX_jump_addr = s'.EX.EX_jump_addr)
Proof
  rw [Acc_compute_def]
QED

Theorem Acc_compute_unchanged_EX_pipeline_items:
  !fext s s'.
    ((Acc_compute fext s s').EX.EX_PC = s'.EX.EX_PC) /\
    ((Acc_compute fext s s').EX.EX_dataA = s'.EX.EX_dataA) /\
    ((Acc_compute fext s s').EX.EX_dataB = s'.EX.EX_dataB) /\
    ((Acc_compute fext s s').EX.EX_dataW = s'.EX.EX_dataW) /\
    ((Acc_compute fext s s').EX.EX_imm = s'.EX.EX_imm) /\
    ((Acc_compute fext s s').EX.EX_write_enable <=> s'.EX.EX_write_enable) /\
    ((Acc_compute fext s s').EX.EX_addrA_disable <=> s'.EX.EX_addrA_disable) /\
    ((Acc_compute fext s s').EX.EX_addrB_disable <=> s'.EX.EX_addrB_disable) /\
    ((Acc_compute fext s s').EX.EX_addrW_disable <=> s'.EX.EX_addrW_disable) /\
    ((Acc_compute fext s s').EX.EX_addrA = s'.EX.EX_addrA) /\
    ((Acc_compute fext s s').EX.EX_addrB = s'.EX.EX_addrB) /\
    ((Acc_compute fext s s').EX.EX_addrW = s'.EX.EX_addrW) /\
    ((Acc_compute fext s s').EX.EX_opc = s'.EX.EX_opc) /\
    ((Acc_compute fext s s').EX.EX_func = s'.EX.EX_func)
Proof
  rw [Acc_compute_def]
QED

Theorem Acc_compute_unchanged_EX_ALU:
  !fext s s'.
    ((Acc_compute fext s s').EX.EX_ALU_res = s'.EX.EX_ALU_res) /\
    ((Acc_compute fext s s').EX.EX_carry_flag = s'.EX.EX_carry_flag) /\
    ((Acc_compute fext s s').EX.EX_overflow_flag = s'.EX.EX_overflow_flag)
Proof
  rw [Acc_compute_def]
QED

Theorem Acc_compute_unchanged_state_items:
  !fext s s'.
    ((Acc_compute fext s s').command = s'.command) /\
    ((Acc_compute fext s s').state = s'.state)
Proof
  rw [Acc_compute_def]
QED

(** unchanged items by IF_PC_update **)
Theorem IF_PC_update_unchanged_EX_jump:
  !fext s s'.
    ((IF_PC_update fext s s').EX.EX_jump_sel <=> s'.EX.EX_jump_sel) /\
    ((IF_PC_update fext s s').EX.EX_jump_addr = s'.EX.EX_jump_addr)
Proof
  rw [IF_PC_update_def]
QED

Theorem IF_PC_update_unchanged_EX_pipeline_items:
  !fext s s'.
    ((IF_PC_update fext s s').EX.EX_PC = s'.EX.EX_PC) /\
    ((IF_PC_update fext s s').EX.EX_dataA = s'.EX.EX_dataA) /\
    ((IF_PC_update fext s s').EX.EX_dataB = s'.EX.EX_dataB) /\
    ((IF_PC_update fext s s').EX.EX_dataW = s'.EX.EX_dataW) /\
    ((IF_PC_update fext s s').EX.EX_imm = s'.EX.EX_imm) /\
    ((IF_PC_update fext s s').EX.EX_write_enable <=> s'.EX.EX_write_enable) /\
    ((IF_PC_update fext s s').EX.EX_addrA_disable <=> s'.EX.EX_addrA_disable) /\
    ((IF_PC_update fext s s').EX.EX_addrB_disable <=> s'.EX.EX_addrB_disable) /\
    ((IF_PC_update fext s s').EX.EX_addrW_disable <=> s'.EX.EX_addrW_disable) /\
    ((IF_PC_update fext s s').EX.EX_addrA = s'.EX.EX_addrA) /\
    ((IF_PC_update fext s s').EX.EX_addrB = s'.EX.EX_addrB) /\
    ((IF_PC_update fext s s').EX.EX_addrW = s'.EX.EX_addrW) /\
    ((IF_PC_update fext s s').EX.EX_opc = s'.EX.EX_opc) /\
    ((IF_PC_update fext s s').EX.EX_func = s'.EX.EX_func)
Proof
  rw [IF_PC_update_def]
QED

Theorem IF_PC_update_unchanged_EX_ALU:
  !fext s s'.
    ((IF_PC_update fext s s').EX.EX_ALU_res = s'.EX.EX_ALU_res) /\
    ((IF_PC_update fext s s').EX.EX_carry_flag = s'.EX.EX_carry_flag) /\
    ((IF_PC_update fext s s').EX.EX_overflow_flag = s'.EX.EX_overflow_flag)
Proof
  rw [IF_PC_update_def]
QED

Theorem IF_PC_update_unchanged_state_items:
  !fext s s'.
    ((IF_PC_update fext s s').command = s'.command) /\
    ((IF_PC_update fext s s').state = s'.state)
Proof
  rw [IF_PC_update_def]
QED

(** unchanged items by ID_pipeline **)
Theorem ID_pipeline_unchanged_IF_items:
  !fext s s'.
    ((ID_pipeline fext s s').IF.IF_PC_write_enable <=> s'.IF.IF_PC_write_enable) /\
    ((ID_pipeline fext s s').IF.IF_PC_input = s'.IF.IF_PC_input)
Proof
  rw [ID_pipeline_def]
QED

Theorem ID_pipeline_unchanged_EX_jump:
  !fext s s'.
    ((ID_pipeline fext s s').EX.EX_jump_sel <=> s'.EX.EX_jump_sel) /\
    ((ID_pipeline fext s s').EX.EX_jump_addr = s'.EX.EX_jump_addr)
Proof
  rw [ID_pipeline_def]
QED

Theorem ID_pipeline_unchanged_EX_pipeline_items:
  !fext s s'.
    ((ID_pipeline fext s s').EX.EX_PC = s'.EX.EX_PC) /\
    ((ID_pipeline fext s s').EX.EX_dataA = s'.EX.EX_dataA) /\
    ((ID_pipeline fext s s').EX.EX_dataB = s'.EX.EX_dataB) /\
    ((ID_pipeline fext s s').EX.EX_dataW = s'.EX.EX_dataW) /\
    ((ID_pipeline fext s s').EX.EX_imm = s'.EX.EX_imm) /\
    ((ID_pipeline fext s s').EX.EX_write_enable <=> s'.EX.EX_write_enable) /\
    ((ID_pipeline fext s s').EX.EX_addrA_disable <=> s'.EX.EX_addrA_disable) /\
    ((ID_pipeline fext s s').EX.EX_addrB_disable <=> s'.EX.EX_addrB_disable) /\
    ((ID_pipeline fext s s').EX.EX_addrW_disable <=> s'.EX.EX_addrW_disable) /\
    ((ID_pipeline fext s s').EX.EX_addrA = s'.EX.EX_addrA) /\
    ((ID_pipeline fext s s').EX.EX_addrB = s'.EX.EX_addrB) /\
    ((ID_pipeline fext s s').EX.EX_addrW = s'.EX.EX_addrW) /\
    ((ID_pipeline fext s s').EX.EX_opc = s'.EX.EX_opc) /\
    ((ID_pipeline fext s s').EX.EX_func = s'.EX.EX_func)
Proof
  rw [ID_pipeline_def]
QED

Theorem ID_pipeline_unchanged_EX_ALU:
  !fext s s'.
    ((ID_pipeline fext s s').EX.EX_ALU_res = s'.EX.EX_ALU_res) /\
    ((ID_pipeline fext s s').EX.EX_carry_flag = s'.EX.EX_carry_flag) /\
    ((ID_pipeline fext s s').EX.EX_overflow_flag = s'.EX.EX_overflow_flag)
Proof
  rw [ID_pipeline_def]
QED

Theorem ID_pipeline_unchanged_state_items:
  !fext s s'.
    ((ID_pipeline fext s s').command = s'.command) /\
    ((ID_pipeline fext s s').state = s'.state)
Proof
  rw [ID_pipeline_def]
QED

(** unchanged items by REG_write **)
Theorem REG_write_unchanged_IF_items:
  !fext s s'.
    ((REG_write fext s s').IF.IF_PC_write_enable <=> s'.IF.IF_PC_write_enable) /\
    ((REG_write fext s s').IF.IF_PC_input = s'.IF.IF_PC_input)
Proof
  rw [REG_write_def]
QED

Theorem REG_write_unchanged_EX_jump:
  !fext s s'.
    ((REG_write fext s s').EX.EX_jump_sel <=> s'.EX.EX_jump_sel) /\
    ((REG_write fext s s').EX.EX_jump_addr = s'.EX.EX_jump_addr)
Proof
  rw [REG_write_def]
QED

Theorem REG_write_unchanged_EX_pipeline_items:
  !fext s s'.
    ((REG_write fext s s').EX.EX_PC = s'.EX.EX_PC) /\
    ((REG_write fext s s').EX.EX_dataA = s'.EX.EX_dataA) /\
    ((REG_write fext s s').EX.EX_dataB = s'.EX.EX_dataB) /\
    ((REG_write fext s s').EX.EX_dataW = s'.EX.EX_dataW) /\
    ((REG_write fext s s').EX.EX_imm = s'.EX.EX_imm) /\
    ((REG_write fext s s').EX.EX_write_enable <=> s'.EX.EX_write_enable) /\
    ((REG_write fext s s').EX.EX_addrA_disable <=> s'.EX.EX_addrA_disable) /\
    ((REG_write fext s s').EX.EX_addrB_disable <=> s'.EX.EX_addrB_disable) /\
    ((REG_write fext s s').EX.EX_addrW_disable <=> s'.EX.EX_addrW_disable) /\
    ((REG_write fext s s').EX.EX_addrA = s'.EX.EX_addrA) /\
    ((REG_write fext s s').EX.EX_addrB = s'.EX.EX_addrB) /\
    ((REG_write fext s s').EX.EX_addrW = s'.EX.EX_addrW) /\
    ((REG_write fext s s').EX.EX_opc = s'.EX.EX_opc) /\
    ((REG_write fext s s').EX.EX_func = s'.EX.EX_func)
Proof
  rw [REG_write_def]
QED

Theorem REG_write_unchanged_EX_ALU:
  !fext s s'.
    ((REG_write fext s s').EX.EX_ALU_res = s'.EX.EX_ALU_res) /\
    ((REG_write fext s s').EX.EX_carry_flag = s'.EX.EX_carry_flag) /\
    ((REG_write fext s s').EX.EX_overflow_flag = s'.EX.EX_overflow_flag)
Proof
  rw [REG_write_def]
QED

Theorem REG_write_unchanged_state_items:
  !fext s s'.
    ((REG_write fext s s').command = s'.command) /\
    ((REG_write fext s s').state = s'.state)
Proof
  rw [REG_write_def]
QED

(** unchanged items by EX_pipeline **)
Theorem EX_pipeline_unchanged_IF_items:
  !fext s s'.
    ((EX_pipeline fext s s').IF.IF_PC_write_enable <=> s'.IF.IF_PC_write_enable) /\
    ((EX_pipeline fext s s').IF.IF_PC_input = s'.IF.IF_PC_input)
Proof
  rw [EX_pipeline_def]
QED

Theorem EX_pipeline_unchanged_EX_jump:
  !fext s s'.
    ((EX_pipeline fext s s').EX.EX_jump_sel <=> s'.EX.EX_jump_sel) /\
    ((EX_pipeline fext s s').EX.EX_jump_addr = s'.EX.EX_jump_addr)
Proof
  rw [EX_pipeline_def]
QED

Theorem EX_pipeline_unchanged_EX_ALU:
  !fext s s'.
    ((EX_pipeline fext s s').EX.EX_ALU_res = s'.EX.EX_ALU_res) /\
    ((EX_pipeline fext s s').EX.EX_carry_flag = s'.EX.EX_carry_flag) /\
    ((EX_pipeline fext s s').EX.EX_overflow_flag = s'.EX.EX_overflow_flag)
Proof
  rw [EX_pipeline_def]
QED

Theorem EX_pipeline_unchanged_state_items:
  !fext s s'.
    ((EX_pipeline fext s s').command = s'.command) /\
    ((EX_pipeline fext s s').state = s'.state)
Proof
  rw [EX_pipeline_def]
QED

(** unchanged items by MEM_pipeline **)
Theorem MEM_pipeline_unchanged_enable_flags:
  !fext s s'.
    ((MEM_pipeline fext s s').ID.ID_EX_write_enable <=> s'.ID.ID_EX_write_enable) /\
    ((MEM_pipeline fext s s').EX.EX_NOP_flag <=> s'.EX.EX_NOP_flag) /\
    ((MEM_pipeline fext s s').MEM.MEM_state_flag <=> s'.MEM.MEM_state_flag)
Proof
  rw [MEM_pipeline_def]
QED

Theorem MEM_pipeline_unchanged_IF_items:
  !fext s s'.
    ((MEM_pipeline fext s s').IF.IF_PC_write_enable <=> s'.IF.IF_PC_write_enable) /\
    ((MEM_pipeline fext s s').IF.IF_PC_input = s'.IF.IF_PC_input)
Proof
  rw [MEM_pipeline_def]
QED

Theorem MEM_pipeline_unchanged_ID_opc_func:
  !fext s s'.
    ((MEM_pipeline fext s s').ID.ID_opc = s'.ID.ID_opc) /\
    ((MEM_pipeline fext s s').ID.ID_func = s'.ID.ID_func)
Proof
  rw [MEM_pipeline_def]
QED

Theorem MEM_pipeline_unchanged_EX_jump:
  !fext s s'.
    ((MEM_pipeline fext s s').EX.EX_jump_sel <=> s'.EX.EX_jump_sel) /\
    ((MEM_pipeline fext s s').EX.EX_jump_addr = s'.EX.EX_jump_addr)
Proof
  rw [MEM_pipeline_def]
QED

Theorem MEM_pipeline_unchanged_EX_ALU:
  !fext s s'.
    ((MEM_pipeline fext s s').EX.EX_ALU_res = s'.EX.EX_ALU_res) /\
    ((MEM_pipeline fext s s').EX.EX_carry_flag = s'.EX.EX_carry_flag) /\
    ((MEM_pipeline fext s s').EX.EX_overflow_flag = s'.EX.EX_overflow_flag)
Proof
  rw [MEM_pipeline_def]
QED

Theorem MEM_pipeline_unchanged_state_items:
  !fext s s'.
    ((MEM_pipeline fext s s').command = s'.command) /\
    ((MEM_pipeline fext s s').state = s'.state)
Proof
  rw [MEM_pipeline_def]
QED

(** unchanged items by WB_pipeline **)
Theorem WB_pipeline_unchanged_enable_flags:
  !fext s s'.
    ((WB_pipeline fext s s').ID.ID_EX_write_enable <=> s'.ID.ID_EX_write_enable) /\
    ((WB_pipeline fext s s').EX.EX_NOP_flag <=> s'.EX.EX_NOP_flag) /\
    ((WB_pipeline fext s s').MEM.MEM_state_flag <=> s'.MEM.MEM_state_flag)
Proof
  rw [WB_pipeline_def]
QED

Theorem WB_pipeline_unchanged_IF_items:
  !fext s s'.
    ((WB_pipeline fext s s').IF.IF_PC_write_enable <=> s'.IF.IF_PC_write_enable) /\
    ((WB_pipeline fext s s').IF.IF_PC_input = s'.IF.IF_PC_input)
Proof
  rw [WB_pipeline_def]
QED

Theorem WB_pipeline_unchanged_ID_opc_func:
  !fext s s'.
    ((WB_pipeline fext s s').ID.ID_opc = s'.ID.ID_opc) /\
    ((WB_pipeline fext s s').ID.ID_func = s'.ID.ID_func)
Proof
  rw [WB_pipeline_def]
QED

Theorem WB_pipeline_unchanged_EX_jump:
  !fext s s'.
    ((WB_pipeline fext s s').EX.EX_jump_sel <=> s'.EX.EX_jump_sel) /\
    ((WB_pipeline fext s s').EX.EX_jump_addr = s'.EX.EX_jump_addr)
Proof
  rw [WB_pipeline_def]
QED

Theorem WB_pipeline_unchanged_EX_ALU:
  !fext s s'.
    ((WB_pipeline fext s s').EX.EX_ALU_res = s'.EX.EX_ALU_res) /\
    ((WB_pipeline fext s s').EX.EX_carry_flag = s'.EX.EX_carry_flag) /\
    ((WB_pipeline fext s s').EX.EX_overflow_flag = s'.EX.EX_overflow_flag)
Proof
  rw [WB_pipeline_def]
QED

Theorem WB_pipeline_unchanged_state_items:
  !fext s s'.
    ((WB_pipeline fext s s').command = s'.command) /\
    ((WB_pipeline fext s s').state = s'.state)
Proof
  rw [WB_pipeline_def]
QED

(** unchanged items by agp32_next_state **)
Theorem agp32_next_state_unchanged_enable_flags:
  !fext s s'.
    ((agp32_next_state fext s s').ID.ID_EX_write_enable <=> s'.ID.ID_EX_write_enable) /\
    ((agp32_next_state fext s s').EX.EX_NOP_flag <=> s'.EX.EX_NOP_flag) /\
    ((agp32_next_state fext s s').MEM.MEM_state_flag <=> s'.MEM.MEM_state_flag)
Proof
  rw [agp32_next_state_def] >>
  Cases_on_word_value `(1 >< 0) s.MEM.MEM_dataB` >> fs []
QED

Theorem agp32_next_state_unchanged_IF_items:
  !fext s s'.
    ((agp32_next_state fext s s').IF.IF_PC_write_enable <=> s'.IF.IF_PC_write_enable) /\
    ((agp32_next_state fext s s').IF.IF_PC_input = s'.IF.IF_PC_input)
Proof
  rw [agp32_next_state_def] >>
  Cases_on_word_value `(1 >< 0) s.MEM.MEM_dataB` >> fs []
QED

Theorem agp32_next_state_unchanged_ID_opc_func:
  !fext s s'.
    ((agp32_next_state fext s s').ID.ID_opc = s'.ID.ID_opc) /\
    ((agp32_next_state fext s s').ID.ID_func = s'.ID.ID_func)
Proof
  rw [agp32_next_state_def] >>
  Cases_on_word_value `(1 >< 0) s.MEM.MEM_dataB` >> fs []
QED

Theorem agp32_next_state_unchanged_EX_jump:
  !fext s s'.
    ((agp32_next_state fext s s').EX.EX_jump_sel <=> s'.EX.EX_jump_sel) /\
    ((agp32_next_state fext s s').EX.EX_jump_addr = s'.EX.EX_jump_addr)
Proof
  rw [agp32_next_state_def] >>
  Cases_on_word_value `(1 >< 0) s.MEM.MEM_dataB` >> fs []
QED
   
Theorem agp32_next_state_unchanged_EX_ALU:
  !fext s s'.
    ((agp32_next_state fext s s').EX.EX_ALU_res = s'.EX.EX_ALU_res) /\
    ((agp32_next_state fext s s').EX.EX_carry_flag = s'.EX.EX_carry_flag) /\
    ((agp32_next_state fext s s').EX.EX_overflow_flag = s'.EX.EX_overflow_flag)
Proof
  rw [agp32_next_state_def] >>
  Cases_on_word_value `(1 >< 0) s.MEM.MEM_dataB` >> fs []
QED


(** lemmas **)
Theorem slist_unchanged_EX_jump:
  !fext s s'.
    ((procs [agp32_next_state;WB_pipeline;MEM_pipeline;EX_pipeline;
             REG_write;ID_pipeline;IF_PC_update;Acc_compute]
      fext s s').EX.EX_jump_sel <=> s'.EX.EX_jump_sel) /\
    ((procs [agp32_next_state;WB_pipeline;MEM_pipeline;EX_pipeline;
             REG_write;ID_pipeline;IF_PC_update;Acc_compute]
      fext s s').EX.EX_jump_addr = s'.EX.EX_jump_addr)
Proof
  rw [] >> 
  slist_update_state_tac >>
  fs [Abbr `ss8`,Acc_compute_unchanged_EX_jump,
      Abbr `ss7`,IF_PC_update_unchanged_EX_jump,
      Abbr `ss6`,ID_pipeline_unchanged_EX_jump,
      Abbr `ss5`,REG_write_unchanged_EX_jump,
      Abbr `ss4`,EX_pipeline_unchanged_EX_jump,
      Abbr `ss3`,MEM_pipeline_unchanged_EX_jump,
      Abbr `ss2`,WB_pipeline_unchanged_EX_jump,
      Abbr `ss1`,agp32_next_state_unchanged_EX_jump]
QED


(* circuit variables are only changed by the certain function *)
(** PC is only changed by the IF_PC_update function **)
Theorem agp32_PC_updated_by_IF_PC_update:
  !fext fbits t s s' s''.
    s = agp32 fext fbits t ==>
    s' = procs [agp32_next_state; WB_pipeline; MEM_pipeline; EX_pipeline;
                REG_write; ID_pipeline]
               (fext t) s s ==>
    (agp32 fext fbits (SUC t)).PC =
    (IF_PC_update (fext (SUC t)) s'' s').PC
Proof
  rw [agp32_def,mk_module_def,mk_circuit_def] >>
  qpat_abbrev_tac `s = mk_circuit (procs _) (procs _) (agp32_init fbits) fext t` >>
  qpat_abbrev_tac `s0 = procs _ (fext t) s s` >>
  qpat_abbrev_tac `s' = procs _ (fext t) s s` >>
  clist_update_state_tac >>
  fs [Abbr `s20`,Abbr `s19`,Abbr `s18`,Abbr `s17`,Abbr `s16`,Abbr `s15`,Abbr `s14`,
      Abbr `s13`,Abbr `s12`,Abbr `s11`,Abbr `s10`,Abbr `s9`,Abbr `s8`,Abbr `s7`,
      Abbr `s6`,Abbr `s5`,Abbr `s4`,Abbr `s3`,Abbr `s2`,Abbr `s1`,Abbr `s0`,Abbr `s'`,
      Hazard_ctrl_unchanged_IF,WB_update_unchanged_IF,MEM_imm_update_unchanged_IF,
      MEM_ctrl_update_unchanged_IF,EX_data_rec_update_unchanged_IF,
      EX_jump_sel_addr_update_unchanged_IF,EX_SHIFT_update_unchanged_IF,
      EX_ALU_update_unchanged_IF,EX_compute_enable_update_unchanged_IF,
      EX_ALU_input_update_unchanged_IF,EX_forward_data_unchanged_IF,
      EX_ctrl_update_unchanged_IF,ID_data_update_unchanged_IF,
      ID_imm_update_unchanged_IF,ID_opc_func_update_unchanged_IF,
      IF_PC_input_update_def,IF_instr_update_def,
      ForwardW_def,ForwardB_def,ForwardA_def] >>
  slist_update_state_tac >>
  fs [Abbr `ss8`,Acc_compute_unchanged_IF,Abbr `ss7`,IF_PC_update_def]
QED

(** IF_PC_input is only changed by the IF_PC_input_update function **)    
Theorem agp32_IF_PC_input_updated_by_IF_PC_input_update:
  !fext fbits t s s' s''.
    s = agp32 fext fbits t ==>
    s' = procs [agp32_next_state; WB_pipeline; MEM_pipeline; EX_pipeline;
                REG_write; ID_pipeline; IF_PC_update; Acc_compute]
               (fext t) s s ==>
    s'' = procs [ForwardA; ForwardB; ForwardW; IF_instr_update; ID_opc_func_update;
                 ID_imm_update; ID_data_update; EX_ctrl_update; EX_forward_data;
                 EX_ALU_input_update; EX_compute_enable_update; EX_ALU_update;
                 EX_SHIFT_update; EX_jump_sel_addr_update; EX_data_rec_update]
                (fext (SUC t)) s' s' ==>
    (agp32 fext fbits (SUC t)).IF.IF_PC_input =
    (IF_PC_input_update (fext (SUC t)) s' s'').IF.IF_PC_input
Proof
  rw [agp32_def,mk_module_def,mk_circuit_def] >>
  qpat_abbrev_tac `s = mk_circuit (procs _) (procs _) (agp32_init fbits) fext t` >>
  qpat_abbrev_tac `s0 = procs _ (fext t) s s` >>
  clist_update_state_tac >>
  fs [Abbr `s20`,Abbr `s19`,Abbr `s18`,Abbr `s17`,
      Hazard_ctrl_unchanged_IF,WB_update_unchanged_IF,
      MEM_imm_update_unchanged_IF,MEM_ctrl_update_unchanged_IF]
QED

(** IF_instr is only changed by the IF_instr_update function **)
Theorem agp32_IF_instr_updated_by_IF_instr_update:
  !fext fbits t s s'.
    (agp32 fext fbits (SUC t)).IF.IF_instr =
    (IF_instr_update (fext (SUC t)) s s').IF.IF_instr
Proof
  rw [agp32_def,IF_instr_update_def,mk_module_def,mk_circuit_def] >>
  qpat_abbrev_tac `s = mk_circuit (procs _) (procs _) (agp32_init fbits) fext t` >>
  qpat_abbrev_tac `s' = procs _ (fext t) s s` >>
  clist_update_state_tac >>
  fs [Abbr `s20`,Abbr `s19`,Abbr `s18`,Abbr `s17`,Abbr `s16`,Abbr `s15`,Abbr `s14`,
      Abbr `s13`,Abbr `s12`,Abbr `s11`,Abbr `s10`,Abbr `s9`,Abbr `s8`,Abbr `s7`,
      Abbr `s6`,Abbr `s5`,Abbr `s4`,
      Hazard_ctrl_unchanged_IF,WB_update_unchanged_IF,MEM_imm_update_unchanged_IF,
      MEM_ctrl_update_unchanged_IF,EX_data_rec_update_unchanged_IF,
      EX_jump_sel_addr_update_unchanged_IF,EX_SHIFT_update_unchanged_IF,
      EX_ALU_update_unchanged_IF,EX_compute_enable_update_unchanged_IF,
      EX_ALU_input_update_unchanged_IF,EX_forward_data_unchanged_IF,
      EX_ctrl_update_unchanged_IF,ID_data_update_unchanged_IF,
      ID_imm_update_unchanged_IF,ID_opc_func_update_unchanged_IF,
      IF_PC_input_update_def,IF_instr_update_def]
QED

(** ID_opc is only chenged by the ID_opc_func_update function **)
Theorem agp32_ID_func_updated_by_ID_opc_func_update:
  !fext fbits t s s' s'' s0.
    s = agp32 fext fbits t ==>
    s' = procs [agp32_next_state; WB_pipeline; MEM_pipeline; EX_pipeline;
                REG_write; ID_pipeline; IF_PC_update; Acc_compute]
               (fext t) s s ==>
    s'' = procs [ForwardA; ForwardB; ForwardW; IF_instr_update]
                (fext (SUC t)) s' s' ==>
    (agp32 fext fbits (SUC t)).ID.ID_func =
    (ID_opc_func_update (fext (SUC t)) s0 s'').ID.ID_func
Proof
  rw [agp32_def,mk_module_def,mk_circuit_def] >>
  qpat_abbrev_tac `s'' = mk_circuit (procs _) (procs _) (agp32_init fbits) fext t` >>
  qpat_abbrev_tac `s''' = procs _ (fext t) s'' s''` >>
  clist_update_state_tac >>
  fs [Abbr `s20`,Abbr `s19`,Abbr `s18`,Abbr `s17`,Abbr `s16`,Abbr `s15`,
      Abbr `s14`,Abbr `s13`,Abbr `s12`,Abbr `s11`,Abbr `s10`,Abbr `s9`,Abbr `s8`,
      Hazard_ctrl_unchanged_ID_opc_func,WB_update_unchanged_ID_opc_func,
      MEM_imm_update_unchanged_ID_opc_func,MEM_ctrl_update_unchanged_ID_opc_func,
      IF_PC_input_update_def,EX_data_rec_update_unchanged_ID_opc_func,
      EX_jump_sel_addr_update_unchanged_ID_opc_func,EX_SHIFT_update_unchanged_ID_opc_func,
      EX_ALU_update_unchanged_ID_opc_func,EX_compute_enable_update_def,
      EX_ALU_input_update_def,EX_forward_data_def,
      EX_ctrl_update_unchanged_ID_opc_func] >>
  fs [Abbr `s7`,Abbr `s6`,Abbr `s5`,
      ID_data_update_def,ID_imm_update_unchanged_ID_opc_func] >>
  rw [ID_opc_func_update_def]
QED

(** EX_carry_flag, EX_ALU_res are only changed by the EX_ALU_update function **)
Theorem agp32_EX_ALU_items_updated_by_EX_ALU_update:
  !fext fbits t s s' s''.
    s = agp32 fext fbits t ==>
    s' = procs [agp32_next_state; WB_pipeline; MEM_pipeline; EX_pipeline;
                REG_write; ID_pipeline; IF_PC_update; Acc_compute]
               (fext t) s s ==>
    s'' = procs [ForwardA; ForwardB; ForwardW;
                 IF_instr_update;ID_opc_func_update; ID_imm_update;
                 ID_data_update; EX_ctrl_update; EX_forward_data;
                 EX_ALU_input_update; EX_compute_enable_update]
                (fext (SUC t)) s' s' ==>
    (agp32 fext fbits (SUC t)).EX.EX_carry_flag =
    (EX_ALU_update (fext (SUC t)) s' s'').EX.EX_carry_flag
Proof
  rw [agp32_def,mk_module_def,mk_circuit_def] >>
  qpat_abbrev_tac `s''' = mk_circuit (procs _) (procs _) (agp32_init fbits) fext t` >>
  qpat_abbrev_tac `s'''' = procs _ (fext t) s''' s'''` >>
  clist_update_state_tac >>
  fs [Abbr `s20`,Abbr `s19`,Abbr `s18`,Abbr `s17`,
      Abbr `s16`,Abbr `s15`,Abbr `s14`,Abbr `s13`,
      Hazard_ctrl_unchanged_EX_ALU,WB_update_unchanged_EX_ALU,
      MEM_imm_update_unchanged_EX_ALU,MEM_ctrl_update_unchanged_EX_ALU,
      IF_PC_input_update_def,EX_data_rec_update_unchanged_EX_ALU,
      EX_jump_sel_addr_update_unchanged_EX_ALU,
      EX_SHIFT_update_unchanged_EX_ALU]
QED

(** EX_opc and func are updated by the EX_pipeline function **)
Theorem agp32_EX_opc_func_updated_by_EX_pipeline:
  !fext fbits t s s' s''.
    s' = agp32 fext fbits t ==>
    s'' = procs [agp32_next_state;WB_pipeline;MEM_pipeline] (fext t) s' s' ==>
    ((agp32 fext fbits (SUC t)).EX.EX_opc = (EX_pipeline (fext (SUC t)) s s'').EX.EX_opc) /\
    ((agp32 fext fbits (SUC t)).EX.EX_func = (EX_pipeline (fext (SUC t)) s s'').EX.EX_func)
Proof
  rw [agp32_def,mk_module_def,mk_circuit_def] >>
  qpat_abbrev_tac `s'' = mk_circuit (procs _) (procs _) (agp32_init fbits) fext t` >>
  qpat_abbrev_tac `s''' = procs _ (fext t) s'' s''` >>
  clist_update_state_tac >>
  fs [Abbr `s20`,Abbr `s19`,Abbr `s18`,Abbr `s17`,
      Hazard_ctrl_unchanged_EX_pipeline_items,WB_update_unchanged_EX_pipeline_items,
      MEM_imm_update_def,MEM_ctrl_update_unchanged_EX_pipeline_items] >>
  fs [Abbr `s16`,Abbr `s15`,Abbr `s14`,Abbr `s13`,Abbr `s12`,Abbr `s11`,Abbr `s10`,
      Abbr `s9`,Abbr `s8`,Abbr `s7`,Abbr `s6`,Abbr `s5`,
      IF_PC_input_update_def,EX_data_rec_update_unchanged_EX_pipeline_items,
      EX_jump_sel_addr_update_unchanged_EX_pipeline_items,
      EX_SHIFT_update_unchanged_EX_pipeline_items,EX_ALU_update_unchanged_EX_pipeline_items,
      EX_compute_enable_update_def,EX_ALU_input_update_def,EX_forward_data_def,
      EX_ctrl_update_unchanged_EX_pipeline_items,ID_data_update_unchanged_EX_pipeline_items,
      ID_imm_update_unchanged_EX_pipeline_items,ID_opc_func_update_unchanged_EX_pipeline_items] >>
  fs [Abbr `s4`,Abbr `s3`,Abbr `s2`,Abbr `s1`,Abbr `s'''`,
      IF_PC_input_update_def,IF_instr_update_def,
      ForwardW_def,ForwardB_def,ForwardA_def] >>
  slist_update_state_tac >>
  fs [Abbr `ss8`,Acc_compute_unchanged_EX_pipeline_items,
      Abbr `ss7`,IF_PC_update_unchanged_EX_pipeline_items,
      Abbr `ss6`,ID_pipeline_unchanged_EX_pipeline_items,
      Abbr `ss5`,REG_write_unchanged_EX_pipeline_items,Abbr `ss4`] >>
  rw [EX_pipeline_def]
QED

(** command is updated by the agp32_next_state function **)
Theorem agp32_command_updated_by_agp32_next_state:
  !fext fbits t s.
    s = agp32 fext fbits t ==>
    (agp32 fext fbits (SUC t)).command = (agp32_next_state (fext t) s s).command
Proof
  rw [agp32_def,mk_module_def,mk_circuit_def] >>
  qpat_abbrev_tac `s' = mk_circuit (procs _) (procs _) (agp32_init fbits) fext t` >>
  qpat_abbrev_tac `s'' = procs _ (fext t) s' s'` >>
  clist_update_state_tac >>
  fs [Abbr `s20`,Abbr `s19`,Abbr `s18`,Abbr `s17`,Abbr `s16`,Abbr `s15`,Abbr `s14`,
      Abbr `s13`,Abbr `s12`,Abbr `s11`,Abbr `s10`,Abbr `s9`,Abbr `s8`,Abbr `s7`,
      Abbr `s6`,Abbr `s5`,Abbr `s4`,Abbr `s3`,Abbr `s2`,Abbr `s1`,Abbr `s''`,
      Hazard_ctrl_unchanged_state_items,WB_update_unchanged_state_items,
      MEM_imm_update_unchanged_state_items,MEM_ctrl_update_unchanged_state_items,
      EX_data_rec_update_unchanged_state_items,EX_jump_sel_addr_update_unchanged_state_items,
      EX_SHIFT_update_unchanged_state_items,EX_ALU_update_unchanged_state_items,
      EX_compute_enable_update_unchanged_state_items,EX_ALU_input_update_unchanged_state_items,
      EX_forward_data_unchanged_state_items,EX_ctrl_update_unchanged_state_items,
      ID_data_update_unchanged_state_items,ID_imm_update_unchanged_state_items,
      ID_opc_func_update_unchanged_state_items,IF_PC_input_update_def,IF_instr_update_def,
      ForwardW_def,ForwardB_def,ForwardA_def] >>
  slist_update_state_tac >>
  fs [Abbr `ss8`,Abbr `ss7`,Abbr `ss6`,Abbr `ss5`,
      Abbr `ss4`,Abbr `ss3`,Abbr `ss2`,
      Acc_compute_unchanged_state_items,IF_PC_update_unchanged_state_items,
      ID_pipeline_unchanged_state_items,REG_write_unchanged_state_items,
      EX_pipeline_unchanged_state_items,MEM_pipeline_unchanged_state_items,
      WB_pipeline_unchanged_state_items]
QED


(* additional theorems for the correctness proof *)
Theorem agp32_same_EX_opc_func_until_ALU_update:
  !fext fbits t s s' s''.
    s = agp32 fext fbits t ==>
    s' = procs [agp32_next_state; WB_pipeline; MEM_pipeline; EX_pipeline;
                REG_write; ID_pipeline; IF_PC_update; Acc_compute]
               (fext t) s s ==>
    s'' = procs [ForwardA; ForwardB; ForwardW; IF_instr_update;
                 ID_opc_func_update; ID_imm_update;ID_data_update;
                 EX_ctrl_update; EX_forward_data;
                 EX_ALU_input_update; EX_compute_enable_update]
                (fext (SUC t)) s' s' ==>
    (s''.EX.EX_opc = (agp32 fext fbits (SUC t)).EX.EX_opc) /\
    (s''.EX.EX_func = (agp32 fext fbits (SUC t)).EX.EX_func)
Proof
  rpt STRIP_TAC >>
  Q.ABBREV_TAC `s0 = procs [agp32_next_state;WB_pipeline;MEM_pipeline] (fext t) s s` >>
  `((agp32 fext fbits (SUC t)).EX.EX_opc = (EX_pipeline (fext (SUC t)) s s0).EX.EX_opc) /\
   ((agp32 fext fbits (SUC t)).EX.EX_func = (EX_pipeline (fext (SUC t)) s s0).EX.EX_func)`
    by fs [agp32_EX_opc_func_updated_by_EX_pipeline,Abbr `s0`] >>
  clist_update_state_before_ALU_tac >>
  fs [Abbr `s11`,Abbr `s10`,Abbr `s9`,Abbr `s8`,Abbr `s7`,Abbr `s6`,Abbr `s5`,
      EX_compute_enable_update_def,EX_ALU_input_update_def,EX_forward_data_def,
      EX_ctrl_update_unchanged_EX_pipeline_items,
      ID_data_update_unchanged_EX_pipeline_items,
      ID_imm_update_unchanged_EX_pipeline_items,
      ID_opc_func_update_unchanged_EX_pipeline_items] >>
  fs [Abbr `s4`,Abbr `s3`,Abbr `s2`,Abbr `s1`,Abbr `s'`,
      IF_instr_update_def,ForwardW_def,ForwardB_def,ForwardA_def] >>
  slist_update_state_tac >>
  fs [Abbr `ss8`,Acc_compute_unchanged_EX_pipeline_items,
      Abbr `ss7`,IF_PC_update_unchanged_EX_pipeline_items,
      Abbr `ss6`,ID_pipeline_unchanged_EX_pipeline_items,
      Abbr `ss5`,REG_write_unchanged_EX_pipeline_items,Abbr `ss4`,
      Abbr `s0`,procs_def] >>
  rw [EX_pipeline_def]
QED

Theorem agp32_same_EX_carry_flag_as_before:
  !fext fbits t s s' s''.
    s = agp32 fext fbits t ==>
    s' = procs [agp32_next_state; WB_pipeline; MEM_pipeline; EX_pipeline;
                REG_write; ID_pipeline; IF_PC_update; Acc_compute]
               (fext t) s s ==>
    s'' = procs [ForwardA; ForwardB; ForwardW; IF_instr_update;
                 ID_opc_func_update; ID_imm_update; ID_data_update;
                 EX_ctrl_update; EX_forward_data;
                 EX_ALU_input_update; EX_compute_enable_update]
                (fext (SUC t)) s' s' ==>
    s''.EX.EX_carry_flag = s.EX.EX_carry_flag
Proof
  clist_update_state_before_ALU_tac >>
  fs [Abbr `s11`,Abbr `s10`,Abbr `s9`,Abbr `s8`,Abbr `s7`,Abbr `s6`,Abbr `s5`,
      EX_compute_enable_update_def,EX_ALU_input_update_def,EX_forward_data_def,
      EX_ctrl_update_unchanged_EX_ALU,ID_data_update_unchanged_EX_ALU,
      ID_imm_update_unchanged_EX_ALU,ID_opc_func_update_unchanged_EX_ALU] >>
  fs [Abbr `s4`,Abbr `s3`,Abbr `s2`,Abbr `s1`,Abbr `s'`,
      IF_instr_update_def,ForwardW_def,ForwardB_def,ForwardA_def] >>
  slist_update_state_tac >>
  fs [Abbr `ss8`,Acc_compute_unchanged_EX_ALU,
      Abbr `ss7`,IF_PC_update_unchanged_EX_ALU,
      Abbr `ss6`,ID_pipeline_unchanged_EX_ALU,
      Abbr `ss5`,REG_write_unchanged_EX_ALU,
      Abbr `ss4`,EX_pipeline_unchanged_EX_ALU,
      Abbr `ss3`,MEM_pipeline_unchanged_EX_ALU,
      Abbr `ss2`,WB_pipeline_unchanged_EX_ALU,
      Abbr `ss1`,agp32_next_state_unchanged_EX_ALU]
QED

Theorem agp32_same_items_until_MEM_pipeline:
  !fext fbits t s s'.
    s = agp32 fext fbits t ==>
    s' = procs [agp32_next_state; WB_pipeline; MEM_pipeline] (fext t) s s ==>
    (s'.ID.ID_EX_write_enable <=> s.ID.ID_EX_write_enable) /\
    (s'.ID.ID_opc = s.ID.ID_opc) /\
    (s'.ID.ID_func = s.ID.ID_func) /\
    (s'.EX.EX_NOP_flag <=> s.EX.EX_NOP_flag)
Proof
  rpt STRIP_TAC >> fs [procs_def] >>
  qpat_abbrev_tac `ss1 = agp32_next_state _ _ _` >>
  qpat_abbrev_tac `ss2 = WB_pipeline _ _ _` >>
  qpat_abbrev_tac `ss3 = MEM_pipeline _ _ _` >>
  fs [Abbr `ss3`,MEM_pipeline_unchanged_enable_flags,
      MEM_pipeline_unchanged_ID_opc_func,
      Abbr `ss2`,WB_pipeline_unchanged_enable_flags,
      WB_pipeline_unchanged_ID_opc_func,
      Abbr `ss1`,agp32_next_state_unchanged_enable_flags,
      agp32_next_state_unchanged_ID_opc_func]
QED

Theorem agp32_same_IF_items_until_ID_pipeline:
  !fext fbits t s s'.
    s = agp32 fext fbits t ==>
    s' = procs [agp32_next_state;WB_pipeline;MEM_pipeline;EX_pipeline;
                REG_write;ID_pipeline] (fext t) s s ==>
    (s'.IF.IF_PC_write_enable <=> s.IF.IF_PC_write_enable) /\
    (s'.IF.IF_PC_input = s.IF.IF_PC_input)
Proof
  rpt STRIP_TAC >> fs [procs_def] >>
  qpat_abbrev_tac `ss1 = agp32_next_state _ _ _` >>
  qpat_abbrev_tac `ss2 = WB_pipeline _ _ _` >>
  qpat_abbrev_tac `ss3 = MEM_pipeline _ _ _` >>
  qpat_abbrev_tac `ss4 = EX_pipeline _ _ _` >>
  qpat_abbrev_tac `ss5 = REG_write _ _ _` >>
  qpat_abbrev_tac `ss6 = ID_pipeline _ _ _` >>
  fs [Abbr `ss6`,ID_pipeline_unchanged_IF_items,
      Abbr `ss5`,REG_write_unchanged_IF_items,
      Abbr `ss4`,EX_pipeline_unchanged_IF_items,
      Abbr `ss3`,MEM_pipeline_unchanged_IF_items,
      Abbr `ss2`,WB_pipeline_unchanged_IF_items,
      Abbr `ss1`,agp32_next_state_unchanged_IF_items]
QED

(* states exist to update specific items *)
(** ID_opc and ID_func **)
Theorem agp32_ID_opc_func_exists_ID_opc_func_update:
  !fext fbits t.
    ?s s'.
      ((agp32 fext fbits t).ID.ID_opc =       
       (ID_opc_func_update (fext t) s s').ID.ID_opc) /\
      ((agp32 fext fbits t).ID.ID_func =
       (ID_opc_func_update (fext t) s s').ID.ID_func)
Proof
  rw [] >> Cases_on `t` >>
  rw [agp32_def,mk_module_def,mk_circuit_def] >-
   (clist_update_state_tac >>
    fs [Abbr `s20`,Abbr `s19`,Abbr `s18`,Abbr `s17`,Abbr `s16`,Abbr `s15`,
        Abbr `s14`,Abbr `s13`,Abbr `s12`,Abbr `s11`,Abbr `s10`,Abbr `s9`,Abbr `s8`,
        Hazard_ctrl_unchanged_ID_opc_func,WB_update_unchanged_ID_opc_func,
        MEM_imm_update_unchanged_ID_opc_func,MEM_ctrl_update_unchanged_ID_opc_func,
        IF_PC_input_update_def,EX_data_rec_update_unchanged_ID_opc_func,
        EX_jump_sel_addr_update_unchanged_ID_opc_func,
        EX_SHIFT_update_unchanged_ID_opc_func,
        EX_ALU_update_unchanged_ID_opc_func,
        EX_compute_enable_update_def,EX_ALU_input_update_def,
        EX_forward_data_def,EX_ctrl_update_unchanged_ID_opc_func] >>
    fs [Abbr `s7`,Abbr `s6`,Abbr `s5`,
        ID_data_update_def,ID_imm_update_unchanged_ID_opc_func] >>
    METIS_TAC []) >>
  qpat_abbrev_tac `s'' = mk_circuit (procs _) (procs _) (agp32_init fbits) fext t` >>
  qpat_abbrev_tac `s''' = procs _ (fext t) s'' s''` >>
  clist_update_state_tac >>
  fs [Abbr `s20`,Abbr `s19`,Abbr `s18`,Abbr `s17`,Abbr `s16`,Abbr `s15`,
      Abbr `s14`,Abbr `s13`,Abbr `s12`,Abbr `s11`,Abbr `s10`,Abbr `s9`,Abbr `s8`,
      Hazard_ctrl_unchanged_ID_opc_func,WB_update_unchanged_ID_opc_func,
      MEM_imm_update_unchanged_ID_opc_func,MEM_ctrl_update_unchanged_ID_opc_func,
      IF_PC_input_update_def,EX_data_rec_update_unchanged_ID_opc_func,
      EX_jump_sel_addr_update_unchanged_ID_opc_func,
      EX_SHIFT_update_unchanged_ID_opc_func,
      EX_ALU_update_unchanged_ID_opc_func,
      EX_compute_enable_update_def,EX_ALU_input_update_def,
      EX_forward_data_def,EX_ctrl_update_unchanged_ID_opc_func] >>
  fs [Abbr `s7`,Abbr `s6`,Abbr `s5`,
      ID_data_update_def,ID_imm_update_unchanged_ID_opc_func] >>
  METIS_TAC []
QED

(** control flags **)
Theorem agp32_ctrl_flags_exists_Hazard_ctrl:
  !fext fbits t.
    ?s s'.
      ((agp32 fext fbits t).ID.ID_ID_write_enable <=>
       (Hazard_ctrl (fext t) s s').ID.ID_ID_write_enable) /\
      ((agp32 fext fbits t).ID.ID_EX_write_enable <=>
       (Hazard_ctrl (fext t) s s').ID.ID_EX_write_enable) /\
      ((agp32 fext fbits t).ID.ID_flush_flag <=>
       (Hazard_ctrl (fext t) s s').ID.ID_flush_flag) /\
      ((agp32 fext fbits t).EX.EX_NOP_flag <=>
       (Hazard_ctrl (fext t) s s').EX.EX_NOP_flag)
Proof
  rw [] >> Cases_on `t` >>
  rw [agp32_def,mk_module_def,mk_circuit_def] >-
   (clist_update_state_tac >> METIS_TAC []) >>
  qpat_abbrev_tac `s'' = mk_circuit (procs _) (procs _) (agp32_init fbits) fext t` >>
  qpat_abbrev_tac `s''' = procs _ (fext t) s'' s''` >>
  clist_update_state_tac >>  METIS_TAC []
QED

(* initial command is 0 *)
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

val _ = export_theory ();
