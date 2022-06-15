open hardwarePreamble translatorTheory arithmeticTheory dep_rewrite blastLib bitstringSyntax fcpSyntax listSyntax wordsSyntax wordsLib agp32StateTheory agp32EnvironmentTheory agp32ProcessorTheory;

val _ = new_theory "agp32Update";

val _ = prefer_num ();
val _ = guess_lengths ();

(* show the unchanged part of different circuit functions in the pipelined Silver *)
(** unchanged items by IF_PC_input_update **)
Theorem IF_PC_input_update_unchanged_IF:
  !fext s s'.
    ((IF_PC_input_update fext s s').IF.IF_instr = s'.IF.IF_instr) /\
    ((IF_PC_input_update fext s s').IF.IF_PC_write_enable = s'.IF.IF_PC_write_enable)
Proof
  rw [IF_PC_input_update_def]
QED

(** unchanged items by ID_opc_func_update **)
Theorem ID_opc_func_update_unchanged_IF:
  !fext s s'.
    ((ID_opc_func_update fext s s').IF.IF_PC_input = s'.IF.IF_PC_input) /\
    ((ID_opc_func_update fext s s').IF.IF_instr = s'.IF.IF_instr) /\
    ((ID_opc_func_update fext s s').IF.IF_PC_write_enable = s'.IF.IF_PC_write_enable)
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

(** unchanged items by ID_imm_update **)
Theorem ID_imm_update_unchanged_IF:
  !fext s s'.
    ((ID_imm_update fext s s').IF.IF_PC_input = s'.IF.IF_PC_input) /\
    ((ID_imm_update fext s s').IF.IF_instr = s'.IF.IF_instr) /\
    ((ID_imm_update fext s s').IF.IF_PC_write_enable = s'.IF.IF_PC_write_enable)
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

(** unchanged items by ID_data_update **)
Theorem ID_data_update_unchanged_IF:
  !fext s s'.
    ((ID_data_update fext s s').IF.IF_PC_input = s'.IF.IF_PC_input) /\
    ((ID_data_update fext s s').IF.IF_instr = s'.IF.IF_instr) /\
    ((ID_data_update fext s s').IF.IF_PC_write_enable = s'.IF.IF_PC_write_enable)
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

(** unchanged items by EX_ctrl_update **)
Theorem EX_ctrl_update_unchanged_IF:
  !fext s s'.
    ((EX_ctrl_update fext s s').IF.IF_PC_input = s'.IF.IF_PC_input) /\
    ((EX_ctrl_update fext s s').IF.IF_instr = s'.IF.IF_instr) /\
    ((EX_ctrl_update fext s s').IF.IF_PC_write_enable = s'.IF.IF_PC_write_enable)
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
        
(** unchanged items by EX_forward_data **)
Theorem EX_forward_data_unchanged_IF:
  !fext s s'.
    ((EX_forward_data fext s s').IF.IF_PC_input = s'.IF.IF_PC_input) /\
    ((EX_forward_data fext s s').IF.IF_instr = s'.IF.IF_instr) /\
    ((EX_forward_data fext s s').IF.IF_PC_write_enable = s'.IF.IF_PC_write_enable)
Proof
  rw [EX_forward_data_def]
QED

(** unchanged items by EX_ALU_input_update **)
Theorem EX_ALU_input_update_unchanged_IF:
  !fext s s'.
    ((EX_ALU_input_update fext s s').IF.IF_PC_input = s'.IF.IF_PC_input) /\  
    ((EX_ALU_input_update fext s s').IF.IF_instr = s'.IF.IF_instr) /\
    ((EX_ALU_input_update fext s s').IF.IF_PC_write_enable = s'.IF.IF_PC_write_enable)
Proof
  rw [EX_ALU_input_update_def]
QED

(** unchanged items by EX_compute_enable_update **)
Theorem EX_compute_enable_update_unchanged_IF:
  !fext s s'.
    ((EX_compute_enable_update fext s s').IF.IF_PC_input = s'.IF.IF_PC_input) /\
    ((EX_compute_enable_update fext s s').IF.IF_instr = s'.IF.IF_instr) /\
    ((EX_compute_enable_update fext s s').IF.IF_PC_write_enable = s'.IF.IF_PC_write_enable)
Proof
  rw [EX_compute_enable_update_def]
QED

(** unchanged items by EX_ALU_update **)
Theorem EX_ALU_update_unchanged_IF:
  !fext s s'.
    ((EX_ALU_update fext s s').IF.IF_PC_input = s'.IF.IF_PC_input) /\
    ((EX_ALU_update fext s s').IF.IF_instr = s'.IF.IF_instr) /\
    ((EX_ALU_update fext s s').IF.IF_PC_write_enable = s'.IF.IF_PC_write_enable)
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

(** unchanged items by EX_SHIFT_update **)
Theorem EX_SHIFT_update_unchanged_IF:
  !fext s s'.
    ((EX_SHIFT_update fext s s').IF.IF_PC_input = s'.IF.IF_PC_input) /\
    ((EX_SHIFT_update fext s s').IF.IF_instr = s'.IF.IF_instr) /\
    ((EX_SHIFT_update fext s s').IF.IF_PC_write_enable = s'.IF.IF_PC_write_enable)
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

(** unchanged items by EX_jump_sel_addr_update **)
Theorem EX_jump_sel_addr_update_unchanged_IF:
  !fext s s'.
    ((EX_jump_sel_addr_update fext s s').IF.IF_PC_input = s'.IF.IF_PC_input) /\
    ((EX_jump_sel_addr_update fext s s').IF.IF_instr = s'.IF.IF_instr) /\
    ((EX_jump_sel_addr_update fext s s').IF.IF_PC_write_enable = s'.IF.IF_PC_write_enable)
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
     
(** unchanged items by EX_data_rec_update **)
Theorem EX_data_rec_update_unchanged_IF:
  !fext s s'.
    ((EX_data_rec_update fext s s').IF.IF_PC_input = s'.IF.IF_PC_input) /\   
    ((EX_data_rec_update fext s s').IF.IF_instr = s'.IF.IF_instr) /\
    ((EX_data_rec_update fext s s').IF.IF_PC_write_enable = s'.IF.IF_PC_write_enable)
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

(** unchanged items by MEM_ctrl_update **)
Theorem MEM_ctrl_update_unchanged_IF:
  !fext s s'.
    ((MEM_ctrl_update fext s s').IF.IF_PC_input = s'.IF.IF_PC_input) /\
    ((MEM_ctrl_update fext s s').IF.IF_instr = s'.IF.IF_instr) /\
    ((MEM_ctrl_update fext s s').IF.IF_PC_write_enable = s'.IF.IF_PC_write_enable)
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

(** unchanged items by MEM_imm_update **)
Theorem MEM_imm_update_unchanged_IF:
  !fext s s'.
    ((MEM_imm_update fext s s').IF.IF_PC_input = s'.IF.IF_PC_input) /\
    ((MEM_imm_update fext s s').IF.IF_instr = s'.IF.IF_instr) /\
    ((MEM_imm_update fext s s').IF.IF_PC_write_enable = s'.IF.IF_PC_write_enable)
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

(** unchanged items by WB_update **)
Theorem WB_update_unchanged_IF:
  !fext s s'.
    ((WB_update fext s s').IF.IF_PC_input = s'.IF.IF_PC_input) /\
    ((WB_update fext s s').IF.IF_instr = s'.IF.IF_instr) /\
    ((WB_update fext s s').IF.IF_PC_write_enable = s'.IF.IF_PC_write_enable)
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

(** unchanged items by Hazard_ctrl **)
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

(** unchanged items by Acc_compute **)
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

(** unchanged items by ID_pipeline **)
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

(** unchanged items by REG_write **)
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

(** unchanged items by EX_pipeline **)
Theorem EX_pipeline_unchanged_EX_jump:
  !fext s s'.
    ((EX_pipeline fext s s').EX.EX_jump_sel <=> s'.EX.EX_jump_sel) /\
    ((EX_pipeline fext s s').EX.EX_jump_addr = s'.EX.EX_jump_addr)
Proof
  rw [EX_pipeline_def]
QED

(** unchanged items by MEM_pipeline **)
Theorem MEM_pipeline_unchanged_EX_jump:
  !fext s s'.
    ((MEM_pipeline fext s s').EX.EX_jump_sel <=> s'.EX.EX_jump_sel) /\
    ((MEM_pipeline fext s s').EX.EX_jump_addr = s'.EX.EX_jump_addr)
Proof
  rw [MEM_pipeline_def]
QED

(** unchanged items by WB_pipeline **)
Theorem WB_pipeline_unchanged_EX_jump:
  !fext s s'.
    ((WB_pipeline fext s s').EX.EX_jump_sel <=> s'.EX.EX_jump_sel) /\
    ((WB_pipeline fext s s').EX.EX_jump_addr = s'.EX.EX_jump_addr)
Proof
  rw [WB_pipeline_def]
QED

(** unchanged items by agp32_next_state **)
Theorem agp32_next_state_unchanged_EX_jump:
  !fext s s'.
    ((agp32_next_state fext s s').EX.EX_jump_sel <=> s'.EX.EX_jump_sel) /\
    ((agp32_next_state fext s s').EX.EX_jump_addr = s'.EX.EX_jump_addr)
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


(* circuit variables are only changed by the certain function *)
(** IF_PC_input is only changed by the IF_PC_input_update function **)
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

(** IF_instr is only changed by the IF_instr_update function **)
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

(** EX_carry_flag, EX_ALU_res are only changed by the EX_ALU_update function **)
Theorem agp32_EX_ALU_items_updated_by_EX_ALU_update:
  !fext fbits t s s' s''.
    s = agp32 fext fbits t ==>
    s' = procs [agp32_next_state; WB_pipeline; MEM_pipeline; EX_pipeline;
                REG_write; ID_pipeline; IF_PC_update; Acc_compute]
               (fext t) s s ==>
    s'' = procs [Hazard_ctrl; ForwardA; ForwardB; ForwardW; IF_instr_update;
                 IF_PC_input_update; ID_opc_func_update; ID_imm_update;
                 ID_data_update; EX_ctrl_update; EX_forward_data;
                 EX_ALU_input_update; EX_compute_enable_update]
                (fext (SUC t)) s' s' ==>
    (agp32 fext fbits (SUC t)).EX.EX_carry_flag =
    (EX_ALU_update (fext (SUC t)) s' s'').EX.EX_carry_flag
Proof
  rw [agp32_def,mk_module_def,mk_circuit_def] >>
  qpat_abbrev_tac `s''' = mk_circuit (procs _) (procs _) (agp32_init fbits) fext t` >>
  qpat_abbrev_tac `s'''' = procs _ (fext t) s''' s'''` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s1 = Hazard_ctrl _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s2 = ForwardA _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s3 = ForwardB _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s4 = ForwardW _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s5 = IF_instr_update _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s6 = IF_PC_input_update _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s7 = ID_opc_func_update _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s8 = ID_imm_update _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s9 = ID_data_update _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s10 = EX_ctrl_update _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s11 = EX_forward_data _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s12 = EX_ALU_input_update _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s13 = EX_compute_enable_update _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s14 = EX_ALU_update _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s15 = EX_SHIFT_update _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s16 = EX_jump_sel_addr_update _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s17 = EX_data_rec_update _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s18 = MEM_ctrl_update _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s19 = MEM_imm_update _ _ _` >>
  rw [procs_def] >>
  qpat_abbrev_tac `s20 = WB_update _ _ _` >>
  fs [Abbr `s20`,WB_update_unchanged_EX_ALU,
      Abbr `s19`,MEM_imm_update_unchanged_EX_ALU,
      Abbr `s18`,MEM_ctrl_update_unchanged_EX_ALU,
      Abbr `s17`,EX_data_rec_update_unchanged_EX_ALU,
      Abbr `s16`,EX_jump_sel_addr_update_unchanged_EX_ALU,
      Abbr `s15`,EX_SHIFT_update_unchanged_EX_ALU]
QED

(** EX_opc is only updated by the EX_pipeline function **)
Theorem agp32_EX_opc_updated_EX_pipeline:
  !fext fbits t s s' s''.
    s' = agp32 fext fbits t ==>
    s'' = procs [agp32_next_state;WB_pipeline;MEM_pipeline] (fext t) s' s' ==>
    (agp32 fext fbits (SUC t)).EX.EX_opc =
    (EX_pipeline (fext (SUC t)) s s'').EX.EX_opc
Proof
  rw [agp32_def,mk_module_def,mk_circuit_def] >>
  qpat_abbrev_tac `s'' = mk_circuit (procs _) (procs _) (agp32_init fbits) fext t` >>
  qpat_abbrev_tac `s''' = procs _ (fext t) s'' s''` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s1 = Hazard_ctrl _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s2 = ForwardA _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s3 = ForwardB _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s4 = ForwardW _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s5 = IF_instr_update _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s6 = IF_PC_input_update _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s7 = ID_opc_func_update _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s8 = ID_imm_update _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s9 = ID_data_update _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s10 = EX_ctrl_update _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s11 = EX_forward_data _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s12 = EX_ALU_input_update _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s13 = EX_compute_enable_update _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s14 = EX_ALU_update _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s15 = EX_SHIFT_update _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s16 = EX_jump_sel_addr_update _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s17 = EX_data_rec_update _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s18 = MEM_ctrl_update _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s19 = MEM_imm_update _ _ _` >>
  rw [procs_def] >>
  qpat_abbrev_tac `s20 = WB_update _ _ _` >>
  fs [Abbr `s20`,WB_update_unchanged_EX_pipeline_items,
      Abbr `s19`,MEM_imm_update_def,
      Abbr `s18`,MEM_ctrl_update_unchanged_EX_pipeline_items,
      Abbr `s17`,EX_data_rec_update_unchanged_EX_pipeline_items,
      Abbr `s16`,EX_jump_sel_addr_update_unchanged_EX_pipeline_items,
      Abbr `s15`,EX_SHIFT_update_unchanged_EX_pipeline_items,
      Abbr `s14`,EX_ALU_update_unchanged_EX_pipeline_items,
      Abbr `s13`,EX_compute_enable_update_def,
      Abbr `s12`,EX_ALU_input_update_def,
      Abbr `s11`,EX_forward_data_def,
      Abbr `s10`,EX_ctrl_update_unchanged_EX_pipeline_items,
      Abbr `s9`,ID_data_update_unchanged_EX_pipeline_items,
      Abbr `s8`,ID_imm_update_unchanged_EX_pipeline_items,
      Abbr `s7`,ID_opc_func_update_unchanged_EX_pipeline_items] >>
  fs [Abbr `s6`,IF_PC_input_update_def,
      Abbr `s5`,IF_instr_update_def,
      Abbr `s4`,ForwardW_def,Abbr `s3`,ForwardB_def,Abbr `s2`,ForwardA_def,
      Abbr `s1`,Hazard_ctrl_unchanged_EX_pipeline_items,Abbr `s'''`] >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s21 = agp32_next_state _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s22 = WB_pipeline _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s23 = MEM_pipeline _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s24 = EX_pipeline _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s25 = REG_write _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s26 = ID_pipeline _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s27 = IF_PC_update _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s28 = Acc_compute _ _ _` >>
  rw [Once procs_def] >>
  fs [Abbr `s28`,Acc_compute_unchanged_EX_pipeline_items,
      Abbr `s27`,IF_PC_update_unchanged_EX_pipeline_items,
      Abbr `s26`,ID_pipeline_unchanged_EX_pipeline_items,
      Abbr `s25`,REG_write_unchanged_EX_pipeline_items,Abbr `s24`] >>
  rw [EX_pipeline_def]
QED


(* additional theorems for the correctness proof *)
Theorem agp32_same_EX_opc_until_ALU_update:
  !fext fbits t s s' s''.
    s = agp32 fext fbits t ==>
    s' = procs [agp32_next_state; WB_pipeline; MEM_pipeline; EX_pipeline;
                REG_write; ID_pipeline; IF_PC_update; Acc_compute]
               (fext t) s s ==>
    s'' = procs [Hazard_ctrl; ForwardA; ForwardB; ForwardW; IF_instr_update;
                 IF_PC_input_update; ID_opc_func_update; ID_imm_update;
                 ID_data_update; EX_ctrl_update; EX_forward_data;
                 EX_ALU_input_update; EX_compute_enable_update]
                (fext (SUC t)) s' s' ==>
    s''.EX.EX_opc = (agp32 fext fbits (SUC t)).EX.EX_opc
Proof
  cheat
QED

val _ = export_theory ();
