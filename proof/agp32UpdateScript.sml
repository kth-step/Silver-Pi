open hardwarePreamble translatorTheory arithmeticTheory dep_rewrite blastLib bitstringSyntax fcpSyntax listSyntax wordsSyntax wordsLib agp32StateTheory agp32EnvironmentTheory agp32ProcessorTheory agp32UpdateLib;

(* Theorems about the pipelined circuit's state update functions *)
val _ = new_theory "agp32Update";

val _ = prefer_num ();
val _ = guess_lengths ();

(* show the unchanged part of different circuit functions in the pipelined Silver *)
(** unchanged items by IF_instr_update **)
Theorem IF_instr_update_unchanged_enable_flags:
  !fext s s'.
    ((IF_instr_update fext s s').ID.ID_EX_write_enable <=> s'.ID.ID_EX_write_enable) /\
    ((IF_instr_update fext s s').EX.EX_NOP_flag <=> s'.EX.EX_NOP_flag) /\
    ((IF_instr_update fext s s').MEM.MEM_state_flag <=> s'.MEM.MEM_state_flag)
Proof
  rw [IF_instr_update_def]
QED

Theorem IF_instr_update_unchanged_IF:
  !fext s s'.
    ((IF_instr_update fext s s').IF.IF_PC_input = s'.IF.IF_PC_input) /\
    ((IF_instr_update fext s s').IF.IF_PC_write_enable = s'.IF.IF_PC_write_enable) /\
    ((IF_instr_update fext s s').PC = s'.PC)
Proof
  rw [IF_instr_update_def]
QED

Theorem IF_instr_update_unchanged_ID_pipeline_items:
  !fext s s'.
    ((IF_instr_update fext s s').ID.ID_PC = s'.ID.ID_PC) /\
    ((IF_instr_update fext s s').ID.ID_instr = s'.ID.ID_instr)
Proof
  rw [IF_instr_update_def]
QED

Theorem IF_instr_update_unchanged_EX_pipeline_items:
  !fext s s'.
    ((IF_instr_update fext s s').EX.EX_PC = s'.EX.EX_PC) /\
    ((IF_instr_update fext s s').EX.EX_dataA = s'.EX.EX_dataA) /\
    ((IF_instr_update fext s s').EX.EX_dataB = s'.EX.EX_dataB) /\
    ((IF_instr_update fext s s').EX.EX_dataW = s'.EX.EX_dataW) /\
    ((IF_instr_update fext s s').EX.EX_imm = s'.EX.EX_imm) /\
    ((IF_instr_update fext s s').EX.EX_addrW = s'.EX.EX_addrW) /\
    ((IF_instr_update fext s s').EX.EX_write_reg = s'.EX.EX_write_reg) /\
    ((IF_instr_update fext s s').EX.EX_opc = s'.EX.EX_opc) /\
    ((IF_instr_update fext s s').EX.EX_func = s'.EX.EX_func)
Proof
  rw [IF_instr_update_def]
QED

Theorem IF_instr_update_unchanged_EX_ctrl_items:
  !fext s s'.
    (IF_instr_update fext s s').EX.EX_PC_sel = s'.EX.EX_PC_sel
Proof
  rw [IF_instr_update_def]
QED

Theorem IF_instr_update_unchanged_EX_ALU:
  !fext s s'.
    ((IF_instr_update fext s s').EX.EX_ALU_res = s'.EX.EX_ALU_res) /\
    ((IF_instr_update fext s s').EX.EX_carry_flag = s'.EX.EX_carry_flag) /\
    ((IF_instr_update fext s s').EX.EX_overflow_flag = s'.EX.EX_overflow_flag)
Proof
  rw [IF_instr_update_def]
QED

Theorem IF_instr_update_unchanged_MEM_pipeline_items:
  !fext s s'.
    ((IF_instr_update fext s s').MEM.MEM_PC = s'.MEM.MEM_PC) /\
    ((IF_instr_update fext s s').MEM.MEM_dataA = s'.MEM.MEM_dataA) /\
    ((IF_instr_update fext s s').MEM.MEM_dataB = s'.MEM.MEM_dataB) /\
    ((IF_instr_update fext s s').MEM.MEM_imm = s'.MEM.MEM_imm) /\
    ((IF_instr_update fext s s').MEM.MEM_ALU_res = s'.MEM.MEM_ALU_res) /\
    ((IF_instr_update fext s s').MEM.MEM_SHIFT_res = s'.MEM.MEM_SHIFT_res) /\
    ((IF_instr_update fext s s').MEM.MEM_addrW = s'.MEM.MEM_addrW) /\
    ((IF_instr_update fext s s').MEM.MEM_opc = s'.MEM.MEM_opc) /\
    ((IF_instr_update fext s s').MEM.MEM_write_reg <=> s'.MEM.MEM_write_reg)
Proof
  rw [IF_instr_update_def]
QED

Theorem IF_instr_update_unchanged_WB_ctrl_items:
  !fext s s'.
    ((IF_instr_update fext s s').WB.WB_state_flag = s'.WB.WB_state_flag)
Proof
  rw [IF_instr_update_def]
QED

Theorem IF_instr_update_unchanged_WB_pipeline_items:
  !fext s s'.
    ((IF_instr_update fext s s').WB.WB_write_reg <=> s'.WB.WB_write_reg) /\
    ((IF_instr_update fext s s').WB.WB_addrW = s'.WB.WB_addrW)
Proof
  rw [IF_instr_update_def]
QED

Theorem IF_instr_update_unchanged_state_items:
  !fext s s'.
    ((IF_instr_update fext s s').command = s'.command) /\
    ((IF_instr_update fext s s').state = s'.state) /\
    ((IF_instr_update fext s s').R = s'.R)
Proof
  rw [IF_instr_update_def]
QED

(** unchanged items by IF_PC_input_update **)
Theorem IF_PC_input_update_unchanged_IF:
  !fext s s'.
    ((IF_PC_input_update fext s s').IF.IF_instr = s'.IF.IF_instr) /\
    ((IF_PC_input_update fext s s').IF.IF_PC_write_enable = s'.IF.IF_PC_write_enable) /\
    ((IF_PC_input_update fext s s').PC = s'.PC)
Proof
  rw [IF_PC_input_update_def]
QED

Theorem IF_PC_input_update_unchanged_ID_pipeline_items:
  !fext s s'.
    ((IF_PC_input_update fext s s').ID.ID_PC = s'.ID.ID_PC) /\
    ((IF_PC_input_update fext s s').ID.ID_instr = s'.ID.ID_instr)
Proof
  rw [IF_PC_input_update_def]
QED

Theorem IF_PC_input_update_unchanged_ID_opc_func:
  !fext s s'.
    ((IF_PC_input_update fext s s').ID.ID_opc = s'.ID.ID_opc) /\
    ((IF_PC_input_update fext s s').ID.ID_func = s'.ID.ID_func)
Proof
  rw [IF_PC_input_update_def]
QED

Theorem IF_PC_input_update_unchanged_ID_data_items:
  !fext s s'.
    ((IF_PC_input_update fext s s').ID.ID_addrA = s'.ID.ID_addrA) /\
    ((IF_PC_input_update fext s s').ID.ID_addrB = s'.ID.ID_addrB) /\
    ((IF_PC_input_update fext s s').ID.ID_addrW = s'.ID.ID_addrW) /\
    ((IF_PC_input_update fext s s').ID.ID_addrA_disable = s'.ID.ID_addrA_disable) /\
    ((IF_PC_input_update fext s s').ID.ID_addrB_disable = s'.ID.ID_addrB_disable) /\
    ((IF_PC_input_update fext s s').ID.ID_addrW_disable = s'.ID.ID_addrW_disable) /\
    ((IF_PC_input_update fext s s').ID.ID_read_dataA = s'.ID.ID_read_dataA) /\
    ((IF_PC_input_update fext s s').ID.ID_read_dataB = s'.ID.ID_read_dataB) /\
    ((IF_PC_input_update fext s s').ID.ID_read_dataW = s'.ID.ID_read_dataW) /\
    ((IF_PC_input_update fext s s').ID.ID_immA = s'.ID.ID_immA) /\
    ((IF_PC_input_update fext s s').ID.ID_immB = s'.ID.ID_immB) /\
    ((IF_PC_input_update fext s s').ID.ID_immW = s'.ID.ID_immW) /\
    ((IF_PC_input_update fext s s').ID.ID_imm = s'.ID.ID_imm) /\
    ((IF_PC_input_update fext s s').ID.ID_dataA = s'.ID.ID_dataA) /\
    ((IF_PC_input_update fext s s').ID.ID_dataB = s'.ID.ID_dataB) /\
    ((IF_PC_input_update fext s s').ID.ID_dataW = s'.ID.ID_dataW)
Proof
  rw [IF_PC_input_update_def]
QED

Theorem IF_PC_input_update_unchanged_ID_data_check_items:
  !fext s s'.
    ((IF_PC_input_update fext s s').EX.EX_checkA = s'.EX.EX_checkA) /\
    ((IF_PC_input_update fext s s').EX.EX_checkB = s'.EX.EX_checkB) /\
    ((IF_PC_input_update fext s s').EX.EX_checkW = s'.EX.EX_checkW) /\
    ((IF_PC_input_update fext s s').MEM.MEM_checkA = s'.MEM.MEM_checkA) /\
    ((IF_PC_input_update fext s s').MEM.MEM_checkB = s'.MEM.MEM_checkB) /\
    ((IF_PC_input_update fext s s').MEM.MEM_checkW = s'.MEM.MEM_checkW) /\
    ((IF_PC_input_update fext s s').WB.WB_checkA = s'.WB.WB_checkA) /\
    ((IF_PC_input_update fext s s').WB.WB_checkB = s'.WB.WB_checkB) /\
    ((IF_PC_input_update fext s s').WB.WB_checkW = s'.WB.WB_checkW)
Proof
  rw [IF_PC_input_update_def]
QED

Theorem IF_PC_input_update_unchanged_EX_pipeline_items:
  !fext s s'.
    ((IF_PC_input_update fext s s').EX.EX_PC = s'.EX.EX_PC) /\
    ((IF_PC_input_update fext s s').EX.EX_dataA = s'.EX.EX_dataA) /\
    ((IF_PC_input_update fext s s').EX.EX_dataB = s'.EX.EX_dataB) /\
    ((IF_PC_input_update fext s s').EX.EX_dataW = s'.EX.EX_dataW) /\
    ((IF_PC_input_update fext s s').EX.EX_imm = s'.EX.EX_imm) /\
    ((IF_PC_input_update fext s s').EX.EX_addrW = s'.EX.EX_addrW) /\
    ((IF_PC_input_update fext s s').EX.EX_write_reg = s'.EX.EX_write_reg) /\
    ((IF_PC_input_update fext s s').EX.EX_opc = s'.EX.EX_opc) /\
    ((IF_PC_input_update fext s s').EX.EX_func = s'.EX.EX_func)
Proof
  rw [IF_PC_input_update_def]
QED

Theorem IF_PC_input_update_unchanged_EX_ctrl_items:
  !fext s s'.
    ((IF_PC_input_update fext s s').EX.EX_PC_sel = s'.EX.EX_PC_sel) /\
    ((IF_PC_input_update fext s s').EX.EX_imm_updated = s'.EX.EX_imm_updated)
Proof
  rw [IF_PC_input_update_def]
QED

Theorem IF_PC_input_update_unchanged_EX_ALU:
  !fext s s'.
    ((IF_PC_input_update fext s s').EX.EX_ALU_input1 = s'.EX.EX_ALU_input1) /\
    ((IF_PC_input_update fext s s').EX.EX_ALU_input2 = s'.EX.EX_ALU_input2) /\
    ((IF_PC_input_update fext s s').EX.EX_ALU_res = s'.EX.EX_ALU_res) /\
    ((IF_PC_input_update fext s s').EX.EX_carry_flag = s'.EX.EX_carry_flag) /\
    ((IF_PC_input_update fext s s').EX.EX_overflow_flag = s'.EX.EX_overflow_flag)
Proof
  rw [IF_PC_input_update_def]
QED

Theorem IF_PC_input_update_unchanged_EX_jump:
  !fext s s'.
    ((IF_PC_input_update fext s s').EX.EX_jump_sel <=> s'.EX.EX_jump_sel) /\
    ((IF_PC_input_update fext s s').EX.EX_jump_addr = s'.EX.EX_jump_addr)
Proof
  rw [IF_PC_input_update_def]
QED

Theorem IF_PC_input_update_unchanged_MEM_pipeline_items:
  !fext s s'.
    ((IF_PC_input_update fext s s').MEM.MEM_PC = s'.MEM.MEM_PC) /\
    ((IF_PC_input_update fext s s').MEM.MEM_dataA = s'.MEM.MEM_dataA) /\
    ((IF_PC_input_update fext s s').MEM.MEM_dataB = s'.MEM.MEM_dataB) /\
    ((IF_PC_input_update fext s s').MEM.MEM_imm = s'.MEM.MEM_imm) /\
    ((IF_PC_input_update fext s s').MEM.MEM_ALU_res = s'.MEM.MEM_ALU_res) /\
    ((IF_PC_input_update fext s s').MEM.MEM_SHIFT_res = s'.MEM.MEM_SHIFT_res) /\
    ((IF_PC_input_update fext s s').MEM.MEM_addrW = s'.MEM.MEM_addrW) /\
    ((IF_PC_input_update fext s s').MEM.MEM_opc = s'.MEM.MEM_opc) /\
    ((IF_PC_input_update fext s s').MEM.MEM_write_reg <=> s'.MEM.MEM_write_reg)
Proof
  rw [IF_PC_input_update_def]
QED

Theorem IF_PC_input_update_unchanged_WB_ctrl_items:
  !fext s s'.
    ((IF_PC_input_update fext s s').WB.WB_state_flag = s'.WB.WB_state_flag)
Proof
  rw [IF_PC_input_update_def]
QED

Theorem IF_PC_input_update_unchanged_WB_pipeline_items:
  !fext s s'.
    ((IF_PC_input_update fext s s').WB.WB_write_reg <=> s'.WB.WB_write_reg) /\
    ((IF_PC_input_update fext s s').WB.WB_addrW = s'.WB.WB_addrW)
Proof
  rw [IF_PC_input_update_def]
QED

Theorem IF_PC_input_update_unchanged_state_items:
  !fext s s'.
    ((IF_PC_input_update fext s s').command = s'.command) /\
    ((IF_PC_input_update fext s s').state = s'.state) /\
    ((IF_PC_input_update fext s s').R = s'.R)
Proof
  rw [IF_PC_input_update_def]
QED

(** unchanged items by ID_opc_func_update **)
Theorem ID_opc_func_update_unchanged_enable_flags:
  !fext s s'.
    ((ID_opc_func_update fext s s').ID.ID_EX_write_enable <=> s'.ID.ID_EX_write_enable) /\
    ((ID_opc_func_update fext s s').EX.EX_NOP_flag <=> s'.EX.EX_NOP_flag) /\
    ((ID_opc_func_update fext s s').MEM.MEM_state_flag <=> s'.MEM.MEM_state_flag)
Proof
  rw [ID_opc_func_update_def]
QED

Theorem ID_opc_func_update_unchanged_IF:
  !fext s s'.
    ((ID_opc_func_update fext s s').IF.IF_PC_input = s'.IF.IF_PC_input) /\
    ((ID_opc_func_update fext s s').IF.IF_instr = s'.IF.IF_instr) /\
    ((ID_opc_func_update fext s s').IF.IF_PC_write_enable = s'.IF.IF_PC_write_enable) /\
    ((ID_opc_func_update fext s s').PC = s'.PC)
Proof
  rw [ID_opc_func_update_def]
QED

Theorem ID_opc_func_update_unchanged_ID_pipeline_items:
  !fext s s'.
    ((ID_opc_func_update fext s s').ID.ID_PC = s'.ID.ID_PC) /\
    ((ID_opc_func_update fext s s').ID.ID_instr = s'.ID.ID_instr)
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
    ((ID_opc_func_update fext s s').EX.EX_addrW = s'.EX.EX_addrW) /\
    ((ID_opc_func_update fext s s').EX.EX_write_reg = s'.EX.EX_write_reg) /\
    ((ID_opc_func_update fext s s').EX.EX_opc = s'.EX.EX_opc) /\
    ((ID_opc_func_update fext s s').EX.EX_func = s'.EX.EX_func)
Proof
  rw [ID_opc_func_update_def]
QED

Theorem ID_opc_func_update_unchanged_EX_ctrl_items:
  !fext s s'.
    (ID_opc_func_update fext s s').EX.EX_PC_sel = s'.EX.EX_PC_sel
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

Theorem ID_opc_func_update_unchanged_MEM_pipeline_items:
  !fext s s'.
    ((ID_opc_func_update fext s s').MEM.MEM_PC = s'.MEM.MEM_PC) /\
    ((ID_opc_func_update fext s s').MEM.MEM_dataA = s'.MEM.MEM_dataA) /\
    ((ID_opc_func_update fext s s').MEM.MEM_dataB = s'.MEM.MEM_dataB) /\
    ((ID_opc_func_update fext s s').MEM.MEM_imm = s'.MEM.MEM_imm) /\
    ((ID_opc_func_update fext s s').MEM.MEM_ALU_res = s'.MEM.MEM_ALU_res) /\
    ((ID_opc_func_update fext s s').MEM.MEM_SHIFT_res = s'.MEM.MEM_SHIFT_res) /\
    ((ID_opc_func_update fext s s').MEM.MEM_addrW = s'.MEM.MEM_addrW) /\
    ((ID_opc_func_update fext s s').MEM.MEM_opc = s'.MEM.MEM_opc) /\
    ((ID_opc_func_update fext s s').MEM.MEM_write_reg <=> s'.MEM.MEM_write_reg)
Proof
  rw [ID_opc_func_update_def]
QED

Theorem ID_opc_func_update_unchanged_WB_ctrl_items:
  !fext s s'.
    ((ID_opc_func_update fext s s').WB.WB_state_flag = s'.WB.WB_state_flag)
Proof
  rw [ID_opc_func_update_def]
QED

Theorem ID_opc_func_update_unchanged_WB_pipeline_items:
  !fext s s'.
    ((ID_opc_func_update fext s s').WB.WB_write_reg <=> s'.WB.WB_write_reg) /\
    ((ID_opc_func_update fext s s').WB.WB_addrW = s'.WB.WB_addrW)
Proof
  rw [ID_opc_func_update_def]
QED

Theorem ID_opc_func_update_unchanged_state_items:
  !fext s s'.
    ((ID_opc_func_update fext s s').command = s'.command) /\
    ((ID_opc_func_update fext s s').state = s'.state) /\
    ((ID_opc_func_update fext s s').R = s'.R)
Proof
  rw [ID_opc_func_update_def]
QED

(** unchanged items by ID_imm_update **)
Theorem ID_imm_update_unchanged_enable_flags:
  !fext s s'.
    ((ID_imm_update fext s s').ID.ID_EX_write_enable <=> s'.ID.ID_EX_write_enable) /\
    ((ID_imm_update fext s s').EX.EX_NOP_flag <=> s'.EX.EX_NOP_flag) /\
    ((ID_imm_update fext s s').MEM.MEM_state_flag <=> s'.MEM.MEM_state_flag)
Proof
  rw [ID_imm_update_def]
QED

Theorem ID_imm_update_unchanged_IF:
  !fext s s'.
    ((ID_imm_update fext s s').IF.IF_PC_input = s'.IF.IF_PC_input) /\
    ((ID_imm_update fext s s').IF.IF_instr = s'.IF.IF_instr) /\
    ((ID_imm_update fext s s').IF.IF_PC_write_enable = s'.IF.IF_PC_write_enable) /\
    ((ID_imm_update fext s s').PC = s'.PC)                
Proof
  rw [ID_imm_update_def]
QED

Theorem ID_imm_update_unchanged_ID_pipeline_items:
  !fext s s'.
    ((ID_imm_update fext s s').ID.ID_PC = s'.ID.ID_PC) /\
    ((ID_imm_update fext s s').ID.ID_instr = s'.ID.ID_instr)
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
    ((ID_imm_update fext s s').EX.EX_addrW = s'.EX.EX_addrW) /\
    ((ID_imm_update fext s s').EX.EX_write_reg = s'.EX.EX_write_reg) /\
    ((ID_imm_update fext s s').EX.EX_opc = s'.EX.EX_opc) /\
    ((ID_imm_update fext s s').EX.EX_func = s'.EX.EX_func)
Proof
  rw [ID_imm_update_def]
QED

Theorem ID_imm_update_unchanged_EX_ctrl_items:
  !fext s s'.
    (ID_imm_update fext s s').EX.EX_PC_sel = s'.EX.EX_PC_sel
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

Theorem ID_imm_update_unchanged_MEM_pipeline_items:
  !fext s s'.
    ((ID_imm_update fext s s').MEM.MEM_PC = s'.MEM.MEM_PC) /\
    ((ID_imm_update fext s s').MEM.MEM_dataA = s'.MEM.MEM_dataA) /\
    ((ID_imm_update fext s s').MEM.MEM_dataB = s'.MEM.MEM_dataB) /\
    ((ID_imm_update fext s s').MEM.MEM_imm = s'.MEM.MEM_imm) /\
    ((ID_imm_update fext s s').MEM.MEM_ALU_res = s'.MEM.MEM_ALU_res) /\
    ((ID_imm_update fext s s').MEM.MEM_SHIFT_res = s'.MEM.MEM_SHIFT_res) /\
    ((ID_imm_update fext s s').MEM.MEM_addrW = s'.MEM.MEM_addrW) /\
    ((ID_imm_update fext s s').MEM.MEM_opc = s'.MEM.MEM_opc) /\
    ((ID_imm_update fext s s').MEM.MEM_write_reg <=> s'.MEM.MEM_write_reg)
Proof
  rw [ID_imm_update_def]
QED

Theorem ID_imm_update_unchanged_WB_ctrl_items:
  !fext s s'.
    ((ID_imm_update fext s s').WB.WB_state_flag = s'.WB.WB_state_flag)
Proof
  rw [ID_imm_update_def]
QED

Theorem ID_imm_update_unchanged_WB_pipeline_items:
  !fext s s'.
    ((ID_imm_update fext s s').WB.WB_write_reg <=> s'.WB.WB_write_reg) /\
    ((ID_imm_update fext s s').WB.WB_addrW = s'.WB.WB_addrW)
Proof
  rw [ID_imm_update_def]
QED

Theorem ID_imm_update_unchanged_state_items:
  !fext s s'.
    ((ID_imm_update fext s s').command = s'.command) /\
    ((ID_imm_update fext s s').state = s'.state) /\
    ((ID_imm_update fext s s').R = s'.R)
Proof
  rw [ID_imm_update_def]
QED

(** unchanged items by ID_data_update **)
Theorem ID_data_update_unchanged_enable_flags:
  !fext s s'.
    ((ID_data_update fext s s').ID.ID_EX_write_enable <=> s'.ID.ID_EX_write_enable) /\
    ((ID_data_update fext s s').EX.EX_NOP_flag <=> s'.EX.EX_NOP_flag) /\
    ((ID_data_update fext s s').MEM.MEM_state_flag <=> s'.MEM.MEM_state_flag)
Proof
  rw [ID_data_update_def]
QED

Theorem ID_data_update_unchanged_IF:
  !fext s s'.
    ((ID_data_update fext s s').IF.IF_PC_input = s'.IF.IF_PC_input) /\
    ((ID_data_update fext s s').IF.IF_instr = s'.IF.IF_instr) /\
    ((ID_data_update fext s s').IF.IF_PC_write_enable = s'.IF.IF_PC_write_enable) /\
    ((ID_data_update fext s s').PC = s'.PC)
Proof
  rw [ID_data_update_def]
QED

Theorem ID_data_update_unchanged_ID_pipeline_items:
  !fext s s'.
    ((ID_data_update fext s s').ID.ID_PC = s'.ID.ID_PC) /\
    ((ID_data_update fext s s').ID.ID_instr = s'.ID.ID_instr)
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

Theorem ID_data_update_unchanged_ID_data_items:
  !fext s s'.
    (ID_data_update fext s s').ID.ID_imm = s'.ID.ID_imm
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
    ((ID_data_update fext s s').EX.EX_addrW = s'.EX.EX_addrW) /\
    ((ID_data_update fext s s').EX.EX_write_reg = s'.EX.EX_write_reg) /\
    ((ID_data_update fext s s').EX.EX_opc = s'.EX.EX_opc) /\
    ((ID_data_update fext s s').EX.EX_func = s'.EX.EX_func)
Proof
  rw [ID_data_update_def]
QED

Theorem ID_data_update_unchanged_EX_ctrl_items:
  !fext s s'.
    (ID_data_update fext s s').EX.EX_PC_sel = s'.EX.EX_PC_sel
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

Theorem ID_data_update_unchanged_MEM_pipeline_items:
  !fext s s'.
    ((ID_data_update fext s s').MEM.MEM_PC = s'.MEM.MEM_PC) /\
    ((ID_data_update fext s s').MEM.MEM_dataA = s'.MEM.MEM_dataA) /\
    ((ID_data_update fext s s').MEM.MEM_dataB = s'.MEM.MEM_dataB) /\
    ((ID_data_update fext s s').MEM.MEM_imm = s'.MEM.MEM_imm) /\
    ((ID_data_update fext s s').MEM.MEM_ALU_res = s'.MEM.MEM_ALU_res) /\
    ((ID_data_update fext s s').MEM.MEM_SHIFT_res = s'.MEM.MEM_SHIFT_res) /\
    ((ID_data_update fext s s').MEM.MEM_addrW = s'.MEM.MEM_addrW) /\
    ((ID_data_update fext s s').MEM.MEM_opc = s'.MEM.MEM_opc) /\
    ((ID_data_update fext s s').MEM.MEM_write_reg <=> s'.MEM.MEM_write_reg)
Proof
  rw [ID_data_update_def]
QED

Theorem ID_data_update_unchanged_WB_pipeline_items:
  !fext s s'.
    ((ID_data_update fext s s').WB.WB_write_reg <=> s'.WB.WB_write_reg) /\
    ((ID_data_update fext s s').WB.WB_addrW = s'.WB.WB_addrW)
Proof
  rw [ID_data_update_def]
QED

Theorem ID_data_update_unchanged_state_items:
  !fext s s'.
    ((ID_data_update fext s s').command = s'.command) /\
    ((ID_data_update fext s s').state = s'.state) /\
    ((ID_data_update fext s s').R = s'.R)
Proof
  rw [ID_data_update_def]
QED

(** unchanged items by ID_data_check_update **)
Theorem ID_data_check_update_unchanged_enable_flags:
  !fext s s'.
    ((ID_data_check_update fext s s').ID.ID_EX_write_enable <=> s'.ID.ID_EX_write_enable) /\
    ((ID_data_check_update fext s s').EX.EX_NOP_flag <=> s'.EX.EX_NOP_flag) /\
    ((ID_data_check_update fext s s').MEM.MEM_state_flag <=> s'.MEM.MEM_state_flag)
Proof
  rw [ID_data_check_update_def]
QED

Theorem ID_data_check_update_unchanged_IF:
  !fext s s'.
    ((ID_data_check_update fext s s').IF.IF_PC_input = s'.IF.IF_PC_input) /\
    ((ID_data_check_update fext s s').IF.IF_instr = s'.IF.IF_instr) /\
    ((ID_data_check_update fext s s').IF.IF_PC_write_enable = s'.IF.IF_PC_write_enable) /\
    ((ID_data_check_update fext s s').PC = s'.PC)
Proof
  rw [ID_data_check_update_def]
QED

Theorem ID_data_check_update_unchanged_ID_pipeline_items:
  !fext s s'.
    ((ID_data_check_update fext s s').ID.ID_PC = s'.ID.ID_PC) /\
    ((ID_data_check_update fext s s').ID.ID_instr = s'.ID.ID_instr)
Proof
  rw [ID_data_check_update_def]
QED

Theorem ID_data_check_update_unchanged_ID_opc_func:
  !fext s s'.
    ((ID_data_check_update fext s s').ID.ID_opc = s'.ID.ID_opc) /\
    ((ID_data_check_update fext s s').ID.ID_func = s'.ID.ID_func)
Proof
  rw [ID_data_check_update_def]
QED

Theorem ID_data_check_update_unchanged_ID_data_items:
  !fext s s'.
    ((ID_data_check_update fext s s').ID.ID_addrA = s'.ID.ID_addrA) /\
    ((ID_data_check_update fext s s').ID.ID_addrB = s'.ID.ID_addrB) /\
    ((ID_data_check_update fext s s').ID.ID_addrW = s'.ID.ID_addrW) /\
    ((ID_data_check_update fext s s').ID.ID_addrA_disable = s'.ID.ID_addrA_disable) /\
    ((ID_data_check_update fext s s').ID.ID_addrB_disable = s'.ID.ID_addrB_disable) /\
    ((ID_data_check_update fext s s').ID.ID_addrW_disable = s'.ID.ID_addrW_disable) /\
    ((ID_data_check_update fext s s').ID.ID_read_dataA = s'.ID.ID_read_dataA) /\
    ((ID_data_check_update fext s s').ID.ID_read_dataB = s'.ID.ID_read_dataB) /\
    ((ID_data_check_update fext s s').ID.ID_read_dataW = s'.ID.ID_read_dataW) /\
    ((ID_data_check_update fext s s').ID.ID_immA = s'.ID.ID_immA) /\
    ((ID_data_check_update fext s s').ID.ID_immB = s'.ID.ID_immB) /\
    ((ID_data_check_update fext s s').ID.ID_immW = s'.ID.ID_immW) /\
    ((ID_data_check_update fext s s').ID.ID_imm = s'.ID.ID_imm) /\
    ((ID_data_check_update fext s s').ID.ID_dataA = s'.ID.ID_dataA) /\
    ((ID_data_check_update fext s s').ID.ID_dataB = s'.ID.ID_dataB) /\
    ((ID_data_check_update fext s s').ID.ID_dataW = s'.ID.ID_dataW)
Proof
  rw [ID_data_check_update_def]
QED

Theorem ID_data_check_update_unchanged_EX_pipeline_items:
  !fext s s'.
    ((ID_data_check_update fext s s').EX.EX_PC = s'.EX.EX_PC) /\
    ((ID_data_check_update fext s s').EX.EX_dataA = s'.EX.EX_dataA) /\
    ((ID_data_check_update fext s s').EX.EX_dataB = s'.EX.EX_dataB) /\
    ((ID_data_check_update fext s s').EX.EX_dataW = s'.EX.EX_dataW) /\
    ((ID_data_check_update fext s s').EX.EX_imm = s'.EX.EX_imm) /\
    ((ID_data_check_update fext s s').EX.EX_addrW = s'.EX.EX_addrW) /\
    ((ID_data_check_update fext s s').EX.EX_write_reg = s'.EX.EX_write_reg) /\
    ((ID_data_check_update fext s s').EX.EX_opc = s'.EX.EX_opc) /\
    ((ID_data_check_update fext s s').EX.EX_func = s'.EX.EX_func)
Proof
  rw [ID_data_check_update_def]
QED

Theorem ID_data_check_update_unchanged_EX_ctrl_items:
  !fext s s'.
    (ID_data_check_update fext s s').EX.EX_PC_sel = s'.EX.EX_PC_sel
Proof
  rw [ID_data_check_update_def]
QED

Theorem ID_data_check_update_unchanged_EX_ALU:
  !fext s s'.
    ((ID_data_check_update fext s s').EX.EX_ALU_res = s'.EX.EX_ALU_res) /\
    ((ID_data_check_update fext s s').EX.EX_carry_flag = s'.EX.EX_carry_flag) /\
    ((ID_data_check_update fext s s').EX.EX_overflow_flag = s'.EX.EX_overflow_flag)
Proof
  rw [ID_data_check_update_def]
QED

Theorem ID_data_check_update_unchanged_MEM_pipeline_items:
  !fext s s'.
    ((ID_data_check_update fext s s').MEM.MEM_PC = s'.MEM.MEM_PC) /\
    ((ID_data_check_update fext s s').MEM.MEM_dataA = s'.MEM.MEM_dataA) /\
    ((ID_data_check_update fext s s').MEM.MEM_dataB = s'.MEM.MEM_dataB) /\
    ((ID_data_check_update fext s s').MEM.MEM_imm = s'.MEM.MEM_imm) /\
    ((ID_data_check_update fext s s').MEM.MEM_ALU_res = s'.MEM.MEM_ALU_res) /\
    ((ID_data_check_update fext s s').MEM.MEM_SHIFT_res = s'.MEM.MEM_SHIFT_res) /\
    ((ID_data_check_update fext s s').MEM.MEM_addrW = s'.MEM.MEM_addrW) /\
    ((ID_data_check_update fext s s').MEM.MEM_opc = s'.MEM.MEM_opc) /\
    ((ID_data_check_update fext s s').MEM.MEM_write_reg <=> s'.MEM.MEM_write_reg)
Proof
  rw [ID_data_check_update_def]
QED

Theorem ID_data_check_update_unchanged_WB_pipeline_items:
  !fext s s'.
    ((ID_data_check_update fext s s').WB.WB_write_reg <=> s'.WB.WB_write_reg) /\
    ((ID_data_check_update fext s s').WB.WB_addrW = s'.WB.WB_addrW)
Proof
  rw [ID_data_check_update_def]
QED

Theorem ID_data_check_update_unchanged_state_items:
  !fext s s'.
    ((ID_data_check_update fext s s').command = s'.command) /\
    ((ID_data_check_update fext s s').state = s'.state) /\
    ((ID_data_check_update fext s s').R = s'.R)
Proof
  rw [ID_data_check_update_def]
QED

(** unchanged items by EX_ctrl_update **)
Theorem EX_ctrl_update_unchanged_enable_flags:
  !fext s s'.
    ((EX_ctrl_update fext s s').ID.ID_EX_write_enable <=> s'.ID.ID_EX_write_enable) /\
    ((EX_ctrl_update fext s s').EX.EX_NOP_flag <=> s'.EX.EX_NOP_flag) /\
    ((EX_ctrl_update fext s s').MEM.MEM_state_flag <=> s'.MEM.MEM_state_flag)
Proof
  rw [EX_ctrl_update_def]
QED

Theorem EX_ctrl_update_unchanged_IF:
  !fext s s'.
    ((EX_ctrl_update fext s s').IF.IF_PC_input = s'.IF.IF_PC_input) /\
    ((EX_ctrl_update fext s s').IF.IF_instr = s'.IF.IF_instr) /\
    ((EX_ctrl_update fext s s').IF.IF_PC_write_enable = s'.IF.IF_PC_write_enable) /\
    ((EX_ctrl_update fext s s').PC = s'.PC)
Proof
  rw [EX_ctrl_update_def]
QED

Theorem EX_ctrl_update_unchanged_ID_pipeline_items:
  !fext s s'.
    ((EX_ctrl_update fext s s').ID.ID_PC = s'.ID.ID_PC) /\
    ((EX_ctrl_update fext s s').ID.ID_instr = s'.ID.ID_instr)
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

Theorem EX_ctrl_update_unchanged_ID_data_items:
  !fext s s'.
    ((EX_ctrl_update fext s s').ID.ID_addrA = s'.ID.ID_addrA) /\
    ((EX_ctrl_update fext s s').ID.ID_addrB = s'.ID.ID_addrB) /\
    ((EX_ctrl_update fext s s').ID.ID_addrW = s'.ID.ID_addrW) /\
    ((EX_ctrl_update fext s s').ID.ID_addrA_disable = s'.ID.ID_addrA_disable) /\
    ((EX_ctrl_update fext s s').ID.ID_addrB_disable = s'.ID.ID_addrB_disable) /\
    ((EX_ctrl_update fext s s').ID.ID_addrW_disable = s'.ID.ID_addrW_disable) /\
    ((EX_ctrl_update fext s s').ID.ID_read_dataA = s'.ID.ID_read_dataA) /\
    ((EX_ctrl_update fext s s').ID.ID_read_dataB = s'.ID.ID_read_dataB) /\
    ((EX_ctrl_update fext s s').ID.ID_read_dataW = s'.ID.ID_read_dataW) /\
    ((EX_ctrl_update fext s s').ID.ID_immA = s'.ID.ID_immA) /\
    ((EX_ctrl_update fext s s').ID.ID_immB = s'.ID.ID_immB) /\
    ((EX_ctrl_update fext s s').ID.ID_immW = s'.ID.ID_immW) /\
    ((EX_ctrl_update fext s s').ID.ID_imm = s'.ID.ID_imm) /\
    ((EX_ctrl_update fext s s').ID.ID_dataA = s'.ID.ID_dataA) /\
    ((EX_ctrl_update fext s s').ID.ID_dataB = s'.ID.ID_dataB) /\
    ((EX_ctrl_update fext s s').ID.ID_dataW = s'.ID.ID_dataW)
Proof
  rw [EX_ctrl_update_def]
QED

Theorem EX_ctrl_update_unchanged_ID_data_check_items:
  !fext s s'.
    ((EX_ctrl_update fext s s').EX.EX_checkA = s'.EX.EX_checkA) /\
    ((EX_ctrl_update fext s s').EX.EX_checkB = s'.EX.EX_checkB) /\
    ((EX_ctrl_update fext s s').EX.EX_checkW = s'.EX.EX_checkW) /\
    ((EX_ctrl_update fext s s').MEM.MEM_checkA = s'.MEM.MEM_checkA) /\
    ((EX_ctrl_update fext s s').MEM.MEM_checkB = s'.MEM.MEM_checkB) /\
    ((EX_ctrl_update fext s s').MEM.MEM_checkW = s'.MEM.MEM_checkW) /\
    ((EX_ctrl_update fext s s').WB.WB_checkA = s'.WB.WB_checkA) /\
    ((EX_ctrl_update fext s s').WB.WB_checkB = s'.WB.WB_checkB) /\
    ((EX_ctrl_update fext s s').WB.WB_checkW = s'.WB.WB_checkW)
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
    ((EX_ctrl_update fext s s').EX.EX_addrW = s'.EX.EX_addrW) /\
    ((EX_ctrl_update fext s s').EX.EX_write_reg = s'.EX.EX_write_reg) /\
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

Theorem EX_ctrl_update_unchanged_MEM_pipeline_items:
  !fext s s'.
    ((EX_ctrl_update fext s s').MEM.MEM_PC = s'.MEM.MEM_PC) /\
    ((EX_ctrl_update fext s s').MEM.MEM_dataA = s'.MEM.MEM_dataA) /\
    ((EX_ctrl_update fext s s').MEM.MEM_dataB = s'.MEM.MEM_dataB) /\
    ((EX_ctrl_update fext s s').MEM.MEM_imm = s'.MEM.MEM_imm) /\
    ((EX_ctrl_update fext s s').MEM.MEM_ALU_res = s'.MEM.MEM_ALU_res) /\
    ((EX_ctrl_update fext s s').MEM.MEM_SHIFT_res = s'.MEM.MEM_SHIFT_res) /\
    ((EX_ctrl_update fext s s').MEM.MEM_addrW = s'.MEM.MEM_addrW) /\
    ((EX_ctrl_update fext s s').MEM.MEM_opc = s'.MEM.MEM_opc) /\
    ((EX_ctrl_update fext s s').MEM.MEM_write_reg <=> s'.MEM.MEM_write_reg)
Proof
  rw [EX_ctrl_update_def]
QED

Theorem EX_ctrl_update_unchanged_WB_pipeline_items:
  !fext s s'.
    ((EX_ctrl_update fext s s').WB.WB_write_reg <=> s'.WB.WB_write_reg) /\
    ((EX_ctrl_update fext s s').WB.WB_addrW = s'.WB.WB_addrW)
Proof
  rw [EX_ctrl_update_def]
QED

Theorem EX_ctrl_update_unchanged_state_items:
  !fext s s'.
    ((EX_ctrl_update fext s s').command = s'.command) /\
    ((EX_ctrl_update fext s s').state = s'.state) /\
    ((EX_ctrl_update fext s s').R = s'.R)
Proof
  rw [EX_ctrl_update_def]
QED

(** unchanged items by EX_ALU_input_imm_update **)
Theorem EX_ALU_input_imm_update_unchanged_enable_flags:
  !fext s s'.
    ((EX_ALU_input_imm_update fext s s').ID.ID_EX_write_enable <=> s'.ID.ID_EX_write_enable) /\
    ((EX_ALU_input_imm_update fext s s').EX.EX_NOP_flag <=> s'.EX.EX_NOP_flag) /\
    ((EX_ALU_input_imm_update fext s s').MEM.MEM_state_flag <=> s'.MEM.MEM_state_flag)
Proof
  rw [EX_ALU_input_imm_update_def]
QED

Theorem EX_ALU_input_imm_update_unchanged_IF:
  !fext s s'.
    ((EX_ALU_input_imm_update fext s s').IF.IF_PC_input = s'.IF.IF_PC_input) /\  
    ((EX_ALU_input_imm_update fext s s').IF.IF_instr = s'.IF.IF_instr) /\
    ((EX_ALU_input_imm_update fext s s').IF.IF_PC_write_enable = s'.IF.IF_PC_write_enable) /\
    ((EX_ALU_input_imm_update fext s s').PC = s'.PC)
Proof
  rw [EX_ALU_input_imm_update_def]
QED

Theorem EX_ALU_input_imm_update_unchanged_ID_pipeline_items:
  !fext s s'.
    ((EX_ALU_input_imm_update fext s s').ID.ID_PC = s'.ID.ID_PC) /\
    ((EX_ALU_input_imm_update fext s s').ID.ID_instr = s'.ID.ID_instr)
Proof
  rw [EX_ALU_input_imm_update_def]
QED

Theorem EX_ALU_input_imm_update_unchanged_ID_opc_func:
  !fext s s'.
    ((EX_ALU_input_imm_update fext s s').ID.ID_opc = s'.ID.ID_opc) /\
    ((EX_ALU_input_imm_update fext s s').ID.ID_func = s'.ID.ID_func)
Proof
  rw [EX_ALU_input_imm_update_def]
QED

Theorem EX_ALU_input_imm_update_unchanged_ID_data_items:
  !fext s s'.
    ((EX_ALU_input_imm_update fext s s').ID.ID_addrA = s'.ID.ID_addrA) /\
    ((EX_ALU_input_imm_update fext s s').ID.ID_addrB = s'.ID.ID_addrB) /\
    ((EX_ALU_input_imm_update fext s s').ID.ID_addrW = s'.ID.ID_addrW) /\
    ((EX_ALU_input_imm_update fext s s').ID.ID_addrA_disable = s'.ID.ID_addrA_disable) /\
    ((EX_ALU_input_imm_update fext s s').ID.ID_addrB_disable = s'.ID.ID_addrB_disable) /\
    ((EX_ALU_input_imm_update fext s s').ID.ID_addrW_disable = s'.ID.ID_addrW_disable) /\
    ((EX_ALU_input_imm_update fext s s').ID.ID_read_dataA = s'.ID.ID_read_dataA) /\
    ((EX_ALU_input_imm_update fext s s').ID.ID_read_dataB = s'.ID.ID_read_dataB) /\
    ((EX_ALU_input_imm_update fext s s').ID.ID_read_dataW = s'.ID.ID_read_dataW) /\
    ((EX_ALU_input_imm_update fext s s').ID.ID_immA = s'.ID.ID_immA) /\
    ((EX_ALU_input_imm_update fext s s').ID.ID_immB = s'.ID.ID_immB) /\
    ((EX_ALU_input_imm_update fext s s').ID.ID_immW = s'.ID.ID_immW) /\
    ((EX_ALU_input_imm_update fext s s').ID.ID_imm = s'.ID.ID_imm) /\
    ((EX_ALU_input_imm_update fext s s').ID.ID_dataA = s'.ID.ID_dataA) /\
    ((EX_ALU_input_imm_update fext s s').ID.ID_dataB = s'.ID.ID_dataB) /\
    ((EX_ALU_input_imm_update fext s s').ID.ID_dataW = s'.ID.ID_dataW)
Proof
  rw [EX_ALU_input_imm_update_def]
QED

Theorem EX_ALU_input_imm_update_unchanged_ID_data_check_items:
  !fext s s'.
    ((EX_ALU_input_imm_update fext s s').EX.EX_checkA = s'.EX.EX_checkA) /\
    ((EX_ALU_input_imm_update fext s s').EX.EX_checkB = s'.EX.EX_checkB) /\
    ((EX_ALU_input_imm_update fext s s').EX.EX_checkW = s'.EX.EX_checkW) /\
    ((EX_ALU_input_imm_update fext s s').MEM.MEM_checkA = s'.MEM.MEM_checkA) /\
    ((EX_ALU_input_imm_update fext s s').MEM.MEM_checkB = s'.MEM.MEM_checkB) /\
    ((EX_ALU_input_imm_update fext s s').MEM.MEM_checkW = s'.MEM.MEM_checkW) /\
    ((EX_ALU_input_imm_update fext s s').WB.WB_checkA = s'.WB.WB_checkA) /\
    ((EX_ALU_input_imm_update fext s s').WB.WB_checkB = s'.WB.WB_checkB) /\
    ((EX_ALU_input_imm_update fext s s').WB.WB_checkW = s'.WB.WB_checkW)
Proof
  rw [EX_ALU_input_imm_update_def]
QED

Theorem EX_ALU_input_imm_update_unchanged_EX_pipeline_items:
  !fext s s'.
    ((EX_ALU_input_imm_update fext s s').EX.EX_PC = s'.EX.EX_PC) /\
    ((EX_ALU_input_imm_update fext s s').EX.EX_dataA = s'.EX.EX_dataA) /\
    ((EX_ALU_input_imm_update fext s s').EX.EX_dataB = s'.EX.EX_dataB) /\
    ((EX_ALU_input_imm_update fext s s').EX.EX_dataW = s'.EX.EX_dataW) /\
    ((EX_ALU_input_imm_update fext s s').EX.EX_imm = s'.EX.EX_imm) /\
    ((EX_ALU_input_imm_update fext s s').EX.EX_addrW = s'.EX.EX_addrW) /\
    ((EX_ALU_input_imm_update fext s s').EX.EX_write_reg = s'.EX.EX_write_reg) /\
    ((EX_ALU_input_imm_update fext s s').EX.EX_opc = s'.EX.EX_opc) /\
    ((EX_ALU_input_imm_update fext s s').EX.EX_func = s'.EX.EX_func)
Proof
  rw [EX_ALU_input_imm_update_def]
QED

Theorem EX_ALU_input_imm_update_unchanged_EX_ALU:
  !fext s s'.
    ((EX_ALU_input_imm_update fext s s').EX.EX_ALU_res = s'.EX.EX_ALU_res) /\
    ((EX_ALU_input_imm_update fext s s').EX.EX_carry_flag = s'.EX.EX_carry_flag) /\
    ((EX_ALU_input_imm_update fext s s').EX.EX_overflow_flag = s'.EX.EX_overflow_flag)
Proof
  rw [EX_ALU_input_imm_update_def]
QED

Theorem EX_ALU_input_imm_update_unchanged_EX_ctrl_items:
  !fext s s'.
    (EX_ALU_input_imm_update fext s s').EX.EX_PC_sel = s'.EX.EX_PC_sel
Proof
  rw [EX_ALU_input_imm_update_def]
QED

Theorem EX_ALU_input_imm_update_unchanged_MEM_pipeline_items:
  !fext s s'.
    ((EX_ALU_input_imm_update fext s s').MEM.MEM_PC = s'.MEM.MEM_PC) /\
    ((EX_ALU_input_imm_update fext s s').MEM.MEM_dataA = s'.MEM.MEM_dataA) /\
    ((EX_ALU_input_imm_update fext s s').MEM.MEM_dataB = s'.MEM.MEM_dataB) /\
    ((EX_ALU_input_imm_update fext s s').MEM.MEM_imm = s'.MEM.MEM_imm) /\
    ((EX_ALU_input_imm_update fext s s').MEM.MEM_ALU_res = s'.MEM.MEM_ALU_res) /\
    ((EX_ALU_input_imm_update fext s s').MEM.MEM_SHIFT_res = s'.MEM.MEM_SHIFT_res) /\
    ((EX_ALU_input_imm_update fext s s').MEM.MEM_addrW = s'.MEM.MEM_addrW) /\
    ((EX_ALU_input_imm_update fext s s').MEM.MEM_opc = s'.MEM.MEM_opc) /\
    ((EX_ALU_input_imm_update fext s s').MEM.MEM_write_reg <=> s'.MEM.MEM_write_reg)
Proof
  rw [EX_ALU_input_imm_update_def]
QED

Theorem EX_ALU_input_imm_update_unchanged_WB_pipeline_items:
  !fext s s'.
    ((EX_ALU_input_imm_update fext s s').WB.WB_write_reg <=> s'.WB.WB_write_reg) /\
    ((EX_ALU_input_imm_update fext s s').WB.WB_addrW = s'.WB.WB_addrW)
Proof
  rw [EX_ALU_input_imm_update_def]
QED

Theorem EX_ALU_input_imm_update_unchanged_state_items:
  !fext s s'.
    ((EX_ALU_input_imm_update fext s s').command = s'.command) /\
    ((EX_ALU_input_imm_update fext s s').state = s'.state) /\
    ((EX_ALU_input_imm_update fext s s').R = s'.R)
Proof
  rw [EX_ALU_input_imm_update_def]
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

Theorem EX_ALU_update_unchanged_ID_pipeline_items:
  !fext s s'.
    ((EX_ALU_update fext s s').ID.ID_PC = s'.ID.ID_PC) /\
    ((EX_ALU_update fext s s').ID.ID_instr = s'.ID.ID_instr)
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

Theorem EX_ALU_update_unchanged_ID_data_items:
  !fext s s'.
    ((EX_ALU_update fext s s').ID.ID_addrA = s'.ID.ID_addrA) /\
    ((EX_ALU_update fext s s').ID.ID_addrB = s'.ID.ID_addrB) /\
    ((EX_ALU_update fext s s').ID.ID_addrW = s'.ID.ID_addrW) /\
    ((EX_ALU_update fext s s').ID.ID_addrA_disable = s'.ID.ID_addrA_disable) /\
    ((EX_ALU_update fext s s').ID.ID_addrB_disable = s'.ID.ID_addrB_disable) /\
    ((EX_ALU_update fext s s').ID.ID_addrW_disable = s'.ID.ID_addrW_disable) /\
    ((EX_ALU_update fext s s').ID.ID_read_dataA = s'.ID.ID_read_dataA) /\
    ((EX_ALU_update fext s s').ID.ID_read_dataB = s'.ID.ID_read_dataB) /\
    ((EX_ALU_update fext s s').ID.ID_read_dataW = s'.ID.ID_read_dataW) /\
    ((EX_ALU_update fext s s').ID.ID_immA = s'.ID.ID_immA) /\
    ((EX_ALU_update fext s s').ID.ID_immB = s'.ID.ID_immB) /\
    ((EX_ALU_update fext s s').ID.ID_immW = s'.ID.ID_immW) /\
    ((EX_ALU_update fext s s').ID.ID_imm = s'.ID.ID_imm) /\
    ((EX_ALU_update fext s s').ID.ID_dataA = s'.ID.ID_dataA) /\
    ((EX_ALU_update fext s s').ID.ID_dataB = s'.ID.ID_dataB) /\
    ((EX_ALU_update fext s s').ID.ID_dataW = s'.ID.ID_dataW)
Proof
  rw [EX_ALU_update_def] >>
  Cases_on_word_value `s'.EX.EX_func` >> fs []
QED

Theorem EX_ALU_update_unchanged_ID_data_check_items:
  !fext s s'.
    ((EX_ALU_update fext s s').EX.EX_checkA = s'.EX.EX_checkA) /\
    ((EX_ALU_update fext s s').EX.EX_checkB = s'.EX.EX_checkB) /\
    ((EX_ALU_update fext s s').EX.EX_checkW = s'.EX.EX_checkW) /\
    ((EX_ALU_update fext s s').MEM.MEM_checkA = s'.MEM.MEM_checkA) /\
    ((EX_ALU_update fext s s').MEM.MEM_checkB = s'.MEM.MEM_checkB) /\
    ((EX_ALU_update fext s s').MEM.MEM_checkW = s'.MEM.MEM_checkW) /\
    ((EX_ALU_update fext s s').WB.WB_checkA = s'.WB.WB_checkA) /\
    ((EX_ALU_update fext s s').WB.WB_checkB = s'.WB.WB_checkB) /\
    ((EX_ALU_update fext s s').WB.WB_checkW = s'.WB.WB_checkW)
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
    ((EX_ALU_update fext s s').EX.EX_addrW = s'.EX.EX_addrW) /\
    ((EX_ALU_update fext s s').EX.EX_write_reg = s'.EX.EX_write_reg) /\
    ((EX_ALU_update fext s s').EX.EX_opc = s'.EX.EX_opc) /\
    ((EX_ALU_update fext s s').EX.EX_func = s'.EX.EX_func)
Proof
  rw [EX_ALU_update_def] >>
  Cases_on_word_value `s'.EX.EX_func` >> fs []
QED

Theorem EX_ALU_update_unchanged_EX_ctrl_items:
  !fext s s'.
    ((EX_ALU_update fext s s').EX.EX_PC_sel = s'.EX.EX_PC_sel) /\
    ((EX_ALU_update fext s s').EX.EX_imm_updated = s'.EX.EX_imm_updated)
Proof
  rw [EX_ALU_update_def] >>
  Cases_on_word_value `s'.EX.EX_func` >> fs []
QED

Theorem EX_ALU_update_unchanged_EX_ALU_input:
  !fext s s'.
    ((EX_ALU_update fext s s').EX.EX_ALU_input1 = s'.EX.EX_ALU_input1) /\
    ((EX_ALU_update fext s s').EX.EX_ALU_input2 = s'.EX.EX_ALU_input2)
Proof
  rw [EX_ALU_update_def] >>
  Cases_on_word_value `s'.EX.EX_func` >> fs []
QED

Theorem EX_ALU_update_unchanged_MEM_pipeline_items:
  !fext s s'.
    ((EX_ALU_update fext s s').MEM.MEM_PC = s'.MEM.MEM_PC) /\
    ((EX_ALU_update fext s s').MEM.MEM_dataA = s'.MEM.MEM_dataA) /\
    ((EX_ALU_update fext s s').MEM.MEM_dataB = s'.MEM.MEM_dataB) /\
    ((EX_ALU_update fext s s').MEM.MEM_imm = s'.MEM.MEM_imm) /\
    ((EX_ALU_update fext s s').MEM.MEM_ALU_res = s'.MEM.MEM_ALU_res) /\
    ((EX_ALU_update fext s s').MEM.MEM_SHIFT_res = s'.MEM.MEM_SHIFT_res) /\
    ((EX_ALU_update fext s s').MEM.MEM_addrW = s'.MEM.MEM_addrW) /\
    ((EX_ALU_update fext s s').MEM.MEM_opc = s'.MEM.MEM_opc) /\
    ((EX_ALU_update fext s s').MEM.MEM_write_reg <=> s'.MEM.MEM_write_reg)
Proof
  rw [EX_ALU_update_def] >>
  Cases_on_word_value `s'.EX.EX_func` >> fs []
QED

Theorem EX_ALU_update_unchanged_WB_pipeline_items:
  !fext s s'.
    ((EX_ALU_update fext s s').WB.WB_write_reg <=> s'.WB.WB_write_reg) /\
    ((EX_ALU_update fext s s').WB.WB_addrW = s'.WB.WB_addrW)
Proof
  rw [EX_ALU_update_def] >>
  Cases_on_word_value `s'.EX.EX_func` >> fs []
QED

Theorem EX_ALU_update_unchanged_state_items:
  !fext s s'.
    ((EX_ALU_update fext s s').command = s'.command) /\
    ((EX_ALU_update fext s s').state = s'.state) /\
    ((EX_ALU_update fext s s').R = s'.R)
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

Theorem EX_SHIFT_update_unchanged_ID_pipeline_items:
  !fext s s'.
    ((EX_SHIFT_update fext s s').ID.ID_PC = s'.ID.ID_PC) /\
    ((EX_SHIFT_update fext s s').ID.ID_instr = s'.ID.ID_instr)
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

Theorem EX_SHIFT_update_unchanged_ID_data_items:
  !fext s s'.
    ((EX_SHIFT_update fext s s').ID.ID_addrA = s'.ID.ID_addrA) /\
    ((EX_SHIFT_update fext s s').ID.ID_addrB = s'.ID.ID_addrB) /\
    ((EX_SHIFT_update fext s s').ID.ID_addrW = s'.ID.ID_addrW) /\
    ((EX_SHIFT_update fext s s').ID.ID_addrA_disable = s'.ID.ID_addrA_disable) /\
    ((EX_SHIFT_update fext s s').ID.ID_addrB_disable = s'.ID.ID_addrB_disable) /\
    ((EX_SHIFT_update fext s s').ID.ID_addrW_disable = s'.ID.ID_addrW_disable) /\
    ((EX_SHIFT_update fext s s').ID.ID_read_dataA = s'.ID.ID_read_dataA) /\
    ((EX_SHIFT_update fext s s').ID.ID_read_dataB = s'.ID.ID_read_dataB) /\
    ((EX_SHIFT_update fext s s').ID.ID_read_dataW = s'.ID.ID_read_dataW) /\
    ((EX_SHIFT_update fext s s').ID.ID_immA = s'.ID.ID_immA) /\
    ((EX_SHIFT_update fext s s').ID.ID_immB = s'.ID.ID_immB) /\
    ((EX_SHIFT_update fext s s').ID.ID_immW = s'.ID.ID_immW) /\
    ((EX_SHIFT_update fext s s').ID.ID_imm = s'.ID.ID_imm) /\
    ((EX_SHIFT_update fext s s').ID.ID_dataA = s'.ID.ID_dataA) /\
    ((EX_SHIFT_update fext s s').ID.ID_dataB = s'.ID.ID_dataB) /\
    ((EX_SHIFT_update fext s s').ID.ID_dataW = s'.ID.ID_dataW)
Proof
  rw [EX_SHIFT_update_def] >>
  Cases_on_word_value `(1 >< 0) s'.EX.EX_func` >> fs []
QED

Theorem EX_SHIFT_update_unchanged_ID_data_check_items:
  !fext s s'.
    ((EX_SHIFT_update fext s s').EX.EX_checkA = s'.EX.EX_checkA) /\
    ((EX_SHIFT_update fext s s').EX.EX_checkB = s'.EX.EX_checkB) /\
    ((EX_SHIFT_update fext s s').EX.EX_checkW = s'.EX.EX_checkW) /\
    ((EX_SHIFT_update fext s s').MEM.MEM_checkA = s'.MEM.MEM_checkA) /\
    ((EX_SHIFT_update fext s s').MEM.MEM_checkB = s'.MEM.MEM_checkB) /\
    ((EX_SHIFT_update fext s s').MEM.MEM_checkW = s'.MEM.MEM_checkW) /\
    ((EX_SHIFT_update fext s s').WB.WB_checkA = s'.WB.WB_checkA) /\
    ((EX_SHIFT_update fext s s').WB.WB_checkB = s'.WB.WB_checkB) /\
    ((EX_SHIFT_update fext s s').WB.WB_checkW = s'.WB.WB_checkW)
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
    ((EX_SHIFT_update fext s s').EX.EX_addrW = s'.EX.EX_addrW) /\
    ((EX_SHIFT_update fext s s').EX.EX_write_reg = s'.EX.EX_write_reg) /\
    ((EX_SHIFT_update fext s s').EX.EX_opc = s'.EX.EX_opc) /\
    ((EX_SHIFT_update fext s s').EX.EX_func = s'.EX.EX_func)
Proof
  rw [EX_SHIFT_update_def] >>
  Cases_on_word_value `(1 >< 0) s'.EX.EX_func` >> fs []
QED

Theorem EX_SHIFT_update_unchanged_EX_ctrl_items:
  !fext s s'.
    ((EX_SHIFT_update fext s s').EX.EX_PC_sel = s'.EX.EX_PC_sel) /\
    ((EX_SHIFT_update fext s s').EX.EX_imm_updated = s'.EX.EX_imm_updated)
Proof
  rw [EX_SHIFT_update_def] >>
  Cases_on_word_value `(1 >< 0) s'.EX.EX_func` >> fs []
QED

Theorem EX_SHIFT_update_unchanged_EX_ALU:
  !fext s s'.
    ((EX_SHIFT_update fext s s').EX.EX_ALU_input1 = s'.EX.EX_ALU_input1) /\
    ((EX_SHIFT_update fext s s').EX.EX_ALU_input2 = s'.EX.EX_ALU_input2) /\
    ((EX_SHIFT_update fext s s').EX.EX_ALU_res = s'.EX.EX_ALU_res) /\
    ((EX_SHIFT_update fext s s').EX.EX_carry_flag = s'.EX.EX_carry_flag) /\
    ((EX_SHIFT_update fext s s').EX.EX_overflow_flag = s'.EX.EX_overflow_flag)
Proof
  rw [EX_SHIFT_update_def] >>
  Cases_on_word_value `(1 >< 0) s'.EX.EX_func` >> fs []
QED

Theorem EX_SHIFT_update_unchanged_MEM_pipeline_items:
  !fext s s'.
    ((EX_SHIFT_update fext s s').MEM.MEM_PC = s'.MEM.MEM_PC) /\
    ((EX_SHIFT_update fext s s').MEM.MEM_dataA = s'.MEM.MEM_dataA) /\
    ((EX_SHIFT_update fext s s').MEM.MEM_dataB = s'.MEM.MEM_dataB) /\
    ((EX_SHIFT_update fext s s').MEM.MEM_imm = s'.MEM.MEM_imm) /\
    ((EX_SHIFT_update fext s s').MEM.MEM_ALU_res = s'.MEM.MEM_ALU_res) /\
    ((EX_SHIFT_update fext s s').MEM.MEM_SHIFT_res = s'.MEM.MEM_SHIFT_res) /\
    ((EX_SHIFT_update fext s s').MEM.MEM_addrW = s'.MEM.MEM_addrW) /\
    ((EX_SHIFT_update fext s s').MEM.MEM_opc = s'.MEM.MEM_opc) /\
    ((EX_SHIFT_update fext s s').MEM.MEM_write_reg <=> s'.MEM.MEM_write_reg)
Proof
  rw [EX_SHIFT_update_def] >>
  Cases_on_word_value `(1 >< 0) s'.EX.EX_func` >> fs []
QED

Theorem EX_SHIFT_update_unchanged_WB_pipeline_items:
  !fext s s'.
    ((EX_SHIFT_update fext s s').WB.WB_write_reg <=> s'.WB.WB_write_reg) /\
    ((EX_SHIFT_update fext s s').WB.WB_addrW = s'.WB.WB_addrW)
Proof
  rw [EX_SHIFT_update_def] >>
  Cases_on_word_value `(1 >< 0) s'.EX.EX_func` >> fs []
QED

Theorem EX_SHIFT_update_unchanged_state_items:
  !fext s s'.
    ((EX_SHIFT_update fext s s').command = s'.command) /\
    ((EX_SHIFT_update fext s s').state = s'.state) /\
    ((EX_SHIFT_update fext s s').R = s'.R)
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

Theorem EX_jump_sel_addr_update_unchanged_ID_pipeline_items:
  !fext s s'.
    ((EX_jump_sel_addr_update fext s s').ID.ID_PC = s'.ID.ID_PC) /\
    ((EX_jump_sel_addr_update fext s s').ID.ID_instr = s'.ID.ID_instr)
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

Theorem EX_jump_sel_addr_update_unchanged_ID_data_items:
  !fext s s'.
    ((EX_jump_sel_addr_update fext s s').ID.ID_addrA = s'.ID.ID_addrA) /\
    ((EX_jump_sel_addr_update fext s s').ID.ID_addrB = s'.ID.ID_addrB) /\
    ((EX_jump_sel_addr_update fext s s').ID.ID_addrW = s'.ID.ID_addrW) /\
    ((EX_jump_sel_addr_update fext s s').ID.ID_addrA_disable = s'.ID.ID_addrA_disable) /\
    ((EX_jump_sel_addr_update fext s s').ID.ID_addrB_disable = s'.ID.ID_addrB_disable) /\
    ((EX_jump_sel_addr_update fext s s').ID.ID_addrW_disable = s'.ID.ID_addrW_disable) /\
    ((EX_jump_sel_addr_update fext s s').ID.ID_read_dataA = s'.ID.ID_read_dataA) /\
    ((EX_jump_sel_addr_update fext s s').ID.ID_read_dataB = s'.ID.ID_read_dataB) /\
    ((EX_jump_sel_addr_update fext s s').ID.ID_read_dataW = s'.ID.ID_read_dataW) /\
    ((EX_jump_sel_addr_update fext s s').ID.ID_immA = s'.ID.ID_immA) /\
    ((EX_jump_sel_addr_update fext s s').ID.ID_immB = s'.ID.ID_immB) /\
    ((EX_jump_sel_addr_update fext s s').ID.ID_immW = s'.ID.ID_immW) /\
    ((EX_jump_sel_addr_update fext s s').ID.ID_imm = s'.ID.ID_imm) /\
    ((EX_jump_sel_addr_update fext s s').ID.ID_dataA = s'.ID.ID_dataA) /\
    ((EX_jump_sel_addr_update fext s s').ID.ID_dataB = s'.ID.ID_dataB) /\
    ((EX_jump_sel_addr_update fext s s').ID.ID_dataW = s'.ID.ID_dataW)
Proof
  rw [EX_jump_sel_addr_update_def]
QED

Theorem EX_jump_sel_addr_update_unchanged_ID_data_check_items:
  !fext s s'.
    ((EX_jump_sel_addr_update fext s s').EX.EX_checkA = s'.EX.EX_checkA) /\
    ((EX_jump_sel_addr_update fext s s').EX.EX_checkB = s'.EX.EX_checkB) /\
    ((EX_jump_sel_addr_update fext s s').EX.EX_checkW = s'.EX.EX_checkW) /\
    ((EX_jump_sel_addr_update fext s s').MEM.MEM_checkA = s'.MEM.MEM_checkA) /\
    ((EX_jump_sel_addr_update fext s s').MEM.MEM_checkB = s'.MEM.MEM_checkB) /\
    ((EX_jump_sel_addr_update fext s s').MEM.MEM_checkW = s'.MEM.MEM_checkW) /\
    ((EX_jump_sel_addr_update fext s s').WB.WB_checkA = s'.WB.WB_checkA) /\
    ((EX_jump_sel_addr_update fext s s').WB.WB_checkB = s'.WB.WB_checkB) /\
    ((EX_jump_sel_addr_update fext s s').WB.WB_checkW = s'.WB.WB_checkW)
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
    ((EX_jump_sel_addr_update fext s s').EX.EX_addrW = s'.EX.EX_addrW) /\
    ((EX_jump_sel_addr_update fext s s').EX.EX_write_reg = s'.EX.EX_write_reg) /\
    ((EX_jump_sel_addr_update fext s s').EX.EX_opc = s'.EX.EX_opc) /\
    ((EX_jump_sel_addr_update fext s s').EX.EX_func = s'.EX.EX_func)
Proof
  rw [EX_jump_sel_addr_update_def]
QED
     
Theorem EX_jump_sel_addr_update_unchanged_EX_ctrl_items:
  !fext s s'.
    ((EX_jump_sel_addr_update fext s s').EX.EX_PC_sel = s'.EX.EX_PC_sel) /\
    ((EX_jump_sel_addr_update fext s s').EX.EX_imm_updated = s'.EX.EX_imm_updated)
Proof
  rw [EX_jump_sel_addr_update_def]
QED

Theorem EX_jump_sel_addr_update_unchanged_EX_ALU:
  !fext s s'.
    ((EX_jump_sel_addr_update fext s s').EX.EX_ALU_input1 = s'.EX.EX_ALU_input1) /\
    ((EX_jump_sel_addr_update fext s s').EX.EX_ALU_input2 = s'.EX.EX_ALU_input2) /\
    ((EX_jump_sel_addr_update fext s s').EX.EX_ALU_res = s'.EX.EX_ALU_res) /\
    ((EX_jump_sel_addr_update fext s s').EX.EX_carry_flag = s'.EX.EX_carry_flag) /\
    ((EX_jump_sel_addr_update fext s s').EX.EX_overflow_flag = s'.EX.EX_overflow_flag)
Proof
  rw [EX_jump_sel_addr_update_def]
QED

Theorem EX_jump_sel_addr_update_unchanged_MEM_pipeline_items:
  !fext s s'.
    ((EX_jump_sel_addr_update fext s s').MEM.MEM_PC = s'.MEM.MEM_PC) /\
    ((EX_jump_sel_addr_update fext s s').MEM.MEM_dataA = s'.MEM.MEM_dataA) /\
    ((EX_jump_sel_addr_update fext s s').MEM.MEM_dataB = s'.MEM.MEM_dataB) /\
    ((EX_jump_sel_addr_update fext s s').MEM.MEM_imm = s'.MEM.MEM_imm) /\
    ((EX_jump_sel_addr_update fext s s').MEM.MEM_ALU_res = s'.MEM.MEM_ALU_res) /\
    ((EX_jump_sel_addr_update fext s s').MEM.MEM_SHIFT_res = s'.MEM.MEM_SHIFT_res) /\
    ((EX_jump_sel_addr_update fext s s').MEM.MEM_addrW = s'.MEM.MEM_addrW) /\
    ((EX_jump_sel_addr_update fext s s').MEM.MEM_opc = s'.MEM.MEM_opc) /\
    ((EX_jump_sel_addr_update fext s s').MEM.MEM_write_reg <=> s'.MEM.MEM_write_reg)
Proof
  rw [EX_jump_sel_addr_update_def]
QED

Theorem EX_jump_sel_addr_update_unchanged_WB_pipeline_items:
  !fext s s'.
    ((EX_jump_sel_addr_update fext s s').WB.WB_write_reg <=> s'.WB.WB_write_reg) /\
    ((EX_jump_sel_addr_update fext s s').WB.WB_addrW = s'.WB.WB_addrW)
Proof
  rw [EX_jump_sel_addr_update_def]
QED

Theorem EX_jump_sel_addr_update_unchanged_state_items:
  !fext s s'.
    ((EX_jump_sel_addr_update fext s s').command = s'.command) /\
    ((EX_jump_sel_addr_update fext s s').state = s'.state) /\
    ((EX_jump_sel_addr_update fext s s').R = s'.R)
Proof
  rw [EX_jump_sel_addr_update_def]
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

Theorem MEM_ctrl_update_unchanged_ID_pipeline_items:
  !fext s s'.
    ((MEM_ctrl_update fext s s').ID.ID_PC = s'.ID.ID_PC) /\
    ((MEM_ctrl_update fext s s').ID.ID_instr = s'.ID.ID_instr)
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

Theorem MEM_ctrl_update_unchanged_ID_data_items:
  !fext s s'.
    ((MEM_ctrl_update fext s s').ID.ID_addrA = s'.ID.ID_addrA) /\
    ((MEM_ctrl_update fext s s').ID.ID_addrB = s'.ID.ID_addrB) /\
    ((MEM_ctrl_update fext s s').ID.ID_addrW = s'.ID.ID_addrW) /\
    ((MEM_ctrl_update fext s s').ID.ID_addrA_disable = s'.ID.ID_addrA_disable) /\
    ((MEM_ctrl_update fext s s').ID.ID_addrB_disable = s'.ID.ID_addrB_disable) /\
    ((MEM_ctrl_update fext s s').ID.ID_addrW_disable = s'.ID.ID_addrW_disable) /\
    ((MEM_ctrl_update fext s s').ID.ID_read_dataA = s'.ID.ID_read_dataA) /\
    ((MEM_ctrl_update fext s s').ID.ID_read_dataB = s'.ID.ID_read_dataB) /\
    ((MEM_ctrl_update fext s s').ID.ID_read_dataW = s'.ID.ID_read_dataW) /\
    ((MEM_ctrl_update fext s s').ID.ID_immA = s'.ID.ID_immA) /\
    ((MEM_ctrl_update fext s s').ID.ID_immB = s'.ID.ID_immB) /\
    ((MEM_ctrl_update fext s s').ID.ID_immW = s'.ID.ID_immW) /\
    ((MEM_ctrl_update fext s s').ID.ID_imm = s'.ID.ID_imm) /\
    ((MEM_ctrl_update fext s s').ID.ID_dataA = s'.ID.ID_dataA) /\
    ((MEM_ctrl_update fext s s').ID.ID_dataB = s'.ID.ID_dataB) /\
    ((MEM_ctrl_update fext s s').ID.ID_dataW = s'.ID.ID_dataW)
Proof
  rw [MEM_ctrl_update_def]
QED

Theorem MEM_ctrl_update_unchanged_ID_data_check_items:
  !fext s s'.
    ((MEM_ctrl_update fext s s').EX.EX_checkA = s'.EX.EX_checkA) /\
    ((MEM_ctrl_update fext s s').EX.EX_checkB = s'.EX.EX_checkB) /\
    ((MEM_ctrl_update fext s s').EX.EX_checkW = s'.EX.EX_checkW) /\
    ((MEM_ctrl_update fext s s').MEM.MEM_checkA = s'.MEM.MEM_checkA) /\
    ((MEM_ctrl_update fext s s').MEM.MEM_checkB = s'.MEM.MEM_checkB) /\
    ((MEM_ctrl_update fext s s').MEM.MEM_checkW = s'.MEM.MEM_checkW) /\
    ((MEM_ctrl_update fext s s').WB.WB_checkA = s'.WB.WB_checkA) /\
    ((MEM_ctrl_update fext s s').WB.WB_checkB = s'.WB.WB_checkB) /\
    ((MEM_ctrl_update fext s s').WB.WB_checkW = s'.WB.WB_checkW)
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
    ((MEM_ctrl_update fext s s').EX.EX_addrW = s'.EX.EX_addrW) /\
    ((MEM_ctrl_update fext s s').EX.EX_write_reg = s'.EX.EX_write_reg) /\
    ((MEM_ctrl_update fext s s').EX.EX_opc = s'.EX.EX_opc) /\
    ((MEM_ctrl_update fext s s').EX.EX_func = s'.EX.EX_func)
Proof
  rw [MEM_ctrl_update_def]
QED

Theorem MEM_ctrl_update_unchanged_EX_ctrl_items:
  !fext s s'.
    ((MEM_ctrl_update fext s s').EX.EX_PC_sel = s'.EX.EX_PC_sel) /\
    ((MEM_ctrl_update fext s s').EX.EX_imm_updated = s'.EX.EX_imm_updated)
Proof
  rw [MEM_ctrl_update_def]
QED

Theorem MEM_ctrl_update_unchanged_EX_ALU:
  !fext s s'.
    ((MEM_ctrl_update fext s s').EX.EX_ALU_input1 = s'.EX.EX_ALU_input1) /\
    ((MEM_ctrl_update fext s s').EX.EX_ALU_input2 = s'.EX.EX_ALU_input2) /\
    ((MEM_ctrl_update fext s s').EX.EX_ALU_res = s'.EX.EX_ALU_res) /\
    ((MEM_ctrl_update fext s s').EX.EX_carry_flag = s'.EX.EX_carry_flag) /\
    ((MEM_ctrl_update fext s s').EX.EX_overflow_flag = s'.EX.EX_overflow_flag)
Proof
  rw [MEM_ctrl_update_def]
QED

Theorem MEM_ctrl_update_unchanged_EX_jump:
  !fext s s'.
    ((MEM_ctrl_update fext s s').EX.EX_jump_sel <=> s'.EX.EX_jump_sel) /\
    ((MEM_ctrl_update fext s s').EX.EX_jump_addr = s'.EX.EX_jump_addr)
Proof
  rw [MEM_ctrl_update_def]
QED

Theorem MEM_ctrl_update_unchanged_MEM_pipeline_items:
  !fext s s'.
    ((MEM_ctrl_update fext s s').MEM.MEM_PC = s'.MEM.MEM_PC) /\
    ((MEM_ctrl_update fext s s').MEM.MEM_dataA = s'.MEM.MEM_dataA) /\
    ((MEM_ctrl_update fext s s').MEM.MEM_dataB = s'.MEM.MEM_dataB) /\
    ((MEM_ctrl_update fext s s').MEM.MEM_imm = s'.MEM.MEM_imm) /\
    ((MEM_ctrl_update fext s s').MEM.MEM_ALU_res = s'.MEM.MEM_ALU_res) /\
    ((MEM_ctrl_update fext s s').MEM.MEM_SHIFT_res = s'.MEM.MEM_SHIFT_res) /\
    ((MEM_ctrl_update fext s s').MEM.MEM_addrW = s'.MEM.MEM_addrW) /\
    ((MEM_ctrl_update fext s s').MEM.MEM_opc = s'.MEM.MEM_opc) /\
    ((MEM_ctrl_update fext s s').MEM.MEM_write_reg <=> s'.MEM.MEM_write_reg)
Proof
  rw [MEM_ctrl_update_def]
QED

Theorem MEM_ctrl_update_unchanged_WB_pipeline_items:
  !fext s s'.
    ((MEM_ctrl_update fext s s').WB.WB_write_reg <=> s'.WB.WB_write_reg) /\
    ((MEM_ctrl_update fext s s').WB.WB_addrW = s'.WB.WB_addrW)
Proof
  rw [MEM_ctrl_update_def]
QED

Theorem MEM_ctrl_update_unchanged_state_items:
  !fext s s'.
    ((MEM_ctrl_update fext s s').command = s'.command) /\
    ((MEM_ctrl_update fext s s').state = s'.state) /\
    ((MEM_ctrl_update fext s s').R = s'.R)
Proof
  rw [MEM_ctrl_update_def]
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

Theorem WB_update_unchanged_ID_pipeline_items:
  !fext s s'.
    ((WB_update fext s s').ID.ID_PC = s'.ID.ID_PC) /\
    ((WB_update fext s s').ID.ID_instr = s'.ID.ID_instr)
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

Theorem WB_update_unchanged_ID_data_items:
  !fext s s'.
    ((WB_update fext s s').ID.ID_addrA = s'.ID.ID_addrA) /\
    ((WB_update fext s s').ID.ID_addrB = s'.ID.ID_addrB) /\
    ((WB_update fext s s').ID.ID_addrW = s'.ID.ID_addrW) /\
    ((WB_update fext s s').ID.ID_addrA_disable = s'.ID.ID_addrA_disable) /\
    ((WB_update fext s s').ID.ID_addrB_disable = s'.ID.ID_addrB_disable) /\
    ((WB_update fext s s').ID.ID_addrW_disable = s'.ID.ID_addrW_disable) /\
    ((WB_update fext s s').ID.ID_read_dataA = s'.ID.ID_read_dataA) /\
    ((WB_update fext s s').ID.ID_read_dataB = s'.ID.ID_read_dataB) /\
    ((WB_update fext s s').ID.ID_read_dataW = s'.ID.ID_read_dataW) /\
    ((WB_update fext s s').ID.ID_immA = s'.ID.ID_immA) /\
    ((WB_update fext s s').ID.ID_immB = s'.ID.ID_immB) /\
    ((WB_update fext s s').ID.ID_immW = s'.ID.ID_immW) /\
    ((WB_update fext s s').ID.ID_imm = s'.ID.ID_imm) /\
    ((WB_update fext s s').ID.ID_dataA = s'.ID.ID_dataA) /\
    ((WB_update fext s s').ID.ID_dataB = s'.ID.ID_dataB) /\
    ((WB_update fext s s').ID.ID_dataW = s'.ID.ID_dataW)
Proof
  rw [WB_update_def]
QED

Theorem WB_update_unchanged_ID_data_check_items:
  !fext s s'.
    ((WB_update fext s s').EX.EX_checkA = s'.EX.EX_checkA) /\
    ((WB_update fext s s').EX.EX_checkB = s'.EX.EX_checkB) /\
    ((WB_update fext s s').EX.EX_checkW = s'.EX.EX_checkW) /\
    ((WB_update fext s s').MEM.MEM_checkA = s'.MEM.MEM_checkA) /\
    ((WB_update fext s s').MEM.MEM_checkB = s'.MEM.MEM_checkB) /\
    ((WB_update fext s s').MEM.MEM_checkW = s'.MEM.MEM_checkW) /\
    ((WB_update fext s s').WB.WB_checkA = s'.WB.WB_checkA) /\
    ((WB_update fext s s').WB.WB_checkB = s'.WB.WB_checkB) /\
    ((WB_update fext s s').WB.WB_checkW = s'.WB.WB_checkW)
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
    ((WB_update fext s s').EX.EX_addrW = s'.EX.EX_addrW) /\
    ((WB_update fext s s').EX.EX_write_reg = s'.EX.EX_write_reg) /\
    ((WB_update fext s s').EX.EX_opc = s'.EX.EX_opc) /\
    ((WB_update fext s s').EX.EX_func = s'.EX.EX_func)
Proof
  rw [WB_update_def]
QED

Theorem WB_update_unchanged_EX_ctrl_items:
  !fext s s'.
    ((WB_update fext s s').EX.EX_PC_sel = s'.EX.EX_PC_sel) /\
    ((WB_update fext s s').EX.EX_imm_updated = s'.EX.EX_imm_updated)
Proof
  rw [WB_update_def]
QED

Theorem WB_update_unchanged_EX_ALU:
  !fext s s'.
    ((WB_update fext s s').EX.EX_ALU_input1 = s'.EX.EX_ALU_input1) /\
    ((WB_update fext s s').EX.EX_ALU_input2 = s'.EX.EX_ALU_input2) /\
    ((WB_update fext s s').EX.EX_ALU_res = s'.EX.EX_ALU_res) /\
    ((WB_update fext s s').EX.EX_carry_flag = s'.EX.EX_carry_flag) /\
    ((WB_update fext s s').EX.EX_overflow_flag = s'.EX.EX_overflow_flag)
Proof
  rw [WB_update_def]
QED

Theorem WB_update_unchanged_EX_jump:
  !fext s s'.
    ((WB_update fext s s').EX.EX_jump_sel <=> s'.EX.EX_jump_sel) /\
    ((WB_update fext s s').EX.EX_jump_addr = s'.EX.EX_jump_addr)
Proof
  rw [WB_update_def]
QED

Theorem WB_update_unchanged_MEM_pipeline_items:
  !fext s s'.
    ((WB_update fext s s').MEM.MEM_PC = s'.MEM.MEM_PC) /\
    ((WB_update fext s s').MEM.MEM_dataA = s'.MEM.MEM_dataA) /\
    ((WB_update fext s s').MEM.MEM_dataB = s'.MEM.MEM_dataB) /\
    ((WB_update fext s s').MEM.MEM_imm = s'.MEM.MEM_imm) /\
    ((WB_update fext s s').MEM.MEM_ALU_res = s'.MEM.MEM_ALU_res) /\
    ((WB_update fext s s').MEM.MEM_SHIFT_res = s'.MEM.MEM_SHIFT_res) /\
    ((WB_update fext s s').MEM.MEM_addrW = s'.MEM.MEM_addrW) /\
    ((WB_update fext s s').MEM.MEM_opc = s'.MEM.MEM_opc) /\
    ((WB_update fext s s').MEM.MEM_write_reg <=> s'.MEM.MEM_write_reg)
Proof
  rw [WB_update_def]
QED

Theorem WB_update_unchanged_WB_pipeline_items:
  !fext s s'.
    ((WB_update fext s s').WB.WB_write_reg <=> s'.WB.WB_write_reg) /\
    ((WB_update fext s s').WB.WB_addrW = s'.WB.WB_addrW)
Proof
  rw [WB_update_def]
QED

Theorem WB_update_unchanged_WB_ctrl_items:
  !fext s s'.
    ((WB_update fext s s').WB.WB_state_flag = s'.WB.WB_state_flag)
Proof
  rw [WB_update_def]
QED

Theorem WB_update_unchanged_state_items:
  !fext s s'.
    ((WB_update fext s s').command = s'.command) /\
    ((WB_update fext s s').state = s'.state) /\
    ((WB_update fext s s').R = s'.R)
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

Theorem Hazard_ctrl_unchanged_ID_pipeline_items:
  !fext s s'.
    ((Hazard_ctrl fext s s').ID.ID_PC = s'.ID.ID_PC) /\
    ((Hazard_ctrl fext s s').ID.ID_instr = s'.ID.ID_instr)
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

Theorem Hazard_ctrl_unchanged_ID_data_items:
  !fext s s'.
    ((Hazard_ctrl fext s s').ID.ID_addrA = s'.ID.ID_addrA) /\
    ((Hazard_ctrl fext s s').ID.ID_addrB = s'.ID.ID_addrB) /\
    ((Hazard_ctrl fext s s').ID.ID_addrW = s'.ID.ID_addrW) /\
    ((Hazard_ctrl fext s s').ID.ID_addrA_disable = s'.ID.ID_addrA_disable) /\
    ((Hazard_ctrl fext s s').ID.ID_addrB_disable = s'.ID.ID_addrB_disable) /\
    ((Hazard_ctrl fext s s').ID.ID_addrW_disable = s'.ID.ID_addrW_disable) /\
    ((Hazard_ctrl fext s s').ID.ID_read_dataA = s'.ID.ID_read_dataA) /\
    ((Hazard_ctrl fext s s').ID.ID_read_dataB = s'.ID.ID_read_dataB) /\
    ((Hazard_ctrl fext s s').ID.ID_read_dataW = s'.ID.ID_read_dataW) /\
    ((Hazard_ctrl fext s s').ID.ID_immA = s'.ID.ID_immA) /\
    ((Hazard_ctrl fext s s').ID.ID_immB = s'.ID.ID_immB) /\
    ((Hazard_ctrl fext s s').ID.ID_immW = s'.ID.ID_immW) /\
    ((Hazard_ctrl fext s s').ID.ID_imm = s'.ID.ID_imm) /\
    ((Hazard_ctrl fext s s').ID.ID_dataA = s'.ID.ID_dataA) /\
    ((Hazard_ctrl fext s s').ID.ID_dataB = s'.ID.ID_dataB) /\
    ((Hazard_ctrl fext s s').ID.ID_dataW = s'.ID.ID_dataW)
Proof
  rw [Hazard_ctrl_def]
QED

Theorem Hazard_ctrl_unchanged_ID_data_check_items:
  !fext s s'.
    ((Hazard_ctrl fext s s').EX.EX_checkA = s'.EX.EX_checkA) /\
    ((Hazard_ctrl fext s s').EX.EX_checkB = s'.EX.EX_checkB) /\
    ((Hazard_ctrl fext s s').EX.EX_checkW = s'.EX.EX_checkW) /\
    ((Hazard_ctrl fext s s').MEM.MEM_checkA = s'.MEM.MEM_checkA) /\
    ((Hazard_ctrl fext s s').MEM.MEM_checkB = s'.MEM.MEM_checkB) /\
    ((Hazard_ctrl fext s s').MEM.MEM_checkW = s'.MEM.MEM_checkW) /\
    ((Hazard_ctrl fext s s').WB.WB_checkA = s'.WB.WB_checkA) /\
    ((Hazard_ctrl fext s s').WB.WB_checkB = s'.WB.WB_checkB) /\
    ((Hazard_ctrl fext s s').WB.WB_checkW = s'.WB.WB_checkW)
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
    ((Hazard_ctrl fext s s').EX.EX_addrW = s'.EX.EX_addrW) /\
    ((Hazard_ctrl fext s s').EX.EX_write_reg = s'.EX.EX_write_reg) /\
    ((Hazard_ctrl fext s s').EX.EX_opc = s'.EX.EX_opc) /\
    ((Hazard_ctrl fext s s').EX.EX_func = s'.EX.EX_func)
Proof
  rw [Hazard_ctrl_def]
QED

Theorem Hazard_ctrl_unchanged_EX_ctrl_items:
  !fext s s'.
    ((Hazard_ctrl fext s s').EX.EX_PC_sel = s'.EX.EX_PC_sel) /\
    ((Hazard_ctrl fext s s').EX.EX_imm_updated = s'.EX.EX_imm_updated)
Proof
  rw [Hazard_ctrl_def]
QED

Theorem Hazard_ctrl_unchanged_EX_ALU:
  !fext s s'.
    ((Hazard_ctrl fext s s').EX.EX_ALU_input1 = s'.EX.EX_ALU_input1) /\
    ((Hazard_ctrl fext s s').EX.EX_ALU_input2 = s'.EX.EX_ALU_input2) /\
    ((Hazard_ctrl fext s s').EX.EX_ALU_res = s'.EX.EX_ALU_res) /\
    ((Hazard_ctrl fext s s').EX.EX_carry_flag = s'.EX.EX_carry_flag) /\
    ((Hazard_ctrl fext s s').EX.EX_overflow_flag = s'.EX.EX_overflow_flag)
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

Theorem Hazard_ctrl_unchanged_MEM_pipeline_items:
  !fext s s'.
    ((Hazard_ctrl fext s s').MEM.MEM_PC = s'.MEM.MEM_PC) /\
    ((Hazard_ctrl fext s s').MEM.MEM_dataA = s'.MEM.MEM_dataA) /\
    ((Hazard_ctrl fext s s').MEM.MEM_dataB = s'.MEM.MEM_dataB) /\
    ((Hazard_ctrl fext s s').MEM.MEM_imm = s'.MEM.MEM_imm) /\
    ((Hazard_ctrl fext s s').MEM.MEM_ALU_res = s'.MEM.MEM_ALU_res) /\
    ((Hazard_ctrl fext s s').MEM.MEM_SHIFT_res = s'.MEM.MEM_SHIFT_res) /\
    ((Hazard_ctrl fext s s').MEM.MEM_addrW = s'.MEM.MEM_addrW) /\
    ((Hazard_ctrl fext s s').MEM.MEM_opc = s'.MEM.MEM_opc) /\
    ((Hazard_ctrl fext s s').MEM.MEM_write_reg <=> s'.MEM.MEM_write_reg)
Proof
  rw [Hazard_ctrl_def]
QED

Theorem Hazard_ctrl_unchanged_WB_pipeline_items:
  !fext s s'.
    ((Hazard_ctrl fext s s').WB.WB_write_reg <=> s'.WB.WB_write_reg) /\
    ((Hazard_ctrl fext s s').WB.WB_addrW = s'.WB.WB_addrW)
Proof
  rw [Hazard_ctrl_def]
QED

Theorem Hazard_ctrl_unchanged_state_items:
  !fext s s'.
    ((Hazard_ctrl fext s s').command = s'.command) /\
    ((Hazard_ctrl fext s s').state = s'.state) /\
    ((Hazard_ctrl fext s s').R = s'.R)
Proof
  rw [Hazard_ctrl_def]
QED

(** unchanged items by Acc_compute **)
Theorem Acc_compute_unchanged_enable_flags:
  !fext s s'.
    ((Acc_compute fext s s').ID.ID_EX_write_enable <=> s'.ID.ID_EX_write_enable) /\
    ((Acc_compute fext s s').EX.EX_NOP_flag <=> s'.EX.EX_NOP_flag) /\
    ((Acc_compute fext s s').MEM.MEM_state_flag <=> s'.MEM.MEM_state_flag)
Proof
  rw [Acc_compute_def]
QED

Theorem Acc_compute_unchanged_IF:
  !fext s s'.
    (Acc_compute fext s s').PC = s'.PC
Proof
  rw [Acc_compute_def]
QED

Theorem Acc_compute_unchanged_ID_items:
  !fext s s'.
    ((Acc_compute fext s s').ID.ID_PC = s'.ID.ID_PC) /\
    ((Acc_compute fext s s').ID.ID_instr = s'.ID.ID_instr)
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
    ((Acc_compute fext s s').EX.EX_write_reg = s'.EX.EX_write_reg) /\
    ((Acc_compute fext s s').EX.EX_addrW = s'.EX.EX_addrW) /\
    ((Acc_compute fext s s').EX.EX_opc = s'.EX.EX_opc) /\
    ((Acc_compute fext s s').EX.EX_func = s'.EX.EX_func)
Proof
  rw [Acc_compute_def]
QED

Theorem Acc_compute_unchanged_EX_ctrl_items:
  !fext s s'.
    (Acc_compute fext s s').EX.EX_PC_sel = s'.EX.EX_PC_sel
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

Theorem Acc_compute_unchanged_EX_jump:
  !fext s s'.
    ((Acc_compute fext s s').EX.EX_jump_sel <=> s'.EX.EX_jump_sel) /\
    ((Acc_compute fext s s').EX.EX_jump_addr = s'.EX.EX_jump_addr)
Proof
  rw [Acc_compute_def]
QED

Theorem Acc_compute_unchanged_WB_ctrl_items:
  !fext s s'.
    ((Acc_compute fext s s').WB.WB_state_flag <=> s'.WB.WB_state_flag)
Proof
  rw [Acc_compute_def]
QED

Theorem Acc_compute_unchanged_state_items:
  !fext s s'.
    ((Acc_compute fext s s').command = s'.command) /\
    ((Acc_compute fext s s').state = s'.state) /\
    ((Acc_compute fext s s').R = s'.R)
Proof
  rw [Acc_compute_def]
QED

(** unchanged items by IF_PC_update **)
Theorem IF_PC_update_unchanged_enable_flags:
  !fext s s'.
    ((IF_PC_update fext s s').ID.ID_EX_write_enable <=> s'.ID.ID_EX_write_enable) /\
    ((IF_PC_update fext s s').EX.EX_NOP_flag <=> s'.EX.EX_NOP_flag) /\
    ((IF_PC_update fext s s').MEM.MEM_state_flag <=> s'.MEM.MEM_state_flag)
Proof
  rw [IF_PC_update_def]
QED

Theorem IF_PC_update_unchanged_ID_pipeline_items:
  !fext s s'.
    ((IF_PC_update fext s s').ID.ID_PC = s'.ID.ID_PC) /\
    ((IF_PC_update fext s s').ID.ID_instr = s'.ID.ID_instr)
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
    ((IF_PC_update fext s s').EX.EX_write_reg = s'.EX.EX_write_reg) /\
    ((IF_PC_update fext s s').EX.EX_addrW = s'.EX.EX_addrW) /\
    ((IF_PC_update fext s s').EX.EX_opc = s'.EX.EX_opc) /\
    ((IF_PC_update fext s s').EX.EX_func = s'.EX.EX_func)
Proof
  rw [IF_PC_update_def]
QED

Theorem IF_PC_update_unchanged_EX_ctrl_items:
  !fext s s'.
    (IF_PC_update fext s s').EX.EX_PC_sel = s'.EX.EX_PC_sel
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

Theorem IF_PC_update_unchanged_EX_jump:
  !fext s s'.
    ((IF_PC_update fext s s').EX.EX_jump_sel <=> s'.EX.EX_jump_sel) /\
    ((IF_PC_update fext s s').EX.EX_jump_addr = s'.EX.EX_jump_addr)
Proof
  rw [IF_PC_update_def]
QED

Theorem IF_PC_update_unchanged_WB_ctrl_items:
  !fext s s'.
    ((IF_PC_update fext s s').WB.WB_state_flag <=> s'.WB.WB_state_flag)
Proof
  rw [IF_PC_update_def]
QED

Theorem IF_PC_update_unchanged_state_items:
  !fext s s'.
    ((IF_PC_update fext s s').command = s'.command) /\
    ((IF_PC_update fext s s').state = s'.state) /\
    ((IF_PC_update fext s s').R = s'.R)
Proof
  rw [IF_PC_update_def]
QED

(** unchanged items by ID_pipeline **)
Theorem ID_pipeline_unchanged_enable_flags:
  !fext s s'.
    ((ID_pipeline fext s s').ID.ID_EX_write_enable <=> s'.ID.ID_EX_write_enable) /\
    ((ID_pipeline fext s s').EX.EX_NOP_flag <=> s'.EX.EX_NOP_flag) /\
    ((ID_pipeline fext s s').MEM.MEM_state_flag <=> s'.MEM.MEM_state_flag)
Proof
  rw [ID_pipeline_def]
QED

Theorem ID_pipeline_unchanged_IF_items:
  !fext s s'.
    ((ID_pipeline fext s s').IF.IF_PC_write_enable <=> s'.IF.IF_PC_write_enable) /\
    ((ID_pipeline fext s s').IF.IF_PC_input = s'.IF.IF_PC_input) /\
    ((ID_pipeline fext s s').PC = s'.PC)
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
    ((ID_pipeline fext s s').EX.EX_write_reg = s'.EX.EX_write_reg) /\
    ((ID_pipeline fext s s').EX.EX_addrW = s'.EX.EX_addrW) /\
    ((ID_pipeline fext s s').EX.EX_opc = s'.EX.EX_opc) /\
    ((ID_pipeline fext s s').EX.EX_func = s'.EX.EX_func)
Proof
  rw [ID_pipeline_def]
QED

Theorem ID_pipeline_unchanged_EX_ctrl_items:
  !fext s s'.
    (ID_pipeline fext s s').EX.EX_PC_sel = s'.EX.EX_PC_sel
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

Theorem ID_pipeline_unchanged_EX_jump:
  !fext s s'.
    ((ID_pipeline fext s s').EX.EX_jump_sel <=> s'.EX.EX_jump_sel) /\
    ((ID_pipeline fext s s').EX.EX_jump_addr = s'.EX.EX_jump_addr)
Proof
  rw [ID_pipeline_def]
QED

Theorem ID_pipeline_unchanged_WB_ctrl_items:
  !fext s s'.
    ((ID_pipeline fext s s').WB.WB_state_flag <=> s'.WB.WB_state_flag)
Proof
  rw [ID_pipeline_def]
QED

Theorem ID_pipeline_unchanged_state_items:
  !fext s s'.
    ((ID_pipeline fext s s').command = s'.command) /\
    ((ID_pipeline fext s s').state = s'.state) /\
    ((ID_pipeline fext s s').R = s'.R)
Proof
  rw [ID_pipeline_def]
QED

(** unchanged items by REG_write **)
Theorem REG_write_unchanged_enable_flags:
  !fext s s'.
    ((REG_write fext s s').ID.ID_EX_write_enable <=> s'.ID.ID_EX_write_enable) /\
    ((REG_write fext s s').EX.EX_NOP_flag <=> s'.EX.EX_NOP_flag) /\
    ((REG_write fext s s').MEM.MEM_state_flag <=> s'.MEM.MEM_state_flag)
Proof
  rw [REG_write_def]
QED

Theorem REG_write_unchanged_IF_items:
  !fext s s'.
    ((REG_write fext s s').IF.IF_PC_write_enable <=> s'.IF.IF_PC_write_enable) /\
    ((REG_write fext s s').IF.IF_PC_input = s'.IF.IF_PC_input) /\
    ((REG_write fext s s').IF.IF_instr = s'.IF.IF_instr) /\
    ((REG_write fext s s').PC = s'.PC)
Proof
  rw [REG_write_def]
QED

Theorem REG_write_unchanged_ID_items:
  !fext s s'.
    ((REG_write fext s s').ID.ID_ID_write_enable <=> s'.ID.ID_ID_write_enable) /\
    ((REG_write fext s s').ID.ID_flush_flag <=> s'.ID.ID_flush_flag) /\
    ((REG_write fext s s').ID.ID_PC = s'.ID.ID_PC) /\
    ((REG_write fext s s').ID.ID_instr = s'.ID.ID_instr)
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
    ((REG_write fext s s').EX.EX_write_reg = s'.EX.EX_write_reg) /\
    ((REG_write fext s s').EX.EX_addrW = s'.EX.EX_addrW) /\
    ((REG_write fext s s').EX.EX_opc = s'.EX.EX_opc) /\
    ((REG_write fext s s').EX.EX_func = s'.EX.EX_func)
Proof
  rw [REG_write_def]
QED

Theorem REG_write_unchanged_EX_ctrl_items:
  !fext s s'.
    (REG_write fext s s').EX.EX_PC_sel = s'.EX.EX_PC_sel
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

Theorem REG_write_unchanged_EX_jump:
  !fext s s'.
    ((REG_write fext s s').EX.EX_jump_sel <=> s'.EX.EX_jump_sel) /\
    ((REG_write fext s s').EX.EX_jump_addr = s'.EX.EX_jump_addr)
Proof
  rw [REG_write_def]
QED

Theorem REG_write_unchanged_WB_ctrl_items:
  !fext s s'.
    ((REG_write fext s s').WB.WB_state_flag <=> s'.WB.WB_state_flag)
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
Theorem EX_pipeline_unchanged_enable_flags:
  !fext s s'.
    ((EX_pipeline fext s s').ID.ID_EX_write_enable <=> s'.ID.ID_EX_write_enable) /\
    ((EX_pipeline fext s s').EX.EX_NOP_flag <=> s'.EX.EX_NOP_flag) /\
    ((EX_pipeline fext s s').MEM.MEM_state_flag <=> s'.MEM.MEM_state_flag)
Proof
  rw [EX_pipeline_def]
QED

Theorem EX_pipeline_unchanged_IF_items:
  !fext s s'.
    ((EX_pipeline fext s s').IF.IF_PC_write_enable <=> s'.IF.IF_PC_write_enable) /\
    ((EX_pipeline fext s s').IF.IF_PC_input = s'.IF.IF_PC_input) /\
    ((EX_pipeline fext s s').IF.IF_instr = s'.IF.IF_instr) /\
    ((EX_pipeline fext s s').PC = s'.PC)
Proof
  rw [EX_pipeline_def]
QED

Theorem EX_pipeline_unchanged_ID_items:
  !fext s s'.
    ((EX_pipeline fext s s').ID.ID_ID_write_enable <=> s'.ID.ID_ID_write_enable) /\
    ((EX_pipeline fext s s').ID.ID_flush_flag <=> s'.ID.ID_flush_flag) /\
    ((EX_pipeline fext s s').ID.ID_PC = s'.ID.ID_PC) /\
    ((EX_pipeline fext s s').ID.ID_instr = s'.ID.ID_instr)
Proof
  rw [EX_pipeline_def]
QED

Theorem EX_pipeline_unchanged_EX_ctrl_items:
  !fext s s'.
    (EX_pipeline fext s s').EX.EX_PC_sel = s'.EX.EX_PC_sel
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

Theorem EX_pipeline_unchanged_EX_jump:
  !fext s s'.
    ((EX_pipeline fext s s').EX.EX_jump_sel <=> s'.EX.EX_jump_sel) /\
    ((EX_pipeline fext s s').EX.EX_jump_addr = s'.EX.EX_jump_addr)
Proof
  rw [EX_pipeline_def]
QED

Theorem EX_pipeline_unchanged_WB_ctrl_items:
  !fext s s'.
    ((EX_pipeline fext s s').WB.WB_state_flag <=> s'.WB.WB_state_flag)
Proof
  rw [EX_pipeline_def]
QED

Theorem EX_pipeline_unchanged_state_items:
  !fext s s'.
    ((EX_pipeline fext s s').command = s'.command) /\
    ((EX_pipeline fext s s').state = s'.state) /\
    ((EX_pipeline fext s s').R = s'.R)
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
    ((MEM_pipeline fext s s').IF.IF_PC_input = s'.IF.IF_PC_input) /\
    ((MEM_pipeline fext s s').IF.IF_instr = s'.IF.IF_instr) /\
    ((MEM_pipeline fext s s').PC = s'.PC)
Proof
  rw [MEM_pipeline_def]
QED

Theorem MEM_pipeline_unchanged_ID_items:
  !fext s s'.
    ((MEM_pipeline fext s s').ID.ID_ID_write_enable <=> s'.ID.ID_ID_write_enable) /\
    ((MEM_pipeline fext s s').ID.ID_flush_flag <=> s'.ID.ID_flush_flag) /\
    ((MEM_pipeline fext s s').ID.ID_PC = s'.ID.ID_PC) /\
    ((MEM_pipeline fext s s').ID.ID_instr = s'.ID.ID_instr) /\
    ((MEM_pipeline fext s s').ID.ID_addrW = s'.ID.ID_addrW) /\
    ((MEM_pipeline fext s s').ID.ID_imm = s'.ID.ID_imm) /\
    ((MEM_pipeline fext s s').ID.ID_dataA = s'.ID.ID_dataA) /\
    ((MEM_pipeline fext s s').ID.ID_dataB = s'.ID.ID_dataB) /\
    ((MEM_pipeline fext s s').ID.ID_dataW = s'.ID.ID_dataW)
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

Theorem MEM_pipeline_unchanged_EX_pipeline_items:
  !fext s s'.
    ((MEM_pipeline fext s s').EX.EX_PC = s'.EX.EX_PC) /\
    ((MEM_pipeline fext s s').EX.EX_dataA = s'.EX.EX_dataA) /\
    ((MEM_pipeline fext s s').EX.EX_dataB = s'.EX.EX_dataB) /\
    ((MEM_pipeline fext s s').EX.EX_dataW = s'.EX.EX_dataW) /\
    ((MEM_pipeline fext s s').EX.EX_imm = s'.EX.EX_imm) /\
    ((MEM_pipeline fext s s').EX.EX_write_reg = s'.EX.EX_write_reg) /\
    ((MEM_pipeline fext s s').EX.EX_addrW = s'.EX.EX_addrW) /\
    ((MEM_pipeline fext s s').EX.EX_opc = s'.EX.EX_opc) /\
    ((MEM_pipeline fext s s').EX.EX_func = s'.EX.EX_func)
Proof
  rw [MEM_pipeline_def]
QED

Theorem MEM_pipeline_unchanged_EX_ctrl_items:
  !fext s s'.
    (MEM_pipeline fext s s').EX.EX_PC_sel = s'.EX.EX_PC_sel
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

Theorem MEM_pipeline_unchanged_EX_jump:
  !fext s s'.
    ((MEM_pipeline fext s s').EX.EX_jump_sel <=> s'.EX.EX_jump_sel) /\
    ((MEM_pipeline fext s s').EX.EX_jump_addr = s'.EX.EX_jump_addr)
Proof
  rw [MEM_pipeline_def]
QED

Theorem MEM_pipeline_unchanged_WB_ctrl_items:
  !fext s s'.
    ((MEM_pipeline fext s s').WB.WB_state_flag <=> s'.WB.WB_state_flag)
Proof
  rw [MEM_pipeline_def]
QED

Theorem MEM_pipeline_unchanged_state_items:
  !fext s s'.
    ((MEM_pipeline fext s s').command = s'.command) /\
    ((MEM_pipeline fext s s').state = s'.state) /\
    ((MEM_pipeline fext s s').R = s'.R)
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
    ((WB_pipeline fext s s').IF.IF_PC_input = s'.IF.IF_PC_input) /\
    ((WB_pipeline fext s s').IF.IF_instr = s'.IF.IF_instr) /\
    ((WB_pipeline fext s s').PC = s'.PC)
Proof
  rw [WB_pipeline_def]
QED

Theorem WB_pipeline_unchanged_ID_items:
  !fext s s'.
    ((WB_pipeline fext s s').ID.ID_ID_write_enable <=> s'.ID.ID_ID_write_enable) /\
    ((WB_pipeline fext s s').ID.ID_flush_flag <=> s'.ID.ID_flush_flag) /\
    ((WB_pipeline fext s s').ID.ID_PC = s'.ID.ID_PC) /\
    ((WB_pipeline fext s s').ID.ID_instr = s'.ID.ID_instr) /\
    ((WB_pipeline fext s s').ID.ID_addrW = s'.ID.ID_addrW) /\
    ((WB_pipeline fext s s').ID.ID_imm = s'.ID.ID_imm) /\
    ((WB_pipeline fext s s').ID.ID_dataA = s'.ID.ID_dataA) /\
    ((WB_pipeline fext s s').ID.ID_dataB = s'.ID.ID_dataB) /\
    ((WB_pipeline fext s s').ID.ID_dataW = s'.ID.ID_dataW)
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

Theorem WB_pipeline_unchanged_EX_pipeline_items:
  !fext s s'.
    ((WB_pipeline fext s s').EX.EX_PC = s'.EX.EX_PC) /\
    ((WB_pipeline fext s s').EX.EX_dataA = s'.EX.EX_dataA) /\
    ((WB_pipeline fext s s').EX.EX_dataB = s'.EX.EX_dataB) /\
    ((WB_pipeline fext s s').EX.EX_dataW = s'.EX.EX_dataW) /\
    ((WB_pipeline fext s s').EX.EX_imm = s'.EX.EX_imm) /\
    ((WB_pipeline fext s s').EX.EX_write_reg = s'.EX.EX_write_reg) /\
    ((WB_pipeline fext s s').EX.EX_addrW = s'.EX.EX_addrW) /\
    ((WB_pipeline fext s s').EX.EX_opc = s'.EX.EX_opc) /\
    ((WB_pipeline fext s s').EX.EX_func = s'.EX.EX_func)
Proof
  rw [WB_pipeline_def]
QED

Theorem WB_pipeline_unchanged_EX_ctrl_items:
  !fext s s'.
    (WB_pipeline fext s s').EX.EX_PC_sel = s'.EX.EX_PC_sel
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

Theorem WB_pipeline_unchanged_EX_jump:
  !fext s s'.
    ((WB_pipeline fext s s').EX.EX_jump_sel <=> s'.EX.EX_jump_sel) /\
    ((WB_pipeline fext s s').EX.EX_jump_addr = s'.EX.EX_jump_addr)
Proof
  rw [WB_pipeline_def]
QED

Theorem WB_pipeline_unchanged_WB_ctrl_items:
  !fext s s'.
    ((WB_pipeline fext s s').WB.WB_state_flag <=> s'.WB.WB_state_flag)
Proof
  rw [WB_pipeline_def]
QED

Theorem WB_pipeline_unchanged_state_items:
  !fext s s'.
    ((WB_pipeline fext s s').command = s'.command) /\
    ((WB_pipeline fext s s').state = s'.state) /\
    ((WB_pipeline fext s s').R = s'.R)
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
    ((agp32_next_state fext s s').IF.IF_PC_input = s'.IF.IF_PC_input) /\
    ((agp32_next_state fext s s').IF.IF_instr = s'.IF.IF_instr) /\
    ((agp32_next_state fext s s').PC = s'.PC)
Proof
  rw [agp32_next_state_def] >>
  Cases_on_word_value `(1 >< 0) s.MEM.MEM_dataB` >> fs []
QED

Theorem agp32_next_state_unchanged_ID_items:
  !fext s s'.
    ((agp32_next_state fext s s').ID.ID_ID_write_enable <=> s'.ID.ID_ID_write_enable) /\
    ((agp32_next_state fext s s').ID.ID_flush_flag <=> s'.ID.ID_flush_flag) /\
    ((agp32_next_state fext s s').ID.ID_PC = s'.ID.ID_PC) /\
    ((agp32_next_state fext s s').ID.ID_instr = s'.ID.ID_instr) /\
    ((agp32_next_state fext s s').ID.ID_addrW = s'.ID.ID_addrW) /\
    ((agp32_next_state fext s s').ID.ID_imm = s'.ID.ID_imm) /\
    ((agp32_next_state fext s s').ID.ID_dataA = s'.ID.ID_dataA) /\
    ((agp32_next_state fext s s').ID.ID_dataB = s'.ID.ID_dataB) /\
    ((agp32_next_state fext s s').ID.ID_dataW = s'.ID.ID_dataW)
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

Theorem agp32_next_state_unchanged_EX_pipeline_items:
  !fext s s'.
    ((agp32_next_state fext s s').EX.EX_PC = s'.EX.EX_PC) /\
    ((agp32_next_state fext s s').EX.EX_dataA = s'.EX.EX_dataA) /\
    ((agp32_next_state fext s s').EX.EX_dataB = s'.EX.EX_dataB) /\
    ((agp32_next_state fext s s').EX.EX_dataW = s'.EX.EX_dataW) /\
    ((agp32_next_state fext s s').EX.EX_imm = s'.EX.EX_imm) /\
    ((agp32_next_state fext s s').EX.EX_write_reg = s'.EX.EX_write_reg) /\
    ((agp32_next_state fext s s').EX.EX_addrW = s'.EX.EX_addrW) /\
    ((agp32_next_state fext s s').EX.EX_opc = s'.EX.EX_opc) /\
    ((agp32_next_state fext s s').EX.EX_func = s'.EX.EX_func)
Proof
  rw [agp32_next_state_def] >>
  Cases_on_word_value `(1 >< 0) s.MEM.MEM_dataB` >> fs []
QED
   
Theorem agp32_next_state_unchanged_EX_ctrl_items:
  !fext s s'.
    (agp32_next_state fext s s').EX.EX_PC_sel = s'.EX.EX_PC_sel
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

Theorem agp32_next_state_unchanged_EX_jump:
  !fext s s'.
    ((agp32_next_state fext s s').EX.EX_jump_sel <=> s'.EX.EX_jump_sel) /\
    ((agp32_next_state fext s s').EX.EX_jump_addr = s'.EX.EX_jump_addr)
Proof
  rw [agp32_next_state_def] >>
  Cases_on_word_value `(1 >< 0) s.MEM.MEM_dataB` >> fs []
QED

Theorem agp32_next_state_unchanged_WB_ctrl_items:
  !fext s s'.
    ((agp32_next_state fext s s').WB.WB_state_flag <=> s'.WB.WB_state_flag)
Proof
  rw [agp32_next_state_def] >>
  Cases_on_word_value `(1 >< 0) s.MEM.MEM_dataB` >> fs []
QED

Theorem agp32_next_state_unchanged_state_items:
  !fext s s'.
    ((agp32_next_state fext s s').R = s'.R)
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
    (agp32 fext fbits (SUC t)).PC = (IF_PC_update (fext t) s s').PC
Proof
  rw [agp32_def,mk_module_def,mk_circuit_def] >>
  qpat_abbrev_tac `s = mk_circuit (procs _) (procs _) (agp32_init fbits) fext t` >>
  qpat_abbrev_tac `s0 = procs _ (fext t) s s` >>
  qpat_abbrev_tac `s' = procs _ (fext t) s s` >>
  clist_update_state_tac >>
  fs [Abbr `s14`,Abbr `s13`,Abbr `s12`,Abbr `s11`,Abbr `s10`,Abbr `s9`,Abbr `s8`,Abbr `s7`,
      Abbr `s6`,Abbr `s5`,Abbr `s4`,Abbr `s3`,Abbr `s2`,Abbr `s1`,Abbr `s0`,Abbr `s'`,
      Hazard_ctrl_unchanged_IF,WB_update_unchanged_IF,
      MEM_ctrl_update_unchanged_IF,IF_PC_input_update_unchanged_IF,
      EX_jump_sel_addr_update_unchanged_IF,EX_SHIFT_update_unchanged_IF,
      EX_ALU_update_unchanged_IF,EX_ALU_input_imm_update_unchanged_IF,
      EX_ctrl_update_unchanged_IF,ID_data_check_update_unchanged_IF,
      ID_data_update_unchanged_IF,ID_imm_update_unchanged_IF,
      ID_opc_func_update_unchanged_IF,IF_instr_update_unchanged_IF] >>
  slist_update_state_tac >>
  fs [Abbr `ss8`,Acc_compute_unchanged_IF,Abbr `ss7`]
QED

(** IF_PC_input is only changed by the IF_PC_input_update function **)    
Theorem agp32_IF_PC_input_updated_by_IF_PC_input_update:
  !fext fbits t s s' s''.
    s = agp32 fext fbits t ==>
    s' = procs [agp32_next_state; WB_pipeline; MEM_pipeline; EX_pipeline;
                REG_write; ID_pipeline; IF_PC_update; Acc_compute]
               (fext t) s s ==>
    s'' = procs [IF_instr_update; ID_opc_func_update; ID_imm_update;
                 ID_data_update; ID_data_check_update; EX_ctrl_update;
                 EX_ALU_input_imm_update; EX_ALU_update;
                 EX_SHIFT_update; EX_jump_sel_addr_update]
                (fext (SUC t)) s' s' ==>
    (agp32 fext fbits (SUC t)).IF.IF_PC_input =
    (IF_PC_input_update (fext (SUC t)) s' s'').IF.IF_PC_input
Proof
  rw [agp32_def,mk_module_def,mk_circuit_def] >>
  qpat_abbrev_tac `s = mk_circuit (procs _) (procs _) (agp32_init fbits) fext t` >>
  qpat_abbrev_tac `s0 = procs _ (fext t) s s` >>
  clist_update_state_tac >>
  fs [Abbr `s14`,Abbr `s13`,Abbr `s12`,Abbr `s11`,
      Hazard_ctrl_unchanged_IF,WB_update_unchanged_IF,MEM_ctrl_update_unchanged_IF]
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
  fs [Abbr `s14`,Abbr `s13`,Abbr `s12`,Abbr `s11`,Abbr `s10`,Abbr `s9`,Abbr `s8`,Abbr `s7`,
      Abbr `s6`,Abbr `s5`,Abbr `s4`,Abbr `s3`,Abbr `s2`,Abbr `s1`,
      Hazard_ctrl_unchanged_IF,WB_update_unchanged_IF,
      MEM_ctrl_update_unchanged_IF,IF_PC_input_update_unchanged_IF,
      EX_jump_sel_addr_update_unchanged_IF,EX_SHIFT_update_unchanged_IF,
      EX_ALU_update_unchanged_IF,EX_ALU_input_imm_update_unchanged_IF,
      EX_ctrl_update_unchanged_IF,ID_data_check_update_unchanged_IF,
      ID_data_update_unchanged_IF,ID_imm_update_unchanged_IF,
      ID_opc_func_update_unchanged_IF,IF_instr_update_def]
QED

(** ID_PC and ID_instr are only changed by the ID_pipeline function **)
Theorem agp32_ID_PC_instr_updated_by_ID_pipeline:
  !fext fbits t s s'.
    s = agp32 fext fbits t ==>
    s' = procs [agp32_next_state; WB_pipeline; MEM_pipeline; EX_pipeline; REG_write] (fext t) s s ==>
    ((agp32 fext fbits (SUC t)).ID.ID_PC = (ID_pipeline (fext t) s s').ID.ID_PC) /\
    ((agp32 fext fbits (SUC t)).ID.ID_instr = (ID_pipeline (fext t) s s').ID.ID_instr)
Proof
  rw [agp32_def,mk_module_def,mk_circuit_def] >>
  qpat_abbrev_tac `s = mk_circuit (procs _) (procs _) (agp32_init fbits) fext t` >>
  qpat_abbrev_tac `s0 = procs _ (fext t) s s` >>
  qpat_abbrev_tac `s' = procs _ (fext t) s s` >>
  clist_update_state_tac >>
  fs [Abbr `s14`,Abbr `s13`,Abbr `s12`,Abbr `s11`,Abbr `s10`,Abbr `s9`,Abbr `s8`,Abbr `s7`,
      Abbr `s6`,Abbr `s5`,Abbr `s4`,Abbr `s3`,Abbr `s2`,Abbr `s1`,Abbr `s0`,Abbr `s'`,
      Hazard_ctrl_unchanged_ID_pipeline_items,WB_update_unchanged_ID_pipeline_items,
      MEM_ctrl_update_unchanged_ID_pipeline_items,IF_PC_input_update_unchanged_ID_pipeline_items,
      EX_jump_sel_addr_update_unchanged_ID_pipeline_items,
      EX_SHIFT_update_unchanged_ID_pipeline_items,EX_ALU_update_unchanged_ID_pipeline_items,
      EX_ALU_input_imm_update_unchanged_ID_pipeline_items,EX_ctrl_update_unchanged_ID_pipeline_items,
      ID_data_check_update_unchanged_ID_pipeline_items,ID_data_update_unchanged_ID_pipeline_items,
      ID_imm_update_unchanged_ID_pipeline_items,ID_opc_func_update_unchanged_ID_pipeline_items,
      IF_instr_update_unchanged_ID_pipeline_items] >>
  slist_update_state_tac >>
  fs [Abbr `ss8`,Acc_compute_unchanged_ID_items,Abbr `ss7`,IF_PC_update_unchanged_ID_pipeline_items]
QED

(** ID_opc and func are only changed by the ID_opc_func_update function **)
Theorem agp32_ID_opc_func_updated_by_ID_opc_func_update:
  !fext fbits t s s' s'' s0.
    s = agp32 fext fbits t ==>
    s' = procs [agp32_next_state; WB_pipeline; MEM_pipeline; EX_pipeline;
                REG_write; ID_pipeline; IF_PC_update; Acc_compute] (fext t) s s ==>
    s'' = procs [IF_instr_update] (fext (SUC t)) s' s' ==>
    ((agp32 fext fbits (SUC t)).ID.ID_func = (ID_opc_func_update (fext (SUC t)) s0 s'').ID.ID_func) /\
    ((agp32 fext fbits (SUC t)).ID.ID_opc = (ID_opc_func_update (fext (SUC t)) s0 s'').ID.ID_opc)
Proof
  rpt gen_tac >> rpt disch_tac >>
  fs [agp32_def,mk_module_def,mk_circuit_def] >>
  qpat_abbrev_tac `s''' = mk_circuit (procs _) (procs _) (agp32_init fbits) fext t` >>
  qpat_abbrev_tac `s'''' = procs _ (fext t) s''' s'''` >>
  clist_update_state_tac >>
  fs [Abbr `s14`,Abbr `s13`,Abbr `s12`,Abbr `s11`,Abbr `s10`,Abbr `s9`,
      Abbr `s8`,Abbr `s7`,Abbr `s6`,Abbr `s5`,Abbr `s4`,Abbr `s3`,Abbr `s2`,
      Hazard_ctrl_unchanged_ID_opc_func,WB_update_unchanged_ID_opc_func,
      MEM_ctrl_update_unchanged_ID_opc_func,IF_PC_input_update_unchanged_ID_opc_func,
      EX_jump_sel_addr_update_unchanged_ID_opc_func,EX_SHIFT_update_unchanged_ID_opc_func,
      EX_ALU_update_unchanged_ID_opc_func,EX_ALU_input_imm_update_def,
      EX_ctrl_update_unchanged_ID_opc_func,ID_data_check_update_unchanged_ID_opc_func,
      ID_data_update_unchanged_ID_opc_func,ID_imm_update_unchanged_ID_opc_func] >>
  rw [ID_opc_func_update_def]
QED

(** ID_addrA/B/W are only changed by the ID_data_update function **)
Theorem agp32_ID_addr_updated_by_ID_data_update:
  !fext fbits t s s' s'' s0.
    s = agp32 fext fbits t ==>
    s' = procs [agp32_next_state; WB_pipeline; MEM_pipeline; EX_pipeline;
                REG_write; ID_pipeline; IF_PC_update; Acc_compute] (fext t) s s ==>
    s'' = procs [IF_instr_update; ID_opc_func_update; ID_imm_update] (fext (SUC t)) s' s' ==>
    ((agp32 fext fbits (SUC t)).ID.ID_addrA = (ID_data_update (fext (SUC t)) s0 s'').ID.ID_addrA) /\
    ((agp32 fext fbits (SUC t)).ID.ID_addrB = (ID_data_update (fext (SUC t)) s0 s'').ID.ID_addrB) /\
    ((agp32 fext fbits (SUC t)).ID.ID_addrW = (ID_data_update (fext (SUC t)) s0 s'').ID.ID_addrW)
Proof
  rpt gen_tac >> rpt disch_tac >>
  fs [agp32_def,mk_module_def,mk_circuit_def] >>
  qpat_abbrev_tac `s''' = mk_circuit (procs _) (procs _) (agp32_init fbits) fext t` >>
  qpat_abbrev_tac `s'''' = procs _ (fext t) s''' s'''` >>
  clist_update_state_tac >>
  fs [Abbr `s14`,Abbr `s13`,Abbr `s12`,Abbr `s11`,Abbr `s10`,Abbr `s9`,
      Abbr `s8`,Abbr `s7`,Abbr `s6`,Abbr `s5`,Abbr `s4`,
      Hazard_ctrl_unchanged_ID_data_items,WB_update_unchanged_ID_data_items,
      MEM_ctrl_update_unchanged_ID_data_items,IF_PC_input_update_unchanged_ID_data_items,
      EX_jump_sel_addr_update_unchanged_ID_data_items,
      EX_SHIFT_update_unchanged_ID_data_items,EX_ALU_update_unchanged_ID_data_items,
      EX_ALU_input_imm_update_unchanged_ID_data_items,EX_ctrl_update_unchanged_ID_data_items,
      ID_data_check_update_unchanged_ID_data_items] >>
  fs [ID_data_update_def]
QED

(** ID_addrA/B/W_disable are only changed by the ID_data_update function **)
Theorem agp32_ID_flag_updated_by_ID_data_update:
  !fext fbits t s s' s''.
    s = agp32 fext fbits t ==>
    s' = procs [agp32_next_state; WB_pipeline; MEM_pipeline; EX_pipeline;
                REG_write; ID_pipeline; IF_PC_update; Acc_compute] (fext t) s s ==>
    s'' = procs [IF_instr_update; ID_opc_func_update; ID_imm_update] (fext (SUC t)) s' s' ==>
    ((agp32 fext fbits (SUC t)).ID.ID_addrA_disable <=>
     (ID_data_update (fext (SUC t)) s' s'').ID.ID_addrA_disable) /\
    ((agp32 fext fbits (SUC t)).ID.ID_addrB_disable <=>
     (ID_data_update (fext (SUC t)) s' s'').ID.ID_addrB_disable) /\
    ((agp32 fext fbits (SUC t)).ID.ID_addrW_disable <=>
     (ID_data_update (fext (SUC t)) s' s'').ID.ID_addrW_disable)
Proof
  rpt gen_tac >> rpt disch_tac >>
  fs [agp32_def,mk_module_def,mk_circuit_def] >>
  qpat_abbrev_tac `s''' = mk_circuit (procs _) (procs _) (agp32_init fbits) fext t` >>
  qpat_abbrev_tac `s'''' = procs _ (fext t) s''' s'''` >>
  clist_update_state_tac >>
  fs [Abbr `s14`,Abbr `s13`,Abbr `s12`,Abbr `s11`,Abbr `s10`,Abbr `s9`,
      Abbr `s8`,Abbr `s7`,Abbr `s6`,Abbr `s5`,Abbr `s4`,
      Hazard_ctrl_unchanged_ID_data_items,WB_update_unchanged_ID_data_items,
      MEM_ctrl_update_unchanged_ID_data_items,IF_PC_input_update_unchanged_ID_data_items,
      EX_jump_sel_addr_update_unchanged_ID_data_items,
      EX_SHIFT_update_unchanged_ID_data_items,EX_ALU_update_unchanged_ID_data_items,
      EX_ALU_input_imm_update_unchanged_ID_data_items,EX_ctrl_update_unchanged_ID_data_items,
      ID_data_check_update_unchanged_ID_data_items] >>
  fs [ID_data_update_def]
QED

(** ID_read_dataA/B/W are only changed by the ID_data_update function **)
Theorem agp32_ID_read_data_updated_by_ID_data_update:
  !fext fbits t s s' s''.
    s = agp32 fext fbits t ==>
    s' = procs [agp32_next_state; WB_pipeline; MEM_pipeline; EX_pipeline;
                REG_write; ID_pipeline; IF_PC_update; Acc_compute] (fext t) s s ==>
    s'' = procs [IF_instr_update; ID_opc_func_update; ID_imm_update] (fext (SUC t)) s' s' ==>
    ((agp32 fext fbits (SUC t)).ID.ID_read_dataA =
     (ID_data_update (fext (SUC t)) s' s'').ID.ID_read_dataA) /\
    ((agp32 fext fbits (SUC t)).ID.ID_read_dataB =
     (ID_data_update (fext (SUC t)) s' s'').ID.ID_read_dataB) /\
    ((agp32 fext fbits (SUC t)).ID.ID_read_dataW =
     (ID_data_update (fext (SUC t)) s' s'').ID.ID_read_dataW)
Proof
  rpt gen_tac >> rpt disch_tac >>
  fs [agp32_def,mk_module_def,mk_circuit_def] >>
  qpat_abbrev_tac `s''' = mk_circuit (procs _) (procs _) (agp32_init fbits) fext t` >>
  qpat_abbrev_tac `s'''' = procs _ (fext t) s''' s'''` >>
  clist_update_state_tac >>
  fs [Abbr `s14`,Abbr `s13`,Abbr `s12`,Abbr `s11`,Abbr `s10`,Abbr `s9`,
      Abbr `s8`,Abbr `s7`,Abbr `s6`,Abbr `s5`,Abbr `s4`,
      Hazard_ctrl_unchanged_ID_data_items,WB_update_unchanged_ID_data_items,
      MEM_ctrl_update_unchanged_ID_data_items,IF_PC_input_update_unchanged_ID_data_items,
      EX_jump_sel_addr_update_unchanged_ID_data_items,
      EX_SHIFT_update_unchanged_ID_data_items,EX_ALU_update_unchanged_ID_data_items,
      EX_ALU_input_imm_update_unchanged_ID_data_items,EX_ctrl_update_unchanged_ID_data_items,
      ID_data_check_update_unchanged_ID_data_items] >>
  fs [ID_data_update_def]
QED

(** ID_immA/B/W are only changed by the ID_data_update function **)
Theorem agp32_ID_imm_data_updated_by_ID_data_update:
  !fext fbits t s s' s''.
    s = agp32 fext fbits t ==>
    s' = procs [agp32_next_state; WB_pipeline; MEM_pipeline; EX_pipeline;
                REG_write; ID_pipeline; IF_PC_update; Acc_compute] (fext t) s s ==>
    s'' = procs [IF_instr_update; ID_opc_func_update; ID_imm_update] (fext (SUC t)) s' s' ==>
    ((agp32 fext fbits (SUC t)).ID.ID_immA = (ID_data_update (fext (SUC t)) s' s'').ID.ID_immA) /\
    ((agp32 fext fbits (SUC t)).ID.ID_immB = (ID_data_update (fext (SUC t)) s' s'').ID.ID_immB) /\
    ((agp32 fext fbits (SUC t)).ID.ID_immW = (ID_data_update (fext (SUC t)) s' s'').ID.ID_immW)
Proof
  rpt gen_tac >> rpt disch_tac >>
  fs [agp32_def,mk_module_def,mk_circuit_def] >>
  qpat_abbrev_tac `s''' = mk_circuit (procs _) (procs _) (agp32_init fbits) fext t` >>
  qpat_abbrev_tac `s'''' = procs _ (fext t) s''' s'''` >>
  clist_update_state_tac >>
  fs [Abbr `s14`,Abbr `s13`,Abbr `s12`,Abbr `s11`,Abbr `s10`,Abbr `s9`,
      Abbr `s8`,Abbr `s7`,Abbr `s6`,Abbr `s5`,Abbr `s4`,
      Hazard_ctrl_unchanged_ID_data_items,WB_update_unchanged_ID_data_items,
      MEM_ctrl_update_unchanged_ID_data_items,IF_PC_input_update_unchanged_ID_data_items,
      EX_jump_sel_addr_update_unchanged_ID_data_items,
      EX_SHIFT_update_unchanged_ID_data_items,EX_ALU_update_unchanged_ID_data_items,
      EX_ALU_input_imm_update_unchanged_ID_data_items,EX_ctrl_update_unchanged_ID_data_items,
      ID_data_check_update_unchanged_ID_data_items] >>
  fs [ID_data_update_def]
QED

(** ID_dataA/B/W are only changed by the ID_data_update function **)
Theorem agp32_ID_data_updated_by_ID_data_update:
  !fext fbits t s s' s''.
    s = agp32 fext fbits t ==>
    s' = procs [agp32_next_state; WB_pipeline; MEM_pipeline; EX_pipeline;
                REG_write; ID_pipeline; IF_PC_update; Acc_compute] (fext t) s s ==>
    s'' = procs [IF_instr_update; ID_opc_func_update; ID_imm_update] (fext (SUC t)) s' s' ==>
    ((agp32 fext fbits (SUC t)).ID.ID_dataA = (ID_data_update (fext (SUC t)) s' s'').ID.ID_dataA) /\
    ((agp32 fext fbits (SUC t)).ID.ID_dataB = (ID_data_update (fext (SUC t)) s' s'').ID.ID_dataB) /\
    ((agp32 fext fbits (SUC t)).ID.ID_dataW = (ID_data_update (fext (SUC t)) s' s'').ID.ID_dataW)
Proof
  rpt gen_tac >> rpt disch_tac >>
  fs [agp32_def,mk_module_def,mk_circuit_def] >>
  qpat_abbrev_tac `s''' = mk_circuit (procs _) (procs _) (agp32_init fbits) fext t` >>
  qpat_abbrev_tac `s'''' = procs _ (fext t) s''' s'''` >>
  clist_update_state_tac >>
  fs [Abbr `s14`,Abbr `s13`,Abbr `s12`,Abbr `s11`,Abbr `s10`,Abbr `s9`,
      Abbr `s8`,Abbr `s7`,Abbr `s6`,Abbr `s5`,Abbr `s4`,
      Hazard_ctrl_unchanged_ID_data_items,WB_update_unchanged_ID_data_items,
      MEM_ctrl_update_unchanged_ID_data_items,IF_PC_input_update_unchanged_ID_data_items,
      EX_jump_sel_addr_update_unchanged_ID_data_items,
      EX_SHIFT_update_unchanged_ID_data_items,EX_ALU_update_unchanged_ID_data_items,
      EX_ALU_input_imm_update_unchanged_ID_data_items,EX_ctrl_update_unchanged_ID_data_items,
      ID_data_check_update_unchanged_ID_data_items] >>
  fs [ID_data_update_def]
QED

(** ID_imm is only changed by the ID_imm_update function **)
Theorem agp32_ID_imm_updated_by_ID_imm_update:
  !fext fbits t s s' s''.
    s = agp32 fext fbits t ==>
    s' = procs [agp32_next_state; WB_pipeline; MEM_pipeline; EX_pipeline;
                REG_write; ID_pipeline; IF_PC_update; Acc_compute] (fext t) s s ==>
    s'' = procs [IF_instr_update; ID_opc_func_update] (fext (SUC t)) s' s' ==>
    (agp32 fext fbits (SUC t)).ID.ID_imm = (ID_imm_update (fext (SUC t)) s' s'').ID.ID_imm
Proof
  rw [agp32_def,mk_module_def,mk_circuit_def] >>
  qpat_abbrev_tac `s''' = mk_circuit (procs _) (procs _) (agp32_init fbits) fext t` >>
  qpat_abbrev_tac `s'''' = procs _ (fext t) s''' s'''` >>
  clist_update_state_tac >>
  fs [Abbr `s14`,Abbr `s13`,Abbr `s12`,Abbr `s11`,Abbr `s10`,Abbr `s9`,
      Abbr `s8`,Abbr `s7`,Abbr `s6`,Abbr `s5`,Abbr `s4`,
      Hazard_ctrl_unchanged_ID_data_items,WB_update_unchanged_ID_data_items,
      MEM_ctrl_update_unchanged_ID_data_items,IF_PC_input_update_unchanged_ID_data_items,
      EX_jump_sel_addr_update_unchanged_ID_data_items,EX_SHIFT_update_unchanged_ID_data_items,
      EX_ALU_update_unchanged_ID_data_items,EX_ALU_input_imm_update_unchanged_ID_data_items,
      EX_ctrl_update_unchanged_ID_data_items,ID_data_check_update_unchanged_ID_data_items,
      ID_data_update_unchanged_ID_data_items]
QED

(** data hazard checks are only updated the ID_data_check_update function **)
Theorem agp32_ID_checks_updated_by_ID_data_check_update:
  !fext fbits t s s' s''.
    s = agp32 fext fbits t ==>
    s' = procs [agp32_next_state; WB_pipeline; MEM_pipeline; EX_pipeline;
                REG_write; ID_pipeline; IF_PC_update; Acc_compute] (fext t) s s ==>
    s'' = procs [IF_instr_update; ID_opc_func_update; ID_imm_update; ID_data_update] (fext (SUC t)) s' s' ==>
    ((agp32 fext fbits (SUC t)).EX.EX_checkA = (ID_data_check_update (fext (SUC t)) s' s'').EX.EX_checkA) /\
    ((agp32 fext fbits (SUC t)).EX.EX_checkB = (ID_data_check_update (fext (SUC t)) s' s'').EX.EX_checkB) /\
    ((agp32 fext fbits (SUC t)).EX.EX_checkW = (ID_data_check_update (fext (SUC t)) s' s'').EX.EX_checkW) /\
    ((agp32 fext fbits (SUC t)).MEM.MEM_checkA = (ID_data_check_update (fext (SUC t)) s' s'').MEM.MEM_checkA) /\
    ((agp32 fext fbits (SUC t)).MEM.MEM_checkB = (ID_data_check_update (fext (SUC t)) s' s'').MEM.MEM_checkB) /\
    ((agp32 fext fbits (SUC t)).MEM.MEM_checkW = (ID_data_check_update (fext (SUC t)) s' s'').MEM.MEM_checkW) /\
    ((agp32 fext fbits (SUC t)).WB.WB_checkA = (ID_data_check_update (fext (SUC t)) s' s'').WB.WB_checkA) /\
    ((agp32 fext fbits (SUC t)).WB.WB_checkB = (ID_data_check_update (fext (SUC t)) s' s'').WB.WB_checkB) /\
    ((agp32 fext fbits (SUC t)).WB.WB_checkW = (ID_data_check_update (fext (SUC t)) s' s'').WB.WB_checkW)
Proof
  rpt gen_tac >> rpt disch_tac >>
  fs [agp32_def,mk_module_def,mk_circuit_def] >>
  qpat_abbrev_tac `s''' = mk_circuit (procs _) (procs _) (agp32_init fbits) fext t` >>
  qpat_abbrev_tac `s'''' = procs _ (fext t) s''' s'''` >>
  clist_update_state_tac >>
  fs [Abbr `s14`,Abbr `s13`,Abbr `s12`,Abbr `s11`,Abbr `s10`,Abbr `s9`,
      Abbr `s8`,Abbr `s7`,Abbr `s6`,Abbr `s5`,Abbr `s4`,
      Hazard_ctrl_unchanged_ID_data_check_items,WB_update_unchanged_ID_data_check_items,
      MEM_ctrl_update_unchanged_ID_data_check_items,IF_PC_input_update_unchanged_ID_data_check_items,
      EX_jump_sel_addr_update_unchanged_ID_data_check_items,
      EX_SHIFT_update_unchanged_ID_data_check_items,EX_ALU_update_unchanged_ID_data_check_items,
      EX_ALU_input_imm_update_unchanged_ID_data_check_items,
      EX_ctrl_update_unchanged_ID_data_check_items]
QED

(** EX_PC/imm/addrW are only changed by the EX_pipeline function **)
Theorem agp32_EX_PC_imm_addrW_updated_by_EX_pipeline:
  !fext fbits t s s'.
    s = agp32 fext fbits t ==>
    s' = procs [agp32_next_state; WB_pipeline; MEM_pipeline] (fext t) s s ==>
    ((agp32 fext fbits (SUC t)).EX.EX_PC = (EX_pipeline (fext t) s s').EX.EX_PC) /\
    ((agp32 fext fbits (SUC t)).EX.EX_imm = (EX_pipeline (fext t) s s').EX.EX_imm) /\
    ((agp32 fext fbits (SUC t)).EX.EX_addrW = (EX_pipeline (fext t) s s').EX.EX_addrW)
Proof
  rw [agp32_def,mk_module_def,mk_circuit_def] >>
  qpat_abbrev_tac `s'' = mk_circuit (procs _) (procs _) (agp32_init fbits) fext t` >>
  qpat_abbrev_tac `s''' = procs _ (fext t) s'' s''` >>
  clist_update_state_tac >>
  fs [Abbr `s14`,Abbr `s13`,Abbr `s12`,Abbr `s11`,Abbr `s10`,Abbr `s9`,Abbr `s8`,Abbr `s7`,
      Abbr `s6`,Abbr `s5`,Abbr `s4`,Abbr `s3`,Abbr `s2`,Abbr `s1`,Abbr `s'''`,
      Hazard_ctrl_unchanged_EX_pipeline_items,WB_update_unchanged_EX_pipeline_items,
      MEM_ctrl_update_unchanged_EX_pipeline_items,IF_PC_input_update_unchanged_EX_pipeline_items,
      EX_jump_sel_addr_update_unchanged_EX_pipeline_items,
      EX_SHIFT_update_unchanged_EX_pipeline_items,EX_ALU_update_unchanged_EX_pipeline_items,
      EX_ALU_input_imm_update_unchanged_EX_pipeline_items,
      EX_ctrl_update_unchanged_EX_pipeline_items,ID_data_check_update_unchanged_EX_pipeline_items,
      ID_data_update_unchanged_EX_pipeline_items,ID_imm_update_unchanged_EX_pipeline_items,
      ID_opc_func_update_unchanged_EX_pipeline_items,IF_instr_update_unchanged_EX_pipeline_items] >>
  slist_update_state_tac >>
  fs [Abbr `ss8`,Acc_compute_unchanged_EX_pipeline_items,
      Abbr `ss7`,IF_PC_update_unchanged_EX_pipeline_items,
      Abbr `ss6`,ID_pipeline_unchanged_EX_pipeline_items,
      Abbr `ss5`,REG_write_unchanged_EX_pipeline_items]
QED

(** EX_dataA/B/W are only changed by the EX_pipeline function **)
Theorem agp32_EX_data_updated_by_EX_pipeline:
  !fext fbits t s s'.
    s = agp32 fext fbits t ==>
    s' = procs [agp32_next_state; WB_pipeline; MEM_pipeline] (fext t) s s ==>
    ((agp32 fext fbits (SUC t)).EX.EX_dataA = (EX_pipeline (fext t) s s').EX.EX_dataA) /\
    ((agp32 fext fbits (SUC t)).EX.EX_dataB = (EX_pipeline (fext t) s s').EX.EX_dataB) /\
    ((agp32 fext fbits (SUC t)).EX.EX_dataW = (EX_pipeline (fext t) s s').EX.EX_dataW)
Proof
  rw [agp32_def,mk_module_def,mk_circuit_def] >>
  qpat_abbrev_tac `s'' = mk_circuit (procs _) (procs _) (agp32_init fbits) fext t` >>
  qpat_abbrev_tac `s''' = procs _ (fext t) s'' s''` >>
  clist_update_state_tac >>
  fs [Abbr `s14`,Abbr `s13`,Abbr `s12`,Abbr `s11`,Abbr `s10`,Abbr `s9`,Abbr `s8`,Abbr `s7`,
      Abbr `s6`,Abbr `s5`,Abbr `s4`,Abbr `s3`,Abbr `s2`,Abbr `s1`,Abbr `s'''`,
      Hazard_ctrl_unchanged_EX_pipeline_items,WB_update_unchanged_EX_pipeline_items,
      MEM_ctrl_update_unchanged_EX_pipeline_items,IF_PC_input_update_unchanged_EX_pipeline_items,
      EX_jump_sel_addr_update_unchanged_EX_pipeline_items,
      EX_SHIFT_update_unchanged_EX_pipeline_items,EX_ALU_update_unchanged_EX_pipeline_items,
      EX_ALU_input_imm_update_unchanged_EX_pipeline_items,
      EX_ctrl_update_unchanged_EX_pipeline_items,ID_data_check_update_unchanged_EX_pipeline_items,
      ID_data_update_unchanged_EX_pipeline_items,ID_imm_update_unchanged_EX_pipeline_items,
      ID_opc_func_update_unchanged_EX_pipeline_items,IF_instr_update_unchanged_EX_pipeline_items] >>
  slist_update_state_tac >>
  fs [Abbr `ss8`,Acc_compute_unchanged_EX_pipeline_items,
      Abbr `ss7`,IF_PC_update_unchanged_EX_pipeline_items,
      Abbr `ss6`,ID_pipeline_unchanged_EX_pipeline_items,
      Abbr `ss5`,REG_write_unchanged_EX_pipeline_items]
QED

(** EX_write_reg is updated by the EX_pipeline function **)
Theorem agp32_EX_write_reg_updated_by_EX_pipeline:
  !fext fbits t s s' s''.
    s = agp32 fext fbits t ==>
    s' = procs [agp32_next_state; WB_pipeline; MEM_pipeline] (fext t) s s ==>
    ((agp32 fext fbits (SUC t)).EX.EX_write_reg = (EX_pipeline (fext t) s s').EX.EX_write_reg)
Proof
  rw [agp32_def,mk_module_def,mk_circuit_def] >>
  qpat_abbrev_tac `s'' = mk_circuit (procs _) (procs _) (agp32_init fbits) fext t` >>
  qpat_abbrev_tac `s''' = procs _ (fext t) s'' s''` >>
  clist_update_state_tac >>
  fs [Abbr `s14`,Abbr `s13`,Abbr `s12`,Abbr `s11`,Abbr `s10`,Abbr `s9`,Abbr `s8`,Abbr `s7`,
      Abbr `s6`,Abbr `s5`,Abbr `s4`,Abbr `s3`,Abbr `s2`,Abbr `s1`,Abbr `s'''`,
      Hazard_ctrl_unchanged_EX_pipeline_items,WB_update_unchanged_EX_pipeline_items,
      MEM_ctrl_update_unchanged_EX_pipeline_items,IF_PC_input_update_unchanged_EX_pipeline_items,
      EX_jump_sel_addr_update_unchanged_EX_pipeline_items,
      EX_SHIFT_update_unchanged_EX_pipeline_items,EX_ALU_update_unchanged_EX_pipeline_items,
      EX_ALU_input_imm_update_unchanged_EX_pipeline_items,
      EX_ctrl_update_unchanged_EX_pipeline_items,ID_data_check_update_unchanged_EX_pipeline_items,
      ID_data_update_unchanged_EX_pipeline_items,ID_imm_update_unchanged_EX_pipeline_items,
      ID_opc_func_update_unchanged_EX_pipeline_items,IF_instr_update_unchanged_EX_pipeline_items] >>
  slist_update_state_tac >>
  fs [Abbr `ss8`,Acc_compute_unchanged_EX_pipeline_items,
      Abbr `ss7`,IF_PC_update_unchanged_EX_pipeline_items,
      Abbr `ss6`,ID_pipeline_unchanged_EX_pipeline_items,
      Abbr `ss5`,REG_write_unchanged_EX_pipeline_items]
QED

(** EX_opc and func are updated by the EX_pipeline function **)
Theorem agp32_EX_opc_func_updated_by_EX_pipeline:
  !fext fbits t s s' s''.
    s = agp32 fext fbits t ==>
    s' = procs [agp32_next_state; WB_pipeline; MEM_pipeline] (fext t) s s ==>
    ((agp32 fext fbits (SUC t)).EX.EX_opc = (EX_pipeline (fext t) s s').EX.EX_opc) /\
    ((agp32 fext fbits (SUC t)).EX.EX_func = (EX_pipeline (fext t) s s').EX.EX_func)
Proof
  rw [agp32_def,mk_module_def,mk_circuit_def] >>
  qpat_abbrev_tac `s'' = mk_circuit (procs _) (procs _) (agp32_init fbits) fext t` >>
  qpat_abbrev_tac `s''' = procs _ (fext t) s'' s''` >>
  clist_update_state_tac >>
  fs [Abbr `s14`,Abbr `s13`,Abbr `s12`,Abbr `s11`,Abbr `s10`,Abbr `s9`,Abbr `s8`,Abbr `s7`,
      Abbr `s6`,Abbr `s5`,Abbr `s4`,Abbr `s3`,Abbr `s2`,Abbr `s1`,Abbr `s'''`,
      Hazard_ctrl_unchanged_EX_pipeline_items,WB_update_unchanged_EX_pipeline_items,
      MEM_ctrl_update_unchanged_EX_pipeline_items,IF_PC_input_update_unchanged_EX_pipeline_items,
      EX_jump_sel_addr_update_unchanged_EX_pipeline_items,
      EX_SHIFT_update_unchanged_EX_pipeline_items,EX_ALU_update_unchanged_EX_pipeline_items,
      EX_ALU_input_imm_update_unchanged_EX_pipeline_items,
      EX_ctrl_update_unchanged_EX_pipeline_items,ID_data_check_update_unchanged_EX_pipeline_items,
      ID_data_update_unchanged_EX_pipeline_items,ID_imm_update_unchanged_EX_pipeline_items,
      ID_opc_func_update_unchanged_EX_pipeline_items,IF_instr_update_unchanged_EX_pipeline_items] >>
  slist_update_state_tac >>
  fs [Abbr `ss8`,Acc_compute_unchanged_EX_pipeline_items,
      Abbr `ss7`,IF_PC_update_unchanged_EX_pipeline_items,
      Abbr `ss6`,ID_pipeline_unchanged_EX_pipeline_items,
      Abbr `ss5`,REG_write_unchanged_EX_pipeline_items]
QED

(** EX_PC_sel is only changed by the EX_ctrl_update function **)
Theorem agp32_EX_PC_sel_updated_by_EX_ctrl_update:
  !fext fbits t s s' s''.
    s = agp32 fext fbits t ==>
    s' = procs [agp32_next_state; WB_pipeline; MEM_pipeline; EX_pipeline;
                REG_write; ID_pipeline; IF_PC_update; Acc_compute] (fext t) s s ==>
    s'' = procs [IF_instr_update; ID_opc_func_update; ID_imm_update;
                 ID_data_update; ID_data_check_update] (fext (SUC t)) s' s' ==>
    (agp32 fext fbits (SUC t)).EX.EX_PC_sel = (EX_ctrl_update (fext (SUC t)) s' s'').EX.EX_PC_sel
Proof
  rw [agp32_def,mk_module_def,mk_circuit_def] >>
  qpat_abbrev_tac `s''' = mk_circuit (procs _) (procs _) (agp32_init fbits) fext t` >>
  qpat_abbrev_tac `s'''' = procs _ (fext t) s''' s'''` >>
  clist_update_state_tac >>
  fs [Abbr `s14`,Abbr `s13`,Abbr `s12`,Abbr `s11`,
      Abbr `s10`,Abbr `s9`,Abbr `s8`,Abbr `s7`,
      Hazard_ctrl_unchanged_EX_ctrl_items,WB_update_unchanged_EX_ctrl_items,
      MEM_ctrl_update_unchanged_EX_ctrl_items,IF_PC_input_update_unchanged_EX_ctrl_items,
      EX_jump_sel_addr_update_unchanged_EX_ctrl_items,EX_SHIFT_update_unchanged_EX_ctrl_items,
      EX_ALU_update_unchanged_EX_ctrl_items,EX_ALU_input_imm_update_unchanged_EX_ctrl_items]
QED

(** EX_ALU_input1/2 are only changed by the EX_ALU_input_imm_update function **)
Theorem agp32_EX_ALU_input_updated_by_EX_ALU_input_imm_update:
  !fext fbits t s s' s''.
    s = agp32 fext fbits t ==>
    s' = procs [agp32_next_state; WB_pipeline; MEM_pipeline; EX_pipeline;
                REG_write; ID_pipeline; IF_PC_update; Acc_compute] (fext t) s s ==>
    s'' = procs [IF_instr_update; ID_opc_func_update; ID_imm_update; ID_data_update;
                 ID_data_check_update; EX_ctrl_update] (fext (SUC t)) s' s' ==>
    ((agp32 fext fbits (SUC t)).EX.EX_ALU_input1 =
     (EX_ALU_input_imm_update (fext (SUC t)) s' s'').EX.EX_ALU_input1) /\
    ((agp32 fext fbits (SUC t)).EX.EX_ALU_input2 =
     (EX_ALU_input_imm_update (fext (SUC t)) s' s'').EX.EX_ALU_input2)
Proof
  rw [agp32_def,mk_module_def,mk_circuit_def] >>
  qpat_abbrev_tac `s' = mk_circuit (procs _) (procs _) (agp32_init fbits) fext t` >>
  qpat_abbrev_tac `s'' = procs _ (fext t) s' s'` >>
  clist_update_state_tac >>
  fs [Abbr `s14`,Abbr `s13`,Abbr `s12`,Abbr `s11`,Abbr `s10`,Abbr `s9`,Abbr `s8`,
      Hazard_ctrl_unchanged_EX_ALU,WB_update_unchanged_EX_ALU,
      MEM_ctrl_update_unchanged_EX_ALU,IF_PC_input_update_unchanged_EX_ALU,
      EX_jump_sel_addr_update_unchanged_EX_ALU,EX_SHIFT_update_unchanged_EX_ALU,
      EX_ALU_update_unchanged_EX_ALU_input]
QED

(** EX_imm_updated is only changed by the EX_ALU_input_imm_update function **)
Theorem agp32_EX_imm_updated_updated_by_EX_ALU_input_imm_update:
  !fext fbits t s s' s''.
    s = agp32 fext fbits t ==>
    s' = procs [agp32_next_state; WB_pipeline; MEM_pipeline; EX_pipeline;
                REG_write; ID_pipeline; IF_PC_update; Acc_compute] (fext t) s s ==>
    s'' = procs [IF_instr_update; ID_opc_func_update; ID_imm_update; ID_data_update;
                 ID_data_check_update; EX_ctrl_update] (fext (SUC t)) s' s' ==>
    (agp32 fext fbits (SUC t)).EX.EX_imm_updated =
    (EX_ALU_input_imm_update (fext (SUC t)) s' s'').EX.EX_imm_updated
Proof
  rw [agp32_def,mk_module_def,mk_circuit_def] >>
  qpat_abbrev_tac `s' = mk_circuit (procs _) (procs _) (agp32_init fbits) fext t` >>
  qpat_abbrev_tac `s'' = procs _ (fext t) s' s'` >>
  clist_update_state_tac >>
  fs [Abbr `s14`,Abbr `s13`,Abbr `s12`,Abbr `s11`,Abbr `s10`,Abbr `s9`,Abbr `s8`,
      Hazard_ctrl_unchanged_EX_ctrl_items,WB_update_unchanged_EX_ctrl_items,
      MEM_ctrl_update_unchanged_EX_ctrl_items,IF_PC_input_update_unchanged_EX_ctrl_items,
      EX_jump_sel_addr_update_unchanged_EX_ctrl_items,EX_SHIFT_update_unchanged_EX_ctrl_items,
      EX_ALU_update_unchanged_EX_ctrl_items]
QED

(** EX_carry_flag, EX_overflow_flag, EX_ALU_res are only changed by the EX_ALU_update function **)
Theorem agp32_EX_ALU_items_updated_by_EX_ALU_update:
  !fext fbits t s s' s''.
    s = agp32 fext fbits t ==>
    s' = procs [agp32_next_state; WB_pipeline; MEM_pipeline; EX_pipeline;
                REG_write; ID_pipeline; IF_PC_update; Acc_compute] (fext t) s s ==>
    s'' = procs [IF_instr_update; ID_opc_func_update; ID_imm_update;
                 ID_data_update; ID_data_check_update; EX_ctrl_update;
                 EX_ALU_input_imm_update] (fext (SUC t)) s' s' ==>
    ((agp32 fext fbits (SUC t)).EX.EX_carry_flag =
     (EX_ALU_update (fext (SUC t)) s' s'').EX.EX_carry_flag) /\
    ((agp32 fext fbits (SUC t)).EX.EX_overflow_flag =
     (EX_ALU_update (fext (SUC t)) s' s'').EX.EX_overflow_flag) /\
    ((agp32 fext fbits (SUC t)).EX.EX_ALU_res = (EX_ALU_update (fext (SUC t)) s' s'').EX.EX_ALU_res)
Proof
  rw [agp32_def,mk_module_def,mk_circuit_def] >>
  qpat_abbrev_tac `s''' = mk_circuit (procs _) (procs _) (agp32_init fbits) fext t` >>
  qpat_abbrev_tac `s'''' = procs _ (fext t) s''' s'''` >>
  clist_update_state_tac >>
  fs [Abbr `s14`,Abbr `s13`,Abbr `s12`,Abbr `s11`,Abbr `s10`,Abbr `s9`,
      Hazard_ctrl_unchanged_EX_ALU,WB_update_unchanged_EX_ALU,
      MEM_ctrl_update_unchanged_EX_ALU,IF_PC_input_update_unchanged_EX_ALU,
      EX_jump_sel_addr_update_unchanged_EX_ALU,EX_SHIFT_update_unchanged_EX_ALU]
QED


(** command and state are updated by the agp32_next_state function **)
Theorem agp32_command_state_updated_by_agp32_next_state:
  !fext fbits t s.
    s = agp32 fext fbits t ==>
    ((agp32 fext fbits (SUC t)).command = (agp32_next_state (fext t) s s).command) /\
    ((agp32 fext fbits (SUC t)).state = (agp32_next_state (fext t) s s).state)
Proof
  rw [agp32_def,mk_module_def,mk_circuit_def] >>
  qpat_abbrev_tac `s' = mk_circuit (procs _) (procs _) (agp32_init fbits) fext t` >>
  qpat_abbrev_tac `s'' = procs _ (fext t) s' s'` >>
  clist_update_state_tac >>
  fs [Abbr `s14`,Abbr `s13`,Abbr `s12`,Abbr `s11`,Abbr `s10`,Abbr `s9`,Abbr `s8`,Abbr `s7`,
      Abbr `s6`,Abbr `s5`,Abbr `s4`,Abbr `s3`,Abbr `s2`,Abbr `s1`,Abbr `s''`,
      Hazard_ctrl_unchanged_state_items,WB_update_unchanged_state_items,
      MEM_ctrl_update_unchanged_state_items,IF_PC_input_update_unchanged_state_items,
      EX_jump_sel_addr_update_unchanged_state_items,EX_SHIFT_update_unchanged_state_items,
      EX_ALU_update_unchanged_state_items,EX_ALU_input_imm_update_unchanged_state_items,
      EX_ctrl_update_unchanged_state_items,ID_data_check_update_unchanged_state_items,
      ID_data_update_unchanged_state_items,ID_imm_update_unchanged_state_items,
      ID_opc_func_update_unchanged_state_items,IF_instr_update_unchanged_state_items] >>
  slist_update_state_tac >>
  fs [Abbr `ss8`,Abbr `ss7`,Abbr `ss6`,Abbr `ss5`,Abbr `ss4`,Abbr `ss3`,Abbr `ss2`,
      Acc_compute_unchanged_state_items,IF_PC_update_unchanged_state_items,
      ID_pipeline_unchanged_state_items,REG_write_unchanged_state_items,
      EX_pipeline_unchanged_state_items,MEM_pipeline_unchanged_state_items,
      WB_pipeline_unchanged_state_items]
QED

(** R is updated by the REG_write function **)
Theorem agp32_R_updated_by_REG_write:
  !fext fbits t s s'.
    s = agp32 fext fbits t ==>
    s' = procs [agp32_next_state; WB_pipeline; MEM_pipeline; EX_pipeline] (fext t) s s ==>
    (agp32 fext fbits (SUC t)).R = (REG_write (fext t) s s').R
Proof
  rw [agp32_def,mk_module_def,mk_circuit_def] >>
  qpat_abbrev_tac `s' = mk_circuit (procs _) (procs _) (agp32_init fbits) fext t` >>
  qpat_abbrev_tac `s'' = procs _ (fext t) s' s'` >>
  clist_update_state_tac >>
  fs [Abbr `s14`,Abbr `s13`,Abbr `s12`,Abbr `s11`,Abbr `s10`,Abbr `s9`,Abbr `s8`,Abbr `s7`,
      Abbr `s6`,Abbr `s5`,Abbr `s4`,Abbr `s3`,Abbr `s2`,Abbr `s1`,Abbr `s''`,
      Hazard_ctrl_unchanged_state_items,WB_update_unchanged_state_items,
      MEM_ctrl_update_unchanged_state_items,IF_PC_input_update_unchanged_state_items,
      EX_jump_sel_addr_update_unchanged_state_items,EX_SHIFT_update_unchanged_state_items,
      EX_ALU_update_unchanged_state_items,EX_ALU_input_imm_update_unchanged_state_items,
      EX_ctrl_update_unchanged_state_items,ID_data_check_update_unchanged_state_items,
      ID_data_update_unchanged_state_items,ID_imm_update_unchanged_state_items,
      ID_opc_func_update_unchanged_state_items,IF_instr_update_unchanged_state_items] >>
  slist_update_state_tac >>
  fs [Abbr `ss8`,Abbr `ss7`,Abbr `ss6`,
      Acc_compute_unchanged_state_items,IF_PC_update_unchanged_state_items,
      ID_pipeline_unchanged_state_items]
QED


(* additional theorems for the correctness proof *)
Theorem agp32_same_EX_opc_func_until_ALU_update:
  !fext fbits t s s' s''.
    s = agp32 fext fbits t ==>
    s' = procs [agp32_next_state; WB_pipeline; MEM_pipeline; EX_pipeline;
                REG_write; ID_pipeline; IF_PC_update; Acc_compute] (fext t) s s ==>
    s'' = procs [IF_instr_update; ID_opc_func_update; ID_imm_update;
                 ID_data_update; ID_data_check_update; EX_ctrl_update;
                 EX_ALU_input_imm_update] (fext (SUC t)) s' s' ==>
    (s''.EX.EX_opc = (agp32 fext fbits (SUC t)).EX.EX_opc) /\
    (s''.EX.EX_func = (agp32 fext fbits (SUC t)).EX.EX_func)
Proof
  rpt strip_tac >>
  Q.ABBREV_TAC `s0 = procs [agp32_next_state;WB_pipeline;MEM_pipeline] (fext t) s s` >>
  `((agp32 fext fbits (SUC t)).EX.EX_opc = (EX_pipeline (fext t) s s0).EX.EX_opc) /\
   ((agp32 fext fbits (SUC t)).EX.EX_func = (EX_pipeline (fext t) s s0).EX.EX_func)`
    by fs [agp32_EX_opc_func_updated_by_EX_pipeline,Abbr `s0`] >>
  clist_update_state_before_ALU_tac >>
  fs [Abbr `s7`,Abbr `s6`,Abbr `s5`,Abbr `s4`,Abbr `s3`,Abbr `s2`,Abbr `s1`,Abbr `s'`,
      EX_ALU_input_imm_update_unchanged_EX_pipeline_items,
      EX_ctrl_update_unchanged_EX_pipeline_items,
      ID_data_check_update_unchanged_EX_pipeline_items,
      ID_data_update_unchanged_EX_pipeline_items,
      ID_imm_update_unchanged_EX_pipeline_items,
      ID_opc_func_update_unchanged_EX_pipeline_items,
      IF_instr_update_unchanged_EX_pipeline_items] >>
  slist_update_state_tac >>
  fs [Abbr `ss8`,Acc_compute_unchanged_EX_pipeline_items,
      Abbr `ss7`,IF_PC_update_unchanged_EX_pipeline_items,
      Abbr `ss6`,ID_pipeline_unchanged_EX_pipeline_items,
      Abbr `ss5`,REG_write_unchanged_EX_pipeline_items,Abbr `ss4`,
      Abbr `s0`,procs_def] >>
  rw [EX_pipeline_def]
QED

Theorem agp32_same_items_until_EX_ALU_update:
  !fext fbits t s s' s''.
    s = agp32 fext fbits t ==>
    s' = procs [agp32_next_state; WB_pipeline; MEM_pipeline; EX_pipeline;
                REG_write; ID_pipeline; IF_PC_update; Acc_compute] (fext t) s s ==>
    s'' = procs [IF_instr_update; ID_opc_func_update; ID_imm_update;
                 ID_data_update; ID_data_check_update; EX_ctrl_update;
                 EX_ALU_input_imm_update] (fext (SUC t)) s' s' ==>
    (s''.EX.EX_carry_flag = s.EX.EX_carry_flag) /\
    (s''.EX.EX_overflow_flag = s.EX.EX_overflow_flag) /\
    (s''.EX.EX_ALU_res = s.EX.EX_ALU_res) /\
    (s''.ID.ID_EX_write_enable = s.ID.ID_EX_write_enable)
Proof
  rw [] >> clist_update_state_before_ALU_tac >>
  fs [Abbr `s7`,Abbr `s6`,Abbr `s5`,Abbr `s4`,Abbr `s3`,Abbr `s2`,Abbr `s1`,Abbr `s'`,
      EX_ALU_input_imm_update_unchanged_EX_ALU,EX_ALU_input_imm_update_unchanged_enable_flags,
      EX_ctrl_update_unchanged_EX_ALU,EX_ctrl_update_unchanged_enable_flags,
      ID_data_check_update_unchanged_EX_ALU,ID_data_check_update_unchanged_enable_flags,
      ID_data_update_unchanged_EX_ALU,ID_data_update_unchanged_enable_flags,
      ID_imm_update_unchanged_EX_ALU,ID_imm_update_unchanged_enable_flags,
      ID_opc_func_update_unchanged_EX_ALU,ID_opc_func_update_unchanged_enable_flags,
      IF_instr_update_unchanged_EX_ALU,IF_instr_update_unchanged_enable_flags] >>
  slist_update_state_tac >>
  fs [Abbr `ss8`,Acc_compute_unchanged_EX_ALU,Acc_compute_unchanged_enable_flags,
      Abbr `ss7`,IF_PC_update_unchanged_EX_ALU,IF_PC_update_unchanged_enable_flags,
      Abbr `ss6`,ID_pipeline_unchanged_EX_ALU,ID_pipeline_unchanged_enable_flags,
      Abbr `ss5`,REG_write_unchanged_EX_ALU,REG_write_unchanged_enable_flags,
      Abbr `ss4`,EX_pipeline_unchanged_EX_ALU,EX_pipeline_unchanged_enable_flags,
      Abbr `ss3`,MEM_pipeline_unchanged_EX_ALU,MEM_pipeline_unchanged_enable_flags,
      Abbr `ss2`,WB_pipeline_unchanged_EX_ALU,WB_pipeline_unchanged_enable_flags,
      Abbr `ss1`,agp32_next_state_unchanged_EX_ALU,agp32_next_state_unchanged_enable_flags]
QED

Theorem agp32_same_EX_jump_items_after_EX_jump_update:
  !fext fbits t s s' s''.
    s = agp32 fext fbits t ==>
    s' = procs [agp32_next_state; WB_pipeline; MEM_pipeline; EX_pipeline;
                REG_write; ID_pipeline; IF_PC_update; Acc_compute] (fext t) s s ==>
    s'' = procs [IF_instr_update; ID_opc_func_update; ID_imm_update; ID_data_update;
                 ID_data_check_update; EX_ctrl_update; EX_ALU_input_imm_update;
                 EX_ALU_update; EX_SHIFT_update; EX_jump_sel_addr_update] (fext (SUC t)) s' s' ==>
    ((agp32 fext fbits (SUC t)).EX.EX_jump_sel <=> s''.EX.EX_jump_sel) /\
    ((agp32 fext fbits (SUC t)).EX.EX_jump_addr = s''.EX.EX_jump_addr)
Proof
  rw [agp32_def,mk_module_def,mk_circuit_def] >>
  qpat_abbrev_tac `s' = mk_circuit (procs _) (procs _) (agp32_init fbits) fext t` >>
  qpat_abbrev_tac `s'' = procs _ (fext t) s' s'` >>
  clist_update_state_tac >>
  fs [Abbr `s14`,Abbr `s13`,Abbr `s12`,Abbr `s11`,
      Hazard_ctrl_unchanged_EX_jump,WB_update_unchanged_EX_jump,
      MEM_ctrl_update_unchanged_EX_jump,IF_PC_input_update_unchanged_EX_jump]
QED

Theorem agp32_same_items_before_EX_ctrl_update:
  !fext fbits t s s' s''.
    s = agp32 fext fbits t ==>
    s' = procs [agp32_next_state; WB_pipeline; MEM_pipeline; EX_pipeline;
                REG_write; ID_pipeline; IF_PC_update; Acc_compute] (fext t) s s ==>
    s'' = procs [IF_instr_update; ID_opc_func_update; ID_imm_update; 
                 ID_data_update; ID_data_check_update] (fext (SUC t)) s' s' ==>
    (s''.ID.ID_EX_write_enable <=> s.ID.ID_EX_write_enable) /\
    (s''.EX.EX_PC_sel = s.EX.EX_PC_sel)
Proof
  rw [agp32_def,mk_module_def,mk_circuit_def] >>
  qpat_abbrev_tac `s' = mk_circuit (procs _) (procs _) (agp32_init fbits) fext t` >>
  qpat_abbrev_tac `s'' = procs _ (fext t) s' s'` >>
  fs [procs_def] >>
  qpat_abbrev_tac `s1 = IF_instr_update _ _ _` >>
  qpat_abbrev_tac `s2 = ID_opc_func_update _ _ _` >>
  qpat_abbrev_tac `s3 = ID_imm_update _ _ _` >>
  qpat_abbrev_tac `s4 = ID_data_update _ _ _` >>
  qpat_abbrev_tac `s5 = ID_data_check_update _ _ _` >>
  fs [Abbr `s5`,Abbr `s4`,Abbr `s3`,Abbr `s2`,Abbr `s1`,Abbr `s''`,
      ID_data_check_update_unchanged_enable_flags,ID_data_check_update_unchanged_EX_ctrl_items,
      ID_data_update_unchanged_enable_flags,ID_data_update_unchanged_EX_ctrl_items,
      ID_imm_update_unchanged_enable_flags,ID_imm_update_unchanged_EX_ctrl_items,
      ID_opc_func_update_unchanged_enable_flags,ID_opc_func_update_unchanged_EX_ctrl_items,
      IF_instr_update_unchanged_enable_flags,IF_instr_update_unchanged_EX_ctrl_items] >>
  slist_update_state_tac >>
  fs [Abbr `ss8`,Acc_compute_unchanged_EX_ctrl_items,Acc_compute_unchanged_enable_flags,
      Abbr `ss7`,IF_PC_update_unchanged_EX_ctrl_items,IF_PC_update_unchanged_enable_flags,
      Abbr `ss6`,ID_pipeline_unchanged_EX_ctrl_items,ID_pipeline_unchanged_enable_flags,
      Abbr `ss5`,REG_write_unchanged_EX_ctrl_items,REG_write_unchanged_enable_flags,
      Abbr `ss4`,EX_pipeline_unchanged_EX_ctrl_items,EX_pipeline_unchanged_enable_flags,
      Abbr `ss3`,MEM_pipeline_unchanged_EX_ctrl_items,MEM_pipeline_unchanged_enable_flags,
      Abbr `ss2`,WB_pipeline_unchanged_EX_ctrl_items,WB_pipeline_unchanged_enable_flags,
      Abbr `ss1`,agp32_next_state_unchanged_EX_ctrl_items,agp32_next_state_unchanged_enable_flags]
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
    (s'.IF.IF_PC_input = s.IF.IF_PC_input) /\
    (s'.PC = s.PC)
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

Theorem agp32_same_items_before_ID_pipeline:
  !fext fbits t s s'.
    s = agp32 fext fbits t ==>
    s' = procs [agp32_next_state;WB_pipeline;MEM_pipeline;EX_pipeline;REG_write] (fext t) s s ==>
    (s'.ID.ID_ID_write_enable <=> s.ID.ID_ID_write_enable) /\
    (s'.ID.ID_flush_flag <=> s.ID.ID_flush_flag) /\
    (s'.ID.ID_PC = s.ID.ID_PC) /\
    (s'.ID.ID_instr = s.ID.ID_instr) /\
    (s'.IF.IF_instr = s.IF.IF_instr)
Proof
  rpt STRIP_TAC >> fs [procs_def] >>
  qpat_abbrev_tac `ss1 = agp32_next_state _ _ _` >>
  qpat_abbrev_tac `ss2 = WB_pipeline _ _ _` >>
  qpat_abbrev_tac `ss3 = MEM_pipeline _ _ _` >>
  qpat_abbrev_tac `ss4 = EX_pipeline _ _ _` >>
  qpat_abbrev_tac `ss5 = REG_write _ _ _` >>
  fs [Abbr `ss5`,REG_write_unchanged_ID_items,REG_write_unchanged_IF_items,
      Abbr `ss4`,EX_pipeline_unchanged_ID_items,EX_pipeline_unchanged_IF_items,
      Abbr `ss3`,MEM_pipeline_unchanged_ID_items,MEM_pipeline_unchanged_IF_items,
      Abbr `ss2`,WB_pipeline_unchanged_ID_items,WB_pipeline_unchanged_IF_items,
      Abbr `ss1`,agp32_next_state_unchanged_ID_items,agp32_next_state_unchanged_IF_items]
QED

Theorem agp32_same_items_before_REG_write:
  !fext fbits t s s'.
    s = agp32 fext fbits t ==>
    s' = procs [agp32_next_state;WB_pipeline;MEM_pipeline;EX_pipeline] (fext t) s s ==>
    (s'.WB.WB_state_flag <=> s.WB.WB_state_flag) /\
    (s'.R = s.R)
Proof
  rpt STRIP_TAC >> fs [procs_def] >>
  qpat_abbrev_tac `ss1 = agp32_next_state _ _ _` >>
  qpat_abbrev_tac `ss2 = WB_pipeline _ _ _` >>
  qpat_abbrev_tac `ss3 = MEM_pipeline _ _ _` >>
  qpat_abbrev_tac `ss4 = EX_pipeline _ _ _` >>
  fs [Abbr `ss4`,EX_pipeline_unchanged_state_items,EX_pipeline_unchanged_WB_ctrl_items,
      Abbr `ss3`,MEM_pipeline_unchanged_state_items,MEM_pipeline_unchanged_WB_ctrl_items,
      Abbr `ss2`,WB_pipeline_unchanged_state_items,WB_pipeline_unchanged_WB_ctrl_items,
      Abbr `ss1`,agp32_next_state_unchanged_state_items,agp32_next_state_unchanged_WB_ctrl_items]
QED

Theorem agp32_same_ID_items_before_EX_pipeline:
  !fext fbits t s s'.
    s = agp32 fext fbits t ==>
    s' = procs [agp32_next_state;WB_pipeline;MEM_pipeline] (fext t) s s ==>
    (s'.ID.ID_imm = s.ID.ID_imm) /\
    (s'.ID.ID_addrW = s.ID.ID_addrW) /\
    (s'.ID.ID_dataA = s.ID.ID_dataA) /\
    (s'.ID.ID_dataB = s.ID.ID_dataB) /\
    (s'.ID.ID_dataW = s.ID.ID_dataW) /\
    (s'.ID.ID_opc = s.ID.ID_opc) /\
    (s'.ID.ID_func = s.ID.ID_func)
Proof
  rpt gen_tac >> rpt disch_tac >>
  fs [procs_def] >>
  qpat_abbrev_tac `ss1 = agp32_next_state _ _ _` >>
  qpat_abbrev_tac `ss2 = WB_pipeline _ _ _` >>
  qpat_abbrev_tac `ss3 = MEM_pipeline _ _ _` >>
  fs [Abbr `ss3`,MEM_pipeline_unchanged_ID_items,MEM_pipeline_unchanged_ID_opc_func,
      Abbr `ss2`,WB_pipeline_unchanged_ID_items,WB_pipeline_unchanged_ID_opc_func,
      Abbr `ss1`,agp32_next_state_unchanged_ID_items,agp32_next_state_unchanged_ID_opc_func]
QED

Theorem agp32_same_EX_items_before_EX_pipeline:
  !fext fbits t s s'.
    s = agp32 fext fbits t ==>
    s' = procs [agp32_next_state;WB_pipeline;MEM_pipeline] (fext t) s s ==>
    (s'.ID.ID_EX_write_enable <=> s.ID.ID_EX_write_enable) /\
    (s'.EX.EX_NOP_flag <=> s.EX.EX_NOP_flag) /\
    (s'.EX.EX_PC = s.EX.EX_PC) /\
    (s'.EX.EX_imm = s.EX.EX_imm) /\
    (s'.EX.EX_addrW = s.EX.EX_addrW) /\
    (s'.EX.EX_dataA = s.EX.EX_dataA) /\
    (s'.EX.EX_dataB = s.EX.EX_dataB) /\
    (s'.EX.EX_dataW = s.EX.EX_dataW) /\
    (s'.EX.EX_opc = s.EX.EX_opc) /\
    (s'.EX.EX_func = s.EX.EX_func) /\
    (s'.EX.EX_write_reg = s.EX.EX_write_reg)
Proof
  rpt gen_tac >> rpt disch_tac >>
  fs [procs_def] >>
  qpat_abbrev_tac `ss1 = agp32_next_state _ _ _` >>
  qpat_abbrev_tac `ss2 = WB_pipeline _ _ _` >>
  qpat_abbrev_tac `ss3 = MEM_pipeline _ _ _` >>
  fs [Abbr `ss3`,MEM_pipeline_unchanged_EX_pipeline_items,MEM_pipeline_unchanged_enable_flags,
      Abbr `ss2`,WB_pipeline_unchanged_EX_pipeline_items,WB_pipeline_unchanged_enable_flags,
      Abbr `ss1`,agp32_next_state_unchanged_EX_pipeline_items,agp32_next_state_unchanged_enable_flags]
QED


(* states exist to update specific items *)
(** IF_instr **)
Theorem agp32_IF_instr_exists_IF_instr_update:
  !fext fbits t.
    ?s s'. (agp32 fext fbits t).IF.IF_instr = (IF_instr_update (fext t) s s').IF.IF_instr
Proof
  rw [] >> Cases_on `t` >-
   (rw [agp32_def,mk_module_def,mk_circuit_def] >>
    clist_update_state_tac >>
    fs [Abbr `s14`,Abbr `s13`,Abbr `s12`,Abbr `s11`,Abbr `s10`,Abbr `s9`,Abbr `s8`,
        Abbr `s7`,Abbr `s6`,Abbr `s5`,Abbr `s4`,Abbr `s3`,Abbr `s2`,Abbr `s1`,
      Hazard_ctrl_unchanged_IF,WB_update_unchanged_IF,
      MEM_ctrl_update_unchanged_IF,IF_PC_input_update_unchanged_IF,
      EX_jump_sel_addr_update_unchanged_IF,EX_SHIFT_update_unchanged_IF,
      EX_ALU_update_unchanged_IF,EX_ALU_input_imm_update_unchanged_IF,
      EX_ctrl_update_unchanged_IF,ID_data_check_update_unchanged_IF,
      ID_data_update_unchanged_IF,ID_imm_update_unchanged_IF,
      ID_opc_func_update_unchanged_IF] >>
    METIS_TAC []) >>
  rw [agp32_IF_instr_updated_by_IF_instr_update]
QED

(** ID_opc and ID_func **)
Theorem agp32_ID_opc_func_exists_ID_opc_func_update:
  !fext fbits t.
    ?s s'.
      ((agp32 fext fbits t).ID.ID_opc = (ID_opc_func_update (fext t) s s').ID.ID_opc) /\
      ((agp32 fext fbits t).ID.ID_func = (ID_opc_func_update (fext t) s s').ID.ID_func)
Proof
  rw [] >> Cases_on `t` >>
  rw [agp32_def,mk_module_def,mk_circuit_def] >-
   (clist_update_state_tac >>
    fs [Abbr `s14`,Abbr `s13`,Abbr `s12`,Abbr `s11`,Abbr `s10`,Abbr `s9`,
        Abbr `s8`,Abbr `s7`,Abbr `s6`,Abbr `s5`,Abbr `s4`,Abbr `s3`,Abbr `s2`,
        Hazard_ctrl_unchanged_ID_opc_func,WB_update_unchanged_ID_opc_func,
        MEM_ctrl_update_unchanged_ID_opc_func,IF_PC_input_update_unchanged_ID_opc_func,
        EX_jump_sel_addr_update_unchanged_ID_opc_func,EX_SHIFT_update_unchanged_ID_opc_func,
        EX_ALU_update_unchanged_ID_opc_func,EX_ALU_input_imm_update_unchanged_ID_opc_func,
        EX_ctrl_update_unchanged_ID_opc_func,ID_data_check_update_unchanged_ID_opc_func,
        ID_data_update_unchanged_ID_opc_func,ID_imm_update_unchanged_ID_opc_func] >>
    METIS_TAC []) >>
  qpat_abbrev_tac `s'' = mk_circuit (procs _) (procs _) (agp32_init fbits) fext t` >>
  qpat_abbrev_tac `s''' = procs _ (fext t) s'' s''` >>
  clist_update_state_tac >>
  fs [Abbr `s14`,Abbr `s13`,Abbr `s12`,Abbr `s11`,Abbr `s10`,Abbr `s9`,
      Abbr `s8`,Abbr `s7`,Abbr `s6`,Abbr `s5`,Abbr `s4`,Abbr `s3`,Abbr `s2`,
      Hazard_ctrl_unchanged_ID_opc_func,WB_update_unchanged_ID_opc_func,
      MEM_ctrl_update_unchanged_ID_opc_func,IF_PC_input_update_unchanged_ID_opc_func,
      EX_jump_sel_addr_update_unchanged_ID_opc_func,EX_SHIFT_update_unchanged_ID_opc_func,
      EX_ALU_update_unchanged_ID_opc_func,EX_ALU_input_imm_update_unchanged_ID_opc_func,
      EX_ctrl_update_unchanged_ID_opc_func,ID_data_check_update_unchanged_ID_opc_func,
      ID_data_update_unchanged_ID_opc_func,ID_imm_update_unchanged_ID_opc_func] >>
  METIS_TAC []
QED

(** ID_opc_func_uodate is only affected by the ID_instr **)
Theorem agp32_ID_opc_func_update_same_output_under_same_ID_instr:
  !fext fext' s1 s2 s3 s4.
    s2.ID.ID_instr = s4.ID.ID_instr ==>
    (ID_opc_func_update fext s1 s2).ID.ID_opc = (ID_opc_func_update fext' s3 s4).ID.ID_opc /\
    (ID_opc_func_update fext s1 s2).ID.ID_func = (ID_opc_func_update fext' s3 s4).ID.ID_func
Proof
  rw [] >- rw [ID_opc_func_update_def] >>
  Cases_on `word_bit 24 s4.ID.ID_instr` >-
   (Cases_on `word_bit 31 s4.ID.ID_instr` >-
     fs [ID_opc_func_update_def] >>
    Cases_on `(23 >< 9) s4.ID.ID_instr = 0w` >>
    fs [ID_opc_func_update_def]) >>
  Cases_on `(5 >< 0) s4.ID.ID_instr = 10w` >-
   fs  [ID_opc_func_update_def] >>
  Cases_on `(5 >< 0) s4.ID.ID_instr = 11w` >-
   fs  [ID_opc_func_update_def] >>
  Cases_on `(5 >< 0) s4.ID.ID_instr = 12w` >-
   fs  [ID_opc_func_update_def] >>
  Cases_on `word_bit 31 s4.ID.ID_instr` >-
   fs [ID_opc_func_update_def] >>
  Cases_on `(5 >< 0) s4.ID.ID_instr <+ 10w` >-
   (fs [ID_opc_func_update_def] >>
    Cases_on `(5 >< 0) s4.ID.ID_instr = 0w \/ (5 >< 0) s4.ID.ID_instr = 6w \/
              (5 >< 0) s4.ID.ID_instr = 9w` >> fs [] >>
    Cases_on `(5 >< 0) s4.ID.ID_instr = 1w` >> fs [] >>
    Cases_on_word_value `(7 >< 6) s4.ID.ID_instr` >> rw []) >>
  fs [ID_opc_func_update_def]
QED
  

(** ID_opc_func_update rewrite**)
Theorem agp32_ID_opc_func_update_rewrite:
  !fext fbits t s.
    ((agp32 fext fbits t).ID.ID_opc = (ID_opc_func_update (fext t) s (agp32 fext fbits t)).ID.ID_opc) /\
    ((agp32 fext fbits t).ID.ID_func = (ID_opc_func_update (fext t) s (agp32 fext fbits t)).ID.ID_func)
Proof
  rpt gen_tac >> Cases_on `t` >>
  fs [agp32_def,mk_module_def,mk_circuit_def] >-
   (clist_update_state_tac >>
    subgoal `s14.ID.ID_opc = (ID_opc_func_update (fext 0)  (agp32_init fbits) s1).ID.ID_opc /\
    s14.ID.ID_func = (ID_opc_func_update (fext 0)  (agp32_init fbits) s1).ID.ID_func` >-
     (fs [Abbr `s14`,Abbr `s13`,Abbr `s12`,Abbr `s11`,Abbr `s10`,Abbr `s9`,
          Abbr `s8`,Abbr `s7`,Abbr `s6`,Abbr `s5`,Abbr `s4`,Abbr `s3`,Abbr `s2`,
          Hazard_ctrl_unchanged_ID_opc_func,WB_update_unchanged_ID_opc_func,
          MEM_ctrl_update_unchanged_ID_opc_func,IF_PC_input_update_unchanged_ID_opc_func,
          EX_jump_sel_addr_update_unchanged_ID_opc_func,EX_SHIFT_update_unchanged_ID_opc_func,
          EX_ALU_update_unchanged_ID_opc_func,EX_ALU_input_imm_update_unchanged_ID_opc_func,
          EX_ctrl_update_unchanged_ID_opc_func,ID_data_check_update_unchanged_ID_opc_func,
          ID_data_update_unchanged_ID_opc_func,ID_imm_update_unchanged_ID_opc_func]) >>
    subgoal `s1.ID.ID_instr = s14.ID.ID_instr` >-
     (fs [Abbr `s14`,Abbr `s13`,Abbr `s12`,Abbr `s11`,Abbr `s10`,Abbr `s9`,Abbr `s8`,Abbr `s7`,
          Abbr `s6`,Abbr `s5`,Abbr `s4`,Abbr `s3`,Abbr `s2`,Abbr `s1`,
          Hazard_ctrl_unchanged_ID_pipeline_items,WB_update_unchanged_ID_pipeline_items,
          MEM_ctrl_update_unchanged_ID_pipeline_items,IF_PC_input_update_unchanged_ID_pipeline_items,
          EX_jump_sel_addr_update_unchanged_ID_pipeline_items,
          EX_SHIFT_update_unchanged_ID_pipeline_items,EX_ALU_update_unchanged_ID_pipeline_items,
          EX_ALU_input_imm_update_unchanged_ID_pipeline_items,EX_ctrl_update_unchanged_ID_pipeline_items,
          ID_data_check_update_unchanged_ID_pipeline_items,ID_data_update_unchanged_ID_pipeline_items,
          ID_imm_update_unchanged_ID_pipeline_items,ID_opc_func_update_unchanged_ID_pipeline_items,
          IF_instr_update_unchanged_ID_pipeline_items]) >>
    fs [Abbr `s2`] >> METIS_TAC [agp32_ID_opc_func_update_same_output_under_same_ID_instr]) >>
  qpat_abbrev_tac `s'' = mk_circuit (procs _) (procs _) (agp32_init fbits) fext t` >>
  qpat_abbrev_tac `s''' = procs _ (fext t) s'' s''` >>
  clist_update_state_tac >>
  subgoal `s14.ID.ID_opc = (ID_opc_func_update (fext (SUC n)) s''' s1).ID.ID_opc /\
  s14.ID.ID_func = (ID_opc_func_update (fext (SUC n)) s''' s1).ID.ID_func` >-
   (fs [Abbr `s14`,Abbr `s13`,Abbr `s12`,Abbr `s11`,Abbr `s10`,Abbr `s9`,
        Abbr `s8`,Abbr `s7`,Abbr `s6`,Abbr `s5`,Abbr `s4`,Abbr `s3`,Abbr `s2`,
        Hazard_ctrl_unchanged_ID_opc_func,WB_update_unchanged_ID_opc_func,
        MEM_ctrl_update_unchanged_ID_opc_func,IF_PC_input_update_unchanged_ID_opc_func,
        EX_jump_sel_addr_update_unchanged_ID_opc_func,EX_SHIFT_update_unchanged_ID_opc_func,
        EX_ALU_update_unchanged_ID_opc_func,EX_ALU_input_imm_update_unchanged_ID_opc_func,
        EX_ctrl_update_unchanged_ID_opc_func,ID_data_check_update_unchanged_ID_opc_func,
        ID_data_update_unchanged_ID_opc_func,ID_imm_update_unchanged_ID_opc_func]) >>
  subgoal `s1.ID.ID_instr = s14.ID.ID_instr`  >-
   (fs [Abbr `s14`,Abbr `s13`,Abbr `s12`,Abbr `s11`,Abbr `s10`,Abbr `s9`,Abbr `s8`,Abbr `s7`,
        Abbr `s6`,Abbr `s5`,Abbr `s4`,Abbr `s3`,Abbr `s2`,Abbr `s1`,
        Hazard_ctrl_unchanged_ID_pipeline_items,WB_update_unchanged_ID_pipeline_items,
        MEM_ctrl_update_unchanged_ID_pipeline_items,IF_PC_input_update_unchanged_ID_pipeline_items,
        EX_jump_sel_addr_update_unchanged_ID_pipeline_items,
        EX_SHIFT_update_unchanged_ID_pipeline_items,EX_ALU_update_unchanged_ID_pipeline_items,
        EX_ALU_input_imm_update_unchanged_ID_pipeline_items,EX_ctrl_update_unchanged_ID_pipeline_items,
        ID_data_check_update_unchanged_ID_pipeline_items,ID_data_update_unchanged_ID_pipeline_items,
        ID_imm_update_unchanged_ID_pipeline_items,ID_opc_func_update_unchanged_ID_pipeline_items,
        IF_instr_update_unchanged_ID_pipeline_items]) >>
  fs [Abbr `s2`] >> METIS_TAC [agp32_ID_opc_func_update_same_output_under_same_ID_instr]
QED

(** control flags **)
Theorem agp32_ctrl_flags_exists_Hazard_ctrl:
  !fext fbits t.
    ?s s'.
      ((agp32 fext fbits t).IF.IF_PC_write_enable <=>
       (Hazard_ctrl (fext t) s s').IF.IF_PC_write_enable) /\
      ((agp32 fext fbits t).ID.ID_ID_write_enable <=>
       (Hazard_ctrl (fext t) s s').ID.ID_ID_write_enable) /\
      ((agp32 fext fbits t).ID.ID_EX_write_enable <=>
       (Hazard_ctrl (fext t) s s').ID.ID_EX_write_enable) /\
      ((agp32 fext fbits t).ID.ID_flush_flag <=>
       (Hazard_ctrl (fext t) s s').ID.ID_flush_flag) /\
      ((agp32 fext fbits t).EX.EX_NOP_flag <=>
       (Hazard_ctrl (fext t) s s').EX.EX_NOP_flag) /\
      ((agp32 fext fbits t).MEM.MEM_state_flag <=>
       (Hazard_ctrl (fext t) s s').MEM.MEM_state_flag) /\
      ((agp32 fext fbits t).MEM.MEM_NOP_flag <=>
       (Hazard_ctrl (fext t) s s').MEM.MEM_NOP_flag) /\
      ((agp32 fext fbits t).WB.WB_state_flag <=>
       (Hazard_ctrl (fext t) s s').WB.WB_state_flag)
Proof
  rw [] >> Cases_on `t` >>
  rw [agp32_def,mk_module_def,mk_circuit_def] >-
   (clist_update_state_tac >> METIS_TAC []) >>
  qpat_abbrev_tac `s'' = mk_circuit (procs _) (procs _) (agp32_init fbits) fext t` >>
  qpat_abbrev_tac `s''' = procs _ (fext t) s'' s''` >>
  clist_update_state_tac >>  METIS_TAC []
QED

(** rewrite the ID_read_data with R and ID_addr**)
Theorem agp32_ID_read_data_rewrite_R_and_ID_addr:
  !fext fbits t.
    ((agp32 fext fbits t).ID.ID_read_dataA = (agp32 fext fbits t).R (agp32 fext fbits t).ID.ID_addrA) /\
    ((agp32 fext fbits t).ID.ID_read_dataB = (agp32 fext fbits t).R (agp32 fext fbits t).ID.ID_addrB) /\
    ((agp32 fext fbits t).ID.ID_read_dataW = (agp32 fext fbits t).R (agp32 fext fbits t).ID.ID_addrW)
Proof
  rpt gen_tac >> Cases_on `t` >>
  fs [agp32_def,mk_module_def,mk_circuit_def] >-
   (clist_update_state_tac >>
    fs [Abbr `s14`,Abbr `s13`,Abbr `s12`,Abbr `s11`,Abbr `s10`,
        Abbr `s9`,Abbr `s8`,Abbr `s7`,Abbr `s6`,Abbr `s5`,Abbr `s4`,
        Hazard_ctrl_unchanged_state_items,Hazard_ctrl_unchanged_ID_data_items,
        WB_update_unchanged_state_items,WB_update_unchanged_ID_data_items,
        MEM_ctrl_update_unchanged_state_items,MEM_ctrl_update_unchanged_ID_data_items,
        IF_PC_input_update_unchanged_state_items,IF_PC_input_update_unchanged_ID_data_items,
        EX_jump_sel_addr_update_unchanged_state_items,EX_jump_sel_addr_update_unchanged_ID_data_items,
        EX_SHIFT_update_unchanged_state_items,EX_SHIFT_update_unchanged_ID_data_items,
        EX_ALU_update_unchanged_state_items,EX_ALU_update_unchanged_ID_data_items,
        EX_ALU_input_imm_update_unchanged_state_items,EX_ALU_input_imm_update_unchanged_ID_data_items,
        EX_ctrl_update_unchanged_state_items,EX_ctrl_update_unchanged_ID_data_items,
        ID_data_check_update_unchanged_state_items,ID_data_check_update_unchanged_ID_data_items] >>
    rw [ID_data_update_def]) >>
  qpat_abbrev_tac `s = mk_circuit (procs _) (procs _) (agp32_init fbits) fext _` >>
  qpat_abbrev_tac `s' = procs _ (fext t) s s` >>
  clist_update_state_tac >>
  fs [Abbr `s14`,Abbr `s13`,Abbr `s12`,Abbr `s11`,Abbr `s10`,
      Abbr `s9`,Abbr `s8`,Abbr `s7`,Abbr `s6`,Abbr `s5`,Abbr `s4`,
      Hazard_ctrl_unchanged_state_items,Hazard_ctrl_unchanged_ID_data_items,
      WB_update_unchanged_state_items,WB_update_unchanged_ID_data_items,
      MEM_ctrl_update_unchanged_state_items,MEM_ctrl_update_unchanged_ID_data_items,
      IF_PC_input_update_unchanged_state_items,IF_PC_input_update_unchanged_ID_data_items,
      EX_jump_sel_addr_update_unchanged_state_items,EX_jump_sel_addr_update_unchanged_ID_data_items,
      EX_SHIFT_update_unchanged_state_items,EX_SHIFT_update_unchanged_ID_data_items,
      EX_ALU_update_unchanged_state_items,EX_ALU_update_unchanged_ID_data_items,
      EX_ALU_input_imm_update_unchanged_state_items,EX_ALU_input_imm_update_unchanged_ID_data_items,
      EX_ctrl_update_unchanged_state_items,EX_ctrl_update_unchanged_ID_data_items,
      ID_data_check_update_unchanged_state_items,ID_data_check_update_unchanged_ID_data_items] >>
  rw [ID_data_update_def]
QED


(* lemma for correctness proof *)
(** PC is unchanged after the IF_PC_update function **)
Theorem agp32_same_PC_after_IF_PC_update:
  !fext fbits t s s'.
    s = agp32 fext fbits t ==>
    s' = procs [agp32_next_state; WB_pipeline; MEM_pipeline; EX_pipeline;
                REG_write; ID_pipeline; IF_PC_update; Acc_compute] (fext t) s s ==>
    s'.PC = (agp32 fext fbits (SUC t)).PC
Proof
  rpt STRIP_TAC >>
  Q.ABBREV_TAC `s'' = procs [agp32_next_state;WB_pipeline;MEM_pipeline;
                             EX_pipeline;REG_write;ID_pipeline] (fext t) s s` >>
  `(agp32 fext fbits (SUC t)).PC = (IF_PC_update (fext t) s s'').PC`
    by fs [Abbr `s''`,agp32_PC_updated_by_IF_PC_update] >> fs [Abbr `s''`] >>
  slist_update_state_tac >>
  fs [Abbr `ss8`,Abbr `ss7`,Acc_compute_unchanged_IF]
QED

(** EX_write_reg and EX_addrW are unchanged after the EX_pipeline function **)
Theorem agp32_same_EX_pipeline_items_after_EX_pipeline:
  !fext fbits t s s'.
    s = agp32 fext fbits t ==>
    s' = procs [agp32_next_state; WB_pipeline; MEM_pipeline; EX_pipeline;
                REG_write; ID_pipeline; IF_PC_update; Acc_compute] (fext t) s s ==>
    (s'.EX.EX_addrW = (agp32 fext fbits (SUC t)).EX.EX_addrW) /\
    (s'.EX.EX_write_reg <=> (agp32 fext fbits (SUC t)).EX.EX_write_reg) /\
    (s'.EX.EX_opc = (agp32 fext fbits (SUC t)).EX.EX_opc) /\
    (s'.EX.EX_PC = (agp32 fext fbits (SUC t)).EX.EX_PC) /\
    (s'.EX.EX_dataA = (agp32 fext fbits (SUC t)).EX.EX_dataA) /\
    (s'.EX.EX_dataB = (agp32 fext fbits (SUC t)).EX.EX_dataB)
Proof
  rpt gen_tac >> rpt disch_tac >>
  fs [agp32_def,mk_module_def,mk_circuit_def] >>
  qpat_abbrev_tac `s'' = mk_circuit (procs _) (procs _) (agp32_init fbits) fext t` >>
  qpat_abbrev_tac `s''' = procs _ (fext t) s'' s''` >>
  clist_update_state_tac >>
  fs [Abbr `s14`,Abbr `s13`,Abbr `s12`,Abbr `s11`,Abbr `s10`,Abbr `s9`,Abbr `s8`,
      Abbr `s7`,Abbr `s6`,Abbr `s5`,Abbr `s4`,Abbr `s3`,Abbr `s2`,Abbr `s1`,
      Hazard_ctrl_unchanged_EX_pipeline_items,WB_update_unchanged_EX_pipeline_items,
      MEM_ctrl_update_unchanged_EX_pipeline_items,IF_PC_input_update_unchanged_EX_pipeline_items,
      EX_jump_sel_addr_update_unchanged_EX_pipeline_items,
      EX_SHIFT_update_unchanged_EX_pipeline_items,EX_ALU_update_unchanged_EX_pipeline_items,
      EX_ALU_input_imm_update_unchanged_EX_pipeline_items,
      EX_ctrl_update_unchanged_EX_pipeline_items,ID_data_check_update_unchanged_EX_pipeline_items,
      ID_data_update_unchanged_EX_pipeline_items,ID_imm_update_unchanged_EX_pipeline_items,
      ID_opc_func_update_unchanged_EX_pipeline_items,IF_instr_update_unchanged_EX_pipeline_items]
QED

(** MEM_write_reg and MEM_addrW are unchanged after the MEM_pipeline function **)
Theorem agp32_same_MEM_pipeline_items_after_MEM_pipeline:
  !fext fbits t s s'.
    s = agp32 fext fbits t ==>
    s' = procs [agp32_next_state; WB_pipeline; MEM_pipeline; EX_pipeline;
                REG_write; ID_pipeline; IF_PC_update; Acc_compute] (fext t) s s ==>
    (s'.MEM.MEM_addrW = (agp32 fext fbits (SUC t)).MEM.MEM_addrW) /\
    (s'.MEM.MEM_write_reg <=> (agp32 fext fbits (SUC t)).MEM.MEM_write_reg)
Proof
  rpt gen_tac >> rpt disch_tac >>
  fs [agp32_def,mk_module_def,mk_circuit_def] >>
  qpat_abbrev_tac `s'' = mk_circuit (procs _) (procs _) (agp32_init fbits) fext t` >>
  qpat_abbrev_tac `s''' = procs _ (fext t) s'' s''` >>
  clist_update_state_tac >>
  fs [Abbr `s14`,Abbr `s13`,Abbr `s12`,Abbr `s11`,Abbr `s10`,Abbr `s9`,Abbr `s8`,
      Abbr `s7`,Abbr `s6`,Abbr `s5`,Abbr `s4`,Abbr `s3`,Abbr `s2`,Abbr `s1`,
      Hazard_ctrl_unchanged_MEM_pipeline_items,WB_update_unchanged_MEM_pipeline_items,
      MEM_ctrl_update_unchanged_MEM_pipeline_items,IF_PC_input_update_unchanged_MEM_pipeline_items,
      EX_jump_sel_addr_update_unchanged_MEM_pipeline_items,
      EX_SHIFT_update_unchanged_MEM_pipeline_items,EX_ALU_update_unchanged_MEM_pipeline_items,
      EX_ALU_input_imm_update_unchanged_MEM_pipeline_items,
      EX_ctrl_update_unchanged_MEM_pipeline_items,ID_data_check_update_unchanged_MEM_pipeline_items,
      ID_data_update_unchanged_MEM_pipeline_items,ID_imm_update_unchanged_MEM_pipeline_items,
      ID_opc_func_update_unchanged_MEM_pipeline_items,IF_instr_update_unchanged_MEM_pipeline_items]
QED

(** WB_write_reg and WB_addrW are unchanged after the WB_pipeline function **)
Theorem agp32_same_WB_pipeline_items_after_WB_pipeline:
  !fext fbits t s s'.
    s = agp32 fext fbits t ==>
    s' = procs [agp32_next_state; WB_pipeline; MEM_pipeline; EX_pipeline;
                REG_write; ID_pipeline; IF_PC_update; Acc_compute] (fext t) s s ==>
    (s'.WB.WB_addrW = (agp32 fext fbits (SUC t)).WB.WB_addrW) /\
    (s'.WB.WB_write_reg <=> (agp32 fext fbits (SUC t)).WB.WB_write_reg)
Proof
  rpt gen_tac >> rpt disch_tac >>
  fs [agp32_def,mk_module_def,mk_circuit_def] >>
  qpat_abbrev_tac `s'' = mk_circuit (procs _) (procs _) (agp32_init fbits) fext t` >>
  qpat_abbrev_tac `s''' = procs _ (fext t) s'' s''` >>
  clist_update_state_tac >>
  fs [Abbr `s14`,Abbr `s13`,Abbr `s12`,Abbr `s11`,Abbr `s10`,Abbr `s9`,Abbr `s8`,
      Abbr `s7`,Abbr `s6`,Abbr `s5`,Abbr `s4`,Abbr `s3`,Abbr `s2`,Abbr `s1`,
      Hazard_ctrl_unchanged_WB_pipeline_items,WB_update_unchanged_WB_pipeline_items,
      MEM_ctrl_update_unchanged_WB_pipeline_items,IF_PC_input_update_unchanged_WB_pipeline_items,
      EX_jump_sel_addr_update_unchanged_WB_pipeline_items,
      EX_SHIFT_update_unchanged_WB_pipeline_items,EX_ALU_update_unchanged_WB_pipeline_items,
      EX_ALU_input_imm_update_unchanged_WB_pipeline_items,
      EX_ctrl_update_unchanged_WB_pipeline_items,ID_data_check_update_unchanged_WB_pipeline_items,
      ID_data_update_unchanged_WB_pipeline_items,ID_imm_update_unchanged_WB_pipeline_items,
      ID_opc_func_update_unchanged_WB_pipeline_items,IF_instr_update_unchanged_WB_pipeline_items]
QED


(** ID_instr is unchanged after the ID_pipeline function **)
(** after the ID_imm_update function **)
Theorem agp32_same_ID_instr_after_ID_imm_update:
  !fext fbits t s s' s''.
    s = agp32 fext fbits t ==>
    s' = procs [agp32_next_state; WB_pipeline; MEM_pipeline; EX_pipeline;
                REG_write; ID_pipeline; IF_PC_update; Acc_compute] (fext t) s s ==>
    s'' = procs [IF_instr_update; ID_opc_func_update; ID_imm_update] (fext (SUC t)) s' s' ==>
    (agp32 fext fbits (SUC t)).ID.ID_instr = s''.ID.ID_instr
Proof
  rw [agp32_def,mk_module_def,mk_circuit_def] >>
  qpat_abbrev_tac `s = mk_circuit (procs _) (procs _) (agp32_init fbits) fext t` >>
  qpat_abbrev_tac `s0 = procs _ (fext t) s s` >>
  Q.ABBREV_TAC `s1 = procs [IF_instr_update;ID_opc_func_update;ID_imm_update] (fext (SUC t)) s0 s0` >>
  clist_update_state_tac >>
  fs [Abbr `s14`,Abbr `s13`,Abbr `s12`,Abbr `s11`,Abbr `s10`,Abbr `s9`,Abbr `s8`,
      Abbr `s7`,Abbr `s6`,Abbr `s5`,Abbr `s4`,
      Hazard_ctrl_unchanged_ID_pipeline_items,
      WB_update_unchanged_ID_pipeline_items,MEM_ctrl_update_unchanged_ID_pipeline_items,
      IF_PC_input_update_unchanged_ID_pipeline_items,
      EX_jump_sel_addr_update_unchanged_ID_pipeline_items,
      EX_SHIFT_update_unchanged_ID_pipeline_items,EX_ALU_update_unchanged_ID_pipeline_items,
      EX_ALU_input_imm_update_unchanged_ID_pipeline_items,
      EX_ctrl_update_unchanged_ID_pipeline_items,
      ID_data_check_update_unchanged_ID_pipeline_items,
      ID_data_update_unchanged_ID_pipeline_items]
QED

(** after the ID_opc_func_update function **)
Theorem agp32_same_ID_instr_after_ID_opc_func_update:
  !fext fbits t s s' s''.
    s = agp32 fext fbits t ==>
    s' = procs [agp32_next_state; WB_pipeline; MEM_pipeline; EX_pipeline;
                REG_write; ID_pipeline; IF_PC_update; Acc_compute] (fext t) s s ==>
    s'' = procs [IF_instr_update; ID_opc_func_update] (fext (SUC t)) s' s' ==>
    (agp32 fext fbits (SUC t)).ID.ID_instr = s''.ID.ID_instr
Proof
  rw [agp32_def,mk_module_def,mk_circuit_def] >>
  qpat_abbrev_tac `s = mk_circuit (procs _) (procs _) (agp32_init fbits) fext t` >>
  qpat_abbrev_tac `s0 = procs _ (fext t) s s` >>
  Q.ABBREV_TAC `s1 = procs [IF_instr_update; ID_opc_func_update] (fext (SUC t)) s0 s0` >>
  clist_update_state_tac >>
  fs [Abbr `s14`,Abbr `s13`,Abbr `s12`,Abbr `s11`,Abbr `s10`,Abbr `s9`,Abbr `s8`,
      Abbr `s7`,Abbr `s6`,Abbr `s5`,Abbr `s4`,Abbr `s3`,
      Hazard_ctrl_unchanged_ID_pipeline_items,
      WB_update_unchanged_ID_pipeline_items,MEM_ctrl_update_unchanged_ID_pipeline_items,
      IF_PC_input_update_unchanged_ID_pipeline_items,
      EX_jump_sel_addr_update_unchanged_ID_pipeline_items,
      EX_SHIFT_update_unchanged_ID_pipeline_items,EX_ALU_update_unchanged_ID_pipeline_items,
      EX_ALU_input_imm_update_unchanged_ID_pipeline_items,
      EX_ctrl_update_unchanged_ID_pipeline_items,
      ID_data_check_update_unchanged_ID_pipeline_items,
      ID_data_update_unchanged_ID_pipeline_items,
      ID_imm_update_unchanged_ID_pipeline_items]
QED

(** after the IF_instr_update function **)
Theorem agp32_same_ID_instr_after_IF_instr_update:
  !fext fbits t s s' s''.
    s = agp32 fext fbits t ==>
    s' = procs [agp32_next_state; WB_pipeline; MEM_pipeline; EX_pipeline;
                REG_write; ID_pipeline; IF_PC_update; Acc_compute] (fext t) s s ==>
    s'' = procs [IF_instr_update] (fext (SUC t)) s' s' ==>
    (agp32 fext fbits (SUC t)).ID.ID_instr = s''.ID.ID_instr
Proof
  rw [agp32_def,mk_module_def,mk_circuit_def] >>
  qpat_abbrev_tac `s = mk_circuit (procs _) (procs _) (agp32_init fbits) fext t` >>
  qpat_abbrev_tac `s0 = procs _ (fext t) s s` >>
  Q.ABBREV_TAC `s1 = procs [ForwardA; ForwardB; ForwardW; IF_instr_update] (fext (SUC t)) s0 s0` >>
  clist_update_state_tac >>
  fs [Abbr `s14`,Abbr `s13`,Abbr `s12`,Abbr `s11`,Abbr `s10`,Abbr `s9`,Abbr `s8`,
      Abbr `s7`,Abbr `s6`,Abbr `s5`,Abbr `s4`,Abbr `s3`,Abbr `s2`,
      Hazard_ctrl_unchanged_ID_pipeline_items,
      WB_update_unchanged_ID_pipeline_items,MEM_ctrl_update_unchanged_ID_pipeline_items,
      IF_PC_input_update_unchanged_ID_pipeline_items,
      EX_jump_sel_addr_update_unchanged_ID_pipeline_items,
      EX_SHIFT_update_unchanged_ID_pipeline_items,EX_ALU_update_unchanged_ID_pipeline_items,
      EX_ALU_input_imm_update_unchanged_ID_pipeline_items,
      EX_ctrl_update_unchanged_ID_pipeline_items,
      ID_data_check_update_unchanged_ID_pipeline_items,
      ID_data_update_unchanged_ID_pipeline_items,
      ID_imm_update_unchanged_ID_pipeline_items,
      ID_opc_func_update_unchanged_ID_pipeline_items]
QED


(** R is unchanged after the REG_write function **)
(** after the ID_imm_update function **)
Theorem agp32_same_R_after_ID_imm_update:
  !fext fbits t s s' s''.
    s = agp32 fext fbits t ==>
    s' = procs [agp32_next_state; WB_pipeline; MEM_pipeline; EX_pipeline;
                REG_write; ID_pipeline; IF_PC_update; Acc_compute]
               (fext t) s s ==>
    s'' = procs [IF_instr_update; ID_opc_func_update; ID_imm_update] (fext (SUC t)) s' s' ==>
    (agp32 fext fbits (SUC t)).R = s''.R
Proof
  rw [agp32_def,mk_module_def,mk_circuit_def] >>
  qpat_abbrev_tac `s = mk_circuit (procs _) (procs _) (agp32_init fbits) fext t` >>
  qpat_abbrev_tac `s0 = procs _ (fext t) s s` >>
  Q.ABBREV_TAC `s1 = procs [IF_instr_update;ID_opc_func_update;ID_imm_update] (fext (SUC t)) s0 s0` >>
  clist_update_state_tac >>
  fs [Abbr `s14`,Abbr `s13`,Abbr `s12`,Abbr `s11`,Abbr `s10`,Abbr `s9`,Abbr `s8`,
      Abbr `s7`,Abbr `s6`,Abbr `s5`,Abbr `s4`,Abbr `s3`,
      Hazard_ctrl_unchanged_state_items,
      WB_update_unchanged_state_items,MEM_ctrl_update_unchanged_state_items,
      IF_PC_input_update_unchanged_state_items,EX_jump_sel_addr_update_unchanged_state_items,
      EX_SHIFT_update_unchanged_state_items,EX_ALU_update_unchanged_state_items,
      EX_ALU_input_imm_update_unchanged_state_items,EX_ctrl_update_unchanged_state_items,
      ID_data_check_update_unchanged_state_items,ID_data_update_unchanged_state_items,
      ID_imm_update_unchanged_state_items]
QED


(** some items are unchanged after the ID_data_update function **)
Theorem agp32_same_items_after_ID_data_update:
  !fext fbits t s s' s''.
    s = agp32 fext fbits t ==>
    s' = procs [agp32_next_state; WB_pipeline; MEM_pipeline; EX_pipeline;
                REG_write; ID_pipeline; IF_PC_update; Acc_compute]
               (fext t) s s ==>
    s'' = procs [IF_instr_update; ID_opc_func_update; ID_imm_update; ID_data_update] (fext (SUC t)) s' s' ==>
    ((agp32 fext fbits (SUC t)).ID.ID_addrA = s''.ID.ID_addrA) /\
    ((agp32 fext fbits (SUC t)).ID.ID_addrB = s''.ID.ID_addrB) /\
    ((agp32 fext fbits (SUC t)).ID.ID_addrW = s''.ID.ID_addrW) /\
    ((agp32 fext fbits (SUC t)).ID.ID_addrA_disable = s''.ID.ID_addrA_disable) /\
    ((agp32 fext fbits (SUC t)).ID.ID_addrB_disable = s''.ID.ID_addrB_disable) /\
    ((agp32 fext fbits (SUC t)).ID.ID_addrW_disable = s''.ID.ID_addrW_disable) /\
    ((agp32 fext fbits (SUC t)).EX.EX_write_reg = s''.EX.EX_write_reg) /\
    ((agp32 fext fbits (SUC t)).MEM.MEM_write_reg = s''.MEM.MEM_write_reg) /\
    ((agp32 fext fbits (SUC t)).WB.WB_write_reg = s''.WB.WB_write_reg)
Proof
  rpt gen_tac >> rpt disch_tac >>
  fs [agp32_def,mk_module_def,mk_circuit_def] >>
  qpat_abbrev_tac `s''' = mk_circuit (procs _) (procs _) (agp32_init fbits) fext t` >>
  qpat_abbrev_tac `s0 = procs _ (fext t) s''' s'''` >>
  Q.ABBREV_TAC `s1 = procs [IF_instr_update; ID_opc_func_update;
                            ID_imm_update; ID_data_update] (fext (SUC t)) s0 s0` >>
  clist_update_state_tac >>
  fs [Abbr `s14`,Abbr `s13`,Abbr `s12`,Abbr `s11`,Abbr `s10`,
      Abbr `s9`,Abbr `s8`,Abbr `s7`,Abbr `s6`,Abbr `s5`,
      Hazard_ctrl_unchanged_ID_data_items,Hazard_ctrl_unchanged_EX_pipeline_items,
      Hazard_ctrl_unchanged_MEM_pipeline_items,Hazard_ctrl_unchanged_WB_pipeline_items,
      WB_update_unchanged_ID_data_items,WB_update_unchanged_EX_pipeline_items,
      WB_update_unchanged_MEM_pipeline_items,WB_update_unchanged_WB_pipeline_items,
      MEM_ctrl_update_unchanged_ID_data_items,MEM_ctrl_update_unchanged_EX_pipeline_items,
      MEM_ctrl_update_unchanged_MEM_pipeline_items,MEM_ctrl_update_unchanged_WB_pipeline_items,
      IF_PC_input_update_unchanged_ID_data_items,IF_PC_input_update_unchanged_EX_pipeline_items,
      IF_PC_input_update_unchanged_MEM_pipeline_items,IF_PC_input_update_unchanged_WB_pipeline_items,
      EX_jump_sel_addr_update_unchanged_ID_data_items,
      EX_jump_sel_addr_update_unchanged_EX_pipeline_items,
      EX_jump_sel_addr_update_unchanged_MEM_pipeline_items,
      EX_jump_sel_addr_update_unchanged_WB_pipeline_items,
      EX_SHIFT_update_unchanged_ID_data_items,EX_SHIFT_update_unchanged_EX_pipeline_items,
      EX_SHIFT_update_unchanged_MEM_pipeline_items,EX_SHIFT_update_unchanged_WB_pipeline_items,
      EX_ALU_update_unchanged_ID_data_items,EX_ALU_update_unchanged_EX_pipeline_items,
      EX_ALU_update_unchanged_MEM_pipeline_items,EX_ALU_update_unchanged_WB_pipeline_items,
      EX_ALU_input_imm_update_unchanged_ID_data_items,
      EX_ALU_input_imm_update_unchanged_EX_pipeline_items,
      EX_ALU_input_imm_update_unchanged_MEM_pipeline_items,
      EX_ALU_input_imm_update_unchanged_WB_pipeline_items,
      EX_ctrl_update_unchanged_ID_data_items,EX_ctrl_update_unchanged_EX_pipeline_items,
      EX_ctrl_update_unchanged_MEM_pipeline_items,EX_ctrl_update_unchanged_WB_pipeline_items,
      ID_data_check_update_unchanged_ID_data_items,
      ID_data_check_update_unchanged_EX_pipeline_items,
      ID_data_check_update_unchanged_MEM_pipeline_items,
      ID_data_check_update_unchanged_WB_pipeline_items]
QED

(** some items are unchanged after the EX_ctrl_update function **)
Theorem agp32_same_items_after_EX_ctrl_update:
  !fext fbits t s s' s''.
    s = agp32 fext fbits t ==>
    s' = procs [agp32_next_state; WB_pipeline; MEM_pipeline; EX_pipeline;
                REG_write; ID_pipeline; IF_PC_update; Acc_compute] (fext t) s s ==>
    s'' = procs [IF_instr_update; ID_opc_func_update; ID_imm_update; 
                 ID_data_update; ID_data_check_update; EX_ctrl_update] (fext (SUC t)) s' s' ==>
    ((agp32 fext fbits (SUC t)).EX.EX_imm = s''.EX.EX_imm) /\
    ((agp32 fext fbits (SUC t)).EX.EX_dataW = s''.EX.EX_dataW)
Proof
  rpt gen_tac >> rpt disch_tac >>
  fs [agp32_def,mk_module_def,mk_circuit_def] >>
  qpat_abbrev_tac `s''' = mk_circuit (procs _) (procs _) (agp32_init fbits) fext t` >>
  qpat_abbrev_tac `s0 = procs _ (fext t) s''' s'''` >>
  Q.ABBREV_TAC `s1 = procs [IF_instr_update;ID_opc_func_update;ID_imm_update;
                            ID_data_update;ID_data_check_update;EX_ctrl_update] (fext (SUC t)) s0 s0` >>
  clist_update_state_tac >>
  fs [Abbr `s14`,Abbr `s13`,Abbr `s12`,Abbr `s11`,Abbr `s10`,Abbr `s9`,Abbr `s8`,Abbr `s7`,
      Hazard_ctrl_unchanged_EX_pipeline_items,WB_update_unchanged_EX_pipeline_items,
      MEM_ctrl_update_unchanged_EX_pipeline_items,IF_PC_input_update_unchanged_EX_pipeline_items,
      EX_jump_sel_addr_update_unchanged_EX_pipeline_items,EX_SHIFT_update_unchanged_EX_pipeline_items,
      EX_ALU_update_unchanged_EX_pipeline_items,EX_ALU_input_imm_update_unchanged_EX_pipeline_items]
QED

val _ = export_theory ();
