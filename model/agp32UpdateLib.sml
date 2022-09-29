structure agp32UpdateLib =
struct

open hardwarePreamble translatorTheory agp32ProcessorTheory;

(* tactic abbreviation to update the pipeline circuit state *)
val  clist_update_state_tac =
 (fs [Once procs_def] >>
  qpat_abbrev_tac `s1 = ForwardA _ _ _` >>
  fs [Once procs_def] >>
  qpat_abbrev_tac `s2 = ForwardB _ _ _` >>
  fs [Once procs_def] >>
  qpat_abbrev_tac `s3 = ForwardW _ _ _` >>
  fs [Once procs_def] >>
  qpat_abbrev_tac `s4 = IF_instr_update _ _ _` >>
  fs [Once procs_def] >>
  qpat_abbrev_tac `s5 = WB_update _ _ _` >>
  fs [Once procs_def] >>  
  qpat_abbrev_tac `s6 = ID_opc_func_update _ _ _` >>
  fs [Once procs_def] >>
  qpat_abbrev_tac `s7 = ID_imm_update _ _ _` >>
  fs [Once procs_def] >>
  qpat_abbrev_tac `s8 = ID_data_update _ _ _` >>
  fs [Once procs_def] >>
  qpat_abbrev_tac `s9 = MEM_imm_update _ _ _` >>
  fs [Once procs_def] >>
  qpat_abbrev_tac `s10 = EX_ctrl_update _ _ _` >>
  fs [Once procs_def] >>
  qpat_abbrev_tac `s11 = EX_forward_data _ _ _` >>
  fs [Once procs_def] >>
  qpat_abbrev_tac `s12 = EX_ALU_input_update _ _ _` >>
  fs [Once procs_def] >>
  qpat_abbrev_tac `s13 = EX_compute_enable_update _ _ _` >>
  fs [Once procs_def] >>
  qpat_abbrev_tac `s14 = EX_ALU_update _ _ _` >>
  fs [Once procs_def] >>
  qpat_abbrev_tac `s15 = EX_SHIFT_update _ _ _` >>
  fs [Once procs_def] >>
  qpat_abbrev_tac `s16 = EX_jump_sel_addr_update _ _ _` >>
  fs [Once procs_def] >>
  qpat_abbrev_tac `s17 = EX_data_rec_update _ _ _` >>
  fs [Once procs_def] >>
  qpat_abbrev_tac `s18 = IF_PC_input_update _ _ _` >>
  fs [Once procs_def] >>
  qpat_abbrev_tac `s19 = MEM_ctrl_update _ _ _` >>
  fs [procs_def] >>
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
  qpat_abbrev_tac `s5 = WB_update _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s6 = ID_opc_func_update _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s7 = ID_imm_update _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s8 = ID_data_update _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s9 = MEM_imm_update _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s10 = EX_ctrl_update _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s11 = EX_forward_data _ _ _` >>
  rw [Once procs_def] >>
  qpat_abbrev_tac `s12 = EX_ALU_input_update _ _ _` >>
  rw [procs_def] >>
  qpat_abbrev_tac `s13 = EX_compute_enable_update _ _ _`);

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

end
