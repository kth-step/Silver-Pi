open hardwarePreamble translatorTheory translatorLib arithmeticTheory dep_rewrite blastLib bitstringSyntax fcpSyntax listSyntax wordsSyntax agp32StateTheory agp32EnvironmentTheory agp32ProcessorTheory ag32Theory ag32ExtraTheory ag32UtilitiesTheory agp32RelationTheory agp32UpdateTheory agp32InternalTheory agp32StepLib agp32SpecialTheory agp32_IF_CorrectTheory agp32_ID_CorrectTheory agp32_EX_CorrectTheory agp32_EX_Flags_CorrectTheory agp32_MEM_CorrectTheory agp32_MEM_Data_CorrectTheory agp32_WB_CorrectTheory;

(* correctness of the pipelined circuit with respect to the ISA *)
val _ = new_theory "agp32Correct";

val _ = prefer_num ();
val _ = guess_lengths ();


(* Init relation implies Rel at cycle 0 *)
Theorem agp32_Init_implies_Rel:
  !fext fbits s a I.
    s = agp32 fext fbits ==>
    is_sch_init I ==>
    Init (fext 0) (s 0) a ==>
    Rel I (fext 0) (s 0) (s 0) a 0
Proof
  rw [Init_def,Rel_def,is_sch_init_def] >>
  fs [agp32_init_IF_PC_input,agp32_init_EX_opc,IF_PC_Rel_def,IF_instr_Rel_def,
      Inv_Rel_def,enable_stg_def,EX_Rel_spec_def,isJump_isa_op_def] >> fs [] >>
  rw [agp32_init_ID_opc,agp32_init_EX_opc,agp32_init_EX_write_reg,
      agp32_init_MEM_opc,agp32_init_MEM_write_reg,agp32_init_WB_opc,
      agp32_init_WB_write_reg,agp32_init_WB_isOut] >>
  `a.data_in = (FUNPOW Next 0 a).data_in` by rw [] >>
  METIS_TAC [ag32_data_in_unchanged_all]
QED


(* correctness of the pipelined circuit with the ISA *)
Theorem agp32_Rel_ag32_correct:
  !fext fbits s a t I.
    s = agp32 fext fbits ==>
    SC_self_mod_isa a ==>
    is_mem fext_accessor_circuit s fext ==>
    is_acc accelerator_f s ==>
    is_interrupt_interface fext_accessor_circuit s fext ==>
    is_data_in fext ==>
    is_sch I s a ==>
    Init (fext 0) (s 0) a ==>
    Rel I (fext t) (s (t-1)) (s t) a t
Proof
  Induct_on `t` >>
  rpt strip_tac >-
   (SIMP_TAC std_ss [] >> METIS_TAC [agp32_Init_implies_Rel,is_sch_def]) >>
  `Rel I' (fext t) (s (t-1)) (s t) a t` by METIS_TAC [] >>
  rw [Rel_def] >-
   (** data_in **)
   METIS_TAC [agp32_Rel_ag32_data_in_correct] >-
   (** carryflag **)
   fs [agp32_Rel_ag32_EX_ALU_carry_flag_correct] >-
   fs [agp32_Rel_ag32_EX_ALU_flags_correct_ID_not_NONE] >-
   fs [agp32_Rel_ag32_EX_ALU_flags_correct_IF_not_NONE] >-
   (** overflow flag **)
   fs [agp32_Rel_ag32_EX_ALU_overflow_flag_correct] >-
   fs [agp32_Rel_ag32_EX_ALU_flags_correct_ID_not_NONE] >-
   fs [agp32_Rel_ag32_EX_ALU_flags_correct_IF_not_NONE] >-
   (** PC_input when jump **)
   fs [is_sch_def,agp32_Rel_ag32_IF_PC_input_jump_correct] >-
   (** PC_input when no jump **)
   fs [agp32_Rel_ag32_IF_PC_input_not_jump_correct] >-
   (** memory under different conditions **)
   METIS_TAC [agp32_Rel_ag32_fext_MEM_correct_WB_not_NONE] >-
   METIS_TAC [agp32_Rel_ag32_fext_MEM_correct_WB_not_NONE_extra] >-
   METIS_TAC [agp32_Rel_ag32_fext_MEM_correct_MEM_not_NONE] >-
   METIS_TAC [agp32_Rel_ag32_fext_MEM_correct_EX_not_NONE] >-
   METIS_TAC [agp32_Rel_ag32_fext_MEM_correct_ID_not_NONE] >-
   METIS_TAC [agp32_Rel_ag32_fext_MEM_correct_IF_not_NONE] >-
   (** fext not ready, fetch disabled **)
   fs [enable_stg_def,not_fext_ready_and_agp32_IF_PC_write_disable] >-
   (** fext not ready, decode disabled **)
   (rw [enable_stg_def] >> METIS_TAC [agp32_ID_ID_write_enable_and_fext_ready]) >-
   (** register data hazard and decode **)
   fs [enable_stg_def,agp32_not_EX_jump_sel_reg_data_hazard_then_ID_ID_write_disable] >-
   (** memory stage op and ex stage **)
   fs [enable_stg_def,MEM_stg_op_agp32_ID_EX_write_disable] >-
   (** data_out **)
   fs [agp32_Rel_ag32_data_out_correct_WB_t] >-
   fs [agp32_Rel_ag32_data_out_correct_WB_SUC_t] >-
   fs [agp32_Rel_ag32_data_out_correct_MEM] >-
   fs [agp32_Rel_ag32_data_out_correct_EX] >-
   fs [agp32_Rel_ag32_data_out_correct_ID] >-
   fs [agp32_Rel_ag32_data_out_correct_IF] >-
   (** registers **)
   fs [agp32_Rel_ag32_R_correct_WB_t_valid_data] >-
   fs [agp32_Rel_ag32_R_correct_WB_t_invalid_data] >-
   fs [agp32_Rel_ag32_R_correct_WB_SUC_t] >-
   fs [agp32_Rel_ag32_R_correct_MEM] >-
   fs [agp32_Rel_ag32_R_correct_EX] >-
   fs [agp32_Rel_ag32_R_correct_ID] >-
   fs [agp32_Rel_ag32_R_correct_IF] >-
   (** Inv_Rel **)
   fs [agp32_Rel_ag32_Inv_Rel_correct] >-
   (** IF_PC **)
   fs [agp32_Rel_ag32_IF_PC_Rel_correct] >-
   (** IF_instr **)
   fs [agp32_Rel_ag32_IF_instr_Rel_correct] >-
   (** ID **)
   fs [is_sch_def,agp32_Rel_ag32_ID_Rel_correct] >-
   fs [agp32_Rel_ag32_ID_data_dep_Rel_correct] >-
   fs [agp32_Rel_ag32_ID_reg_data_Rel_correct] >-
   (** EX **)
   fs [agp32_Rel_ag32_EX_Rel_correct] >-
   fs [agp32_Rel_ag32_EX_Rel_spec_correct] >-
   fs [Rel_def,EX_Rel_spec_def] >-
   (** MEM **)
   fs [agp32_Rel_ag32_MEM_Rel_correct] >-
   fs [agp32_Rel_ag32_MEM_req_rel_correct] >-
   fs [agp32_Rel_ag32_MEM_data_rel_correct] >>
  (** WB **)
  fs [agp32_Rel_ag32_WB_Rel_correct]
QED

val _ = export_theory ();
