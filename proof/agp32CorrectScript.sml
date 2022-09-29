open hardwarePreamble translatorTheory translatorLib arithmeticTheory dep_rewrite blastLib bitstringSyntax fcpSyntax listSyntax wordsSyntax agp32StateTheory agp32EnvironmentTheory agp32ProcessorTheory ag32Theory ag32ExtraTheory ag32UtilitiesTheory agp32RelationTheory agp32UpdateTheory agp32InternalTheory agp32StepLib agp32_IF_CorrectTheory agp32_ID_CorrectTheory agp32_EX_CorrectTheory agp32_WB_CorrectTheory;

(* correctness of the pipelined Silver circuit against the ISA *)
val _ = new_theory "agp32Correct";

val _ = prefer_num ();
val _ = guess_lengths ();


(* lemma *)
Theorem agp32_data_in_unchanged_all:
  !fext t.
    is_data_in fext ==>
    (fext t).data_in = (fext 0).data_in
Proof
  rw [is_data_in_def] >>
  Induct_on `t` >> fs []
QED


(* Init relation implies Rel at cycle 0 *)
Theorem agp32_Init_implies_Rel:
  !fext fbits s a I.
    s = agp32 fext fbits ==>
    is_sch_init I ==>
    Init (fext 0) (s 0) a ==>
    Rel I (fext 0) (s 0) (s 0) a 0
Proof
  rw [Init_def,Rel_def,is_sch_init_def] >>
  fs [agp32_init_IF_PC_input,IF_PC_Rel_def,IF_instr_Rel_def,
      enable_stg_def,reg_data_vaild_def] >> fs []
QED


(* correctness of the pipelined Silver concerning the ISA *)
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
   (fs [agp32_data_in_unchanged_all,Init_def] >>
    `a.data_in = (FUNPOW Next 0 a).data_in` by rw [] >>
    METIS_TAC [ag32_data_in_unchanged_all]) >-
   (** carryflag **)
   (*METIS_TAC [agp32_Rel_ag32_carry_flag_correct]*)
   cheat >-
   (** overflow flag **)
   cheat >-
   (** PC_input when jump **)
   fs [is_sch_def,agp32_Rel_ag32_IF_PC_input_jump_correct] >-
   (** PC_input when no jump **)
   fs [is_sch_def,agp32_Rel_ag32_IF_PC_input_not_jump_correct] >-
   (** memory under different conditions **)
   cheat >-
   cheat >-
   cheat >-
   cheat >-
   (** fext not ready, fetch disabled **)
   fs [enable_stg_def,not_fext_ready_and_agp32_IF_PC_write_disable] >-
   (** fext not ready, decode disabled **)
   (rw [enable_stg_def] >> METIS_TAC [agp32_ID_ID_write_enable_and_fext_ready]) >-
   (** memory stage op and ex stage **)
   fs [enable_stg_def,MEM_stg_op_agp32_ID_EX_write_disable] >-
   (** data_out **)
   cheat >-
   (** registers **)
   fs [agp32_Rel_ag32_R_correct] >-
   cheat >-
   cheat >-
   cheat >-
   cheat >-
   (** IF_PC **)
   fs [is_sch_def,agp32_Rel_ag32_IF_PC_Rel_correct] >-
   (** IF_instr **)
   fs [agp32_Rel_ag32_IF_instr_Rel_correct] >-
   (** ID **)
   fs [is_sch_def,agp32_Rel_ag32_ID_Rel_correct] >-
   fs [agp32_Rel_ag32_ID_Forward_Rel_correct] >-
   (** ID_reg_data **)
   cheat >-
   (** EX_Rel **)
   fs [is_sch_def,agp32_Rel_ag32_EX_Rel_correct] >-
   (** EX_Rel_spec **)
   cheat >-
   (** MEM **)
   cheat >>
  (** WB **)
  cheat
QED

val _ = export_theory ();
