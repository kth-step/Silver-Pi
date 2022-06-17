open hardwarePreamble translatorTheory translatorLib arithmeticTheory dep_rewrite blastLib bitstringSyntax fcpSyntax listSyntax wordsSyntax agp32StateTheory agp32EnvironmentTheory agp32ProcessorTheory ag32Theory ag32ExtraTheory ag32UtilitiesTheory agp32RelationTheory agp32UpdateTheory agp32InternalTheory;

val _ = new_theory "agp32Correct";

(* Special variables used in theorems:
   I: scheduling function.
   C: cache oracle.
 *)

val _ = prefer_num ();
val _ = guess_lengths ();

(* Init relation implies Rel at cycle 0 *)
Theorem agp32_Init_implies_Rel:
  !fext fbits s a I.
    s = agp32 fext fbits ==>
    (!k.I(k,0) = 0) ==>
    Init (fext 0) (s 0) a ==>
    Rel I (fext 0) (s 0) a 0
Proof
  rpt strip_tac >>
  fs [Init_def,Rel_def] >> rw [] >-
   cheat >>
  fs [enable_stg_def] >> fs []
QED

(* carry_flag between ISA and circuit states *)
Theorem agp32_Rel_ag32_carry_flag_correct:
  !fext fbits s a t I.
    (!t k. enable_stg k (agp32 fext fbits t) ==> I (k,SUC t) = I (k,t) + 1) ==>
    Rel I (fext t) (agp32 fext fbits t) a t ==>
    ((agp32 fext fbits (SUC t)).EX.EX_carry_flag <=>
     (FUNPOW Next (I (3,SUC t)) a).CarryFlag)
Proof
  rw [] >> Cases_on `enable_stg 3 (agp32 fext fbits t)` >-
   (** EX stage is enabled **)
   (`I'(3,SUC t) = SUC (I'(3,t))` by fs [] >>
    rw [FUNPOW_SUC] >>
    Q.ABBREV_TAC `ai = FUNPOW Next (I' (3,t)) a` >>             
    rw [Next_def,GSYM word_at_addr_def,GSYM align_addr_def] >>
    Cases_on `Decode (word_at_addr ai.MEM (align_addr ai.PC))` >-
     ((** Accelerator **)
     PairCases_on `p` >> rw [Run_def,dfn'Accelerator_def,incPC_def] >>
     Q.ABBREV_TAC `s = agp32 fext fbits t` >>
     Q.ABBREV_TAC `s' = procs [agp32_next_state;WB_pipeline;MEM_pipeline;EX_pipeline;
                               REG_write;ID_pipeline;IF_PC_update;Acc_compute]
                              (fext t) s s` >>
     Q.ABBREV_TAC `s'' = procs [Hazard_ctrl;ForwardA;ForwardB;ForwardW;IF_instr_update;
                                IF_PC_input_update;ID_opc_func_update;ID_imm_update;
                                ID_data_update;EX_ctrl_update;EX_forward_data;
                                EX_ALU_input_update;EX_compute_enable_update]
                               (fext (SUC t)) s' s'` >>                        
     `(agp32 fext fbits (SUC t)).EX.EX_carry_flag =
     (EX_ALU_update (fext (SUC t)) s' s'').EX.EX_carry_flag`
       by fs [agp32_EX_ALU_items_updated_by_EX_ALU_update,Abbr `s`,Abbr `s'`,Abbr `s''`] >> rw [] >>
     `opc ai = 8w` by fs [ag32_Decode_Acc_opc_8w] >>
     `(agp32 fext fbits (SUC t)).EX.EX_opc = 8w` by cheat >>
     `(s''.EX.EX_opc = 8w) /\ (s''.EX.EX_func = (agp32 fext fbits (SUC t)).EX.EX_func)`
       by METIS_TAC [agp32_same_EX_opc_func_until_ALU_update,Abbr `s`,Abbr `s'`,Abbr `s''`] >>
     `(s''.EX.EX_func = 9w) \/ (s''.EX.EX_func = 12w) \/ (s''.EX.EX_func = 13w) \/
     (s''.EX.EX_func = 14w) \/ (s''.EX.EX_func = 15w)`
       by fs [Abbr `s`,agp32_EX_opc_implies_EX_func] >> 
     `s''.EX.EX_carry_flag = s.EX.EX_carry_flag` 
      by METIS_TAC [agp32_same_EX_carry_flag_as_before,Abbr `s`,Abbr `s'`,Abbr `s''`]>>
     rw [EX_ALU_update_def] >> fs [Rel_def,Abbr `s`]) >-
     ((** In **)
     rw [Run_def,dfn'In_def,incPC_def] >>
     Q.ABBREV_TAC `s = agp32 fext fbits t` >>
     Q.ABBREV_TAC `s' = procs [agp32_next_state;WB_pipeline;MEM_pipeline;EX_pipeline;
                               REG_write;ID_pipeline;IF_PC_update;Acc_compute]
                              (fext t) s s` >>
     Q.ABBREV_TAC `s'' = procs [Hazard_ctrl;ForwardA;ForwardB;ForwardW;IF_instr_update;
                                IF_PC_input_update;ID_opc_func_update;ID_imm_update;
                                ID_data_update;EX_ctrl_update;EX_forward_data;
                                EX_ALU_input_update;EX_compute_enable_update]
                               (fext (SUC t)) s' s'` >>                        
     `(agp32 fext fbits (SUC t)).EX.EX_carry_flag =
     (EX_ALU_update (fext (SUC t)) s' s'').EX.EX_carry_flag`
       by fs [agp32_EX_ALU_items_updated_by_EX_ALU_update,Abbr `s`,Abbr `s'`,Abbr `s''`] >> rw [] >>
     `opc ai = 7w` by fs [ag32_Decode_In_opc_7w] >>
     `(agp32 fext fbits (SUC t)).EX.EX_opc = 7w` by cheat >>
     `(s''.EX.EX_opc = 7w) /\ (s''.EX.EX_func = (agp32 fext fbits (SUC t)).EX.EX_func)`
       by METIS_TAC [agp32_same_EX_opc_func_until_ALU_update,Abbr `s`,Abbr `s'`,Abbr `s''`] >>
     `(s''.EX.EX_func = 9w) \/ (s''.EX.EX_func = 12w) \/ (s''.EX.EX_func = 13w) \/
     (s''.EX.EX_func = 14w) \/ (s''.EX.EX_func = 15w)`
       by fs [Abbr `s`,agp32_EX_opc_implies_EX_func] >> 
     `s''.EX.EX_carry_flag = s.EX.EX_carry_flag` 
      by METIS_TAC [agp32_same_EX_carry_flag_as_before,Abbr `s`,Abbr `s'`,Abbr `s''`]>>
     rw [EX_ALU_update_def] >> fs [Rel_def,Abbr `s`]) >>
    cheat) >>
  (** EX stage is disabled **)
  fs [enable_stg_def] >> cheat
QED

(* correctness of the pipelined Silver concerning the ISA *)
Theorem agp32_Rel_ag32_correct:
  !fext fbits s a (t:num) I C.
    s = agp32 fext fbits ==>
    (!t. SC_self_mod (s t)) ==>
    is_mem fext_accessor_circuit s fext ==>
    is_acc accelerator_f s ==>
    is_interrupt_interface fext_accessor_circuit s fext ==>
    is_data_in fext ==>
    (* cache oracle can introduce hit/miss *)
    (!t. C (s t).data_addr (s t).data_wstrb (s t).data_wdata (s t).command (s t).PC
         <=> (fext t).ready) ==>
    Init (fext 0) (s 0) a ==>
    (** properties of scheduling function I **)
    (!k.I(k,0) = 0) ==>
    (!t k. enable_stg k (s t) ==> I(k,SUC t) = I(k,t) + 1) ==>
    Rel I (fext t) (s t) a t
Proof
  Induct_on `t` >>
  rpt strip_tac >-
   METIS_TAC [agp32_Init_implies_Rel] >>
  `Rel I' (fext t) (s t) a t` by METIS_TAC [] >>
  rw [Rel_def] >-
   (* visible signals *)
   (** data_in **)
   fs [Rel_def,is_data_in_def,ag32_data_in_unchanged_all] >-
   (** carryflag **)
   fs [agp32_Rel_ag32_carry_flag_correct] >-
   (** overflow flag **)
   cheat >-
   (** PC when jump **)
   cheat >-
   (** PC when no jump **)
   cheat >-
   (** memory **)
   cheat >-
   (** data_out **)
   cheat >-
   (** registers **)
   cheat >-
   (** invisiable regs in IF **)
   (rw [IF_Rel_def] >-
    (** IF_instr when memory is ready **)
    (`?s s'. (agp32 fext fbits (SUC t)).IF.IF_instr =
     (IF_instr_update (fext (SUC t)) s s').IF.IF_instr`
       by rw [agp32_IF_instr_updated_by_IF_instr_update] >>
     rw [IF_instr_update_def,instr_def] >> cheat) >>
    (** IF_instr when not ready **)
    cheat) >>
  cheat         
QED

val _ = export_theory ();
