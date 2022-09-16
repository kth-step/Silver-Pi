open hardwarePreamble translatorTheory arithmeticTheory dep_rewrite blastLib bitstringSyntax fcpSyntax listSyntax wordsSyntax wordsLib agp32StateTheory agp32EnvironmentTheory agp32ProcessorTheory agp32RelationTheory agp32UpdateTheory agp32UpdateLib;

val _ = new_theory "agp32Internal";

val _ = prefer_num ();
val _ = guess_lengths ();


(** option from the ISA functions  **)
Theorem isJump_isa_op_not_none:
  !nop a.
    isJump_isa_op nop a ==> nop <> NONE
Proof
  rw [isJump_isa_op_def]
QED


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

(** relation between ID addr_disable imm and data singals **)
Theorem agp32_ID_addrA_disable_dataA_immA:
  !fext fbits t.
    (agp32 fext fbits (SUC t)).ID.ID_addrA_disable ==>
    (agp32 fext fbits (SUC t)).ID.ID_dataA = (agp32 fext fbits (SUC t)).ID.ID_immA
Proof
  rw [] >> Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state; WB_pipeline; MEM_pipeline; EX_pipeline;
                            REG_write; ID_pipeline; IF_PC_update; Acc_compute] (fext t) s s` >>
  Q.ABBREV_TAC `s'' = procs [ForwardA; ForwardB; ForwardW; IF_instr_update;
                             ID_opc_func_update; ID_imm_update] (fext (SUC t)) s' s'` >>
  `((agp32 fext fbits (SUC t)).ID.ID_addrA_disable <=>
  (ID_data_update (fext (SUC t)) s' s'').ID.ID_addrA_disable) /\
  ((agp32 fext fbits (SUC t)).ID.ID_immA = (ID_data_update (fext (SUC t)) s' s'').ID.ID_immA) /\
  ((agp32 fext fbits (SUC t)).ID.ID_dataA = (ID_data_update (fext (SUC t)) s' s'').ID.ID_dataA)`
    by fs [Abbr `s`,Abbr `s'`,Abbr `s''`,agp32_ID_flag_updated_by_ID_data_update,
           agp32_ID_imm_data_updated_by_ID_data_update,agp32_ID_data_updated_by_ID_data_update] >>
  fs [ID_data_update_def,MUX_21_def]
QED

Theorem agp32_ID_addrB_disable_dataB_immB:
  !fext fbits t.
    (agp32 fext fbits (SUC t)).ID.ID_addrB_disable ==>
    (agp32 fext fbits (SUC t)).ID.ID_dataB = (agp32 fext fbits (SUC t)).ID.ID_immB
Proof
  rw [] >> Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state; WB_pipeline; MEM_pipeline; EX_pipeline;
                            REG_write; ID_pipeline; IF_PC_update; Acc_compute] (fext t) s s` >>
  Q.ABBREV_TAC `s'' = procs [ForwardA; ForwardB; ForwardW; IF_instr_update;
                             ID_opc_func_update; ID_imm_update] (fext (SUC t)) s' s'` >>
  `((agp32 fext fbits (SUC t)).ID.ID_addrB_disable <=>
  (ID_data_update (fext (SUC t)) s' s'').ID.ID_addrB_disable) /\
  ((agp32 fext fbits (SUC t)).ID.ID_immB = (ID_data_update (fext (SUC t)) s' s'').ID.ID_immB) /\
  ((agp32 fext fbits (SUC t)).ID.ID_dataB = (ID_data_update (fext (SUC t)) s' s'').ID.ID_dataB)`
    by fs [Abbr `s`,Abbr `s'`,Abbr `s''`,agp32_ID_flag_updated_by_ID_data_update,
           agp32_ID_imm_data_updated_by_ID_data_update,agp32_ID_data_updated_by_ID_data_update] >>
  fs [ID_data_update_def,MUX_21_def]
QED

Theorem agp32_ID_addrW_disable_dataW_immW:
  !fext fbits t.
    (agp32 fext fbits (SUC t)).ID.ID_addrW_disable ==>
    (agp32 fext fbits (SUC t)).ID.ID_dataW = (agp32 fext fbits (SUC t)).ID.ID_immW
Proof
  rw [] >> Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state; WB_pipeline; MEM_pipeline; EX_pipeline;
                            REG_write; ID_pipeline; IF_PC_update; Acc_compute] (fext t) s s` >>
  Q.ABBREV_TAC `s'' = procs [ForwardA; ForwardB; ForwardW; IF_instr_update;
                             ID_opc_func_update; ID_imm_update] (fext (SUC t)) s' s'` >>
  `((agp32 fext fbits (SUC t)).ID.ID_addrW_disable <=>
  (ID_data_update (fext (SUC t)) s' s'').ID.ID_addrW_disable) /\
  ((agp32 fext fbits (SUC t)).ID.ID_immW = (ID_data_update (fext (SUC t)) s' s'').ID.ID_immW) /\
  ((agp32 fext fbits (SUC t)).ID.ID_dataW = (ID_data_update (fext (SUC t)) s' s'').ID.ID_dataW)`
    by fs [Abbr `s`,Abbr `s'`,Abbr `s''`,agp32_ID_flag_updated_by_ID_data_update,
           agp32_ID_imm_data_updated_by_ID_data_update,agp32_ID_data_updated_by_ID_data_update] >>
  fs [ID_data_update_def,MUX_21_def]
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


(** pipeline control flags **)
(* IF_PC_write_enable and EX_enable/MEM_state_flag *)
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

(** IF_PC_write_enable and EX_isAcc **)
Theorem agp32_IF_PC_write_enable_and_EX_isAcc:
  !fext fbits t.
    (agp32 fext fbits t).IF.IF_PC_write_enable ==>
    ~(agp32 fext fbits t).EX.EX_isAcc
Proof
  rw [] >> Cases_on `t` >>
  fs [agp32_def,mk_module_def,mk_circuit_def] >-
   (clist_update_state_tac >>
    fs [Abbr `s20`,Hazard_ctrl_def] >>
    Cases_on `s19.state = 3w \/ s19.state = 5w` >> fs [] >>
    Cases_on `s19.state = 1w \/ s19.state = 2w \/ s19.state = 4w \/ s19.state = 6w` >> fs [] >>
    Cases_on `(fext 0).ready` >> fs [] >>
    Cases_on `(agp32_init fbits).MEM.MEM_opc = 2w \/ (agp32_init fbits).MEM.MEM_opc = 3w \/
              (agp32_init fbits).MEM.MEM_opc = 4w \/ (agp32_init fbits).MEM.MEM_opc = 5w \/      
              (agp32_init fbits).MEM.MEM_opc = 12w` >> fs [] >>
    Cases_on `s19.EX.EX_isAcc` >> fs [] >>
    Cases_on `s19.EX.EX_jump_sel` >> fs []) >>
  qpat_abbrev_tac `s' = mk_circuit (procs _) (procs _) (agp32_init fbits) fext t` >>
  qpat_abbrev_tac `s'' = procs _ (fext t) s' s'` >>
  clist_update_state_tac >>
  fs [Abbr `s20`,Hazard_ctrl_def] >>
  Cases_on `s19.state = 3w \/ s19.state = 5w` >> fs [] >>
  Cases_on `s19.state = 1w \/ s19.state = 2w \/ s19.state = 4w \/ s19.state = 6w` >> fs [] >>
  Cases_on `(fext (SUC n)).ready` >> fs [] >>
  Cases_on `s''.MEM.MEM_opc = 2w \/ s''.MEM.MEM_opc = 3w \/ s''.MEM.MEM_opc = 4w \/
            s''.MEM.MEM_opc = 5w \/ s''.MEM.MEM_opc = 12w` >> fs [] >>
  Cases_on `s19.EX.EX_isAcc` >> fs [] >>
  Cases_on `s19.EX.EX_jump_sel` >> fs []      
QED

(** IF_PC_write_enable and state **)
Theorem agp32_IF_PC_write_enable_and_state:
  !fext fbits t.
    (agp32 fext fbits t).IF.IF_PC_write_enable ==>
    ((agp32 fext fbits t).state <> 1w) /\
    ((agp32 fext fbits t).state <> 2w) /\
    ((agp32 fext fbits t).state <> 3w) /\
    ((agp32 fext fbits t).state <> 4w) /\
    ((agp32 fext fbits t).state <> 5w) /\
    ((agp32 fext fbits t).state <> 6w)
Proof
  rpt GEN_TAC >> STRIP_TAC >> Cases_on `t` >>
  fs [agp32_def,mk_module_def,mk_circuit_def] >-
   (clist_update_state_tac >>
    fs [Abbr `s20`,Hazard_ctrl_def] >>
    Cases_on `s19.state = 3w \/ s19.state = 5w` >> fs [] >>
    Cases_on `s19.state = 1w \/ s19.state = 2w \/ s19.state = 4w \/ s19.state = 6w` >> fs [] >>
    Cases_on `(fext 0).ready` >> fs [] >>
    Cases_on `(agp32_init fbits).MEM.MEM_opc = 2w \/ (agp32_init fbits).MEM.MEM_opc = 3w \/
              (agp32_init fbits).MEM.MEM_opc = 4w \/ (agp32_init fbits).MEM.MEM_opc = 5w \/      
              (agp32_init fbits).MEM.MEM_opc = 12w` >> fs [] >>
    Cases_on `s19.EX.EX_isAcc` >> fs [] >>
    Cases_on `s19.EX.EX_jump_sel` >> fs []) >>
  qpat_abbrev_tac `s' = mk_circuit (procs _) (procs _) (agp32_init fbits) fext t` >>
  qpat_abbrev_tac `s'' = procs _ (fext t) s' s'` >>
  clist_update_state_tac >>
  fs [Abbr `s20`,Hazard_ctrl_def] >>
  Cases_on `s19.state = 3w \/ s19.state = 5w` >> fs [] >>
  Cases_on `s19.state = 1w \/ s19.state = 2w \/ s19.state = 4w \/ s19.state = 6w` >> fs [] >>
  Cases_on `(fext (SUC n)).ready` >> fs [] >>
  Cases_on `s''.MEM.MEM_opc = 2w \/ s''.MEM.MEM_opc = 3w \/ s''.MEM.MEM_opc = 4w \/
            s''.MEM.MEM_opc = 5w \/ s''.MEM.MEM_opc = 12w` >> fs [] >>
  Cases_on `s19.EX.EX_isAcc` >> fs [] >>
  Cases_on `s19.EX.EX_jump_sel` >> fs []
QED

(** IF is disabled then ID flags are F **)
Theorem agp32_IF_disable_ID_disable:
  !fext fbits t.
    ~(agp32 fext fbits t).IF.IF_PC_write_enable ==>
    ~(agp32 fext fbits t).ID.ID_ID_write_enable
Proof
  rw [] >>
  `?s s'.
  ((agp32 fext fbits t).IF.IF_PC_write_enable <=> (Hazard_ctrl (fext t) s s').IF.IF_PC_write_enable) /\
  ((agp32 fext fbits t).ID.ID_ID_write_enable <=> (Hazard_ctrl (fext t) s s').ID.ID_ID_write_enable)`
    by METIS_TAC [agp32_ctrl_flags_exists_Hazard_ctrl] >>
  fs [Hazard_ctrl_def] >>
  Cases_on `s'.state = 3w \/ s'.state = 5w` >> fs [] >>
  Cases_on `s'.state = 1w \/ s'.state = 2w \/ s'.state = 4w \/ s'.state = 6w` >> fs [] >>
  Cases_on `(fext t).ready` >> fs [] >>
  Cases_on `s.MEM.MEM_opc = 2w \/ s.MEM.MEM_opc = 3w \/ s.MEM.MEM_opc = 4w \/
            s.MEM.MEM_opc = 5w \/ s.MEM.MEM_opc = 12w` >> fs [] >>
  Cases_on `s'.EX.EX_isAcc` >> fs [] >>
 Cases_on `s'.EX.EX_jump_sel` >> fs []
QED

(** When IF is enabled and ID is disabled, ID_flush_flag is T **)
Theorem agp32_IF_enable_ID_disable_imply_ID_flush_flag:
  !fext fbits t.
    (agp32 fext fbits t).IF.IF_PC_write_enable ==>
    ~(agp32 fext fbits t).ID.ID_ID_write_enable ==>
    (agp32 fext fbits t).ID.ID_flush_flag
Proof
  rw [] >>
  `?s s'.
  ((agp32 fext fbits t).IF.IF_PC_write_enable <=> (Hazard_ctrl (fext t) s s').IF.IF_PC_write_enable) /\
  ((agp32 fext fbits t).ID.ID_ID_write_enable <=> (Hazard_ctrl (fext t) s s').ID.ID_ID_write_enable) /\
  ((agp32 fext fbits t).ID.ID_flush_flag <=> (Hazard_ctrl (fext t) s s').ID.ID_flush_flag)`
    by METIS_TAC [agp32_ctrl_flags_exists_Hazard_ctrl] >>
  fs [Hazard_ctrl_def] >>
  Cases_on `s'.state = 3w \/ s'.state = 5w` >> fs [] >>
  Cases_on `s'.state = 1w \/ s'.state = 2w \/ s'.state = 4w \/ s'.state = 6w` >> fs [] >>
  Cases_on `(fext t).ready` >> fs [] >>
  Cases_on `s.MEM.MEM_opc = 2w \/ s.MEM.MEM_opc = 3w \/ s.MEM.MEM_opc = 4w \/
            s.MEM.MEM_opc = 5w \/ s.MEM.MEM_opc = 12w` >> fs [] >>
  Cases_on `s'.EX.EX_isAcc` >> fs [] >>
 Cases_on `s'.EX.EX_jump_sel` >> fs []
QED


(* ID_ID_write_enable *)
(* ID_ID_write_enable, ID_EX_write_enable and ID_flush_flag, EX_NOP_flag *)
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

(** ID_ID_write_enable and ID_EX_write_enable **)
Theorem agp32_ID_ID_write_enable_ID_EX_write_enable:
  !fext fbits t.
    (agp32 fext fbits t).ID.ID_ID_write_enable ==>
    (agp32 fext fbits t).ID.ID_EX_write_enable
Proof
  rw [] >>
  `?s s'.
  ((agp32 fext fbits t).ID.ID_ID_write_enable <=> (Hazard_ctrl (fext t) s s').ID.ID_ID_write_enable) /\
  ((agp32 fext fbits t).ID.ID_EX_write_enable <=> (Hazard_ctrl (fext t) s s').ID.ID_EX_write_enable)`
    by METIS_TAC [agp32_ctrl_flags_exists_Hazard_ctrl] >>
  fs [Hazard_ctrl_def] >>
  Cases_on `s'.state = 3w \/ s'.state = 5w` >> fs [] >>
  Cases_on `s'.state = 1w \/ s'.state = 2w \/ s'.state = 4w \/ s'.state = 6w` >> fs [] >>
  Cases_on `(fext t).ready` >> fs [] >>
  Cases_on `s.MEM.MEM_opc = 2w \/ s.MEM.MEM_opc = 3w \/ s.MEM.MEM_opc = 4w \/
            s.MEM.MEM_opc = 5w \/ s.MEM.MEM_opc = 12w` >> fs [] >>
  Cases_on `s'.EX.EX_isAcc` >> fs [] >>
  Cases_on `s'.EX.EX_jump_sel` >> fs []
QED

(** ID_ID_write_enable and MEM_state_flag **)
Theorem agp32_ID_ID_write_enable_MEM_state_flag:
  !fext fbits t.
    (agp32 fext fbits t).ID.ID_ID_write_enable ==>
    (agp32 fext fbits t).MEM.MEM_state_flag
Proof
  rw [] >>
  `?s s'.
  ((agp32 fext fbits t).ID.ID_ID_write_enable <=> (Hazard_ctrl (fext t) s s').ID.ID_ID_write_enable) /\
  ((agp32 fext fbits t).MEM.MEM_state_flag <=> (Hazard_ctrl (fext t) s s').MEM.MEM_state_flag)`
    by METIS_TAC [agp32_ctrl_flags_exists_Hazard_ctrl] >>
  fs [Hazard_ctrl_def] >>
  Cases_on `s'.state = 3w \/ s'.state = 5w` >> fs [] >>
  Cases_on `s'.state = 1w \/ s'.state = 2w \/ s'.state = 4w \/ s'.state = 6w` >> fs [] >>
  Cases_on `(fext t).ready` >> fs [] >>
  Cases_on `s.MEM.MEM_opc = 2w \/ s.MEM.MEM_opc = 3w \/ s.MEM.MEM_opc = 4w \/
            s.MEM.MEM_opc = 5w \/ s.MEM.MEM_opc = 12w` >> fs [] >>
  Cases_on `s'.EX.EX_isAcc` >> fs [] >>
  Cases_on `s'.EX.EX_jump_sel` >> fs []
QED

(** ID_ID_write_enable and WB_state_flag **)
Theorem agp32_ID_ID_write_enable_WB_state_flag:
  !fext fbits t.
    (agp32 fext fbits t).ID.ID_ID_write_enable ==>
    (agp32 fext fbits t).WB.WB_state_flag
Proof
  rw [] >>
  `?s s'.
  ((agp32 fext fbits t).ID.ID_ID_write_enable <=> (Hazard_ctrl (fext t) s s').ID.ID_ID_write_enable) /\
  ((agp32 fext fbits t).WB.WB_state_flag <=> (Hazard_ctrl (fext t) s s').WB.WB_state_flag)`
    by METIS_TAC [agp32_ctrl_flags_exists_Hazard_ctrl] >>
  fs [Hazard_ctrl_def] >>
  Cases_on `s'.state = 3w \/ s'.state = 5w` >> fs [] >>
  Cases_on `s'.state = 1w \/ s'.state = 2w \/ s'.state = 4w \/ s'.state = 6w` >> fs [] >>
  Cases_on `(fext t).ready` >> fs [] >>
  Cases_on `s.MEM.MEM_opc = 2w \/ s.MEM.MEM_opc = 3w \/ s.MEM.MEM_opc = 4w \/
            s.MEM.MEM_opc = 5w \/ s.MEM.MEM_opc = 12w` >> fs [] >>
  Cases_on `s'.EX.EX_isAcc` >> fs [] >>
  Cases_on `s'.EX.EX_jump_sel` >> fs []
QED


(** ID_EX_write_enable **)
(** ID_EX_write_enable and MEM_state_flag **)
Theorem agp32_ID_EX_write_enable_MEM_state_flag:
  !fext fbits t.
    (agp32 fext fbits t).ID.ID_EX_write_enable ==>
    (agp32 fext fbits t).MEM.MEM_state_flag
Proof
  rw [] >>
  `?s s'.
  ((agp32 fext fbits t).ID.ID_EX_write_enable <=> (Hazard_ctrl (fext t) s s').ID.ID_EX_write_enable) /\
  ((agp32 fext fbits t).MEM.MEM_state_flag <=> (Hazard_ctrl (fext t) s s').MEM.MEM_state_flag)`
    by METIS_TAC [agp32_ctrl_flags_exists_Hazard_ctrl] >>
  fs [Hazard_ctrl_def] >>
  Cases_on `s'.state = 3w \/ s'.state = 5w` >> fs [] >>
  Cases_on `s'.state = 1w \/ s'.state = 2w \/ s'.state = 4w \/ s'.state = 6w` >> fs [] >>
  Cases_on `(fext t).ready` >> fs [] >>
  Cases_on `s.MEM.MEM_opc = 2w \/ s.MEM.MEM_opc = 3w \/ s.MEM.MEM_opc = 4w \/
            s.MEM.MEM_opc = 5w \/ s.MEM.MEM_opc = 12w` >> fs [] >>
  Cases_on `s'.EX.EX_isAcc` >> fs [] >>
  Cases_on `s'.EX.EX_jump_sel` >> fs []
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


(* lemmas about the scheduling function I *)
(** instr index relation between IF and EX stages **)
Theorem IF_instr_index_with_ID_instr:
  !I t fext fbits a.
    is_sch I (agp32 fext fbits) a ==>
    I (1,t) <> NONE ==>
    I (2,t) <> NONE ==>
    (THE (I (1,t)) > THE (I (2,t))) /\ (THE (I (1,t)) < THE (I (2,t)) + 2)
Proof
  rpt gen_tac >> rpt disch_tac >>
  fs [is_sch_def] >>
  Induct_on `t` >-
   fs [is_sch_init_def] >>
  rpt disch_tac >>
  Cases_on `enable_stg 1 (agp32 fext fbits t)` >-
   (Cases_on `isJump_isa_op (I' (3,t)) a` >-
     (Cases_on `enable_stg 2 (agp32 fext fbits t)` >-
       (fs [is_sch_fetch_def,is_sch_decode_def] >> METIS_TAC []) >>
      `(agp32 fext fbits t).ID.ID_flush_flag`
        by fs [enable_stg_def,agp32_IF_enable_ID_disable_imply_ID_flush_flag] >>
      fs [is_sch_disable_ID_def] >> METIS_TAC []) >>
    Cases_on `isJump_isa_op (I' (1,t)) a \/ isJump_isa_op (I' (2,t)) a \/
    I' (1,t) = NONE \/ THE (I' (1,t)) = 0` >-
     (fs [is_sch_fetch_def] >> METIS_TAC []) >>
    Cases_on `enable_stg 2 (agp32 fext fbits t)` >-
     fs [is_sch_fetch_def,is_sch_decode_def] >>
    `(agp32 fext fbits t).ID.ID_flush_flag`
      by fs [enable_stg_def,agp32_IF_enable_ID_disable_imply_ID_flush_flag] >>                    
    fs [is_sch_disable_ID_def] >> METIS_TAC []) >>
  `~enable_stg 2 (agp32 fext fbits t)` by fs [enable_stg_def,agp32_IF_disable_ID_disable] >>
  fs [is_sch_disable_ID_def,is_sch_disable_def] >>
  Cases_on `(agp32 fext fbits t).ID.ID_flush_flag` >>
  METIS_TAC []
QED

(** instr index relation between IF and EX stages **)
Theorem IF_instr_index_with_EX_instr:
  !I t fext fbits a.
    is_sch I (agp32 fext fbits) a ==>
    I (1,t) <> NONE ==>
    I (3,t) <> NONE ==>
    (THE (I (1,t)) > THE (I (3,t))) /\ (THE (I (1,t)) < THE (I (3,t)) + 3)
Proof
  rpt gen_tac >> rpt disch_tac >>
  Induct_on `t` >-
   fs [is_sch_def,is_sch_init_def] >>
  rpt disch_tac >>
  Cases_on `enable_stg 1 (agp32 fext fbits t)` >-
   (Cases_on `isJump_isa_op (I' (3,t)) a` >-
     (`enable_stg 3 (agp32 fext fbits t)`
        by fs [enable_stg_def,agp32_IF_PC_write_enable_and_EX_MEM_flags] >>
      fs [is_sch_def,is_sch_fetch_def,is_sch_execute_def] >>
      METIS_TAC []) >>
    Cases_on `isJump_isa_op (I' (1,t)) a \/ isJump_isa_op (I' (2,t)) a \/
    I' (1,t) = NONE \/ THE (I' (1,t)) = 0` >-
     (fs [is_sch_def,is_sch_fetch_def,is_sch_execute_def] >> METIS_TAC []) >>
    fs [] >>
    `enable_stg 3 (agp32 fext fbits t)`
      by fs [enable_stg_def,agp32_IF_PC_write_enable_and_EX_MEM_flags] >>
    Cases_on `isAcc_isa_op (I' (3,t)) a` >-
     (fs [is_sch_def,is_sch_execute_def] >> METIS_TAC []) >>
    `I' (3,SUC t) = I' (2,t)` by fs [is_sch_def,is_sch_execute_def] >> fs [] >>
    `(THE (I' (1,t)) > THE (I' (2,t))) /\ (THE (I' (1,t)) < THE (I' (2,t)) + 2)`
      by METIS_TAC [IF_instr_index_with_ID_instr] >> fs [is_sch_def,is_sch_fetch_def]) >>
  `~enable_stg 3 (agp32 fext fbits t)`
    by fs [enable_stg_def,agp32_IF_PC_write_disable_and_EX_disable] >>
  fs [is_sch_def,is_sch_disable_def] >>
  `1 <> 2 /\ 3 <> 2` by rw [] >> METIS_TAC []
QED

(** instr index relation between IF and MEM stages **)
Theorem IF_instr_index_with_MEM_instr:
  !I t fext fbits a.
    is_sch I (agp32 fext fbits) a ==>
    I (1,t) <> NONE ==>
    I (4,t) <> NONE ==>
    (THE (I (1,t)) > THE (I (4,t))) /\ (THE (I (1,t)) < THE (I (4,t)) + 4)
Proof
  rpt gen_tac >> rpt disch_tac >>
  Induct_on `t` >-
   fs [is_sch_def,is_sch_init_def] >>
  rpt disch_tac >>
  Cases_on `enable_stg 1 (agp32 fext fbits t)` >-
   (Cases_on `isJump_isa_op (I' (3,t)) a` >-
     (`enable_stg 4 (agp32 fext fbits t)`
        by fs [enable_stg_def,agp32_IF_PC_write_enable_and_EX_MEM_flags] >>
      fs [is_sch_def,is_sch_fetch_def,is_sch_memory_def] >>
      Cases_on `isMemOp_isa_op (I' (4,t)) a` >> fs [] >>
      METIS_TAC []) >>
    Cases_on `isJump_isa_op (I' (1,t)) a \/ isJump_isa_op (I' (2,t)) a \/
    I' (1,t) = NONE \/ THE (I' (1,t)) = 0` >-
     (fs [is_sch_def,is_sch_fetch_def,is_sch_execute_def] >> METIS_TAC []) >>
    fs [] >>
    `enable_stg 4 (agp32 fext fbits t)`
      by fs [enable_stg_def,agp32_IF_PC_write_enable_and_EX_MEM_flags] >>
    Cases_on `isMemOp_isa_op (I' (4,t)) a` >-
     (fs [is_sch_def,is_sch_memory_def] >> METIS_TAC []) >>
    `I' (4,SUC t) = I' (3,t)` by fs [is_sch_def,is_sch_memory_def] >> fs [] >>
    `(THE (I' (1,t)) > THE (I' (3,t))) /\ (THE (I' (1,t)) < THE (I' (3,t)) + 3)`
      by METIS_TAC [IF_instr_index_with_EX_instr] >> fs [is_sch_def,is_sch_fetch_def]) >>
  Cases_on `enable_stg 4 (agp32 fext fbits t)` >-
   (Cases_on `isMemOp_isa_op (I' (4,t)) a` >-
     (fs [is_sch_def,is_sch_memory_def] >> METIS_TAC []) >>
    `I' (4,SUC t) = I' (3,t)` by METIS_TAC [is_sch_def,is_sch_memory_def] >> fs [] >>
    `I' (1,SUC t) = I' (1,t)` by fs [is_sch_def,is_sch_disable_def] >> fs [] >>
    `(THE (I' (1,t)) > THE (I' (3,t))) /\ (THE (I' (1,t)) < THE (I' (3,t)) + 3)`
      by METIS_TAC [IF_instr_index_with_EX_instr] >> fs []) >>
  `I' (4,SUC t) = I' (4,t) /\ I' (1,SUC t) = I' (1,t)`
    by fs [is_sch_def,is_sch_disable_def] >> fs []
QED

(** instr index relation between ID and EX stages **)
Theorem ID_instr_index_with_EX_instr:
  !I t fext fbits a.
    is_sch I (agp32 fext fbits) a ==>
    I (2,t) <> NONE ==>
    I (3,t) <> NONE ==>
    (THE (I (2,t)) > THE (I (3,t))) /\ (THE (I (2,t)) < THE (I (3,t)) + 2)
Proof
  rpt gen_tac >> rpt disch_tac >>
  Induct_on `t` >-
   fs [is_sch_def,is_sch_init_def] >>
  rpt disch_tac >>
  Cases_on `enable_stg 2 (agp32 fext fbits t)` >-
   (Cases_on `isJump_isa_op (I' (2,t)) a \/ isJump_isa_op (I' (3,t)) a` >-
     (fs [is_sch_def,is_sch_decode_def] >> METIS_TAC []) >>
    `I' (2,SUC t) = I' (1,t)` by fs [is_sch_def,is_sch_decode_def] >>
    `enable_stg 3 (agp32 fext fbits t)`
      by fs [enable_stg_def,agp32_ID_ID_write_enable_ID_EX_write_enable] >>
    Cases_on `isAcc_isa_op (I' (3,t)) a` >-
     (fs [is_sch_def,is_sch_execute_def] >> METIS_TAC []) >>
    `I' (3,SUC t) = I' (2,t)` by fs [is_sch_def,is_sch_execute_def] >>
    METIS_TAC [IF_instr_index_with_ID_instr]) >>
  Cases_on `enable_stg 3 (agp32 fext fbits t)` >-
   (`(agp32 fext fbits t).ID.ID_flush_flag`
      by fs [enable_stg_def,agp32_ID_enable_flags_imply_flush_NOP_flags] >>
    fs [is_sch_def,is_sch_disable_ID_def] >> METIS_TAC []) >>
  `I' (2,SUC t) = I' (2,t) /\ I' (3,SUC t) = I' (3,t)`
    by METIS_TAC [is_sch_def,is_sch_disable_ID_def,is_sch_disable_def] >> fs []
QED

(** instr index relation between ID and MEM stages **)
Theorem ID_instr_index_with_MEM_instr:
  !I t fext fbits a.
    is_sch I (agp32 fext fbits) a ==>
    I (2,t) <> NONE ==>
    I (4,t) <> NONE ==>
    (THE (I (2,t)) > THE (I (4,t))) /\ (THE (I (2,t)) < THE (I (4,t)) + 3)
Proof
  rpt gen_tac >> rpt disch_tac >>
  Induct_on `t` >-
   fs [is_sch_def,is_sch_init_def] >>
  rpt disch_tac >>
  Cases_on `enable_stg 2 (agp32 fext fbits t)` >-
   (Cases_on `isJump_isa_op (I' (2,t)) a \/ isJump_isa_op (I' (3,t)) a` >-
     (fs [is_sch_def,is_sch_decode_def] >> METIS_TAC []) >>
    `I' (2,SUC t) = I' (1,t)` by fs [is_sch_def,is_sch_decode_def] >>
    `enable_stg 4 (agp32 fext fbits t)`
      by fs [enable_stg_def,agp32_ID_ID_write_enable_MEM_state_flag] >>
    Cases_on `isMemOp_isa_op (I' (4,t)) a` >-
     (fs [is_sch_def,is_sch_memory_def] >> METIS_TAC []) >>
    `I' (4,SUC t) = I' (3,t)` by fs [is_sch_def,is_sch_memory_def] >> fs [] >>
    METIS_TAC [IF_instr_index_with_EX_instr]) >>
  Cases_on `enable_stg 4 (agp32 fext fbits t)` >-
   (Cases_on `(agp32 fext fbits t).ID.ID_flush_flag` >-
     (fs [is_sch_def,is_sch_disable_ID_def] >> METIS_TAC []) >>
    Cases_on `isMemOp_isa_op (I' (4,t)) a` >-
     (fs [is_sch_def,is_sch_memory_def] >> METIS_TAC []) >>
    `I' (2,SUC t) = I' (2,t) /\ I' (4,SUC t) = I' (3,t)`
      by fs [is_sch_def,is_sch_memory_def,is_sch_disable_ID_def] >> fs [] >>
    `(THE (I' (2,t)) > THE (I' (3,t))) /\ (THE (I' (2,t)) < THE (I' (3,t)) + 2)`
      by METIS_TAC [ID_instr_index_with_EX_instr] >> fs []) >>
  `I' (2,SUC t) = I' (2,t) /\ I' (4,SUC t) = I' (4,t)`
    by METIS_TAC [is_sch_def,is_sch_disable_ID_def,is_sch_disable_def] >> fs []
QED

(** instr index relation between EX and MEM stages **)
Theorem EX_instr_index_with_MEM_instr:
  !I t fext fbits a.
    is_sch I (agp32 fext fbits) a ==>
    I (3,t) <> NONE ==>
    I (4,t) <> NONE ==>
    (THE (I (3,t)) >= THE (I (4,t))) /\ (THE (I (3,t)) < THE (I (4,t)) + 2)
Proof
  rpt gen_tac >> rpt disch_tac >>
  Induct_on `t` >-
   fs [is_sch_def,is_sch_init_def] >>
  rpt disch_tac >>
  Cases_on `enable_stg 3 (agp32 fext fbits t)` >-
   (Cases_on `isJump_isa_op (I' (3,t)) a \/ isAcc_isa_op (I' (3,t)) a` >-
     (fs [is_sch_def,is_sch_execute_def] >> METIS_TAC []) >>
    `I' (3,SUC t) = I' (2,t)` by fs [is_sch_def,is_sch_execute_def] >> fs [] >>
    `enable_stg 4 (agp32 fext fbits t)`
      by fs [enable_stg_def,agp32_ID_EX_write_enable_MEM_state_flag] >>
    Cases_on `isMemOp_isa_op (I' (4,t)) a` >-
     (fs [is_sch_def,is_sch_memory_def] >> METIS_TAC []) >>
    `I' (4,SUC t) = I' (3,t)` by fs [is_sch_def,is_sch_memory_def] >> fs [] >>
    `(THE (I' (2,t)) > THE (I' (3,t))) /\ (THE (I' (2,t)) < THE (I' (3,t)) + 2)`
      by METIS_TAC [ID_instr_index_with_EX_instr] >> fs []) >>
  Cases_on `enable_stg 4 (agp32 fext fbits t)` >>
  fs [is_sch_def,is_sch_disable_def] >-
   (Cases_on `isMemOp_isa_op (I' (4,t)) a` >-
     (fs [is_sch_memory_def] >> METIS_TAC []) >>
    `I' (4,SUC t) = I' (3,t)` by fs [is_sch_memory_def] >> fs []) >>
  `I' (3,SUC t) = I' (3,t) /\ I' (4,SUC t) = I' (4,t)` by fs [] >> fs []
QED

(** I (1,t) = I (2,t) + 1 **)
Theorem IF_instr_index_with_ID_instr_plus_1:
  !I t fext fbits a.
    is_sch I (agp32 fext fbits) a ==>
    I (1,t) <> NONE ==>
    I (2,t) <> NONE ==>
    THE (I (1,t)) = THE (I (2,t)) + 1
Proof
  rw [] >>
  `(THE (I' (1,t)) > THE (I' (2,t))) /\ (THE (I' (1,t)) < THE (I' (2,t)) + 2)`
    by METIS_TAC [IF_instr_index_with_ID_instr] >> fs []
QED

(** I (2,t) = I (3,t) + 1 **)
Theorem ID_instr_index_with_EX_instr_plus_1:
  !I t fext fbits a.
    is_sch I (agp32 fext fbits) a ==>
    I (2,t) <> NONE ==>
    I (3,t) <> NONE ==>
    THE (I (2,t)) = THE (I (3,t)) + 1
Proof
  rw [] >>
  `(THE (I' (2,t)) > THE (I' (3,t))) /\ (THE (I' (2,t)) < THE (I' (3,t)) + 2)`
    by METIS_TAC [ID_instr_index_with_EX_instr] >> fs []
QED

(** I (3,SUC t) = I (3,t) + 1 **)
Theorem EX_instr_index_t_SUC_t_enable:
  !I t fext fbits a.
    is_sch I (agp32 fext fbits) a ==>
    enable_stg 3 (agp32 fext fbits t) ==>
    I (3,t) <> NONE ==>
    I (3,SUC t) <> NONE ==>
    THE (I (3,SUC t)) = THE (I (3,t)) + 1
Proof
  rw [] >> Cases_on `isJump_isa_op (I' (3,t)) a \/ isAcc_isa_op (I' (3,t)) a` >-
   (fs [is_sch_def,is_sch_execute_def] >> METIS_TAC []) >>
  `I' (3,SUC t) = I' (2,t)` by fs [is_sch_def,is_sch_execute_def] >> fs [] >>
  METIS_TAC [ID_instr_index_with_EX_instr_plus_1]
QED
 
(* TODO: when IF/ID/EX are enabled, WB must be enabled as well
(** instr index relation between ID and WB stages **)
Theorem ID_instr_index_with_WB_instr:
  !I t fext fbits a.
    is_sch I (agp32 fext fbits) a ==>
    I (2,t) <> NONE ==>
    I (5,t) <> NONE ==>
    (THE (I (2,t)) > THE (I (5,t))) /\
    (THE (I (2,t)) < THE (I (5,t)) + 4)
Proof
  rpt gen_tac >> rpt disch_tac >>
  Induct_on `t` >-
   fs [is_sch_def,is_sch_init_def] >>
  rpt disch_tac >>
  Cases_on `enable_stg 2 (agp32 fext fbits t)` >-
   (Cases_on `isJump_isa_op (I' (2,t)) a \/ isJump_isa_op (I' (3,t)) a` >-
     (fs [is_sch_def,is_sch_decode_def] >> METIS_TAC []) >>
    `I' (2,SUC t) = I' (1,t)` by fs [is_sch_def,is_sch_decode_def] >>
    Cases_on `enable_stg 5 (agp32 fext fbits t)` >-
     (`I' (5,SUC t) = I' (4,t)` by fs [is_sch_def,is_sch_writeback_def] >> fs [] >>
      METIS_TAC [IF_instr_index_with_MEM_instr]) >>
    `I' (5,SUC t) = I' (5,t)` by fs [is_sch_def,is_sch_disable_def] >> fs [] >>
    cheat) >>
  Cases_on `enable_stg 5 (agp32 fext fbits t)` >-
   (Cases_on `(agp32 fext fbits t).ID.ID_flush_flag` >-
     (fs [is_sch_def,is_sch_disable_ID_def] >> METIS_TAC []) >>
    `I' (2,SUC t) = I' (2,t) /\ I' (5,SUC t) = I' (4,t)`
      by fs [is_sch_def,is_sch_writeback_def,is_sch_disable_ID_def] >> fs [] >>
    `(THE (I' (2,t)) > THE (I' (4,t))) /\ (THE (I' (2,t)) < THE (I' (4,t)) + 3)`
      by METIS_TAC [ID_instr_index_with_MEM_instr] >> fs []) >>
  `I' (2,SUC t) = I' (2,t) /\ I' (5,SUC t) = I' (5,t)`
    by METIS_TAC [is_sch_def,is_sch_disable_ID_def,is_sch_disable_def] >> fs []
QED

(** instr index relation between EX and WB stages **)
Theorem EX_instr_index_with_WB_instr:
  !I t fext fbits a.
    is_sch I (agp32 fext fbits) a ==>
    I (3,t) <> NONE ==>
    I (5,t) <> NONE ==>
    (THE (I (3,t)) >= THE (I (5,t))) /\
    (THE (I (3,t)) < THE (I (5,t)) + 3)
Proof
  rpt gen_tac >> rpt disch_tac >>
  Induct_on `t` >-
   fs [is_sch_def,is_sch_init_def] >>
  rpt disch_tac >>
  Cases_on `enable_stg 3 (agp32 fext fbits t)` >-
   (Cases_on `isJump_isa_op (I' (3,t)) a \/ isAcc_isa_op (I' (3,t)) a` >-
     (fs [is_sch_def,is_sch_execute_def] >> METIS_TAC []) >>
    `I' (3,SUC t) = I' (2,t)` by fs [is_sch_def,is_sch_execute_def] >> fs [] >>
    Cases_on `enable_stg 5 (agp32 fext fbits t)` >-
     (`I' (5,SUC t) = I' (4,t)` by fs [is_sch_def,is_sch_writeback_def] >> fs [] >>
      `(THE (I' (2,t)) > THE (I' (4,t))) /\ (THE (I' (2,t)) < THE (I' (4,t)) + 3)`
        by METIS_TAC [ID_instr_index_with_MEM_instr] >> fs []) >>
    `I' (5,SUC t) = I' (5,t)` by fs [is_sch_def,is_sch_disable_def] >> fs [] >>
    cheat) >>
  Cases_on `enable_stg 5 (agp32 fext fbits t)` >-
  (`I' (3,SUC t) = I' (3,t) /\ I' (5,SUC t) = I' (4,t)`
     by fs [is_sch_def,is_sch_writeback_def,is_sch_disable_def] >> fs [] >>
   `(THE (I' (3,t)) >= THE (I' (4,t))) /\ (THE (I' (3,t)) < THE (I' (4,t)) + 2)`
     by METIS_TAC [EX_instr_index_with_MEM_instr] >> fs []) >>
  `I' (3,SUC t) = I' (3,t) /\ I' (5,SUC t) = I' (5,t)`
    by fs [is_sch_def,is_sch_disable_def] >> fs []
QED

(** instr index relation between MEM and WB stages **)
Theorem MEM_instr_index_with_WB_instr:
  !I t fext fbits a.
    is_sch I (agp32 fext fbits) a ==>
    I (4,t) <> NONE ==>
    I (5,t) <> NONE ==>
    (THE (I (4,t)) >= THE (I (5,t))) /\ (THE (I (4,t)) < THE (I (5,t)) + 2)
Proof
  rpt gen_tac >> rpt disch_tac >>
  Induct_on `t` >-
   fs [is_sch_def,is_sch_init_def] >>
  rpt disch_tac >>
  Cases_on `enable_stg 4 (agp32 fext fbits t)` >-
   (Cases_on `isMemOp_isa_op (I' (4,t)) a` >-
     (fs [is_sch_def,is_sch_memory_def] >> METIS_TAC []) >>
    `I' (4,SUC t) = I' (3,t)` by fs [is_sch_def,is_sch_memory_def] >> fs [] >>
    `enable_stg 4 (agp32 fext fbits t)`
      by fs [enable_stg_def,agp32_ID_EX_write_enable_MEM_state_flag] >>
    Cases_on `enable_stg 5 (agp32 fext fbits t)` >-
     (`I' (5,SUC t) = I' (4,t)` by fs [is_sch_def,is_sch_writeback_def] >> fs [] >>
      METIS_TAC [EX_instr_index_with_MEM_instr]) >>
    `I' (5,SUC t) = I' (5,t)` by fs [is_sch_def,is_sch_disable_def] >> fs [] >>
    cheat) >>
  Cases_on `enable_stg 5 (agp32 fext fbits t)` >-
   (`I' (4,SUC t) = I' (4,t) /\ I' (5,SUC t) = I' (4,t)`
      by fs [is_sch_def,is_sch_writeback_def,is_sch_disable_def] >> fs []) >>
  `I' (4,SUC t) = I' (4,t) /\ I' (5,SUC t) = I' (5,t)` by fs [is_sch_def,is_sch_disable_def] >> fs []
QED

(** instr index relation between IF and WB stages **)
Theorem IF_instr_index_with_WB_instr:
  !I t fext fbits a.
    is_sch I (agp32 fext fbits) a ==>
    I (1,t) <> NONE ==>
    I (5,t) <> NONE ==>
    (THE (I (1,t)) > THE (I (5,t))) /\
    (THE (I (1,t)) < THE (I (5,t)) + 5)
Proof
  rpt gen_tac >> rpt disch_tac >>
  Induct_on `t` >-
   fs [is_sch_def,is_sch_init_def] >>
  rpt disch_tac >>
  Cases_on `enable_stg 1 (agp32 fext fbits t)` >-
   (Cases_on `isJump_isa_op (I' (3,t)) a` >-
     (Cases_on `enable_stg 5 (agp32 fext fbits t)` >-
       (`I' (1,SUC t) = SOME (THE (I' (3,t)) + 1) /\ I' (5,SUC t) = I' (4,t)`
          by fs [is_sch_def,is_sch_fetch_def,is_sch_writeback_def] >> fs [] >>
        `I' (3,t) <> NONE` by METIS_TAC [isJump_isa_op_not_none] >>
        `(THE (I' (3,t)) >= THE (I' (4,t))) /\ (THE (I' (3,t)) < THE (I' (4,t)) + 2)`
          by METIS_TAC [EX_instr_index_with_MEM_instr] >> fs []) >>
      `I' (1,SUC t) = SOME (THE (I' (3,t)) + 1) /\ I' (5,SUC t) = I' (5,t)`
        by fs [is_sch_def,is_sch_fetch_def,is_sch_disable_def] >> fs [] >>
      (** I (3,t) with I (5,t) **)
      cheat) >>
    Cases_on `isJump_isa_op (I' (1,t)) a \/ isJump_isa_op (I' (2,t)) a \/
    I' (1,t) = NONE \/ THE (I' (1,t)) = 0` >-
     (fs [is_sch_def,is_sch_fetch_def,is_sch_execute_def] >> METIS_TAC []) >>
    fs [] >>
    `enable_stg 5 (agp32 fext fbits t)` by cheat >>
    `I' (5,SUC t) = I' (4,t)` by fs [is_sch_def,is_sch_writeback_def] >> fs [] >>
    `(THE (I' (1,t)) > THE (I' (4,t))) /\ (THE (I' (1,t)) < THE (I' (4,t)) + 4)`
      by METIS_TAC [IF_instr_index_with_MEM_instr] >> fs [is_sch_def,is_sch_fetch_def]) >>
  Cases_on `enable_stg 5 (agp32 fext fbits t)` >-
   (`I' (5,SUC t) = I' (4,t)` by METIS_TAC [is_sch_def,is_sch_writeback_def] >> fs [] >>
    `I' (1,SUC t) = I' (1,t)` by fs [is_sch_def,is_sch_disable_def] >> fs [] >>
    `(THE (I' (1,t)) > THE (I' (4,t))) /\ (THE (I' (1,t)) < THE (I' (4,t)) + 4)`
      by METIS_TAC [IF_instr_index_with_MEM_instr] >> fs []) >>
  `I' (5,SUC t) = I' (5,t) /\ I' (1,SUC t) = I' (1,t)`
    by fs [is_sch_def,is_sch_disable_def] >> fs []
QED
*)

val _ = export_theory ();
