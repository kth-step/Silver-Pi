open hardwarePreamble translatorTheory arithmeticTheory dep_rewrite blastLib bitstringSyntax fcpSyntax listSyntax wordsSyntax wordsLib agp32StateTheory agp32EnvironmentTheory agp32ProcessorTheory agp32RelationTheory agp32UpdateTheory;

val _ = new_theory "agp32Internal";

val _ = prefer_num ();
val _ = guess_lengths ();

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


(* ID_EX_write_enable, ID_ID_write_enable and ID_flush_flag *)
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

(* IF_PC_write_enable and MEM_state_flag *)
Theorem agp32_IF_PC_write_enable_and_MEM_state_flag:
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
    by fs [agp32_command_updated_by_agp32_next_state,Abbr `s`] >>
  rw [agp32_next_state_def] >>
  Cases_on_word_value `(1 >< 0) s.MEM.MEM_dataB` >> fs []
QED

val _ = export_theory ();
