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
    by fs [agp32_EX_func_updated_EX_pipeline,agp32_EX_opc_updated_EX_pipeline] >>
  fs [EX_pipeline_def] >> rw [] >>
  `s''.ID.ID_EX_write_enable = s'.ID.ID_EX_write_enable` by cheat >> fs [] >>
  `s''.ID.ID_func = s'.ID.ID_func /\ s''.ID.ID_opc = s'.ID.ID_opc` by cheat >>
  METIS_TAC [agp32_ID_opc_implies_ID_func]
QED

val _ = export_theory ();
