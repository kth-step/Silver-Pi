open hardwarePreamble translatorTheory translatorLib arithmeticTheory wordsExtraTheory dep_rewrite blastLib bitstringSyntax fcpSyntax listSyntax wordsSyntax agp32StateTheory agp32EnvironmentTheory agp32ProcessorTheory ag32Theory ag32ExtraTheory ag32UtilitiesTheory agp32RelationTheory agp32UpdateTheory agp32InternalTheory;

(* correctness of EX stage items with respect to the ISA *)
val _ = new_theory "agp32_EX_Correct";

val _ = prefer_num ();
val _ = guess_lengths ();


(** lemmas about words for ALU and SHIFT **)
Theorem ALU_correct_carry_lem:
  !(w:33 word). word_bit 32 w <=> n2w (dimword(:32)) <=+ w
Proof
  simp [] >> BBLAST_PROVE_TAC
QED

Theorem ALU_correct_v2w_carry33_lem:
  !b. v2w [b] = if b then (1w:33 word) else 0w
Proof
  Cases >> EVAL_TAC
QED

Theorem ALU_correct_v2w_carry32_lem:
  !b. v2w [b] = if b then (1w:32 word) else 0w
Proof
  Cases >> EVAL_TAC
QED

Theorem w2n_add_MOD_itself:
  !(w1:word32) (w2:word32).
    w2n w1 + w2n w2 = (w2n w1 + w2n w2) MOD 8589934592
Proof
  rw [] >>
  `(w2n w1 < 4294967296) /\ (w2n w2 < 4294967296)` by METIS_TAC [w2n_lt,dimword_32] >>
  fs []
QED

Theorem w2n_add_MOD_itself_1:
  !(w1:word32) (w2:word32).
    w2n w1 + (w2n w2 + 1) = (w2n w1 + (w2n w2 + 1)) MOD 8589934592
Proof
  rw [] >>
  `(w2n w1 < 4294967296) /\ (w2n w2 < 4294967296)` by METIS_TAC [w2n_lt,dimword_32] >>
  fs []
QED

Theorem MOD_MOD_lt:
  !x n m. n < m /\ 0 <> n ==> (x MOD n) MOD m = x MOD n
Proof
  metis_tac [LESS_MOD,MOD_LESS,LESS_TRANS,NOT_ZERO_LT_ZERO]
QED

Theorem dimindex_MOD_dimword:
  dimindex (:'a) MOD dimword (:'a) = dimindex (:'a)
Proof
  simp [MOD_LESS, dimindex_lt_dimword]
QED

Theorem word_ror_intro_mod:
  !(w:'a word) sh. w #>>~ sh = w #>>~ word_mod sh (n2w (dimindex(:'a)))
Proof
 simp [word_ror_bv_def,word_ror_def,word_mod_def,
       dimindex_MOD_dimword,MOD_MOD_lt,dimindex_lt_dimword]
QED

Theorem word_ror_impl:
  !(w:word32) sh. sh <+ 32w ==> w #>>~ sh = (w >>>~ sh || w <<~ (32w - sh))
Proof
  BBLAST_TAC
QED


(** EX_opc is flushed **)
Theorem EX_instr_index_NONE_opc_flush:
  !I t fext fbits a.
    is_sch I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (3,SUC t) = NONE ==>
    ((agp32 fext fbits (SUC t)).EX.EX_opc = 16w) \/ ((agp32 fext fbits (SUC t)).EX.EX_opc = 15w)
Proof
  rw [] >> Cases_on `enable_stg 3 (agp32 fext fbits t)` >-
   (Cases_on `isJump_hw_op (agp32 fext fbits t)` >-
     (`(agp32 fext fbits t).EX.EX_NOP_flag`
        by fs [enable_stg_def,agp32_ID_EX_write_enable_isJump_hw_op_EX_NOP_flag] >>
      fs [agp32_EX_opc_flush_when_EX_NOP_flag]) >>
    Cases_on `reg_data_hazard (agp32 fext fbits t)` >-
     (`(agp32 fext fbits t).EX.EX_NOP_flag`
        by fs [enable_stg_def,agp32_ID_EX_write_enable_reg_data_hazard_EX_NOP_flag] >>
      fs [agp32_EX_opc_flush_when_EX_NOP_flag]) >>
    `I' (3,SUC t) = I' (2,t)` by METIS_TAC [is_sch_def,is_sch_execute_def] >> fs [] >>
    `~(agp32 fext fbits t).EX.EX_NOP_flag`
      by fs [enable_stg_def,agp32_ID_EX_write_enable_no_jump_or_reg_data_hazard_EX_NOP_flag_F] >>
    `(agp32 fext fbits (SUC t)).EX.EX_opc = (agp32 fext fbits t).ID.ID_opc`
      by fs [agp32_EX_opc_ID_opc_when_not_EX_NOP_flag] >> fs [] >>
    Cases_on `enable_stg 2 (agp32 fext fbits (t-1))` >-
     (`isJump_hw_op (agp32 fext fbits (t-1))` by fs [Rel_def,Inv_Rel_def] >>
      `(agp32 fext fbits (SUC (t-1))).ID.ID_opc = 15w` by fs [EX_isJump_hw_op_next_ID_opc] >>
      Cases_on `t` >> fs []) >>
    fs [Rel_def,Inv_Rel_def]) >>
  `I' (3,SUC t) = I' (3,t)` by METIS_TAC [is_sch_def,is_sch_disable_def] >>
  fs [agp32_EX_opc_unchanged_when_EX_disabled,Rel_def,Inv_Rel_def]
QED


(** EX_PC **)
Theorem agp32_Rel_ag32_EX_PC_correct:
  !fext fbits a t I.
    is_sch_execute I (agp32 fext fbits) a ==>
    is_sch_disable I (agp32 fext fbits) ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (3,SUC t) <> NONE ==>
    (agp32 fext fbits (SUC t)).EX.EX_PC = (FUNPOW Next (THE (I (3,SUC t)) − 1) a).PC
Proof
  rw [] >> Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state;WB_pipeline;MEM_pipeline] (fext t) s s` >>
  `(agp32 fext fbits (SUC t)).EX.EX_PC = (EX_pipeline (fext t) s s').EX.EX_PC`
    by fs [agp32_EX_PC_imm_addrW_updated_by_EX_pipeline] >> rw [] >>
  `(s'.ID.ID_EX_write_enable = s.ID.ID_EX_write_enable) /\ (s'.EX.EX_PC = s.EX.EX_PC)`
    by METIS_TAC [agp32_same_EX_items_before_EX_pipeline,Abbr `s`,Abbr `s'`] >>
  Cases_on `enable_stg 3 (agp32 fext fbits t)` >-
   (fs [is_sch_execute_def] >>
    Cases_on `isJump_hw_op (agp32 fext fbits t)` >-
     METIS_TAC [] >>
    Cases_on `reg_data_hazard (agp32 fext fbits t)` >-
     METIS_TAC [] >>
    `I' (3,SUC t) = I' (2,t)` by fs [] >> fs [] >>
    `s'.ID.ID_EX_write_enable` by fs [enable_stg_def,Abbr `s`] >>
    rw [EX_pipeline_def] >> fs [Rel_def,ID_Rel_def]) >>
  `I' (3,SUC t) = I' (3,t)` by fs [is_sch_disable_def] >>
  `~s'.ID.ID_EX_write_enable` by fs [enable_stg_def,Abbr `s`] >>
  rw [EX_pipeline_def] >>
  fs [Rel_def,EX_Rel_def]
QED

(** EX_addrW **)
Theorem agp32_Rel_ag32_EX_addrW_correct:
  !fext fbits a t I.
    is_sch_execute I (agp32 fext fbits) a ==>
    is_sch_disable I (agp32 fext fbits) ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (3,SUC t) <> NONE ==>
    (agp32 fext fbits (SUC t)).EX.EX_addrW = addrW (FUNPOW Next (THE (I (3,SUC t)) − 1) a)
Proof
  rw [] >> Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state;WB_pipeline;MEM_pipeline] (fext t) s s` >>
  `(agp32 fext fbits (SUC t)).EX.EX_addrW = (EX_pipeline (fext t) s s').EX.EX_addrW`
    by fs [agp32_EX_PC_imm_addrW_updated_by_EX_pipeline] >> rw [] >>
  `(s'.ID.ID_EX_write_enable = s.ID.ID_EX_write_enable) /\ (s'.EX.EX_addrW = s.EX.EX_addrW)`
    by METIS_TAC [agp32_same_EX_items_before_EX_pipeline,Abbr `s`,Abbr `s'`] >>
  `s'.ID.ID_addrW = s.ID.ID_addrW`
    by METIS_TAC [agp32_same_ID_items_before_EX_pipeline,Abbr `s`,Abbr `s'`] >>
  Cases_on `enable_stg 3 (agp32 fext fbits t)` >-
   (fs [is_sch_execute_def] >>
    Cases_on `isJump_hw_op (agp32 fext fbits t)` >-
     METIS_TAC [] >>
    Cases_on `reg_data_hazard (agp32 fext fbits t)` >-
     METIS_TAC [] >>
    `I' (3,SUC t) = I' (2,t)` by fs [] >> fs [] >>
    `s'.ID.ID_EX_write_enable` by fs [enable_stg_def,Abbr `s`] >>
    rw [EX_pipeline_def] >> fs [Rel_def,ID_Rel_def]) >>
  `I' (3,SUC t) = I' (3,t)` by fs [is_sch_disable_def] >>
  `~s'.ID.ID_EX_write_enable` by fs [enable_stg_def,Abbr `s`] >>
  rw [EX_pipeline_def] >>
  fs [Rel_def,EX_Rel_def]
QED

(** EX_imm **)
Theorem agp32_Rel_ag32_EX_imm_correct:
  !fext fbits a t I.
    is_sch_execute I (agp32 fext fbits) a ==>
    is_sch_disable I (agp32 fext fbits) ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (3,SUC t) <> NONE ==>
    (agp32 fext fbits (SUC t)).EX.EX_imm = imm (FUNPOW Next (THE (I (3,SUC t)) − 1) a)
Proof
  rw [] >> Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state;WB_pipeline;MEM_pipeline] (fext t) s s` >>
  `(agp32 fext fbits (SUC t)).EX.EX_imm = (EX_pipeline (fext t) s s').EX.EX_imm`
    by fs [agp32_EX_PC_imm_addrW_updated_by_EX_pipeline] >> rw [] >>
  `(s'.ID.ID_EX_write_enable = s.ID.ID_EX_write_enable) /\ (s'.EX.EX_imm = s.EX.EX_imm)`
    by METIS_TAC [agp32_same_EX_items_before_EX_pipeline,Abbr `s`,Abbr `s'`] >>
  `s'.ID.ID_imm = s.ID.ID_imm`
    by METIS_TAC [agp32_same_ID_items_before_EX_pipeline,Abbr `s`,Abbr `s'`] >>
  Cases_on `enable_stg 3 (agp32 fext fbits t)` >-
   (fs [is_sch_execute_def] >>
    Cases_on `isJump_hw_op (agp32 fext fbits t)` >-
     METIS_TAC [] >>
    Cases_on `reg_data_hazard (agp32 fext fbits t)` >-
     METIS_TAC [] >>
    `I' (3,SUC t) = I' (2,t)` by fs [] >> fs [] >>
    `s'.ID.ID_EX_write_enable` by fs [enable_stg_def,Abbr `s`] >>
    rw [EX_pipeline_def] >> fs [Rel_def,ID_Rel_def]) >>
  `I' (3,SUC t) = I' (3,t)` by fs [is_sch_disable_def] >>
  `~s'.ID.ID_EX_write_enable` by fs [enable_stg_def,Abbr `s`] >>
  rw [EX_pipeline_def] >>
  fs [Rel_def,EX_Rel_def]
QED

(** EX_opc **)
Theorem agp32_Rel_ag32_EX_opc_correct:
  !fext fbits a t I.
    is_sch_execute I (agp32 fext fbits) a ==>
    is_sch_disable I (agp32 fext fbits) ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (3,SUC t) <> NONE ==>
    (agp32 fext fbits (SUC t)).EX.EX_opc = opc (FUNPOW Next (THE (I (3,SUC t)) − 1) a)
Proof
  rw [] >> Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state;WB_pipeline;MEM_pipeline] (fext t) s s` >>
  `(agp32 fext fbits (SUC t)).EX.EX_opc = (EX_pipeline (fext t) s s').EX.EX_opc`
    by fs [agp32_EX_opc_func_updated_by_EX_pipeline] >> rw [] >>
  `(s'.ID.ID_EX_write_enable = s.ID.ID_EX_write_enable) /\ (s'.EX.EX_opc = s.EX.EX_opc) /\
  (s'.EX.EX_NOP_flag = s.EX.EX_NOP_flag)`
    by METIS_TAC [agp32_same_EX_items_before_EX_pipeline,Abbr `s`,Abbr `s'`] >>
  `s'.ID.ID_opc = s.ID.ID_opc`
    by METIS_TAC [agp32_same_ID_items_before_EX_pipeline,Abbr `s`,Abbr `s'`] >>
  Cases_on `enable_stg 3 (agp32 fext fbits t)` >-
   (fs [is_sch_execute_def] >>
    Cases_on `isJump_hw_op (agp32 fext fbits t)` >-
     METIS_TAC [] >>
    Cases_on `reg_data_hazard (agp32 fext fbits t)` >-
     METIS_TAC [] >>
    `I' (3,SUC t) = I' (2,t)` by fs [] >> fs [] >>
    `s'.ID.ID_EX_write_enable` by fs [enable_stg_def,Abbr `s`] >>
    `~s.EX.EX_NOP_flag`
      by fs [enable_stg_def,Abbr `s`,
             agp32_ID_EX_write_enable_no_jump_or_reg_data_hazard_EX_NOP_flag_F] >>
    rw [EX_pipeline_def] >> fs [Rel_def,ID_Rel_def]) >>
  `I' (3,SUC t) = I' (3,t)` by fs [is_sch_disable_def] >>
  `~s'.ID.ID_EX_write_enable` by fs [enable_stg_def,Abbr `s`] >>
  rw [EX_pipeline_def] >>
  fs [Rel_def,EX_Rel_def]
QED

(** EX_func **)
Theorem agp32_Rel_ag32_EX_func_correct:
  !fext fbits a t I.
    is_sch_execute I (agp32 fext fbits) a ==>
    is_sch_disable I (agp32 fext fbits) ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (3,SUC t) <> NONE ==>
    (agp32 fext fbits (SUC t)).EX.EX_func = func (FUNPOW Next (THE (I (3,SUC t)) − 1) a)
Proof
  rw [] >> Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state;WB_pipeline;MEM_pipeline] (fext t) s s` >>
  `(agp32 fext fbits (SUC t)).EX.EX_func = (EX_pipeline (fext t) s s').EX.EX_func`
    by fs [agp32_EX_opc_func_updated_by_EX_pipeline] >> rw [] >>
  `(s'.ID.ID_EX_write_enable = s.ID.ID_EX_write_enable) /\ (s'.EX.EX_func = s.EX.EX_func) /\
  (s'.EX.EX_NOP_flag = s.EX.EX_NOP_flag)`
    by METIS_TAC [agp32_same_EX_items_before_EX_pipeline,Abbr `s`,Abbr `s'`] >>
  `s'.ID.ID_func = s.ID.ID_func`
    by METIS_TAC [agp32_same_ID_items_before_EX_pipeline,Abbr `s`,Abbr `s'`] >>
  Cases_on `enable_stg 3 (agp32 fext fbits t)` >-
   (fs [is_sch_execute_def] >>
    Cases_on `isJump_hw_op (agp32 fext fbits t)` >-
     METIS_TAC [] >>
    Cases_on `reg_data_hazard (agp32 fext fbits t)` >-
     METIS_TAC [] >>
    `I' (3,SUC t) = I' (2,t)` by fs [] >> fs [] >>
    `s'.ID.ID_EX_write_enable` by fs [enable_stg_def,Abbr `s`] >>
    `~s.EX.EX_NOP_flag`
      by fs [enable_stg_def,Abbr `s`,
             agp32_ID_EX_write_enable_no_jump_or_reg_data_hazard_EX_NOP_flag_F] >>
    rw [EX_pipeline_def] >> fs [Rel_def,ID_Rel_def]) >>
  `I' (3,SUC t) = I' (3,t)` by fs [is_sch_disable_def] >>
  `~s'.ID.ID_EX_write_enable` by fs [enable_stg_def,Abbr `s`] >>
  rw [EX_pipeline_def] >>
  fs [Rel_def,EX_Rel_def]
QED

(** EX_write_reg **)
Theorem agp32_Rel_ag32_EX_write_reg_correct:
  !fext fbits a t I.
    is_sch_execute I (agp32 fext fbits) a ==>
    is_sch_disable I (agp32 fext fbits) ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (3,SUC t) <> NONE ==>
    (agp32 fext fbits (SUC t)).EX.EX_write_reg = reg_iswrite (FUNPOW Next (THE (I (3,SUC t)) − 1) a)
Proof
  rw [] >> Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state;WB_pipeline;MEM_pipeline] (fext t) s s` >>
  `(agp32 fext fbits (SUC t)).EX.EX_write_reg = (EX_pipeline (fext t) s s').EX.EX_write_reg`
    by fs [agp32_EX_write_reg_updated_by_EX_pipeline] >> rw [] >>
  `(s'.ID.ID_EX_write_enable = s.ID.ID_EX_write_enable) /\ (s'.EX.EX_write_reg = s.EX.EX_write_reg) /\
  (s'.EX.EX_NOP_flag = s.EX.EX_NOP_flag)`
    by METIS_TAC [agp32_same_EX_items_before_EX_pipeline,Abbr `s`,Abbr `s'`] >>
  `s'.ID.ID_opc = s.ID.ID_opc`
    by METIS_TAC [agp32_same_ID_items_before_EX_pipeline,Abbr `s`,Abbr `s'`] >>
  Cases_on `enable_stg 3 (agp32 fext fbits t)` >-
   (fs [is_sch_execute_def] >>
    Cases_on `isJump_hw_op (agp32 fext fbits t)` >-
     METIS_TAC [] >>
    Cases_on `reg_data_hazard (agp32 fext fbits t)` >-
     METIS_TAC [] >>
    `I' (3,SUC t) = I' (2,t)` by fs [] >> fs [] >>
    `s'.ID.ID_EX_write_enable` by fs [enable_stg_def,Abbr `s`] >>
    `~s.EX.EX_NOP_flag`
      by fs [enable_stg_def,Abbr `s`,
             agp32_ID_EX_write_enable_no_jump_or_reg_data_hazard_EX_NOP_flag_F] >>
    rw [EX_pipeline_def,reg_iswrite_def] >> fs [Rel_def,ID_Rel_def]) >> 
  `I' (3,SUC t) = I' (3,t)` by fs [is_sch_disable_def] >>
  `~s'.ID.ID_EX_write_enable` by fs [enable_stg_def,Abbr `s`] >>
  rw [EX_pipeline_def] >>
  fs [Rel_def,EX_Rel_def]
QED

(** EX_dataA/B/W **)
Theorem agp32_Rel_ag32_EX_dataA_correct:
  !fext fbits a t I.
    is_sch_execute I (agp32 fext fbits) a ==>
    is_sch_disable I (agp32 fext fbits) ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (3,SUC t) <> NONE ==>
    (agp32 fext fbits (SUC t)).EX.EX_dataA = dataA (FUNPOW Next (THE (I (3,SUC t)) − 1) a)
Proof
  rw [] >> Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state;WB_pipeline;MEM_pipeline] (fext t) s s` >>
  `(agp32 fext fbits (SUC t)).EX.EX_dataA = (EX_pipeline (fext t) s s').EX.EX_dataA`
    by fs [agp32_EX_data_updated_by_EX_pipeline] >> rw [] >>
  `(s'.ID.ID_EX_write_enable = s.ID.ID_EX_write_enable) /\
  (s'.EX.EX_dataA = s.EX.EX_dataA) /\ (s'.ID.ID_dataA = s.ID.ID_dataA)`
    by METIS_TAC [Abbr `s`,Abbr `s'`,agp32_same_EX_items_before_EX_pipeline,
                  agp32_same_ID_items_before_EX_pipeline] >>
  Cases_on `enable_stg 3 (agp32 fext fbits t)` >-
   (fs [is_sch_execute_def] >>
    Cases_on `isJump_hw_op (agp32 fext fbits t)` >-
     METIS_TAC [] >>
    Cases_on `reg_data_hazard (agp32 fext fbits t)` >-
     METIS_TAC [] >>
    `I' (3,SUC t) = I' (2,t)` by fs [] >> fs [] >>
    `s'.ID.ID_EX_write_enable` by fs [enable_stg_def,Abbr `s`] >>
    rw [EX_pipeline_def] >> fs [Rel_def,ID_Rel_def,ID_reg_data_Rel_def] >>
    Cases_on `s.ID.ID_addrA_disable` >>
    fs [reg_data_hazard_def,ID_data_dep_Rel_def] >> METIS_TAC []) >> 
  `I' (3,SUC t) = I' (3,t)` by fs [is_sch_disable_def] >>
  `~s'.ID.ID_EX_write_enable` by fs [enable_stg_def,Abbr `s`] >>
  rw [EX_pipeline_def] >>
  fs [Rel_def,EX_Rel_def]
QED

Theorem agp32_Rel_ag32_EX_dataB_correct:
  !fext fbits a t I.
    is_sch_execute I (agp32 fext fbits) a ==>
    is_sch_disable I (agp32 fext fbits) ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (3,SUC t) <> NONE ==>
    (agp32 fext fbits (SUC t)).EX.EX_dataB = dataB (FUNPOW Next (THE (I (3,SUC t)) − 1) a)
Proof
  rw [] >> Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state;WB_pipeline;MEM_pipeline] (fext t) s s` >>
  `(agp32 fext fbits (SUC t)).EX.EX_dataB = (EX_pipeline (fext t) s s').EX.EX_dataB`
    by fs [agp32_EX_data_updated_by_EX_pipeline] >> rw [] >>
  `(s'.ID.ID_EX_write_enable = s.ID.ID_EX_write_enable) /\
  (s'.EX.EX_dataB = s.EX.EX_dataB) /\ (s'.ID.ID_dataB = s.ID.ID_dataB)`
    by METIS_TAC [Abbr `s`,Abbr `s'`,agp32_same_EX_items_before_EX_pipeline,
                  agp32_same_ID_items_before_EX_pipeline] >>
  Cases_on `enable_stg 3 (agp32 fext fbits t)` >-
   (fs [is_sch_execute_def] >>
    Cases_on `isJump_hw_op (agp32 fext fbits t)` >-
     METIS_TAC [] >>
    Cases_on `reg_data_hazard (agp32 fext fbits t)` >-
     METIS_TAC [] >>
    `I' (3,SUC t) = I' (2,t)` by fs [] >> fs [] >>
    `s'.ID.ID_EX_write_enable` by fs [enable_stg_def,Abbr `s`] >>
    rw [EX_pipeline_def] >> fs [Rel_def,ID_Rel_def,ID_reg_data_Rel_def] >>
    Cases_on `s.ID.ID_addrB_disable` >>
    fs [reg_data_hazard_def,ID_data_dep_Rel_def] >> METIS_TAC []) >> 
  `I' (3,SUC t) = I' (3,t)` by fs [is_sch_disable_def] >>
  `~s'.ID.ID_EX_write_enable` by fs [enable_stg_def,Abbr `s`] >>
  rw [EX_pipeline_def] >>
  fs [Rel_def,EX_Rel_def]
QED

Theorem agp32_Rel_ag32_EX_dataW_correct:
  !fext fbits a t I.
    is_sch_execute I (agp32 fext fbits) a ==>
    is_sch_disable I (agp32 fext fbits) ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (3,SUC t) <> NONE ==>
    (agp32 fext fbits (SUC t)).EX.EX_dataW = dataW (FUNPOW Next (THE (I (3,SUC t)) − 1) a)
Proof
  rw [] >> Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state;WB_pipeline;MEM_pipeline] (fext t) s s` >>
  `(agp32 fext fbits (SUC t)).EX.EX_dataW = (EX_pipeline (fext t) s s').EX.EX_dataW`
    by fs [agp32_EX_data_updated_by_EX_pipeline] >> rw [] >>
  `(s'.ID.ID_EX_write_enable = s.ID.ID_EX_write_enable) /\
  (s'.EX.EX_dataW = s.EX.EX_dataW) /\ (s'.ID.ID_dataW = s.ID.ID_dataW)`
    by METIS_TAC [Abbr `s`,Abbr `s'`,agp32_same_EX_items_before_EX_pipeline,
                  agp32_same_ID_items_before_EX_pipeline] >>
  Cases_on `enable_stg 3 (agp32 fext fbits t)` >-
   (fs [is_sch_execute_def] >>
    Cases_on `isJump_hw_op (agp32 fext fbits t)` >-
     METIS_TAC [] >>
    Cases_on `reg_data_hazard (agp32 fext fbits t)` >-
     METIS_TAC [] >>
    `I' (3,SUC t) = I' (2,t)` by fs [] >> fs [] >>
    `s'.ID.ID_EX_write_enable` by fs [enable_stg_def,Abbr `s`] >>
    rw [EX_pipeline_def] >> fs [Rel_def,ID_Rel_def,ID_reg_data_Rel_def] >>
    Cases_on `s.ID.ID_addrW_disable` >>
    fs [reg_data_hazard_def,ID_data_dep_Rel_def] >> METIS_TAC []) >> 
  `I' (3,SUC t) = I' (3,t)` by fs [is_sch_disable_def] >>
  `~s'.ID.ID_EX_write_enable` by fs [enable_stg_def,Abbr `s`] >>
  rw [EX_pipeline_def] >>
  fs [Rel_def,EX_Rel_def]
QED

(** EX_imm_updated **)
(** when opc is not 14w **)
Theorem agp32_Rel_ag32_EX_imm_updated_correct_not_LoadUpperConstant:
  !fext fbits a t I.
    is_sch_execute I (agp32 fext fbits) a ==>
    is_sch_disable I (agp32 fext fbits) ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (3,SUC t) <> NONE ==>
    (agp32 fext fbits (SUC t)).EX.EX_opc <> 14w ==>
    (agp32 fext fbits (SUC t)).EX.EX_imm_updated = imm (FUNPOW Next (THE (I (3,SUC t)) − 1) a)
Proof
  rw [] >> Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state;WB_pipeline;MEM_pipeline;EX_pipeline;
                            REG_write;ID_pipeline;IF_PC_update;Acc_compute] (fext t) s s` >>
  Q.ABBREV_TAC `s'' = procs [IF_instr_update;ID_opc_func_update;ID_imm_update;ID_data_update;
                             ID_data_check_update] (fext (SUC t)) s' s'` >>
  `(agp32 fext fbits (SUC t)).EX.EX_imm_updated =
  (EX_ALU_input_imm_update (fext (SUC t)) s' s'').EX.EX_imm_updated`
    by fs [agp32_EX_imm_updated_updated_by_EX_ALU_input_imm_update] >>
  `s'.EX.EX_opc = (agp32 fext fbits (SUC t)).EX.EX_opc`
    by fs [agp32_same_EX_pipeline_items_after_EX_pipeline] >>
  `s''.EX.EX_imm = (agp32 fext fbits (SUC t)).EX.EX_imm`
    by METIS_TAC [Abbr `s`,Abbr `s'`,Abbr `s''`,agp32_same_items_after_ID_data_check_update] >>
  fs [EX_ALU_input_imm_update_def,MUX_21_def] >>
  METIS_TAC [agp32_Rel_ag32_EX_imm_correct]
QED

(** when opc is 14w **)
Theorem agp32_Rel_ag32_EX_imm_updated_correct_LoadUpperConstant:
  !fext fbits a t I.
    is_sch_execute I (agp32 fext fbits) a ==>
    is_sch_disable I (agp32 fext fbits) ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (3,SUC t) <> NONE ==>
    (agp32 fext fbits (SUC t)).EX.EX_opc = 14w ==>
    (agp32 fext fbits (SUC t)).EX.EX_imm_updated =
    (8 >< 0) (imm (FUNPOW Next (THE (I (3,SUC t)) − 1) a)) @@
             (22 >< 0) (dataW (FUNPOW Next (THE (I (3,SUC t)) − 1) a))
Proof
  rw [] >> Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state;WB_pipeline;MEM_pipeline;EX_pipeline;
                            REG_write;ID_pipeline;IF_PC_update;Acc_compute] (fext t) s s` >>
  Q.ABBREV_TAC `s'' = procs [IF_instr_update;ID_opc_func_update;ID_imm_update;ID_data_update;
                             ID_data_check_update] (fext (SUC t)) s' s'` >>
  `(agp32 fext fbits (SUC t)).EX.EX_imm_updated =
  (EX_ALU_input_imm_update (fext (SUC t)) s' s'').EX.EX_imm_updated`
    by fs [agp32_EX_imm_updated_updated_by_EX_ALU_input_imm_update] >>
  `s'.EX.EX_opc = (agp32 fext fbits (SUC t)).EX.EX_opc`
    by fs [agp32_same_EX_pipeline_items_after_EX_pipeline] >>
  `(s''.EX.EX_imm = (agp32 fext fbits (SUC t)).EX.EX_imm) /\
  (s''.EX.EX_dataW = (agp32 fext fbits (SUC t)).EX.EX_dataW)`
    by METIS_TAC [Abbr `s`,Abbr `s'`,Abbr `s''`,agp32_same_items_after_ID_data_check_update] >>
  fs [EX_ALU_input_imm_update_def,MUX_21_def] >>
  METIS_TAC [agp32_Rel_ag32_EX_imm_correct,agp32_Rel_ag32_EX_dataW_correct]
QED

(** EX_ALU_input **)
Theorem agp32_Rel_ag32_EX_ALU_input1_correct:
  !fext fbits a t I.
    is_sch_execute I (agp32 fext fbits) a ==>
    is_sch_disable I (agp32 fext fbits) ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (3,SUC t) <> NONE ==>
    (agp32 fext fbits (SUC t)).EX.EX_ALU_input1 = ALU_input1 (FUNPOW Next (THE (I (3,SUC t)) − 1) a)
Proof
  rw [] >> Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state;WB_pipeline;MEM_pipeline;EX_pipeline;
                            REG_write;ID_pipeline;IF_PC_update;Acc_compute] (fext t) s s` >>
  Q.ABBREV_TAC `s'' = procs [IF_instr_update;ID_opc_func_update;ID_imm_update;ID_data_update;
                             ID_data_check_update] (fext (SUC t)) s' s'` >>
  `(agp32 fext fbits (SUC t)).EX.EX_ALU_input1 =
  (EX_ALU_input_imm_update (fext (SUC t)) s' s'').EX.EX_ALU_input1`
    by fs [agp32_EX_ALU_input_updated_by_EX_ALU_input_imm_update] >>
  `(s'.EX.EX_opc = (agp32 fext fbits (SUC t)).EX.EX_opc) /\
  (s'.EX.EX_PC = (agp32 fext fbits (SUC t)).EX.EX_PC) /\
  (s'.EX.EX_dataA = (agp32 fext fbits (SUC t)).EX.EX_dataA)`
    by fs [agp32_same_EX_pipeline_items_after_EX_pipeline] >>
  fs [EX_ALU_input_imm_update_def,ALU_input1_def,MUX_21_def] >>
  METIS_TAC [agp32_Rel_ag32_EX_opc_correct,agp32_Rel_ag32_EX_dataA_correct,
             agp32_Rel_ag32_EX_PC_correct]
QED

Theorem agp32_Rel_ag32_EX_ALU_input2_correct:
  !fext fbits a t I.
    is_sch_execute I (agp32 fext fbits) a ==>
    is_sch_disable I (agp32 fext fbits) ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (3,SUC t) <> NONE ==>
    (agp32 fext fbits (SUC t)).EX.EX_ALU_input2 = ALU_input2 (FUNPOW Next (THE (I (3,SUC t)) − 1) a)
Proof
  rw [] >> Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state;WB_pipeline;MEM_pipeline;EX_pipeline;
                            REG_write;ID_pipeline;IF_PC_update;Acc_compute] (fext t) s s` >>
  Q.ABBREV_TAC `s'' = procs [IF_instr_update;ID_opc_func_update;ID_imm_update;ID_data_update;
                             ID_data_check_update] (fext (SUC t)) s' s'` >>
  `(agp32 fext fbits (SUC t)).EX.EX_ALU_input2 =
  (EX_ALU_input_imm_update (fext (SUC t)) s' s'').EX.EX_ALU_input2`
    by fs [agp32_EX_ALU_input_updated_by_EX_ALU_input_imm_update] >>
  `(s'.EX.EX_opc = (agp32 fext fbits (SUC t)).EX.EX_opc) /\
  (s'.EX.EX_dataA = (agp32 fext fbits (SUC t)).EX.EX_dataA) /\
  (s'.EX.EX_dataB = (agp32 fext fbits (SUC t)).EX.EX_dataB)`
    by fs [agp32_same_EX_pipeline_items_after_EX_pipeline] >>
  fs [EX_ALU_input_imm_update_def,ALU_input2_def,MUX_21_def] >>
  METIS_TAC [agp32_Rel_ag32_EX_opc_correct,agp32_Rel_ag32_EX_dataA_correct,
             agp32_Rel_ag32_EX_dataB_correct]
QED

(** EX_ALU_res **)
Theorem agp32_Rel_ag32_EX_ALU_res_correct:
  !fext fbits a t I.
    is_sch I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (3,SUC t) <> NONE ==>
    (agp32 fext fbits (SUC t)).EX.EX_ALU_res = ALU_res (FUNPOW Next (THE (I (3,SUC t)) − 1) a)
Proof
  rw [] >> Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state;WB_pipeline;MEM_pipeline;EX_pipeline;
                            REG_write;ID_pipeline;IF_PC_update;Acc_compute] (fext t) s s` >>
  Q.ABBREV_TAC `s'' = procs [IF_instr_update;ID_opc_func_update;ID_imm_update;ID_data_update;
                             ID_data_check_update;EX_ALU_input_imm_update] (fext (SUC t)) s' s'` >>
  `(agp32 fext fbits (SUC t)).EX.EX_ALU_res = (EX_ALU_update (fext (SUC t)) s' s'').EX.EX_ALU_res`
    by fs [agp32_EX_ALU_items_updated_by_EX_ALU_update] >>
  `(s''.ID.ID_EX_write_enable = s.ID.ID_EX_write_enable) /\
  (s''.EX.EX_overflow_flag = s.EX.EX_overflow_flag) /\
  (s''.EX.EX_carry_flag = s.EX.EX_carry_flag) /\
  (s''.EX.EX_ALU_res = s.EX.EX_ALU_res)`
    by METIS_TAC [agp32_same_items_until_EX_ALU_update,Abbr `s`,Abbr `s'`,Abbr `s''`] >>
  `(s''.EX.EX_ALU_input1 = (agp32 fext fbits (SUC t)).EX.EX_ALU_input1) /\
  (s''.EX.EX_ALU_input2 = (agp32 fext fbits (SUC t)).EX.EX_ALU_input2) /\
  (s''.EX.EX_func = (agp32 fext fbits (SUC t)).EX.EX_func)`
    by METIS_TAC [agp32_same_EX_ALU_input_until_ALU_update,agp32_same_EX_opc_func_until_ALU_update,
                  Abbr `s`,Abbr `s'`,Abbr `s''`] >>
  Cases_on `enable_stg 3 (agp32 fext fbits t)` >-
   (`s''.ID.ID_EX_write_enable` by fs [enable_stg_def,Abbr `s`] >>
    `s''.EX.EX_func = func (FUNPOW Next (THE (I' (3,SUC t)) − 1) a)`
      by fs [is_sch_def,agp32_Rel_ag32_EX_func_correct] >>
    `s''.EX.EX_ALU_input1 = ALU_input1 (FUNPOW Next (THE (I' (3,SUC t)) − 1) a)`
      by fs [is_sch_def,agp32_Rel_ag32_EX_ALU_input1_correct] >>
    `s''.EX.EX_ALU_input2 = ALU_input2 (FUNPOW Next (THE (I' (3,SUC t)) − 1) a)`
      by fs [is_sch_def,agp32_Rel_ag32_EX_ALU_input2_correct] >>
    fs [EX_ALU_update_def,ALU_res_def,ALU_def] >>
    Cases_on_word_value `(agp32 fext fbits (SUC t)).EX.EX_func` >> fs [] >-
     (simp [word_mul_def,w2n_w2w] >> BBLAST_TAC) >-
     (Cases_on `I' (3,t) <> NONE` >-
       (fs [Rel_def] >>
        `THE (I' (3,SUC t)) = THE (I' (3,t)) + 1`
          by METIS_TAC [EX_instr_index_t_SUC_t_enable] >> fs []) >>
      fs [is_sch_def,is_sch_execute_def] >>
      Cases_on `isJump_hw_op (agp32 fext fbits t)` >-
       METIS_TAC [] >>
      Cases_on `reg_data_hazard (agp32 fext fbits t)` >-
       METIS_TAC [] >>
      `I' (3,SUC t) = I' (2,t)` by fs [] >> fs [Rel_def]) >-
     (Cases_on `I' (3,t) <> NONE` >-
       (fs [Rel_def] >>
        `THE (I' (3,SUC t)) = THE (I' (3,t)) + 1`
          by METIS_TAC [EX_instr_index_t_SUC_t_enable] >> fs []) >>
      fs [is_sch_def,is_sch_execute_def] >>
      Cases_on `isJump_hw_op (agp32 fext fbits t)` >-
       METIS_TAC [] >>
      Cases_on `reg_data_hazard (agp32 fext fbits t)` >-
       METIS_TAC [] >>
      `I' (3,SUC t) = I' (2,t)` by fs [] >> fs [Rel_def]) >-
     (subgoal `s.EX.EX_carry_flag = (FUNPOW Next (THE (I' (3,SUC t)) − 1) a).CarryFlag` >-
       (Cases_on `I' (3,t) <> NONE` >-
         (fs [Rel_def] >>
          `THE (I' (3,SUC t)) = THE (I' (3,t)) + 1`
            by METIS_TAC [EX_instr_index_t_SUC_t_enable] >> fs []) >>
        fs [is_sch_def,is_sch_execute_def] >>
        Cases_on `isJump_hw_op (agp32 fext fbits t)` >-
         METIS_TAC [] >>
        Cases_on `reg_data_hazard (agp32 fext fbits t)` >-
         METIS_TAC [] >>
        `I' (3,SUC t) = I' (2,t)` by fs [] >> fs [Rel_def]) >>
      rw [ALU_correct_v2w_carry33_lem,ALU_correct_v2w_carry32_lem] >>
      BBLAST_TAC) >>
    BBLAST_TAC) >>
  `I' (3,SUC t) = I' (3,t)` by fs [is_sch_def,is_sch_disable_def] >>
  `~s''.ID.ID_EX_write_enable` by fs [enable_stg_def,Abbr `s`] >>
  rw [EX_ALU_update_def] >>
  fs [Rel_def,EX_Rel_def]
QED

(** EX_SHIFT_res **)
Theorem agp32_Rel_ag32_EX_SHIFT_res_correct:
  !fext fbits a t I.
    is_sch I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (3,SUC t) <> NONE ==>
    (agp32 fext fbits (SUC t)).EX.EX_opc = 1w ==>
    (agp32 fext fbits (SUC t)).EX.EX_SHIFT_res = shift_res (FUNPOW Next (THE (I (3,SUC t)) − 1) a)
Proof
  rw [] >> Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state;WB_pipeline;MEM_pipeline;EX_pipeline;
                            REG_write;ID_pipeline;IF_PC_update;Acc_compute] (fext t) s s` >>
  Q.ABBREV_TAC `s'' = procs [IF_instr_update;ID_opc_func_update;ID_imm_update;
                             ID_data_update;ID_data_check_update;
                             EX_ALU_input_imm_update;EX_ALU_update] (fext (SUC t)) s' s'` >>
  `(agp32 fext fbits (SUC t)).EX.EX_SHIFT_res =
  (EX_SHIFT_update (fext (SUC t)) s' s'').EX.EX_SHIFT_res`
    by fs [agp32_EX_SHIFT_res_updated_by_EX_SHIFT_update] >>
   `(s''.ID.ID_EX_write_enable = s.ID.ID_EX_write_enable) /\
  (s''.EX.EX_SHIFT_res = s.EX.EX_SHIFT_res)`
    by METIS_TAC [Abbr `s`,Abbr `s'`,Abbr `s''`,agp32_same_items_until_EX_SHIFT_update] >>
  `(s'.EX.EX_dataA = (agp32 fext fbits (SUC t)).EX.EX_dataA) /\
  (s'.EX.EX_dataB = (agp32 fext fbits (SUC t)).EX.EX_dataB) /\
  (s'.EX.EX_opc = (agp32 fext fbits (SUC t)).EX.EX_opc)`
    by METIS_TAC [Abbr `s`,Abbr `s'`,agp32_same_EX_pipeline_items_after_EX_pipeline] >>
  `s''.EX.EX_func = (agp32 fext fbits (SUC t)).EX.EX_func`      
    by METIS_TAC [Abbr `s`,Abbr `s'`,Abbr `s''`,agp32_same_EX_func_after_EX_ALU_update] >>
  Cases_on `enable_stg 3 (agp32 fext fbits t)` >-
   (`s''.ID.ID_EX_write_enable` by fs [enable_stg_def,Abbr `s`] >>
    `s'.EX.EX_opc = opc (FUNPOW Next (THE (I' (3,SUC t)) − 1) a)`
      by METIS_TAC [is_sch_def,agp32_Rel_ag32_EX_opc_correct] >>
    `s''.EX.EX_func = func (FUNPOW Next (THE (I' (3,SUC t)) − 1) a)`
      by fs [is_sch_def,agp32_Rel_ag32_EX_func_correct] >>
    `s'.EX.EX_dataA = dataA (FUNPOW Next (THE (I' (3,SUC t)) − 1) a)`
      by fs [is_sch_def,agp32_Rel_ag32_EX_dataA_correct] >>
    `s'.EX.EX_dataB = dataB (FUNPOW Next (THE (I' (3,SUC t)) − 1) a)`
      by fs [is_sch_def,agp32_Rel_ag32_EX_dataB_correct] >>
    fs [EX_SHIFT_update_def,shift_res_def,shift_def] >>
    qpat_abbrev_tac `a' = FUNPOW Next _ _` >>
    `(1 >< 0) (agp32 fext fbits (SUC t)).EX.EX_func = (7 >< 6) (instr a')`
      by METIS_TAC [ag32_func_for_SHIFT] >> fs [] >>
    Cases_on_word_value `(7 >< 6) (instr a')` >> fs [] >>
    once_rewrite_tac [word_ror_intro_mod] >> simp [] >>
    DEP_REWRITE_TAC [word_ror_impl] >> simp [] >>
    rw [word_mod_def,WORD_LO,MOD_MOD_lt]) >>
  `I' (3,SUC t) = I' (3,t)` by fs [is_sch_def,is_sch_disable_def] >>
  `~s''.ID.ID_EX_write_enable` by fs [enable_stg_def,Abbr `s`] >>
  `(agp32 fext fbits (SUC t)).EX.EX_opc = (agp32 fext fbits t).EX.EX_opc`
    by fs [agp32_EX_opc_unchanged_when_EX_disabled,enable_stg_def] >>
  rw [EX_SHIFT_update_def] >>
  fs [Rel_def,EX_Rel_def]
QED


(* EX Rel *)
Theorem agp32_Rel_ag32_EX_Rel_correct:
  !fext fbits a t I.
    is_sch I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (3,SUC t) <> NONE ==>
    EX_Rel (fext (SUC t)) (agp32 fext fbits (SUC t)) a (THE (I (3,SUC t)))
Proof
  rw [EX_Rel_def] >>
  fs [is_sch_def,agp32_Rel_ag32_EX_PC_correct,agp32_Rel_ag32_EX_addrW_correct,
      agp32_Rel_ag32_EX_imm_correct,agp32_Rel_ag32_EX_opc_correct,
      agp32_Rel_ag32_EX_func_correct,agp32_Rel_ag32_EX_write_reg_correct,
      agp32_Rel_ag32_EX_dataA_correct,agp32_Rel_ag32_EX_dataB_correct,
      agp32_Rel_ag32_EX_dataW_correct,agp32_Rel_ag32_EX_imm_updated_correct_not_LoadUpperConstant,
      agp32_Rel_ag32_EX_imm_updated_correct_LoadUpperConstant,
      agp32_Rel_ag32_EX_ALU_input1_correct,agp32_Rel_ag32_EX_ALU_input2_correct,
      agp32_Rel_ag32_EX_ALU_res_correct,agp32_Rel_ag32_EX_SHIFT_res_correct]
QED


(** EX_jump_sel **)
Theorem agp32_Rel_ag32_EX_jump_sel_correct:
  !fext fbits a t I.
    is_sch I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    (agp32 fext fbits (SUC t)).EX.EX_jump_sel = isJump_isa_op (I (3,SUC t)) a
Proof
  rw [isJump_isa_op_def] >>
  Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state;WB_pipeline;MEM_pipeline;EX_pipeline;
                            REG_write;ID_pipeline;IF_PC_update;Acc_compute] (fext t) s s` >>
  Q.ABBREV_TAC `s'' = procs [IF_instr_update;ID_opc_func_update;ID_imm_update;
                             ID_data_update;ID_data_check_update;
                             EX_ALU_input_imm_update;EX_ALU_update;EX_SHIFT_update] (fext (SUC t)) s' s'` >>
  `(agp32 fext fbits (SUC t)).EX.EX_jump_sel =
  (EX_jump_sel_addr_update (fext (SUC t)) s' s'').EX.EX_jump_sel`
    by fs [agp32_EX_jump_items_updated_by_EX_jump_sel_addr_update] >>
  `s''.EX.EX_ALU_res = (agp32 fext fbits (SUC t)).EX.EX_ALU_res`
    by METIS_TAC [Abbr `s`,Abbr `s'`,Abbr `s''`,agp32_same_EX_items_after_EX_SHIFT_update] >>
  `s'.EX.EX_opc = (agp32 fext fbits (SUC t)).EX.EX_opc`
    by METIS_TAC [Abbr `s`,Abbr `s'`,agp32_same_EX_pipeline_items_after_EX_pipeline] >>
  Cases_on `I' (3,SUC t) = NONE` >> fs [] >-
   (fs [EX_jump_sel_addr_update_def] >> rw [] >>
    `((agp32 fext fbits (SUC t)).EX.EX_opc = 16w) \/ ((agp32 fext fbits (SUC t)).EX.EX_opc = 15w)`
      by METIS_TAC [EX_instr_index_NONE_opc_flush] >> fs []) >>
  rw [isJump_isa_def,EX_jump_sel_addr_update_def] >-
   (fs [is_sch_def] >> METIS_TAC [agp32_Rel_ag32_EX_opc_correct]) >-
   METIS_TAC [is_sch_def,agp32_Rel_ag32_EX_opc_correct,agp32_Rel_ag32_EX_ALU_res_correct] >-
   METIS_TAC [is_sch_def,agp32_Rel_ag32_EX_opc_correct,agp32_Rel_ag32_EX_ALU_res_correct] >-
   (fs [is_sch_def] >> METIS_TAC [agp32_Rel_ag32_EX_opc_correct]) >-
   (`(agp32 fext fbits (SUC t)).EX.EX_opc = 10w`
      by METIS_TAC [is_sch_def,agp32_Rel_ag32_EX_opc_correct] >>
    fs [] >> METIS_TAC [agp32_Rel_ag32_EX_ALU_res_correct]) >>
  `(agp32 fext fbits (SUC t)).EX.EX_opc = 11w`
    by METIS_TAC [is_sch_def,agp32_Rel_ag32_EX_opc_correct] >>
  fs [] >> METIS_TAC [agp32_Rel_ag32_EX_ALU_res_correct]
QED

(** EX_jump_sel **)
Theorem agp32_Rel_ag32_EX_jump_addr_correct:
  !fext fbits a t I.
    is_sch I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    (agp32 fext fbits (SUC t)).EX.EX_jump_sel ==>
    (agp32 fext fbits (SUC t)).EX.EX_jump_addr = (FUNPOW Next (THE (I (3,SUC t))) a).PC
Proof
  rw [] >> `isJump_isa_op (I' (3,SUC t)) a` by METIS_TAC [agp32_Rel_ag32_EX_jump_sel_correct] >>
  Cases_on `I' (3,SUC t) = NONE` >> fs [isJump_isa_op_def] >>
  Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state;WB_pipeline;MEM_pipeline;EX_pipeline;
                            REG_write;ID_pipeline;IF_PC_update;Acc_compute] (fext t) s s` >>
  Q.ABBREV_TAC `s'' = procs [IF_instr_update;ID_opc_func_update;ID_imm_update;
                             ID_data_update;ID_data_check_update;
                             EX_ALU_input_imm_update;EX_ALU_update;EX_SHIFT_update] (fext (SUC t)) s' s'` >>
  `(agp32 fext fbits (SUC t)).EX.EX_jump_addr =
  (EX_jump_sel_addr_update (fext (SUC t)) s' s'').EX.EX_jump_addr`
    by fs [agp32_EX_jump_items_updated_by_EX_jump_sel_addr_update] >>
  `s''.EX.EX_ALU_res = (agp32 fext fbits (SUC t)).EX.EX_ALU_res /\
  s''.EX.EX_dataW = (agp32 fext fbits (SUC t)).EX.EX_dataW`
    by METIS_TAC [Abbr `s`,Abbr `s'`,Abbr `s''`,agp32_same_EX_items_after_EX_SHIFT_update] >>
  `s'.EX.EX_PC = (agp32 fext fbits (SUC t)).EX.EX_PC /\
  s'.EX.EX_opc = (agp32 fext fbits (SUC t)).EX.EX_opc`
    by METIS_TAC [Abbr `s`,Abbr `s'`,agp32_same_EX_pipeline_items_after_EX_pipeline] >>
  Cases_on `THE (I' (3,SUC t))` >-
   METIS_TAC [EX_instr_index_not_0] >>
  `(agp32 fext fbits (SUC t)).EX.EX_opc = opc (FUNPOW Next (SUC n -1) a)`
    by METIS_TAC [is_sch_def,agp32_Rel_ag32_EX_opc_correct] >>
  `(agp32 fext fbits (SUC t)).EX.EX_ALU_res = ALU_res (FUNPOW Next (SUC n -1) a)`
    by METIS_TAC [agp32_Rel_ag32_EX_ALU_res_correct] >>
  `(agp32 fext fbits (SUC t)).EX.EX_PC = (FUNPOW Next (SUC n -1) a).PC`
    by METIS_TAC [is_sch_def,agp32_Rel_ag32_EX_PC_correct] >>
  `(agp32 fext fbits (SUC t)).EX.EX_dataW = dataW (FUNPOW Next (SUC n -1) a)`
    by METIS_TAC [is_sch_def,agp32_Rel_ag32_EX_dataW_correct] >>
  fs [FUNPOW_SUC,isJump_isa_def] >>
  Q.ABBREV_TAC `an = FUNPOW Next n a` >-
   (`(Next an).PC = ALU_res an` by METIS_TAC [ag32_Jump_Next_PC_ALU_res] >>
    fs [EX_jump_sel_addr_update_def]) >-
   (`(Next an).PC = an.PC + (dataW an)`
      by METIS_TAC [ag32_JumpIfZero_Next_PC_PC_and_dataW] >>
    fs [EX_jump_sel_addr_update_def]) >>
  `(Next an).PC = an.PC + (dataW an)`
    by METIS_TAC [ag32_JumpIfNotZero_Next_PC_PC_and_dataW] >>
  fs [EX_jump_sel_addr_update_def]
QED


(* EX Rel_spec: for jumps *)
Theorem agp32_Rel_ag32_EX_Rel_spec_correct:
  !fext fbits a t I.
    is_sch I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    EX_Rel_spec (agp32 fext fbits (SUC t)) a (I (3,SUC t))
Proof
  rw [EX_Rel_spec_def] >>
  fs [agp32_Rel_ag32_EX_jump_sel_correct,agp32_Rel_ag32_EX_jump_addr_correct]
QED


val _ = export_theory ();
