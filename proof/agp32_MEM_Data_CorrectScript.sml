open hardwarePreamble translatorTheory translatorLib arithmeticTheory pred_setTheory wordsExtraTheory dep_rewrite blastLib bitstringSyntax fcpSyntax listSyntax wordsSyntax agp32StateTheory agp32EnvironmentTheory agp32ProcessorTheory ag32Theory ag32ExtraTheory ag32UtilitiesTheory agp32RelationTheory agp32UpdateTheory agp32InternalTheory agp32SpecialTheory agp32StepLib agp32_MEM_CorrectTheory;

(* correctness of memory requests with respect to the ISA *)
val _ = new_theory "agp32_MEM_Data_Correct";

val _ = prefer_num ();
val _ = guess_lengths ();


(** lemma **)
Theorem WB_opc_unchanged_after_disabled_cycles[local]:
  !fext fbits m n.
    (!p. p < m ==> ~(fext (p + n)).ready) ==>
    (agp32 fext fbits (m + n)).WB.WB_opc = (agp32 fext fbits n).WB.WB_opc
Proof
  rw [] >> Induct_on `m` >> rw [] >>
  `!p. p < m ==> ~(fext (n + p)).ready` by fs [] >> fs [] >>
  `m < SUC m` by rw [] >>
  `~(fext (n + m)).ready` by fs [] >>
  `~(agp32 fext fbits (n + m)).WB.WB_state_flag`
    by METIS_TAC [agp32_WB_state_flag_and_fext_ready] >>
  `(agp32 fext fbits (SUC (n + m))).WB.WB_opc = (agp32 fext fbits (n + m)).WB.WB_opc`
    by fs [agp32_WB_opc_unchanged_when_WB_disabled,enable_stg_def] >>
  `n + SUC m = SUC (n + m)` by rw [] >> rw [] >> fs []
QED

Theorem data_addr_wdata_wstrb_unchanged_after_disabled_cycles[local]:
  !fext fbits m n.
    (!p. p < m ==> ~(fext (p + n)).ready) ==>
    ((agp32 fext fbits (m + n)).data_addr = (agp32 fext fbits n).data_addr) /\
    ((agp32 fext fbits (m + n)).data_wdata = (agp32 fext fbits n).data_wdata) /\
    ((agp32 fext fbits (m + n)).data_wstrb = (agp32 fext fbits n).data_wstrb)
Proof
  rw [] >> Induct_on `m` >> rw [] >>
  `!p. p < m ==> ~(fext (n + p)).ready` by fs [] >> fs [] >>
  `m < SUC m` by rw [] >>
  `~(fext (n + m)).ready` by fs [] >>
  `~(agp32 fext fbits (n + m)).WB.WB_state_flag`
    by METIS_TAC [agp32_WB_state_flag_and_fext_ready] >>
  `(agp32 fext fbits (SUC (n + m))).data_addr = (agp32 fext fbits (n + m)).data_addr /\
  (agp32 fext fbits (SUC (n + m))).data_wdata = (agp32 fext fbits (n + m)).data_wdata /\
  (agp32 fext fbits (SUC (n + m))).data_wstrb = (agp32 fext fbits (n + m)).data_wstrb`
    by fs [agp32_data_addr_wstrb_wdata_unchanged_when_WB_disabled,enable_stg_def] >>
  `n + SUC m = SUC (n + m)` by rw [] >> rw [] >> fs []
QED

Theorem WB_opc_unchanged_after_disabled_cycles_0[local]:
  !fext fbits m.
    (!p. p < m ==> ~(fext p).ready) ==>
    (agp32 fext fbits m).WB.WB_opc = (agp32 fext fbits 0).WB.WB_opc
Proof
  rw [] >> `!p. p < m ==> ~(fext (p + 0)).ready` by fs [] >>
  `(agp32 fext fbits (m + 0)).WB.WB_opc = (agp32 fext fbits 0).WB.WB_opc`
    by fs [WB_opc_unchanged_after_disabled_cycles] >> fs []
QED

Theorem EMPTY_no_fext_ready_cycle[local]:
  !t fext.
    {t0 | t0 < t /\ (fext t0).ready} = {} ==>
    (!t0. t0 < t ==> ~(fext t0).ready)
Proof
  rw [] >> Cases_on `(fext t0).ready` >> rw [] >>
  `t0 IN {t0 | t0 < t /\ (fext t0).ready}` by fs [] >>
  METIS_TAC [MEMBER_NOT_EMPTY]
QED

Theorem MAX_SET_0_no_fext_ready_cycle[local]:
  !t fext.
    {t0 | t0 < t /\ (fext t0).ready} <> {} ==>
    MAX_SET {t0 | t0 < t /\ (fext t0).ready} = 0 ==>
    (!t0. t0 < t - 1 ==> ~(fext (t0 + 1)).ready)
Proof
  rw [] >>
  `FINITE {t0 | t0 < t /\ (fext t0).ready}` by rw [FINITE_max_ready_cycle] >>
  Cases_on `(fext (t0 + 1)).ready` >> rw [] >>
  `t0 + 1  < t` by fs [] >>
  `t0 + 1 IN {t0 | t0 < t /\ (fext t0).ready}` by fs [] >>
  `t0 + 1 <= 0` by METIS_TAC [MAX_SET_DEF] >> rw []
QED

Theorem same_mem_t_SUC_t_under_MAX_SET[local]:
  !fext t m n.
    MAX_SET {t0 | t0 < t /\ (fext t0).ready} = n ==>
    (!p. p < m ==> ~(fext (p + (SUC n))).ready /\ (fext (p + SUC n)).mem = (fext n).mem) ==>
    (fext (m + SUC n)).ready ==>
    ~(fext t).ready ==>
    ~(fext (SUC t)).ready ==>
    n <> 0 ==>
    (fext t).mem = (fext (SUC t)).mem
Proof
  rpt strip_tac >>
  `FINITE {t0 | t0 < t /\ (fext t0).ready}` by fs [FINITE_max_ready_cycle] >>
  Cases_on `{t0 | t0 < t /\ (fext t0).ready} = {}` >> fs [MAX_SET_DEF] >>
  `n IN {t0 | t0 < t /\ (fext t0).ready}` by METIS_TAC [MAX_SET_DEF] >>
  fs [MAX_SET_DEF] >>
  Cases_on `m + SUC n = SUC t` >> fs [] >>
  Cases_on `SUC t > m + SUC n` >-
   (Cases_on `t = m + SUC n` >> fs [] >>
    Cases_on `t > m + SUC n` >>
    (`(m + SUC n) IN {t0 | t0 < t /\ (fext t0).ready}` by fs [] >>
     `(m + SUC n) <= n` by METIS_TAC [MAX_SET_DEF] >> fs []) >> fs []) >>
  `SUC t < m + SUC n /\ t < m + SUC n` by fs [] >>
  `SUC t -SUC n < m /\ t - SUC n < m` by rw [] >>   
  `(fext (SUC t -SUC n + SUC n)).mem = (fext n).mem /\
  (fext (t -SUC n + SUC n)).mem = (fext n).mem` by fs [] >>
  `SUC t -SUC n + SUC n = SUC t /\ t - SUC n + SUC n = t` by rw [] >> METIS_TAC []
QED

Theorem same_mem_t_SUC_t_under_MAX_SET_0[local]:
  !fext t m n.
    MAX_SET {t0 | t0 < t /\ (fext t0).ready} = 0 ==>
    (!p. p < m ==> ~(fext (p + 1)).ready /\ (fext 0).mem = (fext (p + 1)).mem) ==>
    (fext (m + 1)).ready ==>
    ~(fext t).ready ==>
    ~(fext (SUC t)).ready ==>
    (fext t).mem = (fext (SUC t)).mem
Proof
  rw [ADD1] >> Cases_on `m = t` >> fs [] >>
  Cases_on `t > m` >-
   (Cases_on `t = m + 1` >> fs [] >>
    `{t0 | t0 < t /\ (fext t0).ready} (m + 1)` by fs [] >>
    Cases_on `{t0 | t0 < t /\ (fext t0).ready} = {}` >-
     METIS_TAC [EMPTY_applied] >>
    `FINITE {t0 | t0 < t /\ (fext t0).ready}` by rw [FINITE_max_ready_cycle] >>
    `(m + 1) IN {t0 | t0 < t /\ (fext t0).ready}` by fs [] >>
    `m + 1 <= 0` by METIS_TAC [MAX_SET_DEF] >> fs []) >>
  `t < m` by fs [] >>
  `t - 1 < m` by fs [] >>   
  `(fext (t + 1)).mem = (fext 0).mem /\ (fext (t - 1 + 1)).mem = (fext 0).mem` by fs [] >>
  Cases_on `t` >> fs [ADD1]
QED


(** memory **)
(** WB **)
(** WB enabled **)
Theorem agp32_Rel_ag32_fext_MEM_correct_WB_not_NONE_WB_enable:
  !fext fbits a t I.
    is_mem fext_accessor_circuit (agp32 fext fbits) fext ==>
    is_sch I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (5,SUC t) <> NONE ==>
    (fext (SUC t)).ready ==>
    enable_stg 5 (agp32 fext fbits t) ==>
    (fext (SUC t)).mem = (FUNPOW Next (THE (I (5,SUC t))) a).MEM
Proof
  rw [] >> `I' (5,SUC t) = I' (4,t)` by fs [is_sch_def,is_sch_writeback_def] >>
  `(fext t).ready` by (fs [enable_stg_def] >> METIS_TAC [agp32_WB_state_flag_and_fext_ready]) >>
  Cases_on `I' (5,t) <> NONE` >> fs [] >-
   (Cases_on `~is_wrMEM_isa (FUNPOW Next (THE (I' (4,t)) - 1) a)` >-
     (fs [GSYM MEM_not_changed_after_normal_instrs] >>
      last_assum (assume_tac o is_mem_def_mem_no_errors) >>
      Cases_on_word_value `(agp32 fext fbits (SUC t)).command` >>
      fs [agp32_command_impossible_values] >-
       (last_assum (mp_tac o is_mem_data_flush `SUC t`) >> rw [] >>
        Cases_on `m` >> fs [] >-
         (`THE (I' (4,t)) = THE (I' (5,t)) + 1`
            by METIS_TAC [MEM_instr_index_with_WB_instr_plus_1] >> fs [Rel_def]) >>
        `~(fext (0 + SUC t)).ready` by fs [] >> fs []) >-
       (fs [is_wrMEM_isa_def] >>
        `(agp32 fext fbits t).MEM.MEM_opc <> 2w /\
        (agp32 fext fbits t).MEM.MEM_opc <> 3w` by fs [Rel_def,MEM_Rel_def] >>
        METIS_TAC [agp32_Rel_ag32_command_not_3_not_write_mem_and_byte_WB_enable]) >-
       (last_assum (mp_tac o is_mem_data_read `SUC t`) >> rw [] >>
        Cases_on `m` >> fs [] >-
         (`THE (I' (4,t)) = THE (I' (5,t)) + 1`
            by METIS_TAC [MEM_instr_index_with_WB_instr_plus_1] >> fs [Rel_def]) >>
        `~(fext (0 + SUC t)).ready` by fs [] >> fs []) >-
       (last_assum (mp_tac o is_mem_inst_read `SUC t`) >> rw [] >>
        Cases_on `m` >> fs [] >-
         (`THE (I' (4,t)) = THE (I' (5,t)) + 1`
            by METIS_TAC [MEM_instr_index_with_WB_instr_plus_1] >> fs [Rel_def]) >>
        `~(fext (0 + SUC t)).ready` by fs [] >> fs []) >>
      last_assum (mp_tac o is_mem_do_nothing `SUC t`) >> rw [] >>
      `THE (I' (4,t)) = THE (I' (5,t)) + 1`
        by METIS_TAC [MEM_instr_index_with_WB_instr_plus_1] >> fs [Rel_def]) >>
    fs [is_wrMEM_isa_def] >-
     (`(agp32 fext fbits t).MEM.MEM_opc = 2w` by fs [is_wrMEM_isa_def,Rel_def,MEM_Rel_def] >>
      `(agp32 fext fbits (SUC t)).WB.WB_opc = 2w` by fs [agp32_WB_opc_MEM_opc_when_WB_enabled] >>
      `(agp32 fext fbits (SUC t)).command = 3w`
        by fs [agp32_Rel_ag32_command_correct_write_mem_WB_enable] >>
      `align_addr (agp32 fext fbits (SUC t)).data_addr =
      mem_data_addr (FUNPOW Next (THE (I' (4,t)) − 1) a)`
        by METIS_TAC [agp32_Rel_ag32_data_addr_correct_write_mem] >>
      `(agp32 fext fbits (SUC t)).data_wdata =
      mem_data_wdata (FUNPOW Next (THE (I' (4,t)) − 1) a)`
        by METIS_TAC [agp32_Rel_ag32_data_wdata_correct_write_mem] >>
      `(agp32 fext fbits (SUC t)).data_wstrb =
      mem_data_wstrb (FUNPOW Next (THE (I' (4,t)) − 1) a)`
        by METIS_TAC [agp32_Rel_ag32_data_wstrb_correct_write_mem] >>
      last_assum (mp_tac o is_mem_data_write `SUC t`) >> rw [] >>
      Cases_on `m` >> fs [] >-
       (`THE (I' (4,t)) = SUC (THE (I' (5,t)))`
          by METIS_TAC [MEM_instr_index_with_WB_instr_plus_1,ADD1] >> fs [FUNPOW_SUC] >>
        qpat_abbrev_tac `ai = FUNPOW Next _ a` >>
        fs [ag32_StoreMEM_mem_update,Rel_def]) >>
      `~(fext (0 + SUC t)).ready` by fs [] >> fs []) >>
    `(agp32 fext fbits t).MEM.MEM_opc = 3w` by fs [is_wrMEM_isa_def,Rel_def,MEM_Rel_def] >>
    `(agp32 fext fbits (SUC t)).WB.WB_opc = 3w` by fs [agp32_WB_opc_MEM_opc_when_WB_enabled] >>
    `(agp32 fext fbits (SUC t)).command = 3w`
      by fs [agp32_Rel_ag32_command_correct_write_mem_byte_WB_enable] >>
    `(agp32 fext fbits (SUC t)).data_addr = mem_data_addr (FUNPOW Next (THE (I' (4,t)) − 1) a)`
      by METIS_TAC [agp32_Rel_ag32_data_addr_correct_write_mem_byte] >>
    `(agp32 fext fbits (SUC t)).data_wstrb = mem_data_wstrb (FUNPOW Next (THE (I' (4,t)) − 1) a)`
      by METIS_TAC [agp32_Rel_ag32_data_wstrb_correct_write_mem_byte] >>
    `word_bit 0 (mem_data_wstrb (FUNPOW Next (THE (I' (4,t)) − 1) a)) ==>
    (7 >< 0) (agp32 fext fbits (SUC t)).data_wdata =
    mem_data_wdata_byte (FUNPOW Next (THE (I' (4,t)) − 1) a)`
      by METIS_TAC [agp32_Rel_ag32_data_wdata_correct_write_mem_byte_word_bit_0] >>
    `word_bit 1 (mem_data_wstrb (FUNPOW Next (THE (I' (4,t)) − 1) a)) ==>
    (15 >< 8) (agp32 fext fbits (SUC t)).data_wdata =
    mem_data_wdata_byte (FUNPOW Next (THE (I' (4,t)) − 1) a)`
      by METIS_TAC [agp32_Rel_ag32_data_wdata_correct_write_mem_byte_word_bit_1] >>
    `word_bit 2 (mem_data_wstrb (FUNPOW Next (THE (I' (4,t)) − 1) a)) ==>
    (23 >< 16) (agp32 fext fbits (SUC t)).data_wdata =
    mem_data_wdata_byte (FUNPOW Next (THE (I' (4,t)) − 1) a)`
      by METIS_TAC [agp32_Rel_ag32_data_wdata_correct_write_mem_byte_word_bit_2] >>
    `word_bit 3 (mem_data_wstrb (FUNPOW Next (THE (I' (4,t)) − 1) a)) ==>
    (31 >< 24) (agp32 fext fbits (SUC t)).data_wdata =
    mem_data_wdata_byte (FUNPOW Next (THE (I' (4,t)) − 1) a)`
      by METIS_TAC [agp32_Rel_ag32_data_wdata_correct_write_mem_byte_word_bit_3] >>
    last_assum (mp_tac o is_mem_data_write `SUC t`) >> rw [] >>
    Cases_on `m` >> fs [] >-
     (`THE (I' (4,t)) = SUC (THE (I' (5,t)))`
        by METIS_TAC [MEM_instr_index_with_WB_instr_plus_1,ADD1] >> fs [FUNPOW_SUC] >>
      qpat_abbrev_tac `ai = FUNPOW Next _ a` >>
      fs [ag32_StoreMEMByte_mem_update,Rel_def]) >>
    `~(fext (0 + SUC t)).ready` by fs [] >> fs []) >>
  Cases_on `~is_wrMEM_isa (FUNPOW Next (THE (I' (4,t)) - 1) a)` >-
   (fs [GSYM MEM_not_changed_after_normal_instrs] >>
    last_assum (assume_tac o is_mem_def_mem_no_errors) >>
    Cases_on_word_value `(agp32 fext fbits (SUC t)).command` >>
    fs [agp32_command_impossible_values] >-
     (last_assum (mp_tac o is_mem_data_flush `SUC t`) >> rw [] >>
      Cases_on `m` >> fs [] >-
       fs [Rel_def] >>
      `~(fext (0 + SUC t)).ready` by fs [] >> fs []) >- 
     (fs [is_wrMEM_isa_def] >>
      `(agp32 fext fbits t).MEM.MEM_opc <> 2w /\
      (agp32 fext fbits t).MEM.MEM_opc <> 3w` by fs [Rel_def,MEM_Rel_def] >>
      METIS_TAC [agp32_Rel_ag32_command_not_3_not_write_mem_and_byte_WB_enable]) >- 
     (last_assum (mp_tac o is_mem_data_read `SUC t`) >> rw [] >>
      Cases_on `m` >> fs [] >-
       fs [Rel_def] >>
      `~(fext (0 + SUC t)).ready` by fs [] >> fs []) >-
     (last_assum (mp_tac o is_mem_inst_read `SUC t`) >> rw [] >>
      Cases_on `m` >> fs [] >-
       fs [Rel_def] >>
      `~(fext (0 + SUC t)).ready` by fs [] >> fs []) >>
    last_assum (mp_tac o is_mem_do_nothing `SUC t`) >> rw [] >> fs [Rel_def]) >>
  fs [is_wrMEM_isa_def] >-
   (`(agp32 fext fbits t).MEM.MEM_opc = 2w` by fs [is_wrMEM_isa_def,Rel_def,MEM_Rel_def] >>
    `(agp32 fext fbits (SUC t)).WB.WB_opc = 2w` by fs [agp32_WB_opc_MEM_opc_when_WB_enabled] >>
    `(agp32 fext fbits (SUC t)).command = 3w`
      by fs [agp32_Rel_ag32_command_correct_write_mem_WB_enable] >>
    `align_addr (agp32 fext fbits (SUC t)).data_addr =
    mem_data_addr (FUNPOW Next (THE (I' (4,t)) − 1) a)`
      by METIS_TAC [agp32_Rel_ag32_data_addr_correct_write_mem] >>
    `(agp32 fext fbits (SUC t)).data_wdata =
    mem_data_wdata (FUNPOW Next (THE (I' (4,t)) − 1) a)`
      by METIS_TAC [agp32_Rel_ag32_data_wdata_correct_write_mem] >>
    `(agp32 fext fbits (SUC t)).data_wstrb =
    mem_data_wstrb (FUNPOW Next (THE (I' (4,t)) − 1) a)`
      by METIS_TAC [agp32_Rel_ag32_data_wstrb_correct_write_mem] >>
    last_assum (mp_tac o is_mem_data_write `SUC t`) >> rw [] >>
    Cases_on `m` >> fs [] >-
     (Cases_on `THE (I' (4,t))` >-
       METIS_TAC [MEM_instr_index_not_0] >> 
      fs [FUNPOW_SUC] >> qpat_abbrev_tac `ai = FUNPOW Next _ a` >>
      fs [ag32_StoreMEM_mem_update,Rel_def]) >> 
    `~(fext (0 + SUC t)).ready` by fs [] >> fs []) >>
  `(agp32 fext fbits t).MEM.MEM_opc = 3w` by fs [is_wrMEM_isa_def,Rel_def,MEM_Rel_def] >>
  `(agp32 fext fbits (SUC t)).WB.WB_opc = 3w` by fs [agp32_WB_opc_MEM_opc_when_WB_enabled] >>
  `(agp32 fext fbits (SUC t)).command = 3w`
    by fs [agp32_Rel_ag32_command_correct_write_mem_byte_WB_enable] >>
  `(agp32 fext fbits (SUC t)).data_addr = mem_data_addr (FUNPOW Next (THE (I' (4,t)) − 1) a)`
    by METIS_TAC [agp32_Rel_ag32_data_addr_correct_write_mem_byte] >>
  `(agp32 fext fbits (SUC t)).data_wstrb = mem_data_wstrb (FUNPOW Next (THE (I' (4,t)) − 1) a)`
    by METIS_TAC [agp32_Rel_ag32_data_wstrb_correct_write_mem_byte] >>
  `word_bit 0 (mem_data_wstrb (FUNPOW Next (THE (I' (4,t)) − 1) a)) ==>
  (7 >< 0) (agp32 fext fbits (SUC t)).data_wdata =
  mem_data_wdata_byte (FUNPOW Next (THE (I' (4,t)) − 1) a)`
    by METIS_TAC [agp32_Rel_ag32_data_wdata_correct_write_mem_byte_word_bit_0] >>
  `word_bit 1 (mem_data_wstrb (FUNPOW Next (THE (I' (4,t)) − 1) a)) ==>
  (15 >< 8) (agp32 fext fbits (SUC t)).data_wdata =
  mem_data_wdata_byte (FUNPOW Next (THE (I' (4,t)) − 1) a)`
    by METIS_TAC [agp32_Rel_ag32_data_wdata_correct_write_mem_byte_word_bit_1] >>
  `word_bit 2 (mem_data_wstrb (FUNPOW Next (THE (I' (4,t)) − 1) a)) ==>
  (23 >< 16) (agp32 fext fbits (SUC t)).data_wdata =
  mem_data_wdata_byte (FUNPOW Next (THE (I' (4,t)) − 1) a)`
    by METIS_TAC [agp32_Rel_ag32_data_wdata_correct_write_mem_byte_word_bit_2] >>
  `word_bit 3 (mem_data_wstrb (FUNPOW Next (THE (I' (4,t)) − 1) a)) ==>
  (31 >< 24) (agp32 fext fbits (SUC t)).data_wdata =
  mem_data_wdata_byte (FUNPOW Next (THE (I' (4,t)) − 1) a)`
    by METIS_TAC [agp32_Rel_ag32_data_wdata_correct_write_mem_byte_word_bit_3] >>
  last_assum (mp_tac o is_mem_data_write `SUC t`) >> rw [] >>
  Cases_on `m` >> fs [] >-       
   (Cases_on `THE (I' (4,t))` >-
     METIS_TAC [MEM_instr_index_not_0] >>
    fs [FUNPOW_SUC] >> qpat_abbrev_tac `ai = FUNPOW Next _ a` >>
    fs [ag32_StoreMEMByte_mem_update,Rel_def]) >>  
  `~(fext (0 + SUC t)).ready` by fs [] >> fs []
QED

(** WB disabled and the previous cycle is not ready **)
Theorem agp32_Rel_ag32_fext_MEM_correct_WB_not_NONE_WB_disable_fext_not_ready:
  !fext fbits a t I.
    is_mem fext_accessor_circuit (agp32 fext fbits) fext ==>
    is_sch I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (5,SUC t) <> NONE ==>
    (fext (SUC t)).ready ==>
    ~(fext t).ready ==>
    ~enable_stg 5 (agp32 fext fbits t) ==>
    (fext (SUC t)).mem = (FUNPOW Next (THE (I (5,SUC t))) a).MEM
Proof
  rw [] >>
  `(agp32 fext fbits (SUC t)).WB.WB_opc <> 16w` by METIS_TAC [WB_instr_index_not_NONE_opc_not_16] >>
  Cases_on `MAX_SET {t0 | t0 < t /\ (fext t0).ready}` >-
   (Cases_on `{t0 | t0 < t /\ (fext t0).ready} = {}` >-
     (`!t0. t0 < t ==> ~(fext t0).ready` by METIS_TAC [EMPTY_no_fext_ready_cycle] >>
      `(agp32 fext fbits t).WB.WB_opc = (agp32 fext fbits 0).WB.WB_opc`
        by fs [WB_opc_unchanged_after_disabled_cycles_0] >>
      gs [agp32_WB_opc_unchanged_when_WB_disabled,agp32_init_WB_opc]) >>
    `!t0. t0 < t - 1 ==> ~(fext (t0 + 1)).ready`
      by METIS_TAC [MAX_SET_0_no_fext_ready_cycle] >>
    `(agp32 fext fbits (t - 1 + 1)).WB.WB_opc = (agp32 fext fbits 1).WB.WB_opc`
      by fs [WB_opc_unchanged_after_disabled_cycles] >>
    `t - 1 + 1 = t` by (Cases_on `t` >> fs []) >> fs [] >>
    `(agp32 fext fbits t).WB.WB_opc <> 16w` by gs [agp32_WB_opc_unchanged_when_WB_disabled] >>
    `~enable_stg 5 (agp32 fext fbits 0)` by fs [agp32_init_ctrl_flags,enable_stg_def] >>
    `(agp32 fext fbits (SUC 0)).WB.WB_opc = 16w`
      by fs [agp32_WB_opc_unchanged_when_WB_disabled,agp32_init_WB_opc] >>
    fs [SUC_ONE_ADD]) >>
  Q.ABBREV_TAC `i = SUC n` >> `i <> 0` by fs [Abbr `i`] >>
  `FINITE {t0 | t0 < t /\ (fext t0).ready}` by fs [FINITE_max_ready_cycle] >>
  Cases_on `{t0 | t0 < t /\ (fext t0).ready} = {}` >> fs [MAX_SET_DEF] >>
  `i IN {t0 | t0 < t /\ (fext t0).ready}` by METIS_TAC [MAX_SET_DEF] >> fs [MAX_SET_DEF] >>
  last_assum (assume_tac o is_mem_def_mem_no_errors) >>
  Cases_on_word_value `(agp32 fext fbits (SUC i)).command` >>
  fs [agp32_command_impossible_values] >-
   (last_assum (mp_tac o is_mem_data_flush `SUC i`) >> simp [] >> strip_tac >>
    `m + SUC i = SUC t` by METIS_TAC [same_t_and_m_under_MAX_SET_SUC] >> fs [] >>
    `I' (5,SUC t) = I' (5,t)` by fs [is_sch_def,is_sch_disable_def] >>
    `(agp32 fext fbits (SUC i)).WB.WB_opc = (agp32 fext fbits (SUC t)).WB.WB_opc`
      by METIS_TAC [WB_opc_unchanged_after_disabled_cycles] >>
    Cases_on `~enable_stg 5 (agp32 fext fbits i)` >-
     gs [agp32_Rel_ag32_command_correct_WB_disable_fext_ready] >>
    `(fext i).mem = (fext (m - 1 + SUC i)).mem` by fs [] >>
    `m - 1 + SUC i = t` by fs [] >> fs [] >>
    Cases_on `~is_wrMEM_isa (FUNPOW Next (THE (I' (5,t)) - 1) a)` >-
     fs [GSYM MEM_not_changed_after_normal_instrs,Rel_def] >>
    fs [is_wrMEM_isa_def] >>
    `(agp32 fext fbits (SUC t)).WB.WB_opc = (agp32 fext fbits t).WB.WB_opc`
      by fs [agp32_WB_opc_unchanged_when_WB_disabled] >>
    fs [Rel_def,WB_Rel_def] >>
    gs [agp32_Rel_ag32_command_correct_write_mem_WB_enable,
        agp32_Rel_ag32_command_correct_write_mem_byte_WB_enable]) >-
   (last_assum (mp_tac o is_mem_data_write `SUC i`) >> simp [] >> strip_tac >>
    `m + SUC i = SUC t` by METIS_TAC [same_t_and_m_under_MAX_SET_SUC] >> fs [] >>
    `I' (5,SUC t) = I' (5,t)` by fs [is_sch_def,is_sch_disable_def] >>
    `(agp32 fext fbits (SUC i)).WB.WB_opc = (agp32 fext fbits (SUC t)).WB.WB_opc`
      by METIS_TAC [WB_opc_unchanged_after_disabled_cycles] >>
    Cases_on `~enable_stg 5 (agp32 fext fbits i)` >-
     gs [agp32_Rel_ag32_command_correct_WB_disable_fext_ready] >>
    `(fext i).mem = (fext (m - 1 + SUC i)).mem` by fs [] >>
    `m - 1 + SUC i = t` by fs [] >> fs [] >>
    Cases_on `~is_wrMEM_isa (FUNPOW Next (THE (I' (5,t)) - 1) a)` >-
     (fs [is_wrMEM_isa_def] >>
      `(agp32 fext fbits t).WB.WB_opc <> 2w /\ (agp32 fext fbits t).WB.WB_opc <> 3w`
        by fs [Rel_def,WB_Rel_def] >>
      `(agp32 fext fbits (SUC i)).WB.WB_opc <> 2w /\ (agp32 fext fbits (SUC i)).WB.WB_opc <> 3w`
        by fs [agp32_WB_opc_unchanged_when_WB_disabled] >>
      `(agp32 fext fbits i).MEM.MEM_opc <> 2w /\ (agp32 fext fbits i).MEM.MEM_opc <> 3w`
        by METIS_TAC [agp32_WB_opc_MEM_opc_when_WB_enabled] >> 
      METIS_TAC [agp32_Rel_ag32_command_not_3_not_write_mem_and_byte_WB_enable]) >>
    fs [is_wrMEM_isa_def] >-
     (`(agp32 fext fbits (SUC t)).WB.WB_opc = 2w`
        by fs [agp32_WB_opc_unchanged_when_WB_disabled,Rel_def,WB_Rel_def] >>
      `(agp32 fext fbits (SUC i)).data_addr = (agp32 fext fbits (SUC t)).data_addr /\
      (agp32 fext fbits (SUC i)).data_wdata = (agp32 fext fbits (SUC t)).data_wdata /\
      (agp32 fext fbits (SUC i)).data_wstrb = (agp32 fext fbits (SUC t)).data_wstrb`
        by METIS_TAC [data_addr_wdata_wstrb_unchanged_after_disabled_cycles] >>
      `align_addr (agp32 fext fbits (SUC i)).data_addr =
      mem_data_addr (FUNPOW Next (THE (I' (5,t)) − 1) a)`
        by METIS_TAC [agp32_Rel_ag32_data_addr_correct_write_mem] >>
      `(agp32 fext fbits (SUC t)).data_wdata =
      mem_data_wdata (FUNPOW Next (THE (I' (5,t)) − 1) a)`
        by METIS_TAC [agp32_Rel_ag32_data_wdata_correct_write_mem] >>
      `(agp32 fext fbits (SUC t)).data_wstrb =
      mem_data_wstrb (FUNPOW Next (THE (I' (5,t)) − 1) a)`
        by METIS_TAC [agp32_Rel_ag32_data_wstrb_correct_write_mem] >>
      Cases_on `THE (I' (5,t))` >-
       METIS_TAC [WB_instr_index_not_0] >>
      fs [FUNPOW_SUC] >>
      qpat_abbrev_tac `ai = FUNPOW Next _ a` >>
      fs [ag32_StoreMEM_mem_update,Rel_def]) >>
    `(agp32 fext fbits (SUC t)).WB.WB_opc = 3w`
      by fs [agp32_WB_opc_unchanged_when_WB_disabled,Rel_def,WB_Rel_def] >>
    `(agp32 fext fbits (SUC i)).data_addr = (agp32 fext fbits (SUC t)).data_addr /\
    (agp32 fext fbits (SUC i)).data_wdata = (agp32 fext fbits (SUC t)).data_wdata /\
    (agp32 fext fbits (SUC i)).data_wstrb = (agp32 fext fbits (SUC t)).data_wstrb`
      by METIS_TAC [data_addr_wdata_wstrb_unchanged_after_disabled_cycles] >>
    `(agp32 fext fbits (SUC i)).data_addr = mem_data_addr (FUNPOW Next (THE (I' (5,t)) − 1) a)`
      by METIS_TAC [agp32_Rel_ag32_data_addr_correct_write_mem_byte] >> 
    `(agp32 fext fbits (SUC i)).data_wstrb = mem_data_wstrb (FUNPOW Next (THE (I' (5,t)) − 1) a)`
      by METIS_TAC [agp32_Rel_ag32_data_wstrb_correct_write_mem_byte] >>
    `word_bit 0 (mem_data_wstrb (FUNPOW Next (THE (I' (5,t)) − 1) a)) ==>
    (7 >< 0) (agp32 fext fbits (SUC i)).data_wdata =
    mem_data_wdata_byte (FUNPOW Next (THE (I' (5,t)) − 1) a)`
      by METIS_TAC [agp32_Rel_ag32_data_wdata_correct_write_mem_byte_word_bit_0] >>
    `word_bit 1 (mem_data_wstrb (FUNPOW Next (THE (I' (5,t)) − 1) a)) ==>
    (15 >< 8) (agp32 fext fbits (SUC i)).data_wdata =
    mem_data_wdata_byte (FUNPOW Next (THE (I' (5,t)) − 1) a)`
      by METIS_TAC [agp32_Rel_ag32_data_wdata_correct_write_mem_byte_word_bit_1] >>
    `word_bit 2 (mem_data_wstrb (FUNPOW Next (THE (I' (5,t)) − 1) a)) ==>
    (23 >< 16) (agp32 fext fbits (SUC i)).data_wdata =
    mem_data_wdata_byte (FUNPOW Next (THE (I' (5,t)) − 1) a)`
      by METIS_TAC [agp32_Rel_ag32_data_wdata_correct_write_mem_byte_word_bit_2] >>
    `word_bit 3 (mem_data_wstrb (FUNPOW Next (THE (I' (5,t)) − 1) a)) ==>
    (31 >< 24) (agp32 fext fbits (SUC i)).data_wdata =
    mem_data_wdata_byte (FUNPOW Next (THE (I' (5,t)) − 1) a)`
      by METIS_TAC [agp32_Rel_ag32_data_wdata_correct_write_mem_byte_word_bit_3] >>
    Cases_on `THE (I' (5,t))` >-
     METIS_TAC [WB_instr_index_not_0] >>
    fs [FUNPOW_SUC] >>
    qpat_abbrev_tac `ai = FUNPOW Next _ a` >>
    fs [Rel_def] >> METIS_TAC [ag32_StoreMEMByte_mem_update]) >-
   (last_assum (mp_tac o is_mem_data_read `SUC i`) >> simp [] >> strip_tac >>
    `m + SUC i = SUC t` by METIS_TAC [same_t_and_m_under_MAX_SET_SUC] >> fs [] >>
    `I' (5,SUC t) = I' (5,t)` by fs [is_sch_def,is_sch_disable_def] >>
    `(agp32 fext fbits (SUC i)).WB.WB_opc = (agp32 fext fbits (SUC t)).WB.WB_opc`
      by METIS_TAC [WB_opc_unchanged_after_disabled_cycles] >>
    Cases_on `~enable_stg 5 (agp32 fext fbits i)` >-
     gs [agp32_Rel_ag32_command_correct_WB_disable_fext_ready] >>
    `(fext i).mem = (fext (m - 1 + SUC i)).mem` by fs [] >>
    `m - 1 + SUC i = t` by fs [] >> fs [] >>
    Cases_on `~is_wrMEM_isa (FUNPOW Next (THE (I' (5,t)) - 1) a)` >-
     fs [GSYM MEM_not_changed_after_normal_instrs,Rel_def] >>
    fs [is_wrMEM_isa_def] >>
    `(agp32 fext fbits (SUC t)).WB.WB_opc = (agp32 fext fbits t).WB.WB_opc`
      by fs [agp32_WB_opc_unchanged_when_WB_disabled] >>
    fs [Rel_def,WB_Rel_def] >>
    gs [agp32_Rel_ag32_command_correct_write_mem_WB_enable,
        agp32_Rel_ag32_command_correct_write_mem_byte_WB_enable]) >-
   (last_assum (mp_tac o is_mem_inst_read `SUC i`) >> simp [] >> strip_tac >>
    `m + SUC i = SUC t` by METIS_TAC [same_t_and_m_under_MAX_SET_SUC] >> fs [] >>
    `I' (5,SUC t) = I' (5,t)` by fs [is_sch_def,is_sch_disable_def] >>
    `(agp32 fext fbits (SUC i)).WB.WB_opc = (agp32 fext fbits (SUC t)).WB.WB_opc`
      by METIS_TAC [WB_opc_unchanged_after_disabled_cycles] >>
    Cases_on `~enable_stg 5 (agp32 fext fbits i)` >-
     gs [agp32_Rel_ag32_command_correct_WB_disable_fext_ready] >>
    `(fext i).mem = (fext (m - 1 + SUC i)).mem` by fs [] >>
    `m - 1 + SUC i = t` by fs [] >> fs [] >>
    Cases_on `~is_wrMEM_isa (FUNPOW Next (THE (I' (5,t)) - 1) a)` >-
     fs [GSYM MEM_not_changed_after_normal_instrs,Rel_def] >>
    fs [is_wrMEM_isa_def] >>
    `(agp32 fext fbits (SUC t)).WB.WB_opc = (agp32 fext fbits t).WB.WB_opc`
      by fs [agp32_WB_opc_unchanged_when_WB_disabled] >>
    fs [Rel_def,WB_Rel_def] >>
    gs [agp32_Rel_ag32_command_correct_write_mem_WB_enable,
        agp32_Rel_ag32_command_correct_write_mem_byte_WB_enable]) >>
  last_assum (mp_tac o is_mem_do_nothing `SUC i`) >> simp [] >> strip_tac >>
  Cases_on `SUC i = t` >> fs [] >>
  Cases_on `SUC i > t` >> fs [] >>
  `SUC i < t` by fs [] >>
  `(SUC i) IN {t0 | t0 < t /\ (fext t0).ready}` by fs [] >>
  `(SUC i) <= i` by METIS_TAC [MAX_SET_DEF] >> fs []
QED

(** WB disabled **)
Theorem agp32_Rel_ag32_fext_MEM_correct_WB_not_NONE_WB_disable:
  !fext fbits a t I.
    is_mem fext_accessor_circuit (agp32 fext fbits) fext ==>
    is_sch I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (5,SUC t) <> NONE ==>
    (fext (SUC t)).ready ==>
    ~enable_stg 5 (agp32 fext fbits t) ==>
    (fext (SUC t)).mem = (FUNPOW Next (THE (I (5,SUC t))) a).MEM
Proof
  rw [] >> Cases_on `(fext t).ready` >-
   (`I' (5,SUC t) = I' (5,t)` by fs [is_sch_def,is_sch_disable_def] >>
    `(agp32 fext fbits (SUC t)).WB.WB_opc <> 16w` by METIS_TAC [WB_instr_index_not_NONE_opc_not_16] >>
    `(agp32 fext fbits (SUC t)).WB.WB_opc = (agp32 fext fbits t).WB.WB_opc`
      by fs [agp32_WB_opc_unchanged_when_WB_disabled] >>
    last_assum (assume_tac o is_mem_def_mem_no_errors) >>
    `(agp32 fext fbits (SUC t)).command = 0w`
      by gs [agp32_Rel_ag32_command_correct_WB_disable_fext_ready] >>
    last_assum (mp_tac o is_mem_do_nothing `SUC t`) >> rw [] >>
    fs [Rel_def]) >>
  METIS_TAC [agp32_Rel_ag32_fext_MEM_correct_WB_not_NONE_WB_disable_fext_not_ready]
QED

(** WB is not NONE and fext is ready **)
Theorem agp32_Rel_ag32_fext_MEM_correct_WB_not_NONE:
  !fext fbits a t I.
    is_mem fext_accessor_circuit (agp32 fext fbits) fext ==>
    is_sch I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (5,SUC t) <> NONE ==>
    (fext (SUC t)).ready ==>
    (fext (SUC t)).mem = (FUNPOW Next (THE (I (5,SUC t))) a).MEM
Proof
  rw [] >> Cases_on `enable_stg 5 (agp32 fext fbits t)` >-
   METIS_TAC [agp32_Rel_ag32_fext_MEM_correct_WB_not_NONE_WB_enable] >>
  METIS_TAC [agp32_Rel_ag32_fext_MEM_correct_WB_not_NONE_WB_disable]
QED


(** WB enabled **)
Theorem agp32_Rel_ag32_fext_MEM_correct_WB_not_NONE_WB_enable_extra:
  !fext fbits a t I.
    is_mem fext_accessor_circuit (agp32 fext fbits) fext ==>
    is_sch I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (5,SUC t) <> NONE ==>
    ~(fext (SUC t)).ready ==>
    enable_stg 5 (agp32 fext fbits t) ==>
    (fext (SUC t)).mem = (FUNPOW Next (THE (I (5,SUC t)) - 1) a).MEM
Proof
  rw [] >> `I' (5,SUC t) = I' (4,t)` by fs [is_sch_def,is_sch_writeback_def] >>
  `(fext t).ready` by (fs [enable_stg_def] >> METIS_TAC [agp32_WB_state_flag_and_fext_ready]) >>
  Cases_on `I' (5,t) <> NONE` >> fs [] >-
   (Cases_on `~is_wrMEM_isa (FUNPOW Next (THE (I' (4,t)) - 1) a)` >-
     (fs [GSYM MEM_not_changed_after_normal_instrs] >>
      last_assum (assume_tac o is_mem_def_mem_no_errors) >>
      Cases_on_word_value `(agp32 fext fbits (SUC t)).command` >>
      fs [agp32_command_impossible_values] >-
       (last_assum (mp_tac o is_mem_data_flush `SUC t`) >> rw [] >>
        Cases_on `m` >> fs [] >>
        `(fext (0 + SUC t)).mem = (fext t).mem` by fs [] >> fs [] >>
        `THE (I' (4,t)) = THE (I' (5,t)) + 1`
            by METIS_TAC [MEM_instr_index_with_WB_instr_plus_1] >> fs [Rel_def]) >-
       (fs [is_wrMEM_isa_def] >>
        `(agp32 fext fbits t).MEM.MEM_opc <> 2w /\
        (agp32 fext fbits t).MEM.MEM_opc <> 3w` by fs [Rel_def,MEM_Rel_def] >>
        METIS_TAC [agp32_Rel_ag32_command_not_3_not_write_mem_and_byte_WB_enable]) >-
       (last_assum (mp_tac o is_mem_data_read `SUC t`) >> rw [] >>
        Cases_on `m` >> fs [] >>
        `(fext (0 + SUC t)).mem = (fext t).mem` by fs [] >> fs [] >>
        `THE (I' (4,t)) = THE (I' (5,t)) + 1`
            by METIS_TAC [MEM_instr_index_with_WB_instr_plus_1] >> fs [Rel_def]) >-
       (last_assum (mp_tac o is_mem_inst_read `SUC t`) >> rw [] >>
        Cases_on `m` >> fs [] >>
        `(fext (0 + SUC t)).mem = (fext t).mem` by fs [] >> fs [] >>
        `THE (I' (4,t)) = THE (I' (5,t)) + 1`
            by METIS_TAC [MEM_instr_index_with_WB_instr_plus_1] >> fs [Rel_def]) >>
      last_assum (mp_tac o is_mem_do_nothing `SUC t`) >> rw []) >>
    fs [is_wrMEM_isa_def] >-
     (`(agp32 fext fbits t).MEM.MEM_opc = 2w` by fs [is_wrMEM_isa_def,Rel_def,MEM_Rel_def] >>
      `(agp32 fext fbits (SUC t)).WB.WB_opc = 2w` by fs [agp32_WB_opc_MEM_opc_when_WB_enabled] >>
      `(agp32 fext fbits (SUC t)).command = 3w`
        by fs [agp32_Rel_ag32_command_correct_write_mem_WB_enable] >>
      last_assum (mp_tac o is_mem_data_write `SUC t`) >> rw [] >>
      Cases_on `m` >> fs [] >>
      `(fext (0 + SUC t)).mem = (fext t).mem` by fs [] >> fs [] >>
      `THE (I' (4,t)) = THE (I' (5,t)) + 1`
        by METIS_TAC [MEM_instr_index_with_WB_instr_plus_1] >> fs [Rel_def]) >>
    `(agp32 fext fbits t).MEM.MEM_opc = 3w` by fs [is_wrMEM_isa_def,Rel_def,MEM_Rel_def] >>
    `(agp32 fext fbits (SUC t)).WB.WB_opc = 3w` by fs [agp32_WB_opc_MEM_opc_when_WB_enabled] >>
    `(agp32 fext fbits (SUC t)).command = 3w`
      by fs [agp32_Rel_ag32_command_correct_write_mem_byte_WB_enable] >>
    last_assum (mp_tac o is_mem_data_write `SUC t`) >> rw [] >>
    Cases_on `m` >> fs [] >>
    `(fext (0 + SUC t)).mem = (fext t).mem` by fs [] >> fs [] >>
    `THE (I' (4,t)) = THE (I' (5,t)) + 1`
      by METIS_TAC [MEM_instr_index_with_WB_instr_plus_1] >> fs [Rel_def]) >>
  Cases_on `~is_wrMEM_isa (FUNPOW Next (THE (I' (4,t)) - 1) a)` >-
   (fs [GSYM MEM_not_changed_after_normal_instrs] >>
    last_assum (assume_tac o is_mem_def_mem_no_errors) >>
    Cases_on_word_value `(agp32 fext fbits (SUC t)).command` >>
    fs [agp32_command_impossible_values] >-
     (last_assum (mp_tac o is_mem_data_flush `SUC t`) >> rw [] >>
      Cases_on `m` >> fs [] >>
      `(fext (0 + SUC t)).mem = (fext t).mem` by fs [] >> fs [Rel_def]) >- 
     (fs [is_wrMEM_isa_def] >>
      `(agp32 fext fbits t).MEM.MEM_opc <> 2w /\
      (agp32 fext fbits t).MEM.MEM_opc <> 3w` by fs [Rel_def,MEM_Rel_def] >>
      METIS_TAC [agp32_Rel_ag32_command_not_3_not_write_mem_and_byte_WB_enable]) >- 
     (last_assum (mp_tac o is_mem_data_read `SUC t`) >> rw [] >>
      Cases_on `m` >> fs [] >>
      `(fext (0 + SUC t)).mem = (fext t).mem` by fs [] >> fs [Rel_def]) >-
     (last_assum (mp_tac o is_mem_inst_read `SUC t`) >> rw [] >>
      Cases_on `m` >> fs [] >>
      `(fext (0 + SUC t)).mem = (fext t).mem` by fs [] >> fs [Rel_def]) >>
    last_assum (mp_tac o is_mem_do_nothing `SUC t`) >> rw []) >>
  fs [is_wrMEM_isa_def] >-
   (`(agp32 fext fbits t).MEM.MEM_opc = 2w` by fs [is_wrMEM_isa_def,Rel_def,MEM_Rel_def] >>
    `(agp32 fext fbits (SUC t)).WB.WB_opc = 2w` by fs [agp32_WB_opc_MEM_opc_when_WB_enabled] >>
    `(agp32 fext fbits (SUC t)).command = 3w`
      by fs [agp32_Rel_ag32_command_correct_write_mem_WB_enable] >>
    last_assum (mp_tac o is_mem_data_write `SUC t`) >> rw [] >>
    Cases_on `m` >> fs [] >>
    `(fext (0 + SUC t)).mem = (fext t).mem` by fs [] >> fs [Rel_def]) >>
  `(agp32 fext fbits t).MEM.MEM_opc = 3w` by fs [is_wrMEM_isa_def,Rel_def,MEM_Rel_def] >>
  `(agp32 fext fbits (SUC t)).WB.WB_opc = 3w` by fs [agp32_WB_opc_MEM_opc_when_WB_enabled] >>
  `(agp32 fext fbits (SUC t)).command = 3w`
    by fs [agp32_Rel_ag32_command_correct_write_mem_byte_WB_enable] >>
  last_assum (mp_tac o is_mem_data_write `SUC t`) >> rw [] >>
  Cases_on `m` >> fs [] >>       
  `(fext (0 + SUC t)).mem = (fext t).mem` by fs [] >> fs [Rel_def]
QED

(** WB disabled and the previous cycle is not ready **)
Theorem agp32_Rel_ag32_fext_MEM_correct_WB_not_NONE_WB_disable_fext_not_ready_extra:
  !fext fbits a t I.
    is_mem fext_accessor_circuit (agp32 fext fbits) fext ==>
    is_sch I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (5,SUC t) <> NONE ==>
    ~(fext (SUC t)).ready ==>
    ~(fext t).ready ==>
    ~enable_stg 5 (agp32 fext fbits t) ==>
    (fext (SUC t)).mem = (FUNPOW Next (THE (I (5,SUC t)) - 1) a).MEM
Proof
  rw [] >>
  `(agp32 fext fbits (SUC t)).WB.WB_opc <> 16w` by METIS_TAC [WB_instr_index_not_NONE_opc_not_16] >>
  Cases_on `MAX_SET {t0 | t0 < t /\ (fext t0).ready}` >-
   (Cases_on `{t0 | t0 < t /\ (fext t0).ready} = {}` >-
     (`!t0. t0 < t ==> ~(fext t0).ready` by METIS_TAC [EMPTY_no_fext_ready_cycle] >>
      `(agp32 fext fbits t).WB.WB_opc = (agp32 fext fbits 0).WB.WB_opc`
        by fs [WB_opc_unchanged_after_disabled_cycles_0] >>
      gs [agp32_WB_opc_unchanged_when_WB_disabled,agp32_init_WB_opc]) >>
    `!t0. t0 < t - 1 ==> ~(fext (t0 + 1)).ready`
      by METIS_TAC [MAX_SET_0_no_fext_ready_cycle] >>
    `(agp32 fext fbits (t - 1 + 1)).WB.WB_opc = (agp32 fext fbits 1).WB.WB_opc`
      by fs [WB_opc_unchanged_after_disabled_cycles] >>
    `t - 1 + 1 = t` by (Cases_on `t` >> fs []) >> fs [] >>
    `(agp32 fext fbits t).WB.WB_opc <> 16w` by gs [agp32_WB_opc_unchanged_when_WB_disabled] >>
    `~enable_stg 5 (agp32 fext fbits 0)` by fs [agp32_init_ctrl_flags,enable_stg_def] >>
    `(agp32 fext fbits (SUC 0)).WB.WB_opc = 16w`
      by fs [agp32_WB_opc_unchanged_when_WB_disabled,agp32_init_WB_opc] >>
    fs [SUC_ONE_ADD]) >>
  Q.ABBREV_TAC `i = SUC n` >> `i <> 0` by fs [Abbr `i`] >>
  `FINITE {t0 | t0 < t /\ (fext t0).ready}` by fs [FINITE_max_ready_cycle] >>
  Cases_on `{t0 | t0 < t /\ (fext t0).ready} = {}` >> fs [MAX_SET_DEF] >>
  `i IN {t0 | t0 < t /\ (fext t0).ready}` by METIS_TAC [MAX_SET_DEF] >> fs [MAX_SET_DEF] >>
  last_assum (assume_tac o is_mem_def_mem_no_errors) >>
  Cases_on_word_value `(agp32 fext fbits (SUC i)).command` >>
  fs [agp32_command_impossible_values] >-
   (last_assum (mp_tac o is_mem_data_flush `SUC i`) >> simp [] >> strip_tac >>
    `(fext (SUC t)).mem = (fext t).mem` by METIS_TAC [same_mem_t_SUC_t_under_MAX_SET] >>
    gs [is_sch_def,is_sch_disable_def,Rel_def]) >-
   (last_assum (mp_tac o is_mem_data_write `SUC i`) >> simp [] >> strip_tac >>
    `(fext (SUC t)).mem = (fext t).mem` by METIS_TAC [same_mem_t_SUC_t_under_MAX_SET] >>
    gs [is_sch_def,is_sch_disable_def,Rel_def]) >-
   (last_assum (mp_tac o is_mem_data_read `SUC i`) >> simp [] >> strip_tac >>
    `(fext (SUC t)).mem = (fext t).mem` by METIS_TAC [same_mem_t_SUC_t_under_MAX_SET] >>
    gs [is_sch_def,is_sch_disable_def,Rel_def]) >-
   (last_assum (mp_tac o is_mem_inst_read `SUC i`) >> simp [] >> strip_tac >>
    `(fext (SUC t)).mem = (fext t).mem` by METIS_TAC [same_mem_t_SUC_t_under_MAX_SET] >>
    gs [is_sch_def,is_sch_disable_def,Rel_def]) >>
  last_assum (mp_tac o is_mem_do_nothing `SUC i`) >> simp [] >> strip_tac >>
  Cases_on `SUC i = t` >> fs [] >>
  Cases_on `SUC i > t` >> fs [] >>
  `SUC i < t` by fs [] >>
  `(SUC i) IN {t0 | t0 < t /\ (fext t0).ready}` by fs [] >>
  `(SUC i) <= i` by METIS_TAC [MAX_SET_DEF] >> fs []
QED

(** WB disabled **)
Theorem agp32_Rel_ag32_fext_MEM_correct_WB_not_NONE_WB_disable_extra:
  !fext fbits a t I.
    is_mem fext_accessor_circuit (agp32 fext fbits) fext ==>
    is_sch I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (5,SUC t) <> NONE ==>
    ~(fext (SUC t)).ready ==>
    ~enable_stg 5 (agp32 fext fbits t) ==>
    (fext (SUC t)).mem = (FUNPOW Next (THE (I (5,SUC t)) - 1) a).MEM
Proof
  rw [] >> Cases_on `(fext t).ready` >-
   (`I' (5,SUC t) = I' (5,t)` by fs [is_sch_def,is_sch_disable_def] >>
    `(agp32 fext fbits (SUC t)).WB.WB_opc <> 16w` by METIS_TAC [WB_instr_index_not_NONE_opc_not_16] >>
    `(agp32 fext fbits (SUC t)).WB.WB_opc = (agp32 fext fbits t).WB.WB_opc`
      by fs [agp32_WB_opc_unchanged_when_WB_disabled] >>
    last_assum (assume_tac o is_mem_def_mem_no_errors) >>
    `(agp32 fext fbits (SUC t)).command = 0w`
      by gs [agp32_Rel_ag32_command_correct_WB_disable_fext_ready] >>
    last_assum (mp_tac o is_mem_do_nothing `SUC t`) >> rw []) >>
  METIS_TAC [agp32_Rel_ag32_fext_MEM_correct_WB_not_NONE_WB_disable_fext_not_ready_extra]
QED

(** WB is not NONE and fext is not ready **)
Theorem agp32_Rel_ag32_fext_MEM_correct_WB_not_NONE_extra:
  !fext fbits a t I.
    is_mem fext_accessor_circuit (agp32 fext fbits) fext ==>
    is_sch I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (5,SUC t) <> NONE ==>
    ~(fext (SUC t)).ready ==>
    (fext (SUC t)).mem = (FUNPOW Next (THE (I (5,SUC t)) - 1) a).MEM
Proof
  rw [] >> Cases_on `enable_stg 5 (agp32 fext fbits t)` >-
   METIS_TAC [agp32_Rel_ag32_fext_MEM_correct_WB_not_NONE_WB_enable_extra] >>
  METIS_TAC [agp32_Rel_ag32_fext_MEM_correct_WB_not_NONE_WB_disable_extra]
QED


(** mem is unchanged when WB is NONE **)
Theorem agp32_mem_unchanged_when_WB_NONE:
  !fext fbits a t I.
    is_mem fext_accessor_circuit (agp32 fext fbits) fext ==>
    is_sch I (agp32 fext fbits) a ==>
    Init (fext 0) (agp32 fext fbits 0) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (5,SUC t) = NONE ==>
    (fext (SUC t)).mem = (fext t).mem
Proof
  rw [] >> Cases_on `enable_stg 5 (agp32 fext fbits t)` >-
   (`(fext t).ready` by (fs [enable_stg_def] >> METIS_TAC [agp32_WB_state_flag_and_fext_ready]) >>
    `(agp32 fext fbits (SUC t)).WB.WB_opc = 16w \/ (agp32 fext fbits (SUC t)).WB.WB_opc = 15w`
      by METIS_TAC [WB_instr_index_NONE_opc_flush] >>
    `(agp32 fext fbits (SUC t)).command = 1w`
      by METIS_TAC [agp32_Rel_ag32_command_correct_none_instr_WB_enable] >>
    last_assum (assume_tac o is_mem_def_mem_no_errors) >>
    last_assum (mp_tac o is_mem_inst_read `SUC t`) >> rw [] >>
    Cases_on `m` >> fs [] >>
    `(fext (0 + SUC t)).mem = (fext t).mem` by fs [] >> fs []) >>
  Cases_on `(fext t).ready` >-
   (`(agp32 fext fbits (SUC t)).command = 1w \/ (agp32 fext fbits (SUC t)).command = 0w`
      by METIS_TAC [agp32_Rel_ag32_command_correct_WB_disable_fext_ready_extra] >>
    last_assum (assume_tac o is_mem_def_mem_no_errors) >-
     (last_assum (mp_tac o is_mem_inst_read `SUC t`) >> rw [] >>
      Cases_on `m` >> fs [] >>
      `(fext (0 + SUC t)).mem = (fext t).mem` by fs [] >> fs []) >>
    last_assum (mp_tac o is_mem_do_nothing `SUC t`) >> rw []) >>
  Cases_on `MAX_SET {t0 | t0 < t /\ (fext t0).ready}` >-
   (last_assum (assume_tac o is_mem_def_mem_no_errors) >>
    `(agp32 fext fbits (SUC 0)).command = 1w \/ (agp32 fext fbits (SUC 0)).command = 0w`
      by METIS_TAC [agp32_command_cycle_1] >-
     (last_assum (mp_tac o is_mem_inst_read `SUC 0`) >> simp [] >> strip_tac >>
      Cases_on `~(fext (SUC t)).ready` >-
       METIS_TAC [same_mem_t_SUC_t_under_MAX_SET_0] >> fs [ADD1] >>
      `m = t` by METIS_TAC [same_t_and_m_under_MAX_SET_0] >> rw [] >>
      Cases_on `m` >> gs [ADD1]) >>
    last_assum (mp_tac o is_mem_do_nothing `SUC 0`) >> simp [] >> strip_tac >>
    Cases_on `(fext 0 ).ready` >> fs [] >-
     (`!p. p < 0 ==> ~(fext (p + 1)).ready /\ (fext 0).mem = (fext (p + 1)).mem` by rw [] >>
      `1 = 0 + 1` by rw [] >>
      `(fext (0 + 1)).ready` by METIS_TAC [] >>
      Cases_on `(fext (SUC t)).ready` >-
       (`SUC t = t + 1` by rw [] >>
        `0 = t` by METIS_TAC [same_t_and_m_under_MAX_SET_0] >> fs []) >>
      METIS_TAC [same_mem_t_SUC_t_under_MAX_SET_0]) >>
    fs [Init_def]) >>
  Q.ABBREV_TAC `i = SUC n` >> `i <> 0` by fs [Abbr `i`] >>
  `FINITE {t0 | t0 < t /\ (fext t0).ready}` by fs [FINITE_max_ready_cycle] >>
  Cases_on `{t0 | t0 < t /\ (fext t0).ready} = {}` >> fs [MAX_SET_DEF] >>
  `i IN {t0 | t0 < t /\ (fext t0).ready}` by METIS_TAC [MAX_SET_DEF] >> fs [MAX_SET_DEF] >>
  last_assum (assume_tac o is_mem_def_mem_no_errors) >>
  Cases_on_word_value `(agp32 fext fbits (SUC i)).command` >>
  fs [agp32_command_impossible_values] >-
   (last_assum (mp_tac o is_mem_data_flush `SUC i`) >> simp [] >> strip_tac >>
    Cases_on `~(fext (SUC t)).ready` >-
     METIS_TAC [same_mem_t_SUC_t_under_MAX_SET] >> fs [] >>
    `m + SUC i = SUC t` by METIS_TAC [same_t_and_m_under_MAX_SET_SUC] >> fs [] >>
    `(fext (m - 1 + SUC i)).mem = (fext i).mem` by fs [] >>
    `m - 1 + SUC i = t` by fs [] >> fs []) >-
   (last_assum (mp_tac o is_mem_data_write `SUC i`) >> simp [] >> strip_tac >>
    Cases_on `~(fext (SUC t)).ready` >-
     METIS_TAC [same_mem_t_SUC_t_under_MAX_SET] >> fs [] >>
    `m + SUC i = SUC t` by METIS_TAC [same_t_and_m_under_MAX_SET_SUC] >> fs [] >>
    Cases_on `enable_stg 5 (agp32 fext fbits i)` >-
     (`(agp32 fext fbits (SUC i)).WB.WB_opc = (agp32 fext fbits (SUC t)).WB.WB_opc`
        by METIS_TAC [WB_opc_unchanged_after_disabled_cycles] >>
      `(agp32 fext fbits (SUC t)).WB.WB_opc = 16w \/ (agp32 fext fbits (SUC t)).WB.WB_opc = 15w`
        by METIS_TAC [WB_instr_index_NONE_opc_flush] >>
       gs [agp32_Rel_ag32_command_correct_none_instr_WB_enable]) >>
    `(agp32 fext fbits (SUC i)).command = 0w \/ (agp32 fext fbits (SUC i)).command = 1w`
      by METIS_TAC [agp32_Rel_ag32_command_correct_WB_disable_fext_ready_extra] >> fs []) >-
   (last_assum (mp_tac o is_mem_data_read `SUC i`) >> simp [] >> strip_tac >>
    Cases_on `~(fext (SUC t)).ready` >-
     METIS_TAC [same_mem_t_SUC_t_under_MAX_SET] >> fs [] >>
    `m + SUC i = SUC t` by METIS_TAC [same_t_and_m_under_MAX_SET_SUC] >> fs [] >>
    `(fext (m - 1 + SUC i)).mem = (fext i).mem` by fs [] >>
    `m - 1 + SUC i = t` by fs [] >> fs []) >-
   (last_assum (mp_tac o is_mem_inst_read `SUC i`) >> simp [] >> strip_tac >>
    Cases_on `~(fext (SUC t)).ready` >-
     METIS_TAC [same_mem_t_SUC_t_under_MAX_SET] >> fs [] >>
    `m + SUC i = SUC t` by METIS_TAC [same_t_and_m_under_MAX_SET_SUC] >> fs [] >>
    `(fext (m - 1 + SUC i)).mem = (fext i).mem` by fs [] >>
    `m - 1 + SUC i = t` by fs [] >> fs []) >>
  last_assum (mp_tac o is_mem_do_nothing `SUC i`) >> simp [] >> strip_tac >>
  Cases_on `SUC i = t` >> fs [] >>
  Cases_on `SUC i > t` >> fs [] >>
  `SUC i < t` by fs [] >>
  `(SUC i) IN {t0 | t0 < t /\ (fext t0).ready}` by fs [] >>
  `(SUC i) <= i` by METIS_TAC [MAX_SET_DEF] >> fs []
QED


(** MEM **)
Theorem agp32_Rel_ag32_fext_MEM_correct_MEM_not_NONE:
  !fext fbits a t I.
    is_mem fext_accessor_circuit (agp32 fext fbits) fext ==>
    is_sch I (agp32 fext fbits) a ==>
    Init (fext 0) (agp32 fext fbits 0) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (5,SUC t) = NONE ==>
    I (4,SUC t) <> NONE ==>
    (fext (SUC t)).mem = (FUNPOW Next (THE (I (4,SUC t)) - 1) a).MEM
Proof
  rw [] >>
  `(fext (SUC t)).mem = (fext t).mem` by METIS_TAC [agp32_mem_unchanged_when_WB_NONE] >>
  Cases_on `enable_stg 4 (agp32 fext fbits t)` >-
   (Cases_on `isMemOp_hw_op (agp32 fext fbits t)` >-
     gs [is_sch_def,is_sch_memory_def] >>
    `I' (4,SUC t) = I' (3,t)` by fs [is_sch_def,is_sch_memory_def] >>
    `enable_stg 5 (agp32 fext fbits t)`
      by fs [enable_stg_def,agp32_MEM_state_flag_eq_WB_state_flag] >>
    `I' (5,SUC t) = I' (4,t)` by gs [is_sch_def,is_sch_writeback_def] >>
    Cases_on `I' (5,t) = NONE` >> fs [Rel_def] >>
    `(fext t).ready` by (fs [enable_stg_def] >> METIS_TAC [agp32_WB_state_flag_and_fext_ready]) >>
    `THE (I' (3,t)) = THE (I' (5,t)) + 1`
      by METIS_TAC [EX_instr_index_with_WB_instr_plus_1_MEM_NONE] >> fs []) >>
  `~enable_stg 5 (agp32 fext fbits t)`
    by fs [enable_stg_def,agp32_MEM_state_flag_eq_WB_state_flag] >>
  `I' (5,SUC t) = I' (5,t) /\ I' (4,SUC t) = I' (4,t)` by gs [is_sch_def,is_sch_disable_def] >>
  fs [Rel_def]
QED

(** EX **)
Theorem agp32_Rel_ag32_fext_MEM_correct_EX_not_NONE:
  !fext fbits a t I.
    is_mem fext_accessor_circuit (agp32 fext fbits) fext ==>
    is_sch I (agp32 fext fbits) a ==>
    Init (fext 0) (agp32 fext fbits 0) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (5,SUC t) = NONE ==>
    I (4,SUC t) = NONE ==>
    I (3,SUC t) <> NONE ==>
    (fext (SUC t)).mem = (FUNPOW Next (THE (I (3,SUC t)) - 1) a).MEM
Proof
  rw [] >>
  `(fext (SUC t)).mem = (fext t).mem` by METIS_TAC [agp32_mem_unchanged_when_WB_NONE] >>
  Cases_on `enable_stg 3 (agp32 fext fbits t)` >-
   (Cases_on `isJump_hw_op (agp32 fext fbits t)` >-
     gs [is_sch_def,is_sch_execute_def] >>
    Cases_on `reg_data_hazard (agp32 fext fbits t)` >-
     gs [is_sch_def,is_sch_execute_def] >>
    `I' (3,SUC t) = I' (2,t)` by fs [is_sch_def,is_sch_execute_def] >>
    `enable_stg 5 (agp32 fext fbits t)`
      by fs [enable_stg_def,agp32_ID_EX_write_enable_WB_state_flag] >>
    `I' (5,SUC t) = I' (4,t)` by gs [is_sch_def,is_sch_writeback_def] >>
    `enable_stg 4 (agp32 fext fbits t)`
      by fs [enable_stg_def,agp32_ID_EX_write_enable_MEM_state_flag] >>
    Cases_on `isMemOp_hw_op (agp32 fext fbits t)` >-
     (fs [enable_stg_def] >>
      METIS_TAC [agp32_ID_EX_write_enable_no_MEM_stg_op]) >>
    `I' (4,SUC t) = I' (3,t)` by METIS_TAC [is_sch_def,is_sch_memory_def] >> fs [] >>
    Cases_on `I' (5,t) = NONE` >> fs [Rel_def] >>
    `(fext t).ready` by (fs [enable_stg_def] >> METIS_TAC [agp32_WB_state_flag_and_fext_ready]) >>
    `THE (I' (2,t)) = THE (I' (5,t)) + 1`
      by METIS_TAC [EX_MEM_NONE_ID_instr_index_with_WB_instr_plus_1] >> fs []) >>
  Cases_on `enable_stg 5 (agp32 fext fbits t)` >-
   (`I' (3,SUC t) = I' (3,t)` by fs [is_sch_def,is_sch_disable_def] >> fs [] >>
    `enable_stg 4 (agp32 fext fbits t)`
      by fs [enable_stg_def,agp32_MEM_state_flag_eq_WB_state_flag] >>
    Cases_on `isMemOp_hw_op (agp32 fext fbits t)` >-
     (`I' (5,SUC t) = I' (4,t)` by gs [is_sch_def,is_sch_writeback_def] >> fs [] >>
      Cases_on `I' (5,t) = NONE` >> fs [Rel_def] >>
      `(fext t).ready` by (fs [enable_stg_def] >> METIS_TAC [agp32_WB_state_flag_and_fext_ready]) >>
      `THE (I' (3,t)) = THE (I' (5,t)) + 1`
        by METIS_TAC [EX_instr_index_with_WB_instr_plus_1_MEM_NONE] >> fs []) >>
    fs [is_sch_def,is_sch_memory_def] >> METIS_TAC []) >>
  `~enable_stg 4 (agp32 fext fbits t)`
    by fs [enable_stg_def,agp32_MEM_state_flag_eq_WB_state_flag] >>
  gs [is_sch_def,is_sch_disable_def,Rel_def]
QED

(** ID **)
Theorem agp32_Rel_ag32_fext_MEM_correct_ID_not_NONE:
  !fext fbits a t I.
    is_mem fext_accessor_circuit (agp32 fext fbits) fext ==>
    is_sch I (agp32 fext fbits) a ==>
    Init (fext 0) (agp32 fext fbits 0) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (5,SUC t) = NONE ==>
    I (4,SUC t) = NONE ==>
    I (3,SUC t) = NONE ==>
    I (2,SUC t) <> NONE ==>
    (fext (SUC t)).mem = (FUNPOW Next (THE (I (2,SUC t)) - 1) a).MEM
Proof
  rw [] >>
  `(fext (SUC t)).mem = (fext t).mem` by METIS_TAC [agp32_mem_unchanged_when_WB_NONE] >>
  Cases_on `enable_stg 2 (agp32 fext fbits t)` >-
   (Cases_on `isJump_isa_op (I' (2,t)) a \/ isJump_hw_op (agp32 fext fbits t)` >-
     gs [is_sch_def,is_sch_decode_def] >>
    `I' (2,SUC t) = I' (1,t)` by fs [is_sch_def,is_sch_decode_def] >> fs [] >>
    `enable_stg 5 (agp32 fext fbits t)`
      by fs [enable_stg_def,agp32_ID_ID_write_enable_WB_state_flag] >>
    `I' (5,SUC t) = I' (4,t)` by gs [is_sch_def,is_sch_writeback_def] >> fs [] >>
    `enable_stg 4 (agp32 fext fbits t)`
      by fs [enable_stg_def,agp32_ID_ID_write_enable_MEM_state_flag] >>
    Cases_on `isMemOp_hw_op (agp32 fext fbits t)` >-
     (`enable_stg 3 (agp32 fext fbits t)`
        by fs [enable_stg_def, agp32_ID_ID_write_enable_and_ID_EX_write_enable] >>
      Cases_on `reg_data_hazard (agp32 fext fbits t)` >-
       (fs [isJump_hw_op_def,enable_stg_def] >>
        METIS_TAC [agp32_ID_ID_write_enable_EX_jump_sel_then_no_reg_data_hazard]) >>
      `I' (3,SUC t) = I' (2,t)` by gs [is_sch_def,is_sch_execute_def] >> fs [] >>
      `I' (3,t) = NONE` by METIS_TAC [IF_instr_NOT_NONE_ID_NONE_THEN_EX_NONE] >>
      Cases_on `I' (5,t) = NONE` >> fs [Rel_def]) >>
    `I' (4,SUC t) = I' (3,t)` by gs [is_sch_def,is_sch_memory_def] >> fs [] >>
    `enable_stg 3 (agp32 fext fbits t)`
      by fs [enable_stg_def,agp32_ID_ID_write_enable_and_ID_EX_write_enable] >>
    Cases_on `reg_data_hazard (agp32 fext fbits t)` >-
     (fs [isJump_hw_op_def,enable_stg_def] >>
      METIS_TAC [agp32_ID_ID_write_enable_EX_jump_sel_then_no_reg_data_hazard]) >>
    `I' (3,SUC t) = I' (2,t)` by gs [is_sch_def,is_sch_execute_def] >> fs [] >>
    Cases_on `I' (5,t) = NONE` >> fs [Rel_def] >>
    `THE (I' (1,t)) > THE (I' (5,t)) /\ THE (I' (1,t)) < THE (I' (5,t)) + 2`
      by fs [Inv_Rel_def] >>
    `THE (I' (1,t)) = THE (I' (5,t)) + 1` by fs [] >> fs []) >>
  Cases_on `enable_stg 5 (agp32 fext fbits t)` >-
   (`I' (5,SUC t) = I' (4,t)` by gs [is_sch_def,is_sch_writeback_def] >>
    Cases_on `~enable_stg 3 (agp32 fext fbits t)` >> fs [] >-
     (`I' (2,SUC t) = I' (2,t) /\ I' (3,SUC t) = I' (3,t)`
        by METIS_TAC [is_sch_def,is_sch_disable_def] >> fs [] >>
      Cases_on `I' (5,t) = NONE` >> fs [Rel_def] >>
      `(fext t).ready` by (fs [enable_stg_def] >> METIS_TAC [agp32_WB_state_flag_and_fext_ready]) >>
      `THE (I' (2,t)) = THE (I' (5,t)) + 1`
        by METIS_TAC [EX_MEM_NONE_ID_instr_index_with_WB_instr_plus_1] >> fs []) >>
    `I' (2,SUC t) = I' (2,t)` by METIS_TAC [is_sch_def,is_sch_disable_def] >> fs [] >>
    `enable_stg 4 (agp32 fext fbits t)`
      by fs [enable_stg_def,agp32_MEM_state_flag_eq_WB_state_flag] >>
    `~isMemOp_hw_op (agp32 fext fbits t)`
      by fs [enable_stg_def,agp32_ID_EX_write_enable_no_MEM_stg_op] >>
    `I' (4,SUC t) = I' (3,t)` by METIS_TAC [is_sch_def,is_sch_memory_def] >> fs [] >>
    Cases_on `I' (5,t) = NONE` >> fs [Rel_def] >>
    `(fext t).ready` by (fs [enable_stg_def] >> METIS_TAC [agp32_WB_state_flag_and_fext_ready]) >>
    `THE (I' (2,t)) = THE (I' (5,t)) + 1`
      by METIS_TAC [EX_MEM_NONE_ID_instr_index_with_WB_instr_plus_1] >> fs []) >>
  Cases_on `enable_stg 4 (agp32 fext fbits t)` >-
   (fs [enable_stg_def] >> fs [agp32_MEM_state_flag_eq_WB_state_flag]) >>
  `~enable_stg 3 (agp32 fext fbits t)`
    by fs [enable_stg_def,agp32_MEM_state_flag_F_and_ID_EX_write_disable] >>
  gs [is_sch_def,is_sch_disable_def,Rel_def]
QED

(** IF **)
Theorem agp32_Rel_ag32_fext_MEM_correct_IF_not_NONE:
  !fext fbits a t I.
    is_mem fext_accessor_circuit (agp32 fext fbits) fext ==>
    is_sch I (agp32 fext fbits) a ==>
    Init (fext 0) (agp32 fext fbits 0) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (5,SUC t) = NONE ==>
    I (4,SUC t) = NONE ==>
    I (3,SUC t) = NONE ==>
    I (2,SUC t) = NONE ==>
    I (1,SUC t) <> NONE ==>
    (fext (SUC t)).mem = (FUNPOW Next (THE (I (1,SUC t)) - 1) a).MEM
Proof
  rw [] >>
  `(fext (SUC t)).mem = (fext t).mem` by METIS_TAC [agp32_mem_unchanged_when_WB_NONE] >>
  Cases_on `enable_stg 1 (agp32 fext fbits t)` >-
   (Cases_on `isJump_hw_op (agp32 fext fbits t)` >-
     (`I' (1,SUC t) = SOME (THE (I' (3,t)) + 1)` by fs [is_sch_def,is_sch_fetch_def] >>
      `isJump_isa_op (I' (3,t)) a` by fs [Rel_def,EX_Rel_spec_def,isJump_hw_op_def] >>
      `I' (3,t) <> NONE` by METIS_TAC [isJump_isa_op_not_none] >>
      `enable_stg 4 (agp32 fext fbits t)`
        by fs [enable_stg_def,agp32_IF_PC_write_enable_and_MEM_flag] >>
      `enable_stg 3 (agp32 fext fbits t)`
        by fs [enable_stg_def,agp32_IF_PC_write_enable_and_ID_EX_write_enable] >>
      Cases_on `isMemOp_hw_op (agp32 fext fbits t)` >-
       (fs [enable_stg_def] >>    
        METIS_TAC [MEM_stg_op_agp32_ID_EX_write_disable]) >>
      `I' (4,SUC t) = I' (3,t)` by gs [is_sch_def,is_sch_memory_def] >> fs []) >>
    Cases_on `isJump_isa_op (I' (1,t)) a \/ isJump_isa_op (I' (2,t)) a \/ I' (1,t) = NONE` >-
     gs [is_sch_def,is_sch_fetch_def,is_sch_execute_def] >>
    `enable_stg 2 (agp32 fext fbits t)`
      by fs [enable_stg_def,agp32_IF_PC_write_enable_and_ID_ID_write_enable] >>
    `I' (2,SUC t) = I' (1,t)` by METIS_TAC [is_sch_def,is_sch_decode_def] >> fs []) >>
  `~enable_stg 2 (agp32 fext fbits t)`
    by METIS_TAC [enable_stg_def,agp32_IF_PC_write_enable_and_ID_ID_write_enable] >>
  Cases_on `enable_stg 5 (agp32 fext fbits t)` >-
   (`I' (5,SUC t) = I' (4,t)` by gs [is_sch_def,is_sch_writeback_def] >>
    Cases_on `~enable_stg 3 (agp32 fext fbits t)` >> fs [] >-
     (`I' (1,SUC t) = I' (1,t) /\ I' (2,SUC t) = I' (2,t) /\ I' (3,SUC t) = I' (3,t)`
        by gs [is_sch_def,is_sch_disable_def] >> fs [] >>
      Cases_on `I' (5,t) = NONE` >> fs [Rel_def] >>
      `(fext t).ready` by (fs [enable_stg_def] >> METIS_TAC [agp32_WB_state_flag_and_fext_ready]) >>
      `THE (I' (1,t)) = THE (I' (5,t)) + 1` by fs [Inv_Rel_def] >> fs []) >>
    `enable_stg 4 (agp32 fext fbits t)`
      by fs [enable_stg_def,agp32_MEM_state_flag_eq_WB_state_flag] >>
    `~isMemOp_hw_op (agp32 fext fbits t)`
      by fs [enable_stg_def,agp32_ID_EX_write_enable_no_MEM_stg_op] >>
    `I' (4,SUC t) = I' (3,t)` by METIS_TAC [is_sch_def,is_sch_memory_def] >> fs [] >>
    `I' (1,SUC t) = I' (1,t) /\ I' (2,SUC t) = I' (2,t)`
      by METIS_TAC [is_sch_def,is_sch_disable_def] >> fs [] >>
    Cases_on `I' (5,t) = NONE` >> fs [Rel_def] >>
    `(fext t).ready` by (fs [enable_stg_def] >> METIS_TAC [agp32_WB_state_flag_and_fext_ready]) >>
    `THE (I' (1,t)) = THE (I' (5,t)) + 1` by fs [Inv_Rel_def] >> fs []) >>
  `~enable_stg 4 (agp32 fext fbits t)` by fs [enable_stg_def,agp32_MEM_state_flag_eq_WB_state_flag] >>
  `~enable_stg 3 (agp32 fext fbits t)`
    by fs [enable_stg_def,agp32_MEM_state_flag_F_and_ID_EX_write_disable] >>
  gs [is_sch_def,is_sch_disable_def,Rel_def]
QED


(** data_rdata **)
(** LoadMem **)
(** WB enabled **)
Theorem agp32_Rel_ag32_read_mem_data_rdata_correct_WB_enable:
  !fext fbits a t I.
    is_mem fext_accessor_circuit (agp32 fext fbits) fext ==>
    is_sch I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (5,SUC t) <> NONE ==>
    (fext (SUC t)).ready ==>
    (agp32 fext fbits (SUC t)).WB.WB_opc = 4w ==>
    enable_stg 5 (agp32 fext fbits t) ==>
    (fext (SUC t)).data_rdata = mem_data_rdata (FUNPOW Next (THE (I (5,SUC t)) - 1) a)
Proof
  rw [] >> `I' (5,SUC t) = I' (4,t)` by fs [is_sch_def,is_sch_writeback_def] >>
  `align_addr (agp32 fext fbits (SUC t)).data_addr =
  mem_data_addr (FUNPOW Next (THE (I' (5,SUC t)) - 1) a)`
    by METIS_TAC [agp32_Rel_ag32_data_addr_correct_read_mem] >>
  `(agp32 fext fbits t).MEM.MEM_opc = 4w` by METIS_TAC [agp32_WB_opc_MEM_opc_when_WB_enabled] >>
  `(agp32 fext fbits t).MEM.MEM_read_mem` by METIS_TAC [agp32_MEM_read_mem_MEM_opc_4w_5w] >>
  `opc (FUNPOW Next (THE (I' (4,t)) - 1) a) = 4w` by fs [Rel_def,MEM_Rel_def] >>
  fs [mem_data_rdata_def] >>
  `(fext t).ready` by (fs [enable_stg_def] >> METIS_TAC [agp32_WB_state_flag_and_fext_ready]) >>
  last_assum (assume_tac o is_mem_def_mem_no_errors) >>
  `(agp32 fext fbits (SUC t)).command = 2w`
    by METIS_TAC [agp32_Rel_ag32_command_correct_read_mem_WB_enable] >>
  last_assum (mp_tac o is_mem_data_read `SUC t`) >> rw [] >>
  Cases_on `m` >> fs [] >-
   (fs [Rel_def] >>
    Cases_on `I' (5,t) = NONE` >> fs [] >>
    `THE (I' (4,t)) = THE (I' (5,t)) + 1`
      by METIS_TAC [MEM_instr_index_with_WB_instr_plus_1] >> fs []) >>
  `~(fext (0 + SUC t)).ready` by fs [] >> fs []
QED

(** WB is disabled and fext is not ready at the previous cycle **)
Theorem agp32_Rel_ag32_read_mem_data_rdata_correct_WB_disable_fext_not_ready:
  !fext fbits a t I.
    is_mem fext_accessor_circuit (agp32 fext fbits) fext ==>
    is_sch I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (5,SUC t) <> NONE ==>
    (fext (SUC t)).ready ==>
    ~(fext t).ready ==>
    (agp32 fext fbits (SUC t)).WB.WB_opc = 4w ==>
    ~enable_stg 5 (agp32 fext fbits t) ==>
    (fext (SUC t)).data_rdata = mem_data_rdata (FUNPOW Next (THE (I (5,SUC t)) - 1) a)
Proof
  rw [] >> Cases_on `MAX_SET {t0 | t0 < t /\ (fext t0).ready}` >-
   (Cases_on `{t0 | t0 < t /\ (fext t0).ready} = {}` >-
     (`!t0. t0 < t ==> ~(fext t0).ready` by METIS_TAC [EMPTY_no_fext_ready_cycle] >>
      `(agp32 fext fbits t).WB.WB_opc = (agp32 fext fbits 0).WB.WB_opc`
        by fs [WB_opc_unchanged_after_disabled_cycles_0] >>
      fs [agp32_WB_opc_unchanged_when_WB_disabled,agp32_init_WB_opc]) >>
    `!t0. t0 < t - 1 ==> ~(fext (t0 + 1)).ready`
      by METIS_TAC [MAX_SET_0_no_fext_ready_cycle] >>
    `(agp32 fext fbits (t - 1 + 1)).WB.WB_opc = (agp32 fext fbits 1).WB.WB_opc`
      by fs [WB_opc_unchanged_after_disabled_cycles] >>
    `t - 1 + 1 = t` by (Cases_on `t` >> fs []) >> fs [] >>
    `(agp32 fext fbits t).WB.WB_opc = 4w` by fs [agp32_WB_opc_unchanged_when_WB_disabled] >>
    `~enable_stg 5 (agp32 fext fbits 0)` by fs [agp32_init_ctrl_flags,enable_stg_def] >>
    `(agp32 fext fbits (SUC 0)).WB.WB_opc = 16w`
      by fs [agp32_WB_opc_unchanged_when_WB_disabled,agp32_init_WB_opc] >>
    fs [SUC_ONE_ADD]) >>
  Q.ABBREV_TAC `i = SUC n` >> `i <> 0` by fs [Abbr `i`] >>
  `FINITE {t0 | t0 < t /\ (fext t0).ready}` by fs [FINITE_max_ready_cycle] >>
  Cases_on `{t0 | t0 < t /\ (fext t0).ready} = {}` >> fs [MAX_SET_DEF] >>
  `i IN {t0 | t0 < t /\ (fext t0).ready}` by METIS_TAC [MAX_SET_DEF] >> fs [MAX_SET_DEF] >>
  last_assum (assume_tac o is_mem_def_mem_no_errors) >>
  Cases_on_word_value `(agp32 fext fbits (SUC i)).command` >>
  fs [agp32_command_impossible_values] >-
   (last_assum (mp_tac o is_mem_data_flush `SUC i`) >> simp [] >> strip_tac >>
    `m + SUC i = SUC t` by METIS_TAC [same_t_and_m_under_MAX_SET_SUC] >> fs [] >>
    `(agp32 fext fbits (SUC i)).WB.WB_opc = 4w`
      by METIS_TAC [WB_opc_unchanged_after_disabled_cycles] >>
    Cases_on `enable_stg 5 (agp32 fext fbits i)` >-
     gs [agp32_Rel_ag32_command_correct_read_mem_WB_enable] >>
    `(agp32 fext fbits (SUC i)).WB.WB_opc <> 16w` by fs [] >>
    gs [agp32_Rel_ag32_command_correct_WB_disable_fext_ready]) >-
   (last_assum (mp_tac o is_mem_data_write `SUC i`) >> simp [] >> strip_tac >>
    `m + SUC i = SUC t` by METIS_TAC [same_t_and_m_under_MAX_SET_SUC] >> fs [] >>
    `(agp32 fext fbits (SUC i)).WB.WB_opc = 4w`
      by METIS_TAC [WB_opc_unchanged_after_disabled_cycles] >>
    Cases_on `enable_stg 5 (agp32 fext fbits i)` >-
     gs [agp32_Rel_ag32_command_correct_read_mem_WB_enable] >>
    `(agp32 fext fbits (SUC i)).WB.WB_opc <> 16w` by fs [] >>
    gs [agp32_Rel_ag32_command_correct_WB_disable_fext_ready]) >-
   (last_assum (mp_tac o is_mem_data_read `SUC i`) >> simp [] >> strip_tac >>
    `m + SUC i = SUC t` by METIS_TAC [same_t_and_m_under_MAX_SET_SUC] >> fs [] >>
    `(fext (SUC t)).mem = (FUNPOW Next (THE (I' (5,SUC t))) a).MEM`
       by METIS_TAC [agp32_Rel_ag32_fext_MEM_correct_WB_not_NONE] >>
    `I' (5,SUC t) = I' (5,t)` by fs [is_sch_def,is_sch_disable_def] >> fs [] >>
    `(agp32 fext fbits (SUC t)).WB.WB_opc = (agp32 fext fbits t).WB.WB_opc`
      by fs [agp32_WB_opc_unchanged_when_WB_disabled] >>
    `opc (FUNPOW Next (THE (I' (5,t)) - 1) a) = 4w` by fs [Rel_def,WB_Rel_def] >>
    simp [mem_data_rdata_def] >>
    `(agp32 fext fbits (SUC i)).data_addr = (agp32 fext fbits (m + SUC i)).data_addr`
      by METIS_TAC [data_addr_wdata_wstrb_unchanged_after_disabled_cycles] >>
    `align_addr (agp32 fext fbits (SUC t)).data_addr =
    mem_data_addr (FUNPOW Next (THE (I' (5,SUC t)) - 1) a)`
      by METIS_TAC [agp32_Rel_ag32_data_addr_correct_read_mem] >>
    `align_addr (agp32 fext fbits (SUC i)).data_addr =
    mem_data_addr (FUNPOW Next (THE (I' (5,t)) - 1) a)` by fs [Rel_def] >> fs [] >>
    `(fext (SUC i)).mem = (fext i).mem`
      by (Cases_on `m` >> fs [] >> `0 < SUC n` by rw [] >>
          `(fext (0 + SUC i)).mem = (fext i).mem` by fs [] >> fs []) >>
    `(fext (SUC i)).mem = (fext (SUC t)).mem` by fs [] >> fs [] >>
    `~is_wrMEM_isa (FUNPOW Next (THE (I' (5,t)) - 1) a)` by fs [is_wrMEM_isa_def] >>
    METIS_TAC [word_at_addr_not_changed_after_normal_instrs]) >-
   (last_assum (mp_tac o is_mem_inst_read `SUC i`) >> simp [] >> strip_tac >>
    `m + SUC i = SUC t` by METIS_TAC [same_t_and_m_under_MAX_SET_SUC] >> fs [] >>
    `(agp32 fext fbits (SUC i)).WB.WB_opc = 4w`
      by METIS_TAC [WB_opc_unchanged_after_disabled_cycles] >>
    Cases_on `enable_stg 5 (agp32 fext fbits i)` >-
     gs [agp32_Rel_ag32_command_correct_read_mem_WB_enable] >>
    `(agp32 fext fbits (SUC i)).WB.WB_opc <> 16w` by fs [] >>
    gs [agp32_Rel_ag32_command_correct_WB_disable_fext_ready]) >>
  last_assum (mp_tac o is_mem_do_nothing `SUC i`) >> simp [] >> strip_tac >>
  Cases_on `SUC i = t` >> fs [] >>
  Cases_on `SUC i > t` >> fs [] >>
  `SUC i < t` by fs [] >>
  `(SUC i) IN {t0 | t0 < t /\ (fext t0).ready}` by fs [] >>
  `(SUC i) <= i` by METIS_TAC [MAX_SET_DEF] >> fs []
QED

(** WB disabled **) 
Theorem agp32_Rel_ag32_read_mem_data_rdata_correct_WB_disable:
  !fext fbits a t I.
    is_mem fext_accessor_circuit (agp32 fext fbits) fext ==>
    is_sch I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (5,SUC t) <> NONE ==>
    (fext (SUC t)).ready ==>
    (agp32 fext fbits (SUC t)).WB.WB_opc = 4w ==>
    ~enable_stg 5 (agp32 fext fbits t) ==>
    (fext (SUC t)).data_rdata = mem_data_rdata (FUNPOW Next (THE (I (5,SUC t)) - 1) a)
Proof
  rw [] >> Cases_on `(fext t).ready` >-
   (`I' (5,SUC t) = I' (5,t)` by fs [is_sch_def,is_sch_disable_def] >>
    `(agp32 fext fbits (SUC t)).WB.WB_opc = (agp32 fext fbits t).WB.WB_opc`
      by fs [agp32_WB_opc_unchanged_when_WB_disabled] >>
    last_assum (assume_tac o is_mem_def_mem_no_errors) >>
    `(agp32 fext fbits (SUC t)).command = 0w`
      by gs [agp32_Rel_ag32_command_correct_WB_disable_fext_ready] >>
    last_assum (mp_tac o is_mem_do_nothing `SUC t`) >> rw [] >>
    fs [Rel_def,MEM_data_rel_def]) >>
  METIS_TAC [agp32_Rel_ag32_read_mem_data_rdata_correct_WB_disable_fext_not_ready]
QED

Theorem agp32_Rel_ag32_read_mem_data_rdata_correct:
  !fext fbits a t I.
    is_mem fext_accessor_circuit (agp32 fext fbits) fext ==>
    is_sch I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (5,SUC t) <> NONE ==>
    (fext (SUC t)).ready ==>
    (agp32 fext fbits (SUC t)).WB.WB_opc = 4w ==>
    (fext (SUC t)).data_rdata = mem_data_rdata (FUNPOW Next (THE (I (5,SUC t)) - 1) a)
Proof
  rw [] >> Cases_on `enable_stg 5 (agp32 fext fbits t)` >>
  METIS_TAC [agp32_Rel_ag32_read_mem_data_rdata_correct_WB_enable,
             agp32_Rel_ag32_read_mem_data_rdata_correct_WB_disable]
QED

(** LoadMemByte **)
(** WB enabled **)
Theorem agp32_Rel_ag32_read_mem_byte_data_rdata_correct_WB_enable:
  !fext fbits a t I.
    is_mem fext_accessor_circuit (agp32 fext fbits) fext ==>
    is_sch I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (5,SUC t) <> NONE ==>
    (fext (SUC t)).ready ==>
    (agp32 fext fbits (SUC t)).WB.WB_opc = 5w ==>
    enable_stg 5 (agp32 fext fbits t) ==>
    (fext (SUC t)).data_rdata = mem_data_rdata_extra (FUNPOW Next (THE (I (5,SUC t)) - 1) a)
Proof
  rw [] >> `I' (5,SUC t) = I' (4,t)` by fs [is_sch_def,is_sch_writeback_def] >>
  `(agp32 fext fbits (SUC t)).data_addr =
  mem_data_addr (FUNPOW Next (THE (I' (5,SUC t)) - 1) a)`
    by METIS_TAC [agp32_Rel_ag32_data_addr_correct_read_mem_byte] >>
  `(agp32 fext fbits t).MEM.MEM_opc = 5w` by METIS_TAC [agp32_WB_opc_MEM_opc_when_WB_enabled] >>
  `(agp32 fext fbits t).MEM.MEM_read_mem` by METIS_TAC [agp32_MEM_read_mem_MEM_opc_4w_5w] >>
  `opc (FUNPOW Next (THE (I' (4,t)) - 1) a) = 5w` by fs [Rel_def,MEM_Rel_def] >>
  fs [mem_data_rdata_extra_def] >>
  `(fext t).ready` by (fs [enable_stg_def] >> METIS_TAC [agp32_WB_state_flag_and_fext_ready]) >>
  last_assum (assume_tac o is_mem_def_mem_no_errors) >>
  `(agp32 fext fbits (SUC t)).command = 2w`
    by METIS_TAC [agp32_Rel_ag32_command_correct_read_mem_byte_WB_enable] >>
  last_assum (mp_tac o is_mem_data_read `SUC t`) >> rw [] >>
  Cases_on `m` >> fs [] >-
   (fs [Rel_def] >>
    Cases_on `I' (5,t) = NONE` >> fs [] >>
    `THE (I' (4,t)) = THE (I' (5,t)) + 1`
      by METIS_TAC [MEM_instr_index_with_WB_instr_plus_1] >> fs []) >>
  `~(fext (0 + SUC t)).ready` by fs [] >> fs []
QED

(** WB is disabled and fext is not ready at the previous cycle **)
Theorem agp32_Rel_ag32_read_mem_byte_data_rdata_correct_WB_disable_fext_not_ready:
  !fext fbits a t I.
    is_mem fext_accessor_circuit (agp32 fext fbits) fext ==>
    is_sch I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (5,SUC t) <> NONE ==>
    (fext (SUC t)).ready ==>
    ~(fext t).ready ==>
    (agp32 fext fbits (SUC t)).WB.WB_opc = 5w ==>
    ~enable_stg 5 (agp32 fext fbits t) ==>
    (fext (SUC t)).data_rdata = mem_data_rdata_extra (FUNPOW Next (THE (I (5,SUC t)) - 1) a)
Proof
  rw [] >> Cases_on `MAX_SET {t0 | t0 < t /\ (fext t0).ready}` >-
   (Cases_on `{t0 | t0 < t /\ (fext t0).ready} = {}` >-
     (`!t0. t0 < t ==> ~(fext t0).ready` by METIS_TAC [EMPTY_no_fext_ready_cycle] >>
      `(agp32 fext fbits t).WB.WB_opc = (agp32 fext fbits 0).WB.WB_opc`
        by fs [WB_opc_unchanged_after_disabled_cycles_0] >>
      fs [agp32_WB_opc_unchanged_when_WB_disabled,agp32_init_WB_opc]) >>
    `!t0. t0 < t - 1 ==> ~(fext (t0 + 1)).ready`
      by METIS_TAC [MAX_SET_0_no_fext_ready_cycle] >>
    `(agp32 fext fbits (t - 1 + 1)).WB.WB_opc = (agp32 fext fbits 1).WB.WB_opc`
      by fs [WB_opc_unchanged_after_disabled_cycles] >>
    `t - 1 + 1 = t` by (Cases_on `t` >> fs []) >> fs [] >>
    `(agp32 fext fbits t).WB.WB_opc = 5w` by fs [agp32_WB_opc_unchanged_when_WB_disabled] >>
    `~enable_stg 5 (agp32 fext fbits 0)` by fs [agp32_init_ctrl_flags,enable_stg_def] >>
    `(agp32 fext fbits (SUC 0)).WB.WB_opc = 16w`
      by fs [agp32_WB_opc_unchanged_when_WB_disabled,agp32_init_WB_opc] >>
    fs [SUC_ONE_ADD]) >>
  Q.ABBREV_TAC `i = SUC n` >> `i <> 0` by fs [Abbr `i`] >>
  `FINITE {t0 | t0 < t /\ (fext t0).ready}` by fs [FINITE_max_ready_cycle] >>
  Cases_on `{t0 | t0 < t /\ (fext t0).ready} = {}` >> fs [MAX_SET_DEF] >>
  `i IN {t0 | t0 < t /\ (fext t0).ready}` by METIS_TAC [MAX_SET_DEF] >> fs [MAX_SET_DEF] >>
  last_assum (assume_tac o is_mem_def_mem_no_errors) >>
  Cases_on_word_value `(agp32 fext fbits (SUC i)).command` >>
  fs [agp32_command_impossible_values] >-
   (last_assum (mp_tac o is_mem_data_flush `SUC i`) >> simp [] >> strip_tac >>
    `m + SUC i = SUC t` by METIS_TAC [same_t_and_m_under_MAX_SET_SUC] >> fs [] >>
    `(agp32 fext fbits (SUC i)).WB.WB_opc = 5w`
      by METIS_TAC [WB_opc_unchanged_after_disabled_cycles] >>
    Cases_on `enable_stg 5 (agp32 fext fbits i)` >-
     gs [agp32_Rel_ag32_command_correct_read_mem_byte_WB_enable] >>
    `(agp32 fext fbits (SUC i)).WB.WB_opc <> 16w` by fs [] >>
    gs [agp32_Rel_ag32_command_correct_WB_disable_fext_ready]) >-
   (last_assum (mp_tac o is_mem_data_write `SUC i`) >> simp [] >> strip_tac >>
    `m + SUC i = SUC t` by METIS_TAC [same_t_and_m_under_MAX_SET_SUC] >> fs [] >>
    `(agp32 fext fbits (SUC i)).WB.WB_opc = 5w`
      by METIS_TAC [WB_opc_unchanged_after_disabled_cycles] >>
    Cases_on `enable_stg 5 (agp32 fext fbits i)` >-
     gs [agp32_Rel_ag32_command_correct_read_mem_byte_WB_enable] >>
    `(agp32 fext fbits (SUC i)).WB.WB_opc <> 16w` by fs [] >>
    gs [agp32_Rel_ag32_command_correct_WB_disable_fext_ready]) >-
   (last_assum (mp_tac o is_mem_data_read `SUC i`) >> simp [] >> strip_tac >>
    `m + SUC i = SUC t` by METIS_TAC [same_t_and_m_under_MAX_SET_SUC] >> fs [] >>
    `(fext (SUC t)).mem = (FUNPOW Next (THE (I' (5,SUC t))) a).MEM`
       by METIS_TAC [agp32_Rel_ag32_fext_MEM_correct_WB_not_NONE] >>
    `I' (5,SUC t) = I' (5,t)` by fs [is_sch_def,is_sch_disable_def] >> fs [] >>
    `(agp32 fext fbits (SUC t)).WB.WB_opc = (agp32 fext fbits t).WB.WB_opc`
      by fs [agp32_WB_opc_unchanged_when_WB_disabled] >>
    `opc (FUNPOW Next (THE (I' (5,t)) - 1) a) = 5w` by fs [Rel_def,WB_Rel_def] >>
    simp [mem_data_rdata_extra_def] >>
    `(agp32 fext fbits (SUC i)).data_addr = (agp32 fext fbits (m + SUC i)).data_addr`
      by METIS_TAC [data_addr_wdata_wstrb_unchanged_after_disabled_cycles] >>
    `(agp32 fext fbits (SUC i)).data_addr =
    mem_data_addr (FUNPOW Next (THE (I' (5,SUC t)) - 1) a)`
      by METIS_TAC [agp32_Rel_ag32_data_addr_correct_read_mem_byte] >> fs [] >>
    `(fext (SUC i)).mem = (fext i).mem`
      by (Cases_on `m` >> fs [] >> `0 < SUC n` by rw [] >>
          `(fext (0 + SUC i)).mem = (fext i).mem` by fs [] >> fs []) >>
    `~is_wrMEM_isa (FUNPOW Next (THE (I' (5,t)) - 1) a)` by fs [is_wrMEM_isa_def] >>
    METIS_TAC [word_at_addr_not_changed_after_normal_instrs]) >-
   (last_assum (mp_tac o is_mem_inst_read `SUC i`) >> simp [] >> strip_tac >>
    `m + SUC i = SUC t` by METIS_TAC [same_t_and_m_under_MAX_SET_SUC] >> fs [] >>
    `(agp32 fext fbits (SUC i)).WB.WB_opc = 5w`
      by METIS_TAC [WB_opc_unchanged_after_disabled_cycles] >>
    Cases_on `enable_stg 5 (agp32 fext fbits i)` >-
     gs [agp32_Rel_ag32_command_correct_read_mem_byte_WB_enable] >>
    `(agp32 fext fbits (SUC i)).WB.WB_opc <> 16w` by fs [] >>
    gs [agp32_Rel_ag32_command_correct_WB_disable_fext_ready]) >>
  last_assum (mp_tac o is_mem_do_nothing `SUC i`) >> simp [] >> strip_tac >>
  Cases_on `SUC i = t` >> fs [] >>
  Cases_on `SUC i > t` >> fs [] >>
  `SUC i < t` by fs [] >>
  `(SUC i) IN {t0 | t0 < t /\ (fext t0).ready}` by fs [] >>
  `(SUC i) <= i` by METIS_TAC [MAX_SET_DEF] >> fs []
QED

(** WB disabled **) 
Theorem agp32_Rel_ag32_read_mem_byte_data_rdata_correct_WB_disable:
  !fext fbits a t I.
    is_mem fext_accessor_circuit (agp32 fext fbits) fext ==>
    is_sch I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (5,SUC t) <> NONE ==>
    (fext (SUC t)).ready ==>
    (agp32 fext fbits (SUC t)).WB.WB_opc = 5w ==>
    ~enable_stg 5 (agp32 fext fbits t) ==>
    (fext (SUC t)).data_rdata = mem_data_rdata_extra (FUNPOW Next (THE (I (5,SUC t)) - 1) a)
Proof
  rw [] >> Cases_on `(fext t).ready` >-
   (`I' (5,SUC t) = I' (5,t)` by fs [is_sch_def,is_sch_disable_def] >>
    `(agp32 fext fbits (SUC t)).WB.WB_opc = (agp32 fext fbits t).WB.WB_opc`
      by fs [agp32_WB_opc_unchanged_when_WB_disabled] >>
    last_assum (assume_tac o is_mem_def_mem_no_errors) >>
    `(agp32 fext fbits (SUC t)).command = 0w`
      by gs [agp32_Rel_ag32_command_correct_WB_disable_fext_ready] >>
    last_assum (mp_tac o is_mem_do_nothing `SUC t`) >> rw [] >>
    fs [Rel_def,MEM_data_rel_def]) >>
  METIS_TAC [agp32_Rel_ag32_read_mem_byte_data_rdata_correct_WB_disable_fext_not_ready]
QED

Theorem agp32_Rel_ag32_read_mem_byte_data_rdata_correct:
  !fext fbits a t I.
    is_mem fext_accessor_circuit (agp32 fext fbits) fext ==>
    is_sch I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (5,SUC t) <> NONE ==>
    (fext (SUC t)).ready ==>
    (agp32 fext fbits (SUC t)).WB.WB_opc = 5w ==>
    (fext (SUC t)).data_rdata = mem_data_rdata_extra (FUNPOW Next (THE (I (5,SUC t)) - 1) a)
Proof
  rw [] >> Cases_on `enable_stg 5 (agp32 fext fbits t)` >>
  METIS_TAC [agp32_Rel_ag32_read_mem_byte_data_rdata_correct_WB_enable,
             agp32_Rel_ag32_read_mem_byte_data_rdata_correct_WB_disable]
QED


(** acc_res **)
Theorem agp32_Rel_ag32_acc_res_correct:
  !fext fbits a t I.
    is_mem fext_accessor_circuit (agp32 fext fbits) fext ==>
    is_sch I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (5, SUC t) <> NONE ==>
    (agp32 fext fbits (SUC t)).WB.WB_state_flag ==>
    (agp32 fext fbits (SUC t)).WB.WB_opc = 8w ==>
    (agp32 fext fbits (SUC t)).acc_res = acc_res (FUNPOW Next (THE (I (5,SUC t)) − 1) a)
Proof
  rw [] >> Cases_on `enable_stg 5 (agp32 fext fbits t)` >-
   (`(agp32 fext fbits (SUC t)).state = 2w` by fs [agp32_state_acc_WB_enable] >>
    gs [enable_stg_def,agp32_WB_state_flag_and_state]) >>
  Q.ABBREV_TAC `s = agp32 fext fbits t` >>
  Q.ABBREV_TAC `s' = procs [agp32_next_state; WB_pipeline; MEM_pipeline; EX_pipeline;
                            REG_write; ID_pipeline; IF_PC_update] (fext t) s s` >>
  `(agp32 fext fbits (SUC t)).acc_res = (Acc_compute (fext t) s s').acc_res`
    by gs [agp32_acc_state_res_and_ready_updated_by_Acc_compute] >>
  rw [Acc_compute_def] >-
   (`(agp32 fext fbits (SUC t)).state = 2w` by gs [Abbr `s`,agp32_acc_arg_ready_then_next_state_2w] >>
    gs [agp32_WB_state_flag_and_state]) >-
   (Cases_on `t = 0` >-
     (`~enable_stg 5 (agp32 fext fbits 0)` by fs [enable_stg_def,agp32_init_ctrl_flags] >>
      `I' (5,SUC 0) = I' (5,0)` by fs [is_sch_def,is_sch_disable_def] >>
      gs [is_sch_def,is_sch_init_def]) >>
    `s'.acc_state = s.acc_state`
      by METIS_TAC [Abbr `s`,Abbr `s'`,agp32_same_acc_items_until_Acc_compute] >>
    `~s.acc_res_ready` by gs [agp32_acc_state_0w_then_acc_res_not_ready,Abbr `s`] >>
    `s.state = 2w` by gs [agp32_acc_state_0w_then_state_2w,Abbr `s`] >>
    `(agp32 fext fbits (SUC t)).state = (agp32_next_state (fext t) s s).state`
      by fs [agp32_command_state_updated_by_agp32_next_state] >>
    `(fext t).error = 0w` by fs [is_mem_def,mem_no_errors_def] >>
    fs [agp32_next_state_def] >>
    gs [agp32_WB_state_flag_and_state]) >-
   (rw [acc_res_def,acc_arg_def,accelerator_f_def] >>
    `I' (5,SUC t) = I' (5,t)` by fs [is_sch_def,is_sch_disable_def] >>
    `(agp32 fext fbits t).WB.WB_opc = 8w` by fs [agp32_WB_opc_unchanged_when_WB_disabled] >>
    fs [Rel_def,MEM_req_rel_def,Abbr `s`]) >>
  `s'.acc_state = s.acc_state`
    by METIS_TAC [Abbr `s`,Abbr `s'`,agp32_same_acc_items_until_Acc_compute] >>
  METIS_TAC [agp32_acc_state_possible_values,Abbr `s`]
QED


(* MEM_data_rel *)
Theorem agp32_Rel_ag32_MEM_data_rel_correct:
  !fext fbits a t I.
    is_mem fext_accessor_circuit (agp32 fext fbits) fext ==>
    is_sch I (agp32 fext fbits) a ==>
    Rel I (fext t) (agp32 fext fbits (t-1)) (agp32 fext fbits t) a t ==>
    I (5,SUC t) <> NONE ==>
    MEM_data_rel (fext (SUC t)) (agp32 fext fbits (SUC t)) a (THE (I (5,SUC t)))
Proof
  rw [MEM_data_rel_def] >>
  METIS_TAC [agp32_Rel_ag32_read_mem_data_rdata_correct,
             agp32_Rel_ag32_read_mem_byte_data_rdata_correct,
             agp32_Rel_ag32_acc_res_correct]
QED

val _ = export_theory ();
