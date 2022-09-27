open hardwarePreamble translatorTheory translatorCoreLib agp32StateTheory agp32EnvironmentTheory;

(* Pipelined Silver processor implementation *)
val _ = new_theory "agp32Processor";

val _ = prefer_num ();
val _ = guess_lengths ();


(* multiplexer functions used by different blocks *)
Definition MUX_21_def:
  MUX_21 sel input0 input1 : word32 =
  if sel then input1 else input0
End

Definition MUX_41_def:
  MUX_41 (sel:word2) input0 input1 input2 input3 : word32 =
  if sel = 0w then input0
  else if sel = 1w then input1
  else if sel = 2w then input2
  else input3
End

Definition MUX_81_def:
  MUX_81 (sel:word3) input0 input1 input2 input3 input4 input5 input6 input7 : word32 =
  if sel = 0w then input0
  else if sel = 1w then input1
  else if sel = 2w then input2
  else if sel = 3w then input3
  else if sel = 4w then input4
  else if sel = 5w then input5
  else if sel = 6w then input6
  else input7
End


(* always_comb related *)
(** assign instruction **)
Definition IF_instr_update_def:
  IF_instr_update fext (s:state_circuit) s' =
  s' with IF := s'.IF with IF_instr := if fext.ready then fext.inst_rdata else 0x0000003Fw
End
   
(** compute PC **)
Definition IF_PC_input_update_def:
  IF_PC_input_update (fext:ext) s s' =
  s' with IF := s'.IF with
                  IF_PC_input := MUX_21 s'.EX.EX_jump_sel (s.PC + 4w) s'.EX.EX_jump_addr
End

Theorem IF_PC_input_update_trans = REWRITE_RULE [MUX_21_def] IF_PC_input_update_def

(** decode instr **)
Definition ID_opc_func_update_def:
  ID_opc_func_update (fext:ext) (s:state_circuit) s' =
  let s' = if word_bit 24 s'.ID.ID_instr then
             if word_bit 31 s'.ID.ID_instr then
               s' with ID := s'.ID with ID_opc := 13w
             else if (23 >< 9) s'.ID.ID_instr = 0w then
               s' with ID := s'.ID with ID_opc := 14w
             else
               s' with ID := s'.ID with ID_opc := 15w
           else if (5 >< 0) s'.ID.ID_instr = 10w \/ (5 >< 0) s'.ID.ID_instr = 11w \/
                   (5 >< 0) s'.ID.ID_instr = 12w then                                             
             s' with ID := s'.ID with ID_opc := (5 >< 0) s'.ID.ID_instr
           else if word_bit 31 s'.ID.ID_instr then
             s' with ID := s'.ID with ID_opc := 15w
           else if (5 >< 0) s'.ID.ID_instr <+ 10w then
             s' with ID := s'.ID with ID_opc := (5 >< 0) s'.ID.ID_instr
           else
             s' with ID := s'.ID with ID_opc := 15w in
  if s'.ID.ID_opc = 0w \/ s'.ID.ID_opc = 6w \/ s'.ID.ID_opc = 9w \/ 
     s'.ID.ID_opc = 10w \/ s'.ID.ID_opc = 11w then
    s' with ID := s'.ID with ID_func := (9 >< 6) s'.ID.ID_instr
  else if s'.ID.ID_opc = 1w then
    s' with ID := s'.ID with ID_func := ((3w:word2) @@ ((7 >< 6) s'.ID.ID_instr))
  else
    s' with ID := s'.ID with ID_func := 9w
End

(** update the data from read_data and imm for A/B/W **)
Definition ID_data_update_def:
  ID_data_update (fext:ext) s s' =
  let s' = s' with ID := s'.ID with ID_addrA := (22 >< 17) s'.ID.ID_instr;
      s' = s' with ID := s'.ID with ID_addrB := (15 >< 10) s'.ID.ID_instr;
      s' = s' with ID := s'.ID with ID_addrW := (30 >< 25) s'.ID.ID_instr;
      s' = s' with ID := s'.ID with ID_addrA_disable := word_bit 23 s'.ID.ID_instr;
      s' = s' with ID := s'.ID with ID_addrB_disable := word_bit 16 s'.ID.ID_instr;
      s' = s' with ID := s'.ID with ID_addrW_disable := word_bit 31 s'.ID.ID_instr;
      s' = s' with ID := s'.ID with ID_read_dataA := s'.R s'.ID.ID_addrA;
      s' = s' with ID := s'.ID with ID_read_dataB := s'.R s'.ID.ID_addrB;
      s' = s' with ID := s'.ID with ID_read_dataW := s'.R s'.ID.ID_addrW;
      s' = s' with ID := s'.ID with ID_immA := sw2sw ((22 >< 17) s'.ID.ID_instr);
      s' = s' with ID := s'.ID with ID_immB := sw2sw ((15 >< 10) s'.ID.ID_instr);
      s' = s' with ID := s'.ID with ID_immW := sw2sw ((30 >< 25) s'.ID.ID_instr);
      s' = s' with ID := s'.ID with ID_ForwardA := if s'.ID.ID_addrA = s.WB.WB_addrW /\
                                                      s.WB.WB_write_reg /\ s'.WB.WB_state_flag then T
                                                   else F;
      s' = s' with ID := s'.ID with ID_ForwardB := if s'.ID.ID_addrB = s.WB.WB_addrW /\
                                                      s.WB.WB_write_reg /\ s'.WB.WB_state_flag then T
                                                   else F;
      s' = s' with ID := s'.ID with ID_ForwardW := if s'.ID.ID_addrW = s.WB.WB_addrW /\
                                                      s.WB.WB_write_reg /\ s'.WB.WB_state_flag then T
                                                   else F;
      s' = s' with ID := s'.ID with ID_read_dataA_updated :=
           MUX_21 s'.ID.ID_ForwardA s'.ID.ID_read_dataA s'.WB.WB_write_data;
      s' = s' with ID := s'.ID with ID_read_dataB_updated :=
           MUX_21 s'.ID.ID_ForwardB s'.ID.ID_read_dataB s'.WB.WB_write_data;
      s' = s' with ID := s'.ID with ID_read_dataW_updated :=
           MUX_21 s'.ID.ID_ForwardW s'.ID.ID_read_dataW s'.WB.WB_write_data;
      s' = s' with ID := s'.ID with ID_dataA :=
           MUX_21 (word_bit 23 s'.ID.ID_instr) s'.ID.ID_read_dataA_updated s'.ID.ID_immA;
      s' = s' with ID := s'.ID with ID_dataB :=
           MUX_21 (word_bit 16 s'.ID.ID_instr) s'.ID.ID_read_dataB_updated s'.ID.ID_immB in
    s' with ID := s'.ID with ID_dataW :=
    MUX_21 (word_bit 31 s'.ID.ID_instr) s'.ID.ID_read_dataW_updated s'.ID.ID_immW
End

Theorem ID_data_update_trans = REWRITE_RULE [MUX_21_def] ID_data_update_def

(** generate immediate **)
Definition ID_imm_update_def:
  ID_imm_update (fext:ext) (s:state_circuit) s' =
  if word_bit 31 s'.ID.ID_instr /\ word_bit 24 s'.ID.ID_instr then
    if word_bit 23 s'.ID.ID_instr then
      s' with ID := s'.ID with ID_imm := 0w - w2w ((22 >< 0) s'.ID.ID_instr)
    else
      s' with ID := s'.ID with ID_imm := w2w ((22 >< 0) s'.ID.ID_instr)
  else if word_bit 24 s'.ID.ID_instr /\ (23 >< 9) s'.ID.ID_instr = 0w then
    s' with ID := s'.ID with ID_imm := w2w ((8 >< 0) s'.ID.ID_instr)
  else
    s' with ID := s'.ID with ID_imm := 0w
End

(** set up flags of EX stage **)
Definition EX_ctrl_update_def:
  EX_ctrl_update (fext:ext) s s' =
  if s'.ID.ID_EX_write_enable then
      s' with EX := s'.EX with EX_PC_sel := if s.EX.EX_opc = 9w then 1w
                                            else if s.EX.EX_opc = 10w then 2w
                                            else if s.EX.EX_opc = 11w then 3w
                                            else 0w
  else s'
End

(** forward data from MEM/WB -> EX **)
Definition EX_forward_data_def:
  EX_forward_data (fext:ext) s s' =
  let s' = s' with EX := s'.EX with EX_dataA_updated :=
           MUX_81 s'.EX.EX_ForwardA s'.EX.EX_dataA s'.WB.WB_write_data
                  s.MEM.MEM_ALU_res s.MEM.MEM_SHIFT_res
                  (s.MEM.MEM_PC + 4w) s'.MEM.MEM_imm_updated 0w 0w;
     s' = s' with EX := s'.EX with EX_dataB_updated :=
          MUX_81 s'.EX.EX_ForwardB s'.EX.EX_dataB s'.WB.WB_write_data
                 s.MEM.MEM_ALU_res s.MEM.MEM_SHIFT_res
                 (s.MEM.MEM_PC + 4w) s'.MEM.MEM_imm_updated 0w 0w in
    s' with EX := s'.EX with EX_dataW_updated :=
    MUX_81 s'.EX.EX_ForwardW s'.EX.EX_dataW s'.WB.WB_write_data
           s.MEM.MEM_ALU_res s.MEM.MEM_SHIFT_res
           (s.MEM.MEM_PC + 4w) s'.MEM.MEM_imm_updated 0w 0w
End

Theorem EX_forward_data_trans = REWRITE_RULE [MUX_81_def] EX_forward_data_def

(** set up inputs for ALU **)
Definition EX_ALU_input_update_def:
  EX_ALU_input_update (fext:ext) s s' =
  let s' = s' with EX := s'.EX with EX_ALU_input1 :=
           MUX_21 (s.EX.EX_opc = 9w) s'.EX.EX_dataA_updated s.EX.EX_PC in
    s' with EX := s'.EX with EX_ALU_input2 :=
    MUX_21 (s.EX.EX_opc = 9w) s'.EX.EX_dataB_updated s'.EX.EX_dataA_updated
End

Theorem EX_ALU_input_update_trans = REWRITE_RULE [MUX_21_def] EX_ALU_input_update_def

(** EX_compute_enable: aviod errors due to stalling **)
Definition EX_compute_enable_update_def:
  EX_compute_enable_update (fext:ext) s s' =
  s' with EX := s'.EX with EX_compute_enable := (s'.state = 0w /\
                                                ((s.MEM.MEM_opc <> 16w /\ s'.EX.EX_ForwardA <> 6w /\ s'.EX.EX_ForwardB <> 6w) \/ 
                                                (s.MEM.MEM_opc = 16w /\ (s'.EX.EX_ForwardA <> 0w \/ s'.EX.EX_ForwardB <> 0w))))
End

(** ALU **)
Definition EX_ALU_update_def:
  EX_ALU_update (fext:ext) (s:state_circuit) s' =
  let s' = s' with ALU_sum := (w2w s'.EX.EX_ALU_input1 + w2w s'.EX.EX_ALU_input2 +
                              (if s'.EX.EX_func = 1w then v2w [s'.EX.EX_carry_flag] else 0w));
      s' = s' with ALU_prod := (w2w s'.EX.EX_ALU_input1 * w2w s'.EX.EX_ALU_input2) in
  if s'.EX.EX_compute_enable then
    case s'.EX.EX_func of
      0w => (let s' = s' with EX := s'.EX with EX_overflow_flag :=
                      ((word_bit 31 s'.EX.EX_ALU_input1 = word_bit 31 s'.EX.EX_ALU_input2) /\
                       (word_bit 31 s'.ALU_sum <> word_bit 31 s'.EX.EX_ALU_input1));
                 s' = s' with EX := s'.EX with EX_carry_flag := word_bit 32 s'.ALU_sum in
               s' with EX := s'.EX with EX_ALU_res := (31 >< 0) s'.ALU_sum)
    | 1w => (let s' = s' with EX := s'.EX with EX_carry_flag := word_bit 32 s'.ALU_sum in
               s' with EX := s'.EX with EX_ALU_res := (31 >< 0) s'.ALU_sum)
    | 2w => (let s' = s' with ALU_sub := s'.EX.EX_ALU_input1 − s'.EX.EX_ALU_input2;
                 s' = s' with EX := s'.EX with EX_ALU_res := s'.ALU_sub in
               s' with EX := s'.EX with EX_overflow_flag :=
               ((word_bit 31 s'.EX.EX_ALU_input1 <> word_bit 31 s'.EX.EX_ALU_input2) /\
                (word_bit 31 s'.ALU_sub <> word_bit 31 s'.EX.EX_ALU_input1)))
    | 3w => s' with EX := s'.EX with EX_ALU_res := v2w [s'.EX.EX_carry_flag]
    | 4w => s' with EX := s'.EX with EX_ALU_res := v2w [s'.EX.EX_overflow_flag]
    | 5w => s' with EX := s'.EX with EX_ALU_res := s'.EX.EX_ALU_input1 + 1w
    | 6w => s' with EX := s'.EX with EX_ALU_res := s'.EX.EX_ALU_input1 - 1w
    | 7w => s' with EX := s'.EX with EX_ALU_res := (31 >< 0) s'.ALU_prod
    | 8w => s' with EX := s'.EX with EX_ALU_res := (63 >< 32) s'.ALU_prod
    | 9w => s' with EX := s'.EX with EX_ALU_res := (s'.EX.EX_ALU_input1 && s'.EX.EX_ALU_input2)
    | 10w => s' with EX := s'.EX with EX_ALU_res := (s'.EX.EX_ALU_input1 || s'.EX.EX_ALU_input2)
    | 11w => s' with EX := s'.EX with EX_ALU_res := (s'.EX.EX_ALU_input1 ?? s'.EX.EX_ALU_input2)
    | 12w => s' with EX := s'.EX with EX_ALU_res := v2w [s'.EX.EX_ALU_input1 = s'.EX.EX_ALU_input2]
    | 13w => s' with EX := s'.EX with EX_ALU_res := v2w [s'.EX.EX_ALU_input1 < s'.EX.EX_ALU_input2]
    | 14w => s' with EX := s'.EX with EX_ALU_res := v2w [s'.EX.EX_ALU_input1 <+ s'.EX.EX_ALU_input2]
    | 15w => s' with EX := s'.EX with EX_ALU_res := s'.EX.EX_ALU_input2
  else s'
End

(** SHIFT **)
Definition EX_SHIFT_update_def:
  EX_SHIFT_update (fext:ext) (s:state_circuit) s' =
  if s'.EX.EX_compute_enable then
    case ((1 >< 0) s'.EX.EX_func) of
      0w => s' with EX := s'.EX with EX_SHIFT_res := s'.EX.EX_dataA_updated <<~ s'.EX.EX_dataB_updated
    | 1w => s' with EX := s'.EX with EX_SHIFT_res := s'.EX.EX_dataA_updated >>>~ s'.EX.EX_dataB_updated
    | 2w => s' with EX := s'.EX with EX_SHIFT_res := s'.EX.EX_dataA_updated >>~ s'.EX.EX_dataB_updated
    | 3w => let s' = s' with shift_sh := word_mod s'.EX.EX_dataB_updated 32w in
              s' with EX := s'.EX with EX_SHIFT_res :=
              (s'.EX.EX_dataA_updated >>>~ s'.shift_sh) || (s'.EX.EX_dataA_updated <<~ (32w - s'.shift_sh))
  else s'
End

Triviality word_mod_32:
 !w. word_mod w (32w : word32) = w2w (((4 >< 0) w):word5)
Proof
 gen_tac >> CONV_TAC (LHS_CONV wordsLib.WORD_MOD_BITS_CONV) >> blastLib.BBLAST_TAC
QED

Theorem EX_SHIFT_update_trans = REWRITE_RULE [word_mod_32] EX_SHIFT_update_def

(** handling jumps **)
Definition EX_jump_sel_addr_update_def:
  EX_jump_sel_addr_update (fext:ext) s s' =
  if (s'.EX.EX_PC_sel = 1w) then
    let s' = s' with EX := s'.EX with EX_jump_sel := T in
      s' with EX := s'.EX with EX_jump_addr := s'.EX.EX_ALU_res
  else if ((s'.EX.EX_PC_sel = 2w) /\ (s'.EX.EX_ALU_res = 0w)) \/
          ((s'.EX.EX_PC_sel = 3w) /\ (s'.EX.EX_ALU_res <> 0w)) then
    let s' = s' with EX := s'.EX with EX_jump_sel := T in
      s' with EX := s'.EX with EX_jump_addr := s.EX.EX_PC + s'.EX.EX_dataW_updated
  else let s' = s' with EX := s'.EX with EX_jump_sel := F in
         s' with EX := s'.EX with EX_jump_addr := 0w
End

(** record data **)
Definition EX_data_rec_update_def:
  EX_data_rec_update (fext:ext) s s' =
  if s'.state = 0w /\ s.MEM.MEM_opc <> 16w then
    let s' = s' with EX := s'.EX with EX_dataA_rec := s'.EX.EX_dataA_updated;
        s' = s' with EX := s'.EX with EX_dataB_rec := s'.EX.EX_dataB_updated in
      s' with EX := s'.EX with EX_dataW_rec := s'.EX.EX_dataW_updated
  else if s'.state = 0w /\ s.MEM.MEM_opc = 16w then
    let s' = if s'.EX.EX_ForwardA <> 0w then
               s' with EX := s'.EX with EX_dataA_rec := s'.EX.EX_dataA_updated
             else s';
        s' = if s'.EX.EX_ForwardB <> 0w then
               s' with EX := s'.EX with EX_dataB_rec := s'.EX.EX_dataB_updated
             else s' in
      if s'.EX.EX_ForwardW <> 0w then
        s' with EX := s'.EX with EX_dataW_rec := s'.EX.EX_dataW_updated
      else s'
  else s'
End

(** Set up flags of MEM stage **)
Definition MEM_ctrl_update_def:
  MEM_ctrl_update (fext:ext) s s' =
  if s'.MEM.MEM_state_flag then
    let s' = s' with MEM := s'.MEM with MEM_read_mem := (s.MEM.MEM_opc = 4w \/ s.MEM.MEM_opc = 5w);
        s' = s' with MEM := s'.MEM with MEM_write_mem := (s.MEM.MEM_opc = 2w);
        s' = s' with MEM := s'.MEM with MEM_write_mem_byte := (s.MEM.MEM_opc = 3w);
        s' = s' with MEM := s'.MEM with MEM_isAcc := (s.MEM.MEM_opc = 8w) in
      s' with MEM := s'.MEM with MEM_isInterrupt := (s.MEM.MEM_opc = 12w)
  else s'
End

(** generate the value for the LoadUpperConstant instruction **)
Definition MEM_imm_update_def:
  MEM_imm_update (fext:ext) s s' =
  s' with MEM := s'.MEM with MEM_imm_updated := MUX_21 (s.MEM.MEM_opc = 14w) s'.MEM.MEM_imm
                                                ((8 >< 0) s'.MEM.MEM_imm @@ (22 >< 0) s'.MEM.MEM_dataW)
End

Theorem MEM_imm_update_trans = REWRITE_RULE [MUX_21_def] MEM_imm_update_def

(** update components for WB stage **)
Definition WB_update_def:
  WB_update fext s s' =
  let s' = s' with WB := s'.WB with WB_read_data := fext.data_rdata;
      s' = s' with WB := s'.WB with WB_read_data_byte := MUX_41 ((1 >< 0) s'.WB.WB_dataA)
                                                                (w2w ((7 >< 0) s'.WB.WB_read_data))
                                                                (w2w ((15 >< 8) s'.WB.WB_read_data))
                                                                (w2w ((23 >< 16) s'.WB.WB_read_data))
                                                                (w2w ((31 >< 24) s'.WB.WB_read_data));
      s' = (if s'.WB.WB_state_flag then
              let s' = s' with WB := s'.WB with WB_isOut := (s'.WB.WB_opc = 6w) in
                s' with WB := s'.WB with WB_data_sel :=
                if s'.WB.WB_opc = 0w \/ s'.WB.WB_opc = 6w then 0w
                else if s'.WB.WB_opc = 1w then 1w
                else if s'.WB.WB_opc = 7w then 2w
                else if s'.WB.WB_opc = 9w then 3w
                else if s'.WB.WB_opc = 13w \/ s'.WB.WB_opc = 14w then 4w
                else if s'.WB.WB_opc = 4w then 5w
                else if s'.WB.WB_opc = 5w then 6w
                else if s'.WB.WB_opc = 8w then 7w
                else 0w
            else s') in
     s' with WB := s'.WB with WB_write_data := MUX_81 s'.WB.WB_data_sel s'.WB.WB_ALU_res
                                                      s'.WB.WB_SHIFT_res (w2w fext.data_in)
                                                      (s'.WB.WB_PC + 4w) s'.WB.WB_imm
                                                      s'.WB.WB_read_data s'.WB.WB_read_data_byte
                                                      s.acc_res
End

Theorem WB_update_trans = REWRITE_RULE [MUX_41_def,MUX_81_def] WB_update_def

(** hazard handling **)
Definition Hazard_ctrl_def:
  Hazard_ctrl fext s s' =
  if s'.state = 1w \/ s'.state = 2w \/ s'.state = 3w \/ 
     s'.state = 5w \/ s'.state = 4w \/ s'.state = 6w then
    let s' = s' with IF := s'.IF with IF_PC_write_enable := F;
        s' = s' with ID := s'.ID with ID_ID_write_enable := F;
        s' = s' with ID := s'.ID with ID_flush_flag := F;
        s' = s' with ID := s'.ID with ID_EX_write_enable := F;
        s' = s' with EX := s'.EX with EX_NOP_flag := F;
        s' = s' with MEM := s'.MEM with MEM_state_flag := F;
        s' = s' with MEM := s'.MEM with MEM_NOP_flag := F in
    s' with WB := s'.WB with WB_state_flag := F
  else if ~fext.ready then
    let s' = s' with IF := s'.IF with IF_PC_write_enable := F;
        s' = s' with ID := s'.ID with ID_ID_write_enable := F;
        s' = s' with ID := s'.ID with ID_flush_flag := F;
        s' = s' with ID := s'.ID with ID_EX_write_enable := F;
        s' = s' with EX := s'.EX with EX_NOP_flag := F;
        s' = s' with MEM := s'.MEM with MEM_state_flag := F;
        s' = s' with MEM := s'.MEM with MEM_NOP_flag := F in
    s' with WB := s'.WB with WB_state_flag := F
  else if s.MEM.MEM_opc = 2w \/ s.MEM.MEM_opc = 3w \/ s.MEM.MEM_opc = 4w \/
          s.MEM.MEM_opc = 5w \/ s.MEM.MEM_opc = 8w \/ s.MEM.MEM_opc = 12w then
    let s' = s' with IF := s'.IF with IF_PC_write_enable := F;
        s' = s' with ID := s'.ID with ID_ID_write_enable := F;
        s' = s' with ID := s'.ID with ID_flush_flag := F;
        s' = s' with ID := s'.ID with ID_EX_write_enable := F;
        s' = s' with EX := s'.EX with EX_NOP_flag := F;
        s' = s' with MEM := s'.MEM with MEM_state_flag := T;
        s' = s' with MEM := s'.MEM with MEM_NOP_flag := T in
    s' with WB := s'.WB with WB_state_flag := T
  else if s'.EX.EX_jump_sel then
    let s' = s' with IF := s'.IF with IF_PC_write_enable := T;
        s' = s' with ID := s'.ID with ID_ID_write_enable := T;
        s' = s' with ID := s'.ID with ID_flush_flag := T;
        s' = s' with ID := s'.ID with ID_EX_write_enable := T;
        s' = s' with EX := s'.EX with EX_NOP_flag := T;
        s' = s' with MEM := s'.MEM with MEM_state_flag := T;
        s' = s' with MEM := s'.MEM with MEM_NOP_flag := F in
    s' with WB := s'.WB with WB_state_flag := T
  else
    let s' = s' with IF := s'.IF with IF_PC_write_enable := T;
        s' = s' with ID := s'.ID with ID_ID_write_enable := T;
        s' = s' with ID := s'.ID with ID_flush_flag := F;
        s' = s' with ID := s'.ID with ID_EX_write_enable := T;
        s' = s' with EX := s'.EX with EX_NOP_flag := F;
        s' = s' with MEM := s'.MEM with MEM_state_flag := T;
        s' = s' with MEM := s'.MEM with MEM_NOP_flag := F in
    s' with WB := s'.WB with WB_state_flag := T
End

(** data forwarding **)
Definition Forward_update_def:
  Forward_update EX_addr addr_disable check s s' : word3 =
  if EX_addr = s.MEM.MEM_addrW /\ s'.MEM.MEM_write_reg /\
     (s.MEM.MEM_opc = 4w \/ s.MEM.MEM_opc = 5w) /\ (~ addr_disable) /\ check then 6w
  else if EX_addr = s.MEM.MEM_addrW /\ s'.MEM.MEM_write_reg /\
     (s.MEM.MEM_opc = 13w \/ s.MEM.MEM_opc = 14w) /\ (~ addr_disable) /\ check then 5w
  else if EX_addr = s.MEM.MEM_addrW /\ s'.MEM.MEM_write_reg /\
          s.MEM.MEM_opc = 9w /\ (~ addr_disable) /\ check then 4w
  else if EX_addr = s.MEM.MEM_addrW /\ s'.MEM.MEM_write_reg /\
          s.MEM.MEM_opc = 1w /\ (~ addr_disable) /\ check then 3w
  else if EX_addr = s.MEM.MEM_addrW /\ s'.MEM.MEM_write_reg /\
          (s.MEM.MEM_opc = 0w \/ s.MEM.MEM_opc = 6w) /\ (~ addr_disable) /\ check then 2w
  else if EX_addr = s.WB.WB_addrW /\ s.WB.WB_write_reg /\ (~ addr_disable) /\ check then 1w
  else 0w
End

Definition ForwardA_def:
  ForwardA (fext:ext) s s' =
  let s' = s' with checkA :=
           (s.EX.EX_opc = 0w \/ s.EX.EX_opc = 1w \/ s.EX.EX_opc = 2w \/ s.EX.EX_opc = 3w \/
            s.EX.EX_opc = 4w \/ s.EX.EX_opc = 5w \/ s.EX.EX_opc = 6w \/ s.EX.EX_opc = 8w \/
            s.EX.EX_opc = 9w \/ s.EX.EX_opc = 10w \/ s.EX.EX_opc = 11w) in
    s' with EX := s'.EX with EX_ForwardA :=
    Forward_update s'.EX.EX_addrA s'.EX.EX_addrA_disable s'.checkA s s'
End

Theorem ForwardA_trans = REWRITE_RULE [Forward_update_def] ForwardA_def

Definition ForwardB_def:
  ForwardB (fext:ext) s s' =
  let s' = s' with checkB :=
           (s.EX.EX_opc = 0w \/ s.EX.EX_opc = 1w \/ s.EX.EX_opc = 2w \/ s.EX.EX_opc = 3w \/
            s.EX.EX_opc = 6w \/ s.EX.EX_opc = 10w \/ s.EX.EX_opc = 11w) in
    s' with EX := s'.EX with EX_ForwardB :=
    Forward_update s'.EX.EX_addrB s'.EX.EX_addrB_disable s'.checkB s s'
End

Theorem ForwardB_trans = REWRITE_RULE [Forward_update_def] ForwardB_def
                                       
Definition ForwardW_def:
  ForwardW (fext:ext) s s' =
  let s' = s' with checkW := (s.EX.EX_opc = 10w \/ s.EX.EX_opc = 11w \/ s.EX.EX_opc = 14w) in
    s' with EX := s'.EX with EX_ForwardW :=
    Forward_update s.EX.EX_addrW s'.EX.EX_addrW_disable s'.checkW s s'
End

Theorem ForwardW_trans = REWRITE_RULE [Forward_update_def] ForwardW_def


(* always_ff related: triggered by posedge clk *)
(** fetch: update PC **)
Definition IF_PC_update_def:
  IF_PC_update (fext:ext) (s:state_circuit) s' =
  if s'.IF.IF_PC_write_enable then
    s' with PC := s'.IF.IF_PC_input
  else s'
End

(** decode: IF -> ID **)
Definition ID_pipeline_def:
  ID_pipeline (fext:ext) s s' =
  if s'.ID.ID_ID_write_enable then
    let s' = s' with ID := s'.ID with ID_PC := s.PC in
    s' with ID := s'.ID with ID_instr := if s'.ID.ID_flush_flag then 0x0000003Fw else s'.IF.IF_instr
  else s'
End

(** register write **)
Definition REG_write_def:
  REG_write (fext:ext) s s' =
  if s.WB.WB_write_reg /\ s'.WB.WB_state_flag then
    s' with R := (s.WB.WB_addrW =+ s'.WB.WB_write_data) s'.R
  else s'
End

(** execute: ID -> EX **)
Definition EX_pipeline_def:
  EX_pipeline (fext:ext) s s' =
  if s'.ID.ID_EX_write_enable then
    let s' = s' with EX := s'.EX with EX_PC := s.ID.ID_PC;
        s' = s' with EX := s'.EX with EX_dataA := s'.ID.ID_dataA;
        s' = s' with EX := s'.EX with EX_dataB := s'.ID.ID_dataB;
        s' = s' with EX := s'.EX with EX_dataW := s'.ID.ID_dataW;
        s' = s' with EX := s'.EX with EX_imm := s'.ID.ID_imm;
        s' = s' with EX := s'.EX with EX_addrA_disable := s'.ID.ID_addrA_disable;
        s' = s' with EX := s'.EX with EX_addrB_disable := s'.ID.ID_addrB_disable;
        s' = s' with EX := s'.EX with EX_addrW_disable := s'.ID.ID_addrW_disable;
        s' = s' with EX := s'.EX with EX_addrA := s'.ID.ID_addrA;
        s' = s' with EX := s'.EX with EX_addrB := s'.ID.ID_addrB;
        s' = s' with EX := s'.EX with EX_addrW := s'.ID.ID_addrW;
        s' = s' with EX := s'.EX with EX_opc := if s'.EX.EX_NOP_flag then 15w else s'.ID.ID_opc in
      s' with EX := s'.EX with EX_func := if s'.EX.EX_NOP_flag then 9w else s'.ID.ID_func
  else
    s'
End

(** memory: EX -> MEM **)
Definition MEM_pipeline_def:
  MEM_pipeline (fext:ext) s s' =
  if s'.MEM.MEM_state_flag then
    let s' = s' with MEM := s'.MEM with MEM_PC := s.EX.EX_PC;
        s' = s' with MEM := s'.MEM with MEM_dataA := s'.EX.EX_dataA_rec;
        s' = s' with MEM := s'.MEM with MEM_dataB := s'.EX.EX_dataB_rec;
        s' = s' with MEM := s'.MEM with MEM_dataW := s'.EX.EX_dataW_rec;
        s' = s' with MEM := s'.MEM with MEM_imm := s.EX.EX_imm;
        s' = s' with MEM := s'.MEM with MEM_ALU_res := s'.EX.EX_ALU_res;
        s' = s' with MEM := s'.MEM with MEM_SHIFT_res := s'.EX.EX_SHIFT_res;
        s' = s' with MEM := s'.MEM with MEM_addrW := s.EX.EX_addrW;
        s' = s' with MEM := s'.MEM with MEM_opc := if s'.MEM.MEM_NOP_flag then 16w else s.EX.EX_opc in
      s' with MEM := s'.MEM with MEM_write_reg := ((s.EX.EX_opc = 0w) \/ (s.EX.EX_opc = 1w) \/ (s.EX.EX_opc = 4w) \/
                                                   (s.EX.EX_opc = 5w) \/ (s.EX.EX_opc = 6w) \/ (s.EX.EX_opc = 7w) \/
                                                   (s.EX.EX_opc = 8w) \/ (s.EX.EX_opc = 9w) \/ (s.EX.EX_opc = 13w) \/
                                                   (s.EX.EX_opc = 14w))
  else s'
End

(** write back: MEM -> WB **)
Definition WB_pipeline_def:
  WB_pipeline (fext:ext) s s' =
  if s'.WB.WB_state_flag then
    let s' = s' with WB := s'.WB with WB_PC := s.MEM.MEM_PC;
        s' = s' with WB := s'.WB with WB_dataA := s.MEM.MEM_dataA;
        s' = s' with WB := s'.WB with WB_imm := s'.MEM.MEM_imm_updated;
        s' = s' with WB := s'.WB with WB_ALU_res := s.MEM.MEM_ALU_res;
        s' = s' with WB := s'.WB with WB_SHIFT_res := s.MEM.MEM_SHIFT_res;
        s' = s' with WB := s'.WB with WB_write_reg :=
             ((s.MEM.MEM_opc = 0w) \/ (s.MEM.MEM_opc = 1w) \/ (s.MEM.MEM_opc = 4w) \/
             (s.MEM.MEM_opc = 5w) \/ (s.MEM.MEM_opc = 6w) \/ (s.MEM.MEM_opc = 7w) \/
             (s.MEM.MEM_opc = 8w) \/ (s.MEM.MEM_opc = 9w) \/ (s.MEM.MEM_opc = 13w) \/
             (s.MEM.MEM_opc = 14w));
        s' = s' with WB := s'.WB with WB_addrW := s.MEM.MEM_addrW in
      s' with WB := s'.WB with WB_opc := s.MEM.MEM_opc
  else s'
End

(** state **)
Definition agp32_next_state_def:
  agp32_next_state fext s s' =
  if fext.error = 0w then
    case s'.state of
      0w => (let s' = s' with data_out := if s'.WB.WB_isOut then (9 >< 0) s'.WB.WB_ALU_res
                                          else s.data_out in
              if ~fext.ready then s' with state := 1w
              else if s'.MEM.MEM_isInterrupt then
                let s' = s' with state := 1w;
                    s' = s' with command := 4w;
                    s' = s' with do_interrupt := T in
                  s' with data_addr := 0w                            
              else if s'.MEM.MEM_read_mem then
                let s' = s' with state := 1w;
                    s' = s' with command := 2w in
                  s' with data_addr := s.MEM.MEM_dataA
              else if s'.MEM.MEM_write_mem then
                let s' = s' with state := 1w;
                    s' = s' with command := 3w;
                    s' = s' with data_addr := s.MEM.MEM_dataB;
                    s' = s' with data_wdata := s.MEM.MEM_dataA in
                  s' with data_wstrb := 15w
              else if s'.MEM.MEM_write_mem_byte then
                let s' = s' with state := 1w;
                    s' = s' with command := 3w;
                    s' = s' with data_addr := s.MEM.MEM_dataB;
                    s' = s' with data_wstrb := 1w <<~ w2w ((1 >< 0) s.MEM.MEM_dataB) in
               case (1 >< 0) s.MEM.MEM_dataB of
                 0w => s' with data_wdata := bit_field_insert 7 0 ((7 >< 0) s.MEM.MEM_dataA) s'.data_wdata
               | 1w => s' with data_wdata := bit_field_insert 15 8 ((7 >< 0) s.MEM.MEM_dataA) s'.data_wdata
               | 2w => s' with data_wdata := bit_field_insert 23 16 ((7 >< 0) s.MEM.MEM_dataA) s'.data_wdata
               | 3w => s' with data_wdata := bit_field_insert 31 24 ((7 >< 0) s.MEM.MEM_dataA) s'.data_wdata
              else if s'.MEM.MEM_isAcc then
                let s' = s' with state := 2w;
                    s' = s' with command := 1w;
                    s' = s' with acc_arg := s.MEM.MEM_dataA in
                  s' with acc_arg_ready := T
              else s' with command := 1w)
    | 1w => (let s' = if fext.ready /\ s.command = 0w then
                        if s'.do_interrupt then let
                          s' = s' with state := 4w;
                          s' = s' with do_interrupt := F;
                          s' = s' with interrupt_req := T in
                         s'
                        else
                         s' with state := 6w
                      else s' in
               s' with command := 0w)
    | 2w => (let s' = if s.acc_res_ready /\ ~s.acc_arg_ready then s' with state := 6w
                      else s';
                 s' = s' with acc_arg_ready := F in
               s' with command := 0w)
    | 3w => if fext.mem_start_ready then
              let s' = s' with state := 1w in
                s' with command := 1w
            else s'
    | 4w => if fext.interrupt_ack then
               let s' = s' with state := 6w in
                 s' with interrupt_req := F
            else s'
    | 6w => let s' = s' with state := 0w in
              s' with command := 1w
    | _ => s'                      
  else
    s' with state := 5w
End

(** accelerator: integer addition **)
Definition Acc_compute_def:
  Acc_compute (fext:ext) s s' =
  if s.acc_arg_ready then
    let s' = s' with acc_res_ready := F in
      s' with acc_state := 0w
  else
    case s'.acc_state of
      0w => s' with acc_state := 1w
    | 1w => let s' = s' with acc_res := w2w ((31 >< 16) s.acc_arg + (15 >< 0) s.acc_arg) in
              s' with acc_res_ready := T
    | _ => s'
End


(* processor *)
(** initialize some items **)
val init_tm = add_x_inits ``<| R := K 0w;
                               PC := 0w;
                               state := 3w;     
                               acc_arg_ready := F;
                               command := 0w;
                               data_addr := 0xffffffffw;         
                               do_interrupt := F;           
                               interrupt_req := F;           
                               IF := <| IF_PC_write_enable := F |>;           
                               ID := <| ID_instr := 0x0000003Fw |>;
                               EX := <| EX_PC_sel := 0w; EX_opc := 15w |>;
                               MEM := <| MEM_write_reg := F; MEM_opc := 15w |>;
                               WB := <| WB_write_reg := F |> |>``;

Definition agp32_init_def:
  agp32_init fbits = ^init_tm
End

(** pipelined Silver **)
Definition agp32_def:
  agp32 = mk_module (procs [agp32_next_state; WB_pipeline; MEM_pipeline;
                            EX_pipeline; REG_write; ID_pipeline; IF_PC_update; Acc_compute])
                    (procs [ForwardA; ForwardB; ForwardW;
                            IF_instr_update;ID_opc_func_update; ID_imm_update; ID_data_update;
                            EX_ctrl_update; EX_forward_data; EX_ALU_input_update;
                            EX_compute_enable_update; EX_ALU_update; EX_SHIFT_update; 
                            EX_jump_sel_addr_update; EX_data_rec_update; IF_PC_input_update;
                            MEM_ctrl_update; MEM_imm_update; WB_update; Hazard_ctrl])
                    agp32_init
End

val _ = export_theory ();
