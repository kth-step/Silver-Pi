open hardwarePreamble translatorTheory translatorCoreLib agp32StateTheory agp32EnvironmentTheory;

val _ = new_theory "agp32Processor";

val _ = prefer_num ();
val _ = guess_lengths ();

(* Pipelined Silver processor implementation *)

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
(** compute PC **)
Definition IF_PC_sel_update_def:
  IF_PC_sel_update (fext:ext) (s:state_circuit) s' =
  if (s'.EX.EX_PC_sel = 1w) \/ ((s'.EX.EX_PC_sel = 2w) /\ (s'.EX.EX_ALU_res = 0w)) \/
     ((s'.EX.EX_PC_sel = 3w) /\ (s'.EX.EX_ALU_res <> 0w)) then
    s' with IF := s'.IF with PC_sel := s'.EX.EX_PC_sel
  else s' with IF := s'.IF with PC_sel := 0w  
End
   
Definition IF_PC_input_update_def:
  IF_PC_input_update (fext:ext) s s' =
  s' with IF := s'.IF with
                  IF_PC_input := MUX_41 s'.IF.PC_sel (s.IF.IF_PC_output + 4w) s'.EX.EX_ALU_res
                                        (s'.EX.EX_PC + s'.EX.EX_dataW_updated)
                                        (s'.EX.EX_PC + s'.EX.EX_dataW_updated)
End

Theorem IF_PC_input_update_trans = REWRITE_RULE [MUX_41_def] IF_PC_input_update_def

(** get register address from instr **)
Definition ID_addr_update_def:
  ID_addr_update (fext:ext) (s:state_circuit) s' =
  s' with ID := s'.ID with <| ID_addrA := (22 >< 17) s'.ID.ID_instr;
                              ID_addrB := (15 >< 10) s'.ID.ID_instr;
                              ID_addrW := (30 >< 25) s'.ID.ID_instr;
                              ID_addrA_enable := word_bit 23 s'.ID.ID_instr;
                              ID_addrB_enable := word_bit 16 s'.ID.ID_instr;
                              ID_addrB_enable := word_bit 31 s'.ID.ID_instr
                           |>
End

(** decode instr **)
Definition ID_opc_update_def:
  ID_opc_update (fext:ext) (s:state_circuit) s' =
  if word_bit 24 s'.ID.ID_instr then
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
    s' with ID := s'.ID with ID_opc := 15w
End

Definition ID_func_update_def:
  ID_func_update (fext:ext) (s:state_circuit) s' =
  if s'.ID.ID_opc = 0w \/ s'.ID.ID_opc = 1w \/ s'.ID.ID_opc = 6w \/
     s'.ID.ID_opc = 9w \/ s'.ID.ID_opc = 10w \/ s'.ID.ID_opc = 11w then
    s' with ID := s'.ID with ID_func := (9 >< 6) s'.ID.ID_instr
  else
    s' with ID := s'.ID with ID_func := 9w
End

(** register read **)
Definition REG_read_def:
  REG_read (fext:ext) (s:state_circuit) s' =
  s' with ID := s'.ID with <| ID_read_dataA := s'.R s'.ID.ID_addrA;
                              ID_read_dataB := s'.R s'.ID.ID_addrB;
                              ID_read_dataW := s'.R s'.ID.ID_addrW 
                           |>
End

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

Definition ID_imm_reg_update_def:
  ID_imm_reg_update (fext:ext) (s:state_circuit) s' =
  s' with ID := s'.ID with <| ID_immA := sw2sw ((22 >< 17) s'.ID.ID_instr);
                              ID_immB := sw2sw ((15 >< 10) s'.ID.ID_instr);
                              ID_immW := sw2sw ((30 >< 25) s'.ID.ID_instr)       
                           |>
End

(** update the value from reg in case the addr is written by the WB stage **)
Definition ID_foward_update_def:
  ID_forward_update (fext:ext) (s:state_circuit) s' =
  s' with ID := s'.ID with <| ID_ForwardA := if s'.ID.ID_addrA = s'.WB.WB_addrW /\
                                                s'.WB.WB_write_reg /\ s'.WB.WB_state_flag then T
                                             else F;
                              ID_ForwardB := if s'.ID.ID_addrB = s'.WB.WB_addrW /\
                                                s'.WB.WB_write_reg /\ s'.WB.WB_state_flag then T
                                             else F;
                              ID_ForwardW := if s'.ID.ID_addrW = s'.WB.WB_addrW /\
                                                s'.WB.WB_write_reg /\ s'.WB.WB_state_flag then T
                                             else F
                           |>
End
    
Definition ID_read_data_update_def:
  ID_read_data_update (fext:ext) (s:state_circuit) s' =
  s' with ID := s'.ID with <| ID_read_dataA_updated :=
                              MUX_21 s'.ID.ID_ForwardA s'.ID.ID_read_dataA s'.WB.WB_write_data;
                              ID_read_dataB_updated :=
                              MUX_21 s'.ID.ID_ForwardB s'.ID.ID_read_dataB s'.WB.WB_write_data;
                              ID_read_dataW_updated :=
                              MUX_21 s'.ID.ID_ForwardW s'.ID.ID_read_dataW s'.WB.WB_write_data
                           |>
End

Theorem ID_read_data_update_trans = REWRITE_RULE [MUX_21_def] ID_read_data_update_def

(** update the data from read_data and imm for A/B/W **)
Definition ID_data_update_def:
  ID_data_update (fext:ext) (s:state_circuit) s' =
  s' with ID := s'.ID with <| ID_dataA := MUX_21 (word_bit 23 s'.ID.ID_instr)
                                                 s'.ID.ID_read_dataA_updated s'.ID.ID_immA;
                              ID_dataB := MUX_21 (word_bit 16 s'.ID.ID_instr)
                                                 s'.ID.ID_read_dataB_updated s'.ID.ID_immB;
                              ID_dataW := MUX_21 (word_bit 31 s'.ID.ID_instr)
                                                 s'.ID.ID_read_dataW_updated s'.ID.ID_immW
                           |>
End

Theorem ID_data_update_trans = REWRITE_RULE [MUX_21_def] ID_data_update_def

(** Set up some flags of EX stage **)
Definition EX_ctrl_update_def:
  EX_ctrl_update (fext:ext) (s:state_circuit) s' =
  if s'.ID.ID_EX_write_enable then
    s' with EX := s'.EX with EX_isAcc := (s'.EX.EX_opc = 8w)
  else s'
End

(* Forward data from MEM/WB -> EX *)
Definition EX_forward_data_def:
  EX_forward_data (fext:ext) (s:state_circuit) s' =
  s' with EX := s'.EX with <| EX_dataA_updated :=
                              MUX_81 s'.EX.EX_ForwardA s'.EX.EX_dataA s'.WB.WB_write_data
                                     s'.MEM.MEM_ALU_res s'.MEM.MEM_SHIFT_res
                                     (s'.MEM.MEM_PC + 4w) s'.MEM.MEM_imm_updated 0w 0w;
                              EX_dataB_updated :=
                              MUX_81 s'.EX.EX_ForwardB s'.EX.EX_dataB s'.WB.WB_write_data
                                     s'.MEM.MEM_ALU_res s'.MEM.MEM_SHIFT_res
                                     (s'.MEM.MEM_PC + 4w) s'.MEM.MEM_imm_updated 0w 0w;
                              EX_dataW_updated :=
                              MUX_81 s'.EX.EX_ForwardW s'.EX.EX_dataW s'.WB.WB_write_data
                                     s'.MEM.MEM_ALU_res s'.MEM.MEM_SHIFT_res
                                     (s'.MEM.MEM_PC + 4w) s'.MEM.MEM_imm_updated 0w 0w
                           |>                  
End

Theorem EX_forward_data_trans = REWRITE_RULE [MUX_81_def] EX_forward_data_def

(** set up inputs for ALU **)
Definition EX_ALU_input_update_def:
  EX_ALU_input_update (fext:ext) (s:state_circuit) s' =
  s' with EX := s'.EX with <| EX_ALU_input1 :=
                              MUX_21 (s'.EX.EX_opc = 9w) s'.EX.EX_dataA_updated s'.EX.EX_PC;
                              EX_ALU_input2 :=
                              MUX_21 (s'.EX.EX_opc = 9w) s'.EX.EX_dataB_updated s'.EX.EX_dataA_updated;
                           |>
End

Theorem EX_ALU_input_update_trans = REWRITE_RULE [MUX_21_def] EX_ALU_input_update_def

(** EX_compute_enable: aviod errors due to stalling **)
Definition EX_compute_enable_update_def:
  EX_compute_enable_update (fext:ext) (s:state_circuit) s' =
  s' with EX := s'.EX with EX_compute_enable := (s'.state = 0w /\
                                                (s'.MEM.MEM_opc <> 16w \/ s'.MEM.MEM_opc = 16w /\
                                                (s'.EX.EX_ForwardA <> 0w \/ s'.EX.EX_ForwardB <> 0w)))
End

(** ALU **)
Definition ALU_def:
  ALU (func:word4) input1 input2 s =
  let ALU_sum = (w2w input1 + w2w input1 +
                 (if func = 1w then v2w [s.EX.EX_carry_flag] else 0w)) : 33 word;
      ALU_prod = (w2w input1 * w2w input2) : word64 in
    case func of
      0w => s with EX := s.EX with <| EX_overflow_flag := ((word_bit 31 input1 = word_bit 31 input2) /\
                                                           (word_bit 31 ALU_sum <> word_bit 31 input1));
                                      EX_carry_flag := word_bit 32 ALU_sum;
                                      EX_ALU_res := (31 >< 0) ALU_sum
                                   |>
    | 1w => s with EX := s.EX with <| EX_carry_flag := word_bit 32 ALU_sum;
                                      EX_ALU_res := (31 >< 0) ALU_sum
                                   |>
                                      
    | 2w => let ALU_sub = input1 − input2 in
              s with EX := s.EX with <| EX_ALU_res := ALU_sub;
                                        EX_overflow_flag := ((word_bit 31 input1 <> word_bit 31 input2) /\
                                                             (word_bit 31 ALU_sub <> word_bit 31 input1))
                                     |>
    | 3w => s with EX := s.EX with EX_ALU_res := v2w [s.EX.EX_carry_flag]
    | 4w => s with EX := s.EX with EX_ALU_res := v2w [s.EX.EX_overflow_flag]
    | 5w => s with EX := s.EX with EX_ALU_res := input1 + 1w
    | 6w => s with EX := s.EX with EX_ALU_res := input1 - 1w
    | 7w => s with EX := s.EX with EX_ALU_res := (31 >< 0) ALU_prod
    | 8w => s with EX := s.EX with EX_ALU_res := (63 >< 32) ALU_prod
    | 9w => s with EX := s.EX with EX_ALU_res := (input1 && input2)
    | 10w => s with EX := s.EX with EX_ALU_res := (input1 || input2)
    | 11w => s with EX := s.EX with EX_ALU_res := (input1 ⊕ input2)
    | 12w => s with EX := s.EX with EX_ALU_res := v2w [input1 = input2]
    | 13w => s with EX := s.EX with EX_ALU_res := v2w [input1 < input2]
    | 14w => s with EX := s.EX with EX_ALU_res := v2w [input1 <+ input2]
    | 15w => s with EX := s.EX with EX_ALU_res := input2
End

Definition EX_ALU_update_def:
  EX_ALU_update (fext:ext) (s:state_circuit) s' =
  if s'.EX.EX_compute_enable then
    ALU s'.EX.EX_func s'.EX.EX_ALU_input1 s'.EX.EX_ALU_input2 s'
  else s'
End

Theorem EX_ALU_update_trans = REWRITE_RULE [ALU_def] EX_ALU_update_def

(** SHIFT **)
Definition SHIFT_def:
  SHIFT (func:word2) inputa inputb s =
  case func of
     0w => s with EX := s.EX with EX_SHIFT_res := inputa <<~ inputb
   | 1w => s with EX := s.EX with EX_SHIFT_res := inputa >>>~ inputb
   | 2w => s with EX := s.EX with EX_SHIFT_res := inputa >>~ inputb
   | 3w => let shift_sh = word_mod inputb 32w in
             s with EX := s.EX with EX_SHIFT_res := (inputa >>>~ shift_sh) || (inputa <<~ (32w - shift_sh))
End

Definition EX_SHIFT_update_def:
  EX_SHIFT_update (fext:ext) (s:state_circuit) s' =
  if s'.EX.EX_compute_enable then
    SHIFT ((1 >< 0) s'.EX.EX_func) s'.EX.EX_dataA_updated s'.EX.EX_dataB_updated s'
  else s'
End

Theorem EX_SHIFT_update_trans = REWRITE_RULE [SHIFT_def] EX_SHIFT_update_def


(* always_ff related: triggered by posedge clk *)
(** Fetch: update PC **)
Definition IF_PC_output_update_def:
  IF_PC_output_update (fext:ext) s s' =
  if s'.IF.IF_PC_write_enable then
    s' with IF := s'.IF with IF_PC_output := s.IF.IF_PC_input
  else s'
End

(** Decode: IF -> ID **)
Definition ID_pipeline_def:
  ID_pipeline (fext:ext) s s' =
  if s'.ID.ID_ID_write_enable then
    s' with ID := s'.ID with <| ID_PC := s.IF.IF_PC_output; ID_instr := s.IF.IF_instr |>
  else if s'.ID.ID_flush_flag then
    s' with ID := s'.ID with ID_instr := 0x0000003Fw
  else s'
End

(** register write **)
Definition REG_write_def:
  REG_write (fext:ext) (s:state_circuit) s' =
  if s'.WB.WB_write_reg /\ s'.WB.WB_state_flag then
    s' with R := (s'.WB.WB_addrW =+ s'.WB.WB_write_data) s'.R
  else s'
End

(** Execute: ID -> EX **)
Definition EX_pipeline_def:
  EX_pipeline (fext:ext) (s:state_circuit) s' =
  if s'.ID.ID_EX_write_enable then
    s' with EX := s'.EX with <| EX_PC := s'.ID.ID_PC; EX_dataA := s'.ID.ID_dataA;
                                EX_dataB := s'.ID.ID_dataB; EX_dataW := s'.ID.ID_dataW;
                                EX_imm := s'.ID.ID_imm; EX_write_enable := s'.ID.ID_EX_write_enable;
                                EX_addrA_enable := s'.ID.ID_addrA_enable;
                                EX_addrB_enable := s'.ID.ID_addrB_enable;
                                EX_addrW_enable := s'.ID.ID_addrW_enable;
                                EX_addrA := s'.ID.ID_addrA; EX_addrB := s'.ID.ID_addrB;
                                EX_addrW := s'.ID.ID_addrW; EX_opc := s'.ID.ID_opc;
                                EX_func := s'.ID.ID_func;
                                EX_PC_sel := if s'.ID.ID_opc = 9w then 1w
                                             else if s'.ID.ID_opc = 10w then 2w
                                             else if s'.ID.ID_opc = 11w then 3w
                                             else 0w
                             |>
  else if s'.EX.EX_NOP_flag then
    s' with EX := s'.EX with <| EX_write_enable := s'.ID.ID_EX_write_enable; EX_opc := 16w |>
  else
    s' with EX := s'.EX with EX_write_enable := s'.ID.ID_EX_write_enable
End

(* processor *)
val init_tm = add_x_inits “<|PC := 0w;
                             R := K 0w;
                             state := 3w;
                             acc_arg_ready := F;
                             command := 0w;
                             do_interrupt := F;
                             interrupt_req := F;
                             IF := <| IF_PC_output := 0w |>;
                             ID := <| ID_instr := 0x0000003Fw; ID_ForwardA := F;
                                      ID_ForwardB := F; ID_ForwardW := F |>;
                             EX := <| EX_PC := 0w |>;
                             MEM := <| MEM_PC := 0w |>;
                             WB := <| WB_PC := 0w |> |>”;

Definition agp32_init_def:
  agp32_init fbits = ^init_tm
End

Definition agp32_def:
  agp32 = mk_module (procs [IF_PC_output_update; ID_pipeline; REG_write; EX_pipeline])
                    (procs [IF_PC_sel_update; IF_PC_input_update; ID_addr_update;
                            ID_opc_update; ID_func_update; REG_read; ID_imm_update;
                            ID_imm_reg_update; ID_forward_update; ID_read_data_update;
                            ID_data_update; EX_ctrl_update; EX_forward_data;
                            EX_ALU_input_update; EX_compute_enable_update;
                            EX_ALU_update; EX_SHIFT_update])
                    agp32_init
End

val _ = export_theory ();
