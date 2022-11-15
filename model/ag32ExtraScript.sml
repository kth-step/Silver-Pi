open hardwarePreamble agp32EnvironmentTheory ag32Theory;

val _ = new_theory "ag32Extra";

(* extra definitions based on the Silver ISA for the equvialence of invisible registers/singals *)

val _ = prefer_num ();
val _ = guess_lengths ();

(* current instruction processed by Silver ISA *)
Definition instr_def:
  instr (a:ag32_state) = word_at_addr a.MEM (align_addr a.PC)
End

(* decode the opc, func and data ports based on the instr *)
Definition opc_def:
  opc a :word6 =
  let i = instr a in
    if word_bit 24 i then
      if word_bit 31 i then 13w
      else if (23 >< 9) i = 0w then 14w
      else 15w
    else if (5 >< 0) i = 10w \/ (5 >< 0) i = 11w \/ (5 >< 0) i = 12w then
      (5 >< 0) i
    else if word_bit 31 i then 15w
    else if (5 >< 0) i <+ 10w then
      (5 >< 0) i
    else 15w
End

Definition func_def:
  func a :word4 =
  let opc = opc a in
    if opc = 0w \/ opc = 6w \/ opc = 9w \/ opc = 10w \/ opc = 11w then
      (9 >< 6) (instr a)
    else if opc = 1w then
      (3w:word2) @@ ((7 >< 6) (instr a))
    else 9w
End

Definition addrA_def:
  addrA a = (22 >< 17) (instr a)
End

Definition addrB_def:
  addrB a = (15 >< 10) (instr a)
End

Definition addrW_def:
  addrW a = (30 >< 25) (instr a)
End

Definition flagA_def:
  flagA a = word_bit 23 (instr a)
End

Definition flagB_def:
  flagB a = word_bit 16 (instr a)
End

Definition flagW_def:
  flagW a = word_bit 31 (instr a)
End

(* generate the correct data for A/B/W ports *)
Definition reg_dataA_def:
  reg_dataA a = a.R (addrA a)
End

Definition reg_dataB_def:
  reg_dataB a = a.R (addrB a)
End

Definition reg_dataW_def:
  reg_dataW a = a.R (addrW a)
End

Definition immA_def:
  immA a :word32 = sw2sw ((22 >< 17) (instr a))
End

Definition immB_def:
  immB a :word32 = sw2sw ((15 >< 10) (instr a))
End

Definition immW_def:
  immW a :word32 = sw2sw ((30 >< 25) (instr a))
End

Definition dataA_def:
  dataA a = ri2word (DecodeReg_imm (v2w [word_bit 23 (word_at_addr a.MEM (align_addr a.PC))],(22 >< 17) (word_at_addr a.MEM (align_addr a.PC)))) a
End

Definition dataB_def:
  dataB a = ri2word (DecodeReg_imm (v2w [word_bit 16 (word_at_addr a.MEM (align_addr a.PC))],(15 >< 10) (word_at_addr a.MEM (align_addr a.PC)))) a
End

Definition dataW_def:
  dataW a = ri2word (DecodeReg_imm (v2w [word_bit 31 (word_at_addr a.MEM (align_addr a.PC))],(30 >< 25) (word_at_addr a.MEM (align_addr a.PC)))) a
End

(* immediate *)
Definition imm_def:
  imm a :word32 =
  let i = instr a in
    if (word_bit 31 i) /\ (word_bit 24 i) then
      if (word_bit 23 i) then 0w - w2w ((22 >< 0) i)
      else w2w ((22 >< 0) i)
    else if (word_bit 24 i) /\ ((23 >< 9) i = 0w) then
      w2w ((8 >< 0) i)
    else 0w
End

(* compute the ALU result *)
Definition ALU_input1_def:
  ALU_input1 a =
  let opc = opc a in
    if opc = 9w then a.PC else dataA a
End

Definition ALU_input2_def:
  ALU_input2 a =
  let opc = opc a in
    if opc = 9w then dataA a else dataB a
End

Definition ALU_res_def:
  ALU_res a =
  let opc = opc a;
      func = func a;
      input1 = ALU_input1 a;
      input2 = ALU_input2 a;
      (v,a') = ALU (num2funcT (w2n func), input1, input2) a in
    v
End

(* compute the shift result *)
Definition shift_res_def:
  shift_res a =
  let instr = instr a;
      shiftOp = num2shiftT (w2n ((7 >< 6) instr)) in
    shift (shiftOp, dataA a, dataB a)
End

(* singals related to the accelerator *)
Definition acc_arg_def:
  acc_arg a = dataA a
End

Definition acc_res_def:
  acc_res a = accelerator_f (acc_arg a)
End

Definition isAcc_isa_def:
  isAcc_isa a = (opc a = 8w)
End

Definition isinterrupt_def:
  isinterrupt a = (opc a = 12w)
End

(* singals related to memory operations *)
Definition mem_isread_def:
  mem_isread a = (opc a = 4w \/ opc a = 5w)
End

Definition is_wrMEM_isa_def:
  is_wrMEM_isa a = (opc a = 2w \/ opc a = 3w)
End

Definition isMEM_stg_op_isa_def:
  isMEM_stg_op_isa a = (opc a = 2w \/ opc a = 3w \/ opc a = 4w \/ opc a = 5w \/ opc a = 8w \/ opc a = 12w)
End

Definition mem_iswrite_def:
  mem_iswrite a = (opc a = 2w)
End

Definition mem_iswrite_byte_def:
  mem_iswrite_byte a = (opc a = 3w)
End

Definition mem_data_addr_def:
  mem_data_addr a =
  let opc = opc a;
      dataA = dataA a;
      dataB = dataB a in
    if opc = 2w then align_addr dataB
    else if opc = 3w then dataB
    else if opc = 4w then align_addr dataA
    else if opc = 5w then dataA
    else 0w
End

Definition mem_data_wstrb_def:
  mem_data_wstrb a :word4 =
  let opc = opc a;
      dataB = dataB a in
    if opc = 2w then 15w
    else if opc = 3w then 1w <<~ w2w ((1 >< 0) dataB)
    else 0w     
End

Definition mem_data_wdata_def:
  mem_data_wdata a =
  let opc = opc a;
      dataA = dataA a in
    if opc = 2w then dataA
    else if opc = 3w then w2w ((7 >< 0) dataA)
    else 0w
End

Definition mem_data_rdata_def:
  mem_data_rdata a =
  let opc = opc a;
      mem_data_addr = mem_data_addr a in
    if opc = 4w then word_at_addr a.MEM mem_data_addr
    else if opc = 5w then w2w (a.MEM mem_data_addr)
    else 0w
End

(* singals related to update Silver register R *)
Definition reg_iswrite_def:
  reg_iswrite a =
  let opc = opc a in
    (opc = 0w) \/ (opc = 1w) \/ (opc = 4w) \/ (opc = 5w) \/ (opc = 6w) \/
    (opc = 7w) \/ (opc = 8w) \/ (opc = 9w) \/ (opc = 13w) \/ (opc = 14w)
End

Definition reg_wdata_sel_def:
  reg_wdata_sel a =
  let opc = opc a in
    if (opc = 0w) \/ (opc = 6w) then 0w
    else if opc = 1w  then 1w
    else if (opc = 4w) \/ (opc = 5w) then 2w
    else if opc = 7w then 3w
    else if opc = 8w then 4w
    else if opc = 9w then 5w
    else if opc = 13w then 6w
    else if opc = 14w then 7w
    else 0w
End

Definition reg_wdata_def:
  reg_wdata a =
  let opc = opc a in
    if (opc = 0w) \/ (opc = 6w) then ALU_res a
    else if opc = 1w  then shift_res a
    else if (opc = 4w) \/ (opc = 5w) then mem_data_rdata a
    else if opc = 7w then w2w a.data_in
    else if opc = 8w then acc_res a
    else if opc = 9w then a.PC + 4w
    else if opc = 13w then imm a
    else if opc = 14w then ((8 >< 0) (imm a)) @@ ((22 >< 0) (dataW a))
    else 0w
End

(* detect if a jump is happening in the ISA machine *)
Definition isJump_isa_def:
  isJump_isa a =
  let opc = opc a;
      ALU_res = ALU_res a in
  ((opc = 9w) \/ (opc = 10w /\ ALU_res = 0w) \/ (opc = 11w /\ ALU_res <> 0w))
End

val _ = export_theory ();
