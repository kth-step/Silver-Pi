open hardwarePreamble agp32EnvironmentTheory ag32Theory;

val _ = new_theory "ag32Extra";

(* extra definitions based on the Silver ISA for the equvialence of invisible registers/singals *)

val _ = prefer_num ();
val _ = guess_lengths ();

(* current instruction processed by Silver ISA *)
Definition instr:
  instr (a:ag32_state) = word_at_addr a.MEM (align_addr a.PC)
End

(* decode the opc, func and data ports based on the instr *)
Definition opc:
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

Definition func:
  func a :word4 =
  let opc = opc a in
    if opc = 0w \/ opc = 6w \/ opc = 9w \/ opc = 10w \/ opc = 11w then
      (9 >< 6) (instr a)
    else 9w
End

Definition addrA:
  addrA a = (22 >< 17) (instr a)
End

Definition addrB:
  addrB a = (15 >< 10) (instr a)
End

Definition addrW:
  addrW a = (30 >< 25) (instr a)
End

Definition flagA:
  flagA a = word_bit 23 (instr a)
End

Definition flagB:
  flagB a = word_bit 16 (instr a)
End

Definition flagW:
  flagW a = word_bit 31 (instr a)
End

(* generate the correct data for A/B/W ports *)
Definition reg_dataA:
  reg_dataA a = a.R (addrA a)
End

Definition reg_dataB:
  reg_dataB a = a.R (addrB a)
End

Definition reg_dataW:
  reg_dataW a = a.R (addrW a)
End

Definition immA:
  immA a :word32 = sw2sw ((22 >< 17) (instr a))
End

Definition immB:
  immB a :word32 = sw2sw ((15 >< 10) (instr a))
End

Definition immW:
  immW a :word32 = sw2sw ((30 >< 25) (instr a))
End

Definition dataA:
  dataA a = if (flagA a) then (immA a) else (reg_dataA a)
End

Definition dataB:
  dataB a = if (flagB a) then (immB a) else (reg_dataB a)
End

Definition dataW:
  dataW a = if (flagW a) then (immW a) else (reg_dataW a)
End

(* immediate *)
Definition imm:
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
Definition ALU_res:
  ALU_res a =
  let opc = opc a;
      func = func a;
      input1 = if opc = 9w then a.PC else dataA a;
      input2 = if opc = 9w then dataA a else dataB a;
      (v,a') = ALU (num2funcT (w2n func), input1, input2) a in
    v
End

(* compute the shift result *)
Definition shift_res:
  shift_res a =
  let instr = instr a;
      shiftOp = num2shiftT (w2n ((7 >< 6) instr)) in
    shift (shiftOp, dataA a, dataB a)
End

(* singals related to the accelerator *)
Definition acc_arg:
  acc_arg a = dataA a
End

Definition acc_res:
  acc_res a = accelerator_f (acc_arg a)
End

(* singals related to memory operations *)
Definition mem_data_addr:
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

Definition mem_data_wstrb:
  mem_data_wstrb a :word4 =
  let opc = opc a;
      dataB = dataB a in
    if opc = 2w then 15w
    else if opc = 3w then 1w <<~ w2w ((1 >< 0) dataB)
    else 0w     
End

Definition mem_data_wdata:
  mem_data_wdata a =
  let opc = opc a;
      dataA = dataA a in
    if opc = 2w then dataA
    else if opc = 3w then w2w ((7 >< 0) dataA)
    else 0w
End

Definition mem_data_rdata:
  mem_data_rdata a =
  let opc = opc a;
      mem_data_addr = mem_data_addr a in
    if opc = 4w then word_at_addr a.MEM mem_data_addr
    else if opc = 5w then w2w (a.MEM mem_data_addr)
    else 0w
End

(* singals related to update Silver register R *)
Definition reg_ifwrite:
  reg_ifwrite a =
  let opc = opc a in
    (opc = 0w) \/ (opc = 1w) \/ (opc = 4w) \/ (opc = 5w) \/ (opc = 6w) \/
    (opc = 7w) \/ (opc = 8w) \/ (opc = 9w) \/ (opc = 13w) \/ (opc = 14w)
End

Definition reg_wdata:
  reg_wdata a =
  let opc = opc a in
    if opc = 0w then ALU_res a
    else if (opc = 1w) \/ (opc = 6w) then shift_res a
    else if (opc = 4w) \/ (opc = 5w) then mem_data_rdata a
    else if opc = 7w then w2w a.data_in
    else if opc = 8w then acc_res a
    else if opc = 9w then a.PC + 4w
    else if opc = 13w then imm a
    else if opc = 14w then ((8 >< 0) (imm a)) @@ ((22 >< 0) (dataW a))
    else 0w
End

val _ = export_theory ();
