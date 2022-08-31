open hardwarePreamble agp32StateTheory agp32EnvironmentTheory ag32Theory ag32ExtraTheory;

val _ = new_theory "agp32Relation";

(** general variables:
    k: pipeline stage.
    t: cycle for the pipeline circuit.
    i: cycle (instr index) for the ISA.
 **)

val _ = prefer_num ();
val _ = guess_lengths ();


(** extra help functions on the ISA level **)
Definition isJump_isa_op_def:
  isJump_isa_op nop a =
  if nop = NONE then F
  else isJump_isa (FUNPOW Next (THE nop - 1) a)
End

Definition isAcc_isa_op_def:
  isAcc_isa_op nop a =
  if nop = NONE then F
  else isAcc_isa (FUNPOW Next (THE nop - 1) a)
End

Definition isMemOp_isa_op_def:
  isMemOp_isa_op nop a =
  if nop = NONE then F
  else isMemOp_isa (FUNPOW Next (THE nop - 1) a)
End

(* Additional definitions for the pipeline correctness proofs *)
(* enable_stg: stage k is enabled in the hardware circuit *)
Definition enable_stg_def:
  enable_stg k s =
  if k = 1 then s.IF.IF_PC_write_enable
  else if k = 2 then s.ID.ID_ID_write_enable
  else if k = 3 then s.ID.ID_EX_write_enable
  else if k = 4 then s.MEM.MEM_state_flag \/ s.MEM.MEM_enable
  else if k = 5 then (s.MEM.MEM_write_enable /\ s.WB.WB_state_flag) \/ s.WB.WB_enable
  else F
End

(* reg_data_vaild: the register data is vaild from the external components e.g. memory *)
(* TODO *)
Definition reg_data_vaild_def:
  reg_data_vaild k s =
  if k = 3 then enable_stg 4 s
  else if k = 5 then s.WB.WB_write_reg /\ s.WB.WB_state_flag
  else F
End

(* software conditions *)
(* self modified: a memory write operation does not affect the fetched value of the next 3 instructions *)
Definition SC_self_mod_isa_def:
  SC_self_mod_isa (a:ag32_state) <=>
  !n i. is_wrMEM_isa (FUNPOW Next (n-1) a) ==>
        i > n ==> i < n + 4 ==>
        align_addr (FUNPOW Next (i-1) a).PC <> align_addr (dataB (FUNPOW Next (n-1) a))
End

(* not used, to remove later
Definition SC_self_mod_def:
  SC_self_mod (I:num # num -> num option) (a:ag32_state) <=>
  !t j. j = THE (I (2,t)) \/ j = THE (I (3,t)) \/ j = THE (I (4,t)) ==>
        is_wrMEM_isa (FUNPOW Next (j-1) a) ==>
        align_addr (dataB (FUNPOW Next (j-1) a)) <> align_addr (FUNPOW Next (THE (I (1,t)) -1) a).PC
End
*)


(* Definitions of relations to prove the correctness of the pipelined Silver *)
(* relation for the initial states *)
Definition Init_def:
  Init (fext:ext) (s:state_circuit) (a:ag32_state) <=>
  (** CPU and ISA common items **)
  (s.PC = a.PC) /\
  (s.R = a.R) /\
  (s.EX.EX_carry_flag = a.CarryFlag) /\
  (s.EX.EX_overflow_flag = a.OverflowFlag) /\
  (s.data_out = a.data_out) /\
  (** memory **)
  (fext.mem = a.MEM) /\
  fext.ready /\
  (** data_in **)
  (fext.data_in = a.data_in) /\
  (** interrupt **)
  (fext.io_events = a.io_events) /\
  (fext.interrupt_state = InterruptReady) /\
  ~fext.interrupt_ack /\
  (** CPU own items **)
  (s.state = 3w) /\
  ~s.acc_arg_ready /\
  ~s.interrupt_req /\
  ~s.do_interrupt /\
  (s.command = 0w) /\
  (s.data_addr = 0xFFFFFFFFw) /\
  (s.IF.IF_instr = instr a) /\
  ~s.IF.IF_PC_write_enable /\
  (s.ID.ID_instr = 0x3Fw) /\
  ~s.ID.ID_ID_write_enable /\
  ~s.ID.ID_EX_write_enable /\
  (s.EX.EX_PC_sel = 0w) /\
  ~s.EX.EX_jump_sel /\
  (s.EX.EX_opc = 15w) /\
  (s.MEM.MEM_opc = 15w) /\
  ~s.MEM.MEM_state_flag /\
  ~s.MEM.MEM_enable /\
  ~s.MEM.MEM_write_reg /\
  ~s.MEM.MEM_write_enable /\
  ~s.WB.WB_enable /\
  ~s.WB.WB_write_reg
End

(* relation between the circuit and ISA state for different pipeline stages *)
Definition IF_PC_Rel_def:
  IF_PC_Rel (s:state_circuit) (a:ag32_state) (i:num) <=>
  (s.PC = (FUNPOW Next (i - 1) a).PC)
End

Definition IF_instr_Rel_def:
  IF_instr_Rel (s:state_circuit) (a:ag32_state) (i:num) <=>
  (s.IF.IF_instr = instr (FUNPOW Next (i - 1) a))
End

Definition ID_Rel_def:
  ID_Rel (fext:ext) (s:state_circuit) (a:ag32_state) (i:num) <=>
  ((s.ID.ID_PC = (FUNPOW Next (i-1) a).PC) /\
   (s.ID.ID_instr = instr (FUNPOW Next (i - 1) a)) /\
   (s.ID.ID_addrA = addrA (FUNPOW Next (i - 1) a)) /\
   (s.ID.ID_addrB = addrB (FUNPOW Next (i - 1) a)) /\
   (s.ID.ID_addrW = addrW (FUNPOW Next (i - 1) a)) /\
   (s.ID.ID_addrA_disable <=> flagA (FUNPOW Next (i - 1) a)) /\
   (s.ID.ID_addrB_disable <=> flagB (FUNPOW Next (i - 1) a)) /\
   (s.ID.ID_addrW_disable <=> flagW (FUNPOW Next (i - 1) a)) /\
   (s.ID.ID_immA = immA (FUNPOW Next (i - 1) a)) /\
   (s.ID.ID_immB = immB (FUNPOW Next (i - 1) a)) /\
   (s.ID.ID_immW = immW (FUNPOW Next (i - 1) a)) /\
   (s.ID.ID_imm = imm (FUNPOW Next (i - 1) a)) /\
   (s.ID.ID_opc = opc (FUNPOW Next (i - 1) a)) /\
   (s.ID.ID_func = func (FUNPOW Next (i - 1) a)) /\
   (s.ID.ID_addrA = s.WB.WB_addrW /\ s.WB.WB_write_reg <=> s.ID.ID_ForwardA) /\
   (s.ID.ID_addrB = s.WB.WB_addrW /\ s.WB.WB_write_reg <=> s.ID.ID_ForwardB) /\
   (s.ID.ID_addrW = s.WB.WB_addrW /\ s.WB.WB_write_reg <=> s.ID.ID_ForwardW) /\
   (s.ID.ID_ForwardA ==> s.WB.WB_write_data = reg_dataA (FUNPOW Next (i - 1) a)) /\
   (~s.ID.ID_ForwardA ==> s.ID.ID_read_dataA = reg_dataA (FUNPOW Next (i - 1) a)) /\
   (s.ID.ID_ForwardB ==> s.WB.WB_write_data = reg_dataB (FUNPOW Next (i - 1) a)) /\
   (~s.ID.ID_ForwardB ==> s.ID.ID_read_dataB = reg_dataB (FUNPOW Next (i - 1) a)) /\
   (s.ID.ID_ForwardW ==> s.WB.WB_write_data = reg_dataW (FUNPOW Next (i - 1) a)) /\
   (~s.ID.ID_ForwardW ==> s.ID.ID_read_dataW = reg_dataW (FUNPOW Next (i - 1) a)) /\
   (s.ID.ID_read_dataA_updated = reg_dataA (FUNPOW Next (i - 1) a)) /\
   (s.ID.ID_read_dataB_updated = reg_dataB (FUNPOW Next (i - 1) a)) /\
   (s.ID.ID_read_dataW_updated = reg_dataW (FUNPOW Next (i - 1) a)) /\
   (s.ID.ID_addrA_disable ==> s.ID.ID_dataA = dataA (FUNPOW Next (i - 1) a)) /\
   (s.ID.ID_addrB_disable ==> s.ID.ID_dataB = dataB (FUNPOW Next (i - 1) a)) /\
   (s.ID.ID_addrW_disable ==> s.ID.ID_dataW = dataW (FUNPOW Next (i - 1) a)))
End

Definition EX_Rel_def:
  EX_Rel (fext:ext) (s:state_circuit) (a:ag32_state) (i:num) <=>
  ((s.EX.EX_PC = (FUNPOW Next (i-1) a).PC) /\
   (s.EX.EX_addrA = addrA (FUNPOW Next (i-1) a)) /\
   (s.EX.EX_addrB = addrB (FUNPOW Next (i-1) a)) /\
   (s.EX.EX_addrW = addrW (FUNPOW Next (i-1) a)) /\
   (s.EX.EX_addrA_disable <=> flagA (FUNPOW Next (i-1) a)) /\
   (s.EX.EX_addrB_disable <=> flagB (FUNPOW Next (i-1) a)) /\
   (s.EX.EX_addrW_disable <=> flagW (FUNPOW Next (i-1) a)) /\
   (s.EX.EX_ForwardA = 0w ==> s.EX.EX_dataA = dataA (FUNPOW Next (i-1) a)) /\
   (s.EX.EX_ForwardA = 1w ==> s.WB.WB_write_data = dataA (FUNPOW Next (i-1) a)) /\
   (s.EX.EX_ForwardA = 2w ==> s.MEM.MEM_ALU_res = dataA (FUNPOW Next (i-1) a)) /\
   (s.EX.EX_ForwardA = 3w ==> s.MEM.MEM_SHIFT_res = dataA (FUNPOW Next (i-1) a)) /\
   (s.EX.EX_ForwardA = 4w ==> s.MEM.MEM_PC + 4w = dataA (FUNPOW Next (i-1) a)) /\
   (s.EX.EX_ForwardA = 5w ==> s.MEM.MEM_imm_updated = dataA (FUNPOW Next (i-1) a)) /\
   (s.EX.EX_ForwardB = 0w ==> s.EX.EX_dataB = dataB (FUNPOW Next (i-1) a)) /\
   (s.EX.EX_ForwardB = 1w ==> s.WB.WB_write_data = dataB (FUNPOW Next (i-1) a)) /\
   (s.EX.EX_ForwardB = 2w ==> s.MEM.MEM_ALU_res = dataB (FUNPOW Next (i-1) a)) /\
   (s.EX.EX_ForwardB = 3w ==> s.MEM.MEM_SHIFT_res = dataB (FUNPOW Next (i-1) a)) /\
   (s.EX.EX_ForwardB = 4w ==> s.MEM.MEM_PC + 4w = dataB (FUNPOW Next (i-1) a)) /\
   (s.EX.EX_ForwardB = 5w ==> s.MEM.MEM_imm_updated = dataB (FUNPOW Next (i-1) a)) /\
   (s.EX.EX_ForwardW = 0w ==> s.EX.EX_dataW = dataW (FUNPOW Next (i-1) a)) /\
   (s.EX.EX_ForwardW = 1w ==> s.WB.WB_write_data = dataW (FUNPOW Next (i-1) a)) /\
   (s.EX.EX_ForwardW = 2w ==> s.MEM.MEM_ALU_res = dataW (FUNPOW Next (i-1) a)) /\
   (s.EX.EX_ForwardW = 3w ==> s.MEM.MEM_SHIFT_res = dataW (FUNPOW Next (i-1) a)) /\
   (s.EX.EX_ForwardW = 4w ==> s.MEM.MEM_PC + 4w = dataW (FUNPOW Next (i-1) a)) /\
   (s.EX.EX_ForwardW = 5w ==> s.MEM.MEM_imm_updated = dataW (FUNPOW Next (i-1) a)) /\
   (s.EX.EX_dataA_updated = dataA (FUNPOW Next (i-1) a)) /\
   (s.EX.EX_dataB_updated = dataB (FUNPOW Next (i-1) a)) /\
   (s.EX.EX_dataW_updated = dataW (FUNPOW Next (i-1) a)) /\
   (s.EX.EX_dataA_rec = dataA (FUNPOW Next (i-1) a)) /\
   (s.EX.EX_dataB_rec = dataB (FUNPOW Next (i-1) a)) /\
   (s.EX.EX_dataW_rec = dataW (FUNPOW Next (i-1) a)) /\
   (s.EX.EX_imm = imm (FUNPOW Next (i-1) a)) /\
   (s.EX.EX_ALU_input1 = ALU_input1 (FUNPOW Next (i-1) a)) /\
   (s.EX.EX_ALU_input2 = ALU_input2 (FUNPOW Next (i-1) a)) /\
   (s.EX.EX_ALU_res = ALU_res (FUNPOW Next (i-1) a)) /\
   (s.EX.EX_SHIFT_res = shift_res (FUNPOW Next (i-1) a)) /\
   (s.EX.EX_opc = 8w <=> s.EX.EX_isAcc) /\
   (s.EX.EX_opc = 9w ==> s.EX.EX_PC_sel = 1w) /\
   (s.EX.EX_opc = 10w ==> s.EX.EX_PC_sel = 2w) /\
   (s.EX.EX_opc = 11w ==> s.EX.EX_PC_sel = 3w) /\
   (s.EX.EX_jump_sel ==> s.EX.EX_jump_addr = (FUNPOW Next i a).PC) /\
   (s.EX.EX_opc = opc (FUNPOW Next (i-1) a)) /\
   (s.EX.EX_func = func (FUNPOW Next (i-1) a)))
End

(** items belong to the EX stage that are checked only when the EX stage has vaild data **)
Definition EX_Rel_spec_def:
   EX_Rel_spec (s:state_circuit) (a:ag32_state) (iop:num option) <=>
   (s.EX.EX_jump_sel <=> isJump_isa_op iop a)
End

Definition MEM_Rel_def:
  MEM_Rel (fext:ext) (s:state_circuit) (a:ag32_state) (i:num) <=>
  ((s.MEM.MEM_PC = (FUNPOW Next (i-1) a).PC) /\
   (s.MEM.MEM_addrW = addrW (FUNPOW Next (i-1) a)) /\
   (s.MEM.MEM_dataA = dataA (FUNPOW Next (i-1) a)) /\
   (s.MEM.MEM_dataB = dataB (FUNPOW Next (i-1) a)) /\
   (s.MEM.MEM_dataW = dataW (FUNPOW Next (i-1) a)) /\
   (s.MEM.MEM_imm = imm (FUNPOW Next (i-1) a)) /\
   (s.MEM.MEM_imm_updated =
    ((8 >< 0) (imm (FUNPOW Next (i-1) a))) @@ ((22 >< 0) (dataW (FUNPOW Next (i-1) a)))) /\
   (s.MEM.MEM_ALU_res = ALU_res (FUNPOW Next (i-1) a)) /\
   (s.MEM.MEM_SHIFT_res = shift_res (FUNPOW Next (i-1) a)) /\
   (s.MEM.MEM_write_reg <=> reg_iswrite (FUNPOW Next (i-1) a)) /\
   (s.MEM.MEM_opc = opc (FUNPOW Next (i-1) a)) /\
   (s.MEM.MEM_read_mem = mem_isread (FUNPOW Next (i-1) a)) /\
   (s.MEM.MEM_write_mem = mem_iswrite (FUNPOW Next (i-1) a)) /\
   (s.MEM.MEM_write_mem_byte = mem_iswrite_byte (FUNPOW Next (i-1) a)) /\
   (s.MEM.MEM_isInterrupt = isinterrupt (FUNPOW Next (i-1) a)) /\
   (s.data_addr = mem_data_addr (FUNPOW Next (i-1) a)) /\
   (s.data_wstrb = mem_data_wstrb (FUNPOW Next (i-1) a)) /\
   (s.data_wdata = mem_data_wdata (FUNPOW Next (i-1) a)) /\
   (fext.data_rdata = mem_data_rdata (FUNPOW Next (i-1) a)))
End

Definition WB_Rel_def:
  WB_Rel (fext:ext) (s:state_circuit) (a:ag32_state) (i:num) <=>
  ((s.WB.WB_PC = (FUNPOW Next (i-1) a).PC) /\
   (s.WB.WB_addrW = addrW (FUNPOW Next (i-1) a)) /\
   (s.WB.WB_dataA = dataA (FUNPOW Next (i-1) a)) /\
   (s.WB.WB_opc = 14w ==> s.WB.WB_imm =
                          ((8 >< 0) (imm (FUNPOW Next (i-1) a))) @@ ((22 >< 0) (dataW (FUNPOW Next (i-1) a)))) /\
   (s.WB.WB_opc <> 14w ==> s.WB.WB_imm = imm (FUNPOW Next (i-1) a)) /\
   (s.WB.WB_ALU_res = ALU_res (FUNPOW Next (i-1) a)) /\
   (s.WB.WB_SHIFT_res = shift_res (FUNPOW Next (i-1) a)) /\
   (s.WB.WB_read_data = mem_data_rdata (FUNPOW Next (i-1) a)) /\
   (s.WB.WB_read_data_byte = mem_data_rdata (FUNPOW Next (i-1) a)) /\
   (s.WB.WB_write_reg = reg_iswrite (FUNPOW Next (i-1) a)) /\
   (s.WB.WB_opc = opc (FUNPOW Next (i-1) a)) /\
   (s.WB.WB_data_sel = reg_wdata_sel (FUNPOW Next (i-1) a)) /\
   (s.WB.WB_write_data = reg_wdata (FUNPOW Next (i-1) a)))
End

(* TODO: refine the definition *)
(* si: circuit state at the previous cycle *)
Definition Rel_def:
  Rel (I:num # num -> num option) (fext:ext) (si:state_circuit) (s:state_circuit) (a:ag32_state) (t:num) <=>
  (fext.data_in = (FUNPOW Next (THE (I (5,t))) a).data_in) /\
  ((s.EX.EX_carry_flag <=> (FUNPOW Next (THE (I (3,t))) a).CarryFlag)) /\
  (reg_data_vaild 3 s ==> (s.EX.EX_overflow_flag <=> (FUNPOW Next (THE (I (3,t))) a).OverflowFlag)) /\
  (reg_data_vaild 3 s ==> (s.EX.EX_jump_sel ==> s.IF.IF_PC_input = (FUNPOW Next (THE (I (3,t))) a).PC)) /\                 
  (I (1,t) <> NONE ==> (~s.EX.EX_jump_sel ==> s.IF.IF_PC_input = (FUNPOW Next (THE (I (1,t)) - 1) a).PC + 4w)) /\
  (fext.ready ==> fext.mem = (FUNPOW Next (THE (I (4,t))) a).MEM) /\
  (~fext.ready ==> ~enable_stg 1 s) /\
  (~fext.ready ==> ~enable_stg 2 s) /\                                     
  (s.data_out = (FUNPOW Next (THE (I (5,t))) a).data_out) /\
  (reg_data_vaild 5 s ==> (s.R = (FUNPOW Next (THE (I (5,t))) a).R)) /\
  ((I (1,t) <> NONE) ==> IF_PC_Rel s a (THE (I (1,t)))) /\
  ((I (1,t) <> NONE) ==> fext.ready ==> IF_instr_Rel s a (THE (I (1,t)))) /\
  (enable_stg 2 si ==> (I (2,t) <> NONE) ==> ID_Rel fext s a (THE (I (2,t)))) /\
  (enable_stg 3 si ==> EX_Rel fext s a (THE (I (3,t)))) /\
  (reg_data_vaild 3 s ==> EX_Rel_spec s a (I (3,t))) /\
  (enable_stg 4 si ==> MEM_Rel fext s a (THE (I (4,t)))) /\
  (enable_stg 5 si ==> WB_Rel fext s a (THE (I (5,t))))
End


(* oracle for the scheduling function I *)
Definition is_sch_init_def:
  is_sch_init (I:num # num -> num option) <=>
  (I (1,0) = SOME 1) /\
  (!k. k <> 1 ==> I (k,0) = NONE)
End

Definition is_sch_fetch_def:
  is_sch_fetch (I:num # num -> num option) (sf:num -> state_circuit) (a:ag32_state) <=>
  (!t. enable_stg 1 (sf t) ==> 
       isJump_isa_op (I (3,t)) a ==>
       I (1,SUC t) = SOME (THE (I (3,t)) + 1)) /\
  (!t. enable_stg 1 (sf t) ==>
       ~isJump_isa_op (I (3,t)) a ==>
       (isJump_isa_op (I (1,t)) a \/ isJump_isa_op (I (2,t)) a \/
        I (1,t) = NONE \/ THE (I (1,t)) = 0) ==>
       I (1,SUC t) = NONE) /\
  (!t. enable_stg 1 (sf t) ==>
       ~isJump_isa_op (I (3,t)) a ==>
       ~isJump_isa_op (I (1,t)) a ==>
       ~isJump_isa_op (I (2,t)) a ==>
       I (1,t) <> NONE ==>
       THE (I (1,t)) <> 0 ==>
       I (1,SUC t) = SOME (THE (I (1,t)) + 1))
End

Definition is_sch_decode_def:
  is_sch_decode (I:num # num -> num option) (sf:num -> state_circuit) (a:ag32_state) <=>
  (!t. enable_stg 2 (sf t) ==>
       (isJump_isa_op (I (2,t)) a \/ isJump_isa_op (I (3,t)) a) ==>
       I (2,SUC t) = NONE) /\
  (!t. enable_stg 2 (sf t) ==>
       ~isJump_isa_op (I (2,t)) a ==>
       ~isJump_isa_op (I (3,t)) a ==>
       I (2,SUC t) = I (1,t))
End

Definition is_sch_execute_def:
  is_sch_execute (I:num # num -> num option) (sf:num -> state_circuit) (a:ag32_state) <=>
  (!t. enable_stg 3 (sf t) ==>
       (isJump_isa_op (I (3,t)) a \/ isAcc_isa_op (I (3,t)) a) ==>
       I (3,SUC t) = NONE) /\
  (!t. enable_stg 3 (sf t) ==>
       ~isJump_isa_op (I (3,t)) a ==>
       ~isAcc_isa_op (I (3,t)) a ==>
       I (3,SUC t) = I (2,t))
End

Definition is_sch_memory_def:
  is_sch_memory (I:num # num -> num option) (sf:num -> state_circuit) (a:ag32_state) <=>
  (!t. enable_stg 4 (sf t) ==>
       isMemOp_isa_op (I (4,t)) a ==>
       I (4,SUC t) = NONE) /\
  (!t. enable_stg 4 (sf t) ==>
       ~isMemOp_isa_op (I (4,t)) a ==>
       I (4,SUC t) = I (3,t))
End

Definition is_sch_writeback_def:
  is_sch_writeback (I:num # num -> num option) (sf:num -> state_circuit) <=>
  (!t. enable_stg 5 (sf t) ==> I (5,SUC t) = I (4,t))
End

Definition is_sch_disable_def:
  is_sch_disable (I:num # num -> num option) (sf:num -> state_circuit) =
  (!t k. ~enable_stg k (sf t) ==> k <> 2 ==> I (k,SUC t) = I (k,t))
End

Definition is_sch_disable_ID_def:
  is_sch_disable_ID (I:num # num -> num option) (sf:num -> state_circuit) <=>
  (!t. (~enable_stg 2 (sf t) ==> (sf t).ID.ID_flush_flag ==> I (2,SUC t) = NONE) /\
       (~enable_stg 2 (sf t) ==> ~(sf t).ID.ID_flush_flag ==> I (2,SUC t) = I (2,t)))
End

Definition is_sch_def:
  is_sch (I:num # num -> num option) (sf:num -> state_circuit) (a:ag32_state) <=>
  is_sch_init I /\
  is_sch_fetch I sf a/\
  is_sch_decode I sf a /\
  is_sch_execute I sf a /\
  is_sch_memory I sf a /\
  is_sch_writeback I sf /\
  is_sch_disable I sf /\
  is_sch_disable_ID I sf
End

val _ = export_theory ();
