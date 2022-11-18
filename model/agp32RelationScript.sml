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

Definition isJump_hw_op_def:
  isJump_hw_op s <=> s.EX.EX_jump_sel
End

Definition isAcc_isa_op_def:
  isAcc_isa_op nop a =
  if nop = NONE then F
  else isAcc_isa (FUNPOW Next (THE nop - 1) a)
End

Definition isMemOp_isa_op_def:
  isMemOp_isa_op nop a =
  if nop = NONE then F
  else isMEM_stg_op_isa (FUNPOW Next (THE nop - 1) a)
End

Definition isMemOp_hw_op_def:
  isMemOp_hw_op s <=> 
  (s.MEM.MEM_opc = 2w) \/ (s.MEM.MEM_opc = 3w) \/ (s.MEM.MEM_opc = 4w) \/
  (s.MEM.MEM_opc = 5w) \/ (s.MEM.MEM_opc = 8w) \/ (s.MEM.MEM_opc = 12w)
End

Definition reg_data_hazard_def:
  reg_data_hazard s <=>
  (s.EX.EX_checkA \/ s.EX.EX_checkB \/ s.EX.EX_checkW \/
   s.MEM.MEM_checkA \/ s.MEM.MEM_checkB \/ s.MEM.MEM_checkW \/
   s.WB.WB_checkA \/ s.WB.WB_checkB \/ s.WB.WB_checkW)
End

Definition reg_adr_update_isa_def:
  reg_adr_update_isa nop a adr =
  if nop = NONE then F
  else reg_iswrite (FUNPOW Next (THE nop - 1) a) /\ (addrW (FUNPOW Next (THE nop - 1) a) = adr)
End

(* Additional definitions for the pipeline correctness proofs *)
(* enable_stg: stage k is enabled in the hardware circuit *)
Definition enable_stg_def:
  enable_stg k s =
  if k = 1 then s.IF.IF_PC_write_enable
  else if k = 2 then s.ID.ID_ID_write_enable
  else if k = 3 then s.ID.ID_EX_write_enable
  else if k = 4 then s.MEM.MEM_state_flag
  else if k = 5 then s.WB.WB_state_flag
  else F
End

(* wb_data_vaild: the register data is vaild from the external components e.g. memory *)
Definition wb_data_vaild_def:
  wb_data_vaild s = s.WB.WB_state_flag
End


(* software conditions *)
(* self modified: a memory write operation does not affect the fetched value of the next 3 instructions *)
Definition SC_self_mod_isa_def:
  SC_self_mod_isa (a:ag32_state) <=>
  !n i. is_wrMEM_isa (FUNPOW Next (n-1) a) ==>
        i > n ==> i < n + 4 ==>
        align_addr (FUNPOW Next (i-1) a).PC <> align_addr (dataB (FUNPOW Next (n-1) a))
End


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
  (** others **)
  (s.state = 3w) /\
  ~s.acc_arg_ready /\
  ~s.interrupt_req /\
  ~s.do_interrupt /\
  ~s.EX.EX_jump_sel /\
  (s.IF.IF_instr = instr a) /\
  ~s.IF.IF_PC_write_enable /\
  ~s.ID.ID_ID_write_enable /\
  ~s.ID.ID_EX_write_enable /\
  ~s.MEM.MEM_state_flag /\
  ~s.WB.WB_state_flag
End


(* relation between the circuit and ISA state for different pipeline stages *)
(** fetch stage **)
Definition IF_PC_Rel_def:
  IF_PC_Rel (s:state_circuit) (a:ag32_state) (i:num) <=>
  (s.PC = (FUNPOW Next (i - 1) a).PC)
End

Definition IF_instr_Rel_def:
  IF_instr_Rel (s:state_circuit) (a:ag32_state) (i:num) <=>
  (s.IF.IF_instr = instr (FUNPOW Next (i - 1) a))
End

(** decode stage **)
Definition ID_Rel_def:
  ID_Rel (s:state_circuit) (a:ag32_state) (i:num) <=>
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
   (s.ID.ID_addrA_disable ==> s.ID.ID_dataA = dataA (FUNPOW Next (i - 1) a)) /\
   (s.ID.ID_addrB_disable ==> s.ID.ID_dataB = dataB (FUNPOW Next (i - 1) a)) /\
   (s.ID.ID_addrW_disable ==> s.ID.ID_dataW = dataW (FUNPOW Next (i - 1) a)))
End

Definition ID_reg_data_Rel_def:
  ID_reg_data_Rel s a i eop mop wop <=>
  (~s.ID.ID_addrA_disable ==>
   ~reg_adr_update_isa eop a s.ID.ID_addrA ==> 
   ~reg_adr_update_isa mop a s.ID.ID_addrA ==> 
   ~reg_adr_update_isa wop a s.ID.ID_addrA ==>
   (s.ID.ID_read_dataA = reg_dataA (FUNPOW Next (i - 1) a)) /\
   (s.ID.ID_dataA = dataA (FUNPOW Next (i - 1) a))) /\
  (~s.ID.ID_addrB_disable ==>
   ~reg_adr_update_isa eop a s.ID.ID_addrB ==> 
   ~reg_adr_update_isa mop a s.ID.ID_addrB ==> 
   ~reg_adr_update_isa wop a s.ID.ID_addrB ==>
   (s.ID.ID_read_dataB = reg_dataB (FUNPOW Next (i - 1) a)) /\
   (s.ID.ID_dataB = dataB (FUNPOW Next (i - 1) a))) /\
  (~s.ID.ID_addrW_disable ==>
   ~reg_adr_update_isa eop a s.ID.ID_addrW ==> 
   ~reg_adr_update_isa mop a s.ID.ID_addrW ==> 
   ~reg_adr_update_isa wop a s.ID.ID_addrW ==>
   (s.ID.ID_read_dataW = reg_dataW (FUNPOW Next (i - 1) a)) /\
   (s.ID.ID_dataW = dataW (FUNPOW Next (i - 1) a)))
End

Definition ID_data_dep_Rel_def:
  ID_data_dep_Rel s a eop mop wop <=>
  (~s.ID.ID_addrA_disable ==> 
   (s.EX.EX_checkA <=> reg_adr_update_isa eop a s.ID.ID_addrA) /\
   (s.MEM.MEM_checkA <=> reg_adr_update_isa mop a s.ID.ID_addrA) /\
   (s.WB.WB_checkA <=> reg_adr_update_isa wop a s.ID.ID_addrA)) /\
  (~s.ID.ID_addrB_disable ==>
   (s.EX.EX_checkB <=> reg_adr_update_isa eop a s.ID.ID_addrB) /\
   (s.MEM.MEM_checkB <=> reg_adr_update_isa mop a s.ID.ID_addrB) /\
   (s.WB.WB_checkB <=> reg_adr_update_isa wop a s.ID.ID_addrB)) /\
  (~s.ID.ID_addrW_disable ==> 
   (s.EX.EX_checkW <=> reg_adr_update_isa eop a s.ID.ID_addrW) /\
   (s.MEM.MEM_checkW <=> reg_adr_update_isa mop a s.ID.ID_addrW) /\
   (s.WB.WB_checkW <=> reg_adr_update_isa wop a s.ID.ID_addrW))
End

(** execute stage **)
Definition EX_Rel_def:
  EX_Rel (fext:ext) (s:state_circuit) (a:ag32_state) (i:num) <=>
  ((s.EX.EX_PC = (FUNPOW Next (i-1) a).PC) /\
   (s.EX.EX_addrW = addrW (FUNPOW Next (i-1) a)) /\
   (s.EX.EX_imm = imm (FUNPOW Next (i-1) a)) /\
   (s.EX.EX_opc = opc (FUNPOW Next (i-1) a)) /\
   (s.EX.EX_func = func (FUNPOW Next (i-1) a)) /\
   (s.EX.EX_write_reg <=> reg_iswrite (FUNPOW Next (i-1) a)) /\
   (s.EX.EX_opc <> 14w ==> s.EX.EX_imm_updated = imm (FUNPOW Next (i-1) a)) /\
   (s.EX.EX_opc = 14w ==> s.EX.EX_imm_updated = ((8 >< 0) (imm (FUNPOW Next (i-1) a))) @@ ((22 >< 0) (dataW (FUNPOW Next (i-1) a)))) /\
   (s.EX.EX_dataA = dataA (FUNPOW Next (i-1) a)) /\
   (s.EX.EX_dataB = dataB (FUNPOW Next (i-1) a)) /\
   (s.EX.EX_dataW = dataW (FUNPOW Next (i-1) a)) /\
   (s.EX.EX_ALU_input1 = ALU_input1 (FUNPOW Next (i-1) a)) /\
   (s.EX.EX_ALU_input2 = ALU_input2 (FUNPOW Next (i-1) a)) /\
   (s.EX.EX_ALU_res = ALU_res (FUNPOW Next (i-1) a)) /\
   (s.EX.EX_opc = 1w ==> s.EX.EX_SHIFT_res = shift_res (FUNPOW Next (i-1) a)))
End

(** items belong to the EX stage that are related to jumps **)
Definition EX_Rel_spec_def:
   EX_Rel_spec (s:state_circuit) (a:ag32_state) (iop:num option) <=>
   (s.EX.EX_jump_sel = isJump_isa_op iop a) /\
   (s.EX.EX_jump_sel ==> s.EX.EX_jump_addr = (FUNPOW Next (THE iop) a).PC)
End

(** memory stage **)
Definition MEM_Rel_def:
  MEM_Rel (s:state_circuit) (a:ag32_state) (i:num) <=>
  ((s.MEM.MEM_PC = (FUNPOW Next (i-1) a).PC) /\
   (s.MEM.MEM_addrW = addrW (FUNPOW Next (i-1) a)) /\
   (s.MEM.MEM_dataA = dataA (FUNPOW Next (i-1) a)) /\
   (s.MEM.MEM_dataB = dataB (FUNPOW Next (i-1) a)) /\
   (s.MEM.MEM_opc = opc (FUNPOW Next (i-1) a)) /\
   (s.MEM.MEM_opc <> 14w ==> s.MEM.MEM_imm = imm (FUNPOW Next (i-1) a)) /\
   (s.MEM.MEM_opc = 14w ==> s.MEM.MEM_imm =
    ((8 >< 0) (imm (FUNPOW Next (i-1) a))) @@ ((22 >< 0) (dataW (FUNPOW Next (i-1) a)))) /\
   (s.MEM.MEM_ALU_res = ALU_res (FUNPOW Next (i-1) a)) /\
   (s.MEM.MEM_opc = 1w ==> s.MEM.MEM_SHIFT_res = shift_res (FUNPOW Next (i-1) a)) /\
   (s.MEM.MEM_write_reg <=> reg_iswrite (FUNPOW Next (i-1) a)) /\
   (s.MEM.MEM_read_mem = mem_isread (FUNPOW Next (i-1) a)) /\
   (s.MEM.MEM_write_mem = mem_iswrite (FUNPOW Next (i-1) a)) /\
   (s.MEM.MEM_write_mem_byte = mem_iswrite_byte (FUNPOW Next (i-1) a)) /\
   (s.MEM.MEM_isAcc = isAcc_isa (FUNPOW Next (i-1) a)) /\
   (s.MEM.MEM_isInterrupt = isinterrupt (FUNPOW Next (i-1) a)))
End

(** requests that may cause delays **)
Definition MEM_req_rel_def:
  MEM_req_rel (fext:ext) (si:state_circuit) (s:state_circuit) (a:ag32_state) (i:num) <=>
  ((s.WB.WB_opc = 4w ==> ((align_addr s.data_addr) = mem_data_addr (FUNPOW Next (i-1) a))) /\
   (s.WB.WB_opc = 5w ==> s.data_addr = mem_data_addr (FUNPOW Next (i-1) a)) /\
   (s.WB.WB_opc = 2w ==> (align_addr s.data_addr) = mem_data_addr (FUNPOW Next (i-1) a)) /\
   (s.WB.WB_opc = 3w ==> s.data_addr = mem_data_addr (FUNPOW Next (i-1) a)) /\
   (s.WB.WB_opc = 2w ==> s.data_wstrb = mem_data_wstrb (FUNPOW Next (i-1) a)) /\
   (s.WB.WB_opc = 3w ==> s.data_wstrb = mem_data_wstrb (FUNPOW Next (i-1) a)) /\
   (s.WB.WB_opc = 2w ==> s.data_wdata = mem_data_wdata (FUNPOW Next (i-1) a)) /\
   (s.WB.WB_opc = 3w ==> s.data_wdata = mem_data_wdata (FUNPOW Next (i-1) a)) /\
   (s.WB.WB_opc = 4w ==> s.command = 2w) /\
   (s.WB.WB_opc = 5w ==> s.command = 2w) /\
   (s.WB.WB_opc = 2w ==> s.command = 3w) /\
   (s.WB.WB_opc = 3w ==> s.command = 3w))
End

(** write back stage **)
Definition WB_Rel_def:
  WB_Rel (fext:ext) (s:state_circuit) (a:ag32_state) (i:num) <=>
  ((s.WB.WB_PC = (FUNPOW Next (i-1) a).PC) /\
   (s.WB.WB_addrW = addrW (FUNPOW Next (i-1) a)) /\
   (s.WB.WB_opc = opc (FUNPOW Next (i-1) a)) /\
   (s.WB.WB_dataA = dataA (FUNPOW Next (i-1) a)) /\
   (s.WB.WB_opc = 14w ==> s.WB.WB_imm =
                          ((8 >< 0) (imm (FUNPOW Next (i-1) a))) @@ ((22 >< 0) (dataW (FUNPOW Next (i-1) a)))) /\
   (s.WB.WB_opc <> 14w ==> s.WB.WB_imm = imm (FUNPOW Next (i-1) a)) /\
   (s.WB.WB_ALU_res = ALU_res (FUNPOW Next (i-1) a)) /\
   (s.WB.WB_opc = 1w ==> s.WB.WB_SHIFT_res = shift_res (FUNPOW Next (i-1) a)) /\
   (s.WB.WB_read_data = mem_data_rdata (FUNPOW Next (i-1) a)) /\
   (s.WB.WB_read_data_byte = mem_data_rdata (FUNPOW Next (i-1) a)) /\
   (s.WB.WB_isOut = (s.WB.WB_opc = 6w)) /\ 
   (s.WB.WB_write_reg = reg_iswrite (FUNPOW Next (i-1) a)) /\
   (s.WB.WB_data_sel = reg_wdata_sel (FUNPOW Next (i-1) a)) /\
   (s.WB.WB_write_data = reg_wdata (FUNPOW Next (i-1) a)))
End

(** circuit level invariants **)
Definition Inv_Rel_def:
  Inv_Rel (I:num # num -> num option) (si:state_circuit) (s:state_circuit) (a:ag32_state) (t:num) <=>
  ((~isJump_hw_op s ==> ~isJump_isa_op (I (2,t)) a ==> I (1,t) <> NONE) /\
   (enable_stg 2 si ==> ~isJump_hw_op s ==> I (2,t) = NONE ==> isJump_hw_op si) /\
   (enable_stg 2 si ==> enable_stg 3 s ==> ~isJump_hw_op s ==> ~reg_data_hazard s ==> I (3,SUC t) = NONE ==>
    isJump_hw_op si) /\
   (~enable_stg 2 si ==> ~isJump_hw_op s ==> I (2,t) = NONE ==> s.ID.ID_opc = 15w) /\
   (I (3,t) = NONE ==> (s.EX.EX_opc = 16w \/ s.EX.EX_opc = 15w)) /\
   (I (3,t) = NONE ==> ~s.EX.EX_write_reg) /\
   (I (4,t) = NONE ==> (s.MEM.MEM_opc = 16w \/ s.MEM.MEM_opc = 15w)) /\
   (I (4,t) = NONE ==> ~s.MEM.MEM_write_reg) /\
   (I (5,t) = NONE ==> (s.WB.WB_opc = 16w \/ s.WB.WB_opc = 15w)) /\
   (I (5,t) = NONE ==> ~s.WB.WB_write_reg) /\
   (I (1,t) <> NONE ==> I (2,t) = NONE ==> I (3,t) = NONE ==> I (4,t) = NONE ==> I (5,t) <> NONE ==>
    (THE (I (1,t)) > THE (I (5,t))) /\ (THE (I (1,t)) < THE (I (5,t)) + 2)))
End


(* si: circuit state at the previous cycle *)
Definition Rel_def:
  Rel (I:num # num -> num option) (fext:ext) (si:state_circuit) (s:state_circuit) (a:ag32_state) (t:num) <=>
  (I (5,t) <> NONE ==> fext.data_in = (FUNPOW Next (THE (I (5,t))) a).data_in) /\
  (I (3,t) <> NONE ==> (s.EX.EX_carry_flag <=> (FUNPOW Next (THE (I (3,t))) a).CarryFlag)) /\
  (I (3,t) = NONE ==> I (2,t) <> NONE ==> (s.EX.EX_carry_flag <=> (FUNPOW Next (THE (I (2,t)) - 1) a).CarryFlag)) /\
  (I (3,t) = NONE ==> I (2,t) = NONE ==> I (1,t) <> NONE ==>
   (s.EX.EX_carry_flag <=> (FUNPOW Next (THE (I (1,t)) - 1) a).CarryFlag)) /\
  (I (3,t) <> NONE ==> (s.EX.EX_overflow_flag <=> (FUNPOW Next (THE (I (3,t))) a).OverflowFlag)) /\
  (I (3,t) = NONE ==> I (2,t) <> NONE ==> (s.EX.EX_overflow_flag <=> (FUNPOW Next (THE (I (2,t)) - 1) a).OverflowFlag)) /\
  (I (3,t) = NONE ==> I (2,t) = NONE ==> I (1,t) <> NONE ==>
   (s.EX.EX_overflow_flag <=> (FUNPOW Next (THE (I (1,t)) - 1) a).OverflowFlag)) /\
  (I (3,t) <> NONE ==> (s.EX.EX_jump_sel ==> s.IF.IF_PC_input = (FUNPOW Next (THE (I (3,t))) a).PC)) /\                 
  (I (1,t) <> NONE ==> (~s.EX.EX_jump_sel ==> s.IF.IF_PC_input = (FUNPOW Next (THE (I (1,t)) - 1) a).PC + 4w)) /\
  (I (4,t) <> NONE ==> fext.ready ==> fext.mem = (FUNPOW Next (THE (I (4,t))) a).MEM) /\
  (I (4,t) = NONE ==> I (3,t) <> NONE ==> fext.ready ==> fext.mem = (FUNPOW Next (THE (I (3,t)) - 1) a).MEM) /\
  (I (4,t) = NONE ==> I (3,t) = NONE ==> I (2,t) <> NONE ==> fext.ready ==> fext.mem = (FUNPOW Next (THE (I (2,t)) - 1) a).MEM) /\
  (I (4,t) = NONE ==> I (3,t) = NONE ==> I (2,t) = NONE ==> I (1,t) <> NONE ==> fext.ready ==> 
   fext.mem = (FUNPOW Next (THE (I (1,t)) - 1) a).MEM) /\
  (~fext.ready ==> ~enable_stg 1 s) /\
  (~fext.ready ==> ~enable_stg 2 s) /\
  (~s.EX.EX_jump_sel ==> reg_data_hazard s ==> ~enable_stg 2 s) /\
  (isMemOp_hw_op s ==> ~enable_stg 3 s) /\
  (I (5,t-1) <> NONE ==> s.data_out = (FUNPOW Next (THE (I (5,t-1))) a).data_out) /\
  (I (5,t-1) <> NONE ==> wb_data_vaild si ==> (s.R = (FUNPOW Next (THE (I (5,t-1))) a).R)) /\
  (I (5,t-1) = NONE ==> I (5,t) <> NONE ==> (s.R = (FUNPOW Next (THE (I (5,t)) - 1) a).R)) /\
  (I (5,t-1) = NONE ==> I (5,t) = NONE ==> I (4,t) <> NONE ==> (s.R = (FUNPOW Next (THE (I (4,t)) - 1) a).R)) /\
  (I (5,t-1) = NONE ==> I (5,t) = NONE ==> I (4,t) = NONE ==> I (3,t) <> NONE ==> 
   (s.R = (FUNPOW Next (THE (I (3,t)) - 1) a).R)) /\
  (I (5,t-1) = NONE ==> I (5,t) = NONE ==> I (4,t) = NONE ==> I (3,t) = NONE ==> I (2,t) <> NONE ==>
   (s.R = (FUNPOW Next (THE (I (2,t)) - 1) a).R)) /\
  (Inv_Rel I si s a t) /\
  (I (1,t) <> NONE ==> IF_PC_Rel s a (THE (I (1,t)))) /\
  (I (1,t) <> NONE ==> fext.ready ==> IF_instr_Rel s a (THE (I (1,t)))) /\
  (I (2,t) <> NONE ==> ID_Rel s a (THE (I (2,t)))) /\
  (I (2,t) <> NONE ==> ID_data_dep_Rel s a (I (3,t)) (I (4,t)) (I (5,t))) /\
  (I (2,t) <> NONE ==> ID_reg_data_Rel s a (THE (I (2,t))) (I (3,t)) (I (4,t)) (I (5,t))) /\
  (I (3,t) <> NONE ==> EX_Rel fext s a (THE (I (3,t)))) /\
  (EX_Rel_spec s a (I (3,t))) /\
  (I (4,t) <> NONE ==> MEM_Rel s a (THE (I (4,t)))) /\
  (I (5,t) <> NONE ==> MEM_req_rel fext si s a (THE (I (5,t)))) /\
  (I (5,t) <> NONE ==> WB_Rel fext s a (THE (I (5,t))))
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
       isJump_hw_op (sf t) ==>
       I (1,SUC t) = SOME (THE (I (3,t)) + 1)) /\
  (!t. enable_stg 1 (sf t) ==>
       ~isJump_hw_op (sf t) ==>
       (isJump_isa_op (I (1,t)) a \/ isJump_isa_op (I (2,t)) a \/ I (1,t) = NONE) ==>
       I (1,SUC t) = NONE) /\
  (!t. enable_stg 1 (sf t) ==>
       ~isJump_hw_op (sf t) ==>
       ~isJump_isa_op (I (1,t)) a ==>
       ~isJump_isa_op (I (2,t)) a ==>
       I (1,t) <> NONE ==>
       I (1,SUC t) = SOME (THE (I (1,t)) + 1))
End

Definition is_sch_decode_def:
  is_sch_decode (I:num # num -> num option) (sf:num -> state_circuit) (a:ag32_state) <=>
  (!t. enable_stg 2 (sf t) ==>
       (isJump_isa_op (I (2,t)) a \/ isJump_hw_op (sf t)) ==>
       I (2,SUC t) = NONE) /\
  (!t. enable_stg 2 (sf t) ==>
       ~isJump_isa_op (I (2,t)) a ==>
       ~isJump_hw_op (sf t) ==>
       I (2,SUC t) = I (1,t))
End

Definition is_sch_execute_def:
  is_sch_execute (I:num # num -> num option) (sf:num -> state_circuit) (a:ag32_state) <=>
  (!t. enable_stg 3 (sf t) ==>
       isJump_hw_op (sf t) ==>
       I (3,SUC t) = NONE) /\
  (!t. enable_stg 3 (sf t) ==>
       ~isJump_hw_op (sf t) ==>
       reg_data_hazard (sf t) ==>
       I (3,SUC t) = NONE) /\
  (!t. enable_stg 3 (sf t) ==>
       ~isJump_hw_op (sf t) ==>
       ~reg_data_hazard (sf t) ==>
       I (3,SUC t) = I (2,t))
End

Definition is_sch_memory_def:
  is_sch_memory (I:num # num -> num option) (sf:num -> state_circuit) (a:ag32_state) <=>
  (!t. enable_stg 4 (sf t) ==>
       isMemOp_hw_op (sf t) ==>
       I (4,SUC t) = NONE) /\
  (!t. enable_stg 4 (sf t) ==>
       ~isMemOp_hw_op (sf t) ==>
       I (4,SUC t) = I (3,t))
End

Definition is_sch_writeback_def:
  is_sch_writeback (I:num # num -> num option) (sf:num -> state_circuit) <=>
  (!t. enable_stg 5 (sf t) ==> I (5,SUC t) = I (4,t))
End

Definition is_sch_disable_def:
  is_sch_disable (I:num # num -> num option) (sf:num -> state_circuit) =
  (!t k. ~enable_stg k (sf t) ==> I (k,SUC t) = I (k,t))
End

Definition is_sch_def:
  is_sch (I:num # num -> num option) (sf:num -> state_circuit) (a:ag32_state) <=>
  is_sch_init I /\
  is_sch_fetch I sf a/\
  is_sch_decode I sf a /\
  is_sch_execute I sf a /\
  is_sch_memory I sf a /\
  is_sch_writeback I sf /\
  is_sch_disable I sf
End

val _ = export_theory ();
