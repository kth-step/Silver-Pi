open hardwarePreamble agp32StateTheory agp32EnvironmentTheory ag32Theory ag32ExtraTheory;

val _ = new_theory "agp32Relation";

(** general variables used in this file:
    k: pipeline stage.
    t: cycle for the hw.
    i: cycle (instr index) for the ISA.
 **)

val _ = guess_lengths ();

(* Additional definitions for the pipeline correctness proofs *)
(* enable_stg: stage k is enabled in the hardware circuit *)
Definition enable_stg:
  enable_stg k s =
  if k = IF then s.IF.IF_PC_write_enable
  else if k = ID then s.ID.ID_ID_write_enable
  else if k = EX then s.ID.ID_EX_write_enable
  else if k = MEM then (s.EX.EX_write_enable /\ s.MEM.MEM_state_flag) \/ s.MEM.MEM_enable
  else (s.MEM.MEM_write_enable /\ s.WB.WB_state_flag) \/ s.WB.WB_enable
End


(* Definitions of relations to prove the correctness of the pipelined Silver *)
(* relation for the initial states *)
Definition Init:
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
  (s.IF.IF_instr = 0x3Fw) /\
  (s.ID.ID_instr = 0x3Fw) /\
  (s.EX.EX_PC_sel = 0w) /\
  ~s.EX.EX_jump_sel /\
  (s.EX.EX_opc = 15w) /\
  (s.MEM.MEM_opc = 15w) /\
  ~s.MEM.MEM_enable /\
  ~s.MEM.MEM_write_reg /\
  ~s.WB.WB_enable /\
  ~s.WB.WB_write_reg
End

(* relation between the pipelined Silver circuit and ISA state *)
Definition Rel:
  Rel (fext:ext) (s:state_circuit) (a:ag32_state) (k:pi_stg) (i:num) <=>
  (fext.data_in = a.data_in) /\
  (** visible part: directly seen by ISA **)
  (** no visible registers in IF and ID **)
  (k = EX ==>
   (s.EX.EX_carry_flag <=> (FUNPOW Next i a).CarryFlag) /\
   (s.EX.EX_overflow_flag <=> (FUNPOW Next i a).OverflowFlag) /\
   (s.PC = (FUNPOW Next i a).PC)) /\
  (k = MEM ==>
   fext.mem = (FUNPOW Next i a).MEM) /\
  (k = WB ==>
   (s.data_out = (FUNPOW Next i a).data_out) /\
   (s.R = (FUNPOW Next i a).R)) /\
  (** invisible part **)
  (k = IF ==>
   (s.IF.IF_instr = instr (FUNPOW Next i a))) /\
  (k = ID ==>
   (s.ID.ID_PC = (FUNPOW Next (i-1) a).PC) /\
   (s.ID.ID_instr = instr (FUNPOW Next i a)) /\
   (** to correct **)
   (s.ID.ID_addrA = addrA (FUNPOW Next i a)) /\
   (s.ID.ID_addrB = addrB (FUNPOW Next i a)) /\
   (s.ID.ID_addrW = addrW (FUNPOW Next i a)) /\
   (s.ID.ID_addrA_disable <=> flagA (FUNPOW Next i a)) /\
   (s.ID.ID_addrB_disable <=> flagB (FUNPOW Next i a)) /\
   (s.ID.ID_addrW_disable <=> flagW (FUNPOW Next i a)) /\
   (s.ID.ID_read_dataA_updated = reg_dataA (FUNPOW Next i a)) /\
   (s.ID.ID_read_dataB_updated = reg_dataB (FUNPOW Next i a)) /\
   (s.ID.ID_read_dataW_updated = reg_dataW (FUNPOW Next i a)) /\
   (s.ID.ID_immA = immA (FUNPOW Next i a)) /\
   (s.ID.ID_immB = immB (FUNPOW Next i a)) /\
   (s.ID.ID_immW = immW (FUNPOW Next i a)) /\
   (s.ID.ID_dataA = dataA (FUNPOW Next i a)) /\
   (s.ID.ID_dataB = dataB (FUNPOW Next i a)) /\
   (s.ID.ID_dataW = dataW (FUNPOW Next i a)) /\
   (s.ID.ID_imm = imm (FUNPOW Next i a)) /\
   (s.ID.ID_opc = opc (FUNPOW Next i a)) /\
   (s.ID.ID_func = func (FUNPOW Next i a))) /\
  (k = EX ==>
   (s.EX.EX_jump_sel ==> s.IF.IF_PC_input = (FUNPOW Next i a).PC) /\
   (~s.EX.EX_jump_sel ==> s.IF.IF_PC_input = (FUNPOW Next i a).PC + 8w) /\
   (s.EX.EX_PC = (FUNPOW Next (i-1) a).PC) /\
   (s.EX.EX_addrA = addrA (FUNPOW Next i a)) /\
   (s.EX.EX_addrB = addrB (FUNPOW Next i a)) /\
   (s.EX.EX_addrW = addrW (FUNPOW Next i a)) /\
   (s.EX.EX_addrA_disable <=> flagA (FUNPOW Next i a)) /\
   (s.EX.EX_addrB_disable <=> flagB (FUNPOW Next i a)) /\
   (s.EX.EX_addrW_disable <=> flagW (FUNPOW Next i a)) /\
   (s.EX.EX_dataA_updated = dataA (FUNPOW Next i a)) /\
   (s.EX.EX_dataB_updated = dataB (FUNPOW Next i a)) /\
   (s.EX.EX_dataW_updated = dataW (FUNPOW Next i a)) /\
   (s.EX.EX_dataA_rec = dataA (FUNPOW Next i a)) /\
   (s.EX.EX_dataB_rec = dataB (FUNPOW Next i a)) /\
   (s.EX.EX_dataW_rec = dataW (FUNPOW Next i a)) /\
   (s.EX.EX_imm = imm (FUNPOW Next i a)) /\
   (s.EX.EX_ALU_res = ALU_res (FUNPOW Next i a)) /\
   (s.EX.EX_SHIFT_res = shift_res (FUNPOW Next i a)) /\
   (s.EX.EX_jump_sel ==> s.EX.EX_jump_addr = (FUNPOW Next i a).PC) /\
   (s.EX.EX_opc = opc (FUNPOW Next i a)) /\
   (s.EX.EX_func = func (FUNPOW Next i a))) /\
  (k = MEM ==>
   (s.MEM.MEM_PC = (FUNPOW Next (i-1) a).PC) /\
   (s.MEM.MEM_addrW = addrW (FUNPOW Next i a)) /\
   (s.MEM.MEM_dataA = dataA (FUNPOW Next i a)) /\
   (s.MEM.MEM_dataB = dataB (FUNPOW Next i a)) /\
   (s.MEM.MEM_dataW = dataW (FUNPOW Next i a)) /\
   (s.MEM.MEM_imm = imm (FUNPOW Next i a)) /\
   (s.MEM.MEM_imm_updated =
    ((8 >< 0) (imm (FUNPOW Next i a))) @@ ((22 >< 0) (dataW (FUNPOW Next i a)))) /\
   (s.MEM.MEM_ALU_res = ALU_res (FUNPOW Next i a)) /\
   (s.MEM.MEM_SHIFT_res = shift_res (FUNPOW Next i a)) /\
   (s.MEM.MEM_write_reg <=> reg_ifwrite (FUNPOW Next i a)) /\
   (s.MEM.MEM_opc = opc (FUNPOW Next i a)) /\
   (s.data_addr = mem_data_addr (FUNPOW Next i a)) /\
   (s.data_wstrb = mem_data_wstrb (FUNPOW Next i a)) /\
   (s.data_wdata = mem_data_wdata (FUNPOW Next i a)) /\
   (fext.data_rdata = mem_data_rdata (FUNPOW Next i a))) /\
  (k = WB ==>
   (s.WB.WB_PC = (FUNPOW Next (i-1) a).PC) /\
   (s.WB.WB_addrW = addrW (FUNPOW Next i a)) /\
   (s.WB.WB_dataA = dataA (FUNPOW Next i a)) /\
   (s.WB.WB_opc = 14w ==> s.WB.WB_imm =
                          ((8 >< 0) (imm (FUNPOW Next i a))) @@ ((22 >< 0) (dataW (FUNPOW Next i a)))) /\
   (s.WB.WB_opc <> 14w ==> s.WB.WB_imm = imm (FUNPOW Next i a)) /\
   (s.WB.WB_ALU_res = ALU_res (FUNPOW Next i a)) /\
   (s.WB.WB_SHIFT_res = shift_res (FUNPOW Next i a)) /\
   (s.WB.WB_write_reg = reg_ifwrite (FUNPOW Next i a)) /\
   (s.WB.WB_opc = opc (FUNPOW Next i a)) /\
   (s.WB.WB_write_data = reg_wdata (FUNPOW Next i a)))
End

val _ = export_theory ();
