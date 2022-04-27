open hardwarePreamble agp32StateTheory agp32EnvironmentTheory ag32Theory;

val _ = new_theory "agp32Rel";

(* Definitions of relations to prove the correctness of the pipelined Silver *)
(* relation for the initial states *)
Definition Init_Rel:
  Init_Rel (fext:ext) (s:state_circuit) (a:ag32_state) <=>
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
(** TODO **)
Definition Rel:
  Rel (fext:ext) (s:state_circuit) (a:ag32_state) <=>
  (s.state = 0w)
End

val _ = export_theory ();
