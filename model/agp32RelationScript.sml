open hardwarePreamble agp32StateTheory agp32EnvironmentTheory ag32Theory;

val _ = new_theory "agp32Relation";

(** general variables used in this file:
    k: pipeline stage.
    t: cycle for the hw.
    i: cycle (instr index) for the ISA.
 **)

val _ = prefer_num ();


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
  (** visible registers: s.R = (FUNPOW Next i a).R **)
  (** no visible registers in IF and ID **)
  (k = EX ==>
   (s.EX.EX_carry_flag <=> (FUNPOW Next i a).CarryFlag) /\
   (s.EX.EX_overflow_flag <=> (FUNPOW Next i a).OverflowFlag) /\
   (s.PC = (FUNPOW Next i a).PC)) /\
  (k = MEM ==>
   fext.mem = (FUNPOW Next i a).MEM) /\
  (k = WB ==>
   (s.data_out = (FUNPOW Next i a).data_out) /\
   (s.R = (FUNPOW Next i a).R))
  (** invisible **)
End

val _ = export_theory ();
