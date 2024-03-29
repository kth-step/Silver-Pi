open hardwarePreamble;
(* depend on the circuit datatype *)
open agp32StateTheory;

(* external environment for the processor, based on the previous Silver work settings *)
val _ = new_theory "agp32Environment";

val _ = prefer_num ();
val _ = guess_lengths ();

val _ = Datatype `
 interrupt_state = InterruptReady | InterruptAck`;

(* External inputs, and model of relevant part of world (i.e., contents of memory) *)
val _ = Datatype `
 ext = <| data_in : word2;

          (* Memory *)
          mem : word32 -> word8;
          error : word2;
          ready : bool;
          data_rdata : word32;
          inst_rdata : word32;

          (* Mem start interface used for indication on when to start *)
          mem_start_ready : bool;
          
          (* Interrupt *)
          interrupt_state : interrupt_state;
          interrupt_ack : bool;
          io_events : (word32 -> word8) list
        |>`;


(** Memory specification **)
val mem_update_def = Define `
 mem_update mem addr wdata wstrb =
  let mem = if word_bit 0 wstrb then (addr      =+ ((7 >< 0) wdata)) mem else mem;
      mem = if word_bit 1 wstrb then (addr + 1w =+ ((15 >< 8) wdata)) mem else mem;
      mem = if word_bit 2 wstrb then (addr + 2w =+ ((23 >< 16) wdata)) mem else mem in
            if word_bit 3 wstrb then (addr + 3w =+ ((31 >< 24) wdata)) mem else mem`;

val align_addr_def = Define `
 align_addr (addr:word32) = ((31 >< 2) addr @@ (0w:word2)):word32`;

val _ = Datatype `
 fext_accessor = <|
  get_command : 'a -> word3;
  get_PC : 'a -> word32;
  get_data_addr : 'a -> word32;
  get_data_wdata : 'a -> word32;
  get_data_wstrb : 'a -> word4;

  get_interrupt_req : 'a -> bool
  |>`;

val fext_accessor_circuit_def = Define `
 fext_accessor_circuit =
  <| get_command := state_circuit_command;
     get_PC := state_circuit_PC;
     get_data_addr := state_circuit_data_addr;
     get_data_wdata := state_circuit_data_wdata;
     get_data_wstrb := state_circuit_data_wstrb;

     get_interrupt_req := state_circuit_interrupt_req |>`;

val word_at_addr_def = Define `
 word_at_addr (mem : word32 -> word8) addr =
  (mem (addr + 3w) @@ (mem (addr + 2w) @@ (mem (addr + 1w) @@ mem addr):word16):word24):word32`;

val mem_no_errors_def = Define `
 mem_no_errors fext = !n. (fext n).error = 0w`;

val is_mem_def = Define `
 is_mem accessors step fext =
  !n.
  (* Mem data semantics *)

  (* Nothing *)
  (accessors.get_command (step n) = 0w /\ (fext (n-1)).ready ==>
   (fext n).mem = (fext (n-1)).mem /\
   (fext n).inst_rdata = (fext (n-1)).inst_rdata /\
   (fext n).data_rdata = (fext (n-1)).data_rdata /\
   (fext n).ready) /\

  (* Read instruction *)
  (accessors.get_command (step n) = 1w /\ ((fext (n-1)).ready) ==>
   ?m. (!p. p < m ==> (fext (n + p)).mem = (fext (n-1)).mem /\ ~(fext (n + p)).ready) /\
       (fext (n + m)).mem = (fext (n-1)).mem /\
       (fext (n + m)).inst_rdata = word_at_addr (fext n).mem (align_addr (accessors.get_PC (step n))) /\
       (fext (n + m)).ready) /\

  (* Read instruction + read data *)
  (accessors.get_command (step n) = 2w /\ ((fext (n-1)).ready) ==>
    ?m. (!p. p < m ==> (fext (n + p)).mem = (fext (n-1)).mem /\ ~(fext (n + p)).ready) /\
        (fext (n + m)).mem = (fext (n-1)).mem /\
        (fext (n + m)).data_rdata = word_at_addr (fext n).mem (align_addr (accessors.get_data_addr (step n))) /\
        (fext (n + m)).inst_rdata = word_at_addr (fext n).mem (align_addr (accessors.get_PC (step n))) /\
        (fext (n + m)).ready) /\

  (* Read instruction + write data, note that the current unverified cache layer do not allow inst read addr and
                                    data write addr to be the same... *)
  (accessors.get_command (step n) = 3w /\ ((fext (n-1)).ready) ==>
    ?m. (!p. p < m ==> (fext (n + p)).mem = (fext (n-1)).mem /\ ~(fext (n + p)).ready) /\
        (let newmem = mem_update (fext (n-1)).mem (align_addr (accessors.get_data_addr (step n))) (accessors.get_data_wdata (step n)) (accessors.get_data_wstrb (step n)) in
         (fext (n + m)).mem = newmem /\
         (fext (n + m)).inst_rdata = word_at_addr newmem (align_addr (accessors.get_PC (step n))) /\
         (fext (n + m)).ready)) /\

 (* Clear cache block used for printing ... exactly the same semantics as "read instruction" *)
 (accessors.get_command (step n) = 4w /\ ((fext (n-1)).ready) ==>
   ?m. (!p. p < m ==> (fext (n + p)).mem = (fext (n-1)).mem /\ ~(fext (n + p)).ready) /\
       (fext (n + m)).mem = (fext (n-1)).mem /\
       (fext (n + m)).inst_rdata = word_at_addr (fext n).mem (align_addr (accessors.get_PC (step n))) /\
       (fext (n + m)).ready) /\

  mem_no_errors fext`;

val is_mem_mem_no_errors = Q.store_thm("is_mem_mem_no_errors",
 `!accs c fext. is_mem accs c fext ==> mem_no_errors fext`,
 rw [is_mem_def]);
 
(** Accelerator specification **)

val is_acc_def = Define `
 is_acc f circuit =
  ?k. !n.
   (circuit n).acc_arg_ready
   ==>
   (k <> 0 ==> ~(circuit (SUC n)).acc_res_ready) /\
   (!l. l < k /\ (!m. m <> 0 /\ m <= l ==> ~(circuit (n + m)).acc_arg_ready) ==>
        ~(circuit (SUC (n + l))).acc_res_ready) /\
   ((!m. m < k ==> ~(circuit (SUC (n + m))).acc_arg_ready /\ (circuit (SUC (n + m))).acc_arg = (circuit n).acc_arg) ==>
    (circuit (SUC (n + k))).acc_res_ready /\
    ((circuit (SUC (n + k))).acc_res = f (circuit n).acc_arg))`;

(** Start of mem interface **)

val is_mem_start_interface_def = Define `
 is_mem_start_interface fext =
  ?n. (!m. m < n ==> ~(fext m).mem_start_ready) /\ (fext n).mem_start_ready`;
  
(** Interrupt interface **)

(* This is a little difficult to model properly because the interrupt interface is async. *)
val is_interrupt_interface_def = Define `
 is_interrupt_interface accessors step fext =
  ((fext 0).interrupt_state = InterruptReady /\
   ~(fext 0).interrupt_ack /\
  !n. case (fext n).interrupt_state of
         InterruptReady =>
          if accessors.get_interrupt_req (step n) then
           ?m. (!p. p < m ==> ~(fext (SUC (n + p))).interrupt_ack /\ 
                             (fext (SUC (n + p))).interrupt_state = InterruptReady) /\
               (fext (SUC (n + m))).interrupt_state = InterruptAck /\
               (fext (SUC (n + m))).interrupt_ack
          else
           (fext (SUC n)).interrupt_state = InterruptReady /\
           ~(fext (SUC n)).interrupt_ack
       | InterruptAck =>
         (fext (SUC n)).interrupt_state = InterruptReady /\
         ~(fext (SUC n)).interrupt_ack)`;

(* data_in: keep unchanged based on the ISA *)
val is_data_in_def = Define `
 is_data_in fext =
 (!n. (fext (SUC n)).data_in = (fext n).data_in)`

(* Collection of all interfaces in the current "laboratory environment" *)
val is_lab_env_def = Define `
 is_lab_env accessors step fext <=>
  is_mem accessors step fext /\
  is_mem_start_interface fext /\
  is_interrupt_interface accessors step fext /\
  is_data_in fext`;(* Memory behavior-selection functions *)

val _ = export_theory ();
