open hardwarePreamble translatorTheory translatorCoreLib;

val _ = new_theory "agp32Processor";

val _ = prefer_num ();
val _ = guess_lengths ();

val _ = Datatype `
   IF_state = <| (** fetch related **)
                 IF_PC_input: word32;
                 IF_PC_output: word32;
                 IF_instr: word32;
                 IF_PC_write_enable: bool;
                 PC_sel: word2 
               |>`;

val _ = Datatype `
   ID_state = <| (** decode related **)
                 ID_PC: word32;
                 ID_instr: word32;
                 ID_read_dataA: word32;
                 ID_read_dataB: word32;
                 ID_read_dataW: word32;
                 ID_read_dataA_updated: word32;
                 ID_read_dataB_updated: word32;
                 ID_read_dataW_updated: word32;
                 ID_immA: word32;
                 ID_immB: word32;
                 ID_immW: word32;
                 ID_imm: word32;
                 ID_dataA: word32;
                 ID_dataB: word32;
                 ID_dataW: word32;
                 ID_ID_write_enable: bool;
                 ID_EX_write_enable: bool;
                 ID_flush_flag: bool;
                 ID_addrA_enable: bool;
                 ID_addrB_enable: bool;
                 ID_addrW_enable: bool;
                 ID_ForwardA: bool;
                 ID_ForwardB: bool;
                 ID_ForwardW: bool;
                 ID_addrA: word6;
                 ID_addrB: word6;
                 ID_addrW: word6;
                 ID_opc: word6;
                 ID_func: word4
               |>`;

val _ = Datatype `
   EX_state = <| (** execute related **)
                 EX_PC: word32;
                 EX_dataA: word32;
                 EX_dataB: word32;
                 EX_dataW: word32;
                 EX_dataA_updated: word32;
                 EX_dataB_updated: word32;
                 EX_dataW_updated: word32;
                 EX_dataA_rec: word32;
                 EX_dataB_rec: word32;
                 EX_dataW_rec: word32;
                 EX_imm: word32;
                 EX_ALU_input1: word32;
                 EX_ALU_input2: word32;
                 EX_ALU_res: word32;
                 EX_SHIFT_res: word32;
                 EX_write_enable: bool;
                 EX_addrA_enable: bool;
                 EX_addrB_enable: bool;
                 EX_addrW_enable: bool;
                 EX_isAcc: bool;
                 EX_NOP_flag: bool;
                 (* EX_compute_enable: bool; *)
                 EX_PC_sel: word2;
                 EX_ForwardA: word3;
                 EX_ForwardB: word3;
                 EX_ForwardW: word3;
                 EX_addrA: word6;
                 EX_addrB: word6;
                 EX_addrW: word6;
                 EX_opc: word6;
                 EX_func: word4
               |>`;

val _ = Datatype `
   MEM_state = <| (** memory related **)
                 MEM_PC: word32;
                 MEM_dataA: word32;
                 MEM_dataB: word32;
                 MEM_dataW: word32;
                 MEM_imm: word32;
                 MEM_imm_updated: word32;
                 MEM_ALU_res: word32;
                 MEM_SHIFT_res: word32;
                 MEM_write_enable: bool;
                 MEM_read_mem: bool;
                 MEM_write_mem: bool;
                 MEM_write_mem_byte: bool;
                 MEM_write_reg: bool;
                 MEM_isInterrupt: bool;
                 MEM_state_flag: bool;
                 MEM_NOP_flag: bool;
                 MEM_enable: bool;
                 MEM_addrW: word6;
                 MEM_opc: word6 
               |>`;

val _ = Datatype `
   WB_state = <| (** write back related **)
                 WB_PC: word32;
                 WB_dataA: word32;
                 WB_read_data: word32;
                 WB_read_data_byte: word32;
                 WB_imm: word32;
                 WB_ALU_res: word32;
                 WB_SHIFT_res: word32;
                 WB_write_data: word32;
                 WB_write_enable: bool;
                 WB_write_reg: bool;
                 WB_isOut: bool;
                 WB_state_flag: bool;
                 WB_enable: bool;
                 WB_data_sel: word3;
                 WB_addrW: word6;
                 WB_opc: word6
               |>`;

val _ = Datatype `
state_circuit = <|(* pipelined Silver CPU *)

                 (** globel state **)
                 state: word3;
                 PC: word32;
                 (* R: word6 -> word32; *)
                 data_out: word10;
                 data_in: word2;
                 acc_arg: word32;
                 acc_arg_ready: bool;
                 interrupt_req: bool;
                 do_interrupt: bool;

                 (** data memory interface **)
                 command: word3;
                 data_addr: word32;
                 data_wdata: word32;
                 data_wstrb: word4;

                 (** accelerator **)
                 acc_res: word32;
                 acc_res_ready: bool;
                 acc_state: word2;

                 (** piepeline **)
                 IF: IF_state;
                 ID: ID_state;
                 EX: EX_state;
                 MEM: MEM_state;
                 WB: WB_state 
               |>`;

val _ = export_theory ();