open hardwarePreamble;

val _ = new_theory "agp32State";

(** IF_state: fetch related **)
Datatype:
  IF_state = <| IF_PC_input: word32;
                IF_instr: word32;
                IF_PC_write_enable: bool
             |>
End

(** ID_state: decode related **)
Datatype:
   ID_state = <| ID_PC: word32;
                 ID_instr: word32;
                 ID_read_dataA: word32;
                 ID_read_dataB: word32;
                 ID_read_dataW: word32;
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
                 ID_addrA_disable: bool;
                 ID_addrB_disable: bool;
                 ID_addrW_disable: bool;
                 ID_addrA: word6;
                 ID_addrB: word6;
                 ID_addrW: word6;
                 ID_opc: word6;
                 ID_func: word4
              |>
End

(** EX_state: execute related **)
Datatype:
   EX_state = <| EX_PC: word32;
                 EX_dataA: word32;
                 EX_dataB: word32;
                 EX_dataW: word32;
                 EX_imm: word32;
                 EX_imm_updated: word32;
                 EX_ALU_input1: word32;
                 EX_ALU_input2: word32;
                 EX_carry_flag : bool;
                 EX_overflow_flag : bool;
                 EX_ALU_res: word32;
                 EX_SHIFT_res: word32;
                 EX_NOP_flag: bool;
                 EX_write_reg: bool;
                 EX_checkA: bool;
                 EX_checkB: bool;
                 EX_checkW: bool;
                 EX_jump_sel: bool;
                 EX_jump_addr: word32;
                 EX_addrW: word6;
                 EX_opc: word6;
                 EX_func: word4
              |>
End

(** MEM_state: memory related **)
Datatype:
   MEM_state = <| MEM_PC: word32;
                  MEM_dataA: word32;
                  MEM_dataB: word32;
                  MEM_imm: word32;               
                  MEM_ALU_res: word32;           
                  MEM_SHIFT_res: word32;                 
                  MEM_read_mem: bool;            
                  MEM_write_mem: bool;              
                  MEM_write_mem_byte: bool;                
                  MEM_write_reg: bool;
                  MEM_isAcc: bool;
                  MEM_isInterrupt: bool;          
                  MEM_state_flag: bool;
                  MEM_NOP_flag: bool;
                  MEM_checkA: bool;
                  MEM_checkB: bool;
                  MEM_checkW: bool;           
                  MEM_addrW: word6;            
                  MEM_opc: word6               
               |>
End

(** WB_state: write back related **)
Datatype:
   WB_state = <| WB_PC: word32;
                 WB_dataA: word32;
                 WB_read_data: word32;
                 WB_read_data_byte: word32;
                 WB_imm: word32;
                 WB_ALU_res: word32;
                 WB_SHIFT_res: word32;
                 WB_write_data: word32;
                 WB_write_reg: bool;
                 WB_isOut: bool;
                 WB_state_flag: bool;
                 WB_checkA: bool;
                 WB_checkB: bool;
                 WB_checkW: bool;
                 WB_data_sel: word3;
                 WB_addrW: word6;
                 WB_opc: word6
              |>
End

(* pipelined Silver CPU *)
Datatype:
  state_circuit = <| 
    (** globel state **)
    state: word3;
    PC: word32;
    R: word6 -> word32;
    data_out: word10;
    interrupt_req: bool;
    do_interrupt: bool;

    (** memory (cache) interface **)
    command: word3;
    data_addr: word32;
    data_wdata: word32;
    data_wstrb: word4;

    (** accelerator **)
    acc_arg: word32;
    acc_arg_ready: bool;
    acc_res: word32;
    acc_res_ready: bool;
    acc_state: word2;
    
    (** additional items used inside pipeline blocks **)
    ALU_sum: 33 word;
    ALU_prod: word64;
    ALU_sub: word32;
    shift_sh: word32;

    (** pipeline **)
    IF: IF_state;
    ID: ID_state;
    EX: EX_state;
    MEM: MEM_state;
    WB: WB_state
  |>
End

val _ = export_theory ();
