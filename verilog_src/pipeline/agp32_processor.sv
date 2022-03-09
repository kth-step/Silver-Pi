/* 5-stage pipelined 32-bit Silver processor, Ning Dong.
   Ref: single-cycle Silver processor, Andreas Lööw. 

   IF: instruction feach.
   ID: instruction deceode.
   EX: execution (mainly ALU and shift).
   MEM: memory operations (load and store).
   WB: write results back to registers.
*/

`timescale 1ns / 1ps
`define WORD_SIZE 32
`define WORD_SIZE_INDEX 31

// MUX: multiplexer
module MUX_21 (input0,input1,sel,output0);
    input [`WORD_SIZE_INDEX:0] input0,input1;
    input sel;

    output [`WORD_SIZE_INDEX:0] output0;
    
    assign output0 = (sel == 0 ? input0 : input1);
endmodule

module MUX_41 (input0,input1,input2,input3,sel,output0);
    input [`WORD_SIZE_INDEX:0] input0,input1,input2,input3;
    input [1:0] sel;

    output [`WORD_SIZE_INDEX:0] output0;

    // select input0/1/2/3 when sel == 0/1/2/3
    assign output0 = (sel == 0 ? input0 :
                     (sel == 1 ? input1 :
                     (sel == 2 ? input2 : input3)));
endmodule

module MUX_81 (input0,input1,input2,input3,input4,input5,input6,input7,sel,output0);
    input [`WORD_SIZE_INDEX:0] input0,input1,input2,input3,input4,input5,input6,input7;
    input [2:0] sel;

    output [`WORD_SIZE_INDEX:0] output0;

    assign output0 = (sel == 0 ? input0 :
                     (sel == 1 ? input1 :
                     (sel == 2 ? input2 :
                     (sel == 3 ? input3 :
                     (sel == 4 ? input4 :
                     (sel == 5 ? input5 :
                     (sel == 6 ? input6 : input7)))))));  
endmodule

// ALU: arithmetic logic unit
module ALU_Unit (write_enable,func,input1,input2,alu_res);
    input write_enable;
    input [3:0] func;
    input [`WORD_SIZE_INDEX:0] input1,input2;
    output logic [`WORD_SIZE_INDEX:0] alu_res;
    
    logic CarryFlag,OverflowFlag;
    logic [`WORD_SIZE:0] alu_sum;
    logic [`WORD_SIZE_INDEX:0] alu_sub;
    logic [63:0] alu_prod;

    always_comb begin
        if (write_enable) begin 
            alu_sum = (33'({input1}) + 33'({input2})) + ((func == 4'd1) ? 33'({CarryFlag}) : 33'd0);
            alu_prod = 64'({input1}) * 64'({input2}); 
            case (func)
            //fAdd
            4'd0: begin
               alu_res = alu_sum[31:0];
               CarryFlag = alu_sum[32];
               OverflowFlag = (input1[31] == input2[31]) && (alu_sum[31] != input1[31]);
            end
            //fAddWithCarry
            4'd1: begin
               alu_res = alu_sum[31:0];
               CarryFlag = alu_sum[32];
            end
            //fSub
            4'd2: begin
               alu_sub = input1 - input2;
               OverflowFlag = (input1[31] != input2[31]) && (alu_sub[31] != input1[31]);
               alu_res = alu_sub;
            end
            //fCarry
            4'd3: begin
                alu_res = 32'({CarryFlag});
            end
            //fOverflow
            4'd4: begin
                alu_res = 32'({OverflowFlag});
            end
            //fInc
            4'd5: begin
                alu_res = input1 + 32'd1;
            end
            //fDec
            4'd6: begin
                alu_res = input1 - 32'd1;
            end
            //fMul
            4'd7: begin
                alu_res = alu_prod[31:0];
            end
            //fMulHU
            4'd8: begin
                alu_res = alu_prod[63:32];
            end
            //fAnd
            4'd9: begin
                alu_res = input1 & input2;
            end
            //fOr
            4'd10: begin
                alu_res = input1 | input2;
            end
            //fXor
            4'd11: begin
                alu_res = input1 ^ input2;
            end
            //fEqual
            4'd12: begin
                alu_res = 32'({input1 == input2});
            end
            //fLess
            4'd13: begin
                alu_res = 32'({{$signed(input1) < $signed(input2)}});
            end
            //fLower
            4'd14: begin
                alu_res = 32'({input1 < input2});
            end
            //fSnd
            4'd15: begin
                alu_res = input2;
            end
            endcase
        end
    end  
endmodule

// Shift instruction.
module SHIFT_Unit (write_enable,func,input_aV,input_bV,shift_res);
    input write_enable;
    input [3:0] func;
    input [`WORD_SIZE_INDEX:0] input_aV,input_bV;

    output logic [`WORD_SIZE_INDEX:0] shift_res;

    logic [`WORD_SIZE_INDEX:0] shift_sh;

    always_comb begin
        if (write_enable) begin
            case (func[1:0])
            2'd0: begin
                shift_res = input_aV << input_bV; //shiftLL
            end
            2'd1: begin
                shift_res = input_aV >> input_bV; //shiftLR
            end
            2'd2: begin
                shift_res = {$signed(input_aV) >>> (input_bV)}; //shiftAR
            end
            2'd3: begin
                shift_sh = input_bV % 32'd32;
                shift_res = (input_aV >> shift_sh) | (input_aV << (32'd32 - shift_sh)); //shiftRor
            end
            endcase
        end
    end
endmodule

// PC: program counter.
module PC_Unit (clk,PC_input,PC_output,write_enable);
    input clk,write_enable;
    input [`WORD_SIZE_INDEX:0] PC_input;

    output logic [`WORD_SIZE_INDEX:0] PC_output = 0;

    always_ff @(posedge clk) begin
        if (write_enable)
           PC_output = PC_input; 
    end 
endmodule

// SetUp_Opc: set up the correct instruction (opc).
module SetUp_Opc (instr,opc);
    input [`WORD_SIZE_INDEX:0] instr;
    
    output logic [5:0] opc;

    always_comb begin 
        if (instr[24]) begin 
            if (instr[31]) 
            opc = 6'd13; //LoadConstant 
            else begin 
                if (instr[23:9] == 15'd0) 
                opc = 6'd14; //LoadUpperConstant 
                else 
                opc = 6'd15; //Invalid instruction 
            end 
        end 
        
        else begin 
            if ((instr[5:0] == 6'd10) || ((instr[5:0] == 6'd11) || (instr[5:0] == 6'd12))) 
            opc = instr[5:0];
            else begin 
                if (instr[31]) 
                opc = 6'd15;
                else begin 
                    if (instr[5:0] < 6'd10) 
                    opc = instr[5:0];
                    else
                    opc = 6'd15;
                end 
            end 
        end
    end
endmodule

// Record the value of register data.
module Data_Record (state,mem_opc,forwarda,forwardb,forwardd,input_aV,input_bV,input_dV,output_aV,output_bV,output_dV);
    input [2:0] state,forwarda,forwardb,forwardd;
    input [5:0] mem_opc;
    input [`WORD_SIZE_INDEX:0] input_aV,input_bV,input_dV;
    output logic [`WORD_SIZE_INDEX:0] output_aV,output_bV,output_dV;
    
    always_comb begin
       if (state == 3'd0 && mem_opc != 6'd16) begin
          output_aV = input_aV;
          output_bV = input_bV;
          output_dV = input_dV;
       end
       else if (state == 3'd0 && mem_opc == 6'd16) begin
          if (forwarda != 0) output_aV = input_aV;
          if (forwardb != 0) output_bV = input_bV;
          if (forwardd != 0) output_dV = input_dV;
       end
    end
endmodule

// Register unit in the decode stage
module REG_Unit (clk,addressA,addressB,rd_addressD,wr_addressD,DataA,DataB,input_DataD,output_DataD,regWrite);
    input clk,regWrite;
    input [5:0] addressA,addressB,rd_addressD,wr_addressD;
    input [`WORD_SIZE_INDEX:0] input_DataD;

    output logic [`WORD_SIZE_INDEX:0] DataA,DataB,output_DataD;

    logic [63:0] [`WORD_SIZE_INDEX:0] R = 0;

    assign DataA = R[addressA];
    assign DataB = R[addressB];
    assign output_DataD = R[rd_addressD];
    
    always_ff @(posedge clk) begin
        if (regWrite) begin
            R[wr_addressD] = input_DataD;
        end
    end
endmodule

// Generate immediate for aV, bV, dV and special instructions.
module Imm_Sel (instr,imm,imm_aV,imm_bV,imm_dV);
    input [`WORD_SIZE_INDEX:0] instr;
    output logic [`WORD_SIZE_INDEX:0] imm,imm_aV,imm_bV,imm_dV;

    always_comb begin
        // set up general imm for LoadUpperConstant and LoadConstant
        // LoadConstant
        if (instr[31] == 1 && instr[24] == 1) begin
            if (instr[23]) begin
                imm[31:0] = 32'd0 - 32'({instr[22:0]});
            end
            else begin
                imm[31:0] = 32'({instr[22:0]});
            end
        end
        // LoadUpperConstant
        else if (instr[24] == 1 && instr[23:9] == 15'd0) begin
            imm[31:0] = 32'({instr[8:0]});
        end
        else begin
            imm[31:0] = 0;
        end

        // set up Imm(aV)
        imm_aV[31:0] = {32'($signed(instr[22:17]))}; 

        // set up Imm(bV)
        imm_bV[31:0] = {32'($signed(instr[15:10]))};

        // set up Imm(dV)
        imm_dV[31:0] = {32'($signed(instr[30:25]))};
    end
endmodule

// set up necessary flags for the corresponding stage.
module EX_Ctrl_Unit (opc,isAcc_flag,MemRead,write_enable);
       input [5:0] opc;
       input write_enable;

       output logic isAcc_flag,MemRead;

       always_comb begin
           if (write_enable) begin
               MemRead = (opc == 6'd4 || opc == 6'd5);
               isAcc_flag = (opc == 6'd8);
           end 
       end
endmodule


module MEM_SetUp (opc,interrupt_flag,write_mem,write_mem_byte,write_reg,write_enable);
    input [5:0] opc;
    input write_enable;

    output logic interrupt_flag,write_mem,write_mem_byte,write_reg;

    always_comb begin
        if (write_enable) begin
            write_mem = (opc == 6'd2); // StoreMem
            write_mem_byte = (opc == 6'd3); // StoreMemByte
            write_reg = (opc == 6'd0 || opc == 6'd1 || opc == 6'd4 || opc == 6'd5 || opc == 6'd6 || opc == 6'd7 || opc == 6'd8 || opc == 6'd9 || opc == 6'd13 || opc == 6'd14);
            interrupt_flag = (opc == 6'd12);        
        end     
    end
endmodule

module WB_Setup (opc,data_sel,isOut_flag,write_enable);
    input [5:0] opc;
    input write_enable;

    output logic [2:0] data_sel;
    output logic isOut_flag;

    always_comb begin
        if (write_enable) begin
            if (opc == 6'd0 || opc == 6'd6)
                data_sel = 3'd0; // Normal and Out, choose ALU_res
            else if (opc == 6'd1)
                data_sel = 3'd1; //Shift, shift_res
            else if (opc == 6'd7)
                data_sel = 3'd2; //In, data_in
            else if (opc == 6'd9) 
                data_sel = 3'd3; //Jump, PC+4w
            else if (opc == 6'd13 || opc == 6'd14)
                data_sel = 3'd4; //LoadConstant and LoadUpperConstant, imm
            else if (opc == 6'd4) 
                data_sel = 3'd5; //LoadMEM, read_data
            else if (opc == 6'd5)  
                data_sel = 3'd6; //LoadMEMByte, read_data_byte
            else if (opc == 6'd8)
                data_sel = 3'd7; //Accelerator, acc_res
            else
                data_sel = 3'd0; //Default

            isOut_flag = (opc == 6'd6);
        end
    end
endmodule

/* X_Pipeline: pass over arguments from one stage to the next stage.
   Com_Pipeline: used for several stages to copy some commun arguments like PC, opc, etc.
*/
module Com_Pipeline (clk,input_PC,input_opc,input_addressD,input_dataA,input_imm,input_write_enable,input_nop_flag,
                     output_PC,output_opc,output_addressD,output_dataA,output_imm,output_write_enable);
        input clk,input_write_enable,input_nop_flag;
        input [5:0] input_opc;
        input [5:0] input_addressD;
        input [`WORD_SIZE_INDEX:0] input_PC,input_dataA,input_imm;

        output logic output_write_enable;
        output logic [5:0] output_opc;
        output logic [5:0] output_addressD;
        output logic [`WORD_SIZE_INDEX:0] output_PC,output_dataA,output_imm;

        always_ff @(posedge clk) begin
            output_write_enable = input_write_enable;
        
            if (input_write_enable) begin 
                output_PC = input_PC;
                output_opc = input_opc;
                output_addressD = input_addressD;
                output_dataA = input_dataA;
                output_imm = input_imm;
            end
            
            if (input_nop_flag) begin
                output_opc = 6'd16;
            end
        end
endmodule

module ID_Pipeline (clk,input_instr,input_PC,output_instr,output_PC,write_enable,flush_flag);
    input clk;
    input [`WORD_SIZE_INDEX:0] input_instr,input_PC;
    input write_enable,flush_flag;

    output logic [`WORD_SIZE_INDEX:0] output_instr = 32'h0000003F,output_PC = 0;

    always_ff @(posedge clk) begin
        if (write_enable) begin
            output_instr = input_instr;
            output_PC = input_PC;
        end

        if (flush_flag) begin
            output_instr = 32'h0000003F; // an invalid instruction
        end   
    end
endmodule

module EX_Pipeline (clk,input_PC,input_opc,input_func,input_addressA,input_addressB,input_addressD,input_imm,input_readdataA,
                    input_readdataB,input_dataD,input_en_addra,input_en_addrb,input_en_addrw,input_write_enable,input_nop_flag,
                    isAcc_flag,MemRead,output_PC,output_opc,output_func,output_addressA,output_addressB,output_addressD,output_imm,output_readdataA,
                    output_readdataB,output_dataD,output_PC_sel,output_en_addra,output_en_addrb,output_en_addrw,output_write_enable);
        input clk,input_en_addra,input_en_addrb,input_en_addrw,input_write_enable,input_nop_flag;
        input [5:0] input_opc;
        input [3:0] input_func;
        input [5:0] input_addressA,input_addressB,input_addressD;
        input [`WORD_SIZE_INDEX:0] input_PC,input_imm,input_readdataA,input_readdataB,input_dataD;

        output logic isAcc_flag,MemRead,output_en_addra,output_en_addrb,output_en_addrw,output_write_enable;
        output logic [5:0] output_opc;
        output logic [3:0] output_func;
        output logic [5:0] output_addressA,output_addressB,output_addressD;
        output logic [`WORD_SIZE_INDEX:0] output_PC,output_readdataA,output_readdataB,output_dataD,output_imm;
        output logic [1:0] output_PC_sel = 0;

        Com_Pipeline com_pipeline_ex(clk,input_PC,input_opc,input_addressD,input_readdataA,input_imm,input_write_enable,input_nop_flag,
                                     output_PC,output_opc,output_addressD,output_readdataA,output_imm,output_write_enable);
        EX_Ctrl_Unit EX_Ctrl(output_opc,isAcc_flag,MemRead,input_write_enable);

        always_ff @(posedge clk) begin
            if (input_write_enable) begin 
                output_addressA = input_addressA;
                output_addressB = input_addressB; 
                output_readdataB = input_readdataB;
                output_dataD = input_dataD;
                output_func = input_func;
                output_en_addra = input_en_addra;
                output_en_addrb = input_en_addrb;
                output_en_addrw = input_en_addrw;
                output_PC_sel = (input_opc == 6'd9 ? 2'b01 : //Jump
                                 (input_opc == 6'd10 ? 2'b10 : //JumpIfZero
                                 (input_opc == 6'd11 ? 2'b11 : 2'b00))); //JumpIfNotZero : Normal case
            end
        end
endmodule

module MEM_Pipeline (clk,input_PC,input_opc,input_addressD,input_imm,input_ALUres,input_shift_res,input_readdataA,
                     input_readdataB,input_readdataD,input_rd_mem,input_write_enable,input_nop_flag,
                     output_rd_mem,output_interrupt_flag,output_wr_mem,output_wr_mem_byte,output_wr_reg,output_PC,output_opc,output_addressD,
                     output_imm,output_ALUres,output_shift_res,output_readdataA,output_readdataB,output_readdataD,output_write_enable);
    input clk,input_rd_mem,input_write_enable,input_nop_flag;
    input [5:0] input_opc;
    input [5:0] input_addressD;
    input [`WORD_SIZE_INDEX:0] input_PC,input_imm,input_readdataA,input_readdataB,input_readdataD,input_ALUres,input_shift_res;

    output logic output_rd_mem = 0, output_interrupt_flag, output_wr_mem, output_wr_mem_byte, output_wr_reg, output_write_enable;
    output logic [5:0] output_opc;
    output logic [5:0] output_addressD;
    output logic [`WORD_SIZE_INDEX:0] output_PC,output_imm,output_ALUres,output_shift_res,output_readdataA,output_readdataB,output_readdataD;


    Com_Pipeline com_pipeline_mem(clk,input_PC,input_opc,input_addressD,input_readdataA,input_imm,input_write_enable,input_nop_flag,
                                  output_PC,output_opc,output_addressD,output_readdataA,output_imm,output_write_enable);
    MEM_SetUp mem_setup(output_opc,output_interrupt_flag,output_wr_mem,output_wr_mem_byte,output_wr_reg,input_write_enable);

    always_ff @(posedge clk) begin
        if (input_write_enable) begin   
            output_ALUres = input_ALUres;
            output_shift_res = input_shift_res;
            output_readdataB = input_readdataB;
            output_readdataD = input_readdataD;
            output_rd_mem = input_rd_mem;
        end
    end 
endmodule

module WB_Pipeline (clk,input_PC,input_opc,input_addressD,input_imm,input_ALUres,input_shift_res,input_readdataA,input_wr_reg,input_write_enable,
                    data_sel,wr_reg_flag,isOut,output_PC,output_opc,output_addressD,output_imm,output_ALUres,output_shift_res,output_readdataA,output_write_enable);

    input clk,input_wr_reg,input_write_enable;
    input [5:0] input_opc;
    input [5:0] input_addressD;
    input [`WORD_SIZE_INDEX:0] input_PC,input_imm,input_readdataA,input_ALUres,input_shift_res;
    
    output [2:0] data_sel;
    output logic wr_reg_flag = 0,isOut,output_write_enable;
    output [5:0] output_opc;
    output [5:0] output_addressD;
    output logic [`WORD_SIZE_INDEX:0] output_PC,output_imm,output_readdataA,output_ALUres,output_shift_res;

    Com_Pipeline com_pipeline_wb(clk,input_PC,input_opc,input_addressD,input_readdataA,input_imm,input_write_enable,0,
                                 output_PC,output_opc,output_addressD,output_readdataA,output_imm,output_write_enable);
    WB_Setup wb_setup(output_opc,data_sel,isOut,input_write_enable);

    always_ff @(posedge clk) begin
        if (input_write_enable) begin
            output_imm = input_imm;
            output_ALUres = input_ALUres;
            output_shift_res = input_shift_res;
            wr_reg_flag = input_wr_reg;
        end
    end
endmodule

// handle hazards
module Hazard_Ctrl_Unit (hit_flag,MEM_opc,state,PC_wr_flag,ID_wr_flag,ID_flush_flag,EX_wr_flag,EX_NOP_flag,MEM_flag,MEM_NOP_flag,WB_flag,PCSel);
    input [5:0] MEM_opc;
    input hit_flag;
    input [1:0] PCSel;
    input [2:0] state;

    output logic PC_wr_flag,ID_wr_flag,ID_flush_flag ,EX_wr_flag,EX_NOP_flag,MEM_flag,MEM_NOP_flag,WB_flag;

    always_comb begin
        if (state == 3'd5 || state == 3'd3)  // special states
        begin
            PC_wr_flag = 0;
            ID_wr_flag = 0;
            ID_flush_flag = 1;
            EX_wr_flag = 0;
            EX_NOP_flag = 0;
            MEM_flag = 0;
            MEM_NOP_flag = 0;
            WB_flag = 0;
        end
        
        else if (state == 3'd2 || state == 3'd4 || state == 3'd6 || state == 3'd7) begin // stalling states
            PC_wr_flag = 0;
            ID_wr_flag = 0;
            ID_flush_flag = 0;
            EX_wr_flag = 0;
            EX_NOP_flag = 0;
            MEM_flag = 0;
            MEM_NOP_flag = 0;
            WB_flag = 0;
        end
        
        else if (state == 3'd1) begin  // fetching new instr state
            PC_wr_flag = 0;
            ID_wr_flag = 0;
            ID_flush_flag = 0;
            EX_wr_flag = 0;
            EX_NOP_flag = 0;
            MEM_flag = 1;
            MEM_NOP_flag = 0;
            WB_flag = 1;
        end

        //special cases when state == 0
        else if (hit_flag == 0) begin // cache miss
            PC_wr_flag = 0;
            ID_wr_flag = 0;
            ID_flush_flag = 0;
            EX_wr_flag = 0;
            EX_NOP_flag = 0;
            MEM_flag = 0;
            MEM_NOP_flag = 0;
            WB_flag = 0;
        end     
        
        else if (MEM_opc == 6'd2 || MEM_opc == 6'd3  || MEM_opc == 6'd4 || MEM_opc == 6'd5 || MEM_opc == 6'd12) begin // stalling for memory instructions
            PC_wr_flag = 0;
            ID_wr_flag = 0;
            ID_flush_flag = 0;
            EX_wr_flag = 0;
            EX_NOP_flag = 0;
            MEM_flag = 0;
            MEM_NOP_flag = 1;
            WB_flag = 1;
        end
        
        else if (PCSel != 0) begin // jump
            PC_wr_flag = 1;
            ID_wr_flag = 0;
            ID_flush_flag = 1;
            EX_wr_flag = 1;
            EX_NOP_flag = 1;
            MEM_flag = 1;
            MEM_NOP_flag = 0;
            WB_flag = 1;
        end
        
        else begin  //normal case
            PC_wr_flag = 1;
            ID_wr_flag = 1;
            ID_flush_flag = 0;
            EX_wr_flag = 1;
            EX_NOP_flag = 0;
            MEM_flag = 1;
            MEM_NOP_flag = 0;
            WB_flag = 1;
        end 
    end
endmodule

// forward control unit
module Forward_Ctrl_Unit (EX_addrA,EX_addrB,EX_addrW,EX_EN_addrA,EX_EN_addrB,EX_EN_addrW,MEM_addrD,WB_addrD,opc,MEM_opc,MEM_wrReg,WB_wrReg,forwardA,forwardB,forwardW);
   input [5:0] EX_addrA,EX_addrB,EX_addrW,MEM_addrD,WB_addrD;
   input [5:0] opc,MEM_opc;
   input EX_EN_addrA,EX_EN_addrB,EX_EN_addrW,MEM_wrReg,WB_wrReg;

   output logic [2:0] forwardA = 0,forwardB = 0,forwardW = 0;
   
   wire check_addrA,check_addrB,check_addrW;

   assign check_addrA = ((opc == 6'd7) || (opc == 6'd12) || (opc == 6'd13) || (opc == 6'd14) || (opc == 6'd15) || (opc == 6'd16)) ? 0 : 1;
   assign check_addrB = ((opc == 6'd0) || (opc == 6'd1) || (opc == 6'd2) || (opc == 6'd3) || (opc == 6'd6) ||
                         (opc == 6'd10) || (opc == 6'd11)) ? 1 : 0;
   assign check_addrW = ((opc == 6'd10) || (opc == 6'd11) || (opc == 6'd14)) ? 1 : 0;

   always_comb begin
       if ((EX_addrA == MEM_addrD) && (MEM_wrReg == 1) && (MEM_opc == 6'd13 || MEM_opc == 6'd14) && (EX_EN_addrA == 0) && check_addrA)
           forwardA = 3'd5;
       else if ((EX_addrA == MEM_addrD) && (MEM_wrReg == 1) && (MEM_opc == 6'd9) && (EX_EN_addrA == 0) && check_addrA)
           forwardA = 3'd4;
       else if ((EX_addrA == MEM_addrD) && (MEM_wrReg == 1) && (MEM_opc == 6'd1) && (EX_EN_addrA == 0) && check_addrA)
           forwardA = 3'd3;
       else if ((EX_addrA == MEM_addrD) && (MEM_wrReg == 1) && (MEM_opc == 6'd0 || MEM_opc == 6'd6) && (EX_EN_addrA == 0) && check_addrA)
           forwardA = 3'd2;
       else if ((EX_addrA == WB_addrD) && (WB_wrReg == 1) && (EX_EN_addrA == 0) && check_addrA) 
           forwardA = 3'd1;
       else
           forwardA = 3'd0;   
    
       
       if ((EX_addrB == MEM_addrD) && (MEM_wrReg == 1) && (MEM_opc == 6'd13 || MEM_opc == 6'd14) && (EX_EN_addrB == 0) && check_addrB)
           forwardB = 3'd5;
       else if ((EX_addrB == MEM_addrD) && (MEM_wrReg == 1) && (MEM_opc == 6'd9) && (EX_EN_addrB == 0) && check_addrB)
           forwardB = 3'd4;
       else if ((EX_addrB == MEM_addrD) && (MEM_wrReg == 1) && (MEM_opc == 6'd1) && (EX_EN_addrB == 0) && check_addrB)
           forwardB = 3'd3;
       else if ((EX_addrB == MEM_addrD) && (MEM_wrReg == 1) && (MEM_opc == 6'd0 || MEM_opc == 6'd6) && (EX_EN_addrB == 0) && check_addrB)
           forwardB = 3'd2;
       else if ((EX_addrB == WB_addrD) && (WB_wrReg == 1) && (EX_EN_addrB == 0) && check_addrB) 
           forwardB = 3'd1;
       else
           forwardB = 3'd0;
           
       if ((EX_addrW == MEM_addrD) && (MEM_wrReg == 1) && (MEM_opc == 6'd13 || MEM_opc == 6'd14) && (EX_EN_addrW == 0) && check_addrW)
           forwardW = 3'd5;
       else if ((EX_addrW == MEM_addrD) && (MEM_wrReg == 1) && (MEM_opc == 6'd9) && (EX_EN_addrW == 0) && check_addrW)
           forwardW = 3'd4;
       else if ((EX_addrW == MEM_addrD) && (MEM_wrReg == 1) && (MEM_opc == 6'd1) && (EX_EN_addrW == 0) && check_addrW)
           forwardW = 3'd3;
       else if ((EX_addrW == MEM_addrD) && (MEM_wrReg == 1) && (MEM_opc == 6'd0 || MEM_opc == 6'd6) && (EX_EN_addrW == 0) && check_addrW)
           forwardW = 3'd2;
       else if ((EX_addrW == WB_addrD) && (WB_wrReg == 1) && (EX_EN_addrW == 0) && check_addrW) 
           forwardW = 3'd1;
       else
           forwardW = 3'd0;

   end
endmodule

// forward value from WB to ID
module ID_Forward (ID_addrA,ID_addrB,ID_addrD,WB_addrD,WB_wrReg,ID_forwardA,ID_forwardB,ID_forwardD);
      input [5:0] ID_addrA,ID_addrB,ID_addrD,WB_addrD;
      input WB_wrReg;
      
      output logic ID_forwardA = 0,ID_forwardB = 0,ID_forwardD = 0;
      
      always_comb begin
         if (ID_addrA == WB_addrD && WB_wrReg)
             ID_forwardA = 1;
         else
             ID_forwardA = 0;
             
         if (ID_addrB == WB_addrD && WB_wrReg)
             ID_forwardB = 1;
         else
             ID_forwardB = 0;
             
         if (ID_addrD == WB_addrD && WB_wrReg)
             ID_forwardD = 1;
         else
             ID_forwardD = 0;
      end
endmodule

module agp32_processor(
    input clk,
    input logic [1:0] data_in,
    output logic [`WORD_SIZE_INDEX:0] PC,
    output logic [9:0] data_out,
    output logic interrupt_req = 0,
    output logic[2:0] command = 3'd0,
    output logic [`WORD_SIZE_INDEX:0] data_addr = 32'hffff_ffff,
    output logic [`WORD_SIZE_INDEX:0] data_wdata,
    output logic [3:0] data_wstrb,
    input logic [1:0] error,
    input logic ready,
    input logic [`WORD_SIZE_INDEX:0] data_rdata,
    input logic [`WORD_SIZE_INDEX:0] inst_rdata,
    input logic mem_start_ready,
    input logic interrupt_ack);

   logic [2:0] state = 3'd3;
   logic do_interrupt = 0;

   /* additional wires for pipeline */
   wire [`WORD_SIZE_INDEX:0] IF_PC_input,IF_PC_output,IF_instr;
   wire [`WORD_SIZE_INDEX:0] ID_PC,ID_instr,ID_readDataA,ID_readDataB,ID_readDataW,ID_readDataA_Updated,ID_readDataB_Updated,ID_readDataW_Updated,ID_DataA,ID_DataB,ID_DataW,ID_imm,ID_immaV,ID_immbV,ID_immwV;
   wire [`WORD_SIZE_INDEX:0] EX_PC,EX_DataA,EX_DataB,EX_DataW,EX_imm,EX_ALU_res,EX_ALU_input1,EX_ALU_input2,EX_SHIFT_res,EX_DataA_Updated,EX_DataB_Updated,EX_DataW_Updated,EX_DataA_Rec,EX_DataB_Rec,EX_DataW_Rec;
   wire [`WORD_SIZE_INDEX:0] MEM_PC,MEM_DataA,MEM_DataB,MEM_DataW,MEM_imm,MEM_imm_Updated,MEM_ALU_res,MEM_SHIFT_res;
   wire [`WORD_SIZE_INDEX:0] WB_PC,WB_DataA,WB_read_data,WB_read_data_byte,WB_imm,WB_ALU_res,WB_SHIFT_res,WB_write_data;

   wire IF_PC_write_enable;
   wire ID_ID_write_enable,ID_EX_write_enable,ID_flush_flag,ID_EN_addra,ID_EN_addrb,ID_EN_addrw,ID_ForwardA,ID_ForwardB,ID_ForwardW;
   wire EX_write_enable,EX_MemRead,EX_EN_addra,EX_EN_addrb,EX_EN_addrw,EX_isAcc,EX_NOP_flag,EX_compute_enable;
   wire MEM_write_enable,MEM_read_mem,MEM_isInterrupt,MEM_wr_mem,MEM_wr_mem_byte,MEM_wr_reg,MEM_state_flag,MEM_NOP_flag;
   wire WB_write_enable,WB_wr_reg,WB_isOut,WB_state_flag;

   wire [1:0] PC_sel;
   wire [5:0] ID_Ra,ID_Rb,ID_Rw;
   wire [5:0] EX_Ra,EX_Rb,EX_Rw;
   wire [1:0] EX_PC_sel;
   wire [2:0] EX_ForwardA,EX_ForwardB,EX_ForwardW;
   wire [5:0] MEM_Rw;
   wire [5:0] WB_Rw;
   wire [2:0] WB_data_sel;
   
   wire [5:0] ID_opc,EX_opc,MEM_opc,WB_opc;
   wire [3:0] ID_func,EX_func;

   // Accelerator
   reg [`WORD_SIZE_INDEX:0] acc_arg,acc_res;
   reg [1:0] acc_state;
   reg acc_arg_ready,acc_res_ready;
   
   // additional flags to work with the hardware memory
   logic enable_mem = 0, enable_wb = 0;

   // assign
   assign PC = IF_PC_output;
   assign IF_instr = (ready ? inst_rdata : 32'h0000003F);
   assign WB_read_data = data_rdata;
   assign PC_sel = ((EX_PC_sel == 2'b01 || (EX_PC_sel == 2'b10 && EX_ALU_res == 0) || (EX_PC_sel == 2'b11 && EX_ALU_res != 0))  ? EX_PC_sel : 2'b00);
   
   /* additional units: (1) hazard_unit, handle hazards.
                        (2) forward_unit, pipeline forwarding.
   */
   Hazard_Ctrl_Unit hazard_ctrl_unit(ready,MEM_opc,state,IF_PC_write_enable,ID_ID_write_enable,ID_flush_flag,ID_EX_write_enable,EX_NOP_flag,MEM_state_flag,MEM_NOP_flag,WB_state_flag,PC_sel);
   Forward_Ctrl_Unit forward_ctrl_unit(EX_Ra,EX_Rb,EX_Rw,EX_EN_addra,EX_EN_addrb,EX_EN_addrw,MEM_Rw,WB_Rw,EX_opc,MEM_opc,
                                       (MEM_wr_reg && MEM_state_flag),(WB_wr_reg && WB_state_flag),EX_ForwardA,EX_ForwardB,EX_ForwardW);

   // IF 
   MUX_41 pc_update(IF_PC_output + 32'd4,EX_ALU_res,EX_PC + EX_DataW_Updated,EX_PC + EX_DataW_Updated,PC_sel,IF_PC_input);
   PC_Unit pc(clk,IF_PC_input,IF_PC_output,IF_PC_write_enable); 

   // ID
   ID_Pipeline id_pipeline(clk,IF_instr,IF_PC_output,ID_instr,ID_PC,ID_ID_write_enable,ID_flush_flag);
   assign ID_Ra = ID_instr[22:17];
   assign ID_Rb = ID_instr[15:10];
   assign ID_Rw = ID_instr[30:25];
   assign ID_EN_addra = ID_instr[23];
   assign ID_EN_addrb = ID_instr[16];
   assign ID_EN_addrw = ID_instr[31];
   // assign opc
   SetUp_Opc ID_setup_opc(ID_instr,ID_opc);
   // assign func
   assign ID_func = ((ID_opc == 6'd0) || (ID_opc == 6'd1) || ((ID_opc == 6'd6) || ((ID_opc == 6'd9) || ((ID_opc == 6'd10) || (ID_opc == 6'd11))))) ? ID_instr[9:6] : 4'd9;
   REG_Unit register(clk,ID_Ra,ID_Rb,ID_Rw,WB_Rw,ID_readDataA,ID_readDataB,WB_write_data,ID_readDataW,(WB_wr_reg && WB_state_flag));
   Imm_Sel imm_sel(ID_instr,ID_imm,ID_immaV,ID_immbV,ID_immwV);
   ID_Forward update_reg_data(ID_Ra,ID_Rb,ID_Rw,WB_Rw,(WB_wr_reg && WB_state_flag),ID_ForwardA,ID_ForwardB,ID_ForwardW);
   MUX_21 update_read_dataA(ID_readDataA,WB_write_data,ID_ForwardA,ID_readDataA_Updated);
   MUX_21 update_read_dataB(ID_readDataB,WB_write_data,ID_ForwardB,ID_readDataB_Updated);
   MUX_21 update_read_dataW(ID_readDataW,WB_write_data,ID_ForwardW,ID_readDataW_Updated);
   MUX_21 aV_sel(ID_readDataA_Updated,ID_immaV,ID_instr[23],ID_DataA);
   MUX_21 bV_sel(ID_readDataB_Updated,ID_immbV,ID_instr[16],ID_DataB);
   MUX_21 wV_sel(ID_readDataW_Updated,ID_immwV,ID_instr[31],ID_DataW);

   // EX
   EX_Pipeline ex_pipeline(clk,ID_PC,ID_opc,ID_func,ID_Ra,ID_Rb,ID_Rw,ID_imm,ID_DataA,ID_DataB,ID_DataW,ID_EN_addra,ID_EN_addrb,ID_EN_addrw,ID_EX_write_enable,EX_NOP_flag,
                           EX_isAcc,EX_MemRead,EX_PC,EX_opc,EX_func,EX_Ra,EX_Rb,EX_Rw,EX_imm,EX_DataA,EX_DataB,EX_DataW,EX_PC_sel,EX_EN_addra,EX_EN_addrb,EX_EN_addrw,EX_write_enable);
   MUX_81 update_aV_forward(EX_DataA,WB_write_data,MEM_ALU_res,MEM_SHIFT_res,MEM_PC + 32'd4,MEM_imm_Updated,32'd0,32'd0,EX_ForwardA,EX_DataA_Updated); 
   MUX_81 update_bV_forward(EX_DataB,WB_write_data,MEM_ALU_res,MEM_SHIFT_res,MEM_PC + 32'd4,MEM_imm_Updated,32'd0,32'd0,EX_ForwardB,EX_DataB_Updated);
   MUX_81 update_wV_forward(EX_DataW,WB_write_data,MEM_ALU_res,MEM_SHIFT_res,MEM_PC + 32'd4,MEM_imm_Updated,32'd0,32'd0,EX_ForwardW,EX_DataW_Updated);
   MUX_21 set_alu_input1(EX_DataA_Updated,EX_PC,1'({EX_opc == 6'd9}),EX_ALU_input1);
   MUX_21 set_alu_input2(EX_DataB_Updated,EX_DataA_Updated,1'({EX_opc == 6'd9}),EX_ALU_input2);
   assign EX_compute_enable = ((state == 3'd0) && (MEM_opc != 6'd16 || (MEM_opc == 6'd16 && (EX_ForwardA != 0 || EX_ForwardB != 0))));
   ALU_Unit compute_alu_res(EX_compute_enable,EX_func,EX_ALU_input1,EX_ALU_input2,EX_ALU_res);
   SHIFT_Unit compute_shift_res((EX_compute_enable && EX_opc == 6'd1),EX_func,EX_DataA_Updated,EX_DataB_Updated,EX_SHIFT_res);
   Data_Record record_value(state,MEM_opc,EX_ForwardA,EX_ForwardB,EX_ForwardW,EX_DataA_Updated,EX_DataB_Updated,EX_DataW_Updated,EX_DataA_Rec,EX_DataB_Rec,EX_DataW_Rec);
   
   // MEM
   MEM_Pipeline mem_pipeline(clk,EX_PC,EX_opc,EX_Rw,EX_imm,EX_ALU_res,EX_SHIFT_res,EX_DataA_Rec,EX_DataB_Rec,EX_DataW_Rec,EX_MemRead,((EX_write_enable && MEM_state_flag) || enable_mem),MEM_NOP_flag,
                             MEM_read_mem,MEM_isInterrupt,MEM_wr_mem,MEM_wr_mem_byte,MEM_wr_reg,MEM_PC,MEM_opc,MEM_Rw,MEM_imm,MEM_ALU_res,MEM_SHIFT_res,MEM_DataA,MEM_DataB,MEM_DataW,MEM_write_enable);
   MUX_21 generate_imm_loadupper(MEM_imm,{MEM_imm[8:0],MEM_DataW[22:0]},1'({MEM_opc == 6'd14}),MEM_imm_Updated);

   // WB
   WB_Pipeline wb_pipeline(clk,MEM_PC,MEM_opc,MEM_Rw,MEM_imm_Updated,MEM_ALU_res,MEM_SHIFT_res,MEM_DataA,MEM_wr_reg,((MEM_write_enable && WB_state_flag) || enable_wb),
                           WB_data_sel,WB_wr_reg,WB_isOut,WB_PC,WB_opc,WB_Rw,WB_imm,WB_ALU_res,WB_SHIFT_res,WB_DataA,WB_write_enable);
   MUX_41 generate_read_data_byte(32'({WB_read_data[7:0]}),32'({WB_read_data[15:8]}),32'({WB_read_data[23:16]}),32'({WB_read_data[31:24]}),2'({WB_DataA[1:0]}),WB_read_data_byte);
   MUX_81 generate_write_data(WB_ALU_res,WB_SHIFT_res,32'({data_in}),WB_PC + 32'd4,WB_imm,WB_read_data,WB_read_data_byte,acc_res,WB_data_sel,WB_write_data);

   always_ff @(posedge clk) begin
       if (error == 2'd0) begin
       case (state)
           3'd0: begin
           
               if (ready == 0) begin
                   state = 3'd7;
               end
               
               else if (MEM_isInterrupt) begin
                   command <= 3'd4;
                   state = 3'd7;
                   do_interrupt = 1;
                   data_addr <= 32'd0;
               end
               
               else if (MEM_read_mem) begin
                   command <= 3'd2;
                   state = 3'd7;
                   data_addr <= MEM_DataA;    
               end

               else if (MEM_wr_mem || MEM_wr_mem_byte) begin 
                   command <= 3'd3;
                   state = 3'd7;
                   data_addr <= MEM_DataB;
                   if (MEM_wr_mem) begin
                       data_wdata <= MEM_DataA;
                       data_wstrb <= 4'd15;
                   end
                   else begin 
                       case (MEM_DataB[1:0]) 
                       2'd0 : data_wdata[7:0] <= MEM_DataA[7:0];
                       2'd1 : data_wdata[15:8] <= MEM_DataA[7:0];
                       2'd2 : data_wdata[23:16] <= MEM_DataA[7:0];
                       2'd3 : data_wdata[31:24] <= MEM_DataA[7:0];
                       endcase
                       data_wstrb <= (4'd1 << 4'({MEM_DataB[1:0]}));
                    end
               end
               
               else if (PC_sel != 2'b00) begin
                   command <= 3'd1;
                   state = 3'd1;
               end
               
               else if (EX_isAcc) begin
                   command <= 3'd1;
                   state = 3'd2;
                   acc_arg = EX_DataA_Updated;
                   acc_arg_ready <= 1;
               end
               
               //data_out: no side effect
               if (WB_isOut) begin
                   data_out <= WB_ALU_res[9:0];
               end
               
               enable_wb = 0;
               enable_mem = 0;
           end
           3'd1: begin
               if (ready && (command == 3'd0)) begin
                   state = 3'd6;
               end
               
               command <= 3'd0;
           end
           3'd2: begin 
               if (acc_res_ready && (!acc_arg_ready)) begin
               state = 3'd6; 
               end
               acc_arg_ready <= 0;
           end
           3'd3: begin 
               if (mem_start_ready) begin
               command <= 3'd1;
               state = 3'd1; 
               end
           end
           3'd4: begin 
               if (interrupt_ack) begin
               state = 3'd6;
               interrupt_req <= 0;
               end
           end
           3'd6: begin
               state = 3'd0;
               command <= 3'd1;
               enable_wb = 1;
               enable_mem = 1;
           end
           3'd7: begin
               if (ready && (command == 3'd0)) begin
                   if (do_interrupt) begin
                      state = 3'd4; 
                      do_interrupt = 0;
                      interrupt_req <= 1;
                   end
                   else state = 3'd6;
               end
               
               command <= 3'd0;
           end 
       endcase
       end
       else state = 4'd5;
   end
   
   always_ff @(posedge clk) begin
       if (acc_arg_ready) begin
           acc_res_ready <= 0;
           acc_state = 2'd0;
       end
       else begin
           case (acc_state) 
            2'd0 : acc_state = 2'd1;
            2'd1 : begin
                acc_res <= 32'({acc_arg[31:16] + acc_arg[15:0]});
                acc_res_ready <= 1;
            end
           endcase
       end
   end
   
endmodule