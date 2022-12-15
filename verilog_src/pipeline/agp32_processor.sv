`timescale 1ns / 1ps

module agp32_processor(
  input clk,
  input logic[1:0] data_in,
  input logic[1:0] error,
  input logic ready,
  input logic[31:0] data_rdata,
  input logic[31:0] inst_rdata,
  input logic mem_start_ready,
  input logic interrupt_ack,
  output logic[31:0] PC = 32'd0,
  output logic[9:0] data_out = 'x,
  output logic interrupt_req = 0,
  output logic[2:0] command = 3'd0,
  output logic[31:0] data_addr = 32'd4294967295,
  output logic[31:0] data_wdata = 'x,
  output logic[3:0] data_wstrb = 'x
);

logic[2:0] state = 3'd3;
logic[31:0] R[63:0] = '{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
logic do_interrupt = 0;
logic[31:0] acc_arg = 'x;
logic acc_arg_ready = 0;
logic[31:0] acc_res = 'x;
logic acc_res_ready = 'x;
logic[1:0] acc_state = 2'd0;
logic[32:0] ALU_sum = 'x;
logic[63:0] ALU_prod = 'x;
logic[31:0] ALU_sub = 'x;
logic[31:0] shift_sh = 'x;
logic[31:0] IF_PC_input = 'x;
logic[31:0] IF_instr = 'x;
logic IF_PC_write_enable = 0;
logic[31:0] ID_PC = 'x;
logic[31:0] ID_instr = 32'd63;
logic[31:0] ID_read_dataA = 'x;
logic[31:0] ID_read_dataB = 'x;
logic[31:0] ID_read_dataW = 'x;
logic[31:0] ID_immA = 'x;
logic[31:0] ID_immB = 'x;
logic[31:0] ID_immW = 'x;
logic[31:0] ID_imm = 'x;
logic[31:0] ID_dataA = 'x;
logic[31:0] ID_dataB = 'x;
logic[31:0] ID_dataW = 'x;
logic ID_ID_write_enable = 'x;
logic ID_EX_write_enable = 'x;
logic ID_flush_flag = 'x;
logic ID_addrA_disable = 'x;
logic ID_addrB_disable = 'x;
logic ID_addrW_disable = 'x;
logic[5:0] ID_addrA = 'x;
logic[5:0] ID_addrB = 'x;
logic[5:0] ID_addrW = 'x;
logic[5:0] ID_opc = 'x;
logic[3:0] ID_func = 'x;
logic[31:0] EX_PC = 'x;
logic[31:0] EX_dataA = 'x;
logic[31:0] EX_dataB = 'x;
logic[31:0] EX_dataW = 'x;
logic[31:0] EX_imm = 'x;
logic[31:0] EX_imm_updated = 'x;
logic[31:0] EX_ALU_input1 = 'x;
logic[31:0] EX_ALU_input2 = 'x;
logic EX_carry_flag = 'x;
logic EX_overflow_flag = 'x;
logic[31:0] EX_ALU_res = 'x;
logic[31:0] EX_SHIFT_res = 'x;
logic EX_NOP_flag = 'x;
logic EX_write_reg = 0;
logic EX_checkA = 'x;
logic EX_checkB = 'x;
logic EX_checkW = 'x;
logic EX_jump_sel = 'x;
logic[31:0] EX_jump_addr = 'x;
logic[5:0] EX_addrW = 'x;
logic[5:0] EX_opc = 6'd16;
logic[3:0] EX_func = 'x;
logic[31:0] MEM_PC = 'x;
logic[31:0] MEM_dataA = 'x;
logic[31:0] MEM_dataB = 'x;
logic[31:0] MEM_imm = 'x;
logic[31:0] MEM_ALU_res = 'x;
logic[31:0] MEM_SHIFT_res = 'x;
logic MEM_read_mem = 'x;
logic MEM_write_mem = 'x;
logic MEM_write_mem_byte = 'x;
logic MEM_write_reg = 0;
logic MEM_isAcc = 'x;
logic MEM_isInterrupt = 'x;
logic MEM_state_flag = 'x;
logic MEM_NOP_flag = 'x;
logic MEM_checkA = 'x;
logic MEM_checkB = 'x;
logic MEM_checkW = 'x;
logic[5:0] MEM_addrW = 'x;
logic[5:0] MEM_opc = 6'd16;
logic[31:0] WB_PC = 'x;
logic[31:0] WB_dataA = 'x;
logic[31:0] WB_read_data = 'x;
logic[31:0] WB_read_data_byte = 'x;
logic[31:0] WB_imm = 'x;
logic[31:0] WB_ALU_res = 'x;
logic[31:0] WB_SHIFT_res = 'x;
logic[31:0] WB_write_data = 'x;
logic WB_write_reg = 0;
logic WB_isOut = 'x;
logic WB_state_flag = 'x;
logic WB_checkA = 'x;
logic WB_checkB = 'x;
logic WB_checkW = 'x;
logic[2:0] WB_data_sel = 'x;
logic[5:0] WB_addrW = 'x;
logic[5:0] WB_opc = 6'd16;

always_comb begin
WB_read_data = data_rdata;
WB_read_data_byte = (WB_dataA[1:0] == 2'd0) ? 32'({data_rdata[7:0]}) : ((WB_dataA[1:0] == 2'd1) ? 32'({data_rdata[15:8]}) : ((WB_dataA[1:0] == 2'd2) ? 32'({data_rdata[23:16]}) : 32'({data_rdata[31:24]})));
if (WB_state_flag) begin
WB_isOut = WB_opc == 6'd6;
WB_data_sel = ((WB_opc == 6'd0) || (WB_opc == 6'd6)) ? 3'd0 : ((WB_opc == 6'd1) ? 3'd1 : ((WB_opc == 6'd7) ? 3'd2 : ((WB_opc == 6'd9) ? 3'd3 : (((WB_opc == 6'd13) || (WB_opc == 6'd14)) ? 3'd4 : ((WB_opc == 6'd4) ? 3'd5 : ((WB_opc == 6'd5) ? 3'd6 : ((WB_opc == 6'd8) ? 3'd7 : 3'd0)))))));
end
WB_write_data = (WB_data_sel == 3'd0) ? WB_ALU_res : ((WB_data_sel == 3'd1) ? WB_SHIFT_res : ((WB_data_sel == 3'd2) ? 32'({data_in}) : ((WB_data_sel == 3'd3) ? (WB_PC + 32'd4) : ((WB_data_sel == 3'd4) ? WB_imm : ((WB_data_sel == 3'd5) ? WB_read_data : ((WB_data_sel == 3'd6) ? WB_read_data_byte : acc_res))))));
end

always_comb begin
MEM_read_mem = (MEM_opc == 6'd4) || (MEM_opc == 6'd5);
MEM_write_mem = MEM_opc == 6'd2;
MEM_write_mem_byte = MEM_opc == 6'd3;
MEM_isAcc = MEM_opc == 6'd8;
MEM_isInterrupt = MEM_opc == 6'd12;
end

always_comb begin
IF_PC_input = EX_jump_sel ? EX_jump_addr : (PC + 32'd4);
end

always_comb begin
if (EX_opc == 6'd9) begin
EX_jump_sel = 1;
EX_jump_addr = EX_ALU_res;
end else begin
if (((EX_opc == 6'd10) && (EX_ALU_res == 32'd0)) || ((EX_opc == 6'd11) && (!(EX_ALU_res == 32'd0)))) begin
EX_jump_sel = 1;
EX_jump_addr = EX_PC + EX_dataW;
end else begin
EX_jump_sel = 0;
EX_jump_addr = 32'd0;
end
end
end

always_comb begin
if (ID_EX_write_enable) begin
case (EX_func[1:0])
2'd0 : EX_SHIFT_res = EX_dataA << EX_dataB;
2'd1 : EX_SHIFT_res = EX_dataA >> EX_dataB;
2'd2 : EX_SHIFT_res = {$signed(EX_dataA) >>> (EX_dataB)};
2'd3 : begin
shift_sh = 32'({EX_dataB[4:0]});
EX_SHIFT_res = (EX_dataA >> shift_sh) | (EX_dataA << (32'd32 - shift_sh));
end
endcase
end
end

always_comb begin
ALU_sum = (33'({EX_ALU_input1}) + 33'({EX_ALU_input2})) + ((EX_func == 4'd1) ? 33'({EX_carry_flag}) : 33'd0);
ALU_prod = 64'({EX_ALU_input1}) * 64'({EX_ALU_input2});
if (ID_EX_write_enable) begin
case (EX_func)
4'd0 : begin
EX_overflow_flag = (EX_ALU_input1[31] == EX_ALU_input2[31]) && (!(ALU_sum[31] == EX_ALU_input1[31]));
EX_carry_flag = ALU_sum[32];
EX_ALU_res = ALU_sum[31:0];
end
4'd1 : begin
EX_carry_flag = ALU_sum[32];
EX_ALU_res = ALU_sum[31:0];
end
4'd2 : begin
ALU_sub = EX_ALU_input1 - EX_ALU_input2;
EX_ALU_res = ALU_sub;
EX_overflow_flag = (!(EX_ALU_input1[31] == EX_ALU_input2[31])) && (!(ALU_sub[31] == EX_ALU_input1[31]));
end
4'd3 : EX_ALU_res = 32'({EX_carry_flag});
4'd4 : EX_ALU_res = 32'({EX_overflow_flag});
4'd5 : EX_ALU_res = EX_ALU_input1 + 32'd1;
4'd6 : EX_ALU_res = EX_ALU_input1 - 32'd1;
4'd7 : EX_ALU_res = ALU_prod[31:0];
4'd8 : EX_ALU_res = ALU_prod[63:32];
4'd9 : EX_ALU_res = EX_ALU_input1 & EX_ALU_input2;
4'd10 : EX_ALU_res = EX_ALU_input1 | EX_ALU_input2;
4'd11 : EX_ALU_res = EX_ALU_input1 ^ EX_ALU_input2;
4'd12 : EX_ALU_res = 32'({EX_ALU_input1 == EX_ALU_input2});
4'd13 : EX_ALU_res = 32'({{$signed(EX_ALU_input1) < $signed(EX_ALU_input2)}});
4'd14 : EX_ALU_res = 32'({EX_ALU_input1 < EX_ALU_input2});
4'd15 : EX_ALU_res = EX_ALU_input2;
endcase
end
end

always_comb begin
EX_ALU_input1 = (EX_opc == 6'd9) ? EX_PC : EX_dataA;
EX_ALU_input2 = (EX_opc == 6'd9) ? EX_dataA : EX_dataB;
EX_imm_updated = (EX_opc == 6'd14) ? {EX_imm[8:0], EX_dataW[22:0]} : EX_imm;
end

always_comb begin
EX_checkA = EX_write_reg && ((EX_addrW == ID_addrA) && (!ID_addrA_disable));
MEM_checkA = MEM_write_reg && ((MEM_addrW == ID_addrA) && (!ID_addrA_disable));
WB_checkA = WB_write_reg && ((WB_addrW == ID_addrA) && (!ID_addrA_disable));
EX_checkB = EX_write_reg && ((EX_addrW == ID_addrB) && (!ID_addrB_disable));
MEM_checkB = MEM_write_reg && ((MEM_addrW == ID_addrB) && (!ID_addrB_disable));
WB_checkB = WB_write_reg && ((WB_addrW == ID_addrB) && (!ID_addrB_disable));
EX_checkW = EX_write_reg && ((EX_addrW == ID_addrW) && (!ID_addrW_disable));
MEM_checkW = MEM_write_reg && ((MEM_addrW == ID_addrW) && (!ID_addrW_disable));
WB_checkW = WB_write_reg && ((WB_addrW == ID_addrW) && (!ID_addrW_disable));
end

always_comb begin
ID_addrA = ID_instr[22:17];
ID_addrB = ID_instr[15:10];
ID_addrW = ID_instr[30:25];
ID_addrA_disable = ID_instr[23];
ID_addrB_disable = ID_instr[16];
ID_addrW_disable = ID_instr[31];
ID_read_dataA = R[ID_addrA];
ID_read_dataB = R[ID_addrB];
ID_read_dataW = R[ID_addrW];
ID_immA = {32'($signed(ID_instr[22:17]))};
ID_immB = {32'($signed(ID_instr[15:10]))};
ID_immW = {32'($signed(ID_instr[30:25]))};
ID_dataA = ID_instr[23] ? ID_immA : ID_read_dataA;
ID_dataB = ID_instr[16] ? ID_immB : ID_read_dataB;
ID_dataW = ID_instr[31] ? ID_immW : ID_read_dataW;
end

always_comb begin
if (ID_instr[31] && ID_instr[24]) begin
if (ID_instr[23]) begin
ID_imm = 32'd0 - 32'({ID_instr[22:0]});
end else begin
ID_imm = 32'({ID_instr[22:0]});
end
end else begin
if (ID_instr[24] && (ID_instr[23:9] == 15'd0)) begin
ID_imm = 32'({ID_instr[8:0]});
end else begin
ID_imm = 32'd0;
end
end
end

always_comb begin
if (ID_instr[24]) begin
if (ID_instr[31]) begin
ID_opc = 6'd13;
end else begin
if (ID_instr[23:9] == 15'd0) begin
ID_opc = 6'd14;
end else begin
ID_opc = 6'd15;
end
end
end else begin
if ((ID_instr[5:0] == 6'd10) || ((ID_instr[5:0] == 6'd11) || (ID_instr[5:0] == 6'd12))) begin
ID_opc = ID_instr[5:0];
end else begin
if (ID_instr[31]) begin
ID_opc = 6'd15;
end else begin
if (ID_instr[5:0] < 6'd10) begin
ID_opc = ID_instr[5:0];
end else begin
ID_opc = 6'd15;
end
end
end
end
if ((ID_opc == 6'd0) || ((ID_opc == 6'd6) || ((ID_opc == 6'd9) || ((ID_opc == 6'd10) || (ID_opc == 6'd11))))) begin
ID_func = ID_instr[9:6];
end else begin
if (ID_opc == 6'd1) begin
ID_func = {2'd3, ID_instr[7:6]};
end else begin
ID_func = 4'd9;
end
end
end

always_comb begin
IF_instr = ready ? inst_rdata : 32'd63;
end

always_comb begin
if ((state == 3'd1) || ((state == 3'd2) || ((state == 3'd3) || ((state == 3'd4) || (state == 3'd5))))) begin
IF_PC_write_enable = 0;
ID_ID_write_enable = 0;
ID_flush_flag = 0;
ID_EX_write_enable = 0;
EX_NOP_flag = 0;
MEM_state_flag = 0;
MEM_NOP_flag = 0;
WB_state_flag = 0;
end else begin
if (!ready) begin
IF_PC_write_enable = 0;
ID_ID_write_enable = 0;
ID_flush_flag = 0;
ID_EX_write_enable = 0;
EX_NOP_flag = 0;
MEM_state_flag = 0;
MEM_NOP_flag = 0;
WB_state_flag = 0;
end else begin
if ((MEM_opc == 6'd2) || ((MEM_opc == 6'd3) || ((MEM_opc == 6'd4) || ((MEM_opc == 6'd5) || ((MEM_opc == 6'd8) || (MEM_opc == 6'd12)))))) begin
IF_PC_write_enable = 0;
ID_ID_write_enable = 0;
ID_flush_flag = 0;
ID_EX_write_enable = 0;
EX_NOP_flag = 0;
MEM_state_flag = 1;
MEM_NOP_flag = 1;
WB_state_flag = 1;
end else begin
if (EX_jump_sel) begin
IF_PC_write_enable = 1;
ID_ID_write_enable = 1;
ID_flush_flag = 1;
ID_EX_write_enable = 1;
EX_NOP_flag = 1;
MEM_state_flag = 1;
MEM_NOP_flag = 0;
WB_state_flag = 1;
end else begin
if (EX_checkA || (EX_checkB || (EX_checkW || (MEM_checkA || (MEM_checkB || (MEM_checkW || (WB_checkA || (WB_checkB || WB_checkW)))))))) begin
IF_PC_write_enable = 0;
ID_ID_write_enable = 0;
ID_flush_flag = 0;
ID_EX_write_enable = 1;
EX_NOP_flag = 1;
MEM_state_flag = 1;
MEM_NOP_flag = 0;
WB_state_flag = 1;
end else begin
IF_PC_write_enable = 1;
ID_ID_write_enable = 1;
ID_flush_flag = 0;
ID_EX_write_enable = 1;
EX_NOP_flag = 0;
MEM_state_flag = 1;
MEM_NOP_flag = 0;
WB_state_flag = 1;
end
end
end
end
end
end

always_ff @ (posedge clk) begin
if (IF_PC_write_enable) begin
PC <= IF_PC_input;
end
end

always_ff @ (posedge clk) begin
if (ID_ID_write_enable) begin
ID_PC <= PC;
ID_instr = ID_flush_flag ? 32'd63 : IF_instr;
end
end

always_ff @ (posedge clk) begin
if (WB_write_reg && WB_state_flag) begin
R[WB_addrW] = WB_write_data;
end
end

always_ff @ (posedge clk) begin
if (ID_EX_write_enable) begin
EX_PC <= ID_PC;
EX_dataA <= ID_dataA;
EX_dataB <= ID_dataB;
EX_dataW = ID_dataW;
EX_imm = ID_imm;
EX_addrW <= ID_addrW;
EX_opc <= EX_NOP_flag ? 6'd16 : ID_opc;
EX_func = EX_NOP_flag ? 4'd9 : ID_func;
EX_write_reg = EX_NOP_flag ? 0 : ((ID_opc == 6'd0) || ((ID_opc == 6'd1) || ((ID_opc == 6'd4) || ((ID_opc == 6'd5) || ((ID_opc == 6'd6) || ((ID_opc == 6'd7) || ((ID_opc == 6'd8) || ((ID_opc == 6'd9) || ((ID_opc == 6'd13) || (ID_opc == 6'd14))))))))));
end
end

always_ff @ (posedge clk) begin
if (MEM_state_flag) begin
MEM_PC <= EX_PC;
MEM_dataA <= EX_dataA;
MEM_dataB <= EX_dataB;
MEM_imm <= EX_imm_updated;
MEM_ALU_res <= EX_ALU_res;
MEM_SHIFT_res <= EX_SHIFT_res;
MEM_addrW <= EX_addrW;
MEM_opc <= MEM_NOP_flag ? 6'd16 : EX_opc;
MEM_write_reg = MEM_NOP_flag ? 0 : ((EX_opc == 6'd0) || ((EX_opc == 6'd1) || ((EX_opc == 6'd4) || ((EX_opc == 6'd5) || ((EX_opc == 6'd6) || ((EX_opc == 6'd7) || ((EX_opc == 6'd8) || ((EX_opc == 6'd9) || ((EX_opc == 6'd13) || (EX_opc == 6'd14))))))))));
end
end

always_ff @ (posedge clk) begin
if (WB_state_flag) begin
WB_PC = MEM_PC;
WB_dataA = MEM_dataA;
WB_imm = MEM_imm;
WB_ALU_res = MEM_ALU_res;
WB_SHIFT_res = MEM_SHIFT_res;
WB_write_reg <= (MEM_opc == 6'd0) || ((MEM_opc == 6'd1) || ((MEM_opc == 6'd4) || ((MEM_opc == 6'd5) || ((MEM_opc == 6'd6) || ((MEM_opc == 6'd7) || ((MEM_opc == 6'd8) || ((MEM_opc == 6'd9) || ((MEM_opc == 6'd13) || (MEM_opc == 6'd14)))))))));
WB_addrW <= MEM_addrW;
WB_opc = MEM_opc;
end
end

always_ff @ (posedge clk) begin
data_out <= WB_isOut ? WB_ALU_res[9:0] : data_out;
if (error == 2'd0) begin
case (state)
3'd0 : if (!ready) begin
state = 3'd1;
end else begin
if (MEM_isInterrupt) begin
state = 3'd1;
command <= 3'd4;
do_interrupt = 1;
data_addr <= 32'd0;
end else begin
if (MEM_read_mem) begin
state = 3'd1;
command <= 3'd2;
data_addr <= MEM_dataA;
end else begin
if (MEM_write_mem) begin
state = 3'd1;
command <= 3'd3;
data_addr <= MEM_dataB;
data_wdata <= MEM_dataA;
data_wstrb <= 4'd15;
end else begin
if (MEM_write_mem_byte) begin
state = 3'd1;
command <= 3'd3;
data_addr <= MEM_dataB;
data_wstrb <= 4'd1 << 4'({MEM_dataB[1:0]});
case (MEM_dataB[1:0])
2'd0 : data_wdata[7:0] <= MEM_dataA[7:0];
2'd1 : data_wdata[15:8] <= MEM_dataA[7:0];
2'd2 : data_wdata[23:16] <= MEM_dataA[7:0];
2'd3 : data_wdata[31:24] <= MEM_dataA[7:0];
endcase
end else begin
if (MEM_isAcc) begin
state = 3'd2;
command <= 3'd1;
acc_arg <= MEM_dataA;
acc_arg_ready <= 1;
end else begin
command <= 3'd1;
end
end
end
end
end
end
3'd1 : begin
if (ready && (command == 3'd0)) begin
if (do_interrupt) begin
state = 3'd4;
do_interrupt = 0;
interrupt_req <= 1;
end else begin
state = 3'd0;
end
end
command <= 3'd0;
end
3'd2 : begin
if (acc_res_ready && (!acc_arg_ready)) begin
state = 3'd0;
end
acc_arg_ready <= 0;
command <= 3'd0;
end
3'd3 : if (mem_start_ready) begin
state = 3'd1;
command <= 3'd1;
end
3'd4 : if (interrupt_ack) begin
state = 3'd0;
interrupt_req <= 0;
end
endcase
end else begin
state = 3'd5;
end
end

always_ff @ (posedge clk) begin
if (acc_arg_ready) begin
acc_res_ready <= 0;
acc_state = 2'd0;
end else begin
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
