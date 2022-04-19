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
logic[31:0] acc_arg = 'x;
logic acc_arg_ready = 0;
logic do_interrupt = 0;
logic[31:0] acc_res = 'x;
logic acc_res_ready = 'x;
logic[1:0] acc_state = 'x;
logic[32:0] ALU_sum = 'x;
logic[63:0] ALU_prod = 'x;
logic[31:0] ALU_sub = 'x;
logic[31:0] shift_sh = 'x;
logic checkA = 'x;
logic checkB = 'x;
logic checkW = 'x;
logic[31:0] IF_PC_input = 'x;
logic[31:0] IF_instr = 32'd63;
logic IF_PC_write_enable = 'x;
logic[31:0] ID_PC = 'x;
logic[31:0] ID_instr = 32'd63;
logic[31:0] ID_read_dataA = 'x;
logic[31:0] ID_read_dataB = 'x;
logic[31:0] ID_read_dataW = 'x;
logic[31:0] ID_read_dataA_updated = 'x;
logic[31:0] ID_read_dataB_updated = 'x;
logic[31:0] ID_read_dataW_updated = 'x;
logic[31:0] ID_immA = 'x;
logic[31:0] ID_immB = 'x;
logic[31:0] ID_immW = 'x;
logic[31:0] ID_imm = 'x;
logic ID_ID_write_enable = 'x;
logic ID_EX_write_enable = 'x;
logic ID_flush_flag = 'x;
logic ID_addrA_enable = 'x;
logic ID_addrB_enable = 'x;
logic ID_addrW_enable = 'x;
logic[5:0] ID_addrA = 'x;
logic[5:0] ID_addrB = 'x;
logic[5:0] ID_addrW = 'x;
logic[5:0] ID_opc = 'x;
logic[3:0] ID_func = 'x;
logic[31:0] EX_PC = 'x;
logic[31:0] EX_dataA = 'x;
logic[31:0] EX_dataB = 'x;
logic[31:0] EX_dataW = 'x;
logic[31:0] EX_dataA_updated = 'x;
logic[31:0] EX_dataB_updated = 'x;
logic[31:0] EX_dataW_updated = 'x;
logic[31:0] EX_dataA_rec = 'x;
logic[31:0] EX_dataB_rec = 'x;
logic[31:0] EX_dataW_rec = 'x;
logic[31:0] EX_imm = 'x;
logic[31:0] EX_ALU_input1 = 'x;
logic[31:0] EX_ALU_input2 = 'x;
logic EX_carry_flag = 'x;
logic EX_overflow_flag = 'x;
logic[31:0] EX_ALU_res = 'x;
logic[31:0] EX_SHIFT_res = 'x;
logic EX_write_enable = 'x;
logic EX_addrA_enable = 'x;
logic EX_addrB_enable = 'x;
logic EX_addrW_enable = 'x;
logic EX_isAcc = 'x;
logic EX_NOP_flag = 'x;
logic EX_compute_enable = 'x;
logic[1:0] EX_PC_sel = 2'd0;
logic EX_jump_sel = 0;
logic[31:0] EX_jump_addr = 'x;
logic[2:0] EX_ForwardA = 3'd0;
logic[2:0] EX_ForwardB = 3'd0;
logic[2:0] EX_ForwardW = 3'd0;
logic[5:0] EX_addrA = 'x;
logic[5:0] EX_addrB = 'x;
logic[5:0] EX_addrW = 'x;
logic[5:0] EX_opc = 6'd15;
logic[3:0] EX_func = 'x;
logic[31:0] MEM_PC = 'x;
logic[31:0] MEM_dataA = 'x;
logic[31:0] MEM_dataB = 'x;
logic[31:0] MEM_dataW = 'x;
logic[31:0] MEM_imm = 'x;
logic[31:0] MEM_imm_updated = 'x;
logic[31:0] MEM_ALU_res = 'x;
logic[31:0] MEM_SHIFT_res = 'x;
logic MEM_write_enable = 'x;
logic MEM_read_mem = 'x;
logic MEM_write_mem = 'x;
logic MEM_write_mem_byte = 'x;
logic MEM_write_reg = 0;
logic MEM_isInterrupt = 'x;
logic MEM_state_flag = 'x;
logic MEM_NOP_flag = 'x;
logic MEM_enable = 0;
logic[5:0] MEM_addrW = 'x;
logic[5:0] MEM_opc = 6'd15;
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
logic WB_enable = 0;
logic[2:0] WB_data_sel = 'x;
logic[5:0] WB_addrW = 'x;
logic[5:0] WB_opc = 'x;

always_comb begin
checkA = (EX_opc == 6'd0) || ((EX_opc == 6'd1) || ((EX_opc == 6'd2) || ((EX_opc == 6'd3) || ((EX_opc == 6'd4) || ((EX_opc == 6'd5) || ((EX_opc == 6'd6) || ((EX_opc == 6'd8) || ((EX_opc == 6'd9) || ((EX_opc == 6'd10) || (EX_opc == 6'd11))))))))));
EX_ForwardA = ((EX_addrA == MEM_addrW) && (MEM_write_reg && (((MEM_opc == 6'd13) || (MEM_opc == 6'd14)) && ((!EX_addrA_enable) && checkA)))) ? 3'd5 : (((EX_addrA == MEM_addrW) && (MEM_write_reg && ((MEM_opc == 6'd9) && ((!EX_addrA_enable) && checkA)))) ? 3'd4 : (((EX_addrA == MEM_addrW) && (MEM_write_reg && ((MEM_opc == 6'd1) && ((!EX_addrA_enable) && checkA)))) ? 3'd3 : (((EX_addrA == MEM_addrW) && (MEM_write_reg && (((MEM_opc == 6'd0) || (MEM_opc == 6'd6)) && ((!EX_addrA_enable) && checkA)))) ? 3'd2 : (((EX_addrA == WB_addrW) && (WB_write_reg && ((!EX_addrA_enable) && checkA))) ? 3'd1 : 3'd0))));
end

always_comb begin
checkB = (EX_opc == 6'd0) || ((EX_opc == 6'd1) || ((EX_opc == 6'd2) || ((EX_opc == 6'd3) || ((EX_opc == 6'd6) || ((EX_opc == 6'd10) || (EX_opc == 6'd11))))));
EX_ForwardB = ((EX_addrB == MEM_addrW) && (MEM_write_reg && (((MEM_opc == 6'd13) || (MEM_opc == 6'd14)) && ((!EX_addrB_enable) && checkB)))) ? 3'd5 : (((EX_addrB == MEM_addrW) && (MEM_write_reg && ((MEM_opc == 6'd9) && ((!EX_addrB_enable) && checkB)))) ? 3'd4 : (((EX_addrB == MEM_addrW) && (MEM_write_reg && ((MEM_opc == 6'd1) && ((!EX_addrB_enable) && checkB)))) ? 3'd3 : (((EX_addrB == MEM_addrW) && (MEM_write_reg && (((MEM_opc == 6'd0) || (MEM_opc == 6'd6)) && ((!EX_addrB_enable) && checkB)))) ? 3'd2 : (((EX_addrB == WB_addrW) && (WB_write_reg && ((!EX_addrB_enable) && checkB))) ? 3'd1 : 3'd0))));
end

always_comb begin
checkW = (EX_opc == 6'd10) || ((EX_opc == 6'd11) || (EX_opc == 6'd14));
EX_ForwardW = ((EX_addrW == MEM_addrW) && (MEM_write_reg && (((MEM_opc == 6'd13) || (MEM_opc == 6'd14)) && ((!EX_addrW_enable) && checkW)))) ? 3'd5 : (((EX_addrW == MEM_addrW) && (MEM_write_reg && ((MEM_opc == 6'd9) && ((!EX_addrW_enable) && checkW)))) ? 3'd4 : (((EX_addrW == MEM_addrW) && (MEM_write_reg && ((MEM_opc == 6'd1) && ((!EX_addrW_enable) && checkW)))) ? 3'd3 : (((EX_addrW == MEM_addrW) && (MEM_write_reg && (((MEM_opc == 6'd0) || (MEM_opc == 6'd6)) && ((!EX_addrW_enable) && checkW)))) ? 3'd2 : (((EX_addrW == WB_addrW) && (WB_write_reg && ((!EX_addrW_enable) && checkW))) ? 3'd1 : 3'd0))));
end

always_comb begin
IF_instr = ready ? inst_rdata : 32'd63;
end

always_comb begin
IF_PC_input = EX_jump_sel ? EX_jump_addr : (PC + 32'd4);
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
if ((ID_opc == 6'd0) || ((ID_opc == 6'd1) || ((ID_opc == 6'd6) || ((ID_opc == 6'd9) || ((ID_opc == 6'd10) || (ID_opc == 6'd11)))))) begin
ID_func = ID_instr[9:6];
end else begin
ID_func = 4'd9;
end
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
ID_addrA_enable = ID_instr[23];
ID_addrB_enable = ID_instr[16];
ID_addrW_enable = ID_instr[31];
ID_immA = {32'($signed(ID_instr[22:17]))};
ID_immB = {32'($signed(ID_instr[15:10]))};
ID_immW = {32'($signed(ID_instr[30:25]))};
/*
ID_read_dataA_updated = ((ID_addrA == WB_addrW) && (WB_write_reg && WB_state_flag)) ? WB_write_data : ID_read_dataA;
ID_read_dataB_updated = ((ID_addrB == WB_addrW) && (WB_write_reg && WB_state_flag)) ? WB_write_data : ID_read_dataB;
ID_read_dataW_updated = ((ID_addrW == WB_addrW) && (WB_write_reg && WB_state_flag)) ? WB_write_data : ID_read_dataW;
*/
end

always_comb begin
if (ID_EX_write_enable) begin
EX_isAcc = EX_opc == 6'd8;
EX_PC_sel = (EX_opc == 6'd9) ? 2'd1 : ((EX_opc == 6'd10) ? 2'd2 : ((EX_opc == 6'd11) ? 2'd3 : 2'd0));
end
end

always_comb begin
EX_dataA_updated = (EX_ForwardA == 3'd0) ? EX_dataA : ((EX_ForwardA == 3'd1) ? WB_write_data : ((EX_ForwardA == 3'd2) ? MEM_ALU_res : ((EX_ForwardA == 3'd3) ? MEM_SHIFT_res : ((EX_ForwardA == 3'd4) ? (MEM_PC + 32'd4) : ((EX_ForwardA == 3'd5) ? MEM_imm_updated : ((EX_ForwardA == 3'd6) ? 32'd0 : 32'd0))))));
EX_dataB_updated = (EX_ForwardB == 3'd0) ? EX_dataB : ((EX_ForwardB == 3'd1) ? WB_write_data : ((EX_ForwardB == 3'd2) ? MEM_ALU_res : ((EX_ForwardB == 3'd3) ? MEM_SHIFT_res : ((EX_ForwardB == 3'd4) ? (MEM_PC + 32'd4) : ((EX_ForwardB == 3'd5) ? MEM_imm_updated : ((EX_ForwardB == 3'd6) ? 32'd0 : 32'd0))))));
EX_dataW_updated = (EX_ForwardW == 3'd0) ? EX_dataW : ((EX_ForwardW == 3'd1) ? WB_write_data : ((EX_ForwardW == 3'd2) ? MEM_ALU_res : ((EX_ForwardW == 3'd3) ? MEM_SHIFT_res : ((EX_ForwardW == 3'd4) ? (MEM_PC + 32'd4) : ((EX_ForwardW == 3'd5) ? MEM_imm_updated : ((EX_ForwardW == 3'd6) ? 32'd0 : 32'd0))))));
end

always_comb begin
EX_ALU_input1 = (EX_opc == 6'd9) ? EX_PC : EX_dataA_updated;
EX_ALU_input2 = (EX_opc == 6'd9) ? EX_dataA_updated : EX_dataB_updated;
end

always_comb begin
EX_compute_enable = (state == 3'd0) && ((!(MEM_opc == 6'd16)) || ((MEM_opc == 6'd16) && ((!(EX_ForwardA == 3'd0)) || (!(EX_ForwardB == 3'd0)))));
end

always_comb begin
ALU_sum = (33'({EX_ALU_input1}) + 33'({EX_ALU_input2})) + ((EX_func == 4'd1) ? 33'({EX_carry_flag}) : 33'd0);
ALU_prod = 64'({EX_ALU_input1}) * 64'({EX_ALU_input2});
if (EX_compute_enable) begin
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
if (EX_compute_enable) begin
case (EX_func[1:0])
2'd0 : EX_SHIFT_res = EX_dataA_updated << EX_dataB_updated;
2'd1 : EX_SHIFT_res = EX_dataA_updated >> EX_dataB_updated;
2'd2 : EX_SHIFT_res = {$signed(EX_dataA_updated) >>> (EX_dataB_updated)};
2'd3 : begin
shift_sh = 32'({EX_dataB_updated[4:0]});
EX_SHIFT_res = (EX_dataA_updated >> shift_sh) | (EX_dataA_updated << (32'd32 - shift_sh));
end
endcase
end
end

always_comb begin
if (EX_PC_sel == 2'd1) begin
EX_jump_sel = 1;
EX_jump_addr = EX_ALU_res;
end else begin
if (((EX_PC_sel == 2'd2) && (EX_ALU_res == 32'd0)) || ((EX_PC_sel == 2'd3) && (!(EX_ALU_res == 32'd0)))) begin
EX_jump_sel = 1;
EX_jump_addr = EX_PC + EX_dataW_updated;
end else begin
EX_jump_sel = 0;
EX_jump_addr = 32'd0;
end
end
end

always_comb begin
if ((state == 3'd0) && (!(MEM_opc == 6'd16))) begin
EX_dataA_rec = EX_dataA_updated;
EX_dataB_rec = EX_dataB_updated;
EX_dataW_rec = EX_dataW_updated;
end else begin
if ((state == 3'd0) && (MEM_opc == 6'd16)) begin
if (!(EX_ForwardA == 3'd0)) begin
EX_dataA_rec = EX_dataA_updated;
end
if (!(EX_ForwardB == 3'd0)) begin
EX_dataB_rec = EX_dataB_updated;
end
if (!(EX_ForwardW == 3'd0)) begin
EX_dataW_rec = EX_dataW_updated;
end
end
end
end

always_comb begin
if ((EX_write_enable && MEM_state_flag) || MEM_enable) begin
MEM_read_mem = (MEM_opc == 6'd4) || (MEM_opc == 6'd5);
MEM_write_mem = MEM_opc == 6'd2;
MEM_write_mem_byte = MEM_opc == 6'd3;
MEM_isInterrupt = MEM_opc == 6'd12;
end
end

always_comb begin
MEM_imm_updated = (MEM_opc == 6'd14) ? {MEM_imm[8:0], MEM_dataW[22:0]} : MEM_imm;
end

always_comb begin
WB_read_data = data_rdata;
WB_read_data_byte = (WB_dataA[1:0] == 2'd0) ? 32'({WB_read_data[7:0]}) : ((WB_dataA[1:0] == 2'd1) ? 32'({WB_read_data[15:8]}) : ((WB_dataA[1:0] == 2'd2) ? 32'({WB_read_data[23:16]}) : 32'({WB_read_data[31:24]})));
if ((MEM_write_enable && WB_state_flag) || WB_enable) begin
WB_isOut = WB_opc == 6'd6;
WB_data_sel = ((WB_opc == 6'd0) || (WB_opc == 6'd6)) ? 3'd0 : ((WB_opc == 6'd1) ? 3'd1 : ((WB_opc == 6'd7) ? 3'd2 : ((WB_opc == 6'd9) ? 3'd3 : (((WB_opc == 6'd13) || (WB_opc == 6'd14)) ? 3'd4 : ((WB_opc == 6'd4) ? 3'd5 : ((WB_opc == 6'd5) ? 3'd6 : ((WB_opc == 6'd8) ? 3'd7 : 3'd0)))))));
end
WB_write_data = (WB_data_sel == 3'd0) ? WB_ALU_res : ((WB_data_sel == 3'd1) ? WB_SHIFT_res : ((WB_data_sel == 3'd2) ? 32'({data_in}) : ((WB_data_sel == 3'd3) ? (WB_PC + 32'd4) : ((WB_data_sel == 3'd4) ? WB_imm : ((WB_data_sel == 3'd5) ? WB_read_data : ((WB_data_sel == 3'd6) ? WB_read_data_byte : acc_res))))));
end

always_comb begin
if ((state == 3'd3) || (state == 3'd5)) begin
IF_PC_write_enable = 0;
ID_ID_write_enable = 0;
ID_flush_flag = 1;
ID_EX_write_enable = 0;
EX_NOP_flag = 0;
MEM_state_flag = 0;
MEM_NOP_flag = 0;
WB_state_flag = 0;
end else begin
if ((state == 3'd1) || ((state == 3'd2) || ((state == 3'd4) || (state == 3'd6)))) begin
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
if ((MEM_opc == 6'd2) || ((MEM_opc == 6'd3) || ((MEM_opc == 6'd4) || ((MEM_opc == 6'd5) || (MEM_opc == 6'd12))))) begin
IF_PC_write_enable = 0;
ID_ID_write_enable = 0;
ID_flush_flag = 0;
ID_EX_write_enable = 0;
EX_NOP_flag = 0;
MEM_state_flag = 0;
MEM_NOP_flag = 1;
WB_state_flag = 1;
end else begin
if (EX_jump_sel) begin
IF_PC_write_enable = 1;
ID_ID_write_enable = 0;
ID_flush_flag = 1;
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
ID_instr = IF_instr;
end else begin
if (ID_flush_flag) begin
ID_instr = 32'd63;
end
end
ID_addrA <= ID_instr[22:17];
ID_addrB <= ID_instr[15:10];
ID_addrW <= ID_instr[30:25];
end

always_ff @ (posedge clk) begin
if (WB_write_reg && WB_state_flag) begin
R[WB_addrW] <= WB_write_data;
end
end

always_ff @ (posedge clk) begin
ID_read_dataA = R[ID_addrA];
ID_read_dataB = R[ID_addrB];
ID_read_dataW = R[ID_addrW];
end

always_ff @ (posedge clk) begin
if (ID_EX_write_enable) begin
EX_PC <= ID_PC;
EX_imm <= ID_imm;
EX_dataA = ID_addrA_enable ? ID_immA : (((ID_addrA == WB_addrW) && (WB_write_reg && WB_state_flag)) ? WB_write_data : ID_read_dataA);
EX_dataB = ID_addrB_enable ? ID_immB : (((ID_addrB == WB_addrW) && (WB_write_reg && WB_state_flag)) ? WB_write_data : ID_read_dataB);
EX_dataW = ID_addrW_enable ? ID_immW : (((ID_addrW == WB_addrW) && (WB_write_reg && WB_state_flag)) ? WB_write_data : ID_read_dataW);
EX_write_enable <= 1;
EX_addrA_enable = ID_addrA_enable;
EX_addrB_enable = ID_addrB_enable;
EX_addrW_enable = ID_addrW_enable;
EX_addrA = ID_addrA;
EX_addrB = ID_addrB;
EX_addrW <= ID_addrW;
EX_opc <= EX_NOP_flag ? 6'd16 : ID_opc;
EX_func = ID_func;
end else begin
EX_write_enable <= 0;
end
end

always_ff @ (posedge clk) begin
if ((EX_write_enable && MEM_state_flag) || MEM_enable) begin
MEM_PC <= EX_PC;
MEM_dataA <= EX_dataA_rec;
MEM_dataB <= EX_dataB_rec;
MEM_dataW = EX_dataW_rec;
MEM_imm = EX_imm;
MEM_ALU_res <= EX_ALU_res;
MEM_SHIFT_res <= EX_SHIFT_res;
MEM_write_enable <= 1;
MEM_addrW <= EX_addrW;
MEM_opc <= EX_opc;
MEM_write_reg = (EX_opc == 6'd0) || ((EX_opc == 6'd1) || ((EX_opc == 6'd4) || ((EX_opc == 6'd5) || ((EX_opc == 6'd6) || ((EX_opc == 6'd7) || ((EX_opc == 6'd8) || ((EX_opc == 6'd9) || ((EX_opc == 6'd13) || (EX_opc == 6'd14)))))))));
end else begin
MEM_write_enable <= 0;
end
if (MEM_NOP_flag) begin
MEM_opc <= 6'd16;
end
end

always_ff @ (posedge clk) begin
if ((MEM_write_enable && WB_state_flag) || WB_enable) begin
WB_PC = MEM_PC;
WB_dataA = MEM_dataA;
WB_imm = MEM_imm_updated;
WB_ALU_res = MEM_ALU_res;
WB_SHIFT_res = MEM_SHIFT_res;
WB_write_reg <= (MEM_opc == 6'd0) || ((MEM_opc == 6'd1) || ((MEM_opc == 6'd4) || ((MEM_opc == 6'd5) || ((MEM_opc == 6'd6) || ((MEM_opc == 6'd7) || ((MEM_opc == 6'd8) || ((MEM_opc == 6'd9) || ((MEM_opc == 6'd13) || (MEM_opc == 6'd14)))))))));
WB_addrW <= MEM_addrW;
WB_opc = MEM_opc;
end
end

always_ff @ (posedge clk) begin
if (error == 2'd0) begin
case (state)
3'd0 : begin
data_out <= WB_isOut ? WB_ALU_res[9:0] : data_out;
MEM_enable <= 0;
WB_enable <= 0;
if (!ready) begin
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
if (EX_isAcc) begin
state = 3'd2;
command <= 3'd0;
acc_arg <= EX_dataA_updated;
acc_arg_ready <= 1;
end
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
state = 3'd6;
end
end
command <= 3'd0;
end
3'd2 : begin
if (acc_res_ready && (!acc_arg_ready)) begin
state = 3'd6;
end
acc_arg_ready <= 0;
end
3'd3 : if (mem_start_ready) begin
state = 3'd1;
command <= 3'd1;
end
3'd4 : if (interrupt_ack) begin
state = 3'd6;
interrupt_req <= 0;
end
3'd6 : begin
state = 3'd0;
command <= 3'd1;
MEM_enable <= 1;
WB_enable <= 1;
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
