`timescale 1ns / 1ps

module processor(
  input clk,
  input logic[1:0] data_in,
  output logic[31:0] PC = 32'd0,
  output logic[9:0] data_out,
  output logic interrupt_req = 0,
  output logic[2:0] command = 3'd0,
  output logic[31:0] data_addr = 32'hffff_ffff,
  output logic[31:0] data_wdata,
  output logic[3:0] data_wstrb,
  input logic[1:0] error,
  input logic ready,
  input logic[31:0] data_rdata,
  input logic[31:0] inst_rdata,
  input logic mem_start_ready,
  input logic interrupt_ack);

logic[2:0] state = 3'd3;
logic[63:0][31:0] R = 0;
logic CarryFlag;
logic OverflowFlag;
logic[31:0] i;
logic[5:0] instruction;
logic[31:0] ALU_res;
logic[5:0] delay_write;
logic[2:0] do_delay_write = 3'd5;
logic[31:0] acc_arg;
logic acc_arg_ready = 0;
logic do_interrupt = 0;
logic acc_res_ready;
logic[31:0] acc_res;
logic[1:0] acc_state;

always_ff @ (posedge clk) begin
automatic logic[31:0] wV;
automatic logic[31:0] shift_sh;
automatic logic[32:0] ALU_sum;
automatic logic[31:0] ALU_sub;
automatic logic[31:0] ALU_snd;
automatic logic[63:0] ALU_prod;
automatic logic[31:0] ALU_fst;
automatic logic[31:0] aV;
automatic logic[31:0] PC_next;
automatic logic[5:0] x;
automatic logic[31:0] bV;
automatic logic[3:0] func;

if (error == 2'd0) begin
case (state)
3'd0 : begin
if (i[24]) begin
if (i[31]) begin
instruction = 6'd13;
end else begin
if (i[23:9] == 15'd0) begin
instruction = 6'd14;
end else begin
instruction = 6'd15;
end
end
end else begin
if ((i[5:0] == 6'd10) || ((i[5:0] == 6'd11) || (i[5:0] == 6'd12))) begin
instruction = i[5:0];
end else begin
if (i[31]) begin
instruction = 6'd15;
end else begin
if (i[5:0] < 6'd10) begin
instruction = i[5:0];
end else begin
instruction = 6'd15;
end
end
end
end
wV = i[31] ? {32'($signed(i[30:25]))} : R[i[30:25]];
aV = i[23] ? {32'($signed(i[22:17]))} : R[i[22:17]];
bV = i[16] ? {32'($signed(i[15:10]))} : R[i[15:10]];
func = ((instruction == 6'd0) || ((instruction == 6'd6) || ((instruction == 6'd9) || ((instruction == 6'd10) || (instruction == 6'd11))))) ? i[9:6] : 4'd9;
ALU_fst = (instruction == 6'd9) ? PC : aV;
ALU_snd = (instruction == 6'd9) ? aV : bV;
ALU_sum = (33'({ALU_fst}) + 33'({ALU_snd})) + ((func == 4'd1) ? 33'({CarryFlag}) : 33'd0);
ALU_prod = 64'({ALU_fst}) * 64'({ALU_snd});
case (func)
4'd0 : begin
ALU_res = ALU_sum[31:0];
CarryFlag = ALU_sum[32];
OverflowFlag = (ALU_fst[31] == ALU_snd[31]) && (ALU_sum[31] != ALU_fst[31]);
end
4'd1 : begin
ALU_res = ALU_sum[31:0];
CarryFlag = ALU_sum[32];
end
4'd2 : begin
ALU_sub = ALU_fst - ALU_snd;
OverflowFlag = (ALU_fst[31] != ALU_snd[31]) && (ALU_sub[31] != ALU_fst[31]);
ALU_res = ALU_sub;
end
4'd3 : ALU_res = 32'({CarryFlag});
4'd4 : ALU_res = 32'({OverflowFlag});
4'd5 : ALU_res = ALU_fst + 32'd1;
4'd6 : ALU_res = ALU_fst - 32'd1;
4'd7 : ALU_res = ALU_prod[31:0];
4'd8 : ALU_res = ALU_prod[63:32];
4'd9 : ALU_res = ALU_fst & ALU_snd;
4'd10 : ALU_res = ALU_fst | ALU_snd;
4'd11 : ALU_res = ALU_fst ^ ALU_snd;
4'd12 : ALU_res = 32'({ALU_fst == ALU_snd});
4'd13 : ALU_res = 32'({{$signed(ALU_fst) < $signed(ALU_snd)}});
4'd14 : ALU_res = 32'({ALU_fst < ALU_snd});
4'd15 : ALU_res = ALU_snd;
endcase
PC_next = PC + 32'd4;
case (instruction)
6'd0 : begin
R[i[30:25]] = ALU_res;
PC <= PC_next;
command <= 3'd1;
state = 3'd1;
end
6'd1 : begin
case (i[7:6])
2'd0 : R[i[30:25]] = aV << bV;
2'd1 : R[i[30:25]] = aV >> bV;
2'd2 : R[i[30:25]] = {$signed(aV) >>> (bV)};
2'd3 : begin
shift_sh = bV % 32'd32;
R[i[30:25]] = (aV >> shift_sh) | (aV << (32'd32 - shift_sh));
end
endcase
PC <= PC_next;
command <= 3'd1;
state = 3'd1;
end
6'd2 : begin
data_wstrb <= 4'd15; // mem_data_mask
data_wdata <= aV; // mem_data_in
data_addr <= bV; // mem_data_addr
PC <= PC_next;
command <= 3'd3;
state = 3'd1;
end
6'd3 : begin
data_wstrb <= 4'd1 << 4'({bV[1:0]});
data_addr <= bV;
PC <= PC_next;
command <= 3'd3;
state = 3'd1;
case (bV[1:0])
2'd0 : data_wdata[7:0] <= aV[7:0];
2'd1 : data_wdata[15:8] <= aV[7:0];
2'd2 : data_wdata[23:16] <= aV[7:0];
2'd3 : data_wdata[31:24] <= aV[7:0];
endcase
end
6'd4 : begin
delay_write = i[30:25];
do_delay_write = 3'd4;
data_addr <= aV;
PC <= PC_next;
command <= 3'd2;
state = 3'd1;
end
6'd5 : begin
delay_write = i[30:25];
do_delay_write = 3'({aV[1:0]});
data_addr <= aV;
PC <= PC_next;
command <= 3'd2;
state = 3'd1;
end
6'd6 : begin
R[i[30:25]] = ALU_res;
data_out <= ALU_res[9:0];
PC <= PC_next;
command <= 3'd1;
state = 3'd1;
end
6'd7 : begin
R[i[30:25]] = 32'({data_in});
PC <= PC_next;
command <= 3'd1;
state = 3'd1;
end
6'd8 : begin
delay_write = i[30:25];
acc_arg <= aV;
acc_arg_ready <= 1;
PC <= PC_next;
state = 3'd2;
end
6'd9 : begin
R[i[30:25]] = PC_next;
PC <= ALU_res;
command <= 3'd1;
state = 3'd1;
end
6'd10 : begin
if (ALU_res == 32'd0) begin
PC <= PC + wV;
end else begin
PC <= PC_next;
end
command <= 3'd1;
state = 3'd1;
end
6'd11 : begin
if (ALU_res != 32'd0) begin
PC <= PC + wV;
end else begin
PC <= PC_next;
end
command <= 3'd1;
state = 3'd1;
end
6'd12 : begin
PC <= PC_next;
do_interrupt = 1;
data_addr <= 32'd0;
command <= 3'd4;
state = 3'd1;
end
6'd13 : begin
if (i[23]) begin
R[i[30:25]] = 32'd0 - 32'({i[22:0]});
end else begin
R[i[30:25]] = 32'({i[22:0]});
end
PC <= PC_next;
command <= 3'd1;
state = 3'd1;
end
6'd14 : begin
x = i[30:25];
R[x][31:23] = i[8:0];
PC <= PC_next;
command <= 3'd1;
state = 3'd1;
end
endcase
end
3'd1 : begin
if (ready && (command == 3'd0)) begin
case (do_delay_write)
3'd0 : R[delay_write] = 32'({data_rdata[7:0]});
3'd1 : R[delay_write] = 32'({data_rdata[15:8]});
3'd2 : R[delay_write] = 32'({data_rdata[23:16]});
3'd3 : R[delay_write] = 32'({data_rdata[31:24]});
3'd4 : R[delay_write] = data_rdata;
endcase
do_delay_write = 3'd5;
i = inst_rdata;
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
R[delay_write] = acc_res;
command <= 3'd1;
state = 3'd1;
end
acc_arg_ready <= 0;
end
3'd3 : if (mem_start_ready) begin
command <= 3'd1;
state = 3'd1;
end
3'd4 : if (interrupt_ack) begin
interrupt_req <= 0;
state = 3'd0;
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
