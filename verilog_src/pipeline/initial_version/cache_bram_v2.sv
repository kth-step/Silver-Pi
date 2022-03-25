`timescale 1ns / 1ps

module cache_bram_v2 (clk, inst_we, inst_addr, inst_in, inst_out);

input clk;

input inst_we;
input [9:0] inst_addr;
input [528:0] inst_in;
output logic [528:0] inst_out;

logic [528:0] ram [2**10 - 1:0];

initial begin
  for (integer i = 0; i < 2**10; i = i + 1) begin
    ram[i] = 0;
  end
end

always @(posedge clk)
begin
  if (inst_we) begin
     ram[inst_addr] <= inst_in;
  end
end

assign inst_out = ram[inst_addr];

endmodule