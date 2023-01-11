`timescale 1ns / 1ps

module cache_bram_v2 (clk, inst_we, inst_addr, inst_tag_in, inst_data_in, inst_tag_out, inst_data_out);

input clk;

input inst_we;
input [9:0] inst_addr;
input [17:0] inst_tag_in;
input [255:0] inst_data_in;
output logic [17:0] inst_tag_out;
output logic [255:0] inst_data_out;

reg [17:0] ram_tag [1023:0];
reg [255:0] ram_data [1023:0];

initial begin
  for (integer i = 0; i < 1024; i = i + 1) begin
    ram_tag[i] = 0;
    ram_data[i] = 0;
  end
end

always @(posedge clk)
begin
  if (inst_we) begin
     ram_tag[inst_addr] <= inst_tag_in;
     ram_data[inst_addr] <= inst_data_in;
  end
end

assign inst_tag_out = ram_tag[inst_addr];
assign inst_data_out = ram_data[inst_addr];

endmodule
