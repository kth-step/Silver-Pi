`timescale 1ns / 1ps

/* Notable changes compared to the previous version:
   1. Only keep the instruction cache, data cache removed.
   2. Data memory operations (load and store) are directly sent to the main memory via AXI.
   3. Update the data structure and code to fetch 16 32-bits instructions in one round.
   4. If the command is 1 (only fetch the next instruction), produce the hit/miss (+ inst_rdata if hit) in one clock cycle.
   5. The cache bram is changed to enable "assign inst_out = ram[inst_addr];".  
*/

module cache_v2(
    input clk,

    //
    // Processor interface
    //
    
    // 000 = nothing,
    // 001 = read instruction,
    // 010 = read instruction + read data,
    // 011 = read instruction + write data
    // 100 = clear cache (based on data addr)
    input[2:0] command,
    // ready in AXI-sense, command != 00 && ready => start new transaction
    output ready,
    output hit,
    
    // data and instruction addr input
    input[31:0] data_addr,
    input[31:0] inst_addr,
    
    // (data) write input
    input[31:0] data_wdata,
    input[3:0] data_wstrb, // mask for byte writes
    
    // data and instruction read output
    output logic[31:0] data_rdata,
    output logic[31:0] inst_rdata,
    output logic[31:0] inst_rdata_cache,
    
    // error reporting, 00 = no error, 01 = AXI error, 10 = internal cache error
    output reg[1:0] error = 0,
    
    //
    // Mem start interface
    //
    input wire mem_start_valid,
    input wire[31:0] mem_start_input,
    
    //
    // AXI memory (data port)
    //
    output reg mem_d_awvalid = 0,
    input wire mem_d_awready,
    output reg[31:0] mem_d_awaddr,
    output reg[7:0] mem_d_awlen = 0,
    output reg[2:0] mem_d_awsize = 'b010,
    output reg[1:0] mem_d_awburst = 0,
    
    output reg mem_d_wvalid = 0,
    input wire mem_d_wready,
    output reg[31:0] mem_d_wdata,
    output reg[3:0] mem_d_wstrb,
    output reg mem_d_wlast = 1,
    
    input wire[1:0] mem_d_bresp,
    input wire mem_d_bvalid,
    output reg mem_d_bready = 1,
    
    output reg mem_d_arvalid = 0,
    input wire mem_d_arready,
    output reg[31:0] mem_d_araddr,
    output reg[7:0] mem_d_arlen = 0,
    output reg[2:0] mem_d_arsize = 'b010,
    output reg[1:0] mem_d_arburst = 0,
    
    input wire[31:0] mem_d_rdata,
    input wire[1:0] mem_d_rresp,
    input wire mem_d_rlast,
    input wire mem_d_rvalid,
    output reg mem_d_rready = 1,
    
    //
    // AXI memory (instruction port)
    //
    output reg mem_i_awvalid = 0,
    input wire mem_i_awready,
    output reg[31:0] mem_i_awaddr,
    output reg[7:0] mem_i_awlen = 0,
    output reg[2:0] mem_i_awsize = 'b010,
    output reg[1:0] mem_i_awburst = 0,
    
    output reg mem_i_wvalid = 0,
    input wire mem_i_wready,
    output reg[31:0] mem_i_wdata,
    output reg[3:0] mem_i_wstrb,
    output reg mem_i_wlast = 1,
    
    input wire[1:0] mem_i_bresp,
    input wire mem_i_bvalid,
    output reg mem_i_bready = 1,
    
    output reg mem_i_arvalid = 0,
    input wire mem_i_arready,
    output reg[31:0] mem_i_araddr,
    output reg[7:0] mem_i_arlen = 15,
    output reg[2:0] mem_i_arsize = 'b010,
    output reg[1:0] mem_i_arburst = 1,
    
    input wire[31:0] mem_i_rdata,
    input wire[1:0] mem_i_rresp,
    input wire mem_i_rlast,
    input wire mem_i_rvalid,
    output reg mem_i_rready = 1
    );

// Sizes
//
// Cache size: 2^16 bytes
// Blocks are 64 bytes, i.e. 2^6
// Number of blocks are 1024, i.e. 2^10

// Address structure
// NOTE: tag bits are the ms-bits here
typedef struct packed {
  logic[15:0] tag;
  logic[9:0] index;
  logic[5:0] block_offset;
} address;

// BRAM structure
typedef struct packed {
  logic active;
  logic[15:0] tag;
  logic[511:0] data;
} cache_block;

logic [31:0] mem_start = 0;

// Instruction BRAM
logic[511:0] inst_buffer;

logic inst_ibram_we = 0;
logic[9:0] inst_ibram_addr;
cache_block inst_ibram_in;
cache_block inst_ibram_out;
                 
cache_bram_v2 ibram(.clk(clk), .inst_we(inst_ibram_we), .inst_addr(inst_ibram_addr), .inst_in(inst_ibram_in), .inst_out(inst_ibram_out));

// Internal state

enum { INIT, BRAM_WAIT, BRAM_RESP, MEM_WORK, ERROR } state = INIT;

typedef enum { BLOCK_NONE, BLOCK_HIT, BLOCK_OVERWRITE, BLOCK_ERROR } block_state;
block_state inst_block_state = BLOCK_NONE;

logic[2:0] data_write_check;
logic[5:0] inst_block_read;

logic data_inf_error = 0;

logic data_inf_done = 1;
logic inst_block_read_done = 1;

assign ready = (state == INIT);

logic[2:0] later_command;

address later_data_addr;
address later_inst_addr;

logic[31:0] later_data_wdata;
logic[3:0] later_data_wstrb;

function block_state inst_block_action;
    input cache_block old_inst_block;
    input address addr;
begin
    if (old_inst_block.active && old_inst_block.tag == addr.tag)
        inst_block_action = BLOCK_HIT;
    else
        inst_block_action = BLOCK_OVERWRITE;
end
endfunction

// mem_start handling
always_ff @ (posedge clk) begin
   if (mem_start_valid) begin
      mem_start <= mem_start_input;
   end
end

assign later_inst_addr = mem_start + inst_addr;
assign inst_ibram_addr = later_inst_addr.index;


// check hit/miss when command == 1
assign hit = ((command == 1) && (inst_ibram_out.active) && (inst_ibram_out.tag == later_inst_addr.tag));
assign inst_rdata_cache = hit ? inst_ibram_out.data[9'd8*later_inst_addr.block_offset +: 32] : 32'h0000003F;

always_ff @ (posedge clk) begin
    case (state)
    INIT: begin
        inst_ibram_we <= 0;
        
        if (((command != 0) && (command != 1)) || ((command == 1) && (hit == 0))) begin
            later_command = command;
            later_data_addr = mem_start + data_addr;
            later_data_wdata = data_wdata;
            later_data_wstrb = data_wstrb;
            
            // Simplifies implementation for now, know that the CakeML compiler
            // will not generate self-modifying code like this:
            if (later_data_addr == later_inst_addr) begin
                error <= 2;
                state <= ERROR;
            end else
                state <= BRAM_WAIT;
        end
 /*       
        else if (command == 1) begin
           later_command = command;
           inst_block_state = inst_block_action(inst_ibram_out, later_inst_addr);
           
           case (inst_block_state)
           BLOCK_HIT: begin 
              //inst_rdata <= inst_ibram_out.data[9'd8*later_inst_addr.block_offset +: 32];
              inst_buffer = inst_ibram_out.data;
              state <= INIT;
           end
           
           BLOCK_OVERWRITE: begin
              state <= BRAM_WAIT;
           end
           endcase
        end
*/        
    end
        
    BRAM_WAIT:
        state <= BRAM_RESP;
        
    BRAM_RESP: begin
        inst_block_state = inst_block_action(inst_ibram_out, later_inst_addr);
        
        //
        // Data
        //
        
        // Data read and write commands are sent to the main memory directly.
        // write command
        if (later_command == 3) begin
            mem_d_awvalid <= 1;
            mem_d_awaddr <= later_data_addr;
        
            mem_d_wvalid <= 1;
            data_write_check = 0;
            mem_d_wdata <= later_data_wdata;
            mem_d_wstrb <= later_data_wstrb;
            
            data_inf_done = 0;
        end
        
        // read command
        if (later_command == 2) begin
            mem_d_arvalid <= 1;
            mem_d_araddr <= later_data_addr;
            
            data_inf_done = 0;
        end
        
        //
        // Inst
        //
        
        case (inst_block_state)
        BLOCK_HIT:
            inst_buffer = inst_ibram_out.data;
        
        BLOCK_OVERWRITE: begin
            mem_i_arvalid <= 1;
            mem_i_araddr <= {later_inst_addr[31:6], 6'b0};
            
            inst_block_read = 0;
        
            inst_block_read_done = 0;
        end
        
        endcase
        
        //
        // State
        //
        
        if ((later_command != 2) && (later_command != 3) && inst_block_state == BLOCK_HIT)
            state <= INIT;
        else
            state <= MEM_WORK;
    end
    
    MEM_WORK: begin
        //
        // Data
        //
    
        // Write address
        if (mem_d_awvalid && mem_d_awready) begin
            mem_d_awvalid <= 0;
            data_write_check += 1;
        end
        
        // Write transfer
        if (mem_d_wvalid && mem_d_wready) begin
            mem_d_wvalid <= 0;
            data_write_check += 1;
        end
        
        // Write response
        if (mem_d_bvalid && mem_d_bready) begin
            data_inf_done = 1;
            
            if (mem_d_bresp != 0 || data_write_check != 2)
                data_inf_error = 1;
        end
    
        // Read address
        if (mem_d_arvalid && mem_d_arready)
            mem_d_arvalid <= 0;
    
        // Read response
        if (mem_d_rvalid && mem_d_rready) begin
            data_rdata <= mem_d_rdata;
            data_inf_done = 1;
                        
            if (mem_d_rresp != 0 || mem_d_rlast != 1) begin
                data_inf_error = 1;    
            end
        end
        
        //
        // Inst
        //
        
        // Read address
        if (mem_i_arvalid && mem_i_arready)
            mem_i_arvalid <= 0;
    
        // Read response
        if (mem_i_rvalid && mem_i_rready) begin
            if (mem_i_rlast)
                inst_block_read_done = 1;
                        
            if (mem_i_rresp == 0) begin
                inst_buffer[9'd32*inst_block_read +: 32] = mem_i_rdata;
                inst_block_read++;
            end else
                inst_block_state = BLOCK_ERROR;
        end
        
        //
        // Final action...
        //
        
        // Write and read ready?
        if (data_inf_done && inst_block_read_done) begin
            if (data_inf_error || inst_block_state == BLOCK_ERROR) begin
                error <= 1;
                state <= ERROR;
            end else begin
                
                //
                // Inst
                //
                if (inst_block_state == BLOCK_OVERWRITE) begin
                    inst_block_state = BLOCK_HIT;
                    
                    inst_ibram_we <= 1;
                    inst_ibram_in <= {1'b1, later_inst_addr.tag, inst_buffer};
                end
            end
        end
    end
        
    endcase
    
    if (data_inf_done && inst_block_state == BLOCK_HIT) begin
        
        // Always update inst_rdata...  
        inst_rdata <= inst_buffer[9'd8*later_inst_addr.block_offset +: 32];    
    
        inst_block_state = BLOCK_NONE;
        state <= INIT;
    end
end

endmodule