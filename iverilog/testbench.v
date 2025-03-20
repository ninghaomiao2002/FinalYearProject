/*  Copyright 2021-2024 Philippos Papaphilippou

	You are free to use, learn from, modify and distribute this creative work under 
	  the following conditions:
	1. No code, text, or other elements of this work can be used as an input to models
	  for the purposes of training. Generative A.I. and language models are prohibited
	  from using this work. These do not include search engines and related tools whose
	  main purpose is to index and appropriately point to the original source and author.
	2. It comes under no warranties.
	3. Any modification to the code shall be made available in the style of GNU General
	  Public License v2.0 (GPL-2.0), but published under the same license (not GPL-2.0,
	  and clause 7 still refers to the original copyright holder).
	4. A proper attribution of the author (copyright holder) is required when the work 
	  is used. (If applicable, it would be appreciated to cite the related academic
	  publication that introduced the work.)
	5. It cannot be used for commercial purposes unless specific permission is given by
	  the author. 
	6. A redistribution shall include this license in its entirety.
	7. The author has the right to change this license for future versions of this work,
	  as well as to update and clarify the author's original intentions of the current
	  version, such as with regard to what is considered "fair use" by the author for
	  future entities and technologies.  
*/

`define StackPointer 32'h0ffffff0

// Use the StartAddress to set the start address of the binary
// Use BINARY to set the path of the binary for simulation

// stream.bin
`define BINARY "stream.bin"
`define StartAddress 32'h00010584 // stream.bin

// `define BINARY "firmware_sort.bin"
// `define StartAddress 32'h00010620




`include "system.v"

`define BMEM_capacity 16*16*16*16*16*16*16
`define ReadLatency 5
`define WriteLatency 10 // must be > `DL2subblocks


// This module represents main memory and is only used in simulation

module Memory (clk, reset, addr, en, we, dinDstrobe, din, doutDstrobe, dout, dready, accR, accW);
	input clk, reset;
	input [`DADDR_bits-1:0] addr;	
    input en;
    input we;    
    input  [`DL2subblocks_Log2-1:0] dinDstrobe;
    input [`DL2block/`DL2subblocks-1:0] din;
    output reg  [`DL2subblocks_Log2-1:0] doutDstrobe;
    output reg [`DL2block/`DL2subblocks-1:0] dout;
    output reg dready;
    output wire accR;
    output wire accW;
    
    (* ram_style = "block" *) reg [`DL2block-1:0] block_ram [`BMEM_capacity/(`DL2block/8)-1:0];
    reg [`DL2block-1:0] rdata;


	always @( posedge clk ) begin		
		if (we) begin
			block_ram[addr>>(`DL2block_Log2-3)]
				[`DL2block/`DL2subblocks*(dinDstrobe+1)-1-:`DL2block/`DL2subblocks]<=din;
			if (`DEB)if (dinDstrobe==`DL2subblocks-1) 
				$display("DRAMstore %h at waddr %h w %h",{din,block_ram[addr>>(`DL2block_Log2-3)][`DL2block-`DL2block/`DL2subblocks-1:0]}, addr);
		end else begin            
			rdata<=block_ram[addr>>(`DL2block_Log2-3)];
			if (`DEB) if(en) $display("DRAMload %h from raddr %h index",block_ram[addr>>(`DL2block_Log2-3)], (addr>>(`DL2block_Log2-3))<<(`DL2block_Log2-3),addr>>(`DL2block_Log2-3)); 	
		end
		
	end

	reg [`ReadLatency-1:0] lat;
	reg [`WriteLatency-1:0] latw;
	assign accR=(lat==0 && send_strobe==0);
	assign accW=(latw==0);

	wire [`DL2block/`DL2subblocks-1:0] subblock [`DL2subblocks-1:0];
	genvar i;
	for (i=0; i<`DL2subblocks; i=i+1) begin
		assign subblock[i]=rdata[(`DL2block/`DL2subblocks)*(i+1)-1-:`DL2block/`DL2subblocks];
	end
	
	reg [`DL2subblocks_Log2-1:0] send_strobe;
	always @( posedge clk ) begin
		if (reset) begin
			dready<=0;
			lat<=0;latw<=0; doutDstrobe<=0; send_strobe<=0;
		end else begin
			if (en) lat<=(lat<<1)|en; else lat<=(lat<<1);
			if (we) latw<=(latw<<1)|we; else latw<=(latw<<1);
			
			dready<=0; doutDstrobe<=0;		
			if(lat[`ReadLatency-1]||(send_strobe!=0)) begin
				dready<=1;
				doutDstrobe<=send_strobe;
				send_strobe<=send_strobe+1;
				dout<= subblock[send_strobe];
			end 
			
		end
	end
	
	// synthesis translate_off	
	integer fd, byte_address;
	reg [7:0] value;	
	reg [`DL2block-1:0] word;
	
	initial begin 

		//byte_address=32'h00010000;
		byte_address=32'h00010074;
	    fd = $fopen(`BINARY, "rb"); 
	    
	    if (!fd) $error("could not read file");
	    while (!$feof(fd)) begin
		     $fread(value,fd);
		     word[(byte_address%(`DL2block/8))*8+8-1-:8]=value;
		     if (byte_address%(`DL2block/8)==(`DL2block/8)-1) begin
		     	block_ram[byte_address/(`DL2block/8)]=word;
		     	if (`DEB)$display ("%h at %h %h",word,byte_address/(`DL2block/8),byte_address);
		     	word=0;		     		     	
		     end
		     byte_address=byte_address+1;	
	   end
	   block_ram[byte_address/(`DL2block/8)]=word;
	   if (`DEB)$display ("%h at %h %h",word,byte_address/(`DL2block/8), byte_address);
	   dout=block_ram[0];
	end
	// synthesis translate_on 
	initial begin		
		if (`DEB)$dumpvars(0,clk,reset,addr, en, we, dinDstrobe, din, doutDstrobe, dout, dready, accR, accW);
	end
endmodule // Memory


// synthesis translate_off
module Top_Level();
	reg clk, reset;	

    wire [`DADDR_bits-1:0] addrD;
    wire [`DL2subblocks_Log2-1:0] dinDstrobe;
    wire [`DL2block/`DL2subblocks-1:0] dinD;
    wire [`DL2subblocks_Log2-1:0] doutDstrobe;
    wire [`DL2block/`DL2subblocks-1:0] doutD;       
    wire enD;
    wire weD;
    wire dreadyD;
    
    wire accR;
    wire accW;
    
    reg flush; wire flushed; wire [31:0] debug;
    
    System s0(clk, reset, `StartAddress, `StackPointer,
   	 addrD, dinDstrobe, dinD, doutDstrobe, doutD, enD, weD, dreadyD, accR, accW,
     debug, flush, flushed); 
    
    Memory md(clk, reset, addrD, enD, weD, dinDstrobe, dinD, doutDstrobe, doutD, dreadyD, accR, accW);

	reg [`IADDR_bits-1:0] PCprevt;
	reg [`IADDR_bits-1:0] PCprev;

	integer k;
	initial begin	
		if (`DEB)$dumpfile("gtkwSystem.vcd");
		if (`DEB)$dumpvars(0, clk, reset, addrD, flush, flushed);

		PCprev=-1;
		k=1;
		reset=1;clk=0;flush=0;
		repeat(100) begin		
			clk=1; #10 clk=0; #10;
		end
		reset=0;
		
		// Wait until the source code has called exit()
		while (PCprev!=debug[`IADDR_bits-1:0]) begin	
			PCprevt=debug;
			clk=1; #10 clk=0;  #10;			
			if(!debug[`IADDR_bits]) PCprev=PCprevt;
			k=k+1;	
		end
		
		// And then issue a "flush-writes" command, to update main memory (here used only for debugging)
		flush=1; $display("\nFlushing remaing dirty blocks to DRAMs\n");
		clk=1; #10 clk=0; #10;
		flush=0;
		
	end
endmodule //Top_Level

// synthesis translate_on
