module DL2cache (clk, reset, 
		addr, en, we, din, dout, dready, accepting, flush_in,
		addrB, enB, weB, dinBstrobe, dinB, doutBstrobe, doutB, dreadyB, accR, accW, flush_out);
	input clk, reset;
	
	input [`DADDR_bits-1:0] addr;	
    input en;
    input we;    
    input [`VLEN-1:0] din;
    output reg [`VLEN-1:0] dout;
    output dready;
    output accepting;
    input flush_in;
    
    output reg [`DADDR_bits-1:0] addrB;	
    output reg enB;
    output reg /*[`VLEN/8-1:0]*/ weB;    
    input [`DL2subblocks_Log2-1:0] dinBstrobe;
    input [`DL2block/`DL2subblocks-1:0] dinB;
    output reg [`DL2subblocks_Log2-1:0] doutBstrobe;
    output /*reg*/ [`DL2block/`DL2subblocks-1:0] doutB;
    input dreadyB;
    input accR;
    input accW;
    output reg flush_out;
    
    (* ram_style = "block" *) reg [`DL2block/`DL2subblocks-1:0] way [`DL2ways-1:0][`DL2sets*`DL2subblocks-1:0] ;
    reg [`DL2block/`DL2subblocks-1:0] rdata [`DL2ways-1:0];
    reg [`DL2block/`DL2subblocks-1:0] wdata;

	reg [`DADDR_bits-(`DL2block_Log2-3)-`DL2setsLog2-1:0] tag_array [`DL2sets-1:0][`DL2ways-1:0];
    reg [`DL2ways-1:0] dirty [`DL2sets-1:0];
    reg [`DL2ways-1:0] valid [`DL2sets-1:0];
    reg [`DL2ways-1:0] nru_bit [`DL2sets-1:0];

    wire [`DADDR_bits-(`DL2block_Log2-3)-`DL2setsLog2-1:0] tag; 
    assign tag = addr>>(`DL2setsLog2+(`DL2block_Log2-3));
    
    reg [`DADDR_bits-(`DL2block_Log2-3)-`DL2setsLog2-1:0] wtag;
    reg [`DADDR_bits-(`DL2block_Log2-3)-`DL2setsLog2-1:0] wtag_next; reg wvalid;
    
    wire access; assign access = (en||we);  
   
    reg flushing; reg waiting; reg waiting_en;

    reg [`DL2setsLog2+`DL2waysLog2+1-1:0] writethrough_block;
    wire [`DL2setsLog2-1:0] writethrough_set; assign writethrough_set = writethrough_block[`DL2setsLog2+`DL2waysLog2-1:`DL2waysLog2];
    wire [`DL2waysLog2-1:0] writethrough_way; assign writethrough_way = writethrough_block[`DL2waysLog2-1:0];
        
    wire [`DL2setsLog2-1:0] set; assign set = (addr>>(`DL2block_Log2-3)); // modulo implied
    
    wire [`DL2subblocks_Log2-1:0] access_strobe; 
    reg  [`DL2subblocks_Log2-1:0] read_strobe;
    reg  [`DL2subblocks_Log2-1:0] write_strobe;
    assign access_strobe=addr>>(`DL2block_Log2-`DL2subblocks_Log2-3);
    	
	reg [`DADDR_bits-(`DL2block_Log2-3)-`DL2setsLog2-1:0] tag_real; 
    reg [`DL2setsLog2-1:0] set_real; 
    always @(*) begin 
    	if (reset) begin 
    		tag_real=0;set_real=0;
    	end else begin
    		if (access) begin
    			tag_real=tag; set_real=set;
    		end
    	end
    end
    
    wire [`DL2setsLog2+`DL2subblocks_Log2-1:0] subset; 
	assign subset={	(flushing && !waiting)?writethrough_set:set_real,
				access?access_strobe:read_strobe};
		
    reg [`DL2ways-1:0] we_local; reg [`DL2setsLog2-1:0] baddr;
    reg [`DL2setsLog2-1:0] bset;
    reg [`DADDR_bits-1:0] writeback_addr;
    	
    reg hit;  
    reg miss; 
    reg [`DL2waysLog2-1:0] candidate;
            
    genvar j; integer j_;
    
    reg zero_found;        

    for (j=0;j<`DL2ways;j=j+1) begin   
   	
		always @(posedge clk) begin
		
			if (we_local[j]) begin
				way[j][{baddr,write_strobe}]<=wdata;

				if (`DEB)$display("...storing2 %h at set %d addr%h way %d",wdata, baddr,{wtag,baddr,write_strobe,{(`DL2block_Log2-`DL2subblocks_Log2-3){1'b0}}},j);
			end         
			rdata[j]<=way[j][subset];
			if (`DEB)if (en&&hit &&j==candidate) $display("...loading %h from set %d (%d) way %d addr %h tag %h ", way[j][subset], set, subset, j, addr, tag);
 			
		end
	end
	
	reg we_pending; reg[`DL2block/`DL2subblocks/`VLEN-1:0] we_pending_v; 
	reg [`VLEN-1:0] we_pending_data;
	
	reg en_pending; reg [`DL2block/`DL2subblocks/`VLEN-1:0] en_pending_write; reg [`DADDR_bits-1:0] en_pending_addr;
	reg writeback; 

	integer i;
	
	assign accepting = !(we_pending||we||en||(waiting)||flushing); 
	
	reg [`DL2setsLog2-1:0] last_set; reg we_local_prev;	
	reg [(`DL2block_Log2-3)-(`DL2subblocks_Log2)-(`VLEN_Log2-3)-1:0] roffset;
	
	reg [`DL2subblocks_Log2-1:0] waiting_en_strobe;
	reg ready;
	wire load_from_prev_lev=dreadyB && waiting_en && (waiting_en_strobe==dinBstrobe);	
	
	assign dready=ready||load_from_prev_lev;
	
	reg read_once;
	reg [`DL2waysLog2-1:0] hit_way;
	reg [`DL2waysLog2-1:0] miss_way;
	
	wire [`DL2block-1:0] rdata_updated;
	wire hitw;  assign hitw = (wtag==tag_real) && (subset=={baddr,write_strobe}) && wvalid;
	assign rdata_updated=(hitw)?wdata:rdata[hit_way];
	reg from_writeback;
	
	reg [`DL2waysLog2-1:0] flush_way;
	assign doutB=rdata[(flushing&&!waiting)?flush_way:miss_way];
	reg hitw_saved;	
	reg [61:0] hit_count;
	reg [61:0] access_count;
	
	always @( posedge clk ) begin
		if (reset) begin
			for (i=0; i<`DL2sets; i=i+1) begin
				dirty[i]<=0;
				valid[i]<=0;
				nru_bit[i]<=0;
			end
			en_pending<=0; we_pending<=0;
			roffset<=0;	
			writethrough_block<=0;	wvalid<=0; wtag<=0; baddr<=0;
			writeback<=0; waiting<=0; waiting_en<=0; waiting_en_strobe<=0;
			
			flush_out<=0; flushing<=0; read_once<=0; from_writeback<=0; 
			read_strobe<=0; write_strobe<=0; doutBstrobe<=0;flush_way<=0;

			hit_count<=0; access_count<=0;

		end else begin

			we_local <=0; we_pending<=0; ready<=0;
			weB<=0; enB<=0; flush_out<=0; 

			if (flush_in) begin flushing<=1; end
			
			last_set<=set; 
			
			if (en) roffset<=addr[(`DL2block_Log2-`DL2subblocks_Log2-3)-1:(`VLEN_Log2-3)];
			
			
			hit=0; miss=access; zero_found=0;
			for (j_=0;j_<`DL2ways;j_=j_+1) begin
				if (access && ((tag_array[set][j_]==tag) && valid[set][j_])) begin
					hit=1;
					candidate=j_;
					miss=0;
				end
				if (access && (nru_bit[set][j_]==0) && (!zero_found) && (!hit)) begin
					candidate=j_;
					zero_found=1;
				end
			end	
			
			if (access) begin
				access_count<=access_count+1;
				if (`DEB)$display("L2 Access hit %d set %d", hit, set);
				if ((nru_bit[set] /*|(1<<candidate)*/)=={`DL2ways{1'b1}})
					nru_bit[set]<=0;
				nru_bit[set][candidate]<=1;
			end
			
			
			if (hit) begin
				hit_count<=hit_count+1;
				// hit_rate<=(hit_count*100)/access_count;
				$display("L2 hit_count %d, access_count %d",hit_count, access_count);
				if (`DEB)$display("hit set %d tag %h way %h",set, tag, candidate);
				if (en) ready<=1;

				read_strobe<=access_strobe; // needed for rdata_updated
				if (we) begin 

					we_pending<=1;	
					we_pending_v=addr[(`DL2block_Log2-`DL2subblocks_Log2-3)-1:(`VLEN_Log2-3)];

					we_pending_data=din;
					wtag_next=tag; bset=set;
					
					dirty[set][candidate]<=1;											
					write_strobe<=access_strobe;
					//read_strobe<=access_strobe;
					read_strobe<=0;
					if (`DEB)$display("L2write %h at %h was_dirty %h",din,addr, dirty[set][candidate]);					
					
				end	
				hit_way<=candidate;
				hitw_saved<=hitw;
				
			end
			
			if (we_pending  
				) begin
				we_local[hit_way]<=1; wvalid<=1; wtag<=wtag_next; baddr<=bset;
				for (i=0; i<`DL2block/`DL2subblocks/`VLEN; i=i+1) 
					wdata[(i+1)*`VLEN-1-:`VLEN]<= we_pending_v==i?
						we_pending_data:(
						 (hitw_saved)?wdata[(i+1)*`VLEN-1-:`VLEN]:
						 rdata[hit_way][(i+1)*`VLEN-1-:`VLEN]);
	 
				if (`DEB)$display("L2write2 %h at %h was_dirty %b (last_set==set) %d (baddr==set) %d ",rdata_updated,{bset,candidate}, dirty[set],(last_set==set),(baddr==set));				
			end
			
		
			if (miss) begin
				if (`DEB)$display("miss set %d tag %h way %d",set, tag, candidate);
				en_pending_addr<={tag,set,{(`DL2block_Log2-3){1'b0}}};
				//baddr<=set;
				en_pending_write<=addr[(`DL2block_Log2-`DL2subblocks_Log2-3)-1:(`VLEN_Log2-3)];//we<<(addr[(`VLEN_Log2-3)-1:2]*4);	
				//if (we) 
				//	$display("write %h at %h tag %h way %d", din, addr,tag, candidate);	
					
				we_pending_data=din;//<<(addr[(`VLEN_Log2-3)-1:2]*32);				
				
				// for writeback
				read_once<=0; 					
				doutBstrobe<=0;
							
				if (dirty[set][candidate]&&valid[set][candidate]) begin
					if (`DEB)$display("was dirty");
					writeback<=1;
					read_strobe<=0;
					
					from_writeback<=1;
					addrB<={tag_array[set][candidate],set,{(`DL2block_Log2-3){1'b0}}};		
				end else begin 
					from_writeback<=0;
					enB<=accR&&accW; addrB<={tag,set,{(`DL2block_Log2-3){1'b0}}}; //waddrh<=addr;
					en_pending<=!(accR&&accW);					
				end
				
				valid[set][candidate]<=1;
				dirty[set][candidate]<=we;
				tag_array[set][candidate]<=tag;
				
				waiting<=1;
				waiting_en<=en; waiting_en_strobe<=access_strobe;
				wtag<=tag; baddr<=set; write_strobe<=0;
				
				miss_way<=candidate;			
			end
			
			
			if (writeback) begin 	
							
				if (accW || (read_strobe!=0))	begin
					
					weB<=1; 
					
					doutBstrobe<=read_strobe; read_strobe<=read_strobe+1;	
					flush_way<=writethrough_way;
								
					if (read_strobe==`DL2subblocks-1) begin
						writeback<=0; 
														
						if (flushing && !waiting) begin
							dirty[writethrough_set][writethrough_way]<=0;
							writethrough_block<=writethrough_block+1;
							if (`DEB)$display("writethrough_block %d set %d way %d ", writethrough_block, writethrough_set,writethrough_way);	
						end	else begin
							en_pending<=1;
						end
								
					end				
				end					
								
			end else if (flushing && accW && !waiting) begin
			
				addrB<={tag_array[writethrough_set][writethrough_way],writethrough_set,{(`DL2block_Log2-3){1'b0}}};
				read_strobe<=0;		
				if (dirty[writethrough_set][writethrough_way]&&valid[writethrough_set][writethrough_way]) begin	
					writeback<=1;
				end else begin
					writeback<=0;
					writethrough_block<=writethrough_block+1;
					if (`DEB)$display("writethrough_block %d set %d way %d ", writethrough_block, writethrough_set,writethrough_way);	
				end
				
				
				if (writethrough_block[`DL2setsLog2+`DL2waysLog2+1-1]==1) begin
					flush_out<=1;		
					writethrough_block<=0;				
				end												

			end 
			
			if (flush_out) begin flushing<=0; flush_out<=0; end 
			
			if (en_pending && accR && (accW||from_writeback)) begin
				enB<=1; addrB<=en_pending_addr;
				en_pending<=0;
			end
			
			
			if (dreadyB) begin				
				write_strobe<=dinBstrobe;
				if (dinBstrobe==`DL2subblocks-1) begin
					waiting<=0; waiting_en<=0; 
				end

				we_local[miss_way]<=1; wvalid<=1;
				
				for (i=0; i<`DL2block/`DL2subblocks/`VLEN; i=i+1)
					wdata[`VLEN*(i+1)-1-:`VLEN]<= ((en_pending_write==i) &&
					 (!waiting_en) && (dinBstrobe==waiting_en_strobe)
					 )?
						we_pending_data: dinB[`VLEN*(i+1)-1-:`VLEN];
			end
		end		
	end
	
	
	always @(*) begin
		for (i=0; i<`DL2block/`DL2subblocks/`VLEN; i=i+1)begin
			if (roffset==i) dout=load_from_prev_lev?
				dinB[`VLEN*(i+1)-1-:`VLEN]:rdata_updated[`VLEN*(i+1)-1-:`VLEN];
		end	
	end
	
	initial begin
		if (`DEB)$dumpvars(0, clk, reset, 
		addr, en, we, din, dout, dready, accepting,
		addrB, enB, weB, dinB, doutB, dreadyB, accR,en_pending_write,
		accepting,accW,en_pending,writeback,we_local,we_pending,weB,enB,hitw,hitw_saved,
		dready,miss,hit,we,en,ready,waiting,waiting_en, wdata,flushing,we_pending_data,
		read_strobe,write_strobe,access_strobe,dinBstrobe,doutBstrobe,waiting_en_strobe
		);
	end
endmodule // DL2cache