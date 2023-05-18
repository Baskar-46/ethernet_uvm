//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date:    17:24:24 06/07/2020 
// Design Name: 
// Module Name:    apb_BDs_bridge 
// Project Name: 
// Target Devices: 
// Tool versions: 
// Description: 
//
// Dependencies: 
//
// Revision: 
// Revision 0.01 - File Created
// Additional Comments: 
//
//////////////////////////////////////////////////////////////////////////////////
module apb_BDs_bridge(

//apb signals
input apb_pclk_i,
input apb_presetn_i,
input apb_psel_i,
input apb_penable_i,
input apb_pwrite_i,
input [31:0]apb_pwdata_i,
input [31:0]apb_paddr_i,
output reg [31:0]apb_prdata_o,	
output reg apb_pready_o,	



//wishbone signals
output reg wb_psel_o,
output reg wb_penable_o,
output reg wb_pwrite_o,
output reg [31:0]wb_pwdata_o,
output reg [31:0]wb_paddr_o,
input [31:0]wb_prdata_i,
input wb_BDAck_i
);
localparam IDLE =0,WB_BUSY=1;
reg state;
wire apb_valid_txn;
reg wb_psel_o_next;
reg wb_penable_o_next;
reg wb_pwrite_o_next;
reg [31:0]wb_pwdata_o_next;
reg [31:0]wb_paddr_o_next;

assign  apb_valid_txn =  apb_psel_i & apb_penable_i  & ~apb_paddr_i[11] &  apb_paddr_i[10];   // 0x400 - 0x7FF



always@(posedge apb_pclk_i or negedge apb_presetn_i)
begin
  if(apb_presetn_i ==0)
   state <= IDLE;
 else 
  begin
   case(state)
     IDLE: state <= apb_valid_txn?WB_BUSY:IDLE;
	 WB_BUSY : state <= wb_BDAck_i?IDLE:WB_BUSY;
   endcase
  end
end


//NOTE: apb_pready_o generation: when ever psel = 1,penable = 1, wishbone_address and other control signals are available make apb_pready_o = 1
always @(*)
begin
   case(state)
     IDLE: begin 
	        if(apb_pwrite_i)	
				apb_pready_o = apb_valid_txn?1'b1:1'b0;
			else
				apb_pready_o = 1'b0;
		   end
	 WB_BUSY: begin 
				if(wb_pwrite_o)			//Note: In this state signals should not depend on primary input, instead depend on the flop output(wb_pwrite_o). Because primary i/p can be chaanged by the apb master even the state=WB_BUSY.
					apb_pready_o = 1'b0;
				else
					apb_pready_o = wb_BDAck_i?1'b1:1'b0;
			  end
   endcase
end

//apb_prdata_o generation
always @(*)
begin
   case(state)
     IDLE: begin
			  apb_prdata_o = 'dz;
		   end
	 WB_BUSY: begin
				apb_prdata_o = apb_pready_o?wb_prdata_i:'dz;
			  end
   endcase

end

//Wishbone signals generation

always @(posedge apb_pclk_i or negedge apb_presetn_i)
begin
  if(apb_presetn_i == 0)
    wb_psel_o <= 1'b0;
  else 
    wb_psel_o <= wb_psel_o_next;
end
always @(*)
    begin
	  case(state)
	    IDLE: begin 
				if(apb_pwrite_i)
					wb_psel_o_next = apb_pready_o?apb_psel_i:wb_psel_o;
				else
					wb_psel_o_next = apb_psel_i;
			  end
		WB_BUSY: begin 
					if(wb_pwrite_o)				//Note: In this state signals should not depend on primary input, instead depend on the flop output(wb_pwrite_o). Because primary i/p can be chaanged by the apb master even the state=WB_BUSY.
						wb_psel_o_next = wb_BDAck_i?1'b0:wb_psel_o;	
					else
						wb_psel_o_next = apb_psel_i;
				 end
	  endcase
	end

always @(posedge apb_pclk_i or negedge apb_presetn_i)
begin
  if(apb_presetn_i == 0)
    wb_penable_o <= 1'b0;
  else 
	wb_penable_o <= wb_penable_o_next;
end	

always@(*)
    begin
	  case(state)
	    IDLE: begin 
				if(apb_pwrite_i)
					wb_penable_o_next = apb_pready_o?apb_penable_i:wb_penable_o;
				else
					wb_penable_o_next = apb_penable_i;
			  end
		WB_BUSY: begin 
					if(wb_pwrite_o)				//Note: In this state signals should not depend on primary input, instead depend on the flop output(wb_pwrite_o). Because primary i/p can be chaanged by the apb master even the state=WB_BUSY.
						wb_penable_o_next = wb_BDAck_i?1'b0:wb_penable_o;	
					else
						wb_penable_o_next = apb_penable_i;
				 end
	  endcase
	end


always @(posedge apb_pclk_i or negedge apb_presetn_i)
begin
  if(apb_presetn_i == 0)
    wb_pwrite_o <= 1'b0;
  else 
    wb_pwrite_o <= wb_pwrite_o_next;
 end
 
 always@(*)
    begin
	  case(state)
	    IDLE: begin 
				if(apb_pwrite_i)
					wb_pwrite_o_next = apb_pready_o?apb_pwrite_i:wb_pwrite_o;
				else
					wb_pwrite_o_next = apb_pwrite_i;
			  end
		WB_BUSY: begin 
					if(wb_pwrite_o)				///Note: In this state signals should not depend on primary input, instead depend on the flop output(wb_pwrite_o). Because primary i/p can be chaanged by the apb master even the state=WB_BUSY.
						wb_pwrite_o_next = wb_BDAck_i?1'b0:wb_pwrite_o;
					else
						wb_pwrite_o_next = apb_pwrite_i;
				end
	  endcase
	end


always @(posedge apb_pclk_i or negedge apb_presetn_i)
begin
  if(apb_presetn_i == 0)
    wb_paddr_o <= 1'b0;
  else 
  wb_paddr_o <= wb_paddr_o_next;
 end
 
 always@(*)
    begin
	  case(state)
	    IDLE:begin 
				if(apb_pwrite_i)
					wb_paddr_o_next = apb_pready_o?apb_paddr_i:wb_paddr_o;	//Note: as wishbone requires only 8-bit[9:2] of address so taking only 8-bits from the apb_address for wb_paddr_o
				else
					wb_paddr_o_next = apb_paddr_i;
			 end
		WB_BUSY: begin 
					if(wb_pwrite_o)			////Note: In this state signals should not depend on primary input, instead depend on the flop output(wb_pwrite_o). Because primary i/p can be chaanged by the apb master even the state=WB_BUSY.
						wb_paddr_o_next = wb_BDAck_i?1'b0:wb_paddr_o;
					else
						wb_paddr_o_next = apb_paddr_i;		
				 end
	  endcase
	end


always @(posedge apb_pclk_i or negedge apb_presetn_i)
begin
  if(apb_presetn_i == 0)
    wb_pwdata_o <= 1'b0;
  else 
    wb_pwdata_o <= wb_pwdata_o_next;
end	
	
always@(*)
    begin
	  case(state)
	    IDLE: begin
				if(apb_pwrite_i)
					wb_pwdata_o_next = apb_pready_o?apb_pwdata_i:wb_pwdata_o;
				else
					wb_pwdata_o_next = apb_pwdata_i;
			  end
		WB_BUSY:begin
					if(wb_pwrite_o)				//Note: In this state signals should not depend on primary input, instead depend on the flop output(wb_pwrite_o). Because primary i/p can be chaanged by the apb master even the state=WB_BUSY.
						wb_pwdata_o_next = wb_BDAck_i?1'b0:wb_pwdata_o;	
					else
						wb_pwdata_o_next = apb_pwdata_i;
				end
	  endcase
	end




endmodule

`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date:    17:24:48 06/07/2020 
// Design Name: 
// Module Name:    eth_clockgen 
// Project Name: 
// Target Devices: 
// Tool versions: 
// Description: 
//
// Dependencies: 
//
// Revision: 
// Revision 0.01 - File Created
// Additional Comments: 
//
//////////////////////////////////////////////////////////////////////////////////
`include "timescale.v"
module eth_clockgen(Clk, Resetn, Divider, MdcEn, MdcEn_n, Mdc);

input       Clk;              // Input clock (Host clock)
input       Resetn;            // Resetn signal
input [7:0] Divider;          // Divider (input clock will be divided by the Divider[7:0])

output      Mdc;              // Output clock
output      MdcEn;            // Enable signal is asserted for one Clk period before Mdc rises.
output      MdcEn_n;          // Enable signal is asserted for one Clk period before Mdc falls.

reg         Mdc;
reg   [7:0] Counter;

wire        CountEq0;
wire  [7:0] CounterPreset;
wire  [7:0] TempDivider;


assign TempDivider[7:0]   = (Divider[7:0]<2)? 8'h02 : Divider[7:0]; // If smaller than 2
assign CounterPreset[7:0] = (TempDivider[7:0]>>1) - 8'b1;           // We are counting half of period


// Counter counts half period
always @ (posedge Clk or negedge Resetn)
begin
  if(Resetn == 0)
    Counter[7:0] <=  8'h1;
  else
    begin
      if(CountEq0)
        begin
          Counter[7:0] <=  CounterPreset[7:0];
        end
      else
        Counter[7:0] <=  Counter - 8'h1;
    end
end


// Mdc is asserted every other half period
always @ (posedge Clk or negedge Resetn)
begin
  if(Resetn == 0)
    Mdc <=  1'b0;
  else
    begin
      if(CountEq0)
        Mdc <=  ~Mdc;
    end
end


assign CountEq0 = Counter == 8'h0;
assign MdcEn = CountEq0 & ~Mdc;
assign MdcEn_n = CountEq0 & Mdc;

endmodule




//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date:    17:25:08 06/07/2020 
// Design Name: 
// Module Name:    eth_crc 
// Project Name: 
// Target Devices: 
// Tool versions: 
// Description: 
//
// Dependencies: 
//
// Revision: 
// Revision 0.01 - File Created
// Additional Comments: 
//
//////////////////////////////////////////////////////////////////////////////////
`include "timescale.v"
module eth_crc (Clk, Resetn, Data, Enable, Initialize, Crc, CrcError);


input Clk;
input Resetn;
input [3:0] Data;
input Enable;
input Initialize;

output [31:0] Crc;
output CrcError;

reg  [31:0] Crc;

wire [31:0] CrcNext;


assign CrcNext[0] = Enable & (Data[0] ^ Crc[28]); 
assign CrcNext[1] = Enable & (Data[1] ^ Data[0] ^ Crc[28] ^ Crc[29]); 
assign CrcNext[2] = Enable & (Data[2] ^ Data[1] ^ Data[0] ^ Crc[28] ^ Crc[29] ^ Crc[30]); 
assign CrcNext[3] = Enable & (Data[3] ^ Data[2] ^ Data[1] ^ Crc[29] ^ Crc[30] ^ Crc[31]); 
assign CrcNext[4] = (Enable & (Data[3] ^ Data[2] ^ Data[0] ^ Crc[28] ^ Crc[30] ^ Crc[31])) ^ Crc[0]; 
assign CrcNext[5] = (Enable & (Data[3] ^ Data[1] ^ Data[0] ^ Crc[28] ^ Crc[29] ^ Crc[31])) ^ Crc[1]; 
assign CrcNext[6] = (Enable & (Data[2] ^ Data[1] ^ Crc[29] ^ Crc[30])) ^ Crc[ 2]; 
assign CrcNext[7] = (Enable & (Data[3] ^ Data[2] ^ Data[0] ^ Crc[28] ^ Crc[30] ^ Crc[31])) ^ Crc[3]; 
assign CrcNext[8] = (Enable & (Data[3] ^ Data[1] ^ Data[0] ^ Crc[28] ^ Crc[29] ^ Crc[31])) ^ Crc[4]; 
assign CrcNext[9] = (Enable & (Data[2] ^ Data[1] ^ Crc[29] ^ Crc[30])) ^ Crc[5]; 
assign CrcNext[10] = (Enable & (Data[3] ^ Data[2] ^ Data[0] ^ Crc[28] ^ Crc[30] ^ Crc[31])) ^ Crc[6]; 
assign CrcNext[11] = (Enable & (Data[3] ^ Data[1] ^ Data[0] ^ Crc[28] ^ Crc[29] ^ Crc[31])) ^ Crc[7]; 
assign CrcNext[12] = (Enable & (Data[2] ^ Data[1] ^ Data[0] ^ Crc[28] ^ Crc[29] ^ Crc[30])) ^ Crc[8]; 
assign CrcNext[13] = (Enable & (Data[3] ^ Data[2] ^ Data[1] ^ Crc[29] ^ Crc[30] ^ Crc[31])) ^ Crc[9]; 
assign CrcNext[14] = (Enable & (Data[3] ^ Data[2] ^ Crc[30] ^ Crc[31])) ^ Crc[10]; 
assign CrcNext[15] = (Enable & (Data[3] ^ Crc[31])) ^ Crc[11]; 
assign CrcNext[16] = (Enable & (Data[0] ^ Crc[28])) ^ Crc[12]; 
assign CrcNext[17] = (Enable & (Data[1] ^ Crc[29])) ^ Crc[13]; 
assign CrcNext[18] = (Enable & (Data[2] ^ Crc[30])) ^ Crc[14]; 
assign CrcNext[19] = (Enable & (Data[3] ^ Crc[31])) ^ Crc[15]; 
assign CrcNext[20] = Crc[16]; 
assign CrcNext[21] = Crc[17]; 
assign CrcNext[22] = (Enable & (Data[0] ^ Crc[28])) ^ Crc[18]; 
assign CrcNext[23] = (Enable & (Data[1] ^ Data[0] ^ Crc[29] ^ Crc[28])) ^ Crc[19]; 
assign CrcNext[24] = (Enable & (Data[2] ^ Data[1] ^ Crc[30] ^ Crc[29])) ^ Crc[20]; 
assign CrcNext[25] = (Enable & (Data[3] ^ Data[2] ^ Crc[31] ^ Crc[30])) ^ Crc[21]; 
assign CrcNext[26] = (Enable & (Data[3] ^ Data[0] ^ Crc[31] ^ Crc[28])) ^ Crc[22]; 
assign CrcNext[27] = (Enable & (Data[1] ^ Crc[29])) ^ Crc[23]; 
assign CrcNext[28] = (Enable & (Data[2] ^ Crc[30])) ^ Crc[24]; 
assign CrcNext[29] = (Enable & (Data[3] ^ Crc[31])) ^ Crc[25]; 
assign CrcNext[30] = Crc[26]; 
assign CrcNext[31] = Crc[27]; 


always @ (posedge Clk or negedge Resetn)
begin
  if (Resetn == 0)
    Crc <=  32'hffffffff;
  else
  if(Initialize)
    Crc <=  32'hffffffff;
  else
    Crc <=  CrcNext;
end

assign CrcError = Crc[31:0] != 32'hc704dd7b;  // CRC not equal to magic number

endmodule


//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date:    17:25:27 06/07/2020 
// Design Name: 
// Module Name:    eth_fifo 
// Project Name: 
// Target Devices: 
// Tool versions: 
// Description: 
//
// Dependencies: 
//
// Revision: 
// Revision 0.01 - File Created
// Additional Comments: 
//
//////////////////////////////////////////////////////////////////////////////////
`include "ethmac_defines.v"
`include "timescale.v"
module eth_fifo (data_in, data_out, clk, resetn, write, read, clear,
                 almost_full, full, almost_empty, empty, cnt);

parameter DATA_WIDTH    = 32;
parameter DEPTH         = 8;
parameter CNT_WIDTH     = 4;

input                     clk;
input                     resetn;
input                     write;
input                     read;
input                     clear;
input   [DATA_WIDTH-1:0]  data_in;

output  [DATA_WIDTH-1:0]  data_out;
output                    almost_full;
output                    full;
output                    almost_empty;
output                    empty;
output  [CNT_WIDTH-1:0]   cnt;

integer fifo_loc_cnt;

`ifdef ETH_FIFO_XILINX
`else
  `ifdef ETH_ALTERA_ALTSYNCRAM
  `else
    reg     [DATA_WIDTH-1:0]  fifo  [0:DEPTH-1];
    reg     [DATA_WIDTH-1:0]  data_out;
  `endif
`endif

reg     [CNT_WIDTH-1:0]   cnt;
reg     [CNT_WIDTH-2:0]   read_pointer;
reg     [CNT_WIDTH-2:0]   write_pointer;


always @ (posedge clk or negedge resetn)
begin
  if(resetn == 0)
    cnt <= 0;
  else
  if(clear)
    cnt <= { {(CNT_WIDTH-1){1'b0}}, read^write};
  else
  if(read ^ write)
    if(read)
      cnt <= cnt - 1;
    else
      cnt <= cnt + 1;
end


always @ (posedge clk or negedge resetn)
begin
  if(resetn == 0)
    read_pointer <= 0;
  else
  if(clear)
    read_pointer <= { {(CNT_WIDTH-2){1'b0}}, read};
  else
  if(read & ~empty)
    read_pointer <= read_pointer + 1'b1;
end

always @ (posedge clk or negedge resetn)
begin
  if(resetn == 0)
    write_pointer <= 0;
  else
  if(clear)
    write_pointer <= { {(CNT_WIDTH-2){1'b0}}, write};
  else
  if(write & ~full)
    write_pointer <= write_pointer + 1'b1;
end

assign empty = ~(|cnt);
assign almost_empty = cnt == 1;
assign full  = cnt == DEPTH;
assign almost_full  = &cnt[CNT_WIDTH-2:0];



`ifdef ETH_FIFO_XILINX
  xilinx_dist_ram_16x32 fifo
  ( .data_out(data_out), 
    .we(write & ~full),
    .data_in(data_in),
    .read_address( clear ? {CNT_WIDTH-1{1'b0}} : read_pointer),
    .write_address(clear ? {CNT_WIDTH-1{1'b0}} : write_pointer),
    .wclk(clk)
  );
`else   // !ETH_FIFO_XILINX
`ifdef ETH_ALTERA_ALTSYNCRAM
  altera_dpram_16x32  altera_dpram_16x32_inst
  (
    .data             (data_in),
    .wren             (write & ~full),
    .wraddress        (clear ? {CNT_WIDTH-1{1'b0}} : write_pointer),
    .rdaddress        (clear ? {CNT_WIDTH-1{1'b0}} : read_pointer ),
    .clock            (clk),
    .q                (data_out)
  );  //exemplar attribute altera_dpram_16x32_inst NOOPT TRUE
`else   // !ETH_ALTERA_ALTSYNCRAM
  always @ (posedge clk)
  begin
    if(resetn == 0)		//Intialised all fifo locations to zero
	begin
		for(fifo_loc_cnt = 0; fifo_loc_cnt <= DEPTH-1; fifo_loc_cnt = fifo_loc_cnt+1)
		begin
			fifo[fifo_loc_cnt] <= 0;
		end
	end
	else begin
		if(write & clear)
			fifo[0] <= data_in;
		else begin
			if(write & ~full)
			fifo[write_pointer] <= data_in; 
		end
	end

  end
  

  always @ (posedge clk)
  begin
    if(clear)
      data_out <= fifo[0];
    else
      data_out <= fifo[read_pointer];
  end
`endif  // !ETH_ALTERA_ALTSYNCRAM
`endif  // !ETH_FIFO_XILINX


endmodule



//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date:    17:25:45 06/07/2020 
// Design Name: 
// Module Name:    eth_maccontrol 
// Project Name: 
// Target Devices: 
// Tool versions: 
// Description: 
//
// Dependencies: 
//
// Revision: 
// Revision 0.01 - File Created
// Additional Comments: 
//
//////////////////////////////////////////////////////////////////////////////////
`include "timescale.v"
module eth_maccontrol (MTxClk, MRxClk, TxResetn, RxResetn, TPauseRq, TxDataIn, TxStartFrmIn, TxUsedDataIn, 
                       TxEndFrmIn, TxDoneIn, TxAbortIn, RxData, RxValid, RxStartFrm, RxEndFrm, ReceiveEnd, 
                       ReceivedPacketGood, ReceivedLengthOK, TxFlow, RxFlow, DlyCrcEn, TxPauseTV, 
                       MAC, PadIn, PadOut, CrcEnIn, CrcEnOut, TxDataOut, TxStartFrmOut, TxEndFrmOut, 
                       TxDoneOut, TxAbortOut, TxUsedDataOut, WillSendControlFrame, TxCtrlEndFrm, 
                       ReceivedPauseFrm, ControlFrmAddressOK, SetPauseTimer, r_PassAll, RxStatusWriteLatched_sync2
                      );



input         MTxClk;                   // Transmit clock (from PHY)
input         MRxClk;                   // Receive clock (from PHY)
input         TxResetn;                  // Transmit reset
input         RxResetn;                  // Receive reset
input         TPauseRq;                 // Transmit control frame (from host)
input   [7:0] TxDataIn;                 // Transmit packet data byte (from host)
input         TxStartFrmIn;             // Transmit packet start frame input (from host)
input         TxUsedDataIn;             // Transmit packet used data (from TxEthMAC)
input         TxEndFrmIn;               // Transmit packet end frame input (from host)
input         TxDoneIn;                 // Transmit packet done (from TxEthMAC)
input         TxAbortIn;                // Transmit packet abort (input from TxEthMAC)
input         PadIn;                    // Padding (input from registers)
input         CrcEnIn;                  // Crc append (input from registers)
input   [7:0] RxData;                   // Receive Packet Data (from RxEthMAC)
input         RxValid;                  // Received a valid packet
input         RxStartFrm;               // Receive packet start frame (input from RxEthMAC)
input         RxEndFrm;                 // Receive packet end frame (input from RxEthMAC)
input         ReceiveEnd;               // End of receiving of the current packet (input from RxEthMAC)
input         ReceivedPacketGood;       // Received packet is good
input         ReceivedLengthOK;         // Length of the received packet is OK
input         TxFlow;                   // Tx flow control (from registers)
input         RxFlow;                   // Rx flow control (from registers)
input         DlyCrcEn;                 // Delayed CRC enabled (from registers)
input  [15:0] TxPauseTV;                // Transmit Pause Timer Value (from registers)
input  [47:0] MAC;                      // MAC address (from registers)
input         RxStatusWriteLatched_sync2;
input         r_PassAll;

output  [7:0] TxDataOut;                // Transmit Packet Data (to TxEthMAC)
output        TxStartFrmOut;            // Transmit packet start frame (output to TxEthMAC)
output        TxEndFrmOut;              // Transmit packet end frame (output to TxEthMAC)
output        TxDoneOut;                // Transmit packet done (to host)
output        TxAbortOut;               // Transmit packet aborted (to host)
output        TxUsedDataOut;            // Transmit packet used data (to host)
output        PadOut;                   // Padding (output to TxEthMAC)
output        CrcEnOut;                 // Crc append (output to TxEthMAC)
output        WillSendControlFrame;
output        TxCtrlEndFrm;
output        ReceivedPauseFrm;
output        ControlFrmAddressOK;
output        SetPauseTimer;

reg           TxUsedDataOutDetected;    
reg           TxAbortInLatched;         
reg           TxDoneInLatched;          
reg           MuxedDone;                
reg           MuxedAbort;               

wire          Pause;                    
wire          TxCtrlStartFrm;
wire    [7:0] ControlData;              
wire          CtrlMux;                  
wire          SendingCtrlFrm;           // Sending Control Frame (enables padding and CRC)
wire          BlockTxDone;


// Signal TxUsedDataOut was detected (a transfer is already in progress)
always @ (posedge MTxClk or negedge TxResetn)
begin
  if(TxResetn == 0)
    TxUsedDataOutDetected <=  1'b0;
  else
  if(TxDoneIn | TxAbortIn)
    TxUsedDataOutDetected <=  1'b0;
  else
  if(TxUsedDataOut)
    TxUsedDataOutDetected <=  1'b1;
end    


// Latching variables
always @ (posedge MTxClk or negedge TxResetn)
begin
  if(TxResetn == 0)
    begin
      TxAbortInLatched <=  1'b0;
      TxDoneInLatched  <=  1'b0;
    end
  else
    begin
      TxAbortInLatched <=  TxAbortIn;
      TxDoneInLatched  <=  TxDoneIn;
    end
end



// Generating muxed abort signal
always @ (posedge MTxClk or negedge TxResetn)
begin
  if(TxResetn == 0)
    MuxedAbort <=  1'b0;
  else
  if(TxStartFrmIn)
    MuxedAbort <=  1'b0;
  else
  if(TxAbortIn & ~TxAbortInLatched & TxUsedDataOutDetected)
    MuxedAbort <=  1'b1;
end


// Generating muxed done signal
always @ (posedge MTxClk or negedge TxResetn)
begin
  if(TxResetn == 0)
    MuxedDone <=  1'b0;
  else
  if(TxStartFrmIn)
    MuxedDone <=  1'b0;
  else
  if(TxDoneIn & (~TxDoneInLatched) & TxUsedDataOutDetected)
    MuxedDone <=  1'b1;
end


// TxDoneOut
assign TxDoneOut  = CtrlMux? ((~TxStartFrmIn) & (~BlockTxDone) & MuxedDone) : 
                             ((~TxStartFrmIn) & (~BlockTxDone) & TxDoneIn);

// TxAbortOut
assign TxAbortOut  = CtrlMux? ((~TxStartFrmIn) & (~BlockTxDone) & MuxedAbort) :
                              ((~TxStartFrmIn) & (~BlockTxDone) & TxAbortIn);

// TxUsedDataOut
assign TxUsedDataOut  = ~CtrlMux & TxUsedDataIn;

// TxStartFrmOut
assign TxStartFrmOut = CtrlMux? TxCtrlStartFrm : (TxStartFrmIn & ~Pause);


// TxEndFrmOut
assign TxEndFrmOut = CtrlMux? TxCtrlEndFrm : TxEndFrmIn;


// TxDataOut[7:0]
assign TxDataOut[7:0] = CtrlMux? ControlData[7:0] : TxDataIn[7:0];


// PadOut
assign PadOut = PadIn | SendingCtrlFrm;


// CrcEnOut
assign CrcEnOut = CrcEnIn | SendingCtrlFrm;



// Connecting receivecontrol module
eth_receivecontrol receivecontrol1 
(
 .MTxClk(MTxClk), .MRxClk(MRxClk), .TxResetn(TxResetn), .RxResetn(RxResetn), .RxData(RxData), 
 .RxValid(RxValid), .RxStartFrm(RxStartFrm), .RxEndFrm(RxEndFrm), .RxFlow(RxFlow), 
 .ReceiveEnd(ReceiveEnd), .MAC(MAC), .DlyCrcEn(DlyCrcEn), .TxDoneIn(TxDoneIn), 
 .TxAbortIn(TxAbortIn), .TxStartFrmOut(TxStartFrmOut), .ReceivedLengthOK(ReceivedLengthOK), 
 .ReceivedPacketGood(ReceivedPacketGood), .TxUsedDataOutDetected(TxUsedDataOutDetected), 
 .Pause(Pause), .ReceivedPauseFrm(ReceivedPauseFrm), .AddressOK(ControlFrmAddressOK), 
 .r_PassAll(r_PassAll), .RxStatusWriteLatched_sync2(RxStatusWriteLatched_sync2), .SetPauseTimer(SetPauseTimer)
);


eth_transmitcontrol transmitcontrol1
(
 .MTxClk(MTxClk), .TxResetn(TxResetn), .TxUsedDataIn(TxUsedDataIn), .TxUsedDataOut(TxUsedDataOut), 
 .TxDoneIn(TxDoneIn), .TxAbortIn(TxAbortIn), .TxStartFrmIn(TxStartFrmIn), .TPauseRq(TPauseRq), 
 .TxUsedDataOutDetected(TxUsedDataOutDetected), .TxFlow(TxFlow), .DlyCrcEn(DlyCrcEn), .TxPauseTV(TxPauseTV), 
 .MAC(MAC), .TxCtrlStartFrm(TxCtrlStartFrm), .TxCtrlEndFrm(TxCtrlEndFrm), .SendingCtrlFrm(SendingCtrlFrm), 
 .CtrlMux(CtrlMux), .ControlData(ControlData), .WillSendControlFrame(WillSendControlFrame), .BlockTxDone(BlockTxDone)
);



endmodule


`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date:    11:25:41 03/31/2020 
// Design Name: 
// Module Name:    ethmac_defines 
// Project Name: 
// Target Devices: 
// Tool versions: 
// Description: 
//
// Dependencies: 
//
// Revision: 
// Revision 0.01 - File Created
// Additional Comments: 
//
//////////////////////////////////////////////////////////////////////////////////
`define ETH_MODER_ADR         8'h0    // 0x0 
`define ETH_INT_SOURCE_ADR    8'h1    // 0x4 
`define ETH_INT_MASK_ADR      8'h2    // 0x8 
`define ETH_IPGT_ADR          8'h3    // 0xC 
`define ETH_IPGR1_ADR         8'h4    // 0x10
`define ETH_IPGR2_ADR         8'h5    // 0x14
`define ETH_PACKETLEN_ADR     8'h6    // 0x18
`define ETH_COLLCONF_ADR      8'h7    // 0x1C
`define ETH_TX_BD_NUM_ADR     8'h8    // 0x20
`define ETH_CTRLMODER_ADR     8'h9    // 0x24
`define ETH_MIIMODER_ADR      8'hA    // 0x28
`define ETH_MIICOMMAND_ADR    8'hB    // 0x2C
`define ETH_MIIADDRESS_ADR    8'hC    // 0x30
`define ETH_MIITX_DATA_ADR    8'hD    // 0x34
`define ETH_MIIRX_DATA_ADR    8'hE    // 0x38
`define ETH_MIISTATUS_ADR     8'hF    // 0x3C
`define ETH_MAC_ADDR0_ADR     8'h10   // 0x40
`define ETH_MAC_ADDR1_ADR     8'h11   // 0x44
`define ETH_HASH0_ADR         8'h12   // 0x48
`define ETH_HASH1_ADR         8'h13   // 0x4C
`define ETH_TX_CTRL_ADR       8'h14   // 0x50
`define ETH_RX_CTRL_ADR       8'h15   // 0x54
`define ETH_DBG_ADR           8'h16   // 0x58

`define ETH_MODER_DEF_0         8'h00
`define ETH_MODER_DEF_1         8'hA2
`define ETH_MODER_DEF_2         1'h0
`define ETH_INT_MASK_DEF_0      7'h0
`define ETH_IPGT_DEF_0          7'h15  //Note: As  of now design is working only for 15.So hardcoding this value. 
`define ETH_IPGR1_DEF_0         7'h0C
`define ETH_IPGR2_DEF_0         7'h12
`define ETH_PACKETLEN_DEF_0     8'h00
`define ETH_PACKETLEN_DEF_1     8'h06
`define ETH_PACKETLEN_DEF_2     8'h40
`define ETH_PACKETLEN_DEF_3     8'h00
`define ETH_COLLCONF_DEF_0      6'h3f
`define ETH_COLLCONF_DEF_2      4'hF
`define ETH_TX_BD_NUM_DEF_0     8'h40
`define ETH_CTRLMODER_DEF_0     3'h0
`define ETH_MIIMODER_DEF_0      8'h64
`define ETH_MIIMODER_DEF_1      1'h0
`define ETH_MIIADDRESS_DEF_0    5'h00
`define ETH_MIIADDRESS_DEF_1    5'h00
`define ETH_MIITX_DATA_DEF_0    8'h00
`define ETH_MIITX_DATA_DEF_1    8'h00
`define ETH_MIIRX_DATA_DEF     16'h0000 // not written from WB
`define ETH_MAC_ADDR0_DEF_0     8'h00
`define ETH_MAC_ADDR0_DEF_1     8'h00
`define ETH_MAC_ADDR0_DEF_2     8'h00
`define ETH_MAC_ADDR0_DEF_3     8'h00
`define ETH_MAC_ADDR1_DEF_0     8'h00
`define ETH_MAC_ADDR1_DEF_1     8'h00
`define ETH_HASH0_DEF_0         8'h00
`define ETH_HASH0_DEF_1         8'h00
`define ETH_HASH0_DEF_2         8'h00
`define ETH_HASH0_DEF_3         8'h00
`define ETH_HASH1_DEF_0         8'h00
`define ETH_HASH1_DEF_1         8'h00
`define ETH_HASH1_DEF_2         8'h00
`define ETH_HASH1_DEF_3         8'h00
`define ETH_TX_CTRL_DEF_0       8'h00 //
`define ETH_TX_CTRL_DEF_1       8'h00 //
`define ETH_TX_CTRL_DEF_2       1'h0  //
`define ETH_RX_CTRL_DEF_0       8'h00
`define ETH_RX_CTRL_DEF_1       8'h00


`define ETH_MODER_WIDTH_0       8
`define ETH_MODER_WIDTH_1       8
`define ETH_MODER_WIDTH_2       1
`define ETH_INT_SOURCE_WIDTH_0  7
`define ETH_INT_MASK_WIDTH_0    7
`define ETH_IPGT_WIDTH_0        7
`define ETH_IPGR1_WIDTH_0       7
`define ETH_IPGR2_WIDTH_0       7
`define ETH_PACKETLEN_WIDTH_0   8
`define ETH_PACKETLEN_WIDTH_1   8
`define ETH_PACKETLEN_WIDTH_2   8
`define ETH_PACKETLEN_WIDTH_3   8
`define ETH_COLLCONF_WIDTH_0    6
`define ETH_COLLCONF_WIDTH_2    4
`define ETH_TX_BD_NUM_WIDTH_0   8
`define ETH_CTRLMODER_WIDTH_0   3
`define ETH_MIIMODER_WIDTH_0    8
`define ETH_MIIMODER_WIDTH_1    1
`define ETH_MIICOMMAND_WIDTH_0  3
`define ETH_MIIADDRESS_WIDTH_0  5
`define ETH_MIIADDRESS_WIDTH_1  5
`define ETH_MIITX_DATA_WIDTH_0  8
`define ETH_MIITX_DATA_WIDTH_1  8
`define ETH_MIIRX_DATA_WIDTH    16 // not written from WB
`define ETH_MIISTATUS_WIDTH     3 // not written from WB
`define ETH_MAC_ADDR0_WIDTH_0   8
`define ETH_MAC_ADDR0_WIDTH_1   8
`define ETH_MAC_ADDR0_WIDTH_2   8
`define ETH_MAC_ADDR0_WIDTH_3   8
`define ETH_MAC_ADDR1_WIDTH_0   8
`define ETH_MAC_ADDR1_WIDTH_1   8
`define ETH_HASH0_WIDTH_0       8
`define ETH_HASH0_WIDTH_1       8
`define ETH_HASH0_WIDTH_2       8
`define ETH_HASH0_WIDTH_3       8
`define ETH_HASH1_WIDTH_0       8
`define ETH_HASH1_WIDTH_1       8
`define ETH_HASH1_WIDTH_2       8
`define ETH_HASH1_WIDTH_3       8
`define ETH_TX_CTRL_WIDTH_0     8
`define ETH_TX_CTRL_WIDTH_1     8
`define ETH_TX_CTRL_WIDTH_2     1
`define ETH_RX_CTRL_WIDTH_0     8
`define ETH_RX_CTRL_WIDTH_1     8


// Outputs are registered (uncomment when needed)
`define ETH_REGISTERED_OUTPUTS

// Settings for TX FIFO
`define ETH_TX_FIFO_CNT_WIDTH  5
`define ETH_TX_FIFO_DEPTH      16
`define ETH_TX_FIFO_DATA_WIDTH 32

// Settings for RX FIFO
`define ETH_RX_FIFO_CNT_WIDTH  5
`define ETH_RX_FIFO_DEPTH      16
`define ETH_RX_FIFO_DATA_WIDTH 32

// Burst length
`define ETH_BURST_LENGTH       4    // Change also ETH_BURST_CNT_WIDTH
`define ETH_BURST_CNT_WIDTH    3    // The counter must be width enough to count to ETH_BURST_LENGTH



`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date:    11:25:41 03/31/2020 
// Design Name: 
// Module Name:    ethmac_defines 
// Project Name: 
// Target Devices: 
// Tool versions: 
// Description: 
//
// Dependencies: 
//
// Revision: 
// Revision 0.01 - File Created
// Additional Comments: 
//
//////////////////////////////////////////////////////////////////////////////////
`define ETH_MODER_ADR         8'h0    // 0x0 
`define ETH_INT_SOURCE_ADR    8'h1    // 0x4 
`define ETH_INT_MASK_ADR      8'h2    // 0x8 
`define ETH_IPGT_ADR          8'h3    // 0xC 
`define ETH_IPGR1_ADR         8'h4    // 0x10
`define ETH_IPGR2_ADR         8'h5    // 0x14
`define ETH_PACKETLEN_ADR     8'h6    // 0x18
`define ETH_COLLCONF_ADR      8'h7    // 0x1C
`define ETH_TX_BD_NUM_ADR     8'h8    // 0x20
`define ETH_CTRLMODER_ADR     8'h9    // 0x24
`define ETH_MIIMODER_ADR      8'hA    // 0x28
`define ETH_MIICOMMAND_ADR    8'hB    // 0x2C
`define ETH_MIIADDRESS_ADR    8'hC    // 0x30
`define ETH_MIITX_DATA_ADR    8'hD    // 0x34
`define ETH_MIIRX_DATA_ADR    8'hE    // 0x38
`define ETH_MIISTATUS_ADR     8'hF    // 0x3C
`define ETH_MAC_ADDR0_ADR     8'h10   // 0x40
`define ETH_MAC_ADDR1_ADR     8'h11   // 0x44
`define ETH_HASH0_ADR         8'h12   // 0x48
`define ETH_HASH1_ADR         8'h13   // 0x4C
`define ETH_TX_CTRL_ADR       8'h14   // 0x50
`define ETH_RX_CTRL_ADR       8'h15   // 0x54
`define ETH_DBG_ADR           8'h16   // 0x58

`define ETH_MODER_DEF_0         8'h00
`define ETH_MODER_DEF_1         8'hA2
`define ETH_MODER_DEF_2         1'h0
`define ETH_INT_MASK_DEF_0      7'h0
`define ETH_IPGT_DEF_0          7'h15  //Note: As  of now design is working only for 15.So hardcoding this value. 
`define ETH_IPGR1_DEF_0         7'h0C
`define ETH_IPGR2_DEF_0         7'h12
`define ETH_PACKETLEN_DEF_0     8'h00
`define ETH_PACKETLEN_DEF_1     8'h06
`define ETH_PACKETLEN_DEF_2     8'h40
`define ETH_PACKETLEN_DEF_3     8'h00
`define ETH_COLLCONF_DEF_0      6'h3f
`define ETH_COLLCONF_DEF_2      4'hF
`define ETH_TX_BD_NUM_DEF_0     8'h40
`define ETH_CTRLMODER_DEF_0     3'h0
`define ETH_MIIMODER_DEF_0      8'h64
`define ETH_MIIMODER_DEF_1      1'h0
`define ETH_MIIADDRESS_DEF_0    5'h00
`define ETH_MIIADDRESS_DEF_1    5'h00
`define ETH_MIITX_DATA_DEF_0    8'h00
`define ETH_MIITX_DATA_DEF_1    8'h00
`define ETH_MIIRX_DATA_DEF     16'h0000 // not written from WB
`define ETH_MAC_ADDR0_DEF_0     8'h00
`define ETH_MAC_ADDR0_DEF_1     8'h00
`define ETH_MAC_ADDR0_DEF_2     8'h00
`define ETH_MAC_ADDR0_DEF_3     8'h00
`define ETH_MAC_ADDR1_DEF_0     8'h00
`define ETH_MAC_ADDR1_DEF_1     8'h00
`define ETH_HASH0_DEF_0         8'h00
`define ETH_HASH0_DEF_1         8'h00
`define ETH_HASH0_DEF_2         8'h00
`define ETH_HASH0_DEF_3         8'h00
`define ETH_HASH1_DEF_0         8'h00
`define ETH_HASH1_DEF_1         8'h00
`define ETH_HASH1_DEF_2         8'h00
`define ETH_HASH1_DEF_3         8'h00
`define ETH_TX_CTRL_DEF_0       8'h00 //
`define ETH_TX_CTRL_DEF_1       8'h00 //
`define ETH_TX_CTRL_DEF_2       1'h0  //
`define ETH_RX_CTRL_DEF_0       8'h00
`define ETH_RX_CTRL_DEF_1       8'h00


`define ETH_MODER_WIDTH_0       8
`define ETH_MODER_WIDTH_1       8
`define ETH_MODER_WIDTH_2       1
`define ETH_INT_SOURCE_WIDTH_0  7
`define ETH_INT_MASK_WIDTH_0    7
`define ETH_IPGT_WIDTH_0        7
`define ETH_IPGR1_WIDTH_0       7
`define ETH_IPGR2_WIDTH_0       7
`define ETH_PACKETLEN_WIDTH_0   8
`define ETH_PACKETLEN_WIDTH_1   8
`define ETH_PACKETLEN_WIDTH_2   8
`define ETH_PACKETLEN_WIDTH_3   8
`define ETH_COLLCONF_WIDTH_0    6
`define ETH_COLLCONF_WIDTH_2    4
`define ETH_TX_BD_NUM_WIDTH_0   8
`define ETH_CTRLMODER_WIDTH_0   3
`define ETH_MIIMODER_WIDTH_0    8
`define ETH_MIIMODER_WIDTH_1    1
`define ETH_MIICOMMAND_WIDTH_0  3
`define ETH_MIIADDRESS_WIDTH_0  5
`define ETH_MIIADDRESS_WIDTH_1  5
`define ETH_MIITX_DATA_WIDTH_0  8
`define ETH_MIITX_DATA_WIDTH_1  8
`define ETH_MIIRX_DATA_WIDTH    16 // not written from WB
`define ETH_MIISTATUS_WIDTH     3 // not written from WB
`define ETH_MAC_ADDR0_WIDTH_0   8
`define ETH_MAC_ADDR0_WIDTH_1   8
`define ETH_MAC_ADDR0_WIDTH_2   8
`define ETH_MAC_ADDR0_WIDTH_3   8
`define ETH_MAC_ADDR1_WIDTH_0   8
`define ETH_MAC_ADDR1_WIDTH_1   8
`define ETH_HASH0_WIDTH_0       8
`define ETH_HASH0_WIDTH_1       8
`define ETH_HASH0_WIDTH_2       8
`define ETH_HASH0_WIDTH_3       8
`define ETH_HASH1_WIDTH_0       8
`define ETH_HASH1_WIDTH_1       8
`define ETH_HASH1_WIDTH_2       8
`define ETH_HASH1_WIDTH_3       8
`define ETH_TX_CTRL_WIDTH_0     8
`define ETH_TX_CTRL_WIDTH_1     8
`define ETH_TX_CTRL_WIDTH_2     1
`define ETH_RX_CTRL_WIDTH_0     8
`define ETH_RX_CTRL_WIDTH_1     8


// Outputs are registered (uncomment when needed)
`define ETH_REGISTERED_OUTPUTS

// Settings for TX FIFO
`define ETH_TX_FIFO_CNT_WIDTH  5
`define ETH_TX_FIFO_DEPTH      16
`define ETH_TX_FIFO_DATA_WIDTH 32

// Settings for RX FIFO
`define ETH_RX_FIFO_CNT_WIDTH  5
`define ETH_RX_FIFO_DEPTH      16
`define ETH_RX_FIFO_DATA_WIDTH 32

// Burst length
`define ETH_BURST_LENGTH       4    // Change also ETH_BURST_CNT_WIDTH
`define ETH_BURST_CNT_WIDTH    3    // The counter must be width enough to count to ETH_BURST_LENGTH



//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date:    17:26:11 06/07/2020 
// Design Name: 
// Module Name:    eth_macstatus 
// Project Name: 
// Target Devices: 
// Tool versions: 
// Description: 
//
// Dependencies: 
//
// Revision: 
// Revision 0.01 - File Created
// Additional Comments: 
//
//////////////////////////////////////////////////////////////////////////////////

`include "timescale.v"
module eth_macstatus(
                      MRxClk, Resetn, ReceivedLengthOK, ReceiveEnd, ReceivedPacketGood, RxCrcError, 
                      MRxErr, MRxDV, RxStateSFD, RxStateData, RxStatePreamble, RxStateIdle,RxStateDA,RxStateSA,RxStateLength, Transmitting, 
                      RxByteCnt, RxByteCntEq0, RxByteCntGreat2, RxByteCntMaxFrame, 
                      InvalidSymbol, MRxD, LatchedCrcError, Collision, CollValid, RxLateCollision,
                      r_RecSmall, r_MinFL, r_MaxFL, ShortFrame, DribbleNibble, ReceivedPacketTooBig, r_HugEn,
                      LoadRxStatus, StartTxDone, StartTxAbort, RetryCnt, RetryCntLatched, MTxClk, MaxCollisionOccured, 
                      RetryLimit, LateCollision, LateCollLatched, DeferIndication, DeferLatched, RstDeferLatched, TxStartFrm,
                      StatePreamble,StateSFD,StateDA,StateSA,StateLength, StateData, CarrierSense, CarrierSenseLost, TxUsedData, LatchedMRxErr, Loopback, 
                      r_FullD
                    );




input         MRxClk;
input         Resetn;
input         RxCrcError;
input         MRxErr;
input         MRxDV;

input         RxStateSFD;
input   [1:0] RxStateData;
input         RxStatePreamble;
input         RxStateIdle;
input 		  RxStateDA;
input 		  RxStateSA;
input 		  RxStateLength;
input         Transmitting;
input  [15:0] RxByteCnt;
input         RxByteCntEq0;
input         RxByteCntGreat2;
input         RxByteCntMaxFrame;
input   [3:0] MRxD;
input         Collision;
input   [5:0] CollValid;
input         r_RecSmall;
input  [15:0] r_MinFL;
input  [15:0] r_MaxFL;
input         r_HugEn;
input         StartTxDone;
input         StartTxAbort;
input   [3:0] RetryCnt;
input         MTxClk;
input         MaxCollisionOccured;
input         LateCollision;
input         DeferIndication;
input         TxStartFrm;
input         StatePreamble;
input 		  StateSFD;
input 		  StateDA;
input 		  StateSA;
input 		  StateLength;
input   [1:0] StateData;
input         CarrierSense;
input         TxUsedData;
input         Loopback;
input         r_FullD;


output        ReceivedLengthOK;
output        ReceiveEnd;
output        ReceivedPacketGood;
output        InvalidSymbol;
output        LatchedCrcError;
output        RxLateCollision;
output        ShortFrame;
output        DribbleNibble;
output        ReceivedPacketTooBig;
output        LoadRxStatus;
output  [3:0] RetryCntLatched;
output        RetryLimit;
output        LateCollLatched;
output        DeferLatched;
input         RstDeferLatched;
output        CarrierSenseLost;
output        LatchedMRxErr;


reg           ReceiveEnd;

reg           LatchedCrcError;
reg           LatchedMRxErr;
reg           LoadRxStatus;
reg           InvalidSymbol;
reg     [3:0] RetryCntLatched;
reg           RetryLimit;
reg           LateCollLatched;
reg           DeferLatched;
reg           CarrierSenseLost;

wire          TakeSample;
reg 		  TakeSample_d;
wire          SetInvalidSymbol; // Invalid symbol was received during reception in 100Mbps 

// Crc error
always @ (posedge MRxClk or negedge Resetn)
begin
  if(Resetn == 0)
    LatchedCrcError <= 1'b0;
  else
  if(RxStateSFD)
    LatchedCrcError <= 1'b0;
  else
  if(RxStateData[1] | TakeSample_d)			
    LatchedCrcError <= RxCrcError & ~RxByteCntEq0;
end


// LatchedMRxErr
always @ (posedge MRxClk or negedge Resetn)
begin
  if(Resetn)
    LatchedMRxErr <= 1'b0;
  else
  if(MRxErr & MRxDV & (RxStatePreamble | RxStateSFD |RxStateDA | RxStateSA | RxStateLength |(|RxStateData) | RxStateIdle & ~Transmitting))
    LatchedMRxErr <= 1'b1;
  else
    LatchedMRxErr <= 1'b0;
end


// ReceivedPacketGood
assign ReceivedPacketGood = ~LatchedCrcError;


// ReceivedLengthOK
assign ReceivedLengthOK = RxByteCnt[15:0] >= r_MinFL[15:0] & RxByteCnt[15:0] <= r_MaxFL[15:0];





// Time to take a sample
assign TakeSample = (|RxStateData)   & (~MRxDV)                    |
                      RxStateData[1] &   MRxDV & RxByteCntMaxFrame;		

always @ (posedge MRxClk or negedge Resetn)
begin
  if(Resetn == 0)
	TakeSample_d <= 0;
  else
    TakeSample_d <= TakeSample;
end

// LoadRxStatus
always @ (posedge MRxClk or negedge Resetn)
begin
  if(Resetn == 0)
    LoadRxStatus <= 1'b0;
  else
    LoadRxStatus <= TakeSample_d;
end



// ReceiveEnd
always @ (posedge MRxClk or negedge Resetn)
begin
  if(Resetn == 0)
    ReceiveEnd  <= 1'b0;
  else
    ReceiveEnd  <= LoadRxStatus;                     
end


// Invalid Symbol received during 100Mbps mode
assign SetInvalidSymbol = MRxDV & MRxErr & MRxD[3:0] == 4'he;


// InvalidSymbol
always @ (posedge MRxClk or negedge Resetn)
begin
  if(Resetn == 0)
    InvalidSymbol <= 1'b0;
  else
  if(LoadRxStatus & ~SetInvalidSymbol)
    InvalidSymbol <= 1'b0;
  else
  if(SetInvalidSymbol)
    InvalidSymbol <= 1'b1;
end


// Late Collision

reg RxLateCollision;
reg RxColWindow;
// Collision Window
always @ (posedge MRxClk or negedge Resetn)
begin
  if(Resetn == 0)
    RxLateCollision <= 1'b0;
  else
  if(LoadRxStatus)
    RxLateCollision <= 1'b0;
  else
  if(Collision & (~r_FullD) & (~RxColWindow | r_RecSmall))
    RxLateCollision <= 1'b1;
end

// Collision Window
always @ (posedge MRxClk or negedge Resetn)
begin
  if(Resetn == 0)
    RxColWindow <= 1'b1;
  else
  if(~Collision & RxByteCnt[5:0] == CollValid[5:0] & RxStateData[1])
    RxColWindow <= 1'b0;
  else
  if(RxStateIdle)
    RxColWindow <= 1'b1;
end


// ShortFrame
reg ShortFrame;
always @ (posedge MRxClk or negedge Resetn)
begin
  if(Resetn == 0)
    ShortFrame <= 1'b0;
  else
  if(LoadRxStatus)
    ShortFrame <= 1'b0;
  else
  if(TakeSample)
    ShortFrame <= RxByteCnt[15:0] < r_MinFL[15:0];		
end


// DribbleNibble
reg DribbleNibble;
always @ (posedge MRxClk or negedge Resetn)
begin
  if(Resetn == 0)
    DribbleNibble <= 1'b0;
  else
  if(RxStateSFD)
    DribbleNibble <= 1'b0;
  else
  if(~MRxDV & RxStateData[0])
    DribbleNibble <= 1'b1;
end


reg ReceivedPacketTooBig;
always @ (posedge MRxClk or negedge Resetn)
begin
  if(Resetn == 0)
    ReceivedPacketTooBig <= 1'b0;
  else
  if(LoadRxStatus)
    ReceivedPacketTooBig <= 1'b0;
  else
  if(TakeSample_d)
   	 ReceivedPacketTooBig <= ~r_HugEn && ((RxByteCnt[15:0]+'d14) > r_MaxFL[15:0] ); 
end



// Latched Retry counter for tx status
always @ (posedge MTxClk or negedge Resetn)
begin
  if(Resetn == 0)
    RetryCntLatched <= 4'h0;
  else
  if(StartTxDone | StartTxAbort)
    RetryCntLatched <= RetryCnt;
end


// Latched Retransmission limit
always @ (posedge MTxClk or negedge Resetn)
begin
  if(Resetn == 0)
    RetryLimit <= 1'h0;
  else
  if(StartTxDone | StartTxAbort)
    RetryLimit <= MaxCollisionOccured;
end


// Latched Late Collision
always @ (posedge MTxClk or negedge Resetn)
begin
  if(Resetn == 0)
    LateCollLatched <= 1'b0;
  else
  if(StartTxDone | StartTxAbort)
    LateCollLatched <= LateCollision;
end



// Latched Defer state
always @ (posedge MTxClk or negedge Resetn)
begin
  if(Resetn == 0)
    DeferLatched <= 1'b0;
  else
  if(DeferIndication)
    DeferLatched <= 1'b1;
  else
  if(RstDeferLatched)
    DeferLatched <= 1'b0;
end


// CarrierSenseLost
always @ (posedge MTxClk or negedge Resetn)
begin
  if(Resetn == 0)
    CarrierSenseLost <= 1'b0;
  else
  if((StatePreamble | StateSFD | StateDA | StateSA | StateLength | (|StateData)) & ~CarrierSense & ~Loopback & ~Collision & ~r_FullD)	
    CarrierSenseLost <= 1'b1;
  else
  if(TxStartFrm)
    CarrierSenseLost <= 1'b0;
end


endmodule


//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date:    17:26:11 06/07/2020 
// Design Name: 
// Module Name:    eth_macstatus 
// Project Name: 
// Target Devices: 
// Tool versions: 
// Description: 
//
// Dependencies: 
//
// Revision: 
// Revision 0.01 - File Created
// Additional Comments: 
//
//////////////////////////////////////////////////////////////////////////////////

`include "timescale.v"
module eth_macstatus(
                      MRxClk, Resetn, ReceivedLengthOK, ReceiveEnd, ReceivedPacketGood, RxCrcError, 
                      MRxErr, MRxDV, RxStateSFD, RxStateData, RxStatePreamble, RxStateIdle,RxStateDA,RxStateSA,RxStateLength, Transmitting, 
                      RxByteCnt, RxByteCntEq0, RxByteCntGreat2, RxByteCntMaxFrame, 
                      InvalidSymbol, MRxD, LatchedCrcError, Collision, CollValid, RxLateCollision,
                      r_RecSmall, r_MinFL, r_MaxFL, ShortFrame, DribbleNibble, ReceivedPacketTooBig, r_HugEn,
                      LoadRxStatus, StartTxDone, StartTxAbort, RetryCnt, RetryCntLatched, MTxClk, MaxCollisionOccured, 
                      RetryLimit, LateCollision, LateCollLatched, DeferIndication, DeferLatched, RstDeferLatched, TxStartFrm,
                      StatePreamble,StateSFD,StateDA,StateSA,StateLength, StateData, CarrierSense, CarrierSenseLost, TxUsedData, LatchedMRxErr, Loopback, 
                      r_FullD
                    );




input         MRxClk;
input         Resetn;
input         RxCrcError;
input         MRxErr;
input         MRxDV;

input         RxStateSFD;
input   [1:0] RxStateData;
input         RxStatePreamble;
input         RxStateIdle;
input 		  RxStateDA;
input 		  RxStateSA;
input 		  RxStateLength;
input         Transmitting;
input  [15:0] RxByteCnt;
input         RxByteCntEq0;
input         RxByteCntGreat2;
input         RxByteCntMaxFrame;
input   [3:0] MRxD;
input         Collision;
input   [5:0] CollValid;
input         r_RecSmall;
input  [15:0] r_MinFL;
input  [15:0] r_MaxFL;
input         r_HugEn;
input         StartTxDone;
input         StartTxAbort;
input   [3:0] RetryCnt;
input         MTxClk;
input         MaxCollisionOccured;
input         LateCollision;
input         DeferIndication;
input         TxStartFrm;
input         StatePreamble;
input 		  StateSFD;
input 		  StateDA;
input 		  StateSA;
input 		  StateLength;
input   [1:0] StateData;
input         CarrierSense;
input         TxUsedData;
input         Loopback;
input         r_FullD;


output        ReceivedLengthOK;
output        ReceiveEnd;
output        ReceivedPacketGood;
output        InvalidSymbol;
output        LatchedCrcError;
output        RxLateCollision;
output        ShortFrame;
output        DribbleNibble;
output        ReceivedPacketTooBig;
output        LoadRxStatus;
output  [3:0] RetryCntLatched;
output        RetryLimit;
output        LateCollLatched;
output        DeferLatched;
input         RstDeferLatched;
output        CarrierSenseLost;
output        LatchedMRxErr;


reg           ReceiveEnd;

reg           LatchedCrcError;
reg           LatchedMRxErr;
reg           LoadRxStatus;
reg           InvalidSymbol;
reg     [3:0] RetryCntLatched;
reg           RetryLimit;
reg           LateCollLatched;
reg           DeferLatched;
reg           CarrierSenseLost;

wire          TakeSample;
reg 		  TakeSample_d;
wire          SetInvalidSymbol; // Invalid symbol was received during reception in 100Mbps 

// Crc error
always @ (posedge MRxClk or negedge Resetn)
begin
  if(Resetn == 0)
    LatchedCrcError <= 1'b0;
  else
  if(RxStateSFD)
    LatchedCrcError <= 1'b0;
  else
  if(RxStateData[1] | TakeSample_d)			
    LatchedCrcError <= RxCrcError & ~RxByteCntEq0;
end


// LatchedMRxErr
always @ (posedge MRxClk or negedge Resetn)
begin
  if(Resetn)
    LatchedMRxErr <= 1'b0;
  else
  if(MRxErr & MRxDV & (RxStatePreamble | RxStateSFD |RxStateDA | RxStateSA | RxStateLength |(|RxStateData) | RxStateIdle & ~Transmitting))
    LatchedMRxErr <= 1'b1;
  else
    LatchedMRxErr <= 1'b0;
end


// ReceivedPacketGood
assign ReceivedPacketGood = ~LatchedCrcError;


// ReceivedLengthOK
assign ReceivedLengthOK = RxByteCnt[15:0] >= r_MinFL[15:0] & RxByteCnt[15:0] <= r_MaxFL[15:0];





// Time to take a sample
assign TakeSample = (|RxStateData)   & (~MRxDV)                    |
                      RxStateData[1] &   MRxDV & RxByteCntMaxFrame;		

always @ (posedge MRxClk or negedge Resetn)
begin
  if(Resetn == 0)
	TakeSample_d <= 0;
  else
    TakeSample_d <= TakeSample;
end

// LoadRxStatus
always @ (posedge MRxClk or negedge Resetn)
begin
  if(Resetn == 0)
    LoadRxStatus <= 1'b0;
  else
    LoadRxStatus <= TakeSample_d;
end



// ReceiveEnd
always @ (posedge MRxClk or negedge Resetn)
begin
  if(Resetn == 0)
    ReceiveEnd  <= 1'b0;
  else
    ReceiveEnd  <= LoadRxStatus;                     
end


// Invalid Symbol received during 100Mbps mode
assign SetInvalidSymbol = MRxDV & MRxErr & MRxD[3:0] == 4'he;


// InvalidSymbol
always @ (posedge MRxClk or negedge Resetn)
begin
  if(Resetn == 0)
    InvalidSymbol <= 1'b0;
  else
  if(LoadRxStatus & ~SetInvalidSymbol)
    InvalidSymbol <= 1'b0;
  else
  if(SetInvalidSymbol)
    InvalidSymbol <= 1'b1;
end


// Late Collision

reg RxLateCollision;
reg RxColWindow;
// Collision Window
always @ (posedge MRxClk or negedge Resetn)
begin
  if(Resetn == 0)
    RxLateCollision <= 1'b0;
  else
  if(LoadRxStatus)
    RxLateCollision <= 1'b0;
  else
  if(Collision & (~r_FullD) & (~RxColWindow | r_RecSmall))
    RxLateCollision <= 1'b1;
end

// Collision Window
always @ (posedge MRxClk or negedge Resetn)
begin
  if(Resetn == 0)
    RxColWindow <= 1'b1;
  else
  if(~Collision & RxByteCnt[5:0] == CollValid[5:0] & RxStateData[1])
    RxColWindow <= 1'b0;
  else
  if(RxStateIdle)
    RxColWindow <= 1'b1;
end


// ShortFrame
reg ShortFrame;
always @ (posedge MRxClk or negedge Resetn)
begin
  if(Resetn == 0)
    ShortFrame <= 1'b0;
  else
  if(LoadRxStatus)
    ShortFrame <= 1'b0;
  else
  if(TakeSample)
    ShortFrame <= RxByteCnt[15:0] < r_MinFL[15:0];		
end


// DribbleNibble
reg DribbleNibble;
always @ (posedge MRxClk or negedge Resetn)
begin
  if(Resetn == 0)
    DribbleNibble <= 1'b0;
  else
  if(RxStateSFD)
    DribbleNibble <= 1'b0;
  else
  if(~MRxDV & RxStateData[0])
    DribbleNibble <= 1'b1;
end


reg ReceivedPacketTooBig;
always @ (posedge MRxClk or negedge Resetn)
begin
  if(Resetn == 0)
    ReceivedPacketTooBig <= 1'b0;
  else
  if(LoadRxStatus)
    ReceivedPacketTooBig <= 1'b0;
  else
  if(TakeSample_d)
   	 ReceivedPacketTooBig <= ~r_HugEn && ((RxByteCnt[15:0]+'d14) > r_MaxFL[15:0] ); 
end



// Latched Retry counter for tx status
always @ (posedge MTxClk or negedge Resetn)
begin
  if(Resetn == 0)
    RetryCntLatched <= 4'h0;
  else
  if(StartTxDone | StartTxAbort)
    RetryCntLatched <= RetryCnt;
end


// Latched Retransmission limit
always @ (posedge MTxClk or negedge Resetn)
begin
  if(Resetn == 0)
    RetryLimit <= 1'h0;
  else
  if(StartTxDone | StartTxAbort)
    RetryLimit <= MaxCollisionOccured;
end


// Latched Late Collision
always @ (posedge MTxClk or negedge Resetn)
begin
  if(Resetn == 0)
    LateCollLatched <= 1'b0;
  else
  if(StartTxDone | StartTxAbort)
    LateCollLatched <= LateCollision;
end



// Latched Defer state
always @ (posedge MTxClk or negedge Resetn)
begin
  if(Resetn == 0)
    DeferLatched <= 1'b0;
  else
  if(DeferIndication)
    DeferLatched <= 1'b1;
  else
  if(RstDeferLatched)
    DeferLatched <= 1'b0;
end


// CarrierSenseLost
always @ (posedge MTxClk or negedge Resetn)
begin
  if(Resetn == 0)
    CarrierSenseLost <= 1'b0;
  else
  if((StatePreamble | StateSFD | StateDA | StateSA | StateLength | (|StateData)) & ~CarrierSense & ~Loopback & ~Collision & ~r_FullD)	
    CarrierSenseLost <= 1'b1;
  else
  if(TxStartFrm)
    CarrierSenseLost <= 1'b0;
end


endmodule


//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date:    17:26:41 06/07/2020 
// Design Name: 
// Module Name:    eth_miim 
// Project Name: 
// Target Devices: 
// Tool versions: 
// Description: 
//
// Dependencies: 
//
// Revision: 
// Revision 0.01 - File Created
// Additional Comments: 
//
//////////////////////////////////////////////////////////////////////////////////

`include "timescale.v"
module eth_miim
(
  Clk,
  Resetn,
  Divider,
  NoPre,
  CtrlData,
  Rgad,
  Fiad,
  WCtrlData,
  RStat,
  ScanStat,
  Mdi,
  Mdo,
  MdoEn,
  Mdc,
  Busy,
  Prsd,
  LinkFail,
  Nvalid,
  WCtrlDataStart,
  RStatStart,
  UpdateMIIRX_DATAReg
);



input         Clk;                // Host Clock
input         Resetn;              // General Resetn
input   [7:0] Divider;            // Divider for the host clock
input  [15:0] CtrlData;           // Control Data (to be written to the PHY reg.)
input   [4:0] Rgad;               // Register Address (within the PHY)
input   [4:0] Fiad;               // PHY Address
input         NoPre;              // No Preamble (no 32-bit preamble)
input         WCtrlData;          // Write Control Data operation
input         RStat;              // Read Status operation
input         ScanStat;           // Scan Status operation
input         Mdi;                // MII Management Data In

output        Mdc;                // MII Management Data Clock
output        Mdo;                // MII Management Data Output
output        MdoEn;              // MII Management Data Output Enable
output        Busy;               // Busy Signal
output        LinkFail;           // Link Integrity Signal
output        Nvalid;             // Invalid Status (qualifier for the valid scan result)

output [15:0] Prsd;               // Read Status Data (data read from the PHY)

output        WCtrlDataStart;     // This signals resets the WCTRLDATA bit in the MIIM Command register
output        RStatStart;         // This signal resets the RSTAT BIT in the MIIM Command register
output        UpdateMIIRX_DATAReg;// Updates MII RX_DATA register with read data


reg           Nvalid;
reg           EndBusy_d;          // Pre-end Busy signal
reg           EndBusy;            // End Busy signal (stops the operation in progress)

reg           WCtrlData_q1;       // Write Control Data operation delayed 1 Clk cycle
reg           WCtrlData_q2;       // Write Control Data operation delayed 2 Clk cycles
reg           WCtrlData_q3;       // Write Control Data operation delayed 3 Clk cycles
reg           WCtrlDataStart;     // Start Write Control Data Command (positive edge detected)
reg           WCtrlDataStart_q;
reg           WCtrlDataStart_q1;  // Start Write Control Data Command delayed 1 Mdc cycle
reg           WCtrlDataStart_q2;  // Start Write Control Data Command delayed 2 Mdc cycles

reg           RStat_q1;           // Read Status operation delayed 1 Clk cycle
reg           RStat_q2;           // Read Status operation delayed 2 Clk cycles
reg           RStat_q3;           // Read Status operation delayed 3 Clk cycles
reg           RStatStart;         // Start Read Status Command (positive edge detected)
reg           RStatStart_q1;      // Start Read Status Command delayed 1 Mdc cycle
reg           RStatStart_q2;      // Start Read Status Command delayed 2 Mdc cycles

reg           ScanStat_q1;        // Scan Status operation delayed 1 cycle
reg           ScanStat_q2;        // Scan Status operation delayed 2 cycles
reg           SyncStatMdcEn;      // Scan Status operation delayed at least cycles and synchronized to MdcEn

wire          WriteDataOp;        // Write Data Operation (positive edge detected)
wire          ReadStatusOp;       // Read Status Operation (positive edge detected)
wire          ScanStatusOp;       // Scan Status Operation (positive edge detected)
wire          StartOp;            // Start Operation (start of any of the preceding operations)
wire          EndOp;              // End of Operation

reg           InProgress;         // Operation in progress
reg           InProgress_q1;      // Operation in progress delayed 1 Mdc cycle
reg           InProgress_q2;      // Operation in progress delayed 2 Mdc cycles
reg           InProgress_q3;      // Operation in progress delayed 3 Mdc cycles

reg           WriteOp;            // Write Operation Latch (When asserted, write operation is in progress)
reg     [6:0] BitCounter;         // Bit Counter


wire    [3:0] ByteSelect;         // Byte Select defines which byte (preamble, data, operation, etc.) is loaded and shifted through the shift register.
wire          MdcEn;              // MII Management Data Clock Enable signal is asserted for one Clk period before Mdc rises.
wire          ShiftedBit;         // This bit is output of the shift register and is connected to the Mdo signal
wire          MdcEn_n;

wire          LatchByte1_d2;
wire          LatchByte0_d2;
reg           LatchByte1_d;
reg           LatchByte0_d;
reg     [1:0] LatchByte;          // Latch Byte selects which part of Read Status Data is updated from the shift register

reg           UpdateMIIRX_DATAReg;// Updates MII RX_DATA register with read data





// Generation of the EndBusy signal. It is used for ending the MII Management operation.
always @ (posedge Clk or negedge Resetn)
begin
  if(Resetn == 0)
    begin
      EndBusy_d <=  1'b0;
      EndBusy <=  1'b0;
    end
  else
    begin
      EndBusy_d <=  ~InProgress_q2 & InProgress_q3;
      EndBusy   <=  EndBusy_d;
    end
end


// Update MII RX_DATA register
always @ (posedge Clk or negedge Resetn)
begin
  if(Resetn == 0)
    UpdateMIIRX_DATAReg <=  0;
  else
  if(EndBusy & ~WCtrlDataStart_q)
    UpdateMIIRX_DATAReg <=  1;
  else
    UpdateMIIRX_DATAReg <=  0;    
end



// Generation of the delayed signals used for positive edge triggering.
always @ (posedge Clk or negedge Resetn)
begin
  if(Resetn == 0)
    begin
      WCtrlData_q1 <=  1'b0;
      WCtrlData_q2 <=  1'b0;
      WCtrlData_q3 <=  1'b0;
      
      RStat_q1 <=  1'b0;
      RStat_q2 <=  1'b0;
      RStat_q3 <=  1'b0;

      ScanStat_q1  <=  1'b0;
      ScanStat_q2  <=  1'b0;
      SyncStatMdcEn <=  1'b0;
    end
  else
    begin
      WCtrlData_q1 <=  WCtrlData;
      WCtrlData_q2 <=  WCtrlData_q1;
      WCtrlData_q3 <=  WCtrlData_q2;

      RStat_q1 <=  RStat;
      RStat_q2 <=  RStat_q1;
      RStat_q3 <=  RStat_q2;

      ScanStat_q1  <=  ScanStat;
      ScanStat_q2  <=  ScanStat_q1;
      if(MdcEn)
        SyncStatMdcEn  <=  ScanStat_q2;
    end
end


// Generation of the Start Commands (Write Control Data or Read Status)
always @ (posedge Clk or negedge Resetn)
begin
  if(Resetn == 0)
    begin
      WCtrlDataStart <=  1'b0;
      WCtrlDataStart_q <=  1'b0;
      RStatStart <=  1'b0;
    end
  else
    begin
      if(EndBusy)
        begin
          WCtrlDataStart <=  1'b0;
          RStatStart <=  1'b0;
        end
      else
        begin
          if(WCtrlData_q2 & ~WCtrlData_q3)
            WCtrlDataStart <=  1'b1;
          if(RStat_q2 & ~RStat_q3)
            RStatStart <=  1'b1;
          WCtrlDataStart_q <=  WCtrlDataStart;
        end
    end
end 


// Generation of the Nvalid signal (indicates when the status is invalid)
always @ (posedge Clk or negedge Resetn)
begin
  if(Resetn == 0)
    Nvalid <=  1'b0;
  else
    begin
      if(~InProgress_q2 & InProgress_q3)
        begin
          Nvalid <=  1'b0;
        end
      else
        begin
          if(ScanStat_q2  & ~SyncStatMdcEn)
            Nvalid <=  1'b1;
        end
    end
end 

// Signals used for the generation of the Operation signals (positive edge)
always @ (posedge Clk or negedge Resetn)
begin
  if(Resetn == 0)
    begin
      WCtrlDataStart_q1 <=  1'b0;
      WCtrlDataStart_q2 <=  1'b0;

      RStatStart_q1 <=  1'b0;
      RStatStart_q2 <=  1'b0;

      InProgress_q1 <=  1'b0;
      InProgress_q2 <=  1'b0;
      InProgress_q3 <=  1'b0;

  	  LatchByte0_d <=  1'b0;
  	  LatchByte1_d <=  1'b0;

  	  LatchByte <=  2'b00;
    end
  else
    begin
      if(MdcEn)
        begin
          WCtrlDataStart_q1 <=  WCtrlDataStart;
          WCtrlDataStart_q2 <=  WCtrlDataStart_q1;

          RStatStart_q1 <=  RStatStart;
          RStatStart_q2 <=  RStatStart_q1;

          LatchByte[0] <=  LatchByte0_d;
          LatchByte[1] <=  LatchByte1_d;

          LatchByte0_d <=  LatchByte0_d2;
          LatchByte1_d <=  LatchByte1_d2;

          InProgress_q1 <=  InProgress;
          InProgress_q2 <=  InProgress_q1;
          InProgress_q3 <=  InProgress_q2;
        end
    end
end 


// Generation of the Operation signals
assign WriteDataOp  = WCtrlDataStart_q1 & ~WCtrlDataStart_q2;    
assign ReadStatusOp = RStatStart_q1     & ~RStatStart_q2;
assign ScanStatusOp = SyncStatMdcEn     & ~InProgress & ~InProgress_q1 & ~InProgress_q2;
assign StartOp      = WriteDataOp | ReadStatusOp | ScanStatusOp;

// Busy
assign Busy = WCtrlData | WCtrlDataStart | RStat | RStatStart | SyncStatMdcEn | EndBusy | InProgress | InProgress_q3 | Nvalid;


// Generation of the InProgress signal (indicates when an operation is in progress)
// Generation of the WriteOp signal (indicates when a write is in progress)
always @ (posedge Clk or negedge Resetn)
begin
  if(Resetn == 0)
    begin
      InProgress <=  1'b0;
      WriteOp <=  1'b0;
    end
  else
    begin
      if(MdcEn)
        begin
          if(StartOp)
            begin
              if(~InProgress)
                WriteOp <=  WriteDataOp;
              InProgress <=  1'b1;
            end
          else
            begin
              if(EndOp)
                begin
                  InProgress <=  1'b0;
                  WriteOp <=  1'b0;
                end
            end
        end
    end
end



// Bit Counter counts from 0 to 63 (from 32 to 63 when NoPre is asserted)
always @ (posedge Clk or negedge Resetn)
begin
  if(Resetn == 0)
    BitCounter[6:0] <=  7'h0;
  else
    begin
      if(MdcEn)
        begin
          if(InProgress)
            begin
              if(NoPre & ( BitCounter == 7'h0 ))
                BitCounter[6:0] <=  7'h21;
              else
                BitCounter[6:0] <=  BitCounter[6:0] + 1;
            end
          else
            BitCounter[6:0] <=  7'h0;
        end
    end
end


// Operation ends when the Bit Counter reaches 63
assign EndOp = BitCounter==63;

assign ByteSelect[0] = InProgress & ((NoPre & (BitCounter == 7'h0)) | (~NoPre & (BitCounter == 7'h20)));
assign ByteSelect[1] = InProgress & (BitCounter == 7'h28);
assign ByteSelect[2] = InProgress & WriteOp & (BitCounter == 7'h30);
assign ByteSelect[3] = InProgress & WriteOp & (BitCounter == 7'h38);


// Latch Byte selects which part of Read Status Data is updated from the shift register
assign LatchByte1_d2 = InProgress & ~WriteOp & BitCounter == 7'h37;
assign LatchByte0_d2 = InProgress & ~WriteOp & BitCounter == 7'h3F;


// Connecting the Clock Generator Module
eth_clockgen clkgen(.Clk(Clk), .Resetn(Resetn), .Divider(Divider[7:0]), .MdcEn(MdcEn), .MdcEn_n(MdcEn_n), .Mdc(Mdc) 
                   );

// Connecting the Shift Register Module
eth_shiftreg shftrg(.Clk(Clk), .Resetn(Resetn), .MdcEn_n(MdcEn_n), .Mdi(Mdi), .Fiad(Fiad), .Rgad(Rgad), 
                    .CtrlData(CtrlData), .WriteOp(WriteOp), .ByteSelect(ByteSelect), .LatchByte(LatchByte), 
                    .ShiftedBit(ShiftedBit), .Prsd(Prsd), .LinkFail(LinkFail)
                   );

// Connecting the Output Control Module
eth_outputcontrol outctrl(.Clk(Clk), .Resetn(Resetn), .MdcEn_n(MdcEn_n), .InProgress(InProgress), 
                          .ShiftedBit(ShiftedBit), .BitCounter(BitCounter), .WriteOp(WriteOp), .NoPre(NoPre), 
                          .Mdo(Mdo), .MdoEn(MdoEn)
                         );

endmodule


//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date:    17:27:02 06/07/2020 
// Design Name: 
// Module Name:    eth_outputcontrol 
// Project Name: 
// Target Devices: 
// Tool versions: 
// Description: 
//
// Dependencies: 
//
// Revision: 
// Revision 0.01 - File Created
// Additional Comments: 
//
//////////////////////////////////////////////////////////////////////////////////

`include "timescale.v"
module eth_outputcontrol(Clk, Resetn, InProgress, ShiftedBit, BitCounter, WriteOp, NoPre, MdcEn_n, Mdo, MdoEn);

input         Clk;                // Host Clock
input         Resetn;              // General Resetn
input         WriteOp;            // Write Operation Latch (When asserted, write operation is in progress)
input         NoPre;              // No Preamble (no 32-bit preamble)
input         InProgress;         // Operation in progress
input         ShiftedBit;         // This bit is output of the shift register and is connected to the Mdo signal
input   [6:0] BitCounter;         // Bit Counter
input         MdcEn_n;            // MII Management Data Clock Enable signal is asserted for one Clk period before Mdc falls.

output        Mdo;                // MII Management Data Output
output        MdoEn;              // MII Management Data Output Enable

wire          SerialEn;

reg           MdoEn_2d;
reg           MdoEn_d;
reg           MdoEn;

reg           Mdo_2d;
reg           Mdo_d;
reg           Mdo;                // MII Management Data Output



// Generation of the Serial Enable signal (enables the serialization of the data)
assign SerialEn =  WriteOp & InProgress & ( BitCounter>31 | ( ( BitCounter == 0 ) & NoPre ) )
                | ~WriteOp & InProgress & (( BitCounter>31 & BitCounter<46 ) | ( ( BitCounter == 0 ) & NoPre ));


// Generation of the MdoEn signal
always @ (posedge Clk or negedge Resetn)
begin
  if(Resetn == 0)
    begin
      MdoEn_2d <=  1'b0;
      MdoEn_d <=  1'b0;
      MdoEn <=  1'b0;
    end
  else
    begin
      if(MdcEn_n)
        begin
          MdoEn_2d <=  SerialEn | InProgress & BitCounter<32;
          MdoEn_d <=  MdoEn_2d;
          MdoEn <=  MdoEn_d;
        end
    end
end


// Generation of the Mdo signal.
always @ (posedge Clk or negedge Resetn)
begin
  if(Resetn == 0)
    begin
      Mdo_2d <=  1'b0;
      Mdo_d <=  1'b0;
      Mdo <=  1'b0;
    end
  else
    begin
      if(MdcEn_n)
        begin
          Mdo_2d <=  ~SerialEn & BitCounter<32;
          Mdo_d <=  ShiftedBit | Mdo_2d;
          Mdo <=  Mdo_d;
        end
    end
end



endmodule


//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date:    17:27:02 06/07/2020 
// Design Name: 
// Module Name:    eth_outputcontrol 
// Project Name: 
// Target Devices: 
// Tool versions: 
// Description: 
//
// Dependencies: 
//
// Revision: 
// Revision 0.01 - File Created
// Additional Comments: 
//
//////////////////////////////////////////////////////////////////////////////////

`include "timescale.v"
module eth_outputcontrol(Clk, Resetn, InProgress, ShiftedBit, BitCounter, WriteOp, NoPre, MdcEn_n, Mdo, MdoEn);

input         Clk;                // Host Clock
input         Resetn;              // General Resetn
input         WriteOp;            // Write Operation Latch (When asserted, write operation is in progress)
input         NoPre;              // No Preamble (no 32-bit preamble)
input         InProgress;         // Operation in progress
input         ShiftedBit;         // This bit is output of the shift register and is connected to the Mdo signal
input   [6:0] BitCounter;         // Bit Counter
input         MdcEn_n;            // MII Management Data Clock Enable signal is asserted for one Clk period before Mdc falls.

output        Mdo;                // MII Management Data Output
output        MdoEn;              // MII Management Data Output Enable

wire          SerialEn;

reg           MdoEn_2d;
reg           MdoEn_d;
reg           MdoEn;

reg           Mdo_2d;
reg           Mdo_d;
reg           Mdo;                // MII Management Data Output



// Generation of the Serial Enable signal (enables the serialization of the data)
assign SerialEn =  WriteOp & InProgress & ( BitCounter>31 | ( ( BitCounter == 0 ) & NoPre ) )
                | ~WriteOp & InProgress & (( BitCounter>31 & BitCounter<46 ) | ( ( BitCounter == 0 ) & NoPre ));


// Generation of the MdoEn signal
always @ (posedge Clk or negedge Resetn)
begin
  if(Resetn == 0)
    begin
      MdoEn_2d <=  1'b0;
      MdoEn_d <=  1'b0;
      MdoEn <=  1'b0;
    end
  else
    begin
      if(MdcEn_n)
        begin
          MdoEn_2d <=  SerialEn | InProgress & BitCounter<32;
          MdoEn_d <=  MdoEn_2d;
          MdoEn <=  MdoEn_d;
        end
    end
end


// Generation of the Mdo signal.
always @ (posedge Clk or negedge Resetn)
begin
  if(Resetn == 0)
    begin
      Mdo_2d <=  1'b0;
      Mdo_d <=  1'b0;
      Mdo <=  1'b0;
    end
  else
    begin
      if(MdcEn_n)
        begin
          Mdo_2d <=  ~SerialEn & BitCounter<32;
          Mdo_d <=  ShiftedBit | Mdo_2d;
          Mdo <=  Mdo_d;
        end
    end
end



endmodule


//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date:    17:27:19 06/07/2020 
// Design Name: 
// Module Name:    eth_random 
// Project Name: 
// Target Devices: 
// Tool versions: 
// Description: 
//
// Dependencies: 
//
// Revision: 
// Revision 0.01 - File Created
// Additional Comments: 
//
//////////////////////////////////////////////////////////////////////////////////

`include "timescale.v"
module eth_random (MTxClk, Resetn, StateJam, StateJam_q, RetryCnt, NibCnt, ByteCnt, 
                   RandomEq0, RandomEqByteCnt);

input MTxClk;
input Resetn;
input StateJam;
input StateJam_q;
input [3:0] RetryCnt;
input [15:0] NibCnt;
input [9:0] ByteCnt;
output RandomEq0;
output RandomEqByteCnt;

wire Feedback;
reg [9:0] x;
wire [9:0] Random;
reg  [9:0] RandomLatched;


always @ (posedge MTxClk or negedge Resetn)
begin
  if(Resetn == 0)
    x[9:0] <=  0;
  else
    x[9:0] <=  {x[8:0], Feedback};
end

assign Feedback = ~(x[2] ^ x[9]);

assign Random [0] = x[0];
assign Random [1] = (RetryCnt > 1) ? x[1] : 1'b0;
assign Random [2] = (RetryCnt > 2) ? x[2] : 1'b0;
assign Random [3] = (RetryCnt > 3) ? x[3] : 1'b0;
assign Random [4] = (RetryCnt > 4) ? x[4] : 1'b0;
assign Random [5] = (RetryCnt > 5) ? x[5] : 1'b0;
assign Random [6] = (RetryCnt > 6) ? x[6] : 1'b0;
assign Random [7] = (RetryCnt > 7) ? x[7] : 1'b0;
assign Random [8] = (RetryCnt > 8) ? x[8] : 1'b0;
assign Random [9] = (RetryCnt > 9) ? x[9] : 1'b0;


always @ (posedge MTxClk or negedge Resetn)
begin
  if(Resetn == 0)
    RandomLatched <=  10'h000;
  else
    begin
      if(StateJam & StateJam_q)
        RandomLatched <=  Random;
    end
end

// Random Number == 0      IEEE 802.3 page 68. If 0 we go to defer and not to backoff.
assign RandomEq0 = RandomLatched == 10'h0; 

assign RandomEqByteCnt = ByteCnt[9:0] == RandomLatched & (&NibCnt[6:0]);

endmodule


//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date:    17:27:42 06/07/2020 
// Design Name: 
// Module Name:    eth_receivecontrol 
// Project Name: 
// Target Devices: 
// Tool versions: 
// Description: 
//
// Dependencies: 
//
// Revision: 
// Revision 0.01 - File Created
// Additional Comments: 
//
//////////////////////////////////////////////////////////////////////////////////
`include "timescale.v"
module eth_receivecontrol (MTxClk, MRxClk, TxResetn, RxResetn, RxData, RxValid, RxStartFrm, 
                           RxEndFrm, RxFlow, ReceiveEnd, MAC, DlyCrcEn, TxDoneIn, 
                           TxAbortIn, TxStartFrmOut, ReceivedLengthOK, ReceivedPacketGood, 
                           TxUsedDataOutDetected, Pause, ReceivedPauseFrm, AddressOK, 
                           RxStatusWriteLatched_sync2, r_PassAll, SetPauseTimer
                          );


input       MTxClk;
input       MRxClk;
input       TxResetn; 
input       RxResetn; 
input [7:0] RxData;
input       RxValid;
input       RxStartFrm;
input       RxEndFrm;
input       RxFlow;
input       ReceiveEnd;
input [47:0]MAC;
input       DlyCrcEn;
input       TxDoneIn;
input       TxAbortIn;
input       TxStartFrmOut;
input       ReceivedLengthOK;
input       ReceivedPacketGood;
input       TxUsedDataOutDetected;
input       RxStatusWriteLatched_sync2;
input       r_PassAll;

output      Pause;
output      ReceivedPauseFrm;
output      AddressOK;
output      SetPauseTimer;


reg         Pause;
reg         AddressOK;                // Multicast or unicast address detected
reg         TypeLengthOK;             // Type/Length field contains 0x8808
reg         DetectionWindow;          // Detection of the PAUSE frame is possible within this window
reg         OpCodeOK;                 // PAUSE opcode detected (0x0001)
reg  [2:0]  DlyCrcCnt;
reg  [4:0]  ByteCnt;
reg [15:0]  AssembledTimerValue;
reg [15:0]  LatchedTimerValue;
reg         ReceivedPauseFrm;
reg         ReceivedPauseFrmWAddr;
reg         PauseTimerEq0_sync1;
reg         PauseTimerEq0_sync2;
reg [15:0]  PauseTimer;
reg         Divider2;
reg  [5:0]  SlotTimer;

wire [47:0] ReservedMulticast;        // 0x0180C2000001
wire [15:0] TypeLength;               // 0x8808
wire        ResetByteCnt;             // 
wire        IncrementByteCnt;         // 
wire        ByteCntEq0;               // ByteCnt = 0
wire        ByteCntEq1;               // ByteCnt = 1
wire        ByteCntEq2;               // ByteCnt = 2
wire        ByteCntEq3;               // ByteCnt = 3
wire        ByteCntEq4;               // ByteCnt = 4
wire        ByteCntEq5;               // ByteCnt = 5
wire        ByteCntEq12;              // ByteCnt = 12
wire        ByteCntEq13;              // ByteCnt = 13
wire        ByteCntEq14;              // ByteCnt = 14
wire        ByteCntEq15;              // ByteCnt = 15
wire        ByteCntEq16;              // ByteCnt = 16
wire        ByteCntEq17;              // ByteCnt = 17
wire        ByteCntEq18;              // ByteCnt = 18
wire        DecrementPauseTimer;      // 
wire        PauseTimerEq0;            // 
wire        ResetSlotTimer;           // 
wire        IncrementSlotTimer;       // 
wire        SlotFinished;             // 



// Reserved multicast address and Type/Length for PAUSE control
assign ReservedMulticast = 48'h0180C2000001;
assign TypeLength = 16'h8808;


// Address Detection (Multicast or unicast)
always @ (posedge MRxClk or negedge RxResetn)
begin
  if(RxResetn == 0)
    AddressOK <=  1'b0;
  else
  if(DetectionWindow & ByteCntEq0)  
    AddressOK <=   RxData[7:0] == ReservedMulticast[47:40] | RxData[7:0] == MAC[47:40];
  else
  if(DetectionWindow & ByteCntEq1)
    AddressOK <=  (RxData[7:0] == ReservedMulticast[39:32] | RxData[7:0] == MAC[39:32]) & AddressOK;
  else
  if(DetectionWindow & ByteCntEq2)
    AddressOK <=  (RxData[7:0] == ReservedMulticast[31:24] | RxData[7:0] == MAC[31:24]) & AddressOK;
  else
  if(DetectionWindow & ByteCntEq3)
    AddressOK <=  (RxData[7:0] == ReservedMulticast[23:16] | RxData[7:0] == MAC[23:16]) & AddressOK;
  else
  if(DetectionWindow & ByteCntEq4)
    AddressOK <=  (RxData[7:0] == ReservedMulticast[15:8]  | RxData[7:0] == MAC[15:8])  & AddressOK;
  else
  if(DetectionWindow & ByteCntEq5)
    AddressOK <=  (RxData[7:0] == ReservedMulticast[7:0]   | RxData[7:0] == MAC[7:0])   & AddressOK;
  else
  if(ReceiveEnd)
    AddressOK <=  1'b0;
end



// TypeLengthOK (Type/Length Control frame detected)
always @ (posedge MRxClk or negedge RxResetn )
begin
  if(RxResetn == 0)
    TypeLengthOK <=  1'b0;
  else
  if(DetectionWindow & ByteCntEq12) 
    TypeLengthOK <=  ByteCntEq12 & (RxData[7:0] == TypeLength[15:8]);
  else
  if(DetectionWindow & ByteCntEq13)
    TypeLengthOK <=  ByteCntEq13 & (RxData[7:0] == TypeLength[7:0]) & TypeLengthOK;
  else
  if(ReceiveEnd)
    TypeLengthOK <=  1'b0;
end



// Latch Control Frame Opcode
always @ (posedge MRxClk or negedge RxResetn )
begin
  if(RxResetn == 0)
    OpCodeOK <=  1'b0;
  else
  if(ByteCntEq16)
    OpCodeOK <=  1'b0;
  else
    begin
      if(DetectionWindow & ByteCntEq14)  
        OpCodeOK <=  ByteCntEq14 & RxData[7:0] == 8'h00;
    
      if(DetectionWindow & ByteCntEq15)
        OpCodeOK <=  ByteCntEq15 & RxData[7:0] == 8'h01 & OpCodeOK;
    end
end


// ReceivedPauseFrmWAddr (+Address Check)
always @ (posedge MRxClk or negedge RxResetn )
begin
  if(RxResetn == 0)
    ReceivedPauseFrmWAddr <=  1'b0;
  else
  if(ReceiveEnd)
    ReceivedPauseFrmWAddr <=  1'b0;
  else
  if(ByteCntEq16 & TypeLengthOK & OpCodeOK & AddressOK)
    ReceivedPauseFrmWAddr <=  1'b1;        
end



// Assembling 16-bit timer value from two 8-bit data
always @ (posedge MRxClk or negedge RxResetn )
begin
  if(RxResetn == 0)
    AssembledTimerValue[15:0] <=  16'h0;
  else
  if(RxStartFrm)
    AssembledTimerValue[15:0] <=  16'h0;
  else
    begin
      if(DetectionWindow & ByteCntEq16) 
        AssembledTimerValue[15:8] <=  RxData[7:0];
      if(DetectionWindow & ByteCntEq17)
        AssembledTimerValue[7:0] <=  RxData[7:0];
    end
end


// Detection window (while PAUSE detection is possible)
always @ (posedge MRxClk or negedge RxResetn )
begin
  if(RxResetn == 0)
    DetectionWindow <=  1'b1;
  else
  if(ByteCntEq18)
    DetectionWindow <=  1'b0;
  else
  if(ReceiveEnd)
    DetectionWindow <=  1'b1;
end



// Latching Timer Value
always @ (posedge MRxClk or negedge RxResetn )
begin
  if(RxResetn == 0)
    LatchedTimerValue[15:0] <=  16'h0;
  else
  if(DetectionWindow &  ReceivedPauseFrmWAddr &  ByteCntEq18)
    LatchedTimerValue[15:0] <=  AssembledTimerValue[15:0];
  else
  if(ReceiveEnd)
    LatchedTimerValue[15:0] <=  16'h0;
end



// Delayed CEC counter
always @ (posedge MRxClk or negedge RxResetn)
begin
  if(RxResetn == 0)
    DlyCrcCnt <=  3'h0;
  else
  if(RxValid & RxEndFrm)
    DlyCrcCnt <=  3'h0;
  else
  if(RxValid & ~RxEndFrm & ~DlyCrcCnt[2])
    DlyCrcCnt <=  DlyCrcCnt + 3'd1;
end

             
assign ResetByteCnt = RxEndFrm;
assign IncrementByteCnt = RxValid & DetectionWindow & ~ByteCntEq18 & 
			  (~DlyCrcEn | DlyCrcEn & DlyCrcCnt[2]);


// Byte counter
always @ (posedge MRxClk or negedge RxResetn)
begin
  if(RxResetn == 0)
    ByteCnt[4:0] <=  5'h0;
  else
  if(ResetByteCnt)
    ByteCnt[4:0] <=  5'h0;
  else
  if(IncrementByteCnt)
    ByteCnt[4:0] <=  ByteCnt[4:0] + 5'd1;
end


assign ByteCntEq0 = RxValid & ByteCnt[4:0] == 5'h0;
assign ByteCntEq1 = RxValid & ByteCnt[4:0] == 5'h1;
assign ByteCntEq2 = RxValid & ByteCnt[4:0] == 5'h2;
assign ByteCntEq3 = RxValid & ByteCnt[4:0] == 5'h3;
assign ByteCntEq4 = RxValid & ByteCnt[4:0] == 5'h4;
assign ByteCntEq5 = RxValid & ByteCnt[4:0] == 5'h5;
assign ByteCntEq12 = RxValid & ByteCnt[4:0] == 5'h0C;
assign ByteCntEq13 = RxValid & ByteCnt[4:0] == 5'h0D;
assign ByteCntEq14 = RxValid & ByteCnt[4:0] == 5'h0E;
assign ByteCntEq15 = RxValid & ByteCnt[4:0] == 5'h0F;
assign ByteCntEq16 = RxValid & ByteCnt[4:0] == 5'h10;
assign ByteCntEq17 = RxValid & ByteCnt[4:0] == 5'h11;
assign ByteCntEq18 = RxValid & ByteCnt[4:0] == 5'h12 & DetectionWindow;


assign SetPauseTimer = ReceiveEnd & ReceivedPauseFrmWAddr & ReceivedPacketGood & ReceivedLengthOK & RxFlow;
assign DecrementPauseTimer = SlotFinished & |PauseTimer;


// PauseTimer[15:0]
always @ (posedge MRxClk or negedge RxResetn)
begin
  if(RxResetn == 0)
    PauseTimer[15:0] <=  16'h0;
  else
  if(SetPauseTimer)
    PauseTimer[15:0] <=  LatchedTimerValue[15:0];
  else
  if(DecrementPauseTimer)
    PauseTimer[15:0] <=  PauseTimer[15:0] - 16'd1;
end

assign PauseTimerEq0 = ~(|PauseTimer[15:0]);



// Synchronization of the pause timer
always @ (posedge MTxClk or negedge TxResetn)
begin
  if(TxResetn == 0)
    begin
      PauseTimerEq0_sync1 <=  1'b1;
      PauseTimerEq0_sync2 <=  1'b1;
    end
  else
    begin
      PauseTimerEq0_sync1 <=  PauseTimerEq0;
      PauseTimerEq0_sync2 <=  PauseTimerEq0_sync1;
    end
end


// Pause signal generation
always @ (posedge MTxClk or negedge TxResetn)
begin
  if(TxResetn == 0)
    Pause <=  1'b0;
  else
  if((TxDoneIn | TxAbortIn | ~TxUsedDataOutDetected) & ~TxStartFrmOut)
    Pause <=  RxFlow & ~PauseTimerEq0_sync2;
end


// Divider2 is used for incrementing the Slot timer every other clock
always @ (posedge MRxClk or negedge RxResetn)
begin
  if(RxResetn == 0)
    Divider2 <=  1'b0;
  else
  if(|PauseTimer[15:0] & RxFlow)
    Divider2 <=  ~Divider2;
  else
    Divider2 <=  1'b0;
end


assign ResetSlotTimer = (RxResetn == 0);
assign IncrementSlotTimer =  Pause & RxFlow & Divider2;


// SlotTimer
always @ (posedge MRxClk or negedge RxResetn)
begin
  if(RxResetn == 0)
    SlotTimer[5:0] <=  6'h0;
  else
  if(ResetSlotTimer)
    SlotTimer[5:0] <=  6'h0;
  else
  if(IncrementSlotTimer)
    SlotTimer[5:0] <=  SlotTimer[5:0] + 6'd1;
end


assign SlotFinished = &SlotTimer[5:0] & IncrementSlotTimer;  // Slot is 512 bits (64 bytes)



// Pause Frame received
always @ (posedge MRxClk or negedge RxResetn)
begin
  if(RxResetn == 0)
    ReceivedPauseFrm <= 1'b0;
  else
  if(RxStatusWriteLatched_sync2 & r_PassAll | ReceivedPauseFrm & (~r_PassAll))
    ReceivedPauseFrm <= 1'b0;
  else
  if(ByteCntEq16 & TypeLengthOK & OpCodeOK)
    ReceivedPauseFrm <= 1'b1;        
end

endmodule


//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date:    17:27:42 06/07/2020 
// Design Name: 
// Module Name:    eth_receivecontrol 
// Project Name: 
// Target Devices: 
// Tool versions: 
// Description: 
//
// Dependencies: 
//
// Revision: 
// Revision 0.01 - File Created
// Additional Comments: 
//
//////////////////////////////////////////////////////////////////////////////////
`include "timescale.v"
module eth_receivecontrol (MTxClk, MRxClk, TxResetn, RxResetn, RxData, RxValid, RxStartFrm, 
                           RxEndFrm, RxFlow, ReceiveEnd, MAC, DlyCrcEn, TxDoneIn, 
                           TxAbortIn, TxStartFrmOut, ReceivedLengthOK, ReceivedPacketGood, 
                           TxUsedDataOutDetected, Pause, ReceivedPauseFrm, AddressOK, 
                           RxStatusWriteLatched_sync2, r_PassAll, SetPauseTimer
                          );


input       MTxClk;
input       MRxClk;
input       TxResetn; 
input       RxResetn; 
input [7:0] RxData;
input       RxValid;
input       RxStartFrm;
input       RxEndFrm;
input       RxFlow;
input       ReceiveEnd;
input [47:0]MAC;
input       DlyCrcEn;
input       TxDoneIn;
input       TxAbortIn;
input       TxStartFrmOut;
input       ReceivedLengthOK;
input       ReceivedPacketGood;
input       TxUsedDataOutDetected;
input       RxStatusWriteLatched_sync2;
input       r_PassAll;

output      Pause;
output      ReceivedPauseFrm;
output      AddressOK;
output      SetPauseTimer;


reg         Pause;
reg         AddressOK;                // Multicast or unicast address detected
reg         TypeLengthOK;             // Type/Length field contains 0x8808
reg         DetectionWindow;          // Detection of the PAUSE frame is possible within this window
reg         OpCodeOK;                 // PAUSE opcode detected (0x0001)
reg  [2:0]  DlyCrcCnt;
reg  [4:0]  ByteCnt;
reg [15:0]  AssembledTimerValue;
reg [15:0]  LatchedTimerValue;
reg         ReceivedPauseFrm;
reg         ReceivedPauseFrmWAddr;
reg         PauseTimerEq0_sync1;
reg         PauseTimerEq0_sync2;
reg [15:0]  PauseTimer;
reg         Divider2;
reg  [5:0]  SlotTimer;

wire [47:0] ReservedMulticast;        // 0x0180C2000001
wire [15:0] TypeLength;               // 0x8808
wire        ResetByteCnt;             // 
wire        IncrementByteCnt;         // 
wire        ByteCntEq0;               // ByteCnt = 0
wire        ByteCntEq1;               // ByteCnt = 1
wire        ByteCntEq2;               // ByteCnt = 2
wire        ByteCntEq3;               // ByteCnt = 3
wire        ByteCntEq4;               // ByteCnt = 4
wire        ByteCntEq5;               // ByteCnt = 5
wire        ByteCntEq12;              // ByteCnt = 12
wire        ByteCntEq13;              // ByteCnt = 13
wire        ByteCntEq14;              // ByteCnt = 14
wire        ByteCntEq15;              // ByteCnt = 15
wire        ByteCntEq16;              // ByteCnt = 16
wire        ByteCntEq17;              // ByteCnt = 17
wire        ByteCntEq18;              // ByteCnt = 18
wire        DecrementPauseTimer;      // 
wire        PauseTimerEq0;            // 
wire        ResetSlotTimer;           // 
wire        IncrementSlotTimer;       // 
wire        SlotFinished;             // 



// Reserved multicast address and Type/Length for PAUSE control
assign ReservedMulticast = 48'h0180C2000001;
assign TypeLength = 16'h8808;


// Address Detection (Multicast or unicast)
always @ (posedge MRxClk or negedge RxResetn)
begin
  if(RxResetn == 0)
    AddressOK <=  1'b0;
  else
  if(DetectionWindow & ByteCntEq0)  
    AddressOK <=   RxData[7:0] == ReservedMulticast[47:40] | RxData[7:0] == MAC[47:40];
  else
  if(DetectionWindow & ByteCntEq1)
    AddressOK <=  (RxData[7:0] == ReservedMulticast[39:32] | RxData[7:0] == MAC[39:32]) & AddressOK;
  else
  if(DetectionWindow & ByteCntEq2)
    AddressOK <=  (RxData[7:0] == ReservedMulticast[31:24] | RxData[7:0] == MAC[31:24]) & AddressOK;
  else
  if(DetectionWindow & ByteCntEq3)
    AddressOK <=  (RxData[7:0] == ReservedMulticast[23:16] | RxData[7:0] == MAC[23:16]) & AddressOK;
  else
  if(DetectionWindow & ByteCntEq4)
    AddressOK <=  (RxData[7:0] == ReservedMulticast[15:8]  | RxData[7:0] == MAC[15:8])  & AddressOK;
  else
  if(DetectionWindow & ByteCntEq5)
    AddressOK <=  (RxData[7:0] == ReservedMulticast[7:0]   | RxData[7:0] == MAC[7:0])   & AddressOK;
  else
  if(ReceiveEnd)
    AddressOK <=  1'b0;
end



// TypeLengthOK (Type/Length Control frame detected)
always @ (posedge MRxClk or negedge RxResetn )
begin
  if(RxResetn == 0)
    TypeLengthOK <=  1'b0;
  else
  if(DetectionWindow & ByteCntEq12) 
    TypeLengthOK <=  ByteCntEq12 & (RxData[7:0] == TypeLength[15:8]);
  else
  if(DetectionWindow & ByteCntEq13)
    TypeLengthOK <=  ByteCntEq13 & (RxData[7:0] == TypeLength[7:0]) & TypeLengthOK;
  else
  if(ReceiveEnd)
    TypeLengthOK <=  1'b0;
end



// Latch Control Frame Opcode
always @ (posedge MRxClk or negedge RxResetn )
begin
  if(RxResetn == 0)
    OpCodeOK <=  1'b0;
  else
  if(ByteCntEq16)
    OpCodeOK <=  1'b0;
  else
    begin
      if(DetectionWindow & ByteCntEq14)  
        OpCodeOK <=  ByteCntEq14 & RxData[7:0] == 8'h00;
    
      if(DetectionWindow & ByteCntEq15)
        OpCodeOK <=  ByteCntEq15 & RxData[7:0] == 8'h01 & OpCodeOK;
    end
end


// ReceivedPauseFrmWAddr (+Address Check)
always @ (posedge MRxClk or negedge RxResetn )
begin
  if(RxResetn == 0)
    ReceivedPauseFrmWAddr <=  1'b0;
  else
  if(ReceiveEnd)
    ReceivedPauseFrmWAddr <=  1'b0;
  else
  if(ByteCntEq16 & TypeLengthOK & OpCodeOK & AddressOK)
    ReceivedPauseFrmWAddr <=  1'b1;        
end



// Assembling 16-bit timer value from two 8-bit data
always @ (posedge MRxClk or negedge RxResetn )
begin
  if(RxResetn == 0)
    AssembledTimerValue[15:0] <=  16'h0;
  else
  if(RxStartFrm)
    AssembledTimerValue[15:0] <=  16'h0;
  else
    begin
      if(DetectionWindow & ByteCntEq16) 
        AssembledTimerValue[15:8] <=  RxData[7:0];
      if(DetectionWindow & ByteCntEq17)
        AssembledTimerValue[7:0] <=  RxData[7:0];
    end
end


// Detection window (while PAUSE detection is possible)
always @ (posedge MRxClk or negedge RxResetn )
begin
  if(RxResetn == 0)
    DetectionWindow <=  1'b1;
  else
  if(ByteCntEq18)
    DetectionWindow <=  1'b0;
  else
  if(ReceiveEnd)
    DetectionWindow <=  1'b1;
end



// Latching Timer Value
always @ (posedge MRxClk or negedge RxResetn )
begin
  if(RxResetn == 0)
    LatchedTimerValue[15:0] <=  16'h0;
  else
  if(DetectionWindow &  ReceivedPauseFrmWAddr &  ByteCntEq18)
    LatchedTimerValue[15:0] <=  AssembledTimerValue[15:0];
  else
  if(ReceiveEnd)
    LatchedTimerValue[15:0] <=  16'h0;
end



// Delayed CEC counter
always @ (posedge MRxClk or negedge RxResetn)
begin
  if(RxResetn == 0)
    DlyCrcCnt <=  3'h0;
  else
  if(RxValid & RxEndFrm)
    DlyCrcCnt <=  3'h0;
  else
  if(RxValid & ~RxEndFrm & ~DlyCrcCnt[2])
    DlyCrcCnt <=  DlyCrcCnt + 3'd1;
end

             
assign ResetByteCnt = RxEndFrm;
assign IncrementByteCnt = RxValid & DetectionWindow & ~ByteCntEq18 & 
			  (~DlyCrcEn | DlyCrcEn & DlyCrcCnt[2]);


// Byte counter
always @ (posedge MRxClk or negedge RxResetn)
begin
  if(RxResetn == 0)
    ByteCnt[4:0] <=  5'h0;
  else
  if(ResetByteCnt)
    ByteCnt[4:0] <=  5'h0;
  else
  if(IncrementByteCnt)
    ByteCnt[4:0] <=  ByteCnt[4:0] + 5'd1;
end


assign ByteCntEq0 = RxValid & ByteCnt[4:0] == 5'h0;
assign ByteCntEq1 = RxValid & ByteCnt[4:0] == 5'h1;
assign ByteCntEq2 = RxValid & ByteCnt[4:0] == 5'h2;
assign ByteCntEq3 = RxValid & ByteCnt[4:0] == 5'h3;
assign ByteCntEq4 = RxValid & ByteCnt[4:0] == 5'h4;
assign ByteCntEq5 = RxValid & ByteCnt[4:0] == 5'h5;
assign ByteCntEq12 = RxValid & ByteCnt[4:0] == 5'h0C;
assign ByteCntEq13 = RxValid & ByteCnt[4:0] == 5'h0D;
assign ByteCntEq14 = RxValid & ByteCnt[4:0] == 5'h0E;
assign ByteCntEq15 = RxValid & ByteCnt[4:0] == 5'h0F;
assign ByteCntEq16 = RxValid & ByteCnt[4:0] == 5'h10;
assign ByteCntEq17 = RxValid & ByteCnt[4:0] == 5'h11;
assign ByteCntEq18 = RxValid & ByteCnt[4:0] == 5'h12 & DetectionWindow;


assign SetPauseTimer = ReceiveEnd & ReceivedPauseFrmWAddr & ReceivedPacketGood & ReceivedLengthOK & RxFlow;
assign DecrementPauseTimer = SlotFinished & |PauseTimer;


// PauseTimer[15:0]
always @ (posedge MRxClk or negedge RxResetn)
begin
  if(RxResetn == 0)
    PauseTimer[15:0] <=  16'h0;
  else
  if(SetPauseTimer)
    PauseTimer[15:0] <=  LatchedTimerValue[15:0];
  else
  if(DecrementPauseTimer)
    PauseTimer[15:0] <=  PauseTimer[15:0] - 16'd1;
end

assign PauseTimerEq0 = ~(|PauseTimer[15:0]);



// Synchronization of the pause timer
always @ (posedge MTxClk or negedge TxResetn)
begin
  if(TxResetn == 0)
    begin
      PauseTimerEq0_sync1 <=  1'b1;
      PauseTimerEq0_sync2 <=  1'b1;
    end
  else
    begin
      PauseTimerEq0_sync1 <=  PauseTimerEq0;
      PauseTimerEq0_sync2 <=  PauseTimerEq0_sync1;
    end
end


// Pause signal generation
always @ (posedge MTxClk or negedge TxResetn)
begin
  if(TxResetn == 0)
    Pause <=  1'b0;
  else
  if((TxDoneIn | TxAbortIn | ~TxUsedDataOutDetected) & ~TxStartFrmOut)
    Pause <=  RxFlow & ~PauseTimerEq0_sync2;
end


// Divider2 is used for incrementing the Slot timer every other clock
always @ (posedge MRxClk or negedge RxResetn)
begin
  if(RxResetn == 0)
    Divider2 <=  1'b0;
  else
  if(|PauseTimer[15:0] & RxFlow)
    Divider2 <=  ~Divider2;
  else
    Divider2 <=  1'b0;
end


assign ResetSlotTimer = (RxResetn == 0);
assign IncrementSlotTimer =  Pause & RxFlow & Divider2;


// SlotTimer
always @ (posedge MRxClk or negedge RxResetn)
begin
  if(RxResetn == 0)
    SlotTimer[5:0] <=  6'h0;
  else
  if(ResetSlotTimer)
    SlotTimer[5:0] <=  6'h0;
  else
  if(IncrementSlotTimer)
    SlotTimer[5:0] <=  SlotTimer[5:0] + 6'd1;
end


assign SlotFinished = &SlotTimer[5:0] & IncrementSlotTimer;  // Slot is 512 bits (64 bytes)



// Pause Frame received
always @ (posedge MRxClk or negedge RxResetn)
begin
  if(RxResetn == 0)
    ReceivedPauseFrm <= 1'b0;
  else
  if(RxStatusWriteLatched_sync2 & r_PassAll | ReceivedPauseFrm & (~r_PassAll))
    ReceivedPauseFrm <= 1'b0;
  else
  if(ByteCntEq16 & TypeLengthOK & OpCodeOK)
    ReceivedPauseFrm <= 1'b1;        
end

endmodule


//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date:    17:38:45 06/07/2020 
// Design Name: 
// Module Name:    eth_registers 
// Project Name: 
// Target Devices: 
// Tool versions: 
// Description: 
//
// Dependencies: 
//
// Revision: 
// Revision 0.01 - File Created
// Additional Comments: 
//
//////////////////////////////////////////////////////////////////////////////////
`include "ethmac_defines.v"
`include "timescale.v"
module eth_registers( wdata, addr, Rw, Cs, Clk, Resetn, DataOut, 
                      r_RecSmall, r_Pad, r_HugEn, r_CrcEn, r_DlyCrcEn, 
                      r_FullD, r_ExDfrEn, r_NoBckof, r_LoopBck, r_IFG, 
                      r_Pro, r_Iam, r_Bro, r_NoPre, r_TxEn, r_RxEn, 
                      TxB_IRQ, TxE_IRQ, RxB_IRQ, RxE_IRQ,Busy_IRQ, 
                      r_IPGT, r_IPGR1, r_IPGR2, r_MinFL, r_MaxFL, r_MaxRet, 
                      r_CollValid, r_TxFlow, r_RxFlow, r_PassAll, 
                      r_MiiNoPre, r_ClkDiv, r_WCtrlData, r_RStat, r_ScanStat, 
                      r_RGAD, r_FIAD, r_CtrlData, NValid_stat, Busy_stat, 
                      LinkFail, r_MAC, WCtrlDataStart, RStatStart,
                      UpdateMIIRX_DATAReg, Prsd, r_TxBDNum, int_o,
                      r_HASH0, r_HASH1, r_TxPauseTV, r_TxPauseRq, RstTxPauseRq, TxCtrlEndFrm,
                      dbg_dat,
                      StartTxDone, TxClk, RxClk, SetPauseTimer
                    );

input [31:0] wdata;
input [7:0] addr;

input Rw;
input [3:0] Cs;
input Clk;
input Resetn;

input WCtrlDataStart;
input RStatStart;

input UpdateMIIRX_DATAReg;
input [15:0] Prsd;

output [31:0] DataOut;
reg    [31:0] DataOut;

output r_RecSmall;
output r_Pad;
output r_HugEn;
output r_CrcEn;
output r_DlyCrcEn;
output r_FullD;
output r_ExDfrEn;
output r_NoBckof;
output r_LoopBck;
output r_IFG;
output r_Pro;
output r_Iam;
output r_Bro;
output r_NoPre;
output r_TxEn;
output r_RxEn;
output [31:0] r_HASH0;
output [31:0] r_HASH1;

input TxB_IRQ;
input TxE_IRQ;
input RxB_IRQ;
input RxE_IRQ;
input Busy_IRQ;


output [6:0] r_IPGT;

output [6:0] r_IPGR1;

output [6:0] r_IPGR2;

output [15:0] r_MinFL;
output [15:0] r_MaxFL;

output [3:0] r_MaxRet;
output [5:0] r_CollValid;

output r_TxFlow;
output r_RxFlow;
output r_PassAll;

output r_MiiNoPre;
output [7:0] r_ClkDiv;

output r_WCtrlData;
output r_RStat;
output r_ScanStat;

output [4:0] r_RGAD;
output [4:0] r_FIAD;

output [15:0]r_CtrlData;


input NValid_stat;
input Busy_stat;
input LinkFail;

output [47:0]r_MAC;
output [7:0] r_TxBDNum;
output       int_o;
output [15:0]r_TxPauseTV;
output       r_TxPauseRq;
input        RstTxPauseRq;
input        TxCtrlEndFrm;
input        StartTxDone;
input        TxClk;
input        RxClk;
input        SetPauseTimer;

input [31:0] dbg_dat; // debug data input

reg          irq_txb;
reg          irq_txe;
reg          irq_rxb;
reg          irq_rxe;
reg          irq_busy;
reg          irq_txc;
reg          irq_rxc;
reg 		 irq_txshortframe;
reg 		 irq_txbigframe;

reg SetTxCIrq_txclk;
reg SetTxCIrq_sync1, SetTxCIrq_sync2, SetTxCIrq_sync3;
reg SetTxCIrq;
reg ResetTxCIrq_sync1, ResetTxCIrq_sync2;

reg SetRxCIrq_rxclk;
reg SetRxCIrq_sync1, SetRxCIrq_sync2, SetRxCIrq_sync3;
reg SetRxCIrq;
reg ResetRxCIrq_sync1;
reg ResetRxCIrq_sync2;
reg ResetRxCIrq_sync3;

wire [3:0] Write =   Cs  & {4{Rw}};
wire       Read  = (|Cs) &   ~Rw;

//Moschip Team
//Note:wdata and addr should be sampled when the psel and penable = 1 and pready = 1.
//
wire [31:0] DataIn = Cs  & {4{Rw}}?wdata:'hz;		
wire [7:0] Address = Cs?addr:'hz;

wire MODER_Sel      = (Address == `ETH_MODER_ADR       );
wire INT_SOURCE_Sel = (Address == `ETH_INT_SOURCE_ADR  );
wire INT_MASK_Sel   = (Address == `ETH_INT_MASK_ADR    );
wire IPGT_Sel       = (Address == `ETH_IPGT_ADR        );
wire IPGR1_Sel      = (Address == `ETH_IPGR1_ADR       );
wire IPGR2_Sel      = (Address == `ETH_IPGR2_ADR       );
wire PACKETLEN_Sel  = (Address == `ETH_PACKETLEN_ADR   );
wire COLLCONF_Sel   = (Address == `ETH_COLLCONF_ADR    );
     
wire CTRLMODER_Sel  = (Address == `ETH_CTRLMODER_ADR   );
wire MIIMODER_Sel   = (Address == `ETH_MIIMODER_ADR    );
wire MIICOMMAND_Sel = (Address == `ETH_MIICOMMAND_ADR  );
wire MIIADDRESS_Sel = (Address == `ETH_MIIADDRESS_ADR  );
wire MIITX_DATA_Sel = (Address == `ETH_MIITX_DATA_ADR  );
wire MAC_ADDR0_Sel  = (Address == `ETH_MAC_ADDR0_ADR   );
wire MAC_ADDR1_Sel  = (Address == `ETH_MAC_ADDR1_ADR   );
wire HASH0_Sel      = (Address == `ETH_HASH0_ADR       );
wire HASH1_Sel      = (Address == `ETH_HASH1_ADR       );
wire TXCTRL_Sel     = (Address == `ETH_TX_CTRL_ADR     );
wire RXCTRL_Sel     = (Address == `ETH_RX_CTRL_ADR     );
wire DBG_REG_Sel    = (Address == `ETH_DBG_ADR         );
wire TX_BD_NUM_Sel  = (Address == `ETH_TX_BD_NUM_ADR   );


wire [2:0] MODER_Wr;
wire [0:0] INT_SOURCE_Wr;
wire [0:0] INT_MASK_Wr;
wire [0:0] IPGT_Wr;
wire [0:0] IPGR1_Wr;
wire [0:0] IPGR2_Wr;
wire [3:0] PACKETLEN_Wr;
wire [2:0] COLLCONF_Wr;
wire [0:0] CTRLMODER_Wr;
wire [1:0] MIIMODER_Wr;
wire [0:0] MIICOMMAND_Wr;
wire [1:0] MIIADDRESS_Wr;
wire [1:0] MIITX_DATA_Wr;
wire       MIIRX_DATA_Wr;
wire [3:0] MAC_ADDR0_Wr;
wire [1:0] MAC_ADDR1_Wr;
wire [3:0] HASH0_Wr;
wire [3:0] HASH1_Wr;
wire [2:0] TXCTRL_Wr;
wire [0:0] TX_BD_NUM_Wr;

assign MODER_Wr[0]       = Write[0]  & MODER_Sel; 
assign MODER_Wr[1]       = Write[1]  & MODER_Sel; 
assign MODER_Wr[2]       = Write[2]  & MODER_Sel; 
assign INT_SOURCE_Wr[0]  = Write[0]  & INT_SOURCE_Sel; 
assign INT_MASK_Wr[0]    = Write[0]  & INT_MASK_Sel; 
assign IPGT_Wr[0]        = Write[0]  & IPGT_Sel; 
assign IPGR1_Wr[0]       = Write[0]  & IPGR1_Sel; 
assign IPGR2_Wr[0]       = Write[0]  & IPGR2_Sel; 
assign PACKETLEN_Wr[0]   = Write[0]  & PACKETLEN_Sel; 
assign PACKETLEN_Wr[1]   = Write[1]  & PACKETLEN_Sel; 
assign PACKETLEN_Wr[2]   = Write[2]  & PACKETLEN_Sel; 
assign PACKETLEN_Wr[3]   = Write[3]  & PACKETLEN_Sel; 
assign COLLCONF_Wr[0]    = Write[0]  & COLLCONF_Sel; 
assign COLLCONF_Wr[1]    = 1'b0;  // Not used
assign COLLCONF_Wr[2]    = Write[2]  & COLLCONF_Sel; 
     
assign CTRLMODER_Wr[0]   = Write[0]  & CTRLMODER_Sel; 
assign MIIMODER_Wr[0]    = Write[0]  & MIIMODER_Sel; 
assign MIIMODER_Wr[1]    = Write[1]  & MIIMODER_Sel; 
assign MIICOMMAND_Wr[0]  = Write[0]  & MIICOMMAND_Sel; 
assign MIIADDRESS_Wr[0]  = Write[0]  & MIIADDRESS_Sel; 
assign MIIADDRESS_Wr[1]  = Write[1]  & MIIADDRESS_Sel; 
assign MIITX_DATA_Wr[0]  = Write[0]  & MIITX_DATA_Sel; 
assign MIITX_DATA_Wr[1]  = Write[1]  & MIITX_DATA_Sel; 
assign MIIRX_DATA_Wr     = UpdateMIIRX_DATAReg;     
assign MAC_ADDR0_Wr[0]   = Write[0]  & MAC_ADDR0_Sel; 
assign MAC_ADDR0_Wr[1]   = Write[1]  & MAC_ADDR0_Sel; 
assign MAC_ADDR0_Wr[2]   = Write[2]  & MAC_ADDR0_Sel; 
assign MAC_ADDR0_Wr[3]   = Write[3]  & MAC_ADDR0_Sel; 
assign MAC_ADDR1_Wr[0]   = Write[0]  & MAC_ADDR1_Sel; 
assign MAC_ADDR1_Wr[1]   = Write[1]  & MAC_ADDR1_Sel; 
assign HASH0_Wr[0]       = Write[0]  & HASH0_Sel; 
assign HASH0_Wr[1]       = Write[1]  & HASH0_Sel; 
assign HASH0_Wr[2]       = Write[2]  & HASH0_Sel; 
assign HASH0_Wr[3]       = Write[3]  & HASH0_Sel; 
assign HASH1_Wr[0]       = Write[0]  & HASH1_Sel; 
assign HASH1_Wr[1]       = Write[1]  & HASH1_Sel; 
assign HASH1_Wr[2]       = Write[2]  & HASH1_Sel; 
assign HASH1_Wr[3]       = Write[3]  & HASH1_Sel; 
assign TXCTRL_Wr[0]      = Write[0]  & TXCTRL_Sel; 
assign TXCTRL_Wr[1]      = Write[1]  & TXCTRL_Sel; 
assign TXCTRL_Wr[2]      = Write[2]  & TXCTRL_Sel; 
wire DataIn_le80 = (DataIn[`ETH_TX_BD_NUM_WIDTH_0 - 1:0] <='h80);
assign TX_BD_NUM_Wr[0]   = Write[0]  & TX_BD_NUM_Sel & (DataIn_le80); 


wire [31:0] MODEROut;
wire [31:0] INT_SOURCEOut;
wire [31:0] INT_MASKOut;
wire [31:0] IPGTOut;
wire [31:0] IPGR1Out;
wire [31:0] IPGR2Out;
wire [31:0] PACKETLENOut;
wire [31:0] COLLCONFOut;
wire [31:0] CTRLMODEROut;
wire [31:0] MIIMODEROut;
wire [31:0] MIICOMMANDOut;
wire [31:0] MIIADDRESSOut;
wire [31:0] MIITX_DATAOut;
wire [31:0] MIIRX_DATAOut;
wire [31:0] MIISTATUSOut;
wire [31:0] MAC_ADDR0Out;
wire [31:0] MAC_ADDR1Out;
wire [31:0] TX_BD_NUMOut;
wire [31:0] HASH0Out;
wire [31:0] HASH1Out;
wire [31:0] TXCTRLOut;
wire [31:0] DBGOut;
wire [(`ETH_MODER_WIDTH_0-1) :0] datain_moder0 = {DataIn[7],1'b0,DataIn[5],1'b0,DataIn[3:0]};
wire [(`ETH_MODER_WIDTH_1-1) :0] datain_moder1 = {DataIn[15:14],3'b100,DataIn[10],2'b10};
wire [(`ETH_MODER_WIDTH_2-1) :0] datain_moder2 = 1'b0;

eth_register #(`ETH_MODER_WIDTH_0, `ETH_MODER_DEF_0)        MODER_0
  (
   //.DataIn    (DataIn[`ETH_MODER_WIDTH_0 - 1:0]),
   .DataIn    (datain_moder0),
   .DataOut   (MODEROut[`ETH_MODER_WIDTH_0 - 1:0]),
   .Write     (MODER_Wr[0] ),
   .Clk       (Clk),
   .Resetn     (Resetn),
   .SyncReset (1'b0)
  );
eth_register #(`ETH_MODER_WIDTH_1, `ETH_MODER_DEF_1)        MODER_1
  (
   //.DataIn    (DataIn[`ETH_MODER_WIDTH_1 + 7:8]),
   .DataIn    (datain_moder1),
   .DataOut   (MODEROut[`ETH_MODER_WIDTH_1 + 7:8]),
   .Write     (MODER_Wr[1]),
   .Clk       (Clk),
   .Resetn     (Resetn),
   .SyncReset (1'b0)
  );
eth_register #(`ETH_MODER_WIDTH_2, `ETH_MODER_DEF_2)        MODER_2
  (
   //.DataIn    (DataIn[`ETH_MODER_WIDTH_2 + 15:16]),
   .DataIn    (datain_moder2),
   .DataOut   (MODEROut[`ETH_MODER_WIDTH_2 + 15:16]),
   .Write     (MODER_Wr[2] ),
   .Clk       (Clk),
   .Resetn     (Resetn),
   .SyncReset (1'b0)
  );
assign MODEROut[31:`ETH_MODER_WIDTH_2 + 16] = 0;
assign MODEROut[11] = 0;
// INT_MASK Register
eth_register #(`ETH_INT_MASK_WIDTH_0, `ETH_INT_MASK_DEF_0)  INT_MASK_0
  (
   .DataIn    (DataIn[`ETH_INT_MASK_WIDTH_0 - 1:0]),  
   .DataOut   (INT_MASKOut[`ETH_INT_MASK_WIDTH_0 - 1:0]),
   .Write     (INT_MASK_Wr[0]),
   .Clk       (Clk),
   .Resetn     (Resetn),
   .SyncReset (1'b0)
  );
assign INT_MASKOut[31:`ETH_INT_MASK_WIDTH_0] = 0;

// IPGT Register
eth_register #(`ETH_IPGT_WIDTH_0, `ETH_IPGT_DEF_0)          IPGT_0
  (
   .DataIn    (DataIn[`ETH_IPGT_WIDTH_0 - 1:0]),
   .DataOut   (IPGTOut[`ETH_IPGT_WIDTH_0 - 1:0]),
   .Write     (1'b0),		//Note: Reset value is 'h15 design is working only for this value. Making write = 0
   .Clk       (Clk),
   .Resetn     (Resetn),
   .SyncReset (1'b0)
  );
assign IPGTOut[31:`ETH_IPGT_WIDTH_0] = 0;

// IPGR1 Register
eth_register #(`ETH_IPGR1_WIDTH_0, `ETH_IPGR1_DEF_0)        IPGR1_0
  (
   .DataIn    (DataIn[`ETH_IPGR1_WIDTH_0 - 1:0]),
   .DataOut   (IPGR1Out[`ETH_IPGR1_WIDTH_0 - 1:0]),
   .Write     (1'b0),		//Note: No user controllability
   .Clk       (Clk),
   .Resetn     (Resetn),
   .SyncReset (1'b0)
  );
assign IPGR1Out[31:`ETH_IPGR1_WIDTH_0] = 0;

// IPGR2 Register
eth_register #(`ETH_IPGR2_WIDTH_0, `ETH_IPGR2_DEF_0)        IPGR2_0
  (
   .DataIn    (DataIn[`ETH_IPGR2_WIDTH_0 - 1:0]),
   .DataOut   (IPGR2Out[`ETH_IPGR2_WIDTH_0 - 1:0]),
   .Write     (1'b0),		//Note: No user controllability
   .Clk       (Clk),
   .Resetn     (Resetn),
   .SyncReset (1'b0)
  );
assign IPGR2Out[31:`ETH_IPGR2_WIDTH_0] = 0;

// PACKETLEN Register
eth_register #(`ETH_PACKETLEN_WIDTH_0, `ETH_PACKETLEN_DEF_0) PACKETLEN_0
  (
   .DataIn    (DataIn[`ETH_PACKETLEN_WIDTH_0 - 1:0]),
   .DataOut   (PACKETLENOut[`ETH_PACKETLEN_WIDTH_0 - 1:0]),
   .Write     (1'b0),		//Note: No user controllability
   .Clk       (Clk), 
   .Resetn     (Resetn),
   .SyncReset (1'b0)
  );
eth_register #(`ETH_PACKETLEN_WIDTH_1, `ETH_PACKETLEN_DEF_1) PACKETLEN_1
  (
   .DataIn    (DataIn[`ETH_PACKETLEN_WIDTH_1 + 7:8]),
   .DataOut   (PACKETLENOut[`ETH_PACKETLEN_WIDTH_1 + 7:8]),
   .Write     (1'b0),		//Note: No user controllability
   .Clk       (Clk), 
   .Resetn     (Resetn),
   .SyncReset (1'b0)
  );
eth_register #(`ETH_PACKETLEN_WIDTH_2, `ETH_PACKETLEN_DEF_2) PACKETLEN_2
  (
   .DataIn    (DataIn[`ETH_PACKETLEN_WIDTH_2 + 15:16]),
   .DataOut   (PACKETLENOut[`ETH_PACKETLEN_WIDTH_2 + 15:16]),
   .Write     (1'b0),		//Note: No user controllability
   .Clk       (Clk), 
   .Resetn     (Resetn),
   .SyncReset (1'b0)
  );
eth_register #(`ETH_PACKETLEN_WIDTH_3, `ETH_PACKETLEN_DEF_3) PACKETLEN_3
  (
   .DataIn    (DataIn[`ETH_PACKETLEN_WIDTH_3 + 23:24]),
   .DataOut   (PACKETLENOut[`ETH_PACKETLEN_WIDTH_3 + 23:24]),
   .Write     (1'b0),		//Note: No user controllability
   .Clk       (Clk), 
   .Resetn     (Resetn),
   .SyncReset (1'b0)
  );

// COLLCONF Register
eth_register #(`ETH_COLLCONF_WIDTH_0, `ETH_COLLCONF_DEF_0)   COLLCONF_0
  (
   .DataIn    (DataIn[`ETH_COLLCONF_WIDTH_0 - 1:0]),
   .DataOut   (COLLCONFOut[`ETH_COLLCONF_WIDTH_0 - 1:0]),
   .Write     (1'b0),		//Note: No user controllability
   .Clk       (Clk),
   .Resetn     (Resetn),
   .SyncReset (1'b0)
  );
eth_register #(`ETH_COLLCONF_WIDTH_2, `ETH_COLLCONF_DEF_2)   COLLCONF_2
  (
   .DataIn    (DataIn[`ETH_COLLCONF_WIDTH_2 + 15:16]),
   .DataOut   (COLLCONFOut[`ETH_COLLCONF_WIDTH_2 + 15:16]),
   .Write     (1'b0),		//Note: No user controllability
   .Clk       (Clk),
   .Resetn     (Resetn),
   .SyncReset (1'b0)
  );
assign COLLCONFOut[15:`ETH_COLLCONF_WIDTH_0] = 0;
assign COLLCONFOut[31:`ETH_COLLCONF_WIDTH_2 + 16] = 0;

// TX_BD_NUM Register
eth_register #(`ETH_TX_BD_NUM_WIDTH_0, `ETH_TX_BD_NUM_DEF_0) TX_BD_NUM_0
  (
   .DataIn    (DataIn[`ETH_TX_BD_NUM_WIDTH_0 - 1:0]),
   .DataOut   (TX_BD_NUMOut[`ETH_TX_BD_NUM_WIDTH_0 - 1:0]),
   .Write     (TX_BD_NUM_Wr[0]),
   .Clk       (Clk),
   .Resetn     (Resetn),
   .SyncReset (1'b0)
  );
assign TX_BD_NUMOut[31:`ETH_TX_BD_NUM_WIDTH_0] = 0;

// CTRLMODER Register
eth_register #(`ETH_CTRLMODER_WIDTH_0, `ETH_CTRLMODER_DEF_0)  CTRLMODER_0
  (
   .DataIn    (DataIn[`ETH_CTRLMODER_WIDTH_0 - 1:0]),
   .DataOut   (CTRLMODEROut[`ETH_CTRLMODER_WIDTH_0 - 1:0]),
   .Write     (1'b0),		//Note: No user controllability
   .Clk       (Clk),
   .Resetn     (Resetn),
   .SyncReset (1'b0)
  );
assign CTRLMODEROut[31:`ETH_CTRLMODER_WIDTH_0] = 0;

// MIIMODER Register
eth_register #(`ETH_MIIMODER_WIDTH_0, `ETH_MIIMODER_DEF_0)    MIIMODER_0
  (
   .DataIn    (DataIn[`ETH_MIIMODER_WIDTH_0 - 1:0]),
   .DataOut   (MIIMODEROut[`ETH_MIIMODER_WIDTH_0 - 1:0]),
   .Write     (1'b0),		//Note: No user controllability
   .Clk       (Clk),
   .Resetn     (Resetn),
   .SyncReset (1'b0)
  );
eth_register #(`ETH_MIIMODER_WIDTH_1, `ETH_MIIMODER_DEF_1)    MIIMODER_1
  (
   .DataIn    (DataIn[`ETH_MIIMODER_WIDTH_1 + 7:8]),
   .DataOut   (MIIMODEROut[`ETH_MIIMODER_WIDTH_1 + 7:8]),
   .Write     (1'b0),		//Note: No user controllability
   .Clk       (Clk),
   .Resetn     (Resetn),
   .SyncReset (1'b0)
  );
assign MIIMODEROut[31:`ETH_MIIMODER_WIDTH_1 + 8] = 0;

// MIICOMMAND Register
eth_register #(1, 0)                                      MIICOMMAND0
  (
   .DataIn    (DataIn[0]),
   .DataOut   (MIICOMMANDOut[0]),
   .Write     (1'b0),		//Note: No user controllability
   .Clk       (Clk),
   .Resetn     (Resetn),
   .SyncReset (1'b0)
  );
eth_register #(1, 0)                                      MIICOMMAND1
  (
   .DataIn    (DataIn[1]),
   .DataOut   (MIICOMMANDOut[1]),
   .Write     (1'b0),		//Note: No user controllability
   .Clk       (Clk),
   .Resetn     (Resetn),
   .SyncReset (RStatStart)
  );
eth_register #(1, 0)                                      MIICOMMAND2
  (
   .DataIn    (DataIn[2]),
   .DataOut   (MIICOMMANDOut[2]),
   .Write     (1'b0),		//Note: No user controllability
   .Clk       (Clk),
   .Resetn     (Resetn),
   .SyncReset (WCtrlDataStart)
  );
assign MIICOMMANDOut[31:`ETH_MIICOMMAND_WIDTH_0] = 29'h0;

// MIIADDRESSRegister
eth_register #(`ETH_MIIADDRESS_WIDTH_0, `ETH_MIIADDRESS_DEF_0) MIIADDRESS_0
  (
   .DataIn    (DataIn[`ETH_MIIADDRESS_WIDTH_0 - 1:0]),
   .DataOut   (MIIADDRESSOut[`ETH_MIIADDRESS_WIDTH_0 - 1:0]),
   .Write     (MIIADDRESS_Wr[0]),
   .Clk       (Clk),
   .Resetn     (Resetn),
   .SyncReset (1'b0)
  );
eth_register #(`ETH_MIIADDRESS_WIDTH_1, `ETH_MIIADDRESS_DEF_1) MIIADDRESS_1
  (
   .DataIn    (DataIn[`ETH_MIIADDRESS_WIDTH_1 + 7:8]),
   .DataOut   (MIIADDRESSOut[`ETH_MIIADDRESS_WIDTH_1 + 7:8]),
   .Write     (1'b0),		//Note: No user controllability
   .Clk       (Clk),
   .Resetn     (Resetn),
   .SyncReset (1'b0)
  );
assign MIIADDRESSOut[7:`ETH_MIIADDRESS_WIDTH_0] = 0;
assign MIIADDRESSOut[31:`ETH_MIIADDRESS_WIDTH_1 + 8] = 0;

// MIITX_DATA Register
eth_register #(`ETH_MIITX_DATA_WIDTH_0, `ETH_MIITX_DATA_DEF_0) MIITX_DATA_0
  (
   .DataIn    (DataIn[`ETH_MIITX_DATA_WIDTH_0 - 1:0]),
   .DataOut   (MIITX_DATAOut[`ETH_MIITX_DATA_WIDTH_0 - 1:0]), 
   .Write     (1'b0),		//Note: No user controllability
   .Clk       (Clk),
   .Resetn     (Resetn),
   .SyncReset (1'b0)
  );
eth_register #(`ETH_MIITX_DATA_WIDTH_1, `ETH_MIITX_DATA_DEF_1) MIITX_DATA_1
  (
   .DataIn    (DataIn[`ETH_MIITX_DATA_WIDTH_1 + 7:8]),
   .DataOut   (MIITX_DATAOut[`ETH_MIITX_DATA_WIDTH_1 + 7:8]), 
   .Write     (1'b0),		//Note: No user controllability
   .Clk       (Clk),
   .Resetn     (Resetn),
   .SyncReset (1'b0)
  );
assign MIITX_DATAOut[31:`ETH_MIITX_DATA_WIDTH_1 + 8] = 0;

// MIIRX_DATA Register
eth_register #(`ETH_MIIRX_DATA_WIDTH, `ETH_MIIRX_DATA_DEF) MIIRX_DATA
  (
   .DataIn    (Prsd[`ETH_MIIRX_DATA_WIDTH-1:0]),
   .DataOut   (MIIRX_DATAOut[`ETH_MIIRX_DATA_WIDTH-1:0]),
   .Write     (1'b0),		//Note: No user controllability
   .Clk       (Clk),
   .Resetn     (Resetn),
   .SyncReset (1'b0)
  );
assign MIIRX_DATAOut[31:`ETH_MIIRX_DATA_WIDTH] = 0;

// MAC_ADDR0 Register
eth_register #(`ETH_MAC_ADDR0_WIDTH_0, `ETH_MAC_ADDR0_DEF_0)  MAC_ADDR0_0
  (
   .DataIn    (DataIn[`ETH_MAC_ADDR0_WIDTH_0 - 1:0]),
   .DataOut   (MAC_ADDR0Out[`ETH_MAC_ADDR0_WIDTH_0 - 1:0]),
   .Write     (MAC_ADDR0_Wr[0]),
   .Clk       (Clk),
   .Resetn     (Resetn),
   .SyncReset (1'b0)
  );
eth_register #(`ETH_MAC_ADDR0_WIDTH_1, `ETH_MAC_ADDR0_DEF_1)  MAC_ADDR0_1
  (
   .DataIn    (DataIn[`ETH_MAC_ADDR0_WIDTH_1 + 7:8]),
   .DataOut   (MAC_ADDR0Out[`ETH_MAC_ADDR0_WIDTH_1 + 7:8]),
   .Write     (MAC_ADDR0_Wr[1]),
   .Clk       (Clk),
   .Resetn     (Resetn),
   .SyncReset (1'b0)
  );
eth_register #(`ETH_MAC_ADDR0_WIDTH_2, `ETH_MAC_ADDR0_DEF_2)  MAC_ADDR0_2
  (
   .DataIn    (DataIn[`ETH_MAC_ADDR0_WIDTH_2 + 15:16]),
   .DataOut   (MAC_ADDR0Out[`ETH_MAC_ADDR0_WIDTH_2 + 15:16]),
   .Write     (MAC_ADDR0_Wr[2]),
   .Clk       (Clk),
   .Resetn     (Resetn),
   .SyncReset (1'b0)
  );
eth_register #(`ETH_MAC_ADDR0_WIDTH_3, `ETH_MAC_ADDR0_DEF_3)  MAC_ADDR0_3
  (
   .DataIn    (DataIn[`ETH_MAC_ADDR0_WIDTH_3 + 23:24]),
   .DataOut   (MAC_ADDR0Out[`ETH_MAC_ADDR0_WIDTH_3 + 23:24]),
   .Write     (MAC_ADDR0_Wr[3]),
   .Clk       (Clk),
   .Resetn     (Resetn),
   .SyncReset (1'b0)
  );

// MAC_ADDR1 Register
eth_register #(`ETH_MAC_ADDR1_WIDTH_0, `ETH_MAC_ADDR1_DEF_0)  MAC_ADDR1_0
  (
   .DataIn    (DataIn[`ETH_MAC_ADDR1_WIDTH_0 - 1:0]),
   .DataOut   (MAC_ADDR1Out[`ETH_MAC_ADDR1_WIDTH_0 - 1:0]),
   .Write     (MAC_ADDR1_Wr[0]),
   .Clk       (Clk),
   .Resetn     (Resetn),
   .SyncReset (1'b0)
  );
eth_register #(`ETH_MAC_ADDR1_WIDTH_1, `ETH_MAC_ADDR1_DEF_1)  MAC_ADDR1_1
  (
   .DataIn    (DataIn[`ETH_MAC_ADDR1_WIDTH_1 + 7:8]),
   .DataOut   (MAC_ADDR1Out[`ETH_MAC_ADDR1_WIDTH_1 + 7:8]),
   .Write     (MAC_ADDR1_Wr[1]),
   .Clk       (Clk),
   .Resetn     (Resetn),
   .SyncReset (1'b0)
  );
assign MAC_ADDR1Out[31:`ETH_MAC_ADDR1_WIDTH_1 + 8] = 0;

// RXHASH0 Register
eth_register #(`ETH_HASH0_WIDTH_0, `ETH_HASH0_DEF_0)          RXHASH0_0
  (
   .DataIn    (DataIn[`ETH_HASH0_WIDTH_0 - 1:0]),
   .DataOut   (HASH0Out[`ETH_HASH0_WIDTH_0 - 1:0]),
   .Write     (1'b0),		//Note: No user controllability
   .Clk       (Clk),
   .Resetn     (Resetn),
   .SyncReset (1'b0)
  );
eth_register #(`ETH_HASH0_WIDTH_1, `ETH_HASH0_DEF_1)          RXHASH0_1
  (
   .DataIn    (DataIn[`ETH_HASH0_WIDTH_1 + 7:8]),
   .DataOut   (HASH0Out[`ETH_HASH0_WIDTH_1 + 7:8]),
   .Write     (1'b0),		//Note: No user controllability
   .Clk       (Clk),
   .Resetn     (Resetn),
   .SyncReset (1'b0)
  );
eth_register #(`ETH_HASH0_WIDTH_2, `ETH_HASH0_DEF_2)          RXHASH0_2
  (
   .DataIn    (DataIn[`ETH_HASH0_WIDTH_2 + 15:16]),
   .DataOut   (HASH0Out[`ETH_HASH0_WIDTH_2 + 15:16]),
   .Write     (1'b0),		//Note: No user controllability
   .Clk       (Clk),
   .Resetn     (Resetn),
   .SyncReset (1'b0)
  );
eth_register #(`ETH_HASH0_WIDTH_3, `ETH_HASH0_DEF_3)          RXHASH0_3
  (
   .DataIn    (DataIn[`ETH_HASH0_WIDTH_3 + 23:24]),
   .DataOut   (HASH0Out[`ETH_HASH0_WIDTH_3 + 23:24]),
   .Write     (1'b0),		//Note: No user controllability
   .Clk       (Clk),
   .Resetn     (Resetn),
   .SyncReset (1'b0)
  );

// RXHASH1 Register
eth_register #(`ETH_HASH1_WIDTH_0, `ETH_HASH1_DEF_0)          RXHASH1_0
  (
   .DataIn    (DataIn[`ETH_HASH1_WIDTH_0 - 1:0]),
   .DataOut   (HASH1Out[`ETH_HASH1_WIDTH_0 - 1:0]),
   .Write     (1'b0),		//Note: No user controllability
   .Clk       (Clk),
   .Resetn     (Resetn),
   .SyncReset (1'b0)
  );
eth_register #(`ETH_HASH1_WIDTH_1, `ETH_HASH1_DEF_1)          RXHASH1_1
  (
   .DataIn    (DataIn[`ETH_HASH1_WIDTH_1 + 7:8]),
   .DataOut   (HASH1Out[`ETH_HASH1_WIDTH_1 + 7:8]),
   .Write     (1'b0),		//Note: No user controllability
   .Clk       (Clk),
   .Resetn     (Resetn),
   .SyncReset (1'b0)
  );
eth_register #(`ETH_HASH1_WIDTH_2, `ETH_HASH1_DEF_2)          RXHASH1_2
  (
   .DataIn    (DataIn[`ETH_HASH1_WIDTH_2 + 15:16]),
   .DataOut   (HASH1Out[`ETH_HASH1_WIDTH_2 + 15:16]),
   .Write     (1'b0),		//Note: No user controllability
   .Clk       (Clk),
   .Resetn     (Resetn),
   .SyncReset (1'b0)
  );
eth_register #(`ETH_HASH1_WIDTH_3, `ETH_HASH1_DEF_3)          RXHASH1_3
  (
   .DataIn    (DataIn[`ETH_HASH1_WIDTH_3 + 23:24]),
   .DataOut   (HASH1Out[`ETH_HASH1_WIDTH_3 + 23:24]),
   .Write     (1'b0),		//Note: No user controllability
   .Clk       (Clk),
   .Resetn     (Resetn),
   .SyncReset (1'b0)
  );

// TXCTRL Register
eth_register #(`ETH_TX_CTRL_WIDTH_0, `ETH_TX_CTRL_DEF_0)  TXCTRL_0
  (
   .DataIn    (DataIn[`ETH_TX_CTRL_WIDTH_0 - 1:0]),
   .DataOut   (TXCTRLOut[`ETH_TX_CTRL_WIDTH_0 - 1:0]),
   .Write     (1'b0),		//Note: No user controllability
   .Clk       (Clk),
   .Resetn     (Resetn),
   .SyncReset (1'b0)
  );
eth_register #(`ETH_TX_CTRL_WIDTH_1, `ETH_TX_CTRL_DEF_1)  TXCTRL_1
  (
   .DataIn    (DataIn[`ETH_TX_CTRL_WIDTH_1 + 7:8]),
   .DataOut   (TXCTRLOut[`ETH_TX_CTRL_WIDTH_1 + 7:8]),
   .Write     (1'b0),		//Note: No user controllability
   .Clk       (Clk),
   .Resetn     (Resetn),
   .SyncReset (1'b0)
  );
eth_register #(`ETH_TX_CTRL_WIDTH_2, `ETH_TX_CTRL_DEF_2)  TXCTRL_2 // Request bit is synchronously reset
  (
   .DataIn    (DataIn[`ETH_TX_CTRL_WIDTH_2 + 15:16]),
   .DataOut   (TXCTRLOut[`ETH_TX_CTRL_WIDTH_2 + 15:16]),
   .Write     (1'b0),		//Note: No user controllability
   .Clk       (Clk),
   .Resetn     (Resetn),
   .SyncReset (RstTxPauseRq)
  );
assign TXCTRLOut[31:`ETH_TX_CTRL_WIDTH_2 + 16] = 0;



// Reading data from registers
always @ (Address       or Read           or MODEROut       or INT_SOURCEOut  or
          INT_MASKOut   or IPGTOut        or IPGR1Out       or IPGR2Out       or
          PACKETLENOut  or COLLCONFOut    or CTRLMODEROut   or MIIMODEROut    or
          MIICOMMANDOut or MIIADDRESSOut  or MIITX_DATAOut  or MIIRX_DATAOut  or 
          MIISTATUSOut  or MAC_ADDR0Out   or MAC_ADDR1Out   or TX_BD_NUMOut   or
          HASH0Out      or HASH1Out       or TXCTRLOut       
         )
begin
  if(Read)  // read
    begin
      case(Address)
        `ETH_MODER_ADR        :  DataOut=MODEROut;
        `ETH_INT_SOURCE_ADR   :  DataOut=INT_SOURCEOut;
        `ETH_INT_MASK_ADR     :  DataOut=INT_MASKOut;
        `ETH_IPGT_ADR         :  DataOut=IPGTOut;
        `ETH_IPGR1_ADR        :  DataOut=IPGR1Out;
        `ETH_IPGR2_ADR        :  DataOut=IPGR2Out;
        `ETH_PACKETLEN_ADR    :  DataOut=PACKETLENOut;
        `ETH_COLLCONF_ADR     :  DataOut=COLLCONFOut;
        `ETH_CTRLMODER_ADR    :  DataOut=CTRLMODEROut;
        `ETH_MIIMODER_ADR     :  DataOut=MIIMODEROut;
        `ETH_MIICOMMAND_ADR   :  DataOut=MIICOMMANDOut;
        `ETH_MIIADDRESS_ADR   :  DataOut=MIIADDRESSOut;
        `ETH_MIITX_DATA_ADR   :  DataOut=MIITX_DATAOut;
        `ETH_MIIRX_DATA_ADR   :  DataOut=MIIRX_DATAOut;
        `ETH_MIISTATUS_ADR    :  DataOut=MIISTATUSOut;
        `ETH_MAC_ADDR0_ADR    :  DataOut=MAC_ADDR0Out;
        `ETH_MAC_ADDR1_ADR    :  DataOut=MAC_ADDR1Out;
        `ETH_TX_BD_NUM_ADR    :  DataOut=TX_BD_NUMOut;
        `ETH_HASH0_ADR        :  DataOut=HASH0Out;
        `ETH_HASH1_ADR        :  DataOut=HASH1Out;
        `ETH_TX_CTRL_ADR      :  DataOut=TXCTRLOut;
        `ETH_DBG_ADR          :  DataOut=dbg_dat;
        default:             DataOut=32'h0;
      endcase
    end
  else
    DataOut=32'h0;
end


assign r_RecSmall         = MODEROut[16];		
assign r_Pad              = MODEROut[15];
assign r_HugEn            = MODEROut[14];
assign r_CrcEn            = MODEROut[13];		
assign r_DlyCrcEn         = MODEROut[12];		
assign r_FullD            = MODEROut[10];
assign r_ExDfrEn          = MODEROut[9];		
assign r_NoBckof          = MODEROut[8];		
assign r_LoopBck          = MODEROut[7];
assign r_IFG              = MODEROut[6];		
assign r_Pro              = MODEROut[5];
assign r_Iam              = MODEROut[4];	
assign r_Bro              = MODEROut[3];
assign r_NoPre            = MODEROut[2];
assign r_TxEn             = MODEROut[1] & (TX_BD_NUMOut>0);     // Transmission is enabled when there is at least one TxBD.
assign r_RxEn             = MODEROut[0] & (TX_BD_NUMOut<'h80);  // Reception is enabled when there is  at least one RxBD.

assign r_IPGT[6:0]        = IPGTOut[6:0];

assign r_IPGR1[6:0]       = IPGR1Out[6:0];

assign r_IPGR2[6:0]       = IPGR2Out[6:0];

assign r_MinFL[15:0]      = PACKETLENOut[31:16];
assign r_MaxFL[15:0]      = PACKETLENOut[15:0];

assign r_MaxRet[3:0]      = COLLCONFOut[19:16];
assign r_CollValid[5:0]   = COLLCONFOut[5:0];

assign r_TxFlow           = CTRLMODEROut[2];
assign r_RxFlow           = CTRLMODEROut[1];
assign r_PassAll          = CTRLMODEROut[0];

assign r_MiiNoPre         = MIIMODEROut[8];
assign r_ClkDiv[7:0]      = MIIMODEROut[7:0];

assign r_WCtrlData        = MIICOMMANDOut[2];
assign r_RStat            = MIICOMMANDOut[1];
assign r_ScanStat         = MIICOMMANDOut[0];

assign r_RGAD[4:0]        = MIIADDRESSOut[12:8];
assign r_FIAD[4:0]        = MIIADDRESSOut[4:0];

assign r_CtrlData[15:0]   = MIITX_DATAOut[15:0];

assign MIISTATUSOut[31:`ETH_MIISTATUS_WIDTH] = 0; 
assign MIISTATUSOut[2]    = NValid_stat         ; 
assign MIISTATUSOut[1]    = Busy_stat           ; 
assign MIISTATUSOut[0]    = LinkFail            ; 

assign r_MAC[31:0]        = MAC_ADDR0Out[31:0];
assign r_MAC[47:32]       = MAC_ADDR1Out[15:0];
assign r_HASH1[31:0]      = HASH1Out;
assign r_HASH0[31:0]      = HASH0Out;

assign r_TxBDNum[7:0]     = TX_BD_NUMOut[7:0];

assign r_TxPauseTV[15:0]  = TXCTRLOut[15:0];
assign r_TxPauseRq        = TXCTRLOut[16];


// Synchronizing TxC Interrupt
always @ (posedge TxClk or negedge Resetn)
begin
  if(Resetn == 0)
    SetTxCIrq_txclk <= 1'b0;
  else
  if(TxCtrlEndFrm & StartTxDone & r_TxFlow)
    SetTxCIrq_txclk <= 1'b1;
  else
  if(ResetTxCIrq_sync2)
    SetTxCIrq_txclk <= 1'b0;
end


always @ (posedge Clk or negedge Resetn)
begin
  if(Resetn == 0)
    SetTxCIrq_sync1 <= 1'b0;
  else
    SetTxCIrq_sync1 <= SetTxCIrq_txclk;
end

always @ (posedge Clk or negedge Resetn)
begin
  if(Resetn == 0)
    SetTxCIrq_sync2 <= 1'b0;
  else
    SetTxCIrq_sync2 <= SetTxCIrq_sync1;
end

always @ (posedge Clk or negedge Resetn)
begin
  if(Resetn == 0)
    SetTxCIrq_sync3 <= 1'b0;
  else
    SetTxCIrq_sync3 <= SetTxCIrq_sync2;
end

always @ (posedge Clk or negedge Resetn)
begin
  if(Resetn == 0)
    SetTxCIrq <= 1'b0;
  else
    SetTxCIrq <= SetTxCIrq_sync2 & ~SetTxCIrq_sync3;
end

always @ (posedge TxClk or negedge Resetn)
begin
  if(Resetn == 0)
    ResetTxCIrq_sync1 <= 1'b0;
  else
    ResetTxCIrq_sync1 <= SetTxCIrq_sync2;
end

always @ (posedge TxClk or negedge Resetn)
begin
  if(Resetn == 0)
    ResetTxCIrq_sync2 <= 1'b0;
  else
    ResetTxCIrq_sync2 <= SetTxCIrq_sync1;
end


// Synchronizing RxC Interrupt
always @ (posedge RxClk or negedge Resetn)
begin
  if(Resetn == 0)
    SetRxCIrq_rxclk <= 1'b0;
  else
  if(SetPauseTimer & r_RxFlow)
    SetRxCIrq_rxclk <= 1'b1;
  else
  if(ResetRxCIrq_sync2 & (~ResetRxCIrq_sync3))
    SetRxCIrq_rxclk <= 1'b0;
end


always @ (posedge Clk or negedge Resetn)
begin
  if(Resetn == 0)
    SetRxCIrq_sync1 <= 1'b0;
  else
    SetRxCIrq_sync1 <= SetRxCIrq_rxclk;
end

always @ (posedge Clk or negedge Resetn)
begin
  if(Resetn == 0)
    SetRxCIrq_sync2 <= 1'b0;
  else
    SetRxCIrq_sync2 <= SetRxCIrq_sync1;
end

always @ (posedge Clk or negedge Resetn)
begin
  if(Resetn == 0)
    SetRxCIrq_sync3 <= 1'b0;
  else
    SetRxCIrq_sync3 <= SetRxCIrq_sync2;
end

always @ (posedge Clk or negedge Resetn)
begin
  if(Resetn == 0)
    SetRxCIrq <= 1'b0;
  else
    SetRxCIrq <= SetRxCIrq_sync2 & ~SetRxCIrq_sync3;
end

always @ (posedge RxClk or negedge Resetn)
begin
  if(Resetn == 0)
    ResetRxCIrq_sync1 <= 1'b0;
  else
    ResetRxCIrq_sync1 <= SetRxCIrq_sync2;
end

always @ (posedge RxClk or negedge Resetn)
begin
  if(Resetn == 0)
    ResetRxCIrq_sync2 <= 1'b0;
  else
    ResetRxCIrq_sync2 <= ResetRxCIrq_sync1;
end

always @ (posedge RxClk or negedge Resetn)
begin
  if(Resetn == 0)
    ResetRxCIrq_sync3 <= 1'b0;
  else
    ResetRxCIrq_sync3 <= ResetRxCIrq_sync2;
end



// Interrupt generation
always @ (posedge Clk or negedge Resetn)
begin
  if(Resetn == 0)
    irq_txb <= 1'b0;
  else
  if(TxB_IRQ)
    irq_txb <=  1'b1;
  else
  if(INT_SOURCE_Wr[0] & DataIn[0])
    irq_txb <=  1'b0;
end

always @ (posedge Clk or negedge Resetn)
begin
  if(Resetn == 0)
    irq_txe <= 1'b0;
  else
  if(TxE_IRQ)
    irq_txe <=  1'b1;
  else
  if(INT_SOURCE_Wr[0] & DataIn[1]) 
    irq_txe <=  1'b0;
end

always @ (posedge Clk or negedge Resetn)
begin
  if(Resetn == 0)
    irq_rxb <= 1'b0;
  else
  if(RxB_IRQ)
    irq_rxb <=  1'b1;
  else
  if(INT_SOURCE_Wr[0] & DataIn[2])
    irq_rxb <=  1'b0;
end

always @ (posedge Clk or negedge Resetn)
begin
  if(Resetn == 0)
    irq_rxe <= 1'b0;
  else if(RxE_IRQ)
    irq_rxe <=  1'b1;
  else
  if(INT_SOURCE_Wr[0] & DataIn[3])
  begin
    irq_rxe <=  1'b0;
  end
  
end

always @ (posedge Clk or negedge Resetn)
begin
  if(Resetn == 0)
    irq_busy <= 1'b0;
  else
  if(Busy_IRQ)
    irq_busy <=  1'b1;
  else
  if(INT_SOURCE_Wr[0] & DataIn[4])
    irq_busy <=  1'b0;
end

always @ (posedge Clk or negedge Resetn)
begin
  if(Resetn == 0)
    irq_txc <= 1'b0;
  else
  if(SetTxCIrq)
    irq_txc <=  1'b1;
  else
  if(INT_SOURCE_Wr[0] & DataIn[5])
    irq_txc <=  1'b0;
end

always @ (posedge Clk or negedge Resetn)
begin
  if(Resetn == 0)
    irq_rxc <= 1'b0;
  else
  if(SetRxCIrq)
    irq_rxc <=  1'b1;
  else
  if(INT_SOURCE_Wr[0] & DataIn[6])
    irq_rxc <=  1'b0;
end

// Generating interrupt signal
assign int_o = irq_txb  & INT_MASKOut[0] | 
               irq_txe  & INT_MASKOut[1] | 
               irq_rxb  & INT_MASKOut[2] | 
               irq_rxe  & INT_MASKOut[3] | 
               irq_busy & INT_MASKOut[4] | 
               irq_txc  & INT_MASKOut[5] | 
               irq_rxc  & INT_MASKOut[6] ;

// For reading interrupt status
assign INT_SOURCEOut = {{(32-`ETH_INT_SOURCE_WIDTH_0){1'b0}}, irq_rxc, irq_txc, irq_busy, irq_rxe, irq_rxb, irq_txe, irq_txb};




endmodule


//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date:    17:28:04 06/07/2020 
// Design Name: 
// Module Name:    eth_register 
// Project Name: 
// Target Devices: 
// Tool versions: 
// Description: 
//
// Dependencies: 
//
// Revision: 
// Revision 0.01 - File Created
// Additional Comments: 
//
//////////////////////////////////////////////////////////////////////////////////

`include "timescale.v"
module eth_register(DataIn, DataOut, Write, Clk, Resetn, SyncReset);

parameter WIDTH = 8; // default parameter of the register width
parameter RESET_VALUE = 0;

input [WIDTH-1:0] DataIn;

input Write;
input Clk;
input Resetn;
input SyncReset;

output [WIDTH-1:0] DataOut;
reg    [WIDTH-1:0] DataOut;



always @ (posedge Clk or negedge Resetn)
begin
  if(Resetn == 0)
    DataOut<= RESET_VALUE;
  else
  if(SyncReset)
    DataOut<= RESET_VALUE;
  else
  if(Write)                         // write
    DataOut<= DataIn;
end



endmodule   // Register


//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date:    17:39:07 06/07/2020 
// Design Name: 
// Module Name:    eth_rxaddrcheck 
// Project Name: 
// Target Devices: 
// Tool versions: 
// Description: 
//
// Dependencies: 
//
// Revision: 
// Revision 0.01 - File Created
// Additional Comments: 
//
//////////////////////////////////////////////////////////////////////////////////

`include "timescale.v"
module eth_rxaddrcheck(MRxClk,  Resetn, MRxD,LatchedByte ,r_Bro ,r_Pro,r_Iam,Rx_NibCnt,
                       ByteCntEq0,ByteCntEq1,ByteCntEq2, ByteCntEq3, ByteCntEq4, 
					   ByteCntEq5,ByteCntEq6, ByteCntEq7, HASH0, HASH1, 
                       CrcHash,    CrcHashGood, StateDA,StateSFD,StateIdle,StateDrop ,RxEndFrm,
                       MAC, Address_mismatch, AddressMiss, PassAll,RxAddressInvalid,
                       ControlFrmAddressOK
                      );


  input        MRxClk; 
  input        Resetn; 
  input [7:0]  LatchedByte;
  input [3:0]  MRxD; 
  input 	   Rx_NibCnt;
  input        r_Bro; 
  input        r_Pro; 
  input 	   r_Iam;
  input        ByteCntEq0;
  input        ByteCntEq1;
  input        ByteCntEq2;
  input        ByteCntEq3;
  input        ByteCntEq4;
  input        ByteCntEq5;
  input        ByteCntEq6;
  input        ByteCntEq7;
  input [31:0] HASH0; 
  input [31:0] HASH1; 
  input [5:0]  CrcHash; 
  input        CrcHashGood;  
  input [47:0] MAC;
  input 	   StateDA;
  input 	   StateSFD;
  input        StateIdle;
  input		   StateDrop;
  input        RxEndFrm;
  input        PassAll;
  input        ControlFrmAddressOK;
  
  output  reg  Address_mismatch;
  output       AddressMiss;
  output  reg  RxAddressInvalid;

 reg BroadcastOK;
 wire ByteCntEq2;
 wire ByteCntEq3;
 wire ByteCntEq4; 
 wire ByteCntEq5;
 reg RxAddressInvalid_next;
 wire HashBit;
 wire [31:0] IntHash;
 reg [7:0]  ByteHash;
 reg MulticastOK;
 reg UnicastOK;
 reg AddressMiss;
 reg Multicast;

function Iamcheck_for_RxAddrInvalid(input reg dummy);
	case(r_Iam)
	1:$display("pending to implement");   
	0:begin
	        case(UnicastOK)
			1:begin
				   case(({LatchedByte[3:0],LatchedByte[7:4]}) == MAC[7:0])
					1:Iamcheck_for_RxAddrInvalid = 'b0;
					0:Iamcheck_for_RxAddrInvalid = 'b1;
					endcase		
			  end
			0:Iamcheck_for_RxAddrInvalid = 'b1;
			endcase
	 end 
	endcase
endfunction


//Note: Adding flop here to avaoid the unwanted(glitches) results , which we are facing with combo
always@(posedge MRxClk or negedge Resetn)
begin
  if(Resetn == 0) RxAddressInvalid <= 0;
  else
       RxAddressInvalid <= RxAddressInvalid_next;
end
always@(*)
begin
		if(StateDA && ByteCntEq5 && Rx_NibCnt)
		begin
			case(r_Pro)
			1: RxAddressInvalid_next = 'b0;
			0: begin
					case(r_Bro)
					1:	begin
							case(({LatchedByte[3:0],LatchedByte[7:4]}) == 'hff && BroadcastOK)
							1:begin
								RxAddressInvalid_next = 'b1;
							  end
							0:begin
								RxAddressInvalid_next = Iamcheck_for_RxAddrInvalid(0);
							  end
							endcase
						end
					0:begin
							case(({LatchedByte[3:0],LatchedByte[7:4]}) == 'hff && BroadcastOK)
							1:begin
								RxAddressInvalid_next = 'b0;
							  end
							0:begin
								RxAddressInvalid_next = Iamcheck_for_RxAddrInvalid(0);
							  end
							endcase
					  end
					endcase
			   end
			endcase
		end
		else 
		begin
		     if(RxEndFrm) RxAddressInvalid_next = 0;
			 else         RxAddressInvalid_next = RxAddressInvalid;        
		end
end	


//Note: 1.RxAddressInvalid generation happens, when StateDA & ByteCntEq5
//      2.So Address_mismatch genaration ,no need to dependent on ByteCntEq5 & StateDA  
//      3.Genarting Address_mismatch as a pulse(one clk pulse wide)
always @ (posedge MRxClk or negedge Resetn)
begin
  if(Resetn == 0)
    Address_mismatch <=  1'b0;
  else if(RxAddressInvalid_next & ByteCntEq5 & StateDA)
    Address_mismatch <=  1'b1;
  else
    Address_mismatch <=  1'b0;
end
 

// This ff holds the "Address Miss" information that is written to the RX BD status.
always @ (posedge MRxClk or negedge Resetn)
begin
  if(Resetn == 0)
    AddressMiss <=  1'b0;
  else if(StateIdle & ByteCntEq0)
    AddressMiss <=  1'b0;
  else if(ByteCntEq5 & StateDA)
		AddressMiss <= RxAddressInvalid_next; 
end


// Hash Address Check, Multicast
always @ (posedge MRxClk or negedge Resetn)
begin
  if(Resetn == 0)
    MulticastOK <=  1'b0;
  else if(RxEndFrm)
    MulticastOK <=  1'b0;
  else if(CrcHashGood & Multicast)
    MulticastOK <=  HashBit;
end


 always @ (posedge MRxClk or negedge Resetn)    
begin
  if(Resetn == 0)
    Multicast <=  1'b0;
  else
    begin      
      if((StateDA & Rx_NibCnt == 'd0) & MRxD[0])		
	  begin
			case(1)
			ByteCntEq0: Multicast <=  1'b1;
			endcase
	  end
	  else
      begin 	  
		  if(RxEndFrm)
		  Multicast <=  1'b0;
	  end
    end
end 


always @ (posedge MRxClk or negedge Resetn)
begin
  if(Resetn == 0)
    UnicastOK <=  1'b0;
  else 
  begin
		if(StateDA)
		begin
			case(1)   //Note: 1.In below comparison , need to check Lsb bits first and then check for Msb.
				      //      2.Which is neccessary in order to sync with RXData generation.
					  //      3.RxData will be sent to the RXFIFO.
			ByteCntEq0:begin //47:40
							if(Rx_NibCnt) begin
								UnicastOK  <=  (({LatchedByte[3:0],LatchedByte[7:4]}) == MAC[47:40]); 
							end
					   end 
					   
			ByteCntEq1:begin  // 39:32	
							if(Rx_NibCnt) begin
								UnicastOK  <=  ( ({LatchedByte[3:0],LatchedByte[7:4]}) == MAC[39:32]) && UnicastOK;								
								end
					   end
			ByteCntEq2:begin  // 31:24
							if(Rx_NibCnt) begin
								UnicastOK  <=  ( ({LatchedByte[3:0],LatchedByte[7:4]}) == MAC[31:24]) && UnicastOK;
						end
					   end
			ByteCntEq3:begin  // 23:16
							if(Rx_NibCnt) begin
								UnicastOK  <=  ( ({LatchedByte[3:0],LatchedByte[7:4]}) == MAC[23:16]) && UnicastOK;
							end
					   end
			ByteCntEq4:begin  // 15:8
							if(Rx_NibCnt) begin
								UnicastOK  <=  ( ({LatchedByte[3:0],LatchedByte[7:4]}) == MAC[15:8]) && UnicastOK;
							end
					   end
			ByteCntEq5:begin  // 7:0
							if(Rx_NibCnt) begin
								 UnicastOK  <=  ( ({LatchedByte[3:0],LatchedByte[7:4]}) == MAC[7:0]) && UnicastOK;
							end
					   end
			endcase
		end
		else 
		begin
			if(RxEndFrm)
				UnicastOK  <=  1'b0;
		end
	end
end

always@(posedge MRxClk or negedge Resetn)
begin
	if(Resetn == 0)
		BroadcastOK <= 1'b0;
	else
	begin
			if(StateDA)
			begin
				case(1)
				ByteCntEq0 :begin	
								if(Rx_NibCnt)
									BroadcastOK <= LatchedByte[7:0] == 'hff;
							end
				ByteCntEq1,
				ByteCntEq2,
				ByteCntEq3,
				ByteCntEq4,
				ByteCntEq5 :begin	
								if(Rx_NibCnt)
									BroadcastOK <= LatchedByte[7:0] == 'hff && BroadcastOK;
							end
				endcase
			end
			else
			begin
				  if(RxEndFrm)  
					BroadcastOK <= 1'b0;
			end
	end
		
end 
 
assign IntHash = (CrcHash[5])? HASH1 : HASH0;
  
always@(CrcHash or IntHash)
begin
  case(CrcHash[4:3])
    2'b00: ByteHash = IntHash[7:0];
    2'b01: ByteHash = IntHash[15:8];
    2'b10: ByteHash = IntHash[23:16];
    2'b11: ByteHash = IntHash[31:24];
  endcase
end
      
assign HashBit = ByteHash[CrcHash[2:0]];


endmodule


//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date:    17:39:07 06/07/2020 
// Design Name: 
// Module Name:    eth_rxaddrcheck 
// Project Name: 
// Target Devices: 
// Tool versions: 
// Description: 
//
// Dependencies: 
//
// Revision: 
// Revision 0.01 - File Created
// Additional Comments: 
//
//////////////////////////////////////////////////////////////////////////////////

`include "timescale.v"
module eth_rxaddrcheck(MRxClk,  Resetn, MRxD,LatchedByte ,r_Bro ,r_Pro,r_Iam,Rx_NibCnt,
                       ByteCntEq0,ByteCntEq1,ByteCntEq2, ByteCntEq3, ByteCntEq4, 
					   ByteCntEq5,ByteCntEq6, ByteCntEq7, HASH0, HASH1, 
                       CrcHash,    CrcHashGood, StateDA,StateSFD,StateIdle,StateDrop ,RxEndFrm,
                       MAC, Address_mismatch, AddressMiss, PassAll,RxAddressInvalid,
                       ControlFrmAddressOK
                      );


  input        MRxClk; 
  input        Resetn; 
  input [7:0]  LatchedByte;
  input [3:0]  MRxD; 
  input 	   Rx_NibCnt;
  input        r_Bro; 
  input        r_Pro; 
  input 	   r_Iam;
  input        ByteCntEq0;
  input        ByteCntEq1;
  input        ByteCntEq2;
  input        ByteCntEq3;
  input        ByteCntEq4;
  input        ByteCntEq5;
  input        ByteCntEq6;
  input        ByteCntEq7;
  input [31:0] HASH0; 
  input [31:0] HASH1; 
  input [5:0]  CrcHash; 
  input        CrcHashGood;  
  input [47:0] MAC;
  input 	   StateDA;
  input 	   StateSFD;
  input        StateIdle;
  input		   StateDrop;
  input        RxEndFrm;
  input        PassAll;
  input        ControlFrmAddressOK;
  
  output  reg  Address_mismatch;
  output       AddressMiss;
  output  reg  RxAddressInvalid;

 reg BroadcastOK;
 wire ByteCntEq2;
 wire ByteCntEq3;
 wire ByteCntEq4; 
 wire ByteCntEq5;
 reg RxAddressInvalid_next;
 wire HashBit;
 wire [31:0] IntHash;
 reg [7:0]  ByteHash;
 reg MulticastOK;
 reg UnicastOK;
 reg AddressMiss;
 reg Multicast;

function Iamcheck_for_RxAddrInvalid(input reg dummy);
	case(r_Iam)
	1:$display("pending to implement");   
	0:begin
	        case(UnicastOK)
			1:begin
				   case(({LatchedByte[3:0],LatchedByte[7:4]}) == MAC[7:0])
					1:Iamcheck_for_RxAddrInvalid = 'b0;
					0:Iamcheck_for_RxAddrInvalid = 'b1;
					endcase		
			  end
			0:Iamcheck_for_RxAddrInvalid = 'b1;
			endcase
	 end 
	endcase
endfunction


//Note: Adding flop here to avaoid the unwanted(glitches) results , which we are facing with combo
always@(posedge MRxClk or negedge Resetn)
begin
  if(Resetn == 0) RxAddressInvalid <= 0;
  else
       RxAddressInvalid <= RxAddressInvalid_next;
end
always@(*)
begin
		if(StateDA && ByteCntEq5 && Rx_NibCnt)
		begin
			case(r_Pro)
			1: RxAddressInvalid_next = 'b0;
			0: begin
					case(r_Bro)
					1:	begin
							case(({LatchedByte[3:0],LatchedByte[7:4]}) == 'hff && BroadcastOK)
							1:begin
								RxAddressInvalid_next = 'b1;
							  end
							0:begin
								RxAddressInvalid_next = Iamcheck_for_RxAddrInvalid(0);
							  end
							endcase
						end
					0:begin
							case(({LatchedByte[3:0],LatchedByte[7:4]}) == 'hff && BroadcastOK)
							1:begin
								RxAddressInvalid_next = 'b0;
							  end
							0:begin
								RxAddressInvalid_next = Iamcheck_for_RxAddrInvalid(0);
							  end
							endcase
					  end
					endcase
			   end
			endcase
		end
		else 
		begin
		     if(RxEndFrm) RxAddressInvalid_next = 0;
			 else         RxAddressInvalid_next = RxAddressInvalid;        
		end
end	


//Note: 1.RxAddressInvalid generation happens, when StateDA & ByteCntEq5
//      2.So Address_mismatch genaration ,no need to dependent on ByteCntEq5 & StateDA  
//      3.Genarting Address_mismatch as a pulse(one clk pulse wide)
always @ (posedge MRxClk or negedge Resetn)
begin
  if(Resetn == 0)
    Address_mismatch <=  1'b0;
  else if(RxAddressInvalid_next & ByteCntEq5 & StateDA)
    Address_mismatch <=  1'b1;
  else
    Address_mismatch <=  1'b0;
end
 

// This ff holds the "Address Miss" information that is written to the RX BD status.
always @ (posedge MRxClk or negedge Resetn)
begin
  if(Resetn == 0)
    AddressMiss <=  1'b0;
  else if(StateIdle & ByteCntEq0)
    AddressMiss <=  1'b0;
  else if(ByteCntEq5 & StateDA)
		AddressMiss <= RxAddressInvalid_next; 
end


// Hash Address Check, Multicast
always @ (posedge MRxClk or negedge Resetn)
begin
  if(Resetn == 0)
    MulticastOK <=  1'b0;
  else if(RxEndFrm)
    MulticastOK <=  1'b0;
  else if(CrcHashGood & Multicast)
    MulticastOK <=  HashBit;
end


 always @ (posedge MRxClk or negedge Resetn)    
begin
  if(Resetn == 0)
    Multicast <=  1'b0;
  else
    begin      
      if((StateDA & Rx_NibCnt == 'd0) & MRxD[0])		
	  begin
			case(1)
			ByteCntEq0: Multicast <=  1'b1;
			endcase
	  end
	  else
      begin 	  
		  if(RxEndFrm)
		  Multicast <=  1'b0;
	  end
    end
end 


always @ (posedge MRxClk or negedge Resetn)
begin
  if(Resetn == 0)
    UnicastOK <=  1'b0;
  else 
  begin
		if(StateDA)
		begin
			case(1)   //Note: 1.In below comparison , need to check Lsb bits first and then check for Msb.
				      //      2.Which is neccessary in order to sync with RXData generation.
					  //      3.RxData will be sent to the RXFIFO.
			ByteCntEq0:begin //47:40
							if(Rx_NibCnt) begin
								UnicastOK  <=  (({LatchedByte[3:0],LatchedByte[7:4]}) == MAC[47:40]); 
							end
					   end 
					   
			ByteCntEq1:begin  // 39:32	
							if(Rx_NibCnt) begin
								UnicastOK  <=  ( ({LatchedByte[3:0],LatchedByte[7:4]}) == MAC[39:32]) && UnicastOK;								
								end
					   end
			ByteCntEq2:begin  // 31:24
							if(Rx_NibCnt) begin
								UnicastOK  <=  ( ({LatchedByte[3:0],LatchedByte[7:4]}) == MAC[31:24]) && UnicastOK;
						end
					   end
			ByteCntEq3:begin  // 23:16
							if(Rx_NibCnt) begin
								UnicastOK  <=  ( ({LatchedByte[3:0],LatchedByte[7:4]}) == MAC[23:16]) && UnicastOK;
							end
					   end
			ByteCntEq4:begin  // 15:8
							if(Rx_NibCnt) begin
								UnicastOK  <=  ( ({LatchedByte[3:0],LatchedByte[7:4]}) == MAC[15:8]) && UnicastOK;
							end
					   end
			ByteCntEq5:begin  // 7:0
							if(Rx_NibCnt) begin
								 UnicastOK  <=  ( ({LatchedByte[3:0],LatchedByte[7:4]}) == MAC[7:0]) && UnicastOK;
							end
					   end
			endcase
		end
		else 
		begin
			if(RxEndFrm)
				UnicastOK  <=  1'b0;
		end
	end
end

always@(posedge MRxClk or negedge Resetn)
begin
	if(Resetn == 0)
		BroadcastOK <= 1'b0;
	else
	begin
			if(StateDA)
			begin
				case(1)
				ByteCntEq0 :begin	
								if(Rx_NibCnt)
									BroadcastOK <= LatchedByte[7:0] == 'hff;
							end
				ByteCntEq1,
				ByteCntEq2,
				ByteCntEq3,
				ByteCntEq4,
				ByteCntEq5 :begin	
								if(Rx_NibCnt)
									BroadcastOK <= LatchedByte[7:0] == 'hff && BroadcastOK;
							end
				endcase
			end
			else
			begin
				  if(RxEndFrm)  
					BroadcastOK <= 1'b0;
			end
	end
		
end 
 
assign IntHash = (CrcHash[5])? HASH1 : HASH0;
  
always@(CrcHash or IntHash)
begin
  case(CrcHash[4:3])
    2'b00: ByteHash = IntHash[7:0];
    2'b01: ByteHash = IntHash[15:8];
    2'b10: ByteHash = IntHash[23:16];
    2'b11: ByteHash = IntHash[31:24];
  endcase
end
      
assign HashBit = ByteHash[CrcHash[2:0]];


endmodule


//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date:    17:39:27 06/07/2020 
// Design Name: 
// Module Name:    eth_rxcounters 
// Project Name: 
// Target Devices: 
// Tool versions: 
// Description: 
//
// Dependencies: 
//
// Revision: 
// Revision 0.01 - File Created
// Additional Comments: 
//
//////////////////////////////////////////////////////////////////////////////////
`include "timescale.v"
module eth_rxcounters 
  (
   MRxClk, Resetn, MRxDV, StateIdle, StateSFD, StateData, StateDrop, StateSA, StateDA,StateLength, StatePreamble, 
   MRxDEq5, MRxDEqD, DlyCrcEn, DlyCrcCnt, Transmitting, MaxFL, r_IFG, HugEn, IFGCounterEq24, 
   ByteCntEq0, ByteCntEq1, ByteCntEq2,ByteCntEq3,ByteCntEq4,ByteCntEq5, ByteCntEq6,
   ByteCntEq7, ByteCntGreat2, ByteCntSmall7, ByteCntMaxFrame, ByteCntOut, Rx_NibCnt,frame_ByteCnt
   );

input         MRxClk;
input         Resetn;
input         MRxDV;
input         StateSFD;
input [1:0]   StateData;
input 		  MRxDEq5;
input         MRxDEqD;
input         StateIdle;
input         StateDrop;
input         DlyCrcEn;
input         StatePreamble;
input 		  StateDA;
input 		  StateSA;
input 		  StateLength;
input         Transmitting;
input         HugEn;
input [15:0]  MaxFL;
input         r_IFG;

output        IFGCounterEq24;           // IFG counter reaches 9600 ns (960 ns)
output [3:0]  DlyCrcCnt;                // Delayed CRC counter
output        ByteCntEq0;               // Byte counter = 0
output        ByteCntEq1;               // Byte counter = 1
output        ByteCntEq2;               // Byte counter = 2  
output        ByteCntEq3;               // Byte counter = 3  
output        ByteCntEq4;               // Byte counter = 4  
output        ByteCntEq5;               // Byte counter = 5  
output        ByteCntEq6;               // Byte counter = 6
output        ByteCntEq7;               // Byte counter = 7
output        ByteCntGreat2;            // Byte counter > 2
output        ByteCntSmall7;            // Byte counter < 7
output        ByteCntMaxFrame;          // Byte counter = MaxFL
output [15:0] ByteCntOut;               // Byte counter
output 		  Rx_NibCnt;
output [15:0] frame_ByteCnt;

wire          ResetByteCounter;
wire 		  ResetFrameByteCounter;
wire          IncrementByteCounter;
wire          ResetIFGCounter;
wire          IncrementIFGCounter;
wire          ByteCntMax;

reg 		  Rx_NibCnt;
wire 		  Rx_ResetNibCnt;
wire 		  Rx_IncrementNibCnt;

reg   [15:0]  ByteCnt;
reg   [15:0]  frame_ByteCnt;
reg   [3:0]   DlyCrcCnt;
reg   [4:0]   IFGCounter;

wire  [15:0]  ByteCntDelayed;

//Moschip Team
//adding the nibcnt code 

assign Rx_ResetNibCnt = MRxDV & (StateSFD | StateData | (StateDA & Rx_NibCnt == 'd1 & ByteCnt == 'd5) |
						(StateSA & Rx_NibCnt == 'd1 & ByteCnt == 'd5) | (StateLength & Rx_NibCnt == 'd1 & ByteCnt == 'd1));

assign Rx_IncrementNibCnt = ~Rx_ResetNibCnt & MRxDV & (StateDA | StateSA | StateLength);


always @(posedge MRxClk or negedge Resetn)
begin
	if(Resetn == 0)
		Rx_NibCnt <= 'd0;
    else
    begin
      if(Rx_ResetNibCnt)
        Rx_NibCnt <= 'd0;
      else
      if(Rx_IncrementNibCnt)
        Rx_NibCnt <=  Rx_NibCnt + 'd1;
    end
end


assign ResetByteCounter = (MRxDV & ((StatePreamble & ByteCnt == 'd13)| (StateSFD &ByteCnt == 1 ) | (StateDA & Rx_NibCnt == 'd1 & ByteCnt == 'd5)|(StateSA & Rx_NibCnt == 'd1 & ByteCnt == 'd5)| 
							(StateLength & Rx_NibCnt == 'd1 & ByteCnt == 'd1)| StateData[1] & ByteCntMaxFrame)) | StateIdle;
							

assign IncrementByteCounter = (~ResetByteCounter & MRxDV & 
                              (StatePreamble | StateSFD | (StateDA & Rx_NibCnt == 'd1) | (StateSA & Rx_NibCnt == 'd1) | (StateLength & Rx_NibCnt == 'd1) |
							  StateIdle & ~Transmitting | StateData[1] & ~ByteCntMax & ~(DlyCrcEn & |DlyCrcCnt) 
                              )) | (~MRxDV & StateData[1]);


always @ (posedge MRxClk or negedge Resetn)
begin
  if(Resetn == 0)
    ByteCnt[15:0] <=  16'd0;
  else
    begin
      if(ResetByteCounter)
        ByteCnt[15:0] <=  16'd0;
      else
      if(IncrementByteCounter)
        ByteCnt[15:0] <=  ByteCnt[15:0] + 16'd1;
     end
end
assign ResetFrameByteCounter = (MRxDV & ((StatePreamble & ByteCnt == 'd13)| (StateSFD &ByteCnt == 1 )| StateData[1] & ByteCntMaxFrame)) | StateIdle;


always @ (posedge MRxClk or negedge Resetn)
begin
  if(Resetn == 0)
    frame_ByteCnt[15:0] <=  16'd0;
  else
    begin
      if(ResetFrameByteCounter)
        frame_ByteCnt[15:0] <=  16'd0;
      else
      if((StateDA  & Rx_NibCnt == 'd1 )| (StateSA & Rx_NibCnt == 'd1)| (StateLength & Rx_NibCnt == 'd1) | StateData[1])
        frame_ByteCnt[15:0] <=  frame_ByteCnt[15:0] + 16'd1;
     end
end

assign ByteCntDelayed = ByteCnt + 16'd4;
assign ByteCntOut = DlyCrcEn ? ByteCntDelayed : ByteCnt;

assign ByteCntEq0       = ByteCnt == 16'd0;
assign ByteCntEq1       = ByteCnt == 16'd1;
assign ByteCntEq2       = ByteCnt == 16'd2; 
assign ByteCntEq3       = ByteCnt == 16'd3; 
assign ByteCntEq4       = ByteCnt == 16'd4; 
assign ByteCntEq5       = ByteCnt == 16'd5; 
assign ByteCntEq6       = ByteCnt == 16'd6;
assign ByteCntEq7       = ByteCnt == 16'd7;
assign ByteCntGreat2    = ByteCnt >  16'd2;
assign ByteCntSmall7    = ByteCnt <  16'd7;
assign ByteCntMax       = ByteCnt == 16'hffff;
assign ByteCntMaxFrame  = ByteCnt == 16'd2048 & ~HugEn;



assign ResetIFGCounter = (StateIdle | StatePreamble)  &  MRxDV & MRxDEq5 | StateDrop;


assign IncrementIFGCounter = ~ResetIFGCounter & (StateDrop | StateIdle | StatePreamble ) & ~IFGCounterEq24;

always @ (posedge MRxClk or negedge Resetn)
begin
  if(Resetn == 0)
    IFGCounter[4:0] <=  5'h0;
  else
    begin
      if(ResetIFGCounter)
        IFGCounter[4:0] <=  5'h0;
      else
      if(IncrementIFGCounter)
        IFGCounter[4:0] <=  IFGCounter[4:0] + 5'd1; 
    end
end



assign IFGCounterEq24 = (IFGCounter[4:0] == 5'd23) | r_IFG; // 24*400 = 9600 ns or r_IFG is set to 1


always @ (posedge MRxClk or negedge Resetn)
begin
  if(Resetn == 0)
    DlyCrcCnt[3:0] <=  4'h0;
  else
    begin
      if(DlyCrcCnt[3:0] == 4'h9)
        DlyCrcCnt[3:0] <=  4'h0;
      else
      if(DlyCrcEn & StateSFD)	
        DlyCrcCnt[3:0] <=  4'h1;
      else
      if(DlyCrcEn & (|DlyCrcCnt[3:0]))
        DlyCrcCnt[3:0] <=  DlyCrcCnt[3:0] + 4'd1;
    end
end


endmodule


//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date:    17:39:27 06/07/2020 
// Design Name: 
// Module Name:    eth_rxcounters 
// Project Name: 
// Target Devices: 
// Tool versions: 
// Description: 
//
// Dependencies: 
//
// Revision: 
// Revision 0.01 - File Created
// Additional Comments: 
//
//////////////////////////////////////////////////////////////////////////////////
`include "timescale.v"
module eth_rxcounters 
  (
   MRxClk, Resetn, MRxDV, StateIdle, StateSFD, StateData, StateDrop, StateSA, StateDA,StateLength, StatePreamble, 
   MRxDEq5, MRxDEqD, DlyCrcEn, DlyCrcCnt, Transmitting, MaxFL, r_IFG, HugEn, IFGCounterEq24, 
   ByteCntEq0, ByteCntEq1, ByteCntEq2,ByteCntEq3,ByteCntEq4,ByteCntEq5, ByteCntEq6,
   ByteCntEq7, ByteCntGreat2, ByteCntSmall7, ByteCntMaxFrame, ByteCntOut, Rx_NibCnt,frame_ByteCnt
   );

input         MRxClk;
input         Resetn;
input         MRxDV;
input         StateSFD;
input [1:0]   StateData;
input 		  MRxDEq5;
input         MRxDEqD;
input         StateIdle;
input         StateDrop;
input         DlyCrcEn;
input         StatePreamble;
input 		  StateDA;
input 		  StateSA;
input 		  StateLength;
input         Transmitting;
input         HugEn;
input [15:0]  MaxFL;
input         r_IFG;

output        IFGCounterEq24;           // IFG counter reaches 9600 ns (960 ns)
output [3:0]  DlyCrcCnt;                // Delayed CRC counter
output        ByteCntEq0;               // Byte counter = 0
output        ByteCntEq1;               // Byte counter = 1
output        ByteCntEq2;               // Byte counter = 2  
output        ByteCntEq3;               // Byte counter = 3  
output        ByteCntEq4;               // Byte counter = 4  
output        ByteCntEq5;               // Byte counter = 5  
output        ByteCntEq6;               // Byte counter = 6
output        ByteCntEq7;               // Byte counter = 7
output        ByteCntGreat2;            // Byte counter > 2
output        ByteCntSmall7;            // Byte counter < 7
output        ByteCntMaxFrame;          // Byte counter = MaxFL
output [15:0] ByteCntOut;               // Byte counter
output 		  Rx_NibCnt;
output [15:0] frame_ByteCnt;

wire          ResetByteCounter;
wire 		  ResetFrameByteCounter;
wire          IncrementByteCounter;
wire          ResetIFGCounter;
wire          IncrementIFGCounter;
wire          ByteCntMax;

reg 		  Rx_NibCnt;
wire 		  Rx_ResetNibCnt;
wire 		  Rx_IncrementNibCnt;

reg   [15:0]  ByteCnt;
reg   [15:0]  frame_ByteCnt;
reg   [3:0]   DlyCrcCnt;
reg   [4:0]   IFGCounter;

wire  [15:0]  ByteCntDelayed;

//Moschip Team
//adding the nibcnt code 

assign Rx_ResetNibCnt = MRxDV & (StateSFD | StateData | (StateDA & Rx_NibCnt == 'd1 & ByteCnt == 'd5) |
						(StateSA & Rx_NibCnt == 'd1 & ByteCnt == 'd5) | (StateLength & Rx_NibCnt == 'd1 & ByteCnt == 'd1));

assign Rx_IncrementNibCnt = ~Rx_ResetNibCnt & MRxDV & (StateDA | StateSA | StateLength);


always @(posedge MRxClk or negedge Resetn)
begin
	if(Resetn == 0)
		Rx_NibCnt <= 'd0;
    else
    begin
      if(Rx_ResetNibCnt)
        Rx_NibCnt <= 'd0;
      else
      if(Rx_IncrementNibCnt)
        Rx_NibCnt <=  Rx_NibCnt + 'd1;
    end
end


assign ResetByteCounter = (MRxDV & ((StatePreamble & ByteCnt == 'd13)| (StateSFD &ByteCnt == 1 ) | (StateDA & Rx_NibCnt == 'd1 & ByteCnt == 'd5)|(StateSA & Rx_NibCnt == 'd1 & ByteCnt == 'd5)| 
							(StateLength & Rx_NibCnt == 'd1 & ByteCnt == 'd1)| StateData[1] & ByteCntMaxFrame)) | StateIdle;
							

assign IncrementByteCounter = (~ResetByteCounter & MRxDV & 
                              (StatePreamble | StateSFD | (StateDA & Rx_NibCnt == 'd1) | (StateSA & Rx_NibCnt == 'd1) | (StateLength & Rx_NibCnt == 'd1) |
							  StateIdle & ~Transmitting | StateData[1] & ~ByteCntMax & ~(DlyCrcEn & |DlyCrcCnt) 
                              )) | (~MRxDV & StateData[1]);


always @ (posedge MRxClk or negedge Resetn)
begin
  if(Resetn == 0)
    ByteCnt[15:0] <=  16'd0;
  else
    begin
      if(ResetByteCounter)
        ByteCnt[15:0] <=  16'd0;
      else
      if(IncrementByteCounter)
        ByteCnt[15:0] <=  ByteCnt[15:0] + 16'd1;
     end
end
assign ResetFrameByteCounter = (MRxDV & ((StatePreamble & ByteCnt == 'd13)| (StateSFD &ByteCnt == 1 )| StateData[1] & ByteCntMaxFrame)) | StateIdle;


always @ (posedge MRxClk or negedge Resetn)
begin
  if(Resetn == 0)
    frame_ByteCnt[15:0] <=  16'd0;
  else
    begin
      if(ResetFrameByteCounter)
        frame_ByteCnt[15:0] <=  16'd0;
      else
      if((StateDA  & Rx_NibCnt == 'd1 )| (StateSA & Rx_NibCnt == 'd1)| (StateLength & Rx_NibCnt == 'd1) | StateData[1])
        frame_ByteCnt[15:0] <=  frame_ByteCnt[15:0] + 16'd1;
     end
end

assign ByteCntDelayed = ByteCnt + 16'd4;
assign ByteCntOut = DlyCrcEn ? ByteCntDelayed : ByteCnt;

assign ByteCntEq0       = ByteCnt == 16'd0;
assign ByteCntEq1       = ByteCnt == 16'd1;
assign ByteCntEq2       = ByteCnt == 16'd2; 
assign ByteCntEq3       = ByteCnt == 16'd3; 
assign ByteCntEq4       = ByteCnt == 16'd4; 
assign ByteCntEq5       = ByteCnt == 16'd5; 
assign ByteCntEq6       = ByteCnt == 16'd6;
assign ByteCntEq7       = ByteCnt == 16'd7;
assign ByteCntGreat2    = ByteCnt >  16'd2;
assign ByteCntSmall7    = ByteCnt <  16'd7;
assign ByteCntMax       = ByteCnt == 16'hffff;
assign ByteCntMaxFrame  = ByteCnt == 16'd2048 & ~HugEn;



assign ResetIFGCounter = (StateIdle | StatePreamble)  &  MRxDV & MRxDEq5 | StateDrop;


assign IncrementIFGCounter = ~ResetIFGCounter & (StateDrop | StateIdle | StatePreamble ) & ~IFGCounterEq24;

always @ (posedge MRxClk or negedge Resetn)
begin
  if(Resetn == 0)
    IFGCounter[4:0] <=  5'h0;
  else
    begin
      if(ResetIFGCounter)
        IFGCounter[4:0] <=  5'h0;
      else
      if(IncrementIFGCounter)
        IFGCounter[4:0] <=  IFGCounter[4:0] + 5'd1; 
    end
end



assign IFGCounterEq24 = (IFGCounter[4:0] == 5'd23) | r_IFG; // 24*400 = 9600 ns or r_IFG is set to 1


always @ (posedge MRxClk or negedge Resetn)
begin
  if(Resetn == 0)
    DlyCrcCnt[3:0] <=  4'h0;
  else
    begin
      if(DlyCrcCnt[3:0] == 4'h9)
        DlyCrcCnt[3:0] <=  4'h0;
      else
      if(DlyCrcEn & StateSFD)	
        DlyCrcCnt[3:0] <=  4'h1;
      else
      if(DlyCrcEn & (|DlyCrcCnt[3:0]))
        DlyCrcCnt[3:0] <=  DlyCrcCnt[3:0] + 4'd1;
    end
end


endmodule


//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date:    17:40:08 06/07/2020 
// Design Name: 
// Module Name:    eth_rxethmac 
// Project Name: 
// Target Devices: 
// Tool versions: 
// Description: 
//
// Dependencies: 
//
// Revision: 
// Revision 0.01 - File Created
// Additional Comments: 
//
//////////////////////////////////////////////////////////////////////////////////

`include "timescale.v"
module eth_rxethmac (MRxClk, MRxDV, MRxD,MRxErr, Resetn, Transmitting, MaxFL,r_MinFL, r_IFG,No_Preamble,
                     HugEn,Pad, DlyCrcEn, RxData, RxValid, RxStartFrm, RxEndFrm,
                     ByteCnt, ByteCntEq0, ByteCntGreat2, ByteCntMaxFrame,
                     CrcError, StateIdle, StatePreamble, StateSFD, StateData, StateDA, StateSA, StateLength,
                     MAC, r_Pro, r_Bro,r_Iam,r_HASH0, r_HASH1, RxAbort, AddressMiss,MRxErr_Detected,Length_Vs_Payload_error,Length_vs_payload_mismatch,
                     PassAll, ControlFrmAddressOK
                    );

input         MRxClk;
input         MRxDV;
input   [3:0] MRxD;
input 		  MRxErr;
input         Transmitting;
input         HugEn;
input 		  Pad;
input         DlyCrcEn;
input  [15:0] r_MinFL;
input  [15:0] MaxFL;
input         r_IFG;
input 		  No_Preamble;
input         Resetn;
input  [47:0] MAC;     //  Station Address  
input         r_Bro;   //  broadcast disable
input         r_Pro;   //  promiscuous enable 
input 		  r_Iam;   //  Individual Address mode
input [31:0]  r_HASH0; //  lower 4 bytes Hash Table
input [31:0]  r_HASH1; //  upper 4 bytes Hash Table
input         PassAll;
input         ControlFrmAddressOK;

output  [7:0] RxData;
output        RxValid;
output        RxStartFrm;
output        RxEndFrm;
output [15:0] ByteCnt;
output        ByteCntEq0;
output        ByteCntGreat2;
output        ByteCntMaxFrame;
output        CrcError;
output        StateIdle;
output        StatePreamble;
output        StateSFD;
output  [1:0] StateData;
output 		  StateDA;
output 		  StateSA;
output 		  StateLength;
output        RxAbort;
output        AddressMiss;
output 		  MRxErr_Detected;
output 		  Length_Vs_Payload_error;
output 		  Length_vs_payload_mismatch;



reg 		  Length_Vs_Payload_error;
wire 		  Length_vs_payload_mismatch;
reg 	[15:0]Frame_Length;
reg     [7:0] RxData;
reg           RxValid;
reg           RxStartFrm;
reg           RxEndFrm;
reg     [5:0] CrcHash;
reg           CrcHashGood;
reg 		  CrcHashGood_next;
reg           DelayData;
reg     [7:0] LatchedByte;
reg     [7:0] RxData_d;
reg           RxValid_d1;
reg 		  RxValid_d2;
reg 		  RxValid_d3;
reg           RxStartFrm_d;
reg           RxEndFrm_d1;
reg 		  RxEndFrm_d2;
reg 		  Frame_drop;
reg 		  shift8_py_gt_len_pad1_dat0_f0;
reg 		  shift8_py_gt_len_pad1_dat0_f1;
reg 		  shift8_py_gt_len_pad1_dat0_f2;
reg 		  shift8_py_gt_len_pad1_dat0_f3;
reg 		  shift8_py_gt_len_pad1_dat0_f4;
reg 		  shift8_py_gt_len_pad1_dat0_f5;
reg 		  shift8_py_gt_len_pad1_dat0_f6;
reg 		  shift8_py_gt_len_pad1_dat0_f7;
reg 		  py_gt_len_pad1_dat0;
reg 		  payld_gt_maxfl_error;





wire          MRxDEqD;
wire          MRxDEq5;
wire          StateDrop;
wire          ByteCntEq1;
wire          ByteCntEq2;
wire          ByteCntEq3;
wire          ByteCntEq4;
wire          ByteCntEq5;
wire          ByteCntEq6;
wire          ByteCntEq7;
wire          ByteCntSmall7;
wire  [15:0]  frame_ByteCnt;
wire   [31:0] Crc;
wire          Enable_Crc;
wire          Initialize_Crc;
wire    [3:0] Data_Crc;
wire          GenerateRxValid;
wire          GenerateRxStartFrm;
wire          GenerateRxEndFrm;
wire          DribbleRxEndFrm;
wire    [3:0] DlyCrcCnt;
wire          IFGCounterEq24;
wire 		  Rx_NibCnt;
wire 		  Address_mismatch;
reg 		  Preamble_mismatch;
reg 		  SFD_mismatch;
wire       rxabort_statedrop;
reg endframe_d;
reg endframe_d1;
reg 		MRxErr_Detected;

assign MRxDEqD = MRxD == 4'hd;
assign MRxDEq5 = MRxD == 4'h5;


// Rx State Machine module
eth_rxstatem rxstatem1
  (.MRxClk(MRxClk),
   .Resetn(Resetn),
   .MRxDV(MRxDV),
   .No_Preamble(No_Preamble),
   .Rx_NibCnt(Rx_NibCnt),
   .Frame_drop(Frame_drop),
   .ByteCnt(ByteCnt),
   .ByteCntEq0(ByteCntEq0),
   .ByteCntGreat2(ByteCntGreat2),
   .Transmitting(Transmitting),
   .MRxDEq5(MRxDEq5),
   .MRxDEqD(MRxDEqD),
   .IFGCounterEq24(IFGCounterEq24),
   .ByteCntMaxFrame(ByteCntMaxFrame),
   .StateData(StateData),
   .StateIdle(StateIdle),
   .StatePreamble(StatePreamble),
   .StateSFD(StateSFD),
   .StateDA(StateDA),
   .StateSA(StateSA),
   .StateLength(StateLength),
   .StateDrop(StateDrop),
	.rxabort_statedrop(rxabort_statedrop)
   );


// Rx Counters module
eth_rxcounters rxcounters1
  (.MRxClk(MRxClk),
   .Resetn(Resetn),
   .MRxDV(MRxDV),
   .StateIdle(StateIdle),
   .StateSFD(StateSFD),
   .StateData(StateData),
   .StateDrop(StateDrop),
   .StatePreamble(StatePreamble),
   .StateDA(StateDA),
   .StateSA(StateSA),
   .StateLength(StateLength),
   .MRxDEq5(MRxDEq5),
   .MRxDEqD(MRxDEqD),
   .DlyCrcEn(DlyCrcEn),
   .DlyCrcCnt(DlyCrcCnt),
   .Transmitting(Transmitting),
   .MaxFL(MaxFL),
   .r_IFG(r_IFG),
   .HugEn(HugEn),
   .IFGCounterEq24(IFGCounterEq24),
   .ByteCntEq0(ByteCntEq0),
   .ByteCntEq1(ByteCntEq1),
   .ByteCntEq2(ByteCntEq2),
   .ByteCntEq3(ByteCntEq3),
   .ByteCntEq4(ByteCntEq4),
   .ByteCntEq5(ByteCntEq5),
   .ByteCntEq6(ByteCntEq6),
   .ByteCntEq7(ByteCntEq7),
   .ByteCntGreat2(ByteCntGreat2),
   .ByteCntSmall7(ByteCntSmall7),
   .ByteCntMaxFrame(ByteCntMaxFrame),
   .ByteCntOut(ByteCnt),
   .frame_ByteCnt(frame_ByteCnt),
   .Rx_NibCnt(Rx_NibCnt)
   );

// Rx Address Check

eth_rxaddrcheck rxaddrcheck1
  (.MRxClk(MRxClk),
   .Resetn( Resetn),
   .MRxD(MRxD),
   .LatchedByte(LatchedByte),
   .Rx_NibCnt(Rx_NibCnt),   
   .r_Bro (r_Bro),
   .r_Pro(r_Pro),
   .r_Iam(r_Iam),
   .ByteCntEq6(ByteCntEq6),
   .ByteCntEq7(ByteCntEq7),
   .ByteCntEq1(ByteCntEq1),
   .ByteCntEq2(ByteCntEq2),
   .ByteCntEq3(ByteCntEq3),
   .ByteCntEq4(ByteCntEq4),
   .ByteCntEq5(ByteCntEq5),
   .HASH0(r_HASH0),
   .HASH1(r_HASH1),
   .ByteCntEq0(ByteCntEq0),
   .CrcHash(CrcHash),
   .CrcHashGood(CrcHashGood),		
   .StateDA(StateDA),
   .StateSFD(StateSFD),
   .StateIdle(StateIdle),
   .StateDrop(StateDrop),
   .MAC(MAC),
   .Address_mismatch(Address_mismatch),
   .RxEndFrm(RxEndFrm),
   .AddressMiss(AddressMiss),
   .RxAddressInvalid(RxAddressInvalid),
   .PassAll(PassAll),
   .ControlFrmAddressOK(ControlFrmAddressOK)
   );
   
//Note: 1.Depending on any error of Frame below frame_error should be Generated.
//      2.And this signal should be high until end of the Frame.
//	    3.So that other logics(ex:fifo) should drop that Frame.    
//assign RxAbort = (endframe_d && AddressMiss) | rxabort_statedrop | Length_Vs_Payload_error;
assign RxAbort = (endframe_d1 && AddressMiss) | rxabort_statedrop | Length_Vs_Payload_error | (endframe_d1 && MRxErr_Detected);

assign Length_vs_payload_mismatch = (!shift8_py_gt_len_pad1_dat0_f5 && endframe_d);

assign Enable_Crc = (MRxDV & (StateDA | StateSA | StateLength |(|StateData & ~ByteCntMaxFrame))) |(~MRxDV & (|StateData & ~ByteCntMaxFrame)) ;		
assign Initialize_Crc = StateSFD | DlyCrcEn & (|DlyCrcCnt[3:0]) &
                        DlyCrcCnt[3:0] < 4'h9;


assign Data_Crc[0] = LatchedByte[7];	
assign Data_Crc[1] = LatchedByte[6];
assign Data_Crc[2] = LatchedByte[5];
assign Data_Crc[3] = LatchedByte[4];

// Connecting module Crc
eth_crc crcrx
  (.Clk(MRxClk),
   .Resetn(Resetn),
   .Data(Data_Crc),
   .Enable(Enable_Crc),
   .Initialize(Initialize_Crc), 
   .Crc(Crc),
   .CrcError(CrcError)
   );


// Latching CRC for use in the hash table
always @ (posedge MRxClk)
begin
  CrcHashGood <= CrcHashGood_next;  
end
always@(*)
begin
    CrcHashGood_next=(StateDA & Rx_NibCnt == 'd1) & ByteCntEq5; 
end
always @ (posedge MRxClk or negedge Resetn)
begin
  if(Resetn == 0 | StateIdle)
    CrcHash[5:0] <=  6'h0;
  else
     if(CrcHashGood_next)
          CrcHash[5:0] <=  Crc[31:26];
end

// Output byte stream
always @ (posedge MRxClk or negedge Resetn)
begin
  if(Resetn == 0)
    begin
      RxData_d[7:0]      <=  8'h0;
      DelayData          <=  1'b0;
      LatchedByte[7:0]   <=  8'h0;
      RxData[7:0]        <=  8'h0;
    end
  else
    begin 
      LatchedByte[7:0]   <=  {MRxD[3:0], LatchedByte[7:4]};
	  DelayData          <=  (StateDA & Rx_NibCnt == 'd1)|(StateSA & Rx_NibCnt == 'd1) | (StateLength & Rx_NibCnt == 'd1)|StateData[1];

      if(GenerateRxValid)
		//Data goes through DA,SA,Length and data States 
        RxData_d[7:0] <=  LatchedByte[7:0] & ({8{|StateData}} | {8{StateDA}} | {8{StateSA}} | {8{StateLength}});
      else
      if(~DelayData)
        // Delaying data to be valid for two cycles.
        // Zero when not active.
        RxData_d[7:0] <=  8'h0;

      RxData[7:0] <=  RxData_d[7:0];          // Output data byte
    end
end
//added code by Moschip Team on September 4th 2020

always @(posedge MRxClk or negedge Resetn)
begin
	if(Resetn == 0)
	begin
		MRxErr_Detected <= 0;
	end
	else if(RxEndFrm)
	begin
		MRxErr_Detected <= 0;
	end
	else 
	begin
		case(1)
			StateDA,StateSA,StateLength,StateData[0],StateData[1]:begin
																	if(MRxErr)
																		MRxErr_Detected <= 1;
																	else
																		MRxErr_Detected <= MRxErr_Detected;
																  end
		endcase
	end
end

//added code by Moschip Team on June 15th

always @(posedge MRxClk or negedge Resetn)
begin
	if(Resetn == 0)
	begin
		Frame_drop <= 0;
		Preamble_mismatch <= 0;
		SFD_mismatch <= 0;
	end
	else 
	begin 
		if(StateIdle)
		begin
			if(MRxDV)
			begin
				case(No_Preamble)
				0 : begin 
						if(MRxD != 'd5)
							begin
								Frame_drop <= 1;
								Preamble_mismatch <= 1;
							end
						else
							begin
								if(MRxErr == 1)
								begin
								Frame_drop <= 1;
								Preamble_mismatch <= 0;
								end
								else
								begin
								Frame_drop <= 0;
								Preamble_mismatch <= 0;
								end
							end
					end
				1: begin
						if(MRxD != 'd5)
						begin 
							Frame_drop <= 1;
							SFD_mismatch <= 1;
						end
						else
						begin
							if(MRxErr == 1)
							begin
							Frame_drop <= 1;
							SFD_mismatch <= 0;
							end
							else
							begin
							Frame_drop <= 0;
							SFD_mismatch <= 0;
							end
						end
				   end
				endcase
			end
			else
			begin
				Frame_drop <= 0;
				Preamble_mismatch <= 0;
				SFD_mismatch <= 0;
			end
		end
		else if(StatePreamble)
		begin
			if(LatchedByte[7:4] == 'd5)
			begin
				if(MRxErr)
				begin
				Frame_drop <= 1;
				Preamble_mismatch <= 0;
				end
				else
				begin
				Frame_drop <= 0;
				Preamble_mismatch <= 0;
				end
			end
			else
			begin
				Frame_drop <= 1;
				Preamble_mismatch <= 1;
			end
		end
		else 
			if(StateSFD)
			begin
				if((LatchedByte[7:4] == 'd5) & ByteCnt == 0)	
				begin
					if(MRxErr)
					begin
					Frame_drop <= 1;
					SFD_mismatch <= 0;
					end
					else
					begin
					Frame_drop <= 0;
					SFD_mismatch <= 0;
					end
				end
				else if((LatchedByte[7:4] == 'hd) & ByteCnt == 1)
				begin
					if(MRxErr)
					begin
					Frame_drop <= 1;
					SFD_mismatch <= 0;
					end
					else
					begin
					Frame_drop <= 0;
					SFD_mismatch <= 0;
					end
				end
				else 
				begin
					Frame_drop <= 1;
					SFD_mismatch <= 1;
				end
			end
		else 
		begin
			Frame_drop <= 0;
			Preamble_mismatch <= 0;
			SFD_mismatch <= 0;
		end
	end
end

assign GenerateRxValid = ((StateDA & Rx_NibCnt == 'd1)| (StateSA & Rx_NibCnt == 'd1) | (StateLength & Rx_NibCnt == 'd1)| StateData[1]);


always @ (posedge MRxClk or negedge Resetn)
begin
  if(Resetn == 0)
    begin
      RxValid_d1 <=  1'b0;
      RxValid   <=  1'b0;
    end
  else
    begin
      RxValid_d1 <=  GenerateRxValid;
      RxValid   <=  RxValid_d1;
	  
    end
end


assign GenerateRxStartFrm = (StateDA & Rx_NibCnt == 'd1) & ((ByteCntEq0 & ~DlyCrcEn)| ((DlyCrcCnt == 4'h3) & DlyCrcEn));	

always @ (posedge MRxClk or negedge Resetn)
begin
  if(Resetn == 0)
    begin
      RxStartFrm_d <=  1'b0;
      RxStartFrm   <=  1'b0;
    end
  else
    begin
      RxStartFrm_d <=  GenerateRxStartFrm;
      RxStartFrm   <=  RxStartFrm_d;
    end
end



assign GenerateRxEndFrm = StateData[1] &
                          (~MRxDV & ByteCntGreat2 | ByteCntMaxFrame);	

assign DribbleRxEndFrm  = StateData[0] &  ~MRxDV & ByteCntGreat2;


always @ (posedge MRxClk or negedge Resetn)
begin
  if(Resetn == 0)
    begin
      RxEndFrm_d1 <=  1'b0;
      RxEndFrm    <=  1'b0;
    end
  else
    begin
      RxEndFrm_d1 <=  GenerateRxEndFrm;
      RxEndFrm    <=  RxEndFrm_d1 | DribbleRxEndFrm;
    end
end

//Added by the Moschip team on June 1st 2020
reg [3:0] MRxD_d;
reg MRxDV_d;


always@(posedge MRxClk or negedge Resetn)
begin
	if(!Resetn)
		MRxD_d <= 0;
	else
	begin
		MRxD_d <= MRxD;
	end
end

always@(posedge MRxClk or negedge Resetn)
begin
	if(!Resetn)
		MRxDV_d <= 0;
	else
	begin
		MRxDV_d <= MRxDV;
	end
end

//added code by Moschip Team on June 8th
always @(posedge MRxClk or negedge Resetn)
begin
	if(Resetn == 0)
		Frame_Length <= 0;
	else
	begin
		if(StateLength)
		begin
			case(1)
			ByteCntEq0:begin   
						Frame_Length[15:8] <= {MRxD_d[3:0],Frame_Length[15:12]}; 
						end
			ByteCntEq1:begin   
						Frame_Length[7:0]  <= {MRxD_d[3:0],Frame_Length[7:4]}; 
					   end
			endcase
		end
	end
end

always @(posedge MRxClk or negedge Resetn)
begin
	if(Resetn == 0)
	begin
		payld_gt_maxfl_error <= 0;
	end
	else
	begin
		if(StateData)
		begin
			if((frame_ByteCnt + 1) > MaxFL)
			begin
				if(HugEn == 0)
				begin
					payld_gt_maxfl_error <= 1;
				end
				else
					payld_gt_maxfl_error <= 0;
			end
			else
				payld_gt_maxfl_error <= 0;
		end
		else
			payld_gt_maxfl_error <= 0;
	end
end


always@(posedge MRxClk or negedge Resetn)
begin
	if(Resetn == 0)
	begin
		py_gt_len_pad1_dat0 <= 1;
	end
	else
	begin
		if(StateData)
		begin
			if((ByteCnt > Frame_Length) && ByteCnt <= 'd46)
			begin
				if(Pad)
				begin
					case(StateData)
						2'b01:begin
								if(RxData_d[3:0] != 0)
								begin
									py_gt_len_pad1_dat0 <= 0;
								end
								else
								begin
									py_gt_len_pad1_dat0 <= py_gt_len_pad1_dat0 && 1'b1;
								end
							  end
						2'b10:begin
								if(RxData_d[7:4] != 0)
								begin
									py_gt_len_pad1_dat0 <= 0;
								end
								else
								begin
									py_gt_len_pad1_dat0 <= py_gt_len_pad1_dat0 && 1'b1;
								end
							  end
					endcase
				end
				else
					py_gt_len_pad1_dat0 <= 0;
			end
			else
			begin
				py_gt_len_pad1_dat0 <= 1; 
			end
		end
		else
			py_gt_len_pad1_dat0 <= 1; 
	end
end

always @(posedge MRxClk or negedge Resetn )
begin
    if(Resetn == 0) 
	begin 
		shift8_py_gt_len_pad1_dat0_f0 <= 1;
		shift8_py_gt_len_pad1_dat0_f1 <= 1;
		shift8_py_gt_len_pad1_dat0_f2 <= 1;
		shift8_py_gt_len_pad1_dat0_f3 <= 1;
		shift8_py_gt_len_pad1_dat0_f4 <= 1;
		shift8_py_gt_len_pad1_dat0_f5 <= 1;
		shift8_py_gt_len_pad1_dat0_f6 <= 1;
		shift8_py_gt_len_pad1_dat0_f7 <= 1;
	end
	else 
	begin
		shift8_py_gt_len_pad1_dat0_f0 <= py_gt_len_pad1_dat0;
		shift8_py_gt_len_pad1_dat0_f1 <= shift8_py_gt_len_pad1_dat0_f0;
		shift8_py_gt_len_pad1_dat0_f2 <= shift8_py_gt_len_pad1_dat0_f1;
		shift8_py_gt_len_pad1_dat0_f3 <= shift8_py_gt_len_pad1_dat0_f2;
		shift8_py_gt_len_pad1_dat0_f4 <= shift8_py_gt_len_pad1_dat0_f3;
		shift8_py_gt_len_pad1_dat0_f5 <= shift8_py_gt_len_pad1_dat0_f4;
		shift8_py_gt_len_pad1_dat0_f6 <= shift8_py_gt_len_pad1_dat0_f5;
		shift8_py_gt_len_pad1_dat0_f7 <= shift8_py_gt_len_pad1_dat0_f6;
	end
end
//

always@(posedge MRxClk or negedge Resetn)
begin
	if(Resetn == 0) endframe_d <= 1'b0;
	else if(StateData[1] && MRxDV == 0) endframe_d <= 1'b1;
	else endframe_d <= 1'b0;
end

always@(posedge MRxClk or negedge Resetn)
begin
	if(Resetn == 0) 
		endframe_d1 <= 1'b0;
	else
		endframe_d1 <= endframe_d;
end

//added code for length_vs_payload error
							
always@(posedge MRxClk or negedge Resetn)
begin
	if(Resetn == 0)
		Length_Vs_Payload_error <= 0;
	else
	begin
		if(endframe_d)
		begin
			case(1)
			(ByteCnt-4 == Frame_Length):begin
											if(CrcError == 0)
											begin
												if(frame_ByteCnt < r_MinFL)
												begin
													Length_Vs_Payload_error <= 1;		//drop frame
												end
												else if(frame_ByteCnt == r_MinFL)
												begin
													Length_Vs_Payload_error <= 0;	//accept frame
												end
												else if(frame_ByteCnt > r_MinFL)
												begin
													if(frame_ByteCnt <= MaxFL)	//FL <= MAXFL
													begin
														Length_Vs_Payload_error <= 0;	//accept frame
													end
													else if(frame_ByteCnt > MaxFL)
													begin
														if(HugEn == 0)
														begin
															Length_Vs_Payload_error <= 1; //drop frame
														end
														else
														begin
															Length_Vs_Payload_error <= 0;
														end
													end
												end
											end
											else
												Length_Vs_Payload_error <= 1;		//drop frame
									    end
			(ByteCnt-4 > Frame_Length):begin
											if(Pad)
											begin
												if(RxEndFrm_d1)
												begin
													if(shift8_py_gt_len_pad1_dat0_f5)	
													begin	
														if(CrcError)
															begin
															Length_Vs_Payload_error <= 1;		//drop frame
															end
														else
														begin
															if(frame_ByteCnt == r_MinFL)
															begin
																Length_Vs_Payload_error <= 0;
															end
															else
															begin
																Length_Vs_Payload_error <= 1;		//drop frame
															end
														end
													end
													else
														Length_Vs_Payload_error <= 1;		//drop frame
												end
												else
													Length_Vs_Payload_error <= 0;
											end
											else
												Length_Vs_Payload_error <= 1;		//drop frame
									   end
			(ByteCnt-4 < Frame_Length):begin
											Length_Vs_Payload_error <= 1;		//drop frame
									   end							
			endcase
		end	
		else
			Length_Vs_Payload_error <= 0;
	end
end	

endmodule


//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date:    17:40:08 06/07/2020 
// Design Name: 
// Module Name:    eth_rxethmac 
// Project Name: 
// Target Devices: 
// Tool versions: 
// Description: 
//
// Dependencies: 
//
// Revision: 
// Revision 0.01 - File Created
// Additional Comments: 
//
//////////////////////////////////////////////////////////////////////////////////

`include "timescale.v"
module eth_rxethmac (MRxClk, MRxDV, MRxD,MRxErr, Resetn, Transmitting, MaxFL,r_MinFL, r_IFG,No_Preamble,
                     HugEn,Pad, DlyCrcEn, RxData, RxValid, RxStartFrm, RxEndFrm,
                     ByteCnt, ByteCntEq0, ByteCntGreat2, ByteCntMaxFrame,
                     CrcError, StateIdle, StatePreamble, StateSFD, StateData, StateDA, StateSA, StateLength,
                     MAC, r_Pro, r_Bro,r_Iam,r_HASH0, r_HASH1, RxAbort, AddressMiss,MRxErr_Detected,Length_Vs_Payload_error,Length_vs_payload_mismatch,
                     PassAll, ControlFrmAddressOK
                    );

input         MRxClk;
input         MRxDV;
input   [3:0] MRxD;
input 		  MRxErr;
input         Transmitting;
input         HugEn;
input 		  Pad;
input         DlyCrcEn;
input  [15:0] r_MinFL;
input  [15:0] MaxFL;
input         r_IFG;
input 		  No_Preamble;
input         Resetn;
input  [47:0] MAC;     //  Station Address  
input         r_Bro;   //  broadcast disable
input         r_Pro;   //  promiscuous enable 
input 		  r_Iam;   //  Individual Address mode
input [31:0]  r_HASH0; //  lower 4 bytes Hash Table
input [31:0]  r_HASH1; //  upper 4 bytes Hash Table
input         PassAll;
input         ControlFrmAddressOK;

output  [7:0] RxData;
output        RxValid;
output        RxStartFrm;
output        RxEndFrm;
output [15:0] ByteCnt;
output        ByteCntEq0;
output        ByteCntGreat2;
output        ByteCntMaxFrame;
output        CrcError;
output        StateIdle;
output        StatePreamble;
output        StateSFD;
output  [1:0] StateData;
output 		  StateDA;
output 		  StateSA;
output 		  StateLength;
output        RxAbort;
output        AddressMiss;
output 		  MRxErr_Detected;
output 		  Length_Vs_Payload_error;
output 		  Length_vs_payload_mismatch;



reg 		  Length_Vs_Payload_error;
wire 		  Length_vs_payload_mismatch;
reg 	[15:0]Frame_Length;
reg     [7:0] RxData;
reg           RxValid;
reg           RxStartFrm;
reg           RxEndFrm;
reg     [5:0] CrcHash;
reg           CrcHashGood;
reg 		  CrcHashGood_next;
reg           DelayData;
reg     [7:0] LatchedByte;
reg     [7:0] RxData_d;
reg           RxValid_d1;
reg 		  RxValid_d2;
reg 		  RxValid_d3;
reg           RxStartFrm_d;
reg           RxEndFrm_d1;
reg 		  RxEndFrm_d2;
reg 		  Frame_drop;
reg 		  shift8_py_gt_len_pad1_dat0_f0;
reg 		  shift8_py_gt_len_pad1_dat0_f1;
reg 		  shift8_py_gt_len_pad1_dat0_f2;
reg 		  shift8_py_gt_len_pad1_dat0_f3;
reg 		  shift8_py_gt_len_pad1_dat0_f4;
reg 		  shift8_py_gt_len_pad1_dat0_f5;
reg 		  shift8_py_gt_len_pad1_dat0_f6;
reg 		  shift8_py_gt_len_pad1_dat0_f7;
reg 		  py_gt_len_pad1_dat0;
reg 		  payld_gt_maxfl_error;





wire          MRxDEqD;
wire          MRxDEq5;
wire          StateDrop;
wire          ByteCntEq1;
wire          ByteCntEq2;
wire          ByteCntEq3;
wire          ByteCntEq4;
wire          ByteCntEq5;
wire          ByteCntEq6;
wire          ByteCntEq7;
wire          ByteCntSmall7;
wire  [15:0]  frame_ByteCnt;
wire   [31:0] Crc;
wire          Enable_Crc;
wire          Initialize_Crc;
wire    [3:0] Data_Crc;
wire          GenerateRxValid;
wire          GenerateRxStartFrm;
wire          GenerateRxEndFrm;
wire          DribbleRxEndFrm;
wire    [3:0] DlyCrcCnt;
wire          IFGCounterEq24;
wire 		  Rx_NibCnt;
wire 		  Address_mismatch;
reg 		  Preamble_mismatch;
reg 		  SFD_mismatch;
wire       rxabort_statedrop;
reg endframe_d;
reg endframe_d1;
reg 		MRxErr_Detected;

assign MRxDEqD = MRxD == 4'hd;
assign MRxDEq5 = MRxD == 4'h5;


// Rx State Machine module
eth_rxstatem rxstatem1
  (.MRxClk(MRxClk),
   .Resetn(Resetn),
   .MRxDV(MRxDV),
   .No_Preamble(No_Preamble),
   .Rx_NibCnt(Rx_NibCnt),
   .Frame_drop(Frame_drop),
   .ByteCnt(ByteCnt),
   .ByteCntEq0(ByteCntEq0),
   .ByteCntGreat2(ByteCntGreat2),
   .Transmitting(Transmitting),
   .MRxDEq5(MRxDEq5),
   .MRxDEqD(MRxDEqD),
   .IFGCounterEq24(IFGCounterEq24),
   .ByteCntMaxFrame(ByteCntMaxFrame),
   .StateData(StateData),
   .StateIdle(StateIdle),
   .StatePreamble(StatePreamble),
   .StateSFD(StateSFD),
   .StateDA(StateDA),
   .StateSA(StateSA),
   .StateLength(StateLength),
   .StateDrop(StateDrop),
	.rxabort_statedrop(rxabort_statedrop)
   );


// Rx Counters module
eth_rxcounters rxcounters1
  (.MRxClk(MRxClk),
   .Resetn(Resetn),
   .MRxDV(MRxDV),
   .StateIdle(StateIdle),
   .StateSFD(StateSFD),
   .StateData(StateData),
   .StateDrop(StateDrop),
   .StatePreamble(StatePreamble),
   .StateDA(StateDA),
   .StateSA(StateSA),
   .StateLength(StateLength),
   .MRxDEq5(MRxDEq5),
   .MRxDEqD(MRxDEqD),
   .DlyCrcEn(DlyCrcEn),
   .DlyCrcCnt(DlyCrcCnt),
   .Transmitting(Transmitting),
   .MaxFL(MaxFL),
   .r_IFG(r_IFG),
   .HugEn(HugEn),
   .IFGCounterEq24(IFGCounterEq24),
   .ByteCntEq0(ByteCntEq0),
   .ByteCntEq1(ByteCntEq1),
   .ByteCntEq2(ByteCntEq2),
   .ByteCntEq3(ByteCntEq3),
   .ByteCntEq4(ByteCntEq4),
   .ByteCntEq5(ByteCntEq5),
   .ByteCntEq6(ByteCntEq6),
   .ByteCntEq7(ByteCntEq7),
   .ByteCntGreat2(ByteCntGreat2),
   .ByteCntSmall7(ByteCntSmall7),
   .ByteCntMaxFrame(ByteCntMaxFrame),
   .ByteCntOut(ByteCnt),
   .frame_ByteCnt(frame_ByteCnt),
   .Rx_NibCnt(Rx_NibCnt)
   );

// Rx Address Check

eth_rxaddrcheck rxaddrcheck1
  (.MRxClk(MRxClk),
   .Resetn( Resetn),
   .MRxD(MRxD),
   .LatchedByte(LatchedByte),
   .Rx_NibCnt(Rx_NibCnt),   
   .r_Bro (r_Bro),
   .r_Pro(r_Pro),
   .r_Iam(r_Iam),
   .ByteCntEq6(ByteCntEq6),
   .ByteCntEq7(ByteCntEq7),
   .ByteCntEq1(ByteCntEq1),
   .ByteCntEq2(ByteCntEq2),
   .ByteCntEq3(ByteCntEq3),
   .ByteCntEq4(ByteCntEq4),
   .ByteCntEq5(ByteCntEq5),
   .HASH0(r_HASH0),
   .HASH1(r_HASH1),
   .ByteCntEq0(ByteCntEq0),
   .CrcHash(CrcHash),
   .CrcHashGood(CrcHashGood),		
   .StateDA(StateDA),
   .StateSFD(StateSFD),
   .StateIdle(StateIdle),
   .StateDrop(StateDrop),
   .MAC(MAC),
   .Address_mismatch(Address_mismatch),
   .RxEndFrm(RxEndFrm),
   .AddressMiss(AddressMiss),
   .RxAddressInvalid(RxAddressInvalid),
   .PassAll(PassAll),
   .ControlFrmAddressOK(ControlFrmAddressOK)
   );
   
//Note: 1.Depending on any error of Frame below frame_error should be Generated.
//      2.And this signal should be high until end of the Frame.
//	    3.So that other logics(ex:fifo) should drop that Frame.    
//assign RxAbort = (endframe_d && AddressMiss) | rxabort_statedrop | Length_Vs_Payload_error;
assign RxAbort = (endframe_d1 && AddressMiss) | rxabort_statedrop | Length_Vs_Payload_error | (endframe_d1 && MRxErr_Detected);

assign Length_vs_payload_mismatch = (!shift8_py_gt_len_pad1_dat0_f5 && endframe_d);

assign Enable_Crc = (MRxDV & (StateDA | StateSA | StateLength |(|StateData & ~ByteCntMaxFrame))) |(~MRxDV & (|StateData & ~ByteCntMaxFrame)) ;		
assign Initialize_Crc = StateSFD | DlyCrcEn & (|DlyCrcCnt[3:0]) &
                        DlyCrcCnt[3:0] < 4'h9;


assign Data_Crc[0] = LatchedByte[7];	
assign Data_Crc[1] = LatchedByte[6];
assign Data_Crc[2] = LatchedByte[5];
assign Data_Crc[3] = LatchedByte[4];

// Connecting module Crc
eth_crc crcrx
  (.Clk(MRxClk),
   .Resetn(Resetn),
   .Data(Data_Crc),
   .Enable(Enable_Crc),
   .Initialize(Initialize_Crc), 
   .Crc(Crc),
   .CrcError(CrcError)
   );


// Latching CRC for use in the hash table
always @ (posedge MRxClk)
begin
  CrcHashGood <= CrcHashGood_next;  
end
always@(*)
begin
    CrcHashGood_next=(StateDA & Rx_NibCnt == 'd1) & ByteCntEq5; 
end
always @ (posedge MRxClk or negedge Resetn)
begin
  if(Resetn == 0 | StateIdle)
    CrcHash[5:0] <=  6'h0;
  else
     if(CrcHashGood_next)
          CrcHash[5:0] <=  Crc[31:26];
end

// Output byte stream
always @ (posedge MRxClk or negedge Resetn)
begin
  if(Resetn == 0)
    begin
      RxData_d[7:0]      <=  8'h0;
      DelayData          <=  1'b0;
      LatchedByte[7:0]   <=  8'h0;
      RxData[7:0]        <=  8'h0;
    end
  else
    begin 
      LatchedByte[7:0]   <=  {MRxD[3:0], LatchedByte[7:4]};
	  DelayData          <=  (StateDA & Rx_NibCnt == 'd1)|(StateSA & Rx_NibCnt == 'd1) | (StateLength & Rx_NibCnt == 'd1)|StateData[1];

      if(GenerateRxValid)
		//Data goes through DA,SA,Length and data States 
        RxData_d[7:0] <=  LatchedByte[7:0] & ({8{|StateData}} | {8{StateDA}} | {8{StateSA}} | {8{StateLength}});
      else
      if(~DelayData)
        // Delaying data to be valid for two cycles.
        // Zero when not active.
        RxData_d[7:0] <=  8'h0;

      RxData[7:0] <=  RxData_d[7:0];          // Output data byte
    end
end
//added code by Moschip Team on September 4th 2020

always @(posedge MRxClk or negedge Resetn)
begin
	if(Resetn == 0)
	begin
		MRxErr_Detected <= 0;
	end
	else if(RxEndFrm)
	begin
		MRxErr_Detected <= 0;
	end
	else 
	begin
		case(1)
			StateDA,StateSA,StateLength,StateData[0],StateData[1]:begin
																	if(MRxErr)
																		MRxErr_Detected <= 1;
																	else
																		MRxErr_Detected <= MRxErr_Detected;
																  end
		endcase
	end
end

//added code by Moschip Team on June 15th

always @(posedge MRxClk or negedge Resetn)
begin
	if(Resetn == 0)
	begin
		Frame_drop <= 0;
		Preamble_mismatch <= 0;
		SFD_mismatch <= 0;
	end
	else 
	begin 
		if(StateIdle)
		begin
			if(MRxDV)
			begin
				case(No_Preamble)
				0 : begin 
						if(MRxD != 'd5)
							begin
								Frame_drop <= 1;
								Preamble_mismatch <= 1;
							end
						else
							begin
								if(MRxErr == 1)
								begin
								Frame_drop <= 1;
								Preamble_mismatch <= 0;
								end
								else
								begin
								Frame_drop <= 0;
								Preamble_mismatch <= 0;
								end
							end
					end
				1: begin
						if(MRxD != 'd5)
						begin 
							Frame_drop <= 1;
							SFD_mismatch <= 1;
						end
						else
						begin
							if(MRxErr == 1)
							begin
							Frame_drop <= 1;
							SFD_mismatch <= 0;
							end
							else
							begin
							Frame_drop <= 0;
							SFD_mismatch <= 0;
							end
						end
				   end
				endcase
			end
			else
			begin
				Frame_drop <= 0;
				Preamble_mismatch <= 0;
				SFD_mismatch <= 0;
			end
		end
		else if(StatePreamble)
		begin
			if(LatchedByte[7:4] == 'd5)
			begin
				if(MRxErr)
				begin
				Frame_drop <= 1;
				Preamble_mismatch <= 0;
				end
				else
				begin
				Frame_drop <= 0;
				Preamble_mismatch <= 0;
				end
			end
			else
			begin
				Frame_drop <= 1;
				Preamble_mismatch <= 1;
			end
		end
		else 
			if(StateSFD)
			begin
				if((LatchedByte[7:4] == 'd5) & ByteCnt == 0)	
				begin
					if(MRxErr)
					begin
					Frame_drop <= 1;
					SFD_mismatch <= 0;
					end
					else
					begin
					Frame_drop <= 0;
					SFD_mismatch <= 0;
					end
				end
				else if((LatchedByte[7:4] == 'hd) & ByteCnt == 1)
				begin
					if(MRxErr)
					begin
					Frame_drop <= 1;
					SFD_mismatch <= 0;
					end
					else
					begin
					Frame_drop <= 0;
					SFD_mismatch <= 0;
					end
				end
				else 
				begin
					Frame_drop <= 1;
					SFD_mismatch <= 1;
				end
			end
		else 
		begin
			Frame_drop <= 0;
			Preamble_mismatch <= 0;
			SFD_mismatch <= 0;
		end
	end
end

assign GenerateRxValid = ((StateDA & Rx_NibCnt == 'd1)| (StateSA & Rx_NibCnt == 'd1) | (StateLength & Rx_NibCnt == 'd1)| StateData[1]);


always @ (posedge MRxClk or negedge Resetn)
begin
  if(Resetn == 0)
    begin
      RxValid_d1 <=  1'b0;
      RxValid   <=  1'b0;
    end
  else
    begin
      RxValid_d1 <=  GenerateRxValid;
      RxValid   <=  RxValid_d1;
	  
    end
end


assign GenerateRxStartFrm = (StateDA & Rx_NibCnt == 'd1) & ((ByteCntEq0 & ~DlyCrcEn)| ((DlyCrcCnt == 4'h3) & DlyCrcEn));	

always @ (posedge MRxClk or negedge Resetn)
begin
  if(Resetn == 0)
    begin
      RxStartFrm_d <=  1'b0;
      RxStartFrm   <=  1'b0;
    end
  else
    begin
      RxStartFrm_d <=  GenerateRxStartFrm;
      RxStartFrm   <=  RxStartFrm_d;
    end
end



assign GenerateRxEndFrm = StateData[1] &
                          (~MRxDV & ByteCntGreat2 | ByteCntMaxFrame);	

assign DribbleRxEndFrm  = StateData[0] &  ~MRxDV & ByteCntGreat2;


always @ (posedge MRxClk or negedge Resetn)
begin
  if(Resetn == 0)
    begin
      RxEndFrm_d1 <=  1'b0;
      RxEndFrm    <=  1'b0;
    end
  else
    begin
      RxEndFrm_d1 <=  GenerateRxEndFrm;
      RxEndFrm    <=  RxEndFrm_d1 | DribbleRxEndFrm;
    end
end

//Added by the Moschip team on June 1st 2020
reg [3:0] MRxD_d;
reg MRxDV_d;


always@(posedge MRxClk or negedge Resetn)
begin
	if(!Resetn)
		MRxD_d <= 0;
	else
	begin
		MRxD_d <= MRxD;
	end
end

always@(posedge MRxClk or negedge Resetn)
begin
	if(!Resetn)
		MRxDV_d <= 0;
	else
	begin
		MRxDV_d <= MRxDV;
	end
end

//added code by Moschip Team on June 8th
always @(posedge MRxClk or negedge Resetn)
begin
	if(Resetn == 0)
		Frame_Length <= 0;
	else
	begin
		if(StateLength)
		begin
			case(1)
			ByteCntEq0:begin   
						Frame_Length[15:8] <= {MRxD_d[3:0],Frame_Length[15:12]}; 
						end
			ByteCntEq1:begin   
						Frame_Length[7:0]  <= {MRxD_d[3:0],Frame_Length[7:4]}; 
					   end
			endcase
		end
	end
end

always @(posedge MRxClk or negedge Resetn)
begin
	if(Resetn == 0)
	begin
		payld_gt_maxfl_error <= 0;
	end
	else
	begin
		if(StateData)
		begin
			if((frame_ByteCnt + 1) > MaxFL)
			begin
				if(HugEn == 0)
				begin
					payld_gt_maxfl_error <= 1;
				end
				else
					payld_gt_maxfl_error <= 0;
			end
			else
				payld_gt_maxfl_error <= 0;
		end
		else
			payld_gt_maxfl_error <= 0;
	end
end


always@(posedge MRxClk or negedge Resetn)
begin
	if(Resetn == 0)
	begin
		py_gt_len_pad1_dat0 <= 1;
	end
	else
	begin
		if(StateData)
		begin
			if((ByteCnt > Frame_Length) && ByteCnt <= 'd46)
			begin
				if(Pad)
				begin
					case(StateData)
						2'b01:begin
								if(RxData_d[3:0] != 0)
								begin
									py_gt_len_pad1_dat0 <= 0;
								end
								else
								begin
									py_gt_len_pad1_dat0 <= py_gt_len_pad1_dat0 && 1'b1;
								end
							  end
						2'b10:begin
								if(RxData_d[7:4] != 0)
								begin
									py_gt_len_pad1_dat0 <= 0;
								end
								else
								begin
									py_gt_len_pad1_dat0 <= py_gt_len_pad1_dat0 && 1'b1;
								end
							  end
					endcase
				end
				else
					py_gt_len_pad1_dat0 <= 0;
			end
			else
			begin
				py_gt_len_pad1_dat0 <= 1; 
			end
		end
		else
			py_gt_len_pad1_dat0 <= 1; 
	end
end

always @(posedge MRxClk or negedge Resetn )
begin
    if(Resetn == 0) 
	begin 
		shift8_py_gt_len_pad1_dat0_f0 <= 1;
		shift8_py_gt_len_pad1_dat0_f1 <= 1;
		shift8_py_gt_len_pad1_dat0_f2 <= 1;
		shift8_py_gt_len_pad1_dat0_f3 <= 1;
		shift8_py_gt_len_pad1_dat0_f4 <= 1;
		shift8_py_gt_len_pad1_dat0_f5 <= 1;
		shift8_py_gt_len_pad1_dat0_f6 <= 1;
		shift8_py_gt_len_pad1_dat0_f7 <= 1;
	end
	else 
	begin
		shift8_py_gt_len_pad1_dat0_f0 <= py_gt_len_pad1_dat0;
		shift8_py_gt_len_pad1_dat0_f1 <= shift8_py_gt_len_pad1_dat0_f0;
		shift8_py_gt_len_pad1_dat0_f2 <= shift8_py_gt_len_pad1_dat0_f1;
		shift8_py_gt_len_pad1_dat0_f3 <= shift8_py_gt_len_pad1_dat0_f2;
		shift8_py_gt_len_pad1_dat0_f4 <= shift8_py_gt_len_pad1_dat0_f3;
		shift8_py_gt_len_pad1_dat0_f5 <= shift8_py_gt_len_pad1_dat0_f4;
		shift8_py_gt_len_pad1_dat0_f6 <= shift8_py_gt_len_pad1_dat0_f5;
		shift8_py_gt_len_pad1_dat0_f7 <= shift8_py_gt_len_pad1_dat0_f6;
	end
end
//

always@(posedge MRxClk or negedge Resetn)
begin
	if(Resetn == 0) endframe_d <= 1'b0;
	else if(StateData[1] && MRxDV == 0) endframe_d <= 1'b1;
	else endframe_d <= 1'b0;
end

always@(posedge MRxClk or negedge Resetn)
begin
	if(Resetn == 0) 
		endframe_d1 <= 1'b0;
	else
		endframe_d1 <= endframe_d;
end

//added code for length_vs_payload error
							
always@(posedge MRxClk or negedge Resetn)
begin
	if(Resetn == 0)
		Length_Vs_Payload_error <= 0;
	else
	begin
		if(endframe_d)
		begin
			case(1)
			(ByteCnt-4 == Frame_Length):begin
											if(CrcError == 0)
											begin
												if(frame_ByteCnt < r_MinFL)
												begin
													Length_Vs_Payload_error <= 1;		//drop frame
												end
												else if(frame_ByteCnt == r_MinFL)
												begin
													Length_Vs_Payload_error <= 0;	//accept frame
												end
												else if(frame_ByteCnt > r_MinFL)
												begin
													if(frame_ByteCnt <= MaxFL)	//FL <= MAXFL
													begin
														Length_Vs_Payload_error <= 0;	//accept frame
													end
													else if(frame_ByteCnt > MaxFL)
													begin
														if(HugEn == 0)
														begin
															Length_Vs_Payload_error <= 1; //drop frame
														end
														else
														begin
															Length_Vs_Payload_error <= 0;
														end
													end
												end
											end
											else
												Length_Vs_Payload_error <= 1;		//drop frame
									    end
			(ByteCnt-4 > Frame_Length):begin
											if(Pad)
											begin
												if(RxEndFrm_d1)
												begin
													if(shift8_py_gt_len_pad1_dat0_f5)	
													begin	
														if(CrcError)
															begin
															Length_Vs_Payload_error <= 1;		//drop frame
															end
														else
														begin
															if(frame_ByteCnt == r_MinFL)
															begin
																Length_Vs_Payload_error <= 0;
															end
															else
															begin
																Length_Vs_Payload_error <= 1;		//drop frame
															end
														end
													end
													else
														Length_Vs_Payload_error <= 1;		//drop frame
												end
												else
													Length_Vs_Payload_error <= 0;
											end
											else
												Length_Vs_Payload_error <= 1;		//drop frame
									   end
			(ByteCnt-4 < Frame_Length):begin
											Length_Vs_Payload_error <= 1;		//drop frame
									   end							
			endcase
		end	
		else
			Length_Vs_Payload_error <= 0;
	end
end	

endmodule


//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date:    17:40:26 06/07/2020 
// Design Name: 
// Module Name:    eth_rxstatem 
// Project Name: 
// Target Devices: 
// Tool versions: 
// Description: 
//
// Dependencies: 
//
// Revision: 
// Revision 0.01 - File Created
// Additional Comments: 
//
//////////////////////////////////////////////////////////////////////////////////
`include "timescale.v"
module eth_rxstatem (MRxClk, Resetn, MRxDV,No_Preamble, Rx_NibCnt,ByteCnt,Frame_drop, ByteCntEq0, ByteCntGreat2, Transmitting, MRxDEq5, MRxDEqD, 
                     IFGCounterEq24, ByteCntMaxFrame, StateData, StateIdle, StatePreamble, StateSFD, StateDA, StateSA,
					 StateLength, StateDrop, rxabort_statedrop
                    );

input         MRxClk;
input         Resetn;
input         MRxDV;
input 		  No_Preamble;
input 		  Rx_NibCnt;
input [15:0]  ByteCnt;
input 		  Frame_drop;
input         ByteCntEq0;
input         ByteCntGreat2;
input         MRxDEq5;
input         Transmitting;
input         MRxDEqD;
input         IFGCounterEq24;
input         ByteCntMaxFrame;

output [1:0]  StateData;
output        StateIdle;
output        StateDrop;
output        StatePreamble;
output        StateSFD;
output		  StateDA;
output		  StateSA;
output 		  StateLength;
reg [3:0] state_rx;
output reg rxabort_statedrop;
localparam STATE_DROP = 1,STATE_IDLE = 2, STATE_PREAMBLE = 3,STATE_SFD = 4, STATE_DA = 5, STATE_SA = 6,
		  STATE_LENGTH = 7, STATE_DATA0 = 8,STATE_DATA1 = 9;

wire           StateData0 	= (state_rx == STATE_DATA0);
wire           StateData1 	= (state_rx == STATE_DATA1);
wire           StateIdle  	= (state_rx == STATE_IDLE);
wire           StateDrop  	= (state_rx == STATE_DROP);
wire           StatePreamble= (state_rx == STATE_PREAMBLE);
wire           StateSFD		= (state_rx == STATE_SFD);
wire 		   StateDA		= (state_rx == STATE_DA);
wire 		   StateSA		= (state_rx == STATE_SA);
wire 		   StateLength	= (state_rx == STATE_LENGTH);


wire          StartIdle;
wire          StartDrop;
wire          StartData0;
wire          StartData1;
wire          StartPreamble;
reg           StartSFD;
wire 		  StartDA;
wire 		  StartSA;
wire 		  StartLength;

// Defining the next state
assign StartIdle = ~MRxDV & ((state_rx ==STATE_DROP) | (state_rx == STATE_PREAMBLE) | (state_rx == STATE_SFD) |(state_rx == STATE_DA)|(state_rx == STATE_SA)|(state_rx == STATE_LENGTH)|(|StateData))  ;

assign StartPreamble = MRxDV & MRxDEq5 & ((state_rx == STATE_IDLE) & ~Transmitting) & ~No_Preamble & IFGCounterEq24;

always@(*)
begin
	if(~No_Preamble)
		StartSFD = MRxDV &((state_rx == STATE_PREAMBLE)& ByteCnt == 'd13);
	else
		StartSFD = MRxDV & MRxDEq5 & ((state_rx == STATE_IDLE) & ~Transmitting) & IFGCounterEq24; 
end

assign StartDA = MRxDV & ((state_rx == STATE_SFD)& ByteCnt == 1);

assign StartSA = MRxDV & ((state_rx == STATE_DA) & ByteCnt == 'd5 & Rx_NibCnt == 'd1);

assign StartLength = MRxDV & ((state_rx == STATE_SA) & Rx_NibCnt == 'd1 & ByteCnt == 'd5);

assign StartData0 = MRxDV & (((state_rx == STATE_LENGTH) & Rx_NibCnt == 'd1 & ByteCnt == 'd1)| (state_rx ==STATE_DATA1));

assign StartData1 = MRxDV & (state_rx == STATE_DATA0) & (~ByteCntMaxFrame);

				  
//Before StateSFD(5d) we are checking Interframegap. 
assign StartDrop = MRxDV & ((state_rx == STATE_IDLE) & Transmitting | (state_rx == STATE_IDLE | state_rx == STATE_PREAMBLE)& ~IFGCounterEq24 &
                  MRxDEqD | (state_rx == STATE_DATA0) &  ByteCntMaxFrame | Frame_drop);

//RX state machine

always@(posedge MRxClk or negedge Resetn)
begin
  if(Resetn == 0)
    begin	
		state_rx <= STATE_DROP;
		rxabort_statedrop <= 1'b0;
	end
  else
  begin
	case(state_rx)
	STATE_DROP : begin	
						rxabort_statedrop <= 1'b0;
					if(StartIdle) begin
						state_rx <= STATE_IDLE;
						end
				  end
	STATE_IDLE : begin
					if(StartDrop)
						state_rx <= STATE_DROP;
					else
					begin
						if(StartPreamble)
							state_rx <= STATE_PREAMBLE;
						else
							if(StartSFD)
								state_rx <= STATE_SFD;
					end
				 end
	STATE_PREAMBLE: begin
						if(StartDrop) begin
							state_rx <= STATE_DROP;
							rxabort_statedrop <= 1'b1;
							end
						else
						begin
							if(StartIdle) 
								state_rx <= STATE_IDLE;
							else
								if(StartSFD)
									state_rx <= STATE_SFD;
						end
					end
	STATE_SFD : begin
					if(StartDrop)
						state_rx <= STATE_DROP;
					else
					begin
						if(StartIdle)
							state_rx <= STATE_IDLE;
						else
						begin
							if(StartDA)
								state_rx <= STATE_DA;
						end
					end
				end
	STATE_DA : begin
				if(StartDrop)
						state_rx <= STATE_DROP;
				else
				begin
					if(StartSA)
						state_rx <= STATE_SA;
				end
			   end
	STATE_SA : begin
				if(StartDrop)
						state_rx <= STATE_DROP;
				else
				begin
					if(StartLength)
						state_rx <= STATE_LENGTH;
				end
			   end
	STATE_LENGTH : begin
					if(StartDrop)
						state_rx <= STATE_DROP;
					else
					begin
					  if(StartData0)
						state_rx <= STATE_DATA0;
					end
				   end
	STATE_DATA0 : begin
					if(StartDrop)
						state_rx <= STATE_DROP;
					else
					begin
						if(StartIdle)
							state_rx <= STATE_IDLE;
						else 
							if(StartData1)
							state_rx <= STATE_DATA1;
					end
				  end
	STATE_DATA1: begin
					if(StartIdle)
						state_rx <= STATE_IDLE;
					else
						if(StartData0)
							state_rx <= STATE_DATA0;
				 end
	endcase
  end
end

assign StateData[1:0] = {(state_rx == STATE_DATA1), (state_rx == STATE_DATA0)};


endmodule


//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date:    17:40:26 06/07/2020 
// Design Name: 
// Module Name:    eth_rxstatem 
// Project Name: 
// Target Devices: 
// Tool versions: 
// Description: 
//
// Dependencies: 
//
// Revision: 
// Revision 0.01 - File Created
// Additional Comments: 
//
//////////////////////////////////////////////////////////////////////////////////
`include "timescale.v"
module eth_rxstatem (MRxClk, Resetn, MRxDV,No_Preamble, Rx_NibCnt,ByteCnt,Frame_drop, ByteCntEq0, ByteCntGreat2, Transmitting, MRxDEq5, MRxDEqD, 
                     IFGCounterEq24, ByteCntMaxFrame, StateData, StateIdle, StatePreamble, StateSFD, StateDA, StateSA,
					 StateLength, StateDrop, rxabort_statedrop
                    );

input         MRxClk;
input         Resetn;
input         MRxDV;
input 		  No_Preamble;
input 		  Rx_NibCnt;
input [15:0]  ByteCnt;
input 		  Frame_drop;
input         ByteCntEq0;
input         ByteCntGreat2;
input         MRxDEq5;
input         Transmitting;
input         MRxDEqD;
input         IFGCounterEq24;
input         ByteCntMaxFrame;

output [1:0]  StateData;
output        StateIdle;
output        StateDrop;
output        StatePreamble;
output        StateSFD;
output		  StateDA;
output		  StateSA;
output 		  StateLength;
reg [3:0] state_rx;
output reg rxabort_statedrop;
localparam STATE_DROP = 1,STATE_IDLE = 2, STATE_PREAMBLE = 3,STATE_SFD = 4, STATE_DA = 5, STATE_SA = 6,
		  STATE_LENGTH = 7, STATE_DATA0 = 8,STATE_DATA1 = 9;

wire           StateData0 	= (state_rx == STATE_DATA0);
wire           StateData1 	= (state_rx == STATE_DATA1);
wire           StateIdle  	= (state_rx == STATE_IDLE);
wire           StateDrop  	= (state_rx == STATE_DROP);
wire           StatePreamble= (state_rx == STATE_PREAMBLE);
wire           StateSFD		= (state_rx == STATE_SFD);
wire 		   StateDA		= (state_rx == STATE_DA);
wire 		   StateSA		= (state_rx == STATE_SA);
wire 		   StateLength	= (state_rx == STATE_LENGTH);


wire          StartIdle;
wire          StartDrop;
wire          StartData0;
wire          StartData1;
wire          StartPreamble;
reg           StartSFD;
wire 		  StartDA;
wire 		  StartSA;
wire 		  StartLength;

// Defining the next state
assign StartIdle = ~MRxDV & ((state_rx ==STATE_DROP) | (state_rx == STATE_PREAMBLE) | (state_rx == STATE_SFD) |(state_rx == STATE_DA)|(state_rx == STATE_SA)|(state_rx == STATE_LENGTH)|(|StateData))  ;

assign StartPreamble = MRxDV & MRxDEq5 & ((state_rx == STATE_IDLE) & ~Transmitting) & ~No_Preamble & IFGCounterEq24;

always@(*)
begin
	if(~No_Preamble)
		StartSFD = MRxDV &((state_rx == STATE_PREAMBLE)& ByteCnt == 'd13);
	else
		StartSFD = MRxDV & MRxDEq5 & ((state_rx == STATE_IDLE) & ~Transmitting) & IFGCounterEq24; 
end

assign StartDA = MRxDV & ((state_rx == STATE_SFD)& ByteCnt == 1);

assign StartSA = MRxDV & ((state_rx == STATE_DA) & ByteCnt == 'd5 & Rx_NibCnt == 'd1);

assign StartLength = MRxDV & ((state_rx == STATE_SA) & Rx_NibCnt == 'd1 & ByteCnt == 'd5);

assign StartData0 = MRxDV & (((state_rx == STATE_LENGTH) & Rx_NibCnt == 'd1 & ByteCnt == 'd1)| (state_rx ==STATE_DATA1));

assign StartData1 = MRxDV & (state_rx == STATE_DATA0) & (~ByteCntMaxFrame);

				  
//Before StateSFD(5d) we are checking Interframegap. 
assign StartDrop = MRxDV & ((state_rx == STATE_IDLE) & Transmitting | (state_rx == STATE_IDLE | state_rx == STATE_PREAMBLE)& ~IFGCounterEq24 &
                  MRxDEqD | (state_rx == STATE_DATA0) &  ByteCntMaxFrame | Frame_drop);

//RX state machine

always@(posedge MRxClk or negedge Resetn)
begin
  if(Resetn == 0)
    begin	
		state_rx <= STATE_DROP;
		rxabort_statedrop <= 1'b0;
	end
  else
  begin
	case(state_rx)
	STATE_DROP : begin	
						rxabort_statedrop <= 1'b0;
					if(StartIdle) begin
						state_rx <= STATE_IDLE;
						end
				  end
	STATE_IDLE : begin
					if(StartDrop)
						state_rx <= STATE_DROP;
					else
					begin
						if(StartPreamble)
							state_rx <= STATE_PREAMBLE;
						else
							if(StartSFD)
								state_rx <= STATE_SFD;
					end
				 end
	STATE_PREAMBLE: begin
						if(StartDrop) begin
							state_rx <= STATE_DROP;
							rxabort_statedrop <= 1'b1;
							end
						else
						begin
							if(StartIdle) 
								state_rx <= STATE_IDLE;
							else
								if(StartSFD)
									state_rx <= STATE_SFD;
						end
					end
	STATE_SFD : begin
					if(StartDrop)
						state_rx <= STATE_DROP;
					else
					begin
						if(StartIdle)
							state_rx <= STATE_IDLE;
						else
						begin
							if(StartDA)
								state_rx <= STATE_DA;
						end
					end
				end
	STATE_DA : begin
				if(StartDrop)
						state_rx <= STATE_DROP;
				else
				begin
					if(StartSA)
						state_rx <= STATE_SA;
				end
			   end
	STATE_SA : begin
				if(StartDrop)
						state_rx <= STATE_DROP;
				else
				begin
					if(StartLength)
						state_rx <= STATE_LENGTH;
				end
			   end
	STATE_LENGTH : begin
					if(StartDrop)
						state_rx <= STATE_DROP;
					else
					begin
					  if(StartData0)
						state_rx <= STATE_DATA0;
					end
				   end
	STATE_DATA0 : begin
					if(StartDrop)
						state_rx <= STATE_DROP;
					else
					begin
						if(StartIdle)
							state_rx <= STATE_IDLE;
						else 
							if(StartData1)
							state_rx <= STATE_DATA1;
					end
				  end
	STATE_DATA1: begin
					if(StartIdle)
						state_rx <= STATE_IDLE;
					else
						if(StartData0)
							state_rx <= STATE_DATA0;
				 end
	endcase
  end
end

assign StateData[1:0] = {(state_rx == STATE_DATA1), (state_rx == STATE_DATA0)};


endmodule


//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date:    17:40:52 06/07/2020 
// Design Name: 
// Module Name:    eth_shiftreg 
// Project Name: 
// Target Devices: 
// Tool versions: 
// Description: 
//
// Dependencies: 
//
// Revision: 
// Revision 0.01 - File Created
// Additional Comments: 
//
//////////////////////////////////////////////////////////////////////////////////
`include "timescale.v"
module eth_shiftreg(Clk, Resetn, MdcEn_n, Mdi, Fiad, Rgad, CtrlData, WriteOp, ByteSelect, 
                    LatchByte, ShiftedBit, Prsd, LinkFail);


input       Clk;              // Input clock (Host clock)
input       Resetn;            // Resetn signal
input       MdcEn_n;          // Enable signal is asserted for one Clk period before Mdc falls.
input       Mdi;              // MII input data
input [4:0] Fiad;             // PHY address
input [4:0] Rgad;             // Register address (within the selected PHY)
input [15:0]CtrlData;         // Control data (data to be written to the PHY)
input       WriteOp;          // The current operation is a PHY register write operation
input [3:0] ByteSelect;       // Byte select
input [1:0] LatchByte;        // Byte select for latching (read operation)

output      ShiftedBit;       // Bit shifted out of the shift register
output[15:0]Prsd;             // Read Status Data (data read from the PHY)
output      LinkFail;         // Link Integrity Signal

reg   [7:0] ShiftReg;         // Shift register for shifting the data in and out
reg   [15:0]Prsd;
reg         LinkFail;




// ShiftReg[7:0] :: Shift Register Data
always @ (posedge Clk or negedge Resetn) 
begin
  if(Resetn == 0)
    begin
      ShiftReg[7:0] <=  8'h0;
      Prsd[15:0] <=  16'h0;
      LinkFail <=  1'b0;
    end
  else
    begin
      if(MdcEn_n)
        begin 
          if(|ByteSelect)
            begin
	       /* verilator lint_off CASEINCOMPLETE */
              case (ByteSelect[3:0])  // synopsys parallel_case full_case
                4'h1 :    ShiftReg[7:0] <=  {2'b01, ~WriteOp, WriteOp, Fiad[4:1]};
                4'h2 :    ShiftReg[7:0] <=  {Fiad[0], Rgad[4:0], 2'b10};
                4'h4 :    ShiftReg[7:0] <=  CtrlData[15:8];
                4'h8 :    ShiftReg[7:0] <=  CtrlData[7:0];
              endcase // case (ByteSelect[3:0])
	       /* verilator lint_on CASEINCOMPLETE */
            end 
          else
            begin
              ShiftReg[7:0] <=  {ShiftReg[6:0], Mdi};
              if(LatchByte[0])
                begin
                  Prsd[7:0] <=  {ShiftReg[6:0], Mdi};
                  if(Rgad == 5'h01)
                    LinkFail <=  ~ShiftReg[1];  // this is bit [2], because it is not shifted yet
                end
              else
                begin
                  if(LatchByte[1])
                    Prsd[15:8] <=  {ShiftReg[6:0], Mdi};
                end
            end
        end
    end
end


assign ShiftedBit = ShiftReg[7];


endmodule


//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date:    17:41:24 06/07/2020 
// Design Name: 
// Module Name:    eth_spram_256x32 
// Project Name: 
// Target Devices: 
// Tool versions: 
// Description: 
//
// Dependencies: 
//
// Revision: 
// Revision 0.01 - File Created
// Additional Comments: 
//
//////////////////////////////////////////////////////////////////////////////////

`include "ethmac_defines.v"
`include "timescale.v"
module eth_spram_256x32(
	// Generic synchronous single-port RAM interface
	clk, rstn, ce, we, oe, addr, di, dato

`ifdef ETH_BIST
  ,
  // debug chain signals
  mbist_si_i,       // bist scan serial in
  mbist_so_o,       // bist scan serial out
  mbist_ctrl_i        // bist chain shift control
`endif



);

   //
   // Generic synchronous single-port RAM interface
   //
   input           clk;  // Clock, rising edge
   input           rstn;  // Reset, active high
   input           ce;   // Chip enable input, active high
   input  [3:0]    we;   // Write enable input, active high
   input           oe;   // Output enable input, active high
   input  [7:0]    addr; // address bus inputs
   input  [31:0]   di;   // input data bus
   output [31:0]   dato;   // output data bus

`ifdef ETH_BIST
   input           mbist_si_i;       // bist scan serial in
   output          mbist_so_o;       // bist scan serial out
   input [`ETH_MBIST_CTRL_WIDTH - 1:0] mbist_ctrl_i;       // bist chain shift control
`endif

`ifdef ETH_XILINX_RAMB4

   /*RAMB4_S16 ram0
    (
    .DO      (do[15:0]),
    .ADDR    (addr),
    .DI      (di[15:0]),
    .EN      (ce),
    .CLK     (clk),
    .WE      (we),
    .RST     (rstn)
    );

    RAMB4_S16 ram1
    (
    .DO      (do[31:16]),
    .ADDR    (addr),
    .DI      (di[31:16]),
    .EN      (ce),
    .CLK     (clk),
    .WE      (we),
    .RST     (rstn)
    );*/

   RAMB4_S8 ram0
     (
      .DO      (dato[7:0]),
      .ADDR    ({1'b0, addr}),
      .DI      (di[7:0]),
      .EN      (ce),
      .CLK     (clk),
      .WE      (we[0]),
      .RST     (rstn)
      );

   RAMB4_S8 ram1
     (
      .DO      (dato[15:8]),
      .ADDR    ({1'b0, addr}),
      .DI      (di[15:8]),
      .EN      (ce),
      .CLK     (clk),
      .WE      (we[1]),
      .RST     (rstn)
      );

   RAMB4_S8 ram2
     (
      .DO      (dato[23:16]),
      .ADDR    ({1'b0, addr}),
      .DI      (di[23:16]),
      .EN      (ce),
      .CLK     (clk),
      .WE      (we[2]),
      .RST     (rstn)
      );

   RAMB4_S8 ram3
     (
      .DO      (dato[31:24]),
      .ADDR    ({1'b0, addr}),
      .DI      (di[31:24]),
      .EN      (ce),
      .CLK     (clk),
      .WE      (we[3]),
      .RST     (rstn)
      );

`else   // !ETH_XILINX_RAMB4
 `ifdef  ETH_VIRTUAL_SILICON_RAM
  `ifdef ETH_BIST
   //vs_hdsp_256x32_bist ram0_bist
   vs_hdsp_256x32_bw_bist ram0_bist
  `else
     //vs_hdsp_256x32 ram0
     vs_hdsp_256x32_bw ram0
  `endif
       (
        .CK         (clk),
        .CEN        (!ce),
        .WEN        (~we),
        .OEN        (!oe),
        .ADR        (addr),
        .DI         (di),
        .DOUT       (dato)

  `ifdef ETH_BIST
        ,
        // debug chain signals
        .mbist_si_i       (mbist_si_i),
        .mbist_so_o       (mbist_so_o),
        .mbist_ctrl_i       (mbist_ctrl_i)
  `endif
       );

 `else   // !ETH_VIRTUAL_SILICON_RAM

  `ifdef  ETH_ARTISAN_RAM
   `ifdef ETH_BIST
   //art_hssp_256x32_bist ram0_bist
   art_hssp_256x32_bw_bist ram0_bist
   `else
     //art_hssp_256x32 ram0
     art_hssp_256x32_bw ram0
   `endif
       (
        .CLK        (clk),
        .CEN        (!ce),
        .WEN        (~we),
        .OEN        (!oe),
        .A          (addr),
        .D          (di),
        .Q          (dato)

   `ifdef ETH_BIST
        ,
        // debug chain signals
        .mbist_si_i       (mbist_si_i),
        .mbist_so_o       (mbist_so_o),
        .mbist_ctrl_i     (mbist_ctrl_i)
   `endif
       );

  `else   // !ETH_ARTISAN_RAM
   `ifdef ETH_ALTERA_ALTSYNCRAM

   altera_spram_256x32	altera_spram_256x32_inst
     (
      .address        (addr),
      .wren           (ce & we),
      .clock          (clk),
      .data           (di),
      .q              (dato)
      );  //exemplar attribute altera_spram_256x32_inst NOOPT TRUE

   `else   // !ETH_ALTERA_ALTSYNCRAM


   //
   // Generic single-port synchronous RAM model
   //

   //
   // Generic RAM's registers and wires
   //
   reg  [ 7: 0] mem0 [255:0]; // RAM content
   reg  [15: 8] mem1 [255:0]; // RAM content
   reg  [23:16] mem2 [255:0]; // RAM content
   reg  [31:24] mem3 [255:0]; // RAM content
   wire [31:0]  q;            // RAM output
   reg   [7:0]   raddr;        // RAM read address
   //
   // Data output drivers
   //
   assign dato = (oe & ce) ? q : {32{1'bz}};

   //
   // RAM read and write
   //

   // read operation
   always@(posedge clk)
     if (ce)
       raddr <=  addr; // read address needs to be registered to read clock

   assign  q = (rstn == 0) ? {32{1'b0}} : {mem3[raddr],
                                   mem2[raddr],
                                   mem1[raddr],
                                   mem0[raddr]};

    // write operation
    always@(posedge clk)
    begin
		if (ce && we[3])
		  mem3[addr] <=  di[31:24];
		if (ce && we[2])
		  mem2[addr] <=  di[23:16];
		if (ce && we[1])
		  mem1[addr] <=  di[15: 8];
		if (ce && we[0])
		  mem0[addr] <=  di[ 7: 0];
	     end

   // Task prints range of memory
   // *** Remember that tasks are non reentrant, don't call this task in parallel for multiple instantiations. 
   task print_ram;
      input [7:0] start;
      input [7:0] finish;
      integer     rnum;
      begin
    	 for (rnum={24'd0,start};rnum<={24'd0,finish};rnum=rnum+1)
           $display("Addr %h = %0h %0h %0h %0h",rnum,mem3[rnum],mem2[rnum],mem1[rnum],mem0[rnum]);
      end
   endtask

   `endif  // !ETH_ALTERA_ALTSYNCRAM
  `endif  // !ETH_ARTISAN_RAM
 `endif  // !ETH_VIRTUAL_SILICON_RAM
`endif  // !ETH_XILINX_RAMB4

endmodule


//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date:    18:22:45 06/07/2020 
// Design Name: 
// Module Name:    eth_top 
// Project Name: 
// Target Devices: 
// Tool versions: 
// Description: 
//
// Dependencies: 
//
// Revision: 
// Revision 0.01 - File Created
// Additional Comments: 
//
//////////////////////////////////////////////////////////////////////////////////
`include "ethmac_defines.v"
`include "timescale.v"
`include "eth_miim.v"
`include "apb_BDs_bridge.v"
`include "eth_clockgen.v"
`include "eth_crc.v"
`include "eth_fifo.v"
`include "eth_maccontrol.v"
`include "eth_macstatus.v"
`include "eth_outputcontrol.v"
`include "eth_random.v"
`include "eth_receivecontrol.v"
`include "eth_register.v"
`include "eth_registers.v"
`include "eth_rxaddrcheck.v"
`include "eth_rxcounters.v"
`include "eth_rxethmac.v"
`include "eth_rxstatem.v"
`include "eth_shiftreg.v"
`include "eth_spram_256x32.v"
`include "eth_transmitcontrol.v"
`include "eth_txcounters.v"
`include "eth_txethmac.v"
`include "eth_txstatem.v"
`include "eth_wishbone.v"

module eth_top
(
  // APB common
  pclk_i, prstn_i, pwdata_i, prdata_o, 

  // APB slave
  paddr_i, psel_i, pwrite_i, penable_i, pready_o, 

  // APB master
  m_paddr_o, m_psel_o, m_pwrite_o, 
  m_pwdata_o, m_prdata_i, m_penable_o, 
  m_pready_i,  

  int_o,
`ifdef ETH_WISHBONE_B3
  m_wb_cti_o, m_wb_bte_o, 
`endif

  //TX
  mtx_clk_pad_i, mtxd_pad_o, mtxen_pad_o, mtxerr_pad_o,

  //RX
  mrx_clk_pad_i, mrxd_pad_i, mrxdv_pad_i, mrxerr_pad_i, mcrs_pad_i 
  `ifdef ETH_COLL
	,mcoll_pad_i 
  `endif
  // MIIM
  `ifdef ETH_MIIM
    ,mdc_pad_o, md_pad_i, md_pad_o, md_padoe_o
  `endif

  // Bist
`ifdef ETH_BIST
  
  // debug chain signals
  ,mbist_si_i,       // bist scan serial in
  mbist_so_o,       // bist scan serial out
  mbist_ctrl_i        // bist chain shift control
`endif

);


parameter TX_FIFO_DATA_WIDTH = `ETH_TX_FIFO_DATA_WIDTH;
parameter TX_FIFO_DEPTH      = `ETH_TX_FIFO_DEPTH;
parameter TX_FIFO_CNT_WIDTH  = `ETH_TX_FIFO_CNT_WIDTH;
parameter RX_FIFO_DATA_WIDTH = `ETH_RX_FIFO_DATA_WIDTH;
parameter RX_FIFO_DEPTH      = `ETH_RX_FIFO_DEPTH;
parameter RX_FIFO_CNT_WIDTH  = `ETH_RX_FIFO_CNT_WIDTH;


// APB common
input           pclk_i;     // APB clock
input           prstn_i;     // APB reset
input   [31:0]  pwdata_i;     // APB data input
output  [31:0]  prdata_o;     // APB data output
wire          pslverr;     // APB slave error output

// APB slave
input   [31:0]  paddr_i;     // APB address input
input      		psel_i;     // APB slave select input
wire 	[3:0]	pstb_i = 4'b1111; //apb_byte select input
input           pwrite_i;      // APB write enable input
input           penable_i;     // APB enable input
output          pready_o;     // APB ready output

// APB master
output  [31:0]  m_paddr_o;
output   		m_psel_o;
output          m_pwrite_o;
input   [31:0]  m_prdata_i;
output  [31:0]  m_pwdata_o;
output          m_penable_o;
input           m_pready_i;
wire           m_perr_i = 0;
output 			int_o;
wire    [29:0]  m_wb_adr_tmp;

`ifdef ETH_WISHBONE_B3
output   [2:0]  m_wb_cti_o;   // Cycle Type Identifier
output   [1:0]  m_wb_bte_o;   // Burst Type Extension
`endif

// Tx
input           mtx_clk_pad_i; // Transmit clock (from PHY)
output   [3:0]  mtxd_pad_o;    // Transmit nibble (to PHY)
output          mtxen_pad_o;   // Transmit enable (to PHY)
output          mtxerr_pad_o;  // Transmit error (to PHY)

// Rx
input           mrx_clk_pad_i; // Receive clock (from PHY)
input    [3:0]  mrxd_pad_i;    // Receive nibble (from PHY)
input           mrxdv_pad_i;   // Receive data valid (from PHY)
input           mrxerr_pad_i;  // Receive data error (from PHY)
input           mcrs_pad_i;    // Carrier sense (from PHY)
// Common Tx and Rx
`ifdef ETH_COLL
input          mcoll_pad_i;   // Collision (from PHY)
`else
wire          mcoll_pad_i = 0;   // Collision (from PHY)
`endif
// MII Management interface
`ifdef ETH_MIIM
input           md_pad_i;      // MII data input (from I/O cell)
output          mdc_pad_o;     // MII Management data clock (to PHY)
output          md_pad_o;      // MII data output (to I/O cell)
output        md_padoe_o;    // MII data output enable (to I/O cell)
`else
wire           md_pad_i = 0;      // MII data input (from I/O cell)
wire          mdc_pad_o;     // MII Management data clock (to PHY)
wire          md_pad_o;      // MII data output (to I/O cell)
wire          md_padoe_o;    // MII data output enable (to I/O cell)
`endif
wire         int_o;         // Interrupt output

// Bist
`ifdef ETH_BIST
input   mbist_si_i;       // bist scan serial in
output  mbist_so_o;       // bist scan serial out
input [`ETH_MBIST_CTRL_WIDTH - 1:0] mbist_ctrl_i;       // bist chain shift control
`endif

wire    [31:0]  wb_dbg_dat0;

wire     [7:0]  r_ClkDiv;
wire            r_MiiNoPre;
wire    [15:0]  r_CtrlData;
wire     [4:0]  r_FIAD;
wire     [4:0]  r_RGAD;
wire            r_WCtrlData;
wire            r_RStat;
wire            r_ScanStat;
wire            NValid_stat;
wire            Busy_stat;
wire            LinkFail;
wire    [15:0]  Prsd;             // Read Status Data (data read from the PHY)
wire            WCtrlDataStart;
wire            RStatStart;
wire            UpdateMIIRX_DATAReg;

wire            TxStartFrm;
wire            TxEndFrm;
wire            TxUsedData;
wire     [7:0]  TxData;
wire            TxRetry;
wire            TxAbort;
wire            TxUnderRun;
wire            TxDone;


reg             WillSendControlFrame_sync1;
reg             WillSendControlFrame_sync2;
reg             WillSendControlFrame_sync3;
reg             RstTxPauseRq;

reg             TxPauseRq_sync1;
reg             TxPauseRq_sync2;
reg             TxPauseRq_sync3;
reg             TPauseRq;


initial
begin
  $display("          *********************************************");
  $display("          =============================================");
  $display("          eth_top.v will be removed shortly.");
  $display("          Please use ethmac.v as top level file instead");
  $display("          =============================================");
  $display("          *********************************************");
end
// Connecting Miim module
eth_miim miim1
(
  .Clk(pclk_i),
  .Resetn(prstn_i),
  .Divider(r_ClkDiv),
  .NoPre(r_MiiNoPre),
  .CtrlData(r_CtrlData),
  .Rgad(r_RGAD),
  .Fiad(r_FIAD),
  .WCtrlData(r_WCtrlData),
  .RStat(r_RStat),
  .ScanStat(r_ScanStat),
  .Mdi(md_pad_i),
  .Mdo(md_pad_o),
  .MdoEn(md_padoe_o),
  .Mdc(mdc_pad_o),
  .Busy(Busy_stat),
  .Prsd(Prsd),
  .LinkFail(LinkFail),
  .Nvalid(NValid_stat),
  .WCtrlDataStart(WCtrlDataStart),
  .RStatStart(RStatStart),
  .UpdateMIIRX_DATAReg(UpdateMIIRX_DATAReg)
);




wire  [3:0] RegCs;          // Connected to registers
wire [31:0] RegDataOut;     // Multiplexed to prdata_o
wire        r_RecSmall;     // Receive small frames
wire        r_LoopBck;      // Loopback
wire        r_TxEn;         // Tx Enable
wire        r_RxEn;         // Rx Enable
wire [15:0]	BD_TxLength;		// Buffer descriptor length
wire 		MRxClk_Lb;		//Muxed MRxClk
wire        MRxDV_Lb;       // Muxed MII receive data valid
wire        MRxErr_Lb;      // Muxed MII Receive Error
wire  [3:0] MRxD_Lb;        // Muxed MII Receive Data
wire        Transmitting;   // Indication that TxEthMAC is transmitting
wire        r_HugEn;        // Huge packet enable
wire        r_DlyCrcEn;     // Delayed CRC enabled
wire [15:0] r_MaxFL;        // Maximum frame length

wire [15:0] r_MinFL;        // Minimum frame length
wire        ShortFrame;
wire        DribbleNibble;  // Extra nibble received
wire        ReceivedPacketTooBig; // Received packet is too big
wire [47:0] r_MAC;          // MAC address
wire        LoadRxStatus;   // Rx status was loaded
wire [31:0] r_HASH0;        // HASH table, lower 4 bytes
wire [31:0] r_HASH1;        // HASH table, upper 4 bytes
wire  [7:0] r_TxBDNum;      // Receive buffer descriptor number
wire  [6:0] r_IPGT;         // 
wire  [6:0] r_IPGR1;        // 
wire  [6:0] r_IPGR2;        // 
wire  [5:0] r_CollValid;    // 
wire [15:0] r_TxPauseTV;    // Transmit PAUSE value
wire        r_TxPauseRq;    // Transmit PAUSE request

wire  [3:0] r_MaxRet;       //
wire        r_NoBckof;      // 
wire        r_ExDfrEn;      // 
wire        r_TxFlow;       // Tx flow control enable
wire        r_IFG;          // Minimum interframe gap for incoming packets

wire        TxB_IRQ;        // Interrupt Tx Buffer
wire        TxE_IRQ;        // Interrupt Tx Error
wire        RxB_IRQ;        // Interrupt Rx Buffer
wire        RxE_IRQ;        // Interrupt Rx Error
wire        Busy_IRQ;       // Interrupt Busy (lack of buffers)

wire        ByteSelected;
wire        BDAck;
wire [31:0] BD_prdata_o;    // prdata_o that comes from the Wishbone module
                            //(for buffer descriptors read/write)
wire  [3:0] BDCs;           // Buffer descriptor CS
wire        CsMiss;         // When access to the address between 0x800
                            // and 0xfff occurs, acknowledge is set
                            // but data is not valid.
wire        r_Pad;
wire        r_CrcEn;
wire        r_FullD;
wire        r_Pro;
wire        r_Bro;
wire 		r_Iam;
wire        r_NoPre;
wire        r_RxFlow;
wire        r_PassAll;
wire        TxCtrlEndFrm;
wire        StartTxDone;
wire        SetPauseTimer;
wire        TxUsedDataIn;
wire        TxDoneIn;
wire        TxAbortIn;
wire        PerPacketPad;
wire        PadOut;
wire        PerPacketCrcEn;
wire        CrcEnOut;
wire        TxStartFrmOut;
wire        TxEndFrmOut;
wire        ReceivedPauseFrm;
wire        ControlFrmAddressOK;
wire        RxStatusWriteLatched_sync2;
wire        LateCollision;
wire        DeferIndication;
wire        LateCollLatched;
wire        DeferLatched;
wire        RstDeferLatched;
wire        CarrierSenseLost;
wire 		Length_Vs_Payload_error;
wire 		Length_vs_payload_mismatch;
wire 		MRxErr_Detected;
wire        temp_pready_o;
reg [31:0] temp_prdata_o;
reg       temp_perr_o;

`ifdef ETH_REGISTERED_OUTPUTS
  reg         temp_pready_o_reg;
  reg [31:0]  temp_prdata_o_reg;
  reg         temp_perr_o_reg;
`endif


wire wb_psel_o;
wire wb_penable_o;
wire wb_pwrite_o;
wire [31:0]wb_pwdata_o;
wire [31:0]wb_paddr_o;
wire apb_bd_bridge_pready_o;
wire [31:0]apb_bd_bridge_prdata_o;


assign ByteSelected = psel_i;
assign RegCs[3] =  psel_i &  penable_i & ByteSelected & ~paddr_i[11] & ~paddr_i[10] & pstb_i[3];   // 0x0   - 0x3FF
assign RegCs[2] =  psel_i & penable_i & ByteSelected & ~paddr_i[11] & ~paddr_i[10] & pstb_i[2];   // 0x0   - 0x3FF
assign RegCs[1] =  psel_i & penable_i & ByteSelected & ~paddr_i[11] & ~paddr_i[10] & pstb_i[1];   // 0x0   - 0x3FF
assign RegCs[0] =  psel_i & penable_i & ByteSelected & ~paddr_i[11] & ~paddr_i[10] & pstb_i[0];   // 0x0   - 0x3FF

assign BDCs[3]  =  wb_psel_o & wb_penable_o & ~wb_paddr_o[11] &  wb_paddr_o[10] & pstb_i[3];   // 0x400 - 0x7FF	// 0100_0000_0000	0111_1111_1111
assign BDCs[2]  =  wb_psel_o & wb_penable_o & ~wb_paddr_o[11] &  wb_paddr_o[10] & pstb_i[2];   // 0x400 - 0x7FF
assign BDCs[1]  =  wb_psel_o & wb_penable_o & ~wb_paddr_o[11] &  wb_paddr_o[10] & pstb_i[1];   // 0x400 - 0x7FF
assign BDCs[0]  =  wb_psel_o & wb_penable_o & ~wb_paddr_o[11] &  wb_paddr_o[10] & pstb_i[0];   // 0x400 - 0x7FF

assign CsMiss =   wb_psel_o & wb_penable_o & wb_paddr_o[11];                   // 0x800 - 0xfFF	1000_0000_0100


//Moschip Team
always @(*)
begin
  if(|RegCs)  
	begin
		if(~pwrite_i)
			temp_prdata_o = RegDataOut; 
		else
			temp_prdata_o = 'dz;
	end
  else
    begin
		if(|BDCs & ~wb_pwrite_o)
		    temp_prdata_o = apb_bd_bridge_prdata_o;
		else
			temp_prdata_o = 'dz;
	end
	
end
`ifdef ETH_REGISTERED_OUTPUT
  assign pready_o = temp_pready_o_reg;
  assign prdata_o[31:0] = temp_prdata_o_reg;	//register outputs are needed so commenting them.
  assign pslverr = temp_perr_o_reg;
`else
  assign pready_o = temp_pready_o;
  assign prdata_o[31:0] = temp_prdata_o;
  assign pslverr = temp_perr_o;
`endif

`ifdef ETH_AVALON_BUS
  // As Avalon has no corresponding "error" signal, I (erroneously) will
  // send an ack to Avalon, even when accessing undefined memory. This
  // is a grey area in Avalon vs. Wishbone specs: My understanding
  // is that Avalon expects all memory addressable by the addr bus feeding
  // a slave to be, at the very minimum, readable.
  assign temp_pready_o = (|RegCs) | BDAck | CsMiss;
`else // APB
//Moschip Team
//Note: Generating the pready by depending on psel, penable and paddr.
//		Depending on paddr, pready can be multiplexed between RegCs and BDCs
  assign temp_pready_o = (|RegCs) | apb_bd_bridge_pready_o;
`endif


`ifdef ETH_REGISTERED_OUTPUT
  always @ (posedge pclk_i or negedge prstn_i)
  begin
    if(prstn_i == 0)
      begin
        temp_pready_o_reg <= 1'b0;
        temp_prdata_o_reg <= 32'h0;
        temp_perr_o_reg <= 1'b0;
      end
    else
      begin
        temp_pready_o_reg <= temp_pready_o & ~temp_pready_o_reg;
        temp_prdata_o_reg <= temp_prdata_o;
        temp_perr_o_reg <= temp_perr_o & ~temp_perr_o_reg;
      end
  end
`endif


// Connecting Ethernet registers
eth_registers ethreg1
(
  .wdata(pwdata_i),
  .addr(paddr_i[9:2]),
  .Rw(pwrite_i),
  .Cs(RegCs),
  .Clk(pclk_i),
  .Resetn(prstn_i),
  .DataOut(RegDataOut),
  .r_RecSmall(r_RecSmall),
  .r_Pad(r_Pad),
  .r_HugEn(r_HugEn),
  .r_CrcEn(r_CrcEn),
  .r_DlyCrcEn(r_DlyCrcEn),
  .r_FullD(r_FullD),
  .r_ExDfrEn(r_ExDfrEn),
  .r_NoBckof(r_NoBckof),
  .r_LoopBck(r_LoopBck),
  .r_IFG(r_IFG),
  .r_Pro(r_Pro),
  .r_Iam(r_Iam),
  .r_Bro(r_Bro),
  .r_NoPre(r_NoPre),
  .r_TxEn(r_TxEn),
  .r_RxEn(r_RxEn),
  .Busy_IRQ(Busy_IRQ),
  .RxE_IRQ(RxE_IRQ),
  .RxB_IRQ(RxB_IRQ),
  .TxE_IRQ(TxE_IRQ),
  .TxB_IRQ(TxB_IRQ),
  .r_IPGT(r_IPGT),
  .r_IPGR1(r_IPGR1),
  .r_IPGR2(r_IPGR2),
  .r_MinFL(r_MinFL),
  .r_MaxFL(r_MaxFL),
  .r_MaxRet(r_MaxRet),
  .r_CollValid(r_CollValid),
  .r_TxFlow(r_TxFlow),
  .r_RxFlow(r_RxFlow),
  .r_PassAll(r_PassAll),
  .r_MiiNoPre(r_MiiNoPre),
  .r_ClkDiv(r_ClkDiv),
  .r_WCtrlData(r_WCtrlData),
  .r_RStat(r_RStat),
  .r_ScanStat(r_ScanStat),
  .r_RGAD(r_RGAD),
  .r_FIAD(r_FIAD),
  .r_CtrlData(r_CtrlData),
  .NValid_stat(NValid_stat),
  .Busy_stat(Busy_stat),
  .LinkFail(LinkFail),
  .r_MAC(r_MAC),
  .WCtrlDataStart(WCtrlDataStart),
  .RStatStart(RStatStart),
  .UpdateMIIRX_DATAReg(UpdateMIIRX_DATAReg),
  .Prsd(Prsd),
  .r_TxBDNum(r_TxBDNum),
  .int_o(int_o),
  .r_HASH0(r_HASH0),
  .r_HASH1(r_HASH1),
  .r_TxPauseRq(r_TxPauseRq),
  .r_TxPauseTV(r_TxPauseTV),
  .RstTxPauseRq(RstTxPauseRq),
  .TxCtrlEndFrm(TxCtrlEndFrm),
  .StartTxDone(StartTxDone),
  .TxClk(mtx_clk_pad_i),
  .RxClk(mrx_clk_pad_i),
  .dbg_dat(wb_dbg_dat0),
  .SetPauseTimer(SetPauseTimer)
  
);



wire  [7:0] RxData;
wire        RxValid;
wire        RxStartFrm;
wire        RxEndFrm;
wire        RxAbort;

wire        WillTransmit;            // Will transmit (to RxEthMAC)
wire        ResetCollision;          // Reset Collision (for synchronizing 
                                     // collision)
wire  [7:0] TxDataOut;               // Transmit Packet Data (to TxEthMAC)
wire        WillSendControlFrame;
wire        ReceiveEnd;
wire        ReceivedPacketGood;
wire        ReceivedLengthOK;
wire        InvalidSymbol;
wire        LatchedCrcError;
wire        RxLateCollision;
wire  [3:0] RetryCntLatched;   
wire  [3:0] RetryCnt;   
wire        StartTxAbort;   
wire        MaxCollisionOccured;   
wire        RetryLimit;   
wire        StatePreamble; 
wire 		StateSFD;  
wire 		StateSA;
wire 		StateDA;
wire 		StateLength;
wire  [1:0] StateData; 

// Connecting MACControl
eth_maccontrol maccontrol1
(
  .MTxClk(mtx_clk_pad_i),
  .TPauseRq(TPauseRq),
  .TxPauseTV(r_TxPauseTV),
  .TxDataIn(TxData),
  .TxStartFrmIn(TxStartFrm),
  .TxEndFrmIn(TxEndFrm),
  .TxUsedDataIn(TxUsedDataIn),
  .TxDoneIn(TxDoneIn),
  .TxAbortIn(TxAbortIn),
  .MRxClk(mrx_clk_pad_i),
  .RxData(RxData),
  .RxValid(RxValid),
  .RxStartFrm(RxStartFrm),
  .RxEndFrm(RxEndFrm),
  .ReceiveEnd(ReceiveEnd),
  .ReceivedPacketGood(ReceivedPacketGood),
  .TxFlow(r_TxFlow),
  .RxFlow(r_RxFlow),
  .DlyCrcEn(r_DlyCrcEn),
  .MAC(r_MAC),
  .PadIn(r_Pad),
  .PadOut(PadOut),
  .CrcEnIn(r_CrcEn),
  .CrcEnOut(CrcEnOut),
  .TxResetn(prstn_i),
  .RxResetn(prstn_i),
  .ReceivedLengthOK(ReceivedLengthOK),
  .TxDataOut(TxDataOut),
  .TxStartFrmOut(TxStartFrmOut),
  .TxEndFrmOut(TxEndFrmOut),
  .TxUsedDataOut(TxUsedData),
  .TxDoneOut(TxDone),
  .TxAbortOut(TxAbort),
  .WillSendControlFrame(WillSendControlFrame),
  .TxCtrlEndFrm(TxCtrlEndFrm),
  .ReceivedPauseFrm(ReceivedPauseFrm),
  .ControlFrmAddressOK(ControlFrmAddressOK),
  .SetPauseTimer(SetPauseTimer),
  .RxStatusWriteLatched_sync2(RxStatusWriteLatched_sync2),
  .r_PassAll(r_PassAll)
);



wire TxCarrierSense;          // Synchronized CarrierSense (to Tx clock)
wire Collision;               // Synchronized Collision

reg CarrierSense_Tx1;
reg CarrierSense_Tx2;
reg Collision_Tx1;
reg Collision_Tx2;

reg RxEnSync;                 // Synchronized Receive Enable
reg WillTransmit_q;
reg WillTransmit_q2;



// Muxed MII receive data valid
assign MRxDV_Lb = r_LoopBck? mtxen_pad_o : mrxdv_pad_i & RxEnSync;

// Muxed MII Receive Error
assign MRxErr_Lb = r_LoopBck? mtxerr_pad_o : mrxerr_pad_i & RxEnSync;

// Muxed MII Receive Data
assign MRxD_Lb[3:0] = r_LoopBck? mtxd_pad_o[3:0] : mrxd_pad_i[3:0];



// Connecting TxEthMAC
eth_txethmac txethmac1
(
  .MTxClk(mtx_clk_pad_i),
  .Resetn(prstn_i),
  .CarrierSense(TxCarrierSense),
  .Collision(Collision),
  .TxData(TxDataOut),
  .TxStartFrm(TxStartFrmOut),
  .TxUnderRun(TxUnderRun),
  .TxEndFrm(TxEndFrmOut),
  .Pad(PadOut),
  .No_Preamble(r_NoPre),		
  .MAC_Address(r_MAC),
  .DA_Address({3'd0,r_FIAD[4],r_FIAD[3:0],40'd0}),
  .Payload_length(BD_TxLength),
  .r_LoopBck(r_LoopBck),
  .MinFL(r_MinFL),
  .CrcEn(CrcEnOut),
  .FullD(r_FullD),
  .HugEn(r_HugEn),
  .DlyCrcEn(r_DlyCrcEn),
  .IPGT(r_IPGT),
  .IPGR1(r_IPGR1),
  .IPGR2(r_IPGR2),
  .CollValid(r_CollValid),
  .MaxRet(r_MaxRet),
  .NoBckof(r_NoBckof),
  .ExDfrEn(r_ExDfrEn),
  .MaxFL(r_MaxFL),
  .MTxEn(mtxen_pad_o),
  .MTxD(mtxd_pad_o),
  .MTxErr(mtxerr_pad_o),
  .TxUsedData(TxUsedDataIn),
  .TxDone(TxDoneIn),
  .TxRetry(TxRetry),
  .TxAbort(TxAbortIn),
  .WillTransmit(WillTransmit),
  .ResetCollision(ResetCollision),
  .RetryCnt(RetryCnt),
  .StartTxDone(StartTxDone),
  .StartTxAbort(StartTxAbort),
  .MaxCollisionOccured(MaxCollisionOccured),
  .LateCollision(LateCollision),
  .DeferIndication(DeferIndication),
  .StatePreamble(StatePreamble),
  .StateSFD(StateSFD),
  .StateDA(StateDA),
  .StateSA(StateSA),
  .StateLength(StateLength),
  .StateData(StateData)   
);




wire  [15:0]  RxByteCnt;
wire          RxByteCntEq0;
wire          RxByteCntGreat2;
wire          RxByteCntMaxFrame;
wire          RxCrcError;
wire          RxStateIdle;
wire          RxStatePreamble;
wire          RxStateSFD;
wire   [1:0]  RxStateData;
wire 		  RxStateDA;
wire		  RxStateSA;
wire 		  RxStateLength;
wire          AddressMiss;




// Connecting RxEthMAC
eth_rxethmac rxethmac1
(
  .MRxClk(mrx_clk_pad_i),
  .MRxDV(MRxDV_Lb),
  .MRxD(MRxD_Lb),
  .MRxErr(MRxErr_Lb),
  .Transmitting(Transmitting),
  .Pad(PadOut),
  .HugEn(r_HugEn),
  .DlyCrcEn(r_DlyCrcEn),
  .r_MinFL(r_MinFL),
  .MaxFL(r_MaxFL),
  .r_IFG(r_IFG),
  .No_Preamble(r_NoPre),
  .Resetn(prstn_i),
  .RxData(RxData),
  .RxValid(RxValid),
  .RxStartFrm(RxStartFrm),
  .RxEndFrm(RxEndFrm),
  .ByteCnt(RxByteCnt),
  .ByteCntEq0(RxByteCntEq0),
  .ByteCntGreat2(RxByteCntGreat2),
  .ByteCntMaxFrame(RxByteCntMaxFrame),
  .CrcError(RxCrcError),
  .StateIdle(RxStateIdle),
  .StatePreamble(RxStatePreamble),
  .StateSFD(RxStateSFD),
  .StateData(RxStateData),
  .StateDA(RxStateDA),
  .StateSA(RxStateSA),
  .StateLength(RxStateLength),
  .MAC(r_MAC),
  .r_Pro(r_Pro),
  .r_Bro(r_Bro),
  .r_Iam(r_Iam),
  .r_HASH0(r_HASH0),
  .r_HASH1(r_HASH1),
  .RxAbort(RxAbort),
  .AddressMiss(AddressMiss),
  .PassAll(r_PassAll),
  .ControlFrmAddressOK(ControlFrmAddressOK),
  .Length_Vs_Payload_error(Length_Vs_Payload_error),
  .MRxErr_Detected(MRxErr_Detected),
  .Length_vs_payload_mismatch(Length_vs_payload_mismatch)
);


// MII Carrier Sense Synchronization
always @ (posedge mtx_clk_pad_i or negedge prstn_i)
begin
  if(prstn_i == 0)
    begin
      CarrierSense_Tx1 <=  1'b0;
      CarrierSense_Tx2 <=  1'b0;
    end
  else
    begin
      CarrierSense_Tx1 <=  mcrs_pad_i;
      CarrierSense_Tx2 <=  CarrierSense_Tx1;
    end
end

assign TxCarrierSense = ~r_FullD & CarrierSense_Tx2;


// MII Collision Synchronization
always @ (posedge mtx_clk_pad_i or negedge prstn_i)
begin
  if(prstn_i == 0)
    begin
      Collision_Tx1 <=  1'b0;
      Collision_Tx2 <=  1'b0;
    end
  else
    begin
      Collision_Tx1 <=  mcoll_pad_i;
      if(ResetCollision)
        Collision_Tx2 <=  1'b0;
      else
      if(Collision_Tx1)
        Collision_Tx2 <=  1'b1;
    end
end


// Synchronized Collision
assign Collision = ~r_FullD & Collision_Tx2;



// Delayed WillTransmit
always @ (posedge mrx_clk_pad_i)
begin
  WillTransmit_q <=  WillTransmit;
  WillTransmit_q2 <=  WillTransmit_q;
end 


assign Transmitting = ~r_FullD & WillTransmit_q2;


always @ (posedge mrx_clk_pad_i or negedge prstn_i)
begin
  if(prstn_i == 0)
    RxEnSync <=  1'b0;
  else
	if(~mrxdv_pad_i)
		RxEnSync <=  r_RxEn;
end

// Synchronizing WillSendControlFrame to WB_CLK;
always @ (posedge pclk_i or negedge prstn_i)
begin
  if(prstn_i == 0)
    WillSendControlFrame_sync1 <= 1'b0;
  else
    WillSendControlFrame_sync1 <= WillSendControlFrame;
end

always @ (posedge pclk_i or negedge prstn_i)
begin
  if(prstn_i == 0)
    WillSendControlFrame_sync2 <= 1'b0;
  else
    WillSendControlFrame_sync2 <= WillSendControlFrame_sync1;
end

always @ (posedge pclk_i or negedge prstn_i)
begin
  if(prstn_i == 0)
    WillSendControlFrame_sync3 <= 1'b0;
  else
    WillSendControlFrame_sync3 <= WillSendControlFrame_sync2;
end

always @ (posedge pclk_i or negedge prstn_i)
begin
  if(prstn_i == 0)
    RstTxPauseRq <= 1'b0;
  else
    RstTxPauseRq <= WillSendControlFrame_sync2 & ~WillSendControlFrame_sync3;
end




// TX Pause request Synchronization
always @ (posedge mtx_clk_pad_i or negedge prstn_i)
begin
  if(prstn_i == 0)
    begin
      TxPauseRq_sync1 <=  1'b0;
      TxPauseRq_sync2 <=  1'b0;
      TxPauseRq_sync3 <=  1'b0;
    end
  else
    begin
      TxPauseRq_sync1 <=  (r_TxPauseRq & r_TxFlow);
      TxPauseRq_sync2 <=  TxPauseRq_sync1;
      TxPauseRq_sync3 <=  TxPauseRq_sync2;
    end
end


always @ (posedge mtx_clk_pad_i or negedge prstn_i)
begin
  if(prstn_i == 0)
    TPauseRq <=  1'b0;
  else
    TPauseRq <=  TxPauseRq_sync2 & (~TxPauseRq_sync3);
end


wire LatchedMRxErr;
reg RxAbort_latch;
//reg RxAbort_sync1;
reg RxAbort_wb;
reg RxAbortRst_sync1;
reg RxAbortRst;

// Synchronizing RxAbort to the APB clock
always @ (posedge mrx_clk_pad_i or negedge prstn_i)
begin
  if(prstn_i == 0)
    RxAbort_latch <=  1'b0;
  else if(RxAbort)
    RxAbort_latch <=  1'b1;
  else if(RxAbortRst)
    RxAbort_latch <=  1'b0;
end

always @ (posedge pclk_i or negedge prstn_i)
begin
  if(prstn_i == 0)
    begin
//      RxAbort_sync1 <=  1'b0;
      RxAbort_wb    <=  1'b0;
      RxAbort_wb    <=  1'b0;
    end
  else
    begin
      RxAbort_wb    <=  RxAbort_latch;
    end
end

always @ (posedge mrx_clk_pad_i or negedge prstn_i)
begin
  if(prstn_i == 0)
    begin
      RxAbortRst_sync1 <=  1'b0;
      RxAbortRst       <=  1'b0;
    end
  else
    begin
      RxAbortRst_sync1 <=  RxAbort_wb;
      RxAbortRst       <=  RxAbortRst_sync1;
    end
end

//Moschip Team 
//Note: To compatible apb signals with the wishbone signals added the below module.
//		Inputs are APB supported signals, outputs are wishbone supported signals.

apb_BDs_bridge u_apb_BDs_bridge(

//apb signals
.apb_pclk_i(pclk_i),
.apb_presetn_i(prstn_i),
.apb_psel_i(psel_i),
.apb_penable_i(penable_i),
.apb_pwrite_i(pwrite_i),
.apb_pwdata_i(pwdata_i),
.apb_paddr_i(paddr_i),
.apb_prdata_o(apb_bd_bridge_prdata_o),	
.apb_pready_o(apb_bd_bridge_pready_o),	

//wishbone signals
.wb_psel_o(wb_psel_o),
.wb_penable_o(wb_penable_o),
.wb_pwrite_o(wb_pwrite_o),
.wb_pwdata_o(wb_pwdata_o),
.wb_paddr_o(wb_paddr_o),
.wb_prdata_i(BD_prdata_o),
.wb_BDAck_i(BDAck)
);



// Connecting Wishbone module
eth_wishbone #(.TX_FIFO_DATA_WIDTH(TX_FIFO_DATA_WIDTH),
	       .TX_FIFO_DEPTH     (TX_FIFO_DEPTH),
	       .TX_FIFO_CNT_WIDTH (TX_FIFO_CNT_WIDTH),
	       .RX_FIFO_DATA_WIDTH(RX_FIFO_DATA_WIDTH),
	       .RX_FIFO_DEPTH     (RX_FIFO_DEPTH),
	       .RX_FIFO_CNT_WIDTH (RX_FIFO_CNT_WIDTH))
wishbone
(
  .WB_CLK_I(pclk_i),
  .WB_DAT_I(wb_pwdata_o),
  .WB_DAT_O(BD_prdata_o),

  // WISHBONE slave
  .WB_ADDR_I(wb_paddr_o[9:2]),
  .WB_WE_I(wb_pwrite_o),
  .BDCs(BDCs),
  .WB_ACK_O(BDAck),
  .Resetn(prstn_i),

  // WISHBONE master
  .m_wb_adr_o(m_wb_adr_tmp),
  .m_wb_sel_o(m_psel_o),
  .m_wb_we_o(m_pwrite_o),
  .m_wb_dat_i(m_prdata_i),
  .m_wb_dat_o(m_pwdata_o),
  .m_wb_cyc_o_delayed_next_state(m_penable_o),	
  .m_wb_ack_i(m_pready_i),
  .m_wb_err_i(m_perr_i),
  
`ifdef ETH_WISHBONE_B3
  .m_wb_cti_o(m_wb_cti_o),
  .m_wb_bte_o(m_wb_bte_o), 
`endif

    //TX
  .MTxClk(mtx_clk_pad_i),
  .TxStartFrm(TxStartFrm),
  .TxEndFrm(TxEndFrm),
  .TxUsedData(TxUsedData),
  
  .TxData(TxData),
  .TxRetry(TxRetry),
  .TxAbort(TxAbort),
  .TxUnderRun(TxUnderRun),
  .TxDone(TxDone),
  .PerPacketCrcEn(PerPacketCrcEn),
  .PerPacketPad(PerPacketPad),

  // Register
  .r_TxEn(r_TxEn),
  .r_RxEn(r_RxEn),
  .r_Pad(r_Pad),
  .r_HugEn(r_HugEn),
  .r_MinFL(r_MinFL),
  .r_MaxFL(r_MaxFL),
  .r_TxBDNum(r_TxBDNum),
  .r_RxFlow(r_RxFlow),
  .r_PassAll(r_PassAll), 
  .BD_TxLength(BD_TxLength),
  //RX
  .MRxClk(mrx_clk_pad_i),
  .RxData(RxData),
  .RxValid(RxValid),
  .RxStartFrm(RxStartFrm),
  .RxEndFrm(RxEndFrm),
  .Busy_IRQ(Busy_IRQ),
  .RxE_IRQ(RxE_IRQ),
  .RxB_IRQ(RxB_IRQ),
  .TxE_IRQ(TxE_IRQ),
  .TxB_IRQ(TxB_IRQ), 


  .RxAbort(RxAbort_wb),
  .RxStatusWriteLatched_sync2(RxStatusWriteLatched_sync2), 

  .InvalidSymbol(InvalidSymbol),
  .LatchedCrcError(LatchedCrcError),
  .RxLength(RxByteCnt),
  .RxLateCollision(RxLateCollision),
  .ShortFrame(ShortFrame),
  .DribbleNibble(DribbleNibble),
  .ReceivedPacketTooBig(ReceivedPacketTooBig),
  .LoadRxStatus(LoadRxStatus),
  .RetryCntLatched(RetryCntLatched),
  .RetryLimit(RetryLimit),
  .LateCollLatched(LateCollLatched),
  .DeferLatched(DeferLatched),
  .RstDeferLatched(RstDeferLatched),
  .CarrierSenseLost(CarrierSenseLost),
  .ReceivedPacketGood(ReceivedPacketGood),
  .AddressMiss(AddressMiss),
  .MRxErr_Detected(MRxErr_Detected),
  .Length_Vs_Payload_error(Length_Vs_Payload_error),
  .Length_vs_payload_mismatch(Length_vs_payload_mismatch),
  .ReceivedPauseFrm(ReceivedPauseFrm)
  
`ifdef ETH_BIST
  ,
  .mbist_si_i       (mbist_si_i),
  .mbist_so_o       (mbist_so_o),
  .mbist_ctrl_i       (mbist_ctrl_i)
`endif
`ifdef WISHBONE_DEBUG
  ,
  .dbg_dat0(wb_dbg_dat0)
`endif

);

assign m_paddr_o = {m_wb_adr_tmp, 2'h0};

// Connecting MacStatus module
eth_macstatus macstatus1 
(
  .MRxClk(mrx_clk_pad_i),
  .Resetn(prstn_i),
  .ReceiveEnd(ReceiveEnd),
  .ReceivedPacketGood(ReceivedPacketGood),
  .ReceivedLengthOK(ReceivedLengthOK),
  .RxCrcError(RxCrcError),
  .MRxErr(MRxErr_Lb),
  .MRxDV(MRxDV_Lb),
  .RxStateSFD(RxStateSFD),
  .RxStateData(RxStateData),
  .RxStatePreamble(RxStatePreamble),
  .RxStateIdle(RxStateIdle),
  .RxStateDA(RxStateDA),
  .RxStateSA(RxStateSA),
  .RxStateLength(RxStateLength),
  .Transmitting(Transmitting),
  .RxByteCnt(RxByteCnt),
  .RxByteCntEq0(RxByteCntEq0),
  .RxByteCntGreat2(RxByteCntGreat2),
  .RxByteCntMaxFrame(RxByteCntMaxFrame),
  .InvalidSymbol(InvalidSymbol),
  .MRxD(MRxD_Lb),
  .LatchedCrcError(LatchedCrcError),
  .Collision(mcoll_pad_i),
  .CollValid(r_CollValid),
  .RxLateCollision(RxLateCollision),
  .r_RecSmall(r_RecSmall),
  .r_MinFL(r_MinFL),
  .r_MaxFL(r_MaxFL),
  .ShortFrame(ShortFrame),
  .DribbleNibble(DribbleNibble),
  .ReceivedPacketTooBig(ReceivedPacketTooBig),
  .r_HugEn(r_HugEn),
  .LoadRxStatus(LoadRxStatus),
  .RetryCnt(RetryCnt),
  .StartTxDone(StartTxDone),
  .StartTxAbort(StartTxAbort),
  .RetryCntLatched(RetryCntLatched),
  .MTxClk(mtx_clk_pad_i),
  .MaxCollisionOccured(MaxCollisionOccured),
  .RetryLimit(RetryLimit),
  .LateCollision(LateCollision),
  .LateCollLatched(LateCollLatched),
  .DeferIndication(DeferIndication),
  .DeferLatched(DeferLatched),
  .RstDeferLatched(RstDeferLatched),
  .TxStartFrm(TxStartFrmOut),
  .StatePreamble(StatePreamble),
  .StateSFD(StateSFD),
  .StateDA(StateDA),
  .StateSA(StateSA),
  .StateLength(StateLength),
  .StateData(StateData),
  .CarrierSense(CarrierSense_Tx2),
  .CarrierSenseLost(CarrierSenseLost),
  .TxUsedData(TxUsedDataIn),
  .LatchedMRxErr(LatchedMRxErr),
  .Loopback(r_LoopBck),
  .r_FullD(r_FullD)
);


endmodule


//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date:    17:42:00 06/07/2020 
// Design Name: 
// Module Name:    eth_transmitcontrol 
// Project Name: 
// Target Devices: 
// Tool versions: 
// Description: 
//
// Dependencies: 
//
// Revision: 
// Revision 0.01 - File Created
// Additional Comments: 
//
//////////////////////////////////////////////////////////////////////////////////

`include "timescale.v"
module eth_transmitcontrol (MTxClk, TxResetn, TxUsedDataIn, TxUsedDataOut, TxDoneIn, TxAbortIn, 
                            TxStartFrmIn, TPauseRq, TxUsedDataOutDetected, TxFlow, DlyCrcEn, 
                            TxPauseTV, MAC, TxCtrlStartFrm, TxCtrlEndFrm, SendingCtrlFrm, CtrlMux, 
                            ControlData, WillSendControlFrame, BlockTxDone
                           );


input         MTxClk;
input         TxResetn;
input         TxUsedDataIn;
input         TxUsedDataOut;
input         TxDoneIn;
input         TxAbortIn;
input         TxStartFrmIn;
input         TPauseRq;
input         TxUsedDataOutDetected;
input         TxFlow;
input         DlyCrcEn;
input  [15:0] TxPauseTV;
input  [47:0] MAC;

output        TxCtrlStartFrm;
output        TxCtrlEndFrm;
output        SendingCtrlFrm;
output        CtrlMux;
output [7:0]  ControlData;
output        WillSendControlFrame;
output        BlockTxDone;

reg           SendingCtrlFrm;
reg           CtrlMux;
reg           WillSendControlFrame;
reg    [3:0]  DlyCrcCnt;
reg    [5:0]  ByteCnt;
reg           ControlEnd_q;
reg    [7:0]  MuxedCtrlData;
reg           TxCtrlStartFrm;
reg           TxCtrlStartFrm_q;
reg           TxCtrlEndFrm;
reg    [7:0]  ControlData;
reg           TxUsedDataIn_q;
reg           BlockTxDone;

wire          IncrementDlyCrcCnt;
wire          ResetByteCnt;
wire          IncrementByteCnt;
wire          ControlEnd;
wire          IncrementByteCntBy2;
wire          EnableCnt;


// A command for Sending the control frame is active (latched)
always @ (posedge MTxClk or negedge TxResetn)
begin
  if(TxResetn == 0)
    WillSendControlFrame <=  1'b0;
  else
  if(TxCtrlEndFrm & CtrlMux)
    WillSendControlFrame <=  1'b0;
  else
  if(TPauseRq & TxFlow)
    WillSendControlFrame <=  1'b1;
end


// Generation of the transmit control packet start frame
always @ (posedge MTxClk or negedge TxResetn)
begin
  if(TxResetn == 0)
    TxCtrlStartFrm <=  1'b0;
  else
  if(TxUsedDataIn_q & CtrlMux)
    TxCtrlStartFrm <=  1'b0;
  else
  if(WillSendControlFrame & ~TxUsedDataOut & (TxDoneIn | TxAbortIn | TxStartFrmIn | (~TxUsedDataOutDetected)))
    TxCtrlStartFrm <=  1'b1;
end



// Generation of the transmit control packet end frame
always @ (posedge MTxClk or negedge TxResetn)
begin
  if(TxResetn == 0)
    TxCtrlEndFrm <=  1'b0;
  else
  if(ControlEnd | ControlEnd_q)
    TxCtrlEndFrm <=  1'b1;
  else
    TxCtrlEndFrm <=  1'b0;
end


// Generation of the multiplexer signal (controls muxes for switching between
// normal and control packets)
always @ (posedge MTxClk or negedge TxResetn)
begin
  if(TxResetn == 0)
    CtrlMux <=  1'b0;
  else
  if(WillSendControlFrame & ~TxUsedDataOut)
    CtrlMux <=  1'b1;
  else
  if(TxDoneIn)
    CtrlMux <=  1'b0;
end



// Generation of the Sending Control Frame signal (enables padding and CRC)
always @ (posedge MTxClk or negedge TxResetn)
begin
  if(TxResetn == 0)
    SendingCtrlFrm <=  1'b0;
  else
  if(WillSendControlFrame & TxCtrlStartFrm)
    SendingCtrlFrm <=  1'b1;
  else
  if(TxDoneIn)
    SendingCtrlFrm <=  1'b0;
end


always @ (posedge MTxClk or negedge TxResetn)
begin
  if(TxResetn == 0)
    TxUsedDataIn_q <=  1'b0;
  else
    TxUsedDataIn_q <=  TxUsedDataIn;
end



// Generation of the signal that will block sending the Done signal to the eth_wishbone module
// While sending the control frame
always @ (posedge MTxClk or negedge TxResetn)
begin
  if(TxResetn == 0)
    BlockTxDone <=  1'b0;
  else
  if(TxCtrlStartFrm)
    BlockTxDone <=  1'b1;
  else
  if(TxStartFrmIn)
    BlockTxDone <=  1'b0;
end


always @ (posedge MTxClk)
begin
  ControlEnd_q     <=  ControlEnd;
  TxCtrlStartFrm_q <=  TxCtrlStartFrm;
end


assign IncrementDlyCrcCnt = CtrlMux & TxUsedDataIn &  ~DlyCrcCnt[2];


// Delayed CRC counter
always @ (posedge MTxClk or negedge TxResetn)
begin
  if(TxResetn == 0)
    DlyCrcCnt <=  4'h0;
  else
  if(ResetByteCnt)
    DlyCrcCnt <=  4'h0;
  else
  if(IncrementDlyCrcCnt)
    DlyCrcCnt <=  DlyCrcCnt + 4'd1;
end

             
assign ResetByteCnt = (TxResetn == 0) | (~TxCtrlStartFrm & (TxDoneIn | TxAbortIn));
assign IncrementByteCnt = CtrlMux & (TxCtrlStartFrm & ~TxCtrlStartFrm_q & ~TxUsedDataIn | TxUsedDataIn & ~ControlEnd);
assign IncrementByteCntBy2 = CtrlMux & TxCtrlStartFrm & (~TxCtrlStartFrm_q) & TxUsedDataIn;     // When TxUsedDataIn and CtrlMux are set at the same time

assign EnableCnt = (~DlyCrcEn | DlyCrcEn & (&DlyCrcCnt[1:0]));
// Byte counter
always @ (posedge MTxClk or negedge TxResetn)
begin
  if(TxResetn == 0)
    ByteCnt <=  6'h0;
  else
  if(ResetByteCnt)
    ByteCnt <=  6'h0;
  else
  if(IncrementByteCntBy2 & EnableCnt)
    ByteCnt <=  (ByteCnt[5:0] ) + 6'd2;
  else
  if(IncrementByteCnt & EnableCnt)
    ByteCnt <=  (ByteCnt[5:0] ) + 6'd1;
end


assign ControlEnd = ByteCnt[5:0] == 6'h22;


// Control data generation (goes to the TxEthMAC module)
always @ (ByteCnt or DlyCrcEn or MAC or TxPauseTV or DlyCrcCnt)
begin
  case(ByteCnt)
    6'h0:    if(~DlyCrcEn | DlyCrcEn & (&DlyCrcCnt[1:0]))
               MuxedCtrlData[7:0] = 8'h01;                   // Reserved Multicast Address
             else
						 	 MuxedCtrlData[7:0] = 8'h0;
    6'h2:      MuxedCtrlData[7:0] = 8'h80;
    6'h4:      MuxedCtrlData[7:0] = 8'hC2;
    6'h6:      MuxedCtrlData[7:0] = 8'h00;
    6'h8:      MuxedCtrlData[7:0] = 8'h00;
    6'hA:      MuxedCtrlData[7:0] = 8'h01;
    6'hC:      MuxedCtrlData[7:0] = MAC[47:40];
    6'hE:      MuxedCtrlData[7:0] = MAC[39:32];
    6'h10:     MuxedCtrlData[7:0] = MAC[31:24];
    6'h12:     MuxedCtrlData[7:0] = MAC[23:16];
    6'h14:     MuxedCtrlData[7:0] = MAC[15:8];
    6'h16:     MuxedCtrlData[7:0] = MAC[7:0];
    6'h18:     MuxedCtrlData[7:0] = 8'h88;                   // Type/Length
    6'h1A:     MuxedCtrlData[7:0] = 8'h08;
    6'h1C:     MuxedCtrlData[7:0] = 8'h00;                   // Opcode
    6'h1E:     MuxedCtrlData[7:0] = 8'h01;
    6'h20:     MuxedCtrlData[7:0] = TxPauseTV[15:8];         // Pause timer value
    6'h22:     MuxedCtrlData[7:0] = TxPauseTV[7:0];
    default:   MuxedCtrlData[7:0] = 8'h0;
  endcase
end


// Latched Control data
always @ (posedge MTxClk or negedge TxResetn)
begin
  if(TxResetn == 0)
    ControlData[7:0] <=  8'h0;
  else
  if(~ByteCnt[0])
    ControlData[7:0] <=  MuxedCtrlData[7:0];
end



endmodule


//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date:    17:42:22 06/07/2020 
// Design Name: 
// Module Name:    eth_txcounters 
// Project Name: 
// Target Devices: 
// Tool versions: 
// Description: 
//
// Dependencies: 
//
// Revision: 
// Revision 0.01 - File Created
// Additional Comments: 
//
//////////////////////////////////////////////////////////////////////////////////
`include "timescale.v"
module eth_txcounters (StatePreamble, StateIPG,StateSA,StateDA, StateLength, StateData, StatePAD, StateFCS, StateJam, 
                       StateBackOff, StateDefer, StateIdle, StartDefer, StartIPG, StartFCS, 
                       StartJam, StartBackoff, TxStartFrm, MTxClk, Resetn, MinFL, MaxFL, HugEn, 
                       ExDfrEn, PacketFinished_q, DlyCrcEn, StateSFD, ByteCnt, NibCnt, 
                       ExcessiveDefer, NibCntEq7, NibCntEq15, MaxFrame, NibbleMinFl, DlyCrcCnt
                      );

input MTxClk;             // Tx clock
input Resetn;              // Resetn
input StatePreamble;      // Preamble state
input StateIPG;           // IPG state
input StateSA;			  // Source address state
input StateDA;			  // Destination address state
input StateLength;		  // payload length State
input [1:0] StateData;    // Data state
input StatePAD;           // PAD state
input StateFCS;           // FCS state
input StateJam;           // Jam state
input StateBackOff;       // Backoff state
input StateDefer;         // Defer state
input StateIdle;          // Idle state
input StateSFD;           // SFD state
input StartDefer;         // Defer state will be activated in next clock
input StartIPG;           // IPG state will be activated in next clock
input StartFCS;           // FCS state will be activated in next clock
input StartJam;           // Jam state will be activated in next clock
input StartBackoff;       // Backoff state will be activated in next clock
input TxStartFrm;         // Tx start frame
input [15:0] MinFL;       // Minimum frame length (in bytes)
input [15:0] MaxFL;       // Miximum frame length (in bytes)
input HugEn;              // Pakets bigger then MaxFL enabled
input ExDfrEn;            // Excessive deferral enabled
input PacketFinished_q;             
input DlyCrcEn;           // Delayed CRC enabled

output [15:0] ByteCnt;    // Byte counter
output [15:0] NibCnt;     // Nibble counter
output ExcessiveDefer;    // Excessive Deferral occuring
output NibCntEq7;         // Nibble counter is equal to 7
output NibCntEq15;        // Nibble counter is equal to 15
output MaxFrame;          // Maximum frame occured
output NibbleMinFl;       // Nibble counter is greater than the minimum frame length
output [2:0] DlyCrcCnt;   // Delayed CRC Count

wire ExcessiveDeferCnt;
wire ResetNibCnt;
wire IncrementNibCnt;
wire ResetByteCnt;
wire IncrementByteCnt;
wire ByteCntMax;

reg [15:0] NibCnt;
reg [15:0] ByteCnt;
reg  [2:0] DlyCrcCnt;



assign IncrementNibCnt = StateIPG | StatePreamble | (|StateData) | StatePAD | StateSFD | StateSA | StateDA | StateLength
                       | StateFCS | StateJam | StateBackOff | StateDefer & ~ExcessiveDefer & TxStartFrm;


assign ResetNibCnt = StateDefer & ExcessiveDefer & ~TxStartFrm | StatePreamble & (NibCnt == 'd13) | StateSFD & (NibCnt == 'd1)
                  | StateDA & (NibCnt == 'd11)| StateSA & (NibCnt == 'd11) | StateLength & (NibCnt == 'd3)| StateJam & NibCntEq7 | StateIdle | StartDefer | StartIPG | StartFCS | StartJam;

// Nibble Counter
always @ (posedge MTxClk or negedge Resetn)
begin
  if(Resetn == 0)
    NibCnt <=  16'h0;
  else
    begin
      if(ResetNibCnt)
        NibCnt <=  16'h0;
      else
      if(IncrementNibCnt)
        NibCnt <=  NibCnt + 16'd1;
     end
end


assign NibCntEq7   = &NibCnt[2:0];
assign NibCntEq15  = &NibCnt[3:0];


assign NibbleMinFl = NibCnt+'d28 >= (((MinFL-16'd4)<<1) -1); //Added on May  	14 bytes(DA,SA,Length)

assign ExcessiveDeferCnt = NibCnt[13:0] == 14'h17b7;

assign ExcessiveDefer  = NibCnt[13:0] == 14'h17b7 & ~ExDfrEn;   // 6071 nibbles

assign IncrementByteCnt = StateData[1] & ~ByteCntMax
                        | StateBackOff & (&NibCnt[6:0])
                        | (StatePAD | StateFCS) & NibCnt[0] & ~ByteCntMax;

assign ResetByteCnt = StartBackoff | StateIdle & TxStartFrm | PacketFinished_q;


// Transmit Byte Counter
always @ (posedge MTxClk or negedge Resetn)
begin
  if(Resetn == 0)
    ByteCnt[15:0] <=  16'h0;
  else
    begin
      if(ResetByteCnt)
        ByteCnt[15:0] <=  16'h0;
      else
      if(IncrementByteCnt)
        ByteCnt[15:0] <=  ByteCnt[15:0] + 16'd1;
    end
end


assign MaxFrame = ByteCnt[15:0] == MaxFL[15:0] & ~HugEn;

assign ByteCntMax = &ByteCnt[15:0];


// Delayed CRC counter
always @ (posedge MTxClk or negedge Resetn)
begin
  if(Resetn == 0)
    DlyCrcCnt <=  3'h0;
  else
    begin        
      if(StateData[1] & DlyCrcCnt == 3'h4 | StartJam | PacketFinished_q)
        DlyCrcCnt <=  3'h0;
      else
      if(DlyCrcEn & (StateSFD | StateData[1] & (|DlyCrcCnt[2:0])))
        DlyCrcCnt <=  DlyCrcCnt + 3'd1;
    end
end



endmodule


//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date:    17:42:46 06/07/2020 
// Design Name: 
// Module Name:    eth_txethmac 
// Project Name: 
// Target Devices: 
// Tool versions: 
// Description: 
//
// Dependencies: 
//
// Revision: 
// Revision 0.01 - File Created
// Additional Comments: 
//
//////////////////////////////////////////////////////////////////////////////////
`include "timescale.v"
module eth_txethmac (MTxClk, Resetn, TxStartFrm, TxEndFrm, TxUnderRun, TxData, CarrierSense, r_LoopBck,
                     Collision, Pad,No_Preamble,MAC_Address,DA_Address,Payload_length, CrcEn, FullD, HugEn, DlyCrcEn, MinFL, MaxFL, IPGT, 
                     IPGR1, IPGR2, CollValid, MaxRet, NoBckof, ExDfrEn, 
                     MTxD, MTxEn, MTxErr, TxDone, TxRetry, TxAbort, TxUsedData, WillTransmit, 
                     ResetCollision, RetryCnt, StartTxDone, StartTxAbort, MaxCollisionOccured,
                     LateCollision, DeferIndication, StatePreamble,StateSFD,StateDA,StateSA,StateLength, StateData
                    );


input MTxClk;                   // Transmit clock (from PHY)
input Resetn;                    // Resetn
input TxStartFrm;               // Transmit packet start frame
input TxEndFrm;                 // Transmit packet end frame
input TxUnderRun;               // Transmit packet under-run
input [7:0] TxData;             // Transmit packet data byte
input CarrierSense;             // Carrier sense (synchronized)
input Collision;                // Collision (synchronized)
input Pad;                      // Pad enable (from register)
input No_Preamble;				//No_Preamble (from register)	added
input [47:0] MAC_Address;		//MAC_Address(Source address)	added
input [47:0] DA_Address;		// PHY_address(destination address) added
input [15:0] Payload_length;	// Length (from Buffer descriptors)
input CrcEn;                    // Crc enable (from register)
input FullD;                    // Full duplex (from register)
input HugEn;                    // Huge packets enable (from register)
input DlyCrcEn;                 // Delayed Crc enabled (from register)
input r_LoopBck;				//Loopback (From Register)
input [15:0] MinFL;             // Minimum frame length (from register)
input [15:0] MaxFL;             // Maximum frame length (from register)
input [6:0] IPGT;               // Back to back transmit inter packet gap parameter (from register)
input [6:0] IPGR1;              // Non back to back transmit inter packet gap parameter IPGR1 (from register)
input [6:0] IPGR2;              // Non back to back transmit inter packet gap parameter IPGR2 (from register)
input [5:0] CollValid;          // Valid collision window (from register)
input [3:0] MaxRet;             // Maximum retry number (from register)
input NoBckof;                  // No backoff (from register)
input ExDfrEn;                  // Excessive defferal enable (from register)

output [3:0] MTxD;              // Transmit nibble (to PHY)
output MTxEn;                   // Transmit enable (to PHY)
output MTxErr;                  // Transmit error (to PHY)
output TxDone;                  // Transmit packet done (to RISC)
output TxRetry;                 // Transmit packet retry (to RISC)
output TxAbort;                 // Transmit packet abort (to RISC)
output TxUsedData;              // Transmit packet used data (to RISC)
output WillTransmit;            // Will transmit (to RxEthMAC)
output ResetCollision;          // Resetn Collision (for synchronizing collision)
output [3:0] RetryCnt;          // Latched Retry Counter for tx status purposes
output StartTxDone;
output StartTxAbort;
output MaxCollisionOccured;
output LateCollision;
output DeferIndication;
output StatePreamble;
output StateSFD;
output StateDA;
output StateSA;
output StateLength;
output [1:0] StateData;

reg [3:0] MTxD;
reg MTxEn;
reg MTxErr;
reg TxDone;
reg TxRetry;
reg TxAbort;
reg TxUsedData;
reg WillTransmit;
reg ColWindow;
reg StopExcessiveDeferOccured;
reg [3:0] RetryCnt;
reg [3:0] MTxD_d;
reg StatusLatch;
reg PacketFinished_q;
reg PacketFinished;


wire ExcessiveDeferOccured;
wire StartIPG;
wire StartPreamble;
wire StartSFD;	
wire StartSA;	//added
wire StartDA;
wire StartLength;

wire [1:0] StartData;
wire StartFCS;
wire StartJam;
wire StartDefer;
wire StartBackoff;
wire StateDefer;
wire StateIPG;
wire StateIdle;
//wire StateSA;
//wire StateDA;
//wire StateLength;
wire StatePAD;
wire StateFCS;
wire StateJam;
wire StateJam_q;
wire StateBackOff;
//wire StateSFD;
wire StartTxRetry;
wire UnderRun;
wire TooBig;
wire [31:0] Crc;
wire CrcError;
wire [2:0] DlyCrcCnt;
wire [15:0] NibCnt;
wire NibCntEq7;
wire NibCntEq15;
wire NibbleMinFl;
wire ExcessiveDefer;
wire [15:0] ByteCnt;
wire MaxFrame;
wire RetryMax;
wire RandomEq0;
wire RandomEqByteCnt;
wire PacketFinished_d;



assign ResetCollision = ~(StatePreamble | StateSFD | StateSA | StateDA | StateLength |(|StateData) | StatePAD | StateFCS);

assign ExcessiveDeferOccured = TxStartFrm & StateDefer & ExcessiveDefer & ~StopExcessiveDeferOccured;

assign StartTxDone = ~Collision & (StateFCS & NibCntEq7 | StateData[1] & TxEndFrm & (~Pad | Pad & NibbleMinFl) & ~CrcEn);

assign UnderRun = StateData[0] & TxUnderRun & ~Collision;

assign TooBig = ~Collision & MaxFrame & (StateData[0] & ~TxUnderRun | StateFCS);

assign StartTxRetry = StartJam & (ColWindow & ~RetryMax) & ~UnderRun;

assign LateCollision = StartJam & ~ColWindow & ~UnderRun;

assign MaxCollisionOccured = StartJam & ColWindow & RetryMax;

assign StartTxAbort = TooBig | UnderRun | ExcessiveDeferOccured | LateCollision | MaxCollisionOccured;		//Update for the Padding error


// StopExcessiveDeferOccured
always @ (posedge MTxClk or negedge Resetn)
begin
  if(Resetn == 0)
    StopExcessiveDeferOccured <=  1'b0;
  else
    begin
      if(~TxStartFrm)
        StopExcessiveDeferOccured <=  1'b0;
      else
      if(ExcessiveDeferOccured)
        StopExcessiveDeferOccured <=  1'b1;
    end
end


// Collision Window
always @ (posedge MTxClk or negedge Resetn)
begin
  if(Resetn == 0)
    ColWindow <=  1'b1;
  else
    begin  
      if(~Collision & ByteCnt[5:0] == CollValid[5:0] & (StateData[1] | StatePAD & NibCnt[0] | StateFCS & NibCnt[0]))
        ColWindow <=  1'b0;
      else
      if(StateIdle | StateIPG)
        ColWindow <=  1'b1;
    end
end


// Start Window
always @ (posedge MTxClk or negedge Resetn)
begin
  if(Resetn == 0)
    StatusLatch <=  1'b0;
  else
    begin
      if(~TxStartFrm)
        StatusLatch <=  1'b0;
      else
      if(ExcessiveDeferOccured | StateIdle)
        StatusLatch <=  1'b1;
     end
end


// Transmit packet used data
always @ (posedge MTxClk or negedge Resetn)
begin
  if(Resetn == 0)
    TxUsedData <=  1'b0;
  else
    TxUsedData <=  |StartData;
end


// Transmit packet done
always @ (posedge MTxClk or negedge Resetn)
begin
  if(Resetn == 0)
    TxDone <=  1'b0;
  else
    begin
      if(TxStartFrm & ~StatusLatch)
        TxDone <=  1'b0;
      else
      if(StartTxDone)
        TxDone <=  1'b1;
    end
end


// Transmit packet retry
always @ (posedge MTxClk or negedge Resetn)
begin
  if(Resetn == 0)
    TxRetry <=  1'b0;
  else
    begin
      if(TxStartFrm & ~StatusLatch)
        TxRetry <=  1'b0;
      else
      if(StartTxRetry)
        TxRetry <=  1'b1;
     end
end                                    


// Transmit packet abort
always @ (posedge MTxClk or negedge Resetn)
begin
  if(Resetn == 0)
    TxAbort <=  1'b0;
  else
    begin
      if(TxStartFrm & ~StatusLatch & ~ExcessiveDeferOccured)
        TxAbort <=  1'b0;
      else
      if(StartTxAbort)
        TxAbort <=  1'b1;
    end
end


// Retry counter
always @ (posedge MTxClk or negedge Resetn)
begin
  if(Resetn == 0)
    RetryCnt[3:0] <=  4'h0;
  else
    begin
      if(ExcessiveDeferOccured | UnderRun | TooBig | StartTxDone | TxUnderRun 
          | StateJam & NibCntEq7 & (~ColWindow | RetryMax))
        RetryCnt[3:0] <=  4'h0;
      else
      if(StateJam & NibCntEq7 & ColWindow & (RandomEq0 | NoBckof) | StateBackOff & RandomEqByteCnt)
        RetryCnt[3:0] <=  RetryCnt[3:0] + 1;
    end
end


assign RetryMax = RetryCnt[3:0] == MaxRet[3:0];

reg [47:0] Source_Address;	// = MAC_Address;
reg [47:0] Destination_address; 
reg [15:0] Data_payload_length;
always @(posedge MTxClk or negedge Resetn)
begin
	if(Resetn == 0)
	begin
		Source_Address <= 0;
		Destination_address <= 0;
	end
	else 
	begin
		case(1)
		StateDA: begin
					if(NibCnt < 11)
						Destination_address <= Destination_address << 4;
				 end
		StateSA: begin
					if(NibCnt < 11)
						Source_Address <= Source_Address << 4;
				 end
		StateLength : begin
						if(NibCnt < 3)
							Data_payload_length <= Data_payload_length >> 4;
					  end
		StateSFD: begin 
					Source_Address <= MAC_Address;
					Destination_address <= DA_Address;
					Data_payload_length <= Payload_length;
				  end
		endcase
	end
end
reg [47:0] DA_Address1;
always@(*)
begin
	if(r_LoopBck)
		DA_Address1 = MAC_Address;
	else
		DA_Address1 = DA_Address;
end

// Transmit nibble
always @ (StatePreamble or StateData or StateFCS or StateJam or StateSFD or StateDA or StateSA or StateLength or TxData or 
          Crc or NibCntEq15 or NibCnt or Destination_address or Source_Address or Data_payload_length)
begin
  if(StateData[0])
    MTxD_d[3:0] = TxData[3:0];                                  // Lower nibble
  else begin
		if(StateData[1])
			MTxD_d[3:0] = TxData[7:4];                                  // Higher nibble
		else begin
			if(StateFCS)
				MTxD_d[3:0] = {~Crc[28], ~Crc[29], ~Crc[30], ~Crc[31]};     // Crc
			else begin
				if(StateJam)
					MTxD_d[3:0] = 4'h9;                                         // Jam pattern
				else begin
					if(StatePreamble)
					begin
						MTxD_d[3:0] = 4'h5; 		//Preamble
					end
					else begin
						if(StateSFD) 
						 begin
							if(NibCnt == 'd1)
								MTxD_d[3:0] = 4'hd;                                       // SFD
							else
								MTxD_d[3:0] = 4'h5;    
						 end
						else begin
							 if(StateDA)
							    begin	
									case(NibCnt)
										'd0:MTxD_d[3:0] = DA_Address1[47:44];
										'd1:MTxD_d[3:0] = DA_Address1[43:40];
										'd2:MTxD_d[3:0] = DA_Address1[39:36];
										'd3:MTxD_d[3:0] = DA_Address1[35:32];
										'd4:MTxD_d[3:0] = DA_Address1[31:28];
										'd5:MTxD_d[3:0] = DA_Address1[27:24];
										'd6:MTxD_d[3:0] = DA_Address1[23:20];
										'd7:MTxD_d[3:0] = DA_Address1[19:16];
										'd8:MTxD_d[3:0] = DA_Address1[15:12];
										'd9:MTxD_d[3:0] = DA_Address1[11:8];
										'd10:MTxD_d[3:0] = DA_Address1[7:4];
										'd11:MTxD_d[3:0] = DA_Address1[3:0];
									endcase	
								end
							 else begin
									if(StateSA)
									begin
										case(NibCnt)
										'd0:MTxD_d[3:0] = MAC_Address[47:44];
										'd1:MTxD_d[3:0] = MAC_Address[43:40];
										'd2:MTxD_d[3:0] = MAC_Address[39:36];
										'd3:MTxD_d[3:0] = MAC_Address[35:32];
										'd4:MTxD_d[3:0] = MAC_Address[31:28];
										'd5:MTxD_d[3:0] = MAC_Address[27:24];
										'd6:MTxD_d[3:0] = MAC_Address[23:20];
										'd7:MTxD_d[3:0] = MAC_Address[19:16];
										'd8:MTxD_d[3:0] = MAC_Address[15:12];
										'd9:MTxD_d[3:0] = MAC_Address[11:8];
										'd10:MTxD_d[3:0] = MAC_Address[7:4];
										'd11:MTxD_d[3:0] = MAC_Address[3:0];
										endcase	
									end
									else begin
										if(StateLength)		//0040
										begin
											case(NibCnt)
											'd0:MTxD_d[3:0] = Payload_length[11:8];
											'd1:MTxD_d[3:0] = Payload_length[15:12];
											'd2:MTxD_d[3:0] = Payload_length[3:0];
											'd3:MTxD_d[3:0] = Payload_length[7:4];
											endcase
										end
										else
											MTxD_d[3:0] = 4'h0;
									end
							 end
						end
					end
				end
			end
		end
	end
end


// Transmit Enable
always @ (posedge MTxClk or negedge Resetn)
begin
  if(Resetn == 0)
    MTxEn <=  1'b0;
  else
    MTxEn <=  StatePreamble| StateSFD | StateSA | StateDA | StateLength |(|StateData) | StatePAD | StateFCS | StateJam;	
end


// Transmit nibble
always @ (posedge MTxClk or negedge Resetn)
begin
  if(Resetn == 0)
    MTxD[3:0] <=  4'h0;
  else
    MTxD[3:0] <=  MTxD_d[3:0];
end


// Transmit error
always @ (posedge MTxClk or negedge Resetn)
begin
  if(Resetn == 0)
    MTxErr <=  1'b0;
  else
    MTxErr <=  TooBig | UnderRun;		
end


// WillTransmit
always @ (posedge MTxClk or negedge Resetn)
begin
  if(Resetn == 0)
    WillTransmit <=   1'b0;
  else
    WillTransmit <=  StartPreamble | StatePreamble | StateSFD | StateSA | StateDA | StateLength |(|StateData) | StatePAD | StateFCS | StateJam;
end


assign PacketFinished_d = StartTxDone | TooBig | UnderRun | LateCollision | MaxCollisionOccured | ExcessiveDeferOccured;


// Packet finished
always @ (posedge MTxClk or negedge Resetn)
begin
  if(Resetn == 0)
    begin
      PacketFinished <=  1'b0;
      PacketFinished_q  <=  1'b0;
    end
  else
    begin
      PacketFinished <=  PacketFinished_d;
      PacketFinished_q  <=  PacketFinished;
    end
end


// Connecting module Counters
eth_txcounters txcounters1 (.StatePreamble(StatePreamble), .StateIPG(StateIPG), .StateSA(StateSA),.StateDA(StateDA),.StateLength(StateLength),
							.StateData(StateData),.StatePAD(StatePAD), .StateFCS(StateFCS), .StateJam(StateJam), .StateBackOff(StateBackOff), 
                            .StateDefer(StateDefer), .StateIdle(StateIdle), .StartDefer(StartDefer), .StartIPG(StartIPG), 
                            .StartFCS(StartFCS), .StartJam(StartJam), .TxStartFrm(TxStartFrm), .MTxClk(MTxClk), 
                            .Resetn(Resetn), .MinFL(MinFL), .MaxFL(MaxFL), .HugEn(HugEn), .ExDfrEn(ExDfrEn), 
                            .PacketFinished_q(PacketFinished_q), .DlyCrcEn(DlyCrcEn), .StartBackoff(StartBackoff), 
                            .StateSFD(StateSFD), .ByteCnt(ByteCnt), .NibCnt(NibCnt), .ExcessiveDefer(ExcessiveDefer), 
                            .NibCntEq7(NibCntEq7), .NibCntEq15(NibCntEq15), .MaxFrame(MaxFrame), .NibbleMinFl(NibbleMinFl), 
                            .DlyCrcCnt(DlyCrcCnt)
                           );


// Connecting module StateM
eth_txstatem txstatem1 (.MTxClk(MTxClk), .Resetn(Resetn), .ExcessiveDefer(ExcessiveDefer), .CarrierSense(CarrierSense), 
                        .NibCnt(NibCnt[6:0]), .IPGT(IPGT), .IPGR1(IPGR1), .IPGR2(IPGR2), .FullD(FullD), 
                        .TxStartFrm(TxStartFrm), .TxEndFrm(TxEndFrm), .TxUnderRun(TxUnderRun), .Collision(Collision), 
                        .UnderRun(UnderRun), .StartTxDone(StartTxDone), .TooBig(TooBig), .NibCntEq7(NibCntEq7), 
                        .NibCntEq15(NibCntEq15), .MaxFrame(MaxFrame), .Pad(Pad), .No_Preamble(No_Preamble),.CrcEn(CrcEn), 
                        .NibbleMinFl(NibbleMinFl), .RandomEq0(RandomEq0), .ColWindow(ColWindow), .RetryMax(RetryMax), 
                        .NoBckof(NoBckof), .RandomEqByteCnt(RandomEqByteCnt), .StateIdle(StateIdle), 
                        .StateIPG(StateIPG), .StatePreamble(StatePreamble), .StateSFD(StateSFD),.StateSA(StateSA),.StateDA(StateDA),
						.StateLength(StateLength),.StateData(StateData), .StatePAD(StatePAD), 
                        .StateFCS(StateFCS), .StateJam(StateJam), .StateJam_q(StateJam_q), .StateBackOff(StateBackOff), 
                        .StateDefer(StateDefer), .StartFCS(StartFCS), .StartJam(StartJam), .StartBackoff(StartBackoff), 
                        .StartDefer(StartDefer), .DeferIndication(DeferIndication), .StartPreamble(StartPreamble), .StartSFD(StartSFD),
						.StartLength(StartLength),.StartData(StartData), .StartIPG(StartIPG),.StartSA(StartSA),.StartDA(StartDA)
                       );


wire Enable_Crc;
reg [3:0] Data_Crc;
wire Initialize_Crc;

assign Enable_Crc = ~StateFCS;

always@(*)
begin
	case(1)
	StateDA : begin
				Data_Crc[0] = MTxD_d[3];
				Data_Crc[1] = MTxD_d[2];
				Data_Crc[2] = MTxD_d[1];
				Data_Crc[3] = MTxD_d[0];
			  end
	StateSA : begin
				Data_Crc[0] = MTxD_d[3];
				Data_Crc[1] = MTxD_d[2];
				Data_Crc[2] = MTxD_d[1];
				Data_Crc[3] = MTxD_d[0];
			  end
	StateLength : begin
					Data_Crc[0] = MTxD_d[3];
					Data_Crc[1] = MTxD_d[2];
					Data_Crc[2] = MTxD_d[1];
					Data_Crc[3] = MTxD_d[0];
				  end
	StateData[0] : begin
					Data_Crc[0] = TxData[3];
					Data_Crc[1] = TxData[2];
					Data_Crc[2] = TxData[1];
					Data_Crc[3] = TxData[0];
				   end
	StateData[1] : begin
					Data_Crc[0] = TxData[7];
					Data_Crc[1] = TxData[6];
					Data_Crc[2] = TxData[5];
					Data_Crc[3] = TxData[4];
				   end
	default: begin
				Data_Crc[0] = 1'b0;
				Data_Crc[1] = 1'b0;
				Data_Crc[2] = 1'b0;
				Data_Crc[3] = 1'b0;
			 end
	
	endcase
end

assign Initialize_Crc = StateIdle | StatePreamble | StateSFD | (|DlyCrcCnt);	


// Connecting module Crc
eth_crc txcrc (.Clk(MTxClk), .Resetn(Resetn), .Data(Data_Crc), .Enable(Enable_Crc), .Initialize(Initialize_Crc), 
               .Crc(Crc), .CrcError(CrcError)
              );


// Connecting module Random
eth_random random1 (.MTxClk(MTxClk), .Resetn(Resetn), .StateJam(StateJam), .StateJam_q(StateJam_q), .RetryCnt(RetryCnt), 
                    .NibCnt(NibCnt), .ByteCnt(ByteCnt[9:0]), .RandomEq0(RandomEq0), .RandomEqByteCnt(RandomEqByteCnt));




endmodule


//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date:    17:43:06 06/07/2020 
// Design Name: 
// Module Name:    eth_txstatem 
// Project Name: 
// Target Devices: 
// Tool versions: 
// Description: 
//
// Dependencies: 
//
// Revision: 
// Revision 0.01 - File Created
// Additional Comments: 
//
//////////////////////////////////////////////////////////////////////////////////
`include "timescale.v"
module eth_txstatem  (MTxClk, Resetn, ExcessiveDefer, CarrierSense, NibCnt, IPGT, IPGR1, 
                      IPGR2, FullD, TxStartFrm, TxEndFrm, TxUnderRun, Collision, UnderRun, 
                      StartTxDone, TooBig, NibCntEq7, NibCntEq15, MaxFrame, Pad, No_Preamble,CrcEn, 
                      NibbleMinFl, RandomEq0, ColWindow, RetryMax, NoBckof, RandomEqByteCnt,
                      StateIdle, StateIPG, StatePreamble, StateSFD, StateSA, StateDA, StateLength, StateData, StatePAD, StateFCS, 
                      StateJam, StateJam_q, StateBackOff, StateDefer, StartFCS, StartJam, 
                      StartBackoff, StartDefer, DeferIndication, StartPreamble, StartSFD,StartSA,StartDA,StartLength,StartData, StartIPG
                     );

input MTxClk;
input Resetn;
input ExcessiveDefer;
input CarrierSense;
input [6:0] NibCnt;
input [6:0] IPGT;
input [6:0] IPGR1;
input [6:0] IPGR2;
input FullD;
input TxStartFrm;
input TxEndFrm;
input TxUnderRun;
input Collision;
input UnderRun;
input StartTxDone; 
input TooBig;
input NibCntEq7;
input NibCntEq15;
input MaxFrame;
input Pad;
input No_Preamble;
input CrcEn;
input NibbleMinFl;
input RandomEq0;
input ColWindow;
input RetryMax;
input NoBckof;
input RandomEqByteCnt;


output StateIdle;         // Idle state
output StateIPG;          // IPG state
output StatePreamble;     // Preamble state
output StateSFD;		  // SFD State
output StateSA;			  // Source address state
output StateDA;			  // destination address state
output StateLength;		  // Payload length state
output [1:0] StateData;   // Data state
output StatePAD;          // PAD state
output StateFCS;          // FCS state
output StateJam;          // Jam state
output StateJam_q;        // Delayed Jam state
output StateBackOff;      // Backoff state
output StateDefer;        // Defer state

output StartFCS;          // FCS state will be activated in next clock
output StartJam;          // Jam state will be activated in next clock
output StartBackoff;      // Backoff state will be activated in next clock
output StartDefer;        // Defer state will be activated in next clock
output DeferIndication;
output StartPreamble;     // Preamble state will be activated in next clock
output reg StartSFD;	  // SFD state will be activated in next clock
output StartSA;			  // Source Address state will be activated in next clock added
output StartDA;			  // Destination Address state will be activated in next clock added
output StartLength;		  // Payload Length state will be activated in next clock added
output [1:0] StartData;   // Data state will be activated in next clock
output StartIPG;          // IPG state will be activated in next clock

localparam STATE_DEFER = 0,STATE_IPG = 1,STATE_IDLE = 2,STATE_PREAMBLE = 3,STATE_SFD = 4,STATE_DA = 5,STATE_SA = 6,
		STATE_LENGTH = 7,STATE_DATA0 = 8,STATE_DATA1 = 9,STATE_PAD = 10,STATE_FCS = 11,STATE_JAM = 12,STATE_BACKOFF =13;

reg [3:0] state_tx;


wire StateIdle 			= (state_tx == STATE_IDLE);
wire StateIPG 			= (state_tx == STATE_IPG);
wire StatePreamble 		= (state_tx == STATE_PREAMBLE);
wire StateSFD 			= (state_tx == STATE_SFD);
wire StateSA			= (state_tx == STATE_SA);
wire StateDA			= (state_tx == STATE_DA);
wire StateLength		= (state_tx == STATE_LENGTH);
wire [1:0] StateData 	= {(state_tx == STATE_DATA1),(state_tx == STATE_DATA0)};
wire StatePAD 			= (state_tx == STATE_PAD);
wire StateFCS 			= (state_tx == STATE_FCS);
wire StateJam 			= (state_tx == STATE_JAM);
wire StateBackOff 		= (state_tx == STATE_BACKOFF);
wire StateDefer 		= (state_tx == STATE_DEFER);

reg Rule1;
reg StateJam_q;

wire NibCntEq13 = (NibCnt == 'd13);
// Defining the next state
assign StartIPG = (state_tx == STATE_DEFER) & ~ExcessiveDefer & ~CarrierSense;

assign StartIdle = (state_tx == STATE_IPG) & (Rule1 & NibCnt[6:0] >= IPGT | ~Rule1 & NibCnt[6:0] >= IPGR2);

assign StartPreamble = (FullD == 1'b0)? ((state_tx == STATE_IDLE)& TxStartFrm & ~CarrierSense & ~No_Preamble) : ((state_tx == STATE_IDLE)& TxStartFrm & ~No_Preamble);

//Updated by Moschip Team
//Note: 1. Adding below four extra signals inorder to support the Tx_path of Ethernet. 
//		2. Which helps to send the complete ethernet packet 
//		3. Signals are StartSFD,StartSA,StartDA,Startlength.
//		4. Considering preamble,SFD,SA,DA,length are the control information. So cheking for the carriersense.

always @(*)
begin
	if(~No_Preamble)
	begin
			StartSFD = (state_tx == STATE_PREAMBLE) & NibCntEq13;
	end
	else
	begin
		if(FullD == 1'b0)
			StartSFD = ((state_tx == STATE_IDLE) & TxStartFrm & ~CarrierSense);
		else
			StartSFD = ((state_tx == STATE_IDLE) & TxStartFrm);
	end
end

assign StartDA = ((state_tx == STATE_SFD) & NibCnt == 'd1);

assign StartSA = ((state_tx == STATE_DA) & NibCnt == 'd11);

assign StartLength = ((state_tx == STATE_SA) & (NibCnt == 'd11));

assign StartData[0] = ~Collision & ((state_tx == STATE_LENGTH) & (NibCnt == 'd3)| (state_tx == STATE_DATA1) & ~TxEndFrm);

assign StartData[1] = ~Collision & (state_tx == STATE_DATA0) & ~TxUnderRun & ~MaxFrame;

assign StartPAD = ~Collision & (state_tx == STATE_DATA1)& TxEndFrm & Pad & ~NibbleMinFl;

assign StartFCS = ~Collision & (state_tx == STATE_DATA1) & TxEndFrm & (~Pad | Pad & NibbleMinFl) & CrcEn
                | ~Collision & (state_tx == STATE_PAD) & NibbleMinFl & CrcEn;

assign StartJam = (Collision | UnderRun) & (((state_tx == STATE_PREAMBLE) & NibCntEq13)|((state_tx == STATE_SFD)& (NibCnt == 'd1)) 
|((state_tx == STATE_SA) & (NibCnt == 'd11))| (((state_tx == STATE_DA) & (NibCnt == 'd11)))|(((state_tx == STATE_LENGTH) & (NibCnt == 'd3)))|((state_tx == STATE_DATA0)|(state_tx == STATE_DATA1)) | StatePAD | StateFCS);

assign StartBackoff = (state_tx == STATE_JAM) & ~RandomEq0 & ColWindow & ~RetryMax & NibCntEq7 & ~NoBckof;

assign StartDefer = (state_tx == STATE_IPG) & ~Rule1 & CarrierSense & NibCnt[6:0] <= IPGR1 & NibCnt[6:0] != IPGR2
                  | (state_tx == STATE_IDLE) & CarrierSense 
                  | (state_tx == STATE_JAM) & NibCntEq7 & (NoBckof | RandomEq0 | ~ColWindow | RetryMax)
                  | (state_tx == STATE_BACKOFF) & (TxUnderRun | RandomEqByteCnt)
                  | StartTxDone | TooBig;
				  
assign DeferIndication = (state_tx == STATE_IDLE) & CarrierSense;

always @(posedge MTxClk or negedge Resetn)
begin
	if(Resetn == 0)
		StateJam_q <= 1'b0;
	else	
		StateJam_q <= StateJam;
end


	
always@(posedge MTxClk or negedge Resetn)
begin
  if(Resetn == 0)
    begin	
		state_tx <= STATE_DEFER;
	end
  else
  begin
	case(state_tx)
	STATE_DEFER : begin	
						if(StartIPG)
							state_tx <= STATE_IPG;
				  end
	STATE_IPG : begin
					if(StartDefer)
							state_tx <= STATE_DEFER;
					else 
					begin
						if(StartIdle)
							state_tx <= STATE_IDLE;
					end
				  end
	STATE_IDLE	: begin
					if(StartDefer)
						state_tx <= STATE_DEFER;
					else
						if(StartPreamble)
							state_tx <= STATE_PREAMBLE;
						else
						begin
if(StartSFD)
								state_tx <= STATE_SFD;
						end
				  end
	STATE_PREAMBLE : begin
						if(StartJam)
							state_tx <= STATE_JAM;	
						else
							if(StartSFD)
								state_tx <= STATE_SFD;
					 end
	STATE_SFD : begin
				if(StartJam)
					state_tx <= STATE_JAM;
				else
					if(StartDA)
						state_tx <= STATE_DA;
				end
	STATE_DA : begin
				if(StartJam)
					state_tx <= STATE_JAM;
				else
					if(StartSA)
						state_tx <= STATE_SA;
			   end
	STATE_SA: begin
				if(StartJam)
					state_tx <= STATE_JAM;
				else
					if(StartLength)
						state_tx <= STATE_LENGTH;
			  end
	STATE_LENGTH: begin
					if(StartJam)
						state_tx <= STATE_JAM;
					else
						if(StartData[0])
							state_tx <= STATE_DATA0;
				  end
	STATE_DATA0	:begin
					if(StartDefer)
						state_tx <= STATE_DEFER;
					else
					begin
						if(StartJam)	
								state_tx <= STATE_JAM;
						else
						begin
							if(StartData[1])
								state_tx <= STATE_DATA1;
						end
					end
				 end
	STATE_DATA1 : begin
					if(StartDefer)
						state_tx <= STATE_DEFER;
					else 
					begin
						if(StartJam)
							state_tx <= STATE_JAM;
						else
						begin 
							if(StartData[0])
								state_tx <= STATE_DATA0;
							else
							begin
								if(StartPAD)
									state_tx <= STATE_PAD;
								else
								begin
									if(StartFCS)
										state_tx <= STATE_FCS;
								end
							end
						end
					end
				 end
	STATE_PAD:begin
				if(StartJam)
					state_tx <= STATE_JAM;
				else
				begin
					if(StartFCS)
						state_tx <= STATE_FCS;
				end
			  end
	STATE_FCS: begin
				if(StartDefer)
					state_tx <= STATE_DEFER;
				else
				begin
					if(StartJam)
						state_tx <= STATE_JAM;
				end
			   end
	STATE_JAM:begin
				if(StartDefer)
					state_tx <= STATE_DEFER;
				else
				begin
					if(StartBackoff)
						state_tx <= STATE_BACKOFF;
				end
			  end
	STATE_BACKOFF:begin
					if(StartDefer)
						state_tx <= STATE_DEFER;
				  end
	endcase
   end	
 end
			
// This sections defines which interpack gap rule to use
always @ (posedge MTxClk or negedge Resetn)
begin
  if(Resetn == 0)
    Rule1 <=  1'b0;
  else
    begin
      if(StateIdle | StateBackOff)
        Rule1 <=  1'b0;
      else
      if((StatePreamble & ~No_Preamble)|(StateSFD & No_Preamble)| FullD)	
        Rule1 <=  1'b1;
    end
end
			
endmodule


//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date:    17:43:26 06/07/2020 
// Design Name: 
// Module Name:    eth_wishbone 
// Project Name: 
// Target Devices: 
// Tool versions: 
// Description: 
//
// Dependencies: 
//
// Revision: 
// Revision 0.01 - File Created
// Additional Comments: 
//
//////////////////////////////////////////////////////////////////////////////////
`include "ethmac_defines.v"
`include "timescale.v"
module eth_wishbone
  (

   // WISHBONE common
   WB_CLK_I, WB_DAT_I, WB_DAT_O, 

   // WISHBONE slave
   WB_ADDR_I, WB_WE_I, WB_ACK_O, 
   BDCs, 

   Resetn, 

   // WISHBONE master
   m_wb_adr_o, m_wb_sel_o, m_wb_we_o, 
   m_wb_dat_o, m_wb_dat_i, m_wb_cyc_o_delayed_next_state, 
   m_wb_ack_i, m_wb_err_i, 

   m_wb_cti_o, m_wb_bte_o, 

   //TX
   MTxClk, TxStartFrm, TxEndFrm, TxUsedData, TxData, 
   TxRetry, TxAbort, TxUnderRun, TxDone, PerPacketCrcEn, 
   PerPacketPad, 

   //RX
   MRxClk, RxData, RxValid, RxStartFrm, RxEndFrm, RxAbort,
   RxStatusWriteLatched_sync2, 
  
   // Register
   r_TxEn, r_RxEn,r_Pad,r_HugEn,r_MinFL,r_MaxFL, r_TxBDNum, r_RxFlow, r_PassAll, 

   // Interrupts
   TxB_IRQ, TxE_IRQ, RxB_IRQ, RxE_IRQ, Busy_IRQ, 
  
   // Rx Status
   InvalidSymbol, LatchedCrcError, RxLateCollision, ShortFrame, DribbleNibble,
   ReceivedPacketTooBig, RxLength, LoadRxStatus, ReceivedPacketGood,
   AddressMiss, MRxErr_Detected,Length_Vs_Payload_error,Length_vs_payload_mismatch,
   ReceivedPauseFrm, 
  
   // Tx Status
   RetryCntLatched, RetryLimit, LateCollLatched, DeferLatched, RstDeferLatched,
   CarrierSenseLost,BD_TxLength	

   // Bist
`ifdef ETH_BIST
   ,
   // debug chain signals
   mbist_si_i,       // bist scan serial in
   mbist_so_o,       // bist scan serial out
   mbist_ctrl_i        // bist chain shift control
`endif

`ifdef WISHBONE_DEBUG
   ,
   dbg_dat0
`endif


   );

parameter TX_FIFO_DATA_WIDTH = `ETH_TX_FIFO_DATA_WIDTH;
parameter TX_FIFO_DEPTH      = `ETH_TX_FIFO_DEPTH;
parameter TX_FIFO_CNT_WIDTH  = `ETH_TX_FIFO_CNT_WIDTH;
parameter RX_FIFO_DATA_WIDTH = `ETH_RX_FIFO_DATA_WIDTH;
parameter RX_FIFO_DEPTH      = `ETH_RX_FIFO_DEPTH;
parameter RX_FIFO_CNT_WIDTH  = `ETH_RX_FIFO_CNT_WIDTH;

// WISHBONE common
input           WB_CLK_I;       // WISHBONE clock
input  [31:0]   WB_DAT_I;       // WISHBONE data input
output [31:0]   WB_DAT_O;       // WISHBONE data output

// WISHBONE slave
input   [9:2]   WB_ADDR_I;       // WISHBONE address input
input           WB_WE_I;        // WISHBONE write enable input
input   [3:0]   BDCs;           // Buffer descriptors are selected
output          WB_ACK_O;       // WISHBONE acknowledge output

// WISHBONE master
output  [29:0]  m_wb_adr_o;     // 
output   	    m_wb_sel_o;     // 
output          m_wb_we_o;      // 
output  [31:0]  m_wb_dat_o;     // 
output          m_wb_cyc_o_delayed_next_state;     // 
input   [31:0]  m_wb_dat_i;     // 
input           m_wb_ack_i;     // 
input           m_wb_err_i;     // 

output   [2:0]  m_wb_cti_o;     // Cycle Type Identifier
output   [1:0]  m_wb_bte_o;     // Burst Type Extension
reg      [2:0]  m_wb_cti_o;     // Cycle Type Identifier

input           Resetn;       // Resetn signal

// Rx Status signals
input           InvalidSymbol;    // Invalid symbol was received during reception in 100 Mbps mode
input           LatchedCrcError;  // CRC error
input           RxLateCollision;  // Late collision occured while receiving frame
input           ShortFrame;       // Frame shorter then the minimum size
                                  // (r_MinFL) was received while small
                                  // packets are enabled (r_RecSmall)
input           DribbleNibble;    // Extra nibble received
input           ReceivedPacketTooBig;// Received packet is bigger than r_MaxFL
input    [15:0] RxLength;         // Length of the incoming frame
reg      [15:0] RxLength_d;  
input           LoadRxStatus;     // Rx status was loaded
input           ReceivedPacketGood;  // Received packet's length and CRC are
                                     // good
input           AddressMiss;      // When a packet is received AddressMiss
                                  // status is written to the Rx BD
input 			MRxErr_Detected;

input           r_RxFlow;
input           r_PassAll;
input           ReceivedPauseFrm;


// Tx Status signals
input     [3:0] RetryCntLatched;  // Latched Retry Counter
input           RetryLimit;       // Retry limit reached (Retry Max value +1
                                  // attempts were made)
input           LateCollLatched;  // Late collision occured
input           DeferLatched;     // Defer indication (Frame was defered
                                  // before sucessfully sent)
output          RstDeferLatched;
input           CarrierSenseLost; // Carrier Sense was lost during the
                                  // frame transmission

// Tx
input           MTxClk;         // Transmit clock (from PHY)
input           TxUsedData;     // Transmit packet used data
input           TxRetry;        // Transmit packet retry
input           TxAbort;        // Transmit packet abort
input           TxDone;         // Transmission ended
output          TxStartFrm;     // Transmit packet start frame
output          TxEndFrm;       // Transmit packet end frame
output  [7:0]   TxData;         // Transmit packet data byte
output          TxUnderRun;     // Transmit packet under-run
output          PerPacketCrcEn; // Per packet crc enable
output          PerPacketPad;   // Per packet pading

// Rx
input 			Length_Vs_Payload_error;
input 			Length_vs_payload_mismatch;
input           MRxClk;         // Receive clock (from PHY)
input   [7:0]   RxData;         // Received data byte (from PHY)
input           RxValid;        // 
input           RxStartFrm;     // 
input           RxEndFrm;       // 
input           RxAbort;        // This signal is set when address doesn't
                                // match.
output          RxStatusWriteLatched_sync2;

//Register
input           r_TxEn;         // Transmit enable
input           r_RxEn;         // Receive enable
input 			r_Pad;
input 			r_HugEn;
input 	[15:0]	r_MinFL;
input 	[15:0]	r_MaxFL;
input   [7:0]   r_TxBDNum;      // Receive buffer descriptor number
output 	reg [15:0]	BD_TxLength;
// Interrupts
output TxB_IRQ;
output TxE_IRQ;
output RxB_IRQ;
output RxE_IRQ;
output Busy_IRQ;


// Bist
`ifdef ETH_BIST
input   mbist_si_i;       // bist scan serial in
output  mbist_so_o;       // bist scan serial out
input [`ETH_MBIST_CTRL_WIDTH - 1:0] mbist_ctrl_i; // bist chain shift control
`endif

`ifdef WISHBONE_DEBUG
   output [31:0]                       dbg_dat0;
`endif

reg TxB_IRQ;
reg TxE_IRQ;
reg RxB_IRQ;
reg RxE_IRQ;

reg             TxStartFrm;
reg             TxEndFrm;
reg     [7:0]   TxData;

reg             TxUnderRun;
reg             TxUnderRun_wb;

reg             TxBDRead;
wire            TxStatusWrite;
reg            TxStatusWrite_f1;
reg            TxStatusWrite_f2;
reg            TxStatusWrite_f3;
reg            TxStatusWrite_f4;
reg            TxStatusWrite_f5;
reg            TxStatusWrite_f6;

reg     [1:0]   TxValidBytesLatched;

reg    [15:0]   TxLength;
reg    [15:0]   LatchedTxLength;
reg   [14:11]   TxStatus;

reg   [14:13]   RxStatus;

reg             TxStartFrm_wb;
reg             TxRetry_wb;
reg             TxAbort_wb;
reg             TxDone_wb;

reg             TxDone_wb_q;
reg             TxAbort_wb_q;
reg             TxRetry_wb_q;
reg             TxRetryPacket;
reg             TxRetryPacket_NotCleared;
reg             TxDonePacket;
reg             TxDonePacket_NotCleared;
reg             TxAbortPacket;
reg             TxAbortPacket_NotCleared;
reg             RxBDReady;
reg             RxReady;
reg             TxBDReady;

reg             RxBDRead;

reg    [31:0]   TxDataLatched;
reg     [1:0]   TxByteCnt;
reg             LastWord;
reg             ReadTxDataFromFifo_tck;

reg             BlockingTxStatusWrite;
reg             BlockingTxBDRead;

reg             Flop;


reg     [7:1]   TxBDAddress;
reg     [7:1]   RxBDAddress;

reg             TxRetrySync1;
reg             TxAbortSync1;
reg             TxDoneSync1;

reg             TxAbort_q;
reg             TxRetry_q;
reg             TxUsedData_q;

reg    [31:0]   RxDataLatched2;

reg    [31:8]   RxDataLatched1;     // Big Endian Byte Ordering

reg     [1:0]   RxValidBytes;
reg     [1:0]   RxByteCnt;
reg             LastByteIn;
reg             ShiftWillEnd;

reg             WriteRxDataToFifo;
reg    [15:0]   LatchedRxLength;
reg             RxAbortLatched;

reg             ShiftEnded;
reg             RxOverrun;

reg     [3:0]   BDWrite;                    // BD Write Enable for access from WISHBONE side
wire    [3:0]   BDWrite_next;
reg             BDRead;                     // BD Read access from WISHBONE side
wire   [31:0]   RxBDDataIn;                 // Rx BD data in
wire   [31:0]   TxBDDataIn;                 // Tx BD data in

reg             TxEndFrm_wb;

wire            TxRetryPulse;
wire            TxDonePulse;
wire            TxAbortPulse;

wire            StartRxBDRead;

wire            StartTxBDRead;

wire            TxIRQEn;
wire            WrapTxStatusBit;

wire            RxIRQEn;
wire            WrapRxStatusBit;

wire    [1:0]   TxValidBytes;

wire    [7:1]   TempTxBDAddress;
wire    [7:1]   TempRxBDAddress;

wire            RxStatusWrite;
wire            RxBufferFull;
wire            RxBufferAlmostEmpty;
wire            RxBufferEmpty;

reg             WB_ACK_O;

wire    [8:0]   RxStatusIn;
reg     [8:0]   RxStatusInLatched;

reg WbEn, WbEn_q;
reg RxEn, RxEn_q;
reg TxEn, TxEn_q;
reg r_TxEn_q;
reg r_RxEn_q;

wire ram_ce;
wire [3:0]  ram_we;
wire ram_oe;
reg [7:0]   ram_addr;
reg [31:0]  ram_di;
wire [31:0] ram_do;

reg StartTxPointerRead;
reg TxPointerRead;
reg TxEn_needed;
reg RxEn_needed;

wire StartRxPointerRead;
reg RxPointerRead;

// RX shift ending signals
reg ShiftEnded_rck;
reg ShiftEndedSync1;
reg ShiftEndedSync2;
reg ShiftEndedSync3;
reg ShiftEndedSync_c1;
reg ShiftEndedSync_c2;

wire StartShiftWillEnd;

reg StartOccured;
reg TxStartFrm_sync1;
reg TxStartFrm_sync2;
reg TxStartFrm_syncb1;
reg TxStartFrm_syncb2;

wire TxFifoClear;
wire TxBufferAlmostFull;
wire TxBufferFull;
wire TxBufferEmpty;
wire TxBufferAlmostEmpty;
wire SetReadTxDataFromMemory;
reg BlockReadTxDataFromMemory;

reg tx_burst_en;
reg rx_burst_en;
reg  [`ETH_BURST_CNT_WIDTH-1:0] tx_burst_cnt;

wire ReadTxDataFromMemory_2;
wire tx_burst;

reg Tx_BAD_FRAME;
reg Tx_BAD_FRAME_f1;
reg Tx_BAD_FRAME_f2;
reg Tx_BAD_FRAME_f3;
reg Tx_BAD_FRAME_f4;
reg Tx_BAD_FRAME_f5;
reg Tx_BAD_FRAME_f6;

wire [31:0] TxData_wb;
wire ReadTxDataFromFifo_wb;

wire [TX_FIFO_CNT_WIDTH-1:0] txfifo_cnt;
wire [RX_FIFO_CNT_WIDTH-1:0] rxfifo_cnt;

reg  [`ETH_BURST_CNT_WIDTH-1:0] rx_burst_cnt;

wire rx_burst;
wire enough_data_in_rxfifo_for_burst;
wire enough_data_in_rxfifo_for_burst_plus1;

reg ReadTxDataFromMemory;
wire WriteRxDataToMemory;

reg MasterWbTX;
reg MasterWbRX;

reg [29:0] m_wb_adr_o;
reg        m_penable_o_delayed;
reg        m_wb_we_o;
reg [3:0] m_wb_stb_o;

wire TxLengthEq0;
wire TxLengthLt4;

reg BlockingIncrementTxPointer;
reg [31:2] TxPointerMSB;
reg [1:0]  TxPointerLSB;
reg [1:0]  TxPointerLSB_rst;
reg [31:2] RxPointerMSB;
reg [1:0]  RxPointerLSB_rst;

wire RxBurstAcc;
wire RxWordAcc;
wire RxHalfAcc;
wire RxByteAcc;

wire ResetTxBDReady;
reg BlockingTxStatusWrite_sync1;
reg BlockingTxStatusWrite_sync2;
reg BlockingTxStatusWrite_sync3;

reg cyc_cleared;
reg IncrTxPointer;

reg  [3:0] RxByteSel;
wire MasterAccessFinished;

reg LatchValidBytes;
reg LatchValidBytes_q;

// Start: Generation of the ReadTxDataFromFifo_tck signal and synchronization to the WB_CLK_I
reg ReadTxDataFromFifo_sync1;
reg ReadTxDataFromFifo_sync2;
reg ReadTxDataFromFifo_sync3;
reg ReadTxDataFromFifo_syncb1;
reg ReadTxDataFromFifo_syncb2;
reg ReadTxDataFromFifo_syncb3;

reg RxAbortSync1;
reg RxAbortSync2;
reg RxAbortSync3;
reg RxAbortSync4;
reg RxAbortSyncb1;
reg RxAbortSyncb2;

reg RxEnableWindow;

reg SetWriteRxDataToFifo;
//reg[1:0]  stretch_rxfifo_wr_append_0sto_datain;

reg WriteRxDataToFifoSync1;
reg WriteRxDataToFifoSync2;
reg WriteRxDataToFifoSync3;

wire WriteRxDataToFifo_wb;

reg LatchedRxStartFrm;
reg SyncRxStartFrm;
reg SyncRxStartFrm_q;
reg SyncRxStartFrm_q2;
wire RxFifoReset;

wire TxError;
wire RxError;

wire TxLength_error1;
wire TxLength_error2;

reg RxStatusWriteLatched;
reg RxStatusWriteLatched_sync1;
reg RxStatusWriteLatched_sync2;
reg RxStatusWriteLatched_syncb1;
reg RxStatusWriteLatched_syncb2;
reg   m_ack_sig;
reg   m_wb_cyc_o;


assign m_wb_bte_o = 2'b00;    // Linear burst


assign m_wb_sel_o = m_wb_cyc_o;

always @ (posedge WB_CLK_I)
begin
  WB_ACK_O <= (|BDWrite) & WbEn & WbEn_q | BDRead & WbEn & ~WbEn_q;
end

assign WB_DAT_O = ram_do;

// Generic synchronous single-port RAM interface
eth_spram_256x32
     bd_ram
     (
      .clk     (WB_CLK_I),
      .rstn    (Resetn),
      .ce      (ram_ce),
      .we      (ram_we),
      .oe      (ram_oe),
      .addr    (ram_addr),
      .di      (ram_di),
      .dato    (ram_do)
`ifdef ETH_BIST
      ,
      .mbist_si_i       (mbist_si_i),
      .mbist_so_o       (mbist_so_o),
      .mbist_ctrl_i       (mbist_ctrl_i)
`endif
      );

assign ram_ce = 1'b1;
assign ram_we = (BDWrite & {4{(WbEn & WbEn_q)}}) |
                {4{(TxStatusWrite | RxStatusWrite)}};
assign ram_oe = ((BDRead & WbEn & WbEn_q )|( TxEn & TxEn_q &
                (TxBDRead | TxPointerRead)) | (RxEn & RxEn_q &
                (RxBDRead | RxPointerRead)));

always @ (posedge WB_CLK_I or negedge Resetn)
begin
  if(Resetn == 0)
    TxEn_needed <= 1'b0;
  else
  if(~TxBDReady & r_TxEn & WbEn & ~WbEn_q)
    TxEn_needed <= 1'b1;
  else
  if(TxPointerRead & TxEn & TxEn_q)
    TxEn_needed <= 1'b0;
end


assign BDWrite_next = BDCs[3:0] & {4{WB_WE_I}};
// Enabling access to the RAM for three devices.
always @ (posedge WB_CLK_I or negedge Resetn)
begin
  if(Resetn == 0)
    begin
      WbEn <= 1'b1;
      RxEn <= 1'b0;
      TxEn <= 1'b0;
      ram_addr <= 8'h0;
      ram_di <= 32'h0;
      BDRead <= 1'b0;
      BDWrite <= 0;
    end
  else
    begin
      // Switching between three stages depends on enable signals
     /* verilator lint_off CASEINCOMPLETE */ // JB
      case ({WbEn_q, RxEn_q, TxEn_q, RxEn_needed, TxEn_needed})  // synopsys parallel_case
        5'b100_10, 5'b100_11 :
          begin
            WbEn <= 1'b0;
            RxEn <= 1'b1;  // wb access stage and r_RxEn is enabled
            TxEn <= 1'b0;
            ram_addr <= {RxBDAddress, RxPointerRead};
            ram_di <= RxBDDataIn;
          end
        5'b100_01 :
          begin
            WbEn <= 1'b0;
            RxEn <= 1'b0;
            TxEn <= 1'b1;  // wb access stage, r_RxEn is disabled but
                           // r_TxEn is enabled
            ram_addr <= {TxBDAddress, TxPointerRead};
            ram_di <= TxBDDataIn;
          end
        5'b010_00, 5'b010_10 :
          begin
            WbEn <= 1'b1;  // RxEn access stage and r_TxEn is disabled
            RxEn <= 1'b0;
            TxEn <= 1'b0;
            ram_addr <= WB_ADDR_I[9:2];
            ram_di <= WB_DAT_I;
			BDWrite <= BDWrite_next;
            BDRead <= (|BDCs) & ~WB_WE_I;
          end
        5'b010_01, 5'b010_11 :
          begin
            WbEn <= 1'b0;
            RxEn <= 1'b0;
            TxEn <= 1'b1;  // RxEn access stage and r_TxEn is enabled
            ram_addr <= {TxBDAddress, TxPointerRead};
            ram_di <= TxBDDataIn;
          end
        5'b001_00, 5'b001_01, 5'b001_10, 5'b001_11 :
          begin
            WbEn <= 1'b1;  // TxEn access stage (we always go to wb
                           // access stage)
            RxEn <= 1'b0;
            TxEn <= 1'b0;
            ram_addr <= WB_ADDR_I[9:2];
            ram_di <= WB_DAT_I;
			BDWrite <= BDWrite_next;
            BDRead <= (|BDCs) & ~WB_WE_I;
          end
        5'b100_00 :
          begin
            WbEn <= 1'b0;  // WbEn access stage and there is no need
                           // for other stages. WbEn needs to be
                           // switched off for a bit
          end
        5'b000_00 :
          begin
            WbEn <= 1'b1;  // Idle state. We go to WbEn access stage.
            RxEn <= 1'b0;
            TxEn <= 1'b0;
            ram_addr <= WB_ADDR_I[9:2];
            ram_di <= WB_DAT_I;
			BDWrite <= BDWrite_next;
            BDRead <= (|BDCs) & ~WB_WE_I;
          end
      endcase
      /* verilator lint_on CASEINCOMPLETE */
    end
end


// Delayed stage signals
always @ (posedge WB_CLK_I or negedge Resetn)
begin
  if(Resetn == 0)
    begin
      WbEn_q <= 1'b0;
      RxEn_q <= 1'b0;
      TxEn_q <= 1'b0;
      r_TxEn_q <= 1'b0;
      r_RxEn_q <= 1'b0;
    end
  else
    begin
      WbEn_q <= WbEn;
      RxEn_q <= RxEn;
      TxEn_q <= TxEn;
      r_TxEn_q <= r_TxEn;
      r_RxEn_q <= r_RxEn;
    end
end

// Changes for tx occur every second clock. Flop is used for this manner.
always @ (posedge MTxClk or negedge Resetn)
begin
  if(Resetn == 0)
    Flop <= 1'b0;
  else
  if(TxDone | TxAbort | TxRetry_q)
    Flop <= 1'b0;
  else
  if(TxUsedData)
    Flop <= ~Flop;
end



assign ResetTxBDReady = TxDonePulse | TxAbortPulse | TxRetryPulse | Tx_BAD_FRAME; 

// Latching READY status of the Tx buffer descriptor
always @(posedge WB_CLK_I or negedge Resetn)
begin
  if(Resetn == 0)
    TxBDReady <= 1'b0;
  else
  if(TxEn & TxEn_q & TxBDRead)
    // TxBDReady is sampled only once at the beginning.
    TxBDReady <= ram_do[15] & (ram_do[31:16] > 4);
  else
  // Only packets larger then 4 bytes are transmitted.
  if(ResetTxBDReady)
    TxBDReady <= 1'b0;
end

// Reading the Tx buffer descriptor
assign StartTxBDRead = (TxRetryPacket_NotCleared | TxStatusWrite_f6 ) &
                       ~BlockingTxBDRead & ~TxBDReady;

always @(posedge WB_CLK_I or negedge Resetn)
begin
  if(Resetn == 0)
    TxBDRead <= 1'b1;
  else
   if(StartTxBDRead) 
    begin
		TxBDRead <= 1'b1;
    end
  else
  if(TxBDReady)
    TxBDRead <= 1'b0;
end
// Reading Tx BD pointer

always@(*)
begin

	if(TxBDRead & TxBDReady)
	begin
		if((BD_TxLength + 'd18) < r_MinFL)
			begin
			if(r_Pad==1)
				begin
					StartTxPointerRead = 1;
					Tx_BAD_FRAME = 0;
				end
				else
				begin
					StartTxPointerRead = 0;
					Tx_BAD_FRAME = 1;
				end
			end
		else if((BD_TxLength + 'd18) > r_MaxFL)	//The frame should be less than are equal to 2kb
			begin 
				if(r_HugEn && ((BD_TxLength + 'd18) <= 'd2048))
				begin
					StartTxPointerRead = 1;
					Tx_BAD_FRAME = 0;
				end
				else
				begin
					StartTxPointerRead = 0;
					Tx_BAD_FRAME = 1;
				end
			end
		else begin
			StartTxPointerRead = 1; 
			Tx_BAD_FRAME = 0;
			end
	end
	else
	begin
		StartTxPointerRead = 0;
		Tx_BAD_FRAME = 0;
	end
end
//Added by Moschip team
// Reading Tx BD Pointer
always @ (posedge WB_CLK_I or negedge Resetn)
begin
  if(Resetn == 0)
    TxPointerRead <= 1'b0;
  else
  if(StartTxPointerRead)
    TxPointerRead <= 1'b1;
  else
  if(TxEn_q)
    TxPointerRead <= 1'b0;
end


// Writing status back to the Tx buffer descriptor
assign TxStatusWrite = ((TxDonePacket_NotCleared | TxAbortPacket_NotCleared) &
                       TxEn & TxEn_q & ~BlockingTxStatusWrite) | Tx_BAD_FRAME_f6;

//Note: When BAD frame comes, the int_o signal is generated at sametime for good and bad frame
always @(posedge WB_CLK_I or negedge Resetn)
begin
  if(Resetn == 0)
  begin
	TxStatusWrite_f1 <= 0;
	TxStatusWrite_f2 <= 0;
	TxStatusWrite_f3 <= 0;
	TxStatusWrite_f4 <= 0;
	TxStatusWrite_f5 <= 0;
	TxStatusWrite_f6 <= 0;
  end	
  else
  begin 			  
	TxStatusWrite_f1 <= TxStatusWrite; 
	TxStatusWrite_f2 <= TxStatusWrite_f1; 
	TxStatusWrite_f3 <= TxStatusWrite_f2; 
	TxStatusWrite_f4 <= TxStatusWrite_f3; 
	TxStatusWrite_f5 <= TxStatusWrite_f4; 
	TxStatusWrite_f6 <= TxStatusWrite_f5; 
  end
end

always @(posedge WB_CLK_I or negedge Resetn)
begin
  if(Resetn == 0)
  begin
	Tx_BAD_FRAME_f1 <= 0;
	Tx_BAD_FRAME_f2 <= 0;
	Tx_BAD_FRAME_f3 <= 0;
	Tx_BAD_FRAME_f4 <= 0;
	Tx_BAD_FRAME_f5 <= 0;
	Tx_BAD_FRAME_f6 <= 0;
  end	
  else
  begin 			  
	Tx_BAD_FRAME_f1 <= Tx_BAD_FRAME; 
	Tx_BAD_FRAME_f2 <= Tx_BAD_FRAME_f1; 
	Tx_BAD_FRAME_f3 <= Tx_BAD_FRAME_f2; 
	Tx_BAD_FRAME_f4 <= Tx_BAD_FRAME_f3; 
	Tx_BAD_FRAME_f5 <= Tx_BAD_FRAME_f4; 
	Tx_BAD_FRAME_f6 <= Tx_BAD_FRAME_f5; 
  end
end


// Status writing must occur only once. Meanwhile it is blocked.
always @ (posedge WB_CLK_I or negedge Resetn)
begin
  if(Resetn == 0)
    BlockingTxStatusWrite <= 1'b0;
  else
  if(~TxDone_wb & ~TxAbort_wb)
    BlockingTxStatusWrite <= 1'b0;
  else
  if(TxStatusWrite_f6)
    BlockingTxStatusWrite <= 1'b1;
end


// Synchronizing BlockingTxStatusWrite to MTxClk
always @ (posedge MTxClk or negedge Resetn)
begin
  if(Resetn == 0)
    BlockingTxStatusWrite_sync1 <= 1'b0;
  else
    BlockingTxStatusWrite_sync1 <= BlockingTxStatusWrite;
end

// Synchronizing BlockingTxStatusWrite to MTxClk
always @ (posedge MTxClk or negedge Resetn)
begin
  if(Resetn == 0)
    BlockingTxStatusWrite_sync2 <= 1'b0;
  else
    BlockingTxStatusWrite_sync2 <= BlockingTxStatusWrite_sync1;
end

// Synchronizing BlockingTxStatusWrite to MTxClk
always @ (posedge MTxClk or negedge Resetn)
begin
  if(Resetn == 0)
    BlockingTxStatusWrite_sync3 <= 1'b0;
  else
    BlockingTxStatusWrite_sync3 <= BlockingTxStatusWrite_sync2;
end

assign RstDeferLatched = BlockingTxStatusWrite_sync2 &
                         ~BlockingTxStatusWrite_sync3;

// TxBDRead state is activated only once. 
always @ (posedge WB_CLK_I or negedge Resetn)
begin
  if(Resetn == 0)
    BlockingTxBDRead <= 1'b0;
  else
  if(StartTxBDRead)
    BlockingTxBDRead <= 1'b1;
  else
  if(~StartTxBDRead & ~TxBDReady)
    BlockingTxBDRead <= 1'b0;
end


// Latching status from the tx buffer descriptor
// Data is avaliable one cycle after the access is started (at that time
// signal TxEn is not active)

always @ (posedge WB_CLK_I or negedge Resetn)
begin
  if(Resetn == 0)
    TxStatus <= 4'h0;
  else
  if(TxEn & TxEn_q & TxBDRead)
    TxStatus <= ({ram_do[14],1'b0,1'b0,1'b1});
end

//adding

always @ (posedge WB_CLK_I or negedge Resetn)
begin
	if(Resetn == 0)
		BD_TxLength <= 16'h0;
	else
	begin
		if(TxEn & TxEn_q & TxBDRead)
			BD_TxLength <= ram_do[31:16];
	end
end

//Latching length from the buffer descriptor;
always @ (posedge WB_CLK_I or negedge Resetn)
begin
  if(Resetn == 0)
    TxLength <= 16'h0;
  else
  if(TxEn & TxEn_q & TxBDRead)
    TxLength <= ram_do[31:16];
  else
  if(MasterWbTX & m_ack_sig)
    begin
      if(TxLengthLt4)
        TxLength <= 16'h0;
      else if(TxPointerLSB_rst==2'h0)
        TxLength <= TxLength - 16'd4;    // Length is subtracted at
                                        // the data request
      else if(TxPointerLSB_rst==2'h1)
        TxLength <= TxLength - 16'd3;    // Length is subtracted
                                         // at the data request
      else if(TxPointerLSB_rst==2'h2)
        TxLength <= TxLength - 16'd2;    // Length is subtracted
                                         // at the data request
      else if(TxPointerLSB_rst==2'h3)
        TxLength <= TxLength - 16'd1;    // Length is subtracted
                                         // at the data request
    end
	
end

//Latching length from the buffer descriptor;
always @ (posedge WB_CLK_I or negedge Resetn)
begin
  if(Resetn == 0)
    LatchedTxLength <= 16'h0;
  else
  if(TxEn & TxEn_q & TxBDRead)
    LatchedTxLength <= ram_do[31:16];
end

assign TxLengthEq0 = TxLength == 0;
assign TxLengthLt4 = TxLength < 4;


// Latching Tx buffer pointer from buffer descriptor. Only 30 MSB bits are
// latched because TxPointerMSB is only used for word-aligned accesses.
always @ (posedge WB_CLK_I or negedge Resetn)
begin
  if(Resetn == 0)
    TxPointerMSB <= 30'h0;
  else
  if(TxEn & TxEn_q & TxPointerRead)
    TxPointerMSB <= ram_do[31:2];
  else
  if(IncrTxPointer & ~BlockingIncrementTxPointer)
    TxPointerMSB <= TxPointerMSB + 1'b1;
end


// Latching 2 MSB bits of the buffer descriptor. Since word accesses are
// performed, valid data does not necesserly start at byte 0 (could be byte
// 0, 1, 2 or 3). This signals are used for proper selection of the start
// byte (TxData and TxByteCnt) are set by this two bits.
always @ (posedge WB_CLK_I or negedge Resetn)
begin
  if(Resetn == 0)
    TxPointerLSB[1:0] <= 0;
  else
  if(TxEn & TxEn_q & TxPointerRead)
    TxPointerLSB[1:0] <= ram_do[1:0];
end


// Latching 2 MSB bits of the buffer descriptor. 
// After the read access, TxLength needs to be decremented for the number of
// the valid bytes (1 to 4 bytes are valid in the first word). After the
// first read all bytes are valid so this two bits are Resetn to zero. 
always @ (posedge WB_CLK_I or negedge Resetn)
begin
  if(Resetn == 0)
    TxPointerLSB_rst[1:0] <= 0;
  else
  if(TxEn & TxEn_q & TxPointerRead)
    TxPointerLSB_rst[1:0] <= ram_do[1:0];
  else
// After first access pointer is word alligned
  if(MasterWbTX & m_ack_sig)
    TxPointerLSB_rst[1:0] <= 0;
end


always @ (posedge WB_CLK_I or negedge Resetn)
begin
  if(Resetn == 0)
    BlockingIncrementTxPointer <= 0;
  else
  if(MasterAccessFinished)
    BlockingIncrementTxPointer <= 0;
  else
  if(IncrTxPointer)
    BlockingIncrementTxPointer <= 1'b1;
end


assign SetReadTxDataFromMemory = TxEn & TxEn_q & TxPointerRead;

always @ (posedge WB_CLK_I or negedge Resetn)
begin
  if(Resetn == 0)
    ReadTxDataFromMemory <= 1'b0;
  else
  if(TxLengthEq0 | TxAbortPulse | TxRetryPulse)
    ReadTxDataFromMemory <= 1'b0;
  else
  if(SetReadTxDataFromMemory)
    ReadTxDataFromMemory <= 1'b1;
end

assign ReadTxDataFromMemory_2 = ReadTxDataFromMemory &
                                ~BlockReadTxDataFromMemory;

assign tx_burst = ReadTxDataFromMemory_2 & tx_burst_en;

always @ (posedge WB_CLK_I or negedge Resetn)
begin
  if(Resetn == 0)
    BlockReadTxDataFromMemory <= 1'b0;
  else
  if((TxBufferAlmostFull | TxLength <= 4) & MasterWbTX & (~cyc_cleared) &
     (!(TxAbortPacket_NotCleared | TxRetryPacket_NotCleared)))
    BlockReadTxDataFromMemory <= 1'b1;
  else
  if(ReadTxDataFromFifo_wb | TxDonePacket | TxAbortPacket | TxRetryPacket)
    BlockReadTxDataFromMemory <= 1'b0;
end


assign MasterAccessFinished = m_ack_sig | m_wb_err_i;

//adding statemachine 
//Note: Making wishbone signals to compatible with apb protocol
//		Inorder to acheive apb protocol rules generating the expected penable(m_wb_cyc_o_delayed_next_state) signal using below state machine 
//		Also generating the pready(m_ack_sig) signal, when the wishbone is capturing the data. 


localparam IDLE = 0,STATE1 = 1,STATE0 = 2;
reg [1:0] state;
reg m_wb_cyc_o_delayed_next_state;
always @(posedge WB_CLK_I or negedge Resetn)
begin
  if(Resetn == 0)
   state <= IDLE;
  else
   begin
	  case(state)
	     IDLE: state <= m_wb_cyc_o === 1? STATE1:IDLE;
		 STATE1: state <= m_wb_ack_i === 1?STATE0:STATE1;
		 STATE0: state <= m_wb_cyc_o === 1?STATE1:STATE0;
	  endcase
	end
end

always@(*)
begin
  case(state)
    IDLE: begin 
				m_wb_cyc_o_delayed_next_state = 0;
				m_ack_sig = 0;
			end
	 STATE1: begin
				m_wb_cyc_o_delayed_next_state = m_wb_cyc_o;
				m_ack_sig = m_wb_ack_i;
				end
	 STATE0: begin 
				m_wb_cyc_o_delayed_next_state = 0;
				m_ack_sig = 0;
				end
  endcase
end



// Enabling master wishbone access to the memory for two devices TX and RX.
always @ (posedge WB_CLK_I or negedge Resetn)
begin
  if(Resetn == 0)
    begin
      MasterWbTX <= 1'b0;
      MasterWbRX <= 1'b0;
      m_wb_adr_o <= 30'h0;
      m_wb_cyc_o <= 1'b0;
      m_wb_we_o  <= 1'b0;
      m_wb_stb_o <= 4'h0;
      cyc_cleared<= 1'b0;
      tx_burst_cnt<= 0;
      rx_burst_cnt<= 0;
      IncrTxPointer<= 1'b0;
      tx_burst_en<= 1'b1;
      rx_burst_en<= 1'b0;
      m_wb_cti_o <= 3'b0;
    end
  else
    begin
      // Switching between two stages depends on enable signals
      casez ({MasterWbTX,
             MasterWbRX,
             ReadTxDataFromMemory_2,
             WriteRxDataToMemory,
             MasterAccessFinished,
             cyc_cleared,
             tx_burst,
             rx_burst})  // synopsys parallel_case

        8'b00_10_00_10, // Idle and MRB needed
        8'b10_1?_10_1?, // MRB continues
        8'b10_10_01_10, // Clear (previously MR) and MRB needed
        8'b01_1?_01_1?: // Clear (previously MW) and MRB needed
          begin
            MasterWbTX <= 1'b1;  // tx burst
            MasterWbRX <= 1'b0;
            m_wb_cyc_o <= 1'b1;
            m_wb_we_o  <= 1'b0;
            m_wb_stb_o <= 4'hf;
            cyc_cleared<= 1'b0;
            IncrTxPointer<= 1'b1;
            tx_burst_cnt <= tx_burst_cnt+3'h1;
            if(tx_burst_cnt==0)
              m_wb_adr_o <= TxPointerMSB;
            else
              m_wb_adr_o <= m_wb_adr_o + 1'b1;
            if(tx_burst_cnt==(`ETH_BURST_LENGTH-1))
              begin
                tx_burst_en<= 1'b0;
                m_wb_cti_o <= 3'b111;
              end
            else
              begin
                m_wb_cti_o <= 3'b010;
              end
          end
        8'b00_?1_00_?1,             // Idle and MWB needed
        8'b01_?1_10_?1,             // MWB continues
        8'b01_01_01_01,             // Clear (previously MW) and MWB needed
        8'b10_?1_01_?1 :            // Clear (previously MR) and MWB needed
          begin
            MasterWbTX <= 1'b0;  // rx burst
            MasterWbRX <= 1'b1;
            m_wb_cyc_o <= 1'b1;
            m_wb_we_o  <= 1'b1;
            m_wb_stb_o <= RxByteSel;
            IncrTxPointer<= 1'b0;
            cyc_cleared<= 1'b0;
            rx_burst_cnt <= rx_burst_cnt+3'h1;

            if(rx_burst_cnt==0)
              m_wb_adr_o <= RxPointerMSB;
            else
              m_wb_adr_o <= m_wb_adr_o+1'b1;

            if(rx_burst_cnt==(`ETH_BURST_LENGTH-1))
              begin
                rx_burst_en<= 1'b0;
                m_wb_cti_o <= 3'b111;
              end
            else
              begin
                m_wb_cti_o <= 3'b010;
              end
          end
        8'b00_?1_00_?0 :// idle and MW is needed (data write to rx buffer)
          begin
            MasterWbTX <= 1'b0;
            MasterWbRX <= 1'b1;
            m_wb_adr_o <= RxPointerMSB;
            m_wb_cyc_o <= 1'b1;
            m_wb_we_o  <= 1'b1;
            m_wb_stb_o <= RxByteSel;
            IncrTxPointer<= 1'b0;
          end
        8'b00_10_00_00 : // idle and MR is needed (data read from tx buffer)
          begin
            MasterWbTX <= 1'b1;
            MasterWbRX <= 1'b0;
            m_wb_adr_o <= TxPointerMSB;
            m_wb_cyc_o <= 1'b1;
            m_wb_we_o  <= 1'b0;
            m_wb_stb_o <= 4'hf;
            IncrTxPointer<= 1'b1;
          end
        8'b10_10_01_00,// MR and MR is needed (data read from tx buffer)
        8'b01_1?_01_0?  :// MW and MR is needed (data read from tx buffer)
          begin
            MasterWbTX <= 1'b1;
            MasterWbRX <= 1'b0;
            m_wb_adr_o <= TxPointerMSB;
            m_wb_cyc_o <= 1'b1;
            m_wb_we_o  <= 1'b0;
            m_wb_stb_o <= 4'hf;
            cyc_cleared<= 1'b0;
            IncrTxPointer<= 1'b1;
          end
        8'b01_01_01_00,// MW and MW needed (data write to rx buffer)
        8'b10_?1_01_?0 :// MR and MW is needed (data write to rx buffer)
          begin
            MasterWbTX <= 1'b0;
            MasterWbRX <= 1'b1;
            m_wb_adr_o <= RxPointerMSB;
            m_wb_cyc_o <= 1'b1;
            m_wb_we_o  <= 1'b1;
            m_wb_stb_o <= RxByteSel;
            cyc_cleared<= 1'b0;
            IncrTxPointer<= 1'b0;
          end
        8'b01_01_10_00,// MW and MW needed (cycle is cleared between
                      // previous and next access)
        8'b01_1?_10_?0,// MW and MW or MR or MRB needed (cycle is
                    // cleared between previous and next access)
        8'b10_10_10_00,// MR and MR needed (cycle is cleared between
                       // previous and next access)
        8'b10_?1_10_0? :// MR and MR or MW or MWB (cycle is cleared
                       // between previous and next access)
          begin
            m_wb_cyc_o <= 1'b0;// whatever and master read or write is
                               // needed. We need to clear m_wb_cyc_o
                               // before next access is started
            cyc_cleared<= 1'b1;
            IncrTxPointer<= 1'b0;
            tx_burst_cnt<= 0;
            tx_burst_en<= txfifo_cnt<(TX_FIFO_DEPTH-`ETH_BURST_LENGTH) & (TxLength>(`ETH_BURST_LENGTH*4+4));
            rx_burst_cnt<= 0;
            rx_burst_en<= MasterWbRX ? enough_data_in_rxfifo_for_burst_plus1 : enough_data_in_rxfifo_for_burst;  // Counter is not decremented, yet, so plus1 is used.
              m_wb_cti_o <= 3'b0;
          end
        8'b??_00_10_00,// whatever and no master read or write is needed
                       // (ack or err comes finishing previous access)
        8'b??_00_01_00 : // Between cyc_cleared request was cleared
          begin
            MasterWbTX <= 1'b0;
            MasterWbRX <= 1'b0;
            m_wb_cyc_o <= 1'b0;
            cyc_cleared<= 1'b0;
            IncrTxPointer<= 1'b0;
            rx_burst_cnt<= 0;
            // Counter is not decremented, yet, so plus1 is used.
            rx_burst_en<= MasterWbRX ? enough_data_in_rxfifo_for_burst_plus1 :
                                       enough_data_in_rxfifo_for_burst;
            m_wb_cti_o <= 3'b0;
          end
        8'b00_00_00_00:  // whatever and no master read or write is needed
                         // (ack or err comes finishing previous access)
          begin
            tx_burst_cnt<= 0;
            tx_burst_en<= txfifo_cnt<(TX_FIFO_DEPTH-`ETH_BURST_LENGTH) & (TxLength>(`ETH_BURST_LENGTH*4+4));
          end
        default:                    // Don't touch
          begin
            MasterWbTX <= MasterWbTX;
            MasterWbRX <= MasterWbRX;
            m_wb_cyc_o <= m_wb_cyc_o;
            m_wb_stb_o <= m_wb_stb_o;
            IncrTxPointer<= IncrTxPointer;
          end
      endcase
    end
end


assign TxFifoClear = (TxAbortPacket | TxRetryPacket);

eth_fifo
     #(
       .DATA_WIDTH(TX_FIFO_DATA_WIDTH),
       .DEPTH(TX_FIFO_DEPTH),
       .CNT_WIDTH(TX_FIFO_CNT_WIDTH))
tx_fifo (
       .data_in(m_wb_dat_i),
       .data_out(TxData_wb),
       .clk(WB_CLK_I),
       .resetn(Resetn),
       .write(MasterWbTX & m_ack_sig),
       .read(ReadTxDataFromFifo_wb & ~TxBufferEmpty),
       .clear(TxFifoClear),
       .full(TxBufferFull), 
       .almost_full(TxBufferAlmostFull),
       .almost_empty(TxBufferAlmostEmpty),
       .empty(TxBufferEmpty),
       .cnt(txfifo_cnt)
       );

// Start: Generation of the TxStartFrm_wb which is then synchronized to the
// MTxClk
always @ (posedge WB_CLK_I or negedge Resetn)
begin
  if(Resetn == 0)
    TxStartFrm_wb <= 1'b0;
  else
  if(TxBDReady & ~StartOccured & (TxBufferFull | TxLengthEq0))
    TxStartFrm_wb <= 1'b1;
  else
  if(TxStartFrm_syncb2)
    TxStartFrm_wb <= 1'b0;
end

// StartOccured: TxStartFrm_wb occurs only ones at the beginning. Then it's
// blocked.
always @ (posedge WB_CLK_I or negedge Resetn)
begin
  if(Resetn == 0)
    StartOccured <= 1'b0;
  else
  if(TxStartFrm_wb)
    StartOccured <= 1'b1;
  else
  if(ResetTxBDReady)
    StartOccured <= 1'b0;
end

// Synchronizing TxStartFrm_wb to MTxClk
always @ (posedge MTxClk or negedge Resetn)
begin
  if(Resetn == 0)
    TxStartFrm_sync1 <= 1'b0;
  else
    TxStartFrm_sync1 <= TxStartFrm_wb;
end

always @ (posedge MTxClk or negedge Resetn)
begin
  if(Resetn == 0)
    TxStartFrm_sync2 <= 1'b0;
  else
    TxStartFrm_sync2 <= TxStartFrm_sync1;
end

always @ (posedge WB_CLK_I or negedge Resetn)
begin
  if(Resetn == 0)
    TxStartFrm_syncb1 <= 1'b0;
  else
    TxStartFrm_syncb1 <= TxStartFrm_sync2;
end

always @ (posedge WB_CLK_I or negedge Resetn)
begin
  if(Resetn == 0)
    TxStartFrm_syncb2 <= 1'b0;
  else
    TxStartFrm_syncb2 <= TxStartFrm_syncb1;
end

always @ (posedge MTxClk or negedge Resetn)
begin
  if(Resetn == 0)
    TxStartFrm <= 1'b0;
  else
  if(TxStartFrm_sync2)
    TxStartFrm <= 1'b1;
  else
  if(TxUsedData_q | ~TxStartFrm_sync2 &
     (TxRetry & (~TxRetry_q) | TxAbort & (~TxAbort_q)))
    TxStartFrm <= 1'b0;
end
// End: Generation of the TxStartFrm_wb which is then synchronized to the
// MTxClk


// TxEndFrm_wb: indicator of the end of frame
always @ (posedge WB_CLK_I or negedge Resetn)
begin
  if(Resetn == 0)
    TxEndFrm_wb <= 1'b0;
  else
  if(TxLengthEq0 & TxBufferAlmostEmpty & TxUsedData)
    TxEndFrm_wb <= 1'b1;
  else
  if(TxRetryPulse | TxDonePulse | TxAbortPulse)
    TxEndFrm_wb <= 1'b0;
end

// Marks which bytes are valid within the word.
assign TxValidBytes = TxLengthLt4 ? TxLength[1:0] : 2'b0;


always @ (posedge WB_CLK_I or negedge Resetn)
begin
  if(Resetn == 0)
    LatchValidBytes <= 1'b0;
  else
  if(TxLengthLt4 & TxBDReady)
    LatchValidBytes <= 1'b1;
  else
    LatchValidBytes <= 1'b0;
end

always @ (posedge WB_CLK_I or negedge Resetn)
begin
  if(Resetn == 0)
    LatchValidBytes_q <= 1'b0;
  else
    LatchValidBytes_q <= LatchValidBytes;
end


// Latching valid bytes
always @ (posedge WB_CLK_I or negedge Resetn)
begin
  if(Resetn == 0)
    TxValidBytesLatched <= 2'h0;
  else
  if(LatchValidBytes & ~LatchValidBytes_q)
    TxValidBytesLatched <= TxValidBytes;
  else
  if(TxRetryPulse | TxDonePulse | TxAbortPulse)
    TxValidBytesLatched <= 2'h0;
end


assign TxIRQEn          = TxStatus[14];
assign WrapTxStatusBit  = TxStatus[13];
assign PerPacketPad     = TxStatus[12];
assign PerPacketCrcEn   = TxStatus[11];


assign RxIRQEn         = RxStatus[14];
assign WrapRxStatusBit = RxStatus[13];


// Temporary Tx and Rx buffer descriptor address
assign TempTxBDAddress[7:1] = {7{ TxStatusWrite_f6  & ~WrapTxStatusBit}} &
                              (TxBDAddress + 1'b1); // Tx BD increment or wrap
                                                    // (last BD)

assign TempRxBDAddress[7:1] = 
  {7{ WrapRxStatusBit}} & (r_TxBDNum[6:0]) | // Using first Rx BD
  {7{~WrapRxStatusBit}} & (RxBDAddress + 1'b1); // Using next Rx BD
                                                // (increment address)

// Latching Tx buffer descriptor address
always @ (posedge WB_CLK_I or negedge Resetn)
begin
  if(Resetn == 0)
    TxBDAddress <= 7'h0;
  else if (r_TxEn & (~r_TxEn_q))
    TxBDAddress <= 7'h0;
  else if (TxStatusWrite_f6)
    TxBDAddress <= TempTxBDAddress;
end

// Latching Rx buffer descriptor address
always @ (posedge WB_CLK_I or negedge Resetn)
begin
  if(Resetn == 0)
    RxBDAddress <= 7'h0;
  else if(r_RxEn & (~r_RxEn_q))
    RxBDAddress <= r_TxBDNum[6:0];
  else if(RxStatusWrite)
    RxBDAddress <= TempRxBDAddress;
end

//Added by Moschip team on June 10 2020

wire [8:0] TxStatusInLatched = {1'b0, 4'h0,
                                1'b0, 1'b0, 1'b0,
                                1'b0};
								
//Added by Moschip team on June 29 2020
assign RxBDDataIn = {(LatchedRxLength -'d4), 1'b0, RxStatus, 4'h0, RxStatusInLatched};
assign TxBDDataIn = {LatchedTxLength, 1'b0, TxStatus, 2'h0, TxStatusInLatched};


// Signals used for various purposes
assign TxRetryPulse   = TxRetry_wb   & ~TxRetry_wb_q;
assign TxDonePulse    = TxDone_wb    & ~TxDone_wb_q;
assign TxAbortPulse   = TxAbort_wb   & ~TxAbort_wb_q;


// Generating delayed signals
always @ (posedge MTxClk or negedge Resetn)
begin
  if(Resetn == 0)
    begin
      TxAbort_q      <= 1'b0;
      TxRetry_q      <= 1'b0;
      TxUsedData_q   <= 1'b0;
    end
  else
    begin
      TxAbort_q      <= TxAbort;
      TxRetry_q      <= TxRetry;
      TxUsedData_q   <= TxUsedData;
    end
end

// Generating delayed signals
always @ (posedge WB_CLK_I or negedge Resetn)
begin
  if(Resetn == 0)
    begin
      TxDone_wb_q   <= 1'b0;
      TxAbort_wb_q  <= 1'b0;
      TxRetry_wb_q  <= 1'b0;
    end
  else
    begin
      TxDone_wb_q   <= TxDone_wb;
      TxAbort_wb_q  <= TxAbort_wb;
      TxRetry_wb_q  <= TxRetry_wb;
    end
end


reg TxAbortPacketBlocked;
always @ (posedge WB_CLK_I or negedge Resetn)
begin
  if(Resetn == 0)
    TxAbortPacket <= 1'b0;
  else
  if(TxAbort_wb & (~tx_burst_en) & MasterWbTX & MasterAccessFinished &
    (~TxAbortPacketBlocked) | TxAbort_wb & (~MasterWbTX) &
    (~TxAbortPacketBlocked))
    TxAbortPacket <= 1'b1;
  else
    TxAbortPacket <= 1'b0;
end


always @ (posedge WB_CLK_I or negedge Resetn)
begin
  if(Resetn == 0)
    TxAbortPacket_NotCleared <= 1'b0;
  else
  if(TxEn & TxEn_q & TxAbortPacket_NotCleared)
    TxAbortPacket_NotCleared <= 1'b0;
  else
  if(TxAbort_wb & (~tx_burst_en) & MasterWbTX & MasterAccessFinished &
     (~TxAbortPacketBlocked) | TxAbort_wb & (~MasterWbTX) &
     (~TxAbortPacketBlocked))
    TxAbortPacket_NotCleared <= 1'b1;
end


always @ (posedge WB_CLK_I or negedge Resetn)
begin
  if(Resetn == 0)
    TxAbortPacketBlocked <= 1'b0;
  else
  if(!TxAbort_wb & TxAbort_wb_q)
    TxAbortPacketBlocked <= 1'b0;
  else
  if(TxAbortPacket)
    TxAbortPacketBlocked <= 1'b1;
end


reg TxRetryPacketBlocked;
always @ (posedge WB_CLK_I or negedge Resetn)
begin
  if(Resetn == 0)
    TxRetryPacket <= 1'b0;
  else
  if(TxRetry_wb & !tx_burst_en & MasterWbTX & MasterAccessFinished &
     !TxRetryPacketBlocked | TxRetry_wb & !MasterWbTX & !TxRetryPacketBlocked)
    TxRetryPacket <= 1'b1;
  else
    TxRetryPacket <= 1'b0;
end


always @ (posedge WB_CLK_I or negedge Resetn)
begin
  if(Resetn == 0)
    TxRetryPacket_NotCleared <= 1'b0;
  else
  if(StartTxBDRead)
    TxRetryPacket_NotCleared <= 1'b0;
  else
  if(TxRetry_wb & !tx_burst_en & MasterWbTX & MasterAccessFinished &
     !TxRetryPacketBlocked | TxRetry_wb & !MasterWbTX & !TxRetryPacketBlocked)
    TxRetryPacket_NotCleared <= 1'b1;
end


always @ (posedge WB_CLK_I or negedge Resetn)
begin
  if(Resetn == 0)
    TxRetryPacketBlocked <= 1'b0;
  else
  if(!TxRetry_wb & TxRetry_wb_q)
    TxRetryPacketBlocked <= 1'b0;
  else
  if(TxRetryPacket)
    TxRetryPacketBlocked <= 1'b1;
end


reg TxDonePacketBlocked;
always @ (posedge WB_CLK_I or negedge Resetn)
begin
  if(Resetn == 0)
    TxDonePacket <= 1'b0;
  else
  if(TxDone_wb & !tx_burst_en & MasterWbTX & MasterAccessFinished &
     !TxDonePacketBlocked | TxDone_wb & !MasterWbTX & !TxDonePacketBlocked)
    TxDonePacket <= 1'b1;
  else
    TxDonePacket <= 1'b0;
end


always @ (posedge WB_CLK_I or negedge Resetn)
begin
  if(Resetn == 0)
    TxDonePacket_NotCleared <= 1'b0;
  else
  if(TxEn & TxEn_q & TxDonePacket_NotCleared)
    TxDonePacket_NotCleared <= 1'b0;
  else
  if(TxDone_wb & !tx_burst_en & MasterWbTX & MasterAccessFinished &
     (~TxDonePacketBlocked) | TxDone_wb & !MasterWbTX & (~TxDonePacketBlocked))
    TxDonePacket_NotCleared <= 1'b1;
end


always @ (posedge WB_CLK_I or negedge Resetn)
begin
  if(Resetn == 0)
    TxDonePacketBlocked <= 1'b0;
  else
  if(!TxDone_wb & TxDone_wb_q)
    TxDonePacketBlocked <= 1'b0;
  else
  if(TxDonePacket)
    TxDonePacketBlocked <= 1'b1;
end


// Indication of the last word
always @ (posedge MTxClk or negedge Resetn)
begin
  if(Resetn == 0)
    LastWord <= 1'b0;
  else
  if((TxEndFrm | TxAbort | TxRetry) & Flop)
    LastWord <= 1'b0;
  else
  if(TxUsedData & Flop & TxByteCnt == 2'h3)
    LastWord <= TxEndFrm_wb;
end


// Tx end frame generation
always @ (posedge MTxClk or negedge Resetn)
begin
  if(Resetn == 0)
    TxEndFrm <= 1'b0;
  else
  if(Flop & TxEndFrm | TxAbort | TxRetry_q)
    TxEndFrm <= 1'b0;        
  else
  if(Flop & LastWord)
    begin
      case (TxValidBytesLatched)  // synopsys parallel_case
        1 : TxEndFrm <= TxByteCnt == 2'h0;
        2 : TxEndFrm <= TxByteCnt == 2'h1;
        3 : TxEndFrm <= TxByteCnt == 2'h2;
        0 : TxEndFrm <= TxByteCnt == 2'h3;
        default : TxEndFrm <= 1'b0;
      endcase
    end
end

//Moschip Team
//Note: 1.When the TxPntr is 3,7,11,... Expected = Need to sample LSB Byte of first Location.
//		2.Actual = Sampled only LSB nibble of first location as LSB and MSB nibble is sampled from the next location as MSB nibble.

reg Delay_StartFrm1_TxUsedData1;
always @(posedge MTxClk or negedge Resetn)
begin
  if(Resetn == 0)
	  Delay_StartFrm1_TxUsedData1 <= 1'b0;
  else
  begin
		case(Delay_StartFrm1_TxUsedData1)
		0: begin
				if(TxStartFrm & TxUsedData & TxPointerLSB==2'h3)
					Delay_StartFrm1_TxUsedData1 <= 1;
		   end
		1: begin
				Delay_StartFrm1_TxUsedData1 <= 0;
		   end
		endcase
  end
end

// Tx data selection (latching)
always @ (posedge MTxClk or negedge Resetn)
begin
  if(Resetn == 0)
    TxData <= 0;
  else
  if(TxStartFrm_sync2 & ~TxStartFrm)
    case(TxPointerLSB)  // synopsys parallel_case
      2'h0 : TxData <= TxData_wb[31:24];// Big Endian Byte Ordering
      2'h1 : TxData <= TxData_wb[23:16];// Big Endian Byte Ordering
      2'h2 : TxData <= TxData_wb[15:08];// Big Endian Byte Ordering
      2'h3 : TxData <= TxData_wb[07:00];// Big Endian Byte Ordering
    endcase
  else
  if(Delay_StartFrm1_TxUsedData1)
    TxData <= TxData_wb[31:24];// Big Endian Byte Ordering
  else
  if(TxUsedData & Flop)
    begin
      case(TxByteCnt)  // synopsys parallel_case
        0 : TxData <= TxDataLatched[31:24];// Big Endian Byte Ordering
        1 : TxData <= TxDataLatched[23:16];
        2 : TxData <= TxDataLatched[15:8];
        3 : TxData <= TxDataLatched[7:0];
      endcase
    end
end


// Latching tx data
always @ (posedge MTxClk or negedge Resetn)
begin
  if(Resetn == 0)
    TxDataLatched[31:0] <= 32'h0;
  else
  if(TxStartFrm_sync2 & ~TxStartFrm | TxUsedData & Flop & TxByteCnt == 2'h3 |
     TxStartFrm & TxUsedData & Flop & TxByteCnt == 2'h0)
    TxDataLatched[31:0] <= TxData_wb[31:0];
end


// Tx under run
always @ (posedge WB_CLK_I or negedge Resetn)
begin
  if(Resetn == 0)
    TxUnderRun_wb <= 1'b0;
  else
  if(TxAbortPulse)
    TxUnderRun_wb <= 1'b0;
  else
  if(TxBufferEmpty & ReadTxDataFromFifo_wb)
    TxUnderRun_wb <= 1'b1;
end


reg TxUnderRun_sync1;

// Tx under run
always @ (posedge MTxClk or negedge Resetn)
begin
  if(Resetn == 0)
    TxUnderRun_sync1 <= 1'b0;
  else
  if(TxUnderRun_wb)
    TxUnderRun_sync1 <= 1'b1;
  else
  if(BlockingTxStatusWrite_sync2)
    TxUnderRun_sync1 <= 1'b0;
end

// Tx under run
always @ (posedge MTxClk or negedge Resetn)
begin
  if(Resetn == 0)
    TxUnderRun <= 1'b0;
  else
  if(BlockingTxStatusWrite_sync2)
    TxUnderRun <= 1'b0;
  else
  if(TxUnderRun_sync1)
    TxUnderRun <= 1'b1;
end


// Tx Byte counter
always @ (posedge MTxClk or negedge Resetn)
begin
  if(Resetn == 0)
    TxByteCnt <= 2'h0;
  else
  if(TxAbort_q | TxRetry_q)
    TxByteCnt <= 2'h0;
  else
  if(TxStartFrm & ~TxUsedData)
    case(TxPointerLSB)  // synopsys parallel_case
      2'h0 : TxByteCnt <= 2'h1;
      2'h1 : TxByteCnt <= 2'h2;
      2'h2 : TxByteCnt <= 2'h3;
      2'h3 : TxByteCnt <= 2'h0;
    endcase
  else
  if(TxUsedData & Flop)
    TxByteCnt <= TxByteCnt + 1'b1;
end


always @ (posedge MTxClk or negedge Resetn)
begin
  if(Resetn == 0)
    ReadTxDataFromFifo_tck <= 1'b0;
  else
  if(TxStartFrm_sync2 & ~TxStartFrm | TxUsedData & Flop & TxByteCnt == 2'h3 &
     ~LastWord | TxStartFrm & TxUsedData & Flop & TxByteCnt == 2'h0)
     ReadTxDataFromFifo_tck <= 1'b1;
  else
  if(ReadTxDataFromFifo_syncb2 & ~ReadTxDataFromFifo_syncb3)
    ReadTxDataFromFifo_tck <= 1'b0;
end

// Synchronizing TxStartFrm_wb to MTxClk
always @ (posedge WB_CLK_I or negedge Resetn)
begin
  if(Resetn == 0)
    ReadTxDataFromFifo_sync1 <= 1'b0;
  else
    ReadTxDataFromFifo_sync1 <= ReadTxDataFromFifo_tck;
end

always @ (posedge WB_CLK_I or negedge Resetn)
begin
  if(Resetn == 0)
    ReadTxDataFromFifo_sync2 <= 1'b0;
  else
    ReadTxDataFromFifo_sync2 <= ReadTxDataFromFifo_sync1;
end

always @ (posedge MTxClk or negedge Resetn)
begin
  if(Resetn == 0)
    ReadTxDataFromFifo_syncb1 <= 1'b0;
  else
    ReadTxDataFromFifo_syncb1 <= ReadTxDataFromFifo_sync2;
end

always @ (posedge MTxClk or negedge Resetn)
begin
  if(Resetn == 0)
    ReadTxDataFromFifo_syncb2 <= 1'b0;
  else
    ReadTxDataFromFifo_syncb2 <= ReadTxDataFromFifo_syncb1;
end

always @ (posedge MTxClk or negedge Resetn)
begin
  if(Resetn == 0)
    ReadTxDataFromFifo_syncb3 <= 1'b0;
  else
    ReadTxDataFromFifo_syncb3 <= ReadTxDataFromFifo_syncb2;
end

always @ (posedge WB_CLK_I or negedge Resetn)
begin
  if(Resetn == 0)
    ReadTxDataFromFifo_sync3 <= 1'b0;
  else
    ReadTxDataFromFifo_sync3 <= ReadTxDataFromFifo_sync2;
end

assign ReadTxDataFromFifo_wb = ReadTxDataFromFifo_sync2 &
                               ~ReadTxDataFromFifo_sync3;
// End: Generation of the ReadTxDataFromFifo_tck signal and synchronization
// to the WB_CLK_I


// Synchronizing TxRetry signal (synchronized to WISHBONE clock)
always @ (posedge WB_CLK_I or negedge Resetn)
begin
  if(Resetn == 0)
    TxRetrySync1 <= 1'b0;
  else
    TxRetrySync1 <= TxRetry;
end

always @ (posedge WB_CLK_I or negedge Resetn)
begin
  if(Resetn == 0)
    TxRetry_wb <= 1'b0;
  else
    TxRetry_wb <= TxRetrySync1;
end


// Synchronized TxDone_wb signal (synchronized to WISHBONE clock)
always @ (posedge WB_CLK_I or negedge Resetn)
begin
  if(Resetn == 0)
    TxDoneSync1 <= 1'b0;
  else
    TxDoneSync1 <= TxDone;
end

always @ (posedge WB_CLK_I or negedge Resetn)
begin
  if(Resetn == 0)
    TxDone_wb <= 1'b0;
  else
    TxDone_wb <= TxDoneSync1;
end

// Synchronizing TxAbort signal (synchronized to WISHBONE clock)
always @ (posedge WB_CLK_I or negedge Resetn)
begin
  if(Resetn == 0)
    TxAbortSync1 <= 1'b0;
  else
    TxAbortSync1 <= TxAbort;
end

always @ (posedge WB_CLK_I or negedge Resetn)
begin
  if(Resetn == 0)
    TxAbort_wb <= 1'b0;
  else
    TxAbort_wb <= TxAbortSync1;
end


assign StartRxBDRead = RxStatusWrite | RxAbortSync3 & ~RxAbortSync4 |
                       r_RxEn & ~r_RxEn_q;

// Reading the Rx buffer descriptor
always @ (posedge WB_CLK_I or negedge Resetn)
begin
  if(Resetn == 0)
    RxBDRead <= 1'b0;
  else
  if(StartRxBDRead & ~RxReady)
    RxBDRead <= 1'b1;
  else
  if(RxBDReady)
    RxBDRead <= 1'b0;
end


// Reading of the next receive buffer descriptor starts after reception status
// is written to the previous one.

// Latching READY status of the Rx buffer descriptor
always @ (posedge WB_CLK_I or negedge Resetn)
begin
  if(Resetn == 0)
    RxBDReady <= 1'b0;
  else
  if(RxPointerRead)
    RxBDReady <= 1'b0;
  else
  if(RxEn & RxEn_q & RxBDRead)
    RxBDReady <= ram_do[15];// RxBDReady is sampled only once at the beginning
end

// Latching Rx buffer descriptor status
// Data is avaliable one cycle after the access is started (at that time
// signal RxEn is not active)
always @ (posedge WB_CLK_I or negedge Resetn)
begin
  if(Resetn == 0)
    RxStatus <= 2'h0;
  else
  if(RxEn & RxEn_q & RxBDRead)
    RxStatus <= {ram_do[14],1'b0};
end


// RxReady generation
always @ (posedge WB_CLK_I or negedge Resetn)
begin
  if(Resetn == 0)
    RxReady <= 1'b0;
  else if(ShiftEnded | RxAbortSync2 & ~RxAbortSync3 | ~r_RxEn & r_RxEn_q)
    RxReady <= 1'b0;
  else if(RxEn & RxEn_q & RxPointerRead)
    RxReady <= 1'b1;
end


// Reading Rx BD pointer
assign StartRxPointerRead = RxBDRead & RxBDReady;

// Reading Tx BD Pointer
always @ (posedge WB_CLK_I or negedge Resetn)
begin
  if(Resetn == 0)
    RxPointerRead <= 1'b0;
  else
  if(StartRxPointerRead)
    RxPointerRead <= 1'b1;
  else
  if(RxEn & RxEn_q)
    RxPointerRead <= 1'b0;
end


//Latching Rx buffer pointer from buffer descriptor;
always @ (posedge WB_CLK_I or negedge Resetn)
begin
  if(Resetn == 0)
    RxPointerMSB <= 30'h0;
  else
  if(RxEn & RxEn_q & RxPointerRead)
    RxPointerMSB <= ram_do[31:2];
  else
  if(MasterWbRX & m_ack_sig)
      RxPointerMSB <= RxPointerMSB + 1'b1; // Word access (always word access.
                                           // m_wb_stb_o are used for
                                           // selecting bytes)
end


//Latching last addresses from buffer descriptor (used as byte-half-word
//indicator);
always @ (posedge WB_CLK_I or negedge Resetn)
begin
  if(Resetn == 0)
    RxPointerLSB_rst[1:0] <= 0;
  else
  if(MasterWbRX & m_ack_sig) // After first write all RxByteSel are active
    RxPointerLSB_rst[1:0] <= 0;
  else
  if(RxEn & RxEn_q & RxPointerRead)
    RxPointerLSB_rst[1:0] <= ram_do[1:0];
end


always @ (RxPointerLSB_rst)
begin
  case(RxPointerLSB_rst[1:0])  // synopsys parallel_case
    2'h0 : RxByteSel[3:0] = 4'hf;
    2'h1 : RxByteSel[3:0] = 4'h7;
    2'h2 : RxByteSel[3:0] = 4'h3;
    2'h3 : RxByteSel[3:0] = 4'h1;
  endcase
end


always @ (posedge WB_CLK_I or negedge Resetn)
begin
  if(Resetn == 0)
    RxEn_needed <= 1'b0;
  else if(~RxReady & r_RxEn & WbEn & ~WbEn_q)
    RxEn_needed <= 1'b1;
  else if(RxPointerRead & RxEn & RxEn_q)
    RxEn_needed <= 1'b0;
end


// Reception status is written back to the buffer descriptor after the end
// of frame is detected.
assign RxStatusWrite = (ShiftEnded & RxEn & RxEn_q);


// Indicating that last byte is being reveived
always @ (posedge MRxClk or negedge Resetn)
begin
  if(Resetn == 0)
    LastByteIn <= 1'b0;
  else
  if(ShiftWillEnd & (&RxByteCnt) | RxAbort)
    LastByteIn <= 1'b0;
  else
  if(RxValid & RxReady & RxEndFrm & ~(&RxByteCnt) & RxEnableWindow)
    LastByteIn <= 1'b1;
end
//
assign StartShiftWillEnd = LastByteIn  | (RxValid & RxEndFrm & (&RxByteCnt) &
									RxEnableWindow & Length_Vs_Payload_error == 1'b0 & (RxEndFrm & AddressMiss == 1'b0) & (RxEndFrm & MRxErr_Detected == 1'b0));
// Indicating that data reception will end
always @ (posedge MRxClk or negedge Resetn)
begin
  if(Resetn == 0)
    ShiftWillEnd <= 1'b0;
  else
  if(ShiftEnded_rck | RxAbort)
    ShiftWillEnd <= 1'b0;
  else
  if(StartShiftWillEnd)
    ShiftWillEnd <= 1'b1;
end


// Receive byte counter
always @ (posedge MRxClk or negedge Resetn)
begin
  if(Resetn == 0)
    RxByteCnt <= 2'h0;
  else
  if(ShiftEnded_rck | RxAbort)
    RxByteCnt <= 2'h0;
  else
  if(RxValid & RxStartFrm & RxReady)
    case(RxPointerLSB_rst)  // synopsys parallel_case
      2'h0 : RxByteCnt <= 2'h1;
      2'h1 : RxByteCnt <= 2'h2;
      2'h2 : RxByteCnt <= 2'h3;
      2'h3 : RxByteCnt <= 2'h0;
    endcase
  else
  if(RxValid & RxEnableWindow & RxReady | LastByteIn)
    RxByteCnt <= RxByteCnt + 1'b1;
end


// Indicates how many bytes are valid within the last word
always @ (posedge MRxClk or negedge Resetn)
begin
  if(Resetn == 0)
    RxValidBytes <= 2'h1;
  else
  if(RxValid & RxStartFrm)
    case(RxPointerLSB_rst)  // synopsys parallel_case
      2'h0 : RxValidBytes <= 2'h1;
      2'h1 : RxValidBytes <= 2'h2;
      2'h2 : RxValidBytes <= 2'h3;
      2'h3 : RxValidBytes <= 2'h0;
    endcase
  else
  if(RxValid & ~LastByteIn & ~RxStartFrm & RxEnableWindow)
    RxValidBytes <= RxValidBytes + 1'b1;
end


always @ (posedge MRxClk or negedge Resetn)
begin
  if(Resetn == 0)
    RxDataLatched1       <= 24'h0;
  else
  if(RxValid & RxReady & ~LastByteIn)
    if(RxStartFrm)
    begin
      case(RxPointerLSB_rst)     // synopsys parallel_case
        // Big Endian Byte Ordering
        2'h0:        RxDataLatched1[31:24] <= RxData;
        2'h1:        RxDataLatched1[23:16] <= RxData;
        2'h2:        RxDataLatched1[15:8]  <= RxData;
        2'h3:        RxDataLatched1        <= RxDataLatched1;
      endcase
    end
    else if (RxEnableWindow)
    begin
      case(RxByteCnt)     // synopsys parallel_case
        // Big Endian Byte Ordering
        2'h0:        RxDataLatched1[31:24] <= RxData;
        2'h1:        RxDataLatched1[23:16] <= RxData;
        2'h2:        RxDataLatched1[15:8]  <= RxData;
        2'h3:        RxDataLatched1        <= RxDataLatched1;
      endcase
    end
end

//Added below on May/4/2020
//Note : 1.Adding below logic to avoid the loss of writing data into rx_fifo
//       2.when loss data happens:
//			a.RTL is writing data into Fifo when there are 4 Bytes available at input pin(data_in)
//		    b.To solve this issue,
//				i.Apending 0's to the data_in .
//              ii.number of 0's are dependent on how many bits are left to make 32 bits of data_in(input of rx_fifo)
//		        iii.Generating one extra pulse of write signal(write of rx_fifo) 
//						-Generate a signal with one clock pulse width ,when  the RxEndFrm  is detected
//						-

/*always@(posedge MRxClk or negedge Resetn)
begin 
  if(Resetn == 0)
       stretch_rxfifo_wr_append_0sto_datain <= 0;
  else
  begin
  	      case(stretch_rxfifo_wr_append_0sto_datain)
		  0:begin
		        if(RxEndFrm & (Length_Vs_Payload_error | AddressMiss | MRxErr_Detected))
				begin
					 case(RxByteCnt)
					 0:stretch_rxfifo_wr_append_0sto_datain <= 3;
					 1:stretch_rxfifo_wr_append_0sto_datain <= 2;
					 2:stretch_rxfifo_wr_append_0sto_datain <= 1;
					 3:stretch_rxfifo_wr_append_0sto_datain <= 0;
					 endcase
				end
				else 
				begin
					if(RxAbort) 
						stretch_rxfifo_wr_append_0sto_datain <= 0;
				end
			end
		  1,
		  2,
		  3: stretch_rxfifo_wr_append_0sto_datain <= 0;
	      endcase
  end
end
*/

// Assembling data that will be written to the rx_fifo
/*always @ (posedge MRxClk or negedge Resetn)
begin 
  if(Resetn == 0)
    RxDataLatched2 <= 32'h0;
  else
  begin
       if(stretch_rxfifo_wr_append_0sto_datain !=0)
       begin
	        case(stretch_rxfifo_wr_append_0sto_datain)
			3: RxDataLatched2 <= {RxData,24'd0};
			2: RxDataLatched2 <= {RxDataLatched1[31:24],RxData,16'd0}; 
            1: RxDataLatched2 <= {RxDataLatched1[31:16],RxData,8'd0}; 	
			0: RxDataLatched2 <= RxDataLatched2;	
			endcase
       end 	   
	   else
	   begin
		  if(SetWriteRxDataToFifo & ~ShiftWillEnd)
			// Big Endian Byte Ordering
			RxDataLatched2 <= {RxDataLatched1[31:8], RxData};
		  else
		  begin
			  if(SetWriteRxDataToFifo & ShiftWillEnd)
				case(RxValidBytes)  // synopsys parallel_case
				  // Big Endian Byte Ordering
				  0 : RxDataLatched2 <= {RxDataLatched1[31:8],  RxData};
				  1 : RxDataLatched2 <= {RxDataLatched1[31:24], 24'h0};
				  2 : RxDataLatched2 <= {RxDataLatched1[31:16], 16'h0};
				  3 : RxDataLatched2 <= {RxDataLatched1[31:8],   8'h0};
				endcase
		  end 
		end
   end
end
*/

always @ (posedge MRxClk or negedge Resetn)
begin 
  if(Resetn == 0)
    RxDataLatched2 <= 32'h0;
  else
  if(SetWriteRxDataToFifo & ~ShiftWillEnd)
    // Big Endian Byte Ordering
    RxDataLatched2 <= {RxDataLatched1[31:8], RxData};
  else
  if(SetWriteRxDataToFifo & ShiftWillEnd)
    case(RxValidBytes)  // synopsys parallel_case
      // Big Endian Byte Ordering
      0 : RxDataLatched2 <= {RxDataLatched1[31:8],  RxData};
      1 : RxDataLatched2 <= {RxDataLatched1[31:24], 24'h0};
      2 : RxDataLatched2 <= {RxDataLatched1[31:16], 16'h0};
      3 : RxDataLatched2 <= {RxDataLatched1[31:8],   8'h0};
    endcase
end


/*always@(*)
begin
	begin
		SetWriteRxDataToFifo = (RxValid & RxReady & ~RxStartFrm & RxEnableWindow & (&RxByteCnt))
                              |(RxValid & RxReady &  RxStartFrm &(&RxPointerLSB_rst))
                              |(ShiftWillEnd & LastByteIn & (&RxByteCnt))
							  |(stretch_rxfifo_wr_append_0sto_datain>0);
	end
end								

always @ (posedge MRxClk or negedge Resetn)
begin
  if(Resetn == 0)
    WriteRxDataToFifo <= 1'b0;
  else
  begin
  	  if(SetWriteRxDataToFifo & ~RxAbort)
			WriteRxDataToFifo <= 1'b1;	
	  else
	  begin
	      if(WriteRxDataToFifoSync2) 
				WriteRxDataToFifo <= 1'b0;
		  else
		  begin
			  if(stretch_rxfifo_wr_append_0sto_datain>0) 
					WriteRxDataToFifo <= 1'b1;	 
			  else
			  begin
				  if(RxAbort)
					WriteRxDataToFifo <= 1'b0;
			  end
		  end
	  end
  end 
end
*/
always@(*)
begin
	begin
		SetWriteRxDataToFifo = (RxValid & RxReady & ~RxStartFrm & RxEnableWindow & (&RxByteCnt))
                              |(RxValid & RxReady &  RxStartFrm &(&RxPointerLSB_rst))
                              |(ShiftWillEnd & LastByteIn & (&RxByteCnt));
							  //|(stretch_rxfifo_wr_append_0sto_datain>0);
	end
end	

always @ (posedge MRxClk or negedge Resetn)
begin
  if(Resetn == 0)
    WriteRxDataToFifo <= 1'b0;
  else
  if(SetWriteRxDataToFifo & ~RxAbort)
    WriteRxDataToFifo <= 1'b1;
  else
  if(WriteRxDataToFifoSync2 | RxAbort)
    WriteRxDataToFifo <= 1'b0;
end

always @ (posedge WB_CLK_I or negedge Resetn)
begin
  if(Resetn == 0)
    WriteRxDataToFifoSync1 <= 1'b0;
  else
  if(WriteRxDataToFifo)
    WriteRxDataToFifoSync1 <= 1'b1;
  else
    WriteRxDataToFifoSync1 <= 1'b0;
end

always @ (posedge WB_CLK_I or negedge Resetn)
begin
  if(Resetn == 0)
    WriteRxDataToFifoSync2 <= 1'b0;
  else
    WriteRxDataToFifoSync2 <= WriteRxDataToFifoSync1;
end

always @ (posedge WB_CLK_I or negedge Resetn)
begin
  if(Resetn == 0)
    WriteRxDataToFifoSync3 <= 1'b0;
  else
    WriteRxDataToFifoSync3 <= WriteRxDataToFifoSync2;
end


assign WriteRxDataToFifo_wb = WriteRxDataToFifoSync2 &
                              ~WriteRxDataToFifoSync3;


always @ (posedge MRxClk or negedge Resetn)
begin
  if(Resetn == 0)
    LatchedRxStartFrm <= 0;
  else
  if(RxStartFrm & ~SyncRxStartFrm_q)
    LatchedRxStartFrm <= 1;
  else
  if(SyncRxStartFrm_q)
    LatchedRxStartFrm <= 0;
end


always @ (posedge WB_CLK_I or negedge Resetn)
begin
  if(Resetn == 0)
    SyncRxStartFrm <= 0;
  else
  if(LatchedRxStartFrm)
    SyncRxStartFrm <= 1;
  else
    SyncRxStartFrm <= 0;
end


always @ (posedge WB_CLK_I or negedge Resetn)
begin
  if(Resetn == 0)
    SyncRxStartFrm_q <= 0;
  else
    SyncRxStartFrm_q <= SyncRxStartFrm;
end

always @ (posedge WB_CLK_I or negedge Resetn)
begin
  if(Resetn == 0)
    SyncRxStartFrm_q2 <= 0;
  else
    SyncRxStartFrm_q2 <= SyncRxStartFrm_q;
end


assign RxFifoReset = SyncRxStartFrm_q & ~SyncRxStartFrm_q2;

eth_fifo #(
           .DATA_WIDTH(RX_FIFO_DATA_WIDTH),
           .DEPTH(RX_FIFO_DEPTH),
           .CNT_WIDTH(RX_FIFO_CNT_WIDTH))
rx_fifo (
         .clk            (WB_CLK_I),
         .resetn          (Resetn),
         // Inputs
         .data_in        (RxDataLatched2),
         .write          (WriteRxDataToFifo_wb & ~RxBufferFull),
         .read           (MasterWbRX & m_ack_sig),
         .clear          (RxFifoReset),
         // Outputs
         .data_out       (m_wb_dat_o), 
         .full           (RxBufferFull),
         .almost_full    (),
         .almost_empty   (RxBufferAlmostEmpty), 
         .empty          (RxBufferEmpty),
         .cnt            (rxfifo_cnt)
        );

assign enough_data_in_rxfifo_for_burst = rxfifo_cnt>=`ETH_BURST_LENGTH;
assign enough_data_in_rxfifo_for_burst_plus1 = rxfifo_cnt>`ETH_BURST_LENGTH;
assign WriteRxDataToMemory = ~RxBufferEmpty;
assign rx_burst = rx_burst_en & WriteRxDataToMemory;


// Generation of the end-of-frame signal
always @ (posedge MRxClk or negedge Resetn)
begin
  if(Resetn == 0)
    ShiftEnded_rck <= 1'b0;
  else
  if(~RxAbort & SetWriteRxDataToFifo & StartShiftWillEnd)
    ShiftEnded_rck <= 1'b1;
  else
  if(RxAbort | ShiftEndedSync_c1 & ShiftEndedSync_c2)
    ShiftEnded_rck <= 1'b0;
end

always @ (posedge WB_CLK_I or negedge Resetn)
begin
  if(Resetn == 0)
    ShiftEndedSync1 <= 1'b0;
  else
    ShiftEndedSync1 <= ShiftEnded_rck;
end

always @ (posedge WB_CLK_I or negedge Resetn)
begin
  if(Resetn == 0)
    ShiftEndedSync2 <= 1'b0;
  else
    ShiftEndedSync2 <= ShiftEndedSync1;
end

always @ (posedge WB_CLK_I or negedge Resetn)
begin
  if(Resetn == 0)
    ShiftEndedSync3 <= 1'b0;
  else
  if(ShiftEndedSync1 & ~ShiftEndedSync2)
    ShiftEndedSync3 <= 1'b1;
  else
  if(ShiftEnded)
    ShiftEndedSync3 <= 1'b0;
end

// Generation of the end-of-frame signal
always @ (posedge WB_CLK_I or negedge Resetn)
begin
  if(Resetn == 0)
    ShiftEnded <= 1'b0;
  else
  if(ShiftEndedSync3 & MasterWbRX & m_ack_sig & RxBufferAlmostEmpty & ~ShiftEnded)
    ShiftEnded <= 1'b1;
  else
  if(RxStatusWrite)
    ShiftEnded <= 1'b0;
end

always @ (posedge MRxClk or negedge Resetn)
begin
  if(Resetn == 0)
    ShiftEndedSync_c1 <= 1'b0;
  else
    ShiftEndedSync_c1 <= ShiftEndedSync2;
end

always @ (posedge MRxClk or negedge Resetn)
begin
  if(Resetn == 0)
    ShiftEndedSync_c2 <= 1'b0;
  else
    ShiftEndedSync_c2 <= ShiftEndedSync_c1;
end

// Generation of the end-of-frame signal
always @ (posedge MRxClk or negedge Resetn)
begin
  if(Resetn == 0)
    RxEnableWindow <= 1'b0;
  else if(RxStartFrm)
    RxEnableWindow <= 1'b1;
  else if(RxEndFrm | RxAbort)
    RxEnableWindow <= 1'b0;
end


always @ (posedge WB_CLK_I or negedge Resetn)
begin
  if(Resetn == 0)
    RxAbortSync1 <= 1'b0;
  else
    RxAbortSync1 <= RxAbortLatched;
end

always @ (posedge WB_CLK_I or negedge Resetn)
begin
  if(Resetn == 0)
    RxAbortSync2 <= 1'b0;
  else
    RxAbortSync2 <= RxAbortSync1;
end

always @ (posedge WB_CLK_I or negedge Resetn)
begin
  if(Resetn == 0)
    RxAbortSync3 <= 1'b0;
  else
    RxAbortSync3 <= RxAbortSync2;
end

always @ (posedge WB_CLK_I or negedge Resetn)
begin
  if(Resetn == 0)
    RxAbortSync4 <= 1'b0;
  else
    RxAbortSync4 <= RxAbortSync3;
end

always @ (posedge MRxClk or negedge Resetn)
begin
  if(Resetn == 0)
    RxAbortSyncb1 <= 1'b0;
  else
    RxAbortSyncb1 <= RxAbortSync2;
end

always @ (posedge MRxClk or negedge Resetn)
begin
  if(Resetn == 0)
    RxAbortSyncb2 <= 1'b0;
  else
    RxAbortSyncb2 <= RxAbortSyncb1;
end


always @ (posedge MRxClk or negedge Resetn)
begin
  if(Resetn == 0)
    RxAbortLatched <= 1'b0;
  else
  if(RxAbortSyncb2)
    RxAbortLatched <= 1'b0;
  else
  if(RxAbort)
    RxAbortLatched <= 1'b1;
end
//Added the logic by Moschip team 27 june 2020
always @(posedge MRxClk or negedge Resetn)
begin
	if(Resetn == 0)
		RxLength_d <= 0;
	else
		RxLength_d[15:0] <= RxLength[15:0];
end

always @ (posedge MRxClk or negedge Resetn)
begin
  if(Resetn == 0)
    LatchedRxLength[15:0] <= 16'h0;
  else
  if(LoadRxStatus)
    LatchedRxLength[15:0] <= RxLength_d[15:0];
end

assign RxStatusIn = {1'b0,
                     AddressMiss,
                     1'b0,
                     1'b0,
                     1'b0,
                     ReceivedPacketTooBig,
                     1'b0,
                     LatchedCrcError,
                     1'b0};

always @ (posedge MRxClk or negedge Resetn)
begin
  if(Resetn == 0)
    RxStatusInLatched <= 'h0;
  else
  if(LoadRxStatus)
    RxStatusInLatched <= RxStatusIn;
end


// Rx overrun
always @ (posedge WB_CLK_I or negedge Resetn)
begin
  if(Resetn == 0)
    RxOverrun <= 1'b0;
  else if(RxStatusWrite)
    RxOverrun <= 1'b0;
  else if(RxBufferFull & WriteRxDataToFifo_wb)
    RxOverrun <= 1'b1;
end

//added by Moschip Team on june 5th
assign TxError =  RetryLimit | LateCollLatched | Tx_BAD_FRAME_f6;


// ShortFrame (RxStatusInLatched[2]) can not set an error because short frames
// are aborted when signal r_RecSmall is set to 0 in MODER register. 
// AddressMiss is identifying that a frame was received because of the
// promiscous mode and is not an error
assign RxError = (|RxStatusInLatched[6:3])|(|RxStatusInLatched[0])| RxStatusIn[7] | (RxEndFrm & Length_Vs_Payload_error) | (RxEndFrm & MRxErr_Detected) ;
// Latching and synchronizing RxStatusWrite signal. This signal is used for
// clearing the ReceivedPauseFrm signal
always @ (posedge WB_CLK_I or negedge Resetn)
begin
  if(Resetn == 0)
    RxStatusWriteLatched <= 1'b0;
  else
  if(RxStatusWriteLatched_syncb2)
    RxStatusWriteLatched <= 1'b0;        
  else
  if(RxStatusWrite)
    RxStatusWriteLatched <= 1'b1;
end


always @ (posedge MRxClk or negedge Resetn)
begin
  if(Resetn == 0)
    begin
      RxStatusWriteLatched_sync1 <= 1'b0;
      RxStatusWriteLatched_sync2 <= 1'b0;
    end
  else
    begin
      RxStatusWriteLatched_sync1 <= RxStatusWriteLatched;
      RxStatusWriteLatched_sync2 <= RxStatusWriteLatched_sync1;
    end
end


always @ (posedge WB_CLK_I or negedge Resetn)
begin
  if(Resetn == 0)
    begin
      RxStatusWriteLatched_syncb1 <= 1'b0;
      RxStatusWriteLatched_syncb2 <= 1'b0;
    end
  else
    begin
      RxStatusWriteLatched_syncb1 <= RxStatusWriteLatched_sync2;
      RxStatusWriteLatched_syncb2 <= RxStatusWriteLatched_syncb1;
    end
end


// Tx Done Interrupt
always @ (posedge WB_CLK_I or negedge Resetn)
begin
  if(Resetn == 0)
    TxB_IRQ <= 1'b0;
  else
  if(TxStatusWrite & TxIRQEn)
	TxB_IRQ <= ~TxError;
  else
    TxB_IRQ <= 1'b0;
end

// Tx Error Interrupt
always @ (posedge WB_CLK_I or negedge Resetn)
begin
  if(Resetn == 0)
    TxE_IRQ <= 1'b0;
  else
  if(TxStatusWrite & TxIRQEn)
    TxE_IRQ <= TxError;
  else
    TxE_IRQ <= 1'b0;
end

// Rx Done Interrupt
always @ (posedge WB_CLK_I or negedge Resetn)
begin
  if(Resetn == 0)
    RxB_IRQ <= 1'b0;
  else
  if(RxStatusWrite & RxIRQEn & ReceivedPacketGood &
     (~ReceivedPauseFrm | ReceivedPauseFrm & r_PassAll & (~r_RxFlow)))
    RxB_IRQ <= (~RxError);
  else
    RxB_IRQ <= 1'b0;
end


//Added by Moschip team on july 4 2020
reg  rxe_low;
reg [6:0] count;
always @ (posedge WB_CLK_I or negedge Resetn)
begin
  if(Resetn == 0) 
  begin
	  rxe_low <= 1'b1;  
  end
  else 
  if(RxE_IRQ)
	  rxe_low <= 1'b0;
  else if(count == 'd40)
  begin 
		rxe_low <= 1'b1;
  end
end
always @ (posedge WB_CLK_I or negedge Resetn)
begin
  if(Resetn == 0) count <= 'd0;
  else if(rxe_low == 1'b0) 
		begin
			count <= count + 1'b1;
				if(count == 'd40)
				count <= 1'b0;
		end
   else 
		count <= count;
end
  
  
  //added by moschip team(rajesh)
reg rxbadcount_en;
reg [6:0] rxbadcount;
always @ (posedge WB_CLK_I or negedge Resetn)
begin
  if(Resetn == 0) begin
  rxbadcount_en <= 0;
  end
  //else if(RxE_IRQ == 1'b1) begin
  else if(((RxEndFrm & AddressMiss & rxe_low) | (RxEndFrm & Length_Vs_Payload_error & rxe_low) | (RxEndFrm & MRxErr_Detected & rxe_low)) & RxIRQEn & (~ReceivedPauseFrm | ReceivedPauseFrm
     & r_PassAll & (~r_RxFlow))) begin
  //else if (RxEndFrm == 1'b1) begin
  rxbadcount_en <= 1'b1;
  end
  else if(rxbadcount == 'd100-1'b1) begin
  rxbadcount_en <= 1'b0;
  end
  else begin
  rxbadcount_en <= rxbadcount_en;
  end
  end
  
always @ (posedge WB_CLK_I or negedge Resetn)
begin
  if(Resetn == 0) begin
  rxbadcount <= 0;
  end
  else if(rxbadcount_en == 1'b1) begin
  rxbadcount <= rxbadcount + 1'b1;
  end
  else begin
  rxbadcount <= 0;
  end
  end
  reg rxbadstatuswrite;
  
always @ (posedge WB_CLK_I or negedge Resetn)
begin
  if(Resetn == 0) begin 	
  rxbadstatuswrite <= 1'b0;
  end
  else if(rxbadcount == 'd95) begin
  //if(RxBDDataIn[1]==1'b1 | RxBDDataIn[3]==1'b1 | RxBDDataIn[7]==1'b1)
  rxbadstatuswrite <= 1'b1;
  end
  else begin
  rxbadstatuswrite <= 1'b0;
  end
  end
  always @ (posedge WB_CLK_I or negedge Resetn)
begin
  if(Resetn == 0)
    RxE_IRQ <= 1'b0;
  else
    if(rxbadstatuswrite == 1'b1)
    RxE_IRQ <= 1'b1;
  else
    RxE_IRQ <= 1'b0;
end

  
/*	
// Rx Error Interrupt
always @ (posedge WB_CLK_I or negedge Resetn)
begin
  if(Resetn == 0)
    RxE_IRQ <= 1'b0;
  else
    if((RxStatusWrite | (RxEndFrm & AddressMiss & rxe_low) | (RxEndFrm & Length_Vs_Payload_error & rxe_low) | (RxEndFrm & MRxErr_Detected & rxe_low)) & RxIRQEn & (~ReceivedPauseFrm | ReceivedPauseFrm
     & r_PassAll & (~r_RxFlow)))
    RxE_IRQ <= RxError;
  else
    RxE_IRQ <= 1'b0;
end
*/

// Busy Interrupt

reg Busy_IRQ_rck;
reg Busy_IRQ_sync1;
reg Busy_IRQ_sync2;
reg Busy_IRQ_sync3;
reg Busy_IRQ_syncb1;
reg Busy_IRQ_syncb2;


always @ (posedge MRxClk or negedge Resetn)
begin
  if(Resetn == 0)
    Busy_IRQ_rck <= 1'b0;
  else
  if(RxValid & RxStartFrm & ~RxReady)
    Busy_IRQ_rck <= 1'b1;
  else
  if(Busy_IRQ_syncb2)
    Busy_IRQ_rck <= 1'b0;
end

always @ (posedge WB_CLK_I)
begin
    Busy_IRQ_sync1 <= Busy_IRQ_rck;
    Busy_IRQ_sync2 <= Busy_IRQ_sync1;
    Busy_IRQ_sync3 <= Busy_IRQ_sync2;
end

always @ (posedge MRxClk)
begin
    Busy_IRQ_syncb1 <= Busy_IRQ_sync2;
    Busy_IRQ_syncb2 <= Busy_IRQ_syncb1;
end

assign Busy_IRQ = Busy_IRQ_sync2 & ~Busy_IRQ_sync3;


// Assign the debug output
`ifdef WISHBONE_DEBUG
// Top byte, burst progress counters
assign dbg_dat0[31] = 0;
assign dbg_dat0[30:28] = rx_burst_cnt;
assign dbg_dat0[27] = 0;
assign dbg_dat0[26:24] = tx_burst_cnt;
// Third byte
assign dbg_dat0[23] = 0; //rx_ethside_fifo_sel;
assign dbg_dat0[22] = 0; //rx_wbside_fifo_sel;
assign dbg_dat0[21] = 0; //rx_fifo0_empty;
assign dbg_dat0[20] = 0; //rx_fifo1_empty;
assign dbg_dat0[19] = 0; //overflow_bug_reset;
assign dbg_dat0[18] = 0; //RxBDOK;
assign dbg_dat0[17] = 0; //write_rx_data_to_memory_go;
assign dbg_dat0[16] = 0; //rx_wb_last_writes;
// Second byte - TxBDAddress - or TX BD address pointer
assign dbg_dat0[15:8] = { BlockingTxBDRead , TxBDAddress};
// Bottom byte - FSM controlling vector
assign dbg_dat0[7:0] = {MasterWbTX,
                       MasterWbRX,
                       ReadTxDataFromMemory_2,
                       WriteRxDataToMemory,
                       MasterAccessFinished,
                       cyc_cleared,
                       tx_burst,
                       rx_burst};
`endif


endmodule



//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date:    17:44:04 06/07/2020 
// Design Name: 
// Module Name:    timescale 
// Project Name: 
// Target Devices: 
// Tool versions: 
// Description: 
//
// Dependencies: 
//
// Revision: 
// Revision 0.01 - File Created
// Additional Comments: 
//
//////////////////////////////////////////////////////////////////////////////////

`timescale 1ns / 1ns
