////////////////////////////////////////////////////////////////////////////////
//
//       This confidential and proprietary software may be used only
//     as authorized by a licensing agreement from Synopsys Inc.
//     In the event of publication, the following notice is applicable:
//
//                    (C) COPYRIGHT 2006 - 2015 SYNOPSYS INC.
//                           ALL RIGHTS RESERVED
//
//       The entire notice above must be reproduced on all authorized
//     copies.
//
// AUTHOR:    Reto Zimmermann    Mar. 22, 2006
//
// VERSION:   Simulation Architecture (Unrolled version for HW-CBMC)
//
// DesignWare_version: dee492f6
// DesignWare_release: J-2014.09-DWBB_201409.3
//
////////////////////////////////////////////////////////////////////////////////
//
// ABSTRACT: Leading Signs Detector
//           - Outputs an 'encoded' value that is the number of sign bits 
//             (from the left) before the first non-sign bit is found in the 
//             input vector. 
//           - Outputs a one-hot 'decoded' value that indicates the position 
//             of the right-most sign bit in the input vector.
//
//           Loop-unrolled version for compatibility with formal verification
//           tools like HW-CBMC that do not support loops or functions.
//
//-----------------------------------------------------------------------------

module DW_lsd_w32 (a, dec, enc);

parameter a_width = 32;

localparam addr_width = 5; // ceil(log2(32)) = 5

input     [a_width-1:0] a;
output    [a_width-1:0] dec;
output [addr_width-1:0] enc;

// Outputs must be declared as 'reg' when driven from an always block
reg    [a_width-1:0] dec;
reg [addr_width-1:0] enc;

// synopsys translate_off
  //-------------------------------------------------------------------------
  // Parameter legality check
  //-------------------------------------------------------------------------
 
wire [a_width-2:0] a_xor_leftshift_one;
assign a_xor_leftshift_one=a[31:1]^{a[30:0]};

  initial begin : parameter_check
    integer param_err_flg;
    param_err_flg = 0;
    
    if (a_width < 1) begin
      param_err_flg = 1;
      $display(
        "ERROR: %m :\n  Invalid value (%d) for parameter a_width (lower bound: 1)",
        a_width );
    end
  
    if ( param_err_flg == 1) begin
      $display(
        "%m :\n  Simulation aborted due to invalid parameter value(s)");
      $finish;
    end
  end // parameter_check 


  // Combinatorial logic block for leading sign detection
  always @(*) begin
    // First case statement for enc
    casex (a_xor_leftshift_one)
      31'b1xxxxxxxxxxxxxxxxxxxxxxxxxxxxxx: enc = 0;
      31'b01xxxxxxxxxxxxxxxxxxxxxxxxxxxxx: enc = 1;
      31'b001xxxxxxxxxxxxxxxxxxxxxxxxxxxx: enc = 2;
      31'b0001xxxxxxxxxxxxxxxxxxxxxxxxxxx: enc = 3;
      31'b00001xxxxxxxxxxxxxxxxxxxxxxxxxx: enc = 4;
      31'b000001xxxxxxxxxxxxxxxxxxxxxxxxx: enc = 5;
      31'b0000001xxxxxxxxxxxxxxxxxxxxxxxx: enc = 6;
      31'b00000001xxxxxxxxxxxxxxxxxxxxxxx: enc = 7;
      31'b000000001xxxxxxxxxxxxxxxxxxxxxx: enc = 8;
      31'b0000000001xxxxxxxxxxxxxxxxxxxxx: enc = 9;
      31'b00000000001xxxxxxxxxxxxxxxxxxxx: enc = 10;
      31'b000000000001xxxxxxxxxxxxxxxxxxx: enc = 11;
      31'b0000000000001xxxxxxxxxxxxxxxxxx: enc = 12;
      31'b00000000000001xxxxxxxxxxxxxxxxx: enc = 13;
      31'b000000000000001xxxxxxxxxxxxxxxx: enc = 14;
      31'b0000000000000001xxxxxxxxxxxxxxx: enc = 15;
      31'b00000000000000001xxxxxxxxxxxxxx: enc = 16;
      31'b000000000000000001xxxxxxxxxxxxx: enc = 17;
      31'b0000000000000000001xxxxxxxxxxxx: enc = 18;
      31'b00000000000000000001xxxxxxxxxxx: enc = 19;
      31'b000000000000000000001xxxxxxxxxx: enc = 20;
      31'b0000000000000000000001xxxxxxxxx: enc = 21;
      31'b00000000000000000000001xxxxxxxx: enc = 22;
      31'b000000000000000000000001xxxxxxx: enc = 23;
      31'b0000000000000000000000001xxxxxx: enc = 24;
      31'b00000000000000000000000001xxxxx: enc = 25;
      31'b000000000000000000000000001xxxx: enc = 26;
      31'b0000000000000000000000000001xxx: enc = 27;
      31'b00000000000000000000000000001xx: enc = 28;
      31'b000000000000000000000000000001x: enc = 29;
      31'b0000000000000000000000000000001: enc = 30;
      default: enc = a_width - 1;
    endcase

    // Second case statement for dec
    casex (a_xor_leftshift_one)
      31'b1xxxxxxxxxxxxxxxxxxxxxxxxxxxxxx: dec = 32'h80000000;
      31'b01xxxxxxxxxxxxxxxxxxxxxxxxxxxxx: dec = 32'h40000000;
      31'b001xxxxxxxxxxxxxxxxxxxxxxxxxxxx: dec = 32'h20000000;
      31'b0001xxxxxxxxxxxxxxxxxxxxxxxxxxx: dec = 32'h10000000;
      31'b00001xxxxxxxxxxxxxxxxxxxxxxxxxx: dec = 32'h08000000;
      31'b000001xxxxxxxxxxxxxxxxxxxxxxxxx: dec = 32'h04000000;
      31'b0000001xxxxxxxxxxxxxxxxxxxxxxxx: dec = 32'h02000000;
      31'b00000001xxxxxxxxxxxxxxxxxxxxxxx: dec = 32'h01000000;
      31'b000000001xxxxxxxxxxxxxxxxxxxxxx: dec = 32'h00800000;
      31'b0000000001xxxxxxxxxxxxxxxxxxxxx: dec = 32'h00400000;
      31'b00000000001xxxxxxxxxxxxxxxxxxxx: dec = 32'h00200000;
      31'b000000000001xxxxxxxxxxxxxxxxxxx: dec = 32'h00100000;
      31'b0000000000001xxxxxxxxxxxxxxxxxx: dec = 32'h00080000;
      31'b00000000000001xxxxxxxxxxxxxxxxx: dec = 32'h00040000;
      31'b000000000000001xxxxxxxxxxxxxxxx: dec = 32'h00020000;
      31'b0000000000000001xxxxxxxxxxxxxxx: dec = 32'h00010000;
      31'b00000000000000001xxxxxxxxxxxxxx: dec = 32'h00008000;
      31'b000000000000000001xxxxxxxxxxxxx: dec = 32'h00004000;
      31'b0000000000000000001xxxxxxxxxxxx: dec = 32'h00002000;
      31'b00000000000000000001xxxxxxxxxxx: dec = 32'h00001000;
      31'b000000000000000000001xxxxxxxxxx: dec = 32'h00000800;
      31'b0000000000000000000001xxxxxxxxx: dec = 32'h00000400;
      31'b00000000000000000000001xxxxxxxx: dec = 32'h00000200;
      31'b000000000000000000000001xxxxxxx: dec = 32'h00000100;
      31'b0000000000000000000000001xxxxxx: dec = 32'h00000080;
      31'b00000000000000000000000001xxxxx: dec = 32'h00000040;
      31'b000000000000000000000000001xxxx: dec = 32'h00000020;
      31'b0000000000000000000000000001xxx: dec = 32'h00000010;
      31'b00000000000000000000000000001xx: dec = 32'h00000008;
      31'b000000000000000000000000000001x: dec = 32'h00000004;
      31'b0000000000000000000000000000001: dec = 32'h00000002;
      default: dec = 32'h00000001;
    endcase
  end

// synopsys translate_on
endmodule