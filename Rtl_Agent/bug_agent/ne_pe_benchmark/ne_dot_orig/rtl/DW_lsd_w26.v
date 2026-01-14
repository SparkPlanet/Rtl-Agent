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

module DW_lsd_w26 (a, dec, enc);

parameter a_width = 26;
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
assign a_xor_leftshift_one=a[a_width-1:1]^a[a_width-2:0];

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
      25'b1xxxxxxxxxxxxxxxxxxxxxxxx: enc = 0;
      25'b01xxxxxxxxxxxxxxxxxxxxxxx: enc = 1;
      25'b001xxxxxxxxxxxxxxxxxxxxxx: enc = 2;
      25'b0001xxxxxxxxxxxxxxxxxxxxx: enc = 3;
      25'b00001xxxxxxxxxxxxxxxxxxxx: enc = 4;
      25'b000001xxxxxxxxxxxxxxxxxxx: enc = 5;
      25'b0000001xxxxxxxxxxxxxxxxxx: enc = 6;
      25'b00000001xxxxxxxxxxxxxxxxx: enc = 7;
      25'b000000001xxxxxxxxxxxxxxxx: enc = 8;
      25'b0000000001xxxxxxxxxxxxxxx: enc = 9;
      25'b00000000001xxxxxxxxxxxxxx: enc = 10;
      25'b000000000001xxxxxxxxxxxxx: enc = 11;
      25'b0000000000001xxxxxxxxxxxx: enc = 12;
      25'b00000000000001xxxxxxxxxxx: enc = 13;
      25'b000000000000001xxxxxxxxxx: enc = 14;
      25'b0000000000000001xxxxxxxxx: enc = 15;
      25'b00000000000000001xxxxxxxx: enc = 16;
      25'b000000000000000001xxxxxxx: enc = 17;
      25'b0000000000000000001xxxxxx: enc = 18;
      25'b00000000000000000001xxxxx: enc = 19;
      25'b000000000000000000001xxxx: enc = 20;
      25'b0000000000000000000001xxx: enc = 21;
      25'b00000000000000000000001xx: enc = 22;
      25'b000000000000000000000001x: enc = 23;
      25'b0000000000000000000000001: enc = 24;
      default: enc = a_width - 1;
    endcase

    // Second case statement for dec
    casex (a_xor_leftshift_one)
      25'b1xxxxxxxxxxxxxxxxxxxxxxxx: dec = 26'h2000000;
      25'b01xxxxxxxxxxxxxxxxxxxxxxx: dec = 26'h1000000;
      25'b001xxxxxxxxxxxxxxxxxxxxxx: dec = 26'h0800000;
      25'b0001xxxxxxxxxxxxxxxxxxxxx: dec = 26'h0400000;
      25'b00001xxxxxxxxxxxxxxxxxxxx: dec = 26'h0200000;
      25'b000001xxxxxxxxxxxxxxxxxxx: dec = 26'h0100000;
      25'b0000001xxxxxxxxxxxxxxxxxx: dec = 26'h0080000;
      25'b00000001xxxxxxxxxxxxxxxxx: dec = 26'h0040000;
      25'b000000001xxxxxxxxxxxxxxxx: dec = 26'h0020000;
      25'b0000000001xxxxxxxxxxxxxxx: dec = 26'h0010000;
      25'b00000000001xxxxxxxxxxxxxx: dec = 26'h0008000;
      25'b000000000001xxxxxxxxxxxxx: dec = 26'h0004000;
      25'b0000000000001xxxxxxxxxxxx: dec = 26'h0002000;
      25'b00000000000001xxxxxxxxxxx: dec = 26'h0001000;
      25'b000000000000001xxxxxxxxxx: dec = 26'h0000800;
      25'b0000000000000001xxxxxxxxx: dec = 26'h0000400;
      25'b00000000000000001xxxxxxxx: dec = 26'h0000200;
      25'b000000000000000001xxxxxxx: dec = 26'h0000100;
      25'b0000000000000000001xxxxxx: dec = 26'h0000080;
      25'b00000000000000000001xxxxx: dec = 26'h0000040;
      25'b000000000000000000001xxxx: dec = 26'h0000020;
      25'b0000000000000000000001xxx: dec = 26'h0000010;
      25'b00000000000000000000001xx: dec = 26'h0000008;
      25'b000000000000000000000001x: dec = 26'h0000004;
      25'b0000000000000000000000001: dec = 26'h0000002;
      default: dec = 26'h000001;
    endcase
  end

// synopsys translate_on
endmodule