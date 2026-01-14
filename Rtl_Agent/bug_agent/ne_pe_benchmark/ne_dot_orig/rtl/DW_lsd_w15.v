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

module DW_lsd_w15 (a, dec, enc);

parameter a_width = 15;

localparam addr_width = 4; // ceil(log2(32)) = 5

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
      14'b1xxxxxxxxxxxxx: enc = 0;
      14'b01xxxxxxxxxxxx: enc = 1;
      14'b001xxxxxxxxxxx: enc = 2;
      14'b0001xxxxxxxxxx: enc = 3;
      14'b00001xxxxxxxxx: enc = 4;
      14'b000001xxxxxxxx: enc = 5;
      14'b0000001xxxxxxx: enc = 6;
      14'b00000001xxxxxx: enc = 7;
      14'b000000001xxxxx: enc = 8;
      14'b0000000001xxxx: enc = 9;
      14'b00000000001xxx: enc = 10;
      14'b000000000001xx: enc = 11;
      14'b0000000000001x: enc = 12;
      14'b00000000000001: enc = 13;
      default: enc = a_width - 1;
    endcase

    // Second case statement for dec
    casex (a_xor_leftshift_one)
      14'b01xxxxxxxxxxxxx: dec = 15'h4000;
      14'b001xxxxxxxxxxxx: dec = 15'h2000;
      14'b0001xxxxxxxxxxx: dec = 15'h1000;
      14'b00001xxxxxxxxxx: dec = 15'h0800;
      14'b000001xxxxxxxxx: dec = 15'h0400;
      14'b0000001xxxxxxxx: dec = 15'h0200;
      14'b00000001xxxxxxx: dec = 15'h0100;
      14'b000000001xxxxxx: dec = 15'h0080;
      14'b0000000001xxxxx: dec = 15'h0040;
      14'b00000000001xxxx: dec = 15'h0020;
      14'b000000000001xxx: dec = 15'h0010;
      14'b0000000000001xx: dec = 15'h0008;
      14'b00000000000001x: dec = 15'h0004;
      14'b000000000000001: dec = 15'h0002;
      default: dec = 15'h0001;
    endcase
  end

// synopsys translate_on
endmodule