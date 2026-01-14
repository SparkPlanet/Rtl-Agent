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

module DW_lsd_w33 (a, dec, enc);

parameter a_width = 33;

localparam addr_width = 6; // ceil(log2(33)) = 6

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
assign a_xor_leftshift_one=a[a_width-1:1]^{a[a_width-2:0]};

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
      32'b1xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx: enc = 0;
      32'b01xxxxxxxxxxxxxxxxxxxxxxxxxxxxxx: enc = 1;
      32'b001xxxxxxxxxxxxxxxxxxxxxxxxxxxxx: enc = 2;
      32'b0001xxxxxxxxxxxxxxxxxxxxxxxxxxxx: enc = 3;
      32'b00001xxxxxxxxxxxxxxxxxxxxxxxxxxx: enc = 4;
      32'b000001xxxxxxxxxxxxxxxxxxxxxxxxxx: enc = 5;
      32'b0000001xxxxxxxxxxxxxxxxxxxxxxxxx: enc = 6;
      32'b00000001xxxxxxxxxxxxxxxxxxxxxxxx: enc = 7;
      32'b000000001xxxxxxxxxxxxxxxxxxxxxxx: enc = 8;
      32'b0000000001xxxxxxxxxxxxxxxxxxxxxx: enc = 9;
      32'b00000000001xxxxxxxxxxxxxxxxxxxxx: enc = 10;
      32'b000000000001xxxxxxxxxxxxxxxxxxxx: enc = 11;
      32'b0000000000001xxxxxxxxxxxxxxxxxxx: enc = 12;
      32'b00000000000001xxxxxxxxxxxxxxxxxx: enc = 13;
      32'b000000000000001xxxxxxxxxxxxxxxxx: enc = 14;
      32'b0000000000000001xxxxxxxxxxxxxxxx: enc = 15;
      32'b00000000000000001xxxxxxxxxxxxxxx: enc = 16;
      32'b000000000000000001xxxxxxxxxxxxxx: enc = 17;
      32'b0000000000000000001xxxxxxxxxxxxx: enc = 18;
      32'b00000000000000000001xxxxxxxxxxxx: enc = 19;
      32'b000000000000000000001xxxxxxxxxxx: enc = 20;
      32'b0000000000000000000001xxxxxxxxxx: enc = 21;
      32'b00000000000000000000001xxxxxxxxx: enc = 22;
      32'b000000000000000000000001xxxxxxxx: enc = 23;
      32'b0000000000000000000000001xxxxxxx: enc = 24;
      32'b00000000000000000000000001xxxxxx: enc = 25;
      32'b000000000000000000000000001xxxxx: enc = 26;
      32'b0000000000000000000000000001xxxx: enc = 27;
      32'b00000000000000000000000000001xxx: enc = 28;
      32'b000000000000000000000000000001xx: enc = 29;
      32'b0000000000000000000000000000001x: enc = 30;
      32'b00000000000000000000000000000001: enc = 31;
      default: enc = a_width - 1;
    endcase

    // Second case statement for dec
    casex (a_xor_leftshift_one)
      32'b1xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx: dec = 33'h100000000;
      32'b01xxxxxxxxxxxxxxxxxxxxxxxxxxxxxx: dec = 33'h080000000;
      32'b001xxxxxxxxxxxxxxxxxxxxxxxxxxxxx: dec = 33'h040000000;
      32'b0001xxxxxxxxxxxxxxxxxxxxxxxxxxxx: dec = 33'h020000000;
      32'b00001xxxxxxxxxxxxxxxxxxxxxxxxxxx: dec = 33'h010000000;
      32'b000001xxxxxxxxxxxxxxxxxxxxxxxxxx: dec = 33'h008000000;
      32'b0000001xxxxxxxxxxxxxxxxxxxxxxxxx: dec = 33'h004000000;
      32'b00000001xxxxxxxxxxxxxxxxxxxxxxxx: dec = 33'h002000000;
      32'b000000001xxxxxxxxxxxxxxxxxxxxxxx: dec = 33'h001000000;
      32'b0000000001xxxxxxxxxxxxxxxxxxxxxx: dec = 33'h000800000;
      32'b00000000001xxxxxxxxxxxxxxxxxxxxx: dec = 33'h000400000;
      32'b000000000001xxxxxxxxxxxxxxxxxxxx: dec = 33'h000200000;
      32'b0000000000001xxxxxxxxxxxxxxxxxxx: dec = 33'h000100000;
      32'b00000000000001xxxxxxxxxxxxxxxxxx: dec = 33'h000080000;
      32'b000000000000001xxxxxxxxxxxxxxxxx: dec = 33'h000040000;
      32'b0000000000000001xxxxxxxxxxxxxxxx: dec = 33'h000020000;
      32'b00000000000000001xxxxxxxxxxxxxxx: dec = 33'h000010000;
      32'b000000000000000001xxxxxxxxxxxxxx: dec = 33'h000008000;
      32'b0000000000000000001xxxxxxxxxxxxx: dec = 33'h000004000;
      32'b00000000000000000001xxxxxxxxxxxx: dec = 33'h000002000;
      32'b000000000000000000001xxxxxxxxxxx: dec = 33'h000001000;
      32'b0000000000000000000001xxxxxxxxxx: dec = 33'h000000800;
      32'b00000000000000000000001xxxxxxxxx: dec = 33'h000000400;
      32'b000000000000000000000001xxxxxxxx: dec = 33'h000000200;
      32'b0000000000000000000000001xxxxxxx: dec = 33'h000000100;
      32'b00000000000000000000000001xxxxxx: dec = 33'h000000080;
      32'b000000000000000000000000001xxxxx: dec = 33'h000000040;
      32'b0000000000000000000000000001xxxx: dec = 33'h000000020;
      32'b00000000000000000000000000001xxx: dec = 33'h000000010;
      32'b000000000000000000000000000001xx: dec = 33'h000000008;
      32'b0000000000000000000000000000001x: dec = 33'h000000004;
      32'b00000000000000000000000000000001: dec = 33'h000000002;
      default: dec = 33'h000000001;
    endcase
  end

// synopsys translate_on
endmodule