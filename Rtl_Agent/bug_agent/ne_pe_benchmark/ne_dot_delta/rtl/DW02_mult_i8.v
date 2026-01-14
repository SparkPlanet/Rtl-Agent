////////////////////////////////////////////////////////////////////////////////
//
//       This confidential and proprietary software may be used only
//     as authorized by a licensing agreement from Synopsys Inc.
//     In the event of publication, the following notice is applicable:
//
//                    (C) COPYRIGHT 1994 - 2015 SYNOPSYS INC.
//                           ALL RIGHTS RESERVED
//
//       The entire notice above must be reproduced on all authorized
//     copies.
//
// AUTHOR:    KB WSFDB		June 30, 1994
//
// VERSION:   Simulation Architecture
//
// DesignWare_version: 1529080b
// DesignWare_release: J-2014.09-DWBB_201409.3
//
////////////////////////////////////////////////////////////////////////////////
//-----------------------------------------------------------------------------------
//
// ABSTRACT:  Multiplier
//           hA_widt-Bits * B_width-Bits => A_width+B_width Bits
//           Operands A and B can be either both signed (two's complement) or 
//	     both unsigned numbers. TC determines the coding of the input operands.
//           ie. TC = '1' => signed multiplication
//	         TC = '0' => unsigned multiplication
//
//	FIXED: by replacement with A tested working version
//		that not only doesn't multiplies right it does it
//		two times faster!
//  RPH 07/17/2002 
//      Rewrote to comply with the new guidelines
//------------------------------------------------------------------------------

module DW02_mult_i8(A,B,TC,PRODUCT);
//parameter	A_width = 8;
//parameter	B_width = 8;
   
input	[7:0]	A;
input	[7:0]	B;
input			TC;
output	[15:0]	PRODUCT;

wire	[15:0]	PRODUCT;

wire	[7:0]	temp_a;
wire	[7:0]	temp_b;
wire	[14:0]	long_temp1,long_temp2;

// synopsys translate_off 
  //-------------------------------------------------------------------------
  // Parameter legality check
  //-------------------------------------------------------------------------

assign	temp_a = (A[7])? (~A + 1'b1) : A;
assign	temp_b = (B[7])? (~B + 1'b1) : B;

assign	long_temp1 = temp_a * temp_b;
assign	long_temp2 = ~(long_temp1 - 1'b1);

assign	PRODUCT = ((^(A ^ A) !== 1'b0) || (^(B ^ B) !== 1'b0) || (^(TC ^ TC) !== 1'b0) ) ? {16{1'bX}} :
		  (TC)? (((A[7] ^ B[7]) && (|long_temp1))?
			 {1'b1,long_temp2} : {1'b0,long_temp1})
		     : A * B;
// synopsys translate_on
endmodule

