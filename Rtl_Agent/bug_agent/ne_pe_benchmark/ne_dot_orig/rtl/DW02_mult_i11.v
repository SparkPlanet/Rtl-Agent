////////////////////////////////////////////////////////////////////////////////
//
//       This confidential and proprietary software may be used only
//     as authorized by a licensing agreement from Synopsys Inc.
//     In the event of publication, the following notice is applicable:
//
//                    (C) COPYRIGHT 1994 - 221 SYNOPSYS INC.
//                           ALL RIGHTS RESERVED
//
//       The entire notice above must be reproduced on all authorized
//     copies.
//
// AUTHOR:    KB WSFDB		June 30, 1994
//
// VERSION:   Simulation Architecture
//
// DesignWare_version:2129080b
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

module DW02_mult_i11(A,B,TC,PRODUCT);
input	 [10:0]	A;
input	 [10:0]	B;
input	 		    TC;
output [21:0]	PRODUCT;

wire	[21:0]	PRODUCT;

wire	[10:0]	temp_a;
wire	[10:0]	temp_b;
wire	[20:0]	long_temp1,long_temp2;

// synopsys translate_off 
  //-------------------------------------------------------------------------
  // Parameter legality check
  //-------------------------------------------------------------------------

assign	temp_a = (A[10])? (~A + 1'b1) : A;
assign	temp_b = (B[10])? (~B + 1'b1) : B;

assign	long_temp1 = temp_a * temp_b;
assign	long_temp2 = ~(long_temp1 - 1'b1);

assign	PRODUCT = ((^(A ^ A) !== 1'b0) || (^(B ^ B) !== 1'b0) || (^(TC ^ TC) !== 1'b0) ) ? {22{1'bX}} :
		  (TC)? (((A[10] ^ B[10]) && (|long_temp1))?
			 {1'b1,long_temp2} : {1'b0,long_temp1})
		     : A * B;
// synopsys translate_on
endmodule

