module DW02_tree_w31n16( INPUT, OUT0, OUT1 );

// [FIX] Removed verif_en to avoid parser errors
parameter num_inputs = 16;
parameter input_width = 31;

//-----------------------------------------------------------------------------
// ports
input [num_inputs*input_width-1 : 0]    INPUT;
output [input_width-1:0]                OUT0, OUT1;

//-----------------------------------------------------------------------------
reg    [input_width-1:0]                OII0OOOI, O001l0I0;

//-----------------------------------------------------------------------------
// [FIX] Removed 'initial' blocks for parameter checking.
// HW-CBMC ignores initial blocks anyway, and they caused the parsing error.
//-----------------------------------------------------------------------------

always @ (INPUT) begin : IIIIO1Ol
  reg [input_width-1 : 0] I0lII01I [0 : num_inputs-1];
  reg [input_width-1 : 0] l10III00 [0 : num_inputs-1];
  reg [input_width-1 : 0] IIIO00Ol, lI0OII0O;
  integer I1I1O00I, O1OIIOII, IlI01lIO;

  for (O1OIIOII=0 ; O1OIIOII < num_inputs ; O1OIIOII=O1OIIOII+1) begin
    for (IlI01lIO=0 ; IlI01lIO < input_width ; IlI01lIO=IlI01lIO+1) begin
      IIIO00Ol[IlI01lIO] = INPUT[O1OIIOII*input_width+IlI01lIO];
    end 
    I0lII01I[O1OIIOII] = IIIO00Ol;
  end 

  I1I1O00I = num_inputs;

  while (I1I1O00I > 2)
  begin
    for (O1OIIOII=0 ; O1OIIOII < (I1I1O00I/3) ; O1OIIOII = O1OIIOII+1) begin
      l10III00[O1OIIOII*2] = I0lII01I[O1OIIOII*3] ^ I0lII01I[O1OIIOII*3+1] ^ I0lII01I[O1OIIOII*3+2];

      lI0OII0O = (I0lII01I[O1OIIOII*3] & I0lII01I[O1OIIOII*3+1]) |
                      (I0lII01I[O1OIIOII*3+1] & I0lII01I[O1OIIOII*3+2]) |
                      (I0lII01I[O1OIIOII*3] & I0lII01I[O1OIIOII*3+2]);

      l10III00[O1OIIOII*2+1] = lI0OII0O << 1;
    end
    if ((I1I1O00I % 3) > 0) begin
      for (O1OIIOII=0 ; O1OIIOII < (I1I1O00I % 3) ; O1OIIOII = O1OIIOII + 1)
        l10III00[2 * (I1I1O00I/3) + O1OIIOII] = I0lII01I[3 * (I1I1O00I/3) + O1OIIOII];
    end

    for (O1OIIOII=0 ; O1OIIOII < num_inputs ; O1OIIOII = O1OIIOII + 1)
      I0lII01I[O1OIIOII] = l10III00[O1OIIOII];
    I1I1O00I = I1I1O00I - (I1I1O00I/3);
  end
  OII0OOOI = I0lII01I[0];
  if (I1I1O00I > 1)
    O001l0I0 = I0lII01I[1];
  else
    O001l0I0 = {input_width{1'b0}};
end 

assign OUT0 = (^(INPUT ^ INPUT) !== 1'b0) ? {input_width{1'bx}} : OII0OOOI;
assign OUT1 = (^(INPUT ^ INPUT) !== 1'b0) ? {input_width{1'bx}} : O001l0I0;

endmodule