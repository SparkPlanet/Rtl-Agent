module ne_fp_ffp2fp_m33 (
    clk,
    a,
    z,
    mode,                //3'b100: tf32, 3'b010: fp8, 3'b001: int8
    z_is_infnan
);
    parameter INTWI=22; //input int data width
    parameter STWI = 3; //input ffp status width
    parameter EWI  =10; //input ffp w width
    parameter SWI  = 1; //input ffp sign width
    parameter SMWI =33; //input ffp m width (sign bit + m bit)

    localparam DATAW = STWI+EWI+SWI+SMWI;
    localparam MWI   = SMWI -1 ;

    input                   clk           ;
    input                   clk ;
    input                   clk     ;

    input  [DATAW-1:0]      a   ;
    input  [3:0]            mode;
    output [31:0]           z;
    output [1:0]            z_is_infnan;

wire                a_is_zero            ;
wire                a_is_inf             ;
wire                a_is_nan             ;
wire                a_s                  ;
wire [EWI-1  :0]    a_e                  ;
wire [SMWI-1  :0]   a_m                  ;
wire [INTWI-1:0]    int_a                ;


//unpack
assign a_is_zero            = a[DATAW-3];//[44];
assign a_is_inf             = a[DATAW-2];//[45];
assign a_is_nan             = a[DATAW-1];//[46];
assign a_e                  = {EWI {|mode[3:1]}} & a[SMWI+SWI+EWI-1:SMWI+SWI];//[43:34];
assign a_s                  = {SWI {|mode[3:1]}} & a[SMWI+SWI-1];//[33];
assign a_m                  = {SMWI{|mode[3:1]}} & a[SMWI-1:0];//[32:0]; //tf32/fp8/fp4
//int process
assign int_a                = {INTWI{mode[0]}}&a[INTWI-1:0];//[21:0];
//---------------------------------------------
    wire [MWI-1+1:0] am      = a_s ? ({1'b0, ~a_m[MWI-1:0]} + {{(MWI){1'd0}},{1'b1}}) : {1'd0,a_m[MWI-1:0]}; //[32][31].[30:0]
    wire [MWI-1  :0] am1     = am[MWI]? {1'b1,{(MWI-1){1'b0}}} : am[MWI-1:0] ;  //[31].[30:0]
    wire          am1_einc   = am[MWI]; // am=33'b1_0000_0000, e+1
    wire          am1_iszero = ((~(|am1)) & (~a_is_inf) & (~a_is_nan)) | a_is_zero;
    wire [   5:0] am1cls; //shift < maxshift 63
    //DW_lsd #(MWI+1)  u_am1cls  (.a({1'b0, am1}  ), .enc(am1cls ), .dec());
    DW_lsd_w33 u_am1cls (.a({1'b0, am1}), .enc(am1cls), .dec());  // 实例化前导1检测器
    wire [EWI+1:0] am2_e =  $signed({a_e[EWI-1],a_e[EWI-1:0]}) - 
                            $signed({{(EWI+1-6){1'b0}},am1cls[5:0]}) + 
                            $signed({{(EWI+1-1){1'b0}},am1_einc}) ;
    wire [MWI-1:0] am2    = am1 << am1cls;   //[31].[30:8][7][6:0]


    reg  [EWI  :0]   am2_e_r1     ;
    reg  [MWI-1:0]   am2_r1       ;
    reg           a_is_inf_r1  ;
    reg           a_is_nan_r1  ;
    reg           am1_iszero_r1;
    reg           a_s_r1       ;    
    reg [ 3:0]    mode_r1      ;
    reg [INTWI-1:0]  int_a_r1     ;

    always@(posedge clk)begin
        am2_e_r1      <= am2_e[EWI:0];//fp8_fp16_fp4
        am2_r1        <= am2  ;
        a_is_inf_r1   <= a_is_inf;
        a_is_nan_r1   <= a_is_nan;
        am1_iszero_r1 <= am1_iszero;
        a_s_r1        <= a_s;
    end 
    always@(posedge clk)begin
        int_a_r1      <= int_a;//int8
    end 
    always@(posedge clk)begin
        mode_r1       <= mode ;//int8_fp8_fp16_fp4
    end 

    wire          am2_iszero = am1_iszero_r1 ;
    wire          am2_isinf  = a_is_inf_r1 | ((($signed(am2_e_r1)>127)|(($signed(am2_e_r1)==127)&(&am2_r1[MWI-1:MWI-24-1]))) &(~am1_iszero_r1)&(~a_is_nan_r1)); 
    wire          am2_isnan  = a_is_nan_r1 ;
    wire          am2_isnorm = (($signed(am2_e_r1) > -127)|(($signed(am2_e_r1)==-127)&(&am2_r1[MWI-1:MWI-24-1]))) &(~am2_isinf)&(~am2_iszero)&(~am2_isnan);
    wire          am2_issubnorm = (($signed(am2_e_r1) > (-127-23-1)))&(~am2_isnorm)&(~am2_isinf)&(~am2_iszero)&(~am2_isnan);  //[31].[30:0] <=> 0.00000000_00000000_0000000_[31]

    wire          am3_cien = am2_r1[MWI-24-1];
    wire [24:0]   am3      = am3_cien ? ({1'd0,am2_r1[MWI-1:MWI-24]} + 24'd1) : {1'd0,am2_r1[MWI-1:MWI-24]};
    wire [EWI+1:0]am3_e    = $signed(am2_e_r1)+ 10'd127 +am3[24] ;
    
    wire [EWI+1:0]am3_sub_rsf = -126 - $signed(am2_e_r1);
    wire [MWI-1:0]am3_subm    = am2_r1 >> am3_sub_rsf[4:0];
    wire [24:0]   am3_sub_m   = am3_subm[MWI-1:MWI-24] + am3_subm[MWI-24-1]; //am3_sub_cien = am3_subm[7]
    wire [EWI-1:0]am3_sub_e   = 0 ;
    
    wire [31:0]   am4_z       = mode_r1[0]      ? {{(32-INTWI){int_a_r1[INTWI-1]}}, int_a_r1} : 
                                am2_iszero      ? {a_s_r1,31'd0   } :
                                am2_isinf       ? {a_s_r1,8'hff,23'h0} :
                                am2_isnan       ? {1'd0  ,8'hff,23'h40_0000} :
                                am2_isnorm      ? {a_s_r1,am3_e[7:0],am3[22:0]} :
                                am2_issubnorm   ? {a_s_r1,am3_sub_e[7:0],am3_sub_m[22:0]} :         
                                                  32'd0;//{a_s_r1,31'd0};  // < subnorm

    assign z = am4_z;
    assign z_is_infnan = {am2_isinf ,am2_isnan};



endmodule






