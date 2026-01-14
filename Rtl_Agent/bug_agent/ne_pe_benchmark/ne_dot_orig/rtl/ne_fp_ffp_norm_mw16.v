module ne_fp_ffp_norm_mw16 (
    a,
    z,
    mode
);

parameter SW = 1;
parameter EW = 10;
parameter MW = 16;
parameter CLOG2_MW=4;//即$clog2(MW)的数值
parameter CLOG2_MW_MINUS1=4;//即$clog2(MW-1)的数值

parameter BW_STATUS = 3;

localparam BW = BW_STATUS+SW+EW+MW;
//localparam [EW-1:0] BIAS = (2 ** (EW - 1)) - 1;
localparam [EW-1:0] BIAS = 511;
localparam signed [EW-1:0] BIAS_NEG = -511;

input [BW-1:0] a;
output [BW-1:0] z;
input [2:0] mode;

wire a_s;
wire [EW-1:0] a_e;
wire [MW-1:0] a_m;
wire a_e_is_zero;
wire a_m_is_zero;
wire a_e_is_max;
wire [CLOG2_MW-1:0] a_m_cls;//此处3代表
wire z_s;
wire [MW-1:0] z_m;
wire [EW-1:0] z_e0;
wire [EW-1:0] z_e;
wire [SW+EW+MW-1:0] z_d;
wire [SW+EW+MW-1:0] z_o;
wire a_is_zero;
wire a_is_inf;
wire a_is_nan;
wire z_is_zero;
wire z_is_inf;
wire z_is_nan;
wire [SW+EW+MW-1:0] z_zero;
wire [SW+EW+MW-1:0] z_inf;
wire [SW+EW+MW-1:0] z_nan;
wire [MW-1:0] a_m_sfl;
wire e_overflow_pos;
wire e_overflow_neg;

    wire [BW_STATUS-1:0] a_status;
generate if(BW_STATUS > 0) begin: gen_unpack_with_status
    //wire [BW_STATUS-1:0] a_status;
    assign {a_status, a_s, a_e, a_m} = (~mode[0]) ? a : {BW{1'b0}}; //tf32/fp8
    assign a_is_nan = a_status[2];
    assign a_is_inf = a_status[1];
    assign a_is_zero = a_status[0];
end else begin: gen_unpack_without_status
    assign {a_s, a_e, a_m} = a;
    assign a_e_is_zero = $signed(a_e) == -BIAS;
    assign a_e_is_max = a_e == BIAS + 1;
    assign a_m_is_zero = ~(|a_m);
    assign a_is_zero = a_e_is_zero & a_m_is_zero;
    assign a_is_inf = a_e_is_max & a_m_is_zero;
    assign a_is_nan = a_e_is_max & (~a_m_is_zero);
end
endgenerate

assign z_s = a_s;

// 移除参数化，使用默认参数值
ne_fp_sfl_blk_w16s4 u_sfl(
    .a (a_m),
    .s (a_m_cls),
    .z (a_m_sfl)
);

wire z_m_neg_overflow = a_m[MW-2] & (~|a_m_sfl[MW-3:0]); // s+s+{MW-2{1'd0}} //am=111111100000
assign z_m = z_m_neg_overflow ? {a_m[MW-1:MW-2],a_m_sfl[MW-2:1]} : {a_m[MW-1:MW-2], a_m_sfl[MW-3:0]};
assign z_e0 = a_e - {{(EW-CLOG2_MW){1'b0}}, a_m_cls} + {{(EW-1){1'b0}},z_m_neg_overflow};
assign e_overflow_pos = ~z_e0[EW-1] & (z_e0[EW-2] | z_e0[EW-3]);
assign e_overflow_neg = z_e0[EW-1] & ((~z_e0[EW-2]) | (~z_e0[EW-3]));
assign z_e = z_e0;

assign z_is_nan = a_is_nan;
assign z_is_inf = a_is_inf;
assign z_is_zero = a_is_zero | ((~|z_m)&(~a_is_inf)&(~a_is_nan));

    wire [BW_STATUS-1:0] z_status;
generate if(BW_STATUS > 0) begin: gen_out_with_status
//    wire [BW_STATUS-1:0] z_status;
    assign z_status = {z_is_nan, z_is_inf, z_is_zero};
    assign z = {z_status, z_o};
end else begin: gen_out_without_status
    assign z = z_o;
end
endgenerate

assign z_d = {z_s, z_e, z_m};
wire [EW-1:0] z_e_max = BIAS + 10'd1;
wire signed [EW-1:0] z_e_zero = BIAS_NEG;
assign z_nan = {z_s, z_e_max, {z_s,z_s,1'b1, {(MW-3){1'b0}}}};
assign z_zero = {z_s, z_e_zero, {z_s,z_s,{(MW-2){1'b0}}}};
assign z_inf = {z_s, z_e_max, {z_s,z_s,{(MW-2){1'b0}}}};
assign z_o = mode[0] ? a[BW-BW_STATUS-1:0] : z_is_nan ? z_nan : z_is_inf ? z_inf : z_is_zero ? z_zero : z_d;

wire [CLOG2_MW_MINUS1-1:0] a_m_cls_w;

generate if(CLOG2_MW - CLOG2_MW_MINUS1 > 0) begin: gen_about_a_m_cls_0
    assign a_m_cls = {{(CLOG2_MW - CLOG2_MW_MINUS1){1'b0}},a_m_cls_w};
end else begin: gen_about_a_m_cls_1
    assign a_m_cls = a_m_cls_w;
end
endgenerate

// 移除参数化，使用默认参数值
DW_lsd_w15 u_cls(
    .a(a_m[MW-2:0]), 
    .enc(a_m_cls_w), 
    .dec()
);

endmodule