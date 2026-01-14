module ne_fp_sfl_blk_w27s5 (a,s,z);

parameter BW_DATA = 27;
parameter BW_SF = 5;
parameter SIGNED = 0;

input [BW_DATA-1:0] a;
input [BW_SF-1:0] s;
output [BW_DATA-1:0] z;

    //initial begin
    //    if (BW_DATA < 1) begin
    //        $fatal("%t Shift data bit-width %0d is abnormal in fp_sfl_blk", $time, BW_DATA);
    //    end
    //    if (BW_SF > 6) begin
    //        $fatal("%t Shift index bit-width %0d is too large in fp_sfl_blk", $time, BW_SF);
    //    end
    //end

//wire [5:0] ss = {{(6-BW_SF){1'b0}}, s};
wire [5:0] ss = s;
wire [BW_DATA-1:0] di  [5:0];
wire [BW_DATA-1:0] tmp [5:0];
wire sign_bit;

generate if(SIGNED == 1) begin: gen_sign_bit_0
    assign sign_bit = a[BW_DATA-1];
end else begin: gen_sign_bit_1
    assign sign_bit = 1'b0;
end
endgenerate

genvar i;
generate for(i = 0; i < 6; i = i + 1) begin: gen_sfl
    if(i == 0) begin: gen_di_0
        assign di[i] = a;
    end else begin: gen_di_1
        assign di[i] = tmp[i-1];
    end

    // 展开指数运算: 2**0=1, 2**1=2, 2**2=4, 2**3=8, 2**4=16, 2**5=32
    if(i == 0) begin: gen_bw_i0
        if(BW_DATA > 1) begin: gen_bw_0
            assign tmp[i] = ss[i] ? {di[i][BW_DATA-1-1:0], {1{sign_bit}}} : di[i];
        end else begin: gen_bw_1
            assign tmp[i] = ss[i] ? {(BW_DATA){sign_bit}} : di[i];
        end
    end else if(i == 1) begin: gen_bw_i1
        if(BW_DATA > 2) begin: gen_bw_0
            assign tmp[i] = ss[i] ? {di[i][BW_DATA-2-1:0], {2{sign_bit}}} : di[i];
        end else begin: gen_bw_1
            assign tmp[i] = ss[i] ? {(BW_DATA){sign_bit}} : di[i];
        end
    end else if(i == 2) begin: gen_bw_i2
        if(BW_DATA > 4) begin: gen_bw_0
            assign tmp[i] = ss[i] ? {di[i][BW_DATA-4-1:0], {4{sign_bit}}} : di[i];
        end else begin: gen_bw_1
            assign tmp[i] = ss[i] ? {(BW_DATA){sign_bit}} : di[i];
        end
    end else if(i == 3) begin: gen_bw_i3
        if(BW_DATA > 8) begin: gen_bw_0
            assign tmp[i] = ss[i] ? {di[i][BW_DATA-8-1:0], {8{sign_bit}}} : di[i];
        end else begin: gen_bw_1
            assign tmp[i] = ss[i] ? {(BW_DATA){sign_bit}} : di[i];
        end
    end else if(i == 4) begin: gen_bw_i4
        if(BW_DATA > 16) begin: gen_bw_0
            assign tmp[i] = ss[i] ? {di[i][BW_DATA-16-1:0], {16{sign_bit}}} : di[i];
        end else begin: gen_bw_1
            assign tmp[i] = ss[i] ? {(BW_DATA){sign_bit}} : di[i];
        end
    end else if(i == 5) begin: gen_bw_i5
        if(BW_DATA > 32) begin: gen_bw_0
            assign tmp[i] = ss[i] ? {di[i][BW_DATA-32-1:0], {32{sign_bit}}} : di[i];
        end else begin: gen_bw_1
            assign tmp[i] = ss[i] ? {(BW_DATA){sign_bit}} : di[i];
        end
    end
end
endgenerate

generate if(BW_DATA > 32) begin: gen_out_0
    assign z = tmp[5];
end else if(BW_DATA > 16) begin: gen_out_1
    assign z = tmp[4];
end else if(BW_DATA > 8) begin: gen_out_2
    assign z = tmp[3];
end else if(BW_DATA > 4) begin: gen_out_3
    assign z = tmp[2];
end else if(BW_DATA > 2) begin: gen_out_4
    assign z = tmp[1];
end else if(BW_DATA > 1) begin: gen_out_5
    assign z = tmp[0];
end
endgenerate

// synopsys translate_on

endmodule