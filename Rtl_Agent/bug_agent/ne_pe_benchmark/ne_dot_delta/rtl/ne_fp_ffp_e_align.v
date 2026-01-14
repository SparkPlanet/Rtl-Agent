module ne_fp_ffp_e_align(
    input               clk ,

    input      [3:0]        op_mode         ,
    input      [16*9-1:0]   a_e             ,
    input      [16*6-1:0]   b_e             ,
    output reg [8:0]        e_max           ,
    output reg [16*6-1:0]   a_e_sub         ,
    output reg [16*6-1:0]   b_e_sub         ,
    output reg [15:0]       a_e_overflow    ,
    output reg [15:0]       b_e_overflow    
 );

    genvar i;
    
    reg  [16*9 - 1:0]       a_e_1r                 ;
    reg  [16*6 - 1:0]       b_e_1r                 ;
    wire [16*9 - 1:0]       minmax_in_a0           ;
    wire [16*6 - 1:0]       minmax_in_b0           ;
    wire [4*9 - 1:0]        max_e_a0_t             ;
    wire [4*6 - 1:0]        max_e_b0_t             ;
    reg  [4*9 - 1:0]        max_e_a0               ;
    reg  [4*6 - 1:0]        max_e_b0               ;
    wire  [8:0]             max_e_a                ;
    wire  [5:0]             max_e_b                ;
    wire [8:0]              max_e_t                ;
    wire [16*9 - 1:0]       a_e_sub_tf32_t         ;
    wire [16*6 - 1:0]       a_e_sub_fp8_t          ;
    wire [16*9 - 1:0]       b_e_sub_fp8_t          ;
    wire [16*9 - 1:0]       a_e_sub_t              ;
    wire [16*6 - 1:0]       b_e_sub_t              ;
    wire [15:0]             a_e_overflow_bias      ;
    wire [15:0]             b_e_overflow_bias      ;
    wire [15:0]             a_e_overflow_tf32_mant ;
    wire [15:0]             a_e_overflow_fp8_mant  ;
    wire [15:0]             b_e_overflow_fp8_mant  ;
    wire [15:0]             a_e_overflow_t         ;
    wire [15:0]             b_e_overflow_t         ;
    reg  [3:0]              op_mode_1r             ;
    reg  [3:0]              op_mode_2r             ;


    wire [9:0]   bias   =  op_mode[1] ?  10'b1_1_11100100:   //-14+-14   =-28
                                       {10{1'b0}};
    reg  [8:0]   bias_r;


    assign max_e_t = op_mode_1r[3] ? {3'd0,3'd5,3'd5}    :
                     op_mode_1r[1] ? $signed(max_e_a) > $signed({{3{max_e_b[5]}},max_e_b}) ? max_e_a : {{3{max_e_b[5]}}, max_e_b} : 9'd0;

    always@(posedge clkg) begin
        e_max      <= max_e_t    ;//fp8_fp16_fp4
        op_mode_1r <= op_mode    ;//fp8_fp16_fp4
        op_mode_2r <= op_mode_1r ;//fp8_fp16_fp4
        a_e_1r     <= a_e        ;//fp8_fp16_fp4
    end
    always@(posedge clkg) begin
        max_e_a0   <= max_e_a0_t ;//fp8_fp16
        bias_r     <= bias[8:0]  ;//fp8_fp16
    end
    always@(posedge clkg) begin
        b_e_1r     <= b_e        ;//fp8_fp4
    end
    always@(posedge clkg) begin
        max_e_b0   <= max_e_b0_t ;//fp8
    end
    

    generate for(i = 0; i < 16; i = i + 1) begin: gen_e_sub
        
        assign a_e_sub_tf32_t[(i+1)*9-1:i*9] = op_mode_1r[0] ? 9'd0: ($signed(max_e_t) - $signed(a_e_1r[(i+1)*9-1:i*9])) ; // max - other = pos data
        assign a_e_sub_fp8_t[(i+1)*6-1:i*6]  =  a_e_sub_tf32_t[i*9+5:i*9]   ;
        assign b_e_sub_fp8_t[(i+1)*9-1:i*9]  = op_mode_1r[0]?9'd0: ($signed(max_e_t[8:0]) - $signed({{3{b_e_1r[i*6+5]}},b_e_1r[(i+1)*6-1:i*6]}));

        assign a_e_sub_t[(i+1)*9-1:i*9]      =  {{3{1'd0}}, a_e_sub_fp8_t[(i+1)*6-1:i*6]};
        assign b_e_sub_t[(i+1)*6-1:i*6]      = b_e_sub_fp8_t[i*9+5:i*9];

        assign a_e_overflow_bias[i]   = (1'b0) & (a_e_sub_t[i*9+8] | (~a_e_sub_t[i*9+8] & a_e_sub_t[i*9+7] & (~(|a_e_sub_t[i*9+6:i*9]))));  // a_e_sub overflow
//        assign a_e_overflow_bias[i]   = (|op_mode_1r[2]) & (a_e_sub_t[i*9+8] | (~a_e_sub_t[i*9+8] & a_e_sub_t[i*9+7] & (~(|a_e_sub_t[i*9+6:i*9]))));  // a_e_sub overflow
        assign b_e_overflow_bias[i]   =   0;//op_mode_1r[  1]  & (b_e_sub_t[i*6+5] | (~b_e_sub_t[i*6+5] & b_e_sub_t[i*6+4] & (~(|b_e_sub_t[i*6+3:i*6]))));
        assign a_e_overflow_tf32_mant[i] = op_mode_1r[2]&(/*$signed*/(a_e_sub_t[(i+1)*9-1:i*9]) >= 26);
        assign a_e_overflow_fp8_mant[i]  = op_mode_1r[1]&(/*$signed*/(a_e_sub_t[(i+1)*9-1:i*9]) >= 25);
        assign b_e_overflow_fp8_mant[i]  = op_mode_1r[1]&(/*$signed*/(b_e_sub_t[(i+1)*6-1:i*6]) >= 25);
        assign a_e_overflow_t[i] = (op_mode_1r[1]&(a_e_overflow_fp8_mant[i]  | a_e_overflow_bias[i])) ;
        assign b_e_overflow_t[i] =  op_mode_1r[1]&(b_e_overflow_bias[i] | b_e_overflow_fp8_mant[i]);

        always@(posedge clkg)begin
            a_e_sub[(i+1)*6-1:i*6] <= {6{|op_mode_1r[3:1]}} & a_e_sub_t[i*9+5:i*9];//fp8_fp16_fp4
            a_e_overflow[i] <= {1{|op_mode_1r[3:1]}} & a_e_overflow_t[i];
        end
        always@(posedge clkg)begin
            b_e_sub[(i+1)*6-1:i*6] <= {6{op_mode_1r[1] | op_mode_1r[3]}} & b_e_sub_t[(i+1)*6-1:i*6];//fp8_fp4
            b_e_overflow[i] <= {1{op_mode_1r[1] | op_mode_1r[3]}} & b_e_overflow_t[i];
        end
    end
    endgenerate

// 最大指数计算模块 - 将输入分为4组，每组4个元素，分别计算最大值（展开后的代码）
    // i=0 情况
    // 为a通道生成最大最小值模块的输入（op_mode[3]为1时输出0，否则使用原始输入）
    assign minmax_in_a0[35:0] = op_mode[3] ? 36'd0 : a_e[35:0];
    
    // 为b通道生成最大最小值模块的输入（op_mode[3]为1时输出0，否则使用原始输入）
    assign minmax_in_b0[23:0] = op_mode[3] ? 24'd0 : b_e[23:0];

    // a通道的最大最小值模块实例（4个9位输入）- i=0
    DW_minmax_w9n4 u_minmax_a0_0(
        .a          (minmax_in_a0[35:0] ), // 4个9位输入（共36位）
        .tc         (1'b1               ), // 有符号比较（tc=1）
        .min_max    (1'b1               ), // 输出最大值（min_max=1）
        .value      (max_e_a0_t[8:0]    ), // 最大值输出（9位）
        .index      (                   )  // 最大值索引（未使用）
    );
     
    // b通道的最大最小值模块实例（4个6位输入）- i=0
    DW_minmax_w6n4 u_minmax_b0_0(
        .a          (minmax_in_b0[23:0] ), // 4个6位输入（共24位）
        .tc         (1'b1               ), // 有符号比较（tc=1）
        .min_max    (1'b1               ), // 输出最大值（min_max=1）
        .value      (max_e_b0_t[5:0]    ), // 最大值输出（6位）
        .index      (                   )  // 最大值索引（未使用）
    );

    // i=1 情况
    // 为a通道生成最大最小值模块的输入（op_mode[3]为1时输出0，否则使用原始输入）
    assign minmax_in_a0[71:36] = op_mode[3] ? 36'd0 : a_e[71:36];
    
    // 为b通道生成最大最小值模块的输入（op_mode[3]为1时输出0，否则使用原始输入）
    assign minmax_in_b0[47:24] = op_mode[3] ? 24'd0 : b_e[47:24];

    // a通道的最大最小值模块实例（4个9位输入）- i=1
    DW_minmax_w9n4 u_minmax_a0_1(
        .a          (minmax_in_a0[71:36] ), // 4个9位输入（共36位）
        .tc         (1'b1                ), // 有符号比较（tc=1）
        .min_max    (1'b1                ), // 输出最大值（min_max=1）
        .value      (max_e_a0_t[17:9]    ), // 最大值输出（9位）
        .index      (                    )  // 最大值索引（未使用）
    );
     
    // b通道的最大最小值模块实例（4个6位输入）- i=1
    DW_minmax_w6n4 u_minmax_b0_1(
        .a          (minmax_in_b0[47:24] ), // 4个6位输入（共24位）
        .tc         (1'b1                ), // 有符号比较（tc=1）
        .min_max    (1'b1                ), // 输出最大值（min_max=1）
        .value      (max_e_b0_t[11:6]    ), // 最大值输出（6位）
        .index      (                    )  // 最大值索引（未使用）
    );

    // i=2 情况
    // 为a通道生成最大最小值模块的输入（op_mode[3]为1时输出0，否则使用原始输入）
    assign minmax_in_a0[107:72] = op_mode[3] ? 36'd0 : a_e[107:72];
    
    // 为b通道生成最大最小值模块实例（4个6位输入）- i=2
    assign minmax_in_b0[71:48] = op_mode[3] ? 24'd0 : b_e[71:48];

    // a通道的最大最小值模块实例（4个9位输入）- i=2
    DW_minmax_w9n4 u_minmax_a0_2(
        .a          (minmax_in_a0[107:72] ), // 4个9位输入（共36位）
        .tc         (1'b1                 ), // 有符号比较（tc=1）
        .min_max    (1'b1                 ), // 输出最大值（min_max=1）
        .value      (max_e_a0_t[26:18]    ), // 最大值输出（9位）
        .index      (                     )  // 最大值索引（未使用）
    );
     
    // b通道的最大最小值模块实例（4个6位输入）- i=2
    DW_minmax_w6n4 u_minmax_b0_2(
        .a          (minmax_in_b0[71:48] ), // 4个6位输入（共24位）
        .tc         (1'b1                 ), // 有符号比较（tc=1）
        .min_max    (1'b1                 ), // 输出最大值（min_max=1）
        .value      (max_e_b0_t[17:12]    ), // 最大值输出（6位）
        .index      (                     )  // 最大值索引（未使用）
    );

    // i=3 情况
    // 为a通道生成最大最小值模块的输入（op_mode[3]为1时输出0，否则使用原始输入）
    assign minmax_in_a0[143:108] = op_mode[3] ? 36'd0 : a_e[143:108];
    
    // 为b通道生成最大最小值模块实例（4个6位输入）- i=3
    assign minmax_in_b0[95:72] = op_mode[3] ? 24'd0 : b_e[95:72];

    // a通道的最大最小值模块实例（4个9位输入）- i=3
    DW_minmax_w9n4 u_minmax_a0_3(
        .a          (minmax_in_a0[143:108] ), // 4个9位输入（共36位）
        .tc         (1'b1                  ), // 有符号比较（tc=1）
        .min_max    (1'b1                  ), // 输出最大值（min_max=1）
        .value      (max_e_a0_t[35:27]     ), // 最大值输出（9位）
        .index      (                      )  // 最大值索引（未使用）
    );
     
    // b通道的最大最小值模块实例（4个6位输入）- i=3
    DW_minmax_w6n4 u_minmax_b0_3(
        .a          (minmax_in_b0[95:72] ), // 4个6位输入（共24位）
        .tc         (1'b1                  ), // 有符号比较（tc=1）
        .min_max    (1'b1                  ), // 输出最大值（min_max=1）
        .value      (max_e_b0_t[23:18]     ), // 最大值输出（6位）
        .index      (                      )  // 最大值索引（未使用）
    );

    // a通道最终最大指数计算（5个9位输入）
    DW_minmax_w9n5 u_minmax_a1(
        .a          ({max_e_a0,bias_r[8:0]} ), // 4个组最大值+1个偏移值（共5个9位输入）
        .tc         (1'b1     ), // 有符号比较（tc=1）
        .min_max    (1'b1     ), // 输出最大值（min_max=1）
        .value      (max_e_a  ), // 最终a通道最大指数（9位）
        .index      (         )  // 最大值索引（未使用）
    );

    // b通道最终最大指数计算（5个6位输入）
    DW_minmax_w6n5 u_minmax_b1(
        .a          ({max_e_b0,bias_r[5:0]} ), // 4个组最大值+1个偏移值（共5个6位输入）
        .tc         (1'b1     ), // 有符号比较（tc=1）
        .min_max    (1'b1     ), // 输出最大值（min_max=1）
        .value      (max_e_b  ), // 最终b通道最大指数（6位）
        .index      (         )  // 最大值索引（未使用）
    );


endmodule



