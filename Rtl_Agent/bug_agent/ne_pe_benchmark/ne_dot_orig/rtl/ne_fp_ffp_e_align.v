/**
 * 浮点数指数对齐模块
 * ne_fp_ffp_e_align.v
 *
 * 功能: 计算两个浮点数指数的最大值，并计算每个指数与最大值的差值
 * 支持多种操作模式，包括不同精度的浮点数（如TF32、FP8等）
 *
 * 输入:
 * - clk: 时钟信号
 * - op_mode: 操作模式选择
 * - a_e: TF32格式的指数输入（16个元素，每个9位）
 * - b_e: FP8格式的指数输入（16个元素，每个6位）
 *
 * 输出:
 * - e_max: 计算得到的最大指数值
 * - a_e_sub: a_e与e_max的差值（16个元素，每个6位）
 * - b_e_sub: b_e与e_max的差值（16个元素，每个6位）
 * - a_e_overflow: a_e的溢出标志（16位，每bit对应一个元素）
 * - b_e_overflow: b_e的溢出标志（16位，每bit对应一个元素）
 */
module ne_fp_ffp_e_align(
    input                   clk             ,   // 时钟信号

    input      [3:0]        op_mode         ,   // 操作模式选择信号
    input      [16*9-1:0]   a_e             ,   // TF32格式指数输入 (16个元素 × 9位)
    input      [16*6-1:0]   b_e             ,   // FP8格式指数输入 (16个元素 × 6位)
    output reg [8:0]        e_max           ,   // 最大指数输出
    output reg [16*6-1:0]   a_e_sub         ,   // a_e与e_max的差值 (16个元素 × 6位)
    output reg [16*6-1:0]   b_e_sub         ,   // b_e与e_max的差值 (16个元素 × 6位)
    output reg [15:0]       a_e_overflow    ,   // a_e溢出标志 (16位)
    output reg [15:0]       b_e_overflow        // b_e溢出标志 (16位)
 );

    genvar i; // 生成块索引变量
    
    // 内部寄存器定义
    reg  [16*9 - 1:0]       a_e_1r                 ; // a_e的1级寄存器缓存
    reg  [16*6 - 1:0]       b_e_1r                 ; // b_e的1级寄存器缓存
    wire [16*9 - 1:0]       minmax_in_a0           ; // 最大最小值模块的a通道输入
    wire [16*6 - 1:0]       minmax_in_b0           ; // 最大最小值模块的b通道输入
    wire [4*9 - 1:0]        max_e_a0_t             ; // a通道最大指数的临时输出
    wire [4*6 - 1:0]        max_e_b0_t             ; // b通道最大指数的临时输出
    reg  [4*9 - 1:0]        max_e_a0               ; // a通道最大指数的寄存器缓存
    reg  [4*6 - 1:0]        max_e_b0               ; // b通道最大指数的寄存器缓存
    wire  [8:0]             max_e_a                ; // 最终a通道最大指数
    wire  [5:0]             max_e_b                ; // 最终b通道最大指数
    wire [8:0]              max_e_t                ; // 最大指数的临时结果
    wire [16*9 - 1:0]       a_e_sub_tf32_t         ; // TF32格式a_e的差值临时计算
    wire [16*6 - 1:0]       a_e_sub_fp8_t          ; // FP8格式a_e的差值临时计算
    wire [16*9 - 1:0]       b_e_sub_fp8_t          ; // FP8格式b_e的差值临时计算
    wire [16*9 - 1:0]       a_e_sub_t              ; // a_e差值的最终临时结果
    wire [16*6 - 1:0]       b_e_sub_t              ; // b_e差值的最终临时结果
    wire [15:0]             a_e_overflow_bias      ; // a_e溢出标志（基于偏移）
    wire [15:0]             b_e_overflow_bias      ; // b_e溢出标志（基于偏移）
    wire [15:0]             a_e_overflow_tf32_mant ; // TF32格式a_e溢出标志（基于尾数）
    wire [15:0]             a_e_overflow_fp8_mant  ; // FP8格式a_e溢出标志（基于尾数）
    wire [15:0]             b_e_overflow_fp8_mant  ; // FP8格式b_e溢出标志（基于尾数）
    wire [15:0]             a_e_overflow_t         ; // a_e溢出标志的最终临时结果
    wire [15:0]             b_e_overflow_t         ; // b_e溢出标志的最终临时结果
    reg  [3:0]              op_mode_1r             ; // op_mode的1级寄存器缓存
    reg  [3:0]              op_mode_2r             ; // op_mode的2级寄存器缓存


    // 计算偏移值，根据操作模式选择
    // - op_mode[2] = 1: TF32格式，偏移为-252
    // - op_mode[1] = 1: FP8格式，偏移为-28
    // - 其他情况: 偏移为0
    wire [9:0]   bias   = op_mode[2] ?  10'b1_1_00000100:   // -126 + (-126) = -252
                          op_mode[1] ?  10'b1_1_11100100:   // -14 + (-14) = -28
                                       {10{1'b0}};
    reg  [8:0]   bias_r; // 偏移值的寄存器缓存


    // 计算最大指数值
    // - op_mode_1r[3] = 1: 设置特定值0x55
    // - op_mode_1r[2] = 1: 使用a通道的最大指数
    // - op_mode_1r[1] = 1: 比较a和b通道的最大指数，取较大值
    // - 其他情况: 返回0
    assign max_e_t = op_mode_1r[3] ? {3'd0,3'd5,3'd5}    :
                     op_mode_1r[2] ? max_e_a :    
                     op_mode_1r[1] ? $signed(max_e_a) > $signed({{3{max_e_b[5]}},max_e_b}) ? max_e_a : {{3{max_e_b[5]}}, max_e_b} : 9'd0;

    // 主寄存器更新逻辑
    always@(posedge clk) begin
        e_max      <= max_e_t    ;// 输出最大指数
        op_mode_1r <= op_mode    ;// 操作模式1级延迟
        op_mode_2r <= op_mode_1r ;// 操作模式2级延迟
        a_e_1r     <= a_e        ;// a_e信号1级延迟
    end

    // a通道相关寄存器更新
    always@(posedge clk) begin
        max_e_a0   <= max_e_a0_t ;// a通道最大指数的临时值缓存
        bias_r     <= bias[8:0]  ;// 偏移值缓存
    end

    // b通道相关寄存器更新
    always@(posedge clk) begin
        b_e_1r     <= b_e        ;// b_e信号1级延迟
    end

    // b通道最大指数寄存器更新
    always@(posedge clk) begin
        max_e_b0   <= max_e_b0_t ;// b通道最大指数的临时值缓存
    end
    

    // 指数差值计算生成块 - 为16个元素分别计算差值和溢出标志
    generate for(i = 0; i < 16; i = i + 1) begin: gen_e_sub
        
        // 计算TF32格式a_e的差值 (max_e_t - a_e_1r[i])
        assign a_e_sub_tf32_t[(i+1)*9-1:i*9] = op_mode_1r[0] ? 9'd0 : ($signed(max_e_t) - $signed(a_e_1r[(i+1)*9-1:i*9])); // 操作模式0时输出0，否则计算差值
        
        // 计算FP8格式a_e的差值（取TF32差值的低6位）
        assign a_e_sub_fp8_t[(i+1)*6-1:i*6]  = a_e_sub_tf32_t[i*9+5:i*9];
        
        // 计算FP8格式b_e的差值 (max_e_t - 符号扩展后的b_e_1r[i])
        assign b_e_sub_fp8_t[(i+1)*9-1:i*9]  = (op_mode_1r[2] | op_mode_1r[0]) ? 9'd0 : ($signed(max_e_t[8:0]) - $signed({{3{b_e_1r[i*6+5]}},b_e_1r[(i+1)*6-1:i*6]}));

        // 选择a_e的差值结果（TF32或FP8格式）
        assign a_e_sub_t[(i+1)*9-1:i*9]      = op_mode_1r[2] ? a_e_sub_tf32_t[(i+1)*9-1:i*9] : {{3{1'd0}}, a_e_sub_fp8_t[(i+1)*6-1:i*6]};
        
        // 选择b_e的差值结果（取FP8差值的低6位）
        assign b_e_sub_t[(i+1)*6-1:i*6]      = b_e_sub_fp8_t[i*9+5:i*9];

        // 计算a_e的偏移溢出标志
        assign a_e_overflow_bias[i]   = (|op_mode_1r[2]) & (a_e_sub_t[(i+1)*9-1] | (~a_e_sub_t[(i+1)*9-1] & a_e_sub_t[(i+1)*9-2] & (~(|a_e_sub_t[(i+1)*9-3:i*9]))));
        
        // b_e的偏移溢出标志（当前未使用，输出0）
        assign b_e_overflow_bias[i]   = 0; // op_mode_1r[1] & (b_e_sub_t[(i+1)*6-1] | (~b_e_sub_t[(i+1)*6-1] & b_e_sub_t[(i+1)*6-2] & (~(|b_e_sub_t[(i+1)*6-3:i*6]))));
        
        // 计算TF32格式a_e的尾数溢出标志（差值 >= 26）
        assign a_e_overflow_tf32_mant[i] = op_mode_1r[2] & (a_e_sub_t[(i+1)*9-1:i*9] >= 26);
        
        // 计算FP8格式a_e的尾数溢出标志（差值 >= 25）
        assign a_e_overflow_fp8_mant[i]  = op_mode_1r[1] & (a_e_sub_t[(i+1)*9-1:i*9] >= 25);
        
        // 计算FP8格式b_e的尾数溢出标志（差值 >= 25）
        assign b_e_overflow_fp8_mant[i]  = op_mode_1r[1] & (b_e_sub_t[(i+1)*6-1:i*6] >= 25);
        
        // 合并a_e的溢出标志（偏移溢出或尾数溢出）
        assign a_e_overflow_t[i] = (op_mode_1r[2] & (a_e_overflow_tf32_mant[i] | a_e_overflow_bias[i])) |  
                                   (op_mode_1r[1] & (a_e_overflow_fp8_mant[i] | a_e_overflow_bias[i]));
        
        // 合并b_e的溢出标志（偏移溢出或尾数溢出）
        assign b_e_overflow_t[i] = op_mode_1r[1] & (b_e_overflow_bias[i] | b_e_overflow_fp8_mant[i]);

        // 输出a_e的差值和溢出标志
        always@(posedge clk) begin
            a_e_sub[(i+1)*6-1:i*6] <= {6{|op_mode_1r[3:1]}} & a_e_sub_t[i*9+5:i*9]; // 根据操作模式选择是否输出
            a_e_overflow[i] <= {1{|op_mode_1r[3:1]}} & a_e_overflow_t[i]; // 根据操作模式选择是否输出
        end
        
        // 输出b_e的差值和溢出标志
        always@(posedge clk) begin
            b_e_sub[(i+1)*6-1:i*6] <= {6{op_mode_1r[1] | op_mode_1r[3]}} & b_e_sub_t[(i+1)*6-1:i*6]; // 根据操作模式选择是否输出
            b_e_overflow[i] <= {1{op_mode_1r[1] | op_mode_1r[3]}} & b_e_overflow_t[i]; // 根据操作模式选择是否输出
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



