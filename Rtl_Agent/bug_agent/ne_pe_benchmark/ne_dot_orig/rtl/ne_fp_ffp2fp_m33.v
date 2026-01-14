// 浮点数格式转换模块：将不同格式的输入数据转换为目标浮点数格式
// 支持的输入格式包括：tf32、fp8、int8等
module ne_fp_ffp2fp_m33 (
    clk,                // 时钟输入
    a,                  // 输入数据总线
    z,                  // 输出数据总线（32位）
    mode,               // 转换模式选择：3'b100: tf32, 3'b010: fp8, 3'b001: int8
    z_is_infnan         // 输出状态：表示输出是否为无穷大或NaN
);

    // 参数定义
    parameter INTWI=22;  // 整数输入数据宽度
    parameter STWI = 3;  // 浮点状态位宽度（0:正常, 1:零, 2:无穷大, 3:NaN）
    parameter EWI  =10;  // 浮点指数位宽度
    parameter SWI  = 1;  // 浮点符号位宽度
    parameter SMWI =33;  // 浮点尾数位宽度（含符号位）

    // 局部参数
    localparam DATAW = STWI+EWI+SWI+SMWI;  // 总输入数据宽度
    localparam MWI   = SMWI -1 ;            // 尾数位宽度（不含符号位）

    // 端口定义
    input                   clk;            // 时钟输入
    input  [DATAW-1:0]      a;              // 47位输入数据总线
    input  [3:0]            mode;           // 转换模式选择
    output [31:0]           z;              // 32位输出数据
    output [1:0]            z_is_infnan;    // 输出状态：[1]无穷大, [0]NaN

    // 内部信号声明

    // 输入数据解析信号
    wire                a_is_zero;    // 输入是否为零
    wire                a_is_inf;     // 输入是否为无穷大
    wire                a_is_nan;     // 输入是否为NaN
    wire                a_s;          // 输入符号位
    wire [EWI-1  :0]    a_e;          // 输入指数位
    wire [SMWI-1 :0]    a_m;          // 输入尾数位
    wire [INTWI-1:0]    int_a;        // 整数输入数据

// 数据解析：从输入总线中提取各部分数据
assign a_is_zero = a[DATAW-3];                          // 输入零标志位（bit[44]）
assign a_is_inf  = a[DATAW-2];                          // 输入无穷大标志位（bit[45]）
assign a_is_nan  = a[DATAW-1];                          // 输入NaN标志位（bit[46]）
// 根据模式选择提取指数位（仅当模式不是int8时有效）
assign a_e       = {EWI {|mode[3:1]}} & a[SMWI+SWI+EWI-1:SMWI+SWI];//[43:34]
// 根据模式选择提取符号位（仅当模式不是int8时有效）
assign a_s       = {SWI {|mode[3:1]}} & a[SMWI+SWI-1];  //[33]
// 根据模式选择提取尾数位（仅当模式不是int8时有效）
assign a_m       = {SMWI{|mode[3:1]}} & a[SMWI-1:0];    //[32:0] (tf32/fp8/fp4)
// 整数数据处理：当模式为int8时提取整数输入
assign int_a     = {INTWI{mode[0]}} & a[INTWI-1:0];     //[21:0]
//---------------------------------------------
// 符号处理和尾数扩展
// 如果输入为负数，对尾数进行补码转换（取反加1）
wire [MWI+1:0] am = a_s ? ({1'b0, ~a_m[MWI-1:0]} + {{(MWI){1'd0}}, 1'b1}) : {1'd0, a_m[MWI-1:0]}; // [32][31].[30:0]

// 溢出处理：如果尾数转换后最高位为1，则设置为最大值
wire [MWI-1:0] am1 = am[MWI] ? {1'b1, {(MWI-1){1'b0}}} : am[MWI-1:0];  // [31].[30:0]

// 指数调整标志：当尾数溢出时，指数需要加1
wire am1_einc = am[MWI];  // am=33'b1_0000_0000时，e+1

// 零值检查：判断处理后的尾数是否为零
wire am1_iszero = ((~(|am1)) & (~a_is_inf) & (~a_is_nan)) | a_is_zero;

// 计算前导1的位置（用于规格化）
wire [5:0] am1cls;  // 前导1的位置编码（最大移位63位）
DW_lsd_w33 u_am1cls (.a({1'b0, am1}), .enc(am1cls), .dec());  // 实例化前导1检测器

// 计算规格化后的指数
wire [EWI+1:0] am2_e =  $signed({a_e[EWI-1], a_e[EWI-1:0]}) -  // 符号扩展输入指数
                        $signed({{(EWI+1-6){1'b0}}, am1cls[5:0]}) +  // 减去前导1位置
                        $signed({{(EWI+1-1){1'b0}}, am1_einc});  // 加上溢出调整

// 尾数规格化：将前导1移到最高位
wire [MWI-1:0] am2 = am1 << am1cls;  // [31].[30:8][7][6:0]


    // 寄存器流水线：用于同步数据和状态
    reg  [EWI  :0]   am2_e_r1;     // 流水线1：规格化后的指数
    reg  [MWI-1:0]   am2_r1;       // 流水线1：规格化后的尾数
    reg              a_is_inf_r1;  // 流水线1：无穷大标志
    reg              a_is_nan_r1;  // 流水线1：NaN标志
    reg              am1_iszero_r1;// 流水线1：零值标志
    reg              a_s_r1;       // 流水线1：符号位
    reg  [ 3:0]      mode_r1;      // 流水线1：转换模式
    reg  [INTWI-1:0] int_a_r1;     // 流水线1：整数输入

    // 流水线1：第一个时钟周期
    always@(posedge clk)begin
        am2_e_r1      <= am2_e[EWI:0];  // 存储规格化后的指数（用于fp8/fp16/fp4）
        am2_r1        <= am2;           // 存储规格化后的尾数
        a_is_inf_r1   <= a_is_inf;      // 存储无穷大标志
        a_is_nan_r1   <= a_is_nan;      // 存储NaN标志
        am1_iszero_r1 <= am1_iszero;    // 存储零值标志
        a_s_r1        <= a_s;           // 存储符号位
    end 

    // 流水线1：整数数据处理
    always@(posedge clk)begin
        int_a_r1      <= int_a;  // 存储整数输入（用于int8模式）
    end 

    // 流水线1：模式控制
    always@(posedge clk)begin
        mode_r1       <= mode;   // 存储转换模式（用于int8/fp8/fp16/fp4）
    end 

    // 规格化判断：确定输入数据的类型（零、无穷大、NaN、规格化数、子规格化数）
    wire          am2_iszero = am1_iszero_r1 ; // 零值标志
    wire          am2_isinf  = a_is_inf_r1 | ((($signed(am2_e_r1)>127)|(($signed(am2_e_r1)==127)&(&am2_r1[MWI-1:MWI-24-1]))) &(~am1_iszero_r1)&(~a_is_nan_r1)); // 无穷大标志
    wire          am2_isnan  = a_is_nan_r1 ; // NaN标志
    wire          am2_isnorm = (($signed(am2_e_r1) > -127)|(($signed(am2_e_r1)==-127)&(&am2_r1[MWI-1:MWI-24-1]))) &(~am2_isinf)&(~am2_iszero)&(~am2_isnan); // 规格化数标志
    wire          am2_issubnorm = (($signed(am2_e_r1) > (-127-23-1)))&(~am2_isnorm)&(~am2_isinf)&(~am2_iszero)&(~am2_isnan);  // 子规格化数标志

    // 规格化数处理：四舍五入和指数调整
    wire          am3_cien = am2_r1[MWI-24-1]; // 四舍五入进位标志
    wire [24:0]   am3      = am3_cien ? ({1'd0,am2_r1[MWI-1:MWI-24]} + 24'd1) : {1'd0,am2_r1[MWI-1:MWI-24]}; // 四舍五入后的尾数
    wire [EWI+1:0]am3_e    = $signed(am2_e_r1)+ 10'd127 +am3[24] ; // 调整后的指数（加上偏移量和可能的进位）
    
    // 子规格化数处理：计算移位量和调整尾数
    wire [EWI+1:0]am3_sub_rsf = -126 - $signed(am2_e_r1); // 子规格化移位量
    wire [MWI-1:0]am3_subm    = am2_r1 >> am3_sub_rsf[4:0]; // 右移后的尾数
    wire [24:0]   am3_sub_m   = am3_subm[MWI-1:MWI-24] + am3_subm[MWI-24-1]; // 子规格化尾数（含四舍五入）
    wire [EWI-1:0]am3_sub_e   = 0 ; // 子规格化数的指数为0
    
    // 输出选择：根据数据类型构建最终32位浮点数输出
    wire [31:0]   am4_z       = mode_r1[0]      ? {{(32-INTWI){int_a_r1[INTWI-1]}}, int_a_r1} : // int8模式：符号扩展整数输入
                                am2_iszero      ? {a_s_r1,31'd0   } : // 零值：符号位 + 全零
                                am2_isinf       ? {a_s_r1,8'hff,23'h0} : // 无穷大：符号位 + 全1指数 + 全零尾数
                                am2_isnan       ? {1'd0  ,8'hff,23'h40_0000} : // NaN：正号 + 全1指数 + 非零尾数
                                am2_isnorm      ? {a_s_r1,am3_e[7:0],am3[22:0]} : // 规格化数：符号位 + 调整后指数 + 四舍五入尾数
                                am2_issubnorm   ? {a_s_r1,am3_sub_e[7:0],am3_sub_m[22:0]} : // 子规格化数：符号位 + 零指数 + 调整后尾数
                                                  32'd0; // 默认值（不应该发生）

    // 输出赋值：将内部计算结果分配给模块输出端口
    assign z = am4_z;  // 32位浮点输出结果
    assign z_is_infnan = {am2_isinf ,am2_isnan};  // 输出状态：[1]无穷大标志, [0]NaN标志
endmodule  // 模块结束