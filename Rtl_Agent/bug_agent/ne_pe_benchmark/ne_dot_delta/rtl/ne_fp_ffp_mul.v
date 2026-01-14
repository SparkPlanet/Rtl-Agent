module ne_fp_ffp_mul(
    input               clk ,

    input  [3:0]        op_mode             ,  //4'b0001: int8, 4'b0010: fp8, 4'b0100: tf32,4'b1000:fp4
    input               i_gp_zero_skip_en   ,
    input  [18:0]       a                   ,
    input  [18:0]       b                   ,
    output [5:0]        z0_e                ,
    output [8:0]        z1_e                ,
    output [31:0]       z_m                 
 );

    wire            ab_zskip  = i_gp_zero_skip_en  ;
    reg             ab0_is_zero_1r;     
    reg             ab1_is_zero_1r; 
    reg             ab2_is_zero_1r; 
    reg             ab3_is_zero_1r; 

    wire [7:0]      a_int8[0:1]    ;
    wire [8:0]      a_fp8[0:1]     ;
    wire [7:0]      b_int8[0:1]    ;
    wire [8:0]      b_fp8[0:1]     ;
    wire [3:0]      a_fp4[0:3]     ;//c0/c1/c32/c33
    wire [3:0]      b_fp4[0:3]     ;//c0/c1/c32/c33
    wire [3:0]      a_s            ;
    wire [3:0]      b_s            ;
    wire [1:0]      a_e_is_zero    ;
    wire [1:0]      a_e_is_max     ;
    wire [1:0]      a_m_is_zero    ;
    wire [1:0]      a_is_zero      ;
    wire [1:0]      a_is_inf       ;
    wire [1:0]      a_is_nan       ;
    wire [1:0]      a_is_subnorm   ;
    wire [1:0]      a_is_inf_nan   ;
    wire [1:0]      a_is_nan_zero  ;
    wire [1:0]      b_e_is_zero    ;
    wire [1:0]      b_e_is_max     ;
    wire [1:0]      b_m_is_zero    ;
    wire [1:0]      b_is_zero      ;
    wire [1:0]      b_is_inf       ;
    wire [1:0]      b_is_nan       ;
    wire [1:0]      b_is_subnorm   ;
    wire [1:0]      b_is_inf_nan   ;
    wire [1:0]      b_is_nan_zero  ;
    wire [10:0]     mul_a[0:1]     ;
    wire [10:0]     mul_b[0:1]     ;
    wire [21:0]     mul_z1         ;
    wire [15:0]     mul_z0         ;
    wire [9:0]      a_e0[0:1]      ;
    wire [9:0]      b_e0[0:1]      ;
    wire [9:0]      bias           ;
    wire [9:0]      a_e1[0:1]      ;
    wire [9:0]      b_e1[0:1]      ;
    wire [10:0]     z_e_t[0:1]     ;
    wire [9:0]      z_e[0:1]       ;
    wire [22:0]     z_m0_1         ;
    wire [8:0]      z_m0_0         ;
    wire [22:0]     z_m1_1         ;
    wire [22:0]     z_m1_11        ;
    wire [8:0]      z_m1_0         ;
    wire [8:0]      z_m1_00        ;
    wire [1:0]      e_overflow_pos ;
    wire [1:0]      e_overflow_neg ;
    wire [3:0]      z_s            ;
    reg  [3:0]      z_s_1r         ;
    wire [1:0]      z_is_zero      ;
    wire [1:0]      z_is_inf       ;
    wire [1:0]      z_is_nan       ;
    wire [2:0]      z0_status      ;
    wire [2:0]      z1_status      ;
    reg  [10:0]     mul_a_1_1r     ;
    reg  [10:0]     mul_b_1_1r     ;
    reg  [7:0]      mul_a_0_1r     ;
    reg  [7:0]      mul_b_0_1r     ;

    reg  [2:0]      z0_status_1r   ;
    reg  [2:0]      z1_status_1r   ;
    reg  [3:0]      op_mode_1r     ;
    wire [1:0]      a_hide_bit     ;
    wire [1:0]      b_hide_bit     ;

    wire [1:0]      a_fp4_m [0:3];    
    wire [1:0]      b_fp4_m [0:3];
    wire [2:0]      e_fp4   [0:3];
    wire [4:0]      z_m_fp4 [0:3];
    wire [4:0]      z_sm_fp4[0:3];
    wire [3:0]      z_is_zero_fp4;
 
    wire ab0_is_zero;
    wire ab1_is_zero;
    wire ab2_is_zero;
    wire ab3_is_zero;
   
    assign a_int8[0]   = {8{op_mode[0]}} & a[7:0]  ;
    assign a_int8[1]   = {8{op_mode[0]}} & a[16:9] ;
    assign b_int8[0]   = {8{op_mode[0]}} & b[7:0]  ;
    assign b_int8[1]   = {8{op_mode[0]}} & b[16:9] ;
    
    assign a_fp8[0]    = {9{op_mode[1]}} & a[8:0]  ;
    assign a_fp8[1]    = {9{op_mode[1]}} & a[17:9] ;
    assign b_fp8[0]    = {9{op_mode[1]}} & b[8:0]  ;
    assign b_fp8[1]    = {9{op_mode[1]}} & b[17:9] ;
    
    assign a_fp4[0]    = {4{op_mode[3]}} & a[3:0]  ;//c0
    assign a_fp4[1]    = {4{op_mode[3]}} & a[7:4]  ;//c1
    assign a_fp4[2]    = {4{op_mode[3]}} & a[12:9] ;//c32
    assign a_fp4[3]    = {4{op_mode[3]}} & a[16:13];//c33
    assign b_fp4[0]    = {4{op_mode[3]}} & b[3:0]  ;//c0
    assign b_fp4[1]    = {4{op_mode[3]}} & b[7:4]  ;//c1
    assign b_fp4[2]    = {4{op_mode[3]}} & b[12:9] ;//c32
    assign b_fp4[3]    = {4{op_mode[3]}} & b[16:13];//c33
    
        assign a_s[3]               = a_fp4[3][3];//fp4_c33
        assign a_s[2]               = a_fp4[2][3];//fp4_c32
        assign a_s[1]               = op_mode[3] ? a_fp4[1][3]:
                                      op_mode[1] ? a_fp8[1][8] : a_int8[1][7];
        assign a_s[0]               = op_mode[3] ? a_fp4[0][3] :
                                      op_mode[1] ? a_fp8[0][8] : a_int8[0][7];
        assign b_s[3]               = b_fp4[3][3];//fp4_c33
        assign b_s[2]               = b_fp4[2][3];//fp4_c32
        assign b_s[1]               = op_mode[3] ? b_fp4[1][3]:
                                      op_mode[1] ? b_fp8[1][8] : b_int8[1][7];
        assign b_s[0]               = op_mode[3] ? b_fp4[0][3] :
                                      op_mode[1] ? b_fp8[0][8] : b_int8[0][7];
    assign a_e_is_zero[1]       = ~(|a_fp8[1][7:3]);
    assign a_e_is_zero[0]       = ~(|a_fp8[0][7:3]);
    assign a_e_is_max[1]        = &a_fp8[1][7:3];
    assign a_e_is_max[0]        = &a_fp8[0][7:3];
    assign a_m_is_zero[1]       = ~(|a_fp8[1][2:0]);
    assign a_m_is_zero[0]       = ~(|a_fp8[0][2:0]);
    assign a_is_zero            = a_e_is_zero & a_m_is_zero;
    assign a_is_inf             = a_e_is_max & a_m_is_zero;
    assign a_is_nan             = a_e_is_max & (~a_m_is_zero);
    assign a_is_subnorm         = a_e_is_zero & (~a_m_is_zero);
    assign a_is_inf_nan         = a_e_is_max;
    assign a_is_nan_zero        = a_is_nan | a_is_zero;
    assign b_e_is_zero[1]       = ~(|b_fp8[1][7:3]);
    assign b_e_is_zero[0]       = ~(|b_fp8[0][7:3]);
    assign b_e_is_max[1]        =  &b_fp8[1][7:3];
    assign b_e_is_max[0]        = &b_fp8[0][7:3];
    assign b_m_is_zero[1]       =  ~(|b_fp8[1][2:0]);
    assign b_m_is_zero[0]       = ~(|b_fp8[0][2:0]);
    assign b_is_zero            = b_e_is_zero & b_m_is_zero;
    assign b_is_inf             = b_e_is_max & b_m_is_zero;
    assign b_is_nan             = b_e_is_max & (~b_m_is_zero);
    assign b_is_subnorm         = b_e_is_zero & (~b_m_is_zero);
    assign b_is_inf_nan         = b_e_is_max;
    assign b_is_nan_zero        = b_is_nan | b_is_zero;
    assign a_hide_bit           = (~a_is_subnorm) & (~a_is_zero) & (~a_is_inf_nan);
    assign b_hide_bit           = (~b_is_subnorm) & (~b_is_zero) & (~b_is_inf_nan);

    assign  a_fp4_m[0] = {|a_fp4[0][2:1],a_fp4[0][0]};     
    assign  a_fp4_m[1] = {|a_fp4[1][2:1],a_fp4[1][0]};     
    assign  a_fp4_m[2] = {|a_fp4[2][2:1],a_fp4[2][0]};     
    assign  a_fp4_m[3] = {|a_fp4[3][2:1],a_fp4[3][0]};     
    assign  b_fp4_m[0] = {|b_fp4[0][2:1],b_fp4[0][0]};     
    assign  b_fp4_m[1] = {|b_fp4[1][2:1],b_fp4[1][0]};     
    assign  b_fp4_m[2] = {|b_fp4[2][2:1],b_fp4[2][0]};     
    assign  b_fp4_m[3] = {|b_fp4[3][2:1],b_fp4[3][0]};     

    assign mul_a[1]             = op_mode[3] ? {a_fp4_m[3],7'd0,a_fp4_m[1]}:
                                  op_mode[1] ? {a_hide_bit[1], a_fp8[1][2:0], {7{1'b0}}}:
                                               {a_int8[1], {3{1'b0}}};
    assign mul_a[0]             = op_mode[3] ? {3'd0,a_fp4_m[2],4'd0,a_fp4_m[0]}:
                                  op_mode[1] ? {{3{1'b0}}, a_hide_bit[0], a_fp8[0][2:0], {4{1'b0}}} :
                                  op_mode[0] ? {{3{1'b0}}, a_int8[0]} : 
                                               {11{1'b0}};

    assign mul_b[1]             = op_mode[3] ? {b_fp4_m[3],7'd0,b_fp4_m[1]}:
                                  op_mode[1] ? {b_hide_bit[1], b_fp8[1][2:0], {7{1'b0}}} :
                                               {b_int8[1], {3{1'b0}}};
    assign mul_b[0]             = op_mode[3] ? {3'd0,b_fp4_m[2],4'd0,b_fp4_m[0]}:
                                  op_mode[1] ? {{3{1'b0}}, b_hide_bit[0], b_fp8[0][2:0], {4{1'b0}}} :
                                  op_mode[0] ? {{3{1'b0}}, b_int8[0]} : 
                                               {11{1'b0}};

    //wire [3:0] a0  = {a_hide_bit[0], a_fp8[0][2:0]};
    //wire [3:0] a1  = {a_hide_bit[1], a_fp8[1][2:0]};
    //wire [3:0] b0  = {b_hide_bit[0], b_fp8[0][2:0]};
    //wire [3:0] b1  = {b_hide_bit[1], b_fp8[1][2:0]};
    //
    //wire [4:0] ea0 = a_fp8[0][7:3];
    //wire [4:0] ea1 = a_fp8[1][7:3];
    //wire [4:0] eb0 = b_fp8[0][7:3];
    //wire [4:0] eb1 = b_fp8[1][7:3];

    //assign mul_a[2] = a_fp4_m[2];
    //assign mul_a[3] = a_fp4_m[3];
    //assign mul_b[2] = b_fp4_m[2];
    //assign mul_b[3] = b_fp4_m[3];
    
    wire [2:0]   a0_e = a_fp4[0][2] ? (a_fp4[0][1]? 3'd2 : 3'd1) : 3'd0;
    wire [2:0]   a1_e = a_fp4[1][2] ? (a_fp4[1][1]? 3'd2 : 3'd1) : 3'd0;
    wire [2:0]   a2_e = a_fp4[2][2] ? (a_fp4[2][1]? 3'd2 : 3'd1) : 3'd0;
    wire [2:0]   a3_e = a_fp4[3][2] ? (a_fp4[3][1]? 3'd2 : 3'd1) : 3'd0;
    wire [2:0]   b0_e = b_fp4[0][2] ? (b_fp4[0][1]? 3'd3 : 3'd2) : 3'd1;
    wire [2:0]   b1_e = b_fp4[1][2] ? (b_fp4[1][1]? 3'd3 : 3'd2) : 3'd1;
    wire [2:0]   b2_e = b_fp4[2][2] ? (b_fp4[2][1]? 3'd3 : 3'd2) : 3'd1;
    wire [2:0]   b3_e = b_fp4[3][2] ? (b_fp4[3][1]? 3'd3 : 3'd2) : 3'd1;
    assign e_fp4[0] = a0_e + b0_e;//a_fp4[0][2:1] - (|a_fp4[0][2:1]) +  b_fp4[0][2:1] - (|b_fp4[0][2:1]) + 1'd1;     
    assign e_fp4[1] = a1_e + b1_e;//a_fp4[1][2:1] - (|a_fp4[1][2:1]) +  b_fp4[1][2:1] - (|b_fp4[1][2:1]) + 1'd1;     
    assign e_fp4[2] = a2_e + b2_e;//a_fp4[2][2:1] - (|a_fp4[2][2:1]) +  b_fp4[2][2:1] - (|b_fp4[2][2:1]) + 1'd1;     
    assign e_fp4[3] = a3_e + b3_e;//a_fp4[3][2:1] - (|a_fp4[3][2:1]) +  b_fp4[3][2:1] - (|b_fp4[3][2:1]) + 1'd1; 

    assign z_is_zero_fp4[0] = (~(|a_fp4[0][2:0])) | (~(|b_fp4[0][2:0])) ;
    assign z_is_zero_fp4[1] = (~(|a_fp4[1][2:0])) | (~(|b_fp4[1][2:0])) ;
    assign z_is_zero_fp4[2] = (~(|a_fp4[2][2:0])) | (~(|b_fp4[2][2:0])) ;
    assign z_is_zero_fp4[3] = (~(|a_fp4[3][2:0])) | (~(|b_fp4[3][2:0])) ;

    DW02_mult_i11 u_dw_mul_1(
        .TC             (op_mode_1r[0] ) ,  // 有符号乘法控制（int8模式下有效）
        .A              (mul_a_1_1r    ) ,  // 乘法器输入A：11位（隐藏位+尾数或符号扩展）
        .B              (mul_b_1_1r    ) ,  // 乘法器输入B：11位（隐藏位+尾数或符号扩展）
        .PRODUCT        (mul_z1        )   // 乘法结果：22位
    );

    // 实例化8x8位乘法器，处理低位数据（int8/fp4模式）
    DW02_mult_i8 u_dw_mul_0(
        .TC             (op_mode_1r[0] ) ,  // 有符号乘法控制（int8模式下有效）
        .A              (mul_a_0_1r    ) ,  // 乘法器输入A：8位
        .B              (mul_b_0_1r    ) ,  // 乘法器输入B：8位
        .PRODUCT        (mul_z0        )   // 乘法结果：16位
    );


    assign a_e0[1]              = op_mode[1] ? {{2{1'b0}}, a_fp8[1][7:3], {3{1'b0}}} :
                                               {10{1'b0}};
    assign a_e0[0]              = op_mode[1] ? {{2{1'b0}}, a_fp8[0][7:3], {3{1'b0}}} :
                                               {10{1'b0}};
    assign b_e0[1]              = op_mode[1] ? {{2{1'b0}}, b_fp8[1][7:3], {3{1'b0}}} :
                                               {10{1'b0}};
    assign b_e0[0]              = op_mode[1] ? {{2{1'b0}}, b_fp8[0][7:3], {3{1'b0}}} :
                                               {10{1'b0}};
    
    assign bias                 = op_mode[1] ? {{3{1'b1}}, {3{1'b0}}, 1'b1, {3{1'b0}}} :
                                               {10{1'b0}};

    wire  [9:0] a_is_subnorm_1       = {{6{1'b0}}, a_is_subnorm[1],3'd0};
    wire  [9:0] a_is_subnorm_0       =                                            {{6{1'b0}}, a_is_subnorm[0],3'd0};
    wire  [9:0] b_is_subnorm_1       = {{6{1'b0}}, b_is_subnorm[1],3'd0};
    wire  [9:0] b_is_subnorm_0       =                                            {{6{1'b0}}, b_is_subnorm[0],3'd0};
    assign a_e1[1]              = $signed(a_e0[1]) + $signed(bias) + $signed(a_is_subnorm_1);//({{9{1'b0}}, a_is_subnorm[1]});  //signed dec; tf32:subnorm e=-126
    assign a_e1[0]              = $signed(a_e0[0]) + $signed(bias) + $signed(a_is_subnorm_0);//({{9{1'b0}}, a_is_subnorm[0]});
    assign b_e1[1]              = $signed(b_e0[1]) + $signed(bias) + $signed(b_is_subnorm_1);//({{9{1'b0}}, b_is_subnorm[1]});
    assign b_e1[0]              = $signed(b_e0[0]) + $signed(bias) + $signed(b_is_subnorm_0);//({{9{1'b0}}, b_is_subnorm[0]});
    wire  [9:0] z_e_t_1 =  {{6{1'b0}}, 1'b1,3'd0};
    wire  [9:0] z_e_t_0 =                                  {{6{1'b0}}, 1'b1,3'd0};
    assign z_e_t[1]             = {a_e1[1][9], a_e1[1]} + {b_e1[1][9], b_e1[1]} + z_e_t_1;//{{9{1'b0}}, 1'b1};   //signed dec; a*b=ea+eb(+1);fixed point mul 
    assign z_e_t[0]             = {a_e1[0][9], a_e1[0]} + {b_e1[0][9], b_e1[0]} + z_e_t_0;//{{9{1'b0}}, 1'b1};
    
    
    assign z_e[1]               = op_mode[3] ? {4'd0,{e_fp4[3]}&{3{~ab3_is_zero}},{e_fp4[1]}&{3{~ab1_is_zero}}}:    //fp4: mix_e=0;
                                  op_mode[1] ? (ab1_is_zero ? 10'b11_11100100 : {{3{z_e_t[1][9]}}, z_e_t[1][9:3]} ) : 
                                                10'd0;//signed dec
    assign z_e[0]               = op_mode[3] ? {4'd0,{e_fp4[2]}&{3{~ab2_is_zero}},{e_fp4[0]}&{3{~ab0_is_zero}}}:
                                  op_mode[1] ? (ab0_is_zero ? 10'b11_11100100 : {{3{z_e_t[0][9]}}, z_e_t[0][9:3]} ):
                                                10'd0; //fp8: min_e=-14+-14=-28
 
    assign z_m0_1               = {1'b0, mul_z1[21:14], {14{1'b0}}};  //1'b0 + m22
    assign z_m0_0               = {1'b0, mul_z0[15: 8]};

    assign z_m1_11              = (z_m0_1 ^ {23{z_s_1r[1]}}) + {{22{1'b0}}, z_s_1r[1]};  //add sign;  s1+m22;m is two's complement
    assign z_m1_1               = {z_s_1r[1],z_m1_11[21:0]};
    assign z_m1_00              = (z_m0_0 ^ {9{z_s_1r[0]}}) + {{8{1'b0}}, z_s_1r[0]};
    assign z_m1_0               = {z_s_1r[0],z_m1_00[7:0]};    
    
    assign z_m_fp4[0]  = op_mode_1r[3] ? (({4{z_s_1r[0]}} ^ mul_z0[ 3: 0]) + {4'd0,z_s_1r[0]}) : 5'd0;
    assign z_m_fp4[1]  = op_mode_1r[3] ? (({4{z_s_1r[1]}} ^ mul_z1[ 3: 0]) + {4'd0,z_s_1r[1]}) : 5'd0;
    assign z_m_fp4[2]  = op_mode_1r[3] ? (({4{z_s_1r[2]}} ^ mul_z0[15:12]) + {4'd0,z_s_1r[2]}) : 5'd0;
    assign z_m_fp4[3]  = op_mode_1r[3] ? (({4{z_s_1r[3]}} ^ mul_z1[21:18]) + {4'd0,z_s_1r[3]}) : 5'd0;
    
    assign z_sm_fp4[0] = {z_s_1r[0]&(|z_m_fp4[0][3:0]),z_m_fp4[0][3:0]}; //signed dec
    assign z_sm_fp4[1] = {z_s_1r[1]&(|z_m_fp4[1][3:0]),z_m_fp4[1][3:0]};
    assign z_sm_fp4[2] = {z_s_1r[2]&(|z_m_fp4[2][3:0]),z_m_fp4[2][3:0]};
    assign z_sm_fp4[3] = {z_s_1r[3]&(|z_m_fp4[3][3:0]),z_m_fp4[3][3:0]};
    
    assign e_overflow_pos[1]    = ~z_e[1][9] & z_e[1][8];
    assign e_overflow_pos[0]    = ~z_e[0][9] & z_e[0][8];
    assign e_overflow_neg[1]    = z_e[1][9] & (~z_e[1][8]);
    assign e_overflow_neg[0]    = z_e[0][9] & (~z_e[0][8]);

    assign z_s                  = a_s ^ b_s;
    assign z_is_zero            = (a_is_zero & (~b_is_inf_nan)) | ((~a_is_inf_nan) & b_is_zero);
    assign z_is_inf             = (a_is_inf & (~b_is_nan_zero)) | ((~a_is_nan_zero) & b_is_inf) | e_overflow_pos | e_overflow_neg;
    assign z_is_nan             = a_is_nan | b_is_nan | (a_is_inf & b_is_zero) | (a_is_zero & b_is_inf);

    assign z0_status            = {z_is_zero[0], z_is_inf[0], z_is_nan[0]};
    assign z1_status            = {z_is_zero[1], z_is_inf[1], z_is_nan[1]};
    assign z0_e                 = z_e[0][5:0];
    assign z1_e                 = z_e[1][8:0];
    assign z_m                  = op_mode_1r[3] ? {{ab3_is_zero_1r,2'd0,z_sm_fp4[3]&{5{~ab3_is_zero_1r}} },
                                                   {ab2_is_zero_1r,2'd0,z_sm_fp4[2]&{5{~ab2_is_zero_1r}} },
                                                   {ab1_is_zero_1r,2'd0,z_sm_fp4[1]&{5{~ab1_is_zero_1r}} },
                                                   {ab0_is_zero_1r,2'd0,z_sm_fp4[0]&{5{~ab0_is_zero_1r}} }}             :
                                  op_mode_1r[1] ? {{4{1'b0}}, z1_status_1r[2:0], z_m1_1[22:14]&{ 9{~ab1_is_zero_1r}} , 
                                                  { 4{1'b0}}, z0_status_1r[2:0], z_m1_0[ 8: 0]&{ 9{~ab0_is_zero_1r}}}   :
                                                  { mul_z1[21:6]&{16{~ab1_is_zero_1r}}, 
                                                    mul_z0[15:0]&{16{~ab0_is_zero_1r}}};
    
    
    assign ab0_is_zero = op_mode[3]?z_is_zero_fp4[0] : op_mode[0]?((~(|a_int8[0])) | (~(|b_int8[0]))) :   op_mode[1]  ?(a_is_zero[0]|b_is_zero[0]) : 1'd0 ;
    assign ab1_is_zero = op_mode[3]?z_is_zero_fp4[1] : op_mode[0]?((~(|a_int8[1])) | (~(|b_int8[1]))) : (|op_mode[1])?(a_is_zero[1]|b_is_zero[1]) : 1'd0 ;
    assign ab2_is_zero = op_mode[3]?z_is_zero_fp4[2] : 1'd0;
    assign ab3_is_zero = op_mode[3]?z_is_zero_fp4[3] : 1'd0;

    wire  [ 7:0] mul_a_0_1r_w;
    wire  [10:0] mul_a_1_1r_w;
    wire  [ 7:0] mul_b_0_1r_w;
    wire  [10:0] mul_b_1_1r_w;

    wire zero_skip_flag0  = (ab_zskip&((ab0_is_zero&op_mode[3])|(ab0_is_zero & |op_mode[1:0])));
    wire zero_skip_flag1  = (ab_zskip&((ab1_is_zero&op_mode[3])|(ab1_is_zero & |op_mode[1:0])));
    wire zero_skip_flag00 = (ab_zskip&((ab0_is_zero & |op_mode[1:0]))); 
    wire zero_skip_flag10 = (ab_zskip&((ab1_is_zero & |op_mode[1:0])));
    wire zero_skip_flag2  = (ab_zskip&((ab2_is_zero&op_mode[3])|(ab0_is_zero & |op_mode[1:0])));
    wire zero_skip_flag3  = (ab_zskip&((ab3_is_zero&op_mode[3])|(ab1_is_zero & |op_mode[1:0])));
                                        


    assign mul_a_0_1r_w[ 1:0] = ({2{zero_skip_flag0}}&mul_a_0_1r[ 1:0])|({2{~zero_skip_flag0}}& mul_a[0][ 1:0]);
    assign mul_b_0_1r_w[ 1:0] = ({2{zero_skip_flag0}}&mul_b_0_1r[ 1:0])|({2{~zero_skip_flag0}}& mul_b[0][ 1:0]);
    assign mul_a_1_1r_w[ 1:0] = ({2{zero_skip_flag1}}&mul_a_1_1r[ 1:0])|({2{~zero_skip_flag1}}& mul_a[1][ 1:0]);
    assign mul_b_1_1r_w[ 1:0] = ({2{zero_skip_flag1}}&mul_b_1_1r[ 1:0])|({2{~zero_skip_flag1}}& mul_b[1][ 1:0]);

    assign mul_a_0_1r_w[ 5:2] = ({4{zero_skip_flag00&(~op_mode[3])}}&mul_a_0_1r[ 5:2])|({4{~zero_skip_flag00&(~op_mode[3])}}& mul_a[0][ 5:2]);
    assign mul_b_0_1r_w[ 5:2] = ({4{zero_skip_flag00&(~op_mode[3])}}&mul_b_0_1r[ 5:2])|({4{~zero_skip_flag00&(~op_mode[3])}}& mul_b[0][ 5:2]);
    assign mul_a_1_1r_w[ 8:2] = ({7{zero_skip_flag10&(~op_mode[3])}}&mul_a_1_1r[ 8:2])|({7{~zero_skip_flag10&(~op_mode[3])}}& mul_a[1][ 8:2]);
    assign mul_b_1_1r_w[ 8:2] = ({7{zero_skip_flag10&(~op_mode[3])}}&mul_b_1_1r[ 8:2])|({7{~zero_skip_flag10&(~op_mode[3])}}& mul_b[1][ 8:2]);

    assign mul_a_0_1r_w[ 7:6] = ({2{zero_skip_flag2}}&mul_a_0_1r[ 7:6])|({2{~zero_skip_flag2}}& mul_a[0][ 7:6]);
    assign mul_b_0_1r_w[ 7:6] = ({2{zero_skip_flag2}}&mul_b_0_1r[ 7:6])|({2{~zero_skip_flag2}}& mul_b[0][ 7:6]);
    assign mul_a_1_1r_w[10:9] = ({2{zero_skip_flag3}}&mul_a_1_1r[10:9])|({2{~zero_skip_flag3}}& mul_a[1][10:9]);
    assign mul_b_1_1r_w[10:9] = ({2{zero_skip_flag3}}&mul_b_1_1r[10:9])|({2{~zero_skip_flag3}}& mul_b[1][10:9]);




    always@(posedge clk) begin
        op_mode_1r      <= op_mode     ;//int8_fp8_fp16_fp4
        ab1_is_zero_1r <= ab1_is_zero  ;//int8_fp8_fp16_fp4
        mul_a_1_1r     <= mul_a_1_1r_w ;//int8_fp8_fp16_fp4
        mul_b_1_1r     <= mul_b_1_1r_w ;      
    end 
    always@(posedge clk) begin

        ab0_is_zero_1r <= ab0_is_zero  ;//int8_fp8_fp4
        mul_a_0_1r     <= mul_a_0_1r_w ;//int8_fp8_fp4
        mul_b_0_1r     <= mul_b_0_1r_w ;
    end 
    always@(posedge clk) begin
        z_s_1r[1]      <= z_s[1]     ;  //fp8_fp16_fp4
    end 
    always@(posedge clk) begin
        z_s_1r[0]      <= z_s[0]     ;  //fp8_fp4
    end 
    always@(posedge clk) begin
        z1_status_1r   <= z1_status  ;  //fp8_fp16
    end 
    always@(posedge clk) begin
        z0_status_1r   <= z0_status  ;  //fp8
    end 
    always@(posedge clk) begin
        z_s_1r[3:2]    <= z_s[3:2]   ;//fp4
        ab2_is_zero_1r <= ab2_is_zero;//fp4
        ab3_is_zero_1r <= ab3_is_zero;//fp4
    end


endmodule



