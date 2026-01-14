module ne_dot( 
    input             clk,

    input             i_gp_zero_skip_en  ,
    input [4:0]       mode               ,//{mx,fp4,tf32,fp8,int8}
    input             fp_vld             ,
    input [32*19-1:0] fp_a               ,
    input [32*19-1:0] fp_b               ,
    input [31:0]      a_scale            ,
    input [31:0]      b_scale            , 

    output reg [31:0] fp_z               ,
    output            fp_z_vld_pre       ,
    output reg        fp_z_vld           , 
    output reg        fp_z_int           ,
    output reg [ 1:0] fp_infnan          
 );

    //wire i_gp_zero_skip_en = 0;
    wire [4:0]                  mul_op_mode        ;
    wire [4:0]                  e_align_op_mode    ;
    wire                        e_align_vld        ;
    reg  [4:0]                  e_align_op_mode_1r ;
    reg                         e_align_vld_1r     ;
    reg  [4:0]                  addtree_op_mode    ;
    reg                         addtree_vld        ;
    reg  [4:0]                  addtree_op_mode_1r ;
    reg                         addtree_vld_1r     ;
    reg  [4:0]                  norm1_op_mode      ;
    reg                         norm1_vld          ;
    reg  [4:0]                  ffpadd1_op_mode    ;
    reg                         ffpadd1_vld        ;
    reg  [4:0]                  ffpadd1_op_mode_1r ;
    reg                         ffpadd1_vld_1r     ;
    reg  [4:0]                  norm2_op_mode      ;
    reg                         norm2_vld          ;       
    reg  [4:0]                  ffpadd2_op_mode    ;
    reg                         ffpadd2_vld        ;
    reg  [4:0]                  ffpadd2_op_mode_1r ;
    reg                         ffpadd2_vld_1r     ;
    reg  [4:0]                  ffp2fp_op_mode_r   ;
    reg                         ffp2fp_vld_r       ;
    reg  [4:0]                  ffp2fp_op_mode_1r  ;
    reg                         ffp2fp_vld_1r      ;
    
    reg  [9:0]                  e_align_abscale0   ;    
    reg  [9:0]                  e_align_abscale1   ;    
    reg  [9:0]                  e_align_abscale2   ;    
    reg  [9:0]                  e_align_abscale3   ;    
    reg  [35:0]                 addtree_abscale    ;    
 
    wire [18 : 0]               mul_a       [0:31] ;//c0-c15
    wire [18 : 0]               mul_b       [0:31] ;
    wire [32*6-1  : 0]          mul_z0_e           ;
    wire [32*9-1  : 0]          mul_z1_e           ;
    wire [32*32-1 : 0]          mul_z_m            ;
    reg  [32*32-1 : 0]          mul_z_m_r          ;
    wire [8:0]                  u0addtree_e_max       ;
    wire [16*6-1 : 0]           u0addtree_ae_sub      ;
    wire [16*6-1 : 0]           u0addtree_be_sub      ;
    wire [15:0]                 u0addtree_ae_overflow ;
    wire [15:0]                 u0addtree_be_overflow ;
    wire [45:0]                 u0addtree_z0          ;
    wire [28:0]                 u0addtree_z1          ;

    wire [8:0]                  u1addtree_e_max       ;
    wire [16*6-1 : 0]           u1addtree_ae_sub      ;
    wire [16*6-1 : 0]           u1addtree_be_sub      ;
    wire [15:0]                 u1addtree_ae_overflow ;
    wire [15:0]                 u1addtree_be_overflow ;
    wire [45:0]                 u1addtree_z2          ;
    wire [28:0]                 u1addtree_z3          ;    

    wire [46:0]                 norm1_z0    ;
    wire [29:0]                 norm1_z1    ;
    wire [46:0]                 norm1_z2    ;
    wire [29:0]                 norm1_z3    ;   
    reg  [46:0]                 norm1_z0_r  ;
    reg  [29:0]                 norm1_z1_r  ;
    reg  [46:0]                 norm1_z2_r  ;
    reg  [29:0]                 norm1_z3_r  ;   

    wire [47:0]                 ffpadd1_z0  ;
    wire [40:0]                 ffpadd1_z1  ;
    reg  [46:0]                 ffpadd1_z0_r;
    reg  [39:0]                 ffpadd1_z1_r;

    reg  [46:0]                 ffpadd1_z0_r1;
    reg  [46:0]                 ffpadd1_z0_r2;
    reg  [46:0]                 ffpadd1_z0_r3;

    wire [40:0]                 norm2_z13   ;
    wire [40:0]                 norm2_z24   ;
    reg  [40:0]                 norm2_z13_r ;
    reg  [40:0]                 norm2_z24_r ;

    wire [41:0]                 ffpadd2_z   ;
    wire [31:0]                 ffp2fp_z    ;

    genvar i;

    //=================================================================================================================
    //mul
    //=================================================================================================================
    assign mul_op_mode = mode[4:0]; //{~(int_mode | fp8_mode), fp8_mode, int_mode};
    // generate for(i = 0; i < 32; i = i+1)begin :GEN_MULT 
    //     assign mul_a[i] = fp_a[(i+1)*19-1:i*19] ;
    //     assign mul_b[i] = fp_b[(i+1)*19-1:i*19] ;
    //     ne_fp_ffp_mul u_mul(
    //         .clk                (clk                 ) ,

    //         .op_mode            (mul_op_mode[3:0]    ) ,
    //         .i_gp_zero_skip_en  (i_gp_zero_skip_en   ) ,
    //         .a                  (mul_a[i]            ) ,
    //         .b                  (mul_b[i]            ) ,
    //         .z0_e               (mul_z0_e[(i+1)*6-1:i*6]    ) ,
    //         .z1_e               (mul_z1_e[(i+1)*9-1:i*9]    ) ,
    //         .z_m                (mul_z_m[(i+1)*32-1:i*32]   )
    //     );
    //     always@(posedge clk) 
    //     begin
    //         mul_z_m_r[(i+1)*32-1:i*32]  <= mul_z_m[(i+1)*32-1:i*32] ;
    //     end 
        
    // end
    // endgenerate
    // 实例0
    assign mul_a[0] = fp_a[18:0];
    assign mul_b[0] = fp_b[18:0];
    ne_fp_ffp_mul u_mul_0(
        .clk                (clk                ),
        .op_mode            (mul_op_mode[3:0]   ),
        .i_gp_zero_skip_en  (i_gp_zero_skip_en  ),
        .a                  (mul_a[0]           ),
        .b                  (mul_b[0]           ),
        .z0_e               (mul_z0_e[5:0]      ),
        .z1_e               (mul_z1_e[8:0]      ),
        .z_m                (mul_z_m[31:0]      )
    );
    always@(posedge clk) begin
        mul_z_m_r[31:0] <= mul_z_m[31:0];
    end

    // 实例1
    assign mul_a[1] = fp_a[37:19];
    assign mul_b[1] = fp_b[37:19];
    ne_fp_ffp_mul u_mul_1(
        .clk                (clk                ),
        .op_mode            (mul_op_mode[3:0]   ),
        .i_gp_zero_skip_en  (i_gp_zero_skip_en  ),
        .a                  (mul_a[1]           ),
        .b                  (mul_b[1]           ),
        .z0_e               (mul_z0_e[11:6]     ),
        .z1_e               (mul_z1_e[17:9]     ),
        .z_m                (mul_z_m[63:32]     )
    );
    always@(posedge clk) begin
        mul_z_m_r[63:32] <= mul_z_m[63:32];
    end

    // 实例2
    assign mul_a[2] = fp_a[56:38];
    assign mul_b[2] = fp_b[56:38];
    ne_fp_ffp_mul u_mul_2(
        .clk                (clk                ),
        .op_mode            (mul_op_mode[3:0]   ),
        .i_gp_zero_skip_en  (i_gp_zero_skip_en  ),
        .a                  (mul_a[2]           ),
        .b                  (mul_b[2]           ),
        .z0_e               (mul_z0_e[17:12]    ),
        .z1_e               (mul_z1_e[26:18]    ),
        .z_m                (mul_z_m[95:64]     )
    );
    always@(posedge clk) begin
        mul_z_m_r[95:64] <= mul_z_m[95:64];
    end

    // 实例3
    assign mul_a[3] = fp_a[75:57];
    assign mul_b[3] = fp_b[75:57];
    ne_fp_ffp_mul u_mul_3(
        .clk                (clk                ),
        .op_mode            (mul_op_mode[3:0]   ),
        .i_gp_zero_skip_en  (i_gp_zero_skip_en  ),
        .a                  (mul_a[3]           ),
        .b                  (mul_b[3]           ),
        .z0_e               (mul_z0_e[23:18]    ),
        .z1_e               (mul_z1_e[35:27]    ),
        .z_m                (mul_z_m[127:96]    )
    );
    always@(posedge clk) begin
        mul_z_m_r[127:96] <= mul_z_m[127:96];
    end

    // 实例4
    assign mul_a[4] = fp_a[94:76];
    assign mul_b[4] = fp_b[94:76];
    ne_fp_ffp_mul u_mul_4(
        .clk                (clk                ),
        .op_mode            (mul_op_mode[3:0]   ),
        .i_gp_zero_skip_en  (i_gp_zero_skip_en  ),
        .a                  (mul_a[4]           ),
        .b                  (mul_b[4]           ),
        .z0_e               (mul_z0_e[29:24]    ),
        .z1_e               (mul_z1_e[44:36]    ),
        .z_m                (mul_z_m[159:128]   )
    );
    always@(posedge clk) begin
        mul_z_m_r[159:128] <= mul_z_m[159:128];
    end

    // 实例5
    assign mul_a[5] = fp_a[113:95];
    assign mul_b[5] = fp_b[113:95];
    ne_fp_ffp_mul u_mul_5(
        .clk                (clk                ),
        .op_mode            (mul_op_mode[3:0]   ),
        .i_gp_zero_skip_en  (i_gp_zero_skip_en  ),
        .a                  (mul_a[5]           ),
        .b                  (mul_b[5]           ),
        .z0_e               (mul_z0_e[35:30]    ),
        .z1_e               (mul_z1_e[53:45]    ),
        .z_m                (mul_z_m[191:160]   )
    );
    always@(posedge clk) begin
        mul_z_m_r[191:160] <= mul_z_m[191:160];
    end

    // 实例6
    assign mul_a[6] = fp_a[132:114];
    assign mul_b[6] = fp_b[132:114];
    ne_fp_ffp_mul u_mul_6(
        .clk                (clk                ),
        .op_mode            (mul_op_mode[3:0]   ),
        .i_gp_zero_skip_en  (i_gp_zero_skip_en  ),
        .a                  (mul_a[6]           ),
        .b                  (mul_b[6]           ),
        .z0_e               (mul_z0_e[41:36]    ),
        .z1_e               (mul_z1_e[62:54]    ),
        .z_m                (mul_z_m[223:192]   )
    );
    always@(posedge clk) begin
        mul_z_m_r[223:192] <= mul_z_m[223:192];
    end

    // 实例7
    assign mul_a[7] = fp_a[151:133];
    assign mul_b[7] = fp_b[151:133];
    ne_fp_ffp_mul u_mul_7(
        .clk                (clk                ),
        .op_mode            (mul_op_mode[3:0]   ),
        .i_gp_zero_skip_en  (i_gp_zero_skip_en  ),
        .a                  (mul_a[7]           ),
        .b                  (mul_b[7]           ),
        .z0_e               (mul_z0_e[47:42]    ),
        .z1_e               (mul_z1_e[71:63]    ),
        .z_m                (mul_z_m[255:224]   )
    );
    always@(posedge clk) begin
        mul_z_m_r[255:224] <= mul_z_m[255:224];
    end

    // 实例8
    assign mul_a[8] = fp_a[170:152];
    assign mul_b[8] = fp_b[170:152];
    ne_fp_ffp_mul u_mul_8(
        .clk                (clk                ),
        .op_mode            (mul_op_mode[3:0]   ),
        .i_gp_zero_skip_en  (i_gp_zero_skip_en  ),
        .a                  (mul_a[8]           ),
        .b                  (mul_b[8]           ),
        .z0_e               (mul_z0_e[53:48]    ),
        .z1_e               (mul_z1_e[80:72]    ),
        .z_m                (mul_z_m[287:256]   )
    );
    always@(posedge clk) begin
        mul_z_m_r[287:256] <= mul_z_m[287:256];
    end

    // 实例9
    assign mul_a[9] = fp_a[189:171];
    assign mul_b[9] = fp_b[189:171];
    ne_fp_ffp_mul u_mul_9(
        .clk                (clk                ),
        .op_mode            (mul_op_mode[3:0]   ),
        .i_gp_zero_skip_en  (i_gp_zero_skip_en  ),
        .a                  (mul_a[9]           ),
        .b                  (mul_b[9]           ),
        .z0_e               (mul_z0_e[59:54]    ),
        .z1_e               (mul_z1_e[89:81]    ),
        .z_m                (mul_z_m[319:288]   )
    );
    always@(posedge clk) begin
        mul_z_m_r[319:288] <= mul_z_m[319:288];
    end

    // 实例10
    assign mul_a[10] = fp_a[208:190];
    assign mul_b[10] = fp_b[208:190];
    ne_fp_ffp_mul u_mul_10(
        .clk                (clk                ),
        .op_mode            (mul_op_mode[3:0]   ),
        .i_gp_zero_skip_en  (i_gp_zero_skip_en  ),
        .a                  (mul_a[10]          ),
        .b                  (mul_b[10]          ),
        .z0_e               (mul_z0_e[65:60]    ),
        .z1_e               (mul_z1_e[98:90]    ),
        .z_m                (mul_z_m[351:320]   )
    );
    always@(posedge clk) begin
        mul_z_m_r[351:320] <= mul_z_m[351:320];
    end

    // 实例11
    assign mul_a[11] = fp_a[227:209];
    assign mul_b[11] = fp_b[227:209];
    ne_fp_ffp_mul u_mul_11(
        .clk                (clk                ),
        .op_mode            (mul_op_mode[3:0]   ),
        .i_gp_zero_skip_en  (i_gp_zero_skip_en  ),
        .a                  (mul_a[11]          ),
        .b                  (mul_b[11]          ),
        .z0_e               (mul_z0_e[71:66]    ),
        .z1_e               (mul_z1_e[107:99]   ),
        .z_m                (mul_z_m[383:352]   )
    );
    always@(posedge clk) begin
        mul_z_m_r[383:352] <= mul_z_m[383:352];
    end

    // 实例12
    assign mul_a[12] = fp_a[246:228];
    assign mul_b[12] = fp_b[246:228];
    ne_fp_ffp_mul u_mul_12(
        .clk                (clk                ),
        .op_mode            (mul_op_mode[3:0]   ),
        .i_gp_zero_skip_en  (i_gp_zero_skip_en  ),
        .a                  (mul_a[12]          ),
        .b                  (mul_b[12]          ),
        .z0_e               (mul_z0_e[77:72]    ),
        .z1_e               (mul_z1_e[116:108]  ),
        .z_m                (mul_z_m[415:384]   )
    );
    always@(posedge clk) begin
        mul_z_m_r[415:384] <= mul_z_m[415:384];
    end

    // 实例13
    assign mul_a[13] = fp_a[265:247];
    assign mul_b[13] = fp_b[265:247];
    ne_fp_ffp_mul u_mul_13(
        .clk                (clk                ),
        .op_mode            (mul_op_mode[3:0]   ),
        .i_gp_zero_skip_en  (i_gp_zero_skip_en  ),
        .a                  (mul_a[13]          ),
        .b                  (mul_b[13]          ),
        .z0_e               (mul_z0_e[83:78]    ),
        .z1_e               (mul_z1_e[125:117]  ),
        .z_m                (mul_z_m[447:416]   )
    );
    always@(posedge clk) begin
        mul_z_m_r[447:416] <= mul_z_m[447:416];
    end

    // 实例14
    assign mul_a[14] = fp_a[284:266];
    assign mul_b[14] = fp_b[284:266];
    ne_fp_ffp_mul u_mul_14(
        .clk                (clk                ),
        .op_mode            (mul_op_mode[3:0]   ),
        .i_gp_zero_skip_en  (i_gp_zero_skip_en  ),
        .a                  (mul_a[14]          ),
        .b                  (mul_b[14]          ),
        .z0_e               (mul_z0_e[89:84]    ),
        .z1_e               (mul_z1_e[134:126]  ),
        .z_m                (mul_z_m[479:448]   )
    );
    always@(posedge clk) begin
        mul_z_m_r[479:448] <= mul_z_m[479:448];
    end

    // 实例15
    assign mul_a[15] = fp_a[303:285];
    assign mul_b[15] = fp_b[303:285];
    ne_fp_ffp_mul u_mul_15(
        .clk                (clk                ),
        .op_mode            (mul_op_mode[3:0]   ),
        .i_gp_zero_skip_en  (i_gp_zero_skip_en  ),
        .a                  (mul_a[15]          ),
        .b                  (mul_b[15]          ),
        .z0_e               (mul_z0_e[95:90]    ),
        .z1_e               (mul_z1_e[143:135]  ),
        .z_m                (mul_z_m[511:480]   )
    );
    always@(posedge clk) begin
        mul_z_m_r[511:480] <= mul_z_m[511:480];
    end

    // 实例16
    assign mul_a[16] = fp_a[322:304];
    assign mul_b[16] = fp_b[322:304];
    ne_fp_ffp_mul u_mul_16(
        .clk                (clk                ),
        .op_mode            (mul_op_mode[3:0]   ),
        .i_gp_zero_skip_en  (i_gp_zero_skip_en  ),
        .a                  (mul_a[16]          ),
        .b                  (mul_b[16]          ),
        .z0_e               (mul_z0_e[101:96]   ),
        .z1_e               (mul_z1_e[152:144]  ),
        .z_m                (mul_z_m[543:512]   )
    );
    always@(posedge clk) begin
        mul_z_m_r[543:512] <= mul_z_m[543:512];
    end

    // 实例17
    assign mul_a[17] = fp_a[341:323];
    assign mul_b[17] = fp_b[341:323];
    ne_fp_ffp_mul u_mul_17(
        .clk                (clk                ),
        .op_mode            (mul_op_mode[3:0]   ),
        .i_gp_zero_skip_en  (i_gp_zero_skip_en  ),
        .a                  (mul_a[17]          ),
        .b                  (mul_b[17]          ),
        .z0_e               (mul_z0_e[107:102]  ),
        .z1_e               (mul_z1_e[161:153]  ),
        .z_m                (mul_z_m[575:544]   )
    );
    always@(posedge clk) begin
        mul_z_m_r[575:544] <= mul_z_m[575:544];
    end

    // 实例18
    assign mul_a[18] = fp_a[360:342];
    assign mul_b[18] = fp_b[360:342];
    ne_fp_ffp_mul u_mul_18(
        .clk                (clk                ),
        .op_mode            (mul_op_mode[3:0]   ),
        .i_gp_zero_skip_en  (i_gp_zero_skip_en  ),
        .a                  (mul_a[18]          ),
        .b                  (mul_b[18]          ),
        .z0_e               (mul_z0_e[113:108]  ),
        .z1_e               (mul_z1_e[170:162]  ),
        .z_m                (mul_z_m[607:576]   )
    );
    always@(posedge clk) begin
        mul_z_m_r[607:576] <= mul_z_m[607:576];
    end

    // 实例19
    assign mul_a[19] = fp_a[379:361];
    assign mul_b[19] = fp_b[379:361];
    ne_fp_ffp_mul u_mul_19(
        .clk                (clk                ),
        .op_mode            (mul_op_mode[3:0]   ),
        .i_gp_zero_skip_en  (i_gp_zero_skip_en  ),
        .a                  (mul_a[19]          ),
        .b                  (mul_b[19]          ),
        .z0_e               (mul_z0_e[119:114]  ),
        .z1_e               (mul_z1_e[179:171]  ),
        .z_m                (mul_z_m[639:608]   )
    );
    always@(posedge clk) begin
        mul_z_m_r[639:608] <= mul_z_m[639:608];
    end

    // 实例20
    assign mul_a[20] = fp_a[398:380];
    assign mul_b[20] = fp_b[398:380];
    ne_fp_ffp_mul u_mul_20(
        .clk                (clk                ),
        .op_mode            (mul_op_mode[3:0]   ),
        .i_gp_zero_skip_en  (i_gp_zero_skip_en  ),
        .a                  (mul_a[20]          ),
        .b                  (mul_b[20]          ),
        .z0_e               (mul_z0_e[125:120]  ),
        .z1_e               (mul_z1_e[188:180]  ),
        .z_m                (mul_z_m[671:640]   )
    );
    always@(posedge clk) begin
        mul_z_m_r[671:640] <= mul_z_m[671:640];
    end

    // 实例21
    assign mul_a[21] = fp_a[417:399];
    assign mul_b[21] = fp_b[417:399];
    ne_fp_ffp_mul u_mul_21(
        .clk                (clk                ),
        .op_mode            (mul_op_mode[3:0]   ),
        .i_gp_zero_skip_en  (i_gp_zero_skip_en  ),
        .a                  (mul_a[21]          ),
        .b                  (mul_b[21]          ),
        .z0_e               (mul_z0_e[131:126]  ),
        .z1_e               (mul_z1_e[197:189]  ),
        .z_m                (mul_z_m[703:672]   )
    );
    always@(posedge clk) begin
        mul_z_m_r[703:672] <= mul_z_m[703:672];
    end

    // 实例22
    assign mul_a[22] = fp_a[436:418];
    assign mul_b[22] = fp_b[436:418];
    ne_fp_ffp_mul u_mul_22(
        .clk                (clk                ),
        .op_mode            (mul_op_mode[3:0]   ),
        .i_gp_zero_skip_en  (i_gp_zero_skip_en  ),
        .a                  (mul_a[22]          ),
        .b                  (mul_b[22]          ),
        .z0_e               (mul_z0_e[137:132]  ),
        .z1_e               (mul_z1_e[206:198]  ),
        .z_m                (mul_z_m[735:704]   )
    );
    always@(posedge clk) begin
        mul_z_m_r[735:704] <= mul_z_m[735:704];
    end

    // 实例23
    assign mul_a[23] = fp_a[455:437];
    assign mul_b[23] = fp_b[455:437];
    ne_fp_ffp_mul u_mul_23(
        .clk                (clk                ),
        .op_mode            (mul_op_mode[3:0]   ),
        .i_gp_zero_skip_en  (i_gp_zero_skip_en  ),
        .a                  (mul_a[23]          ),
        .b                  (mul_b[23]          ),
        .z0_e               (mul_z0_e[143:138]  ),
        .z1_e               (mul_z1_e[215:207]  ),
        .z_m                (mul_z_m[767:736]   )
    );
    always@(posedge clk) begin
        mul_z_m_r[767:736] <= mul_z_m[767:736];
    end

    // 实例24
    assign mul_a[24] = fp_a[474:456];
    assign mul_b[24] = fp_b[474:456];
    ne_fp_ffp_mul u_mul_24(
        .clk                (clk                ),
        .op_mode            (mul_op_mode[3:0]   ),
        .i_gp_zero_skip_en  (i_gp_zero_skip_en  ),
        .a                  (mul_a[24]          ),
        .b                  (mul_b[24]          ),
        .z0_e               (mul_z0_e[149:144]  ),
        .z1_e               (mul_z1_e[224:216]  ),
        .z_m                (mul_z_m[799:768]   )
    );
    always@(posedge clk) begin
        mul_z_m_r[799:768] <= mul_z_m[799:768];
    end

    // 实例25
    assign mul_a[25] = fp_a[493:475];
    assign mul_b[25] = fp_b[493:475];
    ne_fp_ffp_mul u_mul_25(
        .clk                (clk                ),
        .op_mode            (mul_op_mode[3:0]   ),
        .i_gp_zero_skip_en  (i_gp_zero_skip_en  ),
        .a                  (mul_a[25]          ),
        .b                  (mul_b[25]          ),
        .z0_e               (mul_z0_e[155:150]  ),
        .z1_e               (mul_z1_e[233:225]  ),
        .z_m                (mul_z_m[831:800]   )
    );
    always@(posedge clk) begin
        mul_z_m_r[831:800] <= mul_z_m[831:800];
    end

    // 实例26
    assign mul_a[26] = fp_a[512:494];
    assign mul_b[26] = fp_b[512:494];
    ne_fp_ffp_mul u_mul_26(
        .clk                (clk                ),
        .op_mode            (mul_op_mode[3:0]   ),
        .i_gp_zero_skip_en  (i_gp_zero_skip_en  ),
        .a                  (mul_a[26]          ),
        .b                  (mul_b[26]          ),
        .z0_e               (mul_z0_e[161:156]  ),
        .z1_e               (mul_z1_e[242:234]  ),
        .z_m                (mul_z_m[863:832]   )
    );
    always@(posedge clk) begin
        mul_z_m_r[863:832] <= mul_z_m[863:832];
    end

    // 实例27
    assign mul_a[27] = fp_a[531:513];
    assign mul_b[27] = fp_b[531:513];
    ne_fp_ffp_mul u_mul_27(
        .clk                (clk                ),
        .op_mode            (mul_op_mode[3:0]   ),
        .i_gp_zero_skip_en  (i_gp_zero_skip_en  ),
        .a                  (mul_a[27]          ),
        .b                  (mul_b[27]          ),
        .z0_e               (mul_z0_e[167:162]  ),
        .z1_e               (mul_z1_e[251:243]  ),
        .z_m                (mul_z_m[895:864]   )
    );
    always@(posedge clk) begin
        mul_z_m_r[895:864] <= mul_z_m[895:864];
    end

    // 实例28
    assign mul_a[28] = fp_a[550:532];
    assign mul_b[28] = fp_b[550:532];
    ne_fp_ffp_mul u_mul_28(
        .clk                (clk                ),
        .op_mode            (mul_op_mode[3:0]   ),
        .i_gp_zero_skip_en  (i_gp_zero_skip_en  ),
        .a                  (mul_a[28]          ),
        .b                  (mul_b[28]          ),
        .z0_e               (mul_z0_e[173:168]  ),
        .z1_e               (mul_z1_e[260:252]  ),
        .z_m                (mul_z_m[927:896]   )
    );
    always@(posedge clk) begin
        mul_z_m_r[927:896] <= mul_z_m[927:896];
    end

    // 实例29
    assign mul_a[29] = fp_a[569:551];
    assign mul_b[29] = fp_b[569:551];
    ne_fp_ffp_mul u_mul_29(
        .clk                (clk                ),
        .op_mode            (mul_op_mode[3:0]   ),
        .i_gp_zero_skip_en  (i_gp_zero_skip_en  ),
        .a                  (mul_a[29]          ),
        .b                  (mul_b[29]          ),
        .z0_e               (mul_z0_e[179:174]  ),
        .z1_e               (mul_z1_e[269:261]  ),
        .z_m                (mul_z_m[959:928]   )
    );
    always@(posedge clk) begin
        mul_z_m_r[959:928] <= mul_z_m[959:928];
    end

    // 实例30
    assign mul_a[30] = fp_a[588:570];
    assign mul_b[30] = fp_b[588:570];
    ne_fp_ffp_mul u_mul_30(
        .clk                (clk                ),
        .op_mode            (mul_op_mode[3:0]   ),
        .i_gp_zero_skip_en  (i_gp_zero_skip_en  ),
        .a                  (mul_a[30]          ),
        .b                  (mul_b[30]          ),
        .z0_e               (mul_z0_e[185:180]  ),
        .z1_e               (mul_z1_e[278:270]  ),
        .z_m                (mul_z_m[991:960]   )
    );
    always@(posedge clk) begin
        mul_z_m_r[991:960] <= mul_z_m[991:960];
    end

    // 实例31
    assign mul_a[31] = fp_a[607:589];
    assign mul_b[31] = fp_b[607:589];
    ne_fp_ffp_mul u_mul_31(
        .clk                (clk                ),
        .op_mode            (mul_op_mode[3:0]   ),
        .i_gp_zero_skip_en  (i_gp_zero_skip_en  ),
        .a                  (mul_a[31]          ),
        .b                  (mul_b[31]          ),
        .z0_e               (mul_z0_e[191:186]  ),
        .z1_e               (mul_z1_e[287:279]  ),
        .z_m                (mul_z_m[1023:992]  )
    );
    always@(posedge clk) begin
        mul_z_m_r[1023:992] <= mul_z_m[1023:992];
    end



    //=================================================================================================================
    //adder prepare 2 clk
    //=================================================================================================================
    assign e_align_op_mode  = mul_op_mode;
    assign e_align_vld      = fp_vld     ;

    ne_fp_ffp_e_align u0_e_align(
        .clk                (clk) ,

        .op_mode            (e_align_op_mode[3:0]   ),
        .a_e                (mul_z1_e[16*9-1:0]     ),
        .b_e                (mul_z0_e[16*6-1:0]     ),
        .e_max              (u0addtree_e_max        ),
        .a_e_sub            (u0addtree_ae_sub       ),
        .b_e_sub            (u0addtree_be_sub       ),
        .a_e_overflow       (u0addtree_ae_overflow  ),
        .b_e_overflow       (u0addtree_be_overflow  )
     );
    ne_fp_ffp_e_align u16_e_align(
        .clk                (clk) ,
        
        .op_mode            (e_align_op_mode[3:0]   ),
        .a_e                (mul_z1_e[32*9-1:16*9]  ),
        .b_e                (mul_z0_e[32*6-1:16*6]  ),
        .e_max              (u1addtree_e_max        ),
        .a_e_sub            (u1addtree_ae_sub       ),
        .b_e_sub            (u1addtree_be_sub       ),
        .a_e_overflow       (u1addtree_ae_overflow  ),
        .b_e_overflow       (u1addtree_be_overflow  )
     );
    
    always@(posedge clk) begin
        e_align_abscale0   <= $signed({a_scale[ 7],a_scale[ 7: 0]})+$signed({b_scale[ 7],b_scale[ 7: 0]}); //fp8_fp4
        e_align_abscale1   <= $signed({a_scale[15],a_scale[15: 8]})+$signed({b_scale[15],b_scale[15: 8]});
        e_align_abscale2   <= $signed({a_scale[23],a_scale[23:16]})+$signed({b_scale[23],b_scale[23:16]});
        e_align_abscale3   <= $signed({a_scale[31],a_scale[31:24]})+$signed({b_scale[31],b_scale[31:24]});
        addtree_abscale    <= {e_align_abscale3[8:0],e_align_abscale2[8:0],e_align_abscale1[8:0],e_align_abscale0[8:0]}; 
    end    
    always@(posedge clk) begin
        e_align_op_mode_1r <= e_align_op_mode; //int8_fp8_fp16_fp4
        e_align_vld_1r     <= e_align_vld    ;
      
        addtree_op_mode    <= e_align_op_mode_1r;
        addtree_vld        <= e_align_vld_1r    ;
    end 
    //=================================================================================================================
    //adder vector 2clk
    //=================================================================================================================

    ne_fp_ffp_add_vector_m33 u0_addtree(
        .clk                (clk                    ) ,

        .op_mode            (addtree_op_mode[3:0]   ),
        .e_max              (u0addtree_e_max        ),
        .ab_scale           (addtree_abscale[17:0]  ),
        .ae_sub             (u0addtree_ae_sub       ),
        .be_sub             (u0addtree_be_sub       ),
        .a_e_overflow       (u0addtree_ae_overflow  ),
        .b_e_overflow       (u0addtree_be_overflow  ),
        .a_m                (mul_z_m_r[16*32-1:0]   ),
        .z                  (u0addtree_z0           ),
        .z_fp4              (u0addtree_z1           )
    );
    ne_fp_ffp_add_vector_m33 u1_addtree(
        .clk                (clk   ) ,
        .op_mode            (addtree_op_mode[3:0]       ),
        .e_max              (u1addtree_e_max            ),
        .ab_scale           (addtree_abscale[35:18]     ),
        .ae_sub             (u1addtree_ae_sub           ),
        .be_sub             (u1addtree_be_sub           ),
        .a_e_overflow       (u1addtree_ae_overflow      ),
        .b_e_overflow       (u1addtree_be_overflow      ),
        .a_m                (mul_z_m_r[32*32-1:16*32]   ), // m is two's complement
        .z                  (u1addtree_z2               ), //zero/inf/nan/e10/s1+s1+m31
        .z_fp4              (u1addtree_z3               )  //zero/inf/nan/e10/s1+s1+m14
    );
    
    always@(posedge clk) //int8_fp8_fp16_fp4
    begin
        addtree_op_mode_1r<= addtree_op_mode;
        addtree_vld_1r    <= addtree_vld    ;
        norm1_op_mode     <= addtree_op_mode_1r;
        norm1_vld         <= addtree_vld_1r    ;
    end 
    //=================================================================================================================
    //ffp add: norm 1clk + ffpadd 2clk 
    //=================================================================================================================
   
    // #(
    // .SW        (1 ),
    // .EW        (10 ),//s2+e8
    // .MW        (33), //s1+m32
    // .BW_STATUS (3 )
    // )
    ne_fp_ffp_norm_mw33 u0_ffp_norm1(
        // .clk (clk),
        .a   ({u0addtree_z0[43],u0addtree_z0[44],u0addtree_z0[45],u0addtree_z0[32],u0addtree_z0[42:33],u0addtree_z0[32:0]}), //nan/inf/zero/s1/e10/s1+s1+m31
        .z   (norm1_z0),                        //nan/inf/zero/s1/e10/s1+s1+m31
        .mode(norm1_op_mode[2:0])                //3'b100: tf32, 3'b010: fp8, 3'b001: int8
    );

    //  #(
    // .SW        (1 ),
    // .EW        (10 ),//s2+e8
    // .MW        (16), //s1+m15
    // .BW_STATUS (3 )
    // )
   ne_fp_ffp_norm_mw16 u1_ffp_norm1(
        // .clk (clk),
        .a   ({u0addtree_z1[26],u0addtree_z1[27],u0addtree_z1[28],u0addtree_z1[15],u0addtree_z1[25:16],u0addtree_z1[15:0]}), //nan/inf/zero/s1/e10/s1+s1+m14
        .z   (norm1_z1),                        //nan/inf/zero/s1/e10/s1+s1+m14
        .mode(norm1_op_mode[2:0])                //3'b100: tf32, 3'b010: fp8, 3'b001: int8
    );

    // #(
    // .SW        (1 ),
    // .EW        (10),
    // .MW        (33),
    // .BW_STATUS (3 )
    // )
    ne_fp_ffp_norm_mw33 u2_ffp_norm1(
        // .clk (clk),
        .a   ({u1addtree_z2[43],u1addtree_z2[44],u1addtree_z2[45],u1addtree_z2[32],u1addtree_z2[42:33],u1addtree_z2[32:0]}),
        .z   (norm1_z2),
        .mode(norm1_op_mode[2:0])                //3'b100: tf32, 3'b010: fp8, 3'b001: int8
    );
    // #(
    // .SW        (1 ),
    // .EW        (10),
    // .MW        (16),
    // .BW_STATUS (3 )
    // )
    ne_fp_ffp_norm_mw16 u3_ffp_norm1(
        // .clk (clk),
        .a   ({u1addtree_z3[26],u1addtree_z3[27],u1addtree_z3[28],u1addtree_z3[15],u1addtree_z3[25:16],u1addtree_z3[15:0]}),
        .z   (norm1_z3),
        .mode(norm1_op_mode[2:0])                //3'b100: tf32, 3'b010: fp8, 3'b001: int8
    );

    always@(posedge clk) begin
        norm1_z0_r <= norm1_z0 ;//int8_fp8_fp16_fp4
        norm1_z2_r <= norm1_z2 ;//int8_fp8_fp16_fp4
    end 
    always@(posedge clk) begin
        norm1_z1_r <= norm1_z1 ;//fp4
        norm1_z3_r <= norm1_z3 ;//fp4
    end 
    always@(posedge clk) //int8_fp8_fp16_fp4
    begin
        ffpadd1_op_mode <= norm1_op_mode;        
        ffpadd1_vld     <= norm1_vld    ;
    end 
    //-------fp_ffp_add---pipe=1---------
    
    ne_fp_ffp_add_mix #(
    .SWI       (1 ),
    .EWI       (10 ), //s2+e8 
    .MWI       (33), //s1+m32
    .HAVE_INT  (1 ), //have int type
    .INT_CH    (1 ), //a or b have int type ch num
    .BW_INT_I  (21), //int bitwidth  //int8*int8 *c32 = 21bit
    .BW_STATUS (3 ),
    .PIPE      (1 )
    )u0_ffpadd1(
    .clk (clk),
    .a   (norm1_z0_r),    //3status + s1e10+s1s1m31
    .b   (norm1_z2_r),
    .z   (ffpadd1_z0),   //3status + s1e10m34; //nan/inf/zero/s1/e10/s1+s1+m32
    .mode(ffpadd1_op_mode[3:0])                //4'b1000:fp4; 4'b0100: tf32, 3'b0010: fp8, 3'b001: int8
    );
        // ne_fp_ffp_add    : fp4 c0/c64
        // ne_fp_ffp_add_fp4: fp4 c32/c96
    // #(
    // .SWI       (1 ),
    // .EWI       (10), //s2+e8 
    // .MWI       (16+10), //s1+m15+10'd0
    // .HAVE_INT  (0 ), //have int type
    // .INT_CH    (1 ), //a or b have int type ch num
    // .BW_INT_I  (21), //int bitwidth  //int8*int8 *c32 = 21bit
    // .BW_STATUS (3 ),
    // .PIPE      (1 )
    // )
    ne_fp_ffp_add_mwi26 u1_ffpadd1(
    .clk (clk ),
    .a   ({norm1_z1_r,10'd0}),    //3status + s1e10+s1s1m14+10'd0
    .b   ({norm1_z3_r,10'd0}),
    .z   (ffpadd1_z1),   //3status + s1e10m17+10bit; //nan/inf/zero/s1/e10/s1+s1+m15+10bit
    .mode(ffpadd1_op_mode[2:0])                //3'b100: tf32, 3'b010: fp8, 3'b001: int8
    );
    always@(posedge clk) begin
        ffpadd1_z0_r   <= {ffpadd1_z0[47:45],ffpadd1_z0[43:34],ffpadd1_z0[33:0]};//int8_fp8_fp16_fp4 
    end 
    always@(posedge clk) begin
        ffpadd1_z1_r   <= {ffpadd1_z1[40:38],ffpadd1_z1[36:27],ffpadd1_z1[26:0]};//fp4
    end 

    always@(posedge clk) //int8_fp8_fp16_fp4
    begin
      ffpadd1_op_mode_1r   <= ffpadd1_op_mode;    //fp_ffp_add: pipe 1  
      ffpadd1_vld_1r       <= ffpadd1_vld    ; 
      norm2_op_mode        <= ffpadd1_op_mode_1r; //fp_ffp_add: z reg 
      norm2_vld            <= ffpadd1_vld_1r    ; 
    end 
    //====fp4 sum===norm 1clk,ffp_add 2 clk=========
    //     .SW        (1 ),
    // .EW        (10),
    // .MW        (17+10), //s1+m16+10bit
    // .BW_STATUS (3 )
    // )

    wire [2:0] debug_mode=norm2_op_mode[2:0];
    wire [40:0] debug_wire={ffpadd1_z0_r[46],ffpadd1_z0_r[45],ffpadd1_z0_r[44],ffpadd1_z0_r[33],ffpadd1_z0_r[43:34],ffpadd1_z0_r[33:7]};
     ne_fp_ffp_norm_mw27 u0_ffp_norm2(
        // .clk (clk),
        .a   ({ffpadd1_z0_r[46],ffpadd1_z0_r[45],ffpadd1_z0_r[44],ffpadd1_z0_r[33],ffpadd1_z0_r[43:34],ffpadd1_z0_r[33:7]}),
        .z   (norm2_z13),  //nan/inf/zero/s1/e10/s1+s1+m15+10bit
        .mode(norm2_op_mode[2:0])                //3'b100: tf32, 3'b010: fp8, 3'b001: int8
    );

    //  #(
    // .SW        (1 ),
    // .EW        (10),
    // .MW        (17+10), //s1+m16+10bit
    // .BW_STATUS (3 )
    // )
    ne_fp_ffp_norm_mw27 u1_ffp_norm2(
        // .clk (clk),
        .a   ({ffpadd1_z1_r[39],ffpadd1_z1_r[38],ffpadd1_z1_r[37],ffpadd1_z1_r[26],ffpadd1_z1_r[36:27],ffpadd1_z1_r[26:0]}),
        .z   (norm2_z24),
        .mode(norm2_op_mode[2:0])                //3'b100: tf32, 3'b010: fp8, 3'b001: int8
    ); 
    always@(posedge clk) begin
        norm2_z13_r <= norm2_z13;//fp4
        norm2_z24_r <= norm2_z24;//fp4
    end 
    always@(posedge clk) begin
        ffpadd2_op_mode <= norm2_op_mode; //int8_fp8_fp16_fp4
        ffpadd2_vld     <= norm2_vld ;
    end 
    always@(posedge clk) begin
        ffpadd1_z0_r1   <= ffpadd1_z0_r   ;//int8_fp8_fp16
    end 


    // #(
    // .SWI       (1 ),
    // .EWI       (10), //s2+e8 
    // .MWI       (27), //s1+m16+10bit
    // .HAVE_INT  (0 ), //have int type
    // .INT_CH    (1 ), //a or b have int type ch num
    // .BW_INT_I  (21), //int bitwidth  //int8*int8 *c32 = 21bit
    // .BW_STATUS (3 ),
    // .PIPE      (1 )
    // )
    ne_fp_ffp_add_mwi27 u_ffpadd2(
    .clk (clk ),
    .a   (norm2_z13_r&{41{ffpadd2_op_mode[3]}}),    //3status + s1e10+s1s1m15+10bit
    .b   (norm2_z24_r),
    .z   (ffpadd2_z ),   //3status + s1e10m18+10bit; //nan/inf/zero/s1/e10/s1+s1+m16+10bit
    .mode(ffpadd2_op_mode[2:0])                //3'b100: tf32, 3'b010: fp8, 3'b001: int8
    );

    always@(posedge clk) begin
        ffpadd2_op_mode_1r <= ffpadd2_op_mode;//int8_fp8_fp16_fp4
        ffpadd2_vld_1r     <= ffpadd2_vld;
    end 
    always@(posedge clk) begin
        ffpadd1_z0_r2      <= ffpadd1_z0_r1   ; 
    end 

    
    wire [46:0] ffp2fp_a_r_w = ffpadd2_op_mode_1r[3] ?  {ffpadd2_z[41:39],ffpadd2_z[37:28],ffpadd2_z[27:0],6'd0} : 
                                                        {ffpadd1_z0_r2[46:44],ffpadd1_z0_r2[43:34],ffpadd1_z0_r2[33:0]} ;
    reg  [46:0] ffp2fp_a_r ;
    always@(posedge clk) //int8_fp8_fp16_fp4
    begin
        ffp2fp_a_r <= ffp2fp_a_r_w;//({47{(~ffpadd2_op_mode_1r[3])}} & {ffpadd1_z0_r2[47:45],ffpadd1_z0_r2[43:34],ffpadd1_z0_r2[33:0]}) | 
                      //({47{  ffpadd2_op_mode_1r[3] }} & {ffpadd2_z[31:29],ffpadd2_z[27:18],ffpadd2_z[17:0],16'd0} );
    end 

    always@(posedge clk) //int8_fp8_fp16_fp4
    begin
        ffp2fp_vld_r     <=     ffpadd2_vld_1r;//   (ffpadd1_vld_1r & (~ffpadd1_op_mode_1r[3])) | (ffpadd2_vld_1r & ffpadd2_op_mode_1r[3]);
        ffp2fp_op_mode_r <= ffpadd2_op_mode_1r;//({5{ffpadd1_vld_1r & (~ffpadd1_op_mode_1r[3])}} & ffpadd1_op_mode_1r) |  
                                               //({5{ffpadd2_vld_1r &   ffpadd2_op_mode_1r[3] }} & ffpadd2_op_mode_1r) ;
    end 
    
    //=================================================================================================================
    //ffp2fp 2 clk
    //=================================================================================================================
    wire [1:0] z_is_infnan;
    ne_fp_ffp2fp_m33 #(
    .INTWI(22), //input int data width
    .STWI ( 3), //input ffp status width
    .EWI  (10), //input ffp w width
    .SWI  ( 1), //input ffp sign width
    .SMWI (33)  //input ffp m width (sign bit + m bit)
    )
    u_dot_ffp2fp(
        .clk        (clk            ) ,
        .a          (ffp2fp_a_r     ) , //nan/inf/zero/e10/s1+s1+m32
        .z          (ffp2fp_z       ) ,
        .mode       (ffp2fp_op_mode_r[3:0] ),
        .z_is_infnan(z_is_infnan    )
    );
    always@(posedge clk) begin
        ffp2fp_vld_1r     <= ffp2fp_vld_r;//int8_fp8_fp16_fp4
        ffp2fp_op_mode_1r <= ffp2fp_op_mode_r;
    
        fp_z_vld          <= ffp2fp_vld_1r;
        fp_z_int          <= ffp2fp_op_mode_1r[0];
        fp_z              <= ffp2fp_z;
        fp_infnan         <= z_is_infnan;
    end
    assign fp_z_vld_pre = ffp2fp_vld_1r;
endmodule



