module ne_fp_ffp_add_vector_m33 (
    input                   clk                 , 

    input  [3:0]        op_mode     ,  //3'b001: int8, 3'b010: fp8, 3'b100: tf32, 4'b1000: fp4
    input  [8:0]        e_max       ,
    input  [17:0]       ab_scale    ,//C0-31/C32-63; scale !=0 ,mx mode
    input  [16*6-1:0]   ae_sub      ,
    input  [16*6-1:0]   be_sub      ,
    input  [15:0]       a_e_overflow,
    input  [15:0]       b_e_overflow,
    input  [16*32-1:0]  a_m         ,  // {6'd0,zero,inf,nan,s1,m22}
    output [45:0]       z           ,
    output [28:0]       z_fp4       
);
    wire [2:0]                  a_status_fp8_1          [15:0]  ;
    wire [2:0]                  a_status_fp8_0          [15:0]  ;
    wire [15:0]                 a_fp8_is_zero                   ;
    wire [15:0]                 a_fp8_is_inf                    ;
    wire [15:0]                 a_fp8_is_pinf                   ;
    wire [15:0]                 a_fp8_is_ninf                   ;
    wire [15:0]                 a_fp8_is_nan                    ;
    wire [15:0]                 b_fp8_is_zero                   ;
    wire [15:0]                 b_fp8_is_inf                    ;
    wire [15:0]                 b_fp8_is_pinf                   ;
    wire [15:0]                 b_fp8_is_ninf                   ;
    wire [15:0]                 b_fp8_is_nan                    ;
    wire [8:0]                  a_m_fp8_1               [15:0]  ;
    wire [8:0]                  a_m_fp8_0               [15:0]  ;
    wire [15:0]                 a_m_int8_1              [15:0]  ;
    wire [15:0]                 a_m_int8_0              [15:0]  ;
    wire [30:0]                 a_m_fp_1                [15:0]  ;
    wire [29:0]                 a_m_fp_0                [15:0]  ;
    wire [30:0]                 a_m_sfr_1               [15:0]  ;
    wire [29:0]                 a_m_sfr_0               [15:0]  ;
    wire [30:0]                 a_m_align_mask0_1       [15:0]  ;
    wire [29:0]                 a_m_align_mask0_0       [15:0]  ;
    wire [30:0]                 a_m_align_mask1_1       [15:0]  ;
    wire [29:0]                 a_m_align_mask1_0       [15:0]  ;
    wire [30:0]                 norm_bits_1             [15:0]  ;
    wire [29:0]                 norm_bits_0             [15:0]  ;
    wire [15:0]                 norm_bit_1                      ;
    wire [15:0]                 norm_bit_0                      ;
    wire [31:0]                 significant_1           [15:0]  ;
    wire [30:0]                 significant_0           [15:0]  ;
    wire [16*32-1:0]            adder_in_1                      ;
    wire [16*31-1:0]            adder_in_0                      ;
    wire [31:0]                 tree_out1_0_t                   ;
    wire [31:0]                 tree_out1_1_t                   ;
    wire [30:0]                 tree_out0_0_t                   ;
    wire [30:0]                 tree_out0_1_t                   ;
    reg  [31:0]                 tree_out1_0                     ;
    reg  [31:0]                 tree_out1_1                     ;
    reg  [30:0]                 tree_out0_0                     ;
    reg  [30:0]                 tree_out0_1                     ;
    wire [31:0]                 adder1_z                        ;
    wire [30:0]                 adder0_z                        ;
    wire [31:0]                 adder_z                         ;
    wire                        z_fp8_zero_t                    ;
    wire                        z_fp8_nan_t                     ;
    wire                        z_fp8_inf_t                     ;
    wire [9:0]                  z_e0_t                          ;
    wire                        e_overflow_pos                  ;
    wire                        e_overflow_neg                  ;
    wire [11:0]                 z_e_t                           ;
    wire [32:0]                 z_m_fp8_t                       ;
    wire [20:0]                 z_int8_t                        ;
    wire [45:0]                 z_t                             ;
    reg  [45:0]                 z_ext                           ;
    reg  [28:0]                 z_fp4_r                         ;
    reg  [3:0]                  op_mode_1r                      ;
    reg                         z_fp8_zero                      ;
    reg                         z_fp8_inf                       ;
    reg                         z_fp8_nan                       ;
    reg  [9:0]                  z_e                             ;
    reg                         z_s_inf                         ;


    wire  [16*5-1:0]   a_e_sub;
    wire  [16*5-1:0]   b_e_sub;
    //c0-c31
    wire  [15:0]       a_fp4_is_zero; 
    wire  [15:0]       b_fp4_is_zero;
    wire  [4:0]        a_m_fp4[0:15];
    wire  [4:0]        b_m_fp4[0:15];
    wire  [16*32-1:0]  adder_in_01  ;  //bit 14:0 ; 5'bs+m5+4'd0+norm ;
    wire  [16*31-1:0]  adder_in_00  ;  //bit 14:0 ; 5'bs+m5+4'd0+norm ; 
    reg                z_fp4_is_zero;
    //c32-c63
    wire  [15:0]       a1_fp4_is_zero; 
    wire  [15:0]       b1_fp4_is_zero;
    wire  [4:0]        a1_m_fp4[0:15];
    wire  [4:0]        b1_m_fp4[0:15];
    wire  [16*3-1:0]   a1_e_sub ;
    wire  [16*3-1:0]   b1_e_sub ;
    wire  [13:0]       a1_m_fp_1 [15:0]  ;
    wire  [13:0]       a1_m_fp_0 [15:0]  ;
    wire  [13:0]       a1_m_sfr_1[15:0]  ;
    wire  [13:0]       a1_m_sfr_0[15:0]  ;
    wire  [16*15-1:0]  adder_in_11  ;  //bit 14:0 ; 5'bs+m5+4'd0+norm ; 
    wire  [16*15-1:0]  adder_in_10  ;  //bit 14:0 ; 5'bs+m5+4'd0+norm ; 
    reg                z1_fp4_is_zero;
    reg   [19:0]       z_e_fp4;
   
    wire [32*15-1:0] adder_in_2;
    wire [14:0] tree_out2_0_t;
    wire [14:0] tree_out2_1_t;
    reg  [14:0] tree_out2_0;
    reg  [14:0] tree_out2_1;
    wire [14:0] adder2_z;
 
    genvar i;
    generate for(i = 0; i < 16; i = i + 1) begin: gen_add_align
        assign a_fp4_is_zero[i] = { {op_mode[3]}}& a_m[i*32+15];
        assign b_fp4_is_zero[i] = { {op_mode[3]}}& a_m[i*32+ 7];
        assign a_m_fp4[i]       = {5{op_mode[3]}}& a_m[i*32+12:i*32+8]; //c1
        assign b_m_fp4[i]       = {5{op_mode[3]}}& a_m[i*32+ 4:i*32+0]; //c0
        
        assign a_e_sub[i*5+4 : i*5] = op_mode[3]?{2'd0,ae_sub[i*6+2 : i*6]} : ae_sub[i*6+4 : i*6];
        assign b_e_sub[i*5+4 : i*5] = op_mode[3]?{2'd0,be_sub[i*6+2 : i*6]} : be_sub[i*6+4 : i*6];

        assign a_status_fp8_1[i]    = {3{op_mode[1]}} & a_m[i*32+27:i*32+25];
        assign a_status_fp8_0[i]    = {3{op_mode[1]}} & a_m[i*32+11:i*32+9];
        assign a_fp8_is_zero[i]     = a_status_fp8_1[i][2];
        assign a_fp8_is_inf[i]      = a_status_fp8_1[i][1];
            assign a_fp8_is_pinf[i]  = a_fp8_is_inf[i] & (a_fp8_is_inf[i] ^ a_m[i*32+24]);
            assign a_fp8_is_ninf[i]  = a_fp8_is_inf[i] & (a_fp8_is_inf[i] & a_m[i*32+24]);
        assign a_fp8_is_nan[i]      = a_status_fp8_1[i][0];

        assign b_fp8_is_zero[i]     = a_status_fp8_0[i][2];
        assign b_fp8_is_inf[i]      = a_status_fp8_0[i][1];
            assign b_fp8_is_pinf[i]  = b_fp8_is_inf[i] & (b_fp8_is_inf[i] ^ a_m[i*32+8]);
            assign b_fp8_is_ninf[i]  = b_fp8_is_inf[i] & (b_fp8_is_inf[i] & a_m[i*32+8]);
        assign b_fp8_is_nan[i]      = a_status_fp8_0[i][0];
        assign a_m_fp8_1[i]         = { 9{op_mode[1]}}&a_m[i*32+24:i*32+16];
        assign a_m_fp8_0[i]         = { 9{op_mode[1]}}&a_m[i*32+8:i*32];
        assign a_m_int8_1[i]        = {16{op_mode[0]}}&a_m[i*32+31:i*32+16];
        assign a_m_int8_0[i]        = {16{op_mode[0]}}&a_m[i*32+15:i*32];
        assign a_m_fp_1[i]          = op_mode[3] ? {{22{a_m_fp4[i][4]  }},a_m_fp4[i]  , 4'd0}: //fp4:m5+4'd0
                                                   {{ 5{a_m_fp8_1[i][8]}},a_m_fp8_1[i],17'd0/*{4{a_m_fp8_1[i][8]}}*/};  //tf32:23bit+4bit = 27bit
        assign a_m_fp_0[i]          = op_mode[3] ? {{ 21{b_m_fp4[i][4]  }},b_m_fp4[i] , 4'd0}:  //fp4:m5+4'd0
                                                   {{ 4{a_m_fp8_0[i][8]}},a_m_fp8_0[i],17'd0/*{4{a_m_fp8_0[i][8]}}*/}; //4+9+8bit
        assign a_m_sfr_1[i]         = $signed(a_m_fp_1[i]) >>> a_e_sub[i*5+4 : i*5];  //27bit >>>  
        assign a_m_sfr_0[i]         = $signed(a_m_fp_0[i]) >>> b_e_sub[i*5+4 :i*5];
        assign a_m_align_mask0_1[i] = {31{1'b1}} << $signed(a_e_sub[i*5+4 : i*5]); 
        assign a_m_align_mask0_0[i] = {30{1'b1}} << $signed(b_e_sub[i*5+4 : i*5]);
        assign a_m_align_mask1_1[i] = a_e_overflow[i] ? {31{1'b0}} : ~a_m_align_mask0_1[i];
        assign a_m_align_mask1_0[i] = b_e_overflow[i] ? {30{1'b0}} : ~a_m_align_mask0_0[i];
        assign norm_bits_1[i]       = a_m_align_mask1_1[i] & a_m_fp_1[i];
        assign norm_bits_0[i]       = a_m_align_mask1_0[i] & a_m_fp_0[i];
        assign norm_bit_1[i]        = |norm_bits_1[i];
        assign norm_bit_0[i]        = |norm_bits_0[i];
        assign significant_1[i]     = {a_m_sfr_1[i], norm_bit_1[i]} & {32{~a_e_overflow[i]}}; //4{s1},s1,m26,1 norm_bit
        assign significant_0[i]     = {a_m_sfr_0[i], norm_bit_0[i]} & {31{~b_e_overflow[i]}}; //4{s1},s1,m12 ,1 norm
 // [FIX] Expanded +: for adder_in_01 / 00 assignments
        assign adder_in_01[(i*32)+31 : i*32] = op_mode[0] ? {{12{1'b0}},{4{a_m_int8_1[i][15]}}, a_m_int8_1[i][15:0]} : significant_1[i];
        assign adder_in_00[(i*31)+30 : i*31] = op_mode[0] ? {{11{1'b0}},{4{a_m_int8_0[i][15]}}, a_m_int8_0[i][15:0]} : significant_0[i];
    end
    endgenerate
    
    generate for(i = 0; i < 16; i = i + 1) begin: gen_add_fp4
        assign a1_fp4_is_zero[i] = {{op_mode[3]}}&a_m[i*32+31];
        assign b1_fp4_is_zero[i] = {{op_mode[3]}}&a_m[i*32+23];
        assign a1_m_fp4[i] = {5{op_mode[3]}} & a_m[i*32+28:i*32+24] ; //c3
        assign b1_m_fp4[i] = {5{op_mode[3]}} & a_m[i*32+20:i*32+16] ; //c2   
        // [FIX] Expanded +: for a1_e_sub / b1_e_sub
        assign a1_e_sub[(i*3)+2 : i*3] = ae_sub[(i*6)+5 : (i*6)+3] ;
        assign b1_e_sub[(i*3)+2 : i*3] = be_sub[(i*6)+5 : (i*6)+3] ;
        assign a1_m_fp_1[i]  = {{5{a1_m_fp4[i][4]}},a1_m_fp4[i],4'd0}; //5'bs+m5+4'd0
        assign a1_m_fp_0[i]  = {{5{b1_m_fp4[i][4]}},b1_m_fp4[i],4'd0};
        // [FIX] Expanded +: for shift amount
        assign a1_m_sfr_1[i] = $signed(a1_m_fp_1[i]) >>> a1_e_sub[(i*3)+2 : i*3];
        assign a1_m_sfr_0[i] = $signed(a1_m_fp_0[i]) >>> b1_e_sub[(i*3)+2 : i*3];
        
        // [FIX] Expanded +: for adder_in_11 / 10
        assign adder_in_11[(i*15)+14 : i*15] = {a1_m_sfr_1[i],1'd0}; //5'ds+m5+4'd0+norm_bit   //e_sub max = 4 , norm_bit=0
        assign adder_in_10[(i*15)+14 : i*15] = {a1_m_sfr_0[i],1'd0}; //5'ds+m5+4'd0+norm_bit
    end
    endgenerate
    generate for(i = 0; i < 8; i = i + 1) begin: gen_add_in0
        // [FIX] Expanded +: for adder_in_1/0 assignments
        assign adder_in_1[(i*32)+31 : i*32] = adder_in_01[(i*32)+31 : i*32];
        assign adder_in_0[(i*31)+30 : i*31] = adder_in_00[(i*31)+30 : i*31]; 

        assign adder_in_2[((i*2)*15)+14 : (i*2)*15]     = op_mode[3] ? {adder_in_00[((i+8)*31)+14 : (i+8)*31]} : 15'd0;  // 5'bs+m5+4'b0+1norm
        assign adder_in_2[((i*2+1)*15)+14 : (i*2+1)*15] = op_mode[3] ? {adder_in_01[((i+8)*32)+14 : (i+8)*32]} : 15'd0;
    end
    endgenerate
    generate for(i = 8; i < 16; i = i + 1) begin: gen_add_in1
        // [FIX] Expanded +: for adder_in_1/0 assignments
        assign adder_in_1[(i*32)+31 : i*32] = op_mode[3] ? 
            {{17{adder_in_11[((i-8)*15)+14]}}, adder_in_11[((i-8)*15)+14 : (i-8)*15]} : 
            adder_in_01[(i*32)+31 : i*32];
            
        assign adder_in_0[(i*31)+30 : i*31] = op_mode[3] ? 
            {{16{adder_in_10[((i-8)*15)+14]}}, adder_in_10[((i-8)*15)+14 : (i-8)*15]} : 
            adder_in_00[(i*31)+30 : i*31];

        // [FIX] Expanded +: for adder_in_2 assignments
        assign adder_in_2[((i*2)*15)+14 : (i*2)*15]     = op_mode[3] ? {adder_in_10[(i*15)+14 : i*15]} : 15'd0;
        assign adder_in_2[((i*2+1)*15)+14 : (i*2+1)*15] = op_mode[3] ? {adder_in_11[(i*15)+14 : i*15]} : 15'd0;
    end
    endgenerate


    assign z_fp8_zero_t = (&a_fp8_is_zero) & (&b_fp8_is_zero);
    assign z_fp8_nan_t = (|a_fp8_is_nan) | (|b_fp8_is_nan) | (((|a_fp8_is_pinf)|(|b_fp8_is_pinf)) & ((|a_fp8_is_ninf)|(|b_fp8_is_ninf)));
    assign z_fp8_inf_t = ((|a_fp8_is_inf) | (|b_fp8_is_inf)) & (~z_fp8_nan_t);
    localparam [7:0] FP8E_SFL   = 5;//C32 sum
    localparam [7:0] FP4E_SEL   = 5+5;//fp4:C32 sum ,e_max=5
    wire [7:0] e_sfr =   FP8E_SFL;

    assign z_e0_t = {e_max[8], e_max[8:0]} + e_sfr;//4;
    //assign e_overflow_pos = (~z_e0_t[8]) & z_e0_t[7];//(~z_e0_t[9]) & z_e0_t[8];
    //assign e_overflow_neg = z_e0_t[8] & (~z_e0_t[7]);//z_e0_t[9] & (~z_e0_t[8]);
    assign z_e_t = {z_e0_t[9],z_e0_t[9:0]} + {ab_scale[8],ab_scale[8],ab_scale[8:0]} ;  //mxfp8/ fp8/tf32
    
    wire   z_s_fp8  = z_fp8_inf ?z_s_inf: adder_z[31];    

    assign z_m_fp8_t  = {/* adder_z[20]*/z_s_fp8 , adder_z[31:0]};  //fp8: 1s+(m9 + 8'b0+1bit norm )*32 = 24bit ,double sign bit
    assign z_int8_t = adder_z[20:0];
    

    //-----pipe0---
    wire [10:0]  fp4_c0_ab_scale    = {ab_scale[ 8],ab_scale[ 8:0]} + FP4E_SEL;
    wire [10:0]  fp4_c32_ab_scale   = {ab_scale[17],ab_scale[17:9]} + FP4E_SEL;
    wire [19:0] z_e_fp4_scale       = {fp4_c32_ab_scale[9:0],fp4_c0_ab_scale[9:0]};
    //---pip1----
    wire [15:0] z_fp4_m0  = {adder_z[14],adder_z[14:0]}; //double sige bit
    wire [15:0] z_fp4_m32 = {adder2_z[14],adder2_z[14:0]};// 1'bs+5'bs+M5+4'b0+1norm

    wire [28:0]     z_fp4_c32 = op_mode_1r[3]?{z1_fp4_is_zero,2'd0,z_e_fp4[19:10],z_fp4_m32[15:0]}:29'd0;

    assign z_t = op_mode_1r[3] ? {z_fp4_is_zero,2'd0,z_e_fp4[9:0],z_fp4_m0[15:0],17'd0} :
                 op_mode_1r[1] ? {z_fp8_zero , z_fp8_inf , z_fp8_nan , z_e[9:0], z_m_fp8_t[32:0] } : //mxfp8
                                 {{25{1'b0}}, z_int8_t};
    
    always@(posedge clk) begin
    
        op_mode_1r  <= op_mode       ;
        
        tree_out1_0 <= tree_out1_0_t ;//int8_fp8_fp16_fp4
        tree_out1_1 <= tree_out1_1_t ;//int8_fp8_fp16_fp4
        tree_out0_0 <= tree_out0_0_t ;//int8_fp8_fp4
        tree_out0_1 <= tree_out0_1_t ;//int8_fp8_fp4
        tree_out2_0 <= tree_out2_0_t ;//fp4
        tree_out2_1 <= tree_out2_1_t ;//fp4
 

        z_fp8_zero  <= z_fp8_zero_t  ;//fp8
        z_fp8_inf   <= z_fp8_inf_t   ;
        z_fp8_nan   <= z_fp8_nan_t   ;


        z_e         <= z_e_t[9:0]    ;//fp8_fp16
        z_s_inf     <= (op_mode[1] & z_fp8_inf_t  & ((|a_fp8_is_ninf)|(|b_fp8_is_ninf)));


        z_fp4_is_zero <= (&a_fp4_is_zero[ 7:0]) & (&b_fp4_is_zero[ 7:0]) & (&a1_fp4_is_zero[ 7:0]) & (&b1_fp4_is_zero[ 7:0]); //fp4
        z1_fp4_is_zero<= (&a_fp4_is_zero[15:8]) & (&b_fp4_is_zero[15:8]) & (&a1_fp4_is_zero[15:8]) & (&b1_fp4_is_zero[15:8]);

        z_e_fp4       <= z_e_fp4_scale;        
        z_ext       <= z_t           ;//int8_fp8_fp16_fp4
        z_fp4_r <= z_fp4_c32; 
    end

    assign z = z_ext;
    assign z_fp4 = z_fp4_r;    
  

    // ne_dw_add_tree#(
    //     .BW_ADDER       (32         ),
    //     .NUM_INPUT      (16         )
    // )u_tree_1(
    //     .adder_in       (adder_in_1     ),
    //     .out0           (tree_out1_0_t ),
    //     .out1           (tree_out1_1_t )
    // );
    DW02_tree_w32n16 u_tree_0(
        .INPUT(adder_in_1), 
        .OUT0(tree_out1_0_t), 
        .OUT1(tree_out1_1_t)
    );


    // ne_dw_add_tree#(
    //     .BW_ADDER       (31         ),
    //     .NUM_INPUT      (16         )
    // )u_tree_0(
    //     .adder_in       (adder_in_0     ),
    //     .out0           (tree_out0_0_t ),
    //     .out1           (tree_out0_1_t )
    // );
    DW02_tree_w31n16 u_tree_1(
        .INPUT(adder_in_0), 
        .OUT0(tree_out0_0_t), 
        .OUT1(tree_out0_1_t)
    );

    // ne_dw_add_tree#(
    //     .BW_ADDER       (15         ),
    //     .NUM_INPUT      (32         )
    // )u_tree2(
    //     .adder_in       (adder_in_2     ),
    //     .out0           (tree_out2_0_t ),
    //     .out1           (tree_out2_1_t )
    // );
    DW02_tree_w15n32 u_tree_2(
        .INPUT(adder_in_2), 
        .OUT0(tree_out2_0_t), 
        .OUT1(tree_out2_1_t)
    );


//-----------------------1 clk---------------------
    // ne_dw_add#(
    //     .BW_ADDER       (32         )
    // )u_add_1(
    //     .adder_a        (tree_out1_0    ),
    //     .adder_b        (tree_out1_1    ),
    //     .adder_z        (adder1_z       )
    // );
    DW01_add_w32 u_adder_0(
            .A      (tree_out1_0    ),
            .B      (tree_out1_1    ),
            .CI     (1'b0       ),
            .SUM    (adder1_z    ),
            .CO     ()
    );

    // ne_dw_add#(
    //     .BW_ADDER       (31         )
    // )u_add_0(
    //     .adder_a        (tree_out0_0    ),
    //     .adder_b        (tree_out0_1    ),
    //     .adder_z        (adder0_z       )
    // );
    DW01_add_w31 u_adder_1(
            .A      (tree_out0_0    ),
            .B      (tree_out0_1    ),
            .CI     (1'b0       ),
            .SUM    (adder0_z    ),
            .CO     ()
    );
    wire[31:0] adder1_z_mux = op_mode_1r[0] ? {{12{adder1_z[19]}}, adder1_z[19:0]} : adder1_z;
    wire[31:0] adder0_z_mux = op_mode_1r[0] ? {{12{adder0_z[19]}}, adder0_z[19:0]} : {adder0_z[30],adder0_z[30:0]};
        //fp4
        //  ne_dw_add#(
        //     .BW_ADDER       (15         )
        // )u_add_20(
        //     .adder_a        (tree_out2_0    ),
        //     .adder_b        (tree_out2_1    ),
        //     .adder_z        (adder2_z       )
        // );
    DW01_add_w15 u_adder_2(
            .A      (tree_out2_0    ),
            .B      (tree_out2_1    ),
            .CI     (1'b0       ),
            .SUM    (adder2_z    ),
            .CO     ()
    );

    // ne_dw_add#(
    //     .BW_ADDER       (32         )
    // )u_add_2(
    //     .adder_a        (adder1_z_mux                    ) ,
    //     .adder_b        (adder0_z_mux                    ) ,
    //     .adder_z        (adder_z                         )  //fp4: [14:0]
    // );
    DW01_add_w32 u_adder_3(
            .A      (adder1_z_mux    ),
            .B      (adder0_z_mux    ),
            .CI     (1'b0       ),
            .SUM    (adder_z    ),
            .CO     ()
    );

endmodule