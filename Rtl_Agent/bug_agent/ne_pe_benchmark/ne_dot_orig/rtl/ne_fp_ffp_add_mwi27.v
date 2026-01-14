module ne_fp_ffp_add_mwi27(
    clk,
    a,
    b,
    z,
    mode                //3'b100: tf32, 3'b010: fp8, 3'b001: int8
);

    parameter SWI       = 1;
    parameter EWI       = 10;
    parameter MWI       = 27;
    parameter HAVE_INT  = 0;
    parameter INT_CH    = 1;
    parameter BW_INT_I  = 21;
    parameter BW_STATUS = 3;
    parameter PIPE      = 1;   
    // =========================================================
    // 1. Parameter Calculations
    // =========================================================
    localparam                  SWO          = SWI;
    localparam                  EWO          = EWI;
    localparam                  MWO          = MWI + 1;
    localparam                  BWA          = BW_STATUS+SWI+EWI+MWI;
    localparam                  BWZ          = BW_STATUS+SWO+EWO+MWO;
    localparam                  BW_INT_O     = INT_CH == 1 ? BW_INT_I + 2 : BW_INT_I + 1;
    //localparam MAX_BIASED_EXP = {EWI{1'b1}}; // 例如 EWI=8 时，值为 8'hFF = 255
    // Calculate Adder Width
    localparam VAL_A_TEMP = (BW_INT_O > (MWI + 3)) ? BW_INT_O : (MWI + 3);
    localparam VAL_B_TEMP = ((BW_INT_O*2 + 1) > (MWI + 3)) ? (BW_INT_O*2 + 1) : (MWI + 3);
    localparam BW_ADDER   = (INT_CH == 1) ? VAL_A_TEMP : VAL_B_TEMP;
    
   // localparam                  BIAS_I       = 2 ** (EWI - 3) - 1;
   // localparam        [EWO-1:0] BIAS_Z       = 2 ** (EWO - 3) - 1;
    //localparam signed [EWO-1:0] BIAS_Z_NEG   = -BIAS_Z;
    // 假设 EWO = 8

    localparam [7:0] BIAS_I       = 8'b01111111; // 31
localparam [7:0] BIAS_Z       = 8'b01111111; // 31
localparam signed [7:0] BIAS_Z_NEG = 8'b10000001; // -31 in 8-bit two's complement
    // Hardcoded log2(29) = 5
    localparam                  BW_ESUB      = 5; 

    input                   clk;
    input  [BWA-1:0]        a;
    input  [BWA-1:0]        b;
    output [BWZ-1:0]        z;
    input  [2:0]            mode;

    // =========================================================
    // 2. Signal Declarations (FIXED & COMPLETED)
    // =========================================================
    wire                    a_s, b_s;
    wire [EWI-1:0]          a_e, b_e;
    wire [MWI-1:0]          a_m, b_m;
    wire [BW_STATUS-1:0] z_status;
    wire [BW_STATUS-1:0]    a_status, b_status;
    wire                    a_is_zero, a_is_inf, a_is_nan;
    wire                    b_is_zero, b_is_inf, b_is_nan;

    wire                    a_e_is_zero, a_e_is_max, a_m_is_zero;
    wire                    b_e_is_zero, b_e_is_max, b_m_is_zero;
    wire                    a_is_zero_without, a_is_inf_without, a_is_nan_without;
    wire                    b_is_zero_without, b_is_inf_without, b_is_nan_without;

    wire                    ae_lt_be;
    wire [MWI-1:0]          large_m, small_m;
    wire [EWI-1:0]          large_e, small_e;
    wire                    large_m_s, small_m_s;
    wire [EWI:0]            e_sub_t;
    wire [EWI-1:0]          e_sub;
    wire [BW_ESUB-1:0]      e_sub_m;
    wire                    align_overflow;
    wire signed [MWI-1:0]   small_m_align0;
    wire [MWI-1:0]          small_m_align;
    wire [MWI-1:0]          align_mask0, align_mask, align_norm_bits;
    wire                    align_norm_bit;
    wire [MWI+2:0]          large_significant, small_significant;
    
    wire [EWO-1:0]          z_e;
    wire [MWO-1:0]          z_m;
    wire [EWO:0]            z_e0_tt;
    wire [EWO-1:0]          z_e0_t, z_e_t;
    wire                    z_s, z_s_zero, z_s_zero_t;
    wire                    z_inf_nan_t, z_is_zero_t, z_is_inf_t, z_is_nan_t;
    wire                    z_s_inf_t, z_s_nan_t;
    wire                    z_e_overflow1, z_e_overflow1_t;
    
    // [FIX] Added missing declarations here
    wire                    z_is_zero, z_is_zero1, z_is_inf, z_is_nan, z_inf_nan, z_s_inf, z_s_nan;
    wire                    e_overflow_pos, e_overflow_neg;

    wire [BW_INT_I-1:0]     int_a0, int_b0, int_a1, int_b1;
    wire [BW_INT_O-1:0]     int_z0, int_z1;
    wire [BW_ADDER-1:0]     adder_a, adder_b, adder_z;
    wire [BW_ADDER-1:0]     adder_a_t, adder_b_t;
    
    wire [SWO+EWO+MWO-1:0]  z_zero, z_inf, z_nan, z_d, z_o;
    wire [2:0]              mode_o;

    reg  [BW_ADDER-1:0]     adder_a_1r, adder_b_1r;
    reg                     z_s_zero_1r, z_e_overflow1_1r;
    reg  [EWO-1:0]          z_e_1r;
    reg                     z_inf_nan_1r, z_is_zero_1r, z_is_inf_1r, z_is_nan_1r;
    reg                     z_s_inf_1r, z_s_nan_1r;
    reg  [2:0]              mode_1r;

    // =========================================================
    // 3. Unpacking Logic
    // =========================================================
    
    wire [2:0] a_status_padded;
    wire [2:0] b_status_padded;
    
  generate if(BW_STATUS > 0) begin: gen_with_status
    assign {a_status, a_s, a_e, a_m} = a;
    assign {b_status, b_s, b_e, b_m} = b;

    //  无条件提取 status（不管 mode）
    wire [2:0] a_status_padded = (BW_STATUS >= 3) ? a_status[2:0] :
                                 (BW_STATUS == 2) ? {1'b0, a_status} :
                                                    {2'b00, a_status[0]};
    wire [2:0] b_status_padded = (BW_STATUS >= 3) ? b_status[2:0] :
                                 (BW_STATUS == 2) ? {1'b0, b_status} :
                                                    {2'b00, b_status[0]};

    //  不再用 mode[2] 屏蔽！保留原始状态值
    assign a_is_nan  = a_status_padded[2];
    assign a_is_inf  = a_status_padded[1];
    assign a_is_zero = a_status_padded[0];
    assign b_is_nan  = b_status_padded[2];
    assign b_is_inf  = b_status_padded[1];
    assign b_is_zero = b_status_padded[0];

    // Tie-off unused signals
    assign a_is_zero_without = 1'b0; assign a_is_inf_without = 1'b0; assign a_is_nan_without = 1'b0;
    assign b_is_zero_without = 1'b0; assign b_is_inf_without = 1'b0; assign b_is_nan_without = 1'b0;
    assign {a_e_is_zero, a_e_is_max, a_m_is_zero} = 3'b0;
    assign {b_e_is_zero, b_e_is_max, b_m_is_zero} = 3'b0;
        
    end else begin: gen_no_status
        assign {a_s, a_e, a_m} = mode[2] ? a[BWA-1:0] : {BWA{1'b0}};
        assign {b_s, b_e, b_m} = mode[2] ? b[BWA-1:0] : {BWA{1'b0}};
        assign a_status = {BW_STATUS{1'b0}};
        assign b_status = {BW_STATUS{1'b0}};

        assign a_e_is_zero = $signed(a_e) == -BIAS_I;
        //assign a_e_is_max = (a_e == MAX_BIASED_EXP);
        assign a_e_is_max  = a_e == BIAS_I + 1;
        assign a_m_is_zero = ~(|a_m);
        assign a_is_zero_without   = a_e_is_zero & a_m_is_zero;
        assign a_is_inf_without    = a_e_is_max & a_m_is_zero;
        assign a_is_nan_without    = a_e_is_max & (~a_m_is_zero);

        assign b_e_is_zero = $signed(b_e) == -BIAS_I;    
        //assign b_e_is_max = (b_e == MAX_BIASED_EXP);
        assign b_e_is_max  = b_e == BIAS_I + 1;
        assign b_m_is_zero = ~(|b_m);
        assign b_is_zero_without   = b_e_is_zero & b_m_is_zero;
        assign b_is_inf_without    = b_e_is_max & b_m_is_zero;
        assign b_is_nan_without    = b_e_is_max & (~b_m_is_zero);
        
        assign a_is_zero = a_is_zero_without; assign a_is_inf = a_is_inf_without; assign a_is_nan = a_is_nan_without;
        assign b_is_zero = b_is_zero_without; assign b_is_inf = b_is_inf_without; assign b_is_nan = b_is_nan_without;
    end
    endgenerate

    // =========================================================
    // 4. Alignment Logic
    // =========================================================
    assign ae_lt_be         = $signed(a_e) < $signed(b_e);
    assign large_m          = ae_lt_be ? b_m : a_m;
    assign small_m          = ae_lt_be ? a_m : b_m;
    assign large_e          = ae_lt_be ? b_e : a_e;
    assign small_e          = ae_lt_be ? a_e : b_e;
    assign large_m_s        = large_m[MWI-1];
    assign small_m_s        = small_m[MWI-1];
    assign e_sub_t          = ae_lt_be ? {b_e[EWI-1], b_e} - {a_e[EWI-1], a_e} : {a_e[EWI-1], a_e} - {b_e[EWI-1], b_e};
    assign e_sub            = e_sub_t[EWI-1:0];
    
    assign align_overflow   = (e_sub > MWI - 2);
    //|| $signed(e_sub) > BIAS_I + 1 ;
    
    assign e_sub_m          = e_sub[BW_ESUB-1:0];
    assign small_m_align0   = $signed(small_m) >>> e_sub_m;
    //assign small_m_align0 = small_m >> e_sub_m;
    assign align_mask0      = {(MWI){1'b1}} << e_sub_m;
    assign small_m_align    = align_overflow ? {(MWI){small_m_s}} : small_m_align0;
    assign align_mask       = align_overflow ? {(MWI){1'b1}} : ~align_mask0;
    assign align_norm_bits  = align_mask & small_m;
    assign align_norm_bit   = |align_norm_bits;
    assign large_significant = {large_m_s, large_m, 2'd0};
    assign small_significant = {small_m_s, small_m_align, align_norm_bit, 1'b0} & {(MWI+3){~align_overflow}};
    
    assign z_m              = adder_z[MWI+2:2];
    assign z_is_zero        = z_is_zero1 | ((~(|z_m)) & (~(z_is_inf | z_is_nan)) );
    assign z_e0_tt          = {large_e[EWI-1], large_e} + {{(EWI){1'b0}}, 1'b1};
    assign z_e0_t           = z_e0_tt[EWO-1:0];
    assign e_overflow_pos   = ~z_e0_t[EWI-1] & z_e0_t[EWI-2];
    assign e_overflow_neg   = z_e0_t[EWI-1] & (~z_e0_t[EWI-2]);
    assign z_e_t            = z_e0_t;
    assign z_s_zero_t       = a_s & b_s;
    assign z_s              = z_is_zero ? z_s_zero : z_m[MWO-1];

    // =========================================================
    // 5. Integer Path & Adder Mux (FIXED Zero Replication)
    // =========================================================
    generate if (HAVE_INT == 1) begin: int_proc
        // Output Saturation
        assign int_z0 = adder_z[BW_INT_O-1:BW_INT_O-2] == 2'b01 ? {2'b00, 1'b0, {(BW_INT_I-1){1'b1}}} :
                        adder_z[BW_INT_O-1:BW_INT_O-2] == 2'b10 ? {2'b11, 1'b1, {(BW_INT_I-1){1'b0}}} :
                        adder_z[BW_INT_O-1:0];
        if (INT_CH == 2) begin: int_o_ch2
            assign int_z1 = adder_z[BW_ADDER-1:BW_INT_O+1];
        end

        assign int_a0 = mode[0] ? a[BW_INT_I-1:0] : {(BW_INT_I){1'b0}};
        assign int_b0 = mode[0] ? b[BW_INT_I-1:0] : {(BW_INT_I){1'b0}};

        if (INT_CH == 2) begin: int_i_split_ch2
            assign int_a1 = mode[0] ? a[BW_INT_I*2-1:BW_INT_I] : {(BW_INT_I){1'b0}};
            assign int_b1 = mode[0] ? b[BW_INT_I*2-1:BW_INT_I] : {(BW_INT_I){1'b0}};
        end
        
        // [FIX] Removed explicit padding concatenation to avoid "0 replication" error.
        // Verilog will automatically zero-pad high bits.
        if (INT_CH == 2) begin: adder_i_ch2
            assign adder_a_t = mode[2] ? large_significant :
                               mode[0] ? {int_a1[BW_INT_I-1], int_a1, 1'b0, int_a0[BW_INT_I-1], int_a0} : {(BW_ADDER){1'b0}};
                               
            assign adder_b_t = mode[2] ? small_significant :
                               mode[0] ? {int_b1[BW_INT_I-1], int_b1, 1'b0, int_b0[BW_INT_I-1], int_b0} : {(BW_ADDER){1'b0}};
        end else begin: adder_i_ch1
            assign adder_a_t =  mode[0] ? {{(BW_ADDER-BW_INT_I){int_a0[BW_INT_I-1]}}, int_a0} : 
                                large_significant;
            assign adder_b_t = mode[0] ? {{(BW_ADDER-BW_INT_I){int_b0[BW_INT_I-1]}}, int_b0} : 
                                small_significant;
        end
    end else begin: no_int_proc
        // [FIX] Removed explicit padding
        assign adder_a_t = large_significant;
        assign adder_b_t = small_significant;
    end
    endgenerate

    // =========================================================
    // 6. Post Processing Logic
    // =========================================================
    assign z_inf_nan_t      = a_is_inf & b_is_inf & (a_s ^ b_s);
    assign z_is_zero_t      = a_is_zero & b_is_zero;
    assign z_e_overflow1_t  = 1'd0;
    assign z_is_inf_t       = ((a_is_inf | b_is_inf) & (~z_is_nan_t));
    assign z_is_nan_t       = a_is_nan | b_is_nan | z_inf_nan_t;
    assign z_s_inf_t        = a_is_inf ? a_s : b_s;
    assign z_s_nan_t        = a_is_nan ? a_s : b_is_nan ? b_s : 1'b1;

    // Output Generation
    generate if(BW_STATUS > 0) begin: gen_out_with_status
        assign z_status = {z_is_nan, z_is_inf, z_is_zero};
        assign z = {z_status, z_o};
    end else begin: gen_out_without_status
        assign z = z_o;
    end
    endgenerate
    //assign z = { (mode_o[2] ? {z_is_nan, z_is_inf, z_is_zero} : 3'b000), z_o };
    assign z_d = {z_s, z_e, z_m};
    wire [EWO-1:0] z_e_max = BIAS_Z + 1;
    wire signed [EWO-1:0] z_e_zero = BIAS_Z_NEG;
    assign z_nan  = {z_s_nan, z_e_max , {z_s_nan,z_s_nan, 1'b1,{(MWO-3){1'b0}}} };
    assign z_zero = {z_s    , z_e_zero, {z_s    ,z_s    ,{(MWO-2){1'b0}}} };
    assign z_inf  = {z_s_inf, z_e_max , {z_s_inf,z_s_inf,{(MWO-2){1'b0}}} }; 

    generate if (HAVE_INT == 1) begin: int_out
        if (INT_CH == 2) begin: int_out_ch2
            assign z_o = mode_o[0] ? {{(SWO+EWO+MWO-(BW_INT_O*2)){1'b0}}, int_z1, int_z0} : 
                         (z_is_nan ? z_nan : z_is_inf ? z_inf : z_is_zero ? z_zero : z_d);
        end else begin: int_out_ch1
            assign z_o = mode_o[0] ? {{(SWO+EWO+MWO-(BW_INT_O)){int_z0[BW_INT_O-1]}}, int_z0[BW_INT_O-1:0]} : 
                         (z_is_nan ? z_nan : z_is_inf ? z_inf : z_is_zero ? z_zero : z_d);
        end
    end else begin: no_int_out
        assign z_o = z_is_nan ? z_nan : z_is_inf ? z_inf : z_is_zero ? z_zero : z_d;
    end
    endgenerate

    // =========================================================
    // 7. Pipeline Logic
    // =========================================================
    generate if(PIPE == 1) begin: gen_pipe
        always@(posedge clk) begin
            adder_a_1r       <= adder_a_t;
            adder_b_1r       <= adder_b_t;
            mode_1r          <= mode;
            z_s_zero_1r      <= z_s_zero_t;
            z_e_overflow1_1r <= z_e_overflow1_t;
            z_e_1r           <= z_e_t;
            z_inf_nan_1r     <= z_inf_nan_t;
            z_is_zero_1r     <= z_is_zero_t;
            z_is_inf_1r      <= z_is_inf_t;
            z_is_nan_1r      <= z_is_nan_t;
            z_s_inf_1r       <= z_s_inf_t;
            z_s_nan_1r       <= z_s_nan_t;
        end

        assign adder_a       = adder_a_1r;
        assign adder_b       = adder_b_1r;
        assign z_s_zero      = z_s_zero_1r;
        assign z_e_overflow1 = z_e_overflow1_1r;
        assign z_e           = z_e_1r;
        assign z_inf_nan     = z_inf_nan_1r;
        assign z_is_zero1    = z_is_zero_1r;
        assign z_is_inf      = z_is_inf_1r | z_e_overflow1;
        assign z_is_nan      = z_is_nan_1r;
        assign z_s_inf       = z_is_inf_1r ? z_s_inf_1r : z_s;
        assign z_s_nan       = z_s_nan_1r;
        assign mode_o        = mode_1r;
   end else begin: gen_no_pipe
       assign adder_a       = adder_a_t;
      assign adder_b       = adder_b_t;
         assign z_s_zero      = z_s_zero_t;
             assign z_e_overflow1 = z_e_overflow1_t;
            assign z_e           = z_e_t;
        assign z_inf_nan     = z_inf_nan_t;
             assign z_is_zero1    = z_is_zero_t;
         assign z_is_inf      = z_is_inf_t | z_e_overflow1;
            assign z_is_nan      = z_is_nan_t;
        assign z_s_inf       = z_is_inf_t ? z_s_inf_t : z_s;
         assign z_s_nan       = z_s_nan_t;
         assign mode_o        = mode;
    end
    endgenerate

    // =========================================================
    // 8. Adder Instantiation
    // =========================================================
    // ne_dw_add_M27 #(.BW_ADDER (BW_ADDER)
    // ) u_adder(
    //     .adder_a      (adder_a    ),
    //     .adder_b      (adder_b    ),
    //     .adder_z      (adder_z    )
    // );
    DW01_add_w30  u_adder(
        .A      (adder_a    ),
        .B      (adder_b    ),
        .CI     (1'b0       ),
        .SUM    (adder_z    ),
        .CO     ()
    );


endmodule