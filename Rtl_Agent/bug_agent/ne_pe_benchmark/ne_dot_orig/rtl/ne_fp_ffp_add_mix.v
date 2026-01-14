module ne_fp_ffp_add_mix (
   clk,
    a,
    b,
    z,
    mode                //3'b100: tf32, 3'b010: fp8, 3'b001: int8
);
    localparam SWI       = 1;
    localparam EWI       = 10;
    localparam MWI       = 33;
    localparam HAVE_INT  = 1;
    localparam INT_CH    = 1;
    localparam BW_INT_I  = 21;
    localparam BW_STATUS = 3;
    localparam PIPE      =1;
    
    localparam                  SWO          = SWI;
    localparam                  EWO          = EWI;
    localparam                  MWO          = MWI + 1;
    localparam                  BWA          = BW_STATUS+SWI+EWI+MWI;
    localparam                  BWZ          = BW_STATUS+SWO+EWO+MWO;
    localparam                  BW_INT_O     = INT_CH == 1 ? BW_INT_I + 2 : BW_INT_I + 1;
    localparam                  BW_ADDER     = INT_CH == 1 ? (BW_INT_O>(MWI + 3) ? BW_INT_O:(MWI + 3)) : (BW_INT_O*2 + 1) > (MWI + 3) ? (BW_INT_O*2 + 1) : MWI + 3;
    
    localparam [EWO-1:0]        BIAS_Z       = 10'b0001111111;
    localparam                  BIAS_I       = 10'b0001111111; 
    localparam signed [EWO-1:0] BIAS_Z_NEG   = -BIAS_Z;
    localparam                  BW_ESUB      = 6;
    input clk;  
   // input                   clkg_int8fp8fp16fp4 ;
  //  input                   clkg_fp8fp16fp4     ;
    input  [BWA-1:0]        a;
    input  [BWA-1:0]        b;
    output [BWZ-1:0]        z;
    input  [3:0]            mode;

    // [FIX] Move Status definitions to top level to avoid implicit wire errors
    wire [BW_STATUS-1:0]    a_status;
    wire [BW_STATUS-1:0]    b_status;

    wire                    a_s             ;
    wire [EWI-1:0]          a_e             ;
    wire [MWI-1:0]          a_m             ;
    wire                    a_e_is_zero     ;
    wire                    a_m_is_zero     ;
    wire                    a_e_is_max      ;
    wire                    a_is_zero       ;
    wire                    a_is_inf        ;
    wire                    a_is_nan        ;
    wire                    b_s             ;
    wire [EWI-1:0]          b_e             ;
    wire [MWI-1:0]          b_m             ;
    wire                    b_e_is_zero     ;
    wire                    b_m_is_zero     ;
    wire                    b_e_is_max      ;
    wire                    b_is_zero       ;
    wire                    b_is_inf        ;
    wire                    b_is_nan        ;
    wire                    ae_lt_be        ;
    wire [MWI-1:0]          large_m         ;
    wire [MWI-1:0]          small_m         ;
    wire [EWI-1:0]          large_e         ;
    wire [EWI-1:0]          small_e         ;
    wire                    large_m_s       ;
    wire                    small_m_s       ;
    wire [EWI:0]            e_sub_t         ;
    wire [EWI-1:0]          e_sub           ;
    wire [BW_ESUB-1:0]      e_sub_m         ;
    wire                    align_overflow  ;
    wire signed [MWI-1:0]   small_m_align0  ;
    wire [MWI-1:0]          small_m_align   ;
    wire [MWI-1:0]          align_mask0     ;
    wire [MWI-1:0]          align_mask      ;
    wire [MWI-1:0]          align_norm_bits ;
    wire                    align_norm_bit  ;
    wire [MWI+2:0]          large_significant;
    wire [MWI+2:0]          small_significant;
    wire [EWO-1:0]          z_e             ;
    wire [MWO-1:0]          z_m             ;
    wire                    e_overflow_pos  ;
    wire                    e_overflow_neg  ;
    wire                    z_e_overflow1_t ;
    wire                    z_e_overflow1   ;
    wire                    z_s             ;
    wire [BW_INT_I-1:0]     int_a0          ;
    wire [BW_INT_I-1:0]     int_b0          ;
    wire [BW_INT_I-1:0]     int_a1          ;
    wire [BW_INT_I-1:0]     int_b1          ;
    wire [BW_INT_O-1:0]     int_z0          ;
    wire [BW_INT_O-1:0]     int_z1          ;
    wire [BW_ADDER-1:0]     adder_a         ;
    wire [BW_ADDER-1:0]     adder_b         ;
    wire [BW_ADDER-1:0]     adder_z         ;
    wire                    z_inf_nan       ;
    wire                    z_s_inf         ;
    wire                    z_s_nan         ;
    wire                    z_is_zero       ;
    wire                    z_is_zero1      ;
    wire                    z_is_inf        ;
    wire                    z_is_nan        ;
    wire [SWO+EWO+MWO-1:0]  z_zero          ;
    wire [SWO+EWO+MWO-1:0]  z_inf           ;
    wire [SWO+EWO+MWO-1:0]  z_nan           ;
    wire [SWO+EWO+MWO-1:0]  z_d             ;
    wire [SWO+EWO+MWO-1:0]  z_o             ;
    wire [BW_ADDER-1:0]     adder_a_t       ;
    wire [BW_ADDER-1:0]     adder_b_t       ;
    wire                    z_s_zero_t      ;
    wire [EWO:0]            z_e0_tt         ;
    wire [EWO-1:0]          z_e0_t          ;
    wire [EWO-1:0]          z_e_t           ;
    wire                    z_inf_nan_t     ;
    wire                    z_is_zero_t     ;
    wire                    z_is_inf_t      ;
    wire                    z_is_nan_t      ;
    wire                    z_s_inf_t       ;
    wire                    z_s_nan_t       ;
    wire [3:0]              mode_o          ;
    wire                    z_s_zero        ;
    
    reg  [BW_ADDER-1:0]     adder_a_1r      ;
    reg  [BW_ADDER-1:0]     adder_b_1r      ;
    reg                     z_s_zero_1r     ;
    reg                     z_e_overflow1_1r;
    reg  [EWO-1:0]          z_e_1r          ;
    reg                     z_inf_nan_1r    ;
    reg                     z_is_zero_1r    ;
    reg                     z_is_inf_1r     ;
    reg                     z_is_nan_1r     ;
    reg                     z_s_inf_1r      ;
    reg                     z_s_nan_1r      ;
    reg  [3:0]              mode_1r         ;

    // =========================================================
    // 3. Unpacking Logic (Fixed: removed inner wire defs)
    // =========================================================
    generate if(BW_STATUS > 0) begin: gen_unpack_with_status
        assign {a_status, a_s, a_e, a_m}  = ~mode[0] ? a : {BWA{1'b0}};
        assign {b_status, b_s, b_e, b_m}  = ~mode[0] ? b : {BWA{1'b0}};
        assign a_is_nan  = a_status[2];
        assign a_is_inf  = a_status[1];
        assign a_is_zero = a_status[0];
        assign b_is_nan  = b_status[2];
        assign b_is_inf  = b_status[1];
        assign b_is_zero = b_status[0];
    end else begin: gen_unpack_without_status
        // Assign default 0 to unused status wires to avoid floating
        assign a_status = {BW_STATUS{1'b0}};
        assign b_status = {BW_STATUS{1'b0}};
        
        assign {a_s, a_e, a_m}  = mode[2] ? a : {BWA{1'b0}};
        assign {b_s, b_e, b_m}  = mode[2] ? b : {BWA{1'b0}};
        assign a_e_is_zero = $signed(a_e) == -BIAS_I;
        assign a_e_is_max = a_e == BIAS_I + 1;
        assign a_m_is_zero = ~(|a_m);
        assign a_is_zero = a_e_is_zero & a_m_is_zero;
        assign a_is_inf = a_e_is_max & a_m_is_zero;
        assign a_is_nan = a_e_is_max & (~a_m_is_zero);

        assign b_e_is_zero = $signed(b_e) == -BIAS_I;
        assign b_e_is_max = b_e == BIAS_I + 1;
        assign b_m_is_zero = ~(|b_m);
        assign b_is_zero = b_e_is_zero & b_m_is_zero;
        assign b_is_inf = b_e_is_max & b_m_is_zero;
        assign b_is_nan = b_e_is_max & (~b_m_is_zero);
    end
    endgenerate

    // =========================================================
    // 4. Alignment Logic
    // =========================================================
    assign ae_lt_be             = $signed(a_e) < $signed(b_e);
    assign large_m              = ae_lt_be ? b_m : a_m;
    assign small_m              = ae_lt_be ? a_m : b_m;
    assign large_e              = ae_lt_be ? b_e : a_e;
    assign small_e              = ae_lt_be ? a_e : b_e;
    assign large_m_s            = large_m[MWI-1];
    assign small_m_s            = small_m[MWI-1];
    assign e_sub_t              = ae_lt_be ? {b_e[EWI-1], b_e} - {a_e[EWI-1], a_e} : {a_e[EWI-1], a_e} - {b_e[EWI-1], b_e};
    assign e_sub                = e_sub_t[EWI-1:0];
       wire [BW_STATUS-1:0] z_status;
    wire [9:0] sfr_overflow     = mode[3] ? 10'd24 : 10'd31;
    assign align_overflow       = (e_sub > sfr_overflow);
    // || $signed(e_sub) > BIAS_I + 1 || $signed(e_sub) < -BIAS_I;
    
    assign e_sub_m              = e_sub[BW_ESUB-1:0];
    assign small_m_align0       = $signed(small_m) >>> e_sub_m;
    assign align_mask0          = {(MWI){1'b1}} << e_sub_m;
    assign small_m_align        = align_overflow ? {(MWI){small_m_s}} : small_m_align0;
    assign align_mask           = align_overflow ? {(MWI){1'b1}} : ~align_mask0;
    assign align_norm_bits      = align_mask & small_m;
    assign align_norm_bit       = |align_norm_bits;
    assign large_significant    = {large_m_s, large_m, 2'd0};
    assign small_significant    = {small_m_s, small_m_align, align_norm_bit, 1'b0} & {(MWI+3){~align_overflow}};
    
    assign z_m                  = adder_z[MWI+2:2];
    assign z_is_zero            = z_is_zero1 | ((~(|z_m)) & (~(z_is_inf | z_is_nan)) );
    assign z_e0_tt              = {large_e[EWI-1], large_e} + {{(EWI){1'b0}}, 1'b1};
    assign z_e0_t               = z_e0_tt[EWO-1:0];
    assign e_overflow_pos       = ~z_e0_t[EWI-1] & z_e0_t[EWI-2];
    assign e_overflow_neg       = z_e0_t[EWI-1] & (~z_e0_t[EWI-2]);
    assign z_e_t                = z_e0_t;
    assign z_s_zero_t           = a_s & b_s;
    assign z_s                  = z_is_zero ? z_s_zero : z_m[MWO-1];

    // =========================================================
    // 5. Integer Path & Adder Mux (FIXED Zero Replication)
    // =========================================================
    generate if (HAVE_INT == 1) begin: int_proc
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
        
        if (INT_CH == 2) begin: adder_i_ch2
            assign adder_a_t = mode[2] ? {{(BW_ADDER-(MWI+3)){1'b0}}, large_significant} :
                               mode[0] ? {{(BW_ADDER-BW_INT_I*2-3){1'b0}}, 
                                          int_a1[BW_INT_I-1], int_a1, 1'b0, int_a0[BW_INT_I-1], int_a0} : {(BW_ADDER){1'b0}};
            assign adder_b_t = mode[2] ? {{(BW_ADDER-(MWI+3)){1'b0}}, small_significant} :
                               mode[0] ? {{(BW_ADDER-BW_INT_I*2-3){1'b0}},
                                          int_b1[BW_INT_I-1], int_b1, 1'b0, int_b0[BW_INT_I-1], int_b0} : {(BW_ADDER){1'b0}};
        end else begin: adder_i_ch1
            // [FIX] Removed explicit replication of 0 when count is 0
            // Verilog automatically zero-extends large_significant
            assign adder_a_t =  mode[0] ? {{(BW_ADDER-BW_INT_I){int_a0[BW_INT_I-1]}}, int_a0} : 
                                large_significant;
            
            assign adder_b_t = mode[0] ? {{(BW_ADDER-BW_INT_I){int_b0[BW_INT_I-1]}}, int_b0} : 
                                small_significant;
        end
    end else begin: no_int_proc
        // [FIX] Removed explicit replication
        assign adder_a_t = large_significant;
        assign adder_b_t = small_significant;
    end
    endgenerate

    // =========================================================
    // 6. Post Processing Logic
    // =========================================================
    assign z_inf_nan_t            = a_is_inf & b_is_inf & (a_s ^ b_s);
    assign z_is_zero_t            = a_is_zero & b_is_zero;
    assign z_e_overflow1_t        = 1'd0;
    assign z_is_inf_t             = ((a_is_inf | b_is_inf) & (~z_is_nan_t));
    assign z_is_nan_t             = a_is_nan | b_is_nan | z_inf_nan_t;
    assign z_s_inf_t              = a_is_inf ? a_s : b_s;
    assign z_s_nan_t              = a_is_nan ? a_s : b_is_nan ? b_s : 1'b1;

    // Output Generation
    generate if(BW_STATUS > 0) begin: gen_out_with_status
     
        assign z_status = {z_is_nan, z_is_inf, z_is_zero};
        assign z = {z_status, z_o};
    end else begin: gen_out_without_status
        assign z = z_o;
    end
    endgenerate

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
         //    always@(posedge clkg_int8fp8fp16fp4) begin
            adder_a_1r       <= adder_a_t;
            adder_b_1r       <= adder_b_t;
            mode_1r          <= mode;
       // end 
     //   always@(posedge clkg_fp8fp16fp4) begin
      //  always@(posedge clk) begin
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
        
        // [FIX] Corrected logic from z_s_inf_t to z_is_inf_t
        assign z_s_inf       = z_is_inf_t ? z_s_inf_t : z_s;
        assign z_s_nan       = z_s_nan_t;
        assign mode_o        = mode;
    end
    endgenerate

    DW01_add_w36 u_adder(
        .A      (adder_a    ),
        .B      (adder_b    ),
        .CI     (1'b0       ),
        .SUM    (adder_z    ),
        .CO     ()
    );

endmodule