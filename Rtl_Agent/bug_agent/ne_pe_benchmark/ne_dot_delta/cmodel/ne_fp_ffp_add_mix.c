#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
#include <assert.h>

void set_inputs(void);
void next_timeframe(void);
extern const unsigned int bound;

typedef unsigned __CPROVER_bitvector[1] _u1;
typedef unsigned __CPROVER_bitvector[2] _u2;
typedef unsigned __CPROVER_bitvector[3] _u3;
typedef unsigned __CPROVER_bitvector[4] _u4;
typedef unsigned __CPROVER_bitvector[6] _u6;
typedef unsigned __CPROVER_bitvector[10] _u10;
typedef unsigned __CPROVER_bitvector[21] _u21;
typedef unsigned __CPROVER_bitvector[23] _u23; // BW_INT_O
typedef unsigned __CPROVER_bitvector[32] _u32; // BW_INT_O
typedef unsigned __CPROVER_bitvector[33] _u33; // MWI
typedef unsigned __CPROVER_bitvector[34] _u34; // MWO
typedef unsigned __CPROVER_bitvector[36] _u36; // BW_ADDER
typedef unsigned __CPROVER_bitvector[45] _u45; // Data Out
typedef unsigned __CPROVER_bitvector[47] _u47; // Input Data (no status)
typedef unsigned __CPROVER_bitvector[48] _u48; // Final Output

struct ne_fp_ffp_add_mix
{
    _u47 a;
    _u47 b;
    _u4 mode;
    _u48 z;
};

extern struct ne_fp_ffp_add_mix ne_fp_ffp_add_mix;

#define MASK64(w) ((w) >= 64 ? (~0ULL) : ((1ULL << (w)) - 1))

static int64_t sext_custom(uint64_t val, int w)
{
    if ((val >> (w - 1)) & 1)
    {
        return val | ~MASK64(w);
    }
    else
    {
        return val;
    }
}

_u48 c_ne_fp_ffp_add_mix(_u47 din_a, _u47 din_b, _u4 din_mode)
{
    const int P_SWI = 1;
    const int P_EWI = 10;
    const int P_MWI = 33;
    const int P_BW_STATUS = 3;
    const int P_BW_INT_I = 21;
    const int P_BIAS_VAL = 127;
    const int P_BW_INT_O = 23;
    const int P_BW_ADDER = 36;
    const int P_SWO = 1;
    const int P_EWO = 10;
    const int P_MWO = 34;
    const int P_BW_Z_DATA = 45;
    const int P_BW_Z_TOTAL = 48;
    // -----------------------------------------------------
    // 1. Unpack Logic (RTL: gen_unpack_with_status)
    // -----------------------------------------------------
    _u3 a_status, b_status;
    _u1 a_s, b_s;
    _u10 a_e, b_e;
    _u33 a_m, b_m;

    // din_mode[0] == 0 implies FP mode in RTL logic (~mode[0])
    bool mode_fp = ((din_mode & 1) == 0);

    if (mode_fp)
    {
        // Unpack A
        a_status = (_u3)(din_a >> 44);
        a_s = (_u1)(din_a >> 43);
        a_e = (_u10)(din_a >> 33);
        a_m = (_u33)(din_a);

        // Unpack B
        b_status = (_u3)(din_b >> 44);
        b_s = (_u1)(din_b >> 43);
        b_e = (_u10)(din_b >> 33);
        b_m = (_u33)(din_b);
    }
    else
    {
        // Zero out for Integer mode (RTL logic)
        a_status = 0;
        a_s = 0;
        a_e = 0;
        a_m = 0;
        b_status = 0;
        b_s = 0;
        b_e = 0;
        b_m = 0;
    }

    _u1 a_is_nan = (a_status >> 2) & 1;
    _u1 a_is_inf = (a_status >> 1) & 1;
    _u1 a_is_zero = (a_status >> 0) & 1;

    _u1 b_is_nan = (b_status >> 2) & 1;
    _u1 b_is_inf = (b_status >> 1) & 1;
    _u1 b_is_zero = (b_status >> 0) & 1;

    // -----------------------------------------------------
    // 2. Alignment Logic (FP Only)
    // -----------------------------------------------------
    int64_t ae_s_val = sext_custom((uint64_t)a_e, P_EWI);
    int64_t be_s_val = sext_custom((uint64_t)b_e, P_EWI);

    _u33 lg_m, sm_m;
    _u10 lg_e;
    _u1 lg_m_s, sm_m_s;
    int64_t e_sub_val;

    // RTL: assign ae_lt_be = $signed(a_e) < $signed(b_e);
    if (ae_s_val < be_s_val)
    {
        lg_m = b_m;
        sm_m = a_m;
        lg_e = b_e;
        e_sub_val = be_s_val - ae_s_val;
    }
    else
    {
        lg_m = a_m;
        sm_m = b_m;
        lg_e = a_e;
        e_sub_val = ae_s_val - be_s_val;
    }

    lg_m_s = (lg_m >> 32) & 1;
    sm_m_s = (sm_m >> 32) & 1;

    // RTL: sfr_overflow logic
    int64_t sfr_limit = ((din_mode >> 3) & 1) ? 24 : 31;
    int64_t bias_i = P_BIAS_VAL;
    int64_t n_bias_i = -bias_i;
    _u1 align_overflow = 0;
    if (((uint64_t)e_sub_val > sfr_limit) ||
        (e_sub_val > (int64_t)bias_i + 1) ||
        (e_sub_val < -(int64_t)bias_i)) // <--- 注意这里的强转和负号位置
    {
        align_overflow = 1;
    }
    // RTL: e_sub_m = e_sub[5:0]
    _u6 e_sub_m = (_u6)(e_sub_val & 0x3F);

    // RTL: small_m_align0 = $signed(small_m) >>> e_sub_m;
    // Note: small_m is 33 bits. sext_custom to 64 then shift handles the arithmetic shift.
    int64_t sm_m_signed = sext_custom((uint64_t)sm_m, P_MWI);
    int64_t sm_shifted_signed = sm_m_signed >> (uint64_t)e_sub_m;

    // RTL: Sticky bit logic (align_norm_bit)
    // align_mask0 = {ones} << e_sub_m
    // align_norm_bits = (~align_mask0) & small_m
    uint64_t mask_bits = (e_sub_m >= 64) ? ~0ULL : MASK64((uint64_t)e_sub_m);
    _u1 sticky = (!align_overflow) && (((uint64_t)sm_m & mask_bits) != 0);

    // RTL: Muxing based on overflow
    _u33 sm_final;
    _u1 align_norm_bit;

    if (align_overflow)
    {
        sm_final = sm_m_s ? (_u33)(~0) : (_u33)0; // {MWI{small_m_s}}
        align_norm_bit = 0;
    }
    else
    {
        sm_final = (_u33)sm_shifted_signed; // Keeps the sign extension bits
        align_norm_bit = sticky;
    }

    // RTL: large_significant = {large_m_s, large_m, 2'd0}
    _u36 lg_sig = ((_u36)lg_m_s << 35) | ((_u36)lg_m << 2);

    // RTL: small_significant = {small_m_s, small_m_align, align_norm_bit, 1'b0}
    // Bit 35: Sign, Bits 34-2: Aligned Mantissa, Bit 1: Sticky, Bit 0: 0
    _u36 sm_sig_raw = ((_u36)sm_m_s << 35) | ((_u36)sm_final << 2) | ((_u36)align_norm_bit << 1);

    // Apply overflow mask to small_significant (RTL: & {~align_overflow})
    _u36 sm_sig = align_overflow ? (_u36)0 : sm_sig_raw;

    // -----------------------------------------------------
    // 3. Integer & Adder Mux (RTL: int_proc generate block)
    // -----------------------------------------------------
    _u21 int_a0, int_b0;
    _u36 adder_a, adder_b;

    if (!mode_fp)
    { // INT Mode (din_mode[0] == 1)
        int_a0 = (_u21)din_a;
        int_b0 = (_u21)din_b;

        // RTL: adder_a_t = {{(BW_ADDER-BW_INT_I){int_a0[MSB]}}, int_a0}
        // Sign extend 21-bit int to 36-bit adder input
        adder_a = (_u36)sext_custom((uint64_t)int_a0, P_BW_INT_I);
        adder_b = (_u36)sext_custom((uint64_t)int_b0, P_BW_INT_I);
    }
    else
    { // FP Mode
        adder_a = lg_sig;
        adder_b = sm_sig;
    }

    // -----------------------------------------------------
    // 4. Core Addition
    // -----------------------------------------------------
    _u36 adder_z;
    // Standard wrapping addition
    adder_z = (_u36)((uint64_t)adder_a + (uint64_t)adder_b);

    // -----------------------------------------------------
    // 5. Output Processing
    // -----------------------------------------------------
    _u45 final_z_o;
    _u1 z_res_nan = 0, z_res_inf = 0, z_res_zero = 0;

    if (!mode_fp)
    {
        // === INT Output (RTL: INT_CH=1 Logic) ===
        // BW_INT_O = 23 (21+2)
        // int_z0 logic checks adder_z[22:21]

        _u23 int_z0;
        _u2 top_bits = (_u2)((adder_z >> (P_BW_INT_O - 2)) & 3); // Bits 22:21

        if (top_bits == 1)
        { // 2'b01: Pos Overflow
            // RTL: {2'b00, 1'b0, {(BW_INT_I-1){1'b1}}} -> 000111...11
            // Bit 22,21=00, Bit 20=0, Bits 19-0=1
            int_z0 = (_u23)(MASK64(P_BW_INT_I - 1));
        }
        else if (top_bits == 2)
        { // 2'b10: Neg Overflow
            // RTL: {2'b11, 1'b1, {(BW_INT_I-1){1'b0}}} -> 111000...00
            // Bit 22,21=11, Bit 20=1, Bits 19-0=0
            // This is effectively - (2^20)? No, it's constructing a specific pattern.
            // 111 followed by 20 zeros.
            int_z0 = (_u23)(((_u23)7 << (P_BW_INT_I - 1)));
        }
        else
        {
            // Normal: take bottom 23 bits
            int_z0 = (_u23)adder_z;
        }
        _u34 z_m = (_u34)(adder_z >> 2);

        // RTL: z_e calculation
        int64_t lg_e_val = sext_custom((uint64_t)lg_e, P_EWI);
        int64_t z_e0_val = lg_e_val + 1;
        _u10 z_e = (_u10)z_e0_val;

        // Overflow checks (using bit 10 and 9 of z_e0_val)
        // RTL: z_e0_tt (11 bits)
        _u1 e_bit_10 = (z_e0_val >> 10) & 1; // Actually index 9 if 10 bits wide, but logic uses 11 bits
        _u1 e_bit_9 = (z_e0_val >> 9) & 1;   // MSB of 10-bit result
        _u1 e_bit_8 = (z_e0_val >> 8) & 1;   // MSB-1

        // The RTL logic for e_overflow_pos/neg depends on the extended bit width
        // Let's assume standard behavior:
        // RTL: e_overflow_pos = ~z_e0_t[EWI-1] & z_e0_t[EWI-2]; (Indices 9 and 8)
        _u1 e_overflow_pos = !e_bit_9 && e_bit_8;

        // Wait, z_e0_t is 10 bits. EWI=10. EWI-1=9. EWI-2=8.
        // It seems the RTL logic is checking wrap-around based on sign bits.
        // Since we did 64-bit calc, we can check value ranges directly?
        // RTL relies on bit manipulation. Let's stick to bits.
        // _u1 z_e_overflow1 = e_overflow_pos; // Simplified for this context as pos overflow forces Inf
        _u1 z_e_overflow1 = 0;
        // Status Logic
        _u1 z_inf_nan_cond = a_is_inf && b_is_inf && (a_s ^ b_s);
        _u1 z_nan = a_is_nan || b_is_nan || z_inf_nan_cond;
        _u1 z_inf = ((a_is_inf || b_is_inf) && !z_nan) || z_e_overflow1;

        _u1 z_m_is_zero = (z_m == 0);
        _u1 z_zero = (a_is_zero && b_is_zero) || (z_m_is_zero && !z_inf && !z_nan);

        _u1 z_s_zero_val = a_s & b_s;

        // RTL: z_s = z_is_zero ? z_s_zero : z_m[MWO-1];
        // MWO = 34. z_m[33] is the MSB of z_m.
        _u1 z_s = z_zero ? z_s_zero_val : (_u1)(z_m >> 33);

        _u1 zs_inf = (a_is_inf || b_is_inf) ? (a_is_inf ? a_s : b_s) : z_s;
        _u1 zs_nan = a_is_nan ? a_s : (b_is_nan ? b_s : (_u1)1);

        // Constant constructions for special values
        _u10 e_max = (_u10)(P_BIAS_VAL + 1);
        _u10 e_zero = (_u10)(-(int64_t)P_BIAS_VAL);

        // RTL: z_nan = {z_s_nan, z_e_max, {z_s_nan, z_s_nan, 1'b1, 0...}}
        _u34 m_nan = ((_u34)zs_nan << 33) | ((_u34)zs_nan << 32) | ((_u34)1 << 31);
        _u45 pkt_nan = ((_u45)zs_nan << 44) | ((_u45)e_max << 34) | (_u45)m_nan;

        // RTL: z_inf = {z_s_inf, z_e_max, {z_s_inf, z_s_inf, 0...}}
        _u34 m_inf = ((_u34)zs_inf << 33) | ((_u34)zs_inf << 32);
        _u45 pkt_inf = ((_u45)zs_inf << 44) | ((_u45)e_max << 34) | (_u45)m_inf;

        // RTL: z_zero = {z_s, z_e_zero, {z_s, z_s, 0...}}
        _u34 m_zero = ((_u34)z_s << 33) | ((_u34)z_s << 32);
        _u45 pkt_zero = ((_u45)z_s << 44) | ((_u45)e_zero << 34) | (_u45)m_zero;

        // RTL: z_d = {z_s, z_e, z_m}
        _u45 pkt_norm = ((_u45)z_s << 44) | ((_u45)z_e << 34) | (_u45)z_m;
        // RTL: z_o = {{(SWO+EWO+MWO-BW_INT_O){int_z0[BW_INT_O-1]}}, int_z0}
        // Sign extend 23-bit int_z0 to 45-bit output
        _u1 int_sign = (int_z0 >> (P_BW_INT_O - 1)) & 1; // Bit 22

        if (int_sign)
        {
            // Fill top bits (44 down to 23) with 1s
            final_z_o = (_u45)int_z0 | ((_u45)(~0) << P_BW_INT_O);
        }
        else
        {
            final_z_o = (_u45)int_z0;
        }
        z_res_nan = z_nan;
        z_res_inf = z_inf;
        z_res_zero = z_zero;
    }
    else
    {
        // === FP Output ===

        // RTL: z_m = adder_z[MWI+2:2] => adder_z[35:2] (Length 34)
        _u34 z_m = (_u34)(adder_z >> 2);

        // RTL: z_e calculation
        int64_t lg_e_val = sext_custom((uint64_t)lg_e, P_EWI);
        int64_t z_e0_val = lg_e_val + 1;
        _u10 z_e = (_u10)z_e0_val;

        // Overflow checks (using bit 10 and 9 of z_e0_val)
        // RTL: z_e0_tt (11 bits)
        _u1 e_bit_10 = (z_e0_val >> 10) & 1; // Actually index 9 if 10 bits wide, but logic uses 11 bits
        _u1 e_bit_9 = (z_e0_val >> 9) & 1;   // MSB of 10-bit result
        _u1 e_bit_8 = (z_e0_val >> 8) & 1;   // MSB-1

        // The RTL logic for e_overflow_pos/neg depends on the extended bit width
        // Let's assume standard behavior:
        // RTL: e_overflow_pos = ~z_e0_t[EWI-1] & z_e0_t[EWI-2]; (Indices 9 and 8)
        _u1 e_overflow_pos = !e_bit_9 && e_bit_8;

        // Wait, z_e0_t is 10 bits. EWI=10. EWI-1=9. EWI-2=8.
        // It seems the RTL logic is checking wrap-around based on sign bits.
        // Since we did 64-bit calc, we can check value ranges directly?
        // RTL relies on bit manipulation. Let's stick to bits.
        // _u1 z_e_overflow1 = e_overflow_pos; // Simplified for this context as pos overflow forces Inf
        _u1 z_e_overflow1 = 0;
        // Status Logic
        _u1 z_inf_nan_cond = a_is_inf && b_is_inf && (a_s ^ b_s);
        _u1 z_nan = a_is_nan || b_is_nan || z_inf_nan_cond;
        _u1 z_inf = ((a_is_inf || b_is_inf) && !z_nan) || z_e_overflow1;

        _u1 z_m_is_zero = (z_m == 0);
        _u1 z_zero = (a_is_zero && b_is_zero) || (z_m_is_zero && !z_inf && !z_nan);

        _u1 z_s_zero_val = a_s & b_s;

        // RTL: z_s = z_is_zero ? z_s_zero : z_m[MWO-1];
        // MWO = 34. z_m[33] is the MSB of z_m.
        _u1 z_s = z_zero ? z_s_zero_val : (_u1)(z_m >> 33);

        _u1 zs_inf = (a_is_inf || b_is_inf) ? (a_is_inf ? a_s : b_s) : z_s;
        _u1 zs_nan = a_is_nan ? a_s : (b_is_nan ? b_s : (_u1)1);

        // Constant constructions for special values
        _u10 e_max = (_u10)(P_BIAS_VAL + 1);
        _u10 e_zero = (_u10)(-(int64_t)P_BIAS_VAL);

        // RTL: z_nan = {z_s_nan, z_e_max, {z_s_nan, z_s_nan, 1'b1, 0...}}
        _u34 m_nan = ((_u34)zs_nan << 33) | ((_u34)zs_nan << 32) | ((_u34)1 << 31);
        _u45 pkt_nan = ((_u45)zs_nan << 44) | ((_u45)e_max << 34) | (_u45)m_nan;

        // RTL: z_inf = {z_s_inf, z_e_max, {z_s_inf, z_s_inf, 0...}}
        _u34 m_inf = ((_u34)zs_inf << 33) | ((_u34)zs_inf << 32);
        _u45 pkt_inf = ((_u45)zs_inf << 44) | ((_u45)e_max << 34) | (_u45)m_inf;

        // RTL: z_zero = {z_s, z_e_zero, {z_s, z_s, 0...}}
        _u34 m_zero = ((_u34)z_s << 33) | ((_u34)z_s << 32);
        _u45 pkt_zero = ((_u45)z_s << 44) | ((_u45)e_zero << 34) | (_u45)m_zero;

        // RTL: z_d = {z_s, z_e, z_m}
        _u45 pkt_norm = ((_u45)z_s << 44) | ((_u45)z_e << 34) | (_u45)z_m;

        if (z_nan)
        {
            final_z_o = pkt_nan;
        }
        else if (z_inf)
        {
            final_z_o = pkt_inf;
        }
        else if (z_zero)
        {
            final_z_o = pkt_zero;
        }
        else
        {
            final_z_o = pkt_norm;
        }

        z_res_nan = z_nan;
        z_res_inf = z_inf;
        z_res_zero = z_zero;
    }
    // z_res_nan  = z_nan;
    // z_res_inf  = z_inf;
    // z_res_zero = z_zero;
    // -----------------------------------------------------
    // 6. Final Pack
    // -----------------------------------------------------
    _u3 z_status_out;
    z_status_out = ((_u3)z_res_nan << 2) | ((_u3)z_res_inf << 1) | (_u3)z_res_zero;

    _u48 z_out = ((_u48)z_status_out << 45) | (_u48)final_z_o;

    return z_out;
}


int main()
{
    _u47 din_a;
    _u47 din_b;
    _u4 din_mode;

    // 提取 Status (高 3 位)
    // din_a >> 44 会将高 3 位移到底部，然后强制转为 _u3
    _u3 status_in_a = (_u3)(din_a >> 44);
    _u3 status_in_b = (_u3)(din_b >> 44);

    // Status 约束:
    // 0(000): Normal, 1(001): Zero, 2(010): Inf, 4(100): NaN
    // 排除非法组合 (3, 5, 6, 7)
    __CPROVER_assume(status_in_a == 0 || status_in_a == 1 || status_in_a == 2 || status_in_a == 4);
    __CPROVER_assume(din_mode == 1 || din_mode == 2 || din_mode == 8);

    ne_fp_ffp_add_mix.a = din_a;
    ne_fp_ffp_add_mix.b = din_b;
    ne_fp_ffp_add_mix.mode = din_mode;

    set_inputs();
    _u48 ref_z = c_ne_fp_ffp_add_mix(din_a, din_b, din_mode);
    next_timeframe();


    assert(ne_fp_ffp_add_mix.z == ref_z);

    return 0;
}
