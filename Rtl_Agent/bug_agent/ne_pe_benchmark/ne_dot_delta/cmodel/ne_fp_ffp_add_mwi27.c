#include <assert.h>
#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>

void set_inputs(void);
void next_timeframe(void);
extern const unsigned int bound;

typedef unsigned __CPROVER_bitvector[1] _u1;
typedef unsigned __CPROVER_bitvector[3] _u3;
typedef unsigned __CPROVER_bitvector[10] _u10;
typedef unsigned __CPROVER_bitvector[41] _u41;
typedef unsigned __CPROVER_bitvector[42] _u42;

struct ne_fp_ffp_add_mwi27
{
    _u41 a;
    _u41 b;
    _u3 mode;
    _u42 z;
};

extern struct ne_fp_ffp_add_mwi27 ne_fp_ffp_add_mwi27;

#ifndef MASK
#define MASK(w) ((((uint64_t)1) << (w)) - 1)
#endif

#define GET_BITS(val, high, low) (((val) >> (low)) & MASK((high) - (low) + 1))

static int64_t sign_extend(uint64_t val, int width)
{
    if (val & (1ULL << (width - 1)))
    {
        return (int64_t)(val | ~MASK(width));
    }
    return (int64_t)val;
}

uint32_t c_DW01_add_w30(uint32_t adder_a, uint32_t adder_b)
{
    return (adder_a + adder_b) & (uint32_t)MASK(30);
}

uint64_t c_ne_fp_ffp_add_mwi27(uint64_t a, uint64_t b, uint8_t mode)
{
    const int P_SWI = 1;
    const int P_EWI = 10;
    const int P_MWI = 27;
    const int P_BW_STATUS = 3;
    const int P_MWO = (P_MWI + 1);
    const int P_BWA = (P_BW_STATUS + P_SWI + P_EWI + P_MWI);
    const int P_BWZ = (P_BW_STATUS + P_SWI + P_EWI + P_MWO);
    const int P_BIAS_I = 127;
    const int P_BIAS_Z = 127;
    const int P_BIAS_Z_NEG = -127;
    const int P_BW_ESUB = 5;
    const int P_BW_ADDER = 30;
    // --- Step 1: Unpacking (Verilog Section 3) ---
    // Verilog: Extracts status unconditionally based on BW_STATUS > 0
    int offset = P_SWI + P_EWI + P_MWI; // 38

    // Extract raw fields
    uint8_t a_status = (uint8_t)GET_BITS(a, P_BWA - 1, offset);
    uint8_t a_s = (uint8_t)GET_BITS(a, offset - 1, offset - P_SWI);
    uint16_t a_e = (uint16_t)GET_BITS(a, offset - P_SWI - 1, P_MWI);
    uint32_t a_m = (uint32_t)GET_BITS(a, P_MWI - 1, 0);

    uint8_t b_status = (uint8_t)GET_BITS(b, P_BWA - 1, offset);
    uint8_t b_s = (uint8_t)GET_BITS(b, offset - 1, offset - P_SWI);
    uint16_t b_e = (uint16_t)GET_BITS(b, offset - P_SWI - 1, P_MWI);
    uint32_t b_m = (uint32_t)GET_BITS(b, P_MWI - 1, 0);

    // Decode Status (Direct mapping from Verilog)
    bool a_is_nan = (a_status >> 2) & 1;
    bool a_is_inf = (a_status >> 1) & 1;
    bool a_is_zero = (a_status >> 0) & 1;

    bool b_is_nan = (b_status >> 2) & 1;
    bool b_is_inf = (b_status >> 1) & 1;
    bool b_is_zero = (b_status >> 0) & 1;

    // --- Step 2: Alignment (Verilog Section 4) ---
    // Signed comparison of exponents
    int16_t ae_signed = (int16_t)sign_extend(a_e, P_EWI);
    int16_t be_signed = (int16_t)sign_extend(b_e, P_EWI);
    bool ae_lt_be = ae_signed < be_signed;

    // Swap Logic
    uint32_t large_m = ae_lt_be ? b_m : a_m;
    uint32_t small_m = ae_lt_be ? a_m : b_m;
    uint16_t large_e = ae_lt_be ? b_e : a_e;

    // MSB Extraction (Verilog: assign large_m_s = large_m[MWI-1];)
    uint8_t large_m_s = (large_m >> (P_MWI - 1)) & 1;
    uint8_t small_m_s = (small_m >> (P_MWI - 1)) & 1;

    // Exponent Difference
    // Verilog uses simple subtraction of 10-bit values, handled as signed/unsigned mixing in Verilog
    // but here we just take the difference of the signed values calculated above.
    int16_t e_sub = ae_lt_be ? (be_signed - ae_signed) : (ae_signed - be_signed);

    // Overflow check (Verilog: e_sub > MWI - 2)
    bool align_overflow = (e_sub > (P_MWI - 2)) || (e_sub > (int16_t)P_BIAS_I + 1) || (e_sub < (int16_t)P_BIAS_Z_NEG);
    uint8_t e_sub_m = (uint8_t)(e_sub & MASK(P_BW_ESUB)); // Lower 5 bits

    // *** CRITICAL VERILOG MATCH: Signed Shift ***
    // Verilog: assign small_m_align0 = $signed(small_m) >>> e_sub_m;
    // We must treat small_m as a 27-bit signed integer.
    int32_t small_m_signed = (int32_t)sign_extend(small_m, P_MWI);
    // Arithmetic Right Shift (simulates >>> for signed types in C)
    int32_t small_m_shifted = small_m_signed >> e_sub_m;
    uint32_t small_m_align0 = (uint32_t)small_m_shifted & (uint32_t)MASK(P_MWI);

    // Alignment Muxing
    // Verilog: align_overflow ? {(MWI){small_m_s}} : small_m_align0
    uint32_t small_m_align;
    if (align_overflow)
    {
        // If overflow, replicate sign bit (MSB) to all bits
        small_m_align = small_m_s ? (uint32_t)MASK(P_MWI) : 0;
    }
    else
    {
        small_m_align = small_m_align0;
    }

    // Sticky Bit Logic (Norm Bit)
    // Verilog: align_mask0 = {(MWI){1'b1}} << e_sub_m;
    uint32_t align_mask0 = ((uint32_t)MASK(P_MWI) << e_sub_m) & (uint32_t)MASK(P_MWI);
    // Verilog: align_mask = align_overflow ? {(MWI){1'b1}} : ~align_mask0;
    uint32_t align_mask = align_overflow ? (uint32_t)MASK(P_MWI) : (~align_mask0 & (uint32_t)MASK(P_MWI));
    // Verilog: align_norm_bits = align_mask & small_m;
    uint32_t align_norm_bits = align_mask & small_m;
    bool align_norm_bit = (align_norm_bits != 0);

    // *** CRITICAL VERILOG MATCH: Significant Construction ***
    // Verilog: large_significant = {large_m_s, large_m, 2'd0};
    // Structure: [29: MSB of large_m] [28..2: large_m] [1..0: 00]
    // Note: The MSB is effectively duplicated (Bit 29 and Bit 28 (MSB of large_m) are same)
    uint32_t large_significant =
        ((uint32_t)large_m_s << (P_MWI + 2)) |
        (large_m << 2);

    // Verilog: small_significant = {small_m_s, small_m_align, align_norm_bit, 1'b0} ...
    // Structure: [29: MSB of small_m] [28..2: aligned m] [1: sticky] [0: 0]
    uint32_t small_significant_raw =
        ((uint32_t)small_m_s << (P_MWI + 2)) |
        (small_m_align << 2) |
        ((uint32_t)align_norm_bit << 1); // LSB is 0, so just shift sticky to bit 1

    uint32_t small_significant = align_overflow ? 0 : small_significant_raw;

    // --- Step 3 & 4: Integer/Mux (Skipped, HAVE_INT=0) ---
    uint32_t adder_a_t = large_significant;
    uint32_t adder_b_t = small_significant;

    // --- Step 5: Pipeline & Adder (Verilog Section 7 & 8) ---
    // Simulating the functional result of the pipeline + adder
    uint32_t adder_z = c_DW01_add_w30(adder_a_t, adder_b_t);

    // --- Step 6: Post Processing (Verilog Section 6) ---
    // Verilog: assign z_m = adder_z[MWI+2:2];
    uint32_t z_m = (adder_z >> 2) & (uint32_t)MASK(P_MWO);

    // Status Logic
    bool z_inf_nan_t = a_is_inf && b_is_inf && (a_s ^ b_s);
    bool z_is_nan_t = a_is_nan || b_is_nan || z_inf_nan_t;
    bool z_is_inf_t = (a_is_inf || b_is_inf) && !z_is_nan_t;

    // Verilog: z_is_zero = z_is_zero1 | ((~(|z_m)) & (~(z_is_inf | z_is_nan)));
    // z_is_zero1 comes from z_is_zero_t = a_is_zero & b_is_zero
    bool z_is_zero_t = a_is_zero && b_is_zero;
    bool z_is_zero = z_is_zero_t || ((z_m == 0) && !(z_is_inf_t || z_is_nan_t));

    // Exponent Logic
    // Verilog: z_e0_tt = {large_e} + 1;
    // Note: z_e is derived from z_e_t which is z_e0_t
    uint16_t z_e_t = (large_e + 1) & (uint16_t)MASK(P_EWI);

    // Sign Logic
    // Verilog: z_s = z_is_zero ? z_s_zero : z_m[MWO-1];
    uint8_t z_s_zero = a_s & b_s; // z_s_zero_t
    uint8_t z_s = z_is_zero ? z_s_zero : (uint8_t)((z_m >> (P_MWO - 1)) & 1);

    // Special Output Sign Logic
    uint8_t z_s_inf = a_is_inf ? a_s : b_s;
    uint8_t z_s_nan = a_is_nan ? a_s : (b_is_nan ? b_s : 1);

    // --- Step 7: Output Construction ---

    // Construct Payloads
    // Verilog: z_e_max = BIAS_Z + 1 = 127 + 1 = 128
    uint16_t z_e_max = P_BIAS_Z + 1;
    // Verilog: z_e_zero = BIAS_Z_NEG = -127 (as 10-bit signed)
    uint16_t z_e_zero_val = (uint16_t)((_u10)P_BIAS_Z_NEG);

    // Normal Result
    uint64_t z_d = ((uint64_t)z_s << (P_EWI + P_MWO)) | ((uint64_t)z_e_t << P_MWO) | z_m;

    // NaN Packet
    // Verilog: {z_s_nan, z_e_max, {z_s_nan, z_s_nan, 1'b1, 0...}}
    uint64_t nan_payload = ((uint64_t)z_s_nan << (P_MWO - 1)) |
                           ((uint64_t)z_s_nan << (P_MWO - 2)) |
                           (1ULL << (P_MWO - 3));
    uint64_t z_nan = ((uint64_t)z_s_nan << (P_EWI + P_MWO)) |
                     ((uint64_t)z_e_max << P_MWO) |
                     nan_payload;

    // Inf Packet
    // Verilog: {z_s_inf, z_e_max, {z_s_inf, z_s_inf, 0...}}
    uint64_t inf_payload = ((uint64_t)z_s_inf << (P_MWO - 1)) |
                           ((uint64_t)z_s_inf << (P_MWO - 2));
    uint64_t z_inf = ((uint64_t)z_s_inf << (P_EWI + P_MWO)) |
                     ((uint64_t)z_e_max << P_MWO) |
                     inf_payload;

    // Zero Packet
    // Verilog: {z_s, z_e_zero, {z_s, z_s, 0...}}
    uint64_t zero_payload = ((uint64_t)z_s << (P_MWO - 1)) |
                            ((uint64_t)z_s << (P_MWO - 2));
    uint64_t z_zero = ((uint64_t)z_s << (P_EWI + P_MWO)) |
                      ((uint64_t)z_e_zero_val << P_MWO) |
                      zero_payload;

    // Final Mux
    uint64_t z_o;
    if (z_is_nan_t)
        z_o = z_nan;
    else if (z_is_inf_t)
        z_o = z_inf;
    else if (z_is_zero)
        z_o = z_zero;
    else
        z_o = z_d;

    // Append Status Bits (Verilog: assign z = {z_status, z_o})
    uint64_t final_z = z_o;
    if (P_BW_STATUS > 0)
    {
        uint64_t status = ((uint64_t)z_is_nan_t << 2) | ((uint64_t)z_is_inf_t << 1) | z_is_zero;
        int core_width = P_SWI + P_EWI + P_MWO; // 1+10+28 = 39
        final_z = (status << core_width) | (z_o & MASK(core_width));
    }

    return final_z;
}

int main()
{
    _u41 din_a;
    _u41 din_b;
    _u3 din_mode;

    _u3 status_a = (_u3)(din_a >> 38);
    _u3 status_b = (_u3)(din_b >> 38);

    // Assuming valid status encodings (Optional, helps verification speed)
    // 0: Norm, 1: Zero, 2: Inf, 4: NaN
    __CPROVER_assume(status_a == 0 || status_a == 1 || status_a == 2 || status_a == 4);
    __CPROVER_assume(status_b == 0 || status_b == 1 || status_b == 2 || status_b == 4);
    __CPROVER_assume(din_mode == 1 || din_mode == 2);

    ne_fp_ffp_add_mwi27.a = din_a;
    ne_fp_ffp_add_mwi27.b = din_b;
    ne_fp_ffp_add_mwi27.mode = din_mode;

    set_inputs();
    next_timeframe();

    uint64_t c_res = c_ne_fp_ffp_add_mwi27((uint64_t)din_a, (uint64_t)din_b, (uint8_t)din_mode);

    assert(ne_fp_ffp_add_mwi27.z == (_u42)c_res);

    return 0;
}