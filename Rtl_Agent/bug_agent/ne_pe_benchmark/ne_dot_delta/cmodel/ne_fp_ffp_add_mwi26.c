#include <assert.h>
#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>


void next_timeframe(void);
void set_inputs(void);
extern const unsigned int bound;

typedef unsigned __CPROVER_bitvector[1] _u1;
typedef unsigned __CPROVER_bitvector[3] _u3;
typedef unsigned __CPROVER_bitvector[10] _u10;
typedef unsigned __CPROVER_bitvector[40] _u40;
typedef unsigned __CPROVER_bitvector[41] _u41;

struct ne_fp_ffp_add_mwi26
{
    _u40 a;
    _u40 b;
    _u3 mode;
    _u41 z;
};

extern struct ne_fp_ffp_add_mwi26 ne_fp_ffp_add_mwi26;

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

uint32_t c_DW01_add_w29(uint32_t adder_a, uint32_t adder_b)
{
    return (adder_a + adder_b) & (uint32_t)MASK(29);
}

uint64_t c_ne_fp_ffp_add_mwi26(uint64_t a, uint64_t b, uint8_t mode)
{
    const int P_SWI = 1;
    const int P_EWI = 10;
    const int P_MWI = 26;
    const int P_BW_STATUS = 3;
    const int P_MWO = (P_MWI + 1);
    const int P_BWA = (P_BW_STATUS + P_SWI + P_EWI + P_MWI);
    const int P_BWZ = (P_BW_STATUS + P_SWI + P_EWI + P_MWO);
    const int P_BIAS_I = 127;
    const int P_BIAS_Z = 127;
    const int P_BIAS_Z_NEG = -127;
    const int P_BW_ESUB = 5;
    const int P_BW_ADDER = 29;
    // --- Step 1: Unpacking (Verilog Section 3) ---
    // Offset calculation: 1 + 10 + 26 = 37
    int offset = P_SWI + P_EWI + P_MWI;

    // Extract raw fields
    uint8_t a_status = (uint8_t)GET_BITS(a, P_BWA - 1, offset);
    uint8_t a_s = (uint8_t)GET_BITS(a, offset - 1, offset - P_SWI);
    uint16_t a_e = (uint16_t)GET_BITS(a, offset - P_SWI - 1, P_MWI);
    uint32_t a_m = (uint32_t)GET_BITS(a, P_MWI - 1, 0);

    uint8_t b_status = (uint8_t)GET_BITS(b, P_BWA - 1, offset);
    uint8_t b_s = (uint8_t)GET_BITS(b, offset - 1, offset - P_SWI);
    uint16_t b_e = (uint16_t)GET_BITS(b, offset - P_SWI - 1, P_MWI);
    uint32_t b_m = (uint32_t)GET_BITS(b, P_MWI - 1, 0);

    // Decode Status
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

    // MSB Extraction
    uint8_t large_m_s = (large_m >> (P_MWI - 1)) & 1;
    uint8_t small_m_s = (small_m >> (P_MWI - 1)) & 1;

    // Exponent Difference
    int16_t e_sub = ae_lt_be ? (be_signed - ae_signed) : (ae_signed - be_signed);

    // Overflow check (Verilog: e_sub > MWI - 2)
    bool align_overflow = (e_sub > (P_MWI - 2)) || (e_sub > (int16_t)P_BIAS_I + 1) || (e_sub < (int16_t)P_BIAS_Z_NEG);
    //  bool align_overflow =(e_sub < (int16_t)(-P_BIAS_I));
    uint8_t e_sub_m = (uint8_t)(e_sub & MASK(P_BW_ESUB)); // Lower 5 bits

    // *** Signed Shift ***
    int32_t small_m_signed = (int32_t)sign_extend(small_m, P_MWI);
    int32_t small_m_shifted = small_m_signed >> e_sub_m;
    uint32_t small_m_align0 = (uint32_t)small_m_shifted & (uint32_t)MASK(P_MWI);

    // Alignment Muxing
    uint32_t small_m_align;
    if (align_overflow)
    {
        small_m_align = small_m_s ? (uint32_t)MASK(P_MWI) : 0;
    }
    else
    {
        small_m_align = small_m_align0;
    }

    // Sticky Bit Logic
    uint32_t align_mask0 = ((uint32_t)MASK(P_MWI) << e_sub_m) & (uint32_t)MASK(P_MWI);
    uint32_t align_mask = align_overflow ? (uint32_t)MASK(P_MWI) : (~align_mask0 & (uint32_t)MASK(P_MWI));
    uint32_t align_norm_bits = align_mask & small_m;
    bool align_norm_bit = (align_norm_bits != 0);

    // *** Significant Construction ***
    // Structure: [MSB_copy] [MSB..LSB] [Guard] [Guard]
    // Total bits used = 1 + MWI + 2 = MWI+3
    uint32_t large_significant =
        ((uint32_t)large_m_s << (P_MWI + 2)) |
        (large_m << 2);

    uint32_t small_significant_raw =
        ((uint32_t)small_m_s << (P_MWI + 2)) |
        (small_m_align << 2) |
        ((uint32_t)align_norm_bit << 1);

    uint32_t small_significant = align_overflow ? 0 : small_significant_raw;

    // --- Step 3 & 4: Integer/Mux (Skipped, HAVE_INT=0) ---
    uint32_t adder_a_t = large_significant;
    uint32_t adder_b_t = small_significant;

    // --- Step 5: Pipeline & Adder (Verilog Section 7 & 8) ---
    uint32_t adder_z = c_DW01_add_w29(adder_a_t, adder_b_t);

    // --- Step 6: Post Processing (Verilog Section 6) ---
    // Verilog: assign z_m = adder_z[MWI+2:2];
    // Extracts bits from MWI+2 down to 2. Width = (MWI+2)-2 + 1 = MWI+1 = MWO
    uint32_t z_m = (adder_z >> 2) & (uint32_t)MASK(P_MWO);

    // Status Logic
    bool z_inf_nan_t = a_is_inf && b_is_inf && (a_s ^ b_s);
    bool z_is_nan_t = a_is_nan || b_is_nan || z_inf_nan_t;
    bool z_is_inf_t = (a_is_inf || b_is_inf) && !z_is_nan_t;

    bool z_is_zero_t = a_is_zero && b_is_zero;
    bool z_is_zero = z_is_zero_t || ((z_m == 0) && !(z_is_inf_t || z_is_nan_t));

    // Exponent Logic
    uint16_t z_e_t = (large_e + 1) & (uint16_t)MASK(P_EWI);

    // Sign Logic
    uint8_t z_s_zero = a_s & b_s;
    uint8_t z_s = z_is_zero ? z_s_zero : (uint8_t)((z_m >> (P_MWO - 1)) & 1);

    uint8_t z_s_inf = a_is_inf ? a_s : b_s;
    uint8_t z_s_nan = a_is_nan ? a_s : (b_is_nan ? b_s : 1);

    // --- Step 7: Output Construction ---

    // Construct Payloads
    uint16_t z_e_max = P_BIAS_Z + 1;

    // *** FIX from previous turn ***
    // Ensure 8-bit truncation before 16-bit cast to avoid sign extension of -127 to 897
    uint16_t z_e_zero_val = (uint16_t)((_u10)P_BIAS_Z_NEG);

    // Normal Result
    uint64_t z_d = ((uint64_t)z_s << (P_EWI + P_MWO)) | ((uint64_t)z_e_t << P_MWO) | z_m;

    // NaN Packet
    uint64_t nan_payload = ((uint64_t)z_s_nan << (P_MWO - 1)) |
                           ((uint64_t)z_s_nan << (P_MWO - 2)) |
                           (1ULL << (P_MWO - 3));
    uint64_t z_nan = ((uint64_t)z_s_nan << (P_EWI + P_MWO)) |
                     ((uint64_t)z_e_max << P_MWO) |
                     nan_payload;

    // Inf Packet
    uint64_t inf_payload = ((uint64_t)z_s_inf << (P_MWO - 1)) |
                           ((uint64_t)z_s_inf << (P_MWO - 2));
    uint64_t z_inf = ((uint64_t)z_s_inf << (P_EWI + P_MWO)) |
                     ((uint64_t)z_e_max << P_MWO) |
                     inf_payload;

    // Zero Packet
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

    // Append Status Bits
    uint64_t final_z = z_o;
    if (P_BW_STATUS > 0)
    {
        uint64_t status = ((uint64_t)z_is_nan_t << 2) | ((uint64_t)z_is_inf_t << 1) | z_is_zero;
        int core_width = P_SWI + P_EWI + P_MWO;
        final_z = (status << core_width) | (z_o & MASK(core_width));
    }

    return final_z;
}

int main()
{
    _u40 din_a;
    _u40 din_b;
    _u3 din_mode;

    _u3 status_a = (_u3)(din_a >> 37);
    _u3 status_b = (_u3)(din_b >> 37);

    __CPROVER_assume(status_a == 0 || status_a == 1 || status_a == 2 || status_a == 4);
    __CPROVER_assume(status_b == 0 || status_b == 1 || status_b == 2 || status_b == 4);
    __CPROVER_assume(din_mode == 1 || din_mode == 2);

    ne_fp_ffp_add_mwi26.a = din_a;
    ne_fp_ffp_add_mwi26.b = din_b;
    ne_fp_ffp_add_mwi26.mode = din_mode;

    set_inputs();
    next_timeframe();

    uint64_t c_res = c_ne_fp_ffp_add_mwi26((uint64_t)din_a, (uint64_t)din_b, (uint8_t)din_mode);
    assert(ne_fp_ffp_add_mwi26.z == (_u41)c_res);

    return 0;
}