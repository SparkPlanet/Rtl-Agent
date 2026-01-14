#include <stdio.h>
#include <assert.h>
#include <stdint.h>
#include <stdbool.h>
#include "common.h"

void next_timeframe(void);
void set_inputs(void);
extern const unsigned int bound;

struct ne_fp_ffp_norm_mw27
{
    _u41 a;
    _u41 z;
    _u3 mode;
};

extern struct ne_fp_ffp_norm_mw27 ne_fp_ffp_norm_mw27;

void c_ne_fp_sfl_blk_w27s5(
    _u27 a,
    _u5 s,
    _u27 *z)
{
    *z = 0;
    *z = a << s;
}

void c_DW_lsd_w26(_u26 a, _u26 *dec, _u5 *enc)
{
    _u5 i;
    for (i = 25; i > 0; i--)
    {
        if (EXTRACT_BITS(a, i, i) != EXTRACT_BITS(a, i - 1, i - 1))
        {
            *enc = 25 - i;
            *dec = 1ULL << i;
            break;
        }
    }
    if (i == 0)
    {
        *enc = 25;
        *dec = 0x1;
    }
}

uint64_t c_ne_fp_ffp_norm_mw27(uint64_t a, uint64_t mode)
{
    const int SW = 1;
    const int EW = 10;
    const int MW = 27;
    const int BW_STATUS = 3;
    const int BW = (BW_STATUS + SW + EW + MW); // 30
    const int BIAS = 511;
    uint64_t a_status = 0;
    uint64_t a_s = 0;
    uint64_t a_e = 0;
    uint64_t a_m = 0;

    if (BW_STATUS > 0)
    {
        if ((mode & 1) == 0)
        { // ~mode[0] -> tf32/fp8
            int offset = 0;
            a_m = GET_BITS(a, MW - 1, 0);
            offset += MW;
            a_e = GET_BITS(a, offset + EW - 1, offset);
            offset += EW;
            a_s = GET_BITS(a, offset + SW - 1, offset);
            offset += SW;
            a_status = GET_BITS(a, offset + BW_STATUS - 1, offset);
        }
        else
        {
            a_status = 0;
            a_s = 0;
            a_e = 0;
            a_m = 0;
        }
    }
    else
    {
        a_s = GET_BITS(a, BW - 1, BW - SW);
        a_e = GET_BITS(a, BW - SW - 1, MW);
        a_m = GET_BITS(a, MW - 1, 0);
    }

    bool a_is_nan = (a_status >> 2) & 1;
    bool a_is_inf = (a_status >> 1) & 1;
    bool a_is_zero = (a_status >> 0) & 1;

    uint64_t lsd_in_val = a_m & MASK(MW - 1);
    _u26 lsd_in = (_u26)lsd_in_val;

    _u26 lsd_dec_unused;
    _u5 a_m_cls_w;

    c_DW_lsd_w26(lsd_in, &lsd_dec_unused, &a_m_cls_w);

    uint64_t a_m_cls = a_m_cls_w;

    uint64_t sfl_in_val = a_m & MASK(MW);
    _u27 sfl_in = (_u27)sfl_in_val;
    _u27 sfl_out;

    c_ne_fp_sfl_blk_w27s5(sfl_in, (_u5)a_m_cls, &sfl_out);

    uint64_t a_m_sfl = sfl_out;

    int bit_check_pos = MW - 2;  // 25
    int sfl_check_bits = MW - 3; // 24

    bool a_m_top_check = (a_m >> bit_check_pos) & 1;
    // 检查 sfl 低 25 位 (0到24) 是否全为0
    // MASK(25) 对应 bits [24:0]
    uint64_t sfl_low_part = a_m_sfl & MASK(sfl_check_bits + 1);

    bool z_m_neg_overflow = a_m_top_check && (sfl_low_part == 0);

    // -----------------------------------------------------
    // D. Final z_m
    // -----------------------------------------------------
    // Verilog: z_m = overflow ? {a_m[MW-1:MW-2], a_m_sfl[MW-2:1]} : {a_m[MW-1:MW-2], a_m_sfl[MW-3:0]}
    // MW=27 -> Top 2 bits are [26:25]

    uint64_t z_m;
    uint64_t am_top2 = (a_m >> (MW - 2)) & 0x3; // 取高两位

    if (z_m_neg_overflow)
    {
        // 取 sfl [MW-2:1] -> [25:1]
        // 长度是 MW-2 = 25 位
        uint64_t part_sfl = (a_m_sfl >> 1) & MASK(MW - 2);
        z_m = (am_top2 << (MW - 2)) | part_sfl;
    }
    else
    {
        // 取 sfl [MW-3:0] -> [24:0]
        // 长度是 MW-2 = 25 位
        uint64_t part_sfl = a_m_sfl & MASK(MW - 2);
        z_m = (am_top2 << (MW - 2)) | part_sfl;
    }

    // -----------------------------------------------------
    // E. Exponent
    // -----------------------------------------------------
    int64_t a_e_signed = (int64_t)a_e;
    int64_t z_e0_calc = a_e_signed - (int64_t)a_m_cls + (int64_t)z_m_neg_overflow;
    uint64_t z_e0 = z_e0_calc & MASK(EW);

    uint64_t z_e = z_e0;
    uint64_t z_s = a_s;

    // Status logic remains same
    bool z_is_nan = a_is_nan;
    bool z_is_inf = a_is_inf;
    bool z_m_is_zero = (z_m == 0);
    bool z_is_zero = a_is_zero || (z_m_is_zero && !a_is_inf && !a_is_nan);

    uint64_t z_e_max = (BIAS + 1) & MASK(EW);
    uint64_t z_e_zero_val = ((uint64_t)(-BIAS)) & MASK(EW);

    // NaN: {z_s, z_e_max, {z_s,z_s,1'b1, {(MW-3){1'b0}}}}
    uint64_t nan_payload = (z_s << (MW - 1)) | (z_s << (MW - 2)) | (1ULL << (MW - 3));
    uint64_t z_nan_pkt = (z_s << (EW + MW)) | (z_e_max << MW) | nan_payload;

    // Inf: {z_s, z_e_max, {z_s,z_s,{(MW-2){1'b0}}}}
    uint64_t inf_payload = (z_s << (MW - 1)) | (z_s << (MW - 2));
    uint64_t z_inf_pkt = (z_s << (EW + MW)) | (z_e_max << MW) | inf_payload;

    // Zero: {z_s, z_e_zero, {z_s,z_s,{(MW-2){1'b0}}}}
    uint64_t zero_payload = (z_s << (MW - 1)) | (z_s << (MW - 2));
    uint64_t z_zero_pkt = (z_s << (EW + MW)) | (z_e_zero_val << MW) | zero_payload;

    // Data: {z_s, z_e, z_m}
    uint64_t z_d_pkt = (z_s << (EW + MW)) | (z_e << MW) | z_m;

    // -----------------------------------------------------
    // Output Mux
    // -----------------------------------------------------
    uint64_t z_o;
    if ((mode & 1) != 0)
    {
        int data_width = SW + EW + MW;
        z_o = a & MASK(data_width);
    }
    else
    {
        if (z_is_nan)
            z_o = z_nan_pkt;
        else if (z_is_inf)
            z_o = z_inf_pkt;
        else if (z_is_zero)
            z_o = z_zero_pkt;
        else
            z_o = z_d_pkt;
    }

    // Final Pack
    uint64_t final_z;
    if (BW_STATUS > 0)
    {
        uint64_t z_status = (z_is_nan << 2) | (z_is_inf << 1) | z_is_zero;
        int core_width = SW + EW + MW;
        final_z = (z_status << core_width) | (z_o & MASK(core_width));
    }
    else
    {
        final_z = z_o;
    }

    return final_z;
}

int main()
{
    uint64_t din_a;
    uint64_t din_mode;

    din_a = din_a & MASK(41);
    din_mode = din_mode & 0x7;

    uint64_t status_in = (din_a >> 38) & 0x7;

    __CPROVER_assume(status_in == 0 || status_in == 1 || status_in == 2 || status_in == 4);
    __CPROVER_assume(din_mode == 1 || din_mode == 2);

    ne_fp_ffp_norm_mw27.a = din_a;
    ne_fp_ffp_norm_mw27.mode = din_mode;
    set_inputs();

    uint64_t ref_z = c_ne_fp_ffp_norm_mw27(din_a, din_mode);
    
    assert(ne_fp_ffp_norm_mw27.z == ref_z);
}