#include <stdio.h>
#include <assert.h>
#include <stdint.h>
#include <stdbool.h>
#include "common.h"

void next_timeframe(void);
void set_inputs(void);
extern const unsigned int bound;

struct ne_fp_ffp_norm_mw16
{
    _u30 a;
    _u30 z;
    _u3 mode;
};

extern struct ne_fp_ffp_norm_mw16 ne_fp_ffp_norm_mw16;

void c_ne_fp_sfl_blk_w16s4(
    _u16 a,
    _u4 s,
    _u16 *z)
{
    *z = 0;
    *z = a << s;
}

void c_DW_lsd_w15(_u15 a, _u15 *dec, _u4 *enc)
{
    _u32 i; // 修改 i 类型以避免循环警告，逻辑不变

    for (i = 14; i > 0; i--)
    {
        // 提取第i位和第i-1位，检查它们是否不同
        if (EXTRACT_BITS(a, i, i) != EXTRACT_BITS(a, i - 1, i - 1))
        {
            *enc = 14 - i;  // 编码值为从最高位开始的位置索引
            *dec = 1U << i; // 解码值为第i位的掩码
            break;          // 找到第一个不同的位对后退出循环
        }
    }

    // 如果所有位都相同（循环正常结束）
    if (i == 0)
    {
        *enc = 14;
        *dec = 0x1; // Bit 0
    }
}

uint64_t c_ne_fp_ffp_norm_mw16(uint64_t a, uint64_t mode)
{
    const int SW = 1;
    const int EW = 10;
    const int MW = 16;
    const int BW_STATUS = 3;
    const int BW = (BW_STATUS + SW + EW + MW); // 30
    const int BIAS = 511;
    // -----------------------------------------------------

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

    // A. 计算 Leading Sign/Bit Detection (LSD)
    _u15 lsd_in = (_u15)(a_m & MASK(MW - 1)); // 取 a_m 的低15位 [MW-2:0]
    _u15 lsd_dec_unused;
    _u4 a_m_cls_w;

    c_DW_lsd_w15(lsd_in, &lsd_dec_unused, &a_m_cls_w);

    uint64_t a_m_cls = a_m_cls_w; // 扩展回 uint64 方便计算

    // B. 计算移位 (Shifter)
    _u16 sfl_in = (_u16)(a_m & MASK(MW));
    _u16 sfl_out;

    c_ne_fp_sfl_blk_w16s4(sfl_in, (_u4)a_m_cls, &sfl_out);

    uint64_t a_m_sfl = sfl_out; // 扩展回 uint64

    // C. 计算 z_m_neg_overflow
    // Verilog: a_m[MW-2] & (~|a_m_sfl[MW-3:0])
    // MW=16, MW-2=14, MW-3=13
    bool a_m_bit14 = (a_m >> 14) & 1;
    uint64_t sfl_low_14 = a_m_sfl & MASK(14); // bits [13:0]
    bool z_m_neg_overflow = a_m_bit14 && (sfl_low_14 == 0);

    // D. 拼接最终的 z_m
    // Verilog: z_m_neg_overflow ? {a_m[15:14],a_m_sfl[14:1]} : {a_m[15:14], a_m_sfl[13:0]}
    uint64_t z_m;
    uint64_t am_top2 = (a_m >> 14) & 0x3; // a_m[15:14]

    if (z_m_neg_overflow)
    {
        uint64_t part_sfl = (a_m_sfl >> 1) & MASK(14); // a_m_sfl[14:1]
        z_m = (am_top2 << 14) | part_sfl;
    }
    else
    {
        uint64_t part_sfl = a_m_sfl & MASK(14); // a_m_sfl[13:0]
        z_m = (am_top2 << 14) | part_sfl;
    }

    // E. 计算指数 z_e0
    // Verilog: z_e0 = a_e - a_m_cls + z_m_neg_overflow

    int64_t a_e_signed = (int64_t)a_e;
    int64_t z_e0_calc = a_e_signed - (int64_t)a_m_cls + (int64_t)z_m_neg_overflow;
    uint64_t z_e0 = z_e0_calc & MASK(EW); // [9:0]

    uint64_t z_e = z_e0;
    uint64_t z_s = a_s;

    bool z_is_nan = a_is_nan;
    bool z_is_inf = a_is_inf;

    // z_is_zero = a_is_zero | ((~|z_m)&(~a_is_inf)&(~a_is_nan));
    bool z_m_is_zero = (z_m == 0);
    bool z_is_zero = a_is_zero || (z_m_is_zero && !a_is_inf && !a_is_nan);

    uint64_t z_e_max = (BIAS + 1) & MASK(EW);
    uint64_t z_e_zero_val = ((uint64_t)(-BIAS)) & MASK(EW); // 补码表示

    // {z_s, z_e_max, {z_s,z_s,1'b1, {(MW-3){1'b0}}}}
    uint64_t nan_payload = (z_s << (MW - 1)) | (z_s << (MW - 2)) | (1ULL << (MW - 3));
    uint64_t z_nan_pkt = (z_s << (EW + MW)) | (z_e_max << MW) | nan_payload;

    // {z_s, z_e_max, {z_s,z_s,{(MW-2){1'b0}}}}
    uint64_t inf_payload = (z_s << (MW - 1)) | (z_s << (MW - 2));
    uint64_t z_inf_pkt = (z_s << (EW + MW)) | (z_e_max << MW) | inf_payload;

    // {z_s, z_e_zero, {z_s,z_s,{(MW-2){1'b0}}}}
    uint64_t zero_payload = (z_s << (MW - 1)) | (z_s << (MW - 2));
    uint64_t z_zero_pkt = (z_s << (EW + MW)) | (z_e_zero_val << MW) | zero_payload;

    // {z_s, z_e, z_m}
    uint64_t z_d_pkt = (z_s << (EW + MW)) | (z_e << MW) | z_m;

    uint64_t z_o;

    if ((mode & 1) != 0)
    {
        // mode[0] == 1: Bypass mode
        // 截取输入数据的低 BW - BW_STATUS 位 (即 27 位)
        int data_width = SW + EW + MW;
        z_o = a & MASK(data_width);
    }
    else
    {
        // mode[0] == 0: Normalization mode
        if (z_is_nan)
        {
            z_o = z_nan_pkt;
        }
        else if (z_is_inf)
        {
            z_o = z_inf_pkt;
        }
        else if (z_is_zero)
        {
            z_o = z_zero_pkt;
        }
        else
        {
            z_o = z_d_pkt;
        }
    }

    uint64_t final_z;
    if (BW_STATUS > 0)
    {
        uint64_t z_status = (z_is_nan << 2) | (z_is_inf << 1) | z_is_zero;
        int core_width = SW + EW + MW; // 27
        // z = {z_status, z_o}
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

    din_a = din_a & 0x3FFFFFFF;
    din_mode = din_mode & 0x7;
    uint64_t status_in = (din_a >> 27) & 0x7;
    // 0(000): Normal
    // 1(001): Zero
    // 2(010): Inf
    // 4(100): NaN
    // 禁止 3(011), 5, 6, 7 这种"既是Zero又是Inf"的非法组合
    __CPROVER_assume(status_in == 0 || status_in == 1 || status_in == 2 || status_in == 4);
    __CPROVER_assume(din_mode == 1 || din_mode == 4 || din_mode == 2);

    ne_fp_ffp_norm_mw16.a = din_a;
    ne_fp_ffp_norm_mw16.mode = din_mode;
    set_inputs();
    uint64_t ref_z = c_ne_fp_ffp_norm_mw16(din_a, din_mode);

    printf("ne_fp_ffp_norm_mw16.z = %d\n", ne_fp_ffp_norm_mw16.z);
    printf("ref_z = %d\n", ref_z);
    assert(ne_fp_ffp_norm_mw16.z == ref_z);
}
