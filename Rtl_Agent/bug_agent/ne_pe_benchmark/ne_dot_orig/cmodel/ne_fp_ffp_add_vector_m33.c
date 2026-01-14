#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <stdbool.h>

void set_inputs(void);
void next_timeframe(void);
extern const unsigned int bound;

typedef unsigned __CPROVER_bitvector[4] _u4;
typedef unsigned __CPROVER_bitvector[9] _u9;
typedef unsigned __CPROVER_bitvector[16] _u16;
typedef unsigned __CPROVER_bitvector[18] _u18;
typedef unsigned __CPROVER_bitvector[29] _u29;
typedef unsigned __CPROVER_bitvector[46] _u46;
typedef unsigned __CPROVER_bitvector[96] _u96;
typedef unsigned __CPROVER_bitvector[512] _u512;

struct ne_fp_ffp_add_vector_m33
{
    _u4 op_mode;
    _u9 e_max;
    _u18 ab_scale;
    _u96 ae_sub;
    _u96 be_sub;
    _u16 a_e_overflow;
    _u16 b_e_overflow;
    _u512 a_m;
    _u46 z;
    _u29 z_fp4;
};

extern struct ne_fp_ffp_add_vector_m33 ne_fp_ffp_add_vector_m33;

#ifndef MASK
#define MASK(w) ((((uint64_t)1) << (w)) - 1)
#endif

#define GET_BITS(val, high, low) (((val) >> (low)) & MASK((high) - (low) + 1))
#define BIT(val, n) (((val) >> (n)) & 1)

static int64_t sext(uint64_t val, int w)
{
    return (val & (1ULL << (w - 1))) ? (val | ~MASK(w)) : val;
}

uint32_t c_DW01_add(uint32_t adder_a, uint32_t adder_b, uint32_t width)
{
    return (adder_a + adder_b) & (uint32_t)MASK(width);
}

typedef struct
{
    uint64_t z;
    uint64_t z_fp4;
} VectorM33Result;

typedef struct
{
    uint64_t out0;
    uint64_t out1;
} TreeResult;

TreeResult ne_dw_add_tree(const uint64_t *inputs, int num_inputs, int input_width)
{
    uint64_t mask = (input_width >= 64) ? 0xFFFFFFFFFFFFFFFFULL : MASK(input_width);
    uint64_t cur_ops[64];
    uint64_t nxt_ops[64];
    int count = num_inputs;

    for (int i = 0; i < num_inputs; i++)
        cur_ops[i] = inputs[i] & mask;

    while (count > 2)
    {
        int n_idx = 0;
        int grps = count / 3;
        int rem = count % 3;

        for (int i = 0; i < grps; i++)
        {
            uint64_t a = cur_ops[i * 3];
            uint64_t b = cur_ops[i * 3 + 1];
            uint64_t c = cur_ops[i * 3 + 2];
            uint64_t sum = a ^ b ^ c;
            uint64_t carry = (a & b) | (b & c) | (a & c);
            nxt_ops[n_idx++] = sum & mask;
            nxt_ops[n_idx++] = (carry << 1) & mask;
        }
        for (int i = 0; i < rem; i++)
            nxt_ops[n_idx++] = cur_ops[grps * 3 + i];
        for (int i = 0; i < n_idx; i++)
            cur_ops[i] = nxt_ops[i];
        count = n_idx;
    }

    TreeResult res;
    res.out0 = cur_ops[0] & mask;
    res.out1 = (count > 1) ? (cur_ops[1] & mask) : 0;
    return res;
}

static uint64_t get_sub_slice(const uint32_t *arr, int idx, int width)
{
    int bit_start = idx * 6;
    int arr_idx = bit_start / 32;
    int off = bit_start % 32;
    uint64_t val = arr[arr_idx];
    if (off + width > 32)
        val |= ((uint64_t)arr[arr_idx + 1] << 32);
    return (val >> off) & MASK(width);
}

// =========================================================
// 5. 主模型 (直接对齐 RTL 接口)
// =========================================================

typedef struct
{
    uint64_t z;
    uint64_t z_fp4;
} VectorM33Result;

// [修改] 参数列表现在直接使用 HW-CBMC 的 bitvector，与 Verilog 端口一一对应
VectorM33Result c_ne_fp_ffp_add_vector_m33(
    _u4 bv_op_mode,
    _u9 bv_e_max,
    _u18 bv_ab_scale,
    _u96 bv_ae_sub, // 16*6 = 96
    _u96 bv_be_sub, // 16*6 = 96
    _u16 bv_a_e_overflow,
    _u16 bv_b_e_overflow,
    _u512 bv_a_m // 16*32 = 512
)
{
    // -----------------------------------------------------
    // A. 内部转换逻辑 (在此处完成拆包)
    // -----------------------------------------------------
    uint32_t op_mode = (uint32_t)bv_op_mode;
    uint32_t e_max = (uint32_t)bv_e_max;
    uint32_t ab_scale = (uint32_t)bv_ab_scale;
    uint32_t a_e_overflow = (uint32_t)bv_a_e_overflow;
    uint32_t b_e_overflow = (uint32_t)bv_b_e_overflow;

    // 转换 a_m (512 bits -> uint32_t array)
    uint32_t a_m_arr[16];
    for (int i = 0; i < 16; i++)
    {
        a_m_arr[i] = (uint32_t)(bv_a_m >> (i * 32));
    }

    // 转换 ae_sub / be_sub (96 bits -> uint32_t array)
    // 3个 uint32 (96 bit)
    uint32_t ae_sub_arr[3];
    uint32_t be_sub_arr[3];
    for (int i = 0; i < 3; i++)
    {
        ae_sub_arr[i] = (uint32_t)(bv_ae_sub >> (i * 32));
        be_sub_arr[i] = (uint32_t)(bv_be_sub >> (i * 32));
    }

    // -----------------------------------------------------
    // B. 核心算法 (保持不变，只是使用转换后的变量)
    // -----------------------------------------------------

    // [保护] 保存原始的 adder_in_00/01 数据
    uint64_t adder_in_01_raw[16];
    uint64_t adder_in_00_raw[16];

    uint64_t adder_in_1[16];
    uint64_t adder_in_0[16];
    uint64_t adder_in_2[32];

    // Status Accumulators
    bool z_tf32_zero_t = true;
    bool z_tf32_nan_t = false;
    bool z_tf32_inf_t_raw = false;

    bool global_tf32_pinf = false;
    bool global_tf32_ninf = false;

    bool z_fp8_zero_t = true;
    bool z_fp8_nan_t = false;
    bool z_fp8_inf_t_raw = false;

    bool global_fp8_pinf = false;
    bool global_fp8_ninf = false;

    bool z_fp4_is_zero = true;
    bool z1_fp4_is_zero = true;

    uint64_t fp4_add_in_11[16];
    uint64_t fp4_add_in_10[16];

    for (int i = 0; i < 16; i++)
    {
        uint64_t am_slice = a_m_arr[i];

        uint64_t status_tf32 = (op_mode & 4) ? GET_BITS(am_slice, 25, 23) : 0;
        uint64_t status_fp8_1 = (op_mode & 2) ? GET_BITS(am_slice, 27, 25) : 0;
        uint64_t status_fp8_0 = (op_mode & 2) ? GET_BITS(am_slice, 11, 9) : 0;

        // TF32 Status
        bool a_tf32_zero = BIT(status_tf32, 2);
        bool a_tf32_inf = BIT(status_tf32, 1);
        bool a_tf32_nan = BIT(status_tf32, 0);
        bool sign_tf32 = BIT(am_slice, 22);

        bool a_tf32_pinf = a_tf32_inf && (a_tf32_inf ^ sign_tf32);
        bool a_tf32_ninf = a_tf32_inf && sign_tf32;

        z_tf32_zero_t &= a_tf32_zero;
        z_tf32_nan_t |= a_tf32_nan;
        z_tf32_inf_t_raw |= a_tf32_inf;

        global_tf32_pinf |= a_tf32_pinf;
        global_tf32_ninf |= a_tf32_ninf;

        // FP8 Status
        bool a_fp8_zero = BIT(status_fp8_1, 2);
        bool a_fp8_inf = BIT(status_fp8_1, 1);
        bool a_fp8_nan = BIT(status_fp8_1, 0);
        bool sign_fp8_a = BIT(am_slice, 24);

        bool b_fp8_zero = BIT(status_fp8_0, 2);
        bool b_fp8_inf = BIT(status_fp8_0, 1);
        bool b_fp8_nan = BIT(status_fp8_0, 0);
        bool sign_fp8_b = BIT(am_slice, 8);

        bool a_fp8_pinf = a_fp8_inf && (a_fp8_inf ^ sign_fp8_a);
        bool a_fp8_ninf = a_fp8_inf && sign_fp8_a;
        bool b_fp8_pinf = b_fp8_inf && (b_fp8_inf ^ sign_fp8_b);
        bool b_fp8_ninf = b_fp8_inf && sign_fp8_b;

        z_fp8_zero_t &= (a_fp8_zero & b_fp8_zero);
        z_fp8_nan_t |= (a_fp8_nan | b_fp8_nan);
        z_fp8_inf_t_raw |= (a_fp8_inf | b_fp8_inf);

        global_fp8_pinf |= (a_fp8_pinf | b_fp8_pinf);
        global_fp8_ninf |= (a_fp8_ninf | b_fp8_ninf);

        // FP4 Zero Check
        bool op3 = (op_mode & 8) != 0;
        bool a_fp4_z = op3 && BIT(am_slice, 15);
        bool b_fp4_z = op3 && BIT(am_slice, 7);
        bool a1_fp4_z = op3 && BIT(am_slice, 31);
        bool b1_fp4_z = op3 && BIT(am_slice, 23);

        if (i < 8)
            z_fp4_is_zero &= (a_fp4_z & b_fp4_z & a1_fp4_z & b1_fp4_z);
        else
            z1_fp4_is_zero &= (a_fp4_z & b_fp4_z & a1_fp4_z & b1_fp4_z);

        // Mantissa & Alignment
        uint64_t m_fp4_a = (op_mode & 8) ? GET_BITS(am_slice, 12, 8) : 0;
        uint64_t m_fp4_b = (op_mode & 8) ? GET_BITS(am_slice, 4, 0) : 0;
        uint64_t m_tf32 = (op_mode & 4) ? GET_BITS(am_slice, 22, 0) : 0;
        uint64_t m_fp8_1 = (op_mode & 2) ? GET_BITS(am_slice, 24, 16) : 0;
        uint64_t m_fp8_0 = (op_mode & 2) ? GET_BITS(am_slice, 8, 0) : 0;
        uint64_t m_int8_1 = (op_mode & 1) ? GET_BITS(am_slice, 31, 16) : 0;
        uint64_t m_int8_0 = (op_mode & 1) ? GET_BITS(am_slice, 15, 0) : 0;

        uint64_t am_fp_1, am_fp_0;
        if (op_mode & 8)
        {
            uint64_t s = BIT(m_fp4_a, 4);
            am_fp_1 = (s ? MASK(22) << 9 : 0) | (m_fp4_a << 4);
            s = BIT(m_fp4_b, 4);
            am_fp_0 = (s ? MASK(21) << 9 : 0) | (m_fp4_b << 4);
        }
        else if (op_mode & 4)
        {
            uint64_t s = BIT(m_tf32, 22);
            am_fp_1 = (s ? MASK(4) << 27 : 0) | (m_tf32 << 4);
            am_fp_0 = 0;
        }
        else
        {
            uint64_t s = BIT(m_fp8_1, 8);
            am_fp_1 = (s ? MASK(5) << 26 : 0) | (m_fp8_1 << 17);
            s = BIT(m_fp8_0, 8);
            am_fp_0 = (s ? MASK(4) << 26 : 0) | (m_fp8_0 << 17);
        }

        uint64_t ae_raw = get_sub_slice(ae_sub_arr, i, 6);
        uint64_t be_raw = get_sub_slice(be_sub_arr, i, 6);

        uint64_t ae_shift = (op_mode & 8) ? (ae_raw & 7) : (ae_raw & 31);
        uint64_t be_shift = (op_mode & 8) ? (be_raw & 7) : (be_raw & 31);

        int64_t am_sfr_1 = sext(am_fp_1, 31) >> ae_shift;
        int64_t am_sfr_0 = sext(am_fp_0, 30) >> be_shift;

        uint64_t st_mask_1 = (ae_shift >= 31) ? MASK(31) : MASK(ae_shift);
        uint64_t st_mask_0 = (be_shift >= 30) ? MASK(30) : MASK(be_shift);

        bool ovf_1 = BIT(a_e_overflow, i);
        bool ovf_0 = BIT(b_e_overflow, i);

        uint64_t norm_1 = ovf_1 ? 0 : (am_fp_1 & st_mask_1);
        uint64_t norm_0 = ovf_0 ? 0 : (am_fp_0 & st_mask_0);

        uint64_t sig_1 = ((am_sfr_1 << 1) | (norm_1 != 0)) & (ovf_1 ? 0 : ~0ULL);
        uint64_t sig_0 = ((am_sfr_0 << 1) | (norm_0 != 0)) & (ovf_0 ? 0 : ~0ULL);
        sig_1 &= MASK(32);
        sig_0 &= MASK(31);

        if (op_mode & 1)
        {
            uint64_t s1 = BIT(m_int8_1, 15);
            adder_in_01_raw[i] = (s1 ? MASK(4) << 16 : 0) | m_int8_1;
            uint64_t s0 = BIT(m_int8_0, 15);
            adder_in_00_raw[i] = (s0 ? MASK(4) << 16 : 0) | m_int8_0;
        }
        else
        {
            adder_in_01_raw[i] = sig_1;
            adder_in_00_raw[i] = sig_0;
        }

        adder_in_1[i] = adder_in_01_raw[i];
        adder_in_0[i] = adder_in_00_raw[i];

        // FP4 High Part
        uint64_t m_fp4_a1 = (op_mode & 8) ? GET_BITS(am_slice, 28, 24) : 0;
        uint64_t m_fp4_b1 = (op_mode & 8) ? GET_BITS(am_slice, 20, 16) : 0;

        uint64_t a1_e_sh = (ae_raw >> 3) & 7;
        uint64_t b1_e_sh = (be_raw >> 3) & 7;

        uint64_t s_a1 = BIT(m_fp4_a1, 4);
        uint64_t am1_fp_1 = (s_a1 ? MASK(5) << 9 : 0) | (m_fp4_a1 << 4);
        uint64_t s_b1 = BIT(m_fp4_b1, 4);
        uint64_t am1_fp_0 = (s_b1 ? MASK(5) << 9 : 0) | (m_fp4_b1 << 4);

        int64_t am1_sfr_1 = sext(am1_fp_1, 14) >> a1_e_sh;
        int64_t am1_sfr_0 = sext(am1_fp_0, 14) >> b1_e_sh;

        fp4_add_in_11[i] = (am1_sfr_1 << 1) & MASK(15);
        fp4_add_in_10[i] = (am1_sfr_0 << 1) & MASK(15);
    }

    // Post-Loop Assembly
    for (int i = 0; i < 8; i++)
    {
        if (op_mode & 8)
        {
            adder_in_2[i * 2 + 0] = adder_in_00_raw[i + 8] & MASK(15);
            adder_in_2[i * 2 + 1] = adder_in_01_raw[i + 8] & MASK(15);
        }
        else
        {
            adder_in_2[i * 2 + 0] = 0;
            adder_in_2[i * 2 + 1] = 0;
        }
    }

    for (int i = 8; i < 16; i++)
    {
        if (op_mode & 8)
        {
            adder_in_1[i] = sext(fp4_add_in_11[i - 8], 15) & MASK(32);
            adder_in_0[i] = sext(fp4_add_in_10[i - 8], 15) & MASK(31);
            adder_in_2[i * 2 + 0] = fp4_add_in_10[i];
            adder_in_2[i * 2 + 1] = fp4_add_in_11[i];
        }
        else
        {
            adder_in_2[i * 2 + 0] = 0;
            adder_in_2[i * 2 + 1] = 0;
        }
    }

    // Tree & Adders
    TreeResult tr1 = ne_dw_add_tree(adder_in_1, 16, 32);
    TreeResult tr0 = ne_dw_add_tree(adder_in_0, 16, 31);
    TreeResult tr2 = ne_dw_add_tree(adder_in_2, 32, 15);

    uint64_t adder1_z = c_DW01_add(tr1.out0, tr1.out1, 32);
    uint64_t adder0_z = c_DW01_add(tr0.out0, tr0.out1, 31);
    uint64_t adder2_z = c_DW01_add(tr2.out0, tr2.out1, 15);

    uint64_t adder1_z_mux = (op_mode & 1) ? (sext(adder1_z & MASK(20), 20) & MASK(32)) : adder1_z;
    uint64_t adder0_z_ext = (BIT(adder0_z, 30) << 31) | adder0_z;
    uint64_t adder0_z_mux = (op_mode & 1) ? (sext(adder0_z & MASK(20), 20) & MASK(32)) : adder0_z_ext;

    uint64_t adder_z = c_DW01_add(adder1_z_mux, adder0_z_mux, 32);

    // Final Status & Output
    bool z_tf32_nan = z_tf32_nan_t | (global_tf32_pinf & global_tf32_ninf);
    bool z_tf32_inf = z_tf32_inf_t_raw & !z_tf32_nan;
    bool z_fp8_nan = z_fp8_nan_t | (global_fp8_pinf & global_fp8_ninf);
    bool z_fp8_inf = z_fp8_inf_t_raw & !z_fp8_nan;

    uint64_t e_sfr = (op_mode & 4) ? 4 : 5;
    uint64_t e_max_ext = (BIT(e_max, 8) << 9) | e_max;
    uint64_t z_e0_t = e_max_ext + e_sfr;

    uint64_t abs_low = ab_scale & MASK(9);
    uint64_t abs_ext = (BIT(abs_low, 8) << 10) | (BIT(abs_low, 8) << 9) | abs_low;
    uint64_t z_e0_trunc = z_e0_t & MASK(10);
    uint64_t z_e0_sign_ext = (BIT(z_e0_trunc, 9) << 10) | z_e0_trunc;
    uint64_t z_e_t = z_e0_sign_ext + abs_ext;
    uint64_t z_e = z_e_t & MASK(10);

    bool zs_inf = ((op_mode & 4) && z_tf32_inf && global_tf32_ninf) ||
                  ((op_mode & 2) && z_fp8_inf && global_fp8_ninf);

    uint64_t zs_tf32 = z_tf32_inf ? zs_inf : BIT(adder1_z, 31);
    uint64_t zs_fp8 = z_fp8_inf ? zs_inf : BIT(adder_z, 31);

    uint64_t zm_tf32 = (zs_tf32 << 32) | adder1_z;
    uint64_t zm_fp8 = (zs_fp8 << 32) | adder_z;
    uint64_t z_int8 = adder_z & MASK(21);

    uint64_t z_final;
    uint64_t z_fp4_out = 0;

    if (op_mode & 8)
    {
        uint64_t fp4_c0_scale = ((ab_scale & MASK(9)) | (BIT(ab_scale, 8) << 9)) + 10;
        uint64_t fp4_c32_scale = (GET_BITS(ab_scale, 17, 9) | (BIT(ab_scale, 17) << 9)) + 10;
        uint64_t ze_fp4 = ((fp4_c32_scale & MASK(10)) << 10) | (fp4_c0_scale & MASK(10));
        uint64_t zm_fp4_0 = (adder_z & MASK(15)) | (BIT(adder_z, 14) << 15);
        uint64_t zm_fp4_32 = (adder2_z & MASK(15)) | (BIT(adder2_z, 14) << 15);

        z_final = ((uint64_t)z_fp4_is_zero << 45) | ((ze_fp4 & MASK(10)) << 33) | (zm_fp4_0 << 17);
        z_fp4_out = (((uint64_t)z1_fp4_is_zero << 28) | ((ze_fp4 >> 10) << 16) | zm_fp4_32);
    }
    else if (op_mode & 4)
    {
        z_final = ((uint64_t)z_tf32_zero_t << 45) | ((uint64_t)z_tf32_inf << 44) |
                  ((uint64_t)z_tf32_nan << 43) | (z_e << 33) | (zm_tf32 & MASK(33));
    }
    else if (op_mode & 2)
    {
        z_final = ((uint64_t)z_fp8_zero_t << 45) | ((uint64_t)z_fp8_inf << 44) |
                  ((uint64_t)z_fp8_nan << 43) | (z_e << 33) | (zm_fp8 & MASK(33));
    }
    else
    {
        z_final = z_int8;
    }

    VectorM33Result res;
    res.z = z_final & MASK(46);
    res.z_fp4 = z_fp4_out & MASK(29);
    return res;
}

// =========================================================
// Main Testbench
// =========================================================
int main()
{
    // 1. Declarations
    _u4 din_mode;
    _u9 din_e_max;
    _u18 din_ab_scale;
    _u96 din_ae_sub;
    _u96 din_be_sub;
    _u16 din_ae_ovf;
    _u16 din_be_ovf;
    _u512 din_a_m;

    __CPROVER_assume(din_mode == 1 || din_mode == 2 || din_mode == 4 || din_mode == 8);
    // 3. Drive RTL
    ne_fp_ffp_add_vector_m33.op_mode = din_mode;
    ne_fp_ffp_add_vector_m33.e_max = din_e_max;
    ne_fp_ffp_add_vector_m33.ab_scale = din_ab_scale;
    ne_fp_ffp_add_vector_m33.ae_sub = din_ae_sub;
    ne_fp_ffp_add_vector_m33.be_sub = din_be_sub;
    ne_fp_ffp_add_vector_m33.a_e_overflow = din_ae_ovf;
    ne_fp_ffp_add_vector_m33.b_e_overflow = din_be_ovf;
    ne_fp_ffp_add_vector_m33.a_m = din_a_m;

    set_inputs();
    next_timeframe();
    next_timeframe();

    VectorM33Result ref = c_ne_fp_ffp_add_vector_m33(
        din_mode, din_e_max, din_ab_scale,
        din_ae_sub, din_be_sub,
        din_ae_ovf, din_be_ovf,
        din_a_m);

    _u46 rtl_z = ne_fp_ffp_add_vector_m33.z;
    _u29 rtl_z_fp4 = ne_fp_ffp_add_vector_m33.z_fp4;
    _u46 ref_z = ref.z;
    _u29 ref_z_fp4 = ref.z_fp4;
    assert(rtl_z == ref.z);
    assert(rtl_z_fp4 == ref.z_fp4);
    return 0;
}