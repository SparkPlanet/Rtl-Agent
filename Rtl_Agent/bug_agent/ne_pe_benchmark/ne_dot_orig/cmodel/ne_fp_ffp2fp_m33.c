#include <stdio.h>
#include <assert.h>
#include <stdint.h>
#include <stdbool.h>
#include "common.h"

void set_inputs(void);
void next_timeframe(void);
extern const unsigned int bound;

struct ne_fp_ffp2fp_m33
{
    _u47 a;
    _u32 z;
    _u4 mode;
    _u2 z_is_infnan;

    _u32 am2;
    _u11 am2_e;
    _u1 am1_iszero;
};

extern struct ne_fp_ffp2fp_m33 ne_fp_ffp2fp_m33;

void c_DW_lsd_w33(_u33 a, _u6 *enc)
{
    _u6 i;

    for (i = 32; i > 0; i--)
    {
        // 提取第i位和第i-1位，检查它们是否不同
        if (EXTRACT_BITS(a, i, i) != EXTRACT_BITS(a, i - 1, i - 1))
        {
            *enc = 32 - i; // 编码值为从最高位开始的位置索引
            break;         // 找到第一个不同的位对后退出循环
        }
    }

    if (i == 0)
    {
        *enc = 32;
    }
}

void c_ne_fp_ffp2fp_m33(
    _u47 a,
    _u4 mode,

    _u32 *z,
    _u2 *z_is_infnan)
{
    *z = 0;
    *z_is_infnan = 0;

    _u1 a_is_nan = EXTRACT_BITS(a, 46, 46);
    _u1 a_is_inf = EXTRACT_BITS(a, 45, 45);
    _u1 a_is_zero = EXTRACT_BITS(a, 44, 44);
    _u10 a_e = EXTRACT_BITS(a, 43, 34);
    _u1 a_s = EXTRACT_BITS(a, 33, 33);
    _u32 a_m = EXTRACT_BITS(a, 31, 0);

    _u1 z_s = a_s;
    _u1 z_is_zero = 0;
    _u1 z_is_inf = 0;
    _u1 z_is_nan = 0;
    _u1 z_is_norm = 0;
    _u1 z_is_subnorm = 0;

    if (mode == 1)
    { // int8
        // 为什么是直接提取21位符号位拓展可能之后得连着前面的模块一起看看
        _u22 part_int8;
        part_int8 = EXTRACT_BITS(a, 21, 0);
        *z = SIGN_EXTEND(part_int8, 32);
        *z_is_infnan = 0;
    }
    else
    {                  // tf32 fp8 fp4
        _u32 a_m1 = 0; // 补码处理后尾数位
        _u32 a_m2 = 0; // 左移后尾数位
        _u11 a_e2 = 0;
        _u6 a_m1_ls = 0; // 左移位数

        _u33 a_m_ext = a_s ? ((_u33)~a_m + (_u33)1) : a_m;
        _u1 a_m1_ecin = CHECK_SIGN_BIT(a_m_ext);

        // printf("a_m_ext_sign: %d\n", CHECK_SIGN_BIT(a_m_ext));
        a_m1 = CHECK_SIGN_BIT(a_m_ext) ? 0x80000000 : a_m_ext;

        c_DW_lsd_w33(a_m1, &a_m1_ls);
        a_m2 = a_m1 << a_m1_ls;

        int t;
        _u11 a_e_extend = SIGN_EXTEND(a_e, 11);
        _u11 a_m1_ls_extend = a_m1_ls;
        t = (_s11)a_e_extend - (_s11)a_m1_ls_extend + a_m1_ecin;
        a_e2 = t;

        _u1 a_m2_mcin = EXTRACT_BITS(a_m2, 7, 7);
        _u24 a_m2_hign24 = EXTRACT_BITS(a_m2, 31, 8);
        _u25 a_m3_ext = (_u25)a_m2_hign24 + (_u25)a_m2_mcin;
        _u23 z_m = a_m3_ext; // 23+1=25-1少的1位应该是尾数位的隐藏1
        _u1 a_m2_ecin = EXTRACT_BITS(a_m3_ext, 24, 24);
        _u8 z_e = (_s11)a_e2 + (_s11)127 + a_m2_ecin;

        // printf("a_e: %d\n", a_e);
        // printf("ref_a_e2: %d\n", a_e2);
        // printf("act_a_e2: %d\n", ne_fp_ffp2fp_m33.am2_e);
        // assert(a_m2==ne_fp_ffp2fp_m33.am2);
        // assert(a_e2==ne_fp_ffp2fp_m33.am2_e);

        // 分情况判断
        z_is_zero = ((a_m1 == 0) & (~a_is_inf) & (~a_is_nan)) | a_is_zero;
        z_is_nan = a_is_nan;
        z_is_inf = a_is_inf || (!z_is_zero && !z_is_nan && (((_s11)a_e2 > (_s11)127) || (a_e2 == 127) && a_m2_ecin));
        // assert(z_is_zero==ne_fp_ffp2fp_m33.am1_iszero);
        // printf("signed_a_e2>127:%d",(_s11)a_e2>(_s11)127);
        // printf("signed_a_e2==127:%d",(_s11)a_e2==(_s11)127);
        // printf("a_m2_ecin:%d",a_m2_ecin);
        *z_is_infnan = JOIN_BITS(z_is_inf, z_is_nan);

        z_is_norm = (((_s11)a_e2 > (_s11)-127) || ((_s11)a_e2 == (_s11)-127 && a_m2_ecin)) & (~z_is_inf) & (~z_is_nan);
        z_is_subnorm = ((_s11)a_e2 > (_s11)-151) & (~z_is_norm) & (~z_is_inf) & (~z_is_nan) & (~z_is_zero);

        t = -126 - (_s11)a_e2;
        _u5 a_m3_sub_rs = t;
        _u32 a_m3_subm = a_m2 >> a_m3_sub_rs;

        _u8 z_sube = 0;
        _u1 a_subm_mcin = EXTRACT_BITS(a_m3_subm, 7, 7);
        _u24 a_subm_hign24 = EXTRACT_BITS(a_m3_subm, 31, 8);
        _u25 a_subm_ext = (_u25)a_subm_hign24 + (_u25)a_subm_mcin;
        _u23 z_subm = a_subm_ext; // 23+1=25-1少的1位应该是尾数位的隐藏1

        *z = 0;
        if (z_is_zero)
        {
            //*z=0;
            *z = CONCAT_BITS(*z, a_s, 31);
        }
        else if (z_is_inf)
        {
            *z = 0x7f800000;
            *z = CONCAT_BITS(*z, z_s, 31);
        }
        else if (z_is_nan)
        {
            *z = 0x7fc00000;
        }
        else if (z_is_norm)
        {
            *z = CONCAT_BITS(*z, z_s, 31);
            *z = CONCAT_BITS(*z, z_e, 23);
            *z = CONCAT_BITS(*z, z_m, 0);
        }
        else if (z_is_subnorm)
        {
            *z = CONCAT_BITS(*z, z_s, 31);
            *z = CONCAT_BITS(*z, z_sube, 23);
            *z = CONCAT_BITS(*z, z_subm, 0);
        }
    }
}

// 11. 主函数（测试用例）
int main()
{
    // 声明
    _u1 a_is_zero;
    _u1 a_is_inf;
    _u1 a_is_nan;

    _u47 a;
    _u4 mode;
    _u32 z;
    _u2 z_is_infnan;

    // 测试输入设置
    // int8 测试
    //  mode=1;
    //  a_is_nan=0;
    //  a_is_inf=0;
    //  a_is_zero=0;
    //  a=CONCAT_BITS(a,a_is_inf,32);
    //  a=CONCAT_BITS(a,a_is_inf,45);
    //  a=CONCAT_BITS(a,a_is_nan,46);
    //  a=CONCAT_BITS(a,a_is_zero,44);

    // __CPROVER_assume(mode == 2 || mode == 4 || mode == 8);

    __CPROVER_assume(mode == 1 || mode == 2 || mode == 4 || mode == 8);
    __CPROVER_assume((mode != 1) || (mode == 1) && (!a_is_nan) && (!a_is_inf) && (!a_is_zero));
    a = CONCAT_BITS(a, a_is_inf, 32);
    a = CONCAT_BITS(a, a_is_inf, 45);
    a = CONCAT_BITS(a, a_is_nan, 46);
    a = CONCAT_BITS(a, a_is_zero, 44);

    ne_fp_ffp2fp_m33.a = a;
    ne_fp_ffp2fp_m33.mode = mode;
    set_inputs();
    c_ne_fp_ffp2fp_m33(a, mode, &z, &z_is_infnan);
    next_timeframe();
    printf("ref_z_is_infnan: %d\n", z_is_infnan);
    printf("act_z_is_infnan: %d\n", ne_fp_ffp2fp_m33.z_is_infnan);
    assert(ne_fp_ffp2fp_m33.z_is_infnan == z_is_infnan);
    printf("ref_z: %d", z);
    printf("act_z: %d", ne_fp_ffp2fp_m33.z);
    assert(ne_fp_ffp2fp_m33.z == z);
    return 0;
}