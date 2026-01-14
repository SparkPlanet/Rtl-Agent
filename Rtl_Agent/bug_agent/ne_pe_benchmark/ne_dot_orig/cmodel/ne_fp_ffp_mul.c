#include <stdio.h>
#include <assert.h>
#include "common.h"

void next_timeframe(void);
void set_inputs(void);
extern const unsigned int bound;

struct ne_fp_ffp_mul
{
    _u4 op_mode;
    _u1 i_gp_zero_skip_en;
    _u19 a;
    _u19 b;
    _u6 z0_e;
    _u9 z1_e;
    _u32 z_m;

    _u4 op_mode_1r;
    _u8 mul_a_1_1r; // int8_fp8_fp16_fp4
    _u8 mul_b_1_1r;
    _u8 mul_a_0_1r; // int8_fp8_fp16_fp4
    _u8 mul_b_0_1r;
    _u22 mul_z1;
    _u16 mul_z0;
};

extern struct ne_fp_ffp_mul ne_fp_ffp_mul;

// 10. 顶层模块功能实现函数
void c_DW02_mult_i8(
    _u8 A,
    _u8 B,
    _u1 TC,
    _u16 *PRODUCT)
{
    if (TC == 0)
    {
        *PRODUCT = A * B;
    }
    else
    {
        _u8 a_bit_inv = ~A;
        _u8 b_bit_inv = ~B;
        _u16 A_abs = CHECK_SIGN_BIT(A) ? a_bit_inv + 1 : A;
        _u16 B_abs = CHECK_SIGN_BIT(B) ? b_bit_inv + 1 : B;
        _u16 product_abs = A_abs * B_abs;
        *PRODUCT = (CHECK_SIGN_BIT(A) == CHECK_SIGN_BIT(B)) ? product_abs : ~product_abs + 1;
    }
}

void c_ne_fp_ffp_mul(
    _u4 op_mode, // 操作模式选择：4'b0001=int8, 4'b0010=fp8, 4'b0100=tf32, 4'b1000=fp4
    _u19 a,      // 19位输入操作数a
    _u19 b,      // 19位输入操作数b
    _u6 *z0_e,   // 第一个乘法结果的指数部分
    _u9 *z1_e,   // 第二个乘法结果的指数部分
    _u32 *z_m    // 乘法结果的尾数部分
)
{
    *z_m = 0;
    *z0_e = 0;
    *z1_e = 0;

    if (op_mode == 1)
    { // int8
        _u8 a_int[2];
        _u8 b_int[2];
        _u16 z_int[2];
        a_int[0] = EXTRACT_BITS(a, 7, 0);
        a_int[1] = EXTRACT_BITS(a, 16, 9);
        b_int[0] = EXTRACT_BITS(b, 7, 0);
        b_int[1] = EXTRACT_BITS(b, 16, 9);

        c_DW02_mult_i8(a_int[0], b_int[0], 1, &z_int[0]);
        c_DW02_mult_i8(a_int[1], b_int[1], 1, &z_int[1]);
        *z_m = JOIN_BITS(z_int[1], z_int[0]);
        // *z_m = ((_u32)z_int[1] << 16) | ((_u32)z_int[0]);
        *z0_e = 0;
        *z1_e = 0;
    }
    else if (op_mode == 2)
    { // fp8
        int bias = 15;
        int t_e;
        int t_M[2];
        int t_mul;

        _u1 z_s;
        _u9 z_M[2];
        _u9 a_fp8[2];
        _u9 b_fp8[2];
        _u5 a_e[2];
        _u5 b_e[2];
        _u3 a_m[2];
        _u3 b_m[2];
        _u1 a_s[2];
        _u1 b_s[2];
        _u1 a_e_is_zero[2]; // 指数位全0
        _u1 a_e_is_max[2];  // 指数位全1
        _u1 b_e_is_zero[2];
        _u1 b_e_is_max[2];
        _u1 a_m_is_zero[2]; // 尾数位全0
        _u1 b_m_is_zero[2];

        _u1 a_is_zero[2];
        _u1 a_is_inf[2];
        _u1 a_is_nan[2];
        _u1 a_is_subnorm[2];
        _u1 b_is_zero[2];
        _u1 b_is_inf[2];
        _u1 b_is_nan[2];
        _u1 b_is_subnorm[2];

        _u1 z_is_zero[2];
        _u1 z_is_inf[2];
        _u1 z_is_nan[2];
        _u3 z_status[2];

        _u1 a_hide_bit;
        _u1 b_hide_bit;

        for (int i = 0; i < 2; i++)
        {
            a_fp8[i] = EXTRACT_BITS(a, (i + 1) * 9 - 1, i * 9);
            b_fp8[i] = EXTRACT_BITS(b, (i + 1) * 9 - 1, i * 9);
            a_s[i] = EXTRACT_BITS(a_fp8[i], 8, 8);
            b_s[i] = EXTRACT_BITS(b_fp8[i], 8, 8);
            a_e[i] = EXTRACT_BITS(a_fp8[i], 7, 3);
            b_e[i] = EXTRACT_BITS(b_fp8[i], 7, 3);
            a_m[i] = EXTRACT_BITS(a_fp8[i], 2, 0);
            b_m[i] = EXTRACT_BITS(b_fp8[i], 2, 0);
            a_e_is_zero[i] = a_e[i] == 0;
            a_e_is_max[i] = a_e[i] == 31;
            b_e_is_zero[i] = b_e[i] == 0;
            b_e_is_max[i] = b_e[i] == 31;
            a_m_is_zero[i] = a_m[i] == 0;
            b_m_is_zero[i] = b_m[i] == 0;

            a_is_zero[i] = a_e_is_zero[i] && a_m_is_zero[i];
            a_is_inf[i] = a_e_is_max[i] && a_m_is_zero[i];
            a_is_nan[i] = a_e_is_max[i] && !a_m_is_zero[i];
            a_is_subnorm[i] = a_e_is_zero[i] && !a_m_is_zero[i];

            b_is_zero[i] = b_e_is_zero[i] && b_m_is_zero[i];
            b_is_inf[i] = b_e_is_max[i] && b_m_is_zero[i];
            b_is_nan[i] = b_e_is_max[i] && !b_m_is_zero[i];
            b_is_subnorm[i] = b_e_is_zero[i] && !b_m_is_zero[i];

            a_hide_bit = (!a_is_subnorm[i]) && (!a_is_zero[i]) && (!a_is_inf[i] && !a_is_nan[i]);
            b_hide_bit = (!b_is_subnorm[i]) && (!b_is_zero[i]) && (!b_is_inf[i] && !b_is_nan[i]);
            t_M[0] = JOIN_BITS(a_hide_bit, a_m[i]);
            t_M[1] = JOIN_BITS(b_hide_bit, b_m[i]);
            t_mul = t_M[0] * t_M[1];
            z_s = a_s[i] != b_s[i];
            if (z_s)
            {
                if (t_mul != 0) // 尾数部分计算输出非0正常取补码
                    t_mul = -t_mul;
                else if (a_is_zero[i] || b_is_zero[i]) // a,b输入为0导致的0正常输出0
                    t_mul = 0;
                else             // inf导致的尾数部分给mul子模块的输入为0导致的输出0
                    t_mul = 256; // 符号为拓展会给0的最高位补1变成9'h100000000
            }
            z_M[i] = t_mul;
            // 加这个1是处于什么目的
            t_e = a_e[i] + b_e[i] - 2 * bias + a_is_subnorm[i] + b_is_subnorm[i] + 1;
            if (i == 0)
            {
                *z0_e = (a_is_zero[i] || b_is_zero[i]) ? 484 : t_e; // 输入有一个为0时，指数位为-28\484\9'h1_11100100
            }
            else
            {
                *z1_e = (a_is_zero[i] || b_is_zero[i]) ? 484 : t_e;
            }
            // 判断是否为NaN或Inf  输入为NaN或者0×inf
            z_is_nan[i] = (a_is_nan[i] || b_is_nan[i]) || (a_is_inf[i] && b_is_zero[i]) || (a_is_zero[i] && b_is_inf[i]);
            // 判断是否为0         输入为0×非特殊值
            z_is_zero[i] = (a_is_zero[i] && !b_is_nan[i] && !b_is_inf[i]) || (b_is_zero[i] && !a_is_nan[i] && !a_is_inf[i]);
            // 判断是否为Inf       输入为inf×非0非NaN
            z_is_inf[i] = (a_is_inf[i] && !b_is_zero[i] && !b_is_nan[i]) || (b_is_inf[i] && !a_is_zero[i] && !a_is_nan[i]);
        }

        // z_status[0] = {z_is_zero[0], z_is_inf[0], z_is_nan[0]};
        z_status[0] = JOIN_BITS(z_is_zero[0], z_is_inf[0], z_is_nan[0]);
        z_status[1] = JOIN_BITS(z_is_zero[1], z_is_inf[1], z_is_nan[1]);
        *z_m = CONCAT_BITS(*z_m, z_status[1], 25);
        *z_m = CONCAT_BITS(*z_m, z_M[1], 16);
        *z_m = CONCAT_BITS(*z_m, z_status[0], 9);
        *z_m = CONCAT_BITS(*z_m, z_M[0], 0);
    }
    else if (op_mode == 4)
    { // tf32
        int bias = 127;
        int t_e;
        int t_M[2];
        int t_mul;
        _u1 z_s;
        _u23 z_M;
        _u19 a_tf32;
        _u19 b_tf32;

        _u8 a_e;
        _u8 b_e;
        _u10 a_m;
        _u10 b_m;
        _u1 a_s;
        _u1 b_s;

        _u1 a_e_is_zero; // 指数位全0
        _u1 a_e_is_max;  // 指数位全1
        _u1 b_e_is_zero;
        _u1 b_e_is_max;
        _u1 a_m_is_zero; // 尾数位全0
        _u1 b_m_is_zero;

        _u1 a_is_zero;
        _u1 a_is_inf;
        _u1 a_is_nan;
        _u1 a_is_subnorm;
        _u1 b_is_zero;
        _u1 b_is_inf;
        _u1 b_is_nan;
        _u1 b_is_subnorm;

        _u1 e_overflow_pos;
        _u1 e_overflow_neg;

        _u1 z_is_zero;
        _u1 z_is_inf;
        _u1 z_is_nan;
        _u3 z_status;

        _u1 a_hide_bit;
        _u1 b_hide_bit;

        a_tf32 = EXTRACT_BITS(a, 18, 0);
        b_tf32 = EXTRACT_BITS(b, 18, 0);
        a_s = EXTRACT_BITS(a_tf32, 18, 18);
        b_s = EXTRACT_BITS(b_tf32, 18, 18);
        a_e = EXTRACT_BITS(a_tf32, 17, 10);
        b_e = EXTRACT_BITS(b_tf32, 17, 10);
        a_m = EXTRACT_BITS(a_tf32, 9, 0);
        b_m = EXTRACT_BITS(b_tf32, 9, 0);
        a_e_is_zero = a_e == 0;
        a_e_is_max = a_e == 255;
        b_e_is_zero = b_e == 0;
        b_e_is_max = b_e == 255;
        a_m_is_zero = a_m == 0;
        b_m_is_zero = b_m == 0;

        a_is_zero = a_e_is_zero && a_m_is_zero;
        a_is_inf = a_e_is_max && a_m_is_zero;
        a_is_nan = a_e_is_max && !a_m_is_zero;
        a_is_subnorm = a_e_is_zero && !a_m_is_zero;

        b_is_zero = b_e_is_zero && b_m_is_zero;
        b_is_inf = b_e_is_max && b_m_is_zero;
        b_is_nan = b_e_is_max && !b_m_is_zero;
        b_is_subnorm = b_e_is_zero && !b_m_is_zero;

        t_e = a_e + b_e - 2 * bias + a_is_subnorm + b_is_subnorm + 1;
        *z1_e = (a_is_zero || b_is_zero) ? 772 : t_e; // 输入有一个为0时，指数位为-252\772\10'b11_00000100

        e_overflow_pos = !EXTRACT_BITS(t_e, 9, 9) && EXTRACT_BITS(t_e, 8, 8);
        e_overflow_neg = EXTRACT_BITS(t_e, 9, 9) && (!EXTRACT_BITS(t_e, 8, 8));

        z_is_nan = (a_is_nan || b_is_nan) || (a_is_inf && b_is_zero) || (a_is_zero && b_is_inf);
        // 判断是否为0         输入为0×非特殊值
        z_is_zero = (a_is_zero && !b_is_nan && !b_is_inf) || (b_is_zero && !a_is_nan && !a_is_inf);
        // 判断是否为Inf       输入为inf×非0非NaN
        z_is_inf = (a_is_inf && !b_is_zero && !b_is_nan) || (b_is_inf && !a_is_zero && !a_is_nan) || e_overflow_pos || e_overflow_neg;

        a_hide_bit = (!a_is_subnorm) && (!a_is_zero) && (!a_is_inf && !a_is_nan);
        b_hide_bit = (!b_is_subnorm) && (!b_is_zero) && (!b_is_inf && !b_is_nan);

        t_M[0] = JOIN_BITS(a_hide_bit, a_m);
        t_M[1] = JOIN_BITS(b_hide_bit, b_m);
        t_mul = t_M[0] * t_M[1];
        z_s = a_s != b_s;
        if (z_s)
        {
            if (t_mul != 0) // 尾数部分计算输出非0正常取补码
                t_mul = -t_mul;
            else if (a_is_zero || b_is_zero) // a,b输入为0导致的0正常输出0
                t_mul = 0;
            else                 // inf导致的尾数部分给mul子模块的输入为0导致的输出0
                t_mul = 4194304; // 符号为拓展会给0的最高位补1变成23'h100_0000_0000_0000_0000_0000
        }
        z_M = t_mul;
        *z0_e = 0;
        // assign z_m                  = {{6{1'b0}}, z1_status_1r[2:0], z_m1_1[22: 0]&{23{~ab1_is_zero_1r}} }
        z_status = JOIN_BITS(z_is_zero, z_is_inf, z_is_nan);
        *z_m = CONCAT_BITS(*z_m, z_status, 23);
        *z_m = CONCAT_BITS(*z_m, z_M, 0);
    }
    else if (op_mode == 8)
    { // fp4

        int t_e;
        int t_M[2];
        int t_mul;

        _u1 z_s[4];
        _u5 z_M[4];
        _u4 a_fp4[4];
        _u4 b_fp4[4];
        _u2 a_e[4];
        _u2 a_E[4];
        _u2 b_e[4];
        _u2 b_E[4];
        _u3 z_e[4];
        _u1 a_m[4];
        _u1 b_m[4];
        _u1 a_s[4];
        _u1 b_s[4];

        _u1 a_is_zero[4];
        _u1 b_is_zero[4];

        _u1 z_is_zero[4];

        for (int i = 0; i < 4; i++)
        {
            if (i <= 1)
            {
                a_fp4[i] = EXTRACT_BITS(a, (i + 1) * 4 - 1, i * 4);
                b_fp4[i] = EXTRACT_BITS(b, (i + 1) * 4 - 1, i * 4);
            }
            else
            {
                a_fp4[i] = EXTRACT_BITS(a, (i + 1) * 4, i * 4 + 1);
                b_fp4[i] = EXTRACT_BITS(b, (i + 1) * 4, i * 4 + 1);
            }
            a_s[i] = EXTRACT_BITS(a_fp4[i], 3, 3);
            b_s[i] = EXTRACT_BITS(b_fp4[i], 3, 3);
            z_s[i] = a_s[i] != b_s[i];
            a_e[i] = EXTRACT_BITS(a_fp4[i], 2, 1);
            a_E[i] = (a_e[i] > 0x01) ? (a_e[i] - 1) : 0;
            b_e[i] = EXTRACT_BITS(b_fp4[i], 2, 1);
            b_E[i] = (b_e[i] > 0x01) ? b_e[i] : 1;
            a_is_zero[i] = EXTRACT_BITS(a_fp4[i], 2, 0) == 0;
            b_is_zero[i] = EXTRACT_BITS(b_fp4[i], 2, 0) == 0;
            z_is_zero[i] = a_is_zero[i] || b_is_zero[i];
            z_e[i] = z_is_zero[i] ? 0 : a_E[i] + b_E[i];

            a_m[i] = EXTRACT_BITS(a_fp4[i], 0, 0);
            b_m[i] = EXTRACT_BITS(b_fp4[i], 0, 0);

            t_M[0] = JOIN_BITS(a_e[i] != 0, a_m[i]);
            t_M[1] = JOIN_BITS(b_e[i] != 0, b_m[i]);
            t_mul = t_M[0] * t_M[1];
            if (z_s[i])
            {
                //  if(t_mul!= 0)  //尾数部分计算输出非0正常取补码
                t_mul = -t_mul;
                //  else //应该就剩这个判断了
                //      t_mul=16 ;//'b10000
            }
            z_M[i] = t_mul;
        }
        *z0_e = JOIN_BITS(z_e[2], z_e[0]);
        *z1_e = JOIN_BITS(z_e[3], z_e[1]);

        *z_m = CONCAT_BITS(*z_m, z_is_zero[3], 31);
        *z_m = CONCAT_BITS(*z_m, z_M[3], 24);
        *z_m = CONCAT_BITS(*z_m, z_is_zero[2], 23);
        *z_m = CONCAT_BITS(*z_m, z_M[2], 16);
        *z_m = CONCAT_BITS(*z_m, z_is_zero[1], 15);
        *z_m = CONCAT_BITS(*z_m, z_M[1], 8);
        *z_m = CONCAT_BITS(*z_m, z_is_zero[0], 7);
        *z_m = CONCAT_BITS(*z_m, z_M[0], 0);
    }
}

// 11. 主函数（测试用例）
int main()
{
    // 声明
    _u4 op_mode;           // 操作模式选择：4'b0001=int8, 4'b0010=fp8, 4'b0100=tf32, 4'b1000=fp4
    _u1 i_gp_zero_skip_en; // 全局零值跳过使能信号
    _u19 a;                // 19位输入操作数a
    _u19 b;                // 19位输入操作数b
    _u6 ref_z0_e;          // 第一个乘法结果的指数部分
    _u9 ref_z1_e;          // 第二个乘法结果的指数部分
    _u32 ref_z_m;          // 乘法结果的尾数部分
    // 测试输入设置
    //  op_mode=1;
    //  a=0;
    //  b=0;

    // op_mode=2;
    // _u9 a_fp8=0x08;
    // _u9 b_fp8=0x08;
    // a=JOIN_BITS(a_fp8, a_fp8);
    // b=JOIN_BITS(b_fp8, b_fp8);

    // op_mode=8;
    //  _u4 a_fp8=0x1;
    //  _u4 b_fp8=0x1;
    //  a=a_fp8;
    //  b=b_fp8;
    // i_gp_zero_skip_en=0;
    //__CPROVER_assume(op_mode == 1); // 4.624s
    //  __CPROVER_assume(op_mode == 2); // 0.132s
    //__CPROVER_assume(op_mode == 4); // 402.787s
    // __CPROVER_assume(op_mode == 8); // 0.093s
    __CPROVER_assume(op_mode == 1 || op_mode == 2 || op_mode == 4 || op_mode == 8); // 447.086s
    ne_fp_ffp_mul.op_mode = op_mode;
    ne_fp_ffp_mul.i_gp_zero_skip_en = i_gp_zero_skip_en;
    ne_fp_ffp_mul.a = a;
    ne_fp_ffp_mul.b = b;

    set_inputs();
    c_ne_fp_ffp_mul(op_mode, a, b, &ref_z0_e, &ref_z1_e, &ref_z_m);

    printf("act_z0_e: %d\n", ne_fp_ffp_mul.z0_e);
    printf("ref_z0_e: %d\n", ref_z0_e);
    printf("act_z1_e: %d\n", ne_fp_ffp_mul.z1_e);
    printf("ref_z1_e: %d\n", ref_z1_e);

    assert(ne_fp_ffp_mul.z0_e == ref_z0_e);
    assert(ne_fp_ffp_mul.z1_e == ref_z1_e);

    next_timeframe();

    printf("ref_z_m: %d\n", ref_z_m);
    printf("act_z_m: %d\n", ne_fp_ffp_mul.z_m);
    printf("act_mul_z0: %d\n", ne_fp_ffp_mul.mul_z0);
    printf("act_mul_z1: %d\n", ne_fp_ffp_mul.mul_z1);
    assert(ne_fp_ffp_mul.z_m == ref_z_m);
    return 0;
}