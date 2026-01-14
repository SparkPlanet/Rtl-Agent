#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
#include <assert.h>
#include "common.h"

void next_timeframe(void);
void set_inputs(void);
extern const unsigned int bound;

typedef unsigned __CPROVER_bitvector[96] _u96;
typedef unsigned __CPROVER_bitvector[144] _u144;

struct ne_fp_ffp_e_align
{
    _u4 op_mode;       // 操作模式选择信号
    _u144 a_e;         // TF32格式指数输入 (16个元素 × 9位)
    _u96 b_e;          // FP8格式指数输入 (16个元素 × 6位)
    _u9 e_max;         // 最大指数输出
    _u96 a_e_sub;      // a_e与e_max的差值 (16个元素 × 6位)
    _u96 b_e_sub;      // b_e与e_max的差值 (16个元素 × 6位)
    _u16 a_e_overflow; // a_e溢出标志
    _u16 b_e_overflow; // b_e溢出标志
};

extern struct ne_fp_ffp_e_align ne_fp_ffp_e_align;

void c_ne_fp_ffp_e_align(
    _u4 op_mode,
    _u144 a_e,
    _u96 b_e,
    _u9 *e_max,
    _u6 (*a_e_sub_array)[16],
    _u6 (*b_e_sub_array)[16],
    _u16 *a_e_overflow,
    _u16 *b_e_overflow)
{
    // 1. 初始化输出信号
    *e_max = 0;
    for (int i = 0; i < 16; i++)
    {
        (*a_e_sub_array)[i] = 0; // 修改访问方式
        (*b_e_sub_array)[i] = 0; // 修改访问方式
    }
    *a_e_overflow = 0;
    *b_e_overflow = 0;

    // 2. 中间变量声明
    _u9 a_e_slice[16];
    _u6 b_e_slice[16];
    for (int i = 0; i < 16; i++)
    {
        a_e_slice[i] = a_e >> i * 9;
        b_e_slice[i] = b_e >> i * 6;
    }
    _u9 a_e_max = a_e_slice[0];
    for (int i = 1; i < 16; i++)
    {
        if (IS_MAX(a_e_slice[i], a_e_max, 1))
        {
            a_e_max = a_e_slice[i];
        }
    }
    _u6 b_e_max = b_e_slice[0];
    for (int i = 1; i < 16; i++)
    {
        if (IS_MAX(b_e_slice[i], b_e_max, 1))
        {
            b_e_max = b_e_slice[i];
        }
    }

    if (op_mode == 1)
    { // int8
        ;
    }
    else if (op_mode == 2)
    { // fp8
        // wire [9:0]   bias   = 10'b1_111100100:   // -14 + (-14) = -28
        _u9 a_bias = 0x1E4; // a_e的偏置 -28
        _u6 b_bias = 0x24;  // b_e的偏置 -28
        if (IS_MAX(a_bias, a_e_max, 1))
        {
            a_e_max = a_bias;
        }
        if (IS_MAX(b_bias, b_e_max, 1))
        {
            b_e_max = b_bias;
        }
        _u9 b_e_max_extend = SIGN_EXTEND(b_e_max, 9);
        if (IS_MAX(a_e_max, b_e_max_extend, 1))
        {
            *e_max = a_e_max;
        }
        else
        {
            *e_max = b_e_max_extend;
        }

        _u9 t_sub = 0;
        _u9 t_b_e_extend = 0;
        _u6 t_low = 0;
        for (int i = 0; i < 16; i++)
        {
            t_sub = SYM_SUB(*e_max, a_e_slice[i], 1);
            (*a_e_sub_array)[i] = t_sub; // 只取低6位
            t_low = t_sub;
            if (t_low >= 25)
            {
                // 这个溢出条件是怎么样？？？？？
                (*a_e_overflow) |= (1 << i);
            }

            t_b_e_extend = SIGN_EXTEND(b_e_slice[i], 9);
            t_sub = SYM_SUB(*e_max, t_b_e_extend, 1);
            (*b_e_sub_array)[i] = t_sub; // 只取低6位
            t_low = t_sub;
            if (t_low >= 25)
            {
                // 这个溢出条件是怎么样？？？？？
                (*b_e_overflow) |= (1 << i);
            }
        }
    }
    else if (op_mode == 8)
    { // fp4
        // 除了溢出全为0，emax写死。其余与fp8一致
        *e_max = 0x02D;
        _u9 t_sub = 0;
        _u9 t_b_e_extend = 0;
        _u6 t_low = 0;
        for (int i = 0; i < 16; i++)
        {
            t_sub = SYM_SUB(*e_max, a_e_slice[i], 1);
            (*a_e_sub_array)[i] = t_sub; // 只取低6位
            t_low = t_sub;

            t_b_e_extend = SIGN_EXTEND(b_e_slice[i], 9);
            t_sub = SYM_SUB(*e_max, t_b_e_extend, 1);
            (*b_e_sub_array)[i] = t_sub; // 只取低6位
            t_low = t_sub;
        }
    }
}

int main()
{
    // 声明
    _u4 op_mode;
    _u144 a_e;
    _u96 b_e;

    _u9 e_max;
    _u16 a_e_overflow;
    _u16 b_e_overflow;

    // 使用命名联合
    union a_e_sub_union
    {
        _u96 a_e_sub;
        _u6 a_e_sub_array[16];
    } a_e_union;

    union b_e_sub_union
    {
        _u96 b_e_sub;
        _u6 b_e_sub_array[16];
    } b_e_union;

    __CPROVER_assume(op_mode == 1 || op_mode == 2 || op_mode == 8);
    // op_mode=8;
    // op_mode=4;
    // op_mode=1;
    // op_mode=2;
    ne_fp_ffp_e_align.op_mode = op_mode;
    ne_fp_ffp_e_align.a_e = a_e;
    ne_fp_ffp_e_align.b_e = b_e;
    set_inputs();
    c_ne_fp_ffp_e_align(
        op_mode,
        a_e,
        b_e,
        &e_max,
        &a_e_union.a_e_sub_array, // 通过命名联合访问数组
        &b_e_union.b_e_sub_array, // 通过命名联合访问数组
        &a_e_overflow,
        &b_e_overflow);
    next_timeframe();
    next_timeframe();

    // printf("ref_e_max: %d\n", e_max);
    // printf("act_e_max: %d\n", ne_fp_ffp_e_align.e_max);
    assert(e_max == ne_fp_ffp_e_align.e_max);

    // _u6 act_final=0;
    // _u6 ref_final=0;
    // for(int i=0; i<16; i++) {
    //     ref_final=a_e_union.a_e_sub>>i*6;
    //     act_final=ne_fp_ffp_e_align.a_e_sub>>i*6;
    //     if(ref_final != act_final) {
    //         printf("ref_a_e_sub: %d\n",ref_final);
    //         printf("act_a_e_sub: %d\n",act_final);
    //     }
    // }
    assert(a_e_union.a_e_sub == ne_fp_ffp_e_align.a_e_sub);

    // for(int i=0; i<16; i++) {
    //     ref_final=b_e_union.b_e_sub>>i*6;
    //     act_final=ne_fp_ffp_e_align.b_e_sub>>i*6;
    //     if(ref_final != act_final) {
    //         printf("ref_b_e_sub: %d\n",ref_final);
    //         printf("act_b_e_sub: %d\n",act_final);
    //     }
    // }
    assert(b_e_union.b_e_sub == ne_fp_ffp_e_align.b_e_sub);

    // printf("ref_a_e_overflow: %d\n", a_e_overflow);
    // printf("act_a_e_overflow: %d\n", ne_fp_ffp_e_align.a_e_overflow);
    assert(ne_fp_ffp_e_align.a_e_overflow == a_e_overflow);

    // printf("ref_b_e_overflow: %d\n", b_e_overflow);
    // printf("act_b_e_overflow: %d\n", ne_fp_ffp_e_align.b_e_overflow);
    assert(ne_fp_ffp_e_align.b_e_overflow == b_e_overflow);
    return 0;
}