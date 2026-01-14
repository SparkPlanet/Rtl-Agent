#include <assert.h>
#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>


#ifndef MASK
#define MASK(w) ((((uint64_t)1) << (w)) - 1)
#endif
#define MASK64(w)    ((w) >= 64 ? (~0ULL) : ((1ULL << (w)) - 1))
#define GET_BITS(val, high, low) (((val) >> (low)) & MASK((high) - (low) + 1))
// #define BIT_WIDTH(x) _Generic((x), _u1: 1, _u2: 2, _u3: 3, _u4: 4, _u5: 5, _u6: 6, _u7: 7, _u8: 8, _u9: 9, _u10: 10, _u11: 11, _u12: 12, _u13: 13, _u14: 14, _u15: 15, _u16: 16, _u17: 17, _u18: 18, _u19: 19, _u20: 20, _u21: 21, _u22: 22, _u23: 23, _u24: 24, _u25: 25, _u26: 26, _u27: 27, _u28: 28, _u29: 29, _u30: 30, _u31: 31, _u32: 32, _u33: 33, _u34: 34, _u35: 35, _u36: 36, _u37: 37, _u38: 38, _u39: 39, _u40: 40, _u41: 41, _u42: 42, _u43: 43, _u44: 44, _u45: 45, _u46: 46, _u47: 47, _u48: 48, _u49: 49, _u50: 50, _u51: 51, _u52: 52, _u53: 53, _u54: 54, _u55: 55, _u56: 56, _u57: 57, _u58: 58, _u59: 59, _u60: 60, _u61: 61, _u62: 62, _u63: 63, default: -1)
#define BIT_WIDTH(x) _Generic((x),_u1: 1, _u2: 2, _u3: 3, _u4: 4, _u5: 5, _u6: 6, _u7: 7, _u8: 8, _u9: 9, _u10: 10, _u11: 11, _u12: 12, _u13: 13, _u14: 14, _u15: 15, _u16: 16, _u17: 17, _u18: 18, _u19: 19, _u20: 20, _u21: 21, _u22: 22, _u23: 23, _u24: 24, _u25: 25, _u26: 26, _u27: 27, _u28: 28, _u29: 29, _u30: 30, _u31: 31, _u32: 32, _u33: 33, _u34: 34, _u35: 35, _u36: 36, _u37: 37, _u38: 38, _u39: 39, _u40: 40, _u41: 41, _u42: 42, _u43: 43, _u44: 44, _u45: 45, _u46: 46, _u47: 47, _u48: 48, _u49: 49, _u50: 50, _u51: 51, _u52: 52, _u53: 53, _u54: 54, _u55: 55, _u56: 56, _u57: 57, _u58: 58, _u59: 59, _u60: 60, _u61: 61, _u62: 62, _u63: 63, \
                                  _s1: 1, _s2: 2, _s3: 3, _s4: 4, _s5: 5, _s6: 6, _s7: 7, _s8: 8, _s9: 9, _s10: 10, _s11: 11, _s12: 12, _s13: 13, _s14: 14, _s15: 15, _s16: 16, _s17: 17, _s18: 18, _s19: 19, _s20: 20, _s21: 21, _s22: 22, _s23: 23, _s24: 24, _s25: 25, _s26: 26, _s27: 27, _s28: 28, _s29: 29, _s30: 30, _s31: 31, _s32: 32, _s33: 33, _s34: 34, _s35: 35, _s36: 36, _s37: 37, _s38: 38, _s39: 39, _s40: 40, _s41: 41, _s42: 42, _s43: 43, _s44: 44, _s45: 45, _s46: 46, _s47: 47, _s48: 48, _s49: 49, _s50: 50, _s51: 51, _s52: 52, _s53: 53, _s54: 54, _s55: 55, _s56: 56, _s57: 57, _s58: 58, _s59: 59, _s60: 60, _s61: 61, _s62: 62, _s63: 63, \
                              default: -1)
#define EXTRACT_BITS(a, high, low)  (((a) >> (low)) & ((1ULL << ((high) - (low) + 1)) - 1))
#define CHECK_SIGN_BIT(x) (EXTRACT_BITS(x, BIT_WIDTH(x) - 1, BIT_WIDTH(x) - 1))
#define SIGN_EXTEND(x, dest_width) ((CHECK_SIGN_BIT(x) == 1) ? (x | (((1ULL << (dest_width - BIT_WIDTH(x))) - 1) << BIT_WIDTH(x))) : x)
#define CONCAT_BITS(dest, src, low) (((dest) & ~(((1ULL << BIT_WIDTH(src)) - 1) << (low))) | (((src) & ((1ULL << BIT_WIDTH(src)) - 1)) << (low)))
// 拼接两个值的宏
#define _JOIN_BITS_2(high, low) ((high) << BIT_WIDTH(low) | (low))
// 拼接三个值的宏
#define _JOIN_BITS_3(high, middle, low) _JOIN_BITS_2(_JOIN_BITS_2(high, middle), low)

// 宏重载实现 - 支持2或3个参数
#define _JOIN_BITS_N(_1, _2, _3, N, ...) N
#define JOIN_BITS(...) _JOIN_BITS_N(__VA_ARGS__, _JOIN_BITS_3, _JOIN_BITS_2)(__VA_ARGS__)

// 3. 比较宏 - 详细文档请参考 common.md
#define IS_MAX(a, b, tc) ((tc == 0) ? (a >= b) : (CHECK_SIGN_BIT(a) == CHECK_SIGN_BIT(b) ? a >= b : CHECK_SIGN_BIT(a) == 0))
#define IS_MIN(a, b, tc) ((tc == 0) ? (a < b) : (CHECK_SIGN_BIT(a) == CHECK_SIGN_BIT(b) ? a < b : CHECK_SIGN_BIT(a) == 1))
#define FIND_MAX(a, b, tc) IS_MAX(a, b, tc) ? a : b
#define FIND_MIN(a, b, tc) IS_MIN(a, b, tc) ? a : b

// 4. 符号减法宏 - 支持有符号和无符号减法
// 参数: a - 被减数, b - 减数, tc - 有符号标志(0:无符号, 1:有符号)
// 返回: a - b 的结果，保持与输入相同的位宽
#define SYM_SUB(a, b, tc) ((tc == 0) ? ((a) - (b)) : ((SIGN_EXTEND(a, BIT_WIDTH(a) + 1) - SIGN_EXTEND(b, BIT_WIDTH(b) + 1)) & ((1ULL << BIT_WIDTH(a)) - 1)))

#define MASK_128(w) ((((unsigned __int128)1) << (w)) - 1)
// 提取 bits [high:low]
#define SLICE(val, high, low) (((val) >> (low)) & MASK_128((high) - (low) + 1))
// 获取单 bit
#define BIT(val, idx) (((val) >> (idx)) & 1)
// 拼接 {a, b}，其中 width_b 是 b 的位宽
#define CAT(a, b, width_b) ((((unsigned __int128)(a)) << (width_b)) | ((unsigned __int128)(b) & MASK_128(width_b)))
#define MAX_TREE_INPUTS 64

typedef unsigned __CPROVER_bitvector[1] _u1;
typedef unsigned __CPROVER_bitvector[2] _u2;
typedef unsigned __CPROVER_bitvector[3] _u3;
typedef unsigned __CPROVER_bitvector[4] _u4;
typedef unsigned __CPROVER_bitvector[5] _u5;
typedef unsigned __CPROVER_bitvector[6] _u6;
typedef unsigned __CPROVER_bitvector[7] _u7;
typedef unsigned __CPROVER_bitvector[8] _u8;
typedef unsigned __CPROVER_bitvector[9] _u9;
typedef unsigned __CPROVER_bitvector[10] _u10;
typedef unsigned __CPROVER_bitvector[11] _u11;
typedef unsigned __CPROVER_bitvector[12] _u12;
typedef unsigned __CPROVER_bitvector[13] _u13;
typedef unsigned __CPROVER_bitvector[14] _u14;
typedef unsigned __CPROVER_bitvector[15] _u15;
typedef unsigned __CPROVER_bitvector[16] _u16;
typedef unsigned __CPROVER_bitvector[17] _u17;
typedef unsigned __CPROVER_bitvector[18] _u18;
typedef unsigned __CPROVER_bitvector[19] _u19;
typedef unsigned __CPROVER_bitvector[20] _u20;
typedef unsigned __CPROVER_bitvector[21] _u21;
typedef unsigned __CPROVER_bitvector[22] _u22;
typedef unsigned __CPROVER_bitvector[23] _u23;
typedef unsigned __CPROVER_bitvector[24] _u24;
typedef unsigned __CPROVER_bitvector[25] _u25;
typedef unsigned __CPROVER_bitvector[26] _u26;
typedef unsigned __CPROVER_bitvector[27] _u27;
typedef unsigned __CPROVER_bitvector[28] _u28;
typedef unsigned __CPROVER_bitvector[29] _u29;
typedef unsigned __CPROVER_bitvector[30] _u30;
typedef unsigned __CPROVER_bitvector[31] _u31;
typedef unsigned __CPROVER_bitvector[32] _u32;
typedef unsigned __CPROVER_bitvector[33] _u33;
typedef unsigned __CPROVER_bitvector[34] _u34;
typedef unsigned __CPROVER_bitvector[35] _u35;
typedef unsigned __CPROVER_bitvector[36] _u36;
typedef unsigned __CPROVER_bitvector[37] _u37;
typedef unsigned __CPROVER_bitvector[38] _u38;
typedef unsigned __CPROVER_bitvector[39] _u39;
typedef unsigned __CPROVER_bitvector[40] _u40;
typedef unsigned __CPROVER_bitvector[41] _u41;
typedef unsigned __CPROVER_bitvector[42] _u42;
typedef unsigned __CPROVER_bitvector[43] _u43;
typedef unsigned __CPROVER_bitvector[44] _u44;
typedef unsigned __CPROVER_bitvector[45] _u45;
typedef unsigned __CPROVER_bitvector[46] _u46;
typedef unsigned __CPROVER_bitvector[47] _u47;
typedef unsigned __CPROVER_bitvector[48] _u48;
typedef unsigned __CPROVER_bitvector[49] _u49;
typedef unsigned __CPROVER_bitvector[50] _u50;
typedef unsigned __CPROVER_bitvector[51] _u51;
typedef unsigned __CPROVER_bitvector[52] _u52;
typedef unsigned __CPROVER_bitvector[53] _u53;
typedef unsigned __CPROVER_bitvector[54] _u54;
typedef unsigned __CPROVER_bitvector[55] _u55;
typedef unsigned __CPROVER_bitvector[56] _u56;
typedef unsigned __CPROVER_bitvector[57] _u57;
typedef unsigned __CPROVER_bitvector[58] _u58;
typedef unsigned __CPROVER_bitvector[59] _u59;
typedef unsigned __CPROVER_bitvector[60] _u60;
typedef unsigned __CPROVER_bitvector[61] _u61;
typedef unsigned __CPROVER_bitvector[62] _u62;
typedef unsigned __CPROVER_bitvector[63] _u63;
typedef unsigned __CPROVER_bitvector[96] _u96;
typedef unsigned __CPROVER_bitvector[144] _u144;
typedef unsigned __CPROVER_bitvector[512] _u512;
//1. 自定义位宽类型
typedef signed __CPROVER_bitvector[1]  _s1;
typedef signed __CPROVER_bitvector[2]  _s2;
typedef signed __CPROVER_bitvector[3]  _s3;
typedef signed __CPROVER_bitvector[4]  _s4;
typedef signed __CPROVER_bitvector[5]  _s5;
typedef signed __CPROVER_bitvector[6]  _s6;
typedef signed __CPROVER_bitvector[7]  _s7;
typedef signed __CPROVER_bitvector[8]  _s8;
typedef signed __CPROVER_bitvector[9]  _s9;
typedef signed __CPROVER_bitvector[10] _s10;
typedef signed __CPROVER_bitvector[11] _s11;
typedef signed __CPROVER_bitvector[12] _s12;
typedef signed __CPROVER_bitvector[13] _s13;
typedef signed __CPROVER_bitvector[14] _s14;
typedef signed __CPROVER_bitvector[15] _s15;
typedef signed __CPROVER_bitvector[16] _s16;
typedef signed __CPROVER_bitvector[17] _s17;
typedef signed __CPROVER_bitvector[18] _s18;
typedef signed __CPROVER_bitvector[19] _s19;
typedef signed __CPROVER_bitvector[20] _s20;
typedef signed __CPROVER_bitvector[21] _s21;
typedef signed __CPROVER_bitvector[22] _s22;
typedef signed __CPROVER_bitvector[23] _s23;
typedef signed __CPROVER_bitvector[24] _s24;
typedef signed __CPROVER_bitvector[25] _s25;
typedef signed __CPROVER_bitvector[26] _s26;
typedef signed __CPROVER_bitvector[27] _s27;
typedef signed __CPROVER_bitvector[28] _s28;
typedef signed __CPROVER_bitvector[29] _s29;
typedef signed __CPROVER_bitvector[30] _s30;
typedef signed __CPROVER_bitvector[31] _s31;
typedef signed __CPROVER_bitvector[32] _s32;
typedef signed __CPROVER_bitvector[33] _s33;
typedef signed __CPROVER_bitvector[34] _s34;
typedef signed __CPROVER_bitvector[35] _s35;
typedef signed __CPROVER_bitvector[36] _s36;
typedef signed __CPROVER_bitvector[37] _s37;
typedef signed __CPROVER_bitvector[38] _s38;
typedef signed __CPROVER_bitvector[39] _s39;
typedef signed __CPROVER_bitvector[40] _s40;
typedef signed __CPROVER_bitvector[41] _s41;
typedef signed __CPROVER_bitvector[42] _s42;
typedef signed __CPROVER_bitvector[43] _s43;
typedef signed __CPROVER_bitvector[44] _s44;
typedef signed __CPROVER_bitvector[45] _s45;
typedef signed __CPROVER_bitvector[46] _s46;
typedef signed __CPROVER_bitvector[47] _s47;
typedef signed __CPROVER_bitvector[48] _s48;
typedef signed __CPROVER_bitvector[49] _s49;
typedef signed __CPROVER_bitvector[50] _s50;
typedef signed __CPROVER_bitvector[51] _s51;
typedef signed __CPROVER_bitvector[52] _s52;
typedef signed __CPROVER_bitvector[53] _s53;
typedef signed __CPROVER_bitvector[54] _s54;
typedef signed __CPROVER_bitvector[55] _s55;
typedef signed __CPROVER_bitvector[56] _s56;
typedef signed __CPROVER_bitvector[57] _s57;
typedef signed __CPROVER_bitvector[58] _s58;
typedef signed __CPROVER_bitvector[59] _s59;
typedef signed __CPROVER_bitvector[60] _s60;
typedef signed __CPROVER_bitvector[61] _s61;
typedef signed __CPROVER_bitvector[62] _s62;
typedef signed __CPROVER_bitvector[63] _s63;


typedef struct {
    _u32 fp_z;
    _u1  fp_z_vld;
    _u1  fp_z_int;
    _u2  fp_infnan;
} ne_dot_out_t;


static int64_t sign_extend(uint64_t val, int width) {
    if (val & (1ULL << (width - 1))) {
        return (int64_t)(val | ~MASK(width));
    }
    return (int64_t)val;
}
static int64_t sext(uint64_t val, int w) {
    return (val & (1ULL << (w - 1))) ? (val | ~MASK(w)) : val;
}

// ---------------------------------------------------------
// 2. 子模块：ne_dw_add (封装 DW01_add)
// ---------------------------------------------------------
void DW01_add1(uint32_t A, uint32_t B, uint32_t CI, uint32_t *SUM, uint32_t *CO) {
    uint64_t tmp = (uint64_t)A + (uint64_t)B + (uint64_t)CI;
    *SUM = (uint32_t)tmp;
    *CO  = (uint32_t)(tmp >> 32);
}

uint64_t ne_dw_add(uint64_t adder_a, uint64_t adder_b, int bw_adder) {
    uint32_t sum_out, co_dummy;
    DW01_add1((uint32_t)adder_a, (uint32_t)adder_b, 0, &sum_out, &co_dummy);
    uint64_t raw_sum = adder_a + adder_b; 
    return raw_sum & MASK(bw_adder);
}




// Hardware Adder Simulation
uint32_t ne_dw_add_M26(uint32_t adder_a, uint32_t adder_b) {
    const int P_BW_ADDER = 29;
    return (adder_a + adder_b) & (uint32_t)MASK(P_BW_ADDER);
}
uint32_t ne_dw_add_M27(uint32_t adder_a, uint32_t adder_b) {
    const int P_BW_ADDER = 30;
    return (adder_a + adder_b) & (uint32_t)MASK(P_BW_ADDER);
}

static int64_t sext_custom(uint64_t val, int w) {
    if ((val >> (w - 1)) & 1) {
        return val | ~MASK64(w);
    } else {
        return val;
    }
}

void c_DW02_mult_i8(
    _u8	A,
    _u8	B,
    _u1	TC,
    _u16	*PRODUCT
) {
    if (TC == 0) {
        *PRODUCT = A * B;
    } else {
        _u8 a_bit_inv = ~A;  
        _u8 b_bit_inv = ~B;   
        _u16 A_abs = CHECK_SIGN_BIT(A) ? a_bit_inv+1 : A;
        _u16 B_abs = CHECK_SIGN_BIT(B) ? b_bit_inv+1 : B;
        _u16 product_abs = A_abs * B_abs;
        *PRODUCT = (CHECK_SIGN_BIT(A) == CHECK_SIGN_BIT(B)) ? product_abs : ~product_abs + 1;
    }
}

void c_ne_dw_ffp_mul(
    _u4        op_mode              ,  // 操作模式选择：4'b0001=int8, 4'b0010=fp8, 4'b0100=tf32, 4'b1000=fp4
    _u19       a                    ,  // 19位输入操作数a
    _u19       b                    ,  // 19位输入操作数b
    _u6        *z0_e                ,  // 第一个乘法结果的指数部分
    _u9        *z1_e                ,  // 第二个乘法结果的指数部分
    _u32       *z_m                    // 乘法结果的尾数部分    
) {
    *z_m=0;
    *z0_e=0;
    *z1_e=0;

    if(op_mode == 1) { //int8
        _u8	a_int[2];
        _u8	b_int[2];
        _u16 z_int[2];
        a_int[0]=EXTRACT_BITS(a, 7, 0);
        a_int[1]=EXTRACT_BITS(a, 16, 9);
        b_int[0]=EXTRACT_BITS(b, 7, 0);
        b_int[1]=EXTRACT_BITS(b, 16, 9);
        
        c_DW02_mult_i8(a_int[0], b_int[0], 1, &z_int[0]);
        c_DW02_mult_i8(a_int[1], b_int[1], 1, &z_int[1]);
        *z_m = JOIN_BITS(z_int[1], z_int[0]);
        // *z_m = ((_u32)z_int[1] << 16) | ((_u32)z_int[0]);
        *z0_e = 0;
        *z1_e = 0;
    } else if(op_mode == 2) { //fp8
        int bias= 15;
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
        _u1 a_e_is_zero[2];//指数位全0
        _u1 a_e_is_max[2];//指数位全1
        _u1 b_e_is_zero[2];
        _u1 b_e_is_max[2];
        _u1 a_m_is_zero[2];//尾数位全0
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

        for(int i=0;i<2;i++){
            a_fp8[i]=EXTRACT_BITS(a, (i+1)*9-1, i*9);
            b_fp8[i]=EXTRACT_BITS(b, (i+1)*9-1, i*9);   
            a_s[i]=EXTRACT_BITS(a_fp8[i], 8, 8);
            b_s[i]=EXTRACT_BITS(b_fp8[i], 8, 8);
            a_e[i]=EXTRACT_BITS(a_fp8[i], 7, 3);
            b_e[i]=EXTRACT_BITS(b_fp8[i], 7, 3);
            a_m[i]=EXTRACT_BITS(a_fp8[i], 2, 0);
            b_m[i]=EXTRACT_BITS(b_fp8[i], 2, 0);
            a_e_is_zero[i]=a_e[i]==0;
            a_e_is_max[i] =a_e[i]==31;
            b_e_is_zero[i]=b_e[i]==0;
            b_e_is_max[i] =b_e[i]==31;
            a_m_is_zero[i]=a_m[i]==0;
            b_m_is_zero[i]=b_m[i]==0; 

            a_is_zero[i]=a_e_is_zero[i]&&a_m_is_zero[i];
            a_is_inf[i]=a_e_is_max[i]&&a_m_is_zero[i];
            a_is_nan[i]=a_e_is_max[i]&&!a_m_is_zero[i];
            a_is_subnorm[i]=a_e_is_zero[i]&&!a_m_is_zero[i];

            b_is_zero[i]=b_e_is_zero[i]&&b_m_is_zero[i];
            b_is_inf[i]=b_e_is_max[i]&&b_m_is_zero[i];
            b_is_nan[i]=b_e_is_max[i]&&!b_m_is_zero[i];
            b_is_subnorm[i]=b_e_is_zero[i]&&!b_m_is_zero[i];

            a_hide_bit = (!a_is_subnorm[i]) && (!a_is_zero[i]) && (!a_is_inf[i] && !a_is_nan[i]);
            b_hide_bit = (!b_is_subnorm[i]) && (!b_is_zero[i]) && (!b_is_inf[i] && !b_is_nan[i]);
            t_M[0]=JOIN_BITS(a_hide_bit, a_m[i]);
            t_M[1]=JOIN_BITS(b_hide_bit, b_m[i]);
            t_mul=t_M[0]*t_M[1];
            z_s= a_s[i]!=b_s[i];
            if(z_s){
                if(t_mul!= 0)  //尾数部分计算输出非0正常取补码
                    t_mul=-t_mul;
                else if(a_is_zero[i]||b_is_zero[i])//a,b输入为0导致的0正常输出0
                    t_mul=0 ;
                else //inf导致的尾数部分给mul子模块的输入为0导致的输出0
                    t_mul=256 ; //符号为拓展会给0的最高位补1变成9'h100000000
            }
            z_M[i]=t_mul;
            //加这个1是处于什么目的
            t_e=a_e[i]+b_e[i] - 2 * bias + a_is_subnorm[i] + b_is_subnorm[i] +1; 
            if(i==0){
                *z0_e=(a_is_zero[i]||b_is_zero[i])? 484 :t_e; //输入有一个为0时，指数位为-28\484\9'h1_11100100 
            }else{
                *z1_e=(a_is_zero[i]||b_is_zero[i])? 484 :t_e;
            }
            //判断是否为NaN或Inf  输入为NaN或者0×inf
            z_is_nan[i]=(a_is_nan[i]||b_is_nan[i])||(a_is_inf[i]&&b_is_zero[i])||(a_is_zero[i]&&b_is_inf[i]);
            //判断是否为0         输入为0×非特殊值
            z_is_zero[i]=(a_is_zero[i]&&!b_is_nan[i]&&!b_is_inf[i])||(b_is_zero[i]&&!a_is_nan[i]&&!a_is_inf[i]);
            //判断是否为Inf       输入为inf×非0非NaN
            z_is_inf[i]=(a_is_inf[i]&&!b_is_zero[i]&&!b_is_nan[i])||(b_is_inf[i]&&!a_is_zero[i]&&!a_is_nan[i]);
        }

        //z_status[0] = {z_is_zero[0], z_is_inf[0], z_is_nan[0]};
        z_status[0] = JOIN_BITS(z_is_zero[0], z_is_inf[0], z_is_nan[0]);
        z_status[1] = JOIN_BITS(z_is_zero[1], z_is_inf[1], z_is_nan[1]);
        *z_m = CONCAT_BITS(*z_m,z_status[1],25);
        *z_m = CONCAT_BITS(*z_m,z_M[1],16);
        *z_m = CONCAT_BITS(*z_m,z_status[0],9);
        *z_m = CONCAT_BITS(*z_m,z_M[0],0);
    } else if(op_mode == 4) { //tf32
        int bias= 127;
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

        _u1 a_e_is_zero;//指数位全0
        _u1 a_e_is_max;//指数位全1
        _u1 b_e_is_zero;
        _u1 b_e_is_max;
        _u1 a_m_is_zero;//尾数位全0
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
        _u1 z_is_inf ;
        _u1 z_is_nan ;
        _u3 z_status ;

        _u1 a_hide_bit; 
        _u1 b_hide_bit; 
        
        a_tf32=EXTRACT_BITS(a, 18, 0);
        b_tf32=EXTRACT_BITS(b, 18, 0);   
        a_s=EXTRACT_BITS(a_tf32, 18, 18);
        b_s=EXTRACT_BITS(b_tf32, 18, 18);
        a_e=EXTRACT_BITS(a_tf32, 17, 10);
        b_e=EXTRACT_BITS(b_tf32, 17, 10);
        a_m=EXTRACT_BITS(a_tf32, 9, 0);
        b_m=EXTRACT_BITS(b_tf32, 9, 0);
        a_e_is_zero=a_e==0;
        a_e_is_max =a_e==255;
        b_e_is_zero=b_e==0;
        b_e_is_max =b_e==255;
        a_m_is_zero=a_m==0;
        b_m_is_zero=b_m==0; 

        a_is_zero=a_e_is_zero&&a_m_is_zero;
        a_is_inf=a_e_is_max&&a_m_is_zero;
        a_is_nan=a_e_is_max&&!a_m_is_zero;
        a_is_subnorm=a_e_is_zero&&!a_m_is_zero;

        b_is_zero=b_e_is_zero&&b_m_is_zero;
        b_is_inf=b_e_is_max&&b_m_is_zero;
        b_is_nan=b_e_is_max&&!b_m_is_zero;
        b_is_subnorm=b_e_is_zero&&!b_m_is_zero;
        
        t_e=a_e+b_e - 2 * bias + a_is_subnorm + b_is_subnorm +1; 
        *z1_e=(a_is_zero||b_is_zero)? 772 :t_e; //输入有一个为0时，指数位为-252\772\10'b11_00000100

        e_overflow_pos = !EXTRACT_BITS(t_e,9,9)&&EXTRACT_BITS(t_e,8,8);
        e_overflow_neg = EXTRACT_BITS(t_e,9,9)&&(!EXTRACT_BITS(t_e,8,8));

        z_is_nan=(a_is_nan||b_is_nan)||(a_is_inf&&b_is_zero)||(a_is_zero&&b_is_inf);
        //判断是否为0         输入为0×非特殊值
        z_is_zero=(a_is_zero&&!b_is_nan&&!b_is_inf)||(b_is_zero&&!a_is_nan&&!a_is_inf);
        //判断是否为Inf       输入为inf×非0非NaN
        z_is_inf=(a_is_inf&&!b_is_zero&&!b_is_nan)||(b_is_inf&&!a_is_zero&&!a_is_nan)||e_overflow_pos||e_overflow_neg;

        a_hide_bit = (!a_is_subnorm) && (!a_is_zero) && (!a_is_inf && !a_is_nan);
        b_hide_bit = (!b_is_subnorm) && (!b_is_zero) && (!b_is_inf && !b_is_nan);

        t_M[0]=JOIN_BITS(a_hide_bit, a_m);
        t_M[1]=JOIN_BITS(b_hide_bit, b_m);
        t_mul=t_M[0]*t_M[1];
        z_s= a_s!=b_s;
        if(z_s){
            if(t_mul!= 0)  //尾数部分计算输出非0正常取补码
                t_mul=-t_mul;
            else if(a_is_zero||b_is_zero)//a,b输入为0导致的0正常输出0
                t_mul=0 ;
            else //inf导致的尾数部分给mul子模块的输入为0导致的输出0
                t_mul=4194304 ; //符号为拓展会给0的最高位补1变成23'h100_0000_0000_0000_0000_0000
        }
        z_M=t_mul;
        *z0_e = 0;
        //assign z_m                  = {{6{1'b0}}, z1_status_1r[2:0], z_m1_1[22: 0]&{23{~ab1_is_zero_1r}} }
        z_status=JOIN_BITS(z_is_zero, z_is_inf, z_is_nan);
        *z_m = CONCAT_BITS(*z_m,z_status,23);
        *z_m = CONCAT_BITS(*z_m,z_M,0);

    } else if(op_mode == 8) { //fp4

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

        for(int i=0;i<4;i++){
            if(i<=1) {
                a_fp4[i]=EXTRACT_BITS(a, (i+1)*4-1, i*4);
                b_fp4[i]=EXTRACT_BITS(b, (i+1)*4-1, i*4);
            } else  {
                a_fp4[i]=EXTRACT_BITS(a, (i+1)*4, i*4+1);
                b_fp4[i]=EXTRACT_BITS(b, (i+1)*4, i*4+1);  
            }
            a_s[i]=EXTRACT_BITS(a_fp4[i], 3, 3);
            b_s[i]=EXTRACT_BITS(b_fp4[i], 3, 3);
            z_s[i]= a_s[i]!=b_s[i];
            a_e[i]=EXTRACT_BITS(a_fp4[i], 2, 1);
            a_E[i]=(a_e[i]>0x01)? (a_e[i]-1) : 0;
            b_e[i]=EXTRACT_BITS(b_fp4[i], 2, 1);
            b_E[i]=(b_e[i]>0x01)? b_e[i] : 1;
            a_is_zero[i]=EXTRACT_BITS(a_fp4[i], 2, 0)==0;
            b_is_zero[i]=EXTRACT_BITS(b_fp4[i], 2, 0)==0;
            z_is_zero[i]=a_is_zero[i]||b_is_zero[i];
            z_e[i]=z_is_zero[i]? 0 : a_E[i]+b_E[i];
            
            a_m[i]=EXTRACT_BITS(a_fp4[i], 0, 0);
            b_m[i]=EXTRACT_BITS(b_fp4[i], 0, 0);

            t_M[0]=JOIN_BITS(a_e[i]!=0, a_m[i]);
            t_M[1]=JOIN_BITS(b_e[i]!=0, b_m[i]);
            t_mul=t_M[0]*t_M[1];
            if(z_s[i]){
                //  if(t_mul!= 0)  //尾数部分计算输出非0正常取补码
                     t_mul=-t_mul;
                //  else //应该就剩这个判断了
                //      t_mul=16 ;//'b10000
            }
            z_M[i]=t_mul;     
        }
        *z0_e=JOIN_BITS(z_e[2],z_e[0]);
        *z1_e=JOIN_BITS(z_e[3],z_e[1]);

        *z_m = CONCAT_BITS(*z_m,z_is_zero[3],31);
        *z_m = CONCAT_BITS(*z_m,z_M[3],24);
        *z_m = CONCAT_BITS(*z_m,z_is_zero[2],23);
        *z_m = CONCAT_BITS(*z_m,z_M[2],16);
        *z_m = CONCAT_BITS(*z_m,z_is_zero[1],15);
        *z_m = CONCAT_BITS(*z_m,z_M[1],8);
        *z_m = CONCAT_BITS(*z_m,z_is_zero[0],7);
        *z_m = CONCAT_BITS(*z_m,z_M[0],0);
    }
}


_u48 c_ne_fp_ffp_add_mix(_u47 din_a, _u47 din_b, _u4 din_mode) {
    const int P_SWI=1;
    const int P_EWI=10;
    const int P_MWI=33;
    const int P_BW_STATUS=3;
    const int P_BW_INT_I=21;
    const int P_BIAS_VAL= 127;
    const int P_BW_INT_O= 23;
    const int P_BW_ADDER=36;
    const int P_SWO=1;
    const int P_EWO=10;
    const int P_MWO=34;
    const int P_BW_Z_DATA=45;
    const int P_BW_Z_TOTAL=48;
    // -----------------------------------------------------
    // 1. Unpack Logic (RTL: gen_unpack_with_status)
    // -----------------------------------------------------
    _u3  a_status, b_status;
    _u1  a_s, b_s;
    _u10 a_e, b_e;
    _u33 a_m, b_m;

    // din_mode[0] == 0 implies FP mode in RTL logic (~mode[0])
    bool mode_fp = ((din_mode & 1) == 0);

    if (mode_fp) {
        // Unpack A
        a_status = (_u3)(din_a >> 44);
        a_s      = (_u1)(din_a >> 43);
        a_e      = (_u10)(din_a >> 33);
        a_m      = (_u33)(din_a); 

        // Unpack B
        b_status = (_u3)(din_b >> 44);
        b_s      = (_u1)(din_b >> 43);
        b_e      = (_u10)(din_b >> 33);
        b_m      = (_u33)(din_b);
    } else {
        // Zero out for Integer mode (RTL logic)
        a_status = 0; a_s = 0; a_e = 0; a_m = 0;
        b_status = 0; b_s = 0; b_e = 0; b_m = 0;
    }

    _u1 a_is_nan  = (a_status >> 2) & 1;
    _u1 a_is_inf  = (a_status >> 1) & 1;
    _u1 a_is_zero = (a_status >> 0) & 1;

    _u1 b_is_nan  = (b_status >> 2) & 1;
    _u1 b_is_inf  = (b_status >> 1) & 1;
    _u1 b_is_zero = (b_status >> 0) & 1;

    // -----------------------------------------------------
    // 2. Alignment Logic (FP Only)
    // -----------------------------------------------------
    int64_t ae_s_val = sext_custom((uint64_t)a_e, P_EWI);
    int64_t be_s_val = sext_custom((uint64_t)b_e, P_EWI);
    
    _u33 lg_m, sm_m;
    _u10 lg_e;
    _u1  lg_m_s, sm_m_s;
    int64_t e_sub_val;

    // RTL: assign ae_lt_be = $signed(a_e) < $signed(b_e);
    if (ae_s_val < be_s_val) {
        lg_m = b_m; sm_m = a_m;
        lg_e = b_e; 
        e_sub_val = be_s_val - ae_s_val;
    } else {
        lg_m = a_m; sm_m = b_m;
        lg_e = a_e; 
        e_sub_val = ae_s_val - be_s_val;
    }

    lg_m_s = (lg_m >> 32) & 1;
    sm_m_s = (sm_m >> 32) & 1;

    // RTL: sfr_overflow logic
    int64_t sfr_limit = ((din_mode >> 3) & 1) ? 24 : 31;
    int64_t bias_i = P_BIAS_VAL;
    
    _u1 align_overflow = 0;
    // if ((e_sub_val > sfr_limit) || (e_sub_val > bias_i + 1) || (e_sub_val < -bias_i)) {
    //     align_overflow = 1;
    // }
  if ((e_sub_val > sfr_limit) ) {
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

    if (align_overflow) {
        sm_final = sm_m_s ? (_u33)(~0) : (_u33)0; // {MWI{small_m_s}}
        align_norm_bit = 0; 
    } else {
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

    if (!mode_fp) { // INT Mode (din_mode[0] == 1)
        int_a0 = (_u21)din_a; 
        int_b0 = (_u21)din_b;
        
        // RTL: adder_a_t = {{(BW_ADDER-BW_INT_I){int_a0[MSB]}}, int_a0}
        // Sign extend 21-bit int to 36-bit adder input
        adder_a = (_u36)sext_custom((uint64_t)int_a0, P_BW_INT_I);
        adder_b = (_u36)sext_custom((uint64_t)int_b0, P_BW_INT_I);
    } else { // FP Mode
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

    if (!mode_fp) {
        // === INT Output (RTL: INT_CH=1 Logic) ===
        // BW_INT_O = 23 (21+2)
        // int_z0 logic checks adder_z[22:21]
        
        _u23 int_z0;
        _u2 top_bits = (_u2)((adder_z >> (P_BW_INT_O - 2)) & 3); // Bits 22:21

        if (top_bits == 1) {        // 2'b01: Pos Overflow
            // RTL: {2'b00, 1'b0, {(BW_INT_I-1){1'b1}}} -> 000111...11
            // Bit 22,21=00, Bit 20=0, Bits 19-0=1
            int_z0 = (_u23)(MASK64(P_BW_INT_I - 1)); 
        } else if (top_bits == 2) { // 2'b10: Neg Overflow
            // RTL: {2'b11, 1'b1, {(BW_INT_I-1){1'b0}}} -> 111000...00
            // Bit 22,21=11, Bit 20=1, Bits 19-0=0
            // This is effectively - (2^20)? No, it's constructing a specific pattern.
            // 111 followed by 20 zeros.
            int_z0 = (_u23)(((_u23)7 << (P_BW_INT_I - 1))); 
        } else {
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
        _u1 e_bit_9  = (z_e0_val >> 9) & 1;  // MSB of 10-bit result
        _u1 e_bit_8  = (z_e0_val >> 8) & 1;  // MSB-1

        // The RTL logic for e_overflow_pos/neg depends on the extended bit width
        // Let's assume standard behavior:
        // RTL: e_overflow_pos = ~z_e0_t[EWI-1] & z_e0_t[EWI-2]; (Indices 9 and 8)
        _u1 e_overflow_pos = !e_bit_9 && e_bit_8; 
        
        // Wait, z_e0_t is 10 bits. EWI=10. EWI-1=9. EWI-2=8.
        // It seems the RTL logic is checking wrap-around based on sign bits.
        // Since we did 64-bit calc, we can check value ranges directly?
        // RTL relies on bit manipulation. Let's stick to bits.
        // _u1 z_e_overflow1 = e_overflow_pos; // Simplified for this context as pos overflow forces Inf
        _u1 z_e_overflow1 =0;
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
        
        if (int_sign) {
            // Fill top bits (44 down to 23) with 1s
            final_z_o = (_u45)int_z0 | ((_u45)(~0) << P_BW_INT_O); 
        } else {
            final_z_o = (_u45)int_z0;
        }
        z_res_nan  = z_nan;
        z_res_inf  = z_inf;
        z_res_zero = z_zero;
    } else {
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
        _u1 e_bit_9  = (z_e0_val >> 9) & 1;  // MSB of 10-bit result
        _u1 e_bit_8  = (z_e0_val >> 8) & 1;  // MSB-1

        // The RTL logic for e_overflow_pos/neg depends on the extended bit width
        // Let's assume standard behavior:
        // RTL: e_overflow_pos = ~z_e0_t[EWI-1] & z_e0_t[EWI-2]; (Indices 9 and 8)
        _u1 e_overflow_pos = !e_bit_9 && e_bit_8; 
        
        // Wait, z_e0_t is 10 bits. EWI=10. EWI-1=9. EWI-2=8.
        // It seems the RTL logic is checking wrap-around based on sign bits.
        // Since we did 64-bit calc, we can check value ranges directly?
        // RTL relies on bit manipulation. Let's stick to bits.
        // _u1 z_e_overflow1 = e_overflow_pos; // Simplified for this context as pos overflow forces Inf
        _u1 z_e_overflow1 =0;
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

        if (z_nan) {
            final_z_o = pkt_nan;
        } else if (z_inf) {
            final_z_o = pkt_inf;
        } else if (z_zero) {
            final_z_o = pkt_zero;
        } else {
            final_z_o = pkt_norm;
        }

        z_res_nan  = z_nan;
        z_res_inf  = z_inf;
        z_res_zero = z_zero;
    }
    // z_res_nan  = z_nan;
    // z_res_inf  = z_inf;
    // z_res_zero = z_zero;
    // -----------------------------------------------------
    // 6. Final Pack
    // -----------------------------------------------------
    _u3 z_status_out;

    // if (mode_fp) {
        // RTL: z_status = {z_is_nan, z_is_inf, z_is_zero}
        z_status_out = ((_u3)z_res_nan << 2) | ((_u3)z_res_inf << 1) | (_u3)z_res_zero;
    // } else {
        // In INT mode, status bits are just passed through or zeroed in some designs.
        // RTL "gen_out_with_status" packs z_is_nan etc.
        // But in INT mode "z_is_nan" logic depends on inputs which were zeroed.
        // Actually, z_nan/inf/zero logic still runs in INT mode based on zeroed inputs, 
        // usually resulting in zero status unless overflow logic sets them.
        // However, RTL "int_out" block sets z_o directly.
        // The status bits in INT mode usually reflect the Muxed FP flags, which are based on 0 inputs -> 0.
    //     z_status_out = 0; 
    // }

    _u48 z_out = ((_u48)z_status_out << 45) | (_u48)final_z_o;

    return z_out;
}


uint64_t c_ne_fp_ffp_add_mwi26(uint64_t a, uint64_t b, uint8_t mode) {
    const int P_SWI=1;
    const int P_EWI=10;
    const int P_MWI=26;
    const int P_BW_STATUS=3;
    const int P_MWO=(P_MWI + 1);
    const int P_BWA=(P_BW_STATUS + P_SWI + P_EWI + P_MWI);
    const int P_BWZ=(P_BW_STATUS + P_SWI + P_EWI + P_MWO);
    const int P_BIAS_I= 127;
    const int P_BIAS_Z= 127;
    const int P_BIAS_Z_NEG=-127;
    const int P_BW_ESUB=5;
    const int P_BW_ADDER=29;
    // --- Step 1: Unpacking (Verilog Section 3) ---
    // Offset calculation: 1 + 10 + 26 = 37
    int offset = P_SWI + P_EWI + P_MWI; 

    // Extract raw fields
    uint8_t a_status = (uint8_t)GET_BITS(a, P_BWA - 1, offset);
    uint8_t a_s      = (uint8_t)GET_BITS(a, offset - 1, offset - P_SWI);
    uint16_t a_e     = (uint16_t)GET_BITS(a, offset - P_SWI - 1, P_MWI);
    uint32_t a_m     = (uint32_t)GET_BITS(a, P_MWI - 1, 0);

    uint8_t b_status = (uint8_t)GET_BITS(b, P_BWA - 1, offset);
    uint8_t b_s      = (uint8_t)GET_BITS(b, offset - 1, offset - P_SWI);
    uint16_t b_e     = (uint16_t)GET_BITS(b, offset - P_SWI - 1, P_MWI);
    uint32_t b_m     = (uint32_t)GET_BITS(b, P_MWI - 1, 0);

    // Decode Status
    bool a_is_nan  = (a_status >> 2) & 1;
    bool a_is_inf  = (a_status >> 1) & 1;
    bool a_is_zero = (a_status >> 0) & 1;

    bool b_is_nan  = (b_status >> 2) & 1;
    bool b_is_inf  = (b_status >> 1) & 1;
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
    bool align_overflow = (e_sub > (P_MWI - 2));
    uint8_t e_sub_m = (uint8_t)(e_sub & MASK(P_BW_ESUB)); // Lower 5 bits

    // *** Signed Shift ***
    int32_t small_m_signed = (int32_t)sign_extend(small_m, P_MWI); 
    int32_t small_m_shifted = small_m_signed >> e_sub_m; 
    uint32_t small_m_align0 = (uint32_t)small_m_shifted & (uint32_t)MASK(P_MWI);

    // Alignment Muxing
    uint32_t small_m_align;
    if (align_overflow) {
        small_m_align = small_m_s ? (uint32_t)MASK(P_MWI) : 0;
    } else {
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
    uint32_t adder_z = ne_dw_add_M26(adder_a_t, adder_b_t);

    // --- Step 6: Post Processing (Verilog Section 6) ---
    // Verilog: assign z_m = adder_z[MWI+2:2];
    // Extracts bits from MWI+2 down to 2. Width = (MWI+2)-2 + 1 = MWI+1 = MWO
    uint32_t z_m = (adder_z >> 2) & (uint32_t)MASK(P_MWO); 
    
    // Status Logic
    bool z_inf_nan_t = a_is_inf && b_is_inf && (a_s ^ b_s);
    bool z_is_nan_t  = a_is_nan || b_is_nan || z_inf_nan_t;
    bool z_is_inf_t  = (a_is_inf || b_is_inf) && !z_is_nan_t;
    
    bool z_is_zero_t = a_is_zero && b_is_zero;
    bool z_is_zero   = z_is_zero_t || ((z_m == 0) && !(z_is_inf_t || z_is_nan_t));

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
    uint16_t z_e_zero_val = (uint16_t)((uint8_t)P_BIAS_Z_NEG);

    // Normal Result
    uint64_t z_d = ((uint64_t)z_s << (P_EWI + P_MWO)) | ((uint64_t)z_e_t << P_MWO) | z_m;

    // NaN Packet
    uint64_t nan_payload = ((uint64_t)z_s_nan << (P_MWO-1)) | 
                           ((uint64_t)z_s_nan << (P_MWO-2)) | 
                           (1ULL << (P_MWO-3));
    uint64_t z_nan = ((uint64_t)z_s_nan << (P_EWI + P_MWO)) | 
                     ((uint64_t)z_e_max << P_MWO) | 
                     nan_payload;

    // Inf Packet
    uint64_t inf_payload = ((uint64_t)z_s_inf << (P_MWO-1)) | 
                           ((uint64_t)z_s_inf << (P_MWO-2));
    uint64_t z_inf = ((uint64_t)z_s_inf << (P_EWI + P_MWO)) | 
                     ((uint64_t)z_e_max << P_MWO) | 
                     inf_payload;

    // Zero Packet
    uint64_t zero_payload = ((uint64_t)z_s << (P_MWO-1)) | 
                            ((uint64_t)z_s << (P_MWO-2));
    uint64_t z_zero = ((uint64_t)z_s << (P_EWI + P_MWO)) | 
                      ((uint64_t)z_e_zero_val << P_MWO) | 
                      zero_payload;

    // Final Mux
    uint64_t z_o;
    if (z_is_nan_t)       z_o = z_nan;
    else if (z_is_inf_t)  z_o = z_inf;
    else if (z_is_zero)   z_o = z_zero;
    else                  z_o = z_d;

    // Append Status Bits
    uint64_t final_z = z_o;
    if (P_BW_STATUS > 0) {
        uint64_t status = ((uint64_t)z_is_nan_t << 2) | ((uint64_t)z_is_inf_t << 1) | z_is_zero;
        int core_width = P_SWI + P_EWI + P_MWO; 
        final_z = (status << core_width) | (z_o & MASK(core_width));
    }

    return final_z;
}



uint64_t c_ne_fp_ffp_add_mwi27(uint64_t a, uint64_t b, uint8_t mode) {
    const int P_SWI=1;
    const int P_EWI=10;
    const int P_MWI=27;
    const int P_BW_STATUS=3;
    const int P_MWO=(P_MWI + 1);
    const int P_BWA=(P_BW_STATUS + P_SWI + P_EWI + P_MWI);
    const int P_BWZ=(P_BW_STATUS + P_SWI + P_EWI + P_MWO);
    const int P_BIAS_I= 127;
    const int P_BIAS_Z= 127;
    const int P_BIAS_Z_NEG=-127;
    const int P_BW_ESUB=5;
    const int P_BW_ADDER=30;
    // --- Step 1: Unpacking (Verilog Section 3) ---
    // Offset calculation: 1 + 10 + 26 = 37
    int offset = P_SWI + P_EWI + P_MWI; 

    // Extract raw fields
    uint8_t a_status = (uint8_t)GET_BITS(a, P_BWA - 1, offset);
    uint8_t a_s      = (uint8_t)GET_BITS(a, offset - 1, offset - P_SWI);
    uint16_t a_e     = (uint16_t)GET_BITS(a, offset - P_SWI - 1, P_MWI);
    uint32_t a_m     = (uint32_t)GET_BITS(a, P_MWI - 1, 0);

    uint8_t b_status = (uint8_t)GET_BITS(b, P_BWA - 1, offset);
    uint8_t b_s      = (uint8_t)GET_BITS(b, offset - 1, offset - P_SWI);
    uint16_t b_e     = (uint16_t)GET_BITS(b, offset - P_SWI - 1, P_MWI);
    uint32_t b_m     = (uint32_t)GET_BITS(b, P_MWI - 1, 0);

    // Decode Status
    bool a_is_nan  = (a_status >> 2) & 1;
    bool a_is_inf  = (a_status >> 1) & 1;
    bool a_is_zero = (a_status >> 0) & 1;

    bool b_is_nan  = (b_status >> 2) & 1;
    bool b_is_inf  = (b_status >> 1) & 1;
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
    bool align_overflow = (e_sub > (P_MWI - 2));
    uint8_t e_sub_m = (uint8_t)(e_sub & MASK(P_BW_ESUB)); // Lower 5 bits

    // *** Signed Shift ***
    int32_t small_m_signed = (int32_t)sign_extend(small_m, P_MWI); 
    int32_t small_m_shifted = small_m_signed >> e_sub_m; 
    uint32_t small_m_align0 = (uint32_t)small_m_shifted & (uint32_t)MASK(P_MWI);

    // Alignment Muxing
    uint32_t small_m_align;
    if (align_overflow) {
        small_m_align = small_m_s ? (uint32_t)MASK(P_MWI) : 0;
    } else {
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
    uint32_t adder_z = ne_dw_add_M27(adder_a_t, adder_b_t);

    // --- Step 6: Post Processing (Verilog Section 6) ---
    // Verilog: assign z_m = adder_z[MWI+2:2];
    // Extracts bits from MWI+2 down to 2. Width = (MWI+2)-2 + 1 = MWI+1 = MWO
    uint32_t z_m = (adder_z >> 2) & (uint32_t)MASK(P_MWO); 
    
    // Status Logic
    bool z_inf_nan_t = a_is_inf && b_is_inf && (a_s ^ b_s);
    bool z_is_nan_t  = a_is_nan || b_is_nan || z_inf_nan_t;
    bool z_is_inf_t  = (a_is_inf || b_is_inf) && !z_is_nan_t;
    
    bool z_is_zero_t = a_is_zero && b_is_zero;
    bool z_is_zero   = z_is_zero_t || ((z_m == 0) && !(z_is_inf_t || z_is_nan_t));

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
    uint16_t z_e_zero_val = (uint16_t)((uint8_t)P_BIAS_Z_NEG);

    // Normal Result
    uint64_t z_d = ((uint64_t)z_s << (P_EWI + P_MWO)) | ((uint64_t)z_e_t << P_MWO) | z_m;

    // NaN Packet
    uint64_t nan_payload = ((uint64_t)z_s_nan << (P_MWO-1)) | 
                           ((uint64_t)z_s_nan << (P_MWO-2)) | 
                           (1ULL << (P_MWO-3));
    uint64_t z_nan = ((uint64_t)z_s_nan << (P_EWI + P_MWO)) | 
                     ((uint64_t)z_e_max << P_MWO) | 
                     nan_payload;

    // Inf Packet
    uint64_t inf_payload = ((uint64_t)z_s_inf << (P_MWO-1)) | 
                           ((uint64_t)z_s_inf << (P_MWO-2));
    uint64_t z_inf = ((uint64_t)z_s_inf << (P_EWI + P_MWO)) | 
                     ((uint64_t)z_e_max << P_MWO) | 
                     inf_payload;

    // Zero Packet
    uint64_t zero_payload = ((uint64_t)z_s << (P_MWO-1)) | 
                            ((uint64_t)z_s << (P_MWO-2));
    uint64_t z_zero = ((uint64_t)z_s << (P_EWI + P_MWO)) | 
                      ((uint64_t)z_e_zero_val << P_MWO) | 
                      zero_payload;

    // Final Mux
    uint64_t z_o;
    if (z_is_nan_t)       z_o = z_nan;
    else if (z_is_inf_t)  z_o = z_inf;
    else if (z_is_zero)   z_o = z_zero;
    else                  z_o = z_d;

    // Append Status Bits
    uint64_t final_z = z_o;
    if (P_BW_STATUS > 0) {
        uint64_t status = ((uint64_t)z_is_nan_t << 2) | ((uint64_t)z_is_inf_t << 1) | z_is_zero;
        int core_width = P_SWI + P_EWI + P_MWO; 
        final_z = (status << core_width) | (z_o & MASK(core_width));
    }

    return final_z;
}



typedef struct {
    uint64_t out0;
    uint64_t out1;
} TreeResult;

TreeResult ne_dw_add_tree(const uint64_t* inputs, int num_inputs, int input_width) {
    uint64_t mask = (input_width >= 64) ? 0xFFFFFFFFFFFFFFFFULL : MASK(input_width);
    uint64_t cur_ops[64];
    uint64_t nxt_ops[64];
    int count = num_inputs;

    for(int i=0; i<num_inputs; i++) cur_ops[i] = inputs[i] & mask;

    while(count > 2) {
        int n_idx = 0;
        int grps = count / 3;
        int rem = count % 3;

        for(int i=0; i<grps; i++) {
            uint64_t a = cur_ops[i*3];
            uint64_t b = cur_ops[i*3+1];
            uint64_t c = cur_ops[i*3+2];
            uint64_t sum = a ^ b ^ c;
            uint64_t carry = (a&b) | (b&c) | (a&c);
            nxt_ops[n_idx++] = sum & mask;
            nxt_ops[n_idx++] = (carry << 1) & mask;
        }
        for(int i=0; i<rem; i++) nxt_ops[n_idx++] = cur_ops[grps*3 + i];
        for(int i=0; i<n_idx; i++) cur_ops[i] = nxt_ops[i];
        count = n_idx;
    }

    TreeResult res;
    res.out0 = cur_ops[0] & mask;
    res.out1 = (count > 1) ? (cur_ops[1] & mask) : 0;
    return res;
}

static uint64_t get_sub_slice(const uint32_t* arr, int idx, int width) {
    int bit_start = idx * 6; 
    int arr_idx = bit_start / 32;
    int off = bit_start % 32;
    uint64_t val = arr[arr_idx];
    if (off + width > 32) val |= ((uint64_t)arr[arr_idx+1] << 32);
    return (val >> off) & MASK(width);
}

// =========================================================
// 5. 主模型 (直接对齐 RTL 接口)
// =========================================================

typedef struct {
    uint64_t z;      
    uint64_t z_fp4;  
} VectorM33Result;

// [修改] 参数列表现在直接使用 HW-CBMC 的 bitvector，与 Verilog 端口一一对应
VectorM33Result c_ne_fp_ffp_add_vector_m33(
    _u4     bv_op_mode,
    _u9     bv_e_max,
    _u18    bv_ab_scale,
    _u96    bv_ae_sub,      // 16*6 = 96
    _u96    bv_be_sub,      // 16*6 = 96
    _u16    bv_a_e_overflow,
    _u16    bv_b_e_overflow,
    _u512   bv_a_m         // 16*32 = 512
) {
    // -----------------------------------------------------
    // A. 内部转换逻辑 (在此处完成拆包)
    // -----------------------------------------------------
    uint32_t op_mode = (uint32_t)bv_op_mode;
    uint32_t e_max   = (uint32_t)bv_e_max;
    uint32_t ab_scale= (uint32_t)bv_ab_scale;
    uint32_t a_e_overflow = (uint32_t)bv_a_e_overflow;
    uint32_t b_e_overflow = (uint32_t)bv_b_e_overflow;

    // 转换 a_m (512 bits -> uint32_t array)
    uint32_t a_m_arr[16];
    for(int i=0; i<16; i++) {
        a_m_arr[i] = (uint32_t)(bv_a_m >> (i*32));
    }

    // 转换 ae_sub / be_sub (96 bits -> uint32_t array)
    // 3个 uint32 (96 bit)
    uint32_t ae_sub_arr[3];
    uint32_t be_sub_arr[3];
    for(int i=0; i<3; i++) {
        ae_sub_arr[i] = (uint32_t)(bv_ae_sub >> (i*32));
        be_sub_arr[i] = (uint32_t)(bv_be_sub >> (i*32));
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

    for (int i = 0; i < 16; i++) {
        uint64_t am_slice = a_m_arr[i]; 

        uint64_t status_tf32  = (op_mode & 4) ? GET_BITS(am_slice, 25, 23) : 0;
        uint64_t status_fp8_1 = (op_mode & 2) ? GET_BITS(am_slice, 27, 25) : 0;
        uint64_t status_fp8_0 = (op_mode & 2) ? GET_BITS(am_slice, 11, 9) : 0;

        // TF32 Status
        bool a_tf32_zero = BIT(status_tf32, 2);
        bool a_tf32_inf  = BIT(status_tf32, 1);
        bool a_tf32_nan  = BIT(status_tf32, 0);
        bool sign_tf32   = BIT(am_slice, 22);
        
        bool a_tf32_pinf = a_tf32_inf && (a_tf32_inf ^ sign_tf32);
        bool a_tf32_ninf = a_tf32_inf && sign_tf32;

        z_tf32_zero_t &= a_tf32_zero;
        z_tf32_nan_t  |= a_tf32_nan;
        z_tf32_inf_t_raw |= a_tf32_inf;
        
        global_tf32_pinf |= a_tf32_pinf;
        global_tf32_ninf |= a_tf32_ninf;

        // FP8 Status
        bool a_fp8_zero = BIT(status_fp8_1, 2);
        bool a_fp8_inf  = BIT(status_fp8_1, 1);
        bool a_fp8_nan  = BIT(status_fp8_1, 0);
        bool sign_fp8_a = BIT(am_slice, 24);
        
        bool b_fp8_zero = BIT(status_fp8_0, 2);
        bool b_fp8_inf  = BIT(status_fp8_0, 1);
        bool b_fp8_nan  = BIT(status_fp8_0, 0);
        bool sign_fp8_b = BIT(am_slice, 8);

        bool a_fp8_pinf = a_fp8_inf && (a_fp8_inf ^ sign_fp8_a);
        bool a_fp8_ninf = a_fp8_inf && sign_fp8_a;
        bool b_fp8_pinf = b_fp8_inf && (b_fp8_inf ^ sign_fp8_b);
        bool b_fp8_ninf = b_fp8_inf && sign_fp8_b;

        z_fp8_zero_t &= (a_fp8_zero & b_fp8_zero);
        z_fp8_nan_t  |= (a_fp8_nan | b_fp8_nan); 
        z_fp8_inf_t_raw |= (a_fp8_inf | b_fp8_inf);
        
        global_fp8_pinf |= (a_fp8_pinf | b_fp8_pinf);
        global_fp8_ninf |= (a_fp8_ninf | b_fp8_ninf);

        // FP4 Zero Check
        bool op3 = (op_mode & 8) != 0;
        bool a_fp4_z = op3 && BIT(am_slice, 15);
        bool b_fp4_z = op3 && BIT(am_slice, 7);
        bool a1_fp4_z = op3 && BIT(am_slice, 31);
        bool b1_fp4_z = op3 && BIT(am_slice, 23);

        if (i < 8) z_fp4_is_zero  &= (a_fp4_z & b_fp4_z & a1_fp4_z & b1_fp4_z);
        else       z1_fp4_is_zero &= (a_fp4_z & b_fp4_z & a1_fp4_z & b1_fp4_z);

        // Mantissa & Alignment
        uint64_t m_fp4_a = (op_mode & 8) ? GET_BITS(am_slice, 12, 8) : 0;
        uint64_t m_fp4_b = (op_mode & 8) ? GET_BITS(am_slice, 4, 0) : 0;
        uint64_t m_tf32  = (op_mode & 4) ? GET_BITS(am_slice, 22, 0) : 0;
        uint64_t m_fp8_1 = (op_mode & 2) ? GET_BITS(am_slice, 24, 16) : 0;
        uint64_t m_fp8_0 = (op_mode & 2) ? GET_BITS(am_slice, 8, 0) : 0;
        uint64_t m_int8_1 = (op_mode & 1) ? GET_BITS(am_slice, 31, 16) : 0;
        uint64_t m_int8_0 = (op_mode & 1) ? GET_BITS(am_slice, 15, 0) : 0;

        uint64_t am_fp_1, am_fp_0;
        if (op_mode & 8) { 
            uint64_t s = BIT(m_fp4_a, 4);
            am_fp_1 = (s ? MASK(22)<<9 : 0) | (m_fp4_a << 4);
            s = BIT(m_fp4_b, 4);
            am_fp_0 = (s ? MASK(21)<<9 : 0) | (m_fp4_b << 4);
        } else if (op_mode & 4) { 
            uint64_t s = BIT(m_tf32, 22);
            am_fp_1 = (s ? MASK(4)<<27 : 0) | (m_tf32 << 4);
            am_fp_0 = 0;
        } else { 
            uint64_t s = BIT(m_fp8_1, 8);
            am_fp_1 = (s ? MASK(5)<<26 : 0) | (m_fp8_1 << 17);
            s = BIT(m_fp8_0, 8);
            am_fp_0 = (s ? MASK(4)<<26 : 0) | (m_fp8_0 << 17);
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

        if (op_mode & 1) { 
            uint64_t s1 = BIT(m_int8_1, 15);
            adder_in_01_raw[i] = (s1 ? MASK(4)<<16 : 0) | m_int8_1; 
            uint64_t s0 = BIT(m_int8_0, 15);
            adder_in_00_raw[i] = (s0 ? MASK(4)<<16 : 0) | m_int8_0; 
        } else {
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
        uint64_t am1_fp_1 = (s_a1 ? MASK(5)<<9 : 0) | (m_fp4_a1 << 4);
        uint64_t s_b1 = BIT(m_fp4_b1, 4);
        uint64_t am1_fp_0 = (s_b1 ? MASK(5)<<9 : 0) | (m_fp4_b1 << 4);

        int64_t am1_sfr_1 = sext(am1_fp_1, 14) >> a1_e_sh;
        int64_t am1_sfr_0 = sext(am1_fp_0, 14) >> b1_e_sh;

        fp4_add_in_11[i] = (am1_sfr_1 << 1) & MASK(15);
        fp4_add_in_10[i] = (am1_sfr_0 << 1) & MASK(15);
    }

    // Post-Loop Assembly
    for (int i = 0; i < 8; i++) {
        if (op_mode & 8) {
            adder_in_2[i*2+0] = adder_in_00_raw[i+8] & MASK(15);
            adder_in_2[i*2+1] = adder_in_01_raw[i+8] & MASK(15);
        } else {
            adder_in_2[i*2+0] = 0;
            adder_in_2[i*2+1] = 0;
        }
    }

    for (int i = 8; i < 16; i++) {
        if (op_mode & 8) {
            adder_in_1[i] = sext(fp4_add_in_11[i-8], 15) & MASK(32);
            adder_in_0[i] = sext(fp4_add_in_10[i-8], 15) & MASK(31);
            adder_in_2[i*2+0] = fp4_add_in_10[i];
            adder_in_2[i*2+1] = fp4_add_in_11[i];
        } else {
            adder_in_2[i*2+0] = 0;
            adder_in_2[i*2+1] = 0;
        }
    }

    // Tree & Adders
    TreeResult tr1 = ne_dw_add_tree(adder_in_1, 16, 32);
    TreeResult tr0 = ne_dw_add_tree(adder_in_0, 16, 31);
    TreeResult tr2 = ne_dw_add_tree(adder_in_2, 32, 15);

    uint64_t adder1_z = ne_dw_add(tr1.out0, tr1.out1, 32);
    uint64_t adder0_z = ne_dw_add(tr0.out0, tr0.out1, 31);
    uint64_t adder2_z = ne_dw_add(tr2.out0, tr2.out1, 15);

    uint64_t adder1_z_mux = (op_mode & 1) ? (sext(adder1_z & MASK(20), 20) & MASK(32)) : adder1_z;
    uint64_t adder0_z_ext = (BIT(adder0_z, 30) << 31) | adder0_z;
    uint64_t adder0_z_mux = (op_mode & 1) ? (sext(adder0_z & MASK(20), 20) & MASK(32)) : adder0_z_ext;

    uint64_t adder_z = ne_dw_add(adder1_z_mux, adder0_z_mux, 32);

    // Final Status & Output
    bool z_tf32_nan = z_tf32_nan_t | (global_tf32_pinf & global_tf32_ninf);
    bool z_tf32_inf = z_tf32_inf_t_raw & !z_tf32_nan;
    bool z_fp8_nan  = z_fp8_nan_t  | (global_fp8_pinf  & global_fp8_ninf); 
    bool z_fp8_inf  = z_fp8_inf_t_raw & !z_fp8_nan;

    uint64_t e_sfr = (op_mode & 4) ? 4 : 5;
    uint64_t e_max_ext = (BIT(e_max, 8) << 9) | e_max;
    uint64_t z_e0_t = e_max_ext + e_sfr;
    
    uint64_t abs_low = ab_scale & MASK(9);
    uint64_t abs_ext = (BIT(abs_low, 8) << 10) | (BIT(abs_low, 8) << 9) | abs_low;
    uint64_t z_e0_trunc = z_e0_t & MASK(10);
    uint64_t z_e0_sign_ext = (BIT(z_e0_trunc, 9) << 10) | z_e0_trunc;
    uint64_t z_e_t = z_e0_sign_ext + abs_ext;
    uint64_t z_e = z_e_t & MASK(10);

    bool zs_inf = ((op_mode&4) && z_tf32_inf && global_tf32_ninf) ||
                  ((op_mode&2) && z_fp8_inf  && global_fp8_ninf);
                  
    uint64_t zs_tf32 = z_tf32_inf ? zs_inf : BIT(adder1_z, 31);
    uint64_t zs_fp8  = z_fp8_inf  ? zs_inf : BIT(adder_z, 31);

    uint64_t zm_tf32 = (zs_tf32 << 32) | adder1_z;
    uint64_t zm_fp8  = (zs_fp8 << 32)  | adder_z;
    uint64_t z_int8  = adder_z & MASK(21);

    uint64_t z_final;
    uint64_t z_fp4_out = 0;

    if (op_mode & 8) { 
        uint64_t fp4_c0_scale = ((ab_scale & MASK(9)) | (BIT(ab_scale, 8)<<9)) + 10;
        uint64_t fp4_c32_scale = (GET_BITS(ab_scale, 17, 9) | (BIT(ab_scale, 17)<<9)) + 10;
        uint64_t ze_fp4 = ((fp4_c32_scale & MASK(10)) << 10) | (fp4_c0_scale & MASK(10));
        uint64_t zm_fp4_0 = (adder_z & MASK(15)) | (BIT(adder_z, 14) << 15);
        uint64_t zm_fp4_32 = (adder2_z & MASK(15)) | (BIT(adder2_z, 14) << 15);

        z_final = ((uint64_t)z_fp4_is_zero << 45) | ((ze_fp4 & MASK(10)) << 33) | (zm_fp4_0 << 17);
        z_fp4_out = (((uint64_t)z1_fp4_is_zero << 28) | ((ze_fp4 >> 10) << 16) | zm_fp4_32);

    } else if (op_mode & 4) { 
        z_final = ((uint64_t)z_tf32_zero_t << 45) | ((uint64_t)z_tf32_inf << 44) |
                  ((uint64_t)z_tf32_nan << 43) | (z_e << 33) | (zm_tf32 & MASK(33));
    } else if (op_mode & 2) { 
        z_final = ((uint64_t)z_fp8_zero_t << 45) | ((uint64_t)z_fp8_inf << 44) |
                  ((uint64_t)z_fp8_nan << 43) | (z_e << 33) | (zm_fp8 & MASK(33));
    } else { 
        z_final = z_int8;
    }

    VectorM33Result res;
    res.z = z_final & MASK(46);
    res.z_fp4 = z_fp4_out & MASK(29);
    return res;
}

void c_ne_fp_ffp_e_align(
    _u4 op_mode,
    _u144 a_e,
    _u96 b_e,
    _u9 *e_max,
    _u6 (*a_e_sub_array)[16],
    _u6 (*b_e_sub_array)[16],
    _u16 *a_e_overflow,
    _u16 *b_e_overflow
) {
    // 1. 初始化输出信号
    *e_max = 0;
    for(int i=0; i<16; i++) {
        (*a_e_sub_array)[i] = 0;  // 修改访问方式
        (*b_e_sub_array)[i] = 0;  // 修改访问方式
    }
    *a_e_overflow = 0;
    *b_e_overflow = 0;

    // 2. 中间变量声明
    _u9 a_e_slice[16];
    _u6 b_e_slice[16];
    for(int i=0; i<16; i++) {
        a_e_slice[i] = a_e>>i*9;
        b_e_slice[i] = b_e>>i*6;
    }
    _u9 a_e_max = a_e_slice[0];
    for(int i=1; i<16; i++) {
        if(IS_MAX(a_e_slice[i],a_e_max,1)) {
            a_e_max = a_e_slice[i];
        }
    }
    _u6 b_e_max=b_e_slice[0];
    for(int i=1; i<16; i++) {
        if(IS_MAX(b_e_slice[i],b_e_max,1)) {
            b_e_max = b_e_slice[i];
        }
    }

    if(op_mode == 1) { //int8 
        ;
    } else if(op_mode == 2) { //fp8
        //wire [9:0]   bias   = 10'b1_111100100:   // -14 + (-14) = -28
        _u9 a_bias = 0x1E4;//a_e的偏置 -28
        _u6 b_bias = 0x24;//b_e的偏置 -28
        if(IS_MAX(a_bias,a_e_max,1)) {
            a_e_max = a_bias;
        }
        if(IS_MAX(b_bias,b_e_max,1)) {
            b_e_max = b_bias;
        }
        _u9 b_e_max_extend = SIGN_EXTEND(b_e_max,9);
        if(IS_MAX(a_e_max,b_e_max_extend,1)) {
            *e_max = a_e_max;
        } else {
            *e_max = b_e_max_extend;
        }

        _u9 t_sub=0;
        _u9 t_b_e_extend=0;
        _u6 t_low=0;
        for(int i=0; i<16; i++) {
            t_sub = SYM_SUB( *e_max,a_e_slice[i], 1);
            (*a_e_sub_array)[i] = t_sub; //只取低6位
            t_low=t_sub;
            if(t_low >=25) {
                //这个溢出条件是怎么样？？？？？
                (*a_e_overflow) |= (1<<i);
            }

            t_b_e_extend = SIGN_EXTEND(b_e_slice[i],9);
            t_sub = SYM_SUB( *e_max,t_b_e_extend, 1);
            (*b_e_sub_array)[i] = t_sub; //只取低6位
            t_low=t_sub;
            if(t_low >= 25) {
                //这个溢出条件是怎么样？？？？？
                (*b_e_overflow) |= (1<<i);
            }
        }
    } else if(op_mode == 4) { //tf32
        _u9 a_bias = 0x104;//a_e的偏置 -252\9'b100000100
        if(IS_MAX(a_bias,a_e_max,1)) {
            a_e_max = a_bias;
        }
        *e_max = a_e_max;
        _u9 t_sub=0;
        for(int i=0; i<16; i++) {
            t_sub = SYM_SUB( *e_max,a_e_slice[i], 1);
            (*a_e_sub_array)[i] = t_sub; //只取低6位
            // if(CHECK_SIGN_BIT(t_sub)||t_sub==64||t_sub>=26) {
            if(CHECK_SIGN_BIT(t_sub)||t_sub>=26) {
                //这个溢出条件是怎么样？？？？？
                (*a_e_overflow) |= (1<<i);
            }
        }
    } else if(op_mode == 8) { //fp4
        //除了溢出全为0，emax写死。其余与fp8一致
        *e_max = 0x02D;
        _u9 t_sub=0;
        _u9 t_b_e_extend=0;
        _u6 t_low=0;
        for(int i=0; i<16; i++) {
            t_sub = SYM_SUB( *e_max,a_e_slice[i], 1);
            (*a_e_sub_array)[i] = t_sub; //只取低6位
            t_low=t_sub;

            t_b_e_extend = SIGN_EXTEND(b_e_slice[i],9);
            t_sub = SYM_SUB( *e_max,t_b_e_extend, 1);
            (*b_e_sub_array)[i] = t_sub; //只取低6位
            t_low=t_sub;
        }
    }
}
void c_DW_lsd_w33(_u33 a, _u6 *enc) {
    _u6 i;

    for (i = 32; i > 0; i--) {
        // 提取第i位和第i-1位，检查它们是否不同
        if (EXTRACT_BITS(a, i, i) != EXTRACT_BITS(a, i-1, i-1)) {
            *enc= 32 - i;  // 编码值为从最高位开始的位置索引
            break;              // 找到第一个不同的位对后退出循环
        }
    }
    
    // 如果所有位都相同（循环正常结束）
    if (i == 0) {
        *enc= 32;
    }
    
}

void c_ne_fp_ffp2fp_m33(
    _u47 a,
    _u4 mode,

    _u32 *z,
    _u2 *z_is_infnan
) {
    *z = 0;
    *z_is_infnan = 0;

    _u1 a_is_nan  = EXTRACT_BITS(a, 46, 46);
    _u1 a_is_inf  = EXTRACT_BITS(a, 45, 45);
    _u1 a_is_zero = EXTRACT_BITS(a, 44, 44); 
    _u10 a_e = EXTRACT_BITS(a, 43, 34);
    _u1 a_s  = EXTRACT_BITS(a, 33 ,33);
    _u32 a_m = EXTRACT_BITS(a, 31, 0);
    
    _u1 z_s=a_s;
    _u1 z_is_zero = 0;
    _u1 z_is_inf = 0;
    _u1 z_is_nan = 0;
    _u1 z_is_norm = 0;
    _u1 z_is_subnorm = 0;

    if (mode==1) {//int8
        //为什么是直接提取21位符号位拓展可能之后得连着前面的模块一起看看
        _u22 part_int8;
        part_int8 = EXTRACT_BITS(a, 21, 0);
        *z = SIGN_EXTEND(part_int8, 32);
        *z_is_infnan = 0;
    } else {//tf32 fp8 fp4
        _u32 a_m1=0;//补码处理后尾数位
        _u32 a_m2=0;//左移后尾数位
        _u11 a_e2=0;
        _u6 a_m1_ls=0;//左移位数

        _u33 a_m_ext = a_s ? ((_u33)~a_m + (_u33)1) : a_m;
        _u1 a_m1_ecin=CHECK_SIGN_BIT(a_m_ext);

        //printf("a_m_ext_sign: %d\n", CHECK_SIGN_BIT(a_m_ext));
        a_m1 =CHECK_SIGN_BIT(a_m_ext)? 0x80000000 : a_m_ext;

        c_DW_lsd_w33(a_m1, &a_m1_ls);
        a_m2 = a_m1 << a_m1_ls;

        int t;
        _u11 a_e_extend= SIGN_EXTEND(a_e, 11);
        _u11 a_m1_ls_extend= a_m1_ls;
        t = (_s11)a_e_extend - (_s11)a_m1_ls_extend + a_m1_ecin;
        a_e2 = t;


        _u1 a_m2_mcin = EXTRACT_BITS(a_m2, 7, 7);
        _u24 a_m2_hign24= EXTRACT_BITS(a_m2, 31, 8);
        _u25 a_m3_ext= (_u25)a_m2_hign24+(_u25)a_m2_mcin;
        _u23 z_m= a_m3_ext;//23+1=25-1少的1位应该是尾数位的隐藏1
        _u1 a_m2_ecin = EXTRACT_BITS(a_m3_ext, 24, 24);
        _u8  z_e = (_s11)a_e2+(_s11)127+a_m2_ecin;

        // printf("a_e: %d\n", a_e);
        // printf("ref_a_e2: %d\n", a_e2);
        // printf("act_a_e2: %d\n", ne_fp_ffp2fp_m33.am2_e);
        // assert(a_m2==ne_fp_ffp2fp_m33.am2);
        // assert(a_e2==ne_fp_ffp2fp_m33.am2_e);

        //分情况判断
        z_is_zero= ((a_m1 == 0) & (~a_is_inf) & (~a_is_nan)) | a_is_zero;
        z_is_nan = a_is_nan;
        z_is_inf = a_is_inf || (!z_is_zero&&!z_is_nan&&(((_s11)a_e2>(_s11)127)||(a_e2==127)&&a_m2_ecin));
        // assert(z_is_zero==ne_fp_ffp2fp_m33.am1_iszero);
        // printf("signed_a_e2>127:%d",(_s11)a_e2>(_s11)127);
        // printf("signed_a_e2==127:%d",(_s11)a_e2==(_s11)127);
        // printf("a_m2_ecin:%d",a_m2_ecin);    
        *z_is_infnan = JOIN_BITS(z_is_inf, z_is_nan);

        z_is_norm = (((_s11)a_e2 > (_s11)-127) || ((_s11)a_e2 == (_s11)-127 && a_m2_ecin))&(~z_is_inf)&(~z_is_nan);
        z_is_subnorm = ((_s11)a_e2 > (_s11)-151)&(~z_is_norm)&(~z_is_inf)&(~z_is_nan)&(~z_is_zero);
        
        t = -126 - (_s11)a_e2;
        _u5 a_m3_sub_rs = t;
        _u32 a_m3_subm = a_m2 >> a_m3_sub_rs;

        _u8 z_sube = 0;
        _u1 a_subm_mcin = EXTRACT_BITS(a_m3_subm, 7, 7);
        _u24 a_subm_hign24= EXTRACT_BITS(a_m3_subm, 31, 8);
        _u25 a_subm_ext= (_u25)a_subm_hign24+(_u25)a_subm_mcin;
        _u23 z_subm= a_subm_ext;//23+1=25-1少的1位应该是尾数位的隐藏1

        *z = 0;
        if(z_is_zero){
            //*z=0;
            *z=CONCAT_BITS(*z,a_s,31);
        } else if(z_is_inf){
            *z=0x7f800000;
            *z=CONCAT_BITS(*z,z_s,31);
        } else if(z_is_nan){
            *z=0x7fc00000;
        } else if(z_is_norm){
            *z=CONCAT_BITS(*z,z_s,31);
            *z=CONCAT_BITS(*z,z_e,23);
            *z=CONCAT_BITS(*z,z_m,0);
        } else if(z_is_subnorm){
            *z=CONCAT_BITS(*z,z_s,31);
            *z=CONCAT_BITS(*z,z_sube,23);
            *z=CONCAT_BITS(*z,z_subm,0);
        }
    }
}


void c_ne_fp_sfl_blk_w33s6(
    _u33 a,   // [FIXED] _u16 -> _u33
    _u6 s,    // [FIXED] _u4 -> _u6 (log2(33) -> 6 bits)
    _u33 *z   // [FIXED] _u16 -> _u33
) {
    *z = 0;
    *z = a << s;
}

// LSD: 输入 32位 (MW-1)
void c_DW_lsd_w32(
    _u32 a,   // [FIXED] _u15 -> _u32
    _u32 *dec, 
    _u6 *enc  // [FIXED] 足够容纳结果即可，_u6
) {
    _u32 i; 
    

    for (i = 31; i > 0; i--) {
        if (EXTRACT_BITS(a, i, i) != EXTRACT_BITS(a, i-1, i-1)) {
            *enc = 31 - i;      // 编码值
            *dec = 1ULL << i;   // 解码值
            break; 
        }
    }
    
    if (i == 0) {
        *enc = 31;
        *dec = 0x1; // Bit 0
    }
}

// =========================================================
// C Model 
// =========================================================
uint64_t c_ne_fp_ffp_norm_mw33(uint64_t a, uint64_t mode) {
    const int SW = 1;
    const int EW = 10;
    const int MW = 33;
    const int BW_STATUS = 3;
    const int BW = (BW_STATUS + SW + EW + MW); // 30
    const int BIAS = 511;
    uint64_t a_status = 0;
    uint64_t a_s = 0;
    uint64_t a_e = 0;
    uint64_t a_m = 0;
    
    if (BW_STATUS > 0) {
        if ((mode & 1) == 0) { // Normalization mode
            int offset = 0;
            a_m = GET_BITS(a, MW - 1, 0); 
            offset += MW;
            a_e = GET_BITS(a, offset + EW - 1, offset);
            offset += EW;
            a_s = GET_BITS(a, offset + SW - 1, offset);
            offset += SW;
            a_status = GET_BITS(a, offset + BW_STATUS - 1, offset);
        } else {
            // Bypass mode internal logic clear
            a_status = 0; 
            a_s = 0;
            a_e = 0;
            a_m = 0;
        }
    } else {
        a_s = GET_BITS(a, BW-1, BW-SW);
        a_e = GET_BITS(a, BW-SW-1, MW);
        a_m = GET_BITS(a, MW-1, 0);
    }

    bool a_is_nan  = (a_status >> 2) & 1;
    bool a_is_inf  = (a_status >> 1) & 1;
    bool a_is_zero = (a_status >> 0) & 1;

    // -----------------------------------------------------
    // A. Leading Sign/Bit Detection (LSD)
    // -----------------------------------------------------
    // LSD 输入宽度 = MW - 1 = 32 bits
    uint64_t lsd_in_val = a_m & MASK(MW - 1); 
    _u32 lsd_in = (_u32)lsd_in_val; // [FIXED] Cast to _u32
    _u32 lsd_dec_unused;
    _u6  a_m_cls_w; // [FIXED] Width

    c_DW_lsd_w32(lsd_in, &lsd_dec_unused, &a_m_cls_w);
    
    uint64_t a_m_cls = a_m_cls_w; 

    // -----------------------------------------------------
    // B. Shifter
    // -----------------------------------------------------
    // Shifter 输入宽度 = MW = 33 bits
    uint64_t sfl_in_val = a_m & MASK(MW);
    _u33 sfl_in = (_u33)sfl_in_val; // [FIXED] Cast to _u33
    _u33 sfl_out;

    c_ne_fp_sfl_blk_w33s6(sfl_in, (_u6)a_m_cls, &sfl_out);
    
    uint64_t a_m_sfl = sfl_out; 


    // z_m_neg_overflow = a_m[MW-2] & (~|a_m_sfl[MW-3:0])
    // MW=33 -> MW-2=31, MW-3=30
    
    int bit_check_pos = MW - 2; // 31
    int sfl_check_bits = MW - 3; // 30
    
    bool a_m_top_check = (a_m >> bit_check_pos) & 1;
    
    // 检查 sfl 低 (MW-3+1) 位即 [30:0] 是否全为0
    uint64_t sfl_low_part = a_m_sfl & MASK(sfl_check_bits + 1); 
    
    bool z_m_neg_overflow = a_m_top_check && (sfl_low_part == 0);

    // -----------------------------------------------------
    // D. 拼接最终的 z_m
    // -----------------------------------------------------
    // MW-2 = 31
    uint64_t z_m;
    uint64_t am_top2 = (a_m >> (MW - 2)) & 0x3; // a_m[32:31]

    if (z_m_neg_overflow) {
        // 取 sfl [MW-2:1] -> [31:1] (长度 31位)
        uint64_t part_sfl = (a_m_sfl >> 1) & MASK(MW - 2); 
        z_m = (am_top2 << (MW - 2)) | part_sfl;
    } else {
        // 取 sfl [MW-3:0] -> [30:0] (长度 31位)
        uint64_t part_sfl = a_m_sfl & MASK(MW - 2);
        z_m = (am_top2 << (MW - 2)) | part_sfl;
    }

    // -----------------------------------------------------
    //  z_e0
    // -----------------------------------------------------
    int64_t a_e_signed = (int64_t)a_e;
    int64_t z_e0_calc = a_e_signed - (int64_t)a_m_cls + (int64_t)z_m_neg_overflow;
    uint64_t z_e0 = z_e0_calc & MASK(EW); 
    
    uint64_t z_e = z_e0;
    uint64_t z_s = a_s;

    // Status logic
    bool z_is_nan = a_is_nan;
    bool z_is_inf = a_is_inf;
    bool z_m_is_zero = (z_m == 0);
    bool z_is_zero = a_is_zero || (z_m_is_zero && !a_is_inf && !a_is_nan);


    uint64_t z_e_max  = (BIAS + 1) & MASK(EW);
    uint64_t z_e_zero_val = ((uint64_t)(-BIAS)) & MASK(EW);

    // NaN: {z_s, z_e_max, {z_s,z_s,1'b1, {(MW-3){1'b0}}}}
    uint64_t nan_payload = (z_s << (MW-1)) | (z_s << (MW-2)) | (1ULL << (MW-3));
    uint64_t z_nan_pkt = (z_s << (EW + MW)) | (z_e_max << MW) | nan_payload;

    // Inf: {z_s, z_e_max, {z_s,z_s,{(MW-2){1'b0}}}}
    uint64_t inf_payload = (z_s << (MW-1)) | (z_s << (MW-2));
    uint64_t z_inf_pkt = (z_s << (EW + MW)) | (z_e_max << MW) | inf_payload;

    // Zero: {z_s, z_e_zero, {z_s,z_s,{(MW-2){1'b0}}}}
    uint64_t zero_payload = (z_s << (MW-1)) | (z_s << (MW-2));
    uint64_t z_zero_pkt = (z_s << (EW + MW)) | (z_e_zero_val << MW) | zero_payload;

    // Data: {z_s, z_e, z_m}
    uint64_t z_d_pkt = (z_s << (EW + MW)) | (z_e << MW) | z_m;

    // -----------------------------------------------------
    // Output Mux
    // -----------------------------------------------------
    uint64_t z_o;

    if ((mode & 1) != 0) {
        // mode[0] == 1: Bypass
        int data_width = SW + EW + MW; // 44 bits
        z_o = a & MASK(data_width);
    } else {
        if (z_is_nan)      z_o = z_nan_pkt;
        else if (z_is_inf) z_o = z_inf_pkt;
        else if (z_is_zero) z_o = z_zero_pkt;
        else               z_o = z_d_pkt;
    }

    // Final Pack with Status
    uint64_t final_z;
    if (BW_STATUS > 0) {
        uint64_t z_status = (z_is_nan << 2) | (z_is_inf << 1) | z_is_zero;
        int core_width = SW + EW + MW; // 44
        final_z = (z_status << core_width) | (z_o & MASK(core_width));
    } else {
        final_z = z_o;
    }

    return final_z;
}




void c_ne_fp_sfl_blk_w27s5(
    _u27 a,
    _u5 s,
    _u27 *z
) {
    *z = 0;
    *z = a << s;
}

void c_DW_lsd_w26(_u26 a, _u26 *dec, _u5 *enc) {
    _u5 i;
    for (i = 25; i > 0; i--) {
        if (EXTRACT_BITS(a, i, i) != EXTRACT_BITS(a, i-1, i-1)) {
            *enc = 25 - i; 
            *dec = 1ULL << i;
            break; 
        }
    }
    if (i == 0) {
        *enc = 25;
        *dec = 0x1;
    }
}

// =========================================================
// C Model 主逻辑
// =========================================================
uint64_t c_ne_fp_ffp_norm_mw27(uint64_t a, uint64_t mode) {
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

    if (BW_STATUS > 0) {
        if ((mode & 1) == 0) { // ~mode[0] -> tf32/fp8
            int offset = 0;
            a_m = GET_BITS(a, MW - 1, 0); 
            offset += MW;
            a_e = GET_BITS(a, offset + EW - 1, offset);
            offset += EW;
            a_s = GET_BITS(a, offset + SW - 1, offset);
            offset += SW;
            a_status = GET_BITS(a, offset + BW_STATUS - 1, offset);
        } else {
            a_status = 0; 
            a_s = 0;
            a_e = 0;
            a_m = 0;
        }
    } else {
        a_s = GET_BITS(a, BW-1, BW-SW);
        a_e = GET_BITS(a, BW-SW-1, MW);
        a_m = GET_BITS(a, MW-1, 0);
    }

    bool a_is_nan  = (a_status >> 2) & 1;
    bool a_is_inf  = (a_status >> 1) & 1;
    bool a_is_zero = (a_status >> 0) & 1;


    uint64_t lsd_in_val = a_m & MASK(MW - 1); 
    _u26 lsd_in = (_u26)lsd_in_val;
    
    _u26 lsd_dec_unused;
    _u5  a_m_cls_w;

    c_DW_lsd_w26(lsd_in, &lsd_dec_unused, &a_m_cls_w);
    
    uint64_t a_m_cls = a_m_cls_w; 


    uint64_t sfl_in_val = a_m & MASK(MW);
    _u27 sfl_in = (_u27)sfl_in_val;
    _u27 sfl_out;

    c_ne_fp_sfl_blk_w27s5(sfl_in, (_u5)a_m_cls, &sfl_out);
    
    uint64_t a_m_sfl = sfl_out; 


    
    int bit_check_pos = MW - 2; // 25
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

    if (z_m_neg_overflow) {
        // 取 sfl [MW-2:1] -> [25:1]
        // 长度是 MW-2 = 25 位
        uint64_t part_sfl = (a_m_sfl >> 1) & MASK(MW - 2); 
        z_m = (am_top2 << (MW - 2)) | part_sfl;
    } else {
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


    uint64_t z_e_max  = (BIAS + 1) & MASK(EW);
    uint64_t z_e_zero_val = ((uint64_t)(-BIAS)) & MASK(EW);

    // NaN: {z_s, z_e_max, {z_s,z_s,1'b1, {(MW-3){1'b0}}}}
    uint64_t nan_payload = (z_s << (MW-1)) | (z_s << (MW-2)) | (1ULL << (MW-3));
    uint64_t z_nan_pkt = (z_s << (EW + MW)) | (z_e_max << MW) | nan_payload;

    // Inf: {z_s, z_e_max, {z_s,z_s,{(MW-2){1'b0}}}}
    uint64_t inf_payload = (z_s << (MW-1)) | (z_s << (MW-2));
    uint64_t z_inf_pkt = (z_s << (EW + MW)) | (z_e_max << MW) | inf_payload;

    // Zero: {z_s, z_e_zero, {z_s,z_s,{(MW-2){1'b0}}}}
    uint64_t zero_payload = (z_s << (MW-1)) | (z_s << (MW-2));
    uint64_t z_zero_pkt = (z_s << (EW + MW)) | (z_e_zero_val << MW) | zero_payload;

    // Data: {z_s, z_e, z_m}
    uint64_t z_d_pkt = (z_s << (EW + MW)) | (z_e << MW) | z_m;

    // -----------------------------------------------------
    // Output Mux
    // -----------------------------------------------------
    uint64_t z_o;
    if ((mode & 1) != 0) {
        int data_width = SW + EW + MW;
        z_o = a & MASK(data_width);
    } else {
        if (z_is_nan)      z_o = z_nan_pkt;
        else if (z_is_inf) z_o = z_inf_pkt;
        else if (z_is_zero) z_o = z_zero_pkt;
        else               z_o = z_d_pkt;
    }

    // Final Pack
    uint64_t final_z;
    if (BW_STATUS > 0) {
        uint64_t z_status = (z_is_nan << 2) | (z_is_inf << 1) | z_is_zero;
        int core_width = SW + EW + MW; 
        final_z = (z_status << core_width) | (z_o & MASK(core_width));
    } else {
        final_z = z_o;
    }

    return final_z;
}




void c_ne_fp_sfl_blk_w16s4(
    _u16 a,
    _u4 s,
    _u16 *z
) {
    *z = 0;
    *z = a << s;
}

void c_DW_lsd_w15(_u15 a, _u15 *dec, _u4 *enc) {
    _u32 i; // 修改 i 类型以避免循环警告，逻辑不变

    for (i = 14; i > 0; i--) {
        // 提取第i位和第i-1位，检查它们是否不同
        if (EXTRACT_BITS(a, i, i) != EXTRACT_BITS(a, i-1, i-1)) {
            *enc = 14 - i;       // 编码值为从最高位开始的位置索引
            *dec = 1U << i;      // 解码值为第i位的掩码
            break;               // 找到第一个不同的位对后退出循环
        }
    }
    
    // 如果所有位都相同（循环正常结束）
    if (i == 0) {
        *enc = 14;
        *dec = 0x1; // Bit 0
    }
}

// =========================================================
// 2. 主 CModel 函数 (参数宏已移入函数内部)
// =========================================================

uint64_t c_ne_fp_ffp_norm_mw16(uint64_t a, uint64_t mode) {

    // -----------------------------------------------------
    // 将原本的宏定义移动到此处作为局部常量
    // -----------------------------------------------------
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
    

    if (BW_STATUS > 0) {
        if ((mode & 1) == 0) { // ~mode[0] -> tf32/fp8
            int offset = 0;
            a_m = GET_BITS(a, MW - 1, 0); 
            offset += MW;
            a_e = GET_BITS(a, offset + EW - 1, offset);
            offset += EW;
            a_s = GET_BITS(a, offset + SW - 1, offset);
            offset += SW;
            a_status = GET_BITS(a, offset + BW_STATUS - 1, offset);
        } else {

            a_status = 0; 
            a_s = 0;
            a_e = 0;
            a_m = 0;
        }
    } else {

        a_s = GET_BITS(a, BW-1, BW-SW);
        a_e = GET_BITS(a, BW-SW-1, MW);
        a_m = GET_BITS(a, MW-1, 0);
    }

    bool a_is_nan  = (a_status >> 2) & 1;
    bool a_is_inf  = (a_status >> 1) & 1;
    bool a_is_zero = (a_status >> 0) & 1;

    
    // A. 计算 Leading Sign/Bit Detection (LSD)
    _u15 lsd_in = (_u15)(a_m & MASK(MW - 1)); // 取 a_m 的低15位 [MW-2:0]
    _u15 lsd_dec_unused;
    _u4  a_m_cls_w;
    

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

    if (z_m_neg_overflow) {
        uint64_t part_sfl = (a_m_sfl >> 1) & MASK(14); // a_m_sfl[14:1]
        z_m = (am_top2 << 14) | part_sfl;
    } else {
        uint64_t part_sfl = a_m_sfl & MASK(14);        // a_m_sfl[13:0]
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


    uint64_t z_e_max  = (BIAS + 1) & MASK(EW);
    uint64_t z_e_zero_val = ((uint64_t)(-BIAS)) & MASK(EW); // 补码表示

    // {z_s, z_e_max, {z_s,z_s,1'b1, {(MW-3){1'b0}}}}
    uint64_t nan_payload = (z_s << (MW-1)) | (z_s << (MW-2)) | (1ULL << (MW-3));
    uint64_t z_nan_pkt = (z_s << (EW + MW)) | (z_e_max << MW) | nan_payload;


    // {z_s, z_e_max, {z_s,z_s,{(MW-2){1'b0}}}}
    uint64_t inf_payload = (z_s << (MW-1)) | (z_s << (MW-2));
    uint64_t z_inf_pkt = (z_s << (EW + MW)) | (z_e_max << MW) | inf_payload;


    // {z_s, z_e_zero, {z_s,z_s,{(MW-2){1'b0}}}}
    uint64_t zero_payload = (z_s << (MW-1)) | (z_s << (MW-2));
    uint64_t z_zero_pkt = (z_s << (EW + MW)) | (z_e_zero_val << MW) | zero_payload;

    // {z_s, z_e, z_m}
    uint64_t z_d_pkt = (z_s << (EW + MW)) | (z_e << MW) | z_m;


    uint64_t z_o;

    if ((mode & 1) != 0) {
        // mode[0] == 1: Bypass mode
        // 截取输入数据的低 BW - BW_STATUS 位 (即 27 位)
        int data_width = SW + EW + MW;
        z_o = a & MASK(data_width);
    } else {
        // mode[0] == 0: Normalization mode
        if (z_is_nan) {
            z_o = z_nan_pkt;
        } else if (z_is_inf) {
            z_o = z_inf_pkt;
        } else if (z_is_zero) {
            z_o = z_zero_pkt;
        } else {
            z_o = z_d_pkt;
        }
    }


    uint64_t final_z;
    
    if (BW_STATUS > 0) {
        uint64_t z_status = (z_is_nan << 2) | (z_is_inf << 1) | z_is_zero;
        int core_width = SW + EW + MW; // 27
        // z = {z_status, z_o}
        final_z = (z_status << core_width) | (z_o & MASK(core_width));
    } else {
        final_z = z_o;
    }

    return final_z;
}

void c_ne_fp_ffp_mul(
    _u4        op_mode              ,  // 操作模式选择：4'b0001=int8, 4'b0010=fp8, 4'b0100=tf32, 4'b1000=fp4
    _u19       a                    ,  // 19位输入操作数a
    _u19       b                    ,  // 19位输入操作数b
    _u6        *z0_e                ,  // 第一个乘法结果的指数部分
    _u9        *z1_e                ,  // 第二个乘法结果的指数部分
    _u32       *z_m                    // 乘法结果的尾数部分    
) {
    *z_m=0;
    *z0_e=0;
    *z1_e=0;

    if(op_mode == 1) { //int8
        _u8	a_int[2];
        _u8	b_int[2];
        _u16 z_int[2];
        a_int[0]=EXTRACT_BITS(a, 7, 0);
        a_int[1]=EXTRACT_BITS(a, 16, 9);
        b_int[0]=EXTRACT_BITS(b, 7, 0);
        b_int[1]=EXTRACT_BITS(b, 16, 9);
        
        c_DW02_mult_i8(a_int[0], b_int[0], 1, &z_int[0]);
        c_DW02_mult_i8(a_int[1], b_int[1], 1, &z_int[1]);
        *z_m = JOIN_BITS(z_int[1], z_int[0]);
        // *z_m = ((_u32)z_int[1] << 16) | ((_u32)z_int[0]);
        *z0_e = 0;
        *z1_e = 0;
    } else if(op_mode == 2) { //fp8
        int bias= 15;
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
        _u1 a_e_is_zero[2];//指数位全0
        _u1 a_e_is_max[2];//指数位全1
        _u1 b_e_is_zero[2];
        _u1 b_e_is_max[2];
        _u1 a_m_is_zero[2];//尾数位全0
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

        for(int i=0;i<2;i++){
            a_fp8[i]=EXTRACT_BITS(a, (i+1)*9-1, i*9);
            b_fp8[i]=EXTRACT_BITS(b, (i+1)*9-1, i*9);   
            a_s[i]=EXTRACT_BITS(a_fp8[i], 8, 8);
            b_s[i]=EXTRACT_BITS(b_fp8[i], 8, 8);
            a_e[i]=EXTRACT_BITS(a_fp8[i], 7, 3);
            b_e[i]=EXTRACT_BITS(b_fp8[i], 7, 3);
            a_m[i]=EXTRACT_BITS(a_fp8[i], 2, 0);
            b_m[i]=EXTRACT_BITS(b_fp8[i], 2, 0);
            a_e_is_zero[i]=a_e[i]==0;
            a_e_is_max[i] =a_e[i]==31;
            b_e_is_zero[i]=b_e[i]==0;
            b_e_is_max[i] =b_e[i]==31;
            a_m_is_zero[i]=a_m[i]==0;
            b_m_is_zero[i]=b_m[i]==0; 

            a_is_zero[i]=a_e_is_zero[i]&&a_m_is_zero[i];
            a_is_inf[i]=a_e_is_max[i]&&a_m_is_zero[i];
            a_is_nan[i]=a_e_is_max[i]&&!a_m_is_zero[i];
            a_is_subnorm[i]=a_e_is_zero[i]&&!a_m_is_zero[i];

            b_is_zero[i]=b_e_is_zero[i]&&b_m_is_zero[i];
            b_is_inf[i]=b_e_is_max[i]&&b_m_is_zero[i];
            b_is_nan[i]=b_e_is_max[i]&&!b_m_is_zero[i];
            b_is_subnorm[i]=b_e_is_zero[i]&&!b_m_is_zero[i];

            a_hide_bit = (!a_is_subnorm[i]) && (!a_is_zero[i]) && (!a_is_inf[i] && !a_is_nan[i]);
            b_hide_bit = (!b_is_subnorm[i]) && (!b_is_zero[i]) && (!b_is_inf[i] && !b_is_nan[i]);
            t_M[0]=JOIN_BITS(a_hide_bit, a_m[i]);
            t_M[1]=JOIN_BITS(b_hide_bit, b_m[i]);
            t_mul=t_M[0]*t_M[1];
            z_s= a_s[i]!=b_s[i];
            if(z_s){
                if(t_mul!= 0)  //尾数部分计算输出非0正常取补码
                    t_mul=-t_mul;
                else if(a_is_zero[i]||b_is_zero[i])//a,b输入为0导致的0正常输出0
                    t_mul=0 ;
                else //inf导致的尾数部分给mul子模块的输入为0导致的输出0
                    t_mul=256 ; //符号为拓展会给0的最高位补1变成9'h100000000
            }
            z_M[i]=t_mul;
            //加这个1是处于什么目的
            t_e=a_e[i]+b_e[i] - 2 * bias + a_is_subnorm[i] + b_is_subnorm[i] +1; 
            if(i==0){
                *z0_e=(a_is_zero[i]||b_is_zero[i])? 484 :t_e; //输入有一个为0时，指数位为-28\484\9'h1_11100100 
            }else{
                *z1_e=(a_is_zero[i]||b_is_zero[i])? 484 :t_e;
            }
            //判断是否为NaN或Inf  输入为NaN或者0×inf
            z_is_nan[i]=(a_is_nan[i]||b_is_nan[i])||(a_is_inf[i]&&b_is_zero[i])||(a_is_zero[i]&&b_is_inf[i]);
            //判断是否为0         输入为0×非特殊值
            z_is_zero[i]=(a_is_zero[i]&&!b_is_nan[i]&&!b_is_inf[i])||(b_is_zero[i]&&!a_is_nan[i]&&!a_is_inf[i]);
            //判断是否为Inf       输入为inf×非0非NaN
            z_is_inf[i]=(a_is_inf[i]&&!b_is_zero[i]&&!b_is_nan[i])||(b_is_inf[i]&&!a_is_zero[i]&&!a_is_nan[i]);
        }

        //z_status[0] = {z_is_zero[0], z_is_inf[0], z_is_nan[0]};
        z_status[0] = JOIN_BITS(z_is_zero[0], z_is_inf[0], z_is_nan[0]);
        z_status[1] = JOIN_BITS(z_is_zero[1], z_is_inf[1], z_is_nan[1]);
        *z_m = CONCAT_BITS(*z_m,z_status[1],25);
        *z_m = CONCAT_BITS(*z_m,z_M[1],16);
        *z_m = CONCAT_BITS(*z_m,z_status[0],9);
        *z_m = CONCAT_BITS(*z_m,z_M[0],0);
    } else if(op_mode == 4) { //tf32
        int bias= 127;
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

        _u1 a_e_is_zero;//指数位全0
        _u1 a_e_is_max;//指数位全1
        _u1 b_e_is_zero;
        _u1 b_e_is_max;
        _u1 a_m_is_zero;//尾数位全0
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
        _u1 z_is_inf ;
        _u1 z_is_nan ;
        _u3 z_status ;

        _u1 a_hide_bit; 
        _u1 b_hide_bit; 
        
        a_tf32=EXTRACT_BITS(a, 18, 0);
        b_tf32=EXTRACT_BITS(b, 18, 0);   
        a_s=EXTRACT_BITS(a_tf32, 18, 18);
        b_s=EXTRACT_BITS(b_tf32, 18, 18);
        a_e=EXTRACT_BITS(a_tf32, 17, 10);
        b_e=EXTRACT_BITS(b_tf32, 17, 10);
        a_m=EXTRACT_BITS(a_tf32, 9, 0);
        b_m=EXTRACT_BITS(b_tf32, 9, 0);
        a_e_is_zero=a_e==0;
        a_e_is_max =a_e==255;
        b_e_is_zero=b_e==0;
        b_e_is_max =b_e==255;
        a_m_is_zero=a_m==0;
        b_m_is_zero=b_m==0; 

        a_is_zero=a_e_is_zero&&a_m_is_zero;
        a_is_inf=a_e_is_max&&a_m_is_zero;
        a_is_nan=a_e_is_max&&!a_m_is_zero;
        a_is_subnorm=a_e_is_zero&&!a_m_is_zero;

        b_is_zero=b_e_is_zero&&b_m_is_zero;
        b_is_inf=b_e_is_max&&b_m_is_zero;
        b_is_nan=b_e_is_max&&!b_m_is_zero;
        b_is_subnorm=b_e_is_zero&&!b_m_is_zero;
        
        t_e=a_e+b_e - 2 * bias + a_is_subnorm + b_is_subnorm +1; 
        *z1_e=(a_is_zero||b_is_zero)? 772 :t_e; //输入有一个为0时，指数位为-252\772\10'b11_00000100

        e_overflow_pos = !EXTRACT_BITS(t_e,9,9)&&EXTRACT_BITS(t_e,8,8);
        e_overflow_neg = EXTRACT_BITS(t_e,9,9)&&(!EXTRACT_BITS(t_e,8,8));

        z_is_nan=(a_is_nan||b_is_nan)||(a_is_inf&&b_is_zero)||(a_is_zero&&b_is_inf);
        //判断是否为0         输入为0×非特殊值
        z_is_zero=(a_is_zero&&!b_is_nan&&!b_is_inf)||(b_is_zero&&!a_is_nan&&!a_is_inf);
        //判断是否为Inf       输入为inf×非0非NaN
        z_is_inf=(a_is_inf&&!b_is_zero&&!b_is_nan)||(b_is_inf&&!a_is_zero&&!a_is_nan)||e_overflow_pos||e_overflow_neg;

        a_hide_bit = (!a_is_subnorm) && (!a_is_zero) && (!a_is_inf && !a_is_nan);
        b_hide_bit = (!b_is_subnorm) && (!b_is_zero) && (!b_is_inf && !b_is_nan);

        t_M[0]=JOIN_BITS(a_hide_bit, a_m);
        t_M[1]=JOIN_BITS(b_hide_bit, b_m);
        t_mul=t_M[0]*t_M[1];
        z_s= a_s!=b_s;
        if(z_s){
            if(t_mul!= 0)  //尾数部分计算输出非0正常取补码
                t_mul=-t_mul;
            else if(a_is_zero||b_is_zero)//a,b输入为0导致的0正常输出0
                t_mul=0 ;
            else //inf导致的尾数部分给mul子模块的输入为0导致的输出0
                t_mul=4194304 ; //符号为拓展会给0的最高位补1变成23'h100_0000_0000_0000_0000_0000
        }
        z_M=t_mul;
        *z0_e = 0;
        //assign z_m                  = {{6{1'b0}}, z1_status_1r[2:0], z_m1_1[22: 0]&{23{~ab1_is_zero_1r}} }
        z_status=JOIN_BITS(z_is_zero, z_is_inf, z_is_nan);
        *z_m = CONCAT_BITS(*z_m,z_status,23);
        *z_m = CONCAT_BITS(*z_m,z_M,0);

    } else if(op_mode == 8) { //fp4

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

        for(int i=0;i<4;i++){
            if(i<=1) {
                a_fp4[i]=EXTRACT_BITS(a, (i+1)*4-1, i*4);
                b_fp4[i]=EXTRACT_BITS(b, (i+1)*4-1, i*4);
            } else  {
                a_fp4[i]=EXTRACT_BITS(a, (i+1)*4, i*4+1);
                b_fp4[i]=EXTRACT_BITS(b, (i+1)*4, i*4+1);  
            }
            a_s[i]=EXTRACT_BITS(a_fp4[i], 3, 3);
            b_s[i]=EXTRACT_BITS(b_fp4[i], 3, 3);
            z_s[i]= a_s[i]!=b_s[i];
            a_e[i]=EXTRACT_BITS(a_fp4[i], 2, 1);
            a_E[i]=(a_e[i]>0x01)? (a_e[i]-1) : 0;
            b_e[i]=EXTRACT_BITS(b_fp4[i], 2, 1);
            b_E[i]=(b_e[i]>0x01)? b_e[i] : 1;
            a_is_zero[i]=EXTRACT_BITS(a_fp4[i], 2, 0)==0;
            b_is_zero[i]=EXTRACT_BITS(b_fp4[i], 2, 0)==0;
            z_is_zero[i]=a_is_zero[i]||b_is_zero[i];
            z_e[i]=z_is_zero[i]? 0 : a_E[i]+b_E[i];
            
            a_m[i]=EXTRACT_BITS(a_fp4[i], 0, 0);
            b_m[i]=EXTRACT_BITS(b_fp4[i], 0, 0);

            t_M[0]=JOIN_BITS(a_e[i]!=0, a_m[i]);
            t_M[1]=JOIN_BITS(b_e[i]!=0, b_m[i]);
            t_mul=t_M[0]*t_M[1];
            if(z_s[i]){
                //  if(t_mul!= 0)  //尾数部分计算输出非0正常取补码
                     t_mul=-t_mul;
                //  else //应该就剩这个判断了
                //      t_mul=16 ;//'b10000
            }
            z_M[i]=t_mul;     
        }
        *z0_e=JOIN_BITS(z_e[2],z_e[0]);
        *z1_e=JOIN_BITS(z_e[3],z_e[1]);

        *z_m = CONCAT_BITS(*z_m,z_is_zero[3],31);
        *z_m = CONCAT_BITS(*z_m,z_M[3],24);
        *z_m = CONCAT_BITS(*z_m,z_is_zero[2],23);
        *z_m = CONCAT_BITS(*z_m,z_M[2],16);
        *z_m = CONCAT_BITS(*z_m,z_is_zero[1],15);
        *z_m = CONCAT_BITS(*z_m,z_M[1],8);
        *z_m = CONCAT_BITS(*z_m,z_is_zero[0],7);
        *z_m = CONCAT_BITS(*z_m,z_M[0],0);
    }
}