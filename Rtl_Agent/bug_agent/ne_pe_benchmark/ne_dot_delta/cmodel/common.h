#include <assert.h>
#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>

#define BIT_WIDTH(x) _Generic((x), _u1: 1, _u2: 2, _u3: 3, _u4: 4, _u5: 5, _u6: 6, _u7: 7, _u8: 8, _u9: 9, _u10: 10, _u11: 11, _u12: 12, _u13: 13, _u14: 14, _u15: 15, _u16: 16, _u17: 17, _u18: 18, _u19: 19, _u20: 20, _u21: 21, _u22: 22, _u23: 23, _u24: 24, _u25: 25, _u26: 26, _u27: 27, _u28: 28, _u29: 29, _u30: 30, _u31: 31, _u32: 32, _u33: 33, _u34: 34, _u35: 35, _u36: 36, _u37: 37, _u38: 38, _u39: 39, _u40: 40, _u41: 41, _u42: 42, _u43: 43, _u44: 44, _u45: 45, _u46: 46, _u47: 47, _u48: 48, _u49: 49, _u50: 50, _u51: 51, _u52: 52, _u53: 53, _u54: 54, _u55: 55, _u56: 56, _u57: 57, _u58: 58, _u59: 59, _u60: 60, _u61: 61, _u62: 62, _u63: 63, _s1: 1, _s2: 2, _s3: 3, _s4: 4, _s5: 5, _s6: 6, _s7: 7, _s8: 8, _s9: 9, _s10: 10, _s11: 11, _s12: 12, _s13: 13, _s14: 14, _s15: 15, _s16: 16, _s17: 17, _s18: 18, _s19: 19, _s20: 20, _s21: 21, _s22: 22, _s23: 23, _s24: 24, _s25: 25, _s26: 26, _s27: 27, _s28: 28, _s29: 29, _s30: 30, _s31: 31, _s32: 32, _s33: 33, _s34: 34, _s35: 35, _s36: 36, _s37: 37, _s38: 38, _s39: 39, _s40: 40, _s41: 41, _s42: 42, _s43: 43, _s44: 44, _s45: 45, _s46: 46, _s47: 47, _s48: 48, _s49: 49, _s50: 50, _s51: 51, _s52: 52, _s53: 53, _s54: 54, _s55: 55, _s56: 56, _s57: 57, _s58: 58, _s59: 59, _s60: 60, _s61: 61, _s62: 62, _s63: 63, default: -1)
#define EXTRACT_BITS(a, high, low) (((a) >> (low)) & ((1ULL << ((high) - (low) + 1)) - 1))
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

#ifndef MASK
#define MASK(w) ((((uint64_t)1) << (w)) - 1)
#endif
#define MASK64(w) ((w) >= 64 ? (~0ULL) : ((1ULL << (w)) - 1))
#define GET_BITS(val, high, low) (((val) >> (low)) & MASK((high) - (low) + 1))
#define MASK_128(w) ((((unsigned __int128)1) << (w)) - 1)
// 提取 bits [high:low]
#define SLICE(val, high, low) (((val) >> (low)) & MASK_128((high) - (low) + 1))
// 获取单 bit
#define BIT(val, idx) (((val) >> (idx)) & 1)
// 拼接 {a, b}，其中 width_b 是 b 的位宽
#define CAT(a, b, width_b) ((((unsigned __int128)(a)) << (width_b)) | ((unsigned __int128)(b) & MASK_128(width_b)))

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
// 1. 自定义位宽类型
typedef signed __CPROVER_bitvector[1] _s1;
typedef signed __CPROVER_bitvector[2] _s2;
typedef signed __CPROVER_bitvector[3] _s3;
typedef signed __CPROVER_bitvector[4] _s4;
typedef signed __CPROVER_bitvector[5] _s5;
typedef signed __CPROVER_bitvector[6] _s6;
typedef signed __CPROVER_bitvector[7] _s7;
typedef signed __CPROVER_bitvector[8] _s8;
typedef signed __CPROVER_bitvector[9] _s9;
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
