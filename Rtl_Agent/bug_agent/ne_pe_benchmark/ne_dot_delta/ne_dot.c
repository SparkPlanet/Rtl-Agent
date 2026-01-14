#include <assert.h>
#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
#include "ne_dot.h"

void next_timeframe(void);
void set_inputs(void);
extern const unsigned int bound;

typedef unsigned __CPROVER_bitvector[512] _u512;
typedef unsigned __CPROVER_bitvector[608] _u608;
typedef unsigned __CPROVER_bitvector[192] _u192;
typedef unsigned __CPROVER_bitvector[288] _u288;
typedef unsigned __CPROVER_bitvector[1024] _u1024;

// 全局方便debug

// unit tpye
// u0 mul×32
// u1 e_align
// u2 add_vector_m33
// u3 norm_mw33×2 &norm_mw16×2
// u4 ne_fp_ffp_add_mix & ne_fp_ffp_add_mwi26
// u5 norm_mw27×2
// u6 ne_fp_ffp_add_mwi27
// u7 ffp2fp_m33

_u1 t_u1 = 0;
_u3 t_u3 = 0;
_u37 t_u37 = 0;
_u38 t_u38 = 0;
_u44 t_u44 = 0;

union u0o_z_m_union
{
    _u512 u2i_z_m[2];
    _u32 u0o_z_m_array[32];
} u0o_z_m_union;

_u6 u0o_z0_e[32];
_u9 u0o_z1_e[32];

_u9 u1o_e_max[2];
_u16 u1o_a_e_overflow[2];
_u16 u1o_b_e_overflow[2];

union a_e_sub_union
{
    _u96 a_e_sub;
    _u6 a_e_sub_array[16];
} u1o_a_e_union0, u1o_a_e_union1;

union b_e_sub_union
{
    _u96 b_e_sub;
    _u6 b_e_sub_array[16];
} u1o_b_e_union0, u1o_b_e_union1;

_u192 ref_mul_z0_e;
_u288 ref_mul_z1_e;
// _u1024 mul_z_m          ;
_u36 ref_abscale;

_u46 u2o_z[2];
_u29 u2o_z_fp4[2];

_u47 u3i_a47[2] = {0, 0};
_u47 u3o_z47[2] = {0, 0};
_u30 u3i_a30[2] = {0, 0};
_u30 u3o_z30[2] = {0, 0};

_u48 u4o_z48 = 0;
_u40 u4i_a40[2] = {0, 0};
_u41 u4o_z41 = 0;

_u41 u5o_z[2] = {0, 0};
_u42 u6o_z = 0;

// 6. 顶层模块结构体定义
struct ne_dot
{
    _u1 i_gp_zero_skip_en;
    _u5 mode;
    _u1 fp_vld;
    _u608 fp_a;
    _u608 fp_b;
    _u32 a_scale;
    _u32 b_scale;

    _u32 fp_z;
    _u1 fp_z_vld_pre;
    _u1 fp_z_vld;
    _u1 fp_z_int;
    _u2 fp_infnan;

    // ne_dw_ffp_mul
    _u192 mul_z0_e;
    _u288 mul_z1_e;
    _u1024 mul_z_m;

    _u9 u0addtree_e_max;
    _u96 u0addtree_ae_sub;
    _u96 u0addtree_be_sub;
    _u16 u0addtree_ae_overflow;
    _u16 u0addtree_be_overflow;

    _u36 addtree_abscale;

    _u46 u0addtree_z0;
    _u29 u0addtree_z1;

    _u47 norm1_z0;
    _u47 norm1_z2;
    _u30 norm1_z1;

    _u48 ffpadd1_z0;
    _u41 ffpadd1_z1;

    _u41 norm2_z13;
    _u41 norm2_z24;

    _u4 norm2_op_mode;

    // _u3 debug_mode;
    // _u41 debug_wire;

    _u42 ffpadd2_z;
};

// 7. 外部实例声明
extern struct ne_dot ne_dot;

// 10. 顶层模块功能实现函数
void c_ne_dot(
    _u1 i_gp_zero_skip_en,
    _u4 mode,
    _u608 fp_a,
    _u608 fp_b,
    _u32 a_scale,
    _u32 b_scale,

    _u32 *fp_z,
    _u1 *fp_z_int,
    _u2 *fp_infnan)
{
    *fp_z = 0;
    *fp_z_int = 0;
    *fp_infnan = 0;

    _u19 u0i_a[32];
    _u19 u0i_b[32];
    for (int i = 0; i < 32; i++)
    {
        u0i_a[i] = fp_a >> i * 19;
        u0i_b[i] = fp_b >> i * 19;
    }

    // union u0o_z_m_union {
    //     _u512 u2i_z_m[2];
    //     _u32 u0o_z_m_array[32];
    // } u0o_z_m_union;
    // _u6  u0o_z0_e[32];
    // _u9  u0o_z1_e[32];

    _u4 mode4bit = EXTRACT_BITS(mode, 3, 0);
    for (int i = 0; i < 32; i++)
    {
        c_ne_fp_ffp_mul(mode4bit, u0i_a[i], u0i_b[i], &u0o_z0_e[i], &u0o_z1_e[i], &u0o_z_m_union.u0o_z_m_array[i]);
        // if(i==31) u0o_z_m[i]=0; //引入明显错误判断是否有在正常工作
    }

    // mul 到 e_align的输入拼接处理
    _u144 u1i_a_e[2] = {0, 0}; // 经典不置0会出错
    _u96 u1i_b_e[2] = {0, 0};
    for (int i = 0; i < 16; i++)
    {
        u1i_a_e[0] |= (_u144)u0o_z1_e[i] << i * 9;
        u1i_b_e[0] |= (_u96)u0o_z0_e[i] << i * 6;
    }
    for (int i = 16; i < 32; i++)
    {
        u1i_a_e[1] |= (_u144)u0o_z1_e[i] << (i - 16) * 9;
        u1i_b_e[1] |= (_u96)u0o_z0_e[i] << (i - 16) * 6;
    }

    // ref_mul_z0_e = (_u192)u1i_b_e[1] << 96 |  (_u192)u1i_b_e[0];
    // assert(ref_mul_z0_e == ne_dot.mul_z0_e);
    // ref_mul_z1_e = (_u288)u1i_a_e[1] << 144 |  (_u288)u1i_a_e[0];
    // assert(ref_mul_z1_e == ne_dot.mul_z1_e);

    // debug用
    //  _u144 u1i_a_e[0]=ne_dot.mul_z1_e,u1i_a_e[1]=ne_dot.mul_z1_e>>144;
    //  _u96 u1i_b_e[0]=ne_dot.mul_z0_e,u1i_b_e[1]=ne_dot.mul_z0_e>>96;

    // Runtime decision procedure: 16.744s
    // VERIFICATION SUCCESSFUL
    // 乘法器这一块是没问题的

    // _u4 e_align_mode = mode4bit;
    // _u9 u1o_e_max[2];
    // _u16 u1o_a_e_overflow[2];
    // _u16 u1o_b_e_overflow[2];

    c_ne_fp_ffp_e_align(
        mode4bit,
        u1i_a_e[0],
        u1i_b_e[0],
        &u1o_e_max[0],
        &u1o_a_e_union0.a_e_sub_array,
        &u1o_b_e_union0.b_e_sub_array,
        &u1o_a_e_overflow[0],
        &u1o_b_e_overflow[0]);

    c_ne_fp_ffp_e_align(
        mode4bit,
        u1i_a_e[1],
        u1i_b_e[1],
        &u1o_e_max[1],
        &u1o_a_e_union1.a_e_sub_array,
        &u1o_b_e_union1.b_e_sub_array,
        &u1o_a_e_overflow[1],
        &u1o_b_e_overflow[1]);

    _u18 u2i_ab_scale[2] = {0, 0};
    _s8 a_scale_slice[4], b_scale_slice[4];
    _s9 ab_scale_slice[4];
    for (int i = 0; i < 4; i++)
    {
        a_scale_slice[i] = EXTRACT_BITS(a_scale, (i + 1) * 8 - 1, i * 8);
        b_scale_slice[i] = EXTRACT_BITS(b_scale, (i + 1) * 8 - 1, i * 8);
        ab_scale_slice[i] = (_s9)a_scale_slice[i] + (_s9)b_scale_slice[i];
    }

    u2i_ab_scale[0] = CONCAT_BITS(u2i_ab_scale[0], ab_scale_slice[0], 0);
    u2i_ab_scale[0] = CONCAT_BITS(u2i_ab_scale[0], ab_scale_slice[1], 9);
    u2i_ab_scale[1] = CONCAT_BITS(u2i_ab_scale[1], ab_scale_slice[2], 0);
    u2i_ab_scale[1] = CONCAT_BITS(u2i_ab_scale[1], ab_scale_slice[3], 9);

    ref_abscale = CONCAT_BITS(ref_abscale, u2i_ab_scale[0], 0);
    ref_abscale = CONCAT_BITS(ref_abscale, u2i_ab_scale[1], 18);

    // _u46 u2o_z[2];
    // _u29 u2o_z_fp4[2];
    VectorM33Result ref_t = c_ne_fp_ffp_add_vector_m33(
        mode4bit,
        u1o_e_max[0],
        u2i_ab_scale[0],
        u1o_a_e_union0.a_e_sub, // 16*6 = 96
        u1o_b_e_union0.b_e_sub, // 16*6 = 96
        u1o_a_e_overflow[0],
        u1o_b_e_overflow[0],
        u0o_z_m_union.u2i_z_m[0]
        // ,
        // &u2o_z[0],
        // &u2o_z_fp4[0]
    );
    u2o_z[0] = ref_t.z;
    u2o_z_fp4[0] = ref_t.z_fp4;

    ref_t = c_ne_fp_ffp_add_vector_m33(
        mode4bit,
        u1o_e_max[1],
        u2i_ab_scale[1],
        u1o_a_e_union1.a_e_sub, // 16*6 = 96
        u1o_b_e_union1.b_e_sub, // 16*6 = 96
        u1o_a_e_overflow[1],
        u1o_b_e_overflow[1],
        u0o_z_m_union.u2i_z_m[1]
        // ,
        // &u2o_z[1],
        // &u2o_z_fp4[1]
    );
    u2o_z[1] = ref_t.z;
    u2o_z_fp4[1] = ref_t.z_fp4;

    // _u47 u3i_a47[2]={0,0};
    // _u47 u3o_z47[2]={0,0};
    // _u30 u3i_a30[2]={0,0};
    // _u30 u3o_z30[2]={0,0};

    _u3 mode3bit = EXTRACT_BITS(mode, 2, 0);
    for (int i = 0; i < 2; i++)
    {
        u3i_a47[i] = u2o_z[i];
        t_u1 = EXTRACT_BITS(u2o_z[i], 32, 32);
        u3i_a47[i] = CONCAT_BITS(u3i_a47[i], t_u1, 43);
        t_u1 = EXTRACT_BITS(u2o_z[i], 45, 45);
        u3i_a47[i] = CONCAT_BITS(u3i_a47[i], t_u1, 44);
        t_u1 = EXTRACT_BITS(u2o_z[i], 44, 44);
        u3i_a47[i] = CONCAT_BITS(u3i_a47[i], t_u1, 45);
        t_u1 = EXTRACT_BITS(u2o_z[i], 43, 43);
        u3i_a47[i] = CONCAT_BITS(u3i_a47[i], t_u1, 46);

        u3i_a30[i] = u2o_z_fp4[i];
        t_u1 = EXTRACT_BITS(u2o_z_fp4[i], 15, 15);
        u3i_a30[i] = CONCAT_BITS(u3i_a30[i], t_u1, 26);
        t_u1 = EXTRACT_BITS(u2o_z_fp4[i], 28, 28);
        u3i_a30[i] = CONCAT_BITS(u3i_a30[i], t_u1, 27);
        t_u1 = EXTRACT_BITS(u2o_z_fp4[i], 27, 27);
        u3i_a30[i] = CONCAT_BITS(u3i_a30[i], t_u1, 28);
        t_u1 = EXTRACT_BITS(u2o_z_fp4[i], 26, 26);
        u3i_a30[i] = CONCAT_BITS(u3i_a30[i], t_u1, 29);
    }

    u3o_z47[0] = c_ne_fp_ffp_norm_mw33(u3i_a47[0], mode3bit);
    u3o_z47[1] = c_ne_fp_ffp_norm_mw33(u3i_a47[1], mode3bit);
    u3o_z30[0] = c_ne_fp_ffp_norm_mw16(u3i_a30[0], mode3bit);
    u3o_z30[1] = c_ne_fp_ffp_norm_mw16(u3i_a30[1], mode3bit);

    // _u48 u4o_z48=0;

    // debug用
    //  _u3 status_check;
    //  status_check=EXTRACT_BITS(u3o_z47[0],46,44);
    //  assert(status_check == 0||status_check == 1||status_check == 2||status_check == 4);
    //  status_check=EXTRACT_BITS(u3o_z47[1],46,44);
    //  assert(status_check == 0||status_check == 1||status_check == 2||status_check == 4);
    //  for(int i=0;i<2;i++){
    //      _u24 u3o_z47_part=(_u47)u3o_z47[0]>>i*24;
    //      printf("u3o_z47_part: %d\n", u3o_z47_part);
    //  }

    u4o_z48 = c_ne_fp_ffp_add_mix(u3o_z47[0], u3o_z47[1], mode4bit);

    // _u40 u4i_a40[2]={0,0};
    // _u41 u4o_z41=0;
    u4i_a40[0] = (_u40)u3o_z30[0] << 10;
    u4i_a40[1] = (_u40)u3o_z30[1] << 10;
    u4o_z41 = c_ne_fp_ffp_add_mwi26(u4i_a40[0], u4i_a40[1], mode3bit);

    _u41 u5i_a[2] = {0, 0};
    // _u41 u5o_z[2]={0,0};

    t_u37 = EXTRACT_BITS(u4o_z48, 43, 7);
    u5i_a[0] = t_u37;
    t_u1 = EXTRACT_BITS(u4o_z48, 33, 33);
    u5i_a[0] = CONCAT_BITS(u5i_a[0], t_u1, 37);
    t_u3 = EXTRACT_BITS(u4o_z48, 47, 45);
    u5i_a[0] = CONCAT_BITS(u5i_a[0], t_u3, 38);

    t_u37 = EXTRACT_BITS(u4o_z41, 36, 0);
    u5i_a[1] = t_u37;
    t_u1 = EXTRACT_BITS(u4o_z41, 26, 26);
    u5i_a[1] = CONCAT_BITS(u5i_a[1], t_u1, 37);
    t_u3 = EXTRACT_BITS(u4o_z41, 40, 38);
    u5i_a[1] = CONCAT_BITS(u5i_a[1], t_u3, 38);

    u5o_z[0] = c_ne_fp_ffp_norm_mw27(u5i_a[0], mode3bit);
    u5o_z[1] = c_ne_fp_ffp_norm_mw27(u5i_a[1], mode3bit);

    _u41 u6i_a = (mode4bit == 8) ? u5o_z[0] : 0;
    // _u42 u6o_z=0;
    u6o_z = c_ne_fp_ffp_add_mwi27(u6i_a, u5o_z[1], mode3bit);
    //      struct module_ne_fp_ffp_add_mwi27 {
    //    _u41 a;
    //    _u41 b;
    //    _u3  mode;
    //    _u42 z;
    //  };
    // ne_fp_ffp_add_mwi27 u_ffpadd2(
    // .clk (clk ),
    // .a   (norm2_z13_r&{41{ffpadd2_op_mode[3]}}),    //3status + s1e10+s1s1m15+10bit
    // .b   (norm2_z24_r),
    // .z   (ffpadd2_z ),   //3status + s1e10m18+10bit; //nan/inf/zero/s1/e10/s1+s1+m16+10bit
    // .mode(ffpadd2_op_mode[2:0])                //3'b100: tf32, 3'b010: fp8, 3'b001: int8
    // );

    // wire [46:0] ffp2fp_a_r_w = ffpadd2_op_mode_1r[3] ?  {ffpadd2_z[41:39],ffpadd2_z[37:28],ffpadd2_z[27:0],6'd0} :
    //                                                     {ffpadd1_z0_r2[46:44],ffpadd1_z0_r2[43:34],ffpadd1_z0_r2[33:0]} ;
    // reg  [46:0] ffp2fp_a_r ;
    _u47 u7i_a_select[2] = {0, 0};
    t_u38 = EXTRACT_BITS(u6o_z, 37, 0);
    t_u3 = EXTRACT_BITS(u6o_z, 41, 39);
    u7i_a_select[0] = CONCAT_BITS(u7i_a_select[0], t_u38, 6);
    u7i_a_select[0] = CONCAT_BITS(u7i_a_select[0], t_u3, 44);

    // ffpadd1_z0_r   <= {ffpadd1_z0[47:45],ffpadd1_z0[43:34],ffpadd1_z0[33:0]};//int8_fp8_fp16_fp4
    t_u44 = EXTRACT_BITS(u4o_z48, 43, 0);
    t_u3 = EXTRACT_BITS(u4o_z48, 47, 45);
    u7i_a_select[1] = CONCAT_BITS(u7i_a_select[1], t_u44, 0);
    u7i_a_select[1] = CONCAT_BITS(u7i_a_select[1], t_u3, 44);

    _u47 u7i_a = (mode4bit == 8) ? u7i_a_select[0] : u7i_a_select[1];
    _u32 u7o_z = 0;
    _u2 u7o_z_is_infnan = 0;
    c_ne_fp_ffp2fp_m33(u7i_a, mode4bit, &u7o_z, &u7o_z_is_infnan);

    *fp_z_int = mode4bit == 1;
    *fp_z = u7o_z;
    *fp_infnan = u7o_z_is_infnan;

    // u_dot_ffp2fp(
    //     .clk        (clk            ) ,
    //     .a          (ffp2fp_a_r     ) , //nan/inf/zero/e10/s1+s1+m32
    //     .z          (ffp2fp_z       ) ,
    //     .mode       (ffp2fp_op_mode_r[3:0] ),
    //     .z_is_infnan(z_is_infnan    )
    // );
    // c_ne_fp_ffp2fp_m33(
    //     _u47 a,
    //     _u4 mode,

    //     _u32 *z,
    //     _u2 *z_is_infnan
    // )
}

// 11. 主函数（测试用例）
int main()
{
    // 声明
    _u1 i_gp_zero_skip_en;
    _u4 mode;
    _u1 fp_vld;
    _u608 fp_a;
    _u608 fp_b;
    _u32 a_scale;
    _u32 b_scale;

    _u32 fp_z;
    _u1 fp_z_vld_pre;
    _u1 fp_z_vld;
    _u1 fp_z_int;
    _u2 fp_infnan;

    // i_gp_zero_skip_en=0;
    __CPROVER_assume(mode == 1 || mode == 2 || mode == 8);
    ne_dot.i_gp_zero_skip_en = i_gp_zero_skip_en;
    ne_dot.mode = mode;
    ne_dot.fp_vld = fp_vld;
    ne_dot.fp_a = fp_a;
    ne_dot.fp_b = fp_b;
    ne_dot.a_scale = a_scale;
    ne_dot.b_scale = b_scale;

    set_inputs();
    c_ne_dot(i_gp_zero_skip_en, mode, fp_a, fp_b, a_scale, b_scale, &fp_z, &fp_z_int, &fp_infnan);

    // _u6 act_mul_z0_e;
    // _u9 act_mul_z1_e;
    // for(int i=0;i<32;i++){
    //     act_mul_z0_e=ne_dot.mul_z0_e>>i*6;
    //     if(act_mul_z0_e != u0o_z0_e[i]) {
    //         printf("ref_mul_z0_e: %d\n",u0o_z0_e[i]);
    //         printf("act_mul_z0_e: %d\n",act_mul_z0_e);
    //     }
    //     assert(act_mul_z0_e == u0o_z0_e[i]);
    //     act_mul_z1_e=ne_dot.mul_z1_e>>i*9;
    //     assert(act_mul_z1_e == u0o_z1_e[i]);
    //     if(act_mul_z1_e != u0o_z1_e[i]) {
    //         printf("ref_mul_z1_e: %d\n",u0o_z1_e[i]);
    //         printf("act_mul_z1_e: %d\n",act_mul_z1_e);
    //     }
    //     assert(act_mul_z1_e == u0o_z1_e[i]);
    // }
    next_timeframe();
    // _u32 act_mul_z_m;
    // for(int i=0;i<32;i++){
    //     act_mul_z_m=ne_dot.mul_z_m>>i*32;
    //     if(act_mul_z_m != u0o_z_m_union.u0o_z_m_array[i]) {
    //         printf("ref_mul_z_m: %d\n",u0o_z_m_union.u0o_z_m_array[i]);
    //         printf("act_mul_z_m: %d\n",act_mul_z_m);
    //     }
    //     assert(act_mul_z_m == u0o_z_m_union.u0o_z_m_array[i]);
    // }

    next_timeframe();
    // printf("ref_e_max: %d\n", u1o_e_max[0]);
    // printf("act_e_max: %d\n", ne_dot.u0addtree_e_max);
    // assert(u1o_e_max[0] == ne_dot.u0addtree_e_max);

    // _u6 act_final=0;
    // _u6 ref_final=0;
    // for(int i=0; i<16; i++) {
    //     ref_final= u1o_a_e_union0.a_e_sub>>i*6;
    //     act_final= ne_dot.u0addtree_ae_sub>>i*6;
    //     if(ref_final != act_final) {
    //         printf("ref_a_e_sub: %d\n",ref_final);
    //         printf("act_a_e_sub: %d\n",act_final);
    //     }
    // }
    // assert(u1o_a_e_union0.a_e_sub == ne_dot.u0addtree_ae_sub);
    // assert(u1o_b_e_union0.b_e_sub == ne_dot.u0addtree_be_sub);
    // assert(u1o_a_e_overflow[0] == ne_dot.u0addtree_ae_overflow);
    // assert(u1o_b_e_overflow[0] == ne_dot.u0addtree_be_overflow);

    // _u18 act_final=0;
    // _u18 ref_final=0;
    // for(int i=0; i<2; i++) {
    //     ref_final= ref_abscale>>i*18;
    //     act_final= ne_dot.addtree_abscale>>i*18;
    //     if(ref_final != act_final) {
    //         printf("ref_abscale: %d\n",ref_final);
    //         printf("act_abscale: %d\n",act_final);
    //     }
    // }
    // assert(ref_abscale == ne_dot.addtree_abscale);
    next_timeframe();
    next_timeframe();

    // VectorM33Result ref = c_ne_fp_ffp_add_vector_m33(
    //     mode4bit,
    //     u1o_e_max[0],
    //     u2i_ab_scale[0],
    //     u1o_a_e_union0.a_e_sub,      // 16*6 = 96
    //     u1o_b_e_union0.b_e_sub,      // 16*6 = 96
    //     u1o_a_e_overflow[0],
    //     u1o_b_e_overflow[0],
    //     u0o_z_m_union.u2i_z_m[0]
    //     // ,
    //     // &u2o_z[0],
    //     // &u2o_z_fp4[0]
    // );
    // u2o_z[0] = ref.z;
    // u2o_z_fp4[0] = ref.z_fp4;
    // ne_fp_ffp_add_vector_m33 u0_addtree(
    //     .clk                (clk                    ) ,

    //     .op_mode            (addtree_op_mode[3:0]   ),
    //     .e_max              (u0addtree_e_max        ),
    //     .ab_scale           (addtree_abscale[17:0]  ),
    //     .ae_sub             (u0addtree_ae_sub       ),
    //     .be_sub             (u0addtree_be_sub       ),
    //     .a_e_overflow       (u0addtree_ae_overflow  ),
    //     .b_e_overflow       (u0addtree_be_overflow  ),
    //     .a_m                (mul_z_m_r[16*32-1:0]   ),
    //     .z                  (u0addtree_z0           ),
    //     .z_fp4              (u0addtree_z1           )
    // );
    // assert(u2o_z[0] == ne_dot.u0addtree_z0);

    // printf("ref_z_fp4: %d\n", u2o_z_fp4[0]);
    // printf("act_z_fp4: %d\n", ne_dot.u0addtree_z1);
    // assert(u2o_z_fp4[0] == ne_dot.u0addtree_z1);
    // SAT checker: instance is UNSATISFIABLE
    // Runtime decision procedure: 88.086s

    // printf("ref_norm1_z0: %d\n", u3o_z30[0]);
    // printf("act_norm1_z0: %d\n", ne_dot.norm1_z1);
    // assert(u3o_z47[0] == ne_dot.norm1_z0);
    // assert(u3o_z47[1] == ne_dot.norm1_z2);
    // assert(u3o_z30[0] == ne_dot.norm1_z1);

    next_timeframe(); // norm1_z0 ->norm1_z0_r
    next_timeframe(); // aad_mix出结果

    // for(int i=0;i<2;i++){
    //     _u24 ref_ffpadd1_z0=u4o_z48>>i*24;
    //     _u24 act_ffpadd1_z0=ne_dot.ffpadd1_z0>>i*24;
    //     printf("ref_ffpadd1_z0: %d\n", ref_ffpadd1_z0);
    //     printf("act_ffpadd1_z0: %d\n", act_ffpadd1_z0);
    // }

    // _u3 mode3bit=EXTRACT_BITS(mode, 2, 0);
    // u4o_z48=ne_dot.ffpadd1_z0;
    // u4o_z41=ne_dot.ffpadd1_z1;
    // _u41 u5i_a[2]={0,0};

    // t_u37=EXTRACT_BITS(u4o_z48,43,7);
    // u5i_a[0] =t_u37;
    // t_u1 =EXTRACT_BITS(u4o_z48,33,33);
    // u5i_a[0]=CONCAT_BITS(u5i_a[0],t_u1,37);
    // t_u3 =EXTRACT_BITS(u4o_z48,47,45);
    // u5i_a[0]=CONCAT_BITS(u5i_a[0],t_u3,38);
    // u5o_z[0]=c_ne_fp_ffp_norm_mw27(u5i_a[0], mode3bit);

    // t_u37=EXTRACT_BITS(u4o_z41,36,0);
    // u5i_a[1] =t_u37;
    // t_u1 =EXTRACT_BITS(u4o_z41,26,26);
    // u5i_a[1]=CONCAT_BITS(u5i_a[1],t_u1,37);
    // t_u3 =EXTRACT_BITS(u4o_z41,40,38);
    // u5i_a[1]=CONCAT_BITS(u5i_a[1],t_u3,38);
    // u5o_z[1]=c_ne_fp_ffp_norm_mw27(u5i_a[1], mode3bit);

    // assert(u4o_z48 == ne_dot.ffpadd1_z0);
    // assert(u4o_z41 == ne_dot.ffpadd1_z1);
    next_timeframe(); // ffpadd1_z0 ->r

    // printf("mode3bit: %d\n", mode3bit);
    // printf("debug_mode: %d\n", ne_dot.debug_mode);
    // assert(mode3bit == ne_dot.debug_mode);
    // assert(u5i_a[0] == ne_dot.debug_wire);
    // _u3 debug_mode=ne_dot.debug_mode;
    // u5i_a[0]=ne_dot.debug_wire;
    // u5o_z[0]=c_ne_fp_ffp_norm_mw27(u5i_a[0], debug_mode);
    // assert(u5o_z[0] == ne_dot.norm2_z13);
    // // u5o_z[1]=0;//引入明显错误
    // assert(u5o_z[1] == ne_dot.norm2_z24);

    next_timeframe();
    next_timeframe();
    // assert(u6o_z == ne_dot.ffpadd2_z);
    next_timeframe();
    next_timeframe();
    assert(ne_dot.fp_z_vld_pre == fp_vld);
    next_timeframe();
    printf("fp_z: %d\n", fp_z);
    printf("ne_dot.fp_z: %d\n", ne_dot.fp_z);
    printf("fp_z_int: %d\n", fp_z_int);
    printf("ne_dot.fp_z_int: %d\n", ne_dot.fp_z_int);
    printf("fp_infnan: %d\n", fp_infnan);
    printf("ne_dot.fp_infnan: %d\n", ne_dot.fp_infnan);
    assert(ne_dot.fp_z == fp_z);
    assert(ne_dot.fp_z_vld == fp_vld);
    assert(ne_dot.fp_z_int == fp_z_int);
    assert(ne_dot.fp_infnan == fp_infnan);
    // assert(1==0); 引入明显错误看看是否真的在工作
    return 0;
}
