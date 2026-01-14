# Makefile
HW-CBMC=../../hw-cbmc/hw-cbmc
LOG_PREFIX=verfication_  # 日志文件名前缀
LOG_SUFFIX=.log   # 日志文件名后缀

# 默认目标
all: t_ne_dot

t_ne_dot: 
	@# 直接在shell中生成带时间缀的完整日志文件名
	@LOG_FILE="verfication_$$(date '+%Y%m%d_%H%M%S').log"; \
	 echo "$$(date '+%Y-%m-%d %H:%M:%S'): Running command: $(HW-CBMC) ne_dot.c --module ne_dot ne_dot.v ./rtl/*.v --bound 12" > "$$LOG_FILE"; \
	 echo "$$(date '+%Y-%m-%d %H:%M:%S'): Starting verification..." >> "$$LOG_FILE"; \
	 $(HW-CBMC) ne_dot.c --module ne_dot ne_dot.v ./rtl/*.v --bound 12 2>&1 | tee -a "$$LOG_FILE"; \
	 echo "$$(date '+%Y-%m-%d %H:%M:%S'): Verification completed" >> "$$LOG_FILE"; \
	 echo "Log saved to: $$LOG_FILE"; \

t_submodules: t_add_mwi26 t_add_mwi27 t_add_mix t_add_vector t_e_align t_mul t_norm_mw16 t_norm_mw27 t_norm_mw33 t_ffp2fp

t_add_mwi26: 
	@# 直接在shell中生成带时间缀的完整日志文件名
	@LOG_FILE="verfication_add_mwi26_$$(date '+%Y%m%d_%H%M%S').log"; \
	 echo "$$(date '+%Y-%m-%d %H:%M:%S'): Running command: $(HW-CBMC)  cmodel/ne_fp_ffp_add_mwi26.c  rtl/DW01_add_w29.v  rtl/ne_fp_ffp_add_mwi26.v --module ne_fp_ffp_add_mwi26 --bound 1" > "$$LOG_FILE"; \
	 echo "$$(date '+%Y-%m-%d %H:%M:%S'): Starting verification..." >> "$$LOG_FILE"; \
	 $(HW-CBMC)  cmodel/ne_fp_ffp_add_mwi26.c  rtl/DW01_add_w29.v  rtl/ne_fp_ffp_add_mwi26.v --module ne_fp_ffp_add_mwi26 --bound 1 2>&1 | tee -a "$$LOG_FILE"; \
	 echo "$$(date '+%Y-%m-%d %H:%M:%S'): Verification completed" >> "$$LOG_FILE"; \
	 echo "Log saved to: $$LOG_FILE"; \

t_add_mwi27: 
	@# 直接在shell中生成带时间缀的完整日志文件名
	@LOG_FILE="verfication_add_mwi27_$$(date '+%Y%m%d_%H%M%S').log"; \
	 echo "$$(date '+%Y-%m-%d %H:%M:%S'): Running command: $(HW-CBMC)  cmodel/ne_fp_ffp_add_mwi27.c  rtl/DW01_add_w30.v  rtl/ne_fp_ffp_add_mwi27.v --module ne_fp_ffp_add_mwi27 --bound 1" > "$$LOG_FILE"; \
	 echo "$$(date '+%Y-%m-%d %H:%M:%S'): Starting verification..." >> "$$LOG_FILE"; \
	 $(HW-CBMC)  cmodel/ne_fp_ffp_add_mwi27.c  rtl/DW01_add_w30.v  rtl/ne_fp_ffp_add_mwi27.v --module ne_fp_ffp_add_mwi27 --bound 1 2>&1 | tee -a "$$LOG_FILE"; \
	 echo "$$(date '+%Y-%m-%d %H:%M:%S'): Verification completed" >> "$$LOG_FILE"; \
	 echo "Log saved to: $$LOG_FILE"; \

t_add_mix: 
	@# 直接在shell中生成带时间缀的完整日志文件名
	@LOG_FILE="verfication_add_mix_$$(date '+%Y%m%d_%H%M%S').log"; \
	 echo "$$(date '+%Y-%m-%d %H:%M:%S'): Running command: $(HW-CBMC)  cmodel/ne_fp_ffp_add_mix.c  rtl/DW01_add_w36.v  rtl/ne_fp_ffp_add_mix.v --module ne_fp_ffp_add_mix --bound 1" > "$$LOG_FILE"; \
	 echo "$$(date '+%Y-%m-%d %H:%M:%S'): Starting verification..." >> "$$LOG_FILE"; \
	 $(HW-CBMC)  cmodel/ne_fp_ffp_add_mix.c  rtl/DW01_add_w36.v  rtl/ne_fp_ffp_add_mix.v --module ne_fp_ffp_add_mix --bound 1 2>&1 | tee -a "$$LOG_FILE"; \
	 echo "$$(date '+%Y-%m-%d %H:%M:%S'): Verification completed" >> "$$LOG_FILE"; \
	 echo "Log saved to: $$LOG_FILE"; \

t_add_vector: 
	@# 直接在shell中生成带时间缀的完整日志文件名
	@LOG_FILE="verfication_add_vector_$$(date '+%Y%m%d_%H%M%S').log"; \
	 echo "$$(date '+%Y-%m-%d %H:%M:%S'): Running command: $(HW-CBMC)  cmodel/ne_fp_ffp_add_vector_m33.c  rtl/DW01_add_w31.v rtl/DW01_add_w32.v rtl/DW01_add_w15.v rtl/DW02_tree_w15n32.v rtl/DW02_tree_w32n16.v rtl/DW02_tree_w31n16.v  rtl/ne_fp_ffp_add_vector_m33.v --module ne_fp_ffp_add_vector_m33 --bound 2" > "$$LOG_FILE"; \
	 echo "$$(date '+%Y-%m-%d %H:%M:%S'): Starting verification..." >> "$$LOG_FILE"; \
	 $(HW-CBMC)  cmodel/ne_fp_ffp_add_vector_m33.c  rtl/DW01_add_w31.v rtl/DW01_add_w32.v rtl/DW01_add_w15.v rtl/DW02_tree_w15n32.v rtl/DW02_tree_w32n16.v rtl/DW02_tree_w31n16.v  rtl/ne_fp_ffp_add_vector_m33.v --module ne_fp_ffp_add_vector_m33 --bound 2 2>&1 | tee -a "$$LOG_FILE"; \
	 echo "$$(date '+%Y-%m-%d %H:%M:%S'): Verification completed" >> "$$LOG_FILE"; \
	 echo "Log saved to: $$LOG_FILE"; \

t_e_align: 
	@# 直接在shell中生成带时间缀的完整日志文件名
	@LOG_FILE="verfication_e_align_$$(date '+%Y%m%d_%H%M%S').log"; \
	 echo "$$(date '+%Y-%m-%d %H:%M:%S'): Running command: $(HW-CBMC) cmodel/ne_fp_ffp_e_align.c --module ne_fp_ffp_e_align rtl/ne_fp_ffp_e_align.v rtl/DW_minmax_w6n4.v rtl/DW_minmax_w6n5.v rtl/DW_minmax_w9n4.v rtl/DW_minmax_w9n5.v --bound 2 > $$LOG_FILE"; \
	 echo "$$(date '+%Y-%m-%d %H:%M:%S'): Starting verification..." >> "$$LOG_FILE"; \
	 $(HW-CBMC) cmodel/ne_fp_ffp_e_align.c --module ne_fp_ffp_e_align rtl/ne_fp_ffp_e_align.v rtl/DW_minmax_w6n4.v rtl/DW_minmax_w6n5.v rtl/DW_minmax_w9n4.v rtl/DW_minmax_w9n5.v --bound 2 2>&1 | tee -a "$$LOG_FILE"; \
	 echo "$$(date '+%Y-%m-%d %H:%M:%S'): Verification completed" >> "$$LOG_FILE"; \
	 echo "Log saved to: $$LOG_FILE"; \

t_mul: 
	@# 直接在shell中生成带时间缀的完整日志文件名
	@LOG_FILE="verfication_mul_$$(date '+%Y%m%d_%H%M%S').log"; \
	 echo "$$(date '+%Y-%m-%d %H:%M:%S'): Running command: $(HW-CBMC) cmodel/ne_fp_ffp_mul.c --module ne_fp_ffp_mul rtl/DW02_mult_i8.v rtl/DW02_mult_i11.v rtl/ne_fp_ffp_mul.v --bound 1" > "$$LOG_FILE"; \
	 echo "$$(date '+%Y-%m-%d %H:%M:%S'): Starting verification..." >> "$$LOG_FILE"; \
	 $(HW-CBMC) cmodel/ne_fp_ffp_mul.c --module ne_fp_ffp_mul rtl/DW02_mult_i8.v rtl/DW02_mult_i11.v rtl/ne_fp_ffp_mul.v  --bound 1 2>&1 | tee -a "$$LOG_FILE"; \
	 echo "$$(date '+%Y-%m-%d %H:%M:%S'): Verification completed" >> "$$LOG_FILE"; \
	 echo "Log saved to: $$LOG_FILE"; \

t_norm_mw16: 
	@# 直接在shell中生成带时间缀的完整日志文件名
	@LOG_FILE="verfication_norm_mw16_$$(date '+%Y%m%d_%H%M%S').log"; \
	 echo "$$(date '+%Y-%m-%d %H:%M:%S'): Running command: $(HW-CBMC)  cmodel/ne_fp_ffp_norm_mw16.c rtl/DW_lsd_w15.v rtl/ne_fp_sfl_blk_w16s4.v rtl/ne_fp_ffp_norm_mw16.v  --module ne_fp_ffp_norm_mw16 --bound 1" > "$$LOG_FILE"; \
	 echo "$$(date '+%Y-%m-%d %H:%M:%S'): Starting verification..." >> "$$LOG_FILE"; \
	 $(HW-CBMC)  cmodel/ne_fp_ffp_norm_mw16.c rtl/DW_lsd_w15.v rtl/ne_fp_sfl_blk_w16s4.v rtl/ne_fp_ffp_norm_mw16.v  --module ne_fp_ffp_norm_mw16 --bound 1 2>&1 | tee -a "$$LOG_FILE"; \
	 echo "$$(date '+%Y-%m-%d %H:%M:%S'): Verification completed" >> "$$LOG_FILE"; \
	 echo "Log saved to: $$LOG_FILE"; \

t_norm_mw27: 
	@# 直接在shell中生成带时间缀的完整日志文件名
	@LOG_FILE="verfication_norm_mw27_$$(date '+%Y%m%d_%H%M%S').log"; \
	 echo "$$(date '+%Y-%m-%d %H:%M:%S'): Running command: $(HW-CBMC)  cmodel/ne_fp_ffp_norm_mw27.c rtl/DW_lsd_w26.v rtl/ne_fp_sfl_blk_w27s5.v rtl/ne_fp_ffp_norm_mw27.v  --module ne_fp_ffp_norm_mw27 --bound 1" > "$$LOG_FILE"; \
	 echo "$$(date '+%Y-%m-%d %H:%M:%S'): Starting verification..." >> "$$LOG_FILE"; \
	 $(HW-CBMC)  cmodel/ne_fp_ffp_norm_mw27.c rtl/DW_lsd_w26.v rtl/ne_fp_sfl_blk_w27s5.v rtl/ne_fp_ffp_norm_mw27.v  --module ne_fp_ffp_norm_mw27 --bound 1 2>&1 | tee -a "$$LOG_FILE"; \
	 echo "$$(date '+%Y-%m-%d %H:%M:%S'): Verification completed" >> "$$LOG_FILE"; \
	 echo "Log saved to: $$LOG_FILE"; \

t_norm_mw33: 
	@# 直接在shell中生成带时间缀的完整日志文件名
	@LOG_FILE="verfication_norm_mw33_$$(date '+%Y%m%d_%H%M%S').log"; \
	 echo "$$(date '+%Y-%m-%d %H:%M:%S'): Running command: $(HW-CBMC)  cmodel/ne_fp_ffp_norm_mw33.c rtl/DW_lsd_w27.v rtl/ne_fp_sfl_blk_w33s5.v rtl/ne_fp_ffp_norm_mw33.v  --module ne_fp_ffp_norm_mw27 --bound 1" > "$$LOG_FILE"; \
	 echo "$$(date '+%Y-%m-%d %H:%M:%S'): Starting verification..." >> "$$LOG_FILE"; \
	 $(HW-CBMC)  cmodel/ne_fp_ffp_norm_mw33.c rtl/DW_lsd_w32.v rtl/ne_fp_sfl_blk_w33s6.v rtl/ne_fp_ffp_norm_mw33.v  --module ne_fp_ffp_norm_mw33 --bound 1 2>&1 | tee -a "$$LOG_FILE"; \
	 echo "$$(date '+%Y-%m-%d %H:%M:%S'): Verification completed" >> "$$LOG_FILE"; \
	 echo "Log saved to: $$LOG_FILE"; \

t_ffp2fp: 
	@# 直接在shell中生成带时间缀的完整日志文件名
	@LOG_FILE="verfication_ffp2fp_$$(date '+%Y%m%d_%H%M%S').log"; \
	 echo "$$(date '+%Y-%m-%d %H:%M:%S'): Running command: $(HW-CBMC) cmodel/ne_fp_ffp2fp_m33.c --module ne_fp_ffp2fp_m33 rtl/ne_fp_ffp2fp_m33.v rtl/DW_lsd_w33.v --bound 1" > "$$LOG_FILE"; \
	 echo "$$(date '+%Y-%m-%d %H:%M:%S'): Starting verification..." >> "$$LOG_FILE"; \
	 $(HW-CBMC) cmodel/ne_fp_ffp2fp_m33.c --module ne_fp_ffp2fp_m33 rtl/ne_fp_ffp2fp_m33.v rtl/DW_lsd_w33.v --bound 1 2>&1 | tee -a "$$LOG_FILE"; \
	 echo "$$(date '+%Y-%m-%d %H:%M:%S'): Verification completed" >> "$$LOG_FILE"; \
	 echo "Log saved to: $$LOG_FILE"; \

# 清理所有日志文件
clean_log:
	@rm -f $(LOG_PREFIX)*$(LOG_SUFFIX)
	@echo "All log files cleaned"

# 列出所有日志文件
list_logs:
	@ls -lt *.log 2>/dev/null || echo "No log files found"

.PHONY: all clean_log list_logs