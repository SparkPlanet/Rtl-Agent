import os
from utils import get_module_suffix
# 当前文件所在目录
current_dir = os.path.dirname(os.path.abspath(__file__))

# 项目根目录（相对于当前文件）
PROJECT_ROOT = os.path.abspath(os.path.join(current_dir, ".."))  # 假设config.py在 src/ 下
BENCH_ROOT   = os.path.join(PROJECT_ROOT, "ne_pe_benchmark/ne_dot_orig")

CMODEL_DIR = os.path.join(BENCH_ROOT, "cmodel")
RTL_DIR    = os.path.join(BENCH_ROOT, "rtl")

HW_CBMC_EXE  = os.path.join(PROJECT_ROOT, "hw-cbmc/hw-cbmc")
BUG_JSON_DIR = os.path.join(PROJECT_ROOT, "outputs")

TOP_MODULE = "ne_fp_ffp_add_mwi26"
MAX_ITER   = 5

FIXED_DIR = os.path.join(PROJECT_ROOT, "outputs")
os.makedirs(FIXED_DIR, exist_ok=True)

ORGIN_RTL = os.path.join(FIXED_DIR, f"{TOP_MODULE}.v")
FIXED_ORGIN_DIR = FIXED_DIR
OUTPUT_DIR = FIXED_DIR
LLM_LOG_DIR = os.path.join(FIXED_DIR, "llm_logs")
HW_LOG_DIR = os.path.join(FIXED_DIR, "hwcbmc_logs")
os.makedirs(LLM_LOG_DIR, exist_ok=True)
os.makedirs(HW_LOG_DIR, exist_ok=True)

C_FILE = os.path.join(CMODEL_DIR, f"{TOP_MODULE}.c")
RTL_FILE = os.path.join(RTL_DIR, f"{TOP_MODULE}.v")

MODULE_SUFFIX = get_module_suffix(TOP_MODULE)
