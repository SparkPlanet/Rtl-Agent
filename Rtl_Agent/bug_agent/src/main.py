from config import *
from file_utils import backup_rtl
from llm_agent import llm_fix_rtl
from hwcbmc_agent import run_hw_cbmc
from bug_json import generate_initial_bug_json, update_bug_json
import shutil

def main():
    current_rtl = RTL_FILE
    backup_rtl(RTL_FILE, ORGIN_RTL)

    # 第0次迭代：检查原始 RTL
    hw_log_file, success = run_hw_cbmc(MODULE_SUFFIX, 0)
    bug_json_path = None

    if success:
        with open(hw_log_file, "r") as f: hw_output = f.read()
        if "PARSING ERROR" not in hw_output and "CONFLICT" not in hw_output:
            print("[HW-CBMC] Original RTL already verified correct, skipping LLM iterations.")
            print(f"[OUTPUT] Verified RTL at: {current_rtl}")
            return

    bug_json_path = generate_initial_bug_json(MODULE_SUFFIX, 0)

    for i in range(1, MAX_ITER + 1):
        print(f"\n=== Iteration {i} ===")
        fixed_rtl_tmp, llm_log = llm_fix_rtl(C_FILE, current_rtl, bug_json_path, i)
        shutil.copy(fixed_rtl_tmp, current_rtl)
        hw_log, success = run_hw_cbmc(MODULE_SUFFIX, i)
        if not success: continue
        with open(hw_log, "r") as f: hw_output = f.read()
        if "PARSING ERROR" in hw_output or "CONFLICT" in hw_output:
            _,bug_json_path = update_bug_json(hw_log, i)
        else:
            print("[HW-CBMC] Verification passed!")
            print(f"[OUTPUT] RTL at {current_rtl} is now verified correct")
            break
    else:
        print(f"[WARNING] Reached maximum iterations ({MAX_ITER}).")
        print(f"[OUTPUT] Last attempted RTL remains at: {current_rtl}")

if __name__ == "__main__":
    main()
