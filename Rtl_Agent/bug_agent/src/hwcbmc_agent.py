# run_hw_cbmc.py
import subprocess
from datetime import datetime
import os
from config import HW_LOG_DIR

def run_hw_cbmc(module_suffix, iter_num):
    """
    调用 HW-CBMC 并根据日志内容判断是否验证通过
    - 如果 make 命令失败（非零退出码） → success=False
    - 如果日志包含 "VERIFICATION FAILED" → success=False
    - 如果日志正常且未包含 "VERIFICATION FAILED" → success=True
    """
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    hw_log_file = os.path.join(HW_LOG_DIR, f"hwcbmc_iter{iter_num}_{timestamp}.log")
    cmd = ["make", module_suffix]

    print(f"[HW-CBMC] Running iteration {iter_num} with suffix: {module_suffix}")

    try:
        # 执行 make 命令并将输出写入日志
        with open(hw_log_file, "w") as f:
            subprocess.run(cmd, stdout=f, stderr=subprocess.STDOUT, check=True, text=True)
    except subprocess.CalledProcessError as e:
        print(f"[HW-CBMC] Make command failed with exit code: {e.returncode}")
        return hw_log_file, False  # 命令失败

    # 读取日志判断是否验证成功
    with open(hw_log_file, "r") as f:
        log_content = f.read()

    if "VERIFICATION FAILED" in log_content:
        print(f"[HW-CBMC] Verification FAILED! Log saved to: {hw_log_file}")
        return hw_log_file, False
    else:
        print(f"[HW-CBMC] Verification PASSED! Log saved to: {hw_log_file}")
        return hw_log_file, True
