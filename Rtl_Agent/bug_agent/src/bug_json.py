# bug_json.py
import os
import shutil
from datetime import datetime
from bug_info import extract_structured_info
from hwcbmc_agent import run_hw_cbmc
from config import BUG_JSON_DIR

def update_bug_json(hwcbmc_log_path, iter_num, output_dir=BUG_JSON_DIR):
    if not os.path.exists(hwcbmc_log_path):
        raise FileNotFoundError(f"{hwcbmc_log_path} 不存在")
    
    bug_json = extract_structured_info(hwcbmc_log_path)
    
    os.makedirs(output_dir, exist_ok=True)
    
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    output_path = os.path.join(output_dir, f"bug_{timestamp}.json")
    
    with open(output_path, "w", encoding="utf-8") as f:
        import json
        json.dump(bug_json, f, ensure_ascii=False, indent=2)
    
    # 更新 latest.json
    latest_path = os.path.join(output_dir, "latest.json")
    shutil.copy(output_path, latest_path)
    
    print(f"[INFO] 已生成新的 BUG JSON 文件：{output_path}")
    print(f"[INFO] Latest bug JSON updated: {latest_path}")
    
    return bug_json, output_path


def generate_initial_bug_json(module_suffix, iter_num=0):
    """
    如果没有 latest.json，调用 HW-CBMC 生成初始 log，并生成初始 bug JSON
    不会因 VERIFICATION FAILED 直接退出
    """
    print("[INFO] Generating initial HW-CBMC log and bug JSON...")

    hw_log_file, success = run_hw_cbmc(module_suffix, iter_num)

    if not success:
        print(f"[WARNING] Original RTL has issues (VERIFICATION FAILED). Generating bug JSON...")

    # 生成 bug JSON，无论验证是否成功都生成
    bug_json, bug_json_path = update_bug_json(hw_log_file, iter_num)

    return os.path.join(BUG_JSON_DIR, "latest.json")
