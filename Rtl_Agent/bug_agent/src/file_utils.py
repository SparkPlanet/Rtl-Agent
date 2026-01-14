import os
import shutil

def find_module_file(root_dir, module_name, suffix):
    matches = []
    target = f"{module_name}.{suffix}"
    for root, _, files in os.walk(root_dir):
        if target in files:
            matches.append(os.path.join(root, target))
    if not matches:
        raise FileNotFoundError(f"未在 {root_dir} 下找到 {target}")
    if len(matches) > 1:
        raise RuntimeError(f"在 {root_dir} 下找到多个 {target}：\n" + "\n".join(matches))
    return matches[0]

def backup_rtl(src_rtl_path, dst_rtl_path):
    if not os.path.exists(dst_rtl_path):
        shutil.copy(src_rtl_path, dst_rtl_path)
        print(f"[BASELINE] Saved original RTL to {dst_rtl_path}")
    else:
        print(f"[BASELINE] Original RTL already exists, skip copy")
