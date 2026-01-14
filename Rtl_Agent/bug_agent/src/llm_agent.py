import json
import os
from datetime import datetime
from openai import OpenAI
from config import OUTPUT_DIR, LLM_LOG_DIR

api_key = os.environ.get("DASHSCOPE_API_KEY")
if not api_key:
    raise ValueError("环境变量 DASHSCOPE_API_KEY 未设置或无效")

client = OpenAI(
    api_key=api_key,
    base_url="https://dashscope.aliyuncs.com/compatible-mode/v1"
)

def llm_fix_rtl(c_file_path, rtl_file_path, bug_json_path, iter_num):
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    fixed_rtl_tmp = os.path.join(OUTPUT_DIR, f"fixed_iter{iter_num}_{timestamp}.v")
    llm_log_file  = os.path.join(LLM_LOG_DIR, f"llm_iter{iter_num}_{timestamp}.log")

    # 读取输入文件
    with open(c_file_path, "r") as f: c_code = f.read()
    with open(rtl_file_path, "r") as f: rtl_code = f.read()
    with open(bug_json_path, "r") as f: bug_info = json.load(f)

    prompt = f"""
你是一个专业的硬件设计和 RTL 修正专家。
请先给出你的推理分析，最后输出完整 RTL 代码（使用 ```verilog 包裹）。
要求：
- 基于原有 RTL 代码，只做最小必要修改
- 保留原有模块和信号结构
- 不输出其他解释

【C model 参考代码】
{c_code}

【原 RTL 代码】
{rtl_code}

【Bug 信息】
{json.dumps(bug_info, indent=2)}
"""
    raw_chunks = []
    with open(llm_log_file, "w", encoding="utf-8") as log_f:
        log_f.write("========== RAW LLM OUTPUT ==========\n")
        response = client.chat.completions.create(
            model="qwen-plus",
            messages=[
                {"role": "system", "content": "你是专业的 RTL 修正 Agent"},
                {"role": "user", "content": prompt}
            ],
            temperature=0,
            stream=True
        )
        for event in response:
            delta = event.choices[0].delta
            if hasattr(delta, "content") and delta.content:
                chunk = delta.content
                raw_chunks.append(chunk)
                log_f.write(chunk)
                log_f.flush()

    raw_content = "".join(raw_chunks)
    start_idx = raw_content.find("```verilog")
    end_idx = raw_content.rfind("```")
    if start_idx != -1 and end_idx != -1 and end_idx > start_idx:
        rtl_only = raw_content[start_idx+len("```verilog"):end_idx].strip()
        reasoning = (raw_content[:start_idx] + raw_content[end_idx+3:]).strip()
    else:
        rtl_only = raw_content
        reasoning = "[WARNING] 无法识别 fenced RTL，全部内容写入 RTL 文件"

    with open(fixed_rtl_tmp, "w", encoding="utf-8") as rtl_f: rtl_f.write(rtl_only)

    with open(llm_log_file, "a", encoding="utf-8") as log_f:
        log_f.write("\n\n========== LLM REASONING ==========\n")
        log_f.write(reasoning + "\n")
        log_f.write("\n========== GENERATED RTL ==========\n")
        log_f.write("```verilog\n")
        log_f.write(rtl_only + "\n")
        log_f.write("```\n")

    print(f"[LLM] Fixed RTL written to: {fixed_rtl_tmp}")
    print(f"[LLM] Log written to: {llm_log_file}")
    return fixed_rtl_tmp, llm_log_file
