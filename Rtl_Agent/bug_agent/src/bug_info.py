import os
import json
from openai import OpenAI

# ===== 配置 =====
current_dir = os.path.dirname(os.path.abspath(__file__))  

# 模块目录（绝对路径）
MODULE_DIR = os.path.abspath(os.path.join(current_dir, "../../ne_pe_benchmark/ne_dot_orig"))

# 输出目录（绝对路径）
OUTPUT_DIR = os.path.abspath(os.path.join(current_dir, "../outputs"))


# HW-CBMC 日志后缀
HW_LOG_EXT = ".log"

# ===== 初始化 DashScope Qwen 客户端 =====
api_key = os.environ.get("DASHSCOPE_API_KEY")
if not api_key:
    raise ValueError("环境变量 DASHSCOPE_API_KEY 未设置或无效")

client = OpenAI(
    api_key=api_key,
    base_url="https://dashscope.aliyuncs.com/compatible-mode/v1"
)

# ===== 创建输出文件夹 =====
os.makedirs(OUTPUT_DIR, exist_ok=True)

# ===== 获取最新 log =====
def get_latest_log(module_dir):
    logs = [f for f in os.listdir(module_dir) if f.endswith(HW_LOG_EXT)]
    if not logs:
        return None
    logs.sort()
    return os.path.join(module_dir, logs[-1])

# ===== 构建 prompt =====
def build_prompt(log_text):
    return f"""
你是一个 HW-CBMC log 分析助手。
请从下面的 log 中提取结构化信息，包括：
1. 触发 bug 的输入值（din_a, din_b, din_mode）
2. C model 输出（c_res）
3. RTL 输出（z, z_is_zero, z_is_inf, z_is_nan）
4. 可能的语义冲突（C model 与 RTL 不一致）

只返回 JSON 格式：
{{
  "inputs": {{}},
  "c_output": {{}},
  "rtl_output": {{}},
  "conflict": "..."
}}

Log:
{log_text}
"""

# ===== 使用 DashScope Qwen 提取信息 =====
def extract_structured_info(log_path):
    """从 log 文件路径提取结构化信息"""
    with open(log_path, "r") as f:
        log_text = f.read()

    prompt = build_prompt(log_text)

    response = client.chat.completions.create(
        model="qwen-plus",
        messages=[
            {"role": "system", "content": "你是一个专业的 HW-CBMC log 分析 Agent"},
            {"role": "user", "content": prompt}
        ],
        temperature=0
    )

    result_text = response.choices[0].message.content.strip()

    try:
        return json.loads(result_text)
    except json.JSONDecodeError:
        # 简单修复常见 JSON 问题
        try:
            result_text_fixed = result_text.replace("\n", "").replace("'", '"')
            return json.loads(result_text_fixed)
        except Exception:
            return {"raw_llm_output": result_text}

