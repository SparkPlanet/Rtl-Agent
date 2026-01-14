# utils.py
def get_module_suffix(top_module: str) -> str:
    """
    根据 TOP_MODULE 返回 Makefile 对应的目标 MODULE_SUFFIX
    规则：
    - ne_fp_ffp_add_mwi26 -> t_add_mwi26
    - ne_fp_ffp_add_mwi27 -> t_add_mwi27
    - ne_fp_ffp_add_mix -> t_add_mix
    - ne_fp_ffp_add_vector_m33 -> t_add_vector
    - ne_fp_ffp_e_align -> t_e_align
    - ne_fp_ffp_mul -> t_mul
    - ne_fp_ffp_norm_mw16 -> t_norm_mw16
    - ne_fp_ffp_norm_mw27 -> t_norm_mw27
    - ne_fp_ffp_norm_mw33 -> t_norm_mw33
    - ne_fp_ffp2fp_m33 -> t_ffp2fp
    """
    mapping = {
        "ne_fp_ffp_add_mwi26": "t_add_mwi26",
        "ne_fp_ffp_add_mwi27": "t_add_mwi27",
        "ne_fp_ffp_add_mix": "t_add_mix",
        "ne_fp_ffp_add_vector_m33": "t_add_vector",
        "ne_fp_ffp_e_align": "t_e_align",
        "ne_fp_ffp_mul": "t_mul",
        "ne_fp_ffp_norm_mw16": "t_norm_mw16",
        "ne_fp_ffp_norm_mw27": "t_norm_mw27",
        "ne_fp_ffp_norm_mw33": "t_norm_mw33",
        "ne_fp_ffp2fp_m33": "t_ffp2fp",
        "ne_dot": "t_ne_dot",  # 可选，如果需要 ne_dot
    }
    
    if top_module not in mapping:
        raise ValueError(f"No Makefile target found for TOP_MODULE: {top_module}")
    
    return mapping[top_module]
