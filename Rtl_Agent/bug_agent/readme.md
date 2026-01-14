修改config.py里面的TOP_MODULE就可以对相应的文件进行bug修复
依赖在requirements文件夹里面，里面是整个虚拟环境的依赖，可能有的不需要安装，主要是python,openai(调用api用的，这边我用的是qwen,可以改用其他的模型)这些；
api_key封装在环境变量里面，需要自己设置(将密钥设置为DASHSCOPE_API_KEY)即可
以ne_fp_ffp_add_mwi26.v为例，TOP_MODULE = "ne_fp_ffp_add_mwi26"
在ne_pe_benchmark/ne_dot_orig下面运行python ../../src/main.py即可，会在bug_agent/outputs文件夹里面生成修复文件的log其中的(Rtl_Agent/bug_agent/outputs/ne_fp_ffp_add_mwi26.v)是原始bug代码，每次迭代的代码都覆盖原始文件Rtl_Agent/bug_agent/ne_pe_benchmark/ne_dot_orig/rtl/ne_fp_ffp_add_mwi26.v，最后迭代完成后会生成修复后的文件
