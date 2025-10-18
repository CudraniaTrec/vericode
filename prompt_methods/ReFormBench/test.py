import litellm
import os

# 开启详细日志
litellm.set_verbose = True

def test_custom_api():
    api_key = "sk-hvXP-KDUii4LsnggeSZE7g"
    
    # 尝试不同的 API base 格式
    api_bases = [
        "https://llm.xmcp.ltd/v1",
        "https://llm.xmcp.ltd/",
        "https://llm.xmcp.ltd"
    ]
    
    for api_base in api_bases:
        print(f"\n测试 API base: {api_base}")
        try:
            response = litellm.completion(
                model="openai/yunwu/gpt-4.1-2025-04-14",
                messages=[{"role": "user", "content": "Hello"}],
                api_key=api_key,
                api_base=api_base,
                max_tokens=10
            )
            print("✅ 成功!")
            print(f"Response: {response.choices[0].message.content}")
            break
        except Exception as e:
            print(f"❌ 失败: {e}")

test_custom_api()