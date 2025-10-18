import argparse, os
import litellm
from litellm import completion
import json
from tqdm import tqdm
from utils import (
    extract_code_from_llm_output,
    run_dafny,
    is_dafny_verified,
    check_no_cheating,
    save_result,
)
from concurrent.futures import ThreadPoolExecutor, as_completed

def load_test_data(file_path):
    """从JSONL文件加载测试数据"""
    test_items = []
    with open(file_path, "r", encoding='utf-8') as file:
        for line in file:
            if line.strip():
                test_items.append(json.loads(line.strip()))
    return test_items

def fill_hints_for_item(model, item, dafny_path, feedback_turn):
    item_name = item.get("name")
    body = item.get("input").strip()
    system_content = item.get("system")
    instruction = item.get("instruction")
    messages = [
        {"role": "system", "content": system_content},
        {"role": "user", "content": instruction + "```dafny\n" + body + "```"}
    ]

    body_with_hints = ""
    counter = 1
    api_key = os.getenv("OPENAI_API_KEY")
    api_base = os.getenv("OPENAI_API_BASE")
    for _ in range(feedback_turn):
        try:
            response = completion(
                model=f"openai/{model}",
                messages=messages,
                api_key=api_key,
                api_base=api_base,
                max_tokens=4096,
            )
            body_with_hints = extract_code_from_llm_output(response.choices[0].message.content)
            # print(f"Item: {item_name}, Attempt: {counter}\n{body_with_hints}\n{'='*40}")
            messages.append({"role": "assistant", "content": body_with_hints})
            
            out, _ = run_dafny(body_with_hints, dafny_path)
            spec_preserved, no_avoid_verify = check_no_cheating(body, body_with_hints)
            if is_dafny_verified(str(out)) and spec_preserved and no_avoid_verify:
                save_result(model, item_name, counter, body_with_hints)
                return {"name": item_name, "success_tries": counter}
            
            feedback_message = ""
            if not is_dafny_verified(str(out)):
                feedback_message += "This answer got Dafny verification error:\n" + str(out) + "\n"
                feedback_message += "Please try again by taking the Dafny feedback.\n"
            if not spec_preserved:
                feedback_message += "Please keep the invariants the same as the original program, or you fail the test.\n"
            if not no_avoid_verify:
                feedback_message += "Please don't use {:verify false} or assume false."
            messages.append({"role": "user", "content": feedback_message})
            counter += 1 
        except Exception:
            continue
    
    save_result(model, item_name, "failed", body_with_hints)
    return {"name": item_name, "success_tries": -1}

def process_all_items(model, test_items, feedback_turn, dafny_path="dafny", max_workers=4):
    results = []
    with ThreadPoolExecutor(max_workers=max_workers) as executor:
        future_to_item = {
            executor.submit(fill_hints_for_item, model, item, dafny_path, feedback_turn): item 
            for item in test_items
        }
        for future in tqdm(as_completed(future_to_item), total=len(future_to_item)):
            try:
                result = future.result()
                results.append(result)
            except Exception:
                item = future_to_item[future]
                results.append({"name": item.get("name"), "success_tries": -1})
    return results

if __name__ == "__main__":
    comp_test_path = "../../dataset/comp_test_files/passed.jsonl"
    py2dfy_test_path = "../../dataset/py2dfy_test_files/passed.jsonl"
    os.environ["OPENAI_API_KEY"] = "sk-hvXP-KDUii4LsnggeSZE7g"
    os.environ["OPENAI_API_BASE"] = "https://llm.xmcp.ltd/"

    parser = argparse.ArgumentParser(description="批量重构Dafny程序的hints")
    parser.add_argument("--model", type=str, default="yunwu/gpt-4.1-2025-04-14")
    parser.add_argument("--test_path", type=str, default=comp_test_path)
    parser.add_argument("--feedback_turn", type=int, default=3)
    
    args = parser.parse_args()
    model_name = args.model
    test_items = load_test_data(args.test_path)
    results = process_all_items(model_name, test_items, args.feedback_turn, max_workers=8)

    total = len(results)
    successful = sum(1 for r in results if r.get("success_tries") >= 0)
    print(f"Total: {total}, Success: {successful}, Failed: {total - successful}")
    print(f"Success Rate: {successful/total*100:.1f}%")