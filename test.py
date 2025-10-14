import pyarrow.parquet as pq
import json, os, subprocess, shutil
from tqdm import tqdm
from concurrent.futures import ProcessPoolExecutor, as_completed

path1 = "dataset/py2dfy_test.parquet"
path2 = "dataset/comp_test.parquet"

instruction = """Given a Dafny program with function signature, preconditions, postconditions, and code, but with annotations missing. Please return a complete Dafny program with the strongest possible annotation (loop invariants, assert statements, etc.) filled back in. Do not explain or output any text. If you have to explain, put all explanations in comments form. There should only be code body in your output. Please use exactly the same function signature, preconditions, and postconditions. Do not ever modify the given lines. Below is the program:\n"""
system_prompt = """You are an expert in Dafny. You will be given tasks dealing with Dafny programs including precise annotations. You should only return code body in all circumstances. No text is allowed.\n"""

def read_parquet(path):
    table = pq.read_table(path)
    num_rows = table.num_rows
    print("Schema:", table.schema)
    print("\n总行数:", num_rows)
    data = table.to_pydict()
    json_datas = []
    for i in range(num_rows):
        row_dict = {col: data[col][i] for col in data}
        json_datas.append(row_dict)
    return json_datas

def unify_json_comp(json_data):
    unified = []
    for item in json_data:
        row = {
            "instruction": instruction,
            "system": system_prompt,
            "input": item.get("org_input"),
            "output": item.get("gt_output"),
            "name": f"comp_{item.get('self_id')}",
            "id": item.get("self_id"),
        }
        unified.append(row)
    return unified

def unify_json_py2dfy(json_data):
    unified = []
    for item in json_data:
        input = item.get("input")
        if input.startswith("```dafny"):
            input = input[len("```dafny") :]
        if input.endswith("```"):
            input = input[: -len("```")]
        output = item.get("output")
        if output.startswith("```dafny"):
            output = output[len("```dafny") :]
        if output.endswith("```"):
            output = output[: -len("```")]
        row = {
            "instruction": instruction,
            "system": system_prompt,
            "input": input.strip(),
            "output": output.strip(),
            "name": f"py2dfy_{item.get('extra_info').get('index')}",
            "id": item.get('extra_info').get('index'),
        }
        unified.append(row)
    return unified

def verify_one(data, base_path, auto_delete=False):
    name = data["name"]
    tmp_path = os.path.join(base_path, name)
    os.makedirs(tmp_path, exist_ok=True)

    # 写入文件
    with open(os.path.join(tmp_path, "data.json"), "w", encoding="utf-8") as f:
        json.dump(data, f, indent=4, ensure_ascii=False)
    with open(os.path.join(tmp_path, "input.dfy"), "w", encoding="utf-8") as f:
        f.write(data["input"])
    output_path = os.path.join(tmp_path, "output.dfy")
    with open(output_path, "w", encoding="utf-8") as f:
        f.write(data["output"])

    # 调用 Dafny 验证
    try:
        result = subprocess.run(
            ["dafny", "verify", output_path],
            capture_output=True,
            text=True,
            timeout=120
        )
        if result.returncode != 0:
            if auto_delete:
                shutil.rmtree(tmp_path, ignore_errors=True)
            return name, False, result.stderr.strip() or result.stdout.strip(), None
        return name, True, "ok", data
    except Exception as e:
        if auto_delete:
            shutil.rmtree(tmp_path, ignore_errors=True)
        return name, False, str(e), None

def dump_files(name, datas, max_workers=8, auto_delete=False):
    path = f"dataset/{name}_files/"
    os.makedirs(path, exist_ok=True)
    error_files = []
    passed_datas = []

    print(f"🚀 开始处理 {len(datas)} 个样本（并行 {max_workers} 进程）...")
    with ProcessPoolExecutor(max_workers=max_workers) as executor:
        futures = [executor.submit(verify_one, data, path, auto_delete) for data in datas]
        for f in tqdm(as_completed(futures), total=len(futures), desc=f"Verifying {name}"):
            name_, ok, msg, data_passed = f.result()
            if not ok:
                error_files.append(name_)
                print(f"[❌] {name_} failed: {msg[:200]}")
            else:
                passed_datas.append(data_passed)

    # 输出错误文件记录
    print(f"\n共 {len(error_files)} 个文件验证失败。结果已写入 error_files.txt")
    with open(os.path.join(path, "error_files.txt"), "w", encoding="utf-8") as f:
        f.write("\n".join(error_files))

    # 输出验证通过的 JSONL
    jsonl_path = os.path.join(path, f"passed.jsonl")
    with open(jsonl_path, "w", encoding="utf-8") as f:
        for item in passed_datas:
            f.write(json.dumps(item, ensure_ascii=False) + "\n")
    print(f"✅ 验证通过的样本已保存到 {jsonl_path}")
        
py2dfy_tests = unify_json_py2dfy(read_parquet(path1))[:]
comp_tests = unify_json_comp(read_parquet(path2))[:]
dump_files("py2dfy_test", py2dfy_tests, max_workers=96)
dump_files("comp_test", comp_tests, max_workers=96)