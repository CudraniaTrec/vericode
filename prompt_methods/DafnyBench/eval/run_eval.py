#!/usr/bin/env python3
import os
import csv
import subprocess
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor, as_completed
from tqdm import tqdm

def process_single_file(dafny_file, model_to_eval, dafny_path):
    # print(f"Reconstructing {dafny_file}")
    try:
        filename = dafny_file.name
        cmd = [
            "python", "fill_hints.py",
            "--model", model_to_eval,
            "--test_file", filename,
            "--feedback_turn", "3",
            "--dafny_path", dafny_path
        ]
        result = subprocess.run(cmd, capture_output=True, text=True, timeout=300)
        # if result.returncode != 0:
        #     print(f"Error processing {dafny_file}: {result.stdout}\n {result.stderr}")
        return filename, result.returncode
    except Exception as e:
        print(f"Error processing {dafny_file}: {e}")
        return dafny_file.name, False

def setup_environment(dafnybench_root, dafny_path, openai_api_key, model_to_eval):
    os.environ["DAFNYBENCH_ROOT"] = dafnybench_root
    os.environ["DAFNY_PATH"] = dafny_path
    os.environ["OPENAI_API_KEY"] = openai_api_key
    os.environ["PATH"] = f"{dafnybench_root}:{os.environ.get('PATH', '')}"
    
    results_dir = Path("../results/results_summary")
    reconstructed_dir = Path("../results/reconstructed_files")
    results_dir.mkdir(parents=True, exist_ok=True)
    reconstructed_dir.mkdir(parents=True, exist_ok=True)
    
    results_file = results_dir / f"{model_to_eval}_results.csv"
    if not results_file.exists():
        with open(results_file, 'w', newline='') as f:
            writer = csv.writer(f)
            writer.writerow(["test_ID", "test_file", "success_on_attempt_#"])
    
    outputs_file = reconstructed_dir / f"{model_to_eval}_outputs.json"
    if not outputs_file.exists():
        with open(outputs_file, 'w') as f:
            f.write("{}")

def calculate_success_rate(model_to_eval):
    results_file = Path("../results/results_summary") / f"{model_to_eval}_results.csv"
    with open(results_file, 'r') as f:
        lines = f.readlines()
    total_num_files = len(lines) - 1
    num_failed = sum(1 for line in lines[1:] if "failed" in line)
    num_success = total_num_files - num_failed
    success_rate = (num_success * 100) / total_num_files if total_num_files > 0 else 0
    return {
        "total_files": total_num_files,
        "successful": num_success,
        "failed": num_failed,
        "success_rate": round(success_rate, 2)
    }

def run_dafny_evaluation(
    dafnybench_root="/data4/hzc/llm_related/vericode/prompt_methods/DafnyBench",
    dafny_path="/usr/bin/dafny",
    openai_api_key="sk-hvXP-KDUii4LsnggeSZE7g",
    model_to_eval="aws/claude-4-sonnet-20250514",
    max_workers=8
):
    setup_environment(dafnybench_root, dafny_path, openai_api_key, model_to_eval)
    test_set_dir = Path(dafnybench_root) / "DafnyBench/dataset/hints_removed"
    dafny_files = list(test_set_dir.glob("*.dfy"))
    
    with ThreadPoolExecutor(max_workers=max_workers) as executor:
        futures = [
            executor.submit(process_single_file, dafny_file, model_to_eval, dafny_path)
            for dafny_file in dafny_files
        ]
        for future in tqdm(as_completed(futures), total=len(futures), desc="Processing files"):
            filename, ret_code = future.result()
            tqdm.write(f"Processed {filename} with return code {ret_code}")
    
    stats = calculate_success_rate(model_to_eval)
    print("=" * 40)
    print(f"模型: {model_to_eval}")
    print(f"总文件数: {stats['total_files']}")
    print(f"成功数: {stats['successful']}")
    print(f"失败数: {stats['failed']}")
    print(f"成功率: {stats['success_rate']}%")
    print("=" * 40)
    return stats

if __name__ == "__main__":
    results = run_dafny_evaluation(max_workers=4)