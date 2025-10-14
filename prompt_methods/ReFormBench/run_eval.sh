#!/bin/bash

export DAFNYBENCH_ROOT="/home/hzc/data4/llm_related/vericode/prompt_methods/DafnyBench"
export DAFNY_PATH="/usr/bin/dafny"
export OPENAI_API_KEY="sk-r2cq5f6w3LDHYw2VqAp5ZA"
export PATH=$DAFNYBENCH_ROOT:$PATH
export TEST_SET_DIR=$DAFNYBENCH_ROOT/DafnyBench/dataset/hints_removed
export model_to_eval='yunwu/gpt-4.1-2025-04-14'

sleep 0.1

# source $DAFNYBENCH_ROOT/stats/bin/activate

mkdir -p ../results/results_summary
if [ ! -f "../results/results_summary/${model_to_eval}_results.csv" ]; then
    echo "test_ID,test_file,success_on_attempt_#" > "../results/results_summary/${model_to_eval}_results.csv"
fi

mkdir -p ../results/reconstructed_files
outputs_file="../results/reconstructed_files/${model_to_eval}_outputs.json"
if [ ! -f "$outputs_file" ]; then
    echo "{}" > "$outputs_file"
fi

# Evaluation
for DAFNY_FILE in "$TEST_SET_DIR"/*.dfy
do
    echo "Reconstructing $DAFNY_FILE"
    if [ -f "$DAFNY_FILE" ]; then
        FILENAME=$(basename "$DAFNY_FILE")
        python fill_hints.py \
            --model "$model_to_eval" \
            --test_file "$FILENAME" \
            --feedback_turn 3 \
            --dafny_path "$DAFNY_PATH"  # Example Dafny executable path: "/opt/homebrew/bin/Dafny"
    fi
done

# Calculate success rate
results_file="../results/results_summary/${model_to_eval}_results.csv"
mapfile -t lines < "$results_file"
total_num_files=$((${#lines[@]} - 1))
num_failed=0

for ((i=1; i<=total_num_files; i++)); do
    if [[ ${lines[i]} == *"failed"* ]]; then
        ((num_failed++))
    fi
done

success_rate=$(echo "scale=2; (($total_num_files - $num_failed) * 100) / $total_num_files" | bc)
echo "=========================================="
echo "模型: $model_to_eval"
echo "总文件数: $total_num_files"
echo "成功数: $((total_num_files - num_failed))"
echo "失败数: $num_failed"
echo "成功率: ${success_rate}%"
echo "=========================================="
