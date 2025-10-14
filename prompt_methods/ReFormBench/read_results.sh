model_to_eval=$1
# 检查参数是否提供
if [ -z "$model_to_eval" ]; then
    echo "错误：请提供模型名称作为参数"
    echo "用法: $0 <model_name>"
    exit 1
fi

results_file="../results/results_summary/${model_to_eval}_results.csv"
# 检查文件是否存在
if [ ! -f "$results_file" ]; then
    echo "错误：文件 $results_file 不存在"
    exit 1
fi

# 读取文件并计算成功率
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

