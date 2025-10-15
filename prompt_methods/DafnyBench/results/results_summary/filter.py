import pandas as pd
import sys

def standardize_csv_file(target_file, reference_file="codellama-7b_results.csv"):
    """
    基于参考文件标准化目标CSV文件：
    1. 删除重复的test_ID
    2. 添加缺失的行（success_on_attempt_#设为failed）
    3. 按test_ID排序
    """
    
    # 读取参考文件和目标文件
    ref_df = pd.read_csv(reference_file)
    target_df = pd.read_csv(target_file)
    
    print(f"参考文件: {len(ref_df)} 行")
    print(f"目标文件原始数据: {len(target_df)} 行")
    
    # 删除目标文件中的重复test_ID
    target_df_cleaned = target_df.drop_duplicates(subset=['test_ID'], keep='first')
    duplicates_removed = len(target_df) - len(target_df_cleaned)
    if duplicates_removed > 0:
        print(f"删除了 {duplicates_removed} 个重复项")
    
    # 获取参考文件中的所有test_ID和test_file
    ref_ids = set(ref_df['test_ID'].astype(str))
    target_ids = set(target_df_cleaned['test_ID'].astype(str))
    
    # 找出缺失的test_ID
    missing_ids = ref_ids - target_ids
    
    if missing_ids:
        print(f"发现 {len(missing_ids)} 个缺失的test_ID")
        # 创建缺失行的数据
        missing_rows = []
        for test_id in missing_ids:
            ref_row = ref_df[ref_df['test_ID'].astype(str) == test_id].iloc[0]
            missing_rows.append({
                'test_ID': ref_row['test_ID'],
                'test_file': ref_row['test_file'],
                'success_on_attempt_#': 'failed'
            })
        # 添加缺失的行
        missing_df = pd.DataFrame(missing_rows)
        target_df_final = pd.concat([target_df_cleaned, missing_df], ignore_index=True)
    else:
        target_df_final = target_df_cleaned
        print("没有缺失的test_ID")
    
    # 按test_ID排序
    target_df_final['test_ID'] = target_df_final['test_ID'].astype(str)
    target_df_final = target_df_final.sort_values('test_ID')
    
    # 格式化test_ID为三位数字（如果是数字的话）
    try:
        target_df_final['test_ID'] = target_df_final['test_ID'].apply(lambda x: f"{int(x):03d}")
    except:
        pass  # 如果不是数字格式就保持原样
    
    # 保存结果
    target_df_final.to_csv(target_file, index=False)
    print(f"最终数据: {len(target_df_final)} 行")
    print(f"已保存到: {target_file}")

if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("用法: python standardize_csv.py <target_csv_file> [reference_csv_file]")
        print("默认参考文件: codellama-7b_results.csv")
        sys.exit(1)
    
    target_file = sys.argv[1]
    reference_file = sys.argv[2] if len(sys.argv) > 2 else "codellama-7b_results.csv"
    standardize_csv_file(target_file, reference_file)