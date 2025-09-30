import pyarrow.parquet as pq
import json

path = "dataset2/comp_test.parquet"
pf = pq.ParquetFile(path)

# Schema 和元信息
print("Schema:")
print(pf.schema_arrow)
print("\n总行数:", pf.metadata.num_rows, "行组数:", pf.metadata.num_row_groups)

# 查看每个 Row Group 的行数和大小
for i in range(pf.metadata.num_row_groups):
    rg = pf.metadata.row_group(i)
    print(f"RowGroup {i}: rows={rg.num_rows}, total_byte_size={rg.total_byte_size}")

# 分批读取，避免一次性进内存
for batch in pf.iter_batches(batch_size=100):
    pdf = batch.to_pydict()
    for col, values in pdf.items():
        print(f"{col}: {values[0]}\n")
    break