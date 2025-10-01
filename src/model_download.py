from transformers import AutoModelForCausalLM, AutoTokenizer
import torch

model_name = "sft_1.5B"
model_id = f"Veri-Code/{model_name}" 
# Example checkpoint; available include sft_0.5B, sft_1.5B, sft_3B, sft_7B, sft_14B, 14B-RL-entropy

tokenizer = AutoTokenizer.from_pretrained(model_id, trust_remote_code=True)
model = AutoModelForCausalLM.from_pretrained(
    model_id,
    torch_dtype=torch.bfloat16, # Use bfloat16 for optimal performance if supported
    device_map="auto",
    trust_remote_code=True,
)

model.save_pretrained(f"sft_ckpts/{model_name}")
tokenizer.save_pretrained(f"sft_ckpts/{model_name}")

# Example prompt for Dafny code generation
# This prompt asks the model to implement a simple Max method in Dafny.
prompt = "method Max(a: int, b: int) returns (m: int)\
  ensures m == a || m == b\
  ensures m >= a && m >= b\
{\
"

input_ids = tokenizer(prompt, return_tensors="pt").to(model.device)

# Generate Dafny code
generated_ids = model.generate(
    **input_ids,
    max_new_tokens=100,
    temperature=0.7,
    do_sample=True,
    eos_token_id=tokenizer.eos_token_id,
)

generated_text = tokenizer.decode(generated_ids[0], skip_special_tokens=True)
print(generated_text)