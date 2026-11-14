import os
import re

mathlib_dir = '/export/scratch1/braams/lean-codes-lake/packages/mathlib/Mathlib'
pattern = re.compile(r'(?:theorem|lemma)\s+(continuous\w*)\s*.*?:.*Continuous\s*\(?fun.*?∑', re.DOTALL)

for root, _, files in os.walk(mathlib_dir):
    for file in files:
        if file.endswith('.lean'):
            path = os.path.join(root, file)
            with open(path, 'r') as f:
                content = f.read()
                matches = pattern.findall(content)
                if matches:
                    print(f"{path}: {matches}")
