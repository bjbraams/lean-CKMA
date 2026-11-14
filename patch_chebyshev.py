import re

with open("CKMA/Analysis/Approximation/Polynomial/Chebyshev.lean", "r") as f:
    text = f.read()

text = text.replace("eval_smul", "Polynomial.eval_smul")

with open("CKMA/Analysis/Approximation/Polynomial/Chebyshev.lean", "w") as f:
    f.write(text)
