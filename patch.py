with open("CKMA/Analysis/Nonlinear/Monotone.lean", "r") as f:
    text = f.read()
text = text.replace("continuous_finset_sum''", "continuous_finset_sum'")
with open("CKMA/Analysis/Nonlinear/Monotone.lean", "w") as f:
    f.write(text)
