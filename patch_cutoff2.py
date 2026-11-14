with open("CKMA/Analysis/Fourier/Inequalities/Cutoff.lean", "r") as f:
    text = f.read()

text = text.replace(":= rfl", ":= by ext x; rfl")

with open("CKMA/Analysis/Fourier/Inequalities/Cutoff.lean", "w") as f:
    f.write(text)
