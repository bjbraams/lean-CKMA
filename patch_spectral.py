with open("CKMA/Analysis/Operator/SpectralDynamics.lean", "r") as f:
    text = f.read()

text = text.replace("unfold boundedSpectralEvolution\n        fun_prop) _) 0 T)", "unfold boundedSpectralEvolution\n        fun_prop : Continuous fun s : ℝ => ‖F.starProjection (L (boundedSpectralEvolution A s x))‖ ^ 2) _) 0 T)")

with open("CKMA/Analysis/Operator/SpectralDynamics.lean", "w") as f:
    f.write(text)
