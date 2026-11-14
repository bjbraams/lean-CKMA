with open("CKMA/Dynamics/Ergodic/Pointwise/KingmanFull.lean", "r") as f:
    text = f.read()

text = text.replace("/-- The Fekete infimum of the normalized positive-length integrals. -/\nomit [MeasurableSpace Ω] in\n/-- On `EReal`, the linear maximum agrees with the lattice supremum. -/", "omit [MeasurableSpace Ω] in\n/-- On `EReal`, the linear maximum agrees with the lattice supremum. -/")
text = text.replace("def kingmanFekete", "/-- The Fekete infimum of the normalized positive-length integrals. -/\ndef kingmanFekete")

with open("CKMA/Dynamics/Ergodic/Pointwise/KingmanFull.lean", "w") as f:
    f.write(text)
