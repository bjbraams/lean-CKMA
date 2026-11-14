with open("CKMA/Dynamics/Ergodic/Pointwise/KingmanFull.lean", "r") as f:
    text = f.read()

lemmas = """omit [MeasurableSpace Ω] in
/-- On `EReal`, the linear maximum agrees with the lattice supremum. -/
lemma ereal_max_eq_sup (a b : EReal) : max a b = a ⊔ b := by
  rcases le_total a b with hab | hba
  · calc
      max a b = b := max_eq_right hab
      _ = a ⊔ b := (sup_of_le_right hab).symm
  · calc
      max a b = a := max_eq_left hba
      _ = a ⊔ b := (sup_of_le_left hba).symm

omit [MeasurableSpace Ω] in
/-- The coercion into `EReal` preserves binary maxima. -/
lemma ereal_coe_max (a b : ℝ) :
    ((max a b : ℝ) : EReal) = max (a : EReal) (b : EReal) := by
  rcases le_total a b with hab | hba
  · rw [max_eq_right hab, max_eq_right (EReal.coe_le_coe_iff.mpr hab)]
  · rw [max_eq_left hba, max_eq_left (EReal.coe_le_coe_iff.mpr hba)]

"""

text = text.replace("def kingmanFekete", lemmas + "def kingmanFekete")
text = text.replace("EReal.coe_max", "ereal_coe_max")
text = text.replace("max_eq_sup", "ereal_max_eq_sup")

with open("CKMA/Dynamics/Ergodic/Pointwise/KingmanFull.lean", "w") as f:
    f.write(text)
