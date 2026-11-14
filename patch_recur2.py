with open("CKMA/Dynamics/Ergodic/Recurrence.lean", "r") as f:
    text = f.read()

orig = """omit [StandardBorelSpace Ω] [IsProbabilityMeasure μ] in
/-- Inverse iterates undo forward iterates. -/
private lemma symm_iterate_apply (i : ℕ) (x : Ω) : (T.symm^[i]) ((T^[i]) x) = x := by
  induction i generalizing x with
  | zero => rfl
  | succ i ih =>
    change (T.symm^[i]) (T.symm (T ((T^[i]) x))) = x
    rw [T.left_inv]
    exact ih x

omit [StandardBorelSpace Ω] [IsProbabilityMeasure μ] in
/-- Forward iterates undo inverse iterates. -/
private lemma iterate_symm_apply (i : ℕ) (x : Ω) : (T^[i]) ((T.symm^[i]) x) = x := by
  induction i generalizing x with
  | zero => rfl
  | succ i ih =>
    change (T^[i]) (T (T.symm ((T.symm^[i]) x))) = x
    rw [T.right_inv]
    exact ih x"""

new = """omit [StandardBorelSpace Ω] [IsProbabilityMeasure μ] in
/-- Inverse iterates undo forward iterates. -/
private lemma symm_iterate_apply (i : ℕ) (x : Ω) : (T.symm^[i]) ((T^[i]) x) = x := by
  induction i generalizing x with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', T.left_inv, ih]

omit [StandardBorelSpace Ω] [IsProbabilityMeasure μ] in
/-- Forward iterates undo inverse iterates. -/
private lemma iterate_symm_apply (i : ℕ) (x : Ω) : (T^[i]) ((T.symm^[i]) x) = x := by
  induction i generalizing x with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', T.right_inv, ih]"""

text = text.replace(orig, new)

with open("CKMA/Dynamics/Ergodic/Recurrence.lean", "w") as f:
    f.write(text)
