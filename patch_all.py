import re

# 1. Projection.lean
with open("CKMA/Analysis/OrderedSpace/Bands/Projection.lean", "r") as f:
    text = f.read()
text = text.replace("public import Mathlib.Algebra.Order.Hom.Monoid", "public import Mathlib.Algebra.Order.Hom.Monoid\npublic import Mathlib.LinearAlgebra.Basic")
with open("CKMA/Analysis/OrderedSpace/Bands/Projection.lean", "w") as f:
    f.write(text)

# 2. Recurrence.lean
with open("CKMA/Dynamics/Ergodic/Recurrence.lean", "r") as f:
    text = f.read()
orig = """omit [StandardBorelSpace Ω] [IsProbabilityMeasure μ] in
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
new = """omit [StandardBorelSpace Ω] [IsProbabilityMeasure μ] in
/-- Inverse iterates undo forward iterates. -/
private lemma symm_iterate_apply (i : ℕ) (x : Ω) : (T.symm^[i]) ((T^[i]) x) = x := by
  induction i generalizing x with
  | zero => rfl
  | succ i ih => simp [Function.iterate_succ, T.left_inv, ih]

omit [StandardBorelSpace Ω] [IsProbabilityMeasure μ] in
/-- Forward iterates undo inverse iterates. -/
private lemma iterate_symm_apply (i : ℕ) (x : Ω) : (T^[i]) ((T.symm^[i]) x) = x := by
  induction i generalizing x with
  | zero => rfl
  | succ i ih => simp [Function.iterate_succ, T.right_inv, ih]"""
text = text.replace(orig, new)
with open("CKMA/Dynamics/Ergodic/Recurrence.lean", "w") as f:
    f.write(text)

# 3. Monotone.lean
with open("CKMA/Analysis/Nonlinear/Monotone.lean", "r") as f:
    text = f.read()
orig_lemma = """private lemma continuous_finset_sum' {ι : Type*} {s : Finset ι} {f : ι → ℝ → ℂ}
    (hf : ∀ i ∈ s, Continuous (f i)) : Continuous (fun t ↦ ∑ i ∈ s, f i t) := by
  classical
  induction s using Finset.induction with
  | empty =>
    simpa using continuous_const
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add (ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))"""
new_lemma = """private lemma continuous_finset_sum' {α β ι : Type*} [TopologicalSpace α] [AddCommMonoid β] [TopologicalSpace β] [ContinuousAdd β] {s : Finset ι} {f : ι → α → β}
    (hf : ∀ i ∈ s, Continuous (f i)) : Continuous (fun t ↦ ∑ i ∈ s, f i t) := by
  classical
  induction s using Finset.induction with
  | empty =>
    simpa using continuous_const
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add (ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))"""
text = text.replace(orig_lemma, new_lemma)
with open("CKMA/Analysis/Nonlinear/Monotone.lean", "w") as f:
    f.write(text)

# 4. Cutoff.lean
with open("CKMA/Analysis/Fourier/Inequalities/Cutoff.lean", "r") as f:
    text = f.read()
text = text.replace("ext x; rfl", "funext x; rfl")
with open("CKMA/Analysis/Fourier/Inequalities/Cutoff.lean", "w") as f:
    f.write(text)

# 5. SpectralDynamics.lean
with open("CKMA/Analysis/Operator/SpectralDynamics.lean", "r") as f:
    text = f.read()
orig_sd = """  rw [intervalIntegral.integral_add
      ((IntervalIntegrable.const_mul (by
        refine Continuous.intervalIntegrable ?_ 0 T
        let +nondep : NormedAlgebra ℚ (H →L[ℂ] H) := .restrictScalars ℚ ℂ _
        unfold boundedSpectralEvolution
        fun_prop : Continuous fun s : ℝ => ‖F.starProjection (L (boundedSpectralEvolution A s x))‖ ^ 2) _) 0 T)"""
new_sd = """  rw [intervalIntegral.integral_add
      ((IntervalIntegrable.const_mul (by
        refine Continuous.intervalIntegrable (f := fun s : ℝ => ‖F.starProjection (L (boundedSpectralEvolution A s x))‖ ^ 2) ?_ 0 T
        let +nondep : NormedAlgebra ℚ (H →L[ℂ] H) := .restrictScalars ℚ ℂ _
        unfold boundedSpectralEvolution
        fun_prop) _) 0 T)"""
text = text.replace(orig_sd, new_sd)
with open("CKMA/Analysis/Operator/SpectralDynamics.lean", "w") as f:
    f.write(text)

# 6. Norming.lean
with open("CKMA/Analysis/FunctionalAnalysis/WeakCompactness/Norming.lean", "r") as f:
    text = f.read()
text = text.replace("rw [← LinearMap.map_sub]", "have H : Tlin c - Tlin d = Tlin (c - d) := (map_sub Tlin c d).symm\n      rw [H]")
text = text.replace("rw [LinearMap.map_sub, hcd, sub_self]", "have H : Tlin (c - d) = Tlin c - Tlin d := map_sub Tlin c d\n    rw [H, hcd, sub_self]")
with open("CKMA/Analysis/FunctionalAnalysis/WeakCompactness/Norming.lean", "w") as f:
    f.write(text)

