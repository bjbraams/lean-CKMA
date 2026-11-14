
import Mathlib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (Tlin : (ℝ → ℝ) →ₗ[ℝ] E) (c d : ℝ → ℝ)

example : dist (Tlin c) (Tlin d) = ‖Tlin (c - d)‖ := by
  simp only [dist_eq_norm, map_sub]
