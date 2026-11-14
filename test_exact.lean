
import Mathlib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (Tlin : (ℝ → ℝ) →ₗ[ℝ] E) (c d : ℝ → ℝ)

example : dist (Tlin c) (Tlin d) = ‖Tlin (c - d)‖ := by
  rw [map_sub]
  exact dist_eq_norm (Tlin c) (Tlin d)
