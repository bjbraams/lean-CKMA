/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.lpSpace

/-!
# The squared norm on `ℓ²`

For `f : lp G 2` the squared norm is the sum of the squared coordinate norms, and that sum is
summable. These are the `p = 2` cases of `lp.norm_rpow_eq_tsum` and `lp.memℓp`, written with
natural-number powers.

## Main results

* `CKMA.lp.norm_sq_eq_tsum`: `‖f‖ ^ 2 = ∑' i, ‖f i‖ ^ 2`.
* `CKMA.lp.summable_norm_sq`: `Summable fun i => ‖f i‖ ^ 2`.
-/

public section

namespace CKMA

namespace lp

variable {ι : Type*} {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)]

/-- The squared `ℓ²` norm is the sum of the squared coordinate norms. -/
theorem norm_sq_eq_tsum (f : _root_.lp G 2) : ‖f‖ ^ 2 = ∑' i, ‖(f : ∀ i, G i) i‖ ^ 2 := by
  simpa [Real.rpow_natCast] using
    _root_.lp.norm_rpow_eq_tsum (p := 2) (by norm_num : 0 < (2 : ENNReal).toReal) f

/-- The squared coordinate norms of an `ℓ²` element are summable. -/
theorem summable_norm_sq (f : _root_.lp G 2) : Summable fun i => ‖(f : ∀ i, G i) i‖ ^ 2 := by
  simpa [Real.rpow_natCast] using
    (_root_.lp.memℓp f).summable (by norm_num : 0 < (2 : ENNReal).toReal)

end lp

end CKMA
