/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Stirling
public import Mathlib.Analysis.MeanInequalities

/-!
# Carleman inequality and its optimal constant

Geometric means of the first `n+1` nonnegative sequence entries and Carleman's summability
bound with constant `exp 1`. The optimality statement quantifies over finitely supported
nonnegative sequences. Real powers, finite products and Stirling asymptotics use Mathlib
conventions.
Source: GAPS 11.38.
-/

@[expose] public section

noncomputable section

namespace CKMA

open scoped BigOperators

/-- The geometric mean of the first `n + 1` entries of a sequence indexed from zero. -/
def prefixGeometricMean (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  (∏ k ∈ Finset.range (n + 1), a k) ^ (1 / (n + 1 : ℝ))

/-- **11.38**: Carleman's bound, with summability included in the conclusion. -/
theorem carleman {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a) :
    Summable (prefixGeometricMean a) ∧
      (∑' n, prefixGeometricMean a n) ≤ Real.exp 1 * ∑' n, a n := by
  sorry

/-- The constant `e` in Carleman's inequality is optimal already on finitely supported sequences. -/
theorem carleman_constant_le {C : ℝ}
    (hC : ∀ a : ℕ → ℝ, (∀ n, 0 ≤ a n) → (Function.support a).Finite →
      (∑' n, prefixGeometricMean a n) ≤ C * ∑' n, a n) : Real.exp 1 ≤ C := by
  sorry

end CKMA
