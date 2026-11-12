/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.Interpolation.Basic
public import CKMA.Analysis.Interpolation.Bounds.Real
public import CKMA.Analysis.Interpolation.Bounds.Complex

/-!
# Real and complex interpolation bounds

The real bound is the exact K-method estimate, including exponent infinity.
The complex bound is the exact Calderón gauge estimate.
Both are stated at an interior interpolation parameter. Endpoint operator norms may vanish;
their nonnegativity is the operator-norm axiom and is not a separate hypothesis.
Sources: GAPS 26.53 and 26.54.
-/

@[expose] public section

noncomputable section

namespace CKMA

open scoped ENNReal

/-- **26.53**: the exact real interpolation operator bound at the gauge level. -/
theorem realInterpolationGauge_map_le {𝕜 : Type*} [RCLike 𝕜] {C D : BanachCouple 𝕜}
    (T : CoupleMap C D) {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1)
    {q : ℝ≥0∞} (hq : 1 ≤ q) {M₀ M₁ : ℝ}
    (h₀ : ‖T.leftMap‖ ≤ M₀) (h₁ : ‖T.rightMap‖ ≤ M₁) (x : C.ambient)
    (hx : x ∈ C.realInterpolationSet θ q) :
    D.realInterpolationGauge θ q (T.ambientMap x) ≤
      ENNReal.ofReal (M₀ ^ (1 - θ) * M₁ ^ θ) * C.realInterpolationGauge θ q x := by
  have hM₀ : 0 ≤ M₀ := (norm_nonneg _).trans h₀
  have hM₁ : 0 ≤ M₁ := (norm_nonneg _).trans h₁
  refine le_of_endpointFactor_eps hθ hθ1 hM₀ hM₁ ?_ fun ε hε => ?_
  · rw [BanachCouple.realInterpolationSet, Set.mem_ofPred_eq] at hx
    exact hx
  · exact realInterpolationGauge_map_le_of_pos T hq
      (add_pos_of_nonneg_of_pos hM₀ hε) (add_pos_of_nonneg_of_pos hM₁ hε)
      (h₀.trans (le_add_of_nonneg_right hε.le))
      (h₁.trans (le_add_of_nonneg_right hε.le)) x

/-- **26.54**: the complex interpolation operator bound at the gauge level. -/
theorem complexInterpolationGauge_map_le {C D : BanachCouple ℂ}
    (T : CoupleMap C D) {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1)
    {M₀ M₁ : ℝ}
    (h₀ : ‖T.leftMap‖ ≤ M₀) (h₁ : ‖T.rightMap‖ ≤ M₁) (x : C.ambient)
    (hx : x ∈ C.complexInterpolationSet θ) :
    D.complexInterpolationGauge θ (T.ambientMap x) ≤
      ENNReal.ofReal (M₀ ^ (1 - θ) * M₁ ^ θ) * C.complexInterpolationGauge θ x := by
  have hM₀ : 0 ≤ M₀ := (norm_nonneg _).trans h₀
  have hM₁ : 0 ≤ M₁ := (norm_nonneg _).trans h₁
  refine le_of_endpointFactor_eps hθ hθ1 hM₀ hM₁ ?_ fun ε hε => ?_
  · rw [BanachCouple.complexInterpolationSet, Set.mem_ofPred_eq] at hx
    exact hx
  · exact complexInterpolationGauge_map_le_of_pos T hθ hθ1
      (add_pos_of_nonneg_of_pos hM₀ hε) (add_pos_of_nonneg_of_pos hM₁ hε)
      (h₀.trans (le_add_of_nonneg_right hε.le))
      (h₁.trans (le_add_of_nonneg_right hε.le)) x

end CKMA
