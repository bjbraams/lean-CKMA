/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.Interpolation.Basic
public import CKMA.Analysis.Interpolation.Bounds.Real
public import CKMA.Analysis.Interpolation.Bounds.Complex

import Mathlib.Analysis.SpecialFunctions.Pow.Continuity


/-!
# Real and complex interpolation bounds

The real bound is the exact K-method estimate, including exponent infinity.
The complex bound is the exact Calderón gauge estimate.
Both are stated at an interior interpolation parameter. Endpoint operator norms may vanish;
their nonnegativity is the operator-norm axiom and is not a separate hypothesis.
Sources: GAPS 26.53 and 26.54.

## Main results

* `CKMA.realInterpolationGauge_map_le` (**26.53**): the exact real interpolation operator bound at
  the gauge level.
* `CKMA.complexInterpolationGauge_map_le` (**26.54**): the exact complex interpolation operator
  bound at the gauge level.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Filter Topology
open scoped ENNReal

/-- If a bound holds for every `Mᵢ + ε`, it holds for nonnegative `Mᵢ`. -/
private theorem le_of_endpointFactor_eps {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) {M₀ M₁ : ℝ}
    {a G : ℝ≥0∞} (hG : G ≠ ∞)
    (h : ∀ ε : ℝ, 0 < ε →
      a ≤ ENNReal.ofReal ((M₀ + ε) ^ (1 - θ) * (M₁ + ε) ^ θ) * G) :
    a ≤ ENNReal.ofReal (M₀ ^ (1 - θ) * M₁ ^ θ) * G := by
  let εn : ℕ → ℝ := fun n => (↑(n + 1) : ℝ)⁻¹
  have hεpos : ∀ n, 0 < εn n := fun n => inv_pos.mpr (Nat.cast_pos.mpr n.succ_pos)
  have hεlim : Tendsto εn atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have hpow0 : Tendsto (fun n => (M₀ + εn n) ^ (1 - θ)) atTop (𝓝 (M₀ ^ (1 - θ))) := by
    simpa [add_zero] using
      (tendsto_const_nhds.add hεlim).rpow_const (Or.inr (sub_nonneg.mpr hθ1.le))
  have hpow1 : Tendsto (fun n => (M₁ + εn n) ^ θ) atTop (𝓝 (M₁ ^ θ)) := by
    simpa [add_zero] using (tendsto_const_nhds.add hεlim).rpow_const (Or.inr hθ.le)
  have hprod : Tendsto (fun n => (M₀ + εn n) ^ (1 - θ) * (M₁ + εn n) ^ θ) atTop
      (𝓝 (M₀ ^ (1 - θ) * M₁ ^ θ)) := hpow0.mul hpow1
  have hmul : Tendsto (fun n => ENNReal.ofReal ((M₀ + εn n) ^ (1 - θ) * (M₁ + εn n) ^ θ) * G)
      atTop (𝓝 (ENNReal.ofReal (M₀ ^ (1 - θ) * M₁ ^ θ) * G)) :=
    ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal hprod) (Or.inr hG)
  exact le_of_tendsto_of_tendsto' tendsto_const_nhds hmul fun n => h (εn n) (hεpos n)

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
  refine le_of_endpointFactor_eps hθ hθ1 ?_ fun ε hε => ?_
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
  refine le_of_endpointFactor_eps hθ hθ1 ?_ fun ε hε => ?_
  · rw [BanachCouple.complexInterpolationSet, Set.mem_ofPred_eq] at hx
    exact hx
  · exact complexInterpolationGauge_map_le_of_pos T hθ hθ1
      (add_pos_of_nonneg_of_pos hM₀ hε) (add_pos_of_nonneg_of_pos hM₁ hε)
      (h₀.trans (le_add_of_nonneg_right hε.le))
      (h₁.trans (le_add_of_nonneg_right hε.le)) x

end CKMA
