/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.Interpolation.Basic

import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Order.Compact

/-!
# Complex interpolation operator bound

For positive endpoint bounds `M₀` and `M₁`, the entire weight
`exp ((z - θ) * (log M₀ - log M₁))` has modulus `M₀ ^ (z.re - θ) * M₁ ^ (θ - z.re)`.
Multiplying an admissible strip function by this weight and by the ambient operator produces an
admissible strip function for the target couple, whose boundary norm is at most
`M₀ ^ (1 - θ) * M₁ ^ θ` times the source boundary norm. The complex interpolation gauge is the
infimum of those boundary norms.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Filter Metric Set Topology
open scoped ENNReal

variable {C D : BanachCouple ℂ}

/-- Entire scalar weight `exp ((z - θ) * (log M₀ - log M₁))`. -/
def stripWeight (M₀ M₁ θ : ℝ) (z : ℂ) : ℂ :=
  Complex.exp ((z - ↑θ) * ↑(Real.log M₀ - Real.log M₁))

/-- The weight equals `1` at the interpolation parameter. -/
lemma stripWeight_self (M₀ M₁ θ : ℝ) : stripWeight M₀ M₁ θ θ = 1 := by
  unfold stripWeight
  rw [sub_self, zero_mul, Complex.exp_zero]

/-- Modulus of the weight, for positive bases. -/
lemma stripWeight_norm {M₀ M₁ θ : ℝ} (hM₀ : 0 < M₀) (hM₁ : 0 < M₁) (z : ℂ) :
    ‖stripWeight M₀ M₁ θ z‖ = M₀ ^ (z.re - θ) * M₁ ^ (θ - z.re) := by
  have hre : ((z - ↑θ) * ↑(Real.log M₀ - Real.log M₁)).re =
      (z.re - θ) * (Real.log M₀ - Real.log M₁) := by
    rw [Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im, Complex.ofReal_re]
    ring
  have hsplit : (z.re - θ) * (Real.log M₀ - Real.log M₁) =
      Real.log M₀ * (z.re - θ) + Real.log M₁ * (θ - z.re) := by ring
  rw [stripWeight, Complex.norm_exp, hre, hsplit, Real.exp_add, ← Real.rpow_def_of_pos hM₀,
    ← Real.rpow_def_of_pos hM₁]

/-- The weight is entire. -/
lemma stripWeight_differentiable (M₀ M₁ θ : ℝ) : Differentiable ℂ (stripWeight M₀ M₁ θ) := by
  unfold stripWeight
  refine (Complex.differentiable_exp (𝕜 := ℂ)).fun_comp ?_
  exact ((differentiable_id : Differentiable ℂ (id : ℂ → ℂ)).sub_const (θ : ℂ)).mul_const
    (↑(Real.log M₀ - Real.log M₁) : ℂ)

/-- The weight is continuous. -/
lemma stripWeight_continuous (M₀ M₁ θ : ℝ) : Continuous (stripWeight M₀ M₁ θ) :=
  (stripWeight_differentiable M₀ M₁ θ).continuous

/-- On the closed strip the weight is bounded by `exp |log M₀ - log M₁|` when `θ ∈ [0, 1]`. -/
lemma stripWeight_norm_le {M₀ M₁ θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) {z : ℂ} (hz0 : 0 ≤ z.re)
    (hz1 : z.re ≤ 1) :
    ‖stripWeight M₀ M₁ θ z‖ ≤ Real.exp |Real.log M₀ - Real.log M₁| := by
  have hre : (z - ↑θ).re = z.re - θ := by rw [Complex.sub_re, Complex.ofReal_re]
  have habs : |(z - ↑θ).re| ≤ 1 := by
    rw [hre, abs_le]
    constructor <;> linarith
  have hmul : ((z - ↑θ) * ↑(Real.log M₀ - Real.log M₁)).re ≤
      |Real.log M₀ - Real.log M₁| := by
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    calc
      (z - ↑θ).re * (Real.log M₀ - Real.log M₁)
          ≤ |(z - ↑θ).re * (Real.log M₀ - Real.log M₁)| := le_abs_self _
      _ = |(z - ↑θ).re| * |Real.log M₀ - Real.log M₁| := abs_mul _ _
      _ ≤ 1 * |Real.log M₀ - Real.log M₁| :=
          mul_le_mul_of_nonneg_right habs (abs_nonneg _)
      _ = |Real.log M₀ - Real.log M₁| := one_mul _
  rw [stripWeight, Complex.norm_exp]
  exact Real.exp_le_exp.mpr hmul

/-- Real part of a purely imaginary point. -/
lemma re_ofReal_mul_I (t : ℝ) : ((t : ℂ) * Complex.I).re = 0 := by
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

/-- Real part of a point on the right-hand edge of the strip. -/
lemma re_one_add_ofReal_mul_I (t : ℝ) : (1 + (t : ℂ) * Complex.I).re = 1 := by
  rw [Complex.add_re, Complex.one_re, re_ofReal_mul_I]
  ring

/-- On the left edge, the weight modulus times `M₀` is the interpolation factor. -/
lemma stripWeight_norm_left_mul {M₀ M₁ θ : ℝ} (hM₀ : 0 < M₀) (hM₁ : 0 < M₁) (t : ℝ) :
    ‖stripWeight M₀ M₁ θ ((t : ℂ) * Complex.I)‖ * M₀ = M₀ ^ (1 - θ) * M₁ ^ θ := by
  rw [stripWeight_norm hM₀ hM₁, re_ofReal_mul_I, zero_sub, sub_zero]
  have hpow : M₀ ^ (-θ) * M₀ = M₀ ^ (1 - θ) := by
    conv_lhs => arg 2; rw [← Real.rpow_one M₀]
    rw [← Real.rpow_add hM₀]
    congr 1
    ring
  calc
    M₀ ^ (-θ) * M₁ ^ θ * M₀ = M₀ ^ (-θ) * M₀ * M₁ ^ θ := by ring
    _ = M₀ ^ (1 - θ) * M₁ ^ θ := by rw [hpow]

/-- On the right edge, the weight modulus times `M₁` is the interpolation factor. -/
lemma stripWeight_norm_right_mul {M₀ M₁ θ : ℝ} (hM₀ : 0 < M₀) (hM₁ : 0 < M₁) (t : ℝ) :
    ‖stripWeight M₀ M₁ θ (1 + (t : ℂ) * Complex.I)‖ * M₁ = M₀ ^ (1 - θ) * M₁ ^ θ := by
  rw [stripWeight_norm hM₀ hM₁, re_one_add_ofReal_mul_I]
  have hpow : M₁ ^ (θ - 1) * M₁ = M₁ ^ θ := by
    conv_lhs => arg 2; rw [← Real.rpow_one M₁]
    rw [← Real.rpow_add hM₁]
    congr 1
    ring
  calc
    M₀ ^ (1 - θ) * M₁ ^ (θ - 1) * M₁ = M₀ ^ (1 - θ) * (M₁ ^ (θ - 1) * M₁) := by rw [mul_assoc]
    _ = M₀ ^ (1 - θ) * M₁ ^ θ := by rw [hpow]

/-- Equal real parts give the same weight modulus. -/
lemma stripWeight_norm_eq_of_re_eq {M₀ M₁ θ : ℝ} {z w : ℂ} (h : z.re = w.re) :
    ‖stripWeight M₀ M₁ θ z‖ = ‖stripWeight M₀ M₁ θ w‖ := by
  rw [stripWeight, stripWeight, Complex.norm_exp, Complex.norm_exp]
  congr 1
  rw [Complex.mul_re, Complex.mul_re, Complex.sub_re, Complex.sub_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.ofReal_re, h]
  ring

/-- A continuous scalar function vanishing at infinity has bounded norm. -/
private lemma bddAbove_norm_cocompact {E : Type*} [NormedAddCommGroup E] {f : C(ℝ, E)}
    (hf : Tendsto f (cocompact ℝ) (𝓝 0)) :
    BddAbove (range fun t : ℝ => ‖f t‖) := by
  obtain ⟨K, hK, hKc⟩ :=
    Filter.mem_cocompact.mp (hf (closedBall_mem_nhds (0 : E) zero_lt_one))
  have hbdd : BddAbove ((fun t : ℝ => ‖f t‖) '' K) :=
    hK.bddAbove_image ((continuous_norm.comp f.continuous).continuousOn)
  refine ⟨max (sSup ((fun t : ℝ => ‖f t‖) '' K)) 1, ?_⟩
  rintro y ⟨t, rfl⟩
  by_cases ht : t ∈ K
  · exact (le_csSup hbdd ⟨t, ht, rfl⟩).trans (le_max_left _ _)
  · have hball : f t ∈ closedBall (0 : E) 1 := hKc ht
    have hle : ‖f t‖ ≤ 1 := by simpa [mem_closedBall, dist_zero_right] using hball
    exact hle.trans (le_max_right _ _)

/-- Norms of the left boundary are at most the boundary norm. -/
lemma norm_leftBoundary_le_boundaryNorm (F : InterpolationStripFunction C) (t : ℝ) :
    ‖F.leftBoundary t‖ ≤ F.boundaryNorm := by
  refine (le_csSup (bddAbove_norm_cocompact F.left_zero) (mem_range_self t)).trans ?_
  rw [InterpolationStripFunction.boundaryNorm]
  exact le_max_left _ _

/-- Norms of the right boundary are at most the boundary norm. -/
lemma norm_rightBoundary_le_boundaryNorm (F : InterpolationStripFunction C) (t : ℝ) :
    ‖F.rightBoundary t‖ ≤ F.boundaryNorm := by
  refine (le_csSup (bddAbove_norm_cocompact F.right_zero) (mem_range_self t)).trans ?_
  rw [InterpolationStripFunction.boundaryNorm]
  exact le_max_right _ _

/-- The boundary norm is nonnegative. -/
lemma boundaryNorm_nonneg (F : InterpolationStripFunction C) : 0 ≤ F.boundaryNorm :=
  (norm_nonneg (F.leftBoundary 0)).trans (norm_leftBoundary_le_boundaryNorm F 0)

/-- Left boundary of the weighted target strip function. -/
def weightedLeftBoundary (T : CoupleMap C D) (M₀ M₁ θ : ℝ) (F : InterpolationStripFunction C) :
    C(ℝ, D.left) where
  toFun t := stripWeight M₀ M₁ θ ((t : ℂ) * Complex.I) • T.leftMap (F.leftBoundary t)
  continuous_toFun := by
    have hw : Continuous fun t : ℝ => stripWeight M₀ M₁ θ ((t : ℂ) * Complex.I) :=
      (stripWeight_continuous M₀ M₁ θ).comp (Complex.continuous_ofReal.mul continuous_const)
    exact hw.smul (T.leftMap.continuous.comp F.leftBoundary.continuous)

/-- Right boundary of the weighted target strip function. -/
def weightedRightBoundary (T : CoupleMap C D) (M₀ M₁ θ : ℝ) (F : InterpolationStripFunction C) :
    C(ℝ, D.right) where
  toFun t :=
    stripWeight M₀ M₁ θ (1 + (t : ℂ) * Complex.I) • T.rightMap (F.rightBoundary t)
  continuous_toFun := by
    have hw : Continuous fun t : ℝ => stripWeight M₀ M₁ θ (1 + (t : ℂ) * Complex.I) :=
      (stripWeight_continuous M₀ M₁ θ).comp
        ((continuous_const.add (Complex.continuous_ofReal.mul continuous_const)))
    exact hw.smul (T.rightMap.continuous.comp F.rightBoundary.continuous)

/-- The weighted left boundary vanishes at infinity. -/
lemma weightedLeftBoundary_zero (T : CoupleMap C D) (M₀ M₁ θ : ℝ)
    (F : InterpolationStripFunction C) :
    Tendsto (weightedLeftBoundary T M₀ M₁ θ F) (cocompact ℝ) (𝓝 0) := by
  have hconst : ∀ t : ℝ, ‖stripWeight M₀ M₁ θ ((t : ℂ) * Complex.I)‖ =
      ‖stripWeight M₀ M₁ θ 0‖ := by
    intro t
    exact stripWeight_norm_eq_of_re_eq
      (by rw [re_ofReal_mul_I, Complex.zero_re])
  have hF : Tendsto (fun t : ℝ => ‖F.leftBoundary t‖) (cocompact ℝ) (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mp F.left_zero
  have hineq : ∀ t, ‖weightedLeftBoundary T M₀ M₁ θ F t‖ ≤
      ‖stripWeight M₀ M₁ θ 0‖ * ‖T.leftMap‖ * ‖F.leftBoundary t‖ := by
    intro t
    calc
      ‖weightedLeftBoundary T M₀ M₁ θ F t‖
          = ‖stripWeight M₀ M₁ θ ((t : ℂ) * Complex.I) • T.leftMap (F.leftBoundary t)‖ := by
            rw [weightedLeftBoundary, ContinuousMap.coe_mk]
      _ = ‖stripWeight M₀ M₁ θ ((t : ℂ) * Complex.I)‖ * ‖T.leftMap (F.leftBoundary t)‖ :=
          norm_smul _ _
      _ ≤ ‖stripWeight M₀ M₁ θ ((t : ℂ) * Complex.I)‖ *
            (‖T.leftMap‖ * ‖F.leftBoundary t‖) :=
          mul_le_mul_of_nonneg_left (T.leftMap.le_opNorm _) (norm_nonneg _)
      _ = ‖stripWeight M₀ M₁ θ 0‖ * ‖T.leftMap‖ * ‖F.leftBoundary t‖ := by
          rw [hconst t, mul_assoc]
  have hlim : Tendsto (fun t : ℝ => ‖stripWeight M₀ M₁ θ 0‖ * ‖T.leftMap‖ * ‖F.leftBoundary t‖)
      (cocompact ℝ) (𝓝 0) := by
    simpa [mul_zero] using tendsto_const_nhds.mul hF
  exact squeeze_zero_norm hineq hlim

/-- The weighted right boundary vanishes at infinity. -/
lemma weightedRightBoundary_zero (T : CoupleMap C D) (M₀ M₁ θ : ℝ)
    (F : InterpolationStripFunction C) :
    Tendsto (weightedRightBoundary T M₀ M₁ θ F) (cocompact ℝ) (𝓝 0) := by
  have hconst : ∀ t : ℝ, ‖stripWeight M₀ M₁ θ (1 + (t : ℂ) * Complex.I)‖ =
      ‖stripWeight M₀ M₁ θ 1‖ := by
    intro t
    exact stripWeight_norm_eq_of_re_eq
      (by rw [re_one_add_ofReal_mul_I, Complex.one_re])
  have hF : Tendsto (fun t : ℝ => ‖F.rightBoundary t‖) (cocompact ℝ) (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mp F.right_zero
  have hineq : ∀ t, ‖weightedRightBoundary T M₀ M₁ θ F t‖ ≤
      ‖stripWeight M₀ M₁ θ 1‖ * ‖T.rightMap‖ * ‖F.rightBoundary t‖ := by
    intro t
    calc
      ‖weightedRightBoundary T M₀ M₁ θ F t‖
          = ‖stripWeight M₀ M₁ θ (1 + (t : ℂ) * Complex.I) •
              T.rightMap (F.rightBoundary t)‖ := by
            rw [weightedRightBoundary, ContinuousMap.coe_mk]
      _ = ‖stripWeight M₀ M₁ θ (1 + (t : ℂ) * Complex.I)‖ *
            ‖T.rightMap (F.rightBoundary t)‖ := norm_smul _ _
      _ ≤ ‖stripWeight M₀ M₁ θ (1 + (t : ℂ) * Complex.I)‖ *
            (‖T.rightMap‖ * ‖F.rightBoundary t‖) :=
          mul_le_mul_of_nonneg_left (T.rightMap.le_opNorm _) (norm_nonneg _)
      _ = ‖stripWeight M₀ M₁ θ 1‖ * ‖T.rightMap‖ * ‖F.rightBoundary t‖ := by
          rw [hconst t, mul_assoc]
  have hlim : Tendsto (fun t : ℝ => ‖stripWeight M₀ M₁ θ 1‖ * ‖T.rightMap‖ * ‖F.rightBoundary t‖)
      (cocompact ℝ) (𝓝 0) := by
    simpa [mul_zero] using tendsto_const_nhds.mul hF
  exact squeeze_zero_norm hineq hlim

/-- The weighted composition is bounded on the closed strip. -/
lemma weightedStrip_bounded (T : CoupleMap C D) {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (M₀ M₁ : ℝ)
    (F : InterpolationStripFunction C) :
    ∃ M : ℝ, ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 →
      ‖stripWeight M₀ M₁ θ z • T.ambientMap (F.toFun z)‖ ≤ M := by
  obtain ⟨M, hM⟩ := F.bounded
  refine ⟨Real.exp |Real.log M₀ - Real.log M₁| * ‖T.ambientMap‖ * M, fun z hz0 hz1 => ?_⟩
  calc
    ‖stripWeight M₀ M₁ θ z • T.ambientMap (F.toFun z)‖
        = ‖stripWeight M₀ M₁ θ z‖ * ‖T.ambientMap (F.toFun z)‖ := norm_smul _ _
    _ ≤ Real.exp |Real.log M₀ - Real.log M₁| * ‖T.ambientMap (F.toFun z)‖ :=
        mul_le_mul_of_nonneg_right (stripWeight_norm_le hθ.le hθ1.le hz0 hz1) (norm_nonneg _)
    _ ≤ Real.exp |Real.log M₀ - Real.log M₁| * (‖T.ambientMap‖ * ‖F.toFun z‖) :=
        mul_le_mul_of_nonneg_left (T.ambientMap.le_opNorm _) (Real.exp_nonneg _)
    _ ≤ Real.exp |Real.log M₀ - Real.log M₁| * (‖T.ambientMap‖ * M) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hM z hz0 hz1) (norm_nonneg _)) (Real.exp_nonneg _)
    _ = Real.exp |Real.log M₀ - Real.log M₁| * ‖T.ambientMap‖ * M := by rw [← mul_assoc]

/-- Left boundary agreement for the weighted composition. -/
lemma weightedStrip_left_eq (T : CoupleMap C D) (M₀ M₁ θ : ℝ) (F : InterpolationStripFunction C)
    (t : ℝ) :
    stripWeight M₀ M₁ θ ((t : ℂ) * Complex.I) • T.ambientMap (F.toFun ((t : ℂ) * Complex.I)) =
      D.inLeft (weightedLeftBoundary T M₀ M₁ θ F t) := by
  have hfun : weightedLeftBoundary T M₀ M₁ θ F t =
      stripWeight M₀ M₁ θ ((t : ℂ) * Complex.I) • T.leftMap (F.leftBoundary t) := rfl
  rw [hfun, F.left_eq, T.left_comm]
  exact (D.inLeft.map_smul _ _).symm

/-- Right boundary agreement for the weighted composition. -/
lemma weightedStrip_right_eq (T : CoupleMap C D) (M₀ M₁ θ : ℝ) (F : InterpolationStripFunction C)
    (t : ℝ) :
    stripWeight M₀ M₁ θ (1 + (t : ℂ) * Complex.I) •
        T.ambientMap (F.toFun (1 + (t : ℂ) * Complex.I)) =
      D.inRight (weightedRightBoundary T M₀ M₁ θ F t) := by
  have hfun : weightedRightBoundary T M₀ M₁ θ F t =
      stripWeight M₀ M₁ θ (1 + (t : ℂ) * Complex.I) • T.rightMap (F.rightBoundary t) := rfl
  rw [hfun, F.right_eq, T.right_comm]
  exact (D.inRight.map_smul _ _).symm

/-- Target strip function obtained by weighting `T` applied to `F`. -/
def weightedStrip (T : CoupleMap C D) {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (M₀ M₁ : ℝ)
    (F : InterpolationStripFunction C) : InterpolationStripFunction D where
  toFun z := stripWeight M₀ M₁ θ z • T.ambientMap (F.toFun z)
  continuousOn := by
    refine ContinuousOn.smul (stripWeight_continuous M₀ M₁ θ).continuousOn ?_
    exact T.ambientMap.continuous.comp_continuousOn F.continuousOn
  differentiableOn := by
    refine DifferentiableOn.smul (stripWeight_differentiable M₀ M₁ θ).differentiableOn ?_
    exact T.ambientMap.differentiable.comp_differentiableOn F.differentiableOn
  bounded := weightedStrip_bounded T hθ hθ1 M₀ M₁ F
  leftBoundary := weightedLeftBoundary T M₀ M₁ θ F
  rightBoundary := weightedRightBoundary T M₀ M₁ θ F
  left_eq := weightedStrip_left_eq T M₀ M₁ θ F
  right_eq := weightedStrip_right_eq T M₀ M₁ θ F
  left_zero := weightedLeftBoundary_zero T M₀ M₁ θ F
  right_zero := weightedRightBoundary_zero T M₀ M₁ θ F

/-- The weighted strip function has boundary norm at most the scaled source boundary norm. -/
lemma weightedStrip_boundaryNorm_le (T : CoupleMap C D) {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1)
    {M₀ M₁ : ℝ} (hM₀ : 0 < M₀) (hM₁ : 0 < M₁) (h₀ : ‖T.leftMap‖ ≤ M₀) (h₁ : ‖T.rightMap‖ ≤ M₁)
    (F : InterpolationStripFunction C) :
    (weightedStrip T hθ hθ1 M₀ M₁ F).boundaryNorm ≤
      (M₀ ^ (1 - θ) * M₁ ^ θ) * F.boundaryNorm := by
  let factor : ℝ := M₀ ^ (1 - θ) * M₁ ^ θ
  have hfactor : 0 ≤ factor :=
    mul_nonneg (Real.rpow_nonneg hM₀.le _) (Real.rpow_nonneg hM₁.le _)
  rw [InterpolationStripFunction.boundaryNorm]
  refine max_le ?_ ?_
  · refine csSup_le (range_nonempty _) ?_
    rintro y ⟨t, rfl⟩
    have hfun : (weightedStrip T hθ hθ1 M₀ M₁ F).leftBoundary t =
        weightedLeftBoundary T M₀ M₁ θ F t := rfl
    calc
      ‖(weightedStrip T hθ hθ1 M₀ M₁ F).leftBoundary t‖
          = ‖stripWeight M₀ M₁ θ ((t : ℂ) * Complex.I) • T.leftMap (F.leftBoundary t)‖ := by
            rw [hfun, weightedLeftBoundary, ContinuousMap.coe_mk]
      _ = ‖stripWeight M₀ M₁ θ ((t : ℂ) * Complex.I)‖ * ‖T.leftMap (F.leftBoundary t)‖ :=
            norm_smul _ _
      _ ≤ ‖stripWeight M₀ M₁ θ ((t : ℂ) * Complex.I)‖ * (M₀ * ‖F.leftBoundary t‖) :=
            mul_le_mul_of_nonneg_left
              ((T.leftMap.le_opNorm _).trans (mul_le_mul_of_nonneg_right h₀ (norm_nonneg _)))
              (norm_nonneg _)
      _ = (‖stripWeight M₀ M₁ θ ((t : ℂ) * Complex.I)‖ * M₀) * ‖F.leftBoundary t‖ := by
            rw [mul_assoc]
      _ = factor * ‖F.leftBoundary t‖ := by
            rw [stripWeight_norm_left_mul hM₀ hM₁]
      _ ≤ factor * F.boundaryNorm :=
            mul_le_mul_of_nonneg_left (norm_leftBoundary_le_boundaryNorm F t) hfactor
  · refine csSup_le (range_nonempty _) ?_
    rintro y ⟨t, rfl⟩
    have hfun : (weightedStrip T hθ hθ1 M₀ M₁ F).rightBoundary t =
        weightedRightBoundary T M₀ M₁ θ F t := rfl
    calc
      ‖(weightedStrip T hθ hθ1 M₀ M₁ F).rightBoundary t‖
          = ‖stripWeight M₀ M₁ θ (1 + (t : ℂ) * Complex.I) •
              T.rightMap (F.rightBoundary t)‖ := by
            rw [hfun, weightedRightBoundary, ContinuousMap.coe_mk]
      _ = ‖stripWeight M₀ M₁ θ (1 + (t : ℂ) * Complex.I)‖ *
            ‖T.rightMap (F.rightBoundary t)‖ := norm_smul _ _
      _ ≤ ‖stripWeight M₀ M₁ θ (1 + (t : ℂ) * Complex.I)‖ * (M₁ * ‖F.rightBoundary t‖) :=
            mul_le_mul_of_nonneg_left
              ((T.rightMap.le_opNorm _).trans (mul_le_mul_of_nonneg_right h₁ (norm_nonneg _)))
              (norm_nonneg _)
      _ = (‖stripWeight M₀ M₁ θ (1 + (t : ℂ) * Complex.I)‖ * M₁) * ‖F.rightBoundary t‖ := by
            rw [mul_assoc]
      _ = factor * ‖F.rightBoundary t‖ := by
            rw [stripWeight_norm_right_mul hM₀ hM₁]
      _ ≤ factor * F.boundaryNorm :=
            mul_le_mul_of_nonneg_left (norm_rightBoundary_le_boundaryNorm F t) hfactor

/-- For positive endpoint bounds, the complex interpolation gauge scales by
`M₀ ^ (1 - θ) * M₁ ^ θ`. -/
theorem complexInterpolationGauge_map_le_of_pos (T : CoupleMap C D) {θ : ℝ} (hθ : 0 < θ)
    (hθ1 : θ < 1) {M₀ M₁ : ℝ} (hM₀ : 0 < M₀) (hM₁ : 0 < M₁) (h₀ : ‖T.leftMap‖ ≤ M₀)
    (h₁ : ‖T.rightMap‖ ≤ M₁) (x : C.ambient) :
    D.complexInterpolationGauge θ (T.ambientMap x) ≤
      ENNReal.ofReal (M₀ ^ (1 - θ) * M₁ ^ θ) * C.complexInterpolationGauge θ x := by
  let factor : ℝ := M₀ ^ (1 - θ) * M₁ ^ θ
  have hfactor_nonneg : 0 ≤ factor :=
    mul_nonneg (Real.rpow_nonneg hM₀.le _) (Real.rpow_nonneg hM₁.le _)
  have hfactor_pos : 0 < factor :=
    mul_pos (Real.rpow_pos_of_pos hM₀ _) (Real.rpow_pos_of_pos hM₁ _)
  have hmul : ENNReal.ofReal factor ≠ 0 := (ENNReal.ofReal_pos.mpr hfactor_pos).ne'
  have hmain : D.complexInterpolationGauge θ (T.ambientMap x) ≤
      ⨅ F : InterpolationStripFunction C, ⨅ (_h : F.toFun θ = x),
        ENNReal.ofReal factor * ENNReal.ofReal F.boundaryNorm := by
    refine le_iInf fun F => le_iInf fun hF => ?_
    have hat : (weightedStrip T hθ hθ1 M₀ M₁ F).toFun θ = T.ambientMap x := by
      show stripWeight M₀ M₁ θ θ • T.ambientMap (F.toFun θ) = T.ambientMap x
      rw [stripWeight_self, one_smul, hF]
    calc
      D.complexInterpolationGauge θ (T.ambientMap x)
          ≤ ENNReal.ofReal (weightedStrip T hθ hθ1 M₀ M₁ F).boundaryNorm := by
            rw [BanachCouple.complexInterpolationGauge]
            exact iInf_le_of_le (weightedStrip T hθ hθ1 M₀ M₁ F)
              (iInf_le (fun _ => ENNReal.ofReal (weightedStrip T hθ hθ1 M₀ M₁ F).boundaryNorm) hat)
      _ ≤ ENNReal.ofReal (factor * F.boundaryNorm) :=
            ENNReal.ofReal_le_ofReal
              (by simpa [factor] using weightedStrip_boundaryNorm_le T hθ hθ1 hM₀ hM₁ h₀ h₁ F)
      _ = ENNReal.ofReal factor * ENNReal.ofReal F.boundaryNorm :=
            ENNReal.ofReal_mul hfactor_nonneg
  have hpull : ENNReal.ofReal factor * C.complexInterpolationGauge θ x =
      ⨅ F : InterpolationStripFunction C, ⨅ (_h : F.toFun θ = x),
        ENNReal.ofReal factor * ENNReal.ofReal F.boundaryNorm := by
    rw [BanachCouple.complexInterpolationGauge]
    simp_rw [ENNReal.mul_iInf_of_ne hmul ENNReal.ofReal_ne_top]
  exact hmain.trans (le_of_eq hpull.symm)

end CKMA
