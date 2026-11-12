/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.LIntegral
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Topology.Algebra.ConstMulAction

/-!
# The fractional translation kernel

The squared modulus `|exp(2πi ⟨h, ξ⟩) - 1|² / |h|^{d + 2s}` is integrable on Euclidean space
precisely for `0 < s < 1`. Rotation and dilation reduce its integral to a positive finite
multiple of `‖ξ‖^{2s}`.
-/

@[expose] public section

noncomputable section

namespace CKMA

open MeasureTheory Metric Set
open scoped ENNReal RealInnerProductSpace

/-- Euclidean space of dimension `d`. -/
private abbrev Euc (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The Gagliardo exponent `d + 2s`. -/
private abbrev fracPower (d : ℕ) (s : ℝ) : ℝ := (d : ℝ) + 2 * s

/-- The first basis vector of `Euc d`. -/
private def axis (d : ℕ) (hd : 0 < d) : Euc d :=
  EuclideanSpace.single (⟨0, hd⟩ : Fin d) (1 : ℝ)

/-- The first basis vector is a unit vector. -/
private theorem norm_axis (d : ℕ) (hd : 0 < d) : ‖axis d hd‖ = 1 := by
  simp [axis]

/-- Squared phase modulus along the first coordinate, weighted by `|x|^{-d-2s}`. -/
private def phaseKernel (d : ℕ) (hd : 0 < d) (s : ℝ) (x : Euc d) : ℝ :=
  ‖(Real.fourierChar ⟪x, axis d hd⟫ : ℂ) - 1‖ ^ 2 / ‖x‖ ^ fracPower d s

/-- The phase kernel is nonnegative. -/
private theorem phaseKernel_nonneg (d : ℕ) (hd : 0 < d) (s : ℝ) (x : Euc d) :
    0 ≤ phaseKernel d hd s x := by
  unfold phaseKernel
  exact div_nonneg (sq_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _)

/-- The phase kernel vanishes at the origin, where the real quotient is `0 / 0`. -/
private theorem phaseKernel_zero (d : ℕ) (hd : 0 < d) (s : ℝ) :
    phaseKernel d hd s 0 = 0 := by
  unfold phaseKernel
  rw [inner_zero_left, Real.fourierChar_apply, mul_zero, Complex.ofReal_zero, zero_mul,
    Complex.exp_zero, sub_self, norm_zero, zero_pow two_ne_zero, zero_div]

/-- The numerator of the phase kernel is continuous. -/
private theorem continuous_phaseNum (d : ℕ) (hd : 0 < d) :
    Continuous fun x : Euc d => ‖(Real.fourierChar ⟪x, axis d hd⟫ : ℂ) - 1‖ ^ 2 := by
  refine (continuous_norm.comp ?_).pow 2
  refine (continuous_subtype_val.comp ?_).sub continuous_const
  exact Real.continuous_fourierChar.comp (Continuous.inner continuous_id continuous_const)

/-- The radial weight `|x|^{d+2s}` is continuous for `0 ≤ s`. -/
private theorem continuous_phaseDen (d : ℕ) (hd : 0 < d) {s : ℝ} (hs : 0 ≤ s) :
    Continuous fun x : Euc d => ‖x‖ ^ fracPower d s := by
  refine (continuous_norm.comp continuous_id).rpow_const fun _ => Or.inr ?_
  dsimp [fracPower]
  positivity

/-- The phase kernel is measurable. -/
private theorem measurable_phaseKernel (d : ℕ) (hd : 0 < d) {s : ℝ} (hs : 0 ≤ s) :
    Measurable (phaseKernel d hd s) := by
  unfold phaseKernel
  exact (continuous_phaseNum d hd).measurable.div (continuous_phaseDen d hd hs).measurable

/-- The phase kernel is continuous away from the origin. -/
private theorem continuousAt_phaseKernel (d : ℕ) (hd : 0 < d) {s : ℝ} (hs : 0 ≤ s)
    {x : Euc d} (hx : x ≠ 0) : ContinuousAt (phaseKernel d hd s) x := by
  unfold phaseKernel
  refine ContinuousAt.div (continuous_phaseNum d hd).continuousAt
    (continuous_phaseDen d hd hs).continuousAt ?_
  exact (Real.rpow_pos_of_pos (norm_pos_iff.mpr hx) _).ne'

/-- On the ball of radius `(2π)⁻¹`, the phase kernel is bounded by `|x|^{2-d-2s}`. -/
private theorem phaseKernel_le_near (d : ℕ) (hd : 0 < d) {s : ℝ} (_hs : 0 < s) {x : Euc d}
    (hx : ‖x‖ ≤ (2 * Real.pi)⁻¹) :
    phaseKernel d hd s x ≤
      16 * Real.pi ^ 2 * ‖x‖ ^ (-(fracPower d s - 2)) := by
  by_cases hx0 : x = 0
  · rw [hx0, phaseKernel_zero]
    exact mul_nonneg (by positivity) (Real.rpow_nonneg (norm_nonneg _) _)
  have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  set t : ℝ := ⟪x, axis d hd⟫
  have habs : |t| ≤ ‖x‖ := by
    have h := abs_real_inner_le_norm x (axis d hd)
    simpa [t, norm_axis d hd, mul_one] using h
  have hπ : 0 < 2 * Real.pi := by positivity
  have hangle : |2 * Real.pi * t| ≤ 1 := by
    calc
      |2 * Real.pi * t| = 2 * Real.pi * |t| := by rw [abs_mul, abs_of_pos hπ]
      _ ≤ 2 * Real.pi * ‖x‖ := mul_le_mul_of_nonneg_left habs hπ.le
      _ ≤ 2 * Real.pi * (2 * Real.pi)⁻¹ :=
        mul_le_mul_of_nonneg_left hx hπ.le
      _ = 1 := by rw [mul_inv_cancel₀ hπ.ne']
  have hz : ‖(↑(2 * Real.pi * t) * Complex.I : ℂ)‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    exact hangle
  have hexp : ‖Complex.exp (↑(2 * Real.pi * t) * Complex.I) - 1‖ ≤
      2 * |2 * Real.pi * t| := by
    simpa [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs] using
      Complex.norm_exp_sub_one_le hz
  have hcoef : 2 * |2 * Real.pi * t| = 4 * Real.pi * |t| := by
    rw [abs_mul, abs_of_pos hπ]
    ring
  have hnum : ‖(Real.fourierChar t : ℂ) - 1‖ ^ 2 ≤ (4 * Real.pi * |t|) ^ 2 := by
    rw [← hcoef, Real.fourierChar_apply, pow_two, pow_two]
    exact mul_self_le_mul_self (norm_nonneg _) hexp
  have hnum' : ‖(Real.fourierChar t : ℂ) - 1‖ ^ 2 ≤
      16 * Real.pi ^ 2 * ‖x‖ ^ 2 := by
    calc
      ‖(Real.fourierChar t : ℂ) - 1‖ ^ 2 ≤ (4 * Real.pi * |t|) ^ 2 := hnum
      _ ≤ (4 * Real.pi * ‖x‖) ^ 2 := by
        apply pow_le_pow_left₀ (by positivity)
        exact mul_le_mul_of_nonneg_left habs (by positivity)
      _ = 16 * Real.pi ^ 2 * ‖x‖ ^ 2 := by ring
  have hden : 0 < ‖x‖ ^ fracPower d s := Real.rpow_pos_of_pos hxnorm _
  calc
    phaseKernel d hd s x = ‖(Real.fourierChar t : ℂ) - 1‖ ^ 2 / ‖x‖ ^ fracPower d s := by
      simp [phaseKernel, t]
    _ ≤ (16 * Real.pi ^ 2 * ‖x‖ ^ 2) / ‖x‖ ^ fracPower d s :=
      div_le_div_of_nonneg_right hnum' hden.le
    _ = 16 * Real.pi ^ 2 * (‖x‖ ^ 2 / ‖x‖ ^ fracPower d s) := by
      rw [mul_div_assoc]
    _ = 16 * Real.pi ^ 2 * ‖x‖ ^ (2 - fracPower d s) := by
      congr 1
      rw [← Real.rpow_natCast ‖x‖ 2, ← Real.rpow_sub hxnorm]
      ring_nf
    _ = 16 * Real.pi ^ 2 * ‖x‖ ^ (-(fracPower d s - 2)) := by
      congr 1
      ring_nf

/-- Outside that ball the phase kernel is bounded by a multiple of `(1 + |x|)^{-d-2s}`. -/
private theorem phaseKernel_le_far (d : ℕ) (hd : 0 < d) {s : ℝ} (hs : 0 < s) {x : Euc d}
    (hx : (2 * Real.pi)⁻¹ ≤ ‖x‖) :
    phaseKernel d hd s x ≤
      4 * (1 + 2 * Real.pi) ^ fracPower d s * (1 + ‖x‖) ^ (-fracPower d s) := by
  have hx0 : x ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hx
    exact lt_irrefl (0 : ℝ) <| lt_of_lt_of_le (inv_pos.mpr (by positivity)) hx
  have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hnum : ‖(Real.fourierChar ⟪x, axis d hd⟫ : ℂ) - 1‖ ^ 2 ≤ 4 := by
    have hle : ‖(Real.fourierChar ⟪x, axis d hd⟫ : ℂ) - 1‖ ≤ 2 := by
      refine (norm_sub_le _ _).trans ?_
      rw [Circle.norm_coe, norm_one]
      norm_num
    rw [pow_two, show (4 : ℝ) = 2 * 2 by norm_num]
    exact mul_self_le_mul_self (norm_nonneg _) hle
  have hp : 0 ≤ fracPower d s := by dsimp [fracPower]; positivity
  have hden : 0 < ‖x‖ ^ fracPower d s := Real.rpow_pos_of_pos hxnorm _
  have hone : 0 < (1 + ‖x‖) ^ fracPower d s := Real.rpow_pos_of_pos (by positivity) _
  have hratio : (1 + ‖x‖) / ‖x‖ ≤ 1 + 2 * Real.pi := by
    rw [div_le_iff₀ hxnorm]
    have : (1 : ℝ) ≤ 2 * Real.pi * ‖x‖ := by
      have hx' : 1 / (2 * Real.pi) ≤ ‖x‖ := by simpa [one_div] using hx
      simpa [mul_comm] using (div_le_iff₀ (by positivity : 0 < 2 * Real.pi)).mp hx'
    linarith
  have hAB : (1 + ‖x‖) ^ fracPower d s / ‖x‖ ^ fracPower d s ≤
      (1 + 2 * Real.pi) ^ fracPower d s := by
    have hpow := Real.rpow_le_rpow (div_nonneg (by positivity) hxnorm.le) hratio hp
    rwa [Real.div_rpow (by positivity) hxnorm.le] at hpow
  have hinv : 1 / ‖x‖ ^ fracPower d s ≤
      (1 + 2 * Real.pi) ^ fracPower d s / (1 + ‖x‖) ^ fracPower d s := by
    rw [div_le_div_iff₀ hden hone, one_mul]
    rwa [div_le_iff₀ hden] at hAB
  calc
    phaseKernel d hd s x
        ≤ 4 / ‖x‖ ^ fracPower d s := by
          simpa [phaseKernel] using div_le_div_of_nonneg_right hnum hden.le
      _ = 4 * (1 / ‖x‖ ^ fracPower d s) := by rw [mul_one_div]
      _ ≤ 4 * ((1 + 2 * Real.pi) ^ fracPower d s / (1 + ‖x‖) ^ fracPower d s) := by
          gcongr
      _ = 4 * (1 + 2 * Real.pi) ^ fracPower d s * (1 + ‖x‖) ^ (-fracPower d s) := by
          rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ 1 + ‖x‖), div_eq_mul_inv, mul_assoc]

/-- The phase kernel is integrable for `0 < s < 1`. -/
private theorem phaseKernel_integrable {d : ℕ} (hd : 0 < d) {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    Integrable (phaseKernel d hd s) (volume : Measure (Euc d)) := by
  let δ : ℝ := (2 * Real.pi)⁻¹
  have hδ : 0 < δ := by positivity
  have hα : fracPower d s - 2 < ↑(Module.finrank ℝ (Euc d)) := by
    rw [finrank_euclideanSpace_fin]
    dsimp [fracPower]
    linarith
  have hd1 : 1 ≤ Module.finrank ℝ (Euc d) := by
    rw [finrank_euclideanSpace_fin]
    exact hd
  have hball : IntegrableOn (phaseKernel d hd s) (ball 0 δ) volume := by
    refine integrableOn_ball_of_norm_le_rpow (μ := volume) (C := 16 * Real.pi ^ 2) (r := δ) hd1 hα
      ?_ ?_
    · refine ae_restrict_of_forall_mem measurableSet_ball fun x hx => ?_
      have hxle : ‖x‖ ≤ (2 * Real.pi)⁻¹ := by
        have hlt : ‖x‖ < δ := by simpa [mem_ball_zero_iff] using hx
        simpa [δ] using hlt.le
      rw [Real.norm_eq_abs, abs_of_nonneg (phaseKernel_nonneg d hd s x)]
      exact phaseKernel_le_near d hd hs hxle
    · exact (measurable_phaseKernel d hd hs.le).aestronglyMeasurable
  have htail : IntegrableOn (phaseKernel d hd s) (ball 0 δ)ᶜ volume := by
    have hp : ↑(Module.finrank ℝ (Euc d)) < fracPower d s := by
      rw [finrank_euclideanSpace_fin]
      dsimp [fracPower]
      linarith
    let K : ℝ := 4 * (1 + 2 * Real.pi) ^ fracPower d s
    have hmaj : Integrable (fun x : Euc d => K * (1 + ‖x‖) ^ (-fracPower d s)) volume :=
      (integrable_one_add_norm (μ := volume) (E := Euc d) hp).const_mul K
    refine Integrable.mono' hmaj.integrableOn
      ((measurable_phaseKernel d hd hs.le).aestronglyMeasurable.mono_measure
        Measure.restrict_le_self) ?_
    refine ae_restrict_of_forall_mem measurableSet_ball.compl fun x hx => ?_
    have hxnorm : δ ≤ ‖x‖ := by
      simpa [δ, mem_compl_iff, mem_ball_zero_iff, not_lt] using hx
    have hle := phaseKernel_le_far d hd hs hxnorm
    rw [Real.norm_eq_abs, abs_of_nonneg (phaseKernel_nonneg d hd s x)]
    simpa [K, δ] using hle
  have hunion : IntegrableOn (phaseKernel d hd s) (ball 0 δ ∪ (ball 0 δ)ᶜ) volume :=
    hball.union htail
  rw [union_compl_self, integrableOn_univ] at hunion
  exact hunion

/-- Integral of the phase kernel along the first coordinate. -/
private def fourierConst (d : ℕ) (hd : 0 < d) (s : ℝ) : ℝ :=
  ∫ x, phaseKernel d hd s x

/-- `exp(πi) = -1`, so the phase kernel is positive at half the first basis vector. -/
private theorem fourierChar_half : (Real.fourierChar (1 / 2) : ℂ) = -1 := by
  rw [Real.fourierChar_apply', Circle.coe_exp]
  have hpi : (2 : ℝ) * Real.pi * (1 / 2) = Real.pi := by ring
  rw [hpi]
  exact Complex.exp_pi_mul_I

/-- The phase-kernel integral is positive. -/
private theorem fourierConst_pos {d : ℕ} (hd : 0 < d) {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    0 < fourierConst d hd s := by
  have hint : Integrable (phaseKernel d hd s) volume := phaseKernel_integrable hd hs hs1
  set x0 : Euc d := (1 / 2 : ℝ) • axis d hd
  have hx0 : x0 ≠ 0 := by
    intro hzero
    have : ‖x0‖ = 0 := by simp [hzero]
    have hnorm : ‖x0‖ = 1 / 2 := by
      rw [norm_smul, norm_axis d hd, mul_one, Real.norm_eq_abs, abs_of_pos (by norm_num)]
    linarith
  have hinner : ⟪x0, axis d hd⟫ = 1 / 2 := by
    rw [inner_smul_left, real_inner_self_eq_norm_sq, norm_axis d hd]
    simp
  have hker : phaseKernel d hd s x0 = 4 / (1 / 2 : ℝ) ^ fracPower d s := by
    unfold phaseKernel
    rw [hinner, fourierChar_half]
    have hnum : ‖(-1 - 1 : ℂ)‖ ^ 2 = 4 := by
      rw [show (-1 - 1 : ℂ) = -2 by ring, norm_neg]
      norm_num
    have hden : ‖x0‖ = 1 / 2 := by
      rw [norm_smul, norm_axis d hd, mul_one, Real.norm_eq_abs, abs_of_pos (by norm_num)]
    simp [hnum, hden]
  have hkerpos : 0 < phaseKernel d hd s x0 := by
    rw [hker]
    exact div_pos (by norm_num) (Real.rpow_pos_of_pos (by norm_num) _)
  have hcont : ContinuousAt (phaseKernel d hd s) x0 :=
    continuousAt_phaseKernel d hd hs.le hx0
  obtain ⟨δ, hδ, hnear⟩ :=
    Metric.continuousAt_iff.mp hcont (phaseKernel d hd s x0 / 2) (half_pos hkerpos)
  have hlow : ∀ y ∈ ball x0 δ, phaseKernel d hd s x0 / 2 ≤ phaseKernel d hd s y := by
    intro y hy
    have hdist : dist y x0 < δ := mem_ball.mp hy
    have habs : |phaseKernel d hd s y - phaseKernel d hd s x0| < phaseKernel d hd s x0 / 2 := by
      simpa [Real.dist_eq] using hnear (x := y) hdist
    rw [abs_lt] at habs
    linarith
  have hμ : 0 < volume.real (ball x0 δ) := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (measure_ball_pos volume x0 hδ).ne' measure_ball_lt_top.ne
  have hintc : IntegrableOn (fun _ : Euc d => phaseKernel d hd s x0 / 2) (ball x0 δ) volume :=
    integrableOn_const measure_ball_lt_top.ne
  have hintk : IntegrableOn (phaseKernel d hd s) (ball x0 δ) volume := hint.integrableOn
  have hineq := setIntegral_mono_on hintc hintk measurableSet_ball hlow
  have hconst : 0 < ∫ _ in ball x0 δ, phaseKernel d hd s x0 / 2 ∂volume := by
    rw [setIntegral_const, smul_eq_mul]
    exact mul_pos hμ (div_pos hkerpos two_pos)
  have hball : 0 < ∫ x in ball x0 δ, phaseKernel d hd s x ∂volume := lt_of_lt_of_le hconst hineq
  have hfull : ∫ x in ball x0 δ, phaseKernel d hd s x ∂volume ≤ fourierConst d hd s := by
    simpa [fourierConst] using
      setIntegral_le_integral hint (ae_of_all _ fun x => phaseKernel_nonneg d hd s x)
  exact lt_of_lt_of_le hball hfull

/-- The extended integral of the phase kernel is the ordinary integral. -/
private theorem fourierConst_lintegral {d : ℕ} (hd : 0 < d) {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    ENNReal.ofReal (fourierConst d hd s) =
      ∫⁻ x, ENNReal.ofReal (phaseKernel d hd s x) := by
  simpa [fourierConst] using
    ofReal_integral_eq_lintegral_ofReal (phaseKernel_integrable hd hs hs1)
      (ae_of_all _ fun x => phaseKernel_nonneg d hd s x)

set_option backward.isDefEq.respectTransparency false

/-- Every unit direction has the same phase-kernel integral. -/
private theorem lintegral_phase_unit {d : ℕ} (hd : 0 < d) {s : ℝ} (hs : 0 < s) (hs1 : s < 1)
    {w : Euc d} (hw : ‖w‖ = 1) :
    ∫⁻ x, ENNReal.ofReal
        (‖(Real.fourierChar ⟪x, w⟫ : ℂ) - 1‖ ^ 2 / ‖x‖ ^ fracPower d s) =
      ENNReal.ofReal (fourierConst d hd s) := by
  let R : Euc d ≃ₗᵢ[ℝ] Euc d :=
    Submodule.reflection (Submodule.orthogonal (Submodule.span ℝ {axis d hd - w}))
  have hRw : R (axis d hd) = w := by
    simpa [R] using Submodule.reflection_sub (v := axis d hd) (w := w)
      (by simp [norm_axis d hd, hw])
  have hpres := LinearIsometryEquiv.measurePreserving R.symm
  have hembed : MeasurableEmbedding R.symm := R.symm.toHomeomorph.measurableEmbedding
  have hpoint : ∀ a,
      ENNReal.ofReal
          (‖(Real.fourierChar ⟪a, w⟫ : ℂ) - 1‖ ^ 2 / ‖a‖ ^ fracPower d s) =
        ENNReal.ofReal (phaseKernel d hd s (R.symm a)) := by
    intro a
    refine congrArg ENNReal.ofReal ?_
    have hinner : ⟪R.symm a, axis d hd⟫ = ⟪a, w⟫ := by
      simpa [hRw] using (R.inner_map_map (R.symm a) (axis d hd)).symm
    have hnorm : ‖R.symm a‖ = ‖a‖ := R.symm.norm_map a
    calc
      ‖(Real.fourierChar ⟪a, w⟫ : ℂ) - 1‖ ^ 2 / ‖a‖ ^ fracPower d s
          = ‖(Real.fourierChar ⟪R.symm a, axis d hd⟫ : ℂ) - 1‖ ^ 2 / ‖a‖ ^ fracPower d s :=
            congrArg
              (fun t : ℝ => ‖(Real.fourierChar t : ℂ) - 1‖ ^ 2 / ‖a‖ ^ fracPower d s) hinner.symm
      _ = ‖(Real.fourierChar ⟪R.symm a, axis d hd⟫ : ℂ) - 1‖ ^ 2 /
            ‖R.symm a‖ ^ fracPower d s :=
          congrArg
            (fun r : ℝ =>
              ‖(Real.fourierChar ⟪R.symm a, axis d hd⟫ : ℂ) - 1‖ ^ 2 / r ^ fracPower d s)
            hnorm.symm
      _ = phaseKernel d hd s (R.symm a) := by rfl
  exact (lintegral_congr hpoint).trans
    ((hpres.lintegral_comp_emb hembed _).trans (fourierConst_lintegral hd hs hs1).symm)

/-- Scaling the frequency by `t > 0` multiplies the phase integral by `t^{2s}`. -/
private theorem lintegral_phase_smul {d : ℕ} {s : ℝ} {t : ℝ} (ht : 0 < t) {w : Euc d} :
    ∫⁻ h, ENNReal.ofReal
        (‖(Real.fourierChar ⟪h, t • w⟫ : ℂ) - 1‖ ^ 2 / ‖h‖ ^ fracPower d s) =
      ENNReal.ofReal (t ^ (2 * s)) *
        ∫⁻ h, ENNReal.ofReal
          (‖(Real.fourierChar ⟪h, w⟫ : ℂ) - 1‖ ^ 2 / ‖h‖ ^ fracPower d s) := by
  let p : ℝ := fracPower d s
  have hpoint : ∀ h : Euc d,
      ‖(Real.fourierChar ⟪h, t • w⟫ : ℂ) - 1‖ ^ 2 / ‖h‖ ^ p =
        t ^ p * (‖(Real.fourierChar ⟪t • h, w⟫ : ℂ) - 1‖ ^ 2 / ‖t • h‖ ^ p) := by
    intro h
    by_cases hh : h = 0
    · simp [hh, inner_zero_left, mul_zero, zero_div]
    · have hhnorm : 0 < ‖h‖ := norm_pos_iff.mpr hh
      have hinner : ⟪h, t • w⟫ = ⟪t • h, w⟫ := by
        rw [inner_smul_right, inner_smul_left]
        simp
      have hnorm : ‖t • h‖ = t * ‖h‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
      have hden : ‖h‖ ^ p = ‖t • h‖ ^ p / t ^ p := by
        rw [hnorm, Real.mul_rpow ht.le (norm_nonneg _)]
        exact (mul_div_cancel_left₀ _ (Real.rpow_pos_of_pos ht p).ne').symm
      rw [hinner]
      set num : ℝ := ‖(Real.fourierChar ⟪t • h, w⟫ : ℂ) - 1‖ ^ 2
      rw [hden]
      have htpow : t ^ p ≠ 0 := (Real.rpow_pos_of_pos ht p).ne'
      have hsp : ‖t • h‖ ^ p ≠ 0 := by
        rw [hnorm]
        exact (Real.rpow_pos_of_pos (mul_pos ht hhnorm) p).ne'
      field_simp [htpow, hsp]
  have hjac : ∀ f : Euc d → ℝ≥0∞,
      ∫⁻ h, f (t • h) = ENNReal.ofReal (t ^ (-(d : ℝ))) * ∫⁻ h, f h := by
    intro f
    have hembed :=
      (Homeomorph.smulOfNeZero (α := Euc d) t ht.ne').measurableEmbedding
    have hsmul : ∀ h, (Homeomorph.smulOfNeZero (α := Euc d) t ht.ne') h = t • h :=
      fun _ => rfl
    simp_rw [← hsmul]
    rw [← hembed.lintegral_map f]
    have hfun : (⇑(Homeomorph.smulOfNeZero (α := Euc d) t ht.ne') : Euc d → Euc d) =
        (t • ·) := by
      funext h
      exact hsmul h
    rw [hfun, Measure.map_addHaar_smul (volume : Measure (Euc d)) ht.ne',
      lintegral_smul_measure, smul_eq_mul]
    congr 1
    rw [finrank_euclideanSpace_fin, abs_of_pos (inv_pos.mpr (pow_pos ht _)),
      ← Real.rpow_natCast, ← Real.rpow_neg ht.le]
  let kernel : Euc d → ℝ :=
    fun k => ‖(Real.fourierChar ⟪k, w⟫ : ℂ) - 1‖ ^ 2 / ‖k‖ ^ p
  have hrewrite : ∀ h, ENNReal.ofReal
      (‖(Real.fourierChar ⟪h, t • w⟫ : ℂ) - 1‖ ^ 2 / ‖h‖ ^ p) =
      ENNReal.ofReal (t ^ p) * ENNReal.ofReal (kernel (t • h)) := by
    intro h
    calc
      ENNReal.ofReal
          (‖(Real.fourierChar ⟪h, t • w⟫ : ℂ) - 1‖ ^ 2 / ‖h‖ ^ p) =
          ENNReal.ofReal (t ^ p * kernel (t • h)) := congrArg ENNReal.ofReal (hpoint h)
      _ = ENNReal.ofReal (t ^ p) * ENNReal.ofReal (kernel (t • h)) :=
        ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _)
  have hpow : ENNReal.ofReal (t ^ p) * ENNReal.ofReal (t ^ (-(d : ℝ))) =
      ENNReal.ofReal (t ^ (2 * s)) := by
    unfold p
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _), ← Real.rpow_add ht]
    ring_nf
  calc
    ∫⁻ h, ENNReal.ofReal
          (‖(Real.fourierChar ⟪h, t • w⟫ : ℂ) - 1‖ ^ 2 / ‖h‖ ^ fracPower d s)
      = ∫⁻ h, ENNReal.ofReal (t ^ p) * ENNReal.ofReal (kernel (t • h)) :=
        lintegral_congr hrewrite
    _ = ENNReal.ofReal (t ^ p) * ∫⁻ h, ENNReal.ofReal (kernel (t • h)) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (t ^ p) *
          (ENNReal.ofReal (t ^ (-(d : ℝ))) * ∫⁻ h, ENNReal.ofReal (kernel h)) :=
        congrArg (fun z : ℝ≥0∞ => ENNReal.ofReal (t ^ p) * z)
          (hjac fun h => ENNReal.ofReal (kernel h))
    _ = (ENNReal.ofReal (t ^ p) * ENNReal.ofReal (t ^ (-(d : ℝ)))) *
          ∫⁻ h, ENNReal.ofReal (kernel h) := by rw [mul_assoc]
    _ = ENNReal.ofReal (t ^ (2 * s)) * ∫⁻ h, ENNReal.ofReal (kernel h) := by
      rw [hpow]

/-- Integrating the phase weight produces `C ‖ξ‖^{2s}` with `0 < C < ∞`. -/
public theorem phase_kernel_integral {d : ℕ} (hd : 0 < d) {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ ξ : EuclideanSpace ℝ (Fin d),
      ∫⁻ h, ENNReal.ofReal
          (‖(Real.fourierChar ⟪h, ξ⟫ : ℂ) - 1‖ ^ 2 / ‖h‖ ^ ((d : ℝ) + 2 * s)) =
        ENNReal.ofReal (C * ‖ξ‖ ^ (2 * s)) := by
  refine ⟨fourierConst d hd s, fourierConst_pos hd hs hs1, fun ξ => ?_⟩
  by_cases hξ : ξ = 0
  · subst hξ
    simp [inner_zero_right, mul_zero, zero_div,
      Real.zero_rpow (mul_ne_zero two_ne_zero hs.ne'), mul_zero]
  · set t : ℝ := ‖ξ‖
    have ht : 0 < t := norm_pos_iff.mpr hξ
    set w : Euc d := t⁻¹ • ξ
    have hw : ‖w‖ = 1 := by
      rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos ht, inv_mul_cancel₀ ht.ne']
    have hξeq : ξ = t • w := by
      simp [w, smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
    rw [hξeq, lintegral_phase_smul ht, lintegral_phase_unit hd hs hs1 hw]
    rw [← ENNReal.ofReal_mul' (fourierConst_pos hd hs hs1).le, mul_comm]

end CKMA
