/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# One-dimensional Gaussian integration by parts

The standard normal density satisfies `ρ' = -x ρ`. For a `C¹` integrand with bounded value and
derivative, the boundary terms vanish and `∫ x ψ ∂γ = ∫ ψ' ∂γ`.

## Main results

* `CKMA.gaussianPDFReal_zero_one_apply`: Explicit formula for the standard normal density.
* `CKMA.hasDerivAt_gaussianPDFReal_zero_one`: Derivative of the standard normal density.
* `CKMA.integral_id_mul_eq_integral_deriv_gaussianReal`: Gaussian integration by parts
  `∫ x ψ ∂γ = ∫ ψ' ∂γ`.
* `CKMA.integrable_of_abs_le`: Integrability of bounded a.e. strongly measurable functions on
  finite measure spaces.
* `CKMA.exists_bound_of_deriv_eq_zero`: Boundedness of differentiable functions with compactly
  supported derivative.
-/

@[expose] public section

noncomputable section

namespace CKMA

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal Real

/-- Explicit formula for the standard normal density. -/
lemma gaussianPDFReal_zero_one_apply (t : ℝ) :
    gaussianPDFReal 0 1 t = (√(2 * π))⁻¹ * Real.exp (-(t ^ 2) / 2) := by
  unfold gaussianPDFReal
  rw [sub_zero]
  have hcoe : ((1 : NNReal) : ℝ) = 1 := NNReal.coe_one
  simp only [hcoe, mul_one]

/-- The standard normal density has logarithmic derivative `-x`. -/
lemma hasDerivAt_gaussianPDFReal_zero_one (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-x * gaussianPDFReal 0 1 x) x := by
  set c : ℝ := (√(2 * π))⁻¹
  have hinner : HasDerivAt (fun t : ℝ => -(t ^ 2) / 2) (-x) x := by
    have hpow : HasDerivAt (fun t : ℝ => t ^ 2) ((2 : ℕ) * x ^ (2 - 1)) x :=
      hasDerivAt_pow 2 x
    refine hpow.neg.div_const (2 : ℝ) |>.congr_deriv ?_
    simp only [Nat.cast_ofNat]
    ring
  have hexp : HasDerivAt (fun t => Real.exp (-(t ^ 2) / 2))
      (Real.exp (-(x ^ 2) / 2) * -x) x := hinner.exp
  have hmul : HasDerivAt (fun t => c * Real.exp (-(t ^ 2) / 2))
      (c * (Real.exp (-(x ^ 2) / 2) * -x)) x :=
    ((hasDerivAt_const x c).mul hexp).congr_deriv (by ring)
  have hfun : gaussianPDFReal 0 1 = fun t => c * Real.exp (-(t ^ 2) / 2) := by
    funext t
    simpa [c] using gaussianPDFReal_zero_one_apply t
  rw [hfun]
  refine hmul.congr_deriv ?_
  ring

/-- Gaussian integration by parts: `∫ x ψ ∂γ = ∫ ψ' ∂γ` for a bounded `C¹` integrand. -/
lemma integral_id_mul_eq_integral_deriv_gaussianReal {ψ : ℝ → ℝ}
    (hψ : Differentiable ℝ ψ) (hψ' : Continuous (deriv ψ))
    (hψ_bdd : ∃ C, ∀ x, |ψ x| ≤ C) (hψ'_bdd : ∃ C, ∀ x, |deriv ψ x| ≤ C) :
    ∫ x, x * ψ x ∂gaussianReal 0 1 = ∫ x, deriv ψ x ∂gaussianReal 0 1 := by
  obtain ⟨C, hC⟩ := hψ_bdd
  obtain ⟨C', hC'⟩ := hψ'_bdd
  set ρ : ℝ → ℝ := gaussianPDFReal 0 1
  have hρ_nonneg : ∀ x, 0 ≤ ρ x := gaussianPDFReal_nonneg 0 1
  have hρ_int : Integrable ρ volume := integrable_gaussianPDFReal 0 1
  have hxρ_int : Integrable (fun x => |x| * ρ x) volume := by
    have hid0 : Integrable id (gaussianReal 0 1) :=
      memLp_one_iff_integrable.mp (memLp_id_gaussianReal (μ := 0) (v := 1) 1)
    have hid : Integrable (fun x : ℝ => |x|) (gaussianReal 0 1) := by
      simpa [Real.norm_eq_abs] using hid0.norm
    have hone : (1 : NNReal) ≠ 0 := one_ne_zero
    rw [gaussianReal_of_var_ne_zero (0 : ℝ) hone] at hid
    have hsmul :=
      (integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 1)
        (ae_of_all _ fun _ => gaussianPDF_lt_top)).mp hid
    simpa [ρ, gaussianPDF, ENNReal.toReal_ofReal, hρ_nonneg, mul_comm] using hsmul
  let F : ℝ → ℝ := fun x => ψ x * ρ x
  let F' : ℝ → ℝ := fun x => (deriv ψ x - x * ψ x) * ρ x
  have hψ_diff : Differentiable ℝ ψ := hψ
  have hF_deriv : ∀ x, HasDerivAt F (F' x) x := by
    intro x
    have hψx : HasDerivAt ψ (deriv ψ x) x := (hψ_diff x).hasDerivAt
    have hρx : HasDerivAt ρ (-x * ρ x) x := hasDerivAt_gaussianPDFReal_zero_one x
    convert hψx.mul hρx using 1
    simp only [F']
    ring
  have hF_meas : AEStronglyMeasurable F volume :=
    hψ_diff.continuous.aestronglyMeasurable.mul
      (stronglyMeasurable_gaussianPDFReal 0 1).aestronglyMeasurable
  have hF_int : Integrable F volume := by
    refine Integrable.mono' (hρ_int.const_mul (|C| + 1)) hF_meas ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hρ_nonneg x)]
    exact mul_le_mul_of_nonneg_right
      ((hC x).trans <| (le_abs_self C).trans (le_add_of_nonneg_right zero_le_one))
      (hρ_nonneg x)
  have hderiv_meas : AEStronglyMeasurable (fun x => deriv ψ x) volume :=
    hψ'.aestronglyMeasurable
  have hψρ_int : Integrable (fun x => deriv ψ x * ρ x) volume := by
    refine Integrable.mono' (hρ_int.const_mul (|C'| + 1))
      (hderiv_meas.mul (stronglyMeasurable_gaussianPDFReal 0 1).aestronglyMeasurable) ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hρ_nonneg x)]
    exact mul_le_mul_of_nonneg_right
      ((hC' x).trans <| (le_abs_self C').trans (le_add_of_nonneg_right zero_le_one))
      (hρ_nonneg x)
  have hxψρ_int : Integrable (fun x => x * ψ x * ρ x) volume := by
    refine Integrable.mono' (hxρ_int.const_mul (|C| + 1)) ?_ ?_
    · exact ((continuous_id.mul hψ_diff.continuous).aestronglyMeasurable.mul
        (stronglyMeasurable_gaussianPDFReal 0 1).aestronglyMeasurable)
    · filter_upwards with x
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hρ_nonneg x)]
      calc |x| * |ψ x| * ρ x ≤ |x| * (|C| + 1) * ρ x := by
            refine mul_le_mul_of_nonneg_right ?_ (hρ_nonneg x)
            refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg x)
            exact (hC x).trans <| (le_abs_self C).trans (le_add_of_nonneg_right zero_le_one)
        _ = (|C| + 1) * (|x| * ρ x) := by ring
  have hF'_int : Integrable F' volume := by
    have hsub : Integrable (fun x => deriv ψ x * ρ x - x * ψ x * ρ x) volume :=
      hψρ_int.sub hxψρ_int
    convert hsub using 1
    funext x
    simp only [F']
    ring
  have hzero : ∫ x, F' x = 0 :=
    integral_eq_zero_of_hasDerivAt_of_integrable hF_deriv hF'_int hF_int
  have hsplit : ∫ x, deriv ψ x * ρ x - x * ψ x * ρ x = 0 := by
    convert hzero using 2
    funext x
    simp only [F']
    ring
  have hsub_eq :
      (∫ x, deriv ψ x * ρ x) - (∫ x, x * ψ x * ρ x) = 0 := by
    rw [← integral_sub hψρ_int hxψρ_int]
    convert hsplit using 1
  have hEq : (∫ x, deriv ψ x * ρ x) = (∫ x, x * ψ x * ρ x) := sub_eq_zero.mp hsub_eq
  have hγ_deriv : ∫ x, deriv ψ x ∂gaussianReal 0 1 = ∫ x, ρ x * deriv ψ x := by
    simpa [ρ, mul_comm] using
      integral_gaussianReal_eq_integral_smul (E := ℝ) (μ := 0) (v := 1)
        (f := fun x => deriv ψ x) one_ne_zero
  have hγ_id : ∫ x, x * ψ x ∂gaussianReal 0 1 = ∫ x, ρ x * (x * ψ x) := by
    simpa [ρ, mul_comm] using
      integral_gaussianReal_eq_integral_smul (E := ℝ) (μ := 0) (v := 1)
        (f := fun x => x * ψ x) one_ne_zero
  calc ∫ x, x * ψ x ∂gaussianReal 0 1
      = ∫ x, ρ x * (x * ψ x) := hγ_id
    _ = ∫ x, x * ψ x * ρ x := by simp [mul_comm, mul_assoc]
    _ = ∫ x, deriv ψ x * ρ x := hEq.symm
    _ = ∫ x, ρ x * deriv ψ x := by simp [mul_comm]
    _ = ∫ x, deriv ψ x ∂gaussianReal 0 1 := hγ_deriv.symm

/-- An a.e. strongly measurable function bounded by a constant is integrable on a finite measure
space. -/
lemma integrable_of_abs_le {E : Type*} [MeasurableSpace E] {μ : Measure E}
    [IsFiniteMeasure μ] {f : E → ℝ} (hf : AEStronglyMeasurable f μ) {M : ℝ}
    (hM : ∀ x, |f x| ≤ M) : Integrable f μ :=
  .of_bound hf M (ae_of_all _ fun x => (Real.norm_eq_abs _).trans_le (hM x))

/-- A function with vanishing derivative outside a compact interval equals its endpoint value. -/
lemma eq_endpoint_of_deriv_eq_zero {f : ℝ → ℝ} {R : ℝ} (hR : 0 ≤ R)
    (hf : Differentiable ℝ f) (hderiv : ∀ x, R ≤ |x| → deriv f x = 0)
    {x : ℝ} (hx : R ≤ |x|) :
    f x = f (if 0 ≤ x then R else -R) := by
  have hd : ∀ y, R ≤ |y| → HasDerivWithinAt f 0 (Ici y) y := fun y hy => by
    have h := (hf y).hasDerivAt
    rw [hderiv y hy] at h
    exact h.hasDerivWithinAt
  split_ifs with hx0
  · exact constant_of_has_deriv_right_zero hf.continuous.continuousOn
      (fun y hy => hd y (hy.1.trans (le_abs_self y))) x
      ⟨by rwa [abs_of_nonneg hx0] at hx, le_rfl⟩
  · have hxR : x ≤ -R := by
      rw [abs_of_neg (not_le.1 hx0)] at hx
      linarith
    refine (constant_of_has_deriv_right_zero hf.continuous.continuousOn
      (fun y hy => hd y ?_) (-R) ⟨hxR, le_rfl⟩).symm
    rw [abs_of_neg (by linarith [hy.2] : y < 0)]
    linarith [hy.2]

/-- A differentiable function whose derivative vanishes for `R ≤ |x|` is bounded. -/
lemma exists_bound_of_deriv_eq_zero {f : ℝ → ℝ} {R : ℝ} (hR : 0 ≤ R)
    (hf : Differentiable ℝ f) (hderiv : ∀ x, R ≤ |x| → deriv f x = 0) :
    ∃ M, ∀ x, |f x| ≤ M := by
  have hne : (Icc (-R) R).Nonempty := ⟨0, by simp [hR]⟩
  obtain ⟨x0, hx0, hmax⟩ :=
    isCompact_Icc.exists_isMaxOn hne (hf.continuous.continuousOn.abs)
  refine ⟨|f x0|, fun x => ?_⟩
  by_cases hx : |x| ≤ R
  · exact hmax (mem_Icc.2 ⟨by linarith [abs_le.1 hx], by linarith [abs_le.1 hx]⟩)
  · have hx' : R ≤ |x| := le_of_not_ge hx
    have heq := eq_endpoint_of_deriv_eq_zero hR hf hderiv hx'
    by_cases hxs : 0 ≤ x
    · rw [heq]
      simp only [hxs, ite_true]
      exact hmax ⟨by linarith, le_rfl⟩
    · rw [heq]
      simp only [hxs, ite_false]
      exact hmax ⟨le_rfl, by linarith⟩

end CKMA
