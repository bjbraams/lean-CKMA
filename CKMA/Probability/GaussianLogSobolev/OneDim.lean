/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.HasLaw
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# One-dimensional Gaussian integration by parts

The standard normal density satisfies `ρ' = -x ρ`. For a `C¹` integrand with bounded value and
derivative, the boundary terms vanish and `∫ x ψ ∂γ = ∫ ψ' ∂γ`.
-/

@[expose] public section

noncomputable section

namespace CKMA

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal Real RealInnerProductSpace

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

/-- A continuous function bounded by a constant is integrable on a finite measure space. -/
lemma integrable_of_abs_le {E : Type*} [MeasurableSpace E] {μ : Measure E}
    [IsFiniteMeasure μ] {f : E → ℝ} (hf : AEStronglyMeasurable f μ) {M : ℝ}
    (hM : ∀ x, |f x| ≤ M) : Integrable f μ := by
  refine Integrable.mono' (integrable_const (|M|)) hf ?_
  filter_upwards with x
  rw [Real.norm_eq_abs]
  exact (hM x).trans (le_abs_self M)

/-- A function with vanishing derivative outside a compact interval equals its endpoint value. -/
lemma eq_endpoint_of_deriv_eq_zero {f : ℝ → ℝ} {R : ℝ} (hR : 0 ≤ R)
    (hf : Differentiable ℝ f) (hderiv : ∀ x, R ≤ |x| → deriv f x = 0)
    {x : ℝ} (hx : R ≤ |x|) :
    f x = f (if 0 ≤ x then R else -R) := by
  by_cases hx0 : 0 ≤ x
  · have hxR : R ≤ x := by
      rw [abs_of_nonneg hx0] at hx
      exact hx
    simp only [hx0, ite_true]
    rcases hxR.eq_or_lt with rfl | hxlt
    · rfl
    · obtain ⟨c, hc, hslope⟩ :=
        exists_deriv_eq_slope f hxlt hf.continuous.continuousOn hf.differentiableOn
      have hcabs : R ≤ |c| := by
        have hc0 : 0 ≤ c := le_trans hR hc.1.le
        rw [abs_of_nonneg hc0]
        exact hc.1.le
      have hslope' : (f x - f R) / (x - R) = 0 := by
        rw [hderiv c hcabs] at hslope
        exact hslope.symm
      rw [div_eq_zero_iff] at hslope'
      rcases hslope' with h | h
      · linarith
      · linarith
  · have hx0' : x < 0 := lt_of_not_ge hx0
    have hxR : x ≤ -R := by
      rw [abs_of_neg hx0'] at hx
      linarith
    simp only [hx0, ite_false]
    rcases hxR.eq_or_lt with rfl | hxlt
    · rfl
    · obtain ⟨c, hc, hslope⟩ :=
        exists_deriv_eq_slope f hxlt hf.continuous.continuousOn hf.differentiableOn
      have hcabs : R ≤ |c| := by
        have hc0 : c < 0 := lt_of_lt_of_le hc.2 (neg_nonpos.2 hR)
        rw [abs_of_neg hc0]
        have : -R ≥ c := hc.2.le
        linarith
      have hslope' : (f (-R) - f x) / (-R - x) = 0 := by
        rw [hderiv c hcabs] at hslope
        exact hslope.symm
      rw [div_eq_zero_iff] at hslope'
      rcases hslope' with h | h
      · linarith
      · linarith

/-- A differentiable function whose derivative vanishes at infinity is bounded. -/
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

/-- Mehler scale factor `e^{-t}` of the Ornstein–Uhlenbeck semigroup. -/
def ouScale (t : ℝ) : ℝ := Real.exp (-t)

/-- Mehler width `√(1 - e^{-2t})` of the Ornstein–Uhlenbeck semigroup. -/
def ouStdev (t : ℝ) : ℝ := Real.sqrt (1 - Real.exp (-(2 * t)))

/-- Square of the Mehler scale. -/
lemma ouScale_sq (t : ℝ) : ouScale t ^ 2 = Real.exp (-(2 * t)) := by
  unfold ouScale
  rw [sq, ← Real.exp_add]
  congr 1
  ring

/-- The Mehler coefficients lie on the unit circle for nonnegative time. -/
lemma ouScale_sq_add_ouStdev_sq {t : ℝ} (ht : 0 ≤ t) :
    ouScale t ^ 2 + ouStdev t ^ 2 = 1 := by
  have hnonneg : 0 ≤ 1 - ouScale t ^ 2 := by
    rw [ouScale_sq]
    have hle : Real.exp (-(2 * t)) ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith)
    rw [Real.exp_zero] at hle
    linarith
  unfold ouStdev
  rw [← ouScale_sq, Real.sq_sqrt hnonneg]
  ring

/-- The Mehler width is positive for positive time. -/
lemma ouStdev_pos {t : ℝ} (ht : 0 < t) : 0 < ouStdev t := by
  unfold ouStdev
  rw [Real.sqrt_pos]
  have hlt : Real.exp (-(2 * t)) < Real.exp 0 := Real.exp_lt_exp.mpr (by linarith)
  rw [Real.exp_zero] at hlt
  linarith

/-- Derivative of the Mehler scale. -/
lemma hasDerivAt_ouScale (t : ℝ) : HasDerivAt ouScale (-ouScale t) t := by
  unfold ouScale
  have hid : HasDerivAt (fun s : ℝ => -s) (-1) t := (hasDerivAt_id t).neg.congr_deriv (by ring)
  exact hid.exp.congr_deriv (by ring)

/-- Derivative of the Mehler width. -/
lemma hasDerivAt_ouStdev {t : ℝ} (ht : 0 < t) :
    HasDerivAt ouStdev (ouScale t ^ 2 / ouStdev t) t := by
  have hu : HasDerivAt (fun s => 1 - Real.exp (-(2 * s))) (2 * ouScale t ^ 2) t := by
    have hid : HasDerivAt (fun s : ℝ => -(2 * s)) (-2) t := by
      refine ((hasDerivAt_id t).const_mul (2 : ℝ)).neg.congr_deriv ?_
      ring
    refine ((hasDerivAt_const t (1 : ℝ)).sub hid.exp).congr_deriv ?_
    rw [ouScale_sq]
    ring
  have hne : (1 - Real.exp (-(2 * t))) ≠ 0 := by
    have hpos : 0 < ouStdev t := ouStdev_pos ht
    unfold ouStdev at hpos
    rw [Real.sqrt_pos] at hpos
    exact hpos.ne'
  unfold ouStdev
  refine hu.sqrt hne |>.congr_deriv ?_
  rw [ouScale_sq]
  have hσ : Real.sqrt (1 - Real.exp (-(2 * t))) ≠ 0 := by
    simpa [ouStdev] using (ouStdev_pos ht).ne'
  field_simp [hσ]

/-- Ornstein–Uhlenbeck semigroup, as a Gaussian average of the Mehler kernel. -/
def ouSemigroup (t : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y, f (ouScale t * x + ouStdev t * y) ∂gaussianReal 0 1

/-- The Mehler kernel preserves the standard Gaussian. -/
lemma hasLaw_ouMehler {t : ℝ} (ht : 0 ≤ t) :
    HasLaw (fun p : ℝ × ℝ => ouScale t * p.1 + ouStdev t * p.2) (gaussianReal 0 1)
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
  let γ : Measure ℝ := gaussianReal 0 1
  have hX : HasLaw Prod.fst γ (γ.prod γ) := measurePreserving_fst.hasLaw
  have hY : HasLaw Prod.snd γ (γ.prod γ) := measurePreserving_snd.hasLaw
  have hi : IndepFun Prod.fst Prod.snd (γ.prod γ) := by
    simpa using indepFun_prod (μ := γ) (ν := γ) (X := id) (Y := id)
      measurable_id measurable_id
  have hXs := gaussianReal_const_mul hX (ouScale t)
  have hYs := gaussianReal_const_mul hY (ouStdev t)
  have hi' : IndepFun (fun p : ℝ × ℝ => ouScale t * p.1)
      (fun p : ℝ × ℝ => ouStdev t * p.2) (γ.prod γ) := by
    simpa [Function.comp_def] using
      hi.comp (measurable_const_mul (ouScale t)) (measurable_const_mul (ouStdev t))
  have hmap := gaussianReal_add_gaussianReal_of_indepFun hi' hXs hYs
  simp only [mul_zero, add_zero, mul_one] at hmap
  have hvar : NNReal.mk (ouScale t ^ 2) (sq_nonneg _) +
      NNReal.mk (ouStdev t ^ 2) (sq_nonneg _) = 1 := by
    apply NNReal.coe_injective
    simpa [NNReal.coe_add, NNReal.coe_mk, NNReal.coe_one] using
      ouScale_sq_add_ouStdev_sq ht
  rw [hvar] at hmap
  have hfun : (fun p : ℝ × ℝ => ouScale t * p.1) + (fun p => ouStdev t * p.2) =
      fun p => ouScale t * p.1 + ouStdev t * p.2 := rfl
  rw [hfun] at hmap
  exact ⟨by fun_prop, hmap⟩

/-- The Ornstein–Uhlenbeck semigroup preserves integrals of bounded continuous functions. -/
lemma integral_ouSemigroup {f : ℝ → ℝ} {t : ℝ} (ht : 0 ≤ t) (hf : Continuous f)
    (hM : ∃ M, ∀ x, |f x| ≤ M) :
    ∫ x, ouSemigroup t f x ∂gaussianReal 0 1 = ∫ x, f x ∂gaussianReal 0 1 := by
  obtain ⟨M, hM⟩ := hM
  let γ : Measure ℝ := gaussianReal 0 1
  let F : ℝ × ℝ → ℝ := fun p => f (ouScale t * p.1 + ouStdev t * p.2)
  have hF_int : Integrable F (γ.prod γ) := by
    refine integrable_of_abs_le (by fun_prop) (M := M) ?_
    intro p
    exact hM _
  have hlaw := hasLaw_ouMehler (t := t) ht
  have hint : ∫ p, F p ∂γ.prod γ = ∫ x, f x ∂γ := by
    dsimp only [γ] at hlaw ⊢
    have hfmap : AEStronglyMeasurable f
        (((gaussianReal 0 1).prod (gaussianReal 0 1)).map
          (fun p => ouScale t * p.1 + ouStdev t * p.2)) := by
      rw [hlaw.map_eq]
      exact hf.aestronglyMeasurable
    have hcomp : F = f ∘ fun p => ouScale t * p.1 + ouStdev t * p.2 := rfl
    rw [hcomp]
    simp only [Function.comp_def]
    rw [← integral_map hlaw.aemeasurable hfmap, hlaw.map_eq]
  calc ∫ x, ouSemigroup t f x ∂γ
      = ∫ x, ∫ y, F (x, y) ∂γ ∂γ := by simp [ouSemigroup, F, γ]
    _ = ∫ p, F p ∂γ.prod γ := (integral_prod F hF_int).symm
    _ = ∫ x, f x ∂γ := hint

/-- The identity is integrable for the standard Gaussian. -/
lemma integrable_id_gaussianReal : Integrable id (gaussianReal 0 1) :=
  memLp_one_iff_integrable.mp (memLp_id_gaussianReal (μ := 0) (v := 1) 1)

/-- Absolute value is integrable for the standard Gaussian. -/
lemma integrable_abs_gaussianReal : Integrable (fun x : ℝ => |x|) (gaussianReal 0 1) := by
  simpa [Real.norm_eq_abs] using integrable_id_gaussianReal.norm

/-- Spatial derivative of the Mehler argument. -/
lemma hasDerivAt_mehler_space (t y z : ℝ) :
    HasDerivAt (fun x => ouScale t * x + ouStdev t * y) (ouScale t) z := by
  simpa using ((hasDerivAt_id z).const_mul (ouScale t)).add_const (ouStdev t * y)

/-- Time derivative of the Mehler argument. -/
lemma hasDerivAt_mehler_time {t x y : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => ouScale s * x + ouStdev s * y)
      (-ouScale t * x + (ouScale t ^ 2 / ouStdev t) * y) t := by
  refine (((hasDerivAt_ouScale t).mul_const x).add
    ((hasDerivAt_ouStdev ht).mul_const y)).congr_deriv ?_
  ring

/-- Space derivative of the Ornstein–Uhlenbeck semigroup. -/
lemma hasDerivAt_ouSemigroup_space {f : ℝ → ℝ} {t x : ℝ} (hf : ContDiff ℝ 1 f)
    (hB : ∃ B, ∀ y, |deriv f y| ≤ B) (hM : ∃ M, ∀ y, |f y| ≤ M) :
    HasDerivAt (ouSemigroup t f) (ouScale t * ouSemigroup t (deriv f) x) x := by
  obtain ⟨B, hB⟩ := hB
  obtain ⟨M, hM⟩ := hM
  let γ : Measure ℝ := gaussianReal 0 1
  let α : ℝ := ouScale t
  let σ : ℝ := ouStdev t
  let F : ℝ → ℝ → ℝ := fun z y => f (α * z + σ * y)
  let F' : ℝ → ℝ → ℝ := fun z y => deriv f (α * z + σ * y) * α
  let bound : ℝ → ℝ := fun _ => |B| * |α|
  have hmeas : ∀ z, AEStronglyMeasurable (F z) γ := by
    intro z
    have hcont : Continuous (fun y => α * z + σ * y) := by fun_prop
    exact (hf.continuous.comp hcont).aestronglyMeasurable
  have hF_int : Integrable (F x) γ :=
    integrable_of_abs_le (hmeas x) (M := M) (fun y => hM _)
  have hF'_meas : AEStronglyMeasurable (F' x) γ := by
    have hcont : Continuous (fun y => deriv f (α * x + σ * y) * α) := by
      exact ((hf.continuous_deriv_one.comp (by fun_prop)).mul continuous_const)
    exact hcont.aestronglyMeasurable
  have h_bound : ∀ᵐ y ∂γ, ∀ z ∈ univ, ‖F' z y‖ ≤ bound y := by
    refine ae_of_all _ fun y z _ => ?_
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right ((hB _).trans (le_abs_self B)) (abs_nonneg α)
  have h_diff : ∀ᵐ y ∂γ, ∀ z ∈ univ, HasDerivAt (F · y) (F' z y) z := by
    refine ae_of_all _ fun y z _ => ?_
    have houter : HasDerivAt f (deriv f (α * z + σ * y)) (α * z + σ * y) :=
      ((hf.differentiable one_ne_zero) _).hasDerivAt
    have hcomp := houter.comp z (hasDerivAt_mehler_space t y z)
    exact hcomp.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq (by funext w; rfl))
  have hbound_int : Integrable bound γ := integrable_const _
  have hderiv := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := γ) (F := F) (F' := F') (bound := bound) (x₀ := x) (s := univ)
    Filter.univ_mem (Filter.Eventually.of_forall hmeas) hF_int hF'_meas h_bound hbound_int h_diff
  have hint : ∫ y, F' x y ∂γ = α * ouSemigroup t (deriv f) x := by
    simp only [F']
    rw [integral_mul_const]
    rw [mul_comm]
    simp only [ouSemigroup, α, σ, γ]
  unfold ouSemigroup
  exact hderiv.2.congr_deriv hint

/-- Real form of the semigroup space derivative. -/
lemma deriv_ouSemigroup_space {f : ℝ → ℝ} {t x : ℝ} (hf : ContDiff ℝ 1 f)
    (hB : ∃ B, ∀ y, |deriv f y| ≤ B) (hM : ∃ M, ∀ y, |f y| ≤ M) :
    deriv (ouSemigroup t f) x = ouScale t * ouSemigroup t (deriv f) x :=
  (hasDerivAt_ouSemigroup_space hf hB hM).deriv

/-- Time derivative of the Ornstein–Uhlenbeck semigroup at positive time. -/
lemma hasDerivAt_ouSemigroup_time {f : ℝ → ℝ} {t x : ℝ} (ht : 0 < t) (hf : ContDiff ℝ 1 f)
    (hB : ∃ B, ∀ y, |deriv f y| ≤ B) (hM : ∃ M, ∀ y, |f y| ≤ M) :
    HasDerivAt (fun s => ouSemigroup s f x)
      (∫ y, deriv f (ouScale t * x + ouStdev t * y) *
        (-ouScale t * x + (ouScale t ^ 2 / ouStdev t) * y) ∂gaussianReal 0 1) t := by
  obtain ⟨B, hB⟩ := hB
  obtain ⟨M, hM⟩ := hM
  let γ : Measure ℝ := gaussianReal 0 1
  let sset : Set ℝ := Ioo (t / 2) (t + 1)
  have hs : sset ∈ nhds t := Ioo_mem_nhds (by linarith) (by linarith)
  have hσ0 : 0 < ouStdev (t / 2) := ouStdev_pos (by linarith : 0 < t / 2)
  let C : ℝ := 1 / ouStdev (t / 2)
  let F : ℝ → ℝ → ℝ := fun s y => f (ouScale s * x + ouStdev s * y)
  let F' : ℝ → ℝ → ℝ := fun s y =>
    deriv f (ouScale s * x + ouStdev s * y) *
      (-ouScale s * x + (ouScale s ^ 2 / ouStdev s) * y)
  let bound : ℝ → ℝ := fun y => |B| * (|x| + C * |y|)
  have hmeas : ∀ s, AEStronglyMeasurable (F s) γ := by
    intro s
    have hcont : Continuous (fun y => ouScale s * x + ouStdev s * y) := by fun_prop
    exact (hf.continuous.comp hcont).aestronglyMeasurable
  have hF_int : Integrable (F t) γ :=
    integrable_of_abs_le (hmeas t) (M := M) (fun y => hM _)
  have hF'_meas : AEStronglyMeasurable (F' t) γ := by
    have hcont : Continuous (F' t) := by
      refine ((hf.continuous_deriv_one.comp (by fun_prop)).mul (by fun_prop))
    exact hcont.aestronglyMeasurable
  have h_bound : ∀ᵐ y ∂γ, ∀ s ∈ sset, ‖F' s y‖ ≤ bound y := by
    refine ae_of_all _ fun y s hs => ?_
    have hs1 : t / 2 < s := hs.1
    have hs0 : 0 < s := by linarith
    have hσmono : ouStdev (t / 2) ≤ ouStdev s := by
      unfold ouStdev
      refine Real.sqrt_le_sqrt ?_
      have hexp : Real.exp (-(2 * s)) ≤ Real.exp (-(2 * (t / 2))) :=
        Real.exp_le_exp.mpr (by linarith)
      linarith
    have hαle : ouScale s ≤ 1 := by
      unfold ouScale
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by linarith)
    have hα0 : 0 ≤ ouScale s := le_of_lt (Real.exp_pos _)
    have hσpos : 0 < ouStdev s := ouStdev_pos hs0
    have hquot : ouScale s ^ 2 / ouStdev s ≤ C := by
      have hαsq : ouScale s ^ 2 ≤ 1 := by nlinarith [hαle, hα0]
      have hden : 1 / ouStdev s ≤ C := by
        unfold C
        exact one_div_le_one_div_of_le hσ0 hσmono
      exact (div_le_div_of_nonneg_right hαsq (le_of_lt hσpos)).trans hden
    rw [Real.norm_eq_abs, abs_mul]
    have hinner : |-ouScale s * x + (ouScale s ^ 2 / ouStdev s) * y| ≤ |x| + C * |y| := by
      have hsplit := abs_add_le (-ouScale s * x) ((ouScale s ^ 2 / ouStdev s) * y)
      have habs : |-ouScale s * x| + |(ouScale s ^ 2 / ouStdev s) * y| =
          ouScale s * |x| + (ouScale s ^ 2 / ouStdev s) * |y| := by
        have hleft : |-ouScale s * x| = ouScale s * |x| := by
          rw [abs_mul, abs_neg, abs_of_nonneg hα0]
        have hright : |(ouScale s ^ 2 / ouStdev s) * y| =
            (ouScale s ^ 2 / ouStdev s) * |y| := by
          rw [abs_mul, abs_of_nonneg (div_nonneg (sq_nonneg _) (le_of_lt hσpos))]
        rw [hleft, hright]
      have hαx : ouScale s * |x| ≤ |x| := by
        have := mul_le_mul_of_nonneg_right hαle (abs_nonneg x)
        simpa using this
      have hCy : (ouScale s ^ 2 / ouStdev s) * |y| ≤ C * |y| :=
        mul_le_mul_of_nonneg_right hquot (abs_nonneg y)
      linarith
    exact mul_le_mul ((hB _).trans (le_abs_self B)) hinner (abs_nonneg _) (abs_nonneg B)
  have hbound_int : Integrable bound γ := by
    have hsum : Integrable (fun y => |B| * |x| + (|B| * C) * |y|) γ :=
      (integrable_const _).add (integrable_abs_gaussianReal.const_mul (|B| * C))
    refine hsum.congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [bound]
    ring
  have h_diff : ∀ᵐ y ∂γ, ∀ s ∈ sset, HasDerivAt (F · y) (F' s y) s := by
    refine ae_of_all _ fun y s hs => ?_
    have hs0 : 0 < s := by
      have : t / 2 < s := hs.1
      linarith
    have houter : HasDerivAt f (deriv f (ouScale s * x + ouStdev s * y))
        (ouScale s * x + ouStdev s * y) :=
      ((hf.differentiable one_ne_zero) _).hasDerivAt
    have hcomp := houter.comp s (hasDerivAt_mehler_time hs0)
    exact hcomp.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq (by funext w; rfl))
  have hderiv := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := γ) (F := F) (F' := F') (bound := bound) (x₀ := t) (s := sset)
    hs (Filter.Eventually.of_forall hmeas) hF_int hF'_meas h_bound hbound_int h_diff
  unfold ouSemigroup
  have hAt : HasDerivAt (fun s => ∫ y, f (ouScale s * x + ouStdev s * y) ∂γ)
      (∫ y, F' t y ∂γ) t := hderiv.2
  simpa [F', γ] using hAt

/-- Real form of the semigroup time derivative. -/
lemma deriv_ouSemigroup_time {f : ℝ → ℝ} {t x : ℝ} (ht : 0 < t) (hf : ContDiff ℝ 1 f)
    (hB : ∃ B, ∀ y, |deriv f y| ≤ B) (hM : ∃ M, ∀ y, |f y| ≤ M) :
    deriv (fun s => ouSemigroup s f x) t =
      ∫ y, deriv f (ouScale t * x + ouStdev t * y) *
        (-ouScale t * x + (ouScale t ^ 2 / ouStdev t) * y) ∂gaussianReal 0 1 :=
  (hasDerivAt_ouSemigroup_time (x := x) ht hf hB hM).deriv

/-- The Mehler scale is nonnegative. -/
lemma ouScale_nonneg (t : ℝ) : 0 ≤ ouScale t := le_of_lt (Real.exp_pos _)

/-- The Mehler scale is at most one for nonnegative time. -/
lemma ouScale_le_one {t : ℝ} (ht : 0 ≤ t) : ouScale t ≤ 1 := by
  unfold ouScale
  rw [← Real.exp_zero]
  exact Real.exp_le_exp.mpr (by linarith)

/-- A bounded continuous function has a continuous Ornstein–Uhlenbeck semigroup. -/
lemma continuous_ouSemigroup {f : ℝ → ℝ} {t : ℝ} (hf : Continuous f)
    (hM : ∃ M, ∀ x, |f x| ≤ M) : Continuous (ouSemigroup t f) := by
  obtain ⟨M, hM⟩ := hM
  let γ : Measure ℝ := gaussianReal 0 1
  have hcont := continuous_of_dominated (μ := γ)
    (F := fun z y => f (ouScale t * z + ouStdev t * y)) (bound := fun _ => |M|)
    (fun z => (hf.comp (by fun_prop)).aestronglyMeasurable)
    (fun z => ae_of_all _ fun y => by
      rw [Real.norm_eq_abs]
      exact (hM _).trans (le_abs_self M))
    (integrable_const _)
    (ae_of_all _ fun y => hf.comp (by fun_prop))
  unfold ouSemigroup
  exact hcont

/-- Constant lower bounds pass to the Ornstein–Uhlenbeck semigroup. -/
lemma ouSemigroup_lower {f : ℝ → ℝ} {t x δ : ℝ} (hf : Continuous f)
    (hM : ∃ M, ∀ y, |f y| ≤ M) (hδ : ∀ y, δ ≤ f y) : δ ≤ ouSemigroup t f x := by
  obtain ⟨M, hM⟩ := hM
  let γ : Measure ℝ := gaussianReal 0 1
  have hint : Integrable (fun y => f (ouScale t * x + ouStdev t * y)) γ :=
    integrable_of_abs_le ((hf.comp (by fun_prop)).aestronglyMeasurable) (M := M) (fun y => hM _)
  have hconst : Integrable (fun _ : ℝ => δ) γ := integrable_const _
  have hmono := integral_mono hconst hint (fun y => hδ _)
  have hconst_int : ∫ y, δ ∂γ = δ := by
    rw [integral_const]
    simp [probReal_univ, smul_eq_mul]
  rw [← hconst_int]
  simpa [ouSemigroup, γ] using hmono

/-- Derivative of a differentiable function along the Mehler noise coordinate. -/
lemma deriv_mehler_comp {g : ℝ → ℝ} {t x y : ℝ} (hg : Differentiable ℝ g) :
    deriv (fun z => g (ouScale t * x + ouStdev t * z)) y =
      deriv g (ouScale t * x + ouStdev t * y) * ouStdev t := by
  have hinner : HasDerivAt (fun z => ouScale t * x + ouStdev t * z) (ouStdev t) y := by
    simpa using ((hasDerivAt_id y).const_mul (ouStdev t)).add_const (ouScale t * x)
  have houter : HasDerivAt g (deriv g (ouScale t * x + ouStdev t * y))
      (ouScale t * x + ouStdev t * y) := (hg _).hasDerivAt
  exact ((houter.comp y hinner).congr_of_eventuallyEq
    (Filter.EventuallyEq.of_eq (by funext w; rfl))).deriv

/-- A `C²` function is `C¹`, with a `C¹` derivative. -/
lemma contDiff_one_deriv_of_two {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) :
    ContDiff ℝ 1 f ∧ ContDiff ℝ 1 (deriv f) := by
  refine ⟨hf.of_le (by decide : (1 : WithTop ℕ∞) ≤ 2), ?_⟩
  have h : ContDiff ℝ ((1 : WithTop ℕ∞) + 1) f := by
    convert hf using 2
    norm_num
  exact h.deriv'

/-- Second space derivative of the Ornstein–Uhlenbeck semigroup. -/
lemma deriv_ouSemigroup_space₂ {f : ℝ → ℝ} {t x : ℝ} (hf : ContDiff ℝ 2 f)
    (hB : ∃ B, ∀ y, |deriv f y| ≤ B) (hB2 : ∃ B, ∀ y, |deriv (deriv f) y| ≤ B)
    (hM : ∃ M, ∀ y, |f y| ≤ M) :
    deriv (deriv (ouSemigroup t f)) x =
      ouScale t ^ 2 * ouSemigroup t (deriv (deriv f)) x := by
  obtain ⟨hf1, hf'1⟩ := contDiff_one_deriv_of_two hf
  have hfun : deriv (ouSemigroup t f) =
      fun z => ouScale t * ouSemigroup t (deriv f) z :=
    funext fun z => deriv_ouSemigroup_space hf1 hB hM
  rw [hfun, deriv_const_mul_field]
  have h2 := deriv_ouSemigroup_space (f := deriv f) (t := t) (x := x) hf'1 hB2 hB
  rw [h2]
  ring

/-- The semigroup satisfies the Ornstein–Uhlenbeck equation `∂t u = ∂xx u - x ∂x u`. -/
lemma deriv_ouSemigroup_eq_generator {f : ℝ → ℝ} {t x : ℝ} (ht : 0 < t)
    (hf : ContDiff ℝ 2 f) (hB : ∃ B, ∀ y, |deriv f y| ≤ B)
    (hB2 : ∃ B, ∀ y, |deriv (deriv f) y| ≤ B) (hM : ∃ M, ∀ y, |f y| ≤ M) :
    deriv (fun s => ouSemigroup s f x) t =
      deriv (deriv (ouSemigroup t f)) x - x * deriv (ouSemigroup t f) x := by
  obtain ⟨B, hB⟩ := hB
  obtain ⟨B2, hB2⟩ := hB2
  obtain ⟨M, hM⟩ := hM
  obtain ⟨hf1, hf'1⟩ := contDiff_one_deriv_of_two hf
  let γ : Measure ℝ := gaussianReal 0 1
  let α : ℝ := ouScale t
  let σ : ℝ := ouStdev t
  let ψ : ℝ → ℝ := fun y => deriv f (α * x + σ * y)
  have hσne : σ ≠ 0 := (ouStdev_pos ht).ne'
  have hψ_diff : Differentiable ℝ ψ := by
    intro y
    have hinner : DifferentiableAt ℝ (fun z => α * x + σ * z) y := by
      simpa using ((differentiableAt_id.const_mul σ).const_add (α * x))
    exact ((((hf'1.differentiable one_ne_zero) (α * x + σ * y)).comp y
      hinner)).congr_of_eventuallyEq (Filter.EventuallyEq.of_eq (by funext w; rfl))
  have hψ_deriv : ∀ y, deriv ψ y = deriv (deriv f) (α * x + σ * y) * σ := by
    intro y
    simpa [ψ, α, σ] using deriv_mehler_comp (g := deriv f)
      (hg := hf'1.differentiable one_ne_zero) (t := t) (x := x) (y := y)
  have hψ'_cont : Continuous (deriv ψ) := by
    rw [funext hψ_deriv]
    exact ((hf'1.continuous_deriv_one.comp (by fun_prop)).mul continuous_const)
  have hψ_bdd : ∃ C, ∀ y, |ψ y| ≤ C := ⟨B, fun y => hB _⟩
  have hψ'_bdd : ∃ C, ∀ y, |deriv ψ y| ≤ C := by
    refine ⟨|B2| * |σ|, fun y => ?_⟩
    rw [hψ_deriv, abs_mul]
    exact mul_le_mul_of_nonneg_right ((hB2 _).trans (le_abs_self B2)) (abs_nonneg _)
  have hip := integral_id_mul_eq_integral_deriv_gaussianReal hψ_diff hψ'_cont hψ_bdd hψ'_bdd
  have hψ_int : Integrable ψ γ :=
    integrable_of_abs_le hψ_diff.continuous.aestronglyMeasurable (M := B) (fun y => hB _)
  have hyψ_int : Integrable (fun y => y * ψ y) γ := by
    refine Integrable.mono' (integrable_abs_gaussianReal.const_mul (|B| + 1))
      ((continuous_id.mul hψ_diff.continuous).aestronglyMeasurable) ?_
    filter_upwards with y
    rw [Real.norm_eq_abs, abs_mul]
    calc |y| * |ψ y| ≤ |y| * (|B| + 1) := by
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg y)
          exact (hB _).trans ((le_abs_self B).trans (le_add_of_nonneg_right zero_le_one))
      _ = (|B| + 1) * |y| := by ring
  have h1_int : Integrable (fun y => ψ y * (-α * x)) γ := hψ_int.mul_const _
  have h2_int : Integrable (fun y => (α ^ 2 / σ) * (y * ψ y)) γ := hyψ_int.const_mul _
  have hsplit : ∫ y, ψ y * (-α * x + (α ^ 2 / σ) * y) ∂γ =
      (∫ y, ψ y ∂γ) * (-α * x) + (α ^ 2 / σ) * ∫ y, y * ψ y ∂γ := by
    have hfun : (fun y => ψ y * (-α * x + (α ^ 2 / σ) * y)) =
        (fun y => ψ y * (-α * x) + (α ^ 2 / σ) * (y * ψ y)) := by
      funext y; ring
    rw [hfun, integral_add h1_int h2_int, integral_mul_const, integral_const_mul]
  have hderiv_int : ∫ y, deriv ψ y ∂γ =
      σ * ∫ y, deriv (deriv f) (α * x + σ * y) ∂γ := by
    rw [funext hψ_deriv, integral_mul_const, mul_comm]
  have htime := deriv_ouSemigroup_time (x := x) ht hf1 ⟨B, hB⟩ ⟨M, hM⟩
  have htime' : deriv (fun s => ouSemigroup s f x) t =
      (∫ y, ψ y ∂γ) * (-α * x) +
        (α ^ 2 / σ) * (σ * ∫ y, deriv (deriv f) (α * x + σ * y) ∂γ) := by
    rw [htime]
    have hsame : (fun y => deriv f (ouScale t * x + ouStdev t * y) *
          (-ouScale t * x + (ouScale t ^ 2 / ouStdev t) * y)) =
        fun y => ψ y * (-α * x + (α ^ 2 / σ) * y) := by
      funext y; rfl
    rw [hsame, hsplit, hip, hderiv_int]
  have hcoeff : (α ^ 2 / σ) * (σ * ∫ y, deriv (deriv f) (α * x + σ * y) ∂γ) =
      α ^ 2 * ∫ y, deriv (deriv f) (α * x + σ * y) ∂γ := by
    field_simp [hσne]
  have hspace := deriv_ouSemigroup_space (t := t) (x := x) hf1 ⟨B, hB⟩ ⟨M, hM⟩
  have hspace2 := deriv_ouSemigroup_space₂ (t := t) (x := x) hf ⟨B, hB⟩ ⟨B2, hB2⟩ ⟨M, hM⟩
  have hfirst : deriv (ouSemigroup t f) x = α * ∫ y, ψ y ∂γ := by
    rw [hspace]
    simp [ouSemigroup, α, σ, ψ, γ]
  have hsecond : deriv (deriv (ouSemigroup t f)) x =
      α ^ 2 * ∫ y, deriv (deriv f) (α * x + σ * y) ∂γ := by
    rw [hspace2]
    simp [ouSemigroup, α, σ, γ]
  rw [htime', hcoeff, hfirst, hsecond]
  ring

/-- Cauchy–Schwarz for bounded continuous functions against the standard Gaussian. -/
lemma gaussian_cauchy_schwarz {a b : ℝ → ℝ} {A B : ℝ} (ha : Continuous a) (hb : Continuous b)
    (hA : ∀ x, |a x| ≤ A) (hB : ∀ x, |b x| ≤ B) :
    (∫ x, a x * b x ∂gaussianReal 0 1) ^ 2 ≤
      (∫ x, a x ^ 2 ∂gaussianReal 0 1) * (∫ x, b x ^ 2 ∂gaussianReal 0 1) := by
  let γ : Measure ℝ := gaussianReal 0 1
  have haLp : MemLp a 2 γ := MemLp.of_bound ha.aestronglyMeasurable (|A| + 1)
    (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs]
      exact (hA x).trans ((le_abs_self A).trans (le_add_of_nonneg_right zero_le_one)))
  have hbLp : MemLp b 2 γ := MemLp.of_bound hb.aestronglyMeasurable (|B| + 1)
    (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs]
      exact (hB x).trans ((le_abs_self B).trans (le_add_of_nonneg_right zero_le_one)))
  let aL := haLp.toLp a
  let bL := hbLp.toLp b
  have hab : ⟪aL, bL⟫ = ∫ x, a x * b x ∂γ := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [haLp.coeFn_toLp, hbLp.coeFn_toLp] with x hae hbe
    simp [aL, bL, hae, hbe]
    ring
  have ha2 : ⟪aL, aL⟫ = ∫ x, a x ^ 2 ∂γ := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [haLp.coeFn_toLp] with x hae
    simp [aL, hae, sq]
  have hb2 : ⟪bL, bL⟫ = ∫ x, b x ^ 2 ∂γ := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hbLp.coeFn_toLp] with x hbe
    simp [bL, hbe, sq]
  have hcs := abs_real_inner_le_norm aL bL
  have hineq : ⟪aL, bL⟫ ^ 2 ≤ (‖aL‖ * ‖bL‖) ^ 2 :=
    sq_le_sq' (neg_le_of_abs_le hcs) (le_of_abs_le hcs)
  rw [hab, mul_pow, ← real_inner_self_eq_norm_sq aL, ← real_inner_self_eq_norm_sq bL, ha2,
    hb2] at hineq
  simpa [γ] using hineq

/-- Constant upper bounds pass to the Ornstein–Uhlenbeck semigroup. -/
lemma ouSemigroup_upper {f : ℝ → ℝ} {t x M : ℝ} (hf : Continuous f)
    (hbd : ∃ C, ∀ y, |f y| ≤ C) (hM : ∀ y, f y ≤ M) : ouSemigroup t f x ≤ M := by
  obtain ⟨C, hC⟩ := hbd
  let γ : Measure ℝ := gaussianReal 0 1
  have hint : Integrable (fun y => f (ouScale t * x + ouStdev t * y)) γ :=
    integrable_of_abs_le ((hf.comp (by fun_prop)).aestronglyMeasurable) (M := C) (fun y => hC _)
  have hconst : Integrable (fun _ : ℝ => M) γ := integrable_const _
  have hmono := integral_mono hint hconst (fun y => hM _)
  have hconst_int : ∫ y, M ∂γ = M := by
    rw [integral_const]
    simp [probReal_univ, smul_eq_mul]
  rw [← hconst_int]
  simpa [ouSemigroup, γ] using hmono

/-- Logarithmic derivative of the Ornstein–Uhlenbeck semigroup at positive time. -/
lemma hasDerivAt_ouSemigroup_mul_log {f : ℝ → ℝ} {t x δ : ℝ} (ht : 0 < t)
    (hf : ContDiff ℝ 1 f) (hB : ∃ B, ∀ y, |deriv f y| ≤ B) (hM : ∃ M, ∀ y, |f y| ≤ M)
    (hδ : 0 < δ) (hδf : ∀ y, δ ≤ f y) :
    HasDerivAt (fun s => ouSemigroup s f x * Real.log (ouSemigroup s f x))
      ((deriv (fun s => ouSemigroup s f x) t) * (Real.log (ouSemigroup t f x) + 1)) t := by
  have hU0 := hasDerivAt_ouSemigroup_time (x := x) ht hf hB hM
  have hU := hU0.congr_deriv hU0.deriv.symm
  have hpos : 0 < ouSemigroup t f x :=
    lt_of_lt_of_le hδ (ouSemigroup_lower hf.continuous hM hδf)
  have hlog := hU.log hpos.ne'
  refine (hU.mul hlog).congr_deriv ?_
  field_simp [hpos.ne']

/-- The Mehler time velocity is linearly bounded for times at least `t0`. -/
lemma abs_mehler_velocity_le {s t0 x y : ℝ} (ht0 : 0 < t0) (hs : t0 ≤ s) :
    |-ouScale s * x + (ouScale s ^ 2 / ouStdev s) * y| ≤
      |x| + (1 / ouStdev t0) * |y| := by
  have hs0 : 0 < s := lt_of_lt_of_le ht0 hs
  have hσmono : ouStdev t0 ≤ ouStdev s := by
    unfold ouStdev
    refine Real.sqrt_le_sqrt ?_
    have hexp : Real.exp (-(2 * s)) ≤ Real.exp (-(2 * t0)) :=
      Real.exp_le_exp.mpr (by linarith)
    linarith
  have hαle : ouScale s ≤ 1 := ouScale_le_one (le_of_lt hs0)
  have hα0 : 0 ≤ ouScale s := ouScale_nonneg s
  have hσpos : 0 < ouStdev s := ouStdev_pos hs0
  have hσ0 : 0 < ouStdev t0 := ouStdev_pos ht0
  let C : ℝ := 1 / ouStdev t0
  have hquot : ouScale s ^ 2 / ouStdev s ≤ C := by
    have hαsq : ouScale s ^ 2 ≤ 1 := by nlinarith [hαle, hα0]
    have hden : 1 / ouStdev s ≤ C := one_div_le_one_div_of_le hσ0 hσmono
    exact (div_le_div_of_nonneg_right hαsq (le_of_lt hσpos)).trans hden
  have hsplit := abs_add_le (-ouScale s * x) ((ouScale s ^ 2 / ouStdev s) * y)
  have habs : |-ouScale s * x| + |(ouScale s ^ 2 / ouStdev s) * y| =
      ouScale s * |x| + (ouScale s ^ 2 / ouStdev s) * |y| := by
    have hleft : |-ouScale s * x| = ouScale s * |x| := by
      rw [abs_mul, abs_neg, abs_of_nonneg hα0]
    have hright : |(ouScale s ^ 2 / ouStdev s) * y| =
        (ouScale s ^ 2 / ouStdev s) * |y| := by
      rw [abs_mul, abs_of_nonneg (div_nonneg (sq_nonneg _) (le_of_lt hσpos))]
    rw [hleft, hright]
  have hαx : ouScale s * |x| ≤ |x| := by
    simpa using mul_le_mul_of_nonneg_right hαle (abs_nonneg x)
  have hCy : (ouScale s ^ 2 / ouStdev s) * |y| ≤ C * |y| :=
    mul_le_mul_of_nonneg_right hquot (abs_nonneg y)
  linarith

/-- Absolute values are preserved by the Ornstein–Uhlenbeck semigroup. -/
lemma abs_ouSemigroup_le {f : ℝ → ℝ} {t x M : ℝ} (hf : Continuous f) (hM : ∀ y, |f y| ≤ M) :
    |ouSemigroup t f x| ≤ M := by
  have hup : ouSemigroup t f x ≤ M :=
    ouSemigroup_upper hf ⟨M, hM⟩ (fun y => (le_abs_self (f y)).trans (hM y))
  have hlow : -M ≤ ouSemigroup t f x := by
    have hδ : ∀ y, -M ≤ f y := fun y => (neg_le_neg (hM y)).trans (neg_abs_le (f y))
    exact ouSemigroup_lower hf ⟨M, hM⟩ hδ
  exact abs_le.mpr ⟨hlow, hup⟩

/-- The time derivative of the Ornstein–Uhlenbeck semigroup grows at most linearly. -/
lemma abs_deriv_ouSemigroup_time_le {f : ℝ → ℝ} {s x t0 B : ℝ} (ht0 : 0 < t0) (hs : t0 ≤ s)
    (hf : ContDiff ℝ 1 f) (hB : ∀ y, |deriv f y| ≤ B) (hM : ∃ M, ∀ y, |f y| ≤ M) :
    |deriv (fun r => ouSemigroup r f x) s| ≤
      |B| * (|x| + (1 / ouStdev t0) * ∫ y, |y| ∂gaussianReal 0 1) := by
  have hs0 : 0 < s := lt_of_lt_of_le ht0 hs
  have hformula := deriv_ouSemigroup_time (x := x) hs0 hf ⟨B, hB⟩ hM
  let γ : Measure ℝ := gaussianReal 0 1
  let C : ℝ := 1 / ouStdev t0
  let integrand : ℝ → ℝ := fun y =>
    deriv f (ouScale s * x + ouStdev s * y) *
      (-ouScale s * x + (ouScale s ^ 2 / ouStdev s) * y)
  have hvel : ∀ y, |integrand y| ≤ |B| * (|x| + C * |y|) := by
    intro y
    rw [abs_mul]
    refine mul_le_mul ((hB _).trans (le_abs_self B)) ?_ (abs_nonneg _) (abs_nonneg B)
    simpa [C] using abs_mehler_velocity_le (x := x) (y := y) ht0 hs
  have hdom : Integrable (fun y => |B| * (|x| + C * |y|)) γ := by
    have hsum : Integrable (fun y => |B| * |x| + (|B| * C) * |y|) γ :=
      (integrable_const _).add (integrable_abs_gaussianReal.const_mul (|B| * C))
    exact hsum.congr (Filter.Eventually.of_forall fun y => by ring)
  have hmeas : AEStronglyMeasurable integrand γ := by
    have hcont : Continuous integrand :=
      (hf.continuous_deriv_one.comp (by fun_prop)).mul (by fun_prop)
    exact hcont.aestronglyMeasurable
  have hint : Integrable integrand γ := by
    refine Integrable.mono' hdom hmeas ?_
    filter_upwards with y
    rw [Real.norm_eq_abs]
    exact hvel y
  have hnorm : |∫ y, integrand y ∂γ| ≤ ∫ y, |integrand y| ∂γ := by
    simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm integrand
  have habs_int : Integrable (fun y => |integrand y|) γ := hint.abs
  have hmono := integral_mono habs_int hdom hvel
  have hsplit : ∫ y, |B| * (|x| + C * |y|) ∂γ =
      |B| * |x| + (|B| * C) * ∫ y, |y| ∂γ := by
    have hfun : (fun y => |B| * (|x| + C * |y|)) =
        fun y => |B| * |x| + (|B| * C) * |y| := by
      funext y; ring
    rw [hfun, integral_add (integrable_const _) (integrable_abs_gaussianReal.const_mul _),
      integral_const, integral_const_mul]
    simp [probReal_univ, smul_eq_mul, γ]
  rw [hformula]
  calc |∫ y, integrand y ∂gaussianReal 0 1|
      = |∫ y, integrand y ∂γ| := by rfl
    _ ≤ ∫ y, |integrand y| ∂γ := hnorm
    _ ≤ ∫ y, |B| * (|x| + C * |y|) ∂γ := hmono
    _ = |B| * |x| + (|B| * C) * ∫ y, |y| ∂γ := hsplit
    _ = |B| * (|x| + C * ∫ y, |y| ∂γ) := by ring

/-- Integration by parts converts the generator action on `log` into Fisher information. -/
lemma integral_generator_mul_log {f : ℝ → ℝ} {t δ : ℝ} (ht : 0 < t) (hf : ContDiff ℝ 2 f)
    (hδ : 0 < δ) (hδf : ∀ y, δ ≤ f y) (hB : ∃ B, ∀ y, |deriv f y| ≤ B)
    (hB2 : ∃ B2, ∀ y, |deriv (deriv f) y| ≤ B2) (hM : ∃ M, ∀ y, |f y| ≤ M) :
    ∫ x, (deriv (fun s => ouSemigroup s f x) t) * Real.log (ouSemigroup t f x)
        ∂gaussianReal 0 1 =
      -∫ x, (deriv (ouSemigroup t f) x) ^ 2 / ouSemigroup t f x ∂gaussianReal 0 1 := by
  obtain ⟨B, hB⟩ := hB
  obtain ⟨B2, hB2⟩ := hB2
  obtain ⟨M, hM⟩ := hM
  obtain ⟨hf1, hf'1⟩ := contDiff_one_deriv_of_two hf
  let γ : Measure ℝ := gaussianReal 0 1
  let u : ℝ → ℝ := ouSemigroup t f
  let α : ℝ := ouScale t
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB 0)
  have hB20 : 0 ≤ B2 := le_trans (abs_nonneg _) (hB2 0)
  have hMpos : 0 < M := lt_of_lt_of_le hδ ((hδf 0).trans ((le_abs_self _).trans (hM 0)))
  have hpos : ∀ x, 0 < u x := fun x =>
    lt_of_lt_of_le hδ (ouSemigroup_lower hf.continuous ⟨M, hM⟩ hδf)
  have hu_le : ∀ x, u x ≤ M := fun x =>
    ouSemigroup_upper hf.continuous ⟨M, hM⟩ (fun y => (le_abs_self (f y)).trans (hM y))
  have hdu : ∀ x, deriv u x = α * ouSemigroup t (deriv f) x := fun x =>
    deriv_ouSemigroup_space (t := t) (x := x) hf1 ⟨B, hB⟩ ⟨M, hM⟩
  have hdu2 : ∀ x, deriv (deriv u) x =
      α ^ 2 * ouSemigroup t (deriv (deriv f)) x := fun x =>
    deriv_ouSemigroup_space₂ (t := t) (x := x) hf ⟨B, hB⟩ ⟨B2, hB2⟩ ⟨M, hM⟩
  have hgen : ∀ x, deriv (fun s => ouSemigroup s f x) t =
      deriv (deriv u) x - x * deriv u x := fun x =>
    deriv_ouSemigroup_eq_generator (x := x) ht hf ⟨B, hB⟩ ⟨B2, hB2⟩ ⟨M, hM⟩
  have hdu_bdd : ∀ x, |deriv u x| ≤ B := by
    intro x
    rw [hdu x, abs_mul, abs_of_nonneg (ouScale_nonneg t)]
    have hα : α ≤ 1 := ouScale_le_one (le_of_lt ht)
    have hP : |ouSemigroup t (deriv f) x| ≤ B :=
      abs_ouSemigroup_le hf1.continuous_deriv_one hB
    have hmul := mul_le_mul hα hP (abs_nonneg _) zero_le_one
    simpa using hmul
  have hdu2_bdd : ∀ x, |deriv (deriv u) x| ≤ B2 := by
    intro x
    rw [hdu2 x, abs_mul, abs_of_nonneg (sq_nonneg α)]
    have hα : α ^ 2 ≤ 1 := by
      have hα1 : α ≤ 1 := ouScale_le_one (le_of_lt ht)
      have hα0 : 0 ≤ α := ouScale_nonneg t
      nlinarith
    have hP : |ouSemigroup t (deriv (deriv f)) x| ≤ B2 :=
      abs_ouSemigroup_le hf'1.continuous_deriv_one hB2
    have hmul := mul_le_mul hα hP (abs_nonneg _) zero_le_one
    simpa using hmul
  have hlog_bdd : ∃ L, ∀ x, |Real.log (u x)| ≤ L := by
    refine ⟨max |Real.log δ| |Real.log M|, fun x => ?_⟩
    have hle1 : Real.log δ ≤ Real.log (u x) :=
      Real.log_le_log hδ (ouSemigroup_lower hf.continuous ⟨M, hM⟩ hδf)
    have hle2 : Real.log (u x) ≤ Real.log M := Real.log_le_log (hpos x) (hu_le x)
    refine abs_le.mpr ⟨?_, ?_⟩
    · have hleft : -max |Real.log δ| |Real.log M| ≤ Real.log δ :=
        (neg_le_neg (le_max_left _ _)).trans (neg_abs_le _)
      exact hleft.trans hle1
    · exact (hle2.trans (le_abs_self _)).trans (le_max_right _ _)
  obtain ⟨L, hL⟩ := hlog_bdd
  let ψ : ℝ → ℝ := fun x => deriv u x * Real.log (u x)
  have hψAt : ∀ x, HasDerivAt ψ
      (deriv (deriv u) x * Real.log (u x) + (deriv u x) ^ 2 / u x) x := by
    intro x
    have huAt : HasDerivAt u (deriv u x) x :=
      (hasDerivAt_ouSemigroup_space hf1 ⟨B, hB⟩ ⟨M, hM⟩).congr_deriv (hdu x).symm
    have hlog := huAt.log (hpos x).ne'
    have hspace := hasDerivAt_ouSemigroup_space (f := deriv f) (t := t) (x := x)
      hf'1 ⟨B2, hB2⟩ ⟨B, hB⟩
    have hmul0 := HasDerivAt.const_mul α hspace
    have hfun : deriv u = fun z => α * ouSemigroup t (deriv f) z := funext hdu
    have hduAt : HasDerivAt (deriv u) (deriv (deriv u) x) x :=
      (hmul0.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq hfun)).congr_deriv (by
        rw [hdu2 x]
        ring)
    refine (hduAt.mul hlog).congr_deriv ?_
    field_simp [(hpos x).ne']
  have hψ_form : deriv ψ = fun x =>
      deriv (deriv u) x * Real.log (u x) + (deriv u x) ^ 2 / u x :=
    funext fun x => (hψAt x).deriv
  have hu_cont : Continuous u := continuous_ouSemigroup hf.continuous ⟨M, hM⟩
  have hdu_cont : Continuous (deriv u) := by
    rw [funext hdu]
    exact continuous_const.mul (continuous_ouSemigroup hf1.continuous_deriv_one ⟨B, hB⟩)
  have hdu2_cont : Continuous (deriv (deriv u)) := by
    rw [funext hdu2]
    exact continuous_const.mul
      (continuous_ouSemigroup hf'1.continuous_deriv_one ⟨B2, hB2⟩)
  have hlog_cont : Continuous (fun x => Real.log (u x)) :=
    hu_cont.log (fun x => (hpos x).ne')
  have hfish_le : ∀ x, |(deriv u x) ^ 2 / u x| ≤ B ^ 2 / δ := by
    intro x
    rw [abs_div, abs_of_pos (hpos x), abs_sq]
    have hsq : (deriv u x) ^ 2 ≤ B ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hdu_bdd x) 2
    have hrec : (1 : ℝ) / u x ≤ 1 / δ :=
      one_div_le_one_div_of_le hδ (ouSemigroup_lower hf.continuous ⟨M, hM⟩ hδf)
    have hnonneg : 0 ≤ (1 : ℝ) / u x := div_nonneg zero_le_one (le_of_lt (hpos x))
    have hmul := mul_le_mul hsq hrec hnonneg (sq_nonneg _)
    have hrew : (deriv u x) ^ 2 / u x = (deriv u x) ^ 2 * (1 / u x) := by ring
    have hrew' : B ^ 2 / δ = B ^ 2 * (1 / δ) := by ring
    rw [hrew, hrew']
    exact hmul
  have hψ_cont : Continuous (deriv ψ) := by
    rw [hψ_form]
    exact (hdu2_cont.mul hlog_cont).add
      ((hdu_cont.pow 2).div hu_cont (fun x => (hpos x).ne'))
  have hψ_diff : Differentiable ℝ ψ := fun x => (hψAt x).differentiableAt
  have hψ_le : ∀ x, |ψ x| ≤ B * L := by
    intro x
    rw [abs_mul]
    exact mul_le_mul (hdu_bdd x) (hL x) (abs_nonneg _) hB0
  have hψ'_le : ∀ x, |deriv ψ x| ≤ B2 * L + B ^ 2 / δ := by
    intro x
    rw [hψ_form]
    have h1 : |deriv (deriv u) x * Real.log (u x)| ≤ B2 * L := by
      rw [abs_mul]
      exact mul_le_mul (hdu2_bdd x) (hL x) (abs_nonneg _) hB20
    exact (abs_add_le _ _).trans (by linarith [h1, hfish_le x])
  have hip := integral_id_mul_eq_integral_deriv_gaussianReal hψ_diff hψ_cont
    ⟨B * L, hψ_le⟩ ⟨B2 * L + B ^ 2 / δ, hψ'_le⟩
  have hlog_int : Integrable (fun x => deriv (deriv u) x * Real.log (u x)) γ :=
    integrable_of_abs_le ((hdu2_cont.mul hlog_cont).aestronglyMeasurable) (fun x => by
      rw [abs_mul]
      exact mul_le_mul (hdu2_bdd x) (hL x) (abs_nonneg _) hB20)
  have hfish_int : Integrable (fun x => (deriv u x) ^ 2 / u x) γ :=
    integrable_of_abs_le (((hdu_cont.pow 2).div hu_cont
      (fun x => (hpos x).ne')).aestronglyMeasurable)
      (fun x => (hfish_le x).trans (le_abs_self _))
  have hxψ_int : Integrable (fun x => x * ψ x) γ := by
    have hdom : Integrable (fun x => (B * L + 1) * |x|) γ :=
      integrable_abs_gaussianReal.const_mul _
    refine Integrable.mono' hdom ((continuous_id.mul hψ_diff.continuous).aestronglyMeasurable) ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_mul]
    calc |x| * |ψ x| ≤ |x| * (B * L) :=
          mul_le_mul_of_nonneg_left (hψ_le x) (abs_nonneg x)
      _ ≤ (B * L + 1) * |x| := by
          have hgrow : B * L ≤ B * L + 1 := le_add_of_nonneg_right zero_le_one
          have := mul_le_mul_of_nonneg_left hgrow (abs_nonneg x)
          linarith
  have hderiv_int : ∫ x, deriv ψ x ∂γ =
      ∫ x, deriv (deriv u) x * Real.log (u x) ∂γ +
        ∫ x, (deriv u x) ^ 2 / u x ∂γ := by
    rw [hψ_form, integral_add hlog_int hfish_int]
  have hxψ : ∫ x, x * ψ x ∂γ =
      ∫ x, deriv (deriv u) x * Real.log (u x) ∂γ +
        ∫ x, (deriv u x) ^ 2 / u x ∂γ := by
    rw [hip]
    exact hderiv_int
  have hsub : ∫ x, (deriv (deriv u) x - x * deriv u x) * Real.log (u x) ∂γ =
      ∫ x, deriv (deriv u) x * Real.log (u x) ∂γ - ∫ x, x * ψ x ∂γ := by
    have hfun : (fun x => (deriv (deriv u) x - x * deriv u x) * Real.log (u x)) =
        fun x => deriv (deriv u) x * Real.log (u x) - x * ψ x := by
      funext x
      ring
    rw [hfun, integral_sub hlog_int hxψ_int]
  have hgen_fun : (fun x => (deriv (fun s => ouSemigroup s f x) t) * Real.log (u x)) =
      fun x => (deriv (deriv u) x - x * deriv u x) * Real.log (u x) := by
    funext x
    rw [hgen x]
  rw [hgen_fun, hsub, hxψ]
  ring

end CKMA



