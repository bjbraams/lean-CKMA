/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Probability.InfinitelyDivisible.Kernel
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
public import Mathlib.MeasureTheory.Measure.FiniteMeasure
public import Mathlib.Topology.Order.Compact

import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Topology.Instances.NNReal.Lemmas

/-!
# Tightness of quadratically weighted convolution roots

Jordan's cosine bound integrates to a comparison between `1 ∧ x²` and `1 - sinc`.
Integrating `1 - Re φ` of a convolution root against that comparison bounds the total
mass and the tails of the quadratically weighted roots, uniformly in the root order.
-/

@[expose] public section

noncomputable section

namespace CKMA

open MeasureTheory Complex Filter Topology Set Function
open scoped NNReal ENNReal

/-- Constant `3 π² / 2` in the comparison of `1 ∧ x²` with `1 - sinc`. -/
def sincComparison : ℝ := 3 * Real.pi ^ 2 / 2

/-- The constant `3 π² / 2` is positive. -/
lemma sincComparison_pos : 0 < sincComparison := by
  unfold sincComparison
  positivity

/-- Coefficient `2 / (3 π²)` reciprocal to `sincComparison`. -/
def sincCoeff : ℝ := 2 / (3 * Real.pi ^ 2)

/-- The sinc coefficient is nonnegative. -/
lemma sincCoeff_nonneg : 0 ≤ sincCoeff := by
  unfold sincCoeff
  positivity

/-- `sincComparison` and `sincCoeff` are reciprocals. -/
lemma sincComparison_mul_sincCoeff : sincComparison * sincCoeff = 1 := by
  unfold sincComparison sincCoeff
  field_simp

/-- On `[0, π]`, sine lies under the cubic from the integrated cosine bound. -/
lemma sin_le_sub_sincCube {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ Real.pi) :
    Real.sin x ≤ x - sincCoeff * x ^ 3 := by
  let c : ℝ := 2 / Real.pi ^ 2
  have hder : ∀ u ∈ uIcc (0 : ℝ) x,
      HasDerivAt (fun u => u - c * u ^ 3 / 3) (1 - c * u ^ 2) u := by
    intro u _
    have hp : HasDerivAt (fun v : ℝ => v ^ 3) ((3 : ℝ) * u ^ 2) u := by
      simpa [Nat.cast_ofNat] using hasDerivAt_pow 3 u
    have hmul : HasDerivAt (fun v : ℝ => c * v ^ 3 / 3) (c * u ^ 2) u :=
      ((hp.const_mul c).div_const (3 : ℝ)).congr_deriv (by ring)
    have hsub := (hasDerivAt_id u).sub hmul
    refine hsub.congr_of_eventuallyEq ?_
    filter_upwards with v
    rfl
  have hint : IntervalIntegrable (fun u : ℝ => 1 - c * u ^ 2) volume 0 x :=
    (continuous_const.sub
      (continuous_const.mul (continuous_id.pow 2))).intervalIntegrable 0 x
  have hFTC : ∫ u in (0 : ℝ)..x, (1 - c * u ^ 2) =
      (x - c * x ^ 3 / 3) - (0 - c * 0 ^ 3 / 3) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hder hint
  have hpoly : ∫ u in (0 : ℝ)..x, (1 - c * u ^ 2) = x - sincCoeff * x ^ 3 := by
    rw [hFTC]
    unfold c sincCoeff
    ring
  have hcos : ∀ u ∈ Icc (0 : ℝ) x, Real.cos u ≤ 1 - c * u ^ 2 := by
    intro u hu
    have habs : |u| ≤ Real.pi := by
      rw [abs_of_nonneg hu.1]
      exact hu.2.trans hx
    have hpt : Real.cos u ≤ 1 - 2 / Real.pi ^ 2 * u ^ 2 :=
      Real.cos_le_one_sub_mul_cos_sq habs
    simpa [c] using hpt
  have hmono := intervalIntegral.integral_mono_on hx0
    (Real.continuous_cos.intervalIntegrable 0 x) hint hcos
  have hsin : ∫ u in (0 : ℝ)..x, Real.cos u = Real.sin x := by
    simp [integral_cos]
  rw [hsin] at hmono
  exact hmono.trans_eq hpoly

/-- `2 / (3 π²)` does not exceed `1 - 1/π`. -/
lemma sincCoeff_le_one_sub_inv_pi : sincCoeff ≤ 1 - Real.pi⁻¹ := by
  have htwo : (2 : ℝ) ≤ 3 * Real.pi * (Real.pi - 1) := by
    nlinarith [Real.pi_gt_three]
  have hform : 1 - Real.pi⁻¹ = (Real.pi - 1) / Real.pi := by
    field_simp
  rw [hform, sincCoeff]
  rw [div_le_div_iff₀ (by positivity) Real.pi_pos]
  have hπ : 0 ≤ Real.pi := Real.pi_nonneg
  calc
    (2 : ℝ) * Real.pi ≤ 3 * Real.pi * (Real.pi - 1) * Real.pi :=
      mul_le_mul_of_nonneg_right htwo hπ
    _ = (Real.pi - 1) * (3 * Real.pi ^ 2) := by ring

/-- `sincCoeff` times the quadratic weight is at most `1 - sinc`. -/
lemma sincCoeff_mul_quadTrunc_le (x : ℝ) :
    sincCoeff * quadTrunc x ≤ 1 - Real.sinc x := by
  suffices hsuff : sincCoeff * quadTrunc |x| ≤ 1 - Real.sinc |x| by
    have hquad : quadTrunc x = quadTrunc |x| := by simp [quadTrunc, sq_abs]
    have hsinc : Real.sinc x = Real.sinc |x| := by
      rcases le_total 0 x with hx | hx
      · simp [abs_of_nonneg hx]
      · rw [abs_of_nonpos hx, Real.sinc_neg]
    simpa [hquad, hsinc] using hsuff
  set y : ℝ := |x|
  have hy : 0 ≤ y := abs_nonneg x
  by_cases hy0 : y = 0
  · simp [hy0, quadTrunc, Real.sinc_zero]
  have hypos : 0 < y := lt_of_le_of_ne hy (Ne.symm hy0)
  rcases le_or_gt y Real.pi with hypi | hypi
  · have hsin := sin_le_sub_sincCube hy hypi
    rw [Real.sinc_of_ne_zero hy0]
    have hdiv : Real.sin y / y ≤ 1 - sincCoeff * y ^ 2 := by
      rw [div_le_iff₀ hypos, mul_comm]
      have hfac : y - sincCoeff * y ^ 3 = y * (1 - sincCoeff * y ^ 2) := by ring
      rw [← hfac]
      exact hsin
    have hq : quadTrunc y ≤ y ^ 2 := min_le_right _ _
    have hmul : sincCoeff * quadTrunc y ≤ sincCoeff * y ^ 2 :=
      mul_le_mul_of_nonneg_left hq sincCoeff_nonneg
    linarith
  · have hyne : y ≠ 0 := by linarith [Real.pi_pos]
    have hsinc : Real.sinc y ≤ y⁻¹ := by
      simpa [abs_of_nonneg hy] using Real.sinc_le_inv_abs hyne
    have hinv : y⁻¹ ≤ Real.pi⁻¹ := inv_anti₀ Real.pi_pos hypi.le
    have hgap := sincCoeff_le_one_sub_inv_pi
    have hq : quadTrunc y ≤ 1 := quadTrunc_le_one y
    have hmul : sincCoeff * quadTrunc y ≤ sincCoeff := by
      simpa using mul_le_mul_of_nonneg_left hq sincCoeff_nonneg
    linarith

/-- The quadratic weight is dominated by a constant multiple of `1 - sinc`. -/
lemma quadTrunc_le_sincComparison_mul (x : ℝ) :
    quadTrunc x ≤ sincComparison * (1 - Real.sinc x) := by
  have hmul := mul_le_mul_of_nonneg_left (sincCoeff_mul_quadTrunc_le x)
    sincComparison_pos.le
  rwa [← mul_assoc, sincComparison_mul_sincCoeff, one_mul] at hmul

/-- Modulus `r (1 + r exp r)` controlling an exponential increment. -/
def exponentModulus (r : ℝ) : ℝ := r * (1 + r * Real.exp r)

/-- The exponential-increment modulus is continuous. -/
lemma continuous_exponentModulus : Continuous exponentModulus := by
  unfold exponentModulus
  fun_prop

/-- The exponential-increment modulus is monotone on the nonnegative reals. -/
lemma exponentModulus_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    exponentModulus a ≤ exponentModulus b := by
  unfold exponentModulus
  have hexp : Real.exp a ≤ Real.exp b := Real.exp_le_exp.mpr hab
  have hmul : a * Real.exp a ≤ b * Real.exp b :=
    mul_le_mul hab hexp (Real.exp_nonneg _) (ha.trans hab)
  have hinner : 1 + a * Real.exp a ≤ 1 + b * Real.exp b := by linarith
  exact mul_le_mul hab hinner (by positivity) (ha.trans hab)

/-- The exponential-increment modulus is nonnegative on the nonnegative reals. -/
lemma exponentModulus_nonneg {r : ℝ} (hr : 0 ≤ r) : 0 ≤ exponentModulus r := by
  unfold exponentModulus
  positivity

/-- The norm of a characteristic exponent attains its maximum on `[-|δ|, |δ|]`. -/
lemma exists_norm_charExponent_isMaxOn {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (h : IsInfinitelyDivisible μ) (δ : ℝ) :
    ∃ t ∈ Icc (-|δ|) |δ|,
      IsMaxOn (fun s : ℝ => ‖charExponent h s‖) (Icc (-|δ|) |δ|) t := by
  refine IsCompact.exists_isMaxOn isCompact_Icc ?_ ?_
  · exact nonempty_Icc.mpr (by linarith [abs_nonneg δ])
  · exact (continuous_norm.comp (continuous_charExponent h)).continuousOn

/-- A point of `[-|δ|, |δ|]` at which the exponent norm is maximal. -/
def charExponentArg {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (h : IsInfinitelyDivisible μ) (δ : ℝ) : ℝ :=
  Classical.choose (exists_norm_charExponent_isMaxOn h δ)

/-- The exponent norm at the chosen maximizer. -/
def charExponentMax {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (h : IsInfinitelyDivisible μ) (δ : ℝ) : ℝ :=
  ‖charExponent h (charExponentArg h δ)‖

/-- The maximizer lies in `[-|δ|, |δ|]`. -/
lemma abs_charExponentArg_le {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (h : IsInfinitelyDivisible μ) (δ : ℝ) : |charExponentArg h δ| ≤ |δ| := by
  have hmem := (Classical.choose_spec (exists_norm_charExponent_isMaxOn h δ)).1
  exact abs_le.mpr hmem

/-- On `[-|δ|, |δ|]` the exponent norm does not exceed `charExponentMax`. -/
lemma norm_charExponent_le_charExponentMax {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (h : IsInfinitelyDivisible μ) (δ : ℝ) {t : ℝ} (ht : |t| ≤ |δ|) :
    ‖charExponent h t‖ ≤ charExponentMax h δ := by
  have hspec := Classical.choose_spec (exists_norm_charExponent_isMaxOn h δ)
  exact hspec.2 (abs_le.mp ht)

/-- The maximal exponent norm on `[-1/(n+1), 1/(n+1)]` tends to zero. -/
lemma tendsto_charExponentMax_inv {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (h : IsInfinitelyDivisible μ) :
    Tendsto (fun n : ℕ => charExponentMax h (1 / (n + 1 : ℝ))) atTop (𝓝 0) := by
  let t : ℕ → ℝ := fun n => charExponentArg h (1 / (n + 1 : ℝ))
  have hnorm : ∀ n, ‖t n‖ ≤ 1 / ((n : ℝ) + 1) := by
    intro n
    rw [Real.norm_eq_abs]
    have harg := abs_charExponentArg_le h (1 / (n + 1 : ℝ))
    have hpos : (0 : ℝ) ≤ 1 / (n + 1 : ℝ) := by positivity
    rw [abs_of_nonneg hpos] at harg
    simpa [t] using harg
  have ht0 : Tendsto t atTop (𝓝 0) :=
    squeeze_zero_norm hnorm tendsto_one_div_add_atTop_nhds_zero_nat
  have hψ : Tendsto (fun n => charExponent h (t n)) atTop (𝓝 0) := by
    have hcomp := ((continuous_charExponent h).tendsto 0).comp ht0
    rw [charExponent_zero] at hcomp
    simpa [Function.comp_def] using hcomp
  have hnormψ : Tendsto (fun n => ‖charExponent h (t n)‖) atTop (𝓝 0) := by
    have hcomp := (continuous_norm.tendsto (0 : ℂ)).comp hψ
    simpa [Function.comp_def, norm_zero] using hcomp
  simpa [charExponentMax, charExponentArg, t] using hnormψ

/-- The convolution root of order `n + 1`. -/
def positiveRoot {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (h : IsInfinitelyDivisible μ) (n : ℕ) : Measure ℝ :=
  convolutionRoot h (n + 1) (Nat.succ_pos n)

/-- Each positive convolution root is a probability measure. -/
instance isProbabilityMeasure_positiveRoot {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (h : IsInfinitelyDivisible μ) (n : ℕ) :
    IsProbabilityMeasure (positiveRoot h n) :=
  isProbabilityMeasure_convolutionRoot h (Nat.succ_pos n)

/-- The characteristic function of a positive root is the exponential of `ψ / (n + 1)`. -/
lemma charFun_positiveRoot {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (h : IsInfinitelyDivisible μ) (n : ℕ) (t : ℝ) :
    charFun (positiveRoot h n) t =
      exp (charExponent h t / ((n + 1 : ℕ) : ℂ)) :=
  charFun_convolutionRoot h (Nat.succ_pos n) t

/-- Integral of `1 - cos(t x)` over `[-δ, δ]`. -/
lemma intervalIntegral_one_sub_cos {δ x : ℝ} (hδ : 0 ≤ δ) :
    ∫ t in (-δ)..δ, (1 - Real.cos (t * x)) = 2 * δ * (1 - Real.sinc (δ * x)) := by
  by_cases hx : x = 0
  · simp [hx, Real.cos_zero, Real.sinc_zero, sub_self, intervalIntegral.integral_zero]
  by_cases hδ0 : δ = 0
  · simp [hδ0, Real.sinc_zero, intervalIntegral.integral_same]
  have hδpos : 0 < δ := lt_of_le_of_ne hδ (Ne.symm hδ0)
  have hsub : ∫ t in (-δ)..δ, ((1 : ℝ) - Real.cos (t * x)) =
      (∫ t in (-δ)..δ, (1 : ℝ)) - ∫ t in (-δ)..δ, Real.cos (t * x) :=
    intervalIntegral.integral_sub (continuous_const.intervalIntegrable (-δ) δ)
      ((Real.continuous_cos.comp
        (continuous_id.mul continuous_const)).intervalIntegrable (-δ) δ)
  have hconst : ∫ t in (-δ)..δ, (1 : ℝ) = 2 * δ := by
    rw [intervalIntegral.integral_const]
    simp only [sub_neg_eq_add]
    ring
  have hcos : ∫ t in (-δ)..δ, Real.cos (t * x) = 2 * δ * Real.sinc (δ * x) := by
    have hfun : (fun t : ℝ => Real.cos (t * x)) = fun t => Real.cos (x * t) := by
      ext t
      rw [mul_comm]
    rw [hfun, intervalIntegral.integral_comp_mul_left Real.cos hx, integral_cos]
    have hdx : δ * x ≠ 0 := mul_ne_zero hδpos.ne' hx
    rw [Real.sinc_of_ne_zero hdx]
    simp only [smul_eq_mul]
    have hneg : x * -δ = -(x * δ) := by ring
    rw [hneg, Real.sin_neg]
    field_simp [hx, hδpos.ne']
    ring_nf
  rw [hsub, hconst, hcos]
  ring

/-- `1` minus the real part of a characteristic function is an integral of `1 - cos`. -/
lemma one_sub_re_charFun {ν : Measure ℝ} [IsProbabilityMeasure ν] (t : ℝ) :
    1 - (charFun ν t).re = ∫ x, (1 - Real.cos (t * x)) ∂ν := by
  have hchar : charFun ν t = ∫ x, exp (↑t * ↑x * I) ∂ν := by
    rw [charFun_apply_real]
  have hint : Integrable (fun x : ℝ => exp (↑t * ↑x * I)) ν := by
    refine (integrable_const (1 : ℝ)).mono' (by fun_prop) ?_
    refine ae_of_all _ fun x => ?_
    have harg : ↑t * ↑x * I = ↑(t * x) * I := by
      push_cast
      ring
    rw [harg, Complex.norm_exp_ofReal_mul_I]
  have hre : (charFun ν t).re = ∫ x, Real.cos (t * x) ∂ν := by
    rw [hchar]
    change RCLike.re (∫ x, exp (↑t * ↑x * I) ∂ν) = ∫ x, Real.cos (t * x) ∂ν
    rw [← integral_re hint]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    change RCLike.re (exp (↑t * ↑x * I)) = Real.cos (t * x)
    have hcoe : RCLike.re (exp (↑t * ↑x * I)) = (exp (↑t * ↑x * I)).re :=
      congrFun RCLike.re_eq_complex_re _
    rw [hcoe, Complex.exp_re]
    simp [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Real.exp_zero]
  have hcos : Integrable (fun x : ℝ => Real.cos (t * x)) ν := by
    refine (integrable_const (1 : ℝ)).mono' (by fun_prop) ?_
    refine ae_of_all _ fun x => ?_
    rw [Real.norm_eq_abs]
    exact Real.abs_cos_le_one _
  have hone : ∫ _ : ℝ, (1 : ℝ) ∂ν = 1 := by simp [integral_const, probReal_univ]
  have hsub : ∫ x, ((1 : ℝ) - Real.cos (t * x)) ∂ν =
      (∫ _ : ℝ, (1 : ℝ) ∂ν) - ∫ x, Real.cos (t * x) ∂ν :=
    integral_sub (integrable_const _) hcos
  calc
    (1 : ℝ) - (charFun ν t).re =
        (∫ _ : ℝ, (1 : ℝ) ∂ν) - (charFun ν t).re := by rw [hone]
    _ = (∫ _ : ℝ, (1 : ℝ) ∂ν) - ∫ x, Real.cos (t * x) ∂ν := by rw [hre]
    _ = ∫ x, ((1 : ℝ) - Real.cos (t * x)) ∂ν := hsub.symm

/-- The product integrand `1 - cos(t x)` is integrable on a bounded time interval. -/
lemma integrable_one_sub_cos_prod {ν : Measure ℝ} [IsProbabilityMeasure ν] {δ : ℝ}
    (hδ : 0 < δ) :
    Integrable (uncurry fun t x => 1 - Real.cos (t * x))
      ((volume.restrict (uIoc (-δ) δ)).prod ν) := by
  have : IsFiniteMeasure (volume.restrict (uIoc (-δ) δ)) := by
    rw [uIoc_of_le (by linarith : -δ ≤ δ)]
    infer_instance
  refine (integrable_const (2 : ℝ)).mono' (by fun_prop) ?_
  refine ae_of_all _ fun p => ?_
  rw [Real.norm_eq_abs, uncurry]
  have h0 : 0 ≤ 1 - Real.cos (p.1 * p.2) := sub_nonneg.mpr (Real.cos_le_one _)
  rw [abs_of_nonneg h0]
  have hcosb : -1 ≤ Real.cos (p.1 * p.2) := (abs_le.mp (Real.abs_cos_le_one _)).1
  linarith

/-- `n + 1` times `1 - Re φ` of a root is bounded by the exponent modulus. -/
lemma nat_mul_one_sub_re_le {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (h : IsInfinitelyDivisible μ) (n : ℕ) {t δ : ℝ} (ht : |t| ≤ |δ|) :
    ((n + 1 : ℕ) : ℝ) * (1 - (charFun (positiveRoot h n) t).re) ≤
      exponentModulus (charExponentMax h δ) := by
  have hm : 0 < n + 1 := Nat.succ_pos n
  rw [charFun_positiveRoot]
  have hre : (((n + 1 : ℕ) : ℂ) *
        (1 - exp (charExponent h t / ((n + 1 : ℕ) : ℂ)))).re =
      ((n + 1 : ℕ) : ℝ) *
        (1 - (exp (charExponent h t / ((n + 1 : ℕ) : ℂ))).re) := by
    have hmC : ((n + 1 : ℕ) : ℂ) = (((n + 1 : ℕ) : ℝ) : ℂ) := by norm_cast
    rw [hmC, re_ofReal_mul, sub_re, one_re]
  have hnorm : ((n + 1 : ℕ) : ℝ) *
        (1 - (exp (charExponent h t / ((n + 1 : ℕ) : ℂ))).re) ≤
      ‖((n + 1 : ℕ) : ℂ) * (exp (charExponent h t / ((n + 1 : ℕ) : ℂ)) - 1)‖ := by
    rw [← hre]
    calc
      (((n + 1 : ℕ) : ℂ) *
          (1 - exp (charExponent h t / ((n + 1 : ℕ) : ℂ)))).re ≤
          ‖((n + 1 : ℕ) : ℂ) *
            (1 - exp (charExponent h t / ((n + 1 : ℕ) : ℂ)))‖ := re_le_norm _
      _ = ‖((n + 1 : ℕ) : ℂ) *
            (exp (charExponent h t / ((n + 1 : ℕ) : ℂ)) - 1)‖ := by
        rw [show (1 : ℂ) - exp (charExponent h t / ((n + 1 : ℕ) : ℂ)) =
            -(exp (charExponent h t / ((n + 1 : ℕ) : ℂ)) - 1) by ring]
        rw [mul_neg, norm_neg]
  have hinc := norm_nat_mul_exp_div_sub_one_le hm (charExponent h t)
  have hmax : ‖charExponent h t‖ ≤ charExponentMax h δ :=
    norm_charExponent_le_charExponentMax h δ ht
  have hmod : exponentModulus ‖charExponent h t‖ ≤
      exponentModulus (charExponentMax h δ) :=
    exponentModulus_mono (norm_nonneg _) hmax
  refine hnorm.trans (hinc.trans ?_)
  simpa [exponentModulus] using hmod

/-- Integrating `1 - sinc(δ x)` against a root costs at most the exponent modulus. -/
lemma integral_one_sub_sinc_le {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (h : IsInfinitelyDivisible μ) (n : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∫ x, (1 - Real.sinc (δ * x)) ∂positiveRoot h n ≤
      exponentModulus (charExponentMax h δ) / (n + 1 : ℝ) := by
  set ν : Measure ℝ := positiveRoot h n
  set m : ℕ := n + 1
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast Nat.succ_pos n
  have hle_iv : -δ ≤ δ := by linarith
  have hpoint : ∀ t ∈ Icc (-δ) δ,
      1 - (charFun ν t).re ≤ exponentModulus (charExponentMax h δ) / (m : ℝ) := by
    intro t ht
    have habs : |t| ≤ |δ| := by
      rw [abs_of_nonneg hδ.le]
      exact abs_le.mpr ht
    rw [le_div_iff₀ hmpos, mul_comm]
    simpa [ν, m] using nat_mul_one_sub_re_le h n habs
  have hint1 : IntervalIntegrable (fun t : ℝ => 1 - (charFun ν t).re) volume (-δ) δ :=
    (continuous_const.sub
      (continuous_re.comp continuous_charFun)).intervalIntegrable (-δ) δ
  have hint2 : IntervalIntegrable
      (fun _ : ℝ => exponentModulus (charExponentMax h δ) / (m : ℝ)) volume (-δ) δ :=
    continuous_const.intervalIntegrable (-δ) δ
  have hint := intervalIntegral.integral_mono_on hle_iv hint1 hint2 hpoint
  have hconst : ∫ t in (-δ)..δ, exponentModulus (charExponentMax h δ) / (m : ℝ) =
      2 * δ * (exponentModulus (charExponentMax h δ) / (m : ℝ)) := by
    rw [intervalIntegral.integral_const]
    simp only [sub_neg_eq_add]
    ring
  have hiter : ∫ t in (-δ)..δ, (1 - (charFun ν t).re) =
      ∫ t in (-δ)..δ, ∫ x, (1 - Real.cos (t * x)) ∂ν := by
    refine intervalIntegral.integral_congr ?_
    intro t _
    simpa [ν] using one_sub_re_charFun (ν := ν) t
  have hswap := intervalIntegral_integral_swap (a := -δ) (b := δ) (μ := ν)
    (f := fun t x => 1 - Real.cos (t * x)) (integrable_one_sub_cos_prod (ν := ν) hδ)
  have hinner : ∫ x, (∫ t in (-δ)..δ, (1 - Real.cos (t * x))) ∂ν =
      ∫ x, 2 * δ * (1 - Real.sinc (δ * x)) ∂ν := by
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    exact intervalIntegral_one_sub_cos hδ.le
  have hfac : ∫ x, 2 * δ * (1 - Real.sinc (δ * x)) ∂ν =
      2 * δ * ∫ x, (1 - Real.sinc (δ * x)) ∂ν :=
    integral_const_mul (2 * δ) (fun x => 1 - Real.sinc (δ * x))
  have hbound : 2 * δ * ∫ x, (1 - Real.sinc (δ * x)) ∂ν ≤
      2 * δ * (exponentModulus (charExponentMax h δ) / (m : ℝ)) := by
    calc
      2 * δ * ∫ x, (1 - Real.sinc (δ * x)) ∂ν =
          ∫ x, 2 * δ * (1 - Real.sinc (δ * x)) ∂ν := by rw [hfac]
      _ = ∫ x, (∫ t in (-δ)..δ, (1 - Real.cos (t * x))) ∂ν := by rw [hinner]
      _ = ∫ t in (-δ)..δ, ∫ x, (1 - Real.cos (t * x)) ∂ν := by rw [hswap]
      _ = ∫ t in (-δ)..δ, (1 - (charFun ν t).re) := by rw [hiter]
      _ ≤ ∫ t in (-δ)..δ, exponentModulus (charExponentMax h δ) / (m : ℝ) := hint
      _ = 2 * δ * (exponentModulus (charExponentMax h δ) / (m : ℝ)) := hconst
  have hmR : (m : ℝ) = (n : ℝ) + 1 := by simp [m]
  rw [hmR] at hbound
  exact (mul_le_mul_iff_of_pos_left (by positivity : 0 < 2 * δ)).mp hbound

/-- `1 - sinc(δ x)` is integrable on a probability space. -/
lemma integrable_one_sub_sinc_mul {ν : Measure ℝ} [IsProbabilityMeasure ν] (δ : ℝ) :
    Integrable (fun x : ℝ => 1 - Real.sinc (δ * x)) ν := by
  refine (integrable_const (2 : ℝ)).mono' (by fun_prop) ?_
  refine ae_of_all _ fun x => ?_
  rw [Real.norm_eq_abs]
  have h0 : 0 ≤ 1 - Real.sinc (δ * x) := sub_nonneg.mpr (Real.sinc_le_one _)
  rw [abs_of_nonneg h0]
  linarith [Real.neg_one_le_sinc (δ * x)]

/-- The quadratic weight is integrable on a finite measure. -/
lemma integrable_quadTrunc_prob {ν : Measure ℝ} [IsFiniteMeasure ν] :
    Integrable quadTrunc ν := by
  refine (integrable_const (1 : ℝ)).mono' continuous_quadTrunc.aestronglyMeasurable ?_
  refine ae_of_all _ fun x => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (quadTrunc_nonneg x)]
  exact quadTrunc_le_one x

/-- Integrated quadratic weight of a root, scaled by the root order in the denominator. -/
lemma integral_quadTrunc_le {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (h : IsInfinitelyDivisible μ) (n : ℕ) :
    ∫ x, quadTrunc x ∂positiveRoot h n ≤
      sincComparison * exponentModulus (charExponentMax h 1) / (n + 1 : ℝ) := by
  have hintq : Integrable quadTrunc (positiveRoot h n) := integrable_quadTrunc_prob
  have hints : Integrable (fun x : ℝ => 1 - Real.sinc x) (positiveRoot h n) := by
    simpa [one_mul] using integrable_one_sub_sinc_mul (ν := positiveRoot h n) 1
  have hintm : Integrable (fun x : ℝ => sincComparison * (1 - Real.sinc x))
      (positiveRoot h n) := hints.const_mul _
  have hpt : ∀ x, quadTrunc x ≤ sincComparison * (1 - Real.sinc x) :=
    quadTrunc_le_sincComparison_mul
  have hle1 : ∫ x, quadTrunc x ∂positiveRoot h n ≤
      ∫ x, sincComparison * (1 - Real.sinc x) ∂positiveRoot h n :=
    integral_mono hintq hintm hpt
  rw [integral_const_mul] at hle1
  have hle2 : ∫ x, (1 - Real.sinc x) ∂positiveRoot h n ≤
      exponentModulus (charExponentMax h 1) / (n + 1 : ℝ) := by
    simpa [one_mul] using integral_one_sub_sinc_le h n (δ := 1) one_pos
  have hassoc : sincComparison *
        (exponentModulus (charExponentMax h 1) / (n + 1 : ℝ)) =
      sincComparison * exponentModulus (charExponentMax h 1) / (n + 1 : ℝ) := by
    ring
  exact hle1.trans
    ((mul_le_mul_of_nonneg_left hle2 sincComparison_pos.le).trans_eq hassoc)

/-- Total mass of a quadratically weighted positive root. -/
lemma quadWeighted_univ_le {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (h : IsInfinitelyDivisible μ) (n : ℕ) :
    quadWeighted (n + 1) (positiveRoot h n) univ ≤
      ENNReal.ofReal (sincComparison * exponentModulus (charExponentMax h 1)) := by
  rw [quadWeighted, Measure.smul_apply, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal integrable_quadTrunc_prob
      (ae_of_all _ quadTrunc_nonneg), smul_eq_mul]
  have hcast : ((n + 1 : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((n : ℝ) + 1) := by
    rw [← ENNReal.ofReal_natCast (n + 1)]
    congr 1
    simp
  rw [hcast, ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hint := integral_quadTrunc_le h n
  have hassoc : ((n : ℝ) + 1) *
        (sincComparison * exponentModulus (charExponentMax h 1) / ((n : ℝ) + 1)) =
      sincComparison * exponentModulus (charExponentMax h 1) := by
    field_simp
  calc
    ((n : ℝ) + 1) * ∫ x, quadTrunc x ∂positiveRoot h n ≤
        ((n : ℝ) + 1) * (sincComparison * exponentModulus (charExponentMax h 1) /
          ((n : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left hint (by positivity)
    _ = sincComparison * exponentModulus (charExponentMax h 1) := hassoc

/-- The quadratic weight equals one once `|x|` is at least one. -/
lemma quadTrunc_eq_one_of_one_le_abs {x : ℝ} (hx : 1 ≤ |x|) : quadTrunc x = 1 := by
  have : (1 : ℝ) ≤ x ^ 2 := by
    rw [← sq_abs]
    exact one_le_pow₀ hx
  exact min_eq_left this

/-- Compact interval of radius `n + 1`, increasing in `n`. -/
def tailSet (n : ℕ) : Set ℝ := Icc (-(n + 1 : ℝ)) (n + 1 : ℝ)

/-- The tail intervals increase with the index. -/
lemma monotone_tailSet : Monotone tailSet := by
  intro a b hab x hx
  have hcast : (a : ℝ) + 1 ≤ (b : ℝ) + 1 := by
    simpa [add_comm] using add_le_add_right (Nat.cast_le.mpr hab) (1 : ℝ)
  refine ⟨?_, hx.2.trans hcast⟩
  have hneg : (-(b + 1 : ℝ)) ≤ -(a + 1 : ℝ) := neg_le_neg hcast
  exact hneg.trans hx.1

/-- Outside `[-k-1, k+1]` the quadratic weight is dominated by `1 - sinc`. -/
lemma quadTrunc_le_of_not_mem_tailSet {k : ℕ} {x : ℝ} (hx : x ∉ tailSet k) :
    quadTrunc x ≤ sincComparison *
      (1 - Real.sinc ((1 / (k + 1 : ℝ)) * x)) := by
  have hR : (k + 1 : ℝ) < |x| := by
    rw [tailSet, mem_Icc] at hx
    by_cases hxl : x < -(k + 1 : ℝ)
    · rw [abs_of_neg (by linarith)]
      linarith
    · have hxge : -(k + 1 : ℝ) ≤ x := le_of_not_gt hxl
      have hnot : ¬ x ≤ (k + 1 : ℝ) := by
        intro hle
        exact hx ⟨hxge, hle⟩
      have hxr : (k + 1 : ℝ) < x := lt_of_not_ge hnot
      rw [abs_of_nonneg (by linarith)]
      exact hxr
  have hscale : 1 ≤ |(1 / (k + 1 : ℝ)) * x| := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (k + 1 : ℝ))]
    have hdiv : 1 ≤ |x| / (k + 1 : ℝ) := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < (k : ℝ) + 1)]
      have hone : (1 : ℝ) * ((k : ℝ) + 1) = (k : ℝ) + 1 := by ring
      rw [hone]
      exact hR.le
    simpa [div_eq_mul_inv, one_div, mul_comm] using hdiv
  have hbig : 1 ≤ |x| := by
    have hone : (1 : ℝ) ≤ (k + 1 : ℝ) := by
      exact_mod_cast (Nat.succ_le_succ (Nat.zero_le k) : 1 ≤ k + 1)
    exact hone.trans hR.le
  have hqδ := quadTrunc_le_sincComparison_mul ((1 / (k + 1 : ℝ)) * x)
  rw [quadTrunc_eq_one_of_one_le_abs hscale] at hqδ
  simpa [quadTrunc_eq_one_of_one_le_abs hbig] using hqδ

/-- Uniform mass bound, as a nonnegative real, for every weighted root. -/
def idMass {μ : Measure ℝ} [IsProbabilityMeasure μ] (h : IsInfinitelyDivisible μ) : ℝ≥0 :=
  Real.toNNReal (sincComparison * exponentModulus (charExponentMax h 1))

/-- Tail bound outside `[-k-1, k+1]`, independent of the root order. -/
def idTail {μ : Measure ℝ} [IsProbabilityMeasure μ] (h : IsInfinitelyDivisible μ)
    (k : ℕ) : ℝ≥0 :=
  Real.toNNReal (sincComparison *
    exponentModulus (charExponentMax h (1 / (k + 1 : ℝ))))

/-- The uniform tail bounds tend to zero. -/
lemma tendsto_idTail {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (h : IsInfinitelyDivisible μ) : Tendsto (idTail h) atTop (𝓝 0) := by
  have hmax := tendsto_charExponentMax_inv h
  have hzero : exponentModulus 0 = 0 := by
    simp [exponentModulus, Real.exp_zero]
  have hmod : Tendsto (fun n : ℕ =>
      exponentModulus (charExponentMax h (1 / (n + 1 : ℝ)))) atTop (𝓝 0) := by
    have hcomp := (continuous_exponentModulus.tendsto 0).comp hmax
    rw [Function.comp_def, hzero] at hcomp
    exact hcomp
  have hmul : Tendsto (fun n : ℕ => sincComparison *
      exponentModulus (charExponentMax h (1 / (n + 1 : ℝ)))) atTop (𝓝 0) := by
    have hconst := hmod.const_mul sincComparison
    rw [mul_zero] at hconst
    exact hconst
  have hto := tendsto_real_toNNReal hmul
  rw [Real.toNNReal_zero] at hto
  exact hto

/-- Mass of a weighted root outside `[-k-1, k+1]`. -/
lemma quadWeighted_tail_le {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (h : IsInfinitelyDivisible μ) (n k : ℕ) :
    quadWeighted (n + 1) (positiveRoot h n) (tailSet k)ᶜ ≤
      ENNReal.ofReal (sincComparison *
        exponentModulus (charExponentMax h (1 / (k + 1 : ℝ)))) := by
  set δ : ℝ := 1 / (k + 1 : ℝ)
  have hδ : 0 < δ := by
    unfold δ
    positivity
  have hs : MeasurableSet (tailSet k)ᶜ := (isClosed_Icc).measurableSet.compl
  have hpt : ∀ x ∈ (tailSet k)ᶜ, ENNReal.ofReal (quadTrunc x) ≤
      ENNReal.ofReal (sincComparison * (1 - Real.sinc (δ * x))) := by
    intro x hx
    exact ENNReal.ofReal_le_ofReal (by simpa [δ] using quadTrunc_le_of_not_mem_tailSet hx)
  have hmono := setLIntegral_mono' (μ := positiveRoot h n) hs hpt
  have hf : Integrable (fun x => sincComparison * (1 - Real.sinc (δ * x)))
      (positiveRoot h n) :=
    (integrable_one_sub_sinc_mul δ).const_mul _
  have hnn : 0 ≤ᵐ[positiveRoot h n]
      (fun x => sincComparison * (1 - Real.sinc (δ * x))) :=
    ae_of_all _ fun x => mul_nonneg sincComparison_pos.le
      (sub_nonneg.mpr (Real.sinc_le_one _))
  have hmod0 : 0 ≤ exponentModulus (charExponentMax h δ) :=
    exponentModulus_nonneg (norm_nonneg _)
  have hfull : ∫⁻ x in (tailSet k)ᶜ,
      ENNReal.ofReal (sincComparison * (1 - Real.sinc (δ * x))) ∂positiveRoot h n ≤
      ENNReal.ofReal (sincComparison * exponentModulus (charExponentMax h δ) /
        ((n : ℝ) + 1)) := by
    refine (setLIntegral_le_lintegral _ _).trans ?_
    rw [← ofReal_integral_eq_lintegral_ofReal hf hnn, integral_const_mul]
    refine ENNReal.ofReal_le_ofReal ?_
    have hint := mul_le_mul_of_nonneg_left (integral_one_sub_sinc_le h n hδ)
      sincComparison_pos.le
    have hassoc : sincComparison *
          (exponentModulus (charExponentMax h δ) / ((n : ℝ) + 1)) =
        sincComparison * exponentModulus (charExponentMax h δ) / ((n : ℝ) + 1) := by
      ring
    exact hint.trans_eq hassoc
  have hlin : ∫⁻ x in (tailSet k)ᶜ, ENNReal.ofReal (quadTrunc x) ∂positiveRoot h n ≤
      ENNReal.ofReal (sincComparison * exponentModulus (charExponentMax h δ) /
        ((n : ℝ) + 1)) :=
    hmono.trans hfull
  rw [quadWeighted, Measure.smul_apply, withDensity_apply _ hs, smul_eq_mul]
  have hcast : ((n + 1 : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((n : ℝ) + 1) := by
    rw [← ENNReal.ofReal_natCast (n + 1)]
    congr 1
    simp
  have hfin : (∫⁻ x in (tailSet k)ᶜ, ENNReal.ofReal (quadTrunc x) ∂positiveRoot h n) ≠ ∞ :=
    ne_of_lt (hlin.trans_lt ENNReal.ofReal_lt_top)
  rw [hcast, ← ENNReal.ofReal_toReal hfin, ← ENNReal.ofReal_mul
    (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hmul : ((n : ℝ) + 1) * (sincComparison *
      exponentModulus (charExponentMax h δ) / ((n : ℝ) + 1)) =
      sincComparison * exponentModulus (charExponentMax h δ) := by
    field_simp
  have hto := ENNReal.toReal_mono ENNReal.ofReal_ne_top hlin
  rw [ENNReal.toReal_ofReal (div_nonneg (mul_nonneg sincComparison_pos.le hmod0)
    (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1))] at hto
  have hmul' : ((n : ℝ) + 1) *
      (∫⁻ x in (tailSet k)ᶜ, ENNReal.ofReal (quadTrunc x) ∂positiveRoot h n).toReal ≤
      ((n : ℝ) + 1) * (sincComparison * exponentModulus (charExponentMax h δ) /
        ((n : ℝ) + 1)) :=
    mul_le_mul_of_nonneg_left hto (by positivity)
  exact hmul'.trans_eq hmul

/-- Quadratically weighted positive root, packaged as a finite measure. -/
def idRootMeasure {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (h : IsInfinitelyDivisible μ) (n : ℕ) : FiniteMeasure ℝ :=
  ⟨quadWeighted (n + 1) (positiveRoot h n), isFiniteMeasure_quadWeighted (n + 1)⟩

/-- Every weighted root lies in the Prokhorov set of mass `idMass` and tails `idTail`. -/
lemma idRootMeasure_mem {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (h : IsInfinitelyDivisible μ) (n : ℕ) :
    idRootMeasure h n ∈ {ρ : FiniteMeasure ℝ |
      ρ.mass ≤ idMass h ∧ ∀ k, ρ (tailSet k)ᶜ ≤ idTail h k} := by
  refine ⟨?_, ?_⟩
  · have hle := quadWeighted_univ_le h n
    simp only [idRootMeasure, FiniteMeasure.mass, FiniteMeasure.mk_apply]
    refine (ENNReal.toNNReal_mono ENNReal.ofReal_ne_top hle).trans ?_
    simp [idMass, ENNReal.ofReal, ENNReal.toNNReal_coe]
  · intro k
    have hle := quadWeighted_tail_le h n k
    simp only [idRootMeasure, FiniteMeasure.mk_apply]
    refine (ENNReal.toNNReal_mono ENNReal.ofReal_ne_top hle).trans ?_
    simp [idTail, ENNReal.ofReal, ENNReal.toNNReal_coe]

/-- The Prokhorov set containing every quadratically weighted convolution root is compact. -/
lemma isCompact_idApproximant {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (h : IsInfinitelyDivisible μ) :
    IsCompact {ρ : FiniteMeasure ℝ |
      ρ.mass ≤ idMass h ∧ ∀ k, ρ (tailSet k)ᶜ ≤ idTail h k} :=
  isCompact_setOfPred_finiteMeasure_mass_le_compl_isCompact_le (idMass h) (tendsto_idTail h)
    (fun k => by
      simpa [tailSet] using
        (isCompact_Icc : IsCompact (Icc (-(k + 1 : ℝ)) (k + 1 : ℝ))))
    (Or.inr monotone_tailSet)

end CKMA
