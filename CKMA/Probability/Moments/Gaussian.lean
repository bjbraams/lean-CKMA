/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Probability.BrownianMotion.Basic

/-!
# Absolute moments of real Gaussians and of pre-Brownian increments

A centered Gaussian of variance `v` is the law of `√v` times a standard normal. Absolute moments
therefore scale by `v ^ (p / 2)`. Pre-Brownian increments are exactly those Gaussians, so
`∫ |B s - B t| ^ p = gaussianAbsMoment p * |s - t| ^ (p / 2)`, which is the Kolmogorov moment
condition with exponent `p / 2 > 1` once `p > 2`.

## Main definitions

* `CKMA.gaussianAbsMoment`: absolute moment of order `p` of a standard real Gaussian. For
  `p ≤ -1` the integral is the junk value `0`.

## Main results

* `CKMA.integrable_abs_rpow_gaussianReal`: absolute moments of positive order are finite.
* `CKMA.integral_abs_rpow_gaussianReal`: scaling identity for absolute moments of centered real
  Gaussians.
* `CKMA.integral_abs_sub_rpow_eq_of_isPreBrownianReal`: absolute moments of pre-Brownian
  increments, the Kolmogorov moment condition.
-/

public section

noncomputable section

namespace CKMA

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

/-- Absolute moment `∫ |x| ^ p ∂gaussianReal 0 1`, for an arbitrary real order `p`. For `p ≤ -1`
the integrand is not integrable near `0`, so the integral is `0`. For `0 < p`, finiteness is
`integrable_abs_rpow_gaussianReal`. -/
@[expose]
def gaussianAbsMoment (p : ℝ) : ℝ :=
  ∫ x, |x| ^ p ∂gaussianReal 0 1

/-- Defining equation of `gaussianAbsMoment`. -/
theorem gaussianAbsMoment_def (p : ℝ) : gaussianAbsMoment p = ∫ x, |x| ^ p ∂gaussianReal 0 1 :=
  rfl

/-- Absolute moments of every positive order are integrable for every real Gaussian. -/
lemma integrable_abs_rpow_gaussianReal {p : ℝ} (hp : 0 < p) (m : ℝ) (v : ℝ≥0) :
    Integrable (fun x : ℝ ↦ |x| ^ p) (gaussianReal m v) := by
  have hint := (memLp_id_gaussianReal (μ := m) (v := v) (Real.toNNReal p)).integrable_norm_rpow
    (by simp [hp]) (by simp)
  simpa [Real.norm_eq_abs, Real.coe_toNNReal p hp.le] using hint

/-- Multiplication by `√v` sends the standard Gaussian to the centered Gaussian of variance `v`. -/
private lemma gaussianReal_map_sqrt (v : ℝ≥0) :
    (gaussianReal 0 1).map (fun x ↦ Real.sqrt (v : ℝ) * x) = gaussianReal 0 v := by
  let c : ℝ := Real.sqrt (v : ℝ)
  have h := gaussianReal_map_const_mul (μ := 0) (v := 1) c
  have hv' : NNReal.mk (c ^ 2) (sq_nonneg c) = v := by
    ext
    simp [c, Real.sq_sqrt (NNReal.coe_nonneg v)]
  rw [h, hv']
  simp

/-- `√v` raised to `p` is the variance raised to `p / 2`. -/
private lemma sqrt_rpow_eq_rpow_div_two {p : ℝ} {v : ℝ≥0} :
    Real.sqrt (v : ℝ) ^ p = (v : ℝ) ^ (p / 2) := by
  have hc0 : 0 ≤ Real.sqrt (v : ℝ) := Real.sqrt_nonneg _
  calc
    Real.sqrt (v : ℝ) ^ p
      = Real.sqrt (v : ℝ) ^ ((2 : ℝ) * (p / 2)) := by ring_nf
    _ = (Real.sqrt (v : ℝ) ^ (2 : ℝ)) ^ (p / 2) := by
      rw [Real.rpow_mul hc0]
    _ = (Real.sqrt (v : ℝ) ^ 2) ^ (p / 2) := by rw [Real.rpow_two]
    _ = (v : ℝ) ^ (p / 2) := by rw [Real.sq_sqrt (NNReal.coe_nonneg v)]

/-- Scaling identity for absolute moments of centered real Gaussians. -/
lemma integral_abs_rpow_gaussianReal {p : ℝ} (hp : 0 < p) (v : ℝ≥0) :
    ∫ x, |x| ^ p ∂gaussianReal 0 v =
      (v : ℝ) ^ (p / 2) * gaussianAbsMoment p := by
  by_cases hv : v = 0
  · simp [hv, gaussianReal_zero_var, integral_dirac, Real.zero_rpow (div_pos hp two_pos).ne',
      Real.zero_rpow hp.ne', gaussianAbsMoment]
  let c : ℝ := Real.sqrt (v : ℝ)
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  have hmap : (gaussianReal 0 1).map (fun x ↦ c * x) = gaussianReal 0 v :=
    gaussianReal_map_sqrt v
  have hpow : ∀ x : ℝ, |c * x| ^ p = c ^ p * |x| ^ p := by
    intro x
    rw [abs_mul, abs_of_nonneg hc0, Real.mul_rpow hc0 (abs_nonneg x)]
  rw [← hmap, integral_map (by fun_prop) (by fun_prop), gaussianAbsMoment]
  simp_rw [hpow, integral_const_mul]
  rw [sqrt_rpow_eq_rpow_div_two]

/-- The standard Gaussian absolute moment is nonnegative. -/
lemma gaussianAbsMoment_nonneg (p : ℝ) : 0 ≤ gaussianAbsMoment p :=
  integral_nonneg fun _ ↦ Real.rpow_nonneg (abs_nonneg _) _

/-- Absolute moments of pre-Brownian increments scale with the elapsed time:
`∫ |B s - B t| ^ p = gaussianAbsMoment p * |s - t| ^ (p / 2)` for `0 < p`. -/
lemma integral_abs_sub_rpow_eq_of_isPreBrownianReal {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)
    {p : ℝ} (hp : 0 < p) (s t : ℝ≥0) :
    ∫ ω, |B s ω - B t ω| ^ p ∂μ = gaussianAbsMoment p * |(s : ℝ) - t| ^ (p / 2) := by
  have hf : AEStronglyMeasurable (fun x : ℝ ↦ |x| ^ p)
      (gaussianReal 0 (nndist (s : ℝ) (t : ℝ))) := by
    fun_prop
  have hcomp : (fun ω ↦ |B s ω - B t ω| ^ p) = (fun x : ℝ ↦ |x| ^ p) ∘ (B s - B t) := rfl
  have hdist : (nndist (s : ℝ) (t : ℝ) : ℝ) = |(s : ℝ) - t| := by
    rw [nnDist_eq_nnNorm, coe_nnNorm, Real.norm_eq_abs]
  rw [hcomp, (hB.hasLaw_sub s t).integral_comp hf, mul_comm, ← hdist]
  simpa using integral_abs_rpow_gaussianReal hp (nndist (s : ℝ) (t : ℝ))

end CKMA
