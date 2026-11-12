/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.L1

/-!
# Gaussian moments of pre-Brownian increments

A centered Gaussian of variance `v` is the law of `√v` times a standard normal. Absolute moments
therefore scale by `v ^ (p / 2)`. Pre-Brownian increments are exactly those Gaussians, so they
obey the Kolmogorov moment bound with every exponent strictly above `2`.
-/

@[expose] public section

noncomputable section

namespace CKMA

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

/-- Absolute moment of order `p` of a standard real Gaussian. -/
def gaussianAbsMoment (p : ℝ) : ℝ :=
  ∫ x, |x| ^ p ∂gaussianReal 0 1

/-- The standard Gaussian absolute moment of positive order is finite. -/
lemma integrable_abs_rpow_gaussianReal {p : ℝ} (hp : 0 < p) :
    Integrable (fun x : ℝ ↦ |x| ^ p) (gaussianReal 0 1) := by
  have hmem : MemLp (id : ℝ → ℝ) (Real.toNNReal p) (gaussianReal 0 1) :=
    memLp_id_gaussianReal (Real.toNNReal p)
  have hq0 : (Real.toNNReal p : ℝ≥0∞) ≠ 0 := by simp [hp]
  have hqtop : (Real.toNNReal p : ℝ≥0∞) ≠ ∞ := by simp
  have hint := hmem.integrable_norm_rpow hq0 hqtop
  have hpow : (Real.toNNReal p : ℝ) = p := Real.coe_toNNReal p hp.le
  simpa [Real.norm_eq_abs, hpow] using hint

/-- `√v` raised to `p` is the variance raised to `p / 2`. -/
lemma sqrt_rpow_eq_rpow_div_two {p : ℝ} {v : ℝ≥0} :
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
  have hmap : (gaussianReal 0 1).map (fun x ↦ c * x) = gaussianReal 0 v := by
    have h := gaussianReal_map_const_mul (μ := 0) (v := 1) c
    have hv' : NNReal.mk (c ^ 2) (sq_nonneg c) = v := by
      ext
      simp [c, Real.sq_sqrt (NNReal.coe_nonneg v)]
    rw [h, hv']
    simp
  have hpow : ∀ x : ℝ, |c * x| ^ p = c ^ p * |x| ^ p := by
    intro x
    rw [abs_mul, abs_of_nonneg hc0, Real.mul_rpow hc0 (abs_nonneg x)]
  rw [← hmap, integral_map (by fun_prop) (by fun_prop), gaussianAbsMoment]
  simp_rw [hpow, integral_const_mul]
  rw [sqrt_rpow_eq_rpow_div_two]

/-- Absolute moments of every positive order are integrable for every centered Gaussian. -/
lemma integrable_abs_rpow_gaussianReal_var {p : ℝ} (hp : 0 < p) (v : ℝ≥0) :
    Integrable (fun x : ℝ ↦ |x| ^ p) (gaussianReal 0 v) := by
  by_cases hv : v = 0
  · rw [hv, gaussianReal_zero_var]
    exact integrable_dirac (by simp)
  let c : ℝ := Real.sqrt (v : ℝ)
  have hmap : (gaussianReal 0 1).map (fun x ↦ c * x) = gaussianReal 0 v := by
    have h := gaussianReal_map_const_mul (μ := 0) (v := 1) c
    have hv' : NNReal.mk (c ^ 2) (sq_nonneg c) = v := by
      ext
      simp [c, Real.sq_sqrt (NNReal.coe_nonneg v)]
    rw [h, hv']
    simp
  have hint : Integrable (fun x : ℝ ↦ |c * x| ^ p) (gaussianReal 0 1) := by
    have hpow : (fun x : ℝ ↦ |c * x| ^ p) = fun x ↦ |x| ^ p * c ^ p := by
      funext x
      rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _),
        Real.mul_rpow (Real.sqrt_nonneg _) (abs_nonneg x), mul_comm]
    rw [hpow]
    exact (integrable_abs_rpow_gaussianReal hp).mul_const (c ^ p)
  rw [← hmap]
  refine (integrable_map_measure (by fun_prop) (by fun_prop)).2 ?_
  simpa [Function.comp_def] using hint

/-- The scaled absolute moment is nonnegative. -/
lemma gaussianAbsMoment_nonneg {p : ℝ} (hp : 0 < p) : 0 ≤ gaussianAbsMoment p := by
  have _ : 0 ≤ p := hp.le
  exact integral_nonneg fun _ ↦ Real.rpow_nonneg (abs_nonneg _) _

/-- Absolute moments of pre-Brownian increments scale with the elapsed time. -/
lemma IsPreBrownianReal.integral_abs_sub_rpow {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)
    {p : ℝ} (hp : 0 < p) (s t : ℝ≥0) :
    ∫ ω, |B s ω - B t ω| ^ p ∂μ =
      (nndist (s : ℝ) (t : ℝ) : ℝ) ^ (p / 2) * gaussianAbsMoment p := by
  have hlaw := hB.hasLaw_sub s t
  have hf : AEStronglyMeasurable (fun x : ℝ ↦ |x| ^ p)
      (gaussianReal 0 (nndist (s : ℝ) (t : ℝ))) := by
    fun_prop
  have hcomp : (fun ω ↦ |B s ω - B t ω| ^ p) =
      (fun x : ℝ ↦ |x| ^ p) ∘ (B s - B t) := by
    funext ω
    rfl
  rw [hcomp, hlaw.integral_comp hf]
  simpa using integral_abs_rpow_gaussianReal hp (nndist (s : ℝ) (t : ℝ))

/-- Kolmogorov bound for a pre-Brownian increment of order `p > 0`. -/
lemma IsPreBrownianReal.integral_abs_sub_rpow_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)
    {p : ℝ} (hp : 0 < p) (s t : ℝ≥0) :
    ∫ ω, |B s ω - B t ω| ^ p ∂μ ≤
      gaussianAbsMoment p * |(s : ℝ) - t| ^ (p / 2) := by
  rw [IsPreBrownianReal.integral_abs_sub_rpow hB hp s t, mul_comm]
  have hdist : (nndist (s : ℝ) (t : ℝ) : ℝ) = |(s : ℝ) - t| := by
    rw [nndist_eq_nnnorm, coe_nnnorm, Real.norm_eq_abs]
  rw [hdist]

end CKMA
