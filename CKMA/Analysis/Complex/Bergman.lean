/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.Complex.Bergman.Monomial
public import Mathlib.Analysis.InnerProductSpace.Adjoint

import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.Sequences
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.RingTheory.Polynomial.Pochhammer
import TauCeti.MeasureTheory.Integral.PolarCoord

/-!
# Weighted disk Bergman spaces

The normalized disk measure has density `(α+1)(1-|z|²)^α/π` for `α > -1`.
The principal-power kernel `(1-z conj(w))^(-α-2)` reproduces square-integrable
holomorphic functions. Monomial norms, closedness of the analytic subspace and the
orthogonal projection describe the Hilbert case; kernel bounds also cover `1 < p < ∞`.

Sources: GAPS 42.51 and 42.52.

The measure, the kernel and the monomial computations are in
`CKMA.Analysis.Complex.Bergman.Monomial`. The reproducing
formula matches Taylor coefficients with the binomial series of the kernel. Closedness
is locally uniform convergence of holomorphic representatives, together with convergence
in measure. The orthogonal projection is `Submodule.starProjection` on that closed
subspace, and its norm is one because the constants belong to the subspace.

## Main definitions

* `CKMA.bergmanSet`: analytic subspace of weighted `Lᵖ` on the unit disk.
* `CKMA.bergmanSubmodule`: the Bergman space `A²_α(𝔻)` as a subspace of weighted `L²`.
* `CKMA.bergmanIntegral`: weighted Bergman integral operator.

## Main results

* `CKMA.bergman_reproducing`: reproducing formula on `A²_α(𝔻)`.
* `CKMA.isClosed_bergmanSet`: closedness of `A²_α(𝔻)` in `L²`.
* `CKMA.exists_bergmanProjection`: orthogonal Bergman projection on `L²`.
* `CKMA.bergmanIntegral_bounded`: `Lᵖ` boundedness of the Bergman integral for `1 < p < ∞`.
-/

public section

noncomputable section

namespace CKMA

open Complex Filter MeasureTheory Real Set intervalIntegral
open scoped ENNReal ComplexConjugate InnerProductSpace

/-- The analytic part of a weighted `Lᵖ` space, expressed through an a.e. holomorphic
  representative. -/
@[expose]
def bergmanSet (α : ℝ) (p : ℝ≥0∞) : Set (Lp ℂ p (bergmanMeasure α)) :=
  {u | ∃ f : ℂ → ℂ, DifferentiableOn ℂ f (Metric.ball 0 1) ∧ u =ᵐ[bergmanMeasure α] f}

/-- The integral formula for the weighted Bergman projection. -/
@[expose]
def bergmanIntegral (α : ℝ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∫ w, bergmanKernel α z w * f w ∂bergmanMeasure α

/-- Membership in `bergmanSet` is having an a.e. representative holomorphic on the disk. -/
theorem mem_bergmanSet {α : ℝ} {p : ℝ≥0∞} {u : Lp ℂ p (bergmanMeasure α)} :
    u ∈ bergmanSet α p ↔
      ∃ f : ℂ → ℂ, DifferentiableOn ℂ f (Metric.ball 0 1) ∧ u =ᵐ[bergmanMeasure α] f :=
  Iff.rfl

/-- The Bergman integral is `∫ K(z, w) f(w) dA_α(w)`. -/
theorem bergmanIntegral_def (α : ℝ) (f : ℂ → ℂ) (z : ℂ) :
    bergmanIntegral α f z = ∫ w, bergmanKernel α z w * f w ∂bergmanMeasure α :=
  rfl

/-- Square-integrable functions are reproduced by integrating the kernel series termwise. -/
private lemma integral_bergmanKernel_mul_tsum {α : ℝ} (hα : -1 < α) {f : ℂ → ℂ}
    (hLp : MemLp f 2 (bergmanMeasure α)) {z : ℂ} (hz : ‖z‖ < 1) :
    ∫ w, bergmanKernel α z w * f w ∂bergmanMeasure α =
      ∑' n : ℕ, (bergmanMonomialNormSq α n : ℂ)⁻¹ * z ^ n *
        ∫ w, conj (w ^ n) * f w ∂bergmanMeasure α := by
  let c : ℕ → ℝ := bergmanMonomialNormSq α
  let term : ℕ → ℂ → ℂ := fun n w => (c n : ℂ)⁻¹ * z ^ n * conj (w ^ n)
  let F : ℕ → ℂ → ℂ := fun n w => term n w * f w
  have hterm : ∀ w, ‖w‖ < 1 → ∑' n, term n w = bergmanKernel α z w := by
    intro w hw
    have hzw : ‖z * conj w‖ < 1 := by
      rw [norm_mul, Complex.norm_conj]
      have h1 : ‖z‖ * ‖w‖ ≤ ‖z‖ :=
        (mul_le_mul_of_nonneg_left hw.le (norm_nonneg z)).trans_eq (mul_one ‖z‖)
      exact h1.trans_lt hz
    exact (bergmanKernel_eq_tsum hα hzw).symm
  have hint : ∀ n, Integrable (F n) (bergmanMeasure α) := by
    intro n
    have hmul : Integrable (fun w => conj (w ^ n) * f w) (bergmanMeasure α) :=
      memLp_one_iff_integrable.mp ((memLp_conj_monomial hα n).mul hLp)
    have hfun : F n = fun w => ((c n : ℂ)⁻¹ * z ^ n) * (conj (w ^ n) * f w) := by
      ext w
      dsimp only [F, term]
      rw [mul_assoc]
    rw [hfun]
    exact hmul.const_mul _
  have hnorm : ∀ n w, ‖F n w‖ = (‖z‖ ^ n / c n) * ‖w‖ ^ n * ‖f w‖ := by
    intro n w
    dsimp only [F, term]
    rw [norm_mul, norm_mul, norm_mul, norm_inv, norm_pow, norm_conj, norm_pow]
    have hcpos : 0 < c n := by
      dsimp only [c]
      exact bergmanMonomialNormSq_pos hα n
    rw [Complex.norm_of_nonneg hcpos.le, mul_comm ((c n)⁻¹), ← div_eq_mul_inv]
  have hf2 : MemLp f (ENNReal.ofReal 2) (bergmanMeasure α) := by
    simpa [ENNReal.ofReal_ofNat] using hLp
  let C : ℝ := (∫ w, ‖f w‖ ^ 2 ∂bergmanMeasure α) ^ (1 / 2 : ℝ)
  have hbound : ∀ n, ∫ w, ‖F n w‖ ∂bergmanMeasure α ≤
      C * (‖z‖ ^ n / Real.sqrt (c n)) := by
    intro n
    have hmono : MemLp (fun w : ℂ => w ^ n) (ENNReal.ofReal 2) (bergmanMeasure α) := by
      simpa [ENNReal.ofReal_ofNat] using memLp_monomial hα n
    have hintnorm : ∫ w, ‖F n w‖ ∂bergmanMeasure α =
        ∫ w, (‖z‖ ^ n / c n) * ‖w‖ ^ n * ‖f w‖ ∂bergmanMeasure α :=
      integral_congr_ae <| Eventually.of_forall fun w => hnorm n w
    have hsplit : (fun w : ℂ => (‖z‖ ^ n / c n) * ‖w‖ ^ n * ‖f w‖) =
        fun w => (‖z‖ ^ n / c n) * (‖w‖ ^ n * ‖f w‖) := by
      ext w
      ring
    rw [hintnorm, hsplit, MeasureTheory.integral_const_mul]
    have hpow : (fun w : ℂ => ‖w‖ ^ n * ‖f w‖) = fun w => ‖w ^ n‖ * ‖f w‖ := by
      ext w
      rw [norm_pow]
    rw [hpow]
    have hH := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two hmono hf2
    have hsq : ∫ a : ℂ, ‖a ^ n‖ ^ (2 : ℝ) ∂bergmanMeasure α = c n := by
      simp_rw [Real.rpow_two]
      dsimp only [c, bergmanMonomialNormSq]
      exact integral_norm_monomial_sq hα n
    have hCsqrt : Real.sqrt (∫ w, ‖f w‖ ^ 2 ∂bergmanMeasure α) = C := by
      dsimp only [C]
      exact Real.sqrt_eq_rpow _
    have hCR : (∫ a : ℂ, ‖f a‖ ^ (2 : ℝ) ∂bergmanMeasure α) ^ (1 / 2 : ℝ) = C := by
      simp_rw [Real.rpow_two]
      rw [← Real.sqrt_eq_rpow]
      exact hCsqrt
    rw [hsq, hCR, ← Real.sqrt_eq_rpow] at hH
    have hnonneg : 0 ≤ ‖z‖ ^ n / c n :=
      div_nonneg (pow_nonneg (norm_nonneg z) n) (bergmanMonomialNormSq_pos hα n).le
    have hmul := mul_le_mul_of_nonneg_left hH hnonneg
    have halg : (‖z‖ ^ n / c n) * Real.sqrt (c n) = ‖z‖ ^ n / Real.sqrt (c n) := by
      have hcpos : 0 < c n := by
        dsimp only [c]
        exact bergmanMonomialNormSq_pos hα n
      have hs0 : Real.sqrt (c n) ≠ 0 := (Real.sqrt_ne_zero').2 hcpos
      rw [div_mul_eq_mul_div]
      conv_lhs =>
        arg 2
        rw [← Real.mul_self_sqrt hcpos.le]
      exact mul_div_mul_right _ _ hs0
    calc
      (‖z‖ ^ n / c n) * ∫ w, ‖w ^ n‖ * ‖f w‖ ∂bergmanMeasure α
          ≤ (‖z‖ ^ n / c n) * (Real.sqrt (c n) * C) := hmul
      _ = C * (‖z‖ ^ n / Real.sqrt (c n)) := by rw [← mul_assoc, halg, mul_comm]
  have hsum : Summable fun n => ∫ w, ‖F n w‖ ∂bergmanMeasure α :=
    Summable.of_nonneg_of_le (fun n => integral_nonneg fun _ => norm_nonneg _) hbound
      ((summable_div_sqrt_monomialNormSq hα (norm_nonneg z) hz).mul_left C)
  have hswap := integral_tsum_of_summable_integral_norm hint hsum
  have hae : (fun w => ∑' n, F n w) =ᵐ[bergmanMeasure α]
      fun w => bergmanKernel α z w * f w := by
    unfold Filter.EventuallyEq
    rw [ae_iff]
    refine measure_mono_null ?_ (bergmanMeasure_compl_ball α)
    intro w hw
    by_contra hball
    have hwlt : ‖w‖ < 1 := lt_of_not_ge hball
    apply hw
    dsimp only [F]
    rw [tsum_mul_right, hterm w hwlt]
  have hpull : ∀ n, ∫ w, F n w ∂bergmanMeasure α =
      (c n : ℂ)⁻¹ * z ^ n * ∫ w, conj (w ^ n) * f w ∂bergmanMeasure α := by
    intro n
    have hfun : F n = fun w => ((c n : ℂ)⁻¹ * z ^ n) * (conj (w ^ n) * f w) := by
      ext w
      dsimp only [F, term]
      rw [mul_assoc]
    rw [hfun, MeasureTheory.integral_const_mul]
  calc
    ∫ w, bergmanKernel α z w * f w ∂bergmanMeasure α
        = ∫ w, ∑' n, F n w ∂bergmanMeasure α := integral_congr_ae hae.symm
    _ = ∑' n, ∫ w, F n w ∂bergmanMeasure α := hswap.symm
    _ = ∑' n, (c n : ℂ)⁻¹ * z ^ n *
          ∫ w, conj (w ^ n) * f w ∂bergmanMeasure α := tsum_congr hpull

/-- The squared `L²` norm is the integral of the squared pointwise norm. -/
private lemma sq_norm_eq_integral_sq {α : ℝ} (v : Lp ℂ 2 (bergmanMeasure α)) :
    ‖v‖ ^ 2 = ∫ z, ‖v z‖ ^ 2 ∂bergmanMeasure α := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ) v]
  have hint : ∫ z, inner ℂ (v z) (v z) ∂bergmanMeasure α =
      ∫ z, ((‖v z‖ ^ 2 : ℝ) : ℂ) ∂bergmanMeasure α := by
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    dsimp only
    rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ)]
    exact (RCLike.ofReal_pow (‖v z‖) 2).symm
  rw [L2.inner_def, hint, integral_complex_ofReal]
  exact RCLike.ofReal_re _

/-- One monomial coefficient is controlled by Cauchy–Schwarz. -/
private lemma norm_integral_conj_pow_le {α : ℝ} (hα : -1 < α) {f : ℂ → ℂ}
    (hLp : MemLp f 2 (bergmanMeasure α)) (n : ℕ) :
    ‖∫ w, conj (w ^ n) * f w ∂bergmanMeasure α‖ ≤
      Real.sqrt (bergmanMonomialNormSq α n) *
        Real.sqrt (∫ w, ‖f w‖ ^ 2 ∂bergmanMeasure α) := by
  have hle : ‖∫ w, conj (w ^ n) * f w ∂bergmanMeasure α‖ ≤
      ∫ w, ‖conj (w ^ n) * f w‖ ∂bergmanMeasure α :=
    norm_integral_le_integral_norm _
  have hsplit : ∫ w, ‖conj (w ^ n) * f w‖ ∂bergmanMeasure α =
      ∫ w, ‖w ^ n‖ * ‖f w‖ ∂bergmanMeasure α := by
    refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    dsimp only
    rw [norm_mul, norm_conj]
  rw [hsplit] at hle
  have hmono : MemLp (fun w : ℂ => w ^ n) (ENNReal.ofReal 2) (bergmanMeasure α) := by
    simpa [ENNReal.ofReal_ofNat] using memLp_monomial hα n
  have hf2 : MemLp f (ENNReal.ofReal 2) (bergmanMeasure α) := by
    simpa [ENNReal.ofReal_ofNat] using hLp
  have hH := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two hmono hf2
  have hsq : ∫ a : ℂ, ‖a ^ n‖ ^ (2 : ℝ) ∂bergmanMeasure α =
      bergmanMonomialNormSq α n := by
    simp_rw [Real.rpow_two]
    exact integral_norm_monomial_sq hα n
  have hfsq : (∫ a : ℂ, ‖f a‖ ^ (2 : ℝ) ∂bergmanMeasure α) ^ (1 / 2 : ℝ) =
      Real.sqrt (∫ a : ℂ, ‖f a‖ ^ 2 ∂bergmanMeasure α) := by
    simp_rw [Real.rpow_two]
    rw [← Real.sqrt_eq_rpow]
  rw [hsq, ← Real.sqrt_eq_rpow, hfsq] at hH
  exact hle.trans hH

/-- The integral operator is pointwise bounded by the monomial majorant. -/
private lemma norm_bergmanIntegral_le {α : ℝ} (hα : -1 < α) {f : ℂ → ℂ}
    (hLp : MemLp f 2 (bergmanMeasure α)) {z : ℂ} (hz : ‖z‖ < 1) :
    ‖bergmanIntegral α f z‖ ≤
      (∑' n : ℕ, ‖z‖ ^ n / Real.sqrt (bergmanMonomialNormSq α n)) *
        Real.sqrt (∫ w, ‖f w‖ ^ 2 ∂bergmanMeasure α) := by
  rw [bergmanIntegral, integral_bergmanKernel_mul_tsum hα hLp hz]
  let c : ℕ → ℝ := bergmanMonomialNormSq α
  let term : ℕ → ℂ := fun n =>
    (c n : ℂ)⁻¹ * z ^ n * ∫ w, conj (w ^ n) * f w ∂bergmanMeasure α
  let C : ℝ := Real.sqrt (∫ w, ‖f w‖ ^ 2 ∂bergmanMeasure α)
  have hterm : ∀ n, ‖term n‖ ≤ C * (‖z‖ ^ n / Real.sqrt (c n)) := by
    intro n
    dsimp only [term]
    rw [norm_mul, norm_mul, norm_inv, norm_pow]
    have hcpos : 0 < c n := by
      dsimp only [c]
      exact bergmanMonomialNormSq_pos hα n
    rw [Complex.norm_of_nonneg hcpos.le, mul_comm ((c n)⁻¹), ← div_eq_mul_inv]
    have hintle := norm_integral_conj_pow_le hα hLp n
    have hnonneg : 0 ≤ ‖z‖ ^ n / c n :=
      div_nonneg (pow_nonneg (norm_nonneg z) n) hcpos.le
    have hmul := mul_le_mul_of_nonneg_left hintle hnonneg
    have halg : (‖z‖ ^ n / c n) * Real.sqrt (c n) = ‖z‖ ^ n / Real.sqrt (c n) := by
      have hs0 : Real.sqrt (c n) ≠ 0 := (Real.sqrt_ne_zero').2 hcpos
      rw [div_mul_eq_mul_div]
      conv_lhs =>
        arg 2
        rw [← Real.mul_self_sqrt hcpos.le]
      exact mul_div_mul_right _ _ hs0
    have hCdef : Real.sqrt (∫ w, ‖f w‖ ^ 2 ∂bergmanMeasure α) = C := by
      dsimp only [C]
    rw [hCdef] at hmul
    calc
      (‖z‖ ^ n / c n) * ‖∫ w, conj (w ^ n) * f w ∂bergmanMeasure α‖
          ≤ (‖z‖ ^ n / c n) * (Real.sqrt (c n) * C) := hmul
      _ = C * (‖z‖ ^ n / Real.sqrt (c n)) := by rw [← mul_assoc, halg, mul_comm]
  have hmajor : Summable fun n => C * (‖z‖ ^ n / Real.sqrt (c n)) :=
    (summable_div_sqrt_monomialNormSq hα (norm_nonneg z) hz).mul_left C
  have hsumm : Summable fun n => ‖term n‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hmajor
  calc
    ‖∑' n, term n‖ ≤ ∑' n, ‖term n‖ := norm_tsum_le_tsum_norm hsumm
    _ ≤ ∑' n, C * (‖z‖ ^ n / Real.sqrt (c n)) := Summable.tsum_le_tsum hterm hsumm hmajor
    _ = C * ∑' n, ‖z‖ ^ n / Real.sqrt (c n) := tsum_mul_left
    _ = (∑' n, ‖z‖ ^ n / Real.sqrt (bergmanMonomialNormSq α n)) * C := by
      rw [mul_comm]

/-- **42.51**: reproduction on the weighted square-integrable holomorphic space. -/
theorem bergman_reproducing {α : ℝ} (hα : -1 < α) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (Metric.ball 0 1)) (hLp : MemLp f 2 (bergmanMeasure α))
    {z : ℂ} (hz : ‖z‖ < 1) : bergmanIntegral α f z = f z := by
  rw [bergmanIntegral, integral_bergmanKernel_mul_tsum hα hLp hz]
  have hcoeff : ∀ n : ℕ, (bergmanMonomialNormSq α n : ℂ)⁻¹ * z ^ n *
      ∫ w, conj (w ^ n) * f w ∂bergmanMeasure α =
      taylorCoefficient f n * z ^ n := by
    intro n
    rw [integral_conj_pow_mul_holomorphic hα hf hLp n]
    have hc0 : (bergmanMonomialNormSq α n : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (bergmanMonomialNormSq_ne_zero hα n)
    set a : ℂ := (bergmanMonomialNormSq α n : ℂ)
    set b : ℂ := z ^ n
    set t : ℂ := taylorCoefficient f n
    calc
      a⁻¹ * b * (t * a) = (a⁻¹ * b * t) * a := by rw [← mul_assoc]
      _ = (t * (a⁻¹ * b)) * a := by rw [mul_comm (a⁻¹ * b) t]
      _ = t * ((a⁻¹ * b) * a) := by rw [mul_assoc]
      _ = t * (a⁻¹ * (b * a)) := by rw [mul_assoc]
      _ = t * (a⁻¹ * (a * b)) := by rw [mul_comm b a]
      _ = t * ((a⁻¹ * a) * b) := by
        conv_lhs =>
          arg 2
          rw [← mul_assoc]
      _ = t * (b * (a⁻¹ * a)) := by rw [mul_comm (a⁻¹ * a) b]
      _ = t * (b * 1) := by rw [inv_mul_cancel₀ hc0]
      _ = t * b := by rw [mul_one]
  have hzball : z ∈ Metric.ball (0 : ℂ) 1 := by
    rwa [Metric.mem_ball, dist_zero_right]
  have htaylor := taylorSeries_eq_on_ball' hzball hf
  rw [tsum_congr hcoeff, ← htaylor]
  refine tsum_congr fun n => ?_
  rw [taylorCoefficient_def, sub_zero, mul_assoc]

/-- A holomorphic representative is bounded by the same majorant as the integral operator. -/
private lemma norm_holomorphic_apply_le {α : ℝ} (hα : -1 < α) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (Metric.ball 0 1)) (hLp : MemLp f 2 (bergmanMeasure α))
    {z : ℂ} (hz : ‖z‖ < 1) :
    ‖f z‖ ≤ (∑' n : ℕ, ‖z‖ ^ n / Real.sqrt (bergmanMonomialNormSq α n)) *
      Real.sqrt (∫ w, ‖f w‖ ^ 2 ∂bergmanMeasure α) := by
  rw [← bergman_reproducing hα hf hLp hz]
  exact norm_bergmanIntegral_le hα hLp hz

/-- Replacing an `L²` class by an a.e. representative preserves the square-integral norm. -/
private lemma sqrt_integral_ae_eq_norm {α : ℝ} {u : Lp ℂ 2 (bergmanMeasure α)} {f : ℂ → ℂ}
    (h : (u : ℂ → ℂ) =ᵐ[bergmanMeasure α] f) :
    Real.sqrt (∫ z, ‖f z‖ ^ 2 ∂bergmanMeasure α) = ‖u‖ := by
  have hcongr : ∫ z, ‖f z‖ ^ 2 ∂bergmanMeasure α =
      ∫ z, ‖u z‖ ^ 2 ∂bergmanMeasure α := by
    refine integral_congr_ae ?_
    filter_upwards [h] with z hz
    rw [hz]
  rw [hcongr, ← sq_norm_eq_integral_sq, Real.sqrt_sq (norm_nonneg _)]

/-- Values of holomorphic representatives are Lipschitz in the `L²` distance. -/
private lemma norm_representative_sub_le {α : ℝ} (hα : -1 < α)
    {u v : Lp ℂ 2 (bergmanMeasure α)} {f g : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (Metric.ball 0 1))
    (hg : DifferentiableOn ℂ g (Metric.ball 0 1))
    (hu : (u : ℂ → ℂ) =ᵐ[bergmanMeasure α] f)
    (hv : (v : ℂ → ℂ) =ᵐ[bergmanMeasure α] g) {z : ℂ} (hz : ‖z‖ < 1) :
    ‖f z - g z‖ ≤
      (∑' n : ℕ, ‖z‖ ^ n / Real.sqrt (bergmanMonomialNormSq α n)) * ‖u - v‖ := by
  have hsub : ((u - v : Lp ℂ 2 (bergmanMeasure α)) : ℂ → ℂ) =ᵐ[bergmanMeasure α]
      f - g := (Lp.coeFn_sub u v).trans (hu.sub hv)
  have hLp : MemLp (f - g) 2 (bergmanMeasure α) :=
    MemLp.ae_eq hsub (Lp.memLp (u - v))
  have hle := norm_holomorphic_apply_le hα (hf.sub hg) hLp hz
  rw [sqrt_integral_ae_eq_norm hsub] at hle
  simpa [Pi.sub_apply] using hle

/-- The monomial majorant increases with the radius. -/
private lemma sum_div_sqrt_le {α : ℝ} (hα : -1 < α) {r s : ℝ} (hr0 : 0 ≤ r) (hrs : r ≤ s)
    (hs1 : s < 1) :
    ∑' n : ℕ, r ^ n / Real.sqrt (bergmanMonomialNormSq α n) ≤
      ∑' n : ℕ, s ^ n / Real.sqrt (bergmanMonomialNormSq α n) := by
  refine Summable.tsum_le_tsum (fun n => ?_)
    (summable_div_sqrt_monomialNormSq hα hr0 (hrs.trans_lt hs1))
    (summable_div_sqrt_monomialNormSq hα (hr0.trans hrs) hs1)
  exact div_le_div_of_nonneg_right (pow_le_pow_left₀ hr0 hrs n) (Real.sqrt_nonneg _)

/-- `M * ε / (M + 1) < ε` for `0 ≤ M` and `0 < ε`. -/
private lemma mul_majorant_lt {M ε : ℝ} (hM : 0 ≤ M) (hε : 0 < ε) :
    M * (ε / (M + 1)) < ε := by
  have hM1 : 0 < M + 1 := by linarith [hM]
  have hfrac : M / (M + 1) < 1 := by
    rw [div_lt_one hM1]
    linarith [hM]
  calc
    M * (ε / (M + 1)) = (ε / (M + 1)) * M := by rw [mul_comm]
    _ = ε * M / (M + 1) := div_mul_eq_mul_div _ _ _
    _ = ε * (M / (M + 1)) := by rw [← mul_div_assoc]
    _ < ε * 1 := mul_lt_mul_of_pos_left hfrac hε
    _ = ε := mul_one ε

/-- The weighted Bergman space `A²_α(𝔻)`: the holomorphic classes in weighted `L²`, as a
subspace. Its carrier is `bergmanSet α 2`. -/
@[expose]
def bergmanSubmodule (α : ℝ) : Submodule ℂ (Lp ℂ 2 (bergmanMeasure α)) where
  carrier := bergmanSet α 2
  add_mem' := by
    rintro u v ⟨fu, hfu, hue⟩ ⟨fv, hfv, hve⟩
    exact ⟨fu + fv, hfu.add hfv, (Lp.coeFn_add u v).trans (hue.add hve)⟩
  zero_mem' := ⟨(0 : ℂ → ℂ), differentiableOn_const (0 : ℂ),
    Lp.coeFn_zero ℂ 2 (bergmanMeasure α)⟩
  smul_mem' := by
    rintro c u ⟨fu, hfu, hue⟩
    exact ⟨c • fu, hfu.const_smul c, (Lp.coeFn_smul c u).trans (hue.const_smul c)⟩

/-- Membership in the Bergman subspace is membership in `bergmanSet α 2`. -/
theorem mem_bergmanSubmodule {α : ℝ} {u : Lp ℂ 2 (bergmanMeasure α)} :
    u ∈ bergmanSubmodule α ↔ u ∈ bergmanSet α 2 :=
  Iff.rfl

/-- The carrier of the Bergman subspace is `bergmanSet α 2`. -/
theorem coe_bergmanSubmodule (α : ℝ) :
    (bergmanSubmodule α : Set (Lp ℂ 2 (bergmanMeasure α))) = bergmanSet α 2 :=
  rfl

/-- The constant monomial has weighted norm one. -/
private lemma bergmanMonomialNormSq_zero {α : ℝ} (hα : -1 < α) :
    bergmanMonomialNormSq α 0 = 1 := by
  dsimp only [bergmanMonomialNormSq]
  rw [Nat.factorial_zero, Nat.cast_one, mul_one, Nat.cast_zero, zero_add]
  exact div_self (Real.Gamma_pos_of_pos (by linarith : 0 < α + 2)).ne'

/-- The monomial `z ↦ z ^ n` as an element of the weighted `L²` space. -/
private def bergmanMonomialLp {α : ℝ} (hα : -1 < α) (n : ℕ) : Lp ℂ 2 (bergmanMeasure α) :=
  (memLp_monomial hα n).toLp fun z => z ^ n

/-- The monomials lie in the holomorphic subspace. -/
private lemma bergmanMonomialLp_mem {α : ℝ} (hα : -1 < α) (n : ℕ) :
    bergmanMonomialLp hα n ∈ bergmanSubmodule α :=
  ⟨fun z => z ^ n, (differentiable_pow n).differentiableOn,
    (memLp_monomial hα n).coeFn_toLp⟩

/-- The constant function one has weighted norm one. -/
private lemma norm_sq_bergmanMonomialLp_zero {α : ℝ} (hα : -1 < α) :
    ‖bergmanMonomialLp hα 0‖ ^ 2 = 1 := by
  rw [sq_norm_eq_integral_sq]
  have hcongr : ∫ z, ‖bergmanMonomialLp hα 0 z‖ ^ 2 ∂bergmanMeasure α =
      ∫ z, ‖z ^ (0 : ℕ)‖ ^ 2 ∂bergmanMeasure α := by
    refine integral_congr_ae ?_
    filter_upwards [(memLp_monomial hα 0).coeFn_toLp] with z hz
    simp only [bergmanMonomialLp]
    rw [hz]
  rw [hcongr, integral_norm_monomial_sq hα 0]
  exact bergmanMonomialNormSq_zero hα

/-- **42.51**: the holomorphic `L²` subspace is closed. -/
theorem isClosed_bergmanSet {α : ℝ} (hα : -1 < α) : IsClosed (bergmanSet α 2) := by
  refine IsSeqClosed.isClosed ?_
  intro u x hu hx
  choose f hfdiff hfae using hu
  have hCauchy : ∀ z, ‖z‖ < 1 → CauchySeq fun n => f n z := by
    intro z hz
    rw [Metric.cauchySeq_iff]
    intro ε hε
    set M : ℝ := ∑' n : ℕ, ‖z‖ ^ n / Real.sqrt (bergmanMonomialNormSq α n)
    have hM0 : 0 ≤ M :=
      tsum_nonneg fun n => div_nonneg (pow_nonneg (norm_nonneg z) n) (Real.sqrt_nonneg _)
    set δ : ℝ := ε / (M + 1)
    have hδ : 0 < δ := div_pos hε (by linarith [hM0])
    have hcu : CauchySeq u := hx.cauchySeq
    rw [Metric.cauchySeq_iff] at hcu
    obtain ⟨N, hN⟩ := hcu δ hδ
    refine ⟨N, fun m hm n hn => ?_⟩
    have hdist : ‖u m - u n‖ ≤ δ := by
      rw [← dist_eq_norm]
      exact (hN m hm n hn).le
    have hle := norm_representative_sub_le hα (hfdiff m) (hfdiff n) (hfae m) (hfae n) hz
    rw [dist_eq_norm]
    calc
      ‖f m z - f n z‖ ≤ M * ‖u m - u n‖ := hle
      _ ≤ M * δ := mul_le_mul_of_nonneg_left hdist hM0
      _ < ε := by
        dsimp only [δ]
        exact mul_majorant_lt hM0 hε
  let F : ℂ → ℂ := fun z =>
    if hz : ‖z‖ < 1 then limUnder atTop (fun n => f n z) else 0
  have hFtend : ∀ z, ‖z‖ < 1 → Tendsto (fun n => f n z) atTop (nhds (F z)) := by
    intro z hz
    have hlim := (hCauchy z hz).tendsto_limUnder
    dsimp only [F]
    rw [dite_eq_left hz]
    exact hlim
  have hlu : TendstoLocallyUniformlyOn f F atTop (Metric.ball (0 : ℂ) 1) := by
    rw [Metric.tendstoLocallyUniformlyOn_iff]
    intro ε hε z hzball
    rw [Metric.mem_ball, dist_zero_right] at hzball
    set r : ℝ := (‖z‖ + 1) / 2
    have hr0 : 0 ≤ r := by
      dsimp only [r]
      linarith [hzball, norm_nonneg z]
    have hr1 : r < 1 := by
      dsimp only [r]
      linarith [hzball]
    have hrad : 0 < r - ‖z‖ := by
      dsimp only [r]
      linarith [hzball]
    refine ⟨Metric.ball z (r - ‖z‖),
      mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds z hrad), ?_⟩
    set Mr : ℝ := ∑' n : ℕ, r ^ n / Real.sqrt (bergmanMonomialNormSq α n)
    have hMr0 : 0 ≤ Mr :=
      tsum_nonneg fun n => div_nonneg (pow_nonneg hr0 n) (Real.sqrt_nonneg _)
    set δ : ℝ := ε / (Mr + 1)
    have hδ : 0 < δ := div_pos hε (by linarith [hMr0])
    have hcu : CauchySeq u := hx.cauchySeq
    rw [Metric.cauchySeq_iff] at hcu
    obtain ⟨N, hN⟩ := hcu δ hδ
    rw [eventually_atTop]
    refine ⟨N, fun n hn y hy => ?_⟩
    have hyz : ‖y - z‖ < r - ‖z‖ := by rwa [Metric.mem_ball, dist_eq_norm] at hy
    have hyr : ‖y‖ < r := by
      calc
        ‖y‖ = ‖(y - z) + z‖ := by rw [sub_add_cancel]
        _ ≤ ‖y - z‖ + ‖z‖ := norm_add_le _ _
        _ < (r - ‖z‖) + ‖z‖ := by linarith
        _ = r := sub_add_cancel r ‖z‖
    have hy1 : ‖y‖ < 1 := hyr.trans hr1
    have hMy := sum_div_sqrt_le hα (norm_nonneg y) hyr.le hr1
    have hstep : ∀ m, N ≤ m → ‖f m y - f n y‖ ≤ Mr * δ := by
      intro m hm
      have hdist : ‖u m - u n‖ ≤ δ := by
        rw [← dist_eq_norm]
        exact (hN m hm n hn).le
      have hle := norm_representative_sub_le hα (hfdiff m) (hfdiff n) (hfae m) (hfae n) hy1
      calc
        ‖f m y - f n y‖ ≤
            (∑' k : ℕ, ‖y‖ ^ k / Real.sqrt (bergmanMonomialNormSq α k)) *
              ‖u m - u n‖ := hle
        _ ≤ Mr * ‖u m - u n‖ := mul_le_mul_of_nonneg_right hMy (norm_nonneg _)
        _ ≤ Mr * δ := mul_le_mul_of_nonneg_left hdist hMr0
    have hlim : ‖F y - f n y‖ ≤ Mr * δ := by
      have htend : Tendsto (fun m => ‖f m y - f n y‖) atTop (nhds ‖F y - f n y‖) := by
        simpa [Function.comp_def] using (continuous_norm.tendsto (F y - f n y)).comp
          ((hFtend y hy1).sub tendsto_const_nhds)
      exact le_of_tendsto htend (eventually_atTop.2 ⟨N, hstep⟩)
    rw [dist_eq_norm]
    exact hlim.trans_lt (by dsimp only [δ]; exact mul_majorant_lt hMr0 hε)
  have hFdiff : DifferentiableOn ℂ F (Metric.ball 0 1) :=
    hlu.differentiableOn (Eventually.of_forall hfdiff) Metric.isOpen_ball
  have hmeas : TendstoInMeasure (bergmanMeasure α) (fun n => (u n : ℂ → ℂ)) atTop x :=
    tendstoInMeasure_of_tendsto_Lp hx
  obtain ⟨ns, hns, hae⟩ := hmeas.exists_seq_tendsto_ae
  have hseq : ∀ᵐ z ∂bergmanMeasure α, ∀ i, (u (ns i)) z = f (ns i) z := by
    rw [ae_all_iff]
    intro i
    exact hfae (ns i)
  have hdisk : ∀ᵐ z ∂bergmanMeasure α, ‖z‖ < 1 := by
    rw [ae_iff]
    have hset : {z : ℂ | ¬ ‖z‖ < 1} = {z : ℂ | 1 ≤ ‖z‖} := by
      ext z
      exact not_lt
    rw [hset]
    exact bergmanMeasure_compl_ball α
  refine ⟨F, hFdiff, ?_⟩
  filter_upwards [hae, hseq, hdisk] with z hzconv hzeq hzdisk
  have hFseq : Tendsto (fun i => f (ns i) z) atTop (nhds (F z)) :=
    (hFtend z hzdisk).comp hns.tendsto_atTop
  have huseq : Tendsto (fun i => f (ns i) z) atTop (nhds (x z)) :=
    hzconv.congr' (Eventually.of_forall fun i => hzeq i)
  exact tendsto_nhds_unique huseq hFseq

/-- The inner product against `z ↦ z ^ n` is the monomial moment. -/
private lemma inner_monomial_eq_integral {α : ℝ} (hα : -1 < α) (n : ℕ)
    (g : Lp ℂ 2 (bergmanMeasure α)) :
    inner ℂ (bergmanMonomialLp hα n) g =
      ∫ w, conj (w ^ n) * g w ∂bergmanMeasure α := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [(memLp_monomial hα n).coeFn_toLp] with w hw
  simp only [bergmanMonomialLp]
  rw [hw, RCLike.inner_apply']

/-- **42.52**, Hilbert clause: the integral operator is an orthogonal projection with norm one. -/
theorem exists_bergmanProjection {α : ℝ} (hα : -1 < α) :
    ∃ P : Lp ℂ 2 (bergmanMeasure α) →L[ℂ] Lp ℂ 2 (bergmanMeasure α),
      (∀ f, (fun z ↦ P f z) =ᵐ[bergmanMeasure α] bergmanIntegral α f) ∧
      P.comp P = P ∧ P.adjoint = P ∧ ‖P‖ = 1 ∧ Set.range P = bergmanSet α 2 := by
  let S : Submodule ℂ (Lp ℂ 2 (bergmanMeasure α)) := bergmanSubmodule α
  have hclosed : IsClosed (bergmanSet α 2) := isClosed_bergmanSet hα
  have : IsClosed (S : Set (Lp ℂ 2 (bergmanMeasure α))) := by
    rw [← Submodule.carrier_eq_coe]
    dsimp only [S, bergmanSubmodule]
    exact hclosed
  have : CompleteSpace S := by
    infer_instance
  have : S.HasOrthogonalProjection := inferInstance
  let P := S.starProjection
  have hne : S ≠ ⊥ := by
    intro hbot
    have hm : bergmanMonomialLp hα 0 ∈ S := bergmanMonomialLp_mem hα 0
    rw [hbot] at hm
    have hm0 : bergmanMonomialLp hα 0 = 0 := by simpa [Submodule.mem_bot] using hm
    have hnorm := norm_sq_bergmanMonomialLp_zero hα
    rw [hm0, norm_zero, zero_pow two_ne_zero] at hnorm
    exact absurd hnorm zero_ne_one
  refine ⟨P, ?_, ?_, ?_, ?_, ?_⟩
  · intro f
    have hmem : P f ∈ bergmanSet α 2 := Submodule.starProjection_apply_mem S f
    obtain ⟨F, hFdiff, hFae⟩ := hmem
    have hFLp : MemLp F 2 (bergmanMeasure α) :=
      MemLp.ae_eq hFae (Lp.memLp (P f))
    have hpoint : ∀ z, ‖z‖ < 1 → F z = bergmanIntegral α (f : ℂ → ℂ) z := by
      intro z hz
      rw [bergmanIntegral, integral_bergmanKernel_mul_tsum hα (Lp.memLp f) hz]
      have hcoeff : ∀ n : ℕ, (bergmanMonomialNormSq α n : ℂ)⁻¹ * z ^ n *
          ∫ w, conj (w ^ n) * (f : ℂ → ℂ) w ∂bergmanMeasure α =
          taylorCoefficient F n * z ^ n := by
        intro n
        have hmn : bergmanMonomialLp hα n ∈ S := bergmanMonomialLp_mem hα n
        have hzero :=
          Submodule.starProjection_inner_eq_zero (K := S) f (bergmanMonomialLp hα n) hmn
        have hswap : inner ℂ (bergmanMonomialLp hα n) (f - P f) = 0 :=
          inner_eq_zero_symm.mp hzero
        rw [inner_sub_right] at hswap
        have heq : inner ℂ (bergmanMonomialLp hα n) f =
            inner ℂ (bergmanMonomialLp hα n) (P f) :=
          sub_eq_zero.mp hswap
        rw [inner_monomial_eq_integral hα n f, inner_monomial_eq_integral hα n (P f)] at heq
        have hPF : ∫ w, conj (w ^ n) * (P f) w ∂bergmanMeasure α =
            ∫ w, conj (w ^ n) * F w ∂bergmanMeasure α := by
          refine integral_congr_ae ?_
          filter_upwards [hFae] with w hw
          rw [hw]
        rw [hPF] at heq
        rw [heq, integral_conj_pow_mul_holomorphic hα hFdiff hFLp n]
        have hc0 : (bergmanMonomialNormSq α n : ℂ) ≠ 0 :=
          Complex.ofReal_ne_zero.mpr (bergmanMonomialNormSq_ne_zero hα n)
        set a : ℂ := (bergmanMonomialNormSq α n : ℂ)
        set b : ℂ := z ^ n
        set t : ℂ := taylorCoefficient F n
        calc
          a⁻¹ * b * (t * a) = (a⁻¹ * b * t) * a := by rw [← mul_assoc]
          _ = (t * (a⁻¹ * b)) * a := by rw [mul_comm (a⁻¹ * b) t]
          _ = t * ((a⁻¹ * b) * a) := by rw [mul_assoc]
          _ = t * (a⁻¹ * (b * a)) := by rw [mul_assoc]
          _ = t * (a⁻¹ * (a * b)) := by rw [mul_comm b a]
          _ = t * ((a⁻¹ * a) * b) := by
            conv_lhs =>
              arg 2
              rw [← mul_assoc]
          _ = t * (b * (a⁻¹ * a)) := by rw [mul_comm (a⁻¹ * a) b]
          _ = t * (b * 1) := by rw [inv_mul_cancel₀ hc0]
          _ = t * b := by rw [mul_one]
      have hzball : z ∈ Metric.ball (0 : ℂ) 1 := by
        rwa [Metric.mem_ball, dist_zero_right]
      have htaylor := taylorSeries_eq_on_ball' hzball hFdiff
      rw [tsum_congr hcoeff, ← htaylor]
      refine tsum_congr fun n => ?_
      rw [taylorCoefficient_def, sub_zero, mul_assoc]
    have hdisk : ∀ᵐ w ∂bergmanMeasure α, ‖w‖ < 1 := by
      rw [ae_iff]
      have hset : {w : ℂ | ¬ ‖w‖ < 1} = {w : ℂ | 1 ≤ ‖w‖} := by
        ext w
        exact not_lt
      rw [hset]
      exact bergmanMeasure_compl_ball α
    filter_upwards [hFae, hdisk] with w hwF hwdisk
    rw [hwF]
    exact hpoint w hwdisk
  · have hmul : P * P = P := Submodule.isIdempotentElem_starProjection S
    rwa [ContinuousLinearMap.mul_def] at hmul
  · exact IsSelfAdjoint.adjoint_eq (isSelfAdjoint_starProjection S)
  · exact Submodule.norm_starProjection S hne
  · ext g
    constructor
    · rintro ⟨f, rfl⟩
      exact Submodule.starProjection_apply_mem S f
    · intro hg
      exact ⟨g, (Submodule.starProjection_eq_self_iff (K := S)).mpr hg⟩

/-- **42.52**, `Lᵖ` clause: for `1 < p < ∞` the Bergman integral is bounded on weighted `Lᵖ`. -/
theorem bergmanIntegral_bounded {α : ℝ} (hα : -1 < α) {p : ℝ≥0∞}
    (hp : 1 < p) (hp_top : p < ∞) : ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      ∀ f : ℂ → ℂ, MemLp f p (bergmanMeasure α) →
        MemLp (bergmanIntegral α f) p (bergmanMeasure α) ∧
        eLpNorm (bergmanIntegral α f) p (bergmanMeasure α) ≤
          C * eLpNorm f p (bergmanMeasure α) := by
  sorry

end CKMA
