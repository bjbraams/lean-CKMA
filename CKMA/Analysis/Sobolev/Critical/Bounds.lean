/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Topology.Algebra.Order.Field

/-!
# Real bounds for the critical Sobolev profile

Comparison of `Real.log (Real.log (e / s))` with a square-root singularity, and convergence of
the model integral `∫ dy / (y log (e / y) ^ d)` for `d ≥ 2`. `Real.log` of a nonpositive
number is `0`. The elementary power estimate is Mathlib's `add_pow_le`, loosened from
`2 ^ (n - 1)` to `2 ^ n`.

## Main definitions

* `CKMA.logLog`: double logarithm `Real.log (Real.log (e / s))`.
* `CKMA.profileBound`: the constant `2 * exp (1 / 2)` in the logarithm comparison.

## Main results

* `CKMA.logLog_le`: on `(0, 1]` the double logarithm is at most `profileBound * s ^ (-1 / 2)`.
* `CKMA.integrableOn_inv_mul_log_pow`: the model integral converges for `d ≥ 2`.
-/

public section

noncomputable section

namespace CKMA

open MeasureTheory Set Filter Topology
open scoped ENNReal

/-! ### Real bounds and the one-dimensional logarithmic integral -/

/-- Double logarithm `Real.log (Real.log (e / s))`.
`Real.log` of a nonpositive number is `0`. -/
@[expose]
def logLog (s : ℝ) : ℝ :=
  Real.log (Real.log (Real.exp 1 / s))

/-- Defining equation of `logLog`. -/
lemma logLog_def (s : ℝ) : logLog s = Real.log (Real.log (Real.exp 1 / s)) := rfl

/-- Comparison constant in `log z ≤ 2 √z`. -/
@[expose]
def profileBound : ℝ :=
  2 * Real.exp (1 / 2)

/-- The comparison constant is positive. -/
lemma profileBound_pos : 0 < profileBound := by
  unfold profileBound
  positivity

/-- `log (e / s) ≥ 1` for every `s ∈ (0, 1]`. -/
lemma one_le_log_exp_div {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) :
    1 ≤ Real.log (Real.exp 1 / s) := by
  have hdiv : Real.exp 1 ≤ Real.exp 1 / s := by
    rw [le_div_iff₀ hs0]
    simpa using mul_le_of_le_one_right (Real.exp_nonneg _) hs1
  simpa [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hdiv

/-- On `(0, 1]` the double logarithm is nonnegative. -/
lemma logLog_nonneg {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) : 0 ≤ logLog s := by
  unfold logLog
  rw [← Real.log_one]
  exact Real.log_le_log zero_lt_one (one_le_log_exp_div hs0 hs1)

/-- `√(e) = exp (1 / 2)`. -/
private lemma sqrt_exp_one : Real.sqrt (Real.exp 1) = Real.exp (1 / 2) := by
  rw [Real.sqrt_eq_rpow, Real.exp_one_rpow]

/-- `log (log (e / s)) ≤ profileBound * s ^ (-1 / 2)` for `s ∈ (0, 1]`. -/
lemma logLog_le {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) :
    logLog s ≤ profileBound * s ^ (-(1 / 2 : ℝ)) := by
  have hlog_nonneg : 0 ≤ Real.log (Real.exp 1 / s) :=
    (one_le_log_exp_div hs0 hs1).trans' zero_le_one
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  have hlog_le : Real.log (Real.log (Real.exp 1 / s)) ≤
      2 * Real.sqrt (Real.log (Real.exp 1 / s)) := by
    have hpow := Real.log_le_rpow_div hlog_nonneg hhalf
    have hz : Real.log (Real.exp 1 / s) ^ (1 / 2 : ℝ) / (1 / 2) =
        2 * Real.sqrt (Real.log (Real.exp 1 / s)) := by
      rw [div_eq_mul_inv (Real.log (Real.exp 1 / s) ^ (1 / 2 : ℝ)) (1 / 2)]
      rw [show ((1 : ℝ) / 2)⁻¹ = 2 by rw [one_div, inv_inv], mul_comm]
      rw [← Real.sqrt_eq_rpow]
    exact hpow.trans_eq hz
  have hsub : Real.log (Real.exp 1 / s) ≤ Real.exp 1 / s := by
    exact (Real.log_le_sub_one_of_pos (by positivity)).trans (sub_le_self _ zero_le_one)
  have hsqrt_le : Real.sqrt (Real.log (Real.exp 1 / s)) ≤ Real.sqrt (Real.exp 1 / s) :=
    Real.sqrt_le_sqrt hsub
  have hsqrt_div : Real.sqrt (Real.exp 1 / s) = Real.exp (1 / 2) * s ^ (-(1 / 2 : ℝ)) := by
    rw [Real.sqrt_div (Real.exp_nonneg _), sqrt_exp_one, Real.sqrt_eq_rpow, div_eq_mul_inv,
      ← Real.rpow_neg hs0.le]
  calc logLog s ≤ 2 * Real.sqrt (Real.log (Real.exp 1 / s)) := hlog_le
    _ ≤ 2 * Real.sqrt (Real.exp 1 / s) := by gcongr
    _ = profileBound * s ^ (-(1 / 2 : ℝ)) := by
      rw [hsqrt_div, profileBound]
      ring

/-- Derivative of `z ↦ log (e / z)` at a nonzero point. -/
private lemma hasDerivAt_log_exp_div {y : ℝ} (hy : y ≠ 0) :
    HasDerivAt (fun z => Real.log (Real.exp 1 / z)) (-y⁻¹) y := by
  have hdiv : HasDerivAt (fun z => Real.exp 1 / z) (Real.exp 1 * -(y ^ 2)⁻¹) y := by
    simpa [div_eq_mul_inv] using (hasDerivAt_inv hy).const_mul (Real.exp 1)
  have hlog := hdiv.log (div_ne_zero (Real.exp_ne_zero _) hy)
  apply hlog.congr_deriv
  field_simp

/-- Antiderivative of `(y * log (e / y) ^ d)⁻¹`, sent to `0` at the origin. -/
private def logSingAntideriv (d : ℕ) (y : ℝ) : ℝ :=
  if y = 0 then 0 else Real.log (Real.exp 1 / y) ^ (1 - d : ℝ)

/-- The extended antiderivative is continuous on `[0, R]` for `0 < R ≤ 1 / 2`. -/
private lemma continuousOn_logSingAntideriv {d : ℕ} (hd : 2 ≤ d) {R : ℝ} (hR : 0 < R)
    (hRle : R ≤ 1 / 2) : ContinuousOn (logSingAntideriv d) (Icc 0 R) := by
  intro y hy
  by_cases hy0 : y = 0
  · subst hy0
    rw [ContinuousWithinAt, nhdsWithin_Icc_eq_nhdsGE hR]
    have hIci : Ici (0 : ℝ) = insert 0 (Ioi 0) := by
      ext z
      simp [le_iff_eq_or_lt, eq_comm]
    have hfilt : 𝓝[≥] (0 : ℝ) = pure 0 ⊔ 𝓝[>] 0 := by
      rw [hIci, nhdsWithin_insert]
    rw [hfilt]
    refine tendsto_sup.2 ⟨tendsto_pure_nhds _ _, ?_⟩
    have hf0 : logSingAntideriv d 0 = 0 := by simp [logSingAntideriv]
    rw [hf0]
    have hL : Tendsto (fun z => Real.log (Real.exp 1 / z)) (𝓝[>] 0) atTop := by
      have hinv : Tendsto (fun z => Real.exp 1 / z) (𝓝[>] 0) atTop := by
        simpa [div_eq_mul_inv] using
          tendsto_inv_nhdsGT_zero.const_mul_atTop (Real.exp_pos _)
      exact Real.tendsto_log_atTop.comp hinv
    have hp : (0 : ℝ) < (d : ℝ) - 1 := by
      have hd1 : (1 : ℝ) < d := by exact_mod_cast (by omega : 1 < d)
      linarith
    have hexp : (1 - d : ℝ) = -((d : ℝ) - 1) := by ring
    refine Tendsto.congr' ?_ ((tendsto_rpow_neg_atTop hp).comp hL)
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hz0 : z ≠ 0 := hz.ne'
    rw [Function.comp_apply, logSingAntideriv]
    split_ifs with hz'
    · exact absurd hz' hz0
    · rw [hexp]
  · have hypos : 0 < y := lt_of_le_of_ne hy.1 (Ne.symm hy0)
    have hy1 : y ≤ 1 := le_trans hy.2 hRle |>.trans (by norm_num)
    have hL : Real.log (Real.exp 1 / y) ≠ 0 :=
      (one_le_log_exp_div hypos hy1).trans_lt' zero_lt_one |>.ne'
    have hcont : ContinuousAt (fun z => Real.log (Real.exp 1 / z) ^ (1 - d : ℝ)) y := by
      refine ContinuousAt.rpow_const ?_ (Or.inl hL)
      refine ContinuousAt.log ?_ (div_ne_zero (Real.exp_ne_zero _) hypos.ne')
      exact continuousAt_const.div continuousAt_id hypos.ne'
    have hev : logSingAntideriv d =ᶠ[𝓝 y]
        (fun z => Real.log (Real.exp 1 / z) ^ (1 - d : ℝ)) := by
      filter_upwards [eventually_ne_nhds hypos.ne'] with z hz
      simp [logSingAntideriv, hz]
    exact (hcont.congr_of_eventuallyEq hev).continuousWithinAt

/-- Derivative of the logarithmic antiderivative on `(0, 1 / 2]`. -/
private lemma hasDerivAt_logSingAntideriv {d : ℕ} {y : ℝ} (hy : 0 < y)
    (hyR : y ≤ 1 / 2) : HasDerivAt (logSingAntideriv d)
      ((d - 1 : ℝ) * (y * Real.log (Real.exp 1 / y) ^ d)⁻¹) y := by
  set L : ℝ := Real.log (Real.exp 1 / y)
  have hLpos : 0 < L := (one_le_log_exp_div hy (hyR.trans (by norm_num))).trans_lt' zero_lt_one
  have hpow : HasDerivAt (fun z => Real.log (Real.exp 1 / z) ^ (1 - d : ℝ))
      ((-y⁻¹) * (1 - d : ℝ) * L ^ ((1 - d : ℝ) - 1)) y :=
    (hasDerivAt_log_exp_div hy.ne').rpow_const (Or.inl hLpos.ne')
  have hev : logSingAntideriv d =ᶠ[𝓝 y]
      (fun z => Real.log (Real.exp 1 / z) ^ (1 - d : ℝ)) := by
    filter_upwards [eventually_ne_nhds hy.ne'] with z hz
    simp [logSingAntideriv, hz]
  apply (hpow.congr_of_eventuallyEq hev).congr_deriv
  have hexp : (1 - d : ℝ) - 1 = -(d : ℝ) := by ring
  have hcoe : (-y⁻¹) * (1 - d : ℝ) = (d - 1 : ℝ) * y⁻¹ := by ring
  calc (-y⁻¹) * (1 - d : ℝ) * L ^ ((1 - d : ℝ) - 1)
      = (d - 1 : ℝ) * y⁻¹ * L ^ (-(d : ℝ)) := by rw [hcoe, hexp]
    _ = (d - 1 : ℝ) * y⁻¹ * (L ^ (d : ℝ))⁻¹ := by rw [Real.rpow_neg hLpos.le]
    _ = (d - 1 : ℝ) * y⁻¹ * (L ^ d)⁻¹ := by rw [Real.rpow_natCast]
    _ = (d - 1 : ℝ) * (y⁻¹ * (L ^ d)⁻¹) := by rw [mul_assoc]
    _ = (d - 1 : ℝ) * (y * L ^ d)⁻¹ := by rw [mul_inv]

/-- The model integral `∫₀ᴿ dy / (y log (e / y) ^ d)` converges for `d ≥ 2`. -/
lemma integrableOn_inv_mul_log_pow {d : ℕ} (hd : 2 ≤ d) {R : ℝ} (hR : 0 < R)
    (hRle : R ≤ 1 / 2) :
    IntegrableOn (fun y => (y * Real.log (Real.exp 1 / y) ^ d)⁻¹) (Ioo 0 R) := by
  let g' : ℝ → ℝ := fun y => (d - 1 : ℝ) * (y * Real.log (Real.exp 1 / y) ^ d)⁻¹
  have hderiv : ∀ y ∈ Ioo 0 R, HasDerivAt (logSingAntideriv d) (g' y) y := by
    intro y hy
    exact hasDerivAt_logSingAntideriv hy.1 (hy.2.le.trans hRle)
  have hpos : ∀ y ∈ Ioo 0 R, 0 ≤ g' y := by
    intro y hy
    have hy1 : y ≤ 1 := hy.2.le.trans hRle |>.trans (by norm_num)
    have hL : 0 ≤ Real.log (Real.exp 1 / y) :=
      (one_le_log_exp_div hy.1 hy1).trans' zero_le_one
    have hd1 : (0 : ℝ) ≤ (d : ℝ) - 1 := by
      have h1 : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
      linarith
    exact mul_nonneg hd1 (inv_nonneg.mpr (mul_nonneg hy.1.le (pow_nonneg hL _)))
  have hint : IntegrableOn g' (Ioc 0 R) :=
    intervalIntegral.integrableOn_deriv_of_nonneg
      (continuousOn_logSingAntideriv hd hR hRle) hderiv hpos
  have hint' : IntegrableOn g' (Ioo 0 R) :=
    (integrableOn_Ioc_iff_integrableOn_Ioo (f := g') (μ := volume) (a := 0) (b := R)
      (eNorm_ne_top (x := g' R))).1 hint
  have hd1 : ((d : ℝ) - 1) ≠ 0 := by
    have h1 : (1 : ℝ) < d := by exact_mod_cast (by omega : 1 < d)
    linarith
  have heq : EqOn (fun y => ((d : ℝ) - 1)⁻¹ * g' y)
      (fun y => (y * Real.log (Real.exp 1 / y) ^ d)⁻¹) (Ioo 0 R) := by
    intro y _
    simp only [g']
    rw [← mul_assoc, inv_mul_cancel₀ hd1, one_mul]
  exact IntegrableOn.congr_fun (hint'.const_mul ((d : ℝ) - 1)⁻¹) heq measurableSet_Ioo

/-- `(a + b) ^ n ≤ 2 ^ n (a ^ n + b ^ n)` for nonnegative `a, b`.
This is Mathlib's `add_pow_le`, loosened from the constant `2 ^ (n - 1)` to `2 ^ n`. -/
lemma add_pow_le_two_pow_mul {a b : ℝ} {n : ℕ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) ^ n ≤ 2 ^ n * (a ^ n + b ^ n) := by
  calc (a + b) ^ n
      ≤ 2 ^ (n - 1) * (a ^ n + b ^ n) := add_pow_le ha hb n
    _ ≤ 2 ^ n * (a ^ n + b ^ n) :=
        mul_le_mul_of_nonneg_right
          (pow_le_pow_right₀ one_le_two (Nat.sub_le n 1))
          (add_nonneg (pow_nonneg ha n) (pow_nonneg hb n))


end CKMA
