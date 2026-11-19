/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Order.OrderClosed

/-!
# Critical Sobolev functions that are essentially unbounded

In dimension at least two, every nonempty open set contains an essentially unbounded
`W^{1,d}` function. A logarithmic radial profile describes the local singularity before
a smooth cutoff. Weak derivatives reuse TauCeti, and Lebesgue norms use Mathlib.
Source: GAPS 26.16.

## Main definitions

* `CKMA.criticalSobolevProfile`: the radial double-logarithmic singularity `log (log (e / ‖x‖))`.

## Main results

* `CKMA.exists_memSobolev_not_memLp_top`: failure of the critical Sobolev embedding `W^{1,d}(Ω) ↪
  L^∞(Ω)` in dimensions `d ≥ 2` (**26.16**).
-/

@[expose] public section

noncomputable section

namespace CKMA

open MeasureTheory Metric Set Filter Topology ContinuousLinearMap
open scoped ENNReal RealInnerProductSpace NNReal

/-- The radial logarithmic singularity used at the critical exponent, totalized at the origin.
A smooth cutoff is still needed to obtain a compactly supported Sobolev function. -/
def criticalSobolevProfile {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  Real.log (Real.log (Real.exp 1 / ‖x‖))

/-- Euclidean space of dimension `d`, used for the critical profile. -/
private abbrev Euc (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-! ### Real bounds and the one-dimensional logarithmic integral -/

/-- Double logarithm `log (log (e / s))`, with Lean's junk value `log 0 = 0`. -/
private def logLog (s : ℝ) : ℝ :=
  Real.log (Real.log (Real.exp 1 / s))

/-- Comparison constant in `log z ≤ 2 √z`. -/
private def profileBound : ℝ :=
  2 * Real.exp (1 / 2)

/-- The comparison constant is positive. -/
private lemma profileBound_pos : 0 < profileBound := by
  unfold profileBound
  positivity

/-- `log (e / s) ≥ 1` for every `s ∈ (0, 1]`. -/
private lemma one_le_log_exp_div {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) :
    1 ≤ Real.log (Real.exp 1 / s) := by
  have hdiv : Real.exp 1 ≤ Real.exp 1 / s := by
    rw [le_div_iff₀ hs0]
    simpa using mul_le_of_le_one_right (Real.exp_nonneg _) hs1
  simpa [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hdiv

/-- On `(0, 1]` the double logarithm is nonnegative. -/
private lemma logLog_nonneg {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) : 0 ≤ logLog s := by
  unfold logLog
  rw [← Real.log_one]
  exact Real.log_le_log zero_lt_one (one_le_log_exp_div hs0 hs1)

/-- `√(e) = exp (1 / 2)`. -/
private lemma sqrt_exp_one : Real.sqrt (Real.exp 1) = Real.exp (1 / 2) := by
  rw [Real.sqrt_eq_rpow, Real.exp_one_rpow]

/-- `log (log (e / s)) ≤ profileBound * s ^ (-1 / 2)` for `s ∈ (0, 1]`. -/
private lemma logLog_le {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) :
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
private lemma integrableOn_inv_mul_log_pow {d : ℕ} (hd : 2 ≤ d) {R : ℝ} (hR : 0 < R)
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
    (integrableOn_Ioc_iff_integrableOn_Ioo (f := g') (μ := volume) (a := 0) (b := R)).1 hint
  have hd1 : ((d : ℝ) - 1) ≠ 0 := by
    have h1 : (1 : ℝ) < d := by exact_mod_cast (by omega : 1 < d)
    linarith
  have heq : EqOn (fun y => ((d : ℝ) - 1)⁻¹ * g' y)
      (fun y => (y * Real.log (Real.exp 1 / y) ^ d)⁻¹) (Ioo 0 R) := by
    intro y _
    simp only [g']
    rw [← mul_assoc, inv_mul_cancel₀ hd1, one_mul]
  exact IntegrableOn.congr_fun (hint'.const_mul ((d : ℝ) - 1)⁻¹) heq measurableSet_Ioo

/-- `(a + b) ^ n ≤ 2 ^ n (a ^ n + b ^ n)` for nonnegative `a, b`. -/
private lemma add_pow_le_two_pow_mul {a b : ℝ} {n : ℕ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) ^ n ≤ 2 ^ n * (a ^ n + b ^ n) := by
  have hmax : a + b ≤ 2 * max a b := by
    rw [two_mul]
    exact add_le_add (le_max_left a b) (le_max_right a b)
  have hpow : (max a b) ^ n ≤ a ^ n + b ^ n := by
    rcases le_total a b with h | h
    · rw [max_eq_right h]
      exact le_add_of_nonneg_left (pow_nonneg ha _)
    · rw [max_eq_left h]
      exact le_add_of_nonneg_right (pow_nonneg hb _)
  calc (a + b) ^ n ≤ (2 * max a b) ^ n := by gcongr
    _ = 2 ^ n * (max a b) ^ n := by rw [mul_pow]
    _ ≤ 2 ^ n * (a ^ n + b ^ n) := by gcongr

/-! ### Regularized profile -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Regularized radius `√(‖x - c‖² + t)`. -/
private def regNorm (t : ℝ) (c x : E) : ℝ :=
  Real.sqrt (‖x - c‖ ^ 2 + t)

/-- Candidate derivative of `logLog ∘ regNorm`. -/
private def logLogFDeriv (t : ℝ) (c x : E) : E →L[ℝ] ℝ :=
  (-(regNorm t c x ^ 2 * Real.log (Real.exp 1 / regNorm t c x))⁻¹) • innerSL ℝ (x - c)

/-- Smooth cutoff times the regularized double logarithm. -/
private def cutoffProfile {c : E} (η : ContDiffBump c) (t : ℝ) (x : E) : ℝ :=
  η x * logLog (regNorm t c x)

/-- Product rule for the cutoff, using the algebraic derivative of the profile. -/
private def cutoffProfileFDeriv {c : E} (η : ContDiffBump c) (t : ℝ) (x : E) : E →L[ℝ] ℝ :=
  η x • logLogFDeriv t c x + logLog (regNorm t c x) • fderiv ℝ (η : E → ℝ) x

omit [InnerProductSpace ℝ E] in
/-- Square of the regularized radius. -/
private lemma regNorm_sq {t : ℝ} (ht : 0 ≤ t) (c x : E) :
    regNorm t c x ^ 2 = ‖x - c‖ ^ 2 + t :=
  Real.sq_sqrt (by positivity)

omit [InnerProductSpace ℝ E] in
/-- At `t = 0` the regularized radius is the distance to the center. -/
private lemma regNorm_zero (c x : E) : regNorm 0 c x = ‖x - c‖ := by
  simp [regNorm, Real.sqrt_sq (norm_nonneg _)]

omit [InnerProductSpace ℝ E] in
/-- The regularized radius is at least the distance to the center. -/
private lemma regNorm_ge_norm {t : ℝ} (ht : 0 ≤ t) (c x : E) :
    ‖x - c‖ ≤ regNorm t c x := by
  rw [← Real.sqrt_sq (norm_nonneg _), regNorm]
  exact Real.sqrt_le_sqrt (le_add_of_nonneg_right ht)

omit [InnerProductSpace ℝ E] in
/-- Positive regularization stays positive. -/
private lemma regNorm_pos {t : ℝ} (ht : 0 < t) (c x : E) : 0 < regNorm t c x := by
  have : 0 < ‖x - c‖ ^ 2 + t := by positivity
  simpa [regNorm] using Real.sqrt_pos.mpr this

omit [InnerProductSpace ℝ E] in
/-- The regularized radius is continuous. -/
private lemma continuous_regNorm (t : ℝ) (c : E) : Continuous (regNorm t c) := by
  unfold regNorm
  exact Real.continuous_sqrt.comp <|
    ((continuous_norm.comp (continuous_id.sub continuous_const)).pow 2).add continuous_const

omit [InnerProductSpace ℝ E] in
/-- As `t → 0⁺`, the regularized radius tends to the distance to the center. -/
private lemma tendsto_regNorm_zero (c x : E) :
    Tendsto (fun t => regNorm t c x) (𝓝[>] 0) (𝓝 ‖x - c‖) := by
  unfold regNorm
  have hadd : ContinuousAt (fun t : ℝ => ‖x - c‖ ^ 2 + t) 0 :=
    continuousAt_const.add continuousAt_id
  have hcont : ContinuousAt (fun t : ℝ => Real.sqrt (‖x - c‖ ^ 2 + t)) 0 :=
    Real.continuous_sqrt.continuousAt.comp hadd
  have ht : Tendsto (fun t : ℝ => Real.sqrt (‖x - c‖ ^ 2 + t)) (𝓝[>] 0)
      (𝓝 (Real.sqrt (‖x - c‖ ^ 2 + 0))) :=
    hcont.tendsto.mono_left nhdsWithin_le_nhds
  rw [add_zero, Real.sqrt_sq (norm_nonneg _)] at ht
  exact ht

omit [InnerProductSpace ℝ E] in
/-- On the cutoff support the regularized radius stays strictly below `1`. -/
private lemma regNorm_lt_one {c : E} (η : ContDiffBump c) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 4)
    (hOut : η.rOut ≤ 1 / 2) {x : E} (hx : ‖x - c‖ ≤ η.rOut) : regNorm t c x < 1 := by
  have hr : ‖x - c‖ ≤ 1 / 2 := hx.trans hOut
  have hs2 : regNorm t c x ^ 2 ≤ 1 / 2 := by
    rw [regNorm_sq ht0]
    have hsq : ‖x - c‖ ^ 2 ≤ (1 / 2) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hr 2
    nlinarith [hsq]
  have hs_nonneg : 0 ≤ regNorm t c x := Real.sqrt_nonneg _
  have hsq_lt : regNorm t c x ^ 2 < 1 ^ 2 := hs2.trans_lt (by norm_num)
  have habs : |regNorm t c x| < |1| := sq_lt_sq.mp hsq_lt
  simpa [abs_of_nonneg hs_nonneg] using habs

omit [InnerProductSpace ℝ E] in
/-- The profile is nonnegative on the region used by the cutoff. -/
private lemma logLog_regNorm_nonneg {c : E} (η : ContDiffBump c) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1 / 4) (hOut : η.rOut ≤ 1 / 2) {x : E} (hx : ‖x - c‖ ≤ η.rOut)
    (hs : 0 < regNorm t c x) : 0 ≤ logLog (regNorm t c x) :=
  logLog_nonneg hs (le_of_lt (regNorm_lt_one η ht0 ht1 hOut hx))

/-- Derivative of the regularized radius, rewritten as `s⁻¹ • innerSL`. -/
private lemma hasFDerivAt_regNorm {t : ℝ} {c x : E} (ht : 0 ≤ t) (hs : 0 < regNorm t c x) :
    HasFDerivAt (fun y => regNorm t c y) ((regNorm t c x)⁻¹ • innerSL ℝ (x - c)) x := by
  set s : ℝ := regNorm t c x
  have hsq : HasFDerivAt (fun y : E => ‖y - c‖ ^ 2 + t) (2 • innerSL ℝ (x - c)) x := by
    simpa [ContinuousLinearMap.comp_id] using
      ((hasFDerivAt_sub_const c).norm_sq.add_const t)
  have harg : ‖x - c‖ ^ 2 + t ≠ 0 := by
    rw [← regNorm_sq ht]
    exact (sq_pos_of_pos hs).ne'
  have hsqrt := hsq.sqrt harg
  apply hsqrt.congr_fderiv
  ext v
  simp only [IsSMulApply.smul_apply, innerSL_apply_apply, smul_eq_mul, s, regNorm]
  field_simp
  ring

/-- Chain rule for `logLog ∘ regNorm` at a point where both logarithms are genuine. -/
private lemma hasFDerivAt_logLog_regNorm {t : ℝ} {c x : E} (ht : 0 ≤ t) (hs : 0 < regNorm t c x)
    (hL : Real.log (Real.exp 1 / regNorm t c x) ≠ 0) :
    HasFDerivAt (fun y => logLog (regNorm t c y)) (logLogFDeriv t c x) x := by
  set s : ℝ := regNorm t c x
  set L : ℝ := Real.log (Real.exp 1 / s)
  have hreg := hasFDerivAt_regNorm ht hs
  have hinv : HasFDerivAt (fun y => (regNorm t c y)⁻¹)
      ((-(s ^ 2)⁻¹) • (s⁻¹ • innerSL ℝ (x - c))) x :=
    (hasDerivAt_inv hs.ne').comp_hasFDerivAt x hreg
  have hdiv : HasFDerivAt (fun y => Real.exp 1 / regNorm t c y)
      (Real.exp 1 • ((-(s ^ 2)⁻¹) • (s⁻¹ • innerSL ℝ (x - c)))) x := by
    simpa [div_eq_mul_inv] using hinv.const_mul (Real.exp 1)
  have hlog : HasFDerivAt (fun y => Real.log (Real.exp 1 / regNorm t c y))
      ((Real.exp 1 / s)⁻¹ •
        (Real.exp 1 • ((-(s ^ 2)⁻¹) • (s⁻¹ • innerSL ℝ (x - c))))) x :=
    hdiv.log (div_ne_zero (Real.exp_ne_zero _) hs.ne')
  have hLL : HasFDerivAt (fun y => logLog (regNorm t c y))
      (L⁻¹ • ((Real.exp 1 / s)⁻¹ •
        (Real.exp 1 • ((-(s ^ 2)⁻¹) • (s⁻¹ • innerSL ℝ (x - c)))))) x :=
    hlog.log hL
  apply hLL.congr_fderiv
  ext v
  simp only [logLogFDeriv, IsSMulApply.smul_apply, innerSL_apply_apply, smul_eq_mul, s, L,
    div_eq_mul_inv]
  field_simp

/-- The cutoff is differentiable, with the product-rule derivative, for a small positive
regularization, and also at `t = 0` away from the center. -/
private lemma hasFDerivAt_cutoffProfile {c : E} (η : ContDiffBump c) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1 / 4) (hOut : η.rOut ≤ 1 / 2) {x : E} (hx : 0 < t ∨ x ≠ c) :
    HasFDerivAt (cutoffProfile η t) (cutoffProfileFDeriv η t x) x := by
  by_cases hball : ‖x - c‖ ≤ η.rOut
  · have hs : 0 < regNorm t c x := by
      rcases hx with ht | hxc
      · exact regNorm_pos ht c x
      · exact lt_of_lt_of_le (norm_pos_iff.mpr (sub_ne_zero.mpr hxc)) (regNorm_ge_norm ht0 c x)
    have hlt : regNorm t c x < 1 := regNorm_lt_one η ht0 ht1 hOut hball
    have hL : Real.log (Real.exp 1 / regNorm t c x) ≠ 0 :=
      (lt_of_lt_of_le zero_lt_one (one_le_log_exp_div hs (le_of_lt hlt))).ne'
    have hψ := hasFDerivAt_logLog_regNorm ht0 hs hL
    have hη : HasFDerivAt (η : E → ℝ) (fderiv ℝ (η : E → ℝ) x) x :=
      ((η.contDiffAt (n := 1)).differentiableAt one_ne_zero).hasFDerivAt
    unfold cutoffProfile cutoffProfileFDeriv
    exact hη.mul hψ
  · rw [← dist_eq_norm] at hball
    have hxmem : x ∉ tsupport (η : E → ℝ) := by
      rw [ContDiffBump.tsupport_eq, mem_closedBall]
      exact hball
    have hη0 : (η : E → ℝ) =ᶠ[𝓝 x] 0 := (notMem_tsupport_iff_eventuallyEq).mp hxmem
    have hcut : cutoffProfile η t =ᶠ[𝓝 x] 0 := by
      filter_upwards [hη0] with y hy
      simp [cutoffProfile, hy]
    have hderiv0 : cutoffProfileFDeriv η t x = 0 := by
      have hηx : η x = 0 := η.zero_of_le_dist (le_of_lt (lt_of_not_ge hball))
      rw [cutoffProfileFDeriv, hηx, zero_smul, fderiv_of_notMem_tsupport ℝ hxmem,
        smul_zero, zero_add]
    exact ((hasFDerivAt_const (0 : ℝ) x).congr_of_eventuallyEq hcut).congr_fderiv hderiv0.symm

/-- A bound for `‖fderiv η‖`, obtained on the compact support. -/
private lemma exists_bound_norm_fderiv_bump [FiniteDimensional ℝ E] {c : E} (η : ContDiffBump c) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖fderiv ℝ (η : E → ℝ) x‖ ≤ M := by
  have hcont : Continuous fun x => ‖fderiv ℝ (η : E → ℝ) x‖ :=
    continuous_norm.comp ((η.contDiff (n := 1)).continuous_fderiv one_ne_zero)
  obtain ⟨x, _hx, hmax⟩ := (isCompact_closedBall c η.rOut).exists_isMaxOn
    (nonempty_closedBall.mpr η.rOut_pos.le) hcont.continuousOn
  refine ⟨‖fderiv ℝ (η : E → ℝ) x‖, norm_nonneg _, fun y => ?_⟩
  by_cases hy : y ∈ closedBall c η.rOut
  · exact hmax hy
  · have hy' : y ∉ tsupport (η : E → ℝ) := by rwa [η.tsupport_eq]
    rw [fderiv_of_notMem_tsupport ℝ hy', norm_zero]
    exact norm_nonneg _

/-- Operator norm of the algebraic profile derivative, when the logarithms are genuine. -/
private lemma norm_logLogFDeriv {t : ℝ} {c x : E} (hs : 0 < regNorm t c x)
    (hL : 0 < Real.log (Real.exp 1 / regNorm t c x)) :
    ‖logLogFDeriv t c x‖ =
      ‖x - c‖ / (regNorm t c x ^ 2 * Real.log (Real.exp 1 / regNorm t c x)) := by
  unfold logLogFDeriv
  rw [norm_smul, innerSL_apply_norm, Real.norm_eq_abs]
  have hden : 0 < regNorm t c x ^ 2 * Real.log (Real.exp 1 / regNorm t c x) := by positivity
  rw [abs_neg, abs_inv, abs_of_pos hden, mul_comm]
  exact (div_eq_mul_inv (‖x - c‖)
    (regNorm t c x ^ 2 * Real.log (Real.exp 1 / regNorm t c x))).symm

/-- Crude gradient bound `‖D(cutoff)‖ ≤ K / ‖x - c‖`, valid down to `t = 0`. -/
private lemma norm_cutoffProfileFDeriv_le [FiniteDimensional ℝ E] {c : E} (η : ContDiffBump c)
    {M t : ℝ} (hM : ∀ x, ‖fderiv ℝ (η : E → ℝ) x‖ ≤ M) (hM0 : 0 ≤ M) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1 / 4) (hOut : η.rOut ≤ 1 / 2) (x : E) :
    ‖cutoffProfileFDeriv η t x‖ ≤
      (1 + M * profileBound) * ‖x - c‖ ^ (-1 : ℝ) := by
  by_cases hr0 : ‖x - c‖ = 0
  · have hxc : x = c := sub_eq_zero.mp (norm_eq_zero.mp hr0)
    have hηc : fderiv ℝ (η : E → ℝ) c = 0 := by
      simpa using η.eventuallyEq_one.fderiv_eq
    rw [hxc, cutoffProfileFDeriv, hηc, smul_zero, add_zero]
    have hD : logLogFDeriv t c c = 0 := by
      simp [logLogFDeriv, sub_self, map_zero]
    rw [hD, smul_zero, norm_zero]
    exact mul_nonneg (add_nonneg zero_le_one (mul_nonneg hM0 profileBound_pos.le))
      (Real.rpow_nonneg (norm_nonneg _) _)
  · have hr : 0 < ‖x - c‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hr0)
    by_cases hball : ‖x - c‖ ≤ η.rOut
    · set s : ℝ := regNorm t c x
      set L : ℝ := Real.log (Real.exp 1 / s)
      have hs : 0 < s := lt_of_lt_of_le hr (regNorm_ge_norm ht0 c x)
      have hs1 : s < 1 := regNorm_lt_one η ht0 ht1 hOut hball
      have hL : 1 ≤ L := one_le_log_exp_div hs (le_of_lt hs1)
      have hlogle : logLog s ≤ profileBound * s ^ (-(1 / 2 : ℝ)) :=
        logLog_le hs (le_of_lt hs1)
      have hlog0 : 0 ≤ logLog s := logLog_nonneg hs (le_of_lt hs1)
      have hfirst : ‖logLogFDeriv t c x‖ ≤ ‖x - c‖⁻¹ := by
        rw [norm_logLogFDeriv hs (lt_of_lt_of_le zero_lt_one hL)]
        have hden : 0 < s ^ 2 * L := by positivity
        rw [div_le_iff₀ hden]
        have hs2 : ‖x - c‖ ^ 2 ≤ s ^ 2 * L := by
          have hs2' : ‖x - c‖ ^ 2 ≤ s ^ 2 := by
            rw [regNorm_sq ht0]
            exact le_add_of_nonneg_right ht0
          exact hs2'.trans (le_mul_of_one_le_right (sq_nonneg _) hL)
        rw [← mul_le_mul_iff_of_pos_left hr, ← pow_two, ← mul_assoc,
          mul_inv_cancel₀ hr.ne', one_mul]
        exact hs2
      have hhalf : s ^ (-(1 / 2 : ℝ)) ≤ ‖x - c‖ ^ (-(1 / 2 : ℝ)) := by
        have hroot : ‖x - c‖ ^ (1 / 2 : ℝ) ≤ s ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow hr.le (regNorm_ge_norm ht0 c x) (by norm_num)
        have hinv : (s ^ (1 / 2 : ℝ))⁻¹ ≤ (‖x - c‖ ^ (1 / 2 : ℝ))⁻¹ :=
          inv_anti₀ (Real.rpow_pos_of_pos hr (1 / 2)) hroot
        simpa [Real.rpow_neg hr.le, Real.rpow_neg hs.le] using hinv
      have hone : ‖x - c‖ ^ (-(1 / 2 : ℝ)) ≤ ‖x - c‖ ^ (-1 : ℝ) := by
        have h12 : (1 / 2 : ℝ) ≤ 1 := by norm_num
        have hr1 : ‖x - c‖ ≤ 1 := hball.trans (hOut.trans h12)
        have hexpLe : (-1 : ℝ) ≤ -(1 / 2 : ℝ) := by norm_num
        exact Real.rpow_le_rpow_of_exponent_ge hr hr1 hexpLe
      have hsecond : ‖logLog s • fderiv ℝ (η : E → ℝ) x‖ ≤
          M * profileBound * ‖x - c‖ ^ (-1 : ℝ) := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hlog0]
        have h1 : logLog s * ‖fderiv ℝ (η : E → ℝ) x‖ ≤ logLog s * M :=
          mul_le_mul_of_nonneg_left (hM x) hlog0
        have h2 : logLog s * M ≤ (profileBound * s ^ (-(1 / 2 : ℝ))) * M :=
          mul_le_mul_of_nonneg_right hlogle hM0
        have h3 : (profileBound * s ^ (-(1 / 2 : ℝ))) * M ≤
            profileBound * ‖x - c‖ ^ (-(1 / 2 : ℝ)) * M := by
          simp only [mul_assoc]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hhalf hM0)
            profileBound_pos.le
        have h4 : profileBound * ‖x - c‖ ^ (-(1 / 2 : ℝ)) * M ≤
            M * profileBound * ‖x - c‖ ^ (-1 : ℝ) := by
          calc profileBound * ‖x - c‖ ^ (-(1 / 2 : ℝ)) * M
              ≤ profileBound * ‖x - c‖ ^ (-1 : ℝ) * M := by
                simp only [mul_assoc]
                exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hone hM0)
                  profileBound_pos.le
            _ = M * profileBound * ‖x - c‖ ^ (-1 : ℝ) := by ring
        exact ((h1.trans h2).trans h3).trans h4
      have hηabs : |η x| ≤ 1 := by
        rw [abs_of_nonneg η.nonneg]
        exact η.le_one
      calc ‖cutoffProfileFDeriv η t x‖
          ≤ ‖η x • logLogFDeriv t c x‖ + ‖logLog s • fderiv ℝ (η : E → ℝ) x‖ := norm_add_le _ _
        _ ≤ |η x| * ‖logLogFDeriv t c x‖ + ‖logLog s • fderiv ℝ (η : E → ℝ) x‖ := by
            rw [norm_smul, Real.norm_eq_abs]
        _ ≤ 1 * ‖x - c‖⁻¹ + M * profileBound * ‖x - c‖ ^ (-1 : ℝ) := by
            refine add_le_add ?_ hsecond
            exact mul_le_mul hηabs hfirst (norm_nonneg _) zero_le_one
        _ = (1 + M * profileBound) * ‖x - c‖ ^ (-1 : ℝ) := by
            rw [Real.rpow_neg_one, one_mul]
            ring
    · rw [← dist_eq_norm] at hball
      have hxmem : x ∉ tsupport (η : E → ℝ) := by
        rw [ContDiffBump.tsupport_eq, mem_closedBall]
        exact hball
      have hzero : cutoffProfileFDeriv η t x = 0 := by
        rw [cutoffProfileFDeriv, η.zero_of_le_dist (le_of_lt (lt_of_not_ge hball)),
          zero_smul, fderiv_of_notMem_tsupport ℝ hxmem, smul_zero, zero_add]
      rw [hzero, norm_zero]
      exact mul_nonneg (add_nonneg zero_le_one (mul_nonneg hM0 profileBound_pos.le))
        (Real.rpow_nonneg (norm_nonneg _) _)

/-- The algebraic derivative is continuous wherever the cutoff sees a genuine logarithm. -/
private lemma continuousAt_cutoffProfileFDeriv {c : E} (η : ContDiffBump c) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 4) (hOut : η.rOut ≤ 1 / 2) {x : E} (hx : 0 < t ∨ x ≠ c) :
    ContinuousAt (cutoffProfileFDeriv η t) x := by
  by_cases hball : ‖x - c‖ ≤ η.rOut
  · have hs : 0 < regNorm t c x := by
      rcases hx with ht | hxc
      · exact regNorm_pos ht c x
      · exact lt_of_lt_of_le (norm_pos_iff.mpr (sub_ne_zero.mpr hxc)) (regNorm_ge_norm ht0 c x)
    have hlt : regNorm t c x < 1 := regNorm_lt_one η ht0 ht1 hOut hball
    have hLne : Real.log (Real.exp 1 / regNorm t c x) ≠ 0 :=
      (lt_of_lt_of_le zero_lt_one (one_le_log_exp_div hs (le_of_lt hlt))).ne'
    have hreg : ContinuousAt (regNorm t c) x := (continuous_regNorm t c).continuousAt
    have hdiv : ContinuousAt (fun y => Real.exp 1 / regNorm t c y) x :=
      continuousAt_const.div hreg hs.ne'
    have hlog : ContinuousAt (fun y => Real.log (Real.exp 1 / regNorm t c y)) x :=
      hdiv.log (div_ne_zero (Real.exp_ne_zero _) hs.ne')
    have hloglog : ContinuousAt (fun y => logLog (regNorm t c y)) x := hlog.log hLne
    have hden : ContinuousAt (fun y =>
        regNorm t c y ^ 2 * Real.log (Real.exp 1 / regNorm t c y)) x :=
      (hreg.pow 2).mul hlog
    have hden0 : regNorm t c x ^ 2 * Real.log (Real.exp 1 / regNorm t c x) ≠ 0 :=
      mul_ne_zero (pow_ne_zero 2 hs.ne') hLne
    have hinv : ContinuousAt (fun y =>
        (regNorm t c y ^ 2 * Real.log (Real.exp 1 / regNorm t c y))⁻¹) x :=
      hden.inv₀ hden0
    have hinner : ContinuousAt (fun y => innerSL ℝ (y - c)) x :=
      (innerSL ℝ).continuous.continuousAt.comp (continuousAt_id.sub continuousAt_const)
    have hD : ContinuousAt (logLogFDeriv t c) x := by
      unfold logLogFDeriv
      exact (hinv.neg).smul hinner
    have hfderiv : ContinuousAt (fun y => fderiv ℝ (η : E → ℝ) y) x :=
      ((η.contDiff (n := 1)).continuous_fderiv one_ne_zero).continuousAt
    unfold cutoffProfileFDeriv
    exact ((η.continuous.continuousAt).smul hD).add (hloglog.smul hfderiv)
  · have hxmem : x ∉ tsupport (η : E → ℝ) := by
      rw [ContDiffBump.tsupport_eq, mem_closedBall, dist_eq_norm]
      exact hball
    have hη0 : (η : E → ℝ) =ᶠ[𝓝 x] 0 := (notMem_tsupport_iff_eventuallyEq).mp hxmem
    have hdf0 : (fun y => fderiv ℝ (η : E → ℝ) y) =ᶠ[𝓝 x] 0 := by
      have hopen : (tsupport (η : E → ℝ))ᶜ ∈ 𝓝 x :=
        (isClosed_tsupport (η : E → ℝ)).isOpen_compl.mem_nhds hxmem
      filter_upwards [hopen] with y hy
      rw [mem_compl_iff] at hy
      rw [Pi.zero_apply, fderiv_of_notMem_tsupport ℝ hy]
    have heq : cutoffProfileFDeriv η t =ᶠ[𝓝 x] 0 := by
      filter_upwards [hη0, hdf0] with y hyη hyf
      simp [cutoffProfileFDeriv, hyη, hyf]
    exact continuousAt_const.congr_of_eventuallyEq heq

/-- For positive regularization the cutoff derivative is continuous. -/
private lemma continuous_cutoffProfileFDeriv {c : E} (η : ContDiffBump c) {t : ℝ} (ht0 : 0 < t)
    (ht1 : t ≤ 1 / 4) (hOut : η.rOut ≤ 1 / 2) : Continuous (cutoffProfileFDeriv η t) :=
  continuous_iff_continuousAt.mpr fun x =>
    continuousAt_cutoffProfileFDeriv η ht0.le ht1 hOut (Or.inl ht0) (x := x)

/-- The singular profile is continuous away from its center. -/
private lemma continuousOn_cutoffProfile_zero {c : E} (η : ContDiffBump c) (hOut : η.rOut ≤ 1 / 2) :
    ContinuousOn (cutoffProfile η 0) {c}ᶜ := by
  intro x hx
  have hderiv := hasFDerivAt_cutoffProfile η le_rfl (by norm_num) hOut (Or.inr hx)
  exact hderiv.continuousAt.continuousWithinAt

/-- The algebraic derivative at `t = 0` is continuous away from the center. -/
private lemma continuousOn_cutoffProfileFDeriv_zero {c : E} (η : ContDiffBump c)
    (hOut : η.rOut ≤ 1 / 2) : ContinuousOn (cutoffProfileFDeriv η 0) {c}ᶜ := by
  intro x hx
  exact (continuousAt_cutoffProfileFDeriv η le_rfl (by norm_num) hOut
    (Or.inr hx)).continuousWithinAt

/-! ### Integrability on Euclidean space -/

/-- A pure power of the distance to `c` is locally integrable when the exponent is subcritical. -/
private lemma locallyIntegrable_norm_sub_rpow {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα : α < d)
    (c : Euc d) : LocallyIntegrable (fun x : Euc d => ‖x - c‖ ^ (-α)) volume := by
  have hdim : (1 : ℕ) ≤ Module.finrank ℝ (Euc d) := by
    rw [finrank_euclideanSpace_fin]
    exact hd
  have hα' : α < Module.finrank ℝ (Euc d) := by
    rw [finrank_euclideanSpace_fin]
    exact hα
  rw [locallyIntegrable_iff]
  intro K hK
  obtain ⟨R, hKR⟩ := hK.isBounded.subset_ball c
  refine IntegrableOn.mono_set ?_ hKR
  have hpres := measurePreserving_add_right volume c
  have hemb := (MeasurableEquiv.addRight c).measurableEmbedding
  have hpre : (fun z : Euc d => z + c) ⁻¹' ball c R = ball 0 R := by
    ext z
    simp [mem_ball, dist_eq_norm]
  rw [← hpres.integrableOn_comp_preimage hemb, hpre]
  refine integrableOn_ball_of_norm_le_rpow (μ := volume) (C := 1) hdim hα' ?_ ?_
  · filter_upwards with z
    simp only [Function.comp_apply, add_sub_cancel_right]
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    exact le_of_eq (one_mul _).symm
  · have hfun : ((fun x : Euc d => ‖x - c‖ ^ (-α)) ∘ fun z => z + c) =
        fun z => ‖z‖ ^ (-α) := by
      funext z
      rw [Function.comp_apply, add_sub_cancel_right]
    rw [hfun]
    refine (ContinuousOn.measurable_of_countable_compl (s := {z : Euc d | z ≠ 0}) ?_
      (by simp)).aestronglyMeasurable
    intro z hz
    exact ((continuous_norm.continuousAt (x := z)).rpow_const
      (Or.inl (norm_ne_zero_iff.mpr hz))).continuousWithinAt

/-- `‖x - c‖ ^ (-α)` times a compactly supported continuous function is integrable. -/
private lemma integrable_rpow_mul_compact {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα : α < d) {c : Euc d}
    {g : Euc d → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g) :
    Integrable (fun x : Euc d => g x * ‖x - c‖ ^ (-α)) volume := by
  have hloc := locallyIntegrable_norm_sub_rpow hd hα c
  simpa [smul_eq_mul] using hloc.integrable_smul_left_of_hasCompactSupport hg hgc

/-- The sharp radial singularity `(‖x‖ log (e / ‖x‖))^{-d}` is integrable on a small ball. -/
private lemma integrableOn_inv_norm_log_pow_ball {d : ℕ} (hd : 2 ≤ d) {R : ℝ} (hR : 0 < R)
    (hRle : R ≤ 1 / 2) : IntegrableOn (fun x : Euc d =>
      ((‖x‖ * Real.log (Real.exp 1 / ‖x‖))⁻¹) ^ d) (ball 0 R) := by
  have : Nontrivial (Euc d) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by
      rw [finrank_euclideanSpace_fin]
      omega)
  rw [integrableOn_fun_norm_addHaar (μ := volume)
    (f := fun r => ((r * Real.log (Real.exp 1 / r))⁻¹) ^ d)]
  refine (integrableOn_inv_mul_log_pow hd hR hRle).congr_fun ?_ measurableSet_Ioo
  intro y hy
  have hy0 : 0 < y := hy.1
  simp only [smul_eq_mul, finrank_euclideanSpace_fin]
  have hyn : y ^ (d - 1) * (y ^ d)⁻¹ = y⁻¹ := by
    rw [← Real.rpow_natCast y (d - 1), ← Real.rpow_natCast y d, ← Real.rpow_neg hy0.le,
      ← Real.rpow_add hy0]
    have hexp : ((d - 1 : ℕ) : ℝ) + (-(d : ℝ)) = -1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one]
      ring
    rw [hexp, Real.rpow_neg_one]
  calc (y * Real.log (Real.exp 1 / y) ^ d)⁻¹
      = y⁻¹ * (Real.log (Real.exp 1 / y) ^ d)⁻¹ := by rw [mul_inv]
    _ = (y ^ (d - 1) * (y ^ d)⁻¹) * (Real.log (Real.exp 1 / y) ^ d)⁻¹ := by rw [← hyn]
    _ = y ^ (d - 1) * ((y ^ d)⁻¹ * (Real.log (Real.exp 1 / y) ^ d)⁻¹) := by ring
    _ = y ^ (d - 1) * (y ^ d * Real.log (Real.exp 1 / y) ^ d)⁻¹ := by rw [mul_inv]
    _ = y ^ (d - 1) * ((y * Real.log (Real.exp 1 / y)) ^ d)⁻¹ := by rw [mul_pow]
    _ = y ^ (d - 1) * ((y * Real.log (Real.exp 1 / y))⁻¹) ^ d := by rw [inv_pow]

/-- Translated sharp singularity, centered at `c`. -/
private lemma integrableOn_inv_norm_log_pow_ball_center {d : ℕ} (hd : 2 ≤ d) {R : ℝ}
    (hR : 0 < R) (hRle : R ≤ 1 / 2) (c : Euc d) : IntegrableOn (fun x : Euc d =>
      ((‖x - c‖ * Real.log (Real.exp 1 / ‖x - c‖))⁻¹) ^ d) (ball c R) := by
  have hpres := measurePreserving_add_right volume c
  have hemb := (MeasurableEquiv.addRight c).measurableEmbedding
  have hpre : (fun z : Euc d => z + c) ⁻¹' ball c R = ball 0 R := by
    ext z
    simp [mem_ball, dist_eq_norm]
  rw [← hpres.integrableOn_comp_preimage hemb, hpre]
  have hfun : ((fun x : Euc d =>
      ((‖x - c‖ * Real.log (Real.exp 1 / ‖x - c‖))⁻¹) ^ d) ∘ fun z => z + c) =
      fun z => ((‖z‖ * Real.log (Real.exp 1 / ‖z‖))⁻¹) ^ d := by
    ext z
    simp [add_sub_cancel_right]
  rw [hfun]
  exact integrableOn_inv_norm_log_pow_ball hd hR hRle

/-- Pointwise bound for the cutoff at vanishing regularization. -/
private lemma norm_cutoffProfile_zero_le {c : E} (η : ContDiffBump c) (hOut : η.rOut ≤ 1 / 2)
    (x : E) : ‖cutoffProfile η (0 : ℝ) x‖ ≤ profileBound * ‖x - c‖ ^ (-(1 / 2 : ℝ)) := by
  by_cases hr0 : x = c
  · rw [hr0]
    have hzero : cutoffProfile η (0 : ℝ) c = 0 := by
      rw [cutoffProfile, regNorm_zero, sub_self, norm_zero, logLog, div_zero, Real.log_zero,
        Real.log_zero, mul_zero]
    rw [hzero, norm_zero, sub_self, norm_zero,
      Real.zero_rpow (by norm_num : (-(1 / 2 : ℝ)) ≠ 0), mul_zero]
  · by_cases hball : ‖x - c‖ ≤ η.rOut
    · have hr : 0 < ‖x - c‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hr0)
      have hs1 : ‖x - c‖ ≤ 1 := hball.trans (hOut.trans (by norm_num : (1 / 2 : ℝ) ≤ 1))
      have hlog := logLog_le hr hs1
      have hnonneg : 0 ≤ logLog ‖x - c‖ := logLog_nonneg hr hs1
      have hη : 0 ≤ η x := η.nonneg
      rw [cutoffProfile, regNorm_zero, Real.norm_of_nonneg (mul_nonneg hη hnonneg)]
      calc η x * logLog ‖x - c‖ ≤ 1 * logLog ‖x - c‖ := by gcongr; exact η.le_one
        _ ≤ profileBound * ‖x - c‖ ^ (-(1 / 2 : ℝ)) := by simpa using hlog
    · rw [← dist_eq_norm] at hball
      have hzero : cutoffProfile η 0 x = 0 := by
        rw [cutoffProfile, η.zero_of_le_dist (le_of_lt (lt_of_not_ge hball)), zero_mul]
      rw [hzero, norm_zero]
      exact mul_nonneg profileBound_pos.le (Real.rpow_nonneg (norm_nonneg _) _)

/-- The cutoff lies in `L^d`. -/
private lemma memLp_cutoffProfile_zero {d : ℕ} (hd : 2 ≤ d) {c : Euc d} (η : ContDiffBump c)
    (hOut : η.rOut ≤ 1 / 2) : MemLp (cutoffProfile η 0) (d : ℝ≥0∞) (volume : Measure (Euc d)) := by
  have hmeas : AEStronglyMeasurable (cutoffProfile η (0 : ℝ)) volume :=
    (continuousOn_cutoffProfile_zero η hOut).measurable_of_countable_compl
      (by simp : ({c}ᶜᶜ : Set (Euc d)).Countable) |>.aestronglyMeasurable
  rw [← integrable_norm_rpow_iff hmeas (by exact_mod_cast (by omega : d ≠ 0))
      (ENNReal.natCast_ne_top d), ENNReal.toReal_natCast]
  have hdom : Integrable (fun x : Euc d => (ball c η.rOut).indicator
      (fun x => profileBound ^ d * ‖x - c‖ ^ (-((d : ℝ) / 2))) x) volume := by
    rw [integrable_indicator_iff measurableSet_ball]
    have hpow : IntegrableOn (fun x : Euc d => ‖x - c‖ ^ (-((d : ℝ) / 2))) (ball c η.rOut) := by
      have hα : (d : ℝ) / 2 < d := by
        have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
        linarith
      have hloc := locallyIntegrable_norm_sub_rpow (by omega : 1 ≤ d) hα c
      exact hloc.integrableOn_isCompact (isCompact_closedBall c η.rOut) |>.mono_set
        ball_subset_closedBall
    exact hpow.const_mul _
  refine Integrable.mono' hdom ?_ ?_
  · refine AEStronglyMeasurable.congr
      (AEStronglyMeasurable.pow (AEStronglyMeasurable.norm hmeas) d) ?_
    filter_upwards with x
    rw [Pi.pow_apply]
    exact (Real.rpow_natCast (‖cutoffProfile η 0 x‖) d).symm
  · filter_upwards with x
    rw [Real.rpow_natCast, Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) _)]
    by_cases hx : x ∈ ball c η.rOut
    · rw [indicator_of_mem hx]
      have hle := norm_cutoffProfile_zero_le η hOut x
      have hpow : ‖cutoffProfile η 0 x‖ ^ d ≤
          (profileBound * ‖x - c‖ ^ (-(1 / 2 : ℝ))) ^ d :=
        pow_le_pow_left₀ (norm_nonneg _) hle _
      have hmul : (profileBound * ‖x - c‖ ^ (-(1 / 2 : ℝ))) ^ d =
          profileBound ^ d * ‖x - c‖ ^ (-((d : ℝ) / 2)) := by
        rw [mul_pow, ← Real.rpow_natCast (‖x - c‖ ^ (-(1 / 2 : ℝ))) d,
          ← Real.rpow_mul (norm_nonneg _)]
        have hexp : (-(1 / 2 : ℝ)) * (d : ℝ) = -((d : ℝ) / 2) := by ring
        rw [hexp]
      exact hpow.trans_eq hmul
    · rw [indicator_of_notMem hx, cutoffProfile]
      have hη : η x = 0 := η.zero_of_le_dist (by
        rw [dist_eq_norm]
        exact le_of_not_gt (by simpa [mem_ball, dist_eq_norm] using hx))
      rw [hη, zero_mul, norm_zero, zero_pow (by omega : d ≠ 0)]

/-- The algebraic derivative lies in `L^d`. -/
private lemma memLp_cutoffProfileFDeriv_zero {d : ℕ} (hd : 2 ≤ d) {c : Euc d}
    (η : ContDiffBump c) (hOut : η.rOut ≤ 1 / 2) {M : ℝ}
    (hM : ∀ x, ‖fderiv ℝ (η : Euc d → ℝ) x‖ ≤ M) (hM0 : 0 ≤ M) :
    MemLp (cutoffProfileFDeriv η (0 : ℝ)) (d : ℝ≥0∞) (volume : Measure (Euc d)) := by
  have hmeas : Measurable (cutoffProfileFDeriv η (0 : ℝ)) :=
    (continuousOn_cutoffProfileFDeriv_zero η hOut).measurable_of_countable_compl (by simp)
  have hsm : AEStronglyMeasurable (cutoffProfileFDeriv η (0 : ℝ)) volume :=
    hmeas.aestronglyMeasurable
  rw [← integrable_norm_rpow_iff hsm (by exact_mod_cast (by omega : d ≠ 0))
      (ENNReal.natCast_ne_top d), ENNReal.toReal_natCast]
  have hsing : IntegrableOn (fun x : Euc d =>
      ((‖x - c‖ * Real.log (Real.exp 1 / ‖x - c‖))⁻¹) ^ d) (ball c η.rOut) :=
    integrableOn_inv_norm_log_pow_ball_center hd η.rOut_pos hOut c
  have hreg : IntegrableOn (fun x : Euc d =>
      (M * profileBound) ^ d * ‖x - c‖ ^ (-((d : ℝ) / 2))) (ball c η.rOut) := by
    have hα : (d : ℝ) / 2 < d := by
      have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
      linarith
    have hpow : IntegrableOn (fun x : Euc d => ‖x - c‖ ^ (-((d : ℝ) / 2))) (ball c η.rOut) :=
      (locallyIntegrable_norm_sub_rpow (by omega) hα c).integrableOn_isCompact
        (isCompact_closedBall c η.rOut) |>.mono_set ball_subset_closedBall
    exact hpow.const_mul _
  have hsum : Integrable (fun x : Euc d => (ball c η.rOut).indicator
      (fun x => (2 : ℝ) ^ d *
        ((((‖x - c‖ * Real.log (Real.exp 1 / ‖x - c‖))⁻¹) ^ d) +
          (M * profileBound) ^ d * ‖x - c‖ ^ (-((d : ℝ) / 2)))) x) := by
    rw [integrable_indicator_iff measurableSet_ball]
    exact (hsing.add hreg).const_mul _
  refine Integrable.mono' hsum ?_ ?_
  · refine AEStronglyMeasurable.congr
      (AEStronglyMeasurable.pow (AEStronglyMeasurable.norm hsm) d) ?_
    filter_upwards with x
    rw [Pi.pow_apply]
    exact (Real.rpow_natCast (‖cutoffProfileFDeriv η 0 x‖) d).symm
  have hnull : volume (sphere c η.rOut) = 0 := by
    have : Nontrivial (Euc d) :=
      Module.nontrivial_of_finrank_pos (R := ℝ) (by
        rw [finrank_euclideanSpace_fin]
        omega)
    exact Measure.addHaar_sphere volume c η.rOut
  filter_upwards [compl_mem_ae_iff.mpr hnull] with x hx
  rw [Real.rpow_natCast, Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) _)]
  by_cases hball : ‖x - c‖ < η.rOut
  · have hxball : x ∈ ball c η.rOut := by
      rw [mem_ball, dist_eq_norm]
      exact hball
    rw [indicator_of_mem hxball]
    by_cases hr0 : x = c
    · rw [hr0]
      have hηc : fderiv ℝ (η : Euc d → ℝ) c = 0 := by
        simpa using η.eventuallyEq_one.fderiv_eq
      have hD : logLogFDeriv (0 : ℝ) c c = 0 := by
        rw [logLogFDeriv, sub_self, map_zero, smul_zero]
      rw [cutoffProfileFDeriv, hηc, hD, smul_zero, smul_zero, add_zero, norm_zero,
        zero_pow (by omega : d ≠ 0)]
      have hA0 : ((‖c - c‖ * Real.log (Real.exp 1 / ‖c - c‖))⁻¹) ^ d = 0 := by
        rw [sub_self, norm_zero, zero_mul, inv_zero, zero_pow (by omega : d ≠ 0)]
      have hB0 : ‖c - c‖ ^ (-((d : ℝ) / 2)) = 0 := by
        rw [sub_self, norm_zero]
        exact Real.zero_rpow (by
          have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
          exact neg_ne_zero.mpr (div_ne_zero hd0 two_ne_zero))
      rw [hA0, hB0, mul_zero, add_zero, mul_zero]
    · have hr : 0 < ‖x - c‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hr0)
      have hrle : ‖x - c‖ ≤ η.rOut := hball.le
      have hs1 : ‖x - c‖ ≤ 1 := hrle.trans (hOut.trans (by norm_num : (1 / 2 : ℝ) ≤ 1))
      set L : ℝ := Real.log (Real.exp 1 / ‖x - c‖)
      have hL : 1 ≤ L := one_le_log_exp_div hr hs1
      have hreg : 0 < regNorm 0 c x := by
        rw [regNorm_zero]
        exact hr
      have hLpos : 0 < Real.log (Real.exp 1 / regNorm 0 c x) := by
        rw [regNorm_zero]
        exact lt_of_lt_of_le zero_lt_one hL
      have hsing_le : ‖logLogFDeriv 0 c x‖ ≤ (‖x - c‖ * L)⁻¹ := by
        rw [norm_logLogFDeriv hreg hLpos, regNorm_zero]
        have : ‖x - c‖ / (‖x - c‖ ^ 2 * L) = (‖x - c‖ * L)⁻¹ := by
          field_simp
        exact le_of_eq this
      have hlog : logLog ‖x - c‖ ≤ profileBound * ‖x - c‖ ^ (-(1 / 2 : ℝ)) := logLog_le hr hs1
      have hlog0 : 0 ≤ logLog ‖x - c‖ := logLog_nonneg hr hs1
      have hsecond : ‖logLog ‖x - c‖ • fderiv ℝ (η : Euc d → ℝ) x‖ ≤
          M * profileBound * ‖x - c‖ ^ (-(1 / 2 : ℝ)) := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hlog0]
        calc logLog ‖x - c‖ * ‖fderiv ℝ (η : Euc d → ℝ) x‖
            ≤ logLog ‖x - c‖ * M := by gcongr; exact hM x
          _ ≤ profileBound * ‖x - c‖ ^ (-(1 / 2 : ℝ)) * M := by gcongr
          _ = M * profileBound * ‖x - c‖ ^ (-(1 / 2 : ℝ)) := by ring
      have hsplit : ‖cutoffProfileFDeriv η 0 x‖ ≤
          (‖x - c‖ * L)⁻¹ + M * profileBound * ‖x - c‖ ^ (-(1 / 2 : ℝ)) := by
        calc ‖cutoffProfileFDeriv η 0 x‖
            ≤ ‖η x • logLogFDeriv 0 c x‖ +
                ‖logLog (regNorm 0 c x) • fderiv ℝ (η : Euc d → ℝ) x‖ := norm_add_le _ _
          _ ≤ |η x| * ‖logLogFDeriv 0 c x‖ +
                ‖logLog ‖x - c‖ • fderiv ℝ (η : Euc d → ℝ) x‖ := by
              rw [norm_smul, Real.norm_eq_abs, regNorm_zero]
          _ ≤ 1 * (‖x - c‖ * L)⁻¹ +
                M * profileBound * ‖x - c‖ ^ (-(1 / 2 : ℝ)) := by
              refine add_le_add ?_ hsecond
              have hη1 : |η x| ≤ 1 := by
                rw [abs_of_nonneg η.nonneg]
                exact η.le_one
              exact mul_le_mul hη1 hsing_le (norm_nonneg _) zero_le_one
          _ = (‖x - c‖ * L)⁻¹ + M * profileBound * ‖x - c‖ ^ (-(1 / 2 : ℝ)) := by
              rw [one_mul]
      have hL0 : (0 : ℝ) ≤ L := le_trans zero_le_one hL
      have ha : 0 ≤ (‖x - c‖ * L)⁻¹ := inv_nonneg.mpr (mul_nonneg hr.le hL0)
      have hb : 0 ≤ M * profileBound * ‖x - c‖ ^ (-(1 / 2 : ℝ)) :=
        mul_nonneg (mul_nonneg hM0 profileBound_pos.le) (Real.rpow_nonneg (norm_nonneg _) _)
      have hpow := pow_le_pow_left₀ (norm_nonneg _) hsplit d
      have hadd := add_pow_le_two_pow_mul ha hb (n := d)
      have hA : ((‖x - c‖ * L)⁻¹) ^ d =
          ((‖x - c‖ * Real.log (Real.exp 1 / ‖x - c‖))⁻¹) ^ d := rfl
      have hB : (M * profileBound * ‖x - c‖ ^ (-(1 / 2 : ℝ))) ^ d =
          (M * profileBound) ^ d * ‖x - c‖ ^ (-((d : ℝ) / 2)) := by
        rw [mul_pow, ← Real.rpow_natCast (‖x - c‖ ^ (-(1 / 2 : ℝ))) d,
          ← Real.rpow_mul (norm_nonneg _)]
        have hexp : (-(1 / 2 : ℝ)) * (d : ℝ) = -((d : ℝ) / 2) := by ring
        rw [hexp]
      calc ‖cutoffProfileFDeriv η 0 x‖ ^ d
          ≤ ((‖x - c‖ * L)⁻¹ + M * profileBound * ‖x - c‖ ^ (-(1 / 2 : ℝ))) ^ d := hpow
        _ ≤ (2 : ℝ) ^ d * (((‖x - c‖ * L)⁻¹) ^ d +
            (M * profileBound * ‖x - c‖ ^ (-(1 / 2 : ℝ))) ^ d) := hadd
        _ = (2 : ℝ) ^ d * ((((‖x - c‖ * Real.log (Real.exp 1 / ‖x - c‖))⁻¹) ^ d) +
            (M * profileBound) ^ d * ‖x - c‖ ^ (-((d : ℝ) / 2))) := by rw [hA, hB]
  · rw [indicator_of_notMem (by simpa [mem_ball, dist_eq_norm] using hball)]
    have hrgt : η.rOut < ‖x - c‖ := lt_of_le_of_ne (le_of_not_gt hball) (by
      intro h
      exact hx (by rw [mem_sphere, dist_eq_norm, h]))
    simp [cutoffProfileFDeriv, η.zero_of_le_dist hrgt.le,
      fderiv_of_notMem_tsupport ℝ (by
        rw [η.tsupport_eq, mem_closedBall, dist_eq_norm]
        exact not_le.mpr hrgt)]
    exact le_of_eq (zero_pow (by omega : d ≠ 0))

/-- Integration by parts for the regularized cutoff, passed to the limit `t → 0⁺`. -/
private lemma integral_fderiv_mul_cutoff {d : ℕ} (hd : 2 ≤ d) {c : Euc d} (η : ContDiffBump c)
    (hOut : η.rOut ≤ 1 / 2) {M : ℝ} (hM : ∀ x, ‖fderiv ℝ (η : Euc d → ℝ) x‖ ≤ M) (hM0 : 0 ≤ M)
    {g : Euc d → ℝ} (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g) (v : Euc d) :
    ∫ x, fderiv ℝ g x v * cutoffProfile η 0 x =
      -∫ x, g x * cutoffProfileFDeriv η 0 x v := by
  have hcont_g : Continuous fun x : Euc d => ‖fderiv ℝ g x v‖ :=
    continuous_norm.comp <|
      (hg.continuous_fderiv_apply one_ne_zero).comp (continuous_id.prodMk continuous_const)
  have hcs_g : HasCompactSupport fun x : Euc d => ‖fderiv ℝ g x v‖ :=
    HasCompactSupport.norm (hgc.fderiv_apply ℝ v)
  have hbound_u : Integrable (fun x : Euc d =>
      ‖fderiv ℝ g x v‖ * (profileBound * ‖x - c‖ ^ (-(1 / 2 : ℝ)))) volume := by
    have hgc' : HasCompactSupport fun x : Euc d =>
        ‖fderiv ℝ g x v‖ * profileBound := hcs_g.mul_right
    have hcont' : Continuous fun x : Euc d => ‖fderiv ℝ g x v‖ * profileBound :=
      hcont_g.mul continuous_const
    have hα : (1 / 2 : ℝ) < d := by
      have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
      linarith
    have hint := integrable_rpow_mul_compact (c := c) (by omega) hα hcont' hgc'
    simpa [mul_assoc, mul_left_comm, mul_comm] using hint
  have hbound_U : Integrable (fun x : Euc d =>
      ‖g x‖ * ((1 + M * profileBound) * ‖v‖ * ‖x - c‖ ^ (-1 : ℝ))) volume := by
    have hgc' : HasCompactSupport fun x => ‖g x‖ * ((1 + M * profileBound) * ‖v‖) :=
      hgc.norm.mul_right
    have hcont' : Continuous fun x => ‖g x‖ * ((1 + M * profileBound) * ‖v‖) :=
      (continuous_norm.comp hg.continuous).mul continuous_const
    have hα : (1 : ℝ) < d := by exact_mod_cast (by omega : 1 < d)
    have hint := integrable_rpow_mul_compact (c := c) (by omega) hα hcont' hgc'
    simpa [mul_assoc, mul_left_comm, mul_comm] using hint
  have hibp : ∀ t, 0 < t → t ≤ 1 / 4 →
      ∫ x, cutoffProfile η t x * fderiv ℝ g x v =
        -∫ x, cutoffProfileFDeriv η t x v * g x := by
    intro t ht ht'
    have hcut : ∀ x, HasFDerivAt (cutoffProfile η t) (cutoffProfileFDeriv η t x) x :=
      fun x => hasFDerivAt_cutoffProfile η ht.le ht' hOut (Or.inl ht)
    have hfderiv : fderiv ℝ (cutoffProfile η t) = cutoffProfileFDeriv η t := by
      funext x
      exact (hcut x).fderiv
    have hcont : Continuous (cutoffProfile η t) :=
      continuous_iff_continuousAt.mpr fun x => (hcut x).continuousAt
    have hcs : HasCompactSupport (cutoffProfile η t) := η.hasCompactSupport.mul_right
    have hcontD : Continuous (cutoffProfileFDeriv η t) :=
      continuous_cutoffProfileFDeriv η ht ht' hOut
    suffices ∫ x, cutoffProfile η t x * fderiv ℝ g x v =
        -∫ x, (fderiv ℝ (cutoffProfile η t) x) v * g x by
      rw [hfderiv] at this
      exact this
    apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    · rw [hfderiv]
      have happ : Continuous fun x => cutoffProfileFDeriv η t x v :=
        (ContinuousLinearMap.apply ℝ ℝ v).continuous.comp hcontD
      have hcsApply : HasCompactSupport fun x => cutoffProfileFDeriv η t x v := by
        rw [← hfderiv]
        exact hcs.fderiv_apply ℝ v
      exact (happ.mul hg.continuous).integrable_of_hasCompactSupport hcsApply.mul_right
    · exact (hcont.mul ((hg.continuous_fderiv_apply one_ne_zero).comp
        (continuous_id.prodMk continuous_const))).integrable_of_hasCompactSupport
        (hcs.mul_right)
    · exact (hcont.mul hg.continuous).integrable_of_hasCompactSupport (hcs.mul_right)
    · intro x _; exact (hcut x).differentiableAt
    · intro x _; exact hg.differentiable one_ne_zero x
  have hsmall : Ioo (0 : ℝ) (1 / 4) ∈ 𝓝[>] 0 :=
    (nhdsGT_basis 0).mem_of_mem (by norm_num)
  have : Nontrivial (Euc d) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by
      rw [finrank_euclideanSpace_fin]
      omega)
  have hleft : Tendsto (fun t => ∫ x, cutoffProfile η t x * fderiv ℝ g x v) (𝓝[>] 0)
      (𝓝 (∫ x, cutoffProfile η 0 x * fderiv ℝ g x v)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun x => ‖fderiv ℝ g x v‖ * (profileBound * ‖x - c‖ ^ (-(1 / 2 : ℝ))))
      ?_ ?_ hbound_u ?_
    · filter_upwards [hsmall] with t ht
      have hcont : Continuous (cutoffProfile η t) :=
        continuous_iff_continuousAt.mpr fun x =>
          (hasFDerivAt_cutoffProfile η ht.1.le ht.2.le hOut (Or.inl ht.1)).continuousAt
      exact (hcont.mul ((hg.continuous_fderiv_apply one_ne_zero).comp
        (continuous_id.prodMk continuous_const))).measurable.aestronglyMeasurable
    · filter_upwards [hsmall] with t ht
      filter_upwards [compl_mem_ae_iff.mpr (measure_singleton c)] with x hx
      have hnonneg : 0 ≤ cutoffProfile η t x := by
        by_cases hball : ‖x - c‖ ≤ η.rOut
        · have hs : 0 < regNorm t c x := regNorm_pos ht.1 c x
          exact mul_nonneg η.nonneg (logLog_regNorm_nonneg η ht.1.le ht.2.le hOut hball hs)
        · rw [← dist_eq_norm] at hball
          rw [cutoffProfile, η.zero_of_le_dist (le_of_lt (lt_of_not_ge hball)), zero_mul]
      have hpoint : cutoffProfile η t x ≤ profileBound * ‖x - c‖ ^ (-(1 / 2 : ℝ)) := by
        by_cases hball : ‖x - c‖ ≤ η.rOut
        · have hr : 0 < ‖x - c‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hx)
          have hs : 0 < regNorm t c x := lt_of_lt_of_le hr (regNorm_ge_norm ht.1.le c x)
          have hs1 : regNorm t c x ≤ 1 := le_of_lt (regNorm_lt_one η ht.1.le ht.2.le hOut hball)
          have hlog := logLog_le hs hs1
          have hhalf : regNorm t c x ^ (-(1 / 2 : ℝ)) ≤ ‖x - c‖ ^ (-(1 / 2 : ℝ)) := by
            have hroot : ‖x - c‖ ^ (1 / 2 : ℝ) ≤ regNorm t c x ^ (1 / 2 : ℝ) :=
              Real.rpow_le_rpow hr.le (regNorm_ge_norm ht.1.le c x) (by norm_num)
            have hinv := inv_anti₀ (Real.rpow_pos_of_pos hr (1 / 2)) hroot
            simpa [Real.rpow_neg hr.le, Real.rpow_neg hs.le] using hinv
          calc cutoffProfile η t x = η x * logLog (regNorm t c x) := rfl
            _ ≤ 1 * logLog (regNorm t c x) := by
                exact mul_le_mul_of_nonneg_right (η.le_one (x := x)) (logLog_nonneg hs hs1)
            _ ≤ profileBound * regNorm t c x ^ (-(1 / 2 : ℝ)) := by
                rw [one_mul]
                exact hlog
            _ ≤ profileBound * ‖x - c‖ ^ (-(1 / 2 : ℝ)) :=
                mul_le_mul_of_nonneg_left hhalf profileBound_pos.le
        · rw [← dist_eq_norm] at hball
          rw [cutoffProfile, η.zero_of_le_dist (le_of_lt (lt_of_not_ge hball)), zero_mul]
          exact mul_nonneg profileBound_pos.le (Real.rpow_nonneg (norm_nonneg _) _)
      calc ‖cutoffProfile η t x * fderiv ℝ g x v‖
          = cutoffProfile η t x * ‖fderiv ℝ g x v‖ := by
            rw [norm_mul, Real.norm_of_nonneg hnonneg]
        _ ≤ (profileBound * ‖x - c‖ ^ (-(1 / 2 : ℝ))) * ‖fderiv ℝ g x v‖ :=
            mul_le_mul_of_nonneg_right hpoint (norm_nonneg _)
        _ = ‖fderiv ℝ g x v‖ * (profileBound * ‖x - c‖ ^ (-(1 / 2 : ℝ))) := by ring
    · filter_upwards [compl_mem_ae_iff.mpr (measure_singleton c)] with x hx
      have hlim : Tendsto (fun t => regNorm t c x) (𝓝[>] 0) (𝓝 ‖x - c‖) :=
        tendsto_regNorm_zero c x
      have hr : 0 < ‖x - c‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hx)
      have hψ : Tendsto (fun t => cutoffProfile η t x) (𝓝[>] 0) (𝓝 (cutoffProfile η 0 x)) := by
        by_cases hball : ‖x - c‖ ≤ η.rOut
        · have hlogC : ContinuousAt (logLog) ‖x - c‖ := by
            have hdiv : ContinuousAt (fun s => Real.exp 1 / s) ‖x - c‖ :=
              continuousAt_const.div continuousAt_id hr.ne'
            have hinner := hdiv.log (div_ne_zero (Real.exp_ne_zero _) hr.ne')
            have hs1 : ‖x - c‖ ≤ 1 :=
              hball.trans (hOut.trans (by norm_num : (1 / 2 : ℝ) ≤ 1))
            exact hinner.log (lt_of_lt_of_le zero_lt_one (one_le_log_exp_div hr hs1)).ne'
          have hreglog := hlogC.tendsto.comp hlim
          simpa [cutoffProfile, regNorm_zero] using tendsto_const_nhds.mul hreglog
        · rw [← dist_eq_norm] at hball
          have hzero : ∀ t, cutoffProfile η t x = 0 := by
            intro t
            rw [cutoffProfile, η.zero_of_le_dist (le_of_lt (lt_of_not_ge hball)), zero_mul]
          rw [hzero 0]
          refine Tendsto.congr' ?_ tendsto_const_nhds
          filter_upwards with t
          exact (hzero t).symm
      exact hψ.mul tendsto_const_nhds
  have hright : Tendsto (fun t => ∫ x, cutoffProfileFDeriv η t x v * g x) (𝓝[>] 0)
      (𝓝 (∫ x, cutoffProfileFDeriv η 0 x v * g x)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun x => ‖g x‖ * ((1 + M * profileBound) * ‖v‖ * ‖x - c‖ ^ (-1 : ℝ)))
      ?_ ?_ hbound_U ?_
    · filter_upwards [hsmall] with t ht
      have happ : Continuous fun x => cutoffProfileFDeriv η t x v :=
        (ContinuousLinearMap.apply ℝ ℝ v).continuous.comp
          (continuous_cutoffProfileFDeriv η ht.1 ht.2.le hOut)
      exact (happ.mul hg.continuous).measurable.aestronglyMeasurable
    · filter_upwards [hsmall] with t ht
      filter_upwards with x
      have hle := norm_cutoffProfileFDeriv_le η hM hM0 ht.1.le ht.2.le hOut x
      have happly : ‖cutoffProfileFDeriv η t x v‖ ≤
          (1 + M * profileBound) * ‖x - c‖ ^ (-1 : ℝ) * ‖v‖ := by
        calc ‖cutoffProfileFDeriv η t x v‖ ≤ ‖cutoffProfileFDeriv η t x‖ * ‖v‖ := le_opNorm _ _
          _ ≤ ((1 + M * profileBound) * ‖x - c‖ ^ (-1 : ℝ)) * ‖v‖ := by gcongr
          _ = (1 + M * profileBound) * ‖x - c‖ ^ (-1 : ℝ) * ‖v‖ := by ring
      calc ‖cutoffProfileFDeriv η t x v * g x‖
          = ‖cutoffProfileFDeriv η t x v‖ * ‖g x‖ := by rw [norm_mul]
        _ ≤ ((1 + M * profileBound) * ‖x - c‖ ^ (-1 : ℝ) * ‖v‖) * ‖g x‖ := by gcongr
        _ = ‖g x‖ * ((1 + M * profileBound) * ‖v‖ * ‖x - c‖ ^ (-1 : ℝ)) := by ring
    · filter_upwards with x
      have hlim : Tendsto (fun t => cutoffProfileFDeriv η t x v) (𝓝[>] 0)
          (𝓝 (cutoffProfileFDeriv η 0 x v)) := by
        by_cases hball : ‖x - c‖ ≤ η.rOut
        · by_cases hx : x = c
          · have hzero : ∀ t, 0 ≤ t → cutoffProfileFDeriv η t x = 0 := by
              intro t _ht
              have hηc : fderiv ℝ (η : Euc d → ℝ) c = 0 := by
                simpa using η.eventuallyEq_one.fderiv_eq
              rw [hx, cutoffProfileFDeriv, hηc, smul_zero, add_zero]
              simp [logLogFDeriv, sub_self, map_zero]
            have h0 : cutoffProfileFDeriv η 0 x v = 0 := by
              rw [hzero 0 le_rfl]
              rfl
            rw [h0]
            refine Tendsto.congr' ?_ tendsto_const_nhds
            filter_upwards [self_mem_nhdsWithin] with t ht
            rw [hzero t (le_of_lt ht)]
            rfl
          · have hr : 0 < ‖x - c‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hx)
            have hreg' : Tendsto (fun t => regNorm t c x) (𝓝[>] 0) (𝓝 ‖x - c‖) :=
              tendsto_regNorm_zero c x
            have hlogC : ContinuousAt logLog ‖x - c‖ := by
              have hdiv : ContinuousAt (fun s => Real.exp 1 / s) ‖x - c‖ :=
                continuousAt_const.div continuousAt_id hr.ne'
              have hs1 : ‖x - c‖ ≤ 1 :=
                hball.trans (hOut.trans (by norm_num : (1 / 2 : ℝ) ≤ 1))
              exact (hdiv.log (div_ne_zero (Real.exp_ne_zero _) hr.ne')).log
                (lt_of_lt_of_le zero_lt_one (one_le_log_exp_div hr hs1)).ne'
            have hdenC : ContinuousAt (fun s =>
                (s ^ 2 * Real.log (Real.exp 1 / s))⁻¹) ‖x - c‖ := by
              have hdiv : ContinuousAt (fun s => Real.exp 1 / s) ‖x - c‖ :=
                continuousAt_const.div continuousAt_id hr.ne'
              have hlog := hdiv.log (div_ne_zero (Real.exp_ne_zero _) hr.ne')
              have hmul := (continuousAt_id.pow 2).mul hlog
              have hs1 : ‖x - c‖ ≤ 1 :=
                hball.trans (hOut.trans (by norm_num : (1 / 2 : ℝ) ≤ 1))
              exact hmul.inv₀ (mul_ne_zero (pow_ne_zero 2 hr.ne')
                (lt_of_lt_of_le zero_lt_one (one_le_log_exp_div hr hs1)).ne')
            have hD : Tendsto (fun t => logLogFDeriv t c x) (𝓝[>] 0) (𝓝 (logLogFDeriv 0 c x)) := by
              have hcoef := hdenC.tendsto.comp hreg'
              simp only [logLogFDeriv, regNorm_zero] at hcoef ⊢
              exact (hcoef.neg).smul tendsto_const_nhds
            have hconst : Tendsto (fun _ : ℝ => fderiv ℝ (η : Euc d → ℝ) x) (𝓝[>] 0)
                (𝓝 (fderiv ℝ (η : Euc d → ℝ) x)) := tendsto_const_nhds
            have hψ : Tendsto
                (fun t => logLog (regNorm t c x) • fderiv ℝ (η : Euc d → ℝ) x) (𝓝[>] 0)
                (𝓝 (logLog ‖x - c‖ • fderiv ℝ (η : Euc d → ℝ) x)) :=
              (hlogC.tendsto.comp hreg').smul hconst
            have hηconst : Tendsto (fun _ : ℝ => η x) (𝓝[>] 0) (𝓝 (η x)) :=
              tendsto_const_nhds
            unfold cutoffProfileFDeriv
            rw [regNorm_zero]
            exact ((ContinuousLinearMap.apply ℝ ℝ v).continuous.continuousAt.tendsto.comp
              ((hηconst.smul hD).add hψ))
        · rw [← dist_eq_norm] at hball
          have hzero : ∀ t, cutoffProfileFDeriv η t x = 0 := by
            intro t
            have hxmem : x ∉ tsupport (η : Euc d → ℝ) := by
              rw [ContDiffBump.tsupport_eq, mem_closedBall]
              exact hball
            rw [cutoffProfileFDeriv,
              η.zero_of_le_dist (le_of_lt (lt_of_not_ge hball)), zero_smul,
              fderiv_of_notMem_tsupport ℝ hxmem, smul_zero, zero_add]
          have h0 : cutoffProfileFDeriv η 0 x v = 0 := by
            rw [hzero 0]
            rfl
          rw [h0]
          refine Tendsto.congr' ?_ tendsto_const_nhds
          filter_upwards with t
          rw [hzero t]
          rfl
      exact hlim.mul tendsto_const_nhds
  have hlim_left := hleft
  have hlim_right := hright.neg
  have heq_eventually :
      (fun t => ∫ x, cutoffProfile η t x * fderiv ℝ g x v) =ᶠ[𝓝[>] (0 : ℝ)]
        (fun t => -∫ x, cutoffProfileFDeriv η t x v * g x) := by
    filter_upwards [hsmall] with t ht
    exact hibp t ht.1 ht.2.le
  have hlim_ibp : Tendsto (fun t => ∫ x, cutoffProfile η t x * fderiv ℝ g x v) (𝓝[>] 0)
      (𝓝 (-∫ x, cutoffProfileFDeriv η 0 x v * g x)) :=
    Tendsto.congr' heq_eventually.symm hlim_right
  have hunique := tendsto_nhds_unique hlim_left hlim_ibp
  calc ∫ x, fderiv ℝ g x v * cutoffProfile η 0 x
      = ∫ x, cutoffProfile η 0 x * fderiv ℝ g x v := by
        refine integral_congr_ae (ae_of_all _ fun x => mul_comm _ _)
    _ = -∫ x, cutoffProfileFDeriv η 0 x v * g x := hunique
    _ = -∫ x, g x * cutoffProfileFDeriv η 0 x v := by
        refine congrArg Neg.neg (integral_congr_ae (ae_of_all _ fun x => mul_comm _ _))

/-- The cutoff is essentially unbounded. -/
private lemma not_memLp_top_cutoffProfile {d : ℕ} (_hd : 2 ≤ d) {c : Euc d}
    (Ω : TopologicalSpace.Opens (Euc d)) (η : ContDiffBump c)
    (hΩ : ball c η.rIn ⊆ (Ω : Set (Euc d))) :
    ¬ MemLp (cutoffProfile η (0 : ℝ)) ∞ (volume.restrict Ω) := by
  intro hLp
  have hsm := aestronglyMeasurable_of_eLpNorm_ne_top (memLp_iff.mp hLp).ne
  rw [memLp_iff, eLpNorm_exponent_top hsm,
    eLpNormEssSup_lt_top_iff_isBoundedUnder] at hLp
  obtain ⟨C, hC⟩ := hLp
  rw [eventually_map, ae_iff] at hC
  have : Nontrivial (Euc d) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by
      rw [finrank_euclideanSpace_fin]
      omega)
  have htend : Tendsto logLog (𝓝[>] 0) atTop := by
    have hinv : Tendsto (fun s : ℝ => Real.exp 1 / s) (𝓝[>] 0) atTop := by
      simpa [div_eq_mul_inv] using tendsto_inv_nhdsGT_zero.const_mul_atTop (Real.exp_pos _)
    exact Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp hinv)
  obtain ⟨δ, hδ0, hδ⟩ := (nhdsGT_basis (0 : ℝ)).mem_iff.mp
    (htend.eventually (eventually_gt_atTop ((C : ℝ) + 1)))
  set ρ : ℝ := min δ η.rIn
  have hρ : 0 < ρ := lt_min hδ0 η.rIn_pos
  have hS : ball c ρ \ {c} ⊆ {x | ¬ ‖cutoffProfile η 0 x‖₊ ≤ C} := by
    intro x hx
    have hdist : dist x c < ρ := by simpa [mem_ball] using hx.1
    have hx0 : x ≠ c := by simpa using hx.2
    have hr : 0 < ‖x - c‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hx0)
    have hrρ : ‖x - c‖ < ρ := by simpa [dist_eq_norm] using hdist
    have hlog : (C : ℝ) + 1 < logLog ‖x - c‖ :=
      hδ ⟨hr, lt_of_lt_of_le hrρ (min_le_left _ _)⟩
    have hη : η x = 1 := η.one_of_mem_closedBall <| by
      rw [mem_closedBall, dist_eq_norm]
      exact hrρ.le.trans (min_le_right _ _)
    have hu : cutoffProfile η 0 x = logLog ‖x - c‖ := by
      simp [cutoffProfile, regNorm_zero, hη]
    have hpos : 0 ≤ cutoffProfile η 0 x := by
      rw [hu]
      linarith [NNReal.coe_nonneg C]
    have hgt : (C : ℝ) < cutoffProfile η 0 x := by
      rw [hu]
      linarith
    have hnn : C < ‖cutoffProfile η 0 x‖₊ := by
      rw [← NNReal.coe_lt_coe, coe_nnnorm, Real.norm_of_nonneg hpos]
      exact hgt
    exact not_le.mpr hnn
  have hsubΩ : ball c ρ \ {c} ⊆ (Ω : Set (Euc d)) := by
    intro x hx
    exact hΩ (ball_subset_ball (min_le_right _ _) hx.1)
  have hpos : 0 < volume (ball c ρ \ {c}) := by
    have hsub : {c} ⊆ ball c ρ := by
      intro x hx
      rw [mem_singleton_iff] at hx
      rw [hx]
      exact mem_ball_self hρ
    rw [measure_sdiff hsub (nullMeasurableSet_singleton c) (by
      rw [measure_singleton]
      exact ENNReal.zero_ne_top)]
    simp [measure_singleton, measure_ball_pos volume c hρ]
  have hzero : volume ({x | ¬ ‖cutoffProfile η 0 x‖₊ ≤ C} ∩ (Ω : Set _)) = 0 := by
    simpa [Measure.restrict_apply' Ω.isOpen.measurableSet] using hC
  have hle : volume (ball c ρ \ {c}) ≤
      volume ({x | ¬ ‖cutoffProfile η 0 x‖₊ ≤ C} ∩ (Ω : Set _)) := by
    apply measure_mono
    intro x hx
    exact ⟨hS hx, hsubΩ hx⟩
  exact (not_lt_of_ge (hle.trans_eq hzero)) hpos

/-- **26.16**: every nonempty open Euclidean domain in dimension at least two contains an
unbounded `W^{1,d}` function. The `L∞` failure is essential, rather than merely pointwise. -/
theorem exists_memSobolev_not_memLp_top {d : ℕ} (hd : 2 ≤ d)
    (Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))) (hne : (Ω : Set (EuclideanSpace ℝ (Fin
      d))).Nonempty) :
    ∃ (u : EuclideanSpace ℝ (Fin d) → ℝ)
      (U : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ),
      MemLp u (d : ℝ≥0∞) (volume.restrict Ω) ∧
      MemLp U (d : ℝ≥0∞) (volume.restrict Ω) ∧
      TauCeti.HasWeakFDerivOn volume Ω u U ∧ ¬ MemLp u ∞ (volume.restrict Ω) := by
  obtain ⟨c, hc⟩ := hne
  obtain ⟨ε, hε, hεΩ⟩ := Metric.mem_nhds_iff.mp (Ω.isOpen.mem_nhds hc)
  set R : ℝ := min (ε / 2) (1 / 2)
  have hR : 0 < R := by
    have hε2 : 0 < ε / 2 := half_pos hε
    exact lt_min hε2 (by norm_num)
  have hRout : R ≤ 1 / 2 := min_le_right _ _
  have hball : closedBall c R ⊆ (Ω : Set (Euc d)) := by
    intro x hx
    apply hεΩ
    have hdist : dist x c ≤ R := by simpa [mem_closedBall] using hx
    have : dist x c < ε := lt_of_le_of_lt (hdist.trans (min_le_left _ _)) (half_lt_self hε)
    simpa [mem_ball] using this
  let η : ContDiffBump c := ⟨R / 2, R, half_pos hR, half_lt_self hR⟩
  have hOut : η.rOut ≤ 1 / 2 := by simpa [η] using hRout
  have hIn : ball c η.rIn ⊆ (Ω : Set (Euc d)) := by
    intro x hx
    apply hball
    have : dist x c ≤ η.rIn := le_of_lt (by simpa [mem_ball] using hx)
    exact closedBall_subset_closedBall (le_of_lt η.rIn_lt_rOut) (mem_closedBall.mpr this)
  obtain ⟨M, hM0, hM⟩ := exists_bound_norm_fderiv_bump η
  refine ⟨cutoffProfile η 0, cutoffProfileFDeriv η 0, ?_, ?_, ?_, ?_⟩
  · exact (memLp_cutoffProfile_zero hd η hOut).mono_measure Measure.restrict_le_self
  · exact (memLp_cutoffProfileFDeriv_zero hd η hOut hM hM0).mono_measure Measure.restrict_le_self
  · refine TauCeti.hasWeakFDerivOn_of_forall_integral_fderiv_smul ?_ ?_ ?_ Ω
    · have hα : (1 / 2 : ℝ) < d := by
        have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
        linarith
      have hloc := locallyIntegrable_norm_sub_rpow (by omega) hα c
      have hdom : LocallyIntegrable
          (fun x : Euc d => profileBound • ‖x - c‖ ^ (-(1 / 2 : ℝ))) volume :=
        (locallyIntegrable_smul_iff profileBound).2 (Or.inr hloc)
      have hmeas : AEStronglyMeasurable (cutoffProfile η (0 : ℝ))
          (volume : Measure (Euc d)) :=
        ((continuousOn_cutoffProfile_zero η hOut).measurable_of_countable_compl
          (by simp)).aestronglyMeasurable
      refine hdom.mono hmeas (ae_of_all _ fun x => ?_)
      rw [smul_eq_mul, Real.norm_of_nonneg (mul_nonneg profileBound_pos.le
          (Real.rpow_nonneg (norm_nonneg _) _))]
      exact norm_cutoffProfile_zero_le η hOut x
    · have hα : (1 : ℝ) < d := by exact_mod_cast (by omega : 1 < d)
      have hloc := locallyIntegrable_norm_sub_rpow (by omega) hα c
      have hKpos : 0 ≤ 1 + M * profileBound :=
        add_nonneg zero_le_one (mul_nonneg hM0 profileBound_pos.le)
      have hdom : LocallyIntegrable
          (fun x : Euc d => (1 + M * profileBound) • ‖x - c‖ ^ (-1 : ℝ)) volume :=
        (locallyIntegrable_smul_iff (1 + M * profileBound)).2 (Or.inr hloc)
      have hmeas : AEStronglyMeasurable (cutoffProfileFDeriv η (0 : ℝ))
          (volume : Measure (Euc d)) :=
        ((continuousOn_cutoffProfileFDeriv_zero η hOut).measurable_of_countable_compl
          (by simp)).aestronglyMeasurable
      refine hdom.mono hmeas (ae_of_all _ fun x => ?_)
      rw [smul_eq_mul, Real.norm_of_nonneg (mul_nonneg hKpos
          (Real.rpow_nonneg (norm_nonneg _) _))]
      exact norm_cutoffProfileFDeriv_le η hM hM0 le_rfl (by norm_num) hOut x
    · intro g hg hgc v
      have h := integral_fderiv_mul_cutoff hd η hOut hM hM0 hg hgc v
      simpa [smul_eq_mul] using h
  · exact not_memLp_top_cutoffProfile hd Ω η hIn

end CKMA
