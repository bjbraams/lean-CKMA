/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.Sobolev.Critical.Bounds
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Regularized critical profile on an inner product space

A smooth cutoff times `logLog` of the regularized radius `√(‖x - c‖² + t)`. The product rule
gives an algebraic derivative, with a gradient bound that remains integrable down to `t = 0`.
Cross-file rewriting uses the defining equations `regNorm_def`, `logLogFDeriv_apply`,
`cutoffProfile_apply` and `cutoffProfileFDeriv_apply`.

## Main definitions

* `CKMA.regNorm`: regularized radius `√(‖x - c‖² + t)`.
* `CKMA.logLogFDeriv`: algebraic derivative of `logLog ∘ regNorm`.
* `CKMA.cutoffProfile`: cutoff times the regularized double logarithm.
* `CKMA.cutoffProfileFDeriv`: product-rule derivative of the cutoff profile.

## Main results

* `CKMA.hasFDerivAt_cutoffProfile`: differentiability for small nonnegative regularization,
  away from the center when `t = 0`.
* `CKMA.norm_cutoffProfileFDeriv_le`: the gradient bound `‖D(cutoff)‖ ≤ K / ‖x - c‖`.
-/

public section

noncomputable section

namespace CKMA

open MeasureTheory Metric Set Filter Topology ContinuousLinearMap
open scoped ENNReal RealInnerProductSpace NNReal

/-! ### Regularized profile -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Regularized radius `√(‖x - c‖² + t)`. -/
@[expose]
def regNorm (t : ℝ) (c x : E) : ℝ :=
  Real.sqrt (‖x - c‖ ^ 2 + t)

omit [InnerProductSpace ℝ E] in
/-- Defining equation of `regNorm`. -/
lemma regNorm_def (t : ℝ) (c x : E) : regNorm t c x = Real.sqrt (‖x - c‖ ^ 2 + t) := rfl

/-- Candidate derivative of `logLog ∘ regNorm`. -/
@[expose]
def logLogFDeriv (t : ℝ) (c x : E) : E →L[ℝ] ℝ :=
  (-(regNorm t c x ^ 2 * Real.log (Real.exp 1 / regNorm t c x))⁻¹) • innerSL ℝ (x - c)

/-- Defining equation of `logLogFDeriv`. -/
lemma logLogFDeriv_apply (t : ℝ) (c x : E) :
    logLogFDeriv t c x =
      (-(regNorm t c x ^ 2 * Real.log (Real.exp 1 / regNorm t c x))⁻¹) •
        innerSL ℝ (x - c) := rfl

/-- Smooth cutoff times the regularized double logarithm. -/
@[expose]
def cutoffProfile {c : E} (η : ContDiffBump c) (t : ℝ) (x : E) : ℝ :=
  η x * logLog (regNorm t c x)

/-- Defining equation of `cutoffProfile`. -/
lemma cutoffProfile_apply {c : E} (η : ContDiffBump c) (t : ℝ) (x : E) :
    cutoffProfile η t x = η x * logLog (regNorm t c x) := rfl

/-- Product rule for the cutoff, using the algebraic derivative of the profile. -/
@[expose]
def cutoffProfileFDeriv {c : E} (η : ContDiffBump c) (t : ℝ) (x : E) : E →L[ℝ] ℝ :=
  η x • logLogFDeriv t c x + logLog (regNorm t c x) • fderiv ℝ (η : E → ℝ) x

/-- Defining equation of `cutoffProfileFDeriv`. -/
lemma cutoffProfileFDeriv_apply {c : E} (η : ContDiffBump c) (t : ℝ) (x : E) :
    cutoffProfileFDeriv η t x =
      η x • logLogFDeriv t c x +
        logLog (regNorm t c x) • fderiv ℝ (η : E → ℝ) x := rfl

omit [InnerProductSpace ℝ E] in
/-- Square of the regularized radius. -/
private lemma regNorm_sq {t : ℝ} (ht : 0 ≤ t) (c x : E) :
    regNorm t c x ^ 2 = ‖x - c‖ ^ 2 + t :=
  Real.sq_sqrt (by positivity)

omit [InnerProductSpace ℝ E] in
/-- At `t = 0` the regularized radius is the distance to the center. -/
lemma regNorm_zero (c x : E) : regNorm 0 c x = ‖x - c‖ := by
  simp [regNorm, Real.sqrt_sq (norm_nonneg _)]

omit [InnerProductSpace ℝ E] in
/-- The regularized radius is at least the distance to the center. -/
lemma regNorm_ge_norm {t : ℝ} (ht : 0 ≤ t) (c x : E) :
    ‖x - c‖ ≤ regNorm t c x := by
  rw [← Real.sqrt_sq (norm_nonneg _), regNorm]
  exact Real.sqrt_le_sqrt (le_add_of_nonneg_right ht)

omit [InnerProductSpace ℝ E] in
/-- Positive regularization stays positive. -/
lemma regNorm_pos {t : ℝ} (ht : 0 < t) (c x : E) : 0 < regNorm t c x := by
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
lemma tendsto_regNorm_zero (c x : E) :
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
lemma regNorm_lt_one {c : E} (η : ContDiffBump c) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 4)
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
lemma logLog_regNorm_nonneg {c : E} (η : ContDiffBump c) {t : ℝ} (ht0 : 0 ≤ t)
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
lemma hasFDerivAt_cutoffProfile {c : E} (η : ContDiffBump c) {t : ℝ} (ht0 : 0 ≤ t)
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
lemma exists_bound_norm_fderiv_bump [FiniteDimensional ℝ E] {c : E} (η : ContDiffBump c) :
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
lemma norm_logLogFDeriv {t : ℝ} {c x : E} (hs : 0 < regNorm t c x)
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
lemma norm_cutoffProfileFDeriv_le {c : E} (η : ContDiffBump c)
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
lemma continuous_cutoffProfileFDeriv {c : E} (η : ContDiffBump c) {t : ℝ} (ht0 : 0 < t)
    (ht1 : t ≤ 1 / 4) (hOut : η.rOut ≤ 1 / 2) : Continuous (cutoffProfileFDeriv η t) :=
  continuous_iff_continuousAt.mpr fun x =>
    continuousAt_cutoffProfileFDeriv η ht0.le ht1 hOut (Or.inl ht0) (x := x)

/-- The singular profile is continuous away from its center. -/
lemma continuousOn_cutoffProfile_zero {c : E} (η : ContDiffBump c) (hOut : η.rOut ≤ 1 / 2) :
    ContinuousOn (cutoffProfile η 0) {c}ᶜ := by
  intro x hx
  have hderiv := hasFDerivAt_cutoffProfile η le_rfl (by norm_num) hOut (Or.inr hx)
  exact hderiv.continuousAt.continuousWithinAt

/-- The algebraic derivative at `t = 0` is continuous away from the center. -/
lemma continuousOn_cutoffProfileFDeriv_zero {c : E} (η : ContDiffBump c)
    (hOut : η.rOut ≤ 1 / 2) : ContinuousOn (cutoffProfileFDeriv η 0) {c}ᶜ := by
  intro x hx
  exact (continuousAt_cutoffProfileFDeriv η le_rfl (by norm_num) hOut
    (Or.inr hx)).continuousWithinAt


end CKMA
