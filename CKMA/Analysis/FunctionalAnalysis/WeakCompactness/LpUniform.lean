/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.FunctionalAnalysis.WeakCompactness.LpUniform.Young
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.Convex.Uniform
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.MeasureTheory.Measure.WithDensity

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Uniform convexity of scalar Lp

Scalar `Lp` is uniformly convex for every exponent strictly between one and infinity. The argument
is Hanche-Olsen's, *On the uniform convexity of Lp*, Proceedings of the American Mathematical
Society 134 (2006), 2359–2362 (arXiv:math/0502021). A Young defect controls thin slices of the unit
ball of `Lp` on a probability space, and the general slice is reduced to that case by the measure
`‖v‖ ^ p ∂μ` built from an explicit dual weight.
-/

@[expose] public section

noncomputable section

set_option linter.style.haveILetI false

namespace CKMA.WeakCompactness

open Filter MeasureTheory Real Set Topology
open scoped ENNReal

variable {𝕜 : Type*} [RCLike 𝕜]

/-- Off the sphere of radius `ε`, the Young defect dominates; inside it, the constant `ε ^ p`
does. -/
theorem norm_sub_one_rpow_le_youngDefect_add {p : ℝ} (hp : 1 < p) {ε α : ℝ} (hε : 0 ≤ ε)
    (hα0 : 0 ≤ α) (hα : ∀ u : 𝕜, ε ≤ ‖u - 1‖ → ‖u - 1‖ ^ p ≤ α * youngDefect p u) (u : 𝕜) :
    ‖u - 1‖ ^ p ≤ ε ^ p + α * youngDefect p u := by
  by_cases h : ε ≤ ‖u - 1‖
  · linarith [hα u h, rpow_nonneg hε p]
  · push Not at h
    have hle : ‖u - 1‖ ^ p ≤ ε ^ p := rpow_le_rpow (norm_nonneg _) (le_of_lt h) (by linarith)
    have hnn : 0 ≤ α * youngDefect p u := mul_nonneg hα0 (youngDefect_nonneg hp u)
    linarith

/-- An `ℒp` bound `eLpNorm ≤ ofReal c` controls the integral of the powered norm. -/
theorem integral_norm_rpow_le_of_eLpNorm_le {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    {p₀ : ℝ} (hp : 0 < p₀) {z : Ω → 𝕜} (hz : MemLp z (.ofReal p₀) ν) {c : ℝ} (hc : 0 ≤ c)
    (hnorm : eLpNorm z (.ofReal p₀) ν ≤ .ofReal c) :
    ∫ ω, ‖z ω‖ ^ p₀ ∂ν ≤ c ^ p₀ := by
  have hp0 : ENNReal.ofReal p₀ ≠ 0 := ENNReal.ofReal_ne_zero_iff.2 hp
  have hform := hz.eLpNorm_eq_integral_rpow_norm hp0 ENNReal.ofReal_ne_top
  have hint0 : 0 ≤ ∫ ω, ‖z ω‖ ^ p₀ ∂ν := integral_nonneg fun _ ↦ rpow_nonneg (norm_nonneg _) _
  have hroot : (∫ ω, ‖z ω‖ ^ p₀ ∂ν) ^ p₀⁻¹ ≤ c := by
    have hle : ENNReal.ofReal ((∫ ω, ‖z ω‖ ^ p₀ ∂ν) ^ p₀⁻¹) ≤ .ofReal c := by
      simpa [hform, ENNReal.toReal_ofReal hp.le, one_div] using hnorm
    exact (ENNReal.ofReal_le_ofReal_iff hc).1 hle
  rw [← rpow_one (∫ ω, ‖z ω‖ ^ p₀ ∂ν), ← inv_mul_cancel₀ hp.ne', rpow_mul hint0]
  exact rpow_le_rpow (rpow_nonneg hint0 _) hroot hp.le

/-- A strict integral bound on the powered norm is a strict `ℒp` bound. -/
theorem eLpNorm_lt_of_integral_norm_rpow_lt {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    {p₀ : ℝ} (hp : 0 < p₀) {z : Ω → 𝕜} (hz : MemLp z (.ofReal p₀) ν) {η : ℝ} (hη : 0 < η)
    (hint : ∫ ω, ‖z ω‖ ^ p₀ ∂ν < η ^ p₀) :
    eLpNorm z (.ofReal p₀) ν < .ofReal η := by
  have hp0 : ENNReal.ofReal p₀ ≠ 0 := ENNReal.ofReal_ne_zero_iff.2 hp
  have hint0 : 0 ≤ ∫ ω, ‖z ω‖ ^ p₀ ∂ν := integral_nonneg fun _ ↦ rpow_nonneg (norm_nonneg _) _
  have hroot : (∫ ω, ‖z ω‖ ^ p₀ ∂ν) ^ p₀⁻¹ < η := by
    rw [← rpow_lt_rpow_iff (rpow_nonneg hint0 _) hη.le hp, ← rpow_mul hint0,
      inv_mul_cancel₀ hp.ne', rpow_one]
    exact hint
  rw [hz.eLpNorm_eq_integral_rpow_norm hp0 ENNReal.ofReal_ne_top]
  simpa [ENNReal.toReal_ofReal hp.le, one_div] using (ENNReal.ofReal_lt_ofReal_iff hη).2 hroot

/-- A strict `ℒp` bound is a strict integral bound on the powered norm. -/
theorem integral_norm_rpow_lt_of_eLpNorm_lt {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    {p₀ : ℝ} (hp : 0 < p₀) {z : Ω → 𝕜} (hz : MemLp z (.ofReal p₀) ν) {η : ℝ} (hη : 0 < η)
    (hnorm : eLpNorm z (.ofReal p₀) ν < .ofReal η) :
    ∫ ω, ‖z ω‖ ^ p₀ ∂ν < η ^ p₀ := by
  have hp0 : ENNReal.ofReal p₀ ≠ 0 := ENNReal.ofReal_ne_zero_iff.2 hp
  have hint0 : 0 ≤ ∫ ω, ‖z ω‖ ^ p₀ ∂ν := integral_nonneg fun _ ↦ rpow_nonneg (norm_nonneg _) _
  have hform := hz.eLpNorm_eq_integral_rpow_norm hp0 ENNReal.ofReal_ne_top
  have hroot : (∫ ω, ‖z ω‖ ^ p₀ ∂ν) ^ p₀⁻¹ < η := by
    have hlt : ENNReal.ofReal ((∫ ω, ‖z ω‖ ^ p₀ ∂ν) ^ p₀⁻¹) < .ofReal η := by
      simpa [hform, ENNReal.toReal_ofReal hp.le, one_div] using hnorm
    exact (ENNReal.ofReal_lt_ofReal_iff hη).1 hlt
  have hpow : ((∫ ω, ‖z ω‖ ^ p₀ ∂ν) ^ p₀⁻¹) ^ p₀ < η ^ p₀ :=
    rpow_lt_rpow (rpow_nonneg hint0 _) hroot hp
  rw [← rpow_mul hint0, inv_mul_cancel₀ hp.ne', rpow_one] at hpow
  exact hpow

/-- Unit `ℒp` norm means that the powered norm integrates to one. -/
theorem integral_norm_rpow_of_eLpNorm_eq_one {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    {p₀ : ℝ} (hp : 0 < p₀) {z : Ω → 𝕜} (hz : MemLp z (.ofReal p₀) ν)
    (hnorm : eLpNorm z (.ofReal p₀) ν = 1) :
    ∫ ω, ‖z ω‖ ^ p₀ ∂ν = 1 := by
  have hp0 : ENNReal.ofReal p₀ ≠ 0 := ENNReal.ofReal_ne_zero_iff.2 hp
  have hform := hz.eLpNorm_eq_integral_rpow_norm hp0 ENNReal.ofReal_ne_top
  have hint0 : 0 ≤ ∫ ω, ‖z ω‖ ^ p₀ ∂ν := integral_nonneg fun _ ↦ rpow_nonneg (norm_nonneg _) _
  have hroot : (∫ ω, ‖z ω‖ ^ p₀ ∂ν) ^ p₀⁻¹ = 1 := by
    have hle : ENNReal.ofReal ((∫ ω, ‖z ω‖ ^ p₀ ∂ν) ^ p₀⁻¹) = ENNReal.ofReal 1 := by
      simpa [hform, ENNReal.toReal_ofReal hp.le, one_div, ENNReal.ofReal_one] using hnorm
    exact (ENNReal.ofReal_eq_ofReal_iff (rpow_nonneg hint0 _) zero_le_one).1 hle
  have hpow : ((∫ ω, ‖z ω‖ ^ p₀ ∂ν) ^ p₀⁻¹) ^ p₀ = ∫ ω, ‖z ω‖ ^ p₀ ∂ν := by
    rw [← rpow_mul hint0, inv_mul_cancel₀ hp.ne', rpow_one]
  rw [← hpow, hroot, one_rpow]

/-- `MemLp` supplies integrability of the pointwise powered norm. -/
theorem integrable_norm_rpow_of_memLp {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} {p₀ : ℝ}
    (hp : 0 < p₀) {z : Ω → 𝕜} (hz : MemLp z (.ofReal p₀) ν) :
    Integrable (fun ω ↦ ‖z ω‖ ^ p₀) ν := by
  rw [← ENNReal.toReal_ofReal hp.le]
  exact hz.integrable_norm_rpow (ENNReal.ofReal_ne_zero_iff.2 hp) ENNReal.ofReal_ne_top

/-- **Hanche-Olsen, Lemma 1.** On a probability space, an `ℒp` function of norm at most one whose
real part integrates close to one is close to the constant `1`. -/
theorem exists_eLpNorm_sub_one_lt {p₀ : ℝ} (hp : 1 < p₀) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν]
      {z : Ω → 𝕜}, MemLp z (.ofReal p₀) ν → eLpNorm z (.ofReal p₀) ν ≤ 1 →
      1 - δ < ∫ ω, RCLike.re (z ω) ∂ν →
      eLpNorm (fun ω ↦ z ω - 1) (.ofReal p₀) ν < .ofReal η := by
  let ε : ℝ := η / (2 : ℝ) ^ p₀⁻¹
  have hε : 0 < ε := by positivity
  obtain ⟨α, hα, hα'⟩ := exists_youngDefect_mul_le (𝕜 := 𝕜) hp hε
  refine ⟨ε ^ p₀ / (α * p₀), by positivity, ?_⟩
  intro Ω _ ν _ z hz hnorm hre
  have hp0 : 0 < p₀ := zero_lt_one.trans hp
  have hpow : Integrable (fun ω ↦ ‖z ω‖ ^ p₀) ν := integrable_norm_rpow_of_memLp hp0 hz
  have hint_pow : ∫ ω, ‖z ω‖ ^ p₀ ∂ν ≤ 1 := by
    simpa using integral_norm_rpow_le_of_eLpNorm_le hp0 hz zero_le_one (by simpa using hnorm)
  have hz1 : Integrable z ν :=
    memLp_one_iff_integrable.mp <|
      hz.mono_exponent ((ENNReal.one_le_ofReal).2 (by linarith))
  have hre_int : Integrable (fun ω ↦ RCLike.re (z ω)) ν :=
    hz1.norm.mono (RCLike.continuous_re.comp_aestronglyMeasurable hz.aestronglyMeasurable)
      (ae_of_all _ fun ω ↦ by simpa using RCLike.abs_re_le_norm (z ω))
  have hmul : Integrable (fun ω ↦ p₀ * RCLike.re (z ω)) ν := hre_int.const_mul _
  have hdef_fun : (fun ω ↦ youngDefect p₀ (z ω)) =
      ((fun ω ↦ ‖z ω‖ ^ p₀) - fun ω ↦ p₀ * RCLike.re (z ω)) + fun _ ↦ (p₀ - 1) := by
    ext ω
    rw [Pi.add_apply, Pi.sub_apply, youngDefect_eq]
    ring
  have hdef_int : Integrable (fun ω ↦ youngDefect p₀ (z ω)) ν := by
    rw [hdef_fun]
    exact (hpow.sub hmul).add (integrable_const _)
  have hint_def : ∫ ω, youngDefect p₀ (z ω) ∂ν =
      (∫ ω, ‖z ω‖ ^ p₀ ∂ν) - p₀ * ∫ ω, RCLike.re (z ω) ∂ν + p₀ - 1 := by
    rw [hdef_fun, integral_add' (hpow.sub hmul) (integrable_const (p₀ - 1)),
      integral_sub' hpow hmul, integral_const_mul, integral_const, probReal_univ, one_smul]
    ring
  have hint_lt : ∫ ω, youngDefect p₀ (z ω) ∂ν < p₀ * (ε ^ p₀ / (α * p₀)) := by
    have hgap : 1 - ∫ ω, RCLike.re (z ω) ∂ν < ε ^ p₀ / (α * p₀) := by linarith
    have hrew : ∫ ω, youngDefect p₀ (z ω) ∂ν =
        (∫ ω, ‖z ω‖ ^ p₀ ∂ν) - 1 + p₀ * (1 - ∫ ω, RCLike.re (z ω) ∂ν) := by
      rw [hint_def]
      ring
    rw [hrew]
    linarith [mul_lt_mul_of_pos_left hgap hp0]
  have hzsub : MemLp (fun ω ↦ z ω - 1) (.ofReal p₀) ν := hz.sub (memLp_const 1)
  have hleft : Integrable (fun ω ↦ ‖z ω - 1‖ ^ p₀) ν :=
    integrable_norm_rpow_of_memLp hp0 hzsub
  have hright : Integrable (fun ω ↦ ε ^ p₀ + α * youngDefect p₀ (z ω)) ν :=
    (integrable_const _).add (hdef_int.const_mul _)
  have hpoint : ∫ ω, ‖z ω - 1‖ ^ p₀ ∂ν ≤
      ∫ ω, ε ^ p₀ + α * youngDefect p₀ (z ω) ∂ν :=
    integral_mono hleft hright fun ω ↦
      norm_sub_one_rpow_le_youngDefect_add hp hε.le hα.le hα' (z ω)
  have hint_sub : ∫ ω, ‖z ω - 1‖ ^ p₀ ∂ν < η ^ p₀ := by
    have hsplit : ∫ ω, ε ^ p₀ + α * youngDefect p₀ (z ω) ∂ν =
        ε ^ p₀ + α * ∫ ω, youngDefect p₀ (z ω) ∂ν := by
      rw [integral_add (integrable_const _) (hdef_int.const_mul _), integral_const_mul,
        integral_const]
      simp [probReal_univ]
    have htwo : 2 * ε ^ p₀ = η ^ p₀ := by
      have hden : ((2 : ℝ) ^ p₀⁻¹) ^ p₀ = 2 := by
        rw [← rpow_mul (by positivity), inv_mul_cancel₀ hp0.ne', rpow_one]
      calc
        2 * ε ^ p₀ = 2 * (η / (2 : ℝ) ^ p₀⁻¹) ^ p₀ := rfl
        _ = 2 * (η ^ p₀ / ((2 : ℝ) ^ p₀⁻¹) ^ p₀) := by rw [div_rpow hη.le (by positivity)]
        _ = 2 * (η ^ p₀ / 2) := by rw [hden]
        _ = η ^ p₀ := by ring
    have hcancel : ε ^ p₀ + α * (p₀ * (ε ^ p₀ / (α * p₀))) = 2 * ε ^ p₀ := by
      field_simp [hα.ne', hp0.ne']
      ring
    calc
      ∫ ω, ‖z ω - 1‖ ^ p₀ ∂ν ≤ ε ^ p₀ + α * ∫ ω, youngDefect p₀ (z ω) ∂ν := by
        rwa [hsplit] at hpoint
      _ < ε ^ p₀ + α * (p₀ * (ε ^ p₀ / (α * p₀))) := by
        linarith [mul_lt_mul_of_pos_left hint_lt hα]
      _ = 2 * ε ^ p₀ := hcancel
      _ = η ^ p₀ := htwo
  exact eLpNorm_lt_of_integral_norm_rpow_lt hp0 hzsub hη hint_sub

/-- Quotient `u / v` off `{v = 0}`, written so that the value at zero is zero. -/
def phaseQuotient (p₀ : ℝ) (u v : 𝕜) : 𝕜 :=
  u * lpDualFun p₀ v / RCLike.ofReal (‖v‖ ^ p₀)

@[simp]
theorem phaseQuotient_zero (p₀ : ℝ) (u : 𝕜) : phaseQuotient p₀ u 0 = 0 := by
  simp [phaseQuotient, lpDualFun_zero]

/-- Multiplying the quotient by `v` recovers `u` off zero. -/
theorem phaseQuotient_mul {p₀ : ℝ} (hp : 1 < p₀) {u v : 𝕜} (hv : v ≠ 0) :
    phaseQuotient p₀ u v * v = u := by
  have hcoe : RCLike.ofReal (K := 𝕜) (‖v‖ ^ p₀) ≠ 0 := by
    rw [RCLike.ofReal_ne_zero]
    exact (rpow_pos_of_pos (norm_pos_iff.mpr hv) p₀).ne'
  unfold phaseQuotient
  rw [div_mul_eq_mul_div, mul_assoc, mul_comm (lpDualFun p₀ v) v, mul_lpDualFun hp,
    mul_div_cancel_right₀ _ hcoe]

/-- The quotient agrees with division in the scalar field, including at zero. -/
theorem phaseQuotient_eq_div {p₀ : ℝ} (hp : 1 < p₀) (u v : 𝕜) :
    phaseQuotient p₀ u v = u / v := by
  rcases eq_or_ne v 0 with rfl | hv
  · have hp0 : p₀ ≠ 0 := by linarith
    simp [phaseQuotient, lpDualFun_zero, norm_zero, Real.zero_rpow hp0, div_zero]
  · rw [← mul_div_cancel_right₀ (phaseQuotient p₀ u v) hv, phaseQuotient_mul hp hv]

/-- The quotient times the powered norm is the dual pairing, including at zero. -/
theorem phaseQuotient_mul_ofReal (p₀ : ℝ) (u v : 𝕜) :
    phaseQuotient p₀ u v * RCLike.ofReal (‖v‖ ^ p₀) = u * lpDualFun p₀ v := by
  unfold phaseQuotient
  rcases eq_or_ne v 0 with rfl | hv
  · simp [lpDualFun_zero]
  · exact div_mul_cancel₀ _ <| by
      rw [RCLike.ofReal_ne_zero]
      exact (rpow_pos_of_pos (norm_pos_iff.mpr hv) p₀).ne'

/-- Powered norms split into the part supported where `v = 0` and the complementary part. -/
theorem norm_rpow_phase_add {p₀ : ℝ} (hp : 1 < p₀) (u v : 𝕜) :
    ‖u‖ ^ p₀ = ‖u - phaseQuotient p₀ u v * v‖ ^ p₀ + ‖phaseQuotient p₀ u v * v‖ ^ p₀ := by
  have hp0 : p₀ ≠ 0 := by linarith
  rcases eq_or_ne v 0 with rfl | hv
  · simp [phaseQuotient_zero, norm_zero, Real.zero_rpow hp0, sub_zero]
  · rw [phaseQuotient_mul hp hv, sub_self, norm_zero, Real.zero_rpow hp0, zero_add]

/-- Distance to `v` splits into the probability-space defect and the zero set of `v`. -/
theorem norm_sub_rpow_eq_phase {p₀ : ℝ} (hp : 1 < p₀) (u v : 𝕜) :
    ‖u - v‖ ^ p₀ = ‖phaseQuotient p₀ u v - 1‖ ^ p₀ * ‖v‖ ^ p₀ +
      ‖u - phaseQuotient p₀ u v * v‖ ^ p₀ := by
  have hp0 : p₀ ≠ 0 := by linarith
  rcases eq_or_ne v 0 with rfl | hv
  · simp [phaseQuotient_zero, norm_zero, Real.zero_rpow hp0, mul_zero, zero_add, sub_zero]
  · have hdiv : phaseQuotient p₀ u v = u / v := phaseQuotient_eq_div hp u v
    have hnorm : ‖phaseQuotient p₀ u v - 1‖ * ‖v‖ = ‖u - v‖ := by
      rw [hdiv]
      calc
        ‖u / v - 1‖ * ‖v‖ = ‖(u / v - 1) * v‖ := (norm_mul _ _).symm
        _ = ‖u / v * v - v‖ := by rw [sub_mul, one_mul]
        _ = ‖u - v‖ := by rw [div_mul_cancel₀ _ hv]
    rw [phaseQuotient_mul hp hv, sub_self, norm_zero, Real.zero_rpow hp0, add_zero, ← hnorm,
      mul_rpow (norm_nonneg _) (norm_nonneg _)]

/-- The part of `u` aligned with `v` does not increase the powered norm. -/
theorem norm_phase_mul_le {p₀ : ℝ} (hp : 1 < p₀) (u v : 𝕜) :
    ‖phaseQuotient p₀ u v * v‖ ^ p₀ ≤ ‖u‖ ^ p₀ := by
  have hsplit := norm_rpow_phase_add hp u v
  have hnn : 0 ≤ ‖u - phaseQuotient p₀ u v * v‖ ^ p₀ := rpow_nonneg (norm_nonneg _) _
  linarith

/-- The same comparison for extended norms. -/
theorem enorm_rpow_phase_mul_le {p₀ : ℝ} (hp : 1 < p₀) (u v : 𝕜) :
    ‖phaseQuotient p₀ u v * v‖ₑ ^ p₀ ≤ ‖u‖ₑ ^ p₀ := by
  have hp0 : 0 ≤ p₀ := by linarith
  rw [← ofReal_norm, ← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp0,
    ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp0]
  exact ENNReal.ofReal_le_ofReal (norm_phase_mul_le hp u v)

/-- Conjugate power of the dual weight recovers the original powered norm. -/
theorem norm_lpDualFun_rpow {p₀ : ℝ} (hp : 1 < p₀) (z : 𝕜) :
    ‖lpDualFun p₀ z‖ ^ conjExponent p₀ = ‖z‖ ^ p₀ := by
  rw [norm_lpDualFun hp, ← rpow_mul (norm_nonneg _),
    (HolderConjugate.conjExponent hp).sub_one_mul_conj]

/-- The dual weight of an `ℒp` function lies in the conjugate `ℒq` space. -/
theorem memLp_lpDualFun {X : Type*} [MeasurableSpace X] {μ : Measure X} {p₀ : ℝ} (hp : 1 < p₀)
    {v : X → 𝕜} (hv : MemLp v (.ofReal p₀) μ) :
    MemLp (fun x ↦ lpDualFun p₀ (v x)) (.ofReal (conjExponent p₀)) μ := by
  have hq : p₀.HolderConjugate (conjExponent p₀) := HolderConjugate.conjExponent hp
  have hAE : AEStronglyMeasurable (fun x ↦ lpDualFun p₀ (v x)) μ :=
    (continuous_lpDualFun hp).comp_aestronglyMeasurable hv.aestronglyMeasurable
  have hq0 : ENNReal.ofReal (conjExponent p₀) ≠ 0 := ENNReal.ofReal_ne_zero_iff.2 hq.symm.pos
  refine (memLp_norm_rpow_iff (p := ENNReal.ofReal (conjExponent p₀)) hAE hq0
    ENNReal.ofReal_ne_top).1 ?_
  have hEq : (fun x ↦ ‖lpDualFun p₀ (v x)‖ ^ (ENNReal.ofReal (conjExponent p₀)).toReal) =
      fun x ↦ ‖v x‖ ^ p₀ := by
    ext x
    rw [ENNReal.toReal_ofReal hq.symm.nonneg, norm_lpDualFun_rpow hp]
  have hdiv : ENNReal.ofReal (conjExponent p₀) / ENNReal.ofReal (conjExponent p₀) = 1 :=
    ENNReal.div_self hq0 ENNReal.ofReal_ne_top
  have hvn : MemLp (fun x ↦ ‖v x‖ ^ p₀) 1 μ := by
    rw [← ENNReal.toReal_ofReal (zero_lt_one.trans hp).le]
    exact hv.norm_rpow (ENNReal.ofReal_ne_zero_iff.2 (zero_lt_one.trans hp)) ENNReal.ofReal_ne_top
  simpa [hEq, hdiv] using hvn

/-- Real part of a scalar product is at most the product of integral `ℒp` norms. -/
theorem re_integral_mul_le_integral_norm {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {p₀ q₀ : ℝ} (hpq : p₀.HolderConjugate q₀) {u w : X → 𝕜}
    (hu : MemLp u (.ofReal p₀) μ) (hw : MemLp w (.ofReal q₀) μ) :
    RCLike.re (∫ x, u x * w x ∂μ) ≤
      (∫ x, ‖u x‖ ^ p₀ ∂μ) ^ p₀⁻¹ * (∫ x, ‖w x‖ ^ q₀ ∂μ) ^ q₀⁻¹ := by
  calc
    RCLike.re (∫ x, u x * w x ∂μ) ≤ ‖∫ x, u x * w x ∂μ‖ := RCLike.re_le_norm _
    _ ≤ ∫ x, ‖u x * w x‖ ∂μ := norm_integral_le_integral_norm _
    _ = ∫ x, ‖u x‖ * ‖w x‖ ∂μ := by simp [norm_mul]
    _ ≤ (∫ x, ‖u x‖ ^ p₀ ∂μ) ^ (1 / p₀) * (∫ x, ‖w x‖ ^ q₀ ∂μ) ^ (1 / q₀) :=
      integral_mul_norm_le_Lp_mul_Lq hpq hu hw
    _ = (∫ x, ‖u x‖ ^ p₀ ∂μ) ^ p₀⁻¹ * (∫ x, ‖w x‖ ^ q₀ ∂μ) ^ q₀⁻¹ := by simp [one_div]

/-- Integrating against the finite density `‖v‖ ^ p` multiplies the integrand by that density. -/
theorem integral_withDensity_norm_rpow {X : Type*} [MeasurableSpace X] {μ : Measure X} {p₀ : ℝ}
    {v : X → 𝕜} (hv : AEStronglyMeasurable v μ) (g : X → ℝ) :
    ∫ x, g x ∂μ.withDensity (fun x ↦ ENNReal.ofReal (‖v x‖ ^ p₀)) =
      ∫ x, ‖v x‖ ^ p₀ * g x ∂μ := by
  have hρ : AEMeasurable (fun x ↦ ENNReal.ofReal (‖v x‖ ^ p₀)) μ :=
    (hv.norm.aemeasurable.pow_const p₀).ennreal_ofReal
  rw [integral_withDensity_eq_integral_toReal_smul₀ hρ
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
  change (ENNReal.ofReal (‖v x‖ ^ p₀)).toReal • g x = ‖v x‖ ^ p₀ * g x
  rw [ENNReal.toReal_ofReal (rpow_nonneg (norm_nonneg _) p₀), smul_eq_mul]

/-- **Hanche-Olsen, Lemma 2.** If `‖u‖_p ≤ 1`, `‖v‖_p = 1`, and the real pairing against the dual
weight of `v` is close to one, then `u` is close to `v` in `ℒp`. -/
theorem exists_eLpNorm_sub_dual_lt {p₀ : ℝ} (hp : 1 < p₀) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ {X : Type*} [MeasurableSpace X] {μ : Measure X} {u v : X → 𝕜},
      MemLp u (.ofReal p₀) μ → MemLp v (.ofReal p₀) μ →
      eLpNorm u (.ofReal p₀) μ ≤ 1 → eLpNorm v (.ofReal p₀) μ = 1 →
      1 - δ < RCLike.re (∫ x, u x * lpDualFun p₀ (v x) ∂μ) →
      eLpNorm (fun x ↦ u x - v x) (.ofReal p₀) μ < .ofReal η := by
  have hp0 : 0 < p₀ := zero_lt_one.trans hp
  let θ : ℝ := (η ^ p₀ / 2) ^ p₀⁻¹
  have hθ : 0 < θ := by positivity
  obtain ⟨δ₁, hδ₁, hδ₁'⟩ := exists_eLpNorm_sub_one_lt (𝕜 := 𝕜) hp hθ
  refine ⟨min (min δ₁ (1 / 2)) (η ^ p₀ / (2 * p₀)), by positivity, ?_⟩
  intro X _ μ u v hu hv hunorm hvnorm hre
  have hq : p₀.HolderConjugate (conjExponent p₀) := HolderConjugate.conjExponent hp
  set δ : ℝ := min (min δ₁ (1 / 2)) (η ^ p₀ / (2 * p₀))
  have hδle₁ : δ ≤ δ₁ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hδhalf : δ ≤ 1 / 2 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hδpow : δ ≤ η ^ p₀ / (2 * p₀) := min_le_right _ _
  have hw : MemLp (fun x ↦ lpDualFun p₀ (v x)) (.ofReal (conjExponent p₀)) μ :=
    memLp_lpDualFun hp hv
  have hpq : ENNReal.HolderConjugate (ENNReal.ofReal p₀) (ENNReal.ofReal (conjExponent p₀)) :=
    Real.HolderConjugate.ennrealOfReal hq
  have huw : Integrable (fun x ↦ u x * lpDualFun p₀ (v x)) μ :=
    memLp_one_iff_integrable.mp <| hu.mul (hpqr := hpq) hw
  let z : X → 𝕜 := fun x ↦ phaseQuotient p₀ (u x) (v x)
  let ρ : X → ℝ≥0∞ := fun x ↦ ENNReal.ofReal (‖v x‖ ^ p₀)
  have hρ : AEMeasurable ρ μ :=
    (hv.aestronglyMeasurable.norm.aemeasurable.pow_const p₀).ennreal_ofReal
  let ν : Measure X := μ.withDensity ρ
  have hlin : ∫⁻ x, ‖v x‖ₑ ^ p₀ ∂μ = 1 := by
    have hf := eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_ne_zero_iff.2 hp0)
      ENNReal.ofReal_ne_top hv.aestronglyMeasurable
    have hroot : (∫⁻ x, ‖v x‖ₑ ^ p₀ ∂μ) ^ p₀⁻¹ = 1 := by
      simpa [hf, ENNReal.toReal_ofReal hp0.le, one_div] using hvnorm
    have hpow := congrArg (fun t : ℝ≥0∞ ↦ t ^ p₀) hroot
    simpa [← ENNReal.rpow_mul, inv_mul_cancel₀ hp0.ne', ENNReal.rpow_one, ENNReal.one_rpow] using
      hpow
  have hρ_eq : ∫⁻ x, ρ x ∂μ = 1 := by
    rw [← hlin]
    refine lintegral_congr fun x ↦ ?_
    unfold ρ
    rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp0.le, ofReal_norm]
  haveI : IsProbabilityMeasure ν := ⟨by
    rw [withDensity_apply ρ MeasurableSet.univ, setLIntegral_univ]
    exact hρ_eq⟩
  have hintv : ∫ x, ‖v x‖ ^ p₀ ∂μ = 1 :=
    integral_norm_rpow_of_eLpNorm_eq_one hp0 hv hvnorm
  have hintu : ∫ x, ‖u x‖ ^ p₀ ∂μ ≤ 1 := by
    simpa [one_rpow] using
      integral_norm_rpow_le_of_eLpNorm_le hp0 hu zero_le_one (by simpa using hunorm)
  have hz_div : z = fun x ↦ u x / v x := by
    ext x
    exact phaseQuotient_eq_div hp (u x) (v x)
  have hz_aeμ : AEStronglyMeasurable z μ := by
    rw [hz_div]
    exact hu.aestronglyMeasurable.div₀ hv.aestronglyMeasurable
  have hz_ae : AEStronglyMeasurable z ν :=
    hz_aeμ.mono_ac (withDensity_absolutelyContinuous μ ρ)
  let f : X → 𝕜 := fun x ↦ z x * v x
  have hf_ae : AEStronglyMeasurable f μ := hz_aeμ.mul hv.aestronglyMeasurable
  have hlin_f : ∫⁻ x, ‖f x‖ₑ ^ p₀ ∂μ ≤ ∫⁻ x, ‖u x‖ₑ ^ p₀ ∂μ :=
    lintegral_mono fun x ↦ by simpa [f, z] using enorm_rpow_phase_mul_le hp (u x) (v x)
  have hfin_u : ∫⁻ x, ‖u x‖ₑ ^ p₀ ∂μ < ∞ := by
    simpa [ENNReal.toReal_ofReal hp0.le] using lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      (ENNReal.ofReal_ne_zero_iff.2 hp0) ENNReal.ofReal_ne_top hu
  have hf_mem : MemLp f (.ofReal p₀) μ := by
    rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
      (ENNReal.ofReal_ne_zero_iff.2 hp0) ENNReal.ofReal_ne_top hf_ae]
    exact lt_of_le_of_lt (by simpa [ENNReal.toReal_ofReal hp0.le] using hlin_f) hfin_u
  have hzn : AEMeasurable (fun x ↦ ‖z x‖ₑ ^ p₀) μ :=
    (ENNReal.continuous_rpow_const (y := p₀)).measurable.comp_aemeasurable hz_aeμ.enorm
  have hlin_z : ∫⁻ x, ‖z x‖ₑ ^ p₀ ∂ν ≤ ∫⁻ x, ‖u x‖ₑ ^ p₀ ∂μ := by
    rw [lintegral_withDensity_eq_lintegral_mul₀ hρ hzn]
    refine lintegral_mono fun x ↦ ?_
    have hρx : ρ x = ‖v x‖ₑ ^ p₀ := by
      unfold ρ
      rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp0.le, ofReal_norm]
    rw [Pi.mul_apply, hρx, ← ENNReal.mul_rpow_of_nonneg _ _ hp0.le,
      mul_comm (‖v x‖ₑ) (‖z x‖ₑ), ← enorm_mul]
    simpa [f, z] using enorm_rpow_phase_mul_le hp (u x) (v x)
  have hz_mem : MemLp z (.ofReal p₀) ν := by
    rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
      (ENNReal.ofReal_ne_zero_iff.2 hp0) ENNReal.ofReal_ne_top hz_ae]
    exact lt_of_le_of_lt (by simpa [ENNReal.toReal_ofReal hp0.le] using hlin_z) hfin_u
  have hint_z : ∫ x, ‖z x‖ ^ p₀ ∂ν = ∫ x, ‖f x‖ ^ p₀ ∂μ := by
    rw [integral_withDensity_norm_rpow hv.aestronglyMeasurable fun x ↦ ‖z x‖ ^ p₀]
    refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
    change ‖v x‖ ^ p₀ * ‖z x‖ ^ p₀ = ‖f x‖ ^ p₀
    rw [mul_comm, ← mul_rpow (norm_nonneg _) (norm_nonneg _), ← norm_mul]
  have hint_f_int : Integrable (fun x ↦ ‖f x‖ ^ p₀) μ :=
    integrable_norm_rpow_of_memLp hp0 hf_mem
  have hint_u_int : Integrable (fun x ↦ ‖u x‖ ^ p₀) μ :=
    integrable_norm_rpow_of_memLp hp0 hu
  have hint_f_le : ∫ x, ‖f x‖ ^ p₀ ∂μ ≤ ∫ x, ‖u x‖ ^ p₀ ∂μ :=
    integral_mono hint_f_int hint_u_int fun x ↦ by
      simpa [f, z] using norm_phase_mul_le hp (u x) (v x)
  have hint_z_le : ∫ x, ‖z x‖ ^ p₀ ∂ν ≤ 1 := hint_z.trans_le (hint_f_le.trans hintu)
  have hz_norm : eLpNorm z (.ofReal p₀) ν ≤ 1 := by
    have hroot : (∫ x, ‖z x‖ ^ p₀ ∂ν) ^ p₀⁻¹ ≤ 1 := by
      rw [← one_rpow p₀⁻¹]
      exact rpow_le_rpow (integral_nonneg fun _ ↦ rpow_nonneg (norm_nonneg _) _) hint_z_le
        (inv_nonneg.2 hp0.le)
    rw [hz_mem.eLpNorm_eq_integral_rpow_norm (ENNReal.ofReal_ne_zero_iff.2 hp0)
      ENNReal.ofReal_ne_top, ← ENNReal.ofReal_one]
    simpa [ENNReal.toReal_ofReal hp0.le, one_div] using ENNReal.ofReal_le_ofReal hroot
  have hzw : (fun x ↦ f x * lpDualFun p₀ (v x)) = fun x ↦ u x * lpDualFun p₀ (v x) := by
    ext x
    rcases eq_or_ne (v x) 0 with hvx | hvx
    · simp [f, z, hvx, lpDualFun_zero]
    · simp [f, z, phaseQuotient_mul hp hvx]
  have hre_z : 1 - δ₁ < ∫ x, RCLike.re (z x) ∂ν := by
    have hz_int : Integrable z ν :=
      memLp_one_iff_integrable.mp <| hz_mem.mono_exponent ((ENNReal.one_le_ofReal).2 hp.le)
    have hint_eq : ∫ x, z x ∂ν = ∫ x, u x * lpDualFun p₀ (v x) ∂μ := by
      change ∫ x, z x ∂μ.withDensity ρ = _
      rw [integral_withDensity_eq_integral_toReal_smul₀ hρ
        (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
      refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
      change (ρ x).toReal • z x = u x * lpDualFun p₀ (v x)
      rw [show ρ x = ENNReal.ofReal (‖v x‖ ^ p₀) from rfl,
        ENNReal.toReal_ofReal (rpow_nonneg (norm_nonneg _) _),
        RCLike.real_smul_eq_coe_mul, mul_comm]
      exact phaseQuotient_mul_ofReal p₀ (u x) (v x)
    rw [integral_re hz_int, hint_eq]
    exact lt_of_le_of_lt (sub_le_sub_left hδle₁ 1) hre
  have hz1 : MemLp (fun x ↦ z x - 1) (.ofReal p₀) ν := hz_mem.sub (memLp_const 1)
  have hint_phase : ∫ x, ‖z x - 1‖ ^ p₀ ∂ν < θ ^ p₀ :=
    integral_norm_rpow_lt_of_eLpNorm_lt hp0 hz1 hθ (hδ₁' hz_mem hz_norm hre_z)
  have hθpow : θ ^ p₀ = η ^ p₀ / 2 := by
    unfold θ
    rw [← rpow_mul (by positivity), inv_mul_cancel₀ hp0.ne', rpow_one]
  set q₀ : ℝ := conjExponent p₀
  have hint_w : ∫ x, ‖lpDualFun p₀ (v x)‖ ^ q₀ ∂μ = 1 := by
    have hfun : (fun x ↦ ‖lpDualFun p₀ (v x)‖ ^ q₀) = fun x ↦ ‖v x‖ ^ p₀ := by
      ext x
      exact norm_lpDualFun_rpow hp (v x)
    rw [hfun, hintv]
  have hre_f : RCLike.re (∫ x, u x * lpDualFun p₀ (v x) ∂μ) ≤
      (∫ x, ‖f x‖ ^ p₀ ∂μ) ^ p₀⁻¹ := by
    calc
      RCLike.re (∫ x, u x * lpDualFun p₀ (v x) ∂μ)
        = RCLike.re (∫ x, f x * lpDualFun p₀ (v x) ∂μ) := by rw [hzw]
      _ ≤ (∫ x, ‖f x‖ ^ p₀ ∂μ) ^ p₀⁻¹ * (∫ x, ‖lpDualFun p₀ (v x)‖ ^ q₀ ∂μ) ^ q₀⁻¹ :=
        re_integral_mul_le_integral_norm hq hf_mem hw
      _ = (∫ x, ‖f x‖ ^ p₀ ∂μ) ^ p₀⁻¹ := by simp [hint_w, one_rpow, mul_one]
  have hroot_f : 1 - δ < (∫ x, ‖f x‖ ^ p₀ ∂μ) ^ p₀⁻¹ := lt_of_lt_of_le hre hre_f
  have hint_f_gt : (1 - δ) ^ p₀ < ∫ x, ‖f x‖ ^ p₀ ∂μ := by
    have hint0 : 0 ≤ ∫ x, ‖f x‖ ^ p₀ ∂μ :=
      integral_nonneg fun _ ↦ rpow_nonneg (norm_nonneg _) _
    have h1δ : 0 ≤ 1 - δ := by linarith [hδhalf]
    have hlt : (1 - δ) ^ p₀ < ((∫ x, ‖f x‖ ^ p₀ ∂μ) ^ p₀⁻¹) ^ p₀ :=
      (rpow_lt_rpow_iff h1δ (rpow_nonneg hint0 _) hp0).2 hroot_f
    rw [← rpow_mul hint0, inv_mul_cancel₀ hp0.ne', rpow_one] at hlt
    exact hlt
  have hbern : 1 - (1 - δ) ^ p₀ ≤ p₀ * δ := by
    have hs : (-1 : ℝ) ≤ -δ := by linarith [hδhalf]
    have hineq := one_add_mul_self_le_rpow_one_add hs hp.le
    have hL : 1 + p₀ * -δ = 1 - p₀ * δ := by ring
    have hR : 1 + -δ = 1 - δ := by ring
    rw [hL, hR] at hineq
    linarith
  have hgap : 1 - ∫ x, ‖f x‖ ^ p₀ ∂μ < η ^ p₀ / 2 := by
    have hmul : p₀ * δ ≤ p₀ * (η ^ p₀ / (2 * p₀)) :=
      mul_le_mul_of_nonneg_left hδpow hp0.le
    have hcancel : p₀ * (η ^ p₀ / (2 * p₀)) = η ^ p₀ / 2 := by field_simp
    linarith [hbern, hint_f_gt, hmul, hcancel]
  have hfun_diff : (fun x ↦ ‖u x - f x‖ ^ p₀) =
      (fun x ↦ ‖u x‖ ^ p₀) - fun x ↦ ‖f x‖ ^ p₀ := by
    ext x
    rw [Pi.sub_apply]
    have hsplit : ‖u x‖ ^ p₀ = ‖u x - f x‖ ^ p₀ + ‖f x‖ ^ p₀ := by
      simpa [f, z] using norm_rpow_phase_add hp (u x) (v x)
    linarith
  have hint_diff_int : Integrable (fun x ↦ ‖u x - f x‖ ^ p₀) μ := by
    rw [hfun_diff]
    exact hint_u_int.sub hint_f_int
  have hint_diff_eq : ∫ x, ‖u x - f x‖ ^ p₀ ∂μ =
      ∫ x, ‖u x‖ ^ p₀ ∂μ - ∫ x, ‖f x‖ ^ p₀ ∂μ := by
    rw [hfun_diff, integral_sub' hint_u_int hint_f_int]
  have hint_diff_lt : ∫ x, ‖u x - f x‖ ^ p₀ ∂μ < η ^ p₀ / 2 := by
    rw [hint_diff_eq]
    exact lt_of_le_of_lt (by linarith [hintu]) hgap
  have huv_mem : MemLp (fun x ↦ u x - v x) (.ofReal p₀) μ := hu.sub hv
  have hint_uv_int : Integrable (fun x ↦ ‖u x - v x‖ ^ p₀) μ :=
    integrable_norm_rpow_of_memLp hp0 huv_mem
  have hfun_uv : (fun x ↦ ‖u x - v x‖ ^ p₀) =
      (fun x ↦ ‖z x - 1‖ ^ p₀ * ‖v x‖ ^ p₀) + fun x ↦ ‖u x - f x‖ ^ p₀ := by
    ext x
    simpa [z, f] using norm_sub_rpow_eq_phase hp (u x) (v x)
  have hint_phase_μ_int : Integrable (fun x ↦ ‖z x - 1‖ ^ p₀ * ‖v x‖ ^ p₀) μ := by
    have hfun : (fun x ↦ ‖z x - 1‖ ^ p₀ * ‖v x‖ ^ p₀) =
        (fun x ↦ ‖u x - v x‖ ^ p₀) - fun x ↦ ‖u x - f x‖ ^ p₀ := by
      ext x
      rw [Pi.sub_apply]
      have hpt := congrFun hfun_uv x
      rw [Pi.add_apply] at hpt
      linarith
    rw [hfun]
    exact hint_uv_int.sub hint_diff_int
  have hsplit : ∫ x, ‖u x - v x‖ ^ p₀ ∂μ =
      ∫ x, ‖z x - 1‖ ^ p₀ * ‖v x‖ ^ p₀ ∂μ + ∫ x, ‖u x - f x‖ ^ p₀ ∂μ := by
    rw [hfun_uv, integral_add' hint_phase_μ_int hint_diff_int]
  have htransfer : ∫ x, ‖z x - 1‖ ^ p₀ * ‖v x‖ ^ p₀ ∂μ = ∫ x, ‖z x - 1‖ ^ p₀ ∂ν := by
    have hcomm : (fun x ↦ ‖z x - 1‖ ^ p₀ * ‖v x‖ ^ p₀) =
        fun x ↦ ‖v x‖ ^ p₀ * ‖z x - 1‖ ^ p₀ := by
      ext x
      rw [mul_comm]
    rw [hcomm]
    exact (integral_withDensity_norm_rpow hv.aestronglyMeasurable
      (fun x ↦ ‖z x - 1‖ ^ p₀)).symm
  have hint_sum : ∫ x, ‖u x - v x‖ ^ p₀ ∂μ < η ^ p₀ := by
    rw [hsplit, htransfer]
    have hphase_lt : ∫ x, ‖z x - 1‖ ^ p₀ ∂ν < η ^ p₀ / 2 := lt_of_lt_of_eq hint_phase hθpow
    linarith [hphase_lt, hint_diff_lt]
  exact eLpNorm_lt_of_integral_norm_rpow_lt hp0 huv_mem hη hint_sum

/-- Hölder and the dual-weight identity bound a unit-sphere pairing by one. -/
theorem re_integral_lpDualFun_le_one {X : Type*} [MeasurableSpace X] {μ : Measure X} {p₀ : ℝ}
    (hp : 1 < p₀) {u v : X → 𝕜} (hu : MemLp u (.ofReal p₀) μ) (hv : MemLp v (.ofReal p₀) μ)
    (hu1 : ∫ x, ‖u x‖ ^ p₀ ∂μ = 1) (hv1 : ∫ x, ‖v x‖ ^ p₀ ∂μ = 1) :
    RCLike.re (∫ x, u x * lpDualFun p₀ (v x) ∂μ) ≤ 1 := by
  have hq : p₀.HolderConjugate (conjExponent p₀) := HolderConjugate.conjExponent hp
  have hw : MemLp (fun x ↦ lpDualFun p₀ (v x)) (.ofReal (conjExponent p₀)) μ :=
    memLp_lpDualFun hp hv
  have hintw : ∫ x, ‖lpDualFun p₀ (v x)‖ ^ conjExponent p₀ ∂μ = 1 := by
    have hfun : (fun x ↦ ‖lpDualFun p₀ (v x)‖ ^ conjExponent p₀) = fun x ↦ ‖v x‖ ^ p₀ := by
      ext x
      exact norm_lpDualFun_rpow hp (v x)
    rw [hfun, hv1]
  calc
    RCLike.re (∫ x, u x * lpDualFun p₀ (v x) ∂μ)
      ≤ (∫ x, ‖u x‖ ^ p₀ ∂μ) ^ p₀⁻¹ *
          (∫ x, ‖lpDualFun p₀ (v x)‖ ^ conjExponent p₀ ∂μ) ^ (conjExponent p₀)⁻¹ :=
        re_integral_mul_le_integral_norm hq hu hw
    _ = 1 := by simp [hu1, hintw, one_rpow]

/-- **15.33.** Scalar `Lp` is uniformly convex for `1 < p < ∞`, including the Hilbert exponent. -/
theorem uniformConvexSpace_lp {X : Type*} [MeasurableSpace X] (μ : Measure X) {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (hp : 1 < p) (hp_top : p < ∞) : UniformConvexSpace (Lp 𝕜 p μ) := by
  refine ⟨fun ε hε ↦ ?_⟩
  set p₀ : ℝ := p.toReal
  have hp₀ : 1 < p₀ := by
    rw [← ENNReal.toReal_one]
    exact (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hp_top.ne).2 hp
  have hp₀0 : 0 < p₀ := zero_lt_one.trans hp₀
  have hp_eq : p = .ofReal p₀ := (ENNReal.ofReal_toReal hp_top.ne).symm
  set η : ℝ := ε / 2
  have hη : 0 < η := by positivity
  obtain ⟨δ₀, hδ₀, hclose⟩ := exists_eLpNorm_sub_dual_lt (𝕜 := 𝕜) hp₀ hη
  refine ⟨min δ₀ 1, lt_min hδ₀ one_pos, fun x hx y hy hdist ↦ ?_⟩
  set δ : ℝ := min δ₀ 1
  by_contra hbig
  rw [not_le] at hbig
  set s : ℝ := ‖x + y‖
  have hs1 : 1 < s := by
    have hδ1 : δ ≤ 1 := min_le_right _ _
    linarith
  have hs0 : 0 < s := zero_lt_one.trans hs1
  let c : 𝕜 := (s⁻¹ : ℝ)
  let vf : Lp 𝕜 p μ := c • (x + y)
  have hvf_norm : ‖vf‖ = 1 := by
    rw [norm_smul, RCLike.norm_ofReal, abs_of_pos (inv_pos.2 hs0), inv_mul_cancel₀ hs0.ne']
  have hx_e : eLpNorm (⇑x) (.ofReal p₀) μ = 1 := by
    rw [← hp_eq, ← ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top x), ← Lp.norm_def, hx,
      ENNReal.ofReal_one]
  have hy_e : eLpNorm (⇑y) (.ofReal p₀) μ = 1 := by
    rw [← hp_eq, ← ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top y), ← Lp.norm_def, hy,
      ENNReal.ofReal_one]
  have hvf_e : eLpNorm (⇑vf) (.ofReal p₀) μ = 1 := by
    rw [← hp_eq, ← ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top vf), ← Lp.norm_def, hvf_norm,
      ENNReal.ofReal_one]
  have hx_mem : MemLp (⇑x) (.ofReal p₀) μ := by simpa [hp_eq] using Lp.memLp x
  have hy_mem : MemLp (⇑y) (.ofReal p₀) μ := by simpa [hp_eq] using Lp.memLp y
  have hvf_mem : MemLp (⇑vf) (.ofReal p₀) μ := by simpa [hp_eq] using Lp.memLp vf
  have hx_int : ∫ t, ‖x t‖ ^ p₀ ∂μ = 1 :=
    integral_norm_rpow_of_eLpNorm_eq_one hp₀0 hx_mem hx_e
  have hy_int : ∫ t, ‖y t‖ ^ p₀ ∂μ = 1 :=
    integral_norm_rpow_of_eLpNorm_eq_one hp₀0 hy_mem hy_e
  have hvf_int : ∫ t, ‖vf t‖ ^ p₀ ∂μ = 1 :=
    integral_norm_rpow_of_eLpNorm_eq_one hp₀0 hvf_mem hvf_e
  have hsmul : ⇑vf =ᵐ[μ] fun t ↦ c • (x t + y t) := by
    filter_upwards [Lp.coeFn_smul c (x + y), Lp.coeFn_add x y] with t ht hadd
    rw [ht, Pi.smul_apply, hadd, Pi.add_apply]
  have hscale : (fun t ↦ (s : 𝕜) * vf t) =ᵐ[μ] fun t ↦ x t + y t := by
    filter_upwards [hsmul] with t ht
    rw [ht, smul_eq_mul, ← mul_assoc, ← RCLike.ofReal_mul, mul_inv_cancel₀ hs0.ne',
      RCLike.ofReal_one, one_mul]
  have hpair_vf : ∫ t, vf t * lpDualFun p₀ (vf t) ∂μ = 1 := by
    have hpt : (fun t ↦ vf t * lpDualFun p₀ (vf t)) =
        fun t ↦ RCLike.ofReal (‖vf t‖ ^ p₀) := by
      ext t
      exact mul_lpDualFun hp₀ (vf t)
    rw [hpt, integral_ofReal, hvf_int]
    simp
  have hw_mem : MemLp (fun t ↦ lpDualFun p₀ (vf t)) (.ofReal (conjExponent p₀)) μ :=
    memLp_lpDualFun hp₀ hvf_mem
  have hpq : ENNReal.HolderConjugate (ENNReal.ofReal p₀) (ENNReal.ofReal (conjExponent p₀)) :=
    Real.HolderConjugate.ennrealOfReal (HolderConjugate.conjExponent hp₀)
  have hintx : Integrable (fun t ↦ x t * lpDualFun p₀ (vf t)) μ :=
    memLp_one_iff_integrable.mp <| hx_mem.mul (hpqr := hpq) hw_mem
  have hinty : Integrable (fun t ↦ y t * lpDualFun p₀ (vf t)) μ :=
    memLp_one_iff_integrable.mp <| hy_mem.mul (hpqr := hpq) hw_mem
  have hpair_sum : ∫ t, (x t + y t) * lpDualFun p₀ (vf t) ∂μ = (s : 𝕜) := by
    have hfun : (fun t ↦ (x t + y t) * lpDualFun p₀ (vf t)) =ᵐ[μ]
        fun t ↦ (s : 𝕜) * (vf t * lpDualFun p₀ (vf t)) := by
      filter_upwards [hscale] with t ht
      rw [← ht, mul_assoc]
    rw [integral_congr_ae hfun, integral_const_mul, hpair_vf, mul_one]
  have hsplit_int : ∫ t, (x t + y t) * lpDualFun p₀ (vf t) ∂μ =
      ∫ t, x t * lpDualFun p₀ (vf t) ∂μ + ∫ t, y t * lpDualFun p₀ (vf t) ∂μ := by
    rw [← integral_add hintx hinty]
    refine integral_congr_ae (ae_of_all _ fun t ↦ ?_)
    change (x t + y t) * lpDualFun p₀ (vf t) =
      x t * lpDualFun p₀ (vf t) + y t * lpDualFun p₀ (vf t)
    ring
  have hre_sum : RCLike.re (∫ t, x t * lpDualFun p₀ (vf t) ∂μ) +
      RCLike.re (∫ t, y t * lpDualFun p₀ (vf t) ∂μ) = s := by
    rw [← map_add (RCLike.re : 𝕜 →+ ℝ), ← hsplit_int, hpair_sum, RCLike.ofReal_re]
  have hrex_le : RCLike.re (∫ t, x t * lpDualFun p₀ (vf t) ∂μ) ≤ 1 :=
    re_integral_lpDualFun_le_one hp₀ hx_mem hvf_mem hx_int hvf_int
  have hrey_le : RCLike.re (∫ t, y t * lpDualFun p₀ (vf t) ∂μ) ≤ 1 :=
    re_integral_lpDualFun_le_one hp₀ hy_mem hvf_mem hy_int hvf_int
  have hrex_gt : 1 - δ₀ < RCLike.re (∫ t, x t * lpDualFun p₀ (vf t) ∂μ) := by
    have hδle : δ ≤ δ₀ := min_le_left _ _
    linarith [hre_sum, hrey_le, hbig]
  have hrey_gt : 1 - δ₀ < RCLike.re (∫ t, y t * lpDualFun p₀ (vf t) ∂μ) := by
    have hδle : δ ≤ δ₀ := min_le_left _ _
    linarith [hre_sum, hrex_le, hbig]
  have hx_near : eLpNorm (fun t ↦ x t - vf t) (.ofReal p₀) μ < .ofReal η :=
    hclose hx_mem hvf_mem (le_of_eq hx_e) hvf_e hrex_gt
  have hy_near : eLpNorm (fun t ↦ y t - vf t) (.ofReal p₀) μ < .ofReal η :=
    hclose hy_mem hvf_mem (le_of_eq hy_e) hvf_e hrey_gt
  have htri : eLpNorm (fun t ↦ x t - y t) (.ofReal p₀) μ < .ofReal ε := by
    have hdecomp : (fun t ↦ x t - y t) =
        (fun t ↦ x t - vf t) + fun t ↦ vf t - y t := by
      ext t
      exact (sub_add_sub_cancel (x t) (vf t) (y t)).symm
    have hneg : eLpNorm (fun t ↦ vf t - y t) (.ofReal p₀) μ =
        eLpNorm (fun t ↦ y t - vf t) (.ofReal p₀) μ := by
      rw [show (fun t ↦ vf t - y t) = -(fun t ↦ y t - vf t) by
        ext t
        simp [Pi.neg_apply, neg_sub], eLpNorm_neg]
    calc
      eLpNorm (fun t ↦ x t - y t) (.ofReal p₀) μ
        = eLpNorm ((fun t ↦ x t - vf t) + fun t ↦ vf t - y t) (.ofReal p₀) μ := by rw [hdecomp]
      _ ≤ eLpNorm (fun t ↦ x t - vf t) (.ofReal p₀) μ +
            eLpNorm (fun t ↦ vf t - y t) (.ofReal p₀) μ :=
          eLpNorm_add_le ((ENNReal.one_le_ofReal).2 hp₀.le)
      _ < .ofReal η + .ofReal η := by
          rw [hneg]
          exact ENNReal.add_lt_add hx_near hy_near
      _ = .ofReal ε := by
          rw [← ENNReal.ofReal_add hη.le hη.le]
          congr 1
          unfold η
          ring
  have hdist_lt : ‖x - y‖ < ε := by
    rw [Lp.norm_def]
    let φ : X → 𝕜 := fun t ↦ x t - y t
    have hsub : ⇑(x - y) =ᵐ[μ] φ := by
      filter_upwards [Lp.coeFn_sub x y] with t ht
      simpa [φ, Pi.sub_apply] using ht
    rw [eLpNorm_congr_ae hsub, congrArg (fun q ↦ eLpNorm φ q μ) hp_eq]
    exact ENNReal.toReal_lt_of_lt_ofReal htri
  exact not_le_of_gt hdist_lt hdist

end CKMA.WeakCompactness
