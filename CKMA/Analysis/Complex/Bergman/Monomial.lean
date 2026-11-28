/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.MeasureTheory.Function.L2Space
public import CKMA.Analysis.Complex.Bergman.Polar

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
# Weighted Bergman measure, kernel and monomials

The normalized disk measure `dA_α` has density `(α + 1)(1 - |z|²)^α / π` for `α > -1`, and the
weighted Bergman kernel is the principal power `(1 - z w̄)^(-α-2)`. The monomials `zⁿ` are
orthogonal in `L²(dA_α)` with square norms `cₙ = Γ(α + 2) n! / Γ(n + α + 2)`, computed by the Beta
integral in polar coordinates (`CKMA.Analysis.Complex.Bergman.Polar`). The kernel is the binomial
series `∑ zⁿ w̄ⁿ / cₙ`, and the moment `∫ conj(zⁿ) f dA_α` of a square-integrable holomorphic `f`
is `aₙ cₙ`, with `aₙ` its Taylor coefficient.

## Main definitions

* `CKMA.bergmanMeasure`: normalized radially weighted area measure on the unit disk.
* `CKMA.bergmanKernel`: weighted Bergman reproducing kernel.

## Main results

* `CKMA.integral_norm_monomial_sq`: weighted `L²` norm of monomials.
* `CKMA.memLp_monomial`, `CKMA.memLp_conj_monomial`: monomials lie in weighted `L²`.
* `CKMA.bergmanKernel_eq_tsum`: the kernel as a monomial series.
* `CKMA.integral_conj_pow_mul_holomorphic`: monomial moments of holomorphic functions.
* `CKMA.summable_div_sqrt_monomialNormSq`, `CKMA.bergmanMeasure_compl_ball`: auxiliary bounds for
  the kernel series and the support of the measure.
-/

public section

noncomputable section

namespace CKMA

open Complex Filter MeasureTheory Real Set intervalIntegral
open scoped ENNReal ComplexConjugate InnerProductSpace

/-- The normalized weighted disk measure, with total mass one when `-1 < α`. -/
@[expose]
def bergmanMeasure (α : ℝ) : Measure ℂ :=
  volume.withDensity (fun z ↦ if ‖z‖ < 1 then
    ENNReal.ofReal (((α + 1) / Real.pi) * (1 - ‖z‖ ^ 2) ^ α) else 0)

/-- The weighted disk Bergman kernel, with the principal complex power. -/
@[expose]
def bergmanKernel (α : ℝ) (z w : ℂ) : ℂ := (1 - z * conj w) ^ (-(α : ℂ) - 2)

/-- The Bergman measure has density `((α + 1) / π) (1 - |z|²)^α` on the disk and `0` off it. -/
theorem bergmanMeasure_def (α : ℝ) : bergmanMeasure α =
    volume.withDensity (fun z ↦ if ‖z‖ < 1 then
      ENNReal.ofReal (((α + 1) / Real.pi) * (1 - ‖z‖ ^ 2) ^ α) else 0) :=
  rfl

/-- The kernel is the principal power `(1 - z w̄)^(-α-2)`. -/
theorem bergmanKernel_def (α : ℝ) (z w : ℂ) :
    bergmanKernel α z w = (1 - z * conj w) ^ (-(α : ℂ) - 2) :=
  rfl

/-- The weighted square norm of `z ↦ zⁿ` is `bergmanMonomialNormSq α n = Γ(α + 2) n! /
Γ(n + α + 2)`, for `α > -1`; for `α = 0` this is `1 / (n + 1)`. -/
theorem integral_norm_monomial_sq {α : ℝ} (hα : -1 < α) (n : ℕ) :
    (∫ z : ℂ, ‖z ^ n‖ ^ 2 ∂bergmanMeasure α) =
      Real.Gamma (α + 2) * n.factorial / Real.Gamma (n + α + 2) := by
  set c : ℝ := (α + 1) / π
  have hc : 0 < c := div_pos (by linarith) pi_pos
  let dens : ℂ → ℝ≥0∞ := fun z =>
    if ‖z‖ < 1 then ENNReal.ofReal (c * (1 - ‖z‖ ^ 2) ^ α) else 0
  have hμ : bergmanMeasure α = volume.withDensity dens := by
    simp [bergmanMeasure, dens, c]
  have hmeas : Measurable dens := by
    unfold dens
    refine Measurable.ite (measurableSet_lt continuous_norm.measurable measurable_const)
      ?_ measurable_const
    refine ENNReal.measurable_ofReal.comp ?_
    refine (measurable_const.mul ?_)
    refine Measurable.pow_const ?_ α
    exact measurable_const.sub (continuous_norm.measurable.pow_const 2)
  have hfin : ∀ᵐ z ∂volume, dens z < ∞ := ae_of_all _ fun z => by
    by_cases hz : ‖z‖ < 1
    · simp [dens, hz, ENNReal.ofReal_lt_top]
    · simp [dens, hz]
  have hto : ∀ z, (dens z).toReal =
      if ‖z‖ < 1 then c * (1 - ‖z‖ ^ 2) ^ α else 0 := by
    intro z
    by_cases hz : ‖z‖ < 1
    · have hsq : ‖z‖ ^ 2 < 1 := by
        rw [← one_pow 2]
        exact pow_lt_pow_left₀ hz (norm_nonneg z) two_ne_zero
      have hnonneg : 0 ≤ c * (1 - ‖z‖ ^ 2) ^ α :=
        mul_nonneg hc.le (rpow_nonneg (sub_nonneg.mpr hsq.le) α)
      simp [dens, hz, ENNReal.toReal_ofReal hnonneg]
    · simp [dens, hz]
  let φ : ℝ → ℝ := fun r =>
    if r < 1 then c * (1 - r ^ 2) ^ α * r ^ (2 * n + 1) else 0
  rw [hμ, integral_withDensity_eq_integral_toReal_smul hmeas hfin]
  simp_rw [hto, smul_eq_mul, norm_pow, ← pow_mul, mul_comm n 2]
  rw [← Complex.integral_comp_polarCoord_symm (f := fun z : ℂ =>
    (if ‖z‖ < 1 then c * (1 - ‖z‖ ^ 2) ^ α else 0) * ‖z‖ ^ (2 * n))]
  have hpolar : ∀ p ∈ Complex.polarCoord.target,
      p.1 * (((if ‖Complex.polarCoord.symm p‖ < 1 then
        c * (1 - ‖Complex.polarCoord.symm p‖ ^ 2) ^ α else 0) *
        ‖Complex.polarCoord.symm p‖ ^ (2 * n))) =
      φ p.1 * (1 : ℝ) := by
    intro p hp
    rw [Complex.polarCoord_target, mem_prod] at hp
    have hp0 : 0 < p.1 := hp.1
    rw [Complex.norm_polarCoord_symm, abs_of_pos hp0]
    by_cases hr : p.1 < 1
    · simp only [φ, hr, ite_eq_left hr, mul_one]
      calc
        p.1 * (c * (1 - p.1 ^ 2) ^ α * p.1 ^ (2 * n))
            = c * (1 - p.1 ^ 2) ^ α * (p.1 * p.1 ^ (2 * n)) := by ring
        _ = c * (1 - p.1 ^ 2) ^ α * p.1 ^ (2 * n + 1) := by rw [← pow_succ']
    · simp [φ, hr]
  simp_rw [smul_eq_mul]
  have hcongr : ∫ p in Complex.polarCoord.target,
      p.1 * (((if ‖Complex.polarCoord.symm p‖ < 1 then
        c * (1 - ‖Complex.polarCoord.symm p‖ ^ 2) ^ α else 0) *
        ‖Complex.polarCoord.symm p‖ ^ (2 * n))) =
      ∫ p in Complex.polarCoord.target, φ p.1 * (1 : ℝ) :=
    setIntegral_congr_fun Complex.polarCoord.open_target.measurableSet hpolar
  apply hcongr.trans
  rw [Complex.polarCoord_target, Measure.volume_eq_prod]
  rw [setIntegral_prod_mul (μ := volume) (ν := volume) φ (fun _ : ℝ => (1 : ℝ))
    (Ioi (0 : ℝ)) (Ioo (-π) π)]
  have hang : ∫ _ in Ioo (-π) π, (1 : ℝ) = 2 * π := by
    rw [setIntegral_const, smul_eq_mul, mul_one,
      volume_real_Ioo_of_le (by linarith [pi_nonneg] : (-π) ≤ π), sub_neg_eq_add]
    ring
  rw [hang]
  have hφ : ∀ r, φ r =
      c * (if r < 1 then (1 - r ^ 2) ^ α * r ^ (2 * n + 1) else 0) := by
    intro r
    by_cases hr : r < 1
    · dsimp only [φ]
      rw [ite_eq_left hr, ite_eq_left hr, mul_assoc]
    · dsimp only [φ]
      rw [ite_eq_right hr, ite_eq_right hr, mul_zero]
  simp_rw [hφ, MeasureTheory.integral_const_mul]
  let ψ : ℝ → ℝ := fun u =>
    if 0 < u ∧ u < 1 then (1 / 2) * u ^ n * (1 - u) ^ α else 0
  have hrad : ∫ r in Ioi (0 : ℝ),
      (if r < 1 then (1 - r ^ 2) ^ α * r ^ (2 * n + 1) else 0) =
      ∫ u in Ioi (0 : ℝ), ψ u := by
    rw [← integral_comp_rpow_Ioi_of_pos (g := ψ) (p := 2) (by norm_num : (0 : ℝ) < 2)]
    refine setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
    have hr0 : (0 : ℝ) < r := hr
    have h21 : (2 : ℝ) - 1 = 1 := by norm_num
    have h2 : ((2 : ℕ) : ℝ) = 2 := by norm_num
    rw [h21, rpow_one, ← h2, rpow_natCast]
    by_cases h1 : r < 1
    · have hr2 : 0 < r ^ 2 := by positivity
      have hr2lt : r ^ 2 < 1 := by
        rw [← one_pow 2]
        exact pow_lt_pow_left₀ h1 hr0.le two_ne_zero
      dsimp only [ψ]
      have hr2mem : 0 < r ^ 2 ∧ r ^ 2 < 1 := ⟨hr2, hr2lt⟩
      rw [smul_eq_mul, ite_eq_left hr2mem, ite_eq_left h1]
      have hpow : (r ^ 2) ^ n = r ^ (2 * n) := by rw [← pow_mul]
      calc
        (1 - r ^ 2) ^ α * r ^ (2 * n + 1)
            = r ^ (2 * n + 1) * (1 - r ^ 2) ^ α := by ring
        _ = (r * (r ^ 2) ^ n) * (1 - r ^ 2) ^ α := by rw [pow_succ', ← hpow]
        _ = 2 * r * ((1 / 2) * (r ^ 2) ^ n * (1 - r ^ 2) ^ α) := by ring
    · have hr2ge : ¬ (0 < r ^ 2 ∧ r ^ 2 < 1) := by
        intro hr2
        have hr1 : r < 1 := by
          rw [← one_pow 2] at hr2
          exact lt_of_pow_lt_pow_left₀ 2 zero_le_one hr2.2
        exact h1 hr1
      dsimp only [ψ]
      rw [ite_eq_right h1, ite_eq_right hr2ge, smul_eq_mul, mul_zero]
  rw [hrad]
  have hψ : ∫ u in Ioi (0 : ℝ), ψ u =
      (1 / 2) * ∫ x in (0 : ℝ)..1, x ^ n * (1 - x) ^ α := by
    have hψind : ψ = fun u =>
        (1 / 2) * (Ioo (0 : ℝ) 1).indicator (fun v => v ^ n * (1 - v) ^ α) u := by
      ext u
      by_cases hu : u ∈ Ioo (0 : ℝ) 1
      · have hmem : 0 < u ∧ u < 1 := mem_Ioo.mp hu
        dsimp only [ψ]
        rw [ite_eq_left hmem, indicator_of_mem hu, mul_assoc]
      · have hnot : ¬ (0 < u ∧ u < 1) := by simpa [mem_Ioo] using hu
        dsimp only [ψ]
        rw [ite_eq_right hnot, indicator_of_notMem hu, mul_zero]
    rw [hψind, MeasureTheory.integral_const_mul,
      setIntegral_indicator measurableSet_Ioo]
    have hinter : Ioi (0 : ℝ) ∩ Ioo 0 1 = Ioo 0 1 := by
      ext u
      simp only [mem_inter_iff, mem_Ioi, mem_Ioo]
      exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩
    rw [hinter, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      setIntegral_congr_set Ioo_ae_eq_Ioc.symm]
  rw [hψ, integral_pow_mul_one_sub_rpow hα n]
  have hne : α + 1 ≠ 0 := by linarith
  have hshift : (α + 1) + 1 = α + 2 := by ring
  have hhalf : (1 / 2 : ℝ) * (2 * π) = π := by
    rw [← mul_assoc, one_div, inv_mul_cancel₀ two_ne_zero, one_mul]
  have hcπ : c * π = α + 1 := by
    dsimp [c]
    exact div_mul_cancel₀ _ Real.pi_ne_zero
  have hnum : (α + 1) * Real.Gamma (α + 1) = Real.Gamma (α + 2) := by
    rw [← Real.Gamma_add_one hne, hshift]
  set G1 : ℝ := Real.Gamma (α + 1)
  set G2 : ℝ := Real.Gamma (α + 2)
  set Gn : ℝ := Real.Gamma (n + α + 2)
  set Nf : ℝ := (n.factorial : ℝ)
  simp only [div_eq_mul_inv, one_mul]
  have hhalf' : (2 : ℝ)⁻¹ * (2 * π) = π := by rw [← one_div, hhalf]
  have hcoeff : c * (2 : ℝ)⁻¹ * (2 * π) = c * π := by rw [mul_assoc, hhalf']
  have hpull : c * ((2 : ℝ)⁻¹ * (G1 * Nf * Gn⁻¹)) * (2 * π) =
      (c * π) * (G1 * Nf * Gn⁻¹) := by
    calc
      c * ((2 : ℝ)⁻¹ * (G1 * Nf * Gn⁻¹)) * (2 * π)
          = (c * (2 : ℝ)⁻¹ * (2 * π)) * (G1 * Nf * Gn⁻¹) := by ring
      _ = (c * π) * (G1 * Nf * Gn⁻¹) := by rw [hcoeff]
  rw [hpull, hcπ, ← mul_assoc (α + 1), ← mul_assoc (α + 1), hnum]

/-- Every monomial is square-integrable for the weighted measure. -/
private lemma integrable_norm_sq_monomial {α : ℝ} (hα : -1 < α) (n : ℕ) :
    Integrable (fun z : ℂ => ‖z ^ n‖ ^ 2) (bergmanMeasure α) := by
  by_contra h
  have hI := integral_norm_monomial_sq hα n
  rw [integral_undef h] at hI
  exact (bergmanMonomialNormSq_pos hα n).ne' <| by
    simpa [bergmanMonomialNormSq] using hI.symm

/-- Every monomial lies in the weighted `L²` space. -/
theorem memLp_monomial {α : ℝ} (hα : -1 < α) (n : ℕ) :
    MemLp (fun z : ℂ => z ^ n) 2 (bergmanMeasure α) := by
  have hcont : Continuous (fun z : ℂ => z ^ n) := continuous_pow n
  rw [memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable]
  exact integrable_norm_sq_monomial hα n

/-- Every conjugate monomial lies in the weighted `L²` space. -/
theorem memLp_conj_monomial {α : ℝ} (hα : -1 < α) (n : ℕ) :
    MemLp (fun z : ℂ => conj (z ^ n)) 2 (bergmanMeasure α) := by
  have hcont : Continuous (fun z : ℂ => conj (z ^ n)) :=
    continuous_conj.comp (continuous_pow n)
  rw [memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable]
  simpa [norm_conj] using integrable_norm_sq_monomial hα n

/-- The product of a conjugate monomial and a monomial is integrable. -/
private lemma integrable_conj_pow_mul_pow {α : ℝ} (hα : -1 < α) (n m : ℕ) :
    Integrable (fun z : ℂ => conj (z ^ n) * z ^ m) (bergmanMeasure α) :=
  memLp_one_iff_integrable.mp ((memLp_conj_monomial hα n).mul (memLp_monomial hα m))

/-- Monomials are orthogonal, with square norms `bergmanMonomialNormSq α n`. -/
private lemma integral_conj_pow_mul_pow {α : ℝ} (hα : -1 < α) (n m : ℕ) :
    ∫ z, conj (z ^ n) * z ^ m ∂bergmanMeasure α =
      if n = m then (bergmanMonomialNormSq α n : ℂ) else 0 := by
  by_cases hnm : n = m
  · subst hnm
    have hfun : (fun z : ℂ => conj (z ^ n) * z ^ n) =
        fun z => ((‖z ^ n‖ ^ 2 : ℝ) : ℂ) := by
      ext z
      rw [← RCLike.inner_apply', inner_self_eq_norm_sq_to_K]
      exact (Complex.ofReal_pow ‖z ^ n‖ 2).symm
    rw [hfun, integral_complex_ofReal, integral_norm_monomial_sq hα n, ite_eq_left rfl]
    rfl
  · rw [ite_eq_right hnm]
    set c : ℝ := (α + 1) / π
    have hc : 0 < c := div_pos (by linarith) pi_pos
    let dens : ℂ → ℝ≥0∞ := fun z =>
      if ‖z‖ < 1 then ENNReal.ofReal (c * (1 - ‖z‖ ^ 2) ^ α) else 0
    have hμ : bergmanMeasure α = volume.withDensity dens := by
      simp [bergmanMeasure, dens, c]
    have hmeas : Measurable dens := by
      unfold dens
      refine Measurable.ite (measurableSet_lt continuous_norm.measurable measurable_const)
        ?_ measurable_const
      refine ENNReal.measurable_ofReal.comp ?_
      refine measurable_const.mul ?_
      refine Measurable.pow_const ?_ α
      exact measurable_const.sub (continuous_norm.measurable.pow_const 2)
    have hfin : ∀ᵐ z ∂volume, dens z < ∞ := ae_of_all _ fun z => by
      by_cases hz : ‖z‖ < 1
      · simp [dens, hz, ENNReal.ofReal_lt_top]
      · simp [dens, hz]
    have hto : ∀ z, (dens z).toReal =
        if ‖z‖ < 1 then c * (1 - ‖z‖ ^ 2) ^ α else 0 := by
      intro z
      by_cases hz : ‖z‖ < 1
      · have hsq : ‖z‖ ^ 2 < 1 := by
          rw [← one_pow 2]
          exact pow_lt_pow_left₀ hz (norm_nonneg z) two_ne_zero
        have hnonneg : 0 ≤ c * (1 - ‖z‖ ^ 2) ^ α :=
          mul_nonneg hc.le (rpow_nonneg (sub_nonneg.mpr hsq.le) α)
        simp [dens, hz, ENNReal.toReal_ofReal hnonneg]
      · simp [dens, hz]
    let φ : ℝ → ℂ := fun r =>
      ((if r < 1 then c * (1 - r ^ 2) ^ α * r ^ (n + m + 1) else 0 : ℝ) : ℂ)
    let ψ : ℝ → ℂ := fun θ =>
      Complex.exp ((((m : ℤ) - (n : ℤ)) : ℂ) * (θ : ℂ) * I)
    rw [hμ, integral_withDensity_eq_integral_toReal_smul hmeas hfin]
    simp_rw [hto, Algebra.smul_def, Complex.coe_algebraMap]
    rw [← Complex.integral_comp_polarCoord_symm (f := fun z : ℂ =>
      ((if ‖z‖ < 1 then c * (1 - ‖z‖ ^ 2) ^ α else 0 : ℝ) : ℂ) *
        (conj (z ^ n) * z ^ m))]
    have hpolar : ∀ p ∈ polarCoord.target,
        p.1 • ((((if ‖Complex.polarCoord.symm p‖ < 1 then
            c * (1 - ‖Complex.polarCoord.symm p‖ ^ 2) ^ α else 0 : ℝ) : ℂ) *
          (conj ((Complex.polarCoord.symm p) ^ n) * (Complex.polarCoord.symm p) ^ m))) =
          φ p.1 * ψ p.2 := by
      intro p hp
      rw [polarCoord_target, mem_prod] at hp
      have hp0 : 0 < p.1 := hp.1
      have hnorm : ‖Complex.polarCoord.symm p‖ = p.1 := by
        rw [Complex.norm_polarCoord_symm, abs_of_pos hp0]
      rw [hnorm, conj_pow_mul_pow_polar n m p.1 p.2, Algebra.smul_def, Complex.coe_algebraMap]
      set r : ℝ := p.1
      by_cases hr : r < 1
      · rw [ite_eq_left hr]
        have hreal : r * (c * (1 - r ^ 2) ^ α) * r ^ (n + m) =
            c * (1 - r ^ 2) ^ α * r ^ (n + m + 1) := by
          calc
            r * (c * (1 - r ^ 2) ^ α) * r ^ (n + m)
                = c * (1 - r ^ 2) ^ α * (r * r ^ (n + m)) := by ring
            _ = c * (1 - r ^ 2) ^ α * r ^ (n + m + 1) := by rw [← pow_succ']
        have hφ : φ r = ((c * (1 - r ^ 2) ^ α * r ^ (n + m + 1) : ℝ) : ℂ) := by
          simp only [φ, hr, ite_true]
        rw [hφ]
        have hcast : (r : ℂ) * (((c * (1 - r ^ 2) ^ α : ℝ) : ℂ) *
            ((r : ℂ) ^ (n + m) * ψ p.2)) =
            ((c * (1 - r ^ 2) ^ α * r ^ (n + m + 1) : ℝ) : ℂ) * ψ p.2 := by
          calc
            (r : ℂ) * (((c * (1 - r ^ 2) ^ α : ℝ) : ℂ) *
                ((r : ℂ) ^ (n + m) * ψ p.2))
                = ((r : ℂ) * ((c * (1 - r ^ 2) ^ α : ℝ) : ℂ) *
                    (r : ℂ) ^ (n + m)) * ψ p.2 := by ring
            _ = ((r * (c * (1 - r ^ 2) ^ α) * r ^ (n + m) : ℝ) : ℂ) * ψ p.2 := by
                  rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
            _ = ((c * (1 - r ^ 2) ^ α * r ^ (n + m + 1) : ℝ) : ℂ) * ψ p.2 := by
                  rw [hreal]
        exact hcast
      · simp [φ, ψ, hr]
    have hcongr : ∫ p in polarCoord.target,
        p.1 • ((((if ‖Complex.polarCoord.symm p‖ < 1 then
            c * (1 - ‖Complex.polarCoord.symm p‖ ^ 2) ^ α else 0 : ℝ) : ℂ) *
          (conj ((Complex.polarCoord.symm p) ^ n) *
            (Complex.polarCoord.symm p) ^ m))) =
        ∫ p in polarCoord.target, φ p.1 * ψ p.2 :=
      setIntegral_congr_fun polarCoord.open_target.measurableSet hpolar
    rw [hcongr, polarCoord_target, Measure.volume_eq_prod,
      setIntegral_prod_mul (μ := volume) (ν := volume) φ ψ (Ioi (0 : ℝ)) (Ioo (-π) π)]
    have hk : (m : ℤ) - (n : ℤ) ≠ 0 := by
      intro hk0
      exact hnm (Nat.cast_injective (sub_eq_zero.mp hk0).symm)
    have hang : ∫ θ in Ioo (-π) π, ψ θ = 0 := by
      have hint : ∫ θ in (-π)..π, ψ θ = 0 := by
        dsimp only [ψ]
        rw [← Int.cast_sub, integral_exp_int_mul_I, ite_eq_right hk]
      rw [setIntegral_congr_set (Ioo_ae_eq_Ioc (a := -π) (b := π)),
        ← intervalIntegral.integral_of_le (by linarith [pi_nonneg])]
      exact hint
    rw [hang, mul_zero]

/-- The binomial coefficient of the kernel series is the reciprocal monomial weight. -/
private lemma bergmanKernelCoeff {α : ℝ} (hα : -1 < α) (n : ℕ) :
    Ring.choose ((α : ℂ) + n + 1) n = (bergmanMonomialNormSq α n : ℂ)⁻¹ := by
  have hne : ∀ k : ℕ, (α : ℂ) + 2 ≠ -k := by
    intro k hk
    have hre' := congrArg Complex.re hk
    simp only [Complex.add_re, Complex.ofReal_re, Complex.neg_re, Complex.natCast_re] at hre'
    norm_num at hre'
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith [hk0]
  have harg : ((α : ℂ) + n + 1) - n + 1 = (α : ℂ) + 2 := by
    ring
  have hGamma : (ascPochhammer ℂ n).eval ((α : ℂ) + 2) =
      Complex.Gamma ((α : ℂ) + 2 + n) / Complex.Gamma ((α : ℂ) + 2) := by
    exact (Complex.Gamma_add_nat_div_Gamma_eq (n := n) ((α : ℂ) + 2) hne).symm
  rw [Ring.choose_eq_smul, Polynomial.descPochhammer_smeval_eq_ascPochhammer,
    Polynomial.ascPochhammer_smeval_eq_eval, harg, hGamma, smul_eq_mul]
  have hshift : (α : ℂ) + 2 + n = ((n + α + 2 : ℝ) : ℂ) := by
    push_cast
    ring
  have hbase : (α : ℂ) + 2 = ((α + 2 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hshift, hbase, Complex.Gamma_ofReal, Complex.Gamma_ofReal, bergmanMonomialNormSq,
    Complex.ofReal_div, Complex.ofReal_mul, inv_div]
  have hposG : (Real.Gamma (α + 2) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.Gamma_pos_of_pos (by linarith : 0 < α + 2)).ne'
  have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hposn : (Real.Gamma (n + α + 2) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.Gamma_pos_of_pos (by linarith [hnn] : 0 < (n : ℝ) + α + 2)).ne'
  have hfact : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  field_simp [hposG, hposn, hfact]
  norm_cast

/-- `cₙ₊₁ = cₙ · (n+1) / (n+α+2)`. -/
private lemma bergmanMonomialNormSq_succ {α : ℝ} (hα : -1 < α) (n : ℕ) :
    bergmanMonomialNormSq α (n + 1) =
      bergmanMonomialNormSq α n * (((n : ℝ) + 1) / ((n : ℝ) + α + 2)) := by
  dsimp only [bergmanMonomialNormSq]
  have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hden : (n : ℝ) + α + 2 ≠ 0 := by linarith [hnn]
  have hfact : ((n + 1).factorial : ℝ) = (n.factorial : ℝ) * ((n : ℝ) + 1) := by
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add_one, mul_comm]
  have hshiftN : ((n + 1 : ℕ) : ℝ) + α + 2 = (n : ℝ) + α + 2 + 1 := by
    rw [Nat.cast_add_one]
    ring
  rw [hshiftN, Real.Gamma_add_one hden, hfact]
  have hGn : Real.Gamma ((n : ℝ) + α + 2) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by linarith : 0 < (n : ℝ) + α + 2)).ne'
  have hG2 : Real.Gamma (α + 2) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by linarith : 0 < α + 2)).ne'
  field_simp [hden, hGn, hG2]

/-- `cₙ / cₙ₊₁ = (n+α+2) / (n+1)`. -/
private lemma bergmanMonomialNormSq_div_succ {α : ℝ} (hα : -1 < α) (n : ℕ) :
    bergmanMonomialNormSq α n / bergmanMonomialNormSq α (n + 1) =
      ((n : ℝ) + α + 2) / ((n : ℝ) + 1) := by
  rw [bergmanMonomialNormSq_succ hα n]
  have hpos : bergmanMonomialNormSq α n ≠ 0 := (bergmanMonomialNormSq_pos hα n).ne'
  have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hden : (n : ℝ) + 1 ≠ 0 := by linarith [hnn]
  have hden2 : (n : ℝ) + α + 2 ≠ 0 := by linarith [hnn]
  field_simp [hpos, hden, hden2]

/-- `∑ rⁿ / √cₙ` converges for `0 ≤ r < 1`. -/
theorem summable_div_sqrt_monomialNormSq {α : ℝ} (hα : -1 < α) {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun n : ℕ => r ^ n / Real.sqrt (bergmanMonomialNormSq α n)) := by
  by_cases hr : r = 0
  · subst hr
    apply (summable_nat_add_iff 1).1
    convert summable_zero with n
    rw [zero_pow (Nat.succ_ne_zero n), zero_div]
  · have hrpos : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hr)
    refine summable_of_ratio_test_tendsto_lt_one hr1 ?_ ?_
    · refine Eventually.of_forall fun n => ?_
      exact div_ne_zero (pow_ne_zero n hrpos.ne')
        ((Real.sqrt_ne_zero').2 (bergmanMonomialNormSq_pos hα n))
    · have hratio : ∀ n, (r ^ (n + 1) / Real.sqrt (bergmanMonomialNormSq α (n + 1))) /
          (r ^ n / Real.sqrt (bergmanMonomialNormSq α n)) =
          r * Real.sqrt (((n : ℝ) + α + 2) / ((n : ℝ) + 1)) := by
        intro n
        set s0 : ℝ := Real.sqrt (bergmanMonomialNormSq α n)
        set s1 : ℝ := Real.sqrt (bergmanMonomialNormSq α (n + 1))
        have hs0 : s0 ≠ 0 := (Real.sqrt_ne_zero').2 (bergmanMonomialNormSq_pos hα n)
        have hs1 : s1 ≠ 0 := (Real.sqrt_ne_zero').2 (bergmanMonomialNormSq_pos hα (n + 1))
        have hrn : r ^ n ≠ 0 := pow_ne_zero n hrpos.ne'
        have hdiv : (r ^ (n + 1) / s1) / (r ^ n / s0) =
            r ^ (n + 1) * s0 / (s1 * r ^ n) := by
          field_simp [hs0, hs1, hrn]
        rw [hdiv, pow_succ]
        have hcancel : r ^ n * r * s0 / (s1 * r ^ n) = r * s0 / s1 := by
          field_simp [hrn, hs1]
        rw [hcancel, mul_div_assoc]
        have hs : s0 / s1 =
            Real.sqrt (bergmanMonomialNormSq α n / bergmanMonomialNormSq α (n + 1)) := by
          dsimp only [s0, s1]
          exact (Real.sqrt_div (bergmanMonomialNormSq_pos hα n).le _).symm
        rw [hs, bergmanMonomialNormSq_div_succ hα n]
      have hnonneg : ∀ n, 0 ≤ r ^ n / Real.sqrt (bergmanMonomialNormSq α n) :=
        fun n => div_nonneg (pow_nonneg hr0 n) (Real.sqrt_nonneg _)
      simp_rw [fun n => Real.norm_of_nonneg (hnonneg n), hratio]
      have hfrac : Tendsto (fun n : ℕ => ((n : ℝ) + α + 2) / ((n : ℝ) + 1)) atTop (nhds 1) := by
        have hrewrite : ∀ n : ℕ, ((n : ℝ) + α + 2) / ((n : ℝ) + 1) =
            1 + (α + 1) / ((n : ℝ) + 1) := by
          intro n
          have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
          have hn1 : (n : ℝ) + 1 ≠ 0 := by linarith [hnn]
          field_simp [hn1]
          ring
        simp_rw [hrewrite]
        have hden : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
          tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
        have hdiv : Tendsto (fun n : ℕ => (α + 1) / ((n : ℝ) + 1)) atTop (nhds 0) :=
          Tendsto.div_atTop tendsto_const_nhds hden
        have hsum := Tendsto.const_add (1 : ℝ) hdiv
        have hlim : (1 : ℝ) + 0 = 1 := add_zero (1 : ℝ)
        rw [hlim] at hsum
        exact hsum
      have hsq := (Real.continuous_sqrt.tendsto 1).comp hfrac
      simpa [Function.comp_def, Real.sqrt_one, mul_one] using Tendsto.mul tendsto_const_nhds hsq

/-- The binomial series of `(1-ζ)^(-α-2)` has coefficients `1/cₙ`. -/
private lemma bergmanKernelSeries_eq {α : ℝ} (hα : -1 < α) {ζ : ℂ} (hζ : ‖ζ‖ < 1) :
    ∑' n : ℕ, (bergmanMonomialNormSq α n : ℂ)⁻¹ * ζ ^ n = (1 - ζ) ^ (-(α : ℂ) - 2) := by
  have hmem : ζ ∈ Metric.eball (0 : ℂ) (1 : ℝ≥0∞) := by
    rw [Metric.mem_eball, eDist_eq_eNorm_sub, sub_zero, ← ENNReal.coe_one, eNorm_lt_coe,
      ← NNReal.coe_lt_coe, coe_nnNorm, NNReal.coe_one]
    exact hζ
  have hps := one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero ((α : ℂ) + 2)
  have hsum := hps.hasSum hmem
  have hidx : ∀ n : ℕ, (α : ℂ) + 2 + n - 1 = (α : ℂ) + n + 1 := by
    intro n
    ring
  have hterm : ∀ n, FormalMultilinearSeries.ofScalars ℂ
      (fun n ↦ Ring.choose ((α : ℂ) + 2 + n - 1) n) n (fun _ ↦ ζ) =
      (bergmanMonomialNormSq α n : ℂ)⁻¹ * ζ ^ n := by
    intro n
    rw [FormalMultilinearSeries.ofScalars_apply_eq, hidx n, bergmanKernelCoeff hα n, smul_eq_mul]
  have hval : 1 / (1 - ζ) ^ ((α : ℂ) + 2) = (1 - ζ) ^ (-(α : ℂ) - 2) := by
    have hexp : -(α : ℂ) - 2 = -((α : ℂ) + 2) := by ring
    rw [hexp, cpow_neg, inv_eq_one_div]
  have heq := hsum.congr_fun fun n => (hterm n).symm
  rw [zero_add] at heq
  exact heq.tsum_eq.trans hval



/-- `∫ conj(zⁿ) f(z) dA_α = aₙ cₙ` for `f` holomorphic and square-integrable. -/
theorem integral_conj_pow_mul_holomorphic {α : ℝ} (hα : -1 < α) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (Metric.ball 0 1)) (hLp : MemLp f 2 (bergmanMeasure α))
    (n : ℕ) :
    ∫ z, conj (z ^ n) * f z ∂bergmanMeasure α =
      taylorCoefficient f n * (bergmanMonomialNormSq α n : ℂ) := by
  have hconj : Integrable (fun z : ℂ => conj (z ^ n) * f z) (bergmanMeasure α) :=
    memLp_one_iff_integrable.mp ((memLp_conj_monomial hα n).mul hLp)
  set c : ℝ := (α + 1) / π
  have hc : 0 < c := div_pos (by linarith) pi_pos
  let dens : ℂ → ℝ≥0∞ := fun z =>
    if ‖z‖ < 1 then ENNReal.ofReal (c * (1 - ‖z‖ ^ 2) ^ α) else 0
  have hμ : bergmanMeasure α = volume.withDensity dens := by
    simp [bergmanMeasure, dens, c]
  have hmeas : Measurable dens := by
    unfold dens
    refine Measurable.ite (measurableSet_lt continuous_norm.measurable measurable_const)
      ?_ measurable_const
    refine ENNReal.measurable_ofReal.comp ?_
    refine measurable_const.mul ?_
    refine Measurable.pow_const ?_ α
    exact measurable_const.sub (continuous_norm.measurable.pow_const 2)
  have hfin : ∀ᵐ z ∂volume, dens z < ∞ := ae_of_all _ fun z => by
    by_cases hz : ‖z‖ < 1
    · simp [dens, hz, ENNReal.ofReal_lt_top]
    · simp [dens, hz]
  have hto : ∀ z, (dens z).toReal =
      if ‖z‖ < 1 then c * (1 - ‖z‖ ^ 2) ^ α else 0 := by
    intro z
    by_cases hz : ‖z‖ < 1
    · have hsq : ‖z‖ ^ 2 < 1 := by
        rw [← one_pow 2]
        exact pow_lt_pow_left₀ hz (norm_nonneg z) two_ne_zero
      have hnonneg : 0 ≤ c * (1 - ‖z‖ ^ 2) ^ α :=
        mul_nonneg hc.le (rpow_nonneg (sub_nonneg.mpr hsq.le) α)
      simp [dens, hz, ENNReal.toReal_ofReal hnonneg]
    · simp [dens, hz]
  let g0 : ℂ → ℂ := fun z =>
    ((if ‖z‖ < 1 then c * (1 - ‖z‖ ^ 2) ^ α else 0 : ℝ) : ℂ) * (conj (z ^ n) * f z)
  rw [hμ] at hconj
  have hsmul : Integrable (fun z => (dens z).toReal • (conj (z ^ n) * f z)) volume :=
    (integrable_withDensity_iff_integrable_smul₀' hmeas.aemeasurable hfin).1 hconj
  have hg0 : Integrable g0 volume := by
    refine (integrable_congr (Eventually.of_forall fun z => ?_)).2 hsmul
    dsimp only [g0]
    rw [hto z, Algebra.smul_def, Complex.coe_algebraMap]
  rw [hμ, integral_withDensity_eq_integral_toReal_smul hmeas hfin]
  simp_rw [hto, Algebra.smul_def, Complex.coe_algebraMap]
  rw [← Complex.integral_comp_polarCoord_symm (f := g0)]
  let φ : ℝ → ℂ := fun r =>
    ((if r < 1 then c * (1 - r ^ 2) ^ α * r ^ (n + 1) else 0 : ℝ) : ℂ)
  let ang : ℝ → ℝ → ℂ := fun r θ =>
    Complex.exp (-(n : ℂ) * (θ : ℂ) * I) * f (circleMap 0 r θ)
  have hpolar : EqOn (fun p : ℝ × ℝ => p.1 • g0 (Complex.polarCoord.symm p))
      (fun p => φ p.1 * ang p.1 p.2) polarCoord.target := by
    intro p hp
    dsimp only
    rw [polarCoord_target, mem_prod] at hp
    have hp0 : 0 < p.1 := hp.1
    set r : ℝ := p.1
    set θ : ℝ := p.2
    have hnorm : ‖Complex.polarCoord.symm (r, θ)‖ = r := by
      rw [Complex.norm_polarCoord_symm, abs_of_pos hp0]
    have hconj := conj_pow_mul_pow_polar n 0 r θ
    rw [pow_zero, mul_one, Nat.add_zero] at hconj
    have hconj' : conj ((Complex.polarCoord.symm (r, θ)) ^ n) =
        (r : ℂ) ^ n * Complex.exp (-(n : ℂ) * (θ : ℂ) * I) := by
      rw [hconj]
      congr 1
      congr 1
      push_cast
      ring
    rw [Algebra.smul_def, Complex.coe_algebraMap]
    dsimp only [g0]
    rw [hnorm, hconj', ← zero_add (Complex.polarCoord.symm (r, θ)),
      TauCeti.add_polarCoord_symm_eq_circleMap 0 (r, θ)]
    by_cases hr : r < 1
    · rw [ite_eq_left hr]
      have hφ : φ r = ((c * (1 - r ^ 2) ^ α * r ^ (n + 1) : ℝ) : ℂ) := by
        simp [φ, hr]
      rw [hφ]
      have hpow : (r : ℂ) * ((c * (1 - r ^ 2) ^ α : ℝ) : ℂ) * (r : ℂ) ^ n =
          ((c * (1 - r ^ 2) ^ α * r ^ (n + 1) : ℝ) : ℂ) := by
        rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
        have hrpow : r * (c * (1 - r ^ 2) ^ α) * r ^ n =
            c * (1 - r ^ 2) ^ α * r ^ (n + 1) := by
          calc
            r * (c * (1 - r ^ 2) ^ α) * r ^ n
                = c * (1 - r ^ 2) ^ α * (r * r ^ n) := by ring
            _ = c * (1 - r ^ 2) ^ α * r ^ (n + 1) := by rw [← pow_succ']
        rw [hrpow]
      calc
        (r : ℂ) * (((c * (1 - r ^ 2) ^ α : ℝ) : ℂ) *
            (((r : ℂ) ^ n * Complex.exp (-(n : ℂ) * (θ : ℂ) * I)) * f (circleMap 0 r θ)))
            = ((r : ℂ) * ((c * (1 - r ^ 2) ^ α : ℝ) : ℂ) * (r : ℂ) ^ n) *
              (Complex.exp (-(n : ℂ) * (θ : ℂ) * I) * f (circleMap 0 r θ)) := by ring
        _ = ((c * (1 - r ^ 2) ^ α * r ^ (n + 1) : ℝ) : ℂ) * ang r θ := by
              rw [hpow]
    · rw [ite_eq_right hr]
      have hφ : φ r = 0 := by simp [φ, hr]
      rw [hφ, zero_mul]
      rw [Complex.ofReal_zero, zero_mul, mul_zero]
  have hpol : IntegrableOn (fun p : ℝ × ℝ => p.1 • g0 (Complex.polarCoord.symm p))
      polarCoord.target volume :=
    hg0.comp_complexPolarCoord_symm
  have hF : IntegrableOn (fun p : ℝ × ℝ => φ p.1 * ang p.1 p.2) polarCoord.target volume :=
    hpol.congr_fun hpolar polarCoord.open_target.measurableSet
  rw [setIntegral_congr_fun polarCoord.open_target.measurableSet hpolar, polarCoord_target,
    Measure.volume_eq_prod]
  rw [polarCoord_target, Measure.volume_eq_prod] at hF
  rw [setIntegral_prod (fun p => φ p.1 * ang p.1 p.2) hF]
  let ρ : ℝ → ℝ := fun r =>
    if r < 1 then c * (1 - r ^ 2) ^ α * r ^ (2 * n + 1) else 0
  have hinner : ∀ r ∈ Ioi (0 : ℝ),
      ∫ θ in Ioo (-π) π, φ r * ang r θ =
        ((2 * π : ℝ) : ℂ) * taylorCoefficient f n * (ρ r : ℂ) := by
    intro r hr
    have hr0 : 0 < r := hr
    have hθ : ∫ θ in Ioo (-π) π, φ r * ang r θ =
        ∫ θ in (-π)..π, φ r * ang r θ := by
      rw [setIntegral_congr_set (Ioo_ae_eq_Ioc (a := -π) (b := π)),
        ← intervalIntegral.integral_of_le (by linarith [pi_nonneg])]
    by_cases hr1 : r < 1
    · rw [hθ, intervalIntegral.integral_const_mul]
      have hang : ∫ θ in (-π)..π, ang r θ =
          2 * π * taylorCoefficient f n * (r : ℂ) ^ n := by
        simpa [ang] using intervalIntegral_circle_taylorCoeff hf hr0 hr1 n
      rw [hang]
      have hφ : φ r = ((c * (1 - r ^ 2) ^ α * r ^ (n + 1) : ℝ) : ℂ) := by
        simp [φ, hr1]
      have hρ : (ρ r : ℂ) = ((c * (1 - r ^ 2) ^ α * r ^ (2 * n + 1) : ℝ) : ℂ) := by
        simp [ρ, hr1]
      rw [hφ, hρ, Complex.ofReal_mul (c * (1 - r ^ 2) ^ α) (r ^ (n + 1))]
      have hpow : ((r ^ (n + 1) : ℝ) : ℂ) * (r : ℂ) ^ n =
          ((r ^ (2 * n + 1) : ℝ) : ℂ) := by
        rw [← Complex.ofReal_pow, ← Complex.ofReal_mul]
        have hnexp : n + 1 + n = 2 * n + 1 := by
          rw [add_assoc, add_comm 1 n, ← add_assoc, ← two_mul]
        rw [← pow_add, hnexp]
      have htwo : (2 : ℂ) * π = ((2 * π : ℝ) : ℂ) :=
        (Complex.ofReal_mul 2 π).symm
      have hprod : ((c * (1 - r ^ 2) ^ α : ℝ) : ℂ) *
          (((r ^ (n + 1) : ℝ) : ℂ) * (r : ℂ) ^ n) =
          ((c * (1 - r ^ 2) ^ α * r ^ (2 * n + 1) : ℝ) : ℂ) := by
        rw [hpow, ← Complex.ofReal_mul]
      calc
        ((c * (1 - r ^ 2) ^ α : ℝ) : ℂ) * ((r ^ (n + 1) : ℝ) : ℂ) *
            (2 * π * taylorCoefficient f n * (r : ℂ) ^ n)
          = (2 * π * taylorCoefficient f n) *
            (((c * (1 - r ^ 2) ^ α : ℝ) : ℂ) *
              (((r ^ (n + 1) : ℝ) : ℂ) * (r : ℂ) ^ n)) := by ring
        _ = ((2 * π : ℝ) : ℂ) * taylorCoefficient f n *
            ((c * (1 - r ^ 2) ^ α * r ^ (2 * n + 1) : ℝ) : ℂ) := by
          rw [hprod, htwo]
    · rw [hθ, intervalIntegral.integral_const_mul]
      have hφ : φ r = 0 := by simp [φ, hr1]
      have hρ : ρ r = 0 := by simp [ρ, hr1]
      rw [hφ, hρ, zero_mul, Complex.ofReal_zero, mul_zero]
  rw [setIntegral_congr_fun measurableSet_Ioi hinner, MeasureTheory.integral_const_mul,
    integral_complex_ofReal, integral_radial_monomial_weight hα n]
  have hπ : ((2 * π : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast mul_ne_zero two_ne_zero Real.pi_ne_zero
  rw [Complex.ofReal_div]
  field_simp [hπ]

/-- The kernel is the monomial series `∑ zⁿ conj(w)ⁿ / cₙ` for `‖z conj w‖ < 1`. -/
theorem bergmanKernel_eq_tsum {α : ℝ} (hα : -1 < α) {z w : ℂ}
    (hzw : ‖z * conj w‖ < 1) :
    bergmanKernel α z w =
      ∑' n : ℕ, (bergmanMonomialNormSq α n : ℂ)⁻¹ * z ^ n * conj (w ^ n) := by
  rw [bergmanKernel, ← bergmanKernelSeries_eq hα hzw]
  refine tsum_congr fun n => ?_
  rw [mul_pow, ← map_pow (starRingEnd ℂ) w n, ← mul_assoc]

/-- The weighted measure is supported on the open unit disk. -/
theorem bergmanMeasure_compl_ball (α : ℝ) :
    bergmanMeasure α {z : ℂ | 1 ≤ ‖z‖} = 0 := by
  have hs : MeasurableSet {z : ℂ | 1 ≤ ‖z‖} :=
    (isClosed_le continuous_const continuous_norm).measurableSet
  rw [bergmanMeasure, withDensity_apply _ hs]
  refine setLIntegral_eq_zero hs ?_
  intro z hz
  dsimp only
  rw [ite_eq_right (not_lt.mpr hz)]
  exact show (0 : ℝ≥0∞) = (0 : ℂ → ℝ≥0∞) z from rfl

end CKMA
