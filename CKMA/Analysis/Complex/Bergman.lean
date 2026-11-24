/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.MeasureTheory.Function.L2Space

import CKMA.Analysis.Complex.Bergman.Polar
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

/-!
# Weighted disk Bergman spaces

The normalized disk measure has density `(α+1)(1-|z|²)^α/π` for `α > -1`.
The principal-power kernel `(1-z conj(w))^(-α-2)` reproduces square-integrable
holomorphic functions. Monomial norms, closedness of the analytic subspace and the
orthogonal projection describe the Hilbert case; kernel bounds also cover `1 < p < ∞`.

Sources: GAPS 42.51 and 42.52.

The monomial norm is the Beta integral in polar coordinates, using Mathlib's
`Complex.betaIntegral`, `Complex.Gamma_mul_Gamma_eq_betaIntegral`,
`Complex.integral_comp_polarCoord_symm` and
`MeasureTheory.integral_comp_rpow_Ioi_of_pos`. The one-dimensional reduction and the
circular Cauchy formula are in `CKMA.Analysis.Complex.Bergman.Polar`. The reproducing
formula matches Taylor coefficients with the binomial series of the kernel. Closedness
is locally uniform convergence of holomorphic representatives, together with convergence
in measure. The orthogonal projection is `Submodule.starProjection` on that closed
subspace, and its norm is one because the constants belong to the subspace.

## Main definitions

* `CKMA.bergmanMeasure`: normalized radially weighted area measure on the unit disk.
* `CKMA.bergmanKernel`: weighted Bergman reproducing kernel.
* `CKMA.bergmanSet`: analytic subspace of weighted `Lᵖ` on the unit disk.
* `CKMA.bergmanIntegral`: weighted Bergman integral operator.

## Main results

* `CKMA.bergman_reproducing`: reproducing formula on `A²_α(𝔻)`.
* `CKMA.integral_norm_monomial_sq`: weighted `L²` norm of monomials.
* `CKMA.isClosed_bergmanSet`: closedness of `A²_α(𝔻)` in `L²`.
* `CKMA.exists_bergmanProjection`: orthogonal Bergman projection on `L²`.
* `CKMA.bergmanIntegral_bounded`: `Lᵖ` boundedness of the Bergman integral for `1 < p < ∞`.
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

/-- The analytic part of a weighted `Lᵖ` space, expressed through an a.e. holomorphic
  representative. -/
@[expose]
def bergmanSet (α : ℝ) (p : ℝ≥0∞) : Set (Lp ℂ p (bergmanMeasure α)) :=
  {u | ∃ f : ℂ → ℂ, DifferentiableOn ℂ f (Metric.ball 0 1) ∧ u =ᵐ[bergmanMeasure α] f}

/-- The integral formula for the weighted Bergman projection. -/
@[expose]
def bergmanIntegral (α : ℝ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∫ w, bergmanKernel α z w * f w ∂bergmanMeasure α


/-- The monomial square norms; for `α = 0` this is `1/(n+1)`. -/
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


private lemma integrable_norm_sq_monomial {α : ℝ} (hα : -1 < α) (n : ℕ) :
    Integrable (fun z : ℂ => ‖z ^ n‖ ^ 2) (bergmanMeasure α) := by
  by_contra h
  have hI := integral_norm_monomial_sq hα n
  rw [integral_undef h] at hI
  exact (bergmanMonomialNormSq_pos hα n).ne' <| by
    simpa [bergmanMonomialNormSq] using hI.symm

private lemma memLp_monomial {α : ℝ} (hα : -1 < α) (n : ℕ) :
    MemLp (fun z : ℂ => z ^ n) 2 (bergmanMeasure α) := by
  have hcont : Continuous (fun z : ℂ => z ^ n) := continuous_pow n
  rw [memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable]
  exact integrable_norm_sq_monomial hα n

private lemma memLp_conj_monomial {α : ℝ} (hα : -1 < α) (n : ℕ) :
    MemLp (fun z : ℂ => conj (z ^ n)) 2 (bergmanMeasure α) := by
  have hcont : Continuous (fun z : ℂ => conj (z ^ n)) :=
    continuous_conj.comp (continuous_pow n)
  rw [memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable]
  simpa [norm_conj] using integrable_norm_sq_monomial hα n

private lemma integrable_conj_pow_mul_pow {α : ℝ} (hα : -1 < α) (n m : ℕ) :
    Integrable (fun z : ℂ => conj (z ^ n) * z ^ m) (bergmanMeasure α) :=
  memLp_one_iff_integrable.mp ((memLp_conj_monomial hα n).mul (memLp_monomial hα m))


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
private lemma summable_div_sqrt_monomialNormSq {α : ℝ} (hα : -1 < α) {r : ℝ}
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
private lemma integral_conj_pow_mul_holomorphic {α : ℝ} (hα : -1 < α) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (Metric.ball 0 1)) (hLp : MemLp f 2 (bergmanMeasure α))
    (n : ℕ) :
    ∫ z, conj (z ^ n) * f z ∂bergmanMeasure α =
      bergmanTaylorCoeff f n * (bergmanMonomialNormSq α n : ℂ) := by
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
    rw [hnorm, hconj', polarCoord_symm_eq_circleMap r θ]
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
    integrableOn_smul_polarCoord hg0
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
        ((2 * π : ℝ) : ℂ) * bergmanTaylorCoeff f n * (ρ r : ℂ) := by
    intro r hr
    have hr0 : 0 < r := hr
    have hθ : ∫ θ in Ioo (-π) π, φ r * ang r θ =
        ∫ θ in (-π)..π, φ r * ang r θ := by
      rw [setIntegral_congr_set (Ioo_ae_eq_Ioc (a := -π) (b := π)),
        ← intervalIntegral.integral_of_le (by linarith [pi_nonneg])]
    by_cases hr1 : r < 1
    · rw [hθ, intervalIntegral.integral_const_mul]
      have hang : ∫ θ in (-π)..π, ang r θ =
          2 * π * bergmanTaylorCoeff f n * (r : ℂ) ^ n := by
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
            (2 * π * bergmanTaylorCoeff f n * (r : ℂ) ^ n)
          = (2 * π * bergmanTaylorCoeff f n) *
            (((c * (1 - r ^ 2) ^ α : ℝ) : ℂ) *
              (((r ^ (n + 1) : ℝ) : ℂ) * (r : ℂ) ^ n)) := by ring
        _ = ((2 * π : ℝ) : ℂ) * bergmanTaylorCoeff f n *
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
private lemma bergmanKernel_eq_tsum {α : ℝ} (hα : -1 < α) {z w : ℂ}
    (hzw : ‖z * conj w‖ < 1) :
    bergmanKernel α z w =
      ∑' n : ℕ, (bergmanMonomialNormSq α n : ℂ)⁻¹ * z ^ n * conj (w ^ n) := by
  rw [bergmanKernel, ← bergmanKernelSeries_eq hα hzw]
  refine tsum_congr fun n => ?_
  rw [mul_pow, ← map_pow (starRingEnd ℂ) w n, ← mul_assoc]

/-- The weighted measure is supported on the open unit disk. -/
private lemma bergmanMeasure_compl_ball (α : ℝ) :
    bergmanMeasure α {z : ℂ | 1 ≤ ‖z‖} = 0 := by
  have hs : MeasurableSet {z : ℂ | 1 ≤ ‖z‖} :=
    (isClosed_le continuous_const continuous_norm).measurableSet
  rw [bergmanMeasure, withDensity_apply _ hs]
  refine setLIntegral_eq_zero hs ?_
  intro z hz
  dsimp only
  rw [ite_eq_right (not_lt.mpr hz)]
  exact show (0 : ℝ≥0∞) = (0 : ℂ → ℝ≥0∞) z from rfl

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
      bergmanTaylorCoeff f n * z ^ n := by
    intro n
    rw [integral_conj_pow_mul_holomorphic hα hf hLp n]
    have hc0 : (bergmanMonomialNormSq α n : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (bergmanMonomialNormSq_ne_zero hα n)
    set a : ℂ := (bergmanMonomialNormSq α n : ℂ)
    set b : ℂ := z ^ n
    set t : ℂ := bergmanTaylorCoeff f n
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
  rw [bergmanTaylorCoeff, sub_zero, mul_assoc]

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

/-- The weighted holomorphic `L²` classes form a linear subspace. -/
private def bergmanSubmodule (α : ℝ) : Submodule ℂ (Lp ℂ 2 (bergmanMeasure α)) where
  carrier := bergmanSet α 2
  add_mem' := by
    rintro u v ⟨fu, hfu, hue⟩ ⟨fv, hfv, hve⟩
    exact ⟨fu + fv, hfu.add hfv, (Lp.coeFn_add u v).trans (hue.add hve)⟩
  zero_mem' := ⟨(0 : ℂ → ℂ), differentiableOn_const (0 : ℂ),
    Lp.coeFn_zero ℂ 2 (bergmanMeasure α)⟩
  smul_mem' := by
    rintro c u ⟨fu, hfu, hue⟩
    exact ⟨c • fu, hfu.const_smul c, (Lp.coeFn_smul c u).trans (hue.const_smul c)⟩

/-- The constant monomial has weighted norm one. -/
private lemma bergmanMonomialNormSq_zero {α : ℝ} (hα : -1 < α) :
    bergmanMonomialNormSq α 0 = 1 := by
  dsimp only [bergmanMonomialNormSq]
  rw [Nat.factorial_zero, Nat.cast_one, mul_one, Nat.cast_zero, zero_add]
  exact div_self (Real.Gamma_pos_of_pos (by linarith : 0 < α + 2)).ne'

/-- The monomial `z ↦ z ^ n` as an element of the weighted `L²` space. -/
private def bergmanMonomialLp {α : ℝ} (hα : -1 < α) (n : ℕ) : Lp ℂ 2 (bergmanMeasure α) :=
  (memLp_monomial hα n).toLp fun z => z ^ n

private lemma bergmanMonomialLp_mem {α : ℝ} (hα : -1 < α) (n : ℕ) :
    bergmanMonomialLp hα n ∈ bergmanSubmodule α :=
  ⟨fun z => z ^ n, (differentiable_pow n).differentiableOn,
    (memLp_monomial hα n).coeFn_toLp⟩

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

private lemma isClosed_bergmanSet_aux {α : ℝ} (hα : -1 < α) : IsClosed (bergmanSet α 2) := by
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

/-- The holomorphic `L²` subspace is closed. -/
theorem isClosed_bergmanSet {α : ℝ} (hα : -1 < α) : IsClosed (bergmanSet α 2) :=
  isClosed_bergmanSet_aux hα

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

private lemma exists_bergmanProjection_aux {α : ℝ} (hα : -1 < α) :
    ∃ P : Lp ℂ 2 (bergmanMeasure α) →L[ℂ] Lp ℂ 2 (bergmanMeasure α),
      (∀ f, (fun z ↦ P f z) =ᵐ[bergmanMeasure α] bergmanIntegral α f) ∧
      P.comp P = P ∧ P.adjoint = P ∧ ‖P‖ = 1 ∧ Set.range P = bergmanSet α 2 := by
  let S : Submodule ℂ (Lp ℂ 2 (bergmanMeasure α)) := bergmanSubmodule α
  have hclosed : IsClosed (bergmanSet α 2) := isClosed_bergmanSet_aux hα
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
          bergmanTaylorCoeff F n * z ^ n := by
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
        set t : ℂ := bergmanTaylorCoeff F n
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
      rw [bergmanTaylorCoeff, sub_zero, mul_assoc]
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

/-- **42.52**, Hilbert clause: the integral operator is an orthogonal projection with norm one. -/
theorem exists_bergmanProjection {α : ℝ} (hα : -1 < α) :
    ∃ P : Lp ℂ 2 (bergmanMeasure α) →L[ℂ] Lp ℂ 2 (bergmanMeasure α),
      (∀ f, (fun z ↦ P f z) =ᵐ[bergmanMeasure α] bergmanIntegral α f) ∧
      P.comp P = P ∧ P.adjoint = P ∧ ‖P‖ = 1 ∧ Set.range P = bergmanSet α 2 :=
  exists_bergmanProjection_aux hα

/-- The all-`p` weighted kernel estimate, which is outside the short `L²` argument. -/
theorem bergmanIntegral_bounded {α : ℝ} (hα : -1 < α) {p : ℝ≥0∞}
    (hp : 1 < p) (hp_top : p < ∞) : ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      ∀ f : ℂ → ℂ, MemLp f p (bergmanMeasure α) →
        MemLp (bergmanIntegral α f) p (bergmanMeasure α) ∧
        eLpNorm (bergmanIntegral α f) p (bergmanMeasure α) ≤
          C * eLpNorm f p (bergmanMeasure α) := by
  sorry

end CKMA
