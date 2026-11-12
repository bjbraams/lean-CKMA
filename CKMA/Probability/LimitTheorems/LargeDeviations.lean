/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Probability.LargeDeviations
public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.Independence.Basic
public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import TauCeti.Probability.Process.EmpiricalMeasure

import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Order.LiminfLimsup
import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Order.Compact
import TauCeti.InformationTheory.KullbackLeibler.Variational

/-!
# Cramér and Sanov large deviations (06.60, 06.61)

`extendedLogMGF` retains infinite exponential moments and `cramerRate` is its real
Legendre conjugate. `sampleMeanLaws` uses sample size `n + 1`; Cramér's theorem supplies
a good rate and full LDP under local exponential integrability.

Sanov's theorem is formulated in the weak topology of probability measures on a Polish
space. Empirical measures reuse the Tau Ceti contributors' finite-population construction
in `TauCeti.Probability.Process.EmpiricalMeasure`; the rate is Mathlib's relative entropy
`InformationTheory.klDiv`.
-/

@[expose] public section

noncomputable section

namespace CKMA

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped BigOperators NNReal ENNReal

/-- The log MGF as an extended real, retaining infinite exponential moments. -/
def extendedLogMGF {Ω : Type*} [MeasurableSpace Ω]
    (X : Ω → ℝ) (μ : Measure Ω) (t : ℝ) : EReal :=
  ENNReal.log (∫⁻ ω, ENNReal.ofReal (Real.exp (t * X ω)) ∂μ)

/-- Cramer's convex conjugate rate. For a probability law its Legendre supremum is nonnegative. -/
def cramerRate {Ω : Type*} [MeasurableSpace Ω] (X : Ω → ℝ) (μ : Measure Ω) (x : ℝ) : ℝ≥0∞ :=
  (⨆ t : ℝ, (t * x : ℝ) - extendedLogMGF X μ t).toENNReal

/-- The laws of empirical means, using sample size `n+1`. -/
def sampleMeanLaws {Ω : Type*} [MeasurableSpace Ω] (X : ℕ → Ω → ℝ)
    (μ : Measure Ω) (n : ℕ) : Measure ℝ :=
  μ.map (fun ω ↦ (n + 1 : ℝ)⁻¹ * ∑ j ∈ Finset.range (n + 1), X j ω)

/-- Legendre transform of the extended log moment generating function. -/
private def cramerLegendre {Ω : Type*} [MeasurableSpace Ω]
    (X : Ω → ℝ) (μ : Measure Ω) (x : ℝ) : EReal :=
  ⨆ t : ℝ, (t * x : ℝ) - extendedLogMGF X μ t

/-- The extended log MGF agrees with the cumulant generating function when it is finite. -/
private lemma extendedLogMGF_eq_coe_cgf
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {t : ℝ} (hX : Integrable (fun ω ↦ Real.exp (t * X ω)) μ) :
    extendedLogMGF X μ t = ↑(cgf X μ t) := by
  have hnn : 0 ≤ᵐ[μ] fun ω ↦ Real.exp (t * X ω) :=
    ae_of_all μ fun _ ↦ (Real.exp_pos _).le
  have hpos : 0 < ∫ ω, Real.exp (t * X ω) ∂μ := by
    simpa [mgf] using mgf_pos hX
  rw [extendedLogMGF, ← ofReal_integral_eq_lintegral_ofReal hX hnn,
    ENNReal.log_ofReal_of_pos hpos]
  rfl

/-- A non-integrable exponential moment makes the extended log MGF infinite. -/
private lemma extendedLogMGF_eq_top {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → ℝ} {t : ℝ} (hX : AEMeasurable X μ)
    (h : ¬ Integrable (fun ω ↦ Real.exp (t * X ω)) μ) :
    extendedLogMGF X μ t = ⊤ := by
  have hmeas : AEStronglyMeasurable (fun ω ↦ Real.exp (t * X ω)) μ :=
    aemeasurable_exp_mul t hX
  rw [extendedLogMGF, ENNReal.log_eq_top_iff]
  contrapose! h
  refine ⟨hmeas, ?_⟩
  simp only [HasFiniteIntegral, lt_top_iff_ne_top]
  simpa [Real.enorm_eq_ofReal (Real.exp_pos _).le] using h

/-- The extended log MGF vanishes at zero on a probability space. -/
private lemma extendedLogMGF_zero {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (X : Ω → ℝ) : extendedLogMGF X μ 0 = 0 := by
  simp [extendedLogMGF, Real.exp_zero, ENNReal.ofReal_one]

/-- The extended log MGF of a measurable random variable never takes the value bottom. -/
private lemma extendedLogMGF_ne_bot {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : AEMeasurable X μ) (t : ℝ) :
    extendedLogMGF X μ t ≠ ⊥ := by
  rw [extendedLogMGF, ne_eq, ENNReal.log_eq_bot_iff]
  intro hzero
  have hf : AEMeasurable (fun ω ↦ ENNReal.ofReal (Real.exp (t * X ω))) μ :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      (Real.measurable_exp.comp_aemeasurable (hX.const_mul t))
  have hae : (fun ω ↦ ENNReal.ofReal (Real.exp (t * X ω))) =ᵐ[μ] 0 :=
    (lintegral_eq_zero_iff' hf).1 hzero
  have hne : ∀ ω, ENNReal.ofReal (Real.exp (t * X ω)) ≠ 0 :=
    fun ω ↦ (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
  have hfalse : ∀ᵐ ω ∂μ, False := hae.mono fun ω hω ↦ hne ω hω
  exact absurd (by simpa using hfalse) (IsProbabilityMeasure.ne_zero μ)

/-- Negating the random variable reflects the extended log MGF. -/
private lemma extendedLogMGF_neg {Ω : Type*} [MeasurableSpace Ω]
    (X : Ω → ℝ) (μ : Measure Ω) (t : ℝ) :
    extendedLogMGF (fun ω ↦ - X ω) μ t = extendedLogMGF X μ (-t) := by
  simp only [extendedLogMGF, mul_neg, neg_mul]

/-- Negating the random variable reflects the Legendre transform. -/
private lemma cramerLegendre_neg {Ω : Type*} [MeasurableSpace Ω]
    (X : Ω → ℝ) (μ : Measure Ω) (x : ℝ) :
    cramerLegendre (fun ω ↦ - X ω) μ x = cramerLegendre X μ (-x) := by
  unfold cramerLegendre
  refine le_antisymm ?_ ?_
  · refine iSup_le fun t ↦ ?_
    rw [extendedLogMGF_neg]
    have hxy : (t * x : ℝ) = (-t) * (-x) := by ring
    rw [hxy]
    exact le_iSup (fun s : ℝ ↦ (s * (-x) : ℝ) - extendedLogMGF X μ s) (-t)
  · refine iSup_le fun t ↦ ?_
    have hneg : extendedLogMGF X μ t =
        extendedLogMGF (fun ω ↦ - X ω) μ (-t) := by
      simpa [neg_neg] using (extendedLogMGF_neg X μ (-t)).symm
    rw [hneg]
    have hxy : (t * (-x) : ℝ) = (-t) * x := by ring
    rw [hxy]
    exact le_iSup
      (fun s : ℝ ↦ (s * x : ℝ) - extendedLogMGF (fun ω ↦ - X ω) μ s) (-t)

/-- Each Legendre slice is continuous in the spatial variable. -/
private lemma continuous_legendreSlice {Ω : Type*} [MeasurableSpace Ω]
    (X : Ω → ℝ) (μ : Measure Ω) (t : ℝ) :
    Continuous fun x : ℝ ↦ (t * x : ℝ) - extendedLogMGF X μ t := by
  by_cases htop : extendedLogMGF X μ t = ⊤
  · have hfun : (fun x : ℝ ↦ (t * x : ℝ) - extendedLogMGF X μ t) = fun _ ↦ ⊥ := by
      ext x
      rw [htop, EReal.sub_top]
    rw [hfun]
    exact continuous_const
  · by_cases hbot : extendedLogMGF X μ t = ⊥
    · have hfun : (fun x : ℝ ↦ (t * x : ℝ) - extendedLogMGF X μ t) = fun _ ↦ ⊤ := by
        ext x
        rw [hbot, EReal.coe_sub_bot]
      rw [hfun]
      exact continuous_const
    · have hcoe : extendedLogMGF X μ t = ↑((extendedLogMGF X μ t).toReal) :=
        (EReal.coe_toReal htop hbot).symm
      have hfun : (fun x : ℝ ↦ (t * x : ℝ) - extendedLogMGF X μ t) =
          fun x : ℝ ↦ ((t * x - (extendedLogMGF X μ t).toReal : ℝ) : EReal) := by
        ext x
        conv_lhs => rw [hcoe]
        rw [← EReal.coe_sub]
      rw [hfun]
      exact continuous_coe_real_ereal.comp
        ((continuous_const_mul t).sub continuous_const)

/-- A strict inequality against `toENNReal` is the same inequality in `EReal`. -/
private lemma lt_toENNReal_iff {y : ℝ≥0∞} {z : EReal} :
    y < z.toENNReal ↔ (y : EReal) < z := by
  rw [← EReal.coe_ennreal_lt_coe_ennreal_iff, EReal.coe_toENNReal_eq_max]
  have hy : (0 : EReal) ≤ (y : EReal) := EReal.coe_ennreal_nonneg y
  rcases le_total (0 : EReal) z with hz | hz
  · rw [max_eq_right hz]
  · rw [max_eq_left hz]
    constructor <;> intro hlt
    · exact absurd hlt (not_lt_of_ge hy)
    · exact absurd hlt (not_lt_of_ge (hz.trans hy))

/-- Cramér's rate is lower semicontinuous for every reference measure. -/
private lemma lowerSemicontinuous_cramerRate {Ω : Type*} [MeasurableSpace Ω]
    (X : Ω → ℝ) (μ : Measure Ω) : LowerSemicontinuous (cramerRate X μ) := by
  have hslice : LowerSemicontinuous fun x : ℝ ↦
      ⨆ t : ℝ, (t * x : ℝ) - extendedLogMGF X μ t :=
    lowerSemicontinuous_iSup fun t ↦ (continuous_legendreSlice X μ t).lowerSemicontinuous
  rw [lowerSemicontinuous_iff_isOpen_preimage]
  intro y
  have hset : cramerRate X μ ⁻¹' Ioi y =
      (fun x : ℝ ↦ ⨆ t : ℝ, (t * x : ℝ) - extendedLogMGF X μ t) ⁻¹' Ioi (y : EReal) := by
    ext x
    simp only [mem_preimage, mem_Ioi, cramerRate]
    exact lt_toENNReal_iff
  rw [hset]
  exact hslice.isOpen_preimage (y : EReal)

/-- On a probability space the Legendre transform is nonnegative. -/
private lemma cramerLegendre_nonneg {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (X : Ω → ℝ) (x : ℝ) : 0 ≤ cramerLegendre X μ x := by
  refine le_iSup_of_le (0 : ℝ) ?_
  simp [extendedLogMGF_zero]

/-- Coercing the Cramér rate recovers the Legendre transform. -/
private lemma coe_cramerRate {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (X : Ω → ℝ) (x : ℝ) :
    (cramerRate X μ x : EReal) = cramerLegendre X μ x := by
  simpa [cramerRate, cramerLegendre] using EReal.coe_toENNReal (cramerLegendre_nonneg X x)

/-- Negation of an indexed supremum is the indexed infimum of the negations. -/
private lemma ereal_neg_iSup {ι : Sort*} (f : ι → EReal) :
    - ⨆ i, f i = ⨅ i, - f i := by
  refine le_antisymm (le_iInf fun i ↦ EReal.neg_strictAnti.antitone (le_iSup f i)) ?_
  rw [← EReal.neg_le_neg_iff, neg_neg]
  refine iSup_le fun i ↦ ?_
  have hi : ⨅ j, - f j ≤ - f i := iInf_le (fun j ↦ - f j) i
  simpa using EReal.neg_strictAnti.antitone hi

/-- A positive scalar distributes over a maximum in `EReal`. -/
private lemma ereal_mul_max {c a b : EReal} (hc : 0 ≤ c) :
    c * max a b = max (c * a) (c * b) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (mul_le_mul_of_nonneg_left h hc)]
  · rw [max_eq_left h, max_eq_left (mul_le_mul_of_nonneg_left h hc)]

/-- Subtraction of a value other than bottom is monotone in the minuend. -/
private lemma ereal_sub_mono_left {c : EReal} (hc : c ≠ ⊥) {a b : ℝ} (hab : a ≤ b) :
    (a : EReal) - c ≤ (b : EReal) - c := by
  by_cases htop : c = ⊤
  · simp [htop, EReal.sub_top]
  · rw [← EReal.coe_toReal htop hc, ← EReal.coe_sub, ← EReal.coe_sub, EReal.coe_le_coe_iff]
    exact sub_le_sub_right hab _

/-- Local exponential moments put zero in the interior of the integrability interval. -/
private lemma zero_mem_interior_integrableExpSet {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X : Ω → ℝ}
    (hexp : ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, |t| < ε →
      Integrable (fun ω ↦ Real.exp (t * X ω)) μ) :
    0 ∈ interior (integrableExpSet X μ) := by
  obtain ⟨ε, hε, hball⟩ := hexp
  rw [mem_interior]
  refine ⟨ball 0 ε, ?_, isOpen_ball, mem_ball_self hε⟩
  intro t ht
  exact hball t (mem_ball_zero_iff.mp ht)

/-- Jensen's inequality gives `t * mean ≤ cgf` whenever the exponential moment exists. -/
private lemma cgf_ge_mul_integral {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : Integrable X μ) {t : ℝ}
    (ht : Integrable (fun ω ↦ Real.exp (t * X ω)) μ) :
    t * ∫ ω, X ω ∂μ ≤ cgf X μ t := by
  have hJ : Real.exp (∫ ω, t * X ω ∂μ) ≤ ∫ ω, Real.exp (t * X ω) ∂μ :=
    convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
      (ae_of_all μ fun _ ↦ trivial) (hX.const_mul t) ht
  rw [integral_const_mul] at hJ
  have hlog := (Real.log_le_log_iff (Real.exp_pos _) (mgf_pos ht)).2 hJ
  simpa [cgf, mgf, Real.log_exp] using hlog

/-- Every Legendre slice at the mean is at most zero. -/
private lemma legendreSlice_mean_le_zero {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (h0 : 0 ∈ interior (integrableExpSet X μ)) (t : ℝ) :
    (t * ∫ ω, X ω ∂μ : ℝ) - extendedLogMGF X μ t ≤ 0 := by
  have hX : Integrable X μ := integrable_of_mem_interior_integrableExpSet h0
  by_cases ht : Integrable (fun ω ↦ Real.exp (t * X ω)) μ
  · rw [extendedLogMGF_eq_coe_cgf ht, ← EReal.coe_sub, ← EReal.coe_zero,
      EReal.coe_le_coe_iff]
    exact sub_nonpos.mpr (cgf_ge_mul_integral hX ht)
  · rw [extendedLogMGF_eq_top hX.aemeasurable ht, EReal.sub_top]
    exact bot_le

/-- The Legendre transform vanishes at the mean. -/
private lemma cramerLegendre_mean_eq_zero {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (h0 : 0 ∈ interior (integrableExpSet X μ)) :
    cramerLegendre X μ (∫ ω, X ω ∂μ) = 0 := by
  apply le_antisymm
  · exact iSup_le fun t ↦ legendreSlice_mean_le_zero h0 t
  · exact cramerLegendre_nonneg X _

/-- For a point above the mean, nonpositive slopes do not increase the Legendre transform. -/
private lemma legendreSlice_le_zero_of_nonpos {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (h0 : 0 ∈ interior (integrableExpSet X μ)) {t x : ℝ} (ht : t ≤ 0)
    (hx : ∫ ω, X ω ∂μ ≤ x) :
    (t * x : ℝ) - extendedLogMGF X μ t ≤ 0 := by
  have hX : Integrable X μ := integrable_of_mem_interior_integrableExpSet h0
  calc
    (t * x : ℝ) - extendedLogMGF X μ t ≤
        (t * ∫ ω, X ω ∂μ : ℝ) - extendedLogMGF X μ t :=
      ereal_sub_mono_left (extendedLogMGF_ne_bot hX.aemeasurable t)
        (mul_le_mul_of_nonpos_left hx ht)
    _ ≤ 0 := legendreSlice_mean_le_zero h0 t

/-- Under a neighborhood of exponential moments, Cramér's rate is good. -/
private lemma isGoodRateFunction_cramerRate {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hexp : ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, |t| < ε →
      Integrable (fun ω ↦ Real.exp (t * X ω)) μ) :
    IsGoodRateFunction (cramerRate X μ) := by
  refine ⟨lowerSemicontinuous_cramerRate X μ, fun a ↦ ?_⟩
  obtain ⟨ε, hεpos, hε⟩ := hexp
  let tpos : ℝ := ε / 2
  have htpos : 0 < tpos := by positivity
  have hmem : |tpos| < ε := by
    rw [abs_of_pos htpos]
    exact half_lt_self hεpos
  have hmemn : |-tpos| < ε := by simpa [abs_neg] using hmem
  have hint : Integrable (fun ω ↦ Real.exp (tpos * X ω)) μ := hε _ hmem
  have hintn : Integrable (fun ω ↦ Real.exp ((-tpos) * X ω)) μ := hε _ hmemn
  let cpos : ℝ := cgf X μ tpos
  let cneg : ℝ := cgf X μ (-tpos)
  let Bpos : ℝ := (cpos + (a : ℝ) + 1) / tpos
  let Bneg : ℝ := - (cneg + (a : ℝ) + 1) / tpos
  have hclosed : IsClosed {x | cramerRate X μ x ≤ a} := by
    rw [← isOpen_compl_iff]
    have hcompl : {x | cramerRate X μ x ≤ a}ᶜ = cramerRate X μ ⁻¹' Ioi (a : ℝ≥0∞) := by
      ext x
      simp only [mem_compl_iff, mem_ofPred_eq, mem_preimage, mem_Ioi, not_le]
    rw [hcompl]
    exact (lowerSemicontinuous_iff_isOpen_preimage.mp
      (lowerSemicontinuous_cramerRate X μ)) (a : ℝ≥0∞)
  have hge (t c : ℝ) (ht : extendedLogMGF X μ t = ↑c) (x : ℝ) :
      ENNReal.ofReal (t * x - c) ≤ cramerRate X μ x := by
    rw [cramerRate, ← EReal.real_coe_toENNReal]
    refine EReal.toENNReal_le_toENNReal ?_
    rw [EReal.coe_sub, ← ht]
    exact le_iSup (fun s : ℝ ↦ (s * x : ℝ) - extendedLogMGF X μ s) t
  have hBpos : tpos * Bpos - cpos = (a : ℝ) + 1 := by
    simp only [Bpos]
    field_simp [htpos.ne']
    ring
  have hBneg : (-tpos) * Bneg - cneg = (a : ℝ) + 1 := by
    simp only [Bneg]
    field_simp [htpos.ne']
    ring
  have hsub : {x | cramerRate X μ x ≤ a} ⊆ Icc Bneg Bpos := by
    intro x hx
    refine ⟨?_, ?_⟩
    · by_contra hlt
      push Not at hlt
      have hlin : (a : ℝ) < (-tpos) * x - cneg := by nlinarith [hBneg, hlt]
      have hle : ENNReal.ofReal ((-tpos) * x - cneg) ≤ (a : ℝ≥0∞) :=
        (hge (-tpos) cneg (extendedLogMGF_eq_coe_cgf hintn) x).trans hx
      rw [ENNReal.ofReal_le_iff_le_toReal ENNReal.coe_ne_top, ENNReal.coe_toReal] at hle
      linarith
    · by_contra hgt
      push Not at hgt
      have hlin : (a : ℝ) < tpos * x - cpos := by nlinarith [hBpos, hgt]
      have hle : ENNReal.ofReal (tpos * x - cpos) ≤ (a : ℝ≥0∞) :=
        (hge tpos cpos (extendedLogMGF_eq_coe_cgf hint) x).trans hx
      rw [ENNReal.ofReal_le_iff_le_toReal ENNReal.coe_ne_top, ENNReal.coe_toReal] at hle
      linarith
  exact IsCompact.of_isClosed_subset isCompact_Icc hclosed hsub

/-- Partial sums of measurable real random variables are measurable. -/
private lemma measurable_partialSum {Ω : Type*} [MeasurableSpace Ω]
    {X : ℕ → Ω → ℝ} (hm : ∀ n, Measurable (X n)) (n : ℕ) :
    Measurable (fun ω ↦ ∑ j ∈ Finset.range n, X j ω) := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    have hfun : (fun ω ↦ ∑ j ∈ Finset.range (n + 1), X j ω) =
        (fun ω ↦ ∑ j ∈ Finset.range n, X j ω) + X n := by
      ext ω
      simp [Finset.sum_range_succ]
    rw [hfun]
    exact ih.add (hm n)

/-- The empirical-mean map is measurable. -/
private lemma measurable_sampleMean {Ω : Type*} [MeasurableSpace Ω]
    {X : ℕ → Ω → ℝ} (hm : ∀ n, Measurable (X n)) (n : ℕ) :
    Measurable (fun ω ↦ (n + 1 : ℝ)⁻¹ * ∑ j ∈ Finset.range (n + 1), X j ω) :=
  (measurable_partialSum hm (n + 1)).const_mul _

/-- Negating every coordinate negates the empirical-mean laws. -/
private lemma sampleMeanLaws_neg {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : ℕ → Ω → ℝ} (hm : ∀ n, Measurable (X n)) (n : ℕ) :
    sampleMeanLaws (fun i ω ↦ - X i ω) μ n =
      (sampleMeanLaws X μ n).map (fun y : ℝ ↦ - y) := by
  simp only [sampleMeanLaws]
  rw [Measure.map_map measurable_neg (measurable_sampleMean hm n)]
  congr 1
  ext ω
  simp [Function.comp_apply, Finset.sum_neg_distrib, mul_neg]

/-- Laws of empirical means are probability measures. -/
private instance isProbabilityMeasure_sampleMeanLaws {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ} (n : ℕ) :
    IsProbabilityMeasure (sampleMeanLaws X μ n) := by
  unfold sampleMeanLaws
  infer_instance

/-- Logarithmic rate of a probability bounded by an exponential. -/
private lemma logProbabilityRate_le_of_exp_bound {P : Measure ℝ} [IsProbabilityMeasure P]
    {s : Set ℝ} {n : ℕ} {b : ℝ}
    (hb : P.real s ≤ Real.exp ((n + 1 : ℝ) * b)) :
    (((n + 1 : ℝ)⁻¹ : ℝ) : EReal) * ENNReal.log (P s) ≤ (b : EReal) := by
  by_cases h0 : P s = 0
  · simp [h0, ENNReal.log_zero, EReal.coe_mul_bot_of_pos
      (inv_pos.mpr (by positivity : (0 : ℝ) < (n + 1 : ℝ)))]
  · have hfin : P s ≠ ⊤ := measure_ne_top P s
    have hpos : 0 < P.real s := by
      rw [measureReal_def]
      exact ENNReal.toReal_pos h0 hfin
    have hle1 : P.real s ≤ 1 := by
      rw [measureReal_def]
      refine ENNReal.toReal_le_of_le_ofReal zero_le_one ?_
      calc
        P s ≤ P Set.univ := measure_mono (subset_univ s)
        _ = 1 := measure_univ
        _ = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
    have hlog : Real.log (P.real s) ≤ (n + 1) * b := by
      by_cases hb0 : 0 ≤ b
      · exact (Real.log_nonpos hpos.le hle1).trans (mul_nonneg (by positivity) hb0)
      · have hlogle := (Real.log_le_log_iff hpos (Real.exp_pos _)).2 hb
        simpa [Real.log_exp] using hlogle
    rw [measureReal_def] at hlog
    rw [ENNReal.log_pos_real h0 hfin, ← EReal.coe_mul]
    exact EReal.coe_le_coe_iff.mpr
      ((inv_mul_le_iff₀ (by positivity : (0 : ℝ) < (n + 1 : ℝ))).mpr hlog)

/-- Logarithmic probability rates are nonpositive. -/
private lemma logProbabilityRate_le_zero {P : ℕ → Measure ℝ}
    [∀ n, IsProbabilityMeasure (P n)] (s : Set ℝ) (n : ℕ) :
    logProbabilityRate P s n ≤ 0 := by
  have hlog : ENNReal.log (P n s) ≤ 0 := by
    rw [ENNReal.log_le_zero_iff]
    exact (measure_mono (subset_univ s)).trans_eq measure_univ
  have hc : (0 : EReal) ≤ ((n + 1 : ℝ)⁻¹) :=
    EReal.coe_le_coe_iff.mpr (inv_nonneg.2 (by positivity))
  simpa [logProbabilityRate, mul_zero] using mul_le_mul_of_nonneg_left hlog hc

/-- Logarithmic rates increase with the set. -/
private lemma logProbabilityRate_mono {P : ℕ → Measure ℝ} {A B : Set ℝ}
    (hAB : A ⊆ B) (n : ℕ) : logProbabilityRate P A n ≤ logProbabilityRate P B n := by
  have hc : (0 : EReal) ≤ ((n + 1 : ℝ)⁻¹) :=
    EReal.coe_le_coe_iff.mpr (inv_nonneg.2 (by positivity))
  simpa [logProbabilityRate] using
    mul_le_mul_of_nonneg_left (ENNReal.log_monotone (measure_mono hAB)) hc

/-- The normalized logarithm of a union is controlled by the larger summand. -/
private lemma logProbabilityRate_union_le {P : ℕ → Measure ℝ}
    [∀ n, IsProbabilityMeasure (P n)] (A B : Set ℝ) (n : ℕ) :
    logProbabilityRate P (A ∪ B) n ≤
      ↑((n + 1 : ℝ)⁻¹ * Real.log 2) +
        max (logProbabilityRate P A n) (logProbabilityRate P B n) := by
  have hμ : P n (A ∪ B) ≤ 2 * max (P n A) (P n B) := by
    calc
      P n (A ∪ B) ≤ P n A + P n B := measure_union_le A B
      _ ≤ max (P n A) (P n B) + max (P n A) (P n B) :=
        add_le_add (le_max_left _ _) (le_max_right _ _)
      _ = 2 * max (P n A) (P n B) := by rw [two_mul]
  have hlog2 : ENNReal.log (2 : ℝ≥0∞) = ↑(Real.log 2) := by
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num, ENNReal.log_ofReal_of_pos
      (by norm_num : (0 : ℝ) < 2)]
  have hlog : ENNReal.log (P n (A ∪ B)) ≤
      ↑(Real.log 2) + max (ENNReal.log (P n A)) (ENNReal.log (P n B)) := by
    calc
      ENNReal.log (P n (A ∪ B)) ≤ ENNReal.log (2 * max (P n A) (P n B)) :=
        ENNReal.log_monotone hμ
      _ = ENNReal.log 2 + ENNReal.log (max (P n A) (P n B)) := ENNReal.log_mul_add
      _ = ↑(Real.log 2) + max (ENNReal.log (P n A)) (ENNReal.log (P n B)) := by
        rw [hlog2, Monotone.map_max ENNReal.log_monotone]
  have hc0 : (0 : ℝ) < ((n + 1 : ℝ)⁻¹) := by positivity
  have hc : (0 : EReal) ≤ ((n + 1 : ℝ)⁻¹) := EReal.coe_le_coe_iff.mpr hc0.le
  have hcne : ((n + 1 : ℝ)⁻¹ : EReal) ≠ ⊤ := EReal.coe_ne_top _
  rw [logProbabilityRate, logProbabilityRate, logProbabilityRate]
  calc
    (((n + 1 : ℝ)⁻¹ : ℝ) : EReal) * ENNReal.log (P n (A ∪ B)) ≤
        (((n + 1 : ℝ)⁻¹ : ℝ) : EReal) *
          (↑(Real.log 2) + max (ENNReal.log (P n A)) (ENNReal.log (P n B))) :=
      mul_le_mul_of_nonneg_left hlog hc
    _ = ↑((n + 1 : ℝ)⁻¹ * Real.log 2) +
          max (logProbabilityRate P A n) (logProbabilityRate P B n) := by
      rw [EReal.left_distrib_of_nonneg_of_ne_top hc hcne, ← EReal.coe_mul, ereal_mul_max hc,
        logProbabilityRate, logProbabilityRate]

/-- The vanishing speed factor does not raise the limsup of a union. -/
private lemma limsup_logProbabilityRate_union_le {P : ℕ → Measure ℝ}
    [∀ n, IsProbabilityMeasure (P n)] (A B : Set ℝ) :
    limsup (logProbabilityRate P (A ∪ B)) atTop ≤
      max (limsup (logProbabilityRate P A) atTop)
        (limsup (logProbabilityRate P B) atTop) := by
  let α : ℕ → EReal := fun n ↦ ↑((n + 1 : ℝ)⁻¹ * Real.log 2)
  let φ : ℕ → EReal := fun n ↦ max (logProbabilityRate P A n) (logProbabilityRate P B n)
  have htend : Tendsto (fun n : ℕ ↦ (n + 1 : ℝ)⁻¹ * Real.log 2) atTop (𝓝 0) := by
    have hinv : Tendsto (fun n : ℕ ↦ (n + 1 : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp
        (tendsto_atTop_add_const_right _ (1 : ℝ) tendsto_natCast_atTop_atTop)
    simpa [mul_zero] using hinv.mul_const (Real.log 2)
  have hlimsupα : limsup α atTop = 0 := (EReal.tendsto_coe.2 htend).limsup_eq
  have hle : ∀ n, logProbabilityRate P (A ∪ B) n ≤ α n + φ n :=
    fun n ↦ logProbabilityRate_union_le A B n
  have hadd : limsup (fun n ↦ α n + φ n) atTop ≤ limsup α atTop + limsup φ atTop :=
    EReal.limsup_add_le (.inl (by simp [hlimsupα]))
      (.inl (by simp [hlimsupα]))
  calc
    limsup (logProbabilityRate P (A ∪ B)) atTop ≤ limsup (fun n ↦ α n + φ n) atTop :=
      limsup_le_limsup (Eventually.of_forall hle)
    _ ≤ limsup α atTop + limsup φ atTop := hadd
    _ = max (limsup (logProbabilityRate P A) atTop)
          (limsup (logProbabilityRate P B) atTop) := by
      rw [hlimsupα, zero_add, limsup_max]

/-- Chernoff's bound on the upper tail of the empirical mean. -/
private lemma logProbabilityRate_Ici_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ} (hm : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hid : ∀ n, IdentDistrib (X n) (X 0) μ μ)
    {t x : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    logProbabilityRate (sampleMeanLaws X μ) (Ici x) n ≤
      - ((t * x : ℝ) - extendedLogMGF (X 0) μ t) := by
  by_cases hint : Integrable (fun ω ↦ Real.exp (t * X 0 ω)) μ
  · have hintj : ∀ j ∈ Finset.range (n + 1),
        Integrable (fun ω ↦ Real.exp (t * X j ω)) μ := by
      intro j hj
      exact (((hid j).comp ((measurable_const_mul t).exp)).integrable_iff).mpr hint
    let S : Ω → ℝ := ∑ j ∈ Finset.range (n + 1), X j
    have hSint : Integrable (fun ω ↦ Real.exp (t * S ω)) μ :=
      hi.integrable_exp_mul_sum hm hintj
    have hcgf : cgf S μ t = (n + 1 : ℝ) * cgf (X 0) μ t := by
      rw [hi.cgf_sum hm hintj]
      have hsame : ∀ j ∈ Finset.range (n + 1), cgf (X j) μ t = cgf (X 0) μ t := by
        intro j hj
        simp [cgf, mgf_congr_of_identDistrib (X j) (X 0) (hid j) t]
      rw [Finset.sum_congr rfl hsame, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      norm_cast
    have hch := measure_ge_le_exp_cgf (X := S) ((n + 1 : ℝ) * x) ht hSint
    have hset : (fun ω ↦ (n + 1 : ℝ)⁻¹ * S ω) ⁻¹' Ici x =
        {ω | (n + 1 : ℝ) * x ≤ S ω} := by
      ext ω
      simp only [mem_preimage, mem_Ici, mem_ofPred_eq]
      rw [← mul_le_mul_iff_of_pos_left (by positivity : (0 : ℝ) < (n + 1 : ℝ)),
        ← mul_assoc, mul_inv_cancel₀ (by positivity : (n + 1 : ℝ) ≠ 0), one_mul]
    have hreal : (sampleMeanLaws X μ n).real (Ici x) ≤
        Real.exp ((n + 1 : ℝ) * (-t * x + cgf (X 0) μ t)) := by
      calc
        (sampleMeanLaws X μ n).real (Ici x) =
            μ.real ((fun ω ↦ (n + 1 : ℝ)⁻¹ * S ω) ⁻¹' Ici x) := by
          rw [sampleMeanLaws, measureReal_def, Measure.map_apply_of_aemeasurable
            (measurable_sampleMean hm n).aemeasurable measurableSet_Ici, measureReal_def]
          simp [S, Finset.sum_apply]
        _ = μ.real {ω | (n + 1 : ℝ) * x ≤ S ω} := by rw [hset]
        _ ≤ Real.exp (-t * ((n + 1 : ℝ) * x) + cgf S μ t) := hch
        _ = Real.exp ((n + 1 : ℝ) * (-t * x + cgf (X 0) μ t)) := by
          congr 1
          rw [hcgf]
          ring
    have hb := logProbabilityRate_le_of_exp_bound (P := sampleMeanLaws X μ n) hreal
    rw [logProbabilityRate]
    exact hb.trans <| by
      rw [extendedLogMGF_eq_coe_cgf hint, ← EReal.coe_sub, ← EReal.coe_neg]
      exact EReal.coe_le_coe_iff.mpr (le_of_eq (by ring))
  · rw [extendedLogMGF_eq_top (hm 0).aemeasurable hint, EReal.sub_top, EReal.neg_bot]
    exact le_top

/-- Upper-tail logarithmic rates sit under the negative Legendre transform. -/
private lemma limsup_Ici_le_neg_legendre {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ} (hm : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hid : ∀ n, IdentDistrib (X n) (X 0) μ μ)
    (h0 : 0 ∈ interior (integrableExpSet (X 0) μ)) {x : ℝ}
    (hx : ∫ ω, X 0 ω ∂μ ≤ x) :
    limsup (logProbabilityRate (sampleMeanLaws X μ) (Ici x)) atTop ≤
      - cramerLegendre (X 0) μ x := by
  let slice : ℝ → EReal := fun t ↦ (t * x : ℝ) - extendedLogMGF (X 0) μ t
  have hpt : ∀ t : ℝ, 0 ≤ t →
      limsup (logProbabilityRate (sampleMeanLaws X μ) (Ici x)) atTop ≤ - slice t := by
    intro t ht
    exact limsup_le_of_le (h := Eventually.of_forall fun n ↦
      logProbabilityRate_Ici_le hm hi hid ht n)
  have hsup : cramerLegendre (X 0) μ x = ⨆ s : {t : ℝ // 0 ≤ t}, slice s := by
    refine le_antisymm ?_ ?_
    · refine iSup_le fun t ↦ ?_
      by_cases ht : 0 ≤ t
      · exact le_iSup (fun s : {t : ℝ // 0 ≤ t} ↦ slice s) ⟨t, ht⟩
      · have hle0 : slice t ≤ 0 :=
          legendreSlice_le_zero_of_nonpos h0 (le_of_lt (lt_of_not_ge ht)) hx
        have h0le : (0 : EReal) ≤ ⨆ s : {t : ℝ // 0 ≤ t}, slice s := by
          refine le_iSup_of_le (⟨0, le_rfl⟩ : {t : ℝ // 0 ≤ t}) ?_
          simp [slice, extendedLogMGF_zero]
        exact hle0.trans h0le
    · exact iSup_le fun s ↦ le_iSup slice s.1
  rw [hsup, ereal_neg_iSup]
  exact le_iInf fun s ↦ hpt s.1 s.2

/-- Logarithmic rates of lower and upper tails agree after negating the variables. -/
private lemma logProbabilityRate_Iic_eq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : ℕ → Ω → ℝ} (hm : ∀ n, Measurable (X n)) (x : ℝ) (n : ℕ) :
    logProbabilityRate (sampleMeanLaws X μ) (Iic x) n =
      logProbabilityRate (sampleMeanLaws (fun i ω ↦ - X i ω) μ) (Ici (-x)) n := by
  rw [logProbabilityRate, logProbabilityRate, sampleMeanLaws_neg hm n,
    Measure.map_apply measurable_neg measurableSet_Ici]
  have hset : (fun y : ℝ ↦ - y) ⁻¹' Ici (-x) = Iic x := by
    ext y
    simp
  rw [hset]

/-- Lower-tail logarithmic rates sit under the negative Legendre transform. -/
private lemma limsup_Iic_le_neg_legendre {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ} (hm : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hid : ∀ n, IdentDistrib (X n) (X 0) μ μ)
    (hexp : ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, |t| < ε →
      Integrable (fun ω ↦ Real.exp (t * X 0 ω)) μ) {x : ℝ}
    (hx : x ≤ ∫ ω, X 0 ω ∂μ) :
    limsup (logProbabilityRate (sampleMeanLaws X μ) (Iic x)) atTop ≤
      - cramerLegendre (X 0) μ x := by
  let Y : ℕ → Ω → ℝ := fun i ω ↦ - X i ω
  have hiY : iIndepFun Y μ := hi.comp (fun _ ↦ Neg.neg) (fun _ ↦ measurable_neg)
  have hidY : ∀ n, IdentDistrib (Y n) (Y 0) μ μ := fun n ↦ (hid n).comp measurable_neg
  have hexpY : ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, |t| < ε →
      Integrable (fun ω ↦ Real.exp (t * Y 0 ω)) μ := by
    obtain ⟨ε, hε, h⟩ := hexp
    refine ⟨ε, hε, fun t ht ↦ ?_⟩
    simpa [Y, mul_neg, neg_mul] using h (-t) (by rwa [abs_neg])
  have h0 : 0 ∈ interior (integrableExpSet (Y 0) μ) :=
    zero_mem_interior_integrableExpSet hexpY
  have hX : Integrable (X 0) μ :=
    integrable_of_mem_interior_integrableExpSet (zero_mem_interior_integrableExpSet hexp)
  have hmean : ∫ ω, Y 0 ω ∂μ ≤ -x := by
    rw [show Y 0 = fun ω ↦ - X 0 ω from rfl, integral_neg (X 0)]
    exact neg_le_neg hx
  have hlimsup := limsup_Ici_le_neg_legendre (X := Y) (fun n ↦ (hm n).neg) hiY hidY h0 hmean
  have heq : logProbabilityRate (sampleMeanLaws Y μ) (Ici (-x)) =
      logProbabilityRate (sampleMeanLaws X μ) (Iic x) := by
    ext n
    exact (logProbabilityRate_Iic_eq hm x n).symm
  have hleg : cramerLegendre (Y 0) μ (-x) = cramerLegendre (X 0) μ x := by
    simpa [Y, neg_neg] using cramerLegendre_neg (X 0) μ (-x)
  simpa [heq, hleg] using hlimsup

/-- Closed sets obey the large-deviation upper bound at speed `n + 1`. -/
private lemma limsup_closed_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ} (hm : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hid : ∀ n, IdentDistrib (X n) (X 0) μ μ)
    (hexp : ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, |t| < ε →
      Integrable (fun ω ↦ Real.exp (t * X 0 ω)) μ) {F : Set ℝ} (hF : IsClosed F) :
    limsup (logProbabilityRate (sampleMeanLaws X μ) F) atTop ≤
      - ⨅ x ∈ F, (cramerRate (X 0) μ x : EReal) := by
  have hcoe : ∀ x, (cramerRate (X 0) μ x : EReal) = cramerLegendre (X 0) μ x :=
    fun x ↦ coe_cramerRate (X 0) x
  simp_rw [hcoe]
  by_cases hne : F.Nonempty
  · let mean : ℝ := ∫ ω, X 0 ω ∂μ
    have h0 : 0 ∈ interior (integrableExpSet (X 0) μ) :=
      zero_mem_interior_integrableExpSet hexp
    have hmean0 : cramerLegendre (X 0) μ mean = 0 := cramerLegendre_mean_eq_zero h0
    let c : EReal := ⨅ x ∈ F, cramerLegendre (X 0) μ x
    have hc0 : 0 ≤ c := le_iInf fun x ↦ le_iInf fun _ ↦ cramerLegendre_nonneg (X 0) x
    by_cases hcle : c ≤ 0
    · have hc : c = 0 := le_antisymm hcle hc0
      have hnonpos : limsup (logProbabilityRate (sampleMeanLaws X μ) F) atTop ≤ 0 :=
        limsup_le_of_le (h := Eventually.of_forall fun n ↦
          logProbabilityRate_le_zero (P := sampleMeanLaws X μ) F n)
      simpa [c, hc] using hnonpos
    · have hcpos : 0 < c := lt_of_not_ge hcle
      have hmeanF : mean ∉ F := by
        intro hmem
        have : c ≤ cramerLegendre (X 0) μ mean :=
          le_trans (iInf_le _ mean) (iInf_le (fun _ : mean ∈ F ↦ cramerLegendre (X 0) μ mean) hmem)
        rw [hmean0] at this
        exact (not_lt_of_ge this) hcpos
      let left : Set ℝ := F ∩ Iic mean
      let right : Set ℝ := F ∩ Ici mean
      have hleftClosed : IsClosed left := hF.inter isClosed_Iic
      have hrightClosed : IsClosed right := hF.inter isClosed_Ici
      by_cases hL : left.Nonempty
      · by_cases hR : right.Nonempty
        · let xMinus : ℝ := sSup left
          let xPlus : ℝ := sInf right
          have hxMinus_mem : xMinus ∈ left :=
            hleftClosed.csSup_mem hL (bddAbove_Iic.mono inter_subset_right)
          have hxPlus_mem : xPlus ∈ right :=
            hrightClosed.csInf_mem hR (bddBelow_Ici.mono inter_subset_right)
          have hxMinus_le : xMinus ≤ mean := hxMinus_mem.2
          have hxPlus_ge : mean ≤ xPlus := hxPlus_mem.2
          have hcover : F ⊆ Iic xMinus ∪ Ici xPlus := by
            intro y hy
            rcases le_total y mean with hyL | hyR
            · exact Or.inl (le_csSup (bddAbove_Iic.mono inter_subset_right) ⟨hy, hyL⟩)
            · exact Or.inr (csInf_le (bddBelow_Ici.mono inter_subset_right) ⟨hy, hyR⟩)
          have hIic := limsup_Iic_le_neg_legendre hm hi hid hexp hxMinus_le
          have hIci := limsup_Ici_le_neg_legendre hm hi hid h0 hxPlus_ge
          have hunion := limsup_logProbabilityRate_union_le
            (P := sampleMeanLaws X μ) (Iic xMinus) (Ici xPlus)
          have hmono : limsup (logProbabilityRate (sampleMeanLaws X μ) F) atTop ≤
              limsup (logProbabilityRate (sampleMeanLaws X μ) (Iic xMinus ∪ Ici xPlus)) atTop :=
            limsup_le_limsup (Eventually.of_forall fun n ↦
              logProbabilityRate_mono hcover n)
          have hcMinus : c ≤ cramerLegendre (X 0) μ xMinus :=
            le_trans (iInf_le _ xMinus)
              (iInf_le (fun _ : xMinus ∈ F ↦ cramerLegendre (X 0) μ xMinus) hxMinus_mem.1)
          have hcPlus : c ≤ cramerLegendre (X 0) μ xPlus :=
            le_trans (iInf_le _ xPlus)
              (iInf_le (fun _ : xPlus ∈ F ↦ cramerLegendre (X 0) μ xPlus) hxPlus_mem.1)
          calc
            limsup (logProbabilityRate (sampleMeanLaws X μ) F) atTop ≤
                max (limsup (logProbabilityRate (sampleMeanLaws X μ) (Iic xMinus)) atTop)
                  (limsup (logProbabilityRate (sampleMeanLaws X μ) (Ici xPlus)) atTop) :=
              hmono.trans hunion
            _ ≤ max (- cramerLegendre (X 0) μ xMinus)
                (- cramerLegendre (X 0) μ xPlus) :=
              max_le_max hIic hIci
            _ ≤ - c :=
              max_le (EReal.neg_strictAnti.antitone hcMinus)
                (EReal.neg_strictAnti.antitone hcPlus)
        · have hFsub : F ⊆ Iic mean := by
            intro y hy
            rcases le_or_gt y mean with hle | hgt
            · exact hle
            · exact False.elim (hR ⟨y, hy, le_of_lt hgt⟩)
          let xMinus : ℝ := sSup F
          have hxmem : xMinus ∈ F := hF.csSup_mem hne (bddAbove_Iic.mono hFsub)
          have hxle : xMinus ≤ mean := csSup_le hne fun y hy ↦ hFsub hy
          have hcover : F ⊆ Iic xMinus := fun y hy ↦
            le_csSup (bddAbove_Iic.mono hFsub) hy
          have hmono : limsup (logProbabilityRate (sampleMeanLaws X μ) F) atTop ≤
              limsup (logProbabilityRate (sampleMeanLaws X μ) (Iic xMinus)) atTop :=
            limsup_le_limsup (Eventually.of_forall fun n ↦ logProbabilityRate_mono hcover n)
          have htail := limsup_Iic_le_neg_legendre hm hi hid hexp hxle
          have hcle : c ≤ cramerLegendre (X 0) μ xMinus :=
            le_trans (iInf_le _ xMinus)
              (iInf_le (fun _ : xMinus ∈ F ↦ cramerLegendre (X 0) μ xMinus) hxmem)
          exact hmono.trans (htail.trans (EReal.neg_strictAnti.antitone hcle))
      · have hFsub : F ⊆ Ici mean := by
          intro y hy
          rcases le_or_gt y mean with hle | hgt
          · exact False.elim (hL ⟨y, hy, hle⟩)
          · exact le_of_lt hgt
        let xPlus : ℝ := sInf F
        have hxmem : xPlus ∈ F := hF.csInf_mem hne (bddBelow_Ici.mono hFsub)
        have hxge : mean ≤ xPlus := le_csInf hne fun y hy ↦ hFsub hy
        have hcover : F ⊆ Ici xPlus := fun y hy ↦
          csInf_le (bddBelow_Ici.mono hFsub) hy
        have hmono : limsup (logProbabilityRate (sampleMeanLaws X μ) F) atTop ≤
            limsup (logProbabilityRate (sampleMeanLaws X μ) (Ici xPlus)) atTop :=
          limsup_le_limsup (Eventually.of_forall fun n ↦ logProbabilityRate_mono hcover n)
        have htail := limsup_Ici_le_neg_legendre hm hi hid h0 hxge
        have hcle : c ≤ cramerLegendre (X 0) μ xPlus :=
          le_trans (iInf_le _ xPlus)
            (iInf_le (fun _ : xPlus ∈ F ↦ cramerLegendre (X 0) μ xPlus) hxmem)
        exact hmono.trans (htail.trans (EReal.neg_strictAnti.antitone hcle))
  · have hFempty : F = ∅ := not_nonempty_iff_eq_empty.mp hne
    have hrate : logProbabilityRate (sampleMeanLaws X μ) F = fun _ ↦ ⊥ := by
      ext n
      simp [hFempty, logProbabilityRate, measure_empty, ENNReal.log_zero,
        EReal.coe_mul_bot_of_pos (inv_pos.mpr (by positivity : (0 : ℝ) < (n + 1 : ℝ)))]
    have hinf : (⨅ x ∈ F, cramerLegendre (X 0) μ x) = ⊤ := by
      rw [hFempty]
      simp
    simp [hrate, hinf, EReal.neg_top]

/-- **06.60**: Cramer's theorem with the actual extended-log-MGF conjugate as good rate. -/
theorem cramer {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hm : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hid : ∀ n, IdentDistrib (X n) (X 0) μ μ)
    (hexp : ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, |t| < ε →
      Integrable (fun ω ↦ Real.exp (t * X 0 ω)) μ) :
    IsGoodRateFunction (cramerRate (X 0) μ) ∧
      HasLargeDeviationPrinciple (sampleMeanLaws X μ) (cramerRate (X 0) μ) := by
  refine ⟨isGoodRateFunction_cramerRate hexp, ?_⟩
  unfold HasLargeDeviationPrinciple
  refine ⟨?_, ?_⟩
  · sorry
  · intro F hF
    exact limsup_closed_le hm hi hid hexp hF

/-- The empirical probability measure, reusing TauCeti's finite-population construction. -/
def empiricalProbability {Ω E : Type*} [MeasurableSpace E]
    (X : ℕ → Ω → E) (n : ℕ) (ω : Ω) : ProbabilityMeasure E :=
  TauCeti.Probability.empiricalMeasureOfFintype (fun i : Fin (n + 1) ↦ X i ω)

/-- Sanov's entropy rate, using Mathlib's relative entropy of probability measures. -/
def sanovRate {E : Type*} [MeasurableSpace E] (P : ProbabilityMeasure E)
    (ν : ProbabilityMeasure E) : ℝ≥0∞ := InformationTheory.klDiv ν.toMeasure P.toMeasure

/-- Relative entropy is a good rate on a Polish Borel space. -/
private lemma isGoodRateFunction_sanovRate {E : Type*} [TopologicalSpace E] [PolishSpace E]
    [MeasurableSpace E] [BorelSpace E] (P : ProbabilityMeasure E) :
    IsGoodRateFunction (sanovRate P) := by
  have hlsc : LowerSemicontinuous (sanovRate P) := by
    unfold sanovRate
    exact (TauCeti.lowerSemicontinuous_klDiv_probabilityMeasure (α := E)).comp
      (continuous_id.prodMk continuous_const)
  refine ⟨hlsc, fun a ↦ ?_⟩
  let S : Set (ProbabilityMeasure E) := {ν | sanovRate P ν ≤ (a : ℝ≥0∞)}
  have hclosed : IsClosed S := by
    simpa [S, Set.preimage, Set.mem_Iic] using hlsc.isClosed_preimage (a : ℝ≥0∞)
  have hsing : IsTightMeasureSet ({(P : Measure E)} : Set (Measure E)) :=
    isTightMeasureSet_singleton
  have hent : IsTightMeasureSet
      {μ : Measure E | IsFiniteMeasure μ ∧
        InformationTheory.klDiv μ (P : Measure E) ≤ (a : ℝ≥0∞)} :=
    TauCeti.isTightMeasureSet_setOf_klDiv_le hsing ENNReal.coe_ne_top
  have hsub : {((ν : ProbabilityMeasure E) : Measure E) | ν ∈ S} ⊆
      {μ : Measure E | IsFiniteMeasure μ ∧
        InformationTheory.klDiv μ (P : Measure E) ≤ (a : ℝ≥0∞)} := by
    intro μ hμ
    simp only [mem_ofPred_eq] at hμ ⊢
    obtain ⟨ν, hν, rfl⟩ := hμ
    exact ⟨inferInstance, by simpa [S, sanovRate] using hν⟩
  have htight : IsTightMeasureSet {((ν : ProbabilityMeasure E) : Measure E) | ν ∈ S} :=
    IsTightMeasureSet.subset hent hsub
  have hcomp : IsCompact (closure S) := isCompact_closure_of_isTightMeasureSet htight
  rw [hclosed.closure_eq] at hcomp
  simpa [S] using hcomp

/-- **06.61**: Sanov's theorem on a Polish space in the weak topology of probability measures. -/
theorem sanov {Ω E : Type*} [MeasurableSpace Ω] [TopologicalSpace E]
    [PolishSpace E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : ProbabilityMeasure E)
    (X : ℕ → Ω → E) (hm : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hlaw : ∀ n, μ.map (X n) = P.toMeasure) :
    IsGoodRateFunction (sanovRate P) ∧
      HasLargeDeviationPrinciple (fun n ↦ μ.map (empiricalProbability X n)) (sanovRate P) := by
  refine ⟨isGoodRateFunction_sanovRate P, ?_⟩
  sorry

end CKMA
