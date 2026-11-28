/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Probability.LargeDeviations.Basic
public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.Probability.Independence.Basic
public import TauCeti.Probability.Process.EmpiricalMeasure

import Mathlib.MeasureTheory.Measure.Prokhorov
import TauCeti.InformationTheory.KullbackLeibler.Variational

/-!
# Sanov's theorem (06.61)

Sanov's theorem is formulated in the weak topology of probability measures on a Polish
space. Empirical measures reuse the Tau Ceti contributors' finite-population construction
in `TauCeti.Probability.Process.EmpiricalMeasure`; the rate is Mathlib's relative entropy
`InformationTheory.klDiv`, a good rate function by TauCeti's lower semicontinuity and
tightness of its sublevels.

## Main definitions

* `CKMA.empiricalProbability`: empirical measure of the first `n + 1` observations.
* `CKMA.sanovRate`: Sanov's rate, the relative entropy with respect to the sampling law.

## Main results

* `CKMA.sanov`: Sanov's large deviation theorem for empirical measures (**06.61**).
-/

public section

noncomputable section

namespace CKMA

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

/-- The empirical probability measure, reusing TauCeti's finite-population construction. -/
@[expose]
def empiricalProbability {Ω E : Type*} [MeasurableSpace E]
    (X : ℕ → Ω → E) (n : ℕ) (ω : Ω) : ProbabilityMeasure E :=
  TauCeti.Probability.empiricalMeasureOfFintype (fun i : Fin (n + 1) ↦ X i ω)

/-- Defining formula of `empiricalProbability`. -/
lemma empiricalProbability_def {Ω E : Type*} [MeasurableSpace E] (X : ℕ → Ω → E) (n : ℕ)
    (ω : Ω) :
    empiricalProbability X n ω =
      TauCeti.Probability.empiricalMeasureOfFintype (fun i : Fin (n + 1) ↦ X i ω) :=
  rfl

/-- Sanov's entropy rate, using Mathlib's relative entropy of probability measures. -/
@[expose]
def sanovRate {E : Type*} [MeasurableSpace E] (P : ProbabilityMeasure E)
    (ν : ProbabilityMeasure E) : ℝ≥0∞ := InformationTheory.klDiv ν.toMeasure P.toMeasure

/-- Defining formula of `sanovRate`. -/
lemma sanovRate_def {E : Type*} [MeasurableSpace E] (P ν : ProbabilityMeasure E) :
    sanovRate P ν = InformationTheory.klDiv ν.toMeasure P.toMeasure :=
  rfl

/-- Relative entropy is a good rate on a Polish Borel space. -/
private lemma isGoodRateFunction_sanovRate {E : Type*} [TopologicalSpace E] [PolishSpace E]
    [MeasurableSpace E] [BorelSpace E] (P : ProbabilityMeasure E) :
    TauCeti.Probability.IsGoodRateFunction (sanovRate P) := by
  have hlsc : LowerSemicontinuous (sanovRate P) := by
    unfold sanovRate
    exact (TauCeti.lowerSemicontinuous_klDiv_probabilityMeasure (α := E)).comp
      (continuous_id.prodMk continuous_const)
  refine isGoodRateFunction_of_isCompact_nnreal hlsc fun a ↦ ?_
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
    TauCeti.Probability.IsGoodRateFunction (sanovRate P) ∧
      TauCeti.Probability.HasLDP atTop (fun n : ℕ ↦ ((n : ℝ≥0) + 1)⁻¹)
        (fun n ↦ μ.map (empiricalProbability X n)) (sanovRate P) := by
  refine ⟨isGoodRateFunction_sanovRate P, ?_⟩
  sorry

end CKMA
