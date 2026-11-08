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

open MeasureTheory ProbabilityTheory Filter Topology
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

/-- **06.60**: Cramer's theorem with the actual extended-log-MGF conjugate as good rate. -/
theorem cramer {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hm : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hid : ∀ n, IdentDistrib (X n) (X 0) μ μ)
    (hexp : ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, |t| < ε →
      Integrable (fun ω ↦ Real.exp (t * X 0 ω)) μ) :
    IsGoodRateFunction (cramerRate (X 0) μ) ∧
      HasLargeDeviationPrinciple (sampleMeanLaws X μ) (cramerRate (X 0) μ) := by
  sorry

/-- The empirical probability measure, reusing TauCeti's finite-population construction. -/
def empiricalProbability {Ω E : Type*} [MeasurableSpace E]
    (X : ℕ → Ω → E) (n : ℕ) (ω : Ω) : ProbabilityMeasure E :=
  TauCeti.Probability.empiricalMeasureOfFintype (fun i : Fin (n + 1) ↦ X i ω)

/-- Sanov's entropy rate, using Mathlib's relative entropy of probability measures. -/
def sanovRate {E : Type*} [MeasurableSpace E] (P : ProbabilityMeasure E)
    (ν : ProbabilityMeasure E) : ℝ≥0∞ := InformationTheory.klDiv ν.toMeasure P.toMeasure

/-- **06.61**: Sanov's theorem on a Polish space in the weak topology of probability measures. -/
theorem sanov {Ω E : Type*} [MeasurableSpace Ω] [TopologicalSpace E]
    [PolishSpace E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : ProbabilityMeasure E)
    (X : ℕ → Ω → E) (hm : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hlaw : ∀ n, μ.map (X n) = P.toMeasure) :
    IsGoodRateFunction (sanovRate P) ∧
      HasLargeDeviationPrinciple (fun n ↦ μ.map (empiricalProbability X n)) (sanovRate P) := by
  sorry

end CKMA
