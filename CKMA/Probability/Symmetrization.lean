/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Empirical symmetrization for countable classes (07.33)

`IsRademacher` fixes the symmetric law on the real signs. `symmetrization` bounds the
expected supremum of centered empirical averages by twice the corresponding signed
supremum for a nonempty countable function class with an integrable envelope.

Data and signs are sampled on separate probability spaces. Independence within each
sample and equality of the data laws are explicit; the positive sample size avoids a
zero-sample mean convention.
-/

@[expose] public section

noncomputable section

namespace CKMA

open scoped NNReal ENNReal


open MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- A measurable sign with the symmetric law on `{-1, 1}`. -/
def IsRademacher {Ω : Type*} [MeasurableSpace Ω] (ε : Ω → ℝ) (μ : Measure Ω) : Prop :=
  Measurable ε ∧ μ.map ε =
    (1 / 2 : ℝ≥0∞) • Measure.dirac (-1) + (1 / 2 : ℝ≥0∞) • Measure.dirac 1

/-- **07.33**: symmetrization for a nonempty countable class with an integrable envelope.
The signs are sampled on a separate probability space, so independence from the data is explicit. -/
theorem symmetrization {Ω Ω' E ι : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MeasurableSpace E] [Countable ι] [Nonempty ι]
    (μ : Measure Ω) (ν : Measure Ω') (P : Measure E)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure P]
    {n : ℕ} (hn : 0 < n) (X : Fin n → Ω → E) (ε : Fin n → Ω' → ℝ)
    (hX : ∀ i, Measurable (X i)) (hXi : iIndepFun X μ)
    (hlaw : ∀ i, μ.map (X i) = P) (hε : ∀ i, IsRademacher (ε i) ν)
    (hεi : iIndepFun ε ν) (f : ι → E → ℝ) (hf : ∀ i, Measurable (f i))
    (envelope : E → ℝ) (he : Integrable envelope P)
    (hbound : ∀ i x, |f i x| ≤ envelope x) :
    (∫ ω, ⨆ i, |(n : ℝ)⁻¹ * (∑ j, f i (X j ω)) - ∫ x, f i x ∂P| ∂μ) ≤
      2 * ∫ ω, ⨆ i, |(n : ℝ)⁻¹ * ∑ j, ε j ω.2 * f i (X j ω.1)| ∂μ.prod ν := by
  sorry

end CKMA
