/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Moments.Basic
import TauCeti.Probability.Moments.Bernstein

/-!
# Bernstein concentration inequality (07.4)

The two-sided scalar Bernstein inequality for independent centered bounded random variables,
stated with the measure of the tail event. It is derived from TauCeti's
`ProbabilityTheory.iIndepFun.measureReal_abs_sum_ge_le_of_abs_le`.

## Main results

* `CKMA.bernstein`: two-sided Bernstein tail bound for independent centered
  almost-everywhere bounded summands.
-/

public section

namespace CKMA

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **07.4**: scalar Bernstein inequality for independent bounded centered summands.
Independence forces `μ` to be a probability measure. -/
theorem bernstein {ι : Type*} (X : ι → Ω → ℝ) (s : Finset ι)
    (hm : ∀ i ∈ s, AEMeasurable (X i) μ) (hi : iIndepFun X μ)
    (hc : ∀ i ∈ s, ∫ ω, X i ω ∂μ = 0) {b t : ℝ} (ht : 0 ≤ t)
    (hbound : ∀ i ∈ s, ∀ᵐ ω ∂μ, |X i ω| ≤ b) :
    μ {ω | t ≤ |∑ i ∈ s, X i ω|} ≤ ENNReal.ofReal
      (2 * Real.exp (-(t ^ 2 / (2 * ((∑ i ∈ s, ∫ ω, (X i ω) ^ 2 ∂μ) + b * t / 3))))) := by
  have := hi.isProbabilityMeasure
  rw [← ofReal_measureReal, neg_div']
  exact ENNReal.ofReal_le_ofReal (hi.measureReal_abs_sum_ge_le_of_abs_le hm hc hbound ht)

end CKMA
