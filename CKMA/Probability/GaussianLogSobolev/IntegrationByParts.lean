/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real

import TauCeti.Probability.Distributions.Gaussian.IntegrationByParts
import TauCeti.Probability.Distributions.Gaussian.Moments

/-!
# One-dimensional Gaussian integration by parts

For a `C¹` integrand with bounded value and derivative, `∫ x ψ ∂γ = ∫ ψ' ∂γ` under the standard
Gaussian `γ`. This is the bounded case of TauCeti's Stein identity
`TauCeti.Probability.integral_mul_eq_integral_deriv_gaussianReal`.

## Main results

* `CKMA.integral_id_mul_eq_integral_deriv_gaussianReal`: Gaussian integration by parts
  `∫ x ψ ∂γ = ∫ ψ' ∂γ`.
* `CKMA.GaussianLogSobolev.integrable_of_abs_le`: Mathlib's `Integrable.of_bound` with the
  bound stated as `|f x| ≤ M`.
-/

public section

noncomputable section

namespace CKMA

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal Real

/-- Gaussian integration by parts: `∫ x ψ ∂γ = ∫ ψ' ∂γ` for a bounded `C¹` integrand with
bounded derivative. This is TauCeti's
`TauCeti.Probability.integral_mul_eq_integral_deriv_gaussianReal`, whose integrability hypotheses
follow from the bounds. -/
lemma integral_id_mul_eq_integral_deriv_gaussianReal {ψ : ℝ → ℝ}
    (hψ : Differentiable ℝ ψ) (hψ' : Continuous (deriv ψ))
    (hψ_bdd : ∃ C, ∀ x, |ψ x| ≤ C) (hψ'_bdd : ∃ C, ∀ x, |deriv ψ x| ≤ C) :
    ∫ x, x * ψ x ∂gaussianReal 0 1 = ∫ x, deriv ψ x ∂gaussianReal 0 1 := by
  obtain ⟨C, hC⟩ := hψ_bdd
  obtain ⟨C', hC'⟩ := hψ'_bdd
  refine TauCeti.Probability.integral_mul_eq_integral_deriv_gaussianReal ψ hψ ?_
    (.of_bound hψ'.aestronglyMeasurable C' (ae_of_all _ hC'))
  refine ((TauCeti.Probability.integrable_abs_gaussianReal 0 1).const_mul C).mono'
    (continuous_id.mul hψ.continuous).aestronglyMeasurable (ae_of_all _ fun x ↦ ?_)
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, mul_comm C]
  exact mul_le_mul_of_nonneg_left (hC x) (abs_nonneg x)

namespace GaussianLogSobolev

/-- An a.e. strongly measurable function bounded by a constant is integrable on a finite measure
space. -/
lemma integrable_of_abs_le {E : Type*} [MeasurableSpace E] {μ : Measure E}
    [IsFiniteMeasure μ] {f : E → ℝ} (hf : AEStronglyMeasurable f μ) {M : ℝ}
    (hM : ∀ x, |f x| ≤ M) : Integrable f μ :=
  .of_bound hf M (ae_of_all _ fun x => (Real.norm_eq_abs _).trans_le (hM x))

end GaussianLogSobolev

end CKMA
