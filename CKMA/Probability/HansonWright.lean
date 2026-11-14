/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Probability.HansonWright.Bound
public import CKMA.Probability.Concentration.Basic

/-!
# Hanson–Wright concentration for quadratic forms (07.43)

The matrix adapters are the squared Frobenius norm and Euclidean operator norm of a
real finite matrix. `sampledQuadraticForm` evaluates the corresponding form on a random
vector. `hanson_wright` gives the two-scale exponential bound for its centered value
under independent centered sub-Gaussian coordinates.

Diagonal tails are in `HansonWright.Estimates`, the off-diagonal comparison is in
`HansonWright.OffDiagonal`, and the combination is in `HansonWright.Bound`.

Matrices need not be symmetric. The universal constant is independent of dimension,
and positive threshold and scale hypotheses specify the meaningful concentration range.

## Main definitions

* `CKMA.realMatrixFrobeniusSq`: squared Frobenius norm of a real matrix
  (in `HansonWright.Estimates`).
* `CKMA.realMatrixOperatorNorm`: Euclidean operator norm of a real matrix
  (in `HansonWright.Estimates`).
* `CKMA.sampledQuadraticForm`: quadratic form sampled at a coordinate family
  (in `HansonWright.Estimates`).

## Main results

* `CKMA.hanson_wright`: Hanson–Wright concentration inequality with a universal constant.

## Notation

No new notation is introduced in this file.
-/

@[expose] public section

noncomputable section

namespace CKMA

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal RealInnerProductSpace Matrix Matrix.Norms.L2Operator

universe u

/-- **07.43**: Hanson–Wright with a constant uniform over dimensions, probability spaces,
coordinate laws and matrices. The Frobenius denominator is squared, and the operator norm is
  Euclidean. -/
theorem hanson_wright : ∃ c : ℝ, 0 < c ∧
    ∀ (n : ℕ) (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (X : Fin n → Ω → ℝ), (∀ i, Measurable (X i)) → iIndepFun X μ →
      (∀ i, ∫ ω, X i ω ∂μ = 0) →
      ∀ K : ℝ, 0 < K → (∀ i, psiTwoGauge (X i) μ ≤ ENNReal.ofReal K) →
      ∀ (A : Matrix (Fin n) (Fin n) ℝ) (t : ℝ), 0 < t →
      μ {ω | t < |sampledQuadraticForm A X ω - ∫ η, sampledQuadraticForm A X η ∂μ|} ≤
        ENNReal.ofReal (2 * Real.exp (-c * min
          (t ^ 2 / (K ^ 4 * realMatrixFrobeniusSq A))
          (t / (K ^ 2 * realMatrixOperatorNorm A)))) := by
  exact ⟨1 / 2359296, by norm_num, hanson_wright_explicit⟩

end CKMA
