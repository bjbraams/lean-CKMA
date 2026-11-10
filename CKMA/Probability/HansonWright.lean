/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Probability.Concentration
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Hanson–Wright concentration for quadratic forms (07.43)

The matrix adapters are the squared Frobenius norm and Euclidean operator norm of a
real finite matrix. `sampledQuadraticForm` evaluates the corresponding form on a random
vector. `hanson_wright` gives the two-scale exponential bound for its centered value
under independent centered sub-Gaussian coordinates.

Matrices need not be symmetric. The universal constant is independent of dimension,
and positive threshold and scale hypotheses specify the meaningful concentration range.
-/

@[expose] public section

noncomputable section

namespace CKMA

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

universe u

/-- The squared Frobenius norm of a real matrix, given by its entries. -/
def realMatrixFrobeniusSq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ i, ∑ j, (A i j) ^ 2

/-- Euclidean operator norm, as distinct from the entrywise matrix norm. -/
def realMatrixOperatorNorm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ‖(Matrix.toEuclideanLin A).toContinuousLinearMap‖

/-- The real quadratic form sampled at a coordinate family. -/
def sampledQuadraticForm {Ω : Type*} {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (X : Fin n → Ω → ℝ) (ω : Ω) : ℝ :=
  ∑ i, ∑ j, A i j * X i ω * X j ω

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
  sorry

end CKMA
