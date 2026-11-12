/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Probability.HansonWright.Bound

public import CKMA.Probability.Concentration
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Independence.Integration
public import Mathlib.Probability.Moments.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.Algebra.InfiniteSum.Ring
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
