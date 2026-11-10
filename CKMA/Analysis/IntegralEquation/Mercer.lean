/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.Operator.TraceIdeals
public import CKMA.Analysis.IntegralEquation.HilbertSchmidt
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.Topology.ContinuousMap.Compact

/-!
# Mercer expansions of continuous positive-semidefinite kernels

Positive-semidefiniteness is tested by finite Gram matrices on a compact Hausdorff carrier.
A finite measure
with full support determines the integral operator and its continuous positive-eigenvalue
representatives. The expansion permits zero eigenvalue tails, including finite-rank and zero
kernels.

Uniform absolute convergence means uniform control of every finite absolute tail sum; it does
not impose the stronger summability of individual supremum norms. The sum of eigenvalues is
the integral of the diagonal. Source: GAPS 25.8.
-/

@[expose] public section

noncomputable section

namespace CKMA

open MeasureTheory Filter Topology
open scoped BigOperators ComplexConjugate ComplexOrder

/-- Kernel positive-semidefiniteness through all finite Gram matrices.
Zero eigenvalues, finite rank, and the zero kernel are allowed. -/
def IsPositiveSemidefiniteKernel {D : Type*} (k : D → D → ℂ) : Prop :=
  ∀ n : ℕ, ∀ x : Fin n → D, Matrix.PosSemidef (fun i j : Fin n ↦ k (x i) (x j))

/-- The kth Mercer summand with its continuous eigenfunction representative. -/
def mercerTerm {D : Type*} [TopologicalSpace D] (a : ℕ → ℝ) (e : ℕ → C(D, ℂ))
    (n : ℕ) (p : D × D) : ℂ := (a n : ℂ) * e n p.1 * conj (e n p.2)

/-- Uniform absolute convergence in the correct tail sense. Summability of individual
supremum norms would be stronger than Mercer's theorem and is deliberately not assumed. -/
def HasUniformAbsoluteMercerTails {D : Type*} [TopologicalSpace D]
    (a : ℕ → ℝ) (e : ℕ → C(D, ℂ)) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ s : Finset ℕ, (∀ n ∈ s, N ≤ n) →
    ∀ p : D × D, (∑ n ∈ s, ‖mercerTerm a e n p‖) < ε

/-- **25.8**, Mercer: the compact positive-semidefinite kernel has a uniform absolutely
convergent spectral expansion, with continuous normalized eigenfunctions at every positive
eigenvalue. Zero tails are allowed, so finite-rank and zero kernels are included. -/
theorem mercer_expansion {D : Type*} [TopologicalSpace D] [CompactSpace D] [T2Space D]
    [MeasurableSpace D] [BorelSpace D] (μ : Measure D) [IsFiniteMeasure μ]
    (hsupport : ∀ U : Set D, IsOpen U → U.Nonempty → 0 < μ U)
    (k : D → D → ℂ) (hc : Continuous (fun p : D × D ↦ k p.1 p.2))
    (hk : IsPositiveSemidefiniteKernel k) :
    ∃ a : ℕ → ℝ, ∃ e : ℕ → C(D, ℂ), ∃ T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ,
      (∀ n, 0 ≤ a n) ∧ Antitone a ∧ Summable a ∧
      IsTraceClassOperator T ∧ HasIntegralKernel μ T (fun p ↦ k p.1 p.2) ∧
      (∀ n, 0 < a n → ∀ x, (∫ y, k x y * e n y ∂μ) = (a n : ℂ) * e n x) ∧
      (∀ n m, 0 < a n → 0 < a m →
        (∫ x, conj (e n x) * e m x ∂μ) = if n = m then 1 else 0) ∧
      (∀ p : D × D, HasSum (fun n ↦ mercerTerm a e n p) (k p.1 p.2)) ∧
      HasUniformAbsoluteMercerTails a e ∧
      (∑' n, a n) = ∫ x, (k x x).re ∂μ := by
  sorry

end CKMA
