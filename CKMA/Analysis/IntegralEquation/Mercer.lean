/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.Operator.Basic
public import CKMA.Analysis.IntegralEquation.HilbertSchmidt

/-!
# Mercer expansions of continuous positive-semidefinite kernels

Let `D` be a compact Hausdorff space with a finite Borel measure `μ` of full support, and let
`k : D → D → ℂ` be continuous and positive semidefinite (every finite Gram matrix
`(k (x i) (x j))` is positive semidefinite). Mercer's theorem states that the integral operator
of `k` on `L²(μ)` is trace class, that its positive eigenvalues `a n` have continuous
orthonormal eigenfunctions `e n`, and that `k x y = ∑ a n * e n x * conj (e n y)` with uniformly
absolutely convergent tails, and `∑ a n = ∫ k x x ∂μ`. Finitely many or no positive eigenvalues
are allowed (`a n = 0` from some index on), which covers finite-rank and zero kernels.
Source: GAPS 25.8.

## Main definitions

* `CKMA.IsPositiveSemidefiniteKernel`: positive-semidefiniteness of a kernel via finite Gram
  matrices.
* `CKMA.mercerTerm`: the rank-one summand `a n * e n x * conj (e n y)` of Mercer's series.
* `CKMA.HasUniformAbsoluteMercerTails`: the absolute tail sums `∑ n ∈ s, ‖mercerTerm a e n p‖`
  over finite sets `s` of indices `≥ N` are uniformly small for large `N`.

## Main results

* `CKMA.mercer_expansion`: Mercer's spectral expansion and trace formula for continuous
  positive-semidefinite kernels (**25.8**).

## Implementation notes

`HasUniformAbsoluteMercerTails` is the uniform Cauchy condition for the absolute series
`∑ |a n| |e n x| |e n y|`; it is weaker than summability of the supremum norms of the summands,
which Mercer's theorem does not give.

## References

* F. Riesz and B. Sz.-Nagy, *Functional Analysis*, Ungar, 1955.
* R. Kress, *Linear Integral Equations*, 3rd ed., Springer, 2014.
-/

public section

noncomputable section

namespace CKMA

open MeasureTheory Filter Topology
open scoped BigOperators ComplexConjugate ComplexOrder

/-- A kernel `k` is positive semidefinite when every finite Gram matrix `(k (x i) (x j))` is
positive semidefinite. -/
@[expose]
def IsPositiveSemidefiniteKernel {D : Type*} (k : D → D → ℂ) : Prop :=
  ∀ n : ℕ, ∀ x : Fin n → D, Matrix.PosSemidef (fun i j : Fin n ↦ k (x i) (x j))

/-- Defining property of `IsPositiveSemidefiniteKernel`. -/
theorem isPositiveSemidefiniteKernel_iff {D : Type*} {k : D → D → ℂ} :
    IsPositiveSemidefiniteKernel k ↔
      ∀ n : ℕ, ∀ x : Fin n → D, Matrix.PosSemidef (fun i j : Fin n ↦ k (x i) (x j)) :=
  Iff.rfl

/-- The `n`-th summand `a n * e n x * conj (e n y)` of Mercer's series, at `p = (x, y)`. -/
@[expose]
def mercerTerm {D : Type*} [TopologicalSpace D] (a : ℕ → ℝ) (e : ℕ → C(D, ℂ))
    (n : ℕ) (p : D × D) : ℂ := (a n : ℂ) * e n p.1 * conj (e n p.2)

/-- Defining equation of `mercerTerm`. -/
theorem mercerTerm_def {D : Type*} [TopologicalSpace D] (a : ℕ → ℝ) (e : ℕ → C(D, ℂ))
    (n : ℕ) (p : D × D) : mercerTerm a e n p = (a n : ℂ) * e n p.1 * conj (e n p.2) :=
  rfl

/-- Uniform absolute convergence of Mercer's series: for every `ε > 0` there is `N` such that
every finite absolute tail sum over indices `≥ N` is below `ε`, uniformly in `p`. -/
@[expose]
def HasUniformAbsoluteMercerTails {D : Type*} [TopologicalSpace D]
    (a : ℕ → ℝ) (e : ℕ → C(D, ℂ)) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ s : Finset ℕ, (∀ n ∈ s, N ≤ n) →
    ∀ p : D × D, (∑ n ∈ s, ‖mercerTerm a e n p‖) < ε

/-- Defining property of `HasUniformAbsoluteMercerTails`. -/
theorem hasUniformAbsoluteMercerTails_iff {D : Type*} [TopologicalSpace D]
    {a : ℕ → ℝ} {e : ℕ → C(D, ℂ)} :
    HasUniformAbsoluteMercerTails a e ↔ ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ s : Finset ℕ,
      (∀ n ∈ s, N ≤ n) → ∀ p : D × D, (∑ n ∈ s, ‖mercerTerm a e n p‖) < ε :=
  Iff.rfl

/-- **25.8**, Mercer's theorem: for a continuous positive-semidefinite kernel `k` on a compact
Hausdorff space with a finite Borel measure of full support, the integral operator of `k` on
`L²(μ)` is trace class; there are eigenvalues `a n ≥ 0`, antitone and summable, and continuous
functions `e n`, orthonormal and eigenfunctions of the kernel at each positive `a n`, such that
`k x y = ∑ n, mercerTerm a e n (x, y)` with uniformly absolutely convergent tails and
`∑' n, a n = ∫ x, re (k x x) ∂μ`. -/
theorem mercer_expansion {D : Type*} [TopologicalSpace D] [CompactSpace D] [T2Space D]
    [MeasurableSpace D] [BorelSpace D] (μ : Measure D) [IsFiniteMeasure μ] [μ.IsOpenPosMeasure]
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
