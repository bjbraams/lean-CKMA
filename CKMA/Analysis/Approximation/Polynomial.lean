/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Analysis.Polynomial.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Tactic

/-!
# Uniform polynomial and rational approximation

Continuous real functions on `[-1,1]` have best approximation errors measured in the
supremum norm. The interfaces cover existence and uniqueness of best polynomials,
Chebyshev alternation including zero residual, sharp Markov derivative bounds,
Müntz–Szász density, and polynomial and rational approximation rates for the cusp `|x|`.
Rational approximants have denominators without zeros on the interval.

Sources: GAPS 47.6, 47.13, 47.24 and 47.40.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Filter Topology Polynomial
open scoped BigOperators

/-- Real continuous functions on the standard nondegenerate compact interval. -/
abbrev ApproximationIntervalMap := C(Set.Icc (-1 : ℝ) 1, ℝ)

/-- A polynomial restricted to the standard approximation interval. -/
def polynomialOnApproximationInterval (p : ℝ[X]) : ApproximationIntervalMap :=
  ⟨fun x ↦ p.eval x.1, p.continuous.comp continuous_subtype_val⟩

/-- Best uniform polynomial approximation error at degree at most `n`. -/
def bestPolynomialError (f : ApproximationIntervalMap) (n : ℕ) : ℝ :=
  sInf {r | ∃ p : ℝ[X], p.natDegree ≤ n ∧ r = ‖f - polynomialOnApproximationInterval p‖}

/-- A best uniform polynomial approximant, with the degree bound included. -/
def IsBestPolynomialApproximation (f : ApproximationIntervalMap) (n : ℕ) (p : ℝ[X]) : Prop :=
  p.natDegree ≤ n ∧ ∀ q : ℝ[X], q.natDegree ≤ n →
    ‖f - polynomialOnApproximationInterval p‖ ≤ ‖f - polynomialOnApproximationInterval q‖

/-- Alternation of the uniform residual at `n+2` strictly increasing points. -/
def HasPolynomialAlternation (f : ApproximationIntervalMap) (p : ℝ[X]) (n : ℕ) : Prop :=
  ∃ x : Fin (n + 2) → Set.Icc (-1 : ℝ) 1,
    StrictMono (fun i ↦ (x i).1) ∧ ∃ σ : ℝ, |σ| = 1 ∧ ∀ i,
      f (x i) - p.eval (x i).1 = σ * (-1) ^ i.val * ‖f - polynomialOnApproximationInterval p‖

/-- Finite-dimensional polynomial approximation has a unique uniform minimizer. -/
theorem existsUnique_bestPolynomialApproximation (f : ApproximationIntervalMap) (n : ℕ) :
    ∃! p : ℝ[X], IsBestPolynomialApproximation f n p := by
  sorry

/-- **47.6**: Chebyshev's alternation criterion on `[-1,1]`.
The generalized Haar-space criterion is a separate target. -/
theorem isBestPolynomialApproximation_iff_alternation (f : ApproximationIntervalMap)
    (n : ℕ) (p : ℝ[X]) (hp : p.natDegree ≤ n) :
    IsBestPolynomialApproximation f n p ↔ HasPolynomialAlternation f p n := by
  sorry

/-- Polynomial approximation errors are nonnegative. -/
theorem bestPolynomialError_nonneg (f : ApproximationIntervalMap) (n : ℕ) :
    0 ≤ bestPolynomialError f n := by
  apply le_csInf
  · exact ⟨‖f - polynomialOnApproximationInterval 0‖, 0, by simp, rfl⟩
  · rintro r ⟨p, hp, rfl⟩
    exact norm_nonneg _

/-- Any admissible polynomial gives an upper bound on best approximation error. -/
theorem bestPolynomialError_le (f : ApproximationIntervalMap) (n : ℕ) (p : ℝ[X])
    (hp : p.natDegree ≤ n) : bestPolynomialError f n ≤ ‖f - polynomialOnApproximationInterval p‖ :=
      by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro r ⟨q, hq, rfl⟩
    exact norm_nonneg _
  · exact ⟨p, hp, rfl⟩

/-- Increasing the admissible polynomial degree cannot increase best approximation error. -/
theorem bestPolynomialError_antitone (f : ApproximationIntervalMap) :
    Antitone (bestPolynomialError f) := by
  intro m n hmn
  apply le_csInf
  · exact ⟨‖f - polynomialOnApproximationInterval 0‖, 0, by simp, rfl⟩
  · rintro r ⟨p, hp, rfl⟩
    exact bestPolynomialError_le f n p (hp.trans hmn)

/-- **47.24**: Markov's sharp first-derivative bound, including interior points. -/
theorem polynomial_markov {n : ℕ} (p : ℝ[X]) (hp : p.natDegree ≤ n)
    {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    |p.derivative.eval x| ≤ (n : ℝ) ^ 2 * ‖polynomialOnApproximationInterval p‖ := by
  sorry

/-- The `n²` Markov constant is attained by a nonzero polynomial of degree `n`. -/
theorem polynomial_markov_sharp (n : ℕ) : ∃ p : ℝ[X], p.natDegree = n ∧ p ≠ 0 ∧
    ‖polynomialOnApproximationInterval p.derivative‖ =
      (n : ℝ) ^ 2 * ‖polynomialOnApproximationInterval p‖ := by
  sorry

/-- A nonnegative real power as a continuous function on `[0,1]`. -/
def muntzMonomial (a : ℝ) (ha : 0 ≤ a) : C(Set.Icc (0 : ℝ) 1, ℝ) :=
  ⟨fun x ↦ x.1 ^ a, (Real.continuous_rpow_const ha).comp continuous_subtype_val⟩

/-- The Müntz span includes the constant function as well as all prescribed powers. -/
def muntzSpan (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) :
    Submodule ℝ C(Set.Icc (0 : ℝ) 1, ℝ) :=
  Submodule.span ℝ (insert 1 (Set.range (fun n ↦ muntzMonomial (a n) (ha n))))

/-- **47.13**: Müntz–Szász for strictly increasing positive exponents tending to infinity.
Nonsummability of the positive reciprocal sequence expresses divergence to `+∞`. -/
theorem muntz_szasz (a : ℕ → ℝ) (ha : ∀ n, 0 < a n) (hmono : StrictMono a)
    (hlim : Tendsto a atTop atTop) :
    Dense (muntzSpan a (fun n ↦ (ha n).le) : Set C(Set.Icc (0 : ℝ) 1, ℝ)) ↔
      ¬ Summable (fun n ↦ (a n)⁻¹) := by
  sorry

/-- A rational function on the interval whose denominator has no interval zeros. -/
def rationalOnApproximationInterval (p q : ℝ[X])
    (hq : ∀ x : Set.Icc (-1 : ℝ) 1, q.eval x.1 ≠ 0) : ApproximationIntervalMap :=
  ⟨fun x ↦ p.eval x.1 / q.eval x.1,
    (p.continuous.comp continuous_subtype_val).div
      (q.continuous.comp continuous_subtype_val) hq⟩

/-- Best type-`(n,n)` rational approximation error, with poles excluded from the interval. -/
def bestRationalError (f : ApproximationIntervalMap) (n : ℕ) : ℝ :=
  sInf {r | ∃ (p q : ℝ[X]) (hq : ∀ x : Set.Icc (-1 : ℝ) 1, q.eval x.1 ≠ 0),
    p.natDegree ≤ n ∧ q.natDegree ≤ n ∧ r = ‖f - rationalOnApproximationInterval p q hq‖}

/-- The cusp function used in Newman's theorem. -/
def absoluteValueOnApproximationInterval : ApproximationIntervalMap :=
  ⟨fun x ↦ |x.1|, continuous_subtype_val.abs⟩

/-- **47.40**: root-exponential two-sided rational approximation rates for `|x|`. -/
theorem newman_rational_approximation : ∃ c₁ c₂ c₃ c₄ : ℝ,
    0 < c₁ ∧ 0 < c₂ ∧ 0 < c₃ ∧ 0 < c₄ ∧ ∀ n : ℕ, 0 < n →
      c₁ * Real.exp (-c₂ * Real.sqrt n) ≤
        bestRationalError absoluteValueOnApproximationInterval n ∧
      bestRationalError absoluteValueOnApproximationInterval n ≤
        c₃ * Real.exp (-c₄ * Real.sqrt n) := by
  sorry

/-- The polynomial approximation rate for the same cusp is only of order `1/n`. -/
theorem absoluteValue_polynomial_approximation : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ n : ℕ, 0 < n → c / n ≤ bestPolynomialError absoluteValueOnApproximationInterval n ∧
      bestPolynomialError absoluteValueOnApproximationInterval n ≤ C / n := by
  sorry

end CKMA
