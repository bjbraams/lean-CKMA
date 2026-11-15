/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.Approximation.Polynomial.Alternation
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Uniform polynomial and rational approximation

Continuous real functions on `[-1,1]` have best approximation errors measured in the
supremum norm. The interfaces cover existence and uniqueness of best polynomials,
Chebyshev alternation including zero residual, sharp Markov derivative bounds,
Müntz–Szász density, and polynomial and rational approximation rates for the cusp `|x|`.
Rational approximants have denominators without zeros on the interval.

Sources: GAPS 47.6, 47.13, 47.24 and 47.40.

## Main definitions

* `CKMA.muntzMonomial`: a nonnegative real power on `[0, 1]`.
* `CKMA.muntzSpan`: the span of `1` and prescribed powers on `[0, 1]`.
* `CKMA.rationalOnApproximationInterval`: rational function without poles on `[-1, 1]`.
* `CKMA.bestRationalError`: best type-`(n, n)` rational approximation error on `[-1, 1]`.

## Main results

* `CKMA.exists_isBestPolynomialApproximation`: existence of a best polynomial approximant.
* `CKMA.existsUnique_isBestPolynomialApproximation`: unique existence of the best polynomial
  approximant.
* `CKMA.isBestPolynomialApproximation_iff_hasPolynomialAlternation`: Chebyshev's alternation
  criterion.
* `CKMA.polynomial_markov`: Markov's sharp first-derivative inequality.
* `CKMA.muntz_szasz`: Müntz–Szász theorem.
* `CKMA.newman_rational_approximation`: Newman's rational approximation rate for `|x|`.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Filter Metric Topology Polynomial
open scoped BigOperators

/-- The coefficient parametrization of polynomial functions on `[-1,1]`. -/
private def coeffToApproximationMap (n : ℕ) :
    (Fin (n + 1) → ℝ) →ₗ[ℝ] ApproximationIntervalMap where
  toFun c := polynomialOnApproximationInterval (polynomialOfCoeffs n c)
  map_add' c d := by
    ext x
    have hpoly : polynomialOfCoeffs n (c + d) =
        polynomialOfCoeffs n c + polynomialOfCoeffs n d := by
      unfold polynomialOfCoeffs
      simp [map_add, Finset.sum_add_distrib]
    simp [polynomialOnApproximationInterval, hpoly, eval_add]
  map_smul' r c := by
    ext x
    have hpoly : polynomialOfCoeffs n (r • c) = r • polynomialOfCoeffs n c := by
      unfold polynomialOfCoeffs
      simp [smul_monomial, Finset.smul_sum]
    simp [polynomialOnApproximationInterval, hpoly, eval_smul, smul_eq_mul]

/-- Distinct coefficient vectors give distinct continuous functions. -/
private lemma coeffToApproximationMap_injective (n : ℕ) :
    Function.Injective (coeffToApproximationMap n) := by
  intro c d hcd
  rw [← sub_eq_zero, ← LinearMap.map_sub] at hcd
  have hp : polynomialOfCoeffs n (c - d) = 0 :=
    eq_zero_of_polynomialOnApproximationInterval_eq_zero
      (polynomialOfCoeffs n (c - d)) (natDegree_polynomialOfCoeffs_le n (c - d)) hcd
  exact sub_eq_zero.mp ((polynomialOfCoeffs_eq_zero_iff n (c - d)).mp hp)

/-- The coefficient embedding is anti-Lipschitz for the supremum norm. -/
private lemma exists_antilipschitz_coeffToApproximationMap (n : ℕ) :
    ∃ K : NNReal, 0 < K ∧ AntilipschitzWith K (coeffToApproximationMap n) := by
  simpa using (coeffToApproximationMap n).exists_antilipschitzWith
    (LinearMap.ker_eq_bot.mpr (coeffToApproximationMap_injective n))

/-- A minimizing coefficient vector exists for the uniform error. -/
lemma exists_isBestPolynomialApproximation (f : ApproximationIntervalMap) (n : ℕ) :
    ∃ p : ℝ[X], IsBestPolynomialApproximation f n p := by
  obtain ⟨K, hKpos, hK⟩ := exists_antilipschitz_coeffToApproximationMap n
  let err : (Fin (n + 1) → ℝ) → ℝ := fun c => ‖f - coeffToApproximationMap n c‖
  have herr : Continuous err := by
    unfold err
    exact continuous_norm.comp
      ((continuous_const.sub (coeffToApproximationMap n).continuous_of_finiteDimensional))
  let R : ℝ := 2 * (K : ℝ) * ‖f‖
  have hR : 0 ≤ R := by positivity
  let B := closedBall (0 : Fin (n + 1) → ℝ) R
  obtain ⟨c, hc, hmin⟩ := (isCompact_closedBall (0 : Fin (n + 1) → ℝ) R).exists_isMinOn
    ⟨0, mem_closedBall_self hR⟩ herr.continuousOn
  refine ⟨polynomialOfCoeffs n c, natDegree_polynomialOfCoeffs_le n c, ?_⟩
  intro q hq
  let d : Fin (n + 1) → ℝ := fun i => q.coeff i.val
  have hqeq : polynomialOfCoeffs n d = q := polynomialOfCoeffs_of_natDegree_le n q hq
  have herrq : ‖f - polynomialOnApproximationInterval q‖ = err d := by
    simp [err, hqeq, coeffToApproximationMap]
  by_cases hd : ‖d‖ ≤ R
  · have hdB : d ∈ B := by simpa [B, mem_closedBall, dist_zero_right] using hd
    have hmin' := hmin hdB
    simpa [err, coeffToApproximationMap, hqeq] using hmin'
  · have hdlt : R < ‖d‖ := lt_of_not_ge hd
    have hanti := ZeroHomClass.bound_of_antilipschitz (coeffToApproximationMap n) hK d
    have h1 : R < (K : ℝ) * ‖coeffToApproximationMap n d‖ := lt_of_lt_of_le hdlt hanti
    have hK0 : (0 : ℝ) < K := NNReal.coe_pos.mpr hKpos
    have h2 : 2 * ‖f‖ < ‖coeffToApproximationMap n d‖ := by
      have h1' : (K : ℝ) * (2 * ‖f‖) < (K : ℝ) * ‖coeffToApproximationMap n d‖ := by
        simpa [R, mul_left_comm, mul_assoc] using h1
      exact lt_of_mul_lt_mul_left h1' hK0.le
    have hdiff : ‖coeffToApproximationMap n d‖ - ‖f‖ ≤ err d := by
      have hsub := (le_abs_self _).trans
        (abs_norm_sub_norm_le (coeffToApproximationMap n d) f)
      simpa [err, norm_sub_rev] using hsub
    have herrd : ‖f‖ < err d := by
      have : ‖f‖ < ‖coeffToApproximationMap n d‖ - ‖f‖ := by linarith
      linarith
    have herr0 : err c ≤ err 0 := hmin (mem_closedBall_self hR)
    have herr0' : err 0 = ‖f‖ := by simp [err, map_zero]
    have hle : err c < err d := lt_of_le_of_lt (by simpa [herr0'] using herr0) herrd
    simpa [err, coeffToApproximationMap, herrq] using hle.le

/-- Finite-dimensional polynomial approximation has a unique uniform minimizer. -/
theorem existsUnique_isBestPolynomialApproximation (f : ApproximationIntervalMap) (n : ℕ) :
    ∃! p : ℝ[X], IsBestPolynomialApproximation f n p := by
  obtain ⟨p, hp⟩ := exists_isBestPolynomialApproximation f n
  exact ⟨p, hp, fun q hq => (eq_of_isBestPolynomialApproximation f n p q hp hq).symm⟩

/-- **47.6**: Chebyshev's alternation criterion on `[-1,1]`.
The generalized Haar-space criterion is a separate target. -/
theorem isBestPolynomialApproximation_iff_hasPolynomialAlternation (f : ApproximationIntervalMap)
    (n : ℕ) (p : ℝ[X]) (hp : p.natDegree ≤ n) :
    IsBestPolynomialApproximation f n p ↔ HasPolynomialAlternation f p n := by
  constructor
  · intro h
    exact hasPolynomialAlternation_of_isBestPolynomialApproximation f n p h
  · intro h
    exact isBestPolynomialApproximation_of_hasPolynomialAlternation f n p hp h

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
theorem muntz_szasz (a : ℕ → ℝ) (ha0 : 0 < a 0) (hmono : StrictMono a)
    (hlim : Tendsto a atTop atTop) :
    Dense (muntzSpan a (fun n ↦ (ha0.trans_le (hmono.monotone (Nat.zero_le n))).le) :
      Set C(Set.Icc (0 : ℝ) 1, ℝ)) ↔ ¬ Summable (fun n ↦ (a n)⁻¹) := by
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
