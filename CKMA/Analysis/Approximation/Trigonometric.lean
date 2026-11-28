/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs

/-!
# Trigonometric approximation and smoothness

Finite angular-frequency sums approximate continuous `2π`-periodic complex functions
in the unnormalized period `Lᵖ` seminorm. Iterated translation differences define the
smoothness modulus used in Jackson's direct and inverse estimates. Bernstein's
inequality bounds iterated derivatives by the corresponding power of the degree.

Sources: GAPS 47.20, 47.21 and 47.23.

## Main definitions

* `CKMA.trigonometricPeriodMeasure`: Lebesgue measure restricted to `[-π, π]`.
* `CKMA.trigonometricPolynomial`: trigonometric polynomial of degree at most `n`.
* `CKMA.translationDifference`: forward translation difference operator.
* `CKMA.periodicSmoothnessModulus`: order-`r` modulus of smoothness in `Lᵖ` on one period.
* `CKMA.bestTrigonometricError`: best trigonometric approximation error in `Lᵖ`.

## Main results

* `CKMA.trigonometricPolynomial_apply`, `CKMA.periodicSmoothnessModulus_def`,
  `CKMA.bestTrigonometricError_def`: defining lemmas.
* `CKMA.bestTrigonometricError_le`: any trigonometric polynomial bounds the best error.
* `CKMA.jackson_trigonometric`: Jackson's direct theorem for trigonometric approximation.
* `CKMA.inverse_trigonometric`: inverse theorem for trigonometric approximation.
* `CKMA.bernstein_trigonometric`: Bernstein's inequality for derivatives of trigonometric
  polynomials.
-/

public section

noncomputable section

namespace CKMA

open MeasureTheory
open scoped BigOperators ENNReal

/-- The unnormalized measure of one period, for angular frequencies `exp(ikx)`. -/
@[expose]
def trigonometricPeriodMeasure : Measure ℝ := volume.restrict (Set.Icc (-Real.pi) Real.pi)

/-- A trigonometric polynomial of degree at most `n`, with arbitrary complex coefficients. -/
@[expose]
def trigonometricPolynomial (n : ℕ) (a : ℤ → ℂ) (x : ℝ) : ℂ :=
  ∑ k ∈ Finset.Icc (-(n : ℤ)) n, a k * Complex.exp (Complex.I * k * x)

/-- The first forward translation difference. -/
@[expose]
def translationDifference (h : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ := f (x + h) - f x

/-- The order-`r` translation modulus in `Lᵖ` on one period, allowing infinite values. -/
@[expose]
def periodicSmoothnessModulus (r : ℕ) (f : ℝ → ℂ) (t : ℝ) (p : ℝ≥0∞) : ℝ≥0∞ :=
  ⨆ (h : ℝ) (_hh : |h| ≤ t),
    eLpNorm (((translationDifference h)^[r]) f) p trigonometricPeriodMeasure

/-- Best trigonometric approximation error in the period `Lᵖ` seminorm. -/
@[expose]
def bestTrigonometricError (f : ℝ → ℂ) (n : ℕ) (p : ℝ≥0∞) : ℝ≥0∞ :=
  ⨅ a : ℤ → ℂ, eLpNorm (fun x ↦ f x - trigonometricPolynomial n a x)
    p trigonometricPeriodMeasure

/-- The period measure is Lebesgue measure on `[-π, π]`. -/
lemma trigonometricPeriodMeasure_def :
    trigonometricPeriodMeasure = volume.restrict (Set.Icc (-Real.pi) Real.pi) :=
  rfl

/-- Evaluation of a trigonometric polynomial. -/
lemma trigonometricPolynomial_apply (n : ℕ) (a : ℤ → ℂ) (x : ℝ) :
    trigonometricPolynomial n a x =
      ∑ k ∈ Finset.Icc (-(n : ℤ)) n, a k * Complex.exp (Complex.I * k * x) :=
  rfl

/-- Evaluation of a translation difference. -/
@[simp]
lemma translationDifference_apply (h : ℝ) (f : ℝ → ℂ) (x : ℝ) :
    translationDifference h f x = f (x + h) - f x :=
  rfl

/-- The smoothness modulus is the supremum of the `Lᵖ` norms of the iterated differences over
steps `|h| ≤ t`. -/
lemma periodicSmoothnessModulus_def (r : ℕ) (f : ℝ → ℂ) (t : ℝ) (p : ℝ≥0∞) :
    periodicSmoothnessModulus r f t p = ⨆ (h : ℝ) (_hh : |h| ≤ t),
      eLpNorm (((translationDifference h)^[r]) f) p trigonometricPeriodMeasure :=
  rfl

/-- The best trigonometric error is the infimum of the residual `Lᵖ` norms. -/
lemma bestTrigonometricError_def (f : ℝ → ℂ) (n : ℕ) (p : ℝ≥0∞) :
    bestTrigonometricError f n p = ⨅ a : ℤ → ℂ,
      eLpNorm (fun x ↦ f x - trigonometricPolynomial n a x) p trigonometricPeriodMeasure :=
  rfl

/-- A specified trigonometric polynomial bounds the best approximation error. -/
theorem bestTrigonometricError_le (f : ℝ → ℂ) (n : ℕ) (p : ℝ≥0∞) (a : ℤ → ℂ) :
    bestTrigonometricError f n p ≤ eLpNorm (fun x ↦ f x - trigonometricPolynomial n a x)
      p trigonometricPeriodMeasure :=
  iInf_le _ a

/-- **47.20**: Jackson's direct theorem, with constants uniform over `1 ≤ p ≤ ∞`.
Stated for continuous `2π`-periodic `f`. -/
theorem jackson_trigonometric (r : ℕ) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ (p : ℝ≥0∞), 1 ≤ p →
      ∀ (f : ℝ → ℂ), Continuous f → Function.Periodic f (2 * Real.pi) →
      ∀ n : ℕ, 0 < n → bestTrigonometricError f n p ≤
        C * periodicSmoothnessModulus r f (n : ℝ)⁻¹ p := by
  sorry

/-- **47.21**: the inverse trigonometric estimate on continuous periodic functions. -/
theorem inverse_trigonometric (r : ℕ) (hr : 0 < r) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ (p : ℝ≥0∞), 1 ≤ p →
      ∀ (f : ℝ → ℂ), Continuous f → Function.Periodic f (2 * Real.pi) →
      ∀ n : ℕ, 0 < n → periodicSmoothnessModulus r f (n : ℝ)⁻¹ p ≤
        C * ENNReal.ofReal ((n : ℝ)⁻¹ ^ r) *
          ∑ k ∈ Finset.range (n + 1), (k + 1 : ℝ≥0∞) ^ (r - 1) *
            bestTrigonometricError f k p := by
  sorry

/-- **47.23**: the sharp Bernstein derivative inequality at angular normalization. It holds for
every exponent: for `1 ≤ p` it is Bernstein's inequality, for `0 < p < 1` it is Arestov's
theorem, and for `p = 0` both sides vanish. -/
theorem bernstein_trigonometric (n r : ℕ) (a : ℤ → ℂ) (p : ℝ≥0∞) :
    eLpNorm (iteratedDeriv r (trigonometricPolynomial n a)) p trigonometricPeriodMeasure ≤
      (n : ℝ≥0∞) ^ r * eLpNorm (trigonometricPolynomial n a) p trigonometricPeriodMeasure := by
  sorry

end CKMA
