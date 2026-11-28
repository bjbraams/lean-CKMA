/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import TauCeti.MeasureTheory.Group.Convolution.Power

/-!
# Infinite divisibility and Lévy triplets

`IsInfinitelyDivisible` asks for probability convolution roots of every positive order, with
powers taken by TauCeti's `MeasureTheory.Measure.convolutionPower`. `IsLevyMeasure` records
the zero atom and integrability of the truncated quadratic jump size. `LevyTriplet` packages
Gaussian variance, drift and jump measure, with its characteristic exponent using the
truncation `x * 1_{|x| ≤ 1}`.

## Main definitions

* `CKMA.IsInfinitelyDivisible`: infinite divisibility of a real probability law.
* `CKMA.IsLevyMeasure`: Lévy measure condition on `ℝ`.
* `CKMA.LevyTriplet`: Lévy triplet with characteristic exponent `CKMA.LevyTriplet.exponent`.
-/

public section

noncomputable section

namespace CKMA

open MeasureTheory
open scoped BigOperators NNReal ENNReal MeasureTheory

/-- Infinite divisibility of a real probability law by probability convolution roots. -/
@[expose]
def IsInfinitelyDivisible (μ : Measure ℝ) : Prop :=
  IsProbabilityMeasure μ ∧ ∀ n : ℕ, 0 < n →
    ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧ ν.convolutionPower n = μ

/-- A Lévy measure has no atom at zero and integrates the standard quadratic truncation. -/
@[expose]
def IsLevyMeasure (ν : Measure ℝ) : Prop :=
  ν {0} = 0 ∧ (∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂ν) < ∞

/-- Defining property of `IsInfinitelyDivisible`. -/
lemma isInfinitelyDivisible_iff {μ : Measure ℝ} :
    IsInfinitelyDivisible μ ↔ IsProbabilityMeasure μ ∧ ∀ n : ℕ, 0 < n →
      ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧ ν.convolutionPower n = μ :=
  Iff.rfl

/-- An infinitely divisible law is a probability measure. -/
lemma IsInfinitelyDivisible.isProbabilityMeasure {μ : Measure ℝ} (h : IsInfinitelyDivisible μ) :
    IsProbabilityMeasure μ :=
  h.1

/-- An infinitely divisible law has a probability convolution root of each positive order. -/
lemma IsInfinitelyDivisible.exists_convolutionPower_eq {μ : Measure ℝ}
    (h : IsInfinitelyDivisible μ) {n : ℕ} (hn : 0 < n) :
    ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧ ν.convolutionPower n = μ :=
  h.2 n hn

/-- Defining property of `IsLevyMeasure`. -/
lemma isLevyMeasure_iff {ν : Measure ℝ} :
    IsLevyMeasure ν ↔ ν {0} = 0 ∧ (∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂ν) < ∞ :=
  Iff.rfl

/-- A Lévy measure has no atom at zero. -/
lemma IsLevyMeasure.measure_zero {ν : Measure ℝ} (h : IsLevyMeasure ν) : ν {0} = 0 :=
  h.1

/-- A Lévy measure integrates `min 1 x²`. -/
lemma IsLevyMeasure.lintegral_lt_top {ν : Measure ℝ} (h : IsLevyMeasure ν) :
    (∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂ν) < ∞ :=
  h.2

/-- A Lévy triplet for the truncation `x * 1_{|x|≤1}`. -/
@[ext]
structure LevyTriplet where
  /-- Nonnegative Gaussian variance coefficient. -/
  gaussianVariance : ℝ≥0
  /-- Real drift coefficient for the specified truncation. -/
  drift : ℝ
  /-- Jump intensity. -/
  jumpMeasure : Measure ℝ
  /-- The jump intensity satisfies the Lévy integrability condition. -/
  isLevyMeasure : IsLevyMeasure jumpMeasure

/-- The characteristic exponent in the Lévy–Khintchine formula. -/
@[expose]
def LevyTriplet.exponent (L : LevyTriplet) (t : ℝ) : ℂ :=
  Complex.I * L.drift * t - (L.gaussianVariance : ℂ) * (t : ℂ) ^ 2 / 2 +
    ∫ x, Complex.exp (Complex.I * t * x) - 1 -
      (if |x| ≤ 1 then Complex.I * t * x else 0) ∂L.jumpMeasure

/-- Defining formula of `LevyTriplet.exponent`. -/
lemma LevyTriplet.exponent_def (L : LevyTriplet) (t : ℝ) :
    L.exponent t = Complex.I * L.drift * t - (L.gaussianVariance : ℂ) * (t : ℂ) ^ 2 / 2 +
      ∫ x, Complex.exp (Complex.I * t * x) - 1 -
        (if |x| ≤ 1 then Complex.I * t * x else 0) ∂L.jumpMeasure :=
  rfl

end CKMA
