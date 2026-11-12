/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.MeasureTheory.Group.Convolution
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Infinite divisibility and Lévy triplets

`convolutionPower` and `IsInfinitelyDivisible` use positive convolution roots of a real
probability law. `IsLevyMeasure` records the zero atom and integrability of the truncated
quadratic jump size. `LevyTriplet` packages Gaussian variance, drift and jump measure,
with its characteristic exponent using the truncation `x * 1_{|x| ≤ 1}`.
-/

@[expose] public section

noncomputable section

namespace CKMA

open MeasureTheory
open scoped BigOperators NNReal ENNReal MeasureTheory

/-- The additive convolution power, with the point mass at zero as zeroth power. -/
def convolutionPower (μ : Measure ℝ) : ℕ → Measure ℝ
  | 0 => Measure.dirac 0
  | n + 1 => (convolutionPower μ n).conv μ

/-- Infinite divisibility of a real probability law by probability convolution roots. -/
def IsInfinitelyDivisible (μ : Measure ℝ) : Prop :=
  IsProbabilityMeasure μ ∧ ∀ n : ℕ, 0 < n →
    ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧ convolutionPower ν n = μ

/-- A Levy measure has no atom at zero and integrates the standard quadratic truncation. -/
def IsLevyMeasure (ν : Measure ℝ) : Prop :=
  ν {0} = 0 ∧ (∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂ν) < ∞

/-- A Levy triplet for the truncation `x * 1_{|x|≤1}`. -/
structure LevyTriplet where
  /-- Nonnegative Gaussian variance coefficient. -/
  gaussianVariance : ℝ≥0
  /-- Real drift coefficient for the specified truncation. -/
  drift : ℝ
  /-- Jump intensity. -/
  jumpMeasure : Measure ℝ
  /-- The jump intensity satisfies the Levy integrability condition. -/
  isLevyMeasure : IsLevyMeasure jumpMeasure

/-- The characteristic exponent in the Levy–Khintchine formula. -/
def LevyTriplet.exponent (L : LevyTriplet) (t : ℝ) : ℂ :=
  Complex.I * L.drift * t - (L.gaussianVariance : ℂ) * (t : ℂ) ^ 2 / 2 +
    ∫ x, Complex.exp (Complex.I * t * x) - 1 -
      (if |x| ≤ 1 then Complex.I * t * x else 0) ∂L.jumpMeasure

end CKMA
