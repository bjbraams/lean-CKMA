/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import TauCeti.MeasureTheory.Integral.MaximalFunction
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Muckenhoupt weights and maximal estimates

The ball A_p characteristic averages a positive weight and its reciprocal power.
Weighted Lᵖ boundedness of the centered Hardy–Littlewood maximal operator characterizes
A_p for `p > 1`; A₁ weights satisfy the weighted weak (1,1) estimate. The maximal
operator is TauCeti's `maximalFunction`, with Euclidean balls fixing the characteristic
normalization.

Source: GAPS 27.44.
-/

@[expose] public section

noncomputable section

namespace CKMA

open MeasureTheory
open scoped ENNReal

/-- The measure with a nonnegative real weight as density. -/
def weightedLebesgueMeasure {d : ℕ} (w : EuclideanSpace ℝ (Fin d) → ℝ) :
    Measure (EuclideanSpace ℝ (Fin d)) := volume.withDensity (fun x ↦ ENNReal.ofReal (w x))

/-- The ball A_p characteristic. Balls and axis-parallel cubes give equivalent finite classes
in Euclidean space, but the characteristic constants themselves depend on this convention. -/
def muckenhouptCharacteristic {d : ℕ} (p : ℝ) (w : EuclideanSpace ℝ (Fin d) → ℝ) : ℝ≥0∞ :=
  ⨆ (x : EuclideanSpace ℝ (Fin d)) (r : ℝ) (_hr : 0 < r),
    ((∫⁻ y in Metric.ball x r, ENNReal.ofReal (w y)) / volume (Metric.ball x r)) *
      (((∫⁻ y in Metric.ball x r, ENNReal.ofReal ((w y) ^ (-(p - 1)⁻¹))) /
        volume (Metric.ball x r)) ^ (p - 1))

/-- Positive, locally integrable A_p weights, with the characteristic retaining infinity. -/
def IsMuckenhouptWeight {d : ℕ} (p : ℝ) (w : EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  1 < p ∧ Measurable w ∧ (∀ᵐ x ∂volume, 0 < w x) ∧ LocallyIntegrable w volume ∧
    muckenhouptCharacteristic p w < ∞

/-- The A_1 class, using TauCeti's centered maximal function and its actual positive bound. -/
def IsMuckenhouptOneWeight {d : ℕ} (w : EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  Measurable w ∧ (∀ᵐ x ∂volume, 0 < w x) ∧ LocallyIntegrable w volume ∧
    ∃ C : ℝ, 0 < C ∧ ∀ᵐ x ∂volume,
      TauCeti.maximalFunction volume w x ≤ ENNReal.ofReal (C * w x)

/-- **27.44**: boundedness of the actual maximal operator on weighted Lp characterizes A_p. -/
theorem weighted_maximal_iff {d : ℕ} {p : ℝ} (hp : 1 < p)
    {w : EuclideanSpace ℝ (Fin d) → ℝ} (hm : Measurable w)
    (hpos : ∀ᵐ x ∂volume, 0 < w x) (hloc : LocallyIntegrable w volume) :
    IsMuckenhouptWeight p w ↔ ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      ∀ f : EuclideanSpace ℝ (Fin d) → ℂ,
        MemLp f (ENNReal.ofReal p) (weightedLebesgueMeasure w) →
        (∫⁻ x, (TauCeti.maximalFunction volume f x) ^ p ∂weightedLebesgueMeasure w) ≤
          C * (eLpNorm f (ENNReal.ofReal p) (weightedLebesgueMeasure w)) ^ p := by
  sorry

/-- Weighted weak (1,1) maximal control for A_1 weights. -/
theorem weighted_maximal_weakType {d : ℕ} {w : EuclideanSpace ℝ (Fin d) → ℝ}
    (hw : IsMuckenhouptOneWeight w) : ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      ∀ f : EuclideanSpace ℝ (Fin d) → ℂ, Integrable f (weightedLebesgueMeasure w) →
      ∀ a : ℝ, 0 < a → ENNReal.ofReal a *
        weightedLebesgueMeasure w {x | ENNReal.ofReal a < TauCeti.maximalFunction volume f x} ≤
          C * ∫⁻ x, ‖f x‖ₑ ∂weightedLebesgueMeasure w := by
  sorry

end CKMA
