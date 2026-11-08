/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.Complex.Hardy
public import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Carleson measures and bounded disk interpolation

Carleson box bounds characterize embeddings of analytic Hardy classes into disk
measures. Finite separation products formulate uniform pseudohyperbolic separation.
The interpolation interfaces include Carleson's sequence criterion, positivity of
finite Nevanlinna–Pick matrices, and the finite corona theorem with uniform bounds.

Sources: GAPS 42.20, 42.24, 42.26 and 42.27.
-/

@[expose] public section

noncomputable section

namespace CKMA

open MeasureTheory
open scoped BigOperators ENNReal ComplexConjugate ComplexOrder

/-- A Carleson box above an angular arc of normalized length `ℓ`. -/
def carlesonBox (θ ℓ : ℝ) : Set ℂ :=
  {z | ∃ r t : ℝ, 1 - ℓ < r ∧ r < 1 ∧ θ ≤ t ∧ t ≤ θ + 2 * Real.pi * ℓ ∧
    z = (r : ℂ) * unitCirclePoint t}

/-- The Carleson box bound, retaining the measure on the disk as part of its intended support. -/
def IsDiskCarlesonMeasure (μ : Measure ℂ) : Prop :=
  IsFiniteMeasure μ ∧ μ complexUnitDiskᶜ = 0 ∧ ∃ C : ℝ, 0 < C ∧ ∀ θ ℓ : ℝ, 0 < ℓ → ℓ ≤ 1 →
    μ (carlesonBox θ ℓ) ≤ ENNReal.ofReal (C * ℓ)

/-- **42.20**: the Hardy embedding criterion for every finite positive exponent. -/
theorem carleson_embedding_iff (μ : Measure ℂ) [IsFiniteMeasure μ]
    (hμ : μ complexUnitDiskᶜ = 0) {p : ℝ} (hp : 0 < p) :
    IsDiskCarlesonMeasure μ ↔ ∃ C : ℝ, 0 < C ∧ ∀ f : ℂ → ℂ, MemHardyClass p f →
      (∫⁻ z, (ENNReal.ofReal ‖f z‖) ^ p ∂μ) ≤ ENNReal.ofReal C * (hardyGauge p f) ^ p := by
  sorry

/-- Pseudohyperbolic distance on the unit disk. -/
def pseudohyperbolicDistance (z w : ℂ) : ℝ := ‖(z - w) / (1 - conj w * z)‖

/-- Infinite separation product as an infimum of finite products, so no infinite-product
junk value can accidentally certify interpolation. -/
def diskSeparationProduct (a : ℕ → ℂ) (j : ℕ) : ℝ :=
  ⨅ F : Finset ℕ, ∏ k ∈ F.erase j, pseudohyperbolicDistance (a j) (a k)

/-- Interpolation of every uniformly bounded scalar sequence, with a common function bound. -/
def IsHardyInterpolatingSequence (a : ℕ → ℂ) : Prop :=
  (∀ n, a n ∈ complexUnitDisk) ∧ Function.Injective a ∧ ∃ C : ℝ, 0 < C ∧ ∀ b : ℕ → ℂ, (∀ n, ‖b n‖ ≤
    1) →
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f complexUnitDisk ∧
      diskSupGauge f ≤ ENNReal.ofReal C ∧ ∀ n, f (a n) = b n

/-- **42.24**: Carleson's uniform separation criterion. -/
theorem carleson_interpolation_iff (a : ℕ → ℂ) (ha : ∀ n, a n ∈ complexUnitDisk)
    (hinj : Function.Injective a) :
    IsHardyInterpolatingSequence a ↔ ∃ δ : ℝ, 0 < δ ∧ ∀ j, δ ≤ diskSeparationProduct a j := by
  sorry

/-- The finite Nevanlinna–Pick matrix. -/
def pickMatrix {n : ℕ} (z w : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j ↦ (1 - w i * conj (w j)) / (1 - z i * conj (z j))

/-- **42.26**: Pick positivity characterizes contractive finite interpolation, including empty data.
  -/
theorem nevanlinna_pick {n : ℕ} (z w : Fin n → ℂ)
    (hz : ∀ i, z i ∈ complexUnitDisk) (hinj : Function.Injective z) :
    (∃ f : ℂ → ℂ, DifferentiableOn ℂ f complexUnitDisk ∧ diskSupGauge f ≤ 1 ∧
      ∀ i, f (z i) = w i) ↔ (pickMatrix z w).PosSemidef := by
  sorry

/-- **42.27**: the finite corona theorem, with a bound depending only on `n`, `δ` and `M`. -/
theorem disk_corona (n : ℕ) (hn : 0 < n) {δ M : ℝ} (hδ : 0 < δ) (hM : 0 < M) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : Fin n → ℂ → ℂ,
      (∀ j, DifferentiableOn ℂ (f j) complexUnitDisk) →
      (∀ j, diskSupGauge (f j) ≤ ENNReal.ofReal M) →
      (∀ z ∈ complexUnitDisk, δ ≤ ∑ j, ‖f j z‖) →
      ∃ g : Fin n → ℂ → ℂ,
        (∀ j, DifferentiableOn ℂ (g j) complexUnitDisk) ∧
        (∀ j, diskSupGauge (g j) ≤ ENNReal.ofReal C) ∧
        ∀ z ∈ complexUnitDisk, (∑ j, f j z * g j z) = 1 := by
  sorry

end CKMA
