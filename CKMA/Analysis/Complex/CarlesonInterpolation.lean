/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.Complex.Hardy

/-!
# Carleson measures and bounded disk interpolation

Carleson box bounds characterize embeddings of analytic Hardy classes into disk
measures. Finite separation products formulate uniform pseudohyperbolic separation.
The interpolation interfaces include Carleson's sequence criterion, positivity of
finite Nevanlinna–Pick matrices, and the finite corona theorem with uniform bounds.

Sources: GAPS 42.20, 42.24, 42.26 and 42.27.

## Main definitions

* `CKMA.carlesonBox`: Carleson box on the unit disk.
* `CKMA.IsDiskCarlesonMeasure`: Carleson measure on the open unit disk.
* `CKMA.pseudohyperbolicDistance`, `CKMA.diskSeparationProduct`: pseudohyperbolic metric and
  Blaschke separation product.
* `CKMA.IsHardyInterpolatingSequence`: `H^∞` interpolating sequence in the unit disk.
* `CKMA.pickMatrix`: Nevanlinna–Pick interpolation matrix.

## Main results

* `CKMA.carleson_embedding_iff`: Carleson's theorem on `Hᵖ` embedding into `Lᵖ(μ)`.
* `CKMA.carleson_interpolation_iff`: Carleson's uniform separation criterion for `H^∞`
  interpolation.
* `CKMA.nevanlinna_pick`: Nevanlinna–Pick interpolation theorem.
* `CKMA.disk_corona`: Carleson's corona theorem on the unit disk.
-/

public section

noncomputable section

namespace CKMA

open MeasureTheory
open scoped BigOperators ENNReal ComplexConjugate ComplexOrder

/-- A Carleson box above an angular arc of normalized length `ℓ`. -/
@[expose]
def carlesonBox (θ ℓ : ℝ) : Set ℂ :=
  {z | ∃ r t : ℝ, 1 - ℓ < r ∧ r < 1 ∧ θ ≤ t ∧ t ≤ θ + 2 * Real.pi * ℓ ∧
    z = (r : ℂ) * unitCirclePoint t}

/-- Membership in a Carleson box: radius in `(1 - ℓ, 1)` and angle in `[θ, θ + 2πℓ]`. -/
theorem mem_carlesonBox {θ ℓ : ℝ} {z : ℂ} : z ∈ carlesonBox θ ℓ ↔
    ∃ r t : ℝ, 1 - ℓ < r ∧ r < 1 ∧ θ ≤ t ∧ t ≤ θ + 2 * Real.pi * ℓ ∧
      z = (r : ℂ) * unitCirclePoint t :=
  Iff.rfl

/-- The Carleson box bound, retaining the measure on the disk as part of its intended support. -/
@[expose]
def IsDiskCarlesonMeasure (μ : Measure ℂ) : Prop :=
  IsFiniteMeasure μ ∧ μ complexUnitDiskᶜ = 0 ∧ ∃ C : ℝ, 0 < C ∧ ∀ θ ℓ : ℝ, 0 < ℓ → ℓ ≤ 1 →
    μ (carlesonBox θ ℓ) ≤ ENNReal.ofReal (C * ℓ)

/-- A Carleson measure is finite, carried by the disk, and bounded by `C ℓ` on boxes of size `ℓ`.
-/
theorem isDiskCarlesonMeasure_iff {μ : Measure ℂ} : IsDiskCarlesonMeasure μ ↔
    IsFiniteMeasure μ ∧ μ complexUnitDiskᶜ = 0 ∧ ∃ C : ℝ, 0 < C ∧ ∀ θ ℓ : ℝ, 0 < ℓ → ℓ ≤ 1 →
      μ (carlesonBox θ ℓ) ≤ ENNReal.ofReal (C * ℓ) :=
  Iff.rfl

/-- **42.20**: the Hardy embedding criterion for every finite positive exponent. -/
theorem carleson_embedding_iff (μ : Measure ℂ) {p : ℝ} (hp : 0 < p) :
    IsDiskCarlesonMeasure μ ↔ ∃ C : ℝ, 0 < C ∧ ∀ f : ℂ → ℂ, MemHardyClass p f →
      (∫⁻ z, (ENNReal.ofReal ‖f z‖) ^ p ∂μ) ≤ ENNReal.ofReal C * (hardyGauge p f) ^ p := by
  sorry

/-- Pseudohyperbolic distance on the unit disk. -/
@[expose]
def pseudohyperbolicDistance (z w : ℂ) : ℝ := ‖(z - w) / (1 - conj w * z)‖

/-- The pseudohyperbolic distance is `|(z - w) / (1 - w̄ z)|`. -/
theorem pseudohyperbolicDistance_def (z w : ℂ) :
    pseudohyperbolicDistance z w = ‖(z - w) / (1 - conj w * z)‖ :=
  rfl

/-- Infinite separation product as an infimum of finite products, so no infinite-product
junk value can accidentally certify interpolation. -/
@[expose]
def diskSeparationProduct (a : ℕ → ℂ) (j : ℕ) : ℝ :=
  ⨅ F : Finset ℕ, ∏ k ∈ F.erase j, pseudohyperbolicDistance (a j) (a k)

/-- The separation product is the infimum of the finite products of distances to the other
points. -/
theorem diskSeparationProduct_def (a : ℕ → ℂ) (j : ℕ) : diskSeparationProduct a j =
    ⨅ F : Finset ℕ, ∏ k ∈ F.erase j, pseudohyperbolicDistance (a j) (a k) :=
  rfl

/-- Interpolation of every uniformly bounded scalar sequence, with a common function bound. -/
@[expose]
def IsHardyInterpolatingSequence (a : ℕ → ℂ) : Prop :=
  (∀ n, a n ∈ complexUnitDisk) ∧ Function.Injective a ∧ ∃ C : ℝ, 0 < C ∧
    ∀ b : ℕ → ℂ, (∀ n, ‖b n‖ ≤ 1) → ∃ f : ℂ → ℂ, DifferentiableOn ℂ f complexUnitDisk ∧
      diskSupGauge f ≤ ENNReal.ofReal C ∧ ∀ n, f (a n) = b n

/-- An interpolating sequence is an injective sequence in the disk on which every sequence
bounded by one is interpolated by a holomorphic function with a common bound. -/
theorem isHardyInterpolatingSequence_iff {a : ℕ → ℂ} : IsHardyInterpolatingSequence a ↔
    (∀ n, a n ∈ complexUnitDisk) ∧ Function.Injective a ∧ ∃ C : ℝ, 0 < C ∧
      ∀ b : ℕ → ℂ, (∀ n, ‖b n‖ ≤ 1) → ∃ f : ℂ → ℂ, DifferentiableOn ℂ f complexUnitDisk ∧
        diskSupGauge f ≤ ENNReal.ofReal C ∧ ∀ n, f (a n) = b n :=
  Iff.rfl

/-- **42.24**: Carleson's uniform separation criterion. -/
theorem carleson_interpolation_iff (a : ℕ → ℂ) (ha : ∀ n, a n ∈ complexUnitDisk)
    (hinj : Function.Injective a) :
    IsHardyInterpolatingSequence a ↔ ∃ δ : ℝ, 0 < δ ∧ ∀ j, δ ≤ diskSeparationProduct a j := by
  sorry

/-- The finite Nevanlinna–Pick matrix. -/
@[expose]
def pickMatrix {n : ℕ} (z w : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j ↦ (1 - w i * conj (w j)) / (1 - z i * conj (z j))

/-- The Pick matrix entries are `(1 - wᵢ w̄ⱼ) / (1 - zᵢ z̄ⱼ)`. -/
@[simp]
theorem pickMatrix_apply {n : ℕ} (z w : Fin n → ℂ) (i j : Fin n) :
    pickMatrix z w i j = (1 - w i * conj (w j)) / (1 - z i * conj (z j)) :=
  rfl

/-- **42.26**: Pick positivity characterizes contractive finite interpolation, including empty data.
  -/
theorem nevanlinna_pick {n : ℕ} (z w : Fin n → ℂ)
    (hz : ∀ i, z i ∈ complexUnitDisk) (hinj : Function.Injective z) :
    (∃ f : ℂ → ℂ, DifferentiableOn ℂ f complexUnitDisk ∧ diskSupGauge f ≤ 1 ∧
      ∀ i, f (z i) = w i) ↔ (pickMatrix z w).PosSemidef := by
  sorry

/-- **42.27**: the finite corona theorem, with a bound depending only on `n`, `δ` and `M`. For
`M ≤ 0` the hypotheses force every `f j` to vanish on the disk, so they are inconsistent. -/
theorem disk_corona (n : ℕ) {δ : ℝ} (M : ℝ) (hδ : 0 < δ) :
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
