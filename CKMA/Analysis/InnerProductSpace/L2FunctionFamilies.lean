/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import CKMA.Analysis.InnerProductSpace.Frame
public import Mathlib.Data.Finsupp.Basic

/-!
# L2 function families, Riesz bounds, and frame bounds

Finite linear combinations use finitely supported coefficients. Riesz bounds compare their L2
energy with coefficient l2 energy; completeness is tested by vanishing integral coefficients
against every L2 vector. Family membership in L2 is explicit in the Riesz and frame predicates.

The integral coefficients use conjugation on the family element, agreeing with Mathlib's
second-variable-linear L2 inner product. Actual function representatives are separated from their
a.e. equivalence classes, and frame energies are extended nonnegative sums over arbitrary indices.
-/

@[expose] public section

noncomputable section

namespace CKMA

open MeasureTheory
open scoped BigOperators ENNReal ComplexConjugate

/-- The canonical L2 vectors associated with a family of square-integrable representatives. -/
def l2FamilyVectors {X ι : Type*} [MeasurableSpace X] {μ : Measure X}
    (f : ι → X → ℂ) (hf : ∀ i, MemLp (f i) 2 μ) : ι → Lp ℂ 2 μ :=
  fun i ↦ (hf i).toLp (f i)

/-- Integral coefficients of a function family are its Hilbert-space inner products. -/
theorem inner_l2FamilyVectors {X ι : Type*} [MeasurableSpace X] {μ : Measure X}
    (f : ι → X → ℂ) (hf : ∀ i, MemLp (f i) 2 μ) (i : ι) (u : Lp ℂ 2 μ) :
    inner ℂ (l2FamilyVectors f hf i) u = ∫ x, conj (f i x) * u x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(hf i).coeFn_toLp] with x hx
  simp only [l2FamilyVectors] at *
  rw [hx]
  simp [mul_comm]

/-- A finite linear combination of a function family. -/
def l2FunctionCombination {X ι : Type*} (f : ι → X → ℂ) (c : ι →₀ ℂ) (x : X) : ℂ :=
  c.sum (fun i z ↦ z * f i x)

/-- Squared coefficient l2 size, as a nonnegative extended real. -/
def finiteCoefficientEnergy {ι : Type*} (c : ι →₀ ℂ) : ℝ≥0∞ :=
  c.sum (fun _ z ↦ ENNReal.ofReal (‖z‖ ^ 2))

/-- An L2 Riesz sequence, specified by uniform lower and upper finite-coefficient bounds. -/
def IsL2RieszSequence {X ι : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : ι → X → ℂ) : Prop :=
  (∀ i, MemLp (f i) 2 μ) ∧ ∃ A B : ℝ, 0 < A ∧ A ≤ B ∧ ∀ c : ι →₀ ℂ,
    ENNReal.ofReal A * finiteCoefficientEnergy c ≤ (eLpNorm (l2FunctionCombination f c) 2 μ) ^ 2 ∧
      (eLpNorm (l2FunctionCombination f c) 2 μ) ^ 2 ≤ ENNReal.ofReal B * finiteCoefficientEnergy c

/-- An orthogonality test on a function family: vanishing coefficients force a zero L2 class.
Square-integrability of the family itself is supplied separately in the Riesz/frame predicates. -/
def IsL2CompleteFamily {X ι : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : ι → X → ℂ) : Prop :=
  ∀ u : Lp ℂ 2 μ, (∀ i, ∫ x, conj (f i x) * u x ∂μ = 0) → u = 0

/-- A Riesz basis is a complete Riesz sequence. -/
def IsL2RieszBasis {X ι : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : ι → X → ℂ) : Prop :=
  IsL2RieszSequence μ f ∧ IsL2CompleteFamily μ f

/-- A Riesz basis has the finite-coefficient bounds of a Riesz sequence. -/
theorem IsL2RieszBasis.isRieszSequence {X ι : Type*} [MeasurableSpace X]
    {μ : Measure X} {f : ι → X → ℂ} (hf : IsL2RieszBasis μ f) : IsL2RieszSequence μ f := hf.1

/-- Frame inequalities for a family of actual measurable L2 representatives. -/
def IsL2FrameFamily {X ι : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : ι → X → ℂ) : Prop :=
  (∀ i, MemLp (f i) 2 μ) ∧ ∃ A B : ℝ, 0 < A ∧ A ≤ B ∧ ∀ u : Lp ℂ 2 μ,
    ENNReal.ofReal (A * ‖u‖ ^ 2) ≤
      (∑' i, ENNReal.ofReal (‖∫ x, conj (f i x) * u x ∂μ‖ ^ 2)) ∧
    (∑' i, ENNReal.ofReal (‖∫ x, conj (f i x) * u x ∂μ‖ ^ 2)) ≤
      ENNReal.ofReal (B * ‖u‖ ^ 2)

/-- The representative-based frame inequalities agree with the abstract Hilbert-frame predicate. -/
theorem isL2FrameFamily_iff_isFrame {X ι : Type*} [MeasurableSpace X] {μ : Measure X}
    (f : ι → X → ℂ) (hf : ∀ i, MemLp (f i) 2 μ) :
    IsL2FrameFamily μ f ↔ IsFrame (𝕜 := ℂ) (l2FamilyVectors f hf) := by
  constructor
  · rintro ⟨_, A, B, hA, hAB, h⟩
    exact ⟨A, B, hA, hAB, fun u ↦ by
      simpa only [frameEnergy, inner_l2FamilyVectors] using h u⟩
  · rintro ⟨A, B, hA, hAB, h⟩
    exact ⟨hf, A, B, hA, hAB, fun u ↦ by
      simpa only [frameEnergy, inner_l2FamilyVectors] using h u⟩

/-- Every Riesz basis is a frame in its whole Hilbert space. -/
theorem IsL2RieszBasis.isFrameFamily {X ι : Type*} [MeasurableSpace X]
    {μ : Measure X} {f : ι → X → ℂ} (hf : IsL2RieszBasis μ f) : IsL2FrameFamily μ f := by
  sorry

end CKMA
