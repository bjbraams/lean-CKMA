/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.Complex.Hardy
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Fock sampling and uniform planar density

Entire functions are measured in Gaussian-weighted L² area with parameter `α > 0`.
Separated planar sets have lower and upper uniform densities defined through extended
node counts. Stable weighted point sampling is characterized by lower uniform density
strictly greater than `α/π`.

Source: GAPS 42.82.
-/

@[expose] public section

noncomputable section

namespace CKMA

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal

/-- The normalized Gaussian area measure for Fock space. -/
def fockMeasure (α : ℝ) : Measure ℂ :=
  volume.withDensity (fun z ↦ ENNReal.ofReal ((α / Real.pi) * Real.exp (-α * ‖z‖ ^ 2)))

/-- Entire Gaussian-square-integrable functions. -/
def MemFockClass (α : ℝ) (f : ℂ → ℂ) : Prop :=
  Differentiable ℂ f ∧ MemLp f 2 (fockMeasure α)

/-- Fock square energy, preserving infinite values. -/
def fockEnergy (α : ℝ) (f : ℂ → ℂ) : ℝ≥0∞ :=
  ∫⁻ z, ENNReal.ofReal (‖f z‖ ^ 2) ∂fockMeasure α

/-- A uniformly separated planar set. -/
def IsPlanarSeparated (Λ : Set ℂ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ Λ, ∀ w ∈ Λ, z ≠ w → δ ≤ dist z w

/-- Planar counting with value `∞` if infinitely many nodes occur in a ball. -/
def planarNodeCount (Λ : Set ℂ) (c : ℂ) (r : ℝ) : ℝ≥0∞ :=
  ∑' z : Λ, if ‖z.1 - c‖ < r then 1 else 0

/-- Lower uniform planar density, using a liminf rather than an assumed limit. -/
def lowerPlanarDensity (Λ : Set ℂ) : ℝ≥0∞ :=
  liminf (fun r : ℝ ↦ ⨅ c : ℂ, planarNodeCount Λ c r / ENNReal.ofReal (Real.pi * r ^ 2)) atTop

/-- Upper uniform planar density. -/
def upperPlanarDensity (Λ : Set ℂ) : ℝ≥0∞ :=
  limsup (fun r : ℝ ↦ ⨆ c : ℂ, planarNodeCount Λ c r / ENNReal.ofReal (Real.pi * r ^ 2)) atTop

/-- The weighted discrete sampling square norm. -/
def fockSamplingEnergy (α : ℝ) (Λ : Set ℂ) (f : ℂ → ℂ) : ℝ≥0∞ :=
  ∑' z : Λ, ENNReal.ofReal (‖f z.1‖ ^ 2 * Real.exp (-α * ‖z.1‖ ^ 2))

/-- **42.82**: strict lower-density characterization of Fock sampling on separated sets. -/
theorem fock_sampling_iff {α : ℝ} (hα : 0 < α) {Λ : Set ℂ} (hΛ : IsPlanarSeparated Λ) :
    (∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ f : ℂ → ℂ, MemFockClass α f →
      ENNReal.ofReal A * fockEnergy α f ≤ fockSamplingEnergy α Λ f ∧
      fockSamplingEnergy α Λ f ≤ ENNReal.ofReal B * fockEnergy α f) ↔
      ENNReal.ofReal (α / Real.pi) < lowerPlanarDensity Λ := by
  sorry

end CKMA
