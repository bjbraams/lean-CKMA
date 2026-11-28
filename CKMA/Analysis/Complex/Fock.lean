/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Defs

/-!
# Fock sampling and uniform planar density

Entire functions are measured in Gaussian-weighted L² area with parameter `α > 0`.
Separated planar sets have lower and upper uniform densities defined through extended
node counts. Stable weighted point sampling is characterized by lower uniform density
strictly greater than `α/π`.

Source: GAPS 42.82.

## Main definitions

* `CKMA.fockMeasure`, `CKMA.MemFockClass`, `CKMA.fockEnergy`: Gaussian area measure, Fock space
  membership, and Fock energy.
* `CKMA.IsPlanarSeparated`, `CKMA.planarNodeCount`: uniform separation and ball node count.
* `CKMA.lowerPlanarDensity`, `CKMA.upperPlanarDensity`: lower and upper Beurling planar densities.
* `CKMA.fockSamplingEnergy`: discrete Gaussian-weighted sampling energy.

## Main results

* `CKMA.fock_sampling_iff`: Seip–Wallstén density characterization of Fock sampling sets.
-/

public section

noncomputable section

namespace CKMA

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal

/-- The normalized Gaussian area measure for Fock space. -/
@[expose]
def fockMeasure (α : ℝ) : Measure ℂ :=
  volume.withDensity (fun z ↦ ENNReal.ofReal ((α / Real.pi) * Real.exp (-α * ‖z‖ ^ 2)))

/-- The Fock measure has density `(α / π) e^{-α |z|²}` with respect to area. -/
theorem fockMeasure_def (α : ℝ) : fockMeasure α =
    volume.withDensity (fun z ↦ ENNReal.ofReal ((α / Real.pi) * Real.exp (-α * ‖z‖ ^ 2))) :=
  rfl

/-- Entire Gaussian-square-integrable functions. -/
@[expose]
def MemFockClass (α : ℝ) (f : ℂ → ℂ) : Prop :=
  Differentiable ℂ f ∧ MemLp f 2 (fockMeasure α)

/-- Fock-space membership is entirety with square integrability for the Fock measure. -/
theorem memFockClass_iff {α : ℝ} {f : ℂ → ℂ} :
    MemFockClass α f ↔ Differentiable ℂ f ∧ MemLp f 2 (fockMeasure α) :=
  Iff.rfl

/-- Fock square energy, preserving infinite values. -/
@[expose]
def fockEnergy (α : ℝ) (f : ℂ → ℂ) : ℝ≥0∞ :=
  ∫⁻ z, ENNReal.ofReal (‖f z‖ ^ 2) ∂fockMeasure α

/-- The Fock energy is the lower integral of `‖f‖²` against the Fock measure. -/
theorem fockEnergy_def (α : ℝ) (f : ℂ → ℂ) :
    fockEnergy α f = ∫⁻ z, ENNReal.ofReal (‖f z‖ ^ 2) ∂fockMeasure α :=
  rfl

/-- A uniformly separated planar set. -/
@[expose]
def IsPlanarSeparated (Λ : Set ℂ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ Λ, ∀ w ∈ Λ, z ≠ w → δ ≤ dist z w

/-- A set is separated when distinct points are at least a fixed positive distance apart. -/
theorem isPlanarSeparated_iff {Λ : Set ℂ} :
    IsPlanarSeparated Λ ↔ ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ Λ, ∀ w ∈ Λ, z ≠ w → δ ≤ dist z w :=
  Iff.rfl

/-- Planar counting with value `∞` if infinitely many nodes occur in a ball. -/
@[expose]
def planarNodeCount (Λ : Set ℂ) (c : ℂ) (r : ℝ) : ℝ≥0∞ :=
  ∑' z : Λ, if ‖z.1 - c‖ < r then 1 else 0

/-- The node count is the extended number of points of `Λ` in the open ball of radius `r`. -/
theorem planarNodeCount_def (Λ : Set ℂ) (c : ℂ) (r : ℝ) :
    planarNodeCount Λ c r = ∑' z : Λ, if ‖z.1 - c‖ < r then 1 else 0 :=
  rfl

/-- Lower uniform planar density, using a liminf rather than an assumed limit. -/
@[expose]
def lowerPlanarDensity (Λ : Set ℂ) : ℝ≥0∞ :=
  liminf (fun r : ℝ ↦ ⨅ c : ℂ, planarNodeCount Λ c r / ENNReal.ofReal (Real.pi * r ^ 2)) atTop

/-- The lower density is the `liminf` of the smallest normalized node count in balls of radius
`r`. -/
theorem lowerPlanarDensity_def (Λ : Set ℂ) : lowerPlanarDensity Λ =
    liminf (fun r : ℝ ↦ ⨅ c : ℂ, planarNodeCount Λ c r / ENNReal.ofReal (Real.pi * r ^ 2)) atTop :=
  rfl

/-- Upper uniform planar density. -/
@[expose]
def upperPlanarDensity (Λ : Set ℂ) : ℝ≥0∞ :=
  limsup (fun r : ℝ ↦ ⨆ c : ℂ, planarNodeCount Λ c r / ENNReal.ofReal (Real.pi * r ^ 2)) atTop

/-- The upper density is the `limsup` of the largest normalized node count in balls of radius
`r`. -/
theorem upperPlanarDensity_def (Λ : Set ℂ) : upperPlanarDensity Λ =
    limsup (fun r : ℝ ↦ ⨆ c : ℂ, planarNodeCount Λ c r / ENNReal.ofReal (Real.pi * r ^ 2)) atTop :=
  rfl

/-- The weighted discrete sampling square norm. -/
@[expose]
def fockSamplingEnergy (α : ℝ) (Λ : Set ℂ) (f : ℂ → ℂ) : ℝ≥0∞ :=
  ∑' z : Λ, ENNReal.ofReal (‖f z.1‖ ^ 2 * Real.exp (-α * ‖z.1‖ ^ 2))

/-- The sampling energy is the weighted sum of `‖f‖²` over the nodes. -/
theorem fockSamplingEnergy_def (α : ℝ) (Λ : Set ℂ) (f : ℂ → ℂ) : fockSamplingEnergy α Λ f =
    ∑' z : Λ, ENNReal.ofReal (‖f z.1‖ ^ 2 * Real.exp (-α * ‖z.1‖ ^ 2)) :=
  rfl

/-- **42.82**: strict lower-density characterization of Fock sampling on separated sets. -/
theorem fock_sampling_iff {α : ℝ} (hα : 0 < α) {Λ : Set ℂ} (hΛ : IsPlanarSeparated Λ) :
    (∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ f : ℂ → ℂ, MemFockClass α f →
      ENNReal.ofReal A * fockEnergy α f ≤ fockSamplingEnergy α Λ f ∧
      fockSamplingEnergy α Λ f ≤ ENNReal.ofReal B * fockEnergy α f) ↔
      ENNReal.ofReal (α / Real.pi) < lowerPlanarDensity Λ := by
  sorry

end CKMA
