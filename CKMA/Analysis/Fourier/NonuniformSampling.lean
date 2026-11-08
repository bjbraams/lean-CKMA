/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.Fourier.Sampling
public import CKMA.Analysis.InnerProductSpace.L2FunctionFamilies
public import Mathlib.Data.Set.Card

/-!
# Nonuniform band sampling

Normalized frequency-interval exponentials give Kadec's one-quarter perturbation
criterion and its sharpness. Uniformly separated sample families have lower and upper
Beurling densities defined by interval counts. Stable sampling and bounded L²
interpolation of inverse-integral bandlimited representatives obey Landau's necessary
density bounds at bandwidth `[-B,B]`.

Sources: GAPS 29.61 and 29.62.
-/

@[expose] public section

noncomputable section

namespace CKMA

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal

/-- The normalized frequency-interval exponential at sampling location lambda. -/
def samplingExponential (B : ℝ) (samples : ℝ) (ξ : ℝ) : ℂ :=
  (Real.sqrt (2 * B) : ℂ)⁻¹ * Complex.exp (-2 * Real.pi * Complex.I * samples * ξ)

/-- **29.61**: Kadec's one-quarter theorem in its equivalent frequency-exponential form. -/
theorem kadec_oneQuarter {B : ℝ} (hB : 0 < B) (samples : ℤ → ℝ)
    (hsamples : ∃ δ : ℝ, 0 ≤ δ ∧ δ < 1 / 4 ∧ ∀ k : ℤ, |2 * B * samples k - k| ≤ δ) :
    IsL2RieszBasis (volume.restrict (Set.Icc (-B) B)) (fun k ↦ samplingExponential B (samples k)) :=
      by
  sorry

/-- No larger universal perturbation threshold can replace one quarter. -/
theorem kadec_oneQuarter_sharp {c : ℝ} (hc : 1 / 4 < c) :
    ∃ samples : ℤ → ℝ, (∀ k : ℤ, |samples k - k| < c) ∧
      ¬ IsL2RieszBasis (volume.restrict (Set.Icc (-1 / 2 : ℝ) (1 / 2)))
        (fun k ↦ samplingExponential (1 / 2) (samples k)) := by
  sorry

/-- Uniform separation of a sample family; it also implies that the indexing is injective. -/
def IsUniformlySeparatedSamples {ι : Type*} (samples : ι → ℝ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ i j, i ≠ j → δ ≤ dist (samples i) (samples j)

/-- Sample counting on a closed interval. Under uniform separation this cardinal is finite.
Outside the locally finite regime, `Set.ncard` assigns zero to infinite sets. -/
def sampleCount {ι : Type*} (samples : ι → ℝ) (x R : ℝ) : ℕ :=
  (Set.range samples ∩ Set.Icc x (x + R)).ncard

/-- Lower uniform Beurling density for locally finite sample sets.
The Landau targets impose uniform separation. -/
def lowerSampleDensity {ι : Type*} (samples : ι → ℝ) : ℝ≥0∞ :=
  liminf (fun R : ℝ ↦ ⨅ x : ℝ, ENNReal.ofReal (sampleCount samples x R / R)) atTop

/-- Upper uniform Beurling density for locally finite sample sets. -/
def upperSampleDensity {ι : Type*} (samples : ι → ℝ) : ℝ≥0∞ :=
  limsup (fun R : ℝ ↦ ⨆ x : ℝ, ENNReal.ofReal (sampleCount samples x R / R)) atTop

/-- Spectral support in the band [-B,B], interpreted almost everywhere. -/
def HasFrequencyBand (B : ℝ) (u : Lp ℂ 2 (volume : Measure ℝ)) : Prop :=
  ∀ᵐ ξ ∂volume, ξ ∉ Set.Icc (-B) B → u ξ = 0

/-- Stable sampling for all inverse-integral bandlimited representatives. -/
def IsStableBandSampling {ι : Type*} (B : ℝ) (samples : ι → ℝ) : Prop :=
  ∃ A C : ℝ, 0 < A ∧ A ≤ C ∧ ∀ u : Lp ℂ 2 (volume : Measure ℝ),
    HasFrequencyBand B u →
    ENNReal.ofReal (A * ‖u‖ ^ 2) ≤
      (∑' i, ENNReal.ofReal (‖bandlimitedRepresentative B u (samples i)‖ ^ 2)) ∧
    (∑' i, ENNReal.ofReal (‖bandlimitedRepresentative B u (samples i)‖ ^ 2)) ≤
      ENNReal.ofReal (C * ‖u‖ ^ 2)

/-- Stable interpolation means bounded solvability for all l2 data. -/
def IsStableBandInterpolation {ι : Type*} (B : ℝ) (samples : ι → ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ c : lp (fun _ : ι ↦ ℂ) 2,
    ∃ u : Lp ℂ 2 (volume : Measure ℝ), HasFrequencyBand B u ∧
      (∀ i, bandlimitedRepresentative B u (samples i) = c i) ∧ ‖u‖ ≤ C * ‖c‖

/-- **29.62**: Landau's necessary lower density for stable sampling. -/
theorem landau_sampling_density {ι : Type*} {B : ℝ} (hB : 0 < B) (samples : ι → ℝ)
    (hs : IsUniformlySeparatedSamples samples) (hf : IsStableBandSampling B samples) :
    ENNReal.ofReal (2 * B) ≤ lowerSampleDensity samples := by
  sorry

/-- The necessary upper density for stable interpolation. -/
theorem landau_interpolation_density {ι : Type*} {B : ℝ} (hB : 0 < B) (samples : ι → ℝ)
    (hs : IsUniformlySeparatedSamples samples) (hf : IsStableBandInterpolation B samples) :
    upperSampleDensity samples ≤ ENNReal.ofReal (2 * B) := by
  sorry

end CKMA
