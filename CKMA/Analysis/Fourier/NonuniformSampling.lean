/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.Fourier.Sampling.Band
public import CKMA.Analysis.InnerProductSpace.Basic

/-!
# Nonuniform band sampling

Normalized frequency-interval exponentials give Kadec's one-quarter perturbation
criterion and its sharpness. Uniformly separated sample families have lower and upper
Beurling densities defined by interval counts. Stable sampling and bounded L²
interpolation of inverse-integral bandlimited representatives obey Landau's necessary
density bounds at bandwidth `[-B,B]`.

Sources: GAPS 29.61 and 29.62.

## Main definitions

* `CKMA.samplingExponential`: normalized exponential `(2B)⁻¹/² exp(-2πi λ ξ)` on `[-B, B]`.
* `CKMA.IsUniformlySeparatedSamples`: positive minimum separation between distinct sample points.
* `CKMA.sampleCount`, `CKMA.lowerSampleDensity`, `CKMA.upperSampleDensity`: sample counting and
  lower/upper uniform Beurling densities.
* `CKMA.HasFrequencyBand`: spectral support inside `[-B, B]`.
* `CKMA.IsStableBandSampling`, `CKMA.IsStableBandInterpolation`: stable sampling and interpolation
  predicates for bandlimited functions.

## Main results

* `CKMA.kadec_oneQuarter`: Kadec's `1/4` perturbation theorem for exponential Riesz bases
  (**29.61**).
* `CKMA.kadec_oneQuarter_sharp`: sharpness of the `1/4` threshold in Kadec's theorem.
* `CKMA.landau_sampling_density`, `CKMA.landau_interpolation_density`: Landau's necessary Beurling
  density bounds for stable sampling and interpolation (**29.62**).
-/

public section

noncomputable section

namespace CKMA

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal

/-- The normalized frequency-interval exponential at sampling location lambda. -/
@[expose]
def samplingExponential (B : ℝ) (samples : ℝ) (ξ : ℝ) : ℂ :=
  (Real.sqrt (2 * B) : ℂ)⁻¹ * Complex.exp (-2 * Real.pi * Complex.I * samples * ξ)

/-- Unfolding the normalized exponential. -/
theorem samplingExponential_def (B samples ξ : ℝ) :
    samplingExponential B samples ξ =
      (Real.sqrt (2 * B) : ℂ)⁻¹ * Complex.exp (-2 * Real.pi * Complex.I * samples * ξ) := rfl

/-- **29.61**, Kadec's one-quarter theorem at bandwidth `B`: if `|2B λₖ - k| ≤ δ < 1/4` for all
`k`, the normalized exponentials `exp(-2πi λₖ ξ)` form a Riesz basis of `L²[-B, B]`. -/
theorem kadec_oneQuarter {B : ℝ} (hB : 0 < B) (samples : ℤ → ℝ)
    (hsamples : ∃ δ < 1 / 4, ∀ k : ℤ, |2 * B * samples k - k| ≤ δ) :
    IsL2RieszBasis (volume.restrict (Set.Icc (-B) B))
      (fun k ↦ samplingExponential B (samples k)) := by
  sorry

/-- Sharpness of Kadec's threshold: for every `c > 1/4` some perturbation with
`|λₖ - k| < c` fails to give a Riesz basis of `L²[-1/2, 1/2]`. -/
theorem kadec_oneQuarter_sharp {c : ℝ} (hc : 1 / 4 < c) :
    ∃ samples : ℤ → ℝ, (∀ k : ℤ, |samples k - k| < c) ∧
      ¬ IsL2RieszBasis (volume.restrict (Set.Icc (-1 / 2 : ℝ) (1 / 2)))
        (fun k ↦ samplingExponential (1 / 2) (samples k)) := by
  sorry

/-- Uniform separation of a sample family; it also implies that the indexing is injective. -/
@[expose]
def IsUniformlySeparatedSamples {ι : Type*} (samples : ι → ℝ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ i j, i ≠ j → δ ≤ dist (samples i) (samples j)

/-- Unfolding uniform separation. -/
theorem isUniformlySeparatedSamples_iff {ι : Type*} {samples : ι → ℝ} :
    IsUniformlySeparatedSamples samples ↔
      ∃ δ : ℝ, 0 < δ ∧ ∀ i j, i ≠ j → δ ≤ dist (samples i) (samples j) := Iff.rfl

/-- A uniformly separated sample family is injective. -/
theorem IsUniformlySeparatedSamples.injective {ι : Type*} {samples : ι → ℝ}
    (h : IsUniformlySeparatedSamples samples) : Function.Injective samples := by
  obtain ⟨δ, hδ, hsep⟩ := h
  intro i j hij
  by_contra hne
  have := hsep i j hne
  rw [hij, dist_self] at this
  exact (lt_irrefl _ (hδ.trans_le this))

/-- Sample counting on a closed interval. Under uniform separation this cardinal is finite.
Outside the locally finite regime, `Set.ncard` assigns zero to infinite sets. -/
@[expose]
def sampleCount {ι : Type*} (samples : ι → ℝ) (x R : ℝ) : ℕ :=
  (Set.range samples ∩ Set.Icc x (x + R)).ncard

/-- Unfolding the sample count. -/
theorem sampleCount_def {ι : Type*} (samples : ι → ℝ) (x R : ℝ) :
    sampleCount samples x R = (Set.range samples ∩ Set.Icc x (x + R)).ncard := rfl

/-- Lower uniform Beurling density for locally finite sample sets.
The Landau targets impose uniform separation. -/
@[expose]
def lowerSampleDensity {ι : Type*} (samples : ι → ℝ) : ℝ≥0∞ :=
  liminf (fun R : ℝ ↦ ⨅ x : ℝ, ENNReal.ofReal (sampleCount samples x R / R)) atTop

/-- Unfolding the lower density. -/
theorem lowerSampleDensity_def {ι : Type*} (samples : ι → ℝ) :
    lowerSampleDensity samples =
      liminf (fun R : ℝ ↦ ⨅ x : ℝ, ENNReal.ofReal (sampleCount samples x R / R)) atTop := rfl

/-- Upper uniform Beurling density for locally finite sample sets. -/
@[expose]
def upperSampleDensity {ι : Type*} (samples : ι → ℝ) : ℝ≥0∞ :=
  limsup (fun R : ℝ ↦ ⨆ x : ℝ, ENNReal.ofReal (sampleCount samples x R / R)) atTop

/-- Unfolding the upper density. -/
theorem upperSampleDensity_def {ι : Type*} (samples : ι → ℝ) :
    upperSampleDensity samples =
      limsup (fun R : ℝ ↦ ⨆ x : ℝ, ENNReal.ofReal (sampleCount samples x R / R)) atTop := rfl

/-- Spectral support in the band [-B,B], interpreted almost everywhere. -/
@[expose]
def HasFrequencyBand (B : ℝ) (u : Lp ℂ 2 (volume : Measure ℝ)) : Prop :=
  ∀ᵐ ξ ∂volume, ξ ∉ Set.Icc (-B) B → u ξ = 0

/-- Unfolding the band condition. -/
theorem hasFrequencyBand_iff {B : ℝ} {u : Lp ℂ 2 (volume : Measure ℝ)} :
    HasFrequencyBand B u ↔ ∀ᵐ ξ ∂volume, ξ ∉ Set.Icc (-B) B → u ξ = 0 := Iff.rfl

/-- The band condition is monotone in the bandwidth. -/
theorem HasFrequencyBand.mono {B B' : ℝ} {u : Lp ℂ 2 (volume : Measure ℝ)}
    (h : HasFrequencyBand B u) (hB : B ≤ B') : HasFrequencyBand B' u := by
  filter_upwards [h] with ξ hξ hξ'
  exact hξ fun hm ↦ hξ' ⟨(neg_le_neg hB).trans hm.1, hm.2.trans hB⟩

/-- Stable sampling for all inverse-integral bandlimited representatives. -/
@[expose]
def IsStableBandSampling {ι : Type*} (B : ℝ) (samples : ι → ℝ) : Prop :=
  ∃ A C : ℝ, 0 < A ∧ A ≤ C ∧ ∀ u : Lp ℂ 2 (volume : Measure ℝ),
    HasFrequencyBand B u →
    ENNReal.ofReal (A * ‖u‖ ^ 2) ≤
      (∑' i, ENNReal.ofReal (‖bandlimitedRepresentative B u (samples i)‖ ^ 2)) ∧
    (∑' i, ENNReal.ofReal (‖bandlimitedRepresentative B u (samples i)‖ ^ 2)) ≤
      ENNReal.ofReal (C * ‖u‖ ^ 2)

/-- Unfolding stable sampling. -/
theorem isStableBandSampling_iff {ι : Type*} {B : ℝ} {samples : ι → ℝ} :
    IsStableBandSampling B samples ↔ ∃ A C : ℝ, 0 < A ∧ A ≤ C ∧
      ∀ u : Lp ℂ 2 (volume : Measure ℝ), HasFrequencyBand B u →
        ENNReal.ofReal (A * ‖u‖ ^ 2) ≤
          (∑' i, ENNReal.ofReal (‖bandlimitedRepresentative B u (samples i)‖ ^ 2)) ∧
        (∑' i, ENNReal.ofReal (‖bandlimitedRepresentative B u (samples i)‖ ^ 2)) ≤
          ENNReal.ofReal (C * ‖u‖ ^ 2) := Iff.rfl

/-- Stable interpolation means bounded solvability for all l2 data. -/
@[expose]
def IsStableBandInterpolation {ι : Type*} (B : ℝ) (samples : ι → ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ c : lp (fun _ : ι ↦ ℂ) 2,
    ∃ u : Lp ℂ 2 (volume : Measure ℝ), HasFrequencyBand B u ∧
      (∀ i, bandlimitedRepresentative B u (samples i) = c i) ∧ ‖u‖ ≤ C * ‖c‖

/-- Unfolding stable interpolation. -/
theorem isStableBandInterpolation_iff {ι : Type*} {B : ℝ} {samples : ι → ℝ} :
    IsStableBandInterpolation B samples ↔ ∃ C : ℝ, 0 < C ∧ ∀ c : lp (fun _ : ι ↦ ℂ) 2,
      ∃ u : Lp ℂ 2 (volume : Measure ℝ), HasFrequencyBand B u ∧
        (∀ i, bandlimitedRepresentative B u (samples i) = c i) ∧ ‖u‖ ≤ C * ‖c‖ := Iff.rfl

/-- **29.62**: a uniformly separated stable sampling family for the band `[-B, B]` has lower
Beurling density at least `2B` (Landau). -/
theorem landau_sampling_density {ι : Type*} {B : ℝ} (hB : 0 < B) (samples : ι → ℝ)
    (hs : IsUniformlySeparatedSamples samples) (hf : IsStableBandSampling B samples) :
    ENNReal.ofReal (2 * B) ≤ lowerSampleDensity samples := by
  sorry

/-- A uniformly separated stable interpolation family for the band `[-B, B]` has upper Beurling
density at most `2B` (Landau). -/
theorem landau_interpolation_density {ι : Type*} {B : ℝ} (hB : 0 < B) (samples : ι → ℝ)
    (hs : IsUniformlySeparatedSamples samples) (hf : IsStableBandInterpolation B samples) :
    upperSampleDensity samples ≤ ENNReal.ofReal (2 * B) := by
  sorry

end CKMA
