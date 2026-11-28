/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.Complex.Basic
public import TauCeti.Analysis.Complex.Conformal.Schwarzian
public import TauCeti.Analysis.Complex.Laurent.Basic

/-!
# Schlicht functions and radial Loewner evolution

The normalized schlicht class is governed by the exterior area theorem, Koebe's
quarter theorem, sharp derivative distortion and de Branges's coefficient rigidity.
The Koebe function gives explicit quarter-radius sharpness by omitting `-1/4`.
TauCeti's Schwarzian derivative `TauCeti.schwarzian` gives Nehari's injectivity criterion.
Radial Loewner chains have nested univalent images and exponential derivative normalization;
their evolution is described by a measurable normalized Herglotz field. The exterior coefficient
energy uses TauCeti's circle Laurent coefficients `TauCeti.circleLaurentCoeff`.

Sources: GAPS 43.1, 43.3, 43.5, 43.8, 43.21 and 43.31.

## Main definitions

* `CKMA.IsSchlicht`: normalized univalent holomorphic functions on the unit disk.
* `CKMA.koebeFunction`, `CKMA.koebeRotation`: the Koebe function and its rotations.
* `CKMA.exteriorUnitDisk`, `CKMA.IsExteriorSchlicht`, `CKMA.exteriorCoefficientEnergy`: exterior
  schlicht class and Laurent area energy.
* `CKMA.IsRadialLoewnerChain`: radial Loewner subordination chains.

## Main results

* `CKMA.koebeFunction_zero`: the Koebe function vanishes at `0`.
* `CKMA.gronwall_area`: Grönwall's area theorem.
* `CKMA.koebe_quarter`, `CKMA.koebe_quarter_sharp`: Koebe's `1/4`-theorem and its sharpness.
* `CKMA.schlicht_derivative_distortion`: Koebe distortion theorem for derivatives.
* `CKMA.de_branges`: de Branges's theorem on the Bieberbach conjecture.
* `CKMA.nehari_univalent`: Nehari's univalence criterion via the Schwarzian derivative.
* `CKMA.loewner_kufarev`: Loewner–Kufarev differential equation for radial chains.
-/

public section

noncomputable section

namespace CKMA

open Filter Topology MeasureTheory
open scoped BigOperators ENNReal ComplexConjugate

/-- The normalized schlicht class on the unit disk. -/
@[expose]
def IsSchlicht (f : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ f complexUnitDisk ∧ Set.InjOn f complexUnitDisk ∧ f 0 = 0 ∧ deriv f 0 = 1

/-- A schlicht function is holomorphic and injective on the disk with `f 0 = 0`, `f' 0 = 1`. -/
theorem isSchlicht_iff {f : ℂ → ℂ} : IsSchlicht f ↔
    DifferentiableOn ℂ f complexUnitDisk ∧ Set.InjOn f complexUnitDisk ∧ f 0 = 0 ∧
      deriv f 0 = 1 :=
  Iff.rfl

/-- The Koebe extremal function. -/
@[expose]
def koebeFunction (z : ℂ) : ℂ := z / (1 - z) ^ 2

/-- `ζ⁻¹` times the Koebe function at `ζ * z`.
`ζ` is arbitrary. If `ζ = 0`, then `ζ⁻¹ = 0`, so the value is `0`.
If `‖ζ‖ = 1`, this is a rotation of `koebeFunction`. -/
@[expose]
def koebeRotation (ζ z : ℂ) : ℂ := ζ⁻¹ * koebeFunction (ζ * z)

/-- The Koebe function is `z / (1 - z) ^ 2`. -/
theorem koebeFunction_def (z : ℂ) : koebeFunction z = z / (1 - z) ^ 2 :=
  rfl

/-- The rotated Koebe function is `ζ⁻¹ k(ζ z)`. -/
theorem koebeRotation_def (ζ z : ℂ) : koebeRotation ζ z = ζ⁻¹ * koebeFunction (ζ * z) :=
  rfl

/-- The Koebe function vanishes at the origin. -/
theorem koebeFunction_zero : koebeFunction 0 = 0 := by
  simp [koebeFunction]

/-- The exterior disk. -/
@[expose]
def exteriorUnitDisk : Set ℂ := {z | 1 < ‖z‖}

/-- A point lies in the exterior disk exactly when its norm exceeds one. -/
theorem mem_exteriorUnitDisk {z : ℂ} : z ∈ exteriorUnitDisk ↔ 1 < ‖z‖ :=
  Iff.rfl

/-- Exterior schlicht functions, normalized to derivative one at infinity. -/
@[expose]
def IsExteriorSchlicht (g : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ g exteriorUnitDisk ∧ Set.InjOn g exteriorUnitDisk ∧
    ∃ b₀ : ℂ, Tendsto (fun z ↦ g z - z) (cocompact ℂ) (𝓝 b₀)

/-- An exterior schlicht function is holomorphic and injective on `1 < ‖z‖` with
`g z - z` convergent at infinity. -/
theorem isExteriorSchlicht_iff {g : ℂ → ℂ} : IsExteriorSchlicht g ↔
    DifferentiableOn ℂ g exteriorUnitDisk ∧ Set.InjOn g exteriorUnitDisk ∧
      ∃ b₀ : ℂ, Tendsto (fun z ↦ g z - z) (cocompact ℂ) (𝓝 b₀) :=
  Iff.rfl

/-- The nonnegative coefficient energy `∑ n |bₙ|²` in Grönwall's exterior area theorem, with the
Laurent coefficients `bₙ` of `g` at infinity taken on the circle of radius `2`. -/
@[expose]
def exteriorCoefficientEnergy (g : ℂ → ℂ) : ℝ≥0∞ :=
  ∑' n : ℕ, (n + 1 : ℝ≥0∞) *
    ENNReal.ofReal (‖TauCeti.circleLaurentCoeff g 0 2 (-((n + 1 : ℕ) : ℤ))‖ ^ 2)

/-- The coefficient energy is the weighted sum of the squared exterior Laurent coefficients. -/
theorem exteriorCoefficientEnergy_def (g : ℂ → ℂ) :
    exteriorCoefficientEnergy g = ∑' n : ℕ, (n + 1 : ℝ≥0∞) *
      ENNReal.ofReal (‖TauCeti.circleLaurentCoeff g 0 2 (-((n + 1 : ℕ) : ℤ))‖ ^ 2) :=
  rfl

/-- **43.1**: Grönwall's area theorem, with the actual omitted area. -/
theorem gronwall_area {g : ℂ → ℂ} (hg : IsExteriorSchlicht g) :
    exteriorCoefficientEnergy g ≤ 1 ∧
      volume (g '' exteriorUnitDisk)ᶜ = ENNReal.ofReal Real.pi * (1 - exteriorCoefficientEnergy g)
        := by
  sorry

/-- **43.3**: every normalized schlicht image contains the quarter disk. -/
theorem koebe_quarter {f : ℂ → ℂ} (hf : IsSchlicht f) :
    Metric.ball (0 : ℂ) (1 / 4) ⊆ f '' complexUnitDisk := by
  sorry

/-- Sharpness of the quarter radius, witnessed by the actual Koebe function. -/
theorem koebe_quarter_sharp : IsSchlicht koebeFunction ∧
    ∀ r : ℝ, 1 / 4 < r → ¬ Metric.ball (0 : ℂ) r ⊆ koebeFunction '' complexUnitDisk := by
  have hnorm : ∀ z ∈ complexUnitDisk, ‖z‖ < 1 := by
    intro z hz
    simpa only [complexUnitDisk, Metric.mem_ball, dist_zero_right] using hz
  have hden : ∀ z ∈ complexUnitDisk, 1 - z ≠ 0 := by
    intro z hz heq
    have hz1 : z = 1 := (sub_eq_zero.mp heq).symm
    have hh := hnorm z hz
    simp only [hz1, norm_one, lt_self_iff_false] at hh
  have hd : HasDerivAt koebeFunction 1 0 := by
    have hh := (hasDerivAt_id (0 : ℂ)).div
      (((hasDerivAt_const (0 : ℂ) (1 : ℂ)).sub (hasDerivAt_id (0 : ℂ))).pow 2)
      (by norm_num)
    convert! hh using 1
    simp [Pi.sub_def]
  have hsch : IsSchlicht koebeFunction := by
    refine ⟨?_, ?_, koebeFunction_zero, hd.deriv⟩
    · intro z hz
      change DifferentiableWithinAt ℂ (fun w ↦ w / (1 - w) ^ 2) complexUnitDisk z
      have hh : DifferentiableAt ℂ (fun w : ℂ ↦ (1 - w) ^ 2) z := by fun_prop
      exact (differentiableAt_id.div hh (pow_ne_zero 2 (hden z hz))).differentiableWithinAt
    · intro z hz w hw heq
      change z / (1 - z) ^ 2 = w / (1 - w) ^ 2 at heq
      have hc := (div_eq_div_iff (pow_ne_zero 2 (hden z hz))
        (pow_ne_zero 2 (hden w hw))).mp heq
      have hp : (z - w) * (1 - z * w) = 0 := by
        calc (z - w) * (1 - z * w) = z * (1 - w) ^ 2 - w * (1 - z) ^ 2 := by ring
          _ = 0 := sub_eq_zero.mpr hc
      have hzw : 1 - z * w ≠ 0 := by
        intro h
        have he : z * w = 1 := (sub_eq_zero.mp h).symm
        have hn : ‖z * w‖ < 1 := by
          calc ‖z * w‖ = ‖z‖ * ‖w‖ := norm_mul _ _
            _ ≤ 1 * ‖w‖ := mul_le_mul_of_nonneg_right (hnorm z hz).le (norm_nonneg _)
            _ = ‖w‖ := one_mul _
            _ < 1 := hnorm w hw
        simp only [he, norm_one, lt_self_iff_false] at hn
      exact sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_right hzw)
  let y : ℂ := -(1 / 4)
  have hnot : y ∉ koebeFunction '' complexUnitDisk := by
    rintro ⟨z, hz, heq⟩
    have hc : z = y * (1 - z) ^ 2 :=
      (div_eq_iff (pow_ne_zero 2 (hden z hz))).mp heq
    have hs : (z + 1) ^ 2 = 0 := by
      calc (z + 1) ^ 2 = 4 * (z - y * (1 - z) ^ 2) := by dsimp only [y]; ring
        _ = 0 := by rw [sub_eq_zero.mpr hc, mul_zero]
    have hzval : z = -1 := eq_neg_of_add_eq_zero_left ((sq_eq_zero_iff).mp hs)
    have hh := hnorm z hz
    simp only [hzval, norm_neg, norm_one, lt_self_iff_false] at hh
  refine ⟨hsch, fun r hr hball ↦ hnot (hball ?_)⟩
  simpa [y, Metric.mem_ball, dist_eq_norm, norm_div] using hr

/-- **43.5**: sharp two-sided derivative distortion at every disk point. -/
theorem schlicht_derivative_distortion {f : ℂ → ℂ} (hf : IsSchlicht f)
    {z : ℂ} (hz : z ∈ complexUnitDisk) :
    (1 - ‖z‖) / (1 + ‖z‖) ^ 3 ≤ ‖deriv f z‖ ∧
      ‖deriv f z‖ ≤ (1 + ‖z‖) / (1 - ‖z‖) ^ 3 := by
  sorry

/-- **43.8**: de Branges's coefficient theorem, including rigidity at one extremal coefficient.
The coefficients are the Taylor coefficients `CKMA.taylorCoefficient f n = f⁽ⁿ⁾(0) / n!`. -/
theorem de_branges {f : ℂ → ℂ} (hf : IsSchlicht f) (n : ℕ) (hn : 2 ≤ n) :
    ‖taylorCoefficient f n‖ ≤ n ∧
      (‖taylorCoefficient f n‖ = n → ∃ ζ : ℂ, ‖ζ‖ = 1 ∧
        Set.EqOn f (koebeRotation ζ) complexUnitDisk) := by
  sorry

/-- **43.31**, holomorphic Nehari criterion, with TauCeti's Schwarzian derivative
`TauCeti.schwarzian f = f''' / f' - (3 / 2) (f'' / f')²`. Stated for holomorphic `f`; the
meromorphic spherical version is not covered. -/
theorem nehari_univalent {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f complexUnitDisk)
    (hlocal : ∀ z ∈ complexUnitDisk, deriv f z ≠ 0)
    (hS : ∀ z ∈ complexUnitDisk, (1 - ‖z‖ ^ 2) ^ 2 * ‖TauCeti.schwarzian f z‖ ≤ 2) :
    Set.InjOn f complexUnitDisk := by
  sorry

/-- A radial Loewner chain: univalent nested images with the exponential derivative
normalization `f'(0, t) = eᵗ`. Local absolute continuity in `t`, uniformly on compact subdisks,
follows from these two conditions (Pommerenke's estimate `|f(z, t) - f(z, s)| ≤ C_r (eᵗ - eˢ)`)
and is not assumed. -/
@[expose]
def IsRadialLoewnerChain (f : ℝ → ℂ → ℂ) : Prop :=
  (∀ t : ℝ, 0 ≤ t → DifferentiableOn ℂ (f t) complexUnitDisk ∧
    Set.InjOn (f t) complexUnitDisk ∧ f t 0 = 0 ∧ deriv (f t) 0 = Real.exp t) ∧
  (∀ s t : ℝ, 0 ≤ s → s ≤ t → f s '' complexUnitDisk ⊆ f t '' complexUnitDisk)

/-- A radial Loewner chain is a nested family of normalized univalent maps of the disk. -/
theorem isRadialLoewnerChain_iff {f : ℝ → ℂ → ℂ} : IsRadialLoewnerChain f ↔
    (∀ t : ℝ, 0 ≤ t → DifferentiableOn ℂ (f t) complexUnitDisk ∧
      Set.InjOn (f t) complexUnitDisk ∧ f t 0 = 0 ∧ deriv (f t) 0 = Real.exp t) ∧
    (∀ s t : ℝ, 0 ≤ s → s ≤ t → f s '' complexUnitDisk ⊆ f t '' complexUnitDisk) :=
  Iff.rfl

/-- **43.21**: the Loewner–Kufarev equation with a measurable normalized Herglotz field.
The null set is common to all points of the disk. -/
theorem loewner_kufarev {f : ℝ → ℂ → ℂ} (hf : IsRadialLoewnerChain f) :
    ∃ p : ℂ → ℝ → ℂ,
      (∀ z ∈ complexUnitDisk, Measurable (p z)) ∧
      (∀ t : ℝ, 0 ≤ t → DifferentiableOn ℂ (fun z ↦ p z t) complexUnitDisk ∧
        p 0 t = 1 ∧ ∀ z ∈ complexUnitDisk, 0 ≤ (p z t).re) ∧
      ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)), ∀ z ∈ complexUnitDisk,
        HasDerivAt (fun s ↦ f s z) (z * deriv (f t) z * p z t) t := by
  sorry

end CKMA
