/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.Complex.Hardy
public import CKMA.Analysis.Complex.Laurent
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-!
# Schlicht functions and radial Loewner evolution

The normalized schlicht class is governed by the exterior area theorem, Koebe's
quarter theorem, sharp derivative distortion and de Branges's coefficient rigidity.
The Koebe function gives explicit quarter-radius sharpness by omitting `-1/4`.
The Schwarzian derivative gives Nehari's injectivity criterion. Radial Loewner chains
have nested univalent images, exponential derivative normalization and local absolute
continuity; their evolution is described by a measurable normalized Herglotz field.

Sources: GAPS 43.1, 43.3, 43.5, 43.8, 43.21 and 43.31.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Filter Topology MeasureTheory
open scoped BigOperators ENNReal ComplexConjugate

/-- The normalized schlicht class on the unit disk. -/
def IsSchlicht (f : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ f complexUnitDisk ∧ Set.InjOn f complexUnitDisk ∧ f 0 = 0 ∧ deriv f 0 = 1

/-- The Koebe extremal function. -/
def koebeFunction (z : ℂ) : ℂ := z / (1 - z) ^ 2

/-- A rotation of the normalized Koebe function. -/
def koebeRotation (ζ z : ℂ) : ℂ := ζ⁻¹ * koebeFunction (ζ * z)

/-- The Koebe function vanishes at the origin. -/
theorem koebeFunction_zero : koebeFunction 0 = 0 := by
  simp [koebeFunction]

/-- The Taylor coefficient in the usual schlicht normalization. -/
def schlichtCoefficient (f : ℂ → ℂ) (n : ℕ) : ℂ := iteratedDeriv n f 0 / (n.factorial : ℂ)

/-- The exterior disk. -/
def exteriorUnitDisk : Set ℂ := {z | 1 < ‖z‖}

/-- Exterior schlicht functions, normalized to derivative one at infinity. -/
def IsExteriorSchlicht (g : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ g exteriorUnitDisk ∧ Set.InjOn g exteriorUnitDisk ∧
    ∃ b₀ : ℂ, Tendsto (fun z ↦ g z - z) (cocompact ℂ) (𝓝 b₀)

/-- The nonnegative coefficient energy in Grönwall's exterior area theorem. -/
def exteriorCoefficientEnergy (g : ℂ → ℂ) : ℝ≥0∞ :=
  ∑' n : ℕ, (n + 1 : ℝ≥0∞) *
    ENNReal.ofReal (‖laurentCoefficient g 0 2 (-((n + 1 : ℕ) : ℤ))‖ ^ 2)

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

/-- **43.8**: de Branges's coefficient theorem, including rigidity at one extremal coefficient. -/
theorem de_branges {f : ℂ → ℂ} (hf : IsSchlicht f) (n : ℕ) (hn : 2 ≤ n) :
    ‖schlichtCoefficient f n‖ ≤ n ∧
      (‖schlichtCoefficient f n‖ = n → ∃ ζ : ℂ, ‖ζ‖ = 1 ∧
        Set.EqOn f (koebeRotation ζ) complexUnitDisk) := by
  sorry

/-- Schwarzian derivative in the standard normalization. -/
def schwarzianDerivative (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  iteratedDeriv 3 f z / deriv f z - (3 / 2 : ℂ) * (iteratedDeriv 2 f z / deriv f z) ^ 2

/-- **43.31**, holomorphic Nehari criterion. The meromorphic spherical version remains. -/
theorem nehari_univalent {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f complexUnitDisk)
    (hlocal : ∀ z ∈ complexUnitDisk, deriv f z ≠ 0)
    (hS : ∀ z ∈ complexUnitDisk, (1 - ‖z‖ ^ 2) ^ 2 * ‖schwarzianDerivative f z‖ ≤ 2) :
    Set.InjOn f complexUnitDisk := by
  sorry

/-- Local absolute continuity of a time family, with an integrable bound uniform on compact
  subdisks. -/
def IsLocallyAbsolutelyContinuousDiskFamily (f : ℝ → ℂ → ℂ) : Prop :=
  ∀ T r : ℝ, 0 < T → 0 ≤ r → r < 1 → ∃ m : ℝ → ℝ,
    IntegrableOn m (Set.Icc 0 T) ∧ (∀ᵐ t ∂volume.restrict (Set.Icc 0 T), 0 ≤ m t) ∧
    ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ T → ∀ z : ℂ, ‖z‖ ≤ r →
      ‖f t z - f s z‖ ≤ ∫ u in s..t, m u

/-- A radial Loewner chain: univalent nested images, exponential derivative normalization,
and the usual local absolute-continuity control. -/
def IsRadialLoewnerChain (f : ℝ → ℂ → ℂ) : Prop :=
  (∀ t : ℝ, 0 ≤ t → DifferentiableOn ℂ (f t) complexUnitDisk ∧
    Set.InjOn (f t) complexUnitDisk ∧ f t 0 = 0 ∧ deriv (f t) 0 = Real.exp t) ∧
  (∀ s t : ℝ, 0 ≤ s → s ≤ t → f s '' complexUnitDisk ⊆ f t '' complexUnitDisk) ∧
  IsLocallyAbsolutelyContinuousDiskFamily f

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
