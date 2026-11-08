/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.Fourier.LpSpace
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Fractional Hilbert and Bessel-potential energies

Gagliardo fractional square energy and Bessel-potential energy on L² for orders strictly
between zero and one. The Fourier identity has a positive finite normalization constant;
finite energies describe the same functions and the inhomogeneous energies are comparable.
The Fourier transform is Mathlib's L² operator and all energies retain extended values.
Source: GAPS 26.37.
-/

@[expose] public section

noncomputable section

namespace CKMA

open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform

/-- Gagliardo's squared fractional `L²` seminorm, allowing infinite energy. -/
def fractionalEnergy {d : ℕ} (s : ℝ) (u : EuclideanSpace ℝ (Fin d) → ℂ) : ℝ≥0∞ :=
  ∫⁻ x, ∫⁻ y, ENNReal.ofReal (‖u x - u y‖ ^ 2) /
    ENNReal.ofReal (‖x - y‖ ^ ((d : ℝ) + 2 * s))

/-- The Bessel-potential energy at order `s`, on the Fourier side of `L²`. -/
def besselPotentialEnergy {d : ℕ} (s : ℝ)
    (u : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))) : ℝ≥0∞ :=
  ∫⁻ ξ, ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ s * ‖(𝓕 u) ξ‖ ^ 2)

/-- **26.37**: the fractional Hilbert identity with a positive finite convention-dependent constant.
  -/
theorem fractionalEnergy_eq_fourier {d : ℕ} (hd : 0 < d) {s : ℝ}
    (hs : 0 < s) (hs1 : s < 1) : ∃ C : ℝ, 0 < C ∧
      ∀ u : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))),
        fractionalEnergy s u = ENNReal.ofReal C *
          ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ (2 * s) * ‖(𝓕 u) ξ‖ ^ 2) := by
  sorry

/-- Finite Gagliardo energy and finite Bessel energy describe the same `L²` functions. -/
theorem fractionalEnergy_ne_top_iff {d : ℕ} (hd : 0 < d) {s : ℝ}
    (hs : 0 < s) (hs1 : s < 1)
    (u : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))) :
    fractionalEnergy s u ≠ ∞ ↔ besselPotentialEnergy s u ≠ ∞ := by
  sorry


/-- Quantitative equivalence of the inhomogeneous fractional and Bessel square energies. -/
theorem fractional_bessel_energy_comparable {d : ℕ} (hd : 0 < d) {s : ℝ}
    (hs : 0 < s) (hs1 : s < 1) : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ u : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))),
        ENNReal.ofReal c * (ENNReal.ofReal (‖u‖ ^ 2) + fractionalEnergy s u) ≤
          besselPotentialEnergy s u ∧
        besselPotentialEnergy s u ≤
          ENNReal.ofReal C * (ENNReal.ofReal (‖u‖ ^ 2) + fractionalEnergy s u) := by
  sorry

end CKMA
