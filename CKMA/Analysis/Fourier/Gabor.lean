/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Fourier.LpSpace

/-!
# Rectangular Gabor density and the Balian–Low obstruction

Time-frequency atoms use modulation `exp(2πi b n t)` and translation by `a m`.
Single-window frame and Riesz-sequence inequalities bound the rectangular lattice
density in opposite directions, so a Riesz basis has critical density. A Gabor Riesz
basis cannot have finite second moments in both time and frequency.

Sources: GAPS 29.46 and 29.51. The frequency moment uses Mathlib's L² Fourier unitary.

## Main definitions

* `CKMA.gaborAtom`: rectangular time-frequency translate `exp(2πi b p.2 t) * g (t - a p.1)`.

## Main results

* `CKMA.gabor_frame_density`: frame density bound `a * b ≤ 1` (**29.46**).
* `CKMA.gabor_rieszSequence_density`: Riesz-sequence density bound `1 ≤ a * b`.
* `CKMA.gabor_rieszBasis_density`: critical density `a * b = 1` for a Gabor Riesz basis.
* `CKMA.balian_low`: Balian–Low uncertainty obstruction for Gabor Riesz bases (**29.51**).
-/

public section

noncomputable section

namespace CKMA

open MeasureTheory FourierTransform
open scoped FourierTransform

/-- Rectangular time-frequency translates, at Mathlib's exp(2 pi i omega t) modulation. -/
@[expose]
def gaborAtom (g : ℝ → ℂ) (a b : ℝ) (p : ℤ × ℤ) (t : ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * b * p.2 * t) * g (t - a * p.1)

/-- Unfolding the Gabor atom. -/
theorem gaborAtom_def (g : ℝ → ℂ) (a b : ℝ) (p : ℤ × ℤ) (t : ℝ) :
    gaborAtom g a b p t = Complex.exp (2 * Real.pi * Complex.I * b * p.2 * t) * g (t - a * p.1) :=
  rfl

/-- The pointwise modulus of a Gabor atom is that of the translated window. -/
theorem norm_gaborAtom (g : ℝ → ℂ) (a b : ℝ) (p : ℤ × ℤ) (t : ℝ) :
    ‖gaborAtom g a b p t‖ = ‖g (t - a * p.1)‖ := by
  rw [gaborAtom, norm_mul, Complex.norm_exp]
  simp

/-- **29.46**, the frame density bound: if the rectangular Gabor system of `g` with lattice
`aℤ × bℤ` is a frame for `L²(ℝ)`, then `a * b ≤ 1`. -/
theorem gabor_frame_density {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {g : ℝ → ℂ} (hframe : IsL2FrameFamily volume (gaborAtom g a b)) : a * b ≤ 1 := by
  sorry

/-- A rectangular Gabor Riesz sequence has the reverse density bound `1 ≤ a * b`. -/
theorem gabor_rieszSequence_density {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {g : ℝ → ℂ} (hriesz : IsL2RieszSequence volume (gaborAtom g a b)) : 1 ≤ a * b := by
  sorry

/-- A Gabor Riesz basis has critical density `a * b = 1`; it combines the frame and
Riesz-sequence density bounds. -/
theorem gabor_rieszBasis_density {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {g : ℝ → ℂ} (h : IsL2RieszBasis volume (gaborAtom g a b)) : a * b = 1 :=
  le_antisymm (gabor_frame_density ha hb h.isL2FrameFamily)
    (gabor_rieszSequence_density ha hb h.isL2RieszSequence)

/-- **29.51**: a Gabor Riesz basis cannot have finite second moments in both time and frequency. -/
theorem balian_low {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (g : Lp ℂ 2 (volume : Measure ℝ))
    (h : IsL2RieszBasis volume (gaborAtom g a b)) :
    ¬ (MemLp (fun t : ℝ ↦ (t : ℂ) * g t) 2 volume ∧
      MemLp (fun ξ : ℝ ↦ (ξ : ℂ) * (𝓕 g) ξ) 2 volume) := by
  sorry

end CKMA
