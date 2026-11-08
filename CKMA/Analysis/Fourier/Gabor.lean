/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.InnerProductSpace.L2FunctionFamilies
public import Mathlib.Analysis.Fourier.LpSpace
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Rectangular Gabor density and the Balian–Low obstruction

Time-frequency atoms use modulation `exp(2πi b n t)` and translation by `a m`.
Single-window frame and Riesz-sequence inequalities bound the rectangular lattice
density in opposite directions, so a Riesz basis has critical density. A Gabor Riesz
basis cannot have finite second moments in both time and frequency.

Sources: GAPS 29.46 and 29.51. The frequency moment uses Mathlib's L² Fourier unitary.
-/

@[expose] public section

noncomputable section

namespace CKMA

open MeasureTheory FourierTransform
open scoped FourierTransform

/-- Rectangular time-frequency translates, at Mathlib's exp(2 pi i omega t) modulation. -/
def gaborAtom (g : ℝ → ℂ) (a b : ℝ) (p : ℤ × ℤ) (t : ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * b * p.2 * t) * g (t - a * p.1)

/-- **29.46**, the one-dimensional rectangular single-window frame density obstruction. -/
theorem gabor_frame_density {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {g : ℝ → ℂ} (hframe : IsL2FrameFamily volume (gaborAtom g a b)) : a * b ≤ 1 := by
  sorry

/-- A rectangular Gabor Riesz sequence has the reverse density inequality. -/
theorem gabor_rieszSequence_density {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {g : ℝ → ℂ} (hriesz : IsL2RieszSequence volume (gaborAtom g a b)) : 1 ≤ a * b := by
  sorry

/-- A Gabor Riesz basis has critical density. This corollary depends on the density targets. -/
theorem gabor_rieszBasis_density {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {g : ℝ → ℂ} (h : IsL2RieszBasis volume (gaborAtom g a b)) : a * b = 1 :=
  le_antisymm (gabor_frame_density ha hb h.isFrameFamily)
    (gabor_rieszSequence_density ha hb h.isRieszSequence)

/-- **29.51**: a Gabor Riesz basis cannot have finite second moments in both time and frequency. -/
theorem balian_low {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (g : Lp ℂ 2 (volume : Measure ℝ))
    (h : IsL2RieszBasis volume (gaborAtom g a b)) :
    ¬ (MemLp (fun t : ℝ ↦ (t : ℂ) * g t) 2 volume ∧
      MemLp (fun ξ : ℝ ↦ (ξ : ℂ) * (𝓕 g) ξ) 2 volume) := by
  sorry

end CKMA
