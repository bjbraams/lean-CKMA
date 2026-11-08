/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.MeasureTheory.Group.ModularCharacter

/-!
# Modular continuity and Haar inversion (28.2)

The main targets assert continuity of Mathlib's modular character and identify inversion
of left Haar measure with the measure having this character as density. This also yields
the integral inversion formula.

The ambient group is locally compact and Hausdorff. The character convention is the
reciprocal of the commonly used modular function `Δ`; the measure identity explicitly
uses Borel structure and second countability.
-/

@[expose] public section

noncomputable section

namespace CKMA

open MeasureTheory MeasureTheory.Measure
open scoped NNReal ENNReal

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G]

/-- **28.2**: continuity of Mathlib's modular character, the reciprocal of the usual `Δ`. -/
theorem continuous_modularCharacter : Continuous (modularCharacter : G → ℝ≥0) := by
  sorry

/-- Inversion of left Haar measure has density Mathlib's modular character.
This measure identity also supplies the integral inversion formula. -/
theorem map_inv_haar [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
    (μ : Measure G) [IsHaarMeasure μ] :
    μ.map Inv.inv = μ.withDensity (fun x ↦ (modularCharacter x : ℝ≥0∞)) := by
  sorry

end CKMA
