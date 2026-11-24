/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.MeasureTheory.Group.ModularCharacter

import TauCeti.MeasureTheory.Group.ModularCharacter

/-!
# Modular continuity and Haar inversion (28.2)

The main targets assert continuity of Mathlib's modular character and identify inversion
of left Haar measure with the measure having this character as density. This also yields
the integral inversion formula. Both are derived from the pinned TauCeti
(`TauCeti.continuous_modularCharacter` and
`MeasureTheory.Measure.inv_eq_withDensity_modularCharacter_of_regular`).

The ambient group is locally compact; no separation or countability axiom is needed. The
character convention is the reciprocal of the commonly used modular function `Δ`. The measure
identity uses Borel structure and a regular Haar measure; on a second-countable Hausdorff group
every Haar measure is regular, by Mathlib's instance
`MeasureTheory.Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure`.

## Main results

* `CKMA.continuous_modularCharacter`: continuity of Mathlib's modular character.
* `CKMA.map_inv_haar`: inversion of a regular left Haar measure has density given by the
  modular character.
-/

public section

noncomputable section

namespace CKMA

open MeasureTheory MeasureTheory.Measure
open scoped NNReal ENNReal

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G]

/-- **28.2**: continuity of Mathlib's modular character, the reciprocal of the usual `Δ`. -/
theorem continuous_modularCharacter : Continuous (modularCharacter : G → ℝ≥0) :=
  TauCeti.continuous_modularCharacter

/-- Inversion of a regular left Haar measure has density Mathlib's modular character.
This measure identity also supplies the integral inversion formula. Regularity holds in
particular on second-countable Hausdorff groups. -/
theorem map_inv_haar [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [IsHaarMeasure μ]
    [μ.Regular] :
    μ.map Inv.inv = μ.withDensity (fun x ↦ (modularCharacter x : ℝ≥0∞)) :=
  inv_eq_withDensity_modularCharacter_of_regular μ

end CKMA
