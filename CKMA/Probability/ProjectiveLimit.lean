/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.Projective
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

import Mathlib.MeasureTheory.Constructions.KolmogorovExtension

/-!
# Arbitrary-index Kolmogorov extension (06.1)

A consistent family of finite-dimensional probability measures on standard Borel
coordinate spaces has a unique probability measure on the full product sigma-algebra.
The index type is arbitrary, including the empty type.

The theorem is a corollary of Mathlib's Kolmogorov extension theorem
`MeasureTheory.isProjectiveLimit_projectiveLimit`, stated for second-countable completely
metrizable Borel coordinates: each standard Borel space carries such a topology
(`upgradeStandardBorel`). Uniqueness is `MeasureTheory.IsProjectiveLimit.unique`.

## Main results

* `CKMA.existsUnique_isProjectiveLimit`: Kolmogorov extension theorem for arbitrary index sets
  (**06.1**).
-/

public section

namespace CKMA

open MeasureTheory

variable {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]

/-- **06.1**: arbitrary-index Kolmogorov extension on standard Borel coordinates.
Existence and uniqueness come from Mathlib's Polish-space version through a Polish topology
compatible with each standard Borel structure. -/
theorem existsUnique_isProjectiveLimit [∀ i, StandardBorelSpace (X i)]
    (P : ∀ I : Finset ι, Measure (∀ i : I, X i)) [∀ I, IsProbabilityMeasure (P I)]
    (hP : IsProjectiveMeasureFamily P) :
    ∃! μ : Measure (∀ i, X i), IsProbabilityMeasure μ ∧ IsProjectiveLimit μ P := by
  let := fun i => upgradeStandardBorel (X i)
  exact ⟨projectiveLimit P hP, ⟨inferInstance, isProjectiveLimit_projectiveLimit hP⟩,
    fun ν hν => hν.2.unique (isProjectiveLimit_projectiveLimit hP)⟩

end CKMA
