/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import TauCeti.MeasureTheory.Measure.ProjectiveLimit.Countable

/-!
# Arbitrary-index Kolmogorov extension (06.1)

A consistent family of finite-dimensional probability measures on standard Borel
coordinate spaces has a unique probability measure on the full product sigma-algebra.
The index type is arbitrary, including the empty type.

The interface uses Mathlib's projective-family and projective-limit predicates. The
imported TauCeti module supplies countable-index existence; the present target retains
the stronger arbitrary-index conclusion and Mathlib's cylinder-based uniqueness.
-/

@[expose] public section

noncomputable section

namespace CKMA

open scoped NNReal ENNReal


open MeasureTheory

variable {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]

/-- **06.1**: arbitrary-index Kolmogorov extension on standard Borel coordinates.
Uniqueness is inherited from Mathlib; the countable existence theorem is in TauCeti. -/
theorem existsUnique_isProjectiveLimit [∀ i, StandardBorelSpace (X i)]
    (P : ∀ I : Finset ι, Measure (∀ i : I, X i)) [∀ I, IsProbabilityMeasure (P I)]
    (hP : IsProjectiveMeasureFamily P) :
    ∃! μ : Measure (∀ i, X i), IsProbabilityMeasure μ ∧ IsProjectiveLimit μ P := by
  sorry

end CKMA
