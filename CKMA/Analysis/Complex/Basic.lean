/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.Complex.Basic

/-!
# Normal summability and basic complex domains

Normal summability is a predicate on families of functions into a normed additive group.
On a set, every compact subset must have bounded summands and a summable sequence of
compact-supremum norms. This module also defines the open unit disk in `ℂ` shared across
complex analysis and complex geometry.

## Main definitions

* `CKMA.NormallySummableOn`: normal summability of a function family on compact subsets of a set.
* `CKMA.complexUnitDisk`: the open unit disk `Metric.ball (0 : ℂ) 1`.

## Main results

* `CKMA.NormallySummableOn.summable_norm`: normal summability on `s` implies pointwise absolute
  summability at each `x ∈ s`.
* `CKMA.isOpen_complexUnitDisk`: `complexUnitDisk` is open.
-/

@[expose] public section

noncomputable section

namespace CKMA

open scoped BigOperators

/-- The open unit disk, shared by the analytic function-space interfaces. -/
def complexUnitDisk : Set ℂ := Metric.ball 0 1

/-- The shared unit disk is open. This exported lemma avoids unfolding its implementation
from downstream modules. -/
theorem isOpen_complexUnitDisk : IsOpen complexUnitDisk := Metric.isOpen_ball

/-- Normal summability on compact subsets, requiring bounded summands and summability
of their compact supremum norms. -/
def NormallySummableOn {ι X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E]
    (f : ι → X → E) (s : Set X) : Prop :=
  ∀ K : Set X, IsCompact K → K ⊆ s →
    (∀ i, BddAbove ((fun x ↦ ‖f i x‖) '' K)) ∧
      Summable (fun i ↦ sSup ((fun x ↦ ‖f i x‖) '' K))

/-- A normally summable family is absolutely summable at each point of its domain. -/
theorem NormallySummableOn.summable_norm {ι X E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] {f : ι → X → E} {s : Set X}
    (hf : NormallySummableOn f s) {x : X} (hx : x ∈ s) :
    Summable (fun i ↦ ‖f i x‖) := by
  have h := (hf {x} isCompact_singleton (Set.singleton_subset_iff.mpr hx)).2
  simpa only [Set.image_singleton, csSup_singleton] using h

end CKMA
