/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Compactness.Compact

/-!
# Normal summability

Normal summability is a predicate on families of functions into a normed additive group.
On a set, every compact subset must have bounded summands and a summable sequence of
compact-supremum norms. An unbounded real supremum does not certify convergence.
The predicate is not special to complex scalars; Laurent series and polydisc expansions use it.
-/

@[expose] public section

namespace CKMA

open scoped BigOperators

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
