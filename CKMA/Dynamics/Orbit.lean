/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Logic.Function.Iterate

/-!
# Bounded forward orbits

`HasBoundedOrbit` expresses boundedness of the range of forward iterates in an arbitrary
bornological space. Adjoining or deleting the initial point does not change this property.
For normed additive groups a bridge identifies it with a uniform bound on iterate norms.
This interface is independent of the complex-analytic polynomial applications.
-/

@[expose] public section

namespace CKMA

/-- The forward iterate range is bounded in the ambient bornology. -/
def HasBoundedOrbit {X : Type*} [Bornology X] (f : X → X) (x : X) : Prop :=
  Bornology.IsBounded (Set.range (fun n : ℕ ↦ (f^[n]) x))

/-- Deleting the initial point preserves boundedness of an orbit. -/
theorem HasBoundedOrbit.map {X : Type*} [Bornology X] {f : X → X} {x : X}
    (h : HasBoundedOrbit f x) : HasBoundedOrbit f (f x) := by
  apply h.subset
  rintro _ ⟨n, rfl⟩
  exact ⟨n + 1, Function.iterate_succ_apply f n x⟩

/-- Adjoining the initial point to a bounded tail preserves boundedness. -/
theorem HasBoundedOrbit.of_map {X : Type*} [Bornology X] {f : X → X} {x : X}
    (h : HasBoundedOrbit f (f x)) : HasBoundedOrbit f x := by
  apply (h.insert x).subset
  rintro _ ⟨n, rfl⟩
  cases n with
  | zero => exact Set.mem_insert x _
  | succ n =>
    apply Set.mem_insert_of_mem
    exact ⟨n, (Function.iterate_succ_apply f n x).symm⟩

/-- In a normed additive group, an orbit is bounded exactly when its norms have a uniform bound. -/
theorem hasBoundedOrbit_iff_exists_norm_le {X : Type*} [NormedAddCommGroup X]
    (f : X → X) (x : X) :
    HasBoundedOrbit f x ↔ ∃ R : ℝ, ∀ n : ℕ, ‖(f^[n]) x‖ ≤ R := by
  simp only [HasBoundedOrbit, isBounded_iff_forall_norm_le, Set.forall_mem_range]

end CKMA
