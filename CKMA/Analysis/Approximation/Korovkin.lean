/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.ContinuousMap.Ordered

/-!
# Positive approximation operators on the unit interval

For order-preserving continuous linear operators on real continuous functions on
`[0,1]`, convergence on `1`, the coordinate function, and its square characterizes
strong convergence to the identity. Positivity uses Mathlib's order predicate
`Monotone`, which is equivalent to preserving nonnegative functions for linear maps.

Source: GAPS 47.17.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Filter Topology

/-- The real continuous functions on the unit interval, with their supremum norm. -/
abbrev UnitIntervalContinuousMap := C(Set.Icc (0 : ℝ) 1, ℝ)

/-- The coordinate function on the unit interval. -/
def unitIntervalId : UnitIntervalContinuousMap := ⟨fun x ↦ x.1, continuous_subtype_val⟩

/-- Order preservation of a linear operator, equivalently preservation of nonnegative functions. -/
abbrev IsPositiveContinuousMapOperator (L : UnitIntervalContinuousMap →L[ℝ]
    UnitIntervalContinuousMap) : Prop := Monotone L

/-- **47.17**: the three Korovkin test functions characterize strong convergence. -/
theorem korovkin_iff (L : ℕ → UnitIntervalContinuousMap →L[ℝ]
    UnitIntervalContinuousMap) (hL : ∀ n, Monotone (L n)) :
    (∀ f, Tendsto (fun n ↦ L n f) atTop (𝓝 f)) ↔
      Tendsto (fun n ↦ L n 1) atTop (𝓝 1) ∧
      Tendsto (fun n ↦ L n unitIntervalId) atTop (𝓝 unitIntervalId) ∧
      Tendsto (fun n ↦ L n (unitIntervalId ^ 2)) atTop (𝓝 (unitIntervalId ^ 2)) := by
  sorry

end CKMA
