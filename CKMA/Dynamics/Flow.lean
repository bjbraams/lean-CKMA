/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Dynamics.Flow
public import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Flow generators, stability and invariant subsets

`FlowHasGenerator` relates an existing real-time flow to an autonomous vector field.
The metric predicates `IsLyapunovStable` and `IsLocallyAttracting` require no linear
structure. `largestInvariantSubset` takes the points whose full orbit remains in a set.

These common interfaces support Lyapunov criteria, LaSalle invariance and planar
omega-limit arguments without introducing a dependency on a PDE module.
-/

@[expose] public section

namespace CKMA

/-- A global real-time flow has the indicated autonomous generator. -/
def FlowHasGenerator {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ : Flow ℝ E) (F : E → E) : Prop :=
  ∀ x t, HasDerivAt (fun s ↦ φ s x) (F (φ t x)) t

/-- Forward Lyapunov stability of a point for an existing flow on a pseudometric space. -/
def IsLyapunovStable {X : Type*} [PseudoMetricSpace X] (ϕ : Flow ℝ X) (x₀ : X) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x, dist x x₀ < δ →
    ∀ t : ℝ, 0 ≤ t → dist (ϕ t x) x₀ < ε

/-- Local forward attraction to a point for an existing flow on a pseudometric space. -/
def IsLocallyAttracting {X : Type*} [PseudoMetricSpace X] (ϕ : Flow ℝ X) (x₀ : X) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ x, dist x x₀ < δ → Filter.Tendsto (fun t ↦ ϕ t x) Filter.atTop (nhds x₀)

/-- Points whose full real-time orbit is contained in the given set. -/
def largestInvariantSubset {X : Type*} [TopologicalSpace X] (ϕ : Flow ℝ X)
    (s : Set X) : Set X := {x | ∀ t : ℝ, ϕ t x ∈ s}

end CKMA
