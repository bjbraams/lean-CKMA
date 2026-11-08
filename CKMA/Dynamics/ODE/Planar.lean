/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Dynamics.Flow
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Dynamics.Flow
public import Mathlib.Dynamics.OmegaLimit

/-!
# Planar omega-limit sets (31.38)

`poincare_bendixson` identifies a compactly trapped planar orbit's omega-limit set with a
whole periodic orbit when that limit set contains no equilibrium. The generator is C¹
and is related to the existing global flow through `FlowHasGenerator`.

The plane is the real Euclidean space on `Fin 2`; all differential and omega-limit
conventions come from Mathlib and the common `CKMA.Dynamics.Flow` interface.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Filter Topology

/-- **31.38**: a compact planar omega-limit set without equilibria is a periodic orbit.
The compact forward absorbing set supplies nonemptiness, and the conclusion identifies
all points of the omega-limit set, not just one periodic point. -/
theorem poincare_bendixson (φ : Flow ℝ (EuclideanSpace ℝ (Fin 2)))
    (F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)) (hF : ContDiff ℝ 1 F)
    (hgen : FlowHasGenerator φ F) (x : EuclideanSpace ℝ (Fin 2))
    (K : Set (EuclideanSpace ℝ (Fin 2))) (hK : IsCompact K)
    (hstay : ∀ t : ℝ, 0 ≤ t → φ t x ∈ K)
    (hrest : ∀ y ∈ omegaLimit atTop φ {x}, F y ≠ 0) :
    ∃ y : EuclideanSpace ℝ (Fin 2), ∃ T : ℝ, 0 < T ∧ φ T y = y ∧
      omegaLimit atTop φ {x} = Set.range (fun t : ℝ ↦ φ t y) := by
  sorry

end CKMA
