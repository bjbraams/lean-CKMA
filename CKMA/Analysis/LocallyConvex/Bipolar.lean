/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import TauCeti.Analysis.LocallyConvex.Bipolar
public import Mathlib.Analysis.LocallyConvex.WeakDual

/-!
# The bipolar theorem for a weak bilinear pairing

For a bilinear pairing over real or complex scalars, the double polar is the weakly closed
absolutely convex hull. The topology is the actual `WeakBilin` topology induced by the pairing,
without requiring that it separate points. Inserting zero handles the empty-set convention.

The proof transports TauCeti's strong-dual bipolar theorem through Mathlib's surjectivity of the
dual embedding for weak bilinear spaces. Source: GAPS 16.13.
-/

@[expose] public section

noncomputable section

namespace CKMA

open scoped ComplexOrder


variable {𝕜 E F : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [AddCommGroup F] [Module 𝕜 F]
    [Module ℝ E] [IsScalarTower ℝ 𝕜 E]

/-- **16.13**: the bipolar for a bilinear pairing is the weakly closed absolutely convex hull.
The topology is explicitly `WeakBilin B`, rather than an arbitrary topology on `E`. Separating
  hypotheses are unnecessary.
The proof transports TauCeti's `StrongDual.bipolar_eq_closedAbsConvexHull` through
Mathlib's `LinearMap.dualEmbedding_surjective`. -/
theorem bipolar_eq_weakClosure_absConvexHull (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜)
    (s : Set E) :
    B.flip.polar (B.polar s) =
      closure (X := WeakBilin B) (absConvexHull 𝕜 (insert 0 s)) := by
  rw [← closedAbsConvexHull_eq_closure_absConvexHull (E := WeakBilin B)]
  rw [← StrongDual.bipolar_eq_closedAbsConvexHull (E := WeakBilin B) 𝕜 s]
  ext x
  change (∀ y ∈ B.polar s, ‖B x y‖ ≤ 1) ↔
    ∀ g ∈ StrongDual.polar (M := WeakBilin B) 𝕜 s, ‖g x‖ ≤ 1
  constructor
  · intro hx g hg
    obtain ⟨y, rfl⟩ := LinearMap.dualEmbedding_surjective B g
    exact hx y hg
  · intro hx y hy
    exact hx (WeakBilin.eval B y) hy

end CKMA
