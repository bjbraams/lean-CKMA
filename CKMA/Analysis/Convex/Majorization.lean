/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.Convex.Birkhoff
public import Mathlib.Analysis.Convex.Strict

/-!
# Majorization, doubly stochastic mixing, and Karamata inequalities

Majorization is expressed without choosing sorting permutations: total sums agree, and every
fixed-cardinality coordinate sum is bounded by one of the same size in the majorizing vector.
This agrees with decreasing partial sums and includes empty finite index types.

The mixing characterization uses Mathlib's doubly stochastic matrices. Convex functions preserve
the resulting sum inequality; strict convexity characterizes equality by a permutation.
Sources: GAPS 11.22 and 11.24.
-/

@[expose] public section

noncomputable section

namespace CKMA

open scoped BigOperators

variable {n : ℕ}

/-- Majorization without a chosen sorting permutation: every `k`-coordinate sum of `x`
is bounded by some `k`-coordinate sum of `y`, and the total sums agree.
This is the usual decreasing-partial-sum definition, including `n = 0`. -/
def IsMajorizedBy (x y : Fin n → ℝ) : Prop :=
  (∑ i, x i) = ∑ i, y i ∧
    ∀ s : Finset (Fin n), ∃ t : Finset (Fin n),
      t.card = s.card ∧ (∑ i ∈ s, x i) ≤ ∑ i ∈ t, y i

/-- Majorization is reflexive. -/
theorem IsMajorizedBy.refl (x : Fin n → ℝ) : IsMajorizedBy x x :=
  ⟨rfl, fun s ↦ ⟨s, rfl, le_rfl⟩⟩

/-- Majorization is transitive. -/
theorem IsMajorizedBy.trans {x y z : Fin n → ℝ}
    (hxy : IsMajorizedBy x y) (hyz : IsMajorizedBy y z) : IsMajorizedBy x z := by
  refine ⟨hxy.1.trans hyz.1, ?_⟩
  intro s
  obtain ⟨t, ht, hst⟩ := hxy.2 s
  obtain ⟨u, hu, htu⟩ := hyz.2 t
  exact ⟨u, hu.trans ht, hst.trans htu⟩

/-- **11.22**, Hardy–Littlewood–Pólya: majorization is doubly stochastic mixing. -/
theorem isMajorizedBy_iff_exists_doublyStochastic (x y : Fin n → ℝ) :
    IsMajorizedBy x y ↔ ∃ D ∈ doublyStochastic ℝ (Fin n), x = D.mulVec y := by
  sorry

/-- **11.24**, Karamata's inequality on any convex domain containing the coordinates. -/
theorem IsMajorizedBy.sum_convex_le {x y : Fin n → ℝ} (hxy : IsMajorizedBy x y)
    {s : Set ℝ} {φ : ℝ → ℝ} (hφ : ConvexOn ℝ s φ)
    (hx : ∀ i, x i ∈ s) (hy : ∀ i, y i ∈ s) :
    (∑ i, φ (x i)) ≤ ∑ i, φ (y i) := by
  sorry

/-- Equality in strictly convex Karamata holds precisely for permutations. -/
theorem IsMajorizedBy.sum_strictConvex_eq_iff {x y : Fin n → ℝ}
    (hxy : IsMajorizedBy x y) {s : Set ℝ} {φ : ℝ → ℝ}
    (hφ : StrictConvexOn ℝ s φ) (hx : ∀ i, x i ∈ s) (hy : ∀ i, y i ∈ s) :
    (∑ i, φ (x i)) = (∑ i, φ (y i)) ↔
      ∃ σ : Equiv.Perm (Fin n), x = y ∘ σ := by
  sorry

end CKMA
