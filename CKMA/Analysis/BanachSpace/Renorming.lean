/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.BanachSpace.Geometry
public import Mathlib.Analysis.Normed.Module.Seminorm.Basic
public import TauCeti.Analysis.Normed.Module.Dual.Reflexive.Basic

/-!
# Finite representability and superreflexive renorming

Finite representability uses embeddings of finite-dimensional subspaces with arbitrarily small
multiplicative distortion. Superreflexivity quantifies over complete test spaces in the same
carrier universe and uses surjectivity of the canonical bidual inclusion.

Equivalent seminorms are separated by two-sided comparison with the original norm. Uniform
convexity is formulated on their unit balls, and uniform smoothness uses a uniform symmetric
increment estimate. Both characterizations include the zero space. Source: GAPS 17.46.
-/

@[expose] public section

noncomputable section

namespace CKMA

open NormedSpace

universe u

/-- Finite representability in scaled embedding form. Every finite-dimensional subspace
has, at every positive tolerance, an embedding with distortion at most `1+ε`. -/
def IsFinitelyRepresentableIn (F E : Type u) [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup E] [NormedSpace ℝ E] : Prop :=
  ∀ V : Submodule ℝ F, FiniteDimensional ℝ V → ∀ ε : ℝ, 0 < ε →
    ∃ T : V →L[ℝ] E, ∀ x : V, ‖x‖ ≤ ‖T x‖ ∧ ‖T x‖ ≤ (1 + ε) * ‖x‖

/-- Superreflexivity through finite representability and the actual canonical bidual map.
The test spaces range over the same carrier universe as the original space. -/
def IsSuperreflexive (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] : Prop :=
  ∀ (F : Type u) [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F],
    IsFinitelyRepresentableIn F E → Function.Surjective (inclusionInDoubleDual ℝ F)

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Two-sided comparison makes a seminorm into an equivalent norm; its separation and Banach
completeness follow from the lower and upper bounds and completeness of the original norm. -/
def IsEquivalentNorm (N : Seminorm ℝ E) : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : E, c * ‖x‖ ≤ N x ∧ N x ≤ C * ‖x‖

/-- Uniform convexity directly on the unit ball of a seminorm. The equivalent-norm hypothesis
in the renorming theorem ensures that this is a genuine norm geometry. -/
def IsUniformlyConvexSeminorm (N : Seminorm ℝ E) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x y : E,
    N x ≤ 1 → N y ≤ 1 → ε ≤ N (x - y) → N ((1 / 2 : ℝ) • (x + y)) ≤ 1 - δ

/-- Uniform smoothness expressed by the uniform `o(t)` estimate of the symmetric norm increment.
This definition includes the zero vector space without a nonempty-unit-sphere hypothesis. -/
def IsUniformlySmoothSeminorm (N : Seminorm ℝ E) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ →
    ∀ x y : E, N x = 1 → N y = 1 →
      (N (x + t • y) + N (x - t • y)) / 2 - 1 ≤ ε * t

/-- **17.46**, the uniformly convex renorming characterization of real superreflexive Banach spaces.
An actual seminorm with two-sided norm comparison is supplied, not an arbitrary new predicate. -/
theorem superreflexive_iff_exists_isUniformlyConvexSeminorm [CompleteSpace E] :
    IsSuperreflexive E ↔ ∃ N : Seminorm ℝ E, IsEquivalentNorm N ∧ IsUniformlyConvexSeminorm N := by
  sorry

/-- The equivalent uniformly smooth renorming characterization. -/
theorem superreflexive_iff_exists_isUniformlySmoothSeminorm [CompleteSpace E] :
    IsSuperreflexive E ↔ ∃ N : Seminorm ℝ E, IsEquivalentNorm N ∧ IsUniformlySmoothSeminorm N := by
  sorry

end CKMA
