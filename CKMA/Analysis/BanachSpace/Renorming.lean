/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.Normed.Module.DoubleDual
public import TauCeti.Analysis.Normed.Module.FinitelyRepresentable

/-!
# Finite representability and superreflexive renorming

Finite representability is TauCeti's `TauCeti.FinitelyRepresentable`: embeddings of
finite-dimensional subspaces with distortion bounds `1 ± ε` for every `ε > 0`. Superreflexivity
quantifies over complete test spaces in the same carrier universe and uses surjectivity of the
canonical bidual inclusion.

Equivalent seminorms are separated by two-sided comparison with the original norm. Uniform
convexity is formulated on their unit balls, and uniform smoothness uses a uniform symmetric
increment estimate. Both characterizations include the zero space. Source: GAPS 17.46.

## Main definitions

* `CKMA.IsSuperreflexive`: superreflexivity of a Banach space.
* `CKMA.IsEquivalentNorm`: two-sided equivalence of a seminorm with the ambient norm.
* `CKMA.IsUniformlyConvexSeminorm`, `CKMA.IsUniformlySmoothSeminorm`: uniform convexity and
  uniform smoothness of a seminorm.

## Main results

* `CKMA.superreflexive_iff_exists_isUniformlyConvexSeminorm`: Enflo–James uniformly convex
  renorming characterization of superreflexivity.
* `CKMA.superreflexive_iff_exists_isUniformlySmoothSeminorm`: uniformly smooth renorming
  characterization of superreflexivity.
-/

public section

noncomputable section

namespace CKMA

open NormedSpace

universe u

/-- Superreflexivity: every Banach space `F` finitely representable in `E` is reflexive, that is,
its canonical bidual map is surjective. The test spaces range over the carrier universe of `E`. -/
@[expose]
def IsSuperreflexive (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] : Prop :=
  ∀ (F : Type u) [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F],
    TauCeti.FinitelyRepresentable ℝ F E → Function.Surjective (inclusionInDoubleDual ℝ F)

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Unfolding `IsSuperreflexive`. -/
theorem isSuperreflexive_iff : IsSuperreflexive E ↔
    ∀ (F : Type u) [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F],
      TauCeti.FinitelyRepresentable ℝ F E → Function.Surjective (inclusionInDoubleDual ℝ F) :=
  Iff.rfl

/-- Two-sided comparison makes a seminorm into an equivalent norm; its separation and Banach
completeness follow from the lower and upper bounds and completeness of the original norm. -/
@[expose]
def IsEquivalentNorm (N : Seminorm ℝ E) : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : E, c * ‖x‖ ≤ N x ∧ N x ≤ C * ‖x‖

/-- Unfolding `IsEquivalentNorm`. -/
theorem isEquivalentNorm_iff {N : Seminorm ℝ E} : IsEquivalentNorm N ↔
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : E, c * ‖x‖ ≤ N x ∧ N x ≤ C * ‖x‖ :=
  Iff.rfl

/-- Uniform convexity directly on the unit ball of a seminorm. The equivalent-norm hypothesis
in the renorming theorem ensures that this is a genuine norm geometry. -/
@[expose]
def IsUniformlyConvexSeminorm (N : Seminorm ℝ E) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x y : E,
    N x ≤ 1 → N y ≤ 1 → ε ≤ N (x - y) → N ((1 / 2 : ℝ) • (x + y)) ≤ 1 - δ

/-- Unfolding `IsUniformlyConvexSeminorm`. -/
theorem isUniformlyConvexSeminorm_iff {N : Seminorm ℝ E} : IsUniformlyConvexSeminorm N ↔
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x y : E,
      N x ≤ 1 → N y ≤ 1 → ε ≤ N (x - y) → N ((1 / 2 : ℝ) • (x + y)) ≤ 1 - δ :=
  Iff.rfl

/-- Uniform smoothness expressed by the uniform `o(t)` estimate of the symmetric norm increment.
This definition includes the zero vector space without a nonempty-unit-sphere hypothesis. -/
@[expose]
def IsUniformlySmoothSeminorm (N : Seminorm ℝ E) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ →
    ∀ x y : E, N x = 1 → N y = 1 →
      (N (x + t • y) + N (x - t • y)) / 2 - 1 ≤ ε * t

/-- Unfolding `IsUniformlySmoothSeminorm`. -/
theorem isUniformlySmoothSeminorm_iff {N : Seminorm ℝ E} : IsUniformlySmoothSeminorm N ↔
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ →
      ∀ x y : E, N x = 1 → N y = 1 → (N (x + t • y) + N (x - t • y)) / 2 - 1 ≤ ε * t :=
  Iff.rfl

/-- **17.46**, the uniformly convex renorming characterization of real superreflexive Banach
spaces: `E` is superreflexive if and only if it carries a seminorm equivalent to its norm whose
unit ball is uniformly convex. -/
theorem superreflexive_iff_exists_isUniformlyConvexSeminorm [CompleteSpace E] :
    IsSuperreflexive E ↔ ∃ N : Seminorm ℝ E, IsEquivalentNorm N ∧ IsUniformlyConvexSeminorm N := by
  sorry

/-- The uniformly smooth renorming characterization: `E` is superreflexive if and only if it
carries a seminorm equivalent to its norm that is uniformly smooth. -/
theorem superreflexive_iff_exists_isUniformlySmoothSeminorm [CompleteSpace E] :
    IsSuperreflexive E ↔ ∃ N : Seminorm ℝ E, IsEquivalentNorm N ∧ IsUniformlySmoothSeminorm N := by
  sorry

end CKMA
