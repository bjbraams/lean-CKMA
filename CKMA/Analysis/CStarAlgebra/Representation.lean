/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
public import CKMA.Analysis.InnerProductSpace.HilbertModel
public import Mathlib.Analysis.CStarAlgebra.Classes

/-!
# Cyclic C-star representations and faithful operator representations

Cyclicity means density of the algebra orbit of one vector; that orbit is already a linear
subspace. A represented functional has the form `a ↦ ⟪Ω, π(a)Ω⟫`, with Mathlib's inner product
linear in its second variable. Cyclic realizations of one functional are compared by a unique
unitary preserving their cyclic vectors and intertwining the actions.

The faithful representation statement includes nonunital C-star algebras and norm-closed image.
Its Hilbert carrier is allowed in a larger universe for the sum over states.
Sources: GAPS 23.9 and 23.10.
-/

@[expose] public section

noncomputable section

namespace CKMA

open scoped InnerProductSpace

universe u

/-- A complex Hilbert-space model with an explicitly chosen carrier universe. -/
abbrev ComplexHilbertSpace := HilbertSpaceModel.{u} ℂ

variable {A H K : Type*} [NonUnitalCStarAlgebra A]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- A vector is cyclic if its algebra orbit is dense. Since the orbit is a linear subspace,
no separate linear span is necessary. -/
def IsCyclicVector (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (Ω : H) : Prop :=
  DenseRange (fun a ↦ π a Ω)

/-- The vector realizes `φ`, using Mathlib's inner product, which is linear in the second variable.
  -/
def RealizesFunctional (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (Ω : H) (φ : A → ℂ) : Prop :=
  ∀ a, φ a = ⟪Ω, π a Ω⟫_ℂ

/-- **23.9**, uniqueness clause: two cyclic realizations of the same functional have a unique
unitary intertwiner preserving their cyclic vectors. Existence for nonunital algebras is separate.
  -/
theorem existsUnique_cyclicRepresentation_equiv
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ρ : A →⋆ₙₐ[ℂ] (K →L[ℂ] K))
    (Ω : H) (Ω' : K) (hπ : IsCyclicVector π Ω) (hρ : IsCyclicVector ρ Ω')
    (φ : A → ℂ) (hφπ : RealizesFunctional π Ω φ) (hφρ : RealizesFunctional ρ Ω' φ) :
    ∃! U : H ≃ₗᵢ[ℂ] K, U Ω = Ω' ∧ ∀ a x, U (π a x) = ρ a (U x) := by
  sorry

/-- **23.10**: a C*-algebra, including a nonunital one, has an isometric operator representation
with closed image. The larger universe permits the Hilbert sum over all states. -/
theorem exists_isometric_representation (A : Type u) [NonUnitalCStarAlgebra A] :
    ∃ H : ComplexHilbertSpace.{u + 1},
      ∃ π : A →⋆ₙₐ[ℂ] (H.Carrier →L[ℂ] H.Carrier), Isometry π ∧ IsClosed (Set.range π) := by
  sorry

end CKMA
