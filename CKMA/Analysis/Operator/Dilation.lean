/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.CStarAlgebra.Representation
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Wold decomposition, minimal dilations, and commuting lifts

The wandering subspace is the kernel of the adjoint of an isometry, and the unitary part is the
intersection of its forward ranges. Wold decomposition expresses the shift part by an
unconditional sum with coefficients in that actual wandering space.

Unitary power dilation uses two-sided orbit minimality; isometric dilation uses forward orbits
and an explicit co-invariance identity. Commutant lifting preserves the norm and the full
coextension identity. Sources: GAPS 21.26, 21.30, and 21.37.
-/

@[expose] public section

noncomputable section

namespace CKMA

open scoped InnerProductSpace

universe u

variable {H K L : Type u}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]

/-- The wandering subspace `ker V*` of an isometry. -/
def woldWanderingSubspace (V : H →ₗᵢ[ℂ] H) : Submodule ℂ H :=
  LinearMap.ker V.toContinuousLinearMap.adjoint.toLinearMap

/-- The unitary part is the intersection of all forward ranges. -/
def woldUnitarySubspace (V : H →ₗᵢ[ℂ] H) : Submodule ℂ H :=
  ⨅ n : ℕ, LinearMap.range ((V.toContinuousLinearMap ^ n).toLinearMap)

/-- **21.26**: Wold's orthogonal unitary/shift decomposition. The shift multiplicity is
represented by the actual coefficient space `ker V*`, and the expansion is unconditional. -/
theorem wold_decomposition (V : H →ₗᵢ[ℂ] H) :
    (∀ u ∈ woldUnitarySubspace V, V u ∈ woldUnitarySubspace V) ∧
    (∀ u ∈ woldUnitarySubspace V, ∃ v ∈ woldUnitarySubspace V, V v = u) ∧
    (∀ (m n : ℕ), m ≠ n → ∀ u v : woldWanderingSubspace V,
      ⟪(V.toContinuousLinearMap ^ m) u, (V.toContinuousLinearMap ^ n) v⟫_ℂ = 0) ∧
    (∀ u ∈ woldUnitarySubspace V, ∀ n : ℕ, ∀ w : woldWanderingSubspace V,
      ⟪u, (V.toContinuousLinearMap ^ n) w⟫_ℂ = 0) ∧
    ∀ x : H, ∃ u ∈ woldUnitarySubspace V, ∃ w : ℕ → woldWanderingSubspace V,
      HasSum (fun n ↦ (V.toContinuousLinearMap ^ n) (w n)) (x - u) := by
  sorry

/-- Power dilation and two-sided orbit minimality for a unitary realization. -/
def IsMinimalUnitaryPowerDilation (T : H →L[ℂ] H) (J : H →ₗᵢ[ℂ] K)
    (U : K ≃ₗᵢ[ℂ] K) : Prop :=
  (∀ n : ℕ, ∀ x : H, J.toContinuousLinearMap.adjoint ((U^[n]) (J x)) = (T ^ n) x) ∧
    (Submodule.span ℂ {y : K | ∃ k : ℤ, ∃ x : H, y = (U ^ k) (J x)}).topologicalClosure = ⊤

/-- **21.30**: every contraction admits a minimal unitary power dilation. -/
theorem exists_minimalUnitaryPowerDilation (T : H →L[ℂ] H) (hT : ‖T‖ ≤ 1) :
    ∃ M : ComplexHilbertSpace.{u}, ∃ J : H →ₗᵢ[ℂ] M.Carrier,
      ∃ U : M.Carrier ≃ₗᵢ[ℂ] M.Carrier, IsMinimalUnitaryPowerDilation T J U := by
  sorry

/-- Uniqueness is the unique unitary preserving the embedded original space and intertwining
both dilations; it follows from their two-sided orbit minimality. -/
theorem minimalUnitaryPowerDilation_unique (T : H →L[ℂ] H)
    (J : H →ₗᵢ[ℂ] K) (U : K ≃ₗᵢ[ℂ] K) (hU : IsMinimalUnitaryPowerDilation T J U)
    (J' : H →ₗᵢ[ℂ] L) (U' : L ≃ₗᵢ[ℂ] L) (hU' : IsMinimalUnitaryPowerDilation T J' U') :
    ∃! W : K ≃ₗᵢ[ℂ] L, (∀ x, W (J x) = J' x) ∧ ∀ y, W (U y) = U' (W y) := by
  sorry

/-- Minimal isometric dilation with the original space co-invariant. -/
def IsMinimalIsometricDilation (T : H →L[ℂ] H) (J : H →ₗᵢ[ℂ] K)
    (V : K →ₗᵢ[ℂ] K) : Prop :=
  (∀ y : K, J.toContinuousLinearMap.adjoint (V y) = T (J.toContinuousLinearMap.adjoint y)) ∧
    (Submodule.span ℂ {y : K | ∃ n : ℕ, ∃ x : H,
      y = (V.toContinuousLinearMap ^ n) (J x)}).topologicalClosure = ⊤

/-- The minimal isometric dilation required by the commutant-lifting interface exists. -/
theorem exists_minimalIsometricDilation (T : H →L[ℂ] H) (hT : ‖T‖ ≤ 1) :
    ∃ M : ComplexHilbertSpace.{u}, ∃ J : H →ₗᵢ[ℂ] M.Carrier,
      ∃ V : M.Carrier →ₗᵢ[ℂ] M.Carrier, IsMinimalIsometricDilation T J V := by
  sorry

/-- **21.37**: an operator commuting with a contraction has a norm-preserving commuting lift
on its minimal isometric dilation, with the full coextension identity. -/
theorem commutant_lifting (T X : H →L[ℂ] H) (hT : ‖T‖ ≤ 1) (hXT : Commute X T)
    (J : H →ₗᵢ[ℂ] K) (V : K →ₗᵢ[ℂ] K) (hd : IsMinimalIsometricDilation T J V) :
    ∃ Y : K →L[ℂ] K, Commute Y V.toContinuousLinearMap ∧ ‖Y‖ = ‖X‖ ∧
      ∀ y : K, J.toContinuousLinearMap.adjoint (Y y) = X (J.toContinuousLinearMap.adjoint y) := by
  sorry

end CKMA
