/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.InnerProductSpace.Basic
public import CKMA.Analysis.Operator.Dilation.Minimal
public import CKMA.Analysis.Operator.Dilation.UnitaryExists
public import CKMA.Analysis.Operator.Dilation.UnitaryUnique
public import CKMA.Analysis.Operator.Dilation.Wold
public import CKMA.Analysis.Operator.Dilation.CommutantLift
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Wold decomposition, minimal dilations, and commuting lifts

The wandering subspace is the kernel of the adjoint of an isometry, and the unitary part is the
intersection of its forward ranges. Wold decomposition expresses the shift part by an
unconditional sum with coefficients in that actual wandering space.

Unitary power dilation uses two-sided orbit minimality; isometric dilation uses forward orbits
and an explicit co-invariance identity. Commutant lifting preserves the norm and the full
coextension identity. Sources: GAPS 21.26, 21.30, and 21.37.

## Main definitions

* `CKMA.IsMinimalUnitaryPowerDilation`: minimal unitary power dilation of a contraction.
* `CKMA.IsMinimalIsometricDilation`: minimal co-invariant isometric dilation of a contraction.

## Main results

* `CKMA.wold_decomposition`: Wold's orthogonal unitary/shift decomposition of an isometry.
* `CKMA.exists_minimalUnitaryPowerDilation`: Sz.-Nagy's minimal unitary power dilation theorem.
* `CKMA.minimalUnitaryPowerDilation_unique`: uniqueness of a minimal unitary power dilation up to
  unitary equivalence.
* `CKMA.exists_minimalIsometricDilation`: existence of a minimal isometric dilation.
* `CKMA.commutant_lifting`: Sz.-Nagy–Foiaş commutant lifting theorem, on any co-invariant
  isometric dilation.
-/

@[expose] public section

noncomputable section

namespace CKMA

open scoped InnerProductSpace
open ContinuousLinearMap

universe u

variable {H K L : Type u}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]

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
      HasSum (fun n ↦ (V.toContinuousLinearMap ^ n) (w n)) (x - u) :=
  ⟨woldUnitarySubspace_invariant V, woldUnitarySubspace_preimage V, woldShift_inner_eq_zero V,
    woldUnitary_inner_shift_eq_zero V, wold_hasSum_decomposition V⟩

/-- Power dilation and two-sided orbit minimality for a unitary realization. -/
def IsMinimalUnitaryPowerDilation (T : H →L[ℂ] H) (J : H →ₗᵢ[ℂ] K)
    (U : K ≃ₗᵢ[ℂ] K) : Prop :=
  (∀ n : ℕ, ∀ x : H, J.toContinuousLinearMap.adjoint ((U^[n]) (J x)) = (T ^ n) x) ∧
    (Submodule.span ℂ {y : K | ∃ k : ℤ, ∃ x : H, y = (U ^ k) (J x)}).topologicalClosure = ⊤

/-- **21.30**: every contraction admits a minimal unitary power dilation. -/
theorem exists_minimalUnitaryPowerDilation (T : H →L[ℂ] H) (hT : ‖T‖ ≤ 1) :
    ∃ M : ComplexHilbertSpace.{u}, ∃ J : H →ₗᵢ[ℂ] M.carrier,
      ∃ U : M.carrier ≃ₗᵢ[ℂ] M.carrier, IsMinimalUnitaryPowerDilation T J U := by
  obtain ⟨M, J, U, hpow, hmin⟩ := exists_minimalUnitaryPowerDilation_data T hT
  exact ⟨M, J, U, ⟨hpow, hmin⟩⟩

/-- Uniqueness is the unique unitary preserving the embedded original space and intertwining
both dilations; it follows from their two-sided orbit minimality. -/
theorem minimalUnitaryPowerDilation_unique (T : H →L[ℂ] H)
    (J : H →ₗᵢ[ℂ] K) (U : K ≃ₗᵢ[ℂ] K) (hU : IsMinimalUnitaryPowerDilation T J U)
    (J' : H →ₗᵢ[ℂ] L) (U' : L ≃ₗᵢ[ℂ] L) (hU' : IsMinimalUnitaryPowerDilation T J' U') :
    ∃! W : K ≃ₗᵢ[ℂ] L, (∀ x, W (J x) = J' x) ∧ ∀ y, W (U y) = U' (W y) := by
  rcases hU with ⟨hpow, hmin⟩
  rcases hU' with ⟨hpow', hmin'⟩
  let W := unitaryDilationEquiv T J U hpow hmin J' U' hpow' hmin'
  refine ⟨W, ⟨?_, ?_⟩, ?_⟩
  · intro x
    exact unitaryDilationEquiv_embed T J U hpow hmin J' U' hpow' hmin' x
  · intro y
    exact unitaryDilationEquiv_intertwining T J U hpow hmin J' U' hpow' hmin' y
  · intro W' hW'
    exact unitaryDilationEquiv_unique T J U hpow hmin J' U' hpow' hmin' W' hW'.1 hW'.2

/-- Minimal isometric dilation with the original space co-invariant. -/
def IsMinimalIsometricDilation (T : H →L[ℂ] H) (J : H →ₗᵢ[ℂ] K)
    (V : K →ₗᵢ[ℂ] K) : Prop :=
  (∀ y : K, J.toContinuousLinearMap.adjoint (V y) = T (J.toContinuousLinearMap.adjoint y)) ∧
    (Submodule.span ℂ {y : K | ∃ n : ℕ, ∃ x : H,
      y = (V.toContinuousLinearMap ^ n) (J x)}).topologicalClosure = ⊤

/-- The minimal isometric dilation required by the commutant-lifting interface exists. -/
theorem exists_minimalIsometricDilation (T : H →L[ℂ] H) (hT : ‖T‖ ≤ 1) :
    ∃ M : ComplexHilbertSpace.{u}, ∃ J : H →ₗᵢ[ℂ] M.carrier,
      ∃ V : M.carrier →ₗᵢ[ℂ] M.carrier, IsMinimalIsometricDilation T J V := by
  obtain ⟨M, J, V, hcoin, hmin⟩ := exists_minimalIsometricDilation_data T hT
  exact ⟨M, J, V, ⟨hcoin, hmin⟩⟩

/-- **21.37**: an operator commuting with a contraction has a norm-preserving commuting lift
on any isometric dilation with the original space co-invariant, with the full coextension
identity. Minimality of the dilation is not needed; in particular the lift exists on the
minimal isometric dilation of `IsMinimalIsometricDilation`. -/
theorem commutant_lifting (T X : H →L[ℂ] H) (hXT : Commute X T)
    (J : H →ₗᵢ[ℂ] K) (V : K →ₗᵢ[ℂ] K)
    (hcoin : ∀ y : K, J.toContinuousLinearMap.adjoint (V y) =
      T (J.toContinuousLinearMap.adjoint y)) :
    ∃ Y : K →L[ℂ] K, Commute Y V.toContinuousLinearMap ∧ ‖Y‖ = ‖X‖ ∧
      ∀ y : K, J.toContinuousLinearMap.adjoint (Y y) = X (J.toContinuousLinearMap.adjoint y) := by
  let Y : K →L[ℂ] K := commutantLiftCLM T X hXT J V hcoin
  refine ⟨Y, ?_, ?_, ?_⟩
  · rw [Commute, SemiconjBy, mul_def, mul_def]
    ext y
    simp [Y, commutantLiftCLM_apply, commutantLiftAt_apply_isometry T X hXT J V hcoin,
      LinearIsometry.coe_toContinuousLinearMap]
  · apply le_antisymm
    · exact norm_commutantLiftCLM_le T X hXT J V hcoin
    · have hbound : ∀ x : H, ‖X x‖ ≤ ‖Y‖ * ‖x‖ := by
        intro x
        have hcoe : J.toContinuousLinearMap.adjoint (Y (J x)) = X x := by
          rw [show Y (J x) = commutantLiftAt T X hXT J V hcoin (J x) from
            commutantLiftCLM_apply T X hXT J V hcoin (J x)]
          rw [adjoint_commutantLiftAt T X hXT J V hcoin, coextensionCompress,
            comp_apply, embed_adjoint_leftInverse]
        calc
          ‖X x‖ = ‖J.toContinuousLinearMap.adjoint (Y (J x))‖ := by rw [hcoe]
          _ ≤ ‖J.toContinuousLinearMap.adjoint‖ * ‖Y (J x)‖ := le_opNorm _ _
          _ ≤ 1 * (‖Y‖ * ‖J x‖) := by
            gcongr
            · exact norm_embed_adjoint_le J
            · exact le_opNorm Y (J x)
          _ = ‖Y‖ * ‖x‖ := by rw [one_mul, J.norm_map]
      exact opNorm_le_bound X (norm_nonneg Y) hbound
  · intro y
    rw [show Y y = commutantLiftAt T X hXT J V hcoin y from
      commutantLiftCLM_apply T X hXT J V hcoin y,
      adjoint_commutantLiftAt T X hXT J V hcoin, coextensionCompress, comp_apply]


@[deprecated (since := "2026-11-15")] alias commutant_lifting_of := commutant_lifting

end CKMA
