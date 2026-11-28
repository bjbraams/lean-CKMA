/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.Operator.Dilation.Minimal
public import CKMA.Analysis.Operator.Dilation.UnitaryExists
public import CKMA.Analysis.Operator.Dilation.UnitaryUnique
public import CKMA.Analysis.Operator.Dilation.Wold
public import CKMA.Analysis.Operator.Dilation.CommutantLift

/-!
# Wold decomposition, minimal dilations, and commuting lifts

The wandering subspace is the kernel of the adjoint of an isometry, and the unitary part is the
intersection of its forward ranges. Wold decomposition expresses the shift part by an
unconditional sum with coefficients in the wandering space `ker V*`.

Unitary power dilation uses two-sided orbit minimality; isometric dilation uses forward orbits
and an explicit co-invariance identity. Commutant lifting preserves the norm and the full
coextension identity. Sources: GAPS 21.26, 21.30, and 21.37.

This module re-exports the dilation files. `CKMA.IsMinimalIsometricDilation` and
`CKMA.exists_minimalIsometricDilation` are in `CKMA.Analysis.Operator.Dilation.Minimal`;
`CKMA.IsMinimalUnitaryPowerDilation` and `CKMA.minimalUnitaryPowerDilation_unique` (uniqueness up
to unitary equivalence) are in `CKMA.Analysis.Operator.Dilation.UnitaryUnique`;
`CKMA.exists_minimalUnitaryPowerDilation` (Sz.-Nagy's dilation theorem) is in
`CKMA.Analysis.Operator.Dilation.UnitaryExists`.

## Main results

* `CKMA.wold_decomposition`: Wold's orthogonal unitary/shift decomposition of an isometry.
* `CKMA.commutant_lifting`: Sz.-Nagy–Foiaş commutant lifting theorem, on any co-invariant
  isometric dilation.
-/

public section

noncomputable section

namespace CKMA

open scoped InnerProductSpace
open ContinuousLinearMap

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [CompleteSpace E]

/-- **21.26**: Wold's orthogonal unitary/shift decomposition. The coefficients of the shift part
lie in the wandering space `ker V*`, and the expansion is unconditional. -/
theorem wold_decomposition (V : E →ₗᵢ[𝕜] E) :
    (∀ u ∈ woldUnitarySubspace V, V u ∈ woldUnitarySubspace V) ∧
    (∀ u ∈ woldUnitarySubspace V, ∃ v ∈ woldUnitarySubspace V, V v = u) ∧
    (∀ (m n : ℕ), m ≠ n → ∀ u v : woldWanderingSubspace V,
      ⟪(V.toContinuousLinearMap ^ m) u, (V.toContinuousLinearMap ^ n) v⟫_𝕜 = 0) ∧
    (∀ u ∈ woldUnitarySubspace V, ∀ n : ℕ, ∀ w : woldWanderingSubspace V,
      ⟪u, (V.toContinuousLinearMap ^ n) w⟫_𝕜 = 0) ∧
    ∀ x : E, ∃ u ∈ woldUnitarySubspace V, ∃ w : ℕ → woldWanderingSubspace V,
      HasSum (fun n ↦ (V.toContinuousLinearMap ^ n) (w n)) (x - u) :=
  ⟨woldUnitarySubspace_invariant V, woldUnitarySubspace_preimage V, woldShift_inner_eq_zero V,
    woldUnitary_inner_shift_eq_zero V, wold_hasSum_decomposition V⟩

variable {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

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
            comp_apply, linearIsometry_adjoint_apply_self]
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

end CKMA
