/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.Operator.Dilation.Wold
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict

/-!
# Unitary part of an isometry

On the intersection of the forward ranges, an isometry is unitary. Its inverse is the adjoint.
This is the unitary summand in Wold's decomposition, as in Sz.-Nagy–Foiaş–Bercovici–Kérchy,
Chapter I, Section 1.
-/

@[expose] public section

noncomputable section

namespace CKMA

open scoped InnerProductSpace
open ContinuousLinearMap Submodule

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The unitary part is closed, as an intersection of closed ranges of isometries. -/
theorem isClosed_woldUnitarySubspace (V : H →ₗᵢ[ℂ] H) :
    IsClosed (woldUnitarySubspace V : Set H) := by
  rw [woldUnitarySubspace, coe_iInf]
  refine isClosed_iInter fun n => ?_
  have hrange : (LinearMap.range ((V.toContinuousLinearMap ^ n).toLinearMap) : Set H) =
      Set.range (V ^ n) := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy⟩ := LinearMap.mem_range.mp hx
      refine ⟨y, ?_⟩
      rw [isometry_pow_apply, ← toLinearMap_pow_apply]
      exact hy
    · rintro ⟨y, rfl⟩
      refine LinearMap.mem_range.mpr ⟨y, ?_⟩
      rw [toLinearMap_pow_apply, ← isometry_pow_apply]
  rw [hrange]
  exact (V ^ n).antilipschitzWith.isClosed_range (V ^ n).isometry.uniformContinuous

/-- The unitary part is a Hilbert space. -/
instance completeSpace_woldUnitarySubspace (V : H →ₗᵢ[ℂ] H) :
    CompleteSpace (woldUnitarySubspace V) :=
  (isClosed_woldUnitarySubspace V).completeSpace_coe

/-- The isometry, restricted to its unitary part. -/
def woldUnitaryRestrictCLM (V : H →ₗᵢ[ℂ] H) :
    woldUnitarySubspace V →L[ℂ] woldUnitarySubspace V :=
  V.toContinuousLinearMap.restrict fun u hu => by
    rw [LinearIsometry.coe_toContinuousLinearMap]
    exact woldUnitarySubspace_invariant V u hu

omit [CompleteSpace H] in
/-- Evaluation of the restricted isometry in `H`. -/
theorem coe_woldUnitaryRestrictCLM (V : H →ₗᵢ[ℂ] H) (u : woldUnitarySubspace V) :
    (woldUnitaryRestrictCLM V u : H) = V (u : H) := by
  rw [woldUnitaryRestrictCLM, coe_restrict_apply, LinearIsometry.coe_toContinuousLinearMap]

/-- The restricted isometry preserves norms. -/
def woldUnitaryIsometry (V : H →ₗᵢ[ℂ] H) :
    woldUnitarySubspace V →ₗᵢ[ℂ] woldUnitarySubspace V where
  toLinearMap := (woldUnitaryRestrictCLM V).toLinearMap
  norm_map' u := by
    have hmap : (woldUnitaryRestrictCLM V).toLinearMap u = woldUnitaryRestrictCLM V u := rfl
    rw [hmap, ← norm_coe, ← norm_coe, coe_woldUnitaryRestrictCLM]
    exact V.norm_map (u : H)

omit [CompleteSpace H] in
/-- Evaluation of the restricted isometry. -/
theorem woldUnitaryIsometry_apply (V : H →ₗᵢ[ℂ] H) (u : woldUnitarySubspace V) :
    woldUnitaryIsometry V u = woldUnitaryRestrictCLM V u :=
  rfl

/-- The restricted isometry agrees in `H` with the original isometry. -/
theorem coe_woldUnitaryIsometry (V : H →ₗᵢ[ℂ] H) (u : woldUnitarySubspace V) :
    (woldUnitaryIsometry V u : H) = V (u : H) := by
  rw [woldUnitaryIsometry_apply, coe_woldUnitaryRestrictCLM]

/-- The restricted isometry is surjective. -/
theorem woldUnitaryIsometry_surjective (V : H →ₗᵢ[ℂ] H) :
    Function.Surjective (woldUnitaryIsometry V) := by
  intro u
  obtain ⟨v, hv, hVv⟩ := woldUnitarySubspace_preimage V (u : H) u.property
  refine ⟨⟨v, hv⟩, ?_⟩
  apply Subtype.ext
  rw [coe_woldUnitaryIsometry]
  exact hVv

/-- The isometry is unitary on its unitary part. -/
def woldUnitaryEquiv (V : H →ₗᵢ[ℂ] H) :
    woldUnitarySubspace V ≃ₗᵢ[ℂ] woldUnitarySubspace V :=
  LinearIsometryEquiv.ofSurjective (woldUnitaryIsometry V) (woldUnitaryIsometry_surjective V)

/-- Evaluation of the unitary on the unitary part. -/
theorem woldUnitaryEquiv_apply (V : H →ₗᵢ[ℂ] H) (u : woldUnitarySubspace V) :
    woldUnitaryEquiv V u = woldUnitaryIsometry V u :=
  rfl

/-- The unitary on the unitary part agrees in `H` with the original isometry. -/
theorem coe_woldUnitaryEquiv (V : H →ₗᵢ[ℂ] H) (u : woldUnitarySubspace V) :
    (woldUnitaryEquiv V u : H) = V (u : H) := by
  rw [woldUnitaryEquiv_apply, coe_woldUnitaryIsometry]

/-- The inverse unitary is the adjoint, read in `H`. -/
theorem coe_woldUnitaryEquiv_symm (V : H →ₗᵢ[ℂ] H) (u : woldUnitarySubspace V) :
    ((woldUnitaryEquiv V).symm u : H) = V.toContinuousLinearMap.adjoint (u : H) := by
  have hV : V ((woldUnitaryEquiv V).symm u : H) = (u : H) := by
    rw [← coe_woldUnitaryEquiv, LinearIsometryEquiv.apply_symm_apply]
  calc
    ((woldUnitaryEquiv V).symm u : H)
        = V.toContinuousLinearMap.adjoint (V ((woldUnitaryEquiv V).symm u : H)) :=
          (adjoint_isometry_apply V _).symm
    _ = V.toContinuousLinearMap.adjoint (u : H) := by rw [hV]

end CKMA
