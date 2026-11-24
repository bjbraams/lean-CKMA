/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

import TauCeti.Analysis.InnerProductSpace.Positive.Basic

/-!
# Defect operator of a Hilbert-space contraction

For a contraction `T`, the operator `1 - T* T` is positive, and its continuous functional
calculus square root is the defect operator. The identity `‖T x‖² + ‖D_T x‖² = ‖x‖²` is the
norm computation behind Schäffer's isometric dilation.

## Main definitions

* `CKMA.defectOperator`: the defect operator `(1 - T* T)^{1/2}` of a contraction `T`.

## Main results

* `CKMA.contraction_one_sub_star_mul_self_nonneg`: positivity of `1 - T* T` for a contraction.
* `CKMA.defectOperator_mul_self`: the defect operator of a contraction squares to `1 - T* T`.
* `CKMA.norm_sq_add_norm_sq_defectOperator`: Pythagorean identity `‖T x‖² + ‖D_T x‖² = ‖x‖²`.
-/

public section

noncomputable section

namespace CKMA

open scoped InnerProductSpace

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A contraction satisfies `T* T ≤ 1`. -/
private theorem star_mul_self_le_one_of_norm_le_one (T : H →L[ℂ] H) (hT : ‖T‖ ≤ 1) :
    star T * T ≤ 1 := by
  simpa [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.mul_def] using
    (ContinuousLinearMap.self_comp_adjoint_le_one_iff (ContinuousLinearMap.adjoint T)).2
      (by rwa [LinearIsometryEquiv.norm_map])

/-- The defect element `1 - T* T` of a contraction is positive. -/
theorem contraction_one_sub_star_mul_self_nonneg (T : H →L[ℂ] H) (hT : ‖T‖ ≤ 1) :
    0 ≤ (1 - star T * T : H →L[ℂ] H) :=
  sub_nonneg.mpr (star_mul_self_le_one_of_norm_le_one T hT)

/-- The defect operator `CFC.sqrt (1 - star T * T)`.

`CFC.sqrt` is `0` when its argument is not nonnegative. For `‖T‖ ≤ 1`,
`defectOperator_mul_self` is the square identity. -/
@[expose]
def defectOperator (T : H →L[ℂ] H) : H →L[ℂ] H :=
  CFC.sqrt (1 - star T * T)

/-- The defect operator of a contraction squares to `1 - T* T`. -/
theorem defectOperator_mul_self (T : H →L[ℂ] H) (hT : ‖T‖ ≤ 1) :
    defectOperator T * defectOperator T = 1 - star T * T := by
  rw [defectOperator]
  exact CFC.sqrt_mul_sqrt_self _
    (contraction_one_sub_star_mul_self_nonneg T hT)

/-- The defect operator of any operator is self-adjoint. -/
private theorem defectOperator_adjoint (T : H →L[ℂ] H) :
    (defectOperator T).adjoint = defectOperator T := by
  rw [← ContinuousLinearMap.star_eq_adjoint]
  exact (CFC.sqrt_nonneg (1 - star T * T)).star_eq

/-- Pythagorean identity for a contraction and its defect operator. -/
theorem norm_sq_add_norm_sq_defectOperator (T : H →L[ℂ] H) (hT : ‖T‖ ≤ 1) (x : H) :
    ‖T x‖ ^ 2 + ‖defectOperator T x‖ ^ 2 = ‖x‖ ^ 2 := by
  let D : H →L[ℂ] H := defectOperator T
  have hsq : D * D = 1 - star T * T := defectOperator_mul_self T hT
  have hDadj : D.adjoint = D := defectOperator_adjoint T
  have hTsq := ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_left T x
  have hDsq := ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_left D x
  have hTcomp : T.adjoint ∘L T = star T * T := by
    rw [← ContinuousLinearMap.star_eq_adjoint, ← ContinuousLinearMap.mul_def]
  have hDcomp : D.adjoint ∘L D = D * D := by
    rw [hDadj, ← ContinuousLinearMap.mul_def]
  rw [hTsq, hDsq, hTcomp, hDcomp, hsq]
  have hadd :
      ⟪(star T * T) x, x⟫_ℂ + ⟪(1 - star T * T) x, x⟫_ℂ =
        ⟪((star T * T) + (1 - star T * T)) x, x⟫_ℂ := by
    rw [← inner_add_left, add_apply]
  have hre :
      RCLike.re ⟪(star T * T) x, x⟫_ℂ + RCLike.re ⟪(1 - star T * T) x, x⟫_ℂ =
        RCLike.re (⟪(star T * T) x, x⟫_ℂ + ⟪(1 - star T * T) x, x⟫_ℂ) :=
    (map_add (RCLike.re (K := ℂ)) _ _).symm
  rw [hre, hadd]
  have hcancel : (star T * T) + (1 - star T * T) = (1 : H →L[ℂ] H) := by
    rw [← add_sub_assoc]
    exact add_sub_cancel_left (star T * T) 1
  rw [hcancel, ContinuousLinearMap.one_def, ContinuousLinearMap.id_apply]
  exact inner_self_eq_norm_sq (𝕜 := ℂ) x

end CKMA
