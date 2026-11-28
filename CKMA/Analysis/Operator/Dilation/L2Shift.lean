/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.l2Space

import CKMA.Analysis.InnerProductSpace.LpTwo

/-!
# Unilateral shift on `ℓ²(ℕ, H)`

Schäffer's isometric dilation inserts the defect vector at index zero and shifts the existing
`ℓ²` sequence one step to the right. Both maps are linear isometries,
and the inserted vector is orthogonal to the shifted sequence.

## Main definitions

* `CKMA.l2ShiftRight`: right shift on `ℓ²(ℕ, H)`.
* `CKMA.l2InsertZero`: isometric insertion of a vector at index `0` in `ℓ²(ℕ, H)`.

## Main results

* `CKMA.norm_l2ShiftRightElem`: the right shift on `ℓ²(ℕ, H)` is isometric.
* `CKMA.norm_l2InsertZero`: insertion at index `0` is isometric.
* `CKMA.inner_l2InsertZero_l2ShiftRight`: orthogonality of the inserted vector and the shifted
  sequence.
* `CKMA.norm_sq_l2Cons`: the squared norm of an inserted vector plus a shifted sequence is the
  sum of the squared norms.
-/

public section

noncomputable section

namespace CKMA

open scoped InnerProductSpace

universe u

variable {H : Type u} [NormedAddCommGroup H]

/-- Right shift of a sequence, with a zero inserted at index `0`. -/
@[expose]
def l2ShiftRightFun (f : ℕ → H) (n : ℕ) : H :=
  if n = 0 then 0 else f (n - 1)

/-- The right shift vanishes at index zero. -/
@[simp]
theorem l2ShiftRightFun_zero (f : ℕ → H) : l2ShiftRightFun f 0 = 0 := by
  simp [l2ShiftRightFun]

/-- The right shift moves the value at `n` to index `n + 1`. -/
@[simp]
theorem l2ShiftRightFun_succ (f : ℕ → H) (n : ℕ) : l2ShiftRightFun f (n + 1) = f n := by
  simp [l2ShiftRightFun]

/-- Squared norms of a right-shifted `ℓ²` sequence remain summable. -/
theorem summable_norm_sq_l2ShiftRightFun (f : lp (fun _ : ℕ => H) 2) :
    Summable fun n => ‖l2ShiftRightFun (f : ℕ → H) n‖ ^ 2 := by
  refine (summable_nat_add_iff (f := fun n => ‖l2ShiftRightFun (f : ℕ → H) n‖ ^ 2) 1).mp ?_
  simpa [l2ShiftRightFun_succ] using lp.summable_norm_sq f

/-- The right shift of an `ℓ²` sequence, as an element of `ℓ²`. -/
@[expose]
def l2ShiftRightElem (f : lp (fun _ : ℕ => H) 2) : lp (fun _ : ℕ => H) 2 :=
  ⟨l2ShiftRightFun (f : ℕ → H),
    memℓp_gen (by
      simpa [ENNReal.toReal_ofNat, Real.rpow_natCast] using summable_norm_sq_l2ShiftRightFun f)⟩

/-- Evaluation of the right shift. -/
theorem l2ShiftRightElem_apply (f : lp (fun _ : ℕ => H) 2) (n : ℕ) :
    l2ShiftRightElem f n = l2ShiftRightFun (f : ℕ → H) n :=
  rfl

/-- The right shift is additive. -/
theorem l2ShiftRightElem_add (f g : lp (fun _ : ℕ => H) 2) :
    l2ShiftRightElem (f + g) = l2ShiftRightElem f + l2ShiftRightElem g := by
  apply lp.ext
  funext n
  simp [l2ShiftRightElem_apply, l2ShiftRightFun, apply_ite₂]

/-- Right shift preserves the `ℓ²` norm. -/
theorem norm_l2ShiftRightElem (f : lp (fun _ : ℕ => H) 2) :
    ‖l2ShiftRightElem f‖ = ‖f‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), lp.norm_sq_eq_tsum, lp.norm_sq_eq_tsum,
    ← (lp.summable_norm_sq (l2ShiftRightElem f)).sum_add_tsum_nat_add 1]
  simp [l2ShiftRightElem_apply]

variable [InnerProductSpace ℂ H]

/-- The right shift commutes with scalar multiplication. -/
theorem l2ShiftRightElem_smul (c : ℂ) (f : lp (fun _ : ℕ => H) 2) :
    l2ShiftRightElem (c • f) = c • l2ShiftRightElem f := by
  apply lp.ext
  funext n
  simp [l2ShiftRightElem_apply, l2ShiftRightFun, lp.coeFn_smul]

/-- The right shift as a linear map on `ℓ²(ℕ, H)`. -/
@[expose]
def l2ShiftRightLinear : lp (fun _ : ℕ => H) 2 →ₗ[ℂ] lp (fun _ : ℕ => H) 2 where
  toFun := l2ShiftRightElem
  map_add' := l2ShiftRightElem_add
  map_smul' := l2ShiftRightElem_smul

/-- `l2ShiftRightLinear` applies `l2ShiftRightElem`. -/
theorem l2ShiftRightLinear_apply (f : lp (fun _ : ℕ => H) 2) :
    l2ShiftRightLinear f = l2ShiftRightElem f :=
  rfl

/-- The right shift as a continuous linear map on `ℓ²(ℕ, H)`. -/
@[expose]
def l2ShiftRight : lp (fun _ : ℕ => H) 2 →L[ℂ] lp (fun _ : ℕ => H) 2 :=
  l2ShiftRightLinear.mkContinuous 1 fun f => by
    rw [one_mul]
    simpa [l2ShiftRightLinear] using (norm_l2ShiftRightElem f).le

/-- Evaluation of the continuous right shift. -/
theorem l2ShiftRight_apply (f : lp (fun _ : ℕ => H) 2) :
    l2ShiftRight f = l2ShiftRightElem f :=
  rfl

/-- Insert a vector as the sequence supported at index zero. -/
@[expose]
def l2InsertZero : H →L[ℂ] lp (fun _ : ℕ => H) 2 :=
  lp.singleContinuousLinearMap ℂ (fun _ : ℕ => H) 2 0

/-- Inserting a vector agrees with `lp.single`. -/
theorem l2InsertZero_apply (v : H) : l2InsertZero v = lp.single 2 0 v :=
  rfl

/-- Insertion at index zero preserves norms. -/
theorem norm_l2InsertZero (v : H) : ‖l2InsertZero v‖ = ‖v‖ := by
  rw [l2InsertZero_apply]
  exact lp.norm_single (E := fun _ : ℕ => H) (p := 2)
    ((zero_lt_one : (0 : ENNReal) < 1).trans ENNReal.one_lt_two) 0 v

/-- A vector inserted at index zero is orthogonal to every right-shifted sequence. -/
theorem inner_l2InsertZero_l2ShiftRight (v : H) (f : lp (fun _ : ℕ => H) 2) :
    ⟪l2InsertZero v, l2ShiftRight f⟫_ℂ = 0 := by
  rw [l2InsertZero_apply, l2ShiftRight_apply]
  rw [lp.inner_single_left (𝕜 := ℂ) 0 v (l2ShiftRightElem f)]
  simp [l2ShiftRightElem_apply, l2ShiftRightFun_zero]

/-- The sum of an inserted vector and a right shift splits the squared norm. -/
theorem norm_sq_l2Cons (v : H) (f : lp (fun _ : ℕ => H) 2) :
    ‖l2InsertZero v + l2ShiftRight f‖ ^ 2 = ‖v‖ ^ 2 + ‖f‖ ^ 2 := by
  have horth := inner_l2InsertZero_l2ShiftRight v f
  have hpyth := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (l2InsertZero v) (l2ShiftRight f) horth
  rw [← pow_two, ← pow_two, ← pow_two] at hpyth
  rw [hpyth, norm_l2InsertZero, l2ShiftRight_apply, norm_l2ShiftRightElem]

end CKMA
