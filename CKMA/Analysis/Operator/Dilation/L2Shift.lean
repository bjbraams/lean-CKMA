/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Unilateral shift on `ℓ²(ℕ, H)`

Schäffer's isometric dilation inserts the defect vector at index zero and shifts the existing
`ℓ²` sequence one step to the right. Both maps are linear isometries up to the inserted vector,
and the inserted vector is orthogonal to the shifted sequence.
-/

@[expose] public section

noncomputable section

namespace CKMA

open scoped InnerProductSpace

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Right shift of a sequence, with a zero inserted at index `0`. -/
def l2ShiftRightFun (f : ℕ → H) (n : ℕ) : H :=
  if n = 0 then 0 else f (n - 1)

omit [InnerProductSpace ℂ H] in
/-- The right shift vanishes at index zero. -/
theorem l2ShiftRightFun_zero (f : ℕ → H) : l2ShiftRightFun f 0 = 0 := by
  simp [l2ShiftRightFun]

omit [InnerProductSpace ℂ H] in
/-- The right shift moves the value at `n` to index `n + 1`. -/
theorem l2ShiftRightFun_succ (f : ℕ → H) (n : ℕ) : l2ShiftRightFun f (n + 1) = f n := by
  simp [l2ShiftRightFun]

omit [InnerProductSpace ℂ H] in
/-- Squared norms of a right-shifted `ℓ²` sequence remain summable. -/
theorem summable_norm_sq_l2ShiftRightFun (f : lp (fun _ : ℕ => H) 2) :
    Summable fun n => ‖l2ShiftRightFun (f : ℕ → H) n‖ ^ (2 : ℝ) := by
  have hp : 0 < (2 : ENNReal).toReal := by
    rw [ENNReal.toReal_ofNat]
    norm_num
  have hsum : Summable fun n => ‖(f : ℕ → H) n‖ ^ (2 : ℝ) := by
    have hmem := (memℓp_gen_iff (p := 2) hp).1 (lp.memℓp f)
    rw [ENNReal.toReal_ofNat] at hmem
    exact hmem
  have htail : Summable fun n => ‖l2ShiftRightFun (f : ℕ → H) (n + 1)‖ ^ (2 : ℝ) := by
    simpa [l2ShiftRightFun_succ] using hsum
  exact (summable_nat_add_iff (f := fun n => ‖l2ShiftRightFun (f : ℕ → H) n‖ ^ (2 : ℝ)) 1).mp
    htail

/-- The right shift of an `ℓ²` sequence, as an element of `ℓ²`. -/
def l2ShiftRightElem (f : lp (fun _ : ℕ => H) 2) : lp (fun _ : ℕ => H) 2 :=
  ⟨l2ShiftRightFun (f : ℕ → H),
    memℓp_gen (by
      simpa [ENNReal.toReal_ofNat] using summable_norm_sq_l2ShiftRightFun f)⟩

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

/-- The right shift commutes with scalar multiplication. -/
theorem l2ShiftRightElem_smul (c : ℂ) (f : lp (fun _ : ℕ => H) 2) :
    l2ShiftRightElem (c • f) = c • l2ShiftRightElem f := by
  apply lp.ext
  funext n
  simp [l2ShiftRightElem_apply, l2ShiftRightFun, lp.coeFn_smul]

/-- The right shift as a linear map on `ℓ²(ℕ, H)`. -/
def l2ShiftRightLinear : lp (fun _ : ℕ => H) 2 →ₗ[ℂ] lp (fun _ : ℕ => H) 2 where
  toFun := l2ShiftRightElem
  map_add' := l2ShiftRightElem_add
  map_smul' := l2ShiftRightElem_smul

omit [InnerProductSpace ℂ H] in
/-- The squared `ℓ²` norm is the sum of the squared coordinate norms. -/
theorem lp_norm_sq_eq_tsum (f : lp (fun _ : ℕ => H) 2) :
    ‖f‖ ^ 2 = ∑' n, ‖(f : ℕ → H) n‖ ^ 2 := by
  have hp : 0 < (2 : ENNReal).toReal := by
    rw [ENNReal.toReal_ofNat]
    norm_num
  have h := lp.norm_rpow_eq_tsum (p := 2) hp f
  rw [ENNReal.toReal_ofNat] at h
  simpa [Real.rpow_natCast] using h

/-- Right shift preserves the `ℓ²` norm. -/
theorem norm_l2ShiftRightElem (f : lp (fun _ : ℕ => H) 2) :
    ‖l2ShiftRightElem f‖ = ‖f‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
  rw [lp_norm_sq_eq_tsum (l2ShiftRightElem f), lp_norm_sq_eq_tsum f]
  have hcoord : ∀ n, ‖(l2ShiftRightElem f : ℕ → H) (n + 1)‖ ^ 2 =
      ‖(f : ℕ → H) n‖ ^ 2 := by
    intro n
    simp [l2ShiftRightElem_apply, l2ShiftRightFun_succ]
  have hsumf : Summable fun n => ‖(f : ℕ → H) n‖ ^ 2 := by
    have hp : 0 < (2 : ENNReal).toReal := by
      rw [ENNReal.toReal_ofNat]
      norm_num
    have hmem := (memℓp_gen_iff (p := 2) hp).1 (lp.memℓp f)
    rw [ENNReal.toReal_ofNat] at hmem
    simpa [Real.rpow_natCast] using hmem
  have htail : Summable fun n => ‖(l2ShiftRightElem f : ℕ → H) (n + 1)‖ ^ 2 := by
    have hfun : (fun n => ‖(l2ShiftRightElem f : ℕ → H) (n + 1)‖ ^ 2) =
        fun n => ‖(f : ℕ → H) n‖ ^ 2 := by
      funext n
      exact hcoord n
    simpa [hfun] using hsumf
  have htsum : ∑' n, ‖(l2ShiftRightElem f : ℕ → H) (n + 1)‖ ^ 2 =
      ∑' n, ‖(f : ℕ → H) n‖ ^ 2 :=
    tsum_congr hcoord
  have hwhole : Summable fun n => ‖(l2ShiftRightElem f : ℕ → H) n‖ ^ 2 :=
    (summable_nat_add_iff 1).mp htail
  rw [← hwhole.sum_add_tsum_nat_add 1, htsum]
  simp [l2ShiftRightElem_apply, l2ShiftRightFun_zero]

/-- The right shift as a continuous linear map on `ℓ²(ℕ, H)`. -/
def l2ShiftRight : lp (fun _ : ℕ => H) 2 →L[ℂ] lp (fun _ : ℕ => H) 2 :=
  l2ShiftRightLinear.mkContinuous 1 fun f => by
    rw [one_mul]
    simpa [l2ShiftRightLinear] using (norm_l2ShiftRightElem f).le

/-- Evaluation of the continuous right shift. -/
theorem l2ShiftRight_apply (f : lp (fun _ : ℕ => H) 2) :
    l2ShiftRight f = l2ShiftRightElem f :=
  rfl

/-- Insert a vector as the sequence supported at index zero. -/
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
