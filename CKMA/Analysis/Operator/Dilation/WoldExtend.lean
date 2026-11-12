/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.Operator.Dilation.WoldSum
public import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Unitary extension of an isometry

Wold's decomposition realises an isometry as a unitary on the unitary part plus a unilateral
shift. Padding the wandering coefficients by zero on the negative integers extends that shift
to a bilateral unitary. The closed span of the two-sided orbit is the whole extended space.
This is the unitary extension in Sz.-Nagy–Foiaş–Bercovici–Kérchy, Chapter I.
-/

@[expose] public section

noncomputable section

namespace CKMA

open scoped InnerProductSpace
open ContinuousLinearMap Submodule

universe u

variable {ι : Type*} {G : ι → Type u} [∀ i, NormedAddCommGroup (G i)]

/-- The squared `ℓ²` norm is the sum of the squared coordinate norms. -/
theorem woldLp_norm_sq_eq_tsum (f : lp G 2) :
    ‖f‖ ^ 2 = ∑' i, ‖(f : ∀ i, G i) i‖ ^ 2 := by
  have hp : 0 < (2 : ENNReal).toReal := by
    rw [ENNReal.toReal_ofNat]
    norm_num
  have h := lp.norm_rpow_eq_tsum (p := 2) hp f
  rw [ENNReal.toReal_ofNat] at h
  simpa [Real.rpow_natCast] using h

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Summands of the bilateral extension, indexed by the unitary slot and `ℤ`. -/
@[reducible] def woldSummandInt (V : H →ₗᵢ[ℂ] H) : Option ℤ → Type u
  | none => woldUnitarySubspace V
  | some _ => woldWanderingSubspace V

/-- Each bilateral summand is a normed group. -/
instance woldSummandInt.instNormedAddCommGroup (V : H →ₗᵢ[ℂ] H) (i : Option ℤ) :
    NormedAddCommGroup (woldSummandInt V i) :=
  Option.rec (inferInstanceAs (NormedAddCommGroup (woldUnitarySubspace V)))
    (fun _ => inferInstanceAs (NormedAddCommGroup (woldWanderingSubspace V))) i

/-- Each bilateral summand is a complex inner product space. -/
instance woldSummandInt.instInnerProductSpace (V : H →ₗᵢ[ℂ] H) (i : Option ℤ) :
    InnerProductSpace ℂ (woldSummandInt V i) :=
  Option.rec (inferInstanceAs (InnerProductSpace ℂ (woldUnitarySubspace V)))
    (fun _ => inferInstanceAs (InnerProductSpace ℂ (woldWanderingSubspace V))) i

/-- Each bilateral summand is complete. -/
instance woldSummandInt.instCompleteSpace (V : H →ₗᵢ[ℂ] H) (i : Option ℤ) :
    CompleteSpace (woldSummandInt V i) :=
  Option.rec (inferInstanceAs (CompleteSpace (woldUnitarySubspace V)))
    (fun _ => inferInstanceAs (CompleteSpace (woldWanderingSubspace V))) i

/-- Nonnegative times, sent to the corresponding integer times. -/
def woldExtendIndex : Option ℕ → Option ℤ
  | none => none
  | some n => some (n : ℤ)

/-- The inclusion of nonnegative times is injective. -/
theorem woldExtendIndex_injective : Function.Injective woldExtendIndex := by
  intro a b h
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some n => simp [woldExtendIndex] at h
  | some m =>
    cases b with
    | none => simp [woldExtendIndex] at h
    | some n =>
      simp [woldExtendIndex] at h
      exact congrArg some h

/-- The unitary slot stays in the unitary slot. -/
@[simp] theorem woldExtendIndex_none : woldExtendIndex none = none :=
  rfl

/-- A nonnegative time is sent to the same integer. -/
@[simp] theorem woldExtendIndex_some (n : ℕ) : woldExtendIndex (some n) = some (n : ℤ) :=
  rfl

/-- Extend a finitely supported nonnegative coefficient by zero on negative times. -/
def woldPadFun (V : H →ₗᵢ[ℂ] H) (f : ∀ i, woldSummandNat V i) :
    ∀ i, woldSummandInt V i
  | none => f none
  | some k => if _h : 0 ≤ k then f (some k.toNat) else 0

/-- Padding does not change the unitary coordinate. -/
theorem woldPadFun_none (V : H →ₗᵢ[ℂ] H) (f : ∀ i, woldSummandNat V i) :
    woldPadFun V f none = f none :=
  rfl

/-- Padding reads a nonnegative time at its integer index. -/
theorem woldPadFun_nat (V : H →ₗᵢ[ℂ] H) (f : ∀ i, woldSummandNat V i) (n : ℕ) :
    woldPadFun V f (some (n : ℤ)) = f (some n) := by
  simp [woldPadFun, Int.toNat_natCast]

/-- Padding vanishes at a negative time. -/
theorem woldPadFun_neg (V : H →ₗᵢ[ℂ] H) (f : ∀ i, woldSummandNat V i) {k : ℤ}
    (hk : k < 0) : woldPadFun V f (some k) = 0 := by
  simp [woldPadFun, not_le.mpr hk]

/-- Squared norms of a padded coefficient sequence remain summable. -/
theorem summable_norm_sq_woldPadFun (V : H →ₗᵢ[ℂ] H) (f : lp (woldSummandNat V) 2) :
    Summable fun i : Option ℤ => ‖woldPadFun V (f : ∀ i, woldSummandNat V i) i‖ ^ 2 := by
  let φ : Option ℤ → ℝ := fun i =>
    ‖woldPadFun V (f : ∀ i, woldSummandNat V i) i‖ ^ 2
  have hcomp : φ ∘ woldExtendIndex =
      fun j => ‖(f : ∀ i, woldSummandNat V i) j‖ ^ 2 := by
    funext j
    cases j with
    | none =>
      dsimp only [Function.comp_apply, woldExtendIndex, φ]
      rw [woldPadFun_none]
      rfl
    | some n =>
      dsimp only [Function.comp_apply, woldExtendIndex, φ]
      rw [woldPadFun_nat]
      rfl
  have hp : 0 < (2 : ENNReal).toReal := by
    rw [ENNReal.toReal_ofNat]
    norm_num
  have hsum : Summable fun j => ‖(f : ∀ i, woldSummandNat V i) j‖ ^ 2 := by
    have hmem := (memℓp_gen_iff (p := 2) hp).1 (lp.memℓp f)
    rw [ENNReal.toReal_ofNat] at hmem
    simpa [Real.rpow_natCast] using hmem
  have hzero : ∀ x ∉ Set.range woldExtendIndex, φ x = 0 := by
    intro x hx
    cases x with
    | none => exact (hx ⟨none, rfl⟩).elim
    | some k =>
      have hk : ¬ 0 ≤ k := by
        intro hk0
        exact hx ⟨some k.toNat, by simp [woldExtendIndex, Int.toNat_of_nonneg hk0]⟩
      simp [φ, woldPadFun, hk]
  rw [← hcomp] at hsum
  exact (woldExtendIndex_injective.summable_iff hzero).mp hsum

/-- The padded coefficient sequence, as an element of the bilateral `ℓ²` space. -/
def woldPad (V : H →ₗᵢ[ℂ] H) (f : lp (woldSummandNat V) 2) : lp (woldSummandInt V) 2 :=
  ⟨woldPadFun V f, memℓp_gen (by
    simp only [ENNReal.toReal_ofNat]
    exact (summable_congr fun i =>
      (Real.rpow_natCast ‖woldPadFun V (f : ∀ j, woldSummandNat V j) i‖ 2).symm).mp
        (summable_norm_sq_woldPadFun V f))⟩

/-- Evaluation of a padded sequence. -/
theorem woldPad_apply (V : H →ₗᵢ[ℂ] H) (f : lp (woldSummandNat V) 2) (i : Option ℤ) :
    woldPad V f i = woldPadFun V f i :=
  rfl

/-- Padding preserves addition. -/
theorem woldPad_add (V : H →ₗᵢ[ℂ] H) (f g : lp (woldSummandNat V) 2) :
    woldPad V (f + g) = woldPad V f + woldPad V g := by
  apply lp.ext
  funext i
  cases i with
  | none => simp [woldPad_apply, woldPadFun]
  | some k =>
    by_cases hk : 0 ≤ k
    · simp [woldPad_apply, woldPadFun, dite_eq_left hk]
    · simp [woldPad_apply, woldPadFun, dite_eq_right hk]

/-- Padding preserves scalar multiplication. -/
theorem woldPad_smul (V : H →ₗᵢ[ℂ] H) (c : ℂ) (f : lp (woldSummandNat V) 2) :
    woldPad V (c • f) = c • woldPad V f := by
  apply lp.ext
  funext i
  cases i with
  | none => simp [woldPad_apply, woldPadFun, lp.coeFn_smul, Pi.smul_apply]
  | some k =>
    by_cases hk : 0 ≤ k
    · simp [woldPad_apply, woldPadFun, dite_eq_left hk, lp.coeFn_smul, Pi.smul_apply]
    · simp [woldPad_apply, woldPadFun, dite_eq_right hk]

/-- Padding as a linear map. -/
def woldPadLinear (V : H →ₗᵢ[ℂ] H) :
    lp (woldSummandNat V) 2 →ₗ[ℂ] lp (woldSummandInt V) 2 where
  toFun := woldPad V
  map_add' := woldPad_add V
  map_smul' := woldPad_smul V

/-- Padding preserves the `ℓ²` norm. -/
theorem norm_woldPad (V : H →ₗᵢ[ℂ] H) (f : lp (woldSummandNat V) 2) :
    ‖woldPad V f‖ = ‖f‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
  rw [woldLp_norm_sq_eq_tsum (woldPad V f), woldLp_norm_sq_eq_tsum f]
  let φ : Option ℤ → ℝ := fun i => ‖woldPadFun V (f : ∀ i, woldSummandNat V i) i‖ ^ 2
  have hcomp : (fun j => φ (woldExtendIndex j)) =
      fun j => ‖(f : ∀ i, woldSummandNat V i) j‖ ^ 2 := by
    funext j
    cases j with
    | none =>
      dsimp only [woldExtendIndex, φ]
      rw [woldPadFun_none]
    | some n =>
      dsimp only [woldExtendIndex, φ]
      rw [woldPadFun_nat]
  have hzero : ∀ x ∉ Set.range woldExtendIndex, φ x = 0 := by
    intro x hx
    cases x with
    | none => exact (hx ⟨none, rfl⟩).elim
    | some k =>
      have hk : ¬ 0 ≤ k := by
        intro hk0
        exact hx ⟨some k.toNat, by simp [woldExtendIndex, Int.toNat_of_nonneg hk0]⟩
      simp [φ, woldPadFun, hk]
  have hφ : Summable φ := by
    simpa [φ, woldPad_apply] using summable_norm_sq_woldPadFun V f
  have hsum : Summable fun j => φ (woldExtendIndex j) :=
    (woldExtendIndex_injective.summable_iff hzero).mpr hφ
  have hsφ : HasSum φ (∑' j, φ (woldExtendIndex j)) :=
    (woldExtendIndex_injective.hasSum_iff hzero).mp hsum.hasSum
  have hfun : (fun j => ‖(f : ∀ i, woldSummandNat V i) j‖ ^ 2) =
      fun j => φ (woldExtendIndex j) := hcomp.symm
  have htsum : ∑' i, ‖(woldPad V f : ∀ i, woldSummandInt V i) i‖ ^ 2 =
      ∑' j, ‖(f : ∀ i, woldSummandNat V i) j‖ ^ 2 := by
    rw [hfun, ← hsφ.tsum_eq]
    exact tsum_congr fun i => by simp [φ, woldPad_apply]
  exact htsum

/-- Padding as a linear isometry into the bilateral `ℓ²` space. -/
def woldPadIsometry (V : H →ₗᵢ[ℂ] H) :
    lp (woldSummandNat V) 2 →ₗᵢ[ℂ] lp (woldSummandInt V) 2 where
  toLinearMap := woldPadLinear V
  norm_map' f := by
    simpa [woldPadLinear] using norm_woldPad V f

/-- The source index of a bilaterally shifted coordinate. -/
def woldSlotSource : Option ℤ ≃ Option ℤ where
  toFun
    | none => none
    | some k => some (k - 1)
  invFun
    | none => none
    | some k => some (k + 1)
  left_inv i := by
    cases i with
    | none => rfl
    | some k => simp
  right_inv i := by
    cases i with
    | none => rfl
    | some k => simp

/-- The unitary slot is fixed by the source reindexing. -/
@[simp] theorem woldSlotSource_none : woldSlotSource none = none := rfl

/-- A wandering slot is read from the preceding time. -/
@[simp] theorem woldSlotSource_some (k : ℤ) : woldSlotSource (some k) = some (k - 1) := rfl

/-- The inverse source map fixes the unitary slot. -/
@[simp] theorem woldSlotSource_symm_none : woldSlotSource.symm none = none := rfl

/-- The inverse source map reads the following time. -/
@[simp] theorem woldSlotSource_symm_some (k : ℤ) :
    woldSlotSource.symm (some k) = some (k + 1) := rfl

/-- Move wandering mass one step toward positive time, and apply the unitary on its part. -/
def woldBilateralFun (V : H →ₗᵢ[ℂ] H) (f : ∀ i, woldSummandInt V i) :
    ∀ i, woldSummandInt V i
  | none => woldUnitaryEquiv V (f none)
  | some k => f (some (k - 1))

/-- The inverse bilateral step. -/
def woldBilateralInvFun (V : H →ₗᵢ[ℂ] H) (f : ∀ i, woldSummandInt V i) :
    ∀ i, woldSummandInt V i
  | none => (woldUnitaryEquiv V).symm (f none)
  | some k => f (some (k + 1))

/-- A bilateral step preserves squared coordinate norms up to reindexing. -/
theorem norm_sq_woldBilateralFun (V : H →ₗᵢ[ℂ] H) (f : ∀ i, woldSummandInt V i)
    (i : Option ℤ) :
    ‖woldBilateralFun V f i‖ ^ 2 = ‖f (woldSlotSource i)‖ ^ 2 := by
  cases i with
  | none =>
    rw [woldBilateralFun, woldSlotSource]
    exact congrArg (fun t : ℝ => t ^ 2) ((woldUnitaryEquiv V).norm_map (f none))
  | some k =>
    rw [woldBilateralFun, woldSlotSource_some]

/-- Squared norms stay summable under a bilateral step. -/
theorem summable_norm_sq_woldBilateralFun (V : H →ₗᵢ[ℂ] H) (f : lp (woldSummandInt V) 2) :
    Summable fun i => ‖woldBilateralFun V (f : ∀ i, woldSummandInt V i) i‖ ^ 2 := by
  have hp : 0 < (2 : ENNReal).toReal := by
    rw [ENNReal.toReal_ofNat]
    norm_num
  have hsum : Summable fun i => ‖(f : ∀ i, woldSummandInt V i) i‖ ^ 2 := by
    have hmem := (memℓp_gen_iff (p := 2) hp).1 (lp.memℓp f)
    rw [ENNReal.toReal_ofNat] at hmem
    simpa [Real.rpow_natCast] using hmem
  have hre : Summable fun i =>
      ‖(f : ∀ i, woldSummandInt V i) (woldSlotSource i)‖ ^ 2 :=
    (woldSlotSource.summable_iff
      (f := fun i => ‖(f : ∀ i, woldSummandInt V i) i‖ ^ 2)).mpr hsum
  exact (summable_congr fun i => (norm_sq_woldBilateralFun V (f : _) i).symm).mp hre

/-- One bilateral step, as an `ℓ²` vector. -/
def woldBilateral (V : H →ₗᵢ[ℂ] H) (f : lp (woldSummandInt V) 2) :
    lp (woldSummandInt V) 2 :=
  ⟨woldBilateralFun V f, memℓp_gen (by
    simp only [ENNReal.toReal_ofNat]
    exact (summable_congr fun i =>
      (Real.rpow_natCast ‖woldBilateralFun V (f : ∀ j, woldSummandInt V j) i‖ 2).symm).mp
        (summable_norm_sq_woldBilateralFun V f))⟩

/-- Evaluation of one bilateral step. -/
theorem woldBilateral_apply (V : H →ₗᵢ[ℂ] H) (f : lp (woldSummandInt V) 2) (i : Option ℤ) :
    woldBilateral V f i = woldBilateralFun V f i :=
  rfl

/-- A bilateral step preserves addition. -/
theorem woldBilateral_add (V : H →ₗᵢ[ℂ] H) (f g : lp (woldSummandInt V) 2) :
    woldBilateral V (f + g) = woldBilateral V f + woldBilateral V g := by
  apply lp.ext
  funext i
  cases i with
  | none => simp [woldBilateral_apply, woldBilateralFun, map_add]
  | some k => simp [woldBilateral_apply, woldBilateralFun]

/-- A bilateral step preserves scalar multiplication. -/
theorem woldBilateral_smul (V : H →ₗᵢ[ℂ] H) (c : ℂ) (f : lp (woldSummandInt V) 2) :
    woldBilateral V (c • f) = c • woldBilateral V f := by
  apply lp.ext
  funext i
  cases i with
  | none => simp [woldBilateral_apply, woldBilateralFun, lp.coeFn_smul, map_smul]
  | some k => simp [woldBilateral_apply, woldBilateralFun, lp.coeFn_smul]

/-- A bilateral step as a linear map. -/
def woldBilateralLinear (V : H →ₗᵢ[ℂ] H) :
    lp (woldSummandInt V) 2 →ₗ[ℂ] lp (woldSummandInt V) 2 where
  toFun := woldBilateral V
  map_add' := woldBilateral_add V
  map_smul' := woldBilateral_smul V

/-- A bilateral step preserves the `ℓ²` norm. -/
theorem norm_woldBilateral (V : H →ₗᵢ[ℂ] H) (f : lp (woldSummandInt V) 2) :
    ‖woldBilateral V f‖ = ‖f‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
  rw [woldLp_norm_sq_eq_tsum (woldBilateral V f), woldLp_norm_sq_eq_tsum f]
  have hsum : Summable fun i => ‖(f : ∀ i, woldSummandInt V i) i‖ ^ 2 := by
    have hp : 0 < (2 : ENNReal).toReal := by
      rw [ENNReal.toReal_ofNat]
      norm_num
    have hmem := (memℓp_gen_iff (p := 2) hp).1 (lp.memℓp f)
    rw [ENNReal.toReal_ofNat] at hmem
    simpa [Real.rpow_natCast] using hmem
  have hs' : HasSum (fun i => ‖(f : ∀ i, woldSummandInt V i) (woldSlotSource i)‖ ^ 2)
      (∑' i, ‖(f : ∀ i, woldSummandInt V i) i‖ ^ 2) :=
    (woldSlotSource.hasSum_iff
      (f := fun i => ‖(f : ∀ i, woldSummandInt V i) i‖ ^ 2)).mpr hsum.hasSum
  have hshift := hs'.tsum_eq
  have hpt : ∀ i, ‖(woldBilateral V f : ∀ i, woldSummandInt V i) i‖ ^ 2 =
      ‖(f : ∀ i, woldSummandInt V i) (woldSlotSource i)‖ ^ 2 := by
    intro i
    rw [woldBilateral_apply]
    exact norm_sq_woldBilateralFun V (f : ∀ i, woldSummandInt V i) i
  exact (tsum_congr hpt).trans hshift

/-- A bilateral step as a linear isometry. -/
def woldBilateralIsometry (V : H →ₗᵢ[ℂ] H) :
    lp (woldSummandInt V) 2 →ₗᵢ[ℂ] lp (woldSummandInt V) 2 where
  toLinearMap := woldBilateralLinear V
  norm_map' f := by
    simpa [woldBilateralLinear] using norm_woldBilateral V f

/-- The inverse bilateral step, as an `ℓ²` vector. -/
def woldBilateralInv (V : H →ₗᵢ[ℂ] H) (f : lp (woldSummandInt V) 2) :
    lp (woldSummandInt V) 2 :=
  ⟨woldBilateralInvFun V f, memℓp_gen (by
    have hsum : Summable fun i => ‖woldBilateralInvFun V (f : ∀ i, _) i‖ ^ 2 := by
      have hp : 0 < (2 : ENNReal).toReal := by
        rw [ENNReal.toReal_ofNat]
        norm_num
      have hmem := (memℓp_gen_iff (p := 2) hp).1 (lp.memℓp f)
      rw [ENNReal.toReal_ofNat] at hmem
      have hbase : Summable fun i => ‖(f : ∀ i, woldSummandInt V i) i‖ ^ 2 := by
        simpa [Real.rpow_natCast] using hmem
      have hre : Summable fun i =>
          ‖(f : ∀ i, woldSummandInt V i) (woldSlotSource.symm i)‖ ^ 2 :=
        (woldSlotSource.symm.summable_iff
          (f := fun i => ‖(f : ∀ i, woldSummandInt V i) i‖ ^ 2)).mpr hbase
      have hnorm : ∀ i, ‖woldBilateralInvFun V (f : ∀ i, _) i‖ ^ 2 =
          ‖(f : ∀ i, woldSummandInt V i) (woldSlotSource.symm i)‖ ^ 2 := by
        intro i
        cases i with
        | none =>
          simp only [woldBilateralInvFun, woldSlotSource_symm_none]
          exact congrArg (fun t : ℝ => t ^ 2)
            ((woldUnitaryEquiv V).symm.norm_map ((f : _) none))
        | some k =>
          rw [woldBilateralInvFun, woldSlotSource_symm_some]
      exact (summable_congr hnorm).mpr hre
    simp only [ENNReal.toReal_ofNat]
    exact (summable_congr fun i =>
      (Real.rpow_natCast ‖woldBilateralInvFun V (f : ∀ j, woldSummandInt V j) i‖ 2).symm).mp
        hsum)⟩

/-- The inverse step undoes a bilateral step. -/
theorem woldBilateralInv_woldBilateral (V : H →ₗᵢ[ℂ] H) (f : lp (woldSummandInt V) 2) :
    woldBilateralInv V (woldBilateral V f) = f := by
  apply lp.ext
  funext i
  cases i with
  | none =>
    simp [woldBilateralInv, woldBilateral_apply, woldBilateralInvFun, woldBilateralFun,
      LinearIsometryEquiv.symm_apply_apply]
  | some k =>
    simp only [woldBilateralInv, woldBilateral_apply, woldBilateralInvFun, woldBilateralFun]
    rw [add_sub_cancel_right]

/-- A bilateral step undoes the inverse step. -/
theorem woldBilateral_woldBilateralInv (V : H →ₗᵢ[ℂ] H) (f : lp (woldSummandInt V) 2) :
    woldBilateral V (woldBilateralInv V f) = f := by
  apply lp.ext
  funext i
  cases i with
  | none =>
    simp [woldBilateralInv, woldBilateral_apply, woldBilateralInvFun, woldBilateralFun,
      LinearIsometryEquiv.apply_symm_apply]
  | some k =>
    simp only [woldBilateralInv, woldBilateral_apply, woldBilateralInvFun, woldBilateralFun]
    rw [sub_add_cancel]

/-- The inverse step as a linear map. -/
def woldBilateralInvLinear (V : H →ₗᵢ[ℂ] H) :
    lp (woldSummandInt V) 2 →ₗ[ℂ] lp (woldSummandInt V) 2 where
  toFun := woldBilateralInv V
  map_add' f g := by
    apply lp.ext
    funext i
    have hpt (j : Option ℤ) :
        ((f + g : lp (woldSummandInt V) 2) : ∀ t, woldSummandInt V t) j =
          (f : ∀ t, woldSummandInt V t) j + (g : ∀ t, woldSummandInt V t) j :=
      (congrFun (lp.coeFn_add f g) j).trans (Pi.add_apply (⇑f) (⇑g) j)
    have hsum : ((woldBilateralInv V f + woldBilateralInv V g) : _) i =
        woldBilateralInvFun V (⇑f) i + woldBilateralInvFun V (⇑g) i :=
      (congrFun (lp.coeFn_add (woldBilateralInv V f) (woldBilateralInv V g)) i).trans
        (Pi.add_apply _ _ i)
    rw [show ((woldBilateralInv V (f + g)) : _) i =
      woldBilateralInvFun V (⇑(f + g)) i from rfl, hsum]
    cases i with
    | none =>
      rw [woldBilateralInvFun, woldBilateralInvFun, woldBilateralInvFun, hpt none, map_add]
    | some k =>
      rw [woldBilateralInvFun, woldBilateralInvFun, woldBilateralInvFun]
      exact hpt (some (k + 1))
  map_smul' c f := by
    apply lp.ext
    funext i
    have hpt (j : Option ℤ) :
        ((c • f : lp (woldSummandInt V) 2) : ∀ t, woldSummandInt V t) j =
          c • (f : ∀ t, woldSummandInt V t) j :=
      (congrFun (lp.coeFn_smul c f) j).trans (Pi.smul_apply c (⇑f) j)
    have hsum : ((c • woldBilateralInv V f) : _) i =
        c • woldBilateralInvFun V (⇑f) i :=
      (congrFun (lp.coeFn_smul c (woldBilateralInv V f)) i).trans (Pi.smul_apply c _ i)
    have hgoal : woldBilateralInvFun V (⇑(c • f)) i =
        c • woldBilateralInvFun V (⇑f) i := by
      cases i with
      | none =>
        rw [woldBilateralInvFun, woldBilateralInvFun, hpt none, map_smul]
      | some k =>
        rw [woldBilateralInvFun, woldBilateralInvFun]
        exact hpt (some (k + 1))
    exact hgoal.trans hsum.symm

/-- The two bilateral steps are mutual inverses on the nose. -/
theorem woldBilateralLinear_comp_inv (V : H →ₗᵢ[ℂ] H) :
    (woldBilateralLinear V).comp (woldBilateralInvLinear V) = LinearMap.id := by
  apply LinearMap.ext
  intro f
  simp only [LinearMap.comp_apply, LinearMap.id_apply, woldBilateralLinear,
    woldBilateralInvLinear]
  exact woldBilateral_woldBilateralInv V f

/-- The two bilateral steps are mutual inverses on the nose, in the other order. -/
theorem woldBilateralInvLinear_comp (V : H →ₗᵢ[ℂ] H) :
    (woldBilateralInvLinear V).comp (woldBilateralLinear V) = LinearMap.id := by
  apply LinearMap.ext
  intro f
  simp only [LinearMap.comp_apply, LinearMap.id_apply, woldBilateralLinear,
    woldBilateralInvLinear]
  exact woldBilateralInv_woldBilateral V f

/-- The bilateral shift is unitary on the extended coefficient space. -/
def woldBilateralEquiv (V : H →ₗᵢ[ℂ] H) :
    lp (woldSummandInt V) 2 ≃ₗᵢ[ℂ] lp (woldSummandInt V) 2 :=
  LinearIsometryEquiv.ofLinearIsometry (woldBilateralIsometry V) (woldBilateralInvLinear V)
    (woldBilateralLinear_comp_inv V) (woldBilateralInvLinear_comp V)

/-- Evaluation of the bilateral unitary. -/
theorem woldBilateralEquiv_apply (V : H →ₗᵢ[ℂ] H) (f : lp (woldSummandInt V) 2) :
    woldBilateralEquiv V f = woldBilateral V f :=
  rfl

/-- The original space, sent to nonnegative Wold coordinates and then padded. -/
def woldExtensionIncl (V : H →ₗᵢ[ℂ] H) : H →ₗᵢ[ℂ] lp (woldSummandInt V) 2 :=
  (woldPadIsometry V).comp (wold_isHilbertSum V).linearIsometryEquiv.toLinearIsometry

/-- The extension of an isometry intertwines it with the bilateral unitary. -/
theorem woldExtension_intertwining (V : H →ₗᵢ[ℂ] H) (x : H) :
    woldBilateralEquiv V (woldExtensionIncl V x) = woldExtensionIncl V (V x) := by
  apply lp.ext
  funext i
  have hpad : ∀ (y : H) (j : Option ℤ), woldExtensionIncl V y j =
      woldPadFun V ((wold_isHilbertSum V).linearIsometryEquiv y) j := by
    intro y j
    simp [woldExtensionIncl, woldPadIsometry, woldPadLinear, woldPad_apply,
      LinearIsometry.coe_comp, LinearIsometryEquiv.coe_toLinearIsometry, Function.comp_apply]
  have hU : woldBilateralEquiv V (woldExtensionIncl V x) i =
      woldBilateralFun V (woldPadFun V ((wold_isHilbertSum V).linearIsometryEquiv x)) i := by
    rw [woldBilateralEquiv_apply, woldBilateral_apply]
    exact congrFun (congrArg (woldBilateralFun V) (funext (hpad x))) i
  rw [hU, hpad (V x)]
  cases i with
  | none =>
    simp [woldBilateralFun, woldPadFun, wold_coord_unitary]
  | some k =>
    rw [woldBilateralFun]
    by_cases hk : 0 ≤ k
    · have hkNat : (k.toNat : ℤ) = k := Int.toNat_of_nonneg hk
      cases hnat : k.toNat with
      | zero =>
        have hk0 : k = 0 := by
          rw [← hkNat]
          simp [hnat]
        subst hk0
        have hneg : (0 : ℤ) - 1 < 0 := by decide
        rw [woldPadFun_neg V _ hneg]
        exact ((wold_coord_zero V x).symm).trans
          (woldPadFun_nat V ((wold_isHilbertSum V).linearIsometryEquiv (V x)) 0).symm
      | succ n =>
        have hpred : k - 1 = (n : ℤ) := by
          rw [← hkNat, hnat, Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
        have hidx : k = ((n + 1 : ℕ) : ℤ) := by
          rw [← hkNat, hnat]
        rw [hpred, woldPadFun_nat, hidx, woldPadFun_nat]
        exact (wold_coord_succ V x n).symm
    · have hklt : k < 0 := lt_of_not_ge hk
      have hkpred : k - 1 < 0 := by linarith
      rw [woldPadFun_neg V _ hkpred, woldPadFun_neg V _ hklt]

/-- Nonnegative powers of the extension still intertwine the isometry. -/
theorem woldExtension_pow (V : H →ₗᵢ[ℂ] H) (n : ℕ) (x : H) :
    (woldBilateralEquiv V ^ n) (woldExtensionIncl V x) =
      woldExtensionIncl V ((V ^ n) x) := by
  induction n with
  | zero => simp [pow_zero]
  | succ n ih =>
    rw [pow_succ', pow_succ', LinearIsometryEquiv.coe_mul, Function.comp_apply, ih]
    rw [LinearIsometry.mul_def, LinearIsometry.coe_comp, Function.comp_apply]
    exact woldExtension_intertwining V ((V ^ n) x)

/-- The Hilbert-sum coordinate of an included summand is the corresponding basis vector. -/
theorem wold_coord_incl (V : H →ₗᵢ[ℂ] H) (i : Option ℕ) (a : woldSummandNat V i) :
    (wold_isHilbertSum V).linearIsometryEquiv (woldSummandIncl V i a) = lp.single 2 i a := by
  rw [← (wold_isHilbertSum V).linearIsometryEquiv_symm_apply_single (i := i) a]
  exact (wold_isHilbertSum V).linearIsometryEquiv.apply_symm_apply (lp.single 2 i a)

/-- Padding of a unitary basis function, before passing to `ℓ²`. -/
theorem woldPadFun_single_none (V : H →ₗᵢ[ℂ] H) (a : woldUnitarySubspace V) (j : Option ℤ) :
    woldPadFun V (Pi.single none a) j = Pi.single none a j := by
  cases j with
  | none =>
    rw [woldPadFun_none, Pi.single_eq_same, Pi.single_eq_same]
  | some k =>
    have hne : some k ≠ (none : Option ℤ) := by
      intro h
      cases h
    by_cases hk : 0 ≤ k
    · have hneN : some k.toNat ≠ (none : Option ℕ) := by
        intro h
        cases h
      have hpad : woldPadFun V (Pi.single (M := woldSummandNat V) none a) (some k) =
          (Pi.single (M := woldSummandNat V) none a (some k.toNat) :
            woldWanderingSubspace V) := by
        simp [woldPadFun, dite_eq_left hk]
      rw [hpad, Pi.single_eq_of_ne hneN, Pi.single_eq_of_ne hne]
    · rw [woldPadFun_neg V _ (lt_of_not_ge hk), Pi.single_eq_of_ne hne]

/-- Padding fixes a unitary basis vector. -/
theorem woldPad_single_none (V : H →ₗᵢ[ℂ] H) (a : woldUnitarySubspace V) :
    woldPad V (lp.single 2 none a) = lp.single 2 none a := by
  apply lp.ext
  funext j
  have hfun : (⇑(lp.single (E := woldSummandNat V) 2 none a) : ∀ i, woldSummandNat V i) =
      Pi.single (M := woldSummandNat V) none a :=
    lp.coeFn_single (E := woldSummandNat V) 2 none a
  have hint : (⇑(lp.single (E := woldSummandInt V) 2 none a) : ∀ i, woldSummandInt V i) =
      Pi.single (M := woldSummandInt V) none a :=
    lp.coeFn_single (E := woldSummandInt V) 2 none a
  exact (woldPad_apply V _ j).trans ((congrArg (fun f => woldPadFun V f j) hfun).trans
    ((woldPadFun_single_none V a j).trans (congrFun hint j).symm))

/-- Padding of a wandering basis function, before passing to `ℓ²`. -/
theorem woldPadFun_single_some (V : H →ₗᵢ[ℂ] H) (n : ℕ) (a : woldWanderingSubspace V)
    (j : Option ℤ) :
    woldPadFun V (Pi.single (some n) a) j = Pi.single (some (n : ℤ)) a j := by
  cases j with
  | none =>
    rw [woldPadFun_none, Pi.single_eq_of_ne (show none ≠ some n by intro h; cases h),
      Pi.single_eq_of_ne (show (none : Option ℤ) ≠ some (n : ℤ) by intro h; cases h)]
  | some k =>
    by_cases hk : 0 ≤ k
    · by_cases hkn : k = (n : ℤ)
      · obtain rfl := hkn
        have hpad : woldPadFun V (Pi.single (M := woldSummandNat V) (some n) a)
            (some (n : ℤ)) =
            (Pi.single (M := woldSummandNat V) (some n) a (some n) :
              woldWanderingSubspace V) := by
          simp [woldPadFun, Int.toNat_natCast]
        rw [hpad, Pi.single_eq_same, Pi.single_eq_same]
      · have hto : k.toNat ≠ n := by
          intro hto
          apply hkn
          rw [← Int.toNat_of_nonneg hk, hto]
        have hneL : some k.toNat ≠ some n := by
          intro h
          apply hto
          cases h
          rfl
        have hneR : some k ≠ some (n : ℤ) := by
          intro h
          apply hkn
          cases h
          rfl
        have hpad : woldPadFun V (Pi.single (M := woldSummandNat V) (some n) a) (some k) =
            (Pi.single (M := woldSummandNat V) (some n) a (some k.toNat) :
              woldWanderingSubspace V) := by
          simp [woldPadFun, dite_eq_left hk]
        rw [hpad, Pi.single_eq_of_ne hneL, Pi.single_eq_of_ne hneR]
    · have hne : some k ≠ some (n : ℤ) := by
        intro h
        apply hk
        cases h
        exact Int.natCast_nonneg n
      rw [woldPadFun_neg V _ (lt_of_not_ge hk), Pi.single_eq_of_ne hne]

/-- Padding keeps a wandering basis vector at the same integer time. -/
theorem woldPad_single_some (V : H →ₗᵢ[ℂ] H) (n : ℕ) (a : woldWanderingSubspace V) :
    woldPad V (lp.single 2 (some n) a) = lp.single 2 (some (n : ℤ)) a := by
  apply lp.ext
  funext j
  have hnat : (⇑(lp.single (E := woldSummandNat V) 2 (some n) a) :
      ∀ i, woldSummandNat V i) = Pi.single (M := woldSummandNat V) (some n) a :=
    lp.coeFn_single (E := woldSummandNat V) 2 (some n) a
  have hint : (⇑(lp.single (E := woldSummandInt V) 2 (some (n : ℤ)) a) :
      ∀ i, woldSummandInt V i) = Pi.single (M := woldSummandInt V) (some (n : ℤ)) a :=
    lp.coeFn_single (E := woldSummandInt V) 2 (some (n : ℤ)) a
  exact (woldPad_apply V _ j).trans ((congrArg (fun f => woldPadFun V f j) hnat).trans
    ((woldPadFun_single_some V n a j).trans (congrFun hint j).symm))

/-- A time-zero wandering vector is included as itself. -/
theorem woldSummandIncl_zero (V : H →ₗᵢ[ℂ] H) (a : woldWanderingSubspace V) :
    woldSummandIncl V (some 0) a = (a : H) := by
  rw [woldSummandIncl_some, woldShift_apply, pow_zero, one_apply_eq_self]

/-- The extension inclusion, before the padding step. -/
theorem woldExtensionIncl_apply (V : H →ₗᵢ[ℂ] H) (x : H) :
    woldExtensionIncl V x =
      woldPad V ((wold_isHilbertSum V).linearIsometryEquiv x) := by
  simp [woldExtensionIncl, woldPadIsometry, woldPadLinear, LinearIsometry.coe_comp,
    LinearIsometryEquiv.coe_toLinearIsometry, Function.comp_apply]

/-- The extension inclusion sends a wandering vector to the time-zero basis vector. -/
theorem woldExtensionIncl_wandering (V : H →ₗᵢ[ℂ] H) (a : woldWanderingSubspace V) :
    woldExtensionIncl V (a : H) = lp.single 2 (some 0) a := by
  rw [woldExtensionIncl_apply, ← woldSummandIncl_zero V a, wold_coord_incl,
    woldPad_single_some]
  rfl

/-- The extension inclusion sends a unitary vector to the unitary basis vector. -/
theorem woldExtensionIncl_unitary (V : H →ₗᵢ[ℂ] H) (u : woldUnitarySubspace V) :
    woldExtensionIncl V (u : H) = lp.single 2 none u := by
  rw [woldExtensionIncl_apply, ← woldSummandIncl_none V u, wold_coord_incl,
    woldPad_single_none]

/-- One bilateral step on a wandering basis function, before passing to `ℓ²`. -/
theorem woldBilateralFun_single_some (V : H →ₗᵢ[ℂ] H) (k : ℤ) (a : woldWanderingSubspace V)
    (i : Option ℤ) :
    woldBilateralFun V (Pi.single (some k) a) i = Pi.single (some (k + 1)) a i := by
  cases i with
  | none =>
    rw [woldBilateralFun, Pi.single_eq_of_ne (by intro h; cases h), map_zero,
      Pi.single_eq_of_ne (by intro h; cases h)]
  | some j =>
    rw [woldBilateralFun]
    by_cases hj : j = k + 1
    · have hpred : j - 1 = k := by
        rw [hj, add_sub_cancel_right]
      rw [hpred, hj, Pi.single_eq_same, Pi.single_eq_same]
    · have hpred : some (j - 1) ≠ some k := by
        intro h
        apply hj
        cases h
        exact (sub_add_cancel j 1).symm
      have hne : some j ≠ some (k + 1) := by
        intro h
        apply hj
        cases h
        rfl
      rw [Pi.single_eq_of_ne hpred, Pi.single_eq_of_ne hne]

/-- One bilateral step shifts a wandering basis vector one time forward. -/
theorem woldBilateral_single_some (V : H →ₗᵢ[ℂ] H) (k : ℤ) (a : woldWanderingSubspace V) :
    woldBilateralEquiv V (lp.single 2 (some k) a) = lp.single 2 (some (k + 1)) a := by
  apply lp.ext
  funext i
  exact woldBilateralFun_single_some V k a i

/-- Nonnegative powers shift the time-zero wandering vector to time `n`. -/
theorem woldBilateral_pow_single (V : H →ₗᵢ[ℂ] H) (n : ℕ) (a : woldWanderingSubspace V) :
    (woldBilateralEquiv V ^ n) (lp.single 2 (some 0) a) = lp.single 2 (some (n : ℤ)) a := by
  induction n with
  | zero => simp [pow_zero]
  | succ n ih =>
    rw [pow_succ', LinearIsometryEquiv.coe_mul, Function.comp_apply, ih]
    have hshift := woldBilateral_single_some V (n : ℤ) a
    simpa [Nat.cast_add, Nat.cast_one] using hshift

/-- The inverse bilateral unitary, evaluated on `ℓ²`. -/
theorem woldBilateralEquiv_symm_apply (V : H →ₗᵢ[ℂ] H) (f : lp (woldSummandInt V) 2) :
    (woldBilateralEquiv V).symm f = woldBilateralInv V f := by
  simp [woldBilateralEquiv, woldBilateralInvLinear, LinearIsometryEquiv.coe_ofLinearIsometry_symm]

/-- The inverse step on a wandering basis function, before passing to `ℓ²`. -/
theorem woldBilateralInvFun_single_some (V : H →ₗᵢ[ℂ] H) (k : ℤ)
    (a : woldWanderingSubspace V) (i : Option ℤ) :
    woldBilateralInvFun V (Pi.single (some k) a) i = Pi.single (some (k - 1)) a i := by
  cases i with
  | none =>
    rw [woldBilateralInvFun, Pi.single_eq_of_ne (by intro h; cases h), map_zero,
      Pi.single_eq_of_ne (by intro h; cases h)]
  | some j =>
    rw [woldBilateralInvFun]
    by_cases hj : j + 1 = k
    · have hj' : j = k - 1 := by
        rw [← hj, add_sub_cancel_right]
      rw [hj, hj', Pi.single_eq_same, Pi.single_eq_same]
    · have hsrc : some (j + 1) ≠ some k := by
        intro h
        apply hj
        cases h
        rfl
      have hne : some j ≠ some (k - 1) := by
        intro h
        apply hj
        cases h
        rw [sub_add_cancel]
      rw [Pi.single_eq_of_ne hsrc, Pi.single_eq_of_ne hne]

/-- The inverse step shifts a wandering basis vector one time backward. -/
theorem woldBilateralInv_single_some (V : H →ₗᵢ[ℂ] H) (k : ℤ) (a : woldWanderingSubspace V) :
    woldBilateralInv V (lp.single 2 (some k) a) = lp.single 2 (some (k - 1)) a := by
  apply lp.ext
  funext i
  exact woldBilateralInvFun_single_some V k a i

/-- Negative powers shift the time-zero wandering vector to time `-n`. -/
theorem woldBilateral_inv_pow_single (V : H →ₗᵢ[ℂ] H) (n : ℕ) (a : woldWanderingSubspace V) :
    ((woldBilateralEquiv V).symm ^ n) (lp.single 2 (some 0) a) =
      lp.single 2 (some (-n : ℤ)) a := by
  induction n with
  | zero => simp [pow_zero]
  | succ n ih =>
    rw [pow_succ', LinearIsometryEquiv.coe_mul, Function.comp_apply, ih]
    rw [woldBilateralEquiv_symm_apply, woldBilateralInv_single_some]
    congr 1
    rw [Nat.cast_add, Nat.cast_one, neg_add, sub_eq_add_neg]

/-- Every bilateral basis vector lies on the two-sided orbit of an included Wold vector. -/
theorem wold_single_mem_orbit (V : H →ₗᵢ[ℂ] H) (i : Option ℤ) (a : woldSummandInt V i) :
    ∃ k : ℤ, ∃ x : H, lp.single 2 i a =
      (woldBilateralEquiv V ^ k) (woldExtensionIncl V x) := by
  cases i with
  | none =>
    refine ⟨0, (a : H), ?_⟩
    simp [woldExtensionIncl_unitary]
  | some k =>
    cases k with
    | ofNat n =>
      refine ⟨(n : ℤ), (a : H), ?_⟩
      rw [zpow_natCast, woldExtensionIncl_wandering]
      exact (woldBilateral_pow_single V n a).symm
    | negSucc n =>
      refine ⟨-((n + 1 : ℕ) : ℤ), (a : H), ?_⟩
      rw [zpow_neg, zpow_natCast, ← inv_pow, woldExtensionIncl_wandering]
      have hneg : (Int.negSucc n : ℤ) = -((n + 1 : ℕ) : ℤ) := rfl
      rw [hneg]
      exact (woldBilateral_inv_pow_single V (n + 1) a).symm

/-- The closed span of the two-sided orbit is the bilateral coefficient space. -/
theorem woldExtension_minimal (V : H →ₗᵢ[ℂ] H) :
    (span ℂ {y : lp (woldSummandInt V) 2 | ∃ k : ℤ, ∃ x : H,
      y = (woldBilateralEquiv V ^ k) (woldExtensionIncl V x)}).topologicalClosure = ⊤ := by
  let S : Set (lp (woldSummandInt V) 2) :=
    {y | ∃ k : ℤ, ∃ x : H, y = (woldBilateralEquiv V ^ k) (woldExtensionIncl V x)}
  rw [eq_top_iff]
  intro f _
  have hs := lp.hasSum_single (E := woldSummandInt V) ENNReal.ofNat_ne_top f
  refine mem_closure_of_tendsto hs (Filter.Eventually.of_forall fun t => ?_)
  refine Submodule.sum_mem (span ℂ S) fun i _ => ?_
  obtain ⟨k, x, hk⟩ := wold_single_mem_orbit V i ((f : ∀ i, woldSummandInt V i) i)
  exact subset_span ⟨k, x, hk⟩

end CKMA
