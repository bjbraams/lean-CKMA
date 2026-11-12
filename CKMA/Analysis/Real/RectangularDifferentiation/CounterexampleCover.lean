/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.Real.RectangularDifferentiation.Counterexample
public import Mathlib.NumberTheory.Harmonic.Bounds

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

/-!
# Covering and spikes for the Saks counterexample

Translates of the strip union cover a definite fraction of the inner square. The
higher-dimensional set is the product of that plane set with a thin rectangle, and the
integrable function is the sum of the corresponding rectangular spikes.
-/

@[expose] public section

noncomputable section

open Classical MeasureTheory Set Filter Finset
open scoped ENNReal NNReal BigOperators

namespace CKMA.Bohr

/-- Points of the inner square whose reflected picture meets the strip union. -/
def shiftHit (k : ℕ) (v : Fin 2 → ℝ) : Set (Fin 2 → ℝ) :=
  {x | x - v ∈ badPlane k}

/-- A reflected strip is measurable. -/
lemma measurableSet_shiftHit (k : ℕ) (v : Fin 2 → ℝ) : MeasurableSet (shiftHit k v) := by
  have hsub : Measurable (fun x : Fin 2 → ℝ => x - v) := by fun_prop
  have heq : shiftHit k v = (fun x => x - v) ⁻¹' badPlane k := rfl
  rw [heq]
  exact hsub (measurableSet_badPlane k)

/-- Subtracting one removal ratio scales the finite measure by `1 - removalRatio`. -/
lemma volume_sub_removal (k : ℕ) {R : Set (Fin 2 → ℝ)} (hR : volume R < ∞) :
    volume R - ENNReal.ofReal (removalRatio k) * volume R =
      ENNReal.ofReal (1 - removalRatio k) * volume R := by
  have hr := removalRatio_mem_Ioo k
  have hreal : volume R = ENNReal.ofReal (volume.real R) := by
    rw [measureReal_def]
    exact (ENNReal.ofReal_toReal hR.ne).symm
  have hq : 0 ≤ removalRatio k * volume.real R :=
    mul_nonneg hr.1.le ENNReal.toReal_nonneg
  rw [hreal, ← ENNReal.ofReal_mul hr.1.le, ← ENNReal.ofReal_sub _ hq,
    ← ENNReal.ofReal_mul (sub_nonneg.mpr hr.2.le)]
  congr 1
  ring

/-- `n` translates leave at most the factor `(1 - removalRatio) ^ n` of `U` uncovered. -/
lemma exists_shiftPack (k : ℕ) {U : Set (Fin 2 → ℝ)} (hU : MeasurableSet U)
    (hUs : U ⊆ innerPlane k) (n : ℕ) :
    ∃ v : Fin n → Fin 2 → ℝ, (∀ i, v i ∈ domain k) ∧
      volume (U \ ⋃ i, shiftHit k (v i)) ≤
        ENNReal.ofReal ((1 - removalRatio k) ^ n) * volume U := by
  induction n with
  | zero =>
    refine ⟨Fin.elim0, fun i => i.elim0, ?_⟩
    simp [iUnion_of_empty, pow_zero, ENNReal.ofReal_one]
  | succ n ih =>
    obtain ⟨v, hv, hvol⟩ := ih
    let R : Set (Fin 2 → ℝ) := U \ ⋃ i, shiftHit k (v i)
    have hRunion : MeasurableSet (⋃ i, shiftHit k (v i)) :=
      MeasurableSet.iUnion fun i => measurableSet_shiftHit k (v i)
    have hR : MeasurableSet R := hU.diff hRunion
    have hRs : R ⊆ innerPlane k := fun x hx => hUs hx.1
    obtain ⟨w, hw, hheavy⟩ := exists_heavy_translate k hR hRs
    refine ⟨Fin.snoc v w, ?_, ?_⟩
    · intro i
      cases i using Fin.lastCases with
      | last => simpa [Fin.snoc_last] using hw
      | cast i => simpa [Fin.snoc_castSucc] using hv i
    · have hshift : shiftHit k w = {x | x - w ∈ badPlane k} := rfl
      have hRlt : volume R < ∞ :=
        lt_of_le_of_lt (measure_mono hRs) (volume_innerPlane_pos_lt_top k).2
      have hinter : R ∩ shiftHit k w ⊆ R := inter_subset_left
      have hfinI : volume (R ∩ shiftHit k w) ≠ ∞ :=
        ne_of_lt (lt_of_le_of_lt (measure_mono hinter) hRlt)
      have hset : R \ shiftHit k w = R \ (R ∩ shiftHit k w) := by
        ext x
        simp only [Set.mem_sdiff, mem_inter_iff]
        tauto
      have hdiff : volume (R \ shiftHit k w) =
          volume R - volume (R ∩ shiftHit k w) := by
        rw [hset]
        exact measure_sdiff hinter (hR.inter (measurableSet_shiftHit k w)).nullMeasurableSet hfinI
      let v' : Fin (n + 1) → Fin 2 → ℝ := Fin.snoc v w
      have hfun : (fun i => shiftHit k (v' i)) =
          (Fin.snoc (fun i => shiftHit k (v i)) (shiftHit k w) :
            Fin (n + 1) → Set (Fin 2 → ℝ)) := by
        funext i
        cases i using Fin.lastCases with
        | last => simp [v', Fin.snoc_last]
        | cast i => simp [v', Fin.snoc_castSucc]
      have hrest : U \ ⋃ i, shiftHit k (v' i) = R \ shiftHit k w := by
        ext x
        rw [hfun, iUnion_snoc]
        simp only [R, Set.mem_sdiff, mem_union, mem_iUnion]
        tauto
      rw [hrest, hdiff]
      have hle : volume R - volume (R ∩ shiftHit k w) ≤
          volume R - ENNReal.ofReal (removalRatio k) * volume R :=
        tsub_le_tsub_left (by simpa [hshift] using hheavy) _
      refine hle.trans ?_
      rw [volume_sub_removal k hRlt]
      have hbase : 0 ≤ 1 - removalRatio k := sub_nonneg.mpr (removalRatio_mem_Ioo k).2.le
      calc
        ENNReal.ofReal (1 - removalRatio k) * volume R
            ≤ ENNReal.ofReal (1 - removalRatio k) *
              (ENNReal.ofReal ((1 - removalRatio k) ^ n) * volume U) := by
          gcongr
        _ = ENNReal.ofReal ((1 - removalRatio k) ^ (n + 1)) * volume U := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hbase]
          congr 1
          apply congrArg ENNReal.ofReal
          exact (pow_succ' (1 - removalRatio k) n).symm

/-- Powers of the contraction are at most the exponential. -/
lemma removal_pow_le_exp (k n : ℕ) :
    (1 - removalRatio k) ^ n ≤ Real.exp (-((n : ℝ) * removalRatio k)) := by
  have hbase : 0 ≤ 1 - removalRatio k := sub_nonneg.mpr (removalRatio_mem_Ioo k).2.le
  calc
    (1 - removalRatio k) ^ n ≤ Real.exp (-removalRatio k) ^ n :=
      pow_le_pow_left₀ hbase (Real.one_sub_le_exp_neg _) n
    _ = Real.exp (-((n : ℝ) * removalRatio k)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

/-- `exp (-1)` is strictly smaller than one half. -/
lemma exp_neg_one_lt_half : Real.exp (-1) < (1 / 2 : ℝ) := by
  have h2 : (2 : ℝ) < Real.exp 1 := by
    linarith [Real.add_one_lt_exp (x := (1 : ℝ)) one_ne_zero]
  have hinv : (Real.exp 1)⁻¹ < (2 : ℝ)⁻¹ :=
    (inv_lt_inv₀ (Real.exp_pos _) (by norm_num)).mpr h2
  have hhalf : (2 : ℝ)⁻¹ = 1 / 2 := by norm_num
  rw [hhalf] at hinv
  rw [Real.exp_neg]
  exact hinv

/-- `copyCount` steps leave an uncovered factor at most `exp (-1)`. -/
lemma removal_copy_le_exp (k : ℕ) :
    (1 - removalRatio k) ^ copyCount k ≤ Real.exp (-1) :=
  (removal_pow_le_exp k (copyCount k)).trans <|
    Real.exp_le_exp.mpr (neg_le_neg (copyCount_ratio_ge_one k))

/-- Subtracting a factor in `[0, 1]` multiplies a finite area by the complement. -/
lemma volume_sub_scaled {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) {R : Set (Fin 2 → ℝ)}
    (hR : volume R < ∞) :
    volume R - ENNReal.ofReal c * volume R = ENNReal.ofReal (1 - c) * volume R := by
  have hreal : volume R = ENNReal.ofReal (volume.real R) := by
    rw [measureReal_def]
    exact (ENNReal.ofReal_toReal hR.ne).symm
  have hq : 0 ≤ c * volume.real R := mul_nonneg hc0 ENNReal.toReal_nonneg
  rw [hreal, ← ENNReal.ofReal_mul hc0, ← ENNReal.ofReal_sub _ hq,
    ← ENNReal.ofReal_mul (sub_nonneg.mpr hc1)]
  congr 1
  ring

/-- Translates whose uncovered inner area is at most `exp (-1)` times the inner area. -/
lemma exists_almost_cover (k : ℕ) :
    ∃ v : Fin (copyCount k) → Fin 2 → ℝ, (∀ i, v i ∈ domain k) ∧
      volume (innerPlane k \ ⋃ i, shiftHit k (v i)) ≤
        ENNReal.ofReal (Real.exp (-1)) * volume (innerPlane k) := by
  have hmeas : MeasurableSet (innerPlane k) := by
    rw [innerPlane, inner]
    exact (innerRect 2 k le_rfl).measurableSet_carrier
  obtain ⟨v, hv, hvol⟩ := exists_shiftPack k hmeas subset_rfl (copyCount k)
  refine ⟨v, hv, hvol.trans ?_⟩
  gcongr
  exact removal_copy_le_exp k

/-- The covered part of the inner square has area greater than `1 / 8`. -/
lemma volume_planeCover_gt (k : ℕ) (v : Fin (copyCount k) → Fin 2 → ℝ)
    (hvol : volume (innerPlane k \ ⋃ i, shiftHit k (v i)) ≤
      ENNReal.ofReal (Real.exp (-1)) * volume (innerPlane k)) :
    ENNReal.ofReal (1 / 8) < volume (innerPlane k ∩ ⋃ i, shiftHit k (v i)) := by
  have hmu : MeasurableSet (⋃ i, shiftHit k (v i)) :=
    MeasurableSet.iUnion fun i => measurableSet_shiftHit k (v i)
  have hadd := measure_inter_add_sdiff (μ := volume) (innerPlane k) hmu
  have hI : volume (innerPlane k) < ∞ := (volume_innerPlane_pos_lt_top k).2
  have hfin : volume (innerPlane k \ ⋃ i, shiftHit k (v i)) ≠ ∞ :=
    ne_of_lt (lt_of_le_of_lt (measure_mono Set.sdiff_subset) hI)
  have hhit : volume (innerPlane k ∩ ⋃ i, shiftHit k (v i)) =
      volume (innerPlane k) - volume (innerPlane k \ ⋃ i, shiftHit k (v i)) :=
    ENNReal.eq_sub_of_add_eq hfin hadd
  have hge : volume (innerPlane k) -
      ENNReal.ofReal (Real.exp (-1)) * volume (innerPlane k) ≤
        volume (innerPlane k ∩ ⋃ i, shiftHit k (v i)) := by
    rw [hhit]
    exact tsub_le_tsub_left hvol _
  have hc0 : 0 ≤ Real.exp (-1) := Real.exp_nonneg _
  have hc1 : Real.exp (-1) ≤ 1 := (exp_neg_one_lt_half).le.trans (by norm_num)
  rw [volume_sub_scaled hc0 hc1 hI] at hge
  have hreal : (1 / 4 : ℝ) < volume.real (innerPlane k) := by
    rw [volume_real_innerPlane]
    exact planeFactor_gt k
  have hvolEq : volume (innerPlane k) = ENNReal.ofReal (volume.real (innerPlane k)) := by
    rw [measureReal_def]
    exact (ENNReal.ofReal_toReal hI.ne).symm
  have hquart : ENNReal.ofReal (1 / 4) < volume (innerPlane k) := by
    rw [hvolEq]
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr hreal
  have hc : 0 < 1 - Real.exp (-1) := by linarith [exp_neg_one_lt_half]
  have hmul : ENNReal.ofReal (1 - Real.exp (-1)) * ENNReal.ofReal (1 / 4) <
      ENNReal.ofReal (1 - Real.exp (-1)) * volume (innerPlane k) :=
    ENNReal.mul_lt_mul_right (ENNReal.ofReal_pos.mpr hc).ne' ENNReal.ofReal_ne_top hquart
  have hprod : ENNReal.ofReal ((1 - Real.exp (-1)) / 4) =
      ENNReal.ofReal (1 - Real.exp (-1)) * ENNReal.ofReal (1 / 4) := by
    rw [← ENNReal.ofReal_mul hc.le]
    congr 1
    ring
  have hnum : (1 / 8 : ℝ) < (1 - Real.exp (-1)) / 4 := by
    have hhalf : (1 / 2 : ℝ) < 1 - Real.exp (-1) := by linarith [exp_neg_one_lt_half]
    calc
      (1 / 8 : ℝ) = (1 / 2) / 4 := by norm_num
      _ < (1 - Real.exp (-1)) / 4 :=
        div_lt_div_of_pos_right hhalf (by norm_num : (0 : ℝ) < 4)
  have hlt : ENNReal.ofReal (1 / 8) < ENNReal.ofReal ((1 - Real.exp (-1)) / 4) :=
    (ENNReal.ofReal_lt_ofReal_iff (div_pos hc (by norm_num))).mpr hnum
  have hmid : ENNReal.ofReal ((1 - Real.exp (-1)) / 4) <
      ENNReal.ofReal (1 - Real.exp (-1)) * volume (innerPlane k) := by
    rw [hprod]
    exact hmul
  exact (hlt.trans hmid).trans_le hge

/-- The first two coordinate axes. -/
def planeEquiv (d : ℕ) (hd : 2 ≤ d) : Fin 2 ≃ {i : Fin d // i.val ≤ 1} where
  toFun i := ⟨⟨i.val, lt_of_lt_of_le i.isLt hd⟩, Nat.lt_succ_iff.mp i.isLt⟩
  invFun z := ⟨z.1.val, Nat.lt_succ_iff.mpr z.2⟩
  left_inv i := by ext; rfl
  right_inv z := by ext; rfl

/-- The axes beyond the Bohr plane, shifted down by two. -/
def extraEquiv (d : ℕ) (hd : 2 ≤ d) : Fin (d - 2) ≃ {i : Fin d // ¬ i.val ≤ 1} where
  toFun j := ⟨⟨j.val + 2, by
    have h := Nat.add_lt_add_right j.isLt 2
    rwa [Nat.sub_add_cancel hd] at h⟩,
    not_le.mpr (lt_of_lt_of_le (by decide : (1 : ℕ) < 2) (Nat.le_add_left 2 j.val))⟩
  invFun z := ⟨z.1.val - 2, by
    have hlt : z.1.val < d := z.1.isLt
    have hge : 2 ≤ z.1.val := by have := z.2; omega
    omega⟩
  left_inv j := by
    ext
    exact Nat.add_sub_cancel _ _
  right_inv z := by
    have hge : 2 ≤ z.1.val := by have := z.2; omega
    ext
    exact Nat.sub_add_cancel hge

/-- Coordinates split into the Bohr plane and the remaining axes. -/
def splitEquiv (d : ℕ) (hd : 2 ≤ d) :
    (Fin d → ℝ) ≃ᵐ (Fin 2 → ℝ) × (Fin (d - 2) → ℝ) :=
  (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin d => ℝ) (fun i => i.val ≤ 1)).trans
    ((MeasurableEquiv.piCongrLeft (fun _ => ℝ) (planeEquiv d hd)).prodCongr
        (MeasurableEquiv.piCongrLeft (fun _ => ℝ) (extraEquiv d hd))).symm

/-- The coordinate split preserves Lebesgue measure. -/
lemma measurePreserving_splitEquiv (d : ℕ) (hd : 2 ≤ d) :
    MeasurePreserving (splitEquiv d hd) volume volume := by
  unfold splitEquiv
  refine MeasurePreserving.trans
    (volume_preserving_piEquivPiSubtypeProd (fun _ : Fin d => ℝ) (fun i => i.val ≤ 1)) ?_
  refine MeasurePreserving.symm _ ?_
  exact MeasurePreserving.prod
    (volume_measurePreserving_piCongrLeft (fun _ => ℝ) (planeEquiv d hd))
    (volume_measurePreserving_piCongrLeft (fun _ => ℝ) (extraEquiv d hd))

/-- The open unit cube. -/
def unitCube (d : ℕ) : Set (Fin d → ℝ) :=
  univ.pi fun _ => Ioo 0 1

/-- The unit cube has volume one. -/
lemma volume_unitCube (d : ℕ) : volume (unitCube d) = 1 := by
  unfold unitCube
  rw [Real.volume_pi_Ioo]
  simp

/-- Chosen translates at stage `k`. -/
def chosenShifts (k : ℕ) : Fin (copyCount k) → Fin 2 → ℝ :=
  Classical.choose (exists_almost_cover k)

/-- The chosen translates lie in the domain and leave at most an `exp (-1)` gap. -/
lemma chosenShifts_spec (k : ℕ) :
    (∀ i, chosenShifts k i ∈ domain k) ∧
      volume (innerPlane k \ ⋃ i, shiftHit k (chosenShifts k i)) ≤
        ENNReal.ofReal (Real.exp (-1)) * volume (innerPlane k) :=
  Classical.choose_spec (exists_almost_cover k)

/-- Points of the inner square that meet some chosen strip. -/
def planeCover (k : ℕ) : Set (Fin 2 → ℝ) :=
  innerPlane k ∩ ⋃ i, shiftHit k (chosenShifts k i)

/-- The covered part of the inner square has area greater than `1 / 8`. -/
lemma volume_planeCover_pos (k : ℕ) :
    ENNReal.ofReal (1 / 8) < volume (planeCover k) := by
  simpa [planeCover] using
    volume_planeCover_gt k (chosenShifts k) (chosenShifts_spec k).2

/-- The covered part of the inner square is measurable. -/
lemma measurableSet_planeCover (k : ℕ) : MeasurableSet (planeCover k) := by
  have hI : MeasurableSet (innerPlane k) := by
    rw [innerPlane, inner]
    exact (innerRect 2 k le_rfl).measurableSet_carrier
  exact hI.inter (MeasurableSet.iUnion fun i => measurableSet_shiftHit k (chosenShifts k i))

/-- Extra window in which a witnessing side of length `margin` stays inside `(0, 1)`. -/
def extraSet (d k : ℕ) : Set (Fin (d - 2) → ℝ) :=
  univ.pi fun _ => Ioo (margin d k / 2) (1 - margin d k / 2)

/-- The extra window is measurable. -/
lemma measurableSet_extraSet (d k : ℕ) : MeasurableSet (extraSet d k) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ioo

/-- Volume of the extra window. -/
lemma volume_extraSet (d k : ℕ) :
    volume (extraSet d k) = ENNReal.ofReal ((1 - margin d k) ^ (d - 2)) := by
  unfold extraSet
  rw [Real.volume_pi_Ioo]
  have hnn : ∀ i : Fin (d - 2), 0 ≤ (1 - margin d k / 2) - margin d k / 2 := by
    intro _
    linarith [margin_le_inv_four d k]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => hnn i)]
  congr 1
  have hside : ∀ i : Fin (d - 2),
      (1 - margin d k / 2) - margin d k / 2 = 1 - margin d k := by
    intro _
    ring
  rw [Finset.prod_congr rfl fun i _ => hside i, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

/-- The inner square sits in the unit square. -/
lemma innerPlane_subset_unitCube (k : ℕ) : innerPlane k ⊆ unitCube 2 := by
  intro x hx
  rw [unitCube, Set.mem_univ_pi]
  intro i
  rw [innerPlane, inner, OpenRectangle.carrier] at hx
  have h := hx i
  have hi : i.val ≤ 1 := by have := i.isLt; omega
  simp only [innerRect, innerLower, innerUpper, hi, ite_true] at h
  have hb := boxSide_mem_Ioo k
  exact ⟨by linarith, by linarith⟩

/-- The extra window sits in the unit cube of the remaining axes. -/
lemma extraSet_subset_unitCube (d k : ℕ) : extraSet d k ⊆ unitCube (d - 2) := by
  intro x hx
  rw [unitCube, Set.mem_univ_pi]
  intro i
  rw [extraSet, Set.mem_univ_pi] at hx
  have h := hx i
  rw [Set.mem_Ioo] at h
  have hm0 : 0 ≤ margin d k := by
    unfold margin
    split_ifs <;> positivity
  exact ⟨by linarith, by linarith⟩

/-- Stage `k` inside the unit cube: covered plane points with an inner extra window. -/
def stageSet (d k : ℕ) (hd : 2 ≤ d) : Set (Fin d → ℝ) :=
  (splitEquiv d hd) ⁻¹' (planeCover k ×ˢ extraSet d k)

/-- Each stage set is measurable. -/
lemma measurableSet_stageSet (d k : ℕ) (hd : 2 ≤ d) : MeasurableSet (stageSet d k hd) := by
  unfold stageSet
  exact MeasurableSet.preimage
    ((measurableSet_planeCover k).prod (measurableSet_extraSet d k))
    (splitEquiv d hd).measurable

/-- Each stage occupies more than `3 / 32` of the unit cube. -/
lemma volume_stageSet_gt (d k : ℕ) (hd : 2 ≤ d) :
    ENNReal.ofReal (3 / 32) < volume (stageSet d k hd) := by
  rw [stageSet, (measurePreserving_splitEquiv d hd).measure_preimage_equiv,
    Measure.volume_eq_prod, Measure.prod_prod]
  have hP : ENNReal.ofReal (1 / 8) < volume (planeCover k) := volume_planeCover_pos k
  have hE : ENNReal.ofReal (3 / 4) ≤ volume (extraSet d k) := by
    rw [volume_extraSet d k]
    exact ENNReal.ofReal_le_ofReal (extraFactor_ge d k hd)
  have hEpos : volume (extraSet d k) ≠ 0 :=
    (lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (by norm_num)) hE).ne'
  have hEinf : volume (extraSet d k) ≠ ∞ := by
    rw [volume_extraSet d k]
    exact ENNReal.ofReal_ne_top
  have hlt : ENNReal.ofReal (1 / 8) * volume (extraSet d k) <
      volume (planeCover k) * volume (extraSet d k) :=
    ENNReal.mul_lt_mul_left hEpos hEinf hP
  have hle : ENNReal.ofReal (1 / 8) * ENNReal.ofReal (3 / 4) ≤
      ENNReal.ofReal (1 / 8) * volume (extraSet d k) := mul_right_mono hE
  have hprod : ENNReal.ofReal (3 / 32) =
      ENNReal.ofReal (1 / 8) * ENNReal.ofReal (3 / 4) := by
    rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 8)]
    congr 1
    norm_num
  exact (hprod ▸ hle).trans_lt hlt

/-- Points that meet some stage at index `n` or later. -/
def tailSet (d n : ℕ) (hd : 2 ≤ d) : Set (Fin d → ℝ) :=
  ⋃ k ∈ Set.Ici n, stageSet d k hd

/-- The tail is measurable. -/
lemma measurableSet_tailSet (d n : ℕ) (hd : 2 ≤ d) : MeasurableSet (tailSet d n hd) := by
  unfold tailSet
  exact MeasurableSet.biUnion ((Set.countable_univ).mono (Set.subset_univ _))
    fun k _ => measurableSet_stageSet d k hd

/-- Later tails are smaller. -/
lemma antitone_tailSet (d : ℕ) (hd : 2 ≤ d) : Antitone (fun n => tailSet d n hd) := by
  intro a b hab x hx
  simp only [tailSet, Set.mem_iUnion, Set.mem_Ici] at hx ⊢
  obtain ⟨k, hk, hxk⟩ := hx
  exact ⟨k, hab.trans hk, hxk⟩

/-- Stage `n` is contained in the tail from `n`. -/
lemma stageSet_subset_tailSet (d n : ℕ) (hd : 2 ≤ d) :
    stageSet d n hd ⊆ tailSet d n hd := by
  intro x hx
  simp only [tailSet, Set.mem_iUnion, Set.mem_Ici]
  exact ⟨n, le_rfl, hx⟩

/-- Every tail has measure greater than `3 / 32`. -/
lemma volume_tailSet_gt (d n : ℕ) (hd : 2 ≤ d) :
    ENNReal.ofReal (3 / 32) < volume (tailSet d n hd) :=
  (volume_stageSet_gt d n hd).trans_le (measure_mono (stageSet_subset_tailSet d n hd))

/-- The covered plane sits in the unit square. -/
lemma planeCover_subset_unitCube (k : ℕ) : planeCover k ⊆ unitCube 2 :=
  fun _ hx => innerPlane_subset_unitCube k hx.1

/-- Each stage sits in the preimage of the unit cubes. -/
lemma stageSet_subset_unitPreimage (d k : ℕ) (hd : 2 ≤ d) :
    stageSet d k hd ⊆ (splitEquiv d hd) ⁻¹' (unitCube 2 ×ˢ unitCube (d - 2)) := by
  intro x hx
  rw [stageSet, Set.mem_preimage] at hx
  rw [Set.mem_preimage, Set.mem_prod]
  exact ⟨planeCover_subset_unitCube k hx.1, extraSet_subset_unitCube d k hx.2⟩

/-- Every tail sits in the preimage of the unit cubes. -/
lemma tailSet_subset_unitPreimage (d n : ℕ) (hd : 2 ≤ d) :
    tailSet d n hd ⊆ (splitEquiv d hd) ⁻¹' (unitCube 2 ×ˢ unitCube (d - 2)) := by
  intro x hx
  simp only [tailSet, Set.mem_iUnion, Set.mem_Ici] at hx
  obtain ⟨k, _, hxk⟩ := hx
  exact stageSet_subset_unitPreimage d k hd hxk

/-- The split preimage of the unit cubes has measure one. -/
lemma volume_split_unit (d : ℕ) (hd : 2 ≤ d) :
    volume ((splitEquiv d hd) ⁻¹' (unitCube 2 ×ˢ unitCube (d - 2))) = 1 := by
  rw [(measurePreserving_splitEquiv d hd).measure_preimage_equiv, Measure.volume_eq_prod,
    Measure.prod_prod, volume_unitCube, volume_unitCube, mul_one]

/-- Every tail has finite measure. -/
lemma volume_tailSet_lt_top (d n : ℕ) (hd : 2 ≤ d) : volume (tailSet d n hd) < ∞ := by
  refine lt_of_le_of_lt (measure_mono (tailSet_subset_unitPreimage d n hd)) ?_
  rw [volume_split_unit d hd]
  exact ENNReal.one_lt_top

/-- Points that lie in infinitely many tails. -/
def limsupSet (d : ℕ) (hd : 2 ≤ d) : Set (Fin d → ℝ) :=
  ⋂ n, tailSet d n hd

/-- The limsup has measure at least `3 / 32`. -/
lemma volume_limsupSet_ge (d : ℕ) (hd : 2 ≤ d) :
    ENNReal.ofReal (3 / 32) ≤ volume (limsupSet d hd) := by
  have hanti : Antitone (fun n => tailSet d n hd) := antitone_tailSet d hd
  have hsm : ∀ n, NullMeasurableSet (tailSet d n hd) volume :=
    fun n => (measurableSet_tailSet d n hd).nullMeasurableSet
  have hfin : ∃ n, volume (tailSet d n hd) ≠ ∞ :=
    ⟨0, (volume_tailSet_lt_top d 0 hd).ne⟩
  rw [limsupSet, hanti.measure_iInter hsm hfin]
  exact le_iInf fun n => (volume_tailSet_gt d n hd).le

/-- First component of the coordinate split, on the Bohr plane. -/
lemma splitEquiv_fst (d : ℕ) (hd : 2 ≤ d) (x : Fin d → ℝ) (i : Fin 2) :
    (splitEquiv d hd x).1 i = x (planeEquiv d hd i).1 := by
  unfold splitEquiv
  simp only [MeasurableEquiv.trans_apply, MeasurableEquiv.piEquivPiSubtypeProd_apply]
  change (MeasurableEquiv.piCongrLeft (fun _ => ℝ) (planeEquiv d hd)).symm
      (fun z : {i : Fin d // i.val ≤ 1} => x z.1) i =
    x (planeEquiv d hd i).1
  exact Equiv.piCongrLeft_symm_apply (fun _ => ℝ) (planeEquiv d hd)
    (fun z => x z.1) i

/-- Second component of the coordinate split, on the remaining axes. -/
lemma splitEquiv_snd (d : ℕ) (hd : 2 ≤ d) (x : Fin d → ℝ) (j : Fin (d - 2)) :
    (splitEquiv d hd x).2 j = x (extraEquiv d hd j).1 := by
  unfold splitEquiv
  simp only [MeasurableEquiv.trans_apply, MeasurableEquiv.piEquivPiSubtypeProd_apply]
  change (MeasurableEquiv.piCongrLeft (fun _ => ℝ) (extraEquiv d hd)).symm
      (fun z : {i : Fin d // ¬ i.val ≤ 1} => x z.1) j =
    x (extraEquiv d hd j).1
  exact Equiv.piCongrLeft_symm_apply (fun _ => ℝ) (extraEquiv d hd)
    (fun z => x z.1) j

/-- The scaled picture has width `2 ^ (-(k + 2))` times `N + 1` in the denominator. -/
lemma stageScale_mul_succ (k : ℕ) :
    stageScale k * ((stageCount k : ℝ) + 1) = (2 ^ (k + 2) : ℝ)⁻¹ := by
  unfold stageScale
  rw [one_div, mul_inv, mul_assoc, inv_mul_cancel₀ (by positivity), mul_one]
  simp [Nat.cast_pow, Nat.cast_ofNat]

/-- Twice the reciprocal of the strip area equals the normalized spike mass. -/
lemma stageTerm_eq (k : ℕ) :
    (2 : ℝ) / areaLower k * stageHeight k * (stageCount k : ℝ) * stageScale k ^ 2 =
      (1 / 2 : ℝ) ^ (k + 2) := by
  have hτ : stageScale k ^ 2 ≠ 0 := (pow_pos (stageScale_pos k) 2).ne'
  have hN : (stageCount k : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.two_pow_pos (stageLog k) : 0 < stageCount k).ne'
  have hA : stageHeight k ≠ 0 := by unfold stageHeight; positivity
  have hden : stageScale k ^ 2 * (stageCount k : ℝ) ≠ 0 := mul_ne_zero hτ hN
  rw [areaLower, div_mul_eq_mul_div₀, div_mul_eq_mul_div₀, div_mul_eq_mul_div₀]
  have hnum : ((2 * stageHeight k) * (stageCount k : ℝ)) * stageScale k ^ 2 =
      (stageScale k ^ 2 * (stageCount k : ℝ)) * (2 * stageHeight k) := by ac_rfl
  rw [hnum, mul_div_mul_left _ _ hden, div_div_eq_mul_div]
  have hfour : (2 * stageHeight k) * 2 = 4 * stageHeight k := by
    rw [mul_assoc, mul_comm (stageHeight k) 2, ← mul_assoc]
    norm_num
  rw [hfour]
  have hm : (stageLog k : ℝ) = stageHeight k * (2 : ℝ) ^ (k + 4) := by
    simp [stageLog, stageHeight, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [hm, mul_comm (4 : ℝ) (stageHeight k), mul_div_mul_left _ _ hA]
  have hpow : (2 : ℝ) ^ (k + 4) = (2 : ℝ) ^ (k + 2) * 4 := by
    rw [show k + 4 = (k + 2) + 2 by omega, pow_add, pow_two]
    norm_num
  rw [hpow, mul_comm ((2 : ℝ) ^ (k + 2)) 4]
  have h4 : (4 : ℝ) ≠ 0 := by norm_num
  have hcancel : (4 : ℝ) / (4 * (2 : ℝ) ^ (k + 2)) = 1 / (2 : ℝ) ^ (k + 2) :=
    calc
      (4 : ℝ) / (4 * (2 : ℝ) ^ (k + 2)) = (4 * 1) / (4 * (2 : ℝ) ^ (k + 2)) := by
        rw [mul_one]
      _ = 1 / (2 : ℝ) ^ (k + 2) := mul_div_mul_left 1 _ h4
  rw [hcancel, one_div, ← inv_pow, ← one_div]

/-- Copies times one spike mass stay below a geometric term. -/
lemma stageMass_le (k : ℕ) :
    (copyCount k : ℝ) * stageHeight k * (stageCount k : ℝ) * stageScale k ^ 2 ≤
      (1 / 2 : ℝ) ^ (k + 2) := by
  have hr := removalRatio_mem_Ioo k
  have hle := copyCount_le k
  have h1 : (1 : ℝ) ≤ 1 / removalRatio k := by
    rw [one_le_div hr.1]
    exact hr.2.le
  have hcount : (copyCount k : ℝ) ≤ 2 / removalRatio k :=
    hle.trans <| calc
      1 / removalRatio k + 1 ≤ 1 / removalRatio k + 1 / removalRatio k :=
        add_le_add le_rfl h1
      _ = 2 / removalRatio k := by rw [← add_div]; norm_num
  have hdom : volume.real (domain k) ≤ 1 := by
    rw [volume_real_domain]
    have hL := boxSide_mem_Ioo k
    nlinarith
  have hτ : 0 < stageScale k := stageScale_pos k
  have hN : (0 : ℝ) < stageCount k := by
    exact_mod_cast (Nat.two_pow_pos (stageLog k) : 0 < stageCount k)
  have hA : 0 < stageHeight k := by unfold stageHeight; positivity
  have harea : 0 < areaLower k := areaLower_pos k
  have hstep :
      (copyCount k : ℝ) * stageHeight k * ↑(stageCount k) * stageScale k ^ 2 ≤
        (2 / removalRatio k) * stageHeight k * ↑(stageCount k) * stageScale k ^ 2 := by
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    refine mul_le_mul_of_nonneg_right ?_ hN.le
    exact mul_le_mul_of_nonneg_right hcount hA.le
  rw [show (2 : ℝ) / removalRatio k = 2 * volume.real (domain k) / areaLower k by
    rw [removalRatio, div_div_eq_mul_div]] at hstep
  have hfrac : 2 * volume.real (domain k) / areaLower k ≤ (2 : ℝ) / areaLower k := by
    rw [div_le_div_iff_of_pos_right harea]
    nlinarith
  have hstep2 :
      2 * volume.real (domain k) / areaLower k * stageHeight k * ↑(stageCount k) *
          stageScale k ^ 2 ≤
        (2 : ℝ) / areaLower k * stageHeight k * ↑(stageCount k) * stageScale k ^ 2 := by
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    refine mul_le_mul_of_nonneg_right ?_ hN.le
    exact mul_le_mul_of_nonneg_right hfrac hA.le
  exact hstep.trans <| hstep2.trans_eq (stageTerm_eq k)

/-- Corner spike of one translated picture. -/
def spikeRect (d : ℕ) (_hd : 2 ≤ d) (k : ℕ) (v : Fin 2 → ℝ) : OpenRectangle d where
  lower i := if h : i.val ≤ 1 then v ⟨i.val, Nat.lt_succ_iff.mpr h⟩ else 0
  upper i := if h : i.val ≤ 1 then v ⟨i.val, Nat.lt_succ_iff.mpr h⟩ + stageScale k else 1
  lower_lt_upper i := by
    by_cases h : i.val ≤ 1
    · simp only [h, dite_true]
      linarith [stageScale_pos k]
    · simp only [h, dite_false]
      norm_num

/-- Real volume of one corner spike. -/
lemma volume_real_spike (d : ℕ) (hd : 2 ≤ d) (k : ℕ) (v : Fin 2 → ℝ) :
    volume.real (spikeRect d hd k v).carrier = stageScale k ^ 2 := by
  have hle i := (spikeRect d hd k v).lower_lt_upper i |>.le
  rw [measureReal_def, (spikeRect d hd k v).carrier_eq_pi, Real.volume_pi_Ioo_toReal hle]
  let p : Fin d → Prop := fun i => i.val ≤ 1
  have hsplit := Finset.prod_filter_mul_prod_filter_not Finset.univ p
    (fun i => (spikeRect d hd k v).upper i - (spikeRect d hd k v).lower i)
  rw [← hsplit]
  have hsideP : ∀ i, i.val ≤ 1 →
      (spikeRect d hd k v).upper i - (spikeRect d hd k v).lower i = stageScale k := by
    intro i hi
    simp only [spikeRect, hi, dite_true]
    exact add_sub_cancel_left _ _
  have hsideE : ∀ i, ¬ i.val ≤ 1 →
      (spikeRect d hd k v).upper i - (spikeRect d hd k v).lower i = 1 := by
    intro i hi
    simp only [spikeRect, hi, dite_false, sub_zero]
  have hplane : ∏ i ∈ Finset.univ.filter p,
      ((spikeRect d hd k v).upper i - (spikeRect d hd k v).lower i) = stageScale k ^ 2 := by
    rw [Finset.prod_congr rfl (fun i hi => hsideP i (Finset.mem_filter.mp hi).2)]
    rw [Finset.prod_const, card_plane d hd]
  have hextra : ∏ i ∈ Finset.univ.filter (fun i => ¬ p i),
      ((spikeRect d hd k v).upper i - (spikeRect d hd k v).lower i) = 1 := by
    rw [Finset.prod_congr rfl (fun i hi => by
      have hi' : ¬ i.val ≤ 1 := (Finset.mem_filter.mp hi).2
      exact hsideE i hi')]
    rw [Finset.prod_const_one]
  rw [hplane, hextra, mul_one]

/-- Height of the corner spike at stage `k`. -/
def spikeHeight (k : ℕ) : ℝ := stageHeight k * stageCount k

/-- Indicator of one corner spike. -/
def bump (d : ℕ) (hd : 2 ≤ d) (k : ℕ) (v : Fin 2 → ℝ) (x : Fin d → ℝ) : ℝ :=
  (spikeRect d hd k v).carrier.indicator (fun _ => spikeHeight k) x

/-- Nonnegative extended spike. -/
def bumpENN (d : ℕ) (hd : 2 ≤ d) (k : ℕ) (v : Fin 2 → ℝ) (x : Fin d → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (bump d hd k v x)

/-- Sum of every corner spike. -/
def raw (d : ℕ) (hd : 2 ≤ d) (x : Fin d → ℝ) : ℝ≥0∞ :=
  ∑' p : Σ k, Fin (copyCount k), bumpENN d hd p.1 (chosenShifts p.1 p.2) x

/-- The Saks function, finite part of the spike sum. -/
def saks (d : ℕ) (hd : 2 ≤ d) : (Fin d → ℝ) → ℝ := fun x => (raw d hd x).toReal

/-- Each spike indicator is measurable. -/
lemma measurable_bump (d : ℕ) (hd : 2 ≤ d) (k : ℕ) (v : Fin 2 → ℝ) :
    Measurable (bump d hd k v) :=
  measurable_const.indicator (spikeRect d hd k v).measurableSet_carrier

/-- The spike sum is measurable. -/
lemma measurable_raw (d : ℕ) (hd : 2 ≤ d) : Measurable (raw d hd) := by
  unfold raw bumpENN
  simp_rw [ENNReal.tsum_eq_iSup_sum]
  refine Measurable.iSup fun s => Finset.measurable_fun_sum s fun p _ => ?_
  exact (measurable_bump d hd p.1 (chosenShifts p.1 p.2)).ennreal_ofReal

/-- The Saks function is measurable. -/
lemma measurable_saks (d : ℕ) (hd : 2 ≤ d) : Measurable (saks d hd) :=
  (measurable_raw d hd).ennreal_toReal

/-- Integral of one spike. -/
lemma lintegral_bump (d : ℕ) (hd : 2 ≤ d) (k : ℕ) (v : Fin 2 → ℝ) :
    ∫⁻ x, bumpENN d hd k v x = ENNReal.ofReal (spikeHeight k * stageScale k ^ 2) := by
  unfold bumpENN bump
  have hnn : 0 ≤ spikeHeight k := by unfold spikeHeight stageHeight; positivity
  set R := spikeRect d hd k v with hR
  have hind : (fun x => ENNReal.ofReal (R.carrier.indicator (fun _ => spikeHeight k) x)) =
      R.carrier.indicator (fun _ => ENNReal.ofReal (spikeHeight k)) := by
    funext x
    by_cases hx : x ∈ R.carrier
    · rw [indicator_of_mem hx, indicator_of_mem hx]
    · rw [indicator_of_notMem hx, indicator_of_notMem hx, ENNReal.ofReal_zero]
  rw [hind, lintegral_indicator R.measurableSet_carrier, setLIntegral_const]
  have hvol : volume R.carrier = ENNReal.ofReal (stageScale k ^ 2) := by
    rw [hR, ← ENNReal.ofReal_toReal (spikeRect d hd k v).volume_carrier_lt_top.ne,
      ← measureReal_def, volume_real_spike d hd k v]
  rw [hvol, ← ENNReal.ofReal_mul hnn]

end CKMA.Bohr
