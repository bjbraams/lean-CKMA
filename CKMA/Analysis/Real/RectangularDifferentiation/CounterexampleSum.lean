/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.Real.RectangularDifferentiation.CounterexampleCover

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# Integrability of the Saks sum

The rectangular spikes form a measurable integrable function. On the limsup of the stage
sets, a witness rectangle has average at least the stage height and total width tending to
zero, so rectangular differentiation fails on a set of positive measure.
-/

@[expose] public section

noncomputable section

open Classical MeasureTheory Set Filter Finset
open scoped ENNReal NNReal BigOperators

namespace CKMA.Bohr

/-- A constant extended sum over a finite type is the cardinality times the constant. -/
lemma tsum_fin_const (n : ℕ) (c : ℝ≥0∞) : ∑' _i : Fin n, c = (n : ℝ≥0∞) * c := by
  classical
  rw [ENNReal.tsum_eq_iSup_sum]
  refine le_antisymm ?_ ?_
  · exact iSup_le fun s => by
      calc
        ∑ _i ∈ s, c ≤ ∑ _i ∈ (Finset.univ : Finset (Fin n)), c :=
          Finset.sum_le_sum_of_subset (Finset.subset_univ _)
        _ = (n : ℝ≥0∞) * c := by
          simp [Finset.sum_const, nsmul_eq_mul, Fintype.card_fin]
  · have hsum : ∑ _i ∈ (Finset.univ : Finset (Fin n)), c = (n : ℝ≥0∞) * c := by
      simp [Finset.sum_const, nsmul_eq_mul, Fintype.card_fin]
    rw [← hsum]
    exact le_iSup (fun s : Finset (Fin n) => ∑ _i ∈ s, c) Finset.univ

/-- The shifted geometric series of ratio one half sums to one half. -/
lemma tsum_half_pow_shift : ∑' k : ℕ, (1 / 2 : ℝ) ^ (k + 2) = 1 / 2 := by
  have hpow : ∀ k, (1 / 2 : ℝ) ^ (k + 2) = (1 / 4) * (1 / 2) ^ k := by
    intro k
    rw [pow_add, pow_two]
    have : (1 / 2 : ℝ) * (1 / 2) = 1 / 4 := by norm_num
    rw [this, mul_comm]
  simp_rw [hpow]
  rw [summable_geometric_two.tsum_mul_left (1 / 4), tsum_geometric_two]
  norm_num

/-- One stage of chosen spikes has integral `copyCount` times one spike mass. -/
lemma lintegral_stage (d : ℕ) (hd : 2 ≤ d) (k : ℕ) :
    ∑' i : Fin (copyCount k), ∫⁻ x, bumpENN d hd k (chosenShifts k i) x =
      (copyCount k : ℝ≥0∞) *
        ENNReal.ofReal (spikeHeight k * stageScale k ^ 2) := by
  simp_rw [lintegral_bump d hd k]
  exact tsum_fin_const (copyCount k) _

/-- The geometric tail of ratio one half is summable. -/
lemma summable_half_pow_shift :
    Summable (fun k : ℕ => (1 / 2 : ℝ) ^ (k + 2)) := by
  have hpow : ∀ k : ℕ, (1 / 2 : ℝ) ^ (k + 2) = (1 / 4) * (1 / 2) ^ k := by
    intro k
    rw [pow_add, pow_two]
    have : (1 / 2 : ℝ) * (1 / 2) = 1 / 4 := by norm_num
    rw [this, mul_comm]
  simp_rw [hpow]
  exact summable_geometric_two.mul_left (1 / 4)

/-- One stage mass is at most the corresponding geometric term. -/
lemma stageMass_ennreal_le (k : ℕ) :
    (copyCount k : ℝ≥0∞) * ENNReal.ofReal (spikeHeight k * stageScale k ^ 2) ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ (k + 2)) := by
  have hnn : 0 ≤ (copyCount k : ℝ) := Nat.cast_nonneg _
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul hnn]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [spikeHeight, ← mul_assoc, ← mul_assoc]
  exact stageMass_le k

/-- The integral of the spike sum is the sum of the stage masses. -/
lemma lintegral_raw_eq (d : ℕ) (hd : 2 ≤ d) :
    ∫⁻ x, raw d hd x =
      ∑' k, (copyCount k : ℝ≥0∞) *
        ENNReal.ofReal (spikeHeight k * stageScale k ^ 2) := by
  unfold raw
  rw [lintegral_tsum]
  · rw [ENNReal.tsum_sigma']
    exact tsum_congr (lintegral_stage d hd)
  · intro p
    exact (measurable_bump d hd p.1
      (chosenShifts p.1 p.2)).ennreal_ofReal.aemeasurable

/-- The spike sum has finite integral. -/
lemma lintegral_raw_ne_top (d : ℕ) (hd : 2 ≤ d) : ∫⁻ x, raw d hd x ≠ ∞ := by
  rw [lintegral_raw_eq d hd]
  exact ne_top_of_le_ne_top summable_half_pow_shift.tsum_ofReal_ne_top
    (ENNReal.tsum_le_tsum stageMass_ennreal_le)

/-- The Saks function is integrable. -/
lemma integrable_saks (d : ℕ) (hd : 2 ≤ d) : Integrable (saks d hd) volume :=
  integrable_toReal_of_lintegral_ne_top (measurable_raw d hd).aemeasurable
    (lintegral_raw_ne_top d hd)

/-- One rectangular spike is integrable. -/
lemma integrable_bump (d : ℕ) (hd : 2 ≤ d) (k : ℕ) (v : Fin 2 → ℝ) :
    Integrable (bump d hd k v) volume := by
  unfold bump
  rw [integrable_indicator_iff (spikeRect d hd k v).measurableSet_carrier]
  exact integrableOn_const (spikeRect d hd k v).volume_carrier_lt_top.ne

/-- Each chosen spike is at most the Saks function wherever the sum is finite. -/
lemma bump_le_saks (d : ℕ) (hd : 2 ≤ d) (k : ℕ) (i : Fin (copyCount k)) (x : Fin d → ℝ)
    (hfin : raw d hd x ≠ ∞) :
    bump d hd k (chosenShifts k i) x ≤ saks d hd x := by
  have hnn : 0 ≤ bump d hd k (chosenShifts k i) x := by
    unfold bump
    exact indicator_nonneg (fun _ _ => by unfold spikeHeight stageHeight; positivity) x
  have hle : bumpENN d hd k (chosenShifts k i) x ≤ raw d hd x := by
    unfold raw
    exact ENNReal.le_tsum (f := fun p : Σ n, Fin (copyCount n) =>
      bumpENN d hd p.1 (chosenShifts p.1 p.2) x) ⟨k, i⟩
  have hto := ENNReal.toReal_mono hfin hle
  rw [bumpENN, ENNReal.toReal_ofReal hnn] at hto
  simpa [saks] using hto

/-- Real volume is the product of the side lengths. -/
lemma volume_real_sides {d : ℕ} (R : OpenRectangle d) :
    volume.real R.carrier = ∏ i, (R.upper i - R.lower i) := by
  have hnn : ∀ i, 0 ≤ R.upper i - R.lower i := fun i => sub_nonneg.mpr (R.lower_lt_upper i).le
  rw [measureReal_def, R.volume_carrier,
    ← ENNReal.ofReal_prod_of_nonneg (fun i _ => hnn i),
    ENNReal.toReal_ofReal (Finset.prod_nonneg (fun i _ => hnn i))]

/-- `j + N / j` is at most `N + 1` on the harmonic range. -/
lemma ratio_le_succ (k j : ℕ) (hj : j ∈ Finset.Icc 2 (stageCount k)) :
    (j : ℝ) + (stageCount k : ℝ) / j ≤ (stageCount k : ℝ) + 1 := by
  have hjI := Finset.mem_Icc.mp hj
  have hj0 : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  rw [← mul_le_mul_iff_of_pos_right hj0]
  have hleft : ((j : ℝ) + (stageCount k : ℝ) / j) * j =
      (j : ℝ) * j + (stageCount k : ℝ) := by
    rw [add_mul, div_mul_cancel₀ _ hj0.ne']
  have hright : ((stageCount k : ℝ) + 1) * j = (stageCount k : ℝ) * j + j := by
    rw [add_mul, one_mul]
  rw [hleft, hright]
  have hjN : (j : ℝ) ≤ stageCount k := by exact_mod_cast hjI.2
  have hj2 : (2 : ℝ) ≤ j := by exact_mod_cast hjI.1
  have hj1 : (1 : ℝ) ≤ j := by linarith
  nlinarith

/-- The two plane sides of a witness are at most `2 ^ (-(k + 2))`. -/
lemma planeWidth_le (k j : ℕ) (hj : j ∈ Finset.Icc 2 (stageCount k)) :
    stageScale k * (j : ℝ) + stageScale k * (stageCount k : ℝ) / j ≤
      (2 ^ (k + 2) : ℝ)⁻¹ := by
  calc
    stageScale k * (j : ℝ) + stageScale k * (stageCount k : ℝ) / j
        = stageScale k * ((j : ℝ) + (stageCount k : ℝ) / j) := by
          rw [mul_div_assoc, ← mul_add]
    _ ≤ stageScale k * ((stageCount k : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left (ratio_le_succ k j hj) (stageScale_pos k).le
    _ = (2 ^ (k + 2) : ℝ)⁻¹ := stageScale_mul_succ k

/-- Twice `2 ^ (-(k + 2))` is `2 ^ (-(k + 1))`. -/
lemma two_mul_inv_pow (k : ℕ) :
    (2 : ℝ) * (2 ^ (k + 2))⁻¹ = (1 / 2 : ℝ) ^ (k + 1) := by
  have hinv : (2 ^ (k + 2) : ℝ)⁻¹ = (1 / 2) ^ (k + 2) := by
    rw [← inv_pow, ← one_div]
  rw [hinv, pow_succ', ← mul_assoc]
  norm_num

/-- Extra side length is positive in dimension greater than two. -/
lemma margin_pos (d k : ℕ) (hd : 2 < d) : 0 < margin d k := by
  have hnot : ¬ d ≤ 2 := by omega
  simp only [margin, hnot, ite_false, one_div]
  have hden : (0 : ℕ) < 2 ^ (k + 2) * (d - 2) :=
    Nat.mul_pos (Nat.two_pow_pos _) (by omega)
  have hdenR : (0 : ℝ) < (2 ^ (k + 2) * (d - 2) : ℕ) := by exact_mod_cast hden
  exact inv_pos.mpr hdenR

/-- The extra sides contribute at most `2 ^ (-(k + 2))` to the total width. -/
lemma extraWidth_le (d k : ℕ) (hd : 2 ≤ d) :
    ((d - 2 : ℕ) : ℝ) * margin d k ≤ (2 ^ (k + 2) : ℝ)⁻¹ := by
  by_cases hd2 : d = 2
  · simp only [hd2, Nat.sub_self, Nat.cast_zero, zero_mul]
    positivity
  · exact (extraWidth d k (by omega)).le

/-- Witness rectangle through one strip, with a centered extra window. -/
def witnessRect (d : ℕ) (_hd : 2 ≤ d) (k : ℕ) (v : Fin 2 → ℝ) (j : ℕ) (hj : 2 ≤ j)
    (z : Fin (d - 2) → ℝ) : OpenRectangle d where
  lower i :=
    if h0 : i.val = 0 then v 0
    else if h1 : i.val = 1 then v 1
    else z ⟨i.val - 2, by
      have hlt : i.val < d := i.isLt
      omega⟩ - margin d k / 2
  upper i :=
    if h0 : i.val = 0 then v 0 + stageScale k * (j : ℝ)
    else if h1 : i.val = 1 then v 1 + stageScale k * (stageCount k : ℝ) / (j : ℝ)
    else z ⟨i.val - 2, by
      have hlt : i.val < d := i.isLt
      omega⟩ + margin d k / 2
  lower_lt_upper i := by
    by_cases h0 : i.val = 0
    · have hj0 : (0 : ℝ) < (j : ℝ) := by exact_mod_cast (show 0 < j by omega)
      rw [dif_pos h0, dif_pos h0]
      exact lt_add_of_pos_right _ (mul_pos (stageScale_pos k) hj0)
    · by_cases h1 : i.val = 1
      · have hN : (0 : ℝ) < (stageCount k : ℝ) := by
          exact_mod_cast (Nat.two_pow_pos (stageLog k) : 0 < stageCount k)
        have hj0 : (0 : ℝ) < (j : ℝ) := by exact_mod_cast (show 0 < j by omega)
        rw [dif_neg h0, dif_pos h1, dif_neg h0, dif_pos h1]
        exact lt_add_of_pos_right _ (div_pos (mul_pos (stageScale_pos k) hN) hj0)
      · have hm : 0 < margin d k := margin_pos d k (by have := i.isLt; omega)
        rw [dif_neg h0, dif_neg h1, dif_neg h0, dif_neg h1]
        linarith

/-- Plane side of the witness parallel to the first axis. -/
lemma witness_side_zero (d : ℕ) (hd : 2 ≤ d) (k : ℕ) (v : Fin 2 → ℝ) (j : ℕ) (hj : 2 ≤ j)
    (z : Fin (d - 2) → ℝ) (i : Fin d) (hi : i.val = 0) :
    (witnessRect d hd k v j hj z).upper i - (witnessRect d hd k v j hj z).lower i =
      stageScale k * (j : ℝ) := by
  simp only [witnessRect, hi, dite_true, add_sub_cancel_left]

/-- Plane side of the witness parallel to the second axis. -/
lemma witness_side_one (d : ℕ) (hd : 2 ≤ d) (k : ℕ) (v : Fin 2 → ℝ) (j : ℕ) (hj : 2 ≤ j)
    (z : Fin (d - 2) → ℝ) (i : Fin d) (hi : i.val = 1) :
    (witnessRect d hd k v j hj z).upper i - (witnessRect d hd k v j hj z).lower i =
      stageScale k * (stageCount k : ℝ) / (j : ℝ) := by
  have h0 : i.val ≠ 0 := by omega
  simp only [witnessRect]
  rw [dif_neg h0, dif_pos hi, dif_neg h0, dif_pos hi]
  exact add_sub_cancel_left _ _

/-- Each extra side of the witness has length `margin`. -/
lemma witness_side_extra (d : ℕ) (hd : 2 ≤ d) (k : ℕ) (v : Fin 2 → ℝ) (j : ℕ) (hj : 2 ≤ j)
    (z : Fin (d - 2) → ℝ) (i : Fin d) (hi : ¬ i.val ≤ 1) :
    (witnessRect d hd k v j hj z).upper i - (witnessRect d hd k v j hj z).lower i =
      margin d k := by
  have h0 : i.val ≠ 0 := by omega
  have h1 : i.val ≠ 1 := by omega
  simp only [witnessRect, h0, h1, dite_false]
  ring

/-- The witness is narrower than `2 ^ (-(k + 1))`. -/
lemma witness_totalWidth_le (d : ℕ) (hd : 2 ≤ d) (k : ℕ) (v : Fin 2 → ℝ) (j : ℕ)
    (hj : j ∈ Finset.Icc 2 (stageCount k)) (z : Fin (d - 2) → ℝ) :
    (witnessRect d hd k v j (Finset.mem_Icc.mp hj).1 z).totalWidth ≤
      (1 / 2 : ℝ) ^ (k + 1) := by
  let R := witnessRect d hd k v j (Finset.mem_Icc.mp hj).1 z
  let p : Fin d → Prop := fun i => i.val ≤ 1
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ p
    (fun i => R.upper i - R.lower i)
  unfold OpenRectangle.totalWidth
  rw [← hsplit]
  let z0 : Fin d := ⟨0, by omega⟩
  let z1 : Fin d := ⟨1, by omega⟩
  have hne : z0 ≠ z1 := by
    intro h
    have := congrArg Fin.val h
    simp [z0, z1] at this
  have hset : Finset.univ.filter p = {z0, z1} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, p]
    constructor
    · intro hi
      rcases (show i.val = 0 ∨ i.val = 1 by omega) with h0 | h1
      · left
        ext
        simp [z0, h0]
      · right
        ext
        simp [z1, h1]
    · intro h
      rcases h with rfl | rfl
      · simp [z0]
      · simp [z1]
  have hplane : ∑ i ∈ Finset.univ.filter p, (R.upper i - R.lower i) =
      stageScale k * (j : ℝ) + stageScale k * (stageCount k : ℝ) / j := by
    rw [hset, Finset.sum_pair hne]
    rw [witness_side_zero d hd k v j (Finset.mem_Icc.mp hj).1 z z0 (by simp [z0]),
      witness_side_one d hd k v j (Finset.mem_Icc.mp hj).1 z z1 (by simp [z1])]
  have hextra : ∑ i ∈ Finset.univ.filter (fun i => ¬ p i), (R.upper i - R.lower i) =
      ((d - 2 : ℕ) : ℝ) * margin d k := by
    rw [Finset.sum_congr rfl (fun i hi =>
      witness_side_extra d hd k v j (Finset.mem_Icc.mp hj).1 z i (Finset.mem_filter.mp hi).2)]
    rw [Finset.sum_const, card_extra d hd, nsmul_eq_mul]
  rw [hplane, hextra]
  calc
    stageScale k * (j : ℝ) + stageScale k * (stageCount k : ℝ) / j +
          ((d - 2 : ℕ) : ℝ) * margin d k
        ≤ (2 ^ (k + 2) : ℝ)⁻¹ + (2 ^ (k + 2) : ℝ)⁻¹ :=
          add_le_add (planeWidth_le k j hj) (extraWidth_le d k hd)
    _ = (1 / 2 : ℝ) ^ (k + 1) := by rw [← two_mul, two_mul_inv_pow k]

/-- Intersection of the witness with the corner spike. -/
def interRect (d : ℕ) (_hd : 2 ≤ d) (k : ℕ) (v : Fin 2 → ℝ) (z : Fin (d - 2) → ℝ) :
    OpenRectangle d where
  lower i :=
    if h0 : i.val = 0 then v 0
    else if h1 : i.val = 1 then v 1
    else z ⟨i.val - 2, by
      have hlt : i.val < d := i.isLt
      omega⟩ - margin d k / 2
  upper i :=
    if h0 : i.val = 0 then v 0 + stageScale k
    else if h1 : i.val = 1 then v 1 + stageScale k
    else z ⟨i.val - 2, by
      have hlt : i.val < d := i.isLt
      omega⟩ + margin d k / 2
  lower_lt_upper i := by
    by_cases h0 : i.val = 0
    · rw [dif_pos h0, dif_pos h0]
      exact lt_add_of_pos_right _ (stageScale_pos k)
    · by_cases h1 : i.val = 1
      · rw [dif_neg h0, dif_pos h1, dif_neg h0, dif_pos h1]
        exact lt_add_of_pos_right _ (stageScale_pos k)
      · have hm : 0 < margin d k := margin_pos d k (by have := i.isLt; omega)
        rw [dif_neg h0, dif_neg h1, dif_neg h0, dif_neg h1]
        linarith

/-- First plane side of the intersection. -/
lemma inter_side_zero (d : ℕ) (hd : 2 ≤ d) (k : ℕ) (v : Fin 2 → ℝ) (z : Fin (d - 2) → ℝ)
    (i : Fin d) (hi : i.val = 0) :
    (interRect d hd k v z).upper i - (interRect d hd k v z).lower i = stageScale k := by
  simp only [interRect, hi, dite_true, add_sub_cancel_left]

/-- Second plane side of the intersection. -/
lemma inter_side_one (d : ℕ) (hd : 2 ≤ d) (k : ℕ) (v : Fin 2 → ℝ) (z : Fin (d - 2) → ℝ)
    (i : Fin d) (hi : i.val = 1) :
    (interRect d hd k v z).upper i - (interRect d hd k v z).lower i = stageScale k := by
  have h0 : i.val ≠ 0 := by omega
  simp only [interRect]
  rw [dif_neg h0, dif_pos hi, dif_neg h0, dif_pos hi]
  exact add_sub_cancel_left _ _

/-- Each extra side of the intersection has length `margin`. -/
lemma inter_side_extra (d : ℕ) (hd : 2 ≤ d) (k : ℕ) (v : Fin 2 → ℝ) (z : Fin (d - 2) → ℝ)
    (i : Fin d) (hi : ¬ i.val ≤ 1) :
    (interRect d hd k v z).upper i - (interRect d hd k v z).lower i = margin d k := by
  have h0 : i.val ≠ 0 := by omega
  have h1 : i.val ≠ 1 := by omega
  simp only [interRect, h0, h1, dite_false]
  ring

/-- The extra factor `margin ^ (d - 2)` is positive, and equals one when `d = 2`. -/
lemma margin_pow_pos (d k : ℕ) (hd : 2 ≤ d) : 0 < margin d k ^ (d - 2) := by
  by_cases hd2 : d = 2
  · simp [hd2, pow_zero]
  · exact pow_pos (margin_pos d k (by omega)) _

/-- Cancelling the strip index leaves `N` times the squared scale. -/
lemma scale_strip_mul (k j : ℕ) (hj : 0 < j) :
    (stageScale k * (j : ℝ)) * (stageScale k * (stageCount k : ℝ) / (j : ℝ)) =
      stageScale k ^ 2 * (stageCount k : ℝ) := by
  have hj0 : (j : ℝ) ≠ 0 := by exact_mod_cast hj.ne'
  calc
    (stageScale k * (j : ℝ)) * (stageScale k * (stageCount k : ℝ) / (j : ℝ))
        = (stageScale k * (j : ℝ)) *
            (stageScale k * (stageCount k : ℝ) * (j : ℝ)⁻¹) := by rw [div_eq_mul_inv]
    _ = stageScale k * stageScale k * (stageCount k : ℝ) * ((j : ℝ) * (j : ℝ)⁻¹) := by ac_rfl
    _ = stageScale k ^ 2 * (stageCount k : ℝ) := by
          rw [mul_inv_cancel₀ hj0, mul_one, ← pow_two]

/-- Real volume of a witness. -/
lemma volume_real_witness (d : ℕ) (hd : 2 ≤ d) (k : ℕ) (v : Fin 2 → ℝ) (j : ℕ)
    (hj : j ∈ Finset.Icc 2 (stageCount k)) (z : Fin (d - 2) → ℝ) :
    volume.real (witnessRect d hd k v j (Finset.mem_Icc.mp hj).1 z).carrier =
      stageScale k ^ 2 * (stageCount k : ℝ) * margin d k ^ (d - 2) := by
  let R := witnessRect d hd k v j (Finset.mem_Icc.mp hj).1 z
  let p : Fin d → Prop := fun i => i.val ≤ 1
  rw [volume_real_sides R]
  have hsplit := Finset.prod_filter_mul_prod_filter_not Finset.univ p
    (fun i => R.upper i - R.lower i)
  rw [← hsplit]
  let z0 : Fin d := ⟨0, by omega⟩
  let z1 : Fin d := ⟨1, by omega⟩
  have hne : z0 ≠ z1 := by
    intro h
    have := congrArg Fin.val h
    simp [z0, z1] at this
  have hset : Finset.univ.filter p = {z0, z1} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, p]
    constructor
    · intro hi
      rcases (show i.val = 0 ∨ i.val = 1 by omega) with h0 | h1
      · left
        ext
        simp [z0, h0]
      · right
        ext
        simp [z1, h1]
    · intro h
      rcases h with rfl | rfl
      · simp [z0]
      · simp [z1]
  have hplane : ∏ i ∈ Finset.univ.filter p, (R.upper i - R.lower i) =
      (stageScale k * (j : ℝ)) * (stageScale k * (stageCount k : ℝ) / j) := by
    rw [hset, Finset.prod_pair hne]
    rw [witness_side_zero d hd k v j (Finset.mem_Icc.mp hj).1 z z0 (by simp [z0]),
      witness_side_one d hd k v j (Finset.mem_Icc.mp hj).1 z z1 (by simp [z1])]
  have hextra : ∏ i ∈ Finset.univ.filter (fun i => ¬ p i), (R.upper i - R.lower i) =
      margin d k ^ (d - 2) := by
    rw [Finset.prod_congr rfl (fun i hi =>
      witness_side_extra d hd k v j (Finset.mem_Icc.mp hj).1 z i (Finset.mem_filter.mp hi).2)]
    rw [Finset.prod_const, card_extra d hd]
  rw [hplane, hextra, scale_strip_mul k j (by
    exact_mod_cast (show 0 < j by have := (Finset.mem_Icc.mp hj).1; omega))]

/-- Real volume of the spike inside a witness. -/
lemma volume_real_inter (d : ℕ) (hd : 2 ≤ d) (k : ℕ) (v : Fin 2 → ℝ) (z : Fin (d - 2) → ℝ) :
    volume.real (interRect d hd k v z).carrier =
      stageScale k ^ 2 * margin d k ^ (d - 2) := by
  let R := interRect d hd k v z
  let p : Fin d → Prop := fun i => i.val ≤ 1
  rw [volume_real_sides R]
  have hsplit := Finset.prod_filter_mul_prod_filter_not Finset.univ p
    (fun i => R.upper i - R.lower i)
  rw [← hsplit]
  let z0 : Fin d := ⟨0, by omega⟩
  let z1 : Fin d := ⟨1, by omega⟩
  have hne : z0 ≠ z1 := by
    intro h
    have := congrArg Fin.val h
    simp [z0, z1] at this
  have hset : Finset.univ.filter p = {z0, z1} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, p]
    constructor
    · intro hi
      rcases (show i.val = 0 ∨ i.val = 1 by omega) with h0 | h1
      · left
        ext
        simp [z0, h0]
      · right
        ext
        simp [z1, h1]
    · intro h
      rcases h with rfl | rfl
      · simp [z0]
      · simp [z1]
  have hplane : ∏ i ∈ Finset.univ.filter p, (R.upper i - R.lower i) =
      stageScale k * stageScale k := by
    rw [hset, Finset.prod_pair hne]
    rw [inter_side_zero d hd k v z z0 (by simp [z0]),
      inter_side_one d hd k v z z1 (by simp [z1])]
  have hextra : ∏ i ∈ Finset.univ.filter (fun i => ¬ p i), (R.upper i - R.lower i) =
      margin d k ^ (d - 2) := by
    rw [Finset.prod_congr rfl (fun i hi =>
      inter_side_extra d hd k v z i (Finset.mem_filter.mp hi).2)]
    rw [Finset.prod_const, card_extra d hd]
  rw [hplane, hextra, ← pow_two]

/-- The witness meets the spike in the corner rectangle. -/
lemma carrier_inter_eq (d : ℕ) (hd : 2 ≤ d) (k : ℕ) (v : Fin 2 → ℝ) (j : ℕ)
    (hj : j ∈ Finset.Icc 2 (stageCount k)) (z : Fin (d - 2) → ℝ) (hz : z ∈ extraSet d k) :
    (witnessRect d hd k v j (Finset.mem_Icc.mp hj).1 z).carrier ∩
        (spikeRect d hd k v).carrier =
      (interRect d hd k v z).carrier := by
  have hjI := Finset.mem_Icc.mp hj
  have hτ : 0 < stageScale k := stageScale_pos k
  have hτj : stageScale k ≤ stageScale k * (j : ℝ) := by
    have hj2 : (2 : ℝ) ≤ j := by exact_mod_cast hjI.1
    have hj1 : (1 : ℝ) ≤ j := by linarith
    nlinarith
  have hτN : stageScale k ≤ stageScale k * (stageCount k : ℝ) / (j : ℝ) := by
    have hj0 : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
    have hle : (1 : ℝ) ≤ (stageCount k : ℝ) / j := by
      rw [one_le_div hj0]
      exact_mod_cast hjI.2
    calc
      stageScale k = stageScale k * 1 := by rw [mul_one]
      _ ≤ stageScale k * ((stageCount k : ℝ) / j) :=
          mul_le_mul_of_nonneg_left hle hτ.le
      _ = stageScale k * (stageCount k : ℝ) / j := by rw [mul_div_assoc]
  have hzpi : ∀ t : Fin (d - 2),
      margin d k / 2 < z t ∧ z t < 1 - margin d k / 2 := by
    intro t
    rw [extraSet, Set.mem_univ_pi] at hz
    exact Set.mem_Ioo.mp (hz t)
  ext x
  simp only [Set.mem_inter_iff, OpenRectangle.carrier]
  constructor
  · intro hx i
    rcases hx with ⟨hw, hs⟩
    by_cases h0 : i.val = 0
    · have hi : i.val ≤ 1 := by omega
      have hs0 := hs i
      simp only [spikeRect, hi, dite_true] at hs0
      have hv0 : (⟨i.val, Nat.lt_succ_iff.mpr hi⟩ : Fin 2) = 0 := by
        apply Fin.ext
        simp [h0]
      simp only [hv0] at hs0
      simpa only [interRect, h0, dite_true] using hs0
    · by_cases h1 : i.val = 1
      · have hi : i.val ≤ 1 := by omega
        have hs1 := hs i
        simp only [spikeRect, hi, dite_true] at hs1
        have hv1 : (⟨i.val, Nat.lt_succ_iff.mpr hi⟩ : Fin 2) = 1 := by
          apply Fin.ext
          simp [h1]
        simp only [hv1] at hs1
        simp only [interRect]
        rw [dif_neg h0, dif_pos h1, dif_neg h0, dif_pos h1]
        exact hs1
      · have hwE := hw i
        simp only [witnessRect] at hwE
        rw [dif_neg h0, dif_neg h1, dif_neg h0, dif_neg h1] at hwE
        simp only [interRect]
        rw [dif_neg h0, dif_neg h1, dif_neg h0, dif_neg h1]
        exact hwE
  · intro hx
    constructor
    · intro i
      have hxi := hx i
      by_cases h0 : i.val = 0
      · simp only [interRect] at hxi
        rw [dif_pos h0, dif_pos h0] at hxi
        simp only [witnessRect]
        rw [dif_pos h0, dif_pos h0]
        have hle := add_le_add_left hτj (v 0)
        rw [add_comm (stageScale k) (v 0),
          add_comm (stageScale k * (j : ℝ)) (v 0)] at hle
        exact ⟨hxi.1, lt_of_lt_of_le hxi.2 hle⟩
      · by_cases h1 : i.val = 1
        · simp only [interRect] at hxi
          rw [dif_neg h0, dif_pos h1, dif_neg h0, dif_pos h1] at hxi
          simp only [witnessRect]
          rw [dif_neg h0, dif_pos h1, dif_neg h0, dif_pos h1]
          have hle := add_le_add_left hτN (v 1)
          rw [add_comm (stageScale k) (v 1), add_comm
            (stageScale k * (stageCount k : ℝ) / (j : ℝ)) (v 1)] at hle
          exact ⟨hxi.1, lt_of_lt_of_le hxi.2 hle⟩
        · simp only [interRect] at hxi
          rw [dif_neg h0, dif_neg h1, dif_neg h0, dif_neg h1] at hxi
          simp only [witnessRect]
          rw [dif_neg h0, dif_neg h1, dif_neg h0, dif_neg h1]
          exact hxi
    · intro i
      have hxi := hx i
      by_cases h0 : i.val = 0
      · have hi : i.val ≤ 1 := by omega
        simp only [interRect, h0, dite_true] at hxi
        simp only [spikeRect, hi, dite_true]
        have hv0 : (⟨i.val, Nat.lt_succ_iff.mpr hi⟩ : Fin 2) = 0 := by
          apply Fin.ext
          simp [h0]
        simpa only [hv0] using hxi
      · by_cases h1 : i.val = 1
        · have hi : i.val ≤ 1 := by omega
          simp only [interRect] at hxi
          rw [dif_neg h0, dif_pos h1, dif_neg h0, dif_pos h1] at hxi
          simp only [spikeRect, hi, dite_true]
          have hv1 : (⟨i.val, Nat.lt_succ_iff.mpr hi⟩ : Fin 2) = 1 := by
            apply Fin.ext
            simp [h1]
          simpa only [hv1] using hxi
        · have hi : ¬ i.val ≤ 1 := by omega
          simp only [interRect, h0, h1, dite_false] at hxi
          simp only [spikeRect, hi, dite_false]
          have hz' := hzpi ⟨i.val - 2, by have := i.isLt; omega⟩
          constructor <;> linarith

/-- Integral of one spike over its witness. -/
lemma integral_bump_witness (d : ℕ) (hd : 2 ≤ d) (k : ℕ) (v : Fin 2 → ℝ) (j : ℕ)
    (hj : j ∈ Finset.Icc 2 (stageCount k)) (z : Fin (d - 2) → ℝ) (hz : z ∈ extraSet d k) :
    ∫ y in (witnessRect d hd k v j (Finset.mem_Icc.mp hj).1 z).carrier, bump d hd k v y =
      spikeHeight k * volume.real (interRect d hd k v z).carrier := by
  unfold bump
  rw [setIntegral_indicator (spikeRect d hd k v).measurableSet_carrier,
    carrier_inter_eq d hd k v j hj z hz, setIntegral_const, smul_eq_mul, mul_comm]

/-- The spike average on a witness equals the stage height. -/
lemma average_bump_witness (d : ℕ) (hd : 2 ≤ d) (k : ℕ) (v : Fin 2 → ℝ) (j : ℕ)
    (hj : j ∈ Finset.Icc 2 (stageCount k)) (z : Fin (d - 2) → ℝ) (hz : z ∈ extraSet d k) :
    (witnessRect d hd k v j (Finset.mem_Icc.mp hj).1 z).average (bump d hd k v) =
      stageHeight k := by
  let W := witnessRect d hd k v j (Finset.mem_Icc.mp hj).1 z
  let I := interRect d hd k v z
  have hrel : volume.real W.carrier = (stageCount k : ℝ) * volume.real I.carrier := by
    rw [volume_real_witness d hd k v j hj z, volume_real_inter d hd k v z]
    ac_rfl
  have hIpos : 0 < volume.real I.carrier := by
    rw [volume_real_inter d hd k v z]
    exact mul_pos (pow_pos (stageScale_pos k) 2) (margin_pow_pos d k hd)
  have hN : (stageCount k : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.two_pow_pos (stageLog k) : 0 < stageCount k).ne'
  unfold OpenRectangle.average
  rw [← measureReal_def, integral_bump_witness d hd k v j hj z hz, hrel]
  calc
    ((stageCount k : ℝ) * volume.real I.carrier)⁻¹ *
          (spikeHeight k * volume.real I.carrier)
        = (stageCount k : ℝ)⁻¹ * (volume.real I.carrier)⁻¹ *
            (spikeHeight k * volume.real I.carrier) := by rw [mul_inv]
    _ = (stageCount k : ℝ)⁻¹ * spikeHeight k *
          ((volume.real I.carrier)⁻¹ * volume.real I.carrier) := by ac_rfl
    _ = (stageCount k : ℝ)⁻¹ * spikeHeight k := by
          rw [inv_mul_cancel₀ hIpos.ne', mul_one]
    _ = spikeHeight k / (stageCount k : ℝ) := by rw [mul_comm, ← div_eq_mul_inv]
    _ = stageHeight k := by
          rw [spikeHeight, mul_div_cancel_right₀ _ hN]

/-- On a stage set the Saks average over some narrow witness is at least the stage height. -/
lemma exists_stage_rectangle (d : ℕ) (hd : 2 ≤ d) (k : ℕ) (x : Fin d → ℝ)
    (hx : x ∈ stageSet d k hd) :
    ∃ R : OpenRectangle d, x ∈ R.carrier ∧ R.totalWidth ≤ (1 / 2 : ℝ) ^ (k + 1) ∧
      stageHeight k ≤ R.average (saks d hd) := by
  rw [stageSet, Set.mem_preimage, Set.mem_prod] at hx
  rcases hx with ⟨hy, hz⟩
  rw [planeCover, Set.mem_inter_iff, Set.mem_iUnion] at hy
  rcases hy with ⟨_, i, hyi⟩
  have hv : (splitEquiv d hd x).1 - chosenShifts k i ∈ badPlane k := hyi
  simp only [badPlane, Set.mem_iUnion] at hv
  rcases hv with ⟨j, hj, hjmem⟩
  have hj2 : 2 ≤ j := (Finset.mem_Icc.mp hj).1
  rw [stripCarrier_of_mem k j hj] at hjmem
  let v := chosenShifts k i
  let y := (splitEquiv d hd x).1
  let z := (splitEquiv d hd x).2
  let R := witnessRect d hd k v j hj2 z
  have hy0 : y 0 = x ⟨0, by omega⟩ := by
    change (splitEquiv d hd x).1 0 = x ⟨0, by omega⟩
    rw [splitEquiv_fst]
    congr 1
  have hy1 : y 1 = x ⟨1, by omega⟩ := by
    change (splitEquiv d hd x).1 1 = x ⟨1, by omega⟩
    rw [splitEquiv_fst]
    congr 1
  have hmem0 := hjmem 0
  have hmem1 := hjmem 1
  simp only [stripRect, Pi.sub_apply] at hmem0 hmem1
  rw [ite_eq_left trivial, ite_eq_left trivial] at hmem0
  rw [ite_eq_right (show (1 : Fin 2) ≠ 0 by decide),
    ite_eq_right (show (1 : Fin 2) ≠ 0 by decide)] at hmem1
  refine ⟨R, ?_, witness_totalWidth_le d hd k v j hj z, ?_⟩
  · intro t
    dsimp only [R, witnessRect]
    by_cases h0 : t.val = 0
    · rw [dite_eq_left h0, dite_eq_left h0]
      have ht : t = ⟨0, by omega⟩ := by ext; exact h0
      rw [ht]
      have hlow := hmem0.1
      have hup := hmem0.2
      rw [show (splitEquiv d hd x).1 0 = y 0 from rfl,
        show chosenShifts k i 0 = v 0 from rfl, hy0] at hlow
      rw [show (splitEquiv d hd x).1 0 = y 0 from rfl,
        show chosenShifts k i 0 = v 0 from rfl, hy0] at hup
      have hsub : (0 : ℝ) ≤ (j : ℝ) - 1 := by
        have h2 : (2 : ℝ) ≤ j := by exact_mod_cast hj2
        linarith
      constructor
      · linarith [mul_nonneg (stageScale_pos k).le hsub]
      · linarith
    · by_cases h1 : t.val = 1
      · rw [dite_eq_right h0, dite_eq_left h1, dite_eq_right h0, dite_eq_left h1]
        have ht : t = ⟨1, by omega⟩ := by ext; exact h1
        rw [ht]
        constructor
        · have hlow := hmem1.1
          rw [show (splitEquiv d hd x).1 1 = y 1 from rfl,
            show chosenShifts k i 1 = v 1 from rfl, hy1] at hlow
          linarith
        · have hup := hmem1.2
          rw [show (splitEquiv d hd x).1 1 = y 1 from rfl,
            show chosenShifts k i 1 = v 1 from rfl, hy1] at hup
          linarith
      · have hlt : t.val - 2 < d - 2 := by have := t.isLt; omega
        have htE : (splitEquiv d hd x).2 ⟨t.val - 2, hlt⟩ = x t := by
          rw [splitEquiv_snd]
          congr 1
          apply Fin.ext
          simp [extraEquiv]
          omega
        rw [dite_eq_right h0, dite_eq_right h1, dite_eq_right h0, dite_eq_right h1]
        rw [← htE]
        have hm : 0 < margin d k := margin_pos d k (by have := t.isLt; omega)
        constructor <;> linarith
  · have hae : bump d hd k v ≤ᵐ[volume] saks d hd := by
      filter_upwards [ae_lt_top (measurable_raw d hd) (lintegral_raw_ne_top d hd)] with w hw
      exact bump_le_saks d hd k i w (lt_top_iff_ne_top.mp hw)
    have hmono : ∫ w in R.carrier, bump d hd k v w ≤ ∫ w in R.carrier, saks d hd w :=
      setIntegral_mono_ae (integrable_bump d hd k v).integrableOn
        (integrable_saks d hd).integrableOn hae
    have havgB : R.average (bump d hd k v) = stageHeight k :=
      average_bump_witness d hd k v j hj z hz
    have hge : R.average (bump d hd k v) ≤ R.average (saks d hd) := by
      unfold OpenRectangle.average
      exact mul_le_mul_of_nonneg_left hmono
        (inv_nonneg.mpr ENNReal.toReal_nonneg)
    rw [havgB] at hge
    exact hge

/-- Rectangular differentiation fails at every point of the stage limsup. -/
lemma not_rectanglesDifferentiateAt_on_limsup (d : ℕ) (hd : 2 ≤ d) {x : Fin d → ℝ}
    (hx : x ∈ limsupSet d hd) : ¬ RectanglesDifferentiateAt (saks d hd) x := by
  intro hdiff
  obtain ⟨δ, hδpos, hδ⟩ := hdiff 1 (by norm_num : (0 : ℝ) < 1)
  obtain ⟨n0, hn0⟩ := exists_nat_gt (saks d hd x)
  obtain ⟨n1, hn1⟩ := exists_pow_lt_of_lt_one hδpos (by norm_num : (1 / 2 : ℝ) < 1)
  have hxT : x ∈ tailSet d (Nat.max n0 n1) hd := by
    rw [limsupSet, Set.mem_iInter] at hx
    exact hx (Nat.max n0 n1)
  simp only [tailSet, Set.mem_iUnion, Set.mem_Ici] at hxT
  rcases hxT with ⟨k, hk, hxk⟩
  obtain ⟨R, hxR, hwidth, havg⟩ := exists_stage_rectangle d hd k x hxk
  have hpow : (1 / 2 : ℝ) ^ (k + 1) < δ := by
    refine lt_of_le_of_lt ?_ hn1
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num)
      (show n1 ≤ k + 1 by
        have hn1k : n1 ≤ Nat.max n0 n1 := Nat.le_max_right _ _
        omega)
  have hH : saks d hd x + 1 < stageHeight k := by
    unfold stageHeight
    have hn0k : (n0 : ℝ) ≤ k := by
      exact_mod_cast (Nat.le_max_left n0 n1).trans hk
    linarith
  have hδR : R.totalWidth < δ := lt_of_le_of_lt hwidth hpow
  have habs : 1 < |R.average (saks d hd) - saks d hd x| := by
    have hpos : 0 < R.average (saks d hd) - saks d hd x := by linarith
    rw [abs_of_pos hpos]
    linarith
  linarith [habs, hδ R hxR hδR]

/-- In dimension at least two the strong basis does not differentiate `L¹`. -/
theorem exists_integrable_not_rectangularlyDifferentiable {d : ℕ} (hd : 2 ≤ d) :
    ∃ f : (Fin d → ℝ) → ℝ, Measurable f ∧ Integrable f volume ∧
      0 < volume {x | ¬ RectanglesDifferentiateAt f x} := by
  refine ⟨saks d hd, measurable_saks d hd, integrable_saks d hd, ?_⟩
  have hsub : limsupSet d hd ⊆ {x | ¬ RectanglesDifferentiateAt (saks d hd) x} :=
    fun _ hx => not_rectanglesDifferentiateAt_on_limsup d hd hx
  exact (ENNReal.ofReal_pos.mpr (by norm_num : (0 : ℝ) < 3 / 32)).trans_le
    ((volume_limsupSet_ge d hd).trans (measure_mono hsub))

end CKMA.Bohr
