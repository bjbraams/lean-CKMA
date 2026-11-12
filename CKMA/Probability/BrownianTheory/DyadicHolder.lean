/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Field.GeomSum
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.PadicValNat

/-!
# Dyadic chaining on the unit interval

A greedy decomposition writes an integer gap as a sum of powers of two, with each power
appearing at most twice. Summing the corresponding increments gives the Hölder estimate on the
dyadic grid of `[0, 1]`.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Finset

/-- Largest power of two not exceeding `m`, with the value `0` at `m = 0`. -/
def largestPowerOfTwoLe (m : ℕ) : ℕ :=
  if m = 0 then 0 else 2 ^ m.log2

/-- The positive largest power of two below `m` is `2 ^ log2 m`. -/
lemma largestPowerOfTwoLe_of_pos {m : ℕ} (hm : 0 < m) :
    largestPowerOfTwoLe m = 2 ^ m.log2 := by
  simp [largestPowerOfTwoLe, hm.ne']

/-- `largestPowerOfTwoLe m` does not exceed `m`. -/
lemma largestPowerOfTwoLe_le (m : ℕ) : largestPowerOfTwoLe m ≤ m := by
  by_cases hm : m = 0
  · simp [largestPowerOfTwoLe, hm]
  · have h := (Nat.log2_eq_iff hm).mp rfl
    simpa [largestPowerOfTwoLe, hm] using h.1

/-- A positive integer is strictly less than twice its largest power of two. -/
lemma lt_two_mul_largestPowerOfTwoLe {m : ℕ} (hm : 0 < m) :
    m < 2 * largestPowerOfTwoLe m := by
  have h := (Nat.log2_eq_iff hm.ne').mp rfl
  simpa [largestPowerOfTwoLe, hm.ne', pow_succ, Nat.mul_comm] using h.2

/-- Highest power of two dividing `a`, with the value `0` at `a = 0`. -/
def twoAdicPow (a : ℕ) : ℕ :=
  if a = 0 then 0 else 2 ^ padicValNat 2 a

/-- The highest power of two dividing a positive integer divides that integer. -/
lemma twoAdicPow_dvd {a : ℕ} (ha : a ≠ 0) : twoAdicPow a ∣ a := by
  simpa [twoAdicPow, ha] using pow_padicValNat_dvd (p := 2) (n := a)

/-- The highest power of two dividing a positive integer is itself a power of two. -/
lemma twoAdicPow_eq_pow {a : ℕ} (ha : a ≠ 0) :
    twoAdicPow a = 2 ^ padicValNat 2 a := by
  simp [twoAdicPow, ha]

/-- The minimum of two powers of two is the power for the smaller exponent. -/
lemma min_two_pow (k l : ℕ) : min (2 ^ k) (2 ^ l) = 2 ^ min k l := by
  rcases le_total k l with h | h
  · rw [min_eq_left h, min_eq_left (Nat.pow_le_pow_right (by decide) h)]
  · rw [min_eq_right h, min_eq_right (Nat.pow_le_pow_right (by decide) h)]

/-- One greedy step from `a` toward `b`: the largest aligned power of two that fits. -/
def greedyStep (a b : ℕ) : ℕ :=
  let maxPow := largestPowerOfTwoLe (b - a)
  if a = 0 then maxPow else min (twoAdicPow a) maxPow

/-- A greedy step across a positive gap is a positive power of two. -/
lemma greedyStep_eq_pow {a b : ℕ} (h : a < b) : ∃ k, greedyStep a b = 2 ^ k := by
  have hpos : 0 < b - a := by omega
  by_cases ha : a = 0
  · refine ⟨b.log2, ?_⟩
    have hb : 0 < b := by omega
    simp only [greedyStep, ha, Nat.sub_zero]
    exact largestPowerOfTwoLe_of_pos hb
  · refine ⟨min (padicValNat 2 a) ((b - a).log2), ?_⟩
    simp [greedyStep, ha, twoAdicPow_eq_pow ha, largestPowerOfTwoLe_of_pos hpos, min_two_pow]

/-- A greedy step does not exceed the remaining gap. -/
lemma greedyStep_le {a b : ℕ} (_h : a < b) : greedyStep a b ≤ b - a := by
  have hmax := largestPowerOfTwoLe_le (b - a)
  by_cases ha : a = 0
  · simpa [greedyStep, ha] using hmax
  · simpa [greedyStep, ha] using
      (min_le_right (twoAdicPow a) (largestPowerOfTwoLe (b - a))).trans hmax

/-- A greedy step is strictly positive when the gap is positive. -/
lemma greedyStep_pos {a b : ℕ} (h : a < b) : 0 < greedyStep a b := by
  obtain ⟨k, hk⟩ := greedyStep_eq_pow h
  rw [hk]
  exact Nat.two_pow_pos k

/-- A greedy step divides the starting point. -/
lemma greedyStep_dvd {a b : ℕ} (h : a < b) : greedyStep a b ∣ a := by
  by_cases ha : a = 0
  · simp [ha]
  · have hpos : 0 < b - a := by omega
    have hstep : greedyStep a b =
        min (2 ^ padicValNat 2 a) (2 ^ (b - a).log2) := by
      simp [greedyStep, ha, twoAdicPow_eq_pow ha, largestPowerOfTwoLe_of_pos hpos]
    have hpow : 2 ^ padicValNat 2 a ∣ a := by
      simpa [twoAdicPow_eq_pow ha] using twoAdicPow_dvd ha
    rw [hstep, min_two_pow]
    exact (Nat.pow_dvd_pow 2 (Nat.min_le_left _ _)).trans hpow

/-- If the greedy step is the largest power fitting in the gap, the remainder is smaller. -/
lemma remaining_lt_of_eq_largest {a b : ℕ} (h : a < b)
    (hs : greedyStep a b = largestPowerOfTwoLe (b - a)) :
    b - (a + greedyStep a b) < greedyStep a b := by
  have hm : 0 < b - a := by omega
  have hlt := lt_two_mul_largestPowerOfTwoLe hm
  have hsle := greedyStep_le h
  omega

/-- Adding the exact power of two dividing `a` raises the 2-adic valuation by one. -/
lemma two_pow_succ_dvd_add {a q : ℕ} (ha : a ≠ 0) (hq : padicValNat 2 a = q) :
    2 ^ (q + 1) ∣ a + 2 ^ q := by
  have hdvd : 2 ^ q ∣ a :=
    (Nat.pow_dvd_iff_le_padicValNat (by decide) ha).mpr (by omega)
  obtain ⟨m, hm⟩ := hdvd
  have hnot : ¬ 2 ^ (q + 1) ∣ a := by
    intro h
    have := (Nat.pow_dvd_iff_le_padicValNat (by decide) ha).mp h
    omega
  have hodd : ¬ 2 ∣ m := by
    intro h2
    obtain ⟨k, hk⟩ := h2
    apply hnot
    rw [hm, hk, ← Nat.mul_assoc, ← pow_succ]
    exact dvd_mul_right _ _
  rw [hm]
  have hadd : 2 ^ q * m + 2 ^ q = 2 ^ q * (m + 1) := by
    calc
      2 ^ q * m + 2 ^ q = 2 ^ q * m + 2 ^ q * 1 := by rw [Nat.mul_one]
      _ = 2 ^ q * (m + 1) := by rw [← Nat.mul_add]
  rw [hadd]
  refine Nat.mul_dvd_mul_left _ ?_
  have hmod : m % 2 = 1 := by
    rcases Nat.mod_two_eq_zero_or_one m with h0 | h1
    · exact absurd (Nat.dvd_iff_mod_eq_zero.mpr h0) hodd
    · exact h1
  rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, hmod]

/-- Greedy jumps from `a` toward `b`, with an explicit fuel bound. -/
def greedyJumpsAux : ℕ → ℕ → ℕ → List ℕ
  | 0, _, _ => []
  | fuel + 1, a, b =>
    if a < b then
      greedyStep a b :: greedyJumpsAux fuel (a + greedyStep a b) b
    else
      []

/-- Extra fuel does not change the greedy jump list once the fuel meets the gap. -/
lemma greedyJumpsAux_eq (fuel fuel' a b : ℕ) (hf : b - a ≤ fuel) (hf' : b - a ≤ fuel') :
    greedyJumpsAux fuel a b = greedyJumpsAux fuel' a b := by
  induction fuel generalizing fuel' a b with
  | zero =>
      have hb : b ≤ a := by omega
      cases fuel' with
      | zero => rfl
      | succ fuel' => simp [greedyJumpsAux, hb]
  | succ fuel ih =>
      cases fuel' with
      | zero =>
          have hb : b ≤ a := by omega
          simp [greedyJumpsAux, hb]
      | succ fuel' =>
          by_cases hlt : a < b
          · simp only [greedyJumpsAux, hlt, ↓reduceIte]
            congr 1
            apply ih
            · have hpos := greedyStep_pos hlt
              have hle := greedyStep_le hlt
              omega
            · have hpos := greedyStep_pos hlt
              have hle := greedyStep_le hlt
              omega
          · simp [greedyJumpsAux, hlt]

/-- Greedy decomposition of the gap from `a` to `b` into powers of two. -/
def greedyJumps (a b : ℕ) : List ℕ :=
  greedyJumpsAux (b - a) a b

/-- There are no greedy jumps when the endpoint is at most the start. -/
lemma greedyJumps_of_le {a b : ℕ} (h : b ≤ a) : greedyJumps a b = [] := by
  simp [greedyJumps, Nat.sub_eq_zero_of_le h, greedyJumpsAux]

/-- A positive gap starts with one greedy step and continues on the remainder. -/
lemma greedyJumps_cons {a b : ℕ} (h : a < b) :
    greedyJumps a b =
      greedyStep a b :: greedyJumps (a + greedyStep a b) b := by
  have hpos := greedyStep_pos h
  have hle := greedyStep_le h
  have hfuel : b - a = (b - a - 1) + 1 := by omega
  unfold greedyJumps
  rw [hfuel]
  simp only [greedyJumpsAux, h, ↓reduceIte]
  congr 1
  symm
  apply greedyJumpsAux_eq
  · omega
  · omega

/-- The greedy jumps of a fixed gap sum to that gap. -/
lemma sum_greedyJumps_of_dist (d : ℕ) :
    ∀ a b, b - a = d → (greedyJumps a b).sum = d := by
  refine Nat.strongRecOn d fun d ih a b hd => ?_
  by_cases hlt : a < b
  · rw [greedyJumps_cons hlt, List.sum_cons]
    have hpos := greedyStep_pos hlt
    have hle := greedyStep_le hlt
    have hdlt : b - (a + greedyStep a b) < d := by omega
    have hsum := ih (b - (a + greedyStep a b)) hdlt (a + greedyStep a b) b rfl
    omega
  · have hba : b ≤ a := Nat.le_of_not_lt hlt
    rw [greedyJumps_of_le hba, List.sum_nil]
    omega

/-- The greedy jumps sum to the gap. -/
lemma sum_greedyJumps (a b : ℕ) : (greedyJumps a b).sum = b - a :=
  sum_greedyJumps_of_dist (b - a) a b rfl

/-- Every greedy jump of a fixed gap is a positive power of two no larger than the gap. -/
lemma mem_greedyJumps_of_dist (d : ℕ) :
    ∀ a b s, b - a = d → s ∈ greedyJumps a b →
      0 < s ∧ s ≤ d ∧ ∃ k, s = 2 ^ k := by
  refine Nat.strongRecOn d fun d ih a b s hd hs => ?_
  by_cases hlt : a < b
  · rw [greedyJumps_cons hlt] at hs
    have hpos := greedyStep_pos hlt
    have hle := greedyStep_le hlt
    rcases List.mem_cons.mp hs with rfl | hrest
    · exact ⟨hpos, by omega, greedyStep_eq_pow hlt⟩
    · have hdlt : b - (a + greedyStep a b) < d := by omega
      have hmem := ih (b - (a + greedyStep a b)) hdlt
        (a + greedyStep a b) b s rfl hrest
      have hle_d : s ≤ d := by
        have h1 : s ≤ b - (a + greedyStep a b) := hmem.2.1
        omega
      exact ⟨hmem.1, hle_d, hmem.2.2⟩
  · have hba : b ≤ a := Nat.le_of_not_lt hlt
    simp [greedyJumps_of_le hba] at hs

/-- Every greedy jump is a positive power of two no larger than the gap. -/
lemma mem_greedyJumps {a b s : ℕ} (hs : s ∈ greedyJumps a b) :
    0 < s ∧ s ≤ b - a ∧ ∃ k, s = 2 ^ k :=
  mem_greedyJumps_of_dist (b - a) a b s rfl hs

/-- A list of integers strictly below `2 ^ q` does not contain `2 ^ q`. -/
lemma count_eq_zero_of_lt {l : List ℕ} {q : ℕ} (h : ∀ s ∈ l, s < 2 ^ q) :
    l.count (2 ^ q) = 0 := by
  induction l with
  | nil => simp
  | cons s ls ih =>
      have hs : s ≠ 2 ^ q := by
        have hlt := h s (by simp)
        omega
      rw [List.count_cons_of_ne hs]
      exact ih fun t ht => h t (by simp [ht])

/-- A short aligned step is the largest power of two that fits in the gap. -/
lemma greedyStep_eq_largest_of_le_exp {a b r q : ℕ} (h : a < b)
    (hdiv : 2 ^ (q + 1) ∣ a) (hr : r ≤ q) (hs : greedyStep a b = 2 ^ r) :
    greedyStep a b = largestPowerOfTwoLe (b - a) := by
  by_cases ha : a = 0
  · simp [greedyStep, ha]
  · have hpos : 0 < b - a := by omega
    have hv : q + 1 ≤ padicValNat 2 a :=
      (Nat.pow_dvd_iff_le_padicValNat (by decide) ha).mp hdiv
    have hsdef : greedyStep a b =
        min (2 ^ padicValNat 2 a) (2 ^ (b - a).log2) := by
      simp [greedyStep, ha, twoAdicPow_eq_pow ha, largestPowerOfTwoLe_of_pos hpos]
    have hs0 : greedyStep a b = 2 ^ r := hs
    rw [hsdef, min_two_pow] at hs
    have hinj := Nat.pow_right_injective (by decide : 1 < 2) hs
    have hnot : ¬ padicValNat 2 a ≤ (b - a).log2 := by
      intro hle
      have : min (padicValNat 2 a) (b - a).log2 = padicValNat 2 a := min_eq_left hle
      omega
    have hlog : (b - a).log2 ≤ padicValNat 2 a := le_of_not_ge hnot
    have hmin : min (padicValNat 2 a) (b - a).log2 = (b - a).log2 := min_eq_right hlog
    have hlogeq : (b - a).log2 = r := by omega
    rw [largestPowerOfTwoLe_of_pos hpos, hlogeq]
    exact hs0

/-- Each power of two occurs at most twice, and at most once after a stronger alignment. -/
lemma count_greedyJumps_bounds (d : ℕ) :
    (∀ a b q, b - a = d → (greedyJumps a b).count (2 ^ q) ≤ 2) ∧
    (∀ a b q, b - a = d → 2 ^ (q + 1) ∣ a →
      (greedyJumps a b).count (2 ^ q) ≤ 1) := by
  refine Nat.strongRecOn d fun d ih => ?_
  refine ⟨fun a b q hd => ?_, fun a b q hd hdiv => ?_⟩
  · by_cases hlt : a < b
    · have hpos := greedyStep_pos hlt
      have hle := greedyStep_le hlt
      obtain ⟨r, hr⟩ := greedyStep_eq_pow hlt
      have hdlt : b - (a + greedyStep a b) < d := by omega
      have hrest2 := (ih (b - (a + greedyStep a b)) hdlt).1
        (a + greedyStep a b) b q rfl
      rw [greedyJumps_cons hlt]
      by_cases heq : greedyStep a b = 2 ^ q
      · rw [heq, List.count_cons_self]
        have hrest1 : (greedyJumps (a + greedyStep a b) b).count (2 ^ q) ≤ 1 := by
          by_cases hdiva : 2 ^ (q + 1) ∣ a
          · have hrq : r ≤ q := by
              have hpow : 2 ^ r = 2 ^ q := by rw [← hr, heq]
              have hrq' : r = q := Nat.pow_right_injective (by decide : 1 < 2) hpow
              omega
            have hmax := greedyStep_eq_largest_of_le_exp hlt hdiva hrq hr
            have hrem := remaining_lt_of_eq_largest hlt hmax
            have hsmall : ∀ t ∈ greedyJumps (a + greedyStep a b) b, t < 2 ^ q := by
              intro t ht
              have htle : t ≤ b - (a + greedyStep a b) := (mem_greedyJumps ht).2.1
              omega
            simp [count_eq_zero_of_lt hsmall]
          · have ha : a ≠ 0 := by
              intro ha0
              exact hdiva (by simp [ha0])
            have hdvdq : 2 ^ q ∣ a := by
              rw [← heq]
              exact greedyStep_dvd hlt
            have hv : padicValNat 2 a = q := by
              have hlev := (Nat.pow_dvd_iff_le_padicValNat (by decide) ha).mp hdvdq
              have hnot : ¬ q + 1 ≤ padicValNat 2 a := by
                intro h
                exact hdiva ((Nat.pow_dvd_iff_le_padicValNat (by decide) ha).mpr h)
              omega
            have hnext : 2 ^ (q + 1) ∣ a + greedyStep a b := by
              rw [heq]
              exact two_pow_succ_dvd_add ha hv
            exact (ih (b - (a + greedyStep a b)) hdlt).2
              (a + greedyStep a b) b q rfl hnext
        rw [heq] at hrest1
        omega
      · rw [List.count_cons_of_ne heq]
        exact hrest2
    · have hba : b ≤ a := Nat.le_of_not_lt hlt
      simp [greedyJumps_of_le hba]
  · by_cases hlt : a < b
    · have hpos := greedyStep_pos hlt
      have hle := greedyStep_le hlt
      obtain ⟨r, hr⟩ := greedyStep_eq_pow hlt
      have hdlt : b - (a + greedyStep a b) < d := by omega
      rw [greedyJumps_cons hlt]
      by_cases hrq : r ≤ q
      · have hmax := greedyStep_eq_largest_of_le_exp hlt hdiv hrq hr
        have hrem := remaining_lt_of_eq_largest hlt hmax
        have hstepLe : greedyStep a b ≤ 2 ^ q := by
          rw [hr]
          exact Nat.pow_le_pow_right (by decide) hrq
        have hsmall : ∀ t ∈ greedyJumps (a + greedyStep a b) b, t < 2 ^ q := by
          intro t ht
          have htle : t ≤ b - (a + greedyStep a b) := (mem_greedyJumps ht).2.1
          omega
        have hzero := count_eq_zero_of_lt hsmall
        by_cases heq : greedyStep a b = 2 ^ q
        · have hzero' : (greedyJumps (a + 2 ^ q) b).count (2 ^ q) = 0 := by
            simpa [heq] using hzero
          rw [heq, List.count_cons_self, hzero']
        · rw [List.count_cons_of_ne heq, hzero]
          simp
      · have hr' : q + 1 ≤ r := by omega
        have hdvdStep : 2 ^ (q + 1) ∣ greedyStep a b := by
          rw [hr]
          exact Nat.pow_dvd_pow 2 hr'
        have hnext : 2 ^ (q + 1) ∣ a + greedyStep a b := dvd_add hdiv hdvdStep
        have hrest := (ih (b - (a + greedyStep a b)) hdlt).2
          (a + greedyStep a b) b q rfl hnext
        have hne : greedyStep a b ≠ 2 ^ q := by
          rw [hr]
          intro hpow
          have := Nat.pow_right_injective (by decide : 1 < 2) hpow
          omega
        rw [List.count_cons_of_ne hne]
        exact hrest
    · have hba : b ≤ a := Nat.le_of_not_lt hlt
      simp [greedyJumps_of_le hba]

/-- Each power of two occurs at most twice in a greedy decomposition. -/
lemma count_greedyJumps_le_two (a b q : ℕ) : (greedyJumps a b).count (2 ^ q) ≤ 2 :=
  (count_greedyJumps_bounds (b - a)).1 a b q rfl

/-- Constant in the unit-interval dyadic Hölder estimate. -/
def dyadicHolderFactor (α : ℝ) : ℝ :=
  2 / (1 - (2 : ℝ) ^ (-α))

/-- The dyadic Hölder factor is positive for a positive exponent. -/
lemma dyadicHolderFactor_pos {α : ℝ} (hα : 0 < α) : 0 < dyadicHolderFactor α := by
  have h2 : (1 : ℝ) < 2 := by norm_num
  have hpow : (2 : ℝ) ^ (-α) < 1 := by
    rw [Real.rpow_neg (by positivity)]
    exact inv_lt_one_of_one_lt₀ (Real.one_lt_rpow h2 hα)
  have hden : 0 < 1 - (2 : ℝ) ^ (-α) := sub_pos.mpr hpow
  exact div_pos (by norm_num) hden

/-- Rewrite the denominator of the Hölder factor through `2 ^ α`. -/
lemma one_sub_two_rpow_neg {α : ℝ} (_hα : 0 < α) :
    1 - (2 : ℝ) ^ (-α) = ((2 : ℝ) ^ α - 1) / (2 : ℝ) ^ α := by
  rw [Real.rpow_neg (by positivity)]
  field_simp

/-- The Hölder factor equals `2 * 2 ^ α / (2 ^ α - 1)`. -/
lemma dyadicHolderFactor_eq {α : ℝ} (hα : 0 < α) :
    dyadicHolderFactor α = 2 * (2 : ℝ) ^ α / ((2 : ℝ) ^ α - 1) := by
  unfold dyadicHolderFactor
  rw [one_sub_two_rpow_neg hα]
  field_simp

/-- A natural power of two, raised to `α`, is the geometric term `(2 ^ α) ^ q`. -/
lemma two_pow_rpow_eq {α : ℝ} (_hα : 0 < α) (q : ℕ) :
    ((2 : ℝ) ^ q) ^ α = ((2 : ℝ) ^ α) ^ q := by
  have h2 : (0 : ℝ) ≤ 2 := by positivity
  calc
    ((2 : ℝ) ^ q) ^ α = ((2 : ℝ) ^ (q : ℝ)) ^ α := by
      rw [← Real.rpow_natCast 2 q]
    _ = (2 : ℝ) ^ ((q : ℝ) * α) := by rw [Real.rpow_mul h2]
    _ = (2 : ℝ) ^ (α * (q : ℝ)) := by ring_nf
    _ = ((2 : ℝ) ^ α) ^ (q : ℝ) := by rw [← Real.rpow_mul h2]
    _ = ((2 : ℝ) ^ α) ^ q := by rw [Real.rpow_natCast ((2 : ℝ) ^ α) q]

/-- Twice the geometric sum of `2 ^ (q α)` is at most the Hölder factor times `(2 ^ m) ^ α`. -/
lemma two_mul_geom_le {α : ℝ} {m : ℕ} (hα : 0 < α) :
    2 * ∑ q ∈ Finset.range (m + 1), ((2 : ℝ) ^ q) ^ α ≤
      dyadicHolderFactor α * ((2 : ℝ) ^ m) ^ α := by
  set x : ℝ := (2 : ℝ) ^ α
  have h2 : (1 : ℝ) < 2 := by norm_num
  have hx1 : 1 < x := Real.one_lt_rpow h2 hα
  have hxne : x ≠ 1 := ne_of_gt hx1
  have hxpos : 0 < x - 1 := by linarith
  simp_rw [two_pow_rpow_eq hα]
  have hgeom : ∑ q ∈ Finset.range (m + 1), x ^ q = (x ^ (m + 1) - 1) / (x - 1) :=
    geom_sum_eq hxne (m + 1)
  rw [hgeom]
  have hle : 2 * ((x ^ (m + 1) - 1) / (x - 1)) ≤ 2 * (x ^ (m + 1) / (x - 1)) := by
    gcongr
    linarith
  refine hle.trans ?_
  have hmul : x ^ (m + 1) = x * x ^ m := by ring
  rw [hmul]
  have hxm : x ^ m = ((2 : ℝ) ^ m) ^ α := by
    simpa [x] using (two_pow_rpow_eq hα m).symm
  rw [hxm, dyadicHolderFactor_eq hα]
  have hxdef : x = (2 : ℝ) ^ α := rfl
  rw [hxdef]
  field_simp
  rfl

/-- Absolute powers of a list of pure powers of two expand through their counts. -/
lemma sum_map_rpow_eq_count (l : List ℕ) (m : ℕ) (α : ℝ)
    (hmem : ∀ s ∈ l, ∃ k ≤ m, s = 2 ^ k) :
    (l.map (fun s : ℕ => (s : ℝ) ^ α)).sum =
      ∑ q ∈ Finset.range (m + 1), (l.count (2 ^ q) : ℝ) * ((2 : ℝ) ^ q) ^ α := by
  induction l with
  | nil => simp
  | cons s ls ih =>
      obtain ⟨k, hk, rfl⟩ := hmem s (by simp)
      have hls : ∀ t ∈ ls, ∃ k ≤ m, t = 2 ^ k :=
        fun t ht => hmem t (List.mem_cons_of_mem _ ht)
      rw [List.map_cons, List.sum_cons, ih hls]
      have hmemk : k ∈ Finset.range (m + 1) := by
        rw [Finset.mem_range]
        omega
      have hsplit : ∑ q ∈ Finset.range (m + 1),
          (((2 ^ k) :: ls).count (2 ^ q) : ℝ) * ((2 : ℝ) ^ q) ^ α =
          ∑ q ∈ Finset.range (m + 1), (ls.count (2 ^ q) : ℝ) * ((2 : ℝ) ^ q) ^ α +
            ((2 : ℝ) ^ k) ^ α := by
        have hfun : ∀ q ∈ Finset.range (m + 1),
            (((2 ^ k) :: ls).count (2 ^ q) : ℝ) * ((2 : ℝ) ^ q) ^ α =
              (ls.count (2 ^ q) : ℝ) * ((2 : ℝ) ^ q) ^ α +
                (if q = k then ((2 : ℝ) ^ q) ^ α else 0) := by
          intro q hq
          by_cases hqk : q = k
          · simp [hqk, List.count_cons_self, add_mul]
          · have hne : 2 ^ k ≠ 2 ^ q := by
              intro h
              exact hqk (Nat.pow_right_injective (by decide : 1 < 2) h.symm)
            simp [hqk, List.count_cons_of_ne hne]
        rw [Finset.sum_congr rfl hfun, Finset.sum_add_distrib]
        congr 1
        rw [Finset.sum_ite_eq' (Finset.range (m + 1)) k (fun q => ((2 : ℝ) ^ q) ^ α)]
        simp [hmemk]
      have hcast : ((2 ^ k : ℕ) : ℝ) ^ α = ((2 : ℝ) ^ k) ^ α := by
        simp [Nat.cast_pow]
      rw [hcast, hsplit]
      ring

/-- A list of powers of two, each appearing at most twice, has `α`-sum at most the Hölder bound. -/
lemma sum_rpow_le {l : List ℕ} {δ : ℕ} {α : ℝ} (hα : 0 < α) (hδ : 0 < δ)
    (hmem : ∀ s ∈ l, ∃ k, s = 2 ^ k ∧ k ≤ Nat.log2 δ)
    (hcount : ∀ q, l.count (2 ^ q) ≤ 2) :
    (l.map (fun s : ℕ => (s : ℝ) ^ α)).sum ≤
      dyadicHolderFactor α * (δ : ℝ) ^ α := by
  let m := Nat.log2 δ
  have hmem' : ∀ s ∈ l, ∃ k ≤ m, s = 2 ^ k := by
    intro s hs
    obtain ⟨k, hk, hkle⟩ := hmem s hs
    exact ⟨k, hkle, hk⟩
  rw [sum_map_rpow_eq_count l m α hmem']
  have hrpow : ∀ q ∈ Finset.range (m + 1), 0 ≤ ((2 : ℝ) ^ q) ^ α := by
    intro q hq
    exact Real.rpow_nonneg (by positivity) _
  have hle : ∑ q ∈ Finset.range (m + 1), (l.count (2 ^ q) : ℝ) * ((2 : ℝ) ^ q) ^ α ≤
      ∑ q ∈ Finset.range (m + 1), 2 * ((2 : ℝ) ^ q) ^ α := by
    refine Finset.sum_le_sum fun q hq => ?_
    have hc : (l.count (2 ^ q) : ℝ) ≤ 2 := by exact_mod_cast hcount q
    exact mul_le_mul_of_nonneg_right hc (hrpow q hq)
  refine hle.trans ?_
  rw [← Finset.mul_sum]
  have hgeom := two_mul_geom_le (α := α) (m := m) hα
  refine hgeom.trans ?_
  have hlog := (Nat.log2_eq_iff hδ.ne').mp rfl
  have hbase : (2 : ℝ) ^ m ≤ (δ : ℝ) := by exact_mod_cast hlog.1
  have hpow : ((2 : ℝ) ^ m) ^ α ≤ (δ : ℝ) ^ α :=
    Real.rpow_le_rpow (by positivity) hbase hα.le
  exact mul_le_mul_of_nonneg_left hpow (le_of_lt (dyadicHolderFactor_pos hα))

/-- Greedy jumps satisfy the summed power bound. -/
lemma sum_rpow_greedyJumps {a b : ℕ} {α : ℝ} (hα : 0 < α) (hδ : 0 < b - a) :
    ((greedyJumps a b).map (fun s : ℕ => (s : ℝ) ^ α)).sum ≤
      dyadicHolderFactor α * ((b - a : ℕ) : ℝ) ^ α := by
  refine sum_rpow_le hα hδ ?_ (fun q => count_greedyJumps_le_two a b q)
  intro s hs
  obtain ⟨_hpos, hle, ⟨k, hk⟩⟩ := mem_greedyJumps hs
  refine ⟨k, hk, ?_⟩
  have hpow : 2 ^ k ≤ b - a := by simpa [hk] using hle
  by_contra hgt
  have hlog := (Nat.log2_eq_iff (by omega : b - a ≠ 0)).mp rfl
  have hk' : Nat.log2 (b - a) + 1 ≤ k := by omega
  have hlt : b - a < 2 ^ k :=
    lt_of_lt_of_le hlog.2 (Nat.pow_le_pow_right (by decide) hk')
  omega

/-- Divide a constant out of a list of real powers. -/
lemma sum_map_div_rpow (l : List ℕ) {c α : ℝ} (hc : 0 < c) :
    (l.map (fun s : ℕ => ((s : ℝ) / c) ^ α)).sum =
      (l.map (fun s : ℕ => (s : ℝ) ^ α)).sum / c ^ α := by
  induction l with
  | nil => simp
  | cons s ls ih =>
      rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons, ih,
        Real.div_rpow (Nat.cast_nonneg _) (le_of_lt hc)]
      field_simp

/-- One aligned dyadic jump is controlled by the level-increment hypothesis. -/
lemma abs_one_jump {f : ℝ → ℝ} {L p r : ℕ} {α K : ℝ} (_hα : 0 < α) (_hK : 0 ≤ K)
    (hr : r ≤ L) (hp : p + 2 ^ r ≤ 2 ^ L) (hdvd : 2 ^ r ∣ p)
    (hinc : ∀ n, n ≤ L → ∀ i : ℕ, i < 2 ^ n →
      |f ((i + 1 : ℝ) / (2 : ℝ) ^ n) - f ((i : ℝ) / (2 : ℝ) ^ n)| ≤
        K * ((1 : ℝ) / (2 : ℝ) ^ n) ^ α) :
    |f (((p + 2 ^ r : ℕ) : ℝ) / (2 : ℝ) ^ L) - f ((p : ℝ) / (2 : ℝ) ^ L)| ≤
      K * (((2 ^ r : ℕ) : ℝ) / (2 : ℝ) ^ L) ^ α := by
  obtain ⟨i, hi⟩ := hdvd
  set n : ℕ := L - r
  have hn : n ≤ L := Nat.sub_le _ _
  have hL : r + n = L := Nat.add_sub_cancel' hr
  have hi_lt : i < 2 ^ n := by
    have hmul : 2 ^ r * (i + 1) ≤ 2 ^ L := by
      calc
        2 ^ r * (i + 1) = p + 2 ^ r := by rw [hi, Nat.mul_add, Nat.mul_one]
        _ ≤ 2 ^ L := hp
    have hpow : 2 ^ L = 2 ^ r * 2 ^ n := by
      rw [← hL, pow_add]
    rw [hpow] at hmul
    have hle : i + 1 ≤ 2 ^ n := Nat.le_of_mul_le_mul_left hmul (Nat.two_pow_pos r)
    omega
  have hpt : (p : ℝ) / (2 : ℝ) ^ L = (i : ℝ) / (2 : ℝ) ^ n := by
    have hpcast : (p : ℝ) = (2 : ℝ) ^ r * (i : ℝ) := by
      rw [hi, Nat.cast_mul]
      push_cast
      rfl
    have hpow : (2 : ℝ) ^ L = (2 : ℝ) ^ r * (2 : ℝ) ^ n := by
      rw [← hL, pow_add]
    rw [hpcast, hpow]
    exact mul_div_mul_left (i : ℝ) ((2 : ℝ) ^ n) (by positivity)
  have hpt' : (((p + 2 ^ r : ℕ) : ℝ) / (2 : ℝ) ^ L) =
      ((i + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n := by
    have hsum : ((p + 2 ^ r : ℕ) : ℝ) = (2 : ℝ) ^ r * ((i + 1 : ℕ) : ℝ) := by
      have : p + 2 ^ r = 2 ^ r * (i + 1) := by
        rw [hi, Nat.mul_add, Nat.mul_one]
      rw [this, Nat.cast_mul]
      push_cast
      rfl
    have hpow : (2 : ℝ) ^ L = (2 : ℝ) ^ r * (2 : ℝ) ^ n := by
      rw [← hL, pow_add]
    rw [hsum, hpow]
    exact mul_div_mul_left ((i + 1 : ℕ) : ℝ) ((2 : ℝ) ^ n) (by positivity)
  have hrhs : (((2 ^ r : ℕ) : ℝ) / (2 : ℝ) ^ L) = (1 : ℝ) / (2 : ℝ) ^ n := by
    have hpow : (2 : ℝ) ^ L = (2 : ℝ) ^ r * (2 : ℝ) ^ n := by
      rw [← hL, pow_add]
    rw [Nat.cast_pow, hpow]
    push_cast
    simpa using mul_div_mul_left (1 : ℝ) ((2 : ℝ) ^ n) (by positivity)
  rw [hpt, hpt', hrhs]
  simpa [Nat.cast_add, Nat.cast_one] using hinc n hn i hi_lt

/-- Chaining the greedy jumps bounds a grid increment by the sum of the jump powers. -/
lemma abs_sub_le_jumps {f : ℝ → ℝ} {α K : ℝ} {L : ℕ} (hα : 0 < α) (hK : 0 ≤ K)
    (hinc : ∀ n, n ≤ L → ∀ i : ℕ, i < 2 ^ n →
      |f ((i + 1 : ℝ) / (2 : ℝ) ^ n) - f ((i : ℝ) / (2 : ℝ) ^ n)| ≤
        K * ((1 : ℝ) / (2 : ℝ) ^ n) ^ α) (d : ℕ) :
    ∀ a b, b - a = d → a ≤ b → b ≤ 2 ^ L →
      |f ((b : ℝ) / (2 : ℝ) ^ L) - f ((a : ℝ) / (2 : ℝ) ^ L)| ≤
        K * ((greedyJumps a b).map
          (fun s : ℕ => ((s : ℝ) / (2 : ℝ) ^ L) ^ α)).sum := by
  refine Nat.strongRecOn d fun d ih a b hd hab hb => ?_
  by_cases hlt : a < b
  · have hle := greedyStep_le hlt
    obtain ⟨r, hr⟩ := greedyStep_eq_pow hlt
    have hrL : r ≤ L := by
      have hsle : 2 ^ r ≤ 2 ^ L := by
        calc
          2 ^ r = greedyStep a b := hr.symm
          _ ≤ b - a := hle
          _ ≤ b := by omega
          _ ≤ 2 ^ L := hb
      exact (Nat.pow_le_pow_iff_right (by decide)).mp hsle
    have hsum : a + greedyStep a b ≤ b :=
      (Nat.add_le_add_left (greedyStep_le hlt) a).trans_eq (Nat.add_sub_of_le hab)
    have hp : a + 2 ^ r ≤ 2 ^ L := by
      have hrew : a + 2 ^ r ≤ b := by simpa [hr] using hsum
      exact hrew.trans hb
    have hstep := abs_one_jump (p := a) (r := r) hα hK hrL hp
      (by simpa [hr] using greedyStep_dvd hlt) hinc
    have hdlt : b - (a + greedyStep a b) < d := by
      have hlt' : (b - a) - greedyStep a b < b - a :=
        Nat.sub_lt_self (greedyStep_pos hlt) (greedyStep_le hlt)
      rw [← hd, ← Nat.sub_sub]
      exact hlt'
    have hrest := ih (b - (a + greedyStep a b)) hdlt (a + greedyStep a b) b rfl
      hsum hb
    rw [greedyJumps_cons hlt, List.map_cons, List.sum_cons]
    have habs := abs_sub_le (f ((b : ℝ) / (2 : ℝ) ^ L))
      (f (((a + greedyStep a b : ℕ) : ℝ) / (2 : ℝ) ^ L))
      (f ((a : ℝ) / (2 : ℝ) ^ L))
    have hjump : |f (((a + greedyStep a b : ℕ) : ℝ) / (2 : ℝ) ^ L) -
        f ((a : ℝ) / (2 : ℝ) ^ L)| ≤
        K * (((greedyStep a b : ℕ) : ℝ) / (2 : ℝ) ^ L) ^ α := by
      simpa [hr] using hstep
    calc
      |f ((b : ℝ) / (2 : ℝ) ^ L) - f ((a : ℝ) / (2 : ℝ) ^ L)| ≤
          |f ((b : ℝ) / (2 : ℝ) ^ L) -
            f (((a + greedyStep a b : ℕ) : ℝ) / (2 : ℝ) ^ L)| +
          |f (((a + greedyStep a b : ℕ) : ℝ) / (2 : ℝ) ^ L) -
            f ((a : ℝ) / (2 : ℝ) ^ L)| := habs
      _ ≤ K * ((greedyJumps (a + greedyStep a b) b).map
            (fun s : ℕ => ((s : ℝ) / (2 : ℝ) ^ L) ^ α)).sum +
          K * (((greedyStep a b : ℕ) : ℝ) / (2 : ℝ) ^ L) ^ α :=
        add_le_add hrest hjump
      _ = K * ((((greedyStep a b : ℕ) : ℝ) / (2 : ℝ) ^ L) ^ α +
          ((greedyJumps (a + greedyStep a b) b).map
            (fun s : ℕ => ((s : ℝ) / (2 : ℝ) ^ L) ^ α)).sum) := by
        ring
  · have heq : a = b := by omega
    subst heq
    simp [greedyJumps_of_le le_rfl]

/-- Hölder control of a function on one level of the dyadic grid of `[0, 1]`. -/
theorem abs_sub_le_of_dyadic_grid {f : ℝ → ℝ} {α K : ℝ} {L a b : ℕ}
    (hα : 0 < α) (hK : 0 ≤ K)
    (hinc : ∀ n, n ≤ L → ∀ i : ℕ, i < 2 ^ n →
      |f ((i + 1 : ℝ) / (2 : ℝ) ^ n) - f ((i : ℝ) / (2 : ℝ) ^ n)| ≤
        K * ((1 : ℝ) / (2 : ℝ) ^ n) ^ α)
    (hab : a ≤ b) (hb : b ≤ 2 ^ L) :
    |f ((b : ℝ) / (2 : ℝ) ^ L) - f ((a : ℝ) / (2 : ℝ) ^ L)| ≤
      dyadicHolderFactor α * K * (((b - a : ℕ) : ℝ) / (2 : ℝ) ^ L) ^ α := by
  have hdist := abs_sub_le_jumps hα hK hinc (b - a) a b rfl hab hb
  by_cases hlt : a < b
  · have hδ : 0 < b - a := by omega
    have hsum := sum_rpow_greedyJumps (a := a) (b := b) hα hδ
    have hc : (0 : ℝ) < (2 : ℝ) ^ L := by positivity
    have hmap := sum_map_div_rpow (greedyJumps a b) (c := (2 : ℝ) ^ L) (α := α) hc
    have hscale : ((greedyJumps a b).map
        (fun s : ℕ => ((s : ℝ) / (2 : ℝ) ^ L) ^ α)).sum ≤
        dyadicHolderFactor α * (((b - a : ℕ) : ℝ) / (2 : ℝ) ^ L) ^ α := by
      rw [hmap, Real.div_rpow (Nat.cast_nonneg (b - a)) (le_of_lt hc), mul_div]
      exact div_le_div_of_nonneg_right hsum (Real.rpow_nonneg (le_of_lt hc) α)
    calc
      |f ((b : ℝ) / (2 : ℝ) ^ L) - f ((a : ℝ) / (2 : ℝ) ^ L)| ≤
          K * ((greedyJumps a b).map
            (fun s : ℕ => ((s : ℝ) / (2 : ℝ) ^ L) ^ α)).sum := hdist
      _ ≤ K * (dyadicHolderFactor α * (((b - a : ℕ) : ℝ) / (2 : ℝ) ^ L) ^ α) :=
        mul_le_mul_of_nonneg_left hscale hK
      _ = dyadicHolderFactor α * K * (((b - a : ℕ) : ℝ) / (2 : ℝ) ^ L) ^ α := by
        ring
  · have heq : a = b := by omega
    subst heq
    simp [Real.zero_rpow hα.ne', abs_zero, mul_zero]

end CKMA
