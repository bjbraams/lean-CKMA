/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Interval.Finset.Nat

import Mathlib.Tactic.Bound
import Mathlib.Tactic.Monotonicity.Lemmas
import Mathlib.Tactic.ReduceModChar

/-!
# Orbit bound for Kingman's theorem

A subadditive cocycle along one orbit is bounded by a greedy window of length `k`. The bound is
the deterministic step in Avila and Bochi's proof of the liminf estimate. The window objects
are defined for one sequence `w : ℕ → ℝ`; along an orbit they are applied to `u (s + i)`, and
for a random process `f` to the sequence `fun n => f n ω`.

## Main definitions

* `CKMA.IsKingmanWindow`: predicate that a sequence falls below a target slope on `1, …, k`.
* `CKMA.kingmanWindowBound`: the comparison value of a window of length `k`.
* `CKMA.kingmanTailBound`: the tail majorant of the comparison value and the first term.

## Main results

* `CKMA.kingmanCocycle_le_sum_blocks`: a cocycle is at most the sum of equal blocks.
* `CKMA.kingman_orbit_bound`: the deterministic Avila–Bochi orbit bound.
-/

public section

noncomputable section

namespace CKMA

open Finset

attribute [local instance] Classical.propDecidable

/-- A length in `1, …, k` on which the sequence lies strictly below the target slope. -/
@[expose]
def IsKingmanWindow (w : ℕ → ℝ) (slope : ℝ) (k : ℕ) : Prop :=
  ∃ j, 0 < j ∧ j ≤ k ∧ w j < (j : ℝ) * slope

/-- Unfolding of `IsKingmanWindow`. -/
lemma isKingmanWindow_iff {w : ℕ → ℝ} {slope : ℝ} {k : ℕ} :
    IsKingmanWindow w slope k ↔ ∃ j, 0 < j ∧ j ≤ k ∧ w j < (j : ℝ) * slope := Iff.rfl

/-- The comparison value: the target slope on a successful window, otherwise the first term. -/
@[expose]
def kingmanWindowBound (w : ℕ → ℝ) (slope : ℝ) (k : ℕ) : ℝ :=
  if IsKingmanWindow w slope k then slope else w 1

/-- The tail majorant, at least both the comparison value and the first term. -/
@[expose]
def kingmanTailBound (w : ℕ → ℝ) (slope : ℝ) (k : ℕ) : ℝ :=
  max (kingmanWindowBound w slope k) (w 1)

/-- Defining equation of `kingmanTailBound`. -/
lemma kingmanTailBound_def (w : ℕ → ℝ) (slope : ℝ) (k : ℕ) :
    kingmanTailBound w slope k = max (kingmanWindowBound w slope k) (w 1) := rfl

/-- Outside every window the first term is the comparison value. -/
lemma kingmanWindowBound_of_not_window {w : ℕ → ℝ} {slope : ℝ} {k : ℕ}
    (h : ¬ IsKingmanWindow w slope k) : kingmanWindowBound w slope k = w 1 := by
  simp [kingmanWindowBound, h]

/-- A successful window uses the target slope as the comparison value. -/
lemma kingmanWindowBound_of_window {w : ℕ → ℝ} {slope : ℝ} {k : ℕ}
    (h : IsKingmanWindow w slope k) : kingmanWindowBound w slope k = slope := by
  simp [kingmanWindowBound, h]

/-- The comparison value is at least the target slope when `k` is positive. -/
private lemma le_kingmanWindowBound {w : ℕ → ℝ} {slope : ℝ} {k : ℕ} (hk : 0 < k) :
    slope ≤ kingmanWindowBound w slope k := by
  by_cases h : IsKingmanWindow w slope k
  · rw [kingmanWindowBound_of_window h]
  · rw [kingmanWindowBound_of_not_window h]
    have h1 : ¬ w 1 < (1 : ℝ) * slope := by
      intro hlt
      exact h ⟨1, Nat.one_pos, hk, by simpa using hlt⟩
    have : (1 : ℝ) * slope ≤ w 1 := le_of_not_gt h1
    simpa using this

/-- The comparison value is at most the tail majorant. -/
private lemma kingmanWindowBound_le_kingmanTailBound (w : ℕ → ℝ) (slope : ℝ) (k : ℕ) :
    kingmanWindowBound w slope k ≤ kingmanTailBound w slope k :=
  le_max_left _ _

/-- The first term is at most the tail majorant. -/
private lemma le_kingmanTailBound (w : ℕ → ℝ) (slope : ℝ) (k : ℕ) :
    w 1 ≤ kingmanTailBound w slope k :=
  le_max_right _ _

/-- The comparison value is bounded by the slope plus the first term, in absolute value. -/
lemma abs_kingmanWindowBound_le (w : ℕ → ℝ) (slope : ℝ) (k : ℕ) :
    |kingmanWindowBound w slope k| ≤ |slope| + |w 1| := by
  by_cases h : IsKingmanWindow w slope k
  · rw [kingmanWindowBound_of_window h]
    exact le_add_of_nonneg_right (abs_nonneg _)
  · rw [kingmanWindowBound_of_not_window h]
    exact le_add_of_nonneg_left (abs_nonneg _)

/-- The tail majorant is bounded by the slope plus the first term, in absolute value. -/
lemma abs_kingmanTailBound_le (w : ℕ → ℝ) (slope : ℝ) (k : ℕ) :
    |kingmanTailBound w slope k| ≤ |slope| + |w 1| :=
  abs_max_le_max_abs_abs.trans
    (max_le (abs_kingmanWindowBound_le w slope k) (le_add_of_nonneg_left (abs_nonneg _)))

/-- Subadditive blocks of equal length are at most the sum of the block values. -/
lemma kingmanCocycle_le_sum_blocks {u : ℕ → ℕ → ℝ}
    (hsub : ∀ i n m, 0 < n → 0 < m → u i (n + m) ≤ u i n + u (i + n) m)
    {m : ℕ} (hm : 0 < m) {q : ℕ} (hq : 0 < q) :
    u 0 (q * m) ≤ ∑ j ∈ range q, u (j * m) m := by
  induction q with
  | zero =>
    omega
  | succ q ih =>
    cases q with
    | zero =>
      simp
    | succ q =>
      have hq0 : 0 < q + 1 := Nat.succ_pos q
      have hlen : 0 < (q + 1) * m := Nat.mul_pos hq0 hm
      have hstep := hsub 0 ((q + 1) * m) m hlen hm
      have hadd : (q + 1) * m + m = (q + 1 + 1) * m := by
        have hmul : (q + 1) * m + 1 * m = ((q + 1) + 1) * m :=
          (Nat.add_mul (q + 1) 1 m).symm
        simpa [one_mul] using hmul
      rw [hadd] at hstep
      have hIH := ih hq0
      rw [sum_range_succ]
      simp only [Nat.zero_add] at hstep
      linarith

/-- Iterating subadditivity bounds a block by the sum of its one-step increments. -/
private lemma kingmanCocycle_le_sum_one {u : ℕ → ℕ → ℝ}
    (hsub : ∀ i n m, 0 < n → 0 < m → u i (n + m) ≤ u i n + u (i + n) m) :
    ∀ r s, 0 < r → u s r ≤ ∑ t ∈ range r, u (s + t) 1 := by
  intro r
  induction r with
  | zero =>
    intro s hr
    omega
  | succ r ih =>
    intro s hr
    cases r with
    | zero => simp
    | succ r =>
      have hr0 : 0 < r + 1 := Nat.succ_pos r
      have hstep := hsub s (r + 1) 1 hr0 Nat.one_pos
      have hsum := ih s hr0
      rw [sum_range_succ]
      have hadd : (r + 1) + 1 = r + 2 := by omega
      rw [hadd] at hstep
      linarith

/-- A partial comparison sum is absorbed by the slope prefix and the majorant tail. -/
private lemma kingmanWindowBound_prefix_le {u : ℕ → ℕ → ℝ} {slope : ℝ} {k n j s : ℕ}
    (haj : n - k ≤ j) (hjn : j ≤ n) :
    ∑ i ∈ range j, kingmanWindowBound (u (s + i)) slope k +
        ∑ t ∈ range (n - j), kingmanTailBound (u (s + j + t)) slope k ≤
      ∑ i ∈ range (n - k), kingmanWindowBound (u (s + i)) slope k +
        ∑ i ∈ Ico (n - k) n, kingmanTailBound (u (s + i)) slope k := by
  have ha : n - k + (j - (n - k)) = j := by omega
  have hsplit : ∑ i ∈ range j, kingmanWindowBound (u (s + i)) slope k =
      ∑ i ∈ range (n - k), kingmanWindowBound (u (s + i)) slope k +
        ∑ i ∈ range (j - (n - k)), kingmanWindowBound (u (s + (n - k) + i)) slope k := by
    conv_lhs => rw [← ha]
    rw [sum_range_add]
    refine congrArg _ ?_
    apply sum_congr rfl
    intro i hi
    congr 2
    omega
  have hIco : ∑ i ∈ range (j - (n - k)), kingmanWindowBound (u (s + (n - k) + i)) slope k =
      ∑ i ∈ Ico (n - k) j, kingmanWindowBound (u (s + i)) slope k := by
    rw [sum_Ico_eq_sum_range]
    apply sum_congr rfl
    intro i _
    congr 2
    omega
  have hpsi : ∑ i ∈ Ico (n - k) j, kingmanWindowBound (u (s + i)) slope k ≤
      ∑ i ∈ Ico (n - k) j, kingmanTailBound (u (s + i)) slope k :=
    sum_le_sum fun i _ => kingmanWindowBound_le_kingmanTailBound (u (s + i)) slope k
  have htail : ∑ t ∈ range (n - j), kingmanTailBound (u (s + j + t)) slope k =
      ∑ i ∈ Ico j n, kingmanTailBound (u (s + i)) slope k := by
    rw [sum_Ico_eq_sum_range]
    apply sum_congr rfl
    intro i _
    congr 2
    omega
  have hdis : Disjoint (Ico (n - k) j) (Ico j n) := disjoint_left.mpr fun i hi hj => by
    simp only [mem_Ico] at hi hj
    omega
  have hun : Ico (n - k) j ∪ Ico j n = Ico (n - k) n :=
    Ico_union_Ico_eq_Ico (by omega) (by omega)
  have hmx : ∑ i ∈ Ico (n - k) j, kingmanTailBound (u (s + i)) slope k +
      ∑ i ∈ Ico j n, kingmanTailBound (u (s + i)) slope k =
      ∑ i ∈ Ico (n - k) n, kingmanTailBound (u (s + i)) slope k := by
    rw [← sum_union hdis, hun]
  linarith

/-- A positive-length block that meets the window is at most the sum of comparison values. -/
private lemma kingman_block_le_sum_psi {u : ℕ → ℕ → ℝ} {slope : ℝ} {k s : ℕ} (hk : 0 < k) :
    ∃ j, 0 < j ∧ j ≤ k ∧
      u s j ≤ ∑ i ∈ range j, kingmanWindowBound (u (s + i)) slope k := by
  by_cases hwin : IsKingmanWindow (u s) slope k
  · obtain ⟨j, hj0, hjk, hjlt⟩ := hwin
    refine ⟨j, hj0, hjk, ?_⟩
    have hconst : ∑ i ∈ range j, slope = (j : ℝ) * slope := by
      simp [sum_const, card_range, nsmul_eq_mul]
    have hge : ∑ i ∈ range j, slope ≤
        ∑ i ∈ range j, kingmanWindowBound (u (s + i)) slope k :=
      sum_le_sum fun i _ => le_kingmanWindowBound hk
    have hψ : ∑ i ∈ range j, kingmanWindowBound (u (s + i)) slope k ≥ (j : ℝ) * slope := by
      rw [← hconst]
      exact hge
    exact hjlt.le.trans hψ
  · refine ⟨1, Nat.one_pos, hk, ?_⟩
    simp [kingmanWindowBound_of_not_window hwin]

/-- Avila–Bochi orbit bound: the last `k` steps carry the larger majorant. -/
theorem kingman_orbit_bound {u : ℕ → ℕ → ℝ}
    (hsub : ∀ i n m, 0 < n → 0 < m → u i (n + m) ≤ u i n + u (i + n) m)
    {k : ℕ} (hk : 0 < k) (slope : ℝ) :
    ∀ n s, k ≤ n →
      u s n ≤ ∑ i ∈ range (n - k), kingmanWindowBound (u (s + i)) slope k +
        ∑ i ∈ Ico (n - k) n, kingmanTailBound (u (s + i)) slope k := by
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro s hn
    obtain ⟨j, hj0, hjk, hblock⟩ := kingman_block_le_sum_psi (u := u) (slope := slope)
      (k := k) (s := s) hk
    have hjn : j ≤ n := hjk.trans hn
    by_cases hlt : j < n
    · have hnpos : 0 < n - j := by omega
      have hadd : j + (n - j) = n := Nat.add_sub_of_le hlt.le
      have hsplit := hsub s j (n - j) hj0 hnpos
      rw [hadd] at hsplit
      by_cases hik : k ≤ n - j
      · have hsmall : n - j < n := by omega
        have hIH := ih (n - j) hsmall (s + j) hik
        have hsumψ : ∑ i ∈ range (n - k), kingmanWindowBound (u (s + i)) slope k =
            ∑ i ∈ range j, kingmanWindowBound (u (s + i)) slope k +
              ∑ i ∈ range (n - j - k), kingmanWindowBound (u (s + j + i)) slope k := by
          have hlen : n - k = j + (n - j - k) := by omega
          conv_lhs => rw [hlen]
          rw [sum_range_add]
          refine congrArg _ ?_
          apply sum_congr rfl
          intro i hi
          congr 2
          omega
        have hmx : ∑ i ∈ Ico (n - j - k) (n - j), kingmanTailBound (u (s + j + i)) slope k =
            ∑ i ∈ Ico (n - k) n, kingmanTailBound (u (s + i)) slope k := by
          rw [sum_Ico_eq_sum_range, sum_Ico_eq_sum_range]
          have hcard : (n - j) - (n - j - k) = n - (n - k) := by omega
          rw [hcard]
          apply sum_congr rfl
          intro t _
          congr 2
          omega
        linarith
      · have hones := kingmanCocycle_le_sum_one hsub (n - j) (s + j) hnpos
        have hmx1 : ∑ t ∈ range (n - j), u (s + j + t) 1 ≤
            ∑ t ∈ range (n - j), kingmanTailBound (u (s + j + t)) slope k :=
          sum_le_sum fun t _ => le_kingmanTailBound (u (s + j + t)) slope k
        have hpre := kingmanWindowBound_prefix_le (u := u) (slope := slope) (k := k) (n := n)
          (j := j) (s := s) (by omega) hjn
        linarith
    · have hjn' : j = n := le_antisymm hjn (not_lt.mp hlt)
      have hempty : ∑ t ∈ range (n - j), kingmanTailBound (u (s + j + t)) slope k = 0 := by
        rw [hjn', Nat.sub_self, sum_range_zero]
      have hpre := kingmanWindowBound_prefix_le (u := u) (slope := slope) (k := k) (n := n)
        (j := j) (s := s) (by omega) hjn
      rw [hempty, add_zero] at hpre
      have : u s n ≤ ∑ i ∈ range j, kingmanWindowBound (u (s + i)) slope k := by
        simpa [hjn'] using hblock
      linarith

end CKMA
