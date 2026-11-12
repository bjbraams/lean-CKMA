/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Basic.Real.Basic

import Mathlib.Tactic

/-!
# Orbit bound for Kingman's theorem

A subadditive cocycle along one orbit is bounded by a greedy window of length `k`. The bound is
the deterministic step in Avila and Bochi's proof of the liminf estimate.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Finset

attribute [local instance] Classical.propDecidable

/-- A length in `1, …, k` on which the cocycle lies strictly below the target slope. -/
def kingmanWindow (u : ℕ → ℕ → ℝ) (slope : ℝ) (k i : ℕ) : Prop :=
  ∃ j, 0 < j ∧ j ≤ k ∧ u i j < (j : ℝ) * slope

/-- The comparison function: the target slope on a successful window, otherwise one step. -/
def kingmanPsi (u : ℕ → ℕ → ℝ) (slope : ℝ) (k i : ℕ) : ℝ :=
  if kingmanWindow u slope k i then slope else u i 1

/-- The tail majorant, at least both the comparison function and the one-step increment. -/
def kingmanMx (u : ℕ → ℕ → ℝ) (slope : ℝ) (k i : ℕ) : ℝ :=
  max (kingmanPsi u slope k i) (u i 1)

/-- Outside every window the one-step increment is the comparison function. -/
lemma kingmanPsi_of_not_window {u : ℕ → ℕ → ℝ} {slope : ℝ} {k i : ℕ}
    (h : ¬ kingmanWindow u slope k i) : kingmanPsi u slope k i = u i 1 := by
  simp [kingmanPsi, h]

/-- A successful window uses the target slope as the comparison value. -/
lemma kingmanPsi_of_window {u : ℕ → ℕ → ℝ} {slope : ℝ} {k i : ℕ}
    (h : kingmanWindow u slope k i) : kingmanPsi u slope k i = slope := by
  simp [kingmanPsi, h]

/-- Every site is at least the target slope when `k` is positive. -/
lemma le_kingmanPsi {u : ℕ → ℕ → ℝ} {slope : ℝ} {k : ℕ} (hk : 0 < k) (i : ℕ) :
    slope ≤ kingmanPsi u slope k i := by
  by_cases h : kingmanWindow u slope k i
  · rw [kingmanPsi_of_window h]
  · rw [kingmanPsi_of_not_window h]
    have h1 : ¬ u i 1 < (1 : ℝ) * slope := by
      intro hlt
      exact h ⟨1, Nat.one_pos, hk, by simpa using hlt⟩
    have : (1 : ℝ) * slope ≤ u i 1 := le_of_not_gt h1
    simpa using this

/-- The comparison function is at most the tail majorant. -/
lemma kingmanPsi_le_kingmanMx (u : ℕ → ℕ → ℝ) (slope : ℝ) (k i : ℕ) :
    kingmanPsi u slope k i ≤ kingmanMx u slope k i :=
  le_max_left _ _

/-- One-step increments are at most the tail majorant. -/
lemma le_kingmanMx (u : ℕ → ℕ → ℝ) (slope : ℝ) (k i : ℕ) :
    u i 1 ≤ kingmanMx u slope k i :=
  le_max_right _ _

/-- Iterating subadditivity bounds a block by the sum of its one-step increments. -/
lemma kingmanCocycle_le_sum_one {u : ℕ → ℕ → ℝ}
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
lemma kingmanPsi_prefix_le {u : ℕ → ℕ → ℝ} {slope : ℝ} {k n j s : ℕ}
    (haj : n - k ≤ j) (hjn : j ≤ n) :
    ∑ i ∈ range j, kingmanPsi u slope k (s + i) +
        ∑ t ∈ range (n - j), kingmanMx u slope k (s + j + t) ≤
      ∑ i ∈ range (n - k), kingmanPsi u slope k (s + i) +
        ∑ i ∈ Ico (n - k) n, kingmanMx u slope k (s + i) := by
  have ha : n - k + (j - (n - k)) = j := by omega
  have hsplit : ∑ i ∈ range j, kingmanPsi u slope k (s + i) =
      ∑ i ∈ range (n - k), kingmanPsi u slope k (s + i) +
        ∑ i ∈ range (j - (n - k)), kingmanPsi u slope k (s + (n - k) + i) := by
    conv_lhs => rw [← ha]
    rw [sum_range_add]
    refine congrArg _ ?_
    apply sum_congr rfl
    intro i hi
    congr 1
    omega
  have hIco : ∑ i ∈ range (j - (n - k)), kingmanPsi u slope k (s + (n - k) + i) =
      ∑ i ∈ Ico (n - k) j, kingmanPsi u slope k (s + i) := by
    rw [sum_Ico_eq_sum_range]
    apply sum_congr rfl
    intro i _
    congr 1
    omega
  have hpsi : ∑ i ∈ Ico (n - k) j, kingmanPsi u slope k (s + i) ≤
      ∑ i ∈ Ico (n - k) j, kingmanMx u slope k (s + i) :=
    sum_le_sum fun i _ => kingmanPsi_le_kingmanMx u slope k (s + i)
  have htail : ∑ t ∈ range (n - j), kingmanMx u slope k (s + j + t) =
      ∑ i ∈ Ico j n, kingmanMx u slope k (s + i) := by
    rw [sum_Ico_eq_sum_range]
    apply sum_congr rfl
    intro i _
    congr 1
    omega
  have hdis : Disjoint (Ico (n - k) j) (Ico j n) := disjoint_left.mpr fun i hi hj => by
    simp only [mem_Ico] at hi hj
    omega
  have hun : Ico (n - k) j ∪ Ico j n = Ico (n - k) n :=
    Ico_union_Ico_eq_Ico (by omega) (by omega)
  have hmx : ∑ i ∈ Ico (n - k) j, kingmanMx u slope k (s + i) +
      ∑ i ∈ Ico j n, kingmanMx u slope k (s + i) =
      ∑ i ∈ Ico (n - k) n, kingmanMx u slope k (s + i) := by
    rw [← sum_union hdis, hun]
  linarith

/-- A positive-length block that meets the window is at most the sum of comparison values. -/
lemma kingman_block_le_sum_psi {u : ℕ → ℕ → ℝ} {slope : ℝ} {k s : ℕ} (hk : 0 < k) :
    ∃ j, 0 < j ∧ j ≤ k ∧
      u s j ≤ ∑ i ∈ range j, kingmanPsi u slope k (s + i) := by
  by_cases hwin : kingmanWindow u slope k s
  · obtain ⟨j, hj0, hjk, hjlt⟩ := hwin
    refine ⟨j, hj0, hjk, ?_⟩
    have hconst : ∑ i ∈ range j, slope = (j : ℝ) * slope := by
      simp [sum_const, card_range, nsmul_eq_mul]
    have hge : ∑ i ∈ range j, slope ≤ ∑ i ∈ range j, kingmanPsi u slope k (s + i) :=
      sum_le_sum fun i _ => le_kingmanPsi hk (s + i)
    have hψ : ∑ i ∈ range j, kingmanPsi u slope k (s + i) ≥ (j : ℝ) * slope := by
      rw [← hconst]
      exact hge
    exact hjlt.le.trans hψ
  · refine ⟨1, Nat.one_pos, hk, ?_⟩
    simp [kingmanPsi_of_not_window hwin]

/-- Avila–Bochi orbit bound: the last `k` steps carry the larger majorant. -/
theorem kingman_orbit_bound {u : ℕ → ℕ → ℝ}
    (hsub : ∀ i n m, 0 < n → 0 < m → u i (n + m) ≤ u i n + u (i + n) m)
    {k : ℕ} (hk : 0 < k) (slope : ℝ) :
    ∀ n s, k ≤ n →
      u s n ≤ ∑ i ∈ range (n - k), kingmanPsi u slope k (s + i) +
        ∑ i ∈ Ico (n - k) n, kingmanMx u slope k (s + i) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
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
        have hsumψ : ∑ i ∈ range (n - k), kingmanPsi u slope k (s + i) =
            ∑ i ∈ range j, kingmanPsi u slope k (s + i) +
              ∑ i ∈ range (n - j - k), kingmanPsi u slope k (s + j + i) := by
          have hlen : n - k = j + (n - j - k) := by omega
          conv_lhs => rw [hlen]
          rw [sum_range_add]
          refine congrArg _ ?_
          apply sum_congr rfl
          intro i hi
          congr 1
          omega
        have hmx : ∑ i ∈ Ico (n - j - k) (n - j), kingmanMx u slope k (s + j + i) =
            ∑ i ∈ Ico (n - k) n, kingmanMx u slope k (s + i) := by
          rw [sum_Ico_eq_sum_range, sum_Ico_eq_sum_range]
          have hcard : (n - j) - (n - j - k) = n - (n - k) := by omega
          rw [hcard]
          apply sum_congr rfl
          intro t _
          congr 1
          omega
        linarith
      · have hones := kingmanCocycle_le_sum_one hsub (n - j) (s + j) hnpos
        have hmx1 : ∑ t ∈ range (n - j), u (s + j + t) 1 ≤
            ∑ t ∈ range (n - j), kingmanMx u slope k (s + j + t) :=
          sum_le_sum fun t _ => le_kingmanMx u slope k (s + j + t)
        have hpre := kingmanPsi_prefix_le (u := u) (slope := slope) (k := k) (n := n)
          (j := j) (s := s) (by omega) hjn
        linarith
    · have hjn' : j = n := le_antisymm hjn (not_lt.mp hlt)
      have hempty : ∑ t ∈ range (n - j), kingmanMx u slope k (s + j + t) = 0 := by
        rw [hjn', Nat.sub_self, sum_range_zero]
      have hpre := kingmanPsi_prefix_le (u := u) (slope := slope) (k := k) (n := n)
        (j := j) (s := s) (by omega) hjn
      rw [hempty, add_zero] at hpre
      have : u s n ≤ ∑ i ∈ range j, kingmanPsi u slope k (s + i) := by
        simpa [hjn'] using hblock
      linarith

end CKMA
