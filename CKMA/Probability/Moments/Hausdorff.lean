/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Dirac
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Tactic

import Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Polynomial
import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-!
# Hausdorff moment sequences (48.34)

Complete monotonicity uses forward differences with the alternating sign convention.
`hausdorffWeight` and `hausdorffApproximant` give the Bernstein discrete measures used
in the moment construction. Supporting lemmas prove nonnegativity of the weights and
nonnegativity and antitonicity of the original sequence.

The main theorem characterizes these sequences by a unique finite positive measure
concentrated on `[0,1]`. No probability normalization is imposed, so zero mass is included.
Existence extracts a weak limit of the approximants by Prokhorov's theorem. Uniqueness uses
the Weierstrass approximation theorem on `[0,1]`.
-/

@[expose] public section

noncomputable section

namespace CKMA

open MeasureTheory Filter Topology
open scoped BigOperators BoundedContinuousFunction ENNReal NNReal

/-- The forward difference of a real sequence. -/
def forwardDifference (s : ℕ → ℝ) (n : ℕ) : ℝ := s (n + 1) - s n

/-- Discrete complete monotonicity with the forward-difference sign convention. -/
def IsCompletelyMonotoneSequence (s : ℕ → ℝ) : Prop :=
  ∀ n k : ℕ, 0 ≤ (-1 : ℝ) ^ k * ((forwardDifference^[k]) s) n

/-- Bernstein weights in the constructive Hausdorff approximation. -/
def hausdorffWeight (s : ℕ → ℝ) (N k : ℕ) : ℝ :=
  (N.choose k : ℝ) * ((-1 : ℝ) ^ (N - k) * ((forwardDifference^[N - k]) s) k)

/-- The finite discrete measure approximating a Hausdorff moment law. -/
def hausdorffApproximant (s : ℕ → ℝ) (N : ℕ) : Measure ℝ :=
  ∑ k ∈ Finset.range (N + 1), ENNReal.ofReal (hausdorffWeight s N k) •
    Measure.dirac ((k : ℝ) / N)

/-- Complete monotonicity makes every Bernstein weight nonnegative. -/
theorem IsCompletelyMonotoneSequence.hausdorffWeight_nonneg {s : ℕ → ℝ}
    (hs : IsCompletelyMonotoneSequence s) (N k : ℕ) : 0 ≤ hausdorffWeight s N k :=
  mul_nonneg (Nat.cast_nonneg _) (hs k (N - k))

/-- Complete monotonicity includes nonnegativity of the sequence. -/
theorem IsCompletelyMonotoneSequence.nonneg {s : ℕ → ℝ}
    (hs : IsCompletelyMonotoneSequence s) (n : ℕ) : 0 ≤ s n := by
  simpa using hs n 0

/-- Complete monotonicity includes antitonicity. -/
theorem IsCompletelyMonotoneSequence.antitone {s : ℕ → ℝ}
    (hs : IsCompletelyMonotoneSequence s) : Antitone s := by
  apply antitone_nat_of_succ_le
  intro n
  have h := hs n 1
  simp only [pow_one, Function.iterate_one, forwardDifference] at h
  linarith

/-- A finite measure concentrated on `[0,1]` represents all the moments of `s`. -/
def RepresentsHausdorffMoments (μ : Measure ℝ) (s : ℕ → ℝ) : Prop :=
  IsFiniteMeasure μ ∧ μ (Set.Icc (0 : ℝ) 1)ᶜ = 0 ∧ ∀ n : ℕ, ∫ x, x ^ n ∂μ = s n

/-! ### Binomial arithmetic -/

/-- Even and odd powers of `-1` agree when the exponents have the same parity. -/
private lemma neg_one_pow_two_mul_sub (a j : ℕ) (hj : j ≤ a) :
    (-1 : ℝ) ^ (2 * a - j) = (-1) ^ j := by
  have hle : j ≤ 2 * a := by omega
  have hsum : 2 * a - j + j = 2 * a := Nat.sub_add_cancel hle
  have heven : Even (2 * a) := even_two_mul a
  have hiff : Even (2 * a - j) ↔ Even j := by
    have hpar := Nat.even_add (m := 2 * a - j) (n := j)
    rw [hsum] at hpar
    simpa [heven] using hpar
  by_cases h : Even j
  · have h2 : Even (2 * a - j) := hiff.mpr h
    calc (-1 : ℝ) ^ (2 * a - j) = (1 : ℝ) ^ (2 * a - j) := h2.neg_pow 1
      _ = 1 := one_pow _
      _ = (1 : ℝ) ^ j := (one_pow _).symm
      _ = (-1) ^ j := (h.neg_pow 1).symm
  · have hodd : Odd j := Nat.not_even_iff_odd.mp h
    have h2 : Odd (2 * a - j) :=
      Nat.not_even_iff_odd.mp (fun he => h (hiff.mp he))
    calc (-1 : ℝ) ^ (2 * a - j) = -1 := h2.neg_one_pow
      _ = (-1) ^ j := hodd.neg_one_pow.symm

/-- The sign in the expanded Bernstein weight simplifies to `(-1) ^ j`. -/
private lemma neg_one_mul_pow_sub (a j : ℕ) (hj : j ≤ a) :
    (-1 : ℝ) ^ a * (-1) ^ (a - j) = (-1) ^ j := by
  have hsum : a + (a - j) = 2 * a - j := by omega
  rw [← pow_add, hsum]
  exact neg_one_pow_two_mul_sub a j hj

/-- Negating a power of `-1` raises the exponent by one. -/
private lemma neg_neg_one_pow_sub (a b : ℕ) (hb : b ≤ a) :
    -((-1 : ℝ) ^ (a - b)) = (-1) ^ (a + 1 - b) := by
  have h : a + 1 - b = a - b + 1 := by omega
  rw [h, pow_succ, mul_neg_one]

/-- Moving the first index of a range sum onto an interval. -/
private lemma sum_range_succ_eq_Ico (f : ℕ → ℝ) (n : ℕ) :
    ∑ j ∈ Finset.range n, f (j + 1) = ∑ t ∈ Finset.Ico 1 (n + 1), f t := by
  refine Finset.sum_nbij' (fun j => j + 1) (fun t => t - 1) ?_ ?_ ?_ ?_
      (fun _ _ => rfl) <;>
    intro a ha <;> simp only [Finset.mem_range, Finset.mem_Ico] at ha ⊢ <;> omega

/-- Binomial expansion of one step of the forward difference. -/
private lemma forwardDifference_sum_step (s : ℕ → ℝ) (k n : ℕ) :
    (∑ j ∈ Finset.range (k + 1),
        (k.choose j : ℝ) * (-1 : ℝ) ^ (k - j) * s (n + 1 + j)) -
      ∑ j ∈ Finset.range (k + 1),
        (k.choose j : ℝ) * (-1 : ℝ) ^ (k - j) * s (n + j) =
      ∑ j ∈ Finset.range (k + 2),
        ((k + 1).choose j : ℝ) * (-1 : ℝ) ^ (k + 1 - j) * s (n + j) := by
  classical
  let α : ℕ → ℝ := fun j => (k.choose j : ℝ) * (-1 : ℝ) ^ (k - j)
  have hα_last : α (k + 1) = 0 := by
    simp [α]
  have hpad (t : ℕ) :
      ∑ j ∈ Finset.range (k + 1), α j * s (t + j) =
        ∑ j ∈ Finset.range (k + 2), α j * s (t + j) := by
    rw [Finset.sum_range_succ (fun j => α j * s (t + j)) (k + 1), hα_last, zero_mul,
      add_zero]
  have hS1 :
      ∑ j ∈ Finset.range (k + 2), α j * s (n + 1 + j) =
        ∑ t ∈ Finset.Ico 1 (k + 2), α (t - 1) * s (n + t) := by
    have hshift :
        ∑ j ∈ Finset.range (k + 2), α j * s (n + 1 + j) =
          ∑ j ∈ Finset.range (k + 2), α ((j + 1) - 1) * s (n + (j + 1)) := by
      refine Finset.sum_congr rfl fun j _hj => ?_
      have : n + 1 + j = n + (j + 1) := by omega
      simp [this]
    rw [hshift, sum_range_succ_eq_Ico (fun t => α (t - 1) * s (n + t)) (k + 2),
      Finset.sum_Ico_succ_top (by omega : 1 ≤ k + 2)]
    simp [hα_last, show (k + 2) - 1 = k + 1 by omega]
  have hS2 :
      ∑ j ∈ Finset.range (k + 2), α j * s (n + j) =
        α 0 * s n + ∑ t ∈ Finset.Ico 1 (k + 2), α t * s (n + t) := by
    rw [Finset.sum_range_succ' (fun j => α j * s (n + j)) (k + 1), add_comm,
      ← sum_range_succ_eq_Ico (fun t => α t * s (n + t)) (k + 1)]
    simp
  rw [hpad (n + 1), hpad n, hS1, hS2]
  have hdiff :
      ∑ t ∈ Finset.Ico 1 (k + 2), α (t - 1) * s (n + t) -
          (α 0 * s n + ∑ t ∈ Finset.Ico 1 (k + 2), α t * s (n + t)) =
        -(α 0 * s n) +
          ∑ t ∈ Finset.Ico 1 (k + 2), (α (t - 1) - α t) * s (n + t) := by
    rw [sub_add_eq_sub_sub, sub_right_comm]
    have hsub :
        ∑ t ∈ Finset.Ico 1 (k + 2), α (t - 1) * s (n + t) -
            ∑ t ∈ Finset.Ico 1 (k + 2), α t * s (n + t) =
          ∑ t ∈ Finset.Ico 1 (k + 2), (α (t - 1) - α t) * s (n + t) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun t _ht => ?_
      ring
    rw [hsub, sub_eq_add_neg, add_comm]
  rw [hdiff]
  have hsplit :
      -(α 0 * s n) +
          ∑ t ∈ Finset.Ico 1 (k + 2), (α (t - 1) - α t) * s (n + t) =
        ∑ t ∈ Finset.range (k + 2),
          (if t = 0 then -α 0 else α (t - 1) - α t) * s (n + t) := by
    rw [Finset.sum_range_succ' (fun t =>
        (if t = 0 then -α 0 else α (t - 1) - α t) * s (n + t)) (k + 1),
      add_comm]
    congr 1
    · exact (sum_range_succ_eq_Ico (fun t => (α (t - 1) - α t) * s (n + t)) (k + 1)).symm
    · simp
  rw [hsplit]
  refine Finset.sum_congr rfl fun t ht => ?_
  have ht' : t ≤ k + 1 := by
    simp only [Finset.mem_range] at ht
    omega
  have hcoeff :
      (if t = 0 then -α 0 else α (t - 1) - α t) =
        ((k + 1).choose t : ℝ) * (-1) ^ (k + 1 - t) := by
    by_cases ht0 : t = 0
    · subst ht0
      have hsign := neg_neg_one_pow_sub k 0 (Nat.zero_le k)
      simp only [Nat.sub_zero] at hsign
      simp [α, hsign, Nat.choose_zero_right]
    · have htpos : 0 < t := Nat.pos_of_ne_zero ht0
      have hsub : k - (t - 1) = k + 1 - t := by omega
      by_cases htk : t ≤ k
      · have hsign : -((-1 : ℝ) ^ (k - t)) = (-1) ^ (k + 1 - t) :=
          neg_neg_one_pow_sub k t htk
        have hpascal : (k + 1).choose t = k.choose (t - 1) + k.choose t :=
          Nat.choose_succ_left k t htpos
        rw [ite_eq_right ht0]
        dsimp only [α]
        rw [hsub]
        calc
          (k.choose (t - 1) : ℝ) * (-1) ^ (k + 1 - t) -
              (k.choose t : ℝ) * (-1) ^ (k - t) =
            (k.choose (t - 1) : ℝ) * (-1) ^ (k + 1 - t) +
              (k.choose t : ℝ) * (-1) ^ (k + 1 - t) := by
            rw [← hsign]; ring
          _ = ((k.choose (t - 1) + k.choose t : ℕ) : ℝ) *
              (-1) ^ (k + 1 - t) := by
            simp [Nat.cast_add]; ring
          _ = ((k + 1).choose t : ℝ) * (-1) ^ (k + 1 - t) := by rw [← hpascal]
      · have hteq : t = k + 1 := by omega
        subst hteq
        rw [ite_eq_right ht0]
        have hsubk : k - (k + 1) = 0 := by omega
        simp [α, hsubk, Nat.choose_self, pow_zero]
  rw [hcoeff]

/-- Iterated forward differences expand by the binomial theorem. -/
private lemma forwardDifference_iterate_eq_sum (s : ℕ → ℝ) (k n : ℕ) :
    (forwardDifference^[k] s) n =
      ∑ j ∈ Finset.range (k + 1),
        (k.choose j : ℝ) * (-1 : ℝ) ^ (k - j) * s (n + j) := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', forwardDifference, ih (n + 1), ih n,
      forwardDifference_sum_step]

/-- Reindex the triangle `k + j ≤ N` by the sum `m = k + j`. -/
private lemma sum_triangle {M : Type*} [AddCommMonoid M] (N : ℕ) (f : ℕ → ℕ → M) :
    (∑ k ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N - k + 1), f k j) =
      ∑ m ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (m + 1), f k (m - k) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ (fun k => ∑ j ∈ Finset.range ((N + 1) - k + 1), f k j)]
    have hlast :
        ∑ j ∈ Finset.range ((N + 1) - (N + 1) + 1), f (N + 1) j = f (N + 1) 0 := by
      simp
    rw [hlast]
    have hinner : ∀ k ∈ Finset.range (N + 1),
        ∑ j ∈ Finset.range ((N + 1) - k + 1), f k j =
          ∑ j ∈ Finset.range (N - k + 1), f k j + f k ((N + 1) - k) := by
      intro k hk
      have hkN : k ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have h1 : (N + 1) - k + 1 = (N - k + 1) + 1 := by omega
      have h2 : N - k + 1 = (N + 1) - k := by omega
      rw [h1, Finset.sum_range_succ, h2]
    have hcol :
        ∑ k ∈ Finset.range (N + 2), f k ((N + 1) - k) =
          ∑ k ∈ Finset.range (N + 1), f k ((N + 1) - k) + f (N + 1) 0 := by
      rw [Finset.sum_range_succ]
      simp
    rw [Finset.sum_congr rfl hinner, Finset.sum_add_distrib, ih]
    rw [Finset.sum_range_succ (fun m => ∑ k ∈ Finset.range (m + 1), f k (m - k)) (N + 1),
      add_assoc]
    congr 1
    exact hcol.symm

/-- A row of Pascal's triangle with alternating signs is `0 ^ m`. -/
private lemma sum_choose_neg (m : ℕ) :
    ∑ k ∈ Finset.range (m + 1), (m.choose k : ℝ) * (-1 : ℝ) ^ (m - k) =
      (0 : ℝ) ^ m := by
  have h := add_pow (1 : ℝ) (-1) m
  simp only [one_pow, add_neg_cancel, one_mul] at h
  rw [h]
  refine Finset.sum_congr rfl fun k _hk => ?_
  ring

/-- Alternating transform of `k ↦ choose k j`, equal to `1` only on the diagonal. -/
private lemma sum_choose_mul_choose_neg (m j : ℕ) :
    ∑ k ∈ Finset.range (m + 1),
        (m.choose k : ℝ) * (k.choose j : ℝ) * (-1 : ℝ) ^ (m - k) =
      if m = j then (1 : ℝ) else 0 := by
  classical
  by_cases hj : j ≤ m
  · rw [← Finset.sum_range_add_sum_Ico
        (fun k => (m.choose k : ℝ) * (k.choose j : ℝ) * (-1 : ℝ) ^ (m - k))
        (Nat.le_succ_of_le hj)]
    have hhead :
        ∑ k ∈ Finset.range j,
            (m.choose k : ℝ) * (k.choose j : ℝ) * (-1 : ℝ) ^ (m - k) = 0 := by
      refine Finset.sum_eq_zero fun k hk => ?_
      simp [Nat.choose_eq_zero_of_lt (Finset.mem_range.mp hk)]
    rw [hhead, zero_add]
    have hreindex :
        ∑ k ∈ Finset.Ico j (m + 1),
            (m.choose k : ℝ) * (k.choose j : ℝ) * (-1 : ℝ) ^ (m - k) =
          ∑ i ∈ Finset.range (m - j + 1),
            (m.choose (i + j) : ℝ) * ((i + j).choose j : ℝ) *
              (-1 : ℝ) ^ (m - (i + j)) := by
      refine (Finset.sum_nbij' (fun i => i + j) (fun k => k - j)
        (s := Finset.range (m - j + 1)) (t := Finset.Ico j (m + 1))
        ?_ ?_ ?_ ?_ ?_).symm
      · intro i hi
        simp only [Finset.mem_range, Finset.mem_Ico] at hi ⊢
        omega
      · intro k hk
        simp only [Finset.mem_range, Finset.mem_Ico] at hk ⊢
        omega
      · intro i hi
        omega
      · intro k hk
        simp only [Finset.mem_Ico] at hk
        omega
      · intro i hi
        rfl
    rw [hreindex]
    have hterm : ∀ i ∈ Finset.range (m - j + 1),
        (m.choose (i + j) : ℝ) * ((i + j).choose j : ℝ) *
            (-1 : ℝ) ^ (m - (i + j)) =
          (m.choose j : ℝ) * ((m - j).choose i : ℝ) *
            (-1 : ℝ) ^ ((m - j) - i) := by
      intro i hi
      have hi' : i ≤ m - j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have hchoose :
          m.choose (i + j) * (i + j).choose j =
            m.choose j * (m - j).choose i := by
        simpa [Nat.add_sub_cancel] using
          Nat.choose_mul (n := m) (k := i + j) (s := j) (Nat.le_add_left _ _)
      have hexp : m - (i + j) = (m - j) - i := by omega
      rw [hexp]
      calc
        (m.choose (i + j) : ℝ) * ((i + j).choose j : ℝ) *
            (-1) ^ ((m - j) - i) =
            ((m.choose (i + j) * (i + j).choose j : ℕ) : ℝ) *
              (-1) ^ ((m - j) - i) := by simp [Nat.cast_mul]
        _ = ((m.choose j * (m - j).choose i : ℕ) : ℝ) *
              (-1) ^ ((m - j) - i) := by rw [hchoose]
        _ = (m.choose j : ℝ) * ((m - j).choose i : ℝ) *
              (-1) ^ ((m - j) - i) := by simp [Nat.cast_mul]
    rw [Finset.sum_congr rfl hterm]
    simp_rw [mul_assoc, ← Finset.mul_sum]
    rw [sum_choose_neg (m - j)]
    by_cases hmj : m = j
    · simp [hmj, pow_zero]
    · have hpos : m - j ≠ 0 := by omega
      simp [hmj, zero_pow hpos]
  · have hlt : m < j := lt_of_not_ge hj
    simp only [ne_of_lt hlt, ite_false]
    refine Finset.sum_eq_zero fun k hk => ?_
    have hklt : k < j := by
      have hk' : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      omega
    simp [Nat.choose_eq_zero_of_lt hklt]

/-- Expanded form of a Bernstein weight, for `k ≤ N`. -/
private lemma hausdorffWeight_eq_sum (s : ℕ → ℝ) (N k : ℕ) (_hk : k ≤ N) :
    hausdorffWeight s N k =
      ∑ j ∈ Finset.range (N - k + 1),
        (N.choose k : ℝ) * ((N - k).choose j : ℝ) * (-1 : ℝ) ^ j * s (k + j) := by
  unfold hausdorffWeight
  rw [forwardDifference_iterate_eq_sum, ← mul_assoc, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j ≤ N - k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hsign := neg_one_mul_pow_sub (N - k) j hj'
  calc
    ((N.choose k : ℝ) * (-1) ^ (N - k)) *
        ((((N - k).choose j : ℝ) * (-1) ^ (N - k - j)) * s (k + j)) =
        (N.choose k : ℝ) * ((N - k).choose j : ℝ) *
          ((-1) ^ (N - k) * (-1) ^ (N - k - j)) * s (k + j) := by ring
    _ = (N.choose k : ℝ) * ((N - k).choose j : ℝ) * (-1) ^ j * s (k + j) := by
      rw [hsign]

/-- The Bernstein weights of level `N` sum to the total mass `s 0`. -/
private lemma sum_hausdorffWeight (s : ℕ → ℝ) (N : ℕ) :
    ∑ k ∈ Finset.range (N + 1), hausdorffWeight s N k = s 0 := by
  have hsum :
      ∑ k ∈ Finset.range (N + 1), hausdorffWeight s N k =
        ∑ k ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N - k + 1),
          (N.choose k : ℝ) * ((N - k).choose j : ℝ) * (-1 : ℝ) ^ j * s (k + j) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    exact hausdorffWeight_eq_sum s N k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
  rw [hsum, sum_triangle]
  have hindex :
      ∑ m ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (m + 1),
          (N.choose k : ℝ) * ((N - k).choose (m - k) : ℝ) *
            (-1 : ℝ) ^ (m - k) * s (k + (m - k)) =
        ∑ m ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (m + 1),
          (N.choose k : ℝ) * ((N - k).choose (m - k) : ℝ) *
            (-1 : ℝ) ^ (m - k) * s m := by
    refine Finset.sum_congr rfl fun m _hm => Finset.sum_congr rfl fun k hk => ?_
    rw [Nat.add_sub_of_le (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))]
  rw [hindex]
  have hterm :
      ∑ m ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (m + 1),
          (N.choose k : ℝ) * ((N - k).choose (m - k) : ℝ) *
            (-1 : ℝ) ^ (m - k) * s m =
        ∑ m ∈ Finset.range (N + 1),
          (N.choose m : ℝ) * s m * (0 : ℝ) ^ m := by
    refine Finset.sum_congr rfl fun m hm => ?_
    have hrewrite : ∀ k ∈ Finset.range (m + 1),
        (N.choose k : ℝ) * ((N - k).choose (m - k) : ℝ) * (-1 : ℝ) ^ (m - k) * s m =
          (N.choose m : ℝ) * s m *
            ((m.choose k : ℝ) * (-1 : ℝ) ^ (m - k)) := by
      intro k hk
      have hk' : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have hchoose :
          N.choose k * (N - k).choose (m - k) = N.choose m * m.choose k := by
        simpa using (Nat.choose_mul (n := N) (k := m) (s := k) hk').symm
      calc
        (N.choose k : ℝ) * ((N - k).choose (m - k) : ℝ) * (-1) ^ (m - k) * s m =
            ((N.choose k * (N - k).choose (m - k) : ℕ) : ℝ) *
              (-1) ^ (m - k) * s m := by simp [Nat.cast_mul]
        _ = ((N.choose m * m.choose k : ℕ) : ℝ) * (-1) ^ (m - k) * s m := by
          rw [hchoose]
        _ = (N.choose m : ℝ) * s m * ((m.choose k : ℝ) * (-1) ^ (m - k)) := by
          simp [Nat.cast_mul]
          ring
    rw [Finset.sum_congr rfl hrewrite, ← Finset.mul_sum, sum_choose_neg]
  rw [hterm]
  have hzero : ∀ m ∈ Finset.range (N + 1), m ≠ 0 →
      (N.choose m : ℝ) * s m * (0 : ℝ) ^ m = 0 := by
    intro m hm hm0
    simp [zero_pow hm0]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro m hm hm0
    exact hzero m hm hm0
  · intro h0
    exact absurd (Finset.mem_range.mpr (Nat.succ_pos N)) h0

/-- Falling moments of the Bernstein weights recover scaled sequence values. -/
private lemma sum_hausdorffWeight_mul_choose (s : ℕ → ℝ) (N j : ℕ) :
    ∑ k ∈ Finset.range (N + 1), hausdorffWeight s N k * (k.choose j : ℝ) =
      (N.choose j : ℝ) * s j := by
  have hsum :
      ∑ k ∈ Finset.range (N + 1), hausdorffWeight s N k * (k.choose j : ℝ) =
        ∑ k ∈ Finset.range (N + 1),
          (∑ i ∈ Finset.range (N - k + 1),
            (N.choose k : ℝ) * ((N - k).choose i : ℝ) * (-1 : ℝ) ^ i * s (k + i)) *
            (k.choose j : ℝ) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [hausdorffWeight_eq_sum s N k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))]
  rw [hsum]
  simp_rw [Finset.sum_mul]
  have htri := sum_triangle N (fun k i =>
    (N.choose k : ℝ) * ((N - k).choose i : ℝ) * (-1 : ℝ) ^ i * s (k + i) *
      (k.choose j : ℝ))
  rw [htri]
  have hindex :
      ∑ m ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (m + 1),
          (N.choose k : ℝ) * ((N - k).choose (m - k) : ℝ) *
            (-1 : ℝ) ^ (m - k) * s (k + (m - k)) * (k.choose j : ℝ) =
        ∑ m ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (m + 1),
          (N.choose k : ℝ) * ((N - k).choose (m - k) : ℝ) *
            (-1 : ℝ) ^ (m - k) * s m * (k.choose j : ℝ) := by
    refine Finset.sum_congr rfl fun m _hm => Finset.sum_congr rfl fun k hk => ?_
    rw [Nat.add_sub_of_le (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))]
  rw [hindex]
  have hterm :
      ∑ m ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (m + 1),
          (N.choose k : ℝ) * ((N - k).choose (m - k) : ℝ) *
            (-1 : ℝ) ^ (m - k) * s m * (k.choose j : ℝ) =
        ∑ m ∈ Finset.range (N + 1),
          (N.choose m : ℝ) * s m *
            (∑ k ∈ Finset.range (m + 1),
              (m.choose k : ℝ) * (k.choose j : ℝ) * (-1 : ℝ) ^ (m - k)) := by
    refine Finset.sum_congr rfl fun m _hm => ?_
    have hrewrite : ∀ k ∈ Finset.range (m + 1),
        (N.choose k : ℝ) * ((N - k).choose (m - k) : ℝ) * (-1 : ℝ) ^ (m - k) * s m *
            (k.choose j : ℝ) =
          (N.choose m : ℝ) * s m *
            ((m.choose k : ℝ) * (k.choose j : ℝ) * (-1 : ℝ) ^ (m - k)) := by
      intro k hk
      have hk' : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have hchoose :
          N.choose k * (N - k).choose (m - k) = N.choose m * m.choose k := by
        simpa using (Nat.choose_mul (n := N) (k := m) (s := k) hk').symm
      calc
        (N.choose k : ℝ) * ((N - k).choose (m - k) : ℝ) * (-1) ^ (m - k) * s m *
            (k.choose j : ℝ) =
            ((N.choose k * (N - k).choose (m - k) : ℕ) : ℝ) *
              (-1) ^ (m - k) * s m * (k.choose j : ℝ) := by simp [Nat.cast_mul]
        _ = ((N.choose m * m.choose k : ℕ) : ℝ) * (-1) ^ (m - k) * s m *
              (k.choose j : ℝ) := by rw [hchoose]
        _ = (N.choose m : ℝ) * s m *
              ((m.choose k : ℝ) * (k.choose j : ℝ) * (-1) ^ (m - k)) := by
          simp [Nat.cast_mul]
          ring
    rw [Finset.sum_congr rfl hrewrite, ← Finset.mul_sum]
  rw [hterm]
  simp_rw [sum_choose_mul_choose_neg]
  have hsingle :
      ∑ m ∈ Finset.range (N + 1),
          (N.choose m : ℝ) * s m * (if m = j then (1 : ℝ) else 0) =
        if j ≤ N then (N.choose j : ℝ) * s j else 0 := by
    rw [Finset.sum_eq_single j]
    · by_cases hj : j ≤ N
      · simp [hj]
      · simp [hj, Nat.choose_eq_zero_of_lt (lt_of_not_ge hj)]
    · intro m hm hmj
      simp [hmj]
    · intro hjmem
      have hjN : N < j := by
        have : ¬ j < N + 1 := by simpa [Finset.mem_range] using hjmem
        omega
      simp [Nat.choose_eq_zero_of_lt hjN]
  rw [hsingle]
  by_cases hj : j ≤ N
  · simp [hj]
  · simp [hj, Nat.choose_eq_zero_of_lt (lt_of_not_ge hj)]

/-- Power moments of the Bernstein weights, via Stirling numbers of the second kind. -/
private lemma sum_hausdorffWeight_mul_pow (s : ℕ → ℝ) (N m : ℕ) :
    ∑ k ∈ Finset.range (N + 1), hausdorffWeight s N k * ((k : ℝ) / N) ^ m =
      ∑ j ∈ Finset.range (m + 1),
        (Nat.stirlingSecond m j : ℝ) * (N.descFactorial j : ℝ) / (N : ℝ) ^ m * s j := by
  have hdiv : ∀ k : ℕ, ((k : ℝ) / N) ^ m = (k : ℝ) ^ m * ((N : ℝ) ^ m)⁻¹ :=
    fun k => by rw [div_pow, div_eq_mul_inv]
  simp_rw [hdiv, ← mul_assoc, ← Finset.sum_mul]
  have hpow (k : ℕ) : (k : ℝ) ^ m =
      ∑ j ∈ Finset.range (m + 1),
        (Nat.stirlingSecond m j : ℝ) * ((k.descFactorial j : ℕ) : ℝ) := by
    rw [← Nat.cast_pow, Nat.pow_eq_sum_stirlingSecond_mul_descFactorial]
    simp [Nat.cast_sum, Nat.cast_mul]
  have hsum :
      ∑ k ∈ Finset.range (N + 1), hausdorffWeight s N k * (k : ℝ) ^ m =
        ∑ j ∈ Finset.range (m + 1),
          (Nat.stirlingSecond m j : ℝ) * (N.descFactorial j : ℝ) * s j := by
    rw [Finset.sum_congr rfl (fun k (_ : k ∈ Finset.range (N + 1)) =>
      congrArg (fun t => hausdorffWeight s N k * t) (hpow k))]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _hj => ?_
    have hdesc (k : ℕ) : (k.descFactorial j : ℝ) =
        (j.factorial : ℝ) * (k.choose j : ℝ) := by
      simpa [Nat.cast_mul] using
        congrArg (Nat.cast : ℕ → ℝ) (Nat.descFactorial_eq_factorial_mul_choose k j)
    simp_rw [hdesc]
    have hpull (k : ℕ) :
        hausdorffWeight s N k *
            ((Nat.stirlingSecond m j : ℝ) * ((j.factorial : ℝ) * (k.choose j : ℝ))) =
          (Nat.stirlingSecond m j : ℝ) * (j.factorial : ℝ) *
            (hausdorffWeight s N k * (k.choose j : ℝ)) := by ring
    simp_rw [hpull, ← Finset.mul_sum, sum_hausdorffWeight_mul_choose s N j]
    ring
  rw [hsum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _hj => ?_
  rw [div_eq_mul_inv]
  ring

/-- Nodes of the Bernstein grid lie in `[0,1]`, with the `N = 0` node read as `0`. -/
private lemma div_mem_Icc (N k : ℕ) (hk : k ≤ N) :
    (k : ℝ) / N ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _), ?_⟩
  rcases eq_or_ne N 0 with rfl | hN
  · simp [Nat.le_zero.mp hk]
  · rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hN)]
    exact_mod_cast hk

/-- Total mass of a completely monotone Bernstein approximant. -/
private lemma hausdorffApproximant_univ {s : ℕ → ℝ}
    (hs : IsCompletelyMonotoneSequence s) (N : ℕ) :
    hausdorffApproximant s N Set.univ = ENNReal.ofReal (s 0) := by
  unfold hausdorffApproximant
  rw [Measure.finsetSum_apply]
  simp_rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply_of_mem (Set.mem_univ _), mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => hs.hausdorffWeight_nonneg N k)]
  exact congrArg ENNReal.ofReal (sum_hausdorffWeight s N)

/-- A completely monotone Bernstein approximant is a finite measure. -/
private lemma hausdorffApproximant_finite {s : ℕ → ℝ}
    (hs : IsCompletelyMonotoneSequence s) (N : ℕ) :
    IsFiniteMeasure (hausdorffApproximant s N) :=
  ⟨by simp [hausdorffApproximant_univ hs N]⟩

/-- Every Bernstein node lies in `[0,1]`, so the approximant is supported there. -/
private lemma hausdorffApproximant_compl {s : ℕ → ℝ}
    (_hs : IsCompletelyMonotoneSequence s) (N : ℕ) :
    hausdorffApproximant s N (Set.Icc (0 : ℝ) 1)ᶜ = 0 := by
  unfold hausdorffApproximant
  rw [Measure.finsetSum_apply]
  refine Finset.sum_eq_zero fun k hk => ?_
  have hk' : k ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [Measure.smul_apply, Measure.dirac_apply, Set.indicator_of_notMem]
  · simp
  · exact Set.notMem_compl_iff.mpr (div_mem_Icc N k hk')

/-- Every real function is integrable against a Bernstein approximant. -/
private lemma integrable_hausdorffApproximant {s : ℕ → ℝ}
    (hs : IsCompletelyMonotoneSequence s) (N : ℕ) (f : ℝ → ℝ) :
    Integrable f (hausdorffApproximant s N) := by
  have : IsFiniteMeasure (hausdorffApproximant s N) := hausdorffApproximant_finite hs N
  unfold hausdorffApproximant
  rw [integrable_finsetSum_measure]
  intro k hk
  exact (integrable_dirac (f := f) (a := (k : ℝ) / N) (by simp)).smul_measure
    ENNReal.ofReal_ne_top

/-- Integration against a Bernstein approximant is the corresponding finite weighted sum. -/
private lemma integral_hausdorffApproximant {s : ℕ → ℝ}
    (hs : IsCompletelyMonotoneSequence s) (N : ℕ) (f : ℝ → ℝ) :
    ∫ x, f x ∂hausdorffApproximant s N =
      ∑ k ∈ Finset.range (N + 1), hausdorffWeight s N k * f ((k : ℝ) / N) := by
  have hf := integrable_hausdorffApproximant hs N f
  unfold hausdorffApproximant at hf ⊢
  rw [integral_finsetSum_measure ?_]
  · simp_rw [integral_smul_measure, integral_dirac,
      ENNReal.toReal_ofReal (hs.hausdorffWeight_nonneg N _), smul_eq_mul]
  · rw [integrable_finsetSum_measure] at hf
    exact hf

/-- Moments of the approximants are the normalized Stirling expansion of the weights. -/
private lemma integral_pow_hausdorffApproximant {s : ℕ → ℝ}
    (hs : IsCompletelyMonotoneSequence s) (N m : ℕ) :
    ∫ x, x ^ m ∂hausdorffApproximant s N =
      ∑ j ∈ Finset.range (m + 1),
        (Nat.stirlingSecond m j : ℝ) * (N.descFactorial j : ℝ) / (N : ℝ) ^ m * s j := by
  rw [integral_hausdorffApproximant hs N (fun x => x ^ m), sum_hausdorffWeight_mul_pow]

/-- For each fixed order, Bernstein moments converge to the original sequence. -/
private lemma tendsto_integral_pow_hausdorffApproximant {s : ℕ → ℝ}
    (hs : IsCompletelyMonotoneSequence s) (m : ℕ) :
    Tendsto (fun N : ℕ => ∫ x, x ^ m ∂hausdorffApproximant s N) atTop (𝓝 (s m)) := by
  simp_rw [integral_pow_hausdorffApproximant hs _ m]
  have hterm (j : ℕ) (hj : j ∈ Finset.range (m + 1)) :
      Tendsto (fun N : ℕ =>
          (Nat.stirlingSecond m j : ℝ) * (N.descFactorial j : ℝ) / (N : ℝ) ^ m * s j)
        atTop (𝓝 (if j = m then s m else 0)) := by
    have hjle : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hz : ∀ᶠ N : ℕ in atTop, (N ^ j : ℝ) ≠ 0 := by
      filter_upwards [eventually_gt_atTop 0] with N hN
      exact_mod_cast pow_ne_zero j hN.ne'
    have hratio :
        Tendsto (fun N : ℕ => (N.descFactorial j : ℝ) / (N : ℝ) ^ j) atTop (𝓝 1) := by
      refine ((Asymptotics.isEquivalent_iff_tendsto_one hz).mp
        (isEquivalent_descFactorial j)).congr fun N => ?_
      simp [Pi.div_apply]
    by_cases hjm : j = m
    · subst hjm
      rw [ite_eq_left rfl]
      simp only [Nat.stirlingSecond_self, Nat.cast_one, one_mul]
      simpa [one_mul] using hratio.mul_const (s j)
    · have hlt : j < m := lt_of_le_of_ne hjle hjm
      have hdecay :
          Tendsto (fun N : ℕ => (1 : ℝ) / (N : ℝ) ^ (m - j)) atTop (𝓝 0) := by
        refine (tendsto_const_div_pow (1 : ℝ) (m - j) (Nat.sub_ne_zero_of_lt hlt)).congr
          fun N => ?_
        simp
      have heq :
          (fun N : ℕ =>
              ((N.descFactorial j : ℝ) / (N : ℝ) ^ j) *
                ((1 : ℝ) / (N : ℝ) ^ (m - j))) =ᶠ[atTop]
            fun N : ℕ => (N.descFactorial j : ℝ) / (N : ℝ) ^ m := by
        filter_upwards with N
        have hpow : (N : ℝ) ^ m = (N : ℝ) ^ j * (N : ℝ) ^ (m - j) := by
          rw [← pow_add, Nat.add_sub_of_le hjle]
        rw [div_mul_div_comm, mul_one, ← hpow]
      have hmul := hratio.mul hdecay
      simp only [one_mul] at hmul
      have hprod :
          Tendsto (fun N : ℕ => (N.descFactorial j : ℝ) / (N : ℝ) ^ m) atTop (𝓝 0) :=
        Filter.Tendsto.congr' heq hmul
      simpa [hjm, mul_div_assoc] using
        (hprod.const_mul (Nat.stirlingSecond m j : ℝ)).mul_const (s j)
  have hsum := tendsto_finsetSum (Finset.range (m + 1)) hterm
  have hrhs :
      ∑ j ∈ Finset.range (m + 1), (if j = m then s m else (0 : ℝ)) = s m := by
    classical
    rw [Finset.sum_eq_single m]
    · simp
    · intro j hj hjm
      simp [hjm]
    · intro hm
      exact absurd (Finset.mem_range.mpr m.lt_succ_self) hm
  simpa [hrhs] using hsum

/-! ### Representation and uniqueness -/

/-- A measurable function bounded on the support of a finite measure on `[0,1]` is integrable. -/
private lemma integrable_of_bound_on_Icc {μ : Measure ℝ} (hfin : IsFiniteMeasure μ)
    (hsupp : μ (Set.Icc (0 : ℝ) 1)ᶜ = 0) {f : ℝ → ℝ} (hf : AEStronglyMeasurable f μ)
    {C : ℝ} (hbound : ∀ x ∈ Set.Icc (0 : ℝ) 1, ‖f x‖ ≤ C) :
    Integrable f μ := by
  have := hfin
  refine (MemLp.of_bound (p := 1) hf C ?_).integrable le_rfl
  filter_upwards [(mem_ae_iff).mpr hsupp] with x hx
  exact hbound x hx

/-- Monomials are integrable against a representing measure. -/
private lemma integrable_pow_of_represents {μ : Measure ℝ} {s : ℕ → ℝ}
    (hμ : RepresentsHausdorffMoments μ s) (n k : ℕ) :
    Integrable (fun x : ℝ => x ^ n * (x - 1) ^ k) μ := by
  apply integrable_of_bound_on_Icc hμ.1 hμ.2.1
    (Continuous.aestronglyMeasurable (by fun_prop))
  intro x hx
  have habs_x : ‖x‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hx.1]
    exact hx.2
  have habs_sub : ‖x - 1‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hx.2), neg_sub]
    exact sub_le_self 1 hx.1
  rw [norm_mul, norm_pow, norm_pow]
  exact (mul_le_of_le_one_left (pow_nonneg (norm_nonneg _) _)
      (pow_le_one₀ (norm_nonneg _) habs_x)).trans
    (pow_le_one₀ (norm_nonneg _) habs_sub)

/-- Forward differences of a represented sequence are moments of `x ^ n * (x - 1) ^ k`. -/
private lemma forwardDifference_iterate_eq_integral {μ : Measure ℝ} {s : ℕ → ℝ}
    (hμ : RepresentsHausdorffMoments μ s) (k n : ℕ) :
    (forwardDifference^[k] s) n = ∫ x, x ^ n * (x - 1) ^ k ∂μ := by
  induction k generalizing n with
  | zero =>
    simp [hμ.2.2 n]
  | succ k ih =>
    rw [Function.iterate_succ_apply', forwardDifference, ih (n + 1), ih n]
    rw [← integral_sub (integrable_pow_of_represents hμ (n + 1) k)
      (integrable_pow_of_represents hμ n k)]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    ring_nf

/-- A representing measure forces the sequence to be completely monotone. -/
private lemma isCompletelyMonotoneSequence_of_represents {μ : Measure ℝ} {s : ℕ → ℝ}
    (hμ : RepresentsHausdorffMoments μ s) : IsCompletelyMonotoneSequence s := by
  intro n k
  rw [forwardDifference_iterate_eq_integral hμ k n, ← integral_const_mul]
  have hint :
      ∫ x, (-1 : ℝ) ^ k * (x ^ n * (x - 1) ^ k) ∂μ =
        ∫ x, x ^ n * (1 - x) ^ k ∂μ := by
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    calc
      (-1 : ℝ) ^ k * (x ^ n * (x - 1) ^ k) =
          x ^ n * ((-1) ^ k * (x - 1) ^ k) := by ring
      _ = x ^ n * (((-1) * (x - 1)) ^ k) := by rw [mul_pow]
      _ = x ^ n * (1 - x) ^ k := by ring
  rw [hint]
  refine integral_nonneg_of_ae ?_
  filter_upwards [(mem_ae_iff).mpr hμ.2.1] with x hx
  exact mul_nonneg (pow_nonneg hx.1 _) (pow_nonneg (sub_nonneg.mpr hx.2) _)

/-- Two finite measures on `[0,1]` with the same moments integrate every continuous function
equally. -/
private lemma integral_continuous_eq_of_same_moments
    {μ ν : Measure (Set.Icc (0 : ℝ) 1)} {s : ℕ → ℝ}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ n, ∫ x, (x : ℝ) ^ n ∂μ = s n)
    (hν : ∀ n, ∫ x, (x : ℝ) ^ n ∂ν = s n)
    {φ : Set.Icc (0 : ℝ) 1 → ℝ} (hφ : Continuous φ) :
    ∫ x, φ x ∂μ = ∫ x, φ x ∂ν := by
  let I : Set ℝ := Set.Icc 0 1
  let _ : CompactSpace I := isCompact_iff_compactSpace.mp isCompact_Icc
  have hs0 : 0 ≤ s 0 := by
    have h := hμ 0
    simp only [pow_zero] at h
    rw [← h]
    simp
  apply eq_of_forall_dist_le
  intro δ hδ
  let ε : ℝ := if s 0 = 0 then 1 else δ / (2 * s 0)
  have hε : 0 < ε := by
    by_cases h0 : s 0 = 0
    · simp [ε, h0]
    · have hpos : 0 < s 0 := lt_of_le_of_ne hs0 (Ne.symm h0)
      simp only [ε, h0, ite_false]
      positivity
  let φc : C(I, ℝ) := ⟨φ, hφ⟩
  have hclosure :
      closure ((polynomialFunctions I : Subalgebra ℝ C(I, ℝ)) : Set C(I, ℝ)) = Set.univ := by
    rw [← Subalgebra.topologicalClosure_coe, polynomialFunctions.topologicalClosure]
    simp
  obtain ⟨ψ, hψmem, hψdist⟩ :=
    Metric.mem_closure_iff.mp (by rw [hclosure]; exact Set.mem_univ φc) ε hε
  rw [polynomialFunctions_coe] at hψmem
  obtain ⟨p, rfl⟩ := hψmem
  have hpt : ∀ x, ‖(p.toContinuousMapOn I) x - φc x‖ ≤ ε := by
    have hnorm : ‖p.toContinuousMapOn I - φc‖ < ε := by
      rw [norm_sub_rev]
      simpa [dist_eq_norm] using hψdist
    intro x
    exact le_of_lt
      ((ContinuousMap.norm_lt_iff (p.toContinuousMapOn I - φc) hε).mp hnorm x)
  have hpoly (ρ : Measure I) [IsFiniteMeasure ρ]
      (hρ : ∀ n, ∫ x, (x : ℝ) ^ n ∂ρ = s n) :
      ∫ x, p.eval (x : ℝ) ∂ρ =
        ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * s i := by
    have heval : (fun x : I => p.eval (x : ℝ)) =
        fun x : I => ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * (x : ℝ) ^ i := by
      funext x
      simpa using p.eval_eq_sum_range (x : ℝ)
    rw [heval, integral_finsetSum]
    · refine Finset.sum_congr rfl fun i hi => ?_
      rw [integral_const_mul, hρ]
    · intro i hi
      refine Integrable.const_mul ?_ (p.coeff i)
      have : CompactSpace I := isCompact_iff_compactSpace.mp isCompact_Icc
      refine (MemLp.of_bound (p := 1)
        (Continuous.aestronglyMeasurable (by fun_prop : Continuous fun x : I => (x : ℝ) ^ i))
        1 ?_).integrable le_rfl
      filter_upwards with x
      rw [Real.norm_eq_abs, abs_pow, abs_of_nonneg x.2.1]
      exact pow_le_one₀ x.2.1 x.2.2
  have herr (ρ : Measure I) [IsFiniteMeasure ρ]
      (_hρ : ∀ n, ∫ x, (x : ℝ) ^ n ∂ρ = s n) :
      |∫ x, φ x ∂ρ - ∫ x, p.eval (x : ℝ) ∂ρ| ≤ ε * ρ.real Set.univ := by
    have : CompactSpace I := isCompact_iff_compactSpace.mp isCompact_Icc
    have hφi : Integrable φ ρ := by
      let φb := BoundedContinuousFunction.mkOfCompact φc
      refine (MemLp.of_bound (p := 1) hφ.aestronglyMeasurable ‖φb‖
        (ae_of_all _ fun x => φb.norm_coe_le_norm x)).integrable le_rfl
    have hpi : Integrable (fun x : I => p.eval (x : ℝ)) ρ := by
      refine (MemLp.of_bound (p := 1)
        (Continuous.aestronglyMeasurable
          (by fun_prop : Continuous fun x : I => p.eval (x : ℝ)))
        ‖p.toContinuousMapOn I‖
        (ae_of_all _ fun x => ?_)).integrable le_rfl
      simpa [Polynomial.toContinuousMapOn_apply, Polynomial.toContinuousMap_apply] using
        ContinuousMap.norm_coe_le_norm (p.toContinuousMapOn I) x
    have hle := norm_integral_le_of_norm_le_const (μ := ρ)
      (f := fun x : I => φ x - p.eval (x : ℝ)) (C := ε)
      (ae_of_all _ fun x => ?_)
    · rw [← integral_sub hφi hpi]
      simpa [Real.norm_eq_abs] using hle
    · simpa [φc, norm_sub_rev, Polynomial.toContinuousMapOn_apply,
        Polynomial.toContinuousMap_apply] using hpt x
  have hmassμ : μ.real Set.univ = s 0 := by
    have h := hμ 0
    simp only [pow_zero] at h
    simpa [integral_const, smul_eq_mul] using h
  have hmassν : ν.real Set.univ = s 0 := by
    have h := hν 0
    simp only [pow_zero] at h
    simpa [integral_const, smul_eq_mul] using h
  have hpeq : ∫ x, p.eval (x : ℝ) ∂μ = ∫ x, p.eval (x : ℝ) ∂ν := by
    rw [hpoly μ hμ, hpoly ν hν]
  have hbound :
      dist (∫ x, φ x ∂μ) (∫ x, φ x ∂ν) ≤ 2 * ε * s 0 := by
    rw [Real.dist_eq]
    calc
      |∫ x, φ x ∂μ - ∫ x, φ x ∂ν| ≤
          |∫ x, φ x ∂μ - ∫ x, p.eval (x : ℝ) ∂μ| +
            |∫ x, p.eval (x : ℝ) ∂ν - ∫ x, φ x ∂ν| := by
        have hmid : ∫ x, p.eval (x : ℝ) ∂μ = ∫ x, p.eval (x : ℝ) ∂ν := hpeq
        rw [← hmid]
        exact abs_sub_le _ _ _
      _ ≤ ε * μ.real Set.univ + ε * ν.real Set.univ :=
        add_le_add (herr μ hμ) (by simpa [abs_sub_comm] using herr ν hν)
      _ = 2 * ε * s 0 := by rw [hmassμ, hmassν]; ring
  refine hbound.trans ?_
  by_cases h0 : s 0 = 0
  · simp only [ε, h0, mul_zero, ite_true]
    exact hδ.le
  · have hpos : 0 < s 0 := lt_of_le_of_ne hs0 (Ne.symm h0)
    have hεeq : 2 * ε * s 0 = δ := by
      simp only [ε, h0, ite_false]
      field_simp
    exact le_of_eq hεeq

/-- Finite measures on `[0,1]` are determined by their moments. -/
private lemma eq_of_representsHausdorffMoments {μ ν : Measure ℝ} {s : ℕ → ℝ}
    (hμ : RepresentsHausdorffMoments μ s) (hν : RepresentsHausdorffMoments ν s) : μ = ν := by
  let I : Set ℝ := Set.Icc 0 1
  let μI : Measure I := μ.comap Subtype.val
  let νI : Measure I := ν.comap Subtype.val
  have : IsFiniteMeasure μ := hμ.1
  have : IsFiniteMeasure ν := hν.1
  have : IsFiniteMeasure μI := inferInstance
  have : IsFiniteMeasure νI := inferInstance
  have hmomμ : ∀ n, ∫ x, (x : ℝ) ^ n ∂μI = s n := by
    intro n
    dsimp only [μI]
    rw [integral_subtype_comap (μ := μ) measurableSet_Icc (fun y => y ^ n)]
    rw [Measure.restrict_eq_self_of_ae_mem ((mem_ae_iff).mpr hμ.2.1), hμ.2.2]
  have hmomν : ∀ n, ∫ x, (x : ℝ) ^ n ∂νI = s n := by
    intro n
    dsimp only [νI]
    rw [integral_subtype_comap (μ := ν) measurableSet_Icc (fun y => y ^ n)]
    rw [Measure.restrict_eq_self_of_ae_mem ((mem_ae_iff).mpr hν.2.1), hν.2.2]
  have hI : μI = νI := by
    apply ext_of_forall_integral_eq_of_IsFiniteMeasure
    intro f
    exact integral_continuous_eq_of_same_moments hmomμ hmomν f.continuous
  have hmap : μI.map Subtype.val = νI.map Subtype.val := congrArg (Measure.map Subtype.val) hI
  rw [map_comap_subtype_coe measurableSet_Icc, map_comap_subtype_coe measurableSet_Icc] at hmap
  rw [Measure.restrict_eq_self_of_ae_mem ((mem_ae_iff).mpr hμ.2.1),
    Measure.restrict_eq_self_of_ae_mem ((mem_ae_iff).mpr hν.2.1)] at hmap
  exact hmap

/-- Continuous cutoff of `x ↦ x ^ m`, equal to the monomial on `[0,1]`. -/
private def hausdorffMomentTest (m : ℕ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x : ℝ => (min (max x 0) 1) ^ m)
    (by fun_prop)
    1
    (by
      intro x
      have h0 : 0 ≤ min (max x 0) 1 := le_min (le_max_right _ _) zero_le_one
      have h1 : min (max x 0) 1 ≤ 1 := min_le_right _ _
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg h0 _)]
      exact pow_le_one₀ h0 h1)

/-- On `[0,1]` the cutoff monomial agrees with `x ↦ x ^ m`. -/
private lemma hausdorffMomentTest_eq_on_Icc (m : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    hausdorffMomentTest m x = x ^ m := by
  simp [hausdorffMomentTest, max_eq_left hx.1, min_eq_left hx.2]

/-- Every completely monotone sequence is the moment sequence of some finite measure on `[0,1]`. -/
private lemma exists_represents_of_isCompletelyMonotone {s : ℕ → ℝ}
    (hs : IsCompletelyMonotoneSequence s) :
    ∃ μ : Measure ℝ, RepresentsHausdorffMoments μ s := by
  let C : ℝ≥0 := Real.toNNReal (s 0)
  let K : Set ℝ := Set.Icc 0 1
  let T : Set (FiniteMeasure ℝ) := {μ | μ.mass ≤ C ∧ μ Kᶜ = 0}
  have hT : IsCompact T := isCompact_setOfPred_finiteMeasure_le_of_isCompact C isCompact_Icc
  let μs : ℕ → FiniteMeasure ℝ := fun N =>
    ⟨hausdorffApproximant s N, hausdorffApproximant_finite hs N⟩
  have hmem : ∀ N, μs N ∈ T := by
    intro N
    refine ⟨?_, ?_⟩
    · have huniv := hausdorffApproximant_univ hs N
      simp only [FiniteMeasure.mass, μs, FiniteMeasure.mk_apply, huniv, ENNReal.ofReal,
        ENNReal.toNNReal_coe, C]
      exact le_rfl
    · rw [FiniteMeasure.null_iff_toMeasure_null]
      simpa [μs, K] using hausdorffApproximant_compl hs N
  let u : Ultrafilter ℕ := Ultrafilter.of atTop
  have hu : (u : Filter ℕ) ≤ atTop := Ultrafilter.of_le _
  let uf : Ultrafilter (FiniteMeasure ℝ) := u.map μs
  have hTmem : T ∈ uf := by
    rw [Ultrafilter.mem_map]
    exact univ_mem' hmem
  obtain ⟨μF, hμFT, hlim⟩ := hT.ultrafilter_le_nhds' uf hTmem
  have htend : Tendsto μs u (𝓝 μF) := by
    change Filter.map μs ↑u ≤ 𝓝 μF
    simpa [uf, Ultrafilter.coe_map] using hlim
  refine ⟨(μF : Measure ℝ), inferInstance, ?_, ?_⟩
  · rw [← FiniteMeasure.null_iff_toMeasure_null]
    exact hμFT.2
  · intro n
    have htest : ∀ N, ∫ x, hausdorffMomentTest n x ∂(μs N : Measure ℝ) =
        ∫ x, x ^ n ∂(μs N : Measure ℝ) := by
      intro N
      apply integral_congr_ae
      filter_upwards [(mem_ae_iff).mpr (hausdorffApproximant_compl hs N)] with x hx
      exact hausdorffMomentTest_eq_on_Icc n hx
    have htend_test :
        Tendsto (fun N => ∫ x, hausdorffMomentTest n x ∂(μs N : Measure ℝ)) u
          (𝓝 (∫ x, hausdorffMomentTest n x ∂(μF : Measure ℝ))) :=
      (FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp htend) (hausdorffMomentTest n)
    have hmoment := (tendsto_integral_pow_hausdorffApproximant hs n).mono_left hu
    have hmoment' :
        Tendsto (fun N => ∫ x, hausdorffMomentTest n x ∂(μs N : Measure ℝ)) u (𝓝 (s n)) := by
      exact hmoment.congr fun N => (htest N).symm
    have hint_test : ∫ x, hausdorffMomentTest n x ∂(μF : Measure ℝ) = s n :=
      tendsto_nhds_unique htend_test hmoment'
    have hint_pow : Integrable (fun x : ℝ => x ^ n) (μF : Measure ℝ) := by
      apply integrable_of_bound_on_Icc (FiniteMeasure.isFiniteMeasure μF)
        (by rw [← FiniteMeasure.null_iff_toMeasure_null]; exact hμFT.2)
        (Continuous.aestronglyMeasurable (by fun_prop))
      intro x hx
      rw [Real.norm_eq_abs, abs_pow, abs_of_nonneg hx.1]
      exact pow_le_one₀ hx.1 hx.2
    rw [← hint_test]
    apply integral_congr_ae
    filter_upwards [(mem_ae_iff).mpr (by
      rw [← FiniteMeasure.null_iff_toMeasure_null]
      exact hμFT.2)] with x hx
    exact (hausdorffMomentTest_eq_on_Icc n hx).symm

/-- **48.34**: the Hausdorff existence and uniqueness theorem, including the zero measure. -/
theorem isCompletelyMonotoneSequence_iff_existsUnique_measure (s : ℕ → ℝ) :
    IsCompletelyMonotoneSequence s ↔ ∃! μ : Measure ℝ, RepresentsHausdorffMoments μ s := by
  constructor
  · intro hs
    obtain ⟨μ, hμ⟩ := exists_represents_of_isCompletelyMonotone hs
    refine ⟨μ, hμ, ?_⟩
    intro ν hν
    exact eq_of_representsHausdorffMoments hν hμ
  · rintro ⟨μ, hμ, _⟩
    exact isCompletelyMonotoneSequence_of_represents hμ

end CKMA
