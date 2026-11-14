/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Topology.MetricSpace.Holder
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic.Continuity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Dyadic sewing limit and midpoint additivity

Ordered partitions, the sewing constant, and the dyadic primitive used to prove the
sewing lemma. Increments may repeat nodes. The sewn primitive is midpoint-additive and
continuous on the sewing triangle.

## Main definitions

* `CKMA.OrderedIntervalPartition`: ordered finite partition of `[a, b]`.
* `CKMA.sewingConstant`: geometric sewing constant `(1 - 2 ^ (1 - γ))⁻¹`.
* `CKMA.Sewing.dyadicNode`, `CKMA.Sewing.dyadicIncrement`, `CKMA.Sewing.sewnIncrement`:
  dyadic partition nodes, dyadic increment sums, and the dyadic sewing limit.

## Main results

* `CKMA.Sewing.tendsto_dyadicIncrement`: dyadic increment sums converge to `sewnIncrement`.
* `CKMA.Sewing.norm_sewnIncrement_sub`: remainder bound for `sewnIncrement`.
* `CKMA.Sewing.continuousOn_sewnIncrement`: `sewnIncrement` is continuous on `sewingTriangle a b`.

## Notation

No new notation is introduced in this file.
-/

@[expose] public section

noncomputable section

namespace CKMA

open scoped BigOperators NNReal ENNReal

/-- An ordered finite partition, allowing repeated nodes and the degenerate interval. -/
structure OrderedIntervalPartition (a b : ℝ) where
  /-- Number of increments. -/
  size : ℕ
  /-- Nodes including both endpoints. -/
  node : Fin (size + 1) → ℝ
  /-- Nodes are ordered. -/
  monotone_node : Monotone node
  /-- Left endpoint. -/
  node_zero : node 0 = a
  /-- Right endpoint. -/
  node_last : node (Fin.last size) = b

/-- The maximal partition width. -/
def OrderedIntervalPartition.mesh {a b : ℝ} (π : OrderedIntervalPartition a b) : ℝ≥0 :=
  Finset.univ.sup (fun i : Fin π.size ↦ (π.node i.succ - π.node i.castSucc).toNNReal)

/-- The sum of two-parameter increments along a partition. -/
def OrderedIntervalPartition.incrementSum {a b : ℝ} {E : Type*} [AddCommMonoid E]
    (π : OrderedIntervalPartition a b) (A : ℝ → ℝ → E) : E :=
  ∑ i : Fin π.size, A (π.node i.castSucc) (π.node i.succ)

/-- Convergence of all ordered partition sums as their mesh tends to zero. -/
def PartitionSumsConverge {E : Type*} [NormedAddCommGroup E]
    (A : ℝ → ℝ → E) (a b : ℝ) (z : E) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ π : OrderedIntervalPartition a b,
    (π.mesh : ℝ) < δ → ‖π.incrementSum A - z‖ < ε

/-- Geometric sewing constant, finite and positive for exponents strictly greater than one. -/
def sewingConstant (γ : ℝ) : ℝ := (1 - (2 : ℝ) ^ (1 - γ))⁻¹

/-- A continuous interval path is normalized at the left endpoint. -/
def IsLeftNormalized {E : Type*} [TopologicalSpace E] [Zero E] {a b : ℝ}
    (I : C(Set.Icc a b, E)) : Prop := ∀ x : Set.Icc a b, x.val = a → I x = 0

/-- A path's additive increments approximate a given increment field to order `γ`. -/
def HasSewingRemainder {E : Type*} [NormedAddCommGroup E] {a b : ℝ}
    (A : ℝ → ℝ → E) (I : C(Set.Icc a b, E)) (γ C : ℝ) : Prop :=
  ∀ s t : Set.Icc a b, s.val ≤ t.val →
    ‖(I t - I s) - A s.val t.val‖ ≤ C * |t.val - s.val| ^ γ

/-- The path's increments are limits of all partition sums on each subinterval. -/
def HasPartitionSumLimit {E : Type*} [NormedAddCommGroup E] {a b : ℝ}
    (A : ℝ → ℝ → E) (I : C(Set.Icc a b, E)) : Prop :=
  ∀ s t : Set.Icc a b, s.val ≤ t.val → PartitionSumsConverge A s.val t.val (I t - I s)

/-- Closed triangle `a ≤ s ≤ t ≤ b` on which an increment field is sewn. -/
def sewingTriangle (a b : ℝ) : Set (ℝ × ℝ) :=
  {p | a ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ b}

namespace Sewing

open Finset Filter Topology

/-- Level-`n` dyadic node `s + (t - s) · k / 2^n`. -/
def dyadicNode (s t : ℝ) (n k : ℕ) : ℝ :=
  s + (t - s) * ((k : ℝ) / (2 : ℝ) ^ n)

/-- Sum of increments of `A` on the level-`n` dyadic partition of `[s, t]`. -/
def dyadicIncrement {E : Type*} [AddCommMonoid E] (A : ℝ → ℝ → E) (s t : ℝ) (n : ℕ) : E :=
  ∑ k ∈ range (2 ^ n), A (dyadicNode s t n k) (dyadicNode s t n (k + 1))

/-- The dyadic sewing limit `A(s, t) + ∑ (S_{n+1} - S_n)`. -/
noncomputable def sewnIncrement {E : Type*} [NormedAddCommGroup E]
    (A : ℝ → ℝ → E) (s t : ℝ) : E :=
  A s t + ∑' n : ℕ, (dyadicIncrement A s t (n + 1) - dyadicIncrement A s t n)

/-- Node at index `0` is the left endpoint. -/
lemma dyadicNode_zero (s t : ℝ) (n : ℕ) : dyadicNode s t n 0 = s := by
  simp [dyadicNode]

/-- Node at index `2^n` is the right endpoint. -/
lemma dyadicNode_last (s t : ℝ) (n : ℕ) : dyadicNode s t n (2 ^ n) = t := by
  unfold dyadicNode
  have hpow : ((2 ^ n : ℕ) : ℝ) = (2 : ℝ) ^ n := by simp
  rw [hpow, div_self (pow_ne_zero n (by norm_num : (2 : ℝ) ≠ 0)), mul_one]
  abel

/-- Consecutive dyadic nodes differ by `(t - s) / 2^n`. -/
lemma dyadicNode_sub (s t : ℝ) (n k : ℕ) :
    dyadicNode s t n (k + 1) - dyadicNode s t n k = (t - s) / (2 : ℝ) ^ n := by
  unfold dyadicNode
  rw [add_sub_add_left_eq_sub, ← mul_sub, div_sub_div_same]
  rw [show ((k + 1 : ℕ) : ℝ) - (k : ℝ) = 1 by simp [Nat.cast_add]]
  rw [mul_one_div]

/-- Doubling the level repeats even nodes. -/
lemma dyadicNode_two_mul (s t : ℝ) (n k : ℕ) :
    dyadicNode s t n k = dyadicNode s t (n + 1) (2 * k) := by
  unfold dyadicNode
  congr 1
  rw [pow_succ, Nat.cast_mul]
  field_simp
  ring

/-- On a nontrivial interval the nodes increase with the index. -/
lemma dyadicNode_mono {s t : ℝ} (hst : s ≤ t) (n : ℕ) {k j : ℕ} (hkj : k ≤ j) :
    dyadicNode s t n k ≤ dyadicNode s t n j := by
  unfold dyadicNode
  have hc : 0 ≤ t - s := sub_nonneg.mpr hst
  have hden : 0 ≤ (2 : ℝ) ^ n := pow_nonneg (by norm_num) _
  refine add_le_add_right (mul_le_mul_of_nonneg_left ?_ hc) _
  exact div_le_div_of_nonneg_right (Nat.cast_le.mpr hkj) hden

/-- Dyadic nodes of `[s, t]` stay inside `[s, t]` up to index `2^n`. -/
lemma dyadicNode_mem_interval {s t : ℝ} (hst : s ≤ t) (n : ℕ) {k : ℕ} (hk : k ≤ 2 ^ n) :
    s ≤ dyadicNode s t n k ∧ dyadicNode s t n k ≤ t := by
  constructor
  · simpa [dyadicNode_zero] using dyadicNode_mono hst n (Nat.zero_le k)
  · have hlast : dyadicNode s t n k ≤ dyadicNode s t n (2 ^ n) := dyadicNode_mono hst n hk
    simpa [dyadicNode_last] using hlast

/-- The level-`0` dyadic sum is the increment itself. -/
lemma dyadicIncrement_zero {E : Type*} [AddCommMonoid E] (A : ℝ → ℝ → E) (s t : ℝ) :
    dyadicIncrement A s t 0 = A s t := by
  unfold dyadicIncrement
  simp only [pow_zero, range_one, sum_singleton, dyadicNode_zero]
  exact congrArg (A s) (dyadicNode_last s t 0)

/-- Even-odd splitting of a sum over `range (2 * n)`. -/
lemma sum_range_two_mul {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∑ k ∈ range (2 * n), f k =
      ∑ k ∈ range n, f (2 * k) + ∑ k ∈ range n, f (2 * k + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 2 by omega]
    rw [sum_range_succ, sum_range_succ, ih]
    simp only [sum_range_succ]
    ac_rfl

/-- Left half of the dyadic grid is the dyadic grid of `[s, (s + t) / 2]`. -/
lemma dyadicNode_mid_left (s t : ℝ) (n i : ℕ) :
    dyadicNode s ((s + t) / 2) n i = dyadicNode s t (n + 1) i := by
  unfold dyadicNode
  have hm : (s + t) / 2 - s = (t - s) / 2 := by ring
  rw [hm]
  field_simp
  ring

/-- Right half of the dyadic grid is the shifted grid of `[(s + t) / 2, t]`. -/
lemma dyadicNode_mid_right (s t : ℝ) (n i : ℕ) :
    dyadicNode ((s + t) / 2) t n i = dyadicNode s t (n + 1) (2 ^ n + i) := by
  unfold dyadicNode
  have hm : t - (s + t) / 2 = (t - s) / 2 := by ring
  rw [hm, Nat.cast_add, Nat.cast_pow]
  field_simp
  ring_nf

/-- One refinement step splits as the sum of the two half-interval dyadic sums. -/
lemma dyadicIncrement_succ_midpoint {E : Type*} [AddCommMonoid E]
    (A : ℝ → ℝ → E) (s t : ℝ) (n : ℕ) :
    dyadicIncrement A s t (n + 1) =
      dyadicIncrement A s ((s + t) / 2) n + dyadicIncrement A ((s + t) / 2) t n := by
  unfold dyadicIncrement
  have hsplit := sum_range_add
    (fun j => A (dyadicNode s t (n + 1) j) (dyadicNode s t (n + 1) (j + 1)))
    (2 ^ n) (2 ^ n)
  have hpow : 2 ^ n + 2 ^ n = 2 ^ (n + 1) := by
    rw [← two_mul, ← pow_succ']
  rw [hpow] at hsplit
  rw [hsplit]
  refine congrArg₂ (· + ·) ?_ ?_
  · refine sum_congr rfl fun k hk => ?_
    rw [dyadicNode_mid_left, dyadicNode_mid_left]
  · refine sum_congr rfl fun k hk => ?_
    rw [dyadicNode_mid_right, dyadicNode_mid_right]
    simp [Nat.add_assoc]

/-- Refining one dyadic level subtracts the sum of defects on the parent intervals. -/
lemma dyadicIncrement_step_eq {E : Type*} [AddCommGroup E] (A : ℝ → ℝ → E) (s t : ℝ) (n : ℕ) :
    dyadicIncrement A s t n - dyadicIncrement A s t (n + 1) =
      ∑ k ∈ range (2 ^ n),
        (A (dyadicNode s t (n + 1) (2 * k)) (dyadicNode s t (n + 1) (2 * k + 2)) -
          A (dyadicNode s t (n + 1) (2 * k)) (dyadicNode s t (n + 1) (2 * k + 1)) -
          A (dyadicNode s t (n + 1) (2 * k + 1)) (dyadicNode s t (n + 1) (2 * k + 2))) := by
  let g : ℕ → E := fun j =>
    A (dyadicNode s t (n + 1) j) (dyadicNode s t (n + 1) (j + 1))
  have hfine : dyadicIncrement A s t (n + 1) =
      ∑ k ∈ range (2 ^ n), (g (2 * k) + g (2 * k + 1)) := by
    unfold dyadicIncrement
    have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ', Nat.mul_comm]
    rw [hpow, sum_range_two_mul, ← sum_add_distrib]
  have hcoarse : dyadicIncrement A s t n =
      ∑ k ∈ range (2 ^ n),
        A (dyadicNode s t (n + 1) (2 * k)) (dyadicNode s t (n + 1) (2 * k + 2)) := by
    unfold dyadicIncrement
    refine sum_congr rfl fun k _ => ?_
    have hL := dyadicNode_two_mul s t n k
    have hR : dyadicNode s t n (k + 1) = dyadicNode s t (n + 1) (2 * k + 2) := by
      have := dyadicNode_two_mul s t n (k + 1)
      simpa [Nat.mul_add, Nat.mul_one] using this
    rw [hL, hR]
  rw [hcoarse, hfine, ← sum_sub_distrib]
  refine sum_congr rfl fun k _ => ?_
  have hidx : (2 * k + 1) + 1 = 2 * k + 2 := by omega
  simp only [g, hidx, sub_add_eq_sub_sub]

/-- Ratio `2^{1 - γ}` lies in `[0, 1)` whenever `γ > 1`. -/
lemma sewingRatio_mem {γ : ℝ} (hγ : 1 < γ) :
    0 ≤ (2 : ℝ) ^ (1 - γ) ∧ (2 : ℝ) ^ (1 - γ) < 1 := by
  refine ⟨Real.rpow_nonneg (by norm_num) _, ?_⟩
  exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)

/-- The sewing constant is the sum of the geometric refinement ratios. -/
lemma sewingConstant_eq_tsum {γ : ℝ} (hγ : 1 < γ) :
    sewingConstant γ = ∑' n : ℕ, ((2 : ℝ) ^ (1 - γ)) ^ n := by
  rw [sewingConstant, tsum_geometric_of_lt_one (sewingRatio_mem hγ).1 (sewingRatio_mem hγ).2]

/-- `n · (L / n) ^ γ = L ^ γ · n ^ (1 - γ)` for positive integers. -/
lemma nat_mul_div_rpow {n : ℕ} (hn : 0 < n) {L γ : ℝ} (hL : 0 ≤ L) (hγ : γ ≠ 0) :
    (n : ℝ) * (L / (n : ℝ)) ^ γ = L ^ γ * (n : ℝ) ^ (1 - γ) := by
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  rcases hL.eq_or_lt with rfl | hL
  · simp [zero_div, Real.zero_rpow hγ, mul_zero, zero_mul]
  · rw [Real.div_rpow hL.le (Nat.cast_nonneg n)]
    have hsub : (n : ℝ) / (n : ℝ) ^ γ = (n : ℝ) ^ (1 - γ) := by
      rw [Real.rpow_sub hn0, Real.rpow_one]
    calc
      (n : ℝ) * (L ^ γ / (n : ℝ) ^ γ) = (n : ℝ) * L ^ γ / (n : ℝ) ^ γ := by rw [mul_div_assoc]
      _ = L ^ γ * ((n : ℝ) / (n : ℝ) ^ γ) := by ring
      _ = L ^ γ * (n : ℝ) ^ (1 - γ) := by rw [hsub]

/-- Scaling identity for one dyadic parent interval. -/
lemma dyadic_weight {L γ : ℝ} (hL : 0 ≤ L) (hγ : γ ≠ 0) (n : ℕ) :
    (2 ^ n : ℝ) * (L / (2 : ℝ) ^ n) ^ γ = L ^ γ * ((2 : ℝ) ^ (1 - γ)) ^ n := by
  have hpos : 0 < 2 ^ n := pow_pos (by norm_num) n
  have hnat := nat_mul_div_rpow hpos hL hγ
  simp only [Nat.cast_pow, Nat.cast_ofNat] at hnat
  have hexp : ((2 : ℝ) ^ n) ^ (1 - γ) = ((2 : ℝ) ^ (1 - γ)) ^ n := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    rw [mul_comm, Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
  rw [hnat, hexp]

/-- Two fine steps make one coarse dyadic step. -/
lemma dyadicNode_two_step (s t : ℝ) (n k : ℕ) :
    dyadicNode s t (n + 1) (2 * k + 2) - dyadicNode s t (n + 1) (2 * k) =
      (t - s) / (2 : ℝ) ^ n := by
  have h1 := dyadicNode_sub s t (n + 1) (2 * k)
  have h2 := dyadicNode_sub s t (n + 1) (2 * k + 1)
  have hidx : (2 * k + 1) + 1 = 2 * k + 2 := by omega
  rw [hidx] at h2
  have hpow : (2 : ℝ) ^ (n + 1) = 2 * (2 : ℝ) ^ n := by rw [pow_succ']
  calc
    dyadicNode s t (n + 1) (2 * k + 2) - dyadicNode s t (n + 1) (2 * k)
        = (dyadicNode s t (n + 1) (2 * k + 2) - dyadicNode s t (n + 1) (2 * k + 1)) +
          (dyadicNode s t (n + 1) (2 * k + 1) - dyadicNode s t (n + 1) (2 * k)) := by
            abel
    _ = (t - s) / (2 : ℝ) ^ (n + 1) + (t - s) / (2 : ℝ) ^ (n + 1) := by rw [h1, h2]
    _ = (t - s) / (2 : ℝ) ^ n := by
          rw [hpow]
          field_simp
          ring

/-- One dyadic refinement changes the sum by at most `C |t - s|^γ 2^{n(1 - γ)}`. -/
lemma norm_dyadicIncrement_step_le {E : Type*} [NormedAddCommGroup E]
    {a b γ C : ℝ} {A : ℝ → ℝ → E} (hγ : 1 < γ)
    (hdefect : ∀ s u t : ℝ, a ≤ s → s ≤ u → u ≤ t → t ≤ b →
      ‖A s t - A s u - A u t‖ ≤ C * |t - s| ^ γ)
    {s t : ℝ} (hs : a ≤ s) (hst : s ≤ t) (ht : t ≤ b) (n : ℕ) :
    ‖dyadicIncrement A s t n - dyadicIncrement A s t (n + 1)‖ ≤
      C * |t - s| ^ γ * ((2 : ℝ) ^ (1 - γ)) ^ n := by
  rw [dyadicIncrement_step_eq]
  refine (norm_sum_le _ _).trans ?_
  have hpiece : ∀ k ∈ range (2 ^ n),
      ‖A (dyadicNode s t (n + 1) (2 * k)) (dyadicNode s t (n + 1) (2 * k + 2)) -
          A (dyadicNode s t (n + 1) (2 * k)) (dyadicNode s t (n + 1) (2 * k + 1)) -
          A (dyadicNode s t (n + 1) (2 * k + 1))
            (dyadicNode s t (n + 1) (2 * k + 2))‖ ≤
        C * ((t - s) / (2 : ℝ) ^ n) ^ γ := by
    intro k hk
    have hklt : k < 2 ^ n := mem_range.mp hk
    have hk2 : 2 * k + 2 ≤ 2 ^ (n + 1) := by
      have h1 : k + 1 ≤ 2 ^ n := Nat.succ_le_of_lt hklt
      calc
        2 * k + 2 = 2 * (k + 1) := by omega
        _ ≤ 2 * 2 ^ n := Nat.mul_le_mul_left 2 h1
        _ = 2 ^ (n + 1) := by rw [← pow_succ']
    let left := dyadicNode s t (n + 1) (2 * k)
    let mid := dyadicNode s t (n + 1) (2 * k + 1)
    let right := dyadicNode s t (n + 1) (2 * k + 2)
    have hkm : 2 * k ≤ 2 * k + 1 := by omega
    have hmr : 2 * k + 1 ≤ 2 * k + 2 := by omega
    have horderL : left ≤ mid := dyadicNode_mono hst (n + 1) hkm
    have horderR : mid ≤ right := dyadicNode_mono hst (n + 1) hmr
    have hkL : 2 * k ≤ 2 ^ (n + 1) := le_trans (by omega) hk2
    have hmemL := dyadicNode_mem_interval hst (n + 1) hkL
    have hmemR := dyadicNode_mem_interval hst (n + 1) hk2
    have hlen := dyadicNode_two_step s t n k
    have habs : |right - left| = (t - s) / (2 : ℝ) ^ n := by
      rw [← hlen, abs_of_nonneg (sub_nonneg.mpr (horderL.trans horderR))]
    have hdef := hdefect left mid right (le_trans hs hmemL.1) horderL horderR
      (le_trans hmemR.2 ht)
    simpa [left, mid, right, habs] using hdef
  refine (Finset.sum_le_sum hpiece).trans ?_
  have hconst :
      ∑ k ∈ range (2 ^ n), C * ((t - s) / (2 : ℝ) ^ n) ^ γ =
        (2 ^ n : ℝ) * (C * ((t - s) / (2 : ℝ) ^ n) ^ γ) := by
    simp [sum_const, card_range, nsmul_eq_mul]
  rw [hconst]
  have hweight := dyadic_weight (sub_nonneg.mpr hst) (ne_of_gt (lt_trans zero_lt_one hγ)) n
  have hbase : (t - s) ^ γ = |t - s| ^ γ := by
    rw [abs_of_nonneg (sub_nonneg.mpr hst)]
  apply le_of_eq
  calc
    (2 ^ n : ℝ) * (C * ((t - s) / (2 : ℝ) ^ n) ^ γ)
        = C * ((2 ^ n : ℝ) * ((t - s) / (2 : ℝ) ^ n) ^ γ) := by ring
    _ = C * ((t - s) ^ γ * ((2 : ℝ) ^ (1 - γ)) ^ n) := by rw [hweight]
    _ = C * |t - s| ^ γ * ((2 : ℝ) ^ (1 - γ)) ^ n := by rw [hbase]; ring

variable {E : Type*} [NormedAddCommGroup E] [CompleteSpace E] {a b γ C : ℝ}
variable {A : ℝ → ℝ → E}

/-- Dyadic steps are absolutely summable on every subinterval of `[a, b]`. -/
lemma summable_dyadic_step (hγ : 1 < γ)
    (hdefect : ∀ s u t : ℝ, a ≤ s → s ≤ u → u ≤ t → t ≤ b →
      ‖A s t - A s u - A u t‖ ≤ C * |t - s| ^ γ)
    {s t : ℝ} (hs : a ≤ s) (hst : s ≤ t) (ht : t ≤ b) :
    Summable fun n : ℕ =>
      dyadicIncrement A s t (n + 1) - dyadicIncrement A s t n := by
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one (sewingRatio_mem hγ).1 (sewingRatio_mem hγ).2).mul_left
      (C * |t - s| ^ γ)) ?_
  intro n
  have hstep := norm_dyadicIncrement_step_le hγ hdefect hs hst ht n
  simpa [norm_sub_rev, mul_assoc] using hstep

/-- Level-`n` dyadic sums converge to the sewn increment. -/
lemma tendsto_dyadicIncrement (hγ : 1 < γ) (_hC : 0 ≤ C)
    (hdefect : ∀ s u t : ℝ, a ≤ s → s ≤ u → u ≤ t → t ≤ b →
      ‖A s t - A s u - A u t‖ ≤ C * |t - s| ^ γ)
    {s t : ℝ} (hs : a ≤ s) (hst : s ≤ t) (ht : t ≤ b) :
    Tendsto (fun n => dyadicIncrement A s t n) atTop (𝓝 (sewnIncrement A s t)) := by
  have hsum := summable_dyadic_step hγ hdefect hs hst ht
  have htele : ∀ n, dyadicIncrement A s t n =
      A s t + ∑ k ∈ range n,
        (dyadicIncrement A s t (k + 1) - dyadicIncrement A s t k) := by
    intro n
    induction n with
    | zero => simp [dyadicIncrement_zero]
    | succ n ih =>
      rw [sum_range_succ, ih]
      abel
  have hfun : (fun n => dyadicIncrement A s t n) =
      fun n => A s t + ∑ k ∈ range n,
        (dyadicIncrement A s t (k + 1) - dyadicIncrement A s t k) := by
    funext n
    exact htele n
  rw [hfun, sewnIncrement]
  exact hsum.hasSum.tendsto_sum_nat.const_add (A s t)

/-- The sewn increment approximates `A` with constant `sewingConstant γ * C`. -/
lemma norm_sewnIncrement_sub (hγ : 1 < γ) (_hC : 0 ≤ C)
    (hdefect : ∀ s u t : ℝ, a ≤ s → s ≤ u → u ≤ t → t ≤ b →
      ‖A s t - A s u - A u t‖ ≤ C * |t - s| ^ γ)
    {s t : ℝ} (hs : a ≤ s) (hst : s ≤ t) (ht : t ≤ b) :
    ‖sewnIncrement A s t - A s t‖ ≤ sewingConstant γ * C * |t - s| ^ γ := by
  rw [sewnIncrement, add_sub_cancel_left]
  have hcomm : sewingConstant γ * C * |t - s| ^ γ =
      (C * |t - s| ^ γ) * sewingConstant γ := by ring
  rw [hcomm, sewingConstant]
  refine tsum_of_norm_bounded
    ((hasSum_geometric_of_lt_one (sewingRatio_mem hγ).1 (sewingRatio_mem hγ).2).mul_left
      (C * |t - s| ^ γ)) ?_
  intro n
  simpa [norm_sub_rev, mul_assoc] using
    norm_dyadicIncrement_step_le hγ hdefect hs hst ht n

omit [CompleteSpace E] in
/-- Sewing a point to itself produces zero. -/
lemma sewnIncrement_same
    (hdiag : ∀ s ∈ Set.Icc a b, A s s = 0) {s : ℝ} (hs : a ≤ s) (hsb : s ≤ b) :
    sewnIncrement A s s = 0 := by
  have hnode : ∀ n k, dyadicNode s s n k = s := by
    intro n k
    simp [dyadicNode]
  have hS : ∀ n, dyadicIncrement A s s n = 0 := by
    intro n
    unfold dyadicIncrement
    refine sum_eq_zero fun k _ => ?_
    rw [hnode n k, hnode n (k + 1), hdiag s ⟨hs, hsb⟩]
  simp [sewnIncrement, hS, hdiag s ⟨hs, hsb⟩]

/-- The sewn increment is additive across the midpoint. -/
lemma sewnIncrement_midpoint (hγ : 1 < γ) (hC : 0 ≤ C)
    (hdefect : ∀ s u t : ℝ, a ≤ s → s ≤ u → u ≤ t → t ≤ b →
      ‖A s t - A s u - A u t‖ ≤ C * |t - s| ^ γ)
    {s t : ℝ} (hs : a ≤ s) (hst : s ≤ t) (ht : t ≤ b) :
    sewnIncrement A s t =
      sewnIncrement A s ((s + t) / 2) + sewnIncrement A ((s + t) / 2) t := by
  set m : ℝ := (s + t) / 2
  have hsm : s ≤ m := by dsimp [m]; linarith
  have hmt : m ≤ t := by dsimp [m]; linarith
  have hma : a ≤ m := le_trans hs hsm
  have hmb : m ≤ b := le_trans hmt ht
  have h := tendsto_dyadicIncrement hγ hC hdefect hs hst ht
  have hL := tendsto_dyadicIncrement hγ hC hdefect hs hsm hmb
  have hR := tendsto_dyadicIncrement hγ hC hdefect hma hmt ht
  have hshift :
      Tendsto (fun n => dyadicIncrement A s t (n + 1)) atTop (𝓝 (sewnIncrement A s t)) :=
    (tendsto_add_atTop_iff_nat 1).mpr h
  have hsplit : Tendsto (fun n => dyadicIncrement A s t (n + 1)) atTop
      (𝓝 (sewnIncrement A s m + sewnIncrement A m t)) := by
    have hfun : (fun n => dyadicIncrement A s t (n + 1)) =
        fun n => dyadicIncrement A s m n + dyadicIncrement A m t n := by
      funext n
      simpa [m] using dyadicIncrement_succ_midpoint A s t n
    rw [hfun]
    exact hL.add hR
  exact tendsto_nhds_unique hshift hsplit

/-- Dyadic nodes depend continuously on the endpoints. -/
lemma continuous_dyadicNode (n k : ℕ) :
    Continuous (fun p : ℝ × ℝ => dyadicNode p.1 p.2 n k) := by
  unfold dyadicNode
  exact continuous_fst.add ((continuous_snd.sub continuous_fst).mul continuous_const)

/-- Consecutive dyadic nodes of a triangle point stay inside the triangle. -/
lemma dyadicEndpoints_mapsTo {a b : ℝ} (n k : ℕ) (hk : k + 1 ≤ 2 ^ n) :
    Set.MapsTo (fun p : ℝ × ℝ =>
      (dyadicNode p.1 p.2 n k, dyadicNode p.1 p.2 n (k + 1)))
      (sewingTriangle a b) (sewingTriangle a b) := by
  intro p hp
  have hst : p.1 ≤ p.2 := hp.2.1
  have hk0 : k ≤ 2 ^ n := le_trans (Nat.le_succ _) hk
  have h1 := dyadicNode_mem_interval hst n hk0
  have h2 := dyadicNode_mem_interval hst n hk
  exact ⟨le_trans hp.1 h1.1, dyadicNode_mono hst n (Nat.le_succ k), le_trans h2.2 hp.2.2⟩

/-- One summand of a dyadic increment is continuous on the triangle. -/
lemma continuousOn_dyadicPiece
    (hcont : ContinuousOn (fun p : ℝ × ℝ => A p.1 p.2) (sewingTriangle a b))
    (n k : ℕ) (hk : k < 2 ^ n) :
    ContinuousOn (fun p : ℝ × ℝ =>
      A (dyadicNode p.1 p.2 n k) (dyadicNode p.1 p.2 n (k + 1)))
      (sewingTriangle a b) := by
  refine hcont.comp ?_ (dyadicEndpoints_mapsTo n k (Nat.succ_le_of_lt hk))
  exact ((continuous_dyadicNode n k).prodMk
    (continuous_dyadicNode n (k + 1))).continuousOn

/-- Dyadic increment sums are continuous on the triangle. -/
lemma continuousOn_dyadicIncrement
    (hcont : ContinuousOn (fun p : ℝ × ℝ => A p.1 p.2) (sewingTriangle a b)) (n : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => dyadicIncrement A p.1 p.2 n) (sewingTriangle a b) := by
  unfold dyadicIncrement
  refine continuousOn_finsetSum _ fun k hk => ?_
  exact continuousOn_dyadicPiece hcont n k (Finset.mem_range.mp hk)

/-- Uniform majorant of one dyadic step on the whole triangle. -/
lemma norm_dyadic_step_triangle (hab : a ≤ b) (hγ : 1 < γ) (hC : 0 ≤ C)
    (hdefect : ∀ s u t : ℝ, a ≤ s → s ≤ u → u ≤ t → t ≤ b →
      ‖A s t - A s u - A u t‖ ≤ C * |t - s| ^ γ)
    {p : ℝ × ℝ} (hp : p ∈ sewingTriangle a b) (n : ℕ) :
    ‖dyadicIncrement A p.1 p.2 (n + 1) - dyadicIncrement A p.1 p.2 n‖ ≤
      C * |b - a| ^ γ * ((2 : ℝ) ^ (1 - γ)) ^ n := by
  have hstep := norm_dyadicIncrement_step_le hγ hdefect hp.1 hp.2.1 hp.2.2 n
  have ha : a ≤ p.1 := hp.1
  have hst : p.1 ≤ p.2 := hp.2.1
  have hb : p.2 ≤ b := hp.2.2
  have hlen : |p.2 - p.1| ≤ |b - a| := by
    have hsub : p.2 - p.1 ≤ b - a := by linarith
    rw [abs_of_nonneg (sub_nonneg.mpr hst), abs_of_nonneg (sub_nonneg.mpr hab)]
    exact hsub
  have hpow := Real.rpow_le_rpow (abs_nonneg _) hlen (le_of_lt (lt_trans zero_lt_one hγ))
  have hr : 0 ≤ ((2 : ℝ) ^ (1 - γ)) ^ n :=
    pow_nonneg (sewingRatio_mem hγ).1 n
  have hmul : C * |p.2 - p.1| ^ γ ≤ C * |b - a| ^ γ :=
    mul_le_mul_of_nonneg_left hpow hC
  rw [norm_sub_rev]
  exact hstep.trans (mul_le_mul_of_nonneg_right hmul hr)

/-- The sewn increment is continuous on the triangle. -/
lemma continuousOn_sewnIncrement (hab : a ≤ b) (hγ : 1 < γ) (hC : 0 ≤ C)
    (hcont : ContinuousOn (fun p : ℝ × ℝ => A p.1 p.2) (sewingTriangle a b))
    (hdefect : ∀ s u t : ℝ, a ≤ s → s ≤ u → u ≤ t → t ≤ b →
      ‖A s t - A s u - A u t‖ ≤ C * |t - s| ^ γ) :
    ContinuousOn (fun p : ℝ × ℝ => sewnIncrement A p.1 p.2) (sewingTriangle a b) := by
  have hr := sewingRatio_mem hγ
  have hu : Summable fun n : ℕ =>
      C * |b - a| ^ γ * ((2 : ℝ) ^ (1 - γ)) ^ n :=
    (summable_geometric_of_lt_one hr.1 hr.2).mul_left (C * |b - a| ^ γ)
  have hterm : ∀ n, ContinuousOn (fun p : ℝ × ℝ =>
      dyadicIncrement A p.1 p.2 (n + 1) - dyadicIncrement A p.1 p.2 n)
      (sewingTriangle a b) := by
    intro n
    exact (continuousOn_dyadicIncrement hcont (n + 1)).sub
      (continuousOn_dyadicIncrement hcont n)
  have hseries : ContinuousOn (fun p : ℝ × ℝ =>
      ∑' n : ℕ, (dyadicIncrement A p.1 p.2 (n + 1) - dyadicIncrement A p.1 p.2 n))
      (sewingTriangle a b) :=
    continuousOn_tsum hterm hu fun n p hp => norm_dyadic_step_triangle hab hγ hC hdefect hp n
  have hsewn : (fun p : ℝ × ℝ => sewnIncrement A p.1 p.2) =
      fun p => A p.1 p.2 +
        ∑' n : ℕ, (dyadicIncrement A p.1 p.2 (n + 1) - dyadicIncrement A p.1 p.2 n) := by
    funext p
    rfl
  rw [hsewn]
  exact hcont.add hseries

/-- The sewing constant is positive for exponents greater than one. -/
lemma sewingConstant_pos (hγ : 1 < γ) : 0 < sewingConstant γ := by
  rw [sewingConstant]
  exact inv_pos.mpr (sub_pos.mpr (sewingRatio_mem hγ).2)

/-- A midpoint-additive increment of order greater than one vanishes. -/
lemma vanishes_of_midpoint (hγ : 1 < γ) (Z : ℝ → ℝ → E) (M : ℝ)
    (hadd : ∀ s t : ℝ, a ≤ s → s ≤ t → t ≤ b →
      Z s t = Z s ((s + t) / 2) + Z ((s + t) / 2) t)
    (hbound : ∀ s t : ℝ, a ≤ s → s ≤ t → t ≤ b → ‖Z s t‖ ≤ M * |t - s| ^ γ)
    {s t : ℝ} (hs : a ≤ s) (hst : s ≤ t) (ht : t ≤ b) : Z s t = 0 := by
  let r : ℝ := (2 : ℝ) ^ (1 - γ)
  have hr := sewingRatio_mem hγ
  have hpow : ∀ n : ℕ, ∀ s t : ℝ, a ≤ s → s ≤ t → t ≤ b →
      ‖Z s t‖ ≤ M * |t - s| ^ γ * r ^ n := by
    intro n
    induction n with
    | zero =>
      intro s t hs hst ht
      simpa [r] using hbound s t hs hst ht
    | succ n ih =>
      intro s t hs hst ht
      let m : ℝ := (s + t) / 2
      have hsm : s ≤ m := by dsimp [m]; linarith
      have hmt : m ≤ t := by dsimp [m]; linarith
      have hlen : |m - s| = |t - s| / 2 := by
        have hm : m - s = (t - s) / 2 := by dsimp [m]; ring
        rw [hm, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      have hlen' : |t - m| = |t - s| / 2 := by
        have hm : t - m = (t - s) / 2 := by dsimp [m]; ring
        rw [hm, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      have hw : (2 : ℝ) * (|t - s| / 2) ^ γ = |t - s| ^ γ * r := by
        simpa [r, pow_one] using
          dyadic_weight (abs_nonneg (t - s)) (ne_of_gt (lt_trans zero_lt_one hγ)) 1
      calc
        ‖Z s t‖ = ‖Z s m + Z m t‖ := by rw [hadd s t hs hst ht]
        _ ≤ ‖Z s m‖ + ‖Z m t‖ := norm_add_le _ _
        _ ≤ M * |m - s| ^ γ * r ^ n + M * |t - m| ^ γ * r ^ n := by
            exact add_le_add (ih s m hs hsm (le_trans hmt ht))
              (ih m t (le_trans hs hsm) hmt ht)
        _ = 2 * (M * (|t - s| / 2) ^ γ * r ^ n) := by rw [hlen, hlen']; ring
        _ = M * |t - s| ^ γ * r ^ (n + 1) := by
            calc
              2 * (M * (|t - s| / 2) ^ γ * r ^ n)
                  = (2 * (|t - s| / 2) ^ γ) * M * r ^ n := by ring
              _ = (|t - s| ^ γ * r) * M * r ^ n := by rw [hw]
              _ = M * |t - s| ^ γ * (r * r ^ n) := by ring
              _ = M * |t - s| ^ γ * r ^ (n + 1) := by rw [← pow_succ']
  have htend : Tendsto (fun n : ℕ => M * |t - s| ^ γ * r ^ n) atTop (𝓝 0) := by
    simpa [r, mul_assoc] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hr.1 hr.2).const_mul (M * |t - s| ^ γ)
  have hzero : ‖Z s t‖ ≤ 0 :=
    le_of_tendsto_of_tendsto' tendsto_const_nhds htend fun n => hpow n s t hs hst ht
  exact norm_eq_zero.mp (le_antisymm hzero (norm_nonneg _))

end Sewing

end CKMA
