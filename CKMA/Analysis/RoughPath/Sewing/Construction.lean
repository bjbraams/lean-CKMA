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
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Dyadic sewing construction

Ordered partitions, the sewing constant, and the dyadic primitive used to prove the
sewing lemma. Increments may repeat nodes. The sewn primitive is additive, continuous
on the triangle, and approximated by every ordered partition at rate `mesh ^ (γ - 1)`.
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
    {a b γ C : ℝ} {A : ℝ → ℝ → E} (hγ : 1 < γ) (_hC : 0 ≤ C)
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
lemma summable_dyadic_step (hγ : 1 < γ) (hC : 0 ≤ C)
    (hdefect : ∀ s u t : ℝ, a ≤ s → s ≤ u → u ≤ t → t ≤ b →
      ‖A s t - A s u - A u t‖ ≤ C * |t - s| ^ γ)
    {s t : ℝ} (hs : a ≤ s) (hst : s ≤ t) (ht : t ≤ b) :
    Summable fun n : ℕ =>
      dyadicIncrement A s t (n + 1) - dyadicIncrement A s t n := by
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one (sewingRatio_mem hγ).1 (sewingRatio_mem hγ).2).mul_left
      (C * |t - s| ^ γ)) ?_
  intro n
  have hstep := norm_dyadicIncrement_step_le hγ hC hdefect hs hst ht n
  simpa [norm_sub_rev, mul_assoc] using hstep

/-- Level-`n` dyadic sums converge to the sewn increment. -/
lemma tendsto_dyadicIncrement (hγ : 1 < γ) (hC : 0 ≤ C)
    (hdefect : ∀ s u t : ℝ, a ≤ s → s ≤ u → u ≤ t → t ≤ b →
      ‖A s t - A s u - A u t‖ ≤ C * |t - s| ^ γ)
    {s t : ℝ} (hs : a ≤ s) (hst : s ≤ t) (ht : t ≤ b) :
    Tendsto (fun n => dyadicIncrement A s t n) atTop (𝓝 (sewnIncrement A s t)) := by
  have hsum := summable_dyadic_step hγ hC hdefect hs hst ht
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
lemma norm_sewnIncrement_sub (hγ : 1 < γ) (hC : 0 ≤ C)
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
    norm_dyadicIncrement_step_le hγ hC hdefect hs hst ht n

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
  have hstep := norm_dyadicIncrement_step_le hγ hC hdefect hp.1 hp.2.1 hp.2.2 n
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

/-- Node of the uniform `k`-partition of `[s, t]`. -/
def equalNode (s t : ℝ) (k i : ℕ) : ℝ :=
  s + (t - s) * ((i : ℝ) / (k : ℝ))

/-- Sum of an increment field on the uniform `k`-partition. -/
def equalSewn {E : Type*} [AddCommMonoid E] (Z : ℝ → ℝ → E) (s t : ℝ) (k : ℕ) : E :=
  ∑ i ∈ range k, Z (equalNode s t k i) (equalNode s t k (i + 1))

/-- The first uniform node is the left endpoint. -/
lemma equalNode_zero (s t : ℝ) (k : ℕ) : equalNode s t k 0 = s := by
  simp [equalNode]

/-- The last uniform node is the right endpoint. -/
lemma equalNode_last (s t : ℝ) {k : ℕ} (hk : 0 < k) : equalNode s t k k = t := by
  unfold equalNode
  rw [div_self (by exact_mod_cast (Nat.ne_of_gt hk) : (k : ℝ) ≠ 0), mul_one]
  abel

/-- Uniform nodes increase with the index. -/
lemma equalNode_mono {s t : ℝ} (hst : s ≤ t) (k : ℕ) {i j : ℕ} (hij : i ≤ j) :
    equalNode s t k i ≤ equalNode s t k j := by
  unfold equalNode
  have hc : 0 ≤ t - s := sub_nonneg.mpr hst
  refine add_le_add_right (mul_le_mul_of_nonneg_left ?_ hc) _
  exact div_le_div_of_nonneg_right (Nat.cast_le.mpr hij) (Nat.cast_nonneg _)

/-- Uniform nodes up to index `k` stay inside `[s, t]`. -/
lemma equalNode_mem {s t : ℝ} (hst : s ≤ t) {k : ℕ} (hk : 0 < k) {i : ℕ} (hi : i ≤ k) :
    s ≤ equalNode s t k i ∧ equalNode s t k i ≤ t := by
  constructor
  · simpa [equalNode_zero] using equalNode_mono hst k (Nat.zero_le i)
  · simpa [equalNode_last s t hk] using equalNode_mono hst k hi

/-- Consecutive uniform nodes differ by `(t - s) / k`. -/
lemma equalNode_sub (s t : ℝ) (k i : ℕ) :
    equalNode s t k (i + 1) - equalNode s t k i = (t - s) / k := by
  unfold equalNode
  rw [add_sub_add_left_eq_sub, ← mul_sub, div_sub_div_same]
  rw [show ((i + 1 : ℕ) : ℝ) - (i : ℝ) = 1 by simp [Nat.cast_add]]
  rw [mul_one_div]

/-- Even nodes of the doubled grid repeat the coarse grid. -/
lemma equalNode_even (s t : ℝ) (k i : ℕ) :
    equalNode s t k i = equalNode s t (2 * k) (2 * i) := by
  unfold equalNode
  rw [Nat.cast_mul, Nat.cast_mul]
  refine congrArg (fun z => s + (t - s) * z) ?_
  exact (mul_div_mul_left (i : ℝ) (k : ℝ) (by norm_num : (2 : ℝ) ≠ 0)).symm

/-- The midpoint of a coarse piece is the odd doubled node. -/
lemma equalNode_piece_mid (s t : ℝ) {k : ℕ} (hk : 0 < k) (i : ℕ) :
    (equalNode s t k i + equalNode s t k (i + 1)) / 2 =
      equalNode s t (2 * k) (2 * i + 1) := by
  unfold equalNode
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hk
  rw [Nat.cast_add, Nat.cast_mul, Nat.cast_add, Nat.cast_mul, Nat.cast_one]
  field_simp
  ring

/-- Left half-grid of a doubled partition. -/
lemma equalNode_left (s t : ℝ) {k : ℕ} (hk : 0 < k) (i : ℕ) :
    equalNode s ((s + t) / 2) k i = equalNode s t (2 * k) i := by
  unfold equalNode
  have hm : (s + t) / 2 - s = (t - s) / 2 := by ring
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hk
  rw [hm, Nat.cast_mul]
  field_simp
  ring

/-- Right half-grid of a doubled partition. -/
lemma equalNode_right (s t : ℝ) {k : ℕ} (hk : 0 < k) (i : ℕ) :
    equalNode ((s + t) / 2) t k i = equalNode s t (2 * k) (k + i) := by
  unfold equalNode
  have hm : t - (s + t) / 2 = (t - s) / 2 := by ring
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hk
  rw [hm, Nat.cast_add, Nat.cast_mul]
  field_simp
  ring

/-- Doubling a midpoint-additive grid does not change its sewn sum. -/
lemma equalSewn_two_mul (Z : ℝ → ℝ → E)
    (hadd : ∀ s t : ℝ, a ≤ s → s ≤ t → t ≤ b →
      Z s t = Z s ((s + t) / 2) + Z ((s + t) / 2) t)
    {s t : ℝ} (hs : a ≤ s) (hst : s ≤ t) (ht : t ≤ b) {k : ℕ} (hk : 0 < k) :
    equalSewn Z s t k = equalSewn Z s t (2 * k) := by
  unfold equalSewn
  rw [sum_range_two_mul
    (fun j => Z (equalNode s t (2 * k) j) (equalNode s t (2 * k) (j + 1))) k]
  rw [← sum_add_distrib]
  refine sum_congr rfl fun i hi => ?_
  have hik : i < k := mem_range.mp hi
  have hi' : i ≤ k := le_of_lt hik
  have hi1 : i + 1 ≤ k := Nat.succ_le_of_lt hik
  have hLmem := equalNode_mem hst hk hi'
  have hRmem := equalNode_mem hst hk hi1
  have horder : equalNode s t k i ≤ equalNode s t k (i + 1) :=
    equalNode_mono hst k (Nat.le_succ i)
  have haddI := hadd (equalNode s t k i) (equalNode s t k (i + 1))
    (le_trans hs hLmem.1) horder (le_trans hRmem.2 ht)
  have hR : equalNode s t k (i + 1) = equalNode s t (2 * k) (2 * (i + 1)) :=
    equalNode_even s t k (i + 1)
  have hidx : 2 * (i + 1) = 2 * i + 2 := by omega
  rw [haddI, equalNode_piece_mid s t hk i, equalNode_even s t k i, hR, hidx]

/-- A doubled uniform sum splits into the two half intervals. -/
lemma equalSewn_halves {F : Type*} [AddCommMonoid F] (Z : ℝ → ℝ → F) (s t : ℝ) {k : ℕ}
    (hk : 0 < k) :
    equalSewn Z s ((s + t) / 2) k + equalSewn Z ((s + t) / 2) t k =
      equalSewn Z s t (2 * k) := by
  unfold equalSewn
  have hsplit := sum_range_add
    (fun j => Z (equalNode s t (2 * k) j) (equalNode s t (2 * k) (j + 1))) k k
  have hpow : k + k = 2 * k := by omega
  rw [hpow] at hsplit
  rw [hsplit]
  refine congrArg₂ (· + ·) ?_ ?_
  · refine sum_congr rfl fun i _ => ?_
    rw [equalNode_left s t hk i, equalNode_left s t hk (i + 1)]
  · refine sum_congr rfl fun i _ => ?_
    rw [equalNode_right s t hk i, equalNode_right s t hk (i + 1)]
    simp [Nat.add_assoc]

/-- Midpoint additivity passes from `Z` to its uniform sums. -/
lemma equalSewn_midpoint (Z : ℝ → ℝ → E)
    (hadd : ∀ s t : ℝ, a ≤ s → s ≤ t → t ≤ b →
      Z s t = Z s ((s + t) / 2) + Z ((s + t) / 2) t)
    {s t : ℝ} (hs : a ≤ s) (hst : s ≤ t) (ht : t ≤ b) {k : ℕ} (hk : 0 < k) :
    equalSewn Z s t k =
      equalSewn Z s ((s + t) / 2) k + equalSewn Z ((s + t) / 2) t k := by
  rw [equalSewn_two_mul Z hadd hs hst ht hk]
  exact (equalSewn_halves Z s t hk).symm

/-- Partial uniform sums of `A` differ from `A` by at most one defect per step. -/
lemma norm_uniformPrefix_sub (hγ : 1 < γ) (hC : 0 ≤ C)
    (hdiag : ∀ s ∈ Set.Icc a b, A s s = 0)
    (hdefect : ∀ s u t : ℝ, a ≤ s → s ≤ u → u ≤ t → t ≤ b →
      ‖A s t - A s u - A u t‖ ≤ C * |t - s| ^ γ)
    {s t : ℝ} (hs : a ≤ s) (hst : s ≤ t) (ht : t ≤ b) {k : ℕ} (hk : 0 < k) :
    ∀ j ≤ k, ‖(∑ i ∈ range j, A (equalNode s t k i) (equalNode s t k (i + 1))) -
      A s (equalNode s t k j)‖ ≤ (j : ℝ) * C * |t - s| ^ γ := by
  intro j
  induction j with
  | zero =>
    intro _
    rw [sum_range_zero, equalNode_zero, hdiag s ⟨hs, le_trans hst ht⟩]
    simp
  | succ j ih =>
    intro hj
    have hjk : j ≤ k := Nat.le_of_succ_le hj
    have ihj := ih hjk
    have hx := equalNode_mem hst hk hjk
    have hy := equalNode_mem hst hk hj
    have hxy : equalNode s t k j ≤ equalNode s t k (j + 1) :=
      equalNode_mono hst k (Nat.le_succ j)
    have hdef := hdefect s (equalNode s t k j) (equalNode s t k (j + 1)) hs hx.1 hxy
      (le_trans hy.2 ht)
    have hlen : |equalNode s t k (j + 1) - s| ≤ |t - s| := by
      rw [abs_of_nonneg (sub_nonneg.mpr hy.1), abs_of_nonneg (sub_nonneg.mpr hst)]
      exact sub_le_sub_right hy.2 s
    have hpow := Real.rpow_le_rpow (abs_nonneg _) hlen (le_of_lt (lt_trans zero_lt_one hγ))
    have hCpow : C * |equalNode s t k (j + 1) - s| ^ γ ≤ C * |t - s| ^ γ :=
      mul_le_mul_of_nonneg_left hpow hC
    rw [sum_range_succ]
    have hAlg :
        (∑ i ∈ range j, A (equalNode s t k i) (equalNode s t k (i + 1))) +
          A (equalNode s t k j) (equalNode s t k (j + 1)) -
          A s (equalNode s t k (j + 1)) =
        ((∑ i ∈ range j, A (equalNode s t k i) (equalNode s t k (i + 1))) -
          A s (equalNode s t k j)) -
        (A s (equalNode s t k (j + 1)) - A s (equalNode s t k j) -
          A (equalNode s t k j) (equalNode s t k (j + 1))) := by
      abel
    rw [hAlg]
    refine (norm_sub_le _ _).trans ?_
    calc
      ‖(∑ i ∈ range j, A (equalNode s t k i) (equalNode s t k (i + 1))) -
          A s (equalNode s t k j)‖ +
        ‖A s (equalNode s t k (j + 1)) - A s (equalNode s t k j) -
          A (equalNode s t k j) (equalNode s t k (j + 1))‖ ≤
          (j : ℝ) * C * |t - s| ^ γ + C * |equalNode s t k (j + 1) - s| ^ γ :=
        add_le_add ihj hdef
      _ ≤ (j : ℝ) * C * |t - s| ^ γ + C * |t - s| ^ γ := add_le_add (le_refl _) hCpow
      _ = ((j + 1 : ℕ) : ℝ) * C * |t - s| ^ γ := by
        rw [Nat.cast_add, Nat.cast_one]
        ring

/-- On each subinterval the sewn increment matches its uniform sums up to order `γ`. -/
lemma norm_sewn_sub_equalSewn (hγ : 1 < γ) (hC : 0 ≤ C)
    (hdiag : ∀ s ∈ Set.Icc a b, A s s = 0)
    (hdefect : ∀ s u t : ℝ, a ≤ s → s ≤ u → u ≤ t → t ≤ b →
      ‖A s t - A s u - A u t‖ ≤ C * |t - s| ^ γ)
    {s t : ℝ} (hs : a ≤ s) (hst : s ≤ t) (ht : t ≤ b) {k : ℕ} (hk : 0 < k) :
    ‖sewnIncrement A s t - equalSewn (sewnIncrement A) s t k‖ ≤
      (sewingConstant γ * C * (1 + (k : ℝ) ^ (1 - γ)) + C * (k : ℝ)) * |t - s| ^ γ := by
  let Z : ℝ → ℝ → E := sewnIncrement A
  let K : ℝ := sewingConstant γ * C
  have hZA := norm_sewnIncrement_sub hγ hC hdefect hs hst ht
  have hpiece : ∀ i ∈ range k,
      ‖Z (equalNode s t k i) (equalNode s t k (i + 1)) -
        A (equalNode s t k i) (equalNode s t k (i + 1))‖ ≤
        K * (|t - s| / k) ^ γ := by
    intro i hi
    have hik : i < k := mem_range.mp hi
    have hi' : i ≤ k := le_of_lt hik
    have hi1 : i + 1 ≤ k := Nat.succ_le_of_lt hik
    have hL := equalNode_mem hst hk hi'
    have hR := equalNode_mem hst hk hi1
    have horder := equalNode_mono hst k (Nat.le_succ i)
    have hsub := norm_sewnIncrement_sub hγ hC hdefect (le_trans hs hL.1) horder
      (le_trans hR.2 ht)
    have hlen : |equalNode s t k (i + 1) - equalNode s t k i| = |t - s| / k := by
      rw [equalNode_sub, abs_div, abs_of_nonneg (sub_nonneg.mpr hst),
        abs_of_nonneg (Nat.cast_nonneg k)]
    simpa [Z, K, hlen] using hsub
  have hsub :
      equalSewn Z s t k - equalSewn A s t k =
        ∑ i ∈ range k, (Z (equalNode s t k i) (equalNode s t k (i + 1)) -
          A (equalNode s t k i) (equalNode s t k (i + 1))) := by
    unfold equalSewn
    rw [sum_sub_distrib]
  have hsum : ‖equalSewn Z s t k - equalSewn A s t k‖ ≤
      K * |t - s| ^ γ * (k : ℝ) ^ (1 - γ) := by
    rw [hsub]
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum hpiece).trans ?_
    have hconst : ∑ _i ∈ range k, K * (|t - s| / k) ^ γ =
        (k : ℝ) * (K * (|t - s| / k) ^ γ) := by
      simp [sum_const, card_range, nsmul_eq_mul]
    rw [hconst]
    have hscale := nat_mul_div_rpow hk (abs_nonneg (t - s))
      (ne_of_gt (lt_trans zero_lt_one hγ))
    apply le_of_eq
    calc
      (k : ℝ) * (K * (|t - s| / k) ^ γ) = K * ((k : ℝ) * (|t - s| / k) ^ γ) := by ring
      _ = K * (|t - s| ^ γ * (k : ℝ) ^ (1 - γ)) := by rw [hscale]
      _ = K * |t - s| ^ γ * (k : ℝ) ^ (1 - γ) := by ring
  have hA : ‖equalSewn A s t k - A s t‖ ≤ (k : ℝ) * C * |t - s| ^ γ := by
    simpa [equalSewn, equalNode_last s t hk] using
      norm_uniformPrefix_sub hγ hC hdiag hdefect hs hst ht hk k le_rfl
  have htri : Z s t - equalSewn Z s t k =
      (Z s t - A s t) - (equalSewn Z s t k - equalSewn A s t k) -
        (equalSewn A s t k - A s t) := by
    abel
  rw [htri]
  refine (norm_sub_le _ _).trans ?_
  refine (add_le_add (norm_sub_le _ _) (le_refl _)).trans ?_
  calc
    ‖Z s t - A s t‖ + ‖equalSewn Z s t k - equalSewn A s t k‖ +
        ‖equalSewn A s t k - A s t‖ ≤
        K * |t - s| ^ γ + K * |t - s| ^ γ * (k : ℝ) ^ (1 - γ) +
          (k : ℝ) * C * |t - s| ^ γ :=
      add_le_add (add_le_add (by simpa [Z, K] using hZA) hsum) hA
    _ = (K * (1 + (k : ℝ) ^ (1 - γ)) + C * (k : ℝ)) * |t - s| ^ γ := by ring

/-- The sewn increment equals every positive uniform sum. -/
lemma sewnIncrement_eq_equalSewn (hγ : 1 < γ) (hC : 0 ≤ C)
    (hdiag : ∀ s ∈ Set.Icc a b, A s s = 0)
    (hdefect : ∀ s u t : ℝ, a ≤ s → s ≤ u → u ≤ t → t ≤ b →
      ‖A s t - A s u - A u t‖ ≤ C * |t - s| ^ γ)
    {k : ℕ} (hk : 0 < k) {s t : ℝ} (hs : a ≤ s) (hst : s ≤ t) (ht : t ≤ b) :
    sewnIncrement A s t = equalSewn (sewnIncrement A) s t k := by
  let Z : ℝ → ℝ → E := sewnIncrement A
  let M : ℝ := sewingConstant γ * C * (1 + (k : ℝ) ^ (1 - γ)) + C * (k : ℝ)
  let D : ℝ → ℝ → E := fun s t => Z s t - equalSewn Z s t k
  have hD := vanishes_of_midpoint (a := a) (b := b) hγ D M ?_ ?_ hs hst ht
  simpa [D, Z] using sub_eq_zero.mp hD
  · intro s t hs hst ht
    have hZ := sewnIncrement_midpoint hγ hC hdefect hs hst ht
    have hW := equalSewn_midpoint Z
      (fun s t hs hst ht => sewnIncrement_midpoint hγ hC hdefect hs hst ht) hs hst ht hk
    dsimp [D, Z]
    rw [hZ, hW]
    abel
  · intro s t hs hst ht
    simpa [D, Z, M] using norm_sewn_sub_equalSewn hγ hC hdiag hdefect hs hst ht hk

/-- A uniform subgrid reproduces the parent nodes. -/
lemma equalNode_prefix (s t : ℝ) {k j : ℕ} (hk : 0 < k) (hj : 0 < j) (i : ℕ) :
    equalNode s (equalNode s t k j) j i = equalNode s t k i := by
  unfold equalNode
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hk
  have hj0 : (j : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hj
  have hsub : (s + (t - s) * ((j : ℝ) / k)) - s = (t - s) * ((j : ℝ) / k) := by ring
  rw [hsub]
  refine congrArg (fun z => s + z) ?_
  field_simp

/-- The grid to the right of a uniform node repeats the parent nodes. -/
lemma equalNode_suffix (s t : ℝ) {k j : ℕ} (hk : 0 < k) (hj : j < k) (i : ℕ) :
    equalNode (equalNode s t k j) t (k - j) i = equalNode s t k (j + i) := by
  unfold equalNode
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hk
  have hkj : (k : ℝ) - (j : ℝ) ≠ 0 :=
    sub_ne_zero.mpr (by exact_mod_cast Nat.ne_of_gt hj)
  rw [Nat.cast_sub (Nat.le_of_lt hj), Nat.cast_add]
  have hdiff : t - (s + (t - s) * ((j : ℝ) / k)) =
      (t - s) * (((k : ℝ) - j) / k) := by
    field_simp
    ring
  rw [hdiff]
  have hmul : ((k : ℝ) - j) / k * ((i : ℝ) / ((k : ℝ) - j)) = (i : ℝ) / k := by
    field_simp
  calc
    s + (t - s) * ((j : ℝ) / k) +
        (t - s) * (((k : ℝ) - j) / k) * ((i : ℝ) / ((k : ℝ) - j)) =
        s + (t - s) * ((j : ℝ) / k) +
          (t - s) * (((k : ℝ) - j) / k * ((i : ℝ) / ((k : ℝ) - j))) := by ring
    _ = s + (t - s) * ((j : ℝ) / k) + (t - s) * ((i : ℝ) / k) := by rw [hmul]
    _ = s + (t - s) * ((j : ℝ) / k + (i : ℝ) / k) := by ring
    _ = s + (t - s) * (((j : ℝ) + i) / k) := by field_simp

/-- A uniform sum splits at an interior grid node. -/
lemma equalSewn_cut {F : Type*} [AddCommMonoid F] (Z : ℝ → ℝ → F) (s t : ℝ)
    {k j : ℕ} (hk : 0 < k) (hj0 : 0 < j) (hj : j < k) :
    equalSewn Z s t k =
      equalSewn Z s (equalNode s t k j) j +
        equalSewn Z (equalNode s t k j) t (k - j) := by
  unfold equalSewn
  have hsum : j + (k - j) = k := Nat.add_sub_of_le (Nat.le_of_lt hj)
  have hsplit := sum_range_add
    (fun i => Z (equalNode s t k i) (equalNode s t k (i + 1))) j (k - j)
  rw [hsum] at hsplit
  rw [hsplit]
  refine congrArg₂ (· + ·) ?_ ?_
  · refine sum_congr rfl fun i _ => ?_
    rw [equalNode_prefix s t hk hj0 i, equalNode_prefix s t hk hj0 (i + 1)]
  · refine sum_congr rfl fun i _ => ?_
    rw [equalNode_suffix s t hk hj i, equalNode_suffix s t hk hj (i + 1)]
    simp [Nat.add_assoc]

/-- The sewn increment is additive at every positive uniform node. -/
lemma sewnIncrement_grid_add (hγ : 1 < γ) (hC : 0 ≤ C)
    (hdiag : ∀ s ∈ Set.Icc a b, A s s = 0)
    (hdefect : ∀ s u t : ℝ, a ≤ s → s ≤ u → u ≤ t → t ≤ b →
      ‖A s t - A s u - A u t‖ ≤ C * |t - s| ^ γ)
    {s t : ℝ} (hs : a ≤ s) (hst : s ≤ t) (ht : t ≤ b) {k j : ℕ}
    (hk : 0 < k) (hj0 : 0 < j) (hj : j < k) :
    sewnIncrement A s t =
      sewnIncrement A s (equalNode s t k j) +
        sewnIncrement A (equalNode s t k j) t := by
  have hu := equalNode_mem hst hk (Nat.le_of_lt hj)
  have hksub : 0 < k - j := Nat.sub_pos_of_lt hj
  have hZ := sewnIncrement_eq_equalSewn hγ hC hdiag hdefect hk hs hst ht
  have hL := sewnIncrement_eq_equalSewn hγ hC hdiag hdefect hj0 hs hu.1 (le_trans hu.2 ht)
  have hR := sewnIncrement_eq_equalSewn hγ hC hdiag hdefect hksub (le_trans hs hu.1) hu.2 ht
  rw [hZ, hL, hR]
  exact equalSewn_cut (sewnIncrement A) s t hk hj0 hj

/-- The sewn increment is additive on every subinterval of `[a, b]`. -/
lemma sewnIncrement_add (hab : a ≤ b) (hγ : 1 < γ) (hC : 0 ≤ C)
    (hcont : ContinuousOn (fun p : ℝ × ℝ => A p.1 p.2) (sewingTriangle a b))
    (hdiag : ∀ s ∈ Set.Icc a b, A s s = 0)
    (hdefect : ∀ s u t : ℝ, a ≤ s → s ≤ u → u ≤ t → t ≤ b →
      ‖A s t - A s u - A u t‖ ≤ C * |t - s| ^ γ)
    {s u t : ℝ} (hs : a ≤ s) (hsu : s ≤ u) (hut : u ≤ t) (ht : t ≤ b) :
    sewnIncrement A s t = sewnIncrement A s u + sewnIncrement A u t := by
  have hst := hsu.trans hut
  rcases hst.eq_or_lt with hEq | hlt
  · have hu_eq : u = s := le_antisymm (hEq ▸ hut) hsu
    subst hEq
    subst hu_eq
    simp [sewnIncrement_same hdiag hs ht]
  · let ρ : ℝ := (u - s) / (t - s)
    let N : ℕ → ℕ := fun n => n + 1
    let jn : ℕ → ℕ := fun n => Nat.floor (ρ * (N n : ℝ))
    let nodeN : ℕ → ℝ := fun n => equalNode s t (N n) (jn n)
    have hρ0 : 0 ≤ ρ := div_nonneg (sub_nonneg.mpr hsu) (sub_pos.mpr hlt).le
    have hρ1 : ρ ≤ 1 := by
      rw [div_le_iff₀ (sub_pos.mpr hlt)]
      linarith
    have hnode_mem : ∀ n, s ≤ nodeN n ∧ nodeN n ≤ t := by
      intro n
      have hN : 0 < N n := Nat.succ_pos n
      have hρN : ρ * (N n : ℝ) ≤ N n := by
        exact (mul_le_mul_of_nonneg_right hρ1 (Nat.cast_nonneg _)).trans (by simp)
      exact equalNode_mem hst hN (Nat.floor_le_of_le hρN)
    have hgap : ∀ n, |nodeN n - u| ≤ (t - s) / (N n : ℝ) := by
      intro n
      have hN : 0 < N n := Nat.succ_pos n
      have hN0 : (N n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
      have hfloor : (jn n : ℝ) ≤ ρ * (N n : ℝ) :=
        Nat.floor_le (mul_nonneg hρ0 (Nat.cast_nonneg _))
      have hlt1 : ρ * (N n : ℝ) < jn n + 1 := Nat.lt_floor_add_one _
      have hnonneg : 0 ≤ ρ * (N n : ℝ) - jn n := sub_nonneg.mpr hfloor
      have hsmall : ρ * (N n : ℝ) - jn n < 1 := by linarith
      have hAlg : nodeN n - u = (t - s) * ((jn n : ℝ) / N n - ρ) := by
        have hnode : nodeN n = s + (t - s) * ((jn n : ℝ) / N n) := by
          simp [nodeN, equalNode]
        have hu : u = s + (t - s) * ρ := by
          have hts : t - s ≠ 0 := ne_of_gt (sub_pos.mpr hlt)
          simp [ρ]
          field_simp
          ring
        rw [hnode, hu]
        ring
      have hsign : (jn n : ℝ) / N n - ρ = -((ρ * N n - jn n) / N n) := by
        field_simp
        ring
      rw [hAlg, hsign, abs_mul, abs_neg, abs_of_nonneg (sub_nonneg.mpr hst)]
      rw [abs_of_nonneg (div_nonneg hnonneg (Nat.cast_nonneg _))]
      have hfrac : (ρ * (N n : ℝ) - jn n) / N n ≤ 1 / N n := by
        exact div_le_div_of_nonneg_right (le_of_lt hsmall) (Nat.cast_nonneg _)
      calc
        (t - s) * ((ρ * (N n : ℝ) - jn n) / N n) ≤ (t - s) * (1 / N n) :=
          mul_le_mul_of_nonneg_left hfrac (sub_nonneg.mpr hst)
        _ = (t - s) / N n := by rw [mul_one_div]
    have hnode : Tendsto nodeN atTop (𝓝 u) := by
      rw [Metric.tendsto_nhds]
      intro ε hε
      rw [eventually_atTop]
      obtain ⟨M, hM⟩ := exists_nat_gt ((t - s) / ε)
      refine ⟨M, fun n hn => ?_⟩
      rw [dist_eq_norm, Real.norm_eq_abs]
      have hle := hgap n
      have hden : (0 : ℝ) < N n := Nat.cast_pos.mpr (Nat.succ_pos n)
      have hquot : (t - s) / (N n : ℝ) < ε := by
        rw [div_lt_iff₀ hden]
        have hnle : (n : ℝ) ≤ N n := by simp [N]
        calc
          t - s = ((t - s) / ε) * ε := by field_simp
          _ < (M : ℝ) * ε := mul_lt_mul_of_pos_right hM hε
          _ ≤ (n : ℝ) * ε :=
            mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hn) hε.le
          _ = ε * n := by ring
          _ ≤ ε * N n := mul_le_mul_of_nonneg_left hnle hε.le
      exact hle.trans_lt hquot
    have haddN : ∀ n, sewnIncrement A s t =
        sewnIncrement A s (nodeN n) + sewnIncrement A (nodeN n) t := by
      intro n
      have hN : 0 < N n := Nat.succ_pos n
      have hρN : ρ * (N n : ℝ) ≤ N n := by
        exact (mul_le_mul_of_nonneg_right hρ1 (Nat.cast_nonneg _)).trans (by simp)
      have hjle : jn n ≤ N n := Nat.floor_le_of_le hρN
      by_cases hj0 : jn n = 0
      · have hns : nodeN n = s := by simp [nodeN, hj0, equalNode_zero]
        rw [hns, sewnIncrement_same hdiag hs (le_trans hst ht), zero_add]
      · by_cases hjN : jn n = N n
        · have hnt : nodeN n = t := by
            simpa [nodeN, hjN] using equalNode_last s t hN
          rw [hnt, sewnIncrement_same hdiag (le_trans hs hst) ht, add_zero]
        · have hjpos : 0 < jn n := Nat.pos_of_ne_zero hj0
          have hjlt : jn n < N n := lt_of_le_of_ne hjle hjN
          simpa [nodeN] using
            sewnIncrement_grid_add hγ hC hdiag hdefect hs hst ht hN hjpos hjlt
    have hpairL : Tendsto (fun n => (s, nodeN n)) atTop (𝓝[sewingTriangle a b] (s, u)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · rw [nhds_prod_eq]
        exact (tendsto_const_nhds : Tendsto (fun _ : ℕ => s) atTop (𝓝 s)).prodMk hnode
      · refine Eventually.of_forall fun n => ?_
        exact ⟨hs, (hnode_mem n).1, le_trans (hnode_mem n).2 ht⟩
    have hpairR : Tendsto (fun n => (nodeN n, t)) atTop (𝓝[sewingTriangle a b] (u, t)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · rw [nhds_prod_eq]
        exact hnode.prodMk (tendsto_const_nhds : Tendsto (fun _ : ℕ => t) atTop (𝓝 t))
      · refine Eventually.of_forall fun n => ?_
        exact ⟨le_trans hs (hnode_mem n).1, (hnode_mem n).2, ht⟩
    have hcontZ := continuousOn_sewnIncrement hab hγ hC hcont hdefect
    have hlimL : Tendsto (fun n => sewnIncrement A s (nodeN n)) atTop
        (𝓝 (sewnIncrement A s u)) := by
      have hmem : (s, u) ∈ sewingTriangle a b := ⟨hs, hsu, le_trans hut ht⟩
      exact (hcontZ.continuousWithinAt hmem).tendsto.comp hpairL
    have hlimR : Tendsto (fun n => sewnIncrement A (nodeN n) t) atTop
        (𝓝 (sewnIncrement A u t)) := by
      have hmem : (u, t) ∈ sewingTriangle a b := ⟨le_trans hs hsu, hut, ht⟩
      exact (hcontZ.continuousWithinAt hmem).tendsto.comp hpairR
    exact (tendsto_nhds_unique
      ((hlimL.add hlimR).congr' <| Eventually.of_forall fun n => (haddN n).symm)
      tendsto_const_nhds).symm

/-- Telescoping sum of consecutive real increments. -/
lemma real_telescope (f : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ range n, (f (i + 1) - f i) = f n - f 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih]
    abel

/-- Sewn increments add along a monotone sequence in `[a, b]`. -/
lemma sewnIncrement_sum_nat (hab : a ≤ b) (hγ : 1 < γ) (hC : 0 ≤ C)
    (hcont : ContinuousOn (fun p : ℝ × ℝ => A p.1 p.2) (sewingTriangle a b))
    (hdiag : ∀ s ∈ Set.Icc a b, A s s = 0)
    (hdefect : ∀ s u t : ℝ, a ≤ s → s ≤ u → u ≤ t → t ≤ b →
      ‖A s t - A s u - A u t‖ ≤ C * |t - s| ^ γ)
    (node : ℕ → ℝ) (hmono : Monotone node) (h0 : a ≤ node 0) (hb : ∀ i, node i ≤ b)
    (n : ℕ) :
    sewnIncrement A (node 0) (node n) =
      ∑ i ∈ range n, sewnIncrement A (node i) (node (i + 1)) := by
  induction n with
  | zero =>
    simp [sewnIncrement_same hdiag h0 (hb 0)]
  | succ n ih =>
    rw [sum_range_succ, ← ih]
    exact sewnIncrement_add hab hγ hC hcont hdiag hdefect h0 (hmono (Nat.zero_le n))
      (hmono (Nat.le_succ n)) (hb (n + 1))

/-- A short increment of order above one is controlled by the ambient length. -/
lemma step_rpow_le (hγ : 1 < γ) {d m : ℝ} (hd : 0 ≤ d) (hm : d ≤ m) :
    d ^ γ ≤ m ^ (γ - 1) * d := by
  rcases hd.eq_or_lt with rfl | hd0
  · simp [Real.zero_rpow (ne_of_gt (lt_trans zero_lt_one hγ)), mul_zero]
  · have hpow : d ^ (γ - 1) ≤ m ^ (γ - 1) :=
      Real.rpow_le_rpow hd hm (sub_nonneg.mpr (le_of_lt hγ))
    have hdγ : d ^ γ = d ^ (γ - 1) * d := by
      have hγeq : γ = (γ - 1) + 1 := by ring
      conv_lhs => rw [hγeq]
      exact Real.rpow_add_one (ne_of_gt hd0) (γ - 1)
    rw [hdγ]
    exact mul_le_mul_of_nonneg_right hpow hd

/-- Partition sums approach the sewn increment at rate `mesh ^ (γ - 1)`. -/
lemma norm_partition_sub (hab : a ≤ b) (hγ : 1 < γ) (hC : 0 ≤ C)
    (hcont : ContinuousOn (fun p : ℝ × ℝ => A p.1 p.2) (sewingTriangle a b))
    (hdiag : ∀ s ∈ Set.Icc a b, A s s = 0)
    (hdefect : ∀ s u t : ℝ, a ≤ s → s ≤ u → u ≤ t → t ≤ b →
      ‖A s t - A s u - A u t‖ ≤ C * |t - s| ^ γ)
    {s t : ℝ} (hs : a ≤ s) (ht : t ≤ b) (π : OrderedIntervalPartition s t) :
    ‖π.incrementSum A - sewnIncrement A s t‖ ≤
      sewingConstant γ * C * (π.mesh : ℝ) ^ (γ - 1) * (t - s) := by
  let g : ℕ → ℝ := fun i =>
    if h : i < π.size + 1 then π.node ⟨i, h⟩ else π.node (Fin.last π.size)
  have hgmono : Monotone g := by
    intro i j hij
    dsimp [g]
    by_cases hi : i < π.size + 1
    · by_cases hj : j < π.size + 1
      · rw [dite_eq_left hi, dite_eq_left hj]
        exact π.monotone_node (Fin.le_iff_val_le_val.mpr hij)
      · rw [dite_eq_left hi, dite_eq_right hj]
        exact π.monotone_node (Fin.le_last _)
    · have hj : ¬ j < π.size + 1 := not_lt.mpr ((not_lt.mp hi).trans hij)
      rw [dite_eq_right hi, dite_eq_right hj]
  have hgb : ∀ i, g i ≤ b := by
    intro i
    dsimp [g]
    split_ifs with hi
    · have hnode : π.node ⟨i, hi⟩ ≤ π.node (Fin.last π.size) :=
        π.monotone_node (Fin.le_last _)
      have ht' : π.node (Fin.last π.size) ≤ b := by simpa [π.node_last] using ht
      exact hnode.trans ht'
    · simpa [π.node_last] using ht
  have hg0 : g 0 = s := by
    have h0 : 0 < π.size + 1 := Nat.succ_pos _
    rw [show g 0 = π.node ⟨0, h0⟩ by simp [g]]
    simp [π.node_zero]
  have hgs : g π.size = t := by
    have hlt : π.size < π.size + 1 := Nat.lt_succ_self _
    have hlast : (⟨π.size, hlt⟩ : Fin (π.size + 1)) = Fin.last π.size := by
      ext; simp [Fin.val_last]
    rw [show g π.size = π.node ⟨π.size, hlt⟩ by simp [g]]
    simp [hlast, π.node_last]
  have hchain := sewnIncrement_sum_nat hab hγ hC hcont hdiag hdefect g hgmono
    (by simpa [hg0] using hs) hgb π.size
  have hpieces : ∑ i : Fin π.size,
      sewnIncrement A (π.node i.castSucc) (π.node i.succ) = sewnIncrement A s t := by
    have hterm : ∀ i : Fin π.size,
        sewnIncrement A (π.node i.castSucc) (π.node i.succ) =
          sewnIncrement A (g (i : ℕ)) (g ((i : ℕ) + 1)) := by
      intro i
      have hi0 : (i : ℕ) < π.size + 1 := Nat.lt_succ_of_lt i.isLt
      have hi1 : (i : ℕ) + 1 < π.size + 1 := Nat.succ_lt_succ i.isLt
      rw [show g (i : ℕ) = π.node ⟨(i : ℕ), hi0⟩ by simp [g],
        show g ((i : ℕ) + 1) = π.node ⟨(i : ℕ) + 1, hi1⟩ by simp [g]]
      rfl
    have hsumg :
        ∑ i : Fin π.size, sewnIncrement A (g (i : ℕ)) (g ((i : ℕ) + 1)) =
          ∑ i ∈ range π.size, sewnIncrement A (g i) (g (i + 1)) :=
      Fin.sum_univ_eq_sum_range (fun j => sewnIncrement A (g j) (g (j + 1))) π.size
    have hsame : ∑ i : Fin π.size,
        sewnIncrement A (π.node i.castSucc) (π.node i.succ) =
        ∑ i : Fin π.size, sewnIncrement A (g (i : ℕ)) (g ((i : ℕ) + 1)) :=
      Finset.sum_congr rfl fun i _ => hterm i
    rw [hsame, hsumg, ← hchain, hg0, hgs]
  rw [show π.incrementSum A - sewnIncrement A s t =
      ∑ i : Fin π.size, (A (π.node i.castSucc) (π.node i.succ) -
        sewnIncrement A (π.node i.castSucc) (π.node i.succ)) by
    unfold OrderedIntervalPartition.incrementSum
    rw [← hpieces, sum_sub_distrib]]
  refine (norm_sum_le _ _).trans ?_
  have hstep : ∀ i : Fin π.size,
      ‖A (π.node i.castSucc) (π.node i.succ) -
        sewnIncrement A (π.node i.castSucc) (π.node i.succ)‖ ≤
        sewingConstant γ * C * (π.mesh : ℝ) ^ (γ - 1) *
          (π.node i.succ - π.node i.castSucc) := by
    intro i
    have hxy : π.node i.castSucc ≤ π.node i.succ :=
      π.monotone_node (Fin.castSucc_le_succ i)
    have hx : a ≤ π.node i.castSucc := by
      have h0 : s ≤ π.node i.castSucc := by
        simpa [π.node_zero] using π.monotone_node (Fin.zero_le i.castSucc)
      exact le_trans hs h0
    have hy : π.node i.succ ≤ b := by
      have hnode : π.node i.succ ≤ π.node (Fin.last π.size) :=
        π.monotone_node (Fin.le_last _)
      have ht' : π.node (Fin.last π.size) ≤ b := by simpa [π.node_last] using ht
      exact hnode.trans ht'
    have hΔ : 0 ≤ π.node i.succ - π.node i.castSucc := sub_nonneg.mpr hxy
    have hmesh : π.node i.succ - π.node i.castSucc ≤ (π.mesh : ℝ) := by
      let fmesh : Fin π.size → ℝ≥0 := fun j =>
        (π.node j.succ - π.node j.castSucc).toNNReal
      have hsup : fmesh i ≤ Finset.univ.sup fmesh :=
        Finset.le_sup (Finset.mem_univ i)
      have hcoe : (fmesh i : ℝ) ≤ (π.mesh : ℝ) := by
        unfold OrderedIntervalPartition.mesh
        exact NNReal.coe_le_coe.mpr hsup
      rwa [show (fmesh i : ℝ) = π.node i.succ - π.node i.castSucc by
        simp [fmesh, Real.coe_toNNReal', max_eq_left hΔ]] at hcoe
    have hnorm := norm_sewnIncrement_sub hγ hC hdefect hx hxy hy
    have habs : |π.node i.succ - π.node i.castSucc| =
        π.node i.succ - π.node i.castSucc := abs_of_nonneg hΔ
    calc
      ‖A (π.node i.castSucc) (π.node i.succ) -
          sewnIncrement A (π.node i.castSucc) (π.node i.succ)‖ ≤
          sewingConstant γ * C * |π.node i.succ - π.node i.castSucc| ^ γ := by
        simpa [norm_sub_rev] using hnorm
      _ = sewingConstant γ * C * (π.node i.succ - π.node i.castSucc) ^ γ := by rw [habs]
      _ ≤ sewingConstant γ * C *
          ((π.mesh : ℝ) ^ (γ - 1) * (π.node i.succ - π.node i.castSucc)) := by
        exact mul_le_mul_of_nonneg_left (step_rpow_le hγ hΔ hmesh)
          (mul_nonneg (sewingConstant_pos hγ).le hC)
      _ = sewingConstant γ * C * (π.mesh : ℝ) ^ (γ - 1) *
          (π.node i.succ - π.node i.castSucc) := by ring
  refine (Finset.sum_le_sum fun i _ => hstep i).trans ?_
  have hsumΔ : ∑ i : Fin π.size, (π.node i.succ - π.node i.castSucc) = t - s := by
    let f : ℕ → ℝ := fun j => if h : j < π.size + 1 then π.node ⟨j, h⟩ else t
    have hId : ∑ i ∈ range π.size, (f (i + 1) - f i) = t - s := by
      rw [real_telescope f π.size]
      have hf0 : f 0 = s := by
        have h0 : 0 < π.size + 1 := Nat.succ_pos _
        rw [show f 0 = π.node ⟨0, h0⟩ by simp [f]]
        simp [π.node_zero]
      have hfn : f π.size = t := by
        have hlt : π.size < π.size + 1 := Nat.lt_succ_self _
        have hlast : (⟨π.size, hlt⟩ : Fin (π.size + 1)) = Fin.last π.size := by
          ext; simp [Fin.val_last]
        rw [show f π.size = π.node ⟨π.size, hlt⟩ by simp [f]]
        simp [hlast, π.node_last]
      rw [hf0, hfn]
    have hterm : ∀ i : Fin π.size,
        π.node i.succ - π.node i.castSucc = f ((i : ℕ) + 1) - f (i : ℕ) := by
      intro i
      have hi0 : (i : ℕ) < π.size + 1 := Nat.lt_succ_of_lt i.isLt
      have hi1 : (i : ℕ) + 1 < π.size + 1 := Nat.succ_lt_succ i.isLt
      rw [show f (i : ℕ) = π.node ⟨(i : ℕ), hi0⟩ by simp [f],
        show f ((i : ℕ) + 1) = π.node ⟨(i : ℕ) + 1, hi1⟩ by simp [f]]
      rfl
    have hsumg : ∑ i : Fin π.size, (f ((i : ℕ) + 1) - f (i : ℕ)) =
        ∑ i ∈ range π.size, (f (i + 1) - f i) :=
      Fin.sum_univ_eq_sum_range (fun j => f (j + 1) - f j) π.size
    have hsame : ∑ i : Fin π.size, (π.node i.succ - π.node i.castSucc) =
        ∑ i : Fin π.size, (f ((i : ℕ) + 1) - f (i : ℕ)) :=
      Finset.sum_congr rfl fun i _ => hterm i
    exact (hsame.trans hsumg).trans hId
  rw [← Finset.mul_sum, hsumΔ]

/-- Uniform partition into `n` equal steps. -/
def uniformPartition {s t : ℝ} (hst : s ≤ t) (n : ℕ) (hn : 0 < n) :
    OrderedIntervalPartition s t where
  size := n
  node := fun i => equalNode s t n (i : ℕ)
  monotone_node := fun i j hij =>
    equalNode_mono hst n (Fin.le_iff_val_le_val.mp hij)
  node_zero := by simp [equalNode_zero]
  node_last := by simpa [Fin.val_last] using equalNode_last s t hn

/-- The mesh of a uniform partition is the common step length. -/
lemma uniformPartition_mesh {s t : ℝ} (hst : s ≤ t) {n : ℕ} (hn : 0 < n) :
    ((uniformPartition hst n hn).mesh : ℝ) = (t - s) / n := by
  have hΔ : ∀ i : Fin n,
      (uniformPartition hst n hn).node i.succ -
        (uniformPartition hst n hn).node i.castSucc = (t - s) / (n : ℝ) := by
    intro i
    simp only [uniformPartition]
    rw [Fin.val_succ, Fin.val_castSucc]
    exact equalNode_sub s t n (i : ℕ)
  unfold OrderedIntervalPartition.mesh
  set c := Real.toNNReal ((t - s) / (n : ℝ))
  have hfun : ∀ i : Fin n,
      ((uniformPartition hst n hn).node i.succ -
        (uniformPartition hst n hn).node i.castSucc).toNNReal = c := by
    intro i
    rw [hΔ i]
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have hsup : (Finset.univ.sup fun i : Fin n =>
      ((uniformPartition hst n hn).node i.succ -
        (uniformPartition hst n hn).node i.castSucc).toNNReal) = c := by
    refine Eq.trans (Finset.sup_congr rfl fun i _ => hfun i) ?_
    exact Finset.sup_const (α := ℝ≥0) hne c
  exact (congrArg (fun x : ℝ≥0 => (x : ℝ)) hsup).trans (by
    rw [Real.coe_toNNReal',
      max_eq_left (div_nonneg (sub_nonneg.mpr hst) (Nat.cast_nonneg _))])

/-- Every positive width is realized by some ordered partition. -/
lemma exists_mesh_lt {s t : ℝ} (hst : s ≤ t) {δ : ℝ} (hδ : 0 < δ) :
    ∃ π : OrderedIntervalPartition s t, (π.mesh : ℝ) < δ := by
  let n := Nat.floor ((t - s) / δ) + 1
  have hn : 0 < n := Nat.succ_pos _
  refine ⟨uniformPartition hst n hn, ?_⟩
  rw [uniformPartition_mesh hst hn]
  have hden : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  rw [div_lt_iff₀ hden]
  have hfloor : (t - s) / δ < n := by
    simpa [n, Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one ((t - s) / δ)
  calc
    t - s = ((t - s) / δ) * δ := by field_simp
    _ < (n : ℝ) * δ := mul_lt_mul_of_pos_right hfloor hδ
    _ = δ * n := by ring

omit [CompleteSpace E] in
/-- Two partition-sum limits on the same interval agree. -/
lemma partitionLimit_unique {s t : ℝ} (hst : s ≤ t) {z₁ z₂ : E}
    (h₁ : PartitionSumsConverge A s t z₁) (h₂ : PartitionSumsConverge A s t z₂) :
    z₁ = z₂ := by
  by_contra hne
  have hpos : 0 < ‖z₁ - z₂‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  obtain ⟨δ₁, hδ₁, hclose₁⟩ := h₁ (‖z₁ - z₂‖ / 2) (half_pos hpos)
  obtain ⟨δ₂, hδ₂, hclose₂⟩ := h₂ (‖z₁ - z₂‖ / 2) (half_pos hpos)
  have hδ : 0 < min δ₁ δ₂ := lt_min hδ₁ hδ₂
  obtain ⟨π, hmesh⟩ := exists_mesh_lt hst hδ
  have h1 := hclose₁ π (lt_of_lt_of_le hmesh (min_le_left _ _))
  have h2 := hclose₂ π (lt_of_lt_of_le hmesh (min_le_right _ _))
  have hlt : ‖z₁ - z₂‖ < ‖z₁ - z₂‖ := by
    calc
      ‖z₁ - z₂‖ = ‖(z₁ - π.incrementSum A) + (π.incrementSum A - z₂)‖ := by
        congr 1
        abel
      _ ≤ ‖z₁ - π.incrementSum A‖ + ‖π.incrementSum A - z₂‖ := norm_add_le _ _
      _ = ‖π.incrementSum A - z₁‖ + ‖π.incrementSum A - z₂‖ := by rw [norm_sub_rev]
      _ < ‖z₁ - z₂‖ / 2 + ‖z₁ - z₂‖ / 2 := add_lt_add h1 h2
      _ = ‖z₁ - z₂‖ := by ring
  exact lt_irrefl _ hlt

end Sewing

end CKMA
