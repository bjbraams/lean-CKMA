/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.HasLaw
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Moments.Covariance
import Mathlib.Probability.Moments.Variance
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Brownian quadratic variation and covariation (08.7)

`TimePartition` records ordered deterministic nodes, allowing repeated nodes and the
zero time interval. Its mesh controls quadratic and bilinear covariation sums formed
from completed partition intervals. The main statements give uniform convergence in
probability, almost-sure convergence under a summable mesh condition, and cross-coordinate
covariation for independent Brownian coordinates.

The process interface is pre-Brownian: for a sequence of deterministic partitions only
countably many evaluation times are involved. Time and partition nodes are nonnegative
reals; covariance normalization is the standard Brownian one.

The uniform estimate is Kolmogorov's maximal inequality applied to the centered sum of
squared increments. The Gaussian fourth moment is read from the fourth derivative of the
moment-generating function. Cross variation reduces to quadratic variation by polarization.
-/

@[expose] public section

noncomputable section

namespace CKMA

open scoped NNReal ENNReal ProbabilityTheory

open Classical
open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators

/-- A finite deterministic partition of `[0,T]`. Repeated nodes are allowed. -/
structure TimePartition (T : ℝ≥0) where
  /-- Number of increments. -/
  size : ℕ
  /-- Partition nodes, including both endpoints. -/
  node : Fin (size + 1) → ℝ≥0
  /-- Time ordering. -/
  monotone_node : Monotone node
  /-- Initial endpoint. -/
  node_zero : node 0 = 0
  /-- Terminal endpoint. -/
  node_last : node (Fin.last size) = T

/-- Largest time increment of a finite partition. -/
def TimePartition.mesh {T : ℝ≥0} (π : TimePartition T) : ℝ≥0 :=
  Finset.univ.sup fun i : Fin π.size ↦ π.node i.succ - π.node i.castSucc

/-- Quadratic covariation using completed partition intervals up to time `t`.
It is constant between adjacent nodes, as in the argument of `GAPS_EASY.md`. -/
def TimePartition.covariation {Ω : Type*} {T : ℝ≥0} (π : TimePartition T)
    (B C : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∑ i : Fin π.size, if π.node i.succ ≤ t then
    (B (π.node i.succ) ω - B (π.node i.castSucc) ω) *
    (C (π.node i.succ) ω - C (π.node i.castSucc) ω) else 0

namespace TimePartition

variable {T : ℝ≥0} (π : TimePartition T)

/-- Number of partition intervals completed by time `t`. -/
def completedCount (t : ℝ≥0) : ℕ :=
  (Finset.univ.filter fun i : Fin π.size ↦ π.node i.succ ≤ t).card

/-- The completed-count index is at most the number of increments. -/
lemma completedCount_le_size (t : ℝ≥0) : π.completedCount t ≤ π.size := by
  simpa only [completedCount, Finset.card_univ, Fintype.card_fin] using
    Finset.card_filter_le (Finset.univ : Finset (Fin π.size))
      fun i : Fin π.size ↦ π.node i.succ ≤ t

/-- Right endpoint of the last interval completed by time `t`. -/
def covered (t : ℝ≥0) : ℝ≥0 :=
  π.node ⟨π.completedCount t, Nat.lt_succ_of_le (π.completedCount_le_size t)⟩

/-- Completed intervals form an initial segment of the partition. -/
lemma completed_iff_val_lt (t : ℝ≥0) (i : Fin π.size) :
    π.node i.succ ≤ t ↔ i.val < π.completedCount t := by
  have hdown : ∀ a b : Fin π.size, a ≤ b → π.node b.succ ≤ t → π.node a.succ ≤ t := by
    intro a b hab hb
    exact (π.monotone_node (Fin.succ_le_succ_iff.mpr hab)).trans hb
  constructor
  · intro hi
    have hsub : Finset.Iic i ⊆ Finset.univ.filter fun j : Fin π.size ↦ π.node j.succ ≤ t := by
      intro j hj
      rw [Finset.mem_Iic] at hj
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hdown j i hj hi⟩
    have hcard : (Finset.Iic i).card ≤ π.completedCount t := by
      simpa only [completedCount] using Finset.card_le_card hsub
    have hic : (Finset.Iic i).card = i.val + 1 := by
      simpa using Fin.card_Iic i
    omega
  · intro hi
    by_contra hnot
    have hsub : Finset.univ.filter (fun j : Fin π.size ↦ π.node j.succ ≤ t) ⊆ Finset.Iio i := by
      intro j hj
      rw [Finset.mem_filter] at hj
      rw [Finset.mem_Iio]
      by_contra hge
      exact hnot (hdown i j (le_of_not_gt hge) hj.2)
    have hcard : π.completedCount t ≤ i.val := by
      refine le_trans (Finset.card_le_card hsub) ?_
      simpa using Fin.card_Iio i
    omega

/-- Real length of one partition increment. -/
def increment (i : Fin π.size) : ℝ :=
  ((π.node i.succ - π.node i.castSucc : ℝ≥0) : ℝ)

/-- Sum of the first `m` real increments equals the corresponding node. -/
lemma sum_increment_initial :
    ∀ m (hm : m ≤ π.size),
      ∑ i ∈ Finset.univ.filter fun i : Fin π.size ↦ i.val < m, π.increment i =
        (π.node ⟨m, Nat.lt_succ_of_le hm⟩ : ℝ) := by
  intro m
  induction m with
  | zero =>
    intro hm
    simp only [Nat.not_lt_zero, Finset.filter_false, Finset.sum_empty]
    have hz : (⟨0, Nat.lt_succ_of_le hm⟩ : Fin (π.size + 1)) = 0 := by ext; simp
    simp [hz, π.node_zero]
  | succ m ih =>
    intro hm
    have hm' : m < π.size := Nat.lt_of_succ_le hm
    have hmle : m ≤ π.size := Nat.le_of_lt hm'
    let j : Fin π.size := ⟨m, hm'⟩
    have hnot : j ∉ Finset.univ.filter fun i : Fin π.size ↦ i.val < m := by
      simp [j]
    have hsplit : Finset.univ.filter (fun i : Fin π.size ↦ i.val < m + 1) =
        insert j (Finset.univ.filter fun i : Fin π.size ↦ i.val < m) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, j]
      constructor
      · intro hi
        rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with hlt | heq
        · exact Or.inr hlt
        · exact Or.inl (by apply Fin.ext; simpa [j] using heq)
      · intro hi
        rcases hi with hEq | hlt
        · simp [hEq, j]
        · omega
    rw [hsplit, Finset.sum_insert hnot, ih hmle, increment]
    have hsucc : j.succ = ⟨m + 1, Nat.lt_succ_of_le hm⟩ := by
      apply Fin.ext
      simp only [Fin.val_succ, Fin.val_mk, j]
    have hcast : j.castSucc = ⟨m, Nat.lt_succ_of_le hmle⟩ := by
      apply Fin.ext
      simp only [Fin.val_castSucc, Fin.val_mk, j]
    rw [hsucc, hcast]
    have hle : π.node ⟨m, Nat.lt_succ_of_le hmle⟩ ≤
        π.node ⟨m + 1, Nat.lt_succ_of_le hm⟩ :=
      π.monotone_node (by rw [← hcast, ← hsucc]; exact Fin.castSucc_le_succ j)
    rw [NNReal.coe_sub hle]
    ring

/-- The increments of a partition of `[0,T]` sum to `T`. -/
lemma sum_increment : ∑ i : Fin π.size, π.increment i = (T : ℝ) := by
  have h := π.sum_increment_initial π.size le_rfl
  have hfilter : Finset.univ.filter (fun i : Fin π.size ↦ i.val < π.size) = Finset.univ := by
    ext i; simp [i.isLt]
  have hlast : (⟨π.size, Nat.lt_succ_self π.size⟩ : Fin (π.size + 1)) = Fin.last π.size := by
    ext; simp [Fin.val_last]
  simpa [hfilter, hlast, π.node_last] using h

/-- Each real increment is at most the mesh. -/
lemma increment_le_mesh (i : Fin π.size) : π.increment i ≤ π.mesh := by
  simpa only [increment, mesh] using
    (NNReal.coe_le_coe.mpr
      (Finset.le_sup (f := fun j : Fin π.size ↦ π.node j.succ - π.node j.castSucc)
        (Finset.mem_univ i)))

/-- Sum of squared increments is at most mesh times `T`. -/
lemma sum_sq_increment_le : ∑ i : Fin π.size, π.increment i ^ 2 ≤ (π.mesh : ℝ) * (T : ℝ) := by
  calc
    ∑ i : Fin π.size, π.increment i ^ 2
        ≤ ∑ i : Fin π.size, (π.mesh : ℝ) * π.increment i := by
          refine Finset.sum_le_sum fun i _ ↦ ?_
          have hinc : 0 ≤ π.increment i := by simp [increment]
          nlinarith [π.increment_le_mesh i, hinc, sq_nonneg (π.increment i)]
    _ = (π.mesh : ℝ) * ∑ i : Fin π.size, π.increment i := by rw [Finset.mul_sum]
    _ = (π.mesh : ℝ) * (T : ℝ) := by rw [π.sum_increment]

/-- On `[0,T]`, time differs from the covered node by at most the mesh. -/
lemma abs_t_sub_covered_le_mesh {t : ℝ≥0} (ht : t ≤ T) :
    |(t : ℝ) - (π.covered t : ℝ)| ≤ π.mesh := by
  have hk : π.completedCount t ≤ π.size := π.completedCount_le_size t
  by_cases h0 : π.completedCount t = 0
  · have hcov : π.covered t = 0 := by simp [covered, h0, π.node_zero]
    rw [hcov, NNReal.coe_zero, sub_zero, abs_of_nonneg (NNReal.coe_nonneg _)]
    by_cases hsize : π.size = 0
    · have hlast0 : Fin.last π.size = (0 : Fin (π.size + 1)) := by
        apply Fin.ext
        simp [hsize, Fin.val_last]
      have hT : T = 0 := by
        simpa [hlast0, π.node_zero, eq_comm] using π.node_last
      have ht0 : t = 0 := le_antisymm (ht.trans (le_of_eq hT)) (zero_le : 0 ≤ t)
      simp [ht0]
    · let i0 : Fin π.size := ⟨0, Nat.pos_of_ne_zero hsize⟩
      have hnot : ¬ π.node i0.succ ≤ t := by
        intro hle
        have hlt := (π.completed_iff_val_lt t i0).1 hle
        simp [h0, i0, Fin.val_mk] at hlt
      have htlt : (t : ℝ) < π.node i0.succ := NNReal.coe_lt_coe.mpr (not_le.mp hnot)
      have hstep : (π.node i0.succ : ℝ) ≤ π.mesh := by
        have hinc := π.increment_le_mesh i0
        have hcast : i0.castSucc = 0 := by
          apply Fin.ext
          simp [i0]
        have hle0 : π.node 0 ≤ π.node i0.succ := by simp [π.node_zero]
        rw [increment, hcast] at hinc
        rw [NNReal.coe_sub hle0, π.node_zero, NNReal.coe_zero, sub_zero] at hinc
        exact hinc
      exact (le_of_lt htlt).trans hstep
  · by_cases hlast : π.completedCount t = π.size
    · have hidx : (⟨π.size, Nat.lt_succ_self π.size⟩ : Fin (π.size + 1)) =
          Fin.last π.size := by
        apply Fin.ext
        simp [Fin.val_last]
      have hcov : π.covered t = T := by
        simp [covered, hlast, hidx, π.node_last]
      have hsize : 0 < π.size := Nat.pos_of_ne_zero (fun hzero ↦ h0 (hlast.trans hzero))
      let i : Fin π.size := ⟨π.size - 1, Nat.sub_lt hsize (by decide)⟩
      have hi : i.val = π.size - 1 := by simp [i, Fin.val_mk]
      have hval : i.val < π.completedCount t := by
        rw [hi, hlast]
        omega
      have hcomp : π.node i.succ ≤ t := (π.completed_iff_val_lt t i).2 hval
      have hsucc : i.succ = Fin.last π.size := by
        apply Fin.ext
        simp only [Fin.val_succ, Fin.val_last, hi]
        omega
      have hTle : T ≤ t := by simpa [hsucc, π.node_last] using hcomp
      have htEq : t = T := le_antisymm ht hTle
      subst htEq
      simp [hcov]
    · have hkpos : 0 < π.completedCount t := Nat.pos_of_ne_zero h0
      have hklt : π.completedCount t < π.size := lt_of_le_of_ne hk hlast
      let ileft : Fin π.size := ⟨π.completedCount t - 1, by omega⟩
      let iright : Fin π.size := ⟨π.completedCount t, hklt⟩
      have hleftVal : ileft.val = π.completedCount t - 1 := by simp [ileft, Fin.val_mk]
      have hrightVal : iright.val = π.completedCount t := by simp [iright, Fin.val_mk]
      have hleft : π.node ileft.succ ≤ t :=
        (π.completed_iff_val_lt t ileft).2 (by omega)
      have hright : ¬ π.node iright.succ ≤ t := by
        intro hle
        have hlt := (π.completed_iff_val_lt t iright).1 hle
        rw [hrightVal] at hlt
        omega
      have hcovL : π.covered t = π.node ileft.succ := by
        apply congrArg π.node
        apply Fin.ext
        simp only [covered, Fin.val_mk, Fin.val_succ, hleftVal]
        omega
      have hcovR : π.covered t = π.node iright.castSucc := by
        apply congrArg π.node
        apply Fin.ext
        simp only [covered, Fin.val_mk, Fin.val_castSucc, hrightVal]
      have hs_le_t : (π.covered t : ℝ) ≤ t := by
        rw [hcovL]
        exact NNReal.coe_le_coe.mpr hleft
      have ht_lt : (t : ℝ) < π.node iright.succ := NNReal.coe_lt_coe.mpr (not_le.mp hright)
      have hstep : (π.node iright.succ : ℝ) - (π.covered t : ℝ) ≤ π.mesh := by
        have hleNodes : π.node iright.castSucc ≤ π.node iright.succ :=
          π.monotone_node (Fin.castSucc_le_succ iright)
        have hsub : (π.node iright.succ : ℝ) - (π.node iright.castSucc : ℝ) ≤ π.mesh := by
          rw [← NNReal.coe_sub hleNodes]
          exact π.increment_le_mesh iright
        rw [hcovR]
        exact hsub
      have hdiff : (t : ℝ) - (π.covered t : ℝ) ≤ π.mesh :=
        le_of_lt (lt_of_lt_of_le (by linarith) hstep)
      rw [abs_of_nonneg (sub_nonneg.mpr hs_le_t)]
      exact hdiff

end TimePartition

/-- A finite sum of measurable real functions is measurable. -/
private lemma measurable_finset_sum {α ι : Type*} [MeasurableSpace α] {s : Finset ι}
    {f : ι → α → ℝ} (hf : ∀ i ∈ s, Measurable (f i)) :
    Measurable (fun a ↦ ∑ i ∈ s, f i a) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add
      (ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))

/-- Indices strictly before a partial-sum time. -/
private def pastFinset (n : ℕ) (k : Fin (n + 1)) : Finset (Fin n) :=
  Finset.univ.filter fun i ↦ i.val < k.val

/-- Indices at or after a partial-sum time. -/
private def futureFinset (n : ℕ) (k : Fin (n + 1)) : Finset (Fin n) :=
  Finset.univ.filter fun i ↦ k.val ≤ i.val

/-- Sum of the family over indices strictly before `k`. -/
private def partialSum {Ω : Type*} {n : ℕ} (X : Fin n → Ω → ℝ) (k : Fin (n + 1)) : Ω → ℝ :=
  fun ω ↦ ∑ i ∈ pastFinset n k, X i ω

/-- The last partial sum is the sum of the whole family. -/
private lemma partialSum_last {Ω : Type*} {n : ℕ} (X : Fin n → Ω → ℝ) (ω : Ω) :
    partialSum X (Fin.last n) ω = ∑ i : Fin n, X i ω := by
  have hpast : pastFinset n (Fin.last n) = Finset.univ := by
    ext i
    simp [pastFinset, Fin.val_last, i.isLt]
  simp [partialSum, hpast]

/-- Past and future index sets partition the family. -/
private lemma past_future_partition (n : ℕ) (k : Fin (n + 1)) :
    Disjoint (pastFinset n k) (futureFinset n k) ∧
      pastFinset n k ∪ futureFinset n k = Finset.univ := by
  constructor
  · rw [Finset.disjoint_left]
    intro i hi hf
    exact not_le_of_gt (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hf).2
  · ext i
    constructor
    · intro _
      exact Finset.mem_univ i
    · intro _
      rcases lt_or_ge i.val k.val with hlt | hge
      · exact Finset.mem_union_left _ (by simp [pastFinset, hlt])
      · exact Finset.mem_union_right _ (by simp [futureFinset, hge])

/-- The full sum splits as the partial sum plus the future sum. -/
private lemma partialSum_add_future {Ω : Type*} {n : ℕ} (X : Fin n → Ω → ℝ)
    (k : Fin (n + 1)) (ω : Ω) :
    partialSum X (Fin.last n) ω =
      partialSum X k ω + ∑ i ∈ futureFinset n k, X i ω := by
  have hlast : pastFinset n (Fin.last n) = Finset.univ := by
    ext i
    simp [pastFinset, Fin.val_last, i.isLt]
  rw [partialSum, partialSum, hlast, ← (past_future_partition n k).2,
    Finset.sum_union (past_future_partition n k).1]

/-- First time the partial sums reach height `ε`. -/
private def firstHitSet {Ω : Type*} {n : ℕ} (X : Fin n → Ω → ℝ) (ε : ℝ)
    (k : Fin (n + 1)) : Set Ω :=
  {ω | ε ≤ |partialSum X k ω|} ∩
    {ω | ∀ j : Fin (n + 1), j < k → |partialSum X j ω| < ε}

/-- Partial sums of a measurable family are measurable. -/
private lemma measurable_partialSum {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    {X : Fin n → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (k : Fin (n + 1)) :
    Measurable (partialSum X k) :=
  measurable_finset_sum fun i _ ↦ hX i

/-- The first-hit set of a measurable family is measurable. -/
private lemma measurableSet_firstHit {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    {X : Fin n → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (ε : ℝ) (k : Fin (n + 1)) :
    MeasurableSet (firstHitSet X ε k) := by
  refine MeasurableSet.inter ?_ ?_
  · exact measurableSet_le measurable_const
      (continuous_abs.measurable.comp (measurable_partialSum hX k))
  · have hset : {ω | ∀ j : Fin (n + 1), j < k → |partialSum X j ω| < ε} =
        ⋂ j : {j : Fin (n + 1) // j < k}, {ω | |partialSum X j.1 ω| < ε} := by
      ext ω
      simp
    rw [hset]
    refine MeasurableSet.iInter fun j ↦ ?_
    exact measurableSet_lt
      (continuous_abs.measurable.comp (measurable_partialSum hX j.1)) measurable_const

/-- Distinct first-hit sets are disjoint. -/
private lemma pairwise_firstHit {Ω : Type*} {n : ℕ} (X : Fin n → Ω → ℝ) (ε : ℝ) :
    Pairwise fun k m ↦ Disjoint (firstHitSet X ε k) (firstHitSet X ε m) := by
  intro k m hkm
  rcases lt_or_gt_of_ne hkm with hlt | hgt
  · refine Set.disjoint_left.2 fun ω hωk hωm ↦ ?_
    have hltAbs : |partialSum X k ω| < ε := hωm.2 k hlt
    have hge : ε ≤ |partialSum X k ω| := hωk.1
    exact not_lt_of_ge hge hltAbs
  · refine Set.disjoint_left.2 fun ω hωk hωm ↦ ?_
    have hltAbs : |partialSum X m ω| < ε := hωk.2 m hgt
    have hge : ε ≤ |partialSum X m ω| := hωm.1
    exact not_lt_of_ge hge hltAbs

/-- The first-hit sets cover every path whose partial sums reach height `ε`. -/
private lemma iUnion_firstHit {Ω : Type*} {n : ℕ} (X : Fin n → Ω → ℝ) (ε : ℝ) :
    ⋃ k, firstHitSet X ε k = {ω | ∃ k : Fin (n + 1), ε ≤ |partialSum X k ω|} := by
  ext ω
  constructor
  · intro hω
    obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hω
    exact ⟨k, hk.1⟩
  · intro hω
    obtain ⟨k0, hk0⟩ := hω
    let s : Finset (Fin (n + 1)) :=
      Finset.univ.filter fun k ↦ ε ≤ |partialSum X k ω|
    have hs : s.Nonempty := ⟨k0, by simp [s, hk0]⟩
    let k := s.min' hs
    have hkmem : k ∈ s := Finset.min'_mem s hs
    have hkle : ε ≤ |partialSum X k ω| := by
      simpa [s] using hkmem
    have hearly : ∀ j : Fin (n + 1), j < k → |partialSum X j ω| < ε := by
      intro j hj
      have hnot : j ∉ s := by
        intro hjs
        have hmin := Finset.min'_le s j hjs
        exact not_le_of_gt hj hmin
      have hlt : ¬ ε ≤ |partialSum X j ω| := by simpa [s] using hnot
      exact lt_of_not_ge hlt
    exact Set.mem_iUnion.2 ⟨k, ⟨hkle, hearly⟩⟩

/-- Partial sum of a past tuple, using only coordinates before `j`. -/
private def subtypeSum {n : ℕ} (k j : Fin (n + 1))
    (f : {i : Fin n // i ∈ pastFinset n k} → ℝ) : ℝ :=
  ∑ i : pastFinset n k, if i.1.val < j.val then f i else 0

/-- Value of the past tuple on the first-hit event, and zero otherwise. -/
private def hitOfPast {n : ℕ} (k : Fin (n + 1)) (ε : ℝ)
    (f : {i : Fin n // i ∈ pastFinset n k} → ℝ) : ℝ :=
  if (∀ j : Fin (n + 1), j < k → |subtypeSum k j f| < ε) ∧ ε ≤ |subtypeSum k k f| then
    subtypeSum k k f else 0

/-- Sum of a future tuple. -/
private def tailOfFuture {n : ℕ} (k : Fin (n + 1))
    (g : {i : Fin n // i ∈ futureFinset n k} → ℝ) : ℝ :=
  ∑ i, g i

/-- A coordinatewise truncated sum of a tuple is measurable. -/
private lemma measurable_subtypeSum {n : ℕ} (k j : Fin (n + 1)) :
    Measurable (subtypeSum k j) := by
  unfold subtypeSum
  refine measurable_finset_sum fun i _ ↦ ?_
  by_cases h : i.1.val < j.val
  · simpa [h] using measurable_pi_apply i
  · simpa [h] using measurable_const

/-- The first-hit functional of the past tuple is measurable. -/
private lemma measurable_hitOfPast {n : ℕ} (k : Fin (n + 1)) (ε : ℝ) :
    Measurable (hitOfPast k ε) := by
  have hset : MeasurableSet {f |
      (∀ j : Fin (n + 1), j < k → |subtypeSum k j f| < ε) ∧
        ε ≤ |subtypeSum k k f|} := by
    have hrewrite : {f |
        (∀ j : Fin (n + 1), j < k → |subtypeSum k j f| < ε) ∧
          ε ≤ |subtypeSum k k f|} =
        (⋂ j : {j : Fin (n + 1) // j < k}, {f | |subtypeSum k j.1 f| < ε}) ∩
          {f | ε ≤ |subtypeSum k k f|} := by
      ext f
      simp
    rw [hrewrite]
    refine MeasurableSet.inter ?_ ?_
    · refine MeasurableSet.iInter fun j ↦ ?_
      exact measurableSet_lt (continuous_abs.measurable.comp (measurable_subtypeSum k j.1))
        measurable_const
    · exact measurableSet_le measurable_const
        (continuous_abs.measurable.comp (measurable_subtypeSum k k))
  unfold hitOfPast
  exact (measurable_subtypeSum k k).ite hset measurable_const

/-- The future-sum functional is measurable. -/
private lemma measurable_tailOfFuture {n : ℕ} (k : Fin (n + 1)) :
    Measurable (tailOfFuture k) := by
  unfold tailOfFuture
  exact measurable_finset_sum fun i _ ↦ measurable_pi_apply i

/-- Reading the past from the family reproduces partial sums up to time `k`. -/
private lemma subtypeSum_eq_partialSum {Ω : Type*} {n : ℕ} (X : Fin n → Ω → ℝ)
    (k j : Fin (n + 1)) (hj : j ≤ k) (ω : Ω) :
    subtypeSum k j (fun i ↦ X i.1 ω) = partialSum X j ω := by
  rw [subtypeSum, partialSum]
  have hcoe := Finset.sum_coe_sort (s := pastFinset n k)
    (fun i ↦ if i.val < j.val then X i ω else 0)
  rw [hcoe, ← Finset.sum_filter]
  have hjv : j.val ≤ k.val := (Fin.le_def).mp hj
  have hfilt : (pastFinset n k).filter (fun i ↦ i.val < j.val) = pastFinset n j := by
    ext i
    simp only [pastFinset, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      exact h.2
    · intro h
      exact ⟨lt_of_lt_of_le h hjv, h⟩
  rw [hfilt]

/-- The past functional reproduces the partial sum on the first-hit set. -/
private lemma hitOfPast_eq_indicator {Ω : Type*} {n : ℕ} (X : Fin n → Ω → ℝ)
    (k : Fin (n + 1)) (ε : ℝ) (ω : Ω) :
    hitOfPast k ε (fun i ↦ X i.1 ω) =
      (firstHitSet X ε k).indicator (partialSum X k) ω := by
  have hps : ∀ j : Fin (n + 1), j ≤ k →
      subtypeSum k j (fun i ↦ X i.1 ω) = partialSum X j ω :=
    fun j hj ↦ subtypeSum_eq_partialSum X k j hj ω
  by_cases hmem : ω ∈ firstHitSet X ε k
  · rw [Set.indicator_of_mem hmem]
    have hcond : (∀ j : Fin (n + 1), j < k →
        |subtypeSum k j (fun i ↦ X i.1 ω)| < ε) ∧
        ε ≤ |subtypeSum k k (fun i ↦ X i.1 ω)| := by
      constructor
      · intro j hj
        rw [hps j hj.le]
        exact hmem.2 j hj
      · rw [hps k le_rfl]
        exact hmem.1
    rw [hitOfPast, ite_eq_left hcond]
    exact hps k le_rfl
  · rw [Set.indicator_of_notMem hmem]
    have hcond : ¬ ((∀ j : Fin (n + 1), j < k →
        |subtypeSum k j (fun i ↦ X i.1 ω)| < ε) ∧
        ε ≤ |subtypeSum k k (fun i ↦ X i.1 ω)|) := by
      intro h
      apply hmem
      refine ⟨?_, ?_⟩
      · have h2 := h.2
        rw [hps k le_rfl] at h2
        exact h2
      · intro j hj
        have h1 := h.1 j hj
        rw [hps j hj.le] at h1
        exact h1
    rw [hitOfPast, ite_eq_right hcond]

/-- The future functional reproduces the future sum. -/
private lemma tailOfFuture_eq {Ω : Type*} {n : ℕ} (X : Fin n → Ω → ℝ)
    (k : Fin (n + 1)) (ω : Ω) :
    tailOfFuture k (fun i ↦ X i.1 ω) = ∑ i ∈ futureFinset n k, X i ω := by
  unfold tailOfFuture
  exact Finset.sum_coe_sort (s := futureFinset n k) (f := fun i ↦ X i ω)

/-- On a first-hit set, the squared full sum dominates `ε ^ 2` times the measure. -/
private lemma firstHit_integral_lower {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {n : ℕ} {X : Fin n → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hLp : ∀ i, MemLp (X i) 2 μ) (hind : iIndepFun X μ) {ε : ℝ} (hε : 0 < ε)
    (k : Fin (n + 1)) :
    ε ^ 2 * μ.real (firstHitSet X ε k) ≤
      ∫ ω, (firstHitSet X ε k).indicator
        (fun ω ↦ (partialSum X (Fin.last n) ω) ^ 2) ω ∂μ := by
  let A := firstHitSet X ε k
  have hA : MeasurableSet A := measurableSet_firstHit hX ε k
  let Sk := partialSum X k
  let tail : Ω → ℝ := fun ω ↦ ∑ i ∈ futureFinset n k, X i ω
  have hsplit : ∀ ω, partialSum X (Fin.last n) ω = Sk ω + tail ω :=
    fun ω ↦ partialSum_add_future X k ω
  have hSkLp : MemLp Sk 2 μ := by
    unfold Sk partialSum
    exact memLp_finsetSum (pastFinset n k) fun i _ ↦ hLp i
  have htailLp : MemLp tail 2 μ :=
    memLp_finsetSum (futureFinset n k) fun i _ ↦ hLp i
  have hSkSq : Integrable (fun ω ↦ Sk ω ^ 2) μ := hSkLp.integrable_sq
  have htailSq : Integrable (fun ω ↦ tail ω ^ 2) μ := htailLp.integrable_sq
  have hprod : Integrable (fun ω ↦ Sk ω * tail ω) μ := by
    convert hSkLp.integrable_mul htailLp using 1
  have hInd1 : Integrable (A.indicator fun ω ↦ Sk ω ^ 2) μ := hSkSq.indicator hA
  have hInd2 : Integrable (A.indicator fun ω ↦ Sk ω * tail ω) μ := hprod.indicator hA
  have hInd3 : Integrable (A.indicator fun ω ↦ tail ω ^ 2) μ := htailSq.indicator hA
  have hcross : ∫ ω, A.indicator (fun ω ↦ Sk ω * tail ω) ω ∂μ = 0 := by
    let pastRead : Ω → {i : Fin n // i ∈ pastFinset n k} → ℝ := fun ω i ↦ X i.1 ω
    let futureRead : Ω → {i : Fin n // i ∈ futureFinset n k} → ℝ := fun ω i ↦ X i.1 ω
    have hpastMeas : Measurable pastRead :=
      Measurable.of_eval fun i ↦ hX i.1
    have hfutureMeas : Measurable futureRead :=
      Measurable.of_eval fun i ↦ hX i.1
    have hdisj : Disjoint (pastFinset n k) (futureFinset n k) :=
      (past_future_partition n k).1
    have hindep := (hind.indepFun_finset (pastFinset n k) (futureFinset n k) hdisj hX).comp
      (measurable_hitOfPast k ε) (measurable_tailOfFuture k)
    let Xp : Ω → ℝ := fun ω ↦ hitOfPast k ε (pastRead ω)
    let Yf : Ω → ℝ := fun ω ↦ tailOfFuture k (futureRead ω)
    have hindep' : Xp ⟂ᵢ[μ] Yf := by
      simpa [Xp, Yf, Function.comp_def] using hindep
    have hfac := hindep'.integral_fun_mul_eq_mul_integral
      ((measurable_hitOfPast k ε).comp hpastMeas).aestronglyMeasurable
      ((measurable_tailOfFuture k).comp hfutureMeas).aestronglyMeasurable
    have hpoint : (fun ω ↦ Xp ω * Yf ω) = A.indicator (fun ω ↦ Sk ω * tail ω) := by
      ext ω
      unfold Xp Yf pastRead futureRead Sk tail
      rw [hitOfPast_eq_indicator X k ε ω, tailOfFuture_eq X k ω]
      by_cases hω : ω ∈ A
      · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω]
      · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω]
        ring
    have htail0 : ∫ ω, Yf ω ∂μ = 0 := by
      have hint : ∀ i ∈ futureFinset n k, Integrable (X i) μ := by
        intro i _
        exact memLp_one_iff_integrable.1
          ((hLp i).mono_exponent (by simp : (1 : ℝ≥0∞) ≤ 2))
      rw [show (fun ω ↦ Yf ω) = fun ω ↦ ∑ i ∈ futureFinset n k, X i ω by
        ext ω; exact tailOfFuture_eq X k ω, integral_finsetSum _ hint]
      exact Finset.sum_eq_zero fun i _ ↦ hmean i
    rw [← hpoint, hfac, htail0, mul_zero]
  have hexpand : ∫ ω, A.indicator (fun ω ↦ (partialSum X (Fin.last n) ω) ^ 2) ω ∂μ =
      ∫ ω, A.indicator (fun ω ↦ Sk ω ^ 2) ω ∂μ +
      2 * ∫ ω, A.indicator (fun ω ↦ Sk ω * tail ω) ω ∂μ +
      ∫ ω, A.indicator (fun ω ↦ tail ω ^ 2) ω ∂μ := by
    have hpt : ∀ ω, A.indicator (fun η ↦ (partialSum X (Fin.last n) η) ^ 2) ω =
        A.indicator (fun η ↦ Sk η ^ 2) ω +
        2 * A.indicator (fun η ↦ Sk η * tail η) ω +
        A.indicator (fun η ↦ tail η ^ 2) ω := by
      intro ω
      by_cases hω : ω ∈ A
      · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω, Set.indicator_of_mem hω,
          Set.indicator_of_mem hω, hsplit ω]
        ring
      · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω,
          Set.indicator_of_notMem hω, Set.indicator_of_notMem hω]
        ring
    rw [integral_congr_ae (ae_of_all _ hpt), integral_add, integral_add, integral_const_mul]
    · exact hInd1
    · exact hInd2.const_mul 2
    · exact hInd1.add (hInd2.const_mul 2)
    · exact hInd3
  have hsqLower : ε ^ 2 * μ.real A ≤ ∫ ω, A.indicator (fun ω ↦ Sk ω ^ 2) ω ∂μ := by
    have hpt : ∀ ω, ε ^ 2 * A.indicator (1 : Ω → ℝ) ω ≤
        A.indicator (fun η ↦ Sk η ^ 2) ω := by
      intro ω
      by_cases hω : ω ∈ A
      · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω]
        simp only [Pi.one_apply, mul_one]
        have hsqAbs : |ε| ≤ |partialSum X k ω| := by
          rw [abs_of_pos hε]
          exact hω.1
        simpa [Sk] using sq_le_sq.mpr hsqAbs
      · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω]
        simp
    have hint : Integrable (fun ω ↦ ε ^ 2 * A.indicator (1 : Ω → ℝ) ω) μ :=
      (integrable_const _).indicator hA |>.const_mul _
    rw [← integral_indicator_one hA, ← integral_const_mul]
    exact integral_mono hint hInd1 hpt
  have htailNonneg : 0 ≤ ∫ ω, A.indicator (fun ω ↦ tail ω ^ 2) ω ∂μ :=
    integral_nonneg fun ω ↦ by
      by_cases hω : ω ∈ A
      · simp [Set.indicator_of_mem hω, sq_nonneg]
      · simp [Set.indicator_of_notMem hω]
  linarith [hcross, hexpand, hsqLower, htailNonneg]

/-- Kolmogorov's maximal inequality for a finite independent mean-zero family. -/
private lemma kolmogorov_maximal {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {n : ℕ} {X : Fin n → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hLp : ∀ i, MemLp (X i) 2 μ) (hind : iIndepFun X μ) {ε : ℝ} (hε : 0 < ε) :
    μ {ω | ∃ k : Fin (n + 1), ε ≤ |partialSum X k ω|} ≤
      ENNReal.ofReal ((∫ ω, (partialSum X (Fin.last n) ω) ^ 2 ∂μ) / ε ^ 2) := by
  have hmeas : ∀ k, MeasurableSet (firstHitSet X ε k) := fun k ↦ measurableSet_firstHit hX ε k
  have hSLp : MemLp (partialSum X (Fin.last n)) 2 μ := by
    unfold partialSum
    rw [show pastFinset n (Fin.last n) = Finset.univ by
      ext i; simp [pastFinset, Fin.val_last, i.isLt]]
    exact memLp_finsetSum (Finset.univ : Finset (Fin n)) fun i _ ↦ hLp i
  have hSSq : Integrable (fun ω ↦ (partialSum X (Fin.last n) ω) ^ 2) μ := hSLp.integrable_sq
  have hsumLe : ε ^ 2 * μ.real (⋃ k, firstHitSet X ε k) ≤
      ∫ ω, (partialSum X (Fin.last n) ω) ^ 2 ∂μ := by
    rw [measureReal_iUnion_fintype (pairwise_firstHit X ε) hmeas
      (fun _ ↦ measure_ne_top μ _)]
    rw [Finset.mul_sum]
    have hint : ∑ k, ∫ ω, (firstHitSet X ε k).indicator
        (fun ω ↦ (partialSum X (Fin.last n) ω) ^ 2) ω ∂μ ≤
        ∫ ω, (partialSum X (Fin.last n) ω) ^ 2 ∂μ := by
      rw [← integral_finsetSum]
      · have hpt : ∀ ω, ∑ k, (firstHitSet X ε k).indicator
            (fun η ↦ (partialSum X (Fin.last n) η) ^ 2) ω ≤
            (partialSum X (Fin.last n) ω) ^ 2 := by
          intro ω
          have hdisj := pairwise_firstHit X ε
          by_cases hmem : ω ∈ ⋃ k, firstHitSet X ε k
          · obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hmem
            rw [Finset.sum_eq_single k]
            · rw [Set.indicator_of_mem hk]
            · intro m _ hmk
              have hnot : ω ∉ firstHitSet X ε m :=
                Set.disjoint_left.1 (hdisj hmk.symm) hk
              rw [Set.indicator_of_notMem hnot]
            · intro hknot
              exact (hknot (Finset.mem_univ k)).elim
          · rw [Finset.sum_eq_zero]
            · exact sq_nonneg _
            · intro k _
              have hnot : ω ∉ firstHitSet X ε k := by
                intro hk
                exact hmem (Set.mem_iUnion.2 ⟨k, hk⟩)
              rw [Set.indicator_of_notMem hnot]
        exact integral_mono
          (integrable_finsetSum _ fun k _ ↦ hSSq.indicator (hmeas k)) hSSq hpt
      · intro k _
        exact hSSq.indicator (hmeas k)
    refine le_trans (Finset.sum_le_sum fun k _ ↦ firstHit_integral_lower hX hmean hLp hind hε k)
      hint
  have hreal : μ.real {ω | ∃ k : Fin (n + 1), ε ≤ |partialSum X k ω|} ≤
      (∫ ω, (partialSum X (Fin.last n) ω) ^ 2 ∂μ) / ε ^ 2 := by
    rw [← iUnion_firstHit X ε, le_div_iff₀ (sq_pos_of_pos hε), mul_comm]
    exact hsumLe
  rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
  exact ENNReal.ofReal_le_ofReal hreal

/-- Real Gaussian parameter of one partition increment. -/
private lemma increment_eq_nndist {T : ℝ≥0} (π : TimePartition T) (i : Fin π.size) :
    (nndist (π.node i.succ : ℝ) (π.node i.castSucc : ℝ) : ℝ) = π.increment i := by
  have hle : π.node i.castSucc ≤ π.node i.succ := π.monotone_node (Fin.castSucc_le_succ i)
  have hnonneg : 0 ≤ (π.node i.succ : ℝ) - π.node i.castSucc :=
    sub_nonneg.mpr (NNReal.coe_le_coe.mpr hle)
  calc
    (nndist (π.node i.succ : ℝ) (π.node i.castSucc : ℝ) : ℝ)
        = |(π.node i.succ : ℝ) - π.node i.castSucc| := by
          simp [nndist_eq_nnnorm, Real.norm_eq_abs]
    _ = (π.node i.succ : ℝ) - π.node i.castSucc := abs_of_nonneg hnonneg
    _ = π.increment i := by simp [TimePartition.increment, NNReal.coe_sub hle]

/-- Second moment of a centered Gaussian increment. -/
private lemma integral_sq_increment {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)
    {T : ℝ≥0} (π : TimePartition T) (i : Fin π.size) :
    ∫ ω, (B (π.node i.succ) ω - B (π.node i.castSucc) ω) ^ 2 ∂μ = π.increment i := by
  let raw : Ω → ℝ := fun ω ↦ B (π.node i.succ) ω - B (π.node i.castSucc) ω
  have hlaw : HasLaw raw (gaussianReal 0
      (nndist (π.node i.succ : ℝ) (π.node i.castSucc : ℝ))) μ :=
    hB.hasLaw_sub (π.node i.succ) (π.node i.castSucc)
  have hmean : ∫ ω, raw ω ∂μ = 0 := by
    rw [hlaw.integral_eq, integral_id_gaussianReal]
  have hvar : variance raw μ = π.increment i := by
    rw [hlaw.variance_eq, variance_id_gaussianReal, increment_eq_nndist π i]
  rw [variance_of_integral_eq_zero hlaw.aemeasurable hmean] at hvar
  simpa [raw] using hvar

/-- Fourth moment of the centered standard Gaussian measure, via its moment-generating function. -/
private lemma integral_id_pow_four_gaussianReal (v : ℝ≥0) :
    ∫ x, x ^ 4 ∂gaussianReal 0 v = 3 * (v : ℝ) ^ 2 := by
  let φ : ℝ → ℝ := fun t ↦ Real.exp ((v : ℝ) * t ^ 2 / 2)
  have hφder (t : ℝ) : HasDerivAt φ ((v : ℝ) * t * φ t) t := by
    have hpow : HasDerivAt (fun s ↦ s ^ 2) (2 * t) t := by
      simpa using hasDerivAt_pow 2 t
    have hmul : HasDerivAt (fun s ↦ (v : ℝ) * s ^ 2) ((v : ℝ) * (2 * t)) t :=
      hpow.const_mul (v : ℝ)
    have hdiv : HasDerivAt (fun s ↦ (v : ℝ) * s ^ 2 / 2) ((v : ℝ) * t) t := by
      have h := hmul.div_const 2
      exact h.congr_deriv (by ring)
    exact (hdiv.exp).congr_deriv (by simp [φ, mul_comm])
  have hψder (t : ℝ) : HasDerivAt (fun s ↦ (v : ℝ) * s * φ s)
      (((v : ℝ) + (v : ℝ) ^ 2 * t ^ 2) * φ t) t := by
    exact ((hasDerivAt_id t).const_mul (v : ℝ)).mul (hφder t) |>.congr_deriv
      (by simp only [id_eq]; ring)
  have hρder (t : ℝ) : HasDerivAt (fun s ↦ ((v : ℝ) + (v : ℝ) ^ 2 * s ^ 2) * φ s)
      ((v : ℝ) ^ 2 * t * (3 + (v : ℝ) * t ^ 2) * φ t) t := by
    have hpow : HasDerivAt (fun s ↦ s ^ 2) (2 * t) t := by
      simpa using hasDerivAt_pow 2 t
    have hcoeff : HasDerivAt (fun s ↦ (v : ℝ) + (v : ℝ) ^ 2 * s ^ 2)
        (2 * (v : ℝ) ^ 2 * t) t := by
      exact ((hasDerivAt_const t (v : ℝ)).add (hpow.const_mul ((v : ℝ) ^ 2))).congr_deriv
        (by ring)
    exact (hcoeff.mul (hφder t)).congr_deriv (by ring)
  have hσ : deriv (fun s ↦ (v : ℝ) ^ 2 * s * (3 + (v : ℝ) * s ^ 2) * φ s) 0 =
      3 * (v : ℝ) ^ 2 := by
    have hlin : HasDerivAt (fun s ↦ (v : ℝ) ^ 2 * s) ((v : ℝ) ^ 2) 0 := by
      refine HasDerivAt.congr_deriv (HasDerivAt.congr_of_eventuallyEq
        ((hasDerivAt_id 0).const_mul ((v : ℝ) ^ 2))
        (Eventually.of_forall fun s ↦ by simp [id_eq])) (by simp)
    have hcube : HasDerivAt (fun s : ℝ ↦ s ^ 3) (0 : ℝ) 0 := by
      simpa using hasDerivAt_pow 3 (0 : ℝ)
    have hpoly : HasDerivAt (fun s ↦ 3 * (v : ℝ) ^ 2 * s + (v : ℝ) ^ 3 * s ^ 3)
        (3 * (v : ℝ) ^ 2) 0 := by
      refine (((hlin.const_mul 3).add (hcube.const_mul ((v : ℝ) ^ 3))).congr_deriv
        (by simp [mul_zero, add_zero])).congr_of_eventuallyEq
        (Eventually.of_forall fun s ↦ by simp only [Pi.add_apply]; ring)
    have hpoly' : HasDerivAt (fun s ↦ (v : ℝ) ^ 2 * s * (3 + (v : ℝ) * s ^ 2))
        (3 * (v : ℝ) ^ 2) 0 := by
      convert hpoly using 1
      ext s
      ring
    exact ((hpoly'.mul (hφder 0)).congr_deriv
      (by simp [φ, Real.exp_zero, mul_zero, zero_mul, add_zero, mul_one])).deriv
  calc
    ∫ x, x ^ 4 ∂gaussianReal 0 v
        = iteratedDeriv 4 (mgf (fun x ↦ x) (gaussianReal 0 v)) 0 := by
          rw [iteratedDeriv_mgf_zero (by simp) 4]
          simp
    _ = iteratedDeriv 4 φ 0 := by
          rw [mgf_fun_id_gaussianReal]
          congr 1
          ext t
          simp [φ]
    _ = deriv (deriv (deriv (deriv φ))) 0 := by
          rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ,
            iteratedDeriv_succ, iteratedDeriv_zero]
    _ = 3 * (v : ℝ) ^ 2 := by
          have h1 : deriv φ = fun t ↦ (v : ℝ) * t * φ t := by
            ext t
            exact (hφder t).deriv
          have h2 : deriv (fun t ↦ (v : ℝ) * t * φ t) =
              fun t ↦ ((v : ℝ) + (v : ℝ) ^ 2 * t ^ 2) * φ t := by
            ext t
            exact (hψder t).deriv
          have h3 : deriv (fun t ↦ ((v : ℝ) + (v : ℝ) ^ 2 * t ^ 2) * φ t) =
              fun t ↦ (v : ℝ) ^ 2 * t * (3 + (v : ℝ) * t ^ 2) * φ t := by
            ext t
            exact (hρder t).deriv
          rw [h1, h2, h3, hσ]

/-- Fourth moment of a centered Gaussian increment. -/
private lemma integral_pow_four_increment {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)
    {T : ℝ≥0} (π : TimePartition T) (i : Fin π.size) :
    ∫ ω, (B (π.node i.succ) ω - B (π.node i.castSucc) ω) ^ 4 ∂μ =
      3 * π.increment i ^ 2 := by
  let v : ℝ≥0 := nndist (π.node i.succ : ℝ) (π.node i.castSucc : ℝ)
  let raw : Ω → ℝ := fun ω ↦ B (π.node i.succ) ω - B (π.node i.castSucc) ω
  have hlaw : HasLaw raw (gaussianReal 0 v) μ := hB.hasLaw_sub _ _
  have hint := hlaw.integral_comp (f := fun x : ℝ ↦ x ^ 4)
    ((continuous_pow 4).aestronglyMeasurable)
  rw [Function.comp_def] at hint
  have hv : (v : ℝ) = π.increment i := increment_eq_nndist π i
  calc
    ∫ ω, raw ω ^ 4 ∂μ = ∫ x, x ^ 4 ∂gaussianReal 0 v := hint
    _ = 3 * (v : ℝ) ^ 2 := integral_id_pow_four_gaussianReal v
    _ = 3 * π.increment i ^ 2 := by rw [hv]

/-- Energy of the centered squared increments is at most twice mesh times `T`. -/
private lemma centeredIncrement_energy_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)
    {T : ℝ≥0} (π : TimePartition T) (Y : Fin π.size → Ω → ℝ)
    (hYmeas : ∀ i, Measurable (Y i))
    (hYae : ∀ i, (fun ω ↦ B (π.node i.succ) ω - B (π.node i.castSucc) ω) =ᵐ[μ] Y i)
    (hYindep : iIndepFun Y μ) :
    ∫ ω, (∑ i : Fin π.size, ((Y i ω) ^ 2 - π.increment i)) ^ 2 ∂μ ≤
      2 * (π.mesh : ℝ) * (T : ℝ) := by
  let X : Fin π.size → Ω → ℝ := fun i ω ↦ (Y i ω) ^ 2 - π.increment i
  have hsq (i : Fin π.size) : ∫ ω, (Y i ω) ^ 2 ∂μ = π.increment i := by
    have hpow : (fun ω ↦ (B (π.node i.succ) ω - B (π.node i.castSucc) ω) ^ 2) =ᵐ[μ]
        fun ω ↦ (Y i ω) ^ 2 := (hYae i).mono fun ω h ↦ by simp [h]
    rw [← integral_congr_ae hpow]
    exact integral_sq_increment hB π i
  have hfour (i : Fin π.size) : ∫ ω, (Y i ω) ^ 4 ∂μ = 3 * π.increment i ^ 2 := by
    have hpow : (fun ω ↦ (B (π.node i.succ) ω - B (π.node i.castSucc) ω) ^ 4) =ᵐ[μ]
        fun ω ↦ (Y i ω) ^ 4 := (hYae i).mono fun ω h ↦ by simp [h]
    rw [← integral_congr_ae hpow]
    exact integral_pow_four_increment hB π i
  have hYLp4 (i : Fin π.size) : MemLp (Y i) 4 μ := by
    let raw : Ω → ℝ := fun ω ↦ B (π.node i.succ) ω - B (π.node i.castSucc) ω
    have hlaw : HasLaw raw (gaussianReal 0
        (nndist (π.node i.succ : ℝ) (π.node i.castSucc : ℝ))) μ :=
      hB.hasLaw_sub _ _
    have hraw : MemLp raw 4 μ :=
      hlaw.memLp (memLp_id_gaussianReal' 4 (by simp))
    exact hraw.ae_eq (hYae i)
  have hsqLp (i : Fin π.size) : MemLp (fun ω ↦ Y i ω ^ 2) 2 μ := by
    rw [memLp_two_iff_integrable_sq ((hYmeas i).pow_const 2).aestronglyMeasurable]
    convert (hYLp4 i).integrable_norm_pow (by decide : (4 : ℕ) ≠ 0) using 1
    ext x
    rw [Real.norm_eq_abs]
    have hinner : Y i x ^ 2 = |Y i x| ^ 2 := (sq_abs (Y i x)).symm
    rw [hinner, ← pow_mul]
  have hmeanX (i : Fin π.size) : ∫ ω, X i ω ∂μ = 0 := by
    have hint : Integrable (fun ω ↦ Y i ω ^ 2) μ :=
      memLp_one_iff_integrable.1 ((hsqLp i).mono_exponent (by simp : (1 : ℝ≥0∞) ≤ 2))
    rw [show X i = fun ω ↦ Y i ω ^ 2 - π.increment i by rfl,
      integral_sub hint (integrable_const _), hsq i, integral_const, probReal_univ]
    simp
  have hvar (i : Fin π.size) : ∫ ω, (X i ω) ^ 2 ∂μ = 2 * π.increment i ^ 2 := by
    have hAE : AEStronglyMeasurable (fun ω ↦ Y i ω ^ 2) μ :=
      ((hYmeas i).pow_const 2).aestronglyMeasurable
    have hsub : variance (X i) μ = variance (fun ω ↦ Y i ω ^ 2) μ := by
      simpa [X, sub_eq_add_neg] using variance_sub_const hAE (π.increment i)
    have heq : variance (fun ω ↦ Y i ω ^ 2) μ =
        ∫ ω, (Y i ω ^ 2) ^ 2 ∂μ - (∫ ω, Y i ω ^ 2 ∂μ) ^ 2 :=
      variance_eq_sub (hsqLp i)
    have hpow4 : ∫ ω, (Y i ω ^ 2) ^ 2 ∂μ = ∫ ω, (Y i ω) ^ 4 ∂μ := by
      refine integral_congr_ae (ae_of_all _ fun ω ↦ ?_)
      ring
    have hXvar : variance (X i) μ = ∫ ω, (X i ω) ^ 2 ∂μ :=
      variance_of_integral_eq_zero ((hYmeas i).pow_const 2 |>.sub measurable_const).aemeasurable
        (hmeanX i)
    rw [← hXvar, hsub, heq, hpow4, hsq i, hfour i]
    ring
  have hXLp (i : Fin π.size) : MemLp (X i) 2 μ := (hsqLp i).sub (memLp_const _)
  have hXindep : iIndepFun X μ := by
    have hcomp := hYindep.comp (fun i x ↦ x ^ 2 - π.increment i)
      (fun i ↦ (measurable_id.pow_const 2).sub measurable_const)
    simpa [X, Function.comp_def] using hcomp
  have hvarSum : variance (fun ω ↦ ∑ i : Fin π.size, X i ω) μ =
      ∑ i : Fin π.size, variance (X i) μ := by
    have hpi := IndepFun.variance_sum (s := (Finset.univ : Finset (Fin π.size)))
      (fun i _ ↦ hXLp i) (fun i _ j _ hij ↦ hXindep.indepFun hij)
    have hcongr : (fun ω ↦ ∑ i : Fin π.size, X i ω) =ᵐ[μ]
        ∑ i ∈ Finset.univ, X i :=
      ae_of_all _ fun ω ↦ (Finset.sum_apply _ _ _).symm
    rw [variance_congr hcongr]
    simpa using hpi
  have hmeanSum : ∫ ω, (∑ i : Fin π.size, X i ω) ∂μ = 0 := by
    rw [integral_finsetSum]
    · simp [hmeanX]
    · intro i _
      exact memLp_one_iff_integrable.1
        ((hXLp i).mono_exponent (by simp : (1 : ℝ≥0∞) ≤ 2))
  have henergy : ∫ ω, (∑ i : Fin π.size, X i ω) ^ 2 ∂μ =
      ∑ i : Fin π.size, 2 * π.increment i ^ 2 := by
    have hvarFun : variance (fun ω ↦ ∑ i : Fin π.size, X i ω) μ =
        ∫ ω, (∑ i : Fin π.size, X i ω) ^ 2 ∂μ :=
      variance_of_integral_eq_zero
        (measurable_finset_sum fun i _ ↦
          ((hYmeas i).pow_const 2).sub measurable_const).aemeasurable hmeanSum
    have hvarI (i : Fin π.size) : variance (X i) μ = ∫ ω, (X i ω) ^ 2 ∂μ :=
      variance_of_integral_eq_zero
        (((hYmeas i).pow_const 2).sub measurable_const).aemeasurable (hmeanX i)
    rw [← hvarFun, hvarSum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [hvarI i, hvar i]
  rw [henergy]
  calc
    ∑ i : Fin π.size, 2 * π.increment i ^ 2
        = 2 * ∑ i : Fin π.size, π.increment i ^ 2 := by rw [Finset.mul_sum]
    _ ≤ 2 * ((π.mesh : ℝ) * (T : ℝ)) := by
      gcongr
      exact π.sum_sq_increment_le
    _ = 2 * (π.mesh : ℝ) * (T : ℝ) := by ring

/-- One-partition bound for the nonstrict quadratic-variation deviation. -/
private lemma quadraticVariation_measure_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)
    {T : ℝ≥0} (π : TimePartition T) {ε : ℝ} (hε : 0 < ε)
    (hmesh : (π.mesh : ℝ) < ε / 2) :
    μ {ω | ∃ t ≤ T, ε ≤ |π.covariation B B t ω - (t : ℝ)|} ≤
      ENNReal.ofReal (8 * (π.mesh : ℝ) * (T : ℝ) / ε ^ 2) := by
  let raw : Fin π.size → Ω → ℝ :=
    fun i ω ↦ B (π.node i.succ) ω - B (π.node i.castSucc) ω
  let hAe : ∀ i, AEMeasurable (raw i) μ :=
    fun i ↦ (hB.aemeasurable (π.node i.succ)).sub (hB.aemeasurable (π.node i.castSucc))
  let Y : Fin π.size → Ω → ℝ := fun i ↦ (hAe i).mk (raw i)
  have hYmeas : ∀ i, Measurable (Y i) := fun i ↦ (hAe i).measurable_mk
  have hYae : ∀ i, raw i =ᵐ[μ] Y i := fun i ↦ (hAe i).ae_eq_mk
  have hYindep : iIndepFun Y μ :=
    (iIndepFun_congr hYae).1 (hB.hasIndepIncrements π.size π.node π.monotone_node)
  let X : Fin π.size → Ω → ℝ := fun i ω ↦ (Y i ω) ^ 2 - π.increment i
  have hXmeas : ∀ i, Measurable (X i) :=
    fun i ↦ ((hYmeas i).pow_const 2).sub measurable_const
  have hXmean : ∀ i, ∫ ω, X i ω ∂μ = 0 := by
    intro i
    have hsq : ∫ ω, (Y i ω) ^ 2 ∂μ = π.increment i := by
      have hpow : (fun ω ↦ (raw i ω) ^ 2) =ᵐ[μ] fun ω ↦ (Y i ω) ^ 2 :=
        (hYae i).mono fun ω hω ↦ congrArg (fun z ↦ z ^ 2) hω
      rw [← integral_congr_ae hpow]
      unfold raw
      exact integral_sq_increment hB π i
    have hLpY : MemLp (Y i) 4 μ := by
      have hlaw := hB.hasLaw_sub (π.node i.succ) (π.node i.castSucc)
      exact (hlaw.memLp (memLp_id_gaussianReal' 4 (by simp))).ae_eq (hYae i)
    have hsqLp : MemLp (fun ω ↦ Y i ω ^ 2) 2 μ := by
      rw [memLp_two_iff_integrable_sq ((hYmeas i).pow_const 2).aestronglyMeasurable]
      convert hLpY.integrable_norm_pow (by decide : (4 : ℕ) ≠ 0) using 1
      ext x
      rw [Real.norm_eq_abs]
      have hinner : Y i x ^ 2 = |Y i x| ^ 2 := (sq_abs (Y i x)).symm
      rw [hinner, ← pow_mul]
    have hint : Integrable (fun ω ↦ Y i ω ^ 2) μ :=
      memLp_one_iff_integrable.1 (hsqLp.mono_exponent (by simp : (1 : ℝ≥0∞) ≤ 2))
    rw [show X i = fun ω ↦ Y i ω ^ 2 - π.increment i by rfl,
      integral_sub hint (integrable_const _), hsq, integral_const, probReal_univ]
    simp
  have hXLp : ∀ i, MemLp (X i) 2 μ := by
    intro i
    have hLpY : MemLp (Y i) 4 μ := by
      have hlaw := hB.hasLaw_sub (π.node i.succ) (π.node i.castSucc)
      exact (hlaw.memLp (memLp_id_gaussianReal' 4 (by simp))).ae_eq (hYae i)
    have hsqLp : MemLp (fun ω ↦ Y i ω ^ 2) 2 μ := by
      rw [memLp_two_iff_integrable_sq ((hYmeas i).pow_const 2).aestronglyMeasurable]
      convert hLpY.integrable_norm_pow (by decide : (4 : ℕ) ≠ 0) using 1
      ext x
      rw [Real.norm_eq_abs]
      have hinner : Y i x ^ 2 = |Y i x| ^ 2 := (sq_abs (Y i x)).symm
      rw [hinner, ← pow_mul]
    exact hsqLp.sub (memLp_const _)
  have hXindep : iIndepFun X μ := by
    have hcomp := hYindep.comp (fun i x ↦ x ^ 2 - π.increment i)
      (fun _ ↦ (measurable_id.pow_const 2).sub measurable_const)
    simpa [X, Function.comp_def] using hcomp
  have hkol := kolmogorov_maximal hXmeas hXmean hXLp hXindep (half_pos hε)
  have henergy := centeredIncrement_energy_le hB π Y hYmeas hYae hYindep
  have hlast : ∀ ω, partialSum X (Fin.last π.size) ω =
      ∑ i : Fin π.size, X i ω := partialSum_last X
  have hintLe : ∫ ω, (partialSum X (Fin.last π.size) ω) ^ 2 ∂μ ≤
      2 * (π.mesh : ℝ) * (T : ℝ) := by
    have hfun : (fun ω ↦ (partialSum X (Fin.last π.size) ω) ^ 2) =
        fun ω ↦ (∑ i : Fin π.size, ((Y i ω) ^ 2 - π.increment i)) ^ 2 := by
      ext ω
      rw [hlast ω]
    rw [hfun]
    exact henergy
  have hdiv : (∫ ω, (partialSum X (Fin.last π.size) ω) ^ 2 ∂μ) / (ε / 2) ^ 2 ≤
      8 * (π.mesh : ℝ) * (T : ℝ) / ε ^ 2 := by
    have hrewrite : 2 * (π.mesh : ℝ) * (T : ℝ) / (ε / 2) ^ 2 =
        8 * (π.mesh : ℝ) * (T : ℝ) / ε ^ 2 := by
      field_simp
      ring
    exact (div_le_div_of_nonneg_right hintLe (sq_nonneg _)).trans (le_of_eq hrewrite)
  let N : Set Ω := ⋃ i, {ω | Y i ω ≠ raw i ω}
  have hN : μ N = 0 := by
    refine (measure_iUnion_null_iff).2 fun i ↦ ?_
    exact ae_iff.1 (hYae i).symm
  have hsub : {ω | ∃ t ≤ T, ε ≤ |π.covariation B B t ω - (t : ℝ)|} ⊆
      {ω | ∃ k : Fin (π.size + 1), ε / 2 ≤ |partialSum X k ω|} ∪ N := by
    intro ω hω
    by_cases hωN : ω ∈ N
    · exact Or.inr hωN
    · refine Or.inl ?_
      obtain ⟨t, ht, hdev⟩ := hω
      let k : Fin (π.size + 1) :=
        ⟨π.completedCount t, Nat.lt_succ_of_le (π.completedCount_le_size t)⟩
      refine ⟨k, ?_⟩
      have hagree : ∀ i, Y i ω = raw i ω := by
        intro i
        by_contra hne
        exact hωN (Set.mem_iUnion.2 ⟨i, hne⟩)
      have hQ : π.covariation B B t ω = ∑ i ∈ pastFinset π.size k, (Y i ω) ^ 2 := by
        have hfilt : Finset.univ.filter (fun i : Fin π.size ↦ π.node i.succ ≤ t) =
            pastFinset π.size k := by
          ext i
          simp only [pastFinset, Finset.mem_filter, Finset.mem_univ, true_and]
          have hkval : k.val = π.completedCount t := by simp [k]
          rw [hkval]
          exact π.completed_iff_val_lt t i
        unfold TimePartition.covariation
        rw [← Finset.sum_filter, hfilt]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        have hrw : B (π.node i.succ) ω - B (π.node i.castSucc) ω = Y i ω := by
          have hraw := (hagree i).symm
          unfold raw at hraw
          exact hraw
        rw [hrw]
        ring
      have hpartial : partialSum X k ω =
          π.covariation B B t ω - (π.covered t : ℝ) := by
        rw [partialSum, Finset.sum_sub_distrib, hQ]
        have hsumΔ : ∑ i ∈ pastFinset π.size k, π.increment i = (π.covered t : ℝ) := by
          have hidx : (⟨k.val, k.isLt⟩ : Fin (π.size + 1)) = k := by ext; simp
          simpa [pastFinset, hidx, TimePartition.covered] using
            π.sum_increment_initial k.val (π.completedCount_le_size t)
        linarith
      have htri : |π.covariation B B t ω - (t : ℝ)| ≤
          |partialSum X k ω| + |(π.covered t : ℝ) - (t : ℝ)| := by
        have hEq : π.covariation B B t ω - (t : ℝ) =
            partialSum X k ω + ((π.covered t : ℝ) - (t : ℝ)) := by
          linarith [hpartial]
        rw [hEq]
        exact abs_add_le _ _
      have hgap : |(π.covered t : ℝ) - (t : ℝ)| < ε / 2 :=
        lt_of_le_of_lt (by simpa [abs_sub_comm] using π.abs_t_sub_covered_le_mesh ht) hmesh
      have hgt : ε / 2 < |partialSum X k ω| := by linarith [htri, hdev, hgap, hε]
      exact hgt.le
  calc
    μ {ω | ∃ t ≤ T, ε ≤ |π.covariation B B t ω - (t : ℝ)|}
        ≤ μ ({ω | ∃ k : Fin (π.size + 1), ε / 2 ≤ |partialSum X k ω|} ∪ N) :=
          measure_mono hsub
    _ ≤ μ {ω | ∃ k : Fin (π.size + 1), ε / 2 ≤ |partialSum X k ω|} + μ N :=
          measure_union_le _ _
    _ ≤ ENNReal.ofReal ((∫ ω, (partialSum X (Fin.last π.size) ω) ^ 2 ∂μ) / (ε / 2) ^ 2) + 0 := by
          rw [hN, add_zero, add_zero]
          exact hkol
    _ ≤ ENNReal.ofReal (8 * (π.mesh : ℝ) * (T : ℝ) / ε ^ 2) := by
          rw [add_zero]
          exact ENNReal.ofReal_le_ofReal hdiv

/-- **08.7**: uniform-on-compact convergence in probability along deterministic vanishing mesh.
No path continuity assumption is needed for completed-interval quadratic sums. -/
theorem brownian_quadraticVariation_ucp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B μ) {T : ℝ≥0} (π : ℕ → TimePartition T)
    (hmesh : Tendsto (fun n ↦ (π n).mesh) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n ↦ μ {ω | ∃ t ≤ T,
      ε < |(π n).covariation B B t ω - (t : ℝ)|}) atTop (𝓝 0) := by
  intro ε hε
  have hmeshR : Tendsto (fun n ↦ ((π n).mesh : ℝ)) atTop (𝓝 0) := NNReal.tendsto_coe.mpr hmesh
  have hev : ∀ᶠ n in atTop, ((π n).mesh : ℝ) < ε / 2 :=
    hmeshR.eventually (Iio_mem_nhds (half_pos hε))
  have hupper : Tendsto (fun n ↦ ENNReal.ofReal
      (8 * ((π n).mesh : ℝ) * (T : ℝ) / ε ^ 2)) atTop (𝓝 0) := by
    have hlin : Tendsto (fun n ↦ 8 * ((π n).mesh : ℝ) * (T : ℝ) / ε ^ 2) atTop (𝓝 0) := by
      have hrewrite : (fun n ↦ 8 * ((π n).mesh : ℝ) * (T : ℝ) / ε ^ 2) =
          fun n ↦ (8 * (T : ℝ) / ε ^ 2) * ((π n).mesh : ℝ) := by
        ext n
        ring
      rw [hrewrite]
      simpa using hmeshR.const_mul (8 * (T : ℝ) / ε ^ 2)
    simpa [Function.comp_def, ENNReal.ofReal_zero] using
      (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp hlin
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
    (Eventually.of_forall fun _ ↦ bot_le) ?_
  filter_upwards [hev] with n hn
  calc
    μ {ω | ∃ t ≤ T, ε < |(π n).covariation B B t ω - (t : ℝ)|}
        ≤ μ {ω | ∃ t ≤ T, ε ≤ |(π n).covariation B B t ω - (t : ℝ)|} := by
          apply measure_mono
          intro ω ⟨t, ht, hlt⟩
          exact ⟨t, ht, hlt.le⟩
    _ ≤ ENNReal.ofReal (8 * ((π n).mesh : ℝ) * (T : ℝ) / ε ^ 2) :=
          quadraticVariation_measure_le hB (π n) hε hn

/-- Summable meshes give almost sure uniform convergence, hence in particular dyadic convergence. -/
theorem brownian_quadraticVariation_ae {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B μ) {T : ℝ≥0} (π : ℕ → TimePartition T)
    (hmesh : Summable (fun n ↦ ((π n).mesh : ℝ))) :
    ∀ᵐ ω ∂μ, ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      ∀ t ≤ T, |(π n).covariation B B t ω - (t : ℝ)| < ε := by
  have hone : ∀ ε : ℝ, 0 < ε → ∀ᵐ ω ∂μ, ∀ᶠ n in atTop,
      ∀ t ≤ T, |(π n).covariation B B t ω - (t : ℝ)| < ε := by
    intro ε hε
    let bad : ℕ → Set Ω := fun n ↦
      {ω | ∃ t ≤ T, ε ≤ |(π n).covariation B B t ω - (t : ℝ)|}
    let bump : ℕ → ℝ≥0∞ := fun n ↦ if ((π n).mesh : ℝ) < ε / 2 then 0 else 1
    have hle : ∀ n, μ (bad n) ≤
        ENNReal.ofReal (8 * ((π n).mesh : ℝ) * (T : ℝ) / ε ^ 2) + bump n := by
      intro n
      by_cases hn : ((π n).mesh : ℝ) < ε / 2
      · simpa [bad, bump, hn] using quadraticVariation_measure_le hB (π n) hε hn
      · have hprob : μ (bad n) ≤ 1 := by
          calc
            μ (bad n) ≤ μ Set.univ := measure_mono (Set.subset_univ _)
            _ = 1 := measure_univ
        have hnonneg : 0 ≤ ENNReal.ofReal (8 * ((π n).mesh : ℝ) * (T : ℝ) / ε ^ 2) :=
          bot_le
        simpa [bump, hn] using le_trans hprob (by simp)
    have hofReal : ∑' n, ENNReal.ofReal (8 * ((π n).mesh : ℝ) * (T : ℝ) / ε ^ 2) ≠ ∞ := by
      refine Summable.tsum_ofReal_ne_top ?_
      have hrewrite : (fun n ↦ 8 * ((π n).mesh : ℝ) * (T : ℝ) / ε ^ 2) =
          fun n ↦ (8 * (T : ℝ) / ε ^ 2) * ((π n).mesh : ℝ) := by
        ext n
        ring
      rw [hrewrite]
      exact hmesh.mul_left _
    have hzero : Tendsto (fun n ↦ ((π n).mesh : ℝ)) atTop (𝓝 0) := hmesh.tendsto_atTop_zero
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hzero.eventually (Iio_mem_nhds (half_pos hε)))
    have htail : ∑' i, bump (i + N) = 0 := by
      rw [ENNReal.tsum_eq_zero]
      intro i
      simp [bump, hN (i + N) (Nat.le_add_left N i)]
    have heq := Summable.sum_add_tsum_nat_add' (f := bump) (k := N)
      (ENNReal.summable (f := fun i ↦ bump (i + N)))
    have hsumLe : ∑ i ∈ Finset.range N, bump i ≤ N := by
      calc
        ∑ i ∈ Finset.range N, bump i ≤ ∑ i ∈ Finset.range N, (1 : ℝ≥0∞) := by
          gcongr with i hi
          simp only [bump]
          split_ifs <;> simp
        _ = N := by simp
    have hbump : ∑' n, bump n ≠ ∞ := by
      rw [← heq, htail, add_zero]
      exact ne_top_of_le_ne_top (by simp) hsumLe
    have htsum : ∑' n, μ (bad n) ≠ ∞ := by
      refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hle)
      rw [ENNReal.tsum_add]
      exact ENNReal.add_ne_top.2 ⟨hofReal, hbump⟩
    filter_upwards [ae_eventually_notMem htsum] with ω hω
    exact hω.mono fun n hn t ht ↦ by
      have hnot : ¬ ε ≤ |(π n).covariation B B t ω - (t : ℝ)| := by
        intro hle'
        exact hn ⟨t, ht, hle'⟩
      exact lt_of_not_ge hnot
  filter_upwards [ae_all_iff.2 fun m : ℕ ↦
      hone (1 / ((m : ℝ) + 1)) (by positivity)] with ω hω
  intro ε hε
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
  exact (hω m).mono fun n hn t ht ↦ lt_trans (hn t ht) hm

/-- Algebraic polarization identity for one pair of increments. -/
private lemma sq_sub_sq_div_sqrt_two (a b : ℝ) :
    ((a + b) / Real.sqrt 2) * ((a + b) / Real.sqrt 2) -
      ((a - b) / Real.sqrt 2) * ((a - b) / Real.sqrt 2) = 2 * (a * b) := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by positivity)
  field_simp [Real.sqrt_ne_zero'.mpr two_pos]
  rw [h2]
  ring

/-- Polarization expresses bilinear covariation through two quadratic variations. -/
private lemma covariation_polarization {Ω : Type*} {T : ℝ≥0} (π : TimePartition T)
    (B C : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) :
    π.covariation (fun s ω ↦ (B s ω + C s ω) / Real.sqrt 2)
        (fun s ω ↦ (B s ω + C s ω) / Real.sqrt 2) t ω -
      π.covariation (fun s ω ↦ (B s ω - C s ω) / Real.sqrt 2)
        (fun s ω ↦ (B s ω - C s ω) / Real.sqrt 2) t ω =
      2 * π.covariation B C t ω := by
  unfold TimePartition.covariation
  rw [← Finset.sum_sub_distrib]
  refine Eq.trans (Finset.sum_congr rfl fun i _ ↦ ?_) (Finset.mul_sum _ _ _).symm
  by_cases h : π.node i.succ ≤ t
  · simp only [h, ↓reduceIte]
    set u : ℝ := B (π.node i.succ) ω
    set v : ℝ := B (π.node i.castSucc) ω
    set p : ℝ := C (π.node i.succ) ω
    set q : ℝ := C (π.node i.castSucc) ω
    have hL : (u + p) / Real.sqrt 2 - (v + q) / Real.sqrt 2 =
        ((u - v) + (p - q)) / Real.sqrt 2 := by ring
    have hR : (u - p) / Real.sqrt 2 - (v - q) / Real.sqrt 2 =
        ((u - v) - (p - q)) / Real.sqrt 2 := by ring
    rw [hL, hR]
    exact sq_sub_sq_div_sqrt_two (u - v) (p - q)
  · simp [h]

/-- A normalized sum of independent pre-Brownian motions is pre-Brownian. -/
private lemma isPreBrownianReal_normalizedSum {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {B C : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B μ) (hC : IsPreBrownianReal C μ)
    (hind : IndepFun (fun ω ↦ fun t ↦ B t ω) (fun ω ↦ fun t ↦ C t ω) μ) :
    IsPreBrownianReal (fun t ω ↦ (B t ω + C t ω) / Real.sqrt 2) μ := by
  refine IsGaussianProcess.isPreBrownianReal_of_covariance ?_ ?_ ?_
  · refine ⟨fun I ↦ ?_⟩
    have hm : Measurable (fun f : ℝ≥0 → ℝ ↦ I.restrict f) :=
      Measurable.of_eval fun i ↦ measurable_pi_apply (i : ℝ≥0)
    have hindI : IndepFun (fun ω ↦ I.restrict (fun t ↦ B t ω))
        (fun ω ↦ I.restrict (fun t ↦ C t ω)) μ := hind.comp hm hm
    have hpair := hindI.hasGaussianLaw (hB.isGaussianProcess.hasGaussianLaw I)
      (hC.isGaussianProcess.hasGaussianLaw I)
    have hsmul := hpair.fun_add.fun_smul (Real.sqrt 2)⁻¹
    convert hsmul using 1
    ext ω i
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, Finset.restrict, div_eq_mul_inv]
    ring
  · intro t
    have hint : Integrable (fun ω ↦ B t ω + C t ω) μ :=
      (hB.integrable_eval t).add (hC.integrable_eval t)
    rw [show (fun ω ↦ (B t ω + C t ω) / Real.sqrt 2) =
        fun ω ↦ (Real.sqrt 2)⁻¹ * (B t ω + C t ω) by ext; ring,
      integral_const_mul, integral_add (hB.integrable_eval t) (hC.integrable_eval t),
      hB.integral_eval, hC.integral_eval]
    simp
  · intro s t hst
    have hBs : MemLp (B s) 2 μ := (hB.isGaussianProcess.hasGaussianLaw_eval s).memLp_two
    have hBt : MemLp (B t) 2 μ := (hB.isGaussianProcess.hasGaussianLaw_eval t).memLp_two
    have hCs : MemLp (C s) 2 μ := (hC.isGaussianProcess.hasGaussianLaw_eval s).memLp_two
    have hCt : MemLp (C t) 2 μ := (hC.isGaussianProcess.hasGaussianLaw_eval t).memLp_two
    have hcross : cov[B s, C t; μ] = 0 :=
      (hind.comp (measurable_pi_apply s) (measurable_pi_apply t)).covariance_eq_zero hBs hCt
    have hcross' : cov[C s, B t; μ] = 0 := by
      rw [covariance_comm]
      exact (hind.comp (measurable_pi_apply t) (measurable_pi_apply s)).covariance_eq_zero hBt hCs
    have hsum : cov[fun ω ↦ B s ω + C s ω, fun ω ↦ B t ω + C t ω; μ] =
        (s : ℝ) + s := by
      have hLs : (fun ω ↦ B s ω + C s ω) = B s + C s := by
        ext ω
        rfl
      have hLt : (fun ω ↦ B t ω + C t ω) = B t + C t := by
        ext ω
        rfl
      rw [hLs, hLt, covariance_add_left hBs hCs (hBt.add hCt),
        covariance_add_right hBs hBt hCt, covariance_add_right hCs hBt hCt,
        hB.covariance_eval, hC.covariance_eval, hcross, hcross']
      simp [min_eq_left hst]
    have hfun : (fun ω ↦ (B s ω + C s ω) / Real.sqrt 2) =
        fun ω ↦ (Real.sqrt 2)⁻¹ * (B s ω + C s ω) := by
      ext ω
      ring
    have hfun' : (fun ω ↦ (B t ω + C t ω) / Real.sqrt 2) =
        fun ω ↦ (Real.sqrt 2)⁻¹ * (B t ω + C t ω) := by
      ext ω
      ring
    rw [hfun, hfun', covariance_const_mul_left, covariance_const_mul_right, hsum]
    have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by positivity)
    field_simp [Real.sqrt_ne_zero'.mpr two_pos]
    rw [hsq]
    ring

/-- Independent Brownian coordinates have diagonal quadratic covariation.
Independence is imposed on the coordinate processes as random elements, rather than only
on pairs of one-time marginals. -/
theorem brownian_covariation_ucp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ} (B : Fin d → ℝ≥0 → Ω → ℝ)
    (hB : ∀ i, IsPreBrownianReal (B i) μ)
    (hind : iIndepFun (fun i ω ↦ fun t ↦ B i t ω) μ)
    {T : ℝ≥0} (π : ℕ → TimePartition T)
    (hmesh : Tendsto (fun n ↦ (π n).mesh) atTop (𝓝 0)) (i j : Fin d) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n ↦ μ {ω | ∃ t ≤ T,
      ε < |(π n).covariation (B i) (B j) t ω - if i = j then (t : ℝ) else 0|})
      atTop (𝓝 0) := by
  intro ε hε
  by_cases hij : i = j
  · subst hij
    simpa using brownian_quadraticVariation_ucp μ (hB i) π hmesh ε hε
  · let P : ℝ≥0 → Ω → ℝ := fun t ω ↦ (B i t ω + B j t ω) / Real.sqrt 2
    let M : ℝ≥0 → Ω → ℝ := fun t ω ↦ (B i t ω - B j t ω) / Real.sqrt 2
    have hP : IsPreBrownianReal P μ :=
      isPreBrownianReal_normalizedSum (hB i) (hB j) (hind.indepFun hij)
    have hM : IsPreBrownianReal M μ := by
      have hneg : IsPreBrownianReal (-B j) μ := (hB j).neg
      have hnegMeas : Measurable (fun f : ℝ≥0 → ℝ ↦ -f) :=
        Measurable.of_eval fun t ↦ measurable_neg.comp (measurable_pi_apply t)
      have hindneg := (hind.indepFun hij).comp measurable_id hnegMeas
      have hsum := isPreBrownianReal_normalizedSum (hB i) hneg hindneg
      refine IsPreBrownianReal.congr hsum fun t ↦ ae_of_all μ fun ω ↦ ?_
      simp [M, Pi.neg_apply, sub_eq_add_neg]
    have htendP := brownian_quadraticVariation_ucp μ hP π hmesh ε hε
    have htendM := brownian_quadraticVariation_ucp μ hM π hmesh ε hε
    have hupper : Tendsto
        (fun n ↦ μ {ω | ∃ t ≤ T, ε < |(π n).covariation P P t ω - (t : ℝ)|} +
          μ {ω | ∃ t ≤ T, ε < |(π n).covariation M M t ω - (t : ℝ)|})
        atTop (𝓝 0) := by
      rw [show (0 : ℝ≥0∞) = 0 + 0 by simp]
      exact htendP.add htendM
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
      (Eventually.of_forall fun _ ↦ bot_le) ?_
    refine Eventually.of_forall fun n ↦ ?_
    refine le_trans (measure_mono ?_) (measure_union_le _ _)
    intro ω ⟨t, ht, hdev⟩
    have hpol := covariation_polarization (π n) (B i) (B j) t ω
    have hbound : |(π n).covariation (B i) (B j) t ω| ≤
        (|(π n).covariation P P t ω - (t : ℝ)| +
          |(π n).covariation M M t ω - (t : ℝ)|) / 2 := by
      have hEq : (π n).covariation (B i) (B j) t ω =
          (((π n).covariation P P t ω - (t : ℝ)) -
            ((π n).covariation M M t ω - (t : ℝ))) / 2 := by
        linarith [hpol]
      rw [hEq, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      gcongr
      exact abs_sub _ _
    have hsum : ε < (|(π n).covariation P P t ω - (t : ℝ)| +
        |(π n).covariation M M t ω - (t : ℝ)|) / 2 := by
      have hdev0 : ε < |(π n).covariation (B i) (B j) t ω| := by
        rw [ite_eq_right hij, sub_zero] at hdev
        exact hdev
      exact lt_of_lt_of_le hdev0 hbound
    by_cases hp : ε < |(π n).covariation P P t ω - (t : ℝ)|
    · exact Or.inl ⟨t, ht, hp⟩
    · refine Or.inr ⟨t, ht, ?_⟩
      have hle : |(π n).covariation P P t ω - (t : ℝ)| ≤ ε := le_of_not_gt hp
      linarith

end CKMA
