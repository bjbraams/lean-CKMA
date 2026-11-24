/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Fintype.Basic

import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Deterministic time partitions for quadratic variation

`TimePartition` records ordered deterministic nodes on `[0, T]`, allowing repeated nodes and
the zero time interval. Its mesh controls completed-interval quadratic and bilinear covariation
sums.

## Main definitions

* `CKMA.TimePartition`: finite deterministic partition of `[0, T]`.
* `CKMA.TimePartition.mesh`: largest time increment of a partition.
* `CKMA.TimePartition.covariation`: quadratic covariation sum over completed partition intervals.
* `CKMA.TimePartition.completedCount`: number of partition intervals completed by time `t`.
* `CKMA.TimePartition.covered`: right endpoint of the last interval completed by time `t`.
* `CKMA.TimePartition.increment`: real length of one partition increment.
* `CKMA.TimePartition.uniform`: the uniform partition of `[0, T]` into `n + 1` intervals.

## Main results

* `CKMA.TimePartition.sum_increment`: partition increments sum to `T`.
* `CKMA.TimePartition.abs_sub_covered_le_mesh`: distance from `t` to the last completed node is
  at most the mesh.
* `CKMA.TimePartition.mesh_uniform_le`: the uniform partition has mesh at most `T / (n + 1)`.
-/

public section

noncomputable section

namespace CKMA

open scoped NNReal BigOperators

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
@[expose]
def TimePartition.mesh {T : ℝ≥0} (π : TimePartition T) : ℝ≥0 :=
  Finset.univ.sup fun i : Fin π.size ↦ π.node i.succ - π.node i.castSucc

/-- Quadratic covariation using completed partition intervals up to time `t`.
It is constant between adjacent nodes, as in the argument of `GAPS_EASY.md`. -/
@[expose]
def TimePartition.covariation {Ω : Type*} {T : ℝ≥0} (π : TimePartition T)
    (B C : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∑ i : Fin π.size, if π.node i.succ ≤ t then
    (B (π.node i.succ) ω - B (π.node i.castSucc) ω) *
    (C (π.node i.succ) ω - C (π.node i.castSucc) ω) else 0

namespace TimePartition

variable {T : ℝ≥0} (π : TimePartition T)

/-- Number of partition intervals completed by time `t`. -/
@[expose]
def completedCount (t : ℝ≥0) : ℕ :=
  (Finset.univ.filter fun i : Fin π.size ↦ π.node i.succ ≤ t).card

/-- The completed-count index is at most the number of increments. -/
lemma completedCount_le_size (t : ℝ≥0) : π.completedCount t ≤ π.size := by
  simpa only [completedCount, Finset.card_univ, Fintype.card_fin] using
    Finset.card_filter_le (Finset.univ : Finset (Fin π.size))
      fun i : Fin π.size ↦ π.node i.succ ≤ t

/-- Right endpoint of the last interval completed by time `t`. -/
@[expose]
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
@[expose]
def increment (i : Fin π.size) : ℝ :=
  ((π.node i.succ - π.node i.castSucc : ℝ≥0) : ℝ)

/-- A real increment is the difference of consecutive real nodes. -/
lemma increment_eq_sub (i : Fin π.size) :
    π.increment i = (π.node i.succ : ℝ) - π.node i.castSucc := by
  rw [increment, NNReal.coe_sub (π.monotone_node (Fin.castSucc_le_succ i))]

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

/-- On `[0,T]`, time differs from the covered node by at most the mesh. -/
lemma abs_sub_covered_le_mesh {t : ℝ≥0} (ht : t ≤ T) :
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

/-- The uniform partition of `[0,T]` into `n + 1` intervals of length `T / (n + 1)`. -/
@[expose]
def uniform (T : ℝ≥0) (n : ℕ) : TimePartition T where
  size := n + 1
  node k := T * (k.val : ℝ≥0) / ((n : ℝ≥0) + 1)
  monotone_node a b hab := by
    dsimp only
    gcongr
    exact_mod_cast hab
  node_zero := by simp
  node_last := by
    simp only [Fin.val_last, Nat.cast_add, Nat.cast_one]
    rw [mul_div_assoc, div_self (by positivity), mul_one]

/-- The uniform partition of `[0, T]` has `n + 1` intervals. -/
@[simp]
lemma uniform_size (T : ℝ≥0) (n : ℕ) : (uniform T n).size = n + 1 := rfl

/-- Node `k` of the uniform partition is `T * k / (n + 1)`. -/
@[simp]
lemma uniform_node (T : ℝ≥0) (n : ℕ) (k : Fin ((uniform T n).size + 1)) :
    (uniform T n).node k = T * (k.val : ℝ≥0) / ((n : ℝ≥0) + 1) := rfl

/-- The mesh of the uniform partition is at most `T / (n + 1)`. -/
lemma mesh_uniform_le (T : ℝ≥0) (n : ℕ) : (uniform T n).mesh ≤ T / ((n : ℝ≥0) + 1) := by
  refine Finset.sup_le fun i _ ↦ tsub_le_iff_right.2 (le_of_eq ?_)
  simp only [uniform_node, Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]
  rw [← add_div]
  congr 1
  ring

@[deprecated (since := "2026-11-15")] alias abs_t_sub_covered_le_mesh := abs_sub_covered_le_mesh

end TimePartition

end CKMA
