/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.RoughPath.Sewing.Construction
public import Mathlib.Basic.ENNReal.Real
public import Mathlib.Basic.ENNReal.Operations
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Analysis.PSeries
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Order.Compact
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Young–Loeve estimate for finite variation

Partition sums of a Young increment are controlled by `p`- and `q`-variation.
Superadditivity of the control `ω(s,t) = V_p(X;s,t)^{1/p} V_q(Y;s,t)^{1/q}` is
recorded through every second node. Deletion, reflection, and continuity of
finite variation are in `VariationEstimate`.
-/

@[expose] public section

noncomputable section

namespace CKMA

open scoped BigOperators NNReal ENNReal
open Finset Filter Topology Metric

/-- The `p`th power variation, retaining infinite variation. -/
def pathVariationPower {E : Type*} [SeminormedAddCommGroup E]
    (p : ℝ) (X : ℝ → E) (a b : ℝ) : ℝ≥0∞ :=
  ⨆ π : OrderedIntervalPartition a b, ∑ i : Fin π.size,
    ENNReal.ofReal (‖X (π.node i.succ) - X (π.node i.castSucc)‖ ^ p)

namespace YoungLoeve

variable {E : Type*} [SeminormedAddCommGroup E]

/-- Sum of `p`th powers of increments along one ordered partition. -/
def variationSum (p : ℝ) (X : ℝ → E) {a b : ℝ}
    (π : OrderedIntervalPartition a b) : ℝ≥0∞ :=
  ∑ i : Fin π.size, ENNReal.ofReal (‖X (π.node i.succ) - X (π.node i.castSucc)‖ ^ p)

lemma pathVariationPower_eq_iSup (p : ℝ) (X : ℝ → E) (a b : ℝ) :
    pathVariationPower p X a b = ⨆ π : OrderedIntervalPartition a b, variationSum p X π := rfl

/-- Real `p`-variation power on a subinterval, or zero when the power is infinite. -/
def variationReal (p : ℝ) (X : ℝ → E) (s t : ℝ) : ℝ :=
  (pathVariationPower p X s t).toReal

/-- The one-point partition of a degenerate interval. -/
def pointPartition (s : ℝ) : OrderedIntervalPartition s s where
  size := 0
  node := fun _ => s
  monotone_node := fun _ _ _ => le_rfl
  node_zero := rfl
  node_last := rfl

/-- Two endpoints, in order. -/
def segmentPartition {s t : ℝ} (hst : s ≤ t) : OrderedIntervalPartition s t where
  size := 1
  node := fun i => if i.val = 0 then s else t
  monotone_node := by
    intro i j hij
    by_cases hi : i.val = 0
    · by_cases hj : j.val = 0
      · simp [hi, hj]
      · simp [hi, hj, hst]
    · have hi1 : i.val = 1 := by
        have : i.val < 2 := i.isLt
        omega
      have hj1 : j.val = 1 := by
        have hle : 1 ≤ j.val := by simpa [hi1] using Fin.le_iff_val_le_val.mp hij
        have : j.val < 2 := j.isLt
        omega
      simp [hi1, hj1]
  node_zero := by simp
  node_last := by
    show (if (Fin.last 1 : Fin 2).val = 0 then s else t) = t
    simp

lemma variationSum_point (p : ℝ) (X : ℝ → E) (s : ℝ) :
    variationSum p X (pointPartition s) = 0 := by
  unfold variationSum pointPartition
  simp [Finset.univ_eq_empty]

lemma pathVariationPower_point {p : ℝ} (hp : 0 < p) (X : ℝ → E) (s : ℝ) :
    pathVariationPower p X s s = 0 := by
  rw [pathVariationPower_eq_iSup]
  apply le_antisymm
  · refine iSup_le fun π => ?_
    have hnode : ∀ i, π.node i = s := by
      intro i
      have h0 := π.monotone_node (Fin.zero_le i)
      have h1 := π.monotone_node (Fin.le_last i)
      simp only [π.node_zero, π.node_last] at h0 h1
      exact le_antisymm h1 h0
    unfold variationSum
    refine le_of_eq (Finset.sum_eq_zero fun i _ => ?_)
    have hL : π.node i.castSucc = s := hnode _
    have hR : π.node i.succ = s := hnode _
    simp [hL, hR, Real.zero_rpow (ne_of_gt hp)]
  · rw [← variationSum_point p X s]
    exact le_iSup (variationSum p X) (pointPartition s)

lemma variationReal_point {p : ℝ} (hp : 0 < p) (X : ℝ → E) (s : ℝ) :
    variationReal p X s s = 0 := by
  simp [variationReal, pathVariationPower_point hp]

/-- Reading an ordered partition as a monotone sequence on `ℕ`. -/
def nodeSeq {a b : ℝ} (π : OrderedIntervalPartition a b) (i : ℕ) : ℝ :=
  π.node ⟨min i π.size, by omega⟩

lemma nodeSeq_of_le {a b : ℝ} (π : OrderedIntervalPartition a b) {i : ℕ} (hi : i ≤ π.size) :
    nodeSeq π i = π.node ⟨i, by omega⟩ := by
  simp [nodeSeq, hi]

lemma nodeSeq_zero {a b : ℝ} (π : OrderedIntervalPartition a b) : nodeSeq π 0 = a := by
  simp [nodeSeq_of_le π (Nat.zero_le _), π.node_zero]

lemma nodeSeq_size {a b : ℝ} (π : OrderedIntervalPartition a b) : nodeSeq π π.size = b := by
  rw [nodeSeq_of_le π le_rfl]
  have hlast : (⟨π.size, by omega⟩ : Fin (π.size + 1)) = Fin.last π.size := by
    ext
    simp [Fin.val_last]
  rw [hlast, π.node_last]

lemma monotone_nodeSeq {a b : ℝ} (π : OrderedIntervalPartition a b) : Monotone (nodeSeq π) := by
  intro i j hij
  unfold nodeSeq
  apply π.monotone_node
  rw [Fin.le_iff_val_le_val, Fin.val_mk, Fin.val_mk]
  rcases Nat.lt_or_ge π.size j with hj | hj
  · simp [Nat.min_eq_right (le_of_lt hj)]
  · have hi : i ≤ π.size := le_trans hij hj
    simp [Nat.min_eq_left hi, Nat.min_eq_left hj, hij]

/-- Sum of a two-parameter increment along the first `n` steps of a sequence. -/
def stepSum {F : Type*} [AddCommMonoid F] (A : ℝ → ℝ → F) (c : ℕ → ℝ) (n : ℕ) : F :=
  ∑ i ∈ range n, A (c i) (c (i + 1))

lemma variationSum_eq_stepSum (p : ℝ) (X : ℝ → E) {a b : ℝ}
    (π : OrderedIntervalPartition a b) :
    variationSum p X π =
      ∑ i ∈ range π.size,
        ENNReal.ofReal (‖X (nodeSeq π (i + 1)) - X (nodeSeq π i)‖ ^ p) := by
  unfold variationSum
  have hterm : ∀ i : Fin π.size,
      ENNReal.ofReal (‖X (π.node i.succ) - X (π.node i.castSucc)‖ ^ p) =
        ENNReal.ofReal (‖X (nodeSeq π (i + 1)) - X (nodeSeq π i)‖ ^ p) := by
    intro i
    have hi : i.val ≤ π.size := le_of_lt i.isLt
    have hi1 : i.val + 1 ≤ π.size := Nat.succ_le_of_lt i.isLt
    have hs : i.succ = ⟨i.val + 1, by omega⟩ := by ext; simp [Fin.val_succ]
    have hc : i.castSucc = ⟨i.val, by omega⟩ := by ext; simp [Fin.val_castSucc]
    simp [hs, hc, nodeSeq_of_le, hi, hi1]
  rw [Finset.sum_congr rfl fun i _ => hterm i]
  exact Fin.sum_univ_eq_sum_range
    (fun i => ENNReal.ofReal (‖X (nodeSeq π (i + 1)) - X (nodeSeq π i)‖ ^ p)) π.size

/-- Least index at which a sequence exceeds a threshold. -/
lemma exists_least_index_gt (n : ℕ) (c : ℕ → ℝ) (t : ℝ) (h : ∃ i ≤ n, t < c i) :
    ∃ i ≤ n, t < c i ∧ ∀ j < i, c j ≤ t := by
  induction n generalizing c with
  | zero =>
    obtain ⟨i, hi, hlt⟩ := h
    have hi0 : i = 0 := Nat.le_zero.mp hi
    subst hi0
    exact ⟨0, le_rfl, hlt, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | succ n ih =>
    by_cases h0 : t < c 0
    · exact ⟨0, Nat.zero_le _, h0, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
    · have htail : ∃ i ≤ n, t < c (i + 1) := by
        obtain ⟨i, hi, hlt⟩ := h
        have hi0 : 0 < i := by
          have hne : i ≠ 0 := fun hz => h0 (by simpa [hz] using hlt)
          omega
        exact ⟨i - 1, by omega, by simpa [Nat.sub_add_cancel hi0] using hlt⟩
      obtain ⟨i, hi, hlt, hmin⟩ := ih (fun i => c (i + 1)) htail
      refine ⟨i + 1, by omega, hlt, ?_⟩
      intro j hj
      cases j with
      | zero => exact not_lt.mp h0
      | succ j =>
        exact hmin j (by omega)

/-- Join two ordered partitions at a common endpoint. -/
def concatPart {s u t : ℝ} (π₁ : OrderedIntervalPartition s u)
    (π₂ : OrderedIntervalPartition u t) : OrderedIntervalPartition s t where
  size := π₁.size + π₂.size
  node := fun i =>
    if h : (i : ℕ) ≤ π₁.size then nodeSeq π₁ i else nodeSeq π₂ (i - π₁.size)
  monotone_node := by
    intro i j hij
    by_cases hi : (i : ℕ) ≤ π₁.size
    · by_cases hj : (j : ℕ) ≤ π₁.size
      · simpa [hi, hj] using monotone_nodeSeq π₁ (Fin.le_iff_val_le_val.mp hij)
      · have hiu : nodeSeq π₁ i ≤ u := by
          simpa [nodeSeq_size] using monotone_nodeSeq π₁ hi
        have hju : u ≤ nodeSeq π₂ (j - π₁.size) := by
          simpa [nodeSeq_zero] using monotone_nodeSeq π₂ (Nat.zero_le _)
        simpa [hi, hj] using hiu.trans hju
    · have hj : ¬ (j : ℕ) ≤ π₁.size := fun hj' => hi (le_trans (Fin.le_iff_val_le_val.mp hij) hj')
      have hsub : i - π₁.size ≤ j - π₁.size := by
        have hij' := Fin.le_iff_val_le_val.mp hij
        omega
      simpa [hi, hj] using monotone_nodeSeq π₂ hsub
  node_zero := by simp [nodeSeq_zero]
  node_last := by
    by_cases h : π₁.size + π₂.size ≤ π₁.size
    · have h2 : π₂.size = 0 := by omega
      have hlast0 : Fin.last π₂.size = (0 : Fin (π₂.size + 1)) := by
        ext
        simp [Fin.val_last, h2]
      have hut : u = t := by
        rw [← π₂.node_zero, ← hlast0]
        exact π₂.node_last
      have hidx : π₁.size + π₂.size = π₁.size := by omega
      simp [hidx, nodeSeq_size, hut]
    · have hidx : (π₁.size + π₂.size) - π₁.size = π₂.size := by omega
      simp [h, hidx, nodeSeq_size]

lemma variationSum_concat {s u t : ℝ} (p : ℝ) (X : ℝ → E)
    (π₁ : OrderedIntervalPartition s u) (π₂ : OrderedIntervalPartition u t) :
    variationSum p X (concatPart π₁ π₂) = variationSum p X π₁ + variationSum p X π₂ := by
  rw [variationSum_eq_stepSum, variationSum_eq_stepSum, variationSum_eq_stepSum]
  have hsize : (concatPart π₁ π₂).size = π₁.size + π₂.size := rfl
  rw [hsize]
  have hsum := sum_range_add
    (fun i => ENNReal.ofReal (‖X (nodeSeq (concatPart π₁ π₂) (i + 1)) -
      X (nodeSeq (concatPart π₁ π₂) i)‖ ^ p)) π₁.size π₂.size
  rw [hsum]
  have hnode : ∀ {k : ℕ} (hk : k ≤ π₁.size + π₂.size),
      (concatPart π₁ π₂).node ⟨k, by omega⟩ =
        if k ≤ π₁.size then nodeSeq π₁ k else nodeSeq π₂ (k - π₁.size) := by
    intro k hk
    simp [concatPart]
  have hleft : ∀ i ∈ range π₁.size,
      nodeSeq (concatPart π₁ π₂) i = nodeSeq π₁ i ∧
      nodeSeq (concatPart π₁ π₂) (i + 1) = nodeSeq π₁ (i + 1) := by
    intro i hi
    have hi' : i < π₁.size := mem_range.mp hi
    have hi1 : i + 1 ≤ π₁.size := Nat.succ_le_of_lt hi'
    constructor
    · rw [nodeSeq_of_le _ (by omega : i ≤ (concatPart π₁ π₂).size), hnode (by omega)]
      simp [nodeSeq_of_le, hi'.le]
    · rw [nodeSeq_of_le _ (by omega : i + 1 ≤ (concatPart π₁ π₂).size), hnode (by omega)]
      simp [hi1, nodeSeq_of_le]
  have hright : ∀ i ∈ range π₂.size,
      nodeSeq (concatPart π₁ π₂) (π₁.size + i) = nodeSeq π₂ i ∧
      nodeSeq (concatPart π₁ π₂) (π₁.size + i + 1) = nodeSeq π₂ (i + 1) := by
    intro i hi
    have hi' : i < π₂.size := mem_range.mp hi
    have hnot1 : ¬ π₁.size + i + 1 ≤ π₁.size := by omega
    constructor
    · by_cases hi0 : i = 0
      · subst hi0
        simp only [add_zero]
        rw [nodeSeq_of_le _ (by omega : π₁.size ≤ (concatPart π₁ π₂).size), hnode (by omega)]
        simp [nodeSeq_size, nodeSeq_zero]
      · have hnot : ¬ π₁.size + i ≤ π₁.size := by omega
        rw [nodeSeq_of_le _ (by omega : π₁.size + i ≤ (concatPart π₁ π₂).size), hnode (by omega)]
        simp [hnot, show π₁.size + i - π₁.size = i by omega, nodeSeq_of_le, hi'.le]
    · rw [nodeSeq_of_le _ (by omega : π₁.size + i + 1 ≤ (concatPart π₁ π₂).size), hnode (by omega)]
      simp [hnot1, show π₁.size + i + 1 - π₁.size = i + 1 by omega, nodeSeq_of_le,
        Nat.succ_le_of_lt hi']
  refine congrArg₂ HAdd.hAdd ?_ ?_
  · refine sum_congr rfl fun i hi => ?_
    rcases hleft i hi with ⟨hl, hr⟩
    simp [hl, hr]
  · refine sum_congr rfl fun i hi => ?_
    rcases hright i hi with ⟨hl, hr⟩
    simp [hl, hr]

/-- Enlarging the interval does not decrease `p`-variation. -/
lemma pathVariationPower_mono {a b c d : ℝ} (hca : c ≤ a) (hbd : b ≤ d)
    (p : ℝ) (X : ℝ → E) :
    pathVariationPower p X a b ≤ pathVariationPower p X c d := by
  refine iSup_le fun π => ?_
  let πc : OrderedIntervalPartition c a := segmentPartition hca
  let πd : OrderedIntervalPartition b d := segmentPartition hbd
  have hsum : variationSum p X π ≤ variationSum p X (concatPart πc (concatPart π πd)) := by
    rw [variationSum_concat, variationSum_concat]
    calc
      variationSum p X π = 0 + variationSum p X π + 0 := by simp
      _ ≤ variationSum p X πc + variationSum p X π + variationSum p X πd := by
        refine add_le_add (add_le_add ?_ le_rfl) ?_
        · exact (zero_le : (0 : ℝ≥0∞) ≤ variationSum p X πc)
        · exact (zero_le : (0 : ℝ≥0∞) ≤ variationSum p X πd)
      _ = variationSum p X πc + (variationSum p X π + variationSum p X πd) := by
        simp [add_assoc]
  exact hsum.trans (le_iSup (variationSum p X) _)

/-- Superadditivity of `p`-variation power. -/
lemma pathVariationPower_superadd {s u t : ℝ} (hsu : s ≤ u) (hut : u ≤ t) (p : ℝ) (X : ℝ → E) :
    pathVariationPower p X s u + pathVariationPower p X u t ≤ pathVariationPower p X s t := by
  have _ : Nonempty (OrderedIntervalPartition s u) := ⟨segmentPartition hsu⟩
  have _ : Nonempty (OrderedIntervalPartition u t) := ⟨segmentPartition hut⟩
  rw [pathVariationPower_eq_iSup, pathVariationPower_eq_iSup, pathVariationPower_eq_iSup]
  refine ENNReal.iSup_add_iSup_le fun π₁ π₂ => ?_
  rw [← variationSum_concat p X π₁ π₂]
  exact le_iSup (variationSum p X) (concatPart π₁ π₂)

lemma oneStep_le {s t : ℝ} (hst : s ≤ t) (p : ℝ) (X : ℝ → E) :
    ENNReal.ofReal (‖X t - X s‖ ^ p) ≤ pathVariationPower p X s t := by
  rw [pathVariationPower_eq_iSup]
  refine le_iSup_of_le (segmentPartition hst) ?_
  unfold variationSum segmentPartition
  rw [Fin.sum_univ_one]
  simp

lemma variationReal_mono {a b c d : ℝ} (hca : c ≤ a) (hab : a ≤ b) (hbd : b ≤ d)
    {p : ℝ} {X : ℝ → E} (hfin : pathVariationPower p X c d ≠ ∞) :
    variationReal p X a b ≤ variationReal p X c d := by
  have _ := hab
  exact ENNReal.toReal_mono hfin (pathVariationPower_mono hca hbd p X)

lemma variationReal_superadd {s u t : ℝ} (hsu : s ≤ u) (hut : u ≤ t) {p : ℝ} {X : ℝ → E}
    (hfin : pathVariationPower p X s t ≠ ∞) :
    variationReal p X s u + variationReal p X u t ≤ variationReal p X s t := by
  have hsu' : pathVariationPower p X s u ≠ ∞ :=
    ne_top_of_le_ne_top hfin (pathVariationPower_mono (le_refl s) hut p X)
  have hut' : pathVariationPower p X u t ≠ ∞ :=
    ne_top_of_le_ne_top hfin (pathVariationPower_mono hsu (le_refl t) p X)
  rw [variationReal, variationReal, variationReal, ← ENNReal.toReal_add hsu' hut']
  exact ENNReal.toReal_mono hfin (pathVariationPower_superadd hsu hut p X)

lemma norm_increment_le {s t : ℝ} (hst : s ≤ t) {p : ℝ} {X : ℝ → E}
    (hfin : pathVariationPower p X s t ≠ ∞) :
    ‖X t - X s‖ ^ p ≤ variationReal p X s t := by
  have h := oneStep_le hst p X
  exact (ENNReal.ofReal_le_iff_le_toReal hfin).mp h

/-- A near-maximising partition for a finite variation power. -/
lemma exists_variationSum_gt {s t : ℝ} {p : ℝ} {X : ℝ → E}
    (hfin : pathVariationPower p X s t ≠ ∞) {r : ℝ}
    (hr : r < variationReal p X s t) (hr0 : 0 ≤ r) :
    ∃ π : OrderedIntervalPartition s t, r < (variationSum p X π).toReal := by
  have hlt : ENNReal.ofReal r < pathVariationPower p X s t :=
    (ENNReal.ofReal_lt_iff_lt_toReal hr0 hfin).mpr hr
  rw [pathVariationPower_eq_iSup, lt_iSup_iff] at hlt
  obtain ⟨π, hπ⟩ := hlt
  have hπfin : variationSum p X π ≠ ∞ := ne_top_of_le_ne_top hfin (le_iSup _ π)
  exact ⟨π, (ENNReal.ofReal_lt_iff_lt_toReal hr0 hπfin).mp hπ⟩

lemma norm_le_variationReal {s t : ℝ} (hst : s ≤ t) {p : ℝ} {X : ℝ → E}
    (hp : 0 < p) (hfin : pathVariationPower p X s t ≠ ∞) :
    ‖X t - X s‖ ≤ variationReal p X s t ^ p⁻¹ := by
  have hpow := norm_increment_le hst hfin
  have hbase : 0 ≤ ‖X t - X s‖ ^ p := Real.rpow_nonneg (norm_nonneg _) _
  have h := Real.rpow_le_rpow hbase hpow (inv_nonneg.mpr hp.le)
  simpa [Real.rpow_rpow_inv (norm_nonneg _) (ne_of_gt hp)] using h

/-- Weighted splitting of a product of powers, the superadditivity step for controls. -/
lemma young_split_le {α β x₁ x₂ y₁ y₂ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hαβ : α + β = 1)
    (hx₁ : 0 ≤ x₁) (hx₂ : 0 ≤ x₂) (hy₁ : 0 ≤ y₁) (hy₂ : 0 ≤ y₂) :
    x₁ ^ α * y₁ ^ β + x₂ ^ α * y₂ ^ β ≤ (x₁ + x₂) ^ α * (y₁ + y₂) ^ β := by
  have hx : 0 ≤ x₁ + x₂ := add_nonneg hx₁ hx₂
  have hy : 0 ≤ y₁ + y₂ := add_nonneg hy₁ hy₂
  rcases hx.eq_or_lt with hx0 | hsx
  · have hx₁0 : x₁ = 0 := by linarith
    have hx₂0 : x₂ = 0 := by linarith
    rw [hx₁0, hx₂0, zero_add, Real.zero_rpow (ne_of_gt hα), zero_mul, zero_mul, add_zero]
    simp only [zero_mul]
    exact le_rfl
  · rcases hy.eq_or_lt with hy0 | hsy
    · have hy₁0 : y₁ = 0 := by linarith
      have hy₂0 : y₂ = 0 := by linarith
      rw [hy₁0, hy₂0, zero_add, Real.zero_rpow (ne_of_gt hβ), mul_zero, mul_zero, add_zero]
      simp only [mul_zero]
      exact le_rfl
    · let sx := x₁ + x₂
      let sy := y₁ + y₂
      have hg1 := Real.geom_mean_le_arith_mean2_weighted hα.le hβ.le
        (div_nonneg hx₁ hsx.le) (div_nonneg hy₁ hsy.le) hαβ
      have hg2 := Real.geom_mean_le_arith_mean2_weighted hα.le hβ.le
        (div_nonneg hx₂ hsx.le) (div_nonneg hy₂ hsy.le) hαβ
      have hgeom : (x₁ / sx) ^ α * (y₁ / sy) ^ β + (x₂ / sx) ^ α * (y₂ / sy) ^ β ≤ 1 := by
        have hadd := add_le_add hg1 hg2
        have hre : α * (x₁ / sx) + β * (y₁ / sy) + (α * (x₂ / sx) + β * (y₂ / sy)) =
            α * ((x₁ + x₂) / sx) + β * ((y₁ + y₂) / sy) := by ring
        rw [hre] at hadd
        simpa [sx, sy, div_self hsx.ne', div_self hsy.ne', mul_one, hαβ] using hadd
      have hden : 0 < sx ^ α * sy ^ β :=
        mul_pos (Real.rpow_pos_of_pos hsx α) (Real.rpow_pos_of_pos hsy β)
      have hquot₁ : (x₁ / sx) ^ α * (y₁ / sy) ^ β =
          (x₁ ^ α * y₁ ^ β) / (sx ^ α * sy ^ β) := by
        rw [Real.div_rpow hx₁ hsx.le, Real.div_rpow hy₁ hsy.le, div_mul_div_comm]
      have hquot₂ : (x₂ / sx) ^ α * (y₂ / sy) ^ β =
          (x₂ ^ α * y₂ ^ β) / (sx ^ α * sy ^ β) := by
        rw [Real.div_rpow hx₂ hsx.le, Real.div_rpow hy₂ hsy.le, div_mul_div_comm]
      have hfrac : (x₁ ^ α * y₁ ^ β + x₂ ^ α * y₂ ^ β) / (sx ^ α * sy ^ β) ≤ 1 := by
        rw [add_div]
        simpa [hquot₁, hquot₂] using hgeom
      exact (div_le_one hden).mp hfrac

/-- Delete interior index `j` from a node sequence. -/
def dropNode (c : ℕ → ℝ) (j : ℕ) : ℕ → ℝ :=
  fun i => if i < j then c i else c (i + 1)

lemma dropNode_of_lt (c : ℕ → ℝ) {i j : ℕ} (hi : i < j) : dropNode c j i = c i := by
  simp [dropNode, hi]

lemma dropNode_of_ge (c : ℕ → ℝ) {i j : ℕ} (hi : j ≤ i) : dropNode c j i = c (i + 1) := by
  simp [dropNode, hi]

lemma monotone_dropNode {c : ℕ → ℝ} (hc : Monotone c) (j : ℕ) : Monotone (dropNode c j) := by
  intro i k hik
  by_cases hi : i < j
  · by_cases hk : k < j
    · simpa [dropNode, hi, hk] using hc hik
    · simpa [dropNode, hi, hk] using hc (show i ≤ k + 1 by omega)
  · have hk : ¬ k < j := fun hk => hi (lt_of_le_of_lt hik hk)
    simpa [dropNode, hi, hk] using hc (show i + 1 ≤ k + 1 by omega)

/-- Erasing an interior node replaces two increments by the step across them. -/
lemma stepSum_drop {F : Type*} [AddCommGroup F] (A : ℝ → ℝ → F) (c : ℕ → ℝ)
    {n j : ℕ} (hj0 : 0 < j) (hjn : j < n) :
    stepSum A c n = stepSum A (dropNode c j) (n - 1) +
      (A (c (j - 1)) (c j) + A (c j) (c (j + 1)) - A (c (j - 1)) (c (j + 1))) := by
  set d := dropNode c j
  unfold stepSum
  have hlen : (j - 1) + (n - (j - 1)) = n := by omega
  have hlen' : (j - 1) + (n - j) = n - 1 := by omega
  have hsplit : n - (j - 1) = 2 + (n - (j + 1)) := by omega
  have hsplit' : n - j = 1 + (n - (j + 1)) := by omega
  have hold := sum_range_add (fun i => A (c i) (c (i + 1))) (j - 1) (n - (j - 1))
  rw [hlen] at hold
  rw [hsplit, sum_range_add] at hold
  have hnew := sum_range_add (fun i => A (d i) (d (i + 1))) (j - 1) (n - j)
  rw [hlen'] at hnew
  rw [hsplit', sum_range_add] at hnew
  have hjj : j - 1 + 1 = j := by omega
  have htwo : ∑ k ∈ range 2, A (c (j - 1 + k)) (c (j - 1 + k + 1)) =
      A (c (j - 1)) (c j) + A (c j) (c (j + 1)) := by
    rw [sum_range_succ, sum_range_one]
    simp only [Nat.add_zero, hjj]
  have hone : ∑ k ∈ range 1, A (d (j - 1 + k)) (d (j - 1 + k + 1)) =
      A (c (j - 1)) (c (j + 1)) := by
    rw [sum_range_one]
    simp only [Nat.add_zero, hjj, d, dropNode_of_lt c (show j - 1 < j by omega),
      dropNode_of_ge c le_rfl]
  have hleft : ∑ i ∈ range (j - 1), A (c i) (c (i + 1)) =
      ∑ i ∈ range (j - 1), A (d i) (d (i + 1)) := by
    refine sum_congr rfl fun i hi => ?_
    have hi' : i < j - 1 := mem_range.mp hi
    simp [d, dropNode_of_lt c (show i < j by omega), dropNode_of_lt c (show i + 1 < j by omega)]
  have htail : ∑ i ∈ range (n - (j + 1)),
      A (c (j - 1 + (2 + i))) (c (j - 1 + (2 + i) + 1)) =
      ∑ i ∈ range (n - (j + 1)),
        A (d (j - 1 + (1 + i))) (d (j - 1 + (1 + i) + 1)) := by
    refine sum_congr rfl fun i hi => ?_
    have hidx : j - 1 + (2 + i) = j + 1 + i := by omega
    have hidx' : j - 1 + (1 + i) = j + i := by omega
    have hge : j ≤ j + i := by omega
    have hge1 : j ≤ j + i + 1 := by omega
    have hL : j + 1 + i = j + i + 1 := by omega
    simp [hidx, hidx', hL, d, dropNode_of_ge c hge, dropNode_of_ge c hge1]
  rw [hold, hnew, htwo, hone, hleft, htail]
  abel

/-- Partial sums of the point-removal series `(2 / k) ^ θ`. -/
def youngPartial (θ : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ range n, (2 / ((k + 1) : ℝ)) ^ θ

/-- Sum of the point-removal series, finite for `θ > 1`. -/
def youngLoose (θ : ℝ) : ℝ :=
  ∑' k : ℕ, (2 / ((k + 1) : ℝ)) ^ θ

lemma youngPartial_succ (θ : ℝ) (n : ℕ) :
    youngPartial θ (n + 1) = youngPartial θ n + (2 / ((n + 1) : ℝ)) ^ θ := by
  unfold youngPartial
  rw [sum_range_succ]

lemma youngPartial_pos_term (θ : ℝ) (k : ℕ) : 0 ≤ (2 / ((k : ℝ) + 1)) ^ θ := by
  have hk : (0 : ℝ) ≤ (k : ℝ) + 1 := add_nonneg (Nat.cast_nonneg k) zero_le_one
  exact Real.rpow_nonneg (div_nonneg (by norm_num : (0 : ℝ) ≤ 2) hk) θ

lemma summable_youngLoose {θ : ℝ} (hθ : 1 < θ) :
    Summable (fun k : ℕ => (2 / ((k : ℝ) + 1)) ^ θ) := by
  have hs : Summable (fun n : ℕ => 1 / (n : ℝ) ^ θ) :=
    (Real.summable_one_div_nat_rpow).mpr hθ
  have htail : Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ θ) := by
    have hcomp := hs.comp_injective Nat.succ_injective
    refine hcomp.congr fun k => ?_
    rw [Function.comp_apply, Nat.cast_succ]
  refine (htail.mul_left ((2 : ℝ) ^ θ)).congr fun k => ?_
  have hk : (0 : ℝ) ≤ (k : ℝ) + 1 := add_nonneg (Nat.cast_nonneg k) zero_le_one
  rw [Real.div_rpow (by norm_num : (0 : ℝ) ≤ 2) hk, one_div, div_eq_mul_inv]

lemma youngPartial_le_loose {θ : ℝ} (hθ : 1 < θ) (n : ℕ) :
    youngPartial θ n ≤ youngLoose θ := by
  have hsum := summable_youngLoose hθ
  simpa [youngPartial, youngLoose] using
    hsum.sum_le_tsum (range n) fun k _ => youngPartial_pos_term θ k

lemma youngPartial_step {θ : ℝ} {n : ℕ} (hn : 0 < n) :
    youngPartial θ n = youngPartial θ (n - 1) + (2 / (n : ℝ)) ^ θ := by
  have hn1 : (n - 1) + 1 = n := Nat.sub_add_cancel hn
  have hcast : (↑(n - 1) : ℝ) + 1 = (n : ℝ) := by
    calc
      (↑(n - 1) : ℝ) + 1 = (↑(n - 1) : ℝ) + ↑(1 : ℕ) := by rw [← Nat.cast_one (R := ℝ)]
      _ = ↑(n - 1 + 1) := by rw [← Nat.cast_add]
      _ = (n : ℝ) := by rw [hn1]
  calc
    youngPartial θ n = youngPartial θ ((n - 1) + 1) := by rw [hn1]
    _ = youngPartial θ (n - 1) + (2 / (↑(n - 1) + 1)) ^ θ :=
      youngPartial_succ θ (n - 1)
    _ = youngPartial θ (n - 1) + (2 / (n : ℝ)) ^ θ := by rw [hcast]

/-- Sum of positive terms exceeds the constant on a nonempty index set. -/
lemma sum_gt_card_mul {s : Finset ℕ} {f : ℕ → ℝ} {c : ℝ} (hf : ∀ i ∈ s, c < f i)
    (hne : s.Nonempty) : (s.card : ℝ) * c < ∑ i ∈ s, f i := by
  have hlt := Finset.sum_lt_sum (s := s) (f := fun _ => c) (g := f)
    (fun i hi => (hf i hi).le) ?_
  · simpa [Finset.sum_const, nsmul_eq_mul] using hlt
  · obtain ⟨i, hi⟩ := hne
    exact ⟨i, hi, hf i hi⟩

/-- Real variation is nonnegative. -/
lemma variationReal_nonneg (p : ℝ) (X : ℝ → E) (s t : ℝ) : 0 ≤ variationReal p X s t :=
  ENNReal.toReal_nonneg

/-- Complementary Young exponent `p⁻¹ + q⁻¹`. -/
def youngTheta (p q : ℝ) : ℝ := p⁻¹ + q⁻¹

/-- Weight of `p`-variation in the product control. -/
def youngAlpha (p q : ℝ) : ℝ := p⁻¹ / youngTheta p q

/-- Weight of `q`-variation in the product control. -/
def youngBeta (p q : ℝ) : ℝ := q⁻¹ / youngTheta p q

lemma youngTheta_pos {p q : ℝ} (hpq : 1 < p⁻¹ + q⁻¹) : 0 < youngTheta p q :=
  lt_trans zero_lt_one hpq

lemma youngAlpha_pos {p q : ℝ} (hp : 1 ≤ p) (hpq : 1 < p⁻¹ + q⁻¹) : 0 < youngAlpha p q :=
  div_pos (inv_pos.mpr (lt_of_lt_of_le zero_lt_one hp)) (youngTheta_pos hpq)

lemma youngBeta_pos {p q : ℝ} (hq : 1 ≤ q) (hpq : 1 < p⁻¹ + q⁻¹) : 0 < youngBeta p q :=
  div_pos (inv_pos.mpr (lt_of_lt_of_le zero_lt_one hq)) (youngTheta_pos hpq)

lemma youngAlpha_add_beta {p q : ℝ} (hp : 1 ≤ p) (hq : 1 ≤ q) (hpq : 1 < p⁻¹ + q⁻¹) :
    youngAlpha p q + youngBeta p q = 1 := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp).ne'
  have hq0 : q ≠ 0 := (lt_of_lt_of_le zero_lt_one hq).ne'
  have hθ : p⁻¹ + q⁻¹ ≠ 0 := (lt_trans zero_lt_one hpq).ne'
  unfold youngAlpha youngBeta youngTheta
  field_simp

/-- Product control `v_X ^ α · v_Y ^ β`, with `α + β = 1`. -/
def youngCtrl (p q : ℝ) (X : ℝ → E) {G : Type*} [SeminormedAddCommGroup G]
    (Y : ℝ → G) (s t : ℝ) : ℝ :=
  variationReal p X s t ^ youngAlpha p q * variationReal q Y s t ^ youngBeta p q

/-- The Young modulus `v_X ^ (1/p) · v_Y ^ (1/q)`. -/
def youngModulus (p q : ℝ) (X : ℝ → E) {G : Type*} [SeminormedAddCommGroup G]
    (Y : ℝ → G) (s t : ℝ) : ℝ :=
  variationReal p X s t ^ p⁻¹ * variationReal q Y s t ^ q⁻¹

lemma youngCtrl_nonneg {p q : ℝ} (X : ℝ → E) {G : Type*} [SeminormedAddCommGroup G]
    (Y : ℝ → G) (s t : ℝ) : 0 ≤ youngCtrl p q X Y s t :=
  mul_nonneg (Real.rpow_nonneg (variationReal_nonneg p X s t) _)
    (Real.rpow_nonneg (variationReal_nonneg q Y s t) _)

lemma youngModulus_nonneg {p q : ℝ} (X : ℝ → E) {G : Type*} [SeminormedAddCommGroup G]
    (Y : ℝ → G) (s t : ℝ) : 0 ≤ youngModulus p q X Y s t :=
  mul_nonneg (Real.rpow_nonneg (variationReal_nonneg p X s t) _)
    (Real.rpow_nonneg (variationReal_nonneg q Y s t) _)

lemma youngModulus_eq_ctrl_pow {p q : ℝ} (hp : 1 ≤ p) (hq : 1 ≤ q) (hpq : 1 < p⁻¹ + q⁻¹)
    (X : ℝ → E) {G : Type*} [SeminormedAddCommGroup G] (Y : ℝ → G) (s t : ℝ) :
    youngModulus p q X Y s t = youngCtrl p q X Y s t ^ youngTheta p q := by
  have hvx : 0 ≤ variationReal p X s t := variationReal_nonneg p X s t
  have hvy : 0 ≤ variationReal q Y s t := variationReal_nonneg q Y s t
  unfold youngModulus youngCtrl
  rw [Real.mul_rpow (Real.rpow_nonneg hvx _) (Real.rpow_nonneg hvy _),
    ← Real.rpow_mul hvx (youngAlpha p q) (youngTheta p q),
    ← Real.rpow_mul hvy (youngBeta p q) (youngTheta p q)]
  have hα : youngAlpha p q * youngTheta p q = p⁻¹ := by
    have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp).ne'
    have hθ : youngTheta p q ≠ 0 := (youngTheta_pos hpq).ne'
    unfold youngAlpha youngTheta
    field_simp
  have hβ : youngBeta p q * youngTheta p q = q⁻¹ := by
    have hq0 : q ≠ 0 := (lt_of_lt_of_le zero_lt_one hq).ne'
    have hθ : youngTheta p q ≠ 0 := (youngTheta_pos hpq).ne'
    unfold youngBeta youngTheta
    field_simp
  rw [hα, hβ]

lemma youngCtrl_superadd {s u t : ℝ} (hsu : s ≤ u) (hut : u ≤ t) {p q : ℝ}
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hpq : 1 < p⁻¹ + q⁻¹) (X : ℝ → E)
    {G : Type*} [SeminormedAddCommGroup G] (Y : ℝ → G)
    (hX : pathVariationPower p X s t ≠ ∞) (hY : pathVariationPower q Y s t ≠ ∞) :
    youngCtrl p q X Y s u + youngCtrl p q X Y u t ≤ youngCtrl p q X Y s t := by
  have hα := youngAlpha_pos hp hpq
  have hβ := youngBeta_pos hq hpq
  have hx := variationReal_superadd hsu hut hX
  have hy := variationReal_superadd hsu hut hY
  have hsplit := young_split_le hα hβ (youngAlpha_add_beta hp hq hpq)
    (variationReal_nonneg p X s u) (variationReal_nonneg p X u t)
    (variationReal_nonneg q Y s u) (variationReal_nonneg q Y u t)
  have hx0 : 0 ≤ variationReal p X s u + variationReal p X u t :=
    add_nonneg (variationReal_nonneg _ _ _ _) (variationReal_nonneg _ _ _ _)
  have hy0 : 0 ≤ variationReal q Y s u + variationReal q Y u t :=
    add_nonneg (variationReal_nonneg _ _ _ _) (variationReal_nonneg _ _ _ _)
  have hmul := mul_le_mul (Real.rpow_le_rpow hx0 hx hα.le) (Real.rpow_le_rpow hy0 hy hβ.le)
    (Real.rpow_nonneg hy0 _) (Real.rpow_nonneg (variationReal_nonneg p X s t) _)
  exact hsplit.trans hmul

lemma youngCtrl_mono {c a b d : ℝ} (hca : c ≤ a) (hab : a ≤ b) (hbd : b ≤ d) {p q : ℝ}
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hpq : 1 < p⁻¹ + q⁻¹) (X : ℝ → E)
    {G : Type*} [SeminormedAddCommGroup G] (Y : ℝ → G)
    (hX : pathVariationPower p X c d ≠ ∞) (hY : pathVariationPower q Y c d ≠ ∞) :
    youngCtrl p q X Y a b ≤ youngCtrl p q X Y c d := by
  have hα := youngAlpha_pos hp hpq
  have hβ := youngBeta_pos hq hpq
  exact mul_le_mul
    (Real.rpow_le_rpow (variationReal_nonneg p X a b)
      (variationReal_mono hca hab hbd hX) hα.le)
    (Real.rpow_le_rpow (variationReal_nonneg q Y a b)
      (variationReal_mono hca hab hbd hY) hβ.le)
    (Real.rpow_nonneg (variationReal_nonneg q Y a b) _)
    (Real.rpow_nonneg (variationReal_nonneg p X c d) _)

/-- Superadditivity along every second node of a monotone sequence. -/
lemma ctrl_chain {p q : ℝ} (hp : 1 ≤ p) (hq : 1 ≤ q) (hpq : 1 < p⁻¹ + q⁻¹)
    (X : ℝ → E) {G : Type*} [SeminormedAddCommGroup G] (Y : ℝ → G) :
    ∀ (n : ℕ) (c : ℕ → ℝ), Monotone c →
      pathVariationPower p X (c 0) (c (2 * n)) ≠ ∞ →
      pathVariationPower q Y (c 0) (c (2 * n)) ≠ ∞ →
      ∑ k ∈ range n, youngCtrl p q X Y (c (2 * k)) (c (2 * k + 2)) ≤
        youngCtrl p q X Y (c 0) (c (2 * n)) := by
  intro n
  induction n with
  | zero =>
    intro c hc hX hY
    simp only [sum_range_zero]
    exact youngCtrl_nonneg X Y (c 0) (c 0)
  | succ n ih =>
    intro c hc hX hY
    rw [sum_range_succ]
    have hgrow : c (2 * n) ≤ c (2 * (n + 1)) := hc (by omega)
    have hbase : c 0 ≤ c (2 * n) := hc (by omega)
    have hX' : pathVariationPower p X (c 0) (c (2 * n)) ≠ ∞ :=
      ne_top_of_le_ne_top hX (pathVariationPower_mono (le_refl _) hgrow p X)
    have hY' : pathVariationPower q Y (c 0) (c (2 * n)) ≠ ∞ :=
      ne_top_of_le_ne_top hY (pathVariationPower_mono (le_refl _) hgrow q Y)
    have hsuper := youngCtrl_superadd hbase hgrow hp hq hpq X Y hX hY
    have hidx : 2 * n + 2 = 2 * (n + 1) := by omega
    rw [← hidx] at hsuper
    exact (add_le_add (ih c hc hX' hY') le_rfl).trans hsuper

end YoungLoeve

end CKMA
