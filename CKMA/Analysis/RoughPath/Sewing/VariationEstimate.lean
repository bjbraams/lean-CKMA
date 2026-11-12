/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.RoughPath.Sewing.Variation
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
# Deletion and continuity for Young controls

Every second node of a monotone sequence carries a light Young control.
Reflection and almost-subadditivity give continuity of finite `p`-variation,
and short intervals carry an arbitrarily small control.
-/

@[expose] public section

noncomputable section

namespace CKMA

open scoped BigOperators NNReal ENNReal
open Finset Filter Topology Metric

namespace YoungLoeve

variable {E : Type*} [SeminormedAddCommGroup E]

/-- Odd interior indices stay below the length of the node sequence. -/
lemma index_odd_lt {k n : ℕ} (hk : k < n / 2) : 2 * k + 1 < n := by
  have hmul : 2 * (k + 1) ≤ 2 * (n / 2) := Nat.mul_le_mul_left 2 (Nat.succ_le_of_lt hk)
  have hself : 2 * (n / 2) ≤ n := by simpa [Nat.mul_comm] using Nat.div_mul_le_self n 2
  have : 2 * k + 2 ≤ n := by
    calc
      2 * k + 2 = 2 * (k + 1) := by omega
      _ ≤ 2 * (n / 2) := hmul
      _ ≤ n := hself
  omega

/-- Even interior indices stay below the length of the node sequence. -/
lemma index_even_lt {k n : ℕ} (hk : k < (n - 1) / 2) : 2 * k + 2 < n := by
  have hmul : 2 * (k + 1) ≤ 2 * ((n - 1) / 2) :=
    Nat.mul_le_mul_left 2 (Nat.succ_le_of_lt hk)
  have hself : 2 * ((n - 1) / 2) ≤ n - 1 := by
    simpa [Nat.mul_comm] using Nat.div_mul_le_self (n - 1) 2
  have : 2 * k + 2 ≤ n - 1 := by
    calc
      2 * k + 2 = 2 * (k + 1) := by omega
      _ ≤ 2 * ((n - 1) / 2) := hmul
      _ ≤ n - 1 := hself
  omega

/-- Some interior node has merged control at most twice the average. -/
lemma exists_light_ctrl {n : ℕ} (hn : 2 ≤ n) (c : ℕ → ℝ) (hc : Monotone c) {p q : ℝ}
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hpq : 1 < p⁻¹ + q⁻¹) (X : ℝ → E)
    {G : Type*} [SeminormedAddCommGroup G] (Y : ℝ → G)
    (hX : pathVariationPower p X (c 0) (c n) ≠ ∞)
    (hY : pathVariationPower q Y (c 0) (c n) ≠ ∞) :
    ∃ j, 0 < j ∧ j < n ∧
      youngCtrl p q X Y (c (j - 1)) (c (j + 1)) ≤
        (2 / ((n - 1 : ℕ) : ℝ)) * youngCtrl p q X Y (c 0) (c n) := by
  set Ω : ℝ := youngCtrl p q X Y (c 0) (c n)
  set κ : ℝ := (2 : ℝ) / ((n - 1 : ℕ) : ℝ) * Ω
  by_contra h
  push Not at h
  have hΩ : 0 ≤ Ω := youngCtrl_nonneg X Y (c 0) (c n)
  have htail : 2 * (n / 2) ≤ n := by omega
  have hodd_le : ∑ k ∈ range (n / 2), youngCtrl p q X Y (c (2 * k)) (c (2 * k + 2)) ≤ Ω := by
    have hsum := ctrl_chain hp hq hpq X Y (n / 2) c hc
      (ne_top_of_le_ne_top hX (pathVariationPower_mono (le_refl _) (hc htail) p X))
      (ne_top_of_le_ne_top hY (pathVariationPower_mono (le_refl _) (hc htail) q Y))
    exact hsum.trans (youngCtrl_mono (le_refl (c 0)) (hc (by omega : (0 : ℕ) ≤ 2 * (n / 2)))
      (hc htail) hp hq hpq X Y hX hY)
  have heven_le : ∑ k ∈ range ((n - 1) / 2),
      youngCtrl p q X Y (c (2 * k + 1)) (c (2 * k + 3)) ≤ Ω := by
    by_cases hm0 : (n - 1) / 2 = 0
    · simp only [hm0, sum_range_zero]
      exact hΩ
    · let c' : ℕ → ℝ := fun i => c (i + 1)
      have hc' : Monotone c' := fun i j hij => hc (Nat.add_le_add_right hij 1)
      have hend : 2 * ((n - 1) / 2) + 1 ≤ n := by omega
      have hleft : c 0 ≤ c 1 := hc (by omega)
      have hX' : pathVariationPower p X (c' 0) (c' (2 * ((n - 1) / 2))) ≠ ∞ := by
        simpa [c'] using ne_top_of_le_ne_top hX
          (pathVariationPower_mono hleft (hc hend) p X)
      have hY' : pathVariationPower q Y (c' 0) (c' (2 * ((n - 1) / 2))) ≠ ∞ := by
        simpa [c'] using ne_top_of_le_ne_top hY
          (pathVariationPower_mono hleft (hc hend) q Y)
      have hsum := ctrl_chain hp hq hpq X Y ((n - 1) / 2) c' hc' hX' hY'
      have hwide := youngCtrl_mono hleft (hc (by omega : 1 ≤ 2 * ((n - 1) / 2) + 1))
        (hc hend) hp hq hpq X Y hX hY
      simpa [c'] using hsum.trans hwide
  have hcoe : ((n / 2 : ℕ) : ℝ) + (((n - 1) / 2 : ℕ) : ℝ) = ((n - 1 : ℕ) : ℝ) := by
    rw [← Nat.cast_add]
    exact congrArg (Nat.cast : ℕ → ℝ) (by omega)
  have htwo : ((n / 2 : ℕ) : ℝ) * κ + (((n - 1) / 2 : ℕ) : ℝ) * κ = 2 * Ω := by
    have hn0 : ((n - 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show n - 1 ≠ 0 by omega)
    calc
      ((n / 2 : ℕ) : ℝ) * κ + (((n - 1) / 2 : ℕ) : ℝ) * κ =
          (((n / 2 : ℕ) : ℝ) + (((n - 1) / 2 : ℕ) : ℝ)) * κ := by ring
      _ = ((n - 1 : ℕ) : ℝ) * κ := by rw [hcoe]
      _ = 2 * Ω := by simp only [κ]; field_simp [hn0]
  have hodd_term : ∀ k ∈ range (n / 2), κ < youngCtrl p q X Y (c (2 * k)) (c (2 * k + 2)) := by
    intro k hk
    have hL : (2 * k + 1) - 1 = 2 * k := by omega
    have hR : (2 * k + 1) + 1 = 2 * k + 2 := by omega
    simpa [hL, hR] using h (2 * k + 1) (by omega) (index_odd_lt (mem_range.mp hk))
  have hodd_ne : (range (n / 2)).Nonempty := ⟨0, mem_range.mpr (by omega)⟩
  have hodd_gt := sum_gt_card_mul hodd_term hodd_ne
  simp only [card_range] at hodd_gt
  by_cases hm0 : (n - 1) / 2 = 0
  · have hn2 : n = 2 := by omega
    subst hn2
    simp only [κ] at hodd_gt
    linarith
  · have heven_term : ∀ k ∈ range ((n - 1) / 2),
        κ < youngCtrl p q X Y (c (2 * k + 1)) (c (2 * k + 3)) := by
      intro k hk
      have hL : (2 * k + 2) - 1 = 2 * k + 1 := by omega
      have hR : (2 * k + 2) + 1 = 2 * k + 3 := by omega
      simpa [hL, hR] using h (2 * k + 2) (by omega) (index_even_lt (mem_range.mp hk))
    have heven_ne : (range ((n - 1) / 2)).Nonempty := ⟨0, mem_range.mpr (by omega)⟩
    have heven_gt := sum_gt_card_mul heven_term heven_ne
    simp only [card_range] at heven_gt
    have hsum_gt : 2 * Ω <
        (∑ k ∈ range (n / 2), youngCtrl p q X Y (c (2 * k)) (c (2 * k + 2))) +
        (∑ k ∈ range ((n - 1) / 2), youngCtrl p q X Y (c (2 * k + 1)) (c (2 * k + 3))) := by
      linarith [hodd_gt, heven_gt, htwo]
    have hsum_le := add_le_add hodd_le heven_le
    linarith

/-- Left-point Young increment. -/
def youngStep {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (X : ℝ → E) (Y : ℝ → E →L[ℝ] F) (s t : ℝ) : F :=
  Y s (X t - X s)

lemma norm_young_defect {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {s u t : ℝ} (hsu : s ≤ u) (hut : u ≤ t)
    {p q : ℝ} (hp : 1 ≤ p) (hq : 1 ≤ q) (X : ℝ → E)
    (Y : ℝ → E →L[ℝ] F) (hX : pathVariationPower p X s t ≠ ∞)
    (hY : pathVariationPower q Y s t ≠ ∞) :
    ‖youngStep X Y s u + youngStep X Y u t - youngStep X Y s t‖ ≤
      youngModulus p q X Y s t := by
  have hneg : youngStep X Y s u + youngStep X Y u t - youngStep X Y s t =
      - (youngStep X Y s t - youngStep X Y s u - youngStep X Y u t) := by abel
  rw [hneg, norm_neg]
  have hAlg : youngStep X Y s t - youngStep X Y s u - youngStep X Y u t =
      (Y s - Y u) (X t - X u) := by
    simp only [youngStep]
    rw [← map_sub]
    have : (X t - X s) - (X u - X s) = X t - X u := by abel
    rw [this, ← sub_apply]
  rw [hAlg]
  have hYsu : pathVariationPower q Y s u ≠ ∞ :=
    ne_top_of_le_ne_top hY (pathVariationPower_mono (le_refl s) hut q Y)
  have hXut : pathVariationPower p X u t ≠ ∞ :=
    ne_top_of_le_ne_top hX (pathVariationPower_mono hsu (le_refl t) p X)
  have hYle : ‖Y s - Y u‖ ≤ variationReal q Y s u ^ q⁻¹ := by
    rw [norm_sub_rev]
    exact norm_le_variationReal hsu (lt_of_lt_of_le zero_lt_one hq) hYsu
  have hXle := norm_le_variationReal hut (lt_of_lt_of_le zero_lt_one hp) hXut
  have hYm := Real.rpow_le_rpow (variationReal_nonneg q Y s u)
    (variationReal_mono (le_refl s) hsu hut hY) (inv_nonneg.mpr (le_trans zero_le_one hq))
  have hXm := Real.rpow_le_rpow (variationReal_nonneg p X u t)
    (variationReal_mono hsu hut (le_refl t) hX) (inv_nonneg.mpr (le_trans zero_le_one hp))
  calc
    ‖(Y s - Y u) (X t - X u)‖ ≤ ‖Y s - Y u‖ * ‖X t - X u‖ := (Y s - Y u).le_opNorm _
    _ ≤ variationReal q Y s u ^ q⁻¹ * variationReal p X u t ^ p⁻¹ :=
      mul_le_mul hYle hXle (norm_nonneg _)
        (Real.rpow_nonneg (variationReal_nonneg q Y s u) _)
    _ ≤ variationReal q Y s t ^ q⁻¹ * variationReal p X s t ^ p⁻¹ :=
      mul_le_mul hYm hXm (Real.rpow_nonneg (variationReal_nonneg p X u t) _)
        (Real.rpow_nonneg (variationReal_nonneg q Y s t) _)
    _ = youngModulus p q X Y s t := by rw [mul_comm]; rfl

/-- Removing light nodes bounds a partition sum by the loose Young series. -/
lemma young_step_bound {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {p q : ℝ} (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hpq : 1 < p⁻¹ + q⁻¹) (X : ℝ → E) (Y : ℝ → E →L[ℝ] F) :
    ∀ (n : ℕ) (c : ℕ → ℝ), Monotone c →
      pathVariationPower p X (c 0) (c n) ≠ ∞ →
      pathVariationPower q Y (c 0) (c n) ≠ ∞ →
      ‖stepSum (youngStep X Y) c n - youngStep X Y (c 0) (c n)‖ ≤
        youngPartial (youngTheta p q) (n - 1) * youngModulus p q X Y (c 0) (c n) := by
  intro n
  induction n with
  | zero =>
    intro c hc hX hY
    simp [stepSum, youngStep, youngPartial, map_zero, norm_zero]
  | succ n ih =>
    intro c hc hX hY
    by_cases hn0 : n = 0
    · subst hn0
      simp [stepSum, youngPartial, sub_self, norm_zero]
    · have hjn : 2 ≤ n + 1 := by omega
      obtain ⟨j, hj0, hjlt, hlight⟩ := exists_light_ctrl hjn c hc hp hq hpq X Y hX hY
      have hd0 : dropNode c j 0 = c 0 := dropNode_of_lt c hj0
      have hdn : dropNode c j n = c (n + 1) := dropNode_of_ge c (by omega)
      have hXd : pathVariationPower p X (dropNode c j 0) (dropNode c j n) ≠ ∞ := by
        simpa [hd0, hdn] using hX
      have hYd : pathVariationPower q Y (dropNode c j 0) (dropNode c j n) ≠ ∞ := by
        simpa [hd0, hdn] using hY
      have ih' := ih (dropNode c j) (monotone_dropNode hc j) hXd hYd
      rw [hd0, hdn] at ih'
      have hsplit := stepSum_drop (youngStep X Y) c hj0 hjlt
      have hδ : ‖youngStep X Y (c (j - 1)) (c j) + youngStep X Y (c j) (c (j + 1)) -
          youngStep X Y (c (j - 1)) (c (j + 1))‖ ≤
          (2 / (n : ℝ)) ^ youngTheta p q * youngModulus p q X Y (c 0) (c (n + 1)) := by
        have hsj : c (j - 1) ≤ c j := hc (by omega)
        have hjt : c j ≤ c (j + 1) := hc (by omega)
        have houterL : c 0 ≤ c (j - 1) := hc (by omega)
        have houterR : c (j + 1) ≤ c (n + 1) := hc (by omega)
        have hXj : pathVariationPower p X (c (j - 1)) (c (j + 1)) ≠ ∞ :=
          ne_top_of_le_ne_top hX (pathVariationPower_mono houterL houterR p X)
        have hYj : pathVariationPower q Y (c (j - 1)) (c (j + 1)) ≠ ∞ :=
          ne_top_of_le_ne_top hY (pathVariationPower_mono houterL houterR q Y)
        have hmod := norm_young_defect hsj hjt hp hq X Y hXj hYj
        have hr0 : 0 ≤ (2 : ℝ) / (n : ℝ) :=
          div_nonneg (by norm_num) (Nat.cast_nonneg _)
        calc
          ‖youngStep X Y (c (j - 1)) (c j) + youngStep X Y (c j) (c (j + 1)) -
              youngStep X Y (c (j - 1)) (c (j + 1))‖ ≤
              youngModulus p q X Y (c (j - 1)) (c (j + 1)) := hmod
          _ = youngCtrl p q X Y (c (j - 1)) (c (j + 1)) ^ youngTheta p q :=
            youngModulus_eq_ctrl_pow hp hq hpq X Y (c (j - 1)) (c (j + 1))
          _ ≤ ((2 / (n : ℝ)) * youngCtrl p q X Y (c 0) (c (n + 1))) ^ youngTheta p q :=
            Real.rpow_le_rpow (youngCtrl_nonneg X Y (c (j - 1)) (c (j + 1))) hlight
              (youngTheta_pos hpq).le
          _ = (2 / (n : ℝ)) ^ youngTheta p q *
              youngCtrl p q X Y (c 0) (c (n + 1)) ^ youngTheta p q :=
            Real.mul_rpow hr0 (youngCtrl_nonneg X Y (c 0) (c (n + 1)))
          _ = (2 / (n : ℝ)) ^ youngTheta p q * youngModulus p q X Y (c 0) (c (n + 1)) := by
            rw [← youngModulus_eq_ctrl_pow hp hq hpq X Y (c 0) (c (n + 1))]
      have hregroup : stepSum (youngStep X Y) c (n + 1) -
          youngStep X Y (c 0) (c (n + 1)) =
          (stepSum (youngStep X Y) (dropNode c j) n -
            youngStep X Y (c 0) (c (n + 1))) +
          (youngStep X Y (c (j - 1)) (c j) + youngStep X Y (c j) (c (j + 1)) -
            youngStep X Y (c (j - 1)) (c (j + 1))) := by
        rw [hsplit, show n + 1 - 1 = n by omega]
        abel_nf
      calc
        ‖stepSum (youngStep X Y) c (n + 1) - youngStep X Y (c 0) (c (n + 1))‖ =
            ‖(stepSum (youngStep X Y) (dropNode c j) n -
              youngStep X Y (c 0) (c (n + 1))) +
              (youngStep X Y (c (j - 1)) (c j) + youngStep X Y (c j) (c (j + 1)) -
                youngStep X Y (c (j - 1)) (c (j + 1)))‖ := by rw [hregroup]
        _ ≤ ‖stepSum (youngStep X Y) (dropNode c j) n -
              youngStep X Y (c 0) (c (n + 1))‖ +
            ‖youngStep X Y (c (j - 1)) (c j) + youngStep X Y (c j) (c (j + 1)) -
              youngStep X Y (c (j - 1)) (c (j + 1))‖ := norm_add_le _ _
        _ ≤ youngPartial (youngTheta p q) (n - 1) * youngModulus p q X Y (c 0) (c (n + 1)) +
            (2 / (n : ℝ)) ^ youngTheta p q * youngModulus p q X Y (c 0) (c (n + 1)) :=
          add_le_add ih' hδ
        _ = (youngPartial (youngTheta p q) (n - 1) + (2 / (n : ℝ)) ^ youngTheta p q) *
            youngModulus p q X Y (c 0) (c (n + 1)) := by rw [← add_mul]
        _ = youngPartial (youngTheta p q) n * youngModulus p q X Y (c 0) (c (n + 1)) := by
          rw [← youngPartial_step (by omega : 0 < n)]

/-- Tail of an ordered partition, beginning at node `k`. -/
def suffixPart {s u : ℝ} (π : OrderedIntervalPartition s u) (k : ℕ) (hk : k ≤ π.size) :
    OrderedIntervalPartition (nodeSeq π k) u where
  size := π.size - k
  node := fun i => π.node ⟨k + i.val, by have := i.isLt; omega⟩
  monotone_node := by
    intro i j hij
    have hijv : i.val ≤ j.val := (Fin.le_iff_val_le_val).mp hij
    exact π.monotone_node <| (Fin.le_iff_val_le_val).mpr (Nat.add_le_add_left hijv k)
  node_zero := by
    show π.node ⟨k + (0 : Fin (π.size - k + 1)).val, _⟩ = nodeSeq π k
    simp only [Fin.val_zero, add_zero]
    rw [nodeSeq_of_le π hk]
  node_last := by
    show π.node ⟨k + (Fin.last (π.size - k)).val, _⟩ = u
    have hval : k + (Fin.last (π.size - k)).val = π.size := by
      simp [Fin.val_last, Nat.add_sub_of_le hk]
    have hidx : (⟨k + (Fin.last (π.size - k)).val, by omega⟩ : Fin (π.size + 1)) =
        ⟨π.size, by omega⟩ := by
      ext; exact hval
    rw [hidx]
    have hlast : (⟨π.size, by omega⟩ : Fin (π.size + 1)) = Fin.last π.size := by
      ext; simp [Fin.val_last]
    rw [hlast, π.node_last]

/-- Nodes of a tail are nodes of the original partition. -/
lemma nodeSeq_suffix {s u : ℝ} (π : OrderedIntervalPartition s u) {k i : ℕ}
    (hk : k ≤ π.size) (hi : i ≤ π.size - k) :
    nodeSeq (suffixPart π k hk) i = nodeSeq π (k + i) := by
  unfold nodeSeq suffixPart
  have hmin1 : min i (π.size - k) = i := Nat.min_eq_left hi
  have hmin2 : min (k + i) π.size = k + i := Nat.min_eq_left (by omega)
  simp [hmin1, hmin2]

/-- A variation sum splits into a prefix and the tail partition. -/
lemma variationSum_take (p : ℝ) (X : ℝ → E) {s u : ℝ} (π : OrderedIntervalPartition s u)
    {k : ℕ} (hk : k ≤ π.size) :
    variationSum p X π =
      (∑ i ∈ range k, ENNReal.ofReal (‖X (nodeSeq π (i + 1)) - X (nodeSeq π i)‖ ^ p)) +
        variationSum p X (suffixPart π k hk) := by
  rw [variationSum_eq_stepSum, variationSum_eq_stepSum]
  have hsize : (suffixPart π k hk).size = π.size - k := rfl
  simp only [hsize]
  have htail : ∑ i ∈ range (π.size - k),
      ENNReal.ofReal (‖X (nodeSeq (suffixPart π k hk) (i + 1)) -
        X (nodeSeq (suffixPart π k hk) i)‖ ^ p) =
      ∑ i ∈ range (π.size - k),
        ENNReal.ofReal (‖X (nodeSeq π (k + i + 1)) - X (nodeSeq π (k + i))‖ ^ p) := by
    refine sum_congr rfl fun i hi => ?_
    have hi' : i < π.size - k := mem_range.mp hi
    simp [nodeSeq_suffix π hk (le_of_lt hi'), nodeSeq_suffix π hk (Nat.succ_le_of_lt hi'),
      Nat.add_assoc]
  rw [htail]
  have hsplit := sum_range_add
    (fun i => ENNReal.ofReal (‖X (nodeSeq π (i + 1)) - X (nodeSeq π i)‖ ^ p)) k (π.size - k)
  rwa [Nat.add_sub_of_le hk] at hsplit

/-- Reflection of the time parameter through the interval `[c, d]`. -/
def timeReflect (c d : ℝ) (X : ℝ → E) (u : ℝ) : E :=
  X (c + d - u)

/-- The partition read from right to left after time reflection. -/
def reflectPart (c d : ℝ) {s t : ℝ} (π : OrderedIntervalPartition s t) :
    OrderedIntervalPartition (c + d - t) (c + d - s) where
  size := π.size
  node := fun i => c + d - π.node ⟨π.size - i.val, by have := i.isLt; omega⟩
  monotone_node := by
    intro i j hij
    have hrev : π.size - j.val ≤ π.size - i.val := by
      have hijv := Fin.le_iff_val_le_val.mp hij
      omega
    have hle : (⟨π.size - j.val, by have := j.isLt; omega⟩ : Fin (π.size + 1)) ≤
        ⟨π.size - i.val, by have := i.isLt; omega⟩ := by
      rw [Fin.le_iff_val_le_val]
      exact hrev
    have hnode := π.monotone_node hle
    linarith
  node_zero := by
    show c + d - π.node ⟨π.size - (0 : Fin (π.size + 1)).val, _⟩ = c + d - t
    simp only [Fin.val_zero, Nat.sub_zero]
    have hlast : (⟨π.size, by omega⟩ : Fin (π.size + 1)) = Fin.last π.size := by
      ext; simp [Fin.val_last]
    rw [hlast, π.node_last]
  node_last := by
    show c + d - π.node ⟨π.size - (Fin.last π.size).val, _⟩ = c + d - s
    simp only [Fin.val_last]
    have hzero : (⟨π.size - π.size, by omega⟩ : Fin (π.size + 1)) = 0 := by
      ext; simp
    rw [hzero, π.node_zero]

/-- Reflection preserves sums of increment powers. -/
lemma variationSum_reflect (c d p : ℝ) (X : ℝ → E) {s t : ℝ}
    (π : OrderedIntervalPartition s t) :
    variationSum p (timeReflect c d X) (reflectPart c d π) = variationSum p X π := by
  unfold variationSum
  let e : Fin π.size ≃ Fin π.size :=
    { toFun := fun i => ⟨π.size - 1 - i.val, by have := i.isLt; omega⟩
      invFun := fun i => ⟨π.size - 1 - i.val, by have := i.isLt; omega⟩
      left_inv := fun i => by ext; simp; omega
      right_inv := fun i => by ext; simp; omega }
  refine Fintype.sum_equiv e
    (fun i => ENNReal.ofReal (‖timeReflect c d X ((reflectPart c d π).node i.succ) -
      timeReflect c d X ((reflectPart c d π).node i.castSucc)‖ ^ p))
    (fun i => ENNReal.ofReal (‖X (π.node i.succ) - X (π.node i.castSucc)‖ ^ p))
    fun i => ?_
  have hRs : (reflectPart c d π).node i.succ =
      c + d - π.node ⟨π.size - (i.val + 1), by have := i.isLt; omega⟩ := by
    simp [reflectPart, Fin.val_succ]
  have hRc : (reflectPart c d π).node i.castSucc =
      c + d - π.node ⟨π.size - i.val, by have := i.isLt; omega⟩ := by
    simp [reflectPart, Fin.val_castSucc]
  have hEq : timeReflect c d X ((reflectPart c d π).node i.succ) -
      timeReflect c d X ((reflectPart c d π).node i.castSucc) =
      - (X (π.node (e i).succ) - X (π.node (e i).castSucc)) := by
    rw [hRs, hRc]
    simp only [timeReflect, sub_sub_cancel]
    have h1 : (⟨π.size - (i.val + 1), by have := i.isLt; omega⟩ : Fin (π.size + 1)) =
        (e i).castSucc := by ext; simp [e]; omega
    have h2 : (⟨π.size - i.val, by have := i.isLt; omega⟩ : Fin (π.size + 1)) =
        (e i).succ := by ext; simp [e]; omega
    rw [h1, h2]
    abel
  rw [hEq, norm_neg]

/-- Transport an ordered partition across propositionally equal endpoints. -/
def castPart {s t s' t' : ℝ} (hs : s = s') (ht : t = t')
    (π : OrderedIntervalPartition s t) : OrderedIntervalPartition s' t' := by
  cases hs
  cases ht
  exact π

/-- Endpoint transport does not change a variation sum. -/
lemma variationSum_cast {s t s' t' : ℝ} (hs : s = s') (ht : t = t') (p : ℝ) (X : ℝ → E)
    (π : OrderedIntervalPartition s t) :
    variationSum p X (castPart hs ht π) = variationSum p X π := by
  cases hs
  cases ht
  rfl

/-- Reflected paths have the reflected `p`-variation. -/
lemma pathVariationPower_reflect {c d s t : ℝ} (p : ℝ) (X : ℝ → E) :
    pathVariationPower p (timeReflect c d X) (c + d - t) (c + d - s) =
      pathVariationPower p X s t := by
  apply le_antisymm
  · refine iSup_le fun σ => ?_
    have hsum := variationSum_reflect c d p (timeReflect c d X) σ
    have hId : timeReflect c d (timeReflect c d X) = X := by
      funext u
      simp only [timeReflect]
      ring_nf
    rw [hId] at hsum
    have hs : c + d - (c + d - s) = s := by ring
    have ht : c + d - (c + d - t) = t := by ring
    have hcast := variationSum_cast hs ht p X (reflectPart c d σ)
    rw [pathVariationPower_eq_iSup]
    exact (le_of_eq (hsum.symm.trans hcast.symm)).trans
      (le_iSup (variationSum p X) (castPart hs ht (reflectPart c d σ)))
  · refine iSup_le fun π => ?_
    rw [pathVariationPower_eq_iSup]
    exact (le_of_eq (variationSum_reflect c d p X π).symm).trans
      (le_iSup (variationSum p (timeReflect c d X)) (reflectPart c d π))

/-- Deleting the first positive step leaves a definite fraction of the variation. -/
lemma exists_variation_tail {a b p : ℝ} (hp : 1 ≤ p) (X : ℝ → E)
    {t u η δ : ℝ}
    (ht : a ≤ t) (htu : t < u) (hub : u ≤ b) (hδ : u - t < δ) (hη : 0 < η)
    (hclose : ∀ r ∈ Set.Icc a b, |r - t| < δ → ‖X r - X t‖ ^ p < η / 8)
    (hlow : η ≤ variationReal p X t u) (hfin : pathVariationPower p X t u ≠ ∞) :
    ∃ m, t < m ∧ m < u ∧ ∃ σ : OrderedIntervalPartition m u,
      3 / 4 * η < (variationSum p X σ).toReal := by
  have h78 : 7 / 8 * η < variationReal p X t u := by
    have hcoe : 7 / 8 * η < η := by linarith
    exact lt_of_lt_of_le hcoe hlow
  obtain ⟨π, hπ⟩ := exists_variationSum_gt hfin h78 (by positivity)
  obtain ⟨j, hjle, hgt, hmin⟩ := exists_least_index_gt π.size (nodeSeq π) t
    ⟨π.size, le_rfl, by simpa [nodeSeq_size] using htu⟩
  have _hj0 : 0 < j := by
    cases j with
    | zero => simp [nodeSeq_zero] at hgt
    | succ => omega
  have hflat : ∀ i < j, nodeSeq π i = t := by
    intro i hi
    exact le_antisymm (hmin i hi) (by simpa [nodeSeq_zero] using monotone_nodeSeq π (Nat.zero_le i))
  set m : ℝ := nodeSeq π j
  have hmt : t < m := hgt
  have hmu : m ≤ u := by simpa [m, nodeSeq_size] using monotone_nodeSeq π hjle
  have hprefix : ∑ i ∈ range j,
      ENNReal.ofReal (‖X (nodeSeq π (i + 1)) - X (nodeSeq π i)‖ ^ p) =
      ENNReal.ofReal (‖X m - X t‖ ^ p) := by
    have hj1 : j = (j - 1) + 1 := by omega
    rw [hj1, sum_range_succ]
    have hzero : ∑ i ∈ range (j - 1),
        ENNReal.ofReal (‖X (nodeSeq π (i + 1)) - X (nodeSeq π i)‖ ^ p) = 0 := by
      refine Finset.sum_eq_zero fun i hi => ?_
      have hi' : i < j - 1 := mem_range.mp hi
      simp [hflat i (by omega), hflat (i + 1) (by omega), sub_self,
        Real.zero_rpow (ne_of_gt (lt_of_lt_of_le zero_lt_one hp)), ENNReal.ofReal_zero]
    rw [hzero, zero_add, hflat (j - 1) (by omega)]
    have hjj : j - 1 + 1 = j := by omega
    simp [hjj, m]
  have hpow : ‖X m - X t‖ ^ p < η / 8 := by
    have hmI : m ∈ Set.Icc a b := ⟨le_trans ht hmt.le, le_trans hmu hub⟩
    have hdist : |m - t| < δ := by
      rw [abs_of_nonneg (sub_nonneg.mpr hmt.le)]
      exact lt_of_le_of_lt (sub_le_sub_right hmu t) hδ
    exact hclose m hmI hdist
  have hsplit := variationSum_take p X π hjle
  rw [hprefix] at hsplit
  have htot : variationSum p X π ≠ ∞ := ne_top_of_le_ne_top hfin (le_iSup _ π)
  have hne := (ENNReal.add_ne_top).mp (hsplit ▸ htot)
  have hto := ENNReal.toReal_add hne.1 hne.2
  rw [← hsplit] at hto
  have hpre : (ENNReal.ofReal (‖X m - X t‖ ^ p)).toReal = ‖X m - X t‖ ^ p :=
    ENNReal.toReal_ofReal (Real.rpow_nonneg (norm_nonneg _) _)
  have htail : 3 / 4 * η < (variationSum p X (suffixPart π j hjle)).toReal := by
    have hsub : (variationSum p X π).toReal - ‖X m - X t‖ ^ p =
        (variationSum p X (suffixPart π j hjle)).toReal := by
      linarith [hto, hpre]
    linarith [hπ, hpow, hsub]
  have hmlt : m < u := by
    by_contra hge
    have heq : m = u := le_antisymm hmu (le_of_not_gt hge)
    have hnodes : ∀ i, (suffixPart π j hjle).node i = m := by
      intro i
      have h0 := (suffixPart π j hjle).monotone_node (Fin.zero_le i)
      have h1 := (suffixPart π j hjle).monotone_node (Fin.le_last i)
      rw [(suffixPart π j hjle).node_zero] at h0
      rw [(suffixPart π j hjle).node_last] at h1
      change m ≤ (suffixPart π j hjle).node i at h0
      exact le_antisymm (h1.trans (le_of_eq heq.symm)) h0
    have hzero : variationSum p X (suffixPart π j hjle) = 0 := by
      unfold variationSum
      refine Finset.sum_eq_zero fun i _ => ?_
      simp [hnodes i.castSucc, hnodes i.succ, sub_self,
        Real.zero_rpow (ne_of_gt (lt_of_lt_of_le zero_lt_one hp)), ENNReal.ofReal_zero]
    simp [hzero, ENNReal.toReal_zero] at htail
    linarith
  exact ⟨m, hmt, hmlt, suffixPart π j hjle, htail⟩

/-- Convex increments of `x ^ p` increase with the left endpoint. -/
lemma rpow_sub_le {p M α β : ℝ} (hp : 1 ≤ p) (hM : 0 ≤ M) (hα : 0 ≤ α) (hαM : α ≤ M)
    (hβ : 0 ≤ β) : (α + β) ^ p - α ^ p ≤ (M + β) ^ p - M ^ p := by
  rcases eq_or_lt_of_le hβ with rfl | hβ0
  · simp
  · set t := β / (M - α + β)
    have hden : 0 < M - α + β := by linarith
    have ht0 : 0 ≤ t := div_nonneg hβ hden.le
    have ht1 : t ≤ 1 := by rw [div_le_one₀ hden]; linarith
    have hcomb1 : (1 - t) * α + t * (M + β) = α + β := by
      simp only [t]; field_simp [hden.ne']; ring
    have hcomb2 : t * α + (1 - t) * (M + β) = M := by
      simp only [t]; field_simp [hden.ne']; ring
    have hconv := (convexOn_rpow hp).2
    have h1 := hconv (show α ∈ Set.Ici 0 from hα) (show M + β ∈ Set.Ici 0 from add_nonneg hM hβ)
      (sub_nonneg.mpr ht1) ht0 (by ring : (1 - t) + t = 1)
    have h2 := hconv (show α ∈ Set.Ici 0 from hα) (show M + β ∈ Set.Ici 0 from add_nonneg hM hβ)
      ht0 (sub_nonneg.mpr ht1) (by ring : t + (1 - t) = 1)
    simp only [smul_eq_mul] at h1 h2
    rw [hcomb1] at h1
    rw [hcomb2] at h2
    linarith

/-- A uniform positive lower bound on right variation upgrades by the factor `7 / 4`. -/
lemma variation_right_boost {a b p : ℝ} (hp : 1 ≤ p) (X : ℝ → E)
    (hX : ContinuousOn X (Set.Icc a b)) (hfin : pathVariationPower p X a b ≠ ∞)
    {t η : ℝ} (ht : a ≤ t) (htb : t < b) (hη : 0 < η)
    (hlow : ∀ u, t < u → u ≤ b → η ≤ variationReal p X t u) :
    ∀ u, t < u → u ≤ b → (7 / 4) * η ≤ variationReal p X t u := by
  have hcont := hX t ⟨ht, htb.le⟩
  rw [Metric.continuousWithinAt_iff] at hcont
  set c : ℝ := min 1 (η / 8)
  have hc : 0 < c := lt_min one_pos (div_pos hη (by norm_num))
  obtain ⟨δ, hδpos, hnear⟩ := hcont c hc
  have hpow : ∀ r ∈ Set.Icc a b, |r - t| < δ → ‖X r - X t‖ ^ p < η / 8 := by
    intro r hr hrd
    have hn : ‖X r - X t‖ < c := by
      have hdist : dist r t < δ := by simpa [Real.dist_eq] using hrd
      simpa [dist_eq_norm] using hnear hr hdist
    by_cases hzero : ‖X r - X t‖ = 0
    · rw [hzero, Real.zero_rpow (ne_of_gt (lt_of_lt_of_le zero_lt_one hp))]
      exact div_pos hη (by norm_num)
    · have hpos : 0 < ‖X r - X t‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)
      have hle : ‖X r - X t‖ ^ p ≤ ‖X r - X t‖ := by
        simpa [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hpos
          ((hn.trans_le (min_le_left _ _)).le) hp
      exact lt_of_le_of_lt hle (hn.trans_le (min_le_right _ _))
  have hpiece : ∀ u, t < u → u ≤ b → u - t < δ → (7 / 4) * η ≤ variationReal p X t u := by
    intro u htu hub hlen
    have hfinu : pathVariationPower p X t u ≠ ∞ :=
      ne_top_of_le_ne_top hfin (pathVariationPower_mono ht hub p X)
    obtain ⟨m, htm, hmu, σ, hσ⟩ :=
      exists_variation_tail hp X ht htu hub hlen hη hpow (hlow u htu hub) hfinu
    have hfinmu : pathVariationPower p X m u ≠ ∞ :=
      ne_top_of_le_ne_top hfinu (pathVariationPower_mono htm.le (le_refl u) p X)
    have hvtail : (3 / 4) * η < variationReal p X m u :=
      lt_of_lt_of_le hσ (ENNReal.toReal_mono hfinmu (le_iSup (variationSum p X) σ))
    have hsuper := variationReal_superadd htm.le hmu.le hfinu
    exact le_of_lt (by linarith [hlow m htm (hmu.le.trans hub)])
  intro u htu hub
  by_cases hlen : u - t < δ
  · exact hpiece u htu hub hlen
  · have htu1 : t < t + δ / 2 := by linarith [hδpos]
    have hu1u : t + δ / 2 ≤ u := by linarith [not_lt.mp hlen]
    exact (hpiece (t + δ / 2) htu1 (hu1u.trans hub) (by linarith [hδpos])).trans
      (variationReal_mono (le_refl t) htu1.le hu1u
        (ne_top_of_le_ne_top hfin (pathVariationPower_mono ht hub p X)))

/-- Right variation of a continuous finite-variation path vanishes at the diagonal. -/
lemma variation_right_vanish {a b p : ℝ} (hp : 1 ≤ p) (X : ℝ → E)
    (hX : ContinuousOn X (Set.Icc a b)) (hfin : pathVariationPower p X a b ≠ ∞)
    {t : ℝ} (ht : a ≤ t) (htb : t ≤ b) :
    ∀ ε > 0, ∃ δ > 0, ∀ u, t < u → u ≤ b → u - t < δ → variationReal p X t u < ε := by
  intro ε hε
  by_cases htb0 : t = b
  · exact ⟨1, one_pos, fun u htu hub _ => by simp [htb0] at htu hub; linarith⟩
  have htb' : t < b := lt_of_le_of_ne htb htb0
  by_contra hbad
  push Not at hbad
  have hlow : ∀ u, t < u → u ≤ b → ε ≤ variationReal p X t u := by
    intro u htu hub
    obtain ⟨v, htv, hvb, _, hvε⟩ := hbad (u - t) (sub_pos.mpr htu)
    have _ := hvb
    exact hvε.trans (variationReal_mono (le_refl t) htv.le (by linarith : v ≤ u)
      (ne_top_of_le_ne_top hfin (pathVariationPower_mono ht hub p X)))
  have hiter : ∀ n : ℕ, ∀ u, t < u → u ≤ b →
      (7 / 4 : ℝ) ^ n * ε ≤ variationReal p X t u := by
    intro n
    induction n with
    | zero => simpa using hlow
    | succ n ih =>
      intro u hu hub
      have hpow : (7 / 4 : ℝ) ^ (n + 1) * ε = 7 / 4 * ((7 / 4) ^ n * ε) := by
        rw [pow_succ, mul_comm ((7 / 4) ^ n) (7 / 4), mul_assoc]
      rw [hpow]
      exact variation_right_boost hp X hX hfin ht htb'
        (mul_pos (pow_pos (by norm_num) n) hε) ih u hu hub
  have hvb : pathVariationPower p X t b ≠ ∞ :=
    ne_top_of_le_ne_top hfin (pathVariationPower_mono ht (le_refl b) p X)
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (variationReal p X t b / ε)
    (by norm_num : (1 : ℝ) < 7 / 4)
  have hlt : variationReal p X t b < (7 / 4 : ℝ) ^ n * ε := (div_lt_iff₀ hε).mp hn
  exact lt_irrefl _ (hlt.trans_le (hiter n b htb' le_rfl))

/-- Time reflection preserves real `p`-variation. -/
lemma variationReal_reflect {c d s t : ℝ} (p : ℝ) (X : ℝ → E) :
    variationReal p (timeReflect c d X) (c + d - t) (c + d - s) =
      variationReal p X s t := by
  simp [variationReal, pathVariationPower_reflect]

/-- Left variation vanishes at the diagonal by reflecting time. -/
lemma variation_left_vanish {a b p : ℝ} (hp : 1 ≤ p) (X : ℝ → E)
    (hX : ContinuousOn X (Set.Icc a b)) (hfin : pathVariationPower p X a b ≠ ∞)
    {t : ℝ} (ht : a ≤ t) (htb : t ≤ b) :
    ∀ ε > 0, ∃ δ > 0, ∀ s, a ≤ s → s < t → t - s < δ → variationReal p X s t < ε := by
  intro ε hε
  let Z : ℝ → E := timeReflect a b X
  have hZc : ContinuousOn Z (Set.Icc a b) := by
    refine hX.comp (continuous_const.sub continuous_id).continuousOn ?_
    intro u hu
    exact ⟨by linarith [hu.1, hu.2], by linarith [hu.1, hu.2]⟩
  have hZfin : pathVariationPower p Z a b ≠ ∞ := by
    have h := pathVariationPower_reflect (c := a) (d := b) (s := a) (t := b) p X
    rw [show a + b - b = a by ring, show a + b - a = b by ring] at h
    rwa [h]
  obtain ⟨δ, hδ, hδv⟩ := variation_right_vanish hp Z hZc hZfin
    (by linarith : a ≤ a + b - t) (by linarith : a + b - t ≤ b) ε hε
  refine ⟨δ, hδ, fun s hs hst hlen => ?_⟩
  have hrev := hδv (a + b - s) (by linarith) (by linarith) (by linarith)
  simpa [Z, variationReal_reflect] using hrev

/-- Head of an ordered partition, stopping at node `k`. -/
def prefixPart {s u : ℝ} (π : OrderedIntervalPartition s u) (k : ℕ) (hk : k ≤ π.size) :
    OrderedIntervalPartition s (nodeSeq π k) where
  size := k
  node := fun i => π.node ⟨i.val, by have := i.isLt; omega⟩
  monotone_node := fun i j hij =>
    π.monotone_node ((Fin.le_iff_val_le_val).mpr ((Fin.le_iff_val_le_val).mp hij))
  node_zero := by
    show π.node ⟨(0 : Fin (k + 1)).val, _⟩ = s
    simpa [Fin.val_zero] using π.node_zero
  node_last := by
    show π.node ⟨(Fin.last k).val, _⟩ = nodeSeq π k
    have hidx : (⟨(Fin.last k).val, by omega⟩ : Fin (π.size + 1)) = ⟨k, by omega⟩ := by
      ext; simp [Fin.val_last]
    rw [hidx, nodeSeq_of_le π hk]

/-- The head partition carries the first variation steps. -/
lemma variationSum_prefix (p : ℝ) (X : ℝ → E) {s u : ℝ} (π : OrderedIntervalPartition s u)
    {k : ℕ} (hk : k ≤ π.size) :
    variationSum p X (prefixPart π k hk) =
      ∑ i ∈ range k, ENNReal.ofReal (‖X (nodeSeq π (i + 1)) - X (nodeSeq π i)‖ ^ p) := by
  rw [variationSum_eq_stepSum]
  have hsize : (prefixPart π k hk).size = k := rfl
  simp only [hsize]
  refine sum_congr rfl fun i hi => ?_
  have hi0 : i ≤ k := le_of_lt (mem_range.mp hi)
  have hi1 : i + 1 ≤ k := Nat.succ_le_of_lt (mem_range.mp hi)
  have hL : nodeSeq (prefixPart π k hk) i = nodeSeq π i := by
    unfold nodeSeq prefixPart
    have hmin1 : min i k = i := Nat.min_eq_left hi0
    have hmin2 : min i π.size = i := Nat.min_eq_left (hi0.trans hk)
    simp [hmin1, hmin2]
  have hR : nodeSeq (prefixPart π k hk) (i + 1) = nodeSeq π (i + 1) := by
    unfold nodeSeq prefixPart
    have hmin1 : min (i + 1) k = i + 1 := Nat.min_eq_left hi1
    have hmin2 : min (i + 1) π.size = i + 1 := Nat.min_eq_left (hi1.trans hk)
    simp [hmin1, hmin2]
  simp [hL, hR]

/-- Variation across a nearby cut exceeds superadditivity by an arbitrary `ε`. -/
lemma variation_almost_subadd {a b p : ℝ} (hp : 1 ≤ p) (X : ℝ → E)
    (hX : ContinuousOn X (Set.Icc a b)) (hfin : pathVariationPower p X a b ≠ ∞) :
    ∀ ε > 0, ∃ δ > 0, ∀ s t u, a ≤ s → s ≤ t → t ≤ u → u ≤ b → u - t < δ →
      variationReal p X s u ≤ variationReal p X s t + variationReal p X t u + ε := by
  intro ε hε
  set M : ℝ := variationReal p X a b ^ p⁻¹
  have hM0 : 0 ≤ M := Real.rpow_nonneg (variationReal_nonneg p X a b) _
  have hφ : ContinuousAt (fun β : ℝ => (M + β) ^ p) 0 :=
    (continuousAt_const.add continuousAt_id).rpow_const (Or.inr (zero_le_one.trans hp))
  obtain ⟨ξ, hξ, hξclose⟩ := Metric.continuousAt_iff.mp hφ ε hε
  obtain ⟨δ, hδ, hδX⟩ := Metric.uniformContinuousOn_iff.mp
    (IsCompact.uniformContinuousOn_of_continuous isCompact_Icc hX) ξ hξ
  refine ⟨δ, hδ, fun s t u hs hst htu hub hlen => ?_⟩
  by_cases hge : u ≤ t
  · have hut : u = t := le_antisymm hge htu
    simp only [hut, variationReal_point (lt_of_lt_of_le zero_lt_one hp), add_zero]
    linarith [variationReal_nonneg p X s t]
  · have hltu : t < u := lt_of_not_ge hge
    set B : ℝ := variationReal p X s t + variationReal p X t u + ε
    have hB : 0 ≤ B := by linarith [variationReal_nonneg p X s t, variationReal_nonneg p X t u]
    have hfinu : pathVariationPower p X s u ≠ ∞ :=
      ne_top_of_le_ne_top hfin (pathVariationPower_mono hs hub p X)
    rw [variationReal]
    refine (ENNReal.le_ofReal_iff_toReal_le hfinu hB).mp ?_
    rw [pathVariationPower_eq_iSup]
    refine iSup_le fun π => ?_
    have hπfin : variationSum p X π ≠ ∞ := ne_top_of_le_ne_top hfinu (le_iSup _ π)
    obtain ⟨j, hjle, hgt, hmin⟩ := exists_least_index_gt π.size (nodeSeq π) t
      ⟨π.size, le_rfl, by simpa [nodeSeq_size] using hltu⟩
    have hj0 : 0 < j := by
      cases j with
      | zero => simp [nodeSeq_zero] at hgt; linarith
      | succ => omega
    have hLle : j - 1 ≤ π.size := by omega
    set nL : ℝ := nodeSeq π (j - 1)
    set nR : ℝ := nodeSeq π j
    have hsL : s ≤ nL := by
      simpa [nL, nodeSeq_zero] using monotone_nodeSeq π (Nat.zero_le (j - 1))
    have hnL : nL ≤ t := hmin (j - 1) (by omega)
    have hcross : ∑ i ∈ range j,
        ENNReal.ofReal (‖X (nodeSeq π (i + 1)) - X (nodeSeq π i)‖ ^ p) =
        variationSum p X (prefixPart π (j - 1) hLle) +
          ENNReal.ofReal (‖X nR - X nL‖ ^ p) := by
      conv_lhs => rw [show j = (j - 1) + 1 by omega]
      rw [sum_range_succ, variationSum_prefix]
      have hjj : (j - 1) + 1 = j := by omega
      simp [hjj, nL, nR]
    have htake := variationSum_take p X π hjle
    rw [hcross] at htake
    have hne3 := (ENNReal.add_ne_top).mp (htake.symm ▸ hπfin)
    have hpair := hne3.1
    have hsufin := hne3.2
    have hne2 := (ENNReal.add_ne_top).mp hpair
    have hprefin := hne2.1
    have hCfin := hne2.2
    have hto := ENNReal.toReal_add hpair hsufin
    rw [← htake, ENNReal.toReal_add hprefin hCfin] at hto
    have hCreal : (ENNReal.ofReal (‖X nR - X nL‖ ^ p)).toReal = ‖X nR - X nL‖ ^ p :=
      ENNReal.toReal_ofReal (Real.rpow_nonneg (norm_nonneg _) _)
    have hLreal : (variationSum p X (prefixPart π (j - 1) hLle)).toReal ≤
        variationReal p X s nL := by
      have hfinL : pathVariationPower p X s nL ≠ ∞ :=
        ne_top_of_le_ne_top hfin (pathVariationPower_mono hs (hnL.trans (htu.trans hub)) p X)
      exact ENNReal.toReal_mono hfinL (le_iSup (variationSum p X) _)
    have hRreal : (variationSum p X (suffixPart π j hjle)).toReal ≤ variationReal p X t u := by
      have hnRu : nR ≤ u := by simpa [nR, nodeSeq_size] using monotone_nodeSeq π hjle
      have hfinR : pathVariationPower p X nR u ≠ ∞ :=
        ne_top_of_le_ne_top hfin
          (pathVariationPower_mono (hs.trans (hst.trans hgt.le)) hub p X)
      have hle1 := ENNReal.toReal_mono hfinR (le_iSup (variationSum p X) (suffixPart π j hjle))
      exact hle1.trans (variationReal_mono hgt.le hnRu (le_refl u)
        (ne_top_of_le_ne_top hfin (pathVariationPower_mono (le_trans hs hst) hub p X)))
    have hαfin : pathVariationPower p X nL t ≠ ∞ :=
      ne_top_of_le_ne_top hfin (pathVariationPower_mono (hs.trans hsL) (htu.trans hub) p X)
    set α : ℝ := ‖X t - X nL‖
    set β : ℝ := ‖X nR - X t‖
    have hαM : α ≤ M := by
      have hle := norm_le_variationReal hnL (lt_of_lt_of_le zero_lt_one hp) hαfin
      have hv : variationReal p X nL t ≤ variationReal p X a b :=
        variationReal_mono (hs.trans hsL) hnL (htu.trans hub) hfin
      exact hle.trans (Real.rpow_le_rpow (variationReal_nonneg p X nL t) hv
        (inv_nonneg.mpr (zero_le_one.trans hp)))
    have hβ : β < ξ := by
      have hdist : dist nR t < δ := by
        rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hgt.le)]
        exact lt_of_le_of_lt (sub_le_sub_right
          (by simpa [nR, nodeSeq_size] using monotone_nodeSeq π hjle) t) hlen
      have hnRmem : nR ∈ Set.Icc a b :=
        ⟨hs.trans (hst.trans hgt.le), le_trans
          (by simpa [nR, nodeSeq_size] using monotone_nodeSeq π hjle) hub⟩
      have htmem : t ∈ Set.Icc a b := ⟨le_trans hs hst, htu.trans hub⟩
      simpa [β, dist_eq_norm] using hδX nR hnRmem t htmem hdist
    have hgap : (M + β) ^ p - M ^ p < ε := by
      have hdist : dist ((M + β) ^ p) ((M + 0) ^ p) < ε := hξclose <| by
        rw [Real.dist_eq]
        simp only [β, sub_zero]
        rw [abs_of_nonneg (norm_nonneg _)]
        exact hβ
      simp only [add_zero] at hdist
      have hmono : M ^ p ≤ (M + β) ^ p :=
        Real.rpow_le_rpow hM0 (by linarith [norm_nonneg (X nR - X t)]) (zero_le_one.trans hp)
      rwa [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hmono)] at hdist
    have hpow : ‖X nR - X nL‖ ^ p < α ^ p + ε := by
      have htri : ‖X nR - X nL‖ ≤ α + β := by
        have : X nR - X nL = (X t - X nL) + (X nR - X t) := by abel
        rw [this]
        simpa [α, β] using norm_add_le (X t - X nL) (X nR - X t)
      have hle := Real.rpow_le_rpow (norm_nonneg _) htri (zero_le_one.trans hp)
      have hinc := rpow_sub_le hp hM0 (norm_nonneg (X t - X nL)) hαM
        (norm_nonneg (X nR - X t))
      linarith [hinc, hgap, hle]
    have hαpow : α ^ p ≤ variationReal p X nL t := by
      simpa [α] using norm_increment_le hnL hαfin
    have hLtot : (variationSum p X (prefixPart π (j - 1) hLle)).toReal + α ^ p ≤
        variationReal p X s t := by
      linarith [hLreal, hαpow, variationReal_superadd hsL hnL
        (ne_top_of_le_ne_top hfin (pathVariationPower_mono hs (htu.trans hub) p X))]
    have htoB : (variationSum p X π).toReal < B := by
      rw [hto, hCreal]
      linarith [hRreal, hpow, hLtot]
    exact (ENNReal.le_ofReal_iff_toReal_le hπfin hB).mpr htoB.le

/-- Real variation from the left endpoint is continuous up to the right endpoint. -/
lemma continuousOn_variationReal {a b p : ℝ} (hp : 1 ≤ p) (X : ℝ → E)
    (hX : ContinuousOn X (Set.Icc a b)) (hfin : pathVariationPower p X a b ≠ ∞) :
    ContinuousOn (fun r => variationReal p X a r) (Set.Icc a b) := by
  intro t ht
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨δa, hδa, hsub⟩ := variation_almost_subadd hp X hX hfin (ε / 2) (half_pos hε)
  obtain ⟨δR, hδR, hR⟩ := variation_right_vanish hp X hX hfin ht.1 ht.2 (ε / 2) (half_pos hε)
  obtain ⟨δL, hδL, hL⟩ := variation_left_vanish hp X hX hfin ht.1 ht.2 (ε / 2) (half_pos hε)
  refine ⟨min δa (min δR δL), by positivity, fun r hr hdist => ?_⟩
  have habs : |r - t| < min δa (min δR δL) := by rwa [Real.dist_eq] at hdist
  by_cases heq : r = t
  · rw [heq, Real.dist_eq, sub_self, abs_zero]; exact hε
  · by_cases hrt : t < r
    · have hlen : r - t < δa := by
        rw [abs_of_nonneg (sub_nonneg.mpr hrt.le)] at habs
        exact habs.trans_le (min_le_left _ _)
      have hlenR : r - t < δR := by
        rw [abs_of_nonneg (sub_nonneg.mpr hrt.le)] at habs
        exact habs.trans_le (min_le_right _ _ |>.trans (min_le_left _ _))
      have hv := hR r hrt hr.2 hlenR
      have hsub' := hsub a t r (le_refl a) ht.1 hrt.le hr.2 hlen
      have hmono : variationReal p X a t ≤ variationReal p X a r :=
        variationReal_mono (le_refl a) ht.1 hrt.le
          (ne_top_of_le_ne_top hfin (pathVariationPower_mono (le_refl a) hr.2 p X))
      have hdiff : variationReal p X a r - variationReal p X a t < ε := by linarith
      simpa [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hmono)] using hdiff
    · have hrt' : r < t := lt_of_le_of_ne (not_lt.mp hrt) heq
      have hlen : t - r < δa := by
        rw [abs_of_nonpos (sub_nonpos.mpr hrt'.le), neg_sub] at habs
        exact habs.trans_le (min_le_left _ _)
      have hlenL : t - r < δL := by
        rw [abs_of_nonpos (sub_nonpos.mpr hrt'.le), neg_sub] at habs
        exact habs.trans_le ((min_le_right _ _).trans (min_le_right _ _))
      have hv := hL r hr.1 hrt' hlenL
      have hsub' := hsub a r t (le_refl a) hr.1 hrt'.le ht.2 hlen
      have hmono : variationReal p X a r ≤ variationReal p X a t :=
        variationReal_mono (le_refl a) hr.1 hrt'.le
          (ne_top_of_le_ne_top hfin (pathVariationPower_mono (le_refl a) ht.2 p X))
      have hdiff : variationReal p X a t - variationReal p X a r < ε := by linarith
      simpa [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hmono), abs_sub_comm] using hdiff

/-- Short intervals carry arbitrarily small `p`-variation. -/
lemma exists_variation_short {a b p : ℝ} (hp : 1 ≤ p) (X : ℝ → E)
    (hX : ContinuousOn X (Set.Icc a b)) (hfin : pathVariationPower p X a b ≠ ∞) :
    ∀ ε > 0, ∃ δ > 0, ∀ s t, a ≤ s → s ≤ t → t ≤ b → t - s < δ →
      variationReal p X s t < ε := by
  intro ε hε
  have huc := IsCompact.uniformContinuousOn_of_continuous isCompact_Icc
    (continuousOn_variationReal hp X hX hfin)
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ, hδg⟩ := huc ε hε
  refine ⟨δ, hδ, fun s t hs hst ht hlen => ?_⟩
  have hdist : dist t s < δ := by
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hst)]
    exact hlen
  have hclose := hδg t ⟨hs.trans hst, ht⟩ s ⟨hs, hst.trans ht⟩ hdist
  have hfin_at : pathVariationPower p X a t ≠ ∞ :=
    ne_top_of_le_ne_top hfin (pathVariationPower_mono (le_refl a) ht p X)
  have hmono : variationReal p X a s ≤ variationReal p X a t :=
    variationReal_mono (le_refl a) hs hst hfin_at
  have hsuper := variationReal_superadd hs hst hfin_at
  have hdiff : variationReal p X a t - variationReal p X a s < ε := by
    rwa [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hmono)] at hclose
  linarith

/-- Short intervals carry an arbitrarily small Young control. -/
lemma exists_ctrl_short {a b p q : ℝ} (hp : 1 ≤ p) (hq : 1 ≤ q) (hpq : 1 < p⁻¹ + q⁻¹)
    (X : ℝ → E) {G : Type*} [SeminormedAddCommGroup G] (Y : ℝ → G)
    (hX : ContinuousOn X (Set.Icc a b)) (hY : ContinuousOn Y (Set.Icc a b))
    (hXp : pathVariationPower p X a b ≠ ∞) (hYq : pathVariationPower q Y a b ≠ ∞) :
    ∀ η > 0, ∃ δ > 0, ∀ s t, a ≤ s → s ≤ t → t ≤ b → t - s < δ →
      youngCtrl p q X Y s t ≤ η := by
  intro η hη
  set ε : ℝ := min η 1
  have hε : 0 < ε := lt_min hη one_pos
  obtain ⟨δX, hδX, hvX⟩ := exists_variation_short hp X hX hXp ε hε
  obtain ⟨δY, hδY, hvY⟩ := exists_variation_short hq Y hY hYq ε hε
  refine ⟨min δX δY, lt_min hδX hδY, fun s t hs hst ht hlen => ?_⟩
  have hvx : variationReal p X s t ≤ ε :=
    le_of_lt (hvX s t hs hst ht (hlen.trans_le (min_le_left _ _)))
  have hvy : variationReal q Y s t ≤ ε :=
    le_of_lt (hvY s t hs hst ht (hlen.trans_le (min_le_right _ _)))
  have hα := youngAlpha_pos hp hpq
  have hβ := youngBeta_pos hq hpq
  have hx := Real.rpow_le_rpow (variationReal_nonneg p X s t) hvx hα.le
  have hy := Real.rpow_le_rpow (variationReal_nonneg q Y s t) hvy hβ.le
  have hmul := mul_le_mul hx hy (Real.rpow_nonneg (variationReal_nonneg q Y s t) _)
    (Real.rpow_nonneg (by linarith : 0 ≤ ε) _)
  have hpow : ε ^ youngAlpha p q * ε ^ youngBeta p q = ε := by
    rw [← Real.rpow_add hε, youngAlpha_add_beta hp hq hpq, Real.rpow_one]
  have hctrl : youngCtrl p q X Y s t ≤ ε := by simpa [youngCtrl, hpow] using hmul
  exact hctrl.trans (min_le_left _ _)

end YoungLoeve

end CKMA
