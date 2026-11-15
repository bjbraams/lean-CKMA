/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.RoughPath.Sewing.Dyadic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Dyadic sewing construction

Uniform grid approximations, general subinterval additivity, and convergence of ordered
partition sums for the dyadic sewing limit. The sewn primitive is additive, continuous on
the triangle, and approximated by every ordered partition at rate `mesh ^ (γ - 1)`.

## Main definitions

* `CKMA.Sewing.equalNode`, `CKMA.Sewing.equalSewn`: uniform grid nodes and uniform increment sums.
* `CKMA.Sewing.uniformPartition`: uniform ordered partition into `n` equal steps.

## Main results

* `CKMA.Sewing.sewnIncrement_add`: `sewnIncrement` is additive on every subinterval of `[a, b]`.
* `CKMA.Sewing.norm_partition_sub`: partition sums approach `sewnIncrement` at rate `mesh ^ (γ - 1)`.
* `CKMA.Sewing.partitionLimit_unique`: uniqueness of partition-sum limits.
-/

@[expose] public section

noncomputable section

namespace CKMA

open scoped BigOperators NNReal ENNReal

namespace Sewing

open Finset Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [CompleteSpace E] {a b γ C : ℝ}
variable {A : ℝ → ℝ → E}

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
      rw [Finset.sum_range_sub f π.size]
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
