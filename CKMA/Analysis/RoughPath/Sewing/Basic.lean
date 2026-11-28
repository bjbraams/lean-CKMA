/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Ordered partitions, sewing predicates and `p`-variation

Ordered finite partitions of `[a, b]`, which may repeat nodes and allow `a = b`, together with
their mesh and increment sums. On top of these are the predicates of the sewing lemma
(normalization, remainder bound, convergence of partition sums), the geometric sewing constant,
uniform partitions, the `p`th power variation of a path in `ℝ≥0∞`, and the left-point Young
increment `Y s (X t - X s)`. A few arithmetic facts about finite sums used by the sewing and
Young constructions are also here.

## Main definitions

* `CKMA.OrderedIntervalPartition`: an ordered finite partition of `[a, b]`, with
  `OrderedIntervalPartition.mesh` and `OrderedIntervalPartition.incrementSum`.
* `CKMA.PartitionSumsConverge`, `CKMA.IsLeftNormalized`, `CKMA.HasSewingRemainder`,
  `CKMA.HasPartitionSumLimit`, `CKMA.sewingTriangle`: the predicates of the sewing lemma.
* `CKMA.sewingConstant`: the geometric sewing constant `(1 - 2 ^ (1 - γ))⁻¹`.
* `CKMA.Sewing.equalNode`, `CKMA.Sewing.uniformPartition`: uniform nodes and partitions.
* `CKMA.variationSum`, `CKMA.pathVariationPower`, `CKMA.variationReal`: `p`th power variation
  along one partition, its supremum in `ℝ≥0∞`, and its real part.
* `CKMA.youngIncrement`: the left-point Young increment `Y s (X t - X s)`.

## Main results

* `CKMA.sewingConstant_pos`: the sewing constant is positive for `γ > 1`.
* `CKMA.Sewing.exists_mesh_lt`: every interval has partitions of arbitrarily small mesh.
* `CKMA.Sewing.partitionLimit_unique`: limits of partition sums are unique.
* `CKMA.IsLeftNormalized.eq_of_hasPartitionSumLimit`: uniqueness of sewn paths.
* `CKMA.exists_isLeftNormalized_sub_eq`: an additive increment field is the increment field of
  a left-normalized continuous path.
* `CKMA.partitionSumsConverge_of_norm_le`: a rate in the mesh gives convergence of partition
  sums.

## References

* [P. K. Friz and M. Hairer, *A Course on Rough Paths*][frizhairer2020]
-/

public section

noncomputable section

namespace CKMA

open scoped BigOperators NNReal ENNReal
open Finset

/-! ### Ordered partitions and the sewing predicates -/

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
@[expose]
def OrderedIntervalPartition.mesh {a b : ℝ} (π : OrderedIntervalPartition a b) : ℝ≥0 :=
  Finset.univ.sup (fun i : Fin π.size ↦ (π.node i.succ - π.node i.castSucc).toNNReal)

/-- Defining equation of `OrderedIntervalPartition.mesh`. -/
lemma OrderedIntervalPartition.mesh_def {a b : ℝ} (π : OrderedIntervalPartition a b) :
    π.mesh = Finset.univ.sup (fun i : Fin π.size ↦ (π.node i.succ - π.node i.castSucc).toNNReal) :=
  rfl

/-- Each step of a partition is at most its mesh. -/
lemma OrderedIntervalPartition.node_succ_sub_le_mesh {a b : ℝ} (π : OrderedIntervalPartition a b)
    (i : Fin π.size) : π.node i.succ - π.node i.castSucc ≤ π.mesh := by
  have h : (π.node i.succ - π.node i.castSucc).toNNReal ≤ π.mesh :=
    Finset.le_sup (f := fun i : Fin π.size ↦ (π.node i.succ - π.node i.castSucc).toNNReal)
      (Finset.mem_univ i)
  exact (Real.le_coe_toNNReal _).trans (by exact_mod_cast h)

/-- The sum of two-parameter increments along a partition. -/
@[expose]
def OrderedIntervalPartition.incrementSum {a b : ℝ} {E : Type*} [AddCommMonoid E]
    (π : OrderedIntervalPartition a b) (A : ℝ → ℝ → E) : E :=
  ∑ i : Fin π.size, A (π.node i.castSucc) (π.node i.succ)

/-- Defining equation of `OrderedIntervalPartition.incrementSum`. -/
lemma OrderedIntervalPartition.incrementSum_def {a b : ℝ} {E : Type*} [AddCommMonoid E]
    (π : OrderedIntervalPartition a b) (A : ℝ → ℝ → E) :
    π.incrementSum A = ∑ i : Fin π.size, A (π.node i.castSucc) (π.node i.succ) :=
  rfl

/-- Convergence of all ordered partition sums as their mesh tends to zero. -/
@[expose]
def PartitionSumsConverge {E : Type*} [NormedAddCommGroup E]
    (A : ℝ → ℝ → E) (a b : ℝ) (z : E) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ π : OrderedIntervalPartition a b,
    (π.mesh : ℝ) < δ → ‖π.incrementSum A - z‖ < ε

/-- Unfolding `PartitionSumsConverge`. -/
lemma partitionSumsConverge_iff {E : Type*} [NormedAddCommGroup E]
    (A : ℝ → ℝ → E) (a b : ℝ) (z : E) :
    PartitionSumsConverge A a b z ↔ ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ π : OrderedIntervalPartition a b, (π.mesh : ℝ) < δ → ‖π.incrementSum A - z‖ < ε :=
  Iff.rfl

/-- Geometric sewing constant, finite and positive for exponents strictly greater than one. -/
@[expose]
def sewingConstant (γ : ℝ) : ℝ := (1 - (2 : ℝ) ^ (1 - γ))⁻¹

/-- Defining equation of `sewingConstant`. -/
lemma sewingConstant_def (γ : ℝ) : sewingConstant γ = (1 - (2 : ℝ) ^ (1 - γ))⁻¹ := rfl

/-- The ratio `2 ^ (1 - γ)` lies in `[0, 1)` whenever `γ > 1`. -/
lemma sewingRatio_mem {γ : ℝ} (hγ : 1 < γ) :
    0 ≤ (2 : ℝ) ^ (1 - γ) ∧ (2 : ℝ) ^ (1 - γ) < 1 := by
  refine ⟨Real.rpow_nonneg (by norm_num) _, ?_⟩
  exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)

/-- The sewing constant is positive for exponents greater than one. -/
lemma sewingConstant_pos {γ : ℝ} (hγ : 1 < γ) : 0 < sewingConstant γ :=
  inv_pos.mpr (sub_pos.mpr (sewingRatio_mem hγ).2)

/-- A continuous interval path is normalized at the left endpoint. -/
@[expose]
def IsLeftNormalized {E : Type*} [TopologicalSpace E] [Zero E] {a b : ℝ}
    (I : C(Set.Icc a b, E)) : Prop := ∀ x : Set.Icc a b, x.val = a → I x = 0

/-- Unfolding `IsLeftNormalized`. -/
lemma isLeftNormalized_iff {E : Type*} [TopologicalSpace E] [Zero E] {a b : ℝ}
    (I : C(Set.Icc a b, E)) : IsLeftNormalized I ↔ ∀ x : Set.Icc a b, x.val = a → I x = 0 :=
  Iff.rfl

/-- A path's additive increments approximate a given increment field to order `γ`. -/
@[expose]
def HasSewingRemainder {E : Type*} [NormedAddCommGroup E] {a b : ℝ}
    (A : ℝ → ℝ → E) (I : C(Set.Icc a b, E)) (γ C : ℝ) : Prop :=
  ∀ s t : Set.Icc a b, s.val ≤ t.val →
    ‖(I t - I s) - A s.val t.val‖ ≤ C * |t.val - s.val| ^ γ

/-- Unfolding `HasSewingRemainder`. -/
lemma hasSewingRemainder_iff {E : Type*} [NormedAddCommGroup E] {a b : ℝ}
    (A : ℝ → ℝ → E) (I : C(Set.Icc a b, E)) (γ C : ℝ) :
    HasSewingRemainder A I γ C ↔ ∀ s t : Set.Icc a b, s.val ≤ t.val →
      ‖(I t - I s) - A s.val t.val‖ ≤ C * |t.val - s.val| ^ γ :=
  Iff.rfl

/-- The path's increments are limits of all partition sums on each subinterval. -/
@[expose]
def HasPartitionSumLimit {E : Type*} [NormedAddCommGroup E] {a b : ℝ}
    (A : ℝ → ℝ → E) (I : C(Set.Icc a b, E)) : Prop :=
  ∀ s t : Set.Icc a b, s.val ≤ t.val → PartitionSumsConverge A s.val t.val (I t - I s)

/-- Unfolding `HasPartitionSumLimit`. -/
lemma hasPartitionSumLimit_iff {E : Type*} [NormedAddCommGroup E] {a b : ℝ}
    (A : ℝ → ℝ → E) (I : C(Set.Icc a b, E)) :
    HasPartitionSumLimit A I ↔
      ∀ s t : Set.Icc a b, s.val ≤ t.val → PartitionSumsConverge A s.val t.val (I t - I s) :=
  Iff.rfl

/-- Closed triangle `a ≤ s ≤ t ≤ b` on which an increment field is sewn. -/
@[expose]
def sewingTriangle (a b : ℝ) : Set (ℝ × ℝ) :=
  {p | a ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ b}

/-- Membership in `sewingTriangle`. -/
@[simp]
lemma mem_sewingTriangle {a b : ℝ} {p : ℝ × ℝ} :
    p ∈ sewingTriangle a b ↔ a ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ b :=
  Iff.rfl

/-! ### Uniform partitions -/

namespace Sewing

/-- Node of the uniform `k`-partition of `[s, t]`. -/
@[expose]
def equalNode (s t : ℝ) (k i : ℕ) : ℝ :=
  s + (t - s) * ((i : ℝ) / (k : ℝ))

/-- Defining equation of `equalNode`. -/
lemma equalNode_def (s t : ℝ) (k i : ℕ) : equalNode s t k i = s + (t - s) * ((i : ℝ) / (k : ℝ)) :=
  rfl

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

/-- Each uniform node depends continuously on the interval endpoints. -/
lemma continuous_equalNode (k i : ℕ) :
    Continuous (fun z : ℝ × ℝ => equalNode z.1 z.2 k i) := by
  unfold equalNode
  exact continuous_fst.add ((continuous_snd.sub continuous_fst).mul continuous_const)

/-- Uniform nodes of a point of `sewingTriangle a b` lie in `[a, b]`. -/
lemma mapsTo_equalNode {a b : ℝ} {k i : ℕ} (hk : 0 < k) (hi : i ≤ k) :
    Set.MapsTo (fun z : ℝ × ℝ => equalNode z.1 z.2 k i) (sewingTriangle a b) (Set.Icc a b) := by
  intro z hp
  have hmem := equalNode_mem hp.2.1 hk hi
  exact ⟨le_trans hp.1 hmem.1, le_trans hmem.2 hp.2.2⟩

/-- Uniform partition into `n` equal steps. -/
@[expose]
def uniformPartition {s t : ℝ} (hst : s ≤ t) (n : ℕ) (hn : 0 < n) :
    OrderedIntervalPartition s t where
  size := n
  node := fun i => equalNode s t n (i : ℕ)
  monotone_node := fun i j hij =>
    equalNode_mono hst n (Fin.le_iff_val_le_val.mp hij)
  node_zero := by simp [equalNode_zero]
  node_last := by simpa [Fin.val_last] using equalNode_last s t hn

/-- The size of `uniformPartition`. -/
@[simp]
lemma uniformPartition_size {s t : ℝ} (hst : s ≤ t) (n : ℕ) (hn : 0 < n) :
    (uniformPartition hst n hn).size = n :=
  rfl

/-- The nodes of `uniformPartition`. -/
@[simp]
lemma uniformPartition_node {s t : ℝ} (hst : s ≤ t) (n : ℕ) (hn : 0 < n)
    (i : Fin ((uniformPartition hst n hn).size + 1)) :
    (uniformPartition hst n hn).node i = equalNode s t n i :=
  rfl

/-- The mesh of a uniform partition is the common step length. -/
lemma mesh_uniformPartition {s t : ℝ} (hst : s ≤ t) {n : ℕ} (hn : 0 < n) :
    ((uniformPartition hst n hn).mesh : ℝ) = (t - s) / n := by
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have hsup : (uniformPartition hst n hn).mesh = Real.toNNReal ((t - s) / (n : ℝ)) := by
    rw [OrderedIntervalPartition.mesh_def]
    refine Eq.trans (Finset.sup_congr rfl fun i _ => ?_) (Finset.sup_const (α := ℝ≥0) hne _)
    simp only [uniformPartition_node, Fin.val_succ, Fin.val_castSucc]
    rw [equalNode_sub]
  rw [hsup, Real.coe_toNNReal', max_eq_left (div_nonneg (sub_nonneg.mpr hst) (Nat.cast_nonneg _))]

/-- Every positive width is realized by some ordered partition. -/
lemma exists_mesh_lt {s t : ℝ} (hst : s ≤ t) {δ : ℝ} (hδ : 0 < δ) :
    ∃ π : OrderedIntervalPartition s t, (π.mesh : ℝ) < δ := by
  let n := Nat.floor ((t - s) / δ) + 1
  have hn : 0 < n := Nat.succ_pos _
  refine ⟨uniformPartition hst n hn, ?_⟩
  rw [mesh_uniformPartition hst hn]
  have hden : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  rw [div_lt_iff₀ hden]
  have hfloor : (t - s) / δ < n := by
    simpa [n, Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one ((t - s) / δ)
  calc
    t - s = ((t - s) / δ) * δ := by field_simp
    _ < (n : ℝ) * δ := mul_lt_mul_of_pos_right hfloor hδ
    _ = δ * n := by ring

/-- Two partition-sum limits on the same interval agree. -/
lemma partitionLimit_unique {E : Type*} [NormedAddCommGroup E] {A : ℝ → ℝ → E} {s t : ℝ}
    (hst : s ≤ t) {z₁ z₂ : E}
    (h₁ : PartitionSumsConverge A s t z₁) (h₂ : PartitionSumsConverge A s t z₂) :
    z₁ = z₂ := by
  by_contra hne
  have hpos : 0 < ‖z₁ - z₂‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  obtain ⟨δ₁, hδ₁, hclose₁⟩ := h₁ (‖z₁ - z₂‖ / 2) (half_pos hpos)
  obtain ⟨δ₂, hδ₂, hclose₂⟩ := h₂ (‖z₁ - z₂‖ / 2) (half_pos hpos)
  obtain ⟨π, hmesh⟩ := exists_mesh_lt hst (lt_min hδ₁ hδ₂)
  have h1 := hclose₁ π (lt_of_lt_of_le hmesh (min_le_left _ _))
  have h2 := hclose₂ π (lt_of_lt_of_le hmesh (min_le_right _ _))
  have hle : ‖z₁ - z₂‖ ≤ ‖π.incrementSum A - z₁‖ + ‖π.incrementSum A - z₂‖ := by
    rw [norm_sub_rev (π.incrementSum A) z₁]
    exact norm_sub_le_norm_sub_add_norm_sub _ _ _
  linarith

end Sewing

/-! ### Existence and uniqueness of sewn paths -/

/-- Two left-normalized paths whose increments are limits of the same partition sums agree. -/
lemma IsLeftNormalized.eq_of_hasPartitionSumLimit {E : Type*} [NormedAddCommGroup E] {a b : ℝ}
    {A : ℝ → ℝ → E} {I J : C(Set.Icc a b, E)} (hI : IsLeftNormalized I)
    (hJ : IsLeftNormalized J) (hIA : HasPartitionSumLimit A I) (hJA : HasPartitionSumLimit A J) :
    I = J := by
  ext x
  let a0 : Set.Icc a b := ⟨a, le_rfl, x.2.1.trans x.2.2⟩
  have hEq := Sewing.partitionLimit_unique x.2.1 (hIA a0 x x.2.1) (hJA a0 x x.2.1)
  simpa [hI a0 rfl, hJ a0 rfl] using hEq

/-- An additive increment field `Z`, continuous on `sewingTriangle a b`, is the increment field
of a left-normalized continuous path, namely `x ↦ Z a x`. -/
lemma exists_isLeftNormalized_sub_eq {E : Type*} [NormedAddCommGroup E] {a b : ℝ} (hab : a ≤ b)
    (Z : ℝ → ℝ → E) (hcont : ContinuousOn (fun p : ℝ × ℝ => Z p.1 p.2) (sewingTriangle a b))
    (hadd : ∀ s u t : ℝ, a ≤ s → s ≤ u → u ≤ t → t ≤ b → Z s t = Z s u + Z u t) :
    ∃ I : C(Set.Icc a b, E), IsLeftNormalized I ∧
      ∀ s t : Set.Icc a b, s.val ≤ t.val → I t - I s = Z s.val t.val := by
  refine ⟨⟨fun x => Z a x.val, hcont.comp_continuous
      (continuous_const.prodMk continuous_subtype_val) fun x => ⟨le_rfl, x.2.1, x.2.2⟩⟩,
    fun x hx => ?_, fun s t hst => ?_⟩
  · have h := hadd a a a le_rfl le_rfl le_rfl hab
    simp only [ContinuousMap.coe_mk, hx]
    simpa using h
  · simp only [ContinuousMap.coe_mk]
    rw [hadd a s.val t.val le_rfl s.2.1 hst t.2.2]
    abel

/-- A rate `K · mesh ^ (γ - 1)` with `γ > 1` for the partition sums gives their convergence. -/
lemma partitionSumsConverge_of_norm_le {E : Type*} [NormedAddCommGroup E] {A : ℝ → ℝ → E}
    {s t K γ : ℝ} {z : E} (hγ : 1 < γ) (hK : 0 ≤ K)
    (h : ∀ π : OrderedIntervalPartition s t,
      ‖π.incrementSum A - z‖ ≤ K * (π.mesh : ℝ) ^ (γ - 1)) :
    PartitionSumsConverge A s t z := by
  intro ε hε
  have hγ1 : 0 < γ - 1 := sub_pos.mpr hγ
  have hK1 : 0 < K + 1 := by linarith
  refine ⟨(ε / (K + 1)) ^ (γ - 1)⁻¹, Real.rpow_pos_of_pos (div_pos hε hK1) _,
    fun π hmesh => ?_⟩
  have hm : 0 ≤ (π.mesh : ℝ) ^ (γ - 1) := Real.rpow_nonneg (NNReal.coe_nonneg _) _
  have hpow : (π.mesh : ℝ) ^ (γ - 1) < ε / (K + 1) := by
    have := Real.rpow_lt_rpow (NNReal.coe_nonneg _) hmesh hγ1
    rwa [← Real.rpow_mul (div_pos hε hK1).le, inv_mul_cancel₀ hγ1.ne', Real.rpow_one] at this
  calc
    ‖π.incrementSum A - z‖ ≤ K * (π.mesh : ℝ) ^ (γ - 1) := h π
    _ ≤ (K + 1) * (π.mesh : ℝ) ^ (γ - 1) := by nlinarith
    _ < (K + 1) * (ε / (K + 1)) := mul_lt_mul_of_pos_left hpow hK1
    _ = ε := by field_simp

/-! ### `p`th power variation -/

section Variation

variable {E : Type*} [SeminormedAddCommGroup E]

/-- Sum of `p`th powers of increments along one ordered partition. -/
@[expose]
def variationSum (p : ℝ) (X : ℝ → E) {a b : ℝ}
    (π : OrderedIntervalPartition a b) : ℝ≥0∞ :=
  ∑ i : Fin π.size, ENNReal.ofReal (‖X (π.node i.succ) - X (π.node i.castSucc)‖ ^ p)

/-- Defining equation of `variationSum`. -/
lemma variationSum_def (p : ℝ) (X : ℝ → E) {a b : ℝ} (π : OrderedIntervalPartition a b) :
    variationSum p X π =
      ∑ i : Fin π.size, ENNReal.ofReal (‖X (π.node i.succ) - X (π.node i.castSucc)‖ ^ p) :=
  rfl

/-- The `p`th power variation, retaining infinite variation: the supremum of `variationSum`
over ordered partitions. -/
@[expose]
def pathVariationPower (p : ℝ) (X : ℝ → E) (a b : ℝ) : ℝ≥0∞ :=
  ⨆ π : OrderedIntervalPartition a b, variationSum p X π

/-- The `p`th power variation is the supremum of `variationSum` over ordered partitions. -/
lemma pathVariationPower_eq_iSup (p : ℝ) (X : ℝ → E) (a b : ℝ) :
    pathVariationPower p X a b = ⨆ π : OrderedIntervalPartition a b, variationSum p X π := rfl

/-- Each partition sum is at most the `p`th power variation. -/
lemma variationSum_le_pathVariationPower (p : ℝ) (X : ℝ → E) {a b : ℝ}
    (π : OrderedIntervalPartition a b) : variationSum p X π ≤ pathVariationPower p X a b :=
  le_iSup (variationSum p X) π

/-- Real `p`-variation power on a subinterval, or zero when the power is infinite. -/
@[expose]
def variationReal (p : ℝ) (X : ℝ → E) (s t : ℝ) : ℝ :=
  (pathVariationPower p X s t).toReal

/-- Defining equation of `variationReal`. -/
lemma variationReal_def (p : ℝ) (X : ℝ → E) (s t : ℝ) :
    variationReal p X s t = (pathVariationPower p X s t).toReal :=
  rfl

/-- Real variation is nonnegative. -/
lemma variationReal_nonneg (p : ℝ) (X : ℝ → E) (s t : ℝ) : 0 ≤ variationReal p X s t :=
  ENNReal.toReal_nonneg

end Variation

/-! ### Young increments -/

/-- The field of left-point Young increments `Y s (X t - X s)` of the integrand `Y`, an
operator-valued path, against the integrator `X`. -/
@[expose]
def youngIncrement {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (X : ℝ → E) (Y : ℝ → E →L[ℝ] F) (s t : ℝ) : F :=
  Y s (X t - X s)

/-- Defining equation of `youngIncrement`. -/
lemma youngIncrement_apply {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (X : ℝ → E) (Y : ℝ → E →L[ℝ] F) (s t : ℝ) :
    youngIncrement X Y s t = Y s (X t - X s) :=
  rfl

/-! ### Arithmetic of finite sums -/

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

/-- `n · (L / n) ^ γ = L ^ γ · n ^ (1 - γ)` for positive integers. -/
lemma nat_mul_div_rpow {n : ℕ} (hn : 0 < n) {L γ : ℝ} (hL : 0 ≤ L) (hγ : γ ≠ 0) :
    (n : ℝ) * (L / (n : ℝ)) ^ γ = L ^ γ * (n : ℝ) ^ (1 - γ) := by
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  rcases hL.eq_or_lt with rfl | hL
  · simp [zero_div, Real.zero_rpow hγ, mul_zero, zero_mul]
  · rw [Real.div_rpow hL.le (Nat.cast_nonneg n), Real.rpow_sub hn0, Real.rpow_one]
    ring

/-- A sum of terms all larger than `c` over a nonempty set exceeds `card • c`. -/
lemma sum_gt_card_mul {s : Finset ℕ} {f : ℕ → ℝ} {c : ℝ} (hf : ∀ i ∈ s, c < f i)
    (hne : s.Nonempty) : (s.card : ℝ) * c < ∑ i ∈ s, f i := by
  simpa [Finset.sum_const, nsmul_eq_mul] using Finset.sum_lt_sum_of_nonempty hne hf

/-- Least index at which a sequence exceeds a threshold. -/
lemma exists_least_index_gt (n : ℕ) (c : ℕ → ℝ) (t : ℝ) (h : ∃ i ≤ n, t < c i) :
    ∃ i ≤ n, t < c i ∧ ∀ j < i, c j ≤ t := by
  classical
  have hex : ∃ i, i ≤ n ∧ t < c i := by
    obtain ⟨i, hi, hlt⟩ := h
    exact ⟨i, hi, hlt⟩
  obtain ⟨hle, hlt⟩ := Nat.find_spec hex
  exact ⟨Nat.find hex, hle, hlt, fun j hj => not_lt.mp fun hcj =>
    Nat.find_min hex hj ⟨hj.le.trans hle, hcj⟩⟩

end CKMA
