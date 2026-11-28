/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic

import CKMA.Analysis.Nonlinear.FixedPoint
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Convex
import Mathlib.Analysis.LocallyConvex.WeakSpace
import TauCeti.Analysis.Convex.Uniform.Basic
import TauCeti.Analysis.Normed.Module.Dual.Reflexive.WeakCompact

/-!
# Monotone graphs and resolvents in Hilbert space

Monotonicity of a graph `A ⊆ H × H` gives single-valued resolvent fibers at nonnegative scales.
Minty's theorem characterizes maximal monotonicity by nonemptiness of every resolvent fiber at
a positive scale: the finite-intersection property of the slices
`{y | 0 ≤ ⟪y - v, x - y - a u⟫}`, `(v, u) ∈ A`, comes from the Brouwer simplex lemma
`CKMA.exists_forall_nonneg_of_sum_mul_nonneg`, and the slices are closed balls, hence weakly
compact. The normal cone includes its base-point constraint. Source: GAPS 35.32.

## Main definitions

* `CKMA.IsMonotoneGraph`: Monotonicity of a Hilbert-space graph.
* `CKMA.IsMaximalMonotoneGraph`: Maximal monotonicity of a Hilbert-space graph.
* `CKMA.monotoneResolventFiber`: Resolvent fiber `{y | ∃ u, (y, u) ∈ A ∧ x = y + a • u}`.
* `CKMA.normalConeGraph`: Normal-cone graph of a set.

## Main results

* `CKMA.IsMonotoneGraph.resolventFiber_subsingleton`: Uniqueness of the resolvent at nonnegative
  scale.
* `CKMA.isMaximalMonotoneGraph_iff_range`: Minty's characterization of maximal monotone graphs
  (**35.32**).
* `CKMA.IsMaximalMonotoneGraph.existsUnique_resolvent`: Existence and uniqueness of the resolvent
  at positive scale.
* `CKMA.isMonotoneGraph_normalConeGraph`: the normal-cone graph of any set is monotone.
-/

public section

noncomputable section

namespace CKMA

open Filter Topology Bornology
open scoped InnerProductSpace

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Monotonicity of a Hilbert-space graph. -/
@[expose]
def IsMonotoneGraph (A : Set (H × H)) : Prop :=
  ∀ p ∈ A, ∀ q ∈ A, 0 ≤ ⟪p.1 - q.1, p.2 - q.2⟫_ℝ

/-- A monotone graph is maximal when it has no proper monotone enlargement. -/
@[expose]
def IsMaximalMonotoneGraph (A : Set (H × H)) : Prop :=
  IsMonotoneGraph A ∧ ∀ B, IsMonotoneGraph B → A ⊆ B → B ⊆ A

/-- A resolvent fiber: `y` belongs when `x ∈ y + a A(y)`. -/
@[expose]
def monotoneResolventFiber (A : Set (H × H)) (a : ℝ) (x : H) : Set H :=
  {y | ∃ u, (y, u) ∈ A ∧ x = y + a • u}

/-- Defining property of `IsMonotoneGraph`. -/
theorem isMonotoneGraph_iff {A : Set (H × H)} :
    IsMonotoneGraph A ↔ ∀ p ∈ A, ∀ q ∈ A, 0 ≤ ⟪p.1 - q.1, p.2 - q.2⟫_ℝ := Iff.rfl

/-- Defining property of `IsMaximalMonotoneGraph`. -/
theorem isMaximalMonotoneGraph_iff {A : Set (H × H)} :
    IsMaximalMonotoneGraph A ↔
      IsMonotoneGraph A ∧ ∀ B, IsMonotoneGraph B → A ⊆ B → B ⊆ A := Iff.rfl

/-- Membership in a resolvent fiber. -/
theorem mem_monotoneResolventFiber {A : Set (H × H)} {a : ℝ} {x y : H} :
    y ∈ monotoneResolventFiber A a x ↔ ∃ u, (y, u) ∈ A ∧ x = y + a • u := Iff.rfl

/-- A subset of a monotone graph is monotone. -/
theorem IsMonotoneGraph.mono {A B : Set (H × H)} (hB : IsMonotoneGraph B) (hAB : A ⊆ B) :
    IsMonotoneGraph A :=
  fun p hp q hq ↦ hB p (hAB hp) q (hAB hq)

/-- A maximal monotone graph is monotone. -/
theorem IsMaximalMonotoneGraph.isMonotoneGraph {A : Set (H × H)}
    (hA : IsMaximalMonotoneGraph A) : IsMonotoneGraph A :=
  hA.1

/-- A monotone enlargement of a maximal monotone graph is contained in it. -/
theorem IsMaximalMonotoneGraph.subset_of_isMonotoneGraph {A B : Set (H × H)}
    (hA : IsMaximalMonotoneGraph A) (hB : IsMonotoneGraph B) (hAB : A ⊆ B) : B ⊆ A :=
  hA.2 B hB hAB

/-- Monotonicity alone makes a nonnegative-scale resolvent fiber single-valued. -/
theorem IsMonotoneGraph.resolventFiber_subsingleton {A : Set (H × H)}
    (hA : IsMonotoneGraph A) {a : ℝ} (ha : 0 ≤ a) (x : H) :
    (monotoneResolventFiber A a x).Subsingleton := by
  intro y hy z hz
  obtain ⟨u, hu, hxu⟩ := hy
  obtain ⟨v, hv, hxv⟩ := hz
  have hlinear : a • (u - v) = z - y := by
    calc
      a • (u - v) = (y + a • u) - (z + a • v) - (y - z) := by module
      _ = z - y := by rw [← hxu, ← hxv]; abel
  have hmon := hA (y, u) hu (z, v) hv
  have hscaled : 0 ≤ ⟪y - z, a • (u - v)⟫_ℝ := by
    simpa only [inner_smul_right, smul_eq_mul] using mul_nonneg ha hmon
  rw [hlinear] at hscaled
  have hneg : ⟪y - z, z - y⟫_ℝ = -(‖y - z‖ ^ 2) := by
    rw [show z - y = -(y - z) by abel, inner_neg_right, real_inner_self_eq_norm_sq]
  rw [hneg] at hscaled
  have hnorm : ‖y - z‖ = 0 := by nlinarith [sq_nonneg ‖y - z‖]
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

/-- A pair that is monotone against every pair of a maximal monotone graph already belongs to it. -/
private theorem IsMaximalMonotoneGraph.mem_of_monotone_with {A : Set (H × H)}
    (hA : IsMaximalMonotoneGraph A) {y u : H}
    (hmono : ∀ p ∈ A, 0 ≤ ⟪y - p.1, u - p.2⟫_ℝ) : (y, u) ∈ A := by
  let B := A ∪ {(y, u)}
  have hB : IsMonotoneGraph B := by
    intro p hp q hq
    rcases hp with hp | hp
    · rcases hq with hq | hq
      · exact hA.1 p hp q hq
      · rw [Set.mem_singleton_iff.mp hq]
        have hswap : ⟪p.1 - y, p.2 - u⟫_ℝ = ⟪y - p.1, u - p.2⟫_ℝ := by
          rw [show p.1 - y = -(y - p.1) by abel, show p.2 - u = -(u - p.2) by abel,
            inner_neg_left, inner_neg_right, neg_neg]
        rw [hswap]
        exact hmono p hp
    · rw [Set.mem_singleton_iff.mp hp]
      rcases hq with hq | hq
      · exact hmono q hq
      · rw [Set.mem_singleton_iff.mp hq]
        simp
  exact hA.2 B hB Set.subset_union_left (Set.mem_union_right _ rfl)

/-- Pairwise real inner products rearrange into a sum against the weight barycenter. -/
private theorem sum_pair_inner_eq {n : ℕ} (w : Fin n → ℝ) (v u : Fin n → H)
    (hw : ∑ i, w i = 1) :
    ∑ i, ∑ j, w i * w j * ⟪v i - v j, u i - u j⟫_ℝ =
      2 * ∑ i, w i * ⟪v i - ∑ k, w k • v k, u i⟫_ℝ := by
  have hexpand (i j : Fin n) : ⟪v i - v j, u i - u j⟫_ℝ =
      ⟪v i, u i⟫_ℝ - ⟪v i, u j⟫_ℝ - ⟪v j, u i⟫_ℝ + ⟪v j, u j⟫_ℝ := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right]
    abel
  have hterm (i j : Fin n) : w i * w j * ⟪v i - v j, u i - u j⟫_ℝ =
      w i * w j * ⟪v i, u i⟫_ℝ - w i * w j * ⟪v i, u j⟫_ℝ -
        w i * w j * ⟪v j, u i⟫_ℝ + w i * w j * ⟪v j, u j⟫_ℝ := by
    rw [hexpand]
    ring
  have hsplit : ∑ i, ∑ j, w i * w j * ⟪v i - v j, u i - u j⟫_ℝ =
      ∑ i, ∑ j, w i * w j * ⟪v i, u i⟫_ℝ -
        ∑ i, ∑ j, w i * w j * ⟪v i, u j⟫_ℝ -
        ∑ i, ∑ j, w i * w j * ⟪v j, u i⟫_ℝ +
        ∑ i, ∑ j, w i * w j * ⟪v j, u j⟫_ℝ := by
    have hrew :
        ∑ i, ∑ j, w i * w j * ⟪v i - v j, u i - u j⟫_ℝ =
          ∑ i, ∑ j,
            (w i * w j * ⟪v i, u i⟫_ℝ - w i * w j * ⟪v i, u j⟫_ℝ -
              w i * w j * ⟪v j, u i⟫_ℝ + w i * w j * ⟪v j, u j⟫_ℝ) := by
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      exact hterm i j
    rw [hrew]
    have hinner (i : Fin n) :
        ∑ j, (w i * w j * ⟪v i, u i⟫_ℝ - w i * w j * ⟪v i, u j⟫_ℝ -
            w i * w j * ⟪v j, u i⟫_ℝ + w i * w j * ⟪v j, u j⟫_ℝ) =
          ∑ j, w i * w j * ⟪v i, u i⟫_ℝ - ∑ j, w i * w j * ⟪v i, u j⟫_ℝ -
            ∑ j, w i * w j * ⟪v j, u i⟫_ℝ + ∑ j, w i * w j * ⟪v j, u j⟫_ℝ := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    simp_rw [hinner]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have h11 : ∑ i, ∑ j, w i * w j * ⟪v i, u i⟫_ℝ = ∑ i, w i * ⟪v i, u i⟫_ℝ := by
    simp_rw [show ∀ i j, w i * w j * ⟪v i, u i⟫_ℝ = (w i * ⟪v i, u i⟫_ℝ) * w j by
      intros; ring, ← Finset.mul_sum, hw, mul_one]
  have h22 : ∑ i, ∑ j, w i * w j * ⟪v j, u j⟫_ℝ = ∑ i, w i * ⟪v i, u i⟫_ℝ := by
    rw [Finset.sum_comm]
    simp_rw [show ∀ i j, w i * w j * ⟪v j, u j⟫_ℝ = (w j * ⟪v j, u j⟫_ℝ) * w i by
      intros; ring, ← Finset.mul_sum, hw, mul_one]
  have hcross : ∑ i, ∑ j, w i * w j * ⟪v i, u j⟫_ℝ =
      ⟪∑ i, w i • v i, ∑ j, w j • u j⟫_ℝ := by
    symm
    rw [sum_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [real_inner_smul_left, inner_smul_right]
    ring
  have hcross' : ∑ i, ∑ j, w i * w j * ⟪v j, u i⟫_ℝ =
      ∑ i, ∑ j, w i * w j * ⟪v i, u j⟫_ℝ := by
    rw [Finset.sum_comm]
    simp_rw [mul_comm (w _) (w _)]
  have hdot : ⟪∑ i, w i • v i, ∑ j, w j • u j⟫_ℝ =
      ∑ i, w i * ⟪∑ k, w k • v k, u i⟫_ℝ := by
    rw [inner_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_smul_right]
  have hdiff : ∑ i, w i * ⟪v i, u i⟫_ℝ - ∑ i, w i * ⟪∑ k, w k • v k, u i⟫_ℝ =
      ∑ i, w i * ⟪v i - ∑ k, w k • v k, u i⟫_ℝ := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← mul_sub, inner_sub_left]
  rw [hsplit, h11, h22, hcross', hcross, hdot]
  have htwo : ∑ i, w i * ⟪v i, u i⟫_ℝ - ∑ i, w i * ⟪∑ k, w k • v k, u i⟫_ℝ -
      ∑ i, w i * ⟪∑ k, w k • v k, u i⟫_ℝ + ∑ i, w i * ⟪v i, u i⟫_ℝ =
      2 * (∑ i, w i * ⟪v i, u i⟫_ℝ - ∑ i, w i * ⟪∑ k, w k • v k, u i⟫_ℝ) := by
    ring
  rw [htwo, hdiff]

/-- The inequality `0 ≤ ⟪y - v, c - y⟫` cuts out the closed ball with diameter from `v` to `c`. -/
private theorem inner_nonneg_iff_mem_closedBall {v c y : H} :
    0 ≤ ⟪y - v, c - y⟫_ℝ ↔
      y ∈ Metric.closedBall ((2⁻¹ : ℝ) • (v + c)) (‖c - v‖ / 2) := by
  rw [mem_closedBall_iff_norm]
  have hm : y - (2⁻¹ : ℝ) • (v + c) = (y - v) - (2⁻¹ : ℝ) • (c - v) := by
    module
  rw [hm]
  have hrad : 0 ≤ ‖c - v‖ / 2 := div_nonneg (norm_nonneg _) zero_le_two
  rw [← sq_le_sq₀ (norm_nonneg _) hrad]
  have hexpand : ‖(y - v) - (2⁻¹ : ℝ) • (c - v)‖ ^ 2 =
      ‖y - v‖ ^ 2 - ⟪y - v, c - v⟫_ℝ + ‖c - v‖ ^ 2 / 4 := by
    rw [norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr zero_le_two)]
    ring
  have hinner : ⟪y - v, c - y⟫_ℝ = ⟪y - v, c - v⟫_ℝ - ‖y - v‖ ^ 2 := by
    rw [show c - y = (c - v) - (y - v) by abel, inner_sub_right, real_inner_self_eq_norm_sq]
  constructor
  · intro hle
    nlinarith [hexpand, hinner, hle]
  · intro hle
    nlinarith [hexpand, hinner, hle]

/-- For convex weights `w` and points `p i` of a monotone graph, the weighted gaps at the
barycenter `b = ∑ k, w k • (p k).1` are nonnegative on average when `0 ≤ a`:
`0 ≤ ∑ i, w i * ⟪b - (p i).1, x - b - a • (p i).2⟫`. -/
private theorem sum_mul_inner_barycenter_nonneg {A : Set (H × H)} (hA : IsMonotoneGraph A)
    {a : ℝ} (ha : 0 ≤ a) {n : ℕ} (p : Fin n → H × H) (hp : ∀ i, p i ∈ A) (x : H)
    {w : Fin n → ℝ} (hw0 : ∀ i, 0 ≤ w i) (hw : ∑ i, w i = 1) :
    0 ≤ ∑ i, w i * ⟪∑ k, w k • (p k).1 - (p i).1,
      x - ∑ k, w k • (p k).1 - a • (p i).2⟫_ℝ := by
  set b := ∑ k, w k • (p k).1 with hb
  have hvanish : ∑ i, w i * ⟪b - (p i).1, x - b⟫_ℝ = 0 := by
    have hsumv : ∑ i, w i • (b - (p i).1) = 0 := by
      simp_rw [smul_sub, Finset.sum_sub_distrib]
      rw [← Finset.sum_smul, hw, one_smul, ← hb, sub_self]
    have hpair : ∑ i, w i * ⟪b - (p i).1, x - b⟫_ℝ =
        ⟪∑ i, w i • (b - (p i).1), x - b⟫_ℝ := by
      rw [sum_inner]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [real_inner_smul_left]
    rw [hpair, hsumv, inner_zero_left]
  have hsplit : ∑ i, w i * ⟪b - (p i).1, x - b - a • (p i).2⟫_ℝ =
      a * ∑ i, w i * ⟪(p i).1 - b, (p i).2⟫_ℝ := by
    have hgap_eq (i : Fin n) : ⟪b - (p i).1, x - b - a • (p i).2⟫_ℝ =
        ⟪b - (p i).1, x - b⟫_ℝ + a * ⟪(p i).1 - b, (p i).2⟫_ℝ := by
      rw [inner_sub_right, inner_smul_right, ← neg_sub (p i).1 b]
      simp only [inner_neg_left]
      ring
    simp_rw [hgap_eq, mul_add, Finset.sum_add_distrib, hvanish, zero_add]
    simp_rw [mul_left_comm (w _) a, ← Finset.mul_sum]
  have hmono : 0 ≤ ∑ i, w i * ⟪(p i).1 - b, (p i).2⟫_ℝ := by
    have hpairEq := sum_pair_inner_eq w (fun i => (p i).1) (fun i => (p i).2) hw
    have hnn : 0 ≤ ∑ i, ∑ j, w i * w j *
        ⟪(p i).1 - (p j).1, (p i).2 - (p j).2⟫_ℝ :=
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
        mul_nonneg (mul_nonneg (hw0 i) (hw0 j)) (hA _ (hp i) _ (hp j))
    rw [hpairEq, ← hb] at hnn
    linarith
  rw [hsplit]
  exact mul_nonneg ha hmono

/-- Finitely many monotone slices meet: by the simplex lemma, some convex combination of the
base points lies in every slice. -/
private theorem exists_common_monotoneSlice {A : Set (H × H)} (hA : IsMonotoneGraph A) {a : ℝ}
    (ha : 0 ≤ a) {n : ℕ} (hn : 0 < n) (p : Fin n → H × H) (hp : ∀ i, p i ∈ A) (x : H) :
    ∃ y, ∀ i, 0 ≤ ⟪y - (p i).1, x - y - a • (p i).2⟫_ℝ := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let bary (w : Fin n → ℝ) : H := ∑ k, w k • (p k).1
  have hbary : Continuous bary :=
    continuous_finsetSum _ fun k _ ↦ (continuous_apply k).smul continuous_const
  obtain ⟨w, -, -, hw⟩ := exists_forall_nonneg_of_sum_mul_nonneg
    (g := fun w i ↦ ⟪bary w - (p i).1, x - bary w - a • (p i).2⟫_ℝ)
    (continuous_pi fun i ↦ (hbary.sub continuous_const).inner
      ((continuous_const.sub hbary).sub continuous_const))
    fun w hw0 hw1 ↦ sum_mul_inner_barycenter_nonneg hA ha p hp x hw0 hw1
  exact ⟨bary w, hw⟩

/-- **35.32**: Minty's characterization at each positive scale. -/
theorem isMaximalMonotoneGraph_iff_range [CompleteSpace H]
    {A : Set (H × H)} (hA : IsMonotoneGraph A) {a : ℝ} (ha : 0 < a) :
    IsMaximalMonotoneGraph A ↔ ∀ x, (monotoneResolventFiber A a x).Nonempty := by
  constructor
  · intro hmax x
    have hreflexive : Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ H) :=
      TauCeti.surjective_inclusionInDoubleDual_of_uniformConvexSpace
    have hneA : A.Nonempty := by
      by_contra hempty
      have hpair : (0, 0) ∈ A ∪ {(0, 0)} := Set.mem_union_right _ rfl
      have hB : IsMonotoneGraph (A ∪ {(0, 0)}) := by
        intro p hp q hq
        rcases hp with hp | hp
        · exact False.elim (hempty ⟨p, hp⟩)
        · rcases hq with hq | hq
          · exact False.elim (hempty ⟨q, hq⟩)
          · simp [show p = (0, 0) from hp, show q = (0, 0) from hq]
      have hsub := hmax.2 _ hB Set.subset_union_left hpair
      exact hempty ⟨_, hsub⟩
    let slice : A → Set H := fun q =>
      {y | 0 ≤ ⟪y - (q : H × H).1, x - y - a • (q : H × H).2⟫_ℝ}
    have hball (q : ↥A) : slice q =
        Metric.closedBall ((2⁻¹ : ℝ) • ((q : H × H).1 + (x - a • (q : H × H).2)))
          (‖(x - a • (q : H × H).2) - (q : H × H).1‖ / 2) := by
      ext y
      simp only [slice, Set.mem_ofPred_eq]
      rw [show x - y - a • (q : H × H).2 = (x - a • (q : H × H).2) - y by abel]
      exact inner_nonneg_iff_mem_closedBall (v := (q : H × H).1)
        (c := x - a • (q : H × H).2) (y := y)
    have hcompact (q : ↥A) : IsCompact (toWeakSpace ℝ H '' slice q) := by
      rw [hball q]
      exact TauCeti.isCompact_toWeakSpace_closedBall hreflexive _ _
    obtain ⟨q0, hq0⟩ := hneA
    have hst (u : Finset (↥A)) :
        ((toWeakSpace ℝ H '' slice ⟨q0, hq0⟩) ∩
          ⋂ q ∈ u, toWeakSpace ℝ H '' slice q).Nonempty := by
      classical
      let qfin : Fin (u.card + 1) → H × H := fun i =>
        if h : (i : ℕ) < u.card then (u.equivFin.symm ⟨(i : ℕ), h⟩).1 else (⟨q0, hq0⟩ : ↥A)
      have hqfin : ∀ i, qfin i ∈ A := by
        intro i
        by_cases h : (i : ℕ) < u.card
        · exact (by simp [qfin, h])
        · exact (by simpa [qfin, h] using hq0)
      obtain ⟨y, hy⟩ :=
        exists_common_monotoneSlice hA ha.le (Nat.succ_pos u.card) qfin hqfin x
      refine ⟨toWeakSpace ℝ H y, ?_, ?_⟩
      · have hlast : qfin (Fin.last u.card) = q0 := by
          simp [qfin, Fin.val_last]
        exact ⟨y, by simpa [slice, hlast] using hy (Fin.last u.card), rfl⟩
      · rw [Set.mem_iInter₂]
        intro q hq
        let i0 : Fin u.card := u.equivFin ⟨q, hq⟩
        let j : Fin (u.card + 1) := i0.castSucc
        have _hj : (j : ℕ) < u.card := by
          have : (j : ℕ) = (i0 : ℕ) := by simp [j, Fin.val_castSucc]
          simp [this]
        have hqj : qfin j = (q : H × H) := by
          have heq : (u.equivFin.symm i0).1 = q :=
            congrArg Subtype.val (u.equivFin.symm_apply_apply ⟨q, hq⟩)
          simp [qfin, j, Fin.val_castSucc, heq]
        exact ⟨y, by simpa [slice, hqj] using hy j, rfl⟩
    have hinter : (⋂ q : ↥A, toWeakSpace ℝ H '' slice q).Nonempty :=
      ((hcompact ⟨q0, hq0⟩).inter_iInter_nonempty (fun q : ↥A => toWeakSpace ℝ H '' slice q)
        (fun q => (hcompact q).isClosed) hst).imp fun _ h => h.2
    obtain ⟨zW, hzW⟩ := hinter
    let y : H := (toWeakSpace ℝ H).symm zW
    have hySlice : ∀ q : ↥A, y ∈ slice q := by
      intro q
      obtain ⟨y', hy', hzy⟩ := (Set.mem_iInter.mp hzW) q
      have hyeq : y' = y :=
        (toWeakSpace ℝ H).injective (by simpa [y] using hzy)
      exact hyeq ▸ hy'
    have hcrit : ∀ p ∈ A, 0 ≤ ⟪y - p.1, a⁻¹ • (x - y) - p.2⟫_ℝ := by
      intro p hp
      have hscale : a⁻¹ • (x - y) - p.2 = a⁻¹ • (x - y - a • p.2) := by
        calc
          a⁻¹ • (x - y) - p.2 = a⁻¹ • (x - y) - (a⁻¹ * a) • p.2 := by
            rw [inv_mul_cancel₀ ha.ne', one_smul]
          _ = a⁻¹ • (x - y) - a⁻¹ • (a • p.2) := by rw [smul_smul]
          _ = a⁻¹ • (x - y - a • p.2) := by rw [← smul_sub]
      rw [hscale, inner_smul_right]
      exact mul_nonneg (le_of_lt (inv_pos.mpr ha)) (hySlice ⟨p, hp⟩)
    refine ⟨y, a⁻¹ • (x - y), hmax.mem_of_monotone_with hcrit, ?_⟩
    rw [smul_smul, mul_inv_cancel₀ ha.ne', one_smul]
    abel
  · intro hrange
    refine ⟨hA, fun B hB hAB z hz => ?_⟩
    obtain ⟨y, u, huA, hxu⟩ := hrange (z.1 + a • z.2)
    have hzy : z.1 = y := hB.resolventFiber_subsingleton ha.le (z.1 + a • z.2)
      ⟨z.2, hz, rfl⟩ ⟨u, hAB huA, hxu⟩
    have hzu : z.2 = u :=
      smul_right_injective H ha.ne' (by rw [hzy] at hxu; exact add_left_cancel hxu)
    rwa [show z = (y, u) from Prod.ext hzy hzu]

/-- Once a maximal monotone graph is given, every positive-scale resolvent fiber is a singleton. -/
theorem IsMaximalMonotoneGraph.existsUnique_resolvent [CompleteSpace H]
    {A : Set (H × H)} (hA : IsMaximalMonotoneGraph A) {a : ℝ} (ha : 0 < a) (x : H) :
    ∃! y, y ∈ monotoneResolventFiber A a x := by
  obtain ⟨y, hy⟩ := (isMaximalMonotoneGraph_iff_range hA.1 ha).mp hA x
  exact ⟨y, hy, fun z hz ↦ hA.1.resolventFiber_subsingleton ha.le x hz hy⟩

/-- The normal-cone graph of a set. Membership includes the base-point constraint. -/
@[expose]
def normalConeGraph (C : Set H) : Set (H × H) :=
  {p | p.1 ∈ C ∧ ∀ y ∈ C, ⟪p.2, y - p.1⟫_ℝ ≤ 0}

/-- Membership in the normal-cone graph. -/
theorem mem_normalConeGraph {C : Set H} {p : H × H} :
    p ∈ normalConeGraph C ↔ p.1 ∈ C ∧ ∀ y ∈ C, ⟪p.2, y - p.1⟫_ℝ ≤ 0 := Iff.rfl

/-- The normal-cone graph of any set is monotone. -/
theorem isMonotoneGraph_normalConeGraph (C : Set H) : IsMonotoneGraph (normalConeGraph C) := by
  rintro ⟨x, u⟩ ⟨hx, hu⟩ ⟨y, v⟩ ⟨hy, hv⟩
  have h1 := hu y hy
  have h2 := hv x hx
  have : ⟪x - y, u - v⟫_ℝ = -⟪u, y - x⟫_ℝ - ⟪v, x - y⟫_ℝ := by
    rw [inner_sub_right, real_inner_comm, real_inner_comm v, ← inner_neg_right, neg_sub]
  rw [this]
  linarith

end Hilbert

end CKMA
