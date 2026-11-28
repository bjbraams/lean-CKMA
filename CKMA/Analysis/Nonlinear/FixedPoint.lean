/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.Convex.Uniform
public import Mathlib.Topology.Algebra.Module.LocallyConvex
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.Cauchy
import TauCeti.AlgebraicTopology.Singular.BrouwerFixedPoint
import TauCeti.Analysis.Convex.SchauderFixedPoint

/-!
# Fixed points beyond contraction mappings

Brouwer and Schauder concern continuous maps of nonempty convex sets; Schauder assumes a
closed domain and relatively compact total image rather than boundedness of the domain.
Kakutani–Fan–Glicksberg allows upper hemicontinuous multifunctions with nonempty closed convex
values inside a compact convex set in a locally convex Hausdorff space.

The Browder–Göhde–Kirk statement uses uniform convexity and a nonexpansive map on a closed
bounded convex set; compactness of the map is not required. Sources: GAPS 35.12, 35.13, 35.15, and
35.21.

The Brouwer and Schauder statements are adapters of TauCeti's
`brouwerFixedPoint_compactConvex` and `schauderFixedPoint_closedConvex` to maps of the subtype;
the latter does not require completeness of the ambient space.

## Main results

* `CKMA.exists_forall_nonneg_of_sum_mul_nonneg`: a simplex lemma from Brouwer's theorem: a
  continuous `g` with nonnegative weighted sums `∑ i, w i * g w i` on the simplex has a weight
  vector at which every `g w i` is nonnegative.
* `CKMA.exists_fixedPoint_brouwer`: Brouwer's fixed-point theorem on a compact convex subset of a
  finite-dimensional real normed space (**35.12**), derived from TauCeti's
  `TauCeti.brouwerFixedPoint_compactConvex`.
* `CKMA.exists_fixedPoint_schauder`: Schauder's fixed-point theorem with relatively compact total
  image on a closed convex set (**35.13**), from `TauCeti.schauderFixedPoint_closedConvex`.
* `CKMA.exists_fixedPoint_kakutani`: Kakutani–Fan–Glicksberg fixed-point theorem for compact convex
  subsets of locally convex spaces (**35.15**).
* `CKMA.exists_fixedPoint_nonexpansive`: Browder–Göhde–Kirk fixed-point theorem for nonexpansive
  maps on uniformly convex Banach spaces (**35.21**), via the unique asymptotic center
  of a bounded orbit.
-/

public section

noncomputable section

namespace CKMA

open Filter Metric Set Topology Bornology

/-- **35.12**: Brouwer's theorem on a compact convex subset of a finite-dimensional real space. -/
theorem exists_fixedPoint_brouwer {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {C : Set E} (hne : C.Nonempty) (hC : IsCompact C)
    (hc : Convex ℝ C) (T : C → C) (hT : Continuous T) : ∃ x : C, T x = x :=
  TauCeti.brouwerFixedPoint_compactConvex hC hc hne ⟨T, hT⟩

/-- **Simplex lemma**, a consequence of Brouwer's theorem: if `g : (ι → ℝ) → ι → ℝ` is continuous
and `0 ≤ ∑ i, w i * g w i` for every weight vector `w` (nonnegative, summing to one), then some
weight vector `w` has `0 ≤ g w i` for every `i`. The map adding the negative parts of `g w` to `w`
and renormalizing has a fixed point, at which those negative parts vanish. -/
theorem exists_forall_nonneg_of_sum_mul_nonneg {ι : Type*} [Fintype ι] [Nonempty ι]
    {g : (ι → ℝ) → ι → ℝ} (hg : Continuous g)
    (hsum : ∀ w : ι → ℝ, (∀ i, 0 ≤ w i) → ∑ i, w i = 1 → 0 ≤ ∑ i, w i * g w i) :
    ∃ w : ι → ℝ, (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧ ∀ i, 0 ≤ g w i := by
  classical
  let slack (w : ι → ℝ) (i : ι) : ℝ := max 0 (-g w i)
  let denom (w : ι → ℝ) : ℝ := 1 + ∑ i, slack w i
  have hdenom (w : ι → ℝ) : 1 ≤ denom w :=
    le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ ↦ le_max_left _ _)
  have hdenom_ne (w : ι → ℝ) : denom w ≠ 0 := by linarith [hdenom w]
  have hslackC : Continuous slack :=
    continuous_pi fun i ↦ continuous_const.max ((continuous_apply i).comp hg).neg
  let T (w : ι → ℝ) (i : ι) : ℝ := (w i + slack w i) / denom w
  have hT : Continuous T := continuous_pi fun i ↦
    ((continuous_apply i).add ((continuous_apply i).comp hslackC)).div₀
      (continuous_const.add (continuous_finsetSum _ fun i _ ↦ (continuous_apply i).comp hslackC))
      hdenom_ne
  let S : Set (ι → ℝ) := {w | ∀ i, 0 ≤ w i} ∩ {w | ∑ i, w i = 1}
  have hSconv : Convex ℝ S := by
    rintro x ⟨hx0, hx1⟩ y ⟨hy0, hy1⟩ a b ha hb hab
    refine ⟨fun i ↦ add_nonneg (mul_nonneg ha (hx0 i)) (mul_nonneg hb (hy0 i)), ?_⟩
    have hx : ∑ i, x i = 1 := hx1
    have hy : ∑ i, y i = 1 := hy1
    simp only [Set.mem_ofPred_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_add_distrib, ← Finset.mul_sum, hx, hy, mul_one, hab]
  have hScpt : IsCompact S := by
    refine Metric.isCompact_of_isClosed_isBounded ?_ ((Metric.isBounded_Icc (0 : ι → ℝ) 1).subset
      fun w hw ↦ ⟨fun i ↦ hw.1 i, fun i ↦ (Finset.single_le_sum (fun j _ ↦ hw.1 j)
        (Finset.mem_univ i)).trans_eq hw.2⟩)
    refine IsClosed.inter ?_ (isClosed_eq (continuous_finsetSum _ fun i _ ↦ continuous_apply i)
      continuous_const)
    simpa only [Set.ofPred_forall] using isClosed_iInter fun i ↦
      isClosed_le continuous_const (continuous_apply i)
  have hmaps (w : ι → ℝ) (hw : w ∈ S) : T w ∈ S := by
    refine ⟨fun i ↦ div_nonneg (add_nonneg (hw.1 i) (le_max_left _ _))
      (zero_le_one.trans (hdenom w)), ?_⟩
    simp only [Set.mem_ofPred_eq]
    rw [← Finset.sum_div, Finset.sum_add_distrib, hw.2, div_self (hdenom_ne w)]
  have hS0 : Pi.single (Classical.arbitrary ι) 1 ∈ S :=
    ⟨fun i ↦ by by_cases h : i = Classical.arbitrary ι <;> simp [h], by simp⟩
  obtain ⟨⟨w, hw⟩, hfix⟩ := TauCeti.brouwerFixedPoint_compactConvex hScpt hSconv ⟨_, hS0⟩
    ⟨fun w ↦ ⟨T w, hmaps w w.2⟩, (hT.comp continuous_subtype_val).subtype_mk _⟩
  have hTw : T w = w := congrArg Subtype.val hfix
  have hslack (i : ι) : slack w i = (denom w - 1) * w i := by
    have hi := congrFun hTw i
    rw [div_eq_iff (hdenom_ne w)] at hi
    linarith
  -- `slack * g = -slack ^ 2` termwise, while the weighted sum of `g` is nonnegative.
  have hprod (i : ι) : slack w i * g w i = -slack w i ^ 2 := by
    rcases le_total 0 (g w i) with hgi | hgi
    · simp [slack, max_eq_left (neg_nonpos.mpr hgi)]
    · rw [show slack w i = -g w i from max_eq_right (neg_nonneg.mpr hgi)]
      ring
  have hsq : ∑ i, slack w i ^ 2 ≤ 0 := by
    have h1 : ∑ i, slack w i * g w i = (denom w - 1) * ∑ i, w i * g w i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ ↦ by rw [hslack i]; ring
    have h2 : 0 ≤ (denom w - 1) * ∑ i, w i * g w i :=
      mul_nonneg (sub_nonneg.mpr (hdenom w)) (hsum w hw.1 hw.2)
    simp only [hprod, Finset.sum_neg_distrib] at h1
    linarith
  refine ⟨w, hw.1, hw.2, fun i ↦ ?_⟩
  have hi : slack w i ^ 2 = 0 := le_antisymm
    ((Finset.single_le_sum (fun j _ ↦ sq_nonneg (slack w j)) (Finset.mem_univ i)).trans hsq)
    (sq_nonneg _)
  have hi' : max 0 (-g w i) = 0 := pow_eq_zero_iff two_ne_zero |>.mp hi
  linarith [le_max_right 0 (-g w i)]

/-- **35.13**: Schauder's theorem with relatively compact total image on a closed convex set.
Boundedness of the domain is not required when the total image is relatively compact.
Completeness of `E` is not required. This is `TauCeti.schauderFixedPoint_closedConvex`. -/
theorem exists_fixedPoint_schauder {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {C : Set E} (hne : C.Nonempty) (hclosed : IsClosed C)
    (hc : Convex ℝ C) (T : C → C) (hT : Continuous T)
    (himage : IsCompact (closure (Set.range (fun x : C ↦ (T x : E))))) :
    ∃ x : C, T x = x := by
  obtain ⟨x, hx⟩ :=
    TauCeti.schauderFixedPoint_closedConvex hclosed hc hne ⟨T, hT⟩ himage
  exact ⟨x, hx⟩

/-- **35.15**: Kakutani–Fan–Glicksberg for compact convex subsets of locally convex spaces.
The multifunction is defined on the ambient space but only its restriction to `C` is constrained. -/
theorem exists_fixedPoint_kakutani {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [LocallyConvexSpace ℝ E] [T2Space E]
    {C : Set E} (hne : C.Nonempty) (hC : IsCompact C) (hc : Convex ℝ C)
    (T : E → Set E) (hT : UpperHemicontinuousOn T C)
    (hvalues : ∀ x ∈ C, (T x).Nonempty ∧ IsClosed (T x) ∧ Convex ℝ (T x) ∧ T x ⊆ C) :
    ∃ x ∈ C, x ∈ T x := by
  sorry

/-- **35.21**: Browder–Göhde–Kirk requires uniform convexity of the Banach space,
not compactness of the nonexpansive map. -/
theorem exists_fixedPoint_nonexpansive {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [UniformConvexSpace E]
    {C : Set E} (hne : C.Nonempty) (hclosed : IsClosed C) (hbounded : Bornology.IsBounded C)
    (hc : Convex ℝ C) (T : C → C) (hT : LipschitzWith 1 T) : ∃ x : C, T x = x := by
  classical
  obtain ⟨x₀, hx₀⟩ := hne
  let orbit (n : ℕ) : C := T^[n] ⟨x₀, hx₀⟩
  -- Minimize the radii of balls containing a tail of the orbit.
  let covers (x : C) (s : ℝ) := ∀ᶠ n in atTop, dist x (orbit n) ≤ s
  let radii : Set ℝ := {s | ∃ x : C, covers x s}
  let r := sInf radii
  have hradii : radii.Nonempty := by
    obtain ⟨D, hD⟩ := Metric.isBounded_iff.mp hbounded
    exact ⟨D, ⟨x₀, hx₀⟩, Eventually.of_forall fun n ↦ hD hx₀ (orbit n).2⟩
  have hradii_nonneg : ∀ s ∈ radii, 0 ≤ s := by
    rintro s ⟨x, hx⟩
    obtain ⟨n, hn⟩ := hx.exists
    exact dist_nonneg.trans hn
  have hradii_bdd : BddBelow radii := ⟨0, hradii_nonneg⟩
  have hr : 0 ≤ r := le_csInf hradii hradii_nonneg
  have hmono (x : C) {s t : ℝ} (hst : s ≤ t) (hx : covers x s) : covers x t :=
    hx.mono fun _ hn ↦ hn.trans hst
  have hnear (η : ℝ) (hη : 0 < η) : ∃ x : C, covers x (r + η) := by
    obtain ⟨s, ⟨x, hx⟩, hs⟩ := exists_lt_of_csInf_lt hradii (lt_add_of_pos_right r hη)
    exact ⟨x, hmono x hs.le hx⟩
  -- Uniform convexity forces two nearly optimal centers to be close.
  have hclose (ε : ℝ) (hε : 0 < ε) :
      ∃ η > 0, ∀ x y : C, covers x (r + η) → covers y (r + η) → dist x y < ε := by
    rcases hr.eq_or_lt with hr₀ | hrpos
    · refine ⟨ε / 3, by positivity, fun x y hx hy ↦ ?_⟩
      obtain ⟨n, hxn, hyn⟩ := (hx.and hy).exists
      rw [← hr₀, zero_add] at hxn hyn
      exact (dist_triangle_right x y (orbit n)).trans_lt (by linarith)
    obtain ⟨δ, hδ, hconvex⟩ :=
      exists_forall_closed_ball_dist_add_le_two_sub E (div_pos hε (by positivity : 0 < r + 1))
    let η := min 1 (δ * r / 4)
    have hη : 0 < η := lt_min zero_lt_one (by positivity)
    let s := r + η
    have hs : 0 < s := add_pos hrpos hη
    have hs_upper : s ≤ r + 1 := add_le_add_right (min_le_left _ _) r
    have hη_upper : η ≤ δ * r / 4 := min_le_right _ _
    refine ⟨η, hη, fun x y hx hy ↦ ?_⟩
    by_contra! hxy
    let m : C := ⟨midpoint ℝ (x : E) (y : E), hc.midpoint_mem x.2 y.2⟩
    have hm : covers m (s - δ * s / 2) := by
      filter_upwards [hx, hy] with n hxn hyn
      let z : E := orbit n
      let u : E := (x : E) - z
      let v : E := (y : E) - z
      have hnorm (w : E) (hw : ‖w‖ ≤ s) : ‖s⁻¹ • w‖ ≤ 1 := by
        rw [norm_smul_of_nonneg (inv_nonneg.mpr hs.le), inv_mul_eq_div]
        exact (div_le_one hs).mpr hw
      have hsub : u - v = (x : E) - (y : E) := sub_sub_sub_cancel_right _ _ _
      have hsep : ε / (r + 1) ≤ ‖s⁻¹ • u - s⁻¹ • v‖ := by
        rw [← smul_sub, hsub, norm_smul_of_nonneg (inv_nonneg.mpr hs.le),
          inv_mul_eq_div, ← dist_eq_norm]
        exact (div_le_div_of_nonneg_left hε.le hs hs_upper).trans
          (div_le_div_of_nonneg_right hxy hs.le)
      have hsum := hconvex (hnorm u (by simpa only [Subtype.dist_eq, dist_eq_norm] using hxn))
        (hnorm v (by simpa only [Subtype.dist_eq, dist_eq_norm] using hyn)) hsep
      rw [← smul_add, norm_smul_of_nonneg (inv_nonneg.mpr hs.le), inv_mul_eq_div,
        div_le_iff₀ hs] at hsum
      have hmz : (m : E) - z = (⅟(2 : ℝ)) • (u + v) := by
        simpa only [vsub_eq_sub, smul_add] using midpoint_vsub (R := ℝ) (x : E) (y : E) z
      have hd : dist m (orbit n) = ‖u + v‖ / 2 := by
        rw [Subtype.dist_eq, dist_eq_norm, hmz, invOf_eq_inv,
          norm_smul_of_nonneg (by norm_num : 0 ≤ (2 : ℝ)⁻¹), inv_mul_eq_div]
      rw [hd]
      linarith only [hsum]
    have hmin : r ≤ s - δ * s / 2 := csInf_le hradii_bdd ⟨m, hm⟩
    have hδr : δ * r ≤ δ * s := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hη.le) hδ.le
    linarith only [hmin, hη_upper, hδr, mul_pos hδ hrpos]
  let tolerance (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  have htolerance : Tendsto tolerance atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  choose center hcenter using fun n : ℕ ↦ hnear (tolerance n) (by unfold tolerance; positivity)
  have hcauchy : CauchySeq center := by
    refine Metric.cauchySeq_iff.mpr fun ε hε ↦ ?_
    obtain ⟨η, hη, hdiam⟩ := hclose ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.mp (htolerance.eventually (gt_mem_nhds hη))
    exact ⟨N, fun i hi j hj ↦ hdiam _ _
      (hmono _ (add_le_add_right (hN i hi).le r) (hcenter i))
      (hmono _ (add_le_add_right (hN j hj).le r) (hcenter j))⟩
  let : CompleteSpace C := hclosed.isComplete.completeSpace_coe
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hlimit (η : ℝ) (hη : 0 < η) : covers x (r + η) := by
    have hhalf : 0 < η / 2 := half_pos hη
    obtain ⟨i, hi, hdist⟩ :=
      ((htolerance.eventually (gt_mem_nhds hhalf)).and
        (hx.eventually (Metric.ball_mem_nhds x hhalf))).exists
    filter_upwards [hcenter i] with n hn
    have hdist' : dist x (center i) < η / 2 := by
      simpa only [Metric.mem_ball, dist_comm] using hdist
    exact (dist_triangle x (center i) (orbit n)).trans (by linarith)
  have hTlimit (η : ℝ) (hη : 0 < η) : covers (T x) (r + η) := by
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hlimit η hη)
    refine eventually_atTop.mpr ⟨N + 1, fun n hn ↦ ?_⟩
    cases n with
    | zero => omega
    | succ n =>
      have hstep : orbit (n + 1) = T (orbit n) := Function.iterate_succ_apply' T n _
      rw [hstep]
      have hle : dist (T x) (T (orbit n)) ≤ dist x (orbit n) := by
        simpa only [NNReal.coe_one, one_mul] using hT.dist_le_mul x (orbit n)
      exact hle.trans (hN n (by omega))
  refine ⟨x, eq_of_dist_eq_zero (le_antisymm (le_of_not_gt fun hpos ↦ ?_) dist_nonneg)⟩
  obtain ⟨η, hη, hdiam⟩ := hclose _ hpos
  exact (hdiam _ _ (hTlimit η hη) (hlimit η hη)).false

end CKMA
