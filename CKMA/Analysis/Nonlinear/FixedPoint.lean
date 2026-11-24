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

The approximation lemmas build a finite-net Schauder projection and call
`TauCeti.brouwerFixedPoint_compactConvex_finiteSpan`. The closed-convex statement
`exists_fixedPoint_schauder` is TauCeti's `schauderFixedPoint_closedConvex`, which does not
require completeness of the ambient space.

## Main results

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
open scoped BigOperators

/-- **35.12**: Brouwer's theorem on a compact convex subset of a finite-dimensional real space. -/
theorem exists_fixedPoint_brouwer {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {C : Set E} (hne : C.Nonempty) (hC : IsCompact C)
    (hc : Convex ℝ C) (T : C → C) (hT : Continuous T) : ∃ x : C, T x = x :=
  TauCeti.brouwerFixedPoint_compactConvex hC hc hne ⟨T, hT⟩

section SchauderProjection

variable {E : Type*} [NormedAddCommGroup E]

/-- Truncated distance `max (ε - ‖x - y‖, 0)` of `x` from a net point `y`. -/
@[expose]
def schauderWeight (ε : ℝ) (y x : E) : ℝ := max (ε - ‖x - y‖) 0

/-- The Schauder weight is nonnegative. -/
theorem schauderWeight_nonneg (ε : ℝ) (y x : E) : 0 ≤ schauderWeight ε y x :=
  le_max_right _ _

/-- The Schauder weight is positive exactly on the open ball of radius `ε`. -/
theorem schauderWeight_pos_iff {ε : ℝ} {y x : E} :
    0 < schauderWeight ε y x ↔ ‖x - y‖ < ε := by
  simp only [schauderWeight, lt_max_iff, lt_irrefl, or_false, sub_pos]

/-- A positive Schauder weight does not increase the distance it truncates. -/
theorem schauderWeight_mul_norm_sub_le (ε : ℝ) (y x : E) :
    schauderWeight ε y x * ‖y - x‖ ≤ schauderWeight ε y x * ε := by
  rw [norm_sub_rev]
  rcases le_total ‖x - y‖ ε with h | h
  · exact mul_le_mul_of_nonneg_left h (schauderWeight_nonneg ε y x)
  · rw [schauderWeight, max_eq_right (sub_nonpos.2 h)]
    simp

/-- The Schauder weight of a fixed net point depends continuously on the base point. -/
theorem continuous_schauderWeight (ε : ℝ) (y : E) : Continuous (schauderWeight ε y) := by
  unfold schauderWeight
  refine Continuous.max ?_ ?_
  · exact (continuous_const.sub (continuous_id.sub continuous_const).norm)
  · exact continuous_const

/-- Sum of the Schauder weights of a finite net `t` at `x`. -/
@[expose]
def schauderWeightSum (t : Finset E) (ε : ℝ) (x : E) : ℝ :=
  ∑ y ∈ t, schauderWeight ε y x

/-- The total Schauder weight depends continuously on the base point. -/
theorem continuous_schauderWeightSum (t : Finset E) (ε : ℝ) :
    Continuous (schauderWeightSum t ε) := by
  unfold schauderWeightSum
  exact continuous_finsetSum t fun y _ ↦ continuous_schauderWeight ε y

/-- The total weight is positive as soon as one net point lies in the open `ε`-ball. -/
theorem schauderWeightSum_pos_of_mem_ball {t : Finset E} {ε : ℝ} {x : E}
    (hx : ∃ y ∈ t, ‖x - y‖ < ε) : 0 < schauderWeightSum t ε x := by
  obtain ⟨y, hy, hlt⟩ := hx
  refine Finset.sum_pos' (fun z _ ↦ schauderWeight_nonneg ε z x) ⟨y, hy, ?_⟩
  rwa [schauderWeight_pos_iff]

variable [NormedSpace ℝ E]

/-- Schauder projection of `x` onto the convex hull of the finite net `t` at scale `ε`.
The value is the junk center of mass `0` when every weight vanishes. -/
@[expose]
def schauderProjection (t : Finset E) (ε : ℝ) (x : E) : E :=
  t.centerMass (fun y ↦ schauderWeight ε y x) id

/-- The Schauder projection is the normalized weighted average of the net. -/
theorem schauderProjection_apply (t : Finset E) (ε : ℝ) (x : E) :
    schauderProjection t ε x =
      (schauderWeightSum t ε x)⁻¹ • ∑ y ∈ t, schauderWeight ε y x • y := by
  simp [schauderProjection, schauderWeightSum, Finset.centerMass, id_eq]

/-- Where some weight is positive, the projection lands in the convex hull of the net. -/
theorem schauderProjection_mem_convexHull {t : Finset E} {ε : ℝ} {x : E}
    (hx : 0 < schauderWeightSum t ε x) :
    schauderProjection t ε x ∈ convexHull ℝ (t : Set E) := by
  unfold schauderProjection
  exact Finset.centerMass_id_mem_convexHull t
    (fun y _ ↦ schauderWeight_nonneg ε y x) hx

/-- Subtracting `x` from its Schauder projection leaves a normalized combination of
`y - x`. -/
theorem schauderProjection_sub {t : Finset E} {ε : ℝ} {x : E}
    (hx : schauderWeightSum t ε x ≠ 0) :
    schauderProjection t ε x - x =
      (schauderWeightSum t ε x)⁻¹ • ∑ y ∈ t, schauderWeight ε y x • (y - x) := by
  rw [schauderProjection_apply]
  unfold schauderWeightSum at hx ⊢
  symm
  calc
    (∑ y ∈ t, schauderWeight ε y x)⁻¹ • ∑ y ∈ t, schauderWeight ε y x • (y - x)
        = (∑ y ∈ t, schauderWeight ε y x)⁻¹ •
            ∑ y ∈ t, (schauderWeight ε y x • y - schauderWeight ε y x • x) := by
          simp_rw [smul_sub]
    _ = (∑ y ∈ t, schauderWeight ε y x)⁻¹ •
          (∑ y ∈ t, schauderWeight ε y x • y - ∑ y ∈ t, schauderWeight ε y x • x) := by
          rw [Finset.sum_sub_distrib]
    _ = (∑ y ∈ t, schauderWeight ε y x)⁻¹ •
          (∑ y ∈ t, schauderWeight ε y x • y -
            (∑ y ∈ t, schauderWeight ε y x) • x) := by
          rw [← Finset.sum_smul]
    _ = (∑ y ∈ t, schauderWeight ε y x)⁻¹ • ∑ y ∈ t, schauderWeight ε y x • y -
          (∑ y ∈ t, schauderWeight ε y x)⁻¹ • ((∑ y ∈ t, schauderWeight ε y x) • x) := by
          rw [smul_sub]
    _ = (∑ y ∈ t, schauderWeight ε y x)⁻¹ • ∑ y ∈ t, schauderWeight ε y x • y -
          ((∑ y ∈ t, schauderWeight ε y x)⁻¹ * ∑ y ∈ t, schauderWeight ε y x) • x := by
          rw [← mul_smul]
    _ = (∑ y ∈ t, schauderWeight ε y x)⁻¹ • ∑ y ∈ t, schauderWeight ε y x • y - x := by
          rw [inv_mul_cancel₀ hx, one_smul]

/-- Where some weight is positive, the projection moves `x` by at most `ε`. -/
theorem dist_schauderProjection_le {t : Finset E} {ε : ℝ} {x : E}
    (hx : 0 < schauderWeightSum t ε x) : dist (schauderProjection t ε x) x ≤ ε := by
  rw [dist_eq_norm, schauderProjection_sub hx.ne']
  unfold schauderWeightSum at hx ⊢
  set S : ℝ := ∑ y ∈ t, schauderWeight ε y x
  have hpoint : ∀ y ∈ t, ‖schauderWeight ε y x • (y - x)‖ ≤ schauderWeight ε y x * ε := by
    intro y _
    calc
      ‖schauderWeight ε y x • (y - x)‖ = schauderWeight ε y x * ‖y - x‖ :=
        norm_smul_of_nonneg (schauderWeight_nonneg ε y x) _
      _ ≤ schauderWeight ε y x * ε := schauderWeight_mul_norm_sub_le ε y x
  have hsum : ‖∑ y ∈ t, schauderWeight ε y x • (y - x)‖ ≤ S * ε := by
    refine (norm_sum_le_of_le t hpoint).trans_eq ?_
    rw [← Finset.sum_mul]
  rw [norm_smul_of_nonneg (inv_nonneg.2 hx.le)]
  calc
    S⁻¹ * ‖∑ y ∈ t, schauderWeight ε y x • (y - x)‖ ≤ S⁻¹ * (S * ε) :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.2 hx.le)
    _ = ε := by rw [← mul_assoc, inv_mul_cancel₀ hx.ne', one_mul]

/-- The Schauder projection is continuous at every point of positive total weight. -/
theorem continuousAt_schauderProjection {t : Finset E} {ε : ℝ} {x : E}
    (hx : schauderWeightSum t ε x ≠ 0) : ContinuousAt (schauderProjection t ε) x := by
  have hvec : Continuous fun z : E ↦ ∑ y ∈ t, schauderWeight ε y z • y :=
    continuous_finsetSum t fun y _ ↦ (continuous_schauderWeight ε y).smul continuous_const
  have hproj : schauderProjection t ε = fun z ↦
      (schauderWeightSum t ε z)⁻¹ • ∑ y ∈ t, schauderWeight ε y z • y := by
    ext z
    exact schauderProjection_apply t ε z
  rw [hproj]
  exact ((continuous_schauderWeightSum t ε).continuousAt.inv₀ hx).smul hvec.continuousAt

end SchauderProjection

/-- At every positive scale, a continuous self-map whose total image is relatively compact
moves some point of the closed convex domain by at most that scale. -/
theorem exists_dist_le_schauder {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {C : Set E} (hne : C.Nonempty) (hclosed : IsClosed C) (hc : Convex ℝ C) (T : C → C)
    (hT : Continuous T) (himage : IsCompact (closure (Set.range fun x : C ↦ (T x : E))))
    {ε : ℝ} (hε : 0 < ε) : ∃ x : C, dist (x : E) (T x : E) ≤ ε := by
  set K := closure (Set.range fun x : C ↦ (T x : E)) with hK
  have hK_sub : K ⊆ C := by
    rw [hK]
    refine closure_minimal ?_ hclosed
    rintro _ ⟨x, rfl⟩
    exact (T x).2
  have hKne : K.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    refine ⟨(T (⟨x, hx⟩ : C) : E), ?_⟩
    rw [hK]
    exact subset_closure (mem_range_self (⟨x, hx⟩ : C))
  obtain ⟨snet, hsnet, hsfin, hcover⟩ :=
    finite_approx_of_totallyBounded himage.totallyBounded ε hε
  let t : Finset E := hsfin.toFinset
  have ht_coe : (t : Set E) = snet := hsfin.coe_toFinset
  have htK : (t : Set E) ⊆ K := by
    rw [ht_coe]
    exact hsnet
  rw [← ht_coe] at hcover
  have htne : (t : Set E).Nonempty := by
    obtain ⟨z, hz⟩ := hKne
    have hmem : z ∈ ⋃ y ∈ (t : Set E), ball y ε := hcover hz
    simp only [mem_iUnion₂, mem_ball] at hmem
    obtain ⟨y, hy, _⟩ := hmem
    exact ⟨y, hy⟩
  set Q : Set E := convexHull ℝ (t : Set E) with hQ
  have hQcompact : IsCompact Q := by
    rw [hQ]
    exact t.finite_toSet.isCompact_convexHull ℝ
  have hQconv : Convex ℝ Q := by
    rw [hQ]
    exact convex_convexHull ℝ _
  have hQne : Q.Nonempty := by
    rw [hQ]
    exact htne.convexHull
  have hfin : FiniteDimensional ℝ (Submodule.span ℝ Q) := by
    rw [hQ]
    exact Submodule.finiteDimensional_of_le <| by
      rw [Submodule.span_le]
      exact convexHull_min Submodule.subset_span (Submodule.span ℝ (t : Set E)).convex
  have hQC : Q ⊆ C := by
    rw [hQ]
    exact convexHull_min (fun y hy ↦ hK_sub (htK hy)) hc
  let S : Q → E := fun z ↦ (T (inclusion hQC z) : E)
  have hScont : Continuous S :=
    continuous_subtype_val.comp (hT.comp (continuous_inclusion hQC))
  have hSpos : ∀ z, 0 < schauderWeightSum t ε (S z) := by
    intro z
    have hzK : S z ∈ K := by
      rw [hK]
      exact subset_closure (mem_range_self (inclusion hQC z))
    have hmem : S z ∈ ⋃ y ∈ (t : Set E), ball y ε := hcover hzK
    simp only [mem_iUnion₂, mem_ball] at hmem
    obtain ⟨y, hy, hdist⟩ := hmem
    refine schauderWeightSum_pos_of_mem_ball ⟨y, Finset.mem_coe.mp hy, ?_⟩
    rw [← dist_eq_norm]
    exact hdist
  have hSmem : ∀ z, schauderProjection t ε (S z) ∈ Q := by
    intro z
    rw [hQ]
    exact schauderProjection_mem_convexHull (hSpos z)
  let φ : Q → Q := fun z ↦ ⟨schauderProjection t ε (S z), hSmem z⟩
  have hφ : Continuous φ :=
    Continuous.subtype_mk
      (continuous_iff_continuousAt.mpr fun z ↦
        (continuousAt_schauderProjection (hSpos z).ne').comp hScont.continuousAt)
      hSmem
  obtain ⟨z, hz⟩ :=
    @TauCeti.brouwerFixedPoint_compactConvex_finiteSpan E _ _ (Submodule.span ℝ Q) hfin Q
      Submodule.subset_span hQcompact hQconv hQne ⟨φ, hφ⟩
  refine ⟨inclusion hQC z, ?_⟩
  rw [← congrArg Subtype.val hz]
  exact dist_schauderProjection_le (hSpos z)

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

set_option warn.sorry false in
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
