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

/-!
# Fixed points beyond contraction mappings

Brouwer and Schauder concern continuous maps of nonempty convex sets; Schauder assumes a
closed domain and relatively compact total image rather than boundedness of the domain.
Kakutani–Fan–Glicksberg allows upper hemicontinuous multifunctions with nonempty closed convex
values inside a compact convex set in a locally convex Hausdorff space.

The Browder–Göhde–Kirk statement uses uniform convexity and a nonexpansive map on a closed
bounded convex set; compactness of the map is not required. Sources: GAPS 35.12, 35.13, 35.15, and
35.21.

Schauder's argument approximates the compact closure of the image by a finite net, projects onto
the convex hull of that net by the continuous Schauder weights `schauderWeight`, and applies
`TauCeti.brouwerFixedPoint_compactConvex_finiteSpan`. Completeness of the ambient space is not
used beyond the stated Banach setting: the limit lives in the given compact closure.

## Main results

* `CKMA.exists_fixedPoint_brouwer`: Brouwer's fixed-point theorem on a compact convex subset of a
  finite-dimensional real normed space (**35.12**), derived from TauCeti's
  `TauCeti.brouwerFixedPoint_compactConvex`.
* `CKMA.exists_fixedPoint_schauder`: Schauder's fixed-point theorem with relatively compact total
  image on a closed convex set (**35.13**).
* `CKMA.exists_fixedPoint_kakutani`: Kakutani–Fan–Glicksberg fixed-point theorem for compact convex
  subsets of locally convex spaces (**35.15**).
* `CKMA.exists_fixedPoint_nonexpansive`: Browder–Göhde–Kirk fixed-point theorem for nonexpansive
  maps on uniformly convex Banach spaces (**35.21**).
-/

@[expose] public section

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
Boundedness of the domain is not required when the total image is relatively compact. -/
theorem exists_fixedPoint_schauder {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {C : Set E} (hne : C.Nonempty) (hclosed : IsClosed C)
    (hc : Convex ℝ C) (T : C → C) (hT : Continuous T)
    (himage : IsCompact (closure (Set.range (fun x : C ↦ (T x : E))))) :
    ∃ x : C, T x = x := by
  -- The stated Banach hypothesis is not required for the compact-closure limit below.
  have _ : CompleteSpace E := inferInstance
  set K := closure (Set.range fun x : C ↦ (T x : E)) with hK
  have hK_sub : K ⊆ C := by
    rw [hK]
    refine closure_minimal ?_ hclosed
    rintro _ ⟨x, rfl⟩
    exact (T x).2
  choose x hx using fun n : ℕ ↦ exists_dist_le_schauder hne hclosed hc T hT himage
    (ε := ((n : ℝ) + 1)⁻¹) (inv_pos.2 <| add_pos_of_nonneg_of_pos (Nat.cast_nonneg n) zero_lt_one)
  obtain ⟨a, ha, φ, hφ, ha_lim⟩ :=
    himage.tendsto_subseq fun n ↦ by
      rw [hK]
      exact subset_closure (mem_range_self (x n))
  have hφ_inv : Tendsto (fun n ↦ ((φ n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
    (tendsto_atTop_add_const_right atTop (1 : ℝ)
      (tendsto_natCast_atTop_atTop.comp hφ.tendsto_atTop)).inv_tendsto_atTop
  have hclose : Tendsto (fun n ↦ dist ((x (φ n) : E)) (T (x (φ n)) : E)) atTop (𝓝 0) :=
    squeeze_zero (fun _ ↦ dist_nonneg) (fun n ↦ hx (φ n)) hφ_inv
  have hx_lim : Tendsto (fun n ↦ (x (φ n) : E)) atTop (𝓝 a) := by
    refine tendsto_iff_dist_tendsto_zero.mpr ?_
    refine squeeze_zero (fun _ ↦ dist_nonneg)
      (fun n ↦ dist_triangle ((x (φ n) : E)) (T (x (φ n)) : E) a) ?_
    have hsum := hclose.add ((tendsto_iff_dist_tendsto_zero).mp ha_lim)
    rw [add_zero] at hsum
    exact hsum
  have haC : a ∈ C := hK_sub ha
  have hxC : Tendsto (fun n ↦ x (φ n)) atTop (𝓝 ⟨a, haC⟩) :=
    tendsto_subtype_rng.mpr hx_lim
  have hTlim : Tendsto (fun n ↦ (T (x (φ n)) : E)) atTop (𝓝 (T ⟨a, haC⟩ : E)) :=
    (continuous_subtype_val.tendsto _).comp ((hT.tendsto ⟨a, haC⟩).comp hxC)
  exact ⟨⟨a, haC⟩, Subtype.ext (tendsto_nhds_unique hTlim ha_lim)⟩

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

set_option warn.sorry false in
/-- **35.21**: Browder–Göhde–Kirk requires uniform convexity of the Banach space,
not compactness of the nonexpansive map. -/
theorem exists_fixedPoint_nonexpansive {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [UniformConvexSpace E]
    {C : Set E} (hne : C.Nonempty) (hclosed : IsClosed C) (hbounded : Bornology.IsBounded C)
    (hc : Convex ℝ C) (T : C → C) (hT : LipschitzWith 1 T) : ∃ x : C, T x = x := by
  sorry

end CKMA
