/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Order.Filter.Basic
public import Mathlib.Tactic

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Normed.Operator.NNNorm
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Connected.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.UniformSpace.CompactConvergence
import Mathlib.Topology.UniformSpace.UniformEmbedding
import TauCeti.Topology.MetricSpace.Ekeland

/-!
# Palais–Smale compactness and mountain-pass critical points

Continuous paths from zero to a second well define the mountain-pass minimax level.
Positive energy on a separating sphere and negative endpoint energy give a positive
barrier. A C¹ functional on a real Banach space has a critical point at this level
when the Palais–Smale subsequence condition holds there. Compact paths, derivatives
and filter convergence use Mathlib. The deformation is a straight-line push by a
continuous pathwise pseudogradient, built from the operator norm on a finite chart
of the maximum set. Ekeland's principle selects the path, in the form
`LowerSemicontinuous.exists_add_mul_dist_le_and_lt_add_mul_dist` from
`TauCeti.Topology.MetricSpace.Ekeland`. Source: GAPS 36.35.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Filter Topology Set Metric ContinuousLinearMap Finset
open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The Palais–Smale condition at a real energy level, with strong convergence of a subsequence. -/
def HasPalaisSmaleAt (I : E → ℝ) (c : ℝ) : Prop :=
  ∀ u : ℕ → E, Tendsto (fun n ↦ I (u n)) atTop (𝓝 c) →
    Tendsto (fun n ↦ fderiv ℝ I (u n)) atTop (𝓝 0) →
    ∃ (φ : ℕ → ℕ) (x : E), StrictMono φ ∧ Tendsto (u ∘ φ) atTop (𝓝 x)

/-- Continuous paths joining zero to the second well, parameterized on `[0,1]`. -/
def mountainPassPaths (e : E) : Set C(Set.Icc (0 : ℝ) 1, E) :=
  {γ | γ ⟨0, by norm_num⟩ = 0 ∧ γ ⟨1, by norm_num⟩ = e}

/-- The real supremum of energy along a compact path. When the energy functional
is continuous, as in the mountain-pass theorem, this is its attained maximum. -/
def pathMaxEnergy (I : E → ℝ) (γ : C(Set.Icc (0 : ℝ) 1, E)) : ℝ :=
  sSup (Set.range (fun t ↦ I (γ t)))

/-- The mountain-pass minimax level. Under the theorem's hypotheses the infimum is finite
and every path crosses the positive-energy sphere. -/
def mountainPassLevel (I : E → ℝ) (e : E) : ℝ :=
  sInf (pathMaxEnergy I '' mountainPassPaths e)

omit [NormedSpace ℝ E] in
/-- A continuous real energy is bounded above along a compact path. -/
private lemma bddAbove_pathEnergy {I : E → ℝ} (hI : Continuous I) (γ : C(Set.Icc (0 : ℝ) 1, E)) :
    BddAbove (range fun t ↦ I (γ t)) :=
  (isCompact_range (hI.comp γ.continuous)).bddAbove

omit [NormedSpace ℝ E] in
/-- Energy along a path is at most the path maximum. -/
private lemma le_pathMaxEnergy {I : E → ℝ} (hI : Continuous I) (γ : C(Set.Icc (0 : ℝ) 1, E))
    (t : Set.Icc (0 : ℝ) 1) : I (γ t) ≤ pathMaxEnergy I γ :=
  le_csSup (bddAbove_pathEnergy hI γ) (mem_range_self t)

omit [NormedSpace ℝ E] in
/-- A continuous energy attains its supremum on a compact path. -/
private lemma exists_eq_pathMaxEnergy {I : E → ℝ} (hI : Continuous I)
    (γ : C(Set.Icc (0 : ℝ) 1, E)) :
    ∃ t, I (γ t) = pathMaxEnergy I γ :=
  (isCompact_range (hI.comp γ.continuous)).sSup_mem ⟨I (γ ⟨0, by norm_num⟩), mem_range_self _⟩

/-- The straight-line path from `0` to `e`. -/
private def straightMountainPassPath (e : E) : C(Set.Icc (0 : ℝ) 1, E) :=
  ⟨fun t ↦ (t : ℝ) • e, continuous_subtype_val.smul continuous_const⟩

/-- The straight-line path joins `0` to `e`. -/
private lemma straightMountainPassPath_mem (e : E) :
    straightMountainPassPath e ∈ mountainPassPaths e := by
  constructor
  · simp [straightMountainPassPath]
  · simp [straightMountainPassPath]

omit [NormedSpace ℝ E] in
/-- Every continuous path from `0` to `e` meets the sphere of radius `r`. -/
private lemma exists_norm_eq_radius {e : E} {γ : C(Set.Icc (0 : ℝ) 1, E)}
    (hγ : γ ∈ mountainPassPaths e) {r : ℝ} (hr : 0 < r) (he : r < ‖e‖) :
    ∃ t, ‖γ t‖ = r := by
  let _ : ConnectedSpace (Set.Icc (0 : ℝ) 1) :=
    Subtype.connectedSpace (isConnected_Icc (zero_le_one : (0 : ℝ) ≤ 1))
  let f : Set.Icc (0 : ℝ) 1 → ℝ := fun t ↦ ‖γ t‖
  have hf : Continuous f := continuous_norm.comp γ.continuous
  have hpt0 (h : (0 : ℝ) ∈ Icc (0 : ℝ) 1) : γ ⟨0, h⟩ = 0 := by
    simpa [show (⟨0, h⟩ : Set.Icc (0 : ℝ) 1) = ⟨0, by norm_num⟩ from Subtype.ext rfl] using hγ.1
  have hpt1 (h : (1 : ℝ) ∈ Icc (0 : ℝ) 1) : γ ⟨1, h⟩ = e := by
    simpa [show (⟨1, h⟩ : Set.Icc (0 : ℝ) 1) = ⟨1, by norm_num⟩ from Subtype.ext rfl] using hγ.2
  have h0 : (0 : ℝ) ∈ range f := by
    refine ⟨⟨0, by norm_num⟩, ?_⟩
    simp only [f]
    rw [hpt0]
    simp
  have he' : ‖e‖ ∈ range f := by
    refine ⟨⟨1, by norm_num⟩, ?_⟩
    simp only [f]
    rw [hpt1]
  exact (isConnected_range hf).Icc_subset h0 he' ⟨hr.le, he.le⟩

omit [NormedSpace ℝ E] in
/-- Mountain-pass geometry forces every admissible path to reach energy at least `α`. -/
private lemma pathMaxEnergy_ge_barrier {I : E → ℝ} (hI : Continuous I) {e : E}
    {γ : C(Set.Icc (0 : ℝ) 1, E)} (hγ : γ ∈ mountainPassPaths e) {r α : ℝ} (hr : 0 < r)
    (hbarrier : ∀ x : E, ‖x‖ = r → α ≤ I x) (he : r < ‖e‖) :
    α ≤ pathMaxEnergy I γ := by
  obtain ⟨t, ht⟩ := exists_norm_eq_radius hγ hr he
  exact (hbarrier (γ t) ht).trans (le_pathMaxEnergy hI γ t)

/-- The minimax level is at least the barrier, once the path set is nonempty and bounded below. -/
private lemma mountainPassLevel_ge {I : E → ℝ} (hI : Continuous I) {e : E} {r α : ℝ} (hr : 0 < r)
    (hbarrier : ∀ x : E, ‖x‖ = r → α ≤ I x) (he : r < ‖e‖) :
    α ≤ mountainPassLevel I e := by
  have hne : (pathMaxEnergy I '' mountainPassPaths e).Nonempty :=
    ⟨pathMaxEnergy I (straightMountainPassPath e),
      mem_image_of_mem _ (straightMountainPassPath_mem e)⟩
  refine le_csInf hne ?_
  rintro _ ⟨γ, hγ, rfl⟩
  exact pathMaxEnergy_ge_barrier hI hγ hr hbarrier he

omit [NormedSpace ℝ E] in
/-- The path maximum is lower semicontinuous for the supremum metric. -/
private lemma pathMaxEnergy_lowerSemicontinuous {I : E → ℝ} (hI : Continuous I) :
    LowerSemicontinuous (pathMaxEnergy I) := by
  rw [lowerSemicontinuous_iff]
  intro γ
  rw [lowerSemicontinuousAt_iff]
  intro y hy
  obtain ⟨t, ht⟩ := exists_eq_pathMaxEnergy hI γ
  have hyt : y < I (γ t) := ht ▸ hy
  have hcont : Continuous fun σ : C(Set.Icc (0 : ℝ) 1, E) ↦ I (σ t) :=
    hI.comp (continuous_eval_const t)
  filter_upwards [(hcont.tendsto γ).eventually (eventually_gt_nhds hyt)] with σ hσ
  exact hσ.trans_le (le_pathMaxEnergy hI σ t)

omit [NormedSpace ℝ E] in
/-- Endpoint constraints cut out a closed subset of the path space. -/
private lemma isClosed_mountainPassPaths (e : E) : IsClosed (mountainPassPaths e) :=
  (isClosed_eq (continuous_eval_const _) continuous_const).inter
    (isClosed_eq (continuous_eval_const _) continuous_const)

/-- A value below the operator norm is attained, with the sign chosen so the pairing is positive. -/
private lemma exists_apply_gt_of_lt_opNorm {f : E →L[ℝ] ℝ} {c : ℝ} (hc : c < ‖f‖) :
    ∃ v : E, ‖v‖ < 1 ∧ c < f v := by
  obtain ⟨v, hv, hvf⟩ := f.exists_lt_apply_of_lt_opNorm hc
  by_cases h : c < f v
  · exact ⟨v, hv, h⟩
  · have hle : f v ≤ c := le_of_not_gt h
    have habs : c < |f v| := by simpa [Real.norm_eq_abs] using hvf
    have hneg : f v < 0 := by
      by_contra hnn
      rw [abs_of_nonneg (le_of_not_gt hnn)] at habs
      linarith
    refine ⟨-v, by simpa using hv, ?_⟩
    rw [map_neg]
    rw [abs_of_neg hneg] at habs
    exact habs

/-- Near a point where the derivative is large, one direction of norm less than one keeps a
definite pairing. -/
private lemma exists_direction_ball {I : E → ℝ} (hI : ContDiff ℝ 1 I) {κ : ℝ} {x : E}
    (hx : κ < ‖fderiv ℝ I x‖) :
    ∃ v : E, ‖v‖ < 1 ∧ κ < (fderiv ℝ I x) v ∧
      ∃ ρ > 0, ∀ u, ‖u - x‖ < ρ → κ < (fderiv ℝ I u) v := by
  obtain ⟨v, hv, hvf⟩ := exists_apply_gt_of_lt_opNorm hx
  have hcont : Continuous fun u : E ↦ (fderiv ℝ I u) v :=
    (hI.continuous_fderiv_apply one_ne_zero).comp (continuous_id.prodMk continuous_const)
  have hgap : 0 < (fderiv ℝ I x) v - κ := sub_pos.mpr hvf
  obtain ⟨ρ, hρ, hρu⟩ := Metric.continuousAt_iff.mp hcont.continuousAt _ hgap
  refine ⟨v, hv, hvf, ρ, hρ, fun u hu ↦ ?_⟩
  have hdist := hρu (x := u) (by simpa [dist_eq_norm] using hu)
  rw [Real.dist_eq, abs_lt] at hdist
  linarith

/-- A chart along a path: the same direction works uniformly for nearby parameters and nearby
points, on a time interval that misses the endpoints. -/
private lemma exists_chart_along_path {I : E → ℝ} (hI : ContDiff ℝ 1 I) {κ : ℝ}
    (γ : C(Set.Icc (0 : ℝ) 1, E))
    {t : Set.Icc (0 : ℝ) 1} (ht0 : 0 < t.1) (ht1 : t.1 < 1)
    (hderiv : κ < ‖fderiv ℝ I (γ t)‖) :
    ∃ v : E, ‖v‖ < 1 ∧ κ < (fderiv ℝ I (γ t)) v ∧
      ∃ ρ > 0, ∃ η > 0, η < min t.1 (1 - t.1) ∧
        ∀ s, dist s t < η → ∀ u, ‖u - γ s‖ < ρ → κ < (fderiv ℝ I u) v := by
  obtain ⟨v, hv, hvf, ρ0, hρ0, hnear⟩ := exists_direction_ball hI hderiv
  obtain ⟨δ, hδ, hδγ⟩ :=
    Metric.continuousAt_iff.mp γ.continuous.continuousAt (ρ0 / 2) (half_pos hρ0)
  have hminpos : 0 < min t.1 (1 - t.1) := lt_min ht0 (sub_pos.mpr ht1)
  let η : ℝ := min (δ / 2) (min t.1 (1 - t.1) / 2)
  refine ⟨v, hv, hvf, ρ0 / 2, half_pos hρ0, η, ?_, ?_, ?_⟩
  · exact lt_min (half_pos hδ) (half_pos hminpos)
  · exact lt_of_le_of_lt (min_le_right _ _) (half_lt_self hminpos)
  · intro s hs u hu
    have hdist : dist s t < δ :=
      lt_of_le_of_lt (le_of_lt hs |>.trans (min_le_left _ _)) (half_lt_self hδ)
    have hγs : dist (γ s) (γ t) < ρ0 / 2 := hδγ (x := s) hdist
    have hu' : ‖u - γ t‖ < ρ0 := by
      calc ‖u - γ t‖ ≤ ‖u - γ s‖ + ‖γ s - γ t‖ := by
            simpa [dist_eq_norm] using dist_triangle u (γ s) (γ t)
        _ < ρ0 / 2 + ρ0 / 2 := add_lt_add hu (by simpa [dist_eq_norm] using hγs)
        _ = ρ0 := by ring
    exact hnear u hu'

/-- Derivative of energy along the affine segment `s ↦ x - s • v`. -/
private lemma deriv_energySegment {I : E → ℝ} (hI : ContDiff ℝ 1 I) (x v : E) (τ : ℝ) :
    deriv (fun s : ℝ ↦ I (x - s • v)) τ = -((fderiv ℝ I (x - τ • v)) v) := by
  let path : ℝ → E := fun s ↦ x - s • v
  have hpath : HasDerivAt path (-v) τ := by
    simpa [path] using ((hasDerivAt_id τ).smul_const v).const_sub x
  have hdI : DifferentiableAt ℝ I (path τ) :=
    (contDiff_one_iff_fderiv.mp hI).1.differentiableAt
  have hcomp := fderiv_comp_deriv (x := τ) (f := path) (l := I) hdI hpath.differentiableAt
  rw [hpath.deriv, map_neg, Function.comp_def] at hcomp
  simpa [path] using hcomp

/-- If the derivative pairs with `v` by at least `κ` on the segment, the energy drops by at least
`κ` times the step. -/
private lemma energy_along_segment_le {I : E → ℝ} (hI : ContDiff ℝ 1 I) (x v : E) {h κ : ℝ}
    (hh : 0 ≤ h) (hdown : ∀ τ ∈ Icc (0 : ℝ) h, κ ≤ (fderiv ℝ I (x - τ • v)) v) :
    I (x - h • v) ≤ I x - κ * h := by
  let φ : ℝ → ℝ := fun τ ↦ I (x - τ • v)
  have hderiv : ∀ τ ∈ interior (Icc (0 : ℝ) h), deriv φ τ ≤ -κ := by
    intro τ hτ
    calc deriv φ τ = -((fderiv ℝ I (x - τ • v)) v) := deriv_energySegment hI x v τ
      _ ≤ -κ := neg_le_neg (hdown τ (interior_subset hτ))
  have hcont : ContinuousOn φ (Icc (0 : ℝ) h) :=
    (hI.continuous.comp
      (continuous_const.sub (continuous_id.smul continuous_const))).continuousOn
  have hdiff : DifferentiableOn ℝ φ (interior (Icc (0 : ℝ) h)) := by
    intro τ _
    exact (((contDiff_one_iff_fderiv.mp hI).1.differentiableAt).comp τ
      (((hasDerivAt_id τ).smul_const v).const_sub x).differentiableAt).differentiableWithinAt
  have hineq := Convex.image_sub_le_mul_sub_of_deriv_le (convex_Icc (0 : ℝ) h) hcont hdiff hderiv
    0 (left_mem_Icc.mpr hh) h (right_mem_Icc.mpr hh) hh
  have hsub : φ h - φ 0 ≤ -κ * h := by simpa [φ, sub_zero] using hineq
  have hφ0 : φ 0 = I x := by simp [φ]
  have hφh : φ h = I (x - h • v) := rfl
  linarith

/-- A bound on the directional derivative controls the energy change along a short segment. -/
private lemma abs_energy_segment_le {I : E → ℝ} (hI : ContDiff ℝ 1 I) (x v : E) {h C : ℝ}
    (hh : 0 ≤ h) (hbound : ∀ τ ∈ Ico (0 : ℝ) h, ‖(fderiv ℝ I (x - τ • v)) v‖ ≤ C) :
    |I (x - h • v) - I x| ≤ C * h := by
  let φ : ℝ → ℝ := fun τ ↦ I (x - τ • v)
  have hmem : ∀ τ ∈ interior (Icc (0 : ℝ) h), τ ∈ Ico (0 : ℝ) h := by
    intro τ hτ
    rw [interior_Icc] at hτ
    exact Ioo_subset_Ico_self hτ
  have habs : ∀ τ ∈ interior (Icc (0 : ℝ) h), |deriv φ τ| ≤ C := by
    intro τ hτ
    rw [deriv_energySegment hI x v τ, abs_neg]
    simpa [Real.norm_eq_abs] using hbound τ (hmem τ hτ)
  have hle : ∀ τ ∈ interior (Icc (0 : ℝ) h), deriv φ τ ≤ C :=
    fun τ hτ ↦ (abs_le.mp (habs τ hτ)).2
  have hge : ∀ τ ∈ interior (Icc (0 : ℝ) h), -C ≤ deriv φ τ :=
    fun τ hτ ↦ (abs_le.mp (habs τ hτ)).1
  have hcont : ContinuousOn φ (Icc (0 : ℝ) h) :=
    (hI.continuous.comp
      (continuous_const.sub (continuous_id.smul continuous_const))).continuousOn
  have hdiff : DifferentiableOn ℝ φ (interior (Icc (0 : ℝ) h)) := by
    intro τ _
    exact (((contDiff_one_iff_fderiv.mp hI).1.differentiableAt).comp τ
      (((hasDerivAt_id τ).smul_const v).const_sub x).differentiableAt).differentiableWithinAt
  have hupper := Convex.image_sub_le_mul_sub_of_deriv_le (convex_Icc (0 : ℝ) h) hcont hdiff hle
    0 (left_mem_Icc.mpr hh) h (right_mem_Icc.mpr hh) hh
  have hlower := Convex.mul_sub_le_image_sub_of_le_deriv (convex_Icc (0 : ℝ) h) hcont hdiff hge
    0 (left_mem_Icc.mpr hh) h (right_mem_Icc.mpr hh) hh
  rw [abs_le]
  constructor
  · linarith [by simpa [φ, sub_zero] using hlower]
  · linarith [by simpa [φ, sub_zero] using hupper]

/-- Piecewise-linear tent of radius `η` about `center`, vanishing outside that interval. -/
private def mountainPassTent (center η x : ℝ) : ℝ :=
  max 0 (min (x - (center - η)) ((center + η) - x))

/-- The tent map is nonnegative. -/
private lemma mountainPassTent_nonneg (center η x : ℝ) : 0 ≤ mountainPassTent center η x :=
  le_max_left _ _

/-- The tent vanishes once `|x - center|` is at least `η`. -/
private lemma mountainPassTent_eq_zero_of_abs_ge {center η x : ℝ} (h : η ≤ |x - center|) :
    mountainPassTent center η x = 0 := by
  have hmin : min (x - (center - η)) ((center + η) - x) ≤ 0 := by
    rcases le_total 0 (x - center) with h0 | h0
    · rw [abs_of_nonneg h0] at h
      exact le_trans (min_le_right _ _) (by linarith)
    · rw [abs_of_nonpos h0] at h
      exact le_trans (min_le_left _ _) (by linarith)
  exact max_eq_left hmin

/-- The tent is positive exactly on the open interval of radius `η`. -/
private lemma mountainPassTent_pos {center η x : ℝ} :
    0 < mountainPassTent center η x ↔ |x - center| < η := by
  rw [mountainPassTent, lt_max_iff, lt_min_iff, abs_lt]
  constructor
  · rintro (h0 | ⟨hleft, hright⟩)
    · exact absurd h0 (lt_irrefl _)
    · constructor <;> linarith
  · intro ⟨hleft, hright⟩
    exact Or.inr ⟨by linarith, by linarith⟩

/-- The tent depends continuously on the base point. -/
private lemma continuous_mountainPassTent (center η : ℝ) :
    Continuous (mountainPassTent center η) := by
  unfold mountainPassTent
  exact continuous_const.max
    ((continuous_id.sub continuous_const).min (continuous_const.sub continuous_id))

omit [NormedSpace ℝ E] in
/-- Endpoint constraints cut out a complete space of paths once `E` is complete. -/
private lemma completeSpace_mountainPassPaths (e : E) [CompleteSpace E] :
    CompleteSpace (mountainPassPaths e) := by
  let _ : IsClosed (mountainPassPaths e) := isClosed_mountainPassPaths e
  infer_instance

/-- An admissible path obeying the Ekeland slope bound has a maximum point whose derivative
is at most that slope. Both endpoints stay fixed: their energy lies strictly below the maximum,
so the supporting tents never move them. -/
private lemma exists_small_fderiv_of_slope {I : E → ℝ} (hI : ContDiff ℝ 1 I) {e : E}
    {γ : C(Set.Icc (0 : ℝ) 1, E)} (hγ : γ ∈ mountainPassPaths e) {κ : ℝ} (hκ : 0 < κ)
    (hslope : ∀ σ, σ ∈ mountainPassPaths e →
      pathMaxEnergy I γ ≤ pathMaxEnergy I σ + κ * dist σ γ)
    (h0 : I (γ ⟨0, by norm_num⟩) < pathMaxEnergy I γ)
    (h1 : I (γ ⟨1, by norm_num⟩) < pathMaxEnergy I γ) :
    ∃ t, I (γ t) = pathMaxEnergy I γ ∧ ‖fderiv ℝ I (γ t)‖ ≤ κ := by
  by_contra! hbad
  let m : ℝ := pathMaxEnergy I γ
  have hIc : Continuous I := hI.continuous
  let M : Set (Set.Icc (0 : ℝ) 1) := {t | I (γ t) = m}
  have hMcomp : IsCompact M :=
    (isClosed_eq (hIc.comp γ.continuous) continuous_const).isCompact
  obtain ⟨tM, htM⟩ := exists_eq_pathMaxEnergy hIc γ
  have hMne : M.Nonempty := ⟨tM, htM⟩
  have h0not : (⟨0, by norm_num⟩ : Set.Icc (0 : ℝ) 1) ∉ M := by
    intro ht
    exact h0.ne (by simpa [M] using ht)
  have h1not : (⟨1, by norm_num⟩ : Set.Icc (0 : ℝ) 1) ∉ M := by
    intro ht
    exact h1.ne (by simpa [M] using ht)
  have ht_pos (t : M) : 0 < t.1.1 := by
    refine lt_of_le_of_ne t.1.2.1 ?_
    intro h
    have ht0 : t.1 = ⟨0, by norm_num⟩ :=
      Subtype.coe_injective (by simpa using h.symm)
    exact h0not (ht0 ▸ t.2)
  have ht_lt (t : M) : t.1.1 < 1 := by
    refine lt_of_le_of_ne t.1.2.2 ?_
    intro h
    have ht1 : t.1 = ⟨1, by norm_num⟩ := Subtype.coe_injective (by simpa using h)
    exact h1not (ht1 ▸ t.2)
  have hdata (t : M) : ∃ v : E, ‖v‖ < 1 ∧ κ < (fderiv ℝ I (γ t.1)) v ∧
      ∃ ρ > 0, ∃ η > 0, η < min t.1.1 (1 - t.1.1) ∧
        ∀ s, dist s t.1 < η → ∀ u, ‖u - γ s‖ < ρ → κ < (fderiv ℝ I u) v :=
    exists_chart_along_path hI γ (ht_pos t) (ht_lt t) (hbad t.1 t.2)
  choose v hvnorm hvpair ρ hρ η hη hηlt hnear using hdata
  have hcover : M ⊆ ⋃ i : M, ball i.1 (η i) := by
    intro t ht
    exact mem_iUnion.2 ⟨⟨t, ht⟩, mem_ball_self (hη ⟨t, ht⟩)⟩
  obtain ⟨s, hscover⟩ := hMcomp.elim_finite_subcover (fun i : M ↦ ball i.1 (η i))
    (fun _ ↦ isOpen_ball) hcover
  have hsne : s.Nonempty := by
    obtain ⟨t0, ht0⟩ := hMne
    obtain ⟨i, hi, _⟩ := mem_iUnion₂.mp (hscover ht0)
    exact ⟨i, hi⟩
  let θ : ℝ := s.sup' hsne fun i ↦ ‖v i‖
  have hθ : θ < 1 := (Finset.sup'_lt_iff hsne).2 fun i _ ↦ hvnorm i
  have hθ0 : 0 ≤ θ := by
    obtain ⟨i, hi⟩ := hsne
    exact (norm_nonneg _).trans (Finset.le_sup' (fun j ↦ ‖v j‖) hi)
  let g : Set.Icc (0 : ℝ) 1 → ℝ := fun t ↦ ∑ i ∈ s, mountainPassTent i.1.1 (η i) t.1
  have hgcont : Continuous g :=
    continuous_finsetSum s fun i _ ↦ (continuous_mountainPassTent _ _).comp continuous_subtype_val
  let s0 : ℝ := sInf (g '' M)
  have hs0pos : 0 < s0 := by
    have hne : (g '' M).Nonempty := hMne.image g
    have hmem : s0 ∈ g '' M := (hMcomp.image hgcont).sInf_mem hne
    obtain ⟨t, ht, htval⟩ := hmem
    obtain ⟨i, hi, hball⟩ := mem_iUnion₂.mp (hscover ht)
    have htent : 0 < mountainPassTent i.1.1 (η i) t.1 := by
      rw [mountainPassTent_pos, ← Real.dist_eq, ← Subtype.dist_eq]
      exact hball
    have hgt : 0 < g t := by
      unfold g
      refine lt_of_lt_of_le htent ?_
      exact Finset.single_le_sum
        (fun j _ ↦ mountainPassTent_nonneg j.1.1 (η j) t.1) hi
    exact htval.symm ▸ hgt
  have htent0 (i : M) : mountainPassTent i.1.1 (η i) 0 = 0 :=
    mountainPassTent_eq_zero_of_abs_ge <| by
      rw [abs_sub_comm, sub_zero, abs_of_nonneg i.1.2.1]
      exact (hηlt i).le.trans (min_le_left _ _)
  have htent1 (i : M) : mountainPassTent i.1.1 (η i) 1 = 0 := by
    apply mountainPassTent_eq_zero_of_abs_ge
    rw [abs_of_nonneg (sub_nonneg.mpr i.1.2.2)]
    exact (lt_of_lt_of_le (hηlt i) (min_le_right _ _)).le
  let weight : M → Set.Icc (0 : ℝ) 1 → ℝ :=
    fun i t ↦ mountainPassTent i.1.1 (η i) t.1 / max (g t) (s0 / 2)
  have hdenpos (t : Set.Icc (0 : ℝ) 1) : 0 < max (g t) (s0 / 2) :=
    lt_of_lt_of_le (half_pos hs0pos) (le_max_right _ _)
  have hwnn (i : M) (t : Set.Icc (0 : ℝ) 1) : 0 ≤ weight i t :=
    div_nonneg (mountainPassTent_nonneg _ _ _) (hdenpos t).le
  have hweight (i : M) : Continuous (weight i) := by
    refine Continuous.div ((continuous_mountainPassTent _ _).comp continuous_subtype_val)
      (hgcont.max continuous_const) fun t ↦ (hdenpos t).ne'
  have hsum_le (t : Set.Icc (0 : ℝ) 1) : ∑ i ∈ s, weight i t ≤ 1 := by
    by_cases ht : s0 / 2 ≤ g t
    · have hgpos : 0 < g t := lt_of_lt_of_le (half_pos hs0pos) ht
      have : ∑ i ∈ s, weight i t = 1 := by
        simp only [weight, max_eq_left ht, ← Finset.sum_div, g]
        exact div_self hgpos.ne'
      exact this.le
    · push Not at ht
      simp only [weight, max_eq_right ht.le, ← Finset.sum_div, g]
      rw [div_le_one₀ (half_pos hs0pos)]
      exact ht.le
  have hsum_one {t : Set.Icc (0 : ℝ) 1} (ht : s0 / 2 ≤ g t) : ∑ i ∈ s, weight i t = 1 := by
    have hgpos : 0 < g t := lt_of_lt_of_le (half_pos hs0pos) ht
    simp only [weight, max_eq_left ht, ← Finset.sum_div, g]
    exact div_self hgpos.ne'
  let w : Set.Icc (0 : ℝ) 1 → E := fun t ↦ ∑ i ∈ s, weight i t • v i
  have hw : Continuous w :=
    continuous_finsetSum s fun i _ ↦ (hweight i).smul continuous_const
  have hw_le (t : Set.Icc (0 : ℝ) 1) : ‖w t‖ ≤ θ := by
    calc ‖w t‖ ≤ ∑ i ∈ s, ‖weight i t • v i‖ := norm_sum_le _ _
      _ = ∑ i ∈ s, |weight i t| * ‖v i‖ := by simp_rw [norm_smul, Real.norm_eq_abs]
      _ ≤ ∑ i ∈ s, weight i t * θ := by
          refine Finset.sum_le_sum fun i hi ↦ ?_
          rw [abs_of_nonneg (hwnn i t)]
          exact mul_le_mul_of_nonneg_left (Finset.le_sup' (fun j ↦ ‖v j‖) hi) (hwnn i t)
      _ = (∑ i ∈ s, weight i t) * θ := by rw [Finset.sum_mul]
      _ ≤ 1 * θ := mul_le_mul_of_nonneg_right (hsum_le t) hθ0
      _ = θ := one_mul θ
  have hpairG (t : Set.Icc (0 : ℝ) 1) (ht : s0 / 2 ≤ g t) :
      κ < (fderiv ℝ I (γ t)) (w t) := by
    have hterm (i : M) (hi : i ∈ s) :
        weight i t * κ ≤ weight i t * (fderiv ℝ I (γ t)) (v i) := by
      by_cases hwi : weight i t = 0
      · simp [hwi]
      · have hposw : 0 < weight i t := lt_of_le_of_ne (hwnn i t) (Ne.symm hwi)
        have htent : 0 < mountainPassTent i.1.1 (η i) t.1 := by
          have hquot : 0 < weight i t := hposw
          unfold weight at hquot
          exact (div_pos_iff.mp hquot).elim (fun h ↦ h.1) fun h ↦ absurd h.2 (hdenpos t).not_gt
        have hdist : dist t i.1 < η i := by
          rw [Subtype.dist_eq, Real.dist_eq]
          exact mountainPassTent_pos.mp htent
        have hpairi : κ < (fderiv ℝ I (γ t)) (v i) :=
          hnear i t hdist (γ t) (by simpa using hρ i)
        exact mul_le_mul_of_nonneg_left hpairi.le hposw.le
    have hex : ∃ i ∈ s, weight i t * κ < weight i t * (fderiv ℝ I (γ t)) (v i) := by
      have hposw : ∃ i ∈ s, 0 < weight i t := by
        by_contra hnone
        push Not at hnone
        have hzero : ∑ i ∈ s, weight i t = 0 :=
          Finset.sum_eq_zero fun i hi ↦ le_antisymm (hnone i hi) (hwnn i t)
        rw [hsum_one ht] at hzero
        exact one_ne_zero hzero
      obtain ⟨i, hi, hwi⟩ := hposw
      have htent : 0 < mountainPassTent i.1.1 (η i) t.1 := by
        unfold weight at hwi
        exact (div_pos_iff.mp hwi).elim (fun h ↦ h.1) fun h ↦ absurd h.2 (hdenpos t).not_gt
      have hdist : dist t i.1 < η i := by
        rw [Subtype.dist_eq, Real.dist_eq]
        exact mountainPassTent_pos.mp htent
      exact ⟨i, hi, mul_lt_mul_of_pos_left (hnear i t hdist (γ t) (by simpa using hρ i)) hwi⟩
    have hsumlt := Finset.sum_lt_sum hterm hex
    have hleft : ∑ i ∈ s, weight i t * κ = κ := by rw [← Finset.sum_mul, hsum_one ht, one_mul]
    have hright : ∑ i ∈ s, weight i t * (fderiv ℝ I (γ t)) (v i) =
        (fderiv ℝ I (γ t)) (w t) := by
      simp only [w, map_sum, map_smul, smul_eq_mul, mul_comm]
    linarith
  let seg : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) 1 → E :=
    fun p ↦ γ p.1 - (p.2 : ℝ) • w p.1
  have hseg : Continuous seg :=
    (γ.continuous.comp continuous_fst).sub
      ((continuous_subtype_val.comp continuous_snd).smul (hw.comp continuous_fst))
  let normSet : Set ℝ := (fun z : E ↦ ‖fderiv ℝ I z‖) '' range seg
  have hnormCont : Continuous fun z : E ↦ ‖fderiv ℝ I z‖ :=
    continuous_norm.comp (hI.continuous_fderiv one_ne_zero)
  have hnormComp : IsCompact normSet := (isCompact_range hseg).image hnormCont
  let B : ℝ := sSup normSet
  have hB0 : 0 ≤ B := by
    obtain ⟨z, -, hz⟩ := hnormComp.sSup_mem ((range_nonempty seg).image _)
    have hz0 : 0 ≤ ‖fderiv ℝ I z‖ := norm_nonneg _
    exact le_of_le_of_eq hz0 (by simpa [B] using hz)
  have hBbdd : BddAbove normSet := hnormComp.bddAbove
  have hBle {z : E} (hz : z ∈ range seg) : ‖fderiv ℝ I z‖ ≤ B :=
    le_csSup hBbdd (mem_image_of_mem _ hz)
  let G : Set (Set.Icc (0 : ℝ) 1) := {t | s0 / 2 ≤ g t}
  have hGcomp : IsCompact G := (isClosed_le continuous_const hgcont).isCompact
  have hpoint : Continuous (fun p : Set.Icc (0 : ℝ) 1 × ℝ ↦ γ p.1 - p.2 • w p.1) :=
    (γ.continuous.comp continuous_fst).sub (continuous_snd.smul (hw.comp continuous_fst))
  have hΦ : Continuous (fun p : Set.Icc (0 : ℝ) 1 × ℝ ↦
      (fderiv ℝ I (γ p.1 - p.2 • w p.1)) (w p.1)) :=
    (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := E) (F := ℝ)).continuous.comp
      (((hI.continuous_fderiv one_ne_zero).comp hpoint).prodMk (hw.comp continuous_fst))
  let u : Set (Set.Icc (0 : ℝ) 1 × ℝ) :=
    {p | κ < (fderiv ℝ I (γ p.1 - p.2 • w p.1)) (w p.1)}
  have hu : IsOpen u := isOpen_lt continuous_const hΦ
  have htube : G ×ˢ {(0 : ℝ)} ⊆ u := by
    intro p hp
    have hp0 : p.2 = 0 := by simpa using hp.2
    have : κ < (fderiv ℝ I (γ p.1)) (w p.1) := hpairG p.1 hp.1
    simpa [u, hp0] using this
  obtain ⟨_, u2, -, hu2, hGu, h0set, hprod⟩ :=
    generalized_tube_lemma hGcomp (isCompact_singleton (x := (0 : ℝ))) hu htube
  obtain ⟨ε, hε, hεball⟩ := Metric.mem_nhds_iff.mp (hu2.mem_nhds (h0set rfl))
  let F : Set (Set.Icc (0 : ℝ) 1) := {t | g t ≤ s0 / 2}
  have hFcomp : IsCompact F := (isClosed_le hgcont continuous_const).isCompact
  have hg0 : g ⟨0, by norm_num⟩ = 0 := by simp [g, htent0]
  have hFne : F.Nonempty := by
    refine ⟨⟨0, by norm_num⟩, ?_⟩
    show g ⟨0, by norm_num⟩ ≤ s0 / 2
    rw [hg0]
    exact (half_pos hs0pos).le
  let mF : ℝ := sSup ((fun t ↦ I (γ t)) '' F)
  have hmF : mF < m := by
    have himg : IsCompact ((fun t ↦ I (γ t)) '' F) :=
      hFcomp.image (hIc.comp γ.continuous)
    obtain ⟨t, htF, ht⟩ := himg.sSup_mem (hFne.image _)
    have hlt : I (γ t) < m := by
      have hnot : t ∉ M := by
        intro htM
        have hgle : s0 ≤ g t :=
          csInf_le (hMcomp.image hgcont).bddBelow (mem_image_of_mem g htM)
        have hgt : g t < s0 := (htF : g t ≤ s0 / 2).trans_lt (half_lt_self hs0pos)
        exact hgt.not_ge hgle
      exact lt_of_le_of_ne (le_pathMaxEnergy hIc γ t) (by intro h; exact hnot h)
    simpa [mF, ht] using hlt
  have hEnergy_pos : 0 < (m - mF) / (B + κ) :=
    div_pos (sub_pos.mpr hmF) (by linarith [hB0, hκ])
  let hstep : ℝ := min (ε / 2) (min ((m - mF) / (B + κ)) 1)
  have hhstep : 0 < hstep :=
    lt_min (half_pos hε) (lt_min hEnergy_pos zero_lt_one)
  have hhstep_ε : hstep ≤ ε / 2 := min_le_left _ _
  have hhstep_E : hstep ≤ (m - mF) / (B + κ) := (min_le_right _ _).trans (min_le_left _ _)
  have hhstep_one : hstep ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
  have hbudget : mF + B * hstep ≤ m - κ * hstep := by
    have hmul : hstep * (B + κ) ≤ m - mF := (le_div_iff₀ (by linarith [hB0, hκ])).mp hhstep_E
    linarith
  have hw0 : w ⟨0, by norm_num⟩ = 0 := by
    simp only [w, weight]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    rw [htent0 i, zero_div, zero_smul]
  have hw1 : w ⟨1, by norm_num⟩ = 0 := by
    simp only [w, weight]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    rw [htent1 i, zero_div, zero_smul]
  let σ : C(Set.Icc (0 : ℝ) 1, E) :=
    ⟨fun t ↦ γ t - hstep • w t, γ.continuous.sub (continuous_const.smul hw)⟩
  have hσmem : σ ∈ mountainPassPaths e := by
    refine ⟨?_, ?_⟩
    · change γ _ - hstep • w _ = 0
      rw [hw0, smul_zero, sub_zero, hγ.1]
    · change γ _ - hstep • w _ = e
      rw [hw1, smul_zero, sub_zero, hγ.2]
  have hdir (t : Set.Icc (0 : ℝ) 1) {τ : ℝ} (hτ : τ ∈ Ico (0 : ℝ) hstep) :
      ‖(fderiv ℝ I (γ t - τ • w t)) (w t)‖ ≤ B := by
    have hτ1 : τ ∈ Icc (0 : ℝ) 1 := ⟨hτ.1, hτ.2.le.trans hhstep_one⟩
    have hz : γ t - τ • w t ∈ range seg := ⟨(t, ⟨τ, hτ1⟩), rfl⟩
    calc ‖(fderiv ℝ I (γ t - τ • w t)) (w t)‖
        ≤ ‖fderiv ℝ I (γ t - τ • w t)‖ * ‖w t‖ := le_opNorm _ _
      _ ≤ B * θ := mul_le_mul (hBle hz) (hw_le t) (norm_nonneg _) hB0
      _ ≤ B := mul_le_of_le_one_right hB0 hθ.le
  have hIσ (t : Set.Icc (0 : ℝ) 1) : I (σ t) ≤ m - κ * hstep := by
    by_cases htG : s0 / 2 ≤ g t
    · have hdown : ∀ τ ∈ Icc (0 : ℝ) hstep, κ ≤ (fderiv ℝ I (γ t - τ • w t)) (w t) := by
        intro τ hτ
        have hdistτ : dist τ (0 : ℝ) < ε := by
          rw [Real.dist_eq, sub_zero, abs_of_nonneg hτ.1]
          exact lt_of_le_of_lt (hτ.2.trans hhstep_ε) (half_lt_self hε)
        have hmem : (t, τ) ∈ u := hprod ⟨hGu htG, hεball hdistτ⟩
        exact le_of_lt (by simpa [u] using hmem)
      have hdrop := energy_along_segment_le hI (γ t) (w t) hhstep.le hdown
      calc I (σ t) ≤ I (γ t) - κ * hstep := by simpa [σ] using hdrop
        _ ≤ m - κ * hstep := by gcongr; exact le_pathMaxEnergy hIc γ t
    · push Not at htG
      have hγle : I (γ t) ≤ mF :=
        le_csSup (hFcomp.image (hIc.comp γ.continuous)).bddAbove
          (mem_image_of_mem _ htG.le)
      have habs := abs_energy_segment_le hI (γ t) (w t) hhstep.le (fun τ hτ ↦ hdir t hτ)
      have hup : I (σ t) ≤ I (γ t) + B * hstep := by
        have hσt : I (σ t) = I (γ t - hstep • w t) := by simp [σ]
        rw [hσt]
        linarith [(abs_le.mp habs).2]
      linarith [hbudget, hup, hγle]
  have hσmax : pathMaxEnergy I σ ≤ m - κ * hstep :=
    csSup_le (range_nonempty _) fun _ ⟨t, ht⟩ ↦ ht ▸ hIσ t
  have hdistσ : dist σ γ ≤ hstep * θ := by
    rw [ContinuousMap.dist_le (mul_nonneg hhstep.le hθ0)]
    intro t
    rw [dist_eq_norm]
    have hsub : γ t - σ t = hstep • w t := by simp [σ]
    rw [norm_sub_rev, hsub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hhstep.le]
    exact mul_le_mul_of_nonneg_left (hw_le t) hhstep.le
  have hslack : pathMaxEnergy I σ + κ * dist σ γ ≤ m - κ * hstep * (1 - θ) := by
    calc pathMaxEnergy I σ + κ * dist σ γ
        ≤ (m - κ * hstep) + κ * (hstep * θ) :=
          add_le_add hσmax (mul_le_mul_of_nonneg_left hdistσ hκ.le)
      _ = m - κ * hstep * (1 - θ) := by ring
  have hpos : 0 < κ * hstep * (1 - θ) := mul_pos (mul_pos hκ hhstep) (sub_pos.mpr hθ)
  linarith [hslope σ hσmem, hslack, hpos]

/-- **36.35**: mountain-pass geometry and Palais–Smale compactness produce a critical point
at the minimax level. The Palais–Smale condition is needed only at that level. -/
theorem exists_mountainPass_criticalPoint [CompleteSpace E] (I : E → ℝ)
    (hI : ContDiff ℝ 1 I) (hzero : I 0 = 0) {r α : ℝ} (hr : 0 < r) (hα : 0 < α)
    (hbarrier : ∀ x : E, ‖x‖ = r → α ≤ I x) {e : E} (he : r < ‖e‖)
    (hIe : I e < 0) (hPS : HasPalaisSmaleAt I (mountainPassLevel I e)) :
    α ≤ mountainPassLevel I e ∧ ∃ x, I x = mountainPassLevel I e ∧ fderiv ℝ I x = 0 := by
  have hIc : Continuous I := hI.continuous
  have hlevel : α ≤ mountainPassLevel I e := mountainPassLevel_ge hIc hr hbarrier he
  let c : ℝ := mountainPassLevel I e
  have hne : (pathMaxEnergy I '' mountainPassPaths e).Nonempty :=
    ⟨pathMaxEnergy I (straightMountainPassPath e),
      mem_image_of_mem _ (straightMountainPassPath_mem e)⟩
  have hbdd : BddBelow (pathMaxEnergy I '' mountainPassPaths e) := by
    refine ⟨α, ?_⟩
    rintro _ ⟨γ, hγ, rfl⟩
    exact pathMaxEnergy_ge_barrier hIc hγ hr hbarrier he
  let _ : CompleteSpace (mountainPassPaths e) := completeSpace_mountainPassPaths e
  have hnear : ∀ n : ℕ, ∃ x : E, c ≤ I x ∧ I x < c + 1 / ((n : ℝ) + 1) ∧
      ‖fderiv ℝ I x‖ ≤ 1 / ((n : ℝ) + 1) := by
    intro n
    let κ : ℝ := 1 / ((n : ℝ) + 1)
    have hκ : 0 < κ := by positivity
    obtain ⟨_, ⟨γ0, hγ0, rfl⟩, hγ0lt⟩ :=
      exists_lt_of_csInf_lt hne (lt_add_of_pos_right c hκ)
    let φ : mountainPassPaths e → ℝ := fun γ ↦ pathMaxEnergy I γ.1
    have hφ : LowerSemicontinuous φ :=
      (pathMaxEnergy_lowerSemicontinuous hIc).comp continuous_subtype_val
    have hbddφ : BddBelow (range φ) := by
      refine ⟨α, ?_⟩
      rintro _ ⟨γ, rfl⟩
      exact pathMaxEnergy_ge_barrier hIc γ.2 hr hbarrier he
    obtain ⟨y, hy, hslope⟩ :=
      hφ.exists_add_mul_dist_le_and_lt_add_mul_dist hbddφ hκ ⟨γ0, hγ0⟩
    have hy_le : φ y ≤ φ ⟨γ0, hγ0⟩ := by
      have hnn : 0 ≤ κ * dist y ⟨γ0, hγ0⟩ := mul_nonneg hκ.le dist_nonneg
      linarith
    have hy_lt : φ y < c + κ := hy_le.trans_lt hγ0lt
    have hy_ge : c ≤ φ y := csInf_le hbdd (mem_image_of_mem _ y.2)
    have hslope_all (σ : C(Set.Icc (0 : ℝ) 1, E)) (hσ : σ ∈ mountainPassPaths e) :
        pathMaxEnergy I y.1 ≤ pathMaxEnergy I σ + κ * dist σ y.1 := by
      by_cases hEq : (⟨σ, hσ⟩ : mountainPassPaths e) = y
      · have hval : σ = y.1 := congrArg Subtype.val hEq
        simp [hval, dist_self, mul_zero]
      · have hlt := hslope ⟨σ, hσ⟩ hEq
        rw [Subtype.dist_eq] at hlt
        exact hlt.le
    have h0 : I (y.1 ⟨0, by norm_num⟩) < pathMaxEnergy I y.1 := by
      calc I (y.1 ⟨0, by norm_num⟩) = I 0 := by rw [y.2.1]
        _ = 0 := hzero
        _ < α := hα
        _ ≤ pathMaxEnergy I y.1 := hlevel.trans hy_ge
    have h1 : I (y.1 ⟨1, by norm_num⟩) < pathMaxEnergy I y.1 := by
      calc I (y.1 ⟨1, by norm_num⟩) = I e := by rw [y.2.2]
        _ < 0 := hIe
        _ < α := hα
        _ ≤ pathMaxEnergy I y.1 := hlevel.trans hy_ge
    obtain ⟨t, ht, hder⟩ :=
      exists_small_fderiv_of_slope hI y.2 hκ hslope_all h0 h1
    refine ⟨y.1 t, ?_, ?_, hder⟩
    · simpa [φ, ht] using hy_ge
    · simpa [φ, ht, κ] using hy_lt
  choose x hxge hxlt hxnorm using hnear
  have hup : Tendsto (fun n : ℕ ↦ c + 1 / ((n : ℝ) + 1)) atTop (𝓝 c) := by
    simpa using (tendsto_const_nhds (x := c)).add tendsto_one_div_add_atTop_nhds_zero_nat
  have hIx : Tendsto (fun n ↦ I (x n)) atTop (𝓝 c) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun n ↦ hxge n)
      (fun n ↦ (hxlt n).le)
  have hd0 : Tendsto (fun n ↦ fderiv ℝ I (x n)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero (fun _ ↦ norm_nonneg _) (fun n ↦ hxnorm n)
      tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨φn, xLim, hmono, hlim⟩ := hPS x hIx hd0
  have hIxLim : I xLim = c := by
    have h1 : Tendsto (fun n ↦ I (x (φn n))) atTop (𝓝 (I xLim)) := (hIc.tendsto xLim).comp hlim
    have h2 : Tendsto (fun n ↦ I (x (φn n))) atTop (𝓝 c) := hIx.comp hmono.tendsto_atTop
    exact tendsto_nhds_unique h1 h2
  have hdf : fderiv ℝ I xLim = 0 := by
    have h1 : Tendsto (fun n ↦ fderiv ℝ I (x (φn n))) atTop (𝓝 (fderiv ℝ I xLim)) :=
      ((hI.continuous_fderiv one_ne_zero).tendsto xLim).comp hlim
    have h2 : Tendsto (fun n ↦ fderiv ℝ I (x (φn n))) atTop (𝓝 0) :=
      hd0.comp hmono.tendsto_atTop
    exact tendsto_nhds_unique h1 h2
  exact ⟨hlevel, xLim, hIxLim, hdf⟩

end CKMA
