/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.OrderedSpace.Representation.AL.BandProjection
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.MeasureTheory.Function.L1Space.AEEqFun
public import Mathlib.MeasureTheory.Function.SimpleFunc
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.Order.Zorn
public import Mathlib.Topology.Algebra.InfiniteSum.Group
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Topology.Algebra.InfiniteSum.Module

/-!
# Gluing of AL representations along a maximal disjoint family

A maximal pairwise lattice-disjoint family of strictly positive vectors splits an AL-space into
the ℓ¹-sum of the closed principal bands those vectors generate. Each band carries its generator
as a weak unit, so the weak-unit representation supplies an L¹ space. The disjoint union of those
carriers, with the sum of the pushed-forward measures, represents the original space. No
σ-finiteness restriction is imposed: an uncountable disjoint family is allowed, and each vector
meets only countably many bands.

## Main definitions

* `CKMA.IsPositiveDisjointFamily`: pairwise lattice-disjoint family of strictly positive vectors.
* `CKMA.maximalPositiveDisjointFamily`: chosen maximal pairwise disjoint family of strictly positive
  vectors.
* `CKMA.BandIndex`: index type of `maximalPositiveDisjointFamily`.
* `CKMA.BandComponent`: L¹ representation data for a closed principal band.
* `CKMA.indexProjection`: band projection onto the closed principal band of an index vector.

## Main results

* `CKMA.exists_maximal_positiveDisjointFamily`: Zorn existence of a maximal positive disjoint
  family.
* `CKMA.indexProjection_tsum`: every vector is the unconditional sum of its band projections.
* `CKMA.tsum_norm_indexProjection_eq`: the norms of the band projections sum to the ambient norm.
-/

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

open Metric Set Filter Topology MeasureTheory
open scoped ENNReal

namespace CKMA

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [Lattice E]
  [IsOrderedAddMonoid E] [IsOrderedModule ℝ E] [HasSolidNorm E]

/-- A pairwise lattice-disjoint family of strictly positive vectors. -/
def IsPositiveDisjointFamily (S : Set E) : Prop :=
  (∀ x ∈ S, 0 < x) ∧ S.Pairwise (fun a b => LatticeDisjoint a b)

/-- Pairwise disjoint positive families are inductive, so a maximal one exists. -/
theorem exists_maximal_positiveDisjointFamily :
    ∃ M : Set E, IsPositiveDisjointFamily M ∧ Maximal IsPositiveDisjointFamily M := by
  have hchain : ∀ c ⊆ {S : Set E | IsPositiveDisjointFamily S}, IsChain (· ⊆ ·) c →
      ∃ ub ∈ {S : Set E | IsPositiveDisjointFamily S}, ∀ s ∈ c, s ⊆ ub := by
    intro c hc hchain
    refine ⟨⋃₀ c, ?_, fun s hs => subset_sUnion_of_mem hs⟩
    constructor
    · intro x hx
      rcases hx with ⟨s, hs, hx⟩
      exact (hc hs).1 x hx
    · intro x hx y hy hxy
      rcases hx with ⟨s, hs, hx⟩
      rcases hy with ⟨t, ht, hy⟩
      by_cases hst : s = t
      · subst hst
        exact (hc hs).2 hx hy hxy
      · rcases hchain hs ht hst with hsub | hsub
        · exact (hc ht).2 (hsub hx) hy hxy
        · exact (hc hs).2 hx (hsub hy) hxy
  obtain ⟨M, hM⟩ :=
    zorn_subset (α := E) {S : Set E | IsPositiveDisjointFamily S} hchain
  rw [maximal_subset_iff] at hM
  refine ⟨M, by simpa using hM.1, maximal_subset_iff.mpr ⟨?_, ?_⟩⟩
  · simpa using hM.1
  · intro t ht hsub
    exact hM.2 (by simpa using ht) hsub

/-- A chosen maximal pairwise disjoint family of strictly positive vectors. -/
noncomputable def maximalPositiveDisjointFamily : Set E :=
  Classical.choose (exists_maximal_positiveDisjointFamily (E := E))

/-- The chosen family is a maximal positive disjoint family. -/
theorem maximalPositiveDisjointFamily_spec :
    IsPositiveDisjointFamily (E := E) maximalPositiveDisjointFamily ∧
      Maximal (fun S : Set E => IsPositiveDisjointFamily (E := E) S)
        maximalPositiveDisjointFamily :=
  Classical.choose_spec (exists_maximal_positiveDisjointFamily (E := E))

/-- Index of the chosen maximal disjoint family. -/
structure BandIndex where
  /-- Vector belonging to the family. -/
  vec : E
  /-- Proof that the vector lies in the chosen family. -/
  mem_family : vec ∈ maximalPositiveDisjointFamily

/-- Each index vector is strictly positive. -/
private theorem bandIndex_pos (i : BandIndex) : (0 : E) < i.vec :=
  (maximalPositiveDisjointFamily_spec (E := E)).1.1 i.vec i.mem_family

/-- Each index vector is nonnegative. -/
theorem bandIndex_nonneg (i : BandIndex) : (0 : E) ≤ i.vec :=
  le_of_lt (bandIndex_pos i)

/-- Distinct index vectors are lattice disjoint. -/
private theorem bandIndex_disjoint {i j : BandIndex} (hij : i ≠ j) :
    LatticeDisjoint (E := E) i.vec j.vec := by
  have hne : i.vec ≠ j.vec := by
    intro h
    apply hij
    cases i
    cases j
    cases h
    rfl
  exact (maximalPositiveDisjointFamily_spec (E := E)).1.2 i.mem_family j.mem_family hne

/-- Data of an L¹ representation of one closed principal band. -/
structure BandComponent (u : E) where
  /-- Carrier of the representation. -/
  X : Type u
  /-- Sigma-algebra on the carrier. -/
  mSpace : MeasurableSpace X
  /-- Representing measure. -/
  μ : @Measure X mSpace
  /-- Lattice isometry of the closed band onto real L¹. -/
  rep : ClosedPrincipalBand u ≃ₗᵢ[ℝ] @Lp X ℝ mSpace _ 1 μ
  /-- The isometry preserves binary suprema. -/
  preserves_sup : ∀ x y : ClosedPrincipalBand u, rep (x ⊔ y) = rep x ⊔ rep y

/-- Every nonnegative vector's closed band admits an L¹ representation. -/
theorem bandComponent_nonempty (hE : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x + y‖ = ‖x‖ + ‖y‖)
    [CompleteSpace E] {u : E} (hu : 0 ≤ u) : Nonempty (BandComponent u) := by
  let : Fact (0 ≤ u) := ⟨hu⟩
  obtain ⟨X, m, μ, U, hsup⟩ := exists_al_representation_of_weakUnit
    (E := ClosedPrincipalBand u) (ClosedPrincipalBand.isAL hE)
    ClosedPrincipalBand.unit_nonneg (closedPrincipalBand_weakUnit hE)
  exact ⟨⟨X, m, μ, U, hsup⟩⟩

/-- Chosen L¹ representation of the closed band of a nonnegative vector. -/
noncomputable def bandComponent (hE : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x + y‖ = ‖x‖ + ‖y‖)
    [CompleteSpace E] {u : E} (hu : 0 ≤ u) : BandComponent u :=
  Classical.choice (bandComponent_nonempty hE hu)

section IndexProj

variable (hE : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x + y‖ = ‖x‖ + ‖y‖) [CompleteSpace E]

/-- Projection onto the closed band of one vector of the maximal family. -/
noncomputable def indexProjection {u : E} (hu : u ∈ maximalPositiveDisjointFamily) :
    E →ₗ[ℝ] E :=
  bandProjection hE (le_of_lt ((maximalPositiveDisjointFamily_spec (E := E)).1.1 u hu))

/-- On the positive cone the index projection is the truncation limit. -/
private theorem indexProjection_apply_nonneg (i : BandIndex) {x : E} (hx : 0 ≤ x) :
    indexProjection hE i.mem_family x = posBandPart i.vec x :=
  bandProjection_apply_nonneg hE (bandIndex_nonneg i) hx

/-- Absolute value passes inside an index projection. -/
private theorem indexProjection_abs (i : BandIndex) (x : E) :
    |indexProjection hE i.mem_family x| = indexProjection hE i.mem_family |x| :=
  bandProjection_abs hE (bandIndex_nonneg i) x

/-- The index projection agrees with the continuous band projection. -/
theorem indexProjection_eq_clm (i : BandIndex) (x : E) :
    indexProjection hE i.mem_family x = (bandProjectionCLM hE (bandIndex_nonneg i)) x :=
  rfl

/-- Distinct index vectors meet in zero. -/
private theorem bandIndex_inf_eq_zero {i j : BandIndex} (hij : i ≠ j) : i.vec ⊓ j.vec =
    (0 : E) := by
  have h : LatticeDisjoint (E := E) i.vec j.vec := bandIndex_disjoint (i := i) (j := j) hij
  simpa [LatticeDisjoint, abs_of_nonneg (bandIndex_nonneg i),
    abs_of_nonneg (bandIndex_nonneg j)] using h

/-- Projections of one vector onto distinct bands are lattice disjoint. -/
private theorem indexProjection_latticeDisjoint {i j : BandIndex} (hij : i ≠ j) (x : E) :
    LatticeDisjoint (E := E) (indexProjection hE i.mem_family x)
      (indexProjection hE j.mem_family x) := by
  rw [LatticeDisjoint, indexProjection_abs hE i x, indexProjection_abs hE j x,
    indexProjection_apply_nonneg hE i (abs_nonneg x),
    indexProjection_apply_nonneg hE j (abs_nonneg x)]
  exact posBandPart_disjoint_of_disjoint hE (bandIndex_nonneg i) (bandIndex_nonneg j)
    (abs_nonneg x) (bandIndex_inf_eq_zero hij)

/-- A positive band part is disjoint from every other index vector. -/
private theorem indexProjection_inf_vec_eq_zero {i j : BandIndex} (hij : i ≠ j) {x : E}
    (hx : 0 ≤ x) :
    indexProjection hE i.mem_family x ⊓ j.vec = 0 := by
  rw [indexProjection_apply_nonneg hE i hx]
  have htrunc : ∀ n, bandTrunc i.vec x n ⊓ j.vec = 0 := by
    intro n
    refine le_antisymm ?_ (le_inf (bandTrunc_nonneg (bandIndex_nonneg i) hx n) (bandIndex_nonneg j))
    calc
      bandTrunc i.vec x n ⊓ j.vec ≤ ((n : ℝ) • i.vec) ⊓ j.vec :=
        inf_le_inf_right _ inf_le_right
      _ = 0 := inf_smul_eq_zero (Nat.cast_nonneg n) (bandIndex_nonneg i) (bandIndex_nonneg j)
        (bandIndex_inf_eq_zero hij)
  have hlim : Tendsto (fun n => bandTrunc i.vec x n ⊓ j.vec) atTop
      (𝓝 (posBandPart i.vec x ⊓ j.vec)) := by
    have hpair : Tendsto (fun n => (bandTrunc i.vec x n, j.vec)) atTop
        (𝓝 (posBandPart i.vec x, j.vec)) := by
      rw [nhds_prod_eq]
      exact (posBandPart_tendsto hE (bandIndex_nonneg i) hx).prodMk tendsto_const_nhds
    exact (continuous_inf.tendsto _).comp hpair
  exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr fun n => (htrunc n).symm)

/-- The projection onto one band kills the positive part in a different band. -/
theorem indexProjection_cross_eq_zero {i j : BandIndex} (hij : i ≠ j) {x : E} (hx : 0 ≤ x) :
    indexProjection hE j.mem_family (indexProjection hE i.mem_family x) = 0 := by
  have hnonneg : 0 ≤ indexProjection hE i.mem_family x :=
    (bandProjection_contractive hE (bandIndex_nonneg i) hx).1
  rw [indexProjection_apply_nonneg hE j hnonneg]
  exact posBandPart_eq_zero_of_disjoint hE (bandIndex_nonneg j) hnonneg
    (indexProjection_inf_vec_eq_zero hE hij hx)

include hE in
/-- Each truncation lies below the band part. -/
private theorem bandTrunc_le_posBandPart {u x : E} (hu : 0 ≤ u) (hx : 0 ≤ x) (n : ℕ) :
    bandTrunc u x n ≤ posBandPart u x := by
  apply (isClosed_Ici (a := bandTrunc u x n)).mem_of_tendsto (posBandPart_tendsto hE hu hx)
  rw [eventually_atTop]
  exact ⟨n, fun m hm => bandTrunc_mono hu hm⟩

/-- A finite sum of positive band parts is at most the vector. -/
private theorem sum_indexProjection_le {x : E} (hx : 0 ≤ x) (s : Finset BandIndex) :
    ∑ i ∈ s, indexProjection hE i.mem_family x ≤ x := by
  classical
  induction s using Finset.induction with
  | empty => simp [hx]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have hterm : ∀ i ∈ s, LatticeDisjoint (E := E) (indexProjection hE a.mem_family x)
        (indexProjection hE i.mem_family x) := by
      intro i hi
      have hne : a ≠ i := by
        intro h
        exact ha (h ▸ hi)
      exact indexProjection_latticeDisjoint hE hne x
    have hrest := latticeDisjoint_sum hterm
    have ha0 : 0 ≤ indexProjection hE a.mem_family x :=
      (bandProjection_contractive hE (bandIndex_nonneg a) hx).1
    have hs0 : 0 ≤ ∑ i ∈ s, indexProjection hE i.mem_family x :=
      Finset.sum_nonneg fun i hi => (bandProjection_contractive hE (bandIndex_nonneg i) hx).1
    have hinf : indexProjection hE a.mem_family x ⊓
        ∑ i ∈ s, indexProjection hE i.mem_family x = 0 := by
      simpa [LatticeDisjoint, abs_of_nonneg ha0, abs_of_nonneg hs0] using hrest
    rw [add_eq_sup_of_inf_eq_zero hinf]
    exact sup_le (bandProjection_contractive hE (bandIndex_nonneg a) hx).2 ih

/-- Norms add on finite sums of the band projections. -/
private theorem norm_sum_indexProjection (x : E) (s : Finset BandIndex) :
    ‖∑ i ∈ s, indexProjection hE i.mem_family x‖ =
      ∑ i ∈ s, ‖indexProjection hE i.mem_family x‖ := by
  refine norm_sum_of_pairwise_latticeDisjoint hE ?_
  intro i _hi j _hj hij
  exact indexProjection_latticeDisjoint hE hij x

/-- The real series of projection norms converges. -/
theorem summable_norm_indexProjection (x : E) :
    Summable fun i : BandIndex => ‖indexProjection hE i.mem_family x‖ := by
  refine summable_of_sum_le (c := ‖x‖) (fun i => norm_nonneg (indexProjection hE i.mem_family x)) ?_
  intro s
  have hnorm : ∀ i : BandIndex, ‖indexProjection hE i.mem_family x‖ =
      ‖indexProjection hE i.mem_family |x|‖ := by
    intro i
    rw [← norm_abs_eq_norm (indexProjection hE i.mem_family x), indexProjection_abs hE i x]
  rw [Finset.sum_congr rfl fun i _ => hnorm i, ← norm_sum_indexProjection hE |x| s]
  apply norm_le_norm_of_abs_le_abs
  have hsum0 : 0 ≤ ∑ i ∈ s, indexProjection hE i.mem_family |x| :=
    Finset.sum_nonneg fun i _ => by
      rw [indexProjection_apply_nonneg hE i (abs_nonneg x)]
      exact posBandPart_nonneg hE (bandIndex_nonneg i) (abs_nonneg x)
  rw [abs_of_nonneg hsum0]
  exact sum_indexProjection_le hE (abs_nonneg x) s

/-- The band projections of one vector form a summable family. -/
private theorem summable_indexProjection (x : E) :
    Summable fun i : BandIndex => indexProjection hE i.mem_family x :=
  Summable.of_norm (summable_norm_indexProjection hE x)

/-- A nonnegative vector is the sum of its band projections. -/
private theorem indexProjection_tsum_nonneg {x : E} (hx : 0 ≤ x) :
    ∑' (i : BandIndex), indexProjection hE i.mem_family x = x := by
  have hsumm := summable_indexProjection hE x
  set s := ∑' (i : BandIndex), indexProjection hE i.mem_family x with hs
  have hsle : s ≤ x := by
    rw [hs]
    have hmem := (isClosed_Iic (a := x)).mem_of_tendsto hsumm.hasSum
      (Eventually.of_forall fun t => sum_indexProjection_le hE hx t)
    simpa [mem_Iic] using hmem
  set r := x - s with hr
  have hr0 : 0 ≤ r := sub_nonneg.mpr hsle
  have hPk : ∀ k : BandIndex, indexProjection hE k.mem_family s =
      indexProjection hE k.mem_family x := by
    intro k
    rw [hs]
    have hzero : ∀ i : BandIndex, i ≠ k → (bandProjectionCLM hE (bandIndex_nonneg k))
        (indexProjection hE i.mem_family x) = 0 := by
      intro i hi
      rw [← indexProjection_eq_clm hE k]
      exact indexProjection_cross_eq_zero hE hi hx
    rw [indexProjection_eq_clm hE k,
      (bandProjectionCLM hE (bandIndex_nonneg k)).map_tsum hsumm,
      (hasSum_single k hzero).tsum_eq, ← indexProjection_eq_clm hE k]
    exact bandProjection_idem hE (bandIndex_nonneg k) x
  have hPr : ∀ k : BandIndex, indexProjection hE k.mem_family r = 0 := by
    intro k
    rw [hr, map_sub, hPk k, sub_self]
  suffices hr : r = 0 by
    exact (sub_eq_zero.mp hr).symm
  by_contra hne
  have hlt : (0 : E) < r := lt_of_le_of_ne hr0 (Ne.symm hne)
  have hdisj : ∀ u ∈ maximalPositiveDisjointFamily, r ⊓ u = 0 := by
    intro u hu
    let k : BandIndex := ⟨u, hu⟩
    have hle : bandTrunc u r 1 ≤ posBandPart u r :=
      bandTrunc_le_posBandPart hE (bandIndex_nonneg k) hr0 1
    have hP : posBandPart u r = 0 := by
      rw [← indexProjection_apply_nonneg hE k hr0]
      exact hPr k
    have htrunc : bandTrunc u r 1 = r ⊓ u := by simp [bandTrunc, one_smul]
    exact le_antisymm (by simpa [htrunc, hP] using hle) (le_inf hr0 (bandIndex_nonneg k))
  by_cases hmem : r ∈ maximalPositiveDisjointFamily
  · let k : BandIndex := ⟨r, hmem⟩
    have hfix : indexProjection hE k.mem_family r = r := by
      rw [indexProjection_apply_nonneg hE k hr0]
      exact posBandPart_of_le_smul hE (bandIndex_nonneg k) hr0
        (le_of_eq (one_smul ℝ r).symm)
    exact hne (hfix.symm.trans (hPr k))
  · let S := insert r maximalPositiveDisjointFamily
    have hS : IsPositiveDisjointFamily (E := E) S := by
      constructor
      · intro y hy
        rcases Set.mem_insert_iff.mp hy with rfl | hy
        · exact hlt
        · exact (maximalPositiveDisjointFamily_spec (E := E)).1.1 y hy
      · intro a ha b hb hab
        rcases Set.mem_insert_iff.mp ha with rfl | ha
        · rcases Set.mem_insert_iff.mp hb with rfl | hb
          · exact (hab rfl).elim
          · have hzero : r ⊓ b = 0 := hdisj b hb
            simpa [LatticeDisjoint, abs_of_nonneg hr0,
              abs_of_nonneg ((maximalPositiveDisjointFamily_spec (E := E)).1.1 b hb).le] using
              hzero
        · rcases Set.mem_insert_iff.mp hb with rfl | hb
          · have hzero : a ⊓ r = 0 := by simpa [inf_comm] using hdisj a ha
            simpa [LatticeDisjoint, abs_of_nonneg hr0,
              abs_of_nonneg ((maximalPositiveDisjointFamily_spec (E := E)).1.1 a ha).le] using
              hzero
          · exact (maximalPositiveDisjointFamily_spec (E := E)).1.2 ha hb hab
    have hsub : maximalPositiveDisjointFamily ⊆ S := subset_insert _ _
    have hneS : maximalPositiveDisjointFamily ≠ S := by
      intro hEq
      exact hmem (hEq ▸ mem_insert r _)
    exact hneS (Maximal.eq_of_subset (maximalPositiveDisjointFamily_spec (E := E)).2 hS hsub)

/-- Every vector is the sum of its band projections. -/
theorem indexProjection_tsum (x : E) :
    ∑' (i : BandIndex), indexProjection hE i.mem_family x = x := by
  have hlin : ∀ i : BandIndex, indexProjection hE i.mem_family x =
      indexProjection hE i.mem_family x⁺ - indexProjection hE i.mem_family x⁻ := by
    intro i
    have hsub := map_sub (indexProjection hE i.mem_family) x⁺ x⁻
    rwa [posPart_sub_negPart x] at hsub
  calc
    ∑' (i : BandIndex), indexProjection hE i.mem_family x
        = ∑' (i : BandIndex),
            (indexProjection hE i.mem_family x⁺ - indexProjection hE i.mem_family x⁻) :=
      tsum_congr hlin
    _ = (∑' (i : BandIndex), indexProjection hE i.mem_family x⁺) -
          ∑' (i : BandIndex), indexProjection hE i.mem_family x⁻ :=
      Summable.tsum_sub (summable_indexProjection hE x⁺) (summable_indexProjection hE x⁻)
    _ = x⁺ - x⁻ := by
      rw [indexProjection_tsum_nonneg hE (posPart_nonneg x),
        indexProjection_tsum_nonneg hE (negPart_nonneg x)]
    _ = x := (posPart_sub_negPart x)

/-- The series of projection norms recovers the norm. -/
private theorem tsum_norm_indexProjection {x : E} (hx : 0 ≤ x) :
    ∑' (i : BandIndex), ‖indexProjection hE i.mem_family x‖ = ‖x‖ := by
  have hv : Tendsto (fun t : Finset BandIndex => ∑ i ∈ t, indexProjection hE i.mem_family x) atTop
      (𝓝 x) := by
    have hsum := (summable_indexProjection hE x).hasSum
    rwa [indexProjection_tsum_nonneg hE hx] at hsum
  have hn : Tendsto (fun t : Finset BandIndex => ∑ i ∈ t, ‖indexProjection hE i.mem_family x‖)
      atTop (𝓝 ‖x‖) := by
    refine ((continuous_norm.tendsto x).comp hv).congr fun t => ?_
    rw [Function.comp_apply, norm_sum_indexProjection hE x t]
  exact tendsto_nhds_unique (summable_norm_indexProjection hE x).hasSum hn

/-- Projection norms add to the ambient norm for every vector. -/
theorem tsum_norm_indexProjection_eq (x : E) :
    ∑' (i : BandIndex), ‖indexProjection hE i.mem_family x‖ = ‖x‖ := by
  have hterm : ∀ i : BandIndex, ‖indexProjection hE i.mem_family x‖ =
      ‖indexProjection hE i.mem_family |x|‖ := by
    intro i
    rw [← norm_abs_eq_norm (indexProjection hE i.mem_family x), indexProjection_abs hE i x]
  rw [tsum_congr hterm, tsum_norm_indexProjection hE (abs_nonneg x), norm_abs_eq_norm]

end IndexProj

end CKMA
