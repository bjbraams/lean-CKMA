/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Order.Zorn
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Topology.Order.Basic
public import Mathlib.Topology.Order.Lattice

/-!
# Exact Lipschitz extension between Hilbert spaces

Kirszbraun extension preserves the Lipschitz bound of a map from an arbitrary subset
of a real inner-product space into a complete real Hilbert space. The subset may be
empty and the source need not be complete. Norms, distances and Lipschitz predicates
are Mathlib's. Source: GAPS 05.33.
-/

@[expose] public section

noncomputable section

namespace CKMA

open scoped BigOperators NNReal RealInnerProductSpace Topology

open Filter Finset Metric Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Weighted squared distances to a convex combination are the corresponding variance. -/
private lemma sum_w_norm_sub_sq_center {ι : Type*} [Fintype ι] (w : ι → ℝ) (a : ι → E)
    (hw : ∑ i, w i = 1) :
    ∑ i, w i * ‖(∑ j, w j • a j) - a i‖ ^ 2 =
      ∑ i, w i * ‖a i‖ ^ 2 - ‖∑ j, w j • a j‖ ^ 2 := by
  set q : E := ∑ j, w j • a j
  have hinner : ⟪q, q⟫ = ∑ i, w i * ⟪q, a i⟫ := by
    change ⟪q, ∑ i, w i • a i⟫ = _
    rw [inner_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [real_inner_smul_right]
  have hcoeff : ∑ i, w i * ‖q‖ ^ 2 = ‖q‖ ^ 2 := by
    rw [← sum_mul, hw, one_mul]
  have hcross : ∑ i, w i * (2 * ⟪q, a i⟫) = 2 * ⟪q, q⟫ := by
    have hmul : ∀ i, w i * (2 * ⟪q, a i⟫) = 2 * (w i * ⟪q, a i⟫) := fun _ => by ring
    simp_rw [hmul, ← mul_sum, hinner]
  calc
    ∑ i, w i * ‖q - a i‖ ^ 2
        = ∑ i, w i * (‖q‖ ^ 2 - 2 * ⟪q, a i⟫ + ‖a i‖ ^ 2) := by
          refine sum_congr rfl fun i _ => ?_
          rw [norm_sub_sq_real]
    _ = ∑ i, w i * ‖q‖ ^ 2 - ∑ i, w i * (2 * ⟪q, a i⟫) + ∑ i, w i * ‖a i‖ ^ 2 := by
          simp_rw [mul_add, mul_sub, sub_eq_add_neg, sum_add_distrib, sum_neg_distrib]
    _ = ‖q‖ ^ 2 - 2 * ⟪q, q⟫ + ∑ i, w i * ‖a i‖ ^ 2 := by rw [hcoeff, hcross]
    _ = ∑ i, w i * ‖a i‖ ^ 2 - ‖q‖ ^ 2 := by
          rw [real_inner_self_eq_norm_sq]
          ring

/-- The double count of squared distances through weights that sum to one. -/
private lemma sum_pairwise_sq_norm {ι : Type*} [Fintype ι] (w : ι → ℝ) (a : ι → E)
    (hw : ∑ i, w i = 1) :
    ∑ i, ∑ j, w i * w j * ‖a i - a j‖ ^ 2 =
      2 * (∑ i, w i * ‖a i‖ ^ 2 - ‖∑ i, w i • a i‖ ^ 2) := by
  have hsq : ∀ i j, ‖a i - a j‖ ^ 2 = ‖a i‖ ^ 2 + ‖a j‖ ^ 2 - 2 * ⟪a i, a j⟫ := by
    intro i j
    rw [norm_sub_sq_real]
    ring
  have hleft : ∑ i, ∑ j, w i * w j * ‖a i‖ ^ 2 = ∑ i, w i * ‖a i‖ ^ 2 := by
    refine sum_congr rfl fun i _ => ?_
    calc
      ∑ j, w i * w j * ‖a i‖ ^ 2 = ∑ j, w j * (w i * ‖a i‖ ^ 2) := by
        refine sum_congr rfl fun j _ => ?_
        ring
      _ = (∑ j, w j) * (w i * ‖a i‖ ^ 2) := by rw [← sum_mul]
      _ = w i * ‖a i‖ ^ 2 := by rw [hw, one_mul]
  have hright : ∑ i, ∑ j, w i * w j * ‖a j‖ ^ 2 = ∑ j, w j * ‖a j‖ ^ 2 := by
    rw [sum_comm]
    refine sum_congr rfl fun j _ => ?_
    calc
      ∑ i, w i * w j * ‖a j‖ ^ 2 = ∑ i, w i * (w j * ‖a j‖ ^ 2) := by
        refine sum_congr rfl fun i _ => ?_
        ring
      _ = (∑ i, w i) * (w j * ‖a j‖ ^ 2) := by rw [← sum_mul]
      _ = w j * ‖a j‖ ^ 2 := by rw [hw, one_mul]
  have hinner : ∑ i, ∑ j, w i * w j * ⟪a i, a j⟫ = ‖∑ i, w i • a i‖ ^ 2 := by
    have hsum : ⟪∑ i, w i • a i, ∑ j, w j • a j⟫ =
        ∑ i, ∑ j, w i * w j * ⟪a i, a j⟫ := by
      simp_rw [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right, mul_assoc]
    rw [← hsum, real_inner_self_eq_norm_sq]
  calc
    ∑ i, ∑ j, w i * w j * ‖a i - a j‖ ^ 2
        = ∑ i, ∑ j, (w i * w j * ‖a i‖ ^ 2 + w i * w j * ‖a j‖ ^ 2 -
            2 * w i * w j * ⟪a i, a j⟫) := by
          refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
          rw [hsq]
          ring
    _ = ∑ i, ∑ j, w i * w j * ‖a i‖ ^ 2 + ∑ i, ∑ j, w i * w j * ‖a j‖ ^ 2 -
          ∑ i, ∑ j, 2 * w i * w j * ⟪a i, a j⟫ := by
          simp_rw [sum_sub_distrib, sum_add_distrib]
    _ = ∑ i, ∑ j, w i * w j * ‖a i‖ ^ 2 + ∑ i, ∑ j, w i * w j * ‖a j‖ ^ 2 -
          2 * ∑ i, ∑ j, w i * w j * ⟪a i, a j⟫ := by
          have hfac : ∑ i, ∑ j, 2 * w i * w j * ⟪a i, a j⟫ =
              2 * ∑ i, ∑ j, w i * w j * ⟪a i, a j⟫ := by
            simp_rw [show ∀ i j, (2 : ℝ) * w i * w j * ⟪a i, a j⟫ =
              2 * (w i * w j * ⟪a i, a j⟫) from fun _ _ => by ring]
            simp_rw [← Finset.mul_sum]
          rw [hfac]
    _ = 2 * (∑ i, w i * ‖a i‖ ^ 2 - ‖∑ i, w i • a i‖ ^ 2) := by
          rw [hleft, hright, hinner]
          ring

/-- Pairwise squared distances dominate the distance to any external point. -/
private lemma sum_pairwise_sq_le_point {ι : Type*} [Fintype ι] (w : ι → ℝ) (b : ι → E) (p : E)
    (hw : ∑ i, w i = 1) :
    ∑ i, ∑ j, w i * w j * ‖b i - b j‖ ^ 2 ≤ 2 * ∑ i, w i * ‖b i - p‖ ^ 2 := by
  set u : E := ∑ i, w i • b i
  have hpair := sum_pairwise_sq_norm w b hw
  have hvar : ∑ i, w i * ‖b i‖ ^ 2 - ‖u‖ ^ 2 ≤ ∑ i, w i * ‖b i - p‖ ^ 2 := by
    have hexpand : ∑ i, w i * ‖b i - p‖ ^ 2 =
        ∑ i, w i * ‖b i‖ ^ 2 - 2 * ⟪u, p⟫ + ‖p‖ ^ 2 := by
      have hsum : ∑ i, w i * ⟪b i, p⟫ = ⟪u, p⟫ := by
        change ∑ i, w i * ⟪b i, p⟫ = ⟪∑ i, w i • b i, p⟫
        rw [sum_inner]
        refine sum_congr rfl fun i _ => ?_
        rw [real_inner_smul_left, mul_comm]
      calc
        ∑ i, w i * ‖b i - p‖ ^ 2
            = ∑ i, w i * (‖b i‖ ^ 2 - 2 * ⟪b i, p⟫ + ‖p‖ ^ 2) := by
              refine sum_congr rfl fun i _ => ?_
              rw [norm_sub_sq_real]
        _ = ∑ i, w i * ‖b i‖ ^ 2 - 2 * ∑ i, w i * ⟪b i, p⟫ + ∑ i, w i * ‖p‖ ^ 2 := by
              have hterm : ∀ i, w i * (‖b i‖ ^ 2 - 2 * ⟪b i, p⟫ + ‖p‖ ^ 2) =
                  w i * ‖b i‖ ^ 2 - w i * (2 * ⟪b i, p⟫) + w i * ‖p‖ ^ 2 :=
                fun _ => by ring
              simp_rw [hterm, sum_add_distrib, sum_sub_distrib]
              simp_rw [show ∀ i, w i * (2 * ⟪b i, p⟫) = 2 * (w i * ⟪b i, p⟫) from
                fun _ => by ring]
              simp_rw [← Finset.mul_sum]
        _ = ∑ i, w i * ‖b i‖ ^ 2 - 2 * ⟪u, p⟫ + ‖p‖ ^ 2 := by
              rw [hsum, ← sum_mul, hw, one_mul]
    have hnorm : ‖u - p‖ ^ 2 = ‖u‖ ^ 2 - 2 * ⟪u, p⟫ + ‖p‖ ^ 2 := by
      rw [norm_sub_sq_real]
    rw [hexpand]
    linarith [sq_nonneg ‖u - p‖, hnorm]
  calc
    ∑ i, ∑ j, w i * w j * ‖b i - b j‖ ^ 2
        = 2 * (∑ i, w i * ‖b i‖ ^ 2 - ‖u‖ ^ 2) := hpair
    _ ≤ 2 * ∑ i, w i * ‖b i - p‖ ^ 2 := by gcongr

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
/-- Nonnegative weights preserve the comparison of pairwise squared distances. -/
private lemma sum_pairwise_sq_mono {ι : Type*} [Fintype ι]
    {E' F : Type*} [NormedAddCommGroup E'] [NormedAddCommGroup F]
    (w : ι → ℝ) (a : ι → E') (b : ι → F)
    (hw : ∀ i, 0 ≤ w i) (h : ∀ i j, ‖a i - a j‖ ≤ ‖b i - b j‖) :
    ∑ i, ∑ j, w i * w j * ‖a i - a j‖ ^ 2 ≤
      ∑ i, ∑ j, w i * w j * ‖b i - b j‖ ^ 2 := by
  refine sum_le_sum fun i _ => sum_le_sum fun j _ => ?_
  have hcoef : 0 ≤ w i * w j := mul_nonneg (hw i) (hw j)
  have hsq : ‖a i - a j‖ ^ 2 ≤ ‖b i - b j‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (h i j) 2
  exact mul_le_mul_of_nonneg_left hsq hcoef

/-- In a complete real inner-product space, closed balls with the finite-intersection property
have nonempty total intersection. -/
private lemma exists_iInter_closedBall_of_forall_finset
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
    {ι : Type*} (c : ι → K) (r : ι → ℝ)
    (hfin : ∀ s : Finset ι, ∃ z : K, ∀ i ∈ s, dist z (c i) ≤ r i) :
    ∃ z : K, ∀ i, dist z (c i) ≤ r i := by
  classical
  by_cases hι : Nonempty ι
  · let feasible (s : Finset ι) : Set K := {z | ∀ i ∈ s, dist z (c i) ≤ r i}
    let normImg (s : Finset ι) : Set ℝ := norm '' feasible s
    let α (s : Finset ι) : ℝ := sInf (normImg s)
    have hfeas : ∀ s : Finset ι, (feasible s).Nonempty := by
      intro s
      obtain ⟨z, hz⟩ := hfin s
      exact ⟨z, hz⟩
    have hnorm_ne : ∀ s, (normImg s).Nonempty := fun s => (hfeas s).image _
    have hbb : ∀ s, BddBelow (normImg s) := fun s =>
      ⟨0, fun ρ hρ => by
        obtain ⟨_, _, rfl⟩ := hρ
        exact norm_nonneg _⟩
    have hα_nonneg : ∀ s, 0 ≤ α s := fun s =>
      le_csInf (hnorm_ne s) fun ρ hρ => by
        obtain ⟨_, _, rfl⟩ := hρ
        exact norm_nonneg _
    have hα_mono : ∀ {s t : Finset ι}, s ⊆ t → α s ≤ α t := by
      intro s t hst
      have hsub : normImg t ⊆ normImg s := by
        rintro ρ ⟨z, hz, rfl⟩
        exact ⟨z, fun i hi => hz i (hst hi), rfl⟩
      apply le_csInf (hnorm_ne t)
      intro ρ hρ
      exact csInf_le (hbb s) (hsub hρ)
    let i0 : ι := hι.some
    have hα_bdd : ∀ s, α s ≤ ‖c i0‖ + r i0 := by
      intro s
      let s' := insert i0 s
      obtain ⟨z, hz⟩ := hfeas s'
      have hz0 : dist z (c i0) ≤ r i0 := hz i0 (mem_insert_self _ _)
      have hnorm : ‖z‖ ≤ ‖c i0‖ + r i0 := by
        calc
          ‖z‖ ≤ ‖c i0‖ + ‖z - c i0‖ := by
            simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
              norm_add_le (c i0) (z - c i0)
          _ = ‖c i0‖ + dist z (c i0) := by rw [dist_eq_norm, norm_sub_rev]
          _ ≤ ‖c i0‖ + r i0 := by gcongr
      have hmem : ‖z‖ ∈ normImg s' := ⟨z, hz, rfl⟩
      calc
        α s ≤ α s' := hα_mono (subset_insert i0 s)
        _ ≤ ‖z‖ := csInf_le (hbb s') hmem
        _ ≤ ‖c i0‖ + r i0 := hnorm
    let A : ℝ := sSup (range α)
    have hA_bdd : BddAbove (range α) := ⟨‖c i0‖ + r i0, by
      rintro _ ⟨s, rfl⟩
      exact hα_bdd s⟩
    have hA_ne : (range α).Nonempty := ⟨α ∅, mem_range_self _⟩
    have hα_le_A : ∀ s, α s ≤ A := fun s => le_csSup hA_bdd (mem_range_self s)
    have hclose : ∀ n : ℕ, ∃ t : Finset ι, A - 1 / (n + 1 : ℝ) < α t := by
      intro n
      have hlt : A - 1 / (n + 1 : ℝ) < A := by
        have : 0 < 1 / (n + 1 : ℝ) := by positivity
        linarith
      obtain ⟨ρ, ⟨t, rfl⟩, hρ⟩ := exists_lt_of_lt_csSup hA_ne hlt
      exact ⟨t, hρ⟩
    let u : ℕ → Finset ι := fun n => Classical.choose (hclose n)
    have hu : ∀ n : ℕ, A - 1 / (n + 1 : ℝ) < α (u n) :=
      fun n => Classical.choose_spec (hclose n)
    let sSeq : ℕ → Finset ι := fun n => (range (n + 1)).biUnion u ∪ {i0}
    have hs_mono : ∀ {n m}, n ≤ m → sSeq n ⊆ sSeq m := by
      intro n m hnm i hi
      rcases mem_union.mp hi with hi | hi
      · refine mem_union_left _ ?_
        rw [Finset.mem_biUnion] at hi
        obtain ⟨k, hk, hik⟩ := hi
        rw [Finset.mem_range] at hk
        exact Finset.mem_biUnion.mpr
          ⟨k, Finset.mem_range.mpr (hk.trans_le (Nat.succ_le_succ hnm)), hik⟩
      · exact mem_union_right _ hi
    have hu_sub : ∀ n, u n ⊆ sSeq n := by
      intro n i hi
      refine mem_union_left _ ?_
      exact Finset.mem_biUnion.mpr ⟨n, Finset.mem_range.mpr (Nat.lt_succ_self n), hi⟩
    have hα_gt : ∀ n : ℕ, A - 1 / (n + 1 : ℝ) < α (sSeq n) := fun n =>
      lt_of_lt_of_le (hu n) (hα_mono (hu_sub n))
    have hα_lim : Tendsto (fun n => α (sSeq n)) atTop (𝓝 A) := by
      have hdiv : Tendsto (fun n : ℕ => 1 / (n + 1 : ℝ)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have hconst : Tendsto (fun _ : ℕ => A) atTop (𝓝 A) := tendsto_const_nhds
      have hlower : Tendsto (fun n : ℕ => A - 1 / (n + 1 : ℝ)) atTop (𝓝 A) := by
        have hsub := hconst.sub hdiv
        simpa using hsub
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlower tendsto_const_nhds
        (fun n => (hα_gt n).le) (fun n => hα_le_A (sSeq n))
    have hz_ex : ∀ n, ∃ z, z ∈ feasible (sSeq n) ∧ ‖z‖ < α (sSeq n) + 1 / (n + 1 : ℝ) := by
      intro n
      have hlt : α (sSeq n) < α (sSeq n) + 1 / (n + 1 : ℝ) := by
        have : 0 < 1 / (n + 1 : ℝ) := by positivity
        linarith
      obtain ⟨ρ, hρ, hlt'⟩ := exists_lt_of_csInf_lt (hnorm_ne (sSeq n)) hlt
      obtain ⟨z, hz, rfl⟩ := hρ
      exact ⟨z, hz, hlt'⟩
    let zSeq : ℕ → K := fun n => Classical.choose (hz_ex n)
    have hzSeq : ∀ n, zSeq n ∈ feasible (sSeq n) ∧
        ‖zSeq n‖ < α (sSeq n) + 1 / (n + 1 : ℝ) := fun n => Classical.choose_spec (hz_ex n)
    have hnorm_lim : Tendsto (fun n => ‖zSeq n‖) atTop (𝓝 A) := by
      have hdiv : Tendsto (fun n : ℕ => 1 / (n + 1 : ℝ)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have hupper : Tendsto (fun n => α (sSeq n) + 1 / (n + 1 : ℝ)) atTop (𝓝 A) := by
        simpa using hα_lim.add hdiv
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le hα_lim hupper
        (fun n => csInf_le (hbb (sSeq n)) ⟨zSeq n, (hzSeq n).1, rfl⟩)
        (fun n => (hzSeq n).2.le)
    have hnorm_sq_lim : Tendsto (fun n => ‖zSeq n‖ ^ 2) atTop (𝓝 (A ^ 2)) := by
      simpa using hnorm_lim.pow 2
    have hα_sq_lim : Tendsto (fun n => α (sSeq n) ^ 2) atTop (𝓝 (A ^ 2)) := by
      simpa using hα_lim.pow 2
    have hmid_le : ∀ {n m}, n ≤ m →
        dist (zSeq n) (zSeq m) ^ 2 ≤
          2 * ‖zSeq n‖ ^ 2 + 2 * ‖zSeq m‖ ^ 2 - 4 * α (sSeq n) ^ 2 := by
      intro n m hnm
      have hzn : zSeq n ∈ feasible (sSeq n) := (hzSeq n).1
      have hzm : zSeq m ∈ feasible (sSeq n) := fun i hi =>
        (hzSeq m).1 i (hs_mono hnm hi)
      let mid : K := (1 / 2 : ℝ) • zSeq n + (1 / 2 : ℝ) • zSeq m
      have hmid : mid ∈ feasible (sSeq n) := by
        intro i hi
        have hnball := hzn i hi
        have hmball := hzm i hi
        have : mid ∈ closedBall (c i) (r i) :=
          (convex_closedBall (c i) (r i)) hnball hmball (by positivity) (by positivity)
            (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
        simpa [mem_closedBall] using this
      have hnorm_mid : α (sSeq n) ≤ ‖mid‖ :=
        csInf_le (hbb (sSeq n)) ⟨mid, hmid, rfl⟩
      have hpara := parallelogram_law_with_norm ℝ (zSeq n) (zSeq m)
      have hsum : ‖zSeq n + zSeq m‖ = 2 * ‖mid‖ := by
        have : zSeq n + zSeq m = (2 : ℝ) • mid := by
          simp only [mid, smul_add, smul_smul]
          have hcoef : (2 : ℝ) * (1 / 2) = 1 := by norm_num
          rw [hcoef, one_smul, one_smul]
        rw [this, norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      calc
        dist (zSeq n) (zSeq m) ^ 2 = ‖zSeq n - zSeq m‖ ^ 2 := by rw [dist_eq_norm]
        _ = 2 * ‖zSeq n‖ ^ 2 + 2 * ‖zSeq m‖ ^ 2 - ‖zSeq n + zSeq m‖ ^ 2 := by
              linarith [hpara]
        _ = 2 * ‖zSeq n‖ ^ 2 + 2 * ‖zSeq m‖ ^ 2 - 4 * ‖mid‖ ^ 2 := by
              rw [hsum]
              ring
        _ ≤ 2 * ‖zSeq n‖ ^ 2 + 2 * ‖zSeq m‖ ^ 2 - 4 * α (sSeq n) ^ 2 := by
              have hsq : α (sSeq n) ^ 2 ≤ ‖mid‖ ^ 2 :=
                pow_le_pow_left₀ (hα_nonneg _) hnorm_mid 2
              linarith
    have hCauchy : CauchySeq zSeq := by
      rw [Metric.cauchySeq_iff]
      intro ε hε
      have hη : 0 < ε ^ 2 / 8 := by positivity
      obtain ⟨N1, hN1⟩ := (Metric.tendsto_atTop.mp hnorm_sq_lim) (ε ^ 2 / 8) hη
      obtain ⟨N2, hN2⟩ := (Metric.tendsto_atTop.mp hα_sq_lim) (ε ^ 2 / 8) hη
      refine ⟨max N1 N2, ?_⟩
      intro m hm n hn
      have hdist_sq : dist (zSeq m) (zSeq n) ^ 2 < ε ^ 2 := by
        rcases le_total m n with hmn | hnm
        · have hbound := hmid_le hmn
          have hmA : |‖zSeq m‖ ^ 2 - A ^ 2| < ε ^ 2 / 8 :=
            hN1 m (le_trans (le_max_left _ _) hm)
          have hnA : |‖zSeq n‖ ^ 2 - A ^ 2| < ε ^ 2 / 8 := hN1 n (le_trans (le_max_left _ _) hn)
          have hαA : |α (sSeq m) ^ 2 - A ^ 2| < ε ^ 2 / 8 :=
            hN2 m (le_trans (le_max_right _ _) hm)
          have hαle : α (sSeq m) ^ 2 ≤ A ^ 2 := by
            have hαnn : 0 ≤ α (sSeq m) :=
              le_csInf (hnorm_ne _) fun ρ hρ => by
                obtain ⟨_, _, rfl⟩ := hρ
                exact norm_nonneg _
            have hAnn : 0 ≤ A := le_trans hαnn (hα_le_A _)
            exact pow_le_pow_left₀ hαnn (hα_le_A _) 2
          have hupper :
              2 * ‖zSeq m‖ ^ 2 + 2 * ‖zSeq n‖ ^ 2 - 4 * α (sSeq m) ^ 2 < ε ^ 2 := by
            have hm' : ‖zSeq m‖ ^ 2 < A ^ 2 + ε ^ 2 / 8 := by
              rw [abs_lt] at hmA
              linarith
            have hn' : ‖zSeq n‖ ^ 2 < A ^ 2 + ε ^ 2 / 8 := by
              rw [abs_lt] at hnA
              linarith
            have hα' : A ^ 2 - ε ^ 2 / 8 < α (sSeq m) ^ 2 := by
              rw [abs_lt] at hαA
              linarith
            nlinarith [hαle]
          have : dist (zSeq m) (zSeq n) ^ 2 < ε ^ 2 := lt_of_le_of_lt hbound hupper
          exact this
        · rw [dist_comm]
          have hbound := hmid_le hnm
          have hnA : |‖zSeq n‖ ^ 2 - A ^ 2| < ε ^ 2 / 8 :=
            hN1 n (le_trans (le_max_left _ _) hn)
          have hmA : |‖zSeq m‖ ^ 2 - A ^ 2| < ε ^ 2 / 8 := hN1 m (le_trans (le_max_left _ _) hm)
          have hαA : |α (sSeq n) ^ 2 - A ^ 2| < ε ^ 2 / 8 :=
            hN2 n (le_trans (le_max_right _ _) hn)
          have hαnn : 0 ≤ α (sSeq n) :=
            le_csInf (hnorm_ne _) fun ρ hρ => by
              obtain ⟨_, _, rfl⟩ := hρ
              exact norm_nonneg _
          have hAnn : 0 ≤ A := le_trans hαnn (hα_le_A _)
          have hαle : α (sSeq n) ^ 2 ≤ A ^ 2 := pow_le_pow_left₀ hαnn (hα_le_A _) 2
          have hupper :
              2 * ‖zSeq n‖ ^ 2 + 2 * ‖zSeq m‖ ^ 2 - 4 * α (sSeq n) ^ 2 < ε ^ 2 := by
            have hn' : ‖zSeq n‖ ^ 2 < A ^ 2 + ε ^ 2 / 8 := by
              rw [abs_lt] at hnA
              linarith
            have hm' : ‖zSeq m‖ ^ 2 < A ^ 2 + ε ^ 2 / 8 := by
              rw [abs_lt] at hmA
              linarith
            have hα' : A ^ 2 - ε ^ 2 / 8 < α (sSeq n) ^ 2 := by
              rw [abs_lt] at hαA
              linarith
            nlinarith [hαle]
          exact lt_of_le_of_lt hbound hupper
      have hsq : dist (zSeq m) (zSeq n) ^ 2 < ε ^ 2 := hdist_sq
      have := (sq_lt_sq).1 hsq
      rwa [abs_of_nonneg dist_nonneg, abs_of_pos hε] at this
    obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete hCauchy
    refine ⟨z, ?_⟩
    intro j
    let s' : ℕ → Finset ι := fun n => insert j (sSeq n)
    have hα'_gt : ∀ n : ℕ, A - 1 / (n + 1 : ℝ) < α (s' n) := fun n =>
      lt_of_lt_of_le (hα_gt n) (hα_mono (subset_insert _ _))
    have hα'_lim : Tendsto (fun n => α (s' n)) atTop (𝓝 A) := by
      have hdiv : Tendsto (fun n : ℕ => 1 / (n + 1 : ℝ)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have hconst : Tendsto (fun _ : ℕ => A) atTop (𝓝 A) := tendsto_const_nhds
      have hlower : Tendsto (fun n : ℕ => A - 1 / (n + 1 : ℝ)) atTop (𝓝 A) := by
        have hsub := hconst.sub hdiv
        simpa using hsub
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlower tendsto_const_nhds
        (fun n => (hα'_gt n).le) (fun n => hα_le_A (s' n))
    have hw_ex : ∀ n, ∃ w, w ∈ feasible (s' n) ∧ ‖w‖ < α (s' n) + 1 / (n + 1 : ℝ) := by
      intro n
      have hlt : α (s' n) < α (s' n) + 1 / (n + 1 : ℝ) := by
        have : 0 < 1 / (n + 1 : ℝ) := by positivity
        linarith
      obtain ⟨ρ, hρ, hlt'⟩ := exists_lt_of_csInf_lt (hnorm_ne (s' n)) hlt
      obtain ⟨w, hw, rfl⟩ := hρ
      exact ⟨w, hw, hlt'⟩
    let wSeq : ℕ → K := fun n => Classical.choose (hw_ex n)
    have hwSeq : ∀ n, wSeq n ∈ feasible (s' n) ∧
        ‖wSeq n‖ < α (s' n) + 1 / (n + 1 : ℝ) := fun n => Classical.choose_spec (hw_ex n)
    have hwnorm_lim : Tendsto (fun n => ‖wSeq n‖) atTop (𝓝 A) := by
      have hdiv : Tendsto (fun n : ℕ => 1 / (n + 1 : ℝ)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have hupper : Tendsto (fun n => α (s' n) + 1 / (n + 1 : ℝ)) atTop (𝓝 A) := by
        simpa using hα'_lim.add hdiv
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le hα'_lim hupper
        (fun n => csInf_le (hbb (s' n)) ⟨wSeq n, (hwSeq n).1, rfl⟩)
        (fun n => (hwSeq n).2.le)
    have hdist_lim : Tendsto (fun n => dist (wSeq n) (zSeq n)) atTop (𝓝 0) := by
      have hsq_le : ∀ n, dist (wSeq n) (zSeq n) ^ 2 ≤
          2 * ‖wSeq n‖ ^ 2 + 2 * ‖zSeq n‖ ^ 2 - 4 * α (sSeq n) ^ 2 := by
        intro n
        have hw_feas : wSeq n ∈ feasible (sSeq n) := fun i hi =>
          (hwSeq n).1 i (Finset.mem_insert_of_mem hi)
        have hz_feas : zSeq n ∈ feasible (sSeq n) := (hzSeq n).1
        let mid : K := (1 / 2 : ℝ) • wSeq n + (1 / 2 : ℝ) • zSeq n
        have hmid : mid ∈ feasible (sSeq n) := by
          intro i hi
          have : mid ∈ closedBall (c i) (r i) :=
            (convex_closedBall (c i) (r i)) (hw_feas i hi) (hz_feas i hi)
              (by positivity) (by positivity) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
          simpa [mem_closedBall] using this
        have hnorm_mid : α (sSeq n) ≤ ‖mid‖ :=
          csInf_le (hbb (sSeq n)) ⟨mid, hmid, rfl⟩
        have hpara := parallelogram_law_with_norm ℝ (wSeq n) (zSeq n)
        have hsum : ‖wSeq n + zSeq n‖ = 2 * ‖mid‖ := by
          have : wSeq n + zSeq n = (2 : ℝ) • mid := by
            simp only [mid, smul_add, smul_smul]
            have hcoef : (2 : ℝ) * (1 / 2) = 1 := by norm_num
            rw [hcoef, one_smul, one_smul]
          rw [this, norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        calc
          dist (wSeq n) (zSeq n) ^ 2 = ‖wSeq n - zSeq n‖ ^ 2 := by rw [dist_eq_norm]
          _ = 2 * ‖wSeq n‖ ^ 2 + 2 * ‖zSeq n‖ ^ 2 - ‖wSeq n + zSeq n‖ ^ 2 := by
                linarith [hpara]
          _ = 2 * ‖wSeq n‖ ^ 2 + 2 * ‖zSeq n‖ ^ 2 - 4 * ‖mid‖ ^ 2 := by
                rw [hsum]; ring
          _ ≤ 2 * ‖wSeq n‖ ^ 2 + 2 * ‖zSeq n‖ ^ 2 - 4 * α (sSeq n) ^ 2 := by
                have hsq : α (sSeq n) ^ 2 ≤ ‖mid‖ ^ 2 :=
                  pow_le_pow_left₀ (hα_nonneg _) hnorm_mid 2
                linarith
      have hupper_lim : Tendsto (fun n =>
          2 * ‖wSeq n‖ ^ 2 + 2 * ‖zSeq n‖ ^ 2 - 4 * α (sSeq n) ^ 2) atTop (𝓝 0) := by
        have hwsq := hwnorm_lim.pow 2
        have hzsq := hnorm_lim.pow 2
        have hαsq := hα_lim.pow 2
        have htend :=
          ((hwsq.const_mul 2).add (hzsq.const_mul 2)).sub (hαsq.const_mul 4)
        have hzero : (2 : ℝ) * A ^ 2 + 2 * A ^ 2 - 4 * A ^ 2 = 0 := by ring
        rwa [hzero] at htend
      have hsq_lim : Tendsto (fun n => dist (wSeq n) (zSeq n) ^ 2) atTop (𝓝 0) :=
        tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper_lim
          (fun _ => sq_nonneg _) hsq_le
      rw [Metric.tendsto_atTop] at hsq_lim ⊢
      intro ε hε
      obtain ⟨N, hN⟩ := hsq_lim (ε ^ 2) (by positivity)
      refine ⟨N, fun n hn => ?_⟩
      have hlt : dist (wSeq n) (zSeq n) ^ 2 < ε ^ 2 := by
        have := hN n hn
        rw [Real.dist_eq, sub_zero, abs_of_nonneg (sq_nonneg _)] at this
        exact this
      have habs : |dist (wSeq n) (zSeq n)| < ε := by
        have := (sq_lt_sq).mp hlt
        rwa [abs_of_pos hε] at this
      rw [Real.dist_eq, sub_zero]
      exact habs
    have hw_tendsto : Tendsto wSeq atTop (𝓝 z) :=
      tendsto_of_tendsto_of_dist hz <| by
        convert hdist_lim using 2
        rw [dist_comm]
    have hw_ball : ∀ n, dist (wSeq n) (c j) ≤ r j := fun n =>
      (hwSeq n).1 j (mem_insert_self _ _)
    have hdist_tendsto : Tendsto (fun n => dist (wSeq n) (c j)) atTop (𝓝 (dist z (c j))) :=
      hw_tendsto.dist tendsto_const_nhds
    exact le_of_tendsto hdist_tendsto (Eventually.of_forall hw_ball)
  · exact ⟨0, fun i => (hι ⟨i⟩).elim⟩

set_option linter.style.haveILetI false in
/-- Finite Kirszbraun lemma: a distance-nonincreasing cloud of balls that meets in the source
meets in the target. -/
private lemma exists_common_point_closedBall_of_dist_le
    {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    {ι : Type*} [Fintype ι] (x : ι → H) (y : ι → K) (r : ι → ℝ)
    (hdist : ∀ i j, dist (y i) (y j) ≤ dist (x i) (x j))
    (hp : ∃ p : H, ∀ i, dist (x i) p ≤ r i) :
    ∃ q : K, ∀ i, dist (y i) q ≤ r i := by
  classical
  by_cases hι : Nonempty ι
  · haveI : Nonempty ι := hι
    obtain ⟨p, hp⟩ := hp
    have hr0 : ∀ i, 0 ≤ r i := fun i => dist_nonneg.trans (hp i)
    let φ : K → ℝ := fun z =>
      univ.sup' univ_nonempty fun i => dist z (y i) ^ 2 - r i ^ 2
    have le_φ (z : K) (i : ι) : dist z (y i) ^ 2 - r i ^ 2 ≤ φ z :=
      (sup'_le_iff univ_nonempty (fun j => dist z (y j) ^ 2 - r j ^ 2)).mp
        le_rfl i (mem_univ i)
    have hφ_cont : Continuous φ := by
      refine Continuous.finset_sup'_apply univ_nonempty fun i _ => ?_
      exact ((continuous_id.dist continuous_const).pow 2).sub continuous_const
    let V : Submodule ℝ K := Submodule.span ℝ (range y)
    haveI : FiniteDimensional ℝ V := FiniteDimensional.span_of_finite ℝ (finite_range y)
    haveI : CompleteSpace V := FiniteDimensional.complete ℝ V
    have hyV : ∀ i, y i ∈ V := fun i => Submodule.subset_span (mem_range_self i)
    have hproj : ∀ z : K, φ (V.starProjection z) ≤ φ z := by
      intro z
      refine sup'_le _ _ fun i _ => ?_
      have hpyth :=
        Submodule.norm_sq_eq_add_norm_sq_starProjection (z - y i) V
      have horth : 0 ≤ ‖Vᗮ.starProjection (z - y i)‖ ^ 2 := sq_nonneg _
      have hle : ‖V.starProjection (z - y i)‖ ^ 2 ≤ ‖z - y i‖ ^ 2 := by linarith
      have hlin : V.starProjection (z - y i) = V.starProjection z - y i := by
        rw [map_sub, Submodule.starProjection_eq_self_iff.mpr (hyV i)]
      have hterm : dist (V.starProjection z) (y i) ^ 2 ≤ dist z (y i) ^ 2 := by
        rw [dist_eq_norm, dist_eq_norm, ← hlin]
        exact hle
      have : dist (V.starProjection z) (y i) ^ 2 - r i ^ 2 ≤
          dist z (y i) ^ 2 - r i ^ 2 := by linarith
      exact this.trans (le_φ z i)
    let i0 : ι := hι.some
    let base : ℝ := φ 0
    let bound : ℝ := max (base + r i0 ^ 2 + 1) 1
    let R : ℝ := ‖y i0‖ + Real.sqrt bound + 1
    have hR0 : 0 ≤ R := by positivity
    have hcoe : ∀ v : V, R < ‖v‖ → base < φ (v : K) := by
      intro v hv
      have hsqrt_nonneg : 0 ≤ Real.sqrt bound := Real.sqrt_nonneg _
      have hbound_pos : 0 ≤ bound := le_trans zero_le_one (le_max_right _ _)
      have hgap : Real.sqrt bound < ‖(v : K) - y i0‖ := by
        have hlower : ‖(v : K)‖ - ‖y i0‖ ≤ ‖(v : K) - y i0‖ :=
          (le_abs_self _).trans (abs_norm_sub_norm_le _ _)
        have : Real.sqrt bound + 1 < ‖(v : K)‖ - ‖y i0‖ := by
          have : R < ‖v‖ := hv
          dsimp [R] at this
          linarith
        linarith
      have hsq : bound < ‖(v : K) - y i0‖ ^ 2 := by
        have hlt : (Real.sqrt bound) ^ 2 < ‖(v : K) - y i0‖ ^ 2 := by
          exact (sq_lt_sq).2 (by
            rwa [abs_of_nonneg hsqrt_nonneg, abs_of_nonneg (norm_nonneg _)])
        rwa [Real.sq_sqrt hbound_pos] at hlt
      have hterm : base + 1 < ‖(v : K) - y i0‖ ^ 2 - r i0 ^ 2 := by
        have hmax : base + r i0 ^ 2 + 1 ≤ bound := le_max_left _ _
        linarith
      have hle : ‖(v : K) - y i0‖ ^ 2 - r i0 ^ 2 ≤ φ (v : K) := by
        simpa [dist_eq_norm] using le_φ (v : K) i0
      linarith
    have hφV : Continuous fun v : V => φ (v : K) := hφ_cont.comp continuous_subtype_val
    obtain ⟨vMin, hvMin, hminOn⟩ :=
      (isCompact_closedBall (0 : V) R).exists_isMinOn ⟨0, mem_closedBall_self hR0⟩ hφV.continuousOn
    have hball : ∀ v : V, ‖v‖ ≤ R → φ (vMin : K) ≤ φ (v : K) := by
      intro v hv
      exact hminOn (by simpa [mem_closedBall, dist_eq_norm] using hv)
    have hV : ∀ v : V, φ (vMin : K) ≤ φ (v : K) := by
      intro v
      by_cases hv : ‖v‖ ≤ R
      · exact hball v hv
      · have hlt : base < φ (v : K) := hcoe v (lt_of_not_ge hv)
        have h0 : φ (vMin : K) ≤ base := by
          simpa using hball 0 (by simpa using hR0)
        linarith
    let z₀ : K := vMin
    have hglob : ∀ z : K, φ z₀ ≤ φ z := by
      intro z
      have hπ : φ (V.orthogonalProjectionOnto z : K) ≤ φ z := by
        simpa only [Submodule.coe_orthogonalProjectionOnto_apply] using hproj z
      exact (hV (V.orthogonalProjectionOnto z)).trans hπ
    let α : ℝ := φ z₀
    let S : Set K := {q | ∃ i, dist z₀ (y i) ^ 2 - r i ^ 2 = α ∧ q = y i}
    have hS_ne : S.Nonempty := by
      obtain ⟨i, -, hi⟩ := exists_mem_eq_sup' univ_nonempty
        (fun i => dist z₀ (y i) ^ 2 - r i ^ 2)
      exact ⟨y i, i, by simpa [α, φ] using hi.symm, rfl⟩
    have hS_fin : S.Finite := (finite_range y).subset fun q hq => by
      obtain ⟨i, _, rfl⟩ := hq
      exact mem_range_self i
    have hC_ne : (convexHull ℝ S).Nonempty := hS_ne.mono (subset_convexHull _ _)
    have hC_comp : IsCompact (convexHull ℝ S) := hS_fin.isCompact_convexHull ℝ
    obtain ⟨q, hq, hqmin⟩ :=
      exists_norm_eq_iInf_of_complete_convex hC_ne hC_comp.isComplete (convex_convexHull ℝ S) z₀
    have hα_le : α ≤ 0 := by
      by_cases hzero : ‖z₀ - q‖ = 0
      · have hzq : z₀ = q := by
          apply dist_eq_zero.mp
          rw [dist_eq_norm]
          exact hzero
        have hz₀S : z₀ ∈ convexHull ℝ S := by simpa [hzq] using hq
        obtain ⟨κ, hκ, w, z, hw0, hw1, hz, hsum⟩ :=
          (mem_convexHull_iff_exists_fintype).1 hz₀S
        letI : Fintype κ := hκ
        have hjex : ∀ i : κ, ∃ j : ι, dist z₀ (y j) ^ 2 - r j ^ 2 = α ∧ z i = y j := by
          intro i
          obtain ⟨j, hjα, hjz⟩ := hz i
          exact ⟨j, hjα, hjz⟩
        let j : κ → ι := fun i => Classical.choose (hjex i)
        have hj : ∀ i, dist z₀ (y (j i)) ^ 2 - r (j i) ^ 2 = α ∧ z i = y (j i) :=
          fun i => Classical.choose_spec (hjex i)
        have hcomb : z₀ = ∑ i, w i • y (j i) := by
          rw [← hsum]
          refine sum_congr rfl fun i _ => ?_
          rw [(hj i).2]
        let a : κ → K := fun i => y (j i)
        let b : κ → H := fun i => x (j i)
        have ha : ∀ i k, ‖a i - a k‖ ≤ ‖b i - b k‖ := by
          intro i k
          simpa [a, b, dist_eq_norm] using hdist (j i) (j k)
        have hpair_le : ∑ i, ∑ k, w i * w k * ‖a i - a k‖ ^ 2 ≤
            ∑ i, ∑ k, w i * w k * ‖b i - b k‖ ^ 2 :=
          sum_pairwise_sq_mono w a b hw0 ha
        have hsource : ∑ i, ∑ k, w i * w k * ‖b i - b k‖ ^ 2 ≤
            2 * ∑ i, w i * ‖b i - p‖ ^ 2 :=
          sum_pairwise_sq_le_point w b p hw1
        have hpr : ∀ i, ‖b i - p‖ ≤ r (j i) := by
          intro i
          simpa [b, dist_eq_norm] using hp (j i)
        have hpr_sq : ∑ i, w i * ‖b i - p‖ ^ 2 ≤ ∑ i, w i * r (j i) ^ 2 := by
          refine sum_le_sum fun i _ => ?_
          have hsq : ‖b i - p‖ ^ 2 ≤ r (j i) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) (hpr i) 2
          exact mul_le_mul_of_nonneg_left hsq (hw0 i)
        have hactive : ∑ i, w i * ‖z₀ - a i‖ ^ 2 =
            ∑ i, w i * r (j i) ^ 2 + α := by
          have hterm : ∀ i, ‖z₀ - a i‖ ^ 2 = r (j i) ^ 2 + α := by
            intro i
            have hdi : ‖z₀ - a i‖ ^ 2 - r (j i) ^ 2 = α := by
              simpa [a, dist_eq_norm] using (hj i).1
            linarith
          calc
            ∑ i, w i * ‖z₀ - a i‖ ^ 2 = ∑ i, w i * (r (j i) ^ 2 + α) := by
              refine sum_congr rfl fun i _ => ?_
              rw [hterm i]
            _ = ∑ i, w i * r (j i) ^ 2 + ∑ i, w i * α := by
              simp_rw [mul_add, sum_add_distrib]
            _ = ∑ i, w i * r (j i) ^ 2 + α := by
              rw [← Finset.sum_mul, hw1, one_mul]
        have htarget : ∑ i, ∑ k, w i * w k * ‖a i - a k‖ ^ 2 =
            2 * ∑ i, w i * ‖z₀ - a i‖ ^ 2 := by
          have hpair := sum_pairwise_sq_norm w a hw1
          have hvar := sum_w_norm_sub_sq_center w a hw1
          have hzu : ∑ i, w i • a i = z₀ := by simpa [a] using hcomb.symm
          calc
            ∑ i, ∑ k, w i * w k * ‖a i - a k‖ ^ 2
                = 2 * (∑ i, w i * ‖a i‖ ^ 2 - ‖∑ i, w i • a i‖ ^ 2) := hpair
            _ = 2 * ∑ i, w i * ‖(∑ j, w j • a j) - a i‖ ^ 2 := by rw [← hvar]
            _ = 2 * ∑ i, w i * ‖z₀ - a i‖ ^ 2 := by rw [hzu]
        linarith [hpair_le, hsource, hpr_sq, hactive, htarget]
      · let d : K := z₀ - q
        have hd_pos : 0 < ‖d‖ := by
          have : d ≠ 0 := by
            intro hd
            apply hzero
            simpa [d] using congrArg norm hd
          exact norm_pos_iff.mpr this
        have hchar : ∀ w ∈ convexHull ℝ S, ⟪d, w - q⟫ ≤ 0 := by
          intro w hw
          have := (norm_eq_iInf_iff_real_inner_le_zero (convex_convexHull ℝ S) hq).1 hqmin w hw
          simpa [d] using this
        have hinner_active : ∀ i, dist z₀ (y i) ^ 2 - r i ^ 2 = α →
            ‖d‖ ^ 2 ≤ ⟪z₀ - y i, d⟫ := by
          intro i hi
          have hyS : y i ∈ S := ⟨i, hi, rfl⟩
          have hyC : y i ∈ convexHull ℝ S := subset_convexHull _ _ hyS
          have hineq : ⟪d, y i - q⟫ ≤ 0 := hchar _ hyC
          have hsplit : ⟪d, z₀ - y i⟫ = ‖d‖ ^ 2 - ⟪d, y i - q⟫ := by
            have : z₀ - y i = d - (y i - q) := by simp [d]
            rw [this, inner_sub_right, real_inner_self_eq_norm_sq]
          rw [real_inner_comm] at hsplit
          linarith
        let step : ι → ℝ := fun i =>
          if dist z₀ (y i) ^ 2 - r i ^ 2 = α then 1
          else (α - (dist z₀ (y i) ^ 2 - r i ^ 2)) /
            (2 * ‖z₀ - y i‖ * ‖d‖ + ‖d‖ ^ 2 + 1)
        have hstep_pos : ∀ i, 0 < step i := by
          intro i
          by_cases hi : dist z₀ (y i) ^ 2 - r i ^ 2 = α
          · simp [step, hi]
          · have hlt : dist z₀ (y i) ^ 2 - r i ^ 2 < α :=
              lt_of_le_of_ne (le_φ z₀ i) hi
            have hden : 0 < 2 * ‖z₀ - y i‖ * ‖d‖ + ‖d‖ ^ 2 + 1 := by positivity
            have hnum : 0 < α - (dist z₀ (y i) ^ 2 - r i ^ 2) := by linarith
            simpa [step, hi] using div_pos hnum hden
        have hinf_pos : 0 < univ.inf' univ_nonempty step := by
          rw [lt_inf'_iff]
          intro i _
          exact hstep_pos i
        let t : ℝ := univ.inf' univ_nonempty step / 2
        have ht0 : 0 < t := by positivity
        have ht1 : t ≤ 1 / 2 := by
          dsimp [t]
          have hle : univ.inf' univ_nonempty step ≤ 1 := by
            obtain ⟨i, -, hi⟩ := exists_mem_eq_sup' univ_nonempty
              (fun i => dist z₀ (y i) ^ 2 - r i ^ 2)
            have hact : step i = 1 := by
              have hfi : dist z₀ (y i) ^ 2 - r i ^ 2 = α := by
                simpa [α, φ] using hi.symm
              simp [step, hfi]
            have : univ.inf' univ_nonempty step ≤ step i := by
              rw [inf'_le_iff]
              exact ⟨i, mem_univ i, le_rfl⟩
            simpa [hact] using this
          linarith
        let z₁ : K := z₀ - t • d
        have hφlt : φ z₁ < α := by
          have hterm : ∀ i, dist z₁ (y i) ^ 2 - r i ^ 2 < α := by
            intro i
            by_cases hi : dist z₀ (y i) ^ 2 - r i ^ 2 = α
            · have hinner := hinner_active i hi
              have hexpand : ‖z₁ - y i‖ ^ 2 =
                  ‖z₀ - y i‖ ^ 2 - 2 * t * ⟪z₀ - y i, d⟫ + t ^ 2 * ‖d‖ ^ 2 := by
                have : z₁ - y i = (z₀ - y i) - t • d := by
                  simp only [z₁]
                  abel
                rw [this, norm_sub_sq_real, real_inner_smul_right, norm_smul,
                  Real.norm_of_nonneg ht0.le]
                ring
              have hactive_norm : ‖z₀ - y i‖ ^ 2 - r i ^ 2 = α := by
                simpa [dist_eq_norm] using hi
              have hle : dist z₁ (y i) ^ 2 - r i ^ 2 ≤
                  α + t * ‖d‖ ^ 2 * (t - 2) := by
                rw [dist_eq_norm, hexpand]
                have htneg : -2 * t ≤ 0 := by nlinarith
                have hineq : -2 * t * ⟪z₀ - y i, d⟫ ≤ -2 * t * ‖d‖ ^ 2 := by
                  have := mul_le_mul_of_nonpos_left hinner htneg
                  linarith
                linarith [hactive_norm]
              have hdrop : α + t * ‖d‖ ^ 2 * (t - 2) < α := by
                have htwo : 0 < 2 - t := by linarith
                have hdsq : 0 < ‖d‖ ^ 2 := by positivity
                have : 0 < t * ‖d‖ ^ 2 * (2 - t) := by positivity
                linarith
              exact hle.trans_lt hdrop
            · set β : ℝ := dist z₀ (y i) ^ 2 - r i ^ 2
              set denom : ℝ := 2 * ‖z₀ - y i‖ * ‖d‖ + ‖d‖ ^ 2 + 1
              have hβ : β < α := lt_of_le_of_ne (le_φ z₀ i) hi
              have hden : 0 < denom := by positivity
              have hstep : step i = (α - β) / denom := by simp [step, hi, β, denom]
              have ht_le : t ≤ step i / 2 := by
                dsimp [t]
                have hinf : univ.inf' univ_nonempty step ≤ step i := by
                  rw [inf'_le_iff]
                  exact ⟨i, mem_univ i, le_rfl⟩
                linarith
              have hexpand : ‖z₁ - y i‖ ^ 2 ≤
                  ‖z₀ - y i‖ ^ 2 + 2 * t * ‖z₀ - y i‖ * ‖d‖ + t ^ 2 * ‖d‖ ^ 2 := by
                have hzsub : z₁ - y i = (z₀ - y i) - t • d := by
                  simp only [z₁]
                  abel
                rw [hzsub, norm_sub_sq_real, real_inner_smul_right, norm_smul,
                  Real.norm_of_nonneg ht0.le]
                have hlow : -(‖z₀ - y i‖ * ‖d‖) ≤ ⟪z₀ - y i, d⟫ := by
                  have hneg := real_inner_le_norm (z₀ - y i) (-d)
                  rw [inner_neg_right, norm_neg] at hneg
                  linarith
                have hsqt : (t * ‖d‖) ^ 2 = t ^ 2 * ‖d‖ ^ 2 := by ring
                nlinarith [hlow, hsqt, ht0.le]
              have hquad : t ^ 2 * ‖d‖ ^ 2 ≤ t * ‖d‖ ^ 2 := by
                have ht_le_one : t ≤ 1 := by linarith
                have : t ^ 2 ≤ t := by nlinarith [ht0.le, ht_le_one]
                exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
              have hle : dist z₁ (y i) ^ 2 - r i ^ 2 ≤
                  β + t * (2 * ‖z₀ - y i‖ * ‖d‖ + ‖d‖ ^ 2) := by
                have hβnorm : β = ‖z₀ - y i‖ ^ 2 - r i ^ 2 := by
                  simp [β, dist_eq_norm]
                rw [dist_eq_norm, hβnorm]
                linarith [hexpand, hquad]
              have hinc : t * (2 * ‖z₀ - y i‖ * ‖d‖ + ‖d‖ ^ 2) < t * denom := by
                linarith [ht0]
              have hhalf : t * denom ≤ (α - β) / 2 := by
                have hmul : t * denom ≤ (step i / 2) * denom :=
                  mul_le_mul_of_nonneg_right ht_le hden.le
                have hcancel : (step i / 2) * denom = (α - β) / 2 := by
                  rw [hstep]
                  field_simp [hden.ne']
                linarith
              have hmid : β + (α - β) / 2 < α := by linarith
              linarith
          obtain ⟨i, -, hi⟩ := exists_mem_eq_sup' univ_nonempty
            (fun j => dist z₁ (y j) ^ 2 - r j ^ 2)
          have := hterm i
          simpa [φ, hi] using this
        exact absurd (hglob z₁) (not_le_of_gt (by simpa [α] using hφlt))
    refine ⟨z₀, fun i => ?_⟩
    have hle : dist z₀ (y i) ^ 2 - r i ^ 2 ≤ α := le_φ z₀ i
    have hsq : dist z₀ (y i) ^ 2 ≤ r i ^ 2 := by linarith
    rw [dist_comm]
    have habs := (sq_le_sq).1 hsq
    rwa [abs_of_nonneg dist_nonneg, abs_of_nonneg (hr0 i)] at habs
  · exact ⟨0, fun i => (hι ⟨i⟩).elim⟩

/-- One new value preserves the Lipschitz bound against an existing partial extension. -/
private lemma exists_lipschitz_value
    {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
    {L : ℝ≥0} {t : Set H} (g : t → K) (hg : LipschitzWith L g) (x₀ : H) :
    ∃ y₀ : K, ∀ x : t, dist y₀ (g x) ≤ (L : ℝ) * dist (x : H) x₀ := by
  refine exists_iInter_closedBall_of_forall_finset (fun x : t => g x)
    (fun x : t => (L : ℝ) * dist (x : H) x₀) ?_
  intro s
  let ι := {i // i ∈ s}
  have hscale : ∀ a b : H, dist ((L : ℝ) • a) ((L : ℝ) • b) = (L : ℝ) * dist a b := by
    intro a b
    rw [dist_eq_norm, dist_eq_norm, ← smul_sub, norm_smul, Real.norm_of_nonneg L.coe_nonneg]
  obtain ⟨q, hq⟩ := exists_common_point_closedBall_of_dist_le
    (fun i : ι => (L : ℝ) • (i : H)) (fun i : ι => g i.1)
    (fun i : ι => (L : ℝ) * dist (i : H) x₀)
    (fun i j => by
      have hlip := hg.dist_le_mul i.1 j.1
      have hdist_sub : dist (i.1 : H) (j.1 : H) = dist i.1 j.1 := rfl
      calc
        dist (g i.1) (g j.1) ≤ (L : ℝ) * dist i.1 j.1 := by exact_mod_cast hlip
        _ = dist ((L : ℝ) • (i : H)) ((L : ℝ) • (j : H)) := by
              rw [hscale, hdist_sub])
    ⟨(L : ℝ) • x₀, fun i => (hscale (i : H) x₀).le⟩
  refine ⟨q, fun i hi => ?_⟩
  have hqi := hq ⟨i, hi⟩
  rwa [dist_comm] at hqi

/-- **05.33**: a Lipschitz map on any subset of a real inner-product space extends with
exactly the same bound into a complete real Hilbert target. The subset may be empty;
the domain need not be complete. -/
theorem exists_lipschitz_extension_hilbert {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
    (s : Set H) (f : s → K) {L : ℝ≥0} (hf : LipschitzWith L f) :
    ∃ g : H → K, LipschitzWith L g ∧ ∀ x : s, g x = f x := by
  classical
  let S : Set (Set (H × K)) := {G |
    (∀ x : s, ((x : H), f x) ∈ G) ∧
      ∀ ⦃x y : H⦄ ⦃a b : K⦄, (x, a) ∈ G → (y, b) ∈ G → dist a b ≤ (L : ℝ) * dist x y}
  let G0 : Set (H × K) := {p | ∃ x : s, p = ((x : H), f x)}
  have hG0 : G0 ∈ S := by
    refine ⟨fun x => ⟨x, rfl⟩, ?_⟩
    intro x y a b hx hy
    obtain ⟨u, hu⟩ := hx
    injection hu with hxu hau
    obtain ⟨v, hv⟩ := hy
    injection hv with hyv hbv
    have hlip := hf.dist_le_mul u v
    have hdist_sub : dist (u : H) (v : H) = dist u v := rfl
    calc
      dist a b = dist (f u) (f v) := by rw [hau, hbv]
      _ ≤ (L : ℝ) * dist u v := by exact_mod_cast hlip
      _ = (L : ℝ) * dist x y := by rw [hxu, hyv, hdist_sub]
  obtain ⟨G, -, hmax⟩ := zorn_subset_nonempty S
    (fun c hc hchain hne => by
      refine ⟨⋃₀ c, ?_, fun t ht => subset_sUnion_of_mem ht⟩
      refine ⟨?_, ?_⟩
      · intro x
        obtain ⟨G1, hG1⟩ := hne
        exact ⟨G1, hG1, (hc hG1).1 x⟩
      · intro x y a b hx hy
        obtain ⟨G1, hG1, hx1⟩ := hx
        obtain ⟨G2, hG2, hy2⟩ := hy
        by_cases hEq : G1 = G2
        · exact (hc hG1).2 (by simpa [hEq] using hx1) (by simpa [hEq] using hy2)
        · rcases hchain hG1 hG2 hEq with h12 | h21
          · exact (hc hG2).2 (h12 hx1) hy2
          · exact (hc hG1).2 hx1 (h21 hy2))
    G0 hG0
  have hG : G ∈ S := hmax.1
  have htotal : ∀ x : H, ∃ y : K, (x, y) ∈ G := by
    intro x₀
    by_cases hx₀ : ∃ y : K, (x₀, y) ∈ G
    · exact hx₀
    · let t : Set H := {x | ∃ y : K, (x, y) ∈ G}
      have hx₀t : x₀ ∉ t := hx₀
      let g : t → K := fun x => Classical.choose x.2
      have hg : LipschitzWith L g := by
        apply LipschitzWith.of_dist_le_mul
        intro u v
        have hu := Classical.choose_spec u.2
        have hv := Classical.choose_spec v.2
        have hle := hG.2 hu hv
        exact_mod_cast hle
      obtain ⟨y₀, hy₀⟩ := exists_lipschitz_value g hg x₀
      have hunique : ∀ {x : H} {a b : K}, (x, a) ∈ G → (x, b) ∈ G → a = b := by
        intro x a b ha hb
        have hle : dist a b ≤ (L : ℝ) * dist x x := hG.2 ha hb
        simp only [dist_self, mul_zero] at hle
        exact dist_eq_zero.mp (le_antisymm hle dist_nonneg)
      have hinsert : insert (x₀, y₀) G ∈ S := by
        refine ⟨fun x => subset_insert _ _ (hG.1 x), ?_⟩
        intro x y a b hx hy
        rw [mem_insert_iff] at hx hy
        rcases hx with hx | hx
        · rcases hy with hy | hy
          · obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hx
            obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hy
            simp
          · obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hx
            have hy_t : y ∈ t := ⟨b, hy⟩
            have hb : b = g ⟨y, hy_t⟩ :=
              hunique hy (Classical.choose_spec (⟨b, hy⟩ : ∃ z, (y, z) ∈ G))
            have hball := hy₀ ⟨y, hy_t⟩
            simpa [hb, dist_comm] using hball
        · rcases hy with hy | hy
          · obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hy
            have hx_t : x ∈ t := ⟨a, hx⟩
            have ha : a = g ⟨x, hx_t⟩ :=
              hunique hx (Classical.choose_spec (⟨a, hx⟩ : ∃ z, (x, z) ∈ G))
            have hball := hy₀ ⟨x, hx_t⟩
            simpa [ha, dist_comm] using hball
          · exact hG.2 hx hy
      exact ⟨y₀, hmax.mem_of_prop_insert hinsert⟩
  let g : H → K := fun x => Classical.choose (htotal x)
  refine ⟨g, ?_, ?_⟩
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    have hx := Classical.choose_spec (htotal x)
    have hy := Classical.choose_spec (htotal y)
    exact_mod_cast hG.2 hx hy
  · intro x
    have hfx : ((x : H), f x) ∈ G := hG.1 x
    have hgx : ((x : H), g (x : H)) ∈ G := Classical.choose_spec (htotal (x : H))
    have hle : dist (g (x : H)) (f x) ≤ (L : ℝ) * dist (x : H) (x : H) := hG.2 hgx hfx
    simp only [dist_self, mul_zero] at hle
    exact dist_eq_zero.mp (le_antisymm hle dist_nonneg)

end CKMA
