/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Defs

import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Exact Lipschitz extension between Hilbert spaces

Kirszbraun extension preserves the Lipschitz bound of a map from an arbitrary subset
of a real inner-product space into a complete real Hilbert space. The subset may be
empty and the source need not be complete. Norms, distances and Lipschitz predicates
are Mathlib's. Source: GAPS 05.33.

## Main results

* `CKMA.exists_lipschitz_extension_hilbert` (**05.33**): Kirszbraun's Lipschitz extension
  theorem for maps from a subset of a real inner-product space into a complete real
  inner-product space.
-/

public section

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

/-- Parallelogram-law bound on the squared distance between two points in a common intersection
of closed balls. -/
private lemma dist_sq_le_of_forall_dist_le
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    {ι : Type*} (c : ι → K) (r : ι → ℝ) (s : Finset ι) {x y : K}
    (hx : ∀ i ∈ s, dist x (c i) ≤ r i) (hy : ∀ i ∈ s, dist y (c i) ≤ r i) :
    dist x y ^ 2 ≤
      2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 -
        4 * sInf (norm '' {z : K | ∀ i ∈ s, dist z (c i) ≤ r i}) ^ 2 := by
  let feasible : Set K := {z | ∀ i ∈ s, dist z (c i) ≤ r i}
  let normImg : Set ℝ := norm '' feasible
  have hbb : BddBelow normImg := ⟨0, fun ρ hρ => by
    obtain ⟨_, _, rfl⟩ := hρ
    exact norm_nonneg _⟩
  have hne : normImg.Nonempty := ⟨‖x‖, x, hx, rfl⟩
  have hα_nonneg : 0 ≤ sInf normImg := le_csInf hne fun ρ hρ => by
    obtain ⟨_, _, rfl⟩ := hρ
    exact norm_nonneg _
  let mid : K := (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y
  have hmid : mid ∈ feasible := by
    intro i hi
    have : mid ∈ closedBall (c i) (r i) :=
      (convex_closedBall (c i) (r i)) (hx i hi) (hy i hi)
        (by positivity) (by positivity) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
    simpa [mem_closedBall] using this
  have hnorm_mid : sInf normImg ≤ ‖mid‖ := csInf_le hbb ⟨mid, hmid, rfl⟩
  have hpara := parallelogram_law_with_norm ℝ x y
  have hsum : ‖x + y‖ = 2 * ‖mid‖ := by
    have : x + y = (2 : ℝ) • mid := by
      simp only [mid, smul_add, smul_smul]
      have hcoef : (2 : ℝ) * (1 / 2) = 1 := by norm_num
      rw [hcoef, one_smul, one_smul]
    rw [this, norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    dist x y ^ 2 = ‖x - y‖ ^ 2 := by rw [dist_eq_norm]
    _ = 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 - ‖x + y‖ ^ 2 := by linarith [hpara]
    _ = 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 - 4 * ‖mid‖ ^ 2 := by rw [hsum]; ring
    _ ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 - 4 * sInf normImg ^ 2 := by
      have hsq : sInf normImg ^ 2 ≤ ‖mid‖ ^ 2 :=
        pow_le_pow_left₀ hα_nonneg hnorm_mid 2
      linarith

/-- The norms of a set are bounded below by zero. -/
private lemma bddBelow_norm_image {K : Type*} [NormedAddCommGroup K] (S : Set K) :
    BddBelow (norm '' S) :=
  ⟨0, by
    rintro _ ⟨z, -, rfl⟩
    exact norm_nonneg z⟩

/-- The infimum of the norms of a nonempty set is approached by norms of its points. -/
private lemma exists_mem_norm_lt_sInf_add {K : Type*} [NormedAddCommGroup K] {S : Set K}
    (hS : S.Nonempty) {ε : ℝ} (hε : 0 < ε) : ∃ z ∈ S, ‖z‖ < sInf (norm '' S) + ε := by
  obtain ⟨_, ⟨z, hz, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt (hS.image _) (lt_add_of_pos_right _ hε)
  exact ⟨z, hz, hlt⟩

/-- A sequence squeezed between `A - 1 / (n + 1)` and `A` tends to `A`. -/
private lemma tendsto_of_sub_one_div_lt_of_le {a : ℕ → ℝ} {A : ℝ}
    (hlow : ∀ n : ℕ, A - 1 / (n + 1 : ℝ) < a n) (hup : ∀ n, a n ≤ A) :
    Tendsto a atTop (𝓝 A) := by
  have hlower : Tendsto (fun n : ℕ => A - 1 / (n + 1 : ℝ)) atTop (𝓝 A) := by
    simpa using tendsto_const_nhds.sub (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlower tendsto_const_nhds
    (fun n => (hlow n).le) hup

/-- A sequence squeezed between a convergent sequence `a n` and `a n + 1 / (n + 1)` has the
same limit. -/
private lemma tendsto_of_le_of_lt_add_one_div {a b : ℕ → ℝ} {A : ℝ}
    (ha : Tendsto a atTop (𝓝 A)) (hlow : ∀ n, a n ≤ b n)
    (hup : ∀ n : ℕ, b n < a n + 1 / (n + 1 : ℝ)) : Tendsto b atTop (𝓝 A) := by
  have hupper : Tendsto (fun n : ℕ => a n + 1 / (n + 1 : ℝ)) atTop (𝓝 A) := by
    simpa using ha.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le ha hupper hlow fun n => (hup n).le

/-- A monotone function on finite sets admits an increasing sequence of finite sets along which
its values come within `1 / (n + 1)` of the supremum of its range. -/
private lemma exists_monotone_finset_sub_one_div_lt {ι : Type*} (α : Finset ι → ℝ)
    (hα : Monotone α) :
    ∃ s : ℕ → Finset ι, Monotone s ∧
      ∀ n : ℕ, sSup (Set.range α) - 1 / (n + 1 : ℝ) < α (s n) := by
  classical
  have hclose : ∀ n : ℕ, ∃ t : Finset ι, sSup (Set.range α) - 1 / (n + 1 : ℝ) < α t := by
    intro n
    obtain ⟨_, ⟨t, rfl⟩, ht⟩ :=
      exists_lt_of_lt_csSup (Set.range_nonempty α) (sub_lt_self _ Nat.one_div_pos_of_nat)
    exact ⟨t, ht⟩
  choose u hu using hclose
  refine ⟨fun n => (Finset.range (n + 1)).biUnion u, fun n m hnm => ?_, fun n => ?_⟩
  · exact Finset.biUnion_subset_biUnion_of_subset_left _
      (Finset.range_subset_range.mpr (Nat.succ_le_succ hnm))
  · exact (hu n).trans_le
      (hα (Finset.subset_biUnion_of_mem u (Finset.self_mem_range_succ n)))

/-- If the squared distances of a sequence are bounded by the parallelogram defect between norms
converging to `A` and lower bounds `α n` with `α n ^ 2 → A ^ 2`, then the sequence is Cauchy. -/
private lemma cauchySeq_of_dist_sq_le {K : Type*} [NormedAddCommGroup K] {z : ℕ → K}
    {α : ℕ → ℝ} {A : ℝ} (hz : Tendsto (fun n => ‖z n‖ ^ 2) atTop (𝓝 (A ^ 2)))
    (hα : Tendsto (fun n => α n ^ 2) atTop (𝓝 (A ^ 2)))
    (hdist : ∀ {n m}, n ≤ m →
      dist (z n) (z m) ^ 2 ≤ 2 * ‖z n‖ ^ 2 + 2 * ‖z m‖ ^ 2 - 4 * α n ^ 2) :
    CauchySeq z := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  have hη : 0 < ε ^ 2 / 8 := by positivity
  obtain ⟨N1, hN1⟩ := (Metric.tendsto_atTop.mp hz) (ε ^ 2 / 8) hη
  obtain ⟨N2, hN2⟩ := (Metric.tendsto_atTop.mp hα) (ε ^ 2 / 8) hη
  have hstep : ∀ {k l}, max N1 N2 ≤ k → max N1 N2 ≤ l → k ≤ l →
      dist (z k) (z l) ^ 2 < ε ^ 2 := by
    intro k l hk hl hkl
    have hkA : |‖z k‖ ^ 2 - A ^ 2| < ε ^ 2 / 8 := hN1 k (le_trans (le_max_left _ _) hk)
    have hlA : |‖z l‖ ^ 2 - A ^ 2| < ε ^ 2 / 8 := hN1 l (le_trans (le_max_left _ _) hl)
    have hαk : |α k ^ 2 - A ^ 2| < ε ^ 2 / 8 := hN2 k (le_trans (le_max_right _ _) hk)
    rw [abs_lt] at hkA hlA hαk
    nlinarith [hdist hkl]
  refine ⟨max N1 N2, fun m hm n hn => ?_⟩
  have hsq : dist (z m) (z n) ^ 2 < ε ^ 2 := by
    rcases le_total m n with hmn | hnm
    · exact hstep hm hn hmn
    · rw [dist_comm]
      exact hstep hn hm hnm
  have := (sq_lt_sq).1 hsq
  rwa [abs_of_nonneg dist_nonneg, abs_of_pos hε] at this

/-- Two sequences whose norms tend to `A`, and whose squared distances are bounded by the
parallelogram defect against lower bounds `α n → A`, become arbitrarily close. -/
private lemma tendsto_dist_of_dist_sq_le {K : Type*} [NormedAddCommGroup K] {w z : ℕ → K}
    {α : ℕ → ℝ} {A : ℝ} (hw : Tendsto (fun n => ‖w n‖) atTop (𝓝 A))
    (hz : Tendsto (fun n => ‖z n‖) atTop (𝓝 A)) (hα : Tendsto α atTop (𝓝 A))
    (hdist : ∀ n, dist (w n) (z n) ^ 2 ≤ 2 * ‖w n‖ ^ 2 + 2 * ‖z n‖ ^ 2 - 4 * α n ^ 2) :
    Tendsto (fun n => dist (w n) (z n)) atTop (𝓝 0) := by
  have hupper : Tendsto (fun n => 2 * ‖w n‖ ^ 2 + 2 * ‖z n‖ ^ 2 - 4 * α n ^ 2) atTop (𝓝 0) := by
    have htend := (((hw.pow 2).const_mul 2).add ((hz.pow 2).const_mul 2)).sub
      ((hα.pow 2).const_mul 4)
    have hzero : (2 : ℝ) * A ^ 2 + 2 * A ^ 2 - 4 * A ^ 2 = 0 := by ring
    rwa [hzero] at htend
  have hsq : Tendsto (fun n => dist (w n) (z n) ^ 2) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
      (fun _ => sq_nonneg _) hdist
  simpa [Real.sqrt_sq dist_nonneg] using hsq.sqrt

/-- In a complete real inner-product space, closed balls with the finite-intersection property
have nonempty total intersection. -/
private lemma exists_iInter_closedBall_of_forall_finset
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
    {ι : Type*} (c : ι → K) (r : ι → ℝ)
    (hfin : ∀ s : Finset ι, ∃ z : K, ∀ i ∈ s, dist z (c i) ≤ r i) :
    ∃ z : K, ∀ i, dist z (c i) ≤ r i := by
  classical
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨i0⟩⟩
  · exact ⟨0, fun i => isEmptyElim i⟩
  let feasible (s : Finset ι) : Set K := {z | ∀ i ∈ s, dist z (c i) ≤ r i}
  let α (s : Finset ι) : ℝ := sInf (norm '' feasible s)
  have hfeas : ∀ s : Finset ι, (feasible s).Nonempty := by
    intro s
    obtain ⟨z, hz⟩ := hfin s
    exact ⟨z, hz⟩
  have hα_mono : Monotone α := fun s t hst =>
    csInf_le_csInf (bddBelow_norm_image _) ((hfeas t).image _)
      (image_mono fun z hz i hi => hz i (hst hi))
  have hα_bdd : ∀ s, α s ≤ ‖c i0‖ + r i0 := by
    intro s
    obtain ⟨z, hz⟩ := hfeas (insert i0 s)
    have hz0 : dist z (c i0) ≤ r i0 := hz i0 (mem_insert_self _ _)
    calc
      α s ≤ α (insert i0 s) := hα_mono (subset_insert i0 s)
      _ ≤ ‖z‖ := csInf_le (bddBelow_norm_image _) ⟨z, hz, rfl⟩
      _ ≤ ‖c i0‖ + r i0 := by linarith [norm_sub_norm_le z (c i0), dist_eq_norm z (c i0)]
  let A : ℝ := sSup (range α)
  have hA_bdd : BddAbove (range α) := ⟨‖c i0‖ + r i0, by
    rintro _ ⟨s, rfl⟩
    exact hα_bdd s⟩
  have hα_le_A : ∀ s, α s ≤ A := fun s => le_csSup hA_bdd (mem_range_self s)
  obtain ⟨sSeq, hs_mono, hα_gt⟩ := exists_monotone_finset_sub_one_div_lt α hα_mono
  have hα_lim : Tendsto (fun n => α (sSeq n)) atTop (𝓝 A) :=
    tendsto_of_sub_one_div_lt_of_le hα_gt fun n => hα_le_A _
  -- Near-minimal points of the feasible sets along `sSeq` form a Cauchy sequence.
  choose zSeq hzSeq using fun n : ℕ =>
    exists_mem_norm_lt_sInf_add (hfeas (sSeq n)) (Nat.one_div_pos_of_nat (n := n))
  have hnorm_lim : Tendsto (fun n => ‖zSeq n‖) atTop (𝓝 A) :=
    tendsto_of_le_of_lt_add_one_div hα_lim
      (fun n => csInf_le (bddBelow_norm_image _) ⟨zSeq n, (hzSeq n).1, rfl⟩)
      fun n => (hzSeq n).2
  have hCauchy : CauchySeq zSeq :=
    cauchySeq_of_dist_sq_le (hnorm_lim.pow 2) (hα_lim.pow 2) fun {n m} hnm =>
      dist_sq_le_of_forall_dist_le c r (sSeq n) (hzSeq n).1
        fun i hi => (hzSeq m).1 i (hs_mono hnm hi)
  obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete hCauchy
  refine ⟨z, fun j => ?_⟩
  -- Near-minimal points of the enlarged sets `insert j (sSeq n)` have the same limit `z`.
  let s' : ℕ → Finset ι := fun n => insert j (sSeq n)
  have hα'_lim : Tendsto (fun n => α (s' n)) atTop (𝓝 A) :=
    tendsto_of_sub_one_div_lt_of_le
      (fun n => (hα_gt n).trans_le (hα_mono (subset_insert _ _))) fun n => hα_le_A _
  choose wSeq hwSeq using fun n : ℕ =>
    exists_mem_norm_lt_sInf_add (hfeas (s' n)) (Nat.one_div_pos_of_nat (n := n))
  have hwnorm_lim : Tendsto (fun n => ‖wSeq n‖) atTop (𝓝 A) :=
    tendsto_of_le_of_lt_add_one_div hα'_lim
      (fun n => csInf_le (bddBelow_norm_image _) ⟨wSeq n, (hwSeq n).1, rfl⟩)
      fun n => (hwSeq n).2
  have hdist_lim : Tendsto (fun n => dist (wSeq n) (zSeq n)) atTop (𝓝 0) :=
    tendsto_dist_of_dist_sq_le hwnorm_lim hnorm_lim hα_lim fun n =>
      dist_sq_le_of_forall_dist_le c r (sSeq n)
        (fun i hi => (hwSeq n).1 i (Finset.mem_insert_of_mem hi)) (hzSeq n).1
  have hw_tendsto : Tendsto wSeq atTop (𝓝 z) :=
    tendsto_of_tendsto_of_dist hz <| by
      convert hdist_lim using 2
      rw [dist_comm]
  exact le_of_tendsto (hw_tendsto.dist tendsto_const_nhds)
    (Eventually.of_forall fun n => (hwSeq n).1 j (mem_insert_self _ _))

/-- The largest excess `dist z (y i) ^ 2 - r i ^ 2` of a point over a finite family of balls. -/
private def maxExcess {K ι : Type*} [NormedAddCommGroup K] [Fintype ι] [Nonempty ι]
    (y : ι → K) (r : ι → ℝ) (z : K) : ℝ :=
  univ.sup' univ_nonempty fun i => dist z (y i) ^ 2 - r i ^ 2

section maxExcess

variable {K ι : Type*} [NormedAddCommGroup K] [Fintype ι] [Nonempty ι] (y : ι → K) (r : ι → ℝ)

/-- Each excess is at most the maximal excess. -/
private lemma le_maxExcess (z : K) (i : ι) : dist z (y i) ^ 2 - r i ^ 2 ≤ maxExcess y r z :=
  le_sup' (fun i => dist z (y i) ^ 2 - r i ^ 2) (mem_univ i)

/-- The maximal excess is attained at some ball. -/
private lemma exists_maxExcess_eq (z : K) :
    ∃ i, dist z (y i) ^ 2 - r i ^ 2 = maxExcess y r z := by
  obtain ⟨i, -, hi⟩ := exists_mem_eq_sup' univ_nonempty fun i => dist z (y i) ^ 2 - r i ^ 2
  exact ⟨i, hi.symm⟩

/-- The maximal excess is below `c` exactly when every excess is. -/
private lemma maxExcess_lt_iff {z : K} {c : ℝ} :
    maxExcess y r z < c ↔ ∀ i, dist z (y i) ^ 2 - r i ^ 2 < c := by
  simp only [maxExcess, sup'_lt_iff, Finset.mem_univ, true_imp_iff]

/-- The maximal excess is continuous. -/
private lemma continuous_maxExcess : Continuous (maxExcess y r) :=
  Continuous.finset_sup'_apply univ_nonempty fun _ _ =>
    ((continuous_id.dist continuous_const).pow 2).sub continuous_const

variable [InnerProductSpace ℝ K]

/-- Orthogonal projection onto a subspace containing the centres does not increase the maximal
excess. -/
private lemma maxExcess_starProjection_le (V : Submodule ℝ K) [V.HasOrthogonalProjection]
    (hyV : ∀ i, y i ∈ V) (z : K) : maxExcess y r (V.starProjection z) ≤ maxExcess y r z := by
  refine sup'_le _ _ fun i _ => ?_
  have hle : ‖V.starProjection (z - y i)‖ ^ 2 ≤ ‖z - y i‖ ^ 2 := by
    have hpyth := Submodule.norm_sq_eq_add_norm_sq_starProjection (z - y i) V
    nlinarith [sq_nonneg ‖Vᗮ.starProjection (z - y i)‖]
  have hlin : V.starProjection (z - y i) = V.starProjection z - y i := by
    rw [map_sub, Submodule.starProjection_eq_self_iff.mpr (hyV i)]
  have hterm : dist (V.starProjection z) (y i) ^ 2 ≤ dist z (y i) ^ 2 := by
    rw [dist_eq_norm, dist_eq_norm, ← hlin]
    exact hle
  exact (sub_le_sub_right hterm _).trans (le_maxExcess y r z i)

/-- The maximal excess attains its minimum. A minimiser is found on a large closed ball of the
finite-dimensional span of the centres, onto which projection does not increase the excess. -/
private lemma exists_forall_maxExcess_le : ∃ z₀ : K, ∀ z, maxExcess y r z₀ ≤ maxExcess y r z := by
  let V : Submodule ℝ K := Submodule.span ℝ (range y)
  have : FiniteDimensional ℝ V := FiniteDimensional.span_of_finite ℝ (finite_range y)
  have : CompleteSpace V := FiniteDimensional.complete ℝ V
  have hyV : ∀ i, y i ∈ V := fun i => Submodule.subset_span (mem_range_self i)
  let i0 : ι := Classical.arbitrary ι
  let base : ℝ := maxExcess y r 0
  let bound : ℝ := max (base + r i0 ^ 2 + 1) 1
  let R : ℝ := ‖y i0‖ + Real.sqrt bound + 1
  have hR0 : 0 ≤ R := by positivity
  -- Outside the ball of radius `R` the excess exceeds its value at the origin.
  have hcoe : ∀ v : V, R < ‖v‖ → base < maxExcess y r (v : K) := by
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
    have hle : ‖(v : K) - y i0‖ ^ 2 - r i0 ^ 2 ≤ maxExcess y r (v : K) := by
      simpa [dist_eq_norm] using le_maxExcess y r (v : K) i0
    linarith
  have hφV : Continuous fun v : V => maxExcess y r (v : K) :=
    (continuous_maxExcess y r).comp continuous_subtype_val
  obtain ⟨vMin, -, hminOn⟩ :=
    (isCompact_closedBall (0 : V) R).exists_isMinOn ⟨0, mem_closedBall_self hR0⟩ hφV.continuousOn
  have hball : ∀ v : V, ‖v‖ ≤ R → maxExcess y r (vMin : K) ≤ maxExcess y r (v : K) := by
    intro v hv
    exact hminOn (by simpa [mem_closedBall, dist_eq_norm] using hv)
  have hV : ∀ v : V, maxExcess y r (vMin : K) ≤ maxExcess y r (v : K) := by
    intro v
    by_cases hv : ‖v‖ ≤ R
    · exact hball v hv
    · have hlt : base < maxExcess y r (v : K) := hcoe v (lt_of_not_ge hv)
      have h0 : maxExcess y r (vMin : K) ≤ base := by
        simpa using hball 0 (by simpa using hR0)
      linarith
  refine ⟨vMin, fun z => ?_⟩
  have hπ : maxExcess y r (V.orthogonalProjectionOnto z : K) ≤ maxExcess y r z := by
    simpa only [Submodule.coe_orthogonalProjectionOnto_apply] using
      maxExcess_starProjection_le y r V hyV z
  exact (hV (V.orthogonalProjectionOnto z)).trans hπ

/-- A step from `u` against a direction `d ≠ 0` with `‖d‖ ^ 2 ≤ ⟪u, d⟫`, of length `t ∈ (0, 2)`,
strictly decreases the norm. -/
private lemma norm_sub_smul_sq_lt {u d : K} (hd : d ≠ 0) (hud : ‖d‖ ^ 2 ≤ ⟪u, d⟫) {t : ℝ}
    (ht0 : 0 < t) (ht2 : t < 2) : ‖u - t • d‖ ^ 2 < ‖u‖ ^ 2 := by
  rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_of_nonneg ht0.le]
  have hdsq : 0 < ‖d‖ ^ 2 := by
    have := norm_pos_iff.mpr hd
    positivity
  nlinarith [mul_le_mul_of_nonneg_left hud ht0.le, mul_pos (mul_pos ht0 hdsq) (sub_pos.2 ht2)]

/-- If a nonzero direction `d` satisfies `‖d‖ ^ 2 ≤ ⟪z₀ - y i, d⟫` at every ball where the excess
of `z₀` is maximal, then a small step from `z₀` against `d` lowers the maximal excess. -/
private lemma exists_maxExcess_lt {z₀ d : K} (hd : d ≠ 0)
    (hact : ∀ i, dist z₀ (y i) ^ 2 - r i ^ 2 = maxExcess y r z₀ → ‖d‖ ^ 2 ≤ ⟪z₀ - y i, d⟫) :
    ∃ z₁, maxExcess y r z₁ < maxExcess y r z₀ := by
  have hev : ∀ i, ∀ᶠ t in 𝓝[>] (0 : ℝ),
      dist (z₀ - t • d) (y i) ^ 2 - r i ^ 2 < maxExcess y r z₀ := by
    intro i
    by_cases hi : dist z₀ (y i) ^ 2 - r i ^ 2 = maxExcess y r z₀
    · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 2 by norm_num)] with t ht
      have key := norm_sub_smul_sq_lt hd (hact i hi) ht.1 ht.2
      have hsub : z₀ - t • d - y i = (z₀ - y i) - t • d := by abel
      rw [dist_eq_norm, hsub]
      rw [dist_eq_norm] at hi
      linarith
    · have hlt : dist z₀ (y i) ^ 2 - r i ^ 2 < maxExcess y r z₀ :=
        (le_maxExcess y r z₀ i).lt_of_ne hi
      have hcont : Continuous fun t : ℝ => dist (z₀ - t • d) (y i) ^ 2 - r i ^ 2 :=
        (((continuous_const.sub (continuous_id.smul continuous_const)).dist
          continuous_const).pow 2).sub continuous_const
      have htend := hcont.tendsto 0
      simp only [zero_smul, sub_zero] at htend
      exact mem_nhdsWithin_of_mem_nhds (htend.eventually (gt_mem_nhds hlt))
  obtain ⟨t, ht⟩ := (eventually_all.2 hev).exists
  exact ⟨z₀ - t • d, (maxExcess_lt_iff y r).2 ht⟩

/-- If a point is a convex combination of the centres at which its excess is maximal, and the
centres are images of a source configuration under a distance-nonincreasing correspondence with
a point `p` within distance `r i` of each source point, then the maximal excess is nonpositive. -/
private lemma maxExcess_le_zero_of_mem_convexHull
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (x : ι → H)
    (hdist : ∀ i j, dist (y i) (y j) ≤ dist (x i) (x j)) {p : H}
    (hp : ∀ i, dist (x i) p ≤ r i) {z₀ : K}
    (hz₀ : z₀ ∈ convexHull ℝ
      {q | ∃ i, dist z₀ (y i) ^ 2 - r i ^ 2 = maxExcess y r z₀ ∧ q = y i}) :
    maxExcess y r z₀ ≤ 0 := by
  obtain ⟨κ, _, w, z, hw0, hw1, hz, hsum⟩ := (mem_convexHull_iff_exists_fintype).1 hz₀
  have hjex : ∀ i : κ, ∃ j : ι,
      dist z₀ (y j) ^ 2 - r j ^ 2 = maxExcess y r z₀ ∧ z i = y j := fun i => hz i
  choose j hj using hjex
  let a : κ → K := fun i => y (j i)
  let b : κ → H := fun i => x (j i)
  have hcomb : ∑ i, w i • a i = z₀ := by
    rw [← hsum]
    refine sum_congr rfl fun i _ => ?_
    rw [(hj i).2]
  have hpair_le : ∑ i, ∑ k, w i * w k * ‖a i - a k‖ ^ 2 ≤
      ∑ i, ∑ k, w i * w k * ‖b i - b k‖ ^ 2 :=
    sum_pairwise_sq_mono w a b hw0 fun i k => by
      simpa [a, b, dist_eq_norm] using hdist (j i) (j k)
  have hsource : ∑ i, ∑ k, w i * w k * ‖b i - b k‖ ^ 2 ≤ 2 * ∑ i, w i * ‖b i - p‖ ^ 2 :=
    sum_pairwise_sq_le_point w b p hw1
  have hpr_sq : ∑ i, w i * ‖b i - p‖ ^ 2 ≤ ∑ i, w i * r (j i) ^ 2 := by
    refine sum_le_sum fun i _ => ?_
    have hpr : ‖b i - p‖ ≤ r (j i) := by simpa [b, dist_eq_norm] using hp (j i)
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hpr 2) (hw0 i)
  have hactive : ∑ i, w i * ‖z₀ - a i‖ ^ 2 = ∑ i, w i * r (j i) ^ 2 + maxExcess y r z₀ := by
    have hterm : ∀ i, ‖z₀ - a i‖ ^ 2 = r (j i) ^ 2 + maxExcess y r z₀ := by
      intro i
      have hdi : ‖z₀ - a i‖ ^ 2 - r (j i) ^ 2 = maxExcess y r z₀ := by
        simpa [a, dist_eq_norm] using (hj i).1
      linarith
    calc
      ∑ i, w i * ‖z₀ - a i‖ ^ 2 = ∑ i, w i * (r (j i) ^ 2 + maxExcess y r z₀) := by
        refine sum_congr rfl fun i _ => ?_
        rw [hterm i]
      _ = ∑ i, w i * r (j i) ^ 2 + ∑ i, w i * maxExcess y r z₀ := by
        simp_rw [mul_add, sum_add_distrib]
      _ = ∑ i, w i * r (j i) ^ 2 + maxExcess y r z₀ := by
        rw [← Finset.sum_mul, hw1, one_mul]
  have htarget : ∑ i, ∑ k, w i * w k * ‖a i - a k‖ ^ 2 = 2 * ∑ i, w i * ‖z₀ - a i‖ ^ 2 := by
    rw [sum_pairwise_sq_norm w a hw1, ← sum_w_norm_sub_sq_center w a hw1, hcomb]
  linarith [hpair_le, hsource, hpr_sq, hactive, htarget]

end maxExcess

/-- Finite Kirszbraun lemma: a distance-nonincreasing cloud of balls that meets in the source
meets in the target. -/
private lemma exists_common_point_closedBall_of_dist_le
    {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    {ι : Type*} [Fintype ι] (x : ι → H) (y : ι → K) (r : ι → ℝ)
    (hdist : ∀ i j, dist (y i) (y j) ≤ dist (x i) (x j))
    (hp : ∃ p : H, ∀ i, dist (x i) p ≤ r i) :
    ∃ q : K, ∀ i, dist (y i) q ≤ r i := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨0, fun i => isEmptyElim i⟩
  obtain ⟨p, hp⟩ := hp
  -- A minimiser `z₀` of the maximal excess has nonpositive excess.
  obtain ⟨z₀, hglob⟩ := exists_forall_maxExcess_le y r
  let S : Set K := {q | ∃ i, dist z₀ (y i) ^ 2 - r i ^ 2 = maxExcess y r z₀ ∧ q = y i}
  have hS_ne : S.Nonempty := by
    obtain ⟨i, hi⟩ := exists_maxExcess_eq y r z₀
    exact ⟨y i, i, hi, rfl⟩
  have hS_fin : S.Finite := (finite_range y).subset fun q hq => by
    obtain ⟨i, _, rfl⟩ := hq
    exact mem_range_self i
  obtain ⟨q, hq, hqmin⟩ := exists_norm_eq_iInf_of_complete_convex
    (hS_ne.mono (subset_convexHull _ _)) (hS_fin.isCompact_convexHull ℝ).isComplete
    (convex_convexHull ℝ S) z₀
  have hα_le : maxExcess y r z₀ ≤ 0 := by
    by_cases hzq : z₀ = q
    · rw [← hzq] at hq
      exact maxExcess_le_zero_of_mem_convexHull y r x hdist hp hq
    · -- Otherwise the direction towards the nearest point `q` of the hull lowers the excess.
      have hact : ∀ i, dist z₀ (y i) ^ 2 - r i ^ 2 = maxExcess y r z₀ →
          ‖z₀ - q‖ ^ 2 ≤ ⟪z₀ - y i, z₀ - q⟫ := by
        intro i hi
        have hineq : ⟪z₀ - q, y i - q⟫ ≤ 0 :=
          (norm_eq_iInf_iff_real_inner_le_zero (convex_convexHull ℝ S) hq).1 hqmin _
            (subset_convexHull _ _ ⟨i, hi, rfl⟩)
        have hsplit : ⟪z₀ - q, z₀ - y i⟫ = ‖z₀ - q‖ ^ 2 - ⟪z₀ - q, y i - q⟫ := by
          have : z₀ - y i = (z₀ - q) - (y i - q) := by abel
          rw [this, inner_sub_right, real_inner_self_eq_norm_sq]
        rw [real_inner_comm] at hsplit
        linarith
      obtain ⟨z₁, hz₁⟩ := exists_maxExcess_lt y r (sub_ne_zero.2 hzq) hact
      exact absurd (hglob z₁) (not_le_of_gt hz₁)
  refine ⟨z₀, fun i => ?_⟩
  have hsq : dist z₀ (y i) ^ 2 ≤ r i ^ 2 := by linarith [le_maxExcess y r z₀ i]
  rw [dist_comm]
  have habs := (sq_le_sq).1 hsq
  rwa [abs_of_nonneg dist_nonneg, abs_of_nonneg (dist_nonneg.trans (hp i))] at habs

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
