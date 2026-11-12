/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.Operator.Dilation.CommutantBlock
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Topology.MetricSpace.Basic

/-!
# Commutant lifting series

The blocks produced by the defect iteration are pairwise orthogonal after the powers of the
isometric coextension. Their sum, together with the compressed copy of `X`, is a norm-preserving
lift that commutes with the dilation and coextends `X`.
-/

@[expose] public section

noncomputable section

namespace CKMA

open scoped InnerProductSpace Topology
open ContinuousLinearMap Filter

universe u

variable {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Partial sum of the commutant lifting series. -/
def commutantPartial (T X : H →L[ℂ] H) (hT : ‖T‖ ≤ 1) (hXT : Commute X T)
    (J : H →ₗᵢ[ℂ] K) (V : K →ₗᵢ[ℂ] K)
    (hcoin : ∀ y : K, J.toContinuousLinearMap.adjoint (V y) =
      T (J.toContinuousLinearMap.adjoint y)) (n : ℕ) : K →L[ℂ] K :=
  J.toContinuousLinearMap.comp (coextensionCompress X J) +
    ∑ k ∈ Finset.range n,
      (V.toContinuousLinearMap ^ k).comp
        ((dilationDefectSpace T J V).subtypeL.comp
          (commutantLiftBlock T X hT hXT J V hcoin k))

/-- Evaluation of a partial sum. -/
theorem commutantPartial_apply (T X : H →L[ℂ] H) (hT : ‖T‖ ≤ 1) (hXT : Commute X T)
    (J : H →ₗᵢ[ℂ] K) (V : K →ₗᵢ[ℂ] K)
    (hcoin : ∀ y : K, J.toContinuousLinearMap.adjoint (V y) =
      T (J.toContinuousLinearMap.adjoint y)) (n : ℕ) (y : K) :
    commutantPartial T X hT hXT J V hcoin n y =
      J (coextensionCompress X J y) +
        ∑ k ∈ Finset.range n,
          (V.toContinuousLinearMap ^ k)
            ((dilationDefectSpace T J V).subtypeL
              (commutantLiftBlock T X hT hXT J V hcoin k y)) := by
  simp [commutantPartial, add_apply, sum_apply, comp_apply,
    LinearIsometry.coe_toContinuousLinearMap]

/-- A powered block has the same norm as the block. -/
theorem norm_pow_liftBlock (T X : H →L[ℂ] H) (hT : ‖T‖ ≤ 1) (hXT : Commute X T)
    (J : H →ₗᵢ[ℂ] K) (V : K →ₗᵢ[ℂ] K)
    (hcoin : ∀ y : K, J.toContinuousLinearMap.adjoint (V y) =
      T (J.toContinuousLinearMap.adjoint y)) (k : ℕ) (y : K) :
    ‖(V.toContinuousLinearMap ^ k)
        ((dilationDefectSpace T J V).subtypeL
          (commutantLiftBlock T X hT hXT J V hcoin k y))‖ =
      ‖commutantLiftBlock T X hT hXT J V hcoin k y‖ := by
  rw [← isometry_pow_apply, (V ^ k).norm_map, Submodule.subtypeL_apply, Submodule.norm_coe]

/-- Squared norm of a partial sum, by orthogonality of the defect orbit. -/
theorem norm_sq_commutantPartial (T X : H →L[ℂ] H) (hT : ‖T‖ ≤ 1) (hXT : Commute X T)
    (J : H →ₗᵢ[ℂ] K) (V : K →ₗᵢ[ℂ] K)
    (hcoin : ∀ y : K, J.toContinuousLinearMap.adjoint (V y) =
      T (J.toContinuousLinearMap.adjoint y)) (n : ℕ) (y : K) :
    ‖commutantPartial T X hT hXT J V hcoin n y‖ ^ 2 =
      ‖coextensionCompress X J y‖ ^ 2 +
        ∑ k ∈ Finset.range n, ‖commutantLiftBlock T X hT hXT J V hcoin k y‖ ^ 2 := by
  let v : ℕ → K := fun k =>
    (V.toContinuousLinearMap ^ k)
      ((dilationDefectSpace T J V).subtypeL
        (commutantLiftBlock T X hT hXT J V hcoin k y))
  have horth : ⟪J (coextensionCompress X J y), ∑ k ∈ Finset.range n, v k⟫_ℂ = 0 := by
    rw [inner_sum]
    refine Finset.sum_eq_zero fun k _ => ?_
    exact inner_embed_defectSpace_pow_eq_zero T J V hcoin k (coextensionCompress X J y)
      (commutantLiftBlock T X hT hXT J V hcoin k y).property
  have hpair : ∀ i j : ℕ, 0 ≤ i → i < n → 0 ≤ j → j < n → i ≠ j → ⟪v i, v j⟫_ℂ = 0 := by
    intro i j _ hi _ hj hij
    exact inner_defectSpace_pow_eq_zero T J V hcoin hij
      (commutantLiftBlock T X hT hXT J V hcoin i y).property
      (commutantLiftBlock T X hT hXT J V hcoin j y).property
  have hsum := norm_sq_sum_Ico_orthogonal v 0 n hpair
  have hrange : ∑ k ∈ Finset.range n, v k = ∑ k ∈ Finset.Ico 0 n, v k := by
    rw [Finset.range_eq_Ico]
  rw [hrange] at horth
  rw [commutantPartial_apply, hrange]
  have hpy := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth
  rw [← pow_two, ← pow_two, ← pow_two] at hpy
  rw [hpy, hsum, J.norm_map, Finset.range_eq_Ico]
  refine congrArg (fun t => ‖coextensionCompress X J y‖ ^ 2 + t) ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  exact congrArg (fun t : ℝ => t ^ 2)
    (norm_pow_liftBlock T X hT hXT J V hcoin k y)

/-- Partial sums are bounded by `‖X‖`. -/
theorem norm_commutantPartial_le (T X : H →L[ℂ] H) (hT : ‖T‖ ≤ 1) (hXT : Commute X T)
    (J : H →ₗᵢ[ℂ] K) (V : K →ₗᵢ[ℂ] K)
    (hcoin : ∀ y : K, J.toContinuousLinearMap.adjoint (V y) =
      T (J.toContinuousLinearMap.adjoint y)) (n : ℕ) (y : K) :
    ‖commutantPartial T X hT hXT J V hcoin n y‖ ≤ ‖X‖ * ‖y‖ := by
  have hsq := norm_sq_commutantPartial T X hT hXT J V hcoin n y
  have hquad := (commutantLiftState T X hT hXT J V hcoin n).quad y
  rw [re_inner_liftGram] at hquad
  have hle : ‖commutantPartial T X hT hXT J V hcoin n y‖ ^ 2 ≤ (‖X‖ * ‖y‖) ^ 2 := by
    rw [hsq, mul_pow]
    linarith
  have habs := sq_le_sq.mp <| by
    simpa [abs_of_nonneg (norm_nonneg _),
      abs_of_nonneg (mul_nonneg (norm_nonneg X) (norm_nonneg y))] using hle
  simpa [abs_of_nonneg (norm_nonneg _),
    abs_of_nonneg (mul_nonneg (norm_nonneg X) (norm_nonneg y))] using habs

/-- Squared norms of the blocks form a summable series. -/
theorem summable_norm_sq_liftBlock (T X : H →L[ℂ] H) (hT : ‖T‖ ≤ 1) (hXT : Commute X T)
    (J : H →ₗᵢ[ℂ] K) (V : K →ₗᵢ[ℂ] K)
    (hcoin : ∀ y : K, J.toContinuousLinearMap.adjoint (V y) =
      T (J.toContinuousLinearMap.adjoint y)) (y : K) :
    Summable fun k => ‖commutantLiftBlock T X hT hXT J V hcoin k y‖ ^ 2 := by
  refine summable_of_sum_range_le (c := ‖X‖ ^ 2 * ‖y‖ ^ 2) (fun k => sq_nonneg _) fun n => ?_
  have hsq := norm_sq_commutantPartial T X hT hXT J V hcoin n y
  have hquad := (commutantLiftState T X hT hXT J V hcoin n).quad y
  rw [re_inner_liftGram] at hquad
  have hnn : 0 ≤ ‖coextensionCompress X J y‖ ^ 2 := sq_nonneg _
  linarith

/-- The partial sums form a Cauchy sequence. -/
theorem cauchySeq_commutantPartial (T X : H →L[ℂ] H) (hT : ‖T‖ ≤ 1) (hXT : Commute X T)
    (J : H →ₗᵢ[ℂ] K) (V : K →ₗᵢ[ℂ] K)
    (hcoin : ∀ y : K, J.toContinuousLinearMap.adjoint (V y) =
      T (J.toContinuousLinearMap.adjoint y)) (y : K) :
    CauchySeq fun n => commutantPartial T X hT hXT J V hcoin n y := by
  let f : ℕ → ℝ := fun k => ‖commutantLiftBlock T X hT hXT J V hcoin k y‖ ^ 2
  have hf : Summable f := summable_norm_sq_liftBlock T X hT hXT J V hcoin y
  have htail : Tendsto (fun i => ∑' k, f (i + k)) atTop (𝓝 0) := by
    simpa [add_comm] using tendsto_sum_nat_add f
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp htail (ε ^ 2) (pow_pos hε 2)
  refine ⟨N, fun m hm n hn => ?_⟩
  rcases le_total m n with hmn | hmn
  · have hsq : ‖commutantPartial T X hT hXT J V hcoin n y -
        commutantPartial T X hT hXT J V hcoin m y‖ ^ 2 =
        ∑ k ∈ Finset.Ico m n, f k := by
      let v : ℕ → K := fun k =>
        (V.toContinuousLinearMap ^ k)
          ((dilationDefectSpace T J V).subtypeL
            (commutantLiftBlock T X hT hXT J V hcoin k y))
      have horth : ∀ i j : ℕ, m ≤ i → i < n → m ≤ j → j < n → i ≠ j →
          ⟪v i, v j⟫_ℂ = 0 := by
        intro i j hi hj hi' hj' hij
        exact inner_defectSpace_pow_eq_zero T J V hcoin hij
          (commutantLiftBlock T X hT hXT J V hcoin i y).property
          (commutantLiftBlock T X hT hXT J V hcoin j y).property
      have hsum := norm_sq_sum_Ico_orthogonal v m n horth
      have hdiff : commutantPartial T X hT hXT J V hcoin n y -
          commutantPartial T X hT hXT J V hcoin m y =
          ∑ k ∈ Finset.Ico m n, v k := by
        have hIco : ∑ k ∈ Finset.range n, v k - ∑ k ∈ Finset.range m, v k =
            ∑ k ∈ Finset.Ico m n, v k := by
          have hsplit := Finset.sum_range_add_sum_Ico (f := v) hmn
          rw [← hsplit, add_sub_cancel_left]
        rw [commutantPartial_apply, commutantPartial_apply, ← sub_sub, add_sub_cancel_left]
        exact hIco
      rw [hdiff, hsum]
      refine Finset.sum_congr rfl fun k _ => ?_
      exact congrArg (fun t : ℝ => t ^ 2)
        (norm_pow_liftBlock T X hT hXT J V hcoin k y)
    have hle : ∑ k ∈ Finset.Ico m n, f k ≤ ∑' k, f (m + k) := by
      rw [Finset.sum_Ico_eq_sum_range]
      exact (hf.comp_injective (add_right_injective m)).sum_le_tsum (Finset.range (n - m))
        fun _ _ => sq_nonneg _
    have htailm : ∑' k, f (m + k) < ε ^ 2 := by
      have hdist := hN m hm
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (tsum_nonneg fun k => sq_nonneg _)] at hdist
      exact hdist
    have hlt : ‖commutantPartial T X hT hXT J V hcoin n y -
        commutantPartial T X hT hXT J V hcoin m y‖ ^ 2 < ε ^ 2 := by
      rw [hsq]
      exact lt_of_le_of_lt hle htailm
    have habs := (sq_lt_sq).mp hlt
    rw [abs_of_nonneg (norm_nonneg _), abs_of_pos hε] at habs
    rw [dist_eq_norm, norm_sub_rev]
    exact habs
  · rw [dist_comm]
    have hsq : ‖commutantPartial T X hT hXT J V hcoin m y -
        commutantPartial T X hT hXT J V hcoin n y‖ ^ 2 =
        ∑ k ∈ Finset.Ico n m, f k := by
      let v : ℕ → K := fun k =>
        (V.toContinuousLinearMap ^ k)
          ((dilationDefectSpace T J V).subtypeL
            (commutantLiftBlock T X hT hXT J V hcoin k y))
      have horth : ∀ i j : ℕ, n ≤ i → i < m → n ≤ j → j < m → i ≠ j →
          ⟪v i, v j⟫_ℂ = 0 := by
        intro i j hi hj hi' hj' hij
        exact inner_defectSpace_pow_eq_zero T J V hcoin hij
          (commutantLiftBlock T X hT hXT J V hcoin i y).property
          (commutantLiftBlock T X hT hXT J V hcoin j y).property
      have hsum := norm_sq_sum_Ico_orthogonal v n m horth
      have hdiff : commutantPartial T X hT hXT J V hcoin m y -
          commutantPartial T X hT hXT J V hcoin n y =
          ∑ k ∈ Finset.Ico n m, v k := by
        have hIco : ∑ k ∈ Finset.range m, v k - ∑ k ∈ Finset.range n, v k =
            ∑ k ∈ Finset.Ico n m, v k := by
          have hsplit := Finset.sum_range_add_sum_Ico (f := v) hmn
          rw [← hsplit, add_sub_cancel_left]
        rw [commutantPartial_apply, commutantPartial_apply, ← sub_sub, add_sub_cancel_left]
        exact hIco
      rw [hdiff, hsum]
      refine Finset.sum_congr rfl fun k _ => ?_
      exact congrArg (fun t : ℝ => t ^ 2)
        (norm_pow_liftBlock T X hT hXT J V hcoin k y)
    have hle : ∑ k ∈ Finset.Ico n m, f k ≤ ∑' k, f (n + k) := by
      rw [Finset.sum_Ico_eq_sum_range]
      exact (hf.comp_injective (add_right_injective n)).sum_le_tsum (Finset.range (m - n))
        fun _ _ => sq_nonneg _
    have htailn : ∑' k, f (n + k) < ε ^ 2 := by
      have hdist := hN n hn
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (tsum_nonneg fun k => sq_nonneg _)] at hdist
      exact hdist
    have hlt : ‖commutantPartial T X hT hXT J V hcoin m y -
        commutantPartial T X hT hXT J V hcoin n y‖ ^ 2 < ε ^ 2 := by
      rw [hsq]
      exact lt_of_le_of_lt hle htailn
    have habs := (sq_lt_sq).mp hlt
    rw [abs_of_nonneg (norm_nonneg _), abs_of_pos hε] at habs
    rw [dist_eq_norm, norm_sub_rev]
    exact habs

/-- Pointwise limit of the lifting series. -/
def commutantLiftAt (T X : H →L[ℂ] H) (hT : ‖T‖ ≤ 1) (hXT : Commute X T)
    (J : H →ₗᵢ[ℂ] K) (V : K →ₗᵢ[ℂ] K)
    (hcoin : ∀ y : K, J.toContinuousLinearMap.adjoint (V y) =
      T (J.toContinuousLinearMap.adjoint y)) (y : K) : K :=
  limUnder atTop fun n => commutantPartial T X hT hXT J V hcoin n y

/-- The partial sums converge to the lifting series. -/
theorem tendsto_commutantPartial (T X : H →L[ℂ] H) (hT : ‖T‖ ≤ 1) (hXT : Commute X T)
    (J : H →ₗᵢ[ℂ] K) (V : K →ₗᵢ[ℂ] K)
    (hcoin : ∀ y : K, J.toContinuousLinearMap.adjoint (V y) =
      T (J.toContinuousLinearMap.adjoint y)) (y : K) :
    Tendsto (fun n => commutantPartial T X hT hXT J V hcoin n y) atTop
      (𝓝 (commutantLiftAt T X hT hXT J V hcoin y)) :=
  (cauchySeq_commutantPartial T X hT hXT J V hcoin y).tendsto_limUnder

/-- The lifting series is additive. -/
theorem commutantLiftAt_add (T X : H →L[ℂ] H) (hT : ‖T‖ ≤ 1) (hXT : Commute X T)
    (J : H →ₗᵢ[ℂ] K) (V : K →ₗᵢ[ℂ] K)
    (hcoin : ∀ y : K, J.toContinuousLinearMap.adjoint (V y) =
      T (J.toContinuousLinearMap.adjoint y)) (y z : K) :
    commutantLiftAt T X hT hXT J V hcoin (y + z) =
      commutantLiftAt T X hT hXT J V hcoin y +
        commutantLiftAt T X hT hXT J V hcoin z := by
  have hpartial : ∀ n, commutantPartial T X hT hXT J V hcoin n (y + z) =
      commutantPartial T X hT hXT J V hcoin n y +
        commutantPartial T X hT hXT J V hcoin n z := by
    intro n
    simp [commutantPartial, map_add, add_apply]
  refine tendsto_nhds_unique (tendsto_commutantPartial T X hT hXT J V hcoin (y + z)) ?_
  simp_rw [hpartial]
  exact (tendsto_commutantPartial T X hT hXT J V hcoin y).add
    (tendsto_commutantPartial T X hT hXT J V hcoin z)

/-- The lifting series commutes with scalar multiplication. -/
theorem commutantLiftAt_smul (T X : H →L[ℂ] H) (hT : ‖T‖ ≤ 1) (hXT : Commute X T)
    (J : H →ₗᵢ[ℂ] K) (V : K →ₗᵢ[ℂ] K)
    (hcoin : ∀ y : K, J.toContinuousLinearMap.adjoint (V y) =
      T (J.toContinuousLinearMap.adjoint y)) (c : ℂ) (y : K) :
    commutantLiftAt T X hT hXT J V hcoin (c • y) =
      c • commutantLiftAt T X hT hXT J V hcoin y := by
  have hpartial : ∀ n, commutantPartial T X hT hXT J V hcoin n (c • y) =
      c • commutantPartial T X hT hXT J V hcoin n y := by
    intro n
    simp [commutantPartial, map_smul]
  refine tendsto_nhds_unique (tendsto_commutantPartial T X hT hXT J V hcoin (c • y)) ?_
  simp_rw [hpartial]
  exact (tendsto_commutantPartial T X hT hXT J V hcoin y).const_smul c

/-- The lifting series is bounded by `‖X‖`. -/
theorem norm_commutantLiftAt_le (T X : H →L[ℂ] H) (hT : ‖T‖ ≤ 1) (hXT : Commute X T)
    (J : H →ₗᵢ[ℂ] K) (V : K →ₗᵢ[ℂ] K)
    (hcoin : ∀ y : K, J.toContinuousLinearMap.adjoint (V y) =
      T (J.toContinuousLinearMap.adjoint y)) (y : K) :
    ‖commutantLiftAt T X hT hXT J V hcoin y‖ ≤ ‖X‖ * ‖y‖ := by
  have hlim : Tendsto (fun n => ‖commutantPartial T X hT hXT J V hcoin n y‖) atTop
      (𝓝 ‖commutantLiftAt T X hT hXT J V hcoin y‖) :=
    (tendsto_commutantPartial T X hT hXT J V hcoin y).norm
  exact le_of_tendsto hlim <| Eventually.of_forall fun n =>
    norm_commutantPartial_le T X hT hXT J V hcoin n y

/-- Linear map underlying the commutant lift. -/
def commutantLiftLinearMap (T X : H →L[ℂ] H) (hT : ‖T‖ ≤ 1) (hXT : Commute X T)
    (J : H →ₗᵢ[ℂ] K) (V : K →ₗᵢ[ℂ] K)
    (hcoin : ∀ y : K, J.toContinuousLinearMap.adjoint (V y) =
      T (J.toContinuousLinearMap.adjoint y)) : K →ₗ[ℂ] K where
  toFun := commutantLiftAt T X hT hXT J V hcoin
  map_add' := commutantLiftAt_add T X hT hXT J V hcoin
  map_smul' := commutantLiftAt_smul T X hT hXT J V hcoin

/-- Continuous commutant lift, with operator norm at most `‖X‖`. -/
def commutantLiftCLM (T X : H →L[ℂ] H) (hT : ‖T‖ ≤ 1) (hXT : Commute X T)
    (J : H →ₗᵢ[ℂ] K) (V : K →ₗᵢ[ℂ] K)
    (hcoin : ∀ y : K, J.toContinuousLinearMap.adjoint (V y) =
      T (J.toContinuousLinearMap.adjoint y)) : K →L[ℂ] K :=
  (commutantLiftLinearMap T X hT hXT J V hcoin).mkContinuous ‖X‖
    (norm_commutantLiftAt_le T X hT hXT J V hcoin)

/-- The continuous lift agrees with the series. -/
theorem commutantLiftCLM_apply (T X : H →L[ℂ] H) (hT : ‖T‖ ≤ 1) (hXT : Commute X T)
    (J : H →ₗᵢ[ℂ] K) (V : K →ₗᵢ[ℂ] K)
    (hcoin : ∀ y : K, J.toContinuousLinearMap.adjoint (V y) =
      T (J.toContinuousLinearMap.adjoint y)) (y : K) :
    commutantLiftCLM T X hT hXT J V hcoin y =
      commutantLiftAt T X hT hXT J V hcoin y :=
  LinearMap.mkContinuous_apply _ _ _ y

/-- The lift has operator norm at most `‖X‖`. -/
theorem norm_commutantLiftCLM_le (T X : H →L[ℂ] H) (hT : ‖T‖ ≤ 1) (hXT : Commute X T)
    (J : H →ₗᵢ[ℂ] K) (V : K →ₗᵢ[ℂ] K)
    (hcoin : ∀ y : K, J.toContinuousLinearMap.adjoint (V y) =
      T (J.toContinuousLinearMap.adjoint y)) :
    ‖commutantLiftCLM T X hT hXT J V hcoin‖ ≤ ‖X‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg X) _

/-- `J*` kills every powered block. -/
theorem adjoint_pow_liftBlock (T X : H →L[ℂ] H) (hT : ‖T‖ ≤ 1) (hXT : Commute X T)
    (J : H →ₗᵢ[ℂ] K) (V : K →ₗᵢ[ℂ] K)
    (hcoin : ∀ y : K, J.toContinuousLinearMap.adjoint (V y) =
      T (J.toContinuousLinearMap.adjoint y)) (k : ℕ) (y : K) :
    J.toContinuousLinearMap.adjoint
        ((V.toContinuousLinearMap ^ k)
          ((dilationDefectSpace T J V).subtypeL
            (commutantLiftBlock T X hT hXT J V hcoin k y))) = 0 := by
  refine ext_inner_right ℂ fun x => ?_
  rw [adjoint_inner_left, inner_zero_left]
  exact inner_eq_zero_symm.mp <|
    inner_embed_defectSpace_pow_eq_zero T J V hcoin k x
      (commutantLiftBlock T X hT hXT J V hcoin k y).property

/-- Each partial sum coextends `X`. -/
theorem adjoint_commutantPartial (T X : H →L[ℂ] H) (hT : ‖T‖ ≤ 1) (hXT : Commute X T)
    (J : H →ₗᵢ[ℂ] K) (V : K →ₗᵢ[ℂ] K)
    (hcoin : ∀ y : K, J.toContinuousLinearMap.adjoint (V y) =
      T (J.toContinuousLinearMap.adjoint y)) (n : ℕ) (y : K) :
    J.toContinuousLinearMap.adjoint (commutantPartial T X hT hXT J V hcoin n y) =
      coextensionCompress X J y := by
  rw [commutantPartial_apply, map_add, map_sum]
  have hJ : J.toContinuousLinearMap.adjoint (J (coextensionCompress X J y)) =
      coextensionCompress X J y :=
    embed_adjoint_leftInverse J _
  have hsum : ∑ k ∈ Finset.range n, J.toContinuousLinearMap.adjoint
      ((V.toContinuousLinearMap ^ k)
        ((dilationDefectSpace T J V).subtypeL
          (commutantLiftBlock T X hT hXT J V hcoin k y))) = 0 := by
    refine Finset.sum_eq_zero fun k _ => ?_
    exact adjoint_pow_liftBlock T X hT hXT J V hcoin k y
  rw [hJ, hsum, add_zero]

/-- The limit coextends `X`. -/
theorem adjoint_commutantLiftAt (T X : H →L[ℂ] H) (hT : ‖T‖ ≤ 1) (hXT : Commute X T)
    (J : H →ₗᵢ[ℂ] K) (V : K →ₗᵢ[ℂ] K)
    (hcoin : ∀ y : K, J.toContinuousLinearMap.adjoint (V y) =
      T (J.toContinuousLinearMap.adjoint y)) (y : K) :
    J.toContinuousLinearMap.adjoint (commutantLiftAt T X hT hXT J V hcoin y) =
      coextensionCompress X J y := by
  have htend : Tendsto
      (fun n => J.toContinuousLinearMap.adjoint
        (commutantPartial T X hT hXT J V hcoin n y)) atTop
      (𝓝 (J.toContinuousLinearMap.adjoint (commutantLiftAt T X hT hXT J V hcoin y))) :=
    (J.toContinuousLinearMap.adjoint.continuous.tendsto _).comp
      (tendsto_commutantPartial T X hT hXT J V hcoin y)
  have hconst : Tendsto
      (fun n => J.toContinuousLinearMap.adjoint
        (commutantPartial T X hT hXT J V hcoin n y)) atTop
      (𝓝 (coextensionCompress X J y)) := by
    simp_rw [adjoint_commutantPartial T X hT hXT J V hcoin]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique htend hconst

/-- Shifting a partial sum by `V` advances the series by one block. -/
theorem commutantPartial_apply_V (T X : H →L[ℂ] H) (hT : ‖T‖ ≤ 1) (hXT : Commute X T)
    (J : H →ₗᵢ[ℂ] K) (V : K →ₗᵢ[ℂ] K)
    (hcoin : ∀ y : K, J.toContinuousLinearMap.adjoint (V y) =
      T (J.toContinuousLinearMap.adjoint y)) (n : ℕ) (y : K) :
    V (commutantPartial T X hT hXT J V hcoin n y) =
      commutantPartial T X hT hXT J V hcoin (n + 1) (V y) := by
  let L : Submodule ℂ K := dilationDefectSpace T J V
  let block : ℕ → K →L[ℂ] L := commutantLiftBlock T X hT hXT J V hcoin
  have hhead : V (J (coextensionCompress X J y)) =
      J (coextensionCompress X J (V y)) + L.subtypeL (block 0 (V y)) := by
    have hzero := congrArg (fun A : K →L[ℂ] K => A y)
      (commutantLiftBlock_zero_comp T X hT hXT J V hcoin)
    have hD : L.subtypeL (block 0 (V y)) =
        dilationDefect T J V (coextensionCompress X J y) := by
      simpa [comp_apply, Submodule.subtypeL_apply] using hzero
    rw [dilationDefect_apply, coextensionCompress_apply_V T X hXT J V hcoin] at hD
    have hsub : V (J (coextensionCompress X J y)) - J (coextensionCompress X J (V y)) =
        L.subtypeL (block 0 (V y)) := hD.symm
    have hsum := (sub_eq_iff_eq_add).mp hsub
    rw [add_comm] at hsum
    exact hsum
  have hrec : ∀ k : ℕ, block (k + 1) (V y) = block k y := by
    intro k
    have hcomp := congrArg (fun A : K →L[ℂ] L => A y)
      (commutantLiftBlock_succ_comp T X hT hXT J V hcoin k)
    simpa [comp_apply] using hcomp
  have hpow : ∀ (k : ℕ) (z : K), V ((V.toContinuousLinearMap ^ k) z) =
      (V.toContinuousLinearMap ^ (k + 1)) z := by
    intro k z
    have hcoe : V.toContinuousLinearMap ((V.toContinuousLinearMap ^ k) z) =
        V ((V.toContinuousLinearMap ^ k) z) := by
      rw [LinearIsometry.coe_toContinuousLinearMap]
    rw [← hcoe, ← clm_pow_succ'_apply]
  rw [commutantPartial_apply, commutantPartial_apply, map_add]
  have hmap : V (∑ k ∈ Finset.range n,
      (V.toContinuousLinearMap ^ k) (L.subtypeL (block k y))) =
      ∑ k ∈ Finset.range n, V ((V.toContinuousLinearMap ^ k)
        (L.subtypeL (block k y))) := by
    simp [map_sum]
  rw [hmap, hhead, add_assoc]
  refine congrArg (fun w => J (coextensionCompress X J (V y)) + w) ?_
  rw [Finset.sum_range_succ', pow_zero, one_apply_eq_self, add_comm]
  refine congrArg (fun w => w + L.subtypeL (block 0 (V y))) ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hrec, hpow]

/-- The limit intertwines `V`. -/
theorem commutantLiftAt_apply_V (T X : H →L[ℂ] H) (hT : ‖T‖ ≤ 1) (hXT : Commute X T)
    (J : H →ₗᵢ[ℂ] K) (V : K →ₗᵢ[ℂ] K)
    (hcoin : ∀ y : K, J.toContinuousLinearMap.adjoint (V y) =
      T (J.toContinuousLinearMap.adjoint y)) (y : K) :
    V (commutantLiftAt T X hT hXT J V hcoin y) =
      commutantLiftAt T X hT hXT J V hcoin (V y) := by
  have hshift : Tendsto (fun n => commutantPartial T X hT hXT J V hcoin (n + 1) (V y))
      atTop (𝓝 (commutantLiftAt T X hT hXT J V hcoin (V y))) :=
    (tendsto_commutantPartial T X hT hXT J V hcoin (V y)).comp (tendsto_add_atTop_nat 1)
  have hV : Tendsto (fun n => V (commutantPartial T X hT hXT J V hcoin n y)) atTop
      (𝓝 (V (commutantLiftAt T X hT hXT J V hcoin y))) :=
    (V.continuous.tendsto _).comp (tendsto_commutantPartial T X hT hXT J V hcoin y)
  have happly : Tendsto (fun n => V (commutantPartial T X hT hXT J V hcoin n y)) atTop
      (𝓝 (commutantLiftAt T X hT hXT J V hcoin (V y))) := by
    simp_rw [commutantPartial_apply_V T X hT hXT J V hcoin]
    exact hshift
  exact tendsto_nhds_unique hV happly

/-- Norm-preserving commutant lift on a co-invariant isometric dilation. -/
theorem commutant_lifting_of (T X : H →L[ℂ] H) (hT : ‖T‖ ≤ 1) (hXT : Commute X T)
    (J : H →ₗᵢ[ℂ] K) (V : K →ₗᵢ[ℂ] K)
    (hcoin : ∀ y : K, J.toContinuousLinearMap.adjoint (V y) =
      T (J.toContinuousLinearMap.adjoint y)) :
    ∃ Y : K →L[ℂ] K, Commute Y V.toContinuousLinearMap ∧ ‖Y‖ = ‖X‖ ∧
      ∀ y : K, J.toContinuousLinearMap.adjoint (Y y) =
        X (J.toContinuousLinearMap.adjoint y) := by
  let Y : K →L[ℂ] K := commutantLiftCLM T X hT hXT J V hcoin
  refine ⟨Y, ?_, ?_, ?_⟩
  · rw [Commute, SemiconjBy, mul_def, mul_def]
    ext y
    simp [Y, commutantLiftCLM_apply, commutantLiftAt_apply_V T X hT hXT J V hcoin,
      LinearIsometry.coe_toContinuousLinearMap]
  · apply le_antisymm
    · exact norm_commutantLiftCLM_le T X hT hXT J V hcoin
    · have hbound : ∀ x : H, ‖X x‖ ≤ ‖Y‖ * ‖x‖ := by
        intro x
        have hcoe : J.toContinuousLinearMap.adjoint (Y (J x)) = X x := by
          rw [show Y (J x) = commutantLiftAt T X hT hXT J V hcoin (J x) from
            commutantLiftCLM_apply T X hT hXT J V hcoin (J x)]
          rw [adjoint_commutantLiftAt T X hT hXT J V hcoin, coextensionCompress,
            comp_apply, embed_adjoint_leftInverse]
        calc
          ‖X x‖ = ‖J.toContinuousLinearMap.adjoint (Y (J x))‖ := by rw [hcoe]
          _ ≤ ‖J.toContinuousLinearMap.adjoint‖ * ‖Y (J x)‖ := le_opNorm _ _
          _ ≤ 1 * (‖Y‖ * ‖J x‖) := by
            gcongr
            · exact norm_embed_adjoint_le J
            · exact le_opNorm Y (J x)
          _ = ‖Y‖ * ‖x‖ := by rw [one_mul, J.norm_map]
      exact opNorm_le_bound X (norm_nonneg Y) hbound
  · intro y
    rw [show Y y = commutantLiftAt T X hT hXT J V hcoin y from
      commutantLiftCLM_apply T X hT hXT J V hcoin y,
      adjoint_commutantLiftAt T X hT hXT J V hcoin, coextensionCompress, comp_apply]

end CKMA
