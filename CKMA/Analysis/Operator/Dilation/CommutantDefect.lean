/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.Operator.Dilation.Wold
public import Mathlib.Analysis.InnerProductSpace.Orthogonal

/-!
# Defect of an isometric coextension

For a co-invariant isometric embedding `J` of a contraction, the defect
`D x = V (J x) - J (T x)` lands in the orthogonal of the embedded copy of `H`.
Its forward orbit under `V` is pairwise orthogonal, and the identity extends from the
algebraic range of `D` to the closure. That closure is the multiplicity space of the
commutant-lifting series.
-/

@[expose] public section

noncomputable section

namespace CKMA

open scoped InnerProductSpace
open ContinuousLinearMap Submodule

universe u

variable {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The adjoint of an isometric embedding is a left inverse. -/
theorem embed_adjoint_leftInverse (J : H →ₗᵢ[ℂ] K) (x : H) :
    J.toContinuousLinearMap.adjoint (J x) = x := by
  have hs := congrArg (fun A : H →L[ℂ] H => A x) J.adjoint_comp_self
  rw [comp_apply, one_apply_eq_self] at hs
  exact hs

/-- Co-invariance passes to the adjoint as `V* J = J T*`. -/
theorem adjoint_coinvariant (T : H →L[ℂ] H) (J : H →ₗᵢ[ℂ] K) (V : K →ₗᵢ[ℂ] K)
    (hcoin : ∀ y : K, J.toContinuousLinearMap.adjoint (V y) =
      T (J.toContinuousLinearMap.adjoint y)) :
    V.toContinuousLinearMap.adjoint.comp J.toContinuousLinearMap =
      J.toContinuousLinearMap.comp T.adjoint := by
  have hpt : J.toContinuousLinearMap.adjoint.comp V.toContinuousLinearMap =
      T.comp J.toContinuousLinearMap.adjoint := by
    ext y
    simp [hcoin, comp_apply, LinearIsometry.coe_toContinuousLinearMap]
  have hadj := congrArg ContinuousLinearMap.adjoint hpt
  simpa [adjoint_comp, adjoint_adjoint] using hadj

/-- The defect `V J - J T` of an isometric coextension. -/
def dilationDefect (T : H →L[ℂ] H) (J : H →ₗᵢ[ℂ] K) (V : K →ₗᵢ[ℂ] K) : H →L[ℂ] K :=
  V.toContinuousLinearMap.comp J.toContinuousLinearMap -
    J.toContinuousLinearMap.comp T

omit [CompleteSpace H] [CompleteSpace K] in
/-- Evaluation of the coextension defect. -/
theorem dilationDefect_apply (T : H →L[ℂ] H) (J : H →ₗᵢ[ℂ] K) (V : K →ₗᵢ[ℂ] K) (x : H) :
    dilationDefect T J V x = V (J x) - J (T x) := by
  simp [dilationDefect, sub_apply, comp_apply, LinearIsometry.coe_toContinuousLinearMap]

/-- The embedded copy of `H` is orthogonal to the coextension defect. -/
theorem dilationDefect_adjoint_apply (T : H →L[ℂ] H) (J : H →ₗᵢ[ℂ] K) (V : K →ₗᵢ[ℂ] K)
    (hcoin : ∀ y : K, J.toContinuousLinearMap.adjoint (V y) =
      T (J.toContinuousLinearMap.adjoint y)) (x : H) :
    J.toContinuousLinearMap.adjoint (dilationDefect T J V x) = 0 := by
  rw [dilationDefect_apply, map_sub, hcoin, embed_adjoint_leftInverse,
    embed_adjoint_leftInverse, sub_self]

/-- The coextension defect takes values in the orthogonal of the embedded copy. -/
theorem dilationDefect_mem_orthogonal (T : H →L[ℂ] H) (J : H →ₗᵢ[ℂ] K) (V : K →ₗᵢ[ℂ] K)
    (hcoin : ∀ y : K, J.toContinuousLinearMap.adjoint (V y) =
      T (J.toContinuousLinearMap.adjoint y)) (x : H) :
    dilationDefect T J V x ∈ (LinearMap.range J.toLinearMap)ᗮ := by
  rw [mem_orthogonal]
  intro u hu
  obtain ⟨z, rfl⟩ := hu
  have hinner := adjoint_inner_right J.toContinuousLinearMap z (dilationDefect T J V x)
  rw [dilationDefect_adjoint_apply T J V hcoin x] at hinner
  simpa using hinner.symm

/-- Applying `V*` to the defect returns the embedded action of `1 - T* T`. -/
theorem adjoint_dilationDefect (T : H →L[ℂ] H) (J : H →ₗᵢ[ℂ] K) (V : K →ₗᵢ[ℂ] K)
    (hcoin : ∀ y : K, J.toContinuousLinearMap.adjoint (V y) =
      T (J.toContinuousLinearMap.adjoint y)) (y : H) :
    V.toContinuousLinearMap.adjoint (dilationDefect T J V y) =
      J ((1 - T.adjoint.comp T) y) := by
  rw [dilationDefect_apply, map_sub, adjoint_isometry_apply]
  have hJ : V.toContinuousLinearMap.adjoint (J (T y)) = J (T.adjoint (T y)) := by
    have happly := congrArg (fun A : H →L[ℂ] K => A (T y))
      (adjoint_coinvariant T J V hcoin)
    simpa [comp_apply, LinearIsometry.coe_toContinuousLinearMap] using happly
  rw [hJ]
  have hsub : J y - J (T.adjoint (T y)) = J (y - T.adjoint (T y)) := (map_sub J _ _).symm
  rw [hsub]
  congr 1

/-- Every forward image of the defect stays orthogonal to the embedded copy. -/
theorem dilationDefect_pow_mem_orthogonal (T : H →L[ℂ] H) (J : H →ₗᵢ[ℂ] K) (V : K →ₗᵢ[ℂ] K)
    (hcoin : ∀ y : K, J.toContinuousLinearMap.adjoint (V y) =
      T (J.toContinuousLinearMap.adjoint y)) (n : ℕ) (x : H) :
    (V.toContinuousLinearMap ^ n) (dilationDefect T J V x) ∈
      (LinearMap.range J.toLinearMap)ᗮ := by
  induction n with
  | zero =>
    simpa [pow_zero, one_apply_eq_self] using dilationDefect_mem_orthogonal T J V hcoin x
  | succ n ih =>
    rw [mem_orthogonal]
    intro u hu
    obtain ⟨z, rfl⟩ := hu
    rw [clm_pow_succ'_apply]
    simp only [LinearIsometry.coe_toLinearMap]
    rw [← adjoint_inner_left V.toContinuousLinearMap
      ((V.toContinuousLinearMap ^ n) (dilationDefect T J V x)) (J z)]
    have happly := congrArg (fun A : H →L[ℂ] K => A z) (adjoint_coinvariant T J V hcoin)
    rw [comp_apply, comp_apply, LinearIsometry.coe_toContinuousLinearMap] at happly
    rw [happly]
    exact inner_right_of_mem_orthogonal
      (LinearMap.mem_range_self J.toLinearMap (T.adjoint z)) ih

/-- Squared norm of the coextension defect. -/
theorem norm_sq_dilationDefect (T : H →L[ℂ] H) (J : H →ₗᵢ[ℂ] K) (V : K →ₗᵢ[ℂ] K)
    (hcoin : ∀ y : K, J.toContinuousLinearMap.adjoint (V y) =
      T (J.toContinuousLinearMap.adjoint y)) (x : H) :
    ‖dilationDefect T J V x‖ ^ 2 = ‖x‖ ^ 2 - ‖T x‖ ^ 2 := by
  rw [dilationDefect_apply]
  rw [norm_sub_sq (𝕜 := ℂ)]
  have hV : ‖V (J x)‖ = ‖x‖ := by rw [V.norm_map, J.norm_map]
  have hJ : ‖J (T x)‖ = ‖T x‖ := J.norm_map _
  have hinner : RCLike.re ⟪V (J x), J (T x)⟫_ℂ = ‖T x‖ ^ 2 := by
    have hadj : V.toContinuousLinearMap.adjoint (J (T x)) = J (T.adjoint (T x)) := by
      have happly := congrArg (fun A : H →L[ℂ] K => A (T x))
        (adjoint_coinvariant T J V hcoin)
      simpa [comp_apply, LinearIsometry.coe_toContinuousLinearMap] using happly
    have heq : ⟪V (J x), J (T x)⟫_ℂ = ⟪T x, T x⟫_ℂ := by
      have hcoe : V.toContinuousLinearMap (J x) = V (J x) := by
        rw [LinearIsometry.coe_toContinuousLinearMap]
      rw [← hcoe, ← adjoint_inner_right V.toContinuousLinearMap (J x) (J (T x)), hadj,
        J.inner_map_map, adjoint_inner_right]
    rw [heq, inner_self_eq_norm_sq]
  rw [hV, hJ, hinner]
  ring

/-- Distinct forward images of defect vectors are orthogonal. -/
theorem inner_dilationDefect_pow_eq_zero (T : H →L[ℂ] H) (J : H →ₗᵢ[ℂ] K) (V : K →ₗᵢ[ℂ] K)
    (hcoin : ∀ y : K, J.toContinuousLinearMap.adjoint (V y) =
      T (J.toContinuousLinearMap.adjoint y)) {m n : ℕ} (hmn : m < n) (x y : H) :
    ⟪(V.toContinuousLinearMap ^ m) (dilationDefect T J V x),
      (V.toContinuousLinearMap ^ n) (dilationDefect T J V y)⟫_ℂ = 0 := by
  have hle : m ≤ n := le_of_lt hmn
  have hk : 0 < n - m := Nat.sub_pos_of_lt hmn
  rw [inner_eq_zero_symm]
  have hadd : n = m + (n - m) := (Nat.add_sub_of_le hle).symm
  rw [hadd, inner_clm_pow_add_left]
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  rw [hj, clm_pow_succ'_apply]
  rw [← adjoint_inner_right V.toContinuousLinearMap
    ((V.toContinuousLinearMap ^ j) (dilationDefect T J V y)) (dilationDefect T J V x)]
  rw [adjoint_dilationDefect T J V hcoin]
  exact inner_left_of_mem_orthogonal
    (LinearMap.mem_range_self J.toLinearMap ((1 - T.adjoint.comp T) x))
    (dilationDefect_pow_mem_orthogonal T J V hcoin j y)

/-- The closed span of the coextension defect. -/
def dilationDefectSpace (T : H →L[ℂ] H) (J : H →ₗᵢ[ℂ] K) (V : K →ₗᵢ[ℂ] K) : Submodule ℂ K :=
  (LinearMap.range (dilationDefect T J V).toLinearMap).topologicalClosure

omit [CompleteSpace H] [CompleteSpace K] in
/-- Each defect vector lies in the closed defect space. -/
theorem dilationDefect_mem_space (T : H →L[ℂ] H) (J : H →ₗᵢ[ℂ] K) (V : K →ₗᵢ[ℂ] K) (x : H) :
    dilationDefect T J V x ∈ dilationDefectSpace T J V :=
  le_topologicalClosure _ (LinearMap.mem_range_self _ x)

omit [CompleteSpace H] [CompleteSpace K] in
/-- A vector of the closed defect space lies in the closure of the algebraic range. -/
theorem mem_closure_of_mem_dilationDefectSpace (T : H →L[ℂ] H) (J : H →ₗᵢ[ℂ] K)
    (V : K →ₗᵢ[ℂ] K) {w : K} (hw : w ∈ dilationDefectSpace T J V) :
    w ∈ closure (LinearMap.range (dilationDefect T J V).toLinearMap : Set K) := by
  rw [dilationDefectSpace] at hw
  rw [← SetLike.mem_coe] at hw
  rwa [topologicalClosure_coe] at hw

/-- Forward images of the closed defect space stay orthogonal to the embedded copy. -/
theorem dilationDefectSpace_pow_mem_orthogonal (T : H →L[ℂ] H) (J : H →ₗᵢ[ℂ] K)
    (V : K →ₗᵢ[ℂ] K)
    (hcoin : ∀ y : K, J.toContinuousLinearMap.adjoint (V y) =
      T (J.toContinuousLinearMap.adjoint y)) (n : ℕ) {w : K}
    (hw : w ∈ dilationDefectSpace T J V) :
    (V.toContinuousLinearMap ^ n) w ∈ (LinearMap.range J.toLinearMap)ᗮ := by
  have hsub : (LinearMap.range (dilationDefect T J V).toLinearMap : Set K) ⊆
      {u : K | (V.toContinuousLinearMap ^ n) u ∈ (LinearMap.range J.toLinearMap)ᗮ} := by
    intro u hu
    obtain ⟨x, rfl⟩ := hu
    exact dilationDefect_pow_mem_orthogonal T J V hcoin n x
  have hcl : IsClosed
      {u : K | (V.toContinuousLinearMap ^ n) u ∈ (LinearMap.range J.toLinearMap)ᗮ} := by
    exact (isClosed_orthogonal (K := LinearMap.range J.toLinearMap)).preimage
      (V.toContinuousLinearMap ^ n).continuous
  exact closure_minimal hsub hcl (mem_closure_of_mem_dilationDefectSpace T J V hw)

/-- The embedded copy is orthogonal to every forward image of the closed defect space. -/
theorem inner_embed_defectSpace_pow_eq_zero (T : H →L[ℂ] H) (J : H →ₗᵢ[ℂ] K) (V : K →ₗᵢ[ℂ] K)
    (hcoin : ∀ y : K, J.toContinuousLinearMap.adjoint (V y) =
      T (J.toContinuousLinearMap.adjoint y)) (n : ℕ) (x : H) {w : K}
    (hw : w ∈ dilationDefectSpace T J V) :
    ⟪J x, (V.toContinuousLinearMap ^ n) w⟫_ℂ = 0 :=
  inner_right_of_mem_orthogonal (LinearMap.mem_range_self J.toLinearMap x)
    (dilationDefectSpace_pow_mem_orthogonal T J V hcoin n hw)

/-- Forward images of the closed defect space with a smaller index are orthogonal. -/
theorem inner_defectSpace_pow_lt_eq_zero (T : H →L[ℂ] H) (J : H →ₗᵢ[ℂ] K) (V : K →ₗᵢ[ℂ] K)
    (hcoin : ∀ y : K, J.toContinuousLinearMap.adjoint (V y) =
      T (J.toContinuousLinearMap.adjoint y)) {m n : ℕ} (hmn : m < n) {w₁ w₂ : K}
    (hw₁ : w₁ ∈ dilationDefectSpace T J V) (hw₂ : w₂ ∈ dilationDefectSpace T J V) :
    ⟪(V.toContinuousLinearMap ^ m) w₁, (V.toContinuousLinearMap ^ n) w₂⟫_ℂ = 0 := by
  have hstep : ∀ x : H, ⟪(V.toContinuousLinearMap ^ m) w₁,
        (V.toContinuousLinearMap ^ n) (dilationDefect T J V x)⟫_ℂ = 0 := by
      intro x
      have hzero : ∀ z : H, ⟪(V.toContinuousLinearMap ^ m) (dilationDefect T J V z),
          (V.toContinuousLinearMap ^ n) (dilationDefect T J V x)⟫_ℂ = 0 :=
        fun z => inner_dilationDefect_pow_eq_zero T J V hcoin hmn z x
      have hsub : (LinearMap.range (dilationDefect T J V).toLinearMap : Set K) ⊆
          {u | ⟪(V.toContinuousLinearMap ^ m) u,
            (V.toContinuousLinearMap ^ n) (dilationDefect T J V x)⟫_ℂ = 0} := by
        intro u hu
        obtain ⟨z, rfl⟩ := hu
        exact hzero z
      have hcont : Continuous fun u : K => ⟪(V.toContinuousLinearMap ^ m) u,
          (V.toContinuousLinearMap ^ n) (dilationDefect T J V x)⟫_ℂ :=
        Continuous.inner (V.toContinuousLinearMap ^ m).continuous continuous_const
      have hcl : IsClosed {u | ⟪(V.toContinuousLinearMap ^ m) u,
          (V.toContinuousLinearMap ^ n) (dilationDefect T J V x)⟫_ℂ = 0} :=
        isClosed_eq hcont continuous_const
      simpa [Set.mem_ofPred_eq] using closure_minimal hsub hcl
        (mem_closure_of_mem_dilationDefectSpace T J V hw₁)
  have hsub : (LinearMap.range (dilationDefect T J V).toLinearMap : Set K) ⊆
      {u | ⟪(V.toContinuousLinearMap ^ m) w₁, (V.toContinuousLinearMap ^ n) u⟫_ℂ = 0} := by
    intro u hu
    obtain ⟨x, rfl⟩ := hu
    exact hstep x
  have hcont : Continuous fun u : K =>
      ⟪(V.toContinuousLinearMap ^ m) w₁, (V.toContinuousLinearMap ^ n) u⟫_ℂ :=
    Continuous.inner continuous_const (V.toContinuousLinearMap ^ n).continuous
  have hcl : IsClosed {u | ⟪(V.toContinuousLinearMap ^ m) w₁,
      (V.toContinuousLinearMap ^ n) u⟫_ℂ = 0} :=
    isClosed_eq hcont continuous_const
  simpa [Set.mem_ofPred_eq] using closure_minimal hsub hcl
    (mem_closure_of_mem_dilationDefectSpace T J V hw₂)

/-- Distinct forward images of the closed defect space are orthogonal. -/
theorem inner_defectSpace_pow_eq_zero (T : H →L[ℂ] H) (J : H →ₗᵢ[ℂ] K) (V : K →ₗᵢ[ℂ] K)
    (hcoin : ∀ y : K, J.toContinuousLinearMap.adjoint (V y) =
      T (J.toContinuousLinearMap.adjoint y)) {m n : ℕ} (hmn : m ≠ n) {w₁ w₂ : K}
    (hw₁ : w₁ ∈ dilationDefectSpace T J V) (hw₂ : w₂ ∈ dilationDefectSpace T J V) :
    ⟪(V.toContinuousLinearMap ^ m) w₁, (V.toContinuousLinearMap ^ n) w₂⟫_ℂ = 0 := by
  rcases lt_or_gt_of_ne hmn with hlt | hlt
  · exact inner_defectSpace_pow_lt_eq_zero T J V hcoin hlt hw₁ hw₂
  · rw [inner_eq_zero_symm]
    exact inner_defectSpace_pow_lt_eq_zero T J V hcoin hlt hw₂ hw₁

omit [CompleteSpace K] in
/-- Squared norm of an orthogonal sum over an integer interval. -/
theorem norm_sq_sum_Ico_orthogonal (v : ℕ → K) (m n : ℕ)
    (horth : ∀ i j : ℕ, m ≤ i → i < n → m ≤ j → j < n → i ≠ j → ⟪v i, v j⟫_ℂ = 0) :
    ‖∑ i ∈ Finset.Ico m n, v i‖ ^ 2 = ∑ i ∈ Finset.Ico m n, ‖v i‖ ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    by_cases hmn : m ≤ n
    · rw [Finset.sum_Ico_succ_top hmn, Finset.sum_Ico_succ_top hmn]
      have hcross : ⟪∑ i ∈ Finset.Ico m n, v i, v n⟫_ℂ = 0 := by
        rw [sum_inner]
        refine Finset.sum_eq_zero fun i hi => ?_
        have hi' := Finset.mem_Ico.mp hi
        exact horth i n hi'.1 (Nat.lt_succ_of_lt hi'.2) hmn (Nat.lt_succ_self n)
          (ne_of_lt hi'.2)
      have hpy := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hcross
      rw [← pow_two, ← pow_two, ← pow_two] at hpy
      rw [hpy, ih fun i j hi1 hi2 hj1 hj2 hne =>
        horth i j hi1 (Nat.lt_succ_of_lt hi2) hj1 (Nat.lt_succ_of_lt hj2) hne]
    · have hempty : n + 1 ≤ m := by omega
      simp [Finset.Ico_eq_empty_of_le hempty]

end CKMA
