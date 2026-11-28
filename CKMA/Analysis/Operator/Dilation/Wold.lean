/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Wold decomposition of a Hilbert-space isometry

The wandering subspace is `ker V*`, and the unitary part is the intersection of the forward
ranges. Their orthogonality and the unconditional shift expansion are the content of Wold's
theorem. The argument follows Sz.-Nagy–Foiaş–Bercovici–Kérchy, Chapter I, Section 1.

## Main definitions

* `CKMA.woldWanderingSubspace`: the wandering subspace `ker V*`.
* `CKMA.woldUnitarySubspace`: the unitary subspace `⨅ n, range (Vⁿ)`.
* `CKMA.woldShift`: shifted inclusion of the wandering subspace.
* `CKMA.woldCoefficient`: Fourier coefficient along the `n`-th wandering shift.

## Main results

* `CKMA.woldShift_orthogonalFamily`: shifted copies of the wandering subspace are pairwise
  orthogonal.
* `CKMA.wold_hasSum_decomposition`: orthogonal decomposition into unitary part and wandering shift
  series.
-/

public section

noncomputable section

namespace CKMA

open scoped InnerProductSpace
open ContinuousLinearMap Submodule

universe u

variable {𝕜 : Type*} [RCLike 𝕜]

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- The monoid power of a linear isometry agrees with the power of its continuous linear map. -/
theorem linearIsometry_pow_apply (V : H →ₗᵢ[𝕜] H) (n : ℕ) (x : H) :
    (V ^ n) x = (V.toContinuousLinearMap ^ n) x := by
  rw [LinearIsometry.coe_pow, pow_apply_eq_iterate]
  rfl

/-- Powers of an isometry preserve inner products. -/
private theorem inner_pow_apply_pow_apply (V : H →ₗᵢ[𝕜] H) (n : ℕ) (x y : H) :
    ⟪(V.toContinuousLinearMap ^ n) x, (V.toContinuousLinearMap ^ n) y⟫_𝕜 = ⟪x, y⟫_𝕜 := by
  rw [← linearIsometry_pow_apply, ← linearIsometry_pow_apply]
  exact (V ^ n).inner_map_map x y

/-- An inner product against a residual power reduces by the common initial power. -/
theorem linearIsometry_inner_pow_add_apply_pow_apply (V : H →ₗᵢ[𝕜] H) (m k : ℕ)
    (x y : H) :
    ⟪(V.toContinuousLinearMap ^ (m + k)) x, (V.toContinuousLinearMap ^ m) y⟫_𝕜 =
      ⟪(V.toContinuousLinearMap ^ k) x, y⟫_𝕜 := by
  rw [pow_add, mul_apply_eq_comp]
  exact inner_pow_apply_pow_apply V m _ y

/-- A positive power of an isometry lands in the range of the isometry. -/
private theorem mem_range_of_pos_pow (V : H →ₗᵢ[𝕜] H) {k : ℕ} (hk : 0 < k) (x : H) :
    (V.toContinuousLinearMap ^ k) x ∈ LinearMap.range V.toLinearMap := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hk.ne'
  exact ⟨(V.toContinuousLinearMap ^ j) x, by rw [pow_succ', mul_apply_eq_comp]; rfl⟩

/-- The adjoint of a linear isometry between Hilbert spaces is a left inverse. -/
theorem linearIsometry_adjoint_apply_self {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace 𝕜 K] [CompleteSpace H] [CompleteSpace K] (V : H →ₗᵢ[𝕜] K) (x : H) :
    V.toContinuousLinearMap.adjoint (V x) = x :=
  congrArg (fun T : H →L[𝕜] H => T x) V.adjoint_comp_self

/-- The range of a linear isometry between Hilbert spaces is complete. -/
@[expose]
instance completeSpace_range_linearIsometry {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace 𝕜 K] [CompleteSpace H] [CompleteSpace K] (V : H →ₗᵢ[𝕜] K) :
    CompleteSpace (LinearMap.range V.toLinearMap) := by
  have hclosed : IsClosed (LinearMap.range V.toLinearMap : Set K) := by
    rw [LinearMap.coe_range]
    exact V.antilipschitzWith.isClosed_range V.isometry.uniformContinuous
  exact hclosed.completeSpace_coe

variable [CompleteSpace H]

/-- The wandering subspace `ker V*`. -/
@[expose]
def woldWanderingSubspace (V : H →ₗᵢ[𝕜] H) : Submodule 𝕜 H :=
  LinearMap.ker V.toContinuousLinearMap.adjoint.toLinearMap

/-- Membership in the wandering subspace: `V* x = 0`. -/
theorem mem_woldWanderingSubspace_iff (V : H →ₗᵢ[𝕜] H) {x : H} :
    x ∈ woldWanderingSubspace V ↔ V.toContinuousLinearMap.adjoint x = 0 :=
  LinearMap.mem_ker

/-- The wandering subspace is closed, as the kernel of the adjoint. -/
theorem isClosed_woldWanderingSubspace (V : H →ₗᵢ[𝕜] H) :
    IsClosed (woldWanderingSubspace V : Set H) := by
  simpa [woldWanderingSubspace] using isClosed_ker V.toContinuousLinearMap.adjoint

/-- The wandering subspace is a complete space. -/
@[expose]
instance completeSpace_woldWanderingSubspace (V : H →ₗᵢ[𝕜] H) :
    CompleteSpace (woldWanderingSubspace V) :=
  (isClosed_woldWanderingSubspace V).completeSpace_coe

/-- The wandering subspace is the orthogonal of the range of `V`. -/
private theorem woldWanderingSubspace_eq_orthogonal_range (V : H →ₗᵢ[𝕜] H) :
    woldWanderingSubspace V = (LinearMap.range V.toLinearMap)ᗮ := by
  rw [woldWanderingSubspace]
  simpa using (orthogonal_range V.toContinuousLinearMap).symm

/-- The orthogonal of the wandering subspace is the range of `V`. -/
private theorem orthogonal_woldWanderingSubspace (V : H →ₗᵢ[𝕜] H) :
    (woldWanderingSubspace V)ᗮ = LinearMap.range V.toLinearMap := by
  rw [woldWanderingSubspace_eq_orthogonal_range, orthogonal_orthogonal]

/-- The unitary part is the intersection of all forward ranges. -/
@[expose]
def woldUnitarySubspace (V : H →ₗᵢ[𝕜] H) : Submodule 𝕜 H :=
  ⨅ n : ℕ, LinearMap.range ((V.toContinuousLinearMap ^ n).toLinearMap)

omit [CompleteSpace H] in
/-- Membership in the unitary part is membership in every forward range. -/
theorem mem_woldUnitarySubspace_iff (V : H →ₗᵢ[𝕜] H) {x : H} :
    x ∈ woldUnitarySubspace V ↔
      ∀ n : ℕ, x ∈ LinearMap.range ((V.toContinuousLinearMap ^ n).toLinearMap) := by
  simp [woldUnitarySubspace, mem_iInf]

/-- The inclusion of the wandering subspace, shifted by `Vⁿ`. -/
@[expose]
def woldShift (V : H →ₗᵢ[𝕜] H) (n : ℕ) : woldWanderingSubspace V →ₗᵢ[𝕜] H :=
  (V ^ n).comp (woldWanderingSubspace V).subtypeₗᵢ

/-- Applying `woldShift V n` to a wandering vector applies `Vⁿ`. -/
theorem woldShift_apply (V : H →ₗᵢ[𝕜] H) (n : ℕ) (w : woldWanderingSubspace V) :
    woldShift V n w = (V.toContinuousLinearMap ^ n) (w : H) := by
  rw [woldShift, LinearIsometry.coe_comp, Function.comp_apply, Submodule.coe_subtypeₗᵢ]
  exact linearIsometry_pow_apply V n (w : H)

/-- Distinct forward shifts of the wandering subspace are orthogonal. -/
theorem woldShift_inner_eq_zero (V : H →ₗᵢ[𝕜] H) :
    ∀ m n : ℕ, m ≠ n → ∀ u v : woldWanderingSubspace V,
      ⟪(V.toContinuousLinearMap ^ m) u, (V.toContinuousLinearMap ^ n) v⟫_𝕜 = 0 := by
  intro m n hmn u v
  rcases lt_or_gt_of_ne hmn with hlt | hgt
  · have hadd : m + (n - m) = n := Nat.add_sub_of_le hlt.le
    have hpos : 0 < n - m := Nat.sub_pos_of_lt hlt
    have hreduced :
        ⟪(V.toContinuousLinearMap ^ n) (v : H),
            (V.toContinuousLinearMap ^ m) (u : H)⟫_𝕜 =
          ⟪(V.toContinuousLinearMap ^ (n - m)) (v : H), (u : H)⟫_𝕜 := by
      simpa [hadd] using
        linearIsometry_inner_pow_add_apply_pow_apply V m (n - m) (v : H) (u : H)
    have hy := mem_range_of_pos_pow V hpos (v : H)
    have hu : (u : H) ∈ (LinearMap.range V.toLinearMap)ᗮ := by
      rw [← woldWanderingSubspace_eq_orthogonal_range]
      exact u.2
    have hzero :
        ⟪(V.toContinuousLinearMap ^ n) (v : H),
            (V.toContinuousLinearMap ^ m) (u : H)⟫_𝕜 = 0 := by
      rw [hreduced]
      exact hu _ hy
    exact inner_eq_zero_symm.mp hzero
  · have hadd : n + (m - n) = m := Nat.add_sub_of_le hgt.le
    have hpos : 0 < m - n := Nat.sub_pos_of_lt hgt
    have hreduced :
        ⟪(V.toContinuousLinearMap ^ m) (u : H),
            (V.toContinuousLinearMap ^ n) (v : H)⟫_𝕜 =
          ⟪(V.toContinuousLinearMap ^ (m - n)) (u : H), (v : H)⟫_𝕜 := by
      simpa [hadd] using
        linearIsometry_inner_pow_add_apply_pow_apply V n (m - n) (u : H) (v : H)
    rw [hreduced]
    have hy := mem_range_of_pos_pow V hpos (u : H)
    have hv : (v : H) ∈ (LinearMap.range V.toLinearMap)ᗮ := by
      rw [← woldWanderingSubspace_eq_orthogonal_range]
      exact v.2
    exact hv _ hy

/-- The shifted copies of the wandering subspace form an orthogonal family. -/
theorem woldShift_orthogonalFamily (V : H →ₗᵢ[𝕜] H) :
    OrthogonalFamily 𝕜 (fun _ : ℕ => woldWanderingSubspace V) (woldShift V) := by
  intro m n hmn a b
  simpa [woldShift_apply] using woldShift_inner_eq_zero V m n hmn a b

/-- A vector orthogonal to every wandering shift lies in every forward range. -/
private theorem mem_range_pow_of_orthogonal_woldShift (V : H →ₗᵢ[𝕜] H) {x : H}
    (h : ∀ n : ℕ, ∀ w : woldWanderingSubspace V,
      ⟪(V.toContinuousLinearMap ^ n) (w : H), x⟫_𝕜 = 0) :
    ∀ n : ℕ, x ∈ LinearMap.range ((V.toContinuousLinearMap ^ n).toLinearMap) := by
  intro n
  induction n with
  | zero =>
    rw [pow_zero, one_def]
    exact ⟨x, by simp⟩
  | succ n ih =>
    obtain ⟨y, hy⟩ := ih
    rw [ContinuousLinearMap.coe_coe] at hy
    have hy_orth : y ∈ (woldWanderingSubspace V)ᗮ := by
      intro w hw
      have h0 := h n ⟨w, hw⟩
      have hpreserve := inner_pow_apply_pow_apply V n (w : H) y
      rw [hy] at hpreserve
      rw [← hpreserve]
      exact h0
    rw [orthogonal_woldWanderingSubspace] at hy_orth
    obtain ⟨z, hz⟩ := hy_orth
    rw [LinearIsometry.coe_toLinearMap V] at hz
    refine ⟨z, ?_⟩
    rw [ContinuousLinearMap.coe_coe]
    calc
      (V.toContinuousLinearMap ^ (n + 1)) z
          = (V.toContinuousLinearMap ^ n) (V z) := by
            rw [pow_succ, mul_apply_eq_comp, LinearIsometry.coe_toContinuousLinearMap]
      _ = (V.toContinuousLinearMap ^ n) y := by rw [hz]
      _ = x := hy

/-- Orthogonality to every wandering shift characterizes the unitary part. -/
private theorem mem_woldUnitarySubspace_of_orthogonal_woldShift (V : H →ₗᵢ[𝕜] H) {x : H}
    (h : ∀ n : ℕ, ∀ w : woldWanderingSubspace V,
      ⟪(V.toContinuousLinearMap ^ n) (w : H), x⟫_𝕜 = 0) :
    x ∈ woldUnitarySubspace V := by
  rw [mem_woldUnitarySubspace_iff]
  exact mem_range_pow_of_orthogonal_woldShift V h

omit [CompleteSpace H] in
/-- The unitary part is invariant under the isometry. -/
theorem woldUnitarySubspace_invariant (V : H →ₗᵢ[𝕜] H) :
    ∀ u ∈ woldUnitarySubspace V, V u ∈ woldUnitarySubspace V := by
  intro u hu
  rw [mem_woldUnitarySubspace_iff] at hu ⊢
  intro n
  obtain ⟨y, hy⟩ := hu (n + 1)
  rw [ContinuousLinearMap.coe_coe] at hy
  refine ⟨(V.toContinuousLinearMap ^ 2) y, ?_⟩
  rw [ContinuousLinearMap.coe_coe]
  calc
    (V.toContinuousLinearMap ^ n) ((V.toContinuousLinearMap ^ 2) y)
        = (V.toContinuousLinearMap ^ (n + 2)) y := by
          rw [pow_add, mul_apply_eq_comp]
    _ = V.toContinuousLinearMap ((V.toContinuousLinearMap ^ (n + 1)) y) := by
          rw [pow_succ', mul_apply_eq_comp]
    _ = V u := by
          rw [hy, LinearIsometry.coe_toContinuousLinearMap]

/-- The isometry is surjective on its unitary part, with preimage still unitary. -/
theorem woldUnitarySubspace_preimage (V : H →ₗᵢ[𝕜] H) :
    ∀ u ∈ woldUnitarySubspace V, ∃ v ∈ woldUnitarySubspace V, V v = u := by
  intro u hu
  have hu_range : u ∈ LinearMap.range V.toLinearMap := by
    simpa [pow_one] using (mem_woldUnitarySubspace_iff V).1 hu 1
  obtain ⟨v, hv⟩ := hu_range
  refine ⟨v, ?_, hv⟩
  rw [mem_woldUnitarySubspace_iff]
  intro n
  obtain ⟨y, hy⟩ := (mem_woldUnitarySubspace_iff V).1 hu (n + 1)
  rw [ContinuousLinearMap.coe_coe] at hy
  rw [LinearIsometry.coe_toLinearMap V] at hv
  refine ⟨y, ?_⟩
  rw [ContinuousLinearMap.coe_coe]
  have hleft := linearIsometry_adjoint_apply_self V ((V.toContinuousLinearMap ^ n) y)
  rw [← LinearIsometry.coe_toContinuousLinearMap V] at hleft
  calc
    (V.toContinuousLinearMap ^ n) y
        = V.toContinuousLinearMap.adjoint
            (V.toContinuousLinearMap ((V.toContinuousLinearMap ^ n) y)) := hleft.symm
    _ = V.toContinuousLinearMap.adjoint
          ((V.toContinuousLinearMap ^ (n + 1)) y) := by
        rw [pow_succ', mul_apply_eq_comp]
    _ = V.toContinuousLinearMap.adjoint u := by rw [hy]
    _ = V.toContinuousLinearMap.adjoint (V v) := by rw [← hv]
    _ = v := linearIsometry_adjoint_apply_self V v

/-- The unitary part is orthogonal to every forward shift of the wandering subspace. -/
theorem woldUnitary_inner_shift_eq_zero (V : H →ₗᵢ[𝕜] H) :
    ∀ u ∈ woldUnitarySubspace V, ∀ n : ℕ, ∀ w : woldWanderingSubspace V,
      ⟪u, (V.toContinuousLinearMap ^ n) w⟫_𝕜 = 0 := by
  intro u hu n w
  obtain ⟨y, hy⟩ := (mem_woldUnitarySubspace_iff V).1 hu (n + 1)
  rw [ContinuousLinearMap.coe_coe] at hy
  have hshift :
      ⟪(V.toContinuousLinearMap ^ (n + 1)) y,
          (V.toContinuousLinearMap ^ n) (w : H)⟫_𝕜 = ⟪V y, (w : H)⟫_𝕜 := by
    rw [pow_succ, mul_apply_eq_comp]
    rw [← linearIsometry_pow_apply V n (V.toContinuousLinearMap y)]
    rw [← linearIsometry_pow_apply V n (w : H)]
    rw [(V ^ n).inner_map_map (V.toContinuousLinearMap y) (w : H)]
    rw [LinearIsometry.coe_toContinuousLinearMap]
  rw [← hy, hshift]
  have hw : (w : H) ∈ (LinearMap.range V.toLinearMap)ᗮ := by
    rw [← woldWanderingSubspace_eq_orthogonal_range]
    exact w.2
  exact hw (V y) ⟨y, rfl⟩

/-- The Fourier coefficient of `x` along the `n`-th wandering shift. -/
@[expose]
def woldCoefficient (V : H →ₗᵢ[𝕜] H) (x : H) (n : ℕ) : woldWanderingSubspace V :=
  (woldShift V n).toContinuousLinearMap.adjoint x

/-- `woldCoefficient V x n` is the adjoint of the `n`-th wandering shift applied to `x`. -/
theorem woldCoefficient_def (V : H →ₗᵢ[𝕜] H) (x : H) (n : ℕ) :
    woldCoefficient V x n = (woldShift V n).toContinuousLinearMap.adjoint x :=
  rfl

/-- Inner product against a shifted wandering vector equals the inner product in the wandering
subspace against `woldCoefficient`. -/
theorem inner_woldShift_woldCoefficient (V : H →ₗᵢ[𝕜] H) (x : H) (n : ℕ)
    (w : woldWanderingSubspace V) :
    ⟪woldShift V n w, x⟫_𝕜 = ⟪w, woldCoefficient V x n⟫_𝕜 := by
  simpa [woldCoefficient] using
    ((woldShift V n).toContinuousLinearMap.adjoint_inner_right w x).symm

/-- Partial sums of squared wandering coefficients are bounded by `‖x‖²`. -/
private theorem sum_norm_sq_woldCoefficient_le (V : H →ₗᵢ[𝕜] H) (x : H) (s : Finset ℕ) :
    ∑ n ∈ s, ‖woldCoefficient V x n‖ ^ 2 ≤ ‖x‖ ^ 2 := by
  let c : ℕ → woldWanderingSubspace V := woldCoefficient V x
  set vec : H := ∑ n ∈ s, woldShift V n (c n) with hvec
  have horth := woldShift_orthogonalFamily V
  have hnorm : ‖vec‖ ^ 2 = ∑ n ∈ s, ‖c n‖ ^ 2 := by
    simpa [hvec, c] using horth.norm_sum c s
  have hinner : ⟪vec, vec⟫_𝕜 = ⟪vec, x⟫_𝕜 := by
    have hself : ⟪vec, vec⟫_𝕜 = ∑ n ∈ s, ⟪c n, c n⟫_𝕜 := by
      simpa [hvec, c] using horth.inner_sum c c s
    have hcross : ⟪vec, x⟫_𝕜 = ∑ n ∈ s, ⟪c n, c n⟫_𝕜 := by
      rw [hvec, sum_inner]
      refine Finset.sum_congr rfl fun n _ => ?_
      calc
        ⟪woldShift V n (c n), x⟫_𝕜 = ⟪c n, woldCoefficient V x n⟫_𝕜 :=
          inner_woldShift_woldCoefficient V x n (c n)
        _ = ⟪c n, c n⟫_𝕜 := by simp [c]
    rw [hself, hcross]
  have hsq : ‖vec‖ ^ 2 ≤ ‖vec‖ * ‖x‖ := by
    have hre := inner_self_eq_norm_sq (𝕜 := 𝕜) vec
    rw [← hre, hinner]
    exact re_inner_le_norm vec x
  have hmul : ‖vec‖ * ‖vec‖ ≤ ‖vec‖ * ‖x‖ := by simpa [pow_two] using hsq
  have hle : ‖vec‖ ≤ ‖x‖ := by
    by_cases hzero : ‖vec‖ = 0
    · rw [hzero]
      exact norm_nonneg x
    · exact le_of_mul_le_mul_of_pos_left hmul
        (lt_of_le_of_ne (norm_nonneg vec) (Ne.symm hzero))
  have hsq_le : ‖vec‖ ^ 2 ≤ ‖x‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg vec) hle 2
  simpa [c, hnorm] using hsq_le

/-- The squared wandering coefficients of a vector form a summable series. -/
private theorem summable_norm_sq_woldCoefficient (V : H →ₗᵢ[𝕜] H) (x : H) :
    Summable fun n : ℕ => ‖woldCoefficient V x n‖ ^ 2 :=
  summable_of_sum_le (fun _ => sq_nonneg _) fun s => sum_norm_sq_woldCoefficient_le V x s

/-- Every vector is an orthogonal sum of a unitary vector and a wandering shift series. -/
theorem wold_hasSum_decomposition (V : H →ₗᵢ[𝕜] H) :
    ∀ x : H, ∃ u ∈ woldUnitarySubspace V, ∃ w : ℕ → woldWanderingSubspace V,
      HasSum (fun n ↦ (V.toContinuousLinearMap ^ n) (w n)) (x - u) := by
  intro x
  let c : ℕ → woldWanderingSubspace V := woldCoefficient V x
  have horth := woldShift_orthogonalFamily V
  have hsummable : Summable fun n => woldShift V n (c n) :=
    (horth.summable_iff_norm_sq_summable c).2 <| by
      simpa [c] using summable_norm_sq_woldCoefficient V x
  let s : H := ∑' n, woldShift V n (c n)
  have hs : HasSum (fun n => woldShift V n (c n)) s := hsummable.hasSum
  refine ⟨x - s, ?_, c, ?_⟩
  · apply mem_woldUnitarySubspace_of_orthogonal_woldShift
    intro n w
    have hsum : HasSum (fun m => ⟪woldShift V n w, woldShift V m (c m)⟫_𝕜)
        ⟪woldShift V n w, s⟫_𝕜 := by
      simpa [innerSL_apply_apply] using
        (innerSL 𝕜 (woldShift V n w)).hasSum hs
    have hterm : ∀ m, ⟪woldShift V n w, woldShift V m (c m)⟫_𝕜 =
        if m = n then ⟪woldShift V n w, x⟫_𝕜 else 0 := by
      intro m
      by_cases hmn : m = n
      · rw [ite_eq_left hmn, hmn]
        calc
          ⟪woldShift V n w, woldShift V n (c n)⟫_𝕜 = ⟪w, c n⟫_𝕜 :=
            (woldShift V n).inner_map_map w (c n)
          _ = ⟪w, woldCoefficient V x n⟫_𝕜 := by simp [c]
          _ = ⟪woldShift V n w, x⟫_𝕜 :=
            (inner_woldShift_woldCoefficient V x n w).symm
      · rw [ite_eq_right hmn]
        have hzero := woldShift_inner_eq_zero V n m (Ne.symm hmn) w (c m)
        simpa [woldShift_apply] using hzero
    have hsingle : HasSum (fun m => ⟪woldShift V n w, woldShift V m (c m)⟫_𝕜)
        ⟪woldShift V n w, x⟫_𝕜 := by
      have hfun :
          (fun m => ⟪woldShift V n w, woldShift V m (c m)⟫_𝕜) =
            fun m => if m = n then ⟪woldShift V n w, x⟫_𝕜 else 0 := by
        funext m
        exact hterm m
      rw [hfun]
      exact hasSum_ite_eq n _
    have hs_eq := hsum.unique hsingle
    have hzero : ⟪woldShift V n w, x - s⟫_𝕜 = 0 := by
      rw [inner_sub_right, hs_eq, sub_self]
    simpa [woldShift_apply] using hzero
  · have hshift : HasSum (fun n => (V.toContinuousLinearMap ^ n) (c n)) s := by
      simpa [woldShift_apply] using hs
    simpa [sub_sub_self] using hshift

end CKMA
