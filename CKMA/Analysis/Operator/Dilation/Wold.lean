/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Topology.Algebra.InfiniteSum.Module
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Wold decomposition of a Hilbert-space isometry

The wandering subspace is `ker V*`, and the unitary part is the intersection of the forward
ranges. Their orthogonality and the unconditional shift expansion are the content of Wold's
theorem. The argument follows Sz.-Nagy–Foiaş–Bercovici–Kérchy, Chapter I, Section 1.
-/

@[expose] public section

noncomputable section

namespace CKMA

open scoped InnerProductSpace
open ContinuousLinearMap Submodule

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A power of a continuous endomorphism, evaluated on a vector. -/
theorem clm_pow_succ_apply (A : H →L[ℂ] H) (n : ℕ) (x : H) :
    (A ^ (n + 1)) x = (A ^ n) (A x) := by
  rw [pow_succ]
  exact mul_apply_eq_comp _ _ _

/-- A power of a continuous endomorphism, with the outermost factor on the left. -/
theorem clm_pow_succ'_apply (A : H →L[ℂ] H) (n : ℕ) (x : H) :
    (A ^ (n + 1)) x = A ((A ^ n) x) := by
  rw [pow_succ']
  exact mul_apply_eq_comp _ _ _

/-- Adding exponents corresponds to composing the two powers. -/
theorem clm_pow_add_apply (A : H →L[ℂ] H) (m n : ℕ) (x : H) :
    (A ^ (m + n)) x = (A ^ m) ((A ^ n) x) := by
  rw [pow_add]
  exact mul_apply_eq_comp _ _ _

/-- Applying a continuous-linear power agrees with applying its underlying linear map. -/
theorem toLinearMap_pow_apply (A : H →L[ℂ] H) (n : ℕ) (x : H) :
    (A ^ n).toLinearMap x = (A ^ n) x := by
  induction n generalizing x with
  | zero =>
    rw [pow_zero, one_def, ContinuousLinearMap.coe_id]
    rfl
  | succ n ih =>
    rw [pow_succ', toLinearMap_mul, Module.End.mul_apply, ih, mul_apply_eq_comp,
      ContinuousLinearMap.coe_coe]

/-- The monoid power of a linear isometry agrees with the continuous-linear power. -/
theorem isometry_pow_apply (V : H →ₗᵢ[ℂ] H) (n : ℕ) (x : H) :
    (V ^ n) x = (V.toContinuousLinearMap ^ n) x := by
  induction n with
  | zero =>
    simp [pow_zero, LinearIsometry.one_def, LinearIsometry.id_apply, one_def, id_apply]
  | succ n ih =>
    rw [pow_succ', LinearIsometry.mul_def, LinearIsometry.coe_comp, Function.comp_apply, ih,
      pow_succ']
    rw [← LinearIsometry.coe_toContinuousLinearMap V]
    exact (mul_apply_eq_comp _ _ _).symm

/-- Powers of an isometry preserve inner products. -/
theorem inner_clm_pow (V : H →ₗᵢ[ℂ] H) (n : ℕ) (x y : H) :
    ⟪(V.toContinuousLinearMap ^ n) x, (V.toContinuousLinearMap ^ n) y⟫_ℂ = ⟪x, y⟫_ℂ := by
  rw [← isometry_pow_apply, ← isometry_pow_apply]
  exact (V ^ n).inner_map_map x y

/-- An inner product against a residual power reduces by the common initial power. -/
theorem inner_clm_pow_add_left (V : H →ₗᵢ[ℂ] H) (m k : ℕ) (x y : H) :
    ⟪(V.toContinuousLinearMap ^ (m + k)) x, (V.toContinuousLinearMap ^ m) y⟫_ℂ =
      ⟪(V.toContinuousLinearMap ^ k) x, y⟫_ℂ := by
  rw [clm_pow_add_apply]
  rw [← isometry_pow_apply V m ((V.toContinuousLinearMap ^ k) x)]
  rw [← isometry_pow_apply V m y]
  exact (V ^ m).inner_map_map _ _

/-- A positive power of an isometry lands in the range of the isometry. -/
theorem mem_range_of_pos_pow (V : H →ₗᵢ[ℂ] H) {k : ℕ} (hk : 0 < k) (x : H) :
    (V.toContinuousLinearMap ^ k) x ∈ LinearMap.range V.toLinearMap := by
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  rw [hj]
  exact ⟨(V.toContinuousLinearMap ^ j) x,
    (clm_pow_succ'_apply V.toContinuousLinearMap j x).symm⟩

variable [CompleteSpace H]

/-- The adjoint of an isometry is a left inverse. -/
theorem adjoint_isometry_apply (V : H →ₗᵢ[ℂ] H) (x : H) :
    V.toContinuousLinearMap.adjoint (V x) = x := by
  have h := congrArg (fun T : H →L[ℂ] H => T x) V.adjoint_comp_self
  rw [← LinearIsometry.coe_toContinuousLinearMap V, ← comp_apply, h, one_def, id_apply]

/-- The range of an isometry is a Hilbert space. -/
instance completeSpace_range_linearIsometry (V : H →ₗᵢ[ℂ] H) :
    CompleteSpace (LinearMap.range V.toLinearMap) := by
  have hclosed : IsClosed (LinearMap.range V.toLinearMap : Set H) := by
    rw [LinearMap.coe_range]
    exact V.antilipschitzWith.isClosed_range V.isometry.uniformContinuous
  exact hclosed.completeSpace_coe

/-- The wandering subspace `ker V*`. -/
def woldWanderingSubspace (V : H →ₗᵢ[ℂ] H) : Submodule ℂ H :=
  LinearMap.ker V.toContinuousLinearMap.adjoint.toLinearMap

/-- The wandering subspace is closed, as the kernel of the adjoint. -/
theorem isClosed_woldWanderingSubspace (V : H →ₗᵢ[ℂ] H) :
    IsClosed (woldWanderingSubspace V : Set H) := by
  simpa [woldWanderingSubspace] using isClosed_ker V.toContinuousLinearMap.adjoint

instance completeSpace_woldWanderingSubspace (V : H →ₗᵢ[ℂ] H) :
    CompleteSpace (woldWanderingSubspace V) :=
  (isClosed_woldWanderingSubspace V).completeSpace_coe

/-- The wandering subspace is the orthogonal of the range of `V`. -/
theorem woldWanderingSubspace_eq_orthogonal_range (V : H →ₗᵢ[ℂ] H) :
    woldWanderingSubspace V = (LinearMap.range V.toLinearMap)ᗮ := by
  rw [woldWanderingSubspace]
  simpa using (orthogonal_range V.toContinuousLinearMap).symm

/-- The orthogonal of the wandering subspace is the range of `V`. -/
theorem orthogonal_woldWanderingSubspace (V : H →ₗᵢ[ℂ] H) :
    (woldWanderingSubspace V)ᗮ = LinearMap.range V.toLinearMap := by
  rw [woldWanderingSubspace_eq_orthogonal_range, orthogonal_orthogonal]

/-- The unitary part is the intersection of all forward ranges. -/
def woldUnitarySubspace (V : H →ₗᵢ[ℂ] H) : Submodule ℂ H :=
  ⨅ n : ℕ, LinearMap.range ((V.toContinuousLinearMap ^ n).toLinearMap)

omit [CompleteSpace H] in
/-- Membership in the unitary part is membership in every forward range. -/
theorem mem_woldUnitarySubspace_iff (V : H →ₗᵢ[ℂ] H) {x : H} :
    x ∈ woldUnitarySubspace V ↔
      ∀ n : ℕ, x ∈ LinearMap.range ((V.toContinuousLinearMap ^ n).toLinearMap) := by
  simp [woldUnitarySubspace, mem_iInf]

/-- The inclusion of the wandering subspace, shifted by `Vⁿ`. -/
def woldShift (V : H →ₗᵢ[ℂ] H) (n : ℕ) : woldWanderingSubspace V →ₗᵢ[ℂ] H :=
  (V ^ n).comp (woldWanderingSubspace V).subtypeₗᵢ

theorem woldShift_apply (V : H →ₗᵢ[ℂ] H) (n : ℕ) (w : woldWanderingSubspace V) :
    woldShift V n w = (V.toContinuousLinearMap ^ n) (w : H) := by
  rw [woldShift, LinearIsometry.coe_comp, Function.comp_apply, Submodule.coe_subtypeₗᵢ]
  exact isometry_pow_apply V n (w : H)

/-- Distinct forward shifts of the wandering subspace are orthogonal. -/
theorem woldShift_inner_eq_zero (V : H →ₗᵢ[ℂ] H) :
    ∀ m n : ℕ, m ≠ n → ∀ u v : woldWanderingSubspace V,
      ⟪(V.toContinuousLinearMap ^ m) u, (V.toContinuousLinearMap ^ n) v⟫_ℂ = 0 := by
  intro m n hmn u v
  rcases lt_or_gt_of_ne hmn with hlt | hgt
  · have hadd : m + (n - m) = n := Nat.add_sub_of_le hlt.le
    have hpos : 0 < n - m := Nat.sub_pos_of_lt hlt
    have hreduced :
        ⟪(V.toContinuousLinearMap ^ n) (v : H),
            (V.toContinuousLinearMap ^ m) (u : H)⟫_ℂ =
          ⟪(V.toContinuousLinearMap ^ (n - m)) (v : H), (u : H)⟫_ℂ := by
      simpa [hadd] using
        inner_clm_pow_add_left V m (n - m) (v : H) (u : H)
    have hy := mem_range_of_pos_pow V hpos (v : H)
    have hu : (u : H) ∈ (LinearMap.range V.toLinearMap)ᗮ := by
      rw [← woldWanderingSubspace_eq_orthogonal_range]
      exact u.2
    have hzero :
        ⟪(V.toContinuousLinearMap ^ n) (v : H),
            (V.toContinuousLinearMap ^ m) (u : H)⟫_ℂ = 0 := by
      rw [hreduced]
      exact hu _ hy
    exact inner_eq_zero_symm.mp hzero
  · have hadd : n + (m - n) = m := Nat.add_sub_of_le hgt.le
    have hpos : 0 < m - n := Nat.sub_pos_of_lt hgt
    have hreduced :
        ⟪(V.toContinuousLinearMap ^ m) (u : H),
            (V.toContinuousLinearMap ^ n) (v : H)⟫_ℂ =
          ⟪(V.toContinuousLinearMap ^ (m - n)) (u : H), (v : H)⟫_ℂ := by
      simpa [hadd] using
        inner_clm_pow_add_left V n (m - n) (u : H) (v : H)
    rw [hreduced]
    have hy := mem_range_of_pos_pow V hpos (u : H)
    have hv : (v : H) ∈ (LinearMap.range V.toLinearMap)ᗮ := by
      rw [← woldWanderingSubspace_eq_orthogonal_range]
      exact v.2
    exact hv _ hy

/-- The shifted copies of the wandering subspace form an orthogonal family. -/
theorem woldShift_orthogonalFamily (V : H →ₗᵢ[ℂ] H) :
    OrthogonalFamily ℂ (fun _ : ℕ => woldWanderingSubspace V) (woldShift V) := by
  intro m n hmn a b
  simpa [woldShift_apply] using woldShift_inner_eq_zero V m n hmn a b

/-- A vector orthogonal to every wandering shift lies in every forward range. -/
theorem mem_range_pow_of_orthogonal_woldShift (V : H →ₗᵢ[ℂ] H) {x : H}
    (h : ∀ n : ℕ, ∀ w : woldWanderingSubspace V,
      ⟪(V.toContinuousLinearMap ^ n) (w : H), x⟫_ℂ = 0) :
    ∀ n : ℕ, x ∈ LinearMap.range ((V.toContinuousLinearMap ^ n).toLinearMap) := by
  intro n
  induction n with
  | zero =>
    rw [pow_zero, one_def]
    exact ⟨x, by simp⟩
  | succ n ih =>
    obtain ⟨y, hy⟩ := ih
    rw [toLinearMap_pow_apply] at hy
    have hy_orth : y ∈ (woldWanderingSubspace V)ᗮ := by
      intro w hw
      have h0 := h n ⟨w, hw⟩
      have hpreserve := inner_clm_pow V n (w : H) y
      rw [hy] at hpreserve
      rw [← hpreserve]
      exact h0
    rw [orthogonal_woldWanderingSubspace] at hy_orth
    obtain ⟨z, hz⟩ := hy_orth
    rw [LinearIsometry.coe_toLinearMap V] at hz
    refine ⟨z, ?_⟩
    rw [toLinearMap_pow_apply]
    calc
      (V.toContinuousLinearMap ^ (n + 1)) z
          = (V.toContinuousLinearMap ^ n) (V z) := clm_pow_succ_apply _ n z
      _ = (V.toContinuousLinearMap ^ n) y := by rw [hz]
      _ = x := hy

/-- Orthogonality to every wandering shift characterizes the unitary part. -/
theorem mem_woldUnitarySubspace_of_orthogonal_woldShift (V : H →ₗᵢ[ℂ] H) {x : H}
    (h : ∀ n : ℕ, ∀ w : woldWanderingSubspace V,
      ⟪(V.toContinuousLinearMap ^ n) (w : H), x⟫_ℂ = 0) :
    x ∈ woldUnitarySubspace V := by
  rw [mem_woldUnitarySubspace_iff]
  exact mem_range_pow_of_orthogonal_woldShift V h

omit [CompleteSpace H] in
/-- The unitary part is invariant under the isometry. -/
theorem woldUnitarySubspace_invariant (V : H →ₗᵢ[ℂ] H) :
    ∀ u ∈ woldUnitarySubspace V, V u ∈ woldUnitarySubspace V := by
  intro u hu
  rw [mem_woldUnitarySubspace_iff] at hu ⊢
  intro n
  obtain ⟨y, hy⟩ := hu (n + 1)
  rw [toLinearMap_pow_apply] at hy
  refine ⟨(V.toContinuousLinearMap ^ 2) y, ?_⟩
  rw [toLinearMap_pow_apply]
  calc
    (V.toContinuousLinearMap ^ n) ((V.toContinuousLinearMap ^ 2) y)
        = (V.toContinuousLinearMap ^ (n + 2)) y :=
          (clm_pow_add_apply _ n 2 y).symm
    _ = V.toContinuousLinearMap ((V.toContinuousLinearMap ^ (n + 1)) y) :=
          clm_pow_succ'_apply _ (n + 1) y
    _ = V u := by
          rw [hy, LinearIsometry.coe_toContinuousLinearMap]

/-- The isometry is surjective on its unitary part, with preimage still unitary. -/
theorem woldUnitarySubspace_preimage (V : H →ₗᵢ[ℂ] H) :
    ∀ u ∈ woldUnitarySubspace V, ∃ v ∈ woldUnitarySubspace V, V v = u := by
  intro u hu
  have hu_range : u ∈ LinearMap.range V.toLinearMap := by
    simpa [pow_one] using (mem_woldUnitarySubspace_iff V).1 hu 1
  obtain ⟨v, hv⟩ := hu_range
  refine ⟨v, ?_, hv⟩
  rw [mem_woldUnitarySubspace_iff]
  intro n
  obtain ⟨y, hy⟩ := (mem_woldUnitarySubspace_iff V).1 hu (n + 1)
  rw [toLinearMap_pow_apply] at hy
  rw [LinearIsometry.coe_toLinearMap V] at hv
  refine ⟨y, ?_⟩
  rw [toLinearMap_pow_apply]
  have hleft := adjoint_isometry_apply V ((V.toContinuousLinearMap ^ n) y)
  rw [← LinearIsometry.coe_toContinuousLinearMap V] at hleft
  calc
    (V.toContinuousLinearMap ^ n) y
        = V.toContinuousLinearMap.adjoint
            (V.toContinuousLinearMap ((V.toContinuousLinearMap ^ n) y)) := hleft.symm
    _ = V.toContinuousLinearMap.adjoint
          ((V.toContinuousLinearMap ^ (n + 1)) y) := by
        rw [← clm_pow_succ'_apply]
    _ = V.toContinuousLinearMap.adjoint u := by rw [hy]
    _ = V.toContinuousLinearMap.adjoint (V v) := by rw [← hv]
    _ = v := adjoint_isometry_apply V v

/-- The unitary part is orthogonal to every forward shift of the wandering subspace. -/
theorem woldUnitary_inner_shift_eq_zero (V : H →ₗᵢ[ℂ] H) :
    ∀ u ∈ woldUnitarySubspace V, ∀ n : ℕ, ∀ w : woldWanderingSubspace V,
      ⟪u, (V.toContinuousLinearMap ^ n) w⟫_ℂ = 0 := by
  intro u hu n w
  obtain ⟨y, hy⟩ := (mem_woldUnitarySubspace_iff V).1 hu (n + 1)
  rw [toLinearMap_pow_apply] at hy
  have hshift :
      ⟪(V.toContinuousLinearMap ^ (n + 1)) y,
          (V.toContinuousLinearMap ^ n) (w : H)⟫_ℂ = ⟪V y, (w : H)⟫_ℂ := by
    rw [clm_pow_succ_apply V.toContinuousLinearMap n y]
    rw [← isometry_pow_apply V n (V.toContinuousLinearMap y)]
    rw [← isometry_pow_apply V n (w : H)]
    rw [(V ^ n).inner_map_map (V.toContinuousLinearMap y) (w : H)]
    rw [LinearIsometry.coe_toContinuousLinearMap]
  rw [← hy, hshift]
  have hw : (w : H) ∈ (LinearMap.range V.toLinearMap)ᗮ := by
    rw [← woldWanderingSubspace_eq_orthogonal_range]
    exact w.2
  exact hw (V y) ⟨y, rfl⟩

/-- The Fourier coefficient of `x` along the `n`-th wandering shift. -/
def woldCoefficient (V : H →ₗᵢ[ℂ] H) (x : H) (n : ℕ) : woldWanderingSubspace V :=
  (woldShift V n).toContinuousLinearMap.adjoint x

theorem inner_woldShift_woldCoefficient (V : H →ₗᵢ[ℂ] H) (x : H) (n : ℕ)
    (w : woldWanderingSubspace V) :
    ⟪woldShift V n w, x⟫_ℂ = ⟪w, woldCoefficient V x n⟫_ℂ := by
  simpa [woldCoefficient] using
    ((woldShift V n).toContinuousLinearMap.adjoint_inner_right w x).symm

/-- Partial sums of squared wandering coefficients are bounded by `‖x‖²`. -/
theorem sum_norm_sq_woldCoefficient_le (V : H →ₗᵢ[ℂ] H) (x : H) (s : Finset ℕ) :
    ∑ n ∈ s, ‖woldCoefficient V x n‖ ^ 2 ≤ ‖x‖ ^ 2 := by
  let c : ℕ → woldWanderingSubspace V := woldCoefficient V x
  set vec : H := ∑ n ∈ s, woldShift V n (c n) with hvec
  have horth := woldShift_orthogonalFamily V
  have hnorm : ‖vec‖ ^ 2 = ∑ n ∈ s, ‖c n‖ ^ 2 := by
    simpa [hvec, c] using horth.norm_sum c s
  have hinner : ⟪vec, vec⟫_ℂ = ⟪vec, x⟫_ℂ := by
    have hself : ⟪vec, vec⟫_ℂ = ∑ n ∈ s, ⟪c n, c n⟫_ℂ := by
      simpa [hvec, c] using horth.inner_sum c c s
    have hcross : ⟪vec, x⟫_ℂ = ∑ n ∈ s, ⟪c n, c n⟫_ℂ := by
      rw [hvec, sum_inner]
      refine Finset.sum_congr rfl fun n _ => ?_
      calc
        ⟪woldShift V n (c n), x⟫_ℂ = ⟪c n, woldCoefficient V x n⟫_ℂ :=
          inner_woldShift_woldCoefficient V x n (c n)
        _ = ⟪c n, c n⟫_ℂ := by simp [c]
    rw [hself, hcross]
  have hsq : ‖vec‖ ^ 2 ≤ ‖vec‖ * ‖x‖ := by
    have hre := inner_self_eq_norm_sq (𝕜 := ℂ) vec
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
theorem summable_norm_sq_woldCoefficient (V : H →ₗᵢ[ℂ] H) (x : H) :
    Summable fun n : ℕ => ‖woldCoefficient V x n‖ ^ 2 :=
  summable_of_sum_le (fun _ => sq_nonneg _) fun s => sum_norm_sq_woldCoefficient_le V x s

/-- Every vector is an orthogonal sum of a unitary vector and a wandering shift series. -/
theorem wold_hasSum_decomposition (V : H →ₗᵢ[ℂ] H) :
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
    have hsum : HasSum (fun m => ⟪woldShift V n w, woldShift V m (c m)⟫_ℂ)
        ⟪woldShift V n w, s⟫_ℂ := by
      simpa [innerSL_apply_apply] using
        (innerSL ℂ (woldShift V n w)).hasSum hs
    have hterm : ∀ m, ⟪woldShift V n w, woldShift V m (c m)⟫_ℂ =
        if m = n then ⟪woldShift V n w, x⟫_ℂ else 0 := by
      intro m
      by_cases hmn : m = n
      · rw [ite_eq_left hmn, hmn]
        calc
          ⟪woldShift V n w, woldShift V n (c n)⟫_ℂ = ⟪w, c n⟫_ℂ :=
            (woldShift V n).inner_map_map w (c n)
          _ = ⟪w, woldCoefficient V x n⟫_ℂ := by simp [c]
          _ = ⟪woldShift V n w, x⟫_ℂ :=
            (inner_woldShift_woldCoefficient V x n w).symm
      · rw [ite_eq_right hmn]
        have hzero := woldShift_inner_eq_zero V n m (Ne.symm hmn) w (c m)
        simpa [woldShift_apply] using hzero
    have hsingle : HasSum (fun m => ⟪woldShift V n w, woldShift V m (c m)⟫_ℂ)
        ⟪woldShift V n w, x⟫_ℂ := by
      have hfun :
          (fun m => ⟪woldShift V n w, woldShift V m (c m)⟫_ℂ) =
            fun m => if m = n then ⟪woldShift V n w, x⟫_ℂ else 0 := by
        funext m
        exact hterm m
      rw [hfun]
      exact hasSum_ite_eq n _
    have hs_eq := hsum.unique hsingle
    have hzero : ⟪woldShift V n w, x - s⟫_ℂ = 0 := by
      rw [inner_sub_right, hs_eq, sub_self]
    simpa [woldShift_apply] using hzero
  · have hshift : HasSum (fun n => (V.toContinuousLinearMap ^ n) (c n)) s := by
      simpa [woldShift_apply] using hs
    simpa [sub_sub_self] using hshift

end CKMA
