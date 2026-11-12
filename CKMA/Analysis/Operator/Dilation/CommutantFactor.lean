/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Contraction factors through a bounded operator

If `‖B x‖ ≤ ‖A x‖` for every vector, then `B` factors as a contraction following `A`. The factor
is built on the closure of the range and extended by the orthogonal projection, which is the form
used for the blocks in the commutant lifting iteration.
-/

@[expose] public section

noncomputable section

namespace CKMA

universe u

variable {E F : Type u}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- A map dominated by `A` factors through `A` by a contraction into a complete subspace. -/
theorem exists_contraction_factor (L : Submodule ℂ F) [CompleteSpace L]
    (A : E →L[ℂ] F) (B : E →L[ℂ] L) (hAB : ∀ x : E, ‖B x‖ ≤ ‖A x‖) :
    ∃ C : F →L[ℂ] L, ‖C‖ ≤ 1 ∧ C.comp A = B := by
  let R : Submodule ℂ F := (LinearMap.range A.toLinearMap).topologicalClosure
  have : CompleteSpace R := Submodule.topologicalClosure.completeSpace _
  have : R.HasOrthogonalProjection :=
    Submodule.HasOrthogonalProjection.ofCompleteSpace (K := R)
  let e : E →ₗ[ℂ] R :=
    LinearMap.codRestrict R A.toLinearMap fun x =>
      Submodule.le_topologicalClosure _ (LinearMap.mem_range_self _ x)
  have hdense : DenseRange e := by
    intro z
    rw [Metric.mem_closure_range_iff]
    intro ε hε
    have hz : (z : F) ∈ closure (LinearMap.range A.toLinearMap : Set F) := by
      rw [← Submodule.topologicalClosure_coe]
      exact z.property
    obtain ⟨y, hy, hdist⟩ := (Metric.mem_closure_iff.mp hz) ε hε
    rw [SetLike.mem_coe, LinearMap.mem_range] at hy
    obtain ⟨x, rfl⟩ := hy
    refine ⟨x, ?_⟩
    have hnear : ‖(z : F) - A x‖ < ε := by
      simpa [dist_eq_norm] using hdist
    rw [dist_eq_norm, ← Submodule.norm_coe (z - e x), Submodule.coe_sub,
      LinearMap.codRestrict_apply]
    exact hnear
  have hle : ∀ x : E, ‖B.toLinearMap x‖ ≤ 1 * ‖e x‖ := by
    intro x
    rw [one_mul]
    have hnorm : ‖e x‖ = ‖A x‖ := by
      rw [← Submodule.norm_coe (e x), LinearMap.codRestrict_apply]
      rfl
    rw [hnorm]
    exact hAB x
  let φ : R →L[ℂ] L := B.toLinearMap.extendOfNorm e
  have hφ : ‖φ‖ ≤ 1 :=
    LinearMap.opNorm_extendOfNorm_le hdense zero_le_one hle
  let C : F →L[ℂ] L := φ.comp R.orthogonalProjectionOnto
  have hproj : ‖R.orthogonalProjectionOnto‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
      rw [one_mul]
      exact R.norm_orthogonalProjectionOnto_apply_le x
  refine ⟨C, ?_, ?_⟩
  · calc
      ‖C‖ ≤ ‖φ‖ * ‖R.orthogonalProjectionOnto‖ :=
        ContinuousLinearMap.opNorm_comp_le φ _
      _ ≤ 1 * 1 :=
        mul_le_mul hφ hproj (norm_nonneg R.orthogonalProjectionOnto) zero_le_one
      _ = 1 := mul_one 1
  · apply ContinuousLinearMap.ext
    intro x
    apply Subtype.ext
    have hmem : A x ∈ R :=
      Submodule.le_topologicalClosure _ (LinearMap.mem_range_self _ x)
    have hprojx : R.orthogonalProjectionOnto (A x) = e x := by
      apply Subtype.ext
      rw [Submodule.coe_orthogonalProjectionOnto_apply,
        (Submodule.starProjection_eq_self_iff (K := R)).mpr hmem,
        LinearMap.codRestrict_apply]
      rfl
    have happly : φ (e x) = B x := by
      have hφx :=
        LinearMap.extendOfNorm_eq (f := B.toLinearMap) (e := e) hdense ⟨1, hle⟩ x
      simpa using hφx
    have hCx : ((C (A x) : L) : F) = (φ (R.orthogonalProjectionOnto (A x)) : F) := by
      simp [C, ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.comp_apply, hCx, hprojx]
    exact congrArg Subtype.val happly

/-- The contraction factor of a dominated map through `A`. -/
def contractionFactor (L : Submodule ℂ F) [CompleteSpace L]
    (A : E →L[ℂ] F) (B : E →L[ℂ] L) (hAB : ∀ x : E, ‖B x‖ ≤ ‖A x‖) : F →L[ℂ] L :=
  Classical.choose (exists_contraction_factor L A B hAB)

/-- The factor through `A` is a contraction. -/
theorem contractionFactor_norm_le (L : Submodule ℂ F) [CompleteSpace L]
    (A : E →L[ℂ] F) (B : E →L[ℂ] L) (hAB : ∀ x : E, ‖B x‖ ≤ ‖A x‖) :
    ‖contractionFactor L A B hAB‖ ≤ 1 :=
  (Classical.choose_spec (exists_contraction_factor L A B hAB)).1

/-- The factor reproduces `B` on the range of `A`. -/
theorem contractionFactor_comp (L : Submodule ℂ F) [CompleteSpace L]
    (A : E →L[ℂ] F) (B : E →L[ℂ] L) (hAB : ∀ x : E, ‖B x‖ ≤ ‖A x‖) :
    (contractionFactor L A B hAB).comp A = B :=
  (Classical.choose_spec (exists_contraction_factor L A B hAB)).2

end CKMA
