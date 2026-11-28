/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Frobenius

import TauCeti.Analysis.InnerProductSpace.CourantFischer
import TauCeti.Analysis.InnerProductSpace.FanDominance
import Mathlib.Analysis.Convex.Birkhoff
import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.EckartYoung

/-!
# Hermitian eigenvalues, singular values, and low-rank approximation

Sorted Hermitian eigenvalues are Mathlib's `LinearMap.IsSymmetric.eigenvalues`, indexed from
zero in decreasing order. Compression and rank perturbation statements use the corresponding index
shifts; Weyl's additive bound holds for every output index `k ≥ i + j`. Hoffman–Wielandt is
formulated in supplied orthonormal eigenbases, allowing repeated eigenvalues. The eigenvalue
matching is the one picked out of the doubly stochastic matrix of squared eigenbasis overlaps by
Birkhoff's theorem.

Frobenius energy is TauCeti's `TauCeti.UnitarilyInvariantSeminorm.frobenius`, and SVD truncation
uses TauCeti's canonical singular-value data. The low-rank statements include all unitarily
invariant seminorms, the Frobenius tail, and the operator-norm tail, with zero-padding beyond the
available rank. Cauchy interlacing and Weyl's inequality are derived from TauCeti's
Courant–Fischer API (`TauCeti/Analysis/InnerProductSpace/CourantFischer.lean`). Sources: GAPS 13.7,
13.8, 13.10, 13.13, and 13.18.

## Main definitions

* `CKMA.hermitianCompression`: compression `V^* A V` along a linear isometric inclusion `V`.
* `CKMA.svdTruncation`: rank-`k` singular value decomposition truncation.

## Main results

* `CKMA.cauchy_interlacing`: Cauchy eigenvalue interlacing for a compression of any codimension
  (**13.7**).
* `CKMA.weyl_eigenvalue_add`, `CKMA.eigenvalue_rank_perturbation`: Weyl additive eigenvalue
  inequality and rank-perturbation interlacing (**13.8**).
* `CKMA.hoffman_wielandt`: Hoffman–Wielandt eigenvalue perturbation inequality (**13.10**).
* `CKMA.norm_trace_adjoint_comp_le`: von Neumann singular-value trace inequality for maps
  `E →ₗ[𝕜] F` (**13.13**).
* `CKMA.svdTruncation_minimizes`, `CKMA.sq_frobenius_sub_svdTruncation`,
  `CKMA.norm_sub_svdTruncation`: Mirsky / Eckart–Young low-rank approximation properties
  (**13.18**).
-/

public section

noncomputable section

namespace CKMA

open Module
open TauCeti.UnitarilyInvariantSeminorm (frobenius sq_frobenius_apply)
open scoped BigOperators InnerProductSpace

variable {𝕜 E F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- Compression along a linear isometric inclusion. -/
@[expose]
def hermitianCompression (A : E →ₗ[𝕜] E) (V : F →ₗᵢ[𝕜] E) : F →ₗ[𝕜] F :=
  V.toLinearMap.adjoint ∘ₗ A ∘ₗ V.toLinearMap

/-- The compression is `V^* ∘ A ∘ V`. -/
theorem hermitianCompression_def (A : E →ₗ[𝕜] E) (V : F →ₗᵢ[𝕜] E) :
    hermitianCompression A V = V.toLinearMap.adjoint ∘ₗ A ∘ₗ V.toLinearMap :=
  rfl

/-- The compression `V^* A V` evaluated at a vector. -/
theorem hermitianCompression_apply (A : E →ₗ[𝕜] E) (V : F →ₗᵢ[𝕜] E) (x : F) :
    hermitianCompression A V x = V.toLinearMap.adjoint (A (V x)) := by
  simp [hermitianCompression]

/-- The quadratic form of a compression is the quadratic form of `A` pulled back along `V`. -/
theorem inner_hermitianCompression_apply_self (A : E →ₗ[𝕜] E) (V : F →ₗᵢ[𝕜] E) (x : F) :
    ⟪hermitianCompression A V x, x⟫_𝕜 = ⟪A (V x), V x⟫_𝕜 := by
  rw [hermitianCompression_apply, LinearMap.adjoint_inner_left, LinearIsometry.coe_toLinearMap]

/-- Compressing a symmetric operator along an isometry preserves symmetry. -/
theorem isSymmetric_hermitianCompression (A : E →ₗ[𝕜] E) (hA : A.IsSymmetric)
    (V : F →ₗᵢ[𝕜] E) : (hermitianCompression A V).IsSymmetric := by
  intro x y
  simp only [hermitianCompression, LinearMap.comp_apply,
    LinearMap.adjoint_inner_left, LinearMap.adjoint_inner_right]
  exact hA _ _

/-- The `r`-th decreasing eigenvalue of a symmetric map of rank at most `r` is nonpositive. -/
private lemma eigenvalues_le_zero_of_finrank_range_le {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric)
    {r : ℕ} (hr : finrank 𝕜 (LinearMap.range T) ≤ r) (hrn : r < finrank 𝕜 E) :
    hT.eigenvalues rfl ⟨r, hrn⟩ ≤ 0 := by
  by_contra hpos
  have hpos' : 0 < hT.eigenvalues rfl ⟨r, hrn⟩ := lt_of_not_ge hpos
  obtain ⟨S, hSdim, hSlow⟩ :=
    hT.exists_submodule_forall_unit_eigenvalue_le_re_inner rfl ⟨r, hrn⟩
  have hinj : Function.Injective (T ∘ₗ S.subtype) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra hx0
    have hnorm : ‖(x : E)‖ ≠ 0 := norm_ne_zero_iff.mpr (Subtype.coe_injective.ne hx0)
    set z : E := ((‖(x : E)‖⁻¹ : ℝ) : 𝕜) • (x : E)
    have hzS : z ∈ S := S.smul_mem _ x.property
    have hzn : ‖z‖ = 1 := by
      rw [norm_smul, RCLike.norm_ofReal, abs_inv, abs_norm, inv_mul_cancel₀ hnorm]
    have hxT : T (x : E) = 0 := by simpa [LinearMap.comp_apply] using hx
    have hz0 : T z = 0 := by rw [show z = _ from rfl, map_smul, hxT, smul_zero]
    have hlow := hSlow z hzS hzn
    rw [hz0, inner_zero_left, map_zero] at hlow
    exact (hpos'.trans_le hlow).false
  have hrank : finrank 𝕜 (LinearMap.range (T ∘ₗ S.subtype)) = r + 1 := by
    rw [LinearMap.finrank_range_of_inj hinj, hSdim]
  have hle : finrank 𝕜 (LinearMap.range (T ∘ₗ S.subtype)) ≤ finrank 𝕜 (LinearMap.range T) :=
    Submodule.finrank_mono (LinearMap.range_comp_le_range _ _)
  omega

/-- **13.7**: Cauchy interlacing for a compression `V^* A V` along a linear isometry
`V : F →ₗᵢ[𝕜] E` of any codimension `n - m`, where `n = finrank 𝕜 E` and `m = finrank 𝕜 F`:
with zero-based decreasing eigenvalues, `λ_{i + (n - m)}(A) ≤ μᵢ ≤ λᵢ(A)`. It is derived from
TauCeti's `LinearMap.IsSymmetric.eigenvalues_le_eigenvalues_of_isometry` and its primed form. -/
theorem cauchy_interlacing (A : E →ₗ[𝕜] E) (hA : A.IsSymmetric)
    (V : F →ₗᵢ[𝕜] E) (i : Fin (finrank 𝕜 F)) (j k : Fin (finrank 𝕜 E))
    (hj : j.val = i.val) (hk : k.val = i.val + (finrank 𝕜 E - finrank 𝕜 F)) :
    hA.eigenvalues rfl k ≤ (isSymmetric_hermitianCompression A hA V).eigenvalues rfl i ∧
      (isSymmetric_hermitianCompression A hA V).eigenvalues rfl i ≤ hA.eigenvalues rfl j := by
  have hmn : finrank 𝕜 F ≤ finrank 𝕜 E :=
    LinearMap.finrank_le_finrank_of_injective (f := V.toLinearMap) V.injective
  have hST := inner_hermitianCompression_apply_self A V
  have hC := isSymmetric_hermitianCompression A hA V
  obtain rfl : k = Fin.cast (Nat.add_sub_of_le hmn) (i.addNat (finrank 𝕜 E - finrank 𝕜 F)) :=
    Fin.ext (by simp [hk])
  obtain rfl : j = Fin.castLE hmn i := Fin.ext (by simp [hj])
  exact ⟨hA.eigenvalues_le_eigenvalues_of_isometry' hC rfl rfl V hST hmn i,
    hA.eigenvalues_le_eigenvalues_of_isometry hC rfl rfl V hST hmn i⟩

/-- **13.8**: the mixed-index Weyl inequality `λₖ(A + B) ≤ λᵢ(A) + λⱼ(B)` for `i + j ≤ k`.
Indices start at zero. This is TauCeti's `LinearMap.IsSymmetric.eigenvalues_add_le`. -/
theorem weyl_eigenvalue_add (A B : E →ₗ[𝕜] E) (hA : A.IsSymmetric)
    (hB : B.IsSymmetric)
    (i j k : Fin (finrank 𝕜 E)) (hk : i.val + j.val ≤ k.val) :
    (hA.add hB).eigenvalues rfl k ≤ hA.eigenvalues rfl i + hB.eigenvalues rfl j :=
  hA.eigenvalues_add_le hB rfl hk

/-- The corresponding index-shift interlacing bounds for a rank-at-most-`r` perturbation. -/
theorem eigenvalue_rank_perturbation (A B : E →ₗ[𝕜] E) (hA : A.IsSymmetric)
    (hB : B.IsSymmetric) {r : ℕ} (hr : finrank 𝕜 (LinearMap.range (A - B)) ≤ r)
    (i j : Fin (finrank 𝕜 E)) (hj : j.val = i.val + r) :
    hA.eigenvalues rfl j ≤ hB.eigenvalues rfl i ∧
      hB.eigenvalues rfl j ≤ hA.eigenvalues rfl i := by
  have hlt : r < finrank 𝕜 E := by
    have := j.isLt
    rw [hj] at this
    omega
  let t : Fin (finrank 𝕜 E) := ⟨r, hlt⟩
  have ht : j.val = i.val + t.val := by simpa [t] using hj
  have hrBA : finrank 𝕜 (LinearMap.range (B - A)) ≤ r := by
    have hsub : B - A = -(A - B) := by
      rw [sub_eq_add_neg, sub_eq_add_neg, neg_add, neg_neg, add_comm]
    have hrange : LinearMap.range (-(A - B)) = LinearMap.range (A - B) := by
      ext v
      simp only [LinearMap.mem_range, LinearMap.neg_apply]
      constructor
      · rintro ⟨w, hw⟩
        refine ⟨-w, ?_⟩
        rw [← hw, map_neg]
      · rintro ⟨w, hw⟩
        refine ⟨-w, ?_⟩
        rw [map_neg, neg_neg, hw]
    rw [hsub, hrange]
    exact hr
  refine ⟨?_, ?_⟩
  · have hoper : B + (A - B) = A := by
      rw [sub_eq_add_neg, ← add_assoc, add_comm B A, add_assoc, add_neg_cancel, add_zero]
    have hcong : (hB.add (hA.sub hB)).eigenvalues rfl =
        hA.eigenvalues rfl := by
      simpa using
        LinearMap.IsSymmetric.eigenvalues_congr hoper (hB.add (hA.sub hB)) hA rfl
    have hle := weyl_eigenvalue_add B (A - B) hB (hA.sub hB) i t j ht.ge
    have hnonpos : (hA.sub hB).eigenvalues rfl t ≤ 0 :=
      eigenvalues_le_zero_of_finrank_range_le (hA.sub hB) hr hlt
    calc hA.eigenvalues rfl j
        = (hB.add (hA.sub hB)).eigenvalues rfl j := by rw [hcong]
      _ ≤ hB.eigenvalues rfl i + (hA.sub hB).eigenvalues rfl t := hle
      _ ≤ hB.eigenvalues rfl i := by
          simpa using add_le_add_left hnonpos (hB.eigenvalues rfl i)
  · have hoper : A + (B - A) = B := by
      rw [sub_eq_add_neg, ← add_assoc, add_comm A B, add_assoc, add_neg_cancel, add_zero]
    have hcong : (hA.add (hB.sub hA)).eigenvalues rfl =
        hB.eigenvalues rfl := by
      simpa using
        LinearMap.IsSymmetric.eigenvalues_congr hoper (hA.add (hB.sub hA)) hB rfl
    have hle := weyl_eigenvalue_add A (B - A) hA (hB.sub hA) i t j ht.ge
    have hnonpos : (hB.sub hA).eigenvalues rfl t ≤ 0 :=
      eigenvalues_le_zero_of_finrank_range_le (hB.sub hA) hrBA hlt
    calc hB.eigenvalues rfl j
        = (hA.add (hB.sub hA)).eigenvalues rfl j := by rw [hcong]
      _ ≤ hA.eigenvalues rfl i + (hB.sub hA).eigenvalues rfl t := hle
      _ ≤ hA.eigenvalues rfl i := by
          simpa using add_le_add_left hnonpos (hA.eigenvalues rfl i)

/-- An orthonormal eigenbasis of `B` is an eigenbasis of `B.adjoint`, with conjugate eigenvalues. -/
private lemma adjoint_apply_of_orthonormal_eigenbasis (B : E →ₗ[𝕜] E)
    (v : OrthonormalBasis (Fin (finrank 𝕜 E)) 𝕜 E) (β : Fin (finrank 𝕜 E) → 𝕜)
    (hB : ∀ i, B (v i) = β i • v i) (j : Fin (finrank 𝕜 E)) :
    B.adjoint (v j) = star (β j) • v j := by
  rw [← v.sum_repr' (B.adjoint (v j)), ← v.sum_repr' (star (β j) • v j)]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  congr 1
  rw [LinearMap.adjoint_inner_right, hB, inner_smul_left, inner_smul_right]
  by_cases hkj : k = j
  · simp [hkj]
  · simp [v.inner_eq_zero hkj]

omit [FiniteDimensional 𝕜 E] in
/-- A permutation matrix has a single `1` in each row, in the permuted column. -/
private lemma sum_permMatrix_mul (σ : Equiv.Perm (Fin (finrank 𝕜 E)))
    (c : Fin (finrank 𝕜 E) → Fin (finrank 𝕜 E) → ℝ) (i : Fin (finrank 𝕜 E)) :
    ∑ j, σ.permMatrix ℝ i j * c i j = c i (σ i) := by
  rw [Finset.sum_eq_single_of_mem (σ i) (Finset.mem_univ _)]
  · simp [Equiv.Perm.permMatrix]
  · intro j _ hj
    simp [Equiv.Perm.permMatrix]
    intro h
    exact absurd h hj.symm

/-- Squared moduli of the overlaps between two orthonormal bases. -/
private def eigenbasisOverlap (u v : OrthonormalBasis (Fin (finrank 𝕜 E)) 𝕜 E) :
    Matrix (Fin (finrank 𝕜 E)) (Fin (finrank 𝕜 E)) ℝ :=
  Matrix.of fun i j ↦ ‖⟪u i, v j⟫_𝕜‖ ^ 2

omit [FiniteDimensional 𝕜 E] in
/-- The overlap matrix of two orthonormal bases is doubly stochastic. -/
private lemma eigenbasisOverlap_mem_doublyStochastic
    (u v : OrthonormalBasis (Fin (finrank 𝕜 E)) 𝕜 E) :
    eigenbasisOverlap u v ∈ doublyStochastic ℝ (Fin (finrank 𝕜 E)) := by
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨fun i j ↦ ?_, fun i ↦ ?_, fun j ↦ ?_⟩
  · simp only [eigenbasisOverlap, Matrix.of_apply]
    positivity
  · simpa [eigenbasisOverlap, Matrix.of_apply, u.norm_eq_one] using
      v.sum_sq_norm_inner_left (u i)
  · simpa [eigenbasisOverlap, Matrix.of_apply, v.norm_eq_one] using
      u.sum_sq_norm_inner_right (v j)

/-- Frobenius energy of `A - B` in a pair of orthonormal eigenbases. The squared overlaps of the
two bases turn the energy into a doubly stochastic average of the squared eigenvalue gaps. -/
private lemma sq_frobenius_sub_eq_sum_overlap_mul_eigenvalueGap (A B : E →ₗ[𝕜] E)
    (u v : OrthonormalBasis (Fin (finrank 𝕜 E)) 𝕜 E) (α β : Fin (finrank 𝕜 E) → 𝕜)
    (hA : ∀ i, A (u i) = α i • u i) (hB : ∀ i, B (v i) = β i • v i) :
    frobenius 𝕜 E E (A - B) ^ 2 =
      ∑ i, ∑ j, ‖α i - β j‖ ^ 2 * eigenbasisOverlap u v i j := by
  rw [sq_frobenius_apply u (A - B)]
  simp_rw [← v.sum_sq_norm_inner_right]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  have hadj := adjoint_apply_of_orthonormal_eigenbasis B v β hB j
  have hinner : ⟪v j, (A - B) (u i)⟫_𝕜 = (α i - β j) * ⟪v j, u i⟫_𝕜 := by
    rw [LinearMap.sub_apply, inner_sub_right, hA, inner_smul_right,
      ← LinearMap.adjoint_inner_left, hadj, inner_smul_left, starRingEnd_apply, star_star]
    ring
  rw [hinner, norm_mul, mul_pow, norm_inner_symm (v j) (u i), eigenbasisOverlap,
    Matrix.of_apply]

/-- **13.10**: Hoffman–Wielandt in supplied orthonormal eigenbases.
Over complex scalars such bases exist by TauCeti's normal spectral theorem. The supplied-basis
form also applies over real scalars; repeated eigenvalues are allowed. -/
theorem hoffman_wielandt (A B : E →ₗ[𝕜] E)
    (u v : OrthonormalBasis (Fin (finrank 𝕜 E)) 𝕜 E)
    (α β : Fin (finrank 𝕜 E) → 𝕜)
    (hA : ∀ i, A (u i) = α i • u i) (hB : ∀ i, B (v i) = β i • v i) :
    ∃ σ : Equiv.Perm (Fin (finrank 𝕜 E)),
      (∑ i, ‖α i - β (σ i)‖ ^ 2) ≤ frobenius 𝕜 E E (A - B) ^ 2 := by
  obtain ⟨w, hw0, hwsum, hwM⟩ :=
    exists_eq_sum_perm_of_mem_doublyStochastic (eigenbasisOverlap_mem_doublyStochastic u v)
  have havg :
      ∑ σ, w σ * (∑ i, ‖α i - β (σ i)‖ ^ 2) = frobenius 𝕜 E E (A - B) ^ 2 := by
    rw [sq_frobenius_sub_eq_sum_overlap_mul_eigenvalueGap A B u v α β hA hB]
    have hentry (i j) : eigenbasisOverlap u v i j = ∑ σ, w σ * σ.permMatrix ℝ i j := by
      rw [← hwM]
      simp [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    have hcost (σ : Equiv.Perm (Fin (finrank 𝕜 E))) : ∑ i, ‖α i - β (σ i)‖ ^ 2 =
        ∑ i, ∑ j, σ.permMatrix ℝ i j * ‖α i - β j‖ ^ 2 := by
      refine Finset.sum_congr rfl fun i _ ↦
        (sum_permMatrix_mul σ (fun i j ↦ ‖α i - β j‖ ^ 2) i).symm
    simp_rw [hcost, Finset.mul_sum]
    conv_lhs =>
      rw [Finset.sum_comm]
      enter [2]
      ext i
      rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    rw [hentry i j, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ ↦ ?_
    ring
  by_contra! hgt
  have hpos : ∃ σ, 0 < w σ := by
    by_contra hnon
    push Not at hnon
    have hzero : ∑ σ, w σ = 0 :=
      Finset.sum_eq_zero fun σ _ ↦ le_antisymm (hnon σ) (hw0 σ)
    linarith
  obtain ⟨σ₀, hσ₀⟩ := hpos
  have hlt : frobenius 𝕜 E E (A - B) ^ 2 <
      ∑ σ, w σ * (∑ i, ‖α i - β (σ i)‖ ^ 2) := by
    rw [show frobenius 𝕜 E E (A - B) ^ 2 =
        ∑ σ, w σ * frobenius 𝕜 E E (A - B) ^ 2 by
      rw [← Finset.sum_mul, hwsum, one_mul]]
    refine Finset.sum_lt_sum ?_ ⟨σ₀, Finset.mem_univ _, ?_⟩
    · intro σ _
      exact mul_le_mul_of_nonneg_left (le_of_lt (hgt σ)) (hw0 σ)
    · exact mul_lt_mul_of_pos_left (hgt σ₀) hσ₀
  exact lt_irrefl _ (havg.symm ▸ hlt)

/-- **13.13**: the singular-value von Neumann trace inequality
`‖tr (A^* B)‖ ≤ ∑ᵢ σᵢ(A) σᵢ(B)` for maps `A B : E →ₗ[𝕜] F` between finite-dimensional inner
product spaces. The singular values vanish beyond `min (finrank 𝕜 E) (finrank 𝕜 F)`, so the sum
may run over the source dimension. -/
theorem norm_trace_adjoint_comp_le (A B : E →ₗ[𝕜] F) :
    ‖LinearMap.trace 𝕜 E (A.adjoint ∘ₗ B)‖ ≤
      ∑ i : Fin (finrank 𝕜 E), A.singularValues i * B.singularValues i := by
  obtain ⟨w, hw⟩ := A.exists_orthonormalBasis_apply_eq_leftSingularVector
  let v := A.rightSingularBasis
  let d := min (finrank 𝕜 E) (finrank 𝕜 F)
  let ιE : Fin d → Fin (finrank 𝕜 E) := Fin.castLE (min_le_left _ _)
  let ιF : Fin d → Fin (finrank 𝕜 F) := Fin.castLE (min_le_right _ _)
  have hιE : Function.Injective ιE := Fin.castLE_injective _
  -- Indices outside `ιE` are at least `finrank 𝕜 F`, where the singular values of `A` vanish.
  have hout (i : Fin (finrank 𝕜 E)) (hi : i ∉ Set.range ιE) : A.singularValues i = 0 := by
    refine A.singularValues_of_finrank_le_right ?_
    by_contra! h
    exact hi ⟨⟨i, lt_min i.isLt h⟩, rfl⟩
  have hAv (i : Fin d) : A (v (ιE i)) = ((A.singularValues i : ℝ) : 𝕜) • w (ιF i) := by
    rw [A.apply_rightSingularBasis]
    by_cases hσ : A.singularValues i = 0
    · simp [ιE, hσ]
    · rw [hw (ιE i) (ιF i) rfl hσ]
      rfl
  set z := LinearMap.trace 𝕜 E (A.adjoint ∘ₗ B) with hz
  have htr : z = ∑ i : Fin d, ((A.singularValues i : ℝ) : 𝕜) * ⟪w (ιF i), B (v (ιE i))⟫_𝕜 := by
    rw [hz, LinearMap.trace_eq_sum_inner _ v]
    symm
    refine Fintype.sum_of_injective ιE hιE _ _ (fun i hi ↦ ?_) (fun i ↦ ?_)
    · rw [LinearMap.comp_apply, LinearMap.adjoint_inner_right, A.apply_rightSingularBasis,
        hout i hi]
      simp
    · rw [LinearMap.comp_apply, LinearMap.adjoint_inner_right, hAv, inner_smul_left,
        RCLike.conj_ofReal]
  -- Rotate `B` by a unimodular phase that makes the trace real and nonnegative.
  obtain ⟨c, hc, hcz⟩ : ∃ c : 𝕜, ‖c‖ = 1 ∧ (‖z‖ : 𝕜) = c * z := by
    by_cases hz0 : z = 0
    · exact ⟨1, by simp, by simp [hz0]⟩
    · have hn : (‖z‖ : 𝕜) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hz0
      refine ⟨starRingEnd 𝕜 z / ‖z‖, ?_, ?_⟩
      · rw [norm_div, RCLike.norm_conj, RCLike.norm_ofReal, abs_norm,
          div_self (norm_ne_zero_iff.mpr hz0)]
      · rw [div_mul_eq_mul_div, RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.ofReal_pow, sq,
          mul_div_assoc, div_self hn, mul_one]
  have hcross := (c • B).sum_antitone_mul_re_inner_le_sum_mul_singularValues
    (w ∘ ιF) (v ∘ ιE) (w.orthonormal.comp _ (Fin.castLE_injective _))
    (v.orthonormal.comp _ hιE) (fun i _ ↦ A.singularValues_antitone (Nat.le_succ i))
    (A.singularValues_nonneg _)
  have hre : ‖z‖ = ∑ i : Fin d,
      A.singularValues i * RCLike.re ⟪w (ιF i), (c • B) (v (ιE i))⟫_𝕜 := by
    have h := congrArg RCLike.re hcz
    rw [RCLike.ofReal_re] at h
    rw [h, htr, Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [LinearMap.smul_apply, inner_smul_right, ← RCLike.re_ofReal_mul]
    ring_nf
  have hext : ∑ i : Fin d, A.singularValues i * B.singularValues i =
      ∑ i : Fin (finrank 𝕜 E), A.singularValues i * B.singularValues i :=
    Fintype.sum_of_injective ιE hιE _ _ (fun i hi ↦ by rw [hout i hi, zero_mul])
      (fun _ ↦ rfl)
  rw [hre, ← hext]
  simpa [hc] using hcross

/-- The rank-`k` SVD truncation, defined using TauCeti's canonical right singular basis. -/
@[expose]
def svdTruncation (A : E →ₗ[𝕜] F) (k : ℕ) : E →ₗ[𝕜] F :=
  ∑ i : Fin (finrank 𝕜 E), if i.val < k then
    (innerSL 𝕜 (A.rightSingularBasis i)).toLinearMap.smulRight
      (A (A.rightSingularBasis i)) else 0

/-- The SVD truncation is the sum of the rank-one maps `⟪vᵢ, ·⟫ • A vᵢ` over the first `k` right
singular vectors `vᵢ`. -/
theorem svdTruncation_def (A : E →ₗ[𝕜] F) (k : ℕ) :
    svdTruncation A k = ∑ i : Fin (finrank 𝕜 E), if i.val < k then
      (innerSL 𝕜 (A.rightSingularBasis i)).toLinearMap.smulRight
        (A (A.rightSingularBasis i)) else 0 :=
  rfl

/-- Send index `i` to `i + k` when that index stays in range, and otherwise into the head. -/
private def tailFirstTo (n k : ℕ) : Fin n → Fin n := fun i ↦
  if h : (i : ℕ) + k < n then ⟨(i : ℕ) + k, h⟩
  else ⟨(i : ℕ) - (n - k), by have := i.isLt; omega⟩

/-- Inverse index map of `tailFirstTo`, returning the truncated head before the tail. -/
private def tailFirstInv (n k : ℕ) : Fin n → Fin n := fun i ↦
  if h : (i : ℕ) < k then ⟨(i : ℕ) + (n - k), by have := i.isLt; omega⟩
  else ⟨(i : ℕ) - k, by have := i.isLt; omega⟩

/-- Permutation of `Fin n` listing `k, k + 1, …` before `0, …, k - 1`. -/
private def tailFirst (n k : ℕ) : Fin n ≃ Fin n where
  toFun := tailFirstTo n k
  invFun := tailFirstInv n k
  left_inv i := by
    apply Fin.ext
    by_cases h : (i : ℕ) + k < n
    · rw [tailFirstTo, dite_eq_left h, tailFirstInv,
        dite_eq_right (by omega : ¬ (i : ℕ) + k < k), Fin.val_mk, Fin.val_mk]
      exact Nat.add_sub_cancel (i : ℕ) k
    · have hi := i.isLt
      have hlt : (i : ℕ) - (n - k) < k := by omega
      rw [tailFirstTo, dite_eq_right h, tailFirstInv, dite_eq_left hlt, Fin.val_mk, Fin.val_mk]
      exact Nat.sub_add_cancel (by omega : n - k ≤ (i : ℕ))
  right_inv i := by
    apply Fin.ext
    by_cases h : (i : ℕ) < k
    · have hi := i.isLt
      have hnot : ¬ (i : ℕ) + (n - k) + k < n := by omega
      rw [tailFirstInv, dite_eq_left h, tailFirstTo, dite_eq_right hnot, Fin.val_mk, Fin.val_mk]
      exact Nat.add_sub_cancel (i : ℕ) (n - k)
    · have hi := i.isLt
      have hlt : (i : ℕ) - k + k < n := by omega
      rw [tailFirstInv, dite_eq_right h, tailFirstTo, dite_eq_left hlt, Fin.val_mk, Fin.val_mk]
      exact Nat.sub_add_cancel (by omega : k ≤ (i : ℕ))

/-- On the forward branch, `tailFirst` adds `k`. -/
private lemma tailFirst_val_of_add_lt {n k : ℕ} (i : Fin n) (h : (i : ℕ) + k < n) :
    (tailFirst n k i : ℕ) = (i : ℕ) + k := by
  unfold tailFirst
  rw [Equiv.coe_fn_mk, tailFirstTo, dite_eq_left h, Fin.val_mk]

/-- On the complementary branch, `tailFirst` returns the truncated head. -/
private lemma tailFirst_val_of_le_add {n k : ℕ} (i : Fin n) (h : n ≤ (i : ℕ) + k) :
    (tailFirst n k i : ℕ) = (i : ℕ) - (n - k) := by
  unfold tailFirst
  rw [Equiv.coe_fn_mk, tailFirstTo, dite_eq_right (not_lt.mpr h), Fin.val_mk]

/-- `svdTruncation A k` reproduces `A` on the first `k` right singular vectors and vanishes on the
rest. -/
theorem svdTruncation_apply_rightSingularBasis (A : E →ₗ[𝕜] F) (k : ℕ)
    (i : Fin (finrank 𝕜 E)) :
    svdTruncation A k (A.rightSingularBasis i) =
      if i.val < k then A (A.rightSingularBasis i) else 0 := by
  let v := A.rightSingularBasis
  rw [svdTruncation, LinearMap.sum_apply]
  rw [Finset.sum_eq_single i (fun j _ hji ↦ ?_) (by simp)]
  · split_ifs with hi
    · rw [LinearMap.smulRight_apply, ContinuousLinearMap.toLinearMap_innerSL_apply,
        innerₛₗ_apply_apply, v.inner_eq_one i, one_smul]
    · rfl
  · split_ifs with hj
    · rw [LinearMap.smulRight_apply, ContinuousLinearMap.toLinearMap_innerSL_apply,
        innerₛₗ_apply_apply, v.inner_eq_zero hji, zero_smul]
    · rfl

/-- The SVD tail kills the first `k` right singular vectors and agrees with `A` on the rest. -/
theorem sub_svdTruncation_apply_rightSingularBasis (A : E →ₗ[𝕜] F) (k : ℕ)
    (i : Fin (finrank 𝕜 E)) :
    (A - svdTruncation A k) (A.rightSingularBasis i) =
      if i.val < k then 0 else A (A.rightSingularBasis i) := by
  rw [LinearMap.sub_apply, svdTruncation_apply_rightSingularBasis]
  split_ifs <;> simp

/-- The source Gram operator of the SVD tail is diagonal in the right singular basis of `A`, with
eigenvalue `0` on the truncated head and `σᵢ²` on the tail. -/
private lemma adjoint_comp_self_sub_svdTruncation_rightSingularBasis (A : E →ₗ[𝕜] F) (k : ℕ)
    (i : Fin (finrank 𝕜 E)) :
    ((A - svdTruncation A k).adjoint ∘ₗ (A - svdTruncation A k)) (A.rightSingularBasis i) =
      ((if i.val < k then 0 else A.singularValues i ^ 2 : ℝ) : 𝕜) •
        A.rightSingularBasis i := by
  let T := A - svdTruncation A k
  let v := A.rightSingularBasis
  let c : 𝕜 := ((if i.val < k then 0 else A.singularValues i ^ 2 : ℝ) : 𝕜)
  change (T.adjoint ∘ₗ T) (v i) = c • v i
  rw [← v.sum_repr' ((T.adjoint ∘ₗ T) (v i)), ← v.sum_repr' (c • v i)]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  congr 1
  rw [LinearMap.comp_apply, T.adjoint_inner_right, inner_smul_right,
    sub_svdTruncation_apply_rightSingularBasis A k j,
    sub_svdTruncation_apply_rightSingularBasis A k i]
  dsimp only [c]
  by_cases hi : i.val < k
  · rw [ite_eq_left hi, inner_zero_right, ite_eq_left hi, RCLike.ofReal_zero, zero_mul]
  · rw [ite_eq_right hi, ite_eq_right hi]
    by_cases hj : j.val < k
    · have hne : j ≠ i := fun h ↦ hi (h ▸ hj)
      rw [ite_eq_left hj, inner_zero_left, v.inner_eq_zero hne, mul_zero]
    · rw [ite_eq_right hj, A.inner_apply_rightSingularBasis]
      by_cases hji : j = i
      · rw [hji, v.inner_eq_one i, mul_one]
      · rw [v.inner_eq_zero hji, mul_zero, mul_zero]

/-- Singular values of the SVD tail are the singular values of `A`, shifted by `k` and padded by
zeros. The Gram eigenvalues on the right singular basis vanish on the head, so the sorted list is
the tail. -/
theorem singularValues_sub_svdTruncation (A : E →ₗ[𝕜] F) (k i : ℕ) :
    (A - svdTruncation A k).singularValues i = A.singularValues (i + k) := by
  let T := A - svdTruncation A k
  let n := finrank 𝕜 E
  let v := A.rightSingularBasis
  let π : Fin n ≃ Fin n := tailFirst n k
  let w : OrthonormalBasis (Fin n) 𝕜 E := v.reindex π.symm
  let μ : Fin n → ℝ := fun j ↦ A.singularValues ((j : ℕ) + k) ^ 2
  have hμ : Antitone μ := fun a b hab ↦
    A.sq_singularValues_antitone
      (Nat.add_le_add_right (Fin.le_iff_val_le_val.mp hab) k)
  have he : ∀ j, (T.adjoint ∘ₗ T) (w j) = (μ j : 𝕜) • w j := by
    intro j
    have hbasis := adjoint_comp_self_sub_svdTruncation_rightSingularBasis A k (π j)
    simp only [w, OrthonormalBasis.reindex_apply, Equiv.symm_symm] at hbasis ⊢
    rw [hbasis]
    congr 1
    by_cases h : (j : ℕ) + k < n
    · have hval : (π j : ℕ) = (j : ℕ) + k := tailFirst_val_of_add_lt j h
      have hge : ¬ (π j).val < k := by rw [hval]; omega
      rw [ite_eq_right hge]
      simp [μ, hval]
    · have hle : n ≤ (j : ℕ) + k := not_lt.mp h
      have hlt : (π j).val < k := by
        rw [tailFirst_val_of_le_add j hle]
        have := j.isLt
        omega
      simp [μ, hlt, A.singularValues_of_finrank_le hle]
  by_cases hi : i < n
  · have hsq := T.sq_singularValues_eq_of_adjoint_comp_self_eigenbasis w hμ he ⟨i, hi⟩
    exact (sq_eq_sq₀ (T.singularValues_nonneg _) (A.singularValues_nonneg _)).mp (by
      simpa [μ] using hsq)
  · rw [T.singularValues_of_finrank_le (not_lt.mp hi),
      A.singularValues_of_finrank_le (by omega)]

/-- Shifting a square-summable singular-value sequence by `k` leaves the square tail. -/
private lemma sum_singularValues_sq_shift (A : E →ₗ[𝕜] F) (k : ℕ) :
    ∑ i : Fin (finrank 𝕜 E), A.singularValues ((i : ℕ) + k) ^ 2 =
      ∑ i : Fin (finrank 𝕜 E), if k ≤ i.val then A.singularValues i ^ 2 else 0 := by
  let n := finrank 𝕜 E
  let f : ℕ → ℝ := fun i ↦ A.singularValues i ^ 2
  have hf0 {j : ℕ} (hj : n ≤ j) : f j = 0 := by
    simp [f, A.singularValues_of_finrank_le hj]
  rw [Fin.sum_univ_eq_sum_range (fun i ↦ f (i + k)) n,
    Fin.sum_univ_eq_sum_range (fun i ↦ if k ≤ i then f i else 0) n]
  have hsub : Finset.Ico k n ⊆ Finset.range n := fun i hi ↦
    Finset.mem_range.mpr (Finset.mem_Ico.mp hi).2
  have htail : ∑ i ∈ Finset.range n, (if k ≤ i then f i else 0) =
      ∑ i ∈ Finset.Ico k n, f i := by
    have hsubset : ∑ i ∈ Finset.Ico k n, (if k ≤ i then f i else 0) =
        ∑ i ∈ Finset.range n, (if k ≤ i then f i else 0) :=
      Finset.sum_subset hsub fun i hi hnot ↦ by
        have hk : ¬ k ≤ i := fun hki ↦ hnot (Finset.mem_Ico.mpr ⟨hki, Finset.mem_range.mp hi⟩)
        simp [hk]
    rw [← hsubset]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    simp [(Finset.mem_Ico.mp hi).1]
  rw [htail, Finset.sum_Ico_eq_sum_range]
  -- Rewrite `n = (n - k) + k` only in `sum_range_add`, not inside the index `n - k`.
  by_cases hk : k ≤ n
  · have hsplit := Finset.sum_range_add (fun i ↦ f (i + k)) (n - k) k
    rw [Nat.sub_add_cancel hk] at hsplit
    rw [hsplit]
    have hzero : ∑ i ∈ Finset.range k, f (n - k + i + k) = 0 :=
      Finset.sum_eq_zero fun _ _ ↦ hf0 (by omega)
    rw [hzero, add_zero]
    refine Finset.sum_congr rfl fun i _ ↦ congr_arg f (Nat.add_comm i k)
  · rw [Nat.sub_eq_zero_of_le (Nat.le_of_lt (not_le.mp hk)), Finset.sum_range_zero]
    refine Finset.sum_eq_zero fun i hi ↦ hf0 ?_
    have hi' : i < n := Finset.mem_range.mp hi
    omega

/-- The SVD truncation uses at most `k` right singular vectors, so its rank is at most `k`. -/
theorem finrank_range_svdTruncation_le (A : E →ₗ[𝕜] F) (k : ℕ) :
    finrank 𝕜 (LinearMap.range (svdTruncation A k)) ≤ k := by
  let n := finrank 𝕜 E
  let v := A.rightSingularBasis
  let b : Fin (min k n) → F := fun j ↦ A (v ⟨j, by have := j.isLt; omega⟩)
  have hrange : LinearMap.range (svdTruncation A k) ≤ Submodule.span 𝕜 (Set.range b) := by
    rintro y ⟨x, rfl⟩
    rw [svdTruncation, LinearMap.sum_apply]
    refine Submodule.sum_mem _ fun i _ ↦ ?_
    by_cases hi : i.val < k
    · have hi' : (i : ℕ) < min k n := by have := i.isLt; omega
      simp only [hi, ite_true, LinearMap.smulRight_apply,
        ContinuousLinearMap.toLinearMap_innerSL_apply, innerₛₗ_apply_apply]
      have hb : A (v i) = b ⟨(i : ℕ), hi'⟩ := by
        apply congrArg A
        exact congrArg v (Fin.ext (by simp))
      rw [hb]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨(i : ℕ), hi'⟩, rfl⟩)
    · simp [hi]
  calc finrank 𝕜 (LinearMap.range (svdTruncation A k))
      ≤ finrank 𝕜 (Submodule.span 𝕜 (Set.range b)) := Submodule.finrank_mono hrange
    _ = (Set.range b).finrank 𝕜 := rfl
    _ ≤ Fintype.card (Fin (min k n)) := finrank_range_le_card b
    _ = min k n := Fintype.card_fin _
    _ ≤ k := min_le_left _ _

/-- **13.18**: SVD truncation is best in every unitarily invariant seminorm. -/
theorem svdTruncation_minimizes (A : E →ₗ[𝕜] F) (k : ℕ)
    (N : TauCeti.UnitarilyInvariantSeminorm 𝕜 E F) :
    finrank 𝕜 (LinearMap.range (svdTruncation A k)) ≤ k ∧
      ∀ B : E →ₗ[𝕜] F, finrank 𝕜 (LinearMap.range B) ≤ k →
        N (A - svdTruncation A k) ≤ N (A - B) := by
  refine ⟨finrank_range_svdTruncation_le A k, fun B hB ↦ ?_⟩
  -- `σₖ(B) = 0`, so the mixed-index law gives `σ_{j+k}(A) ≤ σⱼ(A - B)`.
  have hshift (j : ℕ) : A.singularValues (j + k) ≤ (A - B).singularValues j := by
    have hB0 : B.toContinuousLinearMap.singularValue k = 0 := by
      apply NNReal.coe_injective
      rw [NNReal.coe_zero, ContinuousLinearMap.singularValue_eq_linearMap_singularValues,
        LinearMap.coe_toContinuousLinearMap,
        B.singularValues_eq_zero_iff_le_finrank_range.mpr hB]
    have hadd : (A - B).toContinuousLinearMap + B.toContinuousLinearMap =
        A.toContinuousLinearMap := by
      ext x
      simp
    have hsum := ContinuousLinearMap.singularValue_add_index_le
      (A - B).toContinuousLinearMap B.toContinuousLinearMap j k
    rw [hadd, hB0, add_zero] at hsum
    simpa [ContinuousLinearMap.singularValue_eq_linearMap_singularValues,
      LinearMap.coe_toContinuousLinearMap] using NNReal.coe_le_coe.mpr hsum
  -- The tail's singular values are that shift, so its Ky Fan sums are smaller.
  refine N.map_le_of_kyFanSum_le fun m ↦ ?_
  simp only [LinearMap.kyFanSum_def]
  refine Finset.sum_le_sum fun j _ ↦ ?_
  rw [singularValues_sub_svdTruncation]
  exact hshift j

/-- The squared Frobenius error is the singular-value square tail. -/
theorem sq_frobenius_sub_svdTruncation (A : E →ₗ[𝕜] F) (k : ℕ) :
    frobenius 𝕜 E F (A - svdTruncation A k) ^ 2 =
      ∑ i : Fin (finrank 𝕜 E), if k ≤ i.val then A.singularValues i ^ 2 else 0 := by
  rw [LinearMap.sq_frobenius_apply_eq_sum_sq_singularValues]
  simp_rw [singularValues_sub_svdTruncation]
  exact sum_singularValues_sq_shift A k

/-- The operator-norm error of SVD truncation, including the zero singular-value tail. -/
theorem norm_sub_svdTruncation (A : E →ₗ[𝕜] F) (k : ℕ) :
    ‖(A - svdTruncation A k).toContinuousLinearMap‖ = A.singularValues k := by
  -- The operator norm is the largest singular value, which is the first entry of the tail.
  rw [LinearMap.norm_toContinuousLinearMap_eq_singularValues_zero,
    singularValues_sub_svdTruncation, Nat.zero_add]

end CKMA
