/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.CourantFischer
public import TauCeti.Analysis.InnerProductSpace.NormalOperator
public import TauCeti.Analysis.InnerProductSpace.FanDominance
public import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Analysis.Convex.Birkhoff
import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Basic
import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.EckartYoung

/-!
# Hermitian eigenvalues, singular values, and low-rank approximation

Sorted Hermitian eigenvalues are indexed from zero. Compression and rank perturbation statements
use the corresponding index shifts; Weyl's additive bound uses the output index `i+j`.
Hoffman–Wielandt is formulated in supplied orthonormal eigenbases, allowing repeated eigenvalues.
The eigenvalue matching is the one picked out of the doubly stochastic matrix of squared eigenbasis
overlaps by Birkhoff's theorem.

Frobenius energy and SVD truncation use TauCeti's canonical singular-value data. The low-rank
statements include all unitarily invariant seminorms, the Frobenius tail, and the operator-norm
tail, with zero-padding beyond the available rank. Sources: GAPS 13.7, 13.8, 13.10, 13.13, and
  13.18.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Module
open scoped BigOperators InnerProductSpace

variable {𝕜 E F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- The decreasing real eigenvalue list of a Hermitian endomorphism, with zero-based indices. -/
def orderedEigenvalues (A : E →ₗ[𝕜] E) (hA : A.IsSymmetric) :
    Fin (finrank 𝕜 E) → ℝ := hA.eigenvalues rfl

/-- Squared Frobenius norm, expressed intrinsically as the sum of squared singular values. -/
def frobeniusNormSq (A : E →ₗ[𝕜] F) : ℝ :=
  ∑ i : Fin (finrank 𝕜 E), A.singularValues i ^ 2

/-- Compression along a linear isometric inclusion. -/
def hermitianCompression (A : E →ₗ[𝕜] E) (V : F →ₗᵢ[𝕜] E) : F →ₗ[𝕜] F :=
  V.toLinearMap.adjoint ∘ₗ A ∘ₗ V.toLinearMap

/-- Compressing a symmetric operator along an isometry preserves symmetry. -/
theorem isSymmetric_hermitianCompression (A : E →ₗ[𝕜] E) (hA : A.IsSymmetric)
    (V : F →ₗᵢ[𝕜] E) : (hermitianCompression A V).IsSymmetric := by
  intro x y
  simp only [hermitianCompression, LinearMap.comp_apply,
    LinearMap.adjoint_inner_left, LinearMap.adjoint_inner_right]
  exact hA _ _

/-- Rayleigh quotient of a compression, pulled back along the isometric inclusion. -/
private lemma re_inner_hermitianCompression (A : E →ₗ[𝕜] E) (V : F →ₗᵢ[𝕜] E) (x : F) :
    RCLike.re ⟪hermitianCompression A V x, x⟫_𝕜 =
      RCLike.re ⟪A (V x), V x⟫_𝕜 := by
  simp only [hermitianCompression, LinearMap.comp_apply, LinearMap.adjoint_inner_left,
    LinearIsometry.coe_toLinearMap]

/-- A subspace of rank at least `d` contains a subspace of rank exactly `d`. -/
private lemma exists_submodule_finrank_eq {G : Type*} [NormedAddCommGroup G]
    [InnerProductSpace 𝕜 G] [FiniteDimensional 𝕜 G] {d : ℕ} {W : Submodule 𝕜 G}
    (hd : d ≤ finrank 𝕜 W) :
    ∃ W₀ : Submodule 𝕜 G, W₀ ≤ W ∧ finrank 𝕜 W₀ = d := by
  obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_finrank hd
  have hg : LinearIndependent 𝕜 (fun i : Fin d ↦ (W.subtype ∘ v) i) :=
    hv.map' W.subtype W.ker_subtype
  refine ⟨Submodule.span 𝕜 (Set.range fun i : Fin d ↦ (W.subtype ∘ v) i), ?_, ?_⟩
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact (v i).property
  · simpa using finrank_span_eq_card hg

/-- The `r`-th decreasing eigenvalue of a symmetric map of rank at most `r` is nonpositive. -/
private lemma eigenvalues_le_zero_of_finrank_range_le {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric)
    {r : ℕ} (hr : finrank 𝕜 (LinearMap.range T) ≤ r) (hrn : r < finrank 𝕜 E) :
    orderedEigenvalues T hT ⟨r, hrn⟩ ≤ 0 := by
  by_contra hpos
  have hpos' : 0 < orderedEigenvalues T hT ⟨r, hrn⟩ := lt_of_not_ge hpos
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
    exact (hpos'.trans_le (by simpa [orderedEigenvalues] using hlow)).false
  have hrank : finrank 𝕜 (LinearMap.range (T ∘ₗ S.subtype)) = r + 1 := by
    rw [LinearMap.finrank_range_of_inj hinj, hSdim]
  have hle : finrank 𝕜 (LinearMap.range (T ∘ₗ S.subtype)) ≤ finrank 𝕜 (LinearMap.range T) :=
    Submodule.finrank_mono (LinearMap.range_comp_le_range _ _)
  omega

/-- **13.7**: Cauchy interlacing for a codimension-one compression. -/
theorem cauchy_interlacing (A : E →ₗ[𝕜] E) (hA : A.IsSymmetric)
    (V : F →ₗᵢ[𝕜] E) (hdim : finrank 𝕜 E = finrank 𝕜 F + 1)
    (i : Fin (finrank 𝕜 F)) (j k : Fin (finrank 𝕜 E))
    (hj : j.val = i.val) (hk : k.val = i.val + 1) :
    orderedEigenvalues A hA k ≤ orderedEigenvalues (hermitianCompression A V)
      (isSymmetric_hermitianCompression A hA V) i ∧
      orderedEigenvalues (hermitianCompression A V) (isSymmetric_hermitianCompression A hA V) i ≤
        orderedEigenvalues A hA j := by
  let hC := isSymmetric_hermitianCompression A hA V
  let Rng := LinearMap.range V.toLinearMap
  have hRng : finrank 𝕜 Rng = finrank 𝕜 F := LinearMap.finrank_range_of_inj V.injective
  constructor
  · -- `λ_{i+1}(A) ≤ μ_i`: test a codimension-one slice of the Courant–Fischer lower subspace.
    obtain ⟨S, hSdim, hSlow⟩ :=
      hA.exists_submodule_forall_unit_eigenvalue_le_re_inner rfl k
    let meet := S ⊓ Rng
    let join := S ⊔ Rng
    have hWinter : (i : ℕ) + 1 ≤ finrank 𝕜 meet := by
      have hsum : finrank 𝕜 join + finrank 𝕜 meet = finrank 𝕜 S + finrank 𝕜 Rng := by
        simpa [join, meet] using Submodule.finrank_sup_add_finrank_inf_eq S Rng
      have hsup : finrank 𝕜 join ≤ finrank 𝕜 E := Submodule.finrank_le _
      have hS : finrank 𝕜 S = (i : ℕ) + 2 := by
        rw [hSdim, show (k : ℕ) = (i : ℕ) + 1 by simpa using hk]
      omega
    let Winter : Submodule 𝕜 Rng := S.comap Rng.subtype
    have hWinterDim : finrank 𝕜 Winter = finrank 𝕜 meet := by
      have himage : Winter.map Rng.subtype = Rng ⊓ S := by
        simp [Winter, Submodule.map_comap_subtype]
      rw [← Submodule.finrank_map_subtype_eq Rng Winter, himage, inf_comm]
    let e := LinearEquiv.ofInjective V.toLinearMap V.injective
    let WF : Submodule 𝕜 F := Winter.map e.symm.toLinearMap
    have hWF : (i : ℕ) + 1 ≤ finrank 𝕜 WF := by
      rw [e.symm.finrank_map_eq, hWinterDim]
      exact hWinter
    obtain ⟨W0, hW0le, hW0dim⟩ := exists_submodule_finrank_eq hWF
    obtain ⟨y, hy, hy1, hyup⟩ :=
      hC.exists_unit_vector_re_inner_le_eigenvalue rfl i W0 hW0dim
    have hyWF : y ∈ WF := hW0le hy
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hyWF
    have hzS : (z : E) ∈ S := by
      simpa [Winter] using hz
    have hVy : V (e.symm z) = (z : E) :=
      LinearEquiv.ofInjective_symm_apply (f := V.toLinearMap) (h := V.injective) z
    have hzn : ‖(z : E)‖ = 1 := by
      rw [← hVy, V.norm_map]
      simpa using hy1
    have hlow := hSlow (z : E) hzS hzn
    have hre := re_inner_hermitianCompression A V (e.symm z)
    have hyup' :
        RCLike.re ⟪hermitianCompression A V (e.symm z), e.symm z⟫_𝕜 ≤
          hC.eigenvalues rfl i := by
      simpa using hyup
    calc orderedEigenvalues A hA k
        ≤ RCLike.re ⟪A (z : E), (z : E)⟫_𝕜 := by simpa [orderedEigenvalues] using hlow
      _ = RCLike.re ⟪hermitianCompression A V (e.symm z), e.symm z⟫_𝕜 := by
          rw [hre, hVy]
      _ ≤ orderedEigenvalues (hermitianCompression A V) hC i := by
          simpa [orderedEigenvalues] using hyup'
  · -- `μ_i ≤ λ_i`: push the compression's lower subspace forward along `V`.
    obtain ⟨W, hWdim, hWlow⟩ :=
      hC.exists_submodule_forall_unit_eigenvalue_le_re_inner rfl i
    have hinj : Function.Injective (V.toLinearMap ∘ₗ W.subtype) :=
      V.injective.comp (Submodule.injective_subtype W)
    have hdimVW : finrank 𝕜 (LinearMap.range (V.toLinearMap ∘ₗ W.subtype)) = (j : ℕ) + 1 := by
      rw [LinearMap.finrank_range_of_inj hinj, hWdim]
      simp [show (i : ℕ) = (j : ℕ) by simpa using hj.symm]
    obtain ⟨x, hx, hx1, hxup⟩ :=
      hA.exists_unit_vector_re_inner_le_eigenvalue rfl j _ hdimVW
    obtain ⟨y, hyx⟩ := LinearMap.mem_range.mp hx
    have hxy : x = V (y : F) := by
      simpa [LinearMap.comp_apply, LinearIsometry.coe_toLinearMap] using hyx.symm
    have hy1 : ‖(y : F)‖ = 1 := by simpa [hxy, V.norm_map] using hx1
    have hlow := hWlow (y : F) y.property hy1
    have hre := re_inner_hermitianCompression A V (y : F)
    calc orderedEigenvalues (hermitianCompression A V) hC i
        ≤ RCLike.re ⟪hermitianCompression A V (y : F), (y : F)⟫_𝕜 := by
          simpa [orderedEigenvalues] using hlow
      _ = RCLike.re ⟪A x, x⟫_𝕜 := by rw [hre, hxy]
      _ ≤ orderedEigenvalues A hA j := by simpa [orderedEigenvalues] using hxup

/-- **13.8**: the mixed-index Weyl inequality. Indices start at zero, so the output index is `i+j`.
  -/
theorem weyl_eigenvalue_add (A B : E →ₗ[𝕜] E) (hA : A.IsSymmetric)
    (hB : B.IsSymmetric)
    (i j k : Fin (finrank 𝕜 E)) (hk : k.val = i.val + j.val) :
    orderedEigenvalues (A + B) (hA.add hB) k ≤ orderedEigenvalues A hA i +
      orderedEigenvalues B hB j := by
  let bA := hA.eigenvectorBasis rfl
  let bB := hB.eigenvectorBasis rfl
  let VA := bA.spanIndices ↑(Finset.Ici i)
  let VB := bB.spanIndices ↑(Finset.Ici j)
  have hVA : finrank 𝕜 VA = finrank 𝕜 E - (i : ℕ) := by
    simp [VA, OrthonormalBasis.finrank_spanIndices, Fin.card_Ici]
  have hVB : finrank 𝕜 VB = finrank 𝕜 E - (j : ℕ) := by
    simp [VB, OrthonormalBasis.finrank_spanIndices, Fin.card_Ici]
  let W := VA ⊓ VB
  let join := VA ⊔ VB
  have hW : finrank 𝕜 E - ((i : ℕ) + (j : ℕ)) ≤ finrank 𝕜 W := by
    have hsum : finrank 𝕜 join + finrank 𝕜 W = finrank 𝕜 VA + finrank 𝕜 VB := by
      simpa [join, W] using Submodule.finrank_sup_add_finrank_inf_eq VA VB
    have hsup : finrank 𝕜 join ≤ finrank 𝕜 E := Submodule.finrank_le _
    have hi : (i : ℕ) ≤ finrank 𝕜 E := Nat.le_of_lt i.isLt
    have hj' : (j : ℕ) ≤ finrank 𝕜 E := Nat.le_of_lt j.isLt
    omega
  obtain ⟨S, hSdim, hSlow⟩ :=
    (hA.add hB).exists_submodule_forall_unit_eigenvalue_le_re_inner rfl k
  have hmeet : S ⊓ W ≠ ⊥ := by
    refine Submodule.inf_ne_bot_of_finrank_lt ?_
    have hS : finrank 𝕜 S = (i : ℕ) + (j : ℕ) + 1 := by
      have hk' : (k : ℕ) = (i : ℕ) + (j : ℕ) := by simpa using hk
      rw [hSdim, hk']
    omega
  obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hmeet
  obtain ⟨hzS, hzW⟩ := Submodule.mem_inf.mp hz
  have hz0' : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz0
  let x : E := ((‖z‖⁻¹ : ℝ) : 𝕜) • z
  have hnx : ‖x‖ = 1 := by
    rw [norm_smul, RCLike.norm_ofReal, abs_inv, abs_norm, inv_mul_cancel₀ hz0']
  have hxS : x ∈ S := S.smul_mem _ hzS
  have hxW : x ∈ W := W.smul_mem _ hzW
  obtain ⟨hxVA, hxVB⟩ := Submodule.mem_inf.mp hxW
  have hlow := hSlow x hxS hnx
  have hAx : RCLike.re ⟪A x, x⟫_𝕜 ≤ orderedEigenvalues A hA i := by
    have hbound := hA.re_inner_apply_self_le_of_mem_spanIndices rfl
      (fun t ht => hA.eigenvalues_antitone rfl (by simpa using ht)) hxVA
    simpa [orderedEigenvalues, hnx] using hbound
  have hBx : RCLike.re ⟪B x, x⟫_𝕜 ≤ orderedEigenvalues B hB j := by
    have hbound := hB.re_inner_apply_self_le_of_mem_spanIndices rfl
      (fun t ht => hB.eigenvalues_antitone rfl (by simpa using ht)) hxVB
    simpa [orderedEigenvalues, hnx] using hbound
  have hadd : RCLike.re ⟪(A + B) x, x⟫_𝕜 =
      RCLike.re ⟪A x, x⟫_𝕜 + RCLike.re ⟪B x, x⟫_𝕜 := by
    rw [LinearMap.add_apply, inner_add_left, map_add]
  calc orderedEigenvalues (A + B) (hA.add hB) k
      ≤ RCLike.re ⟪(A + B) x, x⟫_𝕜 := by simpa [orderedEigenvalues] using hlow
    _ ≤ orderedEigenvalues A hA i + orderedEigenvalues B hB j := by
        rw [hadd]; exact add_le_add hAx hBx

/-- The corresponding index-shift interlacing bounds for a rank-at-most-`r` perturbation. -/
theorem eigenvalue_rank_perturbation (A B : E →ₗ[𝕜] E) (hA : A.IsSymmetric)
    (hB : B.IsSymmetric) {r : ℕ} (hr : finrank 𝕜 (LinearMap.range (A - B)) ≤ r)
    (i j : Fin (finrank 𝕜 E)) (hj : j.val = i.val + r) :
    orderedEigenvalues A hA j ≤ orderedEigenvalues B hB i ∧
      orderedEigenvalues B hB j ≤ orderedEigenvalues A hA i := by
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
    have hcong : orderedEigenvalues (B + (A - B)) (hB.add (hA.sub hB)) =
        orderedEigenvalues A hA := by
      simpa [orderedEigenvalues] using
        LinearMap.IsSymmetric.eigenvalues_congr hoper (hB.add (hA.sub hB)) hA rfl
    have hle := weyl_eigenvalue_add B (A - B) hB (hA.sub hB) i t j ht
    have hnonpos : orderedEigenvalues (A - B) (hA.sub hB) t ≤ 0 :=
      eigenvalues_le_zero_of_finrank_range_le (hA.sub hB) hr hlt
    calc orderedEigenvalues A hA j
        = orderedEigenvalues (B + (A - B)) (hB.add (hA.sub hB)) j := by rw [hcong]
      _ ≤ orderedEigenvalues B hB i + orderedEigenvalues (A - B) (hA.sub hB) t := hle
      _ ≤ orderedEigenvalues B hB i := by
          simpa using add_le_add_left hnonpos (orderedEigenvalues B hB i)
  · have hoper : A + (B - A) = B := by
      rw [sub_eq_add_neg, ← add_assoc, add_comm A B, add_assoc, add_neg_cancel, add_zero]
    have hcong : orderedEigenvalues (A + (B - A)) (hA.add (hB.sub hA)) =
        orderedEigenvalues B hB := by
      simpa [orderedEigenvalues] using
        LinearMap.IsSymmetric.eigenvalues_congr hoper (hA.add (hB.sub hA)) hB rfl
    have hle := weyl_eigenvalue_add A (B - A) hA (hB.sub hA) i t j ht
    have hnonpos : orderedEigenvalues (B - A) (hB.sub hA) t ≤ 0 :=
      eigenvalues_le_zero_of_finrank_range_le (hB.sub hA) hrBA hlt
    calc orderedEigenvalues B hB j
        = orderedEigenvalues (A + (B - A)) (hA.add (hB.sub hA)) j := by rw [hcong]
      _ ≤ orderedEigenvalues A hA i + orderedEigenvalues (B - A) (hB.sub hA) t := hle
      _ ≤ orderedEigenvalues A hA i := by
          simpa using add_le_add_left hnonpos (orderedEigenvalues A hA i)

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

/-- The squared Frobenius norm is the sum of `‖T eᵢ‖²` on every orthonormal basis. -/
private lemma sum_norm_apply_sq_eq_frobeniusNormSq (T : E →ₗ[𝕜] E)
    (b : OrthonormalBasis (Fin (finrank 𝕜 E)) 𝕜 E) :
    ∑ i, ‖T (b i)‖ ^ 2 = frobeniusNormSq T := by
  have htrace (e : OrthonormalBasis (Fin (finrank 𝕜 E)) 𝕜 E) :
      LinearMap.trace 𝕜 E (T.adjoint ∘ₗ T) = ∑ i, (‖T (e i)‖ ^ 2 : 𝕜) := by
    rw [LinearMap.trace_eq_sum_inner _ e]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [LinearMap.comp_apply, LinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
  unfold frobeniusNormSq
  apply RCLike.ofReal_injective (K := 𝕜)
  rw [RCLike.ofReal_sum, RCLike.ofReal_sum]
  simpa [T.norm_apply_rightSingularBasis] using
    (htrace b).symm.trans (htrace T.rightSingularBasis)

/-- Frobenius energy of `A - B` in a pair of orthonormal eigenbases. The squared overlaps of the
two bases turn the energy into a doubly stochastic average of the squared eigenvalue gaps. -/
private lemma frobeniusNormSq_eq_sum_overlap_mul_eigenvalueGap (A B : E →ₗ[𝕜] E)
    (u v : OrthonormalBasis (Fin (finrank 𝕜 E)) 𝕜 E) (α β : Fin (finrank 𝕜 E) → 𝕜)
    (hA : ∀ i, A (u i) = α i • u i) (hB : ∀ i, B (v i) = β i • v i) :
    frobeniusNormSq (A - B) =
      ∑ i, ∑ j, ‖α i - β j‖ ^ 2 * eigenbasisOverlap u v i j := by
  rw [← sum_norm_apply_sq_eq_frobeniusNormSq (A - B) u]
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
      (∑ i, ‖α i - β (σ i)‖ ^ 2) ≤ frobeniusNormSq (A - B) := by
  obtain ⟨w, hw0, hwsum, hwM⟩ :=
    exists_eq_sum_perm_of_mem_doublyStochastic (eigenbasisOverlap_mem_doublyStochastic u v)
  have havg : ∑ σ, w σ * (∑ i, ‖α i - β (σ i)‖ ^ 2) = frobeniusNormSq (A - B) := by
    rw [frobeniusNormSq_eq_sum_overlap_mul_eigenvalueGap A B u v α β hA hB]
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
  have hlt : frobeniusNormSq (A - B) <
      ∑ σ, w σ * (∑ i, ‖α i - β (σ i)‖ ^ 2) := by
    rw [show frobeniusNormSq (A - B) = ∑ σ, w σ * frobeniusNormSq (A - B) by
      rw [← Finset.sum_mul, hwsum, one_mul]]
    refine Finset.sum_lt_sum ?_ ⟨σ₀, Finset.mem_univ _, ?_⟩
    · intro σ _
      exact mul_le_mul_of_nonneg_left (le_of_lt (hgt σ)) (hw0 σ)
    · exact mul_lt_mul_of_pos_left (hgt σ₀) hσ₀
  exact lt_irrefl _ (havg.symm ▸ hlt)

/-- **13.13**: the singular-value von Neumann trace inequality. -/
theorem norm_trace_adjoint_comp_le (A B : E →ₗ[𝕜] E) :
    ‖LinearMap.trace 𝕜 E (A.adjoint ∘ₗ B)‖ ≤
      ∑ i : Fin (finrank 𝕜 E), A.singularValues i * B.singularValues i := by
  sorry

/-- The rank-`k` SVD truncation, defined using TauCeti's canonical right singular basis. -/
def svdTruncation (A : E →ₗ[𝕜] F) (k : ℕ) : E →ₗ[𝕜] F :=
  ∑ i : Fin (finrank 𝕜 E), if i.val < k then
    (innerSL 𝕜 (A.rightSingularBasis i)).toLinearMap.smulRight
      (A (A.rightSingularBasis i)) else 0

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
private lemma svdTruncation_apply_rightSingularBasis (A : E →ₗ[𝕜] F) (k : ℕ)
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
private lemma sub_svdTruncation_apply_rightSingularBasis (A : E →ₗ[𝕜] F) (k : ℕ)
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
private lemma singularValues_sub_svdTruncation (A : E →ₗ[𝕜] F) (k i : ℕ) :
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
private lemma finrank_range_svdTruncation_le (A : E →ₗ[𝕜] F) (k : ℕ) :
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
theorem frobeniusNormSq_sub_svdTruncation (A : E →ₗ[𝕜] F) (k : ℕ) :
    frobeniusNormSq (A - svdTruncation A k) =
      ∑ i : Fin (finrank 𝕜 E), if k ≤ i.val then A.singularValues i ^ 2 else 0 := by
  unfold frobeniusNormSq
  simp_rw [singularValues_sub_svdTruncation]
  exact sum_singularValues_sq_shift A k

/-- The operator-norm error of SVD truncation, including the zero singular-value tail. -/
theorem norm_sub_svdTruncation (A : E →ₗ[𝕜] F) (k : ℕ) :
    ‖(A - svdTruncation A k).toContinuousLinearMap‖ = A.singularValues k := by
  -- The operator norm is the largest singular value, which is the first entry of the tail.
  rw [LinearMap.norm_toContinuousLinearMap_eq_singularValues_zero,
    singularValues_sub_svdTruncation, Nat.zero_add]

end CKMA
