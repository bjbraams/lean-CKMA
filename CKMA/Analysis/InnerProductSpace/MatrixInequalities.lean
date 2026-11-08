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

/-!
# Hermitian eigenvalues, singular values, and low-rank approximation

Sorted Hermitian eigenvalues are indexed from zero. Compression and rank perturbation statements
use the corresponding index shifts; Weyl's additive bound uses the output index `i+j`.
Hoffman–Wielandt is formulated in supplied orthonormal eigenbases, allowing repeated eigenvalues.

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

/-- **13.7**: Cauchy interlacing for a codimension-one compression. -/
theorem cauchy_interlacing (A : E →ₗ[𝕜] E) (hA : A.IsSymmetric)
    (V : F →ₗᵢ[𝕜] E) (hdim : finrank 𝕜 E = finrank 𝕜 F + 1)
    (i : Fin (finrank 𝕜 F)) (j k : Fin (finrank 𝕜 E))
    (hj : j.val = i.val) (hk : k.val = i.val + 1) :
    orderedEigenvalues A hA k ≤ orderedEigenvalues (hermitianCompression A V)
      (isSymmetric_hermitianCompression A hA V) i ∧
      orderedEigenvalues (hermitianCompression A V) (isSymmetric_hermitianCompression A hA V) i ≤
        orderedEigenvalues A hA j := by
  sorry

/-- The corresponding index-shift interlacing bounds for a rank-at-most-`r` perturbation. -/
theorem eigenvalue_rank_perturbation (A B : E →ₗ[𝕜] E) (hA : A.IsSymmetric)
    (hB : B.IsSymmetric) {r : ℕ} (hr : finrank 𝕜 (LinearMap.range (A - B)) ≤ r)
    (i j : Fin (finrank 𝕜 E)) (hj : j.val = i.val + r) :
    orderedEigenvalues A hA j ≤ orderedEigenvalues B hB i ∧
      orderedEigenvalues B hB j ≤ orderedEigenvalues A hA i := by
  sorry

/-- **13.8**: the mixed-index Weyl inequality. Indices start at zero, so the output index is `i+j`.
  -/
theorem weyl_eigenvalue_add (A B : E →ₗ[𝕜] E) (hA : A.IsSymmetric)
    (hB : B.IsSymmetric)
    (i j k : Fin (finrank 𝕜 E)) (hk : k.val = i.val + j.val) :
    orderedEigenvalues (A + B) (hA.add hB) k ≤ orderedEigenvalues A hA i +
      orderedEigenvalues B hB j := by
  sorry

/-- **13.10**: Hoffman–Wielandt in supplied orthonormal eigenbases.
Over complex scalars such bases exist by TauCeti's normal spectral theorem. The supplied-basis
form also applies over real scalars; repeated eigenvalues are allowed. -/
theorem hoffman_wielandt (A B : E →ₗ[𝕜] E)
    (u v : OrthonormalBasis (Fin (finrank 𝕜 E)) 𝕜 E)
    (α β : Fin (finrank 𝕜 E) → 𝕜)
    (hA : ∀ i, A (u i) = α i • u i) (hB : ∀ i, B (v i) = β i • v i) :
    ∃ σ : Equiv.Perm (Fin (finrank 𝕜 E)),
      (∑ i, ‖α i - β (σ i)‖ ^ 2) ≤ frobeniusNormSq (A - B) := by
  sorry

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

/-- **13.18**: SVD truncation is best in every unitarily invariant seminorm. -/
theorem svdTruncation_minimizes (A : E →ₗ[𝕜] F) (k : ℕ)
    (N : TauCeti.UnitarilyInvariantSeminorm 𝕜 E F) :
    finrank 𝕜 (LinearMap.range (svdTruncation A k)) ≤ k ∧
      ∀ B : E →ₗ[𝕜] F, finrank 𝕜 (LinearMap.range B) ≤ k →
        N (A - svdTruncation A k) ≤ N (A - B) := by
  sorry

/-- The squared Frobenius error is the singular-value square tail. -/
theorem frobeniusNormSq_sub_svdTruncation (A : E →ₗ[𝕜] F) (k : ℕ) :
    frobeniusNormSq (A - svdTruncation A k) =
      ∑ i : Fin (finrank 𝕜 E), if k ≤ i.val then A.singularValues i ^ 2 else 0 := by
  sorry


/-- The operator-norm error of SVD truncation, including the zero singular-value tail. -/
theorem norm_sub_svdTruncation (A : E →ₗ[𝕜] F) (k : ℕ) :
    ‖(A - svdTruncation A k).toContinuousLinearMap‖ = A.singularValues k := by
  sorry

end CKMA
