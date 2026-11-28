/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Restricted isometry and stable sparse recovery

Coordinate sparsity and the finite coordinate l1 norm describe best sparse approximation
and basis-pursuit minimizers. A restricted isometry bound at order twice the sparsity
gives a dimension-independent recovery estimate, with constants depending only on the
isometry bound below `√2 - 1`.

Source: GAPS 29.68.

## Main definitions

* `CKMA.coordinateOneNorm`: the finite coordinate `ℓ¹` norm.
* `CKMA.IsCoordinateSparse`: coordinate sparsity of a finite vector.
* `CKMA.bestSparseOneError`: best `s`-term `ℓ¹` approximation error.
* `CKMA.HasRestrictedIsometryBound`: restricted isometry property with explicit bound.
* `CKMA.IsBasisPursuitMinimizer`: feasibility and `ℓ¹` minimality for basis pursuit.

## Main results

* `CKMA.coordinateOneNorm_def`, `CKMA.isCoordinateSparse_iff`, `CKMA.bestSparseOneError_def`,
  `CKMA.hasRestrictedIsometryBound_iff`, `CKMA.isBasisPursuitMinimizer_iff`: defining lemmas.
* `CKMA.isCoordinateSparse_zero`: the zero vector is sparse at every order.
* `CKMA.restricted_isometry_stable_recovery`: stable basis-pursuit recovery below `√2 - 1`.
-/

public section

noncomputable section

namespace CKMA

open scoped BigOperators

/-- The finite coordinate l1 norm, given by the sum of the coordinate norms. -/
@[expose]
def coordinateOneNorm {ι α : Type*} [Fintype ι] [Norm α] (x : ι → α) : ℝ :=
  ∑ i, ‖x i‖

/-- Coordinate sparsity, including the zero vector at sparsity zero. -/
@[expose]
def IsCoordinateSparse {ι α : Type*} [Fintype ι] [Zero α] (s : ℕ) (x : ι → α) : Prop := by
  classical
  exact (Finset.univ.filter (fun i ↦ x i ≠ 0)).card ≤ s

/-- The best s-term l1 approximation error. -/
@[expose]
def bestSparseOneError {𝕜 : Type*} [RCLike 𝕜] {N : ℕ} (s : ℕ)
    (x : EuclideanSpace 𝕜 (Fin N)) : ℝ :=
  sInf {r | ∃ z : EuclideanSpace 𝕜 (Fin N),
    IsCoordinateSparse s z ∧ r = coordinateOneNorm (x - z)}

/-- Restricted isometry with an explicit admissible bound; the infimal constant is unnecessary
in recovery statements, which can use any valid bound below the threshold. -/
@[expose]
def HasRestrictedIsometryBound {𝕜 : Type*} [RCLike 𝕜] {m N : ℕ}
    (A : EuclideanSpace 𝕜 (Fin N) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin m)) (s : ℕ) (δ : ℝ) : Prop :=
  0 ≤ δ ∧ ∀ x : EuclideanSpace 𝕜 (Fin N), IsCoordinateSparse s x →
    (1 - δ) * ‖x‖ ^ 2 ≤ ‖A x‖ ^ 2 ∧ ‖A x‖ ^ 2 ≤ (1 + δ) * ‖x‖ ^ 2

/-- Basis-pursuit feasibility and minimality in the actual l1 objective. -/
@[expose]
def IsBasisPursuitMinimizer {𝕜 : Type*} [RCLike 𝕜] {m N : ℕ}
    (A : EuclideanSpace 𝕜 (Fin N) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin m))
    (y : EuclideanSpace 𝕜 (Fin m)) (η : ℝ) (z : EuclideanSpace 𝕜 (Fin N)) : Prop :=
  ‖A z - y‖ ≤ η ∧ ∀ w, ‖A w - y‖ ≤ η → coordinateOneNorm z ≤ coordinateOneNorm w

/-- The coordinate `ℓ¹` norm is the sum of the coordinate norms. -/
lemma coordinateOneNorm_def {ι α : Type*} [Fintype ι] [Norm α] (x : ι → α) :
    coordinateOneNorm x = ∑ i, ‖x i‖ :=
  rfl

/-- A vector is `s`-sparse when at most `s` coordinates are nonzero. -/
lemma isCoordinateSparse_iff {ι α : Type*} [Fintype ι] [Zero α] {s : ℕ} {x : ι → α}
    [DecidablePred (fun i ↦ x i ≠ 0)] :
    IsCoordinateSparse s x ↔ (Finset.univ.filter (fun i ↦ x i ≠ 0)).card ≤ s := by
  unfold IsCoordinateSparse
  convert Iff.rfl

/-- The best `s`-term error is the infimum of the `ℓ¹` distances to `s`-sparse vectors. -/
lemma bestSparseOneError_def {𝕜 : Type*} [RCLike 𝕜] {N : ℕ} (s : ℕ)
    (x : EuclideanSpace 𝕜 (Fin N)) :
    bestSparseOneError s x = sInf {r | ∃ z : EuclideanSpace 𝕜 (Fin N),
      IsCoordinateSparse s z ∧ r = coordinateOneNorm (x - z)} :=
  rfl

/-- Characterization of a restricted isometry bound. -/
lemma hasRestrictedIsometryBound_iff {𝕜 : Type*} [RCLike 𝕜] {m N : ℕ}
    {A : EuclideanSpace 𝕜 (Fin N) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin m)} {s : ℕ} {δ : ℝ} :
    HasRestrictedIsometryBound A s δ ↔ 0 ≤ δ ∧ ∀ x : EuclideanSpace 𝕜 (Fin N),
      IsCoordinateSparse s x →
        (1 - δ) * ‖x‖ ^ 2 ≤ ‖A x‖ ^ 2 ∧ ‖A x‖ ^ 2 ≤ (1 + δ) * ‖x‖ ^ 2 :=
  Iff.rfl

/-- Characterization of a basis-pursuit minimizer. -/
lemma isBasisPursuitMinimizer_iff {𝕜 : Type*} [RCLike 𝕜] {m N : ℕ}
    {A : EuclideanSpace 𝕜 (Fin N) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin m)}
    {y : EuclideanSpace 𝕜 (Fin m)} {η : ℝ} {z : EuclideanSpace 𝕜 (Fin N)} :
    IsBasisPursuitMinimizer A y η z ↔
      ‖A z - y‖ ≤ η ∧ ∀ w, ‖A w - y‖ ≤ η → coordinateOneNorm z ≤ coordinateOneNorm w :=
  Iff.rfl

/-- The zero vector is sparse at every order. -/
theorem isCoordinateSparse_zero {ι α : Type*} [Fintype ι] [Zero α] {s : ℕ} :
    IsCoordinateSparse s (0 : ι → α) := by
  simp [IsCoordinateSparse]

/-- **29.68**: stable basis-pursuit recovery below the classical sqrt(2)-1 RIP threshold.
The constants depend on delta only, uniformly in dimensions, sample data and sparsity. -/
theorem restricted_isometry_stable_recovery {𝕜 : Type*} [RCLike 𝕜] {δ : ℝ}
    (hδsmall : δ < Real.sqrt 2 - 1) :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∀ (m N s : ℕ), 0 < s →
      ∀ (A : EuclideanSpace 𝕜 (Fin N) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin m)),
      HasRestrictedIsometryBound A (2 * s) δ →
      ∀ (x z : EuclideanSpace 𝕜 (Fin N)) (y : EuclideanSpace 𝕜 (Fin m)) (η : ℝ), 0 ≤ η →
      ‖A x - y‖ ≤ η → IsBasisPursuitMinimizer A y η z →
        ‖x - z‖ ≤ C * bestSparseOneError s x / Real.sqrt s + D * η := by
  sorry

end CKMA
