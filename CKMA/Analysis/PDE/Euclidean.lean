/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.Distribution.TestFunction
public import Mathlib.Analysis.InnerProductSpace.Laplacian

/-!
# Euclidean differential expressions and smooth tests

Euclidean coordinates, compactly supported smooth tests, Hessian traces, divergence
and squared vector-gradient energy. Uniform ellipticity allows nonsymmetric coefficient
fields; nondivergence operators contract their coefficients with the Hessian.
The definitions use Mathlib's Euclidean spaces, distributional test functions, and the
orthonormal-basis Laplacian (`Mathlib.Analysis.Distribution.TestFunction` and
`Mathlib.Analysis.InnerProductSpace.Laplacian`). The smooth-test and identity-coefficient
adapters connect these expressions to `TestFunction` and that Laplacian.

## Main definitions

* `CKMA.euclideanUnitVector`, `CKMA.euclideanOpenBall`: coordinate unit vectors and centered
  open balls bundled as open sets.
* `CKMA.IsCompactSmoothTestOn`: smooth compactly supported test functions on a region.
* `CKMA.euclideanHessianTrace`, `CKMA.euclideanDivergence`, `CKMA.vectorGradientEnergy`:
  differential expressions in Euclidean coordinates.
* `CKMA.IsUniformlyEllipticOn`, `CKMA.nondivergencePrincipal`,
  `CKMA.linearEllipticExpression`: uniformly elliptic coefficient matrices, the nondivergence
  principal part, and the linear elliptic expression with drift and zeroth-order terms.

## Main results

* `CKMA.isCompactSmoothTestOn_iff_exists_testFunction`: on an open set, smooth compactly
  supported tests are exactly the underlying functions of Mathlib `TestFunction`s.
* `CKMA.nondivergencePrincipal_id`: the nondivergence principal part with identity
  coefficients equals the Euclidean Laplacian.
-/

public section

noncomputable section

namespace CKMA

open MeasureTheory
open scoped InnerProductSpace BigOperators

/-- The standard unit vector in a coordinate direction. -/
@[expose]
def euclideanUnitVector {d : ℕ} (i : Fin d) : EuclideanSpace ℝ (Fin d) := EuclideanSpace.single i 1

/-- A centered open ball bundled as an open set, for the weak Sobolev API. -/
@[expose]
def euclideanOpenBall (d : ℕ) (r : ℝ) : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d)) :=
  ⟨Metric.ball 0 r, Metric.isOpen_ball⟩

/-- Smooth compactly supported tests whose support lies in the indicated open region.
For open regions these are the unbundled version of Mathlib's test functions. -/
@[expose]
def IsCompactSmoothTestOn {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (Ω : Set E) (φ : E → F) : Prop :=
  ContDiff ℝ (↑(⊤ : ℕ∞)) φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ Ω

/-- Trace of a continuous bilinear form in Euclidean coordinates. -/
@[expose]
def euclideanHessianTrace {d : ℕ}
    (X : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) : ℝ :=
  ∑ i, X (euclideanUnitVector i) (euclideanUnitVector i)

/-- Pointwise divergence of a Euclidean vector field. -/
@[expose]
def euclideanDivergence {d : ℕ} (u : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∑ i, ⟪euclideanUnitVector i, fderiv ℝ u x (euclideanUnitVector i)⟫_ℝ

/-- Squared Hilbert–Schmidt norm of a vector-field derivative, used in viscous energy. -/
@[expose]
def vectorGradientEnergy {d : ℕ}
    (G : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∑ i, ‖G (euclideanUnitVector i)‖ ^ 2

/-- Bounded uniform ellipticity, without a symmetry assumption on the coefficient field. -/
@[expose]
def IsUniformlyEllipticOn {d : ℕ}
    (A : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (ell Λ : ℝ) (Ω : Set (EuclideanSpace ℝ (Fin d))) : Prop :=
  0 < ell ∧ ell ≤ Λ ∧ ∀ x ∈ Ω,
    (∀ v, ell * ‖v‖ ^ 2 ≤ ⟪v, A x v⟫_ℝ) ∧ ‖A x‖ ≤ Λ

/-- Nondivergence-form principal part, with the coefficient matrix contracted with the Hessian. -/
@[expose]
def nondivergencePrincipal {d : ℕ}
    (A : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (u : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∑ i, fderiv ℝ (fderiv ℝ u) x (euclideanUnitVector i) (A x (euclideanUnitVector i))

/-- Scalar linear elliptic expression including drift and zeroth order terms. -/
@[expose]
def linearEllipticExpression {d : ℕ}
    (A : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (c u : EuclideanSpace ℝ (Fin d) → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  nondivergencePrincipal A u x + fderiv ℝ u x (b x) + c x * u x

section DefiningLemmas

variable {d : ℕ}

/-- The coordinate unit vector is `EuclideanSpace.single i 1`. -/
theorem euclideanUnitVector_def (i : Fin d) :
    euclideanUnitVector i = EuclideanSpace.single i (1 : ℝ) := rfl

/-- Coordinates of a coordinate unit vector. -/
@[simp]
theorem euclideanUnitVector_apply (i j : Fin d) :
    euclideanUnitVector i j = if j = i then 1 else 0 := by
  simp [euclideanUnitVector, PiLp.single_apply]

/-- The bundled ball has the metric ball as underlying set. -/
@[simp]
theorem coe_euclideanOpenBall (r : ℝ) :
    (euclideanOpenBall d r : Set (EuclideanSpace ℝ (Fin d))) = Metric.ball 0 r := rfl

/-- Membership in the bundled centered ball. -/
@[simp]
theorem mem_euclideanOpenBall {r : ℝ} {x : EuclideanSpace ℝ (Fin d)} :
    x ∈ euclideanOpenBall d r ↔ ‖x‖ < r := by
  simp [euclideanOpenBall]

/-- Unfolding `IsCompactSmoothTestOn`. -/
theorem isCompactSmoothTestOn_iff {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {Ω : Set E} {φ : E → F} :
    IsCompactSmoothTestOn Ω φ ↔
      ContDiff ℝ (↑(⊤ : ℕ∞)) φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ Ω := Iff.rfl

/-- A smooth test is smooth. -/
theorem IsCompactSmoothTestOn.contDiff {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {Ω : Set E} {φ : E → F}
    (h : IsCompactSmoothTestOn Ω φ) : ContDiff ℝ (↑(⊤ : ℕ∞)) φ := h.1

/-- A smooth test has compact support. -/
theorem IsCompactSmoothTestOn.hasCompactSupport {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {Ω : Set E} {φ : E → F}
    (h : IsCompactSmoothTestOn Ω φ) : HasCompactSupport φ := h.2.1

/-- The support of a smooth test on `Ω` lies in `Ω`. -/
theorem IsCompactSmoothTestOn.tsupport_subset {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {Ω : Set E} {φ : E → F}
    (h : IsCompactSmoothTestOn Ω φ) : tsupport φ ⊆ Ω := h.2.2

/-- Unfolding the Hessian trace. -/
theorem euclideanHessianTrace_def
    (X : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) :
    euclideanHessianTrace X = ∑ i, X (euclideanUnitVector i) (euclideanUnitVector i) := rfl

/-- Unfolding the divergence. -/
theorem euclideanDivergence_def (u : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (x : EuclideanSpace ℝ (Fin d)) :
    euclideanDivergence u x =
      ∑ i, ⟪euclideanUnitVector i, fderiv ℝ u x (euclideanUnitVector i)⟫_ℝ := rfl

/-- Unfolding the squared Hilbert–Schmidt norm. -/
theorem vectorGradientEnergy_def (G : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
    vectorGradientEnergy G = ∑ i, ‖G (euclideanUnitVector i)‖ ^ 2 := rfl

/-- The squared Hilbert–Schmidt norm is nonnegative. -/
theorem vectorGradientEnergy_nonneg
    (G : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
    0 ≤ vectorGradientEnergy G :=
  Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

/-- Unfolding uniform ellipticity. -/
theorem isUniformlyEllipticOn_iff
    {A : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)}
    {ell Λ : ℝ} {Ω : Set (EuclideanSpace ℝ (Fin d))} :
    IsUniformlyEllipticOn A ell Λ Ω ↔
      0 < ell ∧ ell ≤ Λ ∧ ∀ x ∈ Ω, (∀ v, ell * ‖v‖ ^ 2 ≤ ⟪v, A x v⟫_ℝ) ∧ ‖A x‖ ≤ Λ :=
  Iff.rfl

/-- The coercivity bound of a uniformly elliptic coefficient field. -/
theorem IsUniformlyEllipticOn.coercive
    {A : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)}
    {ell Λ : ℝ} {Ω : Set (EuclideanSpace ℝ (Fin d))} (h : IsUniformlyEllipticOn A ell Λ Ω)
    {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ Ω) (v : EuclideanSpace ℝ (Fin d)) :
    ell * ‖v‖ ^ 2 ≤ ⟪v, A x v⟫_ℝ :=
  (h.2.2 x hx).1 v

/-- The operator-norm bound of a uniformly elliptic coefficient field. -/
theorem IsUniformlyEllipticOn.norm_le
    {A : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)}
    {ell Λ : ℝ} {Ω : Set (EuclideanSpace ℝ (Fin d))} (h : IsUniformlyEllipticOn A ell Λ Ω)
    {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ Ω) : ‖A x‖ ≤ Λ :=
  (h.2.2 x hx).2

/-- Uniform ellipticity passes to subsets. -/
theorem IsUniformlyEllipticOn.mono
    {A : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)}
    {ell Λ : ℝ} {Ω Ω' : Set (EuclideanSpace ℝ (Fin d))} (h : IsUniformlyEllipticOn A ell Λ Ω)
    (hΩ : Ω' ⊆ Ω) : IsUniformlyEllipticOn A ell Λ Ω' :=
  ⟨h.1, h.2.1, fun x hx ↦ h.2.2 x (hΩ hx)⟩

/-- Unfolding the nondivergence principal part. -/
theorem nondivergencePrincipal_def
    (A : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (u : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    nondivergencePrincipal A u x =
      ∑ i, fderiv ℝ (fderiv ℝ u) x (euclideanUnitVector i) (A x (euclideanUnitVector i)) := rfl

/-- Unfolding the linear elliptic expression. -/
theorem linearEllipticExpression_def
    (A : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (c u : EuclideanSpace ℝ (Fin d) → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) :
    linearEllipticExpression A b c u x =
      nondivergencePrincipal A u x + fderiv ℝ u x (b x) + c x * u x := rfl

end DefiningLemmas

/-- Smooth compact tests on an open set are exactly the underlying functions of Mathlib test
  functions. -/
theorem isCompactSmoothTestOn_iff_exists_testFunction {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Ω : TopologicalSpace.Opens E) (φ : E → F) :
    IsCompactSmoothTestOn Ω φ ↔ ∃ ψ : TestFunction Ω F ⊤, (ψ : E → F) = φ := by
  constructor
  · rintro ⟨hc, hs, ht⟩
    exact ⟨⟨φ, hc, hs, ht⟩, rfl⟩
  · rintro ⟨ψ, rfl⟩
    exact ⟨ψ.contDiff, ψ.hasCompactSupport, ψ.tsupport_subset⟩

/-- Identity coefficients recover Mathlib's Euclidean Laplacian. -/
theorem nondivergencePrincipal_id {d : ℕ} (u : EuclideanSpace ℝ (Fin d) → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) :
    nondivergencePrincipal (fun _ ↦ ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d))) u x =
      Laplacian.laplacian u x := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis u
    (EuclideanSpace.basisFun (Fin d) ℝ)]
  simp only [nondivergencePrincipal, ContinuousLinearMap.id_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp [euclideanUnitVector, iteratedFDeriv_two_apply]

end CKMA
