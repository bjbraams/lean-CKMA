/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.Distribution.TestFunction
public import TauCeti.Analysis.Sobolev.W1p.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# Euclidean differential expressions and smooth tests

Euclidean coordinates, compactly supported smooth tests, Hessian traces, divergence
and squared vector-gradient energy. Uniform ellipticity allows nonsymmetric coefficient
fields; nondivergence operators contract their coefficients with the Hessian.
The definitions use Mathlib's Euclidean spaces and Fréchet calculus and TauCeti's
weak-Sobolev infrastructure. The smooth-test and identity-coefficient adapters connect
these expressions to Mathlib's `TestFunction` and orthonormal-basis Laplacian APIs.
-/

@[expose] public section

noncomputable section

namespace CKMA

open MeasureTheory
open scoped InnerProductSpace BigOperators

/-- Real Euclidean space with an explicit spatial dimension. -/
abbrev EuclideanRealSpace (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The standard unit vector in a coordinate direction. -/
def euclideanUnitVector {d : ℕ} (i : Fin d) : EuclideanRealSpace d := EuclideanSpace.single i 1

/-- A centered open ball bundled as an open set, for the weak Sobolev API. -/
def euclideanOpenBall (d : ℕ) (r : ℝ) : TopologicalSpace.Opens (EuclideanRealSpace d) :=
  ⟨Metric.ball 0 r, Metric.isOpen_ball⟩

/-- Smooth compactly supported tests whose support lies in the indicated open region.
For open regions these are the unbundled version of Mathlib's test functions. -/
def IsCompactSmoothTestOn {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (Ω : Set E) (φ : E → F) : Prop :=
  ContDiff ℝ (↑(⊤ : ℕ∞)) φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ Ω

/-- Trace of a continuous bilinear form in Euclidean coordinates. -/
def euclideanHessianTrace {d : ℕ}
    (X : EuclideanRealSpace d →L[ℝ] EuclideanRealSpace d →L[ℝ] ℝ) : ℝ :=
  ∑ i, X (euclideanUnitVector i) (euclideanUnitVector i)

/-- Pointwise divergence of a Euclidean vector field. -/
def euclideanDivergence {d : ℕ} (u : EuclideanRealSpace d → EuclideanRealSpace d)
    (x : EuclideanRealSpace d) : ℝ :=
  ∑ i, ⟪euclideanUnitVector i, fderiv ℝ u x (euclideanUnitVector i)⟫_ℝ

/-- Squared Hilbert–Schmidt norm of a vector-field derivative, used in viscous energy. -/
def vectorGradientEnergy {d : ℕ} (G : EuclideanRealSpace d →L[ℝ] EuclideanRealSpace d) : ℝ :=
  ∑ i, ‖G (euclideanUnitVector i)‖ ^ 2

/-- Bounded uniform ellipticity, without a symmetry assumption on the coefficient field. -/
def IsUniformlyEllipticOn {d : ℕ}
    (A : EuclideanRealSpace d → EuclideanRealSpace d →L[ℝ] EuclideanRealSpace d)
    (ell Λ : ℝ) (Ω : Set (EuclideanRealSpace d)) : Prop :=
  0 < ell ∧ ell ≤ Λ ∧ ∀ x ∈ Ω,
    (∀ v, ell * ‖v‖ ^ 2 ≤ ⟪v, A x v⟫_ℝ) ∧ ‖A x‖ ≤ Λ

/-- Nondivergence-form principal part, with the coefficient matrix contracted with the Hessian. -/
def nondivergencePrincipal {d : ℕ}
    (A : EuclideanRealSpace d → EuclideanRealSpace d →L[ℝ] EuclideanRealSpace d)
    (u : EuclideanRealSpace d → ℝ) (x : EuclideanRealSpace d) : ℝ :=
  ∑ i, fderiv ℝ (fderiv ℝ u) x (euclideanUnitVector i) (A x (euclideanUnitVector i))

/-- Scalar linear elliptic expression including drift and zeroth order terms. -/
def linearEllipticExpression {d : ℕ}
    (A : EuclideanRealSpace d → EuclideanRealSpace d →L[ℝ] EuclideanRealSpace d)
    (b : EuclideanRealSpace d → EuclideanRealSpace d) (c u : EuclideanRealSpace d → ℝ)
    (x : EuclideanRealSpace d) : ℝ :=
  nondivergencePrincipal A u x + fderiv ℝ u x (b x) + c x * u x


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
theorem nondivergencePrincipal_id {d : ℕ} (u : EuclideanRealSpace d → ℝ)
    (x : EuclideanRealSpace d) :
    nondivergencePrincipal (fun _ ↦ ContinuousLinearMap.id ℝ (EuclideanRealSpace d)) u x =
      Laplacian.laplacian u x := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis u (EuclideanSpace.basisFun (Fin
    d) ℝ)]
  simp only [nondivergencePrincipal, ContinuousLinearMap.id_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp [euclideanUnitVector, iteratedFDeriv_two_apply]

end CKMA
