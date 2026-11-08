/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.Polynomial.Basic
public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Algebra.Polynomial.Roots

/-!
# Orthogonal polynomial roots and Gaussian quadrature

Finite absolute moments give integrability of polynomial expressions. A nonzero
orthogonal polynomial for an infinite-support measure has distinct simple real roots
inside the convex support. An orthonormal polynomial family determines a unique
positive Gaussian quadrature rule at these roots, exact through degree `2n-1`, with
weights given by the reciprocal diagonal Christoffel kernel.

Sources: GAPS 48.6 and 48.14.
-/

@[expose] public section

noncomputable section

namespace CKMA

open MeasureTheory Polynomial
open scoped BigOperators

/-- All polynomial moments are absolutely integrable. -/
def HasFiniteMoments (μ : Measure ℝ) : Prop := ∀ n : ℕ, Integrable (fun x ↦ x ^ n) μ

/-- Finite absolute moments include integrability of the constant function one. -/
theorem HasFiniteMoments.isFiniteMeasure {μ : Measure ℝ} (hm : HasFiniteMoments μ) :
    IsFiniteMeasure μ := by
  have h := hm 0
  simp only [pow_zero] at h
  exact (integrable_const_iff_isFiniteMeasure (by norm_num : (1 : ℝ) ≠ 0)).mp h

/-- A nonzero polynomial orthogonal to all polynomials of smaller degree.
Integrability is supplied separately by the moment hypothesis. -/
def IsOrthogonalPolynomial (μ : Measure ℝ) (p : ℝ[X]) : Prop :=
  p ≠ 0 ∧ ∀ q : ℝ[X], q.natDegree < p.natDegree → ∫ x, p.eval x * q.eval x ∂μ = 0

/-- **48.6**: the roots are all real, distinct, interior to the convex support, and simple. -/
theorem roots_orthogonalPolynomial (μ : Measure ℝ) (hm : HasFiniteMoments μ)
    (hi : μ.support.Infinite) {p : ℝ[X]} (hp : IsOrthogonalPolynomial μ p) :
    p.roots.toFinset.card = p.natDegree ∧ ∀ x ∈ p.roots,
      x ∈ interior (convexHull ℝ μ.support) ∧ p.rootMultiplicity x = 1 := by
  sorry

/-- Exactness of a quadrature rule through a specified polynomial degree. -/
def IsQuadratureRule {n : ℕ} (μ : Measure ℝ) (x w : Fin n → ℝ) (degree : ℕ) : Prop :=
  ∀ p : ℝ[X], p.natDegree ≤ degree → ∫ t, p.eval t ∂μ = ∑ j, w j * p.eval (x j)

/-- The finite Christoffel kernel of an orthonormal polynomial system. -/
def christoffelKernel (p : ℕ → ℝ[X]) (n : ℕ) (x y : ℝ) : ℝ :=
  ∑ j ∈ Finset.range n, (p j).eval x * (p j).eval y

/-- **48.14**: the Gaussian rule at the roots is unique, positive, and has Christoffel weights.
The family is orthonormal, so no squared-norm factors are omitted from the kernel. -/
theorem existsUnique_gaussQuadrature (μ : Measure ℝ) (hm : HasFiniteMoments μ)
    (hi : μ.support.Infinite) (p : ℕ → ℝ[X]) (hd : ∀ j, (p j).natDegree = j)
    (ho : ∀ j k, ∫ x, (p j).eval x * (p k).eval x ∂μ = if j = k then 1 else 0)
    {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) (hx : Function.Injective x)
    (hroot : ∀ j, (p n).eval (x j) = 0) :
    ∃! w : Fin n → ℝ, IsQuadratureRule μ x w (2 * n - 1) ∧
      (∀ j, 0 < w j) ∧ ∀ j, w j = (christoffelKernel p n (x j) (x j))⁻¹ := by
  sorry

end CKMA
