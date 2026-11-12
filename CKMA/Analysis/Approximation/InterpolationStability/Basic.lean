/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.Approximation.Polynomial
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Lebesgue constants for polynomial interpolation

Lagrange cardinal polynomials and the interpolant reuse Mathlib's `Lagrange.basis`
and `Lagrange.interpolate`. Their absolute sum is the Lebesgue function on `[-1,1]`,
and its supremum is the Lebesgue constant. Chebyshev extrema are the nodes
`cos(π i / n)`, with the zero-degree family totalized at `1`.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Polynomial
open scoped BigOperators

/-- Mathlib's Lagrange cardinal polynomial for all supplied nodes.
Distinctness is a hypothesis of interpolation theorems rather than of this definition. -/
abbrev lagrangeCardinalPolynomial {n : ℕ} (x : Fin n → ℝ) (i : Fin n) : ℝ[X] :=
  Lagrange.basis Finset.univ x i

/-- The absolute sum of cardinal polynomials at an evaluation point. -/
def lebesgueFunction {n : ℕ} (x : Fin n → ℝ) (t : ℝ) : ℝ :=
  ∑ i : Fin n, |(lagrangeCardinalPolynomial x i).eval t|

/-- The Lebesgue constant on `[-1,1]` for a specified finite node set. -/
def interpolationLebesgueConstant {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  sSup (lebesgueFunction x '' Set.Icc (-1 : ℝ) 1)

/-- The Chebyshev extrema, in decreasing order; `n=0` is harmlessly totalized at the point one. -/
def chebyshevExtremalNodes (n : ℕ) (i : Fin (n + 1)) : ℝ :=
  Real.cos (Real.pi * i.val / n)

/-- The polynomial interpolant at a supplied finite collection of interval nodes. -/
abbrev polynomialInterpolation {n : ℕ} (x : Fin n → Set.Icc (-1 : ℝ) 1)
    (f : ApproximationIntervalMap) : ℝ[X] :=
  Lagrange.interpolate Finset.univ (fun j ↦ (x j).1) (fun j ↦ f (x j))

end CKMA
