/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.Approximation.Polynomial
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Polynomial interpolation and Lebesgue constants

Lagrange cardinal polynomials and interpolation reuse Mathlib's `Lagrange.basis` and
`Lagrange.interpolate`. Their absolute sum defines the Lebesgue function on `[-1,1]`.
Chebyshev extrema have Lebesgue constants `(2/π) log(n+1) + O(1)`, and the Lebesgue
constant controls interpolation error by the best uniform polynomial approximation error.
The estimate uses Mathlib's polynomial reproduction theorem `Lagrange.eq_interpolate`
and compact supremum bounds, without assuming that a best approximant is attained.

Source: GAPS 47.35.
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

/-- **47.35**, asymptotic clause: the Chebyshev-extrema Lebesgue constants equal
`(2/π) log n + O(1)`. Using `log(n+1)` includes the zero-degree convention. -/
theorem chebyshev_lebesgueConstant_log_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
    |interpolationLebesgueConstant (chebyshevExtremalNodes n) -
      (2 / Real.pi) * Real.log (n + 1)| ≤ C := by
  sorry

/-- The Lebesgue function of a finite node family is continuous. -/
theorem continuous_lebesgueFunction {n : ℕ} (x : Fin n → ℝ) :
    Continuous (lebesgueFunction x) := by
  exact continuous_finsetSum _ fun i _ ↦ (lagrangeCardinalPolynomial x i).continuous.abs

/-- The interval Lebesgue constant bounds the Lebesgue function at each interval point. -/
theorem lebesgueFunction_le_interpolationLebesgueConstant {n : ℕ} (x : Fin n → ℝ)
    {t : ℝ} (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    lebesgueFunction x t ≤ interpolationLebesgueConstant x :=
  le_csSup
    (isCompact_Icc.bddAbove_image (continuous_lebesgueFunction x).continuousOn)
    ⟨t, ht, rfl⟩

/-- A finite node family's interval Lebesgue constant is nonnegative. -/
theorem interpolationLebesgueConstant_nonneg {n : ℕ} (x : Fin n → ℝ) :
    0 ≤ interpolationLebesgueConstant x := by
  have h0 : 0 ≤ lebesgueFunction x 0 := Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  exact h0.trans
    (lebesgueFunction_le_interpolationLebesgueConstant x (by norm_num))

/-- The interpolation error is bounded by one plus the Lebesgue constant times the
error of every admissible comparison polynomial. -/
theorem interpolation_error_le_polynomial_error {n : ℕ}
    (x : Fin (n + 1) → Set.Icc (-1 : ℝ) 1)
    (hx : Function.Injective (fun i ↦ (x i).1)) (f : ApproximationIntervalMap)
    (q : ℝ[X]) (hq : q.natDegree ≤ n) :
    ‖f - polynomialOnApproximationInterval (polynomialInterpolation x f)‖ ≤
      (1 + interpolationLebesgueConstant (fun i ↦ (x i).1)) *
        ‖f - polynomialOnApproximationInterval q‖ := by
  let v := fun i ↦ (x i).1
  let E := ‖f - polynomialOnApproximationInterval q‖
  have hdeg : q.degree < ((Finset.univ : Finset (Fin (n + 1))).card : WithBot ℕ) := by
    simp only [Finset.card_univ, Fintype.card_fin]
    exact lt_of_le_of_lt q.degree_le_natDegree (by exact_mod_cast Nat.lt_succ_of_le hq)
  have hIq := Lagrange.eq_interpolate (v := v) (s := Finset.univ) hx.injOn hdeg
  have heval (r : Fin (n + 1) → ℝ) (t : ℝ) :
      (Lagrange.interpolate Finset.univ v r).eval t =
        ∑ i, r i * (lagrangeCardinalPolynomial v i).eval t := by
    simp only [Lagrange.interpolate_apply, Polynomial.eval_finsetSum,
      Polynomial.eval_mul, Polynomial.eval_C, lagrangeCardinalPolynomial]
  have herr : ∀ t : Set.Icc (-1 : ℝ) 1, ‖f t - q.eval t.1‖ ≤ E := by
    intro t
    exact (f - polynomialOnApproximationInterval q).norm_coe_le_norm t
  let : Nonempty (Set.Icc (-1 : ℝ) 1) := ⟨x 0⟩
  apply (ContinuousMap.norm_le_of_nonempty _).mpr
  intro t
  change ‖f t - (polynomialInterpolation x f).eval t.1‖ ≤ _
  have hIf := heval (fun i ↦ f (x i)) t.1
  have hqeval : q.eval t.1 = ∑ i, q.eval (v i) *
      (lagrangeCardinalPolynomial v i).eval t.1 := by
    exact (congrArg (Polynomial.eval t.1) hIq).trans (heval _ _)
  have hdiff : (polynomialInterpolation x f).eval t.1 - q.eval t.1 =
      ∑ i, (f (x i) - q.eval (v i)) * (lagrangeCardinalPolynomial v i).eval t.1 := by
    rw [hIf, hqeval, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  calc ‖f t - (polynomialInterpolation x f).eval t.1‖ =
      ‖(f t - q.eval t.1) -
        ∑ i, (f (x i) - q.eval (v i)) * (lagrangeCardinalPolynomial v i).eval t.1‖ := by
        congr 1
        rw [← hdiff]
        ring
    _ ≤ ‖f t - q.eval t.1‖ +
        ‖∑ i, (f (x i) - q.eval (v i)) * (lagrangeCardinalPolynomial v i).eval t.1‖ :=
      norm_sub_le _ _
    _ ≤ E + ∑ i, E * ‖(lagrangeCardinalPolynomial v i).eval t.1‖ := by
      apply add_le_add (herr t)
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (herr (x i)) (norm_nonneg _)
    _ = (1 + lebesgueFunction v t.1) * E := by
      simp only [lebesgueFunction, ← Finset.mul_sum, Real.norm_eq_abs]
      ring
    _ ≤ (1 + interpolationLebesgueConstant v) * E :=
      mul_le_mul_of_nonneg_right
        (add_le_add (le_refl (1 : ℝ))
          (lebesgueFunction_le_interpolationLebesgueConstant v t.property)) (norm_nonneg _)

/-- Lebesgue's near-best interpolation estimate for arbitrary distinct interval nodes. -/
theorem interpolation_error_le {n : ℕ} (x : Fin (n + 1) → Set.Icc (-1 : ℝ) 1)
    (hx : Function.Injective (fun i ↦ (x i).1)) (f : ApproximationIntervalMap) :
    ‖f - polynomialOnApproximationInterval (polynomialInterpolation x f)‖ ≤
      (1 + interpolationLebesgueConstant (fun i ↦ (x i).1)) * bestPolynomialError f n := by
  have hC : 0 < 1 + interpolationLebesgueConstant (fun i ↦ (x i).1) :=
    lt_of_lt_of_le zero_lt_one
      (le_add_of_nonneg_right (interpolationLebesgueConstant_nonneg _))
  rw [mul_comm]
  apply (div_le_iff₀ hC).mp
  apply le_csInf
  · exact ⟨‖f - polynomialOnApproximationInterval 0‖, 0, by simp, rfl⟩
  · rintro r ⟨q, hq, rfl⟩
    apply (div_le_iff₀ hC).mpr
    simpa only [mul_comm] using interpolation_error_le_polynomial_error x hx f q hq

end CKMA
