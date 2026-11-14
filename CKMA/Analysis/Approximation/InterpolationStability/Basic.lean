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

## Main definitions

* `CKMA.lagrangeCardinalPolynomial`: Lagrange cardinal polynomial for a finite node family.
* `CKMA.lebesgueFunction`: absolute sum of cardinal polynomials at an evaluation point.
* `CKMA.interpolationLebesgueConstant`: supremum of the Lebesgue function on `[-1, 1]`.
* `CKMA.chebyshevExtremalNodes`: Chebyshev extremal nodes `cos (π i / n)`.
* `CKMA.polynomialInterpolation`: Lagrange polynomial interpolant on `[-1, 1]`.
* `CKMA.chebyshevExtremalWeight`: endpoint weight `2` and interior weight `1`.
* `CKMA.nodeAngle`: angular coordinate `π i / n` of an extremal node.
* `CKMA.chebyshevLebesgueSlack`: slack constant in the Chebyshev–Lebesgue asymptotic.

## Main results

* `CKMA.abs_derivative_chebyshevExtremalNodal`: absolute derivative of the nodal polynomial at
  each Chebyshev extremal node.
* `CKMA.lebesgueFunction_chebyshev_node`: the Lebesgue function equals `1` at each extremal node.

## Notation

No new notation is introduced in this file.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Polynomial Real Polynomial.Chebyshev Finset Classical Lagrange
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

/-- Endpoint weight two, and weight one at every interior extremal node. -/
def chebyshevExtremalWeight (n : ℕ) (i : Fin (n + 1)) : ℝ :=
  if i.val = 0 ∨ i.val = n then 2 else 1

/-- Every extremal weight is at least one. -/
lemma one_le_chebyshevExtremalWeight (n : ℕ) (i : Fin (n + 1)) :
    1 ≤ chebyshevExtremalWeight n i := by
  unfold chebyshevExtremalWeight
  split_ifs <;> norm_num

/-- Every extremal weight is positive. -/
lemma chebyshevExtremalWeight_pos (n : ℕ) (i : Fin (n + 1)) :
    0 < chebyshevExtremalWeight n i :=
  lt_of_lt_of_le zero_lt_one (one_le_chebyshevExtremalWeight n i)

/-- Angular coordinate of an extremal node. Division by zero is unused for `n = 0`. -/
def nodeAngle (n : ℕ) (i : Fin (n + 1)) : ℝ :=
  π * (i.val : ℝ) / n

/-- Extremal nodes are the cosines of equally spaced angles. -/
lemma chebyshevExtremalNodes_eq_cos (n : ℕ) (i : Fin (n + 1)) :
    chebyshevExtremalNodes n i = cos (nodeAngle n i) := rfl

/-- Node angles of a positive degree lie in `[0, π]`. -/
lemma nodeAngle_mem_Icc {n : ℕ} (hn : n ≠ 0) (i : Fin (n + 1)) :
    nodeAngle n i ∈ Set.Icc 0 π := by
  unfold nodeAngle
  refine ⟨div_nonneg (mul_nonneg pi_pos.le (Nat.cast_nonneg _)) (Nat.cast_nonneg _), ?_⟩
  have hi : (i.val : ℝ) ≤ n := by exact_mod_cast Nat.le_of_lt_succ i.isLt
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  rw [div_le_iff₀ hn0]
  simpa [mul_comm, mul_assoc] using mul_le_mul_of_nonneg_left hi pi_pos.le

/-- Distinct indices give distinct extremal nodes. -/
lemma chebyshevExtremalNodes_injective {n : ℕ} (hn : n ≠ 0) :
    Function.Injective (chebyshevExtremalNodes n) := by
  intro i j hij
  have hang :=
    (strictAntiOn_cos.injOn.eq_iff (nodeAngle_mem_Icc hn i) (nodeAngle_mem_Icc hn j)).mp
      (by simpa [chebyshevExtremalNodes_eq_cos] using hij)
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hval : (i.val : ℝ) = j.val := by
    unfold nodeAngle at hang
    field_simp at hang
    linarith
  exact Fin.ext (by exact_mod_cast hval)

/-- The integer `n - 1`, shifted by one, recovers `n`. -/
lemma chebyshevIndex_add_one {n : ℕ} (hn : 1 ≤ n) :
    ((n - 1 : ℕ) : ℤ) + 1 = (n : ℤ) := by
  exact_mod_cast (Nat.sub_add_cancel hn : (n - 1) + 1 = n)

/-- The polynomial `(1 - X ^ 2) U_{n-1}`, vanishing on the extremal nodes. -/
def chebyshevExtremalNodal (n : ℕ) : ℝ[X] :=
  (1 - X ^ 2) * U ℝ ((n - 1 : ℕ) : ℤ)

/-- Trigonometric evaluation of the extremal nodal polynomial. -/
lemma eval_chebyshevExtremalNodal {n : ℕ} (hn : 1 ≤ n) (θ : ℝ) :
    (chebyshevExtremalNodal n).eval (cos θ) = sin θ * sin ((n : ℝ) * θ) := by
  unfold chebyshevExtremalNodal
  rw [eval_mul, eval_sub, eval_one, eval_pow, eval_X]
  have hsq : (1 : ℝ) - cos θ ^ 2 = sin θ ^ 2 := by
    rw [← sin_sq_add_cos_sq θ]
    ring
  rw [hsq]
  have hU := U_real_cos θ ((n - 1 : ℕ) : ℤ)
  have hcast : ((((n - 1 : ℕ) : ℤ) : ℝ) + 1) * θ = (n : ℝ) * θ := by
    rw [show (((n - 1 : ℕ) : ℤ) : ℝ) + 1 = (n : ℝ) by
      exact_mod_cast chebyshevIndex_add_one hn]
  calc
      sin θ ^ 2 * (U ℝ ((n - 1 : ℕ) : ℤ)).eval (cos θ)
        = sin θ * ((U ℝ ((n - 1 : ℕ) : ℤ)).eval (cos θ) * sin θ) := by ring
    _ = sin θ * sin ((((n - 1 : ℕ) : ℤ) + 1) * θ) := by rw [hU]
    _ = sin θ * sin ((n : ℝ) * θ) := by rw [hcast]

/-- The extremal nodal polynomial has degree `n + 1`. -/
lemma natDegree_chebyshevExtremalNodal {n : ℕ} (hn : 1 ≤ n) :
    (chebyshevExtremalNodal n).natDegree = n + 1 := by
  unfold chebyshevExtremalNodal
  have hlin : natDegree (1 - X ^ 2 : ℝ[X]) = 2 := by
    have hlt : natDegree (1 : ℝ[X]) < natDegree (X ^ 2 : ℝ[X]) := by simp
    simpa using natDegree_sub_eq_right_of_natDegree_lt hlt
  have hUdeg : natDegree (U ℝ ((n - 1 : ℕ) : ℤ)) = n - 1 := by
    rw [natDegree_U, chebyshevIndex_add_one hn, Int.natAbs_natCast]
  have hlin0 : (1 - X ^ 2 : ℝ[X]) ≠ 0 := by
    intro h
    have := congrArg natDegree h
    simp [hlin, natDegree_zero] at this
  have hU0 : U ℝ ((n - 1 : ℕ) : ℤ) ≠ 0 :=
    U_ne_zero ℝ _ (by
      intro h
      have hnonneg : (0 : ℤ) ≤ ((n - 1 : ℕ) : ℤ) := Int.natCast_nonneg _
      rw [h] at hnonneg
      norm_num at hnonneg)
  rw [natDegree_mul hlin0 hU0, hlin, hUdeg]
  omega

/-- Derivative of `1 - X ^ 2`. -/
lemma derivative_one_sub_X_sq : derivative (1 - X ^ 2 : ℝ[X]) = C (-2) * X := by
  rw [derivative_sub, derivative_one, derivative_X_pow]
  simp

/-- Absolute derivative of the nodal polynomial at each extremal node. -/
lemma abs_derivative_chebyshevExtremalNodal {n : ℕ} (hn : 1 ≤ n)
    (i : Fin (n + 1)) :
    |(chebyshevExtremalNodal n).derivative.eval (chebyshevExtremalNodes n i)| =
      (n : ℝ) * chebyshevExtremalWeight n i := by
  have hn0 : n ≠ 0 := by omega
  have hder : (chebyshevExtremalNodal n).derivative =
      derivative (1 - X ^ 2 : ℝ[X]) * U ℝ ((n - 1 : ℕ) : ℤ) +
        (1 - X ^ 2) * derivative (U ℝ ((n - 1 : ℕ) : ℤ)) := by
    simp [chebyshevExtremalNodal, derivative_mul]
  have hcastR : (((n - 1 : ℕ) : ℤ) : ℝ) + 1 = (n : ℝ) := by
    exact_mod_cast chebyshevIndex_add_one hn
  by_cases h0 : i.val = 0
  · have ha : chebyshevExtremalNodes n i = 1 := by
      simp [chebyshevExtremalNodes, h0, cos_zero]
    have hφ' : (chebyshevExtremalNodal n).derivative.eval 1 = -(2 * (n : ℝ)) := by
      rw [hder, eval_add, eval_mul, eval_mul, derivative_one_sub_X_sq]
      have hv : (1 - X ^ 2 : ℝ[X]).eval 1 = 0 := by simp
      simp only [hv, eval_mul, eval_C, eval_X, U_eval_one, hcastR]
      ring
    have hw : chebyshevExtremalWeight n i = 2 := by
      simp [chebyshevExtremalWeight, h0]
    rw [ha, hφ', hw, abs_neg, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      abs_of_nonneg (Nat.cast_nonneg n)]
    ring
  · by_cases hnI : i.val = n
    · have ha : chebyshevExtremalNodes n i = -1 := by
        have hdiv : (n : ℝ) ≠ 0 := by exact_mod_cast hn0
        simp only [chebyshevExtremalNodes, hnI]
        rw [mul_div_cancel_right₀ _ hdiv, cos_pi]
      have hφ' : (chebyshevExtremalNodal n).derivative.eval (-1) =
          2 * (((n - 1 : ℕ) : ℤ).negOnePow : ℝ) * (n : ℝ) := by
        rw [hder, eval_add, eval_mul, eval_mul, derivative_one_sub_X_sq]
        have hv : (1 - X ^ 2 : ℝ[X]).eval (-1) = 0 := by simp
        simp only [hv, eval_mul, eval_C, eval_X, U_eval_neg_one]
        rw [hcastR]
        ring
      have hsign : |(((n - 1 : ℕ) : ℤ).negOnePow : ℝ)| = 1 := by
        rcases Int.even_or_odd ((n - 1 : ℕ) : ℤ) with h | h
        · rw [Int.negOnePow_even _ h]
          simp
        · rw [Int.negOnePow_odd _ h]
          simp
      have hw : chebyshevExtremalWeight n i = 2 := by
        simp [chebyshevExtremalWeight, hnI]
      rw [ha, hφ', hw, abs_mul, abs_mul, hsign, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
        abs_of_nonneg (Nat.cast_nonneg n)]
      ring
    · have hi0 : 0 < i.val := Nat.pos_of_ne_zero h0
      have hin : i.val < n := lt_of_le_of_ne (Nat.le_of_lt_succ i.isLt) hnI
      let θi : ℝ := nodeAngle n i
      have hθ0 : 0 < θi := by
        unfold θi nodeAngle
        exact div_pos (mul_pos pi_pos (by exact_mod_cast hi0))
          (by exact_mod_cast Nat.pos_of_ne_zero hn0)
      have hθπ : θi < π := by
        unfold θi nodeAngle
        have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
        rw [div_lt_iff₀ hnpos]
        have : (i.val : ℝ) < n := by exact_mod_cast hin
        nlinarith [pi_pos, this]
      have hsinθ : 0 < sin θi := sin_pos_of_pos_of_lt_pi hθ0 hθπ
      let φ : ℝ[X] := chebyshevExtremalNodal n
      have hevalFun : (fun t : ℝ => φ.eval (cos t)) =
          fun t => sin t * sin ((n : ℝ) * t) := by
        ext t
        simpa [φ] using eval_chebyshevExtremalNodal hn t
      have hchain : HasDerivAt (fun t : ℝ => φ.eval (cos t))
          (φ.derivative.eval (cos θi) * -sin θi) θi :=
        (φ.hasDerivAt (cos θi)).comp θi (hasDerivAt_cos θi)
      have hchain' : HasDerivAt (fun t : ℝ => sin t * sin ((n : ℝ) * t))
          (φ.derivative.eval (cos θi) * -sin θi) θi := by
        rw [hevalFun] at hchain
        exact hchain
      have hlin : HasDerivAt (fun t : ℝ => (n : ℝ) * t) (n : ℝ) θi := by
        simpa using (hasDerivAt_id θi).const_mul (n : ℝ)
      have hinner : HasDerivAt (fun t : ℝ => sin ((n : ℝ) * t))
          (cos ((n : ℝ) * θi) * (n : ℝ)) θi :=
        (hasDerivAt_sin ((n : ℝ) * θi)).comp θi hlin
      have hprod : HasDerivAt (fun t : ℝ => sin t * sin ((n : ℝ) * t))
          (cos θi * sin ((n : ℝ) * θi) +
            sin θi * (cos ((n : ℝ) * θi) * (n : ℝ))) θi :=
        (hasDerivAt_sin θi).mul hinner
      have hderEq := hchain'.unique hprod
      have hangle : (n : ℝ) * θi = (i.val : ℝ) * π := by
        unfold θi nodeAngle
        field_simp
      have hsinN : sin ((n : ℝ) * θi) = 0 := by
        rw [hangle, sin_nat_mul_pi]
      have hcosN : cos ((n : ℝ) * θi) = (-1 : ℝ) ^ i.val := by
        rw [hangle, cos_nat_mul_pi]
      rw [hsinN, hcosN] at hderEq
      have hmul0 : cos θi * (0 : ℝ) = 0 := mul_zero _
      rw [hmul0, zero_add] at hderEq
      have hφ' : φ.derivative.eval (cos θi) = -((n : ℝ) * (-1 : ℝ) ^ i.val) := by
        have hne : -sin θi ≠ 0 := by simp [hsinθ.ne']
        apply mul_right_cancel₀ hne
        calc φ.derivative.eval (cos θi) * -sin θi
            = sin θi * (((-1 : ℝ) ^ i.val) * (n : ℝ)) := hderEq
          _ = -((n : ℝ) * (-1 : ℝ) ^ i.val) * -sin θi := by ring
      have habs : |φ.derivative.eval (cos θi)| = (n : ℝ) := by
        rw [hφ', abs_neg, abs_mul, abs_of_nonneg (Nat.cast_nonneg n), abs_pow, abs_neg,
          abs_one, one_pow, mul_one]
      have hw : chebyshevExtremalWeight n i = 1 := by
        rw [chebyshevExtremalWeight, ite_eq_right]
        intro h
        cases h with
        | inl h => exact h0 h
        | inr h => exact hnI h
      simpa [φ, chebyshevExtremalNodes_eq_cos, hw] using habs

/-- Absolute slack large enough for both sides of the Chebyshev–Lebesgue asymptotic. -/
def chebyshevLebesgueSlack : ℝ :=
  11 / 4 + 2 / π + π / 8 + log 2 / π

/-- The slack constant is nonnegative. -/
lemma chebyshevLebesgueSlack_nonneg : 0 ≤ chebyshevLebesgueSlack := by
  have hlog : 0 ≤ log 2 := log_nonneg (by norm_num)
  have hπ : 0 < π := pi_pos
  unfold chebyshevLebesgueSlack
  positivity

/-- One is absorbed by the slack. -/
lemma one_le_chebyshevLebesgueSlack : 1 ≤ chebyshevLebesgueSlack := by
  have hrest : 0 ≤ 2 / π + π / 8 + log 2 / π := by
    have hlog : 0 ≤ log 2 := log_nonneg (by norm_num)
    positivity
  unfold chebyshevLebesgueSlack
  linarith

/-- The midpoint deficit is absorbed by the slack. -/
lemma chebyshevMidpointDeficit_le_slack :
    2 / π + π / 4 + 1 / 2 ≤ chebyshevLebesgueSlack := by
  have hdiff : chebyshevLebesgueSlack - (2 / π + π / 4 + 1 / 2) =
      9 / 4 - π / 8 + log 2 / π := by
    unfold chebyshevLebesgueSlack
    ring
  have hlog : 0 ≤ log 2 / π := by
    have : 0 ≤ log 2 := log_nonneg (by norm_num)
    positivity
  have hpos : 0 ≤ 2 - π / 8 := by linarith [pi_lt_four]
  linarith

/-- Reversal of an extremal index. -/
def reflectNode (n : ℕ) (i : Fin (n + 1)) : Fin (n + 1) :=
  ⟨n - i.val, by have := i.isLt; omega⟩

/-- Reflection is an involution on the extremal indices. -/
lemma reflectNode_involutive (n : ℕ) (i : Fin (n + 1)) :
    reflectNode n (reflectNode n i) = i := by
  apply Fin.ext
  have := i.isLt
  simp [reflectNode]
  omega

/-- Extremal nodes are symmetric about zero. -/
lemma chebyshevExtremalNodes_reflect {n : ℕ} (hn : n ≠ 0) (i : Fin (n + 1)) :
    chebyshevExtremalNodes n (reflectNode n i) = -chebyshevExtremalNodes n i := by
  rw [chebyshevExtremalNodes_eq_cos, chebyshevExtremalNodes_eq_cos]
  have hangle : nodeAngle n (reflectNode n i) = π - nodeAngle n i := by
    unfold nodeAngle reflectNode
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    have hi : i.val ≤ n := Nat.le_of_lt_succ i.isLt
    have hsub : ((n - i.val : ℕ) : ℝ) = (n : ℝ) - i.val := Nat.cast_sub hi
    rw [hsub]
    field_simp
  rw [hangle, cos_sub, cos_pi, sin_pi]
  ring

/-- The Lebesgue function equals one at each extremal node. -/
lemma lebesgueFunction_chebyshev_node {n : ℕ} (hn : n ≠ 0) (i : Fin (n + 1)) :
    lebesgueFunction (chebyshevExtremalNodes n) (chebyshevExtremalNodes n i) = 1 := by
  have hvs : Set.InjOn (chebyshevExtremalNodes n) (univ : Finset (Fin (n + 1))) :=
    (chebyshevExtremalNodes_injective hn).injOn
  unfold lebesgueFunction
  rw [Finset.sum_eq_single i]
  · simp [lagrangeCardinalPolynomial, eval_basis_self hvs (mem_univ i)]
  · intro j _ hji
    simp [lagrangeCardinalPolynomial, eval_basis_of_ne hji (mem_univ i)]
  · simp

end CKMA
