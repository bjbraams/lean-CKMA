/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.Approximation.InterpolationStability.Basic

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
# Chebyshev-extrema nodal estimates

Trigonometric bounds, the nodal polynomial, and the endpoint correction for the
Lebesgue function of the Chebyshev extrema. These estimates feed the logarithmic
bound on the Lebesgue constant.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Polynomial
open scoped BigOperators

open Real Polynomial.Chebyshev Finset Classical Lagrange

/-- Absolute value of a multiple-angle sine is at most the multiple of the sine. -/
private lemma abs_sin_nat_mul (n : ℕ) (x : ℝ) : |sin ((n : ℝ) * x)| ≤ n * |sin x| := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hstep : sin (((n + 1 : ℕ) : ℝ) * x) =
        sin ((n : ℝ) * x) * cos x + cos ((n : ℝ) * x) * sin x := by
      rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, sin_add]
    rw [hstep]
    calc |sin ((n : ℝ) * x) * cos x + cos ((n : ℝ) * x) * sin x|
        ≤ |sin ((n : ℝ) * x) * cos x| + |cos ((n : ℝ) * x) * sin x| := abs_add_le _ _
      _ = |sin ((n : ℝ) * x)| * |cos x| + |cos ((n : ℝ) * x)| * |sin x| := by
          rw [abs_mul, abs_mul]
      _ ≤ |sin ((n : ℝ) * x)| * 1 + 1 * |sin x| := by
          gcongr
          · exact abs_cos_le_one x
          · exact abs_cos_le_one ((n : ℝ) * x)
      _ ≤ (n : ℝ) * |sin x| + |sin x| := by
          rw [one_mul, mul_one]; exact add_le_add ih le_rfl
      _ = (n + 1 : ℕ) * |sin x| := by push_cast; ring

/-- On `(0, π/2)`, the cotangent lies under the reciprocal. -/
private lemma cot_le_inv_of_mem_Ioo_pi_div_two {u : ℝ} (hu : u ∈ Set.Ioo 0 (π / 2)) :
    cot u ≤ 1 / u := by
  have hu0 : 0 < u := hu.1
  have huπ : u < π / 2 := hu.2
  have hsin : 0 < sin u := sin_pos_of_pos_of_lt_pi hu0 (huπ.trans (by linarith [pi_pos]))
  have hcos : 0 < cos u := cos_pos_of_mem_Ioo ⟨by linarith, huπ⟩
  have htan : u ≤ tan u := le_tan hu0.le huπ
  have hucos : u * cos u ≤ sin u := by
    rw [tan_eq_sin_div_cos, le_div_iff₀ hcos] at htan
    simpa [mul_comm] using htan
  rw [cot_eq_cos_div_sin, div_le_div_iff₀ hsin hu0]
  simpa [mul_comm] using hucos

/-- Odd-denominator reciprocals dominate a logarithm by telescoping. -/
lemma sum_odd_reciprocal_ge_log (t : ℕ) :
    (1 / 2) * log (2 * (t : ℝ) + 3) ≤
      ∑ k ∈ range (t + 1), (1 : ℝ) / (2 * (k : ℝ) + 1) := by
  have hterm (k : ℕ) :
      (1 / 2) * (log (2 * ((k + 1 : ℕ) : ℝ) + 1) - log (2 * (k : ℝ) + 1)) ≤
        (1 : ℝ) / (2 * (k : ℝ) + 1) := by
    have hk : 2 * ((k + 1 : ℕ) : ℝ) + 1 = 2 * (k : ℝ) + 3 := by
      push_cast
      ring
    rw [hk]
    have hden : 0 < 2 * (k : ℝ) + 1 := by positivity
    have hnum : 0 < 2 * (k : ℝ) + 3 := by positivity
    have hratio : 0 < (2 * (k : ℝ) + 3) / (2 * (k : ℝ) + 1) := div_pos hnum hden
    have hlog : log ((2 * (k : ℝ) + 3) / (2 * (k : ℝ) + 1)) ≤
        (2 * (k : ℝ) + 3) / (2 * (k : ℝ) + 1) - 1 := log_le_sub_one_of_pos hratio
    have hsub : (2 * (k : ℝ) + 3) / (2 * (k : ℝ) + 1) - 1 =
        2 / (2 * (k : ℝ) + 1) := by
      rw [div_sub_one hden.ne']
      congr 1
      ring
    rw [log_div hnum.ne' hden.ne', hsub] at hlog
    have hmul := mul_le_mul_of_nonneg_left hlog (by norm_num : (0 : ℝ) ≤ 1 / 2)
    calc (1 / 2) * (log (2 * (k : ℝ) + 3) - log (2 * (k : ℝ) + 1))
        ≤ (1 / 2) * (2 / (2 * (k : ℝ) + 1)) := hmul
      _ = 1 / (2 * (k : ℝ) + 1) := by ring
  have htele :
      ∑ k ∈ range (t + 1),
          (1 / 2) * (log (2 * ((k + 1 : ℕ) : ℝ) + 1) - log (2 * (k : ℝ) + 1)) =
        (1 / 2) * log (2 * (t : ℝ) + 3) := by
    rw [← Finset.mul_sum, sum_range_sub (fun k : ℕ => log (2 * (k : ℝ) + 1)) (t + 1)]
    have hlast : log (2 * ((t + 1 : ℕ) : ℝ) + 1) = log (2 * (t : ℝ) + 3) := by
      congr 1
      push_cast
      ring
    rw [hlast]
    have hzero : log (2 * ((0 : ℕ) : ℝ) + 1) = 0 := by
      norm_num [log_one]
    rw [hzero, sub_zero]
  exact (le_of_eq htele.symm).trans (Finset.sum_le_sum fun k _ => hterm k)

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
private lemma chebyshevExtremalNodes_injective {n : ℕ} (hn : n ≠ 0) :
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
private lemma chebyshevIndex_add_one {n : ℕ} (hn : 1 ≤ n) :
    ((n - 1 : ℕ) : ℤ) + 1 = (n : ℤ) := by
  exact_mod_cast (Nat.sub_add_cancel hn : (n - 1) + 1 = n)

/-- The polynomial `(1 - X ^ 2) U_{n-1}`, vanishing on the extremal nodes. -/
private def chebyshevExtremalNodal (n : ℕ) : ℝ[X] :=
  (1 - X ^ 2) * U ℝ ((n - 1 : ℕ) : ℤ)

/-- Trigonometric evaluation of the extremal nodal polynomial. -/
private lemma eval_chebyshevExtremalNodal {n : ℕ} (hn : 1 ≤ n) (θ : ℝ) :
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
private lemma natDegree_chebyshevExtremalNodal {n : ℕ} (hn : 1 ≤ n) :
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
private lemma derivative_one_sub_X_sq : derivative (1 - X ^ 2 : ℝ[X]) = C (-2) * X := by
  rw [derivative_sub, derivative_one, derivative_X_pow]
  simp

/-- Absolute derivative of the nodal polynomial at each extremal node. -/
private lemma abs_derivative_chebyshevExtremalNodal {n : ℕ} (hn : 1 ≤ n)
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
private def reflectNode (n : ℕ) (i : Fin (n + 1)) : Fin (n + 1) :=
  ⟨n - i.val, by have := i.isLt; omega⟩

/-- Reflection is an involution on the extremal indices. -/
private lemma reflectNode_involutive (n : ℕ) (i : Fin (n + 1)) :
    reflectNode n (reflectNode n i) = i := by
  apply Fin.ext
  have := i.isLt
  simp [reflectNode]
  omega

/-- Extremal nodes are symmetric about zero. -/
private lemma chebyshevExtremalNodes_reflect {n : ℕ} (hn : n ≠ 0) (i : Fin (n + 1)) :
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

/-- The nodal polynomial vanishes at every extremal node. -/
private lemma isRoot_chebyshevExtremalNodal {n : ℕ} (hn : 1 ≤ n) (i : Fin (n + 1)) :
    IsRoot (chebyshevExtremalNodal n) (chebyshevExtremalNodes n i) := by
  rw [IsRoot.def, chebyshevExtremalNodes_eq_cos, eval_chebyshevExtremalNodal hn]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hangle : (n : ℝ) * nodeAngle n i = (i.val : ℝ) * π := by
    unfold nodeAngle
    field_simp
  rw [hangle, sin_nat_mul_pi, mul_zero]

/-- Division by a simple nodal factor reproduces the derivative at the root. -/
private lemma eval_divByMonic_derivative (φ : ℝ[X]) (a : ℝ) (ha : IsRoot φ a) :
    (φ.divByMonic (X - C a)).eval a = φ.derivative.eval a := by
  have hmul : (X - C a) * φ.divByMonic (X - C a) = φ :=
    (mul_divByMonic_eq_iff_isRoot).2 ha
  have hder := congrArg derivative hmul
  rw [derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero, one_mul] at hder
  have heval := congrArg (eval a) hder
  simp only [eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul,
    add_zero] at heval
  exact heval

/-- Cardinal polynomials are the scaled monic quotients of the nodal polynomial. -/
private lemma lagrangeCardinal_eq_scaled_divByMonic {n : ℕ} (hn : 1 ≤ n)
    (i : Fin (n + 1)) :
    lagrangeCardinalPolynomial (chebyshevExtremalNodes n) i =
      C (1 / (chebyshevExtremalNodal n).derivative.eval (chebyshevExtremalNodes n i)) *
        (chebyshevExtremalNodal n).divByMonic
          (X - C (chebyshevExtremalNodes n i)) := by
  let x := chebyshevExtremalNodes n
  let φ := chebyshevExtremalNodal n
  let a := x i
  have hvs : Set.InjOn x (univ : Finset (Fin (n + 1))) :=
    (chebyshevExtremalNodes_injective (by omega)).injOn
  have hroot : IsRoot φ a := isRoot_chebyshevExtremalNodal hn i
  have hne : φ.derivative.eval a ≠ 0 := by
    intro hzero
    have habs := abs_derivative_chebyshevExtremalNodal hn i
    rw [hzero, abs_zero] at habs
    have hpos : (0 : ℝ) < (n : ℝ) * chebyshevExtremalWeight n i :=
      mul_pos (by exact_mod_cast (by omega : 0 < n)) (chebyshevExtremalWeight_pos n i)
    linarith
  let q0 := φ.divByMonic (X - C a)
  let q := C (1 / φ.derivative.eval a) * q0
  have hprod : (X - C a) * q0 = φ := (mul_divByMonic_eq_iff_isRoot).2 hroot
  have hq0ne : q0 ≠ 0 := by
    intro hq
    have hφ : φ = 0 := by simpa [q0, hq] using hprod.symm
    have hdeg : φ.natDegree = n + 1 := natDegree_chebyshevExtremalNodal hn
    rw [hφ, natDegree_zero] at hdeg
    omega
  have hnat : q0.natDegree = n := by
    have hmul := natDegree_mul' (p := X - C a) (q := q0)
      (mul_ne_zero (by simp [leadingCoeff_X_sub_C]) (leadingCoeff_ne_zero.mpr hq0ne))
    rw [hprod, natDegree_X_sub_C, natDegree_chebyshevExtremalNodal hn] at hmul
    omega
  let r : Fin (n + 1) → ℝ := fun j => if j = i then 1 else 0
  have hdegq : q.degree < #(univ : Finset (Fin (n + 1))) := by
    rw [Finset.card_univ, Fintype.card_fin]
    have hle : q.natDegree ≤ n := by
      calc q.natDegree ≤ q0.natDegree := natDegree_C_mul_le _ _
        _ = n := hnat
    have : q.degree ≤ (n : WithBot ℕ) :=
      degree_le_natDegree.trans (WithBot.coe_le_coe.mpr hle)
    exact this.trans_lt (WithBot.coe_lt_coe.mpr (Nat.lt_succ_self n))
  have hq0a : q0.eval a = φ.derivative.eval a := eval_divByMonic_derivative φ a hroot
  have hqeval : ∀ j ∈ (univ : Finset (Fin (n + 1))), q.eval (x j) = r j := by
    intro j _
    by_cases hji : j = i
    · rw [hji]
      simp only [q, eval_mul, eval_C]
      rw [show x i = a from rfl, hq0a]
      field_simp [hne]
      simp [r]
    · have hrootj : φ.eval (x j) = 0 := isRoot_chebyshevExtremalNodal hn j
      have hdiff : x j - a ≠ 0 := by
        intro h
        exact hji ((chebyshevExtremalNodes_injective (by omega)) (sub_eq_zero.mp h))
      have heq : (x j - a) * q0.eval (x j) = φ.eval (x j) := by
        have := congrArg (eval (x j)) hprod
        simpa [q0, eval_mul, eval_sub, eval_X, eval_C] using this
      have heq0 : (x j - a) * q0.eval (x j) = 0 := by simpa [hrootj] using heq
      have hqj : q0.eval (x j) = 0 := (mul_eq_zero.mp heq0).resolve_left hdiff
      simp [q, r, hji, eval_mul, eval_C, hqj]
  have hdegB : (lagrangeCardinalPolynomial x i).degree <
      #(univ : Finset (Fin (n + 1))) := by
    rw [degree_basis hvs (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    exact WithBot.coe_lt_coe.mpr (Nat.sub_lt (Nat.succ_pos n) zero_lt_one)
  have hbasis : lagrangeCardinalPolynomial x i = Lagrange.interpolate univ x r := by
    refine eq_interpolate_of_eval_eq _ hvs hdegB ?_
    intro j _
    by_cases hji : j = i
    · rw [hji, lagrangeCardinalPolynomial, eval_basis_self hvs (Finset.mem_univ i)]
      simp [r]
    · rw [lagrangeCardinalPolynomial, eval_basis_of_ne (Ne.symm hji) (Finset.mem_univ j)]
      simp [r, hji]
  have hqint : q = Lagrange.interpolate univ x r :=
    eq_interpolate_of_eval_eq _ hvs hdegq hqeval
  simpa [q, q0, a, φ, x] using hbasis.trans hqint.symm

/-- Absolute cardinal value away from its node, in terms of the nodal polynomial. -/
private lemma abs_eval_cardinal_div {n : ℕ} (hn : 1 ≤ n) (i : Fin (n + 1)) {t : ℝ}
    (ht : t ≠ chebyshevExtremalNodes n i) :
    |(lagrangeCardinalPolynomial (chebyshevExtremalNodes n) i).eval t| =
      |(chebyshevExtremalNodal n).eval t| /
        (|t - chebyshevExtremalNodes n i| *
          |(chebyshevExtremalNodal n).derivative.eval (chebyshevExtremalNodes n i)|) := by
  let φ := chebyshevExtremalNodal n
  let a := chebyshevExtremalNodes n i
  let q0 := φ.divByMonic (X - C a)
  have hroot : IsRoot φ a := isRoot_chebyshevExtremalNodal hn i
  have hprod : (X - C a) * q0 = φ := (mul_divByMonic_eq_iff_isRoot).2 hroot
  have hdiv : (t - a) * q0.eval t = φ.eval t := by
    have := congrArg (eval t) hprod
    simpa [q0, eval_mul, eval_sub, eval_X, eval_C] using this
  have hq0 : q0.eval t = φ.eval t / (t - a) := by
    rw [eq_div_iff (sub_ne_zero.mpr ht), mul_comm]
    exact hdiv
  have hden : φ.derivative.eval a ≠ 0 := by
    intro hzero
    have habs := abs_derivative_chebyshevExtremalNodal hn i
    rw [hzero, abs_zero] at habs
    have hpos : (0 : ℝ) < (n : ℝ) * chebyshevExtremalWeight n i :=
      mul_pos (by exact_mod_cast (by omega : 0 < n)) (chebyshevExtremalWeight_pos n i)
    linarith
  rw [lagrangeCardinal_eq_scaled_divByMonic hn i]
  simp only [eval_mul, eval_C]
  rw [hq0, abs_mul, abs_div, abs_one, abs_div]
  have habsφ' : |φ.derivative.eval a| ≠ 0 := abs_ne_zero.mpr hden
  have habst : |t - a| ≠ 0 := abs_ne_zero.mpr (sub_ne_zero.mpr ht)
  field_simp [habsφ', habst]
  ring

/-- Reflected cardinal polynomials are the originals composed with `-X`. -/
private lemma cardinal_comp_neg {n : ℕ} (hn : 1 ≤ n) (i : Fin (n + 1)) :
    (lagrangeCardinalPolynomial (chebyshevExtremalNodes n) i).comp (-X) =
      lagrangeCardinalPolynomial (chebyshevExtremalNodes n) (reflectNode n i) := by
  let x := chebyshevExtremalNodes n
  have hvs : Set.InjOn x (univ : Finset (Fin (n + 1))) :=
    (chebyshevExtremalNodes_injective (by omega)).injOn
  let p := (lagrangeCardinalPolynomial x i).comp (-X)
  let target := lagrangeCardinalPolynomial x (reflectNode n i)
  have hdegP : p.degree < #(univ : Finset (Fin (n + 1))) := by
    rw [degree_comp_neg_X, degree_basis hvs (Finset.mem_univ i), Finset.card_univ,
      Fintype.card_fin]
    exact WithBot.coe_lt_coe.mpr (Nat.sub_lt (Nat.succ_pos n) zero_lt_one)
  have hdegT : target.degree < #(univ : Finset (Fin (n + 1))) := by
    rw [degree_basis hvs (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    exact WithBot.coe_lt_coe.mpr (Nat.sub_lt (Nat.succ_pos n) zero_lt_one)
  have hval : ∀ j ∈ (univ : Finset (Fin (n + 1))), p.eval (x j) = target.eval (x j) := by
    intro j _
    rw [eval_comp]
    have hnegX : (-X).eval (x j) = -x j := by simp
    rw [hnegX]
    have hneg : -x j = x (reflectNode n j) :=
      (chebyshevExtremalNodes_reflect (by omega) j).symm
    rw [hneg]
    by_cases hji : reflectNode n j = i
    · have hj : j = reflectNode n i := by
        apply_fun reflectNode n at hji
        simpa [reflectNode_involutive n] using hji
      simp [hj, reflectNode_involutive n i, target, lagrangeCardinalPolynomial,
        eval_basis_self hvs (Finset.mem_univ _)]
    · have hjr : j ≠ reflectNode n i := by
        intro hj
        apply hji
        simpa [hj] using reflectNode_involutive n i
      rw [eval_basis_of_ne (Ne.symm hji) (Finset.mem_univ _),
        eval_basis_of_ne (Ne.symm hjr) (Finset.mem_univ _)]
  have htarg : target = Lagrange.interpolate univ x (fun j => target.eval (x j)) :=
    eq_interpolate hvs hdegT
  have hp : p = Lagrange.interpolate univ x (fun j => target.eval (x j)) :=
    eq_interpolate_of_eval_eq _ hvs hdegP hval
  simpa [p, target, x] using hp.trans htarg.symm

/-- The extremal Lebesgue function is even. -/
lemma lebesgueFunction_neg {n : ℕ} (hn : 1 ≤ n) (t : ℝ) :
    lebesgueFunction (chebyshevExtremalNodes n) (-t) =
      lebesgueFunction (chebyshevExtremalNodes n) t := by
  unfold lebesgueFunction
  refine Finset.sum_nbij' (s := univ) (t := univ) (reflectNode n) (reflectNode n)
    (fun _ _ => Finset.mem_univ _) (fun _ _ => Finset.mem_univ _)
    (fun a _ => reflectNode_involutive n a) (fun a _ => reflectNode_involutive n a) ?_
  intro i _
  rw [← cardinal_comp_neg hn i, eval_comp]
  simp

/-- Sign of an off-node angle relative to a node angle. -/
def chebyshevAngleSign (n : ℕ) (θ : ℝ) (i : Fin (n + 1)) : ℝ :=
  if nodeAngle n i < θ then 1 else -1

/-- Cotangent main term in the angular formula for a cardinal polynomial. -/
def chebyshevLebesgueMain (n : ℕ) (θ : ℝ) (i : Fin (n + 1)) : ℝ :=
  |sin ((n : ℝ) * θ)| / (2 * (n : ℝ) * chebyshevExtremalWeight n i) *
    cot (|θ - nodeAngle n i| / 2)

/-- Cotangent correction in the angular formula for a cardinal polynomial. -/
def chebyshevLebesgueCorr (n : ℕ) (θ : ℝ) (i : Fin (n + 1)) : ℝ :=
  |sin ((n : ℝ) * θ)| / (2 * (n : ℝ) * chebyshevExtremalWeight n i) *
    chebyshevAngleSign n θ i * cot ((θ + nodeAngle n i) / 2)

/-- Cosine difference in product form. -/
private lemma abs_cos_sub_cos (θ φ : ℝ) :
    |cos θ - cos φ| = 2 * |sin ((θ + φ) / 2)| * |sin ((θ - φ) / 2)| := by
  rw [Real.cos_sub_cos, abs_mul, abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]

/-- Absolute sine is unchanged by replacing an angle with its absolute value. -/
private lemma abs_sin_div_two_abs (δ : ℝ) : |sin (δ / 2)| = |sin (|δ| / 2)| := by
  rcases le_or_gt 0 δ with hδ | hδ
  · rw [abs_of_nonneg hδ]
  · rw [abs_of_neg hδ, neg_div, sin_neg, abs_neg]

/-- Half-angle gap between an interior angle and a node angle. -/
private lemma nodeGap_mem_Ioo {θ φ : ℝ} (hθ : θ ∈ Set.Ioo 0 π) (hφ : φ ∈ Set.Icc 0 π)
    (hne : θ ≠ φ) : |θ - φ| / 2 ∈ Set.Ioo 0 (π / 2) := by
  have hlt : |θ - φ| < π := by
    have hmax : |θ - φ| ≤ max θ (π - θ) := by
      rcases le_or_gt φ θ with h | h
      · rw [abs_of_nonneg (sub_nonneg.mpr h)]
        have hφ0 : 0 ≤ φ := hφ.1
        have : θ - φ ≤ θ := by linarith
        exact le_trans this (le_max_left _ _)
      · rw [abs_of_neg (sub_neg.mpr h)]
        have : -(θ - φ) ≤ π - θ := by linarith [hφ.2]
        exact le_trans this (le_max_right _ _)
    have hstrict : max θ (π - θ) < π := by
      apply max_lt
      · exact hθ.2
      · linarith [hθ.1]
    exact lt_of_le_of_lt hmax hstrict
  refine ⟨div_pos (abs_pos.mpr (sub_ne_zero.mpr hne)) (by norm_num), ?_⟩
  rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)]
  linarith

/-- Average of an interior angle and a node angle stays inside `(0, π)`. -/
private lemma nodeAverage_mem_Ioo {θ φ : ℝ} (hθ : θ ∈ Set.Ioo 0 π) (hφ : φ ∈ Set.Icc 0 π) :
    (θ + φ) / 2 ∈ Set.Ioo 0 π := by
  refine ⟨div_pos (by linarith [hθ.1, hφ.1]) (by norm_num), ?_⟩
  rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)]
  linarith [hθ.2, hφ.2]

/-- Sine quotient that splits a cardinal factor into cotangent terms. -/
private lemma sin_div_gap {θ φ : ℝ} (hθ : θ ∈ Set.Ioo 0 π) (hφ : φ ∈ Set.Icc 0 π)
    (hne : θ ≠ φ) :
    sin θ / (sin (|θ - φ| / 2) * sin ((θ + φ) / 2)) =
      cot (|θ - φ| / 2) + (if φ < θ then (1 : ℝ) else -1) * cot ((θ + φ) / 2) := by
  set u : ℝ := |θ - φ| / 2
  set avg : ℝ := (θ + φ) / 2
  have hu := nodeGap_mem_Ioo hθ hφ hne
  have havg := nodeAverage_mem_Ioo hθ hφ
  have hsinu : 0 < sin u := sin_pos_of_pos_of_lt_pi hu.1 (hu.2.trans (by linarith [pi_pos]))
  have hsinavg : 0 < sin avg := sin_pos_of_pos_of_lt_pi havg.1 havg.2
  by_cases hlt : φ < θ
  · have huθ : u = (θ - φ) / 2 := by
      simp [u, abs_of_nonneg (sub_nonneg.mpr hlt.le)]
    have hsum : avg + u = θ := by
      simp only [avg, u, huθ]
      ring
    have hsin : sin θ = sin avg * cos u + cos avg * sin u := by
      rw [← hsum, sin_add]
    rw [hsin, ite_eq_left hlt, cot_eq_cos_div_sin, cot_eq_cos_div_sin]
    field_simp [hsinu.ne', hsinavg.ne']
  · have hgt : θ < φ := lt_of_le_of_ne (le_of_not_gt hlt) hne
    have huθ : u = (φ - θ) / 2 := by
      simp [u, abs_of_neg (sub_neg.mpr hgt)]
    have hsum : avg - u = θ := by
      simp only [avg, u, huθ]
      ring
    have hsin : sin θ = sin avg * cos u - cos avg * sin u := by
      rw [← hsum, sin_sub]
    rw [hsin, ite_eq_right hlt, cot_eq_cos_div_sin, cot_eq_cos_div_sin]
    field_simp [hsinu.ne', hsinavg.ne']
    ring

/-- Off a node, each cardinal polynomial is the sum of its main and correction terms. -/
lemma abs_cardinal_eq_main_add_corr {n : ℕ} (hn : 1 ≤ n) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 π) (hnode : ∀ i, θ ≠ nodeAngle n i) (i : Fin (n + 1)) :
    |(lagrangeCardinalPolynomial (chebyshevExtremalNodes n) i).eval (cos θ)| =
      chebyshevLebesgueMain n θ i + chebyshevLebesgueCorr n θ i := by
  have hn0 : n ≠ 0 := by omega
  have hφmem : nodeAngle n i ∈ Set.Icc 0 π := nodeAngle_mem_Icc hn0 i
  have hne : θ ≠ nodeAngle n i := hnode i
  have hcosne : cos θ ≠ chebyshevExtremalNodes n i := by
    rw [chebyshevExtremalNodes_eq_cos]
    intro h
    exact hne ((strictAntiOn_cos.injOn.eq_iff ⟨hθ.1.le, hθ.2.le⟩ hφmem).mp h)
  have habs := abs_eval_cardinal_div hn i hcosne
  have heval : |(chebyshevExtremalNodal n).eval (cos θ)| =
      |sin θ| * |sin ((n : ℝ) * θ)| := by
    rw [eval_chebyshevExtremalNodal hn, abs_mul]
  have hder := abs_derivative_chebyshevExtremalNodal hn i
  have hdiff := abs_cos_sub_cos θ (nodeAngle n i)
  have hsinθ : 0 < sin θ := sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have hu := nodeGap_mem_Ioo hθ hφmem hne
  have havg := nodeAverage_mem_Ioo hθ hφmem
  have hsinu : 0 < sin (|θ - nodeAngle n i| / 2) :=
    sin_pos_of_pos_of_lt_pi hu.1 (hu.2.trans (by linarith [pi_pos]))
  have hsinavg : 0 < sin ((θ + nodeAngle n i) / 2) :=
    sin_pos_of_pos_of_lt_pi havg.1 havg.2
  have hweight : 0 < chebyshevExtremalWeight n i := chebyshevExtremalWeight_pos n i
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hsplit := sin_div_gap hθ hφmem hne
  rw [habs, heval, hder, chebyshevExtremalNodes_eq_cos, hdiff, abs_of_pos hsinθ]
  rw [abs_sin_div_two_abs (θ - nodeAngle n i), abs_of_pos hsinu, abs_of_pos hsinavg]
  unfold chebyshevLebesgueMain chebyshevLebesgueCorr chebyshevAngleSign
  have hcomm : sin θ / (sin ((θ + nodeAngle n i) / 2) * sin (|θ - nodeAngle n i| / 2)) =
      cot (|θ - nodeAngle n i| / 2) +
        (if nodeAngle n i < θ then (1 : ℝ) else -1) *
          cot ((θ + nodeAngle n i) / 2) := by
    rw [mul_comm]
    exact hsplit
  calc
      sin θ * |sin ((n : ℝ) * θ)| /
          (2 * sin ((θ + nodeAngle n i) / 2) * sin (|θ - nodeAngle n i| / 2) *
            ((n : ℝ) * chebyshevExtremalWeight n i))
        = |sin ((n : ℝ) * θ)| / (2 * (n : ℝ) * chebyshevExtremalWeight n i) *
            (sin θ / (sin ((θ + nodeAngle n i) / 2) * sin (|θ - nodeAngle n i| / 2))) := by
          field_simp [hsinu.ne', hsinavg.ne', hweight.ne', hnpos.ne']
    _ = |sin ((n : ℝ) * θ)| / (2 * (n : ℝ) * chebyshevExtremalWeight n i) *
          (cot (|θ - nodeAngle n i| / 2) +
            (if nodeAngle n i < θ then (1 : ℝ) else -1) *
              cot ((θ + nodeAngle n i) / 2)) := by
        rw [hcomm]
    _ = |sin ((n : ℝ) * θ)| / (2 * (n : ℝ) * chebyshevExtremalWeight n i) *
          cot (|θ - nodeAngle n i| / 2) +
        (|sin ((n : ℝ) * θ)| / (2 * (n : ℝ) * chebyshevExtremalWeight n i) *
          (if nodeAngle n i < θ then (1 : ℝ) else -1)) *
          cot ((θ + nodeAngle n i) / 2) := by ring

/-- On `(0, π/2)`, cotangent lies above `1/u - u/2`. -/
lemma cot_ge_inv_sub {u : ℝ} (hu : u ∈ Set.Ioo 0 (π / 2)) :
    1 / u - u / 2 ≤ cot u := by
  have hu0 : 0 < u := hu.1
  have hsin : 0 < sin u :=
    sin_pos_of_pos_of_lt_pi hu0 (hu.2.trans (by linarith [pi_pos]))
  have hcos : 0 < cos u := by
    refine cos_pos_of_mem_Ioo ⟨?_, hu.2⟩
    exact (by linarith [pi_pos] : -(π / 2) < 0).trans hu0
  have hsinle : sin u ≤ u := sin_le hu0.le
  have hcosle : 1 - u ^ 2 / 2 ≤ cos u := one_sub_sq_div_two_le_cos
  have hquot : cos u / u ≤ cos u / sin u := by
    have hmul : cos u * sin u ≤ cos u * u :=
      mul_le_mul_of_nonneg_left hsinle hcos.le
    exact (div_le_div_iff₀ hu0 hsin).mpr hmul
  have hlower : (1 - u ^ 2 / 2) / u ≤ cos u / u :=
    div_le_div_of_nonneg_right hcosle hu0.le
  have hlin : (1 - u ^ 2 / 2) / u = 1 / u - u / 2 := by
    field_simp
  rw [cot_eq_cos_div_sin, ← hlin]
  exact hlower.trans hquot

/-- Harmonic numbers increase with the upper index. -/
private lemma harmonic_mono {a b : ℕ} (h : a ≤ b) : (harmonic a : ℝ) ≤ harmonic b := by
  have hsub : range a ⊆ range b := Finset.range_subset_range.mpr h
  have hsum : harmonic a ≤ harmonic b :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ =>
      inv_nonneg.mpr (Nat.cast_nonneg (i + 1))
  exact_mod_cast hsum

/-- Sum of the cotangent main terms, compared with `(2/π) log(n+1)`. -/
lemma sum_chebyshevLebesgueMain_le {n : ℕ} (hn : 1 ≤ n) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 π) (hnode : ∀ i, θ ≠ nodeAngle n i) :
    ∑ i, chebyshevLebesgueMain n θ i ≤
      (2 / π) * log ((n : ℝ) + 1) + 2 + 2 / π := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hnpos : (n : ℝ) ≠ 0 := hn0.ne'
  let ν : ℝ := (n : ℝ) * θ / π
  let m : ℕ := Nat.floor ν
  let frac : ℝ := ν - m
  have hν0 : 0 < ν := by
    unfold ν
    exact div_pos (mul_pos hn0 hθ.1) pi_pos
  have hνn : ν < n := by
    unfold ν
    rw [div_lt_iff₀ pi_pos]
    nlinarith [hθ.2, hn0, pi_pos]
  have hm_le : (m : ℝ) ≤ ν := Nat.floor_le hν0.le
  have hm_lt_one : ν < (m : ℝ) + 1 := by
    simpa using Nat.lt_floor_add_one ν
  have hm_nat : m < n := by
    have : (m : ℝ) < n := hm_le.trans_lt hνn
    exact_mod_cast this
  have hfrac_nonneg : 0 ≤ frac := by
    unfold frac
    linarith
  have hfrac_lt : frac < 1 := by
    unfold frac
    linarith
  have hfrac_pos : 0 < frac := by
    apply lt_of_le_of_ne hfrac_nonneg
    intro hzero
    have hνeq : ν = m := by
      unfold frac at hzero
      linarith
    have hθeq : θ = nodeAngle n ⟨m, by omega⟩ := by
      unfold nodeAngle
      rw [show (m : ℝ) = ν from hνeq.symm]
      have hνdef : ν = (n : ℝ) * θ / π := rfl
      rw [hνdef]
      field_simp
    exact hnode ⟨m, by omega⟩ hθeq
  have hsin_abs : |sin ((n : ℝ) * θ)| = sin (π * frac) := by
    have hmul : (n : ℝ) * θ = (m : ℝ) * π + π * frac := by
      have hθν : (n : ℝ) * θ = π * ν := by
        unfold ν
        field_simp
      rw [hθν, show ν = (m : ℝ) + frac by unfold frac; ring]
      ring
    rw [hmul, add_comm, sin_add_nat_mul_pi, abs_mul]
    have habs1 : |(-1 : ℝ) ^ m| = 1 := by
      rw [abs_pow, abs_neg, abs_one, one_pow]
    rw [habs1, one_mul, abs_of_pos]
    exact sin_pos_of_pos_of_lt_pi (mul_pos pi_pos hfrac_pos)
      (by nlinarith [hfrac_lt, pi_pos])
  have hterm (i : Fin (n + 1)) : chebyshevLebesgueMain n θ i ≤
      |sin ((n : ℝ) * θ)| / (π * |(i.val : ℝ) - ν|) := by
    have hφ : nodeAngle n i ∈ Set.Icc 0 π := nodeAngle_mem_Icc (by omega) i
    have hneθ : θ ≠ nodeAngle n i := hnode i
    have hu := nodeGap_mem_Ioo hθ hφ hneθ
    have hαpos := chebyshevExtremalWeight_pos n i
    have hα1 := one_le_chebyshevExtremalWeight n i
    have hdpos : 0 < |(i.val : ℝ) - ν| := by
      rw [abs_pos]
      intro hzero
      have hθeq : θ = nodeAngle n i := by
        have hiν : (i.val : ℝ) = ν := by linarith
        unfold nodeAngle
        rw [hiν, show ν = (n : ℝ) * θ / π from rfl]
        field_simp
      exact hneθ hθeq
    have hgap : |θ - nodeAngle n i| = π * |(i.val : ℝ) - ν| / n := by
      have hθv : θ = π * ν / n := by
        unfold ν
        field_simp
      rw [hθv, nodeAngle]
      have hsub : π * ν / n - π * (i.val : ℝ) / n =
          π * (ν - (i.val : ℝ)) / n := by
        field_simp
      rw [hsub, abs_div, abs_mul, abs_of_pos pi_pos, abs_of_pos hn0, abs_sub_comm]
    have hu_eq : |θ - nodeAngle n i| / 2 =
        π * |(i.val : ℝ) - ν| / (2 * n) := by
      rw [hgap]
      ring
    have hcot := cot_le_inv_of_mem_Ioo_pi_div_two hu
    have hfac : 0 ≤ |sin ((n : ℝ) * θ)| /
        (2 * (n : ℝ) * chebyshevExtremalWeight n i) := by
      positivity
    calc chebyshevLebesgueMain n θ i
        = |sin ((n : ℝ) * θ)| /
            (2 * (n : ℝ) * chebyshevExtremalWeight n i) *
            cot (|θ - nodeAngle n i| / 2) := by
          unfold chebyshevLebesgueMain
          rfl
      _ ≤ |sin ((n : ℝ) * θ)| /
            (2 * (n : ℝ) * chebyshevExtremalWeight n i) *
            (1 / (|θ - nodeAngle n i| / 2)) :=
          mul_le_mul_of_nonneg_left hcot hfac
      _ = |sin ((n : ℝ) * θ)| /
            (chebyshevExtremalWeight n i * π * |(i.val : ℝ) - ν|) := by
          rw [hu_eq]
          field_simp [hαpos.ne', hnpos, hdpos.ne', pi_ne_zero]
      _ ≤ |sin ((n : ℝ) * θ)| / (π * |(i.val : ℝ) - ν|) := by
          have hc : 0 < π * |(i.val : ℝ) - ν| := mul_pos pi_pos hdpos
          have hden : π * |(i.val : ℝ) - ν| ≤
              chebyshevExtremalWeight n i * π * |(i.val : ℝ) - ν| := by
            have hmul := mul_le_mul_of_nonneg_right hα1 hc.le
            rwa [one_mul, ← mul_assoc] at hmul
          exact div_le_div_of_nonneg_left (abs_nonneg _) hc hden
  have hsum1 : ∑ i, chebyshevLebesgueMain n θ i ≤
      ∑ i : Fin (n + 1), |sin ((n : ℝ) * θ)| / (π * |(i.val : ℝ) - ν|) :=
    Finset.sum_le_sum fun i _ => hterm i
  have hrange : ∑ i : Fin (n + 1),
        |sin ((n : ℝ) * θ)| / (π * |(i.val : ℝ) - ν|) =
      ∑ j ∈ range (n + 1), |sin ((n : ℝ) * θ)| / (π * |(j : ℝ) - ν|) := by
    exact Fin.sum_univ_eq_sum_range
      (fun j => |sin ((n : ℝ) * θ)| / (π * |(j : ℝ) - ν|)) (n + 1)
  rw [hsin_abs] at hsum1 hrange
  have hsplit := Finset.sum_range_add
    (fun j => sin (π * frac) / (π * |(j : ℝ) - ν|)) (m + 1) (n - m)
  have hcount : m + 1 + (n - m) = n + 1 := by omega
  have hdistL (j : ℕ) (hj : j ≤ m) :
      |(j : ℝ) - ν| = ((m - j : ℕ) : ℝ) + frac := by
    have hjν : (j : ℝ) ≤ ν := by
      have : (j : ℝ) ≤ m := by exact_mod_cast hj
      linarith
    rw [abs_of_nonpos (sub_nonpos.mpr hjν)]
    have hsub : ((m - j : ℕ) : ℝ) = (m : ℝ) - j := Nat.cast_sub hj
    unfold frac
    rw [hsub]
    ring
  have hdistR (k : ℕ) :
      |((m + 1 + k : ℕ) : ℝ) - ν| = (k : ℝ) + 1 - frac := by
    have hlt : ν < ((m + 1 + k : ℕ) : ℝ) := by
      push_cast
      linarith
    rw [abs_of_nonneg (sub_nonneg.mpr hlt.le)]
    unfold frac
    push_cast
    ring
  have hleftEq : ∑ j ∈ range (m + 1), sin (π * frac) / (π * |(j : ℝ) - ν|) =
      ∑ j ∈ range (m + 1), sin (π * frac) / (π * ((j : ℝ) + frac)) := by
    have hrew : ∑ j ∈ range (m + 1), sin (π * frac) / (π * |(j : ℝ) - ν|) =
        ∑ j ∈ range (m + 1),
          sin (π * frac) / (π * (((m - j : ℕ) : ℝ) + frac)) := by
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [hdistL j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))]
    rw [hrew, ← Finset.sum_range_reflect
      (fun j => sin (π * frac) / (π * ((j : ℝ) + frac))) (m + 1)]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hidx : m + 1 - 1 - j = m - j := by
      have := Finset.mem_range.mp hj
      omega
    rw [hidx]
  have hrightEq : ∑ k ∈ range (n - m),
        sin (π * frac) / (π * |((m + 1 + k : ℕ) : ℝ) - ν|) =
      ∑ k ∈ range (n - m), sin (π * frac) / (π * ((k : ℝ) + 1 - frac)) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hdistR k]
  have hsin_le_arg : sin (π * frac) ≤ π * frac := sin_le (mul_nonneg pi_pos.le hfrac_nonneg)
  have hzeroL : sin (π * frac) / (π * frac) ≤ 1 := by
    rw [div_le_one (mul_pos pi_pos hfrac_pos)]
    exact hsin_le_arg
  have honeSub : 0 < 1 - frac := by linarith
  have hsinSymm : sin (π * frac) = sin (π * (1 - frac)) := by
    rw [show π * (1 - frac) = π - π * frac by ring, sin_pi_sub]
  have hzeroR : sin (π * frac) / (π * (1 - frac)) ≤ 1 := by
    rw [hsinSymm, div_le_one (mul_pos pi_pos honeSub)]
    exact sin_le (mul_nonneg pi_pos.le honeSub.le)
  have htailL : ∑ k ∈ range m,
        sin (π * frac) / (π * (((k + 1 : ℕ) : ℝ) + frac)) ≤
      (harmonic m : ℝ) / π := by
    have hle : ∑ k ∈ range m,
        sin (π * frac) / (π * (((k + 1 : ℕ) : ℝ) + frac)) ≤
        ∑ k ∈ range m, (1 : ℝ) / (π * (k + 1 : ℕ)) := by
      refine Finset.sum_le_sum fun k _ => ?_
      have hden1 : 0 < π * ((k + 1 : ℕ) : ℝ) := by positivity
      have hden2 : 0 < π * (((k + 1 : ℕ) : ℝ) + frac) := by positivity
      rw [div_le_div_iff₀ hden2 hden1]
      nlinarith [sin_le_one (π * frac), hfrac_nonneg, pi_pos]
    have hH : ∑ k ∈ range m, (1 : ℝ) / (π * (k + 1 : ℕ)) = (harmonic m : ℝ) / π := by
      calc ∑ k ∈ range m, (1 : ℝ) / (π * (k + 1 : ℕ))
          = ∑ k ∈ range m, ((k + 1 : ℕ) : ℝ)⁻¹ * π⁻¹ := by
            refine Finset.sum_congr rfl fun k _ => ?_
            field_simp
        _ = (∑ k ∈ range m, ((k + 1 : ℕ) : ℝ)⁻¹) * π⁻¹ := by rw [← Finset.sum_mul]
        _ = (harmonic m : ℝ) * π⁻¹ := by
            simp [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
        _ = (harmonic m : ℝ) / π := by rw [div_eq_mul_inv]
    exact hle.trans (le_of_eq hH)
  have htailR : ∑ k ∈ range (n - m - 1),
        sin (π * frac) / (π * (((k + 1 : ℕ) : ℝ) + 1 - frac)) ≤
      (harmonic (n - m - 1) : ℝ) / π := by
    have hle : ∑ k ∈ range (n - m - 1),
        sin (π * frac) / (π * (((k + 1 : ℕ) : ℝ) + 1 - frac)) ≤
        ∑ k ∈ range (n - m - 1), (1 : ℝ) / (π * (k + 1 : ℕ)) := by
      refine Finset.sum_le_sum fun k _ => ?_
      have hden1 : 0 < π * ((k + 1 : ℕ) : ℝ) := by positivity
      have hden2 : 0 < π * (((k + 1 : ℕ) : ℝ) + 1 - frac) := by
        have : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) + 1 - frac := by
          have hk : (1 : ℝ) ≤ (k + 1 : ℕ) := by exact_mod_cast Nat.succ_pos k
          linarith
        positivity
      rw [div_le_div_iff₀ hden2 hden1]
      nlinarith [sin_le_one (π * frac), hfrac_lt, pi_pos]
    have hH : ∑ k ∈ range (n - m - 1), (1 : ℝ) / (π * (k + 1 : ℕ)) =
        (harmonic (n - m - 1) : ℝ) / π := by
      calc ∑ k ∈ range (n - m - 1), (1 : ℝ) / (π * (k + 1 : ℕ))
          = ∑ k ∈ range (n - m - 1), ((k + 1 : ℕ) : ℝ)⁻¹ * π⁻¹ := by
            refine Finset.sum_congr rfl fun k _ => ?_
            field_simp
        _ = (∑ k ∈ range (n - m - 1), ((k + 1 : ℕ) : ℝ)⁻¹) * π⁻¹ := by
            rw [← Finset.sum_mul]
        _ = (harmonic (n - m - 1) : ℝ) * π⁻¹ := by
            simp [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
        _ = (harmonic (n - m - 1) : ℝ) / π := by rw [div_eq_mul_inv]
    exact hle.trans (le_of_eq hH)
  have hleftBound : ∑ j ∈ range (m + 1), sin (π * frac) / (π * ((j : ℝ) + frac)) ≤
      (harmonic m : ℝ) / π + 1 := by
    rw [Finset.sum_range_succ' (fun j => sin (π * frac) / (π * ((j : ℝ) + frac))) m]
    simp only [Nat.cast_zero, zero_add]
    exact add_le_add htailL hzeroL
  have hrightBound : ∑ k ∈ range (n - m),
        sin (π * frac) / (π * ((k : ℝ) + 1 - frac)) ≤
      (harmonic (n - m - 1) : ℝ) / π + 1 := by
    have hlen : n - m = (n - m - 1) + 1 := by omega
    rw [hlen, Finset.sum_range_succ'
      (fun k => sin (π * frac) / (π * ((k : ℝ) + 1 - frac))) (n - m - 1)]
    simp only [Nat.cast_zero, zero_add]
    exact add_le_add htailR hzeroR
  have hHm : (harmonic m : ℝ) ≤ 1 + log (n : ℝ) := by
    have hmn : m ≤ n := Nat.le_of_lt hm_nat
    exact (harmonic_mono hmn).trans (harmonic_le_one_add_log n)
  have hHr : (harmonic (n - m - 1) : ℝ) ≤ 1 + log (n : ℝ) := by
    have hle : n - m - 1 ≤ n := by omega
    exact (harmonic_mono hle).trans (harmonic_le_one_add_log n)
  have hlog : log (n : ℝ) ≤ log ((n : ℝ) + 1) :=
    (log_le_log_iff hn0 (by positivity)).mpr (by linarith)
  have hsumR : ∑ j ∈ range (n + 1), sin (π * frac) / (π * |(j : ℝ) - ν|) ≤
      2 + 2 * (1 + log (n : ℝ)) / π := by
    rw [hcount] at hsplit
    rw [hsplit, hleftEq, hrightEq]
    calc
        (∑ j ∈ range (m + 1), sin (π * frac) / (π * ((j : ℝ) + frac))) +
          ∑ k ∈ range (n - m), sin (π * frac) / (π * ((k : ℝ) + 1 - frac))
          ≤ ((harmonic m : ℝ) / π + 1) + ((harmonic (n - m - 1) : ℝ) / π + 1) :=
            add_le_add hleftBound hrightBound
      _ = 2 + ((harmonic m : ℝ) + harmonic (n - m - 1)) / π := by ring
      _ ≤ 2 + 2 * (1 + log (n : ℝ)) / π := by
          have hHsum : (harmonic m : ℝ) + harmonic (n - m - 1) ≤
              2 * (1 + log (n : ℝ)) := by linarith
          have hdiv := div_le_div_of_nonneg_right hHsum pi_pos.le
          linarith
  have hlogMul : (2 / π) * log (n : ℝ) ≤ (2 / π) * log ((n : ℝ) + 1) :=
    mul_le_mul_of_nonneg_left hlog (by positivity)
  calc ∑ i, chebyshevLebesgueMain n θ i
      ≤ ∑ i : Fin (n + 1), sin (π * frac) / (π * |(i.val : ℝ) - ν|) := hsum1
    _ = ∑ j ∈ range (n + 1), sin (π * frac) / (π * |(j : ℝ) - ν|) := hrange
    _ ≤ 2 + 2 * (1 + log (n : ℝ)) / π := hsumR
    _ = 2 + 2 / π + (2 / π) * log (n : ℝ) := by ring
    _ ≤ (2 / π) * log ((n : ℝ) + 1) + 2 + 2 / π := by linarith [hlogMul]

/-- Cotangent decreases on `(0, π)`. -/
lemma cot_antitone_Ioo {x y : ℝ} (hx : x ∈ Set.Ioo 0 π) (hy : y ∈ Set.Ioo 0 π)
    (hxy : x ≤ y) : cot y ≤ cot x := by
  have hsx : 0 < sin x := sin_pos_of_pos_of_lt_pi hx.1 hx.2
  have hsy : 0 < sin y := sin_pos_of_pos_of_lt_pi hy.1 hy.2
  rw [cot_eq_cos_div_sin, cot_eq_cos_div_sin, div_le_div_iff₀ hsy hsx]
  have hsin : sin (x - y) ≤ 0 := by
    rcases hxy.eq_or_lt with h | h
    · rw [h, sub_self, sin_zero]
    · exact (sin_neg_of_neg_of_neg_pi_lt (by linarith) (by linarith [hx.1, hy.2])).le
  have hsub : cos y * sin x - cos x * sin y = sin (x - y) := by
    rw [sin_sub]
    ring
  rw [← sub_nonpos, hsub]
  exact hsin

/-- Interior extremal weights equal one. -/
lemma chebyshevExtremalWeight_of_interior {n : ℕ} {i : Fin (n + 1)}
    (h0 : i.val ≠ 0) (hn : i.val ≠ n) : chebyshevExtremalWeight n i = 1 := by
  rw [chebyshevExtremalWeight, ite_eq_right]
  intro h
  cases h <;> contradiction

/-- The angle-comparison sign is `1` when the node lies to the left. -/
lemma chebyshevAngleSign_of_lt {n : ℕ} {θ : ℝ} {i : Fin (n + 1)}
    (h : nodeAngle n i < θ) : chebyshevAngleSign n θ i = 1 := by
  simp [chebyshevAngleSign, h]

/-- The angle-comparison sign is `-1` when the node is not to the left. -/
lemma chebyshevAngleSign_of_not_lt {n : ℕ} {θ : ℝ} {i : Fin (n + 1)}
    (h : ¬ nodeAngle n i < θ) : chebyshevAngleSign n θ i = -1 := by
  simp [chebyshevAngleSign, h]

/-- Left-endpoint correction on `(0, π/2]`. -/
lemma chebyshevLebesgueCorr_zero_le {n : ℕ} (hn : 1 ≤ n) {θ : ℝ}
    (hθ : θ ∈ Set.Ioc 0 (π / 2)) :
    chebyshevLebesgueCorr n θ ⟨0, by omega⟩ ≤ 1 / 2 := by
  have hθ0 : 0 < θ := hθ.1
  have hθ2 : θ ≤ π / 2 := hθ.2
  let i0 : Fin (n + 1) := ⟨0, by omega⟩
  have hφ : nodeAngle n i0 = 0 := by simp [nodeAngle, i0]
  have hsign : chebyshevAngleSign n θ i0 = 1 :=
    chebyshevAngleSign_of_lt (by simpa [hφ] using hθ0)
  have hw : chebyshevExtremalWeight n i0 = 2 := by simp [chebyshevExtremalWeight, i0]
  have hsinθ : 0 < sin θ :=
    sin_pos_of_pos_of_lt_pi hθ0 (hθ2.trans_lt (by linarith [pi_pos]))
  have hhalf0 : 0 < θ / 2 := by linarith
  have hhalfπ : θ / 2 < π / 2 := by linarith [hθ2]
  have hsinhalf : 0 < sin (θ / 2) :=
    sin_pos_of_pos_of_lt_pi hhalf0 (hhalfπ.trans (by linarith [pi_pos]))
  have hcoshalf : 0 < cos (θ / 2) :=
    cos_pos_of_mem_Ioo ⟨(by linarith [pi_pos] : -(π / 2) < 0).trans hhalf0, hhalfπ⟩
  have hdouble : sin θ = 2 * sin (θ / 2) * cos (θ / 2) := by
    have h := sin_two_mul (θ / 2)
    rwa [show 2 * (θ / 2) = θ by ring] at h
  have hmul := abs_sin_nat_mul n θ
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hbound : |sin ((n : ℝ) * θ)| ≤ (n : ℝ) * (2 * sin (θ / 2) * cos (θ / 2)) := by
    calc |sin ((n : ℝ) * θ)|
        ≤ (n : ℝ) * |sin θ| := hmul
      _ = (n : ℝ) * sin θ := by rw [abs_of_pos hsinθ]
      _ = (n : ℝ) * (2 * sin (θ / 2) * cos (θ / 2)) := by rw [hdouble]
  unfold chebyshevLebesgueCorr
  rw [hsign, hw, hφ, add_zero, mul_one, cot_eq_cos_div_sin]
  have hden : (2 : ℝ) * n * 2 = 4 * n := by ring
  rw [hden]
  have hfac : 0 ≤ cos (θ / 2) / sin (θ / 2) / (4 * (n : ℝ)) := by positivity
  have hineq := mul_le_mul_of_nonneg_right hbound hfac
  have hassoc : |sin ((n : ℝ) * θ)| * (cos (θ / 2) / sin (θ / 2) / (4 * (n : ℝ))) =
      |sin ((n : ℝ) * θ)| / (4 * (n : ℝ)) * (cos (θ / 2) / sin (θ / 2)) := by ring
  have hsimp : (n : ℝ) * (2 * sin (θ / 2) * cos (θ / 2)) *
        (cos (θ / 2) / sin (θ / 2) / (4 * (n : ℝ))) = cos (θ / 2) ^ 2 / 2 := by
    field_simp [hsinhalf.ne', hnpos.ne']
    norm_num
  rw [← hassoc]
  refine (hineq.trans_eq hsimp).trans ?_
  have hcosle : cos (θ / 2) ^ 2 ≤ 1 := by
    rw [← sq_abs]
    have h1 := abs_cos_le_one (θ / 2)
    have hmul := mul_le_mul h1 h1 (abs_nonneg _) zero_le_one
    simpa [sq] using hmul
  exact (div_le_div_of_nonneg_right hcosle (by norm_num : (0 : ℝ) ≤ 2)).trans (by norm_num)

/-- Right-endpoint correction on `(0, π/2]`. -/
lemma chebyshevLebesgueCorr_last_le {n : ℕ} (hn : 1 ≤ n) {θ : ℝ}
    (hθ : θ ∈ Set.Ioc 0 (π / 2)) :
    chebyshevLebesgueCorr n θ ⟨n, by omega⟩ ≤ π / 8 := by
  have hθ0 : 0 < θ := hθ.1
  have hθ2 : θ ≤ π / 2 := hθ.2
  let iN : Fin (n + 1) := ⟨n, by omega⟩
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hφ : nodeAngle n iN = π := by
    simp [nodeAngle, iN]
    field_simp
  have hsign : chebyshevAngleSign n θ iN = -1 :=
    chebyshevAngleSign_of_not_lt (by
      rw [hφ]
      linarith [hθ2, pi_pos])
  have hw : chebyshevExtremalWeight n iN = 2 := by simp [chebyshevExtremalWeight, iN]
  have hcot : cot ((θ + π) / 2) = -tan (θ / 2) := by
    have harg : (θ + π) / 2 = π / 2 + θ / 2 := by ring
    have hcos : 0 < cos (θ / 2) :=
      cos_pos_of_mem_Ioo ⟨(by linarith [pi_pos] : -(π / 2) < 0).trans (by linarith : 0 < θ / 2),
        by linarith [hθ2]⟩
    rw [harg, cot_eq_cos_div_sin, tan_eq_sin_div_cos, cos_add, sin_add, cos_pi_div_two,
      sin_pi_div_two]
    field_simp [hcos.ne']
    ring
  unfold chebyshevLebesgueCorr
  rw [hsign, hw, hφ, hcot]
  have habs : |sin ((n : ℝ) * θ)| ≤ (n : ℝ) * θ := by
    calc |sin ((n : ℝ) * θ)|
        ≤ |(n : ℝ) * θ| := abs_sin_le_abs
      _ = (n : ℝ) * θ := by rw [abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) hθ0.le)]
  have htan : tan (θ / 2) ≤ 1 := by
    have hmono := strictMonoOn_tan.monotoneOn
    have hmem1 : θ / 2 ∈ Set.Ioo (-(π / 2)) (π / 2) :=
      ⟨by linarith [pi_pos], by linarith [hθ2]⟩
    have hmem2 : π / 4 ∈ Set.Ioo (-(π / 2)) (π / 2) := by
      constructor <;> linarith [pi_pos]
    have hle := hmono hmem1 hmem2 (by linarith [hθ2])
    simpa [tan_pi_div_four] using hle
  have hprod : |sin ((n : ℝ) * θ)| / (4 * (n : ℝ)) * tan (θ / 2) ≤ θ / 4 := by
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hcoef : 0 ≤ tan (θ / 2) / (4 * (n : ℝ)) := by
      have : 0 ≤ tan (θ / 2) :=
        tan_nonneg_of_nonneg_of_le_pi_div_two (by linarith) (by linarith [hθ2])
      positivity
    have hineq := mul_le_mul_of_nonneg_right habs hcoef
    have hleft : |sin ((n : ℝ) * θ)| * (tan (θ / 2) / (4 * (n : ℝ))) =
        |sin ((n : ℝ) * θ)| / (4 * (n : ℝ)) * tan (θ / 2) := by ring
    rw [← hleft]
    have hright : (n : ℝ) * θ * (tan (θ / 2) / (4 * (n : ℝ))) = θ / 4 * tan (θ / 2) := by
      field_simp [hnpos.ne']
    rw [hright] at hineq
    have htan1 : θ / 4 * tan (θ / 2) ≤ θ / 4 := by
      have hθ4 : 0 ≤ θ / 4 := by linarith
      simpa [mul_one] using mul_le_mul_of_nonneg_left htan hθ4
    exact hineq.trans htan1
  have hneg : |sin ((n : ℝ) * θ)| / (2 * (n : ℝ) * 2) * (-1) * (-tan (θ / 2)) =
      |sin ((n : ℝ) * θ)| / (4 * (n : ℝ)) * tan (θ / 2) := by ring
  rw [hneg]
  exact hprod.trans (by linarith [hθ2])


end CKMA
