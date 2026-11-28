/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.NumberTheory.Harmonic.Defs

/-!
# Elementary real bounds for Chebyshev interpolation

Real inequalities used in the Chebyshev–Lebesgue estimates, none of them specific to
interpolation: a multiple-angle sine bound, two-sided cotangent bounds on `(0, π / 2)`, the
antitonicity of the cotangent on `(0, π)`, a logarithmic lower bound for sums of odd
reciprocals, and the monotonicity of the harmonic numbers.

## Main results

* `CKMA.abs_sin_nat_mul_le`: `|sin (n x)| ≤ n |sin x|`.
* `CKMA.cot_le_one_div`, `CKMA.one_div_sub_div_two_le_cot`: `1 / u - u / 2 ≤ cot u ≤ 1 / u` on
  `(0, π / 2)`.
* `CKMA.antitoneOn_cot`: the cotangent is antitone on `(0, π)`.
* `CKMA.sum_odd_reciprocal_ge_log`: `log (2t + 3) / 2 ≤ ∑_{k ≤ t} 1 / (2k + 1)`.
* `CKMA.harmonic_mono`: the harmonic numbers are monotone.
-/

public section

namespace CKMA

open Real Finset
open scoped BigOperators

/-- Absolute value of a multiple-angle sine is at most the multiple of the sine. -/
theorem abs_sin_nat_mul_le (n : ℕ) (x : ℝ) : |sin ((n : ℝ) * x)| ≤ n * |sin x| := by
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
theorem cot_le_one_div {u : ℝ} (hu : u ∈ Set.Ioo 0 (π / 2)) :
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
theorem sum_odd_reciprocal_ge_log (t : ℕ) :
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

/-- On `(0, π/2)`, cotangent lies above `1/u - u/2`. -/
theorem one_div_sub_div_two_le_cot {u : ℝ} (hu : u ∈ Set.Ioo 0 (π / 2)) :
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

/-- Harmonic numbers increase with the index. -/
theorem harmonic_mono : Monotone harmonic := fun _ _ h ↦
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr h) fun i _ _ ↦
    inv_nonneg.mpr (Nat.cast_nonneg (i + 1))

/-- Cotangent decreases on `(0, π)`. -/
theorem antitoneOn_cot : AntitoneOn cot (Set.Ioo 0 π) := by
  intro x hx y hy hxy
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

end CKMA
