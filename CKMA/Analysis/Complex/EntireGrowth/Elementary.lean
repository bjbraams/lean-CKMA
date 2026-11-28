/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import TauCeti.Analysis.Complex.CanonicalProduct.ElementaryFactor

import TauCeti.Analysis.SpecialFunctions.Complex.Log.Taylor

/-!
# Estimates for the genus-`p` Weierstrass elementary factors

Estimates for TauCeti's elementary factor
`Complex.weierstrassFactor p u = (1 - u) exp(u + ⋯ + uᵖ/p)` that make a canonical product of fixed
genus converge and bound it from below away from its zeros.
The definition, its zero, its simple root and the sharp bound
`Complex.norm_weierstrassFactor_sub_one_le` (`‖E_p(u) - 1‖ ≤ ‖u‖ᵖ⁺¹` on `‖u‖ ≤ 1`) are TauCeti's.

## Main results

* `CKMA.weierstrassFactor_eq_exp_remainder`: on the unit disk, `E_p(u)` is the exponential of the
  logarithmic remainder `log (1 - u) - logTaylor (p + 1) (-u)`.
* `CKMA.norm_weierstrass_remainder_le`, `CKMA.norm_weierstrass_remainder_le_half`: bounds for that
  remainder.
* `CKMA.log_norm_weierstrassFactor_le_half`, `CKMA.log_norm_weierstrassFactor_ge_half`:
  `|log ‖E_p(u)‖| ≤ 2 ‖u‖ᵖ⁺¹` on `‖u‖ ≤ 1 / 2`.
* `CKMA.log_norm_weierstrassFactor_ge`: a lower bound by `log ‖1 - u‖` on the whole plane.
* `CKMA.analyticOrderAt_weierstrassFactor_div`: `u ↦ E_p(u / a)` has a simple zero at `a ≠ 0`.
-/

public section

noncomputable section

namespace CKMA

open Complex Finset

/-- Inside the unit disk the elementary factor is the exponential of the logarithmic remainder. -/
theorem weierstrassFactor_eq_exp_remainder {p : ℕ} {u : ℂ} (hu : ‖u‖ < 1) :
    weierstrassFactor p u = exp (log (1 - u) - logTaylor (p + 1) (-u)) := by
  have hne : 1 - u ≠ 0 := by
    intro h
    have : ‖u‖ = 1 := by simpa [sub_eq_zero.mp h] using (norm_one : ‖(1 : ℂ)‖ = 1)
    linarith
  rw [weierstrassFactor_def, sub_eq_add_neg (log _), exp_add, exp_log hne]

/-- The logarithmic remainder after the genus-`p` sum is `O(‖u‖ᵖ⁺¹)` on the unit disk. -/
theorem norm_weierstrass_remainder_le {p : ℕ} {u : ℂ} (hu : ‖u‖ < 1) :
    ‖log (1 - u) - logTaylor (p + 1) (-u)‖ ≤
      ‖u‖ ^ (p + 1) * (1 - ‖u‖)⁻¹ / (p + 1) := by
  simpa [sub_eq_add_neg] using norm_log_sub_logTaylor_le p (z := -u) (by simpa using hu)

/-- On the closed half-disk the logarithmic remainder is at most `2 ‖u‖ᵖ⁺¹`. -/
theorem norm_weierstrass_remainder_le_half {p : ℕ} {u : ℂ} (hu : ‖u‖ ≤ 1 / 2) :
    ‖log (1 - u) - logTaylor (p + 1) (-u)‖ ≤ 2 * ‖u‖ ^ (p + 1) := by
  have hlt : ‖u‖ < 1 := lt_of_le_of_lt hu (by norm_num)
  have hrem := norm_weierstrass_remainder_le (p := p) hlt
  have hden : (1 - ‖u‖)⁻¹ ≤ 2 := by
    have hpos : (0 : ℝ) < 1 - ‖u‖ := by linarith
    rw [inv_le_iff_one_le_mul₀ hpos]
    linarith
  have hpow : 0 ≤ ‖u‖ ^ (p + 1) := pow_nonneg (norm_nonneg u) _
  have hp : (1 : ℝ) ≤ (p + 1 : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le p)
  have hdiv : (1 - ‖u‖)⁻¹ / (p + 1) ≤ 2 := by
    calc
      (1 - ‖u‖)⁻¹ / (p + 1) ≤ (1 - ‖u‖)⁻¹ / 1 := by
        gcongr
      _ = (1 - ‖u‖)⁻¹ := by ring
      _ ≤ 2 := hden
  calc
    _ ≤ ‖u‖ ^ (p + 1) * (1 - ‖u‖)⁻¹ / (p + 1) := hrem
    _ = ‖u‖ ^ (p + 1) * ((1 - ‖u‖)⁻¹ / (p + 1)) := by ring
    _ ≤ ‖u‖ ^ (p + 1) * 2 := mul_le_mul_of_nonneg_left hdiv hpow
    _ = 2 * ‖u‖ ^ (p + 1) := by ring

/-- On the closed half-disk the logarithm of the norm is at most `2 ‖u‖ᵖ⁺¹`. -/
theorem log_norm_weierstrassFactor_le_half {p : ℕ} {u : ℂ} (hu : ‖u‖ ≤ 1 / 2) :
    Real.log ‖weierstrassFactor p u‖ ≤ 2 * ‖u‖ ^ (p + 1) := by
  have hlt : ‖u‖ < 1 := lt_of_le_of_lt hu (by norm_num)
  rw [weierstrassFactor_eq_exp_remainder hlt, norm_exp, Real.log_exp]
  exact (re_le_norm _).trans (norm_weierstrass_remainder_le_half hu)

/-- On the closed half-disk the logarithm of the norm is at least `-2 ‖u‖ᵖ⁺¹`. -/
theorem log_norm_weierstrassFactor_ge_half {p : ℕ} {u : ℂ} (hu : ‖u‖ ≤ 1 / 2) :
    -2 * ‖u‖ ^ (p + 1) ≤ Real.log ‖weierstrassFactor p u‖ := by
  have hlt : ‖u‖ < 1 := lt_of_le_of_lt hu (by norm_num)
  rw [weierstrassFactor_eq_exp_remainder hlt, norm_exp, Real.log_exp]
  have hw := norm_weierstrass_remainder_le_half (p := p) hu
  calc
    -2 * ‖u‖ ^ (p + 1) ≤ -‖log (1 - u) - logTaylor (p + 1) (-u)‖ := by linarith
    _ ≤ (log (1 - u) - logTaylor (p + 1) (-u)).re := (abs_le.mp (abs_re_le_norm _)).1

/-- The exponential sum `-logTaylor (p + 1) (-u) = u + ⋯ + uᵖ/p` of the elementary factor
grows at most like `p (‖u‖ᵖ + 1)`. -/
theorem norm_neg_logTaylor_neg_le (p : ℕ) (u : ℂ) :
    ‖-logTaylor (p + 1) (-u)‖ ≤ (p : ℝ) * (‖u‖ ^ p + 1) := by
  rw [neg_logTaylor_succ_neg_eq_sum]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ k ∈ range p, ‖u ^ (k + 1) / (k + 1 : ℂ)‖ ≤ ‖u‖ ^ p + 1 := by
    intro k hk
    have hcast : ‖(k : ℂ) + 1‖ = (k + 1 : ℝ) := by
      have hℂ : (k : ℂ) + 1 = ((k + 1 : ℕ) : ℂ) := by simp [Nat.cast_add, Nat.cast_one]
      have hℝ : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by simp [Nat.cast_add, Nat.cast_one]
      rw [hℂ, Complex.norm_natCast, hℝ]
    rw [norm_div, norm_pow, hcast]
    have hden : (1 : ℝ) ≤ (k + 1 : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
    have hdiv : ‖u‖ ^ (k + 1) / (k + 1 : ℝ) ≤ ‖u‖ ^ (k + 1) :=
      div_le_self (pow_nonneg (norm_nonneg u) _) hden
    refine hdiv.trans ?_
    rcases le_or_gt (1 : ℝ) ‖u‖ with h1 | h1
    · have hk' : k + 1 ≤ p := Nat.succ_le_of_lt (mem_range.mp hk)
      have hpow : ‖u‖ ^ (k + 1) ≤ ‖u‖ ^ p := pow_le_pow_right₀ h1 hk'
      linarith [pow_nonneg (norm_nonneg u) p]
    · have hsmall : ‖u‖ ^ (k + 1) ≤ 1 := pow_le_one₀ (norm_nonneg u) h1.le
      linarith [pow_nonneg (norm_nonneg u) p]
  refine (Finset.sum_le_sum hterm).trans ?_
  simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_add]

/-- A lower bound by the distance to one, valid away from that zero. -/
theorem log_norm_weierstrassFactor_ge {p : ℕ} {u : ℂ} (hu : u ≠ 1) :
    Real.log ‖1 - u‖ - (p : ℝ) * (‖u‖ ^ p + 1) ≤ Real.log ‖weierstrassFactor p u‖ := by
  have hpos : 0 < ‖1 - u‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hu))
  have hexp : ‖exp (-logTaylor (p + 1) (-u))‖ ≠ 0 := by
    rw [norm_exp]
    exact (Real.exp_pos _).ne'
  rw [weierstrassFactor_def, norm_mul, Real.log_mul hpos.ne' hexp, norm_exp, Real.log_exp]
  have hsum := norm_neg_logTaylor_neg_le p u
  have hre : -‖-logTaylor (p + 1) (-u)‖ ≤ (-logTaylor (p + 1) (-u)).re :=
    (abs_le.mp (abs_re_le_norm _)).1
  linarith

/-- Scaling the argument by a nonzero slope `a` moves the simple zero of the elementary factor
to `a`. -/
theorem analyticOrderAt_weierstrassFactor_div (p : ℕ) {a : ℂ} (ha : a ≠ 0) :
    analyticOrderAt (fun w => weierstrassFactor p (w / a)) a = 1 := by
  simpa only [div_eq_inv_mul] using
    analyticOrderAt_weierstrassFactor_mul p (c := a⁻¹) (inv_mul_cancel₀ ha)

end CKMA
