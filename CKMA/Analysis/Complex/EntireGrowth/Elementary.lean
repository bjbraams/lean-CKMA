/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import TauCeti.Analysis.Complex.CanonicalProduct.ElementaryFactor

import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Genus-`p` Weierstrass elementary factors

The estimates that make a canonical product of fixed genus converge, and the simple-zero
statement used to match multiplicities. The formula agrees definitionally with
`CKMA.weierstrassElementaryFactor`, and with TauCeti's `Complex.weierstrassFactor` by
`weierstrassFactor_eq_complex`.
-/

public section

noncomputable section

namespace CKMA

open Complex Finset

/-- The partial exponential sum `z + z²/2 + ⋯ + zᵖ/p` in the genus-`p` factor. -/
@[expose]
def weierstrassSum (p : ℕ) (z : ℂ) : ℂ :=
  ∑ k ∈ range p, z ^ (k + 1) / (k + 1 : ℂ)

/-- The genus-`p` Weierstrass elementary factor `(1 - z) exp(z + ⋯ + zᵖ/p)`. -/
@[expose]
def weierstrassFactor (p : ℕ) (z : ℂ) : ℂ :=
  (1 - z) * exp (weierstrassSum p z)

/-- The sum in the elementary factor is the defining finite sum. -/
theorem weierstrassSum_def (p : ℕ) (z : ℂ) :
    weierstrassSum p z = ∑ k ∈ range p, z ^ (k + 1) / (k + 1 : ℂ) := rfl

/-- The elementary factor is the defining product. -/
theorem weierstrassFactor_def (p : ℕ) (z : ℂ) :
    weierstrassFactor p z = (1 - z) * exp (weierstrassSum p z) := rfl

/-- The elementary factor equals TauCeti's `Complex.weierstrassFactor`. -/
theorem weierstrassFactor_eq_complex (p : ℕ) (z : ℂ) :
    weierstrassFactor p z = _root_.Complex.weierstrassFactor p z := by
  rw [weierstrassFactor, weierstrassSum, Complex.weierstrassFactor_eq_mul_exp_sum]

/-- The exponential sum vanishes at the origin. -/
@[simp]
theorem weierstrassSum_zero (p : ℕ) : weierstrassSum p 0 = 0 := by
  simp [weierstrassSum]

/-- The elementary factor is normalized to one at the origin. -/
@[simp]
theorem weierstrassFactor_zero (p : ℕ) : weierstrassFactor p 0 = 1 := by
  simp [weierstrassFactor]

/-- The elementary factor vanishes at one. -/
@[simp]
theorem weierstrassFactor_one (p : ℕ) : weierstrassFactor p 1 = 0 := by
  simp [weierstrassFactor]

/-- The Taylor logarithm cancels the exponential sum of the elementary factor. -/
theorem logTaylor_neg_add_weierstrassSum (p : ℕ) (u : ℂ) :
    logTaylor (p + 1) (-u) + weierstrassSum p u = 0 := by
  rw [logTaylor, weierstrassSum, Finset.sum_range_succ'
    (fun j : ℕ => (-1 : ℂ) ^ (j + 1) * (-u) ^ j / j) p]
  have h0 : (-1 : ℂ) ^ ((0 : ℕ) + 1) * (-u) ^ 0 / (0 : ℕ) = 0 := by
    simp [div_zero]
  rw [h0, add_zero, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun k _ => ?_
  have hpow : (-u) ^ (k + 1) = (-1 : ℂ) ^ (k + 1) * u ^ (k + 1) := by
    rw [← neg_one_mul, mul_pow]
  rw [hpow, ← mul_assoc, ← pow_add]
  have hexp : k + 1 + 1 + (k + 1) = 2 * k + 3 := by omega
  rw [hexp]
  have hsign : (-1 : ℂ) ^ (2 * k + 3) = -1 := by
    rw [show 2 * k + 3 = 2 * k + 2 + 1 by omega, pow_succ, pow_add, pow_mul, pow_two]
    simp
  rw [hsign, neg_one_mul]
  simp [div_eq_mul_inv, Nat.cast_add, Nat.cast_one, add_comm]

/-- Inside the unit disk the elementary factor is the exponential of the logarithmic remainder. -/
theorem weierstrassFactor_eq_exp_remainder {p : ℕ} {u : ℂ} (hu : ‖u‖ < 1) :
    weierstrassFactor p u =
      exp (log (1 - u) - logTaylor (p + 1) (-u)) := by
  have hne : 1 - u ≠ 0 := by
    intro h
    have : ‖u‖ = 1 := by simpa [sub_eq_zero.mp h] using (norm_one : ‖(1 : ℂ)‖ = 1)
    linarith
  have hsum : weierstrassSum p u = -logTaylor (p + 1) (-u) := by
    have h := logTaylor_neg_add_weierstrassSum p u
    rw [add_comm] at h
    exact add_eq_zero_iff_eq_neg.mp h
  calc
    weierstrassFactor p u = (1 - u) * exp (weierstrassSum p u) := rfl
    _ = exp (log (1 - u)) * exp (-logTaylor (p + 1) (-u)) := by
      rw [hsum]
      conv_lhs => rw [← exp_log hne]
    _ = exp (log (1 - u) - logTaylor (p + 1) (-u)) := by
      rw [← exp_add, ← sub_eq_add_neg]

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

/-- On the closed half-disk the elementary factor stays within `4 ‖u‖ᵖ⁺¹` of one. -/
theorem norm_weierstrassFactor_sub_one_le {p : ℕ} {u : ℂ} (hu : ‖u‖ ≤ 1 / 2) :
    ‖weierstrassFactor p u - 1‖ ≤ 4 * ‖u‖ ^ (p + 1) := by
  have hlt : ‖u‖ < 1 := lt_of_le_of_lt hu (by norm_num)
  rw [weierstrassFactor_eq_exp_remainder hlt]
  set w : ℂ := log (1 - u) - logTaylor (p + 1) (-u)
  have hw : ‖w‖ ≤ 2 * ‖u‖ ^ (p + 1) := norm_weierstrass_remainder_le_half hu
  have hw1 : ‖w‖ ≤ 1 := by
    have hpow : ‖u‖ ^ (p + 1) ≤ (1 / 2 : ℝ) ^ (p + 1) :=
      pow_le_pow_left₀ (norm_nonneg u) hu _
    have hhalf : (1 / 2 : ℝ) ^ (p + 1) ≤ 1 / 2 := by
      simpa using pow_le_pow_of_le_one (by norm_num) (by norm_num : (1 / 2 : ℝ) ≤ 1)
        (Nat.succ_pos p)
    linarith
  calc
    _ ≤ 2 * ‖w‖ := norm_exp_sub_one_le hw1
    _ ≤ 2 * (2 * ‖u‖ ^ (p + 1)) := by gcongr
    _ = 4 * ‖u‖ ^ (p + 1) := by ring

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

/-- The only zero of the elementary factor is one. -/
theorem weierstrassFactor_eq_zero_iff {p : ℕ} {z : ℂ} :
    weierstrassFactor p z = 0 ↔ z = 1 := by
  rw [weierstrassFactor, mul_eq_zero, or_iff_left (exp_ne_zero _), sub_eq_zero]
  exact eq_comm

/-- The exponential sum grows at most like `p (‖u‖ᵖ + 1)`. -/
theorem norm_weierstrassSum_le (p : ℕ) (u : ℂ) :
    ‖weierstrassSum p u‖ ≤ (p : ℝ) * (‖u‖ ^ p + 1) := by
  unfold weierstrassSum
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
  have hexp : ‖exp (weierstrassSum p u)‖ ≠ 0 := by
    rw [norm_exp]
    exact (Real.exp_pos _).ne'
  rw [weierstrassFactor, norm_mul, Real.log_mul hpos.ne' hexp, norm_exp, Real.log_exp]
  have hsum := norm_weierstrassSum_le p u
  have hre : -‖weierstrassSum p u‖ ≤ (weierstrassSum p u).re :=
    (abs_le.mp (abs_re_le_norm _)).1
  linarith

/-- The exponential sum is entire. -/
theorem differentiable_weierstrassSum (p : ℕ) : Differentiable ℂ (weierstrassSum p) := by
  unfold weierstrassSum
  fun_prop

/-- The elementary factor is entire. -/
theorem differentiable_weierstrassFactor (p : ℕ) : Differentiable ℂ (weierstrassFactor p) := by
  unfold weierstrassFactor
  exact ((differentiable_const (1 : ℂ)).sub differentiable_id).mul
    (differentiable_weierstrassSum p).cexp

/-- The unique zero of the elementary factor is simple. -/
theorem analyticOrderAt_weierstrassFactor_one (p : ℕ) :
    analyticOrderAt (weierstrassFactor p) 1 = 1 := by
  unfold weierstrassFactor
  have hfun : (fun z : ℂ => (1 - z) * exp (weierstrassSum p z)) =
      (fun z : ℂ => 1 - z) * fun z : ℂ => exp (weierstrassSum p z) := rfl
  have hsubA : AnalyticAt ℂ (fun z : ℂ => 1 - z) 1 :=
    ((differentiable_const (1 : ℂ)).sub differentiable_id).analyticAt 1
  have hexpA : AnalyticAt ℂ (fun z : ℂ => exp (weierstrassSum p z)) 1 :=
    (differentiable_weierstrassSum p).cexp.analyticAt 1
  rw [hfun, analyticOrderAt_mul hsubA hexpA]
  have hsub : analyticOrderAt (fun z : ℂ => (1 : ℂ) - z) 1 = 1 := by
    have hneg : (fun z : ℂ => (1 : ℂ) - z) = -fun z : ℂ => z - 1 := by
      funext z
      dsimp [Pi.neg_apply]
      ring
    rw [hneg, analyticOrderAt_neg, analyticOrderAt_id_sub_const_self]
  have hexp : analyticOrderAt (fun z : ℂ => exp (weierstrassSum p z)) 1 = 0 := by
    rw [AnalyticAt.analyticOrderAt_eq_zero hexpA]
    exact exp_ne_zero _
  simp [hsub, hexp]

/-- A zero list may be finite (`none`) or infinite. `some` contributes one elementary factor. -/
@[expose]
def optionFactor (p : ℕ) (a : ℕ → Option ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  match a n with
  | none => 1
  | some w => weierstrassFactor p (z / w)

/-- A missing zero contributes the empty factor. -/
theorem optionFactor_none {p n : ℕ} {a : ℕ → Option ℂ} {z : ℂ} (ha : a n = none) :
    optionFactor p a n z = 1 := by
  simp [optionFactor, ha]

/-- A listed zero contributes the elementary factor of `z / w`. -/
theorem optionFactor_some {p n : ℕ} {a : ℕ → Option ℂ} {z w : ℂ} (ha : a n = some w) :
    optionFactor p a n z = weierstrassFactor p (z / w) := by
  simp [optionFactor, ha]

/-- Each factor is an entire function of `z`. -/
theorem differentiable_optionFactor (p : ℕ) (a : ℕ → Option ℂ) (n : ℕ) :
    Differentiable ℂ (optionFactor p a n) := by
  unfold optionFactor
  split
  · exact differentiable_const _
  · exact (differentiable_weierstrassFactor p).comp (differentiable_id.div_const _)

/-- On a disk of radius `R`, a far zero makes the factor `1 + O((R / ‖w‖) ^ (p + 1))`. -/
theorem norm_optionFactor_sub_one_of_large {p : ℕ} {a : ℕ → Option ℂ} {n : ℕ} {z w : ℂ}
    {R : ℝ} (ha : a n = some w) (hR : 0 < R) (hz : ‖z‖ ≤ R) (hw : 2 * R ≤ ‖w‖) :
    ‖optionFactor p a n z - 1‖ ≤ 4 * (R / ‖w‖) ^ (p + 1) := by
  have hw0 : 0 < ‖w‖ := by linarith
  have hdiv : ‖z / w‖ ≤ R / ‖w‖ := by
    rw [norm_div]
    exact div_le_div_of_nonneg_right hz hw0.le
  have hhalf : ‖z / w‖ ≤ 1 / 2 := by
    refine hdiv.trans ?_
    rw [div_le_iff₀ hw0]
    linarith
  have hpow : ‖z / w‖ ^ (p + 1) ≤ (R / ‖w‖) ^ (p + 1) :=
    pow_le_pow_left₀ (norm_nonneg _) hdiv _
  rw [optionFactor_some ha]
  calc
    _ ≤ 4 * ‖z / w‖ ^ (p + 1) := norm_weierstrassFactor_sub_one_le hhalf
    _ ≤ 4 * (R / ‖w‖) ^ (p + 1) := by gcongr

/-- Scaling the argument by a non-zero slope preserves the simple zero. -/
theorem analyticOrderAt_weierstrassFactor_div {p : ℕ} {a z : ℂ} (ha : a ≠ 0) (hz : z = a) :
    analyticOrderAt (fun w => weierstrassFactor p (w / a)) z = 1 := by
  have hg : AnalyticAt ℂ (fun w : ℂ => w / a) z :=
    (differentiable_id.div_const a).analyticAt z
  have hderiv : deriv (fun w : ℂ => w / a) z ≠ 0 := by
    rw [deriv_div_const, deriv_id'']
    exact div_ne_zero one_ne_zero ha
  rw [show (fun w => weierstrassFactor p (w / a)) =
      weierstrassFactor p ∘ (fun w => w / a) from rfl,
    analyticOrderAt_comp_of_deriv_ne_zero hg hderiv]
  have hdiv : z / a = 1 := by rw [hz, div_self ha]
  simpa [hdiv] using analyticOrderAt_weierstrassFactor_one p

end CKMA
