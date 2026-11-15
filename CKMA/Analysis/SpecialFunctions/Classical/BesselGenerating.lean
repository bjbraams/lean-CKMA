/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Bessel
public import CKMA.Analysis.Complex.Basic

/-!
# Generating Function for Integer-Order Bessel Functions

The bilateral integer-order Bessel generating series `∑_{n ∈ ℤ} J_n(z) t^n = exp((z/2)(t - t⁻¹))`
converges pointwise and normally on compact subsets of `ℂ × (ℂ \ {0})`.

## Main results

* `CKMA.hasSum_bessel_generating`: the bilateral Bessel generating series identity (**49.30**).
* `CKMA.normallySummableOn_bessel_generating`: normal convergence on compact subsets of
  `ℂ × (ℂ \ {0})`.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Filter Topology Complex
open scoped BigOperators ENNReal NNReal Nat

/-- Bidegree bijection for the product of the two exponential series. -/
private def besselIndexEquiv : ℤ × ℕ ≃ ℕ × ℕ where
  toFun p := if 0 ≤ p.1 then (p.2 + p.1.natAbs, p.2) else (p.2, p.2 + p.1.natAbs)
  invFun p := if p.2 ≤ p.1 then (↑(p.1 - p.2), p.2) else (-↑(p.2 - p.1), p.1)
  left_inv := by
    rintro ⟨n, k⟩
    by_cases hn : 0 ≤ n
    · have hk : k ≤ k + n.natAbs := Nat.le_add_right _ _
      dsimp
      rw [ite_eq_left hn, ite_eq_left hk]
      change (↑(k + n.natAbs - k), k) = (n, k)
      rw [Nat.add_sub_cancel_left, Int.natAbs_of_nonneg hn]
    · have hn' : n < 0 := lt_of_not_ge hn
      have hpos : 0 < n.natAbs := Nat.pos_of_ne_zero fun h =>
        hn'.ne (Int.natAbs_eq_zero.mp h)
      have hk : ¬ k + n.natAbs ≤ k := not_le.mpr (Nat.lt_add_of_pos_right hpos)
      dsimp
      rw [ite_eq_right hn, ite_eq_right hk]
      change (-↑(k + n.natAbs - k), k) = (n, k)
      rw [Nat.add_sub_cancel_left, Int.natCast_natAbs, abs_of_neg hn', neg_neg]
  right_inv := by
    rintro ⟨m, k⟩
    by_cases hk : k ≤ m
    · have h0 : 0 ≤ ((m - k : ℕ) : ℤ) := Nat.cast_nonneg _
      dsimp
      rw [ite_eq_left hk, ite_eq_left h0]
      change (k + ((m - k : ℕ) : ℤ).natAbs, k) = (m, k)
      rw [Int.natAbs_natCast, Nat.add_sub_of_le hk]
    · have hk' : m < k := lt_of_not_ge hk
      have hneg : ¬ 0 ≤ -((k - m : ℕ) : ℤ) :=
        not_le.mpr (Int.neg_neg_of_pos (by exact_mod_cast Nat.sub_pos_of_lt hk'))
      dsimp
      rw [ite_eq_right hk, ite_eq_right hneg]
      change (m, m + (-((k - m : ℕ) : ℤ)).natAbs) = (m, k)
      rw [Int.natAbs_neg, Int.natAbs_natCast, Nat.add_sub_of_le hk'.le]

/-- Nonnegative orders land on the diagonal `m = k + n`. -/
private theorem besselIndexEquiv_apply_nonneg {n : ℤ} (hn : 0 ≤ n) (k : ℕ) :
    besselIndexEquiv (n, k) = (k + n.natAbs, k) := by
  dsimp [besselIndexEquiv]
  rw [ite_eq_left hn]

/-- Negative orders land on the diagonal `k = m + |n|`. -/
private theorem besselIndexEquiv_apply_neg {n : ℤ} (hn : n < 0) (k : ℕ) :
    besselIndexEquiv (n, k) = (k, k + n.natAbs) := by
  dsimp [besselIndexEquiv]
  rw [ite_eq_right hn.not_ge]

/-- A nonnegative integer Bessel coefficient, read off the hypergeometric series. -/
private theorem besselSeries_term_eq (n k : ℕ) (z : ℂ) :
    (z / 2) ^ n * (regularizedHGFunCoeff 0 {(n : ℂ) + 1} k * (-(z / 2) ^ 2) ^ k) =
      (-1) ^ k * (z / 2) ^ (n + 2 * k) / ((k ! : ℂ) * ((n + k)! : ℂ)) := by
  have hC : regularizedHGFunCoeff 0 {(n : ℂ) + 1} k =
      1 / ((k ! : ℂ) * ((n + k)! : ℂ)) := by
    simp only [regularizedHGFunCoeff, Multiset.map_zero, Multiset.prod_zero,
      Multiset.map_singleton, Multiset.prod_singleton]
    rw [show (n : ℂ) + 1 + k = ↑(n + k) + 1 by push_cast; ring, Gamma_nat_eq_factorial]
  rw [hC, neg_pow, ← pow_mul (z / 2) 2 k]
  calc
    (z / 2) ^ n * (1 / ((k ! : ℂ) * ((n + k)! : ℂ)) * ((-1) ^ k * (z / 2) ^ (2 * k)))
      = (-1) ^ k * ((z / 2) ^ n * (z / 2) ^ (2 * k)) / ((k ! : ℂ) * ((n + k)! : ℂ)) := by
        ring
    _ = (-1) ^ k * (z / 2) ^ (n + 2 * k) / ((k ! : ℂ) * ((n + k)! : ℂ)) := by
      rw [← pow_add]

/-- The power series of a Bessel function of nonnegative integer order. -/
private theorem hasSum_besselJ_nat (n : ℕ) (z : ℂ) :
    HasSum (fun k : ℕ ↦ (-1) ^ k * (z / 2) ^ (n + 2 * k) /
        ((k ! : ℂ) * ((n + k)! : ℂ)))
      (besselJ (n : ℂ) z) := by
  let w : ℂ := -(z / 2) ^ 2
  have hsum : Summable fun k : ℕ ↦ (regularizedHGFunSeries 0 {(n : ℂ) + 1}) k fun _ ↦ w :=
    (regularizedHGFunSeries 0 {(n : ℂ) + 1}).summable
      (by rw [radius_regularizedHGFunSeries_zero_eq_top, Metric.eball_top]; exact trivial)
  rw [besselJ, cpow_natCast]
  convert hsum.hasSum.mul_left ((z / 2) ^ n) using 1
  · ext k
    rw [regularizedHGFunSeries, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]
    exact (besselSeries_term_eq n k z).symm
  · rw [regularizedHGFun, FormalMultilinearSeries.sum]

/-- A factor from `exp((z/2) t)` times one from `exp(-(z/2) t⁻¹)`, at nonnegative order. -/
private theorem expPair_nonneg_eq (z t : ℂ) (ht : t ≠ 0) (n k : ℕ) :
    ((z / 2) * t) ^ (k + n) / ((k + n)! : ℂ) *
        ((-((z / 2) * t⁻¹)) ^ k / (k ! : ℂ)) =
      ((-1) ^ k * (z / 2) ^ (n + 2 * k) / ((k ! : ℂ) * ((n + k)! : ℂ))) * t ^ n := by
  have hfac : ((k + n)! : ℂ) = ((n + k)! : ℂ) := by simp [Nat.add_comm]
  have hnum :
      ((z / 2) * t) ^ (k + n) * (-((z / 2) * t⁻¹)) ^ k =
        (-1) ^ k * (z / 2) ^ (n + 2 * k) * t ^ n := by
    rw [pow_add ((z / 2) * t) k n, neg_pow, mul_pow (z / 2) t k, mul_pow (z / 2) t n,
      mul_pow (z / 2) (t⁻¹) k]
    calc
      (z / 2) ^ k * t ^ k * ((z / 2) ^ n * t ^ n) * ((-1) ^ k * ((z / 2) ^ k * (t⁻¹) ^ k))
        = (-1) ^ k * ((z / 2) ^ k * (z / 2) ^ k * (z / 2) ^ n) * (t ^ k * (t⁻¹) ^ k) *
            t ^ n := by ring
      _ = (-1) ^ k * (z / 2) ^ (k + k + n) * (t * t⁻¹) ^ k * t ^ n := by
        rw [← pow_add (z / 2) k k, ← pow_add (z / 2) (k + k) n, ← mul_pow t (t⁻¹) k]
      _ = (-1) ^ k * (z / 2) ^ (n + 2 * k) * t ^ n := by
        rw [mul_inv_cancel₀ ht, one_pow, mul_one, Nat.add_comm (k + k) n, ← Nat.two_mul]
  calc
    ((z / 2) * t) ^ (k + n) / ((k + n)! : ℂ) * ((-((z / 2) * t⁻¹)) ^ k / (k ! : ℂ))
      = ((z / 2) * t) ^ (k + n) * (-((z / 2) * t⁻¹)) ^ k /
          ((k ! : ℂ) * ((n + k)! : ℂ)) := by
        rw [div_mul_div_comm, hfac, mul_comm ((n + k)! : ℂ) (k ! : ℂ)]
    _ = (-1) ^ k * (z / 2) ^ (n + 2 * k) * t ^ n / ((k ! : ℂ) * ((n + k)! : ℂ)) := by
      rw [hnum]
    _ = ((-1) ^ k * (z / 2) ^ (n + 2 * k) / ((k ! : ℂ) * ((n + k)! : ℂ))) * t ^ n := by
      rw [← div_mul_eq_mul_div]

/-- A factor from `exp((z/2) t)` times one from `exp(-(z/2) t⁻¹)`, at negative order. -/
private theorem expPair_neg_eq (z t : ℂ) (ht : t ≠ 0) (m k : ℕ) :
    ((z / 2) * t) ^ k / (k ! : ℂ) * ((-((z / 2) * t⁻¹)) ^ (k + m) / ((k + m)! : ℂ)) =
      (-1) ^ m * ((-1) ^ k * (z / 2) ^ (m + 2 * k) / ((k ! : ℂ) * ((m + k)! : ℂ))) *
        t ^ (-m : ℤ) := by
  have hfac : ((k + m)! : ℂ) = ((m + k)! : ℂ) := by simp [Nat.add_comm]
  have hinv : (t⁻¹) ^ m = t ^ (-m : ℤ) := by rw [inv_pow, ← zpow_natCast, ← zpow_neg]
  have hnum :
      ((z / 2) * t) ^ k * (-((z / 2) * t⁻¹)) ^ (k + m) =
        (-1) ^ m * (-1) ^ k * (z / 2) ^ (m + 2 * k) * t ^ (-m : ℤ) := by
    rw [neg_pow ((z / 2) * t⁻¹) (k + m), pow_add ((-1 : ℂ)) k m,
      pow_add ((z / 2) * t⁻¹) k m, mul_pow (z / 2) t k, mul_pow (z / 2) (t⁻¹) k,
      mul_pow (z / 2) (t⁻¹) m, hinv]
    calc
      (z / 2) ^ k * t ^ k * (((-1) ^ k * (-1) ^ m) *
          (((z / 2) ^ k * (t⁻¹) ^ k) * ((z / 2) ^ m * t ^ (-m : ℤ))))
        = (-1) ^ m * (-1) ^ k * ((z / 2) ^ k * (z / 2) ^ k * (z / 2) ^ m) *
            (t ^ k * (t⁻¹) ^ k) * t ^ (-m : ℤ) := by ring
      _ = (-1) ^ m * (-1) ^ k * (z / 2) ^ (k + k + m) * (t * t⁻¹) ^ k *
            t ^ (-m : ℤ) := by
        rw [← pow_add (z / 2) k k, ← pow_add (z / 2) (k + k) m, ← mul_pow t (t⁻¹) k]
      _ = (-1) ^ m * (-1) ^ k * (z / 2) ^ (m + 2 * k) * t ^ (-m : ℤ) := by
        rw [mul_inv_cancel₀ ht, one_pow, mul_one, Nat.add_comm (k + k) m, ← Nat.two_mul]
  calc
    ((z / 2) * t) ^ k / (k ! : ℂ) * ((-((z / 2) * t⁻¹)) ^ (k + m) / ((k + m)! : ℂ))
      = ((z / 2) * t) ^ k * (-((z / 2) * t⁻¹)) ^ (k + m) /
          ((k ! : ℂ) * ((m + k)! : ℂ)) := by
        rw [div_mul_div_comm, hfac]
    _ = (-1) ^ m * (-1) ^ k * (z / 2) ^ (m + 2 * k) * t ^ (-m : ℤ) /
          ((k ! : ℂ) * ((m + k)! : ℂ)) := by
        rw [hnum]
    _ = (-1) ^ m * ((-1) ^ k * (z / 2) ^ (m + 2 * k) /
          ((k ! : ℂ) * ((m + k)! : ℂ))) * t ^ (-m : ℤ) := by
        rw [mul_assoc ((-1) ^ m) ((-1) ^ k),
          mul_assoc ((-1) ^ m) ((-1) ^ k * (z / 2) ^ (m + 2 * k)),
          mul_div_assoc ((-1) ^ m), mul_div_right_comm, ← mul_assoc]

/-- Comparison of the scalar Bessel majorants as the radius and the auxiliary bound grow. -/
private theorem besselMajorant_le {r R a A : ℝ} (hr : r ≤ R) (ha : a ≤ A) (hr0 : 0 ≤ r)
    (ha0 : 0 ≤ a) (n : ℕ) :
    Real.exp (r ^ 2) * (r * a) ^ n / n ! ≤ Real.exp (R ^ 2) * (R * A) ^ n / n ! := by
  have hR : 0 ≤ R := hr0.trans hr
  have hA : 0 ≤ A := ha0.trans ha
  have hmul : r * a ≤ R * A := mul_le_mul hr ha ha0 hR
  have hpow : (r * a) ^ n ≤ (R * A) ^ n := pow_le_pow_left₀ (mul_nonneg hr0 ha0) hmul n
  have hprod : Real.exp (r ^ 2) * (r * a) ^ n ≤ Real.exp (R ^ 2) * (R * A) ^ n :=
    mul_le_mul (Real.exp_le_exp.mpr (pow_le_pow_left₀ hr0 hr 2)) hpow
      (pow_nonneg (mul_nonneg hr0 ha0) n) (Real.exp_nonneg _)
  exact div_le_div_of_nonneg_right hprod (Nat.cast_nonneg (n !))

/-- Modulus bound for a Bessel function of nonnegative integer order. -/
private theorem norm_besselJ_nat_le (n : ℕ) (z : ℂ) :
    ‖besselJ (n : ℂ) z‖ ≤ Real.exp ((‖z‖ / 2) ^ 2) * (‖z‖ / 2) ^ n / n ! := by
  let r : ℝ := ‖z‖ / 2
  have hr0 : 0 ≤ r := div_nonneg (norm_nonneg _) (by norm_num)
  have hser := hasSum_besselJ_nat n z
  have hnorm (k : ℕ) :
      ‖(-1) ^ k * (z / 2) ^ (n + 2 * k) / ((k ! : ℂ) * ((n + k)! : ℂ))‖ =
        r ^ (n + 2 * k) / ((k ! : ℝ) * ((n + k)! : ℝ)) := by
    rw [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_pow, norm_div,
      norm_mul, norm_natCast, norm_natCast]
    have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [h2]
  have hle (k : ℕ) :
      r ^ (n + 2 * k) / ((k ! : ℝ) * ((n + k)! : ℝ)) ≤
        (r ^ n / n !) * ((r ^ 2) ^ k / k !) := by
    have hfac : (n ! : ℝ) ≤ ((n + k)! : ℝ) := by
      exact_mod_cast Nat.factorial_le (Nat.le_add_right n k)
    have hden : (n ! : ℝ) * (k ! : ℝ) ≤ ((n + k)! : ℝ) * (k ! : ℝ) :=
      mul_le_mul_of_nonneg_right hfac (Nat.cast_nonneg _)
    have hdiv : r ^ (n + 2 * k) / (((n + k)! : ℝ) * (k ! : ℝ)) ≤
        r ^ (n + 2 * k) / ((n ! : ℝ) * (k ! : ℝ)) :=
      div_le_div_of_nonneg_left (pow_nonneg hr0 _)
        (mul_pos (by exact_mod_cast Nat.factorial_pos n) (by exact_mod_cast Nat.factorial_pos k))
        (by simpa [mul_comm] using hden)
    calc
      r ^ (n + 2 * k) / ((k ! : ℝ) * ((n + k)! : ℝ))
        = r ^ (n + 2 * k) / (((n + k)! : ℝ) * (k ! : ℝ)) := by
          rw [mul_comm (k ! : ℝ) ((n + k)! : ℝ)]
      _ ≤ r ^ (n + 2 * k) / ((n ! : ℝ) * (k ! : ℝ)) := hdiv
      _ = (r ^ n / n !) * ((r ^ 2) ^ k / k !) := by
        rw [pow_add, pow_mul, div_mul_eq_div_div]
        ring
  have hcmp : Summable fun k : ℕ ↦ (r ^ 2) ^ k / k ! :=
    (NormedSpace.norm_expSeries_div_summable (r ^ 2)).of_norm
  have hterm : Summable fun k : ℕ ↦
      ‖(-1) ^ k * (z / 2) ^ (n + 2 * k) / ((k ! : ℂ) * ((n + k)! : ℂ))‖ := by
    refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun k ↦ ?_)
      (hcmp.mul_left (r ^ n / n !))
    rw [hnorm]
    exact hle k
  have hexp : ∑' k : ℕ, (r ^ 2) ^ k / k ! = Real.exp (r ^ 2) := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  calc
    ‖besselJ (n : ℂ) z‖ = ‖∑' k : ℕ, (-1) ^ k * (z / 2) ^ (n + 2 * k) /
        ((k ! : ℂ) * ((n + k)! : ℂ))‖ := by rw [hser.tsum_eq]
    _ ≤ ∑' k : ℕ, ‖(-1) ^ k * (z / 2) ^ (n + 2 * k) / ((k ! : ℂ) * ((n + k)! : ℂ))‖ :=
      norm_tsum_le_tsum_norm hterm
    _ ≤ ∑' k : ℕ, (r ^ n / n !) * ((r ^ 2) ^ k / k !) := by
      refine hterm.tsum_le_tsum (fun k ↦ ?_) (hcmp.mul_left (r ^ n / n !))
      rw [hnorm]
      exact hle k
    _ = Real.exp (r ^ 2) * r ^ n / n ! := by
      rw [tsum_mul_left, hexp, mul_comm, mul_div_assoc]

/-- Modulus bound for `J_n(z) t^n` at nonnegative integer order. -/
private theorem norm_bessel_generating_nonneg_le (n : ℕ) (z t : ℂ) :
    ‖besselJ (n : ℂ) z * t ^ n‖ ≤ Real.exp ((‖z‖ / 2) ^ 2) * (‖z‖ / 2 * ‖t‖) ^ n / n ! := by
  calc
    ‖besselJ (n : ℂ) z * t ^ n‖ = ‖besselJ (n : ℂ) z‖ * ‖t‖ ^ n := by rw [norm_mul, norm_pow]
    _ ≤ (Real.exp ((‖z‖ / 2) ^ 2) * (‖z‖ / 2) ^ n / n !) * ‖t‖ ^ n :=
      mul_le_mul_of_nonneg_right (norm_besselJ_nat_le n z) (pow_nonneg (norm_nonneg _) _)
    _ = Real.exp ((‖z‖ / 2) ^ 2) * (‖z‖ / 2 * ‖t‖) ^ n / n ! := by
      rw [div_mul_eq_mul_div, mul_assoc, ← mul_pow]

/-- Modulus bound for `J_{-n}(z) t^{-n}`. -/
private theorem norm_bessel_generating_neg_le (n : ℕ) (z t : ℂ) :
    ‖besselJ (-(n : ℤ)) z * t ^ (-n : ℤ)‖ ≤
      Real.exp ((‖z‖ / 2) ^ 2) * (‖z‖ / 2 * ‖t‖⁻¹) ^ n / n ! := by
  have hsign : ‖(-1 : ℂ) ^ (n : ℤ)‖ = 1 := by rw [norm_zpow, norm_neg, norm_one, one_zpow]
  rw [besselJ_neg_int, zpow_neg, norm_mul, norm_mul, hsign, one_mul, norm_inv, norm_zpow,
    zpow_natCast, Int.cast_natCast]
  calc
    ‖besselJ (n : ℂ) z‖ * (‖t‖ ^ n)⁻¹
      ≤ (Real.exp ((‖z‖ / 2) ^ 2) * (‖z‖ / 2) ^ n / n !) * (‖t‖ ^ n)⁻¹ :=
        mul_le_mul_of_nonneg_right (norm_besselJ_nat_le n z) (inv_nonneg.mpr (pow_nonneg
          (norm_nonneg _) _))
    _ = Real.exp ((‖z‖ / 2) ^ 2) * (‖z‖ / 2 * ‖t‖⁻¹) ^ n / n ! := by
      rw [← inv_pow, div_mul_eq_mul_div, mul_assoc, ← mul_pow]

/-- **49.30**: the bilateral Bessel generating series. -/
theorem hasSum_bessel_generating (z : ℂ) {t : ℂ} (ht : t ≠ 0) :
    HasSum (fun n : ℤ ↦ Complex.besselJ (n : ℂ) z * t ^ n)
      (Complex.exp ((z / 2) * (t - t⁻¹))) := by
  let term : ℕ → ℕ → ℂ := fun m k ↦
    ((z / 2) * t) ^ m / (m ! : ℂ) * ((-((z / 2) * t⁻¹)) ^ k / (k ! : ℂ))
  have hprod : Summable fun p : ℕ × ℕ ↦ term p.1 p.2 :=
    summable_mul_of_summable_norm
      (NormedSpace.norm_expSeries_div_summable ((z / 2) * t))
      (NormedSpace.norm_expSeries_div_summable (-((z / 2) * t⁻¹)))
  have hexp := (NormedSpace.expSeries_div_hasSum_exp ((z / 2) * t)).mul
    (NormedSpace.expSeries_div_hasSum_exp (-((z / 2) * t⁻¹))) hprod
  rw [← NormedSpace.exp_add] at hexp
  have harg : (z / 2) * t + -((z / 2) * t⁻¹) = (z / 2) * (t - t⁻¹) := by ring
  rw [harg, ← exp_eq_exp_ℂ] at hexp
  have hre : HasSum (fun p : ℤ × ℕ ↦ term (besselIndexEquiv p).1 (besselIndexEquiv p).2)
      (exp ((z / 2) * (t - t⁻¹))) :=
    (besselIndexEquiv.hasSum_iff).mpr hexp
  refine hre.prod_fiberwise fun n ↦ ?_
  by_cases hn : 0 ≤ n
  · let m : ℕ := n.natAbs
    have hnm : n = m := by rw [Int.natCast_natAbs, abs_of_nonneg hn]
    have hser := (hasSum_besselJ_nat m z).mul_right (t ^ m)
    convert hser using 1
    · ext k
      rw [besselIndexEquiv_apply_nonneg hn]
      simpa [term, m] using expPair_nonneg_eq z t ht m k
    · rw [hnm, zpow_natCast, Int.cast_natCast]
  · have hn' : n < 0 := lt_of_not_ge hn
    let m : ℕ := n.natAbs
    have hnm : n = -(m : ℤ) := by
      rw [← neg_neg n, Int.natCast_natAbs, abs_of_neg hn']
    have hser := ((hasSum_besselJ_nat m z).mul_left ((-1) ^ m)).mul_right (t ^ (-m : ℤ))
    convert hser using 1
    · ext k
      rw [besselIndexEquiv_apply_neg hn']
      simpa [term, m] using expPair_neg_eq z t ht m k
    · rw [hnm, Int.cast_neg, besselJ_neg_int, zpow_natCast, Int.cast_natCast]

/-- Normal convergence on compact sets in `(z,t)` away from `t=0`, including uniformity in `z`. -/
theorem normallySummableOn_bessel_generating :
    NormallySummableOn (fun n : ℤ ↦ fun p : ℂ × ℂ ↦
      Complex.besselJ (n : ℂ) p.1 * p.2 ^ n) {p | p.2 ≠ 0} := by
  intro K hK hKs
  obtain ⟨R, hR⟩ := hK.exists_bound_of_continuousOn
    (continuous_fst.continuousOn.mono (Set.subset_univ _))
  obtain ⟨S, hS⟩ := hK.exists_bound_of_continuousOn
    (continuous_snd.continuousOn.mono (Set.subset_univ _))
  have hinv : ContinuousOn (fun p : ℂ × ℂ ↦ (p.2)⁻¹) K :=
    (continuous_snd.continuousOn.mono hKs).inv₀ fun _ hp ↦ hKs hp
  obtain ⟨T, hT⟩ := hK.exists_bound_of_continuousOn hinv
  let R₀ : ℝ := max R 0
  let S₀ : ℝ := max S 0
  let T₀ : ℝ := max T 0
  let C : ℝ := Real.exp ((R₀ / 2) ^ 2)
  let bound : ℤ → ℝ := fun n ↦
    if 0 ≤ n then C * (R₀ / 2 * S₀) ^ n.natAbs / (n.natAbs)!
    else C * (R₀ / 2 * T₀) ^ n.natAbs / (n.natAbs)!
  have hpoint (n : ℤ) (p : ℂ × ℂ) (hp : p ∈ K) :
      ‖besselJ (n : ℂ) p.1 * p.2 ^ n‖ ≤ bound n := by
    have hz : ‖p.1‖ ≤ R₀ := (hR p hp).trans (le_max_left _ _)
    have ht : ‖p.2‖ ≤ S₀ := (hS p hp).trans (le_max_left _ _)
    have hti : ‖p.2⁻¹‖ ≤ T₀ := (hT p hp).trans (le_max_left _ _)
    have hz' : ‖p.1‖ / 2 ≤ R₀ / 2 := div_le_div_of_nonneg_right hz (by norm_num)
    by_cases hn : 0 ≤ n
    · let m : ℕ := n.natAbs
      have hnm : n = m := by rw [Int.natCast_natAbs, abs_of_nonneg hn]
      unfold bound
      rw [ite_eq_left hn, hnm, zpow_natCast, Int.cast_natCast]
      exact (norm_bessel_generating_nonneg_le m p.1 p.2).trans
        (besselMajorant_le hz' ht (div_nonneg (norm_nonneg _) (by norm_num)) (norm_nonneg _) m)
    · have hn' : n < 0 := lt_of_not_ge hn
      let m : ℕ := n.natAbs
      have hnm : n = -(m : ℤ) := by rw [← neg_neg n, Int.natCast_natAbs, abs_of_neg hn']
      have ha : ‖p.2‖⁻¹ ≤ T₀ := by rw [← norm_inv]; exact hti
      unfold bound
      rw [ite_eq_right hn, hnm, Int.cast_neg, Int.natAbs_neg, Int.natAbs_natCast]
      exact (norm_bessel_generating_neg_le m p.1 p.2).trans
        (besselMajorant_le hz' ha (div_nonneg (norm_nonneg _) (by norm_num))
          (inv_nonneg.mpr (norm_nonneg _)) m)
  have hbound_nonneg (n : ℤ) : 0 ≤ bound n := by
    by_cases hn : 0 ≤ n
    · unfold bound
      rw [ite_eq_left hn]
      positivity
    · unfold bound
      rw [ite_eq_right hn]
      positivity
  have hsup (n : ℤ) :
      sSup ((fun p : ℂ × ℂ ↦ ‖besselJ (n : ℂ) p.1 * p.2 ^ n‖) '' K) ≤ bound n :=
    Real.sSup_le (fun y hy ↦ by
      obtain ⟨p, hp, rfl⟩ := hy
      exact hpoint n p hp) (hbound_nonneg n)
  have hmaj (A : ℝ) : Summable fun m : ℕ ↦ C * (R₀ / 2 * A) ^ m / m ! := by
    refine ((NormedSpace.norm_expSeries_div_summable (R₀ / 2 * A)).of_norm.mul_left C).congr
      fun _ ↦ (mul_div_assoc _ _ _).symm
  have hpos : Summable fun m : ℕ ↦ bound m := by
    refine (hmaj S₀).congr fun m ↦ ?_
    unfold bound
    rw [ite_eq_left (Nat.cast_nonneg m), Int.natAbs_natCast]
  have hneg : Summable fun m : ℕ ↦ bound (-m) := by
    refine (hmaj T₀).congr fun m ↦ ?_
    by_cases hm : m = 0
    · simp [hm, bound, C, pow_zero, Nat.factorial_zero, div_one, mul_one]
    · have hlt : ¬ 0 ≤ -(m : ℤ) :=
        not_le.mpr (Int.neg_neg_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hm))
      unfold bound
      rw [ite_eq_right hlt, Int.natAbs_neg, Int.natAbs_natCast]
  refine ⟨fun n ↦ ⟨bound n, fun y hy ↦ ?_⟩, ?_⟩
  · obtain ⟨p, hp, rfl⟩ := hy
    exact hpoint n p hp
  · refine Summable.of_nat_of_neg ?_ ?_
    · exact Summable.of_nonneg_of_le (fun m ↦ Real.sSup_nonneg fun y hy ↦ by
        obtain ⟨_, _, rfl⟩ := hy
        exact norm_nonneg _) (fun m ↦ by simpa using hsup m) hpos
    · exact Summable.of_nonneg_of_le (fun m ↦ Real.sSup_nonneg fun y hy ↦ by
        obtain ⟨_, _, rfl⟩ := hy
        exact norm_nonneg _) (fun m ↦ by simpa using hsup (-m)) hneg

end CKMA
