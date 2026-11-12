/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Stirling
public import Mathlib.Analysis.MeanInequalities
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Carleman inequality and its optimal constant

Geometric means of the first `n+1` nonnegative sequence entries and Carleman's summability
bound with constant `exp 1`. The optimality statement quantifies over finitely supported
nonnegative sequences.

The upper bound uses weighted AM-GM (`Real.geom_mean_le_arith_mean_weighted`) on the terms
`(k + 1) * a k`, the estimate `log (1 + 1 / k) ≤ 1 / k` (`Real.log_le_sub_one_of_pos`),
the telescoping identity `∑_{n ≥ k} 1/((n + 1) (n + 2)) = 1/(k + 1)`, and comparison for
nonnegative series (`summable_of_sum_range_le`). Sharpness uses
`Stirling.factorial_isEquivalent_stirling`, the root limit `x ^ (1 / x) → 1`, and divergence of
the harmonic series. Real powers, finite products and Stirling asymptotics use Mathlib
conventions.
Source: GAPS 11.38.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Finset Filter Topology Asymptotics
open scoped BigOperators Nat

/-- The geometric mean of the first `n + 1` entries of a sequence indexed from zero. -/
def prefixGeometricMean (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  (∏ k ∈ Finset.range (n + 1), a k) ^ (1 / (n + 1 : ℝ))

/-- `∑_{k < m} (k + 1) log (1 + 1/(k + 1)) = m log (m + 1) - log (m !)`. -/
private lemma sum_succ_mul_log_one_add_inv (m : ℕ) :
    ∑ k ∈ range m, (k + 1 : ℝ) * Real.log (1 + 1 / (k + 1 : ℝ)) =
      (m : ℝ) * Real.log (m + 1) - Real.log (m !) := by
  induction m with
  | zero => simp [Real.log_one]
  | succ m ih =>
    rw [sum_range_succ, ih]
    have hdiv : Real.log (1 + 1 / (m + 1 : ℝ)) = Real.log (m + 2) - Real.log (m + 1) := by
      rw [← Real.log_div (by positivity) (by positivity)]
      congr 1
      field
    have hfact : Real.log ((m + 1)! : ℝ) = Real.log (m ! : ℝ) + Real.log ((m : ℝ) + 1) := by
      rw [Nat.factorial_succ, Nat.cast_mul, mul_comm,
        Real.log_mul (by positivity) (by positivity)]
      have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by norm_cast
      rw [hcast]
    rw [hdiv, hfact]
    push_cast
    ring

/-- Each summand in the factorial expansion is at most `1`. -/
private lemma succ_mul_log_one_add_inv_le_one (k : ℕ) :
    (k + 1 : ℝ) * Real.log (1 + 1 / (k + 1 : ℝ)) ≤ 1 := by
  have hpos : 0 < 1 + 1 / (k + 1 : ℝ) := by positivity
  have hlog : Real.log (1 + 1 / (k + 1 : ℝ)) ≤ 1 / (k + 1 : ℝ) := by
    have hsub := Real.log_le_sub_one_of_pos hpos
    have heq : 1 + 1 / (k + 1 : ℝ) - 1 = 1 / (k + 1 : ℝ) := by ring
    simpa [heq] using hsub
  calc
    (k + 1 : ℝ) * Real.log (1 + 1 / (k + 1 : ℝ))
        ≤ (k + 1 : ℝ) * (1 / (k + 1 : ℝ)) :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = 1 := by field

/-- `(m !)` is at least `((m + 1) / e) ^ m`, by `log (1 + 1/k) ≤ 1/k`. -/
private lemma factorial_ge_carleman (m : ℕ) :
    ((m + 1 : ℝ) / Real.exp 1) ^ (m : ℝ) ≤ (m ! : ℝ) := by
  have hsum : ∑ k ∈ range m, (k + 1 : ℝ) * Real.log (1 + 1 / (k + 1 : ℝ)) ≤ m := by
    calc
      _ ≤ ∑ k ∈ range m, (1 : ℝ) :=
        sum_le_sum fun k _ => succ_mul_log_one_add_inv_le_one k
      _ = m := by simp
  have hlog : (m : ℝ) * Real.log ((m + 1 : ℝ) / Real.exp 1) ≤ Real.log (m ! : ℝ) := by
    rw [Real.log_div (by positivity) (Real.exp_ne_zero _), Real.log_exp]
    have hid := sum_succ_mul_log_one_add_inv m
    linarith
  calc
    ((m + 1 : ℝ) / Real.exp 1) ^ (m : ℝ)
        = Real.exp ((m : ℝ) * Real.log ((m + 1 : ℝ) / Real.exp 1)) := by
          rw [Real.rpow_def_of_pos (by positivity), mul_comm]
    _ ≤ Real.exp (Real.log (m ! : ℝ)) := (Real.exp_le_exp).2 hlog
    _ = (m ! : ℝ) := Real.exp_log (by positivity)

/-- Weighted AM-GM and the factorial bound give the summand estimate in Carleman's inequality. -/
private lemma prefixGeometricMean_le_carleman {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (n : ℕ) :
    prefixGeometricMean a n ≤
      Real.exp 1 * (∑ k ∈ range (n + 1), (k + 1 : ℝ) * a k) / ((n + 1 : ℝ) * (n + 2)) := by
  set m : ℕ := n + 1
  set s : Finset ℕ := range m
  set z : ℕ → ℝ := fun k => (k + 1 : ℝ) * a k
  have hm : (m : ℝ) ≠ 0 := by positivity
  have hw : ∀ i ∈ s, 0 ≤ (1 : ℝ) / m := fun _ _ => by positivity
  have hw' : ∑ i ∈ s, (1 : ℝ) / m = 1 := by
    simp only [s, sum_const, card_range, nsmul_eq_mul]
    field
  have hz : ∀ i ∈ s, 0 ≤ z i := fun _ _ => mul_nonneg (by positivity) (ha _)
  have hAMGM := Real.geom_mean_le_arith_mean_weighted s (fun _ => (1 : ℝ) / m) z hw hw' hz
  have hfact : ∏ i ∈ s, (i + 1 : ℝ) = (m ! : ℝ) := by
    simp only [s]
    have hcast : ∏ i ∈ range m, (i + 1 : ℝ) = ↑(∏ i ∈ range m, (i + 1)) := by
      rw [prod_natCast]
      refine prod_congr rfl fun i _ => ?_
      norm_cast
    rw [hcast, prod_range_add_one_eq_factorial]
  have hgeom : (∏ i ∈ s, a i) ^ (1 / (m : ℝ)) * (m ! : ℝ) ^ (1 / (m : ℝ)) ≤
      (1 / (m : ℝ)) * ∑ i ∈ s, z i := by
    calc
      (∏ i ∈ s, a i) ^ (1 / (m : ℝ)) * (m ! : ℝ) ^ (1 / (m : ℝ))
          = ((∏ i ∈ s, a i) * (m ! : ℝ)) ^ (1 / (m : ℝ)) := by
            rw [← Real.mul_rpow (prod_nonneg fun i _ => ha i) (by positivity)]
      _ = (∏ i ∈ s, z i) ^ (1 / (m : ℝ)) := by
            rw [mul_comm, ← hfact, ← prod_mul_distrib]
      _ = ∏ i ∈ s, z i ^ ((1 : ℝ) / m) := by
            rw [← Real.finsetProd_rpow s z hz]
      _ ≤ ∑ i ∈ s, (1 / (m : ℝ)) * z i := hAMGM
      _ = (1 / (m : ℝ)) * ∑ i ∈ s, z i := by rw [← mul_sum]
  have hroot : 0 < (m ! : ℝ) ^ (1 / (m : ℝ)) := Real.rpow_pos_of_pos (by positivity) _
  have hmean : (∏ i ∈ s, a i) ^ (1 / (m : ℝ)) ≤
      ((1 / (m : ℝ)) * ∑ i ∈ s, z i) / (m ! : ℝ) ^ (1 / (m : ℝ)) :=
    (le_div_iff₀ hroot).mpr hgeom
  have hbase : (m + 1 : ℝ) / Real.exp 1 ≤ (m ! : ℝ) ^ (1 / (m : ℝ)) := by
    have hrpow := Real.rpow_le_rpow (by positivity) (factorial_ge_carleman m)
      (by positivity : 0 ≤ 1 / (m : ℝ))
    rwa [← Real.rpow_mul (by positivity), mul_one_div_cancel hm, Real.rpow_one] at hrpow
  have hinv : ((m ! : ℝ) ^ (1 / (m : ℝ)))⁻¹ ≤ Real.exp 1 / (m + 1 : ℝ) := by
    have hpos : 0 < (m + 1 : ℝ) / Real.exp 1 := by positivity
    simpa [inv_div] using
      (inv_le_inv₀ (Real.rpow_pos_of_pos (Nat.cast_pos.mpr (Nat.factorial_pos m)) _) hpos).mpr
        hbase
  have hcoeff : 1 / ((m : ℝ) * (m ! : ℝ) ^ (1 / (m : ℝ))) ≤
      Real.exp 1 / ((m : ℝ) * (m + 1)) := by
    calc
      1 / ((m : ℝ) * (m ! : ℝ) ^ (1 / (m : ℝ)))
          = ((m ! : ℝ) ^ (1 / (m : ℝ)))⁻¹ * (1 / (m : ℝ)) := by
            rw [one_div, mul_inv, inv_eq_one_div, mul_comm]
      _ ≤ (Real.exp 1 / (m + 1 : ℝ)) * (1 / (m : ℝ)) := by
            gcongr
      _ = Real.exp 1 / ((m : ℝ) * (m + 1)) := by
            field
  calc
    prefixGeometricMean a n = (∏ i ∈ s, a i) ^ (1 / (m : ℝ)) := by simp [prefixGeometricMean, s, m]
    _ ≤ ((1 / (m : ℝ)) * ∑ i ∈ s, z i) / (m ! : ℝ) ^ (1 / (m : ℝ)) := hmean
    _ = (∑ i ∈ s, z i) * (1 / ((m : ℝ) * (m ! : ℝ) ^ (1 / (m : ℝ)))) := by
          field
    _ ≤ (∑ i ∈ s, z i) * (Real.exp 1 / ((m : ℝ) * (m + 1))) := by
          exact mul_le_mul_of_nonneg_left hcoeff (sum_nonneg fun i hi => hz i hi)
    _ = Real.exp 1 * (∑ i ∈ s, z i) / ((m : ℝ) * (m + 1)) := by
          rw [mul_div_assoc', mul_comm]
    _ = Real.exp 1 * (∑ k ∈ range (n + 1), (k + 1 : ℝ) * a k) /
          ((n + 1 : ℝ) * (n + 2)) := by
          simp only [s, z, m]
          push_cast
          ring

/-- `∑_{n < M} 1/((n + 1) (n + 2)) = 1 - 1/(M + 1)`. -/
private lemma sum_range_one_div_succ_succ (M : ℕ) :
    ∑ n ∈ range M, (1 : ℝ) / ((n + 1) * (n + 2)) = 1 - 1 / (M + 1 : ℝ) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [sum_range_succ, ih]
    push_cast
    field

/-- The partial tail `∑_{k ≤ n < N} 1/((n + 1) (n + 2))` equals `1/(k + 1) - 1/(N + 1)`. -/
private lemma sum_Ico_one_div_succ_succ {k N : ℕ} (hk : k ≤ N) :
    ∑ n ∈ Ico k N, (1 : ℝ) / ((n + 1) * (n + 2)) = 1 / (k + 1 : ℝ) - 1 / (N + 1 : ℝ) := by
  have h := sum_range_add_sum_Ico (fun n => (1 : ℝ) / ((n + 1) * (n + 2))) hk
  rw [sum_range_one_div_succ_succ, sum_range_one_div_succ_succ] at h
  linarith

/-- Interchanging the nonnegative triangle and telescoping recovers the partial sums of `a`. -/
private lemma sum_carleman_weights_le {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (N : ℕ) :
    ∑ n ∈ range N, (∑ k ∈ range (n + 1), (k + 1 : ℝ) * a k) / ((n + 1 : ℝ) * (n + 2)) ≤
      ∑ k ∈ range N, a k := by
  simp_rw [div_eq_mul_inv, sum_mul, ← one_div, range_eq_Ico]
  rw [(sum_Ico_Ico_comm 0 N fun k n =>
    (k + 1 : ℝ) * a k * (1 / ((n + 1 : ℝ) * (n + 2)))).symm]
  refine sum_le_sum fun k hk => ?_
  rw [← mul_sum]
  have hkN : k ≤ N := Nat.le_of_lt (mem_Ico.mp hk).2
  calc
    (k + 1 : ℝ) * a k * ∑ n ∈ Ico k N, (1 / ((n + 1 : ℝ) * (n + 2)))
        = (k + 1 : ℝ) * a k * (1 / (k + 1 : ℝ) - 1 / (N + 1 : ℝ)) := by
          rw [sum_Ico_one_div_succ_succ hkN]
    _ ≤ (k + 1 : ℝ) * a k * (1 / (k + 1 : ℝ)) := by
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (by positivity) (ha k))
          have : 0 ≤ 1 / (N + 1 : ℝ) := by positivity
          linarith
    _ = a k := by field

/-- **11.38**: Carleman's bound, with summability included in the conclusion. -/
theorem carleman {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a) :
    Summable (prefixGeometricMean a) ∧
      (∑' n, prefixGeometricMean a n) ≤ Real.exp 1 * ∑' n, a n := by
  have hG (n : ℕ) : 0 ≤ prefixGeometricMean a n := by
    unfold prefixGeometricMean
    exact Real.rpow_nonneg (prod_nonneg fun k _ => ha k) _
  have hpartial (N : ℕ) :
      ∑ n ∈ range N, prefixGeometricMean a n ≤ Real.exp 1 * ∑' n, a n := by
    calc
      ∑ n ∈ range N, prefixGeometricMean a n
          ≤ ∑ n ∈ range N, Real.exp 1 *
              (∑ k ∈ range (n + 1), (k + 1 : ℝ) * a k) / ((n + 1 : ℝ) * (n + 2)) :=
            sum_le_sum fun n _ => prefixGeometricMean_le_carleman ha n
      _ = Real.exp 1 * ∑ n ∈ range N,
            (∑ k ∈ range (n + 1), (k + 1 : ℝ) * a k) / ((n + 1 : ℝ) * (n + 2)) := by
            simp_rw [mul_div_assoc]
            rw [← mul_sum]
      _ ≤ Real.exp 1 * ∑ k ∈ range N, a k :=
            mul_le_mul_of_nonneg_left (sum_carleman_weights_le ha N) (Real.exp_pos _).le
      _ ≤ Real.exp 1 * ∑' n, a n :=
            mul_le_mul_of_nonneg_left
              (hs.sum_le_tsum (range N) fun i _ => ha i) (Real.exp_pos _).le
  exact ⟨summable_of_sum_range_le hG hpartial, Real.tsum_le_of_sum_range_le hG hpartial⟩

/-- A positive sequence tending to `1` has `n`th roots tending to `1`. -/
private lemma tendsto_rpow_nat_inv_one {w : ℕ → ℝ} (hw : Tendsto w atTop (𝓝 1)) :
    Tendsto (fun n : ℕ => w n ^ (n : ℝ)⁻¹) atTop (𝓝 1) := by
  have hpos : ∀ᶠ n : ℕ in atTop, 0 < w n := by
    filter_upwards [hw.eventually (Ioi_mem_nhds zero_lt_one)] with n hn
    exact hn
  have hlog : Tendsto (fun n : ℕ => Real.log (w n) / (n : ℝ)) atTop (𝓝 0) := by
    have hlogw : Tendsto (fun n : ℕ => Real.log (w n)) atTop (𝓝 0) := by
      have hcomp := (Real.continuousAt_log one_ne_zero).tendsto.comp hw
      simp only [Real.log_one] at hcomp
      exact hcomp
    simpa [div_eq_mul_inv] using hlogw.mul tendsto_inv_atTop_nhds_zero_nat
  refine Tendsto.congr' ?_ (by
    simpa [Real.exp_zero, Function.comp_apply] using (Real.continuous_exp.tendsto 0).comp hlog)
  filter_upwards [hpos] with n hn
  rw [Function.comp_apply, Real.rpow_def_of_pos hn, div_eq_mul_inv]

/-- `n / (n !) ^ (1 / n)` tends to `e`. -/
private lemma tendsto_self_div_factorial_rpow :
    Tendsto (fun n : ℕ => (n : ℝ) / (n ! : ℝ) ^ (n : ℝ)⁻¹) atTop (𝓝 (Real.exp 1)) := by
  set s : ℕ → ℝ := fun n => Real.sqrt (2 * n * Real.pi) * ((n : ℝ) / Real.exp 1) ^ n
  have hs_pos : ∀ᶠ n : ℕ in atTop, 0 < s n := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    positivity
  have hratio : Tendsto (fun n : ℕ => (n ! : ℝ) / s n) atTop (𝓝 1) :=
    (isEquivalent_iff_tendsto_one (hs_pos.mono fun _ h => h.ne')).mp
      Stirling.factorial_isEquivalent_stirling
  have hroot : Tendsto (fun n : ℕ => ((n ! : ℝ) / s n) ^ (n : ℝ)⁻¹) atTop (𝓝 1) :=
    tendsto_rpow_nat_inv_one hratio
  have hsqrt : Tendsto (fun n : ℕ => Real.sqrt (2 * (n : ℝ) * Real.pi) ^ (n : ℝ)⁻¹)
      atTop (𝓝 1) := by
    have hlogn : Tendsto (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
      (Real.isLittleO_log_id_atTop.comp_tendsto tendsto_natCast_atTop_atTop).tendsto_div_nhds_zero
    have hconst : Tendsto (fun n : ℕ => Real.log (2 * Real.pi) / (2 * (n : ℝ))) atTop (𝓝 0) := by
      refine (tendsto_const_div_atTop_nhds_zero_nat (Real.log (2 * Real.pi) / 2)).congr fun n => ?_
      ring
    have hlog : Tendsto (fun n : ℕ => Real.log (2 * (n : ℝ) * Real.pi) / (2 * (n : ℝ)))
        atTop (𝓝 0) := by
      have hsum := hconst.add ((tendsto_const_nhds (x := (1 : ℝ) / 2)).mul hlogn)
      have hsum0 : Tendsto (fun n : ℕ => Real.log (2 * Real.pi) / (2 * (n : ℝ)) +
          (1 / 2) * (Real.log (n : ℝ) / (n : ℝ))) atTop (𝓝 0) := by
        simpa [zero_add, mul_zero] using hsum
      refine hsum0.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with n hn
      have hn0 : (n : ℝ) ≠ 0 := by positivity
      rw [show 2 * (n : ℝ) * Real.pi = (n : ℝ) * (2 * Real.pi) by ring,
        Real.log_mul hn0 (mul_ne_zero two_ne_zero Real.pi_ne_zero)]
      ring
    have hexp := (Real.continuous_exp.tendsto (0 : ℝ)).comp hlog
    have hexp1 : Tendsto (Real.exp ∘ fun n : ℕ =>
        Real.log (2 * (n : ℝ) * Real.pi) / (2 * (n : ℝ))) atTop (𝓝 1) := by
      simpa [Real.exp_zero] using hexp
    refine hexp1.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hx : 0 < 2 * (n : ℝ) * Real.pi := by positivity
    rw [Function.comp_apply, Real.rpow_def_of_pos (Real.sqrt_pos.2 hx), Real.log_sqrt hx.le]
    ring
  have hden : Tendsto (fun n : ℕ => ((n ! : ℝ) / s n) ^ (n : ℝ)⁻¹ *
      Real.sqrt (2 * (n : ℝ) * Real.pi) ^ (n : ℝ)⁻¹) atTop (𝓝 1) := by
    simpa using hroot.mul hsqrt
  have hquot : Tendsto (fun n : ℕ => Real.exp 1 / (((n ! : ℝ) / s n) ^ (n : ℝ)⁻¹ *
      Real.sqrt (2 * (n : ℝ) * Real.pi) ^ (n : ℝ)⁻¹)) atTop (𝓝 (Real.exp 1)) := by
    convert (tendsto_const_nhds (x := Real.exp 1)).div hden one_ne_zero using 1
    simp [div_one]
  refine Tendsto.congr' ?_ hquot
  filter_upwards [eventually_gt_atTop 0, hs_pos] with n hn hs
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hphi : 0 < (n ! : ℝ) / s n := div_pos (by positivity) hs
  set phi : ℝ := (n ! : ℝ) / s n
  set sigmaR : ℝ := Real.sqrt (2 * (n : ℝ) * Real.pi)
  set base : ℝ := (n : ℝ) / Real.exp 1
  have hbasepos : 0 < base := by positivity
  have hsigma : 0 ≤ sigmaR := Real.sqrt_nonneg _
  have hfact : (n ! : ℝ) = phi * s n := by
    simpa [phi] using (div_mul_cancel₀ (n ! : ℝ) hs.ne').symm
  have hrpow : (n ! : ℝ) ^ (n : ℝ)⁻¹ = phi ^ (n : ℝ)⁻¹ * s n ^ (n : ℝ)⁻¹ := by
    rw [hfact, Real.mul_rpow hphi.le hs.le]
  have hbasepow : (base ^ n) ^ (n : ℝ)⁻¹ = base := by
    rw [← Real.rpow_natCast base n, ← Real.rpow_mul hbasepos.le, mul_inv_cancel₀ hn0,
      Real.rpow_one]
  have hspow : s n ^ (n : ℝ)⁻¹ = sigmaR ^ (n : ℝ)⁻¹ * base := by
    have hsdef : s n = sigmaR * base ^ n := rfl
    rw [hsdef, Real.mul_rpow hsigma (by positivity : 0 ≤ base ^ n), hbasepow]
  have hdiv : (n : ℝ) / (phi ^ (n : ℝ)⁻¹ * (sigmaR ^ (n : ℝ)⁻¹ * base)) =
      Real.exp 1 / (phi ^ (n : ℝ)⁻¹ * sigmaR ^ (n : ℝ)⁻¹) := by
    have hcancel : base * Real.exp 1 = (n : ℝ) := by
      rw [show base = (n : ℝ) / Real.exp 1 from rfl]
      field
    field_simp
    rw [← hcancel]
  symm
  calc
    (n : ℝ) / (n ! : ℝ) ^ (n : ℝ)⁻¹
        = (n : ℝ) / (phi ^ (n : ℝ)⁻¹ * s n ^ (n : ℝ)⁻¹) := by rw [hrpow]
    _ = (n : ℝ) / (phi ^ (n : ℝ)⁻¹ * (sigmaR ^ (n : ℝ)⁻¹ * base)) := by rw [hspow]
    _ = Real.exp 1 / (phi ^ (n : ℝ)⁻¹ * sigmaR ^ (n : ℝ)⁻¹) := hdiv

/-- The same limit shifted to factorials of `n + 1`. -/
private lemma tendsto_succ_div_factorial_rpow :
    Tendsto (fun n : ℕ => (n + 1 : ℝ) / ((n + 1)! : ℝ) ^ (1 / (n + 1 : ℝ))) atTop
      (𝓝 (Real.exp 1)) := by
  refine (tendsto_self_div_factorial_rpow.comp (tendsto_add_atTop_nat 1)).congr fun n => ?_
  rw [Function.comp_apply, inv_eq_one_div]
  push_cast
  rfl

/-- Harmonic averages of `1 / ((n + 1) !) ^ (1 / (n + 1))` tend to `e`. -/
private lemma tendsto_carleman_series_ratio :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ range N, 1 / ((n + 1)! : ℝ) ^ (1 / (n + 1 : ℝ))) /
        ∑ n ∈ range N, 1 / (n + 1 : ℝ)) atTop (𝓝 (Real.exp 1)) := by
  let b : ℕ → ℝ := fun n => (n + 1 : ℝ) / ((n + 1)! : ℝ) ^ (1 / (n + 1 : ℝ))
  let g : ℕ → ℝ := fun n => 1 / (n + 1 : ℝ)
  let c : ℕ → ℝ := fun n => 1 / ((n + 1)! : ℝ) ^ (1 / (n + 1 : ℝ))
  have hb : Tendsto b atTop (𝓝 (Real.exp 1)) := tendsto_succ_div_factorial_rpow
  have hg0 : ∀ n, 0 ≤ g n := fun _ => by positivity
  have hfo : (fun n => (b n - Real.exp 1) * g n) =o[atTop] g := by
    refine isLittleO_of_tendsto (fun n hgn => ?_) ?_
    · dsimp [g] at hgn
      exact absurd hgn (one_div_ne_zero (by positivity : (n + 1 : ℝ) ≠ 0))
    · have hsub := hb.sub (tendsto_const_nhds (x := Real.exp 1))
      have hsub0 : Tendsto (fun n => b n - Real.exp 1) atTop (𝓝 0) := by
        simpa [sub_self] using hsub
      refine hsub0.congr fun n => ?_
      have hgn : g n ≠ 0 := by positivity
      rw [mul_div_cancel_right₀ _ hgn]
  have hdiv :=
    (hfo.sum_range hg0 Real.tendsto_sum_range_one_div_nat_succ_atTop).tendsto_div_nhds_zero
  have havg := hdiv.add (tendsto_const_nhds (x := Real.exp 1))
  have havg' : Tendsto (fun N : ℕ =>
      (∑ n ∈ range N, (b n - Real.exp 1) * g n) / ∑ n ∈ range N, g n + Real.exp 1) atTop
      (𝓝 (Real.exp 1)) := by
    simpa [zero_add] using havg
  refine Tendsto.congr' ?_ havg'
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hsg : ∑ n ∈ range N, g n ≠ 0 := by
    refine ne_of_gt (sum_pos (fun n _ => ?_) (nonempty_range_iff.mpr (Nat.ne_of_gt hN)))
    positivity
  have hc : ∀ n, c n = b n * g n := by
    intro n
    dsimp [b, c, g]
    have hn0 : (n + 1 : ℝ) ≠ 0 := by positivity
    calc
      1 / ((n + 1)! : ℝ) ^ (1 / (n + 1 : ℝ))
          = (1 / (n + 1 : ℝ) * (n + 1)) / ((n + 1)! : ℝ) ^ (1 / (n + 1 : ℝ)) := by
            rw [div_mul_cancel₀ 1 hn0]
      _ = (1 / (n + 1 : ℝ)) * ((n + 1) / ((n + 1)! : ℝ) ^ (1 / (n + 1 : ℝ))) := by
            rw [mul_div_assoc]
      _ = b n * g n := by ring
  have hsub : ∑ n ∈ range N, (b n - Real.exp 1) * g n =
      ∑ n ∈ range N, c n - Real.exp 1 * ∑ n ∈ range N, g n := by
    simp_rw [sub_mul, sum_sub_distrib, ← mul_sum, hc]
  rw [hsub, sub_div, mul_div_cancel_right₀ _ hsg, sub_add_cancel]

/-- Geometric means of the truncated harmonic sequence. -/
private lemma prefixGeometricMean_trunc (N n : ℕ) :
    prefixGeometricMean (fun k => if k < N then (1 : ℝ) / (k + 1) else 0) n =
      if n < N then 1 / ((n + 1)! : ℝ) ^ (1 / (n + 1 : ℝ)) else 0 := by
  by_cases hn : n < N
  · simp only [hn, ite_true]
    unfold prefixGeometricMean
    have hprod : ∏ k ∈ range (n + 1), (if k < N then (1 : ℝ) / (k + 1) else 0) =
        ∏ k ∈ range (n + 1), (1 : ℝ) / (k + 1) := by
      refine prod_congr rfl fun k hk => ?_
      simp [lt_of_lt_of_le (mem_range.mp hk) (Nat.succ_le_of_lt hn)]
    rw [hprod]
    have hfact : ∏ k ∈ range (n + 1), (1 : ℝ) / (k + 1) = 1 / ((n + 1)! : ℝ) := by
      have hinv : ∏ k ∈ range (n + 1), ((k + 1 : ℝ))⁻¹ = ((n + 1)! : ℝ)⁻¹ := by
        rw [prod_inv_distrib]
        congr 1
        have hcast : ∏ k ∈ range (n + 1), (k + 1 : ℝ) =
            ↑(∏ k ∈ range (n + 1), (k + 1)) := by
          rw [prod_natCast]
          refine prod_congr rfl fun k _ => ?_
          norm_cast
        rw [hcast, prod_range_add_one_eq_factorial]
      simp_rw [one_div]
      rw [hinv, inv_eq_one_div]
    rw [hfact, Real.div_rpow zero_le_one (by positivity), Real.one_rpow]
  · simp only [hn, ite_false]
    unfold prefixGeometricMean
    have hmem : N ∈ range (n + 1) := mem_range.mpr (Nat.lt_succ_of_le (not_lt.mp hn))
    rw [prod_eq_zero hmem (by simp), Real.zero_rpow (by positivity)]

/-- The constant `e` in Carleman's inequality is optimal already on finitely supported sequences. -/
theorem carleman_constant_le {C : ℝ}
    (hC : ∀ a : ℕ → ℝ, (∀ n, 0 ≤ a n) → (Function.support a).Finite →
      (∑' n, prefixGeometricMean a n) ≤ C * ∑' n, a n) : Real.exp 1 ≤ C := by
  refine le_of_tendsto tendsto_carleman_series_ratio ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  let a : ℕ → ℝ := fun k => if k < N then (1 : ℝ) / (k + 1) else 0
  have ha : ∀ n, 0 ≤ a n := by
    intro n
    by_cases hn : n < N
    · simp only [a, hn]
      positivity
    · simp [a, hn]
  have hfin : (Function.support a).Finite := by
    refine (range N).finite_toSet.subset ?_
    intro k hk
    by_contra hkN
    have hkN' : N ≤ k := by simpa [mem_coe, mem_range] using hkN
    simp [a, not_lt.mpr hkN', Function.mem_support] at hk
  have hsum_a : ∑' n, a n = ∑ n ∈ range N, 1 / (n + 1 : ℝ) := by
    rw [tsum_eq_sum (s := range N) (fun k hk => ?_)]
    · exact sum_congr rfl fun k hk => by simp [a, mem_range.mp hk]
    · simp only [mem_range, not_lt] at hk
      simp [a, hk]
  have hsum_g : ∑' n, prefixGeometricMean a n =
      ∑ n ∈ range N, 1 / ((n + 1)! : ℝ) ^ (1 / (n + 1 : ℝ)) := by
    rw [tsum_eq_sum (s := range N) (fun n hn => ?_)]
    · refine sum_congr rfl fun n hn => ?_
      rw [prefixGeometricMean_trunc]
      simp [mem_range.mp hn]
    · rw [prefixGeometricMean_trunc]
      simp [show ¬ n < N by simpa [mem_range] using hn]
  have hden : 0 < ∑ n ∈ range N, 1 / (n + 1 : ℝ) := by
    refine sum_pos (fun n _ => ?_) (nonempty_range_iff.mpr (by omega))
    positivity
  have hle := hC a ha hfin
  rw [hsum_g, hsum_a] at hle
  exact (div_le_iff₀ hden).mpr hle

end CKMA
