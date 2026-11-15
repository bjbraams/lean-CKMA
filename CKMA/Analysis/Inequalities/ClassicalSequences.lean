/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.Inequalities.ClassicalSequences.NewtonMaclaurin
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Order.Interval.Finset.Nat

/-!
# Newton–Maclaurin and discrete Hardy inequalities

Normalized elementary symmetric means of finite tuples, Newton log-concavity and
Maclaurin's chain for nonnegative entries. Cesàro averages use the first `n+1` terms;
Hardy's inequality and its optimal constant are expressed by extended nonnegative sums.
Elementary symmetric polynomials, real powers and infinite sums reuse Mathlib.
Newton's inequality is read off the derivative by Mathlib's Rolle bound
`Polynomial.card_roots_le_derivative`.
Sources: GAPS 11.9 and 11.32.

## Main definitions

* `CKMA.hardyAverage`: Cesàro average of the first `n + 1` entries of a real sequence.

## Main results

* `CKMA.newton_normalizedElementaryMean`: **11.9** Newton log-concavity of normalized
  elementary symmetric means.
* `CKMA.maclaurin_normalizedElementaryMean`: Maclaurin's monotone chain of positive-root
  normalized means.
* `CKMA.discrete_hardy`: **11.32** Hardy's discrete inequality with constant `(p / (p - 1)) ^ p`.
* `CKMA.discrete_hardy_constant_le`: optimality of the constant `(p / (p - 1)) ^ p` in Hardy's
  discrete inequality.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Finset Real Filter

open scoped BigOperators ENNReal Topology

/-- **11.9**: Newton log-concavity of normalized elementary symmetric means. -/
theorem newton_normalizedElementaryMean {n k : ℕ} (x : Fin n → ℝ)
    (hx : ∀ j, 0 ≤ x j) (hk : 1 ≤ k) (hkn : k < n) :
    normalizedElementaryMean x (k - 1) * normalizedElementaryMean x (k + 1) ≤
      normalizedElementaryMean x k ^ 2 := by
  set s : Multiset ℝ := Finset.univ.val.map x
  have hs : ∀ a ∈ s, 0 ≤ a := by
    intro a ha
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.mp ha
    exact hx i
  have hcard : s.card = n := by
    rw [Multiset.card_map, Finset.card_val, Finset.card_univ, Fintype.card_fin]
  simpa [normalizedElementaryMean, elemMean, s, hcard] using
    newton_elemMean s hs hcard k hk hkn

/-- Maclaurin's monotone chain of positive-root normalized means, allowing zero entries. -/
theorem maclaurin_normalizedElementaryMean {n j k : ℕ} (x : Fin n → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hj : 1 ≤ j) (hjk : j ≤ k) (hkn : k ≤ n) :
    normalizedElementaryMean x k ^ (1 / (k : ℝ)) ≤
      normalizedElementaryMean x j ^ (1 / (j : ℝ)) := by
  set s : Multiset ℝ := Finset.univ.val.map x
  have hs : ∀ a ∈ s, 0 ≤ a := by
    intro a ha
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.mp ha
    exact hx i
  have hcard : s.card = n := by
    rw [Multiset.card_map, Finset.card_val, Finset.card_univ, Fintype.card_fin]
  simpa [normalizedElementaryMean, elemMean, s, hcard] using
    maclaurin_elemMean hs hcard hj hjk hkn

/-- Cesaro average of the first `n+1` entries, indexed from zero. -/
def hardyAverage (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  (∑ j ∈ Finset.range (n + 1), a j) / (n + 1 : ℝ)

/-- Telescoping sum of successive differences on an initial segment. -/
private theorem sum_sub_succ_eq_sub {u : ℕ → ℝ} {N : ℕ} :
    ∑ n ∈ range N, (u n - u (n + 1)) = u 0 - u N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, ih]
    ring

/-- If `A ≤ K * B^{1/p} * A^{(p-1)/p}` with nonnegative data and `1 < p`, then `A ≤ K^p * B`. -/
private theorem hardy_absorb_rpow {p A B K : ℝ} (hp : 1 < p) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hK : 0 ≤ K) (h : A ≤ K * B ^ (1 / p) * A ^ ((p - 1) / p)) : A ≤ K ^ p * B := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  rcases hA.eq_or_lt with hA0 | hApos
  · rw [← hA0]
    exact mul_nonneg (rpow_nonneg hK _) hB
  · have hexp : (1 / p) + (p - 1) / p = 1 := by
      field_simp
      ring
    have hsplit : A ^ (1 / p) * A ^ ((p - 1) / p) = A := by
      rw [← rpow_add hApos, hexp, rpow_one]
    have hfactor : 0 < A ^ ((p - 1) / p) := rpow_pos_of_pos hApos _
    have hle : A ^ (1 / p) ≤ K * B ^ (1 / p) := by
      have h' : A ^ (1 / p) * A ^ ((p - 1) / p) ≤
          K * B ^ (1 / p) * A ^ ((p - 1) / p) := by
        rwa [hsplit]
      exact le_of_mul_le_mul_right h' hfactor
    have hpow := rpow_le_rpow (rpow_nonneg hA _) hle hp0.le
    rw [← rpow_mul hA, one_div, inv_mul_cancel₀ hp0.ne', rpow_one] at hpow
    rw [mul_rpow hK (rpow_nonneg hB _), ← rpow_mul hB, inv_mul_cancel₀ hp0.ne',
      rpow_one] at hpow
    exact hpow

/-- One Elliott step: Young’s inequality rearranges a weighted power increment. -/
private theorem hardy_young_step {p : ℝ} (hp : 1 < p) (n : ℕ) {avg prev : ℝ} (havg : 0 ≤ avg)
    (hprev : 0 ≤ prev) :
    avg ^ p - (p / (p - 1)) * ((n + 1 : ℝ) * avg - (n : ℝ) * prev) * avg ^ (p - 1) ≤
      (n : ℝ) / (p - 1) * prev ^ p - (n + 1 : ℝ) / (p - 1) * avg ^ p := by
  set q : ℝ := p / (p - 1) with hq
  set z : ℝ := avg ^ (p - 1) with hz
  have hpq : p.HolderConjugate q := by
    rw [hq]
    exact HolderConjugate.conjExponent hp
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hpm1 : 0 < p - 1 := sub_pos.mpr hp
  have hq0 : 0 < q := by
    rw [hq]
    exact div_pos hp0 hpm1
  have hmul : avg * z = avg ^ p := by
    rw [hz]
    nth_rw 1 [← rpow_one avg]
    rw [← rpow_add' havg (ne_of_gt (by linarith : (0 : ℝ) < 1 + (p - 1)))]
    congr 1
    ring
  have hconj_exp : (p - 1) * q = p := by
    rw [hq, div_eq_mul_inv, mul_left_comm, mul_inv_cancel₀ hpm1.ne', mul_one]
  have hconj : z ^ q = avg ^ p := by
    rw [hz, ← rpow_mul havg, hconj_exp]
  have hyoung : prev * z ≤ prev ^ p / p + avg ^ p / q := by
    rw [hz]
    have hraw := young_inequality_of_nonneg hprev (rpow_nonneg havg (p - 1)) hpq
    rwa [← rpow_mul havg, hconj_exp] at hraw
  have hcross : q * (n : ℝ) * (prev * z) ≤
      q * (n : ℝ) * (prev ^ p / p + avg ^ p / q) :=
    mul_le_mul_of_nonneg_left hyoung (mul_nonneg hq0.le (Nat.cast_nonneg n))
  have h1 : q * (n : ℝ) * (prev ^ p / p) = (q / p) * (n : ℝ) * prev ^ p := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    ac_rfl
  have h2 : q * (n : ℝ) * (avg ^ p / q) = (n : ℝ) * avg ^ p := by
    rw [div_eq_mul_inv]
    calc
      q * ↑n * (avg ^ p * q⁻¹) = q * q⁻¹ * ↑n * avg ^ p := by ac_rfl
      _ = ↑n * avg ^ p := by rw [mul_inv_cancel₀ hq0.ne', one_mul]
  have hcross' : q * (n : ℝ) * (prev ^ p / p + avg ^ p / q) =
      (q / p) * (n : ℝ) * prev ^ p + (n : ℝ) * avg ^ p := by
    rw [mul_add, h1, h2]
  have hqp : q / p = 1 / (p - 1) := by
    rw [hq, div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, one_mul]
    calc
      (p * (p - 1)⁻¹) * p⁻¹ = p * p⁻¹ * (p - 1)⁻¹ := by ac_rfl
      _ = (p - 1)⁻¹ := by rw [mul_inv_cancel₀ hp0.ne', one_mul]
  have hcoeff : (1 : ℝ) - q * ((n : ℝ) + 1) + (n : ℝ) = -(((n : ℝ) + 1) / (p - 1)) := by
    rw [hq]
    apply mul_right_cancel₀ hpm1.ne'
    field_simp
    ring
  have hmuln : (1 / (p - 1)) * (n : ℝ) = (n : ℝ) / (p - 1) := by
    rw [div_eq_mul_inv, one_mul, div_eq_mul_inv, mul_comm]
  have hlin : avg ^ p - q * ((n : ℝ) + 1) * avg ^ p =
      (1 - q * ((n : ℝ) + 1)) * avg ^ p := by
    set x : ℝ := avg ^ p
    ring
  calc
    avg ^ p - q * ((↑n + 1) * avg - ↑n * prev) * z
        = avg ^ p - (q * ((↑n + 1) * avg) - q * (↑n * prev)) * z := by
          rw [mul_sub]
    _ = avg ^ p - (q * ((↑n + 1) * avg) * z - q * (↑n * prev) * z) := by
          rw [sub_mul]
    _ = avg ^ p - q * ((↑n + 1) * avg) * z + q * (↑n * prev) * z := by
          abel
    _ = avg ^ p - q * (↑n + 1) * (avg * z) + q * ↑n * (prev * z) := by
          ring
    _ = avg ^ p - q * (↑n + 1) * avg ^ p + q * ↑n * (prev * z) := by
          rw [hmul]
    _ ≤ avg ^ p - q * (↑n + 1) * avg ^ p +
          q * ↑n * (prev ^ p / p + avg ^ p / q) := by
          exact add_le_add le_rfl hcross
    _ = avg ^ p - q * (↑n + 1) * avg ^ p +
          ((q / p) * ↑n * prev ^ p + ↑n * avg ^ p) := by
          rw [hcross']
    _ = (1 - q * (↑n + 1)) * avg ^ p + (q / p) * ↑n * prev ^ p + ↑n * avg ^ p := by
          rw [hlin, add_assoc]
    _ = (1 - q * (↑n + 1) + ↑n) * avg ^ p + (q / p) * ↑n * prev ^ p := by
          rw [add_right_comm, ← add_mul]
    _ = -(((n : ℝ) + 1) / (p - 1)) * avg ^ p + (1 / (p - 1)) * ↑n * prev ^ p := by
          rw [hcoeff, hqp]
    _ = ↑n / (p - 1) * prev ^ p - (↑n + 1) / (p - 1) * avg ^ p := by
          rw [hmuln, neg_mul, add_comm, ← sub_eq_add_neg]

/-- Partial sums of Cesaro means obey Hardy's inequality with the sharp constant. -/
private theorem sum_hardyAverage_pow_le {p : ℝ} (hp : 1 < p) {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    (N : ℕ) : ∑ n ∈ range N, hardyAverage a n ^ p ≤
      (p / (p - 1)) ^ p * ∑ n ∈ range N, a n ^ p := by
  set q : ℝ := p / (p - 1) with hq
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hpm1 : 0 < p - 1 := sub_pos.mpr hp
  have hq0 : 0 < q := by
    rw [hq]
    exact div_pos hp0 hpm1
  have hpq : p.HolderConjugate q := by
    rw [hq]
    exact HolderConjugate.conjExponent hp
  let S : ℕ → ℝ := fun k => ∑ j ∈ range k, a j
  let prev : ℕ → ℝ := fun n => if n = 0 then 0 else S n / n
  let avg : ℕ → ℝ := fun n => hardyAverage a n
  have hSnonneg : ∀ n, 0 ≤ S n := fun n => by
    simpa [S] using Finset.sum_nonneg fun j _ => ha j
  have havg : ∀ n, 0 ≤ avg n := fun n => by
    unfold avg hardyAverage
    exact div_nonneg (sum_nonneg fun j _ => ha j) (by positivity)
  have hprev : ∀ n, 0 ≤ prev n := fun n => by
    by_cases hn : n = 0
    · simp [prev, hn]
    · have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      simpa [prev, hn] using div_nonneg (hSnonneg n) hn0.le
  have hident : ∀ n, a n = (n + 1 : ℝ) * avg n - (n : ℝ) * prev n := by
    intro n
    by_cases hn : n = 0
    · subst hn
      simp [avg, prev, hardyAverage, S]
    · have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn
      have hn1 : (n + 1 : ℝ) ≠ 0 := by positivity
      simp only [avg, hardyAverage, prev, hn, ite_false, S]
      rw [mul_div_cancel₀ _ hn1, mul_div_cancel₀ _ hn0, sum_range_succ]
      ring
  let u : ℕ → ℝ := fun n => (n : ℝ) / (p - 1) * prev n ^ p
  have hstep : ∀ n ∈ range N, avg n ^ p ≤
      q * a n * avg n ^ (p - 1) + (u n - u (n + 1)) := by
    intro n _
    have hys := hardy_young_step hp n (havg n) (hprev n)
    have hprev_succ : prev (n + 1) = avg n := by
      simp only [prev, Nat.succ_ne_zero n, ite_false, avg, hardyAverage, S]
      rw [Nat.cast_add, Nat.cast_one]
    have hu_n : u n = (n : ℝ) / (p - 1) * prev n ^ p := rfl
    have hu_succ : u (n + 1) = (n + 1 : ℝ) / (p - 1) * avg n ^ p := by
      simp only [u, hprev_succ]
      rw [Nat.cast_add, Nat.cast_one]
    rw [← hident n, ← hu_n, ← hu_succ] at hys
    have : avg n ^ p ≤ u n - u (n + 1) + q * a n * avg n ^ (p - 1) :=
      (sub_le_iff_le_add).mp hys
    linarith
  have hsum : ∑ n ∈ range N, avg n ^ p ≤ q * ∑ n ∈ range N, a n * avg n ^ (p - 1) := by
    calc
      ∑ n ∈ range N, avg n ^ p
          ≤ ∑ n ∈ range N, (q * a n * avg n ^ (p - 1) + (u n - u (n + 1))) :=
            sum_le_sum hstep
      _ = q * ∑ n ∈ range N, a n * avg n ^ (p - 1) +
            ∑ n ∈ range N, (u n - u (n + 1)) := by
            rw [sum_add_distrib]
            congr 1
            simp_rw [mul_assoc]
            rw [← mul_sum]
      _ = q * ∑ n ∈ range N, a n * avg n ^ (p - 1) + (u 0 - u N) := by
            rw [sum_sub_succ_eq_sub]
      _ ≤ q * ∑ n ∈ range N, a n * avg n ^ (p - 1) := by
            have hu0 : u 0 = 0 := by simp [u, prev]
            have huN : 0 ≤ u N :=
              mul_nonneg (div_nonneg (Nat.cast_nonneg _) hpm1.le) (rpow_nonneg (hprev N) _)
            linarith
  have hconj_exp : (p - 1) * q = p := by
    rw [hq, div_eq_mul_inv, mul_left_comm, mul_inv_cancel₀ hpm1.ne', mul_one]
  have hgg : ∀ n, (avg n ^ (p - 1)) ^ q = avg n ^ p := by
    intro n
    rw [← rpow_mul (havg n), hconj_exp]
  have hholder : ∑ n ∈ range N, a n * avg n ^ (p - 1) ≤
      (∑ n ∈ range N, a n ^ p) ^ (1 / p) * (∑ n ∈ range N, avg n ^ p) ^ (1 / q) := by
    have hraw := inner_le_Lp_mul_Lq_of_nonneg (s := range N) (f := a)
      (g := fun n => avg n ^ (p - 1)) hpq (fun n _ => ha n)
      (fun n _ => rpow_nonneg (havg n) _)
    simpa [hgg] using hraw
  have h1q : (1 : ℝ) / q = (p - 1) / p := by
    rw [hq, one_div_div]
  have hA : ∑ n ∈ range N, avg n ^ p ≤
      q * (∑ n ∈ range N, a n ^ p) ^ (1 / p) *
        (∑ n ∈ range N, avg n ^ p) ^ ((p - 1) / p) := by
    calc
      ∑ n ∈ range N, avg n ^ p ≤ q * ∑ n ∈ range N, a n * avg n ^ (p - 1) := hsum
      _ ≤ q * ((∑ n ∈ range N, a n ^ p) ^ (1 / p) *
          (∑ n ∈ range N, avg n ^ p) ^ (1 / q)) :=
            mul_le_mul_of_nonneg_left hholder hq0.le
      _ = q * (∑ n ∈ range N, a n ^ p) ^ (1 / p) *
          (∑ n ∈ range N, avg n ^ p) ^ ((p - 1) / p) := by
            rw [h1q, mul_assoc]
  have habsorb := hardy_absorb_rpow hp
    (Finset.sum_nonneg fun n _ => rpow_nonneg (havg n) _)
    (Finset.sum_nonneg fun n _ => rpow_nonneg (ha n) _) hq0.le hA
  simpa [avg, hq] using habsorb

/-- **11.32**: Hardy's discrete inequality, stated as an extended nonnegative sum. -/
theorem discrete_hardy {p : ℝ} (hp : 1 < p) (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) :
    (∑' n, ENNReal.ofReal (hardyAverage a n ^ p)) ≤
      ENNReal.ofReal ((p / (p - 1)) ^ p) * ∑' n, ENNReal.ofReal (a n ^ p) := by
  set c : ℝ := (p / (p - 1)) ^ p
  have hc : 0 ≤ c := by
    exact rpow_nonneg (div_nonneg (le_of_lt (lt_trans zero_lt_one hp))
      (sub_nonneg.mpr (le_of_lt hp))) _
  have havg : ∀ n, 0 ≤ hardyAverage a n ^ p := fun n => by
    unfold hardyAverage
    exact rpow_nonneg (div_nonneg (sum_nonneg fun j _ => ha j) (by positivity)) _
  have hap : ∀ n, 0 ≤ a n ^ p := fun n => rpow_nonneg (ha n) _
  rw [ENNReal.tsum_eq_iSup_nat]
  refine iSup_le fun N => ?_
  rw [← ENNReal.ofReal_sum_of_nonneg fun n _ => havg n]
  have hpartial := sum_hardyAverage_pow_le hp ha N
  have hmul : ENNReal.ofReal (c * ∑ n ∈ range N, a n ^ p) =
      ENNReal.ofReal c * ENNReal.ofReal (∑ n ∈ range N, a n ^ p) :=
    ENNReal.ofReal_mul hc
  calc
    ENNReal.ofReal (∑ n ∈ range N, hardyAverage a n ^ p)
        ≤ ENNReal.ofReal (c * ∑ n ∈ range N, a n ^ p) :=
          ENNReal.ofReal_le_ofReal hpartial
    _ = ENNReal.ofReal c * ENNReal.ofReal (∑ n ∈ range N, a n ^ p) := hmul
    _ = ENNReal.ofReal c * ∑ n ∈ range N, ENNReal.ofReal (a n ^ p) := by
          rw [ENNReal.ofReal_sum_of_nonneg fun n _ => hap n]
    _ ≤ ENNReal.ofReal c * ∑' n, ENNReal.ofReal (a n ^ p) :=
          mul_le_mul' le_rfl (ENNReal.sum_le_tsum _)

/-- Power weight `(n+1)^{-1/p}` truncated to `n < N`, used to test the Hardy constant. -/
private def hardyTrunc (p : ℝ) (N n : ℕ) : ℝ :=
  if n < N then (n + 1 : ℝ) ^ (-(1 / p)) else 0

/-- The truncated power weight is nonnegative. -/
private theorem hardyTrunc_nonneg (p : ℝ) (N n : ℕ) : 0 ≤ hardyTrunc p N n := by
  unfold hardyTrunc
  split_ifs
  · exact rpow_nonneg (by positivity) _
  · exact le_rfl

/-- The truncated power weight is supported on `n < N`. -/
private theorem hardyTrunc_support_finite (p : ℝ) (N : ℕ) :
    (Function.support (hardyTrunc p N)).Finite := by
  refine (range N).finite_toSet.subset ?_
  intro n hn
  by_contra hmem
  have hlt : ¬ n < N := by simpa [mem_range] using hmem
  apply hn
  simp [hardyTrunc, hlt]

/-- Integral lower bound for one normalized partial sum of `k^{-1/p}`. -/
private theorem hardy_weight_term_lower {p : ℝ} (hp : 1 < p) {m : ℕ} (hm : 1 ≤ m) :
    (p / (p - 1)) ^ p * (m : ℝ)⁻¹ *
        ((1 + (m : ℝ)⁻¹) ^ ((p - 1) / p) - (m : ℝ) ^ (-((p - 1) / p))) ^ p ≤
      ((∑ k ∈ Icc 1 m, (k : ℝ) ^ (-(1 / p))) / (m : ℝ)) ^ p := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hpm1 : 0 < p - 1 := sub_pos.mpr hp
  set β : ℝ := (p - 1) / p with hβ
  have hβ0 : 0 < β := by
    rw [hβ]
    exact div_pos hpm1 hp0
  have hr : -1 < -(1 / p) := neg_lt_neg ((div_lt_one hp0).mpr hp)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-(1 / p)))
      (Set.Icc (↑(1 : ℕ)) (↑(m + 1))) := by
    refine (antitoneOn_rpow_Ioi_of_exponent_nonpos
      (neg_nonpos.mpr (le_of_lt (by positivity : 0 < 1 / p)))).mono ?_
    intro x hx
    have hx1 : (1 : ℝ) ≤ x := by simpa using hx.1
    exact lt_of_lt_of_le zero_lt_one hx1
  have hint_le :=
    AntitoneOn.integral_le_sum_Ico (a := 1) (b := m + 1) (by omega) hanti
  have hIco : ∑ k ∈ Ico 1 (m + 1), (k : ℝ) ^ (-(1 / p)) =
      ∑ k ∈ Icc 1 m, (k : ℝ) ^ (-(1 / p)) := by
    rw [Ico_add_one_right_eq_Icc]
  have hpow : -(1 / p) + 1 = β := by
    rw [hβ]
    field_simp
    ring
  have hinvβ : β⁻¹ = p / (p - 1) := by
    rw [hβ]
    field_simp
  have hint : ∫ x in (1 : ℕ)..(m + 1), x ^ (-(1 / p)) =
      (((m : ℝ) + 1) ^ β - 1) * (p / (p - 1)) := by
    rw [integral_rpow (Or.inl hr), hpow, Nat.cast_one, one_rpow, div_eq_mul_inv, hinvβ]
  set S : ℝ := ∑ k ∈ Icc 1 m, (k : ℝ) ^ (-(1 / p))
  set A : ℝ := ((m : ℝ) + 1) ^ β - 1
  have hA0 : 0 ≤ A := by
    have : (1 : ℝ) ≤ ((m : ℝ) + 1) ^ β :=
      one_le_rpow (by linarith : (1 : ℝ) ≤ (m : ℝ) + 1) hβ0.le
    linarith
  have hS : A * (p / (p - 1)) ≤ S := by
    have hcast : ((m : ℝ) + 1) = ↑(m + 1) := by
      rw [Nat.cast_add, Nat.cast_one]
    rw [← hint, hcast, ← hIco]
    exact hint_le
  have hbase : 0 ≤ A * (p / (p - 1)) / m :=
    div_nonneg (mul_nonneg hA0 (div_nonneg hp0.le hpm1.le)) hm0.le
  have hpowle : (A * (p / (p - 1)) / m) ^ p ≤ (S / m) ^ p :=
    rpow_le_rpow hbase (div_le_div_of_nonneg_right hS hm0.le) hp0.le
  have hc0 : 0 ≤ p / (p - 1) := div_nonneg hp0.le hpm1.le
  have hfactor : (A * (p / (p - 1)) / m) ^ p =
      (p / (p - 1)) ^ p * (A ^ p / (m : ℝ) ^ p) := by
    calc
      (A * (p / (p - 1)) / m) ^ p
          = (A * (p / (p - 1)) * (m : ℝ)⁻¹) ^ p := by rw [div_eq_mul_inv]
      _ = (A * (p / (p - 1))) ^ p * ((m : ℝ)⁻¹) ^ p := by
            rw [mul_rpow (mul_nonneg hA0 hc0) (inv_nonneg.mpr hm0.le)]
      _ = A ^ p * (p / (p - 1)) ^ p * ((m : ℝ) ^ p)⁻¹ := by
            rw [mul_rpow hA0 hc0, inv_rpow hm0.le]
      _ = (p / (p - 1)) ^ p * (A ^ p * ((m : ℝ) ^ p)⁻¹) := by
            rw [mul_assoc, mul_left_comm]
      _ = (p / (p - 1)) ^ p * (A ^ p / (m : ℝ) ^ p) := by
            rw [← div_eq_mul_inv]
  have hβp : β * p = p - 1 := by
    rw [hβ]
    field_simp
  have hratio : (m : ℝ)⁻¹ * (A / (m : ℝ) ^ β) ^ p = A ^ p / (m : ℝ) ^ p := by
    have hmβnonneg : 0 ≤ (m : ℝ) ^ β := rpow_nonneg hm0.le _
    calc
      (m : ℝ)⁻¹ * (A / (m : ℝ) ^ β) ^ p
          = (m : ℝ)⁻¹ * (A ^ p / ((m : ℝ) ^ β) ^ p) := by
            rw [div_rpow hA0 hmβnonneg]
      _ = (m : ℝ)⁻¹ * (A ^ p / (m : ℝ) ^ (β * p)) := by
            rw [← rpow_mul hm0.le]
      _ = (m : ℝ)⁻¹ * (A ^ p / (m : ℝ) ^ (p - 1)) := by
            rw [hβp]
      _ = (m : ℝ)⁻¹ * (A ^ p * ((m : ℝ) ^ (p - 1))⁻¹) := by
            rw [div_eq_mul_inv]
      _ = A ^ p * ((m : ℝ)⁻¹ * ((m : ℝ) ^ (p - 1))⁻¹) := by
            rw [← mul_assoc, mul_comm ((m : ℝ)⁻¹), mul_assoc]
      _ = A ^ p * ((m : ℝ) * (m : ℝ) ^ (p - 1))⁻¹ := by
            rw [← mul_inv]
      _ = A ^ p * ((m : ℝ) ^ p)⁻¹ := by
            congr 1
            nth_rw 1 [← rpow_one (m : ℝ)]
            rw [← rpow_add hm0]
            congr 1
            ring
      _ = A ^ p / (m : ℝ) ^ p := by
            rw [← div_eq_mul_inv]
  have hquot : ((m : ℝ) + 1) / m = 1 + (m : ℝ)⁻¹ := by
    field_simp
  have hshift : A / (m : ℝ) ^ β = (1 + (m : ℝ)⁻¹) ^ β - (m : ℝ) ^ (-β) := by
    calc
      A / (m : ℝ) ^ β = (((m : ℝ) + 1) ^ β - 1) / (m : ℝ) ^ β := rfl
      _ = ((m : ℝ) + 1) ^ β / (m : ℝ) ^ β - 1 / (m : ℝ) ^ β := by rw [sub_div]
      _ = (((m : ℝ) + 1) / m) ^ β - (m : ℝ) ^ (-β) := by
            rw [← div_rpow (by linarith : (0 : ℝ) ≤ (m : ℝ) + 1) hm0.le, one_div,
              ← rpow_neg hm0.le]
      _ = (1 + (m : ℝ)⁻¹) ^ β - (m : ℝ) ^ (-β) := by
            rw [hquot]
  have hgoal : (A * (p / (p - 1)) / m) ^ p =
      (p / (p - 1)) ^ p * (m : ℝ)⁻¹ *
        ((1 + (m : ℝ)⁻¹) ^ β - (m : ℝ) ^ (-β)) ^ p := by
    rw [hfactor, ← hratio, mul_assoc, hshift]
  calc
    (p / (p - 1)) ^ p * (m : ℝ)⁻¹ *
        ((1 + (m : ℝ)⁻¹) ^ β - (m : ℝ) ^ (-β)) ^ p
        = (A * (p / (p - 1)) / m) ^ p := by rw [← hgoal]
    _ ≤ (S / m) ^ p := hpowle

/-- The constant in Hardy's inequality is optimal already on finitely supported inputs. -/
theorem discrete_hardy_constant_le {p C : ℝ} (hp : 1 < p)
    (hbound : ∀ a : ℕ → ℝ, (∀ n, 0 ≤ a n) → (Function.support a).Finite →
      (∑' n, ENNReal.ofReal (hardyAverage a n ^ p)) ≤
        ENNReal.ofReal C * ∑' n, ENNReal.ofReal (a n ^ p)) :
    (p / (p - 1)) ^ p ≤ C := by
  set c : ℝ := (p / (p - 1)) ^ p
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hpm1 : 0 < p - 1 := sub_pos.mpr hp
  have hc0 : 0 < c := rpow_pos_of_pos (div_pos hp0 hpm1) _
  have hC : 0 ≤ C := by
    by_contra hneg
    have hlt : C < 0 := lt_of_not_ge hneg
    let a : ℕ → ℝ := hardyTrunc p 1
    have ha : ∀ n, 0 ≤ a n := fun n => hardyTrunc_nonneg p 1 n
    have hfin := hardyTrunc_support_finite p 1
    have hbd := hbound a ha hfin
    have ha0 : a 0 = 1 := by
      simp [a, hardyTrunc, one_rpow]
    have hone : hardyAverage a 0 ^ p = 1 := by
      simp [hardyAverage, ha0, one_rpow]
    have hge : (1 : ℝ≥0∞) ≤ ∑' n, ENNReal.ofReal (hardyAverage a n ^ p) := by
      calc
        (1 : ℝ≥0∞) = ENNReal.ofReal (hardyAverage a 0 ^ p) := by simp [hone]
        _ = ∑ n ∈ range 1, ENNReal.ofReal (hardyAverage a n ^ p) := by simp
        _ ≤ ∑' n, ENNReal.ofReal (hardyAverage a n ^ p) := ENNReal.sum_le_tsum _
    have hzero : ENNReal.ofReal C = 0 := ENNReal.ofReal_of_nonpos hlt.le
    rw [hzero, zero_mul] at hbd
    exact not_lt_of_ge (hge.trans hbd) zero_lt_one
  let H : ℕ → ℝ := fun N => ∑ k ∈ Icc 1 N, (k : ℝ)⁻¹
  have hHlog : ∀ N : ℕ, Real.log ((N : ℝ) + 1) ≤ H N := by
    intro N
    have hanti : AntitoneOn (fun x : ℝ => x⁻¹) (Set.Icc (↑(1 : ℕ)) (↑(N + 1))) :=
      inv_antitoneOn_Ioi.mono fun x hx =>
        lt_of_lt_of_le zero_lt_one (by simpa using hx.1)
    have hint := AntitoneOn.integral_le_sum_Ico (a := 1) (b := N + 1) (by omega) hanti
    have heq : ∑ k ∈ Ico 1 (N + 1), (k : ℝ)⁻¹ = H N := by
      rw [Ico_add_one_right_eq_Icc]
    have hintv : ∫ x in (1 : ℕ)..(N + 1), x⁻¹ = Real.log ((N : ℝ) + 1) := by
      rw [integral_inv_of_pos (by positivity : (0 : ℝ) < (1 : ℕ)) (by positivity)]
      simp [div_one, Nat.cast_one]
    simpa [heq, hintv] using hint
  have hHtop : Tendsto H atTop atTop :=
    tendsto_atTop_mono hHlog <| tendsto_log_atTop.comp <|
      tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
  set β : ℝ := (p - 1) / p
  have hβ0 : 0 < β := div_pos hpm1 hp0
  let φ : ℕ → ℝ := fun m =>
    ((1 + (m : ℝ)⁻¹) ^ β - (m : ℝ) ^ (-β)) ^ p
  have hφ_nonneg : ∀ m, 1 ≤ m → 0 ≤ φ m := by
    intro m hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
    have hm1r : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hinside : 0 ≤ (1 + (m : ℝ)⁻¹) ^ β - (m : ℝ) ^ (-β) := by
      have hone : (1 : ℝ) ≤ (1 + (m : ℝ)⁻¹) ^ β :=
        one_le_rpow (le_add_of_nonneg_right (inv_nonneg.mpr (Nat.cast_nonneg m))) hβ0.le
      have hsmall : (m : ℝ) ^ (-β) ≤ 1 := by
        rw [rpow_neg hm0.le]
        exact inv_le_one_of_one_le₀ (one_le_rpow hm1r hβ0.le)
      linarith
    exact rpow_nonneg hinside _
  have hφ : Tendsto φ atTop (nhds 1) := by
    have hinv : Tendsto (fun m : ℕ => (m : ℝ)⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    have hbase : Tendsto (fun m : ℕ => 1 + (m : ℝ)⁻¹) atTop (nhds 1) := by
      simpa using tendsto_const_nhds.add hinv
    have hleft : Tendsto (fun m : ℕ => (1 + (m : ℝ)⁻¹) ^ β) atTop (nhds 1) := by
      have hcont := (continuousAt_rpow_const (1 : ℝ) β (Or.inl one_ne_zero)).tendsto
      have hcomp := hcont.comp hbase
      simp only [one_rpow] at hcomp
      exact Tendsto.congr (fun _ => rfl) hcomp
    have hright : Tendsto (fun m : ℕ => (m : ℝ) ^ (-β)) atTop (nhds 0) :=
      (tendsto_rpow_neg_atTop hβ0).comp tendsto_natCast_atTop_atTop
    have hsub : Tendsto (fun m : ℕ => (1 + (m : ℝ)⁻¹) ^ β - (m : ℝ) ^ (-β)) atTop (nhds 1) := by
      simpa using hleft.sub hright
    have hcontp := (continuous_rpow_const (q := p) hp0.le).continuousAt (x := 1)
    have hcomp := hcontp.tendsto.comp hsub
    simp only [one_rpow] at hcomp
    exact Tendsto.congr (fun _ => rfl) hcomp
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set δ : ℝ := min (1 / 2) (ε / c)
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ < 1 := by
    have hδle : δ ≤ 1 / 2 := min_le_left _ _
    have : (1 : ℝ) / 2 < 1 := by norm_num
    linarith
  have hδε : c * δ ≤ ε := by
    have hδle : δ ≤ ε / c := min_le_right _ _
    calc
      c * δ ≤ c * (ε / c) := mul_le_mul_of_nonneg_left hδle hc0.le
      _ = ε := by field_simp
  set η : ℝ := δ / 2
  have hη0 : 0 < η := by positivity
  have hη1 : η < 1 := by
    rw [show η = δ / 2 from rfl, div_lt_one (by norm_num : (0 : ℝ) < 2)]
    linarith [hδ1]
  have hsq : 1 - δ ≤ (1 - η) ^ 2 := by
    have hηdef : η = δ / 2 := rfl
    nlinarith
  have hcloseφ : ∀ᶠ m : ℕ in atTop, φ m ∈ Set.Ioo (1 - η) (1 + η) :=
    hφ.eventually (Ioo_mem_nhds (sub_lt_self 1 hη0) (lt_add_of_pos_right 1 hη0))
  obtain ⟨M0, hM0⟩ := eventually_atTop.mp hcloseφ
  let M : ℕ := max M0 1
  have hM1 : 1 ≤ M := le_max_right _ _
  have hMφ : ∀ m ≥ M, 1 - η < φ m := by
    intro m hm
    have hmem := hM0 m (le_trans (le_max_left _ _) hm)
    rw [Set.mem_Ioo] at hmem
    exact hmem.1
  have hlarge : ∀ᶠ N : ℕ in atTop, H (M - 1) / η ≤ H N ∧ M ≤ N :=
    (hHtop.eventually_ge_atTop (H (M - 1) / η)).and (eventually_ge_atTop M)
  obtain ⟨N, hNge, hNM⟩ := hlarge.exists
  have hN1 : 1 ≤ N := le_trans hM1 hNM
  have hHpos : 0 < H N := by
    have hmem : (1 : ℕ) ∈ Icc 1 N := by simp [hN1]
    have hone : (1 : ℝ)⁻¹ ≤ H N := by
      have hle := Finset.single_le_sum (f := fun k : ℕ => (k : ℝ)⁻¹)
        (fun k _ => inv_nonneg.mpr (Nat.cast_nonneg k)) hmem
      simpa [H] using hle
    have : (1 : ℝ) ≤ H N := by simpa using hone
    linarith
  let a : ℕ → ℝ := hardyTrunc p N
  have ha : ∀ n, 0 ≤ a n := fun n => hardyTrunc_nonneg p N n
  have hfin := hardyTrunc_support_finite p N
  have hbd := hbound a ha hfin
  have hpow : ∀ n, n < N → a n ^ p = (n + 1 : ℝ)⁻¹ := by
    intro n hn
    simp only [a, hardyTrunc, ite_eq_left hn]
    have hexp : -(1 / p) * p = -1 := by
      field_simp
    rw [← rpow_mul (by positivity : (0 : ℝ) ≤ (n + 1 : ℝ)), hexp, rpow_neg_one]
  have hR : ∑ n ∈ range N, a n ^ p = H N := by
    have hcast : ∑ n ∈ range N, a n ^ p = ∑ n ∈ range N, (↑(n + 1))⁻¹ := by
      refine sum_congr rfl fun n hn => ?_
      rw [hpow n (mem_range.mp hn), Nat.cast_add, Nat.cast_one]
    rw [hcast, range_eq_Ico, sum_Ico_add' (fun k : ℕ => (k : ℝ)⁻¹) 0 N (c := 1),
      Ico_add_one_right_eq_Icc]
  let S : ℕ → ℝ := fun m => ∑ k ∈ Icc 1 m, (k : ℝ) ^ (-(1 / p))
  have havg : ∀ n, n < N → hardyAverage a n = S (n + 1) / (n + 1 : ℝ) := by
    intro n hn
    have hterms : ∀ j ∈ range (n + 1), a j = (↑(j + 1)) ^ (-(1 / p)) := by
      intro j hj
      have hjN : j < N := lt_of_le_of_lt (Nat.le_of_lt_succ (mem_range.mp hj)) hn
      simp only [a, hardyTrunc, ite_eq_left hjN, Nat.cast_add, Nat.cast_one]
    simp only [hardyAverage, S]
    rw [sum_congr rfl hterms, range_eq_Ico,
      sum_Ico_add' (fun k : ℕ => (k : ℝ) ^ (-(1 / p))) 0 (n + 1) (c := 1),
      Ico_add_one_right_eq_Icc]
  have hpartial_ge : c * ∑ m ∈ Icc 1 N, φ m * (m : ℝ)⁻¹ ≤
      ∑ n ∈ range N, hardyAverage a n ^ p := by
    have hre : ∑ n ∈ range N, hardyAverage a n ^ p =
        ∑ m ∈ Icc 1 N, (S m / (m : ℝ)) ^ p := by
      rw [range_eq_Ico, ← Ico_add_one_right_eq_Icc,
        ← sum_Ico_add' (fun m : ℕ => (S m / (m : ℝ)) ^ p) 0 N (c := 1)]
      refine sum_congr rfl fun n hn => ?_
      rw [havg n (mem_Ico.mp hn).2, Nat.cast_add, Nat.cast_one]
    rw [hre, mul_sum]
    refine sum_le_sum fun m hm => ?_
    have hm1 : 1 ≤ m := (mem_Icc.mp hm).1
    have hlow := hardy_weight_term_lower hp hm1
    calc
      c * (φ m * (m : ℝ)⁻¹) = c * (m : ℝ)⁻¹ * φ m := by
        rw [mul_comm (φ m), mul_assoc]
      _ ≤ (S m / (m : ℝ)) ^ p := by
        simpa [S, φ, β] using hlow
  have hpartial_le : ∑ n ∈ range N, hardyAverage a n ^ p ≤ C * H N := by
    have hap : ∀ n, 0 ≤ a n ^ p := fun n => rpow_nonneg (ha n) _
    have havg_nonneg : ∀ n, 0 ≤ hardyAverage a n ^ p := fun n =>
      rpow_nonneg (div_nonneg (sum_nonneg fun j _ => ha j) (by positivity)) _
    have htail : ∀ n, N ≤ n → a n = 0 := fun n hn => by
      simp [a, hardyTrunc, not_lt.mpr hn]
    have hcompl : ∑' i : ↥((range N : Set ℕ)ᶜ), ENNReal.ofReal (a i ^ p) = 0 := by
      rw [ENNReal.tsum_eq_zero]
      rintro ⟨n, hn⟩
      have hnN : N ≤ n := by
        simpa [Set.mem_compl_iff, mem_coe, mem_range, not_lt] using hn
      rw [htail n hnN, zero_rpow hp0.ne', ENNReal.ofReal_zero]
    have htsumR : ∑' n, ENNReal.ofReal (a n ^ p) =
        ENNReal.ofReal (∑ n ∈ range N, a n ^ p) := by
      have hadd :=
        ENNReal.sum_add_tsum_compl (range N) (fun n => ENNReal.ofReal (a n ^ p))
      rw [hcompl, add_zero] at hadd
      rw [← hadd, ENNReal.ofReal_sum_of_nonneg fun n _ => hap n]
    have hge : ENNReal.ofReal (∑ n ∈ range N, hardyAverage a n ^ p) ≤
        ∑' n, ENNReal.ofReal (hardyAverage a n ^ p) := by
      rw [ENNReal.ofReal_sum_of_nonneg fun n _ => havg_nonneg n]
      exact ENNReal.sum_le_tsum (range N)
    have hmul := hbd
    rw [htsumR, hR] at hmul
    have : ENNReal.ofReal (∑ n ∈ range N, hardyAverage a n ^ p) ≤
        ENNReal.ofReal C * ENNReal.ofReal (H N) := le_trans hge hmul
    rw [← ENNReal.ofReal_mul hC] at this
    have hHN : 0 ≤ C * H N := mul_nonneg hC (le_of_lt hHpos)
    exact (ENNReal.ofReal_le_ofReal_iff hHN).mp this
  have hsplit : (1 - η) * (H N - H (M - 1)) ≤ ∑ m ∈ Icc 1 N, φ m * (m : ℝ)⁻¹ := by
    have hunion : Icc 1 (M - 1) ∪ Icc M N = Icc 1 N := by
      ext k
      simp only [mem_union, mem_Icc]
      omega
    have hdisj : Disjoint (Icc 1 (M - 1)) (Icc M N) := by
      rw [disjoint_left]
      intro k hk1 hk2
      simp only [mem_Icc] at hk1 hk2
      omega
    have hsum : ∑ m ∈ Icc 1 N, φ m * (m : ℝ)⁻¹ =
        ∑ m ∈ Icc 1 (M - 1), φ m * (m : ℝ)⁻¹ + ∑ m ∈ Icc M N, φ m * (m : ℝ)⁻¹ := by
      rw [← sum_union hdisj, hunion]
    have htail : (1 - η) * ∑ m ∈ Icc M N, (m : ℝ)⁻¹ ≤
        ∑ m ∈ Icc M N, φ m * (m : ℝ)⁻¹ := by
      rw [mul_sum]
      refine sum_le_sum fun m hm => ?_
      have hmM : M ≤ m := (mem_Icc.mp hm).1
      have hinv : 0 ≤ (m : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg m)
      exact mul_le_mul_of_nonneg_right (le_of_lt (hMφ m hmM)) hinv
    have hHsplit : H N = H (M - 1) + ∑ m ∈ Icc M N, (m : ℝ)⁻¹ := by
      have hsumH : ∑ m ∈ Icc 1 N, (m : ℝ)⁻¹ =
          ∑ m ∈ Icc 1 (M - 1), (m : ℝ)⁻¹ + ∑ m ∈ Icc M N, (m : ℝ)⁻¹ := by
        rw [← sum_union hdisj, hunion]
      simpa [H] using hsumH
    have hdrop : 0 ≤ ∑ m ∈ Icc 1 (M - 1), φ m * (m : ℝ)⁻¹ := by
      refine sum_nonneg fun m hm => ?_
      exact mul_nonneg (hφ_nonneg m (mem_Icc.mp hm).1) (inv_nonneg.mpr (Nat.cast_nonneg m))
    have htail_le : (1 - η) * (H N - H (M - 1)) ≤ ∑ m ∈ Icc M N, φ m * (m : ℝ)⁻¹ := by
      rw [hHsplit, add_sub_cancel_left]
      exact htail
    exact (le_trans htail_le (le_add_of_nonneg_left hdrop)).trans_eq hsum.symm
  have hratio : (1 - η) ^ 2 ≤ (∑ m ∈ Icc 1 N, φ m * (m : ℝ)⁻¹) / H N := by
    have hprev : H (M - 1) ≤ η * H N := by
      simpa [mul_comm] using (div_le_iff₀ hη0).mp hNge
    have hdiff : (1 - η) * H N ≤ H N - H (M - 1) := by linarith
    have hcomp : (1 - η) ^ 2 * H N ≤ (1 - η) * (H N - H (M - 1)) := by
      calc
        (1 - η) ^ 2 * H N = (1 - η) * ((1 - η) * H N) := by ring
        _ ≤ (1 - η) * (H N - H (M - 1)) :=
          mul_le_mul_of_nonneg_left hdiff (by linarith)
    exact (le_div_iff₀ hHpos).mpr (hcomp.trans hsplit)
  have hclose : c * (1 - δ) ≤ C := by
    have hquot : c * (1 - δ) ≤
        c * ((∑ m ∈ Icc 1 N, φ m * (m : ℝ)⁻¹) / H N) :=
      mul_le_mul_of_nonneg_left (le_trans hsq hratio) hc0.le
    rw [mul_div_assoc'] at hquot
    have hleC : (c * ∑ m ∈ Icc 1 N, φ m * (m : ℝ)⁻¹) / H N ≤ C := by
      rw [div_le_iff₀ hHpos]
      exact le_trans hpartial_ge hpartial_le
    exact hquot.trans hleC
  have hcδ : c * (1 - δ) = c - c * δ := by ring
  linarith

end CKMA
