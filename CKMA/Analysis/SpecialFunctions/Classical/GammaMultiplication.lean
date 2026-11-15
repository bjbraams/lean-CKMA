/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic

/-!
# Gauss's Gamma Multiplication Formula

Gauss multiplication relates a finite product of shifted Gamma values to a single
Gamma value at the multiplied argument, proved on the positive half-line via the
Bohr–Mollerup theorem and extended to the complex plane by analytic continuation of the
reciprocal Gamma product.

## Main results

* `CKMA.gamma_multiplication`: Gauss's multiplication formula at all nonpolar complex parameters
  (**49.6**).
-/

@[expose] public section

noncomputable section

namespace CKMA

/-- A finite sum of convex real functions on `(0, ∞)` is convex. -/
private theorem convexOn_sum {ι : Type*} {s : Finset ι} {f : ι → ℝ → ℝ}
    (hf : ∀ i ∈ s, ConvexOn ℝ (Set.Ioi 0) (f i)) :
    ConvexOn ℝ (Set.Ioi 0) (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using convexOn_const (0 : ℝ) (convex_Ioi (0 : ℝ))
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

open Filter Topology
open scoped BigOperators ENNReal NNReal

section GaussMultiplication

section RealFormula

open Real Finset Polynomial
open scoped Real

/-- `∏_{k=1}^{n-1} (1 - exp(2 π I / n) ^ k) = n`, including the empty product `1 = 1`. -/
private theorem prod_one_sub_exp (n : ℕ) (hn : 0 < n) :
    ∏ k ∈ Ioo 0 n, (1 - Complex.exp (2 * ↑π * Complex.I / n) ^ k) = n := by
  have : NeZero n := ⟨hn.ne'⟩
  let ζ : ℂ := Complex.exp (2 * ↑π * Complex.I / n)
  have hζ : IsPrimitiveRoot ζ n := Complex.isPrimitiveRoot_exp n hn.ne'
  have hpoly : X ^ n - 1 = ∏ k ∈ range n, (X - C (ζ ^ k)) := by
    rw [X_pow_sub_one_eq_prod hn hζ]
    exact (prod_nbij (fun k : ℕ => ζ ^ k)
      (fun k _ => by
        rw [mem_nthRootsFinset hn (1 : ℂ), ← pow_mul, mul_comm k n, pow_mul, hζ.pow_eq_one,
          one_pow])
      (fun a ha b hb hab => hζ.pow_inj (mem_range.mp ha) (mem_range.mp hb) hab)
      (fun μ hμ => by
        obtain ⟨k, hk, rfl⟩ :=
          hζ.eq_pow_of_pow_eq_one ((mem_nthRootsFinset hn (1 : ℂ)).mp hμ)
        exact ⟨k, mem_range.mpr hk, rfl⟩)
      (fun _ _ => rfl)).symm
  have hder : eval (1 : ℂ) (derivative (X ^ n - 1)) = n := by
    rw [derivative_sub, derivative_X_pow, derivative_one, sub_zero, eval_mul, eval_C, eval_pow,
      eval_X, one_pow, mul_one]
  have heval : eval (1 : ℂ) (derivative (∏ k ∈ range n, (X - C (ζ ^ k)))) =
      ∑ k ∈ range n, ∏ j ∈ (range n).erase k, (1 - ζ ^ j) := by
    rw [derivative_prod_finset, ← coe_evalRingHom (1 : ℂ), map_sum]
    refine sum_congr rfl fun _ _ => ?_
    rw [coe_evalRingHom, eval_mul, derivative_X_sub_C, eval_one, mul_one, eval_prod]
    refine prod_congr rfl fun _ _ => ?_
    rw [eval_sub, eval_X, eval_C]
  have hsum : ∑ k ∈ range n, ∏ j ∈ (range n).erase k, (1 - ζ ^ j) = n := by
    have h := congrArg (fun p : ℂ[X] => eval (1 : ℂ) (derivative p)) hpoly
    rw [hder, heval] at h
    exact h.symm
  rw [sum_eq_single (a := 0) (fun k hk hk0 => ?_) (fun h0 => ?_)] at hsum
  · have herase : (range n).erase 0 = Ioo 0 n := by
      ext k
      simp only [mem_erase, mem_range, mem_Ioo]
      exact ⟨fun h => ⟨Nat.pos_of_ne_zero h.1, h.2⟩, fun h => ⟨h.1.ne', h.2⟩⟩
    simpa [herase, ζ] using hsum
  · refine prod_eq_zero (mem_erase.mpr ⟨hk0.symm, mem_range.mpr hn⟩) ?_
    simp [pow_zero]
  · exact (h0 (mem_range.mpr hn)).elim

/-- `∏_{k=1}^{n-1} sin(π k / n) = n / 2^{n-1}`. The `n = 1` product is empty. -/
private theorem prod_sin_pi_div (n : ℕ) (hn : 0 < n) :
    ∏ k ∈ Ioo 0 n, sin (π * k / n) = (n : ℝ) / 2 ^ (n - 1) := by
  have hnorm := congrArg norm (prod_one_sub_exp n hn)
  rw [Complex.norm_prod, RCLike.norm_natCast] at hnorm
  have hterm : ∀ k ∈ Ioo 0 n,
      ‖1 - Complex.exp (2 * ↑π * Complex.I / n) ^ k‖ = 2 * sin (π * k / n) := by
    intro k hk
    have hk0 : 0 < k := (mem_Ioo.mp hk).1
    have hkn : k < n := (mem_Ioo.mp hk).2
    have hsin : 0 < sin (π * k / n) := by
      refine sin_pos_of_pos_of_lt_pi ?_ ?_
      · exact div_pos (mul_pos pi_pos (Nat.cast_pos.mpr hk0)) (Nat.cast_pos.mpr hn)
      · rw [div_lt_iff₀ (Nat.cast_pos.mpr hn)]
        exact mul_lt_mul_of_pos_left (by exact_mod_cast hkn) pi_pos
    have hx : (k : ℂ) * (2 * ↑π * Complex.I / n) =
        Complex.I * ↑(2 * π * (k : ℝ) / n) := by
      push_cast
      ring
    rw [← Complex.exp_nat_mul, hx, ← norm_neg, neg_sub,
      Complex.norm_exp_I_mul_ofReal_sub_one,
      show (2 * π * (k : ℝ) / n) / 2 = π * (k : ℝ) / n by ring, Real.norm_eq_abs, abs_mul,
      abs_of_pos two_pos, abs_of_pos hsin]
  have hcard : #(Ioo 0 n) = n - 1 := by
    have herase : (range n).erase 0 = Ioo 0 n := by
      ext k
      simp only [mem_erase, mem_range, mem_Ioo]
      exact ⟨fun h => ⟨Nat.pos_of_ne_zero h.1, h.2⟩, fun h => ⟨h.1.ne', h.2⟩⟩
    rw [← herase, card_erase_of_mem (mem_range.mpr hn), card_range]
  rw [prod_congr rfl hterm, prod_mul_distrib, prod_const, hcard, mul_comm] at hnorm
  rw [eq_div_iff_mul_eq (pow_ne_zero _ two_ne_zero)]
  exact hnorm

/-- The Gauss product at unit argument, `∏_{k=1}^{m-1} Gamma(k / m) = (2π)^{(m-1)/2} / √m`.
Reindexing `k ↦ m - k` pairs `k / m` with `(m - k) / m`, so an even `m` contributes the middle
factor `Gamma(1 / 2)` once on each side of the reflection identity. -/
private theorem prod_gamma_frac (m : ℕ) (hm : 0 < m) :
    ∏ k ∈ Ioo 0 m, Gamma ((k : ℝ) / m) =
      (2 * π) ^ (((m : ℝ) - 1) / 2) / sqrt m := by
  let P := ∏ k ∈ Ioo 0 m, Gamma ((k : ℝ) / m)
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hpos : 0 < P := by
    refine prod_pos fun k hk => Gamma_pos_of_pos ?_
    exact div_pos (Nat.cast_pos.mpr (mem_Ioo.mp hk).1) (Nat.cast_pos.mpr hm)
  have hre : ∏ k ∈ Ioo 0 m, Gamma (1 - (k : ℝ) / m) = P := by
    refine prod_nbij' (fun k => m - k) (fun k => m - k) ?_ ?_ ?_ ?_ ?_
    · intro k hk
      have hk' := mem_Ioo.mp hk
      rw [mem_Ioo]
      omega
    · intro k hk
      have hk' := mem_Ioo.mp hk
      rw [mem_Ioo]
      omega
    · intro k hk
      exact Nat.sub_sub_self (le_of_lt (mem_Ioo.mp hk).2)
    · intro k hk
      exact Nat.sub_sub_self (le_of_lt (mem_Ioo.mp hk).2)
    · intro k hk
      congr 1
      have hklt : k < m := (mem_Ioo.mp hk).2
      rw [Nat.cast_sub (le_of_lt hklt), sub_div, div_self hm0]
  have hcard : #(Ioo 0 m) = m - 1 := by
    have herase : (range m).erase 0 = Ioo 0 m := by
      ext k
      simp only [mem_erase, mem_range, mem_Ioo]
      exact ⟨fun h => ⟨Nat.pos_of_ne_zero h.1, h.2⟩, fun h => ⟨h.1.ne', h.2⟩⟩
    rw [← herase, card_erase_of_mem (mem_range.mpr hm), card_range]
  have hsq : P ^ 2 = (2 * π) ^ (m - 1) / m := by
    have hpair : P * P = ∏ k ∈ Ioo 0 m, (π / sin (π * (k : ℝ) / m)) := by
      calc
        P * P = (∏ k ∈ Ioo 0 m, Gamma ((k : ℝ) / m)) *
            (∏ k ∈ Ioo 0 m, Gamma (1 - (k : ℝ) / m)) := by rw [hre]
        _ = ∏ k ∈ Ioo 0 m, Gamma ((k : ℝ) / m) * Gamma (1 - (k : ℝ) / m) := by
          rw [prod_mul_distrib]
        _ = ∏ k ∈ Ioo 0 m, (π / sin (π * (k : ℝ) / m)) := by
          refine prod_congr rfl fun k _ => ?_
          rw [Gamma_mul_Gamma_one_sub, mul_div_assoc]
    calc
      P ^ 2 = P * P := by rw [sq]
      _ = ∏ k ∈ Ioo 0 m, (π / sin (π * (k : ℝ) / m)) := hpair
      _ = π ^ (m - 1) / ((m : ℝ) / 2 ^ (m - 1)) := by
        rw [prod_div_distrib, prod_const, hcard, prod_sin_pi_div m hm]
      _ = (π ^ (m - 1) * 2 ^ (m - 1)) / m := by rw [div_div_eq_mul_div]
      _ = (2 * π) ^ (m - 1) / m := by rw [mul_comm (π ^ _), ← mul_pow]
  have hbase : 0 ≤ 2 * π := (mul_pos two_pos pi_pos).le
  suffices hsqrt : P = (2 * π) ^ (((m : ℝ) - 1) / 2) / sqrt m by simpa [P] using hsqrt
  rw [← sqrt_sq hpos.le, hsq, sqrt_div (pow_nonneg hbase _)]
  congr 1
  rw [sqrt_eq_rpow, ← rpow_natCast, ← rpow_mul hbase]
  congr 1
  rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hm.ne')]
  ring

/-- `log Gamma((s + j) / m)` is convex for `s > 0`. -/
private theorem convexOn_log_gamma_div (m : ℕ) (hm : 0 < m) (j : ℕ) :
    ConvexOn ℝ (Set.Ioi 0) (fun s => log (Gamma ((s + j) / m))) := by
  refine ⟨convex_Ioi 0, fun x hx y hy a b ha hb hab => ?_⟩
  have hxj : (x + (j : ℝ)) / m ∈ Set.Ioi 0 := by
    rw [Set.mem_Ioi]
    exact div_pos (add_pos_of_pos_of_nonneg hx (Nat.cast_nonneg _)) (Nat.cast_pos.mpr hm)
  have hyj : (y + (j : ℝ)) / m ∈ Set.Ioi 0 := by
    rw [Set.mem_Ioi]
    exact div_pos (add_pos_of_pos_of_nonneg hy (Nat.cast_nonneg _)) (Nat.cast_pos.mpr hm)
  have harg : (a * x + b * y + (j : ℝ)) / m =
      a * ((x + (j : ℝ)) / m) + b * ((y + (j : ℝ)) / m) := by
    have hlin : a * x + b * y + (j : ℝ) = a * (x + j) + b * (y + j) := by
      calc
        a * x + b * y + j = a * x + b * y + (a + b) * j := by rw [hab, one_mul]
        _ = a * (x + j) + b * (y + j) := by ring
    rw [hlin, add_div, mul_div_assoc, mul_div_assoc]
  simp only [smul_eq_mul]
  rw [harg]
  simpa [Function.comp_apply] using convexOn_log_Gamma.2 hxj hyj ha hb hab

/-- Shifting the product of Gamma values by one step multiplies it by `s / m`. -/
private theorem prod_gamma_succ (m : ℕ) (hm : 0 < m) {s : ℝ} (hs : s ≠ 0) :
    ∏ k ∈ range m, Gamma ((s + (k + 1 : ℕ)) / m) =
      (s / m) * ∏ k ∈ range m, Gamma ((s + k) / m) := by
  have hle : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm.ne'
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hf : Gamma ((s + m) / m) = (s / m) * Gamma (s / m) := by
    have hdiv : (s + (m : ℝ)) / m = s / m + 1 := by rw [add_div, div_self hm0]
    rw [hdiv, Gamma_add_one (div_ne_zero hs hm0)]
  have hm1 : m = (m - 1) + 1 := (Nat.sub_add_cancel hle).symm
  have hleft : ∏ k ∈ range m, Gamma ((s + (k + 1 : ℕ)) / m) =
      (∏ k ∈ range (m - 1), Gamma ((s + (k + 1 : ℕ)) / m)) * Gamma ((s + m) / m) := by
    conv_lhs => rw [hm1]
    rw [prod_range_succ]
    simp [Nat.sub_add_cancel hle]
  have hright : ∏ k ∈ range m, Gamma ((s + k) / m) =
      (∏ k ∈ range (m - 1), Gamma ((s + (k + 1 : ℕ)) / m)) * Gamma (s / m) := by
    conv_lhs => rw [hm1]
    rw [prod_range_succ']
    simp [Nat.sub_add_cancel hle]
  rw [hleft, hright, hf]
  ring

/-- Bohr–Mollerup auxiliary for Gauss multiplication. It agrees with `Gamma` on `(0, ∞)`. -/
private def gaussMulGamma (m : ℕ) (s : ℝ) : ℝ :=
  (m : ℝ) ^ (s - 1 / 2) * (2 * π) ^ (((1 : ℝ) - m) / 2) *
    ∏ j : Fin m, Gamma ((s + j.val) / m)

/-- The auxiliary satisfies the Gamma recurrence for positive arguments. -/
private theorem gaussMulGamma_add_one (m : ℕ) (hm : 0 < m) {s : ℝ} (hs : 0 < s) :
    gaussMulGamma m (s + 1) = s * gaussMulGamma m s := by
  unfold gaussMulGamma
  rw [Fin.prod_univ_eq_prod_range (fun k => Gamma ((s + 1 + (k : ℝ)) / m)) m,
    Fin.prod_univ_eq_prod_range (fun k => Gamma ((s + (k : ℝ)) / m)) m]
  have hprod : ∏ k ∈ range m, Gamma ((s + 1 + k) / m) =
      (s / m) * ∏ k ∈ range m, Gamma ((s + k) / m) := by
    refine Eq.trans (prod_congr rfl fun k _ => ?_) (prod_gamma_succ m hm hs.ne')
    congr 1
    push_cast
    ring
  rw [hprod, show s + 1 - 1 / 2 = s - 1 / 2 + 1 by ring, rpow_add (Nat.cast_pos.mpr hm),
    rpow_one]
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  calc
      (m : ℝ) ^ (s - 1 / 2) * m * (2 * π) ^ (((1 : ℝ) - m) / 2) *
          ((s / m) * ∏ k ∈ range m, Gamma ((s + k) / m)) =
        (m : ℝ) ^ (s - 1 / 2) * (2 * π) ^ (((1 : ℝ) - m) / 2) * (m * (s / m)) *
          ∏ k ∈ range m, Gamma ((s + k) / m) := by ring
    _ = (m : ℝ) ^ (s - 1 / 2) * (2 * π) ^ (((1 : ℝ) - m) / 2) * s *
          ∏ k ∈ range m, Gamma ((s + k) / m) := by rw [mul_div_cancel₀ _ hm0]
    _ = s * ((m : ℝ) ^ (s - 1 / 2) * (2 * π) ^ (((1 : ℝ) - m) / 2) *
          ∏ k ∈ range m, Gamma ((s + k) / m)) := by ring

/-- The auxiliary equals `1` at `1`, by the reflected product of `Gamma(k / m)`. -/
private theorem gaussMulGamma_one (m : ℕ) (hm : 0 < m) : gaussMulGamma m 1 = 1 := by
  unfold gaussMulGamma
  rw [Fin.prod_univ_eq_prod_range (fun k => Gamma ((1 + (k : ℝ)) / m)) m]
  have hprod : ∏ k ∈ range m, Gamma ((1 + (k : ℝ)) / m) =
      ∏ k ∈ Ioo 0 m, Gamma ((k : ℝ) / m) := by
    have hmem : m ∉ Ioo 0 m := by simp [mem_Ioo]
    have hinsert : Icc 1 m = insert m (Ioo 0 m) := by
      ext k
      simp only [mem_Icc, mem_insert, mem_Ioo]
      omega
    have hI : ∏ k ∈ Icc 1 m, Gamma ((k : ℝ) / m) =
        ∏ k ∈ Ioo 0 m, Gamma ((k : ℝ) / m) := by
      rw [hinsert, prod_insert hmem, div_self (Nat.cast_ne_zero.mpr hm.ne'), Gamma_one, one_mul]
    have hbij : ∏ k ∈ range m, Gamma ((1 + (k : ℝ)) / m) =
        ∏ k ∈ Icc 1 m, Gamma ((k : ℝ) / m) := by
      refine prod_nbij' (fun k => k + 1) (fun k => k - 1) ?_ ?_ ?_ ?_ ?_
      · intro k hk
        rw [mem_range] at hk
        rw [mem_Icc]
        omega
      · intro k hk
        rw [mem_Icc] at hk
        rw [mem_range]
        omega
      · intro k _hk
        exact Nat.add_sub_cancel k 1
      · intro k hk
        exact Nat.sub_add_cancel (mem_Icc.mp hk).1
      · intro k hk
        congr 1
        push_cast
        ring
    rw [hbij, hI]
  rw [hprod, prod_gamma_frac m hm, show (1 : ℝ) - 1 / 2 = 1 / 2 by ring, sqrt_eq_rpow,
    div_eq_mul_inv]
  have h2π : 0 < 2 * π := mul_pos two_pos pi_pos
  have ha : (m : ℝ) ^ (1 / 2 : ℝ) ≠ 0 := (rpow_pos_of_pos (Nat.cast_pos.mpr hm) _).ne'
  calc
      (m : ℝ) ^ (1 / 2 : ℝ) * (2 * π) ^ (((1 : ℝ) - m) / 2) *
          ((2 * π) ^ (((m : ℝ) - 1) / 2) * ((m : ℝ) ^ (1 / 2 : ℝ))⁻¹) =
        (m : ℝ) ^ (1 / 2 : ℝ) * ((m : ℝ) ^ (1 / 2 : ℝ))⁻¹ *
          ((2 * π) ^ (((1 : ℝ) - m) / 2) * (2 * π) ^ (((m : ℝ) - 1) / 2)) := by ring
    _ = 1 := by
        rw [mul_inv_cancel₀ ha, one_mul, ← rpow_add h2π,
          show ((1 : ℝ) - m) / 2 + (((m : ℝ) - 1) / 2) = 0 by ring, rpow_zero]

/-- The auxiliary is positive on `(0, ∞)`. -/
private theorem gaussMulGamma_pos (m : ℕ) (hm : 0 < m) {s : ℝ} (hs : 0 < s) :
    0 < gaussMulGamma m s := by
  unfold gaussMulGamma
  refine mul_pos (mul_pos ?_ ?_) ?_
  · exact rpow_pos_of_pos (Nat.cast_pos.mpr hm) _
  · exact rpow_pos_of_pos (mul_pos two_pos pi_pos) _
  · refine prod_pos fun j _ => Gamma_pos_of_pos ?_
    exact div_pos (add_pos_of_pos_of_nonneg hs (Nat.cast_nonneg _)) (Nat.cast_pos.mpr hm)

/-- Logarithm of the auxiliary on the positive reals. -/
private theorem log_gaussMulGamma_eq (m : ℕ) (hm : 0 < m) :
    Set.EqOn (log ∘ gaussMulGamma m)
      (fun s => (s - 1 / 2) * log (m : ℝ) +
        ∑ j : Fin m, log (Gamma ((s + j.val) / m)) +
        ((1 - (m : ℝ)) / 2) * log (2 * π))
      (Set.Ioi 0) := by
  intro s hs
  have hm0 : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  have h2π : 0 < 2 * π := mul_pos two_pos pi_pos
  have hA : (m : ℝ) ^ (s - 1 / 2) ≠ 0 := (rpow_pos_of_pos hm0 _).ne'
  have hC : (2 * π) ^ (((1 : ℝ) - m) / 2) ≠ 0 := (rpow_pos_of_pos h2π _).ne'
  have hΓ : ∀ j : Fin m, Gamma ((s + j.val) / m) ≠ 0 := fun j =>
    (Gamma_pos_of_pos
      (div_pos (add_pos_of_pos_of_nonneg hs (Nat.cast_nonneg _)) hm0)).ne'
  have hP : ∏ j : Fin m, Gamma ((s + j.val) / m) ≠ 0 :=
    prod_ne_zero_iff.mpr fun j _ => hΓ j
  rw [Function.comp_apply, gaussMulGamma, log_mul (mul_ne_zero hA hC) hP, log_mul hA hC,
    log_rpow hm0, log_rpow h2π, log_prod fun j _ => hΓ j]
  ring

/-- The auxiliary is logarithmically convex on `(0, ∞)`. -/
private theorem gaussMulGamma_log_convex (m : ℕ) (hm : 0 < m) :
    ConvexOn ℝ (Set.Ioi 0) (log ∘ gaussMulGamma m) := by
  have hlog : 0 ≤ log (m : ℝ) :=
    log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm.ne')
  have hsmul : ConvexOn ℝ (Set.Ioi 0) (fun s : ℝ => log (m : ℝ) * s) := by
    simpa [smul_eq_mul] using (convexOn_id (convex_Ioi (0 : ℝ))).smul hlog
  have hlin : ConvexOn ℝ (Set.Ioi 0) (fun s => (s - 1 / 2) * log (m : ℝ)) := by
    have hfun : (fun s : ℝ => (s - 1 / 2) * log (m : ℝ)) =
        (fun s => log (m : ℝ) * s) + fun _ => -(1 / 2) * log (m : ℝ) := by
      ext s
      rw [Pi.add_apply, sub_mul, mul_comm s, sub_eq_add_neg, neg_mul]
    rw [hfun]
    exact hsmul.add_const _
  have hsum : ConvexOn ℝ (Set.Ioi 0)
      (fun s => ∑ j : Fin m, log (Gamma ((s + j.val) / m))) :=
    convexOn_sum fun j _ => convexOn_log_gamma_div m hm j.val
  exact ((hlin.add hsum).add_const (((1 - (m : ℝ)) / 2) * log (2 * π))).congr
    (log_gaussMulGamma_eq m hm).symm

/-- Bohr–Mollerup identifies the auxiliary with `Gamma` on `(0, ∞)`. -/
private theorem gaussMulGamma_eq_Gamma (m : ℕ) (hm : 0 < m) {s : ℝ} (hs : 0 < s) :
    gaussMulGamma m s = Gamma s :=
  eq_Gamma_of_log_convex (gaussMulGamma_log_convex m hm)
    (fun {_y} hy => gaussMulGamma_add_one m hm hy)
    (fun {_y} hy => gaussMulGamma_pos m hm hy)
    (gaussMulGamma_one m hm) hs

/-- Gauss multiplication for positive real arguments. -/
private theorem gamma_multiplication_pos (m : ℕ) (hm : 0 < m) {t : ℝ} (ht : 0 < t) :
    ∏ j : Fin m, Gamma (t + (j.val : ℝ) / m) =
      (2 * π) ^ (((m : ℝ) - 1) / 2) * (m : ℝ) ^ ((1 / 2 : ℝ) - m * t) * Gamma (m * t) := by
  have hg := gaussMulGamma_eq_Gamma m hm (mul_pos (Nat.cast_pos.mpr hm) ht)
  unfold gaussMulGamma at hg
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have harg : ∀ j : Fin m, ((m : ℝ) * t + j.val) / m = t + (j.val : ℝ) / m := by
    intro j
    field
  simp_rw [harg] at hg
  have h2π : 0 < 2 * π := mul_pos two_pos pi_pos
  let P : ℝ := ∏ j : Fin m, Gamma (t + (j.val : ℝ) / m)
  let A : ℝ := (m : ℝ) ^ ((m : ℝ) * t - 1 / 2)
  let C : ℝ := (2 * π) ^ (((1 : ℝ) - m) / 2)
  let G : ℝ := Gamma ((m : ℝ) * t)
  have hA : A ≠ 0 := (rpow_pos_of_pos (Nat.cast_pos.mpr hm) _).ne'
  have hC : C ≠ 0 := (rpow_pos_of_pos h2π _).ne'
  have hG : A * C * P = G := by simpa [P, A, C, G] using hg
  have hP : P = (A * C)⁻¹ * G := by
    calc
        P = (A * C)⁻¹ * ((A * C) * P) := by
          rw [← mul_assoc, inv_mul_cancel₀ (mul_ne_zero hA hC), one_mul]
      _ = (A * C)⁻¹ * G := by rw [hG]
  have hresult : P = (2 * π) ^ (((m : ℝ) - 1) / 2) *
      (m : ℝ) ^ ((1 / 2 : ℝ) - (m : ℝ) * t) * G := by
    rw [hP, mul_inv, ← rpow_neg h2π.le, ← rpow_neg (Nat.cast_nonneg m),
      show -((m : ℝ) * t - 1 / 2) = (1 / 2 : ℝ) - (m : ℝ) * t by ring,
      show -(((1 : ℝ) - m) / 2) = ((m : ℝ) - 1) / 2 by ring,
      mul_comm ((m : ℝ) ^ ((1 / 2 : ℝ) - (m : ℝ) * t))
        ((2 * π) ^ (((m : ℝ) - 1) / 2))]
  simpa [P, G] using hresult

end RealFormula

section ComplexContinuation

open Complex Finset

/-- Casting the positive-real multiplication formula to the reciprocal Gamma function. -/
private theorem gamma_multiplication_ofReal (m : ℕ) (hm : 0 < m) {t : ℝ} (ht : 0 < t) :
    ∏ j : Fin m, (Gamma ((t : ℂ) + (j.val : ℂ) / m))⁻¹ =
      (2 * Real.pi : ℂ) ^ (-(((m : ℂ) - 1) / 2)) *
        (m : ℂ) ^ ((m : ℂ) * t - 1 / 2) * (Gamma ((m : ℂ) * t))⁻¹ := by
  have hreal := gamma_multiplication_pos m hm ht
  have h2π : 0 < 2 * Real.pi := mul_pos two_pos Real.pi_pos
  let P : ℝ := ∏ j : Fin m, Real.Gamma (t + (j.val : ℝ) / m)
  let B : ℝ := (2 * Real.pi) ^ (((m : ℝ) - 1) / 2)
  let A : ℝ := (m : ℝ) ^ ((1 / 2 : ℝ) - (m : ℝ) * t)
  let G : ℝ := Real.Gamma ((m : ℝ) * t)
  have hmul : P = B * A * G := by simpa [P, B, A, G] using hreal
  have hinv : P⁻¹ =
      (2 * Real.pi) ^ (-(((m : ℝ) - 1) / 2)) *
        (m : ℝ) ^ ((m : ℝ) * t - 1 / 2) * G⁻¹ := by
    have hord : P⁻¹ = B⁻¹ * A⁻¹ * G⁻¹ := by
      calc
        P⁻¹ = (B * A * G)⁻¹ := by rw [hmul]
        _ = (B * A)⁻¹ * G⁻¹ := by rw [mul_inv]
        _ = B⁻¹ * A⁻¹ * G⁻¹ := by rw [mul_inv]
    simp only [B, A] at hord
    rw [hord, ← Real.rpow_neg h2π.le, ← Real.rpow_neg (Nat.cast_nonneg m),
      show -((1 / 2 : ℝ) - (m : ℝ) * t) = (m : ℝ) * t - 1 / 2 by ring]
  have hC : ((P⁻¹ : ℝ) : ℂ) =
      (2 * Real.pi : ℂ) ^ (-(((m : ℂ) - 1) / 2)) *
        (m : ℂ) ^ ((m : ℂ) * t - 1 / 2) * ((G : ℝ) : ℂ)⁻¹ := by
    rw [hinv, ofReal_mul, ofReal_mul, ofReal_inv, ofReal_cpow h2π.le,
      ofReal_cpow (Nat.cast_nonneg m)]
    push_cast
    ring
  have hPcast : ((P : ℝ) : ℂ) =
      ∏ j : Fin m, Gamma ((t : ℂ) + (j.val : ℂ) / m) := by
    simp only [P]
    rw [ofReal_prod]
    refine prod_congr rfl fun j _ => ?_
    rw [← Gamma_ofReal]
    congr 1
    push_cast
    ring
  rw [prod_inv_distrib, ← hPcast, ← ofReal_inv, hC]
  congr 1
  simp only [G]
  rw [← Gamma_ofReal]
  congr 1
  push_cast
  ring

/-- A factor `z + j / m` is nonpolar whenever `m * z` is. -/
private theorem gamma_factor_not_nonpos (m : ℕ) (hm : 0 < m) (z : ℂ)
    (hz : ∀ n : ℕ, (m : ℂ) * z ≠ -(n : ℂ)) (j : Fin m) (k : ℕ) :
    z + (j.val : ℂ) / m ≠ -(k : ℂ) := by
  intro h
  apply hz (k * m + j.val)
  have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hmul := congrArg (fun w : ℂ => (m : ℂ) * w) h
  rw [mul_add, mul_div_cancel₀ _ hm0, mul_neg] at hmul
  have hsub : (m : ℂ) * z = -((m : ℂ) * k) - j.val := (eq_sub_iff_add_eq).mpr hmul
  rw [hsub, sub_eq_add_neg, ← neg_add, mul_comm (m : ℂ), ← Nat.cast_mul, Nat.mul_comm,
    ← Nat.cast_add]

/-- Reciprocal form of Gauss multiplication, entire in the argument. -/
private theorem gamma_inv_mul_eq (m : ℕ) (hm : 0 < m) (z : ℂ) :
    ∏ j : Fin m, (Gamma (z + (j.val : ℂ) / m))⁻¹ =
      (2 * Real.pi : ℂ) ^ (-(((m : ℂ) - 1) / 2)) *
        (m : ℂ) ^ ((m : ℂ) * z - 1 / 2) * (Gamma ((m : ℂ) * z))⁻¹ := by
  let f : ℂ → ℂ := fun z => ∏ j : Fin m, (Gamma (z + (j.val : ℂ) / m))⁻¹
  let g : ℂ → ℂ := fun z =>
    (2 * Real.pi : ℂ) ^ (-(((m : ℂ) - 1) / 2)) *
      (m : ℂ) ^ ((m : ℂ) * z - 1 / 2) * (Gamma ((m : ℂ) * z))⁻¹
  have h1 : AnalyticOnNhd ℂ f Set.univ := by
    refine Finset.univ.analyticOnNhd_fun_prod fun j _ => ?_
    refine DifferentiableOn.analyticOnNhd ?_ isOpen_univ
    exact (differentiable_one_div_Gamma.comp
      (differentiable_id.add_const ((j.val : ℂ) / m))).differentiableOn
  have h2 : AnalyticOnNhd ℂ g Set.univ := by
    refine DifferentiableOn.analyticOnNhd ?_ isOpen_univ
    refine Differentiable.differentiableOn ?_
    refine (Differentiable.mul (Differentiable.mul (differentiable_const _) ?_) ?_)
    · intro w
      exact DifferentiableAt.const_cpow ((differentiableAt_id.const_mul _).sub_const _)
        (Or.inl (Nat.cast_ne_zero.mpr hm.ne'))
    · exact differentiable_one_div_Gamma.comp (differentiable_id.const_mul (m : ℂ))
  have h3 : Tendsto ((↑) : ℝ → ℂ) (𝓝[≠] (1 : ℝ)) (𝓝[≠] (1 : ℂ)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · exact tendsto_nhdsWithin_of_tendsto_nhds continuous_ofReal.continuousAt
    · exact eventually_nhdsWithin_iff.mpr
        (Eventually.of_forall fun t ht => ofReal_ne_one.mpr ht)
  have hfg : f = g := by
    refine AnalyticOnNhd.eq_of_frequently_eq h1 h2 (h3.frequently ?_)
    refine ((Eventually.filter_mono nhdsWithin_le_nhds) ?_).frequently
    refine (eventually_gt_nhds zero_lt_one).mp (Eventually.of_forall fun t ht => ?_)
    simpa [f, g] using gamma_multiplication_ofReal m hm ht
  simpa [f, g] using congr_fun hfg z

/-- **49.6**: Gauss's multiplication formula at all nonpolar complex parameters.
The positive real bases fix the principal-power branches. -/
theorem gamma_multiplication (m : ℕ) (hm : 0 < m) (z : ℂ)
    (hz : ∀ n : ℕ, (m : ℂ) * z ≠ -(n : ℂ)) :
    (∏ j : Fin m, Complex.Gamma (z + (j.val : ℂ) / m)) =
      (2 * Real.pi : ℂ) ^ (((m : ℂ) - 1) / 2) *
      (m : ℂ) ^ ((1 / 2 : ℂ) - (m : ℂ) * z) * Complex.Gamma ((m : ℂ) * z) := by
  let P := ∏ j : Fin m, Gamma (z + (j.val : ℂ) / m)
  let B := (2 * Real.pi : ℂ) ^ (-(((m : ℂ) - 1) / 2))
  let M := (m : ℂ) ^ ((m : ℂ) * z - 1 / 2)
  let G := Gamma ((m : ℂ) * z)
  have hP : P ≠ 0 := by
    rw [prod_ne_zero_iff]
    intro j _
    exact Gamma_ne_zero fun k => gamma_factor_not_nonpos m hm z hz j k
  have hG : G ≠ 0 := Gamma_ne_zero hz
  have hB : B ≠ 0 :=
    (cpow_ne_zero_iff).2 (Or.inl (mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)))
  have hM : M ≠ 0 := (cpow_ne_zero_iff).2 (Or.inl (Nat.cast_ne_zero.mpr hm.ne'))
  have h : P⁻¹ = B * M * G⁻¹ := by
    simpa [P, B, M, G, prod_inv_distrib] using gamma_inv_mul_eq m hm z
  have h' : P⁻¹ * G = B * M := by
    calc
        P⁻¹ * G = (B * M * G⁻¹) * G := by rw [h]
      _ = B * M * (G⁻¹ * G) := by rw [mul_assoc]
      _ = B * M := by rw [inv_mul_cancel₀ hG, mul_one]
  have hGeq : G = P * (B * M) := by
    have hmul := congrArg (fun w => P * w) h'
    rwa [← mul_assoc, mul_inv_cancel₀ hP, one_mul] at hmul
  have hPeq : P = G * (B * M)⁻¹ := by
    calc
        P = (B * M)⁻¹ * ((B * M) * P) := by
          rw [← mul_assoc, inv_mul_cancel₀ (mul_ne_zero hB hM), one_mul]
      _ = (B * M)⁻¹ * G := by rw [mul_comm (B * M) P, hGeq]
      _ = G * (B * M)⁻¹ := by rw [mul_comm]
  have hMinv : M⁻¹ = (m : ℂ) ^ ((1 / 2 : ℂ) - (m : ℂ) * z) := by
    simp only [M]
    rw [← cpow_neg]
    congr 1
    ring
  have hBinv : B⁻¹ = (2 * Real.pi : ℂ) ^ (((m : ℂ) - 1) / 2) := by
    simp only [B]
    rw [← cpow_neg]
    congr 1
    rw [neg_neg]
  suffices P = (2 * Real.pi : ℂ) ^ (((m : ℂ) - 1) / 2) *
      (m : ℂ) ^ ((1 / 2 : ℂ) - (m : ℂ) * z) * G by
    simpa [P, G] using this
  rw [hPeq, mul_inv, hMinv, hBinv, mul_comm]

end ComplexContinuation

end GaussMultiplication

end CKMA
