/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
public import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.SpecialFunctions.Bessel
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Topology.Algebra.GroupWithZero
public import Mathlib.Topology.Algebra.InfiniteSum.Constructions
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.Convex.Function
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Data.Fintype.BigOperators
public import CKMA.Analysis.Complex.Basic

/-!
# Gamma multiplication, Gauss's equation and Bessel generating series

Gauss multiplication relates a finite product of shifted Gamma values to a single
Gamma value at the multiplied argument. The hypergeometric series solves Gauss's
equation and is the unique normalized analytic solution germ; the three singular
points are regular singular, as witnessed by analytic rational germs in local and
reciprocal coordinates. The bilateral integer-order Bessel generating series
converges normally away from its auxiliary variable's origin.

Gauss's equation follows from Mathlib's regularized coefficient recurrence and
formal derivative-series API, then its Gamma-scaling identity gives the ordinary version.

Sources: GAPS 49.6, 49.13 and 49.30. Special functions and branches reuse Mathlib.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Filter Topology
open scoped BigOperators ENNReal NNReal

section GaussMultiplication

section RealFormula

open Real Finset Polynomial
open scoped Real

set_option linter.style.haveILetI false in
/-- `∏_{k=1}^{n-1} (1 - exp(2 π I / n) ^ k) = n`, including the empty product `1 = 1`. -/
private theorem prod_one_sub_exp (n : ℕ) (hn : 0 < n) :
    ∏ k ∈ Ioo 0 n, (1 - Complex.exp (2 * ↑π * Complex.I / n) ^ k) = n := by
  haveI : NeZero n := ⟨hn.ne'⟩
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

/-- A finite sum of convex real functions on `(0, ∞)` is convex. -/
private theorem convexOn_sum {ι : Type*} {s : Finset ι} {f : ι → ℝ → ℝ}
    (hf : ∀ i ∈ s, ConvexOn ℝ (Set.Ioi 0) (f i)) :
    ConvexOn ℝ (Set.Ioi 0) (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using convexOn_const (0 : ℝ) (convex_Ioi (0 : ℝ))
  | insert a s ha ih =>
    have hfun : (fun x => ∑ i ∈ insert a s, f i x) =
        (fun x => f a x) + fun x => ∑ i ∈ s, f i x := by
      ext x
      simp [sum_insert ha]
    rw [hfun]
    exact (hf a (mem_insert_self a s)).add
      (ih fun i hi => hf i (mem_insert_of_mem hi))

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
    convexOn_sum (s := (univ : Finset (Fin m)))
      (fun j _ => convexOn_log_gamma_div m hm j.val)
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

/-- Gauss's hypergeometric differential expression. -/
def gaussDifferentialExpression (a b c : ℂ) (y : ℂ → ℂ) (z : ℂ) : ℂ :=
  z * (1 - z) * deriv (deriv y) z + (c - (a + b + 1) * z) * deriv y z - a * b * y z

/-- Termwise differentiation of a scalar power series inside its convergence ball. -/
private theorem hasSum_deriv_of_powerSeries {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    {r : ℝ≥0∞} (h : HasFPowerSeriesOnBall f p 0 r) {z : ℂ}
    (hz : (‖z‖₊ : ℝ≥0∞) < r) :
    HasSum (fun n : ℕ ↦ ((n : ℂ) + 1) * p.coeff (n + 1) * z ^ n) (deriv f z) := by
  have hh := (ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).hasSum
    (h.fderiv.hasSum (y := z) (by simpa [edist_eq_enorm_sub, enorm_eq_nnnorm] using hz))
  simpa only [FormalMultilinearSeries.apply_eq_pow_smul_coeff,
    ContinuousLinearMap.apply_apply, map_smul,
    FormalMultilinearSeries.derivSeries_coeff_one, smul_eq_mul, Nat.cast_add,
    Nat.cast_one, nsmul_eq_mul, add_zero, zero_add, mul_assoc, mul_comm, mul_left_comm,
    deriv] using hh

/-- The second derivative of a scalar power series is its twice differentiated sum. -/
private theorem hasSum_second_deriv_of_powerSeries {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    {r : ℝ≥0∞} (h : HasFPowerSeriesOnBall f p 0 r) {z : ℂ}
    (hz : (‖z‖₊ : ℝ≥0∞) < r) :
    HasSum (fun n : ℕ ↦ ((n : ℂ) + 1) * ((n : ℂ) + 2) * p.coeff (n + 2) * z ^ n)
      (deriv (deriv f) z) := by
  let q := (ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).compFormalMultilinearSeries p.derivSeries
  have hd : HasFPowerSeriesOnBall (deriv f) q 0 r :=
    (ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).comp_hasFPowerSeriesOnBall h.fderiv
  have hq (n : ℕ) : q.coeff n = ((n : ℂ) + 1) * p.coeff (n + 1) := by
    change p.derivSeries.coeff n 1 = _
    simp only [FormalMultilinearSeries.derivSeries_coeff_one, nsmul_eq_mul,
      Nat.cast_add, Nat.cast_one]
  convert hasSum_deriv_of_powerSeries hd hz using 1
  ext n
  rw [hq]
  push_cast
  ring

/-- Multiplying a power series by its variable shifts the weighted coefficients. -/
private theorem hasSum_mul_pow_of_succ {d : ℕ → ℂ} {v : ℂ} (z : ℂ)
    (h : HasSum (fun n : ℕ ↦ ((n : ℂ) + 1) * d (n + 1) * z ^ n) v) :
    HasSum (fun n : ℕ ↦ (n : ℂ) * d n * z ^ n) (z * v) := by
  rw [← hasSum_nat_add_iff' 1]
  convert h.mul_left z using 1
  · ext n
    simp only [Nat.cast_add, Nat.cast_one, pow_succ]
    ring
  · simp

/-- A coefficient identity supplies the hypothesis of the weighted shift. -/
private theorem hasSum_mul_pow_of_succ_of_congr {a d : ℕ → ℂ} {v z : ℂ}
    (h : HasSum (fun n : ℕ ↦ a n * z ^ n) v)
    (ha : ∀ n, a n = ((n : ℂ) + 1) * d (n + 1)) :
    HasSum (fun n : ℕ ↦ (n : ℂ) * d n * z ^ n) (z * v) := by
  have hpre : HasSum (fun n : ℕ ↦ ((n : ℂ) + 1) * d (n + 1) * z ^ n) v := by
    convert h using 1
    ext n
    rw [ha n]
  exact hasSum_mul_pow_of_succ z hpre

/-- The regularized Gauss series and its first two derivatives converge in the unit disk. -/
private theorem hasSum_regularizedGaussHGFun_derivs (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    let p := Complex.regularizedGaussHGFunSeries a b c
    HasSum (fun n : ℕ ↦ p.coeff n * z ^ n) (Complex.regularizedGaussHGFun a b c z) ∧
    HasSum (fun n : ℕ ↦ ((n : ℂ) + 1) * p.coeff (n + 1) * z ^ n)
      (deriv (Complex.regularizedGaussHGFun a b c) z) ∧
    HasSum (fun n : ℕ ↦ ((n : ℂ) + 1) * ((n : ℂ) + 2) * p.coeff (n + 2) * z ^ n)
      (deriv (deriv (Complex.regularizedGaussHGFun a b c)) z) := by
  intro p
  have hr : 1 ≤ p.radius := Complex.radius_regularizedGaussHGFunSeries_ge_one a b c
  have hp := p.hasFPowerSeriesOnBall (lt_of_lt_of_le zero_lt_one hr)
  have hz' : (‖z‖₊ : ℝ≥0∞) < p.radius :=
    (by exact_mod_cast hz : (‖z‖₊ : ℝ≥0∞) < 1).trans_le hr
  refine ⟨?_, hasSum_deriv_of_powerSeries hp hz', hasSum_second_deriv_of_powerSeries hp hz'⟩
  convert hp.hasSum (y := z) (by simpa [edist_eq_enorm_sub, enorm_eq_nnnorm] using hz') using 1
  · ext n
    simp [mul_comm]
  · simp [Complex.regularizedGaussHGFun, p]

/-- The Gauss coefficient recurrence at a nonpolar denominator parameter. -/
private theorem regularizedGaussHGFunSeries_coeff_recurrence (a b c : ℂ)
    (hc : ∀ n : ℕ, c ≠ -(n : ℂ)) (n : ℕ) :
    ((n : ℂ) + 1) * (c + n) *
        (Complex.regularizedGaussHGFunSeries a b c).coeff (n + 1) =
      (a + n) * (b + n) * (Complex.regularizedGaussHGFunSeries a b c).coeff n := by
  have hh := Complex.regularizedHGFunCoeff_add_one (a := {a, b}) (b := {c})
    (n := n) (by simpa using hc n)
  have hn : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hcn : c + (n : ℂ) ≠ 0 := by simpa [eq_neg_iff_add_eq_zero] using hc n
  have hh' : (Complex.regularizedGaussHGFunSeries a b c).coeff (n + 1) =
      (Complex.regularizedGaussHGFunSeries a b c).coeff n *
        ((a + n) * (b + n) / ((c + n) * ((n : ℂ) + 1))) := by
    simpa [Complex.regularizedGaussHGFunSeries] using hh
  rw [hh']
  field_simp

/-- The regularized Gauss hypergeometric function satisfies Gauss's equation in the unit disk. -/
theorem gauss_regularized_hypergeometric_ode (a b c : ℂ) (hc : ∀ n : ℕ, c ≠ -(n : ℂ))
    {z : ℂ} (hz : ‖z‖ < 1) :
    gaussDifferentialExpression a b c (Complex.regularizedGaussHGFun a b c) z = 0 := by
  let d := (Complex.regularizedGaussHGFunSeries a b c).coeff
  let y := Complex.regularizedGaussHGFun a b c
  obtain ⟨h0, h1, h2⟩ := hasSum_regularizedGaussHGFun_derivs a b c hz
  have he1 := hasSum_mul_pow_of_succ z h1
  have he2 : HasSum (fun n : ℕ ↦ (n : ℂ) * ((n : ℂ) + 1) * d (n + 1) * z ^ n)
      (z * deriv (deriv y) z) := by
    convert hasSum_mul_pow_of_succ_of_congr
        (d := fun n ↦ ((n : ℂ) + 1) * d (n + 1)) h2 (fun n ↦ by push_cast; ring) using 1
    ext n
    ring
  have he22 : HasSum (fun n : ℕ ↦ (n : ℂ) * ((n : ℂ) - 1) * d n * z ^ n)
      (z * (z * deriv (deriv y) z)) := by
    convert hasSum_mul_pow_of_succ_of_congr
        (d := fun n ↦ ((n : ℂ) - 1) * d n) he2 (fun n ↦ by push_cast; ring) using 1
    ext n
    ring

  have ha := he2.add (h1.mul_left c)
  have hb := (he22.add (he1.mul_left (a + b + 1))).add (h0.mul_left (a * b))
  have ht :
      (fun n : ℕ ↦ (n : ℂ) * ((n : ℂ) + 1) * d (n + 1) * z ^ n +
        c * (((n : ℂ) + 1) * d (n + 1) * z ^ n)) =
      (fun n : ℕ ↦ (n : ℂ) * ((n : ℂ) - 1) * d n * z ^ n +
        (a + b + 1) * ((n : ℂ) * d n * z ^ n) + (a * b) * (d n * z ^ n)) := by
    funext n
    have hh := regularizedGaussHGFunSeries_coeff_recurrence a b c hc n
    dsimp [d]
    linear_combination (z ^ n) * hh
  change HasSum _ _ at hb
  rw [← ht] at hb
  have heq := ha.unique hb
  dsimp [gaussDifferentialExpression]
  dsimp [y] at heq
  linear_combination heq

/-- **49.13**: the hypergeometric series solves Gauss's equation in the unit disk.
The denominator parameter must avoid the nonpositive integers. -/
theorem gauss_hypergeometric_ode (a b c : ℂ) (hc : ∀ n : ℕ, c ≠ -(n : ℂ))
    {z : ℂ} (hz : ‖z‖ < 1) :
    gaussDifferentialExpression a b c (ordinaryHypergeometric a b c) z = 0 := by
  have he : ordinaryHypergeometric a b c =
      fun w ↦ Complex.Gamma c * Complex.regularizedGaussHGFun a b c w := by
    funext w
    have hh := Complex.ordinaryHypergeometric_div_Gamma_eq (a := a) (b := b) (z := w) hc
    exact (div_eq_iff (Complex.Gamma_ne_zero hc)).mp hh |>.trans (mul_comm _ _)
  rw [he]
  have hh := gauss_regularized_hypergeometric_ode a b c hc hz
  simp only [gaussDifferentialExpression, deriv_const_mul_field', deriv_const_mul_field] at *
  linear_combination Complex.Gamma c * hh

/-- A scalar series that sums to zero near the origin has all coefficients zero. -/
private theorem coeff_eq_zero_of_hasSum_zero_nhds {e : ℕ → ℂ}
    (h : ∀ᶠ z in 𝓝 (0 : ℂ), HasSum (fun n : ℕ ↦ e n * z ^ n) 0) (n : ℕ) : e n = 0 := by
  let p : FormalMultilinearSeries ℂ ℂ ℂ := .ofScalars ℂ e
  have hp : HasFPowerSeriesAt (0 : ℂ → ℂ) p 0 := by
    rw [hasFPowerSeriesAt_iff]
    filter_upwards [h] with z hz
    convert hz using 1
    ext k
    simp [p, FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul, mul_comm]
  have hcoeff : p.coeff n = e n := by simp [p, FormalMultilinearSeries.coeff_ofScalars]
  rw [← hcoeff]
  exact FormalMultilinearSeries.coeff_eq_zero.mpr (congr_fun hp.eq_zero n)

/-- Inside its disk, Gauss's expression is the series of the coefficient discrepancies. -/
private theorem hasSum_gaussDifferentialExpression_coeff {y : ℂ → ℂ}
    {p : FormalMultilinearSeries ℂ ℂ ℂ} {r : ℝ≥0∞} (hp : HasFPowerSeriesOnBall y p 0 r)
    (a b c : ℂ) {z : ℂ} (hz : (‖z‖₊ : ℝ≥0∞) < r) :
    HasSum (fun n : ℕ ↦ (((n : ℂ) + 1) * (c + n) * p.coeff (n + 1) -
        (a + n) * (b + n) * p.coeff n) * z ^ n) (gaussDifferentialExpression a b c y z) := by
  let d := p.coeff
  have h0 : HasSum (fun n : ℕ ↦ d n * z ^ n) (y z) := by
    convert hp.hasSum (by simpa [Metric.mem_eball, edist_eq_enorm_sub, enorm_eq_nnnorm] using hz)
      using 1
    · ext n
      simp [d, mul_comm]
    · simp
  have h1 := hasSum_deriv_of_powerSeries hp hz
  have h2 := hasSum_second_deriv_of_powerSeries hp hz
  have he1 := hasSum_mul_pow_of_succ z h1
  have he2 : HasSum (fun n : ℕ ↦ (n : ℂ) * ((n : ℂ) + 1) * d (n + 1) * z ^ n)
      (z * deriv (deriv y) z) := by
    convert hasSum_mul_pow_of_succ_of_congr
        (d := fun n ↦ ((n : ℂ) + 1) * d (n + 1)) h2 (fun n ↦ by push_cast; ring) using 1
    ext n
    ring
  have he22 : HasSum (fun n : ℕ ↦ (n : ℂ) * ((n : ℂ) - 1) * d n * z ^ n)
      (z * (z * deriv (deriv y) z)) := by
    convert hasSum_mul_pow_of_succ_of_congr
        (d := fun n ↦ ((n : ℂ) - 1) * d n) he2 (fun n ↦ by push_cast; ring) using 1
    ext n
    ring
  have hH := (((he2.sub he22).add (h1.mul_left c)).sub (he1.mul_left (a + b + 1))).sub
    (h0.mul_left (a * b))
  have hval :
      ((z * deriv (deriv y) z - z * (z * deriv (deriv y) z)) + c * deriv y z) -
        (a + b + 1) * (z * deriv y z) - (a * b) * y z =
      gaussDifferentialExpression a b c y z := by
    dsimp [gaussDifferentialExpression]
    ring
  rw [hval] at hH
  convert hH using 1
  ext n
  ring

/-- Taylor coefficients of an analytic solution of Gauss's equation obey its recurrence. -/
private theorem gauss_powerSeries_coeff_recurrence (a b c : ℂ) {y : ℂ → ℂ}
    {p : FormalMultilinearSeries ℂ ℂ ℂ} {r : ℝ≥0∞} (hp : HasFPowerSeriesOnBall y p 0 r)
    (hode : ∀ᶠ z in 𝓝 (0 : ℂ), gaussDifferentialExpression a b c y z = 0) (n : ℕ) :
    ((n : ℂ) + 1) * (c + n) * p.coeff (n + 1) = (a + n) * (b + n) * p.coeff n := by
  have hdisk : ∀ᶠ z in 𝓝 (0 : ℂ), (‖z‖₊ : ℝ≥0∞) < r :=
    eventually_of_mem (Metric.eball_mem_nhds (0 : ℂ) hp.r_pos) fun z hz ↦ by
      simpa [Metric.mem_eball, edist_eq_enorm_sub, enorm_eq_nnnorm, sub_zero] using hz
  have hsum0 : ∀ᶠ z in 𝓝 (0 : ℂ), HasSum (fun n : ℕ ↦ (((n : ℂ) + 1) * (c + n) *
      p.coeff (n + 1) - (a + n) * (b + n) * p.coeff n) * z ^ n) 0 := by
    filter_upwards [hode, hdisk] with z hodez hz
    simpa [hodez] using hasSum_gaussDifferentialExpression_coeff hp a b c hz
  exact sub_eq_zero.mp (coeff_eq_zero_of_hasSum_zero_nhds hsum0 n)

/-- The ordinary series is the Gamma multiple of the regularized series, so its constant term is
one. -/
private theorem ordinaryHypergeometricSeries_coeff_zero (a b c : ℂ)
    (hc : ∀ n : ℕ, c ≠ -(n : ℂ)) :
    (ordinaryHypergeometricSeries ℂ a b c).coeff 0 = 1 := by
  have hreg : (Complex.regularizedGaussHGFunSeries a b c).coeff 0 = (Complex.Gamma c)⁻¹ := by
    simp [Complex.coeff_regularizedGaussHGFunSeries, ascPochhammer_zero, Polynomial.eval_one,
      Nat.factorial_zero, Nat.cast_one, one_div]
  have hg : Complex.Gamma c ≠ 0 := Complex.Gamma_ne_zero hc
  have hscale : (ordinaryHypergeometricSeries ℂ a b c).coeff 0 =
      Complex.Gamma c * (Complex.regularizedGaussHGFunSeries a b c).coeff 0 := by
    rw [← Complex.Gamma_inv_mul_ordinaryHypergeometricSeries_eq (a := a) (b := b) hc (n := 0),
      ← mul_assoc, mul_inv_cancel₀ hg, one_mul]
  rw [hscale, hreg, mul_inv_cancel₀ hg]

/-- Ordinary coefficients are the Gamma multiple of the regularized coefficients, so they obey the
same recurrence. -/
private theorem ordinaryHypergeometricSeries_coeff_recurrence (a b c : ℂ)
    (hc : ∀ n : ℕ, c ≠ -(n : ℂ)) (n : ℕ) :
    ((n : ℂ) + 1) * (c + n) * (ordinaryHypergeometricSeries ℂ a b c).coeff (n + 1) =
      (a + n) * (b + n) * (ordinaryHypergeometricSeries ℂ a b c).coeff n := by
  have hreg := regularizedGaussHGFunSeries_coeff_recurrence a b c hc n
  have hg : Complex.Gamma c ≠ 0 := Complex.Gamma_ne_zero hc
  have hscale (k : ℕ) : (ordinaryHypergeometricSeries ℂ a b c).coeff k =
      Complex.Gamma c * (Complex.regularizedGaussHGFunSeries a b c).coeff k := by
    rw [← Complex.Gamma_inv_mul_ordinaryHypergeometricSeries_eq (a := a) (b := b) hc (n := k),
      ← mul_assoc, mul_inv_cancel₀ hg, one_mul]
  rw [hscale n, hscale (n + 1)]
  calc
    ((n : ℂ) + 1) * (c + n) * (Complex.Gamma c *
          (Complex.regularizedGaussHGFunSeries a b c).coeff (n + 1)) =
        Complex.Gamma c * (((n : ℂ) + 1) * (c + n) *
          (Complex.regularizedGaussHGFunSeries a b c).coeff (n + 1)) := by ring
    _ = Complex.Gamma c * ((a + n) * (b + n) *
          (Complex.regularizedGaussHGFunSeries a b c).coeff n) := by rw [hreg]
    _ = (a + n) * (b + n) * (Complex.Gamma c *
          (Complex.regularizedGaussHGFunSeries a b c).coeff n) := by ring

/-- Normalization at zero determines the analytic solution germ, for a regular denominator
  parameter. -/
theorem gauss_hypergeometric_unique (a b c : ℂ) (hc : ∀ n : ℕ, c ≠ -(n : ℂ))
    {y : ℂ → ℂ} (hy : AnalyticAt ℂ y 0) (hy0 : y 0 = 1)
    (hode : ∀ᶠ z in 𝓝 (0 : ℂ), gaussDifferentialExpression a b c y z = 0) :
    y =ᶠ[𝓝 (0 : ℂ)] ordinaryHypergeometric a b c := by
  obtain ⟨p, hp⟩ := hy
  obtain ⟨r, hp⟩ := hp
  have hd0 : p.coeff 0 = 1 := (hp.coeff_zero (1 : Fin 0 → ℂ)).trans hy0
  have hcoeff : ∀ n, p.coeff n = (ordinaryHypergeometricSeries ℂ a b c).coeff n := by
    intro n
    induction n with
    | zero => rw [hd0, ordinaryHypergeometricSeries_coeff_zero a b c hc]
    | succ n ih =>
      have hn : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
      have hcn : c + (n : ℂ) ≠ 0 := by simpa [eq_neg_iff_add_eq_zero] using hc n
      apply mul_left_cancel₀ (mul_ne_zero hn hcn)
      calc
        ((n : ℂ) + 1) * (c + n) * p.coeff (n + 1) = (a + n) * (b + n) * p.coeff n :=
          gauss_powerSeries_coeff_recurrence a b c hp hode n
        _ = (a + n) * (b + n) * (ordinaryHypergeometricSeries ℂ a b c).coeff n := by rw [ih]
        _ = ((n : ℂ) + 1) * (c + n) * (ordinaryHypergeometricSeries ℂ a b c).coeff (n + 1) :=
          (ordinaryHypergeometricSeries_coeff_recurrence a b c hc n).symm
  have hpeq : p = ordinaryHypergeometricSeries ℂ a b c := by
    ext n
    rw [← FormalMultilinearSeries.mkPiRing_coeff_eq p,
      ← FormalMultilinearSeries.mkPiRing_coeff_eq (ordinaryHypergeometricSeries ℂ a b c),
      hcoeff n]
  filter_upwards [Metric.eball_mem_nhds (0 : ℂ) hp.r_pos] with z hz
  have hyz : y z = p.sum z := by simpa using hp.sum hz
  rw [hyz, ordinaryHypergeometric, hpeq]

/-- The regular-singular criterion for `y'' + P y' + Q y = 0`, allowing removable singularities.
Punctured equalities avoid false continuity claims for totalized rational functions at their poles.
  -/
def IsRegularSingularAt (P Q : ℂ → ℂ) (a : ℂ) : Prop :=
  ∃ p q : ℂ → ℂ, AnalyticAt ℂ p a ∧ AnalyticAt ℂ q a ∧
    (∀ᶠ z in 𝓝[≠] a, p z = (z - a) * P z) ∧
    (∀ᶠ z in 𝓝[≠] a, q z = (z - a) ^ 2 * Q z)

/-- The regular-singular criterion at infinity, after the coordinate change `z = 1/w`. -/
def IsRegularSingularAtInfinity (P Q : ℂ → ℂ) : Prop :=
  IsRegularSingularAt (fun w ↦ 2 / w - P w⁻¹ / w ^ 2) (fun w ↦ Q w⁻¹ / w ^ 4) 0

/-- All three Gauss points are regular singular (possibly ordinary in degenerate cases). -/
theorem gauss_isRegularSingularAt (a b c : ℂ) :
    let P := fun z ↦ (c - (a + b + 1) * z) / (z * (1 - z))
    let Q := fun z ↦ -(a * b) / (z * (1 - z))
    IsRegularSingularAt P Q 0 ∧ IsRegularSingularAt P Q 1 ∧ IsRegularSingularAtInfinity P Q := by
  intro P Q
  have h0 : ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ), z ≠ 0 ∧ z ≠ 1 := by
    have hn : ∀ᶠ z : ℂ in 𝓝 (0 : ℂ), z ≠ 1 :=
      (isOpen_ne_fun continuous_id continuous_const).mem_nhds (by norm_num)
    have hself : ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ), z ≠ 0 := self_mem_nhdsWithin
    exact hself.and (hn.filter_mono nhdsWithin_le_nhds)
  have h1 : ∀ᶠ z : ℂ in 𝓝[≠] (1 : ℂ), z ≠ 0 ∧ z ≠ 1 := by
    have hn : ∀ᶠ z : ℂ in 𝓝 (1 : ℂ), z ≠ 0 :=
      (isOpen_ne_fun continuous_id continuous_const).mem_nhds (by norm_num)
    exact (hn.filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin
  have hminus : ∀ z : ℂ, z ≠ 1 → 1 - z ≠ 0 := by
    intro z hz
    exact sub_ne_zero.mpr (Ne.symm hz)
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨fun z ↦ (c - (a + b + 1) * z) / (1 - z),
      fun z ↦ -(a * b) * z / (1 - z), by fun_prop (disch := norm_num),
      by fun_prop (disch := norm_num), ?_, ?_⟩
    · filter_upwards [h0] with z hz
      dsimp only [P]
      field_simp [hz.1, hminus z hz.2]
      ring
    · filter_upwards [h0] with z hz
      dsimp only [Q]
      field_simp [hz.1, hminus z hz.2]
      ring
  · refine ⟨fun z ↦ ((a + b + 1) * z - c) / z,
      fun z ↦ (a * b) * (z - 1) / z, by fun_prop (disch := norm_num),
      by fun_prop (disch := norm_num), ?_, ?_⟩
    · filter_upwards [h1] with z hz
      dsimp only [P]
      field_simp [hz.1, hminus z hz.2]
      ring
    · filter_upwards [h1] with z hz
      dsimp only [Q]
      field_simp [hz.1, hminus z hz.2]
      ring
  · refine ⟨fun w ↦ 2 - (c * w - (a + b + 1)) / (w - 1),
      fun w ↦ -(a * b) / (w - 1), by fun_prop (disch := norm_num),
      by fun_prop (disch := norm_num), ?_, ?_⟩
    · filter_upwards [h0] with w hw
      dsimp only [P]
      field_simp [hw.1, hminus w hw.2, sub_ne_zero.mpr hw.2]
      ring
    · filter_upwards [h0] with w hw
      dsimp only [Q]
      field_simp [hw.1, hminus w hw.2, sub_ne_zero.mpr hw.2]
      ring

open Complex
open scoped Nat

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
