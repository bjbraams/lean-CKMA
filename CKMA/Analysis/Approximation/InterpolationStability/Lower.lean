/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.Approximation.InterpolationStability.Basic

import CKMA.Analysis.Approximation.InterpolationStability.Estimates
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Algebra.Order.Ring.Star

/-!
# Midpoint lower bound for Chebyshev Lebesgue constants

This file proves the matching lower bound `(2 / π) log (n + 1) - O(1)` for the Lebesgue
function of the Chebyshev extrema at the central angular midpoint, and deduces the
corresponding lower bound for the Lebesgue constant.

## Main results

* `CKMA.lebesgueFunction_chebyshev_midpoint_ge`: lower bound for the Chebyshev-extrema
  Lebesgue function at the central angular midpoint.
* `CKMA.chebyshev_lebesgueConstant_lower_bound`: lower bound `(2 / π) log (n + 1) - C` for the
  Chebyshev-extrema Lebesgue constant.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Polynomial Real Polynomial.Chebyshev Finset Lagrange
open scoped BigOperators

/-- Half-integer reciprocals dominate `log(2q + 3)`. -/
private lemma sum_half_ge_log (q : ℕ) :
    log (2 * (q : ℝ) + 3) ≤ ∑ k ∈ range (q + 1), (1 : ℝ) / ((k : ℝ) + 1 / 2) := by
  have hcoeff (k : ℕ) :
      (1 : ℝ) / ((k : ℝ) + 1 / 2) = 2 * (1 / (2 * (k : ℝ) + 1)) := by
    field_simp
  simp_rw [hcoeff]
  rw [← Finset.mul_sum]
  have h := sum_odd_reciprocal_ge_log q
  linarith

/-- The central half-integer `(n - 1) / 2 + 1 / 2` is at most `n / 2`. -/
private lemma midpoint_le_half {n : ℕ} (hn : 1 ≤ n) :
    (((n - 1) / 2 : ℕ) : ℝ) + 1 / 2 ≤ (n : ℝ) / 2 := by
  have hq : (((n - 1) / 2 : ℕ) : ℝ) ≤ ((n - 1 : ℕ) : ℝ) / 2 := Nat.cast_div_le
  have hsub : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub hn]
    simp
  linarith

/-- Every node index lies within distance `n` of the central half-integer. -/
private lemma abs_sub_midpoint_lt {n : ℕ} (hn : 1 ≤ n) (i : Fin (n + 1)) :
    |(i.val : ℝ) - (((n - 1) / 2 : ℕ) + (1 : ℝ) / 2)| < n := by
  have hνle := midpoint_le_half hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hi : (i.val : ℝ) ≤ n := by exact_mod_cast Nat.le_of_lt_succ i.isLt
  have hi0 : (0 : ℝ) ≤ i.val := Nat.cast_nonneg _
  have hq0 : (0 : ℝ) ≤ (((n - 1) / 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [abs_lt]
  constructor <;> linarith

/-- The central angular midpoint `((n - 1) / 2 + 1 / 2) π / n` lies in `(0, π / 2]`. -/
private lemma midpointAngle_mem_Ioc {n : ℕ} (hn : 1 ≤ n) :
    (((n - 1) / 2 : ℕ) + (1 : ℝ) / 2) * π / n ∈ Set.Ioc 0 (π / 2) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hνle := midpoint_le_half hn
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ hn0]
  nlinarith [hνle, pi_pos]

/-- At the central angular midpoint `θ`, `|sin (n θ)| = 1`. -/
private lemma abs_sin_mul_midpointAngle {n : ℕ} (hn : 1 ≤ n) :
    |sin ((n : ℝ) * ((((n - 1) / 2 : ℕ) + (1 : ℝ) / 2) * π / n))| = 1 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have harg : (n : ℝ) * ((((n - 1) / 2 : ℕ) + (1 : ℝ) / 2) * π / n) =
      (((n - 1) / 2 : ℕ) : ℝ) * π + π / 2 := by
    field_simp
  rw [harg, sin_add, sin_nat_mul_pi, cos_nat_mul_pi, sin_pi_div_two, cos_pi_div_two]
  simp only [mul_zero, zero_add, mul_one]
  exact abs_neg_one_pow _

/-- The central angular midpoint is not a Chebyshev node angle. -/
private lemma midpointAngle_ne_chebyshevNodeAngle {n : ℕ} (hn : 1 ≤ n) (i : Fin (n + 1)) :
    (((n - 1) / 2 : ℕ) + (1 : ℝ) / 2) * π / n ≠ chebyshevNodeAngle n i := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  intro hi
  rw [chebyshevNodeAngle, div_left_inj' hn0.ne', mul_comm π] at hi
  have hval := mul_right_cancel₀ pi_ne_zero hi
  have heven : (2 : ℝ) * i.val = 2 * (((n - 1) / 2 : ℕ) : ℝ) + 1 := by linarith
  have hnat : 2 * i.val = 2 * ((n - 1) / 2) + 1 := by exact_mod_cast heven
  omega

/-- Sum of unweighted midpoint reciprocals dominates `2 * log (n + 1)`. -/
private lemma midpoint_sum_inv_ge_log {n : ℕ} (hn : 1 ≤ n) :
    2 * log ((n : ℝ) + 1) ≤
      ∑ i : Fin (n + 1), (1 : ℝ) / |(i.val : ℝ) - (((n - 1) / 2 : ℕ) + (1 : ℝ) / 2)| := by
  let q : ℕ := (n - 1) / 2
  let ν : ℝ := (q : ℝ) + 1 / 2
  let d : Fin (n + 1) → ℝ := fun i => |(i.val : ℝ) - ν|
  have hdiv' : n - 1 = 2 * q + (n - 1) % 2 := by
    have h := Nat.div_add_mod (n - 1) 2
    omega
  have hqle : q + 1 ≤ n - q := by
    have h2q : 2 * q ≤ n - 1 := by omega
    omega
  have hlogCmp : log ((n : ℝ) + 1) ≤ log (2 * (q : ℝ) + 3) := by
    have hr : (n - 1) % 2 ≤ 1 := by
      have hlt := Nat.mod_lt (n - 1) (by decide : 0 < 2)
      omega
    have hcast : (n : ℝ) = 2 * (q : ℝ) + (Nat.cast ((n - 1) % 2) : ℝ) + 1 := by
      have h1 := congrArg (Nat.cast : ℕ → ℝ) hdiv'
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at h1
      rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one] at h1
      linarith
    have hrR : (Nat.cast ((n - 1) % 2) : ℝ) ≤ 1 := by
      simpa using (Nat.cast_le (α := ℝ)).mpr hr
    exact (log_le_log_iff (by positivity) (by positivity)).mpr (by linarith)
  have hdistL (j : ℕ) (hj : j ≤ q) :
      |(j : ℝ) - ν| = ((q - j : ℕ) : ℝ) + 1 / 2 := by
    have hjν : (j : ℝ) ≤ ν := by
      have : (j : ℝ) ≤ q := by exact_mod_cast hj
      unfold ν; linarith
    rw [abs_of_nonpos (sub_nonpos.mpr hjν), Nat.cast_sub hj]
    unfold ν; ring
  have hleft : ∑ j ∈ range (q + 1), (1 : ℝ) / |(j : ℝ) - ν| =
      ∑ j ∈ range (q + 1), (1 : ℝ) / ((j : ℝ) + 1 / 2) := by
    have hrew : ∑ j ∈ range (q + 1), (1 : ℝ) / |(j : ℝ) - ν| =
        ∑ j ∈ range (q + 1), (1 : ℝ) / (((q - j : ℕ) : ℝ) + 1 / 2) := by
      refine Finset.sum_congr rfl fun j hj => ?_
      exact congrArg (fun t => (1 : ℝ) / t)
        (hdistL j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)))
    rw [hrew, ← Finset.sum_range_reflect (fun j => (1 : ℝ) / ((j : ℝ) + 1 / 2)) (q + 1)]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hidx : q + 1 - 1 - j = q - j := by have := Finset.mem_range.mp hj; omega
    rw [hidx]
  have hright : ∑ k ∈ range (n - q), (1 : ℝ) / |((q + 1 + k : ℕ) : ℝ) - ν| =
      ∑ k ∈ range (n - q), (1 : ℝ) / ((k : ℝ) + 1 / 2) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    have hpos : ν ≤ ((q + 1 + k : ℕ) : ℝ) := by push_cast; unfold ν; linarith
    rw [abs_of_nonneg (sub_nonneg.mpr hpos)]
    unfold ν; push_cast; ring
  have hrange : ∑ i, (1 : ℝ) / d i =
      ∑ j ∈ range (n + 1), (1 : ℝ) / |(j : ℝ) - ν| := by
    simpa [d] using Fin.sum_univ_eq_sum_range (fun j => (1 : ℝ) / |(j : ℝ) - ν|) (n + 1)
  have hsplit := Finset.sum_range_add (fun j => (1 : ℝ) / |(j : ℝ) - ν|) (q + 1) (n - q)
  have hcount : q + 1 + (n - q) = n + 1 := by omega
  change 2 * log ((n : ℝ) + 1) ≤ ∑ i, (1 : ℝ) / d i
  rw [hrange]
  rw [hcount] at hsplit
  rw [hsplit, hleft, hright]
  have hsub : ∑ k ∈ range (q + 1), (1 : ℝ) / ((k : ℝ) + 1 / 2) ≤
      ∑ k ∈ range (n - q), (1 : ℝ) / ((k : ℝ) + 1 / 2) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hqle)
      fun _ _ _ => div_nonneg (by norm_num) (by positivity)
  have htwice : 2 * ∑ k ∈ range (q + 1), (1 : ℝ) / ((k : ℝ) + 1 / 2) ≤
      (∑ j ∈ range (q + 1), (1 : ℝ) / ((j : ℝ) + 1 / 2)) +
        ∑ k ∈ range (n - q), (1 : ℝ) / ((k : ℝ) + 1 / 2) := by
    have h := add_le_add_left hsub (∑ k ∈ range (q + 1), (1 : ℝ) / ((k : ℝ) + 1 / 2))
    simpa [two_mul, add_comm] using h
  exact (mul_le_mul_of_nonneg_left hlogCmp (by norm_num)).trans
    ((mul_le_mul_of_nonneg_left (sum_half_ge_log q) (by norm_num)).trans htwice)

/-- Endpoint weights reduce the midpoint reciprocal sum by at most `2`. -/
private lemma midpoint_sum_weighted_inv_ge {n : ℕ} (hn : 1 ≤ n) :
    ∑ i : Fin (n + 1),
        (1 : ℝ) / |(i.val : ℝ) - (((n - 1) / 2 : ℕ) + (1 : ℝ) / 2)| - 2 ≤
      ∑ i : Fin (n + 1),
        (1 : ℝ) / (chebyshevExtremalWeight n i *
          |(i.val : ℝ) - (((n - 1) / 2 : ℕ) + (1 : ℝ) / 2)|) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  let q : ℕ := (n - 1) / 2
  let ν : ℝ := (q : ℝ) + 1 / 2
  let d : Fin (n + 1) → ℝ := fun i => |(i.val : ℝ) - ν|
  let wt : Fin (n + 1) → ℝ := fun i => chebyshevExtremalWeight n i
  have hνpos : 0 < ν := by unfold ν; positivity
  have hνle : ν ≤ (n : ℝ) / 2 := midpoint_le_half hn
  have hdrop (i : Fin (n + 1)) : (1 : ℝ) / d i - 1 / (wt i * d i) ≤
      if i.val = 0 ∨ i.val = n then 1 else 0 := by
    by_cases hend : i.val = 0 ∨ i.val = n
    · have hwt2 : wt i = 2 := by
        unfold wt chebyshevExtremalWeight
        exact ite_eq_left hend
      have hdhalf : 1 / 2 ≤ d i := by
        unfold d
        rcases hend with h0 | hnI
        · rw [h0, Nat.cast_zero, abs_of_nonpos (sub_nonpos.mpr hνpos.le)]
          unfold ν
          have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
          linarith
        · rw [hnI]
          have hhalf : (n : ℝ) / 2 ≤ n :=
            div_le_self hn0.le (by norm_num : (1 : ℝ) ≤ 2)
          rw [abs_of_nonneg (sub_nonneg.mpr (hνle.trans hhalf)), le_sub_iff_add_le]
          have hνeq : ν = (q : ℝ) + 1 / 2 := rfl
          rw [hνeq, show (1 : ℝ) / 2 + ((q : ℝ) + 1 / 2) = (q : ℝ) + 1 by ring]
          exact_mod_cast (show q + 1 ≤ n by omega)
      rw [hwt2, ite_eq_left hend]
      have : (1 : ℝ) / d i - 1 / (2 * d i) = 1 / (2 * d i) := by field_simp; ring
      rw [this]
      have hden : 0 < 2 * d i := by linarith
      rw [div_le_one hden]
      linarith
    · have hwt1 : wt i = 1 := chebyshevExtremalWeight_of_interior
        (by simpa using (not_or.mp hend).1) (by simpa using (not_or.mp hend).2)
      rw [hwt1, ite_eq_right (by simpa using hend)]
      have : (1 : ℝ) / d i - 1 / (1 * d i) = 0 := by field_simp; ring
      linarith
  have hind : ∑ i : Fin (n + 1), (if i.val = 0 ∨ i.val = n then (1 : ℝ) else 0) = 2 := by
    let i0 : Fin (n + 1) := ⟨0, by omega⟩
    let iN : Fin (n + 1) := ⟨n, by omega⟩
    have hpair : univ.filter (fun i : Fin (n + 1) => i.val = 0 ∨ i.val = n) = {i0, iN} := by
      ext i
      simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton, i0, iN]
      constructor
      · rintro (h | h) <;> [left; right] <;> exact Fin.ext h
      · rintro (h | h) <;> simp [h]
    have hne : i0 ≠ iN := by intro h; have := congrArg Fin.val h; simp [i0, iN] at this; omega
    have hfilter := (Finset.sum_filter (s := univ)
      (fun i : Fin (n + 1) => i.val = 0 ∨ i.val = n) (fun _ => (1 : ℝ))).symm
    rw [hfilter, hpair, Finset.sum_insert (by simp [hne]), Finset.sum_singleton]
    norm_num
  have hsum := Finset.sum_le_sum (s := univ) (fun i _ => hdrop i)
  have hsub := Finset.sum_sub_distrib (s := univ) (fun i => (1 : ℝ) / d i)
    (fun i => (1 : ℝ) / (wt i * d i))
  change ∑ i, (1 : ℝ) / d i - 2 ≤ ∑ i, (1 : ℝ) / (wt i * d i)
  linarith

/-- Sum of the linear cotangent error terms at the midpoint is at most `π / 4`. -/
private lemma midpoint_sum_err_le {n : ℕ} (hn : 1 ≤ n) :
    ∑ i : Fin (n + 1),
        π * |(i.val : ℝ) - (((n - 1) / 2 : ℕ) + (1 : ℝ) / 2)| /
          (8 * (n : ℝ) ^ 2 * chebyshevExtremalWeight n i) ≤ π / 4 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  let q : ℕ := (n - 1) / 2
  let ν : ℝ := (q : ℝ) + 1 / 2
  let d : Fin (n + 1) → ℝ := fun i => |(i.val : ℝ) - ν|
  let wt : Fin (n + 1) → ℝ := fun i => chebyshevExtremalWeight n i
  have hterm (i : Fin (n + 1)) : π * d i / (8 * (n : ℝ) ^ 2 * wt i) ≤ π / (8 * n) := by
    have hdlt : d i < n := abs_sub_midpoint_lt hn i
    have hα : 1 ≤ wt i := one_le_chebyshevExtremalWeight n i
    calc π * d i / (8 * (n : ℝ) ^ 2 * wt i)
        ≤ π * n / (8 * (n : ℝ) ^ 2 * wt i) := by gcongr
      _ ≤ π * n / (8 * (n : ℝ) ^ 2 * 1) :=
          div_le_div_of_nonneg_left (by positivity : 0 ≤ π * (n : ℝ)) (by positivity)
            (by gcongr)
      _ = π / (8 * n) := by field_simp
  have hsum := Finset.sum_le_sum (s := univ) fun i _ => hterm i
  have hconst : ∑ i : Fin (n + 1), π / (8 * n) = (n + 1 : ℝ) * (π / (8 * n)) := by
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hsmall : (n + 1 : ℝ) * (π / (8 * n)) ≤ π / 4 := by
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hratio : (n + 1 : ℝ) / n ≤ 2 := by rw [div_le_iff₀ hn0]; linarith
    calc (n + 1 : ℝ) * (π / (8 * n)) = π / 8 * ((n + 1 : ℝ) / n) := by ring
      _ ≤ π / 8 * 2 := by gcongr
      _ = π / 4 := by ring
  change ∑ i, π * d i / (8 * (n : ℝ) ^ 2 * wt i) ≤ π / 4
  linarith

/-- Sum of the cotangent main terms at the central midpoint. -/
private lemma midpoint_sum_main_ge {n : ℕ} (hn : 1 ≤ n) :
    (2 / π) * log ((n : ℝ) + 1) - (2 / π + π / 4) ≤
      ∑ i, chebyshevLebesgueMain n ((((n - 1) / 2 : ℕ) + (1 : ℝ) / 2) * π / n) i := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  let q : ℕ := (n - 1) / 2
  let ν : ℝ := (q : ℝ) + 1 / 2
  let θ : ℝ := ν * π / n
  let d : Fin (n + 1) → ℝ := fun i => |(i.val : ℝ) - ν|
  let wt : Fin (n + 1) → ℝ := fun i => chebyshevExtremalWeight n i
  have hnode : ∀ i, θ ≠ chebyshevNodeAngle n i := midpointAngle_ne_chebyshevNodeAngle hn
  have hsin : |sin ((n : ℝ) * θ)| = 1 := abs_sin_mul_midpointAngle hn
  have hrecip := midpoint_sum_inv_ge_log hn
  have hdef := midpoint_sum_weighted_inv_ge hn
  have herr := midpoint_sum_err_le hn
  have hterm (i : Fin (n + 1)) : (1 : ℝ) / (wt i * π * d i) -
      π * d i / (8 * (n : ℝ) ^ 2 * wt i) ≤ chebyshevLebesgueMain n θ i := by
    have hdpos : 0 < d i := by
      unfold d
      rw [abs_pos]
      intro hz
      have hiν : (i.val : ℝ) = ν := sub_eq_zero.mp hz
      exact hnode i (by
        unfold chebyshevNodeAngle
        rw [hiν, show θ = π * ν / n by unfold θ; ring])
    have hαpos : 0 < wt i := chebyshevExtremalWeight_pos n i
    let u : ℝ := |θ - chebyshevNodeAngle n i| / 2
    have hu_eq : u = π * d i / (2 * n) := by
      have hθv : θ = π * ν / n := by unfold θ; ring
      have hsub : π * ν / n - π * (i.val : ℝ) / n = π * (ν - (i.val : ℝ)) / n := by
        field_simp
      unfold u d
      rw [hθv, chebyshevNodeAngle, hsub, abs_div, abs_mul, abs_of_pos pi_pos, abs_of_pos hn0,
        abs_sub_comm]
      ring
    have hu : u ∈ Set.Ioo 0 (π / 2) := by
      rw [hu_eq]
      refine ⟨by positivity, ?_⟩
      have hdlt : d i < n := abs_sub_midpoint_lt hn i
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hdlt, pi_pos]
    have hcot := one_div_sub_div_two_le_cot hu
    have hcoef : 0 ≤ 1 / (2 * (n : ℝ) * wt i) := by positivity
    have hineq := mul_le_mul_of_nonneg_left hcot hcoef
    have hmaineq : chebyshevLebesgueMain n θ i =
        1 / (2 * (n : ℝ) * wt i) * cot u := by
      unfold chebyshevLebesgueMain wt
      rw [hsin]
    have halg : 1 / (2 * (n : ℝ) * wt i) * (1 / u - u / 2) =
        1 / (wt i * π * d i) - π * d i / (8 * (n : ℝ) ^ 2 * wt i) := by
      rw [hu_eq]
      field_simp [hdpos.ne', hαpos.ne', hn0.ne', pi_ne_zero]
      ring
    linarith
  have hsum := Finset.sum_le_sum (s := univ) fun i _ => hterm i
  have hrew : ∑ i, ((1 : ℝ) / (wt i * π * d i) -
        π * d i / (8 * (n : ℝ) ^ 2 * wt i)) =
      (1 / π) * ∑ i, (1 : ℝ) / (wt i * d i) -
        ∑ i, π * d i / (8 * (n : ℝ) ^ 2 * wt i) := by
    rw [Finset.sum_sub_distrib]
    congr 1
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => by
        have hdne : d i ≠ 0 := by
          unfold d
          rw [ne_eq, abs_eq_zero]
          intro hz
          have hiν : (i.val : ℝ) = ν := sub_eq_zero.mp hz
          exact hnode i (by
            unfold chebyshevNodeAngle
            rw [hiν, show θ = π * ν / n by unfold θ; ring])
        have hαne := (chebyshevExtremalWeight_pos n i).ne'
        field_simp [hdne, hαne, pi_ne_zero]
  have hcoef : (1 / π) * (2 : ℝ) = 2 / π := by rw [div_mul_eq_mul_div, one_mul]
  have hbase : (2 : ℝ) * log ((n : ℝ) + 1) - 2 ≤ ∑ i, (1 : ℝ) / (wt i * d i) :=
    (sub_le_sub_right hrecip 2).trans hdef
  have hscale : (1 / π) * ((2 : ℝ) * log ((n : ℝ) + 1) - 2) ≤
      (1 / π) * ∑ i, (1 : ℝ) / (wt i * d i) :=
    mul_le_mul_of_nonneg_left hbase (div_nonneg (by norm_num) pi_pos.le)
  have hdropB : (1 / π) * ((2 : ℝ) * log ((n : ℝ) + 1) - 2) -
      ∑ i, π * d i / (8 * (n : ℝ) ^ 2 * wt i) ≤
      (1 / π) * ∑ i, (1 : ℝ) / (wt i * d i) -
        ∑ i, π * d i / (8 * (n : ℝ) ^ 2 * wt i) :=
    sub_le_sub_right hscale _
  have hfloor : (1 / π) * ((2 : ℝ) * log ((n : ℝ) + 1) - 2) - π / 4 ≤
      (1 / π) * ((2 : ℝ) * log ((n : ℝ) + 1) - 2) -
        ∑ i, π * d i / (8 * (n : ℝ) ^ 2 * wt i) :=
    sub_le_sub_left herr _
  have hident : (1 / π) * ((2 : ℝ) * log ((n : ℝ) + 1) - 2) - π / 4 =
      (2 / π) * log ((n : ℝ) + 1) - (2 / π + π / 4) := by
    rw [mul_sub, ← mul_assoc, hcoef, sub_sub]
  have hrewSum : (1 / π) * ∑ i, (1 : ℝ) / (wt i * d i) -
      ∑ i, π * d i / (8 * (n : ℝ) ^ 2 * wt i) ≤
      ∑ i, chebyshevLebesgueMain n θ i := by
    rw [← hrew]
    exact hsum
  change (2 / π) * log ((n : ℝ) + 1) - (2 / π + π / 4) ≤ ∑ i, chebyshevLebesgueMain n θ i
  rw [← hident]
  exact hfloor.trans (hdropB.trans hrewSum)

/-- At the central angular midpoint, the correction terms of the outer indices `i ≤ q` and
`n - q ≤ i`, where `q = (n - 1) / 2`, are nonnegative. -/
private lemma chebyshevLebesgueCorr_midpoint_nonneg {n : ℕ} (hn : 1 ≤ n) {i : Fin (n + 1)}
    (hi : i.val ≤ (n - 1) / 2 ∨ n - (n - 1) / 2 ≤ i.val) :
    0 ≤ chebyshevLebesgueCorr n ((((n - 1) / 2 : ℕ) + (1 : ℝ) / 2) * π / n) i := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  let q : ℕ := (n - 1) / 2
  let ν : ℝ := (q : ℝ) + 1 / 2
  let θ : ℝ := ν * π / n
  have hθmem : θ ∈ Set.Ioc 0 (π / 2) := midpointAngle_mem_Ioc hn
  have hpref : 0 ≤ |sin ((n : ℝ) * θ)| /
      (2 * (n : ℝ) * chebyshevExtremalWeight n i) :=
    div_nonneg (abs_nonneg _)
      (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hn0)
        (chebyshevExtremalWeight_pos n i)).le
  have key : 0 ≤ chebyshevLebesgueCorr n θ i := by
    rcases hi with hleftI | hrightI
    · have hφ : chebyshevNodeAngle n i < θ := by
        have hiν : (i.val : ℝ) < ν := by
          have : (i.val : ℝ) ≤ q := by exact_mod_cast hleftI
          unfold ν; linarith
        unfold chebyshevNodeAngle
        rw [show θ = π * ν / n by unfold θ; ring, div_lt_div_iff₀ hn0 hn0]
        have hmul := mul_lt_mul_of_pos_left hiν pi_pos
        nlinarith [hmul, hn0]
      have hsign := chebyshevAngleSign_of_lt hφ
      have havg : (θ + chebyshevNodeAngle n i) / 2 < π / 2 := by linarith [hθmem.2]
      have havg0 : 0 < (θ + chebyshevNodeAngle n i) / 2 := by
        linarith [hθmem.1, (chebyshevNodeAngle_mem_Icc (by omega) i).1]
      have hcot : 0 < cot ((θ + chebyshevNodeAngle n i) / 2) := by
        rw [cot_eq_cos_div_sin]
        exact div_pos
          (cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], havg⟩)
          (sin_pos_of_pos_of_lt_pi havg0 (havg.trans (by linarith [pi_pos])))
      unfold chebyshevLebesgueCorr
      rw [hsign, mul_one]
      exact mul_nonneg hpref hcot.le
    · have hφ : π - θ < chebyshevNodeAngle n i := by
        have hiν : (n : ℝ) - ν < (i.val : ℝ) := by
          have hi : ((n - q : ℕ) : ℝ) ≤ i.val := by exact_mod_cast hrightI
          have hcast : ((n - q : ℕ) : ℝ) = (n : ℝ) - q := Nat.cast_sub (by omega)
          have hν : (n : ℝ) - ν = (n : ℝ) - q - 1 / 2 := by unfold ν; ring
          linarith
        unfold chebyshevNodeAngle
        rw [lt_div_iff₀ hn0]
        have hright : (π - θ) * n = π * ((n : ℝ) - ν) := by unfold θ; field_simp
        rw [hright]
        exact mul_lt_mul_of_pos_left hiν pi_pos
      have hθle : θ ≤ π - θ := by linarith [hθmem.2]
      have hsign := chebyshevAngleSign_of_not_lt (not_lt_of_gt (hθle.trans_lt hφ))
      have havg : π / 2 < (θ + chebyshevNodeAngle n i) / 2 := by linarith
      have havgπ : (θ + chebyshevNodeAngle n i) / 2 < π := by
        have hφπ : chebyshevNodeAngle n i ≤ π := (chebyshevNodeAngle_mem_Icc (by omega) i).2
        linarith [hθmem.2]
      have hcot : cot ((θ + chebyshevNodeAngle n i) / 2) < 0 := by
        rw [cot_eq_cos_div_sin]
        have hsin' : 0 < sin ((θ + chebyshevNodeAngle n i) / 2) :=
          sin_pos_of_pos_of_lt_pi (by linarith) havgπ
        have hcos : cos ((θ + chebyshevNodeAngle n i) / 2) < 0 :=
          cos_neg_of_pi_div_two_lt_of_lt havg
            (havgπ.trans (lt_add_of_pos_right π (div_pos pi_pos (by norm_num))))
        exact div_neg_of_neg_of_pos hcos hsin'
      unfold chebyshevLebesgueCorr
      rw [hsign]
      have hnonnegCot : 0 ≤ -cot ((θ + chebyshevNodeAngle n i) / 2) :=
        neg_nonneg.mpr hcot.le
      have hrew : |sin ((n : ℝ) * θ)| / (2 * (n : ℝ) * chebyshevExtremalWeight n i) *
          -1 * cot ((θ + chebyshevNodeAngle n i) / 2) =
          |sin ((n : ℝ) * θ)| / (2 * (n : ℝ) * chebyshevExtremalWeight n i) *
            (-cot ((θ + chebyshevNodeAngle n i) / 2)) := by ring
      rw [hrew]
      exact mul_nonneg hpref hnonnegCot
  exact key

/-- `tan (π / (4 n)) ≤ 1` for `n ≥ 1`. -/
private lemma tan_pi_div_four_mul_le_one {n : ℕ} (hn : 1 ≤ n) : tan (π / (4 * n)) ≤ 1 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have h4pos : (0 : ℝ) < 4 := by norm_num
  have h2pos : (0 : ℝ) < 2 := by norm_num
  have hden : 0 < 4 * (n : ℝ) := mul_pos h4pos hn0
  have h1n : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h4n : (4 : ℝ) ≤ 4 * n := by
    simpa [mul_one] using mul_le_mul_of_nonneg_left h1n h4pos.le
  have h2lt : (2 : ℝ) < 4 * n := (by norm_num : (2 : ℝ) < 4).trans_le h4n
  have hxlt : π / (4 * n) < π / 2 := by
    rw [div_lt_div_iff₀ hden h2pos]
    exact mul_lt_mul_of_pos_left h2lt pi_pos
  have hx0 : 0 ≤ π / (4 * n) := div_nonneg pi_pos.le hden.le
  have hxneg : -(π / 2) < π / (4 * n) :=
    (neg_lt_zero.mpr (div_pos pi_pos h2pos)).trans_le hx0
  have hx : π / (4 * n) ∈ Set.Ioo (-(π / 2)) (π / 2) := ⟨hxneg, hxlt⟩
  have hπ4 : π / 4 < π / 2 := by
    rw [div_lt_div_iff₀ h4pos h2pos]
    exact mul_lt_mul_of_pos_left (by norm_num : (2 : ℝ) < 4) pi_pos
  have hy : π / 4 ∈ Set.Ioo (-(π / 2)) (π / 2) :=
    ⟨(neg_lt_zero.mpr (div_pos pi_pos h2pos)).trans_le (div_nonneg pi_pos.le h4pos.le), hπ4⟩
  have hle : π / (4 * n) ≤ π / 4 := by
    rw [div_le_div_iff₀ hden h4pos]
    exact mul_le_mul_of_nonneg_left h4n pi_pos.le
  simpa [tan_pi_div_four] using strictMonoOn_tan.monotoneOn hx hy hle

/-- For even `n`, the middle correction term at index `q + 1`, where `q = (n - 1) / 2`, is at
least `-1 / 2` at the central angular midpoint. -/
private lemma chebyshevLebesgueCorr_midpoint_middle_ge {n : ℕ} (hn : 1 ≤ n)
    (hr1 : (n - 1) % 2 = 1) :
    -(1 / 2) ≤ chebyshevLebesgueCorr n ((((n - 1) / 2 : ℕ) + (1 : ℝ) / 2) * π / n)
      ⟨(n - 1) / 2 + 1, by omega⟩ := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  let q : ℕ := (n - 1) / 2
  let ν : ℝ := (q : ℝ) + 1 / 2
  let θ : ℝ := ν * π / n
  let j : Fin (n + 1) := ⟨q + 1, by omega⟩
  have hsin : |sin ((n : ℝ) * θ)| = 1 := abs_sin_mul_midpointAngle hn
  have hnEven : n = 2 * (q + 1) := by omega
  have hφ : chebyshevNodeAngle n j = π / 2 := by
    unfold chebyshevNodeAngle
    have hcast : ((q + 1 : ℕ) : ℝ) = (n : ℝ) / 2 := by
      have hnR : (n : ℝ) = 2 * ((q + 1 : ℕ) : ℝ) := by exact_mod_cast hnEven
      rw [eq_div_iff (by norm_num : (2 : ℝ) ≠ 0)]
      linarith
    rw [hcast]; field_simp
  have hθeq : θ = π / 2 - π / (2 * n) := by
    unfold θ ν
    have hνeq : (q : ℝ) + 1 / 2 = (n : ℝ) / 2 - 1 / 2 := by
      have : (n : ℝ) = 2 * ((q : ℝ) + 1) := by exact_mod_cast hnEven
      linarith
    rw [hνeq]; field_simp
  have havg : (θ + chebyshevNodeAngle n j) / 2 = π / 2 - π / (4 * n) := by
    rw [hφ, hθeq]; ring
  have hcot : cot ((θ + chebyshevNodeAngle n j) / 2) = tan (π / (4 * n)) := by
    rw [havg, cot_eq_cos_div_sin, cos_pi_div_two_sub, sin_pi_div_two_sub,
      tan_eq_sin_div_cos]
  have hw : chebyshevExtremalWeight n j = 1 :=
    chebyshevExtremalWeight_of_interior (by simp [j]) (by simp [j]; omega)
  have hsign : chebyshevAngleSign n θ j = -1 :=
    chebyshevAngleSign_of_not_lt (by
      rw [hφ, hθeq]
      exact not_lt_of_gt (sub_lt_self (π / 2)
        (div_pos pi_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hn0))))
  have htan := tan_pi_div_four_mul_le_one hn
  have key : -(1 / 2) ≤ chebyshevLebesgueCorr n θ j := by
    unfold chebyshevLebesgueCorr
    rw [hw, hsign, hcot, hsin]
    have hstep : tan (π / (4 * n)) / (2 * (n : ℝ)) ≤ 1 / 2 := by
      have hden : 0 < 2 * (n : ℝ) := mul_pos (by norm_num : (0 : ℝ) < 2) hn0
      have hfrac : tan (π / (4 * n)) / (2 * (n : ℝ)) ≤ 1 / (2 * (n : ℝ)) :=
        div_le_div_of_nonneg_right htan hden.le
      have hsmall : (1 : ℝ) / (2 * n) ≤ 1 / 2 := by
        rw [div_le_div_iff₀ hden (by norm_num : (0 : ℝ) < 2), one_mul, one_mul]
        have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
        simpa [mul_one] using mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 2)
      exact hfrac.trans hsmall
    have hid : (1 : ℝ) / (2 * n * 1) * -1 * tan (π / (4 * n)) =
        -(tan (π / (4 * n)) / (2 * n)) := by
      rw [mul_one, mul_assoc, neg_one_mul, mul_neg, mul_comm, mul_one_div]
    rw [hid]
    exact neg_le_neg hstep
  exact key

/-- Sum of the cotangent correction terms at the central midpoint is at least `-1 / 2`. -/
private lemma midpoint_sum_corr_ge {n : ℕ} (hn : 1 ≤ n) :
    -(1 / 2) ≤
      ∑ i, chebyshevLebesgueCorr n ((((n - 1) / 2 : ℕ) + (1 : ℝ) / 2) * π / n) i := by
  classical
  let q : ℕ := (n - 1) / 2
  let θ : ℝ := ((q : ℝ) + 1 / 2) * π / n
  let p : Fin (n + 1) → Prop := fun i => i.val ≤ q ∨ n - q ≤ i.val
  have hadd := Finset.sum_filter_add_sum_filter_not univ p
    (fun i => chebyshevLebesgueCorr n θ i)
  have hgood : 0 ≤ ∑ i ∈ univ.filter p, chebyshevLebesgueCorr n θ i :=
    Finset.sum_nonneg fun i hi => chebyshevLebesgueCorr_midpoint_nonneg hn (mem_filter.mp hi).2
  have hbad : -(1 / 2) ≤ ∑ i ∈ univ.filter (fun i => ¬ p i), chebyshevLebesgueCorr n θ i := by
    by_cases hr0 : (n - 1) % 2 = 0
    · have hempty : univ.filter (fun i : Fin (n + 1) => ¬ p i) = ∅ := by
        ext i
        simp only [mem_filter, mem_univ, true_and, Finset.notMem_empty]
        constructor
        · intro h
          have hgap : n - q = q + 1 := by omega
          simp only [p, not_or, not_le] at h
          omega
        · intro h
          exact h.elim
      rw [hempty, Finset.sum_empty]
      exact neg_nonpos.mpr (by norm_num : (0 : ℝ) ≤ 1 / 2)
    · have hr1 : (n - 1) % 2 = 1 := by
        have hlt := Nat.mod_lt (n - 1) (by decide : 0 < 2)
        omega
      have honly : univ.filter (fun i : Fin (n + 1) => ¬ p i) = {⟨q + 1, by omega⟩} := by
        ext i
        simp only [mem_filter, mem_univ, true_and, mem_singleton]
        constructor
        · intro hnp
          have hlt : q < i.val := by
            have : ¬ i.val ≤ q := fun h => hnp (Or.inl h)
            omega
          have hgt : i.val < n - q := by
            have : ¬ n - q ≤ i.val := fun h => hnp (Or.inr h)
            omega
          have hgap : n - q = q + 2 := by omega
          exact Fin.ext (by omega : i.val = q + 1)
        · intro hi
          rw [hi]
          intro hp
          have hgap : n - q = q + 2 := by omega
          simp only [p] at hp
          omega
      rw [honly, Finset.sum_singleton]
      exact chebyshevLebesgueCorr_midpoint_middle_ge hn hr1
  have hsumc := add_le_add hgood hbad
  rw [hadd] at hsumc
  simpa [θ, q] using hsumc

/-- The central angular midpoint sees the full logarithmic growth. -/
lemma lebesgueFunction_chebyshev_midpoint_ge {n : ℕ} (hn : 1 ≤ n) :
    (2 / π) * log ((n : ℝ) + 1) - (2 / π + π / 4 + 1 / 2) ≤
      lebesgueFunction (chebyshevExtremalNodes n)
        (cos ((((n - 1) / 2 : ℕ) + (1 : ℝ) / 2) * π / n)) := by
  let q : ℕ := (n - 1) / 2
  let ν : ℝ := (q : ℝ) + 1 / 2
  let θ : ℝ := ν * π / n
  have hθmem : θ ∈ Set.Ioc 0 (π / 2) := midpointAngle_mem_Ioc hn
  have hnode : ∀ i, θ ≠ chebyshevNodeAngle n i := midpointAngle_ne_chebyshevNodeAngle hn
  have hopen : θ ∈ Set.Ioo 0 π := ⟨hθmem.1, hθmem.2.trans_lt (by linarith [pi_pos])⟩
  have hcosarg : ((((n - 1) / 2 : ℕ) + (1 : ℝ) / 2) * π / n) = θ := rfl
  rw [hcosarg, lebesgueFunction_cos_eq hn hopen hnode]
  have hmain := midpoint_sum_main_ge hn
  have hcorr := midpoint_sum_corr_ge hn
  have hsum := add_le_add hmain hcorr
  have hL : (2 / π) * log ((n : ℝ) + 1) - (2 / π + π / 4 + 1 / 2) =
      (2 / π) * log ((n : ℝ) + 1) - (2 / π + π / 4) + -(1 / 2) :=
    (sub_sub ((2 / π) * log ((n : ℝ) + 1)) (2 / π + π / 4) (1 / 2)).symm.trans
      (sub_eq_add_neg _ _)
  rw [hL]
  exact hsum

/-- Lower bound `(2 / π) log (n + 1) - C` for the Chebyshev-extrema Lebesgue constant. -/
theorem chebyshev_lebesgueConstant_lower_bound (n : ℕ) :
    (2 / Real.pi) * Real.log (n + 1) - chebyshevLebesgueSlack ≤
      interpolationLebesgueConstant (chebyshevExtremalNodes n) := by
  by_cases hn0 : n = 0
  · subst hn0
    rw [interpolationLebesgueConstant_chebyshev_zero, Nat.cast_zero, zero_add, Real.log_one,
      mul_zero, zero_sub]
    linarith [chebyshevLebesgueSlack_nonneg]
  · have hn : 1 ≤ n := by omega
    let L : ℝ := (2 / Real.pi) * Real.log ((n : ℝ) + 1)
    have hbdd : BddAbove
        (lebesgueFunction (chebyshevExtremalNodes n) '' Set.Icc (-1 : ℝ) 1) :=
      isCompact_Icc.bddAbove_image (continuous_lebesgueFunction _).continuousOn
    have hpt := lebesgueFunction_chebyshev_midpoint_ge hn
    let tθ : ℝ := Real.cos ((((n - 1) / 2 : ℕ) + (1 : ℝ) / 2) * Real.pi / n)
    have hval : lebesgueFunction (chebyshevExtremalNodes n) tθ ≤
        interpolationLebesgueConstant (chebyshevExtremalNodes n) := by
      rw [interpolationLebesgueConstant]
      exact le_csSup hbdd ⟨tθ, Real.cos_mem_Icc _, rfl⟩
    exact ((sub_le_sub_left chebyshevMidpointDeficit_le_slack L).trans hpt).trans hval

end CKMA
