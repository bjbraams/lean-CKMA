/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Bessel
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Algebra.InfiniteSum.Real
import TauCeti.Analysis.SpecialFunctions.Gamma.Stirling.Basic

/-!
# Bessel second solutions, Airy and Mittag–Leffler functions

The Bessel second-kind connection formula is continued in its order at integers;
its principal slit-plane solution has the standard differential equation and
Wronskian. Airy solutions are defined by their entire initial-value power series and
an oscillatory real integral. Positive-order Mittag–Leffler series are entire for
arbitrary complex second parameter and include the exponential at parameters `(1,1)`.

Sources: GAPS 49.26, 49.36 and 49.76. First-kind Bessel and Gamma functions reuse Mathlib.
The exponential specialization uses Mathlib's Gamma factorial values and exponential series.
Entireness of `E_{α,β}` uses `FormalMultilinearSeries.ofScalars_radius_eq_top_of_tendsto`,
`FormalMultilinearSeries.ofScalars_sum_eq`, and TauCeti's sectorial bound
`TauCeti.abs_log_norm_Gamma_sub_stirling_le`. The Airy series is compared with
`Real.summable_pow_div_factorial` and differentiated by
`hasDerivAt_tsum_of_isPreconnected`. The differentiated series satisfies Airy's equation
by the three-step coefficient recurrence.

## Main definitions

* `CKMA.besselYConnection`, `CKMA.besselY`: Weber's Bessel function of the second kind `Y_ν(z)`.
* `CKMA.hankelOne`, `CKMA.hankelTwo`: Hankel functions `H_ν^{(1)}` and `H_ν^{(2)}`.
* `CKMA.airySeriesCoefficient`, `CKMA.airySeries`: power-series solution of Airy's equation
  with prescribed initial data.
* `CKMA.airyAi`: the Airy function `Ai`.
* `CKMA.mittagLeffler`: the two-parameter Mittag–Leffler function `E_{α,β}(z)`.

## Main results

* `CKMA.besselY_of_noninteger`, `CKMA.tendsto_besselYConnection_int`: the connection formula at
  nonintegral orders and its limit at integer orders.
* `CKMA.besselY_ode`, `CKMA.besselJ_besselY_wronskian`: Bessel's differential equation and
  Wronskian for `J_ν` and `Y_ν` on the slit plane (**49.26**).
* `CKMA.airySeries_ode`, `CKMA.airySeries_initial_and_hasSum`: Airy's differential equation,
  initial values and convergence of the power series.
* `CKMA.airyAi_eq_oscillatory_integral`: oscillatory integral representation of `Ai` on the real
  line (**49.36**).
* `CKMA.mittagLeffler_hasSum_and_entire`, `CKMA.mittagLeffler_one_one`: convergence and
  entireness of `E_{α,β}` for `α > 0`, and `E_{1,1}(z) = exp z` (**49.76**).
-/

public section

noncomputable section

namespace CKMA

open Filter Topology
open scoped BigOperators

/-- The nonintegral-order connection formula for the Bessel function of the second kind. -/
@[expose]
def besselYConnection (ν z : ℂ) : ℂ :=
  (Complex.cos (Real.pi * ν) * Complex.besselJ ν z - Complex.besselJ (-ν) z) /
    Complex.sin (Real.pi * ν)

/-- The second Bessel solution, using the order-limit at integers.
`limUnder` is a totalized limit; the convergence theorem below certifies its intended value
on the slit plane. This definition has no admitted dependency. -/
@[expose]
def besselY (ν z : ℂ) : ℂ := by
  classical
  exact if ∃ n : ℤ, ν = (n : ℂ) then
    Filter.limUnder (𝓝[≠] ν) (fun μ ↦ besselYConnection μ z) else besselYConnection ν z

/-- The outgoing Hankel function. -/
@[expose]
def hankelOne (ν z : ℂ) : ℂ := Complex.besselJ ν z + Complex.I * besselY ν z

/-- The incoming Hankel function. -/
@[expose]
def hankelTwo (ν z : ℂ) : ℂ := Complex.besselJ ν z - Complex.I * besselY ν z

/-- **49.26**, nonintegral-order connection formula, directly from the definition. -/
theorem besselY_of_noninteger {ν z : ℂ} (hν : ¬ ∃ n : ℤ, ν = (n : ℂ)) :
    besselY ν z = besselYConnection ν z := by
  classical
  simp [besselY, hν]

/-- The order-limit exists at each integer, for arguments in the principal slit plane. -/
theorem tendsto_besselYConnection_int (n : ℤ) {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    Tendsto (fun ν ↦ besselYConnection ν z) (𝓝[≠] (n : ℂ)) (𝓝 (besselY n z)) := by
  sorry

/-- The second-kind solution satisfies Bessel's equation on its principal branch. -/
theorem besselY_ode (ν : ℂ) {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    z ^ 2 * deriv (deriv (besselY ν)) z + z * deriv (besselY ν) z +
      (z ^ 2 - ν ^ 2) * besselY ν z = 0 := by
  sorry

/-- The Wronskian normalization certifies independence of the first- and second-kind solutions. -/
theorem besselJ_besselY_wronskian (ν : ℂ) {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    Complex.besselJ ν z * deriv (besselY ν) z - deriv (Complex.besselJ ν) z * besselY ν z =
      2 / (Real.pi * z) := by
  sorry

/-- Coefficients for the Airy initial-value problem `y''=zy`, with `y(0)=a₀`, `y'(0)=a₁`. -/
@[expose]
def airySeriesCoefficient (a₀ a₁ : ℂ) (n : ℕ) : ℂ :=
  if n % 3 = 0 then a₀ /
    ∏ k ∈ Finset.range (n / 3), ((3 * k + 3 : ℕ) : ℂ) * ((3 * k + 2 : ℕ) : ℂ)
  else if n % 3 = 1 then a₁ /
    ∏ k ∈ Finset.range (n / 3), ((3 * k + 4 : ℕ) : ℂ) * ((3 * k + 3 : ℕ) : ℂ)
  else 0

/-- The canonical Airy power-series solution with specified initial data. -/
@[expose]
def airySeries (a₀ a₁ z : ℂ) : ℂ := ∑' n, airySeriesCoefficient a₀ a₁ n * z ^ n

/-- The decaying Airy function with the standard Gamma normalization at zero. -/
@[expose]
def airyAi (z : ℂ) : ℂ :=
  airySeries ((3 : ℂ) ^ (-(2 : ℂ) / 3) / Complex.Gamma (2 / 3))
    (-((3 : ℂ) ^ (-(1 : ℂ) / 3)) / Complex.Gamma (1 / 3)) z

private lemma airySeriesCoefficient_zero (a₀ a₁ : ℂ) :
    airySeriesCoefficient a₀ a₁ 0 = a₀ := by
  have hmod : 0 % 3 = 0 := by decide
  have hdiv : 0 / 3 = 0 := by decide
  simp [airySeriesCoefficient, hmod, hdiv, div_one]

private lemma airySeriesCoefficient_one (a₀ a₁ : ℂ) :
    airySeriesCoefficient a₀ a₁ 1 = a₁ := by
  have hmod : 1 % 3 = 1 := by decide
  have hdiv : 1 / 3 = 0 := by decide
  simp [airySeriesCoefficient, hmod, hdiv, div_one]

private lemma airySeriesCoefficient_norm_le (a₀ a₁ : ℂ) (n : ℕ) :
    ‖airySeriesCoefficient a₀ a₁ n‖ ≤ (‖a₀‖ + ‖a₁‖) / ((n / 3).factorial : ℝ) := by
  have htri : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by
    have := Nat.mod_lt n (by decide : 0 < 3)
    omega
  have hpair {k a b : ℕ} (ha : k + 1 ≤ a) (hb : 1 ≤ b) :
      (k + 1 : ℝ) ≤ ((a * b : ℕ) : ℝ) := by
    have hmul : (k + 1 : ℝ) * 1 ≤ (a : ℝ) * (b : ℝ) :=
      mul_le_mul (by exact_mod_cast ha) (by exact_mod_cast hb) zero_le_one
        (by exact_mod_cast (Nat.zero_le a))
    simpa [Nat.cast_mul] using hmul
  rcases htri with hmod | hmod | hmod
  · rw [airySeriesCoefficient, ite_eq_left hmod, norm_div, norm_prod]
    have hge : ((n / 3).factorial : ℝ) ≤
        ∏ k ∈ Finset.range (n / 3), (((3 * k + 3) * (3 * k + 2) : ℕ) : ℝ) := by
      rw [← Finset.prod_range_add_one_eq_factorial, Nat.cast_prod]
      refine Finset.prod_le_prod₀ (fun _ _ => by positivity) fun k _ => ?_
      simp only [Nat.cast_add, Nat.cast_one]
      have ha : k + 1 ≤ 3 * k + 3 := by omega
      have hb : 1 ≤ 3 * k + 2 := by omega
      exact hpair ha hb
    have hnorm : ∀ k ∈ Finset.range (n / 3),
        ‖((3 * k + 3 : ℕ) : ℂ) * ((3 * k + 2 : ℕ) : ℂ)‖ =
          (((3 * k + 3) * (3 * k + 2) : ℕ) : ℝ) := by
      intro k _
      rw [norm_mul, norm_natCast, norm_natCast, Nat.cast_mul]
    rw [Finset.prod_congr rfl hnorm]
    calc
      ‖a₀‖ / ∏ k ∈ Finset.range (n / 3), (((3 * k + 3) * (3 * k + 2) : ℕ) : ℝ) ≤
          ‖a₀‖ / ((n / 3).factorial : ℝ) :=
        div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) hge
      _ ≤ (‖a₀‖ + ‖a₁‖) / ((n / 3).factorial : ℝ) := by
        gcongr
        exact le_add_of_nonneg_right (norm_nonneg _)
  · rw [airySeriesCoefficient, ite_eq_right (by omega), ite_eq_left hmod, norm_div, norm_prod]
    have hge : ((n / 3).factorial : ℝ) ≤
        ∏ k ∈ Finset.range (n / 3), (((3 * k + 4) * (3 * k + 3) : ℕ) : ℝ) := by
      rw [← Finset.prod_range_add_one_eq_factorial, Nat.cast_prod]
      refine Finset.prod_le_prod₀ (fun _ _ => by positivity) fun k _ => ?_
      simp only [Nat.cast_add, Nat.cast_one]
      have ha : k + 1 ≤ 3 * k + 4 := by omega
      have hb : 1 ≤ 3 * k + 3 := by omega
      exact hpair ha hb
    have hnorm : ∀ k ∈ Finset.range (n / 3),
        ‖((3 * k + 4 : ℕ) : ℂ) * ((3 * k + 3 : ℕ) : ℂ)‖ =
          (((3 * k + 4) * (3 * k + 3) : ℕ) : ℝ) := by
      intro k _
      rw [norm_mul, norm_natCast, norm_natCast, Nat.cast_mul]
    rw [Finset.prod_congr rfl hnorm]
    calc
      ‖a₁‖ / ∏ k ∈ Finset.range (n / 3), (((3 * k + 4) * (3 * k + 3) : ℕ) : ℝ) ≤
          ‖a₁‖ / ((n / 3).factorial : ℝ) :=
        div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) hge
      _ ≤ (‖a₀‖ + ‖a₁‖) / ((n / 3).factorial : ℝ) := by
        gcongr
        exact le_add_of_nonneg_left (norm_nonneg _)
  · rw [airySeriesCoefficient]
    split_ifs with h0 h1
    · omega
    · omega
    · rw [norm_zero]
      positivity

private lemma summable_of_summable_modThree {f : ℕ → ℝ}
    (h0 : Summable fun m => f (3 * m)) (h1 : Summable fun m => f (3 * m + 1))
    (h2 : Summable fun m => f (3 * m + 2)) : Summable f := by
  classical
  let e0 : ℕ → ℕ := fun m => 3 * m
  let e1 : ℕ → ℕ := fun m => 3 * m + 1
  let e2 : ℕ → ℕ := fun m => 3 * m + 2
  have i0 : Function.Injective e0 := mul_right_injective₀ three_ne_zero
  have i1 : Function.Injective e1 := fun a b hab => by
    dsimp [e1] at hab
    exact mul_right_injective₀ three_ne_zero (Nat.add_right_cancel hab)
  have i2 : Function.Injective e2 := fun a b hab => by
    dsimp [e2] at hab
    exact mul_right_injective₀ three_ne_zero (Nat.add_right_cancel hab)
  have hsum := ((summable_extend_zero i0).mpr h0).add
    (((summable_extend_zero i1).mpr h1).add ((summable_extend_zero i2).mpr h2))
  refine Summable.congr hsum fun n => ?_
  generalize hq : n / 3 = q
  have htri : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by
    have := Nat.mod_lt n (by decide : 0 < 3)
    omega
  rcases htri with h | h | h
  · have hn : n = e0 q := by dsimp [e0]; omega
    have ho1 : e0 q ∉ Set.range e1 := by rintro ⟨m, hm⟩; dsimp [e0, e1] at hm; omega
    have ho2 : e0 q ∉ Set.range e2 := by rintro ⟨m, hm⟩; dsimp [e0, e2] at hm; omega
    rw [hn, i0.extend_apply, Function.extend_apply' _ _ _ ho1, Function.extend_apply' _ _ _ ho2]
    simp [e0]
  · have hn : n = e1 q := by dsimp [e1]; omega
    have ho0 : e1 q ∉ Set.range e0 := by rintro ⟨m, hm⟩; dsimp [e0, e1] at hm; omega
    have ho2 : e1 q ∉ Set.range e2 := by rintro ⟨m, hm⟩; dsimp [e1, e2] at hm; omega
    rw [hn, i1.extend_apply, Function.extend_apply' _ _ _ ho0, Function.extend_apply' _ _ _ ho2]
    simp [e1]
  · have hn : n = e2 q := by dsimp [e2]; omega
    have ho0 : e2 q ∉ Set.range e0 := by rintro ⟨m, hm⟩; dsimp [e0, e2] at hm; omega
    have ho1 : e2 q ∉ Set.range e1 := by rintro ⟨m, hm⟩; dsimp [e1, e2] at hm; omega
    rw [hn, i2.extend_apply, Function.extend_apply' _ _ _ ho0, Function.extend_apply' _ _ _ ho1]
    simp [e2]

private lemma summable_norm_airySeriesCoefficient_mul_pow (a₀ a₁ : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    Summable fun n => ‖airySeriesCoefficient a₀ a₁ n‖ * r ^ n := by
  refine summable_of_summable_modThree ?_ ?_ ?_
  · refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun m => ?_)
      ((Real.summable_pow_div_factorial (r ^ 3)).mul_left (‖a₀‖ + ‖a₁‖))
    have hdiv : (3 * m) / 3 = m := by omega
    have hle := airySeriesCoefficient_norm_le a₀ a₁ (3 * m)
    rw [hdiv] at hle
    calc
      ‖airySeriesCoefficient a₀ a₁ (3 * m)‖ * r ^ (3 * m) ≤
          ((‖a₀‖ + ‖a₁‖) / (m.factorial : ℝ)) * (r ^ 3) ^ m := by
        rw [pow_mul]
        exact mul_le_mul_of_nonneg_right hle (pow_nonneg (pow_nonneg hr 3) m)
      _ = (‖a₀‖ + ‖a₁‖) * ((r ^ 3) ^ m / m.factorial) := by
        rw [div_mul_eq_mul_div, ← mul_div_assoc]
  · refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun m => ?_)
      ((Real.summable_pow_div_factorial (r ^ 3)).mul_left ((‖a₀‖ + ‖a₁‖) * r))
    have hdiv : (3 * m + 1) / 3 = m := by omega
    have hle := airySeriesCoefficient_norm_le a₀ a₁ (3 * m + 1)
    rw [hdiv] at hle
    calc
      ‖airySeriesCoefficient a₀ a₁ (3 * m + 1)‖ * r ^ (3 * m + 1) ≤
          ((‖a₀‖ + ‖a₁‖) / (m.factorial : ℝ)) * (r * (r ^ 3) ^ m) := by
        rw [pow_succ', pow_mul]
        exact mul_le_mul_of_nonneg_right hle (mul_nonneg hr (pow_nonneg (pow_nonneg hr 3) m))
      _ = (‖a₀‖ + ‖a₁‖) * r * ((r ^ 3) ^ m / m.factorial) := by
        rw [div_mul_eq_mul_div, ← mul_assoc, ← mul_div_assoc]
  · refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun m => ?_) summable_zero
    have hmod : (3 * m + 2) % 3 = 2 := by omega
    simp [airySeriesCoefficient, hmod]

private lemma summable_airySeries_term (a₀ a₁ z : ℂ) :
    Summable fun n => airySeriesCoefficient a₀ a₁ n * z ^ n := by
  refine Summable.of_norm_bounded
      (summable_norm_airySeriesCoefficient_mul_pow a₀ a₁ (norm_nonneg z)) fun n => ?_
  rw [norm_mul, norm_pow]

/-- `n ^ k q ^ n` is bounded for `0 ≤ q < 1`, since it tends to zero. -/
private lemma exists_bound_nat_pow_mul_const_pow (k : ℕ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    ∃ M : ℝ, ∀ n : ℕ, (n : ℝ) ^ k * q ^ n ≤ M := by
  have htend := tendsto_pow_const_mul_const_pow_of_lt_one k hq0 hq1
  rw [Metric.tendsto_atTop] at htend
  obtain ⟨N, hN⟩ := htend 1 zero_lt_one
  classical
  have hnonneg : ∀ i : ℕ, 0 ≤ (i : ℝ) ^ k * q ^ i :=
    fun i => mul_nonneg (pow_nonneg (Nat.cast_nonneg i) k) (pow_nonneg hq0 i)
  refine ⟨(Finset.range N).sum (fun n => (n : ℝ) ^ k * q ^ n) + 1, fun n => ?_⟩
  by_cases hn : n < N
  · exact le_trans (Finset.single_le_sum (fun i _ => hnonneg i) (Finset.mem_range.mpr hn))
      (le_add_of_nonneg_right zero_le_one)
  · have hlt : (n : ℝ) ^ k * q ^ n < 1 := by
      have hdist := hN n (not_lt.mp hn)
      rwa [Real.dist_eq, sub_zero, abs_of_nonneg (hnonneg n)] at hdist
    have hsum : 0 ≤ (Finset.range N).sum (fun i => (i : ℝ) ^ k * q ^ i) :=
      Finset.sum_nonneg fun i _ => hnonneg i
    linarith

/-- Polynomial growth does not destroy summability of the Airy coefficient majorant. -/
private lemma summable_norm_airySeriesCoefficient_mul_nat_pow_mul_pow
    (a₀ a₁ : ℂ) (k : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    Summable fun n => ‖airySeriesCoefficient a₀ a₁ n‖ * (n : ℝ) ^ k * R ^ n := by
  have hden : 0 < R + 1 := by linarith
  set q : ℝ := R / (R + 1)
  have hq0 : 0 ≤ q := div_nonneg hR hden.le
  have hq1 : q < 1 := by
    rw [div_lt_one hden]
    linarith
  obtain ⟨M, hM⟩ := exists_bound_nat_pow_mul_const_pow k hq0 hq1
  have hsplit : ∀ n, R ^ n = q ^ n * (R + 1) ^ n := by
    intro n
    have hR' : R = q * (R + 1) := by
      dsimp [q]
      exact (div_mul_cancel₀ R hden.ne').symm
    conv_lhs => rw [hR']
    rw [mul_pow]
  refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun n => ?_)
    ((summable_norm_airySeriesCoefficient_mul_pow a₀ a₁ hden.le).mul_left M)
  have hstep : ‖airySeriesCoefficient a₀ a₁ n‖ * ((n : ℝ) ^ k * q ^ n) * (R + 1) ^ n ≤
      ‖airySeriesCoefficient a₀ a₁ n‖ * M * (R + 1) ^ n := by
    refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hden.le n)
    exact mul_le_mul_of_nonneg_left (hM n) (norm_nonneg _)
  calc
    ‖airySeriesCoefficient a₀ a₁ n‖ * (n : ℝ) ^ k * R ^ n
        = ‖airySeriesCoefficient a₀ a₁ n‖ * ((n : ℝ) ^ k * q ^ n) * (R + 1) ^ n := by
          rw [hsplit n]
          ring
    _ ≤ ‖airySeriesCoefficient a₀ a₁ n‖ * M * (R + 1) ^ n := hstep
    _ = M * (‖airySeriesCoefficient a₀ a₁ n‖ * (R + 1) ^ n) := by ring

/-- The three-step recurrence `c_{n+3}(n+3)(n+2) = c_n` built into the Airy coefficients. -/
private lemma airySeriesCoefficient_recurrence (a₀ a₁ : ℂ) (n : ℕ) :
    airySeriesCoefficient a₀ a₁ (n + 3) * ((n + 3 : ℕ) : ℂ) * ((n + 2 : ℕ) : ℂ) =
      airySeriesCoefficient a₀ a₁ n := by
  have hmod : (n + 3) % 3 = n % 3 := by omega
  have hdiv : (n + 3) / 3 = n / 3 + 1 := by omega
  have htri : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by
    have := Nat.mod_lt n (by decide : 0 < 3)
    omega
  rcases htri with h0 | h1 | h2
  · have hlast : 3 * (n / 3) + 3 = n + 3 := by omega
    have hprev : 3 * (n / 3) + 2 = n + 2 := by omega
    rw [airySeriesCoefficient, hmod, ite_eq_left h0, airySeriesCoefficient, ite_eq_left h0, hdiv,
      Finset.prod_range_succ]
    set P : ℂ := ∏ k ∈ Finset.range (n / 3), ((3 * k + 3 : ℕ) : ℂ) * ((3 * k + 2 : ℕ) : ℂ)
    set L : ℂ := ((3 * (n / 3) + 3 : ℕ) : ℂ) * ((3 * (n / 3) + 2 : ℕ) : ℂ)
    have hL : L = ((n + 3 : ℕ) : ℂ) * ((n + 2 : ℕ) : ℂ) := by
      simp [L, hlast, hprev]
    have hL0 : L ≠ 0 := by
      rw [hL]
      exact mul_ne_zero (Nat.cast_ne_zero.mpr (by omega)) (Nat.cast_ne_zero.mpr (by omega))
    calc
      a₀ / (P * L) * ((n + 3 : ℕ) : ℂ) * ((n + 2 : ℕ) : ℂ)
          = a₀ * (((n + 3 : ℕ) : ℂ) * ((n + 2 : ℕ) : ℂ)) / (P * L) := by
            rw [mul_assoc, div_mul_eq_mul_div]
      _ = a₀ * L / (P * L) := by rw [← hL]
      _ = a₀ / P := mul_div_mul_right a₀ P hL0
  · have hlast : 3 * (n / 3) + 4 = n + 3 := by omega
    have hprev : 3 * (n / 3) + 3 = n + 2 := by omega
    rw [airySeriesCoefficient, hmod, ite_eq_right (by omega), ite_eq_left h1,
      airySeriesCoefficient, ite_eq_right (by omega), ite_eq_left h1, hdiv, Finset.prod_range_succ]
    set P : ℂ := ∏ k ∈ Finset.range (n / 3), ((3 * k + 4 : ℕ) : ℂ) * ((3 * k + 3 : ℕ) : ℂ)
    set L : ℂ := ((3 * (n / 3) + 4 : ℕ) : ℂ) * ((3 * (n / 3) + 3 : ℕ) : ℂ)
    have hL : L = ((n + 3 : ℕ) : ℂ) * ((n + 2 : ℕ) : ℂ) := by
      simp [L, hlast, hprev]
    have hL0 : L ≠ 0 := by
      rw [hL]
      exact mul_ne_zero (Nat.cast_ne_zero.mpr (by omega)) (Nat.cast_ne_zero.mpr (by omega))
    calc
      a₁ / (P * L) * ((n + 3 : ℕ) : ℂ) * ((n + 2 : ℕ) : ℂ)
          = a₁ * (((n + 3 : ℕ) : ℂ) * ((n + 2 : ℕ) : ℂ)) / (P * L) := by
            rw [mul_assoc, div_mul_eq_mul_div]
      _ = a₁ * L / (P * L) := by rw [← hL]
      _ = a₁ / P := mul_div_mul_right a₁ P hL0
  · simp [airySeriesCoefficient, h2, hmod]

/-- The normalized power series solves Airy's equation everywhere. -/
theorem airySeries_ode (a₀ a₁ z : ℂ) :
    deriv (deriv (airySeries a₀ a₁)) z = z * airySeries a₀ a₁ z := by
  set c : ℕ → ℂ := airySeriesCoefficient a₀ a₁
  have hterm (n : ℕ) (w : ℂ) : HasDerivAt (fun y => c n * y ^ n)
      (c n * (n : ℂ) * w ^ (n - 1)) w := by
    simpa [c, mul_assoc] using (hasDerivAt_pow n w).const_mul (c n)
  have hterm' (n : ℕ) (w : ℂ) : HasDerivAt (fun y => c n * (n : ℂ) * y ^ (n - 1))
      (c n * (n : ℂ) * ((n - 1 : ℕ) : ℂ) * w ^ (n - 2)) w := by
    have hsub : (n - 1) - 1 = n - 2 := by omega
    simpa [c, mul_assoc, hsub] using
      ((hasDerivAt_pow (n - 1) w).const_mul (c n * (n : ℂ)))
  have hbound (w₀ : ℂ) (n : ℕ) {y : ℂ} (hy : y ∈ Metric.ball w₀ 1) :
      ‖c n * (n : ℂ) * y ^ (n - 1)‖ ≤
        ‖c n‖ * (n : ℝ) ^ 2 * (‖w₀‖ + 1) ^ n := by
    set ρ : ℝ := ‖w₀‖ + 1
    have hρ : 1 ≤ ρ := by dsimp [ρ]; linarith [norm_nonneg w₀]
    have hyρ : ‖y‖ ≤ ρ := by
      have hdist : dist y w₀ < 1 := by simpa [Metric.mem_ball] using hy
      calc
        ‖y‖ = ‖(y - w₀) + w₀‖ := by rw [sub_add_cancel]
        _ ≤ ‖y - w₀‖ + ‖w₀‖ := norm_add_le _ _
        _ = dist y w₀ + ‖w₀‖ := by rw [dist_eq_norm]
        _ ≤ ρ := by dsimp [ρ]; linarith
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_natCast]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hpow : ‖y‖ ^ (n - 1) ≤ ρ ^ n :=
        (pow_le_pow_left₀ (norm_nonneg _) hyρ _).trans
          (pow_le_pow_right₀ hρ (Nat.sub_le n 1))
      have hn2 : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
        rw [pow_two]
        exact le_mul_of_one_le_right (Nat.cast_nonneg _) (by exact_mod_cast hn)
      calc
        ‖c n‖ * (n : ℝ) * ‖y‖ ^ (n - 1) ≤ ‖c n‖ * (n : ℝ) * ρ ^ n :=
          mul_le_mul_of_nonneg_left hpow (mul_nonneg (norm_nonneg _) (Nat.cast_nonneg _))
        _ ≤ ‖c n‖ * (n : ℝ) ^ 2 * ρ ^ n :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hn2 (norm_nonneg (c n)))
            (pow_nonneg (zero_le_one.trans hρ) n)
  have hbound' (w₀ : ℂ) (n : ℕ) {y : ℂ} (hy : y ∈ Metric.ball w₀ 1) :
      ‖c n * (n : ℂ) * ((n - 1 : ℕ) : ℂ) * y ^ (n - 2)‖ ≤
        ‖c n‖ * (n : ℝ) ^ 2 * (‖w₀‖ + 1) ^ n := by
    set ρ : ℝ := ‖w₀‖ + 1
    have hρ : 1 ≤ ρ := by dsimp [ρ]; linarith [norm_nonneg w₀]
    have hyρ : ‖y‖ ≤ ρ := by
      have hdist : dist y w₀ < 1 := by simpa [Metric.mem_ball] using hy
      calc
        ‖y‖ = ‖(y - w₀) + w₀‖ := by rw [sub_add_cancel]
        _ ≤ ‖y - w₀‖ + ‖w₀‖ := norm_add_le _ _
        _ = dist y w₀ + ‖w₀‖ := by rw [dist_eq_norm]
        _ ≤ ρ := by dsimp [ρ]; linarith
    rw [norm_mul, norm_mul, norm_mul, norm_pow, Complex.norm_natCast, Complex.norm_natCast]
    rcases lt_or_ge n 2 with _ | hn
    · interval_cases n
      · simp
      · simp
        positivity
    · have hle : ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.sub_le n 1
      have hn2 : (n : ℝ) * ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 := by
        rw [pow_two]
        exact mul_le_mul_of_nonneg_left hle (Nat.cast_nonneg _)
      have hpow : ‖y‖ ^ (n - 2) ≤ ρ ^ n :=
        (pow_le_pow_left₀ (norm_nonneg _) hyρ _).trans
          (pow_le_pow_right₀ hρ (Nat.sub_le n 2))
      calc
        ‖c n‖ * (n : ℝ) * ((n - 1 : ℕ) : ℝ) * ‖y‖ ^ (n - 2)
            ≤ ‖c n‖ * (n : ℝ) * ((n - 1 : ℕ) : ℝ) * ρ ^ n :=
          mul_le_mul_of_nonneg_left hpow
            (mul_nonneg (mul_nonneg (norm_nonneg _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _))
        _ ≤ ‖c n‖ * (n : ℝ) ^ 2 * ρ ^ n := by
          rw [mul_assoc ‖c n‖]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hn2 (norm_nonneg (c n)))
            (pow_nonneg (zero_le_one.trans hρ) n)
  have hsum (w₀ : ℂ) : Summable fun n => ‖c n‖ * (n : ℝ) ^ 2 * (‖w₀‖ + 1) ^ n :=
    summable_norm_airySeriesCoefficient_mul_nat_pow_mul_pow a₀ a₁ 2 (by positivity)
  have hder (w₀ : ℂ) : HasDerivAt (airySeries a₀ a₁)
      (∑' n, c n * (n : ℂ) * w₀ ^ (n - 1)) w₀ := by
    refine hasDerivAt_tsum_of_isPreconnected (hsum w₀)
      (Metric.isOpen_ball (x := w₀) (ε := 1))
      (Metric.isPreconnected_ball (x := w₀) (r := 1))
      (fun n y _ => hterm n y) (fun n y hy => by simpa [c] using hbound w₀ n hy)
      (y₀ := w₀) ?_ (summable_airySeries_term a₀ a₁ w₀) (y := w₀) ?_
    · simp [Metric.mem_ball, dist_self]
    · simp [Metric.mem_ball, dist_self]
  have hder' (w₀ : ℂ) : HasDerivAt (deriv (airySeries a₀ a₁))
      (∑' n, c n * (n : ℂ) * ((n - 1 : ℕ) : ℂ) * w₀ ^ (n - 2)) w₀ := by
    have hfun : deriv (airySeries a₀ a₁) =
        fun w => ∑' n, c n * (n : ℂ) * w ^ (n - 1) := by
      ext w
      exact (hder w).deriv
    rw [hfun]
    have hsum0 : Summable fun n => c n * (n : ℂ) * w₀ ^ (n - 1) := by
      refine Summable.of_norm_bounded (hsum w₀) fun n => ?_
      simpa [c] using hbound w₀ n (by simp [Metric.mem_ball, dist_self])
    refine hasDerivAt_tsum_of_isPreconnected (hsum w₀)
      (Metric.isOpen_ball (x := w₀) (ε := 1))
      (Metric.isPreconnected_ball (x := w₀) (r := 1))
      (fun n y _ => hterm' n y) (fun n y hy => by simpa [c] using hbound' w₀ n hy)
      (y₀ := w₀) ?_ hsum0 (y := w₀) ?_
    · simp [Metric.mem_ball, dist_self]
    · simp [Metric.mem_ball, dist_self]
  rw [(hder' z).deriv]
  set d : ℕ → ℂ := fun n => c n * (n : ℂ) * ((n - 1 : ℕ) : ℂ) * z ^ (n - 2)
  have hd_sum : Summable d := by
    refine Summable.of_norm_bounded (hsum z) fun n => ?_
    simpa [c, d] using hbound' z n (by simp [Metric.mem_ball, dist_self])
  have hshift : ∑' n, d n = ∑' k, d (k + 2) := by
    rw [hd_sum.tsum_eq_zero_add]
    have hd0 : d 0 = 0 := by simp [d]
    rw [hd0, zero_add]
    have hs1 : Summable fun k => d (k + 1) := (summable_nat_add_iff 1).2 hd_sum
    rw [hs1.tsum_eq_zero_add]
    have hd1 : d 1 = 0 := by simp [d]
    rw [hd1, zero_add]
  have hd2 : ∀ k, d (k + 2) =
      c (k + 2) * ((k + 2 : ℕ) : ℂ) * ((k + 1 : ℕ) : ℂ) * z ^ k := by
    intro k
    have hnat : k + 2 - 1 = k + 1 := by omega
    have hpow : k + 2 - 2 = k := by omega
    simp [d, hnat, hpow, mul_assoc]
  have he : ∀ j, d ((j + 1) + 2) = c j * z ^ (j + 1) := by
    intro j
    rw [hd2 (j + 1)]
    have hidx : j + 1 + 2 = j + 3 := by omega
    have hidx' : j + 1 + 1 = j + 2 := by omega
    rw [hidx, hidx', airySeriesCoefficient_recurrence a₀ a₁ j]
  have htail : ∑' k, d (k + 2) = ∑' j, c j * z ^ (j + 1) := by
    have hs2 : Summable fun k => d (k + 2) := (summable_nat_add_iff 2).2 hd_sum
    rw [hs2.tsum_eq_zero_add]
    have hd2_zero : d (0 + 2) = 0 := by
      rw [hd2 0]
      have hmod : 2 % 3 = 2 := by decide
      simp [c, airySeriesCoefficient, hmod]
    rw [hd2_zero, zero_add]
    refine tsum_congr fun j => ?_
    simpa [add_assoc] using he j
  rw [hshift, htail]
  have hmul : ∑' j, c j * z ^ (j + 1) = z * ∑' j, c j * z ^ j := by
    have hterm_eq : ∀ j, c j * z ^ (j + 1) = z * (c j * z ^ j) := by
      intro j
      calc
        c j * z ^ (j + 1) = c j * (z ^ j * z) := by rw [pow_succ]
        _ = z * (c j * z ^ j) := by ring
    rw [tsum_congr hterm_eq]
    exact (summable_airySeries_term a₀ a₁ z).tsum_mul_left z
  rw [hmul, airySeries]

/-- The Airy initial conditions and convergence of the defining power series. -/
theorem airySeries_initial_and_hasSum (a₀ a₁ : ℂ) :
    airySeries a₀ a₁ 0 = a₀ ∧ deriv (airySeries a₀ a₁) 0 = a₁ ∧
      ∀ z, HasSum (fun n ↦ airySeriesCoefficient a₀ a₁ n * z ^ n) (airySeries a₀ a₁ z) := by
  have hterm (n : ℕ) (z : ℂ) : HasDerivAt (fun w => airySeriesCoefficient a₀ a₁ n * w ^ n)
      (airySeriesCoefficient a₀ a₁ n * (n : ℂ) * z ^ (n - 1)) z := by
    simpa [mul_assoc] using
      (hasDerivAt_pow n z).const_mul (airySeriesCoefficient a₀ a₁ n)
  have hu : Summable fun n => ‖airySeriesCoefficient a₀ a₁ n‖ * (n : ℝ) := by
    refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun n => ?_)
      (summable_norm_airySeriesCoefficient_mul_pow a₀ a₁ (by positivity : (0 : ℝ) ≤ 2))
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    exact_mod_cast (Nat.lt_pow_self (by decide : (1 : ℕ) < 2)).le
  have hder : HasDerivAt (airySeries a₀ a₁)
      (∑' n, airySeriesCoefficient a₀ a₁ n * (n : ℂ) * (0 : ℂ) ^ (n - 1)) 0 := by
    refine hasDerivAt_tsum_of_isPreconnected
      (g := fun n w => airySeriesCoefficient a₀ a₁ n * w ^ n)
      (g' := fun n w => airySeriesCoefficient a₀ a₁ n * (n : ℂ) * w ^ (n - 1))
      hu (Metric.isOpen_ball (x := (0 : ℂ)) (ε := 1))
      (Metric.isPreconnected_ball (x := (0 : ℂ)) (r := 1))
      (fun n y _ => hterm n y) ?_ (y₀ := 0) ?_ ?_ (y := 0) ?_
    · intro n y hy
      rw [norm_mul, norm_mul, norm_pow, Complex.norm_natCast]
      have hy1 : ‖y‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hy
      exact le_of_le_of_eq (mul_le_mul_of_nonneg_left
        (pow_le_one₀ (norm_nonneg _) hy1.le)
        (mul_nonneg (norm_nonneg _) (Nat.cast_nonneg _))) (by ring)
    · simp [Metric.mem_ball, dist_self]
    · exact summable_airySeries_term a₀ a₁ 0
    · simp [Metric.mem_ball, dist_self]
  have hzero :
      ∑' n, airySeriesCoefficient a₀ a₁ n * (n : ℂ) * (0 : ℂ) ^ (n - 1) = a₁ := by
    have hvanish : ∀ n, n ≠ 1 →
        airySeriesCoefficient a₀ a₁ n * (n : ℂ) * (0 : ℂ) ^ (n - 1) = 0 := by
      intro n hn
      by_cases hn0 : n = 0
      · simp [hn0]
      · simp [zero_pow (by omega : n - 1 ≠ 0)]
    rw [tsum_eq_single 1 hvanish]
    simp [airySeriesCoefficient_one, pow_zero, mul_one]
  refine ⟨?_, ?_, fun z => (summable_airySeries_term a₀ a₁ z).hasSum⟩
  · rw [airySeries, tsum_eq_single 0 (fun n hn => by simp [zero_pow hn]),
      airySeriesCoefficient_zero, pow_zero, mul_one]
  · rw [hder.deriv, hzero]

/-- **49.36**: the oscillatory real-axis integral for the Airy function, interpreted by truncation.
  -/
theorem airyAi_eq_oscillatory_integral (x : ℝ) :
    Tendsto (fun T : ℝ ↦ Real.pi⁻¹ * ∫ t in (0 : ℝ)..T, Real.cos (t ^ 3 / 3 + x * t))
      atTop (𝓝 ((airyAi x).re)) := by
  sorry

/-- The two-parameter Mittag–Leffler series, with positive real first parameter in its theorems.
Reciprocals of Gamma at its poles use Mathlib's totalized value zero, as required by `1/Γ`. -/
@[expose]
def mittagLeffler (α : ℝ) (β z : ℂ) : ℂ :=
  ∑' n : ℕ, z ^ n / Complex.Gamma ((α : ℂ) * n + β)

private lemma log_norm_Gamma_div_le {α : ℝ} (hα : 0 < α) {s : ℂ} (hs : 1 ≤ s.re) :
    Real.log (‖Complex.Gamma s‖ / ‖Complex.Gamma (s + α)‖) ≤
      -α * Real.log ‖s + (α : ℂ)‖ + |s.im| * Real.pi + α + 4 := by
  let Φ : ℂ → ℝ := fun w =>
    (w.re - 1 / 2) * Real.log ‖w‖ - w.im * w.arg - w.re + Real.log (2 * Real.pi) / 2
  let t : ℂ := s + α
  have ht : 1 ≤ t.re := by
    dsimp [t]
    linarith
  have hnorm_le : ‖s‖ ≤ ‖t‖ := by
    have hsq : ‖s‖ ^ 2 ≤ ‖t‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
      simp only [t, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im]
      nlinarith [sq_nonneg α]
    exact le_of_sq_le_sq hsq (norm_nonneg _)
  have herr (w : ℂ) (hw : 1 ≤ w.re) : |Real.log ‖Complex.Gamma w‖ - Φ w| ≤ 2 / ‖w‖ := by
    have hw0 : w ≠ 0 := by
      intro hz
      simp [hz] at hw
      linarith
    have harg : |w.arg| ≤ Real.pi / 2 :=
      (Complex.abs_arg_le_pi_div_two_iff).2 (by linarith : 0 ≤ w.re)
    have hsector : |w.arg| ≤ Real.pi - Real.pi / 2 := by
      rwa [show Real.pi - Real.pi / 2 = Real.pi / 2 by ring]
    have hbound := TauCeti.abs_log_norm_Gamma_sub_stirling_le (s := w) (δ := Real.pi / 2)
      (div_pos Real.pi_pos zero_lt_two) (half_lt_self Real.pi_pos) hsector hw0
    simpa [Φ, Real.cos_pi_div_two, sub_zero, one_pow, mul_one] using hbound
  have hGs : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
  have hGt : Complex.Gamma t ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
  have hs1 : 1 ≤ ‖s‖ := (le_trans hs (Complex.re_le_norm s))
  have ht1 : 1 ≤ ‖t‖ := (le_trans ht (Complex.re_le_norm t))
  have hlog := herr s hs
  have hlogt := herr t ht
  rw [abs_le] at hlog hlogt
  have hΦ : Φ s - Φ t =
      (s.re - 1 / 2) * (Real.log ‖s‖ - Real.log ‖t‖) - α * Real.log ‖t‖ +
        s.im * (t.arg - s.arg) + α := by
    simp only [Φ, t, Complex.add_re, Complex.ofReal_re, Complex.add_im, Complex.ofReal_im]
    ring
  have hΔ : Φ s - Φ t ≤ -α * Real.log ‖t‖ + |s.im| * Real.pi + α := by
    rw [hΦ]
    have hlogle : Real.log ‖s‖ - Real.log ‖t‖ ≤ 0 := by
      rw [sub_nonpos]
      exact Real.log_le_log (by positivity) hnorm_le
    have hmul : (s.re - 1 / 2) * (Real.log ‖s‖ - Real.log ‖t‖) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) hlogle
    have harg : s.im * (t.arg - s.arg) ≤ |s.im| * Real.pi := by
      have hsarg : |s.arg| ≤ Real.pi / 2 :=
        (Complex.abs_arg_le_pi_div_two_iff).2 (by linarith : 0 ≤ s.re)
      have htarg : |t.arg| ≤ Real.pi / 2 :=
        (Complex.abs_arg_le_pi_div_two_iff).2 (by linarith : 0 ≤ t.re)
      have hdiff : |t.arg - s.arg| ≤ Real.pi := by
        calc
          |t.arg - s.arg| ≤ |t.arg - 0| + |0 - s.arg| := abs_sub_le _ _ _
          _ = |t.arg| + |s.arg| := by simp [sub_zero, zero_sub, abs_neg]
          _ ≤ Real.pi / 2 + Real.pi / 2 := by gcongr
          _ = Real.pi := by ring
      calc
        s.im * (t.arg - s.arg) ≤ |s.im * (t.arg - s.arg)| := le_abs_self _
        _ = |s.im| * |t.arg - s.arg| := abs_mul _ _
        _ ≤ |s.im| * Real.pi := by gcongr
    linarith
  have herrs : 2 / ‖s‖ ≤ 2 := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  have herrt : 2 / ‖t‖ ≤ 2 := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  calc
    Real.log (‖Complex.Gamma s‖ / ‖Complex.Gamma t‖) =
        Real.log ‖Complex.Gamma s‖ - Real.log ‖Complex.Gamma t‖ :=
      Real.log_div (norm_ne_zero_iff.mpr hGs) (norm_ne_zero_iff.mpr hGt)
    _ ≤ Φ s + 2 / ‖s‖ - (Φ t - 2 / ‖t‖) := by linarith
    _ = Φ s - Φ t + 2 / ‖s‖ + 2 / ‖t‖ := by ring
    _ ≤ -α * Real.log ‖t‖ + |s.im| * Real.pi + α + 4 := by linarith

private lemma tendsto_norm_Gamma_div_Gamma_add {α : ℝ} (hα : 0 < α) (β : ℂ) :
    Tendsto (fun n : ℕ => ‖Complex.Gamma ((α : ℂ) * n + β)‖ /
        ‖Complex.Gamma ((α : ℂ) * n + β + α)‖) atTop (𝓝 0) := by
  have hre : Tendsto (fun n : ℕ => ((α : ℂ) * n + β).re) atTop atTop := by
    have hmul : Tendsto (fun n : ℕ => α * (n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.const_mul_atTop hα
    have hadd : Tendsto (fun n : ℕ => α * (n : ℝ) + β.re) atTop atTop :=
      Filter.tendsto_atTop_add_const_right atTop β.re hmul
    refine hadd.congr fun n => ?_
    simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.natCast_re, Complex.natCast_im]
  set C : ℝ := Real.exp (|β.im| * Real.pi + α + 4)
  have hC : 0 < C := Real.exp_pos _
  have hupper : Tendsto (fun n : ℕ =>
      C / (((α : ℂ) * n + β + α).re) ^ α) atTop (𝓝 0) := by
    have ht : Tendsto (fun n : ℕ => ((α : ℂ) * n + β + α).re) atTop atTop := by
      refine Filter.tendsto_atTop_add_const_right atTop α ?_
      simpa [Complex.add_re, Complex.ofReal_re] using hre
    have hpow : Tendsto (fun n : ℕ => (((α : ℂ) * n + β + α).re) ^ α) atTop atTop :=
      (tendsto_rpow_atTop hα).comp ht
    simpa [div_eq_mul_inv] using hpow.inv_tendsto_atTop.const_mul C
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
    (Filter.Eventually.of_forall fun _ => div_nonneg (norm_nonneg _) (norm_nonneg _)) ?_
  filter_upwards [hre.eventually_ge_atTop 1] with n hn
  set s : ℂ := (α : ℂ) * n + β
  have hsre : 1 ≤ s.re := hn
  have hlog := log_norm_Gamma_div_le hα hsre
  have him : s.im = β.im := by
    simp [s, Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.natCast_im,
      Complex.ofReal_re]
  have hpos : 0 < ‖Complex.Gamma s‖ / ‖Complex.Gamma (s + α)‖ := by
    apply div_pos
    · exact norm_pos_iff.mpr (Complex.Gamma_ne_zero_of_re_pos (by linarith))
    · exact norm_pos_iff.mpr
        (Complex.Gamma_ne_zero_of_re_pos (by
          rw [Complex.add_re, Complex.ofReal_re]; linarith))
  have htpos : 0 < ‖s + (α : ℂ)‖ :=
    norm_pos_iff.mpr <| by
      intro hzero
      have : (s + (α : ℂ)).re = 0 := by simp [hzero]
      rw [Complex.add_re, Complex.ofReal_re] at this
      linarith
  rw [him] at hlog
  have hle_exp : ‖Complex.Gamma s‖ / ‖Complex.Gamma (s + α)‖ ≤
      C / ‖s + (α : ℂ)‖ ^ α := by
    rw [← Real.log_le_log_iff hpos (div_pos hC (Real.rpow_pos_of_pos htpos α))]
    rw [Real.log_div hC.ne' (Real.rpow_pos_of_pos htpos α).ne', Real.log_exp,
      Real.log_rpow htpos]
    linarith
  have hre_le : s.re + α ≤ ‖s + (α : ℂ)‖ := by
    simpa [Complex.add_re, Complex.ofReal_re] using Complex.re_le_norm (s + (α : ℂ))
  have hrpow : (s.re + α) ^ α ≤ ‖s + (α : ℂ)‖ ^ α :=
    Real.rpow_le_rpow (by linarith) hre_le hα.le
  have hden : 0 < (s.re + α) ^ α := Real.rpow_pos_of_pos (by linarith) _
  calc
    ‖Complex.Gamma s‖ / ‖Complex.Gamma (s + α)‖ ≤ C / ‖s + (α : ℂ)‖ ^ α := hle_exp
    _ ≤ C / (s.re + α) ^ α := div_le_div_of_nonneg_left hC.le hden hrpow
    _ = C / (((α : ℂ) * n + β + α).re) ^ α := by
      congr 1

/-- **49.76**, convergence and entireness clause for arbitrary complex second parameter. -/
theorem mittagLeffler_hasSum_and_entire {α : ℝ} (hα : 0 < α) (β : ℂ) :
    (∀ z, HasSum (fun n : ℕ ↦ z ^ n / Complex.Gamma ((α : ℂ) * n + β))
      (mittagLeffler α β z)) ∧ Differentiable ℂ (mittagLeffler α β) := by
  let c : ℕ → ℂ := fun n => (Complex.Gamma ((α : ℂ) * n + β))⁻¹
  let p : FormalMultilinearSeries ℂ ℂ ℂ := FormalMultilinearSeries.ofScalars ℂ c
  have hre : Tendsto (fun n : ℕ => ((α : ℂ) * n + β).re) atTop atTop := by
    have hmul : Tendsto (fun n : ℕ => α * (n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.const_mul_atTop hα
    refine (Filter.tendsto_atTop_add_const_right atTop β.re hmul).congr fun n => ?_
    simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.natCast_re, Complex.natCast_im]
  have hne : ∀ᶠ n in atTop, c n ≠ 0 := by
    filter_upwards [hre.eventually_gt_atTop 0] with n hn
    exact by simp [c, inv_eq_zero, Complex.Gamma_ne_zero_of_re_pos hn]
  have hratio : Tendsto (fun n => ‖c n.succ‖ / ‖c n‖) atTop (𝓝 0) := by
    refine (tendsto_norm_Gamma_div_Gamma_add hα β).congr fun n => ?_
    simp only [c, Nat.succ_eq_add_one, norm_inv]
    have harg : (α : ℂ) * ((n + 1 : ℕ) : ℂ) + β = (α : ℂ) * n + β + α := by
      simp [Nat.cast_add, mul_add, add_left_comm, add_comm]
    rw [harg, inv_div_inv]
  have hrad : p.radius = ⊤ :=
    FormalMultilinearSeries.ofScalars_radius_eq_top_of_tendsto ℂ c hne hratio
  have hpos : 0 < p.radius := by simp [hrad]
  have hball : Metric.eball (0 : ℂ) p.radius = Set.univ := by
    ext z
    simp [hrad]
  have hfun : mittagLeffler α β = p.sum := by
    ext z
    rw [mittagLeffler]
    simp only [p]
    rw [← FormalMultilinearSeries.ofScalarsSum,
      FormalMultilinearSeries.ofScalars_sum_eq c z]
    simp [c, div_eq_mul_inv, smul_eq_mul, mul_comm]
  refine ⟨fun z => ?_, ?_⟩
  · have hz : z ∈ Metric.eball (0 : ℂ) p.radius := by simp [hball]
    have hs := p.hasSum hz
    simpa [hfun, p, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, div_eq_mul_inv,
      mul_comm, c] using hs
  · rw [← differentiableOn_univ, hfun, ← hball]
    exact (p.hasFPowerSeriesOnBall hpos).differentiableOn

/-- The exponential is the Mittag–Leffler function with parameters `(1,1)`. -/
theorem mittagLeffler_one_one (z : ℂ) : mittagLeffler 1 1 z = Complex.exp z := by
  simp only [mittagLeffler, Complex.ofReal_one, one_mul, Complex.Gamma_nat_eq_factorial]
  rw [Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum_div]

end CKMA
