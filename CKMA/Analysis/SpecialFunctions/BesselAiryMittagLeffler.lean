/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Bessel
import TauCeti.Analysis.Analytic.OfScalars
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
`TauCeti.abs_log_norm_Gamma_sub_stirling_le`. The Airy series is the sum of a scalar power series
of infinite radius, differentiated termwise by TauCeti's `HasFPowerSeriesOnBall.deriv_ofScalars`;
the differentiated series satisfies Airy's equation by the three-step coefficient recurrence.

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
* `CKMA.hasFPowerSeriesOnBall_airySeries`, `CKMA.hasSum_airySeries`: the Airy power series has
  infinite radius.
* `CKMA.airySeries_ode`, `CKMA.airySeries_zero`, `CKMA.deriv_airySeries_zero`: Airy's differential
  equation and the initial values.
* `CKMA.airyAi_eq_oscillatory_integral`: oscillatory integral representation of `Ai` on the real
  line (**49.36**).
* `CKMA.hasSum_mittagLeffler`, `CKMA.differentiable_mittagLeffler`, `CKMA.mittagLeffler_one_one`:
  convergence and entireness of `E_{α,β}` for `α > 0`, and `E_{1,1}(z) = exp z` (**49.76**).
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
`limUnder` is a totalized limit; `tendsto_besselYConnection_int` states that it is the limit of
the connection formula at every `z ≠ 0`. -/
@[expose]
def besselY (ν z : ℂ) : ℂ := by
  classical
  exact if ∃ n : ℤ, ν = (n : ℂ) then
    Filter.limUnder (𝓝[≠] ν) (fun μ ↦ besselYConnection μ z) else besselYConnection ν z

/-- At an integer order, `besselY` is the totalized order-limit of the connection formula. -/
theorem besselY_intCast (n : ℤ) (z : ℂ) :
    besselY n z = Filter.limUnder (𝓝[≠] (n : ℂ)) (fun μ ↦ besselYConnection μ z) := by
  classical
  simp [besselY]

/-- The outgoing Hankel function. -/
@[expose]
def hankelOne (ν z : ℂ) : ℂ := Complex.besselJ ν z + Complex.I * besselY ν z

/-- The incoming Hankel function. -/
@[expose]
def hankelTwo (ν z : ℂ) : ℂ := Complex.besselJ ν z - Complex.I * besselY ν z

/-- Unfolding lemma for `besselYConnection`. -/
theorem besselYConnection_def (ν z : ℂ) :
    besselYConnection ν z =
      (Complex.cos (Real.pi * ν) * Complex.besselJ ν z - Complex.besselJ (-ν) z) /
        Complex.sin (Real.pi * ν) :=
  rfl

/-- Unfolding lemma for `hankelOne`: `H_ν^{(1)} = J_ν + i Y_ν`. -/
theorem hankelOne_def (ν z : ℂ) : hankelOne ν z = Complex.besselJ ν z + Complex.I * besselY ν z :=
  rfl

/-- Unfolding lemma for `hankelTwo`: `H_ν^{(2)} = J_ν - i Y_ν`. -/
theorem hankelTwo_def (ν z : ℂ) : hankelTwo ν z = Complex.besselJ ν z - Complex.I * besselY ν z :=
  rfl

/-- **49.26**, nonintegral-order connection formula, directly from the definition. -/
theorem besselY_of_noninteger {ν z : ℂ} (hν : ¬ ∃ n : ℤ, ν = (n : ℂ)) :
    besselY ν z = besselYConnection ν z := by
  classical
  simp [besselY, hν]

/-- The order-limit of the connection formula exists at each integer, for every `z ≠ 0`. The
principal power `z ^ ν = exp (ν log z)` is entire in `ν`, so no branch cut enters. -/
theorem tendsto_besselYConnection_int (n : ℤ) {z : ℂ} (hz : z ≠ 0) :
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

/-- Unfolding lemma for `airySeriesCoefficient`. -/
theorem airySeriesCoefficient_def (a₀ a₁ : ℂ) (n : ℕ) :
    airySeriesCoefficient a₀ a₁ n =
      if n % 3 = 0 then a₀ /
        ∏ k ∈ Finset.range (n / 3), ((3 * k + 3 : ℕ) : ℂ) * ((3 * k + 2 : ℕ) : ℂ)
      else if n % 3 = 1 then a₁ /
        ∏ k ∈ Finset.range (n / 3), ((3 * k + 4 : ℕ) : ℂ) * ((3 * k + 3 : ℕ) : ℂ)
      else 0 :=
  rfl

/-- Unfolding lemma for `airySeries`. -/
theorem airySeries_def (a₀ a₁ z : ℂ) :
    airySeries a₀ a₁ z = ∑' n, airySeriesCoefficient a₀ a₁ n * z ^ n :=
  rfl

/-- Unfolding lemma for `airyAi`: the Airy series with initial data
`Ai(0) = 3^{-2/3} / Γ(2/3)` and `Ai'(0) = -3^{-1/3} / Γ(1/3)`. -/
theorem airyAi_def (z : ℂ) :
    airyAi z = airySeries ((3 : ℂ) ^ (-(2 : ℂ) / 3) / Complex.Gamma (2 / 3))
      (-((3 : ℂ) ^ (-(1 : ℂ) / 3)) / Complex.Gamma (1 / 3)) z :=
  rfl

/-- The constant Airy coefficient is the initial value `a₀`. -/
@[simp]
theorem airySeriesCoefficient_zero (a₀ a₁ : ℂ) :
    airySeriesCoefficient a₀ a₁ 0 = a₀ := by
  have hmod : 0 % 3 = 0 := by decide
  have hdiv : 0 / 3 = 0 := by decide
  simp [airySeriesCoefficient, hmod, hdiv, div_one]

/-- The linear Airy coefficient is the initial slope `a₁`. -/
@[simp]
theorem airySeriesCoefficient_one (a₀ a₁ : ℂ) :
    airySeriesCoefficient a₀ a₁ 1 = a₁ := by
  have hmod : 1 % 3 = 1 := by decide
  have hdiv : 1 / 3 = 0 := by decide
  simp [airySeriesCoefficient, hmod, hdiv, div_one]

/-- The Airy coefficients are bounded by `(‖a₀‖ + ‖a₁‖) / ⌊n/3⌋!`. -/
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

/-- A sequence is summable if its restrictions to the three residue classes modulo `3` are. -/
theorem summable_of_summable_three_mul_add {α : Type*} [AddCommMonoid α] [TopologicalSpace α]
    [ContinuousAdd α] {f : ℕ → α}
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

/-- The Airy coefficients are dominated by `(‖a₀‖ + ‖a₁‖) / ⌊n/3⌋!`, so their power series
converges absolutely for every radius. -/
private lemma summable_norm_airySeriesCoefficient_mul_pow (a₀ a₁ : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    Summable fun n => ‖airySeriesCoefficient a₀ a₁ n‖ * r ^ n := by
  refine summable_of_summable_three_mul_add ?_ ?_ ?_
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

/-- The Airy power series converges at every point. -/
private lemma summable_airySeries_term (a₀ a₁ z : ℂ) :
    Summable fun n => airySeriesCoefficient a₀ a₁ n * z ^ n := by
  refine Summable.of_norm_bounded
      (summable_norm_airySeriesCoefficient_mul_pow a₀ a₁ (norm_nonneg z)) fun n => ?_
  rw [norm_mul, norm_pow]

/-- The three-step recurrence `c_{n+3}(n+3)(n+2) = c_n` built into the Airy coefficients. -/
theorem airySeriesCoefficient_recurrence (a₀ a₁ : ℂ) (n : ℕ) :
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

/-- The Airy series is the sum of the scalar power series with the Airy coefficients. -/
theorem airySeries_eq_ofScalarsSum (a₀ a₁ : ℂ) :
    airySeries a₀ a₁ =
      FormalMultilinearSeries.ofScalarsSum (E := ℂ) (airySeriesCoefficient a₀ a₁) := by
  ext z
  rw [FormalMultilinearSeries.ofScalars_sum_eq]
  simp [airySeries, smul_eq_mul]

/-- The Airy power series has infinite radius of convergence. -/
theorem radius_ofScalars_airySeriesCoefficient (a₀ a₁ : ℂ) :
    (FormalMultilinearSeries.ofScalars ℂ (airySeriesCoefficient a₀ a₁)).radius = ⊤ :=
  FormalMultilinearSeries.radius_eq_top_of_summable_norm _ fun r ↦ by
    simpa only [FormalMultilinearSeries.ofScalars_norm] using
      summable_norm_airySeriesCoefficient_mul_pow a₀ a₁ r.coe_nonneg

/-- The Airy series is the sum of its power series on the whole plane. -/
theorem hasFPowerSeriesOnBall_airySeries (a₀ a₁ : ℂ) :
    HasFPowerSeriesOnBall (airySeries a₀ a₁)
      (FormalMultilinearSeries.ofScalars ℂ (airySeriesCoefficient a₀ a₁)) 0 ⊤ := by
  rw [airySeries_eq_ofScalarsSum, ← radius_ofScalars_airySeriesCoefficient a₀ a₁]
  exact (FormalMultilinearSeries.ofScalars ℂ (airySeriesCoefficient a₀ a₁)).hasFPowerSeriesOnBall
    (by rw [radius_ofScalars_airySeriesCoefficient]; exact ENNReal.zero_lt_top)

/-- The Airy power series converges to the Airy series at every point. -/
theorem hasSum_airySeries (a₀ a₁ z : ℂ) :
    HasSum (fun n ↦ airySeriesCoefficient a₀ a₁ n * z ^ n) (airySeries a₀ a₁ z) :=
  (summable_airySeries_term a₀ a₁ z).hasSum

/-- The Airy series takes the initial value `a₀` at the origin. -/
@[simp]
theorem airySeries_zero (a₀ a₁ : ℂ) : airySeries a₀ a₁ 0 = a₀ := by
  rw [airySeries_eq_ofScalarsSum, FormalMultilinearSeries.ofScalarsSum_zero,
    airySeriesCoefficient_zero, smul_eq_mul, mul_one]

/-- The Airy series has derivative `a₁` at the origin. -/
@[simp]
theorem deriv_airySeries_zero (a₀ a₁ : ℂ) : deriv (airySeries a₀ a₁) 0 = a₁ := by
  rw [(hasFPowerSeriesOnBall_airySeries a₀ a₁).hasFPowerSeriesAt.deriv,
    FormalMultilinearSeries.ofScalars_apply_eq, airySeriesCoefficient_one, one_pow,
    smul_eq_mul, mul_one]

/-- The normalized power series solves Airy's equation `y'' = z y` everywhere. -/
theorem airySeries_ode (a₀ a₁ z : ℂ) :
    deriv (deriv (airySeries a₀ a₁)) z = z * airySeries a₀ a₁ z := by
  set c := airySeriesCoefficient a₀ a₁
  have h := hasFPowerSeriesOnBall_airySeries a₀ a₁
  have hz : z ∈ Metric.eball (0 : ℂ) ⊤ := by simp
  have h2 : HasSum (fun n : ℕ ↦ ((n : ℂ) + 1) * (((n + 1 : ℕ) : ℂ) + 1) * c (n + 2) * z ^ n)
      (deriv (deriv (airySeries a₀ a₁)) z) := by
    simpa [FormalMultilinearSeries.ofScalars_apply_eq, mul_comm, mul_left_comm, mul_assoc]
      using h.deriv_ofScalars.deriv_ofScalars.hasSum hz
  have h0 : c 2 = 0 := by simp [c, airySeriesCoefficient]
  have hshift := (hasSum_nat_add_iff' 1).mpr h2
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, h0, mul_zero, zero_mul,
    sub_zero] at hshift
  refine hshift.unique ?_
  convert (hasSum_airySeries a₀ a₁ z).mul_left z using 1
  ext k
  rw [← airySeriesCoefficient_recurrence a₀ a₁ k]
  push_cast
  ring

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

/-- Unfolding lemma for `mittagLeffler`. -/
theorem mittagLeffler_def (α : ℝ) (β z : ℂ) :
    mittagLeffler α β z = ∑' n : ℕ, z ^ n / Complex.Gamma ((α : ℂ) * n + β) :=
  rfl

/-- Stirling bound for the ratio `Γ(s) / Γ(s + α)` on the half-plane `1 ≤ re s`. -/
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

/-- The ratio `|Γ(αn + β) / Γ(αn + β + α)|` tends to zero, for `α > 0`. -/
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

/-- For `α > 0` and every complex `β`, the Mittag–Leffler function is the sum of its power series
`∑ zⁿ / Γ(αn + β)` on the whole plane. -/
theorem hasFPowerSeriesOnBall_mittagLeffler {α : ℝ} (hα : 0 < α) (β : ℂ) :
    HasFPowerSeriesOnBall (mittagLeffler α β)
      (FormalMultilinearSeries.ofScalars ℂ fun n : ℕ ↦ (Complex.Gamma ((α : ℂ) * n + β))⁻¹)
      0 ⊤ := by
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
  have hfun : mittagLeffler α β = p.sum := by
    ext z
    rw [mittagLeffler]
    simp only [p]
    rw [← FormalMultilinearSeries.ofScalarsSum,
      FormalMultilinearSeries.ofScalars_sum_eq c z]
    simp [c, div_eq_mul_inv, smul_eq_mul, mul_comm]
  rw [hfun, ← hrad]
  exact p.hasFPowerSeriesOnBall hpos

/-- **49.76**: for `α > 0` and every complex `β`, the Mittag–Leffler series converges at every
point. -/
theorem hasSum_mittagLeffler {α : ℝ} (hα : 0 < α) (β z : ℂ) :
    HasSum (fun n : ℕ ↦ z ^ n / Complex.Gamma ((α : ℂ) * n + β)) (mittagLeffler α β z) := by
  have hs := (hasFPowerSeriesOnBall_mittagLeffler hα β).hasSum
    (y := z) (by simp : z ∈ Metric.eball (0 : ℂ) ⊤)
  simpa [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, div_eq_mul_inv, mul_comm]
    using hs

/-- **49.76**: for `α > 0` and every complex `β`, the Mittag–Leffler function is entire. -/
theorem differentiable_mittagLeffler {α : ℝ} (hα : 0 < α) (β : ℂ) :
    Differentiable ℂ (mittagLeffler α β) := by
  rw [← differentiableOn_univ, ← Metric.eball_top_eq_univ (0 : ℂ)]
  exact (hasFPowerSeriesOnBall_mittagLeffler hα β).differentiableOn

/-- The exponential is the Mittag–Leffler function with parameters `(1,1)`. -/
theorem mittagLeffler_one_one (z : ℂ) : mittagLeffler 1 1 z = Complex.exp z := by
  simp only [mittagLeffler, Complex.ofReal_one, one_mul, Complex.Gamma_nat_eq_factorial]
  rw [Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum_div]

end CKMA
