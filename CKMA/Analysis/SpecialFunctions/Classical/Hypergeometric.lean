/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
public import TauCeti.Analysis.SpecialFunctions.OrdinaryHypergeometric

/-!
# Gauss's hypergeometric differential equation

The hypergeometric series solves Gauss's equation in the unit disk and is the unique normalized
analytic solution germ at the origin; the regularized function `F(a, b; c; z) / Γ(c)` solves the
same equation for every `c`. The three singular points `0`, `1`, and `∞` are regular singular, as
witnessed by analytic rational germs in local and reciprocal coordinates.

The basic computation is `CKMA.hasSum_gaussDifferentialExpression`: inside the disc of a scalar
power series `∑ Cₙ zⁿ`, Gauss's expression is the series with coefficients
`(n + 1) (c + n) Cₙ₊₁ - (a + n) (b + n) Cₙ`. It uses TauCeti's termwise differentiation
`HasFPowerSeriesOnBall.deriv_ofScalars` and `HasFPowerSeriesOnBall.hasSum_mul_deriv_ofScalars`.
The equation for the ordinary series is TauCeti's
`TauCeti.ordinaryHypergeometric_gaussEquation_of_norm_lt_one`.

## Main definitions

* `CKMA.gaussDifferentialExpression`: Gauss's hypergeometric differential expression.
* `CKMA.IsRegularSingularAt`: the regular-singular criterion for `y'' + P y' + Q y = 0` at a finite
  point.
* `CKMA.IsRegularSingularAtInfinity`: the regular-singular criterion at infinity after `z = 1 / w`.

## Main results

* `CKMA.hasSum_gaussDifferentialExpression`: Gauss's expression of a scalar power series.
* `CKMA.gaussDifferentialExpression_eq_zero_of_coeff`: the coefficient recurrence implies Gauss's
  equation inside the disc of convergence.
* `CKMA.regularizedGaussHGFunSeries_coeff_recurrence`: the recurrence of the regularized
  coefficients, for every `c`.
* `CKMA.gauss_regularized_hypergeometric_ode`: the regularized Gauss hypergeometric function
  satisfies Gauss's equation in the unit disk, for all parameters.
* `CKMA.gauss_hypergeometric_ode`: the ordinary hypergeometric series solves Gauss's equation in
  the unit disk (**49.13**).
* `CKMA.gauss_hypergeometric_unique`: uniqueness of the normalized analytic solution germ at `0`.
* `CKMA.gauss_isRegularSingularAt`: `0`, `1`, and `∞` are regular singular points of Gauss's
  equation.
-/

public section

noncomputable section

namespace CKMA

open Filter Topology FormalMultilinearSeries
open scoped BigOperators ENNReal NNReal

section GaussExpression

variable {𝕂 : Type*} [NontriviallyNormedField 𝕂]

/-- Gauss's hypergeometric differential expression
`z (1 - z) y'' + (c - (a + b + 1) z) y' - a b y`. -/
@[expose]
def gaussDifferentialExpression (a b c : 𝕂) (y : 𝕂 → 𝕂) (z : 𝕂) : 𝕂 :=
  z * (1 - z) * deriv (deriv y) z + (c - (a + b + 1) * z) * deriv y z - a * b * y z

/-- Unfolding lemma for `gaussDifferentialExpression`. -/
theorem gaussDifferentialExpression_def (a b c : 𝕂) (y : 𝕂 → 𝕂) (z : 𝕂) :
    gaussDifferentialExpression a b c y z =
      z * (1 - z) * deriv (deriv y) z + (c - (a + b + 1) * z) * deriv y z - a * b * y z :=
  rfl

/-- Every scalar formal multilinear series is the scalar series of its coefficients. -/
theorem ofScalars_coeff_self (p : FormalMultilinearSeries 𝕂 𝕂 𝕂) :
    ofScalars 𝕂 p.coeff = p := by
  ext n
  rw [ofScalars_apply_eq, one_pow, smul_eq_mul, mul_one]
  rfl

variable [CompleteSpace 𝕂]

/-- Inside the disc of a scalar power series `y = ∑ Cₙ zⁿ`, Gauss's expression is the series with
coefficients `(n + 1) (c + n) Cₙ₊₁ - (a + n) (b + n) Cₙ`. -/
theorem hasSum_gaussDifferentialExpression {y : 𝕂 → 𝕂} {C : ℕ → 𝕂} {r : ℝ≥0∞}
    (hy : HasFPowerSeriesOnBall y (ofScalars 𝕂 C) 0 r) (a b c : 𝕂) {z : 𝕂} (hz : ‖z‖ₑ < r) :
    HasSum (fun n : ℕ ↦ (((n : 𝕂) + 1) * (c + n) * C (n + 1) - (a + n) * (b + n) * C n) * z ^ n)
      (gaussDifferentialExpression a b c y z) := by
  have hy' := hy.deriv_ofScalars
  have hzb : z ∈ Metric.eball (0 : 𝕂) r := mem_eball_zero_iff.mpr hz
  have h0 : HasSum (fun n : ℕ ↦ C n * z ^ n) (y z) := by
    simpa [ofScalars_apply_eq, mul_comm] using hy.hasSum hzb
  have h1 : HasSum (fun n : ℕ ↦ (n + 1) * C (n + 1) * z ^ n) (deriv y z) := by
    simpa [ofScalars_apply_eq, mul_comm] using hy'.hasSum hzb
  have h2 := hy.hasSum_mul_deriv_ofScalars hz
  have h3 := hy'.hasSum_mul_deriv_ofScalars hz
  have h4 : HasSum (fun n : ℕ ↦ ((n : 𝕂) - 1) * n * C n * z ^ n)
      (z * (z * deriv (deriv y) z)) := by
    refine (hasSum_nat_add_iff' 1).mp ?_
    simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using h3.mul_left z
  have hsum := (h3.add (h1.mul_left c)).sub ((h4.add (h2.mul_left (a + b + 1))).add
    (h0.mul_left (a * b)))
  rw [gaussDifferentialExpression_def]
  convert hsum using 1
  · ext n
    ring
  · ring

/-- If the coefficients of a scalar power series obey Gauss's recurrence
`(n + 1) (c + n) Cₙ₊₁ = (a + n) (b + n) Cₙ`, its sum solves Gauss's equation inside the disc. -/
theorem gaussDifferentialExpression_eq_zero_of_coeff {y : 𝕂 → 𝕂} {C : ℕ → 𝕂} {r : ℝ≥0∞}
    (hy : HasFPowerSeriesOnBall y (ofScalars 𝕂 C) 0 r) {a b c : 𝕂}
    (hC : ∀ n : ℕ, ((n : 𝕂) + 1) * (c + n) * C (n + 1) = (a + n) * (b + n) * C n)
    {z : 𝕂} (hz : ‖z‖ₑ < r) :
    gaussDifferentialExpression a b c y z = 0 := by
  have h := hasSum_gaussDifferentialExpression hy a b c hz
  simp only [hC, sub_self, zero_mul] at h
  exact h.unique hasSum_zero

/-- Conversely, the Taylor coefficients of an analytic solution of Gauss's equation near `0` obey
Gauss's recurrence. -/
theorem coeff_recurrence_of_gaussDifferentialExpression {y : 𝕂 → 𝕂}
    {p : FormalMultilinearSeries 𝕂 𝕂 𝕂} {r : ℝ≥0∞} (hp : HasFPowerSeriesOnBall y p 0 r)
    {a b c : 𝕂} (hode : ∀ᶠ z in 𝓝 (0 : 𝕂), gaussDifferentialExpression a b c y z = 0) (n : ℕ) :
    ((n : 𝕂) + 1) * (c + n) * p.coeff (n + 1) = (a + n) * (b + n) * p.coeff n := by
  rw [← ofScalars_coeff_self p] at hp
  have hser : HasFPowerSeriesAt (0 : 𝕂 → 𝕂) (ofScalars 𝕂 fun n : ℕ ↦
      ((n : 𝕂) + 1) * (c + n) * p.coeff (n + 1) - (a + n) * (b + n) * p.coeff n) 0 := by
    rw [hasFPowerSeriesAt_iff]
    filter_upwards [hode, Metric.eball_mem_nhds (0 : 𝕂) hp.r_pos] with z hodez hz
    have h := hasSum_gaussDifferentialExpression hp a b c (mem_eball_zero_iff.mp hz)
    rw [hodez] at h
    simpa [coeff_ofScalars, mul_comm] using h
  have h := congr_arg (fun q : FormalMultilinearSeries 𝕂 𝕂 𝕂 ↦ q.coeff n) hser.eq_zero
  rw [coeff_ofScalars] at h
  exact sub_eq_zero.mp (h.trans rfl)

end GaussExpression

/-- The Gauss coefficient recurrence `(n + 1) (c + n) C̃ₙ₊₁ = (a + n) (b + n) C̃ₙ` of the
regularized coefficients `C̃ₙ = (a)ₙ (b)ₙ / (n! Γ(c + n))`, for every `c`. When `c + n = 0`, both
sides vanish, by Mathlib's convention `Γ(0) = 0`. -/
theorem regularizedGaussHGFunSeries_coeff_recurrence (a b c : ℂ) (n : ℕ) :
    ((n : ℂ) + 1) * (c + n) *
        (Complex.regularizedGaussHGFunSeries a b c).coeff (n + 1) =
      (a + n) * (b + n) * (Complex.regularizedGaussHGFunSeries a b c).coeff n := by
  simp only [Complex.coeff_regularizedGaussHGFunSeries]
  by_cases hcn : c + n = 0
  · simp [hcn]
  · rw [Nat.cast_add_one, ← add_assoc, Complex.Gamma_add_one _ hcn, ascPochhammer_succ_eval,
      ascPochhammer_succ_eval, Nat.factorial_succ]
    push_cast
    field_simp

/-- The regularized Gauss hypergeometric function `F(a, b; c; z) / Γ(c)` satisfies Gauss's
equation in the unit disk, for all parameters `a`, `b`, `c`. -/
theorem gauss_regularized_hypergeometric_ode (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    gaussDifferentialExpression a b c (Complex.regularizedGaussHGFun a b c) z = 0 := by
  have hr : 1 ≤ (Complex.regularizedGaussHGFunSeries a b c).radius :=
    Complex.radius_regularizedGaussHGFunSeries_ge_one a b c
  have hp : HasFPowerSeriesOnBall (Complex.regularizedGaussHGFun a b c)
      (ofScalars ℂ (Complex.regularizedGaussHGFunSeries a b c).coeff) 0
      (Complex.regularizedGaussHGFunSeries a b c).radius := by
    rw [ofScalars_coeff_self]
    exact (Complex.regularizedGaussHGFunSeries a b c).hasFPowerSeriesOnBall
      (lt_of_lt_of_le zero_lt_one hr)
  refine gaussDifferentialExpression_eq_zero_of_coeff hp
    (regularizedGaussHGFunSeries_coeff_recurrence a b c) ?_
  exact (by rw [← ofReal_norm]; exact ENNReal.ofReal_lt_one.mpr hz : ‖z‖ₑ < 1).trans_le hr

section Ordinary

variable {𝕂 : Type*} [RCLike 𝕂]

/-- **49.13**: the hypergeometric series solves Gauss's equation in the unit disk, when the
denominator parameter `c` avoids the nonpositive integers. This is TauCeti's
`TauCeti.ordinaryHypergeometric_gaussEquation_of_norm_lt_one`. -/
theorem gauss_hypergeometric_ode (a b c : 𝕂) (hc : ∀ k : ℕ, (k : 𝕂) ≠ -c)
    {z : 𝕂} (hz : ‖z‖ < 1) :
    gaussDifferentialExpression a b c (ordinaryHypergeometric a b c) z = 0 :=
  TauCeti.ordinaryHypergeometric_gaussEquation_of_norm_lt_one a b c hc hz

/-- Normalization at zero determines the analytic solution germ of Gauss's equation, when the
denominator parameter `c` avoids the nonpositive integers. -/
theorem gauss_hypergeometric_unique (a b c : 𝕂) (hc : ∀ k : ℕ, (k : 𝕂) ≠ -c)
    {y : 𝕂 → 𝕂} (hy : AnalyticAt 𝕂 y 0) (hy0 : y 0 = 1)
    (hode : ∀ᶠ z in 𝓝 (0 : 𝕂), gaussDifferentialExpression a b c y z = 0) :
    y =ᶠ[𝓝 (0 : 𝕂)] ordinaryHypergeometric a b c := by
  obtain ⟨p, r, hp⟩ := hy
  have hcoeff : ∀ n, p.coeff n = ordinaryHypergeometricCoefficient a b c n := by
    intro n
    induction n with
    | zero =>
      rw [show p.coeff 0 = y 0 from hp.coeff_zero (1 : Fin 0 → 𝕂), hy0]
      simp [ordinaryHypergeometricCoefficient]
    | succ n ih =>
      have hn : (n : 𝕂) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
      have hcn : c + (n : 𝕂) ≠ 0 := fun h ↦ hc n (eq_neg_of_add_eq_zero_right h)
      apply mul_left_cancel₀ (mul_ne_zero hn hcn)
      rw [coeff_recurrence_of_gaussDifferentialExpression hp hode n, ih,
        TauCeti.ordinaryHypergeometricCoefficient_add_one]
      field_simp
  have hpeq : p = ordinaryHypergeometricSeries 𝕂 a b c := by
    rw [← ofScalars_coeff_self p, ordinaryHypergeometricSeries]
    exact congr_arg _ (funext hcoeff)
  filter_upwards [Metric.eball_mem_nhds (0 : 𝕂) hp.r_pos] with z hz
  have hyz : y z = p.sum z := by simpa using hp.sum hz
  rw [hyz, ordinaryHypergeometric, hpeq]

end Ordinary

/-- The regular-singular criterion for `y'' + P y' + Q y = 0`, allowing removable singularities.
Punctured equalities avoid false continuity claims for totalized rational functions at their poles.
  -/
@[expose]
def IsRegularSingularAt (P Q : ℂ → ℂ) (a : ℂ) : Prop :=
  ∃ p q : ℂ → ℂ, AnalyticAt ℂ p a ∧ AnalyticAt ℂ q a ∧
    (∀ᶠ z in 𝓝[≠] a, p z = (z - a) * P z) ∧
    (∀ᶠ z in 𝓝[≠] a, q z = (z - a) ^ 2 * Q z)

/-- Characterization of `IsRegularSingularAt` by analytic germs `p`, `q` with
`p = (z - a) P` and `q = (z - a)² Q` on a punctured neighbourhood of `a`. -/
theorem isRegularSingularAt_iff {P Q : ℂ → ℂ} {a : ℂ} :
    IsRegularSingularAt P Q a ↔ ∃ p q : ℂ → ℂ, AnalyticAt ℂ p a ∧ AnalyticAt ℂ q a ∧
      (∀ᶠ z in 𝓝[≠] a, p z = (z - a) * P z) ∧
      (∀ᶠ z in 𝓝[≠] a, q z = (z - a) ^ 2 * Q z) :=
  Iff.rfl

/-- The regular-singular criterion at infinity, after the coordinate change `z = 1/w`. -/
@[expose]
def IsRegularSingularAtInfinity (P Q : ℂ → ℂ) : Prop :=
  IsRegularSingularAt (fun w ↦ 2 / w - P w⁻¹ / w ^ 2) (fun w ↦ Q w⁻¹ / w ^ 4) 0

/-- `IsRegularSingularAtInfinity P Q` is the regular-singular criterion at `0` for the equation
transformed by `z = 1/w`. -/
theorem isRegularSingularAtInfinity_iff {P Q : ℂ → ℂ} :
    IsRegularSingularAtInfinity P Q ↔
      IsRegularSingularAt (fun w ↦ 2 / w - P w⁻¹ / w ^ 2) (fun w ↦ Q w⁻¹ / w ^ 4) 0 :=
  Iff.rfl

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

end CKMA
