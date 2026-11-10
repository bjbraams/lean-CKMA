/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
public import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.SpecialFunctions.Bessel
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

/-- **49.6**: Gauss's multiplication formula at all nonpolar complex parameters.
The positive real bases fix the principal-power branches. -/
theorem gamma_multiplication (m : ℕ) (hm : 0 < m) (z : ℂ)
    (hz : ∀ n : ℕ, (m : ℂ) * z ≠ -(n : ℂ)) :
    (∏ j : Fin m, Complex.Gamma (z + (j.val : ℂ) / m)) =
      (2 * Real.pi : ℂ) ^ (((m : ℂ) - 1) / 2) *
      (m : ℂ) ^ ((1 / 2 : ℂ) - (m : ℂ) * z) * Complex.Gamma ((m : ℂ) * z) := by
  sorry

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

/-- Normalization at zero determines the analytic solution germ, for a regular denominator
  parameter. -/
theorem gauss_hypergeometric_unique (a b c : ℂ) (hc : ∀ n : ℕ, c ≠ -(n : ℂ))
    {y : ℂ → ℂ} (hy : AnalyticAt ℂ y 0) (hy0 : y 0 = 1)
    (hode : ∀ᶠ z in 𝓝 (0 : ℂ), gaussDifferentialExpression a b c y z = 0) :
    y =ᶠ[𝓝 (0 : ℂ)] ordinaryHypergeometric a b c := by
  sorry

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

/-- **49.30**: the bilateral Bessel generating series. -/
theorem hasSum_bessel_generating (z : ℂ) {t : ℂ} (ht : t ≠ 0) :
    HasSum (fun n : ℤ ↦ Complex.besselJ (n : ℂ) z * t ^ n)
      (Complex.exp ((z / 2) * (t - t⁻¹))) := by
  sorry

/-- Normal convergence on compact sets in `(z,t)` away from `t=0`, including uniformity in `z`. -/
theorem normallySummableOn_bessel_generating :
    NormallySummableOn (fun n : ℤ ↦ fun p : ℂ × ℂ ↦ Complex.besselJ (n : ℂ) p.1 * p.2 ^ n)
      {p | p.2 ≠ 0} := by
  sorry

end CKMA
