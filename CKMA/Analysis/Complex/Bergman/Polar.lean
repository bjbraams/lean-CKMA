/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.PolarCoord

import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Dynamics.Ergodic.MeasurePreserving

/-!
# Polar reduction for weighted Bergman integrals

The weighted area integral of a monomial reduces to a Beta integral in polar coordinates.
On each circle, the Fourier coefficient of a holomorphic function is its Taylor coefficient,
by Cauchy's formula. These identities are the analytic input for the Bergman kernel and the
orthogonal projection.

## Main results

* `CKMA.integral_pow_mul_one_sub_rpow`:
  `∫₀¹ xⁿ (1 - x)^α = Γ(α + 1) n! / Γ(n + α + 2)`.
* `CKMA.bergmanMonomialNormSq`: the monomial weight `Γ(α + 2) n! / Γ(n + α + 2)`.
* `CKMA.intervalIntegral_circle_taylorCoeff`: circular means equal Taylor coefficients.
* `CKMA.integral_radial_monomial_weight`: the radial factor in the monomial norm.

The Beta identity uses Mathlib's `Complex.betaIntegral` and
`Complex.Gamma_mul_Gamma_eq_betaIntegral`. The circular mean uses
`DifferentiableOn.circleIntegral_one_div_sub_center_pow_smul`. The radial substitution
uses `MeasureTheory.integral_comp_rpow_Ioi_of_pos`.
-/

public section

noncomputable section

namespace CKMA

open Complex Filter MeasureTheory Real Set intervalIntegral
open scoped ENNReal ComplexConjugate InnerProductSpace

/-- `∫₀¹ xⁿ (1 - x)^α`, for `α > -1`, as a ratio of Gamma values.
`Real.rpow` of a nonpositive base is the usual junk value, but the integrand is integrated on
`(0, 1)`, where both bases are positive. -/
lemma integral_pow_mul_one_sub_rpow {α : ℝ} (hα : -1 < α) (n : ℕ) :
    (∫ x in (0 : ℝ)..1, x ^ n * (1 - x) ^ α) =
      Real.Gamma (α + 1) * n.factorial / Real.Gamma (n + α + 2) := by
  have hα1 : 0 < α + 1 := by linarith
  have hsn : 0 < ((n + 1 : ℕ) : ℂ).re := by
    rw [Complex.natCast_re]
    positivity
  have htn : 0 < ((α + 1 : ℝ) : ℂ).re := by
    rw [Complex.ofReal_re]
    exact hα1
  have hnat : ((n + 1 : ℕ) : ℂ) = (n : ℂ) + 1 := by
    rw [Nat.cast_add, Nat.cast_one]
  have hsum : (n : ℂ) + 1 + ((α + 1 : ℝ) : ℂ) = ((n + α + 2 : ℝ) : ℂ) := by
    push_cast
    ring
  have hbeta : Complex.betaIntegral ((n + 1 : ℕ) : ℂ) ((α + 1 : ℝ) : ℂ) =
      Complex.ofReal (∫ x in (0 : ℝ)..1, x ^ n * (1 - x) ^ α) := by
    rw [Complex.betaIntegral]
    refine (integral_congr_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1) fun x hx => ?_).trans
      intervalIntegral.integral_ofReal
    rw [mem_Ioo] at hx
    have hx0 : 0 ≤ x := hx.1.le
    have hx1 : 0 ≤ 1 - x := sub_nonneg.mpr hx.2.le
    have hn : ((n + 1 : ℕ) : ℂ) - 1 = (n : ℂ) := by rw [hnat]; ring
    have hαc : ((α + 1 : ℝ) : ℂ) - 1 = (α : ℂ) := by
      rw [Complex.ofReal_add, Complex.ofReal_one]; ring
    rw [hn, hαc, ← Complex.ofReal_natCast, ← Complex.ofReal_cpow hx0 n, rpow_natCast,
      ← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_cpow hx1 α,
      ← Complex.ofReal_mul]
  have hG := Complex.Gamma_mul_Gamma_eq_betaIntegral hsn htn
  rw [hbeta, hnat, Complex.Gamma_nat_eq_factorial, hsum, Complex.Gamma_ofReal,
    Complex.Gamma_ofReal] at hG
  have hpos : Real.Gamma (n + α + 2) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by linarith [(Nat.cast_nonneg n : 0 ≤ (n : ℝ))])).ne'
  have hI : Real.Gamma (n + α + 2) * (∫ x in (0 : ℝ)..1, x ^ n * (1 - x) ^ α) =
      (n.factorial : ℝ) * Real.Gamma (α + 1) := by
    apply Complex.ofReal_injective
    rw [Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_natCast]
    exact hG.symm
  rw [mul_comm, ← eq_div_iff hpos, mul_comm (n.factorial : ℝ)] at hI
  exact hI

/-- Square of the weighted `L²` norm of `z ↦ z ^ n`. -/
@[expose]
def bergmanMonomialNormSq (α : ℝ) (n : ℕ) : ℝ :=
  Real.Gamma (α + 2) * n.factorial / Real.Gamma (n + α + 2)

/-- The monomial weight `cₙ` is positive for `α > -1`. -/
lemma bergmanMonomialNormSq_pos {α : ℝ} (hα : -1 < α) (n : ℕ) :
    0 < bergmanMonomialNormSq α n := by
  dsimp only [bergmanMonomialNormSq]
  have h2 : 0 < α + 2 := by linarith
  have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hn : 0 < (n : ℝ) + α + 2 := by linarith [hnn]
  have hfact : (0 : ℝ) < (n.factorial : ℝ) := Nat.cast_pos.mpr n.factorial_pos
  exact div_pos (mul_pos (Real.Gamma_pos_of_pos h2) hfact) (Real.Gamma_pos_of_pos hn)

/-- The monomial weight `cₙ` is nonzero for `α > -1`. -/
lemma bergmanMonomialNormSq_ne_zero {α : ℝ} (hα : -1 < α) (n : ℕ) :
    bergmanMonomialNormSq α n ≠ 0 :=
  (bergmanMonomialNormSq_pos hα n).ne'

/-- `∫ exp(k θ I) dθ` over a full turn vanishes unless `k = 0`. -/
lemma integral_exp_int_mul_I (k : ℤ) :
    ∫ θ in (-π)..π, Complex.exp ((k : ℂ) * (θ : ℂ) * I) =
      if k = 0 then (2 * π : ℂ) else 0 := by
  by_cases hk : k = 0
  · subst hk
    have hconst : EqOn (fun θ : ℝ => Complex.exp (((0 : ℤ) : ℂ) * (θ : ℂ) * I))
        (fun _ => (1 : ℂ)) (Set.uIcc (-π) π) := by
      intro θ _
      dsimp
      rw [show ((0 : ℤ) : ℂ) * (θ : ℂ) * I = 0 by ring, Complex.exp_zero]
    rw [intervalIntegral.integral_congr hconst, intervalIntegral.integral_const,
      ite_eq_left rfl, sub_neg_eq_add, Algebra.smul_def, Complex.coe_algebraMap, mul_one]
    rw [show (π + π : ℝ) = 2 * π by ring, Complex.ofReal_mul]
    norm_cast
  · rw [ite_eq_right hk]
    have hc : (k : ℂ) * I ≠ 0 := mul_ne_zero (Int.cast_ne_zero.mpr hk) I_ne_zero
    have halign : ∀ θ : ℝ, Complex.exp ((k : ℂ) * (θ : ℂ) * I) =
        Complex.exp (((k : ℂ) * I) * (θ : ℂ)) := by
      intro θ
      congr 1
      ring
    simp_rw [halign]
    rw [integral_exp_mul_complex hc]
    set c : ℂ := (k : ℂ) * I
    rw [ofReal_neg]
    have hpos : Complex.exp (c * π) = (-1 : ℂ) ^ k := by
      have hord : c * π = k * (π * I) := by
        dsimp [c]
        ring
      rw [hord, Complex.exp_int_mul, Complex.exp_pi_mul_I]
    have hneg : Complex.exp (c * (-π)) = ((-1 : ℂ) ^ k)⁻¹ := by
      have hord : c * (-π) = -(c * π) := by ring
      rw [hord, Complex.exp_neg, hpos]
    have hself : ((-1 : ℂ) ^ k)⁻¹ = (-1 : ℂ) ^ k := by
      refine inv_eq_of_mul_eq_one_left ?_
      rw [← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
      have hadd : (k + k : ℤ) = 2 * k := by ring
      rw [hadd, zpow_mul]
      norm_num
    rw [hpos, hneg, hself, sub_self, zero_div]

/-- Polar form of `conj(z ^ n) * z ^ m`. -/
lemma conj_pow_mul_pow_polar (n m : ℕ) (r θ : ℝ) :
    conj ((Complex.polarCoord.symm (r, θ)) ^ n) * (Complex.polarCoord.symm (r, θ)) ^ m =
      (r : ℂ) ^ (n + m) *
        Complex.exp ((((m : ℤ) - (n : ℤ)) : ℂ) * (θ : ℂ) * I) := by
  have hz : Complex.polarCoord.symm (r, θ) = (r : ℂ) * Complex.exp ((θ : ℂ) * I) := by
    rw [Complex.polarCoord_symm_apply]
    dsimp
    rw [Complex.ofReal_cos, Complex.ofReal_sin, ← Complex.exp_mul_I]
  rw [hz]
  have hpow : ∀ k : ℕ, ((r : ℂ) * Complex.exp ((θ : ℂ) * I)) ^ k =
      (r : ℂ) ^ k * Complex.exp ((k : ℂ) * (θ : ℂ) * I) := by
    intro k
    rw [mul_pow, ← Complex.exp_nat_mul]
    congr 1
    rw [← mul_assoc]
  rw [hpow n, hpow m, map_mul conj, map_pow conj, conj_ofReal, ← Complex.exp_conj]
  have hconj : conj ((n : ℂ) * (θ : ℂ) * I) = -((n : ℂ) * (θ : ℂ) * I) := by
    rw [map_mul conj, map_mul conj, Complex.conj_natCast, Complex.conj_ofReal, Complex.conj_I]
    ring
  rw [hconj]
  have hexp : Complex.exp (-((n : ℂ) * (θ : ℂ) * I)) *
        Complex.exp ((m : ℂ) * (θ : ℂ) * I) =
      Complex.exp ((((m : ℤ) - (n : ℤ)) : ℂ) * (θ : ℂ) * I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  calc
    (r : ℂ) ^ n * Complex.exp (-((n : ℂ) * (θ : ℂ) * I)) *
        ((r : ℂ) ^ m * Complex.exp ((m : ℂ) * (θ : ℂ) * I))
        = (r : ℂ) ^ n * (r : ℂ) ^ m *
          (Complex.exp (-((n : ℂ) * (θ : ℂ) * I)) *
            Complex.exp ((m : ℂ) * (θ : ℂ) * I)) := by ring
    _ = (r : ℂ) ^ (n + m) *
          Complex.exp ((((m : ℤ) - (n : ℤ)) : ℂ) * (θ : ℂ) * I) := by
        rw [← pow_add, hexp]

/-- Taylor coefficient of `f` at the origin, `(iteratedDeriv n f 0) / n!`. -/
@[expose]
def bergmanTaylorCoeff (f : ℂ → ℂ) (n : ℕ) : ℂ :=
  (n.factorial : ℂ)⁻¹ * iteratedDeriv n f 0

/-- On each circle of radius `r ∈ (0, 1)`, the Fourier coefficient of a holomorphic function is
its Taylor coefficient. -/
lemma intervalIntegral_circle_taylorCoeff {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (Metric.ball 0 1)) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (n : ℕ) :
    ∫ θ in (-π)..π, Complex.exp (-(n : ℂ) * (θ : ℂ) * I) * f (circleMap 0 r θ) =
      2 * π * bergmanTaylorCoeff f n * (r : ℂ) ^ n := by
  set g : ℝ → ℂ := fun θ =>
    Complex.exp (-(n : ℂ) * (θ : ℂ) * I) * f (circleMap 0 r θ)
  have hpi : Complex.exp (2 * π * I) = 1 := by
    have hper0 := Complex.exp_periodic (0 : ℂ)
    rw [zero_add, Complex.exp_zero] at hper0
    exact hper0
  have hper : Function.Periodic g (2 * π) := by
    intro θ
    have hcirc : circleMap 0 r (θ + 2 * π) = circleMap 0 r θ := by
      rw [circleMap_zero, circleMap_zero]
      congr 1
      have hsum : ((θ + 2 * π : ℝ) : ℂ) * I = (θ : ℂ) * I + 2 * π * I := by
        push_cast
        ring
      rw [hsum, Complex.exp_add, hpi, mul_one]
    have hcoeff : Complex.exp (-(n : ℂ) * ((θ + 2 * π : ℝ) : ℂ) * I) =
        Complex.exp (-(n : ℂ) * (θ : ℂ) * I) := by
      have hsplit : Complex.exp (-(n : ℂ) * ((θ + 2 * π : ℝ) : ℂ) * I) =
          Complex.exp (-(n : ℂ) * (θ : ℂ) * I) *
            Complex.exp (-(n : ℂ) * (2 * π) * I) := by
        rw [← Complex.exp_add]
        congr 1
        push_cast
        ring
      have hone : Complex.exp (-(n : ℂ) * (2 * π) * I) = 1 := by
        have hord : -(n : ℂ) * (2 * π) * I = (-n : ℤ) * (2 * π * I) := by
          push_cast
          ring
        rw [hord, Complex.exp_int_mul, hpi, one_zpow]
      rw [hsplit, hone, mul_one]
    simp only [g, hcirc, hcoeff]
  have hshift : ∫ θ in (-π)..π, g θ = ∫ θ in (0)..(2 * π), g θ := by
    have hint := hper.intervalIntegral_add_eq (-π) 0
    have hleft : -π + 2 * π = π := by ring
    have hright : (0 : ℝ) + 2 * π = 2 * π := by ring
    rw [hleft, hright] at hint
    exact hint
  have hdiff : DifferentiableOn ℂ f (Metric.closedBall 0 r) :=
    hf.mono (Metric.closedBall_subset_ball hr1)
  have hcauchy := hdiff.circleIntegral_one_div_sub_center_pow_smul hr0 n
  have hintg : ∀ θ, (circleMap 0 r θ * I) *
      ((1 / (circleMap 0 r θ) ^ (n + 1)) * f (circleMap 0 r θ)) =
      (I * ((r : ℂ) ^ n)⁻¹) * g θ := by
    intro θ
    set z : ℂ := circleMap 0 r θ
    have hz : z ≠ 0 := by
      dsimp only [z]
      rw [circleMap_zero]
      exact mul_ne_zero (ofReal_ne_zero.mpr hr0.ne') (Complex.exp_ne_zero _)
    have hpow : z ^ n = (r : ℂ) ^ n * Complex.exp ((n : ℂ) * (θ : ℂ) * I) := by
      rw [show z = circleMap 0 r θ from rfl, circleMap_zero_pow, circleMap_zero, ← ofReal_pow]
      congr 1
      have hexp : ((n * θ : ℝ) : ℂ) * I = (n : ℂ) * (θ : ℂ) * I := by
        push_cast
        ring
      rw [hexp]
    have hinv : z * (z ^ (n + 1))⁻¹ = (z ^ n)⁻¹ := by
      rw [pow_succ, mul_inv_rev, ← mul_assoc, mul_inv_cancel₀ hz, one_mul]
    calc
      (z * I) * ((1 / z ^ (n + 1)) * f z)
          = I * (z * (z ^ (n + 1))⁻¹) * f z := by
            rw [one_div]
            ring
      _ = I * (z ^ n)⁻¹ * f z := by rw [hinv]
      _ = I * (((r : ℂ) ^ n)⁻¹ * Complex.exp (-((n : ℂ) * (θ : ℂ) * I))) * f z := by
            rw [hpow, mul_inv_rev, Complex.exp_neg]
            ring
      _ = (I * ((r : ℂ) ^ n)⁻¹) * g θ := by
            simp only [g, z]
            have hexp : Complex.exp (-((n : ℂ) * (θ : ℂ) * I)) =
                Complex.exp (-(n : ℂ) * (θ : ℂ) * I) := by
              congr 1
              rw [neg_mul, neg_mul]
            rw [hexp, ← mul_assoc, mul_assoc]
  simp_rw [circleIntegral, deriv_circleMap, sub_zero, smul_eq_mul] at hcauchy
  simp_rw [hintg] at hcauchy
  rw [intervalIntegral.integral_const_mul] at hcauchy
  have hcne : I * ((r : ℂ) ^ n)⁻¹ ≠ 0 :=
    mul_ne_zero I_ne_zero (inv_ne_zero (pow_ne_zero n (ofReal_ne_zero.mpr hr0.ne')))
  have hIang : ∫ θ in (0)..(2 * π), g θ =
      (I * ((r : ℂ) ^ n)⁻¹)⁻¹ *
        ((2 * π * I / (n.factorial : ℂ)) * iteratedDeriv n f 0) :=
    (eq_inv_mul_iff_mul_eq₀ hcne).2 hcauchy
  rw [hshift, hIang, bergmanTaylorCoeff]
  have hcinv : (I * ((r : ℂ) ^ n)⁻¹)⁻¹ = (r : ℂ) ^ n * I⁻¹ := by
    rw [mul_inv_rev, inv_inv]
  rw [hcinv]
  have hfact : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  field_simp [I_ne_zero, hfact]

/-- The radial weight in the monomial norm: `2π` times this integral is `cₙ`. -/
lemma integral_radial_monomial_weight {α : ℝ} (hα : -1 < α) (n : ℕ) :
    ∫ r in Ioi (0 : ℝ),
        (if r < 1 then ((α + 1) / π) * (1 - r ^ 2) ^ α * r ^ (2 * n + 1) else 0) =
      bergmanMonomialNormSq α n / (2 * π) := by
  set c : ℝ := (α + 1) / π
  have hc : 0 < c := div_pos (by linarith) pi_pos
  let φ : ℝ → ℝ := fun r =>
    if r < 1 then c * (1 - r ^ 2) ^ α * r ^ (2 * n + 1) else 0
  have hφpoint : ∀ r, φ r =
      if r < 1 then ((α + 1) / π) * (1 - r ^ 2) ^ α * r ^ (2 * n + 1) else 0 := by
    intro r
    dsimp only [φ, c]
  rw [setIntegral_congr_fun measurableSet_Ioi fun r _ => (hφpoint r).symm]
  have hφ : ∀ r, φ r =
      c * (if r < 1 then (1 - r ^ 2) ^ α * r ^ (2 * n + 1) else 0) := by
    intro r
    by_cases hr : r < 1
    · dsimp only [φ]
      rw [ite_eq_left hr, ite_eq_left hr, mul_assoc]
    · dsimp only [φ]
      rw [ite_eq_right hr, ite_eq_right hr, mul_zero]
  simp_rw [hφ, MeasureTheory.integral_const_mul]
  let ψ : ℝ → ℝ := fun u =>
    if 0 < u ∧ u < 1 then (1 / 2) * u ^ n * (1 - u) ^ α else 0
  have hrad : ∫ r in Ioi (0 : ℝ),
      (if r < 1 then (1 - r ^ 2) ^ α * r ^ (2 * n + 1) else 0) =
      ∫ u in Ioi (0 : ℝ), ψ u := by
    rw [← integral_comp_rpow_Ioi_of_pos (g := ψ) (p := 2) (by norm_num : (0 : ℝ) < 2)]
    refine setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
    have hr0 : (0 : ℝ) < r := hr
    have h21 : (2 : ℝ) - 1 = 1 := by norm_num
    have h2 : ((2 : ℕ) : ℝ) = 2 := by norm_num
    rw [h21, rpow_one, ← h2, rpow_natCast]
    by_cases h1 : r < 1
    · have hr2 : 0 < r ^ 2 := by positivity
      have hr2lt : r ^ 2 < 1 := by
        rw [← one_pow 2]
        exact pow_lt_pow_left₀ h1 hr0.le two_ne_zero
      dsimp only [ψ]
      have hr2mem : 0 < r ^ 2 ∧ r ^ 2 < 1 := ⟨hr2, hr2lt⟩
      rw [smul_eq_mul, ite_eq_left hr2mem, ite_eq_left h1]
      have hpow : (r ^ 2) ^ n = r ^ (2 * n) := by rw [← pow_mul]
      calc
        (1 - r ^ 2) ^ α * r ^ (2 * n + 1)
            = r ^ (2 * n + 1) * (1 - r ^ 2) ^ α := by ring
        _ = (r * (r ^ 2) ^ n) * (1 - r ^ 2) ^ α := by rw [pow_succ', ← hpow]
        _ = 2 * r * ((1 / 2) * (r ^ 2) ^ n * (1 - r ^ 2) ^ α) := by ring
    · have hr2ge : ¬ (0 < r ^ 2 ∧ r ^ 2 < 1) := by
        intro hr2
        have hr1 : r < 1 := by
          rw [← one_pow 2] at hr2
          exact lt_of_pow_lt_pow_left₀ 2 zero_le_one hr2.2
        exact h1 hr1
      dsimp only [ψ]
      rw [ite_eq_right h1, ite_eq_right hr2ge, smul_eq_mul, mul_zero]
  rw [hrad]
  have hψ : ∫ u in Ioi (0 : ℝ), ψ u =
      (1 / 2) * ∫ x in (0 : ℝ)..1, x ^ n * (1 - x) ^ α := by
    have hψind : ψ = fun u =>
        (1 / 2) * (Ioo (0 : ℝ) 1).indicator (fun v => v ^ n * (1 - v) ^ α) u := by
      ext u
      by_cases hu : u ∈ Ioo (0 : ℝ) 1
      · have hmem : 0 < u ∧ u < 1 := mem_Ioo.mp hu
        dsimp only [ψ]
        rw [ite_eq_left hmem, indicator_of_mem hu, mul_assoc]
      · have hnot : ¬ (0 < u ∧ u < 1) := by simpa [mem_Ioo] using hu
        dsimp only [ψ]
        rw [ite_eq_right hnot, indicator_of_notMem hu, mul_zero]
    rw [hψind, MeasureTheory.integral_const_mul,
      setIntegral_indicator measurableSet_Ioo]
    have hinter : Ioi (0 : ℝ) ∩ Ioo 0 1 = Ioo 0 1 := by
      ext u
      simp only [mem_inter_iff, mem_Ioi, mem_Ioo]
      exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩
    rw [hinter, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      setIntegral_congr_set Ioo_ae_eq_Ioc.symm]
  rw [hψ, integral_pow_mul_one_sub_rpow hα n, bergmanMonomialNormSq]
  have hne : α + 1 ≠ 0 := by linarith
  have hshift : (α + 1) + 1 = α + 2 := by ring
  have hcπ : c * π = α + 1 := by
    dsimp [c]
    exact div_mul_cancel₀ _ Real.pi_ne_zero
  have hnum : (α + 1) * Real.Gamma (α + 1) = Real.Gamma (α + 2) := by
    rw [← Real.Gamma_add_one hne, hshift]
  have hπ : (2 : ℝ) * π ≠ 0 := mul_ne_zero two_ne_zero Real.pi_ne_zero
  have hG1 : Real.Gamma (α + 1) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by linarith : 0 < α + 1)).ne'
  have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hGn : Real.Gamma (n + α + 2) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by linarith [hnn] : 0 < (n : ℝ) + α + 2)).ne'
  field_simp [hπ, hG1, hGn, hc.ne']
  calc
    c * Real.Gamma (α + 1) * π = c * π * Real.Gamma (α + 1) := by ring
    _ = (α + 1) * Real.Gamma (α + 1) := by rw [hcπ]
    _ = Real.Gamma (α + 2) := hnum

/-- Polar coordinates centred at the origin agree with `circleMap`. -/
lemma polarCoord_symm_eq_circleMap (r θ : ℝ) :
    Complex.polarCoord.symm (r, θ) = circleMap 0 r θ := by
  rw [Complex.polarCoord_symm_apply, circleMap_zero, Complex.ofReal_cos, Complex.ofReal_sin,
    ← Complex.exp_mul_I]

/-- Pull an integrable density on `ℂ` back to polar coordinates, including the Jacobian factor. -/
lemma integrableOn_smul_polarCoord {g : ℂ → ℂ} (hg : Integrable g volume) :
    IntegrableOn (fun p : ℝ × ℝ => p.1 • g (Complex.polarCoord.symm p)) polarCoord.target := by
  have hpres :=
    MeasurePreserving.symm measurableEquivRealProd volume_preserving_equiv_real_prod
  have hge : Integrable (g ∘ measurableEquivRealProd.symm) volume :=
    hpres.integrable_comp_of_integrable hg
  have hsource : IntegrableOn (g ∘ measurableEquivRealProd.symm)
      (polarCoord.symm '' polarCoord.target) volume := by
    rw [polarCoord.symm_image_target_eq_source]
    exact hge.integrableOn
  have hjac := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul (μ := volume)
      (f := polarCoord.symm) (f' := fderivPolarCoordSymm) (s := polarCoord.target)
      polarCoord.open_target.measurableSet
      (fun p _ => (hasFDerivAt_polarCoord_symm p).hasFDerivWithinAt) polarCoord.symm.injOn
      (g ∘ measurableEquivRealProd.symm)).1 hsource
  refine hjac.congr_fun ?_ polarCoord.open_target.measurableSet
  intro p hp
  dsimp only
  rw [Function.comp_apply]
  rw [measurableEquivRealProd_symm_polarCoord_symm_apply, det_fderivPolarCoordSymm]
  rw [polarCoord_target, mem_prod] at hp
  rw [abs_of_pos hp.1]


end CKMA
