/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
public import Mathlib.Analysis.Fourier.FourierTransform

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Periodic frequency-domain partial sums on the sampling band

Bandlimited continuous representatives, the normalized sinc function, Shannon sampling
summands, and periodic Fourier series expansions of frequency-domain `L²` data on
`AddCircle (2 * B)` over the band `[-B, B]`.

Source: GAPS 29.58.

The band-level auxiliary definitions and lemmas used in the proof of Shannon sampling live in
the namespace `CKMA.Shannon`.

## Main definitions

* `CKMA.bandlimitedRepresentative`: continuous representative defined by inverse Fourier
  integration over `[-B, B]`.
* `CKMA.normalizedSinc`: normalized sinc function `Real.sinc (π * t)`.
* `CKMA.shannonTerm`: `k`-th Shannon sampling summand at bandwidth `B`.
* `CKMA.Shannon.bandCutoff`: indicator cutoff to the frequency band `[-B, B]`.
* `CKMA.Shannon.samplingCharacter`: the character `exp(-2πi (k/(2B)) ξ)`.
* `CKMA.Shannon.freqPartial`: trigonometric partial sum with sample coefficients on `[-B, B]`.
* `CKMA.Shannon.freqBand`: trigonometric partial sum cut off to `[-B, B]`.

## Main results

* `CKMA.Shannon.fourierCoeffOn_neg_eq_sample`: Fourier coefficient at `-k` on `[-B, B]` equals
  `(2 * B)⁻¹` times the sample at `k / (2 * B)`.
* `CKMA.Shannon.integral_norm_sq_remainder`: squared `L²` norm of the frequency remainder as the
  tail of Parseval's series on `AddCircle (2 * B)`.
-/

public section

noncomputable section

namespace CKMA

open MeasureTheory FourierTransform Filter Topology Metric
open scoped BigOperators ENNReal FourierTransform Real Interval

/-- The continuous representative of inverse Fourier data supported in `[-B,B]`.
For `L²` data on this finite interval the integral is well-defined. -/
@[expose]
def bandlimitedRepresentative (B : ℝ) (u : Lp ℂ 2 (volume : Measure ℝ)) (t : ℝ) : ℂ :=
  ∫ ξ in Set.Icc (-B) B, Complex.exp (2 * Real.pi * Complex.I * t * ξ) * u ξ

/-- The normalized sinc in the sampling convention; Mathlib's `Real.sinc` is unnormalized. -/
@[expose]
def normalizedSinc (t : ℝ) : ℝ := Real.sinc (Real.pi * t)

/-- The `k`th Shannon summand at bandwidth `B`. -/
@[expose]
def shannonTerm (B : ℝ) (f : ℝ → ℂ) (k : ℤ) (t : ℝ) : ℂ :=
  f (k / (2 * B)) * normalizedSinc (2 * B * t - k)

/-- Unfolding the bandlimited representative. -/
theorem bandlimitedRepresentative_def (B : ℝ) (u : Lp ℂ 2 (volume : Measure ℝ)) (t : ℝ) :
    bandlimitedRepresentative B u t =
      ∫ ξ in Set.Icc (-B) B, Complex.exp (2 * Real.pi * Complex.I * t * ξ) * u ξ := rfl

/-- Unfolding the normalized sinc. -/
theorem normalizedSinc_def (t : ℝ) : normalizedSinc t = Real.sinc (Real.pi * t) := rfl

/-- The normalized sinc is `1` at the origin. -/
@[simp]
theorem normalizedSinc_zero : normalizedSinc 0 = 1 := by simp [normalizedSinc]

/-- Unfolding the Shannon summand. -/
theorem shannonTerm_def (B : ℝ) (f : ℝ → ℂ) (k : ℤ) (t : ℝ) :
    shannonTerm B f k t = f (k / (2 * B)) * normalizedSinc (2 * B * t - k) := rfl

namespace Shannon

variable {B : ℝ}

/-- Frequency datum cut off to the sampling band `[-B,B]`. -/
@[expose]
def bandCutoff (B : ℝ) (u : ℝ → ℂ) : ℝ → ℂ :=
  (Set.Icc (-B) B).indicator u

/-- The character `exp(-2πi (k/(2B)) ξ)` paired with the sample at `k/(2B)`. -/
@[expose]
def samplingCharacter (B : ℝ) (k : ℤ) (x : ℝ) : ℂ :=
  Complex.exp (-(2 * Real.pi * Complex.I * (k / (2 * B)) * x))

/-- Trigonometric partial sum with coefficients `(2B)⁻¹` times the samples of `f`. -/
@[expose]
def freqPartial (B : ℝ) (f : ℝ → ℂ) (s : Finset ℤ) (x : ℝ) : ℂ :=
  ∑ k ∈ s, ((2 * B)⁻¹ : ℝ) • f (k / (2 * B)) * samplingCharacter B k x

/-- The partial sum, viewed as an `L²(ℝ)` function supported on `[-B,B]`. -/
@[expose]
def freqBand (B : ℝ) (f : ℝ → ℂ) (s : Finset ℤ) : ℝ → ℂ :=
  bandCutoff B (freqPartial B f s)

/-- Unfolding the band cutoff. -/
theorem bandCutoff_def (B : ℝ) (u : ℝ → ℂ) : bandCutoff B u = (Set.Icc (-B) B).indicator u :=
  rfl

/-- Unfolding the sampling character. -/
theorem samplingCharacter_def (B : ℝ) (k : ℤ) (x : ℝ) :
    samplingCharacter B k x = Complex.exp (-(2 * Real.pi * Complex.I * (k / (2 * B)) * x)) :=
  rfl

/-- Unfolding the trigonometric partial sum. -/
theorem freqPartial_def (B : ℝ) (f : ℝ → ℂ) (s : Finset ℤ) (x : ℝ) :
    freqPartial B f s x = ∑ k ∈ s, ((2 * B)⁻¹ : ℝ) • f (k / (2 * B)) * samplingCharacter B k x :=
  rfl

/-- Unfolding the band-limited partial sum. -/
theorem freqBand_def (B : ℝ) (f : ℝ → ℂ) (s : Finset ℤ) :
    freqBand B f s = bandCutoff B (freqPartial B f s) := rfl

/-- Each sampling character has modulus one. -/
lemma norm_samplingCharacter (k : ℤ) (x : ℝ) :
    ‖samplingCharacter B k x‖ = 1 := by
  rw [samplingCharacter]
  have harg : -(2 * Real.pi * Complex.I * (k / (2 * B)) * x) =
      (↑(-(2 * Real.pi * (k / (2 * B)) * x)) : ℂ) * Complex.I := by
    simp only [Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_ofNat,
      Complex.ofReal_div, Complex.ofReal_intCast]
    ring
  rw [harg]
  exact Complex.norm_exp_ofReal_mul_I _

/-- Each sampling character is continuous. -/
lemma continuous_samplingCharacter (k : ℤ) :
    Continuous (samplingCharacter B k) := by
  unfold samplingCharacter
  fun_prop

/-- A trigonometric partial sum is continuous. -/
lemma continuous_freqPartial (f : ℝ → ℂ) (s : Finset ℤ) :
    Continuous (freqPartial B f s) := by
  unfold freqPartial
  induction s using Finset.induction with
  | empty =>
      simp only [Finset.sum_empty]
      exact continuous_const
  | insert a s ha hs =>
      simp only [Finset.sum_insert ha, Algebra.smul_def]
      exact (continuous_const.mul (continuous_samplingCharacter a)).add hs

section Positive

variable (hB : 0 < B)

include hB

/-- The period interval `[-B, -B + 2B]` of the sampling band is nondegenerate. Its right
endpoint is written as `-B + 2 * B` so that its length is definitionally the period `2 * B` used
by `fourierCoeffOn` on `AddCircle (2 * B)`. -/
lemma neg_lt_neg_add_two_mul : -B < -B + 2 * B :=
  lt_add_of_pos_right (-B) (mul_pos two_pos hB)

omit hB in
/-- The cutoff of an `L²` function remains square-integrable. -/
lemma memLp_bandCutoff (u : Lp ℂ 2 (volume : Measure ℝ)) :
    MemLp (bandCutoff B (⇑u)) 2 volume :=
  (Lp.memLp u).indicator measurableSet_Icc.nullMeasurableSet

omit hB in
/-- The cutoff of an `L²` function is integrable. -/
lemma integrable_bandCutoff (u : Lp ℂ 2 (volume : Measure ℝ)) :
    Integrable (bandCutoff B (⇑u)) := by
  rw [bandCutoff, integrable_indicator_iff measurableSet_Icc]
  refine integrableOn_Lp_of_measure_ne_top u fact_one_le_two_ennreal.elim ?_
  simp [Real.volume_Icc, ENNReal.ofReal_ne_top]

/-- Integral of a linear phase over `[-B,B]`, expressed by the normalized sinc. -/
lemma integral_exp_band (alpha : ℝ) :
    ∫ ξ in Set.Icc (-B) B, Complex.exp (2 * Real.pi * Complex.I * alpha * ξ) =
      (2 * B : ℂ) * (normalizedSinc (2 * B * alpha) : ℂ) := by
  have hle : -B ≤ B := by linarith
  rw [setIntegral_congr_set
      (MeasureTheory.Ioc_ae_eq_Icc' (by simp : volume {(-B)} = 0)).symm,
    ← intervalIntegral.integral_of_le hle]
  by_cases halpha : alpha = 0
  · rw [halpha]
    have hconst : ∀ x : ℝ,
        Complex.exp (2 * Real.pi * Complex.I * (0 : ℝ) * x) = 1 := by
      intro x
      simp [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    simp_rw [hconst, intervalIntegral.integral_const, sub_neg_eq_add, ← two_mul,
      Algebra.smul_def, normalizedSinc]
    have hzero : Real.pi * (2 * B * (0 : ℝ)) = 0 := by ring
    rw [hzero, Real.sinc_zero]
    simp [map_mul, Complex.ofReal_ofNat, mul_one]
  · set c : ℝ := 2 * Real.pi * alpha
    have hc : c ≠ 0 :=
      mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) halpha
    have hphase : ∀ x : ℝ,
        Complex.exp (2 * Real.pi * Complex.I * alpha * x) =
          Complex.exp (↑(c * x) * Complex.I) := by
      intro x
      apply congrArg Complex.exp
      simp only [c]
      push_cast
      ring
    conv_lhs =>
      enter [1, ξ]
      rw [hphase ξ]
    rw [intervalIntegral.integral_comp_mul_left
      (f := fun y : ℝ => Complex.exp (↑y * Complex.I)) hc]
    have hbound : c * -B = -(c * B) := by ring
    have harg : c * B = Real.pi * (2 * B * alpha) := by
      simp only [c]; ring
    rw [hbound, integral_exp_mul_I_eq_sinc, Algebra.smul_def, harg, normalizedSinc]
    have hreal : c⁻¹ * (2 * (Real.pi * (2 * B * alpha)) *
          Real.sinc (Real.pi * (2 * B * alpha))) =
        2 * B * Real.sinc (Real.pi * (2 * B * alpha)) := by
      field_simp [hc]
      simp only [c]
    convert congrArg Complex.ofReal hreal using 1
    · push_cast
      ac_rfl
    · push_cast
      ac_rfl

omit hB in
/-- The representative is the inverse Fourier integral of the band-limited cutoff. -/
lemma bandlimitedRepresentative_eq_fourierInv
    (u : Lp ℂ 2 (volume : Measure ℝ)) (t : ℝ) :
    bandlimitedRepresentative B u t = 𝓕⁻ (bandCutoff B (⇑u)) t := by
  rw [bandlimitedRepresentative, Real.fourierInv_eq', bandCutoff]
  have hmul : ∀ ξ : ℝ,
      Complex.exp (↑(2 * Real.pi * (ξ * t)) * Complex.I) *
          (Set.Icc (-B) B).indicator (⇑u) ξ =
        (Set.Icc (-B) B).indicator
          (fun ξ => Complex.exp (2 * Real.pi * Complex.I * t * ξ) * u ξ) ξ := by
    intro ξ
    by_cases hξ : ξ ∈ Set.Icc (-B) B
    · simp only [hξ, Set.indicator_of_mem]
      congr 1
      simp only [Complex.ofReal_mul, Complex.ofReal_ofNat]
      ring_nf
    · simp [hξ]
  simp_rw [Real.inner_apply, smul_eq_mul, hmul, integral_indicator measurableSet_Icc]

omit hB in
/-- Scaling by `(2B)⁻¹` inverts multiplication by the bandwidth. -/
private lemma inv_bandwidth_smul (hB : 0 < B) (z : ℂ) :
    ((2 * B)⁻¹ : ℝ) • ((2 * B : ℂ) * z) = z := by
  rw [Algebra.smul_def]
  push_cast
  have hB0 : (B : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hB
  field_simp [hB0]
  rfl

/-- Exponents `k/(2B)` and `k / (2B)` agree after the circle monomial is unwound. -/
private lemma phase_sample (k : ℤ) (x : ℝ) :
    2 * Real.pi * Complex.I * k * x / (2 * B) =
      2 * Real.pi * Complex.I * (k / (2 * B)) * x := by
  have hB0 : (B : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hB
  have h2 : (2 : ℂ) ≠ 0 := by norm_num
  field_simp [hB0, h2]

/-- Product of a circle monomial and a sampling character is one linear phase. -/
private lemma phase_product (k m : ℤ) (x : ℝ) :
    fourier (-m) (x : AddCircle (2 * B)) * samplingCharacter B k x =
      Complex.exp (2 * Real.pi * Complex.I *
        (-((m + k : ℤ) : ℝ) / (2 * B)) * x) := by
  rw [fourier_coe_apply, samplingCharacter, ← Complex.exp_add]
  congr 1
  have hB0 : (B : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hB
  have h2 : (2 : ℂ) ≠ 0 := by norm_num
  simp only [Int.cast_add, Int.cast_neg]
  push_cast
  field_simp [hB0, h2]
  ring_nf

/-- Circle coefficient of frequency `-k` is `(2B)⁻¹` times the sample at `k/(2B)`. -/
lemma fourierCoeffOn_neg_eq_sample (u : Lp ℂ 2 (volume : Measure ℝ)) (k : ℤ) :
    fourierCoeffOn (neg_lt_neg_add_two_mul hB) (⇑u) (-k) =
      ((2 * B)⁻¹ : ℝ) • bandlimitedRepresentative B u (k / (2 * B)) := by
  rw [fourierCoeffOn_eq_integral, bandlimitedRepresentative]
  simp_rw [show -B + 2 * B - -B = 2 * B by ring, show -B + 2 * B = B by ring, neg_neg]
  rw [intervalIntegral.integral_of_le (by linarith : -B ≤ B),
    setIntegral_congr_set (MeasureTheory.Ioc_ae_eq_Icc' (by simp : volume {(-B)} = 0)),
    one_div]
  refine congrArg (((2 * B)⁻¹ : ℝ) • ·) ?_
  refine setIntegral_congr_fun measurableSet_Icc fun x _ => ?_
  rw [fourier_coe_apply, smul_eq_mul]
  congr 1
  apply congrArg Complex.exp
  have hden : ((-B + 2 * B - -B : ℝ) : ℂ) = (2 * (B : ℂ)) := by
    exact_mod_cast (show -B + 2 * B - -B = 2 * B by ring)
  rw [hden]
  convert phase_sample hB k x using 1
  · push_cast
    ring

omit hB in
/-- A continuous phase times `L²` data is interval-integrable on the band. -/
private lemma intervalIntegrable_phase_u (u : Lp ℂ 2 (volume : Measure ℝ)) (n : ℤ) :
    IntervalIntegrable (fun x : ℝ => fourier n (x : AddCircle (2 * B)) * u x)
      volume (-B) B := by
  have hcont : Continuous fun x : ℝ => fourier n (x : AddCircle (2 * B)) :=
    (fourier n).continuous.comp (AddCircle.continuous_mk' (p := 2 * B))
  exact IntervalIntegrable.continuousOn_mul
    (((Lp.memLp u).locallyIntegrable one_le_two).integrableOn_isCompact
      isCompact_uIcc).intervalIntegrable hcont.continuousOn

/-- Integral of one sampling character against a circle monomial. -/
private lemma integral_fourier_sampling (k m : ℤ) :
    ∫ x in -B..B, fourier (-m) (x : AddCircle (2 * B)) * samplingCharacter B k x =
      (2 * B : ℂ) * (if m = -k then (1 : ℂ) else 0) := by
  have hphase : ∀ x : ℝ,
      fourier (-m) (x : AddCircle (2 * B)) * samplingCharacter B k x =
        Complex.exp (2 * Real.pi * Complex.I *
          (-((m + k : ℤ) : ℝ) / (2 * B)) * x) := phase_product hB k m
  simp_rw [hphase]
  rw [intervalIntegral.integral_of_le (by linarith : -B ≤ B),
    setIntegral_congr_set
      (MeasureTheory.Ioc_ae_eq_Icc' (by simp : volume {(-B)} = 0))]
  have harg : ∫ x in Set.Icc (-B) B,
      Complex.exp (2 * Real.pi * Complex.I *
        (-((m + k : ℤ) : ℝ) / (2 * B)) * x) =
    ∫ ξ in Set.Icc (-B) B,
      Complex.exp (2 * Real.pi * Complex.I *
        ((-((m + k : ℤ) : ℝ) / (2 * B) : ℝ)) * ξ) := by
    refine setIntegral_congr_fun measurableSet_Icc fun x _ => ?_
    apply congrArg Complex.exp
    push_cast
    ring
  rw [harg, integral_exp_band hB]
  have hscale : 2 * B * (-((m + k : ℤ) : ℝ) / (2 * B)) = -((m + k : ℤ) : ℝ) := by
    have hB0 : (2 * B : ℝ) ≠ 0 := mul_ne_zero two_ne_zero (ne_of_gt hB)
    field_simp [hB0]
  rw [hscale]
  rcases eq_or_ne (m + k) (0 : ℤ) with h0 | h0
  · have hm : m = -k := eq_neg_of_add_eq_zero_left h0
    simp [hm, neg_zero, Int.cast_zero, normalizedSinc, mul_zero, Real.sinc_zero, mul_one]
  · have hm : m ≠ -k := by
      intro hm
      apply h0
      rw [hm]
      exact neg_add_cancel k
    have hnz : Real.pi * (-((m + k : ℤ) : ℝ)) ≠ 0 :=
      mul_ne_zero Real.pi_ne_zero (by exact_mod_cast (neg_ne_zero.mpr h0))
    rw [normalizedSinc, Real.sinc_of_ne_zero hnz]
    have hsin : Real.sin (Real.pi * (-((m + k : ℤ) : ℝ))) = 0 := by
      simpa [mul_comm] using Real.sin_int_mul_pi (-(m + k))
    rw [hsin]
    simp [hm, zero_div, Complex.ofReal_zero, mul_zero]

/-- Circle coefficient of a sampling character is a Kronecker symbol. -/
private lemma fourierCoeffOn_samplingCharacter (k m : ℤ) :
    fourierCoeffOn (neg_lt_neg_add_two_mul hB) (samplingCharacter B k) m =
      if m = -k then 1 else 0 := by
  rw [fourierCoeffOn_eq_integral, show -B + 2 * B - -B = 2 * B by ring,
    show -B + 2 * B = B by ring, one_div]
  simp_rw [smul_eq_mul]
  rw [integral_fourier_sampling hB k m]
  exact inv_bandwidth_smul hB (if m = -k then (1 : ℂ) else 0)

/-- A complex constant factors out of `fourierCoeffOn`. -/
private lemma fourierCoeffOn_const_mul (f : ℝ → ℂ) (c : ℂ) (m : ℤ) :
    fourierCoeffOn (neg_lt_neg_add_two_mul hB) (fun x => c * f x) m =
      c * fourierCoeffOn (neg_lt_neg_add_two_mul hB) f m :=
  fourierCoeffOn.const_mul f c m (neg_lt_neg_add_two_mul hB)

/-- Coefficients of a finite sum are the sums of the coefficients. -/
private lemma fourierCoeffOn_finset_sum (s : Finset ℤ) (f : ℤ → ℝ → ℂ) (m : ℤ)
    (hf : ∀ k ∈ s, IntervalIntegrable (f k) volume (-B) B) :
    fourierCoeffOn (neg_lt_neg_add_two_mul hB) (fun x => ∑ k ∈ s, f k x) m =
      ∑ k ∈ s, fourierCoeffOn (neg_lt_neg_add_two_mul hB) (f k) m := by
  have hbound : ∀ g : ℝ → ℂ,
      (∫ x in -B..(-B + 2 * B), g x) = ∫ x in -B..B, g x := by
    intro _
    rw [show -B + 2 * B = B by ring]
  rw [fourierCoeffOn_eq_integral, show -B + 2 * B - -B = 2 * B by ring, hbound]
  have hsum : ∀ x : ℝ,
      fourier (-m) (x : AddCircle (2 * B)) • ∑ k ∈ s, f k x =
        ∑ k ∈ s, fourier (-m) (x : AddCircle (2 * B)) • f k x :=
    fun _ => Finset.smul_sum
  simp_rw [hsum]
  have hint : ∀ k ∈ s, IntervalIntegrable
      (fun x : ℝ => fourier (-m) (x : AddCircle (2 * B)) • f k x) volume (-B) B := by
    intro k hk
    have hcont : Continuous fun x : ℝ => fourier (-m) (x : AddCircle (2 * B)) :=
      (fourier (-m)).continuous.comp (AddCircle.continuous_mk' (p := 2 * B))
    have hmul : (fun x : ℝ => fourier (-m) (x : AddCircle (2 * B)) • f k x) =
        fun x : ℝ => fourier (-m) (x : AddCircle (2 * B)) * f k x := by
      ext x
      rw [smul_eq_mul]
    rw [hmul]
    exact IntervalIntegrable.continuousOn_mul (hf k hk) hcont.continuousOn
  rw [intervalIntegral.integral_finsetSum hint, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [fourierCoeffOn_eq_integral, show -B + 2 * B - -B = 2 * B by ring, hbound]

/-- Coefficients of the trigonometric partial sum are the selected circle coefficients. -/
private lemma fourierCoeffOn_freqPartial (u : Lp ℂ 2 (volume : Measure ℝ))
    (s : Finset ℤ) (m : ℤ) :
    fourierCoeffOn (neg_lt_neg_add_two_mul hB) (freqPartial B (bandlimitedRepresentative B u) s) m =
      if m ∈ s.image Neg.neg then fourierCoeffOn (neg_lt_neg_add_two_mul hB) (⇑u) m else 0 := by
  unfold freqPartial
  have hint : ∀ k ∈ s, IntervalIntegrable
      (fun x => ((2 * B)⁻¹ : ℝ) • bandlimitedRepresentative B u (k / (2 * B)) *
        samplingCharacter B k x) volume (-B) B := by
    intro k hk
    exact (continuous_const.mul (continuous_samplingCharacter k)).intervalIntegrable _ _
  rw [fourierCoeffOn_finset_sum hB s _ m hint]
  have hterm : ∀ k : ℤ,
      fourierCoeffOn (neg_lt_neg_add_two_mul hB)
          (fun x => ((2 * B)⁻¹ : ℝ) • bandlimitedRepresentative B u (k / (2 * B)) *
            samplingCharacter B k x) m =
        if m = -k then fourierCoeffOn (neg_lt_neg_add_two_mul hB) (⇑u) m else 0 := by
    intro k
    rw [fourierCoeffOn_const_mul hB (samplingCharacter B k)
        (((2 * B)⁻¹ : ℝ) • bandlimitedRepresentative B u (k / (2 * B))) m,
      fourierCoeffOn_samplingCharacter hB k m]
    by_cases hmk : m = -k
    · subst hmk
      rw [ite_eq_left rfl, ite_eq_left rfl, mul_one]
      exact (fourierCoeffOn_neg_eq_sample hB u k).symm
    · simp [hmk]
  simp_rw [hterm]
  by_cases hm : m ∈ s.image Neg.neg
  · have hk : -m ∈ s := by
      rcases Finset.mem_image.1 hm with ⟨a, ha, hma⟩
      simpa [← hma] using ha
    rw [ite_eq_left hm]
    have hsum := Finset.sum_eq_single (s := s) (f := fun k : ℤ =>
        if m = -k then fourierCoeffOn (neg_lt_neg_add_two_mul hB) (⇑u) m else 0) (-m)
      (by
        intro k _ hne
        have hmk : m ≠ -k := by
          intro hmk
          apply hne
          simp [hmk, neg_neg]
        simp [hmk])
      (by
        intro hnot
        exact absurd hk hnot)
    simpa [neg_neg] using hsum
  · rw [ite_eq_right hm]
    refine Finset.sum_eq_zero ?_
    intro k hk
    have hmk : m ≠ -k := by
      intro hmk
      apply hm
      exact Finset.mem_image.2 ⟨k, hk, hmk.symm⟩
    simp [hmk]

/-- Circle coefficients are linear for a band-limited difference. -/
private lemma fourierCoeffOn_sub (f g : ℝ → ℂ) (m : ℤ)
    (hf : IntervalIntegrable (fun x => fourier (-m) (x : AddCircle (2 * B)) * f x)
      volume (-B) B)
    (hg : IntervalIntegrable (fun x => fourier (-m) (x : AddCircle (2 * B)) * g x)
      volume (-B) B) :
    fourierCoeffOn (neg_lt_neg_add_two_mul hB) (f - g) m =
      fourierCoeffOn (neg_lt_neg_add_two_mul hB) f m -
        fourierCoeffOn (neg_lt_neg_add_two_mul hB) g m := by
  rw [fourierCoeffOn_eq_integral, fourierCoeffOn_eq_integral, fourierCoeffOn_eq_integral,
    show -B + 2 * B - -B = 2 * B by ring, show -B + 2 * B = B by ring]
  simp_rw [smul_eq_mul, Pi.sub_apply]
  have hsub : ∀ x : ℝ,
      fourier (-m) (x : AddCircle (2 * B)) * (f x - g x) =
        fourier (-m) (x : AddCircle (2 * B)) * f x -
          fourier (-m) (x : AddCircle (2 * B)) * g x :=
    fun x => mul_sub _ _ _
  simp_rw [hsub]
  rw [intervalIntegral.integral_sub hf hg, smul_sub]

/-- Circle coefficients of the frequency remainder vanish on the selected modes. -/
private lemma fourierCoeffOn_remainder (u : Lp ℂ 2 (volume : Measure ℝ))
    (s : Finset ℤ) (m : ℤ) :
    fourierCoeffOn (neg_lt_neg_add_two_mul hB)
        (⇑u - freqPartial B (bandlimitedRepresentative B u) s) m =
      if m ∈ s.image Neg.neg then 0 else fourierCoeffOn (neg_lt_neg_add_two_mul hB) (⇑u) m := by
  have hu := intervalIntegrable_phase_u (B := B) u (-m)
  have hp : IntervalIntegrable
      (fun x => fourier (-m) (x : AddCircle (2 * B)) *
        freqPartial B (bandlimitedRepresentative B u) s x) volume (-B) B :=
    IntervalIntegrable.continuousOn_mul
      ((continuous_freqPartial (bandlimitedRepresentative B u) s).intervalIntegrable (-B) B)
      (((fourier (-m)).continuous.comp
        (AddCircle.continuous_mk' (p := 2 * B))).continuousOn)
  rw [fourierCoeffOn_sub hB _ _ m hu hp, fourierCoeffOn_freqPartial hB u s m]
  by_cases hm : m ∈ s.image Neg.neg
  · simp [hm]
  · simp [hm]

omit hB in
/-- The tail of a summable series of squares, after deleting a finite set of modes. -/
private lemma tsum_sq_compl {c : ℤ → ℂ} (hc : Summable fun i => ‖c i‖ ^ 2) (s : Finset ℤ) :
    ∑' i, ‖if i ∈ s then (0 : ℂ) else c i‖ ^ 2 =
      ∑' i, ‖c i‖ ^ 2 - ∑ i ∈ s, ‖c i‖ ^ 2 := by
  classical
  let f : ℤ → ℝ := fun i => ‖c i‖ ^ 2
  let phi : ℤ → ℝ := fun i => if i ∈ s then 0 else f i
  have hphi : ∀ i, ‖if i ∈ s then (0 : ℂ) else c i‖ ^ 2 = phi i := by
    intro i
    by_cases hi : i ∈ s <;> simp [phi, f, hi]
  simp_rw [hphi]
  have hfin : Summable fun i => if i ∈ s then f i else 0 := by
    refine summable_of_ne_finset_zero (s := s) ?_
    intro i hi
    simp [hi]
  have hsum : (∑ i ∈ s, f i) + ∑' x : {x // x ∉ s}, f x = ∑' i, f i := by
    simpa using hc.sum_add_tsum_subtype_compl s
  have hsup : Function.support phi ⊆ Set.range (Subtype.val : {x // x ∉ s} → ℤ) := by
    intro i hi
    rw [Function.mem_support] at hi
    have hnot : i ∉ s := by
      intro his
      simp [phi, his] at hi
    exact ⟨⟨i, hnot⟩, rfl⟩
  have hsub : ∑' x : {x // x ∉ s}, phi x = ∑' i, phi i :=
    Subtype.val_injective.tsum_eq hsup
  have hphix : ∀ x : {x // x ∉ s}, phi x = f x := by
    intro x
    simp [phi, x.2]
  simp_rw [hphix] at hsub
  have htail : ∑' i, phi i = ∑' i, f i - ∑ i ∈ s, f i := by
    rw [← hsub, eq_sub_iff_add_eq, add_comm]
    exact hsum
  simpa [f] using htail

/-- Squared `L²` norm of a frequency remainder, as a tail of Parseval's series. -/
lemma integral_norm_sq_remainder (u : Lp ℂ 2 (volume : Measure ℝ)) (s : Finset ℤ) :
    ∫ x, ‖(bandCutoff B (⇑u) - freqBand B (bandlimitedRepresentative B u) s) x‖ ^ 2 =
      (2 * B) * (∑' i, ‖fourierCoeffOn (neg_lt_neg_add_two_mul hB) (⇑u) i‖ ^ 2 -
        ∑ i ∈ s.image Neg.neg, ‖fourierCoeffOn (neg_lt_neg_add_two_mul hB) (⇑u) i‖ ^ 2) := by
  let c : ℤ → ℂ := fourierCoeffOn (neg_lt_neg_add_two_mul hB) (⇑u)
  let r : ℝ → ℂ := ⇑u - freqPartial B (bandlimitedRepresentative B u) s
  have hmem : MemLp r 2 (volume.restrict (Set.Ioc (-B) (-B + 2 * B))) := by
    refine ((Lp.memLp u).restrict _).sub ?_
    refine MemLp.of_bound
      ((continuous_freqPartial (bandlimitedRepresentative B u) s).aestronglyMeasurable.mono_ac
        (Measure.absolutelyContinuous_of_le Measure.restrict_le_self))
      (∑ k ∈ s, ‖((2 * B)⁻¹ : ℝ) •
        bandlimitedRepresentative B u (k / (2 * B))‖) ?_
    filter_upwards with x
    unfold freqPartial
    refine (norm_sum_le _ _).trans ?_
    refine Finset.sum_le_sum fun k _ => ?_
    rw [norm_mul, norm_samplingCharacter k x, mul_one]
  have htail := tsum_sq_compl
    (hasSum_sq_fourierCoeffOn (neg_lt_neg_add_two_mul hB)
      ((Lp.memLp u).restrict _)).summable (s.image Neg.neg)
  have hparse := tsum_sq_fourierCoeffOn (neg_lt_neg_add_two_mul hB) hmem
  have hcoeff : ∀ i, fourierCoeffOn (neg_lt_neg_add_two_mul hB) r i =
      if i ∈ s.image Neg.neg then 0 else c i := by
    intro i
    simpa [r, c] using fourierCoeffOn_remainder hB u s i
  simp_rw [hcoeff] at hparse
  rw [hparse] at htail
  have hint : ∫ x in -B..(-B + 2 * B), ‖r x‖ ^ 2 =
      ∫ x, ‖(bandCutoff B (⇑u) -
        freqBand B (bandlimitedRepresentative B u) s) x‖ ^ 2 := by
    rw [show -B + 2 * B = B by ring]
    rw [intervalIntegral.integral_of_le (by linarith : -B ≤ B)]
    rw [setIntegral_congr_set
      (MeasureTheory.Ioc_ae_eq_Icc' (by simp : volume {(-B)} = 0))]
    rw [← integral_indicator measurableSet_Icc]
    refine integral_congr_ae ?_
    filter_upwards with x
    rw [bandCutoff, freqBand, bandCutoff]
    have hind : (Set.Icc (-B) B).indicator (⇑u) x -
        (Set.Icc (-B) B).indicator
          (freqPartial B (bandlimitedRepresentative B u) s) x =
        (Set.Icc (-B) B).indicator r x := by
      simp only [r]
      by_cases hx : x ∈ Set.Icc (-B) B <;> simp [hx]
    rw [Pi.sub_apply, hind]
    by_cases hx : x ∈ Set.Icc (-B) B <;> simp [hx]
  rw [hint] at htail
  have hscalar : (((-B + 2 * B) - (-B))⁻¹ : ℝ) = (2 * B)⁻¹ := by
    rw [show -B + 2 * B - -B = 2 * B by ring]
  rw [hscalar, smul_eq_mul] at htail
  have hB0 : (2 * B : ℝ) ≠ 0 := mul_ne_zero two_ne_zero (ne_of_gt hB)
  have htail' := congrArg (fun t : ℝ => (2 * B) * t) htail
  rw [← mul_assoc, mul_inv_cancel₀ hB0, one_mul] at htail'
  exact htail'

end Positive

end Shannon

end CKMA
