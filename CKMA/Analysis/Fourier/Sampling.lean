/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.Fourier.LpSpace
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Bandlimited representatives and Shannon sampling

Inverse Fourier integration over `[-B,B]` gives a continuous representative from any
L² frequency datum. Shannon summands use samples at `k/(2B)` and the normalized sinc
`sin(πt)/(πt)`. Reconstruction converges pointwise, uniformly and in L², and the
representative satisfies an exact sampling Parseval identity. These statements depend
only on the datum inside the integration band.

Source: GAPS 29.58.
-/

@[expose] public section

noncomputable section

namespace CKMA

open MeasureTheory FourierTransform Filter Topology Metric
open scoped BigOperators ENNReal FourierTransform Real Interval SchwartzMap

/-- The continuous representative of inverse Fourier data supported in `[-B,B]`.
For `L²` data on this finite interval the integral is well-defined. -/
def bandlimitedRepresentative (B : ℝ) (u : Lp ℂ 2 (volume : Measure ℝ)) (t : ℝ) : ℂ :=
  ∫ ξ in Set.Icc (-B) B, Complex.exp (2 * Real.pi * Complex.I * t * ξ) * u ξ

/-- The normalized sinc in the sampling convention; Mathlib's `Real.sinc` is unnormalized. -/
def normalizedSinc (t : ℝ) : ℝ := Real.sinc (Real.pi * t)

/-- The `k`th Shannon summand at bandwidth `B`. -/
def shannonTerm (B : ℝ) (f : ℝ → ℂ) (k : ℤ) (t : ℝ) : ℂ :=
  f (k / (2 * B)) * normalizedSinc (2 * B * t - k)

variable {B : ℝ}

/-- Frequency datum cut off to the sampling band `[-B,B]`. -/
private def bandCutoff (B : ℝ) (u : ℝ → ℂ) : ℝ → ℂ :=
  (Set.Icc (-B) B).indicator u

/-- The character `exp(-2πi (k/(2B)) ξ)` paired with the sample at `k/(2B)`. -/
private def samplingCharacter (B : ℝ) (k : ℤ) (x : ℝ) : ℂ :=
  Complex.exp (-(2 * Real.pi * Complex.I * (k / (2 * B)) * x))

/-- Trigonometric partial sum with coefficients `(2B)⁻¹` times the samples of `f`. -/
private def freqPartial (B : ℝ) (f : ℝ → ℂ) (s : Finset ℤ) (x : ℝ) : ℂ :=
  ∑ k ∈ s, ((2 * B)⁻¹ : ℝ) • f (k / (2 * B)) * samplingCharacter B k x

/-- The partial sum, viewed as an `L²(ℝ)` function supported on `[-B,B]`. -/
private def freqBand (B : ℝ) (f : ℝ → ℂ) (s : Finset ℤ) : ℝ → ℂ :=
  bandCutoff B (freqPartial B f s)

/-- A linear phase has complex modulus one. -/
private lemma norm_phase (t ξ : ℝ) :
    ‖Complex.exp (2 * Real.pi * Complex.I * t * ξ)‖ = 1 := by
  have harg : 2 * Real.pi * Complex.I * t * ξ =
      (↑(2 * Real.pi * t * ξ) : ℂ) * Complex.I := by
    simp only [Complex.ofReal_mul, Complex.ofReal_ofNat]
    ring
  rw [harg]
  exact Complex.norm_exp_ofReal_mul_I _

/-- Integer values of the normalized sinc are the Kronecker symbol at `0`. -/
private lemma normalizedSinc_int (m : ℤ) :
    normalizedSinc (m : ℝ) = if m = 0 then 1 else 0 := by
  by_cases hm : m = 0
  · simp [hm, normalizedSinc]
  · have hπ : Real.pi * (m : ℝ) ≠ 0 :=
      mul_ne_zero Real.pi_ne_zero (by exact_mod_cast hm)
    rw [normalizedSinc, Real.sinc_of_ne_zero hπ]
    have hsin : Real.sin (Real.pi * (m : ℝ)) = 0 := by
      simpa [mul_comm] using Real.sin_int_mul_pi m
    simp [hsin, hm]

/-- The normalized sinc is even. -/
private lemma normalizedSinc_neg (t : ℝ) : normalizedSinc (-t) = normalizedSinc t := by
  simp [normalizedSinc, Real.sinc_neg]

/-- Each sampling character has modulus one. -/
private lemma norm_samplingCharacter (k : ℤ) (x : ℝ) :
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
private lemma continuous_samplingCharacter (k : ℤ) :
    Continuous (samplingCharacter B k) := by
  unfold samplingCharacter
  fun_prop

/-- A trigonometric partial sum is continuous. -/
private lemma continuous_freqPartial (f : ℝ → ℂ) (s : Finset ℤ) :
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

/-- The sampling band, written so that its length is definitionally a period `2B`. -/
private lemma band_lt : -B < -B + 2 * B :=
  lt_add_of_pos_right (-B) (mul_pos two_pos hB)

omit hB in
/-- Right endpoint of the period interval based at `-B`. -/
private lemma band_right : -B + 2 * B = B := by ring

omit hB in
/-- Length of that period interval. -/
private lemma band_period : (-B + 2 * B) - (-B) = 2 * B := by ring

omit hB in
/-- The cutoff of an `L²` function remains square-integrable. -/
private lemma memLp_bandCutoff (u : Lp ℂ 2 (volume : Measure ℝ)) :
    MemLp (bandCutoff B (⇑u)) 2 volume :=
  (Lp.memLp u).indicator measurableSet_Icc.nullMeasurableSet

omit hB in
/-- The cutoff of an `L²` function is integrable. -/
private lemma integrable_bandCutoff (u : Lp ℂ 2 (volume : Measure ℝ)) :
    Integrable (bandCutoff B (⇑u)) := by
  rw [bandCutoff, integrable_indicator_iff measurableSet_Icc]
  refine integrableOn_Lp_of_measure_ne_top u fact_one_le_two_ennreal.elim ?_
  simp [Real.volume_Icc, ENNReal.ofReal_ne_top]

/-- Integral of a linear phase over `[-B,B]`, expressed by the normalized sinc. -/
private lemma integral_exp_band (alpha : ℝ) :
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
private lemma bandlimitedRepresentative_eq_fourierInv
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
      ring
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
private lemma fourierCoeffOn_neg_eq_sample (u : Lp ℂ 2 (volume : Measure ℝ)) (k : ℤ) :
    fourierCoeffOn (band_lt hB) (⇑u) (-k) =
      ((2 * B)⁻¹ : ℝ) • bandlimitedRepresentative B u (k / (2 * B)) := by
  rw [fourierCoeffOn_eq_integral, bandlimitedRepresentative]
  simp_rw [band_period, band_right, neg_neg]
  rw [intervalIntegral.integral_of_le (by linarith : -B ≤ B),
    setIntegral_congr_set (MeasureTheory.Ioc_ae_eq_Icc' (by simp : volume {(-B)} = 0)),
    one_div]
  refine congrArg (((2 * B)⁻¹ : ℝ) • ·) ?_
  refine setIntegral_congr_fun measurableSet_Icc fun x _ => ?_
  rw [fourier_coe_apply, smul_eq_mul]
  congr 1
  apply congrArg Complex.exp
  have hden : ((-B + 2 * B - -B : ℝ) : ℂ) = (2 * (B : ℂ)) := by
    exact_mod_cast (band_period)
  rw [hden]
  convert phase_sample hB k x using 1
  · push_cast
    ring

omit hB in
/-- The band-limited cutoff is square-integrable on the period interval. -/
private lemma memLp_u_Ioc (u : Lp ℂ 2 (volume : Measure ℝ)) :
    MemLp (⇑u) 2 (volume.restrict (Set.Ioc (-B) (-B + 2 * B))) :=
  (Lp.memLp u).restrict _

/-- `L²` data on the sampling band are interval-integrable. -/
private lemma intervalIntegrable_u (u : Lp ℂ 2 (volume : Measure ℝ)) :
    IntervalIntegrable (⇑u) volume (-B) B := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith : -B ≤ B)]
  rw [← integrable_indicator_iff measurableSet_Icc]
  simpa [bandCutoff] using integrable_bandCutoff u

/-- A continuous phase times band-limited `L²` data stays interval-integrable. -/
private lemma intervalIntegrable_phase_u (u : Lp ℂ 2 (volume : Measure ℝ)) (n : ℤ) :
    IntervalIntegrable (fun x : ℝ => fourier n (x : AddCircle (2 * B)) * u x)
      volume (-B) B := by
  have hcont : Continuous fun x : ℝ => fourier n (x : AddCircle (2 * B)) :=
    (fourier n).continuous.comp (AddCircle.continuous_mk' (p := 2 * B))
  exact IntervalIntegrable.continuousOn_mul (intervalIntegrable_u hB u) hcont.continuousOn

omit hB in
/-- Sampling characters are interval-integrable. -/
private lemma intervalIntegrable_samplingCharacter (k : ℤ) :
    IntervalIntegrable (samplingCharacter B k) volume (-B) B :=
  (continuous_samplingCharacter k).intervalIntegrable _ _

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
    fourierCoeffOn (band_lt hB) (samplingCharacter B k) m = if m = -k then 1 else 0 := by
  rw [fourierCoeffOn_eq_integral, band_period, band_right, one_div]
  simp_rw [smul_eq_mul]
  rw [integral_fourier_sampling hB k m]
  exact inv_bandwidth_smul hB (if m = -k then (1 : ℂ) else 0)

/-- A complex constant factors out of `fourierCoeffOn`. -/
private lemma fourierCoeffOn_const_mul (f : ℝ → ℂ) (c : ℂ) (m : ℤ) :
    fourierCoeffOn (band_lt hB) (fun x => c * f x) m =
      c * fourierCoeffOn (band_lt hB) f m :=
  fourierCoeffOn.const_mul f c m (band_lt hB)

/-- Coefficients of a finite sum are the sums of the coefficients. -/
private lemma fourierCoeffOn_finset_sum (s : Finset ℤ) (f : ℤ → ℝ → ℂ) (m : ℤ)
    (hf : ∀ k ∈ s, IntervalIntegrable (f k) volume (-B) B) :
    fourierCoeffOn (band_lt hB) (fun x => ∑ k ∈ s, f k x) m =
      ∑ k ∈ s, fourierCoeffOn (band_lt hB) (f k) m := by
  have hbound : ∀ g : ℝ → ℂ,
      (∫ x in -B..(-B + 2 * B), g x) = ∫ x in -B..B, g x := by
    intro _
    rw [band_right]
  rw [fourierCoeffOn_eq_integral, band_period, hbound]
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
  rw [fourierCoeffOn_eq_integral, band_period, hbound]

/-- Coefficients of the trigonometric partial sum are the selected circle coefficients. -/
private lemma fourierCoeffOn_freqPartial (u : Lp ℂ 2 (volume : Measure ℝ))
    (s : Finset ℤ) (m : ℤ) :
    fourierCoeffOn (band_lt hB) (freqPartial B (bandlimitedRepresentative B u) s) m =
      if m ∈ s.image Neg.neg then fourierCoeffOn (band_lt hB) (⇑u) m else 0 := by
  unfold freqPartial
  have hint : ∀ k ∈ s, IntervalIntegrable
      (fun x => ((2 * B)⁻¹ : ℝ) • bandlimitedRepresentative B u (k / (2 * B)) *
        samplingCharacter B k x) volume (-B) B := by
    intro k hk
    exact (continuous_const.mul (continuous_samplingCharacter k)).intervalIntegrable _ _
  rw [fourierCoeffOn_finset_sum hB s _ m hint]
  have hterm : ∀ k : ℤ,
      fourierCoeffOn (band_lt hB)
          (fun x => ((2 * B)⁻¹ : ℝ) • bandlimitedRepresentative B u (k / (2 * B)) *
            samplingCharacter B k x) m =
        if m = -k then fourierCoeffOn (band_lt hB) (⇑u) m else 0 := by
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
        if m = -k then fourierCoeffOn (band_lt hB) (⇑u) m else 0) (-m)
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
    fourierCoeffOn (band_lt hB) (f - g) m =
      fourierCoeffOn (band_lt hB) f m - fourierCoeffOn (band_lt hB) g m := by
  rw [fourierCoeffOn_eq_integral, fourierCoeffOn_eq_integral, fourierCoeffOn_eq_integral,
    band_period, band_right]
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
    fourierCoeffOn (band_lt hB) (⇑u - freqPartial B (bandlimitedRepresentative B u) s) m =
      if m ∈ s.image Neg.neg then 0 else fourierCoeffOn (band_lt hB) (⇑u) m := by
  have hu := intervalIntegrable_phase_u hB u (-m)
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
/-- Squared modulus of an indicator is the indicator of the squared modulus. -/
private lemma norm_sq_indicator (s : Set ℝ) (f : ℝ → ℂ) (x : ℝ) :
    ‖s.indicator f x‖ ^ 2 = s.indicator (fun y => ‖f y‖ ^ 2) x := by
  by_cases hx : x ∈ s <;> simp [hx]

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
private lemma integral_norm_sq_remainder (u : Lp ℂ 2 (volume : Measure ℝ)) (s : Finset ℤ) :
    ∫ x, ‖(bandCutoff B (⇑u) - freqBand B (bandlimitedRepresentative B u) s) x‖ ^ 2 =
      (2 * B) * (∑' i, ‖fourierCoeffOn (band_lt hB) (⇑u) i‖ ^ 2 -
        ∑ i ∈ s.image Neg.neg, ‖fourierCoeffOn (band_lt hB) (⇑u) i‖ ^ 2) := by
  let c : ℤ → ℂ := fourierCoeffOn (band_lt hB) (⇑u)
  let r : ℝ → ℂ := ⇑u - freqPartial B (bandlimitedRepresentative B u) s
  have hmem : MemLp r 2 (volume.restrict (Set.Ioc (-B) (-B + 2 * B))) := by
    refine (memLp_u_Ioc u).sub ?_
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
    (hasSum_sq_fourierCoeffOn (band_lt hB) (memLp_u_Ioc u)).summable (s.image Neg.neg)
  have hparse := tsum_sq_fourierCoeffOn (band_lt hB) hmem
  have hcoeff : ∀ i, fourierCoeffOn (band_lt hB) r i =
      if i ∈ s.image Neg.neg then 0 else c i := by
    intro i
    simpa [r, c] using fourierCoeffOn_remainder hB u s i
  simp_rw [hcoeff] at hparse
  rw [hparse] at htail
  have hint : ∫ x in -B..(-B + 2 * B), ‖r x‖ ^ 2 =
      ∫ x, ‖(bandCutoff B (⇑u) -
        freqBand B (bandlimitedRepresentative B u) s) x‖ ^ 2 := by
    rw [band_right]
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
    exact (norm_sq_indicator (Set.Icc (-B) B) r x).symm
  rw [hint] at htail
  have hscalar : (((-B + 2 * B) - (-B))⁻¹ : ℝ) = (2 * B)⁻¹ := by
    rw [band_period]
  rw [hscalar, smul_eq_mul] at htail
  have hB0 : (2 * B : ℝ) ≠ 0 := mul_ne_zero two_ne_zero (ne_of_gt hB)
  have htail' := congrArg (fun t : ℝ => (2 * B) * t) htail
  rw [← mul_assoc, mul_inv_cancel₀ hB0, one_mul] at htail'
  exact htail'

omit hB in
/-- Negation preserves the `atTop` filter of finite sets. -/
private lemma tendsto_image_neg :
    Tendsto (fun s : Finset ℤ => s.image Neg.neg) atTop atTop := by
  rw [Filter.tendsto_atTop]
  intro b
  rw [eventually_atTop]
  refine ⟨b.image Neg.neg, fun s hs k hk => ?_⟩
  refine Finset.mem_image.2 ⟨-k, hs ?_, neg_neg k⟩
  exact Finset.mem_image.2 ⟨k, hk, rfl⟩

omit hB in
/-- The frequency partial sum, cut off to the band, is square-integrable. -/
private lemma memLp_freqBand (f : ℝ → ℂ) (s : Finset ℤ) :
    MemLp (freqBand B f s) 2 volume := by
  have hsupp : HasCompactSupport (freqBand B f s) := by
    refine HasCompactSupport.intro (K := Set.Icc (-B) B) isCompact_Icc ?_
    intro x hx
    simp [freqBand, bandCutoff, Set.indicator_of_notMem hx]
  have hmeas : AEStronglyMeasurable (freqBand B f s) volume :=
    (continuous_freqPartial f s).aestronglyMeasurable.indicator measurableSet_Icc
  refine hsupp.memLp_of_bound hmeas
    (∑ k ∈ s, ‖((2 * B)⁻¹ : ℝ) • f (k / (2 * B))‖) ?_
  filter_upwards with x
  rw [freqBand, bandCutoff]
  by_cases hx : x ∈ Set.Icc (-B) B
  · simp only [hx, Set.indicator_of_mem, freqPartial]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [norm_mul, norm_samplingCharacter k x, mul_one]
  · rw [Set.indicator_of_notMem hx, norm_zero]
    positivity

/-- `L²` norm of the frequency remainder tends to zero along finite sets. -/
private lemma tendsto_lpNorm_remainder (u : Lp ℂ 2 (volume : Measure ℝ)) :
    Tendsto (fun s : Finset ℤ =>
      lpNorm (bandCutoff B (⇑u) - freqBand B (bandlimitedRepresentative B u) s) 2 volume)
      atTop (𝓝 0) := by
  let c : ℤ → ℂ := fourierCoeffOn (band_lt hB) (⇑u)
  have hc : Summable fun i => ‖c i‖ ^ 2 :=
    (hasSum_sq_fourierCoeffOn (band_lt hB) (memLp_u_Ioc u)).summable
  have hsum : Tendsto (fun s : Finset ℤ => ∑ i ∈ s, ‖c i‖ ^ 2) atTop
      (𝓝 (∑' i, ‖c i‖ ^ 2)) := by
    simpa [HasSum, SummationFilter.unconditional_filter] using hc.hasSum
  have htail : Tendsto (fun s : Finset ℤ =>
      ∑' i, ‖c i‖ ^ 2 - ∑ i ∈ s.image Neg.neg, ‖c i‖ ^ 2) atTop (𝓝 0) := by
    have hconst : Tendsto (fun _ : Finset ℤ => ∑' i, ‖c i‖ ^ 2) atTop
        (𝓝 (∑' i, ‖c i‖ ^ 2)) := tendsto_const_nhds
    have hsub := hconst.sub (hsum.comp tendsto_image_neg)
    simp only [Function.comp_apply] at hsub
    simpa only [sub_self] using hsub
  have hnn : ∀ s : Finset ℤ,
      0 ≤ ∑' i, ‖c i‖ ^ 2 - ∑ i ∈ s.image Neg.neg, ‖c i‖ ^ 2 := by
    intro s
    have hle := hc.sum_le_tsum (s.image Neg.neg) (fun _ _ => sq_nonneg _)
    linarith
  have hsqrt : Tendsto (fun s : Finset ℤ =>
      Real.sqrt ((2 * B) * (∑' i, ‖c i‖ ^ 2 -
        ∑ i ∈ s.image Neg.neg, ‖c i‖ ^ 2))) atTop (𝓝 0) := by
    have hmul := htail.const_mul (2 * B)
    have hzero : Tendsto (fun s : Finset ℤ => (2 * B) * (∑' i, ‖c i‖ ^ 2 -
        ∑ i ∈ Finset.image Neg.neg s, ‖c i‖ ^ 2)) atTop (𝓝 0) := by
      simpa only [mul_zero] using hmul
    simpa [Function.comp_def, Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto 0).comp hzero
  have heq : (fun s : Finset ℤ =>
      lpNorm (bandCutoff B (⇑u) - freqBand B (bandlimitedRepresentative B u) s) 2 volume) =
      fun s => Real.sqrt ((2 * B) * (∑' i, ‖c i‖ ^ 2 -
        ∑ i ∈ s.image Neg.neg, ‖c i‖ ^ 2)) := by
    ext s
    have hmem : MemLp (bandCutoff B (⇑u) -
        freqBand B (bandlimitedRepresentative B u) s) 2 volume :=
      (memLp_bandCutoff u).sub (memLp_freqBand _ s)
    rw [lpNorm_eq_integral_norm_rpow_toReal (by simp) (by simp) hmem.aestronglyMeasurable]
    simp only [ENNReal.toReal_ofNat]
    simp_rw [Real.rpow_two]
    rw [integral_norm_sq_remainder hB u s]
    rw [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]
  rw [heq]
  exact hsqrt

/-- One sampling character, integrated against the inverse phase, is a normalized sinc. -/
private lemma integral_samplingCharacter (k : ℤ) (t : ℝ) :
    ∫ ξ in Set.Icc (-B) B,
        Complex.exp (2 * Real.pi * Complex.I * t * ξ) * samplingCharacter B k ξ =
      (2 * B : ℂ) * (normalizedSinc (2 * B * t - k) : ℂ) := by
  set alpha : ℝ := t - (k : ℝ) / (2 * B)
  have hphase : ∀ ξ : ℝ,
      Complex.exp (2 * Real.pi * Complex.I * t * ξ) * samplingCharacter B k ξ =
        Complex.exp (2 * Real.pi * Complex.I * alpha * ξ) := by
    intro ξ
    rw [samplingCharacter, ← Complex.exp_add]
    congr 1
    simp only [alpha]
    push_cast
    ring_nf
  rw [setIntegral_congr_fun measurableSet_Icc fun ξ _ => hphase ξ,
    integral_exp_band hB]
  congr 1
  have hB0 : (2 * B : ℝ) ≠ 0 := mul_ne_zero two_ne_zero (ne_of_gt hB)
  congr 1
  simp only [alpha]
  field_simp [hB0]

/-- One frequency term inverts to one Shannon summand. -/
private lemma integral_one_shannonTerm (u : Lp ℂ 2 (volume : Measure ℝ)) (k : ℤ) (t : ℝ) :
    ∫ ξ in Set.Icc (-B) B,
        Complex.exp (2 * Real.pi * Complex.I * t * ξ) *
          (((2 * B)⁻¹ : ℝ) • bandlimitedRepresentative B u (k / (2 * B)) *
            samplingCharacter B k ξ) =
      shannonTerm B (bandlimitedRepresentative B u) k t := by
  have hpull : ∀ ξ : ℝ,
      Complex.exp (2 * Real.pi * Complex.I * t * ξ) *
          (((2 * B)⁻¹ : ℝ) • bandlimitedRepresentative B u (k / (2 * B)) *
            samplingCharacter B k ξ) =
        (((2 * B)⁻¹ : ℝ) • bandlimitedRepresentative B u (k / (2 * B))) *
          (Complex.exp (2 * Real.pi * Complex.I * t * ξ) * samplingCharacter B k ξ) := by
    intro ξ
    rw [mul_left_comm]
  simp_rw [hpull]
  rw [integral_const_mul, integral_samplingCharacter hB k t, shannonTerm]
  rw [Algebra.smul_def, mul_assoc]
  push_cast
  have hB0 : (B : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hB
  field_simp [hB0]
  rw [mul_comm (bandlimitedRepresentative B u (k / (2 * B))) (B : ℂ)]
  rfl

/-- A Shannon partial sum is the inverse Fourier integral of the frequency partial sum. -/
private lemma shannonSum_eq_fourierInv (u : Lp ℂ 2 (volume : Measure ℝ))
    (s : Finset ℤ) (t : ℝ) :
    ∑ k ∈ s, shannonTerm B (bandlimitedRepresentative B u) k t =
      𝓕⁻ (freqBand B (bandlimitedRepresentative B u) s) t := by
  rw [Real.fourierInv_eq', freqBand, bandCutoff]
  simp_rw [Real.inner_apply, smul_eq_mul]
  have hmul : ∀ ξ : ℝ,
      Complex.exp (↑(2 * Real.pi * (ξ * t)) * Complex.I) *
          (Set.Icc (-B) B).indicator
            (freqPartial B (bandlimitedRepresentative B u) s) ξ =
        (Set.Icc (-B) B).indicator
          (fun ξ => Complex.exp (2 * Real.pi * Complex.I * t * ξ) *
            freqPartial B (bandlimitedRepresentative B u) s ξ) ξ := by
    intro ξ
    by_cases hξ : ξ ∈ Set.Icc (-B) B
    · simp only [hξ, Set.indicator_of_mem]
      congr 1
      simp only [Complex.ofReal_mul, Complex.ofReal_ofNat]
      ring
    · simp [hξ]
  simp_rw [hmul, integral_indicator measurableSet_Icc, freqPartial, Finset.mul_sum]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun k _ => ?_
    simpa [mul_assoc] using (integral_one_shannonTerm hB u k t).symm
  · intro k _
    exact ((Complex.continuous_exp.comp (by fun_prop)).mul
      ((continuous_const.mul (continuous_samplingCharacter k)))).integrableOn_Icc

omit hB in
/-- Inverse Fourier integrals preserve differences of integrable functions. -/
private lemma fourierInv_sub {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (t : ℝ) :
    𝓕⁻ (f - g) t = 𝓕⁻ f t - 𝓕⁻ g t := by
  rw [Real.fourierInv_eq, Real.fourierInv_eq, Real.fourierInv_eq]
  have hsub : (fun v => 𝐞 (inner ℝ v t) • (f - g) v) =
      (fun v => 𝐞 (inner ℝ v t) • f v) - fun v => 𝐞 (inner ℝ v t) • g v := by
    ext v
    simp [smul_sub, Pi.sub_apply]
  have hpoint : ((fun v => 𝐞 (inner ℝ v t) • f v) - fun v => 𝐞 (inner ℝ v t) • g v) =
      fun v => 𝐞 (inner ℝ v t) • f v - 𝐞 (inner ℝ v t) • g v := by
    ext v
    rfl
  rw [hsub, hpoint, integral_sub]
  · simpa [inner_neg_right, neg_neg] using (Real.fourierIntegral_convergent_iff (-t)).2 hf
  · simpa [inner_neg_right, neg_neg] using (Real.fourierIntegral_convergent_iff (-t)).2 hg

omit hB in
/-- Inner product on `ℝ` is symmetric, so negating it is invariant under flip. -/
private lemma neg_inner_flip : LinearMap.flip (-innerₗ ℝ) = -innerₗ ℝ := by
  ext
  simp [LinearMap.flip_apply, LinearMap.neg_apply]

omit hB in
/-- The integral inverse Fourier transform of an `L¹ ∩ L²` function agrees almost everywhere
with the `L²` inverse Fourier transform. -/
private lemma fourierInv_toLp_ae_eq {f : ℝ → ℂ} (hf1 : Integrable f) (hf2 : MemLp f 2 volume) :
    (⇑(𝓕⁻ (hf2.toLp f) : Lp ℂ 2 volume) : ℝ → ℂ) =ᵐ[volume] 𝓕⁻ f := by
  let F : Lp ℂ 2 volume := hf2.toLp f
  let G : Lp ℂ 2 volume := 𝓕⁻ F
  have hlocLp : LocallyIntegrable (⇑G) volume :=
    (Lp.memLp G).locallyIntegrable fact_one_le_two_ennreal.elim
  have hcontL : Continuous fun p : ℝ × ℝ => (innerₗ ℝ) p.1 p.2 :=
    continuous_snd.mul continuous_fst
  have hcontNeg : Continuous fun p : ℝ × ℝ => (-innerₗ ℝ) p.1 p.2 := by
    have hneg : (fun p : ℝ × ℝ => (-innerₗ ℝ) p.1 p.2) =
        fun p => -((innerₗ ℝ) p.1 p.2) := by
      ext p
      simp [LinearMap.neg_apply]
    rw [hneg]
    exact hcontL.neg
  have hcontF : Continuous (𝓕 f) :=
    VectorFourier.fourierIntegral_continuous (L := innerₗ ℝ)
      Real.continuous_fourierChar hcontL hf1
  have hlocInv : LocallyIntegrable (𝓕⁻ f) volume := by
    have heq : 𝓕⁻ f = fun w => 𝓕 f (-w) := by
      ext w
      exact Real.fourierInv_eq_fourier_neg f w
    rw [heq]
    exact (hcontF.comp continuous_neg).locallyIntegrable
  refine ae_eq_of_integral_contDiff_smul_eq hlocLp hlocInv ?_
  intro g hg_diff hg_supp
  let phiFun : ℝ → ℂ := fun x => (g x : ℂ)
  have hphiSupp : HasCompactSupport phiFun := hg_supp.comp_left Complex.ofReal_zero
  have hphiDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) phiFun :=
    (Complex.ofRealCLM.contDiff.of_le
      (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) le_top).comp hg_diff
  let phi : 𝓢(ℝ, ℂ) := hphiSupp.toSchwartzMap hphiDiff
  have hphiCoe : (phi : ℝ → ℂ) = phiFun := rfl
  have hsmul : ∀ x z, g x • z = phiFun x * z := by
    intro x z
    simp [phiFun, Algebra.smul_def]
  have hleft : ∫ x, g x • G x =
      ∫ x, phi x • G x := by
    refine integral_congr_ae ?_
    filter_upwards with x
    rw [hphiCoe, hsmul]
    simp [smul_eq_mul]
  have hright : ∫ x, g x • 𝓕⁻ f x = ∫ x, phiFun x * 𝓕⁻ f x := by
    refine integral_congr_ae ?_
    filter_upwards with x
    rw [hsmul]
  rw [hleft, hright]
  have hdist := congrArg (fun T : 𝓢'(ℝ, ℂ) => T phi)
    (Lp.fourierInv_toTemperedDistribution_eq F)
  simp only [TemperedDistribution.fourierInv_apply] at hdist
  rw [Lp.toTemperedDistribution_apply, Lp.toTemperedDistribution_apply] at hdist
  have hcoe : (⇑F : ℝ → ℂ) =ᵐ[volume] f := hf2.coeFn_toLp
  have hswap : ∫ x, (𝓕⁻ phi) x • F x =
      ∫ x, (𝓕⁻ (phi : ℝ → ℂ)) x * f x := by
    refine integral_congr_ae ?_
    filter_upwards [hcoe] with x hx
    rw [hx, SchwartzMap.fourierInv_coe, smul_eq_mul]
  rw [hswap] at hdist
  have hFub : ∫ x, (𝓕⁻ (phi : ℝ → ℂ)) x * f x =
      ∫ x, phiFun x * 𝓕⁻ f x := by
    have hphiInt : Integrable (phi : ℝ → ℂ) := phi.integrable
    have hadj := VectorFourier.integral_bilin_fourierIntegral_eq_flip
      (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
      (L := -innerₗ ℝ) (e := 𝐞)
      (ContinuousLinearMap.mul ℂ ℂ)
      Real.continuous_fourierChar hcontNeg hphiInt hf1
    simp only [ContinuousLinearMap.mul_apply', neg_inner_flip] at hadj
    have hFT : ∀ (g : ℝ → ℂ) (w : ℝ),
        VectorFourier.fourierIntegral 𝐞 volume (-innerₗ ℝ) g w = 𝓕⁻ g w := by
      intro g w
      rw [Real.fourierInv_eq, VectorFourier.fourierIntegral]
      refine integral_congr_ae (ae_of_all _ fun v => ?_)
      simp [LinearMap.neg_apply, innerₗ_apply_apply]
    simp_rw [hFT] at hadj
    simpa [hphiCoe] using hadj
  rw [← hdist, hFub]

omit hB in
/-- Plancherel: the integral inverse Fourier transform preserves the `L²` norm. -/
private lemma eLpNorm_fourierInv_eq {f : ℝ → ℂ} (hf1 : Integrable f) (hf2 : MemLp f 2 volume) :
    eLpNorm (𝓕⁻ f) 2 volume = eLpNorm f 2 volume := by
  let F : Lp ℂ 2 volume := hf2.toLp f
  let G : Lp ℂ 2 volume := 𝓕⁻ F
  have hF : ⇑F =ᵐ[volume] f := hf2.coeFn_toLp
  have hinv : ⇑G =ᵐ[volume] 𝓕⁻ f := fourierInv_toLp_ae_eq hf1 hf2
  have hnorm : ‖G‖ = ‖F‖ := by
    rw [← Lp.norm_fourier_eq G, fourier_fourierInv_eq]
  have henn : eLpNorm (⇑G) 2 volume = eLpNorm (⇑F) 2 volume := by
    have hreal : (eLpNorm (⇑G) 2 volume).toReal =
        (eLpNorm (⇑F) 2 volume).toReal := by
      simp_rw [← Lp.norm_def]
      exact hnorm
    exact (ENNReal.toReal_eq_toReal_iff' (Lp.memLp G).eLpNorm_ne_top
      (Lp.memLp F).eLpNorm_ne_top).1 hreal
  rw [← eLpNorm_congr_ae hinv, henn, eLpNorm_congr_ae hF]

/-- Cauchy–Schwarz on the band upgrades an `L²` remainder to a uniform bound. -/
private lemma norm_shannon_remainder_le (u : Lp ℂ 2 (volume : Measure ℝ))
    (s : Finset ℤ) (t : ℝ) :
    ‖(∑ k ∈ s, shannonTerm B (bandlimitedRepresentative B u) k t) -
        bandlimitedRepresentative B u t‖ ≤
      Real.sqrt (2 * B) *
        lpNorm (bandCutoff B (⇑u) - freqBand B (bandlimitedRepresentative B u) s) 2 volume := by
  let r : ℝ → ℂ := fun ξ =>
    freqPartial B (bandlimitedRepresentative B u) s ξ - u ξ
  have hint : (∑ k ∈ s, shannonTerm B (bandlimitedRepresentative B u) k t) -
      bandlimitedRepresentative B u t =
      ∫ ξ in Set.Icc (-B) B, Complex.exp (2 * Real.pi * Complex.I * t * ξ) * r ξ := by
    have hfBand : Integrable (freqBand B (bandlimitedRepresentative B u) s) := by
      unfold freqBand bandCutoff
      rw [integrable_indicator_iff measurableSet_Icc]
      exact (continuous_freqPartial (bandlimitedRepresentative B u) s).integrableOn_Icc
    have hgCut : Integrable (bandCutoff B (⇑u)) := integrable_bandCutoff u
    rw [shannonSum_eq_fourierInv hB, bandlimitedRepresentative_eq_fourierInv,
      ← fourierInv_sub hfBand hgCut t]
    rw [Real.fourierInv_eq', freqBand]
    unfold bandCutoff
    simp_rw [Real.inner_apply, smul_eq_mul]
    have hsub : ∀ ξ : ℝ,
        Complex.exp (↑(2 * Real.pi * (ξ * t)) * Complex.I) *
            ((Set.Icc (-B) B).indicator
                (freqPartial B (bandlimitedRepresentative B u) s) -
              (Set.Icc (-B) B).indicator (⇑u)) ξ =
          (Set.Icc (-B) B).indicator
            (fun ξ => Complex.exp (2 * Real.pi * Complex.I * t * ξ) * r ξ) ξ := by
      intro ξ
      by_cases hξ : ξ ∈ Set.Icc (-B) B
      · rw [Pi.sub_apply, Set.indicator_of_mem hξ, Set.indicator_of_mem hξ,
          Set.indicator_of_mem hξ]
        congr 1
        · simp only [Complex.ofReal_mul, Complex.ofReal_ofNat]
          ring
      · rw [Pi.sub_apply, Set.indicator_of_notMem hξ, Set.indicator_of_notMem hξ,
          Set.indicator_of_notMem hξ, sub_self, mul_zero]
    rw [integral_congr_ae (ae_of_all volume hsub), integral_indicator measurableSet_Icc]
  rw [hint]
  have hL1 : IntegrableOn r (Set.Icc (-B) B) := by
    have hu : IntegrableOn (⇑u) (Set.Icc (-B) B) := by
      rw [← intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith : -B ≤ B)]
      exact intervalIntegrable_u hB u
    exact ((continuous_freqPartial _ s).integrableOn_Icc).sub hu
  have hphase : IntegrableOn
      (fun ξ : ℝ => Complex.exp (2 * Real.pi * Complex.I * t * ξ) * r ξ)
      (Set.Icc (-B) B) := by
    refine hL1.bdd_mul (c := 1) ?_ ?_
    · exact (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable.mono_ac
        (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
    · filter_upwards with ξ
      simp [norm_phase]
  refine (norm_integral_le_integral_norm _).trans ?_
  have hnorm : ∫ ξ in Set.Icc (-B) B,
      ‖Complex.exp (2 * Real.pi * Complex.I * t * ξ) * r ξ‖ =
      ∫ ξ in Set.Icc (-B) B, ‖r ξ‖ := by
    refine setIntegral_congr_fun measurableSet_Icc fun ξ _ => ?_
    rw [norm_mul, norm_phase, one_mul]
  rw [hnorm]
  let μ : Measure ℝ := volume.restrict (Set.Icc (-B) B)
  have hr : MemLp r 2 μ := by
    have hu : MemLp (⇑u) 2 μ := (Lp.memLp u).restrict (Set.Icc (-B) B)
    have hp : MemLp (freqPartial B (bandlimitedRepresentative B u) s) 2 μ := by
      refine MemLp.of_bound
        ((continuous_freqPartial _ s).aestronglyMeasurable.mono_ac
          (Measure.absolutelyContinuous_of_le Measure.restrict_le_self))
        (∑ k ∈ s, ‖((2 * B)⁻¹ : ℝ) •
          bandlimitedRepresentative B u (k / (2 * B))‖) ?_
      filter_upwards with x
      unfold freqPartial
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
      rw [norm_mul, norm_samplingCharacter, mul_one]
    exact hp.sub hu
  have hone : MemLp (fun _ : ℝ => (1 : ℂ)) (ENNReal.ofReal 2) μ := by
    simpa [ENNReal.ofReal_ofNat] using (memLp_const (1 : ℂ) : MemLp (fun _ => (1 : ℂ)) 2 μ)
  have hr2 : MemLp r (ENNReal.ofReal 2) μ := by simpa [ENNReal.ofReal_ofNat] using hr
  have hholder := integral_mul_norm_le_Lp_mul_Lq (μ := μ)
    Real.HolderConjugate.two_two hr2 hone
  have honeInt : ∫ a, ‖(1 : ℂ)‖ ^ (2 : ℝ) ∂μ = 2 * B := by
    simp_rw [norm_one, Real.one_rpow]
    rw [integral_const]
    have hμ : μ.real Set.univ = 2 * B := by
      unfold μ
      rw [Measure.real, Measure.restrict_apply_univ]
      rw [show (volume (Set.Icc (-B) B)).toReal = B - (-B) by
        simpa [Measure.real] using
          Real.volume_real_Icc_of_le (by linarith : -B ≤ B)]
      ring
    rw [hμ, smul_eq_mul, mul_one]
  have hrInt : ∫ a, ‖r a‖ ^ (2 : ℝ) ∂μ =
      ∫ x, ‖(bandCutoff B (⇑u) - freqBand B (bandlimitedRepresentative B u) s) x‖ ^ 2 := by
    simp_rw [Real.rpow_two]
    rw [← integral_indicator measurableSet_Icc]
    refine integral_congr_ae ?_
    filter_upwards with x
    unfold freqBand
    unfold bandCutoff
    by_cases hx : x ∈ Set.Icc (-B) B
    · rw [Set.indicator_of_mem hx, Pi.sub_apply, Set.indicator_of_mem hx,
        Set.indicator_of_mem hx]
      simp [r, norm_sub_rev]
    · rw [Set.indicator_of_notMem hx, Pi.sub_apply, Set.indicator_of_notMem hx,
        Set.indicator_of_notMem hx, sub_self, norm_zero]
      norm_num
  have hleft : ∫ a, ‖r a‖ * ‖(1 : ℂ)‖ ∂μ = ∫ ξ in Set.Icc (-B) B, ‖r ξ‖ := by
    simp [μ, norm_one, mul_one]
  rw [hleft, honeInt, hrInt] at hholder
  have hlp : (∫ x, ‖(bandCutoff B (⇑u) -
        freqBand B (bandlimitedRepresentative B u) s) x‖ ^ 2) ^ (1 / 2 : ℝ) =
      lpNorm (bandCutoff B (⇑u) - freqBand B (bandlimitedRepresentative B u) s) 2 volume := by
    have hmem : MemLp (bandCutoff B (⇑u) -
        freqBand B (bandlimitedRepresentative B u) s) 2 volume :=
      (memLp_bandCutoff u).sub (memLp_freqBand _ s)
    rw [lpNorm_eq_integral_norm_rpow_toReal (by simp) (by simp) hmem.aestronglyMeasurable]
    simp only [ENNReal.toReal_ofNat]
    simp_rw [Real.rpow_two]
    rw [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num]
  have hsqrt : ((2 * B : ℝ) ^ (1 / 2 : ℝ)) = Real.sqrt (2 * B) := by
    rw [← Real.sqrt_eq_rpow]
  rw [hlp] at hholder
  rw [hsqrt, mul_comm] at hholder
  exact hholder

end Positive

/-- **29.58**: Shannon reconstruction for the integral representative, both pointwise and uniformly.
  -/
theorem shannon_sampling {B : ℝ} (hB : 0 < B)
    (u : Lp ℂ 2 (volume : Measure ℝ)) :
    (∀ t, HasSum (fun k : ℤ ↦ shannonTerm B (bandlimitedRepresentative B u) k t)
      (bandlimitedRepresentative B u t)) ∧
    TendstoUniformly
      (fun s : Finset ℤ ↦ fun t ↦ ∑ k ∈ s, shannonTerm B (bandlimitedRepresentative B u) k t)
      (bandlimitedRepresentative B u) atTop := by
  have hlp := tendsto_lpNorm_remainder hB u
  have hbound : ∀ s t,
      dist (∑ k ∈ s, shannonTerm B (bandlimitedRepresentative B u) k t)
        (bandlimitedRepresentative B u t) ≤
      Real.sqrt (2 * B) *
        lpNorm (bandCutoff B (⇑u) - freqBand B (bandlimitedRepresentative B u) s) 2 volume := by
    intro s t
    rw [dist_eq_norm]
    simpa [norm_sub_rev] using norm_shannon_remainder_le hB u s t
  have hzero : Tendsto (fun s : Finset ℤ =>
      Real.sqrt (2 * B) *
        lpNorm (bandCutoff B (⇑u) - freqBand B (bandlimitedRepresentative B u) s) 2 volume)
      atTop (𝓝 0) := by
    simpa using hlp.const_mul (Real.sqrt (2 * B))
  refine ⟨fun t => ?_, ?_⟩
  · rw [HasSum, SummationFilter.unconditional_filter]
    refine Metric.tendsto_atTop.2 fun ε hε => ?_
    have hε' := (tendsto_order.1 hzero).2 ε hε
    rw [Filter.eventually_atTop] at hε'
    rcases hε' with ⟨N, hN⟩
    exact ⟨N, fun s hs => (hbound s t).trans_lt (hN s hs)⟩
  · rw [Metric.tendstoUniformly_iff]
    intro ε hε
    have hε' := (tendsto_order.1 hzero).2 ε hε
    filter_upwards [hε'] with s hs t
    rw [dist_comm]
    exact (hbound s t).trans_lt hs

/-- The same sampling sums converge in `L²`. -/
theorem shannon_sampling_L2 {B : ℝ} (hB : 0 < B)
    (u : Lp ℂ 2 (volume : Measure ℝ)) :
    Tendsto (fun s : Finset ℤ ↦ eLpNorm
      (fun t ↦ (∑ k ∈ s, shannonTerm B (bandlimitedRepresentative B u) k t) -
        bandlimitedRepresentative B u t) 2 volume) atTop (𝓝 0) := by
  have hintFreq : ∀ s : Finset ℤ,
      Integrable (freqBand B (bandlimitedRepresentative B u) s) := by
    intro s
    unfold freqBand bandCutoff
    rw [integrable_indicator_iff measurableSet_Icc]
    exact (continuous_freqPartial (bandlimitedRepresentative B u) s).integrableOn_Icc
  have hintCut : Integrable (bandCutoff B (⇑u)) := integrable_bandCutoff u
  have hpoint : ∀ s t,
      (∑ k ∈ s, shannonTerm B (bandlimitedRepresentative B u) k t) -
        bandlimitedRepresentative B u t =
      𝓕⁻ (freqBand B (bandlimitedRepresentative B u) s - bandCutoff B (⇑u)) t := by
    intro s t
    rw [shannonSum_eq_fourierInv hB, bandlimitedRepresentative_eq_fourierInv,
      ← fourierInv_sub (hintFreq s) hintCut]
  have hnorm : ∀ s, eLpNorm
      (fun t => (∑ k ∈ s, shannonTerm B (bandlimitedRepresentative B u) k t) -
        bandlimitedRepresentative B u t) 2 volume =
      eLpNorm (freqBand B (bandlimitedRepresentative B u) s - bandCutoff B (⇑u)) 2 volume := by
    intro s
    have hf1 : Integrable (freqBand B (bandlimitedRepresentative B u) s -
        bandCutoff B (⇑u)) := (hintFreq s).sub hintCut
    have hf2 : MemLp (freqBand B (bandlimitedRepresentative B u) s -
        bandCutoff B (⇑u)) 2 :=
      (memLp_freqBand _ s).sub (memLp_bandCutoff u)
    rw [show (fun t => (∑ k ∈ s, shannonTerm B (bandlimitedRepresentative B u) k t) -
          bandlimitedRepresentative B u t) =
        𝓕⁻ (freqBand B (bandlimitedRepresentative B u) s - bandCutoff B (⇑u)) by
      ext t
      exact hpoint s t, eLpNorm_fourierInv_eq hf1 hf2]
  have htail := tendsto_lpNorm_remainder hB u
  have hmem : ∀ s, MemLp (freqBand B (bandlimitedRepresentative B u) s - bandCutoff B (⇑u)) 2 :=
    fun s => (memLp_freqBand _ s).sub (memLp_bandCutoff u)
  have hreal : Tendsto (fun s =>
      lpNorm (freqBand B (bandlimitedRepresentative B u) s - bandCutoff B (⇑u)) 2 volume)
      atTop (𝓝 0) := by
    have heq : (fun s =>
        lpNorm (freqBand B (bandlimitedRepresentative B u) s - bandCutoff B (⇑u)) 2 volume) =
        fun s => lpNorm (bandCutoff B (⇑u) -
          freqBand B (bandlimitedRepresentative B u) s) 2 volume := by
      ext s
      rw [lpNorm_sub_comm]
    rw [heq]
    exact htail
  have henn : Tendsto (fun s =>
      eLpNorm (freqBand B (bandlimitedRepresentative B u) s - bandCutoff B (⇑u)) 2 volume)
      atTop (𝓝 0) := by
    have heq : (fun s =>
        eLpNorm (freqBand B (bandlimitedRepresentative B u) s - bandCutoff B (⇑u)) 2 volume) =
        fun s => ENNReal.ofReal
          (lpNorm (freqBand B (bandlimitedRepresentative B u) s - bandCutoff B (⇑u)) 2 volume) := by
      ext s
      exact (ofReal_lpNorm (hmem s)).symm
    rw [heq, ← ENNReal.ofReal_zero]
    exact (ENNReal.continuous_ofReal.tendsto 0).comp hreal
  exact henn.congr fun s => (hnorm s).symm

/-- Exact sampling Parseval identity. -/
theorem shannon_norm_identity {B : ℝ} (hB : 0 < B)
    (u : Lp ℂ 2 (volume : Measure ℝ)) :
    (∫⁻ t, ENNReal.ofReal (‖bandlimitedRepresentative B u t‖ ^ 2)) =
      ENNReal.ofReal ((2 * B)⁻¹) * ∑' k : ℤ,
        ENNReal.ofReal (‖bandlimitedRepresentative B u (k / (2 * B))‖ ^ 2) := by
  let c : ℤ → ℂ := fourierCoeffOn (band_lt hB) (⇑u)
  have hc : Summable fun i => ‖c i‖ ^ 2 :=
    (hasSum_sq_fourierCoeffOn (band_lt hB) (memLp_u_Ioc u)).summable
  have hparse : ∑' i, ‖c i‖ ^ 2 =
      (2 * B)⁻¹ * ∫ x, ‖bandCutoff B (⇑u) x‖ ^ 2 := by
    have hts := tsum_sq_fourierCoeffOn (band_lt hB) (memLp_u_Ioc u)
    have hscalar : (((-B + 2 * B) - (-B))⁻¹ : ℝ) = (2 * B)⁻¹ := by
      rw [band_period]
    rw [hscalar, smul_eq_mul] at hts
    have hint : ∫ x in -B..(-B + 2 * B), ‖u x‖ ^ 2 =
        ∫ x, ‖bandCutoff B (⇑u) x‖ ^ 2 := by
      rw [band_right]
      rw [intervalIntegral.integral_of_le (by linarith : -B ≤ B)]
      rw [setIntegral_congr_set
        (MeasureTheory.Ioc_ae_eq_Icc' (by simp : volume {(-B)} = 0))]
      rw [← integral_indicator measurableSet_Icc]
      refine integral_congr_ae ?_
      filter_upwards with x
      rw [bandCutoff]
      exact (norm_sq_indicator _ _ _).symm
    rw [hint] at hts
    exact hts
  have hcoeff : ∀ k : ℤ, ‖bandlimitedRepresentative B u (k / (2 * B))‖ ^ 2 =
      (2 * B) ^ 2 * ‖c (-k)‖ ^ 2 := by
    intro k
    have hc' : c (-k) = ((2 * B)⁻¹ : ℝ) • bandlimitedRepresentative B u (k / (2 * B)) :=
      fourierCoeffOn_neg_eq_sample hB u k
    have hrec : bandlimitedRepresentative B u (k / (2 * B)) = (2 * B : ℝ) • c (-k) := by
      rw [hc', smul_smul, mul_inv_cancel₀ (mul_ne_zero two_ne_zero (ne_of_gt hB)), one_smul]
    rw [hrec, norm_smul, Real.norm_eq_abs, abs_of_pos (mul_pos two_pos hB)]
    ring
  have hsumm : Summable fun k : ℤ => ‖bandlimitedRepresentative B u (k / (2 * B))‖ ^ 2 := by
    have hre : Summable fun k : ℤ => ‖c (-k)‖ ^ 2 := hc.comp_injective neg_injective
    exact (summable_congr fun k => (hcoeff k).symm).mp (hre.mul_left ((2 * B) ^ 2))
  have htsum : ∑' k : ℤ, ‖bandlimitedRepresentative B u (k / (2 * B))‖ ^ 2 =
      (2 * B) * ∫ x, ‖bandCutoff B (⇑u) x‖ ^ 2 := by
    have hfun : (fun k : ℤ => ‖bandlimitedRepresentative B u (k / (2 * B))‖ ^ 2) =
        fun k => (2 * B) ^ 2 * ‖c (-k)‖ ^ 2 := by
      ext k
      exact hcoeff k
    rw [hfun, tsum_mul_left]
    have hneg : ∑' x : ℤ, ‖c (-x)‖ ^ 2 = ∑' i, ‖c i‖ ^ 2 :=
      (Equiv.neg ℤ).tsum_eq (fun i => ‖c i‖ ^ 2)
    rw [hneg, hparse]
    have hB0 : (2 * B : ℝ) ≠ 0 := mul_ne_zero two_ne_zero (ne_of_gt hB)
    field_simp [hB0]
  have hf1 : Integrable (bandCutoff B (⇑u)) := integrable_bandCutoff u
  have hf2 : MemLp (bandCutoff B (⇑u)) 2 := memLp_bandCutoff u
  have hplan : ∫ t, ‖bandlimitedRepresentative B u t‖ ^ 2 =
      ∫ x, ‖bandCutoff B (⇑u) x‖ ^ 2 := by
    have hrep : bandlimitedRepresentative B u = 𝓕⁻ (bandCutoff B (⇑u)) := by
      ext t
      exact bandlimitedRepresentative_eq_fourierInv u t
    have hmemRep : MemLp (bandlimitedRepresentative B u) 2 volume := by
      change eLpNorm (bandlimitedRepresentative B u) 2 volume < ⊤
      rw [hrep, eLpNorm_fourierInv_eq hf1 hf2]
      exact hf2
    have hlpRep := lpNorm_eq_integral_norm_rpow_toReal (p := 2) (by simp) (by simp)
      hmemRep.aestronglyMeasurable
    have hlpCut := lpNorm_eq_integral_norm_rpow_toReal (p := 2) (by simp) (by simp)
      hf2.aestronglyMeasurable
    simp only [ENNReal.toReal_ofNat] at hlpRep hlpCut
    simp_rw [Real.rpow_two] at hlpRep hlpCut
    have hsame : lpNorm (bandlimitedRepresentative B u) 2 volume =
        lpNorm (bandCutoff B (⇑u)) 2 volume := by
      rw [hrep, lpNorm, lpNorm, eLpNorm_fourierInv_eq hf1 hf2]
    have hsq : (∫ t, ‖bandlimitedRepresentative B u t‖ ^ 2) ^ (2 : ℝ)⁻¹ =
        (∫ x, ‖bandCutoff B (⇑u) x‖ ^ 2) ^ (2 : ℝ)⁻¹ := by
      rw [← hlpRep, ← hlpCut, hsame]
    have hnn1 : 0 ≤ ∫ t, ‖bandlimitedRepresentative B u t‖ ^ 2 :=
      integral_nonneg fun _ => sq_nonneg _
    have hnn2 : 0 ≤ ∫ x, ‖bandCutoff B (⇑u) x‖ ^ 2 :=
      integral_nonneg fun _ => sq_nonneg _
    rw [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num] at hsq
    have hsqrt : Real.sqrt (∫ t, ‖bandlimitedRepresentative B u t‖ ^ 2) =
        Real.sqrt (∫ x, ‖bandCutoff B (⇑u) x‖ ^ 2) := by
      simpa [Real.sqrt_eq_rpow] using hsq
    exact (Real.sqrt_inj hnn1 hnn2).mp hsqrt
  have hreal : ∫ t, ‖bandlimitedRepresentative B u t‖ ^ 2 =
      (2 * B)⁻¹ * ∑' k : ℤ, ‖bandlimitedRepresentative B u (k / (2 * B))‖ ^ 2 := by
    rw [hplan, htsum]
    have hB0 : (2 * B : ℝ) ≠ 0 := mul_ne_zero two_ne_zero (ne_of_gt hB)
    field_simp [hB0]
  have hint : Integrable fun t => ‖bandlimitedRepresentative B u t‖ ^ 2 := by
    have hmem : MemLp (bandlimitedRepresentative B u) 2 volume := by
      have hfun : bandlimitedRepresentative B u = 𝓕⁻ (bandCutoff B (⇑u)) := by
        ext t
        exact bandlimitedRepresentative_eq_fourierInv u t
      change eLpNorm (bandlimitedRepresentative B u) 2 volume < ⊤
      rw [hfun, eLpNorm_fourierInv_eq hf1 hf2]
      exact hf2
    simpa [ENNReal.toReal_ofNat, Real.rpow_two] using
      hmem.integrable_norm_rpow (p := 2) (by simp) (by simp)
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun _ => sq_nonneg _)]
  rw [hreal, ENNReal.ofReal_mul (inv_nonneg.mpr (mul_nonneg two_pos.le hB.le)),
    ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) hsumm]

end CKMA
