/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Probability.InfinitelyDivisible.Basic
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Integrand of a Lévy characteristic exponent

The Lévy–Khintchine integrand is bounded by a multiple of `1 ∧ x²`, hence integrable for every
Lévy measure. The resulting exponent is continuous, vanishes at zero, is compatible with
conjugation, and scales by `1 / n` under division of the triplet by `n`.
-/

@[expose] public section

noncomputable section

namespace CKMA

open MeasureTheory Complex intervalIntegral Set
open scoped BigOperators NNReal ENNReal Real

/-- The Lévy–Khintchine integrand at frequency `t` and jump size `x`. -/
def levyIntegrand (t x : ℝ) : ℂ :=
  exp (I * t * x) - 1 - (if |x| ≤ 1 then I * t * x else 0)

/-- The exponent is the Gaussian part plus the integral of `levyIntegrand`. -/
lemma LevyTriplet.exponent_eq_levyIntegrand (L : LevyTriplet) (t : ℝ) :
    L.exponent t =
      I * L.drift * t - (L.gaussianVariance : ℂ) * (t : ℂ) ^ 2 / 2 +
        ∫ x, levyIntegrand t x ∂L.jumpMeasure :=
  rfl

/-- The imaginary exponential along the segment from `0` to `s` stays within `|y| * s` of `1`. -/
lemma norm_exp_segment_sub_one_le (y s : ℝ) (hs : 0 ≤ s) :
    ‖exp (I * y * s) - 1‖ ≤ |y| * s := by
  set c : ℂ := I * y
  set f : ℝ → ℂ := fun u => exp (c * u)
  have hfder : ∀ u, HasDerivAt f (f u * c) u := by
    intro u
    have hlin : HasDerivAt (fun v : ℝ => c * (v : ℂ)) c u := by
      simpa [mul_comm] using (ofRealCLM.hasDerivAt (x := u)).const_mul c
    simpa [f, mul_comm] using hlin.cexp
  have hfcont : Continuous f := by
    unfold f
    fun_prop
  have hint : IntervalIntegrable (fun u => f u * c) volume 0 s :=
    (hfcont.mul continuous_const).intervalIntegrable 0 s
  have hFTC : ∫ u in (0 : ℝ)..s, f u * c = f s - f 0 :=
    integral_eq_sub_of_hasDerivAt (fun u _ => hfder u) hint
  have hf0 : f 0 = 1 := by simp [f]
  have hgoal : ‖f s - 1‖ ≤ |y| * s := by
    rw [← hf0, ← hFTC]
    calc
      ‖∫ u in (0 : ℝ)..s, f u * c‖ ≤ ∫ u in (0 : ℝ)..s, ‖f u * c‖ :=
        norm_integral_le_integral_norm (μ := volume) hs
      _ = ∫ u in (0 : ℝ)..s, |y| := by
        refine intervalIntegral.integral_congr (fun u _ => ?_)
        rw [norm_mul]
        have hnorm : ‖f u‖ = 1 := by
          rw [norm_exp]
          simp [c, mul_assoc]
        rw [hnorm, one_mul]
        simp [c, norm_I, norm_real, Real.norm_eq_abs]
      _ = |y| * s := by
        rw [intervalIntegral.integral_const]
        simp only [sub_zero]
        ring
  simpa [f, c, mul_assoc] using hgoal

/-- The second-order remainder of `exp (I y)` is at most `y² / 2`. -/
lemma norm_exp_I_sub_one_sub_I_le (y : ℝ) :
    ‖exp (I * y) - 1 - I * y‖ ≤ y ^ 2 / 2 := by
  set c : ℂ := I * y
  set f : ℝ → ℂ := fun s => exp (c * s)
  have hfder : ∀ s, HasDerivAt f (f s * c) s := by
    intro s
    have hlin : HasDerivAt (fun u : ℝ => c * (u : ℂ)) c s := by
      simpa [mul_comm] using (ofRealCLM.hasDerivAt (x := s)).const_mul c
    simpa [f, mul_comm] using hlin.cexp
  have hfcont : Continuous f := by
    unfold f
    fun_prop
  have hint : IntervalIntegrable (fun s => f s * c) volume 0 1 :=
    (hfcont.mul continuous_const).intervalIntegrable 0 1
  have hintc : IntervalIntegrable (fun _ : ℝ => c) volume 0 1 :=
    continuous_const.intervalIntegrable 0 1
  have hFTC : ∫ s in (0 : ℝ)..1, f s * c = f 1 - f 0 :=
    integral_eq_sub_of_hasDerivAt (fun s _ => hfder s) hint
  have hf0 : f 0 = 1 := by simp [f]
  have hf1 : f 1 = exp c := by simp [f]
  have hrest : exp c - 1 - c = ∫ s in (0 : ℝ)..1, (f s - 1) * c := by
    have hsub : (fun s => (f s - 1) * c) = fun s => f s * c - c := by
      ext s
      ring
    rw [hsub, integral_sub hint hintc, hFTC, hf0, hf1, intervalIntegral.integral_const]
    simp
  rw [hrest]
  have hle : ‖∫ s in (0 : ℝ)..1, (f s - 1) * c‖ ≤ ∫ s in (0 : ℝ)..1, y ^ 2 * s := by
    refine norm_integral_le_of_norm_le (μ := volume) (a := 0) (b := 1) (by norm_num)
      (ae_of_all _ fun s hs => ?_) ?_
    · have hs0 : 0 ≤ s := le_of_lt hs.1
      have hseg : ‖f s - 1‖ ≤ |y| * s := by
        simpa [f, c, mul_assoc] using norm_exp_segment_sub_one_le y s hs0
      calc
        ‖(f s - 1) * c‖ = ‖f s - 1‖ * ‖c‖ := norm_mul _ _
        _ ≤ (|y| * s) * |y| := by
          gcongr
          simp [c, norm_I, norm_real, Real.norm_eq_abs]
        _ = y ^ 2 * s := by
          rw [mul_assoc, mul_comm s |y|, ← mul_assoc, ← sq_abs]
          ring
    · exact (continuous_const.mul continuous_id').intervalIntegrable 0 1
  refine hle.trans_eq ?_
  have hid : ∫ s in (0 : ℝ)..1, s = (1 / 2 : ℝ) := by
    have hder : ∀ u ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun s : ℝ => s ^ 2 / 2) u u := by
      intro u _
      have hpow : HasDerivAt (fun s : ℝ => s ^ 2) (2 * u) u := by
        simpa [Nat.cast_ofNat, pow_one] using hasDerivAt_pow 2 u
      have hdiv := hpow.div_const (2 : ℝ)
      simpa [sq, mul_comm, mul_left_comm, mul_assoc] using hdiv
    have hint_id : IntervalIntegrable (fun s : ℝ => s) volume 0 1 :=
      continuous_id'.intervalIntegrable 0 1
    have hFTC' : ∫ s in (0 : ℝ)..1, s = (fun s : ℝ => s ^ 2 / 2) 1 -
        (fun s : ℝ => s ^ 2 / 2) 0 :=
      integral_eq_sub_of_hasDerivAt hder hint_id
    simp [hFTC']
  rw [intervalIntegral.integral_const_mul, hid]
  ring

/-- `levyIntegrand` is Borel measurable in the jump variable. -/
lemma measurable_levyIntegrand (t : ℝ) : Measurable (levyIntegrand t) := by
  have hset : MeasurableSet {x : ℝ | |x| ≤ 1} :=
    (isClosed_le continuous_norm continuous_const).measurableSet
  unfold levyIntegrand
  refine Measurable.sub (Measurable.sub (by fun_prop) measurable_const) ?_
  exact Measurable.ite hset (by fun_prop) measurable_const

/-- Pointwise quadratic bound for the Lévy integrand. -/
lemma norm_levyIntegrand_le (t x : ℝ) :
    ‖levyIntegrand t x‖ ≤ (t ^ 2 / 2 + 2) * min 1 (x ^ 2) := by
  by_cases hx : |x| ≤ 1
  · have hI : (I * t * x : ℂ) = I * (t * x) := by ring
    rw [levyIntegrand, ite_eq_left hx, hI]
    have hy := norm_exp_I_sub_one_sub_I_le (t * x)
    rw [ofReal_mul] at hy
    have hxsq : x ^ 2 ≤ 1 := by
      rw [← sq_abs]
      exact pow_le_one₀ (abs_nonneg x) hx
    calc
      ‖exp (I * (t * x)) - 1 - I * (t * x)‖ ≤ (t * x) ^ 2 / 2 := hy
      _ = t ^ 2 * x ^ 2 / 2 := by ring
      _ ≤ (t ^ 2 / 2 + 2) * x ^ 2 := by
        have hnn : 0 ≤ x ^ 2 := sq_nonneg x
        nlinarith [sq_nonneg t]
      _ = (t ^ 2 / 2 + 2) * min 1 (x ^ 2) := by rw [min_eq_right hxsq]
  · rw [levyIntegrand, ite_eq_right hx, sub_zero]
    have hxlt : 1 < |x| := lt_of_not_ge hx
    have hxsq : 1 < x ^ 2 := by
      rw [← sq_abs]
      exact one_lt_pow₀ hxlt (by norm_num)
    have hmin : min 1 (x ^ 2) = 1 := min_eq_left hxsq.le
    have hnorm : ‖exp (I * t * x)‖ = 1 := by
      rw [norm_exp]
      simp [mul_assoc]
    calc
      ‖exp (I * t * x) - 1‖ ≤ ‖exp (I * t * x)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [hnorm, norm_one]; norm_num
      _ ≤ (t ^ 2 / 2 + 2) * min 1 (x ^ 2) := by
        rw [hmin]
        have : 0 ≤ t ^ 2 / 2 := by positivity
        linarith

/-- The truncated quadratic weight is integrable for a Lévy measure. -/
lemma integrable_min_one_sq {ν : Measure ℝ} (hν : IsLevyMeasure ν) :
    Integrable (fun x : ℝ => min 1 (x ^ 2)) ν := by
  have hcont : Continuous (fun x : ℝ => min 1 (x ^ 2)) := by fun_prop
  refine (lintegral_ofReal_ne_top_iff_integrable hcont.aestronglyMeasurable ?_).1 hν.2.ne
  exact ae_of_all _ fun x => le_min (by norm_num) (sq_nonneg x)

/-- The Lévy integrand is Bochner integrable against a Lévy measure. -/
lemma integrable_levyIntegrand {ν : Measure ℝ} (hν : IsLevyMeasure ν) (t : ℝ) :
    Integrable (levyIntegrand t) ν := by
  have hdom : Integrable (fun x : ℝ => (t ^ 2 / 2 + 2) * min 1 (x ^ 2)) ν :=
    (integrable_min_one_sq hν).const_mul (t ^ 2 / 2 + 2)
  refine hdom.mono (measurable_levyIntegrand t).aestronglyMeasurable ?_
  refine ae_of_all _ fun x => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) (le_min (by norm_num)
    (sq_nonneg x)))]
  exact norm_levyIntegrand_le t x

/-- The set `{|x| ≥ ε}` is Borel. -/
lemma measurableSet_abs_ge (ε : ℝ) : MeasurableSet {x : ℝ | ε ≤ |x|} :=
  (isClosed_le continuous_const continuous_norm).measurableSet

/-- A Lévy measure gives finite mass to `{|x| ≥ ε}`. -/
lemma IsLevyMeasure.measure_abs_ge_lt_top {ν : Measure ℝ} (hν : IsLevyMeasure ν) {ε : ℝ}
    (hε : 0 < ε) : ν {x | ε ≤ |x|} < ∞ := by
  set s := {x : ℝ | ε ≤ |x|}
  have hs : MeasurableSet s := measurableSet_abs_ge ε
  have hpos : 0 < min (1 : ℝ) (ε ^ 2) := lt_min (by norm_num) (by positivity)
  have hcoe : ENNReal.ofReal (min 1 (ε ^ 2)) ≠ 0 := ne_of_gt ((ENNReal.ofReal_pos).2 hpos)
  have hle : ENNReal.ofReal (min 1 (ε ^ 2)) * ν s ≤
      ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂ν := by
    calc
      ENNReal.ofReal (min 1 (ε ^ 2)) * ν s
          = ∫⁻ _ in s, ENNReal.ofReal (min 1 (ε ^ 2)) ∂ν := by
            rw [setLIntegral_const]
      _ ≤ ∫⁻ x in s, ENNReal.ofReal (min 1 (x ^ 2)) ∂ν := by
            refine setLIntegral_mono' hs fun x hx => ?_
            exact ENNReal.ofReal_le_ofReal <| min_le_min le_rfl <| by
              have hxε : ε ≤ |x| := hx
              nlinarith [sq_abs x]
      _ ≤ ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂ν := setLIntegral_le_lintegral _ _
  have hfin : ENNReal.ofReal (min 1 (ε ^ 2)) * ν s < ∞ := hle.trans_lt hν.2
  by_contra htop
  have hs_top : ν s = ∞ := le_antisymm le_top (not_lt.mp htop)
  rw [hs_top, ENNReal.mul_top hcoe] at hfin
  exact (lt_irrefl _) hfin

/-- Restriction of a Lévy measure away from zero is a Lévy measure. -/
lemma IsLevyMeasure.restrict_abs_ge {ν : Measure ℝ} (hν : IsLevyMeasure ν) {ε : ℝ}
    (hε : 0 < ε) : IsLevyMeasure (ν.restrict {x | ε ≤ |x|}) := by
  refine ⟨?_, ?_⟩
  · rw [Measure.restrict_apply (measurableSet_singleton _)]
    have hempty : {x : ℝ | ε ≤ |x|} ∩ {(0 : ℝ)} = ∅ := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false,
        Set.mem_ofPred_eq, iff_false, not_and]
      intro hx h0
      subst h0
      simp [abs_zero] at hx
      linarith
    rw [Set.inter_comm, hempty, measure_empty]
  · exact (setLIntegral_le_lintegral _ _).trans_lt hν.2

/-- Restriction of a Lévy measure to `{|x| ≥ ε}` is a finite measure. -/
lemma isFiniteMeasure_restrict_abs_ge {ν : Measure ℝ} (hν : IsLevyMeasure ν) {ε : ℝ}
    (hε : 0 < ε) : IsFiniteMeasure (ν.restrict {x | ε ≤ |x|}) := by
  refine ⟨?_⟩
  rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
  exact hν.measure_abs_ge_lt_top hε

/-- The Lévy integrand vanishes at frequency zero. -/
lemma levyIntegrand_zero (x : ℝ) : levyIntegrand 0 x = 0 := by
  simp [levyIntegrand, exp_zero]

/-- A Lévy exponent vanishes at frequency zero. -/
lemma LevyTriplet.exponent_zero (L : LevyTriplet) : L.exponent 0 = 0 := by
  rw [exponent_eq_levyIntegrand, integral_congr_ae <| ae_of_all _ levyIntegrand_zero,
    integral_zero]
  simp

/-- The map `t ↦ levyIntegrand t x` is continuous for each fixed jump. -/
lemma continuous_levyIntegrand (x : ℝ) : Continuous fun t : ℝ => levyIntegrand t x := by
  by_cases hx : |x| ≤ 1
  · simpa [levyIntegrand, hx] using
      (by fun_prop : Continuous fun t : ℝ => exp (I * t * x) - 1 - I * t * x)
  · simpa [levyIntegrand, hx] using
      (by fun_prop : Continuous fun t : ℝ => exp (I * t * x) - 1 - (0 : ℂ))

/-- The integral of the Lévy integrand depends continuously on the frequency. -/
lemma continuous_integral_levyIntegrand {ν : Measure ℝ} (hν : IsLevyMeasure ν) :
    Continuous fun t : ℝ => ∫ x, levyIntegrand t x ∂ν := by
  rw [continuous_iff_continuousAt]
  intro t0
  let C : ℝ := (|t0| + 1) ^ 2 / 2 + 2
  let bound : ℝ → ℝ := fun x => C * min 1 (x ^ 2)
  have hbound_int : Integrable bound ν := (integrable_min_one_sq hν).const_mul C
  refine continuousAt_of_dominated (bound := bound) ?meas ?hb hbound_int ?hcont
  · filter_upwards [Metric.ball_mem_nhds t0 (by norm_num : (0 : ℝ) < 1)] with t _
    exact (measurable_levyIntegrand t).aestronglyMeasurable
  · filter_upwards [Metric.ball_mem_nhds t0 (by norm_num : (0 : ℝ) < 1)] with t ht
    refine ae_of_all _ fun x => ?_
    have habs : |t - t0| < 1 := by simpa [Real.dist_eq] using ht
    have htle : |t| ≤ |t0| + 1 := by
      have htri : |t| ≤ |t - t0| + |t0| := by
        simpa [sub_add_cancel, Real.norm_eq_abs] using norm_add_le (t - t0) t0
      linarith
    have hsq : t ^ 2 / 2 + 2 ≤ C := by
      have hpow : |t| ^ 2 ≤ (|t0| + 1) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) htle 2
      have : t ^ 2 ≤ (|t0| + 1) ^ 2 := by simpa [sq_abs] using hpow
      unfold C
      linarith
    calc
      ‖levyIntegrand t x‖ ≤ (t ^ 2 / 2 + 2) * min 1 (x ^ 2) := norm_levyIntegrand_le t x
      _ ≤ C * min 1 (x ^ 2) := by
        gcongr
  · exact ae_of_all _ fun x => (continuous_levyIntegrand x).continuousAt

/-- A Lévy exponent is a continuous function of the frequency. -/
lemma LevyTriplet.continuous_exponent (L : LevyTriplet) : Continuous L.exponent := by
  have hgauss : Continuous fun t : ℝ =>
      I * L.drift * t - (L.gaussianVariance : ℂ) * (t : ℂ) ^ 2 / 2 := by
    fun_prop
  change Continuous fun t : ℝ =>
    I * L.drift * t - (L.gaussianVariance : ℂ) * (t : ℂ) ^ 2 / 2 +
      ∫ x, levyIntegrand t x ∂L.jumpMeasure
  exact hgauss.add (continuous_integral_levyIntegrand L.isLevyMeasure)

/-- Conjugation sends the Lévy integrand at frequency `t` to the integrand at `-t`. -/
lemma conj_levyIntegrand (t x : ℝ) :
    starRingEnd ℂ (levyIntegrand t x) = levyIntegrand (-t) x := by
  have hexp : starRingEnd ℂ (exp (I * t * x)) = exp (I * (-t) * x) := by
    rw [← exp_conj]
    congr 1
    simp only [map_mul, conj_I, conj_ofReal]
    ring
  have hlin : starRingEnd ℂ (if |x| ≤ 1 then I * t * x else 0) =
      if |x| ≤ 1 then I * (-t) * x else 0 := by
    by_cases hx : |x| ≤ 1
    · rw [ite_eq_left hx, ite_eq_left hx]
      simp only [map_mul, conj_I, conj_ofReal]
      ring
    · rw [ite_eq_right hx, ite_eq_right hx, map_zero]
  simp only [levyIntegrand, map_sub, map_one, hexp, hlin, ofReal_neg]

/-- The exponent at `-t` is the conjugate of the exponent at `t`. -/
lemma LevyTriplet.exponent_neg (L : LevyTriplet) (t : ℝ) :
    L.exponent (-t) = starRingEnd ℂ (L.exponent t) := by
  have hint : Integrable (levyIntegrand t) L.jumpMeasure :=
    integrable_levyIntegrand L.isLevyMeasure t
  rw [exponent_eq_levyIntegrand, exponent_eq_levyIntegrand, map_add, map_sub, ← integral_conj]
  refine congr_arg₂ HAdd.hAdd ?_ ?_
  · refine congr_arg₂ HSub.hSub ?_ ?_
    · simp [map_mul, conj_ofReal, conj_I, mul_left_comm, mul_comm]
    · simp [map_mul, map_div₀, map_pow, conj_ofReal, conj_ofNat]
  · exact integral_congr_ae <| ae_of_all _ fun x => (conj_levyIntegrand t x).symm

/-- Scaling a Lévy measure by the reciprocal of a positive integer preserves the Lévy condition. -/
lemma isLevyMeasure_inv_nsmul {ν : Measure ℝ} (hν : IsLevyMeasure ν) {n : ℕ} (hn : 0 < n) :
    IsLevyMeasure ((n : ℝ≥0∞)⁻¹ • ν) := by
  refine ⟨?_, ?_⟩
  · simp [Measure.smul_apply, hν.1]
  · rw [lintegral_smul_measure]
    refine ENNReal.mul_lt_top ?_ hν.2
    rw [ENNReal.inv_lt_top]
    exact_mod_cast hn

/-- The triplet scaled by `1 / n`, for the same truncation. -/
def LevyTriplet.divNat (L : LevyTriplet) (n : ℕ) (hn : 0 < n) : LevyTriplet where
  gaussianVariance := L.gaussianVariance / n
  drift := L.drift / n
  jumpMeasure := (n : ℝ≥0∞)⁻¹ • L.jumpMeasure
  isLevyMeasure := isLevyMeasure_inv_nsmul L.isLevyMeasure hn

/-- Dividing a triplet by `n` divides its exponent by `n`. -/
lemma LevyTriplet.exponent_divNat (L : LevyTriplet) {n : ℕ} (hn : 0 < n) (t : ℝ) :
    (L.divNat n hn).exponent t = L.exponent t / n := by
  have hint : Integrable (levyIntegrand t) L.jumpMeasure :=
    integrable_levyIntegrand L.isLevyMeasure t
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [exponent_eq_levyIntegrand, exponent_eq_levyIntegrand]
  simp only [LevyTriplet.divNat]
  rw [MeasureTheory.integral_smul_measure]
  have hto : ((n : ℝ≥0∞)⁻¹).toReal = (n : ℝ)⁻¹ := by
    simp [ENNReal.toReal_inv]
  rw [hto, RCLike.real_smul_eq_coe_mul]
  rw [show (ofReal (L.drift / n)) = (L.drift : ℂ) / n from ofReal_div _ _]
  rw [show ((L.gaussianVariance / (n : ℝ≥0) : ℝ≥0) : ℂ) =
      (L.gaussianVariance : ℂ) / n by
    rw [NNReal.coe_div, ofReal_div]
    norm_cast]
  push_cast
  field_simp [hnC]

end CKMA
