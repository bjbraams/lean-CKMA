/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Probability.InfinitelyDivisible.Basic
public import CKMA.Probability.InfinitelyDivisible.Exponent
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Second differences of a Lévy exponent

The drift is linear and the compensator is linear in the frequency, so both have vanishing second
differences. The Gaussian term contributes a constant multiple of `h²`, and the jump integrand
contributes `-4 sin(h x / 2)² exp(I t x)`. The resulting finite sine measure has that second
difference, up to sign, as its characteristic function.
-/

@[expose] public section

noncomputable section

namespace CKMA

open MeasureTheory Complex Filter Topology Set ENNReal
open scoped NNReal ENNReal

/-- The second symmetric difference of `f` at step `h`. -/
def secondDiff (f : ℝ → ℂ) (h t : ℝ) : ℂ :=
  f (t + h) + f (t - h) - 2 * f t

/-- Second differences are additive. -/
lemma secondDiff_add (f g : ℝ → ℂ) (h t : ℝ) :
    secondDiff (fun s => f s + g s) h t = secondDiff f h t + secondDiff g h t := by
  simp only [secondDiff]
  ring

/-- Second differences respect subtraction. -/
lemma secondDiff_sub (f g : ℝ → ℂ) (h t : ℝ) :
    secondDiff (fun s => f s - g s) h t = secondDiff f h t - secondDiff g h t := by
  simp only [secondDiff]
  ring

/-- A constant function has vanishing second difference. -/
lemma secondDiff_const (c : ℂ) (h t : ℝ) : secondDiff (fun _ => c) h t = 0 := by
  simp only [secondDiff]
  ring

/-- The second difference of `exp(I s x)` factors through the step `h`. -/
lemma secondDiff_exp (h t x : ℝ) :
    secondDiff (fun s => exp (I * s * x)) h t =
      exp (I * t * x) * (exp (I * h * x) + exp (-(I * h * x)) - 2) := by
  simp only [secondDiff]
  have h1 : I * ↑(t + h) * ↑x = I * ↑t * ↑x + I * ↑h * ↑x := by
    push_cast
    ring
  have h2 : I * ↑(t - h) * ↑x = I * ↑t * ↑x + -(I * ↑h * ↑x) := by
    push_cast
    ring
  rw [h1, h2, exp_add, exp_add]
  ring

/-- `exp(I θ) + exp(-I θ) - 2 = -4 sin(θ / 2)²`. -/
lemma exp_I_add_exp_neg_sub_two (θ : ℝ) :
    exp (I * θ) + exp (-I * θ) - 2 = -4 * (Real.sin (θ / 2) : ℂ) ^ 2 := by
  have hcos : (Real.cos θ : ℂ) =
      (exp ((θ : ℂ) * I) + exp ((-θ : ℂ) * I)) / 2 := by
    rw [ofReal_cos]
    rfl
  have h1 : exp (I * θ) = exp ((θ : ℂ) * I) := by
    congr 1
    ring
  have h2 : exp (-I * θ) = exp ((-θ : ℂ) * I) := by
    congr 1
    ring
  rw [← h1, ← h2] at hcos
  have htrig : Real.cos θ = 1 - 2 * Real.sin (θ / 2) ^ 2 := by
    simpa [show (2 : ℝ) * (θ / 2) = θ by ring] using
      Real.cos_two_mul_eq_one_sub (x := θ / 2)
  have hsub : (Real.cos θ : ℂ) - 1 = -2 * (Real.sin (θ / 2) : ℂ) ^ 2 := by
    rw [htrig]
    push_cast
    ring
  calc
    exp (I * θ) + exp (-I * θ) - 2
        = 2 * ((exp (I * θ) + exp (-I * θ)) / 2 - 1) := by ring
    _ = 2 * ((Real.cos θ : ℂ) - 1) := by rw [hcos]
    _ = 2 * (-2 * (Real.sin (θ / 2) : ℂ) ^ 2) := by rw [hsub]
    _ = -4 * (Real.sin (θ / 2) : ℂ) ^ 2 := by ring

/-- The second difference of the Lévy integrand is the sine weight times the oscillation. -/
lemma secondDiff_levyIntegrand (h t x : ℝ) :
    secondDiff (fun s => levyIntegrand s x) h t =
      exp (I * t * x) * (-4 * (Real.sin (h * x / 2) : ℂ) ^ 2) := by
  have hsplit : (fun s => levyIntegrand s x) =
      fun s : ℝ => (exp (I * s * x) -
        (if |x| ≤ 1 then I * s * x else 0)) - 1 := by
    ext s
    simp only [levyIntegrand]
    ring
  have hcomp : secondDiff (fun s => if |x| ≤ 1 then I * s * x else 0) h t = 0 := by
    by_cases hx : |x| ≤ 1
    · simp only [secondDiff, hx, ite_true]
      push_cast
      ring
    · simp only [secondDiff, hx, ite_false]
      ring
  rw [hsplit, secondDiff_sub, secondDiff_const, sub_zero, secondDiff_sub, hcomp, sub_zero,
    secondDiff_exp]
  have hθ : exp (I * h * x) + exp (-(I * h * x)) - 2 =
      -4 * (Real.sin (h * x / 2) : ℂ) ^ 2 := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using exp_I_add_exp_neg_sub_two (h * x)
  rw [hθ]

/-- Second differences pass inside the Lévy integral. -/
lemma secondDiff_integral_levyIntegrand {ν : Measure ℝ} (hν : IsLevyMeasure ν) (h t : ℝ) :
    secondDiff (fun s => ∫ x, levyIntegrand s x ∂ν) h t =
      ∫ x, secondDiff (fun s => levyIntegrand s x) h t ∂ν := by
  have hi (s : ℝ) : Integrable (levyIntegrand s) ν := integrable_levyIntegrand hν s
  simp only [secondDiff]
  have hsum : Integrable (fun x => levyIntegrand (t + h) x + levyIntegrand (t - h) x) ν :=
    (hi (t + h)).add (hi (t - h))
  have htwo : Integrable (fun x => (2 : ℂ) * levyIntegrand t x) ν := (hi t).const_mul 2
  rw [← integral_const_mul (2 : ℂ) (levyIntegrand t),
    ← integral_add (hi (t + h)) (hi (t - h)), ← integral_sub hsum htwo]

/-- Drift and Gaussian parts of the second difference. -/
lemma secondDiff_drift_gaussian (b : ℝ) (a : ℂ) (h t : ℝ) :
    secondDiff (fun s => I * b * s - a * (s : ℂ) ^ 2 / 2) h t = -(a * (h : ℂ) ^ 2) := by
  simp only [secondDiff]
  push_cast
  ring

/-- The second difference of a Lévy exponent. -/
lemma secondDiff_exponent (L : LevyTriplet) (h t : ℝ) :
    secondDiff L.exponent h t =
      -((L.gaussianVariance : ℂ) * (h : ℂ) ^ 2) +
        ∫ x, exp (I * t * x) * (-4 * (Real.sin (h * x / 2) : ℂ) ^ 2) ∂L.jumpMeasure := by
  have hfun : L.exponent = fun s : ℝ =>
      I * L.drift * s - (L.gaussianVariance : ℂ) * (s : ℂ) ^ 2 / 2 +
        ∫ x, levyIntegrand s x ∂L.jumpMeasure := by
    ext s
    exact L.exponent_eq_levyIntegrand s
  rw [hfun, secondDiff_add, secondDiff_drift_gaussian,
    secondDiff_integral_levyIntegrand L.isLevyMeasure]
  simp_rw [secondDiff_levyIntegrand]

/-- The weight `4 sin(h x / 2)²`. -/
def sineWeight (h x : ℝ) : ℝ :=
  4 * Real.sin (h * x / 2) ^ 2

/-- The sine weight is nonnegative. -/
lemma sineWeight_nonneg (h x : ℝ) : 0 ≤ sineWeight h x := by
  unfold sineWeight
  positivity

/-- The sine weight is continuous. -/
lemma continuous_sineWeight (h : ℝ) : Continuous (sineWeight h) := by
  unfold sineWeight
  fun_prop

/-- `4 sin(h x / 2)²` is dominated by a multiple of `1 ∧ x²`. -/
lemma sineWeight_le (h x : ℝ) :
    sineWeight h x ≤ (h ^ 2 + 4) * min 1 (x ^ 2) := by
  have hsq : 4 * Real.sin (h * x / 2) ^ 2 ≤ h ^ 2 * x ^ 2 := by
    calc
      4 * Real.sin (h * x / 2) ^ 2 ≤ 4 * (h * x / 2) ^ 2 :=
        mul_le_mul_of_nonneg_left Real.sin_sq_le_sq (by norm_num)
      _ = h ^ 2 * x ^ 2 := by ring
  have hfour : 4 * Real.sin (h * x / 2) ^ 2 ≤ 4 := by
    have := Real.sin_sq_le_one (h * x / 2)
    nlinarith
  have hmin : sineWeight h x ≤ min (h ^ 2 * x ^ 2) 4 := by
    simpa [sineWeight] using le_min hsq hfour
  refine hmin.trans ?_
  by_cases hx : x ^ 2 ≤ 1
  · rw [min_eq_right hx]
    exact (min_le_left _ _).trans (by nlinarith [sq_nonneg h, sq_nonneg x])
  · rw [min_eq_left (le_of_not_ge hx)]
    exact (min_le_right _ _).trans (by nlinarith [sq_nonneg h])

/-- The sine weight is integrable against a Lévy measure. -/
lemma integrable_sineWeight {ν : Measure ℝ} (hν : IsLevyMeasure ν) (h : ℝ) :
    Integrable (sineWeight h) ν := by
  have hdom : Integrable (fun x : ℝ => (h ^ 2 + 4) * min 1 (x ^ 2)) ν :=
    (integrable_min_one_sq hν).const_mul (h ^ 2 + 4)
  refine hdom.mono' (continuous_sineWeight h).aestronglyMeasurable ?_
  refine ae_of_all _ fun x => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (sineWeight_nonneg h x)]
  exact sineWeight_le h x

/-- The sine weight as an extended-nonnegative density. -/
def sineDensity (h : ℝ) : ℝ → ℝ≥0∞ :=
  fun x => ENNReal.ofReal (sineWeight h x)

/-- The sine density is measurable. -/
lemma measurable_sineDensity (h : ℝ) : Measurable (sineDensity h) :=
  ENNReal.measurable_ofReal.comp (continuous_sineWeight h).measurable

/-- The set where `sin(h x / 2)` does not vanish. -/
def sineSet (h : ℝ) : Set ℝ :=
  {x | Real.sin (h * x / 2) ≠ 0}

/-- The sine set is Borel. -/
lemma measurableSet_sineSet (h : ℝ) : MeasurableSet (sineSet h) := by
  have hc : Continuous fun x : ℝ => Real.sin (h * x / 2) := by fun_prop
  have hclosed : IsClosed {x : ℝ | Real.sin (h * x / 2) = 0} :=
    isClosed_eq hc continuous_const
  have hs : sineSet h = {x : ℝ | Real.sin (h * x / 2) = 0}ᶜ := by
    ext x
    simp [sineSet]
  rw [hs]
  exact hclosed.measurableSet.compl

/-- The origin lies in every nodal set of `sin(h x / 2)`. -/
lemma zero_notMem_sineSet (h : ℝ) : (0 : ℝ) ∉ sineSet h := by
  simp [sineSet, Real.sin_zero]

/-- On the sine set the density is strictly positive. -/
lemma sineDensity_ne_zero {h x : ℝ} (hx : x ∈ sineSet h) : sineDensity h x ≠ 0 := by
  simp only [sineSet] at hx
  rw [sineDensity, ne_eq, ENNReal.ofReal_eq_zero, not_le]
  have hsin : 0 < Real.sin (h * x / 2) ^ 2 := sq_pos_of_ne_zero hx
  simpa [sineWeight] using mul_pos (by norm_num : (0 : ℝ) < 4) hsin

/-- The finite measure `a h² δ_0` plus the sine-weighted jump measure. -/
def sineMeasure (L : LevyTriplet) (h : ℝ) : Measure ℝ :=
  ENNReal.ofReal ((L.gaussianVariance : ℝ) * h ^ 2) • Measure.dirac 0 +
    L.jumpMeasure.withDensity (sineDensity h)

/-- A Lévy measure weighted by the sine density is finite. -/
lemma isFiniteMeasure_withDensity_sine (L : LevyTriplet) (h : ℝ) :
    IsFiniteMeasure (L.jumpMeasure.withDensity (sineDensity h)) := by
  refine ⟨?_⟩
  rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
  exact lt_top_iff_ne_top.2 <|
    (lintegral_ofReal_ne_top_iff_integrable (continuous_sineWeight h).aestronglyMeasurable
      (ae_of_all _ (sineWeight_nonneg h))).2 (integrable_sineWeight L.isLevyMeasure h)

/-- The Gaussian atom in the sine measure is a finite measure. -/
lemma isFiniteMeasure_gaussianAtom (L : LevyTriplet) (h : ℝ) :
    IsFiniteMeasure
      (ENNReal.ofReal ((L.gaussianVariance : ℝ) * h ^ 2) • Measure.dirac (0 : ℝ)) := by
  refine ⟨?_⟩
  have hdir : Measure.dirac (0 : ℝ) Set.univ = 1 := by
    rw [Measure.dirac_apply' _ MeasurableSet.univ]
    simp [Set.indicator_of_mem]
  rw [Measure.smul_apply, hdir, smul_eq_mul, mul_one]
  exact ENNReal.ofReal_lt_top

/-- The sine measure of a Lévy triplet is finite. -/
lemma isFiniteMeasure_sineMeasure (L : LevyTriplet) (h : ℝ) :
    IsFiniteMeasure (sineMeasure L h) := by
  have hjump : IsFiniteMeasure (L.jumpMeasure.withDensity (sineDensity h)) :=
    isFiniteMeasure_withDensity_sine L h
  have hgauss : IsFiniteMeasure
      (ENNReal.ofReal ((L.gaussianVariance : ℝ) * h ^ 2) • Measure.dirac (0 : ℝ)) :=
    isFiniteMeasure_gaussianAtom L h
  unfold sineMeasure
  exact isFiniteMeasureAdd

/-- The integrand of a real characteristic function is integrable on a finite measure. -/
lemma integrable_charIntegrand {μ : Measure ℝ} [IsFiniteMeasure μ] (t : ℝ) :
    Integrable (fun x : ℝ => exp (t * x * I)) μ := by
  have hc : Continuous fun x : ℝ => exp (t * x * I) := by fun_prop
  refine (integrable_const (1 : ℝ)).mono' hc.aestronglyMeasurable ?_
  refine ae_of_all _ fun x => ?_
  have harg : ↑t * ↑x * I = ↑(t * x) * I := by
    push_cast
    ring
  rw [harg, norm_exp_ofReal_mul_I]

/-- Characteristic functions add over a sum of finite measures. -/
lemma charFun_add {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν] (t : ℝ) :
    charFun (μ + ν) t = charFun μ t + charFun ν t := by
  simp_rw [charFun_apply_real]
  exact integral_add_measure (integrable_charIntegrand t) (integrable_charIntegrand t)

/-- The atom of the sine measure has characteristic function `a h²`. -/
lemma charFun_gaussianAtom (L : LevyTriplet) (h t : ℝ) :
    charFun (ENNReal.ofReal ((L.gaussianVariance : ℝ) * h ^ 2) • Measure.dirac (0 : ℝ)) t =
      ((L.gaussianVariance : ℝ) * h ^ 2 : ℂ) := by
  have hnn : 0 ≤ (L.gaussianVariance : ℝ) * h ^ 2 :=
    mul_nonneg (NNReal.coe_nonneg _) (sq_nonneg _)
  rw [charFun_apply_real, integral_smul_measure, integral_dirac]
  rw [ENNReal.toReal_ofReal hnn, RCLike.real_smul_eq_coe_mul]
  simp

/-- The sine-weighted jump measure has characteristic function `∫ 4 sin² exp`. -/
lemma charFun_jumpSine (L : LevyTriplet) (h t : ℝ) :
    charFun (L.jumpMeasure.withDensity (sineDensity h)) t =
      ∫ x, (sineWeight h x : ℂ) * exp (I * t * x) ∂L.jumpMeasure := by
  rw [charFun_apply_real,
    integral_withDensity_eq_integral_toReal_smul (measurable_sineDensity h)
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [sineDensity, ENNReal.toReal_ofReal (sineWeight_nonneg h x),
    RCLike.real_smul_eq_coe_mul]
  congr 1
  ring

/-- The characteristic function of the sine measure is the negative second difference. -/
lemma charFun_sineMeasure (L : LevyTriplet) (h t : ℝ) :
    charFun (sineMeasure L h) t = -secondDiff L.exponent h t := by
  have hgaussFin : IsFiniteMeasure
      (ENNReal.ofReal ((L.gaussianVariance : ℝ) * h ^ 2) • Measure.dirac (0 : ℝ)) :=
    isFiniteMeasure_gaussianAtom L h
  have hjumpFin : IsFiniteMeasure (L.jumpMeasure.withDensity (sineDensity h)) :=
    isFiniteMeasure_withDensity_sine L h
  have hint : ∫ x, exp (I * t * x) * (-4 * (Real.sin (h * x / 2) : ℂ) ^ 2)
      ∂L.jumpMeasure =
      -∫ x, (sineWeight h x : ℂ) * exp (I * t * x) ∂L.jumpMeasure := by
    rw [← integral_neg]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [sineWeight]
    push_cast
    ring_nf
  rw [sineMeasure, charFun_add, charFun_gaussianAtom, charFun_jumpSine, secondDiff_exponent, hint]
  ring_nf

/-- The sine measure charges the origin by the Gaussian mass `a h²`. -/
lemma sineMeasure_real_singleton (L : LevyTriplet) (h : ℝ) :
    (sineMeasure L h).real {0} = (L.gaussianVariance : ℝ) * h ^ 2 := by
  have hden : L.jumpMeasure.withDensity (sineDensity h) {(0 : ℝ)} = 0 := by
    rw [withDensity_apply _ (measurableSet_singleton _), lintegral_singleton,
      L.isLevyMeasure.1, mul_zero]
  have hdir : Measure.dirac (0 : ℝ) {(0 : ℝ)} = 1 := by
    rw [Measure.dirac_apply' _ (measurableSet_singleton _)]
    simp [Set.indicator_of_mem]
  rw [measureReal_def, sineMeasure, Measure.add_apply, Measure.smul_apply, hden, add_zero,
    hdir, smul_eq_mul, mul_one, ENNReal.toReal_ofReal
      (mul_nonneg (NNReal.coe_nonneg _) (sq_nonneg _))]

/-- Inverting the sine density recovers the Lévy measure on the sine set. -/
lemma jumpMeasure_restrict_eq_inv_sine (L : LevyTriplet) (h : ℝ) :
    L.jumpMeasure.restrict (sineSet h) =
      ((sineMeasure L h).restrict (sineSet h)).withDensity
        (fun x => (sineDensity h x)⁻¹) := by
  have hs : MeasurableSet (sineSet h) := measurableSet_sineSet h
  have hf : Measurable (sineDensity h) := measurable_sineDensity h
  have h0 : (0 : ℝ) ∉ sineSet h := zero_notMem_sineSet h
  have hdir : (ENNReal.ofReal ((L.gaussianVariance : ℝ) * h ^ 2) •
      Measure.dirac (0 : ℝ)).restrict (sineSet h) = 0 := by
    ext t ht
    rw [Measure.restrict_apply ht, Measure.smul_apply,
      Measure.dirac_apply' _ (ht.inter hs),
      Set.indicator_of_notMem (fun hmem => h0 (Set.mem_of_mem_inter_right hmem)),
      smul_zero]
    simp [Measure.coe_zero]
  have hrest : (sineMeasure L h).restrict (sineSet h) =
      (L.jumpMeasure.withDensity (sineDensity h)).restrict (sineSet h) := by
    unfold sineMeasure
    rw [Measure.restrict_add, hdir, zero_add]
  have hwd : (L.jumpMeasure.restrict (sineSet h)).withDensity (sineDensity h) =
      (sineMeasure L h).restrict (sineSet h) := by
    rw [← restrict_withDensity hs]
    exact hrest.symm
  rw [← hwd]
  symm
  exact withDensity_inv_same hf
    (ae_restrict_of_forall_mem hs fun x hx => sineDensity_ne_zero hx)
    (ae_of_all _ fun _ => ENNReal.ofReal_ne_top)

end CKMA
