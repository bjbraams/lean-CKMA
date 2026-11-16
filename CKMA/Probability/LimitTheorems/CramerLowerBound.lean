/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
public import Mathlib.Analysis.SpecialFunctions.Exp

import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Probability.Moments.Tilted
import Mathlib.Probability.Moments.Variance
import TauCeti.MeasureTheory.Measure.PiWithDensity

/-!
# The lower bound in Cramér's theorem (06.60)

For a probability measure `ρ` on `ℝ`, the empirical mean of `n + 1` coordinates under the
product measure `ρ ^ (n + 1)` lies within `δ` of a point `x` with probability at least
`exp (-(n + 1) (I x + o(1)))`, where `I` is the Legendre transform of the extended logarithmic
moment generating function of `ρ`. No integrability assumption on `ρ` is needed.

The proof follows Dembo–Zeitouni, *Large Deviations Techniques and Applications*, Theorem 2.2.3.
After centring at `x`, the law is truncated to `[-M, M]`. When both half-lines carry mass, the
truncated cumulant generating function has a minimiser `η`, and the exponential tilt of the
truncated law by `η` has mean zero; Chebyshev's inequality for the tilted product measure and the
change of measure bound the probability from below by the minimum of the truncated cumulant
generating function. A compactness argument lets `M` tend to infinity. When one half-line is
null, the atom at zero gives the bound directly.

## Main results

* `CKMA.neg_iSup_sub_log_lintegral_le_liminf_log_pi`: the Cramér lower bound for balls under
  finite product measures.
-/

public section

noncomputable section

namespace CKMA

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

/-! ### Notation for the proof -/

/-- The empirical mean of `n + 1` real coordinates. -/
private def meanFin (n : ℕ) (y : Fin (n + 1) → ℝ) : ℝ := (n + 1 : ℝ)⁻¹ * ∑ i, y i

/-- The product law of `n + 1` independent draws from `ρ`. -/
private def piLaw (ρ : Measure ℝ) (n : ℕ) : Measure (Fin (n + 1) → ℝ) :=
  Measure.pi fun _ ↦ ρ

/-- The extended logarithmic Laplace transform of a measure on `ℝ`. -/
private def logLaplace (ρ : Measure ℝ) (t : ℝ) : EReal :=
  ENNReal.log (∫⁻ y, ENNReal.ofReal (Real.exp (t * y)) ∂ρ)

/-- The normalized logarithmic probability that the empirical mean lies in `(-δ, δ)`. -/
private def ballRate (ρ : Measure ℝ) (δ : ℝ) (n : ℕ) : EReal :=
  (((n + 1 : ℝ)⁻¹ : ℝ) : EReal) * ENNReal.log (piLaw ρ n {y | |meanFin n y| < δ})

/-- The empirical mean is measurable. -/
private lemma measurable_meanFin (n : ℕ) : Measurable (meanFin n) := by
  unfold meanFin
  fun_prop

/-- The event that the empirical mean lies in `(-δ, δ)` is measurable. -/
private lemma measurableSet_meanFin_lt (n : ℕ) (δ : ℝ) :
    MeasurableSet {y : Fin (n + 1) → ℝ | |meanFin n y| < δ} :=
  measurableSet_lt (continuous_abs.measurable.comp (measurable_meanFin n)) measurable_const

/-- Finite products of probability measures are probability measures. -/
private instance isProbabilityMeasure_piLaw (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (n : ℕ) :
    IsProbabilityMeasure (piLaw ρ n) := by
  unfold piLaw
  infer_instance

/-- The speed factor `(n + 1)⁻¹` is nonnegative in `EReal`. -/
private lemma inv_succ_nonneg (n : ℕ) : (0 : EReal) ≤ (((n + 1 : ℝ)⁻¹ : ℝ) : EReal) :=
  EReal.coe_le_coe_iff.mpr (inv_nonneg.2 (by positivity))

/-- The ball rate increases with the radius. -/
private lemma ballRate_mono (ρ : Measure ℝ) {δ δ' : ℝ} (h : δ' ≤ δ) (n : ℕ) :
    ballRate ρ δ' n ≤ ballRate ρ δ n :=
  mul_le_mul_of_nonneg_left
    (ENNReal.log_monotone (measure_mono fun _ hy ↦ lt_of_lt_of_le hy h)) (inv_succ_nonneg n)

/-- An eventual lower bound `c * exp ((n + 1) b)` on probabilities gives the rate bound `b`. -/
private lemma coe_le_liminf_of_exp_le {s : ℕ → ℝ≥0∞} {b c : ℝ} (hc : 0 < c)
    (h : ∀ᶠ n : ℕ in atTop, ENNReal.ofReal (c * Real.exp ((n + 1 : ℝ) * b)) ≤ s n) :
    (b : EReal) ≤
      liminf (fun n : ℕ ↦ (((n + 1 : ℝ)⁻¹ : ℝ) : EReal) * ENNReal.log (s n)) atTop := by
  have hlow : ∀ᶠ n : ℕ in atTop, (((n + 1 : ℝ)⁻¹ * Real.log c + b : ℝ) : EReal) ≤
      (((n + 1 : ℝ)⁻¹ : ℝ) : EReal) * ENNReal.log (s n) := by
    filter_upwards [h] with n hn
    have hpos : 0 < c * Real.exp ((n + 1 : ℝ) * b) := mul_pos hc (Real.exp_pos _)
    have hlog : ENNReal.log (ENNReal.ofReal (c * Real.exp ((n + 1 : ℝ) * b))) =
        ((Real.log c + (n + 1 : ℝ) * b : ℝ) : EReal) := by
      rw [ENNReal.log_ofReal_of_pos hpos, Real.log_mul hc.ne' (Real.exp_pos _).ne',
        Real.log_exp]
    calc (((n + 1 : ℝ)⁻¹ * Real.log c + b : ℝ) : EReal)
        = (((n + 1 : ℝ)⁻¹ : ℝ) : EReal) * ((Real.log c + (n + 1 : ℝ) * b : ℝ) : EReal) := by
          rw [← EReal.coe_mul]
          congr 1
          field_simp
      _ ≤ (((n + 1 : ℝ)⁻¹ : ℝ) : EReal) * ENNReal.log (s n) := by
          rw [← hlog]
          exact mul_le_mul_of_nonneg_left (ENNReal.log_monotone hn) (inv_succ_nonneg n)
  have htend : Tendsto (fun n : ℕ ↦ (((n + 1 : ℝ)⁻¹ * Real.log c + b : ℝ) : EReal)) atTop
      (𝓝 (b : EReal)) := by
    have hinv : Tendsto (fun n : ℕ ↦ (n + 1 : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp
        (tendsto_atTop_add_const_right _ (1 : ℝ) tendsto_natCast_atTop_atTop)
    have hreal : Tendsto (fun n : ℕ ↦ (n + 1 : ℝ)⁻¹ * Real.log c + b) atTop (𝓝 b) := by
      simpa using (hinv.mul_const (Real.log c)).add_const b
    exact continuous_coe_real_ereal.tendsto b |>.comp hreal
  rw [← htend.liminf_eq]
  exact liminf_le_liminf hlow

/-! ### One half-line is null -/

/-- The atom at zero bounds the ball probability from below. -/
private lemma log_measure_zero_le_ballRate (ρ : Measure ℝ) [IsProbabilityMeasure ρ] {δ : ℝ}
    (hδ : 0 < δ) (n : ℕ) : ENNReal.log (ρ {0}) ≤ ballRate ρ δ n := by
  have hsub : (univ.pi fun _ : Fin (n + 1) ↦ ({0} : Set ℝ)) ⊆
      {y : Fin (n + 1) → ℝ | |meanFin n y| < δ} := by
    intro y hy
    have hy0 : ∀ i, y i = 0 := fun i ↦ hy i (mem_univ i)
    simp [meanFin, hy0, hδ]
  have hpi : piLaw ρ n (univ.pi fun _ : Fin (n + 1) ↦ ({0} : Set ℝ)) = ρ {0} ^ (n + 1) := by
    simp [piLaw, Measure.pi_pi]
  have hle : ENNReal.log (ρ {0} ^ (n + 1)) ≤
      ENNReal.log (piLaw ρ n {y | |meanFin n y| < δ}) :=
    ENNReal.log_monotone (hpi ▸ measure_mono hsub)
  have hcast : (((n + 1 : ℕ) : EReal)) = (((n + 1 : ℝ) : ℝ) : EReal) := by norm_cast
  calc ENNReal.log (ρ {0})
      = (((n + 1 : ℝ)⁻¹ : ℝ) : EReal) * ((((n + 1 : ℝ) : ℝ) : EReal) * ENNReal.log (ρ {0})) := by
        rw [← mul_assoc, ← EReal.coe_mul, inv_mul_cancel₀ (by positivity), EReal.coe_one,
          one_mul]
    _ = (((n + 1 : ℝ)⁻¹ : ℝ) : EReal) * ENNReal.log (ρ {0} ^ (n + 1)) := by
        rw [ENNReal.log_pow, hcast]
    _ ≤ ballRate ρ δ n := mul_le_mul_of_nonneg_left hle (inv_succ_nonneg n)

/-- If the negative half-line is null, the logarithmic Laplace transform tends to the log of
the atom at zero at `-∞`. -/
private lemma iInf_logLaplace_le_of_Iio (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    (h : ρ (Iio 0) = 0) : ⨅ t, logLaplace ρ t ≤ ENNReal.log (ρ {0}) := by
  let F : ℕ → ℝ → ℝ≥0∞ := fun k y ↦ ENNReal.ofReal (Real.exp (-(k : ℝ) * y))
  have hnn : ∀ᵐ y ∂ρ, 0 ≤ y := by
    have := measure_eq_zero_iff_ae_notMem.mp h
    filter_upwards [this] with y hy
    simpa using hy
  have hlim : Tendsto (fun k ↦ ∫⁻ y, F k y ∂ρ) atTop
      (𝓝 (∫⁻ y, ({0} : Set ℝ).indicator 1 y ∂ρ)) := by
    refine tendsto_lintegral_of_dominated_convergence 1 (fun k ↦ by fun_prop) (fun k ↦ ?_)
      (by simp) ?_
    · filter_upwards [hnn] with y hy
      simp only [F, Pi.one_apply]
      rw [ENNReal.ofReal_le_one]
      exact Real.exp_le_one_iff.mpr (by nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
    · filter_upwards [hnn] with y hy
      rcases hy.eq_or_lt with rfl | hpos
      · simp [F]
      · have hne : y ≠ 0 := hpos.ne'
        simp only [F, indicator_of_notMem (show y ∉ ({0} : Set ℝ) from hne)]
        have hlin : Tendsto (fun k : ℕ ↦ -(k : ℝ) * y) atTop atBot := by
          have hk : Tendsto (fun k : ℕ ↦ (k : ℝ) * y) atTop atTop :=
            tendsto_natCast_atTop_atTop.atTop_mul_const hpos
          exact (tendsto_neg_atTop_atBot.comp hk).congr fun k ↦ by simp [neg_mul]
        simpa using (ENNReal.tendsto_ofReal (Real.tendsto_exp_atBot.comp hlin))
  rw [lintegral_indicator_one (measurableSet_singleton 0)] at hlim
  have hlog : Tendsto (fun k : ℕ ↦ logLaplace ρ (-(k : ℝ))) atTop (𝓝 (ENNReal.log (ρ {0}))) :=
    (ENNReal.continuous_log.tendsto _).comp hlim
  exact ge_of_tendsto' hlog fun k ↦ iInf_le _ _

/-- Reflecting the measure reflects the logarithmic Laplace transform. -/
private lemma logLaplace_map_neg (ρ : Measure ℝ) (t : ℝ) :
    logLaplace (ρ.map Neg.neg) t = logLaplace ρ (-t) := by
  unfold logLaplace
  rw [lintegral_map (by fun_prop) measurable_neg]
  simp [mul_neg, neg_mul]

/-- The ball rate is bounded below by the atom at zero when one half-line is null. -/
private lemma iInf_logLaplace_le_ballRate_of_null (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    {δ : ℝ} (hδ : 0 < δ) (h : ρ (Iio 0) = 0 ∨ ρ (Ioi 0) = 0) :
    ⨅ t, logLaplace ρ t ≤ liminf (ballRate ρ δ) atTop := by
  have hatom : ⨅ t, logLaplace ρ t ≤ ENNReal.log (ρ {0}) := by
    rcases h with h | h
    · exact iInf_logLaplace_le_of_Iio ρ h
    · have hIio : ρ.map Neg.neg (Iio 0) = 0 := by
        rw [Measure.map_apply measurable_neg measurableSet_Iio]
        simpa using h
      have h0 : ρ.map Neg.neg {0} = ρ {0} := by
        rw [Measure.map_apply measurable_neg (measurableSet_singleton 0)]
        simp
      calc ⨅ t, logLaplace ρ t ≤ ⨅ t, logLaplace (ρ.map Neg.neg) t :=
            le_iInf fun t ↦ (logLaplace_map_neg ρ t).symm ▸ iInf_le _ (-t)
        _ ≤ ENNReal.log (ρ {0}) := h0 ▸ iInf_logLaplace_le_of_Iio _ hIio
  exact le_liminf_of_le (h := Eventually.of_forall fun n ↦
    hatom.trans (log_measure_zero_le_ballRate ρ hδ n))

/-! ### Truncation and tilting -/

/-- Exponentials are integrable against a truncation of a finite measure. -/
private lemma integrable_exp_restrict (ρ : Measure ℝ) [IsFiniteMeasure ρ] (M t : ℝ) :
    Integrable (fun y ↦ Real.exp (t * y)) (ρ.restrict (Icc (-M) M)) :=
  (by fun_prop : Continuous fun y : ℝ ↦ Real.exp (t * y)).integrableOn_Icc

/-- Chebyshev's inequality: the empirical mean of a centred square-integrable law eventually
lies in `(-δ, δ)` with probability at least one half. -/
private lemma half_le_piLaw_meanFin_lt (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hmem : MemLp id 2 ν) (hmean : ∫ y, y ∂ν = 0) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ENNReal.ofReal (1 / 2) ≤ piLaw ν n {y | |meanFin n y| < δ} := by
  set V := Var[id; ν]
  have hV : Tendsto (fun n : ℕ ↦ V / ((n + 1 : ℝ) * δ ^ 2)) atTop (𝓝 0) := by
    have h : Tendsto (fun n : ℕ ↦ (n + 1 : ℝ) * δ ^ 2) atTop atTop :=
      (tendsto_atTop_add_const_right _ (1 : ℝ) tendsto_natCast_atTop_atTop).atTop_mul_const
        (by positivity)
    exact h.const_div_atTop V
  filter_upwards [hV.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 2)] with n hn
  set B := {y : Fin (n + 1) → ℝ | |meanFin n y| < δ}
  let S : (Fin (n + 1) → ℝ) → ℝ := ∑ i, fun y ↦ id (y i)
  have hSapp : ∀ y, S y = ∑ i, y i := fun y ↦ by simp [S, Finset.sum_apply]
  have hcoord : ∀ i : Fin (n + 1), MemLp (fun y : Fin (n + 1) → ℝ ↦ id (y i)) 2 (piLaw ν n) :=
    fun i ↦ hmem.comp_measurePreserving (measurePreserving_eval _ i)
  have hmemS : MemLp S 2 (piLaw ν n) := memLp_finsetSum' _ fun i _ ↦ hcoord i
  have hint : (piLaw ν n)[S] = 0 := by
    rw [show S = fun y ↦ ∑ i, id (y i) from funext fun y ↦ by simp [S, Finset.sum_apply],
      integral_finsetSum _ fun i _ ↦ (hcoord i).integrable one_le_two]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    have hmap := (measurePreserving_eval (fun _ : Fin (n + 1) ↦ ν) i).map_eq
    calc ∫ a, id (a i) ∂piLaw ν n = ∫ y, id y ∂((piLaw ν n).map (Function.eval i)) :=
          (integral_map (μ := piLaw ν n) (φ := Function.eval i) (f := id)
            (measurable_pi_apply i).aemeasurable aestronglyMeasurable_id).symm
      _ = 0 := by
          rw [piLaw, hmap]
          exact hmean
  have hvar : Var[S; piLaw ν n] = (n + 1 : ℝ) * V := by
    rw [piLaw, variance_sum_pi (fun _ ↦ hmem)]
    simp [V]
  have hc : 0 < (n + 1 : ℝ) * δ := by positivity
  have hcheb := meas_ge_le_variance_div_sq hmemS hc
  have hsub : Bᶜ ⊆ {y | (n + 1 : ℝ) * δ ≤ |S y - (piLaw ν n)[S]|} := by
    intro y hy
    simp only [B, mem_compl_iff, mem_ofPred_eq, not_lt] at hy
    simp only [mem_ofPred_eq]
    rw [hint, sub_zero, hSapp]
    have hsum : ∑ i, y i = (n + 1 : ℝ) * meanFin n y := by
      simp only [meanFin]
      field_simp
    rw [hsum, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < n + 1)]
    exact mul_le_mul_of_nonneg_left hy (by positivity)
  have hcompl : piLaw ν n Bᶜ ≤ ENNReal.ofReal (1 / 2) := by
    refine (measure_mono hsub).trans (hcheb.trans (ENNReal.ofReal_le_ofReal ?_))
    rw [hvar]
    calc (n + 1 : ℝ) * V / ((n + 1 : ℝ) * δ) ^ 2 = V / ((n + 1 : ℝ) * δ ^ 2) := by
          field_simp
      _ ≤ 1 / 2 := hn
  have hreal : (piLaw ν n).real Bᶜ ≤ 1 / 2 :=
    ENNReal.toReal_le_of_le_ofReal (by norm_num) hcompl
  rw [probReal_compl_eq_one_sub (measurableSet_meanFin_lt n δ)] at hreal
  rw [ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)]
  change 1 / 2 ≤ (piLaw ν n).real B
  linarith

/-- On the ball, the product density of the tilted truncated law is at most
`exp ((n + 1) (|η| δ - L))`, where `L` is the logarithmic normalizer. -/
private lemma prod_density_le {η δ L Z : ℝ} (hZ : Real.exp L = Z) {n : ℕ}
    {y : Fin (n + 1) → ℝ} (hy : |meanFin n y| < δ) :
    ∏ i, Real.exp (η * y i) / Z ≤ Real.exp ((n + 1 : ℝ) * (|η| * δ - L)) := by
  have hprod : ∏ i, Real.exp (η * y i) / Z = Real.exp (η * ∑ i, y i - (n + 1 : ℝ) * L) := by
    rw [← hZ]
    simp_rw [← Real.exp_sub]
    rw [← Real.exp_sum, Finset.sum_sub_distrib, Finset.mul_sum]
    simp
  rw [hprod, Real.exp_le_exp]
  have hsum : ∑ i, y i = (n + 1 : ℝ) * meanFin n y := by
    simp only [meanFin]
    field_simp
  have hbound : η * ∑ i, y i ≤ (n + 1 : ℝ) * (|η| * δ) := by
    rw [hsum]
    calc η * ((n + 1 : ℝ) * meanFin n y) ≤ |η * ((n + 1 : ℝ) * meanFin n y)| := le_abs_self _
      _ = (n + 1 : ℝ) * (|η| * |meanFin n y|) := by
          rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < n + 1)]
          ring
      _ ≤ (n + 1 : ℝ) * (|η| * δ) := by gcongr
  nlinarith

/-- **Tilting.** At a critical point `η` of the truncated cumulant generating function, the
ball rate is at least the value of that function at `η`, minus `|η| δ`. -/
private lemma tilt_lower_bound (ρ : Measure ℝ) [IsProbabilityMeasure ρ] {M η δ : ℝ}
    (hδ : 0 < δ) (hM : ρ (Icc (-M) M) ≠ 0)
    (hη : deriv (cgf id (ρ.restrict (Icc (-M) M))) η = 0) :
    ((cgf id (ρ.restrict (Icc (-M) M)) η - |η| * δ : ℝ) : EReal) ≤
      liminf (ballRate ρ δ) atTop := by
  set ν := ρ.restrict (Icc (-M) M) with hν
  have hν0 : NeZero ν := ⟨by rwa [hν, Ne, Measure.restrict_eq_zero]⟩
  have hint : ∀ t, Integrable (fun y ↦ Real.exp (t * y)) ν := integrable_exp_restrict ρ M
  set L := cgf id ν η
  set Z := mgf id ν η
  have hZ : Real.exp L = Z := exp_cgf (hint η)
  set g : ℝ → ℝ≥0∞ := fun y ↦ ENNReal.ofReal (Real.exp (η * y) / Z)
  have hg : Measurable g := by fun_prop
  set ν' := ν.tilted (fun y ↦ η * y)
  have hν'prob : IsProbabilityMeasure ν' := isProbabilityMeasure_tilted (hint η)
  have hν'eq : ν' = ρ.withDensity ((Icc (-M) M).indicator g) := by
    rw [withDensity_indicator measurableSet_Icc]
    rfl
  have hmean : ∫ y, y ∂ν' = 0 := by
    have hset : η ∈ interior (integrableExpSet id ν) := by
      rw [show integrableExpSet id ν = univ from eq_univ_of_forall hint, interior_univ]
      exact mem_univ η
    have h := integral_tilted_mul_self hset
    rw [hη] at h
    exact h
  have hsupp : ∀ᵐ y ∂ν', y ∈ Icc (-M) M :=
    (tilted_absolutelyContinuous ν _).ae_le (ae_restrict_mem measurableSet_Icc)
  have hmem : MemLp id 2 ν' :=
    MemLp.of_bound aestronglyMeasurable_id M
      (hsupp.mono fun y hy ↦ by simpa [Real.norm_eq_abs] using abs_le.mpr hy)
  have hcm : ∀ n, piLaw ν' n {y | |meanFin n y| < δ} ≤
      ENNReal.ofReal (Real.exp ((n + 1 : ℝ) * (|η| * δ - L))) *
        piLaw ρ n {y | |meanFin n y| < δ} := by
    intro n
    have : IsFiniteMeasure (ρ.withDensity ((Icc (-M) M).indicator g)) := hν'eq ▸ inferInstance
    have hpi : piLaw ν' n =
        (piLaw ρ n).withDensity fun y ↦ ∏ i, (Icc (-M) M).indicator g (y i) := by
      rw [piLaw, piLaw, hν'eq]
      exact TauCeti.pi_withDensity (fun _ ↦ ρ) fun _ ↦ hg.indicator measurableSet_Icc
    rw [hpi, withDensity_apply _ (measurableSet_meanFin_lt n δ), ← setLIntegral_const]
    refine setLIntegral_mono measurable_const fun y hy ↦ ?_
    calc ∏ i, (Icc (-M) M).indicator g (y i) ≤ ∏ i, g (y i) :=
          Finset.prod_le_prod fun i _ ↦ indicator_le_self _ _ _
      _ = ENNReal.ofReal (∏ i, Real.exp (η * y i) / Z) :=
          (ENNReal.ofReal_prod_of_nonneg fun i _ ↦
            div_nonneg (Real.exp_pos _).le (hZ ▸ (Real.exp_pos _).le)).symm
      _ ≤ ENNReal.ofReal (Real.exp ((n + 1 : ℝ) * (|η| * δ - L))) :=
          ENNReal.ofReal_le_ofReal (prod_density_le hZ hy)
  have hfin : ∀ᶠ n : ℕ in atTop,
      ENNReal.ofReal (1 / 2 * Real.exp ((n + 1 : ℝ) * (L - |η| * δ))) ≤
        piLaw ρ n {y | |meanFin n y| < δ} := by
    filter_upwards [half_le_piLaw_meanFin_lt ν' hmem hmean hδ] with n hn
    set E := Real.exp ((n + 1 : ℝ) * (L - |η| * δ))
    have hE : Real.exp ((n + 1 : ℝ) * (|η| * δ - L)) = E⁻¹ := by
      rw [← Real.exp_neg]
      ring_nf
    have hEpos : 0 < E := Real.exp_pos _
    calc ENNReal.ofReal (1 / 2 * E) = ENNReal.ofReal E * ENNReal.ofReal (1 / 2) := by
          rw [← ENNReal.ofReal_mul hEpos.le, mul_comm]
      _ ≤ ENNReal.ofReal E * (ENNReal.ofReal E⁻¹ * piLaw ρ n {y | |meanFin n y| < δ}) := by
          gcongr
          exact hn.trans (hE ▸ hcm n)
      _ = piLaw ρ n {y | |meanFin n y| < δ} := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hEpos.le, mul_inv_cancel₀ hEpos.ne',
            ENNReal.ofReal_one, one_mul]
  exact coe_le_liminf_of_exp_le (by norm_num) hfin

/-- Shrinking the radius removes the `|η| δ` correction in `tilt_lower_bound`. -/
private lemma cgf_le_liminf_ballRate (ρ : Measure ℝ) [IsProbabilityMeasure ρ] {M η δ : ℝ}
    (hδ : 0 < δ) (hM : ρ (Icc (-M) M) ≠ 0)
    (hη : deriv (cgf id (ρ.restrict (Icc (-M) M))) η = 0) :
    ((cgf id (ρ.restrict (Icc (-M) M)) η : ℝ) : EReal) ≤ liminf (ballRate ρ δ) atTop := by
  set L := cgf id (ρ.restrict (Icc (-M) M)) η
  have hsmall : Tendsto (fun k : ℕ ↦ δ * (1 / ((k : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul δ
  have hreal : Tendsto (fun k : ℕ ↦ L - |η| * (δ * (1 / ((k : ℝ) + 1)))) atTop (𝓝 L) := by
    simpa using (hsmall.const_mul |η|).const_sub L
  refine le_of_tendsto' ((continuous_coe_real_ereal.tendsto L).comp hreal) fun k ↦ ?_
  have hδk : 0 < δ * (1 / ((k : ℝ) + 1)) := by positivity
  have hle : δ * (1 / ((k : ℝ) + 1)) ≤ δ := by
    have hk : 1 / ((k : ℝ) + 1) ≤ 1 :=
      (div_le_one (by positivity)).mpr (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
    calc δ * (1 / ((k : ℝ) + 1)) ≤ δ * 1 := by gcongr
      _ = δ := mul_one δ
  exact (tilt_lower_bound ρ hδk hM hη).trans
    (liminf_le_liminf (Eventually.of_forall fun n ↦ ballRate_mono ρ hle n))

/-! ### Minimisers of truncated cumulant generating functions -/

/-- A set of positive mass on which `b ≤ t y` bounds the cumulant generating function below. -/
private lemma add_log_le_cgf (ν : Measure ℝ) [IsFiniteMeasure ν]
    (hint : ∀ t, Integrable (fun y ↦ Real.exp (t * y)) ν) {S : Set ℝ} (hS : MeasurableSet S)
    (hS0 : 0 < ν.real S) {t b : ℝ} (hb : ∀ y ∈ S, b ≤ t * y) :
    b + Real.log (ν.real S) ≤ cgf id ν t := by
  have hlow : Real.exp b * ν.real S ≤ mgf id ν t := by
    calc Real.exp b * ν.real S ≤ ∫ y in S, Real.exp (t * y) ∂ν :=
          setIntegral_ge_of_const_le_real hS (measure_ne_top _ _)
            (fun y hy ↦ Real.exp_le_exp.mpr (hb y hy)) (hint t).integrableOn
      _ ≤ ∫ y, Real.exp (t * y) ∂ν :=
          setIntegral_le_integral (hint t) (Eventually.of_forall fun y ↦ (Real.exp_pos _).le)
      _ = mgf id ν t := rfl
  have hpos : 0 < Real.exp b * ν.real S := mul_pos (Real.exp_pos _) hS0
  calc b + Real.log (ν.real S) = Real.log (Real.exp b * ν.real S) := by
        rw [Real.log_mul (Real.exp_pos _).ne' hS0.ne', Real.log_exp]
    _ ≤ cgf id ν t := Real.log_le_log hpos hlow

/-- Mass on both sides of the origin gives a lower bound `|t| a + c` on the cumulant generating
function. -/
private lemma abs_mul_add_le_cgf (ν : Measure ℝ) [IsFiniteMeasure ν]
    (hint : ∀ t, Integrable (fun y ↦ Real.exp (t * y)) ν) {a b : ℝ}
    (hpos : 0 < ν.real (Icc a b)) (hneg : 0 < ν.real (Icc (-b) (-a))) (t : ℝ) :
    |t| * a + min (Real.log (ν.real (Icc a b))) (Real.log (ν.real (Icc (-b) (-a)))) ≤
      cgf id ν t := by
  rcases le_total 0 t with ht | ht
  · have h := add_log_le_cgf ν hint measurableSet_Icc hpos (t := t) (b := t * a)
      fun y hy ↦ mul_le_mul_of_nonneg_left hy.1 ht
    rw [abs_of_nonneg ht]
    linarith [min_le_left (Real.log (ν.real (Icc a b))) (Real.log (ν.real (Icc (-b) (-a))))]
  · have h := add_log_le_cgf ν hint measurableSet_Icc hneg (t := t) (b := -t * a)
      fun y hy ↦ by nlinarith [hy.2]
    rw [abs_of_nonpos ht]
    linarith [min_le_right (Real.log (ν.real (Icc a b))) (Real.log (ν.real (Icc (-b) (-a))))]

/-- The cumulant generating function of a law with all exponential moments is continuous. -/
private lemma continuous_cgf_id (ν : Measure ℝ) [IsFiniteMeasure ν] (hν : ν ≠ 0)
    (hint : ∀ t, Integrable (fun y ↦ Real.exp (t * y)) ν) : Continuous (cgf id ν) :=
  (continuous_mgf hint).log fun t ↦ (mgf_pos' hν (hint t)).ne'

/-- With mass on both sides of the origin, the cumulant generating function has a minimiser. -/
private lemma exists_forall_cgf_le (ν : Measure ℝ) [IsFiniteMeasure ν]
    (hint : ∀ t, Integrable (fun y ↦ Real.exp (t * y)) ν) {a b : ℝ} (ha : 0 < a)
    (hpos : 0 < ν.real (Icc a b)) (hneg : 0 < ν.real (Icc (-b) (-a))) :
    ∃ η, ∀ t, cgf id ν η ≤ cgf id ν t := by
  have hν : ν ≠ 0 := by
    rintro rfl
    simp at hpos
  set c := min (Real.log (ν.real (Icc a b))) (Real.log (ν.real (Icc (-b) (-a))))
  have hnorm : Tendsto (fun t : ℝ ↦ ‖t‖ * a + c) (cocompact ℝ) atTop :=
    tendsto_atTop_add_const_right _ c (tendsto_norm_cocompact_atTop.atTop_mul_const ha)
  have htend : Tendsto (cgf id ν) (cocompact ℝ) atTop :=
    tendsto_atTop_mono (fun t ↦ by
      simpa [Real.norm_eq_abs, c] using abs_mul_add_le_cgf ν hint hpos hneg t) hnorm
  exact (continuous_cgf_id ν hν hint).exists_forall_le htend

/-! ### Both half-lines carry mass -/

/-- Mass on the open positive half-line is seen by an interval `[1 / (k + 1), k + 1]`. -/
private lemma exists_measure_Icc_ne_zero (ρ : Measure ℝ) (h : ρ (Ioi 0) ≠ 0) :
    ∃ k : ℕ, ρ (Icc (1 / ((k : ℝ) + 1)) ((k : ℝ) + 1)) ≠ 0 := by
  by_contra! hcon
  apply h
  have hsub : Ioi (0 : ℝ) ⊆ ⋃ k : ℕ, Icc (1 / ((k : ℝ) + 1)) ((k : ℝ) + 1) := by
    intro y hy
    obtain ⟨k, hk⟩ := exists_nat_gt (max y (1 / y))
    refine mem_iUnion.mpr ⟨k, ?_, ?_⟩
    · have h1 : 1 / y < k + 1 := (le_max_right _ _).trans_lt (hk.trans (lt_add_one _))
      have h2 : 1 < (k + 1) * y := (div_lt_iff₀ (mem_Ioi.mp hy)).mp h1
      rw [div_le_iff₀ (by positivity)]
      linarith
    · linarith [le_max_left y (1 / y)]
  exact measure_mono_null hsub (measure_iUnion_null hcon)

/-- Mass on both open half-lines is seen by `[a, b]` and `[-b, -a]` for some `0 < a ≤ b`. -/
private lemma exists_Icc_pos (ρ : Measure ℝ) [IsFiniteMeasure ρ] (hpos : ρ (Ioi 0) ≠ 0)
    (hneg : ρ (Iio 0) ≠ 0) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ 0 < ρ.real (Icc a b) ∧ 0 < ρ.real (Icc (-b) (-a)) := by
  obtain ⟨k₁, hk₁⟩ := exists_measure_Icc_ne_zero ρ hpos
  have hneg' : ρ.map Neg.neg (Ioi 0) ≠ 0 := by
    rw [Measure.map_apply measurable_neg measurableSet_Ioi]
    convert hneg using 2
    ext y
    simp
  obtain ⟨k₂, hk₂⟩ := exists_measure_Icc_ne_zero _ hneg'
  rw [Measure.map_apply measurable_neg measurableSet_Icc] at hk₂
  set k := max k₁ k₂
  have hsub (j : ℕ) (hj : j ≤ k) :
      Icc (1 / ((j : ℝ) + 1)) ((j : ℝ) + 1) ⊆ Icc (1 / ((k : ℝ) + 1)) ((k : ℝ) + 1) := by
    have hjk : (j : ℝ) ≤ k := by exact_mod_cast hj
    exact Icc_subset_Icc (one_div_le_one_div_of_le (by positivity) (by linarith))
      (by linarith)
  refine ⟨1 / ((k : ℝ) + 1), (k : ℝ) + 1, by positivity, by positivity, ?_, ?_⟩
  · rw [measureReal_def]
    exact ENNReal.toReal_pos (fun h0 ↦ hk₁ (measure_mono_null (hsub k₁ (le_max_left _ _)) h0))
      (measure_ne_top _ _)
  · rw [measureReal_def]
    refine ENNReal.toReal_pos (fun h0 ↦ hk₂ (measure_mono_null ?_ h0)) (measure_ne_top _ _)
    have h := hsub k₂ (le_max_right _ _)
    intro y hy
    have hy' : -y ∈ Icc (1 / ((k : ℝ) + 1)) ((k : ℝ) + 1) := h hy
    exact ⟨by linarith [hy'.2], by linarith [hy'.1]⟩

/-- The cumulant generating function of a truncation, as an extended logarithm of a set
integral. -/
private lemma coe_cgf_restrict (ρ : Measure ℝ) [IsFiniteMeasure ρ] {M : ℝ}
    (hM : ρ (Icc (-M) M) ≠ 0) (t : ℝ) :
    ((cgf id (ρ.restrict (Icc (-M) M)) t : ℝ) : EReal) =
      ENNReal.log (∫⁻ y in Icc (-M) M, ENNReal.ofReal (Real.exp (t * y)) ∂ρ) := by
  have hν : ρ.restrict (Icc (-M) M) ≠ 0 := by rwa [Ne, Measure.restrict_eq_zero]
  have hint := integrable_exp_restrict ρ M t
  have hpos : 0 < ∫ y in Icc (-M) M, Real.exp (t * y) ∂ρ := mgf_pos' hν hint
  rw [← ofReal_integral_eq_lintegral_ofReal hint
      (Eventually.of_forall fun _ ↦ (Real.exp_pos _).le), ENNReal.log_ofReal_of_pos hpos]
  rfl

/-- Truncated cumulant generating functions increase with the truncation level. -/
private lemma cgf_restrict_mono (ρ : Measure ℝ) [IsFiniteMeasure ρ] {M M' : ℝ}
    (hM : ρ (Icc (-M) M) ≠ 0) (h : M ≤ M') (t : ℝ) :
    cgf id (ρ.restrict (Icc (-M) M)) t ≤ cgf id (ρ.restrict (Icc (-M') M')) t := by
  have hν : ρ.restrict (Icc (-M) M) ≠ 0 := by rwa [Ne, Measure.restrict_eq_zero]
  refine Real.log_le_log (mgf_pos' hν (integrable_exp_restrict ρ M t)) ?_
  exact setIntegral_mono_set (integrable_exp_restrict ρ M' t)
    (Eventually.of_forall fun _ ↦ (Real.exp_pos _).le)
    (Icc_subset_Icc (neg_le_neg h) h).eventuallyLE

/-- Truncated cumulant generating functions are nonpositive at the origin. -/
private lemma cgf_restrict_zero_nonpos (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (M : ℝ) :
    cgf id (ρ.restrict (Icc (-M) M)) 0 ≤ 0 := by
  rw [cgf_zero']
  refine Real.log_nonpos measureReal_nonneg ?_
  rw [measureReal_restrict_apply_univ]
  exact measureReal_le_one

/-- Truncated Laplace integrals converge to the full Laplace integral. -/
private lemma tendsto_lintegral_Icc (ρ : Measure ℝ) (B t : ℝ) (hB : 0 ≤ B) :
    Tendsto (fun m : ℕ ↦ ∫⁻ y in Icc (-((m : ℝ) + B)) ((m : ℝ) + B),
      ENNReal.ofReal (Real.exp (t * y)) ∂ρ) atTop
      (𝓝 (∫⁻ y, ENNReal.ofReal (Real.exp (t * y)) ∂ρ)) := by
  set f : ℝ → ℝ≥0∞ := fun y ↦ ENNReal.ofReal (Real.exp (t * y))
  have hmono : Monotone fun m : ℕ ↦ Icc (-((m : ℝ) + B)) ((m : ℝ) + B) := by
    intro m m' h
    have h' : (m : ℝ) ≤ m' := by exact_mod_cast h
    exact Icc_subset_Icc (by linarith) (by linarith)
  have hunion : (⋃ m : ℕ, Icc (-((m : ℝ) + B)) ((m : ℝ) + B)) = univ := by
    refine eq_univ_of_forall fun y ↦ mem_iUnion.mpr ?_
    obtain ⟨m, hm⟩ := exists_nat_ge |y|
    exact ⟨m, by linarith [neg_abs_le y], by linarith [le_abs_self y]⟩
  have h := tendsto_measure_iUnion_atTop (μ := ρ.withDensity f) hmono
  rw [hunion, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h
  refine h.congr fun m ↦ ?_
  simp only [Function.comp_apply]
  exact withDensity_apply _ measurableSet_Icc

/-- **Both half-lines carry mass.** The truncated minima bound the ball rate, and a compactness
argument passes to the full logarithmic Laplace transform. -/
private lemma iInf_logLaplace_le_ballRate_of_pos (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    {δ : ℝ} (hδ : 0 < δ) (hpos : ρ (Ioi 0) ≠ 0) (hneg : ρ (Iio 0) ≠ 0) :
    ⨅ t, logLaplace ρ t ≤ liminf (ballRate ρ δ) atTop := by
  obtain ⟨a, b, ha, hb, hP, hN⟩ := exists_Icc_pos ρ hpos hneg
  set N : ℕ → ℝ := fun m ↦ (m : ℝ) + b
  set L : ℕ → ℝ → ℝ := fun m ↦ cgf id (ρ.restrict (Icc (-N m) (N m)))
  set ℓ := liminf (ballRate ρ δ) atTop
  have hsub : ∀ m, Icc a b ⊆ Icc (-N m) (N m) ∧ Icc (-b) (-a) ⊆ Icc (-N m) (N m) := by
    intro m
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    exact ⟨Icc_subset_Icc (by simp only [N]; linarith) (by simp only [N]; linarith),
      Icc_subset_Icc (by simp only [N]; linarith) (by simp only [N]; linarith)⟩
  have hreal : ∀ m {s : Set ℝ}, MeasurableSet s → s ⊆ Icc (-N m) (N m) →
      (ρ.restrict (Icc (-N m) (N m))).real s = ρ.real s := fun m s hs hsm ↦ by
    rw [measureReal_restrict_apply hs, inter_eq_left.mpr hsm]
  have hPm : ∀ m, 0 < (ρ.restrict (Icc (-N m) (N m))).real (Icc a b) := fun m ↦ by
    rw [hreal m measurableSet_Icc (hsub m).1]
    exact hP
  have hNm : ∀ m, 0 < (ρ.restrict (Icc (-N m) (N m))).real (Icc (-b) (-a)) := fun m ↦ by
    rw [hreal m measurableSet_Icc (hsub m).2]
    exact hN
  have hM : ∀ m, ρ (Icc (-N m) (N m)) ≠ 0 := fun m h0 ↦ by
    have := measure_mono_null (hsub m).1 h0
    rw [measureReal_def, this] at hP
    simp at hP
  have hint : ∀ m t, Integrable (fun y ↦ Real.exp (t * y)) (ρ.restrict (Icc (-N m) (N m))) :=
    fun m ↦ integrable_exp_restrict ρ (N m)
  choose η hη using fun m ↦ exists_forall_cgf_le _ (hint m) ha (hPm m) (hNm m)
  have hηℓ : ∀ m, ((L m (η m) : ℝ) : EReal) ≤ ℓ := fun m ↦
    cgf_le_liminf_ballRate ρ hδ (hM m) (IsLocalMin.deriv_eq_zero (Eventually.of_forall (hη m)))
  have hmono : ∀ {m m'}, m ≤ m' → ∀ t, L m t ≤ L m' t := fun {m m'} h t ↦
    cgf_restrict_mono ρ (hM m) (by
      have h' : (m : ℝ) ≤ m' := by exact_mod_cast h
      simp only [N]
      linarith) t
  set c := min (Real.log ((ρ.restrict (Icc (-N 0) (N 0))).real (Icc a b)))
    (Real.log ((ρ.restrict (Icc (-N 0) (N 0))).real (Icc (-b) (-a))))
  have hbound : ∀ m, η m ∈ Icc (-(-c / a)) (-c / a) := fun m ↦ by
    have h1 := abs_mul_add_le_cgf _ (hint 0) (hPm 0) (hNm 0) (η m)
    have h2 : L 0 (η m) ≤ L m (η m) := hmono (Nat.zero_le m) (η m)
    have h3 : L m (η m) ≤ L m 0 := hη m 0
    have h4 : L m 0 ≤ 0 := cgf_restrict_zero_nonpos ρ (N m)
    have habs : |η m| ≤ -c / a := by
      rw [le_div_iff₀ ha]
      change |η m| * a + c ≤ L 0 (η m) at h1
      linarith
    exact abs_le.mp habs
  obtain ⟨η₀, -, φ, hφ, hlim⟩ := isCompact_Icc.tendsto_subseq hbound
  have hη₀ : ∀ m, ((L m η₀ : ℝ) : EReal) ≤ ℓ := by
    intro m
    have hcont : Continuous (L m) :=
      continuous_cgf_id _ (by rw [Ne, Measure.restrict_eq_zero]; exact hM m) (hint m)
    have hT : Tendsto (fun k ↦ ((L m (η (φ k)) : ℝ) : EReal)) atTop (𝓝 ((L m η₀ : ℝ) : EReal)) :=
      (continuous_coe_real_ereal.tendsto _).comp ((hcont.tendsto η₀).comp hlim)
    refine le_of_tendsto hT (eventually_atTop.2 ⟨m, fun k hk ↦ ?_⟩)
    exact (EReal.coe_le_coe_iff.mpr (hmono (hk.trans (hφ.id_le k)) (η (φ k)))).trans
      (hηℓ (φ k))
  have hlog : Tendsto (fun m : ℕ ↦ ((L m η₀ : ℝ) : EReal)) atTop (𝓝 (logLaplace ρ η₀)) := by
    have h := (ENNReal.continuous_log.tendsto _).comp (tendsto_lintegral_Icc ρ b η₀ hb.le)
    refine h.congr fun m ↦ ?_
    exact (coe_cgf_restrict ρ (hM m) η₀).symm
  exact (iInf_le _ η₀).trans (le_of_tendsto' hlog hη₀)

/-- The Cramér lower bound at the origin. -/
private lemma iInf_logLaplace_le_liminf_ballRate (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    {δ : ℝ} (hδ : 0 < δ) : ⨅ t, logLaplace ρ t ≤ liminf (ballRate ρ δ) atTop := by
  by_cases h : ρ (Iio 0) = 0 ∨ ρ (Ioi 0) = 0
  · exact iInf_logLaplace_le_ballRate_of_null ρ hδ h
  · obtain ⟨hneg, hpos⟩ := not_or.mp h
    exact iInf_logLaplace_le_ballRate_of_pos ρ hδ hpos hneg

/-! ### Centring -/

/-- Shifting the measure by `-x` multiplies the Laplace transform by `exp (-t x)`. -/
private lemma logLaplace_map_sub (ρ : Measure ℝ) (x t : ℝ) :
    logLaplace (ρ.map fun y ↦ y - x) t = logLaplace ρ t + ((-(t * x) : ℝ) : EReal) := by
  unfold logLaplace
  rw [lintegral_map (by fun_prop) (measurable_sub_const x)]
  have h : ∀ y : ℝ, ENNReal.ofReal (Real.exp (t * (y - x))) =
      ENNReal.ofReal (Real.exp (-(t * x))) * ENNReal.ofReal (Real.exp (t * y)) := by
    intro y
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2
    ring
  simp_rw [h]
  rw [lintegral_const_mul _ (by fun_prop), ENNReal.log_mul_add, add_comm,
    ENNReal.log_ofReal_of_pos (Real.exp_pos _), Real.log_exp]

/-- Shifting the measure by `-x` moves the ball around `x` to the ball around `0`. -/
private lemma piLaw_map_sub (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (x δ : ℝ) (n : ℕ) :
    piLaw (ρ.map fun y ↦ y - x) n {y | |meanFin n y| < δ} =
      piLaw ρ n {y | dist (meanFin n y) x < δ} := by
  have hpi : piLaw (ρ.map fun y ↦ y - x) n = (piLaw ρ n).map fun y i ↦ y i - x := by
    rw [piLaw, piLaw, Measure.pi_map_pi fun _ ↦ (measurable_sub_const x).aemeasurable]
  rw [hpi, Measure.map_apply (by fun_prop) (measurableSet_meanFin_lt n δ)]
  congr 1
  ext y
  have hmean : meanFin n (fun i ↦ y i - x) = meanFin n y - x := by
    simp only [meanFin, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    field_simp
    push_cast
    ring
  simp only [mem_preimage, mem_ofPred_eq, hmean, Real.dist_eq]

/-- Negation of an indexed supremum in `EReal`. -/
private lemma ereal_neg_iSup' {ι : Sort*} (f : ι → EReal) : - ⨆ i, f i = ⨅ i, - f i := by
  refine le_antisymm (le_iInf fun i ↦ EReal.neg_strictAnti.antitone (le_iSup f i)) ?_
  rw [← EReal.neg_le_neg_iff, neg_neg]
  refine iSup_le fun i ↦ ?_
  simpa using EReal.neg_strictAnti.antitone (iInf_le (fun j ↦ - f j) i)

/-- **Cramér lower bound (06.60).** For a probability measure `ρ` on `ℝ`, a point `x` and a
radius `δ > 0`, the probability under `ρ ^ (n + 1)` that the empirical mean lies within `δ` of
`x` is at least `exp (-(n + 1) (I x + o(1)))`, where
`I x = ⨆ t, (t x - log ∫ exp (t y) dρ(y))` with the logarithm taken in `[-∞, ∞]`. -/
theorem neg_iSup_sub_log_lintegral_le_liminf_log_pi (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    (x : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    -(⨆ t : ℝ, ((t * x : ℝ) : EReal) -
        ENNReal.log (∫⁻ y, ENNReal.ofReal (Real.exp (t * y)) ∂ρ)) ≤
      liminf (fun n : ℕ ↦ (((n + 1 : ℝ)⁻¹ : ℝ) : EReal) *
        ENNReal.log (Measure.pi (fun _ : Fin (n + 1) ↦ ρ)
          {y | dist ((n + 1 : ℝ)⁻¹ * ∑ i, y i) x < δ})) atTop := by
  have key := iInf_logLaplace_le_liminf_ballRate (ρ.map fun y ↦ y - x) hδ
  have hlhs : -(⨆ t : ℝ, ((t * x : ℝ) : EReal) - logLaplace ρ t) =
      ⨅ t, logLaplace (ρ.map fun y ↦ y - x) t := by
    rw [ereal_neg_iSup']
    congr 1
    ext t
    rw [logLaplace_map_sub, EReal.neg_sub (Or.inl (EReal.coe_ne_bot _))
      (Or.inl (EReal.coe_ne_top _)), ← EReal.coe_neg, add_comm]
  have hrhs : ballRate (ρ.map fun y ↦ y - x) δ = fun n : ℕ ↦ (((n + 1 : ℝ)⁻¹ : ℝ) : EReal) *
      ENNReal.log (Measure.pi (fun _ : Fin (n + 1) ↦ ρ)
        {y | dist ((n + 1 : ℝ)⁻¹ * ∑ i, y i) x < δ}) := by
    ext n
    rw [ballRate, piLaw_map_sub]
    rfl
  change -(⨆ t : ℝ, ((t * x : ℝ) : EReal) - logLaplace ρ t) ≤ _
  rw [hlhs, ← hrhs]
  exact key

end CKMA
