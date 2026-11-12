/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Probability.InfinitelyDivisible.Basic
public import CKMA.Probability.InfinitelyDivisible.Exponent
public import CKMA.Probability.InfinitelyDivisible.CompoundPoisson
public import CKMA.Probability.InfinitelyDivisible.Convergence
public import Mathlib.Algebra.Order.Archimedean.Defs
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Laws with a prescribed Lévy exponent

A finite Lévy measure, compensated on `{|x| ≤ 1}`, together with a Gaussian factor, has
characteristic function `exp` of the Lévy–Khintchine exponent. Truncating a general Lévy measure
away from zero and passing to the limit produces a probability law with that exponent, and every
such law is infinitely divisible.
-/

@[expose] public section

noncomputable section

namespace CKMA

open MeasureTheory Complex Filter Topology ProbabilityTheory
open scoped BigOperators NNReal ENNReal MeasureTheory

/-- The truncation `x 1_{|x| ≤ 1}` used in the Lévy compensator. -/
def truncCompensator (x : ℝ) : ℝ :=
  if |x| ≤ 1 then x else 0

/-- The truncation `x 1_{|x| ≤ 1}` is Borel measurable. -/
lemma measurable_truncCompensator : Measurable truncCompensator := by
  have hset : MeasurableSet {x : ℝ | |x| ≤ 1} :=
    (isClosed_le continuous_norm continuous_const).measurableSet
  unfold truncCompensator
  exact Measurable.ite hset (by fun_prop) measurable_const

/-- The truncation `x 1_{|x| ≤ 1}` is integrable against every finite measure. -/
lemma integrable_truncCompensator {ν : Measure ℝ} [IsFiniteMeasure ν] :
    Integrable truncCompensator ν := by
  refine (integrable_const (1 : ℝ)).mono
    measurable_truncCompensator.aestronglyMeasurable ?_
  refine ae_of_all _ fun x => ?_
  simp only [Real.norm_eq_abs, abs_one]
  simp only [truncCompensator]
  by_cases hx : |x| ≤ 1
  · rw [ite_eq_left hx]
    exact hx
  · rw [ite_eq_right hx, abs_zero]
    exact zero_le_one

/-- The complex compensator `(I t)` times the truncation is integrable on a finite measure. -/
lemma integrable_complexCompensator {ν : Measure ℝ} [IsFiniteMeasure ν] (t : ℝ) :
    Integrable (fun x : ℝ => (I * t) * (truncCompensator x : ℂ)) ν := by
  have hmeas : AEStronglyMeasurable
      (fun x : ℝ => (I * t) * (truncCompensator x : ℂ)) ν :=
    (measurable_const.mul
      (continuous_ofReal.measurable.comp measurable_truncCompensator)).aestronglyMeasurable
  refine (integrable_const |t|).mono' hmeas ?_
  refine ae_of_all _ fun x => ?_
  have htrunc : |truncCompensator x| ≤ 1 := by
    simp only [truncCompensator]
    by_cases hx : |x| ≤ 1
    · simp [hx]
    · simp [hx]
  calc
    ‖(I * t) * (truncCompensator x : ℂ)‖ = |t| * |truncCompensator x| := by
      rw [norm_mul, norm_mul, norm_I, one_mul, norm_real, norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs]
    _ ≤ |t| := by
      have habs : 0 ≤ |t| := abs_nonneg t
      nlinarith [habs, htrunc]

/-- On a finite Lévy measure, removing the compensator recovers `exp(I t x) - 1`. -/
lemma integral_exp_sub_one_eq {ν : Measure ℝ} [IsFiniteMeasure ν] (hν : IsLevyMeasure ν)
    (t : ℝ) :
    ∫ x, exp (I * t * x) - 1 ∂ν =
      ∫ x, levyIntegrand t x ∂ν +
        I * t * ((∫ x, truncCompensator x ∂ν : ℝ) : ℂ) := by
  have hfun : (fun x : ℝ => exp (I * t * x) - 1) =
      fun x => levyIntegrand t x + (I * t) * (truncCompensator x : ℂ) := by
    ext x
    by_cases hx : |x| ≤ 1
    · simp [levyIntegrand, truncCompensator, hx]
    · simp [levyIntegrand, truncCompensator, hx]
  rw [hfun, integral_add (integrable_levyIntegrand hν t) (integrable_complexCompensator t),
    integral_const_mul, integral_complex_ofReal]

/-- Characteristic function of a Gaussian convolved with a finite-activity compound Poisson law. -/
lemma charFun_gaussian_conv_compoundPoisson {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hν : IsLevyMeasure ν) (a : ℝ≥0) (b : ℝ) (t : ℝ) :
    charFun ((gaussianReal (b - ∫ x, truncCompensator x ∂ν) a) ∗ compoundPoisson ν) t =
      exp (I * b * t - (a : ℂ) * (t : ℂ) ^ 2 / 2 + ∫ x, levyIntegrand t x ∂ν) := by
  have : IsProbabilityMeasure (compoundPoisson ν) := isProbabilityMeasure_compoundPoisson
  rw [charFun_conv, charFun_gaussianReal, charFun_compoundPoisson, ← exp_add]
  congr 1
  rw [integral_exp_sub_one_eq hν t]
  push_cast
  ring

/-- Jumps kept by the `k`-th truncation, namely `{|x| ≥ 1 / (k + 1)}`. -/
def truncSet (k : ℕ) : Set ℝ :=
  {x | 1 / ((k : ℝ) + 1) ≤ |x|}

/-- Lévy triplet with jumps restricted to `{|x| ≥ 1 / (k + 1)}`. -/
def LevyTriplet.trunc (L : LevyTriplet) (k : ℕ) : LevyTriplet where
  gaussianVariance := L.gaussianVariance
  drift := L.drift
  jumpMeasure := L.jumpMeasure.restrict (truncSet k)
  isLevyMeasure := by
    simpa [truncSet] using
      L.isLevyMeasure.restrict_abs_ge (ε := 1 / ((k : ℝ) + 1)) (by positivity)

/-- Each truncated jump measure is finite. -/
lemma isFiniteMeasure_trunc (L : LevyTriplet) (k : ℕ) :
    IsFiniteMeasure (L.trunc k).jumpMeasure := by
  rw [LevyTriplet.trunc]
  simpa [truncSet] using
    isFiniteMeasure_restrict_abs_ge L.isLevyMeasure
      (ε := 1 / ((k : ℝ) + 1)) (by positivity)

/-- Law of the Gaussian factor convolved with the compound Poisson law of the `k`-th truncation. -/
def LevyTriplet.truncLaw (L : LevyTriplet) (k : ℕ) : Measure ℝ :=
  (gaussianReal (L.drift - ∫ x, truncCompensator x ∂(L.trunc k).jumpMeasure)
      L.gaussianVariance) ∗
    @compoundPoisson (L.trunc k).jumpMeasure (isFiniteMeasure_trunc L k)

/-- The truncated finite-activity law is a probability measure. -/
lemma isProbabilityMeasure_truncLaw (L : LevyTriplet) (k : ℕ) :
    IsProbabilityMeasure (L.truncLaw k) := by
  have : IsFiniteMeasure (L.trunc k).jumpMeasure := isFiniteMeasure_trunc L k
  have : IsProbabilityMeasure (compoundPoisson (L.trunc k).jumpMeasure) :=
    isProbabilityMeasure_compoundPoisson
  simpa [LevyTriplet.truncLaw] using
    (inferInstance : IsProbabilityMeasure
      ((gaussianReal (L.drift - ∫ x, truncCompensator x ∂(L.trunc k).jumpMeasure)
          L.gaussianVariance) ∗
        compoundPoisson (L.trunc k).jumpMeasure))

/-- The truncated finite-activity law has the truncated Lévy exponent. -/
lemma charFun_truncLaw (L : LevyTriplet) (k : ℕ) (t : ℝ) :
    charFun (L.truncLaw k) t = exp ((L.trunc k).exponent t) := by
  have : IsFiniteMeasure (L.trunc k).jumpMeasure := isFiniteMeasure_trunc L k
  have : IsProbabilityMeasure (compoundPoisson (L.trunc k).jumpMeasure) :=
    isProbabilityMeasure_compoundPoisson
  simp only [LevyTriplet.truncLaw, LevyTriplet.exponent_eq_levyIntegrand, LevyTriplet.trunc]
  exact charFun_gaussian_conv_compoundPoisson (L.trunc k).isLevyMeasure
    L.gaussianVariance L.drift t

/-- Indicators of the truncations converge pointwise to the Lévy integrand. -/
lemma tendsto_truncIndicator_levyIntegrand (t x : ℝ) :
    Tendsto (fun k => (truncSet k).indicator (levyIntegrand t) x) atTop
      (𝓝 (levyIntegrand t x)) := by
  by_cases hx : x = 0
  · subst hx
    have hnot : ∀ k, (0 : ℝ) ∉ truncSet k := by
      intro k hk
      have hk' : 1 / ((k : ℝ) + 1) ≤ |(0 : ℝ)| := hk
      simp [abs_zero] at hk'
      linarith [show 0 < 1 / ((k : ℝ) + 1) by positivity]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards with k
    rw [Set.indicator_of_notMem (hnot k)]
    simp [levyIntegrand, exp_zero]
  · have hx0 : 0 < |x| := abs_pos.mpr hx
    have hmem : ∀ᶠ k in atTop, x ∈ truncSet k := by
      obtain ⟨N, hN⟩ := exists_nat_gt (1 / |x|)
      filter_upwards [eventually_ge_atTop N] with k hk
      have hk' : 1 / |x| < (k : ℝ) := lt_of_lt_of_le hN (Nat.cast_le.mpr hk)
      have hone : (1 : ℝ) < (k : ℝ) * |x| := (div_lt_iff₀ hx0).mp hk'
      have hden : 0 < (k : ℝ) + 1 := by positivity
      have hlt : 1 / ((k : ℝ) + 1) < |x| := by
        rw [div_lt_iff₀ hden]
        nlinarith
      simpa [truncSet] using (le_of_lt hlt)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hmem] with k hk
    rw [Set.indicator_of_mem hk]

/-- Integrals of the Lévy integrand against the truncations converge to the full integral. -/
lemma tendsto_integral_levyIntegrand_trunc (L : LevyTriplet) (t : ℝ) :
    Tendsto (fun k => ∫ x, levyIntegrand t x ∂(L.trunc k).jumpMeasure) atTop
      (𝓝 (∫ x, levyIntegrand t x ∂L.jumpMeasure)) := by
  have hs : ∀ k, MeasurableSet (truncSet k) := fun _ => measurableSet_abs_ge _
  have heq : ∀ k, ∫ x, levyIntegrand t x ∂(L.trunc k).jumpMeasure =
      ∫ x, (truncSet k).indicator (levyIntegrand t) x ∂L.jumpMeasure := by
    intro k
    rw [LevyTriplet.trunc, ← integral_indicator (hs k)]
  simp_rw [heq]
  refine tendsto_integral_of_dominated_convergence
      (fun x => (t ^ 2 / 2 + 2) * min 1 (x ^ 2)) ?meas ?int ?bound ?lim
  · intro k
    exact ((measurable_levyIntegrand t).indicator (hs k)).aestronglyMeasurable
  · exact (integrable_min_one_sq L.isLevyMeasure).const_mul (t ^ 2 / 2 + 2)
  · intro k
    refine ae_of_all _ fun x => ?_
    by_cases hx : x ∈ truncSet k
    · rw [Set.indicator_of_mem hx]
      exact norm_levyIntegrand_le t x
    · rw [Set.indicator_of_notMem hx, norm_zero]
      positivity
  · exact ae_of_all _ fun x => tendsto_truncIndicator_levyIntegrand t x

/-- Exponents of the truncated triplets converge pointwise to the full exponent. -/
lemma tendsto_exponent_trunc (L : LevyTriplet) (t : ℝ) :
    Tendsto (fun k => (L.trunc k).exponent t) atTop (𝓝 (L.exponent t)) := by
  have hexp : ∀ k, (L.trunc k).exponent t =
      I * L.drift * t - (L.gaussianVariance : ℂ) * (t : ℂ) ^ 2 / 2 +
        ∫ x, levyIntegrand t x ∂(L.trunc k).jumpMeasure :=
    fun k => LevyTriplet.exponent_eq_levyIntegrand (L.trunc k) t
  simp_rw [hexp, LevyTriplet.exponent_eq_levyIntegrand]
  exact tendsto_const_nhds.add (tendsto_integral_levyIntegrand_trunc L t)

/-- Some probability measure has characteristic function `exp` of the Lévy exponent. -/
lemma exists_charFun_eq_exp_exponent (L : LevyTriplet) :
    ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧ ∀ t, charFun μ t = exp (L.exponent t) := by
  have : ∀ k, IsProbabilityMeasure (L.truncLaw k) := fun k =>
    isProbabilityMeasure_truncLaw L k
  obtain ⟨μ, hμ, hchar⟩ := exists_isProbabilityMeasure_of_tendsto_charFun
      (μ := fun k => L.truncLaw k)
      (f := fun t => exp (L.exponent t))
      ((continuous_exp.comp L.continuous_exponent).continuousAt)
      (fun t => by
        simp_rw [fun k => charFun_truncLaw L k t]
        exact continuous_exp.continuousAt.tendsto.comp (tendsto_exponent_trunc L t))
  exact ⟨μ, hμ, fun t => congrFun hchar t⟩

/-- A probability whose characteristic function is `exp` of a Lévy exponent is infinitely
divisible. -/
lemma isInfinitelyDivisible_of_forall_charFun_eq_exp (L : LevyTriplet) {μ : Measure ℝ}
    [IsProbabilityMeasure μ] (hL : ∀ t, charFun μ t = exp (L.exponent t)) :
    IsInfinitelyDivisible μ := by
  refine ⟨inferInstance, ?_⟩
  intro n hn
  obtain ⟨ρ, hρ, hchar⟩ := exists_charFun_eq_exp_exponent (L.divNat n hn)
  have : IsProbabilityMeasure ρ := hρ
  have := isProbabilityMeasure_convolutionPower ρ n
  refine ⟨ρ, hρ, ?_⟩
  apply Measure.ext_of_charFun
  ext t
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [charFun_convolutionPower ρ n t, hchar t, LevyTriplet.exponent_divNat L hn t, hL t,
    ← exp_nat_mul]
  congr 1
  rw [mul_comm]
  exact div_mul_cancel₀ (L.exponent t) hnC

end CKMA
