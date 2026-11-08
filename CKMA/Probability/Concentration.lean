/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Sub-Gaussian gauges, Bernstein and dimension reduction (07.4, 07.6, 07.47)

`HasPsiTwoBound`, `HasGaussianTail` and `HasGaussianMoments` express the exponential,
tail and moment descriptions of a real sub-Gaussian random variable. The extended
nonnegative `psiTwoGauge` is infinite if no positive admissible scale exists.
The implication theorems compare these descriptions and Mathlib's sub-Gaussian MGF API.

The other main statements are Bernstein's inequality for independent centered variables
and the Johnson–Lindenstrauss finite-set embedding bound. Scale and probability
normalizations are explicit at the theorem interfaces. The exponential-square to tail
implication applies Markov's inequality; the moment implication compares powers directly with
the exponential square. Neither implication requires probability normalization.
-/

@[expose] public section

noncomputable section

namespace CKMA

open scoped NNReal ENNReal


open MeasureTheory ProbabilityTheory
open scoped BigOperators

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The exponential square condition defining an admissible positive sub-Gaussian scale. -/
def HasPsiTwoBound (X : Ω → ℝ) (μ : Measure Ω) (K : ℝ) : Prop :=
  0 < K ∧ (∫⁻ ω, ENNReal.ofReal (Real.exp ((X ω / K) ^ 2)) ∂μ) ≤ 2

/-- The sub-Gaussian Luxemburg gauge, with value `∞` if there is no admissible scale. -/
def psiTwoGauge (X : Ω → ℝ) (μ : Measure Ω) : ℝ≥0∞ :=
  sInf {s | ∃ K : ℝ, s = ENNReal.ofReal K ∧ HasPsiTwoBound X μ K}

/-- Gaussian two-sided tails at scale `K`. -/
def HasGaussianTail (X : Ω → ℝ) (μ : Measure Ω) (K : ℝ) : Prop :=
  0 < K ∧ ∀ t : ℝ, 0 ≤ t →
    μ {ω | t < |X ω|} ≤ ENNReal.ofReal (2 * Real.exp (-((t / K) ^ 2)))

/-- Square-root growth of all real moments of order at least one. -/
def HasGaussianMoments (X : Ω → ℝ) (μ : Measure Ω) (K : ℝ) : Prop :=
  0 < K ∧ ∀ p : ℝ, 1 ≤ p →
    eLpNorm X (ENNReal.ofReal p) μ ≤ ENNReal.ofReal (K * Real.sqrt p)

/-- An admissible scale bounds the Luxemburg gauge. -/
theorem HasPsiTwoBound.psiTwoGauge_le {X : Ω → ℝ} {K : ℝ}
    (h : HasPsiTwoBound X μ K) : psiTwoGauge X μ ≤ ENNReal.ofReal K :=
  sInf_le ⟨K, rfl, h⟩

/-- **07.4**: scalar Bernstein inequality for independent bounded centered summands. -/
theorem bernstein [IsProbabilityMeasure μ] {n : ℕ} (X : Fin n → Ω → ℝ)
    (hm : ∀ i, Measurable (X i)) (hi : iIndepFun X μ)
    (hc : ∀ i, ∫ ω, X i ω ∂μ = 0) {b t : ℝ} (hb : 0 ≤ b) (ht : 0 ≤ t)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ b) :
    μ {ω | t ≤ |∑ i, X i ω|} ≤ ENNReal.ofReal
      (2 * Real.exp (-(t ^ 2 / (2 * ((∑ i, ∫ ω, (X i ω) ^ 2 ∂μ) + b * t / 3))))) := by
  sorry

/-- **07.6**: exponential square control implies Gaussian tails, without centering. -/
theorem HasPsiTwoBound.hasGaussianTail
    {X : Ω → ℝ} (hm : Measurable X) {K : ℝ} (h : HasPsiTwoBound X μ K) :
    HasGaussianTail X μ K := by
  refine ⟨h.1, fun t ht ↦ ?_⟩
  have hmeas : Measurable (fun ω ↦ ENNReal.ofReal (Real.exp ((X ω / K) ^ 2))) :=
    ((hm.div_const K).pow_const 2).exp.ennreal_ofReal
  have hsub : {ω | t < |X ω|} ⊆
      {ω | ENNReal.ofReal (Real.exp ((t / K) ^ 2)) ≤
        ENNReal.ofReal (Real.exp ((X ω / K) ^ 2))} := by
    intro ω hω
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    simpa only [div_pow, sq_abs] using
      (sq_le_sq₀ (div_nonneg ht h.1.le) (div_nonneg (abs_nonneg _) h.1.le)).2
        (div_le_div_of_nonneg_right hω.le h.1.le)
  calc
    μ {ω | t < |X ω|} ≤ μ {ω | ENNReal.ofReal (Real.exp ((t / K) ^ 2)) ≤
        ENNReal.ofReal (Real.exp ((X ω / K) ^ 2))} := measure_mono hsub
    _ ≤ (∫⁻ ω, ENNReal.ofReal (Real.exp ((X ω / K) ^ 2)) ∂μ) /
        ENNReal.ofReal (Real.exp ((t / K) ^ 2)) :=
      meas_ge_le_lintegral_div hmeas.aemeasurable
        (ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)) ENNReal.ofReal_ne_top
    _ ≤ 2 / ENNReal.ofReal (Real.exp ((t / K) ^ 2)) := ENNReal.div_le_div_right h.2 _
    _ = ENNReal.ofReal (2 * Real.exp (-((t / K) ^ 2))) := by
      rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_div_of_pos (Real.exp_pos _)]
      congr 1
      rw [div_eq_mul_inv, ← Real.exp_neg]

/-- Gaussian tails give the exponential square condition at twice the scale. -/
theorem HasGaussianTail.hasPsiTwoBound [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hm : Measurable X) {K : ℝ} (h : HasGaussianTail X μ K) :
    HasPsiTwoBound X μ (2 * K) := by
  sorry

/-- The exponential square dominates each real power at its square-root moment scale. -/
private lemma rpow_le_scaled_exp_sq (r K p : ℝ) (hr : 0 ≤ r) (hK : 0 < K) (hp : 1 ≤ p) :
    r ^ p ≤ (K * Real.sqrt p) ^ p * Real.exp ((r / K) ^ 2) := by
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  have ha : 0 < K * Real.sqrt p := mul_pos hK (Real.sqrt_pos.2 hp0)
  have hz : 0 ≤ r / (K * Real.sqrt p) := div_nonneg hr ha.le
  have hpow : (r / (K * Real.sqrt p)) ^ p ≤
      Real.exp (p * (r / (K * Real.sqrt p)) ^ 2) := by
    rcases eq_or_lt_of_le hz with hz0 | hz0
    · rw [← hz0, Real.zero_rpow (ne_of_gt hp0)]
      positivity
    · rw [Real.rpow_def_of_pos hz0]
      apply Real.exp_le_exp.mpr
      have hlog := Real.log_le_sub_one_of_pos hz0
      have hlog' : Real.log (r / (K * Real.sqrt p)) ≤ (r / (K * Real.sqrt p)) ^ 2 := by
        nlinarith [sq_nonneg (r / (K * Real.sqrt p) - 1 / 2)]
      nlinarith [mul_le_mul_of_nonneg_left hlog' hp0.le]
  have heq : p * (r / (K * Real.sqrt p)) ^ 2 = (r / K) ^ 2 := by
    rw [div_pow, mul_pow, Real.sq_sqrt hp0.le, div_pow]
    field_simp
  rw [heq, Real.div_rpow hr ha.le] at hpow
  simpa only [mul_comm] using (div_le_iff₀ (Real.rpow_pos_of_pos ha p)).1 hpow


/-- Exponential square control implies square-root moment growth, without probability
normalization. -/
theorem HasPsiTwoBound.hasGaussianMoments
    {X : Ω → ℝ} (hm : Measurable X) {K : ℝ} (h : HasPsiTwoBound X μ K) :
    HasGaussianMoments X μ (2 * K) := by
  refine ⟨mul_pos (by norm_num) h.1, fun p hp => ?_⟩
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  have ha : 0 < K * Real.sqrt p := mul_pos h.1 (Real.sqrt_pos.2 hp0)
  have hI : (∫⁻ ω, ‖X ω‖ₑ ^ p ∂μ) ≤
      ENNReal.ofReal ((K * Real.sqrt p) ^ p) * 2 := by
    calc
      _ ≤ ∫⁻ ω, ENNReal.ofReal ((K * Real.sqrt p) ^ p) *
          ENNReal.ofReal (Real.exp ((X ω / K) ^ 2)) ∂μ := by
        apply lintegral_mono
        intro ω
        dsimp only
        rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp0.le,
          ← ENNReal.ofReal_mul (Real.rpow_nonneg ha.le p)]
        apply ENNReal.ofReal_le_ofReal
        simpa only [div_pow, sq_abs] using rpow_le_scaled_exp_sq |X ω| K p (abs_nonneg _) h.1 hp
      _ = ENNReal.ofReal ((K * Real.sqrt p) ^ p) *
          ∫⁻ ω, ENNReal.ofReal (Real.exp ((X ω / K) ^ 2)) ∂μ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ _ := by gcongr; exact h.2
  have htwo : (2 : ℝ) ≤ 2 ^ p := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hp
  have hbound : ENNReal.ofReal ((K * Real.sqrt p) ^ p) * 2 ≤
      ENNReal.ofReal (2 * K * Real.sqrt p) ^ p := by
    rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (Real.rpow_nonneg ha.le p),
      ENNReal.ofReal_rpow_of_nonneg (by nlinarith [ha]) hp0.le]
    apply ENNReal.ofReal_le_ofReal
    rw [show 2 * K * Real.sqrt p = 2 * (K * Real.sqrt p) by ring,
      Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) ha.le]
    nlinarith [Real.rpow_nonneg ha.le p,
      mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg ha.le p)]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
    (ENNReal.ofReal_ne_zero_iff.2 hp0) ENNReal.ofReal_ne_top hm.aestronglyMeasurable,
    ENNReal.toReal_ofReal hp0.le]
  calc
    _ ≤ (ENNReal.ofReal (2 * K * Real.sqrt p) ^ p) ^ (1 / p) :=
      ENNReal.rpow_le_rpow (hI.trans hbound) (by positivity)
    _ = _ := by rw [← ENNReal.rpow_mul]; simp [ne_of_gt hp0]


/-- Moment growth gives exponential square integrability, with a universal change of scale. -/
theorem HasGaussianMoments.hasPsiTwoBound [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hm : Measurable X) {K : ℝ} (h : HasGaussianMoments X μ K) :
    HasPsiTwoBound X μ (4 * K) := by
  sorry

/-- Centered exponential square control implies a sub-Gaussian MGF.
The numerical constant is deliberately nonoptimal. -/
theorem HasPsiTwoBound.hasSubgaussianMGF [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hm : Measurable X) (hc : ∫ ω, X ω ∂μ = 0)
    {K : ℝ} (h : HasPsiTwoBound X μ K) :
    HasSubgaussianMGF X (⟨16 * K ^ 2, by positivity⟩ : ℝ≥0) μ := by
  sorry

/-- **07.47**: Johnson–Lindenstrauss, with a constant uniform in dimensions and points.
The `max N 1` convention includes the empty configuration. -/
theorem johnson_lindenstrauss : ∃ C : ℝ, 0 < C ∧
    ∀ (d N : ℕ) (x : Fin N → EuclideanSpace ℝ (Fin d)) (ε : ℝ), 0 < ε → ε < 1 →
    ∃ (m : ℕ) (T : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)),
      (m : ℝ) ≤ C * ε⁻¹ ^ 2 * Real.log (2 * (max N 1 : ℕ)) ∧
      ∀ i j, (1 - ε) * ‖x i - x j‖ ^ 2 ≤ ‖T (x i - x j)‖ ^ 2 ∧
        ‖T (x i - x j)‖ ^ 2 ≤ (1 + ε) * ‖x i - x j‖ ^ 2 := by
  sorry

end CKMA
