/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Complex.ExponentialBounds
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
the exponential square. Neither implication requires probability normalization. The converse
tail implication uses Mathlib's layer-cake formula and exponential integral. The converse moment
implication uses Mathlib's exponential series, a factorial estimate, and a geometric series.
The centered MGF bound uses Mathlib's global exponential Taylor remainder and Young's inequality.
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

/-- Layer cake bounds an exponential moment from a sufficiently fast exponential tail. -/
private lemma lintegral_exp_le_of_exp_tail [IsProbabilityMeasure μ]
    {Y : Ω → ℝ} (hm : Measurable Y) (hnonneg : ∀ ω, 0 ≤ Y ω)
    (htail : ∀ t : ℝ, 0 ≤ t → μ {ω | t < Y ω} ≤ ENNReal.ofReal (2 * Real.exp (-4 * t))) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp (Y ω)) ∂μ) ≤ 2 := by
  have hlayer := lintegral_comp_eq_lintegral_meas_lt_mul μ
    (Filter.Eventually.of_forall hnonneg) hm.aemeasurable
    (fun t _ ↦ Real.continuous_exp.intervalIntegrable 0 t)
    (Filter.Eventually.of_forall fun t : ℝ ↦ (Real.exp_pos t).le)
  simp only [integral_exp, Real.exp_zero] at hlayer
  have hdecay : (∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (2 * Real.exp (-3 * t))) =
      ENNReal.ofReal (2 / 3 : ℝ) := by
    rw [← ofReal_integral_eq_lintegral_ofReal
      ((integrableOn_exp_mul_Ioi (by norm_num : (-3 : ℝ) < 0) 0).const_mul 2)
      (Filter.Eventually.of_forall fun _ ↦ by positivity)]
    rw [integral_const_mul, integral_exp_mul_Ioi (by norm_num : (-3 : ℝ) < 0) 0]
    norm_num
  have hrem : (∫⁻ ω, ENNReal.ofReal (Real.exp (Y ω) - 1) ∂μ) ≤
      ENNReal.ofReal (2 / 3 : ℝ) := by
    rw [hlayer, ← hdecay]
    apply setLIntegral_mono' measurableSet_Ioi
    intro t ht
    calc
      μ {ω | t < Y ω} * ENNReal.ofReal (Real.exp t) ≤
          ENNReal.ofReal (2 * Real.exp (-4 * t)) * ENNReal.ofReal (Real.exp t) :=
        mul_le_mul_left (htail t ht.le) _
      _ = ENNReal.ofReal (2 * Real.exp (-3 * t)) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring
  have hsplit (ω : Ω) : ENNReal.ofReal (Real.exp (Y ω)) =
      1 + ENNReal.ofReal (Real.exp (Y ω) - 1) := by
    have he : 0 ≤ Real.exp (Y ω) - 1 := sub_nonneg.2 (Real.one_le_exp (hnonneg ω))
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one he]
    congr 1
    ring
  rw [lintegral_congr hsplit, lintegral_add_left measurable_const]
  have hc : ENNReal.ofReal (2 / 3 : ℝ) ≤ 1 := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by norm_num)
  simpa only [lintegral_const, measure_univ, mul_one, one_add_one_eq_two, add_comm] using
    add_le_add_left (hrem.trans hc) 1

/-- Gaussian tails give the exponential square condition at twice the scale. -/
theorem HasGaussianTail.hasPsiTwoBound [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hm : Measurable X) {K : ℝ} (h : HasGaussianTail X μ K) :
    HasPsiTwoBound X μ (2 * K) := by
  refine ⟨mul_pos (by norm_num) h.1, ?_⟩
  apply lintegral_exp_le_of_exp_tail ((hm.div_const (2 * K)).pow_const 2)
    (fun _ ↦ sq_nonneg _)
  intro t ht
  have hsub : {ω | t < (X ω / (2 * K)) ^ 2} ⊆ {ω | 2 * K * Real.sqrt t < |X ω|} := by
    intro ω hω
    change t < (X ω / (2 * K)) ^ 2 at hω
    have hs := Real.sq_sqrt ht
    have hK : 0 < 2 * K := mul_pos (by norm_num) h.1
    have hsq : (2 * K) ^ 2 * t < |X ω| ^ 2 := by
      rw [div_pow] at hω
      have hh := (lt_div_iff₀ (sq_pos_of_pos hK)).1 hω
      nlinarith [sq_abs (X ω)]
    apply (sq_lt_sq₀ (mul_nonneg hK.le (Real.sqrt_nonneg t)) (abs_nonneg _)).1
    simpa only [mul_pow, hs] using hsq
  calc
    μ {ω | t < (X ω / (2 * K)) ^ 2} ≤ μ {ω | 2 * K * Real.sqrt t < |X ω|} := measure_mono hsub
    _ ≤ ENNReal.ofReal (2 * Real.exp (-((2 * K * Real.sqrt t / K) ^ 2))) :=
      h.2 _ (mul_nonneg (mul_nonneg (by norm_num) h.1.le) (Real.sqrt_nonneg t))
    _ = ENNReal.ofReal (2 * Real.exp (-4 * t)) := by
      congr 3
      have hK := h.1.ne'
      field_simp
      nlinarith [Real.sq_sqrt ht]

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


/-- Real Gaussian moment growth bounds each natural absolute moment. -/
private lemma lintegral_pow_le_of_gaussianMoments {X : Ω → ℝ} (hm : Measurable X)
    {K : ℝ} (h : HasGaussianMoments X μ K) {m : ℕ} (hmpos : 0 < m) :
    (∫⁻ ω, ENNReal.ofReal (|X ω| ^ m) ∂μ) ≤
      ENNReal.ofReal ((K * Real.sqrt m) ^ m) := by
  have hm0 : 0 < (m : ℝ) := Nat.cast_pos.mpr hmpos
  have he := ENNReal.rpow_le_rpow (h.2 m (by exact_mod_cast hmpos)) hm0.le
  rw [eLpNorm_eq_eLpNorm' (by simpa using hmpos.ne') ENNReal.ofReal_ne_top
    hm.aestronglyMeasurable, ENNReal.toReal_ofReal hm0.le,
    ← lintegral_rpow_enorm_eq_rpow_eLpNorm' hm0] at he
  simpa only [ENNReal.rpow_natCast, Real.enorm_eq_ofReal_abs,
    ← ENNReal.ofReal_pow (abs_nonneg _),
    ← ENNReal.ofReal_pow (mul_nonneg h.1.le (Real.sqrt_nonneg _))] using he

/-- Factorials control the coefficients obtained by inserting Gaussian moment growth. -/
private lemma gaussian_moment_exp_coefficient_le (n : ℕ) :
    (n : ℝ) ^ n / n.factorial / 8 ^ n ≤ (1 / 2 : ℝ) ^ n := by
  calc
    (n : ℝ) ^ n / n.factorial / 8 ^ n ≤ Real.exp n / 8 ^ n :=
      div_le_div_of_nonneg_right (Real.pow_div_factorial_le_exp n (Nat.cast_nonneg n) n)
        (by positivity)
    _ ≤ (3 : ℝ) ^ n / 8 ^ n := by
      rw [show (n : ℝ) = n * 1 by ring, Real.exp_nat_mul]
      exact div_le_div_of_nonneg_right
        (pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le n) (by positivity)
    _ = (3 / 8 : ℝ) ^ n := (div_pow _ _ _).symm
    _ ≤ (1 / 2 : ℝ) ^ n := pow_le_pow_left₀ (by norm_num) (by norm_num) n

/-- Each integrated exponential coefficient is bounded by a geometric-series coefficient. -/
private lemma lintegral_exp_coefficient_le_of_gaussianMoments [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hm : Measurable X) {K : ℝ} (h : HasGaussianMoments X μ K) (n : ℕ) :
    (∫⁻ ω, ENNReal.ofReal (((X ω / (4 * K)) ^ 2) ^ n / n.factorial) ∂μ) ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ n) := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  have hKpos := h.1
  have hK := hKpos.ne'
  have hD : 0 < (4 * K) ^ (2 * n) * (n.factorial : ℝ) := by positivity
  have hpoint (ω : Ω) : ((X ω / (4 * K)) ^ 2) ^ n / n.factorial =
      |X ω| ^ (2 * n) / ((4 * K) ^ (2 * n) * (n.factorial : ℝ)) := by
    rw [← pow_mul, div_pow, div_div]
    congr 1
    rw [pow_mul, pow_mul, sq_abs]
  have hcalc : (K * Real.sqrt (2 * n)) ^ (2 * n) /
      ((4 * K) ^ (2 * n) * (n.factorial : ℝ)) =
      (n : ℝ) ^ n / n.factorial / 8 ^ n := by
    rw [pow_mul, mul_pow, Real.sq_sqrt (by positivity : 0 ≤ (2 * n : ℝ)), pow_mul]
    simp only [mul_pow]
    field_simp [hK]
    rw [← mul_pow]
    norm_num
  calc
    _ = (∫⁻ ω, ENNReal.ofReal (|X ω| ^ (2 * n)) ∂μ) /
        ENNReal.ofReal ((4 * K) ^ (2 * n) * (n.factorial : ℝ)) := by
      simp_rw [hpoint, ENNReal.ofReal_div_of_pos hD, div_eq_mul_inv]
      exact lintegral_mul_const' _ _ (by
        exact ENNReal.inv_ne_top.mpr (ENNReal.ofReal_ne_zero_iff.mpr hD))
    _ ≤ ENNReal.ofReal ((K * Real.sqrt (2 * n)) ^ (2 * n)) /
        ENNReal.ofReal ((4 * K) ^ (2 * n) * (n.factorial : ℝ)) := by
      apply ENNReal.div_le_div_right
      convert lintegral_pow_le_of_gaussianMoments hm h (m := 2 * n)
        (Nat.mul_pos (by decide : 0 < 2) hn) using 1
      norm_num
    _ = ENNReal.ofReal ((n : ℝ) ^ n / n.factorial / 8 ^ n) := by
      rw [← ENNReal.ofReal_div_of_pos hD, hcalc]
    _ ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ n) :=
      ENNReal.ofReal_le_ofReal (gaussian_moment_exp_coefficient_le n)

/-- Moment growth gives exponential square integrability, with a universal change of scale. -/
theorem HasGaussianMoments.hasPsiTwoBound [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hm : Measurable X) {K : ℝ} (h : HasGaussianMoments X μ K) :
    HasPsiTwoBound X μ (4 * K) := by
  refine ⟨mul_pos (by norm_num) h.1, ?_⟩
  have hseries (ω : Ω) : ENNReal.ofReal (Real.exp ((X ω / (4 * K)) ^ 2)) =
      ∑' n : ℕ, ENNReal.ofReal (((X ω / (4 * K)) ^ 2) ^ n / n.factorial) := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
    exact ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ by positivity)
      (Real.summable_pow_div_factorial _)
  have hmeas (n : ℕ) : Measurable
      (fun ω ↦ ENNReal.ofReal (((X ω / (4 * K)) ^ 2) ^ n / n.factorial)) :=
    Measurable.ennreal_ofReal
      ((((hm.div_const (4 * K)).pow_const 2).pow_const n).div_const n.factorial)
  rw [lintegral_congr hseries, lintegral_tsum (fun n ↦ (hmeas n).aemeasurable)]
  calc
    _ ≤ ∑' n : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ n) :=
      ENNReal.tsum_le_tsum (lintegral_exp_coefficient_le_of_gaussianMoments hm h)
    _ = 2 := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ by positivity)
        (summable_geometric_of_abs_lt_one (by norm_num : |(1 / 2 : ℝ)| < 1)),
        tsum_geometric_of_abs_lt_one (by norm_num : |(1 / 2 : ℝ)| < 1)]
      norm_num

/-- A global quadratic remainder bound for the real exponential. -/
private lemma abs_exp_sub_one_sub_le (u : ℝ) :
    |Real.exp u - 1 - u| ≤ u ^ 2 * Real.exp |u| := by
  have hrem := Complex.norm_exp_sub_sum_le_norm_mul_exp (u : ℂ) 2
  have hnorm : ‖Complex.exp (u : ℂ) -
      ∑ m ∈ Finset.range 2, (u : ℂ) ^ m / m.factorial‖ = |Real.exp u - 1 - u| := by
    have heq : Complex.exp (u : ℂ) -
        ∑ m ∈ Finset.range 2, (u : ℂ) ^ m / m.factorial = (Real.exp u - 1 - u : ℝ) := by
      push_cast
      simp [Finset.sum_range_succ, sub_add_eq_sub_sub]
    rw [heq, Complex.norm_real, Real.norm_eq_abs]
  rw [hnorm] at hrem
  simpa using hrem

/-- An exponential-linear function has an integrable quadratic-square remainder. -/
private lemma exp_mul_le_linear_add_exp_sq (s y : ℝ) :
    Real.exp (s * y) ≤ 1 + s * y +
      (2 * s ^ 2 * Real.exp (s ^ 2 / 2)) * Real.exp (y ^ 2) := by
  have hy : y ^ 2 ≤ 2 * Real.exp (y ^ 2 / 2) := by
    have he := Real.add_one_le_exp (y ^ 2 / 2)
    nlinarith
  have hprod : |s * y| ≤ s ^ 2 / 2 + y ^ 2 / 2 := by
    rw [abs_mul]
    nlinarith [sq_nonneg (|s| - |y|), sq_abs s, sq_abs y]
  have hrem : Real.exp (s * y) - 1 - s * y ≤
      (2 * s ^ 2 * Real.exp (s ^ 2 / 2)) * Real.exp (y ^ 2) := calc
    _ ≤ (s * y) ^ 2 * Real.exp |s * y| :=
      (le_abs_self _).trans (abs_exp_sub_one_sub_le _)
    _ ≤ (s ^ 2 * (2 * Real.exp (y ^ 2 / 2))) *
        Real.exp (s ^ 2 / 2 + y ^ 2 / 2) := by
      rw [mul_pow]
      gcongr
    _ = (2 * s ^ 2 * Real.exp (s ^ 2 / 2)) *
        (Real.exp (y ^ 2 / 2) * Real.exp (y ^ 2 / 2)) := by rw [Real.exp_add]; ring
    _ = _ := by
      rw [← Real.exp_add]
      congr 2
      ring
  linarith

/-- An admissible exponential-square bound gives integrability of its defining exponential. -/
theorem HasPsiTwoBound.integrable_exp_sq {X : Ω → ℝ} (hm : Measurable X)
    {K : ℝ} (h : HasPsiTwoBound X μ K) :
    Integrable (fun ω ↦ Real.exp ((X ω / K) ^ 2)) μ := by
  refine ⟨((hm.div_const K).pow_const 2).exp.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun _ ↦ (Real.exp_pos _).le)]
  exact h.2.trans_lt (by norm_num)

/-- An admissible exponential-square bound implies integrability of every linear exponential. -/
theorem HasPsiTwoBound.integrable_exp_mul {X : Ω → ℝ} (hm : Measurable X)
    {K : ℝ} (h : HasPsiTwoBound X μ K) (t : ℝ) :
    Integrable (fun ω ↦ Real.exp (t * X ω)) μ := by
  apply ((h.integrable_exp_sq hm).const_mul (Real.exp ((t * K) ^ 2 / 4))).mono'
    (hm.const_mul t).exp.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro ω
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hscale : t * K * (X ω / K) = t * X ω := by field_simp [h.1.ne']
  nlinarith [sq_nonneg (X ω / K - t * K / 2)]

/-- A quadratic exponential remainder is absorbed into a Gaussian exponential. -/
private lemma one_add_scaled_exp_sq_le (z : ℝ) (hz : 0 ≤ z) :
    1 + 4 * z * Real.exp (z / 2) ≤ Real.exp (8 * z) := by
  calc
    _ ≤ Real.exp (z / 2) * (1 + 4 * z) := by
      have he := Real.one_le_exp (by positivity : 0 ≤ z / 2)
      nlinarith
    _ ≤ Real.exp (z / 2) * Real.exp (4 * z) :=
      mul_le_mul_of_nonneg_left
        (by simpa only [add_comm] using Real.add_one_le_exp (4 * z)) (Real.exp_pos _).le
    _ = Real.exp (z / 2 + 4 * z) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (8 * z) := Real.exp_le_exp.mpr (by linarith)

/-- Centered exponential square control implies a sub-Gaussian MGF.
The numerical constant is deliberately nonoptimal. -/
theorem HasPsiTwoBound.hasSubgaussianMGF [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hm : Measurable X) (hc : ∫ ω, X ω ∂μ = 0)
    {K : ℝ} (h : HasPsiTwoBound X μ K) :
    HasSubgaussianMGF X (⟨16 * K ^ 2, by positivity⟩ : ℝ≥0) μ := by
  have hG := h.integrable_exp_sq hm
  have hGbound : (∫ ω, Real.exp ((X ω / K) ^ 2) ∂μ) ≤ 2 := by
    apply (ENNReal.ofReal_le_ofReal_iff (by norm_num : (0 : ℝ) ≤ 2)).1
    simpa only [ENNReal.ofReal_ofNat] using
      (ofReal_integral_eq_lintegral_ofReal hG
        (Filter.Eventually.of_forall fun _ ↦ (Real.exp_pos _).le)).trans_le h.2
  have hX : Integrable X μ := by
    apply memLp_one_iff_integrable.1
    change eLpNorm X 1 μ < ∞
    have hmom := (h.hasGaussianMoments hm).2 1 le_rfl
    simpa only [ENNReal.ofReal_one] using hmom.trans_lt ENNReal.ofReal_lt_top
  refine ⟨h.integrable_exp_mul hm, fun t ↦ ?_⟩
  let c := 2 * (t * K) ^ 2 * Real.exp ((t * K) ^ 2 / 2)
  have hcpos : 0 ≤ c := by dsimp [c]; positivity
  have h1 : Integrable (fun _ : Ω ↦ (1 : ℝ)) μ := integrable_const 1
  have htX : Integrable (fun ω ↦ t * X ω) μ := hX.const_mul t
  have h1t : Integrable (fun ω ↦ 1 + t * X ω) μ := h1.add htX
  have hctG : Integrable (fun ω ↦ c * Real.exp ((X ω / K) ^ 2)) μ := hG.const_mul c
  have hsum : Integrable
      (fun ω ↦ 1 + t * X ω + c * Real.exp ((X ω / K) ^ 2)) μ := h1t.add hctG
  change (∫ ω, Real.exp (t * X ω) ∂μ) ≤ _
  calc
    _ ≤ ∫ ω, 1 + t * X ω + c * Real.exp ((X ω / K) ^ 2) ∂μ := by
      apply integral_mono (h.integrable_exp_mul hm t) hsum
      intro ω
      have hpoint := exp_mul_le_linear_add_exp_sq (t * K) (X ω / K)
      have hscale : t * K * (X ω / K) = t * X ω := by field_simp [h.1.ne']
      simpa only [hscale] using hpoint
    _ = 1 + c * ∫ ω, Real.exp ((X ω / K) ^ 2) ∂μ := by
      rw [integral_add h1t hctG, integral_add h1 htX, integral_const,
        integral_const_mul, integral_const_mul, hc]
      simp
    _ ≤ 1 + c * 2 := add_le_add_right (mul_le_mul_of_nonneg_left hGbound hcpos) 1
    _ ≤ Real.exp (8 * (t * K) ^ 2) := by
      convert one_add_scaled_exp_sq_le ((t * K) ^ 2) (sq_nonneg _) using 1
      dsimp [c]
      ring
    _ = _ := by
      change Real.exp (8 * (t * K) ^ 2) = Real.exp ((16 * K ^ 2) * t ^ 2 / 2)
      congr 1
      ring

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
