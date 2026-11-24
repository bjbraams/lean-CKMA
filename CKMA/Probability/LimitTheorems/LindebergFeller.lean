/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.Probability.Independence.CharacteristicFunction
import TauCeti.Analysis.Normed.Ring.ProdSubProd
import TauCeti.MeasureTheory.Function.LpSeminorm.Truncation
import TauCeti.Probability.CentralLimitTheorem.Lindeberg
import CKMA.Probability.LimitTheorems.ThreeSeries

/-!
# Feller's converse to the Lindeberg–Feller theorem

Let `Y n i`, `i : ι n`, be a row-independent triangular array of centred square-integrable real
random variables whose second moments sum to `1` in every row. If no single second moment
contributes a positive fraction of the row sum (Feller's condition) and the row sums converge in
distribution to the standard Gaussian law, then the Lindeberg condition holds.

The proof follows Billingsley, *Probability and Measure*, Section 27. Writing `φᵢ` for the
characteristic functions of a row at a fixed frequency `t`, Feller's condition makes
`∏ᵢ φᵢ` asymptotically equal to `∏ᵢ exp (φᵢ - 1)`, whose norm is `exp (∑ᵢ Re (φᵢ - 1))`.
Hence `∑ᵢ E[1 - cos (t Yᵢ)] → t² / 2`, and the elementary bound
`y² 1{ε ≤ |y|} ≤ t² y² / 2 - (1 - cos (t y))` for `t² = 2 + 4 / ε²` gives the Lindeberg sum.

## Main results

* `CKMA.tendsto_sum_integral_cos_sub_one_of_feller`: the real parts of `φᵢ - 1` sum to `-t²/2`.
* `CKMA.lindeberg_of_feller_of_tendstoInDistribution`: Feller's theorem for normalized rows.
* `CKMA.lindeberg_of_feller_of_tendstoInDistribution_div_sqrt`: the same statement for an
  unnormalized array divided by the square root of the row second-moment sum.
-/

public section

noncomputable section

namespace CKMA

open MeasureTheory ProbabilityTheory Filter Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ι : ℕ → Type*} [∀ n, Fintype (ι n)]

/-- Under Feller's condition and the central limit theorem, `∑ᵢ (E[cos (t Y n i)] - 1)` tends
to `-t² / 2` for every frequency `t`. -/
theorem tendsto_sum_integral_cos_sub_one_of_feller {Y : ∀ n, ι n → Ω → ℝ}
    (hi : ∀ n, iIndepFun (Y n) μ) (hL2 : ∀ n i, MemLp (Y n i) 2 μ)
    (h0 : ∀ n i, μ[Y n i] = 0) (hvar : ∀ n, ∑ i, ∫ ω, Y n i ω ^ 2 ∂μ = 1)
    (hF : ∀ δ > 0, ∀ᶠ n in atTop, ∀ i, ∫ ω, Y n i ω ^ 2 ∂μ < δ)
    (hclt : TendstoInDistribution (fun n ω ↦ ∑ i, Y n i ω) atTop id (fun _ ↦ μ)
      (gaussianReal 0 1))
    (t : ℝ) :
    Tendsto (fun n ↦ ∑ i, (∫ ω, Real.cos (t * Y n i ω) ∂μ - 1)) atTop (𝓝 (-(t ^ 2 / 2))) := by
  set φ : ∀ n, ι n → ℂ := fun n i ↦ charFun (μ.map (Y n i)) t with hφ
  set σ : ∀ n, ι n → ℝ := fun n i ↦ ∫ ω, Y n i ω ^ 2 ∂μ with hσ
  set C := 3 / 2 * t ^ 2
  have hC0 : 0 ≤ C := by positivity
  have hσ0 n i : 0 ≤ σ n i := integral_nonneg fun ω ↦ sq_nonneg _
  have hYm n i : AEMeasurable (Y n i) μ := (hL2 n i).aestronglyMeasurable.aemeasurable
  -- each factor is close to `1`
  have hz n i : ‖φ n i - 1‖ ≤ C * σ n i := by
    have h := (hL2 n i).norm_charFun_sub_one_sub_le (h0 n i) t le_rfl
    have hind : ∫ ω, ({ω | (0 : ℝ) ≤ |Y n i ω|}.indicator fun ω ↦ Y n i ω ^ 2) ω ∂μ =
        σ n i := by
      simp [hσ]
    rw [hind] at h
    simp only [mul_zero, zero_div, zero_mul, zero_add] at h
    have hq : ‖(t : ℂ) ^ 2 * (σ n i : ℂ) / 2‖ = t ^ 2 * σ n i / 2 := by
      rw [show (t : ℂ) ^ 2 * (σ n i : ℂ) / 2 = ((t ^ 2 * σ n i / 2 : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_of_nonneg (by have := hσ0 n i; positivity)]
    calc ‖φ n i - 1‖ = ‖(φ n i - (1 - (t : ℂ) ^ 2 * (σ n i : ℂ) / 2)) -
          (t : ℂ) ^ 2 * (σ n i : ℂ) / 2‖ := by ring_nf
      _ ≤ ‖φ n i - (1 - (t : ℂ) ^ 2 * (σ n i : ℂ) / 2)‖ +
          ‖(t : ℂ) ^ 2 * (σ n i : ℂ) / 2‖ := norm_sub_le _ _
      _ ≤ t ^ 2 * σ n i + t ^ 2 * σ n i / 2 := by rw [hq]; exact add_le_add_left h _
      _ = C * σ n i := by ring
  -- the product of the factors is the characteristic function of the row sum
  have hlim : Tendsto (fun n ↦ ∏ i, φ n i) atTop (𝓝 (Real.exp (-(t ^ 2 / 2)) : ℂ)) := by
    have h := hclt.tendsto_charFun t
    have hprod n : charFun (μ.map fun ω ↦ ∑ i, Y n i ω) t = ∏ i, φ n i := by
      rw [(hi n).charFun_map_fun_sum_eq_prod (hYm n), Finset.prod_apply]
    simp only [hprod, Measure.map_id, charFun_gaussianReal] at h
    convert h using 2
    push_cast
    ring_nf
  -- comparison with `∏ exp (φ - 1)`
  set w : ∀ n, ι n → ℂ := fun n i ↦ Complex.exp (φ n i - 1) with hw
  have hw1 n i : ‖w n i‖ ≤ 1 := by
    rw [hw, Complex.norm_exp, Real.exp_le_one_iff, Complex.sub_re, Complex.one_re, sub_nonpos]
    exact (Complex.re_le_norm _).trans (norm_charFun_le_one t)
  have hφ1 n i : ‖φ n i‖ ≤ 1 := norm_charFun_le_one t
  have hsmall : Tendsto (fun n ↦ ∑ i, ‖φ n i - w n i‖) atTop (𝓝 0) := by
    rw [tendsto_order]
    refine ⟨fun a ha ↦ Eventually.of_forall fun n ↦
      ha.trans_le (Finset.sum_nonneg fun i _ ↦ norm_nonneg _), fun η hη ↦ ?_⟩
    set δ := min (1 / (C + 1)) (η / (C ^ 2 + 1)) with hδ
    have hδ0 : 0 < δ := lt_min (by positivity) (by positivity)
    filter_upwards [hF δ hδ0] with n hn
    have hi' i : ‖φ n i - w n i‖ ≤ C ^ 2 * δ * σ n i := by
      have hzi : ‖φ n i - 1‖ ≤ C * δ := (hz n i).trans (by gcongr; exact (hn i).le)
      have hCδ : C * δ ≤ 1 := by
        calc C * δ ≤ C * (1 / (C + 1)) := by gcongr; exact min_le_left _ _
          _ ≤ 1 := by rw [mul_one_div, div_le_one (by positivity)]; linarith
      have hexp := Complex.norm_exp_sub_one_sub_id_le (hzi.trans hCδ)
      rw [show φ n i - w n i = -(Complex.exp (φ n i - 1) - 1 - (φ n i - 1)) by
        simp only [hw]; ring, norm_neg]
      calc _ ≤ ‖φ n i - 1‖ ^ 2 := hexp
        _ = ‖φ n i - 1‖ * ‖φ n i - 1‖ := sq _
        _ ≤ (C * σ n i) * (C * δ) := mul_le_mul (hz n i) hzi (norm_nonneg _) (by positivity)
        _ = C ^ 2 * δ * σ n i := by ring
    calc ∑ i, ‖φ n i - w n i‖ ≤ ∑ i, C ^ 2 * δ * σ n i := Finset.sum_le_sum fun i _ ↦ hi' i
      _ = C ^ 2 * δ := by rw [← Finset.mul_sum, hvar n, mul_one]
      _ ≤ C ^ 2 * (η / (C ^ 2 + 1)) := by gcongr; exact min_le_right _ _
      _ < η := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith
  have hnorm : Tendsto (fun n ↦ ‖∏ i, w n i‖) atTop (𝓝 (Real.exp (-(t ^ 2 / 2)))) := by
    have h1 : Tendsto (fun n ↦ ‖∏ i, φ n i‖) atTop (𝓝 (Real.exp (-(t ^ 2 / 2)))) := by
      have := (continuous_norm.tendsto _).comp hlim
      rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le] at this
      exact this
    have h2 : Tendsto (fun n ↦ ‖∏ i, φ n i‖ - ‖∏ i, w n i‖) atTop (𝓝 0) := by
      refine squeeze_zero_norm (fun n ↦ ?_) hsmall
      rw [Real.norm_eq_abs]
      exact (abs_norm_sub_norm_le _ _).trans
        (TauCeti.norm_prod_sub_prod_le_sum_norm_sub _ (fun i _ ↦ hφ1 n i) fun i _ ↦ hw1 n i)
    simpa using h1.sub h2
  have hlog := (Real.continuousAt_log (Real.exp_pos _).ne').tendsto.comp hnorm
  rw [Real.log_exp] at hlog
  refine hlog.congr fun n ↦ ?_
  simp only [Function.comp_apply, hw, norm_prod, Complex.norm_exp, ← Real.exp_sum,
    Real.log_exp]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Complex.sub_re, Complex.one_re, hφ, charFun_map_re (hYm n i)]

/-- **Feller's theorem.** For a row-independent array of centred square-integrable random
variables whose second moments sum to `1` in every row, Feller's condition together with
convergence of the row sums to the standard Gaussian law implies the Lindeberg condition. -/
theorem lindeberg_of_feller_of_tendstoInDistribution {Y : ∀ n, ι n → Ω → ℝ}
    (hi : ∀ n, iIndepFun (Y n) μ) (hL2 : ∀ n i, MemLp (Y n i) 2 μ)
    (h0 : ∀ n i, μ[Y n i] = 0) (hvar : ∀ n, ∑ i, ∫ ω, Y n i ω ^ 2 ∂μ = 1)
    (hF : ∀ δ > 0, ∀ᶠ n in atTop, ∀ i, ∫ ω, Y n i ω ^ 2 ∂μ < δ)
    (hclt : TendstoInDistribution (fun n ω ↦ ∑ i, Y n i ω) atTop id (fun _ ↦ μ)
      (gaussianReal 0 1)) :
    ∀ ε > 0, Tendsto (fun n ↦ ∑ i,
      ∫ ω, {ω | ε ≤ |Y n i ω|}.indicator (fun ω ↦ Y n i ω ^ 2) ω ∂μ) atTop (𝓝 0) := by
  intro ε hε
  set t := Real.sqrt (2 + 4 / ε ^ 2)
  have ht2 : t ^ 2 = 2 + 4 / ε ^ 2 := Real.sq_sqrt (by positivity)
  have hA := tendsto_sum_integral_cos_sub_one_of_feller hi hL2 h0 hvar hF hclt t
  have hpt : ∀ y : ℝ, {y : ℝ | ε ≤ |y|}.indicator (fun y ↦ y ^ 2) y ≤
      t ^ 2 / 2 * y ^ 2 + (Real.cos (t * y) - 1) := by
    intro y
    by_cases hy : ε ≤ |y|
    · rw [Set.indicator_of_mem (by exact hy)]
      have hy2 : ε ^ 2 ≤ y ^ 2 := by
        rw [← sq_abs y]
        exact pow_le_pow_left₀ hε.le hy 2
      have h4 : 2 ≤ 2 / ε ^ 2 * y ^ 2 := by
        rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
        linarith
      have hc := Real.neg_one_le_cos (t * y)
      rw [ht2]
      have : (2 + 4 / ε ^ 2) / 2 * y ^ 2 = y ^ 2 + 2 / ε ^ 2 * y ^ 2 := by ring
      linarith
    · rw [Set.indicator_of_notMem (by exact hy)]
      have := Real.one_sub_sq_div_two_le_cos (x := t * y)
      nlinarith
  refine squeeze_zero (fun n ↦ Finset.sum_nonneg fun i _ ↦
    integral_nonneg fun ω ↦ Set.indicator_nonneg (fun _ _ ↦ sq_nonneg _) _) (fun n ↦ ?_)
    (by have := (tendsto_const_nhds (x := t ^ 2 / 2)).add hA; rwa [add_neg_cancel] at this)
  have hcos n i : Integrable (fun ω ↦ Real.cos (t * Y n i ω)) μ :=
    Integrable.of_bound
      (Real.continuous_cos.comp_aestronglyMeasurable
        ((hL2 n i).aestronglyMeasurable.const_mul t)) 1
      (ae_of_all _ fun ω ↦ by simpa [Real.norm_eq_abs] using Real.abs_cos_le_one _)
  calc ∑ i, ∫ ω, {ω | ε ≤ |Y n i ω|}.indicator (fun ω ↦ Y n i ω ^ 2) ω ∂μ
      ≤ ∑ i, (t ^ 2 / 2 * ∫ ω, Y n i ω ^ 2 ∂μ + (∫ ω, Real.cos (t * Y n i ω) ∂μ - 1)) := by
        refine Finset.sum_le_sum fun i _ ↦ ?_
        have hcs : Integrable (fun ω ↦ Real.cos (t * Y n i ω) - 1) μ :=
          (hcos n i).sub (integrable_const 1)
        have hint : Integrable (fun ω ↦ t ^ 2 / 2 * Y n i ω ^ 2 +
            (Real.cos (t * Y n i ω) - 1)) μ :=
          ((hL2 n i).integrable_sq.const_mul (t ^ 2 / 2)).add hcs
        refine (integral_mono ((hL2 n i).integrable_indicator_sq ε) hint
          fun ω ↦ hpt (Y n i ω)).trans_eq ?_
        rw [integral_add ((hL2 n i).integrable_sq.const_mul _) hcs, integral_const_mul,
          integral_sub (hcos n i) (integrable_const 1)]
        simp
    _ = t ^ 2 / 2 + ∑ i, (∫ ω, Real.cos (t * Y n i ω) ∂μ - 1) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, hvar n, mul_one]

/-- **Feller's theorem**, unnormalized form. Let `X n i` be a row-independent array of centred
square-integrable random variables with positive row second-moment sums `vₙ`. If
`E[X n i ^ 2] / vₙ → 0` uniformly in `i` and `(∑ᵢ X n i) / √vₙ` converges in distribution to the
standard Gaussian law, then `vₙ⁻¹ ∑ᵢ E[X n i ^ 2; ε √vₙ < |X n i|] → 0` for every `ε > 0`. -/
theorem lindeberg_of_feller_of_tendstoInDistribution_div_sqrt {X : ∀ n, ι n → Ω → ℝ}
    (hi : ∀ n, iIndepFun (X n) μ) (hLp : ∀ n i, MemLp (X n i) 2 μ)
    (hc : ∀ n i, ∫ ω, X n i ω ∂μ = 0) (hv : ∀ n, 0 < ∑ i, ∫ ω, (X n i ω) ^ 2 ∂μ)
    (hF : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ i,
      (∫ ω, (X n i ω) ^ 2 ∂μ) / (∑ j, ∫ ω, (X n j ω) ^ 2 ∂μ) < ε)
    (hclt : TendstoInDistribution
      (fun n ω ↦ (∑ i, X n i ω) / Real.sqrt (∑ j, ∫ ω, (X n j ω) ^ 2 ∂μ)) atTop id
      (fun _ ↦ μ) (gaussianReal 0 1)) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n ↦ (∑ j, ∫ ω, (X n j ω) ^ 2 ∂μ)⁻¹ *
      ∑ i, ∫ ω, if ε * Real.sqrt (∑ j, ∫ ω, (X n j ω) ^ 2 ∂μ) < |X n i ω|
        then (X n i ω) ^ 2 else 0 ∂μ) atTop (𝓝 0) := by
  obtain ⟨v, hvv⟩ : ∃ v : ℕ → ℝ, v = fun n ↦ ∑ j, ∫ ω, (X n j ω) ^ 2 ∂μ := ⟨_, rfl⟩
  have hv' n : 0 < v n := by rw [hvv]; exact hv n
  have hs n : 0 < Real.sqrt (v n) := Real.sqrt_pos.2 (hv' n)
  have hsq n : Real.sqrt (v n) ^ 2 = v n := Real.sq_sqrt (hv' n).le
  obtain ⟨Y, hY⟩ : ∃ Y : ∀ n, ι n → Ω → ℝ,
      Y = fun n i ω ↦ X n i ω / Real.sqrt (v n) := ⟨_, rfl⟩
  have hYL2 n i : MemLp (Y n i) 2 μ := by
    simpa only [hY, div_eq_mul_inv] using (hLp n i).mul_const (Real.sqrt (v n))⁻¹
  have hY0 n i : μ[Y n i] = 0 := by simp only [hY, integral_div, hc, zero_div]
  have hind n : iIndepFun (Y n) μ := by
    rw [hY]
    exact (hi n).comp (fun _ x ↦ x / Real.sqrt (v n)) fun _ ↦ measurable_id.div_const _
  have hYsq n i : ∫ ω, Y n i ω ^ 2 ∂μ = (∫ ω, (X n i ω) ^ 2 ∂μ) / v n := by
    simp only [hY, div_pow, hsq, integral_div]
  have hvar n : ∑ i, ∫ ω, Y n i ω ^ 2 ∂μ = 1 := by
    simp only [hYsq, ← Finset.sum_div]
    rw [div_eq_one_iff_eq (hv' n).ne', hvv]
  have hF' : ∀ δ > 0, ∀ᶠ n in atTop, ∀ i, ∫ ω, Y n i ω ^ 2 ∂μ < δ := by
    intro δ hδ
    filter_upwards [hF δ hδ] with n hn i
    rw [hYsq, hvv]
    exact hn i
  have hsum : (fun n ω ↦ ∑ i, Y n i ω) =
      fun n ω ↦ (∑ i, X n i ω) / Real.sqrt (∑ j, ∫ ω, (X n j ω) ^ 2 ∂μ) := by
    funext n ω
    simp only [hY, Finset.sum_div, hvv]
  have hL := lindeberg_of_feller_of_tendstoInDistribution hind hYL2 hY0 hvar hF'
    (by rw [hsum]; exact hclt)
  intro ε hε
  refine squeeze_zero (fun n ↦ ?_) (fun n ↦ ?_) (hL ε hε)
  · refine mul_nonneg (inv_nonneg.2 (hv n).le) (Finset.sum_nonneg fun i _ ↦
      integral_nonneg fun ω ↦ ?_)
    dsimp only
    split_ifs <;> simp [sq_nonneg]
  have hvn : (∑ j, ∫ ω, (X n j ω) ^ 2 ∂μ) = v n := by rw [hvv]
  rw [hvn, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  rw [← integral_const_mul]
  have hφ : Measurable fun x : ℝ ↦ if ε * Real.sqrt (v n) < |x| then x ^ 2 else 0 :=
    Measurable.ite (measurableSet_lt measurable_const continuous_abs.measurable)
      (measurable_id.pow_const 2) measurable_const
  refine integral_mono_of_nonneg (ae_of_all _ fun ω ↦ ?_)
    ((hYL2 n i).integrable_indicator_sq ε) (ae_of_all _ fun ω ↦ ?_)
  · exact mul_nonneg (inv_nonneg.2 (hv' n).le) (by split_ifs <;> simp [sq_nonneg])
  · simp only [Set.indicator_apply, Set.mem_ofPred_eq, hY]
    split_ifs with h1 h2
    · rw [div_pow, hsq, div_eq_inv_mul]
    · rw [abs_div, abs_of_pos (hs n), le_div_iff₀ (hs n)] at h2
      exact absurd h1.le h2
    all_goals simp only [mul_zero, le_refl]
    positivity

end CKMA
