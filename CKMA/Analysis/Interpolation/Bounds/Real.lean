/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.Interpolation.Basic

import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Real interpolation operator bound

Peetre's `K`-functional scales by the endpoint bounds of a compatible couple map. The measure
`dt/t` is invariant under positive dilations, so the real interpolation gauge obeys the bound
`M₀ ^ (1 - θ) * M₁ ^ θ` whenever those endpoint bounds are positive. Nonnegative endpoint bounds
follow by replacing `Mᵢ` with `Mᵢ + ε` and passing to the limit.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Filter MeasureTheory Set Topology
open scoped ENNReal

variable {𝕜 : Type*} [RCLike 𝕜] {C D : BanachCouple 𝕜}

/-- Multiplication by a positive finite constant passes inside a three-fold infimum. -/
private lemma mul_iInf₃ {α β : Type*} {γ : α → β → Prop} (a : ℝ≥0∞) (ha₀ : a ≠ 0) (ha : a ≠ ∞)
    (f : ∀ x, ∀ y, γ x y → ℝ≥0∞) :
    a * (⨅ x, ⨅ y, ⨅ h, f x y h) = ⨅ x, ⨅ y, ⨅ h, a * f x y h := by
  simp_rw [ENNReal.mul_iInf_of_ne ha₀ ha]

/-- A decomposition of `x` pushes forward to a decomposition of `T.ambientMap x`. -/
private lemma CoupleMap.image_decomp (T : CoupleMap C D) {x : C.ambient} {x₀ : C.left}
    {x₁ : C.right} (h : C.inLeft x₀ + C.inRight x₁ = x) :
    D.inLeft (T.leftMap x₀) + D.inRight (T.rightMap x₁) = T.ambientMap x := by
  rw [← T.left_comm, ← T.right_comm, ← map_add, h]

/-- Positive endpoint bounds scale the `K`-functional by `M₀`, with time `t * M₁ / M₀`. -/
private lemma kFunctional_map_le (T : CoupleMap C D) {M₀ M₁ t : ℝ} (hM₀ : 0 < M₀)
    (h₀ : ‖T.leftMap‖ ≤ M₀) (h₁ : ‖T.rightMap‖ ≤ M₁) (ht : 0 < t) (x : C.ambient) :
    D.kFunctional t (T.ambientMap x) ≤
      ENNReal.ofReal M₀ * C.kFunctional (t * M₁ / M₀) x := by
  set s : ℝ := t * M₁ / M₀
  have hMs : M₀ * s = t * M₁ := by
    simp only [s]
    field_simp [hM₀.ne']
  have hM₀e : ENNReal.ofReal M₀ ≠ 0 := (ENNReal.ofReal_pos.mpr hM₀).ne'
  have hpull : ENNReal.ofReal M₀ * C.kFunctional s x =
      ⨅ x₀ : C.left, ⨅ x₁ : C.right, ⨅ (_h : C.inLeft x₀ + C.inRight x₁ = x),
        ENNReal.ofReal (M₀ * (‖x₀‖ + s * ‖x₁‖)) := by
    rw [BanachCouple.kFunctional]
    rw [mul_iInf₃ _ hM₀e ENNReal.ofReal_ne_top]
    refine iInf_congr fun x₀ => iInf_congr fun x₁ => iInf_congr fun _h => ?_
    exact (ENNReal.ofReal_mul hM₀.le).symm
  rw [hpull]
  refine le_iInf fun x₀ => le_iInf fun x₁ => le_iInf fun h => ?_
  have hL : ‖T.leftMap x₀‖ ≤ M₀ * ‖x₀‖ :=
    (T.leftMap.le_opNorm x₀).trans (mul_le_mul_of_nonneg_right h₀ (norm_nonneg _))
  have hR : ‖T.rightMap x₁‖ ≤ M₁ * ‖x₁‖ :=
    (T.rightMap.le_opNorm x₁).trans (mul_le_mul_of_nonneg_right h₁ (norm_nonneg _))
  have hsum : ‖T.leftMap x₀‖ + t * ‖T.rightMap x₁‖ ≤ M₀ * (‖x₀‖ + s * ‖x₁‖) := by
    calc
      ‖T.leftMap x₀‖ + t * ‖T.rightMap x₁‖
          ≤ M₀ * ‖x₀‖ + t * (M₁ * ‖x₁‖) :=
            add_le_add hL (mul_le_mul_of_nonneg_left hR ht.le)
      _ = M₀ * ‖x₀‖ + (t * M₁) * ‖x₁‖ := by rw [← mul_assoc]
      _ = M₀ * ‖x₀‖ + (M₀ * s) * ‖x₁‖ := by rw [← hMs]
      _ = M₀ * ‖x₀‖ + M₀ * (s * ‖x₁‖) := by rw [mul_assoc]
      _ = M₀ * (‖x₀‖ + s * ‖x₁‖) := by rw [← mul_add]
  calc
    D.kFunctional t (T.ambientMap x)
        ≤ ENNReal.ofReal (‖T.leftMap x₀‖ + t * ‖T.rightMap x₁‖) := by
          rw [BanachCouple.kFunctional]
          exact iInf_le_of_le (T.leftMap x₀)
            (iInf_le_of_le (T.rightMap x₁)
              (iInf_le (fun _ => ENNReal.ofReal (‖T.leftMap x₀‖ + t * ‖T.rightMap x₁‖))
                (T.image_decomp h)))
    _ ≤ ENNReal.ofReal (M₀ * (‖x₀‖ + s * ‖x₁‖)) := ENNReal.ofReal_le_ofReal hsum

/-- The scalar identity `t ^ (-θ) * M₀ = M₀ ^ (1 - θ) * M₁ ^ θ * (t * M₁ / M₀) ^ (-θ)`. -/
private lemma endpointFactor_mul_rpow {M₀ M₁ t θ : ℝ} (hM₀ : 0 < M₀) (hM₁ : 0 < M₁) (ht : 0 < t) :
    t ^ (-θ) * M₀ = M₀ ^ (1 - θ) * M₁ ^ θ * (t * M₁ / M₀) ^ (-θ) := by
  have hs : 0 < t * M₁ / M₀ := by positivity
  have hlog : Real.log (t * M₁ / M₀) = Real.log t + Real.log M₁ - Real.log M₀ := by
    rw [Real.log_div (mul_pos ht hM₁).ne' hM₀.ne', Real.log_mul ht.ne' hM₁.ne']
  calc
    t ^ (-θ) * M₀ = Real.exp (Real.log t * (-θ)) * M₀ := by rw [Real.rpow_def_of_pos ht]
    _ = Real.exp (Real.log t * (-θ)) * Real.exp (Real.log M₀) := by
        conv_lhs => arg 2; rw [← Real.exp_log hM₀]
    _ = Real.exp (Real.log t * (-θ) + Real.log M₀) := by rw [← Real.exp_add]
    _ = Real.exp (Real.log M₀ * (1 - θ) + Real.log M₁ * θ +
          Real.log (t * M₁ / M₀) * (-θ)) := by
        apply congrArg Real.exp
        rw [hlog]
        ring
    _ = Real.exp (Real.log M₀ * (1 - θ)) * Real.exp (Real.log M₁ * θ) *
          Real.exp (Real.log (t * M₁ / M₀) * (-θ)) := by rw [Real.exp_add, Real.exp_add]
    _ = M₀ ^ (1 - θ) * M₁ ^ θ * (t * M₁ / M₀) ^ (-θ) := by
        rw [← Real.rpow_def_of_pos hM₀, ← Real.rpow_def_of_pos hM₁, ← Real.rpow_def_of_pos hs]

/-- The scalar identity of `endpointFactor_mul_rpow`, transferred to `ℝ≥0∞`. -/
private lemma ofReal_endpointFactor_mul {M₀ M₁ t θ : ℝ} (hM₀ : 0 < M₀) (hM₁ : 0 < M₁)
    (ht : 0 < t) :
    ENNReal.ofReal (t ^ (-θ)) * ENNReal.ofReal M₀ =
      ENNReal.ofReal (M₀ ^ (1 - θ) * M₁ ^ θ) *
        ENNReal.ofReal ((t * M₁ / M₀) ^ (-θ)) := by
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _), endpointFactor_mul_rpow hM₀ hM₁ ht,
    ENNReal.ofReal_mul
      (mul_nonneg (Real.rpow_nonneg hM₀.le _) (Real.rpow_nonneg hM₁.le _))]

/-- Weighted `K`-functionals satisfy the pointwise real-interpolation comparison. -/
private lemma weighted_kFunctional_le (T : CoupleMap C D) {M₀ M₁ t θ : ℝ} (hM₀ : 0 < M₀)
    (hM₁ : 0 < M₁) (h₀ : ‖T.leftMap‖ ≤ M₀) (h₁ : ‖T.rightMap‖ ≤ M₁) (ht : 0 < t) (x : C.ambient) :
    ENNReal.ofReal (t ^ (-θ)) * D.kFunctional t (T.ambientMap x) ≤
      ENNReal.ofReal (M₀ ^ (1 - θ) * M₁ ^ θ) *
        (ENNReal.ofReal ((t * M₁ / M₀) ^ (-θ)) * C.kFunctional (t * M₁ / M₀) x) := by
  calc
    ENNReal.ofReal (t ^ (-θ)) * D.kFunctional t (T.ambientMap x)
        ≤ ENNReal.ofReal (t ^ (-θ)) *
            (ENNReal.ofReal M₀ * C.kFunctional (t * M₁ / M₀) x) :=
          mul_le_mul_right (kFunctional_map_le T hM₀ h₀ h₁ ht x) _
    _ = (ENNReal.ofReal (t ^ (-θ)) * ENNReal.ofReal M₀) *
          C.kFunctional (t * M₁ / M₀) x := by rw [mul_assoc]
    _ = (ENNReal.ofReal (M₀ ^ (1 - θ) * M₁ ^ θ) *
          ENNReal.ofReal ((t * M₁ / M₀) ^ (-θ))) *
          C.kFunctional (t * M₁ / M₀) x := by
        rw [ofReal_endpointFactor_mul hM₀ hM₁ ht]
    _ = ENNReal.ofReal (M₀ ^ (1 - θ) * M₁ ^ θ) *
          (ENNReal.ofReal ((t * M₁ / M₀) ^ (-θ)) * C.kFunctional (t * M₁ / M₀) x) := by
        rw [mul_assoc]

/-- Reindex a supremum over the positive line by multiplication with `c > 0`. -/
private lemma iSup_Ioi_mul_left (c : ℝ) (hc : 0 < c) (f : ℝ → ℝ≥0∞) :
    ⨆ t : ℝ, ⨆ (_ : 0 < t), f (c * t) = ⨆ t : ℝ, ⨆ (_ : 0 < t), f t := by
  apply le_antisymm
  · refine iSup_le fun t => iSup_le fun ht => ?_
    exact le_iSup_of_le (c * t) (le_iSup_of_le (mul_pos hc ht) le_rfl)
  · refine iSup_le fun t => iSup_le fun ht => ?_
    have hdiv : 0 < t / c := div_pos ht hc
    have hmul : c * (t / c) = t := mul_div_cancel₀ t hc.ne'
    exact le_iSup_of_le (t / c) (le_iSup_of_le hdiv (by rw [hmul]))

/-- Integrals against `dt/t` are unchanged by a positive dilation of the integrand. -/
private lemma lintegral_interpolationMeasure_comp_mul (c : ℝ) (hc : 0 < c) (f : ℝ → ℝ≥0∞) :
    ∫⁻ t, f (c * t) ∂interpolationMeasure = ∫⁻ t, f t ∂interpolationMeasure := by
  let dens : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal t⁻¹
  let μ : Measure ℝ := volume.restrict (Set.Ioi 0)
  have hdens : Measurable dens := ENNReal.measurable_ofReal.comp measurable_inv
  have hfin : ∀ᵐ t ∂μ, dens t < ∞ := ae_of_all _ fun _ => ENNReal.ofReal_lt_top
  let F : ℝ → ℝ≥0∞ := (Set.Ioi 0).indicator fun s => ENNReal.ofReal s⁻¹ * f s
  have hvanish : ∀ t, t ∉ Set.Ioi 0 → F (c * t) = 0 := by
    intro t ht
    have hct : c * t ∉ Set.Ioi 0 := by
      intro hpos
      exact ht ((mul_pos_iff_of_pos_left hc).mp hpos)
    rw [show F (c * t) = (Set.Ioi 0).indicator (fun s => ENNReal.ofReal s⁻¹ * f s) (c * t) from rfl,
      Set.indicator_of_notMem hct]
  have hscale : ∀ t, 0 < t → dens t * f (c * t) = ENNReal.ofReal c * F (c * t) := by
    intro t ht
    have hct : 0 < c * t := mul_pos hc ht
    have hinv : t⁻¹ = c * (c * t)⁻¹ := by field_simp
    have hmem : c * t ∈ Set.Ioi 0 := Set.mem_Ioi.mpr hct
    simp only [dens, F, Set.indicator_of_mem hmem]
    rw [hinv, ENNReal.ofReal_mul hc.le, mul_assoc]
  have hembed : MeasurableEmbedding (fun t : ℝ => c * t) :=
    (Homeomorph.mulLeft₀ c hc.ne').measurableEmbedding
  rw [interpolationMeasure]
  calc
    ∫⁻ t, f (c * t) ∂μ.withDensity dens
        = ∫⁻ t, dens t * f (c * t) ∂μ :=
          lintegral_withDensity_eq_lintegral_mul_non_measurable μ hdens hfin _
    _ = ∫⁻ t in Set.Ioi 0, dens t * f (c * t) ∂volume := rfl
    _ = ∫⁻ t in Set.Ioi 0, ENNReal.ofReal c * F (c * t) ∂volume := by
          refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
          exact hscale t ht
    _ = ENNReal.ofReal c * ∫⁻ t in Set.Ioi 0, F (c * t) ∂volume := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = ENNReal.ofReal c * ∫⁻ t, F (c * t) ∂volume := by
          rw [← lintegral_indicator measurableSet_Ioi]
          refine congrArg (HMul.hMul (ENNReal.ofReal c)) ?_
          refine lintegral_congr fun t => ?_
          by_cases ht : t ∈ Set.Ioi 0
          · rw [Set.indicator_of_mem ht]
          · rw [Set.indicator_of_notMem ht, hvanish t ht]
    _ = ENNReal.ofReal c * ∫⁻ s, F s ∂Measure.map (fun t : ℝ => c * t) volume := by
          rw [← hembed.lintegral_map F]
    _ = ENNReal.ofReal c * ∫⁻ s, F s ∂(ENNReal.ofReal c⁻¹ • volume) := by
          rw [Real.map_volume_mul_left hc.ne', abs_of_pos (inv_pos.mpr hc)]
    _ = ENNReal.ofReal c * (ENNReal.ofReal c⁻¹ * ∫⁻ s, F s ∂volume) := by
          rw [lintegral_smul_measure, smul_eq_mul]
    _ = ∫⁻ s, F s ∂volume := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hc.le, mul_inv_cancel₀ hc.ne', ENNReal.ofReal_one,
            one_mul]
    _ = ∫⁻ s in Set.Ioi 0, ENNReal.ofReal s⁻¹ * f s ∂volume := by
          rw [← lintegral_indicator measurableSet_Ioi]
    _ = ∫⁻ s, dens s * f s ∂μ := rfl
    _ = ∫⁻ s, f s ∂μ.withDensity dens := by
          exact (lintegral_withDensity_eq_lintegral_mul_non_measurable μ hdens hfin f).symm

/-- `interpolationMeasure` is supported on the positive half-line. -/
private lemma ae_pos_interpolationMeasure : ∀ᵐ t ∂interpolationMeasure, 0 < t := by
  rw [ae_iff]
  have hset : {t : ℝ | ¬ 0 < t} = (Set.Ioi 0)ᶜ := by
    ext t
    simp
  rw [hset, interpolationMeasure, withDensity_apply _ measurableSet_Ioi.compl]
  refine setLIntegral_measure_zero _ _ ?_
  rw [Measure.restrict_apply measurableSet_Ioi.compl]
  rw [show (Set.Ioi (0 : ℝ))ᶜ ∩ Set.Ioi 0 = ∅ by ext t; simp]
  exact measure_empty

/-- For positive endpoint bounds, the real interpolation gauge scales by `M₀ ^ (1 - θ) * M₁ ^ θ`. -/
theorem realInterpolationGauge_map_le_of_pos (T : CoupleMap C D) {θ : ℝ}
    {q : ℝ≥0∞} (hq : 1 ≤ q) {M₀ M₁ : ℝ} (hM₀ : 0 < M₀) (hM₁ : 0 < M₁)
    (h₀ : ‖T.leftMap‖ ≤ M₀) (h₁ : ‖T.rightMap‖ ≤ M₁) (x : C.ambient) :
    D.realInterpolationGauge θ q (T.ambientMap x) ≤
      ENNReal.ofReal (M₀ ^ (1 - θ) * M₁ ^ θ) * C.realInterpolationGauge θ q x := by
  have hc : 0 < M₁ / M₀ := div_pos hM₁ hM₀
  have hc_mul : ∀ t : ℝ, (M₁ / M₀) * t = t * M₁ / M₀ := fun t => by ring
  let factor : ℝ≥0∞ := ENNReal.ofReal (M₀ ^ (1 - θ) * M₁ ^ θ)
  by_cases hq_top : q = ∞
  · rw [BanachCouple.realInterpolationGauge, BanachCouple.realInterpolationGauge, hq_top]
    simp only [↓reduceIte]
    have hpt : ∀ t : ℝ, 0 < t →
        ENNReal.ofReal (t ^ (-θ)) * D.kFunctional t (T.ambientMap x) ≤
          factor * (ENNReal.ofReal (((M₁ / M₀) * t) ^ (-θ)) *
            C.kFunctional ((M₁ / M₀) * t) x) := by
      intro t ht
      simpa [factor, hc_mul t] using weighted_kFunctional_le T hM₀ hM₁ h₀ h₁ ht x
    calc
      ⨆ t : ℝ, ⨆ (_ : 0 < t), ENNReal.ofReal (t ^ (-θ)) * D.kFunctional t (T.ambientMap x)
          ≤ ⨆ t : ℝ, ⨆ (_ : 0 < t),
              factor * (ENNReal.ofReal (((M₁ / M₀) * t) ^ (-θ)) *
                C.kFunctional ((M₁ / M₀) * t) x) := by
            refine iSup_le fun t => iSup_le fun ht => ?_
            exact le_iSup_of_le t (le_iSup_of_le ht (hpt t ht))
      _ = factor * ⨆ t : ℝ, ⨆ (_ : 0 < t),
            ENNReal.ofReal (((M₁ / M₀) * t) ^ (-θ)) * C.kFunctional ((M₁ / M₀) * t) x := by
          simp_rw [← ENNReal.mul_iSup]
      _ = factor * ⨆ t : ℝ, ⨆ (_ : 0 < t),
            ENNReal.ofReal (t ^ (-θ)) * C.kFunctional t x := by
          congr 1
          exact iSup_Ioi_mul_left (M₁ / M₀) hc
            (fun u => ENNReal.ofReal (u ^ (-θ)) * C.kFunctional u x)
  · have hp : 0 < q.toReal := ENNReal.toReal_pos (zero_lt_one.trans_le hq).ne' hq_top
    rw [BanachCouple.realInterpolationGauge, BanachCouple.realInterpolationGauge]
    rw [ite_eq_right hq_top, ite_eq_right hq_top]
    let φC : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (t ^ (-θ)) * C.kFunctional t x
    let φD : ℝ → ℝ≥0∞ := fun t =>
      ENNReal.ofReal (t ^ (-θ)) * D.kFunctional t (T.ambientMap x)
    have hpt : ∀ᵐ t ∂interpolationMeasure,
        (φD t) ^ q.toReal ≤ factor ^ q.toReal * (φC ((M₁ / M₀) * t)) ^ q.toReal := by
      filter_upwards [ae_pos_interpolationMeasure] with t ht
      have hw : φD t ≤ factor * φC ((M₁ / M₀) * t) := by
        simpa [φD, φC, factor, hc_mul t] using weighted_kFunctional_le T hM₀ hM₁ h₀ h₁ ht x
      calc
        (φD t) ^ q.toReal ≤ (factor * φC ((M₁ / M₀) * t)) ^ q.toReal :=
          ENNReal.rpow_le_rpow hw hp.le
        _ = factor ^ q.toReal * (φC ((M₁ / M₀) * t)) ^ q.toReal :=
          ENNReal.mul_rpow_of_nonneg _ _ hp.le
    have hint : ∫⁻ t, (φD t) ^ q.toReal ∂interpolationMeasure ≤
        factor ^ q.toReal *
          ∫⁻ t, (φC t) ^ q.toReal ∂interpolationMeasure := by
      calc
        ∫⁻ t, (φD t) ^ q.toReal ∂interpolationMeasure
            ≤ ∫⁻ t, factor ^ q.toReal * (φC ((M₁ / M₀) * t)) ^ q.toReal
                ∂interpolationMeasure := lintegral_mono_ae hpt
        _ = factor ^ q.toReal *
              ∫⁻ t, (φC ((M₁ / M₀) * t)) ^ q.toReal ∂interpolationMeasure := by
            rw [lintegral_const_mul' _ _
              (ENNReal.rpow_ne_top_of_nonneg hp.le ENNReal.ofReal_ne_top)]
        _ = factor ^ q.toReal * ∫⁻ t, (φC t) ^ q.toReal ∂interpolationMeasure := by
            rw [lintegral_interpolationMeasure_comp_mul (M₁ / M₀) hc
              (fun u => (φC u) ^ q.toReal)]
    have hexp : 0 ≤ 1 / q.toReal := div_nonneg zero_le_one hp.le
    have hpow := ENNReal.rpow_le_rpow hint hexp
    rw [ENNReal.mul_rpow_of_nonneg _ _ hexp, ← ENNReal.rpow_mul,
      show q.toReal * (1 / q.toReal) = 1 by field_simp [hp.ne'], ENNReal.rpow_one] at hpow
    simpa [φD, φC, factor] using hpow

/-- If a bound holds for every `Mᵢ + ε`, it holds for nonnegative `Mᵢ`. -/
theorem le_of_endpointFactor_eps {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) {M₀ M₁ : ℝ} (_hM₀ : 0 ≤ M₀)
    (_hM₁ : 0 ≤ M₁) {a G : ℝ≥0∞} (hG : G ≠ ∞)
    (h : ∀ ε : ℝ, 0 < ε →
      a ≤ ENNReal.ofReal ((M₀ + ε) ^ (1 - θ) * (M₁ + ε) ^ θ) * G) :
    a ≤ ENNReal.ofReal (M₀ ^ (1 - θ) * M₁ ^ θ) * G := by
  let εn : ℕ → ℝ := fun n => (↑(n + 1) : ℝ)⁻¹
  have hεpos : ∀ n, 0 < εn n := fun n => inv_pos.mpr (Nat.cast_pos.mpr n.succ_pos)
  have hεlim : Tendsto εn atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have hpow0 : Tendsto (fun n => (M₀ + εn n) ^ (1 - θ)) atTop (𝓝 (M₀ ^ (1 - θ))) := by
    simpa [add_zero] using
      (tendsto_const_nhds.add hεlim).rpow_const (Or.inr (sub_nonneg.mpr hθ1.le))
  have hpow1 : Tendsto (fun n => (M₁ + εn n) ^ θ) atTop (𝓝 (M₁ ^ θ)) := by
    simpa [add_zero] using (tendsto_const_nhds.add hεlim).rpow_const (Or.inr hθ.le)
  have hprod : Tendsto (fun n => (M₀ + εn n) ^ (1 - θ) * (M₁ + εn n) ^ θ) atTop
      (𝓝 (M₀ ^ (1 - θ) * M₁ ^ θ)) := hpow0.mul hpow1
  have hmul : Tendsto (fun n => ENNReal.ofReal ((M₀ + εn n) ^ (1 - θ) * (M₁ + εn n) ^ θ) * G)
      atTop (𝓝 (ENNReal.ofReal (M₀ ^ (1 - θ) * M₁ ^ θ) * G)) :=
    ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal hprod) (Or.inr hG)
  exact le_of_tendsto_of_tendsto' tendsto_const_nhds hmul fun n => h (εn n) (hεpos n)

end CKMA
