/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.Fourier.WeightedMaximal.Sufficiency
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Sufficiency of the Muckenhoupt condition

An `A_p` bound makes the centred maximal operator strong type `(p,p)` on the weighted
measure. The argument compares an unweighted ball average with the centred maximal operator
of the dual weight, then with the centred maximal operator of the original weight, and
invokes the Marcinkiewicz bounds already proved for those two operators.

Source: GAPS 27.44. The comparison follows Lerner, Proc. Amer. Math. Soc. 136 (2008), with
the outer exponent `1/(p-1)` required by the ball form of the `A_p` characteristic.
-/

public section

noncomputable section

namespace CKMA

open MeasureTheory Metric Set ENNReal Filter
open scoped ENNReal

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

namespace ApWeight

variable {p : ℝ}

/-- `1 - q = -1/(p-1)` for the conjugate exponent `q`. -/
private lemma one_sub_conj (W : ApWeight (d := d) p) : 1 - W.conj = -(p - 1)⁻¹ := by
  rw [← neg_sub, W.conj_sub_one]

/-- On `{w > 0}` the measurable dual density is a power of the weight density. -/
private lemma dualMk_eq_rpow (W : ApWeight (d := d) p) {y : E} (hy : 0 < W.w y) :
    W.dualMk y = weightDensity W.w y ^ (1 - W.conj) := by
  rw [dualMk]
  simp only [hy, ite_true]
  rw [← Real.rpow_def_of_pos hy, W.one_sub_conj, ← ENNReal.ofReal_rpow_of_pos hy]
  unfold weightDensity
  rfl

/-- Raising a quotient by the weight density returns the dual density. -/
private lemma weighted_pow_div (W : ApWeight (d := d) p) (a : ℝ≥0∞) (y : E) :
    (a ^ (p - 1) / weightDensity W.w y) ^ W.conj * weightDensity W.w y =
      a ^ p * W.dualMk y := by
  by_cases hy : 0 < W.w y
  · set ρ := weightDensity W.w y
    have hρ0 : ρ ≠ 0 := (ENNReal.ofReal_pos.mpr hy).ne'
    have hρt : ρ ≠ ∞ := ENNReal.ofReal_ne_top
    have hq : 0 ≤ W.conj := W.conj_pos.le
    have hsub : (p - 1) * W.conj = p := W.holder.sub_one_mul_conj
    calc
      (a ^ (p - 1) / ρ) ^ W.conj * ρ
          = (a ^ (p - 1)) ^ W.conj / ρ ^ W.conj * ρ := by
            rw [ENNReal.div_rpow_of_nonneg _ _ hq]
        _ = a ^ ((p - 1) * W.conj) / ρ ^ W.conj * ρ := by rw [← ENNReal.rpow_mul]
        _ = a ^ p / ρ ^ W.conj * ρ := by rw [hsub]
        _ = a ^ p * (ρ / ρ ^ W.conj) := by rw [ENNReal.mul_comm_div]
        _ = a ^ p * ρ ^ (1 - W.conj) := by
            congr 1
            rw [ENNReal.rpow_sub 1 W.conj hρ0 hρt, ENNReal.rpow_one]
        _ = a ^ p * W.dualMk y := by rw [W.dualMk_eq_rpow hy]
  · have hρ : weightDensity W.w y = 0 := by
      simp only [weightDensity, ENNReal.ofReal_eq_zero]
      exact not_lt.mp hy
    have hmk : W.dualMk y = 0 := by simp [dualMk, hy]
    simp [hρ, hmk, mul_zero]

/-- Dividing by the dual density and raising to `p` returns the weight density. -/
private lemma enorm_div_pow_mul (W : ApWeight (d := d) p) (a : ℝ≥0∞) (y : E) :
    (a / W.dualMk y) ^ p * W.dualMk y = a ^ p * weightDensity W.w y := by
  by_cases hy : 0 < W.w y
  · have hδ0 : W.dualMk y ≠ 0 := by
      rw [W.dualMk_eq_rpow hy]
      exact (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr hy) ENNReal.ofReal_ne_top).ne'
    have hδt : W.dualMk y ≠ ∞ := by
      rw [W.dualMk_eq_rpow hy]
      exact ENNReal.rpow_ne_top_of_nonneg' (ENNReal.ofReal_pos.mpr hy) ENNReal.ofReal_ne_top
    set δ := W.dualMk y
    set ρ := weightDensity W.w y
    have hp0 : 0 ≤ p := W.p_pos.le
    have hexp : -(p - 1)⁻¹ * (1 - p) = 1 := by
      have hsub : 1 - p = -(p - 1) := by ring
      rw [hsub, neg_mul_neg, inv_mul_cancel₀ W.sub_one_pos.ne']
    calc
      (a / δ) ^ p * δ
          = a ^ p / δ ^ p * δ := by rw [ENNReal.div_rpow_of_nonneg _ _ hp0]
        _ = a ^ p * (δ / δ ^ p) := by rw [ENNReal.mul_comm_div]
        _ = a ^ p * δ ^ (1 - p) := by
            congr 1
            rw [ENNReal.rpow_sub 1 p hδ0 hδt, ENNReal.rpow_one]
        _ = a ^ p * ρ := by
            have hδ : δ = ρ ^ (-(p - 1)⁻¹) := by
              change W.dualMk y = weightDensity W.w y ^ (-(p - 1)⁻¹)
              rw [W.dualMk_eq_rpow hy, W.one_sub_conj]
            rw [hδ, ← ENNReal.rpow_mul, hexp, ENNReal.rpow_one]
  · have hρ : weightDensity W.w y = 0 := by
      simp only [weightDensity, ENNReal.ofReal_eq_zero]
      exact not_lt.mp hy
    have hmk : W.dualMk y = 0 := by simp [dualMk, hy]
    simp [hρ, hmk, mul_zero]

/-- Factor coming from the radius-`3` enlargement of the dual measure. -/
def enlargeConst (W : ApWeight (d := d) p) : ℝ≥0∞ :=
  W.A ^ (p - 1)⁻¹ * ENNReal.ofReal ((3 : ℝ) ^ d) ^ W.conj

/-- The enlargement factor is finite. -/
private lemma enlargeConst_ne_top (W : ApWeight (d := d) p) : W.enlargeConst ≠ ∞ := by
  unfold enlargeConst
  exact mul_ne_top W.dualA_ne_zero_top.2
    (rpow_ne_top_of_nonneg' (ENNReal.ofReal_pos.mpr (by positivity)) ENNReal.ofReal_ne_top)

/-- The enlargement factor is positive. -/
private lemma enlargeConst_pos (W : ApWeight (d := d) p) : 0 < W.enlargeConst := by
  unfold enlargeConst
  exact ENNReal.mul_pos W.dualA_ne_zero_top.1
    (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr (by positivity)) ENNReal.ofReal_ne_top).ne'

/-- Pointwise factor in the comparison of the two centred maximal operators. -/
def pointConst (W : ApWeight (d := d) p) : ℝ≥0∞ :=
  W.A ^ (p - 1)⁻¹ * W.enlargeConst

/-- The pointwise factor is finite. -/
private lemma pointConst_ne_top (W : ApWeight (d := d) p) : W.pointConst ≠ ∞ := by
  unfold pointConst
  exact mul_ne_top W.dualA_ne_zero_top.2 W.enlargeConst_ne_top

/-- A characteristic bound `t * u ^ e ≤ A` controls `u` by `A` and `t⁻¹`. -/
private lemma ratio_le {e : ℝ} {t A u : ℝ≥0∞} (he : 0 < e) (ht0 : t ≠ 0) (hA : A ≠ ∞)
    (h : t * u ^ e ≤ A) : u ≤ A ^ e⁻¹ * t⁻¹ ^ e⁻¹ := by
  have he0 : 0 ≤ e⁻¹ := inv_nonneg.mpr he.le
  have hdiv : u ^ e ≤ A / t :=
    (ENNReal.le_div_iff_mul_le (Or.inl ht0) (Or.inr hA)).2 (by rwa [mul_comm])
  have hroot := ENNReal.rpow_le_rpow hdiv he0
  rw [← ENNReal.rpow_mul, mul_inv_cancel₀ he.ne', ENNReal.rpow_one] at hroot
  rw [ENNReal.div_rpow_of_nonneg _ _ he0, div_eq_mul_inv, ← ENNReal.inv_rpow] at hroot
  exact hroot

/-- The dual measure of a positive ball is finite. -/
private lemma dualMk_measure_ne_top (W : ApWeight (d := d) p) (x : E) {r : ℝ} (hr : 0 < r) :
    W.dualMeasureMk (ball x r) ≠ ∞ := by
  unfold dualMeasureMk
  rw [withDensity_apply _ measurableSet_ball]
  have hint : ∫⁻ y in ball x r, W.dualMk y ∂volume =
      ∫⁻ y in ball x r, dualDensity p W.w y ∂volume := by
    refine (setLIntegral_congr_fun_ae measurableSet_ball ?_).symm
    filter_upwards [W.dualDensity_ae_eq_dualMk] with y hy
    exact fun _ => hy
  rw [hint]
  exact W.dual_ball_ne_top x hr

/-- The dual measure of a positive ball is positive. -/
private lemma dualMk_measure_ne_zero (W : ApWeight (d := d) p) (x : E) {r : ℝ} (hr : 0 < r) :
    W.dualMeasureMk (ball x r) ≠ 0 := by
  unfold dualMeasureMk
  rw [withDensity_apply _ measurableSet_ball]
  have hint : ∫⁻ y in ball x r, W.dualMk y ∂volume =
      ∫⁻ y in ball x r, dualDensity p W.w y ∂volume := by
    refine (setLIntegral_congr_fun_ae measurableSet_ball ?_).symm
    filter_upwards [W.dualDensity_ae_eq_dualMk] with y hy
    exact fun _ => hy
  rw [hint]
  exact W.dual_ball_ne_zero x hr

/-- Radius `3` enlarges the dual measure by at most `enlargeConst`. -/
private lemma dualMk_three_le (W : ApWeight (d := d) p) (x : E) {r : ℝ} (hr : 0 < r) :
    W.dualMeasureMk (ball x (3 * r)) ≤ W.enlargeConst * W.dualMeasureMk (ball x r) := by
  have hdoub := W.dual_doubling (c := (3 : ℝ)) (by norm_num) x hr
  rw [W.dualMeasure_eq_mk] at hdoub
  unfold enlargeConst
  exact hdoub

/-- A dual ball average is controlled by the dual maximal function on that ball. -/
private lemma div_lintegral_le_enlarge (W : ApWeight (d := d) p) (v : E → ℝ≥0∞) (x : E)
    {r : ℝ} (hr : 0 < r) {y : E} (hy : y ∈ ball x r) :
    (∫⁻ z in ball x r, v z ∂W.dualMeasureMk) / W.dualMeasureMk (ball x r) ≤
      W.enlargeConst * TauCeti.maximalFunction W.dualMeasureMk v y := by
  let σ : Measure E := W.dualMeasureMk
  have htwo : 0 < 2 * r := mul_pos two_pos hr
  have hthree : 0 < 3 * r := mul_pos (by norm_num : (0 : ℝ) < 3) hr
  have hS0 : σ (ball x r) ≠ 0 := W.dualMk_measure_ne_zero x hr
  have hSTop : σ (ball x r) ≠ ∞ := W.dualMk_measure_ne_top x hr
  have hsub1 : ball x r ⊆ ball y (2 * r) := ball_subset_double_ball hy
  have hsub2 : ball y (2 * r) ⊆ ball x (3 * r) := ball_two_subset_ball_three hy
  have h2Top : σ (ball y (2 * r)) ≠ ∞ :=
    ne_top_of_le_ne_top (W.dualMk_measure_ne_top x hthree) (measure_mono hsub2)
  have hint : ∫⁻ z in ball x r, v z ∂σ ≤ ∫⁻ z in ball y (2 * r), v z ∂σ :=
    lintegral_mono_set hsub1
  have hball : ∫⁻ z in ball y (2 * r), v z ∂σ ≤
      σ (ball y (2 * r)) * TauCeti.maximalFunction σ v y := by
    simpa using TauCeti.setLIntegral_ball_le_measure_mul_maximalFunction (μ := σ) (f := v)
      (x := y) htwo h2Top
  let M : ℝ≥0∞ := TauCeti.maximalFunction σ v y
  have hI : ∫⁻ z in ball x r, v z ∂σ ≤ (W.enlargeConst * σ (ball x r)) * M := by
    calc ∫⁻ z in ball x r, v z ∂σ
        ≤ ∫⁻ z in ball y (2 * r), v z ∂σ := hint
      _ ≤ σ (ball y (2 * r)) * M := hball
      _ ≤ σ (ball x (3 * r)) * M := mul_le_mul_left (measure_mono hsub2) _
      _ ≤ (W.enlargeConst * σ (ball x r)) * M :=
          mul_le_mul_left (W.dualMk_three_le x hr) _
  have hcomm : (W.enlargeConst * σ (ball x r)) * M =
      (W.enlargeConst * M) * σ (ball x r) := by
    rw [mul_assoc, mul_comm (σ (ball x r)), ← mul_assoc]
  rw [hcomm] at hI
  exact (ENNReal.div_le_iff hS0 hSTop).2 hI

/-- The dual ball average is at most an unweighted average of the dual maximal function. -/
private lemma div_lintegral_le_average (W : ApWeight (d := d) p) (v : E → ℝ≥0∞) (x : E)
    {r : ℝ} (hr : 0 < r) :
    (∫⁻ z in ball x r, v z ∂W.dualMeasureMk) / W.dualMeasureMk (ball x r) ≤
      W.enlargeConst * ((∫⁻ y in ball x r,
        TauCeti.maximalFunction W.dualMeasureMk v y ^ (p - 1) ∂volume) /
          volume (ball x r)) ^ (p - 1)⁻¹ := by
  let σ : Measure E := W.dualMeasureMk
  let φ : E → ℝ≥0∞ := fun y => TauCeti.maximalFunction σ v y
  let α : ℝ≥0∞ := (∫⁻ z in ball x r, v z ∂σ) / σ (ball x r)
  let β : ℝ≥0∞ := α / W.enlargeConst
  have hD0 : W.enlargeConst ≠ 0 := W.enlargeConst_pos.ne'
  have hDTop : W.enlargeConst ≠ ∞ := W.enlargeConst_ne_top
  have hV0 : volume (ball x r) ≠ 0 := volume_ball_ne_zero x hr
  have hVTop : volume (ball x r) ≠ ∞ := volume_ball_ne_top x r
  have hpt : ∀ y ∈ ball x r, β ^ (p - 1) ≤ φ y ^ (p - 1) := by
    intro y hy
    have hle : α ≤ W.enlargeConst * φ y := W.div_lintegral_le_enlarge v x hr hy
    have hdiv : β ≤ φ y := (ENNReal.div_le_iff hD0 hDTop).2 (by rwa [mul_comm])
    exact ENNReal.rpow_le_rpow hdiv W.sub_one_pos.le
  have hint := setLIntegral_mono' (μ := volume) measurableSet_ball hpt
  have hconst : ∫⁻ _ in ball x r, β ^ (p - 1) ∂volume =
      β ^ (p - 1) * volume (ball x r) := setLIntegral_const _ _
  rw [hconst] at hint
  have hpow : β ^ (p - 1) ≤
      (∫⁻ y in ball x r, φ y ^ (p - 1) ∂volume) / volume (ball x r) :=
    (ENNReal.le_div_iff_mul_le (Or.inl hV0) (Or.inl hVTop)).2 hint
  have hroot : β ≤ ((∫⁻ y in ball x r, φ y ^ (p - 1) ∂volume) /
      volume (ball x r)) ^ (p - 1)⁻¹ := by
    have h := ENNReal.rpow_le_rpow hpow (inv_nonneg.mpr W.sub_one_pos.le)
    rw [← ENNReal.rpow_mul, mul_inv_cancel₀ W.sub_one_pos.ne', ENNReal.rpow_one] at h
    exact h
  have hαβ : α = W.enlargeConst * β := (ENNReal.mul_div_cancel hD0 hDTop).symm
  change α ≤ _
  rw [hαβ]
  exact mul_le_mul_right hroot _

/-- Unweighted and dual-weighted integrals of `‖f‖ₑ` agree on every ball. -/
private lemma lintegral_enorm_eq_dual (W : ApWeight (d := d) p) (f : E → ℂ) (x : E) (r : ℝ) :
    ∫⁻ y in ball x r, ‖f y‖ₑ ∂volume =
      ∫⁻ y in ball x r, (fun z => ‖f z‖ₑ / W.dualMk z) y ∂W.dualMeasureMk := by
  have hfin : ∀ᵐ y ∂volume.restrict (ball x r), W.dualMk y < ∞ := by
    rw [ae_restrict_iff' measurableSet_ball]
    refine Eventually.of_forall fun y _ => ?_
    simp only [dualMk]
    split_ifs <;> simp [ENNReal.ofReal_lt_top]
  unfold dualMeasureMk
  rw [setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable volume W.measurable_dualMk
    (fun z => ‖f z‖ₑ / W.dualMk z) measurableSet_ball hfin]
  refine setLIntegral_congr_fun_ae measurableSet_ball ?_
  filter_upwards [W.dualDensity_pos_ae, W.dualDensity_ae_eq_dualMk] with y hy heq _
  have h0 : W.dualMk y ≠ 0 := (hy.trans_eq heq).ne'
  have ht : W.dualMk y ≠ ∞ := by
    rw [← heq]
    exact ENNReal.ofReal_ne_top
  simp only [Pi.mul_apply]
  exact (ENNReal.mul_div_cancel h0 ht).symm

/-- An unweighted ball average of `‖f‖ₑ` is bounded by the weight maximal function. -/
private lemma average_enorm_le (W : ApWeight (d := d) p) (f : E → ℂ) (x : E) {r : ℝ}
    (hr : 0 < r) :
    (∫⁻ y in ball x r, ‖f y‖ₑ ∂volume) / volume (ball x r) ≤
      W.pointConst * TauCeti.maximalFunction (weightMeasure W.w)
        (fun y => TauCeti.maximalFunction W.dualMeasureMk
          (fun z => ‖f z‖ₑ / W.dualMk z) y ^ (p - 1) / weightDensity W.w y) x ^
        (p - 1)⁻¹ := by
  let v : E → ℝ≥0∞ := fun z => ‖f z‖ₑ / W.dualMk z
  let σ : Measure E := W.dualMeasureMk
  let ν : Measure E := weightMeasure W.w
  let φ : E → ℝ≥0∞ := fun y => TauCeti.maximalFunction σ v y
  let ψ : E → ℝ≥0∞ := fun y => φ y ^ (p - 1) / weightDensity W.w y
  let V : ℝ≥0∞ := volume (ball x r)
  let wInt : ℝ≥0∞ := ∫⁻ y in ball x r, weightDensity W.w y ∂volume
  let sInt : ℝ≥0∞ := ∫⁻ y in ball x r, dualDensity p W.w y ∂volume
  have hV0 : V ≠ 0 := volume_ball_ne_zero x hr
  have hVTop : V ≠ ∞ := volume_ball_ne_top x r
  have hw0 : wInt ≠ 0 := W.weight_ball_ne_zero x hr
  have hwTop : wInt ≠ ∞ := W.weight_ball_ne_top x r
  have hs0 : sInt ≠ 0 := W.dual_ball_ne_zero x hr
  have hsTop : sInt ≠ ∞ := W.dual_ball_ne_top x hr
  have hI : ∫⁻ y in ball x r, ‖f y‖ₑ ∂volume = ∫⁻ y in ball x r, v y ∂σ :=
    W.lintegral_enorm_eq_dual f x r
  have hWb : ν (ball x r) = wInt := by
    unfold ν weightMeasure wInt
    rw [withDensity_apply _ measurableSet_ball]
  have hSb : σ (ball x r) = sInt := by
    unfold σ dualMeasureMk sInt
    rw [withDensity_apply _ measurableSet_ball]
    refine (setLIntegral_congr_fun_ae measurableSet_ball ?_).symm
    filter_upwards [W.dualDensity_ae_eq_dualMk] with y hy
    exact fun _ => hy
  have hJ : ∫⁻ y in ball x r, φ y ^ (p - 1) ∂volume = ∫⁻ y in ball x r, ψ y ∂ν := by
    have hfin : ∀ᵐ y ∂volume.restrict (ball x r), weightDensity W.w y < ∞ := by
      rw [ae_restrict_iff' measurableSet_ball]
      exact Eventually.of_forall fun _ _ => ENNReal.ofReal_lt_top
    unfold ν
    unfold weightMeasure
    rw [setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable volume
      W.measurable_weightDensity ψ measurableSet_ball hfin]
    refine setLIntegral_congr_fun_ae measurableSet_ball ?_
    filter_upwards [W.weightDensity_pos_ae] with y hy _
    simp only [Pi.mul_apply, ψ]
    exact (ENNReal.mul_div_cancel hy.ne' ENNReal.ofReal_ne_top).symm
  have hα : (∫⁻ y in ball x r, v y ∂σ) / σ (ball x r) ≤
      W.enlargeConst * ((∫⁻ y in ball x r, φ y ^ (p - 1) ∂volume) / V) ^ (p - 1)⁻¹ :=
    W.div_lintegral_le_average v x hr
  have hratio : sInt / V ≤ W.A ^ (p - 1)⁻¹ * (V / wInt) ^ (p - 1)⁻¹ := by
    have ht0 : wInt / V ≠ 0 := (ENNReal.div_ne_zero).2 ⟨hw0, hVTop⟩
    have hchar : wInt / V * (sInt / V) ^ (p - 1) ≤ W.A := W.ball_le x r hr
    have hinv : (wInt / V)⁻¹ = V / wInt :=
      ENNReal.inv_div (Or.inr hwTop) (Or.inl hV0)
    simpa [hinv] using ratio_le W.sub_one_pos ht0 W.A_ne_top hchar
  have havg : (∫⁻ y in ball x r, ψ y ∂ν) / wInt ≤
      TauCeti.maximalFunction ν ψ x := by
    rw [← hWb, ← setLAverage_eq]
    simpa using TauCeti.setLAverage_le_maximalFunction ν ψ x hr
  have hpowJ : ((∫⁻ y in ball x r, φ y ^ (p - 1) ∂volume) / V) ^ (p - 1)⁻¹ ≤
      TauCeti.maximalFunction ν ψ x ^ (p - 1)⁻¹ * (wInt / V) ^ (p - 1)⁻¹ := by
    rw [hJ]
    have hsplit : (∫⁻ y in ball x r, ψ y ∂ν) / V =
        ((∫⁻ y in ball x r, ψ y ∂ν) / wInt) * (wInt / V) := by
      rw [← ENNReal.div_mul_div_cancel hw0 hwTop]
    rw [hsplit, ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.mpr W.sub_one_pos.le)]
    exact mul_le_mul_left (ENNReal.rpow_le_rpow havg (inv_nonneg.mpr W.sub_one_pos.le)) _
  have hcancel : (wInt / V) ^ (p - 1)⁻¹ * (V / wInt) ^ (p - 1)⁻¹ = 1 := by
    rw [← ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.mpr W.sub_one_pos.le)]
    have h1 : wInt / V * (V / wInt) = 1 := by
      rw [ENNReal.div_mul_div_cancel hV0 hVTop, ENNReal.div_self hw0 hwTop]
    rw [h1, ENNReal.one_rpow]
  calc (∫⁻ y in ball x r, ‖f y‖ₑ ∂volume) / V
      = ((∫⁻ y in ball x r, v y ∂σ) / σ (ball x r)) * (sInt / V) := by
          rw [hI, hSb, ENNReal.div_mul_div_cancel hs0 hsTop]
    _ ≤ (W.enlargeConst * ((∫⁻ y in ball x r, φ y ^ (p - 1) ∂volume) / V) ^ (p - 1)⁻¹) *
          (W.A ^ (p - 1)⁻¹ * (V / wInt) ^ (p - 1)⁻¹) :=
        mul_le_mul' hα hratio
    _ = W.pointConst * (((∫⁻ y in ball x r, φ y ^ (p - 1) ∂volume) / V) ^ (p - 1)⁻¹ *
          (V / wInt) ^ (p - 1)⁻¹) := by
          unfold pointConst
          ac_rfl
    _ ≤ W.pointConst * (TauCeti.maximalFunction ν ψ x ^ (p - 1)⁻¹ *
          (wInt / V) ^ (p - 1)⁻¹ * (V / wInt) ^ (p - 1)⁻¹) := by
          refine mul_le_mul_right ?_ _
          exact mul_le_mul_left hpowJ _
    _ = W.pointConst * TauCeti.maximalFunction ν ψ x ^ (p - 1)⁻¹ := by
          congr 1
          rw [mul_assoc, hcancel, mul_one]

/-- Almost-everywhere properties for the weight pass to the dual measure. -/
private lemma aemeasurable_dual_of_weight (W : ApWeight (d := d) p) {g : E → ℝ≥0∞}
    (hg : AEMeasurable g (weightMeasure W.w)) : AEMeasurable g W.dualMeasureMk := by
  refine ⟨hg.mk g, hg.measurable_mk, ?_⟩
  have himp := (ae_withDensity_iff W.measurable_weightDensity).1 hg.ae_eq_mk
  have hvol : g =ᵐ[volume] hg.mk g := by
    filter_upwards [himp, W.weightDensity_pos_ae] with y hy hpos
    exact hy hpos.ne'
  exact (withDensity_absolutelyContinuous volume W.dualMk).ae_le hvol

/-- The centred weight and dual maximal operators control the unweighted maximal function. -/
private lemma lintegral_maximal_le (W : ApWeight (d := d) p) {f : E → ℂ}
    (hf : MemLp f (ENNReal.ofReal p) (weightMeasure W.w)) :
    ∫⁻ x, TauCeti.maximalFunction volume f x ^ p ∂weightMeasure W.w ≤
      W.pointConst ^ p * marcFactor W.conj W.weakConst * marcFactor p W.dualWeakConst *
        ∫⁻ x, ‖f x‖ₑ ^ p ∂weightMeasure W.w := by
  let v : E → ℝ≥0∞ := fun z => ‖f z‖ₑ / W.dualMk z
  let σ : Measure E := W.dualMeasureMk
  let ν : Measure E := weightMeasure W.w
  let φ : E → ℝ≥0∞ := fun y => TauCeti.maximalFunction σ v y
  let ψ : E → ℝ≥0∞ := fun y => φ y ^ (p - 1) / weightDensity W.w y
  have hvMeas : AEMeasurable v σ := by
    have henorm : AEMeasurable (fun y => ‖f y‖ₑ) σ :=
      W.aemeasurable_dual_of_weight hf.aemeasurable.enorm
    have hdiv : AEMeasurable ((fun y => ‖f y‖ₑ) / W.dualMk) σ :=
      henorm.div (W.measurable_dualMk.aemeasurable : AEMeasurable W.dualMk σ)
    refine hdiv.congr ?_
    filter_upwards with y
    rw [Pi.div_apply]
  have hpos : ∀ x r, 0 < r → σ (ball x r) ≠ 0 := fun x r hr => W.dualMk_measure_ne_zero x hr
  have hfin : ∀ x r, 0 < r → σ (ball x r) ≠ ∞ := fun x r hr => W.dualMk_measure_ne_top x hr
  have hφ : Measurable φ :=
    measurable_maximalFunction_withDensity W.measurable_dualMk hvMeas hpos hfin
  have hψ : Measurable ψ := (hφ.pow_const _).div W.measurable_weightDensity
  have hpoint : ∀ x, TauCeti.maximalFunction volume f x ≤
      W.pointConst * TauCeti.maximalFunction ν ψ x ^ (p - 1)⁻¹ := by
    intro x
    refine TauCeti.maximalFunction_le fun r hr => ?_
    rw [setLAverage_eq]
    exact W.average_enorm_le f x hr
  have hexp : (p - 1)⁻¹ * p = W.conj := by
    rw [mul_comm, ← div_eq_mul_inv]
    exact W.holder.conjugate_eq.symm
  have hpow : ∀ x, TauCeti.maximalFunction volume f x ^ p ≤
      W.pointConst ^ p * TauCeti.maximalFunction ν ψ x ^ W.conj := by
    intro x
    calc TauCeti.maximalFunction volume f x ^ p
        ≤ (W.pointConst * TauCeti.maximalFunction ν ψ x ^ (p - 1)⁻¹) ^ p :=
          ENNReal.rpow_le_rpow (hpoint x) W.p_pos.le
      _ = W.pointConst ^ p * (TauCeti.maximalFunction ν ψ x ^ (p - 1)⁻¹) ^ p :=
          ENNReal.mul_rpow_of_nonneg _ _ W.p_pos.le
      _ = W.pointConst ^ p * TauCeti.maximalFunction ν ψ x ^ ((p - 1)⁻¹ * p) := by
          rw [← ENNReal.rpow_mul]
      _ = W.pointConst ^ p * TauCeti.maximalFunction ν ψ x ^ W.conj := by rw [hexp]
  have hKp : W.pointConst ^ p ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg W.p_pos.le W.pointConst_ne_top
  have hint : ∫⁻ x, TauCeti.maximalFunction volume f x ^ p ∂ν ≤
      W.pointConst ^ p * ∫⁻ x, TauCeti.maximalFunction ν ψ x ^ W.conj ∂ν := by
    calc ∫⁻ x, TauCeti.maximalFunction volume f x ^ p ∂ν
        ≤ ∫⁻ x, W.pointConst ^ p * TauCeti.maximalFunction ν ψ x ^ W.conj ∂ν :=
          lintegral_mono hpow
      _ = W.pointConst ^ p * ∫⁻ x, TauCeti.maximalFunction ν ψ x ^ W.conj ∂ν :=
          lintegral_const_mul' _ _ hKp
  have hweight := W.lintegral_rpow_maximal_weight hψ.aemeasurable
  have hψφ : ∫⁻ y, ψ y ^ W.conj ∂ν = ∫⁻ y, φ y ^ p ∂σ := by
    have hfin : ∀ᵐ y ∂volume, weightDensity W.w y < ∞ :=
      Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
    have hfinδ : ∀ᵐ y ∂volume, W.dualMk y < ∞ := by
      refine Eventually.of_forall fun y => ?_
      simp only [dualMk]
      split_ifs <;> simp [ENNReal.ofReal_lt_top]
    unfold ν σ weightMeasure dualMeasureMk
    rw [lintegral_withDensity_eq_lintegral_mul_non_measurable volume W.measurable_weightDensity
        hfin (fun y => ψ y ^ W.conj),
      lintegral_withDensity_eq_lintegral_mul_non_measurable volume W.measurable_dualMk hfinδ
        (fun y => φ y ^ p)]
    refine lintegral_congr fun y => ?_
    simp only [Pi.mul_apply]
    rw [mul_comm, W.weighted_pow_div (φ y) y, mul_comm]
  have hdual := W.lintegral_rpow_maximal_dual hvMeas
  have hvf : ∫⁻ y, v y ^ p ∂σ = ∫⁻ y, ‖f y‖ₑ ^ p ∂ν := by
    have hfinρ : ∀ᵐ y ∂volume, weightDensity W.w y < ∞ :=
      Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
    have hfinδ : ∀ᵐ y ∂volume, W.dualMk y < ∞ := by
      refine Eventually.of_forall fun y => ?_
      simp only [dualMk]
      split_ifs <;> simp [ENNReal.ofReal_lt_top]
    unfold ν σ weightMeasure dualMeasureMk
    rw [lintegral_withDensity_eq_lintegral_mul_non_measurable volume W.measurable_dualMk hfinδ
        (fun y => v y ^ p),
      lintegral_withDensity_eq_lintegral_mul_non_measurable volume W.measurable_weightDensity
        hfinρ (fun y => ‖f y‖ₑ ^ p)]
    refine lintegral_congr fun y => ?_
    simp only [Pi.mul_apply, v]
    rw [mul_comm, W.enorm_div_pow_mul (‖f y‖ₑ) y, mul_comm]
  calc ∫⁻ x, TauCeti.maximalFunction volume f x ^ p ∂ν
      ≤ W.pointConst ^ p * ∫⁻ x, TauCeti.maximalFunction ν ψ x ^ W.conj ∂ν := hint
    _ ≤ W.pointConst ^ p * (marcFactor W.conj W.weakConst * ∫⁻ y, ψ y ^ W.conj ∂ν) :=
        mul_le_mul_right hweight _
    _ = W.pointConst ^ p * marcFactor W.conj W.weakConst * ∫⁻ y, ψ y ^ W.conj ∂ν := by
        rw [← mul_assoc]
    _ = W.pointConst ^ p * marcFactor W.conj W.weakConst * ∫⁻ y, φ y ^ p ∂σ := by rw [hψφ]
    _ ≤ W.pointConst ^ p * marcFactor W.conj W.weakConst *
          (marcFactor p W.dualWeakConst * ∫⁻ y, v y ^ p ∂σ) :=
        mul_le_mul_right hdual _
    _ = W.pointConst ^ p * marcFactor W.conj W.weakConst * marcFactor p W.dualWeakConst *
          ∫⁻ y, ‖f y‖ₑ ^ p ∂ν := by
        rw [← mul_assoc, hvf]

/-- The Marcinkiewicz constant of either doubling measure is finite. -/
private lemma marcFactor_ne_top (t : ℝ) {D : ℝ≥0∞} (hD : D ≠ ∞) : marcFactor t D ≠ ∞ := by
  unfold marcFactor
  exact mul_ne_top ENNReal.ofReal_ne_top (mul_ne_top ENNReal.ofReal_ne_top hD)

/-- Strong type `(p,p)` for one `A_p` weight, with an explicit finite constant. -/
private lemma exists_bound (W : ApWeight (d := d) p) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ f : E → ℂ,
      MemLp f (ENNReal.ofReal p) (volume.withDensity (fun x => ENNReal.ofReal (W.w x))) →
        (∫⁻ x, TauCeti.maximalFunction volume f x ^ p
          ∂volume.withDensity (fun x => ENNReal.ofReal (W.w x))) ≤
          C * (eLpNorm f (ENNReal.ofReal p)
            (volume.withDensity (fun x => ENNReal.ofReal (W.w x)))) ^ p := by
  refine ⟨W.pointConst ^ p * marcFactor W.conj W.weakConst * marcFactor p W.dualWeakConst,
    ?_, ?_⟩
  · exact mul_ne_top
      (mul_ne_top (ENNReal.rpow_ne_top_of_nonneg W.p_pos.le W.pointConst_ne_top)
        (marcFactor_ne_top _ W.weakConst_ne_top))
      (marcFactor_ne_top _ W.dualWeakConst_ne_top)
  · intro f hf
    have hmeas : weightMeasure W.w =
        volume.withDensity fun x => ENNReal.ofReal (W.w x) := by
      unfold weightMeasure weightDensity
      rfl
    rw [← hmeas] at hf ⊢
    have hint := W.lintegral_maximal_le hf
    have hp0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr W.p_pos).ne'
    have hpt : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
    have hnorm : (eLpNorm f (ENNReal.ofReal p) (weightMeasure W.w)) ^ p =
        ∫⁻ x, ‖f x‖ₑ ^ p ∂weightMeasure W.w := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt hf.aestronglyMeasurable,
        ENNReal.toReal_ofReal W.p_pos.le, ← ENNReal.rpow_mul, one_div,
        inv_mul_cancel₀ W.p_pos.ne', ENNReal.rpow_one]
    rw [hnorm]
    exact hint

end ApWeight

/-- An `A_p` bound makes the centred maximal operator strong type `(p,p)` on the weighted
measure. -/
theorem exists_weightedMaximal_bound {d : ℕ} {p : ℝ} (hp : 1 < p)
    {w : EuclideanSpace ℝ (Fin d) → ℝ} (hm : Measurable w)
    (hpos : ∀ᵐ x ∂volume, 0 < w x) (hloc : LocallyIntegrable w volume) {A : ℝ≥0∞}
    (hA : A ≠ ∞)
    (hball : ∀ x r, 0 < r →
      ((∫⁻ y in ball x r, ENNReal.ofReal (w y)) / volume (ball x r)) *
        (((∫⁻ y in ball x r, ENNReal.ofReal (w y ^ (-(p - 1)⁻¹))) / volume (ball x r)) ^
          (p - 1)) ≤ A) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ f : EuclideanSpace ℝ (Fin d) → ℂ,
      MemLp f (ENNReal.ofReal p) (volume.withDensity (fun x => ENNReal.ofReal (w x))) →
        (∫⁻ x, TauCeti.maximalFunction volume f x ^ p
          ∂volume.withDensity (fun x => ENNReal.ofReal (w x))) ≤
          C * (eLpNorm f (ENNReal.ofReal p)
            (volume.withDensity (fun x => ENNReal.ofReal (w x)))) ^ p := by
  let W : ApWeight (d := d) p :=
    { w := w
      hp := hp
      measurable_w := hm
      pos_ae := hpos
      locallyIntegrable_w := hloc
      A := A
      A_ne_top := hA
      ball_le := hball }
  exact W.exists_bound

end CKMA
