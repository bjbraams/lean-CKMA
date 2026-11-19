/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import TauCeti.MeasureTheory.Integral.MaximalFunction
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace

import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.Normed.Group.Real

/-!
# Doubling for Muckenhoupt `A_p` weights

An `A_p` ball bound makes the weight and its dual density double on Euclidean balls. The
argument is Hölder’s inequality on the pair of densities, whose product is identically one
almost everywhere, together with the ball characteristic. These comparisons are the input to
the weighted maximal bound in `CKMA.Analysis.Fourier.WeightedMaximal.Sufficiency`.

Source: GAPS 27.44. The doubling constant is the one used by Lerner’s reduction of the
weighted strong-type bound to the weighted maximal operator on its own measure.
-/

@[expose] public section

noncomputable section

namespace CKMA

open MeasureTheory Metric Set ENNReal Filter
open scoped ENNReal

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Density of a real weight in `ℝ≥0∞`. -/
def weightDensity (w : E → ℝ) (y : E) : ℝ≥0∞ := ENNReal.ofReal (w y)

/-- Dual density `w ^ (-1/(p-1))`, matching the ball `A_p` characteristic. -/
def dualDensity (p : ℝ) (w : E → ℝ) (y : E) : ℝ≥0∞ :=
  ENNReal.ofReal (w y ^ (-(p - 1)⁻¹))

/-- Lebesgue measure weighted by `weightDensity w`. -/
def weightMeasure (w : E → ℝ) : Measure E := volume.withDensity (weightDensity w)

/-- Lebesgue measure weighted by `dualDensity p w`. -/
def dualMeasure (p : ℝ) (w : E → ℝ) : Measure E := volume.withDensity (dualDensity p w)

/-- The summand of the ball `A_p` characteristic at centre `x` and radius `r`. -/
def ballProduct (p : ℝ) (w : E → ℝ) (x : E) (r : ℝ) : ℝ≥0∞ :=
  ((∫⁻ y in ball x r, weightDensity w y ∂volume) / volume (ball x r)) *
    (((∫⁻ y in ball x r, dualDensity p w y ∂volume) / volume (ball x r)) ^ (p - 1))

/-- Data of an `A_p` weight with an explicit finite ball bound. -/
structure ApWeight (p : ℝ) where
  /-- The weight. -/
  w : E → ℝ
  /-- The integrability exponent is greater than one. -/
  hp : 1 < p
  /-- The weight is measurable. -/
  measurable_w : Measurable w
  /-- The weight is positive almost everywhere. -/
  pos_ae : ∀ᵐ x ∂volume, 0 < w x
  /-- The weight is locally integrable. -/
  locallyIntegrable_w : LocallyIntegrable w volume
  /-- A finite upper bound for every ball product. -/
  A : ℝ≥0∞
  /-- The ball bound is finite. -/
  A_ne_top : A ≠ ∞
  /-- Every positive-radius ball has product at most `A`. -/
  ball_le : ∀ x r, 0 < r → ballProduct p w x r ≤ A

namespace ApWeight

variable {p : ℝ}

/-- The conjugate exponent `p / (p - 1)`. -/
def conj (_W : ApWeight (d := d) p) : ℝ := Real.conjExponent p

/-- `p` is conjugate to `W.conj`. -/
lemma holder (W : ApWeight (d := d) p) : p.HolderConjugate W.conj :=
  Real.HolderConjugate.conjExponent W.hp

lemma one_lt_conj (W : ApWeight (d := d) p) : 1 < W.conj :=
  (Real.holderConjugate_iff.mp W.holder.symm).1

lemma conj_pos (W : ApWeight (d := d) p) : 0 < W.conj := W.holder.symm.pos

lemma sub_one_pos (W : ApWeight (d := d) p) : 0 < p - 1 := W.holder.sub_one_pos

lemma p_pos (W : ApWeight (d := d) p) : 0 < p := W.holder.pos

lemma conj_sub_one (W : ApWeight (d := d) p) : W.conj - 1 = (p - 1)⁻¹ := by
  rw [conj, Real.conjExponent]
  calc p / (p - 1) - 1
      = p / (p - 1) - (p - 1) / (p - 1) := by
        refine congrArg (fun t => p / (p - 1) - t) ?_
        exact (div_self W.sub_one_pos.ne').symm
    _ = (p - (p - 1)) / (p - 1) := by rw [← sub_div]
    _ = 1 / (p - 1) := by
        refine congrArg (fun t => t / (p - 1)) ?_
        ring
    _ = (p - 1)⁻¹ := by rw [one_div]

lemma div_conj (W : ApWeight (d := d) p) : p / W.conj = p - 1 :=
  W.holder.div_conj_eq_sub_one

lemma conj_div (W : ApWeight (d := d) p) : W.conj / p = (p - 1)⁻¹ := by
  rw [div_eq_iff W.p_pos.ne', ← inv_mul_cancel_left₀ W.sub_one_pos.ne' W.conj,
    W.holder.sub_one_mul_conj]

/-- The weight density is measurable. -/
lemma measurable_weightDensity (W : ApWeight (d := d) p) : Measurable (weightDensity W.w) :=
  ENNReal.continuous_ofReal.measurable.comp W.measurable_w

/-- A measurable representative of the dual density, equal to it where `w` is positive. -/
def dualMk (W : ApWeight (d := d) p) (y : E) : ℝ≥0∞ :=
  if 0 < W.w y then ENNReal.ofReal (Real.exp (Real.log (W.w y) * -(p - 1)⁻¹)) else 0

/-- The dual representative is measurable. -/
lemma measurable_dualMk (W : ApWeight (d := d) p) : Measurable (W.dualMk) := by
  refine Measurable.ite (measurableSet_lt measurable_const W.measurable_w) ?_ measurable_const
  exact ENNReal.continuous_ofReal.measurable.comp
    (Real.measurable_exp.comp ((W.measurable_w.log).mul measurable_const))

/-- The dual density agrees almost everywhere with its measurable representative. -/
lemma dualDensity_ae_eq_dualMk (W : ApWeight (d := d) p) :
    dualDensity p W.w =ᵐ[volume] W.dualMk := by
  filter_upwards [W.pos_ae] with y hy
  simp only [dualDensity, dualMk, hy, ite_true, Real.rpow_def_of_pos hy]

/-- The dual density is almost everywhere measurable. -/
lemma aemeasurable_dualDensity (W : ApWeight (d := d) p) :
    AEMeasurable (dualDensity p W.w) volume :=
  ⟨W.dualMk, W.measurable_dualMk, W.dualDensity_ae_eq_dualMk⟩

/-- The two densities multiply to one, after the conjugate powers, wherever `w` is positive. -/
lemma density_prod_eq_one (W : ApWeight (d := d) p) {y : E} (hy : 0 < W.w y) :
    weightDensity W.w y ^ (1 / p) * dualDensity p W.w y ^ (1 / W.conj) = 1 := by
  have hρ : 0 < weightDensity W.w y := ofReal_pos.mpr hy
  have hρt : weightDensity W.w y ≠ ∞ := ofReal_ne_top
  have hδ : dualDensity p W.w y = weightDensity W.w y ^ (-(p - 1)⁻¹) := by
    simp only [dualDensity, weightDensity, ← ofReal_rpow_of_pos hy]
  rw [hδ, ← rpow_mul]
  have hexp : -(p - 1)⁻¹ * (1 / W.conj) = -(1 / p) := by
    rw [neg_mul, neg_inj, mul_one_div, div_eq_div_iff W.conj_pos.ne' W.p_pos.ne', one_mul,
      mul_comm, ← div_eq_mul_inv]
    exact W.holder.conjugate_eq.symm
  rw [hexp, ← rpow_add _ _ hρ.ne' hρt]
  have hadd : 1 / p + -(1 / p) = 0 := by ring
  rw [hadd, rpow_zero]

/-- The weighted densities multiply to one almost everywhere. -/
lemma density_prod_ae_eq_one (W : ApWeight (d := d) p) :
    (fun y => weightDensity W.w y ^ (1 / p) * dualDensity p W.w y ^ (1 / W.conj)) =ᵐ[volume]
      fun _ => 1 := by
  filter_upwards [W.pos_ae] with y hy
  exact W.density_prod_eq_one hy

/-- The weight density is positive almost everywhere. -/
lemma weightDensity_pos_ae (W : ApWeight (d := d) p) :
    ∀ᵐ y ∂volume, 0 < weightDensity W.w y := by
  filter_upwards [W.pos_ae] with y hy
  exact ofReal_pos.mpr hy

/-- The dual density is positive almost everywhere. -/
lemma dualDensity_pos_ae (W : ApWeight (d := d) p) :
    ∀ᵐ y ∂volume, 0 < dualDensity p W.w y := by
  filter_upwards [W.pos_ae] with y hy
  exact ofReal_pos.mpr (Real.rpow_pos_of_pos hy _)

/-- A locally integrable weight charges every ball finitely. -/
lemma weight_ball_ne_top (W : ApWeight (d := d) p) (x : E) (r : ℝ) :
    (∫⁻ y in ball x r, weightDensity W.w y ∂volume) ≠ ∞ := by
  have hint : ∫⁻ y in closedBall x r, ‖W.w y‖ₑ ∂volume < ∞ := by
    rw [← hasFiniteIntegral_iff_enorm]
    exact (W.locallyIntegrable_w.integrableOn_isCompact
      (isCompact_closedBall x r)).hasFiniteIntegral
  refine ne_of_lt (lt_of_le_of_lt ?_ hint)
  calc ∫⁻ y in ball x r, weightDensity W.w y ∂volume
      ≤ ∫⁻ y in closedBall x r, weightDensity W.w y ∂volume :=
        lintegral_mono_set ball_subset_closedBall
    _ ≤ ∫⁻ y in closedBall x r, ‖W.w y‖ₑ ∂volume :=
        setLIntegral_mono' isClosed_closedBall.measurableSet
          fun _ _ => Real.ofReal_le_enorm _

/-- A positive weight charges every positive ball. -/
lemma weight_ball_ne_zero (W : ApWeight (d := d) p) (x : E) {r : ℝ} (hr : 0 < r) :
    (∫⁻ y in ball x r, weightDensity W.w y ∂volume) ≠ 0 := by
  intro hzero
  have hvanish : ∀ᵐ y ∂volume, y ∈ ball x r → weightDensity W.w y = 0 :=
    (setLIntegral_eq_zero_iff measurableSet_ball W.measurable_weightDensity).1 hzero
  have hempty : ∀ᵐ y ∂volume, y ∉ ball x r := by
    filter_upwards [hvanish, W.weightDensity_pos_ae] with y hy hpos hyball
    exact (hpos.ne' (hy hyball)).elim
  have : volume (ball x r) = 0 := by
    rw [ae_iff] at hempty
    simpa [ball] using hempty
  exact (measure_ball_pos volume x hr).ne' this

/-- The volume of a positive ball lies in `(0, ∞)`. -/
lemma volume_ball_ne_zero (x : E) {r : ℝ} (hr : 0 < r) : volume (ball x r) ≠ 0 :=
  (measure_ball_pos volume x hr).ne'

/-- The volume of a ball is finite. -/
lemma volume_ball_ne_top (x : E) (r : ℝ) : volume (ball x r) ≠ ∞ := measure_ball_lt_top.ne

/-- Scaling the radius by `c > 0` multiplies the volume by `c ^ d`. -/
lemma ball_volume_mul {c r : ℝ} (hc : 0 < c) (hr : 0 < r) (x y : E) :
    volume (ball y (c * r)) = ENNReal.ofReal (c ^ d) * volume (ball x r) := by
  have hcr : 0 < c * r := mul_pos hc hr
  rw [Measure.addHaar_ball_of_pos volume y hcr, Measure.addHaar_ball_of_pos volume x hr,
    finrank_euclideanSpace_fin, mul_pow, ofReal_mul (pow_nonneg hc.le _), mul_assoc]

/-- The ball characteristic controls the dual integral. -/
lemma dual_ball_ne_top (W : ApWeight (d := d) p) (x : E) {r : ℝ} (hr : 0 < r) :
    (∫⁻ y in ball x r, dualDensity p W.w y ∂volume) ≠ ∞ := by
  intro hS
  have hVt : volume (ball x r) ≠ ∞ := volume_ball_ne_top x r
  have hW0 : (∫⁻ y in ball x r, weightDensity W.w y ∂volume) ≠ 0 :=
    W.weight_ball_ne_zero x hr
  have hdiv : (∫⁻ y in ball x r, dualDensity p W.w y ∂volume) / volume (ball x r) = ∞ := by
    rw [hS]
    exact top_div_of_ne_top hVt
  have hpow : ((∫⁻ y in ball x r, dualDensity p W.w y ∂volume) /
      volume (ball x r)) ^ (p - 1) = ∞ := by
    rw [hdiv]
    exact top_rpow_of_pos W.sub_one_pos
  have hWdiv : (∫⁻ y in ball x r, weightDensity W.w y ∂volume) / volume (ball x r) ≠ 0 :=
    (ENNReal.div_ne_zero).2 ⟨hW0, hVt⟩
  have hprod : ballProduct p W.w x r = ∞ := by
    rw [ballProduct, hpow, ENNReal.mul_top hWdiv]
  exact W.A_ne_top (top_le_iff.mp (hprod ▸ W.ball_le x r hr))

/-- A positive dual density charges every positive ball. -/
lemma dual_ball_ne_zero (W : ApWeight (d := d) p) (x : E) {r : ℝ} (hr : 0 < r) :
    (∫⁻ y in ball x r, dualDensity p W.w y ∂volume) ≠ 0 := by
  intro hzero
  have hmk : (∫⁻ y in ball x r, W.dualMk y ∂volume) = 0 := by
    rw [setLIntegral_congr_fun_ae measurableSet_ball, hzero]
    filter_upwards [W.dualDensity_ae_eq_dualMk] with y hy _
    exact hy.symm
  have hvanish : ∀ᵐ y ∂volume, y ∈ ball x r → W.dualMk y = 0 :=
    (setLIntegral_eq_zero_iff measurableSet_ball W.measurable_dualMk).1 hmk
  have hpos : ∀ᵐ y ∂volume, 0 < W.dualMk y := by
    filter_upwards [W.dualDensity_pos_ae, W.dualDensity_ae_eq_dualMk] with y hy heq
    simpa [heq] using hy
  have hempty : ∀ᵐ y ∂volume, y ∉ ball x r := by
    filter_upwards [hvanish, hpos] with y hy hposy hyball
    exact (hposy.ne' (hy hyball)).elim
  have : volume (ball x r) = 0 := by
    rw [ae_iff] at hempty
    simpa [ball] using hempty
  exact (measure_ball_pos volume x hr).ne' this

/-- Every ball product is positive, so the characteristic bound is positive. -/
lemma A_ne_zero (W : ApWeight (d := d) p) : W.A ≠ 0 := by
  let x : E := 0
  have hr : (0 : ℝ) < 1 := one_pos
  have hW : 0 < (∫⁻ y in ball x 1, weightDensity W.w y ∂volume) / volume (ball x 1) :=
    ENNReal.div_pos (W.weight_ball_ne_zero x hr) (volume_ball_ne_top x 1)
  have hS : 0 < (∫⁻ y in ball x 1, dualDensity p W.w y ∂volume) / volume (ball x 1) :=
    ENNReal.div_pos (W.dual_ball_ne_zero x hr) (volume_ball_ne_top x 1)
  have hpow : 0 < ((∫⁻ y in ball x 1, dualDensity p W.w y ∂volume) /
      volume (ball x 1)) ^ (p - 1) :=
    rpow_pos hS (div_ne_top (W.dual_ball_ne_top x hr) (volume_ball_ne_zero x hr))
  have hprod : 0 < ballProduct p W.w x 1 := by
    rw [ballProduct]
    exact ENNReal.mul_pos hW.ne' hpow.ne'
  exact (hprod.trans_le (W.ball_le x 1 hr)).ne'

/-- The characteristic bound raised to `1/(p-1)` is finite and positive. -/
lemma dualA_ne_zero_top (W : ApWeight (d := d) p) :
    W.A ^ (p - 1)⁻¹ ≠ 0 ∧ W.A ^ (p - 1)⁻¹ ≠ ∞ := by
  refine ⟨?_, ?_⟩
  · exact (rpow_pos (pos_iff_ne_zero.mpr W.A_ne_zero) W.A_ne_top).ne'
  · exact rpow_ne_top_of_nonneg (inv_nonneg.mpr W.sub_one_pos.le) W.A_ne_top

/-- Doubling rearrangement: a Hölder bound and one characteristic bound give the weight ratio. -/
lemma rearrange_ap {t : ℝ} {A vE vQ wE wQ sQ : ℝ≥0∞} (ht : 1 < t)
    (hvE0 : vE ≠ 0) (hvEt : vE ≠ ∞) (hvQ0 : vQ ≠ 0) (hvQt : vQ ≠ ∞)
    (hwQ0 : wQ ≠ 0) (hwQt : wQ ≠ ∞)
    (hhold : vE ^ t ≤ wE * sQ ^ (t - 1))
    (hchar : wQ / vQ * (sQ / vQ) ^ (t - 1) ≤ A) :
    wQ ≤ A * (vQ / vE) ^ t * wE := by
  have ht0 : 0 ≤ t := by linarith
  have ht1 : 0 ≤ t - 1 := (sub_pos.mpr ht).le
  have hvEp0 : vE ^ t ≠ 0 := (rpow_pos (pos_iff_ne_zero.mpr hvE0) hvEt).ne'
  have hvEpt : vE ^ t ≠ ∞ := rpow_ne_top_of_nonneg ht0 hvEt
  have hvQp0 : vQ ^ t ≠ 0 := (rpow_pos (pos_iff_ne_zero.mpr hvQ0) hvQt).ne'
  have hvQpt : vQ ^ t ≠ ∞ := rpow_ne_top_of_nonneg ht0 hvQt
  have hv10 : vQ ^ (t - 1) ≠ 0 := (rpow_pos (pos_iff_ne_zero.mpr hvQ0) hvQt).ne'
  have hsplit : (sQ / vQ) ^ (t - 1) = sQ ^ (t - 1) / vQ ^ (t - 1) :=
    div_rpow_of_nonneg _ _ ht1
  have hden : vQ ^ t = vQ * vQ ^ (t - 1) := by
    have hsum : t = 1 + (t - 1) := by ring
    conv_lhs => rw [hsum]
    rw [rpow_add 1 (t - 1) hvQ0 hvQt, rpow_one]
  have hfrac : wQ / vQ * (sQ ^ (t - 1) / vQ ^ (t - 1)) =
      wQ * sQ ^ (t - 1) / vQ ^ t := by
    rw [hden]
    exact (ENNReal.mul_div_mul_comm (Or.inl hvQ0) (Or.inr hv10)).symm
  have hchar' : wQ * sQ ^ (t - 1) / vQ ^ t ≤ A := by
    rw [← hfrac, ← hsplit]
    exact hchar
  have hmul : wQ * sQ ^ (t - 1) ≤ A * vQ ^ t :=
    (ENNReal.div_le_iff hvQp0 hvQpt).1 hchar'
  have hsle : sQ ^ (t - 1) ≤ (A * vQ ^ t) / wQ :=
    (ENNReal.le_div_iff_mul_le (Or.inl hwQ0) (Or.inl hwQt)).2 (by rwa [mul_comm])
  have hhold' : vE ^ t ≤ wE * ((A * vQ ^ t) / wQ) :=
    hhold.trans (mul_le_mul_right hsle wE)
  have hcancel : wE * ((A * vQ ^ t) / wQ) * wQ = wE * (A * vQ ^ t) := by
    rw [mul_assoc, ENNReal.div_mul_cancel hwQ0 hwQt]
  have hscaled : vE ^ t * wQ ≤ wE * (A * vQ ^ t) := by
    have hle : vE ^ t * wQ ≤ wE * ((A * vQ ^ t) / wQ) * wQ :=
      mul_le_mul_left hhold' wQ
    rwa [hcancel] at hle
  have hdiv : wQ ≤ (wE * (A * vQ ^ t)) / vE ^ t :=
    (ENNReal.le_div_iff_mul_le (Or.inl hvEp0) (Or.inl hvEpt)).2 (by rwa [mul_comm])
  have hpow : (vQ / vE) ^ t = vQ ^ t / vE ^ t := div_rpow_of_nonneg _ _ ht0
  refine hdiv.trans (le_of_eq ?_)
  rw [hpow, div_eq_mul_inv, div_eq_mul_inv]
  ac_rfl

/-- Hölder comparison of a smaller ball against the dual integral of a larger one. -/
lemma volume_pow_le_weight_mul_dual (W : ApWeight (d := d) p) {x : E} {r R : ℝ}
    (hR : r ≤ R) :
    volume (ball x r) ^ p ≤
      (∫⁻ y in ball x r, weightDensity W.w y ∂volume) *
        (∫⁻ y in ball x R, dualDensity p W.w y ∂volume) ^ (p - 1) := by
  let ρ := weightDensity W.w
  let δ := dualDensity p W.w
  let f := fun y => ρ y ^ (1 / p)
  let g := fun y => δ y ^ (1 / W.conj)
  have hf : AEMeasurable f volume := (W.measurable_weightDensity.pow_const _).aemeasurable
  have hg : AEMeasurable g volume := W.aemeasurable_dualDensity.pow_const _
  have hprod : ∫⁻ y in ball x r, f y * g y ∂volume = volume (ball x r) := by
    refine (setLIntegral_congr_fun_ae measurableSet_ball ?_).trans (setLIntegral_one _)
    filter_upwards [W.density_prod_ae_eq_one] with y hy _
    simpa [f, g] using hy
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict (ball x r)) W.holder
    hf.restrict hg.restrict
  have hfg : ∫⁻ y in ball x r, (f * g) y ∂volume = ∫⁻ y in ball x r, f y * g y ∂volume :=
    setLIntegral_congr_fun measurableSet_ball fun y _ => Pi.mul_apply f g y
  have hfint : ∫⁻ y in ball x r, f y ^ p ∂volume = ∫⁻ y in ball x r, ρ y ∂volume :=
    setLIntegral_congr_fun measurableSet_ball fun y _ => by
      simp only [f]
      rw [← rpow_mul, one_div, inv_mul_cancel₀ W.p_pos.ne', rpow_one]
  have hgint : ∫⁻ y in ball x r, g y ^ W.conj ∂volume =
      ∫⁻ y in ball x r, δ y ∂volume :=
    setLIntegral_congr_fun measurableSet_ball fun y _ => by
      simp only [g]
      rw [← rpow_mul, one_div, inv_mul_cancel₀ W.conj_pos.ne', rpow_one]
  have hsmall : volume (ball x r) ≤
      (∫⁻ y in ball x r, ρ y ∂volume) ^ (1 / p) *
        (∫⁻ y in ball x r, δ y ∂volume) ^ (1 / W.conj) := by
    rw [hfg, hprod, hfint, hgint] at hH
    exact hH
  have hmono : (∫⁻ y in ball x r, δ y ∂volume) ^ (1 / W.conj) ≤
      (∫⁻ y in ball x R, δ y ∂volume) ^ (1 / W.conj) :=
    rpow_le_rpow (lintegral_mono_set (ball_subset_ball hR))
      (div_nonneg zero_le_one W.conj_pos.le)
  have hle : volume (ball x r) ≤
      (∫⁻ y in ball x r, ρ y ∂volume) ^ (1 / p) *
        (∫⁻ y in ball x R, δ y ∂volume) ^ (1 / W.conj) :=
    hsmall.trans (mul_le_mul_right hmono _)
  have hp0 : 0 ≤ p := W.p_pos.le
  have hraise := rpow_le_rpow hle hp0
  have hmulp : ((∫⁻ y in ball x r, ρ y ∂volume) ^ (1 / p) *
      (∫⁻ y in ball x R, δ y ∂volume) ^ (1 / W.conj)) ^ p =
      (∫⁻ y in ball x r, ρ y ∂volume) *
        (∫⁻ y in ball x R, δ y ∂volume) ^ (p - 1) := by
    rw [mul_rpow_of_nonneg _ _ hp0]
    refine congr_arg₂ HMul.hMul ?_ ?_
    · rw [← rpow_mul, one_div, inv_mul_cancel₀ W.p_pos.ne', rpow_one]
    · rw [← rpow_mul]
      exact congrArg
        (fun t : ℝ => (∫⁻ y in ball x R, δ y ∂volume) ^ t)
        (by rw [mul_comm, ← div_eq_mul_one_div]; exact W.div_conj)
  rw [hmulp] at hraise
  simpa [ρ, δ] using hraise

/-- The weight measure of a concentric enlargement. -/
lemma weight_doubling (W : ApWeight (d := d) p) {c : ℝ} (hc : 1 ≤ c) (x : E) {r : ℝ}
    (hr : 0 < r) :
    weightMeasure W.w (ball x (c * r)) ≤
      W.A * ENNReal.ofReal (c ^ d) ^ p * weightMeasure W.w (ball x r) := by
  have hc0 : 0 < c := by linarith
  have hR : r ≤ c * r := by nlinarith [hr, hc]
  let vE := volume (ball x r)
  let vQ := volume (ball x (c * r))
  let wE := ∫⁻ y in ball x r, weightDensity W.w y ∂volume
  let wQ := ∫⁻ y in ball x (c * r), weightDensity W.w y ∂volume
  let sQ := ∫⁻ y in ball x (c * r), dualDensity p W.w y ∂volume
  have hvE0 : vE ≠ 0 := volume_ball_ne_zero x hr
  have hvEt : vE ≠ ∞ := volume_ball_ne_top x r
  have hvQ0 : vQ ≠ 0 := volume_ball_ne_zero x (mul_pos hc0 hr)
  have hvQt : vQ ≠ ∞ := volume_ball_ne_top x (c * r)
  have hwQ0 : wQ ≠ 0 := W.weight_ball_ne_zero x (mul_pos hc0 hr)
  have hwQt : wQ ≠ ∞ := W.weight_ball_ne_top x (c * r)
  have hhold := W.volume_pow_le_weight_mul_dual (x := x) hR
  have hchar : wQ / vQ * (sQ / vQ) ^ (p - 1) ≤ W.A :=
    W.ball_le x (c * r) (mul_pos hc0 hr)
  have hrearr := rearrange_ap W.hp hvE0 hvEt hvQ0 hvQt hwQ0 hwQt hhold hchar
  have hvol : vQ / vE = ENNReal.ofReal (c ^ d) := by
    have hvQ' : vQ = volume (ball x (c * r)) := rfl
    have hvE' : vE = volume (ball x r) := rfl
    rw [hvQ', hvE', ball_volume_mul hc0 hr x x, ENNReal.mul_div_cancel_right hvE0 hvEt]
  have hmeasE : weightMeasure W.w (ball x r) = wE := by
    rw [weightMeasure, withDensity_apply _ measurableSet_ball]
  have hmeasQ : weightMeasure W.w (ball x (c * r)) = wQ := by
    rw [weightMeasure, withDensity_apply _ measurableSet_ball]
  rw [hvol] at hrearr
  rw [hmeasE, hmeasQ]
  exact hrearr

/-- The dual ball product is the original product to the power `1/(p-1)`. -/
lemma dual_ballProduct_le (W : ApWeight (d := d) p) (x : E) {r : ℝ} (hr : 0 < r) :
    (∫⁻ y in ball x r, dualDensity p W.w y ∂volume) / volume (ball x r) *
      (((∫⁻ y in ball x r, weightDensity W.w y ∂volume) / volume (ball x r)) ^
        (W.conj - 1)) ≤ W.A ^ (p - 1)⁻¹ := by
  have hchar := W.ball_le x r hr
  have hp1 : 0 ≤ (p - 1)⁻¹ := inv_nonneg.mpr W.sub_one_pos.le
  rw [W.conj_sub_one]
  have hident : (∫⁻ y in ball x r, dualDensity p W.w y ∂volume) / volume (ball x r) *
      (((∫⁻ y in ball x r, weightDensity W.w y ∂volume) / volume (ball x r)) ^
        (p - 1)⁻¹) = ballProduct p W.w x r ^ (p - 1)⁻¹ := by
    simp only [ballProduct]
    rw [mul_rpow_of_nonneg _ _ hp1, ← rpow_mul, mul_inv_cancel₀ W.sub_one_pos.ne', rpow_one,
      mul_comm]
  rw [hident]
  exact rpow_le_rpow hchar hp1

/-- Hölder comparison with the conjugate exponent on the dual density. -/
lemma volume_pow_le_dual_mul_weight (W : ApWeight (d := d) p) {x : E} {r R : ℝ}
    (hR : r ≤ R) :
    volume (ball x r) ^ W.conj ≤
      (∫⁻ y in ball x r, dualDensity p W.w y ∂volume) *
        (∫⁻ y in ball x R, weightDensity W.w y ∂volume) ^ (W.conj - 1) := by
  let ρ := dualDensity p W.w
  let δ := weightDensity W.w
  let f := fun y => ρ y ^ (1 / W.conj)
  let g := fun y => δ y ^ (1 / p)
  have hf : AEMeasurable f volume := W.aemeasurable_dualDensity.pow_const _
  have hg : AEMeasurable g volume := (W.measurable_weightDensity.pow_const _).aemeasurable
  have hswap : W.conj.HolderConjugate p := W.holder.symm
  have hprod : ∫⁻ y in ball x r, f y * g y ∂volume = volume (ball x r) := by
    refine (setLIntegral_congr_fun_ae measurableSet_ball ?_).trans (setLIntegral_one _)
    filter_upwards [W.density_prod_ae_eq_one] with y hy _
    simpa [f, g, mul_comm] using hy
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict (ball x r)) hswap
    hf.restrict hg.restrict
  have hfg : ∫⁻ y in ball x r, (f * g) y ∂volume = ∫⁻ y in ball x r, f y * g y ∂volume :=
    setLIntegral_congr_fun measurableSet_ball fun y _ => Pi.mul_apply f g y
  have hfint : ∫⁻ y in ball x r, f y ^ W.conj ∂volume =
      ∫⁻ y in ball x r, ρ y ∂volume :=
    setLIntegral_congr_fun measurableSet_ball fun y _ => by
      simp only [f]
      rw [← rpow_mul, one_div, inv_mul_cancel₀ W.conj_pos.ne', rpow_one]
  have hgint : ∫⁻ y in ball x r, g y ^ p ∂volume = ∫⁻ y in ball x r, δ y ∂volume :=
    setLIntegral_congr_fun measurableSet_ball fun y _ => by
      simp only [g]
      rw [← rpow_mul, one_div, inv_mul_cancel₀ W.p_pos.ne', rpow_one]
  have hsmall : volume (ball x r) ≤
      (∫⁻ y in ball x r, ρ y ∂volume) ^ (1 / W.conj) *
        (∫⁻ y in ball x r, δ y ∂volume) ^ (1 / p) := by
    rw [hfg, hprod, hfint, hgint] at hH
    exact hH
  have hmono : (∫⁻ y in ball x r, δ y ∂volume) ^ (1 / p) ≤
      (∫⁻ y in ball x R, δ y ∂volume) ^ (1 / p) :=
    rpow_le_rpow (lintegral_mono_set (ball_subset_ball hR))
      (div_nonneg zero_le_one W.p_pos.le)
  have hle : volume (ball x r) ≤
      (∫⁻ y in ball x r, ρ y ∂volume) ^ (1 / W.conj) *
        (∫⁻ y in ball x R, δ y ∂volume) ^ (1 / p) :=
    hsmall.trans (mul_le_mul_right hmono _)
  have hq0 : 0 ≤ W.conj := W.conj_pos.le
  have hraise := rpow_le_rpow hle hq0
  have hmulp : ((∫⁻ y in ball x r, ρ y ∂volume) ^ (1 / W.conj) *
      (∫⁻ y in ball x R, δ y ∂volume) ^ (1 / p)) ^ W.conj =
      (∫⁻ y in ball x r, ρ y ∂volume) *
        (∫⁻ y in ball x R, δ y ∂volume) ^ (W.conj - 1) := by
    rw [mul_rpow_of_nonneg _ _ hq0]
    refine congr_arg₂ HMul.hMul ?_ ?_
    · rw [← rpow_mul, one_div, inv_mul_cancel₀ W.conj_pos.ne', rpow_one]
    · rw [← rpow_mul]
      exact congrArg
        (fun t : ℝ => (∫⁻ y in ball x R, δ y ∂volume) ^ t)
        (by rw [mul_comm, ← div_eq_mul_one_div]; exact W.holder.symm.div_conj_eq_sub_one)
  rw [hmulp] at hraise
  simpa [ρ, δ] using hraise

/-- The dual measure of a concentric enlargement. -/
lemma dual_doubling (W : ApWeight (d := d) p) {c : ℝ} (hc : 1 ≤ c) (x : E) {r : ℝ}
    (hr : 0 < r) :
    dualMeasure p W.w (ball x (c * r)) ≤
      W.A ^ (p - 1)⁻¹ * ENNReal.ofReal (c ^ d) ^ W.conj *
        dualMeasure p W.w (ball x r) := by
  have hc0 : 0 < c := by linarith
  have hcr : 0 < c * r := mul_pos hc0 hr
  have hR : r ≤ c * r := by nlinarith [hr, hc]
  let vE := volume (ball x r)
  let vQ := volume (ball x (c * r))
  let wE := ∫⁻ y in ball x r, dualDensity p W.w y ∂volume
  let wQ := ∫⁻ y in ball x (c * r), dualDensity p W.w y ∂volume
  let sQ := ∫⁻ y in ball x (c * r), weightDensity W.w y ∂volume
  have hvE0 : vE ≠ 0 := volume_ball_ne_zero x hr
  have hvEt : vE ≠ ∞ := volume_ball_ne_top x r
  have hvQ0 : vQ ≠ 0 := volume_ball_ne_zero x hcr
  have hvQt : vQ ≠ ∞ := volume_ball_ne_top x (c * r)
  have hwQ0 : wQ ≠ 0 := W.dual_ball_ne_zero x hcr
  have hwQt : wQ ≠ ∞ := W.dual_ball_ne_top x hcr
  have hhold := W.volume_pow_le_dual_mul_weight (x := x) hR
  have hchar : wQ / vQ * (sQ / vQ) ^ (W.conj - 1) ≤ W.A ^ (p - 1)⁻¹ := by
    simpa [wQ, vQ, sQ] using W.dual_ballProduct_le x hcr
  have hrearr := rearrange_ap W.one_lt_conj hvE0 hvEt hvQ0 hvQt hwQ0 hwQt hhold hchar
  have hvol : vQ / vE = ENNReal.ofReal (c ^ d) := by
    have hvQ' : vQ = volume (ball x (c * r)) := rfl
    have hvE' : vE = volume (ball x r) := rfl
    rw [hvQ', hvE', ball_volume_mul hc0 hr x x, ENNReal.mul_div_cancel_right hvE0 hvEt]
  have hmeasE : dualMeasure p W.w (ball x r) = wE := by
    rw [dualMeasure, withDensity_apply _ measurableSet_ball]
  have hmeasQ : dualMeasure p W.w (ball x (c * r)) = wQ := by
    rw [dualMeasure, withDensity_apply _ measurableSet_ball]
  rw [hvol] at hrearr
  rw [hmeasE, hmeasQ]
  exact hrearr

end ApWeight

/-- A closed ball of radius `4r` sits in the concentric ball of radius `5r`. -/
lemma closedBall_subset_concentric_five {x : E} {r : ℝ} (hr : 0 < r) :
    closedBall x (4 * r) ⊆ ball x (5 * r) := by
  intro z hz
  have hzx : dist z x ≤ 4 * r := mem_closedBall.mp hz
  exact mem_ball.mpr (hzx.trans_lt (by nlinarith [hr]))

/-- A ball sits in the double ball about any of its points. -/
lemma ball_subset_double_ball {x y : E} {r : ℝ} (hy : y ∈ ball x r) :
    ball x r ⊆ ball y (2 * r) := by
  intro z hz
  have hzx : dist z x < r := mem_ball.mp hz
  have hxy : dist x y < r := by simpa [dist_comm] using mem_ball.mp hy
  exact mem_ball.mpr (by linarith [dist_triangle z x y])

/-- Doubling the radius about a nearby centre stays inside the triple ball. -/
lemma ball_two_subset_ball_three {x y : E} {r : ℝ} (hy : y ∈ ball x r) :
    ball y (2 * r) ⊆ ball x (3 * r) := by
  intro z hz
  have hzy : dist z y < 2 * r := mem_ball.mp hz
  have hxy : dist y x < r := mem_ball.mp hy
  exact mem_ball.mpr (by linarith [dist_triangle z y x])

end CKMA
