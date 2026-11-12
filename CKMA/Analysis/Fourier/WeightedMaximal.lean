/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import TauCeti.MeasureTheory.Integral.MaximalFunction
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Covering.Vitali
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Muckenhoupt weights and maximal estimates

The ball A_p characteristic averages a positive weight and its reciprocal power.
Weighted Lᵖ boundedness of the centered Hardy–Littlewood maximal operator characterizes
A_p for `p > 1`; A₁ weights satisfy the weighted weak (1,1) estimate. The maximal
operator is TauCeti's `maximalFunction`, with Euclidean balls fixing the characteristic
normalization.

Source: GAPS 27.44.
-/

@[expose] public section

noncomputable section

namespace CKMA

open MeasureTheory MeasureTheory.Measure Metric Filter Set Topology ENNReal TauCeti
open scoped ENNReal

/-- The measure with a nonnegative real weight as density. -/
def weightedLebesgueMeasure {d : ℕ} (w : EuclideanSpace ℝ (Fin d) → ℝ) :
    Measure (EuclideanSpace ℝ (Fin d)) := volume.withDensity (fun x ↦ ENNReal.ofReal (w x))

/-- The ball A_p characteristic. Balls and axis-parallel cubes give equivalent finite classes
in Euclidean space, but the characteristic constants themselves depend on this convention. -/
def muckenhouptCharacteristic {d : ℕ} (p : ℝ) (w : EuclideanSpace ℝ (Fin d) → ℝ) : ℝ≥0∞ :=
  ⨆ (x : EuclideanSpace ℝ (Fin d)) (r : ℝ) (_hr : 0 < r),
    ((∫⁻ y in Metric.ball x r, ENNReal.ofReal (w y)) / volume (Metric.ball x r)) *
      (((∫⁻ y in Metric.ball x r, ENNReal.ofReal ((w y) ^ (-(p - 1)⁻¹))) /
        volume (Metric.ball x r)) ^ (p - 1))

/-- Positive, locally integrable A_p weights, with the characteristic retaining infinity. -/
def IsMuckenhouptWeight {d : ℕ} (p : ℝ) (w : EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  1 < p ∧ Measurable w ∧ (∀ᵐ x ∂volume, 0 < w x) ∧ LocallyIntegrable w volume ∧
    muckenhouptCharacteristic p w < ∞

/-- The A_1 class, using TauCeti's centered maximal function and its actual positive bound. -/
def IsMuckenhouptOneWeight {d : ℕ} (w : EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  Measurable w ∧ (∀ᵐ x ∂volume, 0 < w x) ∧ LocallyIntegrable w volume ∧
    ∃ C : ℝ, 0 < C ∧ ∀ᵐ x ∂volume,
      TauCeti.maximalFunction volume w x ≤ ENNReal.ofReal (C * w x)

section Aux

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

local notation "ofReal" => ENNReal.ofReal

open Classical

/-- Scaling the radius of a Euclidean ball by `c > 0` multiplies its volume by `c ^ d`. -/
private lemma ball_volume_mul {c r : ℝ} (hc : 0 < c) (hr : 0 < r) (x y : E) :
    volume (ball y (c * r)) = ofReal (c ^ d) * volume (ball x r) := by
  have hcr : 0 < c * r := mul_pos hc hr
  rw [addHaar_ball_of_pos volume y hcr, addHaar_ball_of_pos volume x hr,
    finrank_euclideanSpace_fin, mul_pow, ofReal_mul (pow_nonneg hc.le _), mul_assoc]

/-- A fourfold closed ball about `x` sits in the fivefold open ball about any nearby centre. -/
private lemma closedBall_subset_ball_five {x y : E} {r : ℝ}
    (hy : y ∈ ball x r) : closedBall x (4 * r) ⊆ ball y (5 * r) := by
  intro z hz
  have hzx : dist z x ≤ 4 * r := mem_closedBall.mp hz
  have hxy : dist x y < r := by simpa [dist_comm] using mem_ball.mp hy
  have hdist : dist z y < 5 * r := by
    calc dist z y ≤ dist z x + dist x y := dist_triangle z x y
      _ < 4 * r + r := add_lt_add_of_le_of_lt hzx hxy
      _ = 5 * r := by ring
  exact mem_ball.mpr hdist

/-- Doubling the radius still contains the original ball. -/
private lemma ball_subset_ball_two {x y : E} {r : ℝ} (hy : y ∈ ball x r) :
    ball x r ⊆ ball y (2 * r) := by
  intro z hz
  have hzx : dist z x < r := mem_ball.mp hz
  have hxy : dist x y < r := by simpa [dist_comm] using mem_ball.mp hy
  exact mem_ball.mpr <| by linarith [dist_triangle z x y]

/-- Integrals agree when the integrand vanishes off the smaller set. -/
private lemma setLIntegral_eq_of_support {g : E → ℝ≥0∞} {s t : Set E}
    (hs : MeasurableSet s) (ht : MeasurableSet t) (hst : s ⊆ t)
    (hsupp : ∀ z, z ∉ s → g z = 0) :
    ∫⁻ z in t, g z ∂volume = ∫⁻ z in s, g z ∂volume := by
  apply le_antisymm
  · calc ∫⁻ z in t, g z ∂volume
        = ∫⁻ z in t, s.indicator g z ∂volume := by
          refine setLIntegral_congr_fun ht fun z hz => ?_
          by_cases hzs : z ∈ s
          · simp [hzs]
          · simp [hzs, hsupp z hzs]
      _ ≤ ∫⁻ z, s.indicator g z ∂volume := setLIntegral_le_lintegral _ _
      _ = ∫⁻ z in s, g z ∂volume := lintegral_indicator hs g
  · exact lintegral_mono_set hst

/-- A strict ball average above `t` survives at nearby centres, for one slightly larger radius. -/
private lemma exists_radius_nhds_average_gt {F : Type*} [ENorm F] {f : E → F} {x : E}
    {t : ℝ≥0∞} (ht : t < maximalFunction volume f x) :
    ∃ s δ : ℝ, 0 < s ∧ 0 < δ ∧ ∀ y, dist y x < δ →
      t * volume (ball y s) < ∫⁻ z in ball y s, ‖f z‖ₑ ∂volume := by
  obtain ⟨r, hr, hlt⟩ := lt_maximalFunction_iff.mp ht
  let unit : ℝ≥0∞ := volume (ball (0 : E) 1)
  have hunit0 : unit ≠ 0 := (measure_ball_pos volume (0 : E) one_pos).ne'
  have hunittop : unit ≠ ∞ := measure_ball_lt_top.ne
  let scale : ℝ → ℝ≥0∞ := fun s => ofReal (s ^ Module.finrank ℝ E) * unit
  have hscale0 : ∀ s : ℝ, 0 < s → scale s ≠ 0 := fun s hs =>
    mul_ne_zero (ofReal_pos.mpr (pow_pos hs _)).ne' hunit0
  rw [setLAverage_eq] at hlt
  have hmul : t * scale r < ∫⁻ y in ball x r, ‖f y‖ₑ ∂volume := by
    unfold scale
    rw [← addHaar_ball_of_pos volume x hr]
    exact mul_lt_of_lt_div hlt
  have hcont : Tendsto (fun s : ℝ => t * scale s) (𝓝 r) (𝓝 (t * scale r)) :=
    ENNReal.Tendsto.const_mul
      (ENNReal.Tendsto.mul_const
        ((continuous_ofReal.tendsto _).comp ((continuous_pow _).tendsto r))
        (.inr hunittop))
      (.inl (hscale0 r hr))
  have hev : ∀ᶠ s : ℝ in 𝓝[>] r, t * scale s < ∫⁻ y in ball x r, ‖f y‖ₑ ∂volume :=
    (hcont.mono_left nhdsWithin_le_nhds).eventually_lt_const hmul
  obtain ⟨s, hs, hrs⟩ := (hev.and self_mem_nhdsWithin).exists
  have hrs' : r < s := hrs
  refine ⟨s, s - r, hr.trans hrs', sub_pos.mpr hrs', ?_⟩
  intro y hy
  have hsub : ball x r ⊆ ball y s := by
    intro z hz
    have hzx : dist z x < r := mem_ball.mp hz
    have hxy : dist x y < s - r := by simpa [dist_comm] using hy
    exact mem_ball.mpr <| by linarith [dist_triangle z x y]
  rw [show volume (ball y s) = scale s by
    rw [addHaar_ball_of_pos volume y (hr.trans hrs')]]
  exact hs.trans_le (lintegral_mono_set hsub)

/-- `ofReal (w y)` is at most the extended norm of the real value `w y`. -/
private lemma ofReal_w_le_enorm (w : E → ℝ) (y : E) : ofReal (w y) ≤ ‖w y‖ₑ :=
  (ofReal_le_ofReal ((le_abs_self (w y)).trans_eq (Real.norm_eq_abs _).symm)).trans_eq
    (ofReal_norm (w y))

/-- A locally integrable weight charges every closed ball finitely. -/
private lemma weighted_closedBall_lt_top {w : E → ℝ} (hloc : LocallyIntegrable w volume)
    (x : E) (r : ℝ) : weightedLebesgueMeasure w (closedBall x r) < ∞ := by
  rw [weightedLebesgueMeasure, withDensity_apply _ isClosed_closedBall.measurableSet]
  exact lt_of_le_of_lt
    (setLIntegral_mono' isClosed_closedBall.measurableSet fun _ _ => ofReal_w_le_enorm w _)
    (hasFiniteIntegral_iff_enorm.mp
      (hloc.integrableOn_isCompact (isCompact_closedBall x r)).hasFiniteIntegral)

/-- One selected ball in the A₁ covering: the weight on the fourfold ball is controlled by the
integral of `g` against the weight on the original ball. -/
private lemma one_ball_weighted_estimate {w : E → ℝ} {C : ℝ} (hC : 0 < C)
    (hA : ∀ᵐ x ∂volume, maximalFunction volume w x ≤ ofReal (C * w x))
    (hpos : ∀ᵐ x ∂volume, 0 < w x) (hloc : LocallyIntegrable w volume) {x : E} {r : ℝ}
    (hr : 0 < r) {t : ℝ≥0∞} {g : E → ℝ≥0∞}
    (havg : t * volume (ball x r) ≤ ∫⁻ y in ball x r, g y ∂volume) :
    t * ∫⁻ y in closedBall x (4 * r), ofReal (w y) ∂volume ≤
      ofReal C * (5 : ℝ≥0∞) ^ d * ∫⁻ y in ball x r, g y * ofReal (w y) ∂volume := by
  let v : ℝ≥0∞ := volume (ball x r)
  let five : ℝ≥0∞ := (5 : ℝ≥0∞) ^ d
  let c : ℝ≥0∞ := ofReal C * five
  let coef : ℝ≥0∞ := c * v
  let I4 : ℝ≥0∞ := ∫⁻ z in closedBall x (4 * r), ofReal (w z) ∂volume
  have hv0 : v ≠ 0 := (measure_ball_pos volume x hr).ne'
  have hvtop : v ≠ ∞ := measure_ball_lt_top.ne
  have hfive0 : five ≠ 0 := pow_ne_zero _ (by simp : (5 : ℝ≥0∞) ≠ 0)
  have hfivetop : five ≠ ∞ := pow_ne_top (by simp : (5 : ℝ≥0∞) ≠ ∞)
  have hC0 : ofReal C ≠ 0 := by simpa [ofReal_eq_zero] using not_le.mpr hC
  have hCtop : ofReal C ≠ ∞ := ofReal_ne_top
  have hc0 : c ≠ 0 := mul_ne_zero hC0 hfive0
  have hctop : c ≠ ∞ := mul_ne_top hCtop hfivetop
  have hcoef0 : coef ≠ 0 := mul_ne_zero hc0 hv0
  have hcoeftop : coef ≠ ∞ := mul_ne_top hctop hvtop
  have hI4top : I4 ≠ ∞ := by
    unfold I4
    rw [← withDensity_apply _ isClosed_closedBall.measurableSet]
    exact (weighted_closedBall_lt_top hloc x (4 * r)).ne
  have hvol : ∀ y : E, volume (ball y (5 * r)) = five * v := by
    intro y
    rw [ball_volume_mul (by norm_num : (0 : ℝ) < 5) hr x y]
    simp [five, v, ofReal_pow (by norm_num : (0 : ℝ) ≤ 5), ofReal_ofNat]
  have hlow : ∀ᵐ y ∂volume, y ∈ ball x r → I4 / coef ≤ ofReal (w y) := by
    filter_upwards [hA, hpos] with y hAy hypos hy
    have hsub : closedBall x (4 * r) ⊆ ball y (5 * r) := closedBall_subset_ball_five hy
    have hI : I4 ≤ ∫⁻ z in ball y (5 * r), ‖w z‖ₑ ∂volume := by
      calc I4
          ≤ ∫⁻ z in ball y (5 * r), ofReal (w z) ∂volume := lintegral_mono_set hsub
        _ ≤ ∫⁻ z in ball y (5 * r), ‖w z‖ₑ ∂volume :=
            lintegral_mono fun z => ofReal_w_le_enorm w z
    have havgle : ∫⁻ z in ball y (5 * r), ‖w z‖ₑ ∂volume ≤
        maximalFunction volume w y * volume (ball y (5 * r)) := by
      have hdiv := setLAverage_le_maximalFunction volume w y
        (mul_pos (by norm_num : (0 : ℝ) < 5) hr)
      rw [setLAverage_eq] at hdiv
      exact (ENNReal.div_le_iff
        (measure_ball_pos volume y (mul_pos (by norm_num : (0 : ℝ) < 5) hr)).ne'
        measure_ball_lt_top.ne).mp hdiv
    have hsplit : ofReal (C * w y) * (five * v) = ofReal (w y) * coef := by
      simp only [coef, c]
      rw [ofReal_mul hC.le]
      ac_rfl
    have hbound : I4 ≤ ofReal (w y) * coef := by
      calc I4
          ≤ maximalFunction volume w y * volume (ball y (5 * r)) := hI.trans havgle
        _ ≤ ofReal (C * w y) * (five * v) := by rw [hvol]; exact mul_le_mul' hAy le_rfl
        _ = ofReal (w y) * coef := hsplit
    exact div_le_of_le_mul hbound
  have hconst : I4 / coef ≠ ∞ := div_ne_top hI4top hcoef0
  have hcancel : I4 / coef * v = I4 / c := by
    have hv : v = coef / c := by
      rw [show coef = v * c by simp only [coef, mul_comm]]
      exact (ENNReal.mul_div_cancel_right hc0 hctop).symm
    rw [hv]
    exact ENNReal.div_mul_div_cancel hcoef0 hcoeftop
  have hassoc : I4 / coef * (t * v) = t * I4 / c := by
    calc I4 / coef * (t * v)
        = t * (I4 / coef * v) := by rw [mul_left_comm]
      _ = t * (I4 / c) := by rw [hcancel]
      _ = t * I4 / c := by rw [div_eq_mul_inv, ← mul_assoc, ← div_eq_mul_inv]
  have hrestore : c * (I4 / coef * (t * v)) = t * I4 := by
    rw [hassoc, ENNReal.mul_div_cancel hc0 hctop]
  have hlower : I4 / coef * ∫⁻ y in ball x r, g y ∂volume ≤
      ∫⁻ y in ball x r, g y * ofReal (w y) ∂volume := by
    rw [← lintegral_const_mul' _ _ hconst]
    refine setLIntegral_mono_ae' measurableSet_ball ?_
    filter_upwards [hlow] with y hy
    intro hmem
    rw [mul_comm (g y)]
    exact mul_le_mul' (hy hmem) le_rfl
  calc t * I4
      = c * (I4 / coef * (t * v)) := hrestore.symm
    _ ≤ c * (I4 / coef * ∫⁻ y in ball x r, g y ∂volume) := by
        exact mul_le_mul' le_rfl (mul_le_mul' le_rfl havg)
    _ ≤ c * ∫⁻ y in ball x r, g y * ofReal (w y) ∂volume :=
        mul_le_mul' le_rfl hlower

/-- Compact subsets of a maximal superlevel set obey the weighted weak bound. -/
private lemma weighted_compact_mul_le {w : E → ℝ} {C : ℝ} (hm : Measurable w) (hC : 0 < C)
    (hA : ∀ᵐ x ∂volume, maximalFunction volume w x ≤ ofReal (C * w x))
    (hpos : ∀ᵐ x ∂volume, 0 < w x) (hloc : LocallyIntegrable w volume) {a : ℝ} (_ha : 0 < a)
    {f : E → ℂ} {K : Set E} (hK : IsCompact K)
    (hsub : K ⊆ {x | ofReal a < maximalFunction volume f x}) :
    ofReal a * weightedLebesgueMeasure w K ≤
      ofReal C * (5 : ℝ≥0∞) ^ d * ∫⁻ x, ‖f x‖ₑ ∂weightedLebesgueMeasure w := by
  classical
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · simp
  have hex : ∀ x ∈ K, ∃ s δ : ℝ, 0 < s ∧ 0 < δ ∧ ∀ y, dist y x < δ →
      ofReal a * volume (ball y s) < ∫⁻ z in ball y s, ‖f z‖ₑ ∂volume :=
    fun x hx => exists_radius_nhds_average_gt (hsub hx)
  choose! s δ hs hδ hnear using hex
  obtain ⟨t, ht, hcover⟩ := hK.elim_nhds_subcover (fun x => ball x (δ x))
    (fun x hx => ball_mem_nhds x (hδ x hx))
  let R : ℝ := ∑ x ∈ t, s x
  have hpoint : ∀ z ∈ K, ∃ radius ∈ Ioc (0 : ℝ) R,
      ofReal a * volume (ball z radius) ≤ ∫⁻ y in ball z radius, ‖f y‖ₑ ∂volume := by
    intro z hz
    obtain ⟨c, hc, hzc⟩ := mem_iUnion₂.mp (hcover hz)
    refine ⟨s c, ⟨hs c (ht c hc), Finset.single_le_sum (fun y hy => (hs y (ht y hy)).le) hc⟩,
      (hnear c (ht c hc) z (mem_ball.mp hzc)).le⟩
  choose! radius hrad havg using hpoint
  obtain ⟨u, hu, hdisj, hcov⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall K id radius R
      (fun z hz => (hrad z hz).2) 4 (by norm_num)
  simp only [id_eq] at hdisj hcov
  have hcount : u.Countable :=
    hdisj.countable_of_nonempty_interior fun z hz =>
      ⟨z, ball_subset_interior_closedBall (mem_ball_self (hrad z (hu hz)).1)⟩
  have : Countable u := hcount.to_subtype
  have hcoverK : K ⊆ ⋃ b ∈ u, closedBall b (4 * radius b) := by
    intro z hz
    obtain ⟨b, hb, hball⟩ := hcov z hz
    exact mem_biUnion hb (hball (mem_closedBall_self (hrad z hz).1.le))
  have hdisjOpen : Pairwise (Function.onFun Disjoint fun b : u => ball (b : E) (radius b)) :=
    fun b b' hbb => (hdisj b.2 b'.2 (Subtype.coe_injective.ne hbb)).mono
      ball_subset_closedBall ball_subset_closedBall
  let g : E → ℝ≥0∞ := fun y => ‖f y‖ₑ * ofReal (w y)
  let five : ℝ≥0∞ := (5 : ℝ≥0∞) ^ d
  let ν : Measure E := weightedLebesgueMeasure w
  calc ofReal a * ν K
      ≤ ofReal a * ∑' b : u, ν (closedBall (b : E) (4 * radius b)) := by
        refine mul_le_mul' le_rfl ?_
        exact (measure_mono hcoverK).trans
          (measure_biUnion_le ν hcount fun b => closedBall (b : E) (4 * radius b))
    _ = ∑' b : u, ofReal a * ∫⁻ y in closedBall (b : E) (4 * radius b), ofReal (w y) := by
        rw [ENNReal.tsum_mul_left.symm]
        refine congrArg tsum (funext fun b => ?_)
        rw [show ν = volume.withDensity (fun y => ofReal (w y)) from rfl,
          withDensity_apply _ isClosed_closedBall.measurableSet]
    _ ≤ ∑' b : u, ofReal C * five *
          ∫⁻ y in ball (b : E) (radius b), g y ∂volume := by
        refine ENNReal.tsum_le_tsum fun b => ?_
        simpa [g, five] using one_ball_weighted_estimate hC hA hpos hloc
          (hrad b (hu b.2)).1 (havg b (hu b.2))
    _ = ofReal C * five * ∑' b : u, ∫⁻ y in ball (b : E) (radius b), g y ∂volume :=
        ENNReal.tsum_mul_left
    _ = ofReal C * five * ∫⁻ y in ⋃ b : u, ball (b : E) (radius b), g y ∂volume := by
        rw [lintegral_iUnion (fun _ => measurableSet_ball) hdisjOpen]
    _ ≤ ofReal C * five * ∫⁻ y, g y ∂volume :=
        mul_le_mul' le_rfl (setLIntegral_le_lintegral _ _)
    _ = ofReal C * five * ∫⁻ y, ‖f y‖ₑ ∂ν := by
        rw [show ν = volume.withDensity (ofReal ∘ w) from rfl]
        rw [lintegral_withDensity_eq_lintegral_mul_non_measurable volume
          (continuous_ofReal.measurable.comp hm) (ae_of_all _ fun _ => ofReal_lt_top)]
        refine congrArg (fun t => ofReal C * five * t) ?_
        refine lintegral_congr fun y => ?_
        simp only [g]
        rw [Pi.mul_apply, Function.comp_apply, mul_comm]

/-- The exponent `-(p - 1)⁻¹` appearing in the dual average of an A_p product. -/
private def conjugateExponent (p : ℝ) : ℝ := -((p - 1)⁻¹)

/-- `conjugateExponent p * p + 1` collapses back to the same exponent. -/
private lemma conjugateExponent_mul_self {p : ℝ} (hp : 1 < p) :
    conjugateExponent p * p + 1 = conjugateExponent p := by
  have hne : p - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt hp)
  unfold conjugateExponent
  field_simp [hne]
  ring

/-- The nonnegative representative of `w ^ conjugateExponent p`, equal to zero where `w ≤ 0`. -/
private def dualPower (p : ℝ) (w : E → ℝ) (y : E) : ℝ :=
  if 0 < w y then Real.exp (Real.log (w y) * conjugateExponent p) else 0

/-- `dualPower` agrees with the real power on the positive set. -/
private lemma dualPower_rpow {p : ℝ} {w : E → ℝ} {y : E} (hy : 0 < w y) :
    dualPower p w y = w y ^ conjugateExponent p := by
  simp [dualPower, hy, Real.rpow_def_of_pos hy]

/-- `dualPower` is nonnegative. -/
private lemma dualPower_nonneg (p : ℝ) (w : E → ℝ) (y : E) : 0 ≤ dualPower p w y := by
  unfold dualPower
  split_ifs with hy
  · exact le_of_lt (Real.exp_pos _)
  · exact le_rfl

/-- `dualPower` is measurable for a measurable weight. -/
private lemma measurable_dualPower {p : ℝ} {w : E → ℝ} (hw : Measurable w) :
    Measurable (dualPower p w) := by
  have hs : MeasurableSet {y | 0 < w y} := measurableSet_lt measurable_const hw
  exact Measurable.ite hs ((hw.log.mul_const _).exp) measurable_const

/-- The dual weight cut off to one ball and one height, as a complex test function. -/
private def truncatedDual (p : ℝ) (w : E → ℝ) (x : E) (r : ℝ) (n : ℕ) (y : E) : ℂ :=
  if y ∈ ball x r ∧ dualPower p w y ≤ (n : ℝ) then Complex.ofReal (dualPower p w y) else 0

/-- The cutoff dual weight is measurable. -/
private lemma measurable_truncatedDual {p : ℝ} {w : E → ℝ} (hw : Measurable w)
    (x : E) (r : ℝ) (n : ℕ) : Measurable (truncatedDual p w x r n) := by
  have hset : MeasurableSet {y | y ∈ ball x r ∧ dualPower p w y ≤ (n : ℝ)} :=
    measurableSet_ball.inter (measurableSet_le (measurable_dualPower hw) measurable_const)
  exact Measurable.ite hset ((Complex.measurable_ofReal.comp (measurable_dualPower hw)))
    measurable_const

/-- Extended norm of the cutoff: the real dual weight on its support, and zero elsewhere. -/
private lemma enorm_truncatedDual (p : ℝ) (w : E → ℝ) (x : E) (r : ℝ) (n : ℕ) (y : E) :
    ‖truncatedDual p w x r n y‖ₑ =
      if y ∈ ball x r ∧ dualPower p w y ≤ (n : ℝ) then ofReal (dualPower p w y) else 0 := by
  by_cases h : y ∈ ball x r ∧ dualPower p w y ≤ (n : ℝ)
  · rw [truncatedDual, ite_eq_left h, ← ofReal_norm, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (dualPower_nonneg p w y), ite_eq_left h]
  · rw [truncatedDual, ite_eq_right h, ite_eq_right h]
    simp

/-- On the support of a dual-weight test function, `‖f‖ₑ ^ p * w = ‖f‖ₑ`. -/
private lemma truncatedDual_testing {p : ℝ} (hp : 1 < p) (w : E → ℝ) (x : E) (r : ℝ)
    (n : ℕ) (y : E) :
    ‖truncatedDual p w x r n y‖ₑ ^ p * ofReal (w y) =
      ‖truncatedDual p w x r n y‖ₑ := by
  have hp0 : 0 < p := lt_trans one_pos hp
  by_cases hmem : y ∈ ball x r ∧ dualPower p w y ≤ (n : ℝ)
  · rw [enorm_truncatedDual, ite_eq_left hmem]
    by_cases hs : dualPower p w y = 0
    · simp [hs, zero_rpow_of_pos hp0]
    · have hposd : 0 < dualPower p w y := by
        refine lt_of_le_of_ne (dualPower_nonneg p w y) ?_
        intro hzero
        exact hs hzero.symm
      have hy : 0 < w y := by
        by_contra hnot
        have : dualPower p w y = 0 := by simp [dualPower, hnot]
        exact hs this
      have hreal : dualPower p w y ^ p * w y = dualPower p w y := by
        calc dualPower p w y ^ p * w y
            = (w y ^ conjugateExponent p) ^ p * w y := by rw [dualPower_rpow hy]
          _ = w y ^ (conjugateExponent p * p) * w y := by
              rw [← Real.rpow_mul (le_of_lt hy)]
          _ = w y ^ (conjugateExponent p * p) * w y ^ (1 : ℝ) := by rw [Real.rpow_one]
          _ = w y ^ (conjugateExponent p * p + 1) := by rw [← Real.rpow_add hy]
          _ = w y ^ conjugateExponent p := by rw [conjugateExponent_mul_self hp]
          _ = dualPower p w y := by rw [dualPower_rpow hy]
      rw [ofReal_rpow_of_pos hposd, ← ofReal_mul (Real.rpow_nonneg hposd.le p), hreal]
  · rw [enorm_truncatedDual, ite_eq_right hmem]
    simp [zero_rpow_of_pos hp0]

/-- Extract the A_p product from a bound `(a / (k b)) ^ p * w ≤ c * a`. -/
private lemma muckenhouptFactor_le {a b c k w : ℝ≥0∞} {p : ℝ} (hp : 1 < p) (ha : a ≠ ∞)
    (hb0 : b ≠ 0) (hb : b ≠ ∞) (hk0 : k ≠ 0) (hk : k ≠ ∞)
    (h : (a / (k * b)) ^ p * w ≤ c * a) :
    (a / b) ^ (p - 1) * (w / b) ≤ c * k ^ p := by
  have hp0 : 0 < p := lt_trans one_pos hp
  have hp1 : 0 < p - 1 := sub_pos.mpr hp
  by_cases ha0 : a = 0
  · simp [ha0, ENNReal.zero_div, zero_rpow_of_pos hp1, zero_mul]
  have hkb0 : k * b ≠ 0 := mul_ne_zero hk0 hb0
  have hkbt : k * b ≠ ∞ := mul_ne_top hk hb
  have hbp0 : b ^ p ≠ 0 := (rpow_eq_zero_iff_of_pos hp0).not.mpr hb0
  have hbpt : b ^ p ≠ ∞ := rpow_ne_top_of_nonneg hp0.le hb
  have hkp0 : k ^ p ≠ 0 := (rpow_eq_zero_iff_of_pos hp0).not.mpr hk0
  have hkpt : k ^ p ≠ ∞ := rpow_ne_top_of_nonneg hp0.le hk
  have hD : (k * b) ^ p = k ^ p * b ^ p := mul_rpow_of_nonneg _ _ hp0.le
  have hD0 : (k * b) ^ p ≠ 0 := by rw [hD]; exact mul_ne_zero hkp0 hbp0
  have hDt : (k * b) ^ p ≠ ∞ := by rw [hD]; exact mul_ne_top hkpt hbpt
  have hpow : a ^ p = a * a ^ (p - 1) := by
    have hsum : a ^ (p - 1) * a ^ (1 : ℝ) = a ^ ((p - 1) + 1) :=
      (rpow_add (p - 1) 1 ha0 ha).symm
    rw [rpow_one, sub_add_cancel] at hsum
    simpa [mul_comm] using hsum.symm
  have hstep : a ^ (p - 1) * w ≤ c * k ^ p * b ^ p := by
    have hrew : a ^ p * w / (k * b) ^ p ≤ c * a := by
      have h0 : a ^ p / (k * b) ^ p * w ≤ c * a := by
        rwa [div_rpow_of_nonneg _ _ hp0.le] at h
      calc a ^ p * w / (k * b) ^ p
          = a ^ p * w * ((k * b) ^ p)⁻¹ := by rw [div_eq_mul_inv]
        _ = a ^ p / (k * b) ^ p * w := by rw [div_eq_mul_inv, mul_right_comm]
        _ ≤ c * a := h0
    have hmul : a ^ p * w ≤ c * a * (k * b) ^ p := (ENNReal.div_le_iff hD0 hDt).mp hrew
    rw [hD, hpow] at hmul
    have hleft : (a * a ^ (p - 1)) * w = a * (a ^ (p - 1) * w) := mul_assoc _ _ _
    have hright : c * a * (k ^ p * b ^ p) = a * (c * k ^ p * b ^ p) := by
      calc c * a * (k ^ p * b ^ p)
          = a * (c * (k ^ p * b ^ p)) := by rw [mul_comm c a, mul_assoc]
        _ = a * (c * k ^ p * b ^ p) := by
            apply congrArg (fun t => a * t)
            rw [← mul_assoc]
    rw [hleft, hright] at hmul
    exact (ENNReal.mul_le_mul_iff_right ha0 ha).mp hmul
  have hdiv : a ^ (p - 1) * w / b ^ p ≤ c * k ^ p :=
    (ENNReal.div_le_iff hbp0 hbpt).mpr hstep
  have hbp1_0 : b ^ (p - 1) ≠ 0 := (rpow_eq_zero_iff_of_pos hp1).not.mpr hb0
  have hbp1t : b ^ (p - 1) ≠ ∞ := rpow_ne_top_of_nonneg hp1.le hb
  have hbpow : b ^ (p - 1) * b = b ^ p := by
    have hsum : b ^ (p - 1) * b ^ (1 : ℝ) = b ^ ((p - 1) + 1) :=
      (rpow_add (p - 1) 1 hb0 hb).symm
    simpa [rpow_one, sub_add_cancel] using hsum
  calc (a / b) ^ (p - 1) * (w / b)
      = a ^ (p - 1) / b ^ (p - 1) * (w / b) := by rw [div_rpow_of_nonneg _ _ hp1.le]
    _ = a ^ (p - 1) * (b ^ (p - 1))⁻¹ * (w * b⁻¹) := by simp only [div_eq_mul_inv]
    _ = a ^ (p - 1) * w * ((b ^ (p - 1))⁻¹ * b⁻¹) := by
        rw [mul_assoc]
        have hinner :
            (b ^ (p - 1))⁻¹ * (w * b⁻¹) = w * ((b ^ (p - 1))⁻¹ * b⁻¹) := by
          rw [mul_left_comm]
        rw [hinner, ← mul_assoc]
    _ = a ^ (p - 1) * w * (b ^ (p - 1) * b)⁻¹ := by
        rw [← ENNReal.mul_inv (Or.inl hbp1_0) (Or.inl hbp1t)]
    _ = a ^ (p - 1) * w / b ^ p := by rw [hbpow, div_eq_mul_inv]
    _ ≤ c * k ^ p := hdiv

/-- One height of the truncated dual weight yields an A_p factor at most the operator constant. -/
private lemma testing_product_le {p : ℝ} (hp : 1 < p) {w : E → ℝ} (hm : Measurable w)
    {C : ℝ≥0∞}
    (hbound : ∀ f : E → ℂ, MemLp f (ofReal p) (weightedLebesgueMeasure w) →
      ∫⁻ y, (maximalFunction volume f y) ^ p ∂weightedLebesgueMeasure w ≤
        C * (eLpNorm f (ofReal p) (weightedLebesgueMeasure w)) ^ p)
    {x : E} {r : ℝ} (hr : 0 < r) (n : ℕ) :
    ((∫⁻ y in ball x r, ‖truncatedDual p w x r n y‖ₑ) / volume (ball x r)) ^ (p - 1) *
      ((∫⁻ y in ball x r, ofReal (w y)) / volume (ball x r)) ≤
        C * ((2 : ℝ≥0∞) ^ d) ^ p := by
  let v : ℝ≥0∞ := volume (ball x r)
  let In : ℝ≥0∞ := ∫⁻ y in ball x r, ‖truncatedDual p w x r n y‖ₑ
  let W : ℝ≥0∞ := ∫⁻ y in ball x r, ofReal (w y)
  let f : E → ℂ := truncatedDual p w x r n
  let ν : Measure E := weightedLebesgueMeasure w
  have hp0 : 0 < p := lt_trans one_pos hp
  have hv0 : v ≠ 0 := (measure_ball_pos volume x hr).ne'
  have hvtop : v ≠ ∞ := measure_ball_lt_top.ne
  have hsupp : ∀ z, z ∉ ball x r → ‖f z‖ₑ = 0 := fun z hz => by
    rw [enorm_truncatedDual, ite_eq_right fun h => hz h.1]
  have hIbound : In ≤ ofReal (n : ℝ) * v := by
    calc In
        ≤ ∫⁻ y in ball x r, ofReal (n : ℝ) ∂volume := by
          refine setLIntegral_mono' measurableSet_ball fun y _hy => ?_
          rw [enorm_truncatedDual]
          split_ifs with hcut
          · exact ofReal_le_ofReal hcut.2
          · exact zero_le
      _ = ofReal (n : ℝ) * v := setLIntegral_const _ _
  have hIne : In ≠ ∞ := ne_top_of_le_ne_top (mul_ne_top ofReal_ne_top hvtop) hIbound
  have hspace : ∫⁻ y, ‖f y‖ₑ ∂volume = In := by
    rw [← setLIntegral_univ]
    exact setLIntegral_eq_of_support measurableSet_ball MeasurableSet.univ (subset_univ _) hsupp
  have hpowInt : ∫⁻ y, ‖f y‖ₑ ^ p ∂ν = In := by
    rw [show ν = volume.withDensity (ofReal ∘ w) from rfl]
    rw [lintegral_withDensity_eq_lintegral_mul_non_measurable volume
      (continuous_ofReal.measurable.comp hm) (ae_of_all _ fun _ => ofReal_lt_top)]
    refine (lintegral_congr fun y => ?_).trans hspace
    rw [mul_comm]
    exact truncatedDual_testing hp w x r n y
  have hfasm : AEStronglyMeasurable f ν :=
    (measurable_truncatedDual hm x r n).aestronglyMeasurable
  have hp_ne : ofReal p ≠ 0 := (ofReal_pos.mpr hp0).ne'
  have hto : (ofReal p).toReal = p := toReal_ofReal hp0.le
  have hnorm : (eLpNorm f (ofReal p) ν) ^ p = In := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp_ne ofReal_ne_top hfasm, hto, ← rpow_mul]
    rw [show (1 / p) * p = (1 : ℝ) by field_simp, rpow_one, hpowInt]
  have hmem : MemLp f (ofReal p) ν := by
    rw [memLp_iff]
    exact (rpow_lt_top_iff_of_pos hp0).mp (by rw [hnorm]; exact hIne.lt_top)
  let k : ℝ≥0∞ := (2 : ℝ≥0∞) ^ d
  have hk0 : k ≠ 0 := pow_ne_zero _ (by simp : (2 : ℝ≥0∞) ≠ 0)
  have hkt : k ≠ ∞ := pow_ne_top (by simp : (2 : ℝ≥0∞) ≠ ∞)
  have htwo : ∀ y ∈ ball x r, ∫⁻ z in ball y (2 * r), ‖f z‖ₑ ∂volume = In := by
    intro y hy
    exact setLIntegral_eq_of_support measurableSet_ball measurableSet_ball
      (ball_subset_ball_two hy) hsupp
  have hvol : ∀ y : E, volume (ball y (2 * r)) = k * v := by
    intro y
    simp only [k]
    rw [ball_volume_mul (by norm_num : (0 : ℝ) < 2) hr x y]
    simp [v, ofReal_pow (by norm_num : (0 : ℝ) ≤ 2), ofReal_ofNat]
  have hM : ∀ y ∈ ball x r, In / (k * v) ≤ maximalFunction volume f y := by
    intro y hy
    have havg := setLAverage_le_maximalFunction volume f y
      (mul_pos (by norm_num : (0 : ℝ) < 2) hr)
    rw [setLAverage_eq, htwo y hy, hvol y] at havg
    exact havg
  have hconst : (In / (k * v)) ^ p ≠ ∞ :=
    rpow_ne_top_of_nonneg hp0.le (div_ne_top hIne (mul_ne_zero hk0 hv0))
  have hmain : (In / (k * v)) ^ p * W ≤ C * In := by
    calc (In / (k * v)) ^ p * W
        = ∫⁻ y in ball x r, (In / (k * v)) ^ p * ofReal (w y) ∂volume := by
          rw [← lintegral_const_mul' _ _ hconst]
      _ ≤ ∫⁻ y in ball x r, (maximalFunction volume f y) ^ p * ofReal (w y) ∂volume := by
          refine setLIntegral_mono' measurableSet_ball fun y hy => ?_
          exact mul_le_mul' (rpow_le_rpow (hM y hy) hp0.le) le_rfl
      _ ≤ ∫⁻ y, (maximalFunction volume f y) ^ p * ofReal (w y) ∂volume :=
          setLIntegral_le_lintegral _ _
      _ = ∫⁻ y, (maximalFunction volume f y) ^ p ∂ν := by
          rw [show ν = volume.withDensity (ofReal ∘ w) from rfl]
          rw [lintegral_withDensity_eq_lintegral_mul_non_measurable volume
            (continuous_ofReal.measurable.comp hm) (ae_of_all _ fun _ => ofReal_lt_top)]
          refine lintegral_congr fun y => ?_
          rw [Pi.mul_apply, Function.comp_apply, mul_comm]
      _ ≤ C * (eLpNorm f (ofReal p) ν) ^ p := hbound f hmem
      _ = C * In := by rw [hnorm]
  simpa [k] using muckenhouptFactor_le hp hIne hv0 hvtop hk0 hkt hmain

/-- Every ball contributes at most `C * 2 ^ (d p)` to the A_p characteristic. -/
private lemma muckenhoupt_ball_le {p : ℝ} (hp : 1 < p) {w : E → ℝ} (hm : Measurable w)
    (hpos : ∀ᵐ y ∂volume, 0 < w y) {C : ℝ≥0∞}
    (hbound : ∀ f : E → ℂ, MemLp f (ofReal p) (weightedLebesgueMeasure w) →
      ∫⁻ y, (maximalFunction volume f y) ^ p ∂weightedLebesgueMeasure w ≤
        C * (eLpNorm f (ofReal p) (weightedLebesgueMeasure w)) ^ p)
    (x : E) {r : ℝ} (hr : 0 < r) :
    ((∫⁻ y in ball x r, ofReal (w y)) / volume (ball x r)) *
      (((∫⁻ y in ball x r, ofReal (w y ^ conjugateExponent p)) / volume (ball x r)) ^
        (p - 1)) ≤
      C * ((2 : ℝ≥0∞) ^ d) ^ p := by
  classical
  let v : ℝ≥0∞ := volume (ball x r)
  let W : ℝ≥0∞ := ∫⁻ y in ball x r, ofReal (w y) ∂volume
  let F : ℕ → E → ℝ≥0∞ := fun n y =>
    if dualPower p w y ≤ (n : ℝ) then ofReal (dualPower p w y) else 0
  let I : ℕ → ℝ≥0∞ := fun n => ∫⁻ y in ball x r, ‖truncatedDual p w x r n y‖ₑ ∂volume
  have hp1 : 0 ≤ p - 1 := (sub_pos.mpr hp).le
  have hFmeas : ∀ n, Measurable (F n) := by
    intro n
    exact Measurable.ite (measurableSet_le (measurable_dualPower hm) measurable_const)
      (continuous_ofReal.measurable.comp (measurable_dualPower hm)) measurable_const
  have hmono : Monotone F := by
    intro m n hmn y
    by_cases hmle : dualPower p w y ≤ (m : ℝ)
    · have hnle : dualPower p w y ≤ (n : ℝ) := hmle.trans (Nat.cast_le.mpr hmn)
      simp [F, hmle, hnle]
    · simp [F, hmle]
  have hsup : ∀ y, ⨆ n, F n y = ofReal (dualPower p w y) := by
    intro y
    apply le_antisymm
    · exact iSup_le fun n => by
        unfold F
        split_ifs
        · exact le_rfl
        · exact zero_le
    · refine le_iSup_of_le ⌈dualPower p w y⌉₊ ?_
      unfold F
      rw [ite_eq_left (Nat.le_ceil (dualPower p w y))]
  have hIn : ∀ n, I n = ∫⁻ y in ball x r, F n y ∂volume := by
    intro n
    refine setLIntegral_congr_fun measurableSet_ball fun y hy => ?_
    rw [enorm_truncatedDual]
    by_cases hle : dualPower p w y ≤ (n : ℝ)
    · unfold F
      rw [ite_eq_left ⟨hy, hle⟩, ite_eq_left hle]
    · unfold F
      rw [ite_eq_right (fun h => hle h.2), ite_eq_right hle]
  have hIsup : ⨆ n, I n =
      ∫⁻ y in ball x r, ofReal (dualPower p w y) ∂volume := by
    simp_rw [hIn]
    rw [← lintegral_iSup hFmeas hmono]
    exact lintegral_congr hsup
  have hsig : ∫⁻ y in ball x r, ofReal (dualPower p w y) ∂volume =
      ∫⁻ y in ball x r, ofReal (w y ^ conjugateExponent p) ∂volume := by
    refine setLIntegral_congr_fun_ae measurableSet_ball ?_
    filter_upwards [hpos] with y hy _hmem
    rw [dualPower_rpow hy]
  have hlim : ⨆ n, I n =
      ∫⁻ y in ball x r, ofReal (w y ^ conjugateExponent p) ∂volume := hIsup.trans hsig
  have hImono : Monotone I := by
    intro m n hmn
    rw [hIn m, hIn n]
    exact lintegral_mono (hmono hmn)
  have hquotmono : Monotone fun n => I n / v := fun m n hmn => by
    dsimp
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul' (hImono hmn) le_rfl
  have hrpowmono : Monotone fun n => (I n / v) ^ (p - 1) := fun m n hmn =>
    rpow_le_rpow (hquotmono hmn) hp1
  have hsuppow : (⨆ n, I n / v) ^ (p - 1) = ⨆ n, (I n / v) ^ (p - 1) :=
    tendsto_nhds_unique
      ((ENNReal.continuous_rpow_const.tendsto (⨆ n, I n / v)).comp
        (tendsto_atTop_iSup hquotmono))
      (tendsto_atTop_iSup hrpowmono)
  have hprod : ((⨆ n, I n) / v) ^ (p - 1) * (W / v) =
      ⨆ n, (I n / v) ^ (p - 1) * (W / v) := by
    calc ((⨆ n, I n) / v) ^ (p - 1) * (W / v)
        = (⨆ n, I n / v) ^ (p - 1) * (W / v) := by rw [iSup_div]
      _ = (⨆ n, (I n / v) ^ (p - 1)) * (W / v) := by rw [hsuppow]
      _ = ⨆ n, (I n / v) ^ (p - 1) * (W / v) := iSup_mul _ _
  rw [mul_comm]
  refine le_trans (le_of_eq ?_)
    (iSup_le fun n => testing_product_le hp hm hbound (x := x) hr n)
  calc ((∫⁻ y in ball x r, ofReal (w y ^ conjugateExponent p)) / v) ^ (p - 1) * (W / v)
      = ((⨆ n, I n) / v) ^ (p - 1) * (W / v) := by rw [← hlim]
    _ = ⨆ n, (I n / v) ^ (p - 1) * (W / v) := hprod

end Aux

/-- **27.44**: boundedness of the actual maximal operator on weighted Lp characterizes A_p. -/
theorem weighted_maximal_iff {d : ℕ} {p : ℝ} (hp : 1 < p)
    {w : EuclideanSpace ℝ (Fin d) → ℝ} (hm : Measurable w)
    (hpos : ∀ᵐ x ∂volume, 0 < w x) (hloc : LocallyIntegrable w volume) :
    IsMuckenhouptWeight p w ↔ ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      ∀ f : EuclideanSpace ℝ (Fin d) → ℂ,
        MemLp f (ENNReal.ofReal p) (weightedLebesgueMeasure w) →
        (∫⁻ x, (TauCeti.maximalFunction volume f x) ^ p ∂weightedLebesgueMeasure w) ≤
          C * (eLpNorm f (ENNReal.ofReal p) (weightedLebesgueMeasure w)) ^ p := by
  constructor
  · -- Sufficiency uses the reverse Hölder property of an A_p weight.
    sorry
  · intro h
    obtain ⟨C, hC, hbound⟩ := h
    refine ⟨hp, hm, hpos, hloc, ?_⟩
    have hchar : muckenhouptCharacteristic p w ≤ C * ((2 : ℝ≥0∞) ^ d) ^ p := by
      unfold muckenhouptCharacteristic
      refine iSup_le fun x => iSup_le fun r => iSup_le fun hr => ?_
      simpa [conjugateExponent] using muckenhoupt_ball_le hp hm hpos hbound x hr
    exact hchar.trans_lt (mul_lt_top (lt_top_iff_ne_top.mpr hC)
      (rpow_lt_top_of_nonneg (by positivity) (pow_ne_top (by simp : (2 : ℝ≥0∞) ≠ ∞))))

/-- Weighted weak (1,1) maximal control for A_1 weights. -/
theorem weighted_maximal_weakType {d : ℕ} {w : EuclideanSpace ℝ (Fin d) → ℝ}
    (hw : IsMuckenhouptOneWeight w) : ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      ∀ f : EuclideanSpace ℝ (Fin d) → ℂ, Integrable f (weightedLebesgueMeasure w) →
      ∀ a : ℝ, 0 < a → ENNReal.ofReal a *
        weightedLebesgueMeasure w {x | ENNReal.ofReal a < TauCeti.maximalFunction volume f x} ≤
          C * ∫⁻ x, ‖f x‖ₑ ∂weightedLebesgueMeasure w := by
  obtain ⟨hm, hpos, hloc, ⟨C, hC, hA⟩⟩ := hw
  refine ⟨ENNReal.ofReal C * (5 : ℝ≥0∞) ^ d, ?_, ?_⟩
  · exact mul_ne_top ENNReal.ofReal_ne_top (pow_ne_top (by simp : (5 : ℝ≥0∞) ≠ ∞))
  · intro f _ a ha
    let ν := weightedLebesgueMeasure w
    let U := {x | ENNReal.ofReal a < maximalFunction volume f x}
    have hU : MeasurableSet U :=
      measurableSet_lt measurable_const (measurable_maximalFunction volume f)
    let slice : ℕ → Set _ := fun n => U ∩ closedBall 0 (n : ℝ)
    have hmono : Monotone slice := fun m n hmn x hx =>
      ⟨hx.1, closedBall_subset_closedBall (Nat.cast_le.mpr hmn) hx.2⟩
    have hunion : ⋃ n, slice n = U := by
      apply subset_antisymm
      · exact iUnion_subset fun _ => inter_subset_left
      · intro x hx
        refine mem_iUnion.mpr ⟨⌈‖x‖⌉₊, hx, ?_⟩
        rw [mem_closedBall_zero_iff]
        exact Nat.le_ceil _
    have hsup : ν U = ⨆ n, ν (slice n) := by
      rw [← hunion]
      exact hmono.measure_iUnion
    rw [hsup, mul_iSup]
    refine iSup_le fun n => ?_
    have hfin : ν (slice n) ≠ ∞ :=
      (lt_of_le_of_lt (measure_mono inter_subset_right)
        (weighted_closedBall_lt_top hloc 0 (n : ℝ))).ne
    rw [(hU.inter isClosed_closedBall.measurableSet).measure_eq_iSup_isCompact_of_ne_top hfin]
    simp_rw [mul_iSup]
    refine iSup_le fun K => iSup_le fun hKsub => iSup_le fun hK => ?_
    exact weighted_compact_mul_le hm hC hA hpos hloc ha hK (hKsub.trans inter_subset_left)

end CKMA
